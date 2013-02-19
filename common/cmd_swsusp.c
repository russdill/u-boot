/*
 * (C) Copyright 2013
 * Russ Dill <Russ.Dill@ti.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 */

#include <common.h>
#include <command.h>
#include <part.h>
#include <malloc.h>

#include <linux/lzo.h>

DECLARE_GLOBAL_DATA_PTR;

#define HIBERNATE_SIG "S1SUSPEND"
#define PAGE_SIZE 4096

struct swsusp_header {
	char reserved[PAGE_SIZE - 20 - sizeof(u64) - sizeof(int) - sizeof(u32)];
	u32	crc32;
	u64	image;
	unsigned int flags;
	char	orig_sig[10];
	char	sig[10];
} __attribute__((packed));

#define __NEW_UTS_LEN 64

struct new_utsname {
	char sysname[__NEW_UTS_LEN + 1];
	char nodename[__NEW_UTS_LEN + 1];
	char release[__NEW_UTS_LEN + 1];
	char version[__NEW_UTS_LEN + 1];
	char machine[__NEW_UTS_LEN + 1];
	char domainname[__NEW_UTS_LEN + 1];
};

struct swsusp_info {
	struct new_utsname	uts;
	u32			version_code;
	unsigned long		num_physpages;
	int			cpus;
	unsigned long		image_pages;
	unsigned long		pages;
	unsigned long		size;
	void			(*cpu_resume)(void);
};

struct swap_map_page {
	u64 entries[PAGE_SIZE / sizeof(u64) - 1];
	u64 next_swap;
};

struct swsusp_finish_context {
	void *remap_orig_page;
	void *remap_temp_page;
	void (*cpu_resume)(void);
};

#define SF_NOCOMPRESS_MODE 2

#define LZO_HEADER      sizeof(size_t)

/* Number of pages/bytes we'll compress at one time. */
#define LZO_UNC_PAGES	32
#define LZO_UNC_SIZE	(LZO_UNC_PAGES * PAGE_SIZE)

/* Number of pages/bytes we need for compressed data (worst case). */
#define LZO_CMP_PAGES	DIV_ROUND_UP(lzo1x_worst_compress(LZO_UNC_SIZE) + \
				LZO_HEADER, PAGE_SIZE)
#define LZO_CMP_SIZE	(LZO_CMP_PAGES * PAGE_SIZE)

extern void arch_preboot_os(void);
extern void call_with_stack(void (*fn)(void*), void *userdata, void *stack);

static block_dev_desc_t *swap_dev;
static disk_partition_t swap_info;

static inline u32 pg_ub2zero(u32 pg)
{
	return pg - CONFIG_SYS_SDRAM_BASE / PAGE_SIZE;
}

static inline u32 pg_zero2ub(u32 pg)
{
	return pg + CONFIG_SYS_SDRAM_BASE / PAGE_SIZE;
}

static inline void *pg2addr(u32 page)
{
	return (void *) (page * PAGE_SIZE);
}

static int page_read (u32 page, void *addr)
{
	__u32 cnt;
	int blk_per_page;

	blk_per_page = PAGE_SIZE / swap_dev->blksz;
	cnt = swap_dev->block_read(swap_dev->dev,
				swap_info.start + (page * blk_per_page),
				blk_per_page, addr);
	return cnt != blk_per_page;
}

static int page_write (u32 page, void *addr)
{
	__u32 cnt;
	int blk_per_page;

	blk_per_page = PAGE_SIZE / swap_dev->blksz;
	cnt = swap_dev->block_write(swap_dev->dev,
				swap_info.start + (page * blk_per_page),
				blk_per_page, addr);
	return cnt != blk_per_page;
}

static void swsusp_finish (void *userdata)
{
	struct swsusp_finish_context *context = userdata;
	u32 **remap_orig;
	u32 **remap_temp;
	int idx = 0;

	remap_orig = context->remap_orig_page;
	remap_temp = context->remap_temp_page;

	for (;;) {
		u32 *orig, *temp;
		int count;

		/* Linked list to next page */
		if (idx + 1 == PAGE_SIZE / sizeof(u32)) {
			remap_orig = remap_orig[idx];
			remap_temp = remap_temp[idx];
			idx = 0;
		}
		if (!remap_orig || remap_orig[idx] == ~0UL)
			break;

		count = PAGE_SIZE / sizeof(u32);
		orig = remap_orig[idx];
		temp = remap_temp[idx];
		while (count--)
			*orig++ = *temp++;

		idx++;
	}
	context->cpu_resume();
}

static struct swap_map_page *meta_map;
static u64 meta_map_next;
static u64 meta_map_curr;
static u64 meta_map_start;
static int meta_idx;

int raw_page_init (u64 start)
{
	meta_map = malloc(PAGE_SIZE);
	if (!meta_map)
		return -1;
	meta_map_next = 0;
	meta_map_curr = 0;
	meta_map_start = start;
	return 0;
}

void raw_page_start (void)
{
	meta_idx = ARRAY_SIZE(meta_map->entries);
	meta_map_next = meta_map_start;
}

int raw_page_get_next (void *buffer)
{
	if (meta_idx == ARRAY_SIZE(meta_map->entries)) {
		if (!meta_map_next)
			return 0;
		if (meta_map_curr != meta_map_next) {
			if (page_read(meta_map_next, meta_map))
				return -1;
			meta_map_curr = meta_map_next;
			meta_map_next = meta_map->next_swap;
		}
		meta_idx = 0;
	}
	if (page_read(meta_map->entries[meta_idx++], buffer))
		return -1;

	return 1;
}

void raw_page_exit (void)
{
	free(meta_map);
	meta_map = NULL;
}

static int image_compressed;
static int image_pages_avail;
static unsigned char *unc_buf, *cmp_buf;
static int unc_offset;

int image_page_init (int compressed)
{
	if (compressed) {
		unc_buf = malloc(LZO_UNC_SIZE);
		cmp_buf = malloc(LZO_CMP_SIZE);
		if (!unc_buf || !cmp_buf)
			return -1;
	}

	image_compressed = compressed;

	return 0;
}

void image_page_start (void)
{
	image_pages_avail = 0;
}

int image_page_get_next (void *buffer)
{
	if (image_compressed) {
#ifdef CONFIG_LZO
		if (!image_pages_avail) {
			int ret;
			size_t unc_len, cmp_len, cmp_avail;

			ret = raw_page_get_next(cmp_buf);
			if (ret <= 0)
				return ret;

			cmp_len = *(size_t *) cmp_buf;
			cmp_avail = PAGE_SIZE;

			while (cmp_avail < cmp_len + LZO_HEADER) {
				ret = raw_page_get_next(cmp_buf + cmp_avail);
				if (ret <= 0)
					return ret;
				cmp_avail += PAGE_SIZE;
			}

			unc_len = LZO_UNC_SIZE;
			ret = lzo1x_decompress_safe(cmp_buf + LZO_HEADER,
						cmp_len, unc_buf, &unc_len);
			if (ret != LZO_E_OK) {
				printf("Decompression failure: %d\n", ret);
				return ret;
			}
			image_pages_avail = unc_len / PAGE_SIZE;
			unc_offset = 0;
		}

		memcpy(buffer, unc_buf + unc_offset, PAGE_SIZE);
		unc_offset += PAGE_SIZE;
		image_pages_avail--;
		return 1;
#else
		printf("No LZO support in u-boot.\n");
		return -1;
#endif
	} else {
		return raw_page_get_next(buffer);
	}
}

void image_page_exit (void)
{
	free(unc_buf);
	free(cmp_buf);
	unc_buf = cmp_buf = NULL;
}

static void bitmap_set (u32 *bm, unsigned int bit)
{
	bm[bit >> 5] |= (1 << (bit & 0x1f));
}

static int bitmap_is_set (u32 *bm, unsigned int bit)
{
	return !!(bm[bit >> 5] & (1 << (bit & 0x1f)));
}

static u32 *used_bitmap;
static u32 total_pages;
static u32 next_free_page;

static int free_page_init (void)
{
	total_pages = gd->ram_size / PAGE_SIZE;
	used_bitmap = malloc(total_pages / 8);
	if (!used_bitmap)
		return -1;
	return 0;
}

static void free_page_start (int offset)
{
	memset(used_bitmap, 0, total_pages / 8);
	next_free_page = pg_ub2zero(offset);
}

static int free_page_get_next (void)
{
	while (bitmap_is_set(used_bitmap, next_free_page))
		next_free_page++;
	return pg_zero2ub(next_free_page++);
}

static void free_page_mark_used (u32 page)
{
	bitmap_set(used_bitmap, pg_ub2zero(page));
}

static void free_page_exit (void)
{
	free(used_bitmap);
	used_bitmap = NULL;
}

int do_swsusp (cmd_tbl_t *cmdtp, int flag, int argc, char * const argv[])
{
	int ret;
	__u32 offset = 0;
	void *spare_page = NULL;
	struct swsusp_header *swsusp_header;
	struct swsusp_info *swsusp_info;
	struct swsusp_finish_context *context;
	int min_page, max_page;
	int i;
	u32 nr_pfn_pages;
	u32 **pfn_pages = NULL;
	u32 *remap_orig_page;
	u32 *remap_temp_page;
	u32 **remap_orig;
	u32 **remap_temp;
	int remap_idx;
	int m;
	void (*swsusp_finish_copy)(void*);
	char *data_page;
	char *stack_addr;

	if (argc < 2) {
		printf("usage: swsusp <interface> [<dev[:part]>] [<offset>]\n");
		return 0;
	}

	if (argc == 4) {
		char *ep;
		offset = simple_strtoul(argv[3], &ep, 16);
		if (*ep) {
			printf("Invalid block offset\n");
			return 1;
		}
	}

	/* Allow 2 pages for exception vectors */
	min_page = pg_zero2ub(2);

	/* Allow for 16 pages of stack */
	max_page = gd->start_addr_sp / PAGE_SIZE - 16;

	if (free_page_init())
		goto mem_err;
	free_page_start(min_page);

	spare_page = malloc(PAGE_SIZE);
	if (!spare_page)
		goto mem_err;

	ret = get_device_and_partition(argv[1], argv[2], &swap_dev, &swap_info,
								1);
	if (ret < 0)
		goto err;

	swsusp_header = spare_page;
	if (page_read(offset, swsusp_header))
		goto read_err;

	if (memcmp(HIBERNATE_SIG, swsusp_header->sig, 10)) {
		printf("No hibernation image present\n");
		return 0;
	}

	/* Overwrite header if necessary */
	if (memcmp(swsusp_header->sig, swsusp_header->orig_sig, 10)) {
		memcpy(swsusp_header->sig, swsusp_header->orig_sig, 10);
		if (page_write(offset, swsusp_header))
			printf("Write error resetting header\n");
	}

	if (raw_page_init(swsusp_header->image))
		goto mem_err;
	raw_page_start();

	if (image_page_init(!(swsusp_header->flags & SF_NOCOMPRESS_MODE)))
		goto mem_err;
	image_page_start();

	swsusp_info = spare_page;
	if (raw_page_get_next(swsusp_info) <= 0)
		goto read_err;

	nr_pfn_pages = (swsusp_info->image_pages * 4 + PAGE_SIZE - 1) /
								PAGE_SIZE;
	pfn_pages = malloc(nr_pfn_pages * sizeof(u32 *));
	if (!pfn_pages)
		goto mem_err;
	memset(pfn_pages, 0, nr_pfn_pages * sizeof(u32 *));
	for (i = 0; i < nr_pfn_pages; i++) {
		u32 idx;
		pfn_pages[i] = malloc(PAGE_SIZE);
		if (!pfn_pages[i])
			goto mem_err;
		if (image_page_get_next(pfn_pages[i]) <= 0)
			goto read_err;
		for (idx = 0; idx < PAGE_SIZE / sizeof(u32); idx++) {
			u32 page = pfn_pages[i][idx];
			if (page == ~0UL)
				break;
			free_page_mark_used(page);
		}
	}

	printf("Loading image data pages (%lu pages)\n",
						swsusp_info->image_pages);

	remap_orig_page = pg2addr(free_page_get_next());
	remap_temp_page = pg2addr(free_page_get_next());

	remap_orig = remap_orig_page;
	remap_temp = remap_temp_page;
	remap_idx = 0;

	m = (swsusp_info->image_pages / 10) ? : 1;
	for (i = 0; i < swsusp_info->image_pages; i++) {
		u32 page = pfn_pages[i >> 10][i & 0x3ff];
		if (page < min_page || page > max_page) {
			remap_orig[remap_idx] = pg2addr(page);
			page = free_page_get_next();
			remap_temp[remap_idx] = pg2addr(page);
			remap_idx++;
			/* If we fill our current page, allocate a new one */
			if (remap_idx + 1 == PAGE_SIZE / sizeof(u32)) {
				u32 *next;

				next = pg2addr(free_page_get_next());
				remap_orig[remap_idx] = next;
				remap_orig = next;

				next = pg2addr(free_page_get_next());
				remap_temp[remap_idx] = next;
				remap_temp = next;

				remap_idx = 0;
			}
		}
		if (image_page_get_next(pg2addr(page)) <= 0)
			goto read_err;
		if (!(i % m))
			printf("Image loading progress: %3d%%\n", 10 * i / m);
	}

	printf("Image loading done.\n");

	/* put end markers on the remap list */
	remap_orig[remap_idx] = (void *) ~0UL;
	remap_temp[remap_idx] = (void *) ~0UL;

	/* Make a copy of swsusp_finish in a free data page */
	data_page = pg2addr(free_page_get_next());
	memcpy(data_page, swsusp_finish, PAGE_SIZE);
	swsusp_finish_copy = (void *) data_page;

	/* Setup context for swsusp_finish at the end of the data_page */
	context = (struct swsusp_finish_context *) (data_page + PAGE_SIZE);
	context--;
	context->remap_orig_page = remap_orig_page;
	context->remap_temp_page = remap_temp_page;
	context->cpu_resume = swsusp_info->cpu_resume;

	/* Get a stack pointer for swsusp_finish, growing down from context */
	stack_addr = (char *) context;

#ifdef CONFIG_NETCONSOLE
	/*
	 * Stop the ethernet stack if NetConsole could have
	 * left it up
	 */
	eth_halt();
#endif
	arch_preboot_os();
#ifdef CONFIG_USB_DEVICE
	udc_disconnect();
#endif
	cleanup_before_linux();

	/* Copy the final data from a safe place */
	call_with_stack(swsusp_finish_copy, context, stack_addr);

	return 0;

mem_err:
	printf("Not enough memory.\n");
	goto err;

read_err:
	printf("Read error while restoring image.\n");

err:
	raw_page_exit();
	image_page_exit();
	free_page_exit();
	if (pfn_pages) {
		for (i = 0; i < nr_pfn_pages; i++)
			free(pfn_pages[i]);
		free(pfn_pages);
	}
	free(spare_page);

	return 1;
}

U_BOOT_CMD(swsusp, 4, 0, do_swsusp,
	"Restore SWSUSP hibernation image",
	"<interface> [<dev[:part]>] [<offset>]"
);
