/*
 *
 * DaVinci EMAC initialization.
 *
 * (C) Copyright 2011, Ilya Yanok, Emcraft Systems
 *
 * See file CREDITS for list of people who contributed to this
 * project.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of
 * the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc.
 */

#include <common.h>
#include <netdev.h>
#include <asm/io.h>
#include <asm/arch/am35x_def.h>
#include <asm/arch/emac_defs.h>

/*
 * Initializes on-chip ethernet controllers.
 * to override, implement board_eth_init()
 */
int cpu_eth_init(bd_t *bis)
{
	u32 reset, msb, lsb;
	u_int8_t macaddr[6];
	int i;

	/* ensure that the module is out of reset */
	reset = readl(&am35x_scm_general_regs->ip_sw_reset);
	reset &= ~CPGMACSS_SW_RST;
	writel(reset, &am35x_scm_general_regs->ip_sw_reset);

	/* Read MAC address */
	msb = readl(EMAC_MACADDR_MSB);
	lsb = readl(EMAC_MACADDR_LSB);

	for (i = 0; i < 3; i++) {
		macaddr[5 - i] = lsb & 0xFF;
		lsb >>= 8;
	}

	for (i = 0; i < 3; i++) {
		macaddr[2 - i] = msb & 0xFF;
		msb >>= 8;
	}
	eth_setenv_enetaddr("ethaddr", macaddr);

	return davinci_emac_initialize();
}
