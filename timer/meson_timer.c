// https://github.com/seL4/util_libs/blob/master/libplatsupport/src/plat/odroidc2/meson_timer.c#L34
/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* #include <errno.h>
#include <stdlib.h>
#include <utils/util.h>
#include <platsupport/timer.h>
#include <platsupport/plat/meson_timer.h>
*/
#include "meson_timer.h"

/*

The device contains 5 timers, A,B C,D,E, but the driver only use timer A and E.
Timer E is a chronomoter while timer A is a countdown.

*/
int meson_init(meson_timer_t *timer, meson_timer_config_t config)
{
    // This won't appear in the cogent code (we assume that
    // we are given non null pointers
    if (timer == NULL || config.vaddr == NULL) {
        return EINVAL;
    }

    timer->regs = (void *)((uintptr_t) config.vaddr + (TIMER_BASE + TIMER_REG_START * 4 - TIMER_MAP_BASE));
   
   /*
To do: put these two lines in a separate function and write it in cogent with Dargent.
For linearity reasons, the cogent function would return the pointer timer->regs as well.
*/
// This first line activates timer A and sets the time resolution for timers A 
// in principle, timer->regs is volatile, but actually, timer->regs->mux behaves normally
// except maybe for the unused bits.
    timer->regs->mux = TIMER_A_EN | (TIMESTAMP_TIMEBASE_1_US << TIMER_E_INPUT_CLK) 
       |          (TIMEOUT_TIMEBASE_1_MS << TIMER_A_INPUT_CLK);
 // timer_e is a volatile register: it is incremented at each tick automatically
 // writing anything to it reset it to 0
 // Maybe leave this out of cogent?
    timer->regs->timer_e = 0;

    return 0;
}


// return the chronometer value (timer E)
uint64_t meson_get_time(meson_timer_t *timer)
{
    // these are volatile : reading the lower register may trigger an overflow
    uint64_t initial_high = timer->regs->timer_e_hi;
    uint64_t low = timer->regs->timer_e;
    uint64_t high = timer->regs->timer_e_hi;
    // This is a trick to check that overflow did not happen
    if (high != initial_high) {
        low = timer->regs->timer_e;
    }

    uint64_t ticks = (high << 32) | low;
    uint64_t time = ticks * NS_IN_US;
    return time;
}

// this sets the timeout for the timer A (countdown)
// at the end of the countdown, an interrupt is generated
void meson_set_timeout(meson_timer_t *timer, uint16_t timeout, bool periodic)
{
    if (periodic) {
        timer->regs->mux |= TIMER_A_MODE;
    } else {
        timer->regs->mux &= ~TIMER_A_MODE;
    }

    timer->regs->timer_a = timeout;

    // actually timer->disable is rudendant with  timer->regs->mux & TIMER_A_EN, isn't it?
    if (timer->disable) {
        timer->regs->mux |= TIMER_A_EN;
        timer->disable = false;
    }
}

// stop the countdown (Timer A)
void meson_stop_timer(meson_timer_t *timer)
{
    timer->regs->mux &= ~TIMER_A_EN;
    timer->disable = true;
}
