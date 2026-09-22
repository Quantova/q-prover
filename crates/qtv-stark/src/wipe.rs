// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

use core::sync::atomic::{compiler_fence, Ordering};

pub(crate) fn wipe<T: Copy>(buf: &mut [T], zero: T) {
    for slot in buf.iter_mut() {
        unsafe { core::ptr::write_volatile(slot, zero) }
    }
    compiler_fence(Ordering::SeqCst);
}
