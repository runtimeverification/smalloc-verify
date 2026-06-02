//! Minimal extraction of smalloc's `reqali_to_sc` size-class mapping
//! function, isolated so it can be lifted into Lean 4 via Charon + Aeneas
//! for formal verification.
//!
//! Source upstream:
//! <https://github.com/zooko/smalloc/blob/main/smalloc/src/lib.rs>

/// Number of bits available for distinguishing size classes (upstream:
/// `SizeClass = u8`).
pub type SizeClass = u8;

/// Number of bits in the smallest slot size. Upstream is derived as
/// `bits_needed(usize::BITS / 2)`; here baked in as `2`, matching the
/// upstream constant.
pub const SMALLEST_SLOT_SIZE_BITS: u32 = 2;

/// Bit mask of the smallest slot size: `(1 << SMALLEST_SLOT_SIZE_BITS) - 1`
/// equals `0b11` (i.e., `3`).
pub const SMALLEST_SLOT_SIZE_BITS_MASK: usize =
    (1usize << SMALLEST_SLOT_SIZE_BITS) - 1;

/// Maps a `(size, alignment)` allocation request to a size class.
///
/// Computes `⌊log2( (siz-1) | (ali-1) | mask )⌋ + 1`, which is `⌈log2(x)⌉`
/// where `x = max(siz, ali, SMALLEST_SLOT_SIZE)`.
///
/// Preconditions (debug-asserted in upstream smalloc):
/// - `siz > 0`
/// - `ali > 0`
/// - `ali` is a power of two
/// - `ali < 2^32`
pub fn reqali_to_sc(siz: usize, ali: usize) -> SizeClass {
    (((siz - 1) | (ali - 1) | SMALLEST_SLOT_SIZE_BITS_MASK).ilog2() + 1)
        as SizeClass
}
