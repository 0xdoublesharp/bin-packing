//! Widened coordinate arithmetic shared by packing and readback.

/// Whether the trailing edge and its clearance end at or before the limit.
pub(crate) fn end_with_gap_at_most(start: u32, extent: u32, gap: u32, limit: u32) -> bool {
    start as u64 + extent as u64 + gap as u64 <= limit as u64
}

/// Applies trailing kerf relief up to the representable coordinate limit.
#[cfg(feature = "two-d")]
pub(crate) fn effective_axis_bound(extent: u32, kerf: u32, edge_kerf_relief: bool) -> u32 {
    if edge_kerf_relief { extent.saturating_add(kerf) } else { extent }
}

/// Whether the interval lies between the leading and trailing stock trims.
#[cfg(feature = "two-d")]
pub(crate) fn fits_trimmed_axis(
    start: u32,
    extent: u32,
    trim_low: u32,
    trim_high: u32,
    stock: u32,
) -> bool {
    trim_low <= start && start as u64 + extent as u64 + trim_high as u64 <= stock as u64
}

/// Computes a planar area after widening both dimensions.
#[cfg(feature = "two-d")]
pub(crate) fn area_u64(width: u32, height: u32) -> u64 {
    width as u64 * height as u64
}
