/// get a size hint for a call to ratio::<T>() with these parameters
pub fn size_hint_for_ratio<T: arbitrary::unstructured::Int>(
    _a: T,
    _b: T,
) -> (usize, Option<usize>) {
    // the following hint is based on looking at the source for ratio()
    size_hint_for_nonzero_range::<T>()
}

/// get a size hint for a call to int_in_range::<T>() with the parameter a..=b
pub fn size_hint_for_range<T: arbitrary::unstructured::Int>(a: T, b: T) -> (usize, Option<usize>) {
    // the following hint is based on looking at the source for int_in_range()
    if a >= b {
        (0, Some(0))
    } else {
        size_hint_for_nonzero_range::<T>()
    }
}

/// get a size hint for a call to int_in_range::<T>(a..=b) where we assume a < b
/// given this assumption, a and b don't matter for the calculation
pub fn size_hint_for_nonzero_range<T: arbitrary::unstructured::Int>() -> (usize, Option<usize>) {
    (1, Some(std::mem::size_of::<T>()))
}

/// get a size hint for a call to choose(). More precise estimate available if
/// you have an upper bound on how many things you're choosing from
pub fn size_hint_for_choose(max_num_choices: Option<usize>) -> (usize, Option<usize>) {
    // the following hint is based on looking at the source for choose()
    match max_num_choices {
        Some(max_num_choices) => size_hint_for_range::<usize>(0, max_num_choices - 1),
        None => (1, None), // hard to know upper bound here
    }
}
