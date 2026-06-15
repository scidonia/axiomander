"""
Binary Search — Verified Implementation

Classic algorithm with a well-known overflow bug (Java's Arrays.binarySearch
had it for 9 years — used `(lo+hi)//2` which overflows for large arrays).
This implementation uses `lo + (hi - lo) // 2` which is overflow-safe.

Properties to prove:
  1. If target is in arr, the returned index points to it
  2. If target is not in arr, returns -1
  3. Loop invariant: target ∈ arr[lo..hi] iff target ∈ original_arr
  4. Termination: (hi - lo) strictly decreases each iteration
"""

from axiomander.contracts import requires, ensures


@requires(lambda arr, target: len(arr) >= 0)  # array may be empty
@ensures(lambda arr, target, result:
    (result == -1 and not any(x == target for x in arr)) or
    (0 <= result < len(arr) and arr[result] == target))
def binary_search(arr: list[int], target: int) -> int:
    """
    Return index of target in sorted arr, or -1 if not found.
    Assumes arr is sorted in non-decreasing order.

    Loop invariant:
      lo <= hi + 1  ∧  (target ∈ arr[lo..hi] ↔ target ∈ arr)
    """
    lo = 0
    hi = len(arr) - 1

    while lo <= hi:
        mid = lo + (hi - lo) // 2       # overflow-safe midpoint
        if arr[mid] == target:
            return mid
        elif arr[mid] < target:
            lo = mid + 1
        else:
            hi = mid - 1

    return -1
