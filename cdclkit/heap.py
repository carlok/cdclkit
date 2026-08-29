# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Indexed binary max-heap over an external activity array.

The VSIDS decision heuristic needs three operations that a plain ``heapq``
cannot provide:

1. ``pop_max`` -- take the unassigned variable with the highest activity;
2. ``bump`` -- increase the key of a variable that may already be inside the
   heap and restore the invariant in O(log n);
3. ``insert`` -- put a variable back when it is unassigned during backtracking,
   without inserting duplicates.

So the heap keeps a position index (``pos[v]`` = slot of ``v`` in the array, or
-1 when absent) alongside the array itself.  Keys are *not* stored in the heap:
they live in the caller's ``act`` list and are read through it, so a bump is
"write ``act[v]``, then percolate up".  That is exactly the MiniSat design.

Ties are broken by variable index (lower index wins) so that solver runs are
deterministic even when many activities are equal, which matters for
reproducible proofs and regression tests.
"""

from __future__ import annotations

__all__ = ["ActivityHeap"]


class ActivityHeap:
    """Max-heap of variables ordered by ``act[v]``, ties broken by index."""

    __slots__ = ("act", "heap", "pos")

    def __init__(self, act: list[float], capacity: int = 0) -> None:
        self.act = act
        self.heap: list[int] = []
        self.pos: list[int] = [-1] * capacity

    # -- capacity -----------------------------------------------------------

    def grow(self, n: int) -> None:
        """Make room for variables ``[0, n)``."""
        while len(self.pos) < n:
            self.pos.append(-1)

    # -- predicates ---------------------------------------------------------

    def __len__(self) -> int:
        return len(self.heap)

    def __contains__(self, v: int) -> bool:
        return v < len(self.pos) and self.pos[v] >= 0

    def empty(self) -> bool:
        return not self.heap

    # -- ordering -----------------------------------------------------------

    def _better(self, a: int, b: int) -> bool:
        """True when ``a`` must sit above ``b``."""
        act = self.act
        aa = act[a]
        ab = act[b]
        if aa != ab:
            return aa > ab
        return a < b

    def _up(self, i: int) -> None:
        heap = self.heap
        pos = self.pos
        v = heap[i]
        while i > 0:
            parent = (i - 1) >> 1
            pv = heap[parent]
            if not self._better(v, pv):
                break
            heap[i] = pv
            pos[pv] = i
            i = parent
        heap[i] = v
        pos[v] = i

    def _down(self, i: int) -> None:
        heap = self.heap
        pos = self.pos
        n = len(heap)
        v = heap[i]
        while True:
            left = 2 * i + 1
            if left >= n:
                break
            right = left + 1
            child = left
            if right < n and self._better(heap[right], heap[left]):
                child = right
            cv = heap[child]
            if not self._better(cv, v):
                break
            heap[i] = cv
            pos[cv] = i
            i = child
        heap[i] = v
        pos[v] = i

    # -- mutation -----------------------------------------------------------

    def insert(self, v: int) -> None:
        """Insert ``v`` if it is not already present."""
        if v >= len(self.pos):
            self.grow(v + 1)
        if self.pos[v] >= 0:
            return
        self.heap.append(v)
        self.pos[v] = len(self.heap) - 1
        self._up(len(self.heap) - 1)

    def bump(self, v: int) -> None:
        """Restore the invariant after ``act[v]`` was increased."""
        if v < len(self.pos) and self.pos[v] >= 0:
            self._up(self.pos[v])

    def pop_max(self) -> int:
        """Remove and return the variable with the largest activity."""
        heap = self.heap
        pos = self.pos
        top = heap[0]
        last = heap.pop()
        pos[top] = -1
        if heap:
            heap[0] = last
            pos[last] = 0
            self._down(0)
        return top

    def peek_max(self) -> int:
        return self.heap[0]

    def remove(self, v: int) -> None:
        """Remove ``v`` from the heap if present."""
        i = self.pos[v] if v < len(self.pos) else -1
        if i < 0:
            return
        heap = self.heap
        pos = self.pos
        pos[v] = -1
        last = heap.pop()
        if i < len(heap):
            heap[i] = last
            pos[last] = i
            self._up(i)
            self._down(i)

    def rebuild(self, variables) -> None:
        """Discard the contents and heapify ``variables`` from scratch."""
        for v in self.heap:
            self.pos[v] = -1
        self.heap = list(variables)
        for i, v in enumerate(self.heap):
            if v >= len(self.pos):
                self.grow(v + 1)
            self.pos[v] = i
        for i in range(len(self.heap) // 2 - 1, -1, -1):
            self._down(i)

    # -- debugging ----------------------------------------------------------

    def check_invariant(self) -> bool:
        """Verify heap order and index consistency (used by the test suite)."""
        for i, v in enumerate(self.heap):
            if self.pos[v] != i:
                return False
            left, right = 2 * i + 1, 2 * i + 2
            if left < len(self.heap) and self._better(self.heap[left], v):
                return False
            if right < len(self.heap) and self._better(self.heap[right], v):
                return False
        for v, p in enumerate(self.pos):
            if p >= 0 and (p >= len(self.heap) or self.heap[p] != v):
                return False
        return True
