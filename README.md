# program-verification-project-2
Project 2: Verification with Permissions

Verify functional correctness and derive runtime upper bounds for heap-manipulating programs using Viper (Silicon/Carbon). The project contains four independent challenges; solve them in any order.

## Table of Contents
- [Guidelines](#guidelines)
- [Runtime Model](#runtime-model)
- [Examples](#examples)
- [Challenges](#challenges)
  - [Challenge 1 — Fibonacci](#challenge-1-recursive-fibonacci)
  - [Challenge 2 — Fast Exponentiation](#challenge-2-iterative-fast-exponentiation)
  - [Challenge 3 — Dynamic Arrays (Amortized Analysis)](#challenge-3-amortized-analysis-of-dynamic-arrays)
  - [Challenge 4 — Binary Search Trees (BSTs)](#challenge-4-binary-search-trees-bsts)

## Guidelines
- Solve tasks using Viper and verify with Silicon or Carbon (preferably both).
- Each challenge has a `.vpr` skeleton file; place solutions in the corresponding file.
- Challenges are independent.
- Submit final solutions on DTU Learn.
- You may add ghost code and specifications, but do not modify production code unless explicitly allowed.
- Stars (★) indicate estimated difficulty. Documentation matters — even partial solutions can earn stars if well explained.
- Anything added to the trusted code base must be justified; verification must never allow `assert false`.

Grading (total: 30 stars)
- Grade 12 → ≥ 27 stars
- Grade 10 → ≥ 22 stars
- Grade 7 → ≥ 18 stars
- Grade 4–2 → ≥ 15 stars
- (Subtract 1 star for groups of 2, subtract 2 stars for solo work.)

---

## Runtime Model
We use an abstract time model:
- Each method call consumes 1 time credit.
- Each loop iteration consumes 1 time credit.
- All other statements cost 0 time units.

Time credits are represented by:
- predicate `time_credit()`
- method `consume_time_credit()` that requires `time_credit()`

Rules
- Every non-ghost method body must start with `consume_time_credit()`.
- Every loop body must start with `consume_time_credit()`.
- You may not create time credits; they must come from preconditions.
- Providing enough time credits in the precondition proves an upper bound on runtime.

Example usage (pseudocode)
```text
predicate time_credit()

method consume_time_credit()
  requires time_credit()
```

Credits can be fractional:
- Example: `requires acc(time_credit(), n/1)`

---

## Examples

Not enough credits (illustrative)
```text
method example()
    requires time_credit() && time_credit()
{
    consume_time_credit()
    consume_time_credit()
    consume_time_credit() // verification fails: not enough credits
}
```

---

## Challenges

### Challenge 1: Recursive Fibonacci (★)
File: `fibonacci.vpr`

Tasks:
- Prove functional correctness of the recursive Fibonacci function.
- Derive a minimal upper bound on its runtime with the time-credit model.
- Prove the bound is tight.

---

### Challenge 2: Iterative Fast Exponentiation (★★)
File: `fastexp.vpr`

Tasks:
- Prove the given contract is correct.
- Derive a tight runtime upper bound.
- Use time credits to verify the implementation respects this bound.

---

### Challenge 3: Amortized Analysis of Dynamic Arrays
File: `dyn_array.vpr`

Dynamic arrays must support:
- A static array on the heap,
- Dynamic resizing (doubling capacity when full),
- Amortized constant-time append.

Prove:
- Memory safety,
- Functional correctness,
- Worst-case linear runtime in capacity,
- Amortized constant-time append.

Tasks
- 3.1 (★) Define a `dynamic array` predicate capturing representation invariants, permissions, ghost fields, and helper accessors.
- 3.2 (★) Implement `method cons(_capacity: Int) returns (arr: Ref)` and prove memory safety, correct capacity, and constant-time execution (time credits).
- 3.3 (★★) Define `arr_contents(arr: Ref) : Seq[Int]` (abstraction function) and use it throughout.
- 3.4 (★★★) Prove `append_nogrow(arr, val)` preserves invariants, appends value, is constant-time, and saves a time credit for amortization.
- 3.5 (★★★★) Prove `grow(arr)` correctly doubles capacity, copies contents, preserves invariants, and has linear worst-case runtime while respecting amortization.
- 3.6 (★★★★) Prove `append(arr, val)` is memory-safe, functionally correct, and amortized constant-time using saved credits.

---

### Challenge 4: Binary Search Trees (BSTs)
File: `bst.vpr`

Goals:
- Implement and verify BST insertion and runtime bounds.

Tasks
- 4.1 (★★★) Define predicate `bst(self: Ref)` capturing ordering, tree structure, permissions, and any ghost state.
- 4.2 (★★★★) Implement `method bst_insert(tree: Ref, val: Int)` and verify safety, preserved BST property, and correct insertion behavior.
- 4.3 (★★) Use time credits to show runtime ≤ h + c (h = tree height, c = constant).
- 4.4 (★★★) Prove insertion preserves the set of stored values: values_after = values_before ∪ {val}.

---

Notes
- Each task includes more detailed requirements in the corresponding `.vpr` file.
- Keep specifications, ghost state, and time-credit usage explicit in proofs to make runtime and functional guarantees checkable by the verifier.