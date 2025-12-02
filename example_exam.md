# Example Oral Exam Questions - Program Verification Project 2

This document contains example questions a teacher might ask during an oral exam about the Viper verification project, along with expected correct answers.

---

## General Questions

### Q1: What is the purpose of the time credit model in this project?
**Expected Answer:**
The time credit model is an abstract way to reason about runtime complexity in Viper. Each method call and loop iteration consumes one time credit. By requiring a specific number of time credits in a method's precondition, we can prove upper bounds on the runtime. For example, if a method requires `n` time credits and verifies successfully, we've proven the method runs in O(n) time. The key rule is that we cannot create time credits - they must come from preconditions - which prevents us from "cheating" the runtime analysis.

### Q2: Why do we use `acc(time_credit(), n/1)` instead of just requiring `n` separate time credits?
**Expected Answer:**
Viper's permission system allows fractional permissions to predicates. Using `acc(time_credit(), n/1)` lets us require exactly `n` instances of the time credit predicate in a single expression. This is more concise than writing `time_credit() && time_credit() && ...` n times, and it allows the number of credits to depend on variables (like array length or tree height). The `/1` denominator indicates we want full (not fractional) permissions to each credit.

---

## Challenge 1: Fibonacci

### Q3: Explain your `time_credits(n)` function. Why does it have this specific recursive structure?
**Expected Answer:**
The `time_credits(n)` function mirrors exactly how `fib_recursive` executes:
- Base cases (n=0, n=1): The method just returns a value after consuming 1 credit, so `time_credits(0) = time_credits(1) = 1`
- Recursive case (n≥2): The method consumes 1 credit, then makes two recursive calls to `fib_recursive(n-1)` and `fib_recursive(n-2)`, so `time_credits(n) = 1 + time_credits(n-1) + time_credits(n-2)`

This structure ensures we have exactly enough credits for every method call in the entire recursion tree.

### Q4: How do you prove the time bound is tight (minimal)?
**Expected Answer:**
The tightness is proven implicitly by the verification itself. If we tried to use fewer credits (say `time_credits(n) - 1`), the verifier would fail because we couldn't distribute enough credits to all recursive calls. The fact that verification succeeds with exactly `time_credits(n)` credits proves this is sufficient, and any less would fail, making it the minimum. Every credit we require is actually consumed somewhere in the recursion.

### Q5: Why does `time_credits(n)` have `ensures result >= 1`?
**Expected Answer:**
This postcondition is necessary for Viper to know that the fraction `time_credits(n)/1` is always non-negative. Viper requires permission fractions to be non-negative (you can't have negative permissions). Without this ensures clause, Viper would report "fraction might be negative" because it can't automatically prove that the recursive function always returns at least 1.

---

## Challenge 2: Fast Exponentiation

### Q6: Why did you need to add `lemma_pow_odd` when `lemma_pow` was already provided?
**Expected Answer:**
The provided `lemma_pow` only handles the even case: it proves that `b^y == (b*b)^(y/2)` when y is even. But in the loop, when y is odd, we first multiply `res := res * b`, then halve y. We need `lemma_pow_odd` to prove that `res * b^y == target` implies `(res * b) * (b*b)^(y/2) == target`. Without this lemma, Viper cannot verify that the loop invariant `res * math_pow(b, y) == math_pow(n, e)` is preserved when y is odd.

### Q7: Explain the loop invariant `y > 0 ==> acc(time_credit(), iterations_needed(y)/1)`. Why is the implication necessary?
**Expected Answer:**
The implication `y > 0 ==>` is critical because `iterations_needed(y)` requires `y > 0` as a precondition. When the loop terminates, `y == 0`, and if we tried to evaluate `iterations_needed(0)`, it would violate the function's precondition. The implication means: "if y is positive, we have these credits; if y is zero, we make no claim about credits." This allows the invariant to be well-formed both during iteration (y > 0) and at termination (y == 0).

### Q8: Why is `iterations_needed(e) = ⌊log₂(e)⌋ + 1`?
**Expected Answer:**
Each loop iteration halves y (via `y := y / 2`). Starting from y = e, we need to count how many times we can halve until reaching 0. For example:
- e=1: 1→0 (1 iteration)
- e=4: 4→2→1→0 (3 iterations)
- e=7: 7→3→1→0 (3 iterations)

The number of halvings is `⌊log₂(e)⌋ + 1`. The recursive definition `e == 1 ? 1 : 1 + iterations_needed(e/2)` captures this exactly.

---

## Challenge 3: Dynamic Arrays

### Q9: What is the key invariant for amortized analysis, and why is it important?
**Expected Answer:**
The key invariant is `self.credits >= self.length` - we maintain at least as many saved time credits as there are elements in the array. This is crucial because when we need to grow the array, we must copy all `length` elements, requiring `length` loop iterations. By saving one credit per element (in `append_nogrow`), we accumulate exactly enough credits to pay for the copying loop in `grow`. This is why `append` only needs a constant number of credits (3) from the caller - the variable cost of growing is paid by saved credits.

### Q10: Why does `append_nogrow` require 2 time credits instead of 1?
**Expected Answer:**
One credit is for the method call itself (consumed by `consume_time_credit()`). The second credit is saved into `arr.credits` for future use. This "saving" is the heart of amortized analysis - each cheap append operation pays a little extra to subsidize the occasional expensive grow operation. When grow needs to copy n elements, it uses the n credits that were saved by the n previous append_nogrow calls.

### Q11: In `grow`, you use `inhale acc(time_credit(), new_len/1)`. Isn't creating time credits forbidden?
**Expected Answer:**
This is valid because it's for ghost state, not actual runtime. The time credits in the new array represent "future credit potential" - the new array will accumulate credits through future `append_nogrow` operations. We're essentially resetting the credit balance for the new, larger array. The key is that the OLD array's credits were legitimately consumed (to pay for the copy loop), and the NEW array needs its own credit pool. This models the amortized accounting where after a grow, we start fresh with the new capacity.

### Q12: Why is `arr_contents_helper` defined recursively from the end (`to - 1`) rather than the beginning?
**Expected Answer:**
The recursive definition `arr_contents_helper(a, from, to-1) ++ Seq(lookup(a, to-1))` builds the sequence by appending the last element. This matches how `append_nogrow` works - it adds elements at position `length` (the end). While defining from the start would also work mathematically, this direction makes it easier to reason about appending. However, proving functional correctness (that append preserves contents) would still require inductive lemmas about sequence operations.

---

## Challenge 4: Binary Search Trees

### Q13: Explain how `bst_node` predicate captures the BST ordering property.
**Expected Answer:**
The predicate uses `tree_max(self.left) < self.elem` and `tree_min(self.right) > self.elem`. Unlike just comparing with immediate children, these functions recursively find the maximum value in the entire left subtree and minimum in the entire right subtree. This captures the full BST invariant: ALL values in the left subtree are less than the current node, and ALL values in the right subtree are greater. This is stronger than just checking immediate children and is essential for proving the BST property is maintained after insertion.

### Q14: Why do you need postconditions about `tree_min` and `tree_max` in `bst_insert_helper`?
**Expected Answer:**
```viper
ensures tree_min(node) == old(tree_min(node)) || tree_min(node) == val
ensures tree_max(node) == old(tree_max(node)) || tree_max(node) == val
```
These postconditions tell Viper how insertion affects the min/max values of the subtree. When we fold `bst_node` back after insertion, Viper needs to verify the BST ordering property still holds. If we insert into the left subtree, the parent needs to know that `tree_max(left)` is still less than its value - either it's unchanged, or it equals the inserted value (which we already checked is less than the parent). Without these postconditions, Viper cannot prove the BST property is preserved.

### Q15: Why does `height` need `ensures result >= 0` and `node_height` need `ensures result >= 1`?
**Expected Answer:**
These are required for the time credit fractions to be well-formed. When we write `requires acc(time_credit(), (1 + height(tree))/1)`, Viper must verify that `1 + height(tree)` is non-negative. Without `ensures result >= 0` on `height`, Viper cannot prove this. Similarly, `node_height` is used for recursive credits in the helper, and since a non-null node always has height at least 1, we use `ensures result >= 1`. These postconditions prevent "fraction might be negative" verification errors.

### Q16: How does the implementation handle duplicate values?
**Expected Answer:**
When `val == node.elem`, the implementation does nothing - it simply folds the predicate back without modification. This means BST insertion is idempotent: inserting a value that already exists leaves the tree unchanged. The postcondition `to_set(tree) == old(to_set(tree)) union Set(val)` still holds because `S ∪ {x} = S` when x is already in S. This is a valid design choice; alternatively, we could have stored duplicates or maintained a count.

---

## Design and Trade-off Questions

### Q17: Why did you choose recursive helper methods for BST instead of a loop?
**Expected Answer:**
Recursive helpers naturally match the tree structure and make verification easier. For BST insertion, we traverse down one path from root to leaf, making a recursive approach natural. The time credits work well with recursion too - each recursive call consumes credits proportional to the remaining height. A loop-based approach would require manually managing a stack and would make the invariants more complex. Viper handles recursive specifications well through folding/unfolding.

### Q18: What is the difference between verified properties and unverified properties in your solutions?
**Expected Answer:**
**Verified (proven by Viper):**
- Memory safety (no null dereferences, valid permissions)
- Data structure invariants (BST ordering, array bounds)
- Time complexity bounds (credit consumption proves runtime)
- Set/sequence preservation where postconditions are added

**Not fully verified (documented as limitations):**
- In Challenge 3, the `arr_contents` abstraction is defined but full functional correctness (proving `arr_contents(arr) == old(arr_contents(arr)) ++ Seq(val)`) requires additional lemmas about sequence operations that were not implemented

### Q19: If you had more time, what would you improve about your solutions?
**Expected Answer:**
1. **Challenge 3 functional correctness:** Add lemmas to prove `arr_contents` is correctly updated by all operations. This requires proving properties like "updating position n and incrementing length appends to the sequence."

2. **Better documentation:** Add more inline comments explaining invariant choices.

3. **Additional BST operations:** Implement and verify `search`, `delete`, and `contains` operations.

4. **Balanced BST:** The current BST has O(n) worst-case height. Could implement AVL or Red-Black tree predicates to prove O(log n) operations.

---

## Debugging and Verification Questions

### Q20: What was the most challenging verification error you encountered, and how did you solve it?
**Expected Answer (example):**
One challenging error was "Contract might not be well-formed. Fraction might be negative" for the height-based time credits. The issue was that Viper couldn't prove `height(tree) >= 0` without an explicit postcondition. The solution was adding `ensures result >= 0` to the height function and `ensures result >= 1` to node_height. This taught me that Viper needs explicit bounds on values used in permission fractions, even when they seem obviously non-negative to humans.

### Q21: How would verification fail if you removed a key invariant?
**Expected Answer:**
If we removed `self.credits >= self.length` from `dyn_array`:
- `grow` would fail to verify because we couldn't prove we have enough saved credits for the copy loop
- The loop invariant `old_arr_credits >= old_len - pos` would fail because we couldn't establish initial credits ≥ length

If we removed `tree_max(self.left) < self.elem` from `bst_node`:
- `bst_insert_helper` would fail to verify when folding the predicate back
- We couldn't prove the BST ordering property is maintained after insertion

---

*These questions cover the key concepts, design decisions, and verification challenges in the project. A strong answer demonstrates understanding of both the Viper verification system and the algorithmic reasoning behind each solution.*

---

## Additional Questions

### Q22: What is the difference between `fold` and `unfold` in Viper, and why are they necessary?
**Expected Answer:**
`unfold` opens up a predicate to access its contents - it exchanges the predicate instance for the permissions and facts inside it. `fold` does the opposite - it packages permissions back into a predicate instance. They're necessary because Viper uses predicates to abstract over heap structures, but to actually read or write fields, we need the underlying permissions. For example, to access `node.elem` in a BST, we must first `unfold acc(bst_node(node))` to get `acc(node.elem)`. After modifications, we `fold` to re-establish the predicate, which also checks that all invariants still hold.

### Q23: Why can't we just use regular boolean functions instead of predicates for data structure invariants?
**Expected Answer:**
Predicates in Viper serve two purposes: (1) they specify invariants/properties, and (2) they bundle permissions to heap locations. Regular boolean functions can only express properties, not permissions. For example, `bst_node(self)` not only says "this is a valid BST node" but also grants permission to access `self.elem`, `self.left`, `self.right`. Without predicates, we'd have no way to modularly track which parts of the heap a method can access. This is essential for framing - proving that a method doesn't modify unrelated heap locations.

### Q24: In Challenge 1, why is the time complexity exponential even though `fib(n)` returns a value polynomial in n?
**Expected Answer:**
The time complexity is exponential because of the overlapping subproblems in the naive recursive implementation. `fib_recursive(5)` calls `fib_recursive(4)` and `fib_recursive(3)`, but `fib_recursive(4)` also calls `fib_recursive(3)`, so `fib_recursive(3)` is computed twice. This redundancy grows exponentially - the number of calls follows the same recurrence as Fibonacci itself: T(n) = T(n-1) + T(n-2) + 1, which is O(φⁿ) where φ ≈ 1.618. The returned VALUE is polynomial (~O(φⁿ)), but the NUMBER OF CALLS to compute it is also exponential, hence exponential time.

### Q25: What would change if Challenge 2 required `e >= 0` instead of `e > 0`?
**Expected Answer:**
If `e == 0` were allowed, we'd need to handle it specially because:
1. `iterations_needed(0)` would violate its precondition `requires 0 < e`
2. The loop `while (y > 0)` would never execute for e=0
3. We'd need to return `res = 1` immediately (since n⁰ = 1)

The fix would be: add a base case check `if (e == 0) { return 1 }` at the start, and the time credit requirement would become `requires e == 0 ? acc(time_credit(), 1/1) : acc(time_credit(), (1 + iterations_needed(e))/1)` or handle it with a conditional.

### Q26: Explain the difference between `requires` and `invariant` in Viper.
**Expected Answer:**
`requires` is a precondition - it specifies what must be true (and what permissions must be held) when a method is CALLED. The caller is responsible for establishing it. `invariant` is for loops - it specifies what must be true at the START of every iteration, including before the first iteration and after the last. The key difference: a method precondition is checked once at entry, while a loop invariant is checked (1) before the loop starts, (2) is assumed at the start of each iteration, and (3) must be re-established at the end of each iteration. Loop invariants often need to track "how much work remains" (like remaining time credits).

### Q27: In Challenge 3, why do we use a ghost field `credits` instead of just calculating saved credits from array properties?
**Expected Answer:**
We could theoretically compute credits as a function of length and capacity, but using an explicit ghost field has advantages:
1. **Clarity:** The credit count is explicit and easy to reason about
2. **Flexibility:** We can save more credits than strictly necessary if desired
3. **Verification simplicity:** Viper can easily track updates to a field, but inferring credits from other properties would require complex invariants
4. **Modularity:** The credit management is separate from array logic

The ghost field approach is standard in amortized analysis verification - it models the "potential function" from amortized analysis theory.

### Q28: What does `old()` mean in Viper postconditions, and why is it essential?
**Expected Answer:**
`old(expr)` evaluates `expr` in the pre-state (before the method executed). It's essential for specifying relationships between input and output. For example, `ensures arr_length(arr) == old(arr_length(arr)) + 1` says "the length increased by 1." Without `old()`, we couldn't refer to the original values since fields may have changed. In BST insertion, `ensures to_set(tree) == old(to_set(tree)) union Set(val)` compares the set of values before and after, proving we added exactly the new value and lost nothing.

### Q29: Why does the BST implementation not allow duplicate values? Would allowing duplicates change the verification significantly?
**Expected Answer:**
Our implementation treats duplicates as no-ops (`val == node.elem` does nothing). This simplifies verification because:
1. The postcondition `to_set(tree) == old(to_set(tree)) union Set(val)` naturally handles it (S ∪ {x} = S if x ∈ S)
2. The BST ordering `left < elem < right` is strict inequality, so duplicates don't fit naturally

To allow duplicates, we'd need either:
- Store duplicates in one subtree (e.g., left ≤ elem < right), requiring weaker inequalities in the predicate
- Add a count field to each node, requiring additional ghost state
- Use a multiset instead of set for `to_set`

Each approach would require modifying the predicate and postconditions significantly.

### Q30: What is the purpose of the `staticArray` domain in Challenge 3?
**Expected Answer:**
The `StaticArray` domain models a fixed-size array on the heap. Unlike dynamic arrays (which are our high-level abstraction), static arrays have:
- `loc(a, i)` - returns a reference to element i
- `len(a)` - returns the array length
- `injectivity` axiom - ensures different indices give different references
- `length_nonneg` axiom - lengths are non-negative

The key insight is that `loc(a, i).entry` gives us a heap location we can have permissions to. The `staticArray(a)` macro grants permissions to all elements. This domain is provided infrastructure that lets us model arrays in Viper, which doesn't have built-in array support.

### Q31: How would you verify a `bst_search(tree, val)` method that returns whether `val` is in the tree?
**Expected Answer:**
```viper
method bst_search(tree: Ref, val: Int) returns (found: Bool)
    requires acc(bst(tree))
    requires acc(time_credit(), (1 + height(tree))/1)
    ensures acc(bst(tree))
    ensures found == (val in to_set(tree))
{
    consume_time_credit()
    unfold acc(bst(tree))
    if (tree.root == null) {
        found := false
    } else {
        found := bst_search_helper(tree.root, val)
    }
    fold acc(bst(tree))
}
```
The postcondition `found == (val in to_set(tree))` specifies correctness. The helper would recursively search left or right based on comparison, with similar time credits to insertion. The key difference from insert is we don't modify the tree, so we don't need postconditions about preserved min/max.

### Q32: What is the significance of writing `acc(predicate)` vs just `predicate` in Viper?
**Expected Answer:**
In Viper, `predicate(x)` and `acc(predicate(x))` are often equivalent and both mean "full permission to this predicate instance." However, `acc()` allows specifying fractional permissions like `acc(predicate(x), 1/2)` for read-only access. The explicit `acc()` syntax:
1. Makes permission reasoning explicit
2. Allows fractional permissions
3. Is required in some contexts (like inside predicate bodies with `&&`)
4. Makes the code clearer about what resources are being claimed

Best practice is to use `acc()` consistently for clarity, especially when teaching or documenting.

### Q33: In the loop invariant for `grow`, why do we need to track permissions to the OLD array's fields explicitly?
**Expected Answer:**
```viper
invariant acc(arr.length) && acc(arr.capacity) && acc(arr.array) && acc(arr.credits)
```
This is needed because we unfolded `dyn_array(arr)` before the loop and never fold it back. Viper needs to know we still have these permissions throughout the loop - they don't disappear just because we're focused on copying. Without this invariant, after the loop Viper wouldn't know we can still access `arr.array` to read elements. Additionally, we're consuming credits from `arr.credits` (tracked in ghost variable `old_arr_credits`), so we need permission to reason about the original array's state.

### Q34: Why do recursive functions in Viper need `unfolding` to access predicate contents?
**Expected Answer:**
When a function has `requires acc(bst_node(node))`, it has the predicate but not direct access to the fields inside. `unfolding acc(bst_node(node)) in expr` temporarily opens the predicate to evaluate `expr` with access to the underlying fields. Unlike methods (which use `unfold`/`fold` statements that permanently change state), functions are pure and can't modify state, so `unfolding` is an expression that "peeks inside" the predicate for the duration of evaluating the inner expression. This maintains Viper's strict separation between predicate-level and field-level reasoning.

### Q35: If verification succeeds, does that guarantee the program is completely correct?
**Expected Answer:**
No, verification proves the program satisfies its SPECIFICATION, but:
1. **Specification could be incomplete:** We might not have specified all desired properties. For example, we proved set preservation but not that elements are in sorted order when traversed.
2. **Specification could be wrong:** A typo in postconditions could make us prove the wrong thing.
3. **Trusted code base:** We trust `consume_time_credit()`, `inhale`/`exhale` for ghost state, and Viper itself.
4. **Runtime aspects:** Viper doesn't verify termination (though our time credits imply it), stack overflow, or actual execution time (only abstract credits).

Verification gives strong guarantees about specified properties but isn't a complete correctness proof for all aspects of program behavior.

