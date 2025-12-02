# bst.vpr - Line-by-Line Explanation

This document provides a detailed line-by-line explanation of `bst.vpr`, covering Binary Search Tree verification in Viper.

---

## File Overview

This file implements a Binary Search Tree with:
1. **Recursive predicates**: For tree structure with BST property
2. **Insertion with proof**: Maintains BST invariant
3. **Runtime bound**: O(height) time complexity proven with credits
4. **Set abstraction**: Maps tree to mathematical set of values

---

## Lines 1-12: Runtime Model

```viper
// -----------------------------------------
// Runtime model
// Notice that we can hold at most one permission
// to *fields*, but this does not apply to *predicates*
predicate time_credit() // represents one abstract unit of time

// models spending an abstract unit of time 
// needs to be called at the beginning of every method
// and loop iteration
method consume_time_credit() // 
    requires acc(time_credit(), 1/1)
// -----------------------------------------
```

Same as other files - see `fibonacci_explained.md` for details.

---

## Lines 14-28: Object Model (Fields)

```viper
// -----------------------------------------
// Object model
// The provided fields are required.
// You can add additional (ghost) fields
// if you want

// a BST node
field elem : Int // value stored in the node
field left : Ref // left child
field right : Ref // right child

// Object for the whole BST, which just stores a 
// pointer to the root node of the tree
field root: Ref 
// -----------------------------------------
```

### Line 21: `field elem : Int`

**Purpose**: The integer value stored at this node.

### Lines 22-23: `field left : Ref` and `field right : Ref`

**Viper Syntax**:
- `Ref` is the reference type (like a pointer)
- Can be `null` or point to an object

**Purpose**: Pointers to left and right children.

### Line 27: `field root: Ref`

**Purpose**: 
- The BST object just holds a pointer to the root node
- Allows empty trees (root == null)
- Separates "tree container" from "tree nodes"

---

## Lines 30-46: Utility Functions

```viper
// -----------------------------------------
// Utility functions, which you may find useful
function max(a : Int, b : Int) : Int 
    ensures result >= a && result >= b
    ensures result == a || result == b
{
    a > b ? a : b
}

function min(a : Int, b : Int) : Int 
    ensures result <= a && result <= b
    ensures result == a || result == b
{
    a < b ? a : b
}
// -----------------------------------------
```

### Lines 32-37: max Function

```viper
function max(a : Int, b : Int) : Int 
    ensures result >= a && result >= b
    ensures result == a || result == b
{
    a > b ? a : b
}
```

**Postconditions**:
- `result >= a && result >= b`: Result is at least as large as both inputs
- `result == a || result == b`: Result is exactly one of the inputs

**Why Both Postconditions?**:
- First says "it's big enough"
- Second says "it's one of the inputs" (not some arbitrary larger value)
- Together they fully specify max behavior

### Lines 39-44: min Function

Same pattern for minimum.

---

## Lines 48-67: Helper Functions for BST Bounds

```viper
// -----------------------------------------
// TASK 4.1: Define a predicate for binary search trees and individual BST nodes.
// You may define additional fields, predicates, arguments or heap-based functions.

// Helper functions to get min and max values in a subtree
function tree_min(node: Ref): Int
    requires node != null
    requires acc(bst_node(node))
{
    unfolding acc(bst_node(node)) in (
        node.left == null ? node.elem : min(node.elem, tree_min(node.left))
    )
}

function tree_max(node: Ref): Int
    requires node != null
    requires acc(bst_node(node))
{
    unfolding acc(bst_node(node)) in (
        node.right == null ? node.elem : max(node.elem, tree_max(node.right))
    )
}
```

### Line 53: `function tree_min(node: Ref): Int`

**Purpose**: Find the minimum value in a subtree rooted at `node`.

### Line 54: `requires node != null`

**Purpose**: Can't find min of null node.

### Line 55: `requires acc(bst_node(node))`

**Purpose**: 
- Need permission to the bst_node predicate
- This gives us access to the node's structure

### Lines 56-59: tree_min Body

```viper
{
    unfolding acc(bst_node(node)) in (
        node.left == null ? node.elem : min(node.elem, tree_min(node.left))
    )
}
```

**Logic**:
- If no left child: this node has the minimum value
- Otherwise: minimum is min of this node and left subtree's minimum

**Why Check node.elem Too?**:
- In a BST, left subtree values < node.elem
- So tree_min(node.left) < node.elem
- But we use `min()` anyway for robustness
- Actually, for a proper BST, we could just use tree_min(node.left)

### Lines 61-67: tree_max Function

```viper
function tree_max(node: Ref): Int
    requires node != null
    requires acc(bst_node(node))
{
    unfolding acc(bst_node(node)) in (
        node.right == null ? node.elem : max(node.elem, tree_max(node.right))
    )
}
```

**Logic**: Symmetric to tree_min but for right subtree.

---

## Lines 69-76: BST Predicate (Tree Container)

```viper
// The whole tree has just a reference to the root
// The empty tree is represented by self.root == null
predicate bst(self: Ref) {
    acc(self.root) &&
    (self.root != null ==> acc(bst_node(self.root)))
}
```

### Line 71: `predicate bst(self: Ref) { ... }`

**Purpose**: Represents a complete BST data structure.

### Line 72: `acc(self.root)`

**Purpose**: Permission to the root field.

### Line 73: `(self.root != null ==> acc(bst_node(self.root)))`

**Viper Syntax**:
- `==>` is implication
- `A ==> B` means "if A then B"

**Purpose**:
- If root is not null, we have permission to the root node predicate
- Empty tree (root == null) has no node permissions
- This is a **conditional permission**

---

## Lines 78-91: BST Node Predicate

```viper
// A single BST node. Apart from field permissions, the current value
// must be greater than the largest value in the left subtree and
// smaller than the smallest value in the right subtree.
predicate bst_node(self: Ref) {
    acc(self.elem) && acc(self.left) && acc(self.right) &&
    
    // Left subtree: either null or valid BST node with max < current
    (self.left != null ==> 
        acc(bst_node(self.left)) && tree_max(self.left) < self.elem) &&
    
    // Right subtree: either null or valid BST node with min > current
    (self.right != null ==> 
        acc(bst_node(self.right)) && tree_min(self.right) > self.elem)
}
```

### Line 82: `acc(self.elem) && acc(self.left) && acc(self.right)`

**Purpose**: Permission to all three fields of the node.

### Lines 84-86: Left Subtree Constraints

```viper
    (self.left != null ==> 
        acc(bst_node(self.left)) && tree_max(self.left) < self.elem)
```

**Purpose**:
- If left child exists: permission to it as a bst_node
- **BST Property**: Maximum value in left subtree < this node's value
- `tree_max(self.left) < self.elem` enforces the BST ordering

### Lines 88-90: Right Subtree Constraints

```viper
    (self.right != null ==> 
        acc(bst_node(self.right)) && tree_min(self.right) > self.elem)
```

**Purpose**:
- If right child exists: permission to it as a bst_node
- **BST Property**: Minimum value in right subtree > this node's value

**Key Insight**: This predicate is **recursive** - bst_node contains bst_node!
- This naturally models tree structure
- Permission to a node includes permission to entire subtree

---

## Lines 94-119: bst_insert Method

```viper
method bst_insert(tree: Ref, val: Int)
    requires acc(bst(tree))
    requires acc(time_credit(), (1 + height(tree))/1)
    ensures acc(bst(tree))
    ensures to_set(tree) == old(to_set(tree)) union Set(val)
{
    consume_time_credit()
    
    unfold acc(bst(tree))
    
    if (tree.root == null) {
        // Empty tree - create new root node
        var new_node: Ref
        new_node := new(elem, left, right)
        new_node.elem := val
        new_node.left := null
        new_node.right := null
        fold acc(bst_node(new_node))
        tree.root := new_node
    } else {
        // Non-empty tree - insert into existing tree
        bst_insert_helper(tree.root, val)
    }
    
    fold acc(bst(tree))
}
```

### Line 95: `requires acc(bst(tree))`

**Purpose**: Need permission to the BST.

### Line 96: `requires acc(time_credit(), (1 + height(tree))/1)`

**Purpose**:
- Runtime bound: O(height)
- 1 credit for this method + height credits for traversal
- `height(tree)` is defined later

### Line 98: `ensures to_set(tree) == old(to_set(tree)) union Set(val)`

**Viper Syntax**:
- `Set(val)` creates a singleton set containing val
- `union` is set union operator

**Purpose**: After insert, tree contains all old values plus the new value.

### Line 103: `unfold acc(bst(tree))`

**Purpose**: Open the bst predicate to access tree.root.

### Lines 105-113: Empty Tree Case

```viper
    if (tree.root == null) {
        var new_node: Ref
        new_node := new(elem, left, right)
        new_node.elem := val
        new_node.left := null
        new_node.right := null
        fold acc(bst_node(new_node))
        tree.root := new_node
    }
```

**Logic**:
1. Allocate new node
2. Set value and null children
3. `fold acc(bst_node(new_node))` - package as valid BST node
4. Set as root

### Line 112: `fold acc(bst_node(new_node))`

**Purpose**:
- Before fold: have permissions to fields, null children
- After fold: have bst_node predicate
- Must satisfy predicate body (trivially satisfied - no children)

### Lines 114-116: Non-empty Tree Case

```viper
    } else {
        bst_insert_helper(tree.root, val)
    }
```

**Purpose**: Delegate to recursive helper.

### Line 119: `fold acc(bst(tree))`

**Purpose**: Re-package as bst predicate.

---

## Lines 122-165: bst_insert_helper Method

```viper
// Helper method to insert into a non-null BST node
method bst_insert_helper(node: Ref, val: Int)
    requires node != null
    requires acc(bst_node(node))
    requires acc(time_credit(), node_height(node)/1)
    ensures acc(bst_node(node))
    // Preserve min/max bounds
    ensures tree_min(node) == old(tree_min(node)) || tree_min(node) == val
    ensures tree_max(node) == old(tree_max(node)) || tree_max(node) == val
    // Value set preservation
    ensures node_to_set(node) == old(node_to_set(node)) union Set(val)
{
    consume_time_credit()
    
    unfold acc(bst_node(node))
    
    if (val < node.elem) {
        // Insert into left subtree
        if (node.left == null) {
            var new_node: Ref
            new_node := new(elem, left, right)
            new_node.elem := val
            new_node.left := null
            new_node.right := null
            fold acc(bst_node(new_node))
            node.left := new_node
        } else {
            bst_insert_helper(node.left, val)
        }
    } elseif (val > node.elem) {
        // Insert into right subtree
        if (node.right == null) {
            var new_node: Ref
            new_node := new(elem, left, right)
            new_node.elem := val
            new_node.left := null
            new_node.right := null
            fold acc(bst_node(new_node))
            node.right := new_node
        } else {
            bst_insert_helper(node.right, val)
        }
    } else {
        // val == node.elem, do nothing (no duplicates)
    }
    
    fold acc(bst_node(node))
}
```

### Line 126: `requires acc(time_credit(), node_height(node)/1)`

**Purpose**: Need height(node) credits for recursive traversal.

### Lines 128-130: Postconditions about Bounds

```viper
    ensures tree_min(node) == old(tree_min(node)) || tree_min(node) == val
    ensures tree_max(node) == old(tree_max(node)) || tree_max(node) == val
```

**Purpose**:
- After insert, tree_min is either unchanged OR equals val (if val is new minimum)
- Same for tree_max
- This helps verify BST property is maintained

### Line 132: `ensures node_to_set(node) == old(node_to_set(node)) union Set(val)`

**Purpose**: Functional correctness - value is added to set.

### Lines 138-149: Insert Left Case

```viper
    if (val < node.elem) {
        if (node.left == null) {
            // Create new left child
            var new_node: Ref
            new_node := new(elem, left, right)
            new_node.elem := val
            new_node.left := null
            new_node.right := null
            fold acc(bst_node(new_node))
            node.left := new_node
        } else {
            // Recurse into left subtree
            bst_insert_helper(node.left, val)
        }
    }
```

**BST Logic**:
- `val < node.elem` → insert in left subtree
- If no left child → create one
- If has left child → recurse

### Lines 150-162: Insert Right Case

Symmetric to left case, for `val > node.elem`.

### Lines 163-165: Equal Case

```viper
    } else {
        // val == node.elem, do nothing (no duplicates)
    }
```

**Purpose**: BST doesn't store duplicates; value already exists.

### Line 167: `fold acc(bst_node(node))`

**Purpose**: 
- Re-establish bst_node predicate
- Verifier must prove BST property still holds
- The postconditions about tree_min/tree_max help here

---

## Lines 172-189: Height Functions

```viper
// -----------------------------------------
// Auxiliary definition of the height of a tree
function height(tree: Ref) : Int
    requires acc(bst(tree))
    ensures result >= 0
{
    unfolding acc(bst(tree)) in (
        tree.root == null ? 0 : 1 + node_height(tree.root)
    )
}

function node_height(node: Ref): Int
    requires node != null
    requires acc(bst_node(node))
    ensures result >= 1
{
    unfolding acc(bst_node(node)) in (
        1 + max(
            node.left == null ? 0 : node_height(node.left),
            node.right == null ? 0 : node_height(node.right)
        )
    )
}
// -----------------------------------------
```

### Line 174: `function height(tree: Ref) : Int`

**Purpose**: Height of entire tree.

### Line 176: `ensures result >= 0`

**Purpose**: Height is non-negative (empty tree has height 0).

### Lines 178-181: height Body

```viper
{
    unfolding acc(bst(tree)) in (
        tree.root == null ? 0 : 1 + node_height(tree.root)
    )
}
```

**Logic**:
- Empty tree (root == null): height 0
- Non-empty: 1 + height of root node

### Line 183: `function node_height(node: Ref): Int`

**Purpose**: Height of subtree rooted at node.

### Line 186: `ensures result >= 1`

**Purpose**: Non-null node has height at least 1.

### Lines 188-193: node_height Body

```viper
{
    unfolding acc(bst_node(node)) in (
        1 + max(
            node.left == null ? 0 : node_height(node.left),
            node.right == null ? 0 : node_height(node.right)
        )
    )
}
```

**Logic**:
- Height = 1 + max(left height, right height)
- Null children contribute 0

---

## Lines 196-218: Set Abstraction Functions

```viper
// -----------------------------------------
// Auxiliary function mapping every BST
// to the set of values it stores.
function to_set(tree: Ref): Set[Int]
    requires acc(bst(tree))
{
    unfolding acc(bst(tree)) in (
        tree.root == null ? Set[Int]() : node_to_set(tree.root)
    )
}

function node_to_set(node: Ref): Set[Int]
    requires node != null
    requires acc(bst_node(node))
{
    unfolding acc(bst_node(node)) in (
        Set(node.elem) union
        (node.left == null ? Set[Int]() : node_to_set(node.left)) union
        (node.right == null ? Set[Int]() : node_to_set(node.right))
    )
}
// -----------------------------------------
```

### Line 199: `function to_set(tree: Ref): Set[Int]`

**Viper Syntax**:
- `Set[Int]` is a mathematical set type
- Built-in type for specifications

**Purpose**: Abstract tree to set of values.

### Lines 201-205: to_set Body

```viper
{
    unfolding acc(bst(tree)) in (
        tree.root == null ? Set[Int]() : node_to_set(tree.root)
    )
}
```

**Logic**:
- Empty tree → empty set
- Non-empty → set from root node

### Line 207: `function node_to_set(node: Ref): Set[Int]`

**Purpose**: Set of values in subtree.

### Lines 212-217: node_to_set Body

```viper
{
    unfolding acc(bst_node(node)) in (
        Set(node.elem) union
        (node.left == null ? Set[Int]() : node_to_set(node.left)) union
        (node.right == null ? Set[Int]() : node_to_set(node.right))
    )
}
```

**Viper Syntax**:
- `Set(value)` creates singleton set
- `union` is set union

**Logic**: Set = {this value} ∪ left subtree set ∪ right subtree set

---

## Summary: Key BST Verification Concepts

### Recursive Predicates

```viper
predicate bst_node(self: Ref) {
    acc(self.elem) && acc(self.left) && acc(self.right) &&
    (self.left != null ==> acc(bst_node(self.left)) && ...)
}
```

- Predicate can reference itself
- Models tree structure naturally
- Permission to node = permission to entire subtree

### BST Property Encoding

```viper
    tree_max(self.left) < self.elem    // All left values smaller
    tree_min(self.right) > self.elem   // All right values larger
```

- Use helper functions to express ordering constraints
- Checked when folding the predicate

### Framing with old()

```viper
    ensures tree_min(node) == old(tree_min(node)) || tree_min(node) == val
```

- `old()` captures pre-state values
- Helps specify what can change and what's preserved

### Conditional Permissions

```viper
    (self.left != null ==> acc(bst_node(self.left)))
```

- Only have permission if condition is true
- Natural for nullable pointers

---

## Key Viper Concepts Summary

| Concept | Syntax | Purpose |
|---------|--------|---------|
| Recursive Predicate | `predicate p(x) { ... acc(p(y)) ... }` | Model recursive structures |
| Conditional Permission | `cond ==> acc(...)` | Nullable/optional fields |
| Set Type | `Set[T]`, `Set(val)`, `union` | Mathematical sets for specs |
| Reference Type | `Ref` | Pointer to heap object |
| Null Check | `x != null` | Guard before dereferencing |
| Height Function | Recursive with base cases | For runtime bounds |
