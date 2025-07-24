# Structured Data

**Core Chapter**: Functions as the foundation of TLA+ data structures - sequences and structs are syntactic sugar for the mathematical function type.

## Structures (Structs)
Hash-map like data with named fields:
```tla+
struct == [a |-> 1, b |-> {}]
struct["a"] = 1  // or struct.a = 1
```

**Set of structs:**
```tla+
BankTransactionType == [acct: Accounts, amnt: 1..10, type: {"deposit", "withdraw"}]
// Creates all possible combinations: 3 × 10 × 2 = 60 elements
```

**Getting keys:** `DOMAIN struct` returns set of all keys.

## Functions - The Real Foundation
Mathematical mappings from domain set to codomain set:
```tla+
F == [x \in S |-> expr]           // Function definition
Prod == [x, y \in S |-> x * y]    // Multiple parameters
F[value]                          // Function call
DOMAIN F                          // Get domain set
```

**Key insight:** Sequences and structures are just special cases of functions:
- **Sequence**: Function where domain is `1..n`
- **Structure**: Function where domain is set of strings

**Function notation:**
```tla+
x :> y              // Single-value function [s \in {x} |-> y]
f @@ g              // Merge functions (f takes precedence for shared keys)
```

## Function Sets
Sets of all functions with specific domain/codomain:
```tla+
[S -> T]            // All functions: domain S, values in T
[Tasks -> SUBSET CPUs]  // Each task maps to subset of CPUs
```

**Size calculation:** `[A -> B]` has `|B|^|A|` elements.

**Examples:**
- Server status: `[Server -> {"online", "booting", "offline"}]`
- Directed graph: `[Node \X Node -> BOOLEAN]`
- Resource allocation: `[Resource -> User \union {NULL}]`

## Practical Examples

### Task Assignment
```tla+
variables
  assignments = [t \in Tasks |-> {}]

// Assign CPU to task
assignment[t] := assignment[t] \union {cpu}

// Invariant: No shared CPUs
OnlyOneTaskPerCpu ==
  \A t1, t2 \in Tasks:
    (t1 # t2) => assignments[t1] \intersect assignments[t2] = {}
```

### Sequence Sorting
```tla+
Sort(seq) ==
  CHOOSE sorted \in [DOMAIN seq -> Range(seq)]:
    /\ \A i \in DOMAIN seq:
        CountMatching(seq, seq[i]) = CountMatching(sorted, seq[i])
    /\ IsSorted(sorted)

CountMatching(f, val) ==
  Cardinality({key \in DOMAIN f: f[key] = val})
```

## State Sweeping with Function Sets
Use function sets for parameterizable sequence lengths:
```tla+
// Instead of hardcoded: seq \in S \X S \X S \X S
CONSTANT Size
variable seq \in [1..Size -> S]

// State sweeping - vary length dynamically:
variable 
  n \in 1..Size;
  seq \in [1..n -> S];  // Tests all lengths up to Size
```

## Critical Distinctions
**Function definition vs function set:**
- `[x \in S |-> expr]` - Single function
- `[S -> T]` - Set of all functions

**Syntax gotchas:**
- Function: `[x \in S |-> T]` (with `|->`)
- Function set: `[S -> T]` (with `->`)
- Struct: `[key |-> val]` (with `|->`)
- Struct set: `[key: ValueSet]` (with `:`)

## Key Unification
All TLA+ collections are built on two primitives:
1. **Sets** - unordered, unique collections
2. **Functions** - mathematical mappings

Everything else (sequences, structures) is syntactic sugar for functions with specific domain patterns.

## Common Patterns
- **Function as variable**: `assignments \in [Tasks -> SUBSET CPUs]`
- **Dynamic domains**: `[1..n -> Values]` for variable-length sequences
- **Merge operations**: `f @@ g` for combining functions
- **Domain inspection**: `DOMAIN f` for getting valid inputs
- **State sweeping**: Use variables to control function domain sizes 