# Writing Specifications

**Core Chapter**: Introduction to PlusCal - the programming-like DSL that compiles to TLA+ for easier specification writing.

## PlusCal Overview
PlusCal is a DSL created by Leslie Lamport in 2009 to make TLA+ more accessible. It provides programming-like syntax that translates to TLA+ actions, making it easier to learn formal specification.

**Basic Structure:**
```tla+
---- MODULE name ----
EXTENDS Integers, TLC

(* --algorithm name
variables
  x = 2;
  y = TRUE;

begin
  A:
    x := x + 1;
  B: 
    x := x + 1;
    y := FALSE;
end algorithm; *)
====
```

## Key Concepts

### Labels - Units of Atomicity
Labels represent what happens in a single system step. Everything in a label is atomic.

**Critical Design Choice:**
- `Label1: x := Sum(seq);` - Summation is instantaneous 
- vs. separate labels for each step - allows interruption

**Label Rules:**
1. All algorithms must begin with a label
2. All statements must belong to a label  
3. Each variable can only be updated once per label
4. While statements must begin with a label
5. Macros and `with` cannot contain labels
6. `goto` must be followed by a new label
7. If any branch in a block has a label, the end must be followed by a label

### Variable Updates
- **Assignment**: `:=` for updating existing variables
- **Simultaneous assignment**: `||` for multiple updates in one label
```tla+
Label:
  seq[1] := seq[1] + 1 ||
  seq[2] := seq[2] - 1;
```

### PlusCal Constructs

**Control Flow:**
```tla+
if Expr then
  skip;
elsif Expr2 then  
  skip;
else
  skip;
end if;
```

**Loops (non-atomic):**
```tla+
Sum:
  while i <= Len(seq) do
    x := x + seq[i];
    Inc:
      i := i + 1;
  end while;
```

**Macros (textual substitution):**
```tla+
macro inc(var) begin
  if var < 10 then
    var := var + 1;
  end if;
end macro;
```

**Temporary bindings:**
```tla+
with tmp_x = x, tmp_y = y do
  y := tmp_x;
  x := tmp_y;
end with;
```

**Other statements:**
- `skip` - no-op
- `assert expr` - immediate failure if false
- `goto L` - jump to label L

## Multiple Starting States
Variables can be nondeterministic:
```tla+
variable seq \in {<<1, 2, 3, 2>>, <<1, 2, 3, 4>>};
```
TLC tests all possible starting combinations.

**Scaling example:**
```tla+
S == 1..10
variable seq \in S \X S \X S \X S;  // 10,000 test cases
```

## Translation Process
1. Write PlusCal in `(* --algorithm ... *)`
2. Translate via menu or Ctrl+T/Cmd+T
3. Generated TLA+ appears below the comment block
4. TLC runs the generated TLA+, not the PlusCal

## Common Patterns
- **Algorithm template**: variables → define block → begin → labels
- **Testing multiple inputs**: Use set membership `\in` for variables
- **Broad coverage**: Generate large test sets with Cartesian products
- **Atomic vs interruptible**: Use label placement to control concurrency

## Critical Gotchas
- Use `:=` for assignment, `=` for equality
- Each variable can only be updated once per label
- While loops are non-atomic (each iteration is separate step)
- Must translate PlusCal before running TLC
- Labels determine what can be interrupted by concurrency 