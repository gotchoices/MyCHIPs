# Concurrency

**Core Chapter**: Multi-process systems where independent agents interact - the primary advantage of formal methods over traditional testing.

## Processes
Agents of concurrency representing OS processes, threads, machines, or even people. Basic syntax:
```tla+
process writer = 1
begin
  AddToQueue:
    queue := Append(queue, 1);
end process;
```

**Key Rules:**
- All processes must have comparable types (all integers, strings, etc.) or model values
- Different processes cannot share label names
- `pc` becomes a function from process values to strings (`pc[0]`, `pc[1]`)

## Process Sets
Multiple instances of the same process type:
```tla+
Writers == {1, 2, 3}
process writer \in Writers
begin
  AddToQueue:
    queue := Append(queue, self);  // self = process value
end process;
```

**`self` keyword**: Retrieves the value of the process within a process set.

## Control Flow Constructs

### `await` - Blocking Conditions
```tla+
await queue = <<>>;  // Label only runs when condition is true
await queue # <<>>;  // Blocks until non-empty
```
Prevents label execution until condition evaluates to true. If no labels can run → deadlock.

### `goto` - Infinite Loops
```tla+
ReadFromQueue:
  if queue # <<>> then
    total := total + Head(queue);
    queue := Tail(queue);
  end if;
  goto ReadFromQueue;  // Equivalent to while TRUE
```

### Local Variables
Process-specific variables not visible to other processes:
```tla+
process writer \in Writers
variables i = 0;  // Local to each writer instance
begin
  // ... use i for bookkeeping
```

**Limitations:** Cannot be used in `define` blocks (no typechecking, helper operators).

## Concurrency Patterns

### Race Conditions
Classic example - non-atomic counter increment:
```tla+
process thread \in Threads
variables tmp = 0;
begin
  GetCounter: tmp := counter;
  IncCounter: counter := tmp + 1;
end process;
```
Problem: Both threads read `counter = 0`, both set to 1.

### Mutual Exclusion
```tla+
variables lock = NULL;

process thread \in Threads
begin
  GetLock:
    await lock = NULL;
    lock := self;
  CriticalSection:
    // ... protected operations
  ReleaseLock:
    lock := NULL;
```

## State Space Explosion
With `n` processes having `m` actions each, there are `(n×m)!` possible orderings. Concurrency is a major source of exponential state growth.

## Procedures (Advanced)
Reusable code blocks with labels (more complex than macros):
```tla+
procedure Name(arg1, ...)
variables var1 = ...
begin
  Label1: // stuff
  Label2: return;
end procedure;

// Usage
call Name(val1, ...);
```

**Requirements:**
- Must extend `Sequences` for call stack
- Must end with `return`
- Call must be followed by label or goto

## Critical Insights
- **Everything can crash**: TLA+ assumes worst-case scenarios including infinite stuttering
- **Deadlock detection**: When no process can make progress
- **Race conditions**: Rare orderings that violate properties - why concurrency is hard
- **Fairness**: Required to prevent infinite stuttering (`fair process`)

## Gotchas
- Race conditions appear in very specific orderings (hard to find, hard to reproduce)
- Stuttering can mask liveness property violations
- State explosion makes large concurrent systems expensive to verify
- Local variables can't be used in invariants or define blocks 