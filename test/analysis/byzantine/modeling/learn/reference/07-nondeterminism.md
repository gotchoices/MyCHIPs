# Nondeterminism

**Core Chapter**: Breaking from deterministic algorithms to model randomness, user input, sensor readings, and uncertain system behaviors.

## What is Nondeterminism?
Nondeterminism allows specs to choose between multiple possible behaviors at a single point. Unlike deterministic specs (fixed behavior from each starting state), nondeterministic specs create multiple execution branches.

**Use cases:**
- Randomness (dice rolls, random failures)
- Interactive systems (unknown user actions)
- Sensor readings (unknown but bounded values)
- External system responses
- Concurrent execution ordering

## Core Constructs

### Nondeterministic `with`
Choose any value from a set:
```tla+
with roll \in 1..6 do
  sum := sum + roll;
end with;
```

**Creates 6 branches** - model checker explores all possibilities.

**Mixed assignments:**
```tla+
with
  x \in BOOLEAN,    // nondeterministic
  y \in 1..10,      // nondeterministic  
  z = TRUE          // deterministic
do
  // ... logic using x, y, z
end with;
```

**From variable sets:**
```tla+
with thread \in sleeping do
  sleeping := sleeping \ {thread};
end with;
```

⚠️ **Warning**: If variable set is empty, `with` blocks (can cause deadlock).

### `either-or` Branches
Nondeterministic control flow:
```tla+
either
  approve_pull_request();
or
  request_changes();
or
  reject_request();
end either;
```

Creates 3 execution branches. Labels allowed inside branches.

## Abstraction Power

### Abstracting Implementation Details
Model high-level outcomes without implementation complexity:

**Instead of modeling:**
- Authorization policies
- Resource reservation logic  
- CI process details
- Error handling code

**Use nondeterminism:**
```tla+
macro request_resource(r) begin
  either
    reserved := reserved \union {r};  // Success
  or
    skip;                            // Failure (any reason)
  end either;
end macro;
```

### Modeling Error Types
Control level of detail:
```tla+
macro request_resource(r) begin
  either
    reserved := reserved \union {r};
    failure_reason := "";
  or
    with reason \in {"unauthorized", "in_use", "other"} do
      failure_reason := reason;
    end with;
  or
    skip;  // Unknown error type
  end either;
end macro;
```

### User Input Simulation
Model all possible user actions:
```tla+
RequestType == [from: Client, type: {"GET", "POST"}, params: ParamType]

with request \in RequestType do
  if request.type = "GET" then
    // get logic
  elsif request.type = "POST" then  
    // post logic
  else
    assert FALSE;  // Spec error
  end if;
end with;
```

## Practical Example: Calculator

Model user operating a calculator with bounded input:
```tla+
Calculator:
  while i < NumInputs do
    with x \in Digits do
      either
        sum := sum + x;    // Add
      or
        sum := sum - x;    // Subtract  
      or
        sum := sum * x;    // Multiply
      end either;
    end with;
    i := i + 1;
  end while;
```

### Finding Solutions
Use nondeterminism to discover paths to specific outcomes:

**Problem**: Can we reach 417 in 5 operations?
**Solution**: Add invariant `sum # 417` - if reachable, model checker fails and shows path!

```
Error trace: 0 → +1 → ×9 → ×6 → ×7 → -3 = 417
```

## State Space Impact

Nondeterminism dramatically increases state space:
- **Deterministic**: Single path from each starting state
- **Nondeterministic**: Multiple paths branch from each decision point
- **Concurrency**: Different orderings create more distinct states

**Example**: 3 operations × 3 operators = 27 possible execution sequences

## Common Patterns

### `either or skip`
Model optional actions:
```tla+
either
  do_optional_work();
or
  skip;  // Do nothing
end either;
```

### Failure Modeling  
```tla+
either
  normal_operation();
or
  // Various failure modes
  with error \in ErrorTypes do
    handle_error(error);
  end with;
end either;
```

### Bounded Resources
```tla+
with resource \in available_resources do
  either
    allocate(resource);
  or
    // Resource contention
    skip;
  end either;
end with;
```

## Key Benefits

1. **Higher abstraction**: Focus on system properties, not implementation details
2. **Comprehensive testing**: Explores all possible execution paths
3. **Early error detection**: Finds race conditions and edge cases
4. **Design validation**: Verifies system works under all possible inputs
5. **Solution discovery**: Can find paths to desired outcomes

## Critical Rules
- Model checker explores **ALL** nondeterministic choices
- Empty sets in `with` statements cause blocking/deadlock
- Use constants to bound state space (avoid infinite behaviors)
- Each `either` branch creates separate execution path
- Labels can appear inside `either` blocks but not `with` statements 