# TLA+ Language Reference Index

**Purpose**: Quick topic lookup across all TLA+ language summaries for efficient AI navigation.

## 📖 **Core Reading Order**
1. **[01-conceptual.md](01-conceptual.md)** - High-level overview and wire transfer example
2. **[02-operators-values.md](02-operators-values.md)** - Basic syntax and data types  
3. **[03-writing-specifications.md](03-writing-specifications.md)** - PlusCal introduction
4. **[04-writing-invariants.md](04-writing-invariants.md)** - Testing and verification
5. **[12-tla-plus.md](12-tla-plus.md)** - Pure TLA+ transition (after PlusCal foundation)

## 🔍 **Topic Quick Reference**

### **Language Fundamentals**
- **TLA+ vs PlusCal distinction** → [03-writing-specifications.md](03-writing-specifications.md), [12-tla-plus.md](12-tla-plus.md)
- **Basic operators** (`+`, `-`, `=`, `=>`, `/\`, `\/`) → [02-operators-values.md](02-operators-values.md)
- **Data types** (sets, sequences, functions, records) → [02-operators-values.md](02-operators-values.md), [06-structured-data.md](06-structured-data.md)

### **PlusCal Programming**
- **Variables and assignment** → [03-writing-specifications.md](03-writing-specifications.md)
- **Labels and atomicity** → [03-writing-specifications.md](03-writing-specifications.md), [08-concurrency.md](08-concurrency.md)  
- **Control flow** (`if`, `while`, `either`, `with`) → [03-writing-specifications.md](03-writing-specifications.md), [07-nondeterminism.md](07-nondeterminism.md)
- **Processes and concurrency** → [08-concurrency.md](08-concurrency.md)
- **Procedures and macros** → [08-concurrency.md](08-concurrency.md)

### **Pure TLA+ Features**
- **Actions and prime operators** → [11-action-properties.md](11-action-properties.md), [12-tla-plus.md](12-tla-plus.md)
- **EXCEPT operator** → [12-tla-plus.md](12-tla-plus.md)
- **Init, Next, Spec structure** → [12-tla-plus.md](12-tla-plus.md)
- **Helper actions** → [12-tla-plus.md](12-tla-plus.md)

### **Properties and Verification**
- **Invariants** → [04-writing-invariants.md](04-writing-invariants.md)
- **Temporal properties** (`[]`, `<>`, `~>`) → [09-temporal-properties.md](09-temporal-properties.md)
- **Action properties** (`[A]_v`, `<A>_v`) → [11-action-properties.md](11-action-properties.md)
- **Safety vs liveness** → [09-temporal-properties.md](09-temporal-properties.md)
- **Fairness** (weak/strong) → [09-temporal-properties.md](09-temporal-properties.md), [12-tla-plus.md](12-tla-plus.md)

### **Advanced Features**
- **Nondeterminism** (`with`, `either`) → [07-nondeterminism.md](07-nondeterminism.md)
- **Constants and models** → [05-parameterizing-specs.md](05-parameterizing-specs.md)
- **Recursive operators** → [10-more-operators.md](10-more-operators.md)
- **Higher-order operators** → [10-more-operators.md](10-more-operators.md)
- **LAMBDA expressions** → [10-more-operators.md](10-more-operators.md)
- **CASE statements** → [10-more-operators.md](10-more-operators.md)

### **Data Structures Deep Dive**
- **Functions as foundation** → [06-structured-data.md](06-structured-data.md)
- **Sequences** (`<<>>`, `Head`, `Tail`, `Append`) → [02-operators-values.md](02-operators-values.md), [15-standard-modules.md](15-standard-modules.md)
- **Sets** (`{}`, `\cup`, `\cap`, `\subseteq`) → [02-operators-values.md](02-operators-values.md)
- **Records** (`[h1 |-> v1, h2 |-> v2]`) → [06-structured-data.md](06-structured-data.md)
- **Function sets** (`[S -> T]`) → [06-structured-data.md](06-structured-data.md)

### **Module System**
- **EXTENDS** → [13-modules.md](13-modules.md)
- **INSTANCE** → [13-modules.md](13-modules.md)
- **Parameterized modules** → [13-modules.md](13-modules.md)
- **LOCAL definitions** → [13-modules.md](13-modules.md)

### **Standard Library**
- **Naturals, Integers** (arithmetic) → [15-standard-modules.md](15-standard-modules.md)
- **Sequences** (Head, Tail, Append) → [15-standard-modules.md](15-standard-modules.md)
- **FiniteSets** (Cardinality) → [15-standard-modules.md](15-standard-modules.md)
- **TLC** (Assert, Print) → [15-standard-modules.md](15-standard-modules.md)
- **Bags** (multisets) → [15-standard-modules.md](15-standard-modules.md)

### **Testing and Debugging**
- **Quantifiers** (`\A`, `\E`) → [04-writing-invariants.md](04-writing-invariants.md)
- **Implication patterns** (`=>`) → [04-writing-invariants.md](04-writing-invariants.md)
- **pc variable** → [04-writing-invariants.md](04-writing-invariants.md)
- **Error traces** → [04-writing-invariants.md](04-writing-invariants.md)
- **CHOOSE operator** → [02-operators-values.md](02-operators-values.md)

## 🚀 **Problem-Solving Quick Reference**

### **"How do I...?"**
- **Model randomness/uncertainty** → [07-nondeterminism.md](07-nondeterminism.md)
- **Handle concurrency** → [08-concurrency.md](08-concurrency.md)
- **Check system properties** → [04-writing-invariants.md](04-writing-invariants.md), [09-temporal-properties.md](09-temporal-properties.md)
- **Parameterize my spec** → [05-parameterizing-specs.md](05-parameterizing-specs.md)
- **Work with complex data** → [06-structured-data.md](06-structured-data.md)
- **Debug my specification** → [04-writing-invariants.md](04-writing-invariants.md), [15-standard-modules.md](15-standard-modules.md)

### **"What does X mean?"**
- **Symbols** (`'`, `[]`, `<>`, `~>`, `/\`, `\/`) → Search respective chapters above
- **Error messages** → [04-writing-invariants.md](04-writing-invariants.md), [12-tla-plus.md](12-tla-plus.md)
- **PlusCal translation** → [12-tla-plus.md](12-tla-plus.md)

## 📊 **File Statistics**
- **Total files**: 15 chapters + index
- **Total size**: ~59KB (~14.7K tokens)
- **Context usage**: ~7.4% of Claude's context window
- **Reading time**: All files easily fit in single context load 