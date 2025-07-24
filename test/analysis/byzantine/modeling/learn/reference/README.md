# TLA+ Tutorial Reference

## Purpose

This folder contains condensed summaries of the complete [Learn TLA+ tutorial](https://learntla.com/) optimized for AI context loading and rapid knowledge restoration.

## Project Objectives

**Goal**: Create a comprehensive, ultra-compact TLA+ knowledge base that enables an AI assistant to answer TLA+ questions with certainty rather than guessing or hallucinating.

**Method**: 
1. Systematically review every chapter of the learntla.com tutorial
2. Extract core concepts, syntax patterns, and critical examples
3. Condense into ~200-300 word summaries per chapter
4. Include minimal working code examples for each concept
5. Cross-reference with existing resources (summary-standalone.pdf)

## Integration with Existing Resources

- **`../summary-standalone.pdf`** - TLA+ cheat sheet with syntax quick reference
- **`../DieHard/`** - Basic TLA+ example (water jug puzzle)
- **`../TCommit/`** - Two-phase commit example (distributed systems)

This reference augments these with systematic conceptual understanding from the full tutorial.

## Usage Pattern

When helping with TLA+ questions:
1. Load relevant chapter summaries into context
2. Reference syntax from cheat sheet if needed
3. Apply knowledge to specific modeling questions
4. Provide guidance based on tutorial-verified best practices

## File Organization

```
reference/
├── README.md           # This file
├── STATUS.md           # Progress tracking and chapter checklist
├── 01-conceptual.md    # Conceptual overview chapter
├── 02-setup.md         # Installation and tooling
├── 03-core-*.md        # Core TLA+ concept chapters
├── 04-topics-*.md      # Advanced topics chapters
├── 05-examples-*.md    # Example specifications
└── 99-integration.md   # Cross-references and patterns
```

## Success Criteria

Project complete when:
- ✅ All learntla.com chapters summarized
- ✅ Key syntax patterns captured with examples  
- ✅ Common pitfalls and best practices documented
- ✅ AI can answer TLA+ questions without guessing
- ✅ Knowledge integrates seamlessly with MyCHIPs modeling work

This creates a reliable TLA+ expertise foundation for the broader Byzantine fault tolerance modeling project. 