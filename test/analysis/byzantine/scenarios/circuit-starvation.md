# Circuit Starvation Attack

## Overview

### Attack Objective
Degrade network trading capacity by creating unresolvable promised lifts that lock resources on non-colluding nodes.

### Required Capabilities
- Multiple colluding nodes (>50% of circuit)
- Ability to participate in lift discovery
- Coordination for synchronized withdrawal
- **Critical Addition: Social Trust Requirements**
  - Established real-world business/social relationships
  - Legitimate trading history with honest nodes
  - Multiple trust relationships per colluding node
  - Demonstrated credit worthiness
  - Regular value exchange patterns

### Expected Impact
- Locked credit capacity on honest nodes
- Trading uncertainty due to unresolved promises
- Resource consumption from stuck transactions
- Reduced network efficiency

### Business Motivation
- Damage competitor trading capacity
- Create uncertainty in credit system
- Force manual intervention costs
- Demonstrate system vulnerability

### Attack Cost Analysis
- **Social Investment**:
  - Time to build legitimate relationships
  - Real business/social presence establishment
  - Regular trading activity maintenance
  - Credit history development

- **Value Requirements**:
  - Actual value locked in relationships
  - Working capital for trading
  - Business operation costs
  - Relationship maintenance expenses

- **Permanent Losses**:
  - Burned trust relationships
  - Damaged business reputation
  - Lost trading partnerships
  - Potential legal consequences

## Component Attacks

### Primary Attack Vectors
1. [Delayed Vote Attack](../attacks/delayed-vote.md)
   - Coordinated withholding of commit votes
   - Exploits timeout mechanisms
   - Prevents transaction resolution

2. [Selective Communication](../attacks/selective-communication.md)
   - Strategic offline behavior
   - Information asymmetry creation
   - Coordinated partition

3. [Deadbeat Attack](../attacks/deadbeat.md)
   - Multiple simultaneous node disappearance
   - Promise phase participation only
   - Resource locking through non-completion

### Novel Combination Aspects
- Uses majority control within circuit
- Exploits promise-to-commit gap
- Creates persistent unresolved state
- Targets business impact over direct value theft

## Detailed Flow

### Social Trust Barriers
```mermaid
graph TD
    A[Attack Prerequisites] --> B[Establish Real Business/Social Presence]
    B --> C[Build Multiple Trust Relationships]
    C --> D[Develop Trading History]
    D --> E[Lock Real Value]
    E --> F[Coordinate Attack]
    F --> G[Accept Permanent Losses]
    
    style B fill:#ffd,stroke:#666
    style C fill:#ffd,stroke:#666
    style D fill:#ffd,stroke:#666
    style E fill:#ffd,stroke:#666
```

### Attack Progression
```mermaid
sequenceDiagram
    participant H1 as Honest Node 1
    participant C1 as Colluding Node 1
    participant C2 as Colluding Node 2
    participant H2 as Honest Node 2
    participant C3 as Colluding Node 3

    Note over C1,C3: Colluding nodes coordinate
    C1->>H1: Initiate lift discovery
    H1->>C2: Route discovery
    C2->>H2: Route discovery
    H2->>C3: Route discovery
    C3->>C1: Complete circuit

    Note over C1,C3: Circuit formed with colluding majority
    C1->>H1: Promise phase
    H1->>C2: Promise phase
    C2->>H2: Promise phase
    H2->>C3: Promise phase
    C3->>C1: Promises complete

    Note over C1,C3: Colluding nodes go offline
    H1--xC1: Commit attempt fails
    H2--xC2: Commit attempt fails
    H2--xC3: Commit attempt fails

    Note over H1,H2: Honest nodes left with<br/>unresolvable promises
```

### Social Response Flow
```mermaid
sequenceDiagram
    participant HN as Honest Node
    participant TP as Trading Partner
    participant ON as Other Networks
    participant LE as Legal Entities

    HN->>TP: Direct Contact (Phone/Email)
    TP->>HN: Confirm Unresponsiveness
    HN->>ON: Alert Trading Community
    ON->>TP: Share Attack Information
    HN->>LE: Consider Legal Action
    LE->>ON: Document Bad Actors
```

### State Transitions
1. **Discovery Phase**
   - Colluders participate normally
   - Ensure circuit has colluding majority
   - Position colluders strategically

2. **Promise Phase**
   - All nodes sign conditional commitments
   - Honest nodes lock resources
   - Promises recorded in tallies

3. **Attack Execution**
   - Colluders withdraw simultaneously
   - Prevent commit phase completion
   - Leave promises in limbo

## Impact Analysis

### Direct Financial Impact
- No immediate value transfer
- Potential opportunity costs
- Recovery process expenses

### Operational Disruption
- Locked credit capacity
- Uncertain tally states
- Manual intervention required
- Reduced trading efficiency

### Resource Consumption
- Database space for promises
- Network capacity for retries
- Administrative overhead
- Investigation costs

### Trust/Reputation Effects
- Uncertainty in credit system
- Reduced participant confidence
- Trust network degradation
- Protocol reliability questions

### Social Trust Impact
- **Relationship Damage**:
  - Broken business partnerships
  - Lost trading opportunities
  - Community trust violations
  - Reputation network effects

- **Detection Advantages**:
  - Direct communication channels
  - Real-world identity verification
  - Community information sharing
  - Social pressure mechanisms

- **Recovery Channels**:
  - Existing business relationships
  - Alternative contact methods
  - Legal recourse availability
  - Community support networks

## Detection Points

### Observable Indicators
- Multiple nodes offline post-promise
- Pattern of unresolved promises
- Coordinated timing of failures
- Circuit composition anomalies

### Social Indicators
- Unusual relationship formation patterns
- Accelerated trust building attempts
- Inconsistent trading behaviors
- Multiple relationship establishments

### Monitoring Requirements
- Circuit participant diversity
- Promise resolution timing
- Node reliability metrics
- Coordination pattern detection

## Mitigation Analysis

### Existing Mitigation Interaction
1. **Timeout Mechanisms**
   - Help but don't fully resolve
   - May take too long
   - Resource still locked

2. **Majority Consensus**
   - Ineffective when attackers have circuit majority
   - Doesn't prevent promise phase
   - Can't force resolution

3. **Reputation Systems**
   - Can identify participants after the fact
   - Doesn't prevent initial attack
   - Helps prevent repeat attacks

### Social Trust Layer
1. **Relationship Requirements**
   - Real-world identity verification
   - Established business connections
   - Regular trading patterns
   - Community reputation

2. **Value Lock**
   - Actual asset commitment
   - Ongoing business operations
   - Trading history requirements
   - Relationship investment

3. **Social Consequences**
   - Permanent relationship damage
   - Community-wide reputation loss
   - Legal liability exposure
   - Business opportunity costs

### Mitigation Rating: EFFECTIVELY MITIGATED
- **Primary Defense**: Social trust requirements
- **Secondary Defense**: Technical consensus mechanisms
- **Remaining Exposure**: Temporary resource locking
- **Edge Cases**: High-value, short-term relationships

**Rating Justification**:
1. Attack requires extensive social investment
2. High cost-to-impact ratio for attackers
3. Clear attribution through real relationships
4. Strong social recovery mechanisms
5. Permanent consequences for attackers

### Gaps Identified
1. No circuit composition requirements
2. Lack of promise phase protections
3. Insufficient resource locking limits
4. Missing coordination detection

### Recommended Improvements
1. **Circuit Requirements**
   - Minimum honest node percentage
   - Reputation-based participation limits
   - Geographic/domain diversity rules

2. **Promise Phase Protection**
   - Resource reservation limits
   - Progressive commitment stages
   - Collateral requirements

3. **Resolution Mechanisms**
   - Automatic timeout cleanup
   - Forced resolution protocols
   - Resource recovery procedures

## Recovery Process

### Immediate Response
1. Identify affected tallies
2. Document promise chain
3. Notify affected parties
4. Begin timeout countdown

### Resource Recovery
1. Wait for timeout completion
2. Release locked resources
3. Update tally states
4. Record attack pattern

### Social Recovery Steps
1. Contact trading partners directly
2. Alert connected community members
3. Document relationship violations
4. Consider legal remedies
5. Update trust policies

### Long-term Prevention
1. Update circuit formation rules
2. Enhance monitoring systems
3. Adjust timeout parameters
4. Improve coordination detection

## Open Questions

1. **Circuit Formation**
   - Optimal honest node percentage?
   - How to verify node independence?
   - Balance between security and efficiency?

2. **Resource Management**
   - Maximum safe promise duration?
   - Automatic vs. manual cleanup?
   - Resource reservation limits?

3. **Attack Evolution**
   - Potential attack variations?
   - Other resource targeting methods?
   - Combined attack patterns?

### Social Trust Dynamics
- How to balance trust requirements vs. network growth?
- What defines a legitimate trading relationship?
- How to measure relationship authenticity?
- What are optimal trust building timeframes? 

## Partition Healing Mechanism

### Original Circuit Scenario
```mermaid
graph LR
    subgraph "Honest Minority"
        A -->|"Promise"| B
        B -->|"Promise"| C
    end
    
    subgraph "Majority Partition"
        D -->|"Promise"| E
        E -->|"Promise"| F
        F -->|"Promise"| G
    end
    
    C -->|"Margin<br/>Promise"| D
    G -->|"Margin<br/>Promise"| A
    
    I[Insurer I<br/>Referee]
    
    style D fill:#f88,stroke:#666
    style E fill:#f88,stroke:#666
    style F fill:#f88,stroke:#666
    style G fill:#f88,stroke:#666
    style I fill:#8f8,stroke:#666
```

### Initial Problem
1. **Circuit Composition**:
   - Minority (A,B,C): Honest/accessible
   - Majority (D,E,F,G): Malicious or partitioned
   - Critical promises at margins:
     * G → A (first node)
     * C → D (partition boundary)

2. **Voting Issues**:
   - Participant-based voting fails
   - Majority can force outcome
   - Minority resources locked
   - No resolution mechanism

### Insurer-Based Solution

#### Setup Phase
```mermaid
sequenceDiagram
    participant M as Minority Nodes
    participant I as Insurer
    participant P as Promise Phase
    
    P->>I: Include as primary referee
    P->>M: Accept insurer authority
    Note over I,M: Cryptographic commitment
    I->>M: Acknowledge role
```

1. **Insurer Role**:
   - Designated primary referee
   - Agreed during promise phase
   - Cryptographically committed
   - Timeout authority

#### Healing Process
```mermaid
sequenceDiagram
    participant M as Minority
    participant I as Insurer
    participant J as Majority
    
    Note over M,J: Partition occurs
    M->>I: Request timeout evaluation
    I-->>M: Verify extended outage
    I->>M: Issue veto signature
    Note over M: Resources released
    
    Note over J: Later reconnection
    J->>I: Discover veto
    I->>J: Provide veto proof
    Note over J: Must reconcile
```

#### Margin Resolution
```mermaid
graph LR
    subgraph "Before"
        G1[G] -->|"Voided<br/>Promise"| A1[A]
        C1[C] -->|"Voided<br/>Promise"| D1[D]
    end
    
    subgraph "After"
        G2[G] -->|"Chit"| I2[Insurer]
        I2 -->|"Chit"| D2[D]
    end
```

1. **Margin Imbalance**:
   - G ahead (owes nothing, promised to A)
   - D behind (owed by C, promise voided)
   - Need value transfer mechanism

2. **Resolution Process**:
   - I creates tallies with G and D
   - G→I chit validated by majority result
   - I→D chit balances the equation
   - All parties made whole

### Implementation Requirements

1. **Protocol Changes**:
   - Insurer as primary referee
   - Timeout evaluation criteria
   - Veto mechanism
   - Margin resolution process

2. **Cryptographic Needs**:
   - Insurer authority validation
   - Timeout proof mechanism
   - Veto signature format
   - Chit validation chain

3. **State Management**:
   - Original lift reference
   - Timeout evidence
   - Veto records
   - Resolution tracking

### Advantages

1. **Simplification**:
   - Single authoritative referee
   - Clear resolution path
   - Deterministic outcome
   - Automatic healing

2. **Fairness**:
   - Minority protected
   - Majority can complete
   - Value preserved
   - Minimal penalties

3. **Prevention**:
   - Discourages partitioning
   - Clear consequences
   - Built-in resolution
   - Automatic healing

### Limitations

1. **Trust Requirements**:
   - Insurer must be reliable
   - Pre-agreed authority
   - Cannot be partitioned
   - Must be available

2. **Operational Impact**:
   - New tally creation
   - Forced relationships
   - Additional overhead
   - Complex state tracking

### Conclusions

1. **Prevention vs Cure**:
   - Better to prevent with proper referee
   - Healing mechanism as backup
   - Clear resolution path needed
   - Trust relationships critical

2. **Design Implications**:
   - Prefer single trusted referee
   - Build in timeout handling
   - Plan for margin resolution
   - Consider forced relationships

3. **Future Considerations**:
   - Multiple insurer options
   - Automated resolution
   - Reputation effects
   - Prevention mechanisms 