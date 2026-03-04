

# LTLf and Finite Automata in Norm-Guided Planning


This project integrates temporal norms into a classical planning framework by compiling temporal logic specifications into finite-state automata and synchronously composing them with a planner’s transition system.

The core idea is simple but powerful:

Temporal constraints over plans can be enforced incrementally during search, rather than verified post hoc over completed plans.

Instead of generating a plan and checking it afterwards, we ensure that every action considered during search already respects the specified normative constraints.

Motivation

This work addresses a practical architectural problem.

We use a Haskell-based domain-specific language (DSL) that interfaces with a C++ classical planner (e.g., Fast Downward). The C++ planner owns the search tree and execution paths. The Haskell DSL defines the domain and actions but does not have access to the evolving search history.

This raises a fundamental question:

How can we constrain action generation using Linear Temporal Logic (LTL) formulas if we do not have access to execution traces?

Since temporal logic is naturally defined over traces, and the DSL cannot observe traces directly, we must enforce temporal constraints without direct access to history.

Approach

The solution is to compile Linear Temporal Logic over finite traces (LTLf) into finite-state automata.

At runtime:

After a potential action is executed,

A snapshot of the resulting world state is extracted,

The norm automaton transitions based on that snapshot,

The automaton signals one of:

Violation

Waiting

Satisfaction

If a violation state is reached, the action is deemed inadmissible and pruned from the search.

This effectively transforms temporal constraints into state-based admissibility checks, allowing normative filtering even though the DSL has no access to the full execution trace.

Conceptually, we construct the synchronous product of:

The planning transition system, and

The norm automaton derived from an LTLf formula.

State Mutation and Backtracking

A significant engineering challenge arises from state mutation.

The Effect monad provides IO capabilities and internally uses IORefs to manage mutable planner state. This design yields a clean interface for classical planning but complicates norm enforcement.

If an action:

Mutates the world state,

Advances the norm automaton,

And is later found to violate a temporal constraint,

then the system must revert to the original state. Without proper rollback, the planner’s internal state becomes inconsistent.

Because the DSL does not provide built-in variable backtracking, we introduce an explicit snapshot-and-restore mechanism to ensure:

Norm violations do not leave residual side effects.

The planner remains semantically consistent.

Search remains sound under temporal constraints.
------------------------------------------------------------------------------
1. The Planning Setting
------------------------------------------------------------------------------

A classical planner searches for a finite sequence of actions:

    a0, a1, a2, ..., an

that transforms an initial state s0 into a state satisfying a goal condition.

Each action induces a transition:

    si --ai--> si+1

A plan is therefore a finite trace:

    s0, s1, s2, ..., sn

Standard planners enforce:
    - Action preconditions
    - Goal conditions

However, they do not natively enforce *temporal constraints*, such as:

    - "Safety must always hold."
    - "A task must eventually be completed."
    - "Condition A must hold until condition B occurs."
    - "Event X must occur before event Y."

These are naturally expressed in temporal logic. And are inescapable for planning in a normatively constrained domain

------------------------------------------------------------------------------
2. Linear Temporal Logic over Finite Traces (LTLf)
------------------------------------------------------------------------------

LTLf (Linear Temporal Logic over finite traces) is a formal language for
specifying temporal properties of *finite* sequences of states.

Unlike classical LTL (which is interpreted over infinite traces), LTLf is
interpreted over finite sequences:

    s0, s1, ..., sn

This makes LTLf particularly appropriate for planning, since plans are finite.

LTLf includes temporal operators such as:

    X φ        (Next)
    F φ        (Eventually)
    G φ        (Always)
    φ U ψ      (Until)
    ¬φ         (Negation)
    φ ∧ ψ      (Conjunction)
    φ ∨ ψ      (Disjunction)

Semantics are defined relative to positions within a finite trace.

For example:

    F φ

means that φ holds at some state si in the trace.

    G φ

means that φ holds at every state of the trace.

    φ U ψ

means that ψ must eventually hold, and φ must hold at all states prior
to the first occurrence of ψ.

------------------------------------------------------------------------------
3. Why We Compile LTLf to Finite Automata
------------------------------------------------------------------------------

Directly evaluating temporal formulas over traces during search is expensive
and conceptually awkward, because it requires reasoning over prefixes of
potentially long execution histories.

Instead, we exploit the following fundamental result:

    For every LTLf formula φ, there exists a finite automaton Aφ such that
    a finite trace satisfies φ if and only if that trace is accepted by Aφ.

This means:

    Temporal logic over traces
        ⇔
    Language recognition by a finite automaton

Thus, instead of reasoning about formulas over histories, we can reason about
automaton states.

------------------------------------------------------------------------------
4. What the Automaton Represents
------------------------------------------------------------------------------

The automaton encodes the "progress" of a temporal formula.

Each automaton state summarises:

    - Which sub-obligations of the temporal formula remain to be satisfied
    - Whether a violation has occurred

The automaton consumes, at each step, a *snapshot* of the world state.

A snapshot is a set of atomic propositions that are true in the current state,
for example:

    { APSafety, APTaskCompletion }

The transition function:

    δ : Q × Snapshot → Q

advances the automaton state based on which propositions hold after each action.

The automaton may contain:

    - Normal states (norm still satisfiable)
    - Accepting states (norm satisfied at end of trace)
    - Violation states (norm irreparably broken)

In our norm-enforcement setting, violation states are treated as dead states
and are pruned immediately during search.

------------------------------------------------------------------------------
5. Synchronous Product with the Planner
------------------------------------------------------------------------------

Conceptually, we construct the synchronous product of:

    (1) The planning transition system
    (2) The norm automaton

The combined state space becomes:

    (world_state, automaton_state)

For each candidate action:

    1. The world transitions to a successor state.
    2. A snapshot is extracted.
    3. The automaton transitions accordingly.
    4. If the automaton reaches a violation state, the transition is rejected.

Thus, norm enforcement reduces to:

    State-based admissibility filtering

rather than trace-based verification.

------------------------------------------------------------------------------
6. Why LTLf (Not Full LTL)
------------------------------------------------------------------------------

Classical LTL assumes infinite traces and is typically compiled into Büchi
automata with acceptance conditions based on infinite recurrence.

Planning problems, however, produce finite traces.

LTLf is therefore strictly more appropriate, because:

    - Acceptance is defined at the end of a finite trace.
    - The resulting automata are finite automata (DFA/NFA),
      not Büchi automata.
    - No reasoning about infinite repetition is required.

In this module, temporal norms are interpreted over finite plans.

------------------------------------------------------------------------------
7. Practical Implications for This Module
------------------------------------------------------------------------------

In this implementation:

    - Temporal formulas are represented explicitly (TemporalFormula).
    - Relevant atomic propositions are extracted from world states.
    - A deterministic norm automaton tracks compliance.
    - The planner state is augmented with an automaton state variable.
    - Actions are wrapped so that transitions leading to violations are pruned.

This ensures:

    ✔ All generated plans satisfy the temporal norms by construction.
    ✔ No post-hoc trace checking is required.
    ✔ Norms can be composed modularly by combining automata.

------------------------------------------------------------------------------
8. Conceptual Summary
------------------------------------------------------------------------------

LTLf provides a declarative way to specify temporal norms over plans.

Finite automata provide an operational mechanism to enforce those norms
incrementally during search.

The core theoretical bridge is:

    LTLf formula φ
        ⇓ (compilation)
    Deterministic finite automaton Aφ
        ⇓ (synchronous composition)
    Norm-guided planning

This architecture cleanly separates:

    - Domain dynamics (world transitions)
    - Normative constraints (automaton progression)

while preserving correctness and modularity.

================================================================================



