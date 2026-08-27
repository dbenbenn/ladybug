/-
# The ladybug on the clock

A ladybug performs a simple symmetric random walk on the 12 fields of a clock,
starting at noon, and stops the moment it has visited every field.

**Claim.** It stops on the 3 o'clock field with probability `1 / 11`.

More generally, the last field visited is uniformly distributed over the eleven
fields other than the starting one.

Proof sketch (not formalised here).  Fix a target field `k ≠ 0`.  Since the walk
can only enter `k` through one of its two neighbours, `k` is the last field
visited iff the walk reaches both `k - 1` and `k + 1` before it ever reaches `k`.
Cutting the cycle open at `k` turns the walk into a simple random walk on a path
of 11 interior vertices with the two copies of `k` absorbing, and the probability
above is computed by gambler's ruin.  The dependence on the position of `k`
relative to the start cancels, leaving `1 / 11` for every `k ≠ 0`.
-/

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LadybugClock

/-! ## The walk -/

/-- The twelve fields of the clock, with noon identified with `0`. -/
abbrev Clock := ZMod 12

/-- A single step: `true` moves clockwise, `false` counter-clockwise. -/
def step (b : Bool) : Clock := if b then 1 else -1

/-- The position of the ladybug after `n` steps, driven by the coin flips `ω`.
It starts at noon. -/
def walk (ω : ℕ → Bool) : ℕ → Clock
  | 0 => 0
  | n + 1 => walk ω n + step (ω n)

/-- The fields visited up to and including time `n`. -/
def visited (ω : ℕ → Bool) (n : ℕ) : Finset Clock :=
  (Finset.range (n + 1)).image (walk ω)

/-- The walk driven by `ω` eventually visits every field. -/
def Covers (ω : ℕ → Bool) : Prop := ∃ n, visited ω n = Finset.univ

/-- The cover time: the first moment at which every field has been visited.
(Junk value `0` if the walk never covers the clock.) -/
noncomputable def coverTime (ω : ℕ → Bool) : ℕ :=
  sInf {n | visited ω n = Finset.univ}

/-- The field the ladybug stops on, i.e. the last field it visits. -/
noncomputable def lastField (ω : ℕ → Bool) : Clock := walk ω (coverTime ω)

/-! ## The driving measure

Rather than committing to a particular construction of the infinite product
measure, we characterise it: `μ` is a probability measure on coin-flip sequences
whose coordinates are independent and fair.  Specifying `μ` on cylinder sets
determines it, since the cylinders form a π-system generating the σ-algebra.

This is satisfied by Mathlib's infinite product of `Bernoulli 1/2` measures. -/

variable {μ : Measure (ℕ → Bool)} [IsProbabilityMeasure μ]

/-- The coordinates of `μ` are i.i.d. fair coin flips. -/
def IsFairCoinFlips (μ : Measure (ℕ → Bool)) : Prop :=
  ∀ (s : Finset ℕ) (f : ℕ → Bool),
    μ {ω | ∀ i ∈ s, ω i = f i} = (1 / 2 : ℝ≥0∞) ^ s.card

/-! ## Measurability -/

theorem measurable_walk (n : ℕ) : Measurable fun ω => walk ω n := by
  sorry

theorem measurableSet_lastField_eq (k : Clock) :
    MeasurableSet {ω | lastField ω = k} := by
  sorry

/-! ## The walk covers the clock almost surely -/

theorem ae_covers (hμ : IsFairCoinFlips μ) : ∀ᵐ ω ∂μ, Covers ω := by
  sorry

/-! ## Key structural lemma

`k` is the last field visited exactly when both of its neighbours are reached
strictly before `k` itself. -/

/-- The walk reaches `a` at some time at which it has not yet reached `k`. -/
def ReachesBefore (ω : ℕ → Bool) (a k : Clock) : Prop :=
  ∃ n, walk ω n = a ∧ ∀ m ≤ n, walk ω m ≠ k

theorem lastField_eq_iff (ω : ℕ → Bool) (hω : Covers ω) (k : Clock) (hk : k ≠ 0) :
    lastField ω = k ↔ ReachesBefore ω (k - 1) k ∧ ReachesBefore ω (k + 1) k := by
  sorry

/-! ## Main results -/

/-- **The last field visited is uniform on the eleven non-starting fields.** -/
theorem prob_lastField_eq (hμ : IsFairCoinFlips μ) (k : Clock) (hk : k ≠ 0) :
    μ {ω | lastField ω = k} = 1 / 11 := by
  sorry

/-- **The ladybug stops on the 3 o'clock field with probability `1 / 11`.** -/
theorem prob_stops_at_three (hμ : IsFairCoinFlips μ) :
    μ {ω | lastField ω = 3} = 1 / 11 := by
  refine prob_lastField_eq hμ 3 ?_
  decide

/-- The ladybug never stops where it started. -/
theorem prob_stops_at_noon (hμ : IsFairCoinFlips μ) :
    μ {ω | lastField ω = 0} = 0 := by
  sorry

end LadybugClock
