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

/-! ## Basic facts about `visited` and `coverTime` -/

theorem visited_succ (ω : ℕ → Bool) (n : ℕ) :
    visited ω (n + 1) = insert (walk ω (n + 1)) (visited ω n) := by
  simp [visited, Finset.range_add_one]

theorem zero_mem_visited (ω : ℕ → Bool) (n : ℕ) : (0 : Clock) ∈ visited ω n := by
  simp only [visited, Finset.mem_image]
  exact ⟨0, by simp, rfl⟩

theorem coverTime_mem (ω : ℕ → Bool) (hω : Covers ω) :
    visited ω (coverTime ω) = Finset.univ :=
  Nat.sInf_mem hω

/-- If `n` covers the clock and nothing before it does, then `n` is the cover time. -/
theorem coverTime_eq_of {ω : ℕ → Bool} {n : ℕ} (h : visited ω n = Finset.univ)
    (hlt : ∀ m < n, visited ω m ≠ Finset.univ) : coverTime ω = n := by
  have hmemS : n ∈ {j | visited ω j = Finset.univ} := h
  refine le_antisymm (Nat.sInf_le hmemS) ?_
  by_contra hcon
  push Not at hcon
  exact hlt _ hcon (Nat.sInf_mem ⟨n, hmemS⟩)

/-- On a walk that never covers the clock, `coverTime` takes its junk value. -/
theorem coverTime_eq_zero_of_not_covers {ω : ℕ → Bool} (h : ¬ Covers ω) : coverTime ω = 0 := by
  have : {n | visited ω n = Finset.univ} = ∅ := by
    ext n; simpa using fun hn => h ⟨n, hn⟩
  simp [coverTime, this]

/-- The ladybug never stops where it started: the start is visited at time `0`, so it
cannot be the field that completes the tour. -/
theorem lastField_ne_zero (ω : ℕ → Bool) (hω : Covers ω) : lastField ω ≠ 0 := by
  have hmem := coverTime_mem ω hω
  rcases Nat.eq_zero_or_pos (coverTime ω) with h0 | hpos
  · -- at time `0` only the starting field has been seen
    rw [h0] at hmem
    have hcard : (visited ω 0).card = 1 := by simp [visited]
    rw [hmem] at hcard
    simp at hcard
  · obtain ⟨m, hm⟩ : ∃ m, coverTime ω = m + 1 := ⟨coverTime ω - 1, by omega⟩
    intro hcon
    -- if the final field were `0` it was already visited, so `m` would already cover
    have hnot : visited ω m ≠ Finset.univ :=
      Nat.notMem_of_lt_sInf (show m < coverTime ω by omega)
    apply hnot
    have hins := visited_succ ω m
    rw [← hm] at hins
    rw [hins, show walk ω (coverTime ω) = (0 : Clock) from hcon,
      Finset.insert_eq_self.mpr (zero_mem_visited ω m)] at hmem
    exact hmem

/-! ## Measurability -/

theorem measurable_walk (n : ℕ) : Measurable fun ω => walk ω n := by
  induction n with
  | zero => simp [walk]
  | succ n ih =>
      simp only [walk]
      exact ih.add ((Measurable.of_discrete : Measurable step).comp (measurable_pi_apply n))

theorem measurableSet_visited_eq_univ (n : ℕ) :
    MeasurableSet {ω | visited ω n = Finset.univ} := by
  have hset : {ω | visited ω n = Finset.univ}
      = ⋂ c : Clock, ⋃ j ∈ Finset.range (n + 1), {ω | walk ω j = c} := by
    ext ω
    simp [visited, Finset.eq_univ_iff_forall, Finset.mem_image]
  rw [hset]
  refine MeasurableSet.iInter fun c => ?_
  refine MeasurableSet.biUnion (Finset.range (n + 1)).countable_toSet fun j _ => ?_
  exact measurable_walk j (measurableSet_singleton c)

theorem measurableSet_covers : MeasurableSet {ω | Covers ω} := by
  have : {ω | Covers ω} = ⋃ n, {ω | visited ω n = Finset.univ} := by ext ω; simp [Covers]
  rw [this]
  exact MeasurableSet.iUnion fun n => measurableSet_visited_eq_univ n

theorem measurableSet_lastField_eq (k : Clock) :
    MeasurableSet {ω | lastField ω = k} := by
  by_cases hk : k = 0
  · -- the walk ends at its start exactly when it never covers the clock
    subst hk
    have hset : {ω | lastField ω = (0 : Clock)} = {ω | Covers ω}ᶜ := by
      ext ω
      constructor
      · intro h hc; exact lastField_ne_zero ω hc h
      · intro h
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at h
        simp [lastField, coverTime_eq_zero_of_not_covers h, walk]
    rw [hset]
    exact measurableSet_covers.compl
  · -- otherwise, split over the exact value of the cover time
    have hset : {ω | lastField ω = k}
        = ⋃ n, (({ω | visited ω n = Finset.univ}
            ∩ ⋂ m ∈ Finset.range n, {ω | visited ω m = Finset.univ}ᶜ)
          ∩ {ω | walk ω n = k}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Finset.mem_range]
      constructor
      · intro h
        have hc : Covers ω := by
          by_contra hcon
          rw [lastField, coverTime_eq_zero_of_not_covers hcon] at h
          exact hk (by simpa [walk] using h.symm)
        refine ⟨coverTime ω, ⟨coverTime_mem ω hc, fun m hm => ?_⟩, h⟩
        exact Nat.notMem_of_lt_sInf hm
      · rintro ⟨n, ⟨hn, hmin⟩, hwk⟩
        rw [lastField, coverTime_eq_of hn fun m hm => hmin m hm]
        exact hwk
    rw [hset]
    refine MeasurableSet.iUnion fun n => ?_
    refine ((measurableSet_visited_eq_univ n).inter ?_).inter
      (measurable_walk n (measurableSet_singleton k))
    refine MeasurableSet.biInter (Finset.range n).countable_toSet fun m _ => ?_
    exact (measurableSet_visited_eq_univ m).compl

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
  have hnull : μ {ω | ¬ Covers ω} = 0 := ae_iff.mp (ae_covers hμ)
  exact measure_mono_null (fun ω hω hc => lastField_ne_zero ω hc hω) hnull

end LadybugClock
