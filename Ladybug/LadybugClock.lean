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

theorem walk_succ (ω : ℕ → Bool) (n : ℕ) : walk ω (n + 1) = walk ω n + step (ω n) := rfl

theorem visited_succ (ω : ℕ → Bool) (n : ℕ) :
    visited ω (n + 1) = insert (walk ω (n + 1)) (visited ω n) := by
  simp [visited, Finset.range_add_one]

theorem mem_visited_iff (ω : ℕ → Bool) (n : ℕ) (c : Clock) :
    c ∈ visited ω n ↔ ∃ m ≤ n, walk ω m = c := by
  simp [visited, Finset.mem_image]

theorem visited_eq_univ_iff (ω : ℕ → Bool) (n : ℕ) :
    visited ω n = Finset.univ ↔ ∀ c, ∃ m ≤ n, walk ω m = c := by
  simp [Finset.eq_univ_iff_forall, mem_visited_iff]

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

/-! ## The walk covers the clock almost surely

Eleven consecutive clockwise steps sweep the whole clock, so it suffices to know that some
block of eleven consecutive flips comes up all heads.  That follows from a union bound: among
the patterns of the first `M` blocks of eleven flips, only `2047 ^ M` out of `2048 ^ M` contain
no all-heads block, and `(2047 / 2048) ^ M` tends to `0`. -/

private theorem natCast_val_self (a : Clock) : ((a.val : ℕ) : Clock) = a := by revert a; decide

private theorem step_true : step true = 1 := rfl

/-- After `j ≤ 11` clockwise steps taken from time `N`, the walk has advanced by `j` fields. -/
theorem walk_add_of_block {ω : ℕ → Bool} {N : ℕ} (h : ∀ i < 11, ω (N + i) = true) :
    ∀ j ≤ 11, walk ω (N + j) = walk ω N + (j : Clock) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      intro hj
      rw [show N + (j + 1) = N + j + 1 from rfl, walk_succ, ih (by omega), h j (by omega),
        step_true]
      push_cast
      ring

/-- Eleven consecutive clockwise steps sweep the whole clock. -/
theorem covers_of_block {ω : ℕ → Bool} {N : ℕ} (h : ∀ i < 11, ω (N + i) = true) : Covers ω := by
  refine ⟨N + 11, (visited_eq_univ_iff ω _).2 fun c => ?_⟩
  have hlt : (c - walk ω N).val < 12 := ZMod.val_lt _
  refine ⟨N + (c - walk ω N).val, by omega, ?_⟩
  rw [walk_add_of_block h _ (by omega), natCast_val_self]
  ring

/-- The bad event: no block `[11 * N, 11 * N + 11)` of flips comes up all heads. -/
private def NoGoodBlock (ω : ℕ → Bool) : Prop := ∀ N : ℕ, ∃ i < 11, ω (11 * N + i) = false

/-- The coin-flip sequence spelled out by `M` blocks of eleven flips (all later flips heads). -/
private def blockExt (M : ℕ) (g : Fin M → Fin 11 → Bool) (i : ℕ) : Bool :=
  if h : i / 11 < M then g ⟨i / 11, h⟩ ⟨i % 11, by omega⟩ else true

/-- The patterns of `M` blocks of eleven flips in which no block is all heads. -/
private def badPatterns (M : ℕ) : Finset (Fin M → Fin 11 → Bool) :=
  Fintype.piFinset fun _ => {h ∈ Finset.univ | ∃ b, h b = false}

private theorem card_bad_block :
    ({h ∈ (Finset.univ : Finset (Fin 11 → Bool)) | ∃ b, h b = false}).card = 2047 := by
  have hkey : {h ∈ (Finset.univ : Finset (Fin 11 → Bool)) | ∃ b, h b = false}
      = Finset.univ.erase (fun _ => true) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · rintro ⟨b, hb⟩ rfl
      simp at hb
    · intro hne
      by_contra hcon
      push_neg at hcon
      exact hne (funext fun b => by simpa using hcon b)
  rw [hkey, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_pi_const]
  norm_num

private theorem card_badPatterns (M : ℕ) : (badPatterns M).card = 2047 ^ M := by
  rw [badPatterns, Fintype.card_piFinset_const, card_bad_block]

/-- Every sequence with no all-heads block agrees, on the first `11 * M` flips, with one of the
bad patterns. -/
private theorem noGoodBlock_subset (M : ℕ) :
    {ω : ℕ → Bool | NoGoodBlock ω} ⊆
      ⋃ g ∈ badPatterns M, {ω | ∀ i ∈ Finset.range (11 * M), ω i = blockExt M g i} := by
  intro ω hω
  have hg : (fun (a : Fin M) (b : Fin 11) => ω (11 * (a : ℕ) + (b : ℕ))) ∈ badPatterns M := by
    rw [badPatterns, Fintype.mem_piFinset]
    intro a
    obtain ⟨i, hi, hif⟩ := hω a
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨⟨i, hi⟩, hif⟩⟩
  refine Set.mem_biUnion hg ?_
  intro i hi
  rw [Finset.mem_range] at hi
  have hdiv : i / 11 < M := by omega
  rw [blockExt, dif_pos hdiv]
  change ω i = ω (11 * (i / 11) + i % 11)
  congr 1
  omega

omit [IsProbabilityMeasure μ] in
theorem ae_covers (hμ : IsFairCoinFlips μ) : ∀ᵐ ω ∂μ, Covers ω := by
  classical
  have hsub : {ω | ¬ Covers ω} ⊆ {ω | NoGoodBlock ω} := by
    intro ω hω N
    by_contra hcon
    push_neg at hcon
    exact hω (covers_of_block (N := 11 * N) fun i hi => by simpa using hcon i hi)
  -- a union bound over the bad patterns of the first `M` blocks
  have hbound : ∀ M : ℕ, μ {ω | NoGoodBlock ω} ≤ ((2047 : ℝ≥0∞) * (1 / 2) ^ 11) ^ M := by
    intro M
    calc μ {ω | NoGoodBlock ω}
        ≤ μ (⋃ g ∈ badPatterns M,
            {ω | ∀ i ∈ Finset.range (11 * M), ω i = blockExt M g i}) :=
          measure_mono (noGoodBlock_subset M)
      _ ≤ ∑ g ∈ badPatterns M, μ {ω | ∀ i ∈ Finset.range (11 * M), ω i = blockExt M g i} :=
          measure_biUnion_finset_le _ _
      _ = ∑ _g ∈ badPatterns M, (1 / 2 : ℝ≥0∞) ^ (11 * M) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [hμ (Finset.range (11 * M)) (blockExt M g), Finset.card_range]
      _ = (2047 : ℝ≥0∞) ^ M * (1 / 2 : ℝ≥0∞) ^ (11 * M) := by
          rw [Finset.sum_const, card_badPatterns, nsmul_eq_mul]
          push_cast
          ring
      _ = ((2047 : ℝ≥0∞) * (1 / 2) ^ 11) ^ M := by rw [mul_pow, ← pow_mul]
  -- and that bound tends to zero
  have hne : (1 / 2 : ℝ≥0∞) ^ 11 ≠ 0 := pow_ne_zero _ (by norm_num)
  have htop : (1 / 2 : ℝ≥0∞) ^ 11 ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have hone : (2048 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ 11 = 1 := by
    rw [show (1 / 2 : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ by norm_num, ← ENNReal.inv_pow,
      show (2 : ℝ≥0∞) ^ 11 = 2048 by norm_num]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hr : (2047 : ℝ≥0∞) * (1 / 2) ^ 11 < 1 := by
    calc (2047 : ℝ≥0∞) * (1 / 2) ^ 11 = (1 / 2 : ℝ≥0∞) ^ 11 * 2047 := mul_comm _ _
      _ < (1 / 2 : ℝ≥0∞) ^ 11 * 2048 := ENNReal.mul_lt_mul_right hne htop (by norm_num)
      _ = 2048 * (1 / 2 : ℝ≥0∞) ^ 11 := mul_comm _ _
      _ = 1 := hone
  have hzero : μ {ω | NoGoodBlock ω} = 0 :=
    nonpos_iff_eq_zero.mp
      (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) hbound)
  exact ae_iff.mpr (measure_mono_null hsub hzero)

/-! ## Key structural lemma

`k` is the last field visited exactly when both of its neighbours are reached
strictly before `k` itself. -/

/-- The walk reaches `a` at some time at which it has not yet reached `k`. -/
def ReachesBefore (ω : ℕ → Bool) (a k : Clock) : Prop :=
  ∃ n, walk ω n = a ∧ ∀ m ≤ n, walk ω m ≠ k

/-! ### A discrete intermediate value theorem -/

/-- A function `ℕ → ℕ` that changes by exactly one at each step of `[a, b]` attains every
value between `f a` and `f b`. -/
private theorem exists_eq_of_step_one {f : ℕ → ℕ} (a : ℕ) :
    ∀ b : ℕ, a ≤ b →
      (∀ n, a ≤ n → n < b → f (n + 1) = f n + 1 ∨ f n = f (n + 1) + 1) →
      ∀ j : ℕ, ((f a ≤ j ∧ j ≤ f b) ∨ (f b ≤ j ∧ j ≤ f a)) →
        ∃ m, a ≤ m ∧ m ≤ b ∧ f m = j := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _ j hj; exact ⟨a, le_rfl, le_rfl, by omega⟩
  | succ b hb ih =>
      intro hstep j hj
      have hs := hstep b hb (Nat.lt_succ_self b)
      by_cases hin : (f a ≤ j ∧ j ≤ f b) ∨ (f b ≤ j ∧ j ≤ f a)
      · obtain ⟨m, hm1, hm2, hm3⟩ := ih (fun n hn _ => hstep n hn (by omega)) j hin
        exact ⟨m, hm1, by omega, hm3⟩
      · exact ⟨b + 1, by omega, le_rfl, by omega⟩

/-! ### Cutting the clock open at `k`

Writing `d x = (x - k).val`, the walk seen through `d` is a walk on `{0, …, 11}` that moves
by exactly one at each step, as long as it stays away from `k`, i.e. as long as `d ≠ 0`. -/

private theorem val_step {a b : Clock} (ha : a ≠ 0) (hb : b ≠ 0) (h : b = a + 1 ∨ b = a - 1) :
    b.val = a.val + 1 ∨ a.val = b.val + 1 := by
  revert a b; decide

private theorem val_mem_Icc {a : Clock} (ha : a ≠ 0) : 1 ≤ a.val ∧ a.val ≤ 11 := by
  revert a; decide

private theorem val_sub_pred (k : Clock) : ((k - 1) - k).val = 11 := by revert k; decide

private theorem val_sub_succ (k : Clock) : ((k + 1) - k).val = 1 := by revert k; decide

private theorem sub_one_ne (k : Clock) : k - 1 ≠ k := by revert k; decide

private theorem add_one_ne (k : Clock) : k + 1 ≠ k := by revert k; decide

/-- Each coin flip moves the walk one field clockwise or one field counter-clockwise. -/
theorem walk_succ_eq (ω : ℕ → Bool) (n : ℕ) :
    walk ω (n + 1) = walk ω n + 1 ∨ walk ω (n + 1) = walk ω n - 1 := by
  rcases h : ω n with _ | _
  · right; simp [walk, step, h, sub_eq_add_neg]
  · left; simp [walk, step, h]

/-- The field reached at the cover time is reached there for the first time: otherwise the
previous instant would already have completed the tour. -/
theorem walk_ne_of_lt_coverTime {ω : ℕ → Bool} (hω : Covers ω) {m : ℕ} (hm : m < coverTime ω) :
    walk ω m ≠ walk ω (coverTime ω) := by
  intro h
  obtain ⟨T, hT⟩ : ∃ T, coverTime ω = T + 1 := ⟨coverTime ω - 1, by omega⟩
  refine Nat.notMem_of_lt_sInf (s := {n | visited ω n = Finset.univ})
    (show T < coverTime ω by omega) ?_
  have hmem : walk ω (coverTime ω) ∈ visited ω T := (mem_visited_iff ω T _).2 ⟨m, by omega, h⟩
  have huniv := coverTime_mem ω hω
  rw [hT, visited_succ, ← hT, Finset.insert_eq_self.mpr hmem] at huniv
  exact huniv

/-- The ladybug stops on `k` exactly when it reaches both neighbours of `k` before `k` itself.
(The hypothesis `k ≠ 0` is not needed: for `k = 0` both sides are false, since the start is
visited at time `0`.) -/
theorem lastField_eq_iff (ω : ℕ → Bool) (hω : Covers ω) (k : Clock) (_hk : k ≠ 0) :
    lastField ω = k ↔ ReachesBefore ω (k - 1) k ∧ ReachesBefore ω (k + 1) k := by
  constructor
  · -- If the tour ends at `k`, then `k` is untouched before the cover time, while every
    -- other field — in particular both neighbours of `k` — is reached strictly earlier.
    intro h
    have hlf : walk ω (coverTime ω) = k := h
    have hne : ∀ m < coverTime ω, walk ω m ≠ k := fun m hm => hlf ▸ walk_ne_of_lt_coverTime hω hm
    have huniv := (visited_eq_univ_iff ω _).1 (coverTime_mem ω hω)
    have key : ∀ a : Clock, a ≠ k → ReachesBefore ω a k := by
      intro a ha
      obtain ⟨n, hn, hnk⟩ := huniv a
      have hnlt : n < coverTime ω := by
        rcases lt_or_eq_of_le hn with h' | h'
        · exact h'
        · exact absurd (hnk.symm.trans (h' ▸ hlf)) ha
      exact ⟨n, hnk, fun m hm => hne m (by omega)⟩
    exact ⟨key _ (sub_one_ne k), key _ (add_one_ne k)⟩
  · -- Conversely, once both neighbours have been seen, the walk cannot have avoided any
    -- field: cut open at `k`, the trajectory is an interval-valued walk with unit steps.
    rintro ⟨⟨n₁, hn₁, hn₁k⟩, ⟨n₂, hn₂, hn₂k⟩⟩
    have hcovk : ∃ n ≤ coverTime ω, walk ω n = k :=
      (visited_eq_univ_iff ω _).1 (coverTime_mem ω hω) k
    have hS : {n | walk ω n = k}.Nonempty := by obtain ⟨n, -, hn⟩ := hcovk; exact ⟨n, hn⟩
    set s := sInf {n | walk ω n = k} with hs_def
    have hsk : walk ω s = k := Nat.sInf_mem hS
    have hlt : ∀ m, m < s → walk ω m ≠ k := fun m hm => Nat.notMem_of_lt_sInf hm
    have hn₁s : n₁ < s := by by_contra hcon; exact hn₁k s (by omega) hsk
    have hn₂s : n₂ < s := by by_contra hcon; exact hn₂k s (by omega) hsk
    -- Every field has been visited by the first time `k` is reached.
    have hcov : visited ω s = Finset.univ := by
      rw [visited_eq_univ_iff]
      intro c
      by_cases hck : c = k
      · exact ⟨s, le_rfl, by rw [hsk, hck]⟩
      set f : ℕ → ℕ := fun n => (walk ω n - k).val with hf
      have hstep : ∀ n, n + 1 < s → f (n + 1) = f n + 1 ∨ f n = f (n + 1) + 1 := by
        intro n hn
        refine val_step (sub_ne_zero_of_ne (hlt n (by omega)))
          (sub_ne_zero_of_ne (hlt (n + 1) (by omega))) ?_
        rcases walk_succ_eq ω n with h' | h' <;> rw [h']
        · left; ring
        · right; ring
      have h11 : f n₁ = 11 := by rw [hf]; simp [hn₁]
      have h1 : f n₂ = 1 := by rw [hf]; simpa [hn₂] using val_sub_succ k
      obtain ⟨hj1, hj2⟩ := val_mem_Icc (sub_ne_zero_of_ne hck)
      have hval : ∀ {m : ℕ}, f m = (c - k).val → walk ω m = c := by
        intro m hm
        exact sub_left_injective (ZMod.val_injective 12 hm)
      rcases le_total n₁ n₂ with hle | hle
      · obtain ⟨m, -, hm2, hm3⟩ :=
          exists_eq_of_step_one n₁ n₂ hle (fun n _ hn => hstep n (by omega)) (c - k).val
            (by omega)
        exact ⟨m, by omega, hval hm3⟩
      · obtain ⟨m, -, hm2, hm3⟩ :=
          exists_eq_of_step_one n₂ n₁ hle (fun n _ hn => hstep n (by omega)) (c - k).val
            (by omega)
        exact ⟨m, by omega, hval hm3⟩
    have hTle : coverTime ω ≤ s := Nat.sInf_le hcov
    have hsle : s ≤ coverTime ω := by
      obtain ⟨n, hn, hnk⟩ := hcovk
      exact le_trans (Nat.sInf_le hnk) hn
    change walk ω (coverTime ω) = k
    rw [show coverTime ω = s from le_antisymm hTle hsle, hsk]

/-! ## Reduction to gambler's ruin

By the structural lemma, the ladybug stops on `k` exactly when it reaches both neighbours of
`k` before `k`.  One of the two neighbours is *always* reached before `k` — the walk has to
step onto `k` from somewhere — so the two events cover a set of full measure, and
inclusion–exclusion turns the answer into the sum of two ruin probabilities. -/

theorem measurableSet_reachesBefore (a k : Clock) :
    MeasurableSet {ω | ReachesBefore ω a k} := by
  have hset : {ω | ReachesBefore ω a k}
      = ⋃ n, ({ω | walk ω n = a} ∩ ⋂ m ∈ Finset.range (n + 1), {ω | walk ω m = k}ᶜ) := by
    ext ω
    simp only [ReachesBefore, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range, Nat.lt_succ_iff]
  rw [hset]
  refine MeasurableSet.iUnion fun n => ?_
  refine (measurable_walk n (measurableSet_singleton a)).inter ?_
  refine MeasurableSet.biInter (Finset.range (n + 1)).countable_toSet fun m _ => ?_
  exact (measurable_walk m (measurableSet_singleton k)).compl

/-- The walk can only step onto `k` from a neighbour of `k`, so on a covering path at least one
of the two neighbours is reached before `k`. -/
theorem reachesBefore_or (ω : ℕ → Bool) (hω : Covers ω) (k : Clock) (hk : k ≠ 0) :
    ReachesBefore ω (k - 1) k ∨ ReachesBefore ω (k + 1) k := by
  have hS : {n | walk ω n = k}.Nonempty := by
    obtain ⟨n, -, hn⟩ := (visited_eq_univ_iff ω _).1 (coverTime_mem ω hω) k
    exact ⟨n, hn⟩
  obtain ⟨s, hsk, hslt⟩ : ∃ s, walk ω s = k ∧ ∀ m < s, walk ω m ≠ k :=
    ⟨sInf {n | walk ω n = k}, Nat.sInf_mem hS, fun m hm => Nat.notMem_of_lt_sInf hm⟩
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hsk
    exact hk (by simpa [walk] using hsk.symm)
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hlt : ∀ m ≤ t, walk ω m ≠ k := fun m hm => hslt m (by omega)
  rcases walk_succ_eq ω t with h | h
  · refine Or.inl ⟨t, ?_, hlt⟩
    rw [h] at hsk
    linear_combination hsk
  · refine Or.inr ⟨t, ?_, hlt⟩
    rw [h] at hsk
    linear_combination hsk

/-! ## The cylinder characterisation pins down the measure -/

theorem measurableSet_cylSet (s : Finset ℕ) (g : ℕ → Bool) :
    MeasurableSet {ω : ℕ → Bool | ∀ i ∈ s, ω i = g i} := by
  have hset : {ω : ℕ → Bool | ∀ i ∈ s, ω i = g i} = ⋂ i ∈ s, {ω : ℕ → Bool | ω i = g i} := by
    ext ω; simp
  rw [hset]
  refine MeasurableSet.biInter s.countable_toSet fun i _ => ?_
  show MeasurableSet ((fun f : ℕ → Bool => f i) ⁻¹' {g i})
  exact measurable_pi_apply i (measurableSet_singleton (g i))

/-- The coin-flip sequence spelled out by a point of `∀ i : s, Bool`. -/
private def cylFun (s : Finset ℕ) (f : ∀ _ : s, Bool) : ℕ → Bool :=
  fun j => if h : j ∈ s then f ⟨j, h⟩ else true

private theorem cylinder_singleton_eq (s : Finset ℕ) (f : ∀ _ : s, Bool) :
    cylinder (α := fun _ : ℕ => Bool) s {f} = {ω : ℕ → Bool | ∀ i ∈ s, ω i = cylFun s f i} := by
  ext ω
  simp only [mem_cylinder, Set.mem_singleton_iff, Set.mem_ofPred_eq, cylFun]
  constructor
  · intro h i hi
    rw [dif_pos hi, ← h]
    rfl
  · intro h
    funext i
    have hi := h i.1 i.2
    rw [dif_pos i.2] at hi
    exact hi

/-- Two fair coin-flip measures agree: the cylinder values determine the measure, since the
cylinders form a π-system generating the σ-algebra. -/
theorem eq_of_isFairCoinFlips {ν₁ ν₂ : Measure (ℕ → Bool)} [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂] (h₁ : IsFairCoinFlips ν₁) (h₂ : IsFairCoinFlips ν₂) : ν₁ = ν₂ := by
  classical
  refine ext_of_generate_finite (measurableCylinders fun _ : ℕ => Bool)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ (by simp)
  rintro t ht
  obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders t).1 ht
  have hdecomp : ∀ lam : Measure (ℕ → Bool),
      lam (cylinder (α := fun _ : ℕ => Bool) s S)
        = ∑ f ∈ Finset.univ.filter (· ∈ S), lam (cylinder (α := fun _ : ℕ => Bool) s {f}) := by
    intro lam
    have hunion : cylinder (α := fun _ : ℕ => Bool) s S
        = ⋃ f ∈ Finset.univ.filter (· ∈ S), cylinder (α := fun _ : ℕ => Bool) s {f} := by
      ext ω
      simp only [mem_cylinder, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_univ, true_and, Set.mem_singleton_iff, exists_prop]
      exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨f, hf, hfe⟩ => hfe ▸ hf⟩
    rw [hunion]
    refine measure_biUnion_finset ?_ fun f _ => MeasurableSet.cylinder s (measurableSet_singleton f)
    intro f _ g _ hfg
    simp only [Function.onFun, Set.disjoint_left]
    intro ω hω hω'
    rw [mem_cylinder, Set.mem_singleton_iff] at hω hω'
    exact hfg (hω ▸ hω')
  rw [hdecomp ν₁, hdecomp ν₂]
  exact Finset.sum_congr rfl fun f _ => by rw [cylinder_singleton_eq, h₁, h₂]

/-! ## Conditioning on the first flip -/

/-- The shift that forgets the first coin flip. -/
def shift (ω : ℕ → Bool) : ℕ → Bool := fun i => ω (i + 1)

theorem measurable_shift : Measurable shift :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (i + 1)

omit [IsProbabilityMeasure μ] in
private theorem shiftMeasure_apply (b : Bool) {E : Set (ℕ → Bool)} (hE : MeasurableSet E) :
    ((2 : ℝ≥0∞) • ((μ.restrict {ω : ℕ → Bool | ω 0 = b}).map shift)) E
      = 2 * μ (shift ⁻¹' E ∩ {ω | ω 0 = b}) := by
  rw [Measure.smul_apply, Measure.map_apply measurable_shift hE,
    Measure.restrict_apply (measurable_shift hE), smul_eq_mul]

private theorem two_mul_half : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
  rw [show (1 / 2 : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ by norm_num]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- **The first flip is fair and independent of the rest.** -/
theorem measure_first_shift (hμ : IsFairCoinFlips μ) (b : Bool) {E : Set (ℕ → Bool)}
    (hE : MeasurableSet E) : μ (shift ⁻¹' E ∩ {ω | ω 0 = b}) = (1 / 2 : ℝ≥0∞) * μ E := by
  classical
  set ν : Measure (ℕ → Bool) := (2 : ℝ≥0∞) • ((μ.restrict {ω : ℕ → Bool | ω 0 = b}).map shift)
    with hν
  have hfair : IsFairCoinFlips ν := by
    intro s g
    rw [hν, shiftMeasure_apply b (measurableSet_cylSet s g)]
    have hset : shift ⁻¹' {ω : ℕ → Bool | ∀ i ∈ s, ω i = g i} ∩ {ω | ω 0 = b}
        = {ω : ℕ → Bool | ∀ j ∈ insert 0 (s.image (· + 1)),
            ω j = (fun j => if j = 0 then b else g (j - 1)) j} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, shift,
        Finset.mem_insert, Finset.mem_image]
      constructor
      · rintro ⟨h1, h2⟩ j (rfl | ⟨i, hi, rfl⟩)
        · simpa using h2
        · simpa using h1 i hi
      · intro h
        refine ⟨fun i hi => ?_, by simpa using h 0 (Or.inl rfl)⟩
        have := h (i + 1) (Or.inr ⟨i, hi, rfl⟩)
        simpa using this
    have hcard : (insert 0 (s.image (· + 1))).card = s.card + 1 := by
      rw [Finset.card_insert_of_notMem (by simp),
        Finset.card_image_of_injective _ (fun a b hab => by omega)]
    rw [hset, hμ, hcard, pow_succ]
    calc (2 : ℝ≥0∞) * ((1 / 2) ^ s.card * (1 / 2))
        = (1 / 2 : ℝ≥0∞) ^ s.card * (2 * (1 / 2)) := by ring
      _ = (1 / 2 : ℝ≥0∞) ^ s.card := by rw [two_mul_half, mul_one]
  have hprob : IsProbabilityMeasure ν := ⟨by simpa using hfair ∅ (fun _ => true)⟩
  have hνμ : ν = μ := eq_of_isFairCoinFlips hfair hμ
  have happ := shiftMeasure_apply (μ := μ) b hE
  rw [← hν, hνμ] at happ
  rw [happ, ← mul_assoc, mul_comm (1 / 2 : ℝ≥0∞) 2, two_mul_half, one_mul]


private theorem measurableSet_first (b : Bool) : MeasurableSet {ω : ℕ → Bool | ω 0 = b} := by
  show MeasurableSet ((fun ω : ℕ → Bool => ω 0) ⁻¹' {b})
  exact measurable_pi_apply 0 (measurableSet_singleton b)

/-! ## The ±1 walk on the integers -/

/-- A single ±1 step. -/
def zstep (b : Bool) : ℤ := if b then 1 else -1

/-- The ±1 walk started at `a`. -/
def zwalk (a : ℤ) (ω : ℕ → Bool) : ℕ → ℤ
  | 0 => a
  | n + 1 => zwalk a ω n + zstep (ω n)

theorem zwalk_zero (a : ℤ) (ω : ℕ → Bool) : zwalk a ω 0 = a := rfl

theorem zwalk_succ (a : ℤ) (ω : ℕ → Bool) (n : ℕ) :
    zwalk a ω (n + 1) = zwalk a ω n + zstep (ω n) := rfl

theorem zwalk_add_const (a c : ℤ) (ω : ℕ → Bool) (n : ℕ) :
    zwalk (a + c) ω n = zwalk a ω n + c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [zwalk_succ, zwalk_succ, ih]; ring

/-- Peeling the first flip off the walk. -/
theorem zwalk_shift (a : ℤ) (ω : ℕ → Bool) (n : ℕ) :
    zwalk a ω (n + 1) = zwalk (a + zstep (ω 0)) (shift ω) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [zwalk_succ (n := n + 1), ih, zwalk_succ]; rfl

theorem measurable_zwalk (a : ℤ) (n : ℕ) : Measurable fun ω => zwalk a ω n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      simp only [zwalk_succ]
      exact ih.add ((Measurable.of_discrete : Measurable zstep).comp (measurable_pi_apply n))

/-! ## Gambler's ruin -/

/-- The walk started at `a` reaches `t` at a time before which it has stayed strictly inside
the open interval `(0, N)`.  For `t = N` this says it leaves `[0, N]` through the top, for
`t = 0` through the bottom. -/
def ExitsAt (a N t : ℤ) (ω : ℕ → Bool) : Prop :=
  ∃ n, zwalk a ω n = t ∧ ∀ m < n, 0 < zwalk a ω m ∧ zwalk a ω m < N

theorem measurableSet_exitsAt (a N t : ℤ) : MeasurableSet {ω | ExitsAt a N t ω} := by
  have hset : {ω | ExitsAt a N t ω}
      = ⋃ n, ({ω | zwalk a ω n = t}
          ∩ ⋂ m ∈ Finset.range n, {ω | 0 < zwalk a ω m ∧ zwalk a ω m < N}) := by
    ext ω
    simp only [ExitsAt, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter,
      Finset.mem_range]
  rw [hset]
  refine MeasurableSet.iUnion fun n => ?_
  refine MeasurableSet.inter ?_ ?_
  · show MeasurableSet ((fun ω => zwalk a ω n) ⁻¹' {t})
    exact measurable_zwalk a n (measurableSet_singleton t)
  · refine MeasurableSet.biInter (Finset.range n).countable_toSet fun m _ => ?_
    show MeasurableSet ((fun ω => zwalk a ω m) ⁻¹' {x : ℤ | 0 < x ∧ x < N})
    exact measurable_zwalk a m MeasurableSet.of_discrete

/-- First-step analysis: from an interior point the walk takes one step and starts afresh. -/
theorem exitsAt_iff_shift {a N t : ℤ} (h0 : 0 < a) (hN : a < N) (hat : a ≠ t) (ω : ℕ → Bool) :
    ExitsAt a N t ω ↔ ExitsAt (a + zstep (ω 0)) N t (shift ω) := by
  constructor
  · rintro ⟨n, hn, hbd⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
      cases n with
      | zero => exact absurd hn hat
      | succ n' => exact ⟨n', rfl⟩
    exact ⟨n', by rw [← zwalk_shift]; exact hn,
      fun m hm => by rw [← zwalk_shift]; exact hbd (m + 1) (by omega)⟩
  · rintro ⟨n, hn, hbd⟩
    refine ⟨n + 1, by rw [zwalk_shift]; exact hn, fun m hm => ?_⟩
    cases m with
    | zero => exact ⟨h0, hN⟩
    | succ m' => rw [zwalk_shift]; exact hbd m' (by omega)

/-- The ruin probability satisfies the discrete Laplace equation in the interior. -/
theorem measure_exitsAt_rec (hμ : IsFairCoinFlips μ) {a N t : ℤ} (h0 : 0 < a) (hN : a < N)
    (hat : a ≠ t) :
    μ {ω | ExitsAt a N t ω}
      = 1 / 2 * μ {ω | ExitsAt (a + 1) N t ω} + 1 / 2 * μ {ω | ExitsAt (a - 1) N t ω} := by
  have hsplit : {ω | ExitsAt a N t ω}
      = (shift ⁻¹' {ω | ExitsAt (a + 1) N t ω} ∩ {ω | ω 0 = true})
        ∪ (shift ⁻¹' {ω | ExitsAt (a - 1) N t ω} ∩ {ω | ω 0 = false}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro h
      rw [exitsAt_iff_shift h0 hN hat ω] at h
      rcases hb : ω 0 with _ | _
      · rw [hb] at h
        exact Or.inr ⟨by simpa [zstep, sub_eq_add_neg] using h, rfl⟩
      · rw [hb] at h
        exact Or.inl ⟨by simpa [zstep] using h, rfl⟩
    · rintro (⟨h, hb⟩ | ⟨h, hb⟩)
      · have hb' : ω 0 = true := hb
        rw [exitsAt_iff_shift h0 hN hat ω, hb']
        simpa [zstep] using h
      · have hb' : ω 0 = false := hb
        rw [exitsAt_iff_shift h0 hN hat ω, hb']
        simpa [zstep, sub_eq_add_neg] using h
  have hdisj : Disjoint (shift ⁻¹' {ω | ExitsAt (a + 1) N t ω} ∩ {ω : ℕ → Bool | ω 0 = true})
      (shift ⁻¹' {ω | ExitsAt (a - 1) N t ω} ∩ {ω : ℕ → Bool | ω 0 = false}) := by
    rw [Set.disjoint_left]
    rintro ω ⟨-, h1⟩ ⟨-, h2⟩
    have h1' : ω 0 = true := h1
    have h2' : ω 0 = false := h2
    rw [h1'] at h2'
    exact Bool.noConfusion h2'
  rw [hsplit, measure_union hdisj
      ((measurable_shift (measurableSet_exitsAt _ _ _)).inter (measurableSet_first false)),
    measure_first_shift hμ true (measurableSet_exitsAt _ _ _),
    measure_first_shift hμ false (measurableSet_exitsAt _ _ _)]



/-! ### Boundary values -/

theorem exitsAt_self (N t : ℤ) (ω : ℕ → Bool) : ExitsAt t N t ω :=
  ⟨0, rfl, fun m hm => absurd hm (Nat.not_lt_zero m)⟩

theorem not_exitsAt {a N t : ℤ} (hat : a ≠ t) (ha : ¬(0 < a ∧ a < N)) (ω : ℕ → Bool) :
    ¬ ExitsAt a N t ω := by
  rintro ⟨n, hn, hbd⟩
  cases n with
  | zero => exact hat hn
  | succ n' => exact ha (hbd 0 (by omega))

omit [IsProbabilityMeasure μ] in
theorem measure_exitsAt_eq_zero {a N t : ℤ} (hat : a ≠ t) (ha : ¬(0 < a ∧ a < N)) :
    μ {ω | ExitsAt a N t ω} = 0 := by
  have hempty : {ω | ExitsAt a N t ω} = ∅ := Set.eq_empty_of_forall_notMem (not_exitsAt hat ha)
  rw [hempty, measure_empty]

theorem measure_exitsAt_eq_one (N t : ℤ) : μ {ω | ExitsAt t N t ω} = 1 := by
  have huniv : {ω | ExitsAt t N t ω} = Set.univ := Set.eq_univ_of_forall (exitsAt_self N t)
  rw [huniv, measure_univ]

/-! ### Solving the discrete Laplace equation -/

private theorem eq_linear_of_harmonic {F : ℕ → ℝ} {N : ℕ}
    (h : ∀ j, 0 < j → j < N → 2 * F j = F (j + 1) + F (j - 1)) :
    ∀ j, j ≤ N → F j = F 0 + j * (F 1 - F 0) := by
  have key : ∀ j, j ≤ N → F j = F 0 + j * (F 1 - F 0) ∧
      (j + 1 ≤ N → F (j + 1) = F 0 + (j + 1 : ℕ) * (F 1 - F 0)) := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨by simp, fun _ => by push_cast; ring⟩
    | succ j ih =>
        intro hj
        obtain ⟨e0, e1⟩ := ih (by omega)
        refine ⟨e1 hj, fun hj2 => ?_⟩
        have hrec := h (j + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hrec
        have ej1 := e1 hj
        push_cast at e0 ej1 ⊢
        linear_combination -hrec + 2 * ej1 - e0
  exact fun j hj => (key j hj).1

private theorem toReal_rec (hμ : IsFairCoinFlips μ) {a N t : ℤ} (h0 : 0 < a) (hN : a < N)
    (hat : a ≠ t) :
    2 * (μ {ω | ExitsAt a N t ω}).toReal
      = (μ {ω | ExitsAt (a + 1) N t ω}).toReal + (μ {ω | ExitsAt (a - 1) N t ω}).toReal := by
  rw [measure_exitsAt_rec hμ h0 hN hat,
    ENNReal.toReal_add (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _))
      (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, show (1 / 2 : ℝ≥0∞).toReal = 1 / 2 by norm_num]
  ring

/-- The ruin probability is an affine function of the starting point. -/
private theorem toReal_exitsAt_affine (hμ : IsFairCoinFlips μ) {N : ℕ} {t : ℤ}
    (hint : ∀ i : ℕ, 0 < i → i < N → (i : ℤ) ≠ t) {j : ℕ} (hj : j ≤ N) :
    (μ {ω | ExitsAt (j : ℤ) (N : ℤ) t ω}).toReal
      = (μ {ω | ExitsAt (0 : ℤ) (N : ℤ) t ω}).toReal
        + j * ((μ {ω | ExitsAt (1 : ℤ) (N : ℤ) t ω}).toReal
             - (μ {ω | ExitsAt (0 : ℤ) (N : ℤ) t ω}).toReal) := by
  have hharm : ∀ i : ℕ, 0 < i → i < N →
      2 * (μ {ω | ExitsAt ((i : ℕ) : ℤ) (N : ℤ) t ω}).toReal
        = (μ {ω | ExitsAt ((i + 1 : ℕ) : ℤ) (N : ℤ) t ω}).toReal
          + (μ {ω | ExitsAt ((i - 1 : ℕ) : ℤ) (N : ℤ) t ω}).toReal := by
    intro i hi hiN
    have hr := toReal_rec hμ (a := (i : ℤ)) (N := (N : ℤ)) (t := t)
      (by exact_mod_cast hi) (by exact_mod_cast hiN) (hint i hi hiN)
    rw [show ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) by push_cast; ring,
      show ((i : ℤ) - 1) = ((i - 1 : ℕ) : ℤ) by omega] at hr
    exact hr
  have hkey := eq_linear_of_harmonic
    (F := fun i : ℕ => (μ {ω | ExitsAt ((i : ℕ) : ℤ) (N : ℤ) t ω}).toReal) hharm j hj
  simpa using hkey

/-- **Gambler's ruin, upper barrier.**  Started at `j ∈ {0, …, N}`, the walk reaches `N` before
`0` with probability `j / N`. -/
theorem toReal_exitsAt_top (hμ : IsFairCoinFlips μ) {N : ℕ} (hN : 0 < N) {j : ℕ} (hj : j ≤ N) :
    (μ {ω | ExitsAt (j : ℤ) (N : ℤ) (N : ℤ) ω}).toReal = j / N := by
  have hint : ∀ i : ℕ, 0 < i → i < N → (i : ℤ) ≠ (N : ℤ) := fun i _ hiN => by
    exact_mod_cast Nat.ne_of_lt hiN
  have h0 : μ {ω | ExitsAt (0 : ℤ) (N : ℤ) (N : ℤ) ω} = 0 :=
    measure_exitsAt_eq_zero (by exact_mod_cast hN.ne) (by omega)
  have hNN : μ {ω | ExitsAt ((N : ℕ) : ℤ) (N : ℤ) (N : ℤ) ω} = 1 := measure_exitsAt_eq_one _ _
  have keyN := toReal_exitsAt_affine hμ hint (j := N) le_rfl
  have keyj := toReal_exitsAt_affine hμ hint hj
  rw [h0] at keyN keyj
  rw [hNN] at keyN
  simp only [ENNReal.toReal_zero, ENNReal.toReal_one, sub_zero, zero_add] at keyN keyj
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hF1 : (μ {ω | ExitsAt (1 : ℤ) (N : ℤ) (N : ℤ) ω}).toReal = 1 / N := by
    field_simp
    linarith [keyN]
  rw [keyj, hF1]
  field_simp

/-- **Gambler's ruin, lower barrier.**  Started at `j ∈ {0, …, N}`, the walk reaches `0` before
`N` with probability `(N - j) / N`. -/
theorem toReal_exitsAt_bot (hμ : IsFairCoinFlips μ) {N : ℕ} (hN : 0 < N) {j : ℕ} (hj : j ≤ N) :
    (μ {ω | ExitsAt (j : ℤ) (N : ℤ) 0 ω}).toReal = ((N : ℝ) - j) / N := by
  have hint : ∀ i : ℕ, 0 < i → i < N → (i : ℤ) ≠ 0 := fun i hi _ => by
    exact_mod_cast hi.ne'
  have h0 : μ {ω | ExitsAt (0 : ℤ) (N : ℤ) 0 ω} = 1 := measure_exitsAt_eq_one _ _
  have hNN : μ {ω | ExitsAt ((N : ℕ) : ℤ) (N : ℤ) 0 ω} = 0 :=
    measure_exitsAt_eq_zero (by exact_mod_cast hN.ne') (by omega)
  have keyN := toReal_exitsAt_affine hμ hint (j := N) le_rfl
  have keyj := toReal_exitsAt_affine hμ hint hj
  rw [h0] at keyN keyj
  rw [hNN] at keyN
  simp only [ENNReal.toReal_zero, ENNReal.toReal_one] at keyN keyj
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hF1 : (μ {ω | ExitsAt (1 : ℤ) (N : ℤ) 0 ω}).toReal = 1 - 1 / N := by
    field_simp
    linarith [keyN]
  rw [keyj, hF1]
  field_simp
  ring

/-- **Gambler's ruin on the cut clock.**  Write `d = (-k).val ∈ {1, …, 11}` for the position of
the start relative to `k`.  Cutting the cycle open at `k` turns the walk into a simple random
walk on `{0, …, 12}` started at `d`, with both endpoints standing for `k`; reaching `k - 1`
before `k` means reaching `11` before `0`, which has probability `d / 11`, and reaching `k + 1`
before `k` means reaching `1` before `12`, which has probability `(12 - d) / 11`.  The two add
up to `12 / 11 = 1 + 1 / 11`, independently of `d`. -/
theorem prob_reachesBefore_add (hμ : IsFairCoinFlips μ) (k : Clock) (hk : k ≠ 0) :
    μ {ω | ReachesBefore ω (k - 1) k} + μ {ω | ReachesBefore ω (k + 1) k} = 1 + 1 / 11 := by
  sorry

/-! ## Main results -/

/-- **The last field visited is uniform on the eleven non-starting fields.** -/
theorem prob_lastField_eq (hμ : IsFairCoinFlips μ) (k : Clock) (hk : k ≠ 0) :
    μ {ω | lastField ω = k} = 1 / 11 := by
  -- the event `lastField = k` agrees off a null set with the intersection of the two events
  have hAB : μ {ω | lastField ω = k}
      = μ ({ω | ReachesBefore ω (k - 1) k} ∩ {ω | ReachesBefore ω (k + 1) k}) := by
    refine measure_congr ?_
    filter_upwards [ae_covers hμ] with ω hω
    exact propext (lastField_eq_iff ω hω k hk)
  -- the walk almost surely covers the clock, hence almost surely lies in the union
  have hcovers : μ {ω | Covers ω} = 1 := by
    have he : {ω | Covers ω} =ᵐ[μ] (Set.univ : Set (ℕ → Bool)) := by
      filter_upwards [ae_covers hμ] with ω hω
      exact propext (iff_of_true hω trivial)
    rw [measure_congr he, measure_univ]
  have hunion :
      μ ({ω | ReachesBefore ω (k - 1) k} ∪ {ω | ReachesBefore ω (k + 1) k}) = 1 := by
    refine le_antisymm prob_le_one ?_
    rw [← hcovers]
    exact measure_mono fun ω hω => reachesBefore_or ω hω k hk
  -- inclusion–exclusion against the two ruin probabilities
  have hie := measure_union_add_inter (μ := μ) {ω | ReachesBefore ω (k - 1) k}
    (measurableSet_reachesBefore (k + 1) k)
  rw [hunion, prob_reachesBefore_add hμ k hk] at hie
  rw [hAB]
  exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 hie

/-- **The ladybug stops on the 3 o'clock field with probability `1 / 11`.** -/
theorem prob_stops_at_three (hμ : IsFairCoinFlips μ) :
    μ {ω | lastField ω = 3} = 1 / 11 := by
  refine prob_lastField_eq hμ 3 ?_
  decide

omit [IsProbabilityMeasure μ] in
/-- The ladybug never stops where it started. -/
theorem prob_stops_at_noon (hμ : IsFairCoinFlips μ) :
    μ {ω | lastField ω = 0} = 0 := by
  have hnull : μ {ω | ¬ Covers ω} = 0 := ae_iff.mp (ae_covers hμ)
  exact measure_mono_null (fun ω hω hc => lastField_ne_zero ω hc hω) hnull

end LadybugClock
