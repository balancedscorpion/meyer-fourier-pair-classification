module

public import MeyerGeneralProblem.Distribution.SplineSignAlternations
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Order.Fin.Tuple
public import Mathlib.Topology.Order.IsLUB

@[expose] public section

/-!
# Phase crossings and sign alternation

A strict downward jump cannot be the first upward crossing of a
level. Consecutive integer multiples of pi reached in order give
ordered witnesses for alternating signs.
-/

namespace MeyerGeneralProblem

open Filter Set
open scoped Topology

/-- The phase is continuous on its open domain. Each omitted point
is isolated and the right phase limit is strictly below the left. -/
def HasDownwardPhaseJumps (p : ℝ → ℝ) (D : Set ℝ) : Prop :=
  IsOpen D ∧ (∀ x ∈ D, ContinuousAt p x) ∧
    ∀ x ∉ D, (∀ᶠ y in 𝓝[≠] x, y ∈ D) ∧
      ∃ ℓ r : ℝ, r < ℓ ∧ Tendsto p (𝓝[<] x) (𝓝 ℓ) ∧ Tendsto p (𝓝[>] x) (𝓝 r)

/-- A continuous addition preserves the direction of every jump. -/
theorem HasDownwardPhaseJumps.continuous_add {p q : ℝ → ℝ} {D : Set ℝ}
    (h : HasDownwardPhaseJumps p D) (hq : Continuous q) :
    HasDownwardPhaseJumps (fun x => q x + p x) D := by
  refine ⟨h.1, fun x hx => hq.continuousAt.add (h.2.1 x hx), ?_⟩
  intro x hx
  obtain ⟨hIso, ℓ, r, hr, hℓ, hr'⟩ := h.2.2 x hx
  refine ⟨hIso, q x + ℓ, q x + r, add_lt_add_right hr _, ?_, ?_⟩
  · exact (hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).add hℓ
  · exact (hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).add hr'

/-- A strict increase across an interval realizes each intermediate
phase level at a point in the domain of continuity. -/
theorem HasDownwardPhaseJumps.exists_crossing {p : ℝ → ℝ} {D : Set ℝ}
    (h : HasDownwardPhaseJumps p D) {a b v : ℝ} (hab : a < b)
    (ha : a ∈ D) (hb : b ∈ D) (hav : p a < v) (hvb : v < p b) :
    ∃ x ∈ Ioo a b, x ∈ D ∧ p x = v := by
  let S := {x : ℝ | x ∈ Ioo a b ∧ x ∈ D ∧ v < p x}
  have hS : S.Nonempty := by
    have hEv : ∀ᶠ x in 𝓝[<] b, x ∈ S := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hab), self_mem_nhdsWithin,
        nhdsWithin_le_nhds (h.1.mem_nhds hb),
        nhdsWithin_le_nhds ((h.2.1 b hb).tendsto.eventually (Ioi_mem_nhds hvb))]
        with x (hax : a < x) (hxb : x < b) hxD hxv
      exact ⟨⟨hax, hxb⟩, hxD, hxv⟩
    exact hEv.exists
  have hBound : BddBelow S := ⟨a, fun _ hx => hx.1.1.le⟩
  let z := sInf S
  have hzInf : IsGLB S z := isGLB_csInf hS hBound
  have hzFreq := hzInf.frequently_nhds_mem hS
  have haz : a < z := by
    refine lt_of_le_of_ne (le_csInf hS (fun x hx => hx.1.1.le)) ?_
    intro he
    have hFreq : ∃ᶠ x in 𝓝 a, x ∈ S := he.symm ▸ hzFreq
    have hBelow := (h.2.1 a ha).tendsto.eventually (Iio_mem_nhds hav)
    obtain ⟨x, hx, hxv⟩ := (hFreq.and_eventually hBelow).exists
    exact hx.2.2.not_gt hxv
  have hzb : z < b := by
    obtain ⟨x, hx⟩ := hS
    exact (hzInf.1 hx).trans_lt hx.1.2
  have hLeft : ∀ᶠ x in 𝓝[<] z, x ∈ D → p x ≤ v := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds haz), self_mem_nhdsWithin]
      with x (hax : a < x) (hxz : x < z) hxD
    exact le_of_not_gt (fun hxv => hxz.not_ge (hzInf.1 ⟨⟨hax, hxz.trans hzb⟩, hxD, hxv⟩))
  by_cases hzD : z ∈ D
  · have hCont := (h.2.1 z hzD).tendsto
    have hDom : ∀ᶠ x in 𝓝[<] z, x ∈ D := nhdsWithin_le_nhds (h.1.mem_nhds hzD)
    have hle : p z ≤ v := le_of_tendsto (hCont.mono_left nhdsWithin_le_nhds) (hDom.mp hLeft)
    have hge : v ≤ p z := ge_of_tendsto_of_frequently hCont (hzFreq.mono fun _ hx => hx.2.2.le)
    exact ⟨z, ⟨haz, hzb⟩, hzD, le_antisymm hle hge⟩
  · obtain ⟨hIso, ℓ, r, hr, hℓ, hr'⟩ := h.2.2 z hzD
    have hNearL : 𝓝[<] z ≤ 𝓝[≠] z :=
      nhdsWithin_mono _ fun x hx => (show x < z from hx).ne
    have hle : ℓ ≤ v := le_of_tendsto hℓ ((hIso.filter_mono hNearL).mp hLeft)
    have hRight : ∃ᶠ x in 𝓝[>] z, x ∈ S := by
      rw [frequently_nhdsWithin_iff]
      refine hzFreq.mono fun x hx => ⟨hx, lt_of_le_of_ne (hzInf.1 hx) ?_⟩
      intro he
      exact hzD (he.symm ▸ hx.2.1)
    have hge : v ≤ r := ge_of_tendsto_of_frequently hr' (hRight.mono fun _ hx => hx.2.2.le)
    exact False.elim (hr.not_ge (hle.trans hge))

private theorem exists_ordered_phase_levels {p : ℝ → ℝ} {D : Set ℝ}
    (h : HasDownwardPhaseJumps p D) {a b : ℝ} (hab : a < b) (ha : a ∈ D) (hb : b ∈ D)
    (k : ℤ) (n : ℕ) (hLow : p a < (k : ℝ) * Real.pi)
    (hHigh : ((k : ℝ) + n) * Real.pi < p b) :
    ∃ x : Fin (n + 1) → ℝ, StrictMono x ∧
      ∀ i, x i ∈ Ioo a b ∧ x i ∈ D ∧ p (x i) = ((k : ℝ) + (i.val : ℝ)) * Real.pi := by
  induction n generalizing a k with
  | zero =>
    obtain ⟨x, hx, hxD, hxv⟩ := h.exists_crossing hab ha hb hLow (by simpa using hHigh)
    refine ⟨fun _ => x, ?_, fun i => ⟨hx, hxD, ?_⟩⟩
    · intro i j hij
      exact (hij.ne (Subsingleton.elim (α := Fin 1) i j)).elim
    · simpa using hxv
  | succ n ih =>
    have hUpper : (k : ℝ) * Real.pi < p b := calc
      _ ≤ ((k : ℝ) + (n + 1 : ℕ)) * Real.pi :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg _)) Real.pi_pos.le
      _ < _ := hHigh
    obtain ⟨z, hz, hzD, hzv⟩ := h.exists_crossing hab ha hb hLow hUpper
    have hzNext : p z < ((k + 1 : ℤ) : ℝ) * Real.pi := by
      rw [hzv, Int.cast_add, Int.cast_one]
      linarith only [Real.pi_pos]
    have hTop : (((k + 1 : ℤ) : ℝ) + n) * Real.pi < p b := by
      rw [show (((k + 1 : ℤ) : ℝ) + n) * Real.pi = ((k : ℝ) + (n + 1 : ℕ)) * Real.pi by
        push_cast
        ring]
      exact hHigh
    obtain ⟨x, hMono, hx⟩ := ih hz.2 hzD (k + 1) hzNext hTop
    refine ⟨Fin.cons z x, Fin.strictMono_cons.mpr ⟨fun i => (hx i).1.1, hMono⟩, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using And.intro hz (And.intro hzD hzv)
    · refine ⟨⟨hz.1.trans (hx j).1.1, (hx j).1.2⟩, (hx j).2.1, ?_⟩
      rw [Fin.cons_succ, (hx j).2.2, Fin.val_succ]
      push_cast
      ring

/-- A phase increase exceeding `(n + 1)π` yields `n` strict sign
alternations for its cosine with a positive amplitude on the domain. -/
theorem HasDownwardPhaseJumps.hasSignAlternations {p A f : ℝ → ℝ} {D : Set ℝ}
    (h : HasDownwardPhaseJumps p D) (hA : ∀ x ∈ D, 0 < A x)
    (hf : ∀ x ∈ D, f x = A x * Real.cos (p x))
    {a b : ℝ} (hab : a < b) (ha : a ∈ D) (hb : b ∈ D) {n : ℕ}
    (hIncrease : ((n : ℝ) + 1) * Real.pi < p b - p a) :
    HasSignAlternations f (Icc a b) n := by
  let k : ℤ := ⌊p a / Real.pi⌋ + 1
  have hLow : p a < (k : ℝ) * Real.pi := (div_lt_iff₀ Real.pi_pos).mp (by
    dsimp only [k]
    rw [Int.cast_add, Int.cast_one]
    exact Int.lt_floor_add_one (p a / Real.pi))
  have hFloor : (⌊p a / Real.pi⌋ : ℝ) * Real.pi ≤ p a :=
    (le_div_iff₀ Real.pi_pos).mp (Int.floor_le _)
  have hHigh : ((k : ℝ) + n) * Real.pi < p b := by
    simp only [k, Int.cast_add, Int.cast_one]
    linarith only [hFloor, hIncrease]
  obtain ⟨x, hMono, hx⟩ := exists_ordered_phase_levels h hab ha hb k n hLow hHigh
  refine ⟨x, hMono, fun i => Ioo_subset_Icc_self (hx i).1, fun i => ?_⟩
  have hStep : p (x i.succ) = p (x i.castSucc) + Real.pi := by
    rw [(hx i.succ).2.2, (hx i.castSucc).2.2, Fin.val_succ, Fin.val_castSucc]
    push_cast
    ring
  have hCos : Real.cos (p (x i.castSucc)) ≠ 0 := by
    have hAbs : |Real.cos (p (x i.castSucc))| = 1 := by
      rw [(hx i.castSucc).2.2]
      exact_mod_cast Real.abs_cos_int_mul_pi (k + (i.castSucc.val : ℤ))
    intro he
    rw [he, abs_zero] at hAbs
    exact zero_ne_one hAbs
  rw [hf _ (hx i.castSucc).2.1, hf _ (hx i.succ).2.1, hStep, Real.cos_add_pi]
  let c := Real.cos (p (x i.castSucc))
  change A (x i.castSucc) * c * (A (x i.succ) * -c) < 0
  rw [show A (x i.castSucc) * c * (A (x i.succ) * -c) =
    -(A (x i.castSucc) * A (x i.succ) * c ^ 2) by ring]
  exact neg_neg_of_pos (mul_pos (mul_pos (hA _ (hx i.castSucc).2.1) (hA _ (hx i.succ).2.1))
    (sq_pos_of_ne_zero hCos))

end MeyerGeneralProblem
