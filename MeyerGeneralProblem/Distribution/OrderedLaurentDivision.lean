module

public import MeyerGeneralProblem.Cardinal.Strong.LaurentArrayAlgebraAction
public import Mathlib.Algebra.MonoidAlgebra.Support

@[expose] public section

/-!
# Ordered geometric division for locally finite Laurent arrays

The group can be dense in the real frequency line. Positivity of the
finitely many steps makes the power expansion coefficientwise finite
and bounds each frequency window by a finite box of multiplicities.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped Pointwise

variable {G : Type*} [AddCommGroup G]

/-- A contributing label in the order-`k` term has a numerator label
and exactly `k` positive steps, counted by their multiplicities. -/
theorem LaurentPower_support_multiplicities
    (q R : AddMonoidAlgebra ℂ G) {k : ℕ} {n : G}
    (hn : n ∈ (q ^ k * R).coeff.support) :
    ∃ a ∈ R.coeff.support, ∃ c : q.coeff.support → ℕ,
      (∑ j, c j) = k ∧ n = a + ∑ j, c j • (j : G) := by
  classical
  induction k generalizing n with
  | zero =>
    have hm : n ∈ R.coeff.support := by simpa using hn
    exact ⟨n, hm, 0, by simp, by simp⟩
  | succ k ih =>
    rw [pow_succ', mul_assoc] at hn
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp
      (AddMonoidAlgebra.support_coeff_mul_subset q (q ^ k * R) hn)
    obtain ⟨a, ha, c, hc, hrep⟩ := ih hy
    let i : q.coeff.support := ⟨x, hx⟩
    let d : q.coeff.support → ℕ := fun j => if j = i then 1 else 0
    have hd : (∑ j, d j) = 1 := by simp [d]
    have hval : (∑ j, d j • (j : G)) = x := by
      calc
        _ = ∑ j : q.coeff.support, if j = i then (i : G) else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases h : j = i <;> simp [d, h]
        _ = x := by simp [i]
    refine ⟨a, ha, fun j => c j + d j, ?_, ?_⟩
    · rw [Finset.sum_add_distrib, hc, hd]
    · simp only [add_nsmul, Finset.sum_add_distrib, hval]
      rw [← hxy, hrep]
      abel

/-- A power term has at least the numerator's lower weight plus its number of positive steps. -/
theorem LaurentPower_support_lower
    (L : G →+ ℝ) (q R : AddMonoidAlgebra ℂ G) (a δ : ℝ)
    (ha : ∀ x ∈ R.coeff.support, a ≤ L x) (hq : ∀ x ∈ q.coeff.support, δ ≤ L x)
    {k : ℕ} {n : G} (hn : n ∈ (q ^ k * R).coeff.support) :
    a + (k : ℝ) * δ ≤ L n := by
  obtain ⟨x, hx, c, hc, he⟩ := LaurentPower_support_multiplicities q R hn
  rw [he, map_add, map_sum]
  apply add_le_add (ha x hx)
  calc
    (k : ℝ) * δ = ∑ j : q.coeff.support, (c j : ℝ) * δ := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, hc]
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
      rw [map_nsmul, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hq j j.property) (Nat.cast_nonneg _)

/-- The finite geometric sum through powers strictly below `N`. -/
def orderedTruncation (q R : AddMonoidAlgebra ℂ G) (N : ℕ) : AddMonoidAlgebra ℂ G :=
  ∑ k ∈ Finset.range N, q ^ k * R

private theorem coeff_orderedTruncation
    (q R : AddMonoidAlgebra ℂ G) (N : ℕ) (n : G) :
    (orderedTruncation q R N).coeff n = ∑ k ∈ Finset.range N, (q ^ k * R).coeff n := by
  unfold orderedTruncation
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]

/-- The formal quotient by `1 - q`. The proof below supplies actual
coefficientwise finiteness from the positive order of the steps. -/
def orderedGeometricExpansion (q R : AddMonoidAlgebra ℂ G) (n : G) : ℂ :=
  ∑' k : ℕ, (q ^ k * R).coeff n

/-- A geometric coefficient below the next possible weight is already exact in a finite truncation. -/
theorem orderedGeometricExpansion_eq_coeff_of_lt
    (L : G →+ ℝ) (q R : AddMonoidAlgebra ℂ G) (a δ : ℝ)
    (ha : ∀ x ∈ R.coeff.support, a ≤ L x) (hq : ∀ x ∈ q.coeff.support, δ ≤ L x)
    (hδ : 0 ≤ δ) (N : ℕ) (n : G) (hn : L n < a + (N : ℝ) * δ) :
    orderedGeometricExpansion q R n = (orderedTruncation q R N).coeff n := by
  rw [orderedGeometricExpansion, coeff_orderedTruncation]
  apply tsum_eq_sum
  intro k hk
  have hNk : N ≤ k := by simpa using hk
  by_contra hne
  have hlo := LaurentPower_support_lower L q R a δ ha hq (Finsupp.mem_support_iff.mpr hne)
  have hmul : (N : ℝ) * δ ≤ (k : ℝ) * δ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hNk) hδ
  linarith

/-- The exact finite geometric product, including its last power term. -/
theorem orderedTruncation_sub_mul
    (q R : AddMonoidAlgebra ℂ G) (N : ℕ) :
    orderedTruncation q R N - q * orderedTruncation q R N = R - q ^ N * R := by
  induction N with
  | zero => simp [orderedTruncation]
  | succ N ih =>
    have hs : orderedTruncation q R (N + 1) =
      orderedTruncation q R N + q ^ N * R := Finset.sum_range_succ _ _
    rw [hs, mul_add, pow_succ', mul_assoc]
    calc
      _ = (orderedTruncation q R N - q * orderedTruncation q R N) +
          (q ^ N * R - q * (q ^ N * R)) := by abel
      _ = _ := by rw [ih]; abel

/-- Applying `1 - q` to the ordered expansion gives the exact numerator
at every label. Every coefficient in the recurrence is read from one
finite truncation chosen for that label and all its predecessor labels. -/
theorem orderedGeometricExpansion_sub_convolution
    (L : G →+ ℝ) (q R : AddMonoidAlgebra ℂ G) (a δ : ℝ)
    (ha : ∀ x ∈ R.coeff.support, a ≤ L x) (hq : ∀ x ∈ q.coeff.support, δ ≤ L x)
    (hδ : 0 < δ) (n : G) :
    orderedGeometricExpansion q R n -
      annihilatorArrayConvolution q.coeff (orderedGeometricExpansion q R) n = R.coeff n := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((L n - a) / δ)
  have hb : L n < a + (N : ℝ) * δ := by
    linarith [(div_lt_iff₀ hδ).mp hN]
  have hconv : annihilatorArrayConvolution q.coeff (orderedGeometricExpansion q R) n =
      (q * orderedTruncation q R N).coeff n := by
    rw [← annihilatorArrayConvolution_finite]
    unfold annihilatorArrayConvolution
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply orderedGeometricExpansion_eq_coeff_of_lt L q R a δ ha hq hδ.le N
    rw [map_sub]
    linarith [hq j hj]
  have hlast : (q ^ N * R).coeff n = 0 := by
    by_contra hz
    have hlow := LaurentPower_support_lower L q R a δ ha hq (Finsupp.mem_support_iff.mpr hz)
    linarith
  rw [orderedGeometricExpansion_eq_coeff_of_lt L q R a δ ha hq hδ.le N n hb, hconv]
  have ht := congrArg (fun p : AddMonoidAlgebra ℂ G => p.coeff n) (orderedTruncation_sub_mul q R N)
  simpa only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hlast, sub_zero] using ht

/-- Every bounded frequency window meets the expansion in a finite box of
step multiplicities. This keeps the proof valid for a dense frequency group. -/
theorem orderedGeometricExpansion_frequencyLocallyFinite
    (L : G →+ ℝ) (q R : AddMonoidAlgebra ℂ G) (a δ : ℝ)
    (ha : ∀ x ∈ R.coeff.support, a ≤ L x) (hq : ∀ x ∈ q.coeff.support, δ ≤ L x)
    (hδ : 0 < δ) : FrequencyLocallyFinite L (orderedGeometricExpansion q R) := by
  classical
  intro x y
  obtain ⟨N, hN⟩ := exists_nat_gt ((y - a) / δ)
  have hb : y < a + (N : ℝ) * δ := by linarith [(div_lt_iff₀ hδ).mp hN]
  refine (Set.finite_range (fun t : R.coeff.support × (q.coeff.support → Fin N) =>
    (t.1 : G) + ∑ j : q.coeff.support, (t.2 j : ℕ) • (j : G))).subset ?_
  rintro n ⟨hn, _, hny⟩
  have htr : (orderedTruncation q R N).coeff n ≠ 0 := by
    rw [← orderedGeometricExpansion_eq_coeff_of_lt L q R a δ ha hq hδ.le N n (hny.trans_lt hb)]
    exact hn
  rw [coeff_orderedTruncation] at htr
  obtain ⟨k, hk, hkn⟩ := Finset.exists_ne_zero_of_sum_ne_zero htr
  obtain ⟨r, hr, c, hc, he⟩ := LaurentPower_support_multiplicities q R
    (Finsupp.mem_support_iff.mpr hkn)
  let d (j : q.coeff.support) : Fin N :=
    ⟨c j, (show c j ≤ k by
      rw [← hc]
      exact Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) (Finset.mem_univ j)).trans_lt
        (Finset.mem_range.mp hk)⟩
  exact ⟨(⟨r, hr⟩, d), he.symm⟩

/-- A nonzero coefficient comes from a genuine positive-step word,
with the same real lower bound as the corresponding finite power. -/
theorem orderedGeometricExpansion_support_multiplicities
    (L : G →+ ℝ) (q R : AddMonoidAlgebra ℂ G) (a δ : ℝ)
    (ha : ∀ x ∈ R.coeff.support, a ≤ L x) (hq : ∀ x ∈ q.coeff.support, δ ≤ L x)
    (hδ : 0 < δ) {n : G} (hn : orderedGeometricExpansion q R n ≠ 0) :
    ∃ r ∈ R.coeff.support, ∃ c : q.coeff.support → ℕ, n = r + ∑ j, c j • (j : G) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((L n - a) / δ)
  have hb : L n < a + (N : ℝ) * δ := by linarith [(div_lt_iff₀ hδ).mp hN]
  rw [orderedGeometricExpansion_eq_coeff_of_lt L q R a δ ha hq hδ.le N n hb,
    coeff_orderedTruncation] at hn
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  obtain ⟨r, hr, c, _, hrep⟩ := LaurentPower_support_multiplicities q R
    (Finsupp.mem_support_iff.mpr hk)
  exact ⟨r, hr, c, hrep⟩

private theorem exists_Laurent_support_lower (L : G →+ ℝ) (p : AddMonoidAlgebra ℂ G) :
    ∃ a : ℝ, ∀ x ∈ p.coeff.support, a ≤ L x := by
  classical
  by_cases h : p.coeff.support.Nonempty
  · obtain ⟨x, _, hx⟩ := p.coeff.support.exists_min_image L h
    exact ⟨L x, hx⟩
  · refine ⟨0, fun x hx => ?_⟩
    exact (h ⟨x, hx⟩).elim

private theorem exists_Laurent_support_positive_lower (L : G →+ ℝ) (p : AddMonoidAlgebra ℂ G)
    (hp : ∀ x ∈ p.coeff.support, 0 < L x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ p.coeff.support, δ ≤ L x := by
  classical
  by_cases h : p.coeff.support.Nonempty
  · obtain ⟨x, hx, hmin⟩ := p.coeff.support.exists_min_image L h
    exact ⟨L x, hp x hx, hmin⟩
  · exact ⟨1, zero_lt_one, fun x hx => (h ⟨x, hx⟩).elim⟩

/-- Translation and rescaling of each coefficient at a chosen denominator label. -/
theorem normalizedLaurent_coeff (p R : AddMonoidAlgebra ℂ G) (m n : G) :
    (AddMonoidAlgebra.single (-m) (p.coeff m)⁻¹ * R).coeff n =
      (p.coeff m)⁻¹ * R.coeff (m + n) := by simp

/-- The nonconstant part of the normalized denominator uses only the
differences from the chosen denominator label. -/
theorem normalizedLaurentRemainder_support (p : AddMonoidAlgebra ℂ G) (m : G)
    (hm : p.coeff m ≠ 0) (n : G)
    (hn : n ∈ (1 - AddMonoidAlgebra.single (-m) (p.coeff m)⁻¹ * p).coeff.support) :
    m + n ∈ p.coeff.support ∧ m + n ≠ m := by
  classical
  let shift : AddMonoidAlgebra ℂ G := AddMonoidAlgebra.single (-m) (p.coeff m)⁻¹
  let q := 1 - shift * p
  have hmul (P : AddMonoidAlgebra ℂ G) (n : G) :
      (shift * P).coeff n = (p.coeff m)⁻¹ * P.coeff (m + n) :=
    normalizedLaurent_coeff p P m n
  have hc := Finsupp.mem_support_iff.mp hn
  change q.coeff n ≠ 0 at hc
  have hzero : n ≠ 0 := by
    intro he
    subst n
    have hh : q.coeff 0 = 0 := by
      simp only [q, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
        AddMonoidAlgebra.coeff_one_zero, hmul, add_zero, inv_mul_cancel₀ hm, sub_self]
    exact hc hh
  refine ⟨Finsupp.mem_support_iff.mpr ?_, by simpa using hzero⟩
  intro hpc
  apply hc
  rw [show q.coeff n = (1 : AddMonoidAlgebra ℂ G).coeff n - (shift * p).coeff n by rfl,
      hmul, hpc, mul_zero, sub_zero, AddMonoidAlgebra.one_def,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  exact ite_eq_right (Ne.symm hzero)

/-- Translate the chosen extremal term to the origin and divide by its
coefficient before forming the geometric expansion. -/
def orderedLaurentExpansion (p R : AddMonoidAlgebra ℂ G) (m : G) : G → ℂ :=
  let shift := AddMonoidAlgebra.single (-m) (p.coeff m)⁻¹
  orderedGeometricExpansion (1 - shift * p) (shift * R)

set_option maxHeartbeats 800000 in
/-- Exact ordered division at a lower extreme, including the support in
the translate of the nonnegative monoid of original denominator steps.
Changing the frequency map to its negative gives the upper expansion. -/
theorem orderedLaurentExpansion_at_extreme (L : G →+ ℝ)
    (p R : AddMonoidAlgebra ℂ G) (m : G) (hm : p.coeff m ≠ 0)
    (hmin : ∀ x ∈ p.coeff.support, x ≠ m → L m < L x) :
    FrequencyLocallyFinite L (orderedLaurentExpansion p R m) ∧
    (∀ n, annihilatorArrayConvolution p.coeff (orderedLaurentExpansion p R m) n = R.coeff n) ∧
    (∀ n, orderedLaurentExpansion p R m n ≠ 0 →
      ∃ r ∈ R.coeff.support,
        n - (r - m) ∈ AddSubmonoid.closure {d | ∃ x ∈ p.coeff.support, x ≠ m ∧ d = x - m}) := by
  classical
  let shift : AddMonoidAlgebra ℂ G := AddMonoidAlgebra.single (-m) (p.coeff m)⁻¹
  let unshift : AddMonoidAlgebra ℂ G := AddMonoidAlgebra.single m (p.coeff m)
  let q := 1 - shift * p
  let S := shift * R
  let u := orderedGeometricExpansion q S
  change FrequencyLocallyFinite L u ∧ _ ∧ _
  have hmul (P : AddMonoidAlgebra ℂ G) (n : G) :
      (shift * P).coeff n = (p.coeff m)⁻¹ * P.coeff (m + n) :=
    normalizedLaurent_coeff p P m n
  have hstep (n : G) (hn : n ∈ q.coeff.support) : m + n ∈ p.coeff.support ∧ m + n ≠ m :=
    normalizedLaurentRemainder_support p m hm n hn
  have hpos (n : G) (hn : n ∈ q.coeff.support) : 0 < L n := by
    obtain ⟨hnp, hne⟩ := hstep n hn
    have h := hmin (m + n) hnp hne
    rwa [map_add, lt_add_iff_pos_right] at h
  obtain ⟨a, ha⟩ := exists_Laurent_support_lower L S
  obtain ⟨δ, hδ, hd⟩ := exists_Laurent_support_positive_lower L q hpos
  refine ⟨orderedGeometricExpansion_frequencyLocallyFinite L q S a δ ha hd hδ, ?_, ?_⟩
  · have hconv : originalLaurentArrayAction (1 - q) u = fun n => S.coeff n := by
      funext n
      rw [map_sub, map_one, LinearMap.sub_apply]
      change u n - originalLaurentArrayAction q u n = _
      rw [originalLaurentArrayAction_apply]
      exact orderedGeometricExpansion_sub_convolution L q S a δ ha hd hδ n
    have hmonomial : unshift * shift = 1 := by
      simp [unshift, shift, hm, ← AddMonoidAlgebra.one_def]
    have hfactor : unshift * (1 - q) = p := by
      have hq' : 1 - q = shift * p := by dsimp [q]; abel
      rw [hq', ← mul_assoc, hmonomial, one_mul]
    intro n
    change annihilatorArrayConvolution p.coeff u n = R.coeff n
    rw [← originalLaurentArrayAction_apply p u n, ← hfactor, map_mul, Module.End.mul_apply,
      hconv, originalLaurentArrayAction_apply, annihilatorArrayConvolution_finite]
    simp only [S, ← mul_assoc, hmonomial, one_mul]
  · intro n hn
    obtain ⟨r, hr, c, hrep⟩ :=
      orderedGeometricExpansion_support_multiplicities L q S a δ ha hd hδ hn
    have hr' : m + r ∈ R.coeff.support := by
      apply Finsupp.mem_support_iff.mpr
      intro hz
      exact (Finsupp.mem_support_iff.mp hr) (by rw [show S = shift * R by rfl, hmul, hz, mul_zero])
    refine ⟨m + r, hr', ?_⟩
    have hu : n - (m + r - m) = ∑ j : q.coeff.support, c j • (j : G) := by rw [hrep]; abel
    rw [hu]
    apply AddSubmonoid.sum_mem
    intro j _
    apply AddSubmonoid.nsmul_mem
    apply AddSubmonoid.subset_closure
    obtain ⟨hj, hne⟩ := hstep j j.property
    exact ⟨m + (j : G), hj, hne, by abel⟩

end

end MeyerGeneralProblem
