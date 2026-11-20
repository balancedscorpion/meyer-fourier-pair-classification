module

public import MeyerGeneralProblem.Distribution.OrderedLaurentGrading
public import MeyerGeneralProblem.Distribution.LaurentJumpPresentation
public import MeyerGeneralProblem.Distribution.FiniteExponentialMean

@[expose] public section

/-!
# Polynomial growth on a root-free graded direction

A root-free polynomial slice gives a uniform bound on its entire degree
sum. Averaging the degree sum over the original real phases recovers
the bound for each original Laurent coefficient.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- The phase of an actual original frequency under real translation. -/
def originalLaurentPhase (L : G →+ ℝ) (x : ℝ) : Multiplicative G →* ℂ where
  toFun m := combModulationCharacter (L m.toAdd) x
  map_one' := by simp [combModulationCharacter_zero_left]
  map_mul' a b := by
    change combModulationCharacter (L (a.toAdd + b.toAdd)) x =
      combModulationCharacter (L a.toAdd) x * combModulationCharacter (L b.toAdd) x
    rw [map_add, combModulationCharacter_add_left]

private theorem phaseGradedPolynomial_eval_norm_le
    (ν : G →+ ℤ) (L : G →+ ℝ) (x : ℝ) (q : AddMonoidAlgebra ℂ G)
    (hq : ∀ m ∈ q.coeff.support, 0 ≤ ν m) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(phaseGradedPolynomial ν (originalLaurentPhase L x) q).eval z‖ ≤
      ∑ m ∈ q.coeff.support, ‖q.coeff m‖ := by
  rw [phaseGradedPolynomial_eq_sum_monomial ν _ q hq, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [norm_mul, norm_mul, norm_pow]
  change ‖q.coeff m‖ * ‖combModulationCharacter (L m) x‖ * ‖z‖ ^ (ν m).toNat ≤ ‖q.coeff m‖
  rw [norm_combModulationCharacter, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

private theorem phaseGradedPolynomial_natDegree_le
    (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ) (q : AddMonoidAlgebra ℂ G)
    (hq : ∀ m ∈ q.coeff.support, 0 ≤ ν m) :
    (phaseGradedPolynomial ν χ q).natDegree ≤ q.coeff.support.sup fun m => (ν m).toNat := by
  rw [phaseGradedPolynomial_eq_sum_monomial ν χ q hq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  exact (Polynomial.natDegree_monomial_le _).trans (Finset.le_sup (f := fun j => (ν j).toNat) hm)

private theorem exists_grade_comparison
    (ν : G →+ ℤ) (L : G →+ ℝ) (hL : Function.Injective L)
    (S : Finset G) (hν : ∀ m ∈ S, 0 ≤ ν m) (hL₀ : ∀ m ∈ S, 0 ≤ L m) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m ∈ S, ((ν m : ℤ) : ℝ) ≤ C * L m := by
  classical
  let F (m : G) := ((ν m : ℤ) : ℝ) / L m
  let C := 1 + ∑ m ∈ S, F m
  have hF (m : G) (hm : m ∈ S) : 0 ≤ F m :=
    div_nonneg (by exact_mod_cast hν m hm) (hL₀ m hm)
  refine ⟨C, le_add_of_nonneg_right (Finset.sum_nonneg hF), fun m hm => ?_⟩
  by_cases hz : L m = 0
  · have he : m = 0 := hL (hz.trans (map_zero L).symm)
    simp [he]
  · have hm' : 0 < L m := lt_of_le_of_ne (hL₀ m hm) (Ne.symm hz)
    exact (div_le_iff₀ hm').mp ((Finset.single_le_sum hF hm).trans (le_add_of_nonneg_left zero_le_one))

/-- Polynomial degree bounds for every stable specialised quotient imply
polynomial growth in the original real frequency. The proof recovers
the original coefficients even when several labels have the same degree. -/
theorem orderedGeometricExpansion_polynomialGrowth_of_phaseGradedRootFree
    (ν : G →+ ℤ) (L : G →+ ℝ) (hL : Function.Injective L)
    (q R : AddMonoidAlgebra ℂ G)
    (hνq : ∀ m ∈ q.coeff.support, 0 < ν m) (hνR : ∀ m ∈ R.coeff.support, 0 ≤ ν m)
    (hLq : ∀ m ∈ q.coeff.support, 0 < L m) (hLR : ∀ m ∈ R.coeff.support, 0 ≤ L m)
    (hroot : ∀ x : ℝ, ∀ z : ℂ, ‖z‖ < 1 →
      (phaseGradedPolynomial ν (originalLaurentPhase L x) (1 - q)).eval z ≠ 0) :
    ∃ M : ℝ, ∃ k : ℕ, 0 ≤ M ∧ ∀ n : G,
      ‖orderedGeometricExpansion q R n‖ ≤ M * (1 + |L n|) ^ k := by
  classical
  let D := (1 - q).coeff.support.sup fun m => (ν m).toNat
  let M := ∑ m ∈ R.coeff.support, ‖R.coeff m‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hν₀ (m : G) (hm : m ∈ q.coeff.support ∪ R.coeff.support) : 0 ≤ ν m :=
    (Finset.mem_union.mp hm).elim (fun h => (hνq m h).le) (hνR m)
  have hL₀ (m : G) (hm : m ∈ q.coeff.support ∪ R.coeff.support) : 0 ≤ L m :=
    (Finset.mem_union.mp hm).elim (fun h => (hLq m h).le) (hLR m)
  obtain ⟨C, hC, hid⟩ := exists_grade_comparison ν L hL
    (q.coeff.support ∪ R.coeff.support) hν₀ hL₀
  have hrestrict (j : ℕ) (x : ℝ) :
      ‖∑ m ∈ orderedGradeSlice ν q R j,
        orderedGeometricExpansion q R m * combModulationCharacter (L m) x‖ ≤
          (Real.exp 1 * M) * (2 * (1 + (j : ℝ))) ^ D := by
    let χ := originalLaurentPhase L x
    let P := phaseGradedPolynomial ν χ (1 - q)
    let Q := phaseGradedPolynomial ν χ R
    have hdeg : P.natDegree ≤ D := phaseGradedPolynomial_natDegree_le ν χ _
      (one_sub_degree_nonneg ν q hνq)
    have hP₀ : P.eval 0 = 1 := phaseGradedPolynomial_one_sub_eval_zero ν χ q hνq
    have hcoeff := polynomialQuotient_taylorCoefficient_norm_le P Q (hroot x) M hM
      (phaseGradedPolynomial_eval_norm_le ν L x R hνR) j
    rw [hP₀, norm_one, div_one] at hcoeff
    change ‖∑ m ∈ orderedGradeSlice ν q R j,
      orderedGeometricExpansion q R m * χ (.ofAdd m)‖ ≤ _
    rw [← orderedGradeSeries_coeff ν χ q R hνq hνR j,
      orderedGradeSeries_eq_actualTaylorSeriesAtZero ν χ q R hνq hνR,
      actualTaylorSeriesAtZero, PowerSeries.coeff_mk]
    exact hcoeff.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) j]) hdeg) (by positivity))
  refine ⟨(Real.exp 1 * M) * (2 * C) ^ D, D, by positivity, fun n => ?_⟩
  by_cases hn : orderedGeometricExpansion q R n = 0
  · rw [hn, norm_zero]
    positivity
  obtain ⟨r, hr, c, hrep⟩ :=
    orderedGeometricExpansion_support_multiplicities_of_grade ν q R hνq hνR hn
  have hνn : 0 ≤ ν n := by
    rw [hrep, map_add, map_sum]
    refine add_nonneg (hνR r hr) (Finset.sum_nonneg fun m _ => ?_)
    rw [map_nsmul, nsmul_eq_mul]
    have hm := (hνq m m.property).le
    positivity
  have hdeg : ((ν n : ℤ) : ℝ) ≤ C * L n := by
    let D' := (Int.castAddHom ℝ).comp ν
    have hD (m : G) (hm : m ∈ q.coeff.support ∪ R.coeff.support) :
        D' m ≤ C * L m := hid m hm
    change D' n ≤ C * L n
    rw [hrep]
    simp only [map_add, map_sum, mul_add, Finset.mul_sum]
    refine add_le_add (hD r (Finset.mem_union_right _ hr)) (Finset.sum_le_sum fun m _ => ?_)
    rw [map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul, mul_left_comm C]
    exact mul_le_mul_of_nonneg_left (hD m (Finset.mem_union_left _ m.property)) (Nat.cast_nonneg _)
  let j := (ν n).toNat
  have hj : (j : ℤ) = ν n := Int.toNat_of_nonneg hνn
  have hm : n ∈ orderedGradeSlice ν q R j := (mem_orderedGradeSlice ν q R hνq hνR j n).mpr ⟨hn, hj.symm⟩
  have hlabel := norm_coefficient_le_of_finiteExponentialSum_bound (orderedGradeSlice ν q R j)
    L (orderedGeometricExpansion q R) hL.injOn _ (hrestrict j) n hm
  have hbound : 2 * (1 + (j : ℝ)) ≤ (2 * C) * (1 + |L n|) := by
    have hj' : (j : ℝ) = ((ν n : ℤ) : ℝ) := by exact_mod_cast hj
    rw [hj']
    have hle := mul_le_mul_of_nonneg_left (le_abs_self (L n)) (show 0 ≤ C by linarith)
    linarith
  calc
    _ ≤ (Real.exp 1 * M) * (2 * (1 + (j : ℝ))) ^ D := hlabel
    _ ≤ (Real.exp 1 * M) * ((2 * C) * (1 + |L n|)) ^ D :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbound _) (by positivity)
    _ = _ := by simp only [mul_pow, mul_assoc]


/-- The ordinary polynomial slices of an extremally normalized denominator
are zero-free in the open unit disk along this integral direction. -/
def RootFreeNormalizedLaurentSlices (ν : G →+ ℤ) (L : G →+ ℝ)
    (p : AddMonoidAlgebra ℂ G) (m : G) : Prop :=
  ∀ x : ℝ, ∀ z : ℂ, ‖z‖ < 1 →
    (phaseGradedPolynomial ν (originalLaurentPhase L x)
      (AddMonoidAlgebra.single (-m) (p.coeff m)⁻¹ * p)).eval z ≠ 0

/-- Growth on one ordered side of the original finite denominator at
a common extremum of the integral and real frequency directions. -/
theorem orderedLaurentExpansion_polynomialGrowth_of_rootFreeNormalizedSlices
    (ν : G →+ ℤ) (L : G →+ ℝ) (hL : Function.Injective L)
    (p R : AddMonoidAlgebra ℂ G) (m : G) (hm : p.coeff m ≠ 0)
    (hνmin : ∀ x ∈ p.coeff.support, x ≠ m → ν m < ν x)
    (hLmin : ∀ x ∈ p.coeff.support, x ≠ m → L m < L x)
    (hνR : ∀ x ∈ R.coeff.support, ν m ≤ ν x)
    (hLR : ∀ x ∈ R.coeff.support, L m ≤ L x)
    (hroot : RootFreeNormalizedLaurentSlices ν L p m) :
    ∃ M : ℝ, ∃ k : ℕ, 0 ≤ M ∧ ∀ n : G,
      ‖orderedLaurentExpansion p R m n‖ ≤ M * (1 + |L n|) ^ k := by
  classical
  let shift : AddMonoidAlgebra ℂ G := AddMonoidAlgebra.single (-m) (p.coeff m)⁻¹
  let q := 1 - shift * p
  let Q := shift * R
  have hνq (n : G) (hn : n ∈ q.coeff.support) : 0 < ν n := by
    obtain ⟨hs, hne⟩ := normalizedLaurentRemainder_support p m hm n hn
    have h := hνmin (m + n) hs hne
    rwa [map_add, lt_add_iff_pos_right] at h
  have hLq (n : G) (hn : n ∈ q.coeff.support) : 0 < L n := by
    obtain ⟨hs, hne⟩ := normalizedLaurentRemainder_support p m hm n hn
    have h := hLmin (m + n) hs hne
    rwa [map_add, lt_add_iff_pos_right] at h
  have hQ (n : G) (hn : n ∈ Q.coeff.support) : m + n ∈ R.coeff.support := by
    apply Finsupp.mem_support_iff.mpr
    intro hz
    have hn' := Finsupp.mem_support_iff.mp hn
    change (shift * R).coeff n ≠ 0 at hn'
    apply hn'
    rw [normalizedLaurent_coeff, hz, mul_zero]
  have hνQ (n : G) (hn : n ∈ Q.coeff.support) : 0 ≤ ν n := by
    have h := hνR (m + n) (hQ n hn)
    rwa [map_add, le_add_iff_nonneg_right] at h
  have hLQ (n : G) (hn : n ∈ Q.coeff.support) : 0 ≤ L n := by
    have h := hLR (m + n) (hQ n hn)
    rwa [map_add, le_add_iff_nonneg_right] at h
  apply orderedGeometricExpansion_polynomialGrowth_of_phaseGradedRootFree ν L hL q Q
    hνq hνQ hLq hLQ
  intro x z hz
  have he : 1 - q = shift * p := sub_sub_cancel _ _
  rw [he]
  exact hroot x z hz


/-- The two root-free oriented directions give a common polynomial
coefficient bound for the full jump, with both halves in the original
real frequency variable. -/
theorem orderedLaurentJump_polynomialGrowth_of_rootFreeNormalizedSlices
    (νlo νhi : G →+ ℤ) (L : G →+ ℝ) (hL : Function.Injective L)
    (p R : AddMonoidAlgebra ℂ G) (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hνlo : ∀ x ∈ p.coeff.support, x ≠ lo → νlo lo < νlo x)
    (hνhi : ∀ x ∈ p.coeff.support, x ≠ hi → νhi hi < νhi x)
    (hmin : ∀ x ∈ p.coeff.support, x ≠ lo → L lo < L x)
    (hmax : ∀ x ∈ p.coeff.support, x ≠ hi → L x < L hi)
    (hRν : ∀ x ∈ R.coeff.support, νlo lo ≤ νlo x ∧ νhi hi ≤ νhi x)
    (hR : ∀ x ∈ R.coeff.support, L lo ≤ L x ∧ L x ≤ L hi)
    (hrootlo : RootFreeNormalizedLaurentSlices νlo L p lo)
    (hroothi : RootFreeNormalizedLaurentSlices νhi (-L) p hi) :
    ∃ M : ℝ, ∃ k : ℕ, 0 ≤ M ∧ ∀ n : G,
      ‖orderedLaurentJump p R lo hi n‖ ≤ M * (1 + |L n|) ^ k := by
  have hL' : Function.Injective (-L) := by
    intro x y h
    apply hL
    simpa only [AddMonoidHom.neg_apply, neg_inj] using h
  have hmax' : ∀ x ∈ p.coeff.support, x ≠ hi → (-L) hi < (-L) x := by
    simpa only [AddMonoidHom.neg_apply, neg_lt_neg_iff] using hmax
  have hR' (x : G) (hx : x ∈ R.coeff.support) : (-L) hi ≤ (-L) x := by
    simpa only [AddMonoidHom.neg_apply, neg_le_neg_iff] using (hR x hx).2
  obtain ⟨Mlo, klo, hMlo, hblo⟩ := orderedLaurentExpansion_polynomialGrowth_of_rootFreeNormalizedSlices
    νlo L hL p R lo hlo hνlo hmin (fun x hx => (hRν x hx).1) (fun x hx => (hR x hx).1) hrootlo
  obtain ⟨Mhi, khi, hMhi, hbhi⟩ := orderedLaurentExpansion_polynomialGrowth_of_rootFreeNormalizedSlices
    νhi (-L) hL' p R hi hhi hνhi hmax' (fun x hx => (hRν x hx).2) hR' hroothi
  simp only [AddMonoidHom.neg_apply, abs_neg] at hbhi
  let k := max klo khi
  refine ⟨Mlo + Mhi, k, add_nonneg hMlo hMhi, fun n => ?_⟩
  have hb : 1 ≤ 1 + |L n| := by linarith [abs_nonneg (L n)]
  have hc (M : ℝ) (hM : 0 ≤ M) (l : ℕ) (hl : l ≤ k) :
      M * (1 + |L n|) ^ l ≤ M * (1 + |L n|) ^ k :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb hl) hM
  change ‖orderedLaurentExpansion p R lo n - orderedLaurentExpansion p R hi n‖ ≤ _
  calc
    _ ≤ ‖orderedLaurentExpansion p R lo n‖ + ‖orderedLaurentExpansion p R hi n‖ :=
      norm_sub_le _ _
    _ ≤ Mlo * (1 + |L n|) ^ k + Mhi * (1 + |L n|) ^ k :=
      add_le_add ((hblo n).trans (hc Mlo hMlo klo (le_max_left _ _)))
        ((hbhi n).trans (hc Mhi hMhi khi (le_max_right _ _)))
    _ = _ := by rw [add_mul]

end

end MeyerGeneralProblem
