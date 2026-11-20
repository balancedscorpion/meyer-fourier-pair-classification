module

public import MeyerGeneralProblem.Distribution.OrderedLaurentDivision
public import MeyerGeneralProblem.Distribution.PolynomialQuotientGrowth
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

@[expose] public section

/-!
# Integral grading of an ordered Laurent expansion

An integral degree map combines every original label of a fixed degree,
with its original phase. Each grade is a finite sum even when the real
frequency module is dense. The graded series satisfies the genuine
polynomial quotient equation.
-/

namespace MeyerGeneralProblem

noncomputable section

open LaurentPolynomial

variable {G : Type*} [AddCommGroup G]

def phaseGradedMonomial (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ) :
    Multiplicative G →* LaurentPolynomial ℂ where
  toFun m := C (χ m) * T (ν m.toAdd)
  map_one' := by simp
  map_mul' a b := by
    change C (χ (a * b)) * T (ν (a.toAdd + b.toAdd)) =
      C (χ a) * T (ν a.toAdd) * (C (χ b) * T (ν b.toAdd))
    rw [map_mul, map_add, map_mul, T_add]
    ac_rfl

/-- Specialise the original finite Laurent coefficients by degree and phase. -/
def phaseGradedLaurentHom (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ) :
    AddMonoidAlgebra ℂ G →+* LaurentPolynomial ℂ :=
  AddMonoidAlgebra.liftNCRingHom C (phaseGradedMonomial ν χ) (fun _ _ => Commute.all _ _)

@[simp]
theorem phaseGradedLaurentHom_single (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ)
    (m : G) (z : ℂ) :
    phaseGradedLaurentHom ν χ (AddMonoidAlgebra.single m z) =
      AddMonoidAlgebra.single (ν m) (z * χ (.ofAdd m)) := by
  simp [phaseGradedLaurentHom, phaseGradedMonomial, LaurentPolynomial.single_eq_C_mul_T, ← mul_assoc]

/-- The polynomial obtained from the nonnegative degrees of a finite Laurent sum. -/
def phaseGradedPolynomial (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ)
    (p : AddMonoidAlgebra ℂ G) : Polynomial ℂ :=
  LaurentPolynomial.trunc (phaseGradedLaurentHom ν χ p)

open scoped BigOperators in
theorem phaseGradedLaurentHom_coeff (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ)
    (p : AddMonoidAlgebra ℂ G) (j : ℤ) :
    (phaseGradedLaurentHom ν χ p).coeff j =
      ∑ m ∈ p.coeff.support with ν m = j, p.coeff m * χ (.ofAdd m) := by
  classical
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  simp only [Finsupp.sum, map_sum, phaseGradedLaurentHom_single, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    Finset.sum_filter]

private theorem phaseGradedPolynomial_coeff_aux (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ)
    (p : AddMonoidAlgebra ℂ G) (j : ℕ) :
    (phaseGradedPolynomial ν χ p).coeff j = (phaseGradedLaurentHom ν χ p).coeff (j : ℤ) := by
  simp [phaseGradedPolynomial, LaurentPolynomial.trunc, ← Polynomial.toFinsupp_apply]

theorem phaseGradedPolynomial_coeff (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ)
    (p : AddMonoidAlgebra ℂ G) (j : ℕ) :
    (phaseGradedPolynomial ν χ p).coeff j =
      ∑ m ∈ p.coeff.support with ν m = (j : ℤ), p.coeff m * χ (.ofAdd m) := by
  rw [phaseGradedPolynomial_coeff_aux, phaseGradedLaurentHom_coeff]

private theorem toLaurent_phaseGradedPolynomial (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ)
    (p : AddMonoidAlgebra ℂ G) (hp : ∀ m ∈ p.coeff.support, 0 ≤ ν m) :
    Polynomial.toLaurent (phaseGradedPolynomial ν χ p) = phaseGradedLaurentHom ν χ p := by
  apply LaurentPolynomial.ext
  intro j
  by_cases hj : 0 ≤ j
  · lift j to ℕ using hj
    rw [LaurentPolynomial.coeff_toLaurent]
    change ((phaseGradedPolynomial ν χ p).toFinsupp.coeff.mapDomain
      (Nat.castEmbedding : ℕ ↪ ℤ)) (Nat.castEmbedding j) = _
    rw [Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective]
    rw [Polynomial.toFinsupp_apply]
    exact phaseGradedPolynomial_coeff_aux ν χ p j
  · have h₁ : ((phaseGradedPolynomial ν χ p).toLaurent).coeff j = 0 := by
      apply Finsupp.notMem_support_iff.mp
      rw [LaurentPolynomial.support_coeff_toLaurent]
      intro hmem
      obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hmem
      exact hj (Int.natCast_nonneg k)
    have h₂ : (phaseGradedLaurentHom ν χ p).coeff j = 0 := by
      rw [phaseGradedLaurentHom_coeff]
      apply Finset.sum_eq_zero
      intro m hm
      obtain ⟨hm, he⟩ := Finset.mem_filter.mp hm
      exact (hj (he ▸ hp m hm)).elim
    rw [h₁, h₂]

/-- Graded numerator or denominator as the literal sum of its original monomials. -/
theorem phaseGradedPolynomial_eq_sum_monomial (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ)
    (p : AddMonoidAlgebra ℂ G) (hp : ∀ m ∈ p.coeff.support, 0 ≤ ν m) :
    phaseGradedPolynomial ν χ p = ∑ m ∈ p.coeff.support,
      Polynomial.monomial (ν m).toNat (p.coeff m * χ (.ofAdd m)) := by
  classical
  ext j
  rw [phaseGradedPolynomial_coeff, Finset.sum_filter, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Polynomial.coeff_monomial]
  by_cases he : ν m = (j : ℤ)
  · simp [he]
  · have h' : (ν m).toNat ≠ j := by
      intro h
      have hnonneg := hp m hm
      exact he (by omega)
    simp [he, h']

private theorem phaseGradedPolynomial_coeff_eq_on_grade
    (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ) (p q : AddMonoidAlgebra ℂ G) (j : ℕ)
    (he : ∀ m : G, ν m = (j : ℤ) → p.coeff m = q.coeff m) :
    (phaseGradedPolynomial ν χ p).coeff j = (phaseGradedPolynomial ν χ q).coeff j := by
  classical
  rw [phaseGradedPolynomial_coeff, phaseGradedPolynomial_coeff]
  apply Finset.sum_congr
  · ext m
    by_cases hm : ν m = (j : ℤ)
    · simp only [Finset.mem_filter, Finsupp.mem_support_iff, he m hm]
    · simp [hm]
  · intro m hm
    rw [he m (Finset.mem_filter.mp hm).2]

private abbrev realGrading (ν : G →+ ℤ) : G →+ ℝ := (Int.castAddHom ℝ).comp ν

private theorem realGrading_numerator
    (ν : G →+ ℤ) (R : AddMonoidAlgebra ℂ G) (hR : ∀ m ∈ R.coeff.support, 0 ≤ ν m)
    (m : G) (hm : m ∈ R.coeff.support) : 0 ≤ realGrading ν m := by
  change 0 ≤ ((ν m : ℤ) : ℝ)
  exact_mod_cast hR m hm

private theorem realGrading_steps
    (ν : G →+ ℤ) (q : AddMonoidAlgebra ℂ G) (hq : ∀ m ∈ q.coeff.support, 0 < ν m)
    (m : G) (hm : m ∈ q.coeff.support) : 1 ≤ realGrading ν m := by
  change 1 ≤ ((ν m : ℤ) : ℝ)
  exact_mod_cast Int.add_one_le_of_lt (hq m hm)

private theorem LaurentPower_le_degree
    (ν : G →+ ℤ) (q R : AddMonoidAlgebra ℂ G)
    (hq : ∀ m ∈ q.coeff.support, 0 < ν m) (hR : ∀ m ∈ R.coeff.support, 0 ≤ ν m)
    (k : ℕ) (m : G) (hm : m ∈ (q ^ k * R).coeff.support) : (k : ℤ) ≤ ν m := by
  have h := LaurentPower_support_lower (realGrading ν) q R 0 1
    (realGrading_numerator ν R hR) (realGrading_steps ν q hq) hm
  simp only [zero_add, mul_one] at h
  change (k : ℝ) ≤ ((ν m : ℤ) : ℝ) at h
  exact_mod_cast h

private theorem orderedTruncation_degree_nonneg
    (ν : G →+ ℤ) (q R : AddMonoidAlgebra ℂ G)
    (hq : ∀ m ∈ q.coeff.support, 0 < ν m) (hR : ∀ m ∈ R.coeff.support, 0 ≤ ν m)
    (N : ℕ) (m : G) (hm : m ∈ (orderedTruncation q R N).coeff.support) : 0 ≤ ν m := by
  have hn := Finsupp.mem_support_iff.mp hm
  unfold orderedTruncation at hn
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at hn
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact (Int.natCast_nonneg k).trans (LaurentPower_le_degree ν q R hq hR k m
    (Finsupp.mem_support_iff.mpr hk))

/-- The normalized denominator has no negative integral degrees. -/
theorem one_sub_degree_nonneg (ν : G →+ ℤ) (q : AddMonoidAlgebra ℂ G)
    (hq : ∀ m ∈ q.coeff.support, 0 < ν m)
    (m : G) (hm : m ∈ (1 - q).coeff.support) : 0 ≤ ν m := by
  by_cases he : m = 0
  · simp [he]
  · have h₁ : (1 : AddMonoidAlgebra ℂ G).coeff m = 0 := by simp [AddMonoidAlgebra.one_def, he]
    have hn : q.coeff m ≠ 0 := by
      intro hz
      exact (Finsupp.mem_support_iff.mp hm) (by simp [h₁, hz])
    exact (hq m (Finsupp.mem_support_iff.mpr hn)).le

private theorem gradeCoeff_eq_truncation
    (ν : G →+ ℤ) (q R : AddMonoidAlgebra ℂ G)
    (hq : ∀ m ∈ q.coeff.support, 0 < ν m) (hR : ∀ m ∈ R.coeff.support, 0 ≤ ν m)
    (j N : ℕ) (hj : j < N) (m : G) (hm : ν m = (j : ℤ)) :
    orderedGeometricExpansion q R m = (orderedTruncation q R N).coeff m := by
  apply orderedGeometricExpansion_eq_coeff_of_lt (realGrading ν) q R 0 1
    (realGrading_numerator ν R hR) (realGrading_steps ν q hq) zero_le_one N m
  change ((ν m : ℤ) : ℝ) < 0 + (N : ℝ) * 1
  rw [hm, Int.cast_natCast, zero_add, mul_one]
  exact_mod_cast hj

/-- Every present original label is a numerator label plus a nonnegative sum of the graded steps. -/
theorem orderedGeometricExpansion_support_multiplicities_of_grade
    (ν : G →+ ℤ) (q R : AddMonoidAlgebra ℂ G)
    (hq : ∀ m ∈ q.coeff.support, 0 < ν m) (hR : ∀ m ∈ R.coeff.support, 0 ≤ ν m)
    {m : G} (hm : orderedGeometricExpansion q R m ≠ 0) :
    ∃ r ∈ R.coeff.support, ∃ c : q.coeff.support → ℕ, m = r + ∑ j, c j • (j : G) :=
  orderedGeometricExpansion_support_multiplicities (realGrading ν) q R 0 1
    (realGrading_numerator ν R hR) (realGrading_steps ν q hq) zero_lt_one hm

/-- The finite set of original labels appearing in a fixed integral grade. -/
def orderedGradeSlice (ν : G →+ ℤ) (q R : AddMonoidAlgebra ℂ G) (j : ℕ) : Finset G :=
  (orderedTruncation q R (j + 1)).coeff.support.filter fun m => ν m = (j : ℤ)

/-- The grade contains exactly the nonzero coefficients of the original expansion in that degree. -/
theorem mem_orderedGradeSlice (ν : G →+ ℤ) (q R : AddMonoidAlgebra ℂ G)
    (hq : ∀ m ∈ q.coeff.support, 0 < ν m) (hR : ∀ m ∈ R.coeff.support, 0 ≤ ν m)
    (j : ℕ) (m : G) :
    m ∈ orderedGradeSlice ν q R j ↔ orderedGeometricExpansion q R m ≠ 0 ∧ ν m = (j : ℤ) := by
  unfold orderedGradeSlice
  simp only [Finset.mem_filter, Finsupp.mem_support_iff]
  by_cases hm : ν m = (j : ℤ)
  · rw [gradeCoeff_eq_truncation ν q R hq hR j _ (Nat.lt_succ_self _) m hm]
  · simp [hm]

/-- The actual grouped coefficients of the geometric expansion, in integral degree order. -/
def orderedGradeSeries (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ)
    (q R : AddMonoidAlgebra ℂ G) : PowerSeries ℂ :=
  PowerSeries.mk fun j => (phaseGradedPolynomial ν χ (orderedTruncation q R (j + 1))).coeff j

theorem orderedGradeSeries_coeff (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ)
    (q R : AddMonoidAlgebra ℂ G) (hq : ∀ m ∈ q.coeff.support, 0 < ν m)
    (hR : ∀ m ∈ R.coeff.support, 0 ≤ ν m) (j : ℕ) :
    PowerSeries.coeff j (orderedGradeSeries ν χ q R) =
      ∑ m ∈ orderedGradeSlice ν q R j, orderedGeometricExpansion q R m * χ (.ofAdd m) := by
  classical
  rw [orderedGradeSeries, PowerSeries.coeff_mk, phaseGradedPolynomial_coeff]
  apply Finset.sum_congr rfl
  intro m hm
  rw [gradeCoeff_eq_truncation ν q R hq hR j _ (Nat.lt_succ_self _) m (Finset.mem_filter.mp hm).2]

/-- The graded series solves the exact polynomial equation with denominator given by the
graded Laurent polynomial `1 - q`. Every collision contributes its actual phase. -/
theorem phaseGradedPolynomial_mul_orderedGradeSeries (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ)
    (q R : AddMonoidAlgebra ℂ G) (hq : ∀ m ∈ q.coeff.support, 0 < ν m)
    (hR : ∀ m ∈ R.coeff.support, 0 ≤ ν m) :
    (phaseGradedPolynomial ν χ (1 - q) : PowerSeries ℂ) * orderedGradeSeries ν χ q R =
      (phaseGradedPolynomial ν χ R : PowerSeries ℂ) := by
  classical
  ext j
  let P := phaseGradedPolynomial ν χ (1 - q)
  let A := orderedTruncation q R (j + 1)
  let E := q ^ (j + 1) * R
  let F := phaseGradedPolynomial ν χ A
  have hA := orderedTruncation_degree_nonneg ν q R hq hR (j + 1)
  have hE (m : G) (hm : m ∈ E.coeff.support) : 0 ≤ ν m :=
    (Int.natCast_nonneg (j + 1)).trans (LaurentPower_le_degree ν q R hq hR (j + 1) m hm)
  have hprod : P * F = phaseGradedPolynomial ν χ R - phaseGradedPolynomial ν χ E := by
    apply Polynomial.toLaurent_injective
    dsimp only [P, F]
    rw [map_mul, map_sub,
      toLaurent_phaseGradedPolynomial ν χ _ (one_sub_degree_nonneg ν q hq),
      toLaurent_phaseGradedPolynomial ν χ _ hA,
      toLaurent_phaseGradedPolynomial ν χ _ hR,
      toLaurent_phaseGradedPolynomial ν χ _ hE, ← map_mul, ← map_sub]
    congr 1
    rw [sub_mul, one_mul]
    exact orderedTruncation_sub_mul q R (j + 1)
  have hErr : (phaseGradedPolynomial ν χ E).coeff j = 0 := by
    rw [phaseGradedPolynomial_coeff]
    apply Finset.sum_eq_zero
    intro m hm
    obtain ⟨hm, he⟩ := Finset.mem_filter.mp hm
    have hc := LaurentPower_le_degree ν q R hq hR (j + 1) m hm
    rw [he] at hc
    omega
  have hcomp (k : ℕ) (hk : k ≤ j) :
      PowerSeries.coeff k (orderedGradeSeries ν χ q R) = PowerSeries.coeff k F := by
    rw [orderedGradeSeries, PowerSeries.coeff_mk, Polynomial.coeff_coe]
    apply phaseGradedPolynomial_coeff_eq_on_grade
    intro m hm
    have h₁ := gradeCoeff_eq_truncation ν q R hq hR k (k + 1) (Nat.lt_succ_self _) m hm
    have h₂ := gradeCoeff_eq_truncation ν q R hq hR k (j + 1) (Nat.lt_succ_of_le hk) m hm
    exact h₁.symm.trans h₂
  change PowerSeries.coeff j ((P : PowerSeries ℂ) * orderedGradeSeries ν χ q R) = _
  calc
    _ = PowerSeries.coeff j ((P : PowerSeries ℂ) * (F : PowerSeries ℂ)) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro ab hab
      rw [hcomp ab.2 (by have h := Finset.mem_antidiagonal.mp hab; omega)]
    _ = _ := by
      rw [← Polynomial.coe_mul, Polynomial.coeff_coe, hprod, Polynomial.coeff_sub, hErr,
        sub_zero, Polynomial.coeff_coe]

theorem phaseGradedPolynomial_one_sub_eval_zero (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ)
    (q : AddMonoidAlgebra ℂ G) (hq : ∀ m ∈ q.coeff.support, 0 < ν m) :
    (phaseGradedPolynomial ν χ (1 - q)).eval 0 = 1 := by
  classical
  have hq₀ : (phaseGradedPolynomial ν χ q).coeff 0 = 0 := by
    rw [phaseGradedPolynomial_coeff]
    apply Finset.sum_eq_zero
    intro m hm
    obtain ⟨hm, he⟩ := Finset.mem_filter.mp hm
    exact ((hq m hm).ne' (by simpa using he)).elim
  rw [← Polynomial.coeff_zero_eq_eval_zero,
    show phaseGradedPolynomial ν χ (1 - q) =
      phaseGradedPolynomial ν χ 1 - phaseGradedPolynomial ν χ q by simp [phaseGradedPolynomial],
    Polynomial.coeff_sub, hq₀, sub_zero]
  rw [phaseGradedPolynomial_coeff_aux, map_one]
  simp

/-- Every graded coefficient is the corresponding genuine Taylor coefficient of the
specialised numerator and denominator quotient. -/
theorem orderedGradeSeries_eq_actualTaylorSeriesAtZero (ν : G →+ ℤ) (χ : Multiplicative G →* ℂ)
    (q R : AddMonoidAlgebra ℂ G) (hq : ∀ m ∈ q.coeff.support, 0 < ν m)
    (hR : ∀ m ∈ R.coeff.support, 0 ≤ ν m) :
    orderedGradeSeries ν χ q R = actualTaylorSeriesAtZero (fun z =>
      (phaseGradedPolynomial ν χ R).eval z / (phaseGradedPolynomial ν χ (1 - q)).eval z) := by
  have hP : (phaseGradedPolynomial ν χ (1 - q)).eval 0 ≠ 0 := by
    rw [phaseGradedPolynomial_one_sub_eval_zero ν χ q hq]
    exact one_ne_zero
  apply mul_left_cancel₀ (a := (phaseGradedPolynomial ν χ (1 - q) : PowerSeries ℂ))
  · intro hz
    apply hP
    simpa only [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, map_zero] using
      congrArg (PowerSeries.coeff 0) hz
  · rw [phaseGradedPolynomial_mul_orderedGradeSeries ν χ q R hq hR,
      polynomial_mul_actualTaylorSeriesAtZero_div _ _ hP]

end

end MeyerGeneralProblem
