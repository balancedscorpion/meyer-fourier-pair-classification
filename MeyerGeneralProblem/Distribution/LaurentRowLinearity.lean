module

public import MeyerGeneralProblem.Distribution.RealRootedRationalRows
public import Mathlib.Algebra.MonoidAlgebra.Module

@[expose] public section

/-! The maps giving the literal rational classification rows are linear in the numerator. -/

namespace MeyerGeneralProblem

noncomputable section

open Set

variable {G : Type*} [AddCommGroup G]

theorem FrequencyLocallyFinite.smul_complex {L : G →+ ℝ} {u : G → ℂ}
    (hu : FrequencyLocallyFinite L u) (c : ℂ) : FrequencyLocallyFinite L (c • u) := by
  intro a b
  apply (hu a b).subset
  rintro n ⟨hn, hI⟩
  exact ⟨fun h => hn (by simp [h]), hI⟩

theorem FrequencyLocallyFinite.add_complex {L : G →+ ℝ} {u v : G → ℂ}
    (hu : FrequencyLocallyFinite L u) (hv : FrequencyLocallyFinite L v) :
    FrequencyLocallyFinite L (u + v) := by
  intro a b
  apply ((hu a b).union (hv a b)).subset
  rintro n ⟨hn, hI⟩
  by_cases he : u n = 0
  · right
    exact ⟨fun h => hn (by simp [he, h]), hI⟩
  · exact Or.inl ⟨he, hI⟩

def cutArrayNumeratorLinearMap (L : G →+ ℝ) (p : AddMonoidAlgebra ℂ G) (s : ℝ) :
    (G → ℂ) →ₗ[ℂ] (G → ℂ) := by
  let M : (G → ℂ) →ₗ[ℂ] (G → ℂ) := {
    toFun := arrayPositiveCut L s
    map_add' := fun u v => funext fun n => by
      by_cases h : s ≤ L n <;> simp [arrayPositiveCut, h]
    map_smul' := fun c u => funext fun n => by
      by_cases h : s ≤ L n <;> simp [arrayPositiveCut, h] }
  exact (originalLaurentArrayAction p).comp M

theorem cutArrayNumeratorLinearMap_apply (L : G →+ ℝ)
    (p : AddMonoidAlgebra ℂ G) (s : ℝ) (u : G → ℂ) :
    cutArrayNumeratorLinearMap L p s u = cutArrayNumerator L p.coeff s u := by
  funext n
  exact originalLaurentArrayAction_apply p (arrayPositiveCut L s u) n

/-- The full signed Laurent array is linear in its numerator on the
half-open slab, by uniqueness of the original formal recurrence. -/
def orderedLaurentJumpLinearMap
    (L : G →+ ℝ) (p : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (s : ℝ) (W : Set G) (hW : ∀ n ∈ W, L lo + s ≤ L n ∧ L n < L hi + s) :
    AddMonoidAlgebra.supported ℂ ℂ W →ₗ[ℂ] (G → ℂ) := by
  let V := AddMonoidAlgebra.supported ℂ ℂ W
  let d (R : V) := orderedLaurentJump p R.val lo hi
  let M := cutArrayNumeratorLinearMap L p s
  have hc (R : V) : FrequencyLocallyFinite L (d R) ∧
      originalLaurentArrayAction p (d R) = 0 ∧
      M (d R) = (fun n => R.val.coeff n) := by
    obtain ⟨hl, hr, _, _, hnum⟩ :=
      orderedLaurentJump_exact_cuts L p R.val lo hi hlo hhi hmin hmax s
        (fun n hn => hW n (R.property hn))
    refine ⟨hl, ?_, (cutArrayNumeratorLinearMap_apply L p s _).trans hnum⟩
    funext n
    exact (originalLaurentArrayAction_apply p (d R) n).trans (hr n)
  have hu (R : V) (u : G → ℂ) (hl : FrequencyLocallyFinite L u)
      (hconv : originalLaurentArrayAction p u = 0)
      (hnum : M u = (fun n => R.val.coeff n)) : u = d R := by
    apply originalArray_eq_orderedLaurentJump L p R.val lo hi hlo hhi hmin hmax s u hl
    · intro n
      simpa only [originalLaurentArrayAction_apply, Pi.zero_apply] using congrFun hconv n
    · exact (cutArrayNumeratorLinearMap_apply L p s u).symm.trans hnum
  refine { toFun := d, map_add' := ?_, map_smul' := ?_ }
  · intro R S
    obtain ⟨hlR, hcR, hmR⟩ := hc R
    obtain ⟨hlS, hcS, hmS⟩ := hc S
    symm
    apply hu (R + S) (d R + d S) (hlR.add_complex hlS)
    · rw [map_add, hcR, hcS, zero_add]
    · rw [map_add, hmR, hmS]
      rfl
  · intro c R
    obtain ⟨hlR, hcR, hmR⟩ := hc R
    symm
    apply hu (c • R) (c • d R) (hlR.smul_complex c)
    · rw [map_smul, hcR, smul_zero]
    · rw [map_smul, hmR]
      rfl

@[simp]
theorem orderedLaurentJumpLinearMap_apply
    (L : G →+ ℝ) (p : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (s : ℝ) (W : Set G) (hW : ∀ n ∈ W, L lo + s ≤ L n ∧ L n < L hi + s)
    (R : AddMonoidAlgebra.supported ℂ ℂ W) :
    orderedLaurentJumpLinearMap L p lo hi hlo hhi hmin hmax s W hW R =
      orderedLaurentJump p R.val lo hi := rfl

def exponentialNumeratorLinearMap (L : G →+ ℝ) :
    AddMonoidAlgebra ℂ G →ₗ[ℂ] (ℂ → ℂ) :=
  (Finsupp.linearCombination ℂ (fun n z =>
    Complex.exp (2 * Real.pi * Complex.I * (L n : ℂ) * z))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem exponentialNumeratorLinearMap_apply (L : G →+ ℝ)
    (R : AddMonoidAlgebra ℂ G) :
    exponentialNumeratorLinearMap L R = complexExponentialSum L R.coeff := by
  funext z
  simp only [exponentialNumeratorLinearMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    AddMonoidAlgebra.coeffLinearEquiv_apply, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, complexExponentialSum]

/-- A physical numerator derivative row, as a genuine linear functional. -/
def exponentialNumeratorDerivativeRow (L : G →+ ℝ) (a : ℝ) (j : ℕ) :
    AddMonoidAlgebra ℂ G →ₗ[ℂ] ℂ where
  toFun R := iteratedDeriv j (complexExponentialSum L R.coeff) (a : ℂ)
  map_add' R S := by
    simp only [← exponentialNumeratorLinearMap_apply, map_add]
    rw [iteratedDeriv_add]
    · rw [exponentialNumeratorLinearMap_apply]
      exact (complexExponentialSum_entire L R.coeff _ (mem_univ _)).contDiffAt
    · rw [exponentialNumeratorLinearMap_apply]
      exact (complexExponentialSum_entire L S.coeff _ (mem_univ _)).contDiffAt
  map_smul' c R := by
    simp only [← exponentialNumeratorLinearMap_apply, map_smul, RingHom.id_apply]
    exact iteratedDeriv_const_smul_field c (exponentialNumeratorLinearMap L R)

end

end MeyerGeneralProblem
