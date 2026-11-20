module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyCutoffCovariance

@[expose] public section

/-!
# Measurable covariant fields on square-summable sequences

Finite operator expressions in a measurable covariant field preserve its
matrix measurability and frequency-shift covariance.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

local notation "SeqL2(" ι ")" => lp (fun _ : ι => ℂ) 2

/-- Bounded operators at each threshold with Borel matrix entries and
covariance under frequency shifts. -/
structure LpOperatorField {ι : Type*} [AddGroup ι] [DecidableEq ι]
    (b : ι → ℝ) (V : ℝ → SeqL2(ι) →L[ℂ] SeqL2(ι)) : Prop where
  measurable_entry : ∀ i j : ι,
    Measurable (fun t => V t (lp.single (E := fun _ : ι => ℂ) 2 j (1 : ℂ)) i)
  shift_apply : ∀ (t : ℝ) (j : ι) (f : SeqL2(ι)),
    V (t + b j) (lpFrequencyShift j f) = lpFrequencyShift j (V t f)

namespace LpOperatorField

variable {ι : Type*} [AddGroup ι] [DecidableEq ι]
variable {b : ι → ℝ} {V W : ℝ → SeqL2(ι) →L[ℂ] SeqL2(ι)}

theorem sub (hV : LpOperatorField b V) (hW : LpOperatorField b W) :
    LpOperatorField b (fun t => V t - W t) where
  measurable_entry i j := by
    change Measurable (fun t => V t (lp.single 2 j (1 : ℂ)) i - W t (lp.single 2 j (1 : ℂ)) i)
    exact (hV.measurable_entry i j).sub (hW.measurable_entry i j)
  shift_apply t j f := by
    simp only [sub_apply, hV.shift_apply, hW.shift_apply, map_sub]

theorem mul [Countable ι] (hV : LpOperatorField b V) (hW : LpOperatorField b W) :
    LpOperatorField b (fun t => V t * W t) where
  measurable_entry i j := by
    let e (k : ι) := lp.single (E := fun _ : ι => ℂ) 2 k (1 : ℂ)
    have hEq : (fun t : ℝ => (V t * W t) (e j) i) =
        fun t : ℝ => ∑' k : ι, V t (e k) i * W t (e j) k := by
      funext t
      exact (hasSum_lpOperator_matrix_apply (V t) (W t (e j)) i).tsum_eq.symm
    rw [hEq]
    exact Measurable.tsum fun k => (hV.measurable_entry i k).mul (hW.measurable_entry k j)
  shift_apply t j f := by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      hW.shift_apply, hV.shift_apply]

/-- Shift covariance specializes to the matrix-entry identity needed for
integrated trace symmetry. -/
theorem zero_column_eq_translated_row (hV : LpOperatorField b V) (t : ℝ) (j : ι) :
    V t (lp.single (E := fun _ : ι => ℂ) 2 0 (1 : ℂ)) j =
      V (t - b j) (lp.single (E := fun _ : ι => ℂ) 2 (-j) (1 : ℂ)) 0 := by
  let e (k : ι) := lp.single (E := fun _ : ι => ℂ) 2 k (1 : ℂ)
  have he : lpFrequencyShift j (e (-j)) = e 0 := by
    ext i
    rw [lpFrequencyShift_apply]
    have hi : i - j = -j ↔ i = 0 := by
      rw [← zero_sub (a := j)]
      exact sub_left_inj
    simp only [e, lp.coeFn_single, Pi.single_apply, hi]
  have h := hV.shift_apply (t - b j) j (e (-j))
  rw [sub_add_cancel, he] at h
  have hAt := congrArg (fun f : SeqL2(ι) => f j) h
  simpa only [lpFrequencyShift_apply, sub_self] using hAt

/-- A measurable operator field has a measurable nonnegative diagonal. -/
theorem measurable_zeroDiagonal (hV : LpOperatorField b V) :
    Measurable (fun t => ENNReal.ofReal
      (⟪lp.single (E := fun _ : ι => ℂ) 2 0 (1 : ℂ),
        V t (lp.single (E := fun _ : ι => ℂ) 2 0 (1 : ℂ))⟫_ℂ).re) := by
  simp only [lp.inner_single_left, RCLike.inner_apply', map_one, one_mul]
  exact ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp (hV.measurable_entry 0 0))

end LpOperatorField
end
end MeyerGeneralProblem
