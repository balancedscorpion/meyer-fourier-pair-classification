module

public import MeyerGeneralProblem.Sampling.KNSOpenSector
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

/-!
# Logarithmic geometry of the strict Cartesian KNS sector

The Cartesian inequality first proves positive real part and excludes zero.
Only then is the principal argument compared using tangent on its strictly
monotone interval. The logarithmic strip bounds therefore do not rely on
the totalized value of the argument at zero. Closed symmetric horizontal
strips of half-width below pi/2 exponentiate into the open right half-plane.
No sector-growth principle or converse sector characterization is asserted.
-/

namespace MeyerGeneralProblem

/-- The strict Cartesian sector lies in the open right half-plane when its
half-angle is strictly between zero and pi/2. -/
theorem re_pos_of_mem_knsOpenSector {α : ℝ} {w : ℂ}
    (hα0 : 0 < α) (hαhalf : α < Real.pi / 2) (hw : w ∈ knsOpenSector α) :
    0 < w.re := by
  have hsin : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαhalf⟩
  change 0 < Real.sin α * w.re - Real.cos α * |w.im| at hw
  have hp : 0 < Real.sin α * w.re := by
    linarith [mul_nonneg hcos.le (abs_nonneg w.im)]
  exact (mul_pos_iff_of_pos_left hsin).mp hp

/-- A point of the strict Cartesian sector is nonzero; the argument at zero
is never used to justify membership in a logarithmic strip. -/
theorem ne_zero_of_mem_knsOpenSector {α : ℝ} {w : ℂ}
    (hα0 : 0 < α) (hαhalf : α < Real.pi / 2) (hw : w ∈ knsOpenSector α) :
    w ≠ 0 := by
  have hre := re_pos_of_mem_knsOpenSector hα0 hαhalf hw
  intro hw0
  exact (ne_of_gt hre) (congrArg Complex.re hw0)

/-- The principal argument of an actual Cartesian-sector point lies between
the two strict boundary angles. Positive real part fixes the tangent branch. -/
theorem arg_mem_Ioo_of_mem_knsOpenSector {α : ℝ} {w : ℂ}
    (hα0 : 0 < α) (hαhalf : α < Real.pi / 2) (hw : w ∈ knsOpenSector α) :
    w.arg ∈ Set.Ioo (-α) α := by
  have hre := re_pos_of_mem_knsOpenSector hα0 hαhalf hw
  have hcos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαhalf⟩
  have harg : w.arg ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))
  have hα : α ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], hαhalf⟩
  have hnα : -α ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  change 0 < Real.sin α * w.re - Real.cos α * |w.im| at hw
  have hu : w.im / w.re < Real.tan α := by
    rw [Real.tan_eq_sin_div_cos, div_lt_div_iff₀ hre hcos]
    nlinarith [le_abs_self w.im]
  have hl : Real.tan (-α) < w.im / w.re := by
    rw [Real.tan_neg, Real.tan_eq_sin_div_cos, ← neg_div,
      div_lt_div_iff₀ hcos hre]
    nlinarith [neg_le_abs w.im]
  rw [← Complex.tan_arg] at hu hl
  exact ⟨(Real.strictMonoOn_tan.lt_iff_lt hnα harg).mp hl,
    (Real.strictMonoOn_tan.lt_iff_lt harg hα).mp hu⟩

/-- The imaginary part of the principal logarithm of an actual sector point
lies in the strict symmetric strip. Sector membership separately excludes zero. -/
theorem log_im_mem_Ioo_of_mem_knsOpenSector {α : ℝ} {w : ℂ}
    (hα0 : 0 < α) (hαhalf : α < Real.pi / 2) (hw : w ∈ knsOpenSector α) :
    (Complex.log w).im ∈ Set.Ioo (-α) α := by
  simpa only [Complex.log_im] using arg_mem_Ioo_of_mem_knsOpenSector hα0 hαhalf hw

/-- Every point of a closed symmetric horizontal strip narrower than pi
exponentiates into the open right half-plane, including both boundary lines.
The strip premise itself suffices without a separate positivity assumption on
its half-width. The exponential image never includes zero. -/
theorem exp_re_pos_of_im_mem_Icc_symmetric {α : ℝ} {ζ : ℂ}
    (hαhalf : α < Real.pi / 2) (hz : ζ.im ∈ Set.Icc (-α) α) :
    0 < (Complex.exp ζ).re := by
  rw [Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [hz.1, hz.2]

end MeyerGeneralProblem
