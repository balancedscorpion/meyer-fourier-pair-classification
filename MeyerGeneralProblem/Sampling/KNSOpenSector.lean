module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Cartesian sectors and moving closed disks

The strict Cartesian sector condition excludes the origin without using the
totalized complex argument. Coordinate estimates place full closed disks with
positive real centers inside the right half-plane and, under an explicit margin,
inside the sector. The same estimates give the norm lower bound needed to keep
these disks outside a fixed central region.
-/

namespace MeyerGeneralProblem

/-- The strict Cartesian sector of half-angle `α` about the positive real axis.
For `0 < α < π / 2` its defining inequality excludes the origin and both rays. -/
def knsOpenSector (α : ℝ) : Set ℂ :=
  {w | 0 < Real.sin α * w.re - Real.cos α * |w.im|}

/-- Coordinate consequences of membership in a closed disk with real center. -/
private theorem realCenter_closedBall_coordinate_bounds {x s : ℝ} {w : ℂ}
    (hw : w ∈ Metric.closedBall (x : ℂ) (s * x)) :
    (1 - s) * x ≤ w.re ∧ |w.im| ≤ s * x := by
  have hnorm : ‖w - (x : ℂ)‖ ≤ s * x := mem_closedBall_iff_norm.mp hw
  have hre := (abs_le.mp ((Complex.abs_re_le_norm (w - (x : ℂ))).trans hnorm)).1
  have him := (Complex.abs_im_le_norm (w - (x : ℂ))).trans hnorm
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  refine ⟨by linarith, ?_⟩
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using him

/-- A closed disk of relative radius strictly below one and positive real
center lies in the open right half-plane, including every boundary point. -/
theorem closedBall_realCenter_subset_rightHalfPlane {x s : ℝ}
    (hx0 : 0 < x) (hs1 : s < 1) :
    Metric.closedBall (x : ℂ) (s * x) ⊆ {w : ℂ | 0 < w.re} := by
  intro w hw
  exact (mul_pos (sub_pos.mpr hs1) hx0).trans_le
    (realCenter_closedBall_coordinate_bounds hw).1

/-- Every point of a real-centered closed disk has norm at least the center
minus its radius. This form needs no sign assumptions on the real parameters. -/
theorem realCenter_closedBall_norm_lower_bound {x s : ℝ} {w : ℂ}
    (hw : w ∈ Metric.closedBall (x : ℂ) (s * x)) :
    (1 - s) * x ≤ ‖w‖ :=
  (realCenter_closedBall_coordinate_bounds hw).1.trans (Complex.re_le_norm w)

/-- An explicit strict Cartesian margin puts the full moving closed disk
inside the open sector. No argument convention or tangent-disk assertion is
used; the relative-radius inequality is the actual quantitative premise. -/
theorem closedBall_realCenter_subset_knsOpenSector {α x s : ℝ}
    (hα0 : 0 < α) (hαhalf : α < Real.pi / 2) (hx0 : 0 < x)
    (hsSector : s * (Real.sin α + Real.cos α) < Real.sin α) :
    Metric.closedBall (x : ℂ) (s * x) ⊆ knsOpenSector α := by
  intro w hw
  obtain ⟨hre, him⟩ := realCenter_closedBall_coordinate_bounds hw
  have hsin : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαhalf⟩
  change 0 < Real.sin α * w.re - Real.cos α * |w.im|
  calc
    0 < (Real.sin α - s * (Real.sin α + Real.cos α)) * x :=
      mul_pos (sub_pos.mpr hsSector) hx0
    _ = Real.sin α * ((1 - s) * x) - Real.cos α * (s * x) := by ring
    _ ≤ Real.sin α * w.re - Real.cos α * |w.im| :=
      sub_le_sub (mul_le_mul_of_nonneg_left hre hsin.le)
        (mul_le_mul_of_nonneg_left him hcos.le)

end MeyerGeneralProblem
