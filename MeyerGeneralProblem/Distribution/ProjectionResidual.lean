module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

/-!
# Positive residuals of a compressed projection

The residual recurrence removes one Gram operator at each step. This
gives strong convergence on every vector when the compression map has
trivial kernel on the starting projection.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter
open scoped InnerProductSpace Topology

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "End" => H →L[ℂ] H

/-- Residuals for the compression of an orthogonal projection. The removed
part at each step is the Gram operator of the current residual. -/
def projectionResidual (P B : End) : ℕ → End
  | 0 => P
  | n + 1 => projectionResidual P B n - projectionResidual P B n * B * projectionResidual P B n

theorem projectionResidual_nonneg_and_le
    (P B : End) (hP₀ : 0 ≤ P) (hP₁ : P ≤ 1) (hB₀ : 0 ≤ B) (hB₁ : B ≤ 1)
    (n : ℕ) :
    0 ≤ projectionResidual P B n ∧ projectionResidual P B n ≤ P := by
  induction n with
  | zero => exact ⟨hP₀, le_rfl⟩
  | succ n ih =>
    let D := projectionResidual P B n
    have hD₀ : 0 ≤ D := ih.1
    have hD₁ : D ≤ 1 := ih.2.trans hP₁
    have hAdj : star D = D :=
      (ContinuousLinearMap.nonneg_iff_isPositive |>.mp hD₀).isSelfAdjoint.star_eq
    have hUpper : D * B * D ≤ D * D := by
      have h := star_left_conjugate_le_conjugate hB₁ D
      simpa only [hAdj, mul_one] using h
    have hLower : 0 ≤ D * B * D := by
      have h := star_left_conjugate_le_conjugate hB₀ D
      simpa only [hAdj, mul_zero, zero_mul] using h
    have hSquare : D * D ≤ D := by
      have hComm : Commute D (1 - D) := (Commute.one_right D).sub_right (Commute.refl D)
      have h := Commute.mul_nonneg hD₀ (sub_nonneg.mpr hD₁) hComm
      simpa only [mul_sub, mul_one, sub_nonneg] using h
    change 0 ≤ D - D * B * D ∧ D - D * B * D ≤ P
    exact ⟨sub_nonneg.mpr (hUpper.trans hSquare), (sub_le_self D hLower).trans ih.2⟩

theorem projectionResidual_antitone
    (P B : End) (hP₀ : 0 ≤ P) (hP₁ : P ≤ 1) (hB₀ : 0 ≤ B) (hB₁ : B ≤ 1) :
    Antitone (projectionResidual P B) := by
  apply antitone_nat_of_succ_le
  intro n
  let D := projectionResidual P B n
  have hD₀ : 0 ≤ D := (projectionResidual_nonneg_and_le P B hP₀ hP₁ hB₀ hB₁ n).1
  have hAdj : star D = D :=
    (ContinuousLinearMap.nonneg_iff_isPositive |>.mp hD₀).isSelfAdjoint.star_eq
  have h := star_left_conjugate_le_conjugate hB₀ D
  have hLower : 0 ≤ D * B * D := by
    simpa only [hAdj, mul_zero, zero_mul] using h
  exact sub_le_self D hLower

omit [CompleteSpace H] in
theorem projectionResidual_mul_eq_left_of_mul_eq_left
    (P B : End) (hP : P * P = P) (n : ℕ) :
    P * projectionResidual P B n = projectionResidual P B n := by
  induction n with
  | zero => exact hP
  | succ n ih =>
    let D := projectionResidual P B n
    change P * (D - D * B * D) = D - D * B * D
    rw [mul_sub, ← mul_assoc, ← mul_assoc, ih]

omit [CompleteSpace H] in
theorem projectionResidual_intertwine
    (P Q A B C : End) (hAP : A * P = Q * A) (hABC : A * B = C * A) (n : ℕ) :
    A * projectionResidual P B n = projectionResidual Q C n * A := by
  induction n with
  | zero => exact hAP
  | succ n ih =>
    let D := projectionResidual P B n
    let E := projectionResidual Q C n
    change A * (D - D * B * D) = (E - E * C * E) * A
    rw [mul_sub, sub_mul, ← mul_assoc, ← mul_assoc, ih]
    congr 1
    calc
      E * A * B * D = E * (A * B) * D := by rw [mul_assoc E A B]
      _ = E * (C * A) * D := by rw [hABC]
      _ = E * C * (A * D) := by simp only [mul_assoc]
      _ = E * C * E * A := by rw [ih, mul_assoc (E * C) E A]

omit [CompleteSpace H] in
private theorem re_inner_operator_mono {X Y : End} (h : X ≤ Y) (x : H) :
    (⟪x, X x⟫_ℂ).re ≤ (⟪x, Y x⟫_ℂ).re := by
  have hPos := (ContinuousLinearMap.le_def.mp h).re_inner_nonneg_right x
  change 0 ≤ (⟪x, (Y - X) x⟫_ℂ).re at hPos
  simpa only [sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg] using hPos

private theorem norm_sq_apply_le_re_inner_of_nonneg_le_one
    (X : End) (hX₀ : 0 ≤ X) (hX₁ : X ≤ 1) (x : H) :
    ‖X x‖ ^ 2 ≤ (⟪x, X x⟫_ℂ).re := by
  have hComm : Commute X (1 - X) := (Commute.one_right X).sub_right (Commute.refl X)
  have hs := Commute.mul_nonneg hX₀ (sub_nonneg.mpr hX₁) hComm
  have hSq : X * X ≤ X := by
    simpa only [mul_sub, mul_one, sub_nonneg] using hs
  have hAdj : X.adjoint = X :=
    (ContinuousLinearMap.nonneg_iff_isPositive |>.mp hX₀).isSelfAdjoint.star_eq
  rw [X.apply_norm_sq_eq_inner_adjoint_right, hAdj]
  exact re_inner_operator_mono hSq x

/-- The residuals converge strongly to zero if the only vector fixed
by the starting projection and killed by the compression map is zero. -/
theorem tendsto_projectionResidual_apply_zero_of_no_kernel
    (P A : End) (hP₀ : 0 ≤ P) (hP₁ : P ≤ 1) (hP : P * P = P)
    (hA : A.adjoint * A ≤ 1) (hKer : ∀ y : H, P y = y → A y = 0 → y = 0) (x : H) :
    Tendsto (fun n => projectionResidual P (A.adjoint * A) n x) atTop (𝓝 0) := by
  let B := A.adjoint * A
  let D := projectionResidual P B
  let a (n : ℕ) := (⟪x, D n x⟫_ℂ).re
  have hB₀ : 0 ≤ B := star_mul_self_nonneg A
  have hD (n : ℕ) : 0 ≤ D n ∧ D n ≤ P :=
    projectionResidual_nonneg_and_le P B hP₀ hP₁ hB₀ hA n
  have hAnti := projectionResidual_antitone P B hP₀ hP₁ hB₀ hA
  have haAnti : Antitone a := fun _ _ hmn => re_inner_operator_mono (hAnti hmn) x
  have ha₀ (n : ℕ) : 0 ≤ a n :=
    (ContinuousLinearMap.nonneg_iff_isPositive |>.mp (hD n).1).re_inner_nonneg_right x
  have haLim : Tendsto a atTop (𝓝 (⨅ n, a n)) :=
    tendsto_atTop_ciInf haAnti ⟨0, fun _ ⟨n, hn⟩ => hn ▸ ha₀ n⟩
  have hDist (m n : ℕ) (hmn : m ≤ n) :
      dist (D m x) (D n x) ^ 2 ≤ dist (a m) (a n) := by
    have hl : 0 ≤ D m - D n := sub_nonneg.mpr (hAnti hmn)
    have hu : D m - D n ≤ 1 :=
      (sub_le_self (D m) (hD n).1).trans ((hD m).2.trans hP₁)
    have hn := norm_sq_apply_le_re_inner_of_nonneg_le_one (D m - D n) hl hu x
    rw [dist_eq_norm, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (haAnti hmn))]
    simpa only [sub_apply, inner_sub_right, Complex.sub_re] using hn
  have hc : CauchySeq (fun n => D n x) := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 haLim.cauchySeq (ε ^ 2) (sq_pos_of_pos hε)
    have hTail (m n : ℕ) (hm : N ≤ m) (hn : N ≤ n) (hmn : m ≤ n) :
        dist (D m x) (D n x) < ε := by
      have hd := (hDist m n hmn).trans_lt (hN m hm n hn)
      exact lt_of_pow_lt_pow_left₀ 2 hε.le hd
    refine ⟨N, fun m hm n hn => ?_⟩
    rcases le_total m n with hmn | hnm
    · exact hTail m n hm hn hmn
    · rw [dist_comm]
      exact hTail n m hn hm hnm
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  have hyP : P y = y := by
    have h := (P.continuous.tendsto y).comp hy
    apply tendsto_nhds_unique h
    convert hy using 1
    funext n
    have he := congrArg (fun f : End => f x) (projectionResidual_mul_eq_left_of_mul_eq_left P B hP n)
    exact he
  have hDrop (n : ℕ) : ‖A (D n x)‖ ^ 2 = a n - a (n + 1) := by
    have hdAdj : (D n).adjoint = D n :=
      (ContinuousLinearMap.nonneg_iff_isPositive |>.mp (hD n).1).isSelfAdjoint.star_eq
    have hGram : (A * D n).adjoint * (A * D n) = D n * B * D n := by
      simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
        hdAdj, B, ContinuousLinearMap.comp_assoc]
    have hg := (A * D n).apply_norm_sq_eq_inner_adjoint_right x
    change ‖A (D n x)‖ ^ 2 = (⟪x, ((A * D n).adjoint * (A * D n)) x⟫_ℂ).re at hg
    rw [hGram] at hg
    rw [hg]
    change _ = (⟪x, D n x⟫_ℂ).re - (⟪x, (D n - D n * B * D n) x⟫_ℂ).re
    simp only [sub_apply, inner_sub_right, Complex.sub_re, sub_sub_cancel]
  have hZero : Tendsto (fun n => ‖A (D n x)‖ ^ 2) atTop (𝓝 0) := by
    have hNext : Tendsto (fun n => a (n + 1)) atTop (𝓝 (⨅ n, a n)) :=
      haLim.comp (tendsto_add_atTop_nat 1)
    simpa only [hDrop, sub_self] using haLim.sub hNext
  have hLimit : Tendsto (fun n => ‖A (D n x)‖ ^ 2) atTop (𝓝 (‖A y‖ ^ 2)) :=
    (((A.continuous.tendsto y).comp hy).norm).pow 2
  have hyA : A y = 0 := by
    have hz := tendsto_nhds_unique hLimit hZero
    exact norm_eq_zero.mp (mul_self_eq_zero.mp (by simpa only [pow_two] using hz))
  rwa [hKer y hyP hyA] at hy

end
end
end MeyerGeneralProblem
