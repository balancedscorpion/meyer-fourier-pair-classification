module

public import MeyerGeneralProblem.Distribution.LpOperatorField
public import MeyerGeneralProblem.Distribution.ProjectionResidual

@[expose] public section

/-!
# Trace comparison for covariant projections

Finite positive residual differences have equal integrated diagonals on the
two sides of the compression. Monotone convergence supplies a kernel vector
when the integrated diagonal of the starting projection is strictly larger.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace Topology

local notation "SeqL2(" ι ")" => lp (fun _ : ι => ℂ) 2

section

variable {ι : Type*} [AddGroup ι] [Countable ι] [DecidableEq ι]
local notation "End" => SeqL2(ι) →L[ℂ] SeqL2(ι)

omit [AddGroup ι] [Countable ι] [DecidableEq ι] in
private theorem starProjection_le_one {P : End} (h : IsStarProjection P) : P ≤ 1 :=
  sub_nonneg.mp (isStarProjection_one_sub_iff.mpr h).nonneg

omit [AddGroup ι] [Countable ι] [DecidableEq ι] in
private theorem starProjection_compression_bounds
    {P Q : End} (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    0 ≤ P * Q * P ∧ P * Q * P ≤ 1 := by
  have hPAdj : star P = P := hP.isSelfAdjoint.star_eq
  have hPP : P * P = P := hP.isIdempotentElem
  have hLo := star_left_conjugate_le_conjugate hQ.nonneg P
  have hHi := star_left_conjugate_le_conjugate (starProjection_le_one hQ) P
  refine ⟨?_, le_trans ?_ (starProjection_le_one hP)⟩
  · simpa only [hPAdj, mul_zero, zero_mul] using hLo
  · simpa only [hPAdj, mul_one, hPP] using hHi

omit [AddGroup ι] [Countable ι] [DecidableEq ι] in
private theorem re_inner_operator_le {X Y : End} (h : X ≤ Y) (x : SeqL2(ι)) :
    (⟪x, X x⟫_ℂ).re ≤ (⟪x, Y x⟫_ℂ).re := by
  have hPos := (ContinuousLinearMap.le_def.mp h).re_inner_nonneg_right x
  change 0 ≤ (⟪x, (Y - X) x⟫_ℂ).re at hPos
  simpa only [sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg] using hPos

omit [Countable ι] in
private theorem lpIntegratedZeroDiagonal_add_of_nonneg
    {b : ι → ℝ} (X Y : ℝ → End) (hX : LpOperatorField b X)
    (hX₀ : ∀ t, 0 ≤ X t) (hY₀ : ∀ t, 0 ≤ Y t) :
    lpIntegratedZeroDiagonal (fun t => X t + Y t) =
      lpIntegratedZeroDiagonal X + lpIntegratedZeroDiagonal Y := by
  let e := lp.single (E := fun _ : ι => ℂ) 2 0 (1 : ℂ)
  unfold lpIntegratedZeroDiagonal
  rw [← lintegral_add_left hX.measurable_zeroDiagonal]
  apply lintegral_congr
  intro t
  have hx := (ContinuousLinearMap.nonneg_iff_isPositive |>.mp (hX₀ t)).re_inner_nonneg_right e
  have hy := (ContinuousLinearMap.nonneg_iff_isPositive |>.mp (hY₀ t)).re_inner_nonneg_right e
  change 0 ≤ (⟪e, X t e⟫_ℂ).re at hx
  change 0 ≤ (⟪e, Y t e⟫_ℂ).re at hy
  simp only [add_apply, inner_add_right, Complex.add_re]
  exact ENNReal.ofReal_add hx hy

/-- If the first projection has greater integrated diagonal, then at some
threshold its range contains a nonzero vector in the second projection's kernel. -/
theorem exists_fixed_vector_in_kernel_of_lt_integrated_diagonal
    (b : ι → ℝ) (P Q : ℝ → End) (hP : LpOperatorField b P) (hQ : LpOperatorField b Q)
    (hPP : ∀ t, IsStarProjection (P t)) (hQQ : ∀ t, IsStarProjection (Q t))
    (hLt : lpIntegratedZeroDiagonal Q < lpIntegratedZeroDiagonal P) :
    ∃ (t : ℝ) (x : SeqL2(ι)), x ≠ 0 ∧ P t x = x ∧ Q t x = 0 := by
  by_contra! hKer
  let A (t : ℝ) := Q t * P t
  let B (t : ℝ) := P t * Q t * P t
  let C (t : ℝ) := Q t * P t * Q t
  let D (n : ℕ) (t : ℝ) := projectionResidual (P t) (B t) n
  let E (n : ℕ) (t : ℝ) := projectionResidual (Q t) (C t) n
  have hA : LpOperatorField b A := hQ.mul hP
  have hB : LpOperatorField b B := (hP.mul hQ).mul hP
  have hC : LpOperatorField b C := hA.mul hQ
  have hD (n : ℕ) : LpOperatorField b (D n) := by
    induction n with
    | zero => exact hP
    | succ n ih => exact ih.sub ((ih.mul hB).mul ih)
  have hE (n : ℕ) : LpOperatorField b (E n) := by
    induction n with
    | zero => exact hQ
    | succ n ih => exact ih.sub ((ih.mul hC).mul ih)
  have hDP (n : ℕ) (t : ℝ) : 0 ≤ D n t ∧ D n t ≤ P t :=
    projectionResidual_nonneg_and_le _ _ (hPP t).nonneg (starProjection_le_one (hPP t))
      (starProjection_compression_bounds (hPP t) (hQQ t)).1
      (starProjection_compression_bounds (hPP t) (hQQ t)).2 n
  have hEQ (n : ℕ) (t : ℝ) : 0 ≤ E n t ∧ E n t ≤ Q t :=
    projectionResidual_nonneg_and_le _ _ (hQQ t).nonneg (starProjection_le_one (hQQ t))
      (starProjection_compression_bounds (hQQ t) (hPP t)).1
      (starProjection_compression_bounds (hQQ t) (hPP t)).2 n
  have hAntiD (t : ℝ) : Antitone (fun n => D n t) :=
    projectionResidual_antitone _ _ (hPP t).nonneg (starProjection_le_one (hPP t))
      (starProjection_compression_bounds (hPP t) (hQQ t)).1
      (starProjection_compression_bounds (hPP t) (hQQ t)).2
  have hAntiE (t : ℝ) : Antitone (fun n => E n t) :=
    projectionResidual_antitone _ _ (hQQ t).nonneg (starProjection_le_one (hQQ t))
      (starProjection_compression_bounds (hQQ t) (hPP t)).1
      (starProjection_compression_bounds (hQQ t) (hPP t)).2
  have hGramB (t : ℝ) : (A t).adjoint * A t = B t := by
    have hp : (P t).adjoint = P t := (hPP t).isSelfAdjoint.star_eq
    have hq : (Q t).adjoint = Q t := (hQQ t).isSelfAdjoint.star_eq
    have hqq : Q t * Q t = Q t := (hQQ t).isIdempotentElem
    have ha : (A t).adjoint = P t * Q t := by
      simp only [A, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp, hp, hq]
    rw [ha]
    change P t * Q t * (Q t * P t) = P t * Q t * P t
    rw [← mul_assoc, mul_assoc (P t) (Q t) (Q t), hqq]
  have hGramC (t : ℝ) : A t * (A t).adjoint = C t := by
    have hp : (P t).adjoint = P t := (hPP t).isSelfAdjoint.star_eq
    have hq : (Q t).adjoint = Q t := (hQQ t).isSelfAdjoint.star_eq
    have hpp : P t * P t = P t := (hPP t).isIdempotentElem
    have ha : (A t).adjoint = P t * Q t := by
      simp only [A, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp, hp, hq]
    rw [ha]
    change Q t * P t * (P t * Q t) = Q t * P t * Q t
    rw [← mul_assoc, mul_assoc (Q t) (P t) (P t), hpp]
  have hInter (n : ℕ) (t : ℝ) : A t * D n t = E n t * A t := by
    apply projectionResidual_intertwine
    · have hp : P t * P t = P t := (hPP t).isIdempotentElem
      have hq : Q t * Q t = Q t := (hQQ t).isIdempotentElem
      change Q t * P t * P t = Q t * (Q t * P t)
      rw [mul_assoc, ← mul_assoc (Q t) (Q t), hp, hq]
    · rw [← hGramB, ← hGramC]
      exact (mul_assoc (A t) (A t).adjoint (A t)).symm
  have hStep (n : ℕ) :
      lpIntegratedZeroDiagonal (fun t => D n t * B t * D n t) =
        lpIntegratedZeroDiagonal (fun t => E n t * C t * E n t) := by
    let V (t : ℝ) := A t * D n t
    have hV : LpOperatorField b V := hA.mul (hD n)
    have hL (t : ℝ) : (V t).adjoint * V t = D n t * B t * D n t := by
      have hd : (D n t).adjoint = D n t :=
        (ContinuousLinearMap.nonneg_iff_isPositive |>.mp (hDP n t).1).isSelfAdjoint.star_eq
      have ha : (V t).adjoint = D n t * (A t).adjoint := by
        simp only [V, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp, hd]
      rw [ha, ← hGramB]
      simp only [V, mul_assoc]
    have hR (t : ℝ) : V t * (V t).adjoint = E n t * C t * E n t := by
      have he : (E n t).adjoint = E n t :=
        (ContinuousLinearMap.nonneg_iff_isPositive |>.mp (hEQ n t).1).isSelfAdjoint.star_eq
      have ha : (E n t * A t).adjoint = (A t).adjoint * E n t := by
        simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp, he]
      change (A t * D n t) * (A t * D n t).adjoint = _
      rw [hInter, ha, ← hGramC]
      simp only [mul_assoc]
    have hTrace := lpIntegratedZeroDiagonal_adjoint_mul_eq_mul_adjoint b V
      hV.measurable_entry hV.zero_column_eq_translated_row
    simp_rw [hL, hR] at hTrace
    exact hTrace
  let F (n : ℕ) (t : ℝ) := P t - D n t
  let G (n : ℕ) (t : ℝ) := Q t - E n t
  have hF (n : ℕ) : LpOperatorField b (F n) := hP.sub (hD n)
  have hG (n : ℕ) : LpOperatorField b (G n) := hQ.sub (hE n)
  have hEq (n : ℕ) : lpIntegratedZeroDiagonal (F n) = lpIntegratedZeroDiagonal (G n) := by
    induction n with
    | zero =>
      have hFzero : F 0 = fun _ => 0 := funext fun t => sub_self (P t)
      have hGzero : G 0 = fun _ => 0 := funext fun t => sub_self (Q t)
      rw [hFzero, hGzero]
    | succ n ih =>
      have hFn : F (n + 1) = fun t => F n t + D n t * B t * D n t := by
        funext t
        change P t - (D n t - D n t * B t * D n t) = _
        unfold F
        abel
      have hGn : G (n + 1) = fun t => G n t + E n t * C t * E n t := by
        funext t
        change Q t - (E n t - E n t * C t * E n t) = _
        unfold G
        abel
      have hDL (t : ℝ) : 0 ≤ D n t * B t * D n t := by
        have h := sub_nonneg.mpr (hAntiD t (Nat.le_succ n))
        change 0 ≤ D n t - (D n t - D n t * B t * D n t) at h
        simpa only [sub_sub_cancel] using h
      have hEL (t : ℝ) : 0 ≤ E n t * C t * E n t := by
        have h := sub_nonneg.mpr (hAntiE t (Nat.le_succ n))
        change 0 ≤ E n t - (E n t - E n t * C t * E n t) at h
        simpa only [sub_sub_cancel] using h
      rw [hFn, hGn, lpIntegratedZeroDiagonal_add_of_nonneg _ _ (hF n)
        (fun t => sub_nonneg.mpr (hDP n t).2) hDL,
        lpIntegratedZeroDiagonal_add_of_nonneg _ _ (hG n)
          (fun t => sub_nonneg.mpr (hEQ n t).2) hEL, ih, hStep n]
  let e := lp.single (E := fun _ : ι => ℂ) 2 0 (1 : ℂ)
  let a (n : ℕ) (t : ℝ) := ENNReal.ofReal (⟪e, F n t e⟫_ℂ).re
  have hMono (t : ℝ) : Monotone (fun n => a n t) := by
    intro m n hmn
    exact ENNReal.ofReal_le_ofReal (re_inner_operator_le (sub_le_sub_left (hAntiD t hmn) _) e)
  have hLim (t : ℝ) :
      Tendsto (fun n => a n t) atTop (𝓝 (ENNReal.ofReal (⟪e, P t e⟫_ℂ).re)) := by
    have ht : Tendsto (fun n => D n t e) atTop (𝓝 0) := by
      have hle : (A t).adjoint * A t ≤ 1 := by
        rw [hGramB]
        exact (starProjection_compression_bounds (hPP t) (hQQ t)).2
      have h := tendsto_projectionResidual_apply_zero_of_no_kernel (P t) (A t)
        (hPP t).nonneg (starProjection_le_one (hPP t)) (hPP t).isIdempotentElem hle
        (fun x hxP hxA => by
          have hxQ : Q t x = 0 := by
            change Q t (P t x) = 0 at hxA
            rwa [hxP] at hxA
          by_contra hx₀
          exact hKer t x hx₀ hxP hxQ) e
      simpa only [hGramB, D] using h
    have hVec : Tendsto (fun n => F n t e) atTop (𝓝 (P t e)) := by
      simpa only [F, sub_apply, sub_zero] using tendsto_const_nhds.sub ht
    have hCont : Continuous (fun y : SeqL2(ι) => ENNReal.ofReal (⟪e, y⟫_ℂ).re) :=
      ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.inner continuous_id))
    exact (hCont.tendsto _).comp hVec
  have hConv : Tendsto (fun n => lpIntegratedZeroDiagonal (F n)) atTop
      (𝓝 (lpIntegratedZeroDiagonal P)) :=
    lintegral_tendsto_of_tendsto_of_monotone (fun n => (hF n).measurable_zeroDiagonal.aemeasurable)
      (Eventually.of_forall hMono) (Eventually.of_forall hLim)
  have hBound (n : ℕ) : lpIntegratedZeroDiagonal (F n) ≤ lpIntegratedZeroDiagonal Q := by
    rw [hEq n]
    apply lintegral_mono
    intro t
    exact ENNReal.ofReal_le_ofReal (re_inner_operator_le (sub_le_self _ (hEQ n t).1) e)
  exact hLt.not_ge (le_of_tendsto' hConv hBound)

end
end
end MeyerGeneralProblem
