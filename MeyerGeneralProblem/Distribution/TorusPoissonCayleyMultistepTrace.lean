module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyCutoffCovariance

@[expose] public section

/-!
# Multistep integrated cutoff trace

Conjugation preserves the integrated diagonal of the cutoff defect.
The nested-cutoff recursion then gives its exact trace at every power.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory UnitAddTorus
open scoped ENNReal InnerProductSpace Topology

local notation "SeqL2(" ι ")" => lp (fun _ : ι => ℂ) 2

section

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Set.Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

/-- Conjugating a multistep defect by the Cayley unitary preserves its
integrated trace. -/
theorem lpIntegratedZeroDiagonal_conj_torusPoissonCayleyCutoffDefect (q : ℕ) :
    let U : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) :=
      (torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance : _ ≃ₗᵢ[ℂ] _)
    let L (t : ℝ) := torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance t q
    lpIntegratedZeroDiagonal (fun t => U * L t * U.adjoint) = lpIntegratedZeroDiagonal L := by
  classical
  intro C L
  let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
  let b := torusDirectionalFrequency β
  let V (t : ℝ) := L t * C.adjoint
  let e (i : d → ℤ) := lp.single (E := fun _ : d → ℤ => ℂ) 2 i (1 : ℂ)
  have hVMeas (i j : d → ℤ) : Measurable (fun t => V t (e j) i) :=
    measurable_torusPoissonCayleyCutoffDefect_apply β S T hT hCont hCount hAdvance q (C.adjoint (e j)) i
  have hAdjShift (j : d → ℤ) (f : SeqL2(d → ℤ)) :
      C.adjoint (lpFrequencyShift j f) = lpFrequencyShift j (C.adjoint f) := by
    change ((U : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ)).adjoint) (lpFrequencyShift j f) = _
    rw [U.adjoint_eq_symm]
    change U.symm (lpFrequencyShift j f) = lpFrequencyShift j (U.symm f)
    apply U.injective
    rw [U.apply_symm_apply, torusPoissonCayleyConvolution_lpFrequencyShift,
      U.apply_symm_apply]
  have hVCov (t : ℝ) (j : d → ℤ) : V t (e 0) j = V (t - b j) (e (-j)) 0 := by
    have he : lpFrequencyShift j (e (-j)) = e 0 := by
      ext i
      rw [lpFrequencyShift_apply]
      by_cases hi : i = 0
      · subst i
        simp [e]
      · have hj : i - j ≠ -j := by
          intro h
          exact hi (by simpa [sub_add_cancel] using congrArg (· + j) h)
        simp only [e, lp.coeFn_single, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hi]
    have h := torusPoissonCayleyCutoffDefect_lpFrequencyShift β S T hT hCont hCount hAdvance
      q j (t - b j) (C.adjoint (e (-j)))
    change L (t - b j + b j) (lpFrequencyShift j (C.adjoint (e (-j)))) =
      lpFrequencyShift j (L (t - b j) (C.adjoint (e (-j)))) at h
    rw [sub_add_cancel, ← hAdjShift, he] at h
    have hp := congrArg (fun f : SeqL2(d → ℤ) => f j) h
    simpa only [V, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      lpFrequencyShift_apply, sub_self] using hp
  have hCC : C.adjoint * C = 1 := by
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using
      C.isometry_iff_adjoint_comp_self.mp U.isometry
  have hADJ (t : ℝ) : (V t).adjoint = C * L t := by
    have hL := (torusPoissonCayleyCutoffDefect_is_projection β S T hT hCont hCount hAdvance t q).1
    change (L t).adjoint = L t at hL
    simp only [V, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, hL]
  have hProj (t : ℝ) : L t * L t = L t :=
    (torusPoissonCayleyCutoffDefect_is_projection β S T hT hCont hCount hAdvance t q).2
  have hLeft (t : ℝ) : (V t).adjoint * V t = C * L t * C.adjoint := by
    rw [hADJ]
    change C * L t * (L t * C.adjoint) = _
    rw [← mul_assoc (C * L t), mul_assoc C (L t), hProj]
  have hRight (t : ℝ) : V t * (V t).adjoint = L t := by
    rw [hADJ]
    change L t * C.adjoint * (C * L t) = _
    rw [← mul_assoc, mul_assoc (L t) C.adjoint, hCC, mul_one, hProj]
  have h := lpIntegratedZeroDiagonal_adjoint_mul_eq_mul_adjoint b V hVMeas hVCov
  simp_rw [hLeft, hRight] at h
  exact h


include hAdvance in
/-- The integrated diagonal of the q-step Cayley defect is q times the
finite directional energy. -/
theorem lpIntegratedZeroDiagonal_torusPoissonCayleyCutoffDefect_eq_mul_energy
    (E : ℝ)
    (hE : HasSum (fun n : d → ℤ => torusDirectionalFrequency β n *
      ‖mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) n‖ ^ 2) E)
    (q : ℕ) :
    lpIntegratedZeroDiagonal (fun t => torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance t q) =
      (q : ℝ≥0∞) * ENNReal.ofReal E := by
  classical
  let U := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
  let C : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) := U
  let L (q : ℕ) (t : ℝ) := torusPoissonCayleyCutoffDefect β S T hT hCont hCount hAdvance t q
  let e := lp.single (E := fun _ : d → ℤ => ℂ) 2 0 (1 : ℂ)
  have hOne : lpIntegratedZeroDiagonal (L 1) = ENNReal.ofReal E :=
    lintegral_torusPoissonCayleyCutoffDefect_one_eq_energy β S T hT hCont hCount hAdvance E hE
  have hZero (t : ℝ) : L 0 t = 0 := by
    unfold L torusPoissonCayleyCutoffDefect
    rw [pow_zero]
    change _ - 1 * _ * (1 : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ)).adjoint = 0
    rw [ContinuousLinearMap.adjoint_one, one_mul, mul_one, sub_self]
  have hRec (q : ℕ) (t : ℝ) : L (q + 1) t = L 1 t + C * L q t * C.adjoint := by
    let P := lpUpperFrequencyProjection (torusDirectionalFrequency β) t
    let V : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) := (U ^ q : _ ≃ₗᵢ[ℂ] _)
    let W : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) := (U ^ (q + 1) : _ ≃ₗᵢ[ℂ] _)
    have hW : W = C * V := by
      apply ContinuousLinearMap.ext
      intro f
      change (U ^ (q + 1)) f = U ((U ^ q) f)
      rw [pow_succ', LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply]
    have hAdj : (C * V).adjoint = V.adjoint * C.adjoint := by
      simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp]
    have hL : L 1 t = P - C * P * C.adjoint := by
      unfold L torusPoissonCayleyCutoffDefect
      rw [pow_one]
    rw [hL]
    change P - W * P * W.adjoint =
      (P - C * P * C.adjoint) + C * (P - V * P * V.adjoint) * C.adjoint
    rw [hW, hAdj]
    simp only [mul_sub, sub_mul, mul_assoc]
    abel
  have hPos (q : ℕ) (t : ℝ) (f : SeqL2(d → ℤ)) : 0 ≤ (⟪f, L q t f⟫_ℂ).re := by
    have ⟨ha, hmul⟩ := torusPoissonCayleyCutoffDefect_is_projection β S T hT hCont hCount hAdvance t q
    change (L q t).adjoint = L q t at ha
    change L q t * L q t = L q t at hmul
    have h := (L q t).apply_norm_sq_eq_inner_adjoint_right f
    change ‖L q t f‖ ^ 2 = (⟪f, ((L q t).adjoint * L q t) f⟫_ℂ).re at h
    rw [ha, hmul] at h
    rw [← h]
    positivity
  have hMeas : Measurable (fun t : ℝ => ENNReal.ofReal (⟪e, L 1 t e⟫_ℂ).re) := by
    have he : (fun t : ℝ => ENNReal.ofReal (⟪e, L 1 t e⟫_ℂ).re) =
        fun t : ℝ => ENNReal.ofReal (L 1 t e 0).re := by
      funext t
      change ENNReal.ofReal (⟪lp.single 2 0 (1 : ℂ), L 1 t e⟫_ℂ).re = _
      rw [lp.inner_single_left, RCLike.inner_apply', map_one, one_mul]
    rw [he]
    exact ENNReal.measurable_ofReal.comp (Complex.continuous_re.measurable.comp
      (measurable_torusPoissonCayleyCutoffDefect_apply β S T hT hCont hCount hAdvance 1 e 0))
  change lpIntegratedZeroDiagonal (L q) = _
  induction q with
  | zero =>
    simp only [show L 0 = fun _ => 0 from funext hZero, lpIntegratedZeroDiagonal,
      zero_apply, inner_zero_right, Complex.zero_re, ENNReal.ofReal_zero,
      lintegral_zero, Nat.cast_zero, zero_mul]
  | succ q ih =>
    have hTraceConj := lpIntegratedZeroDiagonal_conj_torusPoissonCayleyCutoffDefect
      β S T hT hCont hCount hAdvance q
    change lpIntegratedZeroDiagonal (fun t => C * L q t * C.adjoint) = lpIntegratedZeroDiagonal (L q)
      at hTraceConj
    have hAdd : lpIntegratedZeroDiagonal (L (q + 1)) =
        lpIntegratedZeroDiagonal (L 1) +
          lpIntegratedZeroDiagonal (fun t => C * L q t * C.adjoint) := by
      unfold lpIntegratedZeroDiagonal
      change (∫⁻ t : ℝ, ENNReal.ofReal (⟪e, L (q + 1) t e⟫_ℂ).re) = _
      rw [← lintegral_add_left hMeas]
      apply lintegral_congr
      intro t
      rw [hRec, add_apply, inner_add_right, Complex.add_re, ENNReal.ofReal_add (hPos 1 t e)]
      have h := C.adjoint_inner_left (L q t (C.adjoint e)) e
      exact h ▸ hPos q t (C.adjoint e)
    rw [hAdd, hOne, hTraceConj, ih, Nat.cast_succ, add_mul, one_mul, add_comm]

end

end
end MeyerGeneralProblem
