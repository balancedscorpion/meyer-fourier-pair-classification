module

public import MeyerGeneralProblem.Gram.CanonicalGroupedUniformFloor
public import MeyerGeneralProblem.Cross.GroupedNormalizerPeeling
public import MeyerGeneralProblem.Endpoint.CompactModelFiniteness
public import MeyerGeneralProblem.Trace.PointTrace

@[expose] public section

/-!
# Conditional compact-cross consumer for actual canonical grouped traces

Inverse Hermite Fourier transports the full actual synthesis onto the
intrinsic inverse-Fourier support, without changing its Gram. A genuine raw
cross compact model with a strict floor-to-ceiling comparison then forces
the actual Meyer intersection to be finite-dimensional. The raw cross
compactness premise remains explicit; no analytic endpoint success is
claimed by this operator-theoretic adapter.
-/

namespace MeyerGeneralProblem

open Filter

noncomputable section

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ}
  (horder : BoundedClusterOrder S.signedSquareImage d q)

/-- The actual full grouped synthesis transported by inverse Hermite Fourier. -/
def actualGroupedInverseFourierSynthesis (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) :
    CoefficientSpace horder.signedGrouping.Index →L[ℂ] HermiteScale (-(m:ℤ)) :=
  (hermiteFourier (-(m:ℤ))).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (horder.actualGroupedBesselAnalysis hd m hm).synthesis

/-- Inverse Fourier preserves the actual coefficient Gram at the same order. -/
theorem actualGroupedInverseFourier_gram_eq (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) :
    coefficientGram (horder.actualGroupedInverseFourierSynthesis hd m hm) =
      horder.actualGroupedGramOperator hd m hm := by
  let B := (horder.actualGroupedBesselAnalysis hd m hm).synthesis
  let U : HermiteScale (-(m:ℤ)) →L[ℂ] HermiteScale (-(m:ℤ)) :=
    (hermiteFourier (-(m:ℤ))).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hU : U.adjoint.comp U = 1 := by
    apply U.norm_map_iff_adjoint_comp_self.mp
    exact (hermiteFourier (-(m:ℤ))).symm.norm_map
  rw [actualGroupedInverseFourierSynthesis, actualGroupedGramOperator,
    coefficientGram, coefficientGram, ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro c
  change B.adjoint (U.adjoint (U (B c))) = B.adjoint (B c)
  exact congrArg B.adjoint (congrArg
    (fun V : HermiteScale (-(m:ℤ)) →L[ℂ] HermiteScale (-(m:ℤ)) => V (B c)) hU)

/-- Full physical grouped coefficient support is the intrinsic support,
including the finite central groups. -/
theorem actualGrouped_coefficientAtomicSupport_eq (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) :
    coefficientAtomicSupport (horder.actualGroupedBesselAnalysis hd m hm).synthesis =
      fixedOrderPhysicalSupport S m (by have := (le_max_left _ _).trans hm; omega) := by
  classical
  apply SetLike.ext
  intro u
  change u ∈ atomicSupportSubspace (fun i =>
    (horder.actualGroupedBesselAnalysis hd m hm).synthesis (coefficientAtom i)) ↔ _
  simp only [BesselAnalysis.synthesis_coefficientAtom]
  rw [horder.signedGrouping.atom_closedSpan]
  rfl

/-- Full inverse-Fourier grouped support is exactly the corresponding
intrinsic inverse-Fourier support. -/
theorem actualGroupedInverseFourier_coefficientAtomicSupport_eq (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) :
    coefficientAtomicSupport (horder.actualGroupedInverseFourierSynthesis hd m hm) =
      fixedOrderInverseFourierSupport S m (by have := (le_max_left _ _).trans hm; omega) := by
  classical
  apply SetLike.ext
  intro u
  change u ∈ atomicSupportSubspace (fun i =>
    (horder.actualGroupedInverseFourierSynthesis hd m hm) (coefficientAtom i)) ↔ _
  simp only [actualGroupedInverseFourierSynthesis, ContinuousLinearMap.comp_apply,
    BesselAnalysis.synthesis_coefficientAtom]
  have hm1 : 1 ≤ m := by have := (le_max_left _ _).trans hm; omega
  change u ∈ atomicSupportSubspace (fun i =>
    (hermiteFourier (-(m:ℤ))).symm.toContinuousLinearEquiv
      (horder.signedGrouping.atom m hm1 i)) ↔ u ∈ fixedOrderInverseFourierSupport S m hm1
  rw [← atomicSupportSubspace_map_continuousLinearEquiv, horder.signedGrouping.atom_closedSpan]
  rfl

/-- The genuine raw cross is oriented as inverse-Fourier synthesis against
physical synthesis, hence has the source physical/Fourier kernel entries. -/
def actualGroupedRawCoefficientCross (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) :
    CoefficientSpace horder.signedGrouping.Index →L[ℂ] CoefficientSpace horder.signedGrouping.Index :=
  rawCoefficientCross (horder.actualGroupedInverseFourierSynthesis hd m hm)
    (horder.actualGroupedBesselAnalysis hd m hm).synthesis

/-- Exact raw-cross entries are the existing actual grouped Hilbert kernel,
with the original anchor weights and original signed-node prefix ordering. -/
theorem actualGroupedRawCoefficientCross_entry (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) (i j : horder.signedGrouping.Index) :
    inner ℂ (coefficientAtom i)
      (horder.actualGroupedRawCoefficientCross hd m hm (coefficientAtom j)) =
        horder.signedGrouping.crossKernel m
          (by have := (le_max_left _ _).trans hm; omega) i j := by
  classical
  rw [actualGroupedRawCoefficientCross, rawCoefficientCross, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, actualGroupedInverseFourierSynthesis,
    ContinuousLinearMap.comp_apply, BesselAnalysis.synthesis_coefficientAtom,
    BesselAnalysis.synthesis_coefficientAtom]
  exact ((hermiteFourier (-(m:ℤ))).inner_map_map
    ((hermiteFourier (-(m:ℤ))).symm (horder.signedGrouping.atom m _ i))
    (horder.signedGrouping.atom m _ j)).symm.trans (by simp [OrderedCarrierGrouping.crossKernel])

/-- A strict genuine cross-model comparison yields finite dimension of the
actual intrinsic Meyer layer. Only the raw cross compactness remains an
analytic premise; the actual Gram compactness and injectivity are proved. -/
theorem fixedOrderMeyerLayer_finiteDimensional_of_actualGrouped_crossModel
    (hd : 0 < d) (m : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    {W : ℝ} (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S.signedSquareImage < ENNReal.ofReal (2*W))
    (B₀ : CoefficientSpace horder.signedGrouping.Index →L[ℂ] CoefficientSpace horder.signedGrouping.Index)
    (hCross : IsCompactOperator (horder.actualGroupedRawCoefficientCross hd m hm-B₀))
    {A β : ℝ} (hA : 0 < A)
    (hfloor : A • (1 : CoefficientSpace horder.signedGrouping.Index →L[ℂ]
      CoefficientSpace horder.signedGrouping.Index) ≤ horder.universalGroupedGramOperator hd m hm)
    (hB₀ : ‖B₀‖ ≤ β) (hgap : β/A < 1) :
    FiniteDimensional ℂ (FixedOrderMeyerLayer S m
      (by have := (le_max_left _ _).trans hm; omega)) := by
  classical
  let G := horder.actualGroupedGramOperator hd m hm
  let H := horder.universalGroupedGramOperator hd m hm
  have hG : IsStrictlyPositive G := horder.actualGroupedGramOperator_strictlyPositive hd m hm hW hS
  have hH : IsStrictlyPositive H := horder.universalGroupedGramOperator_strictlyPositive hd m hm hW hS
  let C := gramWhitener H*B₀*gramWhitener H
  have hWcompact : IsCompactOperator (gramWhitener G-gramWhitener H) :=
    compact_gramWhitener_sub G H hG hH (horder.actualGroupedGram_sub_universal_isCompact hd m hm)
  have hcompact : IsCompactOperator
      (whitenedCoefficientCross (horder.actualGroupedInverseFourierSynthesis hd m hm)
        (horder.actualGroupedBesselAnalysis hd m hm).synthesis-C) := by
    rw [whitenedCoefficientCross, horder.actualGroupedInverseFourier_gram_eq]
    exact compact_whitenedCross_sub_model (gramWhitener G) (gramWhitener H)
      (horder.actualGroupedRawCoefficientCross hd m hm) B₀ hWcompact hCross
  have hC : ‖C‖ < 1 := by
    rcases subsingleton_or_nontrivial (CoefficientSpace horder.signedGrouping.Index) with h | h
    · let := h
      rw [Subsingleton.elim C 0, norm_zero]
      exact zero_lt_one
    · let := h
      exact norm_whitenedModel_lt_one_of_gram_le (gramWhitener H) B₀ hA
        (gramWhitener_gram_le_inv_floor H hA hfloor) hB₀ hgap
  have hfinite := coefficientAtomicSupport_inf_finiteDimensional_of_compact_model
    (horder.actualGroupedInverseFourierSynthesis hd m hm)
    (horder.actualGroupedBesselAnalysis hd m hm).synthesis
    (by rw [horder.actualGroupedInverseFourier_gram_eq]; exact hG) hG C hcompact hC
  rw [horder.actualGroupedInverseFourier_coefficientAtomicSupport_eq,
    horder.actualGrouped_coefficientAtomicSupport_eq, inf_comm] at hfinite
  exact hfinite

/-- Conditional cofinal finiteness from one genuine full cross-model
ceiling before all orders. The uniform Gram constant and geometric squeeze
are derived; actual raw cross compactness is deliberately still explicit. -/
theorem eventually_finiteLayer_of_uniform_actualGrouped_crossModels (hd : 0 < d)
    (hS : upperUniformBeurlingDensity S.signedSquareImage < 1) (C : ℝ)
    (hmodels : ∀ᶠ m : ℕ in atTop,
      ∀ hm : groupedHermiteDifferentiationOrder (q+1) ≤ m,
        ∃ B₀ : CoefficientSpace horder.signedGrouping.Index →L[ℂ]
            CoefficientSpace horder.signedGrouping.Index,
          ‖B₀‖ ≤ C*gramNormalization m*(m+1:ℝ)*(4:ℝ)⁻¹^m ∧
          IsCompactOperator (horder.actualGroupedRawCoefficientCross hd m hm-B₀)) :
    ∀ᶠ m : ℕ in atTop, ∀ hm : groupedHermiteDifferentiationOrder (q+1) ≤ m,
      FiniteDimensional ℂ (FixedOrderMeyerLayer S m
        (by have := (le_max_left _ _).trans hm; omega)) := by
  obtain ⟨W, hW, hWlt, hwindow⟩ := exists_subcritical_density_window S.signedSquareImage hS
  obtain ⟨A, hA, hfloor⟩ := horder.exists_uniform_universalGroupedGramFloor hd hW hwindow
  have hratio := eventually_leadingCrossCeiling_div_beurlingWindowFloor_lt_one C hA hW.le hWlt
  filter_upwards [hmodels, hratio] with m hmodel hratioM
  intro hm
  have hm1 : 1 ≤ m := by have := (le_max_left _ _).trans hm; omega
  obtain ⟨B₀, hB₀, hcompact⟩ := hmodel hm
  exact horder.fixedOrderMeyerLayer_finiteDimensional_of_actualGrouped_crossModel hd m hm hW hwindow
    B₀ hcompact (beurlingWindowGramFloor_pos hm1 W hA) (hfloor m hm) hB₀ (hratioM hm1)

end BoundedClusterOrder

end

end MeyerGeneralProblem
