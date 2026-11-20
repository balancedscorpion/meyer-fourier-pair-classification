module

public import MeyerGeneralProblem.Interpolation.CentralPhysicalInterpolation

@[expose] public section

/-!
# Exact finite values reconstructed from canonical prefix data

The disjoint union of the actual ordered clusters is equivalent to the
carrier. On each fiber the genuine finite Newton inverse reconstructs point
values. This gives one complex-linear value map on the carrier, an extension
to real arguments, and finite-selection bounds by the full canonical energy.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ} (ho : BoundedClusterOrder S d q)

/-- The actual canonical cluster/index pair of each carrier point. -/
def canonicalNodeEquiv : (Σ C : CanonicalClusterIndex S d, Fin (ho.clusterSize C)) ≃ S.subtype :=
  Equiv.ofBijective (fun p => ho.orderedClusterNode p.1 p.2) ho.orderedClusterNode_bijective

/-- Values and original prefix data on one actual canonical class. -/
def canonicalValuesEquiv (C : CanonicalClusterIndex S d) :
    (Fin (ho.clusterSize C) → ℂ) ≃ₗ[ℂ] (Fin (ho.clusterSize C) → ℂ) :=
  valuesEquivDividedDifferencesOfInjective (fun i => (ho.realClusterNode C i : ℂ))
    (Complex.ofReal_injective.comp (ho.realClusterNode_strictMono C).injective)

/-- Reconstructed values at actual carrier points, from the finite Newton
inverse on their exact canonical classes. -/
def canonicalDataValueMap :
    ((C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ) →ₗ[ℂ] (S.subtype → ℂ) where
  toFun data x :=
    let p := ho.canonicalNodeEquiv.symm x
    (ho.canonicalValuesEquiv p.1).symm (data p.1) p.2
  map_add' a b := by ext x; simp
  map_smul' a b := by ext x; simp

/-- At an enumerated canonical node the global map is exactly its own
class's finite inverse, without any change of prefix order. -/
theorem canonicalDataValueMap_node
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ)
    (C : CanonicalClusterIndex S d) (i : Fin (ho.clusterSize C)) :
    ho.canonicalDataValueMap data (ho.orderedClusterNode C i) =
      (ho.canonicalValuesEquiv C).symm (data C) i := by
  have h : ho.canonicalNodeEquiv.symm (ho.orderedClusterNode C i) = ⟨C, i⟩ :=
    ho.canonicalNodeEquiv.symm_apply_apply ⟨C, i⟩
  change (fun p : Σ C : CanonicalClusterIndex S d, Fin (ho.clusterSize C) =>
    (ho.canonicalValuesEquiv p.1).symm (data p.1) p.2)
      (ho.canonicalNodeEquiv.symm (ho.orderedClusterNode C i)) = _
  rw [h]

/-- The reconstructed carrier values extended by zero off the carrier.
The extension is used only to express exact finite analytic prefixes. -/
def canonicalDataFunctionMap :
    ((C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun data s := if hs : s ∈ S.carrier then ho.canonicalDataValueMap data ⟨s, hs⟩ else 0
  map_add' a b := by ext s; by_cases hs : s ∈ S.carrier <;> simp [hs]
  map_smul' a b := by ext s; by_cases hs : s ∈ S.carrier <;> simp [hs]

/-- On the actual carrier the real-argument extension is the value map. -/
theorem canonicalDataFunctionMap_on_carrier
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ) (x : S.subtype) :
    ho.canonicalDataFunctionMap data x = ho.canonicalDataValueMap data x := by
  change (if hs : (x : ℝ) ∈ S.subtype then ho.canonicalDataValueMap data ⟨x, hs⟩ else 0) = _
  rw [dite_eq_left x.property]

/-- Reconstructing values from arbitrary prefix data and taking their
actual analytic prefixes recovers every original coefficient exactly. -/
theorem canonicalPrefixData_canonicalDataFunctionMap
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ) :
    ho.canonicalPrefixData (ho.canonicalDataFunctionMap data) = data := by
  funext C i
  rw [canonicalPrefixData, analyticDividedDifference_eq_dividedDifferences
    (ho.realClusterNode C) (ho.realClusterNode_strictMono C).injective]
  have hv : (fun j => ho.canonicalDataFunctionMap data (ho.realClusterNode C j)) =
      (ho.canonicalValuesEquiv C).symm (data C) := by
    funext j
    exact (ho.canonicalDataFunctionMap_on_carrier data (ho.orderedClusterNode C j)).trans
      (ho.canonicalDataValueMap_node data C j)
  rw [hv]
  exact congrFun ((ho.canonicalValuesEquiv C).apply_symm_apply (data C)) i

/-- Original canonical prefixes themselves form a complex-linear map on
arbitrary functions, since actual nodes are distinct. -/
def canonicalPrefixDataLinearMap :
    (ℝ → ℂ) →ₗ[ℂ] ((C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ) where
  toFun := ho.canonicalPrefixData
  map_add' a b := by
    funext C i
    simp only [Pi.add_apply, canonicalPrefixData, analyticDividedDifference_eq_dividedDifferences
      (ho.realClusterNode C) (ho.realClusterNode_strictMono C).injective]
    exact congrFun ((ho.canonicalValuesEquiv C).map_add
      (fun j => a (ho.realClusterNode C j)) (fun j => b (ho.realClusterNode C j))) i
  map_smul' a b := by
    funext C i
    simp only [Pi.smul_apply, RingHom.id_apply, canonicalPrefixData, analyticDividedDifference_eq_dividedDifferences
      (ho.realClusterNode C) (ho.realClusterNode_strictMono C).injective]
    exact congrFun ((ho.canonicalValuesEquiv C).map_smul a
      (fun j => b (ho.realClusterNode C j))) i

/-- Reconstructing a function's prefix data reproduces its actual carrier
values, without any regularity assumption on the function. -/
theorem canonicalDataValueMap_canonicalPrefixData (g : ℝ → ℂ) (x : S.subtype) :
    ho.canonicalDataValueMap (ho.canonicalPrefixData g) x = g x := by
  obtain ⟨⟨C, i⟩, rfl⟩ := ho.orderedClusterNode_bijective.2 x
  rw [ho.canonicalDataValueMap_node]
  have hd : ho.canonicalPrefixData g C =
      ho.canonicalValuesEquiv C (fun j => g (ho.realClusterNode C j)) := by
    funext j
    exact analyticDividedDifference_eq_dividedDifferences
      (ho.realClusterNode C) (ho.realClusterNode_strictMono C).injective g j
  rw [hd, LinearEquiv.symm_apply_apply]
  rfl

/-- One fixed class's actual finite Newton inverse has a finite operator
norm. This is a central-geometry constant, not a uniform intragroup bound. -/
def canonicalValueInverseBound (C : CanonicalClusterIndex S d) : ℝ :=
  ‖(ho.canonicalValuesEquiv C).symm.toContinuousLinearEquiv.toContinuousLinearMap‖ ^ 2

/-- A reconstructed point value is bounded by the full finite coefficient
energy of its class, with the norm of the genuine finite inverse. -/
theorem canonicalDataValueMap_sq_le
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ)
    (x : S.subtype) :
    ‖ho.canonicalDataValueMap data x‖ ^ 2 ≤
      ho.canonicalValueInverseBound (ho.canonicalNodeEquiv.symm x).1 *
        ∑ j, ‖data (ho.canonicalNodeEquiv.symm x).1 j‖ ^ 2 := by
  let C := (ho.canonicalNodeEquiv.symm x).1
  let i := (ho.canonicalNodeEquiv.symm x).2
  let L := (ho.canonicalValuesEquiv C).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hnorm : ‖ho.canonicalDataValueMap data x‖ ≤ ‖L‖ * ‖data C‖ :=
    (norm_le_pi_norm (L (data C)) i).trans (L.le_opNorm (data C))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hdata : ‖data C‖ ^ 2 ≤ ∑ j, ‖data C j‖ ^ 2 := by
    have h := groupedData_norm_sq_le_sum (fun _ : Fin 1 => ho.clusterSize C) (fun _ => data C)
    simpa using h
  change ‖ho.canonicalDataValueMap data x‖ ^ 2 ≤ ‖L‖ ^ 2 * ∑ j, ‖data C j‖ ^ 2
  exact hsq.trans (by simpa only [mul_pow] using
    mul_le_mul_of_nonneg_left hdata (sq_nonneg ‖L‖))

/-- Every unweighted class energy is below the full canonical weighted
energy, because every physical anchor weight is at least one. -/
theorem classDataEnergy_le_canonicalWeighted (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ)
    (C : CanonicalClusterIndex S d) :
    ENNReal.ofReal (∑ j, ‖data C j‖ ^ 2) ≤ ho.canonicalWeightedDataEnergy k anchor data := by
  have hw : 1 ≤ (1 + Real.sqrt |ho.realClusterNode C (anchor C)|) ^ (2*k-1) :=
    one_le_pow₀ (by linarith [Real.sqrt_nonneg |ho.realClusterNode C (anchor C)|])
  have hw' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal
      ((1 + Real.sqrt |ho.realClusterNode C (anchor C)|) ^ (2*k-1)) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hw
  unfold canonicalWeightedDataEnergy
  apply (le_mul_of_one_le_left' hw').trans
  exact ENNReal.le_tsum (f := fun D => ENNReal.ofReal
    ((1 + Real.sqrt |ho.realClusterNode D (anchor D)|) ^ (2 * k - 1)) *
    ENNReal.ofReal (∑ j, ‖data D j‖ ^ 2)) C

/-- Any actual finite selection of carrier values has a squared bound by
the full canonical weighted data. The constant is fixed before the data;
its allowed dependence is only on the selected finite geometry. -/
theorem exists_finite_canonicalDataValue_energy_bound (F : Finset S.subtype) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      ∀ anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C),
      ∀ data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ,
      ENNReal.ofReal (∑ x : F, ‖ho.canonicalDataValueMap data x.val‖ ^ 2) ≤
        ENNReal.ofReal C * ho.canonicalWeightedDataEnergy k anchor data := by
  let c (x : F) := ho.canonicalValueInverseBound (ho.canonicalNodeEquiv.symm x.val).1
  have hc (x : F) : 0 ≤ c x := sq_nonneg _
  have hcs : 0 ≤ ∑ x : F, c x := Finset.sum_nonneg (fun x _ => hc x)
  refine ⟨1 + ∑ x : F, c x, by positivity, ?_⟩
  intro k anchor data
  rw [ENNReal.ofReal_sum_of_nonneg (by intro x _; positivity)]
  have hp (x : F) : ENNReal.ofReal (‖ho.canonicalDataValueMap data x.val‖ ^ 2) ≤
      ENNReal.ofReal (c x) * ho.canonicalWeightedDataEnergy k anchor data := by
    apply (ENNReal.ofReal_le_ofReal (ho.canonicalDataValueMap_sq_le data x.val)).trans
    rw [ENNReal.ofReal_mul (hc x)]
    exact mul_le_mul' le_rfl (ho.classDataEnergy_le_canonicalWeighted k anchor data _)
  calc
    _ ≤ ∑ x : F, ENNReal.ofReal (c x)*ho.canonicalWeightedDataEnergy k anchor data :=
      Finset.sum_le_sum (fun x _ => hp x)
    _ = ENNReal.ofReal (∑ x : F, c x)*ho.canonicalWeightedDataEnergy k anchor data := by
      rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun x _ => hc x)]
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end BoundedClusterOrder

end

end MeyerGeneralProblem
