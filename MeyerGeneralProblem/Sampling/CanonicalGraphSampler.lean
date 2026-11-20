module

public import MeyerGeneralProblem.Sampling.KNSGraphPointIdentification

@[expose] public section

/-!
# Conditional construction of the canonical graph sampler

This module isolates the algebraic bridge from a real
summable weighted original-prefix estimate for the actual graph
representative to a bounded complex-linear sampler. The estimate itself is
an explicit parameter; no sampler bound is assumed silently.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal FourierTransform

attribute [local instance] Classical.propDecidable

namespace KNSGraphSpace

private theorem frequency_power_memLp_for_sampler
    {k : ℕ} (v : KNSGraphSpace k) :
    MemLp (fun x : ℝ => (x : ℂ) ^ k * frequency k v x) 2 :=
  (memLp_congr_ae (frequencyWeight_ae v)).mpr (Lp.memLp _)

private theorem frequency_integrable_for_sampler
    {k : ℕ} (hk : 1 ≤ k) (v : KNSGraphSpace k) :
    Integrable (frequency k v : ℝ → ℂ) :=
  (fourier_regular_of_physical_power k hk (Lp.memLp _)
    (frequency_power_memLp_for_sampler v)).1

/-- The chosen actual representative is additive at positive graph order.
This is proved from genuine integrability of both frequency coordinates,
not from an almost-everywhere representative identity. -/
theorem representative_add {k : ℕ} (hk : 1 ≤ k)
    (v w : KNSGraphSpace k) :
    representative k (v + w) = representative k v + representative k w := by
  funext x
  change 𝓕 (frequency k (v + w) : ℝ → ℂ) (-x) =
    𝓕 (frequency k v : ℝ → ℂ) (-x) +
      𝓕 (frequency k w : ℝ → ℂ) (-x)
  have hfreq : (frequency k (v + w) : ℝ → ℂ) =ᵐ[volume]
      (frequency k v : ℝ → ℂ) + (frequency k w : ℝ → ℂ) := by
    rw [map_add]
    exact Lp.coeFn_add _ _
  calc
    _ = 𝓕 ((frequency k v : ℝ → ℂ) +
        (frequency k w : ℝ → ℂ)) (-x) := Real.fourier_congr_ae hfreq (-x)
    _ = _ := congrFun (VectorFourier.fourierIntegral_add Real.continuous_fourierChar
      continuous_inner (frequency_integrable_for_sampler hk v)
        (frequency_integrable_for_sampler hk w)) (-x)

/-- The chosen actual representative respects complex scalar multiplication
pointwise. -/
theorem representative_smul {k : ℕ} (_hk : 1 ≤ k)
    (a : ℂ) (v : KNSGraphSpace k) :
    representative k (a • v) = a • representative k v := by
  funext x
  change 𝓕 (frequency k (a • v) : ℝ → ℂ) (-x) =
    a * 𝓕 (frequency k v : ℝ → ℂ) (-x)
  have hfreq : (frequency k (a • v) : ℝ → ℂ) =ᵐ[volume]
      a • (frequency k v : ℝ → ℂ) := by
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  calc
    _ = 𝓕 (a • (frequency k v : ℝ → ℂ)) (-x) :=
      Real.fourier_congr_ae hfreq (-x)
    _ = _ := congrFun (VectorFourier.fourierIntegral_const_smul
      Real.fourierChar volume (innerₗ ℝ) (frequency k v : ℝ → ℂ) a) (-x)

/-- The actual pointwise representative as a complex-linear function-valued
map. No topology is put on the function codomain. -/
def representativeLinearMap (k : ℕ) (hk : 1 ≤ k) :
    KNSGraphSpace k →ₗ[ℂ] (ℝ → ℂ) where
  toFun := representative k
  map_add' := representative_add hk
  map_smul' := representative_smul hk

@[simp] theorem representativeLinearMap_apply
    (k : ℕ) (hk : 1 ≤ k) (v : KNSGraphSpace k) :
    representativeLinearMap k hk v = representative k v := rfl

end KNSGraphSpace

namespace BoundedClusterOrder

variable (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
  (ho : BoundedClusterOrder S.signedSquareImage d q)

/-- The raw original canonical-prefix vector of the chosen actual physical
representative, before weighted Hilbert-space encoding. -/
def canonicalPhysicalPrefixLinearMap (k : ℕ) (hk : 1 ≤ k) :
    KNSGraphSpace k →ₗ[ℂ]
      ((C : CanonicalClusterIndex S.signedSquareImage d) →
        Fin (ho.clusterSize C) → ℂ) :=
  (ho.canonicalPrefixDataLinearMap.comp S.physicalSignedSquarePullbackMap).comp
    (KNSGraphSpace.representativeLinearMap k hk)

@[simp] theorem canonicalPhysicalPrefixLinearMap_apply
    (k : ℕ) (hk : 1 ≤ k) (v : KNSGraphSpace k)
    (C : CanonicalClusterIndex S.signedSquareImage d)
    (j : Fin (ho.clusterSize C)) :
    ho.canonicalPhysicalPrefixLinearMap S k hk v C j =
      ho.canonicalPrefixData
        (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j := rfl

/-- One nonnegative real weighted block energy of the actual original
canonical prefixes. -/
def canonicalPhysicalPrefixBlockEnergy (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k)
    (C : CanonicalClusterIndex S.signedSquareImage d) : ℝ :=
    (1 + Real.sqrt |ho.realClusterNode C (anchor C)|) ^ (2 * k - 1) *
      ∑ j, ‖ho.canonicalPhysicalPrefixLinearMap S k hk v C j‖ ^ 2

/-- The real full weighted original-prefix energy whose summability and bound
are the sole analytic inputs to this bridge. -/
def canonicalPhysicalPrefixRealEnergy (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k) : ℝ :=
  ∑' C : CanonicalClusterIndex S.signedSquareImage d,
    ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v C

theorem canonicalPhysicalPrefixBlockEnergy_nonneg
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k)
    (C : CanonicalClusterIndex S.signedSquareImage d) :
    0 ≤ ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v C := by
  unfold canonicalPhysicalPrefixBlockEnergy
  positivity

theorem canonicalPhysicalPrefixRealEnergy_nonneg
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k) :
    0 ≤ ho.canonicalPhysicalPrefixRealEnergy S k hk anchor v := by
  exact tsum_nonneg (fun C =>
    ho.canonicalPhysicalPrefixBlockEnergy_nonneg S k hk anchor v C)

/-- A summable real full-prefix energy is exactly the existing ENNReal
canonical weighted energy of the raw representative prefixes. -/
theorem canonicalWeightedDataEnergy_canonicalPhysicalPrefix_eq_ofReal
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k)
    (hsum : Summable
      (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v)) :
    ho.canonicalWeightedDataEnergy k anchor
        (ho.canonicalPhysicalPrefixLinearMap S k hk v) =
      ENNReal.ofReal (ho.canonicalPhysicalPrefixRealEnergy S k hk anchor v) := by
  unfold canonicalWeightedDataEnergy canonicalPhysicalPrefixRealEnergy
  calc
    _ = ∑' C : CanonicalClusterIndex S.signedSquareImage d,
        ENNReal.ofReal
          (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v C) := by
      apply tsum_congr
      intro C
      unfold canonicalPhysicalPrefixBlockEnergy
      rw [ENNReal.ofReal_mul (by positivity)]
    _ = _ := (ENNReal.ofReal_tsum_of_nonneg
      (fun C => ho.canonicalPhysicalPrefixBlockEnergy_nonneg S k hk anchor v C) hsum).symm

/-- Real summability proves ENNReal finiteness before any call to
`canonicalGraphEncode`. -/
theorem canonicalPhysicalPrefix_energy_ne_top
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k)
    (hsum : Summable
      (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v)) :
    ho.canonicalWeightedDataEnergy k anchor
        (ho.canonicalPhysicalPrefixLinearMap S k hk v) ≠ ⊤ := by
  rw [ho.canonicalWeightedDataEnergy_canonicalPhysicalPrefix_eq_ofReal
    S k hk anchor v hsum]
  exact ENNReal.ofReal_ne_top

/-- The everywhere-defined complex-linear sampler obtained after proving
summability for every graph vector. Its value is the exact existing weighted
encoding of the actual original-prefix vector. -/
def canonicalPhysicalSamplerLinearMap
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v)) :
    KNSGraphSpace k →ₗ[ℂ] ho.CanonicalGraphData where
  toFun v := ho.canonicalGraphEncode k anchor
    (ho.canonicalPhysicalPrefixLinearMap S k hk v)
    (ho.canonicalPhysicalPrefix_energy_ne_top S k hk anchor v (hsummable v))
  map_add' v w := by
    apply Subtype.ext
    funext C
    apply PiLp.ext
    intro j
    change (ho.canonicalGraphWeight k anchor C : ℂ) *
        ho.canonicalPhysicalPrefixLinearMap S k hk (v + w) C j =
      (ho.canonicalGraphWeight k anchor C : ℂ) *
          ho.canonicalPhysicalPrefixLinearMap S k hk v C j +
        (ho.canonicalGraphWeight k anchor C : ℂ) *
          ho.canonicalPhysicalPrefixLinearMap S k hk w C j
    rw [map_add]
    simp only [Pi.add_apply]
    ring
  map_smul' a v := by
    apply Subtype.ext
    funext C
    apply PiLp.ext
    intro j
    change (ho.canonicalGraphWeight k anchor C : ℂ) *
        ho.canonicalPhysicalPrefixLinearMap S k hk (a • v) C j =
      a * ((ho.canonicalGraphWeight k anchor C : ℂ) *
        ho.canonicalPhysicalPrefixLinearMap S k hk v C j)
    rw [map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Decoding the linear sampler recovers every raw original prefix exactly. -/
theorem canonicalGraphDecode_canonicalPhysicalSamplerLinearMap
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v))
    (v : KNSGraphSpace k) :
    ho.canonicalGraphDecode k anchor
        (ho.canonicalPhysicalSamplerLinearMap S k hk anchor hsummable v) =
      ho.canonicalPhysicalPrefixLinearMap S k hk v := by
  simpa only [canonicalPhysicalSamplerLinearMap, LinearMap.coe_mk,
    AddHom.coe_mk] using
      ho.canonicalGraphDecode_encode k anchor
        (ho.canonicalPhysicalPrefixLinearMap S k hk v)
        (ho.canonicalPhysicalPrefix_energy_ne_top S k hk anchor v (hsummable v))

/-- The sampler's Hilbert norm squared is exactly the real weighted
original-prefix energy. -/
theorem norm_sq_canonicalPhysicalSamplerLinearMap
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v))
    (v : KNSGraphSpace k) :
    ‖ho.canonicalPhysicalSamplerLinearMap S k hk anchor hsummable v‖ ^ 2 =
      ho.canonicalPhysicalPrefixRealEnergy S k hk anchor v := by
  have hdecode := ho.canonicalGraphDecode_canonicalPhysicalSamplerLinearMap
    S k hk anchor hsummable v
  have hencoded := ho.canonicalWeightedDataEnergy_decode k anchor
    (ho.canonicalPhysicalSamplerLinearMap S k hk anchor hsummable v)
  rw [hdecode] at hencoded
  have hreal := ho.canonicalWeightedDataEnergy_canonicalPhysicalPrefix_eq_ofReal
    S k hk anchor v (hsummable v)
  have h := congrArg ENNReal.toReal (hencoded.symm.trans hreal)
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal
      (ho.canonicalPhysicalPrefixRealEnergy_nonneg S k hk anchor v)] using h

/-- A real full-energy bound gives the square-root norm bound needed to
bundle the sampler continuously. -/
theorem norm_canonicalPhysicalSamplerLinearMap_le
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (A : ℝ) (hA : 0 ≤ A)
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v))
    (hbound : ∀ v : KNSGraphSpace k,
      ho.canonicalPhysicalPrefixRealEnergy S k hk anchor v ≤ A * ‖v‖ ^ 2)
    (v : KNSGraphSpace k) :
    ‖ho.canonicalPhysicalSamplerLinearMap S k hk anchor hsummable v‖ ≤
      Real.sqrt A * ‖v‖ := by
  have hsquare :
      ‖ho.canonicalPhysicalSamplerLinearMap S k hk anchor hsummable v‖ ^ 2 ≤
        A * ‖v‖ ^ 2 := by
    rw [ho.norm_sq_canonicalPhysicalSamplerLinearMap S k hk anchor hsummable v]
    exact hbound v
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg A) (norm_nonneg v))).mp
  rw [mul_pow, Real.sq_sqrt hA]
  exact hsquare

/-- The bounded complex-linear physical sampler. This maps graph functions to
weighted original-prefix coordinates; it is the direction opposite to the
existing `canonicalGraphInterpolator`. -/
def canonicalPhysicalSampler
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (A : ℝ) (hA : 0 ≤ A)
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v))
    (hbound : ∀ v : KNSGraphSpace k,
      ho.canonicalPhysicalPrefixRealEnergy S k hk anchor v ≤ A * ‖v‖ ^ 2) :
    KNSGraphSpace k →L[ℂ] ho.CanonicalGraphData :=
  (ho.canonicalPhysicalSamplerLinearMap S k hk anchor hsummable).mkContinuous
    (Real.sqrt A)
    (ho.norm_canonicalPhysicalSamplerLinearMap_le S k hk anchor A hA hsummable hbound)

/-- Exact weighted original-prefix coordinate formula for the bounded
physical sampler. -/
@[simp] theorem canonicalPhysicalSampler_apply_coord
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (A : ℝ) (hA : 0 ≤ A)
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v))
    (hbound : ∀ v : KNSGraphSpace k,
      ho.canonicalPhysicalPrefixRealEnergy S k hk anchor v ≤ A * ‖v‖ ^ 2)
    (v : KNSGraphSpace k)
    (C : CanonicalClusterIndex S.signedSquareImage d)
    (j : Fin (ho.clusterSize C)) :
    ho.canonicalPhysicalSampler S k hk anchor A hA hsummable hbound v C j =
      (ho.canonicalGraphWeight k anchor C : ℂ) *
        ho.canonicalPrefixData
          (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j := rfl

/-- The declared continuous-map bound. -/
theorem norm_canonicalPhysicalSampler_le
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (A : ℝ) (hA : 0 ≤ A)
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v))
    (hbound : ∀ v : KNSGraphSpace k,
      ho.canonicalPhysicalPrefixRealEnergy S k hk anchor v ≤ A * ‖v‖ ^ 2)
    (v : KNSGraphSpace k) :
    ‖ho.canonicalPhysicalSampler S k hk anchor A hA hsummable hbound v‖ ≤
      Real.sqrt A * ‖v‖ :=
  ho.norm_canonicalPhysicalSamplerLinearMap_le S k hk anchor A hA hsummable hbound v

/-- Decoding the bounded sampler recovers the unweighted raw original
prefixes exactly. -/
theorem canonicalGraphDecode_canonicalPhysicalSampler
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (A : ℝ) (hA : 0 ≤ A)
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v))
    (hbound : ∀ v : KNSGraphSpace k,
      ho.canonicalPhysicalPrefixRealEnergy S k hk anchor v ≤ A * ‖v‖ ^ 2)
    (v : KNSGraphSpace k) :
    ho.canonicalGraphDecode k anchor
        (ho.canonicalPhysicalSampler S k hk anchor A hA hsummable hbound v) =
      ho.canonicalPhysicalPrefixLinearMap S k hk v :=
  ho.canonicalGraphDecode_canonicalPhysicalSamplerLinearMap S k hk anchor hsummable v

/-- Fourier sampling is physical sampling after the genuine graph Fourier
isometric equivalence. -/
def canonicalFourierSampler
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (A : ℝ) (hA : 0 ≤ A)
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v))
    (hbound : ∀ v : KNSGraphSpace k,
      ho.canonicalPhysicalPrefixRealEnergy S k hk anchor v ≤ A * ‖v‖ ^ 2) :
    KNSGraphSpace k →L[ℂ] ho.CanonicalGraphData :=
  (ho.canonicalPhysicalSampler S k hk anchor A hA hsummable hbound).comp
    (KNSGraphSpace.fourierEquiv k).toContinuousLinearEquiv.toContinuousLinearMap

/-- Exact Fourier-sampler coordinate formula, retaining the actual
representative of the transformed graph element. -/
@[simp] theorem canonicalFourierSampler_apply_coord
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (A : ℝ) (hA : 0 ≤ A)
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v))
    (hbound : ∀ v : KNSGraphSpace k,
      ho.canonicalPhysicalPrefixRealEnergy S k hk anchor v ≤ A * ‖v‖ ^ 2)
    (v : KNSGraphSpace k)
    (C : CanonicalClusterIndex S.signedSquareImage d)
    (j : Fin (ho.clusterSize C)) :
    ho.canonicalFourierSampler S k hk anchor A hA hsummable hbound v C j =
      (ho.canonicalGraphWeight k anchor C : ℂ) *
        ho.canonicalPrefixData
          (S.physicalSignedSquarePullbackMap
            (KNSGraphSpace.representative k (KNSGraphSpace.fourier k v))) C j := rfl

/-- Fourier sampling inherits the same bound because graph Fourier is an
isometry. -/
theorem norm_canonicalFourierSampler_le
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (A : ℝ) (hA : 0 ≤ A)
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v))
    (hbound : ∀ v : KNSGraphSpace k,
      ho.canonicalPhysicalPrefixRealEnergy S k hk anchor v ≤ A * ‖v‖ ^ 2)
    (v : KNSGraphSpace k) :
    ‖ho.canonicalFourierSampler S k hk anchor A hA hsummable hbound v‖ ≤
      Real.sqrt A * ‖v‖ := by
  change ‖ho.canonicalPhysicalSampler S k hk anchor A hA hsummable hbound
      (KNSGraphSpace.fourierEquiv k v)‖ ≤ _
  simpa using ho.norm_canonicalPhysicalSampler_le S k hk anchor A hA hsummable hbound
    (KNSGraphSpace.fourierEquiv k v)

/-- On the existing interpolation range, the physical sampler is an exact
left inverse of `canonicalGraphInterpolator`. Thus the interpolator is a
right inverse of this sampler; the two operators are kept directionally
distinct. -/
theorem canonicalPhysicalSampler_canonicalGraphInterpolator
    (N k : ℕ) (hk : 2 ≤ k) {B : ℝ} (hB : 1 ≤ B)
    (hd : 0 < d) (hdiam : (q : ℝ) * d ≤ B) (b₀ : ℤ)
    (hpositive : ∀ j : ℤ, b₀ ≤ j →
      (orientedBlockPoints S.signedSquareImage B 1 j).ncard ≤ N)
    (hnegative : ∀ j : ℤ, b₀ ≤ j →
      (orientedBlockPoints S.signedSquareImage B (-1) j).ncard ≤ N)
    (start : ℕ) (hstart : 3 ≤ start) (hstart₀ : b₀ + 1 ≤ (start : ℤ))
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (A : ℝ) (hA : 0 ≤ A)
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k (by omega) anchor v))
    (hbound : ∀ v : KNSGraphSpace k,
      ho.canonicalPhysicalPrefixRealEnergy S k (by omega) anchor v ≤ A * ‖v‖ ^ 2)
    (y : ho.CanonicalGraphData) :
    ho.canonicalPhysicalSampler S k (by omega) anchor A hA hsummable hbound
        (S.canonicalGraphInterpolator ho N k hk hB hd hdiam b₀
          hpositive hnegative start hstart hstart₀ anchor y) = y := by
  let hk₁ : 1 ≤ k := by omega
  let T := S.canonicalGraphInterpolator ho N k hk hB hd hdiam b₀
    hpositive hnegative start hstart hstart₀ anchor
  have hp : ho.canonicalPhysicalPrefixLinearMap S k hk₁ (T y) =
      ho.canonicalGraphDecode k anchor y := by
    exact KNSGraphSpace.representative_canonicalGraphInterpolator_prefix
      S ho N k hk hB hd hdiam b₀ hpositive hnegative start hstart hstart₀ anchor y
  apply Subtype.ext
  change ho.canonicalGraphNormalize k anchor
      (ho.canonicalPhysicalPrefixLinearMap S k hk₁ (T y)) = y
  rw [hp, ho.canonicalGraphNormalize_decode]

end BoundedClusterOrder

end

end MeyerGeneralProblem
