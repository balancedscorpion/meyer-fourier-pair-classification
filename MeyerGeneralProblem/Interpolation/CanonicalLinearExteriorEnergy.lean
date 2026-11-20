module

public import MeyerGeneralProblem.Interpolation.CanonicalPolynomialLinearity
public import MeyerGeneralProblem.Interpolation.CanonicalExteriorInterpolation

@[expose] public section

/-!
# Energy of the actual canonical exterior linear map

The named polynomial inverse and locally finite ray sum receive the uniform
energy bound directly from their proved derivatives and the actual weighted
five-window reindexing. No separately chosen interpolating family is used.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ} (ho : BoundedClusterOrder S d q)

/-- The named exterior linear map is the actual ray tail of the named
canonical polynomial family. -/
theorem canonicalExteriorLinearMap_apply (hd : 0 < d) {B : ℝ} (hB : 0 < B)
    (start : ℕ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ) :
    ho.canonicalExteriorLinearMap hd hB start hε data =
      physicalRayBlockTail B start ε (ho.canonicalLocalFamilyMap hd B hε data) := rfl

/-- The actual exterior linear map is smooth for arbitrary canonical data. -/
theorem contDiff_canonicalExteriorLinearMap (hd : 0 < d) {B : ℝ} (hB : 0 < B)
    (start : ℕ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ) :
    ContDiff ℝ ∞ (ho.canonicalExteriorLinearMap hd hB start hε data) :=
  contDiff_physicalRayBlockTail hB start ε _
    (fun b => ho.contDiff_allTouchingLocalFunctionMap hd B hε b data)

/-- The actual exterior linear map vanishes on the other ray and at zero. -/
theorem canonicalExteriorLinearMap_wrongRay (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B)
    (start : ℕ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ)
    {x : ℝ} (hx : ε*x ≤ 0) :
    ho.canonicalExteriorLinearMap hd (B := B) (by linarith) start hε data x = 0 := by
  exact physicalRayBlockTail_eq_zero_of_nonpos hB start
    (by rcases hε with rfl | rfl <;> norm_num) _ hx

/-- Function-derived canonical data give exact transition-weighted values
for the named exterior linear map on its actual physical ray. -/
theorem canonicalExteriorLinearMap_eq_on_carrier (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B)
    (start : ℕ) (hstart : 3 ≤ start) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (g : ℝ → ℂ) (x : ℝ) (hx : 0 < ε*x) (hs : ε*x^2 ∈ S.carrier) :
    ho.canonicalExteriorLinearMap hd (B := B) (by linarith) start hε (ho.canonicalPrefixData g) x =
      blockTransition B start (x^2) • g (ε*x^2) := by
  exact ho.physicalRayBlockTail_eq_on_carrier hB start hstart hε g _
    (fun b _ C hC i => ho.allTouchingLocalFunctionMap_prefix hd B hε b _ C hC i) x hx hs

end BoundedClusterOrder

/-- The actual named exterior linear map has a common weighted energy bound.
Constants precede the carrier, ray, source threshold, tail start, anchor, and
data. Only the actual numerical block count and geometric bounds are inputs. -/
theorem exists_uniform_canonicalExteriorLinearMap_energy (N q k : ℕ) (hk : 1 ≤ k)
    {B d : ℝ} (hB : 1 ≤ B) (hd : 0 < d) (hdiam : (q : ℝ)*d ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ S : LocallyFiniteCarrier,
      ∀ ho : BoundedClusterOrder S d q, ∀ ε : ℝ, ∀ hε : ε = 1 ∨ ε = -1,
      ∀ b₀ : ℤ, (∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S B ε j).ncard ≤ N) →
      ∀ start : ℕ, 3 ≤ start → b₀+1 ≤ (start : ℤ) →
      ∀ anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C),
      ∀ data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ,
        physicalInterpolationEnergy k
          (ho.canonicalExteriorLinearMap hd (B := B) (by linarith) start hε data) ≤
            ENNReal.ofReal K * ho.canonicalWeightedDataEnergy k anchor data := by
  have hBpos : 0 < B := by linarith
  obtain ⟨A, hA, hfamily⟩ := exists_uniform_canonicalLocalFamilyMap_bound N q k hB hd hdiam
  obtain ⟨R, hR, hray⟩ := exists_uniform_exteriorRayBlockSum_lintegral_bound k
  let K : ℝ := (3*R*B)*(A^2*(5*(3:ℝ)^((k:ℝ)-1/2)))
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro S ho ε hε b₀ hcount start _hstart hstart₀ anchor data
  let h := ho.canonicalLocalFamilyMap hd B hε data
  have hs (b : ℕ) : ContDiff ℝ ∞ (h b) :=
    ho.contDiff_allTouchingLocalFunctionMap hd B hε b data
  have hεsq : ε^2=1 := by rcases hε with rfl | rfl <;> norm_num
  have hlocal : ∀ b : ℕ, 3 ≤ b →
      ∀ x ∈ Icc ((b:ℝ)*B-B/8) (((b:ℝ)+1)*B+B/8), ∀ j ≤ k,
        ‖iteratedDeriv j (tailBlockFunctions start h b) x‖ ≤
          A*Real.sqrt (ho.canonicalBlockDataEnergy B hε b data) := by
    intro b _hb x hx j hj
    by_cases hsb : start ≤ b
    · have hb₀ : b₀+1 ≤ (b:ℤ) := hstart₀.trans (by exact_mod_cast hsb)
      simpa only [tailBlockFunctions, hsb, ite_true, h] using
        hfamily S ho ε hε b₀ hcount b hb₀ data x hx j hj
    · simpa only [tailBlockFunctions, hsb, ite_false, iteratedDeriv_const, ite_self, norm_zero]
        using mul_nonneg hA.le (Real.sqrt_nonneg (ho.canonicalBlockDataEnergy B hε b data))
  have he := hray B hB ε hεsq (tailBlockFunctions start h)
    (fun b => contDiff_tailBlockFunctions start b h (hs b))
    (fun b => A*Real.sqrt (ho.canonicalBlockDataEnergy B hε b data))
    (fun b => mul_nonneg hA.le (Real.sqrt_nonneg _)) hlocal
  have hw := ho.tsum_canonicalBlockDataEnergy_weighted_le hBpos hd hdiam hε k hk anchor data
  have hKcast : ENNReal.ofReal K = ENNReal.ofReal (3*R*B)*
      (ENNReal.ofReal (A^2)*(5*ENNReal.ofReal ((3:ℝ)^((k:ℝ)-1/2)))) := by
    dsimp [K]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 3*R*B),
      ENNReal.ofReal_mul (sq_nonneg A), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5)]
    norm_num
  calc
    _ ≤ ENNReal.ofReal (3*R*B)*(ENNReal.ofReal (A^2)*∑' b : ℕ,
        if 3 ≤ b then ENNReal.ofReal (((b:ℝ)*B)^((k:ℝ)-1/2))*
          ENNReal.ofReal (ho.canonicalBlockDataEnergy B hε b data) else 0) := by
      simpa only [ho.canonicalExteriorLinearMap_apply, physicalInterpolationEnergy,
        physicalRayBlockTail, h, ho.tsum_canonicalBlock_sqrtEnergy_sq B hε k A data] using he
    _ ≤ ENNReal.ofReal (3*R*B)*(ENNReal.ofReal (A^2)*
        (5*ENNReal.ofReal ((3:ℝ)^((k:ℝ)-1/2))*ho.canonicalWeightedDataEnergy k anchor data)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hw)
    _ = _ := by rw [hKcast]; simp only [mul_assoc]

end

end MeyerGeneralProblem
