module

public import MeyerGeneralProblem.Sampling.CanonicalFinitePrefixBound
public import MeyerGeneralProblem.Sampling.CanonicalPrefixGlobalTail
public import MeyerGeneralProblem.Sampling.CanonicalGraphSampler

@[expose] public section

/-!
# Unconditional canonical graph samplers from central and tail bounds

This module composes the exact finite complement of the
original-prefix tail, its forward finite-family estimate, and the global
two-ray tail estimate.  The resulting physical and Fourier samplers depend
only on the geometric hypotheses, not on per-vector energy assumptions.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set MeasureTheory
open scoped ENNReal FourierTransform

attribute [local instance] Classical.propDecidable

namespace BoundedClusterOrder

variable (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
  (ho : BoundedClusterOrder S.signedSquareImage d q)

/-- The full real weighted original-prefix energy is summable and uniformly
bounded.  The finite part is exactly the complement of the analytic tail;
there is no intermediate radius and hence no omitted annulus. -/
theorem exists_canonicalPhysicalPrefixRealEnergy_bound
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k) :
    ∃ A : ℝ, 0 < A ∧
      ∀ anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
          Fin (ho.clusterSize C),
      ∀ v : KNSGraphSpace k,
        Summable (ho.canonicalPhysicalPrefixBlockEnergy S k (by omega) anchor v) ∧
        ho.canonicalPhysicalPrefixRealEnergy S k (by omega) anchor v ≤
          A * ‖v‖ ^ 2 := by
  let hk : 1 ≤ k := by omega
  let F : Finset (CanonicalClusterIndex S.signedSquareImage d) :=
    (CanonicalPrefixTail.finite_not_original_prefix_tail ho hd).toFinset
  obtain ⟨Ac, hAc, hcentral⟩ :=
    ho.exists_finite_canonicalPrefixData_representative_energy_bound S k hk F
  obtain ⟨At, hAt, htail⟩ :=
    CanonicalPrefixTail.exists_weighted_original_prefix_tail_energy_bound ho hd hq
  refine ⟨Ac + At, add_pos hAc hAt, ?_⟩
  intro anchor v
  let E : CanonicalClusterIndex S.signedSquareImage d → ℝ :=
    ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v
  let P : CanonicalClusterIndex S.signedSquareImage d → Prop := fun C ↦
    ho.exteriorGroup C ∧ 4 ≤ |ho.signedAnchorCoordinate C|
  have htail' : Summable (fun C => if P C then E C else 0) ∧
      (∑' C, if P C then E C else 0) ≤ At * ‖v‖ ^ 2 := by
    simpa only [P, E, canonicalPhysicalPrefixBlockEnergy,
      canonicalPhysicalPrefixLinearMap_apply] using htail anchor v
  have hcentral' :
      ∑ C ∈ F, E C ≤ Ac * ‖v‖ ^ 2 := by
    simpa only [E, canonicalPhysicalPrefixBlockEnergy,
      canonicalPhysicalPrefixLinearMap_apply] using hcentral anchor v
  have hfiniteSupport :
      Function.HasFiniteSupport (fun C => if ¬ P C then E C else 0) := by
    refine (CanonicalPrefixTail.finite_not_original_prefix_tail ho hd).subset ?_
    intro C hC
    change ¬ P C
    intro hP
    change (if ¬ P C then E C else 0) ≠ 0 at hC
    exact hC (by simp [hP])
  have hcentralSummable : Summable (fun C => if ¬ P C then E C else 0) :=
    summable_of_hasFiniteSupport hfiniteSupport
  have hcentralTsum :
      (∑' C, if ¬ P C then E C else 0) = ∑ C ∈ F, E C := by
    rw [tsum_eq_sum (s := F)]
    · apply Finset.sum_congr rfl
      intro C hC
      have hnP : ¬ P C := by
        have hmem : C ∈ {C : CanonicalClusterIndex S.signedSquareImage d |
            ¬ (ho.exteriorGroup C ∧ 4 ≤ |ho.signedAnchorCoordinate C|)} := by
          simpa only [F, Set.Finite.mem_toFinset] using hC
        exact hmem
      simp [hnP]
    · intro C hC
      have hP : P C := by
        by_contra hnP
        apply hC
        have hmem : C ∈ {C : CanonicalClusterIndex S.signedSquareImage d |
            ¬ (ho.exteriorGroup C ∧ 4 ≤ |ho.signedAnchorCoordinate C|)} := by
          change ¬ (ho.exteriorGroup C ∧ 4 ≤ |ho.signedAnchorCoordinate C|) at hnP
          exact hnP
        simpa only [F, Set.Finite.mem_toFinset] using hmem
      simp [hP]
  have hsum : Summable E := by
    have hadd := htail'.1.add hcentralSummable
    refine hadd.congr ?_
    intro C
    by_cases hP : P C <;> simp [hP]
  refine ⟨by simpa only [E] using hsum, ?_⟩
  change (∑' C, E C) ≤ (Ac + At) * ‖v‖ ^ 2
  calc
    (∑' C, E C) =
        (∑' C, if P C then E C else 0) +
          (∑' C, if ¬ P C then E C else 0) := by
      rw [← htail'.1.tsum_add hcentralSummable]
      apply tsum_congr
      intro C
      by_cases hP : P C <;> simp [hP]
    _ ≤ At * ‖v‖ ^ 2 + Ac * ‖v‖ ^ 2 := by
      rw [hcentralTsum]
      exact add_le_add htail'.2 hcentral'
    _ = (Ac + At) * ‖v‖ ^ 2 := by ring

/-- One geometry-dependent full-energy constant, chosen once and before the
anchor and graph vector. -/
def canonicalPhysicalPrefixBoundConstant
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k) : ℝ :=
  (ho.exists_canonicalPhysicalPrefixRealEnergy_bound S hd hq).choose

theorem canonicalPhysicalPrefixBoundConstant_pos
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k) :
    0 < ho.canonicalPhysicalPrefixBoundConstant S hd hq :=
  (ho.exists_canonicalPhysicalPrefixRealEnergy_bound S hd hq).choose_spec.1

theorem summable_canonicalPhysicalPrefixBlockEnergy
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k) :
    Summable (ho.canonicalPhysicalPrefixBlockEnergy S k (by omega) anchor v) :=
  (ho.exists_canonicalPhysicalPrefixRealEnergy_bound S hd hq).choose_spec.2
    anchor v |>.1

theorem canonicalPhysicalPrefixRealEnergy_le
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k) :
    ho.canonicalPhysicalPrefixRealEnergy S k (by omega) anchor v ≤
      ho.canonicalPhysicalPrefixBoundConstant S hd hq * ‖v‖ ^ 2 :=
  (ho.exists_canonicalPhysicalPrefixRealEnergy_bound S hd hq).choose_spec.2
    anchor v |>.2

/-- The physical canonical sampler obtained from the unconditional full
energy theorem.  Its inputs contain no per-vector summability or bound
assumptions. -/
def canonicalPhysicalSamplerBounded
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C)) :
    KNSGraphSpace k →L[ℂ] ho.CanonicalGraphData :=
  ho.canonicalPhysicalSampler S k (by omega) anchor
    (ho.canonicalPhysicalPrefixBoundConstant S hd hq)
    (ho.canonicalPhysicalPrefixBoundConstant_pos S hd hq).le
    (ho.summable_canonicalPhysicalPrefixBlockEnergy S hd hq anchor)
    (ho.canonicalPhysicalPrefixRealEnergy_le S hd hq anchor)

@[simp] theorem canonicalPhysicalSamplerBounded_apply_coord
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k)
    (C : CanonicalClusterIndex S.signedSquareImage d)
    (j : Fin (ho.clusterSize C)) :
    ho.canonicalPhysicalSamplerBounded S hd hq anchor v C j =
      (ho.canonicalGraphWeight k anchor C : ℂ) *
        ho.canonicalPrefixData
          (S.physicalSignedSquarePullbackMap
            (KNSGraphSpace.representative k v)) C j := rfl

theorem norm_canonicalPhysicalSamplerBounded_le
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k) :
    ‖ho.canonicalPhysicalSamplerBounded S hd hq anchor v‖ ≤
      Real.sqrt (ho.canonicalPhysicalPrefixBoundConstant S hd hq) * ‖v‖ :=
  ho.norm_canonicalPhysicalSampler_le S k (by omega) anchor
    (ho.canonicalPhysicalPrefixBoundConstant S hd hq)
    (ho.canonicalPhysicalPrefixBoundConstant_pos S hd hq).le
    (ho.summable_canonicalPhysicalPrefixBlockEnergy S hd hq anchor)
    (ho.canonicalPhysicalPrefixRealEnergy_le S hd hq anchor) v

theorem canonicalGraphDecode_canonicalPhysicalSamplerBounded
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k) :
    ho.canonicalGraphDecode k anchor
        (ho.canonicalPhysicalSamplerBounded S hd hq anchor v) =
      ho.canonicalPhysicalPrefixLinearMap S k (by omega) v :=
  ho.canonicalGraphDecode_canonicalPhysicalSampler S k (by omega) anchor
    (ho.canonicalPhysicalPrefixBoundConstant S hd hq)
    (ho.canonicalPhysicalPrefixBoundConstant_pos S hd hq).le
    (ho.summable_canonicalPhysicalPrefixBlockEnergy S hd hq anchor)
    (ho.canonicalPhysicalPrefixRealEnergy_le S hd hq anchor) v

/-- The Fourier canonical sampler obtained by precomposing the unconditional
physical sampler with the genuine graph Fourier isometric equivalence. -/
def canonicalFourierSamplerBounded
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C)) :
    KNSGraphSpace k →L[ℂ] ho.CanonicalGraphData :=
  ho.canonicalFourierSampler S k (by omega) anchor
    (ho.canonicalPhysicalPrefixBoundConstant S hd hq)
    (ho.canonicalPhysicalPrefixBoundConstant_pos S hd hq).le
    (ho.summable_canonicalPhysicalPrefixBlockEnergy S hd hq anchor)
    (ho.canonicalPhysicalPrefixRealEnergy_le S hd hq anchor)

@[simp] theorem canonicalFourierSamplerBounded_apply_coord
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k)
    (C : CanonicalClusterIndex S.signedSquareImage d)
    (j : Fin (ho.clusterSize C)) :
    ho.canonicalFourierSamplerBounded S hd hq anchor v C j =
      (ho.canonicalGraphWeight k anchor C : ℂ) *
        ho.canonicalPrefixData
          (S.physicalSignedSquarePullbackMap
            (KNSGraphSpace.representative k
              (KNSGraphSpace.fourier k v))) C j := rfl

theorem norm_canonicalFourierSamplerBounded_le
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k) :
    ‖ho.canonicalFourierSamplerBounded S hd hq anchor v‖ ≤
      Real.sqrt (ho.canonicalPhysicalPrefixBoundConstant S hd hq) * ‖v‖ :=
  ho.norm_canonicalFourierSampler_le S k (by omega) anchor
    (ho.canonicalPhysicalPrefixBoundConstant S hd hq)
    (ho.canonicalPhysicalPrefixBoundConstant_pos S hd hq).le
    (ho.summable_canonicalPhysicalPrefixBlockEnergy S hd hq anchor)
    (ho.canonicalPhysicalPrefixRealEnergy_le S hd hq anchor) v

/-- On the already-constructed interpolation range, the unconditional
physical sampler is the exact left inverse (and the interpolator the right
inverse). -/
theorem canonicalPhysicalSamplerBounded_canonicalGraphInterpolator
    (N k : ℕ) (hk : 2 ≤ k) (hq : q + 1 ≤ k)
    {B : ℝ} (hB : 1 ≤ B)
    (hd : 0 < d) (hdiam : (q : ℝ) * d ≤ B) (b₀ : ℤ)
    (hpositive : ∀ j : ℤ, b₀ ≤ j →
      (orientedBlockPoints S.signedSquareImage B 1 j).ncard ≤ N)
    (hnegative : ∀ j : ℤ, b₀ ≤ j →
      (orientedBlockPoints S.signedSquareImage B (-1) j).ncard ≤ N)
    (start : ℕ) (hstart : 3 ≤ start) (hstart₀ : b₀ + 1 ≤ (start : ℤ))
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (y : ho.CanonicalGraphData) :
    ho.canonicalPhysicalSamplerBounded S hd hq anchor
        (S.canonicalGraphInterpolator ho N k hk hB hd hdiam b₀
          hpositive hnegative start hstart hstart₀ anchor y) = y :=
  ho.canonicalPhysicalSampler_canonicalGraphInterpolator S N k hk hB hd hdiam b₀
    hpositive hnegative start hstart hstart₀ anchor
    (ho.canonicalPhysicalPrefixBoundConstant S hd hq)
    (ho.canonicalPhysicalPrefixBoundConstant_pos S hd hq).le
    (ho.summable_canonicalPhysicalPrefixBlockEnergy S hd hq anchor)
    (ho.canonicalPhysicalPrefixRealEnergy_le S hd hq anchor) y

end BoundedClusterOrder

end

end MeyerGeneralProblem
