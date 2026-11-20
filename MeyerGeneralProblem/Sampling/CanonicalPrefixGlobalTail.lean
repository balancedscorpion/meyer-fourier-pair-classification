module

public import MeyerGeneralProblem.Sampling.CanonicalPrefixTail

@[expose] public section

/-!
# Global two-ray original-prefix tail energy

This module constructs the genuine global tail estimate. The tail is the
exact intersection needed by the reciprocal cluster theorem: whole exterior
groups whose actual signed anchor has modulus at least four.  The negative
ray retains the original increasing signed node order; only the smooth chart
argument is reflected.
-/

namespace MeyerGeneralProblem.CanonicalPrefixTail
noncomputable section

open Set MeasureTheory
open scoped ContDiff BigOperators

attribute [local instance] Classical.propDecidable

private theorem exists_reflected_iteratedDeriv_memLp_norm_eq
    {f : ℝ → ℂ} (j : ℕ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h : MemLp (iteratedDeriv j f) 2) :
    ∃ hf : MemLp (iteratedDeriv j (fun x => f (ε*x))) 2,
      ‖hf.toLp‖ = ‖h.toLp‖ := by
  rcases hε with rfl | rfl
  · let hp : MemLp (iteratedDeriv j (fun x => f (1*x))) 2 := by
      simpa only [one_mul] using h
    refine ⟨hp, ?_⟩
    rw [Lp.norm_toLp, Lp.norm_toLp]
    simp only [one_mul]
  · let mp := Measure.measurePreserving_neg (volume : Measure ℝ)
    let hn₀ := (h.comp_measurePreserving mp).const_smul ((-1 : ℝ)^j)
    let hn : MemLp (iteratedDeriv j (fun x => f ((-1)*x))) 2 := by
      convert hn₀ using 1
      funext x
      simpa only [neg_one_mul, Function.comp_apply, Pi.smul_apply] using
        (iteratedDeriv_comp_neg j f x)
    refine ⟨hn, ?_⟩
    rw [Lp.norm_toLp, Lp.norm_toLp]
    apply congrArg ENNReal.toReal
    calc
      eLpNorm (iteratedDeriv j (fun x => f ((-1)*x))) 2 volume =
          eLpNorm ((iteratedDeriv j f) ∘ Neg.neg) 2 volume := by
        apply eLpNorm_congr_norm_ae
        filter_upwards [] with x
        rw [show (fun x => f ((-1)*x)) = fun x => f (-x) by
          funext y; rw [neg_one_mul], iteratedDeriv_comp_neg]
        simp only [Function.comp_apply, norm_smul, Real.norm_eq_abs, abs_pow,
          abs_neg, abs_one, one_pow, one_mul]
      _ = eLpNorm (iteratedDeriv j f) 2 volume :=
        eLpNorm_comp_measurePreserving (p := (2 : ENNReal)) h.aestronglyMeasurable mp

/-- Finite Cauchy, twice: each prefix has at most `q` terms and there are at
most `q` prefixes.  This is the exact `q²` combinatorial loss. -/
private theorem sum_prefix_bound_sq_le_q_sq_mul_sum_sq
    {n q : ℕ} (hn : n ≤ q) (M : ℝ)
    (a : ℕ → ℝ)
    (b : Fin n → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hbound : ∀ j : Fin n, b j ≤ M * ∑ r ∈ Finset.range (j.val+1), a r) :
    ∑ j, b j ^ 2 ≤
      M^2 * (q : ℝ)^2 * ∑ r ∈ Finset.range n, a r ^ 2 := by
  have hone (j : Fin n) :
      b j ^ 2 ≤ M^2 * (q : ℝ) * ∑ r ∈ Finset.range n, a r ^ 2 := by
    have hjn : j.val+1 ≤ n := by omega
    have hjq : j.val+1 ≤ q := hjn.trans hn
    have hb2 := pow_le_pow_left₀ (hb j) (hbound j) 2
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j.val+1))
      (f := fun r => a r)
    have hsub : ∑ r ∈ Finset.range (j.val+1), (a r)^2 ≤
        ∑ r ∈ Finset.range n, a r^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjn)
      intro i hi hnot
      exact sq_nonneg _
    calc
      b j^2 ≤ (M * ∑ r ∈ Finset.range (j.val+1), a r)^2 := hb2
      _ = M^2 * (∑ r ∈ Finset.range (j.val+1), a r)^2 := by ring
      _ ≤ M^2 * ((j.val+1 : ℕ) : ℝ) *
          ∑ r ∈ Finset.range (j.val+1), (a r)^2 := by
        simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one, mul_assoc] using
          mul_le_mul_of_nonneg_left hcs (sq_nonneg M)
      _ ≤ M^2 * (q : ℝ) * ∑ r ∈ Finset.range n, a r^2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hjq) (sq_nonneg M)) hsub
          (Finset.sum_nonneg (fun r _ => sq_nonneg _))
          (mul_nonneg (sq_nonneg M) (by positivity))
  calc
    ∑ j, b j^2 ≤
        ∑ _j : Fin n, M^2 * (q : ℝ) * ∑ r ∈ Finset.range n, a r^2 :=
      Finset.sum_le_sum (fun j _ => hone j)
    _ = (n : ℝ) * (M^2 * (q : ℝ) * ∑ r ∈ Finset.range n, a r^2) := by
      simp
    _ ≤ (q : ℝ) * (M^2 * (q : ℝ) * ∑ r ∈ Finset.range n, a r^2) := by
      gcongr
    _ = M^2 * (q : ℝ)^2 * ∑ r ∈ Finset.range n, a r^2 := by ring

/-- The complement of the exact analytic tail is a finite family of whole
canonical clusters.  Equivalently, the sufficient one-line threshold is
`max 4 (q*d+1) < |signedAnchorCoordinate C|`; keeping the conjunction below
matches the two inputs of the cluster theorem without concealing either. -/
theorem finite_not_original_prefix_tail
    {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ}
    (ho : BoundedClusterOrder S.signedSquareImage d q) (hd : 0<d) :
    {C : CanonicalClusterIndex S.signedSquareImage d |
      ¬(ho.exteriorGroup C ∧ 4≤|ho.signedAnchorCoordinate C|)}.Finite := by
  apply (ho.finite_signedAnchorCoordinate_band hd
    (max 4 ((q:ℝ)*d+1))).subset
  intro C hC
  change |ho.signedAnchorCoordinate C| ≤ max 4 ((q:ℝ)*d+1)
  by_cases hext : ho.exteriorGroup C
  · have hfour : ¬ 4≤|ho.signedAnchorCoordinate C| := fun h => hC ⟨hext,h⟩
    exact (le_of_lt (lt_of_not_ge hfour)).trans (le_max_left _ _)
  · have hband : |ho.signedAnchorCoordinate C| ≤ (q:ℝ)*d+1 := by
      simpa only [BoundedClusterOrder.exteriorGroup, not_lt] using hext
    exact hband.trans (le_max_right _ _)

/-- The exact genuine two-ray tail of the actual canonical prefix samples is
summable, with a bound fixed before the arbitrary graph anchor and graph
vector.  No inverse internal gap occurs. -/
theorem exists_weighted_original_prefix_tail_energy_bound
    {S : LocallyFiniteCarrier} {d : ℝ} {q k : ℕ}
    (ho : BoundedClusterOrder S.signedSquareImage d q) (hd : 0<d)
    (hq : q+1≤k) :
    ∃ A>0, ∀
      (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
      (v : KNSGraphSpace k),
      Summable (fun C : CanonicalClusterIndex S.signedSquareImage d =>
        if ho.exteriorGroup C ∧ 4≤|ho.signedAnchorCoordinate C| then
          (1+Real.sqrt |ho.realClusterNode C (anchor C)|)^(2*k-1) *
            ∑ j, ‖ho.canonicalPrefixData
              (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j‖^2
        else 0) ∧
      (∑' C : CanonicalClusterIndex S.signedSquareImage d,
        if ho.exteriorGroup C ∧ 4≤|ho.signedAnchorCoordinate C| then
          (1+Real.sqrt |ho.realClusterNode C (anchor C)|)^(2*k-1) *
            ∑ j, ‖ho.canonicalPrefixData
              (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j‖^2
        else 0) ≤ A*‖v‖^2 := by
  obtain ⟨M,hM,B,hB,hchart,hprefix⟩ :=
    exists_original_prefix_tail_chart_package ho hd hq
  let A : ℝ := 1 + M^2*(q:ℝ)^2 *
    (2*((q:ℝ)*(2*d⁻¹+d)*B))
  have hA : 0<A := by
    dsimp [A]
    positivity
  refine ⟨A,hA,?_⟩
  intro anchor v
  let chart : ℝ → ℝ → ℂ := fun ε s =>
    signedSquareCutoffChart k 2 ε (KNSGraphSpace.representative k v) (ε*s)
  let E : CanonicalClusterIndex S.signedSquareImage d → ℝ := fun C =>
    if ho.exteriorGroup C ∧ 4≤|ho.signedAnchorCoordinate C| then
      (1+Real.sqrt |ho.realClusterNode C (anchor C)|)^(2*k-1) *
        ∑ j, ‖ho.canonicalPrefixData
          (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j‖^2
    else 0
  let F : ℝ → CanonicalClusterIndex S.signedSquareImage d → ℝ := fun ε C =>
    ∑ j : Fin (ho.clusterSize C),
      ‖analyticDividedDifference (finiteNodeSequence (ho.realClusterNode C)) j (chart ε)‖^2
  have hsample (ε : ℝ) (hε : ε^2=1) :
      Summable (F ε) ∧
      (∑' C, F ε C) ≤ (q:ℝ)*(2*d⁻¹+d)*B*‖v‖^2 := by
    have hsign : ε=1 ∨ ε=-1 := sq_eq_one_iff.mp hε
    have hcont : ContDiff ℝ q (chart ε) := by
      dsimp [chart]
      exact (hchart v ε hε).1.comp (by fun_prop)
    have href (r : ℕ) (hr : r≤q) :
        ∃ hJ : MemLp (iteratedDeriv r (chart ε)) 2,
          ‖hJ.toLp‖^2≤B*‖v‖^2 := by
      obtain ⟨hD,hDbound⟩ := (hchart v ε hε).2 r hr
      obtain ⟨hJ,hJnorm⟩ :=
        exists_reflected_iteratedDeriv_memLp_norm_eq r ε hsign hD
      refine ⟨hJ,?_⟩
      rw [hJnorm]
      exact hDbound
    let hL2 (r : ℕ) (hr : r≤q) : MemLp (iteratedDeriv r (chart ε)) 2 :=
      Classical.choose (href r hr)
    have hL2bound (r : ℕ) (hr : r≤q) :
        ‖(hL2 r hr).toLp‖^2≤B*‖v‖^2 :=
      Classical.choose_spec (href r hr)
    have hs := canonical_grouped_sobolev_sampling_upper
      S.signedSquareImage ho hd hcont hL2
    refine ⟨?_,hs.2.trans ?_⟩
    · simpa only [F] using hs.1
    calc
      ∑ j : Fin q, (2*d⁻¹*‖(hL2 j j.isLt.le).toLp‖^2+
          d*‖(hL2 (j+1) (by omega)).toLp‖^2) ≤
          ∑ _j : Fin q, (2*d⁻¹+d)*(B*‖v‖^2) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj₀ := hL2bound j j.isLt.le
        have hj₁ := hL2bound (j+1) (by omega)
        have hd₀ : 0≤2*d⁻¹ := by positivity
        nlinarith
      _ = (q:ℝ)*(2*d⁻¹+d)*B*‖v‖^2 := by
        simp
        ring
  have hp := hsample 1 (by norm_num)
  have hn := hsample (-1) (by norm_num)
  have hcluster (C : CanonicalClusterIndex S.signedSquareImage d) :
      E C ≤ M^2*(q:ℝ)^2*(F 1 C+F (-1) C) := by
    by_cases htail : ho.exteriorGroup C ∧ 4≤|ho.signedAnchorCoordinate C|
    · rw [show E C =
          (1+Real.sqrt |ho.realClusterNode C (anchor C)|)^(2*k-1) *
            ∑ j, ‖ho.canonicalPrefixData
              (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j‖^2 by
          simp [E, htail]]
      have hweight :
          (1+Real.sqrt |ho.realClusterNode C (anchor C)|)^(2*k-1) *
              ∑ j, ‖ho.canonicalPrefixData
                (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j‖^2 =
            ∑ j, ‖(ho.canonicalGraphWeight k anchor C : ℂ) *
              ho.canonicalPrefixData
                (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (ho.canonicalGraphWeight_pos k anchor C), mul_pow,
          ho.canonicalGraphWeight_sq]
      rw [hweight]
      have hcauchy := sum_prefix_bound_sq_le_q_sq_mul_sum_sq
        (ho.clusterSize_le C) M
        (fun r => ‖analyticDividedDifference
          (finiteNodeSequence (ho.realClusterNode C)) r (chart (ho.exteriorRay C))‖)
        (fun j => ‖(ho.canonicalGraphWeight k anchor C : ℂ) *
          ho.canonicalPrefixData
            (S.physicalSignedSquarePullbackMap (KNSGraphSpace.representative k v)) C j‖)
        (fun j => norm_nonneg _)
        (hprefix anchor v C htail.1 htail.2)
      rw [← Fin.sum_univ_eq_sum_range] at hcauchy
      rcases sq_eq_one_iff.mp (ho.exteriorRay_sq C) with hray | hray
      · rw [hray] at hcauchy
        exact hcauchy.trans (by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg M) (sq_nonneg (q:ℝ)))
          exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => sq_nonneg _)))
      · rw [hray] at hcauchy
        exact hcauchy.trans (by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg M) (sq_nonneg (q:ℝ)))
          exact le_add_of_nonneg_left (Finset.sum_nonneg (fun j _ => sq_nonneg _)))
    · rw [show E C=0 by simp [E,htail]]
      positivity
  let G : CanonicalClusterIndex S.signedSquareImage d → ℝ := fun C =>
    M^2*(q:ℝ)^2*(F 1 C+F (-1) C)
  have hG : Summable G := by
    dsimp [G]
    exact (hp.1.add hn.1).mul_left (M^2*(q:ℝ)^2)
  have hE0 (C : CanonicalClusterIndex S.signedSquareImage d) : 0≤E C := by
    dsimp [E]
    split_ifs
    · positivity
    · rfl
  have hE : Summable E :=
    Summable.of_nonneg_of_le hE0 (fun C => by simpa only [G] using hcluster C) hG
  refine ⟨hE,?_⟩
  have htsum := Summable.tsum_le_tsum
    (fun C => by simpa only [G] using hcluster C) hE hG
  calc
    ∑' C, E C ≤ ∑' C, G C := htsum
    _ = M^2*(q:ℝ)^2*((∑' C, F 1 C)+(∑' C, F (-1) C)) := by
      rw [show (∑' C, G C) = M^2*(q:ℝ)^2*∑' C, (F 1 C+F (-1) C) by
        dsimp [G]
        rw [tsum_mul_left]]
      rw [hp.1.tsum_add hn.1]
    _ ≤ M^2*(q:ℝ)^2*
        (2*((q:ℝ)*(2*d⁻¹+d)*B*‖v‖^2)) := by
      gcongr
      nlinarith [hp.2,hn.2]
    _ ≤ A*‖v‖^2 := by
      dsimp [A]
      have hv : 0≤‖v‖^2 := sq_nonneg _
      ring_nf
      nlinarith

end
end MeyerGeneralProblem.CanonicalPrefixTail
