module

public import MeyerGeneralProblem.Sampling.GroupedCompactKernelBounds
public import MeyerGeneralProblem.Sampling.GroupedDensityColouring
public import MeyerGeneralProblem.Interpolation.CanonicalDataValues
public import MeyerGeneralProblem.Distribution.BroadCauchyPairing

@[expose] public section

/-!
# Uniform Newton moments of the original atomic record

Finite grouped interpolation yields spectral tests in one fixed compact
window. The raw kernel mass bounds these tests in the spectral supremum
norm and bounds their physical Fourier images in Schwartz seminorms for
one fixed target cluster. Compact physical cutoffs recover the exact
original Newton moment in the limit.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology

/-- Expanding compact cutoffs approximate on every tempered distribution
uniformly for a family with bounded Schwartz seminorms. -/
theorem tendsto_norm_compactSchwartzApproximation_sub_apply_zero
    (T : TemperedDistribution ℝ ℂ) (f : ℕ → SchwartzMap ℝ ℂ)
    (hF : ∀ k j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N, SchwartzMap.seminorm ℂ k j (f N) ≤ C) :
    Tendsto (fun N => ‖T (compactSchwartzApproximation N (f N) - f N)‖) atTop (𝓝 0) := by
  obtain ⟨q, _, C, hC, hT⟩ := exists_hasSchwartzOrderBound T
  choose B hB hb using hF
  let I : Finset (ℕ × ℕ) := Finset.Iic (q, q)
  let b (i : ℕ × ℕ) :=
    ∑ j ∈ Finset.range (i.2 + 1), (i.2.choose j : ℝ) *
      if j = 0 then 2 * B (i.1 + 1) i.2
      else SchwartzMap.seminorm ℂ 0 j compactSchwartzCutoff * B i.1 (i.2 - j)
  have hb0 (i : ℕ × ℕ) : 0 ≤ b i := by
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (Nat.cast_nonneg _)
    split_ifs
    · exact mul_nonneg (by norm_num) (hB _ _)
    · exact mul_nonneg (apply_nonneg _ _) (hB _ _)
  have hbnd (i : ℕ × ℕ) (N : ℕ) : compactSchwartzApproximationBound i.1 i.2 (f N) ≤ b i := by
    unfold compactSchwartzApproximationBound b
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    split_ifs
    · exact mul_le_mul_of_nonneg_left (hb _ _ _) (by norm_num)
    · exact mul_le_mul_of_nonneg_left (hb _ _ _) (apply_nonneg _ _)
  let M := ∑ i ∈ I, b i
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => hb0 i)
  have hUpper (N : ℕ) :
      ‖T (compactSchwartzApproximation N (f N) - f N)‖ ≤ compactSchwartzCutoffScale N * (C * M) := by
    have hscale := (compactSchwartzCutoffScale_pos N).le
    have hsup : (I.sup (schwartzSeminormFamily ℂ ℝ ℂ))
        (compactSchwartzApproximation N (f N) - f N) ≤ compactSchwartzCutoffScale N * M := by
      refine Seminorm.finset_sup_apply_le (mul_nonneg hscale hM) (fun i hi => ?_)
      exact (compactSchwartzApproximation_seminorm_le N i.1 i.2 (f N)).trans
        (mul_le_mul_of_nonneg_left ((hbnd i N).trans
          (Finset.single_le_sum (fun j _ => hb0 j) hi)) hscale)
    exact (hT _).trans ((mul_le_mul_of_nonneg_left hsup hC).trans_eq (by ring))
  apply squeeze_zero (fun _ => norm_nonneg _) hUpper
  simpa only [zero_mul] using compactSchwartzCutoffScale_tendsto.mul_const (C * M)


/-- A compact test with zero values off a given finite atom set is
evaluated using precisely that finite set of original coefficients. -/
theorem atomicOnCarrier_apply_eq_sum_of_compact_of_zero_off_finset
    (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (f : SchwartzMap ℝ ℂ) (hfc : HasCompactSupport (f : ℝ → ℂ))
    (E : Finset A.subtype) (hE : ∀ x : A.subtype, x ∉ E → f x = 0) :
    T f = ∑ x ∈ E, T (A.isolationSchwartz x) * f x := by
  classical
  obtain ⟨F, hF, hSum⟩ := atomicOnCarrier_isLocallyAtomicCoefficientFamily A T hT f hfc
  calc
    _ = ∑ x ∈ F, T (A.isolationSchwartz x) * f x := hSum
    _ = ∑ x ∈ F ∪ E, T (A.isolationSchwartz x) * f x := by
      apply Finset.sum_subset Finset.subset_union_left
      intro x _ hx
      rw [hF x hx, mul_zero]
    _ = _ := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro x _ hx
      rw [hE x hx, mul_zero]

/-- Absolute mass of the original atoms in a fixed finite closed window. -/
def originalClosedWindowMass (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (W : ℝ) : ℝ :=
  ∑ x ∈ ((A.finite_inter_Icc (-W) W).preimage (Set.injOn_of_injective Subtype.val_injective)).toFinset,
    ‖T (A.isolationSchwartz x)‖

theorem originalClosedWindowMass_nonneg (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (W : ℝ) :
    0 ≤ originalClosedWindowMass A T W :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- A test in the fixed closed window uses only the finite original
spectral mass in that window. -/
theorem norm_atomicOnCarrier_apply_le_of_window (A : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (W M : ℝ) (f : SchwartzMap ℝ ℂ) (hf : Function.support f ⊆ Icc (-W) W)
    (hM : ∀ x, ‖f x‖ ≤ M) : ‖T f‖ ≤ originalClosedWindowMass A T W * M := by
  classical
  let E := (A.finite_inter_Icc (-W) W).preimage (f := fun x : A.subtype => (x : ℝ))
    (Set.injOn_of_injective Subtype.val_injective)
  have hfc : HasCompactSupport (f : ℝ → ℂ) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => by by_contra h; exact hx (hf h))
  rw [atomicOnCarrier_apply_eq_sum_of_compact_of_zero_off_finset A T hT f hfc E.toFinset]
  · calc
      _ ≤ ∑ x ∈ E.toFinset, ‖T (A.isolationSchwartz x) * f x‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ E.toFinset, ‖T (A.isolationSchwartz x)‖ * M := by
        apply Finset.sum_le_sum
        intro x _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; rfl
  · intro x hx
    by_contra hn
    exact hx (E.mem_toFinset.mpr ⟨x.property, hf hn⟩)

/-- Supported interpolation, for every finite clustered family on one carrier,
with one bound for the squared integral norms of all raw kernels. -/
def HasUniformFiniteGroupedFourierKernels (S : LocallyFiniteCarrier)
    (q : ℕ) (R d D C : ℝ) : Prop :=
  ∀ (N : ℕ) (size : Fin N → ℕ), (∀ g, size g ≤ q) →
  ∀ (nodes : (g : Fin N) → Fin (size g) → ℝ),
  (∀ g, Function.Injective (nodes g)) →
  (∀ g i, nodes g i ∈ S.carrier) →
  (∀ g i j, dist (nodes g i) (nodes g j) ≤ D) →
  (∀ g h, g ≠ h → ∀ i j, d ≤ |nodes g i - nodes h j|) →
  ∃ ρ : (g : Fin N) → Fin (size g) → ℝ → ℂ,
    (∀ g i, Integrable (ρ g i)) ∧
    (∀ g i, Function.support (ρ g i) ⊆ Set.Icc (-R) R) ∧
    (∀ g (i j : Fin (size g)), analyticDividedDifference (finiteNodeSequence (nodes g)) j
      (FourierTransform.fourier (ρ g i)) = if i = j then 1 else 0) ∧
    (∀ g h, g ≠ h → ∀ (i : Fin (size g)) (j : Fin (size h)),
      analyticDividedDifference (finiteNodeSequence (nodes h)) j
        (FourierTransform.fourier (ρ g i)) = 0) ∧
    ∀ g i, (∫ t : ℝ, ‖ρ g i t‖) ^ 2 ≤ C

/-- A common unit-window cap gives the same support and mass bounds for
finite grouped Fourier interpolation on every carrier with that cap. -/
theorem exists_uniform_finite_grouped_kernels_of_unit_window_cap
    (K q : ℕ) {d D : ℝ} (hd : 0 < d) (hD : 0 ≤ D) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧
      ∀ S : LocallyFiniteCarrier, (∀ x, windowCount S x 1 ≤ K) →
        HasUniformFiniteGroupedFourierKernels S q R d D C := by
  obtain ⟨C, hC, hkernels⟩ :=
    exists_uniform_supported_grouped_kernels_of_finite_colouring K q
      (b := 1) (r := 1) (L := 1) (by norm_num) (by norm_num) (by norm_num) hd hD (by norm_num)
  refine ⟨(K + 1 : ℕ) * (1 + q * 1), C, by positivity, hC, ?_⟩
  intro S hCap N size hSize nodes hNodes hMem hDiam hSep
  have hi := grouped_nodes_injective_of_intercluster_separation size nodes hNodes hd hSep
  obtain ⟨colour, hColour⟩ := exists_grouped_finite_colouring_of_uniform_windowCap
    (Nat.succ_pos K) (fun x => (hCap x).trans (Nat.le_succ _)) size nodes hi hMem
  exact hkernels N size hSize nodes hNodes hDiam hSep colour hColour

namespace BoundedClusterOrder

variable {A : LocallyFiniteCarrier} {d : ℝ} {q : ℕ} (ho : BoundedClusterOrder A d q)

/-- The polynomial dual to the selected canonical Newton coordinate. -/
def clusterNewtonPolynomial (C : CanonicalClusterIndex A d) (j : Fin (ho.clusterSize C)) :
    Polynomial ℂ :=
  newtonBasisPolynomial (fun i => (ho.realClusterNode C i : ℂ)) j

/-- A common group of compact spectral tests recovers each prescribed
Newton coordinate on any finite family of complete canonical clusters. -/
def HasUniformCompactNewtonTests (R η M : ℝ) (G : SchwartzMap ℝ ℂ) : Prop :=
  ∀ (E : Finset (CanonicalClusterIndex A d))
    (C : CanonicalClusterIndex A d) (j : Fin (ho.clusterSize C)),
    ∃ (v : SchwartzMap ℝ ℂ) (κ : ℝ → ℂ),
      Integrable κ ∧ (∫ t : ℝ, ‖κ t‖) ≤ M ∧
      ((v : ℝ → ℂ) = fourierKernelConvolution κ (fun t => G t * gramPhase (ho.clusterLower C) t)) ∧
      Function.support v ⊆ Icc (-(R + η)) (R + η) ∧
      (∀ i : Fin (ho.clusterSize C),
        (𝓕 (v : ℝ → ℂ)) (ho.realClusterNode C i) =
          (ho.clusterNewtonPolynomial C j).eval (ho.realClusterNode C i : ℂ)) ∧
      ∀ P ∈ E, P ≠ C → ∀ i : Fin (ho.clusterSize P), (𝓕 (v : ℝ → ℂ)) (ho.realClusterNode P i) = 0

/-- Correct and smooth the finite grouped kernels with constants depending
only on the geometric and raw kernel bounds, uniformly over carriers. -/
theorem exists_uniform_compact_newton_tests_of_finite_grouped_kernels
    (q : ℕ) {d R η C₀ : ℝ} (hd : 0 < d) (hη : 0 < η) (hC₀ : 0 < C₀) :
    ∃ (M : ℝ) (G : SchwartzMap ℝ ℂ), 0 ≤ M ∧ Function.support G ⊆ Icc (-η) η ∧
      ∀ (A : LocallyFiniteCarrier) (ho : BoundedClusterOrder A d q),
        HasUniformFiniteGroupedFourierKernels A q R d ((q : ℝ) * d) C₀ →
        ho.HasUniformCompactNewtonTests R η M G := by
  classical
  let D := (q : ℝ) * d
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨G, hGs, _, hGpos, hGfloor⟩ := exists_compact_positive_fourier_band_smoothing hη hD
  obtain ⟨_, M, _, hM, hCorrect⟩ :=
    exists_uniform_corrected_grouped_schwartz_kernels_with_convolution
      q G (R := R) hη hd hD hC₀ hGs hGpos hGfloor
  refine ⟨M, G, hM, hGs, ?_⟩
  intro A ho hRaw E C j
  let F := E.erase C
  let e := Fintype.equivFin ↥F
  let groups : Fin (Fintype.card ↥F + 1) → CanonicalClusterIndex A d :=
    Fin.cases C (fun i => (e.symm i).1)
  have hzero : groups 0 = C := rfl
  have hsucc (i : Fin (Fintype.card ↥F)) : groups i.succ = (e.symm i).1 := rfl
  have hne (i : Fin (Fintype.card ↥F)) : groups i.succ ≠ C :=
    (Finset.mem_erase.mp (e.symm i).2).1
  have hInj : Function.Injective groups := by
    intro i k h
    revert h
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases (fun _ => rfl) (fun k h => ?_) k
      exact (hne k (hzero.symm.trans h).symm).elim
    · refine Fin.cases (fun h => ?_) (fun k h => ?_) k
      · exact (hne i (h.trans hzero)).elim
      · rw [hsucc, hsucc] at h
        exact congrArg Fin.succ (e.symm.injective (Subtype.ext h))
  let size (g : Fin (Fintype.card ↥F + 1)) := ho.clusterSize (groups g)
  let nodes (g : Fin (Fintype.card ↥F + 1)) := ho.realClusterNode (groups g)
  let anchor (g : Fin (Fintype.card ↥F + 1)) := ho.clusterLower (groups g)
  have hSize (g) : size g ≤ q := ho.clusterSize_le _
  have hNodes (g) : Function.Injective (nodes g) := (ho.realClusterNode_strictMono _).injective
  have hMem (g) (i : Fin (size g)) : nodes g i ∈ A.carrier := ho.realClusterNode_mem _ _
  have hDiam (g) (i k : Fin (size g)) : dist (nodes g i) (nodes g k) ≤ D :=
    ho.realClusterNode_diameter hd _ _ _
  have hSep (g h) (hgh : g ≠ h) (i : Fin (size g)) (k : Fin (size h)) :
      d ≤ |nodes g i - nodes h k| := ho.realClusterNode_separated (hInj.ne hgh) i k
  have hAnchorSep : PairwiseFrequencySeparated anchor d :=
    fun g h hgh => hSep g h hgh ⟨0, ho.clusterSize_pos _⟩ ⟨0, ho.clusterSize_pos _⟩
  have hAnchor (g) (i : Fin (size g)) : |nodes g i - anchor g| ≤ D := by
    simpa only [anchor, BoundedClusterOrder.clusterLower, Real.dist_eq] using
      hDiam g i ⟨0, ho.clusterSize_pos _⟩
  obtain ⟨ρ, hρ, hs, ht, hoff, hm⟩ := hRaw _ size hSize nodes hNodes hMem hDiam hSep
  obtain ⟨v, hvs, hData, hOff, _, hConv⟩ :=
    hCorrect _ size hSize nodes hNodes anchor hAnchorSep hAnchor ρ hρ hs ht hoff hm
  let i₀ : Fin (size 0) := j
  obtain ⟨κ, hκ, _, hκM, hκv⟩ := hConv 0 i₀
  refine ⟨v 0 i₀, κ, hκ, hκM, hκv, hvs 0 i₀, ?_, ?_⟩
  · intro i
    exact values_eq_newtonBasis_of_initialData (nodes 0) (hNodes 0) _ i₀ (hData 0 i₀) i
  · intro P hP hPC
    obtain ⟨k, hk⟩ : ∃ k : Fin (Fintype.card ↥F), groups k.succ = P := by
      refine ⟨e ⟨P, Finset.mem_erase.mpr ⟨hPC, hP⟩⟩, ?_⟩
      rw [hsucc, e.symm_apply_apply]
    subst P
    intro i
    exact values_eq_of_initialData_eq (nodes k.succ) (hNodes k.succ) _ (fun _ => 0)
      (fun l => (hOff 0 k.succ (Fin.succ_ne_zero _).symm i₀ l).trans
        (initialData_zero (nodes k.succ) l).symm) i

/-- Strict upper density gives compact tests at the original gap threshold. -/
theorem exists_uniform_compact_newton_tests (hd : 0 < d) {W : ℝ} (hW : 0 < W)
    (hA : upperUniformBeurlingDensity A < ENNReal.ofReal (2 * W)) :
    ∃ (R η M : ℝ) (G : SchwartzMap ℝ ℂ), 0 < R ∧ 0 < η ∧ 0 ≤ M ∧
      Function.support G ⊆ Icc (-η) η ∧ ho.HasUniformCompactNewtonTests R η M G := by
  let D := (q : ℝ) * d
  obtain ⟨R, η, C₀, hR, hη, _, hC₀, hRaw⟩ :=
    exists_uniform_finite_grouped_kernels_of_upperDensity_lt A q hW hd
      (show 0 ≤ D by dsimp [D]; positivity) hA
  obtain ⟨M, G, hM, hGs, hTests⟩ :=
    exists_uniform_compact_newton_tests_of_finite_grouped_kernels q (R := R) hd hη hC₀
  exact ⟨R, η, M, G, hR, hη, hM, hGs, hTests A ho hRaw⟩

/-- The actual Newton moment of one original atomic cluster. The
coefficient pairing remains a finite sum even for a broad source. -/
def originalClusterNewtonMoment (T : TemperedDistribution ℝ ℂ)
    (C : CanonicalClusterIndex A d) (j : Fin (ho.clusterSize C)) : ℂ :=
  ∑ i : Fin (ho.clusterSize C), T (A.isolationSchwartz (ho.orderedClusterNode C i)) *
    (ho.clusterNewtonPolynomial C j).eval (ho.realClusterNode C i : ℂ)

/-- From a supplied compact test family, bound every original Newton
moment by a fixed multiple of the original opposite compact mass. -/
theorem originalClusterNewtonMoment_le_of_uniform_compact_newton_tests
    (B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hAt : AtomicOnCarrier A T) (hSpec : AtomicOnCarrier B (𝓕 T))
    {R η M : ℝ} {G : SchwartzMap ℝ ℂ}
    (hR : 0 < R) (hη : 0 < η) (hM : 0 ≤ M) (hGs : Function.support G ⊆ Icc (-η) η)
    (hTests : ho.HasUniformCompactNewtonTests R η M G)
    (C : CanonicalClusterIndex A d) (j : Fin (ho.clusterSize C)) :
    ‖ho.originalClusterNewtonMoment T C j‖ ≤
      originalClosedWindowMass B (𝓕 T) (R + η) * (M * SchwartzMap.seminorm ℂ 0 0 G) := by
  classical
  let W₀ := R + η
  let Q := SchwartzMap.seminorm ℂ 0 0 G
  let C₀ := originalClosedWindowMass B (𝓕 T) W₀ * (M * Q)
  have hQ : 0 ≤ Q := apply_nonneg _ _
  change ‖ho.originalClusterNewtonMoment T C j‖ ≤ C₀
  change ∀ E C j, _ at hTests
  obtain ⟨g, hg, hgs⟩ := exists_schwartz_modulation G hGs (ho.clusterLower C)
  have hgc : HasCompactSupport (g : ℝ → ℂ) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => by by_contra h; exact hx (hgs h))
  have hgNorm (x : ℝ) : ‖g x‖ ≤ Q := by
    rw [hg, norm_mul, norm_gramPhase, mul_one]
    exact SchwartzMap.norm_le_seminorm ℂ G x
  choose F hF using fun N : ℕ =>
    A.exists_finite_nonzero_values_of_hasCompactSupport (scaledCompactSchwartzCutoff N)
      (scaledCompactSchwartzCutoff_hasCompactSupport N)
  let classes (N : ℕ) := (F N).image (fun x => (ho.canonicalNodeEquiv.symm x).1)
  choose v κ hκ hκM hκv hvs htarget hoff using (fun N : ℕ => hTests (classes N) C j)
  let f (N : ℕ) : SchwartzMap ℝ ℂ := 𝓕 (v N)
  have hConv (N : ℕ) : (v N : ℝ → ℂ) = fourierKernelConvolution (κ N) g := by
    rw [hκv N, show (g : ℝ → ℂ) = (fun t => G t * gramPhase (ho.clusterLower C) t) from funext hg]
  have hUniformSeminorm (k n : ℕ) :
      ∃ H : ℝ, 0 ≤ H ∧ ∀ N, SchwartzMap.seminorm ℂ k n (f N) ≤ H := by
    obtain ⟨H, hH, hEstimate⟩ := exists_schwartz_seminorm_fourier_smoothedKernel_bound
      g hgc W₀ (add_nonneg hR.le hη.le) k n
    exact ⟨H * M, mul_nonneg hH hM, fun N =>
      (hEstimate (κ N) (hκ N) (v N) (hConv N) (hvs N)).trans (mul_le_mul_of_nonneg_left (hκM N) hH)⟩
  have hLimit := tendsto_norm_compactSchwartzApproximation_sub_apply_zero T f hUniformSeminorm
  have hBound (N : ℕ) : ‖T (f N)‖ ≤ C₀ := by
    change ‖(𝓕 T) (v N)‖ ≤ _
    apply norm_atomicOnCarrier_apply_le_of_window B (𝓕 T) hSpec W₀ (M * Q) (v N) (hvs N)
    intro x
    rw [show v N x = fourierKernelConvolution (κ N) g x from congrFun (hConv N) x]
    exact (norm_fourierKernelConvolution_le_mass_mul _ _ (hκ N) Q hgNorm x).trans
      (mul_le_mul_of_nonneg_right (hκM N) hQ)
  let E : Finset A.subtype := (Finset.univ : Finset (Fin (ho.clusterSize C))).image (ho.orderedClusterNode C)
  have hOff (N : ℕ) (x : A.subtype) (hx : x ∉ E) : compactSchwartzApproximation N (f N) x = 0 := by
    rw [compactSchwartzApproximation_apply]
    by_cases hxF : x ∈ F N
    · let y := ho.canonicalNodeEquiv.symm x
      have hy : ho.orderedClusterNode y.1 y.2 = x := ho.canonicalNodeEquiv.apply_symm_apply x
      have hY : y.1 ∈ classes N := Finset.mem_image_of_mem _ hxF
      have hYC : y.1 ≠ C := by
        intro hyC
        apply hx
        obtain ⟨P, i⟩ : (Σ P : CanonicalClusterIndex A d, Fin (ho.clusterSize P)) := y
        change P = C at hyC
        subst P
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hy⟩
      have hfZero : f N x = 0 := by
        rw [← hy]
        exact hoff N y.1 hY hYC y.2
      rw [hfZero, mul_zero]
    · rw [hF N x hxF, zero_mul]
  let Radius := ∑ i : Fin (ho.clusterSize C), |ho.realClusterNode C i|
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt Radius
  have hEventually : ∀ᶠ N : ℕ in atTop,
      T (compactSchwartzApproximation N (f N)) = ho.originalClusterNewtonMoment T C j := by
    filter_upwards [eventually_ge_atTop N₀] with N hN
    rw [atomicOnCarrier_apply_eq_sum_of_compact_of_zero_off_finset A T hAt _
      (compactSchwartzApproximation_hasCompactSupport N (f N)) E (hOff N)]
    unfold originalClusterNewtonMoment E
    rw [Finset.sum_image (fun i _ k _ h => (ho.orderedClusterNode C).injective h)]
    apply Finset.sum_congr rfl
    intro i _
    have hAbs : |ho.realClusterNode C i| ≤ (N : ℝ) + 1 := by
      have hb : |ho.realClusterNode C i| ≤ Radius :=
        Finset.single_le_sum (f := fun i => |ho.realClusterNode C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
      have hh : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    rw [compactSchwartzApproximation_apply, show scaledCompactSchwartzCutoff N (ho.orderedClusterNode C i) = 1 from
      scaledCompactSchwartzCutoff_eq_one N hAbs, one_mul]
    rw [show f N (ho.orderedClusterNode C i) = (ho.clusterNewtonPolynomial C j).eval
      (ho.realClusterNode C i : ℂ) from htarget N i]
  have hEstimate : ∀ᶠ N : ℕ in atTop,
      ‖ho.originalClusterNewtonMoment T C j‖ ≤
        C₀ + ‖T (compactSchwartzApproximation N (f N) - f N)‖ := by
    filter_upwards [hEventually] with N hEq
    rw [← hEq, map_sub]
    calc
      _ = ‖T (f N) + (T (compactSchwartzApproximation N (f N)) - T (f N))‖ := by
        rw [add_sub_cancel]
      _ ≤ ‖T (f N)‖ + ‖T (compactSchwartzApproximation N (f N)) - T (f N)‖ :=
        norm_add_le _ _
      _ ≤ _ := add_le_add (hBound N) le_rfl
  exact ge_of_tendsto (by simpa only [add_zero] using hLimit.const_add C₀) hEstimate

/-- Uniform original cluster moments follow from the finite mass of the
opposite record in one compact spectral window. -/
theorem exists_uniform_originalClusterNewtonMoment_bound
    (B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hAt : AtomicOnCarrier A T) (hSpec : AtomicOnCarrier B (𝓕 T))
    (hd : 0 < d) {W : ℝ} (hW : 0 < W)
    (hDensity : upperUniformBeurlingDensity A < ENNReal.ofReal (2 * W)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (C : CanonicalClusterIndex A d) (j : Fin (ho.clusterSize C)),
      ‖ho.originalClusterNewtonMoment T C j‖ ≤ C₀ := by
  obtain ⟨R, η, M, G, hR, hη, hM, hGs, hTests⟩ := ho.exists_uniform_compact_newton_tests hd hW hDensity
  exact ⟨_, mul_nonneg (originalClosedWindowMass_nonneg _ _ _)
    (mul_nonneg hM (apply_nonneg _ _)),
    ho.originalClusterNewtonMoment_le_of_uniform_compact_newton_tests B T hAt hSpec hR hη hM hGs hTests⟩

/-- The window and the moment estimate factor can be chosen for the entire
family of original records with the same unit-window and cluster caps. -/
theorem exists_uniform_originalClusterNewtonMoment_factor_of_unit_window_cap
    (K q : ℕ) {d : ℝ} (hd : 0 < d) :
    ∃ W C₀ : ℝ, 0 < W ∧ 0 ≤ C₀ ∧
      ∀ (A : LocallyFiniteCarrier) (ho : BoundedClusterOrder A d q),
        (∀ x, windowCount A x 1 ≤ K) →
        ∀ (B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ),
          AtomicOnCarrier A T → AtomicOnCarrier B (𝓕 T) →
          ∀ (C : CanonicalClusterIndex A d) (j : Fin (ho.clusterSize C)),
            ‖ho.originalClusterNewtonMoment T C j‖ ≤ originalClosedWindowMass B (𝓕 T) W * C₀ := by
  obtain ⟨R, C₁, hR, hC₁, hRaw⟩ := exists_uniform_finite_grouped_kernels_of_unit_window_cap
    K q hd (D := (q : ℝ) * d) (by positivity)
  obtain ⟨M, G, hM, hGs, hTests⟩ :=
    exists_uniform_compact_newton_tests_of_finite_grouped_kernels q (R := R) hd (show 0 < (1 : ℝ) by norm_num) hC₁
  refine ⟨R + 1, M * SchwartzMap.seminorm ℂ 0 0 G, by linarith,
    mul_nonneg hM (apply_nonneg _ _), ?_⟩
  intro A ho hK B T hAt hSpec
  exact ho.originalClusterNewtonMoment_le_of_uniform_compact_newton_tests B T hAt hSpec
    hR (by norm_num) hM hGs (hTests A ho (hRaw A hK))


end BoundedClusterOrder

end
end MeyerGeneralProblem
