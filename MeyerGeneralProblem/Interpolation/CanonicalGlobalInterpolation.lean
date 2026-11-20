module

public import MeyerGeneralProblem.Interpolation.CanonicalDataValues
public import MeyerGeneralProblem.Interpolation.CanonicalLinearExteriorEnergy

@[expose] public section

/-!
# Actual global linear interpolation from canonical grouped data

The central physical polynomial and both named exterior maps use the same
original canonical prefix data. Finite Newton inverses reconstruct the central
values. Whole central clusters, both ray signs, and the origin are retained.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

attribute [local instance] Classical.propDecidable

private theorem weighted_lintegral_norm_add_le (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (f g : ℝ → ℂ) (hf : Continuous f) (_hg : Continuous g) :
    (∫⁻ x, w x * ENNReal.ofReal (‖f x+g x‖ ^ 2)) ≤
      2*((∫⁻ x, w x*ENNReal.ofReal (‖f x‖ ^ 2)) +
        ∫⁻ x, w x*ENNReal.ofReal (‖g x‖ ^ 2)) := by
  have hp (x : ℝ) : ENNReal.ofReal (‖f x+g x‖ ^ 2) ≤
      2*(ENNReal.ofReal (‖f x‖ ^ 2)+ENNReal.ofReal (‖g x‖ ^ 2)) := by
    have hsq : ‖f x+g x‖ ^ 2 ≤ 2*(‖f x‖ ^ 2+‖g x‖ ^ 2) := by
      have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (f x) (g x)) 2
      nlinarith [sq_nonneg (‖f x‖-‖g x‖)]
    simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)] using ENNReal.ofReal_le_ofReal hsq
  have hm : Measurable (fun x => w x*ENNReal.ofReal (‖f x‖ ^ 2)) := by fun_prop
  calc
    _ ≤ ∫⁻ x, 2*(w x*ENNReal.ofReal (‖f x‖ ^ 2)+w x*ENNReal.ofReal (‖g x‖ ^ 2)) := by
      apply lintegral_mono
      intro x
      exact (mul_le_mul' (a := w x) (b := w x) le_rfl (hp x)).trans_eq (by ring)
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left hm]

/-- The true physical energy of a sum is bounded by twice the sum of the
true energies, including infinite values. Smoothness justifies derivative
additivity; no integrability or desired energy bound is assumed. -/
theorem physicalInterpolationEnergy_add_le (k : ℕ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    physicalInterpolationEnergy k (f+g) ≤
      2*(physicalInterpolationEnergy k f+physicalInterpolationEnergy k g) := by
  have hv := weighted_lintegral_norm_add_le (fun x => ENNReal.ofReal (|x|^(2*k)))
    (by fun_prop) f g hf.continuous hg.continuous
  have hderiv : iteratedDeriv k (f+g) = iteratedDeriv k f+iteratedDeriv k g := by
    funext x
    exact iteratedDeriv_add (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))
  have hd := weighted_lintegral_norm_add_le (fun _ => 1) measurable_const
    (iteratedDeriv k f) (iteratedDeriv k g)
    (hf.continuous_iteratedDeriv k (by simp)) (hg.continuous_iteratedDeriv k (by simp))
  simp only [one_mul] at hd
  unfold physicalInterpolationEnergy
  rw [hderiv]
  exact (add_le_add hv hd).trans_eq (by ring)

namespace LocallyFiniteCarrier

variable (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
    (ho : BoundedClusterOrder S.signedSquareImage d q)

/-- The physical carrier values reconstructed from original signed-square
prefix data by the genuine finite Newton inverse. -/
def canonicalPhysicalValueMap :
    ((C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ) →ₗ[ℂ]
      (S.subtype → ℂ) where
  toFun data x := ho.canonicalDataValueMap data (S.signedSquareSubtypeEquiv x)
  map_add' a b := by ext x; simp
  map_smul' a b := by ext x; simp

/-- The actual central finite data obtained from the same global canonical
prefix vector used by the exterior polynomials. -/
def canonicalCentralDataMap (R : ℝ) :
    ((C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ) →ₗ[ℂ]
      (S.centralPhysicalFinset ho R → ℂ) where
  toFun data i := S.canonicalPhysicalValueMap ho data i.val
  map_add' a b := by ext i; simp
  map_smul' a b := by ext i; simp

/-- The actual central cutoff polynomial as a linear map of global
canonical grouped data, not a separately supplied point-value vector. -/
def canonicalCentralLinearMap (B : ℝ) (start : ℕ) :
    ((C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ) →ₗ[ℂ]
      (ℝ → ℂ) :=
  (centralPhysicalInterpolant B start
    (S.centralPhysicalNode ho (((start:ℝ)+1/8)*B))).comp
      (S.canonicalCentralDataMap ho (((start:ℝ)+1/8)*B))

/-- The actual central map is smooth for all input data. -/
theorem contDiff_canonicalCentralLinearMap {B : ℝ} (hB : 0 < B) (start : ℕ)
    (data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ) :
    ContDiff ℝ ∞ (S.canonicalCentralLinearMap ho B start data) := by
  obtain ⟨_, _, h⟩ := exists_uniform_centralPhysical_energy_bound 0 hB start
    (S.centralPhysicalNode ho (((start:ℝ)+1/8)*B))
  exact (h (S.canonicalCentralDataMap ho (((start:ℝ)+1/8)*B) data)).1

/-- The central cutoff map has the exact transition-weighted value at
every physical carrier point, including zero and straddling central groups. -/
theorem canonicalCentralLinearMap_on_carrier {B : ℝ} (hB : 0 < B) (start : ℕ)
    (data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ)
    (x : S.subtype) :
    S.canonicalCentralLinearMap ho B start data x =
      (1-blockTransition B start ((x:ℝ)^2)) • S.canonicalPhysicalValueMap ho data x := by
  by_cases hz : 1-blockTransition B start ((x:ℝ)^2) = 0
  · change (1-blockTransition B start ((x:ℝ)^2)) •
      finitePhysicalPolynomialFunction (S.centralPhysicalNode ho (((start:ℝ)+1/8)*B))
        (S.canonicalCentralDataMap ho (((start:ℝ)+1/8)*B) data) x = _
    rw [hz, zero_smul, zero_smul]
  · let i : S.centralPhysicalFinset ho (((start:ℝ)+1/8)*B) :=
      ⟨x, S.mem_centralPhysicalFinset_of_cutoff ho hB start x hz⟩
    exact centralPhysicalInterpolant_eval B start _ (S.centralPhysicalNode_injective ho _)
      (S.canonicalCentralDataMap ho (((start:ℝ)+1/8)*B) data) i

/-- The fixed central Newton reconstruction has finite squared norm against
the full canonical weighted data, with no intragroup uniformity premise. -/
theorem exists_canonicalCentralData_energy_bound (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      ∀ anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C),
      ∀ data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ,
        ENNReal.ofReal (∑ i, ‖S.canonicalCentralDataMap ho R data i‖ ^ 2) ≤
          ENNReal.ofReal C * ho.canonicalWeightedDataEnergy k anchor data := by
  let F := S.centralPhysicalFinset ho R
  let G := F.map S.signedSquareSubtypeEquiv.toEmbedding
  obtain ⟨C, hC, hb⟩ := ho.exists_finite_canonicalDataValue_energy_bound G
  refine ⟨C, hC, ?_⟩
  intro k anchor data
  have heq : (∑ i : F, ‖S.canonicalCentralDataMap ho R data i‖ ^ 2) =
      ∑ x : G, ‖ho.canonicalDataValueMap data x.val‖ ^ 2 := by
    change (∑ i : F, ‖ho.canonicalDataValueMap data (S.signedSquareSubtypeEquiv i.val)‖ ^ 2) = _
    rw [Finset.sum_coe_sort F (fun x => ‖ho.canonicalDataValueMap data (S.signedSquareSubtypeEquiv x)‖ ^ 2),
      Finset.sum_coe_sort G (fun x => ‖ho.canonicalDataValueMap data x‖ ^ 2)]
    exact (Finset.sum_map F S.signedSquareSubtypeEquiv.toEmbedding
      (fun x => ‖ho.canonicalDataValueMap data x‖ ^ 2)).symm
  rw [heq]
  exact hb k anchor data

/-- The actual central linear map has a full canonical weighted energy
bound. The constant may depend on the fixed finite central geometry but is
chosen before all data and all actual anchor choices. -/
theorem exists_canonicalCentralLinearMap_energy (k : ℕ) {B : ℝ} (hB : 0 < B)
    (start : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C),
      ∀ data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ,
        physicalInterpolationEnergy k (S.canonicalCentralLinearMap ho B start data) ≤
          ENNReal.ofReal K * ho.canonicalWeightedDataEnergy k anchor data := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_centralPhysical_energy_bound k hB start
    (S.centralPhysicalNode ho (((start:ℝ)+1/8)*B))
  obtain ⟨D, hD, hd⟩ := S.exists_canonicalCentralData_energy_bound ho (((start:ℝ)+1/8)*B)
  refine ⟨C*D, mul_pos hC hD, ?_⟩
  intro anchor data
  have he := (hb (S.canonicalCentralDataMap ho (((start:ℝ)+1/8)*B) data)).2.2.2.2.2
  apply he.trans
  calc
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal D * ho.canonicalWeightedDataEnergy k anchor data) :=
      mul_le_mul' le_rfl (hd k anchor data)
    _ = _ := by rw [ENNReal.ofReal_mul hC.le, mul_assoc]

/-- The global complex-linear interpolant: the physical central polynomial
and the two independent actual ray tails of the same canonical prefix data. -/
def canonicalGlobalLinearMap (hd : 0 < d) {B : ℝ} (hB : 0 < B) (start : ℕ) :
    ((C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ) →ₗ[ℂ]
      (ℝ → ℂ) :=
  S.canonicalCentralLinearMap ho B start +
    ho.canonicalExteriorLinearMap hd hB start (ε := 1) (Or.inl rfl) +
    ho.canonicalExteriorLinearMap hd hB start (ε := -1) (Or.inr rfl)

/-- The genuine global linear interpolant is smooth across both rays and
the origin, without any finite-energy assumption. -/
theorem contDiff_canonicalGlobalLinearMap (hd : 0 < d) {B : ℝ} (hB : 0 < B)
    (start : ℕ)
    (data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ) :
    ContDiff ℝ ∞ (S.canonicalGlobalLinearMap ho hd hB start data) :=
  ((S.contDiff_canonicalCentralLinearMap ho hB start data).add
    (ho.contDiff_canonicalExteriorLinearMap hd hB start (Or.inl rfl) data)).add
      (ho.contDiff_canonicalExteriorLinearMap hd hB start (Or.inr rfl) data)

/-- On its correct ray the named exterior map interpolates the exact
physical values reconstructed from the original full grouped data. -/
theorem canonicalExteriorLinearMap_physical_value (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B)
    (start : ℕ) (hstart : 3 ≤ start) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ)
    (x : S.subtype) (hx : 0 < ε*(x:ℝ)) :
    ho.canonicalExteriorLinearMap hd (B := B) (by linarith) start hε data x =
      blockTransition B start ((x:ℝ)^2) • S.canonicalPhysicalValueMap ho data x := by
  have he : signedSquare (x:ℝ) = ε*(x:ℝ)^2 := by
    rcases hε with rfl | rfl
    · simpa only [one_mul] using signedSquare_of_nonneg (by simpa using hx.le)
    · simpa only [neg_one_mul] using signedSquare_of_nonpos (by linarith)
  have hm : ε*(x:ℝ)^2 ∈ S.signedSquareImage.carrier := by
    rw [← he]
    exact ⟨x, x.property, rfl⟩
  have h := ho.canonicalExteriorLinearMap_eq_on_carrier hd hB start hstart hε
    (ho.canonicalDataFunctionMap data) x hx hm
  rw [ho.canonicalPrefixData_canonicalDataFunctionMap] at h
  have hv := ho.canonicalDataFunctionMap_on_carrier data (S.signedSquareSubtypeEquiv x)
  change ho.canonicalDataFunctionMap data (signedSquare (x:ℝ)) =
    S.canonicalPhysicalValueMap ho data x at hv
  rw [he] at hv
  exact h.trans (congrArg (fun z => blockTransition B start ((x:ℝ)^2) • z) hv)

/-- Exact interpolation at every actual physical carrier point, including
the origin, central straddlers, both ray signs, and transition endpoints. -/
theorem canonicalGlobalLinearMap_on_carrier (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B)
    (start : ℕ) (hstart : 3 ≤ start)
    (data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ)
    (x : S.subtype) :
    S.canonicalGlobalLinearMap ho hd (B := B) (by linarith) start data x =
      S.canonicalPhysicalValueMap ho data x := by
  change S.canonicalCentralLinearMap ho B start data x +
    ho.canonicalExteriorLinearMap hd (B := B) (by linarith) start (Or.inl rfl) data x +
    ho.canonicalExteriorLinearMap hd (B := B) (by linarith) start (Or.inr rfl) data x = _
  rw [S.canonicalCentralLinearMap_on_carrier ho (by linarith) start data x]
  rcases lt_trichotomy 0 (x:ℝ) with hx | hx | hx
  · rw [S.canonicalExteriorLinearMap_physical_value ho hd hB start hstart (Or.inl rfl) data x
      (by simpa using hx),
      ho.canonicalExteriorLinearMap_wrongRay hd hB start (Or.inr rfl) data (by linarith),
      add_zero, ← add_smul]
    simp
  · rw [ho.canonicalExteriorLinearMap_wrongRay hd hB start (Or.inl rfl) data (by simp [← hx]),
      ho.canonicalExteriorLinearMap_wrongRay hd hB start (Or.inr rfl) data (by simp [← hx]),
      add_zero, add_zero, blockTransition_square_eq_zero_near_origin hB hstart (by simp [← hx])]
    simp
  · rw [ho.canonicalExteriorLinearMap_wrongRay hd hB start (Or.inl rfl) data (by linarith),
      add_zero, S.canonicalExteriorLinearMap_physical_value ho hd hB start hstart (Or.inr rfl)
        data x (by linarith), ← add_smul]
    simp

/-- Pullback to actual signed-square nodes, extended by zero elsewhere.
This uses the exact carrier equivalence, including at zero. -/
def physicalSignedSquarePullbackMap : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun f s := if hs : s ∈ S.signedSquareImage.subtype then
    f (S.signedSquareSubtypeEquiv.symm ⟨s, hs⟩) else 0
  map_add' a b := by ext s; by_cases hs : s ∈ S.signedSquareImage.subtype <;> simp [hs]
  map_smul' a b := by ext s; by_cases hs : s ∈ S.signedSquareImage.subtype <;> simp [hs]

/-- Pullback evaluation at an actual image node is the physical value at
its unique source point. -/
theorem physicalSignedSquarePullbackMap_on_carrier (f : ℝ → ℂ)
    (s : S.signedSquareImage.subtype) :
    S.physicalSignedSquarePullbackMap f s = f (S.signedSquareSubtypeEquiv.symm s) := by
  change (if hs : (s:ℝ) ∈ S.signedSquareImage.subtype then
    f (S.signedSquareSubtypeEquiv.symm ⟨s, hs⟩) else 0) = _
  rw [dite_eq_left s.property]

/-- Every original canonical prefix is interpolated by the actual global
map, including groups crossing zero or the central/exterior transition. -/
theorem canonicalGlobalLinearMap_prefix (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B)
    (start : ℕ) (hstart : 3 ≤ start)
    (data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ) :
    ho.canonicalPrefixData (S.physicalSignedSquarePullbackMap
      (S.canonicalGlobalLinearMap ho hd (B := B) (by linarith) start data)) = data := by
  conv_rhs => rw [← ho.canonicalPrefixData_canonicalDataFunctionMap data]
  funext C i
  simp only [BoundedClusterOrder.canonicalPrefixData, analyticDividedDifference_eq_dividedDifferences
    (ho.realClusterNode C) (ho.realClusterNode_strictMono C).injective]
  congr 1
  funext j
  change S.physicalSignedSquarePullbackMap _ (ho.orderedClusterNode C j) = _
  rw [S.physicalSignedSquarePullbackMap_on_carrier _ (ho.orderedClusterNode C j),
    S.canonicalGlobalLinearMap_on_carrier ho hd hB start hstart]
  change ho.canonicalDataValueMap data
      (S.signedSquareSubtypeEquiv (S.signedSquareSubtypeEquiv.symm (ho.orderedClusterNode C j))) = _
  rw [Equiv.apply_symm_apply]
  exact (ho.canonicalDataFunctionMap_on_carrier data (ho.orderedClusterNode C j)).symm

/-- The actual global interpolation operator on arbitrary function samples.
Its only input coordinates are their original canonical signed-square data. -/
def canonicalGlobalSampleLinearMap (hd : 0 < d) {B : ℝ} (hB : 0 < B) (start : ℕ) :
    (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
  (S.canonicalGlobalLinearMap ho hd hB start).comp
    (ho.canonicalPrefixDataLinearMap.comp S.physicalSignedSquarePullbackMap)

/-- The global sample operator reproduces every physical carrier value.
Neither continuity of the input function nor a point-interpolation premise
is required. -/
theorem canonicalGlobalSampleLinearMap_on_carrier (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B)
    (start : ℕ) (hstart : 3 ≤ start) (f : ℝ → ℂ) (x : S.subtype) :
    S.canonicalGlobalSampleLinearMap ho hd (B := B) (by linarith) start f x = f x := by
  change S.canonicalGlobalLinearMap ho hd (B := B) (by linarith) start
    (ho.canonicalPrefixData (S.physicalSignedSquarePullbackMap f)) x = _
  rw [S.canonicalGlobalLinearMap_on_carrier ho hd hB start hstart]
  change ho.canonicalDataValueMap (ho.canonicalPrefixData (S.physicalSignedSquarePullbackMap f))
    (S.signedSquareSubtypeEquiv x) = _
  rw [ho.canonicalDataValueMap_canonicalPrefixData, S.physicalSignedSquarePullbackMap_on_carrier,
    Equiv.symm_apply_apply]

/-- Actual source counts on both rays give a full weighted-plus-derivative
energy bound for the genuine global complex-linear interpolant. Dependence
on the finite central geometry is permitted, but the constant is fixed
before the canonical data and anchor choices. -/
theorem exists_canonicalGlobalLinearMap_energy (N k : ℕ) (hk : 1 ≤ k)
    {B : ℝ} (hB : 1 ≤ B) (hd : 0 < d) (hdiam : (q:ℝ)*d ≤ B)
    (b₀ : ℤ)
    (hpositive : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S.signedSquareImage B 1 j).ncard ≤ N)
    (hnegative : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S.signedSquareImage B (-1) j).ncard ≤ N)
    (start : ℕ) (hstart : 3 ≤ start) (hstart₀ : b₀+1 ≤ (start:ℤ)) :
    ∃ K : ℝ, 0 < K ∧
      ∀ anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C),
      ∀ data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ,
        physicalInterpolationEnergy k
          (S.canonicalGlobalLinearMap ho hd (B := B) (by linarith) start data) ≤
            ENNReal.ofReal K * ho.canonicalWeightedDataEnergy k anchor data := by
  have hBpos : 0 < B := by linarith
  obtain ⟨A, hA, ha⟩ := S.exists_canonicalCentralLinearMap_energy ho k hBpos start
  obtain ⟨D, hD, hdBound⟩ := exists_uniform_canonicalExteriorLinearMap_energy N q k hk hB hd hdiam
  refine ⟨2*(2*(A+D)+D), by positivity, ?_⟩
  intro anchor data
  let c := S.canonicalCentralLinearMap ho B start data
  let p := ho.canonicalExteriorLinearMap hd hBpos start (ε := 1) (Or.inl rfl) data
  let n := ho.canonicalExteriorLinearMap hd hBpos start (ε := -1) (Or.inr rfl) data
  have hc := S.contDiff_canonicalCentralLinearMap ho hBpos start data
  have hp := ho.contDiff_canonicalExteriorLinearMap hd hBpos start (Or.inl rfl) data
  have hn := ho.contDiff_canonicalExteriorLinearMap hd hBpos start (Or.inr rfl) data
  have hpE := hdBound S.signedSquareImage ho 1 (Or.inl rfl) b₀ hpositive start hstart hstart₀ anchor data
  have hnE := hdBound S.signedSquareImage ho (-1) (Or.inr rfl) b₀ hnegative start hstart hstart₀ anchor data
  have hcE := ha anchor data
  have hadd := physicalInterpolationEnergy_add_le k c p hc hp
  have hall := physicalInterpolationEnergy_add_le k (c+p) n (hc.add hp) hn
  apply hall.trans
  calc
    _ ≤ 2*(2*(physicalInterpolationEnergy k c+physicalInterpolationEnergy k p)+
        physicalInterpolationEnergy k n) := mul_le_mul' le_rfl (add_le_add hadd le_rfl)
    _ ≤ 2*(2*(ENNReal.ofReal A*ho.canonicalWeightedDataEnergy k anchor data+
        ENNReal.ofReal D*ho.canonicalWeightedDataEnergy k anchor data)+
        ENNReal.ofReal D*ho.canonicalWeightedDataEnergy k anchor data) := by
      gcongr
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ENNReal.ofReal_add (by positivity) hD.le,
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_add hA.le hD.le]
      norm_num only [ENNReal.ofReal_ofNat]
      ring

/-- Finite canonical energy yields actual ordinary integrability and the
real weighted/derivative estimate for the named global operator. -/
theorem exists_canonicalGlobalLinearMap_real_energy (N k : ℕ) (hk : 1 ≤ k)
    {B : ℝ} (hB : 1 ≤ B) (hd : 0 < d) (hdiam : (q:ℝ)*d ≤ B)
    (b₀ : ℤ)
    (hpositive : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S.signedSquareImage B 1 j).ncard ≤ N)
    (hnegative : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S.signedSquareImage B (-1) j).ncard ≤ N)
    (start : ℕ) (hstart : 3 ≤ start) (hstart₀ : b₀+1 ≤ (start:ℤ)) :
    ∃ K : ℝ, 0 < K ∧
      ∀ anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C),
      ∀ data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ,
        ho.canonicalWeightedDataEnergy k anchor data ≠ ⊤ →
        let f := S.canonicalGlobalLinearMap ho hd (B := B) (by linarith) start data
        Integrable (fun x : ℝ => |x|^(2*k)*‖f x‖^2) ∧
        Integrable (fun x : ℝ => ‖iteratedDeriv k f x‖^2) ∧
        (∫ x : ℝ, |x|^(2*k)*‖f x‖^2)+(∫ x : ℝ, ‖iteratedDeriv k f x‖^2) ≤
          K*(ho.canonicalWeightedDataEnergy k anchor data).toReal := by
  obtain ⟨K, hK, hb⟩ := S.exists_canonicalGlobalLinearMap_energy ho N k hk hB hd hdiam
    b₀ hpositive hnegative start hstart hstart₀
  refine ⟨K, hK, ?_⟩
  intro anchor data hfinite
  exact integrable_and_real_energy_le_of_physicalInterpolationEnergy_le k _
    (S.contDiff_canonicalGlobalLinearMap ho hd (by linarith) start data) hK.le hfinite (hb anchor data)

end LocallyFiniteCarrier

end

end MeyerGeneralProblem
