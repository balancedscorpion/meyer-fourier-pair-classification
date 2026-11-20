module

public import MeyerGeneralProblem.Sampling.CanonicalGraphData
public import MeyerGeneralProblem.Sampling.KNSGraphSpaceSmooth
public import MeyerGeneralProblem.Interpolation.CanonicalSobolevDomain

@[expose] public section

/-!
# The named canonical interpolator as a bounded graph operator

The original canonical prefix data are decoded explicitly. The same named
global interpolant is lifted into the actual complete KNS graph, with its
unweighted mass controlled by the finite center and the actual exterior
support. Constants are chosen before the coefficient data.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal

private theorem canonicalExterior_zero_near_core {S : LocallyFiniteCarrier}
    {d : ℝ} {q : ℕ} (ho : BoundedClusterOrder S d q)
    (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) (start : ℕ)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ)
    {x : ℝ} (hx : |x| < 1) :
    ho.canonicalExteriorLinearMap hd (B := B) (by linarith) start hε data x = 0 := by
  rw [ho.canonicalExteriorLinearMap_apply]
  unfold physicalRayBlockTail exteriorRayBlockSum
  calc
    _ = ∑' _b : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro b
      rw [quadraticBlockPiece_exteriorRayBlockFactor]
      split_ifs with hb
      · by_contra hn
        have ht := tsupport_iteratedDeriv_rayQuadraticBlockPiece_subset
          (B := B) (by linarith) b 0 ε _ (subset_closure (by simpa using hn))
        exact (not_le_of_gt hx) (quadraticBlockDomain_bounds hB (by omega : 2 ≤ b) ht).1
      · rfl
    _ = 0 := tsum_zero

private theorem physicalEnergy_zero_le_twice_of_core_zero (k : ℕ) (f : ℝ → ℂ)
    (hz : ∀ x : ℝ, |x| < 1 → f x = 0) :
    physicalInterpolationEnergy 0 f ≤ 2 * physicalInterpolationEnergy k f := by
  have hv : (∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖ ^ 2)) ≤
      ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 * k)) * ENNReal.ofReal (‖f x‖ ^ 2) := by
    apply lintegral_mono
    intro x
    by_cases hx : |x| < 1
    · simp [hz x hx]
    · have hp : 1 ≤ |x| ^ (2 * k) := one_le_pow₀ (le_of_not_gt hx)
      exact (le_mul_of_one_le_left (by positivity)
        (show 1 ≤ ENNReal.ofReal (|x| ^ (2 * k)) by
          simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp))
  unfold physicalInterpolationEnergy
  simp only [Nat.mul_zero, pow_zero, ENNReal.ofReal_one, one_mul, iteratedDeriv_zero]
  calc
    _ ≤ (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 * k)) * ENNReal.ofReal (‖f x‖ ^ 2)) +
        ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 * k)) * ENNReal.ofReal (‖f x‖ ^ 2) := add_le_add hv hv
    _ = 2 * (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 * k)) * ENNReal.ofReal (‖f x‖ ^ 2)) :=
      (two_mul _).symm
    _ ≤ _ := mul_le_mul' le_rfl le_self_add

namespace LocallyFiniteCarrier

variable (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
    (ho : BoundedClusterOrder S.signedSquareImage d q)

/-- The missing unweighted energy estimate for the actual named global
interpolant. The finite central geometry is fixed before all raw data;
actual exterior support makes its physical power weight dominate its mass. -/
theorem exists_canonicalGlobalLinearMap_mass_energy (N k : ℕ) (hk : 1 ≤ k)
    {B : ℝ} (hB : 1 ≤ B) (hd : 0 < d) (hdiam : (q : ℝ) * d ≤ B)
    (b₀ : ℤ)
    (hpositive : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S.signedSquareImage B 1 j).ncard ≤ N)
    (hnegative : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S.signedSquareImage B (-1) j).ncard ≤ N)
    (start : ℕ) (hstart : 3 ≤ start) (hstart₀ : b₀ + 1 ≤ (start : ℤ)) :
    ∃ M : ℝ, 0 < M ∧
      ∀ anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C),
      ∀ data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ,
        ho.canonicalWeightedDataEnergy k anchor data ≠ ⊤ →
        (∫ x : ℝ, ‖S.canonicalGlobalLinearMap ho hd (B := B) (by linarith) start data x‖ ^ 2) ≤
          M * (ho.canonicalWeightedDataEnergy k anchor data).toReal := by
  have hBpos : 0 < B := by linarith
  obtain ⟨A, hA, ha⟩ := S.exists_canonicalCentralLinearMap_energy ho 0 hBpos start
  obtain ⟨D, hD, hdBound⟩ := exists_uniform_canonicalExteriorLinearMap_energy N q k hk hB hd hdiam
  let M : ℝ := 4 * A + 12 * D
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro anchor data hfinite
  let c := S.canonicalCentralLinearMap ho B start data
  let p := ho.canonicalExteriorLinearMap hd hBpos start (ε := 1) (Or.inl rfl) data
  let n := ho.canonicalExteriorLinearMap hd hBpos start (ε := -1) (Or.inr rfl) data
  let E := ho.canonicalWeightedDataEnergy k anchor data
  have hc := S.contDiff_canonicalCentralLinearMap ho hBpos start data
  have hp := ho.contDiff_canonicalExteriorLinearMap hd hBpos start (Or.inl rfl) data
  have hn := ho.contDiff_canonicalExteriorLinearMap hd hBpos start (Or.inr rfl) data
  have hcE : physicalInterpolationEnergy 0 c ≤ ENNReal.ofReal A * E :=
    (ha anchor data).trans (mul_le_mul' le_rfl
      (ho.canonicalWeightedDataEnergy_mono_order (Nat.zero_le k) anchor data))
  have hpE : physicalInterpolationEnergy 0 p ≤ ENNReal.ofReal (2 * D) * E := by
    apply (physicalEnergy_zero_le_twice_of_core_zero k p
      (fun x hx => canonicalExterior_zero_near_core ho hd hB start (Or.inl rfl) data hx)).trans
    have h := mul_le_mul' (le_refl (2 : ℝ≥0∞)) (hdBound S.signedSquareImage ho 1 (Or.inl rfl) b₀
      hpositive start hstart hstart₀ anchor data)
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      mul_assoc] using h
  have hnE : physicalInterpolationEnergy 0 n ≤ ENNReal.ofReal (2 * D) * E := by
    apply (physicalEnergy_zero_le_twice_of_core_zero k n
      (fun x hx => canonicalExterior_zero_near_core ho hd hB start (Or.inr rfl) data hx)).trans
    have h := mul_le_mul' (le_refl (2 : ℝ≥0∞)) (hdBound S.signedSquareImage ho (-1) (Or.inr rfl) b₀
      hnegative start hstart hstart₀ anchor data)
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      mul_assoc] using h
  have he : physicalInterpolationEnergy 0 (c + p + n) ≤ ENNReal.ofReal M * E := by
    apply (physicalInterpolationEnergy_add_le 0 (c + p) n (hc.add hp) hn).trans
    calc
      _ ≤ 2 * (2 * (physicalInterpolationEnergy 0 c + physicalInterpolationEnergy 0 p) +
          physicalInterpolationEnergy 0 n) :=
        mul_le_mul' le_rfl (add_le_add (physicalInterpolationEnergy_add_le 0 c p hc hp) le_rfl)
      _ ≤ 2 * (2 * (ENNReal.ofReal A * E + ENNReal.ofReal (2 * D) * E) +
          ENNReal.ofReal (2 * D) * E) := by gcongr
      _ = _ := by
        have hmcast : ENNReal.ofReal M = 4 * ENNReal.ofReal A + 12 * ENNReal.ofReal D := by
          rw [show M = 4 * A + 12 * D from rfl,
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12)]
          norm_num
        rw [hmcast]
        simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        ring
  have hreal := (integrable_and_real_energy_le_of_physicalInterpolationEnergy_le 0 (c + p + n)
    ((hc.add hp).add hn) hM.le hfinite he).2.2
  simp only [Nat.mul_zero, pow_zero, one_mul, iteratedDeriv_zero] at hreal
  have hnMass : 0 ≤ ∫ x : ℝ, ‖(c + p + n) x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  change (∫ x : ℝ, ‖(c + p + n) x‖ ^ 2) ≤ _
  linarith

/-- The same named global canonical interpolant applied to the explicit
decoded original prefixes, still as an actual function-valued linear map. -/
def canonicalGraphFunction (k : ℕ) (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) (start : ℕ)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C)) :
    ho.CanonicalGraphData →ₗ[ℂ] (ℝ → ℂ) :=
  (S.canonicalGlobalLinearMap ho hd (B := B) (by linarith) start).comp
    (ho.canonicalGraphDecode k anchor)

/-- The actual decoded function is smooth for every Hilbert datum. -/
theorem contDiff_canonicalGraphFunction (k : ℕ) (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) (start : ℕ)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
    (y : ho.CanonicalGraphData) : ContDiff ℝ ∞ (S.canonicalGraphFunction ho k hd hB start anchor y) :=
  S.contDiff_canonicalGlobalLinearMap ho hd (B := B) (by linarith) start _

/-- Every original prefix of the actual smooth decoded function is the
corresponding decoded coordinate, including all finite central blocks. -/
theorem canonicalGraphFunction_prefix (k : ℕ) (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B)
    (start : ℕ) (hstart : 3 ≤ start)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
    (y : ho.CanonicalGraphData) :
    ho.canonicalPrefixData (S.physicalSignedSquarePullbackMap
      (S.canonicalGraphFunction ho k hd hB start anchor y)) = ho.canonicalGraphDecode k anchor y :=
  S.canonicalGlobalLinearMap_prefix ho hd hB start hstart _

section GraphOperator

variable (N k : ℕ) (hk : 2 ≤ k) {B : ℝ} (hB : 1 ≤ B) (hd : 0 < d) (hdiam : (q : ℝ) * d ≤ B)
    (b₀ : ℤ)
    (hpositive : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S.signedSquareImage B 1 j).ncard ≤ N)
    (hnegative : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S.signedSquareImage B (-1) j).ncard ≤ N)
    (start : ℕ) (hstart : 3 ≤ start) (hstart₀ : b₀ + 1 ≤ (start : ℤ))

include N k hk hB hd hdiam b₀ hpositive hnegative start hstart hstart₀

private theorem canonicalGraphFunction_domain
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
    (y : ho.CanonicalGraphData) :
    let f := S.canonicalGraphFunction ho k hd hB start anchor y
    MemLp f 2 ∧ MemLp (fun x : ℝ => (x : ℂ) ^ k * f x) 2 ∧
      ∀ j ≤ k, MemLp (iteratedDeriv j f) 2 :=
  S.canonicalGlobalLinearMap_memLp_derivatives ho N k (by omega) hB hd hdiam b₀ hpositive hnegative
    start hstart hstart₀ anchor _ (ho.canonicalWeightedDataEnergy_decode_ne_top k anchor y)

/-- Lift the actual named smooth interpolant to the complete graph. All
domain properties are derived from its actual finite decoded data energy. -/
def canonicalGraphInterpolant
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
    (y : ho.CanonicalGraphData) : KNSGraphSpace k :=
  let hdom := S.canonicalGraphFunction_domain ho N k hk hB hd hdiam b₀ hpositive hnegative
    start hstart hstart₀ anchor y
  KNSGraphSpace.ofSmooth k (S.contDiff_canonicalGraphFunction ho k hd hB start anchor y)
    hdom.1 hdom.2.1 (hdom.2.2 k le_rfl)

/-- The graph element has exactly the actual named interpolating function
as its almost-everywhere representative; point samples use that smooth function. -/
theorem canonicalGraphInterpolant_physical_ae
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
    (y : ho.CanonicalGraphData) :
    (KNSGraphSpace.physical k (S.canonicalGraphInterpolant ho N k hk hB hd hdiam b₀
      hpositive hnegative start hstart hstart₀ anchor y) : ℝ → ℂ) =ᵐ[volume]
        S.canonicalGraphFunction ho k hd hB start anchor y :=
  (S.canonicalGraphFunction_domain ho N k hk hB hd hdiam b₀ hpositive hnegative
    start hstart hstart₀ anchor y).1.coeFn_toLp

/-- Complex linearity of the actual graph lift follows from its actual
function representative and the injective physical graph projection. -/
def canonicalGraphLinearMap
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C)) :
    ho.CanonicalGraphData →ₗ[ℂ] KNSGraphSpace k where
  toFun := S.canonicalGraphInterpolant ho N k hk hB hd hdiam b₀ hpositive hnegative start hstart hstart₀ anchor
  map_add' y z := by
    apply KNSGraphSpace.physical_injective k
    rw [map_add]
    apply Lp.ext
    filter_upwards [S.canonicalGraphInterpolant_physical_ae ho N k hk hB hd hdiam b₀
      hpositive hnegative start hstart hstart₀ anchor (y + z),
      S.canonicalGraphInterpolant_physical_ae ho N k hk hB hd hdiam b₀
      hpositive hnegative start hstart hstart₀ anchor y,
      S.canonicalGraphInterpolant_physical_ae ho N k hk hB hd hdiam b₀
      hpositive hnegative start hstart hstart₀ anchor z,
      Lp.coeFn_add
        (KNSGraphSpace.physical k (S.canonicalGraphInterpolant ho N k hk hB hd hdiam b₀
          hpositive hnegative start hstart hstart₀ anchor y))
        (KNSGraphSpace.physical k (S.canonicalGraphInterpolant ho N k hk hB hd hdiam b₀
          hpositive hnegative start hstart hstart₀ anchor z))] with x hx hy hz ha
    rw [hx, ha]
    simp only [Pi.add_apply, hy, hz]
    exact congrFun (map_add (S.canonicalGraphFunction ho k hd hB start anchor) y z) x
  map_smul' a y := by
    apply KNSGraphSpace.physical_injective k
    simp only [map_smul, RingHom.id_apply]
    apply Lp.ext
    filter_upwards [S.canonicalGraphInterpolant_physical_ae ho N k hk hB hd hdiam b₀
      hpositive hnegative start hstart hstart₀ anchor (a • y),
      S.canonicalGraphInterpolant_physical_ae ho N k hk hB hd hdiam b₀
      hpositive hnegative start hstart hstart₀ anchor y,
      Lp.coeFn_smul a (KNSGraphSpace.physical k (S.canonicalGraphInterpolant ho N k hk hB hd hdiam b₀
        hpositive hnegative start hstart hstart₀ anchor y))] with x hx hy ha
    rw [hx, ha]
    simp only [Pi.smul_apply, smul_eq_mul, hy]
    exact congrFun (map_smul (S.canonicalGraphFunction ho k hd hB start anchor) a y) x

/-- The actual global interpolant is bounded into the complete graph,
including its unweighted L2 term. A single positive constant precedes all
anchors and all original-prefix Hilbert data at the fixed geometry and order. -/
theorem exists_norm_canonicalGraphLinearMap_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C),
      ∀ y : ho.CanonicalGraphData,
        ‖S.canonicalGraphLinearMap ho N k hk hB hd hdiam b₀ hpositive hnegative
          start hstart hstart₀ anchor y‖ ≤ C * ‖y‖ := by
  obtain ⟨M, hM, hm⟩ := S.exists_canonicalGlobalLinearMap_mass_energy ho N k (by omega) hB hd hdiam
    b₀ hpositive hnegative start hstart hstart₀
  obtain ⟨K, hK, he⟩ := S.exists_canonicalGlobalLinearMap_real_energy ho N k (by omega) hB hd hdiam
    b₀ hpositive hnegative start hstart hstart₀
  refine ⟨Real.sqrt (2 * M + K), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro anchor y
  let data := ho.canonicalGraphDecode k anchor y
  let f := S.canonicalGraphFunction ho k hd hB start anchor y
  have hfinite := ho.canonicalWeightedDataEnergy_decode_ne_top k anchor y
  have hdom := S.canonicalGraphFunction_domain ho N k hk hB hd hdiam b₀ hpositive hnegative
    start hstart hstart₀ anchor y
  have hmass := hm anchor data hfinite
  have htop := (he anchor data hfinite).2.2
  have hdata : (ho.canonicalWeightedDataEnergy k anchor data).toReal = ‖y‖ ^ 2 := by
    rw [ho.canonicalWeightedDataEnergy_decode, ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [hdata] at hmass htop
  have hpnorm : ‖hdom.2.1.toLp‖ ^ 2 = ∫ x : ℝ, |x| ^ (2 * k) * ‖f x‖ ^ 2 := by
    rw [← integral_norm_sq_eq_toLp_norm_sq_complex hdom.2.1]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow, ← pow_mul,
      Nat.mul_comm k 2]
    rfl
  have hg := KNSGraphSpace.norm_ofSmooth_sq_le k
    (S.contDiff_canonicalGraphFunction ho k hd hB start anchor y) hdom.1 hdom.2.1 (hdom.2.2 k le_rfl)
  rw [hpnorm, ← integral_norm_sq_eq_toLp_norm_sq_complex hdom.1,
    ← integral_norm_sq_eq_toLp_norm_sq_complex (hdom.2.2 k le_rfl)] at hg
  have hsq : ‖S.canonicalGraphLinearMap ho N k hk hB hd hdiam b₀ hpositive hnegative
      start hstart hstart₀ anchor y‖ ^ 2 ≤ (2 * M + K) * ‖y‖ ^ 2 := by
    change ‖KNSGraphSpace.ofSmooth k (S.contDiff_canonicalGraphFunction ho k hd hB start anchor y)
      hdom.1 hdom.2.1 (hdom.2.2 k le_rfl)‖ ^ 2 ≤ _
    change (∫ x : ℝ, ‖f x‖ ^ 2) ≤ M * ‖y‖ ^ 2 at hmass
    change (∫ x : ℝ, |x| ^ (2 * k) * ‖f x‖ ^ 2) +
      (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2) ≤ K * ‖y‖ ^ 2 at htop
    linarith
  have hsqrt := Real.sq_sqrt (show 0 ≤ 2 * M + K by positivity)
  have hn : 0 ≤ Real.sqrt (2 * M + K) * ‖y‖ := by positivity
  nlinarith [norm_nonneg (S.canonicalGraphLinearMap ho N k hk hB hd hdiam b₀ hpositive hnegative
    start hstart hstart₀ anchor y)]

/-- The genuine bounded complex-linear canonical interpolation operator
from the full weighted original-prefix coefficient Hilbert space to E_k. -/
def canonicalGraphInterpolator
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C)) :
    ho.CanonicalGraphData →L[ℂ] KNSGraphSpace k :=
  (S.canonicalGraphLinearMap ho N k hk hB hd hdiam b₀ hpositive hnegative start hstart hstart₀ anchor).mkContinuous
      (S.exists_norm_canonicalGraphLinearMap_le ho N k hk hB hd hdiam b₀ hpositive hnegative
        start hstart hstart₀).choose
      ((S.exists_norm_canonicalGraphLinearMap_le ho N k hk hB hd hdiam b₀ hpositive hnegative
        start hstart hstart₀).choose_spec.2 anchor)

/-- The bounded graph operator has the same actual smooth representative
and every original-prefix value; no point evaluation of an arbitrary L2
representative is asserted. -/
theorem canonicalGraphInterpolator_represents_prefixes
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
    (y : ho.CanonicalGraphData) :
    let f := S.canonicalGraphFunction ho k hd hB start anchor y
    ContDiff ℝ ∞ f ∧
      ((KNSGraphSpace.physical k (S.canonicalGraphInterpolator ho N k hk hB hd hdiam b₀
        hpositive hnegative start hstart hstart₀ anchor y) : ℝ → ℂ) =ᵐ[volume] f) ∧
      ho.canonicalPrefixData (S.physicalSignedSquarePullbackMap f) = ho.canonicalGraphDecode k anchor y :=
  ⟨S.contDiff_canonicalGraphFunction ho k hd hB start anchor y,
    S.canonicalGraphInterpolant_physical_ae ho N k hk hB hd hdiam b₀ hpositive hnegative
      start hstart hstart₀ anchor y,
    S.canonicalGraphFunction_prefix ho k hd hB start hstart anchor y⟩

/-- Every raw finite-energy canonical vector is handled by the bounded
operator, with exactly the original named interpolant and its original
prefixes. This is the explicit all-finite-energy, rather than proper-subdomain, form. -/
theorem canonicalGraphInterpolator_on_raw_data
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
    (data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ)
    (hfinite : ho.canonicalWeightedDataEnergy k anchor data ≠ ⊤) :
    let f := S.canonicalGlobalLinearMap ho hd (B := B) (by linarith) start data
    ContDiff ℝ ∞ f ∧
      ((KNSGraphSpace.physical k (S.canonicalGraphInterpolator ho N k hk hB hd hdiam b₀
        hpositive hnegative start hstart hstart₀ anchor
          (ho.canonicalGraphEncode k anchor data hfinite)) : ℝ → ℂ) =ᵐ[volume] f) ∧
      ho.canonicalPrefixData (S.physicalSignedSquarePullbackMap f) = data := by
  have h := S.canonicalGraphInterpolator_represents_prefixes ho N k hk hB hd hdiam b₀
    hpositive hnegative start hstart hstart₀ anchor (ho.canonicalGraphEncode k anchor data hfinite)
  simpa only [canonicalGraphFunction, LinearMap.comp_apply, ho.canonicalGraphDecode_encode] using h

end GraphOperator

end LocallyFiniteCarrier

end

end MeyerGeneralProblem
