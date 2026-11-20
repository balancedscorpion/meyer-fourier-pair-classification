module

public import MeyerGeneralProblem.Interpolation.UniformGroupedPatterns
public import MeyerGeneralProblem.Interpolation.TripleBlockIncidence
public import MeyerGeneralProblem.Interpolation.QuadraticBlockEnergy

@[expose] public section

/-!
# Local interpolation on actual canonical clusters

Whole canonical clusters meeting a triple block lie in a uniformly enlarged
window, by their proved diameter bound. Their genuine inter-cluster separation
therefore places the actual nodes in the compact configuration space of the
uniform polynomial interpolation theorem. The resulting polynomial matches
every original ordered prefix and has uniformly bounded derivatives on the
cutoff support. On the negative ray the signed node order is retained exactly;
only the argument of the resulting polynomial is reflected.

The number of listed distinct clusters has an explicit finite bound. No node
gap inside a cluster, inverse estimate, or derivative bound is assumed. The
global choice of all touching clusters and weighted summation remain separate.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Polynomial
open scoped ContDiff

/-- A reflection preserves derivative norms at every order, including for
functions whose derivatives are defined by the default derivative convention. -/
theorem norm_iteratedDeriv_comp_sign (f : ℝ → ℂ) (j : ℕ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (x : ℝ) :
    ‖iteratedDeriv j (fun t => f (ε * t)) x‖ =
      ‖iteratedDeriv j f (ε * x)‖ := by
  rcases hε with rfl | rfl
  · simp only [one_mul]
  · simp only [neg_one_mul, iteratedDeriv_comp_neg, norm_smul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul]

/-- A full canonical cluster touching the oriented triple window lies within
radius `3B` of the signed block base. The witness is an actual cluster node. -/
theorem BoundedClusterOrder.canonicalBlock_node_bound
    {S : LocallyFiniteCarrier} {d B : ℝ} {q : ℕ}
    (horder : BoundedClusterOrder S d q) (hd : 0 < d) (hB : 0 < B)
    (hdiam : (q : ℝ) * d ≤ B) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (b : ℕ) (C : CanonicalClusterIndex S d)
    (htouch : groupTouchesTripleBlock B
      (range (fun i => ε * horder.realClusterNode C i)) b)
    (i : Fin (horder.clusterSize C)) :
    |horder.realClusterNode C i - ε * ((b : ℝ) * B)| ≤ 3 * B := by
  obtain ⟨s, ⟨j, rfl⟩, hs⟩ := htouch
  have hnear : |horder.realClusterNode C i - horder.realClusterNode C j| ≤ B := by
    simpa only [Real.dist_eq] using (horder.realClusterNode_diameter hd C i j).trans hdiam
  change ((b : ℝ) - 1) * B ≤ ε * horder.realClusterNode C j ∧
    ε * horder.realClusterNode C j < ((b : ℝ) + 2) * B at hs
  rcases abs_le.mp hnear with ⟨hl, hu⟩
  rcases hε with rfl | rfl
  · simp only [one_mul] at hs ⊢
    exact abs_le.mpr ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  · simp only [neg_one_mul] at hs ⊢
    exact abs_le.mpr ⟨by nlinarith [hs.2], by nlinarith [hs.1]⟩

/-- The actual nodes of distinct touching canonical clusters satisfy the
uniform configuration hypotheses. Internal node gaps never enter this proof. -/
theorem BoundedClusterOrder.canonicalBlock_mem_groupedNodeConfigurations
    {S : LocallyFiniteCarrier} {d B : ℝ} {q n : ℕ}
    (horder : BoundedClusterOrder S d q) (hd : 0 < d) (hB : 0 < B)
    (hdiam : (q : ℝ) * d ≤ B) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (b : ℕ) (clusters : Fin n → CanonicalClusterIndex S d)
    (hinj : Function.Injective clusters)
    (htouch : ∀ g, groupTouchesTripleBlock B
      (range (fun i => ε * horder.realClusterNode (clusters g) i)) b) :
    (fun g i => horder.realClusterNode (clusters g) i - ε * ((b : ℝ) * B)) ∈
      GroupedNodeConfigurations (fun g => horder.clusterSize (clusters g)) (3 * B) d := by
  constructor
  · intro g i
    exact horder.canonicalBlock_node_bound hd hB hdiam hε b (clusters g) (htouch g) i
  · intro g h hgh i j
    have h := horder.realClusterNode_separated (fun heq => hgh (hinj heq)) i j
    convert h using 1
    congr 1
    ring

/-- The positive square-coordinate cutoff window remains in the enlarged
signed interpolation window on either ray. -/
theorem quadraticBlock_cutoff_mem_signedWindow {B : ℝ} (hB : 0 < B)
    (b : ℕ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {x : ℝ}
    (hx : x ∈ Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8)) :
    |ε * x - ε * ((b : ℝ) * B)| ≤ 3 * B := by
  have hb : |x - (b : ℝ) * B| ≤ 3 * B :=
    abs_le.mpr ⟨by linarith [hx.1], by nlinarith [hx.2]⟩
  rcases hε with rfl | rfl
  · simpa only [one_mul] using hb
  · simpa only [neg_one_mul, neg_sub_neg, abs_sub_comm] using hb

/-- One actual polynomial interpolates every original canonical prefix in
any bounded list of distinct touching clusters. The square-coordinate
function has all derivatives through `k` bounded on the actual cutoff window.
The constant precedes the carrier, block, ray, list, and prescribed data. -/
theorem exists_uniform_canonicalBlock_polynomialInterpolant (N q k : ℕ)
    {B d : ℝ} (hB : 1 ≤ B) (hd : 0 < d) (hdiam : (q : ℝ) * d ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : LocallyFiniteCarrier,
      ∀ horder : BoundedClusterOrder S d q, ∀ n : ℕ, n ≤ N →
      ∀ clusters : Fin n → CanonicalClusterIndex S d,
        Function.Injective clusters → ∀ b : ℕ, ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
        (∀ g, groupTouchesTripleBlock B
          (range (fun i => ε * horder.realClusterNode (clusters g) i)) b) →
        ∀ data : (g : Fin n) → Fin (horder.clusterSize (clusters g)) → ℂ,
          ∃ p : Polynomial.degreeLT ℂ (∑ g, horder.clusterSize (clusters g)),
            let h := fun t : ℝ => p.1.eval ((ε * t - ε * ((b : ℝ) * B) : ℝ) : ℂ)
            ContDiff ℝ ∞ h ∧
            (∀ g, ∀ i : Fin (horder.clusterSize (clusters g)),
              analyticDividedDifference
                (finiteNodeSequence (horder.realClusterNode (clusters g))) i
                (fun s => h (ε * s)) = data g i) ∧
            ‖Polynomial.degreeLTEquiv ℂ (∑ g, horder.clusterSize (clusters g)) p‖ ≤
              C * ‖data‖ ∧
            ∀ x ∈ Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8),
              ∀ j ≤ k, ‖iteratedDeriv j h x‖ ≤ C * ‖data‖ := by
  have hBpos : 0 < B := by linarith
  obtain ⟨C, hC, hinterp⟩ := exists_uniform_groupedPattern_centeredPolynomialInterpolant
    N q k (show 0 ≤ 3 * B by positivity) hd
  refine ⟨C, hC, ?_⟩
  intro S horder n hn clusters hinj b ε hε htouch data
  obtain ⟨p, hp, _⟩ := hinterp n hn (fun g => horder.clusterSize (clusters g))
    (fun g => horder.clusterSize_le (clusters g)) (ε * ((b : ℝ) * B))
    (fun g => horder.realClusterNode (clusters g))
    (horder.canonicalBlock_mem_groupedNodeConfigurations hd hBpos hdiam hε b
      clusters hinj htouch) data
  refine ⟨p, ?_, ?_, hp.2.1, ?_⟩
  · have hpoly : ContDiff ℝ ∞ (fun z : ℂ => p.1.eval z) := by
      simpa using (p.1.contDiff_aeval (𝕜 := ℂ) ∞).restrict_scalars ℝ
    exact hpoly.comp (Complex.ofRealCLM.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const))
  · intro g i
    have heq : (fun s : ℝ =>
        p.1.eval ((ε * (ε * s) - ε * ((b : ℝ) * B) : ℝ) : ℂ)) =
        (fun s : ℝ => p.1.eval ((s - ε * ((b : ℝ) * B) : ℝ) : ℂ)) := by
      rcases hε with rfl | rfl <;> simp only [one_mul, neg_one_mul, neg_neg]
    change analyticDividedDifference _ _ (fun s : ℝ =>
      p.1.eval ((ε * (ε * s) - ε * ((b : ℝ) * B) : ℝ) : ℂ)) = _
    rw [heq]
    exact hp.1 g i
  · intro x hx j hj
    change ‖iteratedDeriv j
      (fun t : ℝ => (fun s : ℝ => p.1.eval ((s - ε * ((b : ℝ) * B) : ℝ) : ℂ))
        (ε * t)) x‖ ≤ _
    exact (norm_iteratedDeriv_comp_sign
      (fun s : ℝ => p.1.eval ((s - ε * ((b : ℝ) * B) : ℝ) : ℂ)) j hε x).trans_le
      (hp.2.2 j hj (ε * x) (quadraticBlock_cutoff_mem_signedWindow hBpos b hε hx))

/-- Matching all actual prefixes at distinct nodes forces equality of the
original point values. This uses the genuine values-to-Newton equivalence. -/
theorem values_eq_of_analyticDividedDifference_prefix_eq {n : ℕ}
    (nodes : Fin n → ℝ) (hinj : Function.Injective nodes) (f g : ℝ → ℂ)
    (hdata : ∀ i : Fin n,
      analyticDividedDifference (finiteNodeSequence nodes) i f =
        analyticDividedDifference (finiteNodeSequence nodes) i g) :
    ∀ i, f (nodes i) = g (nodes i) := by
  have heq : (fun i => f (nodes i)) = (fun i => g (nodes i)) := by
    apply (valuesEquivDividedDifferencesOfInjective (fun i => (nodes i : ℂ))
      (Complex.ofReal_injective.comp hinj)).injective
    funext i
    exact (analyticDividedDifference_eq_dividedDifferences nodes hinj f i).symm.trans
      ((hdata i).trans (analyticDividedDifference_eq_dividedDifferences nodes hinj g i))
  exact congrFun heq

/-- In particular, assigning a function's canonical prefix data interpolates
its actual point values in their original signed-node order on either ray. -/
theorem BoundedClusterOrder.canonicalBlock_values_of_prefix_eq
    {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ}
    (horder : BoundedClusterOrder S d q) (C : CanonicalClusterIndex S d)
    (f h : ℝ → ℂ) (ε : ℝ)
    (hdata : ∀ i : Fin (horder.clusterSize C),
      analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) i
        (fun s => h (ε * s)) =
      analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) i f) :
    ∀ i, h (ε * horder.realClusterNode C i) = f (horder.realClusterNode C i) :=
  values_eq_of_analyticDividedDifference_prefix_eq _
    (horder.realClusterNode_strictMono C).injective _ _ hdata

/-- The finite grouped sup norm is controlled by the actual sum of squared
coefficient norms, with constant one, including the empty pattern. -/
theorem groupedData_norm_sq_le_sum {n : ℕ} (size : Fin n → ℕ)
    (data : (g : Fin n) → Fin (size g) → ℂ) :
    ‖data‖ ^ 2 ≤ ∑ g, ∑ i, ‖data g i‖ ^ 2 := by
  classical
  let E : ℝ := ∑ g, ∑ i, ‖data g i‖ ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun g _ =>
    Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hcoord (g : Fin n) (i : Fin (size g)) : ‖data g i‖ ^ 2 ≤ E := by
    exact (Finset.single_le_sum (fun i _ => sq_nonneg ‖data g i‖) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun g : Fin n => ∑ i : Fin (size g), ‖data g i‖ ^ 2)
        (fun g _ => Finset.sum_nonneg (fun i _ => sq_nonneg ‖data g i‖)) (Finset.mem_univ g))
  have hnorm : ‖data‖ ≤ Real.sqrt E := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg E)).mpr
    intro g
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg E)).mpr
    intro i
    nlinarith [hcoord g i, Real.sq_sqrt hE, Real.sqrt_nonneg E, norm_nonneg (data g i)]
  nlinarith [Real.sq_sqrt hE, norm_nonneg data, Real.sqrt_nonneg E]

/-- The actual local canonical interpolant satisfies the physical block
energy estimate in the squared coefficient norm. Both polynomial construction
and derivative control are conclusions; only the listed data are supplied. -/
theorem exists_uniform_canonicalBlock_interpolant_energy (N q k : ℕ)
    {B d : ℝ} (hB : 1 ≤ B) (hd : 0 < d) (hdiam : (q : ℝ) * d ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : LocallyFiniteCarrier,
      ∀ horder : BoundedClusterOrder S d q, ∀ n : ℕ, n ≤ N →
      ∀ clusters : Fin n → CanonicalClusterIndex S d,
        Function.Injective clusters → ∀ b : ℕ, 2 ≤ b →
        ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
        (∀ g, groupTouchesTripleBlock B
          (range (fun i => ε * horder.realClusterNode (clusters g) i)) b) →
        ∀ data : (g : Fin n) → Fin (horder.clusterSize (clusters g)) → ℂ,
          ∃ p : Polynomial.degreeLT ℂ (∑ g, horder.clusterSize (clusters g)),
            let h := fun t : ℝ => p.1.eval ((ε * t - ε * ((b : ℝ) * B) : ℝ) : ℂ)
            let f := quadraticBlockPiece B b (fun x : ℝ => h (x ^ 2))
            ContDiff ℝ ∞ h ∧
            (∀ g, ∀ i : Fin (horder.clusterSize (clusters g)),
              analyticDividedDifference
                (finiteNodeSequence (horder.realClusterNode (clusters g))) i
                (fun s => h (ε * s)) = data g i) ∧
            MeasureTheory.Integrable (fun x => |x| ^ (2 * k) * ‖f x‖ ^ 2) ∧
            MeasureTheory.Integrable (fun x => ‖iteratedDeriv k f x‖ ^ 2) ∧
            (∫ x : ℝ, |x| ^ (2 * k) * ‖f x‖ ^ 2) +
                (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2) ≤
              C * B * (((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) *
                (∑ g, ∑ i, ‖data g i‖ ^ 2) := by
  obtain ⟨CI, hCI, hinterp⟩ := exists_uniform_canonicalBlock_polynomialInterpolant N q k hB hd hdiam
  obtain ⟨CE, hCE, henergy⟩ := exists_uniform_quadraticBlock_energy_bound k
  refine ⟨CE * CI ^ 2, mul_pos hCE (sq_pos_of_pos hCI), ?_⟩
  intro S horder n hn clusters hinj b hb ε hε htouch data
  obtain ⟨p, hsmooth, hprefix, _hcoeff, hderiv⟩ :=
    hinterp S horder n hn clusters hinj b ε hε htouch data
  have he := henergy B hB b hb _ hsmooth (CI * ‖data‖)
    (mul_nonneg hCI.le (norm_nonneg _)) hderiv
  refine ⟨p, hsmooth, hprefix, he.1, he.2.1, ?_⟩
  calc
    _ ≤ CE * B * (((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) * (CI * ‖data‖) ^ 2 := he.2.2
    _ = (CE * CI ^ 2) * B * (((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) * ‖data‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (groupedData_norm_sq_le_sum _ data) (by positivity)

end

end MeyerGeneralProblem
