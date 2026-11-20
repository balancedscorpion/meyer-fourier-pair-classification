module

public import MeyerGeneralProblem.Gram.GroupedDifferentiatedAsymptotics
public import MeyerGeneralProblem.Trace.GroupedTrace
public import MeyerGeneralProblem.Sampling.GroupedExponential
public import MeyerGeneralProblem.Interpolation.BlockPartition
public import MeyerGeneralProblem.Gram.UniversalOperator

@[expose] public section

/-!
# Actual grouped Gram kernels and two-variable divided differences

The source family uses a single Dirac norm per cluster, not separate
normalization at each node. The exact finite Gram identity below retains
those two anchor norms. Gap-independent estimates are obtained from actual
Hermite–Genocchi integrals, not from the absolute barycentric weights.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped Topology
open Finset

/-- Real barycentric weights remain real after inclusion into the complex
field. This discharges the conjugation in an actual Hilbert Gram entry. -/
theorem groupedNewtonWeight_ofReal {n : ℕ} (nodes : Fin n → ℝ) (j i : Fin n) :
    groupedNewtonWeight (fun k => (nodes k : ℂ)) j i =
      ((groupedNewtonWeight (K := ℝ) nodes j i) : ℂ) := by
  simp only [groupedNewtonWeight,Lagrange.nodalWeight]
  split_ifs <;> simp

/-- Negating every node changes an order-`j` barycentric weight by exactly
`(-1)^j`; this is the negative-ray coordinate orientation factor. -/
theorem groupedNewtonWeight_neg {n : ℕ} (nodes : Fin n → ℝ) (j i : Fin n) :
    groupedNewtonWeight (fun k => -nodes k) j i = (-1:ℝ)^j.val * groupedNewtonWeight nodes j i := by
  unfold groupedNewtonWeight
  split_ifs with hij
  · unfold Lagrange.nodalWeight
    have heq (k : Fin n) : (-nodes i - -nodes k)⁻¹ = (-1:ℝ)*(nodes i-nodes k)⁻¹ := by
      rw [show -nodes i - -nodes k = -(nodes i-nodes k) by ring, inv_neg]
      ring
    simp_rw [heq]
    rw [prod_mul_distrib,prod_const,card_erase_of_mem (mem_Iic.mpr hij),Fin.card_Iic,Nat.add_sub_cancel]
  · simp

theorem groupedNewtonWeight_sign {n : ℕ} (nodes : Fin n → ℝ) (j i : Fin n)
    (ε : ℝ) (hε : ε^2=1) :
    groupedNewtonWeight (fun k => ε*nodes k) j i = ε^j.val * groupedNewtonWeight nodes j i := by
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simp
  · simpa only [neg_one_mul] using groupedNewtonWeight_neg nodes j i

/-- A genuine real-node divided difference, as an explicit finite sum. -/
def groupedRealDividedDifference {n : ℕ} (nodes : Fin n → ℝ) (j : Fin n)
    (f : ℝ → ℂ) : ℂ := ∑ i, (groupedNewtonWeight (K := ℝ) nodes j i : ℂ) * f (nodes i)

/-- Exact identification with the analytic Newton/HG construction at the
actual distinct nodes; it is independent of function regularity. -/
theorem groupedRealDividedDifference_eq_analytic {n : ℕ} (nodes : Fin n → ℝ)
    (hnodes : Function.Injective nodes) (j : Fin n) (f : ℝ → ℂ) :
    groupedRealDividedDifference nodes j f =
      analyticDividedDifference (finiteNodeSequence nodes) j f := by
  rw [analyticDividedDifference_eq_dividedDifferences nodes hnodes f j,
    dividedDifferences_eq_groupedNewtonWeights]
  simp only [groupedRealDividedDifference,groupedNewtonWeight_ofReal]

/-- Actual double divided difference in the two lists of distinct real
nodes. The first index is the row/first-variable derivative order. -/
def groupedDoubleDividedDifference {n k : ℕ} (nodes : Fin n → ℝ) (other : Fin k → ℝ)
    (i : Fin n) (j : Fin k) (K : ℝ → ℝ → ℂ) : ℂ :=
  groupedRealDividedDifference nodes i (fun s => groupedRealDividedDifference other j (K s))

theorem groupedDoubleDividedDifference_sum {n k : ℕ} (nodes : Fin n → ℝ) (other : Fin k → ℝ)
    (i : Fin n) (j : Fin k) (K : ℝ → ℝ → ℂ) :
    groupedDoubleDividedDifference nodes other i j K =
      ∑ a, ∑ b, (groupedNewtonWeight (K := ℝ) nodes i a : ℂ) *
        (groupedNewtonWeight (K := ℝ) other j b : ℂ) * K (nodes a) (other b) := by
  simp only [groupedDoubleDividedDifference,groupedRealDividedDifference,mul_sum,mul_assoc]

theorem groupedDoubleDividedDifference_nodes_sign {n k : ℕ}
    (nodes : Fin n → ℝ) (other : Fin k → ℝ) (i : Fin n) (j : Fin k)
    (K : ℝ → ℝ → ℂ) (ε η : ℝ) (hε : ε^2=1) (hη : η^2=1) :
    groupedDoubleDividedDifference (fun a => ε*nodes a) (fun b => η*other b) i j K =
      (ε^i.val*η^j.val) • groupedDoubleDividedDifference nodes other i j (fun s t => K (ε*s) (η*t)) := by
  simp only [groupedDoubleDividedDifference_sum,groupedNewtonWeight_sign nodes i _ ε hε,
    groupedNewtonWeight_sign other j _ η hη,Complex.ofReal_mul,smul_sum,Complex.real_smul]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  ring

theorem norm_groupedDoubleDividedDifference_nodes_sign {n k : ℕ}
    (nodes : Fin n → ℝ) (other : Fin k → ℝ) (i : Fin n) (j : Fin k)
    (K : ℝ → ℝ → ℂ) (ε η : ℝ) (hε : ε^2=1) (hη : η^2=1) :
    ‖groupedDoubleDividedDifference (fun a => ε*nodes a) (fun b => η*other b) i j K‖ =
      ‖groupedDoubleDividedDifference nodes other i j (fun s t => K (ε*s) (η*t))‖ := by
  rw [groupedDoubleDividedDifference_nodes_sign nodes other i j K ε η hε hη,norm_smul,norm_mul,norm_pow,norm_pow]
  have heps : ‖ε‖=1 := by rw [Real.norm_eq_abs]; nlinarith [sq_abs ε,abs_nonneg ε]
  have heta : ‖η‖=1 := by rw [Real.norm_eq_abs]; nlinarith [sq_abs η,abs_nonneg η]
  simp only [heps,heta,one_pow,one_mul]

theorem groupedDoubleDividedDifference_sub {n k : ℕ}
    (nodes : Fin n → ℝ) (other : Fin k → ℝ) (i : Fin n) (j : Fin k) (K L : ℝ → ℝ → ℂ) :
    groupedDoubleDividedDifference nodes other i j (fun s t => K s t-L s t) =
      groupedDoubleDividedDifference nodes other i j K - groupedDoubleDividedDifference nodes other i j L := by
  simp only [groupedDoubleDividedDifference_sum,mul_sub,sum_sub_distrib]

theorem groupedDoubleDividedDifference_congr_values {n k : ℕ}
    (nodes : Fin n → ℝ) (other : Fin k → ℝ) (i : Fin n) (j : Fin k)
    (K L : ℝ → ℝ → ℂ) (h : ∀ a b, K (nodes a) (other b)=L (nodes a) (other b)) :
    groupedDoubleDividedDifference nodes other i j K=groupedDoubleDividedDifference nodes other i j L := by
  simp only [groupedDoubleDividedDifference_sum,h]

theorem groupedDoubleDividedDifference_eq_analytic {n k : ℕ}
    (nodes : Fin n → ℝ) (other : Fin k → ℝ)
    (hnodes : Function.Injective nodes) (hother : Function.Injective other)
    (i : Fin n) (j : Fin k) (K : ℝ → ℝ → ℂ) :
    groupedDoubleDividedDifference nodes other i j K =
      analyticDividedDifference (finiteNodeSequence nodes) i (fun s =>
        analyticDividedDifference (finiteNodeSequence other) j (K s)) := by
  simp only [groupedDoubleDividedDifference,groupedRealDividedDifference_eq_analytic nodes hnodes,
    groupedRealDividedDifference_eq_analytic other hother]

/-- Derivatives pass through the actual finite divided-difference sum.
No inverse-gap estimate is used here. -/
theorem iteratedDeriv_groupedRealDividedDifference_param {n : ℕ}
    (nodes : Fin n → ℝ) (j : Fin n) (K : ℝ → ℝ → ℂ) (i : ℕ) (s : ℝ)
    (hK : ∀ a, ContDiffAt ℝ i (fun x => K x (nodes a)) s) :
    iteratedDeriv i (fun x => groupedRealDividedDifference nodes j (K x)) s =
      groupedRealDividedDifference nodes j (fun y => iteratedDeriv i (fun x => K x y) s) := by
  unfold groupedRealDividedDifference
  change iteratedDeriv i (fun x => ∑ a, (groupedNewtonWeight (K := ℝ) nodes j a : ℂ) • K x (nodes a)) s =
    ∑ a, (groupedNewtonWeight (K := ℝ) nodes j a : ℂ) • iteratedDeriv i (fun x => K x (nodes a)) s
  rw [iteratedDeriv_fun_sum (fun a _ => (hK a).const_smul (groupedNewtonWeight (K := ℝ) nodes j a : ℂ))]
  simp only [iteratedDeriv_fun_const_smul_field]

/-- A genuine two-variable HG estimate with the exact two factorials.
It is uniform under arbitrary collision limits of the distinct node lists. -/
theorem norm_groupedDoubleDividedDifference_le {n k : ℕ}
    (nodes : Fin n → ℝ) (other : Fin k → ℝ)
    (hnodes : Function.Injective nodes) (hother : Function.Injective other)
    (i : Fin n) (j : Fin k) (K : ℝ → ℝ → ℂ)
    (hleft : ∀ y, ContDiff ℝ i (fun x => K x y))
    (hright : ∀ x, ContDiff ℝ j (fun y => iteratedDeriv i (fun z => K z y) x))
    {L U V W M : ℝ}
    (hnode : ∀ a, nodes a ∈ Set.Icc L U) (hoth : ∀ b, other b ∈ Set.Icc V W)
    (hbound : ∀ x ∈ Set.Icc L U, ∀ y ∈ Set.Icc V W,
      ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => K u v) x) y‖ ≤ M) :
    ‖groupedDoubleDividedDifference nodes other i j K‖ ≤
      (M / (j.val.factorial : ℝ)) / (i.val.factorial : ℝ) := by
  unfold groupedDoubleDividedDifference
  rw [groupedRealDividedDifference_eq_analytic nodes hnodes]
  have hreg : ContDiff ℝ i (fun x => groupedRealDividedDifference other j (K x)) := by
    unfold groupedRealDividedDifference
    apply ContDiff.sum
    intro b _
    exact (hleft (other b)).const_smul (groupedNewtonWeight (K := ℝ) other j b : ℂ)
  apply norm_analyticDividedDifference_le_of_contDiff _ _ hreg
    (fun a ha => by simpa only [finiteNodeSequence,dite_eq_left (ha.trans_lt i.isLt)] using hnode ⟨a,ha.trans_lt i.isLt⟩)
  intro x hx
  rw [iteratedDeriv_groupedRealDividedDifference_param other j K i x (fun b => (hleft (other b)).contDiffAt),
    groupedRealDividedDifference_eq_analytic other hother]
  exact norm_analyticDividedDifference_le_of_contDiff _ _ (hright x)
    (fun b hb => by simpa only [finiteNodeSequence,dite_eq_left (hb.trans_lt j.isLt)] using hoth ⟨b,hb.trans_lt j.isLt⟩)
    (hbound x hx)

/-- A smooth positive coordinate map which is exactly the identity on
the tail. It is only an extension device for the global HG theorem. -/
def groupedPositiveExtension (x : ℝ) : ℝ :=
  (1-Real.smoothTransition (4*x-1)) + Real.smoothTransition (4*x-1)*x

theorem contDiff_groupedPositiveExtension (q : ℕ) : ContDiff ℝ q groupedPositiveExtension := by
  unfold groupedPositiveExtension
  have h : ContDiff ℝ q (fun x : ℝ => Real.smoothTransition (4*x-1)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  exact (contDiff_const.sub h).add (h.mul contDiff_id)

theorem groupedPositiveExtension_pos (x : ℝ) : 0 < groupedPositiveExtension x := by
  by_cases hx : x ≤ 1/4
  · unfold groupedPositiveExtension
    rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
    norm_num
  · have h0 := Real.smoothTransition.nonneg (4*x-1)
    have h1 := Real.smoothTransition.le_one (4*x-1)
    have hp : 0 ≤ Real.smoothTransition (4*x-1)*(x-1/4) := mul_nonneg h0 (by linarith)
    unfold groupedPositiveExtension
    nlinarith

theorem groupedPositiveExtension_eq {x : ℝ} (hx : 1/2 ≤ x) : groupedPositiveExtension x=x := by
  unfold groupedPositiveExtension
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem groupedPositiveExtension_eventuallyEq {x : ℝ} (hx : 1/2 < x) :
    groupedPositiveExtension =ᶠ[nhds x] id := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact groupedPositiveExtension_eq hy.le

/-- A local positive-ray HG estimate for the actual distinct-node sum.
The extension agrees with the function near the whole tested interval,
so both the values and the actual top derivative are unchanged. -/
theorem norm_groupedRealDividedDifference_le_positive {n : ℕ}
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes) (j : Fin n) (f : ℝ → ℂ)
    (hreg : ∀ x > 0, ContDiffAt ℝ j f x) {L U M : ℝ} (hL : 1 ≤ L)
    (hnode : ∀ a, nodes a ∈ Set.Icc L U)
    (hbound : ∀ x ∈ Set.Icc L U, ‖iteratedDeriv j f x‖ ≤ M) :
    ‖groupedRealDividedDifference nodes j f‖ ≤ M/(j.val.factorial : ℝ) := by
  let g : ℝ → ℂ := fun x => f (groupedPositiveExtension x)
  have hg : ContDiff ℝ j g := contDiff_iff_contDiffAt.mpr (fun x =>
    (hreg _ (groupedPositiveExtension_pos x)).comp x (contDiff_groupedPositiveExtension j).contDiffAt)
  have heq : groupedRealDividedDifference nodes j f = groupedRealDividedDifference nodes j g := by
    unfold groupedRealDividedDifference
    apply sum_congr rfl
    intro a _
    dsimp [g]
    rw [groupedPositiveExtension_eq (by linarith [(hnode a).1])]
  rw [heq,groupedRealDividedDifference_eq_analytic nodes hnodes]
  apply norm_analyticDividedDifference_le_of_contDiff _ _ hg
    (fun a ha => by simpa only [finiteNodeSequence,dite_eq_left (ha.trans_lt j.isLt)] using hnode ⟨a,ha.trans_lt j.isLt⟩)
  intro x hx
  have he : g =ᶠ[nhds x] f := by
    filter_upwards [groupedPositiveExtension_eventuallyEq (show 1/2 < x by linarith [hx.1])] with y hy
    dsimp [g]
    rw [hy]
    rfl
  rw [he.iteratedDeriv_eq]
  exact hbound x hx

/-- Two-variable HG on actual tail nodes. Only actual positive-ray
smoothness is required, and the two reciprocal factorials are exact. -/
theorem norm_groupedDoubleDividedDifference_le_positive {n k : ℕ}
    (nodes : Fin n → ℝ) (other : Fin k → ℝ)
    (hnodes : Function.Injective nodes) (hother : Function.Injective other)
    (i : Fin n) (j : Fin k) (K : ℝ → ℝ → ℂ)
    (hleft : ∀ x y : ℝ, 0 < x → 0 < y → ContDiffAt ℝ i (fun z => K z y) x)
    (hright : ∀ x y : ℝ, 0 < x → 0 < y →
      ContDiffAt ℝ j (fun v => iteratedDeriv i (fun u => K u v) x) y)
    {L U V W M : ℝ} (hL : 1 ≤ L) (hV : 1 ≤ V)
    (hnode : ∀ a, nodes a ∈ Set.Icc L U) (hoth : ∀ b, other b ∈ Set.Icc V W)
    (hbound : ∀ x ∈ Set.Icc L U, ∀ y ∈ Set.Icc V W,
      ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => K u v) x) y‖ ≤ M) :
    ‖groupedDoubleDividedDifference nodes other i j K‖ ≤
      (M / (j.val.factorial : ℝ)) / (i.val.factorial : ℝ) := by
  unfold groupedDoubleDividedDifference
  apply norm_groupedRealDividedDifference_le_positive nodes hnodes i _
    (fun x hx => by
      unfold groupedRealDividedDifference
      apply ContDiffAt.sum
      intro b _
      exact (hleft x (other b) hx (by linarith [(hoth b).1])).const_smul
        (groupedNewtonWeight (K := ℝ) other j b : ℂ)) hL hnode
  intro x hx
  rw [iteratedDeriv_groupedRealDividedDifference_param other j K i x
    (fun b => hleft x (other b) (by linarith [hx.1]) (by linarith [(hoth b).1]))]
  exact norm_groupedRealDividedDifference_le_positive other hother j _
    (fun y hy => hright x y (by linarith [hx.1]) hy) hV hoth (hbound x hx)

namespace OrderedCarrierGrouping

variable {S : LocallyFiniteCarrier} {κ : Type*} (G : OrderedCarrierGrouping S κ)

/-- Real signed-square nodes of an actual cluster. -/
def realNodes (C : κ) (i : Fin (G.size C)) : ℝ := signedSquare (G.point C i)

theorem realNodes_injective (C : κ) : Function.Injective (G.realNodes C) := (G.strictMono C).injective

/-- The actual grouped Hilbert Gram kernel, prior to asserting Bessel
boundedness or any infinite-dimensional Gram operator. -/
def gramKernel (m : ℕ) (hm : 1 ≤ m) (x y : G.Index) : ℂ :=
  inner ℂ (G.atom m hm x) (G.atom m hm y)

/-- The source's exact two-anchor-normalized finite Gram formula. This
retains the raw kernel and does not substitute divided differences of Γ. -/
theorem gramKernel_eq_weighted_sum (m : ℕ) (hm : 1 ≤ m)
    (C D : κ) (i : Fin (G.size C)) (j : Fin (G.size D)) :
    G.gramKernel m hm ⟨C,i⟩ ⟨D,j⟩ =
      ((G.weight m hm C)⁻¹ : ℂ) * ((G.weight m hm D)⁻¹ : ℂ) *
        ∑ a, ∑ b, (groupedNewtonWeight (K := ℝ) (G.realNodes C) i a : ℂ) *
          (groupedNewtonWeight (K := ℝ) (G.realNodes D) j b : ℂ) *
          hermiteResolventKernel m (G.point C a) (G.point D b) := by
  simp only [gramKernel,atom,rawAtom,groupedFiniteAtom,inner_smul_left,inner_smul_right,
    inner_sum, sum_inner,
    map_inv₀, Complex.conj_ofReal, inner_hermitePointMass_eq_resolventKernel,
    mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  have hC := groupedNewtonWeight_ofReal (G.realNodes C) i a
  have hD := groupedNewtonWeight_ofReal (G.realNodes D) j b
  change groupedNewtonWeight (G.nodes C) i a = _ at hC
  change groupedNewtonWeight (G.nodes D) j b = _ at hD
  rw [hC,hD,Complex.conj_ofReal]
  ring

end OrderedCarrierGrouping

/-- The actual point-mass norm decreases with signed-square magnitude.
This follows directly from the positive Laplace integral. -/
theorem groupedMagnitudeNormalizer_antitone (m : ℕ) (hm : 1 ≤ m)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖hermitePointMass m hm (Real.sqrt b)‖ ≤ ‖hermitePointMass m hm (Real.sqrt a)‖ := by
  have hD : groupedHermiteDiagonalMoment m 0 b ≤ groupedHermiteDiagonalMoment m 0 a := by
    unfold groupedHermiteDiagonalMoment
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply MeasureTheory.setIntegral_mono_on
      (integrable_groupedHermiteDiagonalMomentIntegrand m hm 0 b)
      (integrable_groupedHermiteDiagonalMomentIntegrand m hm 0 a) measurableSet_Ioi
    intro t ht
    simp only [groupedHermiteDiagonalMomentIntegrand,pow_zero,one_mul]
    apply mul_le_mul_of_nonneg_left _ (hermiteResolventDiagonalIntegrand_nonneg m 0 ht)
    apply Real.exp_le_exp.mpr
    nlinarith [groupedHermiteDiagonalRate_nonneg ht]
  rw [groupedHermiteDiagonalMoment_zero_eq_norm_sq m hm (ha.trans hab),
    groupedHermiteDiagonalMoment_zero_eq_norm_sq m hm ha] at hD
  nlinarith [norm_nonneg (hermitePointMass m hm (Real.sqrt a)),norm_nonneg (hermitePointMass m hm (Real.sqrt b))]

/-- The exact ratio restoring point normalization before division by the
one-per-cluster anchor norm. -/
def groupedNormalizerRatio (m : ℕ) (hm : 1 ≤ m) (a s : ℝ) : ℝ :=
  ‖hermitePointMass m hm (Real.sqrt a)‖⁻¹ * ‖hermitePointMass m hm (Real.sqrt s)‖

theorem groupedNormalizerRatio_pos (m : ℕ) (hm : 1 ≤ m) (a s : ℝ) :
    0 < groupedNormalizerRatio m hm a s := by
  unfold groupedNormalizerRatio
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (hermitePointMass_ne_zero m hm _)))
    (norm_pos_iff.mpr (hermitePointMass_ne_zero m hm _))

theorem groupedNormalizerRatio_le_one (m : ℕ) (hm : 1 ≤ m)
    {a s : ℝ} (ha : 0 ≤ a) (has : a ≤ s) : groupedNormalizerRatio m hm a s ≤ 1 := by
  unfold groupedNormalizerRatio
  rw [inv_mul_le_iff₀ (norm_pos_iff.mpr (hermitePointMass_ne_zero m hm _)),mul_one]
  exact groupedMagnitudeNormalizer_antitone m hm ha has

theorem groupedNormalizerRatio_self (m : ℕ) (hm : 1 ≤ m) (a : ℝ) :
    groupedNormalizerRatio m hm a a=1 := by
  unfold groupedNormalizerRatio
  exact inv_mul_cancel₀ (norm_pos_iff.mpr (hermitePointMass_ne_zero m hm _)).ne'

theorem contDiffAt_groupedNormalizerRatio (m : ℕ) (hm : 1 ≤ m) (q : ℕ) (a s : ℝ) (hs : 0 < s) :
    ContDiffAt ℝ q (groupedNormalizerRatio m hm a) s := by
  change ContDiffAt ℝ q (fun z => ‖hermitePointMass m hm (Real.sqrt a)‖⁻¹ •
    ‖hermitePointMass m hm (Real.sqrt z)‖) s
  exact (contDiffAt_norm_hermitePointMass_sqrt m hm q hs).const_smul _

/-- Every actual derivative of the anchor ratio has the same inverse
power bound as the norm; the ratio itself is at most one on the group hull. -/
theorem norm_iteratedDeriv_groupedNormalizerRatio_le (m : ℕ) (hm : 1 ≤ m)
    (q k : ℕ) (hk : k ≤ q) {a s : ℝ} (ha : 1 ≤ a) (has : a ≤ s) :
    ‖iteratedDeriv k (groupedNormalizerRatio m hm a) s‖ ≤
      groupedNormalizerDerivativeConstant m q / a^k := by
  have hn : 0 < ‖hermitePointMass m hm (Real.sqrt a)‖ := norm_pos_iff.mpr (hermitePointMass_ne_zero m hm _)
  have hs : 1 ≤ s := ha.trans has
  have h := (groupedHermiteRayNormalizer_derivative_bounds m hm q k hk 1 s (by norm_num) (by simpa using hs)).1
  rw [groupedHermiteRayNormalizer_one_fun,abs_of_pos (by linarith : 0 < s)] at h
  change ‖iteratedDeriv k (fun z => ‖hermitePointMass m hm (Real.sqrt a)‖⁻¹ •
    ‖hermitePointMass m hm (Real.sqrt z)‖) s‖ ≤ _
  rw [iteratedDeriv_fun_const_smul_field,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
  calc
    _ ≤ ‖hermitePointMass m hm (Real.sqrt a)‖⁻¹ *
        ((groupedNormalizerDerivativeConstant m q / s^k)*‖hermitePointMass m hm (Real.sqrt s)‖) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hn.le)
    _ = (groupedNormalizerDerivativeConstant m q / s^k)*groupedNormalizerRatio m hm a s := by
      unfold groupedNormalizerRatio; ring
    _ ≤ groupedNormalizerDerivativeConstant m q / s^k :=
      mul_le_of_le_one_right (by positivity [groupedNormalizerDerivativeConstant_pos m hm q])
        (groupedNormalizerRatio_le_one m hm (by linarith) has)
    _ ≤ groupedNormalizerDerivativeConstant m q / a^k := by
      apply div_le_div_of_nonneg_left (groupedNormalizerDerivativeConstant_pos m hm q).le (by positivity)
      exact pow_le_pow_left₀ (by linarith) has k

/-- The genuine anchor correction tends to one uniformly on a fixed
diameter tail group. This estimate is needed before the raw grouped Gram
can be replaced by grouped differences of the normalized kernel. -/
theorem norm_groupedNormalizerRatio_sub_one_le (m : ℕ) (hm : 1 ≤ m)
    {a s D : ℝ} (ha : 1 ≤ a) (has : a ≤ s) (hsD : s ≤ a+D) :
    ‖groupedNormalizerRatio m hm a s-1‖ ≤
      (groupedNormalizerDerivativeConstant m 1 / a)*D := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := groupedNormalizerRatio m hm a) (s := Set.Icc a s)
    (fun x hx => (contDiffAt_groupedNormalizerRatio m hm 1 a x (by linarith [hx.1])).differentiableAt (by norm_num))
    (C := groupedNormalizerDerivativeConstant m 1 / a)
    (fun x hx => by simpa only [iteratedDeriv_one,pow_one] using
      norm_iteratedDeriv_groupedNormalizerRatio_le m hm 1 1 le_rfl ha hx.1)
    (convex_Icc _ _) (Set.left_mem_Icc.mpr has) (Set.right_mem_Icc.mpr has)
  rw [groupedNormalizerRatio_self,Real.norm_of_nonneg (sub_nonneg.mpr has)] at h
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity [groupedNormalizerDerivativeConstant_pos m hm 1]))

/-- The genuine raw Hermite kernel divided by the two anchor norms.
Both anchors are positive magnitudes; the signs select physical rays. -/
def groupedAnchorNormalizedKernel (m : ℕ) (hm : 1 ≤ m) (ε η a b s t : ℝ) : ℂ :=
  (‖hermitePointMass m hm (Real.sqrt a)‖⁻¹ * ‖hermitePointMass m hm (Real.sqrt b)‖⁻¹) •
    hermiteResolventKernel m (ε*Real.sqrt s) (η*Real.sqrt t)

/-- Exact source-normalized same-side kernel remainder. -/
def groupedAnchorHermiteRemainder (m : ℕ) (hm : 1 ≤ m) (ε a b s t : ℝ) : ℂ :=
  groupedAnchorNormalizedKernel m hm ε ε a b s t - universalGramKernel m (ε*(t-s))

theorem norm_hermitePointMass_sign_sqrt (m : ℕ) (hm : 1 ≤ m) (ε s : ℝ) (hε : ε^2=1) :
    ‖hermitePointMass m hm (ε*Real.sqrt s)‖=‖hermitePointMass m hm (Real.sqrt s)‖ := by
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simp
  · simp only [neg_one_mul,norm_hermitePointMass_neg]

/-- Restoring the two point norms is exact; the source-normalized kernel
is the product of the two genuine anchor ratios and the normalized kernel. -/
theorem groupedAnchorNormalizedKernel_eq_ratios (m : ℕ) (hm : 1 ≤ m)
    (ε η a b s t : ℝ) (hε : ε^2=1) (hη : η^2=1) :
    groupedAnchorNormalizedKernel m hm ε η a b s t =
      (groupedNormalizerRatio m hm a s * groupedNormalizerRatio m hm b t) •
        groupedMagnitudeNormalizedKernel m hm ε η s t := by
  unfold groupedAnchorNormalizedKernel groupedMagnitudeNormalizedKernel
  rw [normalizedHermiteGramKernel_eq_resolventKernel,
    norm_hermitePointMass_sign_sqrt m hm ε s hε,norm_hermitePointMass_sign_sqrt m hm η t hη]
  unfold groupedNormalizerRatio
  rw [← Complex.real_smul,smul_smul]
  congr 1
  have hs := (norm_pos_iff.mpr (hermitePointMass_ne_zero m hm (Real.sqrt s))).ne'
  have ht := (norm_pos_iff.mpr (hermitePointMass_ne_zero m hm (Real.sqrt t))).ne'
  field_simp

theorem groupedAnchorNormalizedKernel_eq_ray (m : ℕ) (hm : 1 ≤ m)
    (ε η a b s t : ℝ) (hε : ε^2=1) (hη : η^2=1) :
    groupedAnchorNormalizedKernel m hm ε η a b s t =
      (‖hermitePointMass m hm (Real.sqrt a)‖⁻¹ * ‖hermitePointMass m hm (Real.sqrt b)‖⁻¹) •
        hermiteResolventKernel m (groupedSignedSquareRayPoint ε (ε*s)) (groupedSignedSquareRayPoint η (η*t)) := by
  rw [groupedSignedSquareRayPoint_sign_mul ε s hε,groupedSignedSquareRayPoint_sign_mul η t hη]
  rfl

theorem iteratedDeriv_groupedAnchorNormalizedKernel_left (m : ℕ) (hm : 1 ≤ m)
    (i : ℕ) (ε η a b s t : ℝ) (hε : ε^2=1) (hη : η^2=1) :
    iteratedDeriv i (fun u => groupedAnchorNormalizedKernel m hm ε η a b u t) s =
      (‖hermitePointMass m hm (Real.sqrt a)‖⁻¹ * ‖hermitePointMass m hm (Real.sqrt b)‖⁻¹) •
        (ε^i • iteratedDeriv i (fun u => hermiteResolventKernel m
          (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η (η*t))) (ε*s)) := by
  simp_rw [groupedAnchorNormalizedKernel_eq_ray m hm ε η a b _ _ hε hη]
  rw [iteratedDeriv_fun_const_smul_field]
  congr 1
  exact grouped_iteratedDeriv_comp_sign (fun u => hermiteResolventKernel m
    (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η (η*t))) i ε s hε

theorem contDiffAt_groupedAnchorNormalizedKernel_left
    (q m : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (ε η a b s t : ℝ) (hε : ε^2=1) (hη : η^2=1) (hs : 0 < s) :
    ContDiffAt ℝ q (fun u => groupedAnchorNormalizedKernel m
      (by have := (le_max_left _ _).trans hm; omega) ε η a b u t) s := by
  simp_rw [groupedAnchorNormalizedKernel_eq_ray m _ ε η a b _ _ hε hη]
  apply ContDiffAt.const_smul
  exact (contDiffAt_hermiteResolventKernel_ray_left q m hm ε (ε*s)
    (groupedSignedSquareRayPoint η (η*t)) (by nlinarith [hε])).comp s
      (contDiffAt_const.mul contDiffAt_id)

theorem contDiffAt_iteratedDeriv_groupedAnchorNormalizedKernel_right
    (q m i : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q)
    (ε η a b s t : ℝ) (hε : ε^2=1) (hη : η^2=1) (hs : 0 < s) (ht : 0 < t) :
    ContDiffAt ℝ q (fun v => iteratedDeriv i (fun u => groupedAnchorNormalizedKernel m
      (by have := (le_max_left _ _).trans hm; omega) ε η a b u v) s) t := by
  simp_rw [iteratedDeriv_groupedAnchorNormalizedKernel_left m _ i ε η a b s _ hε hη]
  apply ContDiffAt.const_smul
  apply ContDiffAt.const_smul
  exact (contDiffAt_iteratedDeriv_hermiteResolventKernel_ray_right q m i hm hi ε η
    (ε*s) (η*t) (by nlinarith [hε]) (by nlinarith [hη])).comp t
      (contDiffAt_const.mul contDiffAt_id)

/-- All raw anchor-normalized derivatives are genuinely uniformly
bounded when both variables are beyond their anchors. The proof uses
the same-order weighted raw bound and monotonicity of the actual norm. -/
theorem exists_norm_mixedDeriv_groupedAnchorNormalizedKernel_le
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q) (hj : j ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε η : ℝ, ε^2=1 → η^2=1 → ∀ a b s t : ℝ,
      1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t →
      ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => groupedAnchorNormalizedKernel m
        (by have := (le_max_left _ _).trans hm; omega) ε η a b u v) s) t‖ ≤ C := by
  have hp : 1 ≤ m := by have := (le_max_left _ _).trans hm; omega
  obtain ⟨C,hC,hbound⟩ := exists_norm_iteratedDeriv_iteratedDeriv_hermiteResolventKernel_signedSquareRay_le_weighted
    q m i j hm hi hj
  refine ⟨C,hC,?_⟩
  intro ε η hε hη a b s t ha hb has hbt
  simp_rw [groupedAnchorNormalizedKernel_eq_ray m hp ε η a b _ _ hε hη]
  simp_rw [iteratedDeriv_fun_const_smul_field]
  rw [norm_smul,Real.norm_of_nonneg (by positivity),grouped_norm_mixedDeriv_comp_signs
    (fun u v => hermiteResolventKernel m (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v))
    i j ε η s t hε hη]
  have h := hbound ε η hε hη (ε*s) (η*t) (by nlinarith [hε]) (by nlinarith [hη])
  rw [groupedSignedSquareRayPoint_sign_mul ε s hε,groupedSignedSquareRayPoint_sign_mul η t hη,
    norm_hermitePointMass_sign_sqrt m hp ε s hε,norm_hermitePointMass_sign_sqrt m hp η t hη] at h
  calc
    _ ≤ (‖hermitePointMass m hp (Real.sqrt a)‖⁻¹*‖hermitePointMass m hp (Real.sqrt b)‖⁻¹)*
        (C*‖hermitePointMass m hp (Real.sqrt s)‖*‖hermitePointMass m hp (Real.sqrt t)‖) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = C*groupedNormalizerRatio m hp a s*groupedNormalizerRatio m hp b t := by
      unfold groupedNormalizerRatio; ring
    _ ≤ C := by
      exact (mul_le_of_le_one_right (by positivity [groupedNormalizerRatio_pos m hp a s])
        (groupedNormalizerRatio_le_one m hp (by linarith) hbt)).trans
        (mul_le_of_le_one_right hC.le (groupedNormalizerRatio_le_one m hp (by linarith) has))

theorem contDiffAt_groupedAnchorHermiteRemainder_left
    (q m : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (ε a b s t : ℝ) (hε : ε^2=1) (hs : 0 < s) :
    ContDiffAt ℝ q (fun u => groupedAnchorHermiteRemainder m
      (by have := (le_max_left _ _).trans hm; omega) ε a b u t) s := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  exact (contDiffAt_groupedAnchorNormalizedKernel_left q m hm ε ε a b s t hε hε hs).sub
    ((contDiff_grouped_universalGramKernel m q (by omega)).contDiffAt.comp s
      (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)))

theorem iteratedDeriv_groupedAnchorHermiteRemainder_left_eq
    (q m i : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q)
    (ε a b s t : ℝ) (hε : ε^2=1) (hs : 0 < s) :
    iteratedDeriv i (fun u => groupedAnchorHermiteRemainder m
      (by have := (le_max_left _ _).trans hm; omega) ε a b u t) s =
      iteratedDeriv i (fun u => groupedAnchorNormalizedKernel m
        (by have := (le_max_left _ _).trans hm; omega) ε ε a b u t) s -
      iteratedDeriv i (fun u => universalGramKernel m (ε*(t-u))) s := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  exact iteratedDeriv_sub
    ((contDiffAt_groupedAnchorNormalizedKernel_left q m hm ε ε a b s t hε hε hs).of_le (by exact_mod_cast hi))
    ((contDiff_grouped_universalGramKernel m i (by omega)).contDiffAt.comp s
      (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)))

theorem contDiffAt_iteratedDeriv_groupedAnchorHermiteRemainder_right
    (q m i : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q)
    (ε a b s t : ℝ) (hε : ε^2=1) (hs : 0 < s) (ht : 0 < t) :
    ContDiffAt ℝ q (fun v => iteratedDeriv i (fun u => groupedAnchorHermiteRemainder m
      (by have := (le_max_left _ _).trans hm; omega) ε a b u v) s) t := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  simp_rw [iteratedDeriv_groupedAnchorHermiteRemainder_left_eq q m i hm hi ε a b s _ hε hs]
  exact (contDiffAt_iteratedDeriv_groupedAnchorNormalizedKernel_right q m i hm hi ε ε a b s t hε hε hs ht).sub
    (contDiffAt_iteratedDeriv_grouped_universalMagnitude_right m q i (by omega) ε s t hε)

theorem mixedDeriv_groupedAnchorHermiteRemainder_eq
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q) (hj : j ≤ q)
    (ε a b s t : ℝ) (hε : ε^2=1) (hs : 0 < s) (ht : 0 < t) :
    iteratedDeriv j (fun v => iteratedDeriv i (fun u => groupedAnchorHermiteRemainder m
      (by have := (le_max_left _ _).trans hm; omega) ε a b u v) s) t =
      iteratedDeriv j (fun v => iteratedDeriv i (fun u => groupedAnchorNormalizedKernel m
        (by have := (le_max_left _ _).trans hm; omega) ε ε a b u v) s) t -
      iteratedDeriv j (fun v => iteratedDeriv i (fun u => universalGramKernel m (ε*(v-u))) s) t := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  simp_rw [iteratedDeriv_groupedAnchorHermiteRemainder_left_eq q m i hm hi ε a b s _ hε hs]
  exact iteratedDeriv_sub
    ((contDiffAt_iteratedDeriv_groupedAnchorNormalizedKernel_right q m i hm hi ε ε a b s t hε hε hs ht).of_le
      (by exact_mod_cast hj))
    (contDiffAt_iteratedDeriv_grouped_universalMagnitude_right m j i (by omega) ε s t hε)

theorem exists_norm_mixedDeriv_groupedAnchorHermiteRemainder_le
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q) (hj : j ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ε^2=1 → ∀ a b s t : ℝ,
      1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t →
      ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => groupedAnchorHermiteRemainder m
        (by have := (le_max_left _ _).trans hm; omega) ε a b u v) s) t‖ ≤ C := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  obtain ⟨C,hC,hbound⟩ := exists_norm_mixedDeriv_groupedAnchorNormalizedKernel_le q m i j hm hi hj
  refine ⟨C+groupedUniversalDerivativeBound m (j+i),add_nonneg hC.le (groupedUniversalDerivativeBound_nonneg m _),?_⟩
  intro ε hε a b s t ha hb has hbt
  rw [mixedDeriv_groupedAnchorHermiteRemainder_eq q m i j hm hi hj ε a b s t hε (by linarith) (by linarith)]
  refine (norm_sub_le _ _).trans (add_le_add (hbound ε ε hε hε a b s t ha hb has hbt) ?_)
  rw [norm_iteratedDeriv_iteratedDeriv_grouped_universalMagnitude m i j ε s t hε]
  exact norm_iteratedDeriv_universalGramKernel_le_groupedBound m (j+i) (by omega) _

/-- Exact value-level control of the source anchor correction. -/
theorem norm_groupedAnchorHermiteRemainder_le (m : ℕ) (hm : 1 ≤ m)
    (ε a b s t D : ℝ) (hε : ε^2=1) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hs : s ∈ Set.Icc a (a+D)) (ht : t ∈ Set.Icc b (b+D)) :
    ‖groupedAnchorHermiteRemainder m hm ε a b s t‖ ≤
      ‖groupedMagnitudeHermiteRemainder m hm ε s t‖ +
        (groupedNormalizerDerivativeConstant m 1/a)*D + (groupedNormalizerDerivativeConstant m 1/b)*D := by
  let A := groupedNormalizerRatio m hm a s
  let B := groupedNormalizerRatio m hm b t
  have hA0 : 0 ≤ A := (groupedNormalizerRatio_pos m hm a s).le
  have hB0 : 0 ≤ B := (groupedNormalizerRatio_pos m hm b t).le
  have hA1 : A ≤ 1 := groupedNormalizerRatio_le_one m hm (by linarith) hs.1
  have hB1 : B ≤ 1 := groupedNormalizerRatio_le_one m hm (by linarith) ht.1
  have hAB : A*B ≤ 1 := (mul_le_of_le_one_right hA0 hB1).trans hA1
  have heq : groupedAnchorHermiteRemainder m hm ε a b s t =
      (A*B) • groupedMagnitudeHermiteRemainder m hm ε s t +
      (A*B-1) • universalGramKernel m (ε*(t-s)) := by
    unfold groupedAnchorHermiteRemainder groupedMagnitudeHermiteRemainder
    rw [groupedAnchorNormalizedKernel_eq_ratios m hm ε ε a b s t hε hε]
    dsimp [A,B]
    simp only [Complex.ofReal_sub,Complex.ofReal_one]
    ring
  have hweight : |A*B-1| ≤ |A-1|+|B-1| := by
    rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hA1) (sub_nonneg.mpr hB1)]
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul,norm_smul,Real.norm_of_nonneg (mul_nonneg hA0 hB0),Real.norm_eq_abs]
  have hfirst := mul_le_of_le_one_left (norm_nonneg (groupedMagnitudeHermiteRemainder m hm ε s t)) hAB
  have hsecond := mul_le_of_le_one_right (abs_nonneg (A*B-1)) (norm_universalGramKernel_le_one hm (ε*(t-s)))
  have hwA := norm_groupedNormalizerRatio_sub_one_le m hm ha hs.1 hs.2
  have hwB := norm_groupedNormalizerRatio_sub_one_le m hm hb ht.1 ht.2
  rw [Real.norm_eq_abs] at hwA hwB
  dsimp [A,B] at hweight
  linarith

namespace OrderedCarrierGrouping

variable {S : LocallyFiniteCarrier} {κ : Type*} (G : OrderedCarrierGrouping S κ)

/-- Ray-oriented square magnitudes of the actual nodes. For the negative
ray this reverses their order, without reindexing any Newton prefix. -/
def magnitudeNodes (ε : ℝ) (C : κ) (i : Fin (G.size C)) : ℝ := ε*G.realNodes C i

/-- Square magnitude of the actual minimum-modulus anchor on a declared ray. -/
def anchorMagnitude (ε : ℝ) (C : κ) : ℝ := G.magnitudeNodes ε C (G.anchor C)

theorem magnitudeNodes_injective (ε : ℝ) (hε : ε^2=1) (C : κ) :
    Function.Injective (G.magnitudeNodes ε C) := by
  intro i j hij
  apply G.realNodes_injective C
  have he : ε ≠ 0 := by nlinarith
  exact mul_left_cancel₀ he hij

theorem realNodes_eq_sign_magnitudeNodes (ε : ℝ) (hε : ε^2=1) (C : κ) :
    G.realNodes C = fun i => ε*G.magnitudeNodes ε C i := by
  funext i
  dsimp [magnitudeNodes]
  rw [← mul_assoc,← pow_two,hε,one_mul]

theorem point_eq_sign_sqrt_magnitudeNodes (ε : ℝ) (hε : ε^2=1) (C : κ)
    (i : Fin (G.size C)) (hi : 0 ≤ G.magnitudeNodes ε C i) :
    (G.point C i : ℝ) = ε*Real.sqrt (G.magnitudeNodes ε C i) := by
  apply signedSquare_injective
  rw [← groupedSignedSquareRayPoint_sign_mul ε _ hε,
    signedSquare_groupedSignedSquareRayPoint hε (by
      simpa only [← mul_assoc,← pow_two,hε,one_mul] using hi)]
  have h := congrFun (G.realNodes_eq_sign_magnitudeNodes ε hε C) i
  exact h

theorem weight_eq_norm_sqrt_anchorMagnitude (m : ℕ) (hm : 1 ≤ m)
    (ε : ℝ) (hε : ε^2=1) (C : κ) (hC : 0 ≤ G.anchorMagnitude ε C) :
    G.weight m hm C = ‖hermitePointMass m hm (Real.sqrt (G.anchorMagnitude ε C))‖ := by
  unfold weight
  rw [G.point_eq_sign_sqrt_magnitudeNodes ε hε C (G.anchor C) hC]
  exact norm_hermitePointMass_sign_sqrt m hm ε _ hε

/-- The model grouped atom is an actual finite combination of the universal
`L²` atoms, with exactly the original signed-square Newton weights. -/
def universalAtom (m : ℕ) (hm : 1 ≤ m) (x : G.Index) :
    MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
  groupedFiniteAtom (G.nodes x.1)
    (fun a => universalGramAtom m hm (G.realNodes x.1 a)) x.2

/-- Actual Hilbert Gram entry of the source universal grouped family. -/
def universalGroupedGramKernel (m : ℕ) (hm : 1 ≤ m) (x y : G.Index) : ℂ :=
  inner ℂ (G.universalAtom m hm x) (G.universalAtom m hm y)

theorem universalGroupedGramKernel_eq_DD (m : ℕ) (hm : 1 ≤ m)
    (C D : κ) (i : Fin (G.size C)) (j : Fin (G.size D)) :
    G.universalGroupedGramKernel m hm ⟨C,i⟩ ⟨D,j⟩ =
      groupedDoubleDividedDifference (G.realNodes C) (G.realNodes D) i j
        (fun s t => universalGramKernel m (t-s)) := by
  simp only [universalGroupedGramKernel,universalAtom,groupedFiniteAtom,inner_sum,sum_inner,
    inner_smul_left,inner_smul_right,inner_universalGramAtom,groupedDoubleDividedDifference_sum,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  have hC := groupedNewtonWeight_ofReal (G.realNodes C) i a
  have hD := groupedNewtonWeight_ofReal (G.realNodes D) j b
  change groupedNewtonWeight (G.nodes C) i a = _ at hC
  change groupedNewtonWeight (G.nodes D) j b = _ at hD
  rw [hC,hD,Complex.conj_ofReal]
  ring

theorem gramKernel_eq_magnitude_DD (m : ℕ) (hm : 1 ≤ m)
    (ε η : ℝ) (hε : ε^2=1) (hη : η^2=1)
    (C D : κ) (i : Fin (G.size C)) (j : Fin (G.size D))
    (hC : ∀ a, 0 ≤ G.magnitudeNodes ε C a) (hD : ∀ b, 0 ≤ G.magnitudeNodes η D b) :
    G.gramKernel m hm ⟨C,i⟩ ⟨D,j⟩ =
      (ε^i.val*η^j.val) • groupedDoubleDividedDifference
        (G.magnitudeNodes ε C) (G.magnitudeNodes η D) i j
        (groupedAnchorNormalizedKernel m hm ε η (G.anchorMagnitude ε C) (G.anchorMagnitude η D)) := by
  rw [G.gramKernel_eq_weighted_sum, G.weight_eq_norm_sqrt_anchorMagnitude m hm ε hε C (hC _),
    G.weight_eq_norm_sqrt_anchorMagnitude m hm η hη D (hD _)]
  rw [G.realNodes_eq_sign_magnitudeNodes ε hε C, G.realNodes_eq_sign_magnitudeNodes η hη D]
  simp only [groupedNewtonWeight_sign _ _ _ ε hε,groupedNewtonWeight_sign _ _ _ η hη,
    groupedDoubleDividedDifference_sum,groupedAnchorNormalizedKernel,smul_sum,
    Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv,mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  rw [G.point_eq_sign_sqrt_magnitudeNodes ε hε C a (hC a),
    G.point_eq_sign_sqrt_magnitudeNodes η hη D b (hD b)]
  ring

/-- Exact source atom/model remainder, including the negative-ray unitary
orientation factors. No derivative of point normalization is substituted. -/
theorem gramRemainder_eq_magnitude_DD (m : ℕ) (hm : 1 ≤ m)
    (ε : ℝ) (hε : ε^2=1) (C D : κ) (i : Fin (G.size C)) (j : Fin (G.size D))
    (hC : ∀ a, 0 ≤ G.magnitudeNodes ε C a) (hD : ∀ b, 0 ≤ G.magnitudeNodes ε D b) :
    G.gramKernel m hm ⟨C,i⟩ ⟨D,j⟩ - G.universalGroupedGramKernel m hm ⟨C,i⟩ ⟨D,j⟩ =
      (ε^i.val*ε^j.val) • groupedDoubleDividedDifference
        (G.magnitudeNodes ε C) (G.magnitudeNodes ε D) i j
        (groupedAnchorHermiteRemainder m hm ε (G.anchorMagnitude ε C) (G.anchorMagnitude ε D)) := by
  rw [G.gramKernel_eq_magnitude_DD m hm ε ε hε hε C D i j hC hD,
    G.universalGroupedGramKernel_eq_DD,
    G.realNodes_eq_sign_magnitudeNodes ε hε C,G.realNodes_eq_sign_magnitudeNodes ε hε D,
    groupedDoubleDividedDifference_nodes_sign _ _ _ _ _ ε ε hε hε]
  unfold groupedAnchorHermiteRemainder
  simp_rw [mul_sub, groupedDoubleDividedDifference_sub, smul_sub]

theorem norm_gramRemainder_eq_magnitude_DD (m : ℕ) (hm : 1 ≤ m)
    (ε : ℝ) (hε : ε^2=1) (C D : κ) (i : Fin (G.size C)) (j : Fin (G.size D))
    (hC : ∀ a, 0 ≤ G.magnitudeNodes ε C a) (hD : ∀ b, 0 ≤ G.magnitudeNodes ε D b) :
    ‖G.gramKernel m hm ⟨C,i⟩ ⟨D,j⟩ - G.universalGroupedGramKernel m hm ⟨C,i⟩ ⟨D,j⟩‖ =
      ‖groupedDoubleDividedDifference
        (G.magnitudeNodes ε C) (G.magnitudeNodes ε D) i j
        (groupedAnchorHermiteRemainder m hm ε (G.anchorMagnitude ε C) (G.anchorMagnitude ε D))‖ := by
  rw [G.gramRemainder_eq_magnitude_DD m hm ε hε C D i j hC hD,norm_smul,norm_mul,norm_pow,norm_pow]
  have he : ‖ε‖=1 := by rw [Real.norm_eq_abs]; nlinarith [sq_abs ε,abs_nonneg ε]
  simp only [he,one_pow,one_mul]

/-- Both ray variables are independent in this exact norm identity. The
universal model remains in the original signed-square coordinates. -/
theorem norm_gramRemainder_eq_twoRay_DD (m : ℕ) (hm : 1 ≤ m)
    (ε η : ℝ) (hε : ε^2=1) (hη : η^2=1)
    (C D : κ) (i : Fin (G.size C)) (j : Fin (G.size D))
    (hC : ∀ a, 0 ≤ G.magnitudeNodes ε C a) (hD : ∀ b, 0 ≤ G.magnitudeNodes η D b) :
    ‖G.gramKernel m hm ⟨C,i⟩ ⟨D,j⟩ - G.universalGroupedGramKernel m hm ⟨C,i⟩ ⟨D,j⟩‖ =
      ‖groupedDoubleDividedDifference (G.magnitudeNodes ε C) (G.magnitudeNodes η D) i j
        (fun s t => groupedAnchorNormalizedKernel m hm ε η
          (G.anchorMagnitude ε C) (G.anchorMagnitude η D) s t - universalGramKernel m (η*t-ε*s))‖ := by
  rw [G.gramKernel_eq_magnitude_DD m hm ε η hε hη C D i j hC hD,
    G.universalGroupedGramKernel_eq_DD,
    G.realNodes_eq_sign_magnitudeNodes ε hε C,G.realNodes_eq_sign_magnitudeNodes η hη D,
    groupedDoubleDividedDifference_nodes_sign _ _ _ _ _ ε η hε hη,
    groupedDoubleDividedDifference_sub,← smul_sub,norm_smul,norm_mul,norm_pow,norm_pow]
  have he : ‖ε‖=1 := by rw [Real.norm_eq_abs]; nlinarith [sq_abs ε,abs_nonneg ε]
  have ht : ‖η‖=1 := by rw [Real.norm_eq_abs]; nlinarith [sq_abs η,abs_nonneg η]
  simp only [he,ht,one_pow,one_mul]

end OrderedCarrierGrouping

end

end MeyerGeneralProblem
