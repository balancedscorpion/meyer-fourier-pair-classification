module

public import MeyerGeneralProblem.Sampling.SignedSquareCutoffTransfer
public import MeyerGeneralProblem.Sampling.KNSGraphRepresentative

@[expose] public section

/-!
# Finite-regularity signed-square chart identities and limits

Exact finite derivative recursions and the cutoff neighborhood identity handle
both signs and the zero-extension region. Pointwise convergence of the actual
finite physical jets transfers to actual chart derivatives. The original graph
representative has Cq regularity whenever q+1 is at most its stored order.
-/

namespace MeyerGeneralProblem.SignedSquareFiniteChart
noncomputable section
open Filter Set
open scoped ContDiff Topology BigOperators

/-- Lower classical derivatives retain exactly the available finite regularity. -/
theorem contDiff_lower {h : ℝ → ℂ} {q n b : ℕ}
    (hh : ContDiff ℝ q h) (hnb : n+b ≤ q) :
    ContDiff ℝ n (iteratedDeriv b h) := by
  have he (m : ℕ) : iteratedDeriv m (iteratedDeriv b h) = iteratedDeriv (m+b) h := by
    simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]
  rw [contDiff_nat_iff_iteratedDeriv]
  constructor
  · intro m hm
    rw [he]
    exact hh.continuous_iteratedDeriv (m+b) (by exact_mod_cast (show m+b≤q by omega))
  · intro m hm
    rw [he]
    exact hh.differentiable_iteratedDeriv (m+b) (by exact_mod_cast (show m+b<q by omega))

/-- A monomial is only differentiated as far as the actual finite input allows. -/
theorem monomial_contDiffAt {h : ℝ → ℂ} {q n b : ℕ}
    (hh : ContDiff ℝ q h) (hnb : n+b≤q) (a ε : ℝ)
    {σ : ℝ} (hσ : 0<σ) :
    ContDiffAt ℝ n (signedSquareChartMonomial a ε b h) σ := by
  exact (Real.contDiffAt_rpow_const_of_ne hσ.ne').smul
    ((contDiff_lower hh hnb).contDiffAt.comp σ
      (contDiffAt_const.mul (Real.contDiffAt_sqrt (n := n) hσ.ne')))

/-- The exact recursive chart jet at every permitted finite order. -/
theorem monomial_iteratedDeriv {h : ℝ → ℂ} {q : ℕ} (hh : ContDiff ℝ q h)
    (n : ℕ) (a ε : ℝ) (b : ℕ) (hnb : n+b≤q)
    {σ : ℝ} (hσ : 0<σ) :
    iteratedDeriv n (signedSquareChartMonomial a ε b h) σ =
      signedSquareChartExpansion n a ε b h σ := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have heq : deriv (signedSquareChartMonomial a ε b h) =ᶠ[𝓝 σ]
        (fun s => a • signedSquareChartMonomial (a-1) ε b h s +
          (ε/2) • signedSquareChartMonomial (a-1/2) ε (b+1) h s) := by
      filter_upwards [Ioi_mem_nhds hσ] with s hs
      exact (hasDerivAt_signedSquareChartMonomial a ε b h hs
        (hh.differentiable_iteratedDeriv b (by exact_mod_cast (show b<q by omega)) _)).deriv
    rw [heq.iteratedDeriv_eq n]
    rw [iteratedDeriv_fun_add
      ((monomial_contDiffAt hh (show n+b≤q by omega) (a-1) ε hσ).const_smul a)
      ((monomial_contDiffAt hh (show n+(b+1)≤q by omega) (a-1/2) ε hσ).const_smul (ε/2))]
    simp only [iteratedDeriv_fun_const_smul_field]
    rw [ih _ _ (by omega), ih _ _ (by omega)]
    rfl

/-- The cutoff removes the singularity at every finite regularity order. -/
theorem cutoff_contDiff (k q : ℕ) {R : ℝ} (hR : 1<R)
    (ε : ℝ) {h : ℝ → ℂ} (hh : ContDiff ℝ q h) :
    ContDiff ℝ q (signedSquareCutoffChart k R ε h) := by
  rw [contDiff_iff_contDiffAt]
  intro σ
  by_cases hσ : 0<σ
  · exact ((contDiff_signedSquareTailCutoff R).of_le (by simp)).contDiffAt.smul
      (monomial_contDiffAt hh (by omega : q+0≤q) _ ε hσ)
  · have hσ' : σ<R^2-1 := by nlinarith
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hσ'] with t ht
    exact signedSquareCutoffChart_zero k R ε h ht.le

/-- At nonpositive chart arguments every derivative is zero by a genuine
neighborhood identity, independently of input regularity. -/
theorem cutoff_derivative_zero (k n : ℕ) {R : ℝ} (hR : 1<R)
    (ε : ℝ) (h : ℝ → ℂ) {σ : ℝ} (hσ : σ≤0) :
    iteratedDeriv n (signedSquareCutoffChart k R ε h) σ = 0 := by
  have hσ' : σ<R^2-1 := by nlinarith
  have heq : signedSquareCutoffChart k R ε h =ᶠ[𝓝 σ] (fun _ => (0 : ℂ)) := by
    filter_upwards [Iio_mem_nhds hσ'] with t ht
    exact signedSquareCutoffChart_zero k R ε h ht.le
  rw [heq.iteratedDeriv_eq n]
  exact iteratedDeriv_fun_const_zero

/-- Exact finite Leibniz formula for the actual cutoff chart, at a derivative
order independent of its physical weight index. -/
theorem cutoff_iteratedDeriv (k n q : ℕ) (R ε : ℝ)
    {h : ℝ → ℂ} (hh : ContDiff ℝ q h) (hn : n≤q)
    {σ : ℝ} (hσ : 0<σ) :
    iteratedDeriv n (signedSquareCutoffChart k R ε h) σ =
      ∑ i ∈ Finset.range (n+1), n.choose i •
        iteratedDeriv i (signedSquareTailCutoff R) σ •
        signedSquareChartExpansion (n-i) ((2*(k:ℝ)-1)/4) ε 0 h σ := by
  change iteratedDeriv n (fun t => signedSquareTailCutoff R t •
    signedSquareWeightedChart k ε h t) σ = _
  have hc : ContDiffAt ℝ n (signedSquareWeightedChart k ε h) σ :=
    monomial_contDiffAt hh (by omega : n+0≤q) ((2*(k:ℝ)-1)/4) ε hσ
  rw [iteratedDeriv_fun_real_smul (g := signedSquareWeightedChart k ε h)
    (((contDiff_signedSquareTailCutoff R).of_le (by simp)).contDiffAt) hc]
  apply Finset.sum_congr rfl
  intro i hi
  rw [signedSquareWeightedChart, monomial_iteratedDeriv hh _ _ _ _ (by omega) hσ]

/-- The explicit finite chart expansion respects convergence of its actual
physical jets at the pulled-back point, on either sign. -/
theorem expansion_tendsto {h : ℝ → ℂ} {u : ℕ → ℝ → ℂ} {q : ℕ}
    (hlim : ∀ j≤q, ∀ x, Tendsto (fun N => iteratedDeriv j (u N) x) atTop
      (𝓝 (iteratedDeriv j h x)))
    (n : ℕ) (a ε : ℝ) (b : ℕ) (hnb : n+b≤q) (σ : ℝ) :
    Tendsto (fun N => signedSquareChartExpansion n a ε b (u N) σ) atTop
      (𝓝 (signedSquareChartExpansion n a ε b h σ)) := by
  induction n generalizing a b with
  | zero =>
    exact (hlim b (by omega) (ε*Real.sqrt σ)).const_smul (σ^a)
  | succ n ih =>
    exact ((ih (a-1) b (by omega)).const_smul a).add
      ((ih (a-1/2) (b+1) (by omega)).const_smul (ε/2))

/-- Finite physical-jet convergence yields pointwise convergence of every
actual permitted chart derivative, including the zero-extension region. -/
theorem cutoff_derivative_tendsto (k q : ℕ) {R : ℝ} (hR : 1<R) (ε : ℝ)
    {h : ℝ → ℂ} {u : ℕ → ℝ → ℂ} (hh : ContDiff ℝ q h)
    (hu : ∀ N, ContDiff ℝ q (u N))
    (hlim : ∀ j≤q, ∀ x, Tendsto (fun N => iteratedDeriv j (u N) x) atTop
      (𝓝 (iteratedDeriv j h x)))
    (j : ℕ) (hj : j≤q) (σ : ℝ) :
    Tendsto (fun N => iteratedDeriv j (signedSquareCutoffChart k R ε (u N)) σ) atTop
      (𝓝 (iteratedDeriv j (signedSquareCutoffChart k R ε h) σ)) := by
  by_cases hσ : 0<σ
  · simp only [cutoff_iteratedDeriv k j q R ε hh hj hσ,
      cutoff_iteratedDeriv k j q R ε (hu _) hj hσ]
    apply tendsto_finsetSum
    intro i hi
    exact ((expansion_tendsto hlim (j-i) _ ε 0 (by omega) σ).const_smul
      (iteratedDeriv i (signedSquareTailCutoff R) σ)).const_smul (j.choose i)
  · simp only [cutoff_derivative_zero k j hR ε _ (le_of_not_gt hσ)]
    exact tendsto_const_nhds

end
end MeyerGeneralProblem.SignedSquareFiniteChart

namespace MeyerGeneralProblem.SignedSquareFiniteChart
noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform
/-- The actual graph representative has exactly every finite regularity order
strictly below the stored graph order, using only its genuine pure frequency weight. -/
theorem representative_contDiff {q k : ℕ} (hq : q+1≤k) (v : KNSGraphSpace k) :
    ContDiff ℝ q (KNSGraphSpace.representative k v) := by
  have hp : MemLp (fun x : ℝ => (x : ℂ)^k * KNSGraphSpace.frequency k v x) 2 :=
    (memLp_congr_ae (KNSGraphSpace.frequencyWeight_ae v)).mpr (Lp.memLp _)
  have hK := memLp_fourierDerivativeData_of_physical_power k hp
  have hm : ∀ j≤q, Integrable (fun x : ℝ => x^j • KNSGraphSpace.frequency k v x) :=
    fun j hj => integrable_real_moment_of_fourierSobolev (Lp.memLp _) hK (by omega)
  have hF := contDiff_fourier_of_integrable_moments_le hm
  exact hF.comp (by fun_prop : ContDiff ℝ q (fun x : ℝ => -x))
end
end MeyerGeneralProblem.SignedSquareFiniteChart
