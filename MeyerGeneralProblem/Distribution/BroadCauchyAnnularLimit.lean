module

public import MeyerGeneralProblem.Distribution.BroadCauchyCompactAction

@[expose] public section

/-!
# Analytic continuation of the expanding Cauchy tails

The difference of two compact cutoffs vanishes near the origin. Its
Cauchy action is holomorphic throughout a disk about zero, and the
same tail bound applies to real and nonreal poles in that disk.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Metric Set
open scoped Topology

/-- Removing a single compact inner cutoff leaves an analytic tail across
the entire prescribed disk, with the same original Cauchy pairing off
the real line. -/
theorem exists_analytic_broadCauchyAnnularTail (T : TemperedDistribution ℝ ℂ)
    (q m : ℕ) (hT : HasSchwartzOrderBound T q) (hm : q < m)
    (R : ℝ) (N₀ : ℕ) (hR : 2 * R ≤ (N₀ : ℝ) + 1) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 R) ∧
      ∀ z ∈ ball 0 R, ∀ hz : z.im ≠ 0, broadCauchyPairing T q m hT hm z hz =
        H z + T (broadCauchySchwartzCut m z hz N₀) := by
  classical
  let F (N : ℕ) (z : ℂ) := T (broadCauchyAnnularCut m z N N₀)
  have hnorm {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) : ‖z‖ < R := by
    simpa only [mem_ball, dist_zero_right] using hz
  have hbase {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) : ‖z‖ < (N₀ : ℝ) + 1 := by
    linarith [hnorm hz, (norm_nonneg z)]
  obtain ⟨C, _, hC⟩ := norm_broadCauchyAnnularCut_action_le T q m hT hm
  have hunif (ε : ℝ) (hε : 0 < ε) : ∃ K : ℕ, ∀ z ∈ ball (0 : ℂ) R,
      ∀ N M : ℕ, K ≤ N → K ≤ M → dist (F N z) (F M z) < ε := by
    have ht : Tendsto (fun K : ℕ => C * compactSchwartzCutoffScale K) atTop (𝓝 0) := by
      simpa only [mul_zero] using compactSchwartzCutoffScale_tendsto.const_mul C
    obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually_lt_const hε)
    let L := max K N₀
    have hLN₀ : N₀ ≤ L := le_max_right _ _
    have hcast : (N₀ : ℝ) ≤ L := by exact_mod_cast hLN₀
    refine ⟨L, fun z hz N M hN hM => ?_⟩
    change dist (T (broadCauchyAnnularCut m z N N₀)) (T (broadCauchyAnnularCut m z M N₀)) < ε
    rw [dist_eq_norm, ← map_sub, broadCauchyAnnularCut_sub m z N₀ N M N₀ (hbase hz)
      (hLN₀.trans hN) (hLN₀.trans hM) le_rfl]
    exact (hC z L N M (by linarith [hnorm hz]) hN hM).trans_lt (hK L (le_max_left _ _))
  have hex (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) : ∃ w : ℂ, Tendsto (F · z) atTop (𝓝 w) := by
    apply cauchySeq_tendsto_of_complete
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨K, hK⟩ := hunif ε hε
    exact ⟨K, fun N hN M hM => hK z hz N M hN hM⟩
  let H (z : ℂ) := if hz : z ∈ ball (0 : ℂ) R then (hex z hz).choose else 0
  have hH (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) : Tendsto (F · z) atTop (𝓝 (H z)) := by
    simpa only [H, dite_eq_left hz] using (hex z hz).choose_spec
  have hconv : TendstoUniformlyOn F H atTop (ball (0 : ℂ) R) := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    obtain ⟨K, hK⟩ := hunif (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop K] with N hN z hz
    have hlim := (hH z hz).dist (tendsto_const_nhds (x := F N z))
    have hle := le_of_tendsto hlim ((eventually_ge_atTop K).mono fun M hM => (hK z hz M N hM hN).le)
    exact hle.trans_lt (half_lt_self hε)
  have hhol : ∀ᶠ N in atTop, DifferentiableOn ℂ (F N) (ball 0 R) := by
    filter_upwards [eventually_ge_atTop N₀] with N hN z hz
    have hd := mem_compactCauchyPoleDomain_annularSchwartzCutoff hN le_rfl (hbase hz)
    exact (hasDerivAt_compactCauchyAction T (annularSchwartzCutoff N N₀)
      (annularSchwartzCutoff_hasCompactSupport N N₀) m hd).differentiableAt.differentiableWithinAt
  refine ⟨H, (hconv.tendstoLocallyUniformlyOn.differentiableOn hhol isOpen_ball).analyticOnNhd isOpen_ball,
    fun z hz him => ?_⟩
  have hsub := (tendsto_broadCauchyPairing T q m hT hm z him).sub
    (tendsto_const_nhds (x := T (broadCauchySchwartzCut m z him N₀)))
  have he : (fun N => T (broadCauchySchwartzCut m z him N) - T (broadCauchySchwartzCut m z him N₀)) =ᶠ[atTop]
      (F · z) := Eventually.of_forall fun N => by
    dsimp only [F]
    rw [broadCauchyAnnularCut_eq_sub_offReal m z him N N₀, map_sub]
  exact sub_eq_iff_eq_add.mp (tendsto_nhds_unique (hsub.congr' he) (hH z hz))

end

end MeyerGeneralProblem
