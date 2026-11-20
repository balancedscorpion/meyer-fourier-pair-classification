module

public import MeyerGeneralProblem.Distribution.LatticeSlabAsymptotics
public import MeyerGeneralProblem.Distribution.OriginalSpectralWeight
public import MeyerGeneralProblem.Distribution.FiniteModulationGap
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

/-!
# The finite-prefix lattice-slab modulation construction

Embed the original contributing spectral prefix in a finite-rank real
integer module. The exact slab ratio bounds the number of shifted rows
in the detecting window. The existing finite convolution matrix turns
the strict deficit into a whole-source annihilator.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter Set UniformDiscrete
open scoped Topology FourierTransform

/-- A finite real prefix is contained in an injectively presented finite
rank integer module with at least two coordinates and positive last step. -/
theorem exists_latticeSlabCoordinates_of_finset (E : Finset ℝ) :
    ∃ (r : ℕ) (β : Fin (r + 1) → ℝ) (p : ℝ),
      0 < p ∧ Function.Injective (slabLatticeFrequency β p) ∧
      ∀ x ∈ E, ∃ u : (Fin (r + 1) → ℤ) × ℤ, slabLatticeFrequency β p u = x := by
  classical
  let F := insert 1 (insert (Real.sqrt 2) E)
  let A : LocallyFiniteCarrier := ⟨F, fun _ _ => F.finite_toSet.subset Set.inter_subset_left⟩
  have hF : (AddSubgroup.closure A.carrier).FG :=
    (AddSubgroup.fg_iff _).2 ⟨A.carrier, rfl, F.finite_toSet⟩
  obtain ⟨d, β, L, label, hInj, hLfreq, hLabel, _⟩ :=
    exists_coordinates_of_finitely_generated_spectral_module A hF
  let u₁ : A.subtype := ⟨1, by
    change (1 : ℝ) ∈ F
    simp [F]⟩
  let u₂ : A.subtype := ⟨Real.sqrt 2, by
    change Real.sqrt 2 ∈ F
    simp [F]⟩
  have h₁ : L (label u₁) = 1 := hLabel u₁
  have h₂ : L (label u₂) = Real.sqrt 2 := hLabel u₂
  have hd : 2 ≤ d := by
    by_contra! h
    have h01 : d = 0 ∨ d = 1 := by omega
    rcases h01 with (rfl | rfl)
    · have he : label u₁ = 0 := Subsingleton.elim _ _
      rw [he, map_zero] at h₁
      norm_num at h₁
    · let m : ℤ := label u₁ 0
      let n : ℤ := label u₂ 0
      have hm : (m : ℝ) * β 0 = 1 := by
        simpa only [hLfreq, torusDirectionalFrequency, Fin.sum_univ_one] using h₁
      have hn : (n : ℝ) * β 0 = Real.sqrt 2 := by
        simpa only [hLfreq, torusDirectionalFrequency, Fin.sum_univ_one] using h₂
      have hmne : (m : ℝ) ≠ 0 := by
        intro he
        simp [he] at hm
      have hrat : Real.sqrt 2 = (n : ℝ) / (m : ℝ) := by
        apply (eq_div_iff hmne).mpr
        calc
          _ = ((n : ℝ) * β 0) * (m : ℝ) := by rw [hn]
          _ = (n : ℝ) * ((m : ℝ) * β 0) := by ring
          _ = _ := by rw [hm, mul_one]
      exact irrational_sqrt_two.ne_rational n m hrat
  obtain ⟨r, hr⟩ : ∃ r : ℕ, d = r + 1 + 1 := ⟨d - 2, by omega⟩
  subst d
  have hβ₀ : β 0 ≠ 0 := by
    intro h0
    let w : Fin (r + 1 + 1) → ℤ := Pi.single 0 1
    have hw : L w = L 0 := by
      rw [map_zero, hLfreq, torusDirectionalFrequency, Fin.sum_univ_succ]
      simp [w, h0]
    have hei := congrFun (hInj hw) 0
    simp [w] at hei
  let p := |β 0|
  let s : ℤ := if β 0 < 0 then -1 else 1
  have hs : (s : ℝ) * β 0 = p := by
    by_cases h : β 0 < 0
    · simp [s, p, h, abs_of_neg h]
    · simp [s, p, h, abs_of_nonneg (le_of_not_gt h)]
  have hss : s * s = 1 := by
    by_cases h : β 0 < 0 <;> simp [s, h]
  have hsne : s ≠ 0 := by
    intro h
    simp [h] at hss
  let γ (i : Fin (r + 1)) := β i.succ
  let e (u : (Fin (r + 1) → ℤ) × ℤ) : Fin (r + 1 + 1) → ℤ := Fin.cons (s * u.2) u.1
  have he (u : (Fin (r + 1) → ℤ) × ℤ) : L (e u) = slabLatticeFrequency γ p u := by
    rw [hLfreq, torusDirectionalFrequency, Fin.sum_univ_succ, slabLatticeFrequency]
    simp only [e, Fin.cons_zero, Fin.cons_succ, Int.cast_mul, γ]
    rw [mul_right_comm, hs, add_comm, mul_comm p]
  have hEinj : Function.Injective e := by
    intro a b heq
    refine Prod.ext (funext fun j => ?_) ?_
    · simpa only [e, Fin.cons_succ] using congrFun heq j.succ
    · apply mul_left_cancel₀ hsne
      simpa only [e, Fin.cons_zero] using congrFun heq 0
  refine ⟨r, γ, p, abs_pos.mpr hβ₀, ?_, ?_⟩
  · intro a b hab
    apply hEinj
    apply hInj
    exact (he a).trans (hab.trans (he b).symm)
  · intro x hx
    let y : A.subtype := ⟨x, by
      change x ∈ F
      simp [F, hx]⟩
    let u : (Fin (r + 1) → ℤ) × ℤ := (fun j => label y j.succ, s * label y 0)
    refine ⟨u, (he u).symm.trans ?_⟩
    have hui : e u = label y := by
      funext i
      refine Fin.cases ?_ (fun j => rfl) i
      change s * (s * label y 0) = label y 0
      rw [← mul_assoc, hss, one_mul]
    exact (congrArg L hui).trans (hLabel y)


private theorem slabLatticeFrequency_add {d : Type*} [Fintype d]
    (β : d → ℝ) (p : ℝ) (u v : (d → ℤ) × ℤ) :
    slabLatticeFrequency β p (u + v) = slabLatticeFrequency β p u + slabLatticeFrequency β p v := by
  simp only [slabLatticeFrequency, Prod.fst_add, Prod.snd_add, Pi.add_apply, Int.cast_add,
    add_mul, Finset.sum_add_distrib]
  ring

/-- Apply the slab ratio to the literal finite prefix that can take part
in the detecting interval. Every contributing row of the original convolution
lies in the narrower enlarged slab. -/
theorem exists_finiteModulationMenu_card_lt_via_latticeSlabs
    (B : LocallyFiniteCarrier) {J L : ℝ} (hJ : 0 < J) (hJL : J < L) :
    ∃ (ι : Type) (f : Fintype ι) (a : ι → ℝ), Function.Injective a ∧
      Fintype.card (spectralWindow (@finiteCombConvolutionCarrier ι f B a) J) < @Fintype.card ι f := by
  classical
  let E₀ := B.finite_inter_Icc (-(J + L)) (J + L)
  let E := E₀.toFinset
  obtain ⟨r, β, p, hp, hβ, hPrefix⟩ := exists_latticeSlabCoordinates_of_finset E
  choose u hu using fun x : E => hPrefix x x.property
  let H : ℕ := ∑ x : E, ∑ i, ((u x).1 i).natAbs
  have hH (x : E) (i : Fin (r + 1)) : |(u x).1 i| ≤ (H : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast
      ((Finset.single_le_sum (fun j _ => Nat.zero_le ((u x).1 j).natAbs) (Finset.mem_univ i)).trans
        (Finset.single_le_sum (fun y _ => Nat.zero_le (∑ j, ((u y).1 j).natAbs)) (Finset.mem_univ x)))
  obtain ⟨N, hN⟩ := (eventually_ncard_latticeSlabFrequencies_lt β hp hJ hJL H hβ).exists
  let S₀ := finite_latticeSlabFrequencies β hp L N hβ
  let S := S₀.toFinset
  let a (i : S) : ℝ := i
  let R₀ := finite_latticeSlabFrequencies β hp J (N + H) hβ
  let R := R₀.toFinset
  have hRow (x : spectralWindow (finiteCombConvolutionCarrier B a) J) :
      (x : ℝ) ∈ latticeSlabFrequencies β p J (N + H) := by
    obtain ⟨i, y, hy, hxy⟩ := mem_iUnion.mp x.property.1
    have hx : |(x : ℝ)| ≤ J := abs_le.mpr x.property.2
    obtain ⟨v, hv, hvf, hAi⟩ := S₀.mem_toFinset.mp i.property
    have hyb : |y| ≤ J + L := by
      have he : y = (x : ℝ) - a i := by linarith
      rw [he]
      exact (abs_sub _ _).trans (add_le_add hx hAi)
    let j : E := ⟨y, E₀.mem_toFinset.mpr ⟨hy, abs_le.mp hyb⟩⟩
    refine ⟨v + u j, ?_, ?_, hx⟩
    · intro k
      change |v.1 k + (u j).1 k| ≤ ((N + H : ℕ) : ℤ)
      rw [Nat.cast_add]
      exact (abs_add_le _ _).trans (add_le_add (hv k) (hH j k))
    · rw [slabLatticeFrequency_add, hvf, hu]
      exact hxy
  let f (x : spectralWindow (finiteCombConvolutionCarrier B a) J) : R :=
    ⟨x, R₀.mem_toFinset.mpr (hRow x)⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : R => (z : ℝ)) he)
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe, R, ← Set.ncard_eq_toFinset_card] at hcard
  refine ⟨S, inferInstance, a, Subtype.val_injective, ?_⟩
  rw [Fintype.card_coe, ← Set.ncard_eq_toFinset_card _ S₀]
  exact hcard.trans_lt hN

/-- The exact finite-prefix slab construction yields a genuine finite
exponential annihilator from a whole-source detecting gap. -/
theorem exists_finiteExponentialAnnihilator_of_spectralGapUniqueness_via_latticeSlabs
    (A B : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A U) (hB : AtomicOnCarrier B (𝓕 U))
    {J L : ℝ} (hJ : 0 < J) (hJL : J < L)
    (hGap : SpectralGapUniqueness A J) :
    ∃ (ι : Type) (f : Fintype ι), letI := f
      ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧
        (∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0) ∧
        finiteExponentialMultiplication a c U = 0 := by
  obtain ⟨ι, f, a, ha, hcard⟩ := exists_finiteModulationMenu_card_lt_via_latticeSlabs B hJ hJL
  let _ := f
  obtain ⟨c, hc, hzero⟩ :=
    exists_finiteModulation_eq_zero_of_card_lt_of_gap A B U hA hB a J hGap hcard
  exact ⟨ι, f, a, c, ha, exists_eval_ne_zero_of_finiteModulation_coefficients_ne_zero a ha c hc, hzero⟩

/-- The upper-linear centered count theorem through the exact lattice
slab and the original Cauchy detector for the source's Schwartz order. -/
theorem exists_finiteExponentialAnnihilator_of_centered_count_via_latticeSlabs
    (A B : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((A.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (U : TemperedDistribution ℝ ℂ) (hA : AtomicOnCarrier A U)
    (hB : AtomicOnCarrier B (𝓕 U)) :
    ∃ (ι : Type) (f : Fintype ι), letI := f
      ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧
        (∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0) ∧
        finiteExponentialMultiplication a c U = 0 := by
  obtain ⟨q, _, hq⟩ := exists_hasSchwartzOrderBound U
  let D := ((q + 2 + q : ℕ) : ℝ) *
    limsup (fun t : ℝ => ((A.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)) atTop
  let J := max 0 D + 1
  have hJ : 0 < J := by dsimp [J]; linarith [le_max_left 0 D]
  have hw : 2 * D < J - (-J) := by dsimp [J]; linarith [le_max_right 0 D]
  obtain ⟨ι, f, a, ha, hcard⟩ :=
    exists_finiteModulationMenu_card_lt_via_latticeSlabs B hJ (lt_add_of_pos_right J zero_lt_one)
  let _ := f
  obtain ⟨c, hc, hGap⟩ := exists_finiteModulation_fourierGap_of_card_lt B U hB a J hcard
  have hSupp : DistributionSupportedOn A.carrier U := by
    intro g _ hg
    exact hA g fun x hx => (hg x hx).eq_of_nhds
  exact ⟨ι, f, a, c, ha, exists_eval_ne_zero_of_finiteModulation_coefficients_ne_zero a ha c hc,
    finiteExponentialMultiplication_eq_zero_of_centered_count_and_fourier_gap
      A hb U q hSupp hq (-J) J hw a c hGap⟩

end
end MeyerGeneralProblem
