import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.TheoremMCB

namespace Formalism.InvariantFactorPaths.MC

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO Formalism.InvariantFactorPaths.OddLevelGainBounds.TB MvPolynomial Finset

/- English proof (translation)
Introduce `p _ N r _ _ LL q J M ρ e1 hr hHP z hz hprim`. Take `⟨hP1, hP2⟩` from `hHP`. Set `Tj : Fin (N + 1) → Set (Fin r → ℤ)` to `fun j => {la | ∀ k, min (J k) N = (j : ℕ) → ((la 0 : ℤ) : WithTop ℤ) ≤ M k}`. Establish `hex : ∀ j : Fin (N + 1), ∃ P, IsTypeProj p LL j univ (Tj j) P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧ ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r)` using `fun j => hP1 j (Nat.lt_succ_iff.mp j.isLt) univ (Or.inl rfl) (Tj j) (fun la la' h => by rw [show la = la' from funext fun c => h c (mem_univ c)])`. Use `choose P hPt hPsa hPint using hex`.

Establish `hPP : ∀ j x, P j (P j x) = P j x` using `fun j x => LinearMap.congr_fun (hPt j).1 x`. Establish `hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x)`. Introduce `j j' x`. Break down `le_total (j : ℕ) (j' : ℕ) with h | h` into its components or cases. Conclude with `LinearMap.congr_fun (hP2 j j' univ univ (Tj j) (Tj j') (P j) (P j') h subset_rfl (Or.inl rfl) (Or.inl rfl) (hPt j) (hPt j')) x`.

Conclude with `(LinearMap.congr_fun (hP2 j' j univ univ (Tj j') (Tj j) (P j') (P j) h subset_rfl (Or.inl rfl) (Or.inl rfl) (hPt j') (hPt j)) x).symm`. Establish `hPpol : ∀ j, ∀ x ∈ Pol p r LL, P j x ∈ Pol p r LL` using `fun j => typeProj_pol LL j (Tj j) (P j) (hPt j)`. Establish `hfixY : ∀ j : Fin (N + 1), ∀ x ∈ Y p (r` using `r) LL J M, P j x = x := by`. Introduce `j`. Use `set S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := Pol p r LL ⊓ ⨅ (k : Fin q) (_ : min (J k) N = (j : ℕ)), YCond p (r := r) LL j (M k) with hSdef`.

Establish `hmemS : ∀ x, x ∈ S ↔ x ∈ Pol p r LL ∧ ∀ k, min (J k) N = (j : ℕ) → x ∈ YCond p (r` using `r) LL j (M k) := by`. Introduce `x`. Simplify using `only [hSdef, Submodule.mem_inf, Submodule.mem_iInf]`. Establish `hfix` using `proj_fix LL j (Tj j) (P j) (hPt j) S inf_le_left (fun c d x hx => by`. Rewrite `hx`, the goal using `[hmemS]`.

Conclude with `⟨glAct_pol LL j c d x hx.1, fun k hk => ycond_glStable LL j (M k) c d x (hx.2 k hk)⟩)`. Use the proof step `(fun x hx => by`. Rewrite `hx`, the goal using `[hmemS]`. Conclude with `⟨hPpol j x hx.1, fun k hk => typeProj_ycond LL j (Tj j) (P j) (hPt j) (M k) x (hx.2 k hk)⟩)`. Use the proof step `(fun h hh hh0 μ hμ => by`.

Rewrite `hh` using `[hmemS]`. Introduce `k hk`. Establish `h1` using `ycond_le_supp LL j (M k) (hh.2 k hk)`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, m ∈ h.support := by`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Conclude with `hh0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))`. Rewrite `h1` using `[mem_restrictSupport_iff]`. Establish `h2` using `h1 (Finset.mem_coe.mpr hm)`. Establish `h3` using `(Submodule.mem_inf.mp hμ).1`.

Rewrite `h3` using `[WtSpC, mem_restrictSupport_iff]`. Establish `h4` using `h3 (Finset.mem_coe.mpr hm) 0 (Finset.mem_univ _)`. Simplify using `only [Set.mem_ofPred_eq] at h2`. Rewrite `h2` using `[h4]`. Conclude with `h2)`.

Introduce `x hx`. Apply `hfix` to reduce the goal to its premises. Rewrite using `[hmemS]`. Use `⟨(Submodule.mem_inf.mp hx).1, fun k hk => ?_⟩` and prove the remaining obligations. Use `(Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hx).2 k` as an intermediate fact.

Rewrite `this` using `[ycond_min, hk]`. Conclude with `this`. Establish `hranY : ∀ j : Fin (N + 1), ∀ u, P j u = u → ∀ k, min (J k) N = (j : ℕ) → u ∈ YCond p (r` using `r) LL (J k) (M k) := by`. Introduce `j u hu k hk`. Rewrite using `[ycond_min, hk]`.

Establish `h1 : u ∈ LinearMap.range (P j)` using `⟨u, hu⟩`. Rewrite `h1` using `[(hPt j).2.1]`. Conclude with `(iSup₂_le fun la hla => isoC_le_ycond LL j la (M k) (hla k hk)) h1`. Take `⟨m0, hm0⟩` from `prim_unit_coeff LL J M z hz hprim`. Establish `hzY : z ∈ Y p (r` using `r) LL J M := (Submodule.mem_inf.mp hz).1`.

Establish `hzP : z ∈ Pol p r LL` using `(Submodule.mem_inf.mp (Submodule.mem_inf.mp hz).2).1`. Establish `hm0mem : m0 ∈ z.support`. Rewrite using `[mem_support_iff]`. Introduce `h`. Rewrite `hm0` using `[h, norm_zero]`.

Conclude with `zero_ne_one hm0`. Establish `hmd : MultiDeg LL m0`. Rewrite `hzP` using `[Pol, mem_restrictSupport_iff]`. Conclude with `hzP (Finset.mem_coe.mpr hm0mem)`. Establish `hmonZ : (monomial m0 (1 : ℚ_[p])) ∈ PolZ p r LL` using `by classical`.

Use `Submodule.mem_inf.mpr ⟨?_, mem_intPol_of_norm _ fun m => ?_⟩` and prove the remaining obligations. Use `show monomial m0 (1 : ℚ_[p]) ∈ Pol p r LL`. Rewrite using `[Pol, mem_restrictSupport_iff]`. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_coe]`.

Rewrite using `[Finset.mem_singleton.mp (support_monomial_subset hm)]`. Conclude with `hmd`. Apply the tactic sequence `rw [coeff_monomial]; split_ifs <;> simp`. Use `set u := lcomp P (List.finRange (N + 1)) (monomial m0 (1 : ℚ_[p])) with hu`. Establish `hufix : ∀ j, P j u = u` using `fun j => lcomp_fix P hPP hcomm _ j (List.mem_finRange j) _`.

Establish `hint` using `lcomp_int LL e1 P hPpol hPint (List.finRange (N + 1)) _ hmonZ`. Rewrite `hint` using `[List.length_finRange]`. Use `⟨((p : ℚ_[p]) ^ (e1 * (N + 1))) • u, ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hint).1, ?_⟩, hint⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_iInf]`.

Introduce `k`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Conclude with `hranY ⟨min (J k) N, by omega⟩ u (hufix _) k rfl`. Rewrite using `[fockN_smul_right', norm_mul, norm_pow, Padic.norm_p]`. Establish `hf : fockN p LL z u = fockN p LL z (monomial m0 1)`.

Unfold `fockN`. Rewrite using `[hu, lcomp_fock P hPsa z (fun j => hfixY j z hzY)]`. Rewrite using `[hf]`. Establish `hge` using `fockN_monomial_ge LL z m0 hmd hm0`. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).pos`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[zpow_neg, zpow_natCast, inv_pow, mul_one]`. Use `_ ≤ (p : ℝ)⁻¹ ^ (e1 * (N + 1)) * ‖fockN p LL z (monomial m0 1)‖ := mul_le_mul_of_nonneg_left hge (by positivity)`.
-/
theorem partner_condition_holds : YPartnerC := by
  intro p _ N r _ _ LL q J M ρ e1 hr hHP z hz hprim
  obtain ⟨hP1, hP2⟩ := hHP
  let Tj : Fin (N + 1) → Set (Fin r → ℤ) := fun j =>
    {la | ∀ k, min (J k) N = (j : ℕ) → ((la 0 : ℤ) : WithTop ℤ) ≤ M k}
  have hex : ∀ j : Fin (N + 1), ∃ P, IsTypeProj p LL j univ (Tj j) P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r) :=
    fun j => hP1 j (Nat.lt_succ_iff.mp j.isLt) univ (Or.inl rfl) (Tj j)
      (fun la la' h => by rw [show la = la' from funext fun c => h c (mem_univ c)])
  choose P hPt hPsa hPint using hex
  have hPP : ∀ j x, P j (P j x) = P j x := fun j x => LinearMap.congr_fun (hPt j).1 x
  have hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x) := by
    intro j j' x
    rcases le_total (j : ℕ) (j' : ℕ) with h | h
    · exact LinearMap.congr_fun (hP2 j j' univ univ (Tj j) (Tj j') (P j) (P j') h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j) (hPt j')) x
    · exact (LinearMap.congr_fun (hP2 j' j univ univ (Tj j') (Tj j) (P j') (P j) h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j') (hPt j)) x).symm
  have hPpol : ∀ j, ∀ x ∈ Pol p r LL, P j x ∈ Pol p r LL := fun j => typeProj_pol LL j (Tj j) (P j) (hPt j)

  have hfixY : ∀ j : Fin (N + 1), ∀ x ∈ Y p (r := r) LL J M, P j x = x := by
    intro j
    set S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
      Pol p r LL ⊓ ⨅ (k : Fin q) (_ : min (J k) N = (j : ℕ)), YCond p (r := r) LL j (M k) with hSdef
    have hmemS : ∀ x, x ∈ S ↔ x ∈ Pol p r LL ∧ ∀ k, min (J k) N = (j : ℕ) → x ∈ YCond p (r := r) LL j (M k) := by
      intro x; simp only [hSdef, Submodule.mem_inf, Submodule.mem_iInf]
    have hfix := proj_fix LL j (Tj j) (P j) (hPt j) S inf_le_left
      (fun c d x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨glAct_pol LL j c d x hx.1, fun k hk => ycond_glStable LL j (M k) c d x (hx.2 k hk)⟩)
      (fun x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨hPpol j x hx.1, fun k hk => typeProj_ycond LL j (Tj j) (P j) (hPt j) (M k) x (hx.2 k hk)⟩)
      (fun h hh hh0 μ hμ => by
        rw [hmemS] at hh
        intro k hk
        have h1 := ycond_le_supp LL j (M k) (hh.2 k hk)
        obtain ⟨m, hm⟩ : ∃ m, m ∈ h.support := by
          by_contra hc; push Not at hc
          exact hh0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
        rw [mem_restrictSupport_iff] at h1
        have h2 := h1 (Finset.mem_coe.mpr hm)
        have h3 := (Submodule.mem_inf.mp hμ).1
        rw [WtSpC, mem_restrictSupport_iff] at h3
        have h4 := h3 (Finset.mem_coe.mpr hm) 0 (Finset.mem_univ _)
        simp only [Set.mem_ofPred_eq] at h2
        rw [h4] at h2
        exact h2)
    intro x hx
    apply hfix
    rw [hmemS]
    refine ⟨(Submodule.mem_inf.mp hx).1, fun k hk => ?_⟩
    have := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hx).2 k
    rw [ycond_min, hk] at this
    exact this

  have hranY : ∀ j : Fin (N + 1), ∀ u, P j u = u → ∀ k, min (J k) N = (j : ℕ) →
      u ∈ YCond p (r := r) LL (J k) (M k) := by
    intro j u hu k hk
    rw [ycond_min, hk]
    have h1 : u ∈ LinearMap.range (P j) := ⟨u, hu⟩
    rw [(hPt j).2.1] at h1
    exact (iSup₂_le fun la hla => isoC_le_ycond LL j la (M k) (hla k hk)) h1

  obtain ⟨m0, hm0⟩ := prim_unit_coeff LL J M z hz hprim
  have hzY : z ∈ Y p (r := r) LL J M := (Submodule.mem_inf.mp hz).1
  have hzP : z ∈ Pol p r LL := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hz).2).1
  have hm0mem : m0 ∈ z.support := by
    rw [mem_support_iff]; intro h; rw [h, norm_zero] at hm0; exact zero_ne_one hm0
  have hmd : MultiDeg LL m0 := by
    rw [Pol, mem_restrictSupport_iff] at hzP; exact hzP (Finset.mem_coe.mpr hm0mem)
  have hmonZ : (monomial m0 (1 : ℚ_[p])) ∈ PolZ p r LL := by
    classical
    refine Submodule.mem_inf.mpr ⟨?_, mem_intPol_of_norm _ fun m => ?_⟩
    · show monomial m0 (1 : ℚ_[p]) ∈ Pol p r LL
      rw [Pol, mem_restrictSupport_iff]
      intro m hm
      rw [Finset.mem_coe] at hm
      rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
      exact hmd
    · rw [coeff_monomial]; split_ifs <;> simp
  set u := lcomp P (List.finRange (N + 1)) (monomial m0 (1 : ℚ_[p])) with hu
  have hufix : ∀ j, P j u = u := fun j => lcomp_fix P hPP hcomm _ j (List.mem_finRange j) _
  have hint := lcomp_int LL e1 P hPpol hPint (List.finRange (N + 1)) _ hmonZ
  rw [List.length_finRange] at hint
  refine ⟨((p : ℚ_[p]) ^ (e1 * (N + 1))) • u, ?_, ?_⟩
  · refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hint).1, ?_⟩, hint⟩
    rw [Submodule.mem_iInf]
    intro k
    refine Submodule.smul_mem _ _ ?_
    exact hranY ⟨min (J k) N, by omega⟩ u (hufix _) k rfl
  ·
    rw [fockN_smul_right', norm_mul, norm_pow, Padic.norm_p]
    have hf : fockN p LL z u = fockN p LL z (monomial m0 1) := by
      unfold fockN
      rw [hu, lcomp_fock P hPsa z (fun j => hfixY j z hzY)]
    rw [hf]
    have hge := fockN_monomial_ge LL z m0 hmd hm0
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    calc (p : ℝ) ^ (-((e1 * (N + 1) : ℕ) : ℤ)) = (p : ℝ)⁻¹ ^ (e1 * (N + 1)) * 1 := by
          rw [zpow_neg, zpow_natCast, inv_pow, mul_one]
      _ ≤ (p : ℝ)⁻¹ ^ (e1 * (N + 1)) * ‖fockN p LL z (monomial m0 1)‖ :=
          mul_le_mul_of_nonneg_left hge (by positivity)

end Formalism.InvariantFactorPaths.MC
