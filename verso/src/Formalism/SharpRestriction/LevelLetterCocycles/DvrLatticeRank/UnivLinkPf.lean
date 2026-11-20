import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UnivLinkPfB

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules Formalism.MainNotions.N.Ln34.UnivLinkPf

/- English proof (translation)
Introduce `a ha`. Break down `ha with ha | ⟨h1, h2⟩` into its components or cases. Unfold `deep at ha split_ifs at ha`. Take `⟨h1, h2⟩` from `ha`. Conclude with `⟨by omega, by omega⟩`.

Take `⟨h1, h2⟩` from `ha`. Conclude with `⟨by omega, by omega⟩`. Conclude with `⟨by omega, by omega⟩`.
-/
theorem univLinkPf_deep_sub {up : Bool} {bτ S η h' : ℕ} (hb : η < bτ) (hS : bτ + S ≤ h') :
    deep up bτ S ∪ Set.Icc (-(η : ℤ)) η ⊆ Set.Icc (-(h' : ℤ)) h' := by
  intro a ha
  rcases ha with ha | ⟨h1, h2⟩
  · unfold deep at ha
    split_ifs at ha
    · obtain ⟨h1, h2⟩ := ha
      exact ⟨by omega, by omega⟩
    · obtain ⟨h1, h2⟩ := ha
      exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D HW Fo hA hd hR hC hH hMF hU1 hk hU2 hDn hUp hMx`. Introduce `l _ hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b hN c`. Take `⟨hc₁, hc₂, -, hJ₁, hJ₂, hηb, hbS, hh', -, hposition⟩` from `id hN`. Establish `hj₁ : ∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h')` using `fun τ a ha => univLinkPf_deep_sub (hηb τ) (hbS τ) (hJ₁ τ a ha)`. Establish `hj₂ : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h')` using `fun τ a ha => univLinkPf_deep_sub (hηb τ) (hbS τ) (hJ₂ τ a ha)`.

Establish `hs : 1 ≤ sK l K`. Establish `hdv` using `hd l hl K LL hG`. Establish `hlp : l.Prime` using `Fact.out`. Establish `h2` using `hlp.two_le`. Establish `hpos : 0 < l - 1` using `by omega`.

Establish `he : 0 < eK K` using `Nat.pos_of_ne_zero fun h0 => by`. Rewrite `hdv` using `[h0, zero_dvd_iff]`. Use linear arithmetic over natural numbers and integers. Conclude with `Nat.div_pos (Nat.le_of_dvd hpos hdv) he`. Establish `hM : 1 ≤ MK l K h'`.

Establish `h4 : (0 : ℝ) < 4 * (h' : ℝ)`. Establish `: (1 : ℝ) ≤ h'` using `by exact_mod_cast hh'`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs' : (0 : ℝ) < (sK l K : ℝ)` using `by exact_mod_cast hs`. Conclude with `Nat.ceil_pos.2 (div_pos h4 hs')`.

Take `⟨α, β, hfr⟩` from `hH l hl K LL hG π' E hp9 h' hh' c`. Establish `hU3 : ThirdPropositionSlot ((HW l).W K 1 LL hG) F (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') S up b c (rhoA l (eK K) h' + max (2 * sigA l (sK l K) h') (ycA l h' η)) α`. Break down `hposition with h2 | hsl` into its components or cases. Conclude with `hMx l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr hN h2`. Distinguish the cases in `hex : ∃ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c ∧ up τ = true`.

Take `⟨τ₀, hτ₀, hu₀⟩` from `hex`. Conclude with `universal_lift_mono_exponent _ F (hUp l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr hN fun τ hτ => (hsl τ τ₀ (hτ.trans hτ₀.symm)).trans hu₀) _`. Use `universal_lift_mono_exponent _ F (hDn l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr hN fun τ hτ => ?_) _` and prove the remaining obligations. Consider the cases of `h : up τ`. Both sides reduce to the same expression.

Conclude with `absurd ⟨τ, hτ, h⟩ hex`. Take `⟨s₀, hcard, hsub, hmain⟩` from `univLinkPf_local ((HW l).W K 1 LL hG) F hc₁ hc₂ ((hA l K 1 LL hG).2.1 (fun h2 => absurd (((D.loc l).PD_p K).symm.trans h2) hl)) (hfr.1 T₂ hc₂ hj₂).2.2.2.1 (hMF l hl K LL hG π' E hp9 h' hh' c α β hfr T₂ hc₂ hj₂) hM (hR l hl K LL hG π' E hp9 T₁ h' hh' hc₁ hj₁ c) (hR l hl K LL hG π' …`. Use `⟨s₀, hcard, hsub, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h` using `hmain x hx`. Establish `hpl : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`.

Rewrite `h` using `[hpl]`. Establish `hexp : sigA l (sK l K) h' + y2K l K h' S η = sigA l (sK l K) h' + (2 * sigA l (sK l K) h' + kapA l (eK K) h' S + (rhoA l (eK K) h' + max (2 * sigA l (sK l K) h') (ycA l h' η)))`. Unfold `y2K`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hexp, ← Nat.cast_smul_eq_nsmul ↥(OL LL), Nat.cast_pow]`.

Conclude with `h`.
-/
theorem univlink_pf : UnivLinkStep := by
  intro D HW Fo hA hd hR hC hH hMF hU1 hk hU2 hDn hUp hMx
  intro l _ hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b hN c
  obtain ⟨hc₁, hc₂, -, hJ₁, hJ₂, hηb, hbS, hh', -, hposition⟩ := id hN
  have hj₁ : ∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h') :=
    fun τ a ha => univLinkPf_deep_sub (hηb τ) (hbS τ) (hJ₁ τ a ha)
  have hj₂ : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') :=
    fun τ a ha => univLinkPf_deep_sub (hηb τ) (hbS τ) (hJ₂ τ a ha)
  have hs : 1 ≤ sK l K := by
    have hdv := hd l hl K LL hG
    have hlp : l.Prime := Fact.out
    have h2 := hlp.two_le
    have hpos : 0 < l - 1 := by omega
    have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_dvd_iff] at hdv
      omega
    exact Nat.div_pos (Nat.le_of_dvd hpos hdv) he
  have hM : 1 ≤ MK l K h' := by
    have h4 : (0 : ℝ) < 4 * (h' : ℝ) := by
      have : (1 : ℝ) ≤ h' := by exact_mod_cast hh'
      linarith
    have hs' : (0 : ℝ) < (sK l K : ℝ) := by exact_mod_cast hs
    exact Nat.ceil_pos.2 (div_pos h4 hs')
  obtain ⟨α, β, hfr⟩ := hH l hl K LL hG π' E hp9 h' hh' c
  have hU3 : ThirdPropositionSlot ((HW l).W K 1 LL hG) F (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h'
      (MK l K h') S up b c (rhoA l (eK K) h' + max (2 * sigA l (sK l K) h') (ycA l h' η)) α := by
    rcases hposition with h2 | hsl
    · exact hMx l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr hN h2
    · by_cases hex : ∃ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c ∧ up τ = true
      · obtain ⟨τ₀, hτ₀, hu₀⟩ := hex
        exact universal_lift_mono_exponent _ F (hUp l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr hN
          fun τ hτ => (hsl τ τ₀ (hτ.trans hτ₀.symm)).trans hu₀) _
      · refine universal_lift_mono_exponent _ F (hDn l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr hN
          fun τ hτ => ?_) _
        cases h : up τ
        · rfl
        · exact absurd ⟨τ, hτ, h⟩ hex
  obtain ⟨s₀, hcard, hsub, hmain⟩ := univLinkPf_local ((HW l).W K 1 LL hG) F hc₁ hc₂
    ((hA l K 1 LL hG).2.1 (fun h2 => absurd (((D.loc l).PD_p K).symm.trans h2) hl)) (hfr.1 T₂ hc₂ hj₂).2.2.2.1
    (hMF l hl K LL hG π' E hp9 h' hh' c α β hfr T₂ hc₂ hj₂) hM
    (hR l hl K LL hG π' E hp9 T₁ h' hh' hc₁ hj₁ c) (hR l hl K LL hG π' E hp9 T₂ h' hh' hc₂ hj₂ c)
    (hC l hl K LL hG π' E hp9 T₁ h' hh' hc₁ hj₁ c) (hC l hl K LL hG π' E hp9 T₂ h' hh' hc₂ hj₂ c)
    (hk l hl K LL hG π' E hp9 h' S up b c (fun τ => by have := hηb τ; omega) hbS)
    (hU1 l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr) hN
    (hU2 l hl K LL hG π' E hp9 T₂ h' hh' hc₂ hj₂ c) hU3
  refine ⟨s₀, hcard, hsub, fun x hx => ?_⟩
  have h := hmain x hx
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hpl] at h
  have hexp : sigA l (sK l K) h' + y2K l K h' S η = sigA l (sK l K) h' +
      (2 * sigA l (sK l K) h' + kapA l (eK K) h' S +
        (rhoA l (eK K) h' + max (2 * sigA l (sK l K) h') (ycA l h' η))) := by
    unfold y2K; ring
  rw [hexp, ← Nat.cast_smul_eq_nsmul ↥(OL LL), Nat.cast_pow]
  exact h

end Formalism.MainNotions.N.Ln34

end
