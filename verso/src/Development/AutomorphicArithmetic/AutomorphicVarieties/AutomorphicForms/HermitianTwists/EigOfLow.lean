import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RepEig

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
  UpperTheory.V.Br CongruenceSubgroup

open private untwist eig_unique level_zero_eq_maximal_compact ev_not_dvd from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RepEig

/- English proof (translation)
Introduce `hCC k hk1 π hlw`. Take `⟨N, ψ, ν, hN, hν, φ, hφ, h0, hlow, hfix⟩` from `levelVec k π hlw`. Use `haveI : NeZero N := ⟨by omega⟩`. Take `⟨ω, hω, -⟩` from `hCC ℚ (π.twist ν)`. Establish `hc` using `fun z g => hω z φ hφ g`.

Take `⟨χ, hχ⟩` from `charOf N hN ω φ h0 hlow.one hfix hc`. Establish `hcusp` using `(π.twist ν).cusp φ hφ`. Take `⟨f, hf, hL⟩` from `deadel k N hN χ ω hχ φ hcusp hlow hfix hc`. Establish `hf0 : f ≠ 0`. Introduce and unpack `rfl`.

Use `h0 (Subtype.ext (funext fun g => ?_))` and prove the remaining obligations. Take `⟨γ, h, u, hu, rfl⟩` from `decomp N hN g`. Rewrite using `[hL γ h u hu]`. Simplify using `[nsl]`. Establish `hhol : IsHol k (lev N) ω φ` using `⟨hcusp.1, fun w u hu => hfix _ (kLocal N hN w u hu), hc, hlow.wt, hlow.low⟩`.

Take `⟨g, hg⟩` from `eigEx N k hk1 χ f hf hf0 fun p => Classical.epsilon (IsEigAt k χ f p)`. Take `⟨χ', g', hg'⟩` from `untwist k N hk1 χ ψ g`. Use `⟨N * N, inferInstance, χ', g', ?_⟩` and prove the remaining obligations. Use `filter_upwards [Gk.satAE ℚ 2 π, ev_not_dvd (NeZero.ne N), Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.unr_ae_and_level ℚ ν).1] with w ⟨B, hB⟩ hw hu`. Take `⟨α, β, rfl⟩` from `Multiset.card_eq_two.1 (TR.CuspSub.HasSat.card hB)`.

Use `⟨α, β, hB, ?_⟩` and prove the remaining obligations. Establish `hT` using `TR.CuspSub.HasSat.twist hB hu`. Establish `hp` using `(places w).1`. Establish `hv : GlobalTheory.LFun.IsSatVecGL w (locSm ℚ w) φ {α * ν.val w, β * ν.val w}` using `(hT.2 ⟨φ, hφ⟩ (GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (hfix _ (kLocal N hN w u (by`. Rewrite using `[(places w).2.2.2 N hN hw, level_zero_eq_maximal_compact])))) fun e => h0 (congrArg Subtype.val e)).map` and apply the resulting hypothesis.

Use the proof step `(π.twist ν).V.subtype (fun _ _ => rfl) h0`. Take `⟨h1, h2⟩` from `eigOf k N hk1 hN χ ω hχ f φ hL hhol w _ _ hw hv`. Establish `h3` using `Classical.epsilon_spec (p := IsEigAt k χ f (normV w)) ⟨_, h1⟩`. Establish `h4` using `(hg _ hp h3).trans (eig_unique hf0 h3 h1)`. Take `⟨h5, h6⟩` from `hg' _ hp hw`.

Establish `h7` using `(charVal N hN ψ ν hν).2 w hw`. Establish `h8 : ψ (normV w : ZMod N) ≠ 0` using `h7 ▸ Units.ne_zero _`. Simplify using `only [Units.val_mul, h7] at h2 h4 ⊢`. Prove the components needed by the constructor for the conclusion. Use `mul_right_cancel₀ h8 ?_` and prove the remaining obligations.

Rewrite using `[h5, h4]`. Expand and normalize the polynomial expressions, which then agree. Use `mul_right_cancel₀ (pow_ne_zero 2 h8) ?_` and prove the remaining obligations. Rewrite using `[h6, ← h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Af.Rn.eigOfLow :
    UpperTheory.V.Sd.Wc.CentChar → UpperTheory.V.Af.Rn.EigOfLow := by
  intro hCC k hk1 π hlw
  obtain ⟨N, ψ, ν, hN, hν, φ, hφ, h0, hlow, hfix⟩ := levelVec k π hlw
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨ω, hω, -⟩ := hCC ℚ (π.twist ν)
  have hc := fun z g => hω z φ hφ g
  obtain ⟨χ, hχ⟩ := charOf N hN ω φ h0 hlow.one hfix hc
  have hcusp := (π.twist ν).cusp φ hφ
  obtain ⟨f, hf, hL⟩ := deadel k N hN χ ω hχ φ hcusp hlow hfix hc
  have hf0 : f ≠ 0 := by
    rintro rfl
    refine h0 (Subtype.ext (funext fun g => ?_))
    obtain ⟨γ, h, u, hu, rfl⟩ := decomp N hN g
    rw [hL γ h u hu]
    simp [nsl]
  have hhol : IsHol k (lev N) ω φ := ⟨hcusp.1, fun w u hu => hfix _ (kLocal N hN w u hu), hc, hlow.wt, hlow.low⟩
  obtain ⟨g, hg⟩ := eigEx N k hk1 χ f hf hf0 fun p => Classical.epsilon (IsEigAt k χ f p)
  obtain ⟨χ', g', hg'⟩ := untwist k N hk1 χ ψ g
  refine ⟨N * N, inferInstance, χ', g', ?_⟩
  filter_upwards [Gk.satAE ℚ 2 π, ev_not_dvd (NeZero.ne N),
    Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.unr_ae_and_level ℚ ν).1] with w ⟨B, hB⟩ hw hu
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 (TR.CuspSub.HasSat.card hB)
  refine ⟨α, β, hB, ?_⟩
  have hT := TR.CuspSub.HasSat.twist hB hu
  have hp := (places w).1
  have hv : GlobalTheory.LFun.IsSatVecGL w (locSm ℚ w) φ {α * ν.val w, β * ν.val w} :=
    (hT.2 ⟨φ, hφ⟩ (GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (hfix _ (kLocal N hN w u (by
      rwa [(places w).2.2.2 N hN hw, level_zero_eq_maximal_compact])))) fun e => h0 (congrArg Subtype.val e)).map
      (π.twist ν).V.subtype (fun _ _ => rfl) h0
  obtain ⟨h1, h2⟩ := eigOf k N hk1 hN χ ω hχ f φ hL hhol w _ _ hw hv
  have h3 := Classical.epsilon_spec (p := IsEigAt k χ f (normV w)) ⟨_, h1⟩
  have h4 := (hg _ hp h3).trans (eig_unique hf0 h3 h1)
  obtain ⟨h5, h6⟩ := hg' _ hp hw
  have h7 := (charVal N hN ψ ν hν).2 w hw
  have h8 : ψ (normV w : ZMod N) ≠ 0 := h7 ▸ Units.ne_zero _
  simp only [Units.val_mul, h7] at h2 h4 ⊢
  constructor
  · refine mul_right_cancel₀ h8 ?_
    rw [h5, h4]; ring
  · refine mul_right_cancel₀ (pow_ne_zero 2 h8) ?_
    rw [h6, ← h2]; ring
