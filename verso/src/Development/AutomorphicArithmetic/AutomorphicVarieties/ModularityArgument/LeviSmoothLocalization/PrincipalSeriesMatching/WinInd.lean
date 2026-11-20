import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.CrossG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.UnrOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormVal

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `e : ∀ c : ℝ, ((q ^ f : ℝ)) ^ c = (q ^ c) ^ f`. Introduce `c`. Rewrite using `[← Real.rpow_natCast q f, ← Real.rpow_mul hq.le, mul_comm, Real.rpow_mul hq.le, Real.rpow_natCast]`. Rewrite `h1`, `h2` using `[e]`. Conclude with `⟨lt_of_pow_lt_pow_left₀ f hx h1, lt_of_pow_lt_pow_left₀ f (Real.rpow_nonneg hq.le _) h2⟩`.
-/
private theorem rootBounds {q x a b : ℝ} {f : ℕ} (hf : 0 < f) (hq : 0 < q) (hx : 0 ≤ x)
    (h1 : ((q ^ f : ℝ)) ^ a < x ^ f) (h2 : x ^ f < ((q ^ f : ℝ)) ^ b) :
    q ^ a < x ∧ x < q ^ b := by
  have e : ∀ c : ℝ, ((q ^ f : ℝ)) ^ c = (q ^ c) ^ f := by
    intro c
    rw [← Real.rpow_natCast q f, ← Real.rpow_mul hq.le, mul_comm, Real.rpow_mul hq.le, Real.rpow_natCast]
  rw [e] at h1 h2
  exact ⟨lt_of_pow_lt_pow_left₀ f hx h1, lt_of_pow_lt_pow_left₀ f (Real.rpow_nonneg hq.le _) h2⟩

/- English proof (translation)
Introduce `K M _ _ _ _ _ _ _ h2 P π hsys t v hw`. Use `⟨indTor K M h2 P π hsys v fun w => ⟨(hw w).1.1, (hw w).2⟩, fun s hs ξ hξ => ?_⟩` and prove the remaining obligations. Establish `hs' : ∀ w : GroundTheory.Global.SemiLocal.PlacesOver M v, ∃ s', SuppAt π w.1 s'` using `fun w => (suppFacts M 2 (by norm_num) π w.1).1`. Use `choose s' hs' using hs'`. Take `⟨w, hζ⟩` from `indX K M h2 P π hsys v s s' hs hs' ξ hξ`.

Take `⟨hsm, -⟩` from `hξ`. Take `⟨-, hnorm, hf, hN⟩` from `normVal K M v w ξ`. Take `⟨b1, b2⟩` from `(hw w).1.2 (s' w) (hs' w) _ hζ`. Establish `hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)` using `Nat.cast_pos.2 (Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot))`. Simplify using `only [MonoidHom.comp_apply] at b1 b2`.

Rewrite `b1`, `b2` using `[hnorm hsm, hN, Nat.cast_pow]`. Conclude with `rootBounds hf hq (norm_nonneg _) b1 b2`.
-/
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winInd :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.WinInd := by
  intro K M _ _ _ _ _ _ _ h2 P π hsys t v hw
  refine ⟨indTor K M h2 P π hsys v fun w => ⟨(hw w).1.1, (hw w).2⟩, fun s hs ξ hξ => ?_⟩
  have hs' : ∀ w : GroundTheory.Global.SemiLocal.PlacesOver M v, ∃ s', SuppAt π w.1 s' := fun w =>
    (suppFacts M 2 (by norm_num) π w.1).1
  choose s' hs' using hs'
  obtain ⟨w, hζ⟩ := indX K M h2 P π hsys v s s' hs hs' ξ hξ
  obtain ⟨hsm, -⟩ := hξ
  obtain ⟨-, hnorm, hf, hN⟩ := normVal K M v w ξ
  obtain ⟨b1, b2⟩ := (hw w).1.2 (s' w) (hs' w) _ hζ
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot))
  simp only [MonoidHom.comp_apply] at b1 b2
  rw [hnorm hsm, hN, Nat.cast_pow] at b1 b2
  exact rootBounds hf hq (norm_nonneg _) b1 b2
