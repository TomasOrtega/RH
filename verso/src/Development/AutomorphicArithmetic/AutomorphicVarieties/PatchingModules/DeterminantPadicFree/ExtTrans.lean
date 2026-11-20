import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ F n x x' x'' j j' h1 h2`. Take `⟨⟨hi, hl, hf, hρ, ha, hψ⟩, hw, ht⟩` from `h1`. Take `⟨⟨hi', hl', hf', hρ', ha', hψ'⟩, hw', ht'⟩` from `h2`. Use `⟨⟨hi'.comp hi, @RingHom.isLocalHom_comp _ _ _ _ _ _ j' j hl' hl, hf'.comp hf, ?_, ha'.trans ha, ?_⟩, ?_, ht'.trans ht⟩` and prove the remaining obligations. Rewrite using `[hρ', hρ]`.

Simplify using `only [pushRep, GeneralLinearGroup.map_comp, MonoidHom.comp_assoc]`. Introduce `v i`. Rewrite using `[hψ', hψ]`. Use extensionality with `g`. Simplify using `[pushCh]`.

Introduce `v`. Rewrite using `[hw', hw, GeneralLinearGroup.map_comp]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Pa.Det.extTrans :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' x'' : NP F n) (j : x.A →+* x'.A) (j' : x'.A →+* x''.A), x.Ext2 x' j → x'.Ext2 x'' j' → x.Ext2 x'' (j'.comp j) := by
  intro l _ F n x x' x'' j j' h1 h2
  obtain ⟨⟨hi, hl, hf, hρ, ha, hψ⟩, hw, ht⟩ := h1
  obtain ⟨⟨hi', hl', hf', hρ', ha', hψ'⟩, hw', ht'⟩ := h2
  refine ⟨⟨hi'.comp hi, @RingHom.isLocalHom_comp _ _ _ _ _ _ j' j hl' hl, hf'.comp hf, ?_, ha'.trans ha, ?_⟩,
    ?_, ht'.trans ht⟩
  · rw [hρ', hρ]
    simp only [pushRep, GeneralLinearGroup.map_comp, MonoidHom.comp_assoc]
  · intro v i
    rw [hψ', hψ]
    ext g
    simp [pushCh]
  · intro v
    rw [hw', hw, GeneralLinearGroup.map_comp]
    rfl
