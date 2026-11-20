import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties

noncomputable section

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

/- English proof (translation)
Introduce `Ω _ _ _ ε X l _ n`. Take `⟨hsurj, hinj, hmul, hone, hsmul, hmap, hsucc⟩` from `H3.cls_props Ω ε X l n`. Establish `hdiv : ∀ f f' : X.Kˣ, X.cls l n (f / f') = X.cls l n f - X.cls l n f'`. Introduce `f f'`. Establish `h` using `hmul (f / f') f'`.

Rewrite `h` using `[div_mul_cancel]`. Rewrite using `[h]`. Normalize the expressions using the abelian group laws. Establish `hpow : ∀ (f : X.Kˣ) (k : ℕ), X.cls l n (f ^ k) = k • X.cls l n f`. Introduce `f k`.

Proceed by induction on `k with`. Consider the case `zero => simp [hone]`. Consider the case `succ k ih => rw [pow_succ, hmul, ih, succ_nsmul]`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f`.

Establish `hf : (f : X.K) ≠ 0` using `f.ne_zero`. Use `show (AdicCompletion.eval (idl l) (X.Kl l) n) (clsK X l n (f : X.K)) = X.cls l n f`. Unfold `clsK`. Rewrite using `[dif_pos hf, Units.mk0_val]`. Unfold `liftK`.

Conclude with `Classical.epsilon_spec (p := fun b => (AdicCompletion.eval (idl l) (X.Kl l) n) b = X.cls l n f) (AdicCompletion.eval_surjective (idl l) (X.Kl l) n (X.cls l n f))`. Introduce `f f' a a' ha ha'`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (AdicCompletion.eval (idl l) (X.Kl l) n) (a + a') = X.cls l n (f * f')`. Rewrite using `[map_add, hmul]`.

Rewrite using `[ha, ha']`. Use `show (AdicCompletion.eval (idl l) (X.Kl l) n) (a - a') = X.cls l n (f / f')`. Rewrite using `[map_sub, hdiv]`. Rewrite using `[ha, ha']`. Introduce `f a k ha show (AdicCompletion.eval (idl l) (X.Kl l) n) (k • a) = X.cls l n (f ^ k)`.

Rewrite using `[map_nsmul, hpow]`. Rewrite using `[ha]`. Introduce `f f' a a' ha ha' hc`. Take `⟨g, hg⟩` from `hc`. Rewrite using `[map_sub]`.

Rewrite using `[ha, ha', (hinj f f').2 ⟨g, hg⟩, sub_self]`. Introduce `φ f a ha`. Conclude with `hmap φ a f ha`. Introduce `f a ha`. Conclude with `hsucc a f ha`.

Introduce `f k a ha`. Use `⟨((PadicInt.toZModPow n) k).val, ?_⟩` and prove the remaining obligations. Use `show (AdicCompletion.eval (idl l) (X.Kl l) n) (k • a) = X.cls l n (f ^ ((PadicInt.toZModPow n) k).val)`. Rewrite using `[map_smul]`. Rewrite using `[ha, hsmul]`.
-/
theorem sCls : SCls := by
  intro Ω _ _ _ ε X l _ n
  obtain ⟨hsurj, hinj, hmul, hone, hsmul, hmap, hsucc⟩ := H3.cls_props Ω ε X l n
  have hdiv : ∀ f f' : X.Kˣ, X.cls l n (f / f') = X.cls l n f - X.cls l n f' := by
    intro f f'
    have h := hmul (f / f') f'
    rw [div_mul_cancel] at h
    rw [h]
    abel
  have hpow : ∀ (f : X.Kˣ) (k : ℕ), X.cls l n (f ^ k) = k • X.cls l n f := by
    intro f k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ, hmul, ih, succ_nsmul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    have hf : (f : X.K) ≠ 0 := f.ne_zero
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (clsK X l n (f : X.K)) = X.cls l n f
    unfold clsK
    rw [dif_pos hf, Units.mk0_val]
    unfold liftK
    exact Classical.epsilon_spec (p := fun b => (AdicCompletion.eval (idl l) (X.Kl l) n) b = X.cls l n f)
      (AdicCompletion.eval_surjective (idl l) (X.Kl l) n (X.cls l n f))
  · intro f f' a a' ha ha'
    refine ⟨?_, ?_⟩
    · show (AdicCompletion.eval (idl l) (X.Kl l) n) (a + a') = X.cls l n (f * f')
      rw [map_add, hmul]
      rw [ha, ha']
    · show (AdicCompletion.eval (idl l) (X.Kl l) n) (a - a') = X.cls l n (f / f')
      rw [map_sub, hdiv]
      rw [ha, ha']
  · intro f a k ha
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (k • a) = X.cls l n (f ^ k)
    rw [map_nsmul, hpow]
    rw [ha]
  · intro f f' a a' ha ha' hc
    obtain ⟨g, hg⟩ := hc
    rw [map_sub]
    rw [ha, ha', (hinj f f').2 ⟨g, hg⟩, sub_self]
  · intro φ f a ha
    exact hmap φ a f ha
  · intro f a ha
    exact hsucc a f ha
  · intro f k a ha
    refine ⟨((PadicInt.toZModPow n) k).val, ?_⟩
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (k • a) = X.cls l n (f ^ ((PadicInt.toZModPow n) k).val)
    rw [map_smul]
    rw [ha, hsmul]

end UpperTheory.V.Z.Kato.Nb

end
