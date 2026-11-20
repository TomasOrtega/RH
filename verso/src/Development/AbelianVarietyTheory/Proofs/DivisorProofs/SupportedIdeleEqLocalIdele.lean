import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.Div.SuppIdele

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem snd_apply_mul {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a b : AdeleRing (𝓞 K) K) : (a * b).2 v = a.2 v * b.2 v := rfl

/- English proof (translation)
Introduce `K _ _ v a ha`. Set `x : (v.adicCompletion K)ˣ` to `{ val := (a : AdeleRing (𝓞 K) K).2 v inv := ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v val_inv := by`. Rewrite using `[← snd_apply_mul, Units.mul_inv]`. Both sides reduce to the same expression. Use `inv_val := by`.

Rewrite using `[← snd_apply_mul, Units.inv_mul]`. Use `rfl }`. Use `⟨x, rfl, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `w`. Conclude with `(ha.1 w).symm`. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `w`. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Conclude with `(localIdele_snd_self K w x).trans rfl`. Conclude with `((localIdele_isSupportedAt K v x).2 w hw).trans (ha.2 w hw).symm`.
-/
theorem supported_eq_localIdele : ∀ {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {a : Ideles K},
    IsSupportedAt K a v → ∃ x : (v.adicCompletion K)ˣ, (x : v.adicCompletion K) = (a : AdeleRing (𝓞 K) K).2 v ∧
      localIdele K v x = a := by
  intro K _ _ v a ha
  classical
  let x : (v.adicCompletion K)ˣ :=
    { val := (a : AdeleRing (𝓞 K) K).2 v
      inv := ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v
      val_inv := by
        rw [← snd_apply_mul, Units.mul_inv]; rfl
      inv_val := by
        rw [← snd_apply_mul, Units.inv_mul]; rfl }
  refine ⟨x, rfl, ?_⟩
  apply Units.ext
  apply Prod.ext
  · funext w
    exact (ha.1 w).symm
  · apply RestrictedProduct.ext
    intro w
    by_cases hw : w = v
    · subst hw
      exact (localIdele_snd_self K w x).trans rfl
    · exact ((localIdele_isSupportedAt K v x).2 w hw).trans (ha.2 w hw).symm

end GlobalTheory.Div.SuppIdele
