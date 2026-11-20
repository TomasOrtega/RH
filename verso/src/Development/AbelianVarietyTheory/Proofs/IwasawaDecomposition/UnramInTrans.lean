import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published

namespace GlobalTheory.Mem.UnramTower

/- English proof (translation)
Introduce `K L N _ _ _ _ _ _ _ _ _ _ _ _ hL hN 𝔭 σ hσ`. Take `⟨Q, hQ, hQo, hσ⟩` from `hσ`. Establish `hσ' : ∀ x : 𝓞 N, σ • x - x ∈ Q` using `fun x => hσ x`. Establish `hPo : (Q.under (𝓞 L)).LiesOver 𝔭.asIdeal` using `inferInstance`. Establish `hP : (Q.under (𝓞 L)).IsPrime` using `inferInstance`.

Establish `h1 : σ.restrictNormal L = 1`. Use `hL 𝔭 _ ⟨Q.under (𝓞 L), hP, hPo, ?_⟩` and prove the remaining obligations. Introduce `x`. Establish `hx` using `hσ' (algebraMap (𝓞 L) (𝓞 N) x)`. Establish `e : algebraMap (𝓞 L) (𝓞 N) ((σ.restrictNormal L) • x) = σ • algebraMap (𝓞 L) (𝓞 N) x`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `AlgEquiv.restrictNormal_commutes σ L (x : L)`. Use `show (σ.restrictNormal L) • x - x ∈ Ideal.comap (algebraMap (𝓞 L) (𝓞 N)) Q`. Rewrite using `[Ideal.mem_comap, map_sub, e]`. Conclude with `hx`.

Establish `hfix : ∀ y : L, σ (algebraMap L N y) = algebraMap L N y`. Introduce `y`. Rewrite using `[← AlgEquiv.restrictNormal_commutes σ L y, h1]`. Both sides reduce to the same expression. Set `τ : N ≃ₐ[L] N` to `{ σ.toRingEquiv with commutes' := hfix }`.

Set `P : HeightOneSpectrum (𝓞 L)` to `⟨Q.under (𝓞 L), hP, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _⟩`. Establish `h2 : τ = 1`. Use `hN P τ ⟨Q, hQ, ⟨rfl⟩, ?_⟩` and prove the remaining obligations. Introduce `x`. Conclude with `hσ' x`.

Use extensionality with `y`. Conclude with `DFunLike.congr_fun h2 y`.
-/
theorem unramIn_trans : ∀ (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field N] [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L] [IsGalois K N], (∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn L 𝔭) → (∀ P : HeightOneSpectrum (𝓞 L), GlobalTheory.NT.UnramIn N P) → ∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn N 𝔭 := by
  intro K L N _ _ _ _ _ _ _ _ _ _ _ _ hL hN 𝔭 σ hσ
  obtain ⟨Q, hQ, hQo, hσ⟩ := hσ
  have hσ' : ∀ x : 𝓞 N, σ • x - x ∈ Q := fun x => hσ x
  have hPo : (Q.under (𝓞 L)).LiesOver 𝔭.asIdeal := inferInstance
  have hP : (Q.under (𝓞 L)).IsPrime := inferInstance
  have h1 : σ.restrictNormal L = 1 := by
    refine hL 𝔭 _ ⟨Q.under (𝓞 L), hP, hPo, ?_⟩
    intro x
    have hx := hσ' (algebraMap (𝓞 L) (𝓞 N) x)
    have e : algebraMap (𝓞 L) (𝓞 N) ((σ.restrictNormal L) • x) = σ • algebraMap (𝓞 L) (𝓞 N) x := by
      apply RingOfIntegers.ext
      exact AlgEquiv.restrictNormal_commutes σ L (x : L)
    show (σ.restrictNormal L) • x - x ∈ Ideal.comap (algebraMap (𝓞 L) (𝓞 N)) Q
    rw [Ideal.mem_comap, map_sub, e]
    exact hx
  have hfix : ∀ y : L, σ (algebraMap L N y) = algebraMap L N y := by
    intro y
    rw [← AlgEquiv.restrictNormal_commutes σ L y, h1]
    rfl
  let τ : N ≃ₐ[L] N := { σ.toRingEquiv with commutes' := hfix }
  let P : HeightOneSpectrum (𝓞 L) :=
    ⟨Q.under (𝓞 L), hP, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _⟩
  have h2 : τ = 1 := by
    refine hN P τ ⟨Q, hQ, ⟨rfl⟩, ?_⟩
    intro x
    exact hσ' x
  ext y
  exact DFunLike.congr_fun h2 y

end GlobalTheory.Mem.UnramTower
