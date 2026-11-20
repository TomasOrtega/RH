import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.FiniteDimensionalTranslationCoordinates

noncomputable section

open GlobalTheory.PRep

namespace UpperTheory.NonzeroTypeTheory

namespace TranslationCoordinates

variable {K : Type} [Group K] (W : Submodule ℂ (K → ℂ))
  (hW : ∀ φ ∈ W, ∀ k : K, rightReg ℂ K ℂ k φ ∈ W)

def rW : Representation ℂ K W := sub (rightReg ℂ K ℂ) W (fun k φ hφ => hW φ hφ k)

def coord {m : ℕ} (c : W ≃ₗ[ℂ] (Fin m → ℂ)) : Representation ℂ K (Fin m → ℂ) where
  toFun k := c.toLinearMap ∘ₗ rW W hW k ∘ₗ c.symm.toLinearMap
  map_one' := by ext v i; simp
  map_mul' a b := by ext v i; simp [map_mul]

end TranslationCoordinates

/- English proof (translation)
Introduce `K _ _ W hfin hW hsm`. Use `hfin` as an intermediate fact. Set `c` to `(Module.finBasis ℂ W).equivFun`. Set `V0` to `TranslationCoordinates.coord W hW c`. Set `e : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] (K → ℂ)` to `W.subtype ∘ₗ c.symm.toLinearMap`.

Establish `he : ∀ k v, e (V0 k v) = rightReg ℂ K ℂ k (e v)`. Introduce `k v`. Simplify using `[e, V0, TranslationCoordinates.coord, TranslationCoordinates.rW, sub]`. Establish `hinj : Function.Injective e` using `W.injective_subtype.comp c.symm.injective`. Use `⟨_, V0, e, hinj, ?_, he, ?_⟩` and prove the remaining obligations.

Use extensionality with `φ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, rfl⟩`. Simplify using `[e]`. Introduce `hφ`.

Conclude with `⟨c ⟨φ, hφ⟩, by simp [e]⟩`. Introduce `v`. Establish `hset : {g : K | V0 g v = v} = {g : K | rightReg ℂ K ℂ g (e v) = e v}`. Use extensionality with `g`. Simplify using `only [Set.mem_ofPred_eq]`.

Rewrite using `[← he]`. Conclude with `hinj.eq_iff.symm`. Rewrite using `[hset]`. Conclude with `hsm _ (by simp [e])`.
-/
theorem finiteDimensionalTranslation_holds : FiniteDimensionalTranslationCoordinates := by
  intro K _ _ W hfin hW hsm
  have := hfin
  let c := (Module.finBasis ℂ W).equivFun
  let V0 := TranslationCoordinates.coord W hW c
  let e : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] (K → ℂ) := W.subtype ∘ₗ c.symm.toLinearMap
  have he : ∀ k v, e (V0 k v) = rightReg ℂ K ℂ k (e v) := by
    intro k v
    simp [e, V0, TranslationCoordinates.coord, TranslationCoordinates.rW, sub]
  have hinj : Function.Injective e := W.injective_subtype.comp c.symm.injective
  refine ⟨_, V0, e, hinj, ?_, he, ?_⟩
  · ext φ
    constructor
    · rintro ⟨v, rfl⟩
      simp [e]
    · intro hφ
      exact ⟨c ⟨φ, hφ⟩, by simp [e]⟩
  · intro v
    have hset : {g : K | V0 g v = v} = {g : K | rightReg ℂ K ℂ g (e v) = e v} := by
      ext g
      simp only [Set.mem_ofPred_eq]
      rw [← he]
      exact hinj.eq_iff.symm
    rw [hset]
    exact hsm _ (by simp [e])

end UpperTheory.NonzeroTypeTheory
