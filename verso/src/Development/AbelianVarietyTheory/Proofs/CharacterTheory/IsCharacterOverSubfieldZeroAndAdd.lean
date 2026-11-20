import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
namespace GlobalTheory.BI

/- English proof (translation)
Set `e : ((Fin n → K) × (Fin m → K)) ≃ₗ[K] (Fin (n + m) → K)` to `(LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) K K).symm ≪≫ₗ LinearEquiv.funCongrLeft K K finSumFinEquiv.symm`. Use `⟨{ toFun := fun g => e.conj ((ρ g).prodMap (σ g)), map_one' := ?_, map_mul' := ?_ }, fun g => ?_⟩` and prove the remaining obligations. Simplify using `only [map_one, LinearMap.prodMap_one]`. Conclude with `e.conj_id`. Introduce `g h`.

Simplify using `only [map_mul]`. Rewrite using `[← LinearMap.prodMap_mul]`. Conclude with `e.conj_comp _ _`. Simplify using `only [Representation.character] show LinearMap.trace K _ (e.conj _) = _`. Rewrite using `[LinearMap.trace_conj', LinearMap.trace_prodMap']`.
-/
private theorem exists_representation_character_eq_add (K : Type) [Field K] (G : Type) [Group G]
    (n m : ℕ) (ρ : Representation K G (Fin n → K)) (σ : Representation K G (Fin m → K)) :
    ∃ τ : Representation K G (Fin (n + m) → K),
      ∀ g, τ.character g = ρ.character g + σ.character g := by
  let e : ((Fin n → K) × (Fin m → K)) ≃ₗ[K] (Fin (n + m) → K) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) K K).symm ≪≫ₗ
      LinearEquiv.funCongrLeft K K finSumFinEquiv.symm
  refine ⟨{ toFun := fun g => e.conj ((ρ g).prodMap (σ g)), map_one' := ?_, map_mul' := ?_ },
    fun g => ?_⟩
  · simp only [map_one, LinearMap.prodMap_one]
    exact e.conj_id
  · intro g h
    simp only [map_mul]
    rw [← LinearMap.prodMap_mul]
    exact e.conj_comp _ _
  · simp only [Representation.character]
    show LinearMap.trace K _ (e.conj _) = _
    rw [LinearMap.trace_conj', LinearMap.trace_prodMap']

/- English proof (translation)
Introduce `K L _ _ _ G _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `_root_.GlobalTheory.BI.IsChar`. Use `⟨0, 1, fun g => ?_⟩` and prove the remaining obligations. Simplify using `[Representation.character]`.

Introduce `a b ha hb`. Unfold `_root_.GlobalTheory.BI.IsChar at ha hb ⊢`. Take `⟨n, ρ, hρ⟩` from `ha`. Take `⟨m, σ, hσ⟩` from `hb`. Take `⟨τ, hτ⟩` from `exists_representation_character_eq_add K G n m ρ σ`.

Use `⟨n + m, τ, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.add_apply, hρ g, hσ g, hτ g, map_add]`.
-/
theorem _root_.GlobalTheory.BI.isChar_zero_and_add : ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    (G : Type) [Group G], _root_.GlobalTheory.BI.IsChar K L (0 : G → L) ∧
      ∀ a b : G → L, _root_.GlobalTheory.BI.IsChar K L a → _root_.GlobalTheory.BI.IsChar K L b →
        _root_.GlobalTheory.BI.IsChar K L (a + b) := by
  intro K L _ _ _ G _
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.BI.IsChar
    refine ⟨0, 1, fun g => ?_⟩
    simp [Representation.character]
  · intro a b ha hb
    unfold _root_.GlobalTheory.BI.IsChar at ha hb ⊢
    obtain ⟨n, ρ, hρ⟩ := ha
    obtain ⟨m, σ, hσ⟩ := hb
    obtain ⟨τ, hτ⟩ := exists_representation_character_eq_add K G n m ρ σ
    refine ⟨n + m, τ, fun g => ?_⟩
    rw [Pi.add_apply, hρ g, hσ g, hτ g, map_add]

end GlobalTheory.BI
