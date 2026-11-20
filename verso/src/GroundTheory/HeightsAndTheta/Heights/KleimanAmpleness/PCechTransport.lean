import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSerrePoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace Cech

/- English proof (translation)
Introduce `n U R _ G _ _ G' _ _ ρ ρ' deg deg' φ hφ hdeg hinj hmap i`. Establish `minj : ∀ i, Function.Injective (mapC (G` using `G) (G' := G') φ i) := fun i s t h => funext fun I => hinj I.1 (congrFun h I)`. Establish `lift : ∀ (i : ℕ) (w' : Cochain G' i), w' ∈ Cdeg G' deg' i → ∃ w ∈ Cdeg G deg i, mapC φ i w = w'`. Introduce `i w' hw'`. Establish `h : ∀ I : Idx U i, ∃ x ∈ deg I.1, φ I.1 x = w' I` using `fun I => by`.

Establish `hI : w' I ∈ deg' I.1` using `hw' I (Set.mem_univ _)`. Rewrite `hI` using `[← hmap I.1]`. Conclude with `Submodule.mem_map.mp hI`. Use `choose w hw hφw using h`. Conclude with `⟨w, fun I _ => hw I, funext fun I => hφw I⟩`.

Establish `bdry : ∀ (i : ℕ) (z : Cochain G i), mapC φ i z ∈ bdryDeg G' deg' ρ' i → z ∈ bdryDeg G deg ρ i`. Introduce `i z h`. Consider the cases of `i with`. Consider the case `zero`. Express the relevant statement in the definitionally equal form `mapC φ 0 z ∈ (⊥ : Submodule R _) at h`.

Express the relevant statement in the definitionally equal form `z ∈ (⊥ : Submodule R _)`. Rewrite `h`, the goal using `[Submodule.mem_bot]`. Conclude with `minj 0 (h.trans (map_zero _).symm)`. Consider the case `succ i`. Express the relevant statement in the definitionally equal form `mapC φ (i + 1) z ∈ (Cdeg G' deg' i).map (d G' ρ' i) at h`.

Express the relevant statement in the definitionally equal form `z ∈ (Cdeg G deg i).map (d G ρ i)`. Take `⟨w', hw', hd⟩` from `Submodule.mem_map.mp h`. Take `⟨w, hw, rfl⟩` from `lift i w' hw'`. Use `Submodule.mem_map.mpr ⟨w, hw, minj (i + 1) ?_⟩` and prove the remaining obligations. Rewrite using `[mapC_d φ hφ]`.

Conclude with `hd`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = 0 at hx`. Establish `hx'` using `(Submodule.Quotient.mk_eq_zero _).mp hx`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mpr (bdry i z hx')`. Introduce `y`. Take `⟨z', rfl⟩` from `Submodule.Quotient.mk_surjective _ y`.

Take `⟨w, hw, hwz⟩` from `lift i z' z'.2.2`. Establish `hdw : d G ρ i w = 0`. Apply `minj (i + 1)` to reduce the goal to its premises. Rewrite using `[mapC_d φ hφ, hwz, map_zero]`. Conclude with `z'.2.1`.

Use `⟨Submodule.Quotient.mk ⟨w, hdw, hw⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = _`. Use `congr 1`. Conclude with `Subtype.ext hwz`.
-/
theorem Transport.proof : Transport.Statement.{u, v, w} := by
  intro n U R _ G _ _ G' _ _ ρ ρ' deg deg' φ hφ hdeg hinj hmap i

  have minj : ∀ i, Function.Injective (mapC (G := G) (G' := G') φ i) :=
    fun i s t h => funext fun I => hinj I.1 (congrFun h I)

  have lift : ∀ (i : ℕ) (w' : Cochain G' i), w' ∈ Cdeg G' deg' i →
      ∃ w ∈ Cdeg G deg i, mapC φ i w = w' := by
    intro i w' hw'
    have h : ∀ I : Idx U i, ∃ x ∈ deg I.1, φ I.1 x = w' I := fun I => by
      have hI : w' I ∈ deg' I.1 := hw' I (Set.mem_univ _)
      rw [← hmap I.1] at hI
      exact Submodule.mem_map.mp hI
    choose w hw hφw using h
    exact ⟨w, fun I _ => hw I, funext fun I => hφw I⟩

  have bdry : ∀ (i : ℕ) (z : Cochain G i), mapC φ i z ∈ bdryDeg G' deg' ρ' i → z ∈ bdryDeg G deg ρ i := by
    intro i z h
    cases i with
    | zero =>
      change mapC φ 0 z ∈ (⊥ : Submodule R _) at h
      change z ∈ (⊥ : Submodule R _)
      rw [Submodule.mem_bot] at h ⊢
      exact minj 0 (h.trans (map_zero _).symm)
    | succ i =>
      change mapC φ (i + 1) z ∈ (Cdeg G' deg' i).map (d G' ρ' i) at h
      change z ∈ (Cdeg G deg i).map (d G ρ i)
      obtain ⟨w', hw', hd⟩ := Submodule.mem_map.mp h
      obtain ⟨w, hw, rfl⟩ := lift i w' hw'
      refine Submodule.mem_map.mpr ⟨w, hw, minj (i + 1) ?_⟩
      rw [mapC_d φ hφ]
      exact hd
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk _ = 0 at hx
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr (bdry i z hx')
  · intro y
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨w, hw, hwz⟩ := lift i z' z'.2.2
    have hdw : d G ρ i w = 0 := by
      apply minj (i + 1)
      rw [mapC_d φ hφ, hwz, map_zero]
      exact z'.2.1
    refine ⟨Submodule.Quotient.mk ⟨w, hdw, hw⟩, ?_⟩
    change Submodule.Quotient.mk _ = _
    congr 1
    exact Subtype.ext hwz

end Cech

end

end GroundTheory.Heights₂.Heights.Kleiman
