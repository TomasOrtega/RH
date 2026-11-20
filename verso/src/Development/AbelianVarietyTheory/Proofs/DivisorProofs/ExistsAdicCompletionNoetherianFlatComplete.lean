import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

namespace GlobalTheory.AdicPackage

/- English proof (translation)
Introduce `B _ _ I`. Establish `fg : I.FG` using `IsNoetherian.noetherian I`. Use `⟨AdicCompletion I B, inferInstance, algebraMap B (AdicCompletion I B), GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B I, RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian I), AdicCompletion.isAdicComplete_self I fg, ?_⟩` and prove the remaining obligations. Introduce `m a h`. Use `le_antisymm ?_ Ideal.le_comap_map` and prove the remaining obligations.

Establish `key : ∀ y : B, (AdicCompletion.evalₐ I m) (algebraMap B (AdicCompletion I B) y) = Ideal.Quotient.mk (I ^ m) y` using `fun y => (AdicCompletion.evalₐ I m).commutes y`. Establish `hle : a.map (algebraMap B (AdicCompletion I B)) ≤ (a.map (Ideal.Quotient.mk (I ^ m))).comap (AdicCompletion.evalₐ I m)`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `y hy`. Simplify using `only [Ideal.mem_comap]`.

Rewrite using `[key]`. Conclude with `Ideal.mem_map_of_mem _ hy`. Introduce `x hx`. Rewrite `hx` using `[Ideal.mem_comap]`. Establish `h2` using `hle hx`.

Rewrite `h2` using `[Ideal.mem_comap, key]`. Conclude with `(Ideal.mem_quotient_iff_mem h).1 h2`.
-/
theorem adicCompletion_package : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I : Ideal B),
    ∃ (C : Type) (_ : CommRing C) (φ : B →+* C), IsNoetherianRing C ∧ φ.Flat ∧
      IsAdicComplete (I.map φ) C ∧ ∀ (m : ℕ) (a : Ideal B), I ^ m ≤ a → (a.map φ).comap φ = a := by
  intro B _ _ I
  have fg : I.FG := IsNoetherian.noetherian I
  refine ⟨AdicCompletion I B, inferInstance, algebraMap B (AdicCompletion I B),
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B I,
    RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian I),
    AdicCompletion.isAdicComplete_self I fg, ?_⟩
  intro m a h
  refine le_antisymm ?_ Ideal.le_comap_map
  have key : ∀ y : B, (AdicCompletion.evalₐ I m) (algebraMap B (AdicCompletion I B) y) =
      Ideal.Quotient.mk (I ^ m) y := fun y => (AdicCompletion.evalₐ I m).commutes y
  have hle : a.map (algebraMap B (AdicCompletion I B)) ≤
      (a.map (Ideal.Quotient.mk (I ^ m))).comap (AdicCompletion.evalₐ I m) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp only [Ideal.mem_comap]
    rw [key]
    exact Ideal.mem_map_of_mem _ hy
  intro x hx
  rw [Ideal.mem_comap] at hx
  have h2 := hle hx
  rw [Ideal.mem_comap, key] at h2
  exact (Ideal.mem_quotient_iff_mem h).1 h2

end GlobalTheory.AdicPackage
