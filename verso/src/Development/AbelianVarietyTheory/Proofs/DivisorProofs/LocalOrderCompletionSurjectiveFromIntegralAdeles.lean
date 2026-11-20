import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulMemIntA
open IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.OrdLift

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Introduce `v` and use `by rw [map_one]; exact one_mem _`.
-/
theorem one_mem_intAf : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := fun v => by
  rw [map_one]; exact one_mem _

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.Uc13.mul_mem_intA <;> assumption`.
-/
theorem mul_mem_intA {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E} (hx : x ∈ GlobalTheory.PlaceComp.intA F E)
    (hy : y ∈ GlobalTheory.PlaceComp.intA F E) : x * y ∈ GlobalTheory.PlaceComp.intA F E :=
  by apply _root_.UpperTheory.Reformulated.B.Uc13.mul_mem_intA <;> assumption

end GlobalTheory.OrdLift

/- English proof (translation)
Introduce `F E _ _ _ _ _ v a ha`. Proceed by induction on `ha using Subring.closure_induction with`. Consider the case `mem y hy`. Take `⟨b, hb, x, rfl⟩` from `hy`. Use `⟨Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v b ⊗ₜ[F] (x : E), AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf F v ⟨b, hb⟩, x, rfl⟩, ?_⟩` and prove the remaining obligations.

Use `show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v b) ⊗ₜ[F] (x : E) = _`. Rewrite using `[GlobalTheory.SplitIdem.evalV_singleV_same]`. Consider the case `zero => exact ⟨0, zero_mem _, map_zero _⟩`. Consider the case `one`. Use `⟨1, AddSubgroup.subset_closure ⟨1, GlobalTheory.OrdLift.one_mem_intAf F, 1, ?_⟩, map_one _⟩` and prove the remaining obligations.

Simplify using `[Algebra.TensorProduct.one_def]`. Consider the case `add x y _ _ hx hy`. Take `⟨s, hs, rfl⟩` from `hx`. Take `⟨t, ht, rfl⟩` from `hy`. Conclude with `⟨s + t, add_mem hs ht, map_add _ _ _⟩`.

Consider the case `neg x _ hx`. Take `⟨s, hs, rfl⟩` from `hx`. Conclude with `⟨-s, neg_mem hs, map_neg _ _⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨s, hs, rfl⟩` from `hx`.

Take `⟨t, ht, rfl⟩` from `hy`. Conclude with `⟨s * t, GlobalTheory.OrdLift.mul_mem_intA F E hs ht, map_mul _ _ _⟩`.
-/
theorem GlobalTheory.OrdLift.ordAt_lift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E),
    a ∈ GlobalTheory.PlaceComp.ordAt E v → ∃ t ∈ GlobalTheory.PlaceComp.intA F E, GlobalTheory.PlaceComp.evF E v t = a := by
  intro F E _ _ _ _ _ v a ha
  induction ha using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, x, rfl⟩ := hy
    refine ⟨Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v b ⊗ₜ[F] (x : E),
      AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf F v ⟨b, hb⟩, x, rfl⟩, ?_⟩
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v b) ⊗ₜ[F] (x : E) = _
    rw [GlobalTheory.SplitIdem.evalV_singleV_same]
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | one =>
    refine ⟨1, AddSubgroup.subset_closure ⟨1, GlobalTheory.OrdLift.one_mem_intAf F, 1, ?_⟩, map_one _⟩
    simp [Algebra.TensorProduct.one_def]
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s + t, add_mem hs ht, map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact ⟨-s, neg_mem hs, map_neg _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s * t, GlobalTheory.OrdLift.mul_mem_intA F E hs ht, map_mul _ _ _⟩

end
