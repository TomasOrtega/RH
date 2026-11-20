import Formalism.PeriodIntegrals.LocHerm
import Formalism.PeriodIntegrals.AlgebraMapMemO

noncomputable section

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.Glue

def Riesz : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (f : V →ₗ[E] E),
    ∃ x : V, ∀ v, H.h v x = f v

def Scale : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → ∀ (V : Type) [AddCommGroup V] [Module E V] (S : Submodule M.L.O V)
    (w : V), w ∈ Submodule.span E (S : Set V) →
    ∃ r : 𝒪[F], (r : F) ≠ 0 ∧ algebraMap F E r • w ∈ S

def Pair : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V)
    (abelian₂ : Submodule M.L.O V), H.IsSelfDual abelian₂ → ∀ (A B : Submodule E V) (hAB : IsCompl A B),
    (∀ a ∈ A, ∀ b ∈ B, H.h a b = 0 ∧ H.h b a = 0) →
    ∀ u : V, u ∈ A → ((∃ x ∈ abelian₂, (Submodule.linearProjOfIsCompl A B hAB x : V) = u) ↔
        ∀ y ∈ abelian₂, y ∈ A → H.h u y ∈ M.L.O)

set_option linter.deprecated false in
/- English proof (translation)
Unfold `PI.LocHerm.LocGlue PI.LocHerm.AllLoc`. Introduce `F _ _ _ E _ _ _ _ M hM V _ _ H abelian₂ hLam U hU`. Use `⟨fun u hu => hP M hM V H abelian₂ hLam U (H.perp U) hU ?_ u hu, fun u hu => hP M hM V H abelian₂ hLam (H.perp U) U hU.symm ?_ u hu⟩` and prove the remaining obligations. Introduce `a ha b hb`. Establish `hb' : ∀ x ∈ U, H.h b x = 0` using `hb`.

Establish `h1 : H.h b a = 0` using `hb' a ha`. Conclude with `⟨by rw [H.h_herm b a, h1, map_zero], h1⟩`. Introduce `a ha b hb`. Establish `ha' : ∀ x ∈ U, H.h a x = 0` using `ha`. Establish `h1 : H.h a b = 0` using `ha' b hb`.

Conclude with `⟨h1, by rw [H.h_herm a b, h1, map_zero]⟩`.
-/
theorem locGlue_of_pair (hP : Pair) : PI.LocHerm.LocGlue := by
  unfold PI.LocHerm.LocGlue PI.LocHerm.AllLoc
  intro F _ _ _ E _ _ _ _ M hM V _ _ H abelian₂ hLam U hU
  refine ⟨fun u hu => hP M hM V H abelian₂ hLam U (H.perp U) hU ?_ u hu,
    fun u hu => hP M hM V H abelian₂ hLam (H.perp U) U hU.symm ?_ u hu⟩
  · intro a ha b hb
    have hb' : ∀ x ∈ U, H.h b x = 0 := hb
    have h1 : H.h b a = 0 := hb' a ha
    exact ⟨by rw [H.h_herm b a, h1, map_zero], h1⟩
  · intro a ha b hb
    have ha' : ∀ x ∈ U, H.h a x = 0 := ha
    have h1 : H.h a b = 0 := ha' b hb
    exact ⟨h1, by rw [H.h_herm a b, h1, map_zero]⟩

end PI.LocHerm.Glue
