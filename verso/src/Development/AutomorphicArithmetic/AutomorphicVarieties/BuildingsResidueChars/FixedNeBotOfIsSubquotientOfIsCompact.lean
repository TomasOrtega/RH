import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

/- English proof (translation)
Introduce `G _ _ _ V W _ _ _ _ σ π H hπ hsq hH hne`. Take `⟨S, f, hf⟩` from `hsq`. Establish `hS : IsSmooth S.toRepresentation` using `fun v => by`. Establish `: {g : G | S.toRepresentation g v = v} = {g : G | π g v = v}`. Use extensionality with `g`.

Conclude with `Subtype.ext_iff`. Rewrite using `[this]`. Conclude with `hπ v`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 hne`. Take `⟨u, rfl⟩` from `hf x`.

Take `⟨v, hv, e⟩` from `IwahoriOnto.exists_fixed_map_eq hS hH f.toLinearMap u fun h hh => by show f (S.toRepresentation h u) = f u`. Rewrite using `[f.isIntertwining]`. Simplify using `using hx ⟨h, hh⟩`. Use `(Submodule.ne_bot_iff _).2 ⟨v.1, fun h => ?_, fun h0 => hx0 ?_⟩` and prove the remaining obligations. Conclude with `congrArg Subtype.val (hv h)`.

Establish `hv0 : v = 0` using `Subtype.ext h0`. Establish `e' : f.toLinearMap v = f u` using `e`. Rewrite using `[← e', hv0, map_zero]`.
-/
theorem UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G V) (π : Representation ℂ G W) (H : Subgroup G), IsSmooth π → IsSubquotient σ π → IsCompact (H : Set G) →
    fixed σ H ≠ ⊥ → fixed π H ≠ ⊥ := by
  intro G _ _ _ V W _ _ _ _ σ π H hπ hsq hH hne
  obtain ⟨S, f, hf⟩ := hsq
  have hS : IsSmooth S.toRepresentation := fun v => by
    have : {g : G | S.toRepresentation g v = v} = {g : G | π g v = v} := by
      ext g; exact Subtype.ext_iff
    rw [this]; exact hπ v
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨u, rfl⟩ := hf x
  obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hS hH f.toLinearMap u fun h hh => by
    show f (S.toRepresentation h u) = f u
    rw [f.isIntertwining]
    simpa using hx ⟨h, hh⟩
  refine (Submodule.ne_bot_iff _).2 ⟨v.1, fun h => ?_, fun h0 => hx0 ?_⟩
  · exact congrArg Subtype.val (hv h)
  · have hv0 : v = 0 := Subtype.ext h0
    have e' : f.toLinearMap v = f u := e
    rw [← e', hv0, map_zero]
