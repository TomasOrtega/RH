import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

/- English proof (translation)
Introduce `Z X f _ _ T hT hE`. Set `U : X.Opens` to `⟨(Set.range f.base)ᶜ, f.isClosedMap.isClosed_range.isOpen_compl⟩`. Establish `hU : IsEmpty (pullback f U.ι : Scheme.{0})`. Use `⟨fun p => ?_⟩` and prove the remaining obligations. Establish `h1 : (pullback.snd f U.ι ≫ U.ι).base p = (pullback.fst f U.ι ≫ f).base p`.

Rewrite using `[pullback.condition]`. Establish `h2 : (pullback.snd f U.ι ≫ U.ι).base p ∈ U`. Rewrite using `[Scheme.Hom.comp_base, TopCat.comp_app]`. Establish `hr` using `U.range_ι`. Conclude with `(Set.ext_iff.1 hr _).1 ⟨_, rfl⟩`.

Rewrite `h2` using `[h1, Scheme.Hom.comp_base, TopCat.comp_app]`. Conclude with `h2 ⟨_, rfl⟩`. Establish `hTU : T U.ι` using `hE U.ι hU`. Set `V : Bool → Scheme.{0}` to `fun b => Bool.rec U.toScheme Z b`. Set `j : ∀ b, V b ⟶ X` to `fun b => match b with`.

Consider the case `true => f`. Consider the case `false => U.ι`. Establish `hmem : Presieve.ofArrows V j ∈ Scheme.etalePrecoverage X`. Use `(Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun b => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ Set.range f.base`.

Take `⟨z, rfl⟩` from `hx`. Conclude with `⟨true, z, rfl⟩`. Conclude with `⟨false, ⟨x, hx⟩, rfl⟩`. Consider the cases of `b`. Express the relevant statement in the definitionally equal form `Etale U.ι infer_instance`.

Express the relevant statement in the definitionally equal form `Etale f infer_instance`. Use `Scheme.etaleTopology.transitive (Precoverage.generate_mem_toGrothendieck hmem) _ ?_` and prove the remaining obligations. Introduce and unpack `W g ⟨Y, h, k, ⟨b⟩, rfl⟩`. Rewrite using `[Sieve.pullback_comp]`. Use `Scheme.etaleTopology.pullback_stable h ?_` and prove the remaining obligations.

Consider the cases of `b`. Express the relevant statement in the definitionally equal form `T.pullback U.ι ∈ _`. Rewrite using `[Sieve.pullback_eq_top_of_mem _ hTU]`. Conclude with `Scheme.etaleTopology.top_mem _`. Conclude with `hT`.
-/
theorem mem_etaleTopology_of_pullback_finite : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (T : Sieve X), T.pullback f ∈ Scheme.etaleTopology Z → (∀ {V : Scheme.{0}} (v : V ⟶ X), IsEmpty (pullback f v : Scheme.{0}) → T v) → T ∈ Scheme.etaleTopology X := by
  intro Z X f _ _ T hT hE
  let U : X.Opens := ⟨(Set.range f.base)ᶜ, f.isClosedMap.isClosed_range.isOpen_compl⟩
  have hU : IsEmpty (pullback f U.ι : Scheme.{0}) := by
    refine ⟨fun p => ?_⟩
    have h1 : (pullback.snd f U.ι ≫ U.ι).base p = (pullback.fst f U.ι ≫ f).base p := by
      rw [pullback.condition]
    have h2 : (pullback.snd f U.ι ≫ U.ι).base p ∈ U := by
      rw [Scheme.Hom.comp_base, TopCat.comp_app]
      have hr := U.range_ι
      exact (Set.ext_iff.1 hr _).1 ⟨_, rfl⟩
    rw [h1, Scheme.Hom.comp_base, TopCat.comp_app] at h2
    exact h2 ⟨_, rfl⟩
  have hTU : T U.ι := hE U.ι hU
  let V : Bool → Scheme.{0} := fun b => Bool.rec U.toScheme Z b
  let j : ∀ b, V b ⟶ X := fun b => match b with
    | true => f
    | false => U.ι
  have hmem : Presieve.ofArrows V j ∈ Scheme.etalePrecoverage X := by
    refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun b => ?_⟩
    · by_cases hx : x ∈ Set.range f.base
      · obtain ⟨z, rfl⟩ := hx
        exact ⟨true, z, rfl⟩
      · exact ⟨false, ⟨x, hx⟩, rfl⟩
    · cases b
      · change Etale U.ι
        infer_instance
      · change Etale f
        infer_instance
  refine Scheme.etaleTopology.transitive (Precoverage.generate_mem_toGrothendieck hmem) _ ?_
  rintro W g ⟨Y, h, k, ⟨b⟩, rfl⟩
  rw [Sieve.pullback_comp]
  refine Scheme.etaleTopology.pullback_stable h ?_
  cases b
  · change T.pullback U.ι ∈ _
    rw [Sieve.pullback_eq_top_of_mem _ hTU]
    exact Scheme.etaleTopology.top_mem _
  · exact hT

/- English proof (translation)
The claim follows from `mem_etaleTopology_of_pullback_finite`.
-/
example : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (T : Sieve X), T.pullback f ∈ Scheme.etaleTopology Z → (∀ {V : Scheme.{0}} (v : V ⟶ X), IsEmpty (pullback f v : Scheme.{0}) → T v) → T ∈ Scheme.etaleTopology X :=
  mem_etaleTopology_of_pullback_finite

end GlobalTheory.EtC.Tr
