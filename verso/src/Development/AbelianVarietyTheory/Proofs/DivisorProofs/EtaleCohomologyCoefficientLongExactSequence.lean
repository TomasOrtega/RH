import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHypercohomologyIsoOfInjectiveResolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCompHomComplexAssocOnCohomologyClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMappingConeResolutionHomotopyEquivStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.CoefSeq

variable {R : Type} [CommRing R]

end GlobalTheory.EtC.CoefSeq

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
/- English proof (translation)
Introduce `y`. Rewrite using `[← hfg y, Function.comp_apply, ← h0]`. Conclude with `hβ.eq_iff`.
-/
private lemma exact_comp_injective {A B C C' : Type*} [Zero C] [Zero C'] {f : A → B} {g : B → C}
    {β : C → C'} (hfg : Function.Exact f g) (hβ : Function.Injective β) (h0 : β 0 = 0) :
    Function.Exact f (β ∘ g) := by
  intro y
  rw [← hfg y, Function.comp_apply, ← h0]
  exact hβ.eq_iff

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
/- English proof (translation)
Introduce `y`. Rewrite using `[Function.comp_apply, hfg (δ y)]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx⟩`. Conclude with `⟨x, by rw [Function.comp_apply, hx, hβδ]⟩`.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨x, by rw [Function.comp_apply, hδβ]⟩`.
-/
private lemma exact_conj_bijection_middle {A B B' C : Type*} [Zero C] {f : A → B} {g : B → C}
    (β : B → B') (δ : B' → B) (hδβ : ∀ b, δ (β b) = b) (hβδ : ∀ b', β (δ b') = b')
    (hfg : Function.Exact f g) : Function.Exact (β ∘ f) (g ∘ δ) := by
  intro y
  rw [Function.comp_apply, hfg (δ y)]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [Function.comp_apply, hx, hβδ]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [Function.comp_apply, hδβ]⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
/- English proof (translation)
Introduce `y`. Rewrite using `[hfg y, Set.range_comp, hγ.range_eq, Set.image_univ]`.
-/
private lemma exact_comp_surjective {A A' B C : Type*} [Zero C] {f : A → B} {g : B → C}
    {γ : A' → A} (hfg : Function.Exact f g) (hγ : Function.Surjective γ) :
    Function.Exact (f ∘ γ) g := by
  intro y
  rw [hfg y, Set.range_comp, hγ.range_eq, Set.image_univ]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in

/- English proof (translation)
Unfold `_root_.GlobalTheory.EtC.A7`. Introduce `R _ S hS`. Take `⟨e, ⟨hom⟩⟩` from `_root_.GlobalTheory.EtC.cone_resMap_homotopyEquiv R S hS`. Use `⟨_root_.GlobalTheory.EtC.zcomp (Cocycle.ofHom e.inv) (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) (zero_add 1), fun K n => ?_⟩` and prove the remaining obligations. Take `⟨ex₁, ex₂, ex₃⟩` from `_root_.GlobalTheory.EtC.coneSeqTgt_exact R K (_root_.GlobalTheory.EtC.resMap R S.f) n`.

Establish `hinvhom : ∀ x, _root_.GlobalTheory.EtC.cpush K e.inv n (_root_.GlobalTheory.EtC.cpush K e.hom n x) = x`. Introduce `x`. Rewrite using `[← _root_.GlobalTheory.EtC.InjResCmp.cpush_comp, _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K e.homotopyHomInvId, _root_.GlobalTheory.EtC.InjResCmp.cpush_id]`. Establish `hhominv : ∀ x, _root_.GlobalTheory.EtC.cpush K e.hom n (_root_.GlobalTheory.EtC.cpush K e.inv n x) = x`. Introduce `x`.

Rewrite using `[← _root_.GlobalTheory.EtC.InjResCmp.cpush_comp, _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K e.homotopyInvHomId, _root_.GlobalTheory.EtC.InjResCmp.cpush_id]`. Establish `hg : ⇑(_root_.GlobalTheory.EtC.HK.post R K S.g n) = ⇑(_root_.GlobalTheory.EtC.cpush K e.hom n) ∘ ⇑(_root_.GlobalTheory.EtC.cpush K (mappingCone.inr (_root_.GlobalTheory.EtC.resMap R S.f)) n)`. Use function extensionality and compare the values at `x`. Use `show _root_.GlobalTheory.EtC.cpush K (_root_.GlobalTheory.EtC.resMap R S.g) n x = _`. Rewrite using `[← _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K hom, _root_.GlobalTheory.EtC.InjResCmp.cpush_comp]`.

Both sides reduce to the same expression. Establish `hδ : ⇑(_root_.GlobalTheory.EtC.HK.ext R K (_root_.GlobalTheory.EtC.zcomp (Cocycle.ofHom e.inv) (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) (zero_add 1)) n (n + 1) rfl) = ⇑(_root_.GlobalTheory.EtC.cpost K (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) n (n + …`. Use function extensionality and compare the values at `y`. Conclude with `((_root_.GlobalTheory.cocycle_comp_assoc_classes R (add_zero n) (zero_add 1) rfl rfl).2.2 y (Cocycle.ofHom e.inv) (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)))`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hg]`. Conclude with `exact_comp_injective ex₁ (Function.LeftInverse.injective hinvhom) (map_zero _)`. Rewrite using `[hg, hδ]`. Conclude with `exact_conj_bijection_middle _ _ hinvhom hhominv ex₂`. Rewrite using `[hδ]`.

Conclude with `exact_comp_surjective ex₃ (Function.LeftInverse.surjective hinvhom)`.
-/
theorem _root_.GlobalTheory.EtC.coefSeq_exact : _root_.GlobalTheory.EtC.A7 := by
  unfold _root_.GlobalTheory.EtC.A7
  intro R _ S hS
  obtain ⟨e, ⟨hom⟩⟩ := _root_.GlobalTheory.EtC.cone_resMap_homotopyEquiv R S hS
  refine ⟨_root_.GlobalTheory.EtC.zcomp (Cocycle.ofHom e.inv)
    (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) (zero_add 1), fun K n => ?_⟩
  obtain ⟨ex₁, ex₂, ex₃⟩ :=
    _root_.GlobalTheory.EtC.coneSeqTgt_exact R K (_root_.GlobalTheory.EtC.resMap R S.f) n
  have hinvhom : ∀ x, _root_.GlobalTheory.EtC.cpush K e.inv n (_root_.GlobalTheory.EtC.cpush K e.hom n x) = x := by
    intro x
    rw [← _root_.GlobalTheory.EtC.InjResCmp.cpush_comp, _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K e.homotopyHomInvId,
      _root_.GlobalTheory.EtC.InjResCmp.cpush_id]
  have hhominv : ∀ x, _root_.GlobalTheory.EtC.cpush K e.hom n (_root_.GlobalTheory.EtC.cpush K e.inv n x) = x := by
    intro x
    rw [← _root_.GlobalTheory.EtC.InjResCmp.cpush_comp, _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K e.homotopyInvHomId,
      _root_.GlobalTheory.EtC.InjResCmp.cpush_id]
  have hg : ⇑(_root_.GlobalTheory.EtC.HK.post R K S.g n) =
      ⇑(_root_.GlobalTheory.EtC.cpush K e.hom n) ∘
        ⇑(_root_.GlobalTheory.EtC.cpush K (mappingCone.inr (_root_.GlobalTheory.EtC.resMap R S.f)) n) := by
    funext x
    show _root_.GlobalTheory.EtC.cpush K (_root_.GlobalTheory.EtC.resMap R S.g) n x = _
    rw [← _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K hom, _root_.GlobalTheory.EtC.InjResCmp.cpush_comp]
    rfl
  have hδ : ⇑(_root_.GlobalTheory.EtC.HK.ext R K
      (_root_.GlobalTheory.EtC.zcomp (Cocycle.ofHom e.inv)
        (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) (zero_add 1)) n (n + 1) rfl) =
      ⇑(_root_.GlobalTheory.EtC.cpost K (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) n (n + 1) rfl) ∘
        ⇑(_root_.GlobalTheory.EtC.cpush K e.inv n) := by
    funext y
    exact ((_root_.GlobalTheory.cocycle_comp_assoc_classes R (add_zero n) (zero_add 1) rfl rfl).2.2
      y (Cocycle.ofHom e.inv) (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)))
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    exact exact_comp_injective ex₁ (Function.LeftInverse.injective hinvhom) (map_zero _)
  · rw [hg, hδ]
    exact exact_conj_bijection_middle _ _ hinvhom hhominv ex₂
  · rw [hδ]
    exact exact_comp_surjective ex₃ (Function.LeftInverse.surjective hinvhom)
