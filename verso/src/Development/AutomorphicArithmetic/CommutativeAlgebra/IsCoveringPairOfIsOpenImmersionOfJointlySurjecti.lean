import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCechNerveAugmentationIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace UpperTheory.CoverSieveFree

private def coverSieve {Y A B T : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y) (x : T ⟶ Y) : Sieve T where
  arrows V g := (∃ u : V ⟶ A, u ≫ a = g ≫ x) ∨ ∃ v : V ⟶ B, v ≫ b = g ≫ x
  downward_closed := by
    rintro V W g (⟨u, hu⟩ | ⟨v, hv⟩) h
    · exact Or.inl ⟨h ≫ u, by simp [hu]⟩
    · exact Or.inr ⟨h ≫ v, by simp [hv]⟩

/- English proof (translation)
Set `Xs : Bool → Scheme.{0}` to `fun i => Bool.casesOn i B A`. Set `fs : ∀ i, Xs i ⟶ Y` to `fun i => Bool.casesOn (motive := fun i => Xs i ⟶ Y) i b a`. Establish `hmem : Presieve.ofArrows Xs fs ∈ Scheme.precoverage @Etale Y`. Use `(Scheme.ofArrows_mem_precoverage_iff @Etale).2 ⟨fun y => ?_, fun i => ?_⟩` and prove the remaining obligations. Break down `hc y with h | h` into its components or cases.

Conclude with `⟨true, h⟩`. Conclude with `⟨false, h⟩`. Apply the tactic sequence `cases i <;> dsimp [fs] <;> infer_instance`. Establish `hS` using `Precoverage.generate_mem_toGrothendieck hmem`. Use `Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.pullback_stable x hS)` and prove the remaining obligations.

Introduce and unpack `V g ⟨W, h, k, hk, e⟩`. Break down `hk with ⟨i⟩` into its components or cases. Consider the cases of `i`. Conclude with `Or.inr ⟨h, e⟩`. Conclude with `Or.inl ⟨h, e⟩`.
-/
private theorem coverSieve_mem {Y A B T : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y) [IsOpenImmersion a]
    [IsOpenImmersion b] (hc : ∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b) (x : T ⟶ Y) :
    coverSieve a b x ∈ Scheme.etaleTopology.{0} T := by
  let Xs : Bool → Scheme.{0} := fun i => Bool.casesOn i B A
  let fs : ∀ i, Xs i ⟶ Y := fun i => Bool.casesOn (motive := fun i => Xs i ⟶ Y) i b a
  have hmem : Presieve.ofArrows Xs fs ∈ Scheme.precoverage @Etale Y := by
    refine (Scheme.ofArrows_mem_precoverage_iff @Etale).2 ⟨fun y => ?_, fun i => ?_⟩
    · rcases hc y with h | h
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
    · cases i <;> dsimp [fs] <;> infer_instance
  have hS := Precoverage.generate_mem_toGrothendieck hmem
  refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.pullback_stable x hS)
  rintro V g ⟨W, h, k, hk, e⟩
  rcases hk with ⟨i⟩
  cases i
  · exact Or.inr ⟨h, e⟩
  · exact Or.inl ⟨h, e⟩

/- English proof (translation)
Apply `free_ext` to reduce the goal to its premises. Introduce `U x`. Use `G.isSeparated _ (coverSieve a b x) (coverSieve_mem a b hc x) _ _ ?_` and prove the remaining obligations. Introduce `V g hg`. Express the relevant statement in the definitionally equal form `Sec.res g (Sec.map φ _) = Sec.res g (Sec.map ψ _)`.

Rewrite using `[map_res, map_res, freeGen_res]`. Break down `hg with ⟨u, hu⟩ | ⟨v, hv⟩` into its components or cases. Establish `e : (ConcreteCategory.hom ((yoneda.obj Y).map g.op)) x = (ConcreteCategory.hom ((yoneda.map a).app (op V))) u` using `hu.symm`. Rewrite using `[e, ← freeGen_map]`. Express the relevant statement in the definitionally equal form `Sec.map ((free R).map (yoneda.map a) ≫ φ) _ = Sec.map ((free R).map (yoneda.map a) ≫ ψ) _`.

Rewrite using `[ha]`. Establish `e : (ConcreteCategory.hom ((yoneda.obj Y).map g.op)) x = (ConcreteCategory.hom ((yoneda.map b).app (op V))) v` using `hv.symm`. Rewrite using `[e, ← freeGen_map]`. Express the relevant statement in the definitionally equal form `Sec.map ((free R).map (yoneda.map b) ≫ φ) _ = Sec.map ((free R).map (yoneda.map b) ≫ ψ) _`. Rewrite using `[hb]`.
-/
private theorem free_hom_ext (R : Type) [CommRing R] {Y A B : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion b] (hc : ∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b)
    {G : Shv R} (φ ψ : (free R).obj (yoneda.obj Y) ⟶ G)
    (ha : (free R).map (yoneda.map a) ≫ φ = (free R).map (yoneda.map a) ≫ ψ)
    (hb : (free R).map (yoneda.map b) ≫ φ = (free R).map (yoneda.map b) ≫ ψ) : φ = ψ := by
  apply free_ext
  intro U x
  refine G.isSeparated _ (coverSieve a b x) (coverSieve_mem a b hc x) _ _ ?_
  intro V g hg
  change Sec.res g (Sec.map φ _) = Sec.res g (Sec.map ψ _)
  rw [map_res, map_res, freeGen_res]
  rcases hg with ⟨u, hu⟩ | ⟨v, hv⟩
  · have e : (ConcreteCategory.hom ((yoneda.obj Y).map g.op)) x =
        (ConcreteCategory.hom ((yoneda.map a).app (op V))) u := hu.symm
    rw [e, ← freeGen_map]
    change Sec.map ((free R).map (yoneda.map a) ≫ φ) _ = Sec.map ((free R).map (yoneda.map a) ≫ ψ) _
    rw [ha]
  · have e : (ConcreteCategory.hom ((yoneda.obj Y).map g.op)) x =
        (ConcreteCategory.hom ((yoneda.map b).app (op V))) v := hv.symm
    rw [e, ← freeGen_map]
    change Sec.map ((free R).map (yoneda.map b) ≫ φ) _ = Sec.map ((free R).map (yoneda.map b) ≫ ψ) _
    rw [hb]

end UpperTheory.CoverSieveFree

open UpperTheory.CoverSieveFree in
/- English proof (translation)
Introduce `R _ Y A B a b ha hb hc`. Establish `hy : ∀ {Z : Scheme.{0}} (f : Z ⟶ Y) [Mono f], Mono (sch.map f)`. Introduce `Z f _`. Establish `h1 : ∀ X, Mono ((yoneda.map f).app X)` using `fun X => (mono_iff_injective _).2 (fun g h e => (cancel_mono f).1 (by simpa using e))`. Establish `h2 : Mono (yoneda.map f)` using `NatTrans.mono_of_mono_app _`.

Establish `h3 : ∀ n, Mono ((sch.map f).app n)` using `fun n => h2`. Conclude with `NatTrans.mono_of_mono_app _`. Use `⟨hy a, hy b, fun n => ⟨fun {G} φ ψ h => ?_⟩⟩` and prove the remaining obligations. Apply `free_hom_ext R a b hc φ ψ` to reduce the goal to its premises. Establish `e` using `congrArg (fun k => biprod.inl ≫ k) h`.

Simplify using `only [biprod.inl_desc_assoc] at e`. Conclude with `e`. Establish `e` using `congrArg (fun k => biprod.inr ≫ k) h`. Simplify using `only [biprod.inr_desc_assoc] at e`. Conclude with `e`.
-/
theorem UpperTheory.isCovering_pair_of_isOpenImmersion_of_jointly_surjective :
    ∀ (R : Type) [CommRing R] {Y A B : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y), IsOpenImmersion a → IsOpenImmersion b →
       (∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b) → Cover2 R (sch.map a) (sch.map b) := by
  intro R _ Y A B a b ha hb hc
  have hy : ∀ {Z : Scheme.{0}} (f : Z ⟶ Y) [Mono f], Mono (sch.map f) := by
    intro Z f _
    have h1 : ∀ X, Mono ((yoneda.map f).app X) := fun X =>
      (mono_iff_injective _).2 (fun g h e => (cancel_mono f).1 (by simpa using e))
    have h2 : Mono (yoneda.map f) := NatTrans.mono_of_mono_app _
    have h3 : ∀ n, Mono ((sch.map f).app n) := fun n => h2
    exact NatTrans.mono_of_mono_app _
  refine ⟨hy a, hy b, fun n => ⟨fun {G} φ ψ h => ?_⟩⟩
  apply free_hom_ext R a b hc φ ψ
  · have e := congrArg (fun k => biprod.inl ≫ k) h
    simp only [biprod.inl_desc_assoc] at e
    exact e
  · have e := congrArg (fun k => biprod.inr ≫ k) h
    simp only [biprod.inr_desc_assoc] at e
    exact e
