import Development.EtaleCohomology.WeilConjectures.PurityCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.EWeil.EmptyVan₂

instance isEmpty_bot : IsEmpty (⊥_ Scheme.{0}) := by
  infer_instance

/- English proof (translation)
Establish `: IsEmpty U` using `⟨fun x => isEmptyElim (f.base x)⟩`. Conclude with `(ModuleCat.isZero_iff_subsingleton).1 (IsTerminal.isZero (Sheaf.isTerminalOfBotCover G U (Scheme.bot_mem_grothendieckTopology U)))`.
-/
theorem sec_subsingleton {R : Type} [CommRing R] (G : Shv R) {U : Scheme.{0}} (f : U ⟶ ⊥_ Scheme.{0}) :
    Subsingleton (G.obj.obj (op U)) := by
  have : IsEmpty U := ⟨fun x => isEmptyElim (f.base x)⟩
  exact (ModuleCat.isZero_iff_subsingleton).1
    (IsTerminal.isZero (Sheaf.isTerminalOfBotCover G U (Scheme.bot_mem_grothendieckTopology U)))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `f g`. Apply `((sheafificationAdjunction Scheme.etaleTopology.{0} _).homEquiv _ _).injective` to reduce the goal to its premises. Use extensionality with `U x`. Distinguish the cases in `h : Nonempty (U.unop ⟶ ⊥_ Scheme.{0})`.

Take `⟨φ⟩` from `h`. Conclude with `@Subsingleton.elim _ (sec_subsingleton G φ) _ _`. Establish `: IsEmpty (U.unop ⟶ ⊥_ Scheme.{0})` using `not_nonempty_iff.1 h`. Establish `hx : x = 0` using `Finsupp.ext fun a => isEmptyElim (a.down : U.unop ⟶ ⊥_ Scheme.{0})`. Substitute `hx` using the available equality.

Simplify using `only [map_zero]`.
-/
theorem free_hom_subsingleton {R : Type} [CommRing R] (G : Shv R) :
    Subsingleton ((free R).obj (yoneda.obj (⊥_ Scheme.{0})) ⟶ G) := by
  constructor
  intro f g
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} _).homEquiv _ _).injective
  ext U x
  by_cases h : Nonempty (U.unop ⟶ ⊥_ Scheme.{0})
  · obtain ⟨φ⟩ := h
    exact @Subsingleton.elim _ (sec_subsingleton G φ) _ _
  · have : IsEmpty (U.unop ⟶ ⊥_ Scheme.{0}) := not_nonempty_iff.1 h
    have hx : x = 0 := Finsupp.ext fun a => isEmptyElim (a.down : U.unop ⟶ ⊥_ Scheme.{0})
    subst hx
    simp only [map_zero]

/- English proof (translation)
Rewrite using `[IsZero.iff_id_eq_zero]`. Use `free_hom_subsingleton (R := R) ((free R).obj (yoneda.obj (⊥_ Scheme.{0})))` as an intermediate fact. Conclude with `Subsingleton.elim _ _`.
-/
theorem isZero_free {R : Type} [CommRing R] : IsZero ((free R).obj (yoneda.obj (⊥_ Scheme.{0}))) := by
  rw [IsZero.iff_id_eq_zero]
  have := free_hom_subsingleton (R := R) ((free R).obj (yoneda.obj (⊥_ Scheme.{0})))
  exact Subsingleton.elim _ _

end LateralTheory.EWeil.EmptyVan₂
