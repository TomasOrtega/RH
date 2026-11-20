import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafSectionLocallyFiniteCombinationStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

/- English proof (translation)
The claim follows from `(GlobalTheory.T.etaleSheafSections_ext_and_glue R F T).1 a 0 ⟨⊥, Scheme.bot_mem_grothendieckTopology T, fun _ _ h => h.elim⟩`.
-/
private theorem sec_empty {R : Type} [CommRing R] (F : Shv R) (T : Scheme.{0}) [IsEmpty T] (a : Sec F T) : a = 0 :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue R F T).1 a 0 ⟨⊥, Scheme.bot_mem_grothendieckTopology T, fun _ _ h => h.elim⟩

/- English proof (translation)
Take `⟨S, hS, h⟩` from `(GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R P U).1 y`. Use `(GlobalTheory.T.etaleSheafSections_ext_and_glue R _ U).1 y 0 ⟨S, hS, fun V g hg => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `h V g hg`. Establish `h0 : Sec.res g (0 : Sec ((free R).obj P) U) = 0` using `map_zero (((free R).obj P).obj.map g.op).hom`. Rewrite using `[h0]`.

Distinguish the cases in `hV : IsEmpty V`. Conclude with `sec_empty _ _ _`. Rewrite using `[hc]`. Establish `: IsEmpty (P.obj (op V))` using `⟨fun x => hV (hP V ⟨x⟩)⟩`. Establish `hc0 : c = 0` using `Subsingleton.elim _ _`.

Simplify using `[hc0]`.
-/
private theorem free_sec_zero (R : Type) [CommRing R] (P : PSh)
    (hP : ∀ T : Scheme.{0}, Nonempty (P.obj (op T)) → IsEmpty T) (U : Scheme.{0})
    (y : Sec ((free R).obj P) U) : y = 0 := by
  obtain ⟨S, hS, h⟩ := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R P U).1 y
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue R _ U).1 y 0 ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨c, hc⟩ := h V g hg
  have h0 : Sec.res g (0 : Sec ((free R).obj P) U) = 0 := map_zero (((free R).obj P).obj.map g.op).hom
  rw [h0]
  by_cases hV : IsEmpty V
  · exact sec_empty _ _ _
  · rw [hc]
    have : IsEmpty (P.obj (op V)) := ⟨fun x => hV (hP V ⟨x⟩)⟩
    have hc0 : c = 0 := Subsingleton.elim _ _
    simp [hc0]

/- English proof (translation)
Rewrite using `[IsZero.iff_id_eq_zero]`. Apply `Sheaf.hom_ext` to reduce the goal to its premises. Use extensionality with `U y`. Conclude with `free_sec_zero R P hP U.unop y`.
-/
private theorem free_isZero (R : Type) [CommRing R] (P : PSh)
    (hP : ∀ T : Scheme.{0}, Nonempty (P.obj (op T)) → IsEmpty T) : IsZero ((free R).obj P) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  ext U y
  exact free_sec_zero R P hP U.unop y

/- English proof (translation)
Establish `y : Sx (PGL 0) p T` using `Sx.map (pullback.snd (triv E 0) (PGL.pr 0)) x`. Establish `v : Um 0 Γ(T, ⊤)` using `(show ComposableArrows (Um 0 Γ(T, ⊤)) p from y).obj 0`. Establish `h : (⊥ : Ideal Γ(T, ⊤)) = ⊤`. Use `v.2` as an intermediate fact. Rewrite `this` using `[Set.range_eq_empty, Ideal.span_empty]`. Then use the resulting hypothesis.

Establish `hs : Subsingleton Γ(T, ⊤)`. Break down `subsingleton_or_nontrivial Γ(T, ⊤) with hs | hn` into its components or cases. Conclude with `hs`. Conclude with `absurd h bot_ne_top`. Use `⟨fun t => ?_⟩` and prove the remaining obligations.

Use `(T.presheaf.germ ⊤ t trivial).hom.codomain_trivial` as an intermediate fact. Conclude with `not_subsingleton (T.presheaf.stalk t) this`.
-/
private theorem sx_empty (E : Spc) (p : ℕ) (T : Scheme.{0})
    (x : Sx (pullback (triv E 0) (PGL.pr 0)) p T) : IsEmpty T := by
  have y : Sx (PGL 0) p T := Sx.map (pullback.snd (triv E 0) (PGL.pr 0)) x
  have v : Um 0 Γ(T, ⊤) := (show ComposableArrows (Um 0 Γ(T, ⊤)) p from y).obj 0
  have h : (⊥ : Ideal Γ(T, ⊤)) = ⊤ := by
    have := v.2
    rwa [Set.range_eq_empty, Ideal.span_empty] at this
  have hs : Subsingleton Γ(T, ⊤) := by
    rcases subsingleton_or_nontrivial Γ(T, ⊤) with hs | hn
    · exact hs
    · exact absurd h bot_ne_top
  refine ⟨fun t => ?_⟩
  have := (T.presheaf.germ ⊤ t trivial).hom.codomain_trivial
  exact not_subsingleton (T.presheaf.stalk t) this

/- English proof (translation)
Distinguish the cases in `hk : k ≤ 0`. Take `⟨p, rfl⟩ : ∃ p : ℕ, k = -(p : ℤ)` from `⟨(-k).toNat, by omega⟩`. Conclude with `(free_isZero R _ (hX p)).of_iso (chainsXIso R X p)`. Use `HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingDownNat k fun i => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `-(i : ℤ) ≠ k`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem chains_isZero (R : Type) [CommRing R] (X : Spc)
    (hX : ∀ (p : ℕ) (T : Scheme.{0}), Nonempty (Sx X p T) → IsEmpty T) (k : ℤ) :
    IsZero (((chains R).obj X).X k) := by
  by_cases hk : k ≤ 0
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, k = -(p : ℤ) := ⟨(-k).toNat, by omega⟩
    exact (free_isZero R _ (hX p)).of_iso (chainsXIso R X p)
  · refine HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingDownNat k fun i => ?_
    change -(i : ℤ) ≠ k
    omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a b => by obtain ⟨a, rfl⟩ := a.mk_surjective obtain ⟨b, rfl⟩ := b.mk_surjective congr 1 exact Cocycle.ext (Cochain.ext _ _ fun p q h => (chains_isZero R X hX p).eq_of_src _ _)⟩`.
-/
private theorem H_subsingleton (R : Type) [CommRing R] (X : Spc)
    (hX : ∀ (p : ℕ) (T : Scheme.{0}), Nonempty (Sx X p T) → IsEmpty T) (F : Shv R) (n : ℤ) :
    Subsingleton (H R X F n) := ⟨fun a b => by
  obtain ⟨a, rfl⟩ := a.mk_surjective
  obtain ⟨b, rfl⟩ := b.mk_surjective
  congr 1
  exact Cocycle.ext (Cochain.ext _ _ fun p q h => (chains_isZero R X hX p).eq_of_src _ _)⟩

/- English proof (translation)
Introduce `q _ E n i`. Use `haveI : Subsingleton (Ht q (pullback (triv E 0) (PGL.pr 0)) n i) := H_subsingleton _ _ (fun p T ⟨x⟩ => sx_empty E p T x) _ _`. Conclude with `⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨fun j => j.elim0, Subsingleton.elim _ _⟩⟩`.
-/
theorem UpperTheory.projectiveBundleFormula_rank_zero :
    ∀ (q : ℕ) [NeZero q] (E : Spc), PBF q E 0 := by
  intro q _ E n i
  haveI : Subsingleton (Ht q (pullback (triv E 0) (PGL.pr 0)) n i) :=
    H_subsingleton _ _ (fun p T ⟨x⟩ => sx_empty E p T x) _ _
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨fun j => j.elim0, Subsingleton.elim _ _⟩⟩
