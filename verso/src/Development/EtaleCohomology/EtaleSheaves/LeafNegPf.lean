import Development.EtaleCohomology.EtaleSheaves.LeafDegCut

noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNegPf

/- English proof (translation)
Express the relevant statement in the definitionally equal form `IsZero ((((chainsN R).obj E).extend ComplexShape.embeddingDownNat).X n)`. Apply `HomologicalComplex.isZero_extend_X` to reduce the goal to its premises. Introduce `i`. Express the relevant statement in the definitionally equal form `-(i : ℤ) ≠ n`. Use linear arithmetic over natural numbers and integers.
-/
theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) :
    IsZero (((chains R).obj E).X n) := by
  change IsZero ((((chainsN R).obj E).extend ComplexShape.embeddingDownNat).X n)
  apply HomologicalComplex.isZero_extend_X
  intro i
  change -(i : ℤ) ≠ n
  omega

/- English proof (translation)
Unfold `res`. Conclude with `CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)`.
-/
theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) :
    IsZero ((res R F).X n) := by
  unfold res
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)

/- English proof (translation)
Rewrite using `[IsZero.iff_id_eq_zero]`. Apply `mappingCone.ext_from _ (p + 1) p rfl` to reduce the goal to its premises. Conclude with `(chains_isZero R U (p + 1) (by omega)).eq_of_src _ _`. Conclude with `(chains_isZero R E p hp).eq_of_src _ _`.
-/
theorem cone_isZero (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (p : ℤ) (hp : 0 < p) :
    IsZero ((mappingCone ((chains R).map f)).X p) := by
  rw [IsZero.iff_id_eq_zero]
  apply mappingCone.ext_from _ (p + 1) p rfl
  · exact (chains_isZero R U (p + 1) (by omega)).eq_of_src _ _
  · exact (chains_isZero R E p hp).eq_of_src _ _

/- English proof (translation)
Use `Cochain.ext _ _ (fun p q hpq => ?_)` and prove the remaining obligations. Rewrite using `[Cochain.zero_v]`. Distinguish the cases in `hq : q < 0`. Conclude with `(res_isZero R F q hq).eq_of_tgt _ _`. Conclude with `(cone_isZero R f p (by omega)).eq_of_src _ _`.
-/
theorem cochain_eq_zero (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (m : ℤ) (hm : m < 0)
    (z : Cochain (mappingCone ((chains R).map f)) (res R F) m) : z = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hq : q < 0
  · exact (res_isZero R F q hq).eq_of_tgt _ _
  · exact (cone_isZero R f p (by omega)).eq_of_src _ _

/- English proof (translation)
Introduce `R _ U E f F m hm`. Prove the components needed by the constructor for the conclusion. Introduce `a b`. Take `⟨x, rfl⟩` from `CohomologyClass.mk_surjective a`. Take `⟨y, rfl⟩` from `CohomologyClass.mk_surjective b`.

Establish `hx : x = y` using `by ext1`. Rewrite using `[cochain_eq_zero R f F m hm (x : Cochain _ _ m), cochain_eq_zero R f F m hm (y : Cochain _ _ m)]`. Rewrite using `[hx]`.
-/
theorem LeafNeg_of : LateralTheory.E.LeafDegCut.LeafNeg := by
  intro R _ U E f F m hm
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective b
  have hx : x = y := by
    ext1
    rw [cochain_eq_zero R f F m hm (x : Cochain _ _ m), cochain_eq_zero R f F m hm (y : Cochain _ _ m)]
  rw [hx]

end LateralTheory.E.LeafNegPf
