import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.Seam

/- English proof (translation)
Use `haveI hK : ((chains R).obj E).IsStrictlyLE 0 := (inferInstance : CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)`. Use `haveI hL : (res R F).IsStrictlyGE 0 := by dsimp [res] infer_instance`. Establish `hz : ∀ z : Cochain ((chains R).obj E) (res R F) n, z = 0`. Introduce `z`. Apply `Cochain.ext` to reduce the goal to its premises.

Introduce `p q hpq`. Distinguish the cases in `hp : 0 < p`. Conclude with `(CochainComplex.isZero_of_isStrictlyLE ((chains R).obj E) 0 p hp).eq_of_src _ _`. Conclude with `(CochainComplex.isZero_of_isStrictlyGE (res R F) 0 q (by omega)).eq_of_tgt _ _`. Prove the components needed by the constructor for the conclusion.

Introduce `a b`. Take `⟨x, rfl⟩` from `CohomologyClass.mk_surjective a`. Take `⟨y, rfl⟩` from `CohomologyClass.mk_surjective b`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hz x.1, hz y.1]`.
-/
private theorem H_subsingleton_of_neg (R : Type) [CommRing R] (E : Spc) (F : Shv R) {n : ℤ} (hn : n < 0) :
    Subsingleton (H R E F n) := by
  haveI hK : ((chains R).obj E).IsStrictlyLE 0 :=
    (inferInstance : CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)
  haveI hL : (res R F).IsStrictlyGE 0 := by
    dsimp [res]
    infer_instance
  have hz : ∀ z : Cochain ((chains R).obj E) (res R F) n, z = 0 := by
    intro z
    apply Cochain.ext
    intro p q hpq
    by_cases hp : 0 < p
    · exact (CochainComplex.isZero_of_isStrictlyLE ((chains R).obj E) 0 p hp).eq_of_src _ _
    · exact (CochainComplex.isZero_of_isStrictlyGE (res R F) 0 q (by omega)).eq_of_tgt _ _
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective b
  congr 1
  apply Subtype.ext
  rw [hz x.1, hz y.1]

/- English proof (translation)
Introduce `l _ X n hn`. Use `haveI : ∀ k : ℕ, Subsingleton (HtL l k (sch.obj X) n 0) := fun k => H_subsingleton_of_neg (ZMod (l ^ k)) (sch.obj X) (tw (l ^ k) 0) hn`. Use `haveI : Subsingleton (Hl l (sch.obj X) n 0) := by dsimp only [Hl] infer_instance`. Simplify using `only [HQ]`. Use `infer_instance`.
-/
theorem UpperTheory.Gal.Seam.negVan :
    NegVan := by
  intro l _ X n hn
  haveI : ∀ k : ℕ, Subsingleton (HtL l k (sch.obj X) n 0) := fun k =>
    H_subsingleton_of_neg (ZMod (l ^ k)) (sch.obj X) (tw (l ^ k) 0) hn
  haveI : Subsingleton (Hl l (sch.obj X) n 0) := by
    dsimp only [Hl]
    infer_instance
  dsimp only [HQ]
  infer_instance
