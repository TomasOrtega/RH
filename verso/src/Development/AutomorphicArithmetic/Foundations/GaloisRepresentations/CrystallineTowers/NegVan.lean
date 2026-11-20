import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.Seam

/- English proof (translation)
Simplify by unfolding definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Simplify by unfolding definitions. Simplify by unfolding definitions. A detailed English derivation is pending.
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
