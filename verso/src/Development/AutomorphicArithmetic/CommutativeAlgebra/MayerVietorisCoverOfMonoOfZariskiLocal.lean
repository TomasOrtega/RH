import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafMapMonoEpiIsoStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.Cover2Loc

private def sumP (A B : PSh) : PSh where
  obj T := A.obj T ⊕ B.obj T
  map h := TypeCat.ofHom (Sum.map (A.map h) (B.map h))
  map_id T := by
    ext x
    cases x <;> simp
  map_comp h k := by
    ext x
    cases x <;> simp

private def sumD {A B C : PSh} (a : A ⟶ C) (b : B ⟶ C) : sumP A B ⟶ C where
  app T := TypeCat.ofHom (Sum.elim (a.app T) (b.app T))
  naturality S T h := by
    ext x
    cases x with
    | inl x => exact FunctorToTypes.naturality a h x
    | inr x => exact FunctorToTypes.naturality b h x

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem map_comp_gen (R : Type) [CommRing R] {P C : PSh} (c : P ⟶ C) {M : Shv R}
    (p : (free R).obj C ⟶ M) (T : Scheme.{0}) (x : P.obj (op T)) :
    Sec.map ((free R).map c ≫ p) (freeGen R P T x) = Sec.map p (freeGen R C T (c.app (op T) x)) := by
  have h4 := (GlobalTheory.T.free_sections_ext_res_map R P M).2.2.2 C c T x
  show Sec.map p (Sec.map ((free R).map c) (freeGen R P T x)) = _
  rw [h4]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components.

Supply the required witnesses or components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Split into cases according to the possible forms of the given data. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem epi_desc (R : Type) [CommRing R] {A B C : PSh} (a : A ⟶ C) (b : B ⟶ C)
    (h : ∀ (T : Scheme.{0}) (y : C.obj (op T)), Loc T fun W k =>
      (∃ x, a.app (op W) x = C.map k.op y) ∨ (∃ x, b.app (op W) x = C.map k.op y)) :
    Epi (biprod.desc ((free R).map a) ((free R).map b)) := by
  haveI : Epi ((free R).map (sumD a b)) := by
    refine (GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R (sumD a b)).2.1 fun T y => ?_
    obtain ⟨S, hS, hP⟩ := h T y
    refine ⟨S, hS, fun W k hk => ?_⟩
    rcases hP W k hk with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr x, hx⟩
  constructor
  intro M p q hpq
  have h1 : (free R).map a ≫ p = (free R).map a ≫ q := by
    simpa using biprod.inl ≫= hpq
  have h2 : (free R).map b ≫ p = (free R).map b ≫ q := by
    simpa using biprod.inr ≫= hpq
  apply (cancel_epi ((free R).map (sumD a b))).1
  apply (GlobalTheory.T.free_sections_ext_res_map R (sumP A B) M).2.1
  intro T x
  rw [map_comp_gen, map_comp_gen]
  cases x with
  | inl x =>
    show Sec.map p (freeGen R C T (a.app (op T) x)) = Sec.map q (freeGen R C T (a.app (op T) x))
    rw [← map_comp_gen, ← map_comp_gen, h1]
  | inr x =>
    show Sec.map p (freeGen R C T (b.app (op T) x)) = Sec.map q (freeGen R C T (b.app (op T) x))
    rw [← map_comp_gen, ← map_comp_gen, h2]

end UpperTheory.Cover2Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Proceed by induction. Treat this case separately. Proceed by induction.

Treat this case separately.
-/
theorem UpperTheory.mayerVietorisCover_of_mono_of_zariskiLocal :
    ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Mono f → Mono g →
        (∀ (k : ℕ) (T : Scheme.{0}) (y : Sx E k T), Loc T fun W h => (∃ x : Sx U k W, x.map f = y.res h) ∨ (∃ x : Sx V k W, x.map g = y.res h)) →
        Cover2 R f g := by
  intro R _ U V E f g hf hg hl
  refine ⟨hf, hg, fun n => ?_⟩
  induction n using Opposite.rec with
  | op n =>
    induction n using SimplexCategory.rec with
    | mk k => exact UpperTheory.Cover2Loc.epi_desc R _ _ fun T y => hl k T y
