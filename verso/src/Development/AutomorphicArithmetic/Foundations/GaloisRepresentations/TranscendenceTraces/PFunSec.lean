import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSepGlueOfSurjectiveFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem res_zsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℤ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := by
  simp

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem sec_eq_of_isEmpty {R : Type} [CommRing R] {F : Shv R} (W : Scheme.{0}) [IsEmpty W] (a b : Sec F W) : a = b :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue R F W).1 a b (GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.2 W _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.TranscendenceTraces.funSec_of :
    FunSec := by
  intro q _ i U ζ φ hφ
  let V : ℤ → U.Opens := fun n => ⟨{x | φ x = n}, hφ.isOpen_fiber n⟩
  have hmem : ∀ (n : ℤ) (v : (V n : Scheme)), φ ((V n).ι v) = n := by
    intro n v
    have h1 : (V n).ι v ∈ Set.range (V n).ι := ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι] at h1
    exact h1
  have hcov : ∀ u : U, ∃ n, ∃ v, (V n).ι v = u := by
    intro u
    refine ⟨φ u, ?_⟩
    have h1 : u ∈ Set.range (V (φ u)).ι := by
      rw [Scheme.Opens.range_ι]
      exact rfl
    exact h1
  obtain ⟨y, hy⟩ := (GlobalTheory.T.etaleSheafSections_sep_glue_of_surjective_family (ZMod q) (tw q i) U ℤ (fun n => (V n : Scheme)) (fun n => (V n).ι)
    (fun n => inferInstance) hcov).2 (fun n => n • Sec.res (V n).ι (twGen i ζ)) (by
      intro n m
      by_cases h : n = m
      · subst h
        rw [res_zsmul, res_zsmul, res_res, res_res, pullback.condition]
      · haveI : IsEmpty ↥(pullback (V n).ι (V m).ι) := by
          refine ⟨fun p => h ?_⟩
          have e1 := hmem n (pullback.fst (V n).ι (V m).ι p)
          have e2 := hmem m (pullback.snd (V n).ι (V m).ι p)
          have hc : (V n).ι (pullback.fst (V n).ι (V m).ι p) =
              (V m).ι (pullback.snd (V n).ι (V m).ι p) :=
            congrArg (fun f : pullback (V n).ι (V m).ι ⟶ U => f p) pullback.condition
          rw [hc] at e1
          exact e1.symm.trans e2
        exact sec_eq_of_isEmpty _ _ _)
  refine ⟨y, ?_⟩
  intro Ω _ _ x
  have hr : Set.range x ⊆ Set.range (V (φ (pt x))).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    show φ (x s) = φ (pt x)
    rw [pt_eq]
  obtain ⟨k, hk⟩ : ∃ k, k ≫ (V (φ (pt x))).ι = x := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  calc Sec.res x y = Sec.res (k ≫ (V (φ (pt x))).ι) y := by rw [hk]
    _ = Sec.res k ((φ (pt x)) • Sec.res (V (φ (pt x))).ι (twGen i ζ)) := by
        rw [← res_res, hy]
    _ = φ (pt x) • Sec.res x (twGen i ζ) := by rw [res_zsmul, res_res, hk]
