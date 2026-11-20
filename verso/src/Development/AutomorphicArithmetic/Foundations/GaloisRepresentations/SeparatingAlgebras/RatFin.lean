import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import GroundTheory.AutomorphicForms.AdelicGLn
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Gen.ratFin_pf :
    UpperTheory.Gal.Gen.RatFin := by
  intro E _ _ _ a
  refine ⟨?_, ?_⟩
  · intro Z hZ
    haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
    have hcl : IsClosed (((ratGL E a).range : Subgroup (GA E a)) : Set (GA E a)) := Subgroup.isClosed_of_discrete
    let K : Set (GA E a) := Subtype.val '' Z
    have hK : IsCompact K := hZ.image continuous_subtype_val
    have hKG : IsCompact (K ∩ ((ratGL E a).range : Set (GA E a))) := hK.inter_right hcl
    let t : Set (ratGL E a).range := {x | (x : GA E a) ∈ K}
    have himg : Subtype.val '' t = K ∩ ((ratGL E a).range : Set (GA E a)) := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
      · rintro ⟨hy, hy'⟩; exact ⟨⟨y, hy'⟩, hy, rfl⟩
    have ht : IsCompact t := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]; exact hKG
    have hfin : (K ∩ ((ratGL E a).range : Set (GA E a))).Finite := by
      rw [← himg]; exact (ht.finite_of_discrete).image _
    refine Set.Finite.of_finite_image (f := Subtype.val) (hfin.subset ?_) Subtype.val_injective.injOn
    rintro _ ⟨x, ⟨hxZ, hxr⟩, rfl⟩
    exact ⟨⟨x, hxZ, rfl⟩, (Subgroup.mem_subgroupOf).1 hxr⟩
  · intro w γ hγ h1
    obtain ⟨δ, hδ⟩ := (Subgroup.mem_subgroupOf).1 hγ
    have hδ1 : δ = 1 := by
      ext i j
      have h2 := congrArg (fun g : GL (Fin a) (w.adicCompletion E) => g.1 i j) h1
      have h3 : (cLoc w γ : GL (Fin a) (w.adicCompletion E)).1 i j = algebraMap E (w.adicCompletion E) (δ.1 i j) := by
        simp [cLoc, ← hδ, pLoc, pFin, ratGL]
        rfl
      have h4 : algebraMap E (w.adicCompletion E) (δ.1 i j) =
          algebraMap E (w.adicCompletion E) ((1 : GL (Fin a) E).1 i j) := by
        rw [← h3]
        refine h2.trans ?_
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      exact (algebraMap E (w.adicCompletion E)).injective h4
    apply Subtype.ext
    rw [← hδ, hδ1, map_one]; rfl
