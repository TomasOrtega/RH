import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import GroundTheory.AutomorphicForms.AdelicGLn
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `E _ _ _ a`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `Z hZ haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a`. Establish `hcl : IsClosed (((ratGL E a).range : Subgroup (GA E a)) : Set (GA E a))` using `Subgroup.isClosed_of_discrete`. Set `K : Set (GA E a)` to `Subtype.val '' Z`.

Establish `hK : IsCompact K` using `hZ.image continuous_subtype_val`. Establish `hKG : IsCompact (K ∩ ((ratGL E a).range : Set (GA E a)))` using `hK.inter_right hcl`. Set `t : Set (ratGL E a).range` to `{x | (x : GA E a) ∈ K}`. Establish `himg : Subtype.val '' t = K ∩ ((ratGL E a).range : Set (GA E a))`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨hx, x.2⟩`. Introduce and unpack `⟨hy, hy'⟩`. Conclude with `⟨⟨y, hy'⟩, hy, rfl⟩`.

Establish `ht : IsCompact t`. Rewrite using `[Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]`. Conclude with `hKG`. Establish `hfin : (K ∩ ((ratGL E a).range : Set (GA E a))).Finite`. Rewrite using `[← himg]`.

Conclude with `(ht.finite_of_discrete).image _`. Use `Set.Finite.of_finite_image (f := Subtype.val) (hfin.subset ?_) Subtype.val_injective.injOn` and prove the remaining obligations. Introduce and unpack `_ ⟨x, ⟨hxZ, hxr⟩, rfl⟩`. Conclude with `⟨⟨x, hxZ, rfl⟩, (Subgroup.mem_subgroupOf).1 hxr⟩`. Introduce `w γ hγ h1`.

Take `⟨δ, hδ⟩` from `(Subgroup.mem_subgroupOf).1 hγ`. Establish `hδ1 : δ = 1`. Use extensionality with `i j`. Establish `h2` using `congrArg (fun g : GL (Fin a) (w.adicCompletion E) => g.1 i j) h1`. Establish `h3 : (cLoc w γ : GL (Fin a) (w.adicCompletion E)).1 i j = algebraMap E (w.adicCompletion E) (δ.1 i j)`.

Simplify using `[cLoc, ← hδ, pLoc, pFin, ratGL]`. Both sides reduce to the same expression. Establish `h4 : algebraMap E (w.adicCompletion E) (δ.1 i j) = algebraMap E (w.adicCompletion E) ((1 : GL (Fin a) E).1 i j)`. Rewrite using `[← h3]`. Use `h2.trans ?_` and prove the remaining obligations.

Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Conclude with `(algebraMap E (w.adicCompletion E)).injective h4`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hδ, hδ1, map_one]`. Both sides reduce to the same expression.
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
