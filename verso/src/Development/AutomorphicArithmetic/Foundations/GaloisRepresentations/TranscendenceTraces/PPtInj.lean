import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Establish `h0 : ((q : ℕ) : ULift.{1} (ZMod q)) = 0`. Apply `ULift.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) q t, h0, zero_smul]`.
-/
private theorem q_smul_sec (q : ℕ) (i : ℤ) {V : Scheme.{0}} (t : Sec (tw q i) V) : q • t = 0 := by
  have h0 : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) q t, h0, zero_smul]

/- English proof (translation)
The claim follows from `map_sub (F.obj.map g.op).hom a b`.
-/
private theorem res_sub' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub (F.obj.map g.op).hom a b

/- English proof (translation)
The claim follows from `map_zero (F.obj.map g.op).hom`.
-/
private theorem res_zero' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero (F.obj.map g.op).hom

/- English proof (translation)
The claim follows from `map_nsmul (F.obj.map g.op).hom c a`.
-/
private theorem res_nsmul' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (a : Sec F U) :
    Sec.res g (c • a) = c • Sec.res g a := map_nsmul (F.obj.map g.op).hom c a

/- English proof (translation)
The claim follows from `(GlobalTheory.T.etaleSheafSections_ext_and_glue R F V).1 a b ((GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.2.2 V _)`.
-/
private theorem sec_empty {R : Type} [CommRing R] (F : Shv R) {V : Scheme.{0}} [IsEmpty V] (a b : Sec F V) : a = b :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue R F V).1 a b ((GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.2.2 V _)

/- English proof (translation)
Introduce `hEx q _ i U b b' h`. Establish `hy : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ U), Sec.res x (b - b') = 0`. Introduce `Ω _ _ x`. Rewrite using `[res_sub', h Ω x, sub_self]`. Use `(GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (tw q i) U).1 b b' ?_` and prove the remaining obligations.

Use `(GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ ((GlobalTheory.T.tateTwist_sections_locally_generated q i).1 U (b - b')) ?_` and prove the remaining obligations. Introduce `V g hg`. Establish `key : Sec.res g (b - b') = 0`. Break down `hg with hg | ⟨ζ, c, hc⟩` into its components or cases. Conclude with `hg`.

Break down `isEmpty_or_nonempty V with hV | ⟨⟨v⟩⟩` into its components or cases. Conclude with `sec_empty _ _ _`. Take `⟨Ω, _, _, x, -⟩` from `hEx V v`. Establish `h1 : c • twGen i (ζ.map x.appTop.hom) = 0`. Establish `h2` using `hy Ω (x ≫ g)`.

Rewrite `h2` using `[← res_res, hc, res_nsmul', (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1]`. Conclude with `h2`. Use `haveI : Nonempty (gp Ω) := ⟨IsLocalRing.closedPoint Ω⟩`. Take `⟨d, rfl⟩` from `(GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 (gp Ω) _ c h1`. Rewrite using `[hc, mul_nsmul', q_smul_sec]`.

Rewrite `key` using `[res_sub']`. Conclude with `sub_eq_zero.1 key`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.ptInj_of :
    PtEx → PtInj := by
  intro hEx q _ i U b b' h
  have hy : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ U), Sec.res x (b - b') = 0 := by
    intro Ω _ _ x
    rw [res_sub', h Ω x, sub_self]
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (tw q i) U).1 b b' ?_
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ ((GlobalTheory.T.tateTwist_sections_locally_generated q i).1 U (b - b')) ?_
  intro V g hg
  have key : Sec.res g (b - b') = 0 := by
    rcases hg with hg | ⟨ζ, c, hc⟩
    · exact hg
    · rcases isEmpty_or_nonempty V with hV | ⟨⟨v⟩⟩
      · exact sec_empty _ _ _
      · obtain ⟨Ω, _, _, x, -⟩ := hEx V v
        have h1 : c • twGen i (ζ.map x.appTop.hom) = 0 := by
          have h2 := hy Ω (x ≫ g)
          rw [← res_res, hc, res_nsmul', (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1] at h2
          exact h2
        haveI : Nonempty (gp Ω) := ⟨IsLocalRing.closedPoint Ω⟩
        obtain ⟨d, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 (gp Ω) _ c h1
        rw [hc, mul_nsmul', q_smul_sec]
  rw [res_sub'] at key
  exact sub_eq_zero.1 key
