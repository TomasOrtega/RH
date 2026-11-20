import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `E _ _ _ A n p _ S F hc w`. Establish `h1 : IsFac F w (fac F.tr hc w)`. Use `⟨fun g => ?_, fun y => ?_⟩` and prove the remaining obligations. Establish `e : F.tr.j (F.tr.sec (F.tr.j g)) = F.tr.j g` using `F.tr.j_sec _`. Use `(F.tr.j_eq _ _).1 e w.1 w.2.2` as an intermediate fact.

Rewrite using `[F.j_tr]`. Conclude with `this`. Rewrite using `[F.j_tr]`. Both sides reduce to the same expression. Use `⟨h1, fun L hL => ?_⟩` and prove the remaining obligations.

Establish `hpr : L.pr = (fac F.tr hc w).pr` using `MonoidHom.ext fun h => by`. Take `⟨g, rfl⟩` from `F.surj h`. Rewrite using `[hL.1 g, h1.1 g]`. Establish `hloc : L.loc = (fac F.tr hc w).loc` using `MonoidHom.ext fun y => by`. Rewrite using `[hL.2 y, h1.2 y]`.

Consider the cases of `hf : fac F.tr hc w with`. Consider the case `mk pr loc pr_loc comm`. Consider the cases of `L with`. Consider the case `mk pr' loc' pr_loc' comm'`. Rewrite `hpr`, `hloc` using `[hf]`.

Simplify using `only at hpr hloc`. Substitute `hpr hloc` using the available equality. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.W2.Seed.pFacEq :
    FacEq := by
  intro E _ _ _ A n p _ S F hc w
  have h1 : IsFac F w (fac F.tr hc w) := by
    refine ⟨fun g => ?_, fun y => ?_⟩
    · have e : F.tr.j (F.tr.sec (F.tr.j g)) = F.tr.j g := F.tr.j_sec _
      have := (F.tr.j_eq _ _).1 e w.1 w.2.2
      rw [F.j_tr]
      exact this
    · rw [F.j_tr]
      rfl
  refine ⟨h1, fun L hL => ?_⟩
  have hpr : L.pr = (fac F.tr hc w).pr := MonoidHom.ext fun h => by
    obtain ⟨g, rfl⟩ := F.surj h
    rw [hL.1 g, h1.1 g]
  have hloc : L.loc = (fac F.tr hc w).loc := MonoidHom.ext fun y => by
    rw [hL.2 y, h1.2 y]
  cases hf : fac F.tr hc w with
  | mk pr loc pr_loc comm =>
    cases L with
    | mk pr' loc' pr_loc' comm' =>
      rw [hf] at hpr hloc
      simp only at hpr hloc
      subst hpr hloc
      rfl
