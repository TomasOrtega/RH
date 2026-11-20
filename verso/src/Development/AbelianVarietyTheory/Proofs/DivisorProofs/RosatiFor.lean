import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToSiegAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {S : Scheme.{0}}

def RosatiFor (D : Datum p) {A : Over S} [GrpObj A] (act : OActN D.O A) (P : LB (G2 A).left) : Prop :=
  ∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
    (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left)

def EtaOK (D : Datum p) (N : ℕ) {A : Over S} [GrpObj A] (act : OActN D.O A) (eta : D.La → (𝟙_ (Over S) ⟶ A)) :
    Prop :=
  (∀ x y, eta (x + y) = eta x * eta y) ∧ (∀ (c : D.O) x, eta (c • x) = eta x ≫ act.act c) ∧ ∀ x, eta (N • x) = 1

def GeomAt (D : Datum p) (N : ℕ) {A : Over S} [GrpObj A] (act : OActN D.O A) (P : LB (G2 A).left)
    (eta : D.La → (𝟙_ (Over S) ⟶ A)) (k : Type) [Field k] (x : Sp k ⟶ S) : Prop :=
  ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c)
      (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)),
    ∀ y, toUnit _ ≫ eta y = I.ev N y

variable {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {s : S ⟶ Sp R}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Obj.rosatiFor (o : Obj b N s) : RosatiFor D o.act o.P := o.rosati

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem Obj.etaOK (o : Obj b N s) : EtaOK D N o.act o.eta := ⟨o.eta_add, o.eta_lin, o.eta_ker⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Obj.geomAt (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k)
    (hx : x ≫ s = spMap β) : GeomAt D N o.act o.P o.eta k x := o.geom k x β hx

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem Obj.lieHer (o : Obj b N s) (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S)
    (hx : x ≫ s = spMap β) : LieHer b o.act β x := by
  intro R'' _ g
  have e₁ : (spMap g ≫ x) ≫ s = spMap (g.comp β) := by
    rw [Category.assoc, hx]
    simp [spMap, ← Spec.map_comp]
    try rfl
  refine ⟨o.lie R'' (g.comp β) (spMap g ≫ x) e₁, fun k _ _ g' i => ?_⟩
  refine o.lieRank k (spMap g' ≫ spMap g ≫ x) (g'.comp (g.comp β)) ?_ i
  rw [Category.assoc, Category.assoc, hx]
  simp [spMap, ← Spec.map_comp]
  try rfl

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem RosatiFor.of_iso {A : Over S} [GrpObj A] {act : OActN D.O A} {P P' : LB (G2 A).left} (hP : P.IsLB)
    (hP' : P'.IsLB) (H : LBIso P P') (h : RosatiFor D act P) : RosatiFor D act P' := fun c =>
  LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB hP' _)
    (GlobalTheory.RigidBundleGlue.LBIso.pull H _).symm
    (LBIso.trans (pull_isLB hP _) (pull_isLB hP _) (pull_isLB hP' _) (h c) (GlobalTheory.RigidBundleGlue.LBIso.pull H _))

end GlobalTheory.UPel.HT
