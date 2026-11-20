import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearChangeEulerProduct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

open GlobalTheory.AbDual GlobalTheory.CechPic

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pullPol_dual_hom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ' : B ⟶ o.A), IsAbelianScheme B → IsMonHom ψ' → ∃ (C : Over Y) (_ : GrpObj C) (Q : LB (B ⊗ C).left) (h : B ⟶ C), IsAbelianScheme C ∧ GlobalTheory.AbDual.IsDual B C Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ IsMonHom h ∧ LBIso (o.P.pull (ψ' ⊗ₘ ψ').left) (Q.pull (lift (fst B B) (snd B B ≫ h)).left) ∧ ∀ (T : Over Y) (x : T ⟶ B), PullPolTriv o ψ' x ↔ x ≫ h = 1 := by
  intro p _ D R _ b N Y s o B _ _ ψ' hB hψ
  obtain ⟨C, _, Q, h, hC, hQ, hQ', hh, e⟩ :=
    GlobalTheory.DualHomPull.exists_dual_hom Y B o.A ψ' o.P hB o.ab hψ o.isLB o.rig₁ o.rig₂
  refine ⟨C, inferInstance, Q, h, hC, hQ, hQ', hh, e, fun T x ↦ ?_⟩
  have eχ : ψ' ⊗ₘ ψ' = lift (fst B B ≫ ψ') (snd B B ≫ ψ') := by ext <;> simp
  rw [eχ] at e
  have hE : (ev o.P (fst B B ≫ ψ') (snd B B ≫ ψ')).IsLB := pull_isLB o.isLB _
  have hF : (ev Q (fst B B) (snd B B ≫ h)).IsLB := pull_isLB hQ.isLB _
  have c := congrArg (CechPic.pull (lift (fst B T) (snd B T ≫ x)).left) ((cls_eq_iff hE hF).2 e)
  rw [cls_ev o.isLB, cls_ev hQ.isLB, pull_evc, pull_evc, lift_fst_assoc, lift_snd_assoc, lift_fst,
    lift_snd_assoc] at c
  simp only [Category.assoc] at c
  have k : PullPolTriv o ψ' x ↔ evc o.isLB (fst B T ≫ ψ') (snd B T ≫ x ≫ ψ') = 0 :=
    triv_ev_iff o.isLB _ _
  rw [k, c]
  constructor
  · intro z
    exact hQ.eq_one (x ≫ h) ((triv_ev_iff hQ.isLB _ _).2 z)
  · intro z
    rw [z, MonObj.comp_one]
    exact evc_one_right hQ.isLB hQ.zero _

end GlobalTheory.UPel.HT.ES
