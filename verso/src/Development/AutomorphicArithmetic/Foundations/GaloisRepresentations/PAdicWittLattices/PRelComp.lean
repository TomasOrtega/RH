import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetIsHeckeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.G3.pRelComp :
    RelComp := by
  unfold UpperTheory.Gal.G3.RelComp
  intro p _ D G L R _ _ gb S s N₁ N₂ N₃ o₁ o₂ o₃ k _ t I₁ I₂ I₃ ψ₁ ψ₂ h₁ h₂ hψ₁ hψ₂ hint
  unfold UpperTheory.Gal.G3.Rel
  refine ⟨?_, ?_⟩
  · intro n hn hcop x y
    rw [Category.comp_id]
    refine (HeckeRestrict.ev_eq_iff I₁ n hn x y).trans
      ((ForgetHecke.acts_one_iff L n hn hcop x y).symm.trans ?_)
    simp
  · intro r₁ r₂ n hn hcop x z
    have htor : (I₁.ev n x ≫ ψ₁) ^ n = 1 := by
      haveI := hψ₁
      have e := map_pow (IsMonHom.monoidHom ψ₁ (Over.mk t)) (I₁.ev n x) n
      simp only [IsMonHom.monoidHom_apply] at e
      rw [← e, (I₁.onto n hn (I₁.ev n x)).2 ⟨x, rfl⟩]
      exact (IsMonHom.monoidHom ψ₁ (Over.mk t)).map_one
    obtain ⟨y, hy⟩ := (I₂.onto n hn _).1 htor
    obtain ⟨v₁, hv₁, e₁⟩ := (r₁ n hn hcop x y).1 hy.symm
    rw [← Category.assoc, ← hy, r₂ n hn hcop y z, map_mul, Module.End.mul_apply, e₁, map_add,
      map_nsmul]
    have hw := hint v₁ hv₁
    constructor
    · rintro ⟨v, hv, e⟩
      refine ⟨v + L.actG h₂ v₁, add_mem hv hw, ?_⟩
      rw [e, smul_add, add_assoc]
    · rintro ⟨v, hv, e⟩
      refine ⟨v - L.actG h₂ v₁, sub_mem hv hw, ?_⟩
      rw [smul_sub, ← add_sub_assoc, ← e, add_sub_cancel_right]
