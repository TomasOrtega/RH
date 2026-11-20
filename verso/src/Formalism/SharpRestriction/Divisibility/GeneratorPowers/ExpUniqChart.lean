import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqGlue
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndExp

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqChart

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

A detailed English derivation is pending.
-/
theorem epsMul_zero {S : Type} [CommRing S] :
    epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · first
    | simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    | (simp [epsMul]; rfl)
  · first
    | simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    | (simp [epsMul]; rfl)

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem epsMul_one {S : Type} [CommRing S] : epsMul (1 : S) = RingHom.id (DualNumber S) := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Treat this case separately. Apply the first step, then apply the next step to every resulting obligation.

Treat this case separately. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem fst_comp_tan {S : Type} [CommRing S] (d : ℕ) (j : Fin d) :
    (TrivSqZeroExt.fstHom S S S).comp
      (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) = jetAug := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  first
  | (simp only [AlgHom.comp_apply, Formalism.L2.Pj.jetTan, Formalism.L2.Pj.jetAug, Formalism.L2.Pj.liftJet, Ideal.Quotient.liftₐ_apply,
      Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_toRingHom]
     erw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
     by_cases h : i = (0, j) <;> simp [h])
  | (show TrivSqZeroExt.fst ((MvPolynomial.aeval _) (MvPolynomial.X i)) = (MvPolynomial.aeval _) (MvPolynomial.X i)
     by_cases h : i = (0, j) <;> simp [h])

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem comp_one_gen {X : Scheme.{0}} {Y Z M : Over X} [GrpObj M] (f : Y ⟶ Z) : f ≫ (1 : Z ⟶ M) = 1 := by
  first
  | simp
  | (rw [MonObj.Hom.one_def, MonObj.Hom.one_def, ← Category.assoc]; congr 1; exact toUnit_unique _ _)
  | simp [MonObj.Hom.one_def]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem tan_eq (y : FrPt Xo c S) (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G) (hx : IsExpChart y x)
    (j : Fin (dL Dw)) :
    (homAt y.x (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left =
      y.u ((ltIdx Dw).symm j).1 ((ltIdx Dw).symm j).2 := by
  obtain ⟨u, hu, hprod⟩ := hx.tan ((ltIdx Dw).symm j)
  have hj : ltIdx Dw ((ltIdx Dw).symm j) = j := Equiv.apply_symm_apply _ _
  have hone : ∀ i, i ≠ j → u i = 1 := by
    intro i hi
    have e : u i = homAt y.x (Algebra.ofId S (DualNumber S)) ≫
        (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] S) ≫ x 1) := by
      apply Over.OverMorphism.ext
      simp only [hu i, hj, if_neg hi, epsMul_zero, ← fst_comp_tan (dL Dw) i]
      simp only [Over.comp_left, homAt, Over.homMk_left]
      simp only [spMap, ← Category.assoc]
      congr 1
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    rw [e, hx.zero 1, comp_one_gen]
  have huj : (u j).left = (homAt y.x (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left := by
    simp [hu j, hj, epsMul_one, spMap, CommRingCat.ofHom_id, Spec.map_id]
  rw [← hprod, ← huj]
  congr 1
  rw [List.prod_ofFn]
  exact (Finset.prod_eq_single j (fun i _ hi => hone i hi) (fun h => absurd (Finset.mem_univ j) h)).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem expUniqTan : ExpUniqTanSt := by
  intro E _ _ _ H Dw l Xo c S _ _ _ y x x' hx hx'
  refine ExpUniqGlue.expUniq E H Dw l Xo c S y (dL Dw) x x' ⟨hx.trunc, hx.law⟩ ⟨hx'.trunc, hx'.law⟩ ?_
  intro j
  apply Over.OverMorphism.ext
  rw [tan_eq y x hx j, tan_eq y x' hx' j]

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqChart
