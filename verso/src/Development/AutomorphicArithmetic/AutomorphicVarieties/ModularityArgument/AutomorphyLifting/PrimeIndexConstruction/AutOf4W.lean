import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.RankFourAutomorphyOfTensor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.AutOf4Of
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.GoodOf4
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.IrrIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralityOfNormCoefficients
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3 UpperTheory.V.Cu

open UpperTheory.V.Cu.AutomorphyOfRankFourLift in
/- English proof (translation)
Introduce `Ω _ _ _ l _ d T hT hok hirr hoff`. Establish `h1 : Irr ((mapRep (algebraMap d.c₁.O (PadicAlgCl l)) (rep4 1 d.ρ₁ d.τ)).comp (resQ T.L))`. Use `irr_cover _ _ (fun x => ?_) hirr` and prove the remaining obligations. Establish `hfix : ∀ z ∈ T.L, (x : G T.F Ω) z = z`. Introduce `z hz`.

Establish `hz' : z ∈ T.F ⊔ T.K` using `T.hL ▸ hz`. Establish `hle : T.F ⊔ T.K ≤ IntermediateField.fixedField (Subgroup.zpowers (resQ T.F x))`. Rewrite using `[sup_le_iff, IntermediateField.le_iff_le, IntermediateField.le_iff_le, Subgroup.zpowers_le, Subgroup.zpowers_le]`. Use `⟨?_, x.2.1⟩` and prove the remaining obligations. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`.

Conclude with `fun y hy => x.1.commutes ⟨y, hy⟩`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).1 (hle hz') _ (Subgroup.mem_zpowers _)`. Set `y : G T.L Ω` to `{ (x : G T.F Ω).toRingEquiv with commutes' := fun z => hfix z.1 z.2 }`. Use `⟨y, ((toB d.δ (resQ T.F x) : (Qbar l)ˣ) : Qbar l), ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.comp_apply, MonoidHom.comp_apply, q_apply, show resQ T.L y = resQ T.F (x : G T.F Ω) from AlgEquiv.ext fun _ => rfl]`.

Both sides reduce to the same expression. Establish `hL : IsIrr ((tenB d.ρ₁ d.τ).comp (resQ T.L))`. Use `((irrIff (Qbar l)).1 _).1 h1` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g : 2`.

Both sides reduce to the same expression. Establish `hkL : ¬ d.K' ≤ T.L` using `fun hle => by`. Take `⟨g, hg, hn⟩` from `hne Ω l d T hT hok`. Use `hn (IntermediateField.fixingSubgroup_le hle ?_)` and prove the remaining obligations. Rewrite using `[T.hL, IntermediateField.fixingSubgroup_sup]`.

Conclude with `⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => g.commutes ⟨y, hy⟩, hg.1⟩`. Use `haveI : Algebra.IsQuadraticExtension ℚ T.K := { finrank_eq_two' := T.degK }`. Establish `hK : IsAbelianGalois ℚ T.K` using `IsAbelianGalois.of_isCyclic ℚ T.K`. Establish `hLa : IsAbelianGalois ℚ T.L`. Establish `h` using `@GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ T.F T.K T.nF.to_finiteDimensional T.nK.to_finiteDimensional T.abF hK`.

Rewrite `h` using `[← T.hL]`. Conclude with `h`. Establish `hatt` using `hoff T.L hLa hkL (goodOf4 Ω l d.c d.D d.T₀ T d.ctx.1 hT d.K' d.quad.splS d.quad.off d.w d.θ d.wp d.wsp d.wunr d.k _ d.ρ d.c₁ d.h d.ρ₁ d.x d.mod) hL`. Establish `key : Af.tw (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp (resLe T.F_le)).toHomUnits ((toB d.δ).comp (resQ T.L))⁻¹ = (tenB d.ρ₁ d.τ).comp (resQ T.L)`. Use extensionality with `g : 2`.

Rewrite using `[tw_val]`. Express the relevant statement in the definitionally equal form `_ • ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r (resLe T.F_le g) = _`. Rewrite using `[q_apply, smul_smul]`. Simplify using `only [MonoidHom.inv_apply, MonoidHom.comp_apply]`. Rewrite using `[show resQ T.F (resLe T.F_le g) = resQ T.L g from AlgEquiv.ext fun _ => rfl, Units.inv_mul, one_smul]`.

Both sides reduce to the same expression. Rewrite using `[key]`. Conclude with `hatt`.
-/
theorem UpperTheory.V.Z.Win.Birth.autOf4W (hne : AlNe) :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Cu.Dat Ω l) (T : Tower d.D), d.T₀.Le T → T.Ok →
    Irr (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp T.G'.subtype) → Z.Win.Birth.OffW d.ι d.K' d.ρ (tenB d.ρ₁ d.τ) →
    Z.Win.Birth.AllW d.ι (Af.tw (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp
      (resLe T.F_le)).toHomUnits ((toB d.δ).comp (resQ T.L))⁻¹) := by
  intro Ω _ _ _ l _ d T hT hok hirr hoff
  have h1 : Irr ((mapRep (algebraMap d.c₁.O (PadicAlgCl l)) (rep4 1 d.ρ₁ d.τ)).comp (resQ T.L)) := by
    refine irr_cover _ _ (fun x => ?_) hirr
    have hfix : ∀ z ∈ T.L, (x : G T.F Ω) z = z := by
      intro z hz
      have hz' : z ∈ T.F ⊔ T.K := T.hL ▸ hz
      have hle : T.F ⊔ T.K ≤ IntermediateField.fixedField (Subgroup.zpowers (resQ T.F x)) := by
        rw [sup_le_iff, IntermediateField.le_iff_le, IntermediateField.le_iff_le, Subgroup.zpowers_le,
          Subgroup.zpowers_le]
        refine ⟨?_, x.2.1⟩
        rw [IntermediateField.mem_fixingSubgroup_iff]
        exact fun y hy => x.1.commutes ⟨y, hy⟩
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hz') _ (Subgroup.mem_zpowers _)
    let y : G T.L Ω := { (x : G T.F Ω).toRingEquiv with commutes' := fun z => hfix z.1 z.2 }
    refine ⟨y, ((toB d.δ (resQ T.F x) : (Qbar l)ˣ) : Qbar l), ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, q_apply,
      show resQ T.L y = resQ T.F (x : G T.F Ω) from AlgEquiv.ext fun _ => rfl]
    rfl
  have hL : IsIrr ((tenB d.ρ₁ d.τ).comp (resQ T.L)) := by
    have := ((irrIff (Qbar l)).1 _).1 h1
    convert this using 1
    ext g : 2
    rfl
  have hkL : ¬ d.K' ≤ T.L := fun hle => by
    obtain ⟨g, hg, hn⟩ := hne Ω l d T hT hok
    refine hn (IntermediateField.fixingSubgroup_le hle ?_)
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => g.commutes ⟨y, hy⟩, hg.1⟩
  haveI : Algebra.IsQuadraticExtension ℚ T.K := { finrank_eq_two' := T.degK }
  have hK : IsAbelianGalois ℚ T.K := IsAbelianGalois.of_isCyclic ℚ T.K
  have hLa : IsAbelianGalois ℚ T.L := by
    have h := @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ T.F T.K
      T.nF.to_finiteDimensional T.nK.to_finiteDimensional T.abF hK
    rw [← T.hL] at h
    exact h
  have hatt := hoff T.L hLa hkL
    (goodOf4 Ω l d.c d.D d.T₀ T d.ctx.1 hT d.K' d.quad.splS d.quad.off d.w d.θ d.wp d.wsp d.wunr d.k _ d.ρ d.c₁ d.h d.ρ₁ d.x d.mod) hL
  have key : Af.tw (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp (resLe T.F_le)).toHomUnits
      ((toB d.δ).comp (resQ T.L))⁻¹ = (tenB d.ρ₁ d.τ).comp (resQ T.L) := by
    ext g : 2
    rw [tw_val]
    change _ • ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r (resLe T.F_le g) = _
    rw [q_apply, smul_smul]
    simp only [MonoidHom.inv_apply, MonoidHom.comp_apply]
    rw [show resQ T.F (resLe T.F_le g) = resQ T.L g from AlgEquiv.ext fun _ => rfl, Units.inv_mul, one_smul]
    rfl
  rw [key]
  exact hatt
