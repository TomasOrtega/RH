import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyConstPts
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GenericPointsConstantPointsFormalSumValuesStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecThroughUp
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRigidifiedIsoAgreeAbelianFibresStatement

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

/- English proof (translation)
The claim follows from `RingHom.ext fun _ => rfl`.
-/
theorem algebraMap_laurent_comp_C :
    (algebraMap ℂ⟦X⟧ ℂ⸨X⸩).comp (PowerSeries.C (R := ℂ)) = algebraMap ℂ ℂ⸨X⸩ :=
  RingHom.ext fun _ => rfl

/- English proof (translation)
Introduce `h`. Establish `h' : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ PowerSeries.X ∈ p.asIdeal` using `h`. Establish `hne : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ PowerSeries.X ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective ℂ⟦X⟧ ℂ⸨X⸩)).2 PowerSeries.X_ne_zero`. Conclude with `p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (IsUnit.mk0 _ hne))`.
-/
theorem X_not_mem_gen (p : Sp ℂ⸨X⸩) : PowerSeries.X ∉ (gen p).asIdeal := by
  intro h
  have h' : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ PowerSeries.X ∈ p.asIdeal := h
  have hne : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ PowerSeries.X ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℂ⟦X⟧ ℂ⸨X⸩)).2 PowerSeries.X_ne_zero
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (IsUnit.mk0 _ hne))

/- English proof (translation)
Establish `h : (gen ≫ χ) ≫ Y.s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF) ≫ spMap β`. Rewrite using `[Category.assoc, hχ, ← algebraMap_laurent_comp_C, spMap_comp, spMap_comp, spMap_comp]`. Simplify using `only [Category.assoc]`. Use `Y.jQ_open` as an intermediate fact. Establish `hr : Set.range (pullback.lift _ _ h) ⊆ Set.range Y.jQ`.

Introduce and unpack `_ ⟨p, rfl⟩`. Take `⟨q, hq⟩` from `hab _ (X_not_mem_gen p)`. Establish `hz : Y.jQ q ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G`. Rewrite using `[Y.ab_gen]`. Conclude with `⟨_, rfl⟩`.

Establish `hz' : Y.j q ∈ abLocus Y.t.G`. Simplify `hz` using `only [Model.j, Scheme.Hom.comp_apply, Set.mem_preimage]`. Rewrite using `[← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, ← hq]`. Conclude with `hz'`. Establish `hτ` using `IsOpenImmersion.lift_fac Y.jQ _ hr`.

Use `⟨IsOpenImmersion.lift Y.jQ _ hr, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Model.j, ← Category.assoc, hτ, pullback.lift_fst]`. Rewrite using `[← Y.jQ_over, ← Category.assoc, hτ, pullback.lift_snd]`.
-/
theorem exists_generic_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (bF : c.F →+* ℂ) (χ : Sp ℂ⟦X⟧ ⟶ Y.X)
    (hχ : χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (bF.comp β))
    (hab : ∀ x : Sp ℂ⟦X⟧, PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) :
    ∃ yF : Sp ℂ⸨X⸩ ⟶ Xo.XF c, yF ≫ Y.j = gen ≫ χ ∧
      yF ≫ pullback.snd _ _ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF) := by
  have h : (gen ≫ χ) ≫ Y.s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF) ≫ spMap β := by
    rw [Category.assoc, hχ, ← algebraMap_laurent_comp_C, spMap_comp, spMap_comp, spMap_comp]
    simp only [Category.assoc]
  have := Y.jQ_open
  have hr : Set.range (pullback.lift _ _ h) ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, hq⟩ := hab _ (X_not_mem_gen p)
    have hz : Y.jQ q ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    have hz' : Y.j q ∈ abLocus Y.t.G := by
      simpa only [Model.j, Scheme.Hom.comp_apply, Set.mem_preimage] using hz
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, ← hq]
    exact hz'
  have hτ := IsOpenImmersion.lift_fac Y.jQ _ hr
  refine ⟨IsOpenImmersion.lift Y.jQ _ hr, ?_, ?_⟩
  · rw [Model.j, ← Category.assoc, hτ, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, hτ, pullback.lift_snd]

/- English proof (translation)
Introduce `L₁ L₂ E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ hχ hab`. Take `⟨Ξ⟩` from `GlobalTheory.ConstPoint.nonempty_constPts L₁ L₂ E H D l Xo c O β Y _ a χ W Λ`. Take `⟨ΦW, hW⟩` from `GlobalTheory.T.genericPoints_constantPoints_formalSum_values L₁ L₂ E H D l Xo c O β Y _ a χ W Λ Ξ`. Take `⟨yF, hj, ho⟩` from `exists_generic_point Y bF χ hχ hab`. Take `⟨w₂, r₂⟩` from `(GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres L₁ L₂ E H _ _ Y.t W.t χ W.m).1`.

Take `⟨w₁, r₁⟩` from `(GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres L₁ L₂ E H _ _ Y.t Y.oF.t _ Y.m).1`. Take `⟨w₀, r₀⟩` from `(GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres L₁ L₂ E H _ _ Xo.univ.t Y.oF.t _ Y.m0.toSABMap).1`. Take `⟨ΦY, e₂⟩` from `(GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Y.t W.t χ W.m w₂ gen (gen ≫ χ) r₂ rfl).1 ΦW`. Take `⟨ΦF, e₁⟩` from `(GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Y.t Y.oF.t _ Y.m w₁ yF (gen ≫ χ) r₁ hj).2 ΦY`. Take `⟨Φ, e₀⟩` from `(GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Xo.univ.t Y.oF.t _ Y.m0.toSABMap w₀ yF (yF ≫ pullback.fst _ _) r₀ rfl).1 ΦF`.

Conclude with `⟨⟨Ξ, ΦW, hW, yF, hj, ho, ΦY, ΦF, Φ, w₂, w₁, w₀, r₂, r₁, r₀, e₂, e₁, e₀⟩⟩`.
-/
theorem nonempty_chain : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) , χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (bF.comp β) → (∀ x : Sp ℂ⟦X⟧, PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → Nonempty (Chain W Λ) := by
  intro L₁ L₂ E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ hχ hab
  obtain ⟨Ξ⟩ := GlobalTheory.ConstPoint.nonempty_constPts L₁ L₂ E H D l Xo c O β Y _ a χ W Λ
  obtain ⟨ΦW, hW⟩ := GlobalTheory.T.genericPoints_constantPoints_formalSum_values L₁ L₂ E H D l Xo c O β Y _ a χ W Λ Ξ
  obtain ⟨yF, hj, ho⟩ := exists_generic_point Y bF χ hχ hab
  obtain ⟨w₂, r₂⟩ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres L₁ L₂ E H _ _ Y.t W.t χ W.m).1
  obtain ⟨w₁, r₁⟩ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres L₁ L₂ E H _ _ Y.t Y.oF.t _ Y.m).1
  obtain ⟨w₀, r₀⟩ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres L₁ L₂ E H _ _ Xo.univ.t Y.oF.t _ Y.m0.toSABMap).1
  obtain ⟨ΦY, e₂⟩ := (GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Y.t W.t χ W.m w₂ gen (gen ≫ χ) r₂ rfl).1 ΦW
  obtain ⟨ΦF, e₁⟩ := (GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Y.t Y.oF.t _ Y.m w₁ yF (gen ≫ χ) r₁ hj).2 ΦY
  obtain ⟨Φ, e₀⟩ := (GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Xo.univ.t Y.oF.t _ Y.m0.toSABMap w₀ yF
    (yF ≫ pullback.fst _ _) r₀ rfl).1 ΦF
  exact ⟨⟨Ξ, ΦW, hW, yF, hj, ho, ΦY, ΦF, Φ, w₂, w₁, w₀, r₂, r₁, r₀, e₂, e₁, e₀⟩⟩

end GlobalTheory.ArcPts
