import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ModuliInhabitant

/- English proof (translation)
Establish `h1` using `IsTotallyComplex.finrank E`. Establish `h2 : 0 < Module.finrank ℚ E` using `Module.finrank_pos`. Use linear arithmetic over natural numbers and integers.
-/
theorem half_finrank_pos (E : Type) [Field E] [NumberField E] [IsCMField E] :
    0 < Module.finrank ℚ E / 2 := by
  have h1 := IsTotallyComplex.finrank E
  have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hc : Countable Λ` using `TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Establish `hinj : Function.Injective (fun c : ℂ => (⟨fun _ => c, hne _⟩ : Λ))` using `fun a b h => congrFun (congrArg Subtype.val h) ⟨0, hg⟩`. Establish `: Countable ℂ` using `hinj.countable`.

Conclude with `not_countable_iff.2 (inferInstance : Uncountable ℝ) Complex.ofReal_injective.countable`.
-/
theorem exists_not_mem_of_discrete {g : ℕ} (hg : 0 < g) (Λ : AddSubgroup (Fin g → ℂ))
    [DiscreteTopology Λ] : ∃ z, z ∉ Λ := by
  by_contra hne
  push Not at hne
  have hc : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hinj : Function.Injective (fun c : ℂ => (⟨fun _ => c, hne _⟩ : Λ)) := fun a b h =>
    congrFun (congrArg Subtype.val h) ⟨0, hg⟩
  have : Countable ℂ := hinj.countable
  exact not_countable_iff.2 (inferInstance : Uncountable ℝ) Complex.ofReal_injective.countable

/- English proof (translation)
Take `⟨Xo⟩` from `GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level E H D l hr`. Take `⟨⟨g, ty, h⟩, h2, -⟩` from `GlobalTheory.PeriodExists.typeFn_period_exist E H D`. Establish `hg : 0 < g`. Rewrite using `[(h2 g ty h).1]`. Conclude with `Nat.mul_pos (half_finrank_pos E) hr`.

Take `⟨U⟩` from `GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (KA l).val.toRingHom g ty hr rfl h`. Set `i : Fin U.n` to `⟨0, U.n_pos⟩`. Take `⟨-, P, hP⟩` from `(GlobalTheory.PeriodExists.typeFn_period_exist E H (U.Di i)).2.1 g ty (by rw [(U.sig i).1, (U.sig i).2]; exact h)`. Use `haveI := hP.2.2.1`. Take `⟨z, hz⟩` from `exists_not_mem_of_discrete hg P.range`.

Conclude with `⟨Xo, g, ty, hg, h, ⟨U⟩, U.u i P, U.over_σ i P hP, U.ex i P z, fun hx => hz ((U.ex_ker i P hP z).1 hx)⟩`.
-/
theorem exists_unif_point (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (hr : 1 ≤ D.p + D.q) (l : Level H) :
    ∃ (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 0 < g ∧ IsTypeFn H D.p D.q ty ∧
      Nonempty (FamilyUnif Xo (KA l).val.toRingHom ty) ∧
      ∃ (y : Sp ℂ ⟶ Xo.X), y ≫ Xo.s = spMap (KA l).val.toRingHom ∧ ∃ x : Over.mk y ⟶ Xo.univ.t.G, x ≠ 1 := by
  obtain ⟨Xo⟩ := GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level E H D l hr
  obtain ⟨⟨g, ty, h⟩, h2, -⟩ := GlobalTheory.PeriodExists.typeFn_period_exist E H D
  have hg : 0 < g := by
    rw [(h2 g ty h).1]
    exact Nat.mul_pos (half_finrank_pos E) hr
  obtain ⟨U⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (KA l).val.toRingHom g ty hr rfl h
  let i : Fin U.n := ⟨0, U.n_pos⟩
  obtain ⟨-, P, hP⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist E H (U.Di i)).2.1 g ty
    (by rw [(U.sig i).1, (U.sig i).2]; exact h)
  haveI := hP.2.2.1
  obtain ⟨z, hz⟩ := exists_not_mem_of_discrete hg P.range
  exact ⟨Xo, g, ty, hg, h, ⟨U⟩, U.u i P, U.over_σ i P hP, U.ex i P z, fun hx => hz ((U.ex_ker i P hP z).1 hx)⟩

/- English proof (translation)
Use `⟨fun E _ _ _ H D hr l => ?_, ?_⟩` and prove the remaining obligations. Take `⟨Xo, g, ty, -, -, -, y, hy⟩` from `exists_unif_point E H D hr l`. Conclude with `⟨Xo, y, hy⟩`. Take `⟨Xo, g, ty, hg, h, hU, y, -⟩` from `exists_unif_point _ GlobalTheory.HostModel.host (GlobalTheory.HostModel.hypDatum GlobalTheory.HostModel.host) (by simp) (GlobalTheory.HostModel.level GlobalTheory.HostModel.host 1 one_pos)`. Use `⟨_, inferInstance, inferInstance, inferInstance, GlobalTheory.HostModel.host, _, _, Xo, ?_, ⟨y.base (IsLocalRing.closedPoint ℂ)⟩, g, ty, hg, h, hU⟩` and prove the remaining obligations.

Simplify `half_finrank_pos GlobalTheory.HostModel.E21` using `[Datum.dim]`.
-/
theorem moduli_inhabited : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → ∀ l : Level H, ∃ (Xo : Moduli D l) (y : Sp ℂ ⟶ Xo.X), y ≫ Xo.s = spMap (KA l).val.toRingHom ∧ ∃ x : Over.mk y ⟶ Xo.univ.t.G, x ≠ 1) ∧ ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l), 0 < D.dim ∧ Nonempty Xo.X ∧ ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), 0 < g ∧ IsTypeFn H D.p D.q ty ∧ Nonempty (FamilyUnif Xo (KA l).val.toRingHom ty) := by
  refine ⟨fun E _ _ _ H D hr l => ?_, ?_⟩
  · obtain ⟨Xo, g, ty, -, -, -, y, hy⟩ := exists_unif_point E H D hr l
    exact ⟨Xo, y, hy⟩
  · obtain ⟨Xo, g, ty, hg, h, hU, y, -⟩ := exists_unif_point _ GlobalTheory.HostModel.host
      (GlobalTheory.HostModel.hypDatum GlobalTheory.HostModel.host) (by simp) (GlobalTheory.HostModel.level GlobalTheory.HostModel.host 1 one_pos)
    refine ⟨_, inferInstance, inferInstance, inferInstance, GlobalTheory.HostModel.host, _, _, Xo, ?_,
      ⟨y.base (IsLocalRing.closedPoint ℂ)⟩, g, ty, hg, h, hU⟩
    simpa [Datum.dim] using half_finrank_pos GlobalTheory.HostModel.E21

end GlobalTheory.ModuliInhabitant
