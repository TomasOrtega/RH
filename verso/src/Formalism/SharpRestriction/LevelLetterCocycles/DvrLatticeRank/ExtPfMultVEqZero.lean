import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ExtPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

/- English proof (translation)
Establish `hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp` using `fun x hx => PD.Fil_anti a hx`. Unfold `FilV`. Introduce and unpack `_ ⟨t, rfl⟩`. Use `⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle) t, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp]`.

Both sides reduce to the same expression.
-/
theorem extPf_filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  have hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp :=
    fun x hx => PD.Fil_anti a hx
  unfold FilV
  rintro _ ⟨t, rfl⟩
  refine ⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle) t, ?_⟩
  rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp]
  rfl

/- English proof (translation)
The claim follows from `inf_le_inf_left _ (extPf_filV_succ_le PD (LL := LL) (V := V) a)`.
-/
theorem extPf_fildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a :=
  inf_le_inf_left _ (extPf_filV_succ_le PD (LL := LL) (V := V) a)

/- English proof (translation)
Unfold `IsJumpV at h`. Unfold `multV`. Rewrite using `[not_not.1 h, sub_self]`.
-/
theorem extPf_multV_eq_zero (τ : K →ₐ[Qp] LL) (a : ℤ) (h : ¬ IsJumpV PD ρ τ a) :
    multV PD ρ τ a = 0 := by
  unfold IsJumpV at h
  unfold multV
  rw [not_not.1 h, sub_self]

/- English proof (translation)
Introduce `hj`. Unfold `IsJumpV at hj`. Apply `hj` to reduce the goal to its premises. Use `haveI : FiniteDimensional LL ↥(DdRE PD ρ τ) := hfin`. Establish `hsub : FildR PD ρ τ a ≤ DdRE PD ρ τ`.

Unfold `FildR`. Conclude with `inf_le_left`. Use `haveI : FiniteDimensional LL ↥(FildR PD ρ τ a) := Submodule.finiteDimensional_of_le hsub`. Apply `Submodule.eq_of_le_of_finrank_eq (extPf_fildR_succ_le PD ρ τ a)` to reduce the goal to its premises. Unfold `multV at h`.

Use linear arithmetic over natural numbers and integers.
-/
theorem extPf_not_jump (τ : K →ₐ[Qp] LL) (hfin : Module.Finite LL ↥(DdRE PD ρ τ)) (a : ℤ)
    (h : multV PD ρ τ a = 0) : ¬ IsJumpV PD ρ τ a := by
  intro hj
  unfold IsJumpV at hj
  apply hj
  haveI : FiniteDimensional LL ↥(DdRE PD ρ τ) := hfin
  have hsub : FildR PD ρ τ a ≤ DdRE PD ρ τ := by
    unfold FildR
    exact inf_le_left
  haveI : FiniteDimensional LL ↥(FildR PD ρ τ a) := Submodule.finiteDimensional_of_le hsub
  apply Submodule.eq_of_le_of_finrank_eq (extPf_fildR_succ_le PD ρ τ a)
  unfold multV at h
  omega

end Gen

/- English proof (translation)
Introduce `D HW F Cm CA CB CK hA l _ _ K LL hG T h' hh' hc hj κ hκ`. Take `⟨-, -, -, -, -, -, -, -, -, -, h8, h11, -⟩` from `hA`. Establish `: FiniteDimensional ℚ_[l] ↥LL.1` using `LL.2`. Take `⟨h1, hz⟩` from `Formalism.MainNotions.LiftingTheory.lone_HOne0 ((HW l).W K 1 LL hG)`. Take `⟨Tp, ι, π, hcp, hext⟩` from `Formalism.MainNotions.LiftingTheory.lext_HExt_D D HW F l K 1 LL hG h1 T κ hc hκ`.

Use `⟨Tp, ι, π, hext, hcp, h1, fun τ a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hout`. Take `⟨-, -, hadd⟩` from `h11 l K LL T Tp ((HW l).W K 1 LL hG).one ι π hext.1 hcp`. Establish `hfin` using `((h8 l K LL Tp).2 τ).1`. Establish `h0 : multV ((D.loc l).PD K) T.ρ τ a = 0` using `extPf_multV_eq_zero _ _ τ a fun hT => hout (hj τ a hT)`.

Establish `h2 : multV ((D.loc l).PD K) ((HW l).W K 1 LL hG).one.ρ τ a = 0`. Use `extPf_multV_eq_zero _ _ τ a fun hO => hout ?_` and prove the remaining obligations. Rewrite using `[hz τ a hO]`. Conclude with `Set.mem_Icc.2 ⟨by omega, by omega⟩`. Conclude with `extPf_not_jump _ _ τ hfin a (by have := hadd τ a; omega) ha`.
-/
theorem ext_pf : Formalism.MainNotions.N.Ln34.ExtStep := by
  intro D HW F Cm CA CB CK hA l _ _ K LL hG T h' hh' hc hj κ hκ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h8, h11, -⟩ := hA
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨h1, hz⟩ := Formalism.MainNotions.LiftingTheory.lone_HOne0 ((HW l).W K 1 LL hG)
  obtain ⟨Tp, ι, π, hcp, hext⟩ := Formalism.MainNotions.LiftingTheory.lext_HExt_D D HW F l K 1 LL hG h1 T κ hc hκ
  refine ⟨Tp, ι, π, hext, hcp, h1, fun τ a ha => ?_⟩
  by_contra hout
  obtain ⟨-, -, hadd⟩ := h11 l K LL T Tp ((HW l).W K 1 LL hG).one ι π hext.1 hcp
  have hfin := ((h8 l K LL Tp).2 τ).1
  have h0 : multV ((D.loc l).PD K) T.ρ τ a = 0 :=
    extPf_multV_eq_zero _ _ τ a fun hT => hout (hj τ a hT)
  have h2 : multV ((D.loc l).PD K) ((HW l).W K 1 LL hG).one.ρ τ a = 0 := by
    refine extPf_multV_eq_zero _ _ τ a fun hO => hout ?_
    rw [hz τ a hO]
    exact Set.mem_Icc.2 ⟨by omega, by omega⟩
  exact extPf_not_jump _ _ τ hfin a (by have := hadd τ a; omega) ha

end Formalism.MainNotions.N.Ln34.ExtPf

end
