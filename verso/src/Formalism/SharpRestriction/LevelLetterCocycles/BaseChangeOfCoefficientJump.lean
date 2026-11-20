import Formalism.SharpRestriction.LevelLetterCocycles.BcAtDesc
import Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPosConstLagrangeCondition
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.UnusedSlot80.BCW

variable {l : ℕ} [Fact l.Prime]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Use `letI iA : Algebra ↥LL.1 ↥LL'.1 := (IntermediateField.inclusion hLL).toRingHom.toAlgebra`. Use `haveI tA : IsScalarTower ℚ_[l] ↥LL.1 ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion hLL).commutes x).symm`. Use `letI iO : Algebra ↥(OL LL) ↥(OL LL') := (jO hLL).toAlgebra`. Use `letI sO : SMul ↥(OL LL) ↥(OL LL') := iO.toSMul`. Use `haveI t1 : IsScalarTower ↥(OL LL) ↥(OL LL') ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Use `haveI := isFrac_OL LL`. Establish `hc : Continuous (algebraMap ↥LL.1 ↥LL'.1)`. Use `continuous_induced_rng.2 ?_` and prove the remaining obligations. Conclude with `continuous_subtype_val`. Establish `hO' : Function.Injective (algebraMap ↥(OL LL') ↥LL'.1)` using `Subtype.val_injective`.

Establish `hjO : Function.Injective (algebraMap ↥(OL LL) ↥(OL LL'))`. Introduce `a b h`. Establish `h1` using `congrArg (fun x : ↥(OL LL') => ((x : ↥LL'.1) : Om l)) h`. Conclude with `Subtype.ext (Subtype.ext h1)`. Use `haveI tZ : IsScalarTower ℤ_[l] ↥(OL LL) ↥(OL LL') := IsScalarTower.of_algebraMap_eq fun z => by`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((algebraMap ℤ_[l] ↥(OL LL') z : ↥LL'.1) : Om l) = ((algebraMap ℤ_[l] ↥(OL LL) z : ↥LL.1) : Om l)`. Simplify using `only [SubalgebraClass.coe_algebraMap]`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL'.1, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]`.

Both sides reduce to the same expression. Use `haveI : Module.Finite ↥(OL LL) ↥(OL LL') := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _`. Use `haveI : FaithfulSMul ↥(OL LL) ↥(OL LL') := (faithfulSMul_iff_algebraMap_injective _ _).2 hjO`. Use `haveI : Module.IsTorsionFree ↥(OL LL) ↥(OL LL') := ⟨fun r hr a b hab => by`. Establish `hr0 : algebraMap ↥(OL LL) ↥(OL LL') r ≠ 0` using `fun h => hr.ne_zero (hjO (h.trans (map_zero _).symm))`.

Simplify using `only [Algebra.smul_def] at hab`. Conclude with `mul_left_cancel₀ hr0 hab⟩`. Use `haveI : Module.Free ↥(OL LL) ↥(OL LL') := Module.free_of_finite_type_torsion_free'`. Set `bO` to `Module.Free.chooseBasis ↥(OL LL) ↥(OL LL')`. Use `haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2`.

Use `haveI : IsIntegralClosure ↥(OL LL') ℤ_[l] ↥LL'.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL'.1`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid ↥(OL LL') (nonZeroDivisors ℤ_[l])) ↥LL'.1 := IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] ↥LL'.1 ↥(OL LL')`. Set `b : Module.Free.ChooseBasisIndex ↥(OL LL) ↥(OL LL') → ↥LL'.1` to `fun i => algebraMap ↥(OL LL') ↥LL'.1 (bO i)`. Establish `hliO : LinearIndependent ↥(OL LL) b` using `bO.linearIndependent.map' (IsScalarTower.toAlgHom ↥(OL LL) ↥(OL LL') ↥LL'.1).toLinearMap (LinearMap.ker_eq_bot.2 hO')`. Establish `hli : LinearIndependent ↥LL.1 b` using `linInd_frac (O := ↥(OL LL)) b hliO`.

Establish `hy : ∀ a : ↥(OL LL'), algebraMap ↥(OL LL') ↥LL'.1 a ∈ Submodule.span ↥LL.1 (Set.range b)`. Introduce `a`. Rewrite using `[← bO.sum_repr a, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `e : algebraMap ↥(OL LL') ↥LL'.1 (bO.repr a i • bO i) = (algebraMap ↥(OL LL) ↥LL.1 (bO.repr a i)) • b i`.

Rewrite using `[Algebra.smul_def, map_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hsp : ⊤ ≤ Submodule.span ↥LL.1 (Set.range b)`. Introduce `x _`.

Take `⟨⟨a, s⟩, hx⟩` from `IsLocalization.surj (Algebra.algebraMapSubmonoid ↥(OL LL') (nonZeroDivisors ℤ_[l])) x`. Take `⟨z, hz, hzs⟩` from `s.2`. Establish `e1 : algebraMap ↥(OL LL') ↥LL'.1 (s : ↥(OL LL')) = algebraMap ℚ_[l] ↥LL'.1 (z : ℚ_[l])`. Rewrite using `[← hzs, ← IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL') ↥LL'.1, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL'.1]`. Both sides reduce to the same expression.

Establish `hz0 : (z : ℚ_[l]) ≠ 0`. Introduce `h0`. Conclude with `nonZeroDivisors.coe_ne_zero ⟨z, hz⟩ (PadicInt.coe_eq_zero.1 h0)`. Establish `hq : algebraMap ℚ_[l] ↥LL'.1 (z : ℚ_[l]) ≠ 0` using `(map_ne_zero _).2 hz0`. Establish `hxe : x = algebraMap ↥LL.1 ↥LL'.1 (algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l])⁻¹) * algebraMap ↥(OL LL') ↥LL'.1 a`.

Rewrite using `[← IsScalarTower.algebraMap_apply, map_inv₀, ← hx, e1]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hxe, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ (hy a)`. Set `bL` to `Module.Basis.mk hli hsp`.

Establish `hb : ∀ i, bL i = algebraMap ↥(OL LL') ↥LL'.1 (bO i)` using `fun i => Module.Basis.mk_apply hli hsp i`. Establish `hlin : ∀ φ : ↥LL'.1 →ₗ[↥LL.1] ↥LL.1, Continuous φ` using `fun φ => LinearMap.continuous_of_finiteDimensional (φ.restrictScalars ℚ_[l])`. Establish `hk : lenOl ((Th l).PD K) (O` using `↥(OL LL)) ≠ ⊤ := by`. Establish `hp : (((((Th l).PD K).p : ℕ)) : ↥(OL LL)) ≠ 0`. Rewrite using `[(Th l).PD_p K]`.

Introduce `h0`. Establish `h1` using `congrArg (algebraMap ↥(OL LL) ↥LL.1) h0`. Rewrite `h1` using `[map_natCast, map_zero]`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1`. Take `⟨k, hk⟩` from `Formalism.MainNotions.RamifiedCoefficientChains.len_quot_nat _ hp`.

Unfold `lenOl`. Rewrite using `[hk]`. Conclude with `ENat.natCast_ne_top k`. Establish `e : IsScalarTower.toAlgHom ℚ_[l] ↥LL.1 ↥LL'.1 = IntermediateField.inclusion hLL` using `AlgHom.ext fun _ => rfl`. Rewrite using `[← e]`.

Conclude with `bcAt_desc ((Th l).PD K) hc hO' hJ bO bL hb hlin hk`.
-/
theorem bcAt_fin (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) (Th : LocTheory) (K LL LL' : FinExt l)
    (hLL : LL.1 ≤ LL'.1) :
    Formalism.MainNotions.WachCoordinates.BCAt ((Th l).PD K) (LL := ↥LL.1) (O := ↥(OL LL)) (O' := ↥(OL LL'))
      (IntermediateField.inclusion hLL) := by
  letI iA : Algebra ↥LL.1 ↥LL'.1 := (IntermediateField.inclusion hLL).toRingHom.toAlgebra
  haveI tA : IsScalarTower ℚ_[l] ↥LL.1 ↥LL'.1 :=
    IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion hLL).commutes x).symm
  letI iO : Algebra ↥(OL LL) ↥(OL LL') := (jO hLL).toAlgebra
  letI sO : SMul ↥(OL LL) ↥(OL LL') := iO.toSMul
  haveI t1 : IsScalarTower ↥(OL LL) ↥(OL LL') ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := isFrac_OL LL
  have hc : Continuous (algebraMap ↥LL.1 ↥LL'.1) := by
    refine continuous_induced_rng.2 ?_
    exact continuous_subtype_val
  have hO' : Function.Injective (algebraMap ↥(OL LL') ↥LL'.1) := Subtype.val_injective
  have hjO : Function.Injective (algebraMap ↥(OL LL) ↥(OL LL')) := by
    intro a b h
    have h1 := congrArg (fun x : ↥(OL LL') => ((x : ↥LL'.1) : Om l)) h
    exact Subtype.ext (Subtype.ext h1)

  haveI tZ : IsScalarTower ℤ_[l] ↥(OL LL) ↥(OL LL') := IsScalarTower.of_algebraMap_eq fun z => by
    apply Subtype.ext; apply Subtype.ext
    show ((algebraMap ℤ_[l] ↥(OL LL') z : ↥LL'.1) : Om l) = ((algebraMap ℤ_[l] ↥(OL LL) z : ↥LL.1) : Om l)
    simp only [SubalgebraClass.coe_algebraMap]
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL'.1, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
    rfl
  haveI : Module.Finite ↥(OL LL) ↥(OL LL') := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI : FaithfulSMul ↥(OL LL) ↥(OL LL') := (faithfulSMul_iff_algebraMap_injective _ _).2 hjO
  haveI : Module.IsTorsionFree ↥(OL LL) ↥(OL LL') := ⟨fun r hr a b hab => by
    have hr0 : algebraMap ↥(OL LL) ↥(OL LL') r ≠ 0 := fun h => hr.ne_zero (hjO (h.trans (map_zero _).symm))
    simp only [Algebra.smul_def] at hab
    exact mul_left_cancel₀ hr0 hab⟩
  haveI : Module.Free ↥(OL LL) ↥(OL LL') := Module.free_of_finite_type_torsion_free'
  let bO := Module.Free.chooseBasis ↥(OL LL) ↥(OL LL')

  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : IsIntegralClosure ↥(OL LL') ℤ_[l] ↥LL'.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL'.1
  haveI : IsLocalization (Algebra.algebraMapSubmonoid ↥(OL LL') (nonZeroDivisors ℤ_[l])) ↥LL'.1 :=
    IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] ↥LL'.1 ↥(OL LL')
  let b : Module.Free.ChooseBasisIndex ↥(OL LL) ↥(OL LL') → ↥LL'.1 :=
    fun i => algebraMap ↥(OL LL') ↥LL'.1 (bO i)
  have hliO : LinearIndependent ↥(OL LL) b :=
    bO.linearIndependent.map' (IsScalarTower.toAlgHom ↥(OL LL) ↥(OL LL') ↥LL'.1).toLinearMap
      (LinearMap.ker_eq_bot.2 hO')
  have hli : LinearIndependent ↥LL.1 b := linInd_frac (O := ↥(OL LL)) b hliO
  have hy : ∀ a : ↥(OL LL'), algebraMap ↥(OL LL') ↥LL'.1 a ∈ Submodule.span ↥LL.1 (Set.range b) := by
    intro a
    rw [← bO.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : algebraMap ↥(OL LL') ↥LL'.1 (bO.repr a i • bO i) =
        (algebraMap ↥(OL LL) ↥LL.1 (bO.repr a i)) • b i := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span ↥LL.1 (Set.range b) := by
    intro x _
    obtain ⟨⟨a, s⟩, hx⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid ↥(OL LL') (nonZeroDivisors ℤ_[l])) x
    obtain ⟨z, hz, hzs⟩ := s.2
    have e1 : algebraMap ↥(OL LL') ↥LL'.1 (s : ↥(OL LL')) = algebraMap ℚ_[l] ↥LL'.1 (z : ℚ_[l]) := by
      rw [← hzs, ← IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL') ↥LL'.1,
        IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL'.1]
      rfl
    have hz0 : (z : ℚ_[l]) ≠ 0 := by
      intro h0
      exact nonZeroDivisors.coe_ne_zero ⟨z, hz⟩ (PadicInt.coe_eq_zero.1 h0)
    have hq : algebraMap ℚ_[l] ↥LL'.1 (z : ℚ_[l]) ≠ 0 := (map_ne_zero _).2 hz0
    have hxe : x = algebraMap ↥LL.1 ↥LL'.1 (algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l])⁻¹) *
        algebraMap ↥(OL LL') ↥LL'.1 a := by
      rw [← IsScalarTower.algebraMap_apply, map_inv₀, ← hx, e1]
      field_simp
    rw [hxe, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hy a)
  let bL := Module.Basis.mk hli hsp
  have hb : ∀ i, bL i = algebraMap ↥(OL LL') ↥LL'.1 (bO i) := fun i => Module.Basis.mk_apply hli hsp i
  have hlin : ∀ φ : ↥LL'.1 →ₗ[↥LL.1] ↥LL.1, Continuous φ := fun φ =>
    LinearMap.continuous_of_finiteDimensional (φ.restrictScalars ℚ_[l])
  have hk : lenOl ((Th l).PD K) (O := ↥(OL LL)) ≠ ⊤ := by
    have hp : (((((Th l).PD K).p : ℕ)) : ↥(OL LL)) ≠ 0 := by
      rw [(Th l).PD_p K]
      intro h0
      have h1 := congrArg (algebraMap ↥(OL LL) ↥LL.1) h0
      rw [map_natCast, map_zero] at h1
      exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
    obtain ⟨k, hk⟩ := Formalism.MainNotions.RamifiedCoefficientChains.len_quot_nat _ hp
    unfold lenOl
    rw [hk]
    exact ENat.natCast_ne_top k
  have e : IsScalarTower.toAlgHom ℚ_[l] ↥LL.1 ↥LL'.1 = IntermediateField.inclusion hLL :=
    AlgHom.ext fun _ => rfl
  rw [← e]
  exact bcAt_desc ((Th l).PD K) hc hO' hJ bO bL hb hlin hk

/- English proof (translation)
Introduce `l _ K LL LL' hLL`. Conclude with `bcAt_fin hJ Th K LL LL' hLL`.
-/
theorem base_change_of_coefficient_jump (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) (Th : LocTheory) : Formalism.MainNotions.WachCoordinates.admBC Th := by
  intro l _ K LL LL' hLL
  exact bcAt_fin hJ Th K LL LL' hLL

/- English proof (translation)
The claim follows from `base_change_of_coefficient_jump hJ D.loc`.
-/
theorem base_change_statement_of_jump (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) (D : D7) : Formalism.MainNotions.UnusedSlot80.H1fBaseChangeTheorem D :=
  base_change_of_coefficient_jump hJ D.loc

end Formalism.MainNotions.UnusedSlot80.BCF
