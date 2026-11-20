import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf

set_option autoImplicit false
noncomputable section
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1.Base

variable (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

/- English proof (translation)
Rewrite using `[ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]`. Conclude with `congrArg (fun l => List.prod l) (congrArg List.ofFn (funext fun i => by show mapDR k K L (ExteriorAlgebra.ι K (v i)) = _`. Rewrite using `[mapDR, ExteriorAlgebra.lift_ι_apply]`. Use the proof step `rfl))`.
-/
theorem mapDR_ιMulti (n : ℕ) (v : Fin n → Ω[K⁄k]) :
    mapDR k K L (ExteriorAlgebra.ιMulti K n v) =
      ExteriorAlgebra.ιMulti L n (fun i => KaehlerDifferential.map k k K L (v i)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  exact congrArg (fun l => List.prod l) (congrArg List.ofFn (funext fun i => by
    show mapDR k K L (ExteriorAlgebra.ι K (v i)) = _
    rw [mapDR, ExteriorAlgebra.lift_ι_apply]; rfl))

variable {k K L} in

/- English proof (translation)
Rewrite using `[ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_family, mapDR_ιMulti]`. Conclude with `congrArg _ (funext fun i => (h _).symm)`.
-/
theorem mapDR_basis {I : Type} [LinearOrder I] (bK : Module.Basis I K Ω[K⁄k]) (bL : Module.Basis I L Ω[L⁄k])
    (h : ∀ i, bL i = KaehlerDifferential.map k k K L (bK i)) (s : Finset I) :
    mapDR k K L (bK.ExteriorAlgebra s) = bL.ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.basis_apply_ofCard _ rfl,
    ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_family, mapDR_ιMulti]
  exact congrArg _ (funext fun i => (h _).symm)

variable {k K L} in

/- English proof (translation)
Establish `: ((bL.ExteriorAlgebra.coord s).restrictScalars K ∘ₗ (mapDR k K L).toLinearMap) = Algebra.linearMap K L ∘ₗ bK.ExteriorAlgebra.coord s`. Use `bK.ExteriorAlgebra.ext fun t => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, mapDR_basis bK bL h, LinearMap.coe_restrictScalars, Module.Basis.coord_apply, Module.Basis.repr_self, Algebra.linearMap_apply]`. Distinguish the cases in `hts : t = s`. Substitute `hts` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Finsupp.single_apply, hts]`. Conclude with `congrArg (· ω) this`.
-/
theorem repr_mapDR {I : Type} [LinearOrder I] (bK : Module.Basis I K Ω[K⁄k]) (bL : Module.Basis I L Ω[L⁄k])
    (h : ∀ i, bL i = KaehlerDifferential.map k k K L (bK i)) (ω : DR k K) (s : Finset I) :
    bL.ExteriorAlgebra.repr (mapDR k K L ω) s = algebraMap K L (bK.ExteriorAlgebra.repr ω s) := by
  have : ((bL.ExteriorAlgebra.coord s).restrictScalars K ∘ₗ (mapDR k K L).toLinearMap) =
      Algebra.linearMap K L ∘ₗ bK.ExteriorAlgebra.coord s := by
    refine bK.ExteriorAlgebra.ext fun t => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, mapDR_basis bK bL h,
      LinearMap.coe_restrictScalars, Module.Basis.coord_apply, Module.Basis.repr_self, Algebra.linearMap_apply]
    by_cases hts : t = s
    · subst hts; simp
    · simp [Finsupp.single_apply, hts]
  exact congrArg (· ω) this

end GlobalTheory.W1.Base

namespace GlobalTheory.W1.Base

/- English proof (translation)
Introduce `k K L _ _ _ _ _ _ _ _ _`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective`. Use `haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField`. Use `haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L`. Set `I` to `Module.Basis.ofVectorSpaceIndex K Ω[K⁄k]`.

Use `letI : LinearOrder I := linearOrderOfSTO WellOrderingRel`. Set `bK : Module.Basis I K Ω[K⁄k]` to `Module.Basis.ofVectorSpace K Ω[K⁄k]`. Set `bL : Module.Basis I L Ω[L⁄k]` to `(bK.baseChange L).map (tensorKaehlerEquivOfFormallyEtale k K L)`. Establish `h : ∀ i, bL i = KaehlerDifferential.map k k K L (bK i)` using `fun i => by`. Simplify using `only [bL, Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul]`.

Use `set BK := bK.ExteriorAlgebra`. Use `set BL := bL.ExteriorAlgebra`. Use `⟨fun y => ?_, fun m b ω hb hsum j => ?_⟩` and prove the remaining obligations. Use `set S := (BL.repr y).support`. Use `⟨S.card, fun j => BL.repr y (S.equivFin.symm j), fun j => BK (S.equivFin.symm j), ?_⟩` and prove the remaining obligations.

Simplify using `only [BK, BL, mapDR_basis bK bL h]`. Use `conv_lhs => rw [← BL.linearCombination_repr y, Finsupp.linearCombination_apply, Finsupp.sum, ← Finset.sum_coe_sort]`. Conclude with `(Fintype.sum_equiv S.equivFin _ _ fun _ => by rw [Equiv.symm_apply_apply])`. Establish `hc : ∀ s, ∀ j, BK.repr (ω j) s = 0`. Introduce `s`.

Establish `h0` using `congrArg (fun z => BL.repr z s) hsum`. Simplify using `only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply, BK, BL, repr_mapDR bK bL h] at h0`. Use `Fintype.linearIndependent_iff.1 hb (fun j => BK.repr (ω j) s) ?_` and prove the remaining obligations. Simplify `h0` using `[Algebra.smul_def, mul_comm]`. Conclude with `BK.repr.injective (Finsupp.ext fun s => by simpa using hc s j)`.
-/
theorem forms_baseChange : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L],
    (∀ y : DR k L, ∃ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), y = ∑ j, b j • mapDR k K L (ω j)) ∧
      ∀ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), LinearIndependent K b →
        ∑ j, b j • mapDR k K L (ω j) = 0 → ∀ j, ω j = 0 := by
  intro k K L _ _ _ _ _ _ _ _ _
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let I := Module.Basis.ofVectorSpaceIndex K Ω[K⁄k]
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let bK : Module.Basis I K Ω[K⁄k] := Module.Basis.ofVectorSpace K Ω[K⁄k]
  let bL : Module.Basis I L Ω[L⁄k] := (bK.baseChange L).map (tensorKaehlerEquivOfFormallyEtale k K L)
  have h : ∀ i, bL i = KaehlerDifferential.map k k K L (bK i) := fun i => by
    simp only [bL, Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply,
      mapBaseChange_tmul, one_smul]
  set BK := bK.ExteriorAlgebra
  set BL := bL.ExteriorAlgebra
  refine ⟨fun y => ?_, fun m b ω hb hsum j => ?_⟩
  · set S := (BL.repr y).support
    refine ⟨S.card, fun j => BL.repr y (S.equivFin.symm j), fun j => BK (S.equivFin.symm j), ?_⟩
    simp only [BK, BL, mapDR_basis bK bL h]
    conv_lhs => rw [← BL.linearCombination_repr y, Finsupp.linearCombination_apply, Finsupp.sum, ← Finset.sum_coe_sort]
    exact (Fintype.sum_equiv S.equivFin _ _ fun _ => by rw [Equiv.symm_apply_apply])
  · have hc : ∀ s, ∀ j, BK.repr (ω j) s = 0 := by
      intro s
      have h0 := congrArg (fun z => BL.repr z s) hsum
      simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
        map_zero, Finsupp.coe_zero, Pi.zero_apply, BK, BL, repr_mapDR bK bL h] at h0
      refine Fintype.linearIndependent_iff.1 hb (fun j => BK.repr (ω j) s) ?_
      simpa [Algebra.smul_def, mul_comm] using h0
    exact BK.repr.injective (Finsupp.ext fun s => by simpa using hc s j)

end GlobalTheory.W1.Base
