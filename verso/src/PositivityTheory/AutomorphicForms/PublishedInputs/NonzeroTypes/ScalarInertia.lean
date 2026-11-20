import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Module
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilDeligne

namespace UpperTheory.TNZ.ScalarInertia

/- English proof (translation)
Establish `hg : (f - algebraMap ℂ (End ℂ V) c).IsSemisimple` using `Module.End.isSemisimple_sub_algebraMap_iff.mpr hs`. Establish `hn : IsNilpotent (f - algebraMap ℂ (End ℂ V) c)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Use `LinearMap.aeval_self_charpoly f` as an intermediate fact. Rewrite `this` using `[hc]`.

Simplify `this` using `[map_pow, map_sub, aeval_X, aeval_C]`. Conclude with `sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hn hg)`.
-/
theorem eq_algebraMap_of_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : End ℂ V) (hs : f.IsSemisimple) (c : ℂ) (m : ℕ) (hc : f.charpoly = (X - C c) ^ m) :
    f = algebraMap ℂ (End ℂ V) c := by
  have hg : (f - algebraMap ℂ (End ℂ V) c).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.mpr hs
  have hn : IsNilpotent (f - algebraMap ℂ (End ℂ V) c) := by
    refine ⟨m, ?_⟩
    have := LinearMap.aeval_self_charpoly f
    rw [hc] at this
    simpa [map_pow, map_sub, aeval_X, aeval_C] using this
  exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hn hg)

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
The claim follows from `hψ.of_le fun σ hσ => by simp [hσ]`.
-/
theorem isSmooth_inv {ψ : Weil h →* ℂˣ} (hψ : IsSmooth ψ) : IsSmooth ψ⁻¹ :=
  hψ.of_le fun σ hσ => by simp [hσ]

variable [IsAlgClosure E Ω]

/- English proof (translation)
Use `⟨hN, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[WDRep.twist_ρ, eq_algebraMap_of_charpoly _ (a.semisimple _) _ _ (hc t), Algebra.algebraMap_eq_smul_one, smul_smul, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]`.
-/
theorem unr_twist {n : ℕ} (a : WDRep h (Fin n → ℂ)) (ψ : Weil h →* ℂˣ) (hψ : IsSmooth ψ) (hN : a.N = 0)
    (m : ℕ) (hc : ∀ t : Ine (F := E) A,
      (a.ρ (ineIncl h t)).charpoly = (X - C ((ψ (ineIncl h t) : ℂˣ) : ℂ)) ^ m) :
    (a.twist ψ⁻¹ (isSmooth_inv hψ)).Unr := by
  refine ⟨hN, fun t => ?_⟩
  rw [WDRep.twist_ρ, eq_algebraMap_of_charpoly _ (a.semisimple _) _ _ (hc t),
    Algebra.algebraMap_eq_smul_one, smul_smul, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]

/- English proof (translation)
Use `⟨(TensorProduct.congr (LinearEquiv.refl ℂ (Fin n → ℂ)) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans (TensorProduct.rid ℂ (Fin n → ℂ)), fun σ x => ?_, fun x => ?_⟩` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y`. Simplify using `only [WDRep.tensor_ρ, TensorProduct.map_tmul, WDRep.twist_ρ, WDRep.ofChars_ρ, LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.rid_tmul, LinearEquiv.funUnique_apply, Function.eval, diagEnd_apply, LinearMap.smul_apply, map_smul, smul_smul, M …`.

Use `congr 1`. Rewrite using `[mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Simplify using `[hN]`.
-/
theorem iso_tensor {n : ℕ} (a : WDRep h (Fin n → ℂ)) (ψ : Weil h →* ℂˣ) (hψ : IsSmooth ψ) (hN : a.N = 0) :
    ((a.twist ψ⁻¹ (isSmooth_inv hψ)).tensor
      (WDRep.ofChars h (ι := Fin 1) (fun _ => ψ) fun _ => hψ)).Iso a := by
  refine ⟨(TensorProduct.congr (LinearEquiv.refl ℂ (Fin n → ℂ)) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ (Fin n → ℂ)), fun σ x => ?_, fun x => ?_⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [WDRep.tensor_ρ, TensorProduct.map_tmul, WDRep.twist_ρ, WDRep.ofChars_ρ,
        LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.rid_tmul,
        LinearEquiv.funUnique_apply, Function.eval, diagEnd_apply, LinearMap.smul_apply, map_smul, smul_smul,
        MonoidHom.inv_apply]
      congr 1
      rw [mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    | add x y hx hy => simp only [map_add, hx, hy]
  · simp [hN]

end UpperTheory.TNZ.ScalarInertia

namespace UpperTheory.TNZ

open ScalarInertia in
/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h v ψ hψ hv hc`. Take `⟨n, a, rfl⟩` from `WD.exists_rep v`. Rewrite `hv` using `[WD.monodromyZero_ofWeilDeligneRepClass_iff]`. Simplify using `only [WD.charPol_mk, WD.lpDim_mk] at hc`. Use `⟨WD.mk (a.twist ψ⁻¹ (isSmooth_inv hψ)), (WD.unr_mk _).mpr (unr_twist a ψ hψ hv _ hc), by simp, ?_⟩` and prove the remaining obligations.

Rewrite using `[WD.lpOfChar, WD.lpChar_mk]`. Conclude with `WD.sound (iso_tensor a ψ hψ hv).symm`.
-/
theorem step_scalarInertia : ScalarOnInertiaProp := by
  intro E Ω _ _ _ _ _ A w h v ψ hψ hv hc
  obtain ⟨n, a, rfl⟩ := WD.exists_rep v
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hv
  simp only [WD.charPol_mk, WD.lpDim_mk] at hc
  refine ⟨WD.mk (a.twist ψ⁻¹ (isSmooth_inv hψ)), (WD.unr_mk _).mpr (unr_twist a ψ hψ hv _ hc), by simp, ?_⟩
  rw [WD.lpOfChar, WD.lpChar_mk]
  exact WD.sound (iso_tensor a ψ hψ hv).symm

end UpperTheory.TNZ
