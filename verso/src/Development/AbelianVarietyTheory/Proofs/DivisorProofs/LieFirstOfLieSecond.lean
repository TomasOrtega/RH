import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetry

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open NumberField MvPolynomial Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift.LieFirstPf

variable {P Q R S : ℕ}

def swapE (P Q R S : ℕ) : Formalism.BasicNotions.TH.Pol R S P Q ≃ₗ[ℂ] Formalism.BasicNotions.TH.Pol P Q R S :=
  (renameEquiv ℂ (Equiv.prodComm (Ix R S) (Ix P Q))).toLinearEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem swapE_apply (f : Formalism.BasicNotions.TH.Pol R S P Q) : swapE P Q R S f = rename Prod.swap f := rfl

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> rfl`.
-/
theorem lineSign_swap (a : Ix P Q) (b : Ix R S) :
    lineSign (p := R) (q := S) (r := P) (s := Q) b a = lineSign (p := P) (q := Q) (r := R) (s := S) a b := by
  rcases a with a | a <;> rcases b with b | b <;> rfl

/- English proof (translation)
Simplify using `only [heisOp, swapE_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply, map_smul, map_sum, map_sub, GlobalTheory.FockSwap.rename_raiB, GlobalTheory.FockSwap.rename_lowB]`. Use `congr 1`. Use `Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l => ?_` and prove the remaining obligations. Simplify using `[lineSign_swap]`.
-/
theorem swapE_heisOp (c : Matrix (Ix R S) (Ix P Q) ℂ) (f : Formalism.BasicNotions.TH.Pol R S P Q) :
    swapE P Q R S (heisOp c f) = heisOp cᵀ (swapE P Q R S f) := by
  simp only [heisOp, swapE_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
    map_smul, map_sum, map_sub, GlobalTheory.FockSwap.rename_raiB, GlobalTheory.FockSwap.rename_lowB]
  congr 1
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l => ?_
  simp [lineSign_swap]

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def swapT (ι : Type) (P Q R S : ℕ) :
    (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) ≃ₗ[ℂ] ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S :=
  PiTensorProduct.congr fun _ => swapE P Q R S

/- English proof (translation)
Establish `e : (swapT ι P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (swapT ι P Q R S).toLinearMap`. Use `PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, swapT, PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `hi : i = w`. Substitute `hi` using the available equality. Simplify using `[h]`. Simplify using `[Function.update_of_ne hi]`. Conclude with `LinearMap.congr_fun e T`.
-/
theorem swapT_atPl (w : ι) (L' : Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ f, swapE P Q R S (L' f) = L (swapE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    swapT ι P Q R S (atPl w L' T) = atPl w L (swapT ι P Q R S T) := by
  have e : (swapT ι P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (swapT ι P Q R S).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, swapT,
      PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    by_cases hi : i = w
    · subst hi; simp [h]
    · simp [Function.update_of_ne hi]
  exact LinearMap.congr_fun e T

/- English proof (translation)
Simplify using `only [sumPl, LinearMap.sum_apply, map_sum]`. Conclude with `Finset.sum_congr rfl fun w _ => swapT_atPl w (L' w) (L w) (h w) T`.
-/
theorem swapT_sumPl (L' : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ w f, swapE P Q R S (L' w f) = L w (swapE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    swapT ι P Q R S (sumPl L' T) = sumPl L (swapT ι P Q R S T) := by
  simp only [sumPl, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun w _ => swapT_atPl w (L' w) (L w) (h w) T

end Tensor

open scoped Classical in

/- English proof (translation)
Introduce `h2 F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d d' a b A C Φ om χ m hCM hψ hfr hΦ hdd hW hm`. Establish `hfr' : Framed τ JB JA b a C A` using `⟨by rw [mul_comm]; exact hfr.1, hfr.2.2, hfr.2.1⟩`. Establish `hΦ' : IsFockMap ψ τ d' C A (Φ ∘ₗ (swapT (InfinitePlace F) P Q R S).toLinearMap)`. Use `⟨hΦ.1.comp (swapT (InfinitePlace F) P Q R S).injective, fun u hu c hc T => ?_⟩` and prove the remaining obligations. Establish `hu' : At (evI F) uᵀ` using `fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]`.

Establish `hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ` using `fun w => by`. Rewrite using `[Matrix.transpose_map, hc w]`. Simplify using `[Matrix.transpose_mul, Matrix.mul_assoc]`. Establish `key` using `hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (swapT (InfinitePlace F) P Q R S T)`. Establish `hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ)` using `fun t => by show schr ψ (d'.e _) = schr ψ (d.e _)`.

Rewrite using `[← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr]`. Rewrite using `[swapT_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ) (fun w f => swapE_heisOp (c w) f)]` and apply the resulting hypothesis. Establish `hA` using `h2 F E σ β α κ R S P Q ψ τ JB JA d' b a C A _ om χ m hCM hψ hfr' hΦ' hW hm`. Introduce `γ hγ Y hY T`.

Establish `key` using `hA γ hγ Y hY ((swapT (InfinitePlace F) P Q R S).symm T)`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at key`. Rewrite using `[swapT_sumPl (fun w => fockAct2 R S P Q (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • 1) (fun w => fockAct1 P Q R S (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • 1) (fun w f => by` and apply the resulting hypothesis. Apply the tactic sequence `simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul, swapE_apply, (GlobalTheory.FockSwap.swap_symmetry R S P Q).2.1]), LinearEquiv.apply_symm_apply] at key`.
-/
theorem lieFirst_of_lieSecond : LieSecond → LieFirst := by
  intro h2 F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d d' a b A C Φ om χ m hCM hψ hfr hΦ hdd hW hm
  have hfr' : Framed τ JB JA b a C A := ⟨by rw [mul_comm]; exact hfr.1, hfr.2.2, hfr.2.1⟩
  have hΦ' : IsFockMap ψ τ d' C A (Φ ∘ₗ (swapT (InfinitePlace F) P Q R S).toLinearMap) := by
    refine ⟨hΦ.1.comp (swapT (InfinitePlace F) P Q R S).injective, fun u hu c hc T => ?_⟩
    have hu' : At (evI F) uᵀ := fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]
    have hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ := fun w => by
      rw [Matrix.transpose_map, hc w]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
    have key := hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (swapT (InfinitePlace F) P Q R S T)
    have hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ) := fun t => by
      show schr ψ (d'.e _) = schr ψ (d.e _)
      rw [← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr]
    rwa [swapT_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ) (fun w f => swapE_heisOp (c w) f)]
  have hA := h2 F E σ β α κ R S P Q ψ τ JB JA d' b a C A _ om χ m hCM hψ hfr' hΦ' hW hm
  intro γ hγ Y hY T
  have key := hA γ hγ Y hY ((swapT (InfinitePlace F) P Q R S).symm T)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at key
  rwa [swapT_sumPl (fun w => fockAct2 R S P Q (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • 1)
    (fun w => fockAct1 P Q R S (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • 1) (fun w f => by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul, swapE_apply,
        (GlobalTheory.FockSwap.swap_symmetry R S P Q).2.1]), LinearEquiv.apply_symm_apply] at key

end GlobalTheory.RealLift.LieFirstPf
