import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.CellVecFixed
import Development.DiscreteGroups.GlobalIrreducibility.DzGenCpt
import Development.DiscreteGroups.GlobalIrreducibility.DzGenLin

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix MeasureTheory

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

abbrev PS (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) : Type :=
  IndSp (eOne m) (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ))

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `g₀`. Establish `hU : IsOpen {x : GL (Fin m) k | ind (parab k (eOne m)) ((twist (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) (deltaHalf k _)).comp (leviProj k (eOne m))) x f.1 = f.1}` using `f.2`. Establish `h1 : (1 : GL (Fin m) k) ∈ {x : GL (Fin m) k | ind (parab k (eOne m)) ((twist (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) (deltaHalf k _)).comp (leviProj k (eOne m))) x f.1 = f.1}` using `by simp`. Establish `hc : Continuous fun x : GL (Fin m) k => g₀⁻¹ * x` using `continuous_const.mul continuous_id`.

Establish `hmem` using `hc.continuousAt.preimage_mem_nhds (x := g₀) (by rw [inv_mul_cancel]; exact hU.mem_nhds h1)`. Establish `hev : (fun _ => f.1.1 g₀) =ᶠ[nhds g₀] f.1.1`. Use `Filter.mem_of_superset hmem fun x hx => ?_` and prove the remaining obligations. Establish `h2 : f.1.1 (g₀ * (g₀⁻¹ * x)) = f.1.1 g₀` using `congrArg (fun F => F.1 g₀) hx`. Rewrite `h2` using `[mul_inv_cancel_left]`.

Conclude with `h2.symm`. Conclude with `continuousAt_const.congr hev`.
-/
theorem continuous_ps (f : PS k m) : Continuous f.1.1 := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have hU : IsOpen {x : GL (Fin m) k | ind (parab k (eOne m))
      ((twist (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) (deltaHalf k _)).comp (leviProj k (eOne m))) x f.1 =
        f.1} := f.2
  have h1 : (1 : GL (Fin m) k) ∈ {x : GL (Fin m) k | ind (parab k (eOne m))
      ((twist (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) (deltaHalf k _)).comp (leviProj k (eOne m))) x f.1 =
        f.1} := by simp
  have hc : Continuous fun x : GL (Fin m) k => g₀⁻¹ * x := continuous_const.mul continuous_id
  have hmem := hc.continuousAt.preimage_mem_nhds (x := g₀) (by rw [inv_mul_cancel]; exact hU.mem_nhds h1)
  have hev : (fun _ => f.1.1 g₀) =ᶠ[nhds g₀] f.1.1 := by
    refine Filter.mem_of_superset hmem fun x hx => ?_
    have h2 : f.1.1 (g₀ * (g₀⁻¹ * x)) = f.1.1 g₀ := congrArg (fun F => F.1 g₀) hx
    rw [mul_inv_cancel_left] at h2
    exact h2.symm
  exact continuousAt_const.congr hev

def thC (ψ : AddChar k Circle) (c : GL (Fin m) k) : ℂ := ((ψ⁻¹) (superDiag c) : ℂ)

/- English proof (translation)
Simplify using `[thC, superDiag_mul ha hb, AddChar.map_add_eq_mul]`.
-/
theorem thC_mul (ψ : AddChar k Circle) {a b : GL (Fin m) k} (ha : a ∈ unipB k (Fin m)) (hb : b ∈ unipB k (Fin m)) :
    thC ψ (a * b) = thC ψ a * thC ψ b := by
  simp [thC, superDiag_mul ha hb, AddChar.map_add_eq_mul]

/- English proof (translation)
Unfold `superDiag`. Conclude with `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => (Units.continuous_val (M := Matrix (Fin m) (Fin m) k)).matrix_elem i j`.
-/
theorem continuous_superDiag : Continuous (superDiag : GL (Fin m) k → k) := by
  unfold superDiag
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (Units.continuous_val (M := Matrix (Fin m) (Fin m) k)).matrix_elem i j

/- English proof (translation)
Establish `: (thC ψ : GL (Fin m) k → ℂ) = fun c => ((ψ (-superDiag c) : Circle) : ℂ)`. Use function extensionality and compare the values at `c`. Simplify using `[thC, AddChar.inv_apply]`. Rewrite using `[this]`. Conclude with `continuous_subtype_val.comp (hψc.comp continuous_superDiag.neg)`.
-/
theorem continuous_thC (ψ : AddChar k Circle) (hψc : Continuous ψ) : Continuous (thC ψ : GL (Fin m) k → ℂ) := by
  have : (thC ψ : GL (Fin m) k → ℂ) = fun c => ((ψ (-superDiag c) : Circle) : ℂ) := by
    funext c; simp [thC, AddChar.inv_apply]
  rw [this]
  exact continuous_subtype_val.comp (hψc.comp continuous_superDiag.neg)

/- English proof (translation)
Establish `hv : valuation k (superDiag c) < 1`. Unfold `superDiag`. Use `Valuation.map_sum_lt _ one_ne_zero fun i _ => Valuation.map_sum_lt _ one_ne_zero fun j hj => ?_` and prove the remaining obligations. Establish `hij : i ≠ j`. Introduce `h`.

Use `(Finset.mem_filter.1 hj).2` as an intermediate fact. Rewrite `this` using `[h]`. Use linear arithmetic over natural numbers and integers. Conclude with `val_lt_of_mem_KOne hc hij`. Establish `h1 : ψ (-superDiag c) = 1` using `hψ _ (by rwa [Valuation.map_neg])`.

Simplify using `[thC, AddChar.inv_apply, h1]`.
-/
theorem thC_of_mem_KOne (ψ : AddChar k Circle) (hψ : ∀ x, valuation k x < 1 → ψ x = 1) {c : GL (Fin m) k}
    (hc : c ∈ KOne k (Fin m)) : thC ψ c = 1 := by
  have hv : valuation k (superDiag c) < 1 := by
    unfold superDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => Valuation.map_sum_lt _ one_ne_zero fun j hj => ?_
    have hij : i ≠ j := by
      intro h; have := (Finset.mem_filter.1 hj).2; rw [h] at this; omega
    exact val_lt_of_mem_KOne hc hij
  have h1 : ψ (-superDiag c) = 1 := hψ _ (by rwa [Valuation.map_neg])
  simp [thC, AddChar.inv_apply, h1]

end DiscreteGroups.sglob.DzType
