import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiagScaleApply

noncomputable section

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

omit [NeZero e] in

/- English proof (translation)
Establish `h1 (u : Vec K a ι) : diagScale K a ι s u = (fun τ => (C (s τ) : K⟦X⟧)) • u`. Use extensionality with `τ i : 2`. Simplify using `[diagScale_apply, smul_eq_C_mul]`. Establish `h2 : ringAct (TameGal.inertia ξ : TameGal K l e a) (fun τ => (C (s τ) : K⟦X⟧)) = fun τ => C (s τ)`. Use extensionality with `τ n`.

Rewrite using `[ringAct_apply, TameGal.shift_inertia, sub_zero, coeff_rescale, coeff_C]`. Apply the tactic sequence `split_ifs with h <;> simp [h]`. Rewrite using `[h1, h1, Δ.act_smul_tot, h2]`.
-/
theorem act_inertia_diagScale {P : PhiMod O K l e a ι} (Δ : Descent P) (ξ : rootsOfUnity e K)
    (s : ZMod a → K) (w : Vec K a ι) :
    Δ.act (TameGal.inertia ξ) (diagScale K a ι s w) =
      diagScale K a ι s (Δ.act (TameGal.inertia ξ) w) := by
  have h1 (u : Vec K a ι) : diagScale K a ι s u = (fun τ => (C (s τ) : K⟦X⟧)) • u := by
    ext τ i : 2
    simp [diagScale_apply, smul_eq_C_mul]
  have h2 : ringAct (TameGal.inertia ξ : TameGal K l e a) (fun τ => (C (s τ) : K⟦X⟧)) =
      fun τ => C (s τ) := by
    ext τ n
    rw [ringAct_apply, TameGal.shift_inertia, sub_zero, coeff_rescale, coeff_C]
    split_ifs with h <;> simp [h]
  rw [h1, h1, Δ.act_smul_tot, h2]

/- English proof (translation)
Use `letI := Fintype.ofFinite (rootsOfUnity e K)`. Unfold `isoProj`. Rewrite using `[LinearMap.smul_apply]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Introduce `ξ τ`.

Simplify using `only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, act_inertia_diagScale, Finset.sum_apply, diagScale_apply, Finset.smul_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft ξ) _ _ fun ζ => ?_` and prove the remaining obligations. Rewrite using `[Equiv.coe_mulLeft, ← Module.End.mul_apply, ← map_mul, ← map_mul, smul_smul]`. Use `congr 1`. Rewrite using `[map_mul, TameGal.root_mul, TameGal.shift_inertia, sub_zero, ← mul_pow, mul_inv, mul_inv_cancel_left₀ (TameGal.root_ne_zero _ _)]`.
-/
theorem isoProj_mem_isotypic {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e)
    (v : Vec K a ι) : isoProj Δ c v ∈ Δ.isotypic c := by
  letI := Fintype.ofFinite (rootsOfUnity e K)
  unfold isoProj
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  intro ξ τ
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, act_inertia_diagScale,
    Finset.sum_apply, diagScale_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft ξ) _ _ fun ζ => ?_
  rw [Equiv.coe_mulLeft, ← Module.End.mul_apply, ← map_mul, ← map_mul, smul_smul]
  congr 1
  rw [map_mul, TameGal.root_mul, TameGal.shift_inertia, sub_zero, ← mul_pow, mul_inv,
    mul_inv_cancel_left₀ (TameGal.root_ne_zero _ _)]

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Δ c v` and use `isoProj_mem_isotypic Δ c v`.
-/
theorem isoProj_mem_isotypic' : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι)
    (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), GlobalTheory.CokerL.isoProj Δ c v ∈ Δ.isotypic c :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Δ c v => isoProj_mem_isotypic Δ c v

end GlobalTheory.CokerL
