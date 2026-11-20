import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.CotRank

/- English proof (translation)
Establish `hex : Function.Exact ((p : R) • (LinearMap.id : M →ₗ[R] M)) c` using `fun w => by`. Rewrite using `[hk w]`. Conclude with `⟨fun ⟨w', h⟩ => ⟨w', h.symm⟩, fun ⟨w', h⟩ => ⟨w', h.symm⟩⟩`. Establish `hex'` using `lTensor_exact k hex hs`. Establish `hsurj : Function.Surjective (c.baseChange k)`.

Rewrite using `[LinearMap.baseChange_eq_ltensor]`. Conclude with `LinearMap.lTensor_surjective k hs`. Establish `hzero : ∀ x : k ⊗[R] M, LinearMap.lTensor k ((p : R) • (LinearMap.id : M →ₗ[R] M)) x = 0` using `fun x => by`. Rewrite using `[LinearMap.lTensor_smul, LinearMap.lTensor_id, LinearMap.smul_apply, LinearMap.id_apply]`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a m`. Rewrite using `[TensorProduct.smul_tmul', Algebra.smul_def, map_natCast, CharP.cast_eq_zero, zero_mul, TensorProduct.zero_tmul]`. Consider the case `add x y hx hy => rw [smul_add, hx, hy, add_zero]`. Establish `hinj : Function.Injective (c.baseChange k)`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Rewrite `hx` using `[LinearMap.baseChange_eq_ltensor]`. Take `⟨y, rfl⟩` from `(hex' x).1 hx`. Conclude with `hzero y`.

Conclude with `(LinearEquiv.ofBijective (c.baseChange k) ⟨hinj, hsurj⟩).finrank_eq.symm`.
-/
theorem finrank_baseChange_eq {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : ℕ) (c : M →ₗ[R] N) (hs : Function.Surjective c) (hk : ∀ w, c w = 0 ↔ ∃ w', w = (p : R) • w')
    (k : Type) [Field k] [Algebra R k] [CharP k p] :
    Module.finrank k (k ⊗[R] N) = Module.finrank k (k ⊗[R] M) := by
  have hex : Function.Exact ((p : R) • (LinearMap.id : M →ₗ[R] M)) c := fun w => by
    rw [hk w]
    exact ⟨fun ⟨w', h⟩ => ⟨w', h.symm⟩, fun ⟨w', h⟩ => ⟨w', h.symm⟩⟩
  have hex' := lTensor_exact k hex hs
  have hsurj : Function.Surjective (c.baseChange k) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective k hs
  have hzero : ∀ x : k ⊗[R] M, LinearMap.lTensor k ((p : R) • (LinearMap.id : M →ₗ[R] M)) x = 0 := fun x => by
    rw [LinearMap.lTensor_smul, LinearMap.lTensor_id, LinearMap.smul_apply, LinearMap.id_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      rw [TensorProduct.smul_tmul', Algebra.smul_def, map_natCast, CharP.cast_eq_zero, zero_mul, TensorProduct.zero_tmul]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  have hinj : Function.Injective (c.baseChange k) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    rw [LinearMap.baseChange_eq_ltensor] at hx
    obtain ⟨y, rfl⟩ := (hex' x).1 hx
    exact hzero y
  exact (LinearEquiv.ofBijective (c.baseChange k) ⟨hinj, hsurj⟩).finrank_eq.symm

/- English proof (translation)
Take `⟨hs, hk, -⟩` from `hc 1`. Conclude with `finrank_baseChange_eq p _ hs (fun w => (hk w).trans (by simp only [pow_one])) k`.
-/
theorem finrank_cot_one (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (GG : PDivGroup p R)
    (θ : TorsionMap A GG) (c : Pdiv.omega A →ₗ[R] GG.omega) (hc : θ.IsOmega c) (k : Type) [Field k] [Algebra R k]
    [CharP k p] : Module.finrank k (k ⊗[R] Cot R (GG.A 1)) = Module.finrank k (k ⊗[R] Pdiv.omega A) := by
  obtain ⟨hs, hk, -⟩ := hc 1
  exact finrank_baseChange_eq p _ hs (fun w => (hk w).trans (by simp only [pow_one])) k

end GlobalTheory.GroupBplus.CotRank
