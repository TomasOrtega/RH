import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneTmulQuotReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesLiftQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomEvalCompEqEvAMap

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.Chart

/- English proof (translation)
Use `Submodule.smul_induction_on hh (fun a ha x _ => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_smul]`. Conclude with `I.mul_mem_right _ ha`. Rewrite using `[map_add]`. Conclude with `I.add_mem hx hy`.
-/
theorem coeff_mem_of_mem_smul_top {O σ : Type} [CommRing O] (I : Ideal O)
    {h : MvPowerSeries σ O} (hh : h ∈ I • (⊤ : Submodule O (MvPowerSeries σ O))) (α : σ →₀ ℕ) :
    coeff α h ∈ I := by
  refine Submodule.smul_induction_on hh (fun a ha x _ => ?_) (fun x y hx hy => ?_)
  · rw [MvPowerSeries.coeff_smul]
    exact I.mul_mem_right _ ha
  · rw [map_add]
    exact I.add_mem hx hy

/- English proof (translation)
Introduce `p _ O _ G d c I m hm`. Establish `hp : ∀ n, ((p : (O ⧸ I) ⊗[O] G.A n)) ^ m = 0` using `fun n => by`. Establish `h0 : ((p : O ⧸ I)) ^ m = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hm`.

Rewrite using `[← map_natCast (algebraMap (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n)), ← map_pow, h0, map_zero]`. Establish `hx : ∀ n i, IsNilpotent ((1 : O ⧸ I) ⊗ₜ[O] c.x n i)` using `fun n i => by`. Take `⟨N, y, hy⟩` from `c.nil n i`. Use `⟨N * m, ?_⟩` and prove the remaining obligations. Establish `: (1 : O ⧸ I) ⊗ₜ[O] c.x n i = Algebra.TensorProduct.includeRight (R` using `O) (A := O ⧸ I) (c.x n i) := rfl`.

Rewrite using `[this, ← map_pow, pow_mul, hy, mul_pow, map_mul, map_pow, map_natCast, hp, zero_mul]`. Establish `hev : ∀ n f, evA (O ⧸ I) (fun i => (1 : O ⧸ I) ⊗ₜ[O] c.x n i) (hx n) (map (Ideal.Quotient.mk I) f) = 1 ⊗ₜ[O] c.ev n f` using `fun n f => (GlobalTheory.algHom_eval_comp_eq_evA_map p m O (G.A n) (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n) (Fin d) (c.x n) (c.ev n) (c.isEval n) (Ideal.Quotient.mk I) (Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I)).toRingHom (fun a => by`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I) (algebraMap O (G.A n) a) = _`. Rewrite using `[AlgHom.commutes]`. Conclude with `IsScalarTower.algebraMap_apply O (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n) a)`.

Use the proof step `(hp n) (hx n) f).symm`. Use `⟨hx, hev, fun n y => ?_, fun N => ?_⟩` and prove the remaining obligations. Take `⟨b, rfl⟩` from `(GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A n) I).1 y`. Take `⟨f, rfl⟩` from `c.surj n b`. Conclude with `⟨_, hev n f⟩`.

Take `⟨n, hn⟩` from `c.ker m N`. Use `⟨n, fun g hg α hα => ?_⟩` and prove the remaining obligations. Take `⟨f, rfl, -⟩` from `(GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I).1 g`. Rewrite `hg` using `[hev]`. Establish `h1 : c.ev n f ∈ I • (⊤ : Submodule O (G.A n))` using `((GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A n) I).2.1 _).1 hg`.

Establish `h2 : c.ev n f ∈ (I • (⊤ : Submodule O (MvPowerSeries (Fin d) O))).map (c.ev n).toLinearMap`. Rewrite using `[Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 (c.surj n)]`. Conclude with `h1`. Take `⟨h, hh, he⟩` from `h2`. Establish `h3 : c.ev n (f - h) = 0`.

Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `he.symm`. Establish `h4 : coeff α (f - h) ∈ I`. Take `⟨z, hz⟩` from `hn (f - h) h3 α hα`. Rewrite using `[hz]`.

Conclude with `I.mul_mem_right _ hm`. Establish `h5 : coeff α f ∈ I`. Use `I.add_mem h4 (coeff_mem_of_mem_smul_top I hh α)` as an intermediate fact. Rewrite `this` using `[map_sub, sub_add_cancel]`. Then use the resulting hypothesis. Rewrite using `[coeff_map, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `h5`.
-/
theorem presents_quotient :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
      (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I →
      ∃ hx : ∀ n i, IsNilpotent ((1 : O ⧸ I) ⊗ₜ[O] c.x n i),
        (∀ n f, evA (O ⧸ I) (fun i => (1 : O ⧸ I) ⊗ₜ[O] c.x n i) (hx n)
          (map (Ideal.Quotient.mk I) f) = 1 ⊗ₜ[O] c.ev n f) ∧
        Presents (O ⧸ I) (B := fun n => (O ⧸ I) ⊗[O] G.A n) (fun n i => 1 ⊗ₜ[O] c.x n i) hx := by
  intro p _ O _ G d c I m hm
  have hp : ∀ n, ((p : (O ⧸ I) ⊗[O] G.A n)) ^ m = 0 := fun n => by
    have h0 : ((p : O ⧸ I)) ^ m = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact hm
    rw [← map_natCast (algebraMap (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n)), ← map_pow, h0, map_zero]
  have hx : ∀ n i, IsNilpotent ((1 : O ⧸ I) ⊗ₜ[O] c.x n i) := fun n i => by
    obtain ⟨N, y, hy⟩ := c.nil n i
    refine ⟨N * m, ?_⟩
    have : (1 : O ⧸ I) ⊗ₜ[O] c.x n i = Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I)
      (c.x n i) := rfl
    rw [this, ← map_pow, pow_mul, hy, mul_pow, map_mul, map_pow, map_natCast, hp, zero_mul]
  have hev : ∀ n f, evA (O ⧸ I) (fun i => (1 : O ⧸ I) ⊗ₜ[O] c.x n i) (hx n)
      (map (Ideal.Quotient.mk I) f) = 1 ⊗ₜ[O] c.ev n f := fun n f =>
    (GlobalTheory.algHom_eval_comp_eq_evA_map p m O (G.A n) (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n) (Fin d) (c.x n) (c.ev n) (c.isEval n)
      (Ideal.Quotient.mk I)
      (Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I)).toRingHom
      (fun a => by
        change Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I) (algebraMap O (G.A n) a) = _
        rw [AlgHom.commutes]
        exact IsScalarTower.algebraMap_apply O (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n) a)
      (hp n) (hx n) f).symm
  refine ⟨hx, hev, fun n y => ?_, fun N => ?_⟩
  · obtain ⟨b, rfl⟩ := (GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A n) I).1 y
    obtain ⟨f, rfl⟩ := c.surj n b
    exact ⟨_, hev n f⟩
  · obtain ⟨n, hn⟩ := c.ker m N
    refine ⟨n, fun g hg α hα => ?_⟩
    obtain ⟨f, rfl, -⟩ := (GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I).1 g
    rw [hev] at hg
    have h1 : c.ev n f ∈ I • (⊤ : Submodule O (G.A n)) := ((GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A n) I).2.1 _).1 hg
    have h2 : c.ev n f ∈ (I • (⊤ : Submodule O (MvPowerSeries (Fin d) O))).map
        (c.ev n).toLinearMap := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 (c.surj n)]
      exact h1
    obtain ⟨h, hh, he⟩ := h2
    have h3 : c.ev n (f - h) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact he.symm
    have h4 : coeff α (f - h) ∈ I := by
      obtain ⟨z, hz⟩ := hn (f - h) h3 α hα
      rw [hz]
      exact I.mul_mem_right _ hm
    have h5 : coeff α f ∈ I := by
      have := I.add_mem h4 (coeff_mem_of_mem_smul_top I hh α)
      rwa [map_sub, sub_add_cancel] at this
    rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem]
    exact h5

end GlobalTheory.QLog.Chart
