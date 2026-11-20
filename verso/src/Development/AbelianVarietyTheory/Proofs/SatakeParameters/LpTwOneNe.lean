import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTheRecOfIsRec
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedGaloisRepNarrow2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnlinkedGLOutright
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.TheRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Take `⟨n, a, rfl⟩` from `WD.exists_rep x`. Introduce `hn heq`. Rewrite `heq` using `[WD.lpTw_mk, WD.mk_eq_mk]`. Take `⟨e, he, -⟩` from `heq`. Rewrite `hn` using `[WD.lpDim_mk, Module.finrank_fin_fun]`.

Use `set σ := frob h`. Use `set T := (a.tw 1).ρ σ`. Use `set B := a.ρ σ`. Establish `hconj : (e : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ T ∘ₗ (e.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = B`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Use `show e ((a.tw 1).ρ σ (e.symm v)) = a.ρ σ v`. Rewrite using `[he, LinearEquiv.apply_symm_apply]`. Establish `hdet : LinearMap.det T = LinearMap.det B`. Rewrite using `[← hconj, LinearMap.det_conj]`. Establish `hT : T = ((normV w : ℕ) : ℂ) • B` using `by show (a.tw 1).ρ σ = _`.

Rewrite using `[WDRep.tw_ρ, deg_frob]`. Simplify using `only [Complex.ofReal_one, Complex.cpow_one, zpow_one]`. Both sides reduce to the same expression. Rewrite `hdet` using `[hT, LinearMap.det_smul, Module.finrank_fin_fun]`. Establish `hB : LinearMap.det B ≠ 0`.

Introduce `h0`. Establish `h1 : B * a.ρ σ⁻¹ = 1` using `by show a.ρ σ * a.ρ σ⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Use `congrArg LinearMap.det h1` as an intermediate fact. Rewrite `this` using `[map_mul, h0, zero_mul, map_one]`.

Conclude with `zero_ne_one this`. Establish `hq : ((normV w : ℕ) : ℂ) ^ n = 1`. Use `mul_right_cancel₀ hB (hdet.trans (one_mul _).symm)` as an intermediate fact. Conclude with `this`. Establish `hq' : (normV w : ℕ) ^ n = 1` using `by exact_mod_cast hq`.

Establish `h1q` using `one_lt_normV w`. Establish `: 1 < (normV w : ℕ) ^ n` using `Nat.one_lt_pow hn.ne' h1q`. Use linear arithmetic over natural numbers and integers.
-/
theorem WeilDeligne.WD.lpTw_one_ne {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (x : WD h) : 0 < x.lpDim → x.lpTw 1 ≠ x := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  intro hn heq
  rw [WD.lpTw_mk, WD.mk_eq_mk] at heq
  obtain ⟨e, he, -⟩ := heq
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hn
  set σ := frob h
  set T := (a.tw 1).ρ σ
  set B := a.ρ σ
  have hconj : (e : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ T ∘ₗ (e.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = B := by
    refine LinearMap.ext fun v => ?_
    show e ((a.tw 1).ρ σ (e.symm v)) = a.ρ σ v
    rw [he, LinearEquiv.apply_symm_apply]
  have hdet : LinearMap.det T = LinearMap.det B := by
    rw [← hconj, LinearMap.det_conj]
  have hT : T = ((normV w : ℕ) : ℂ) • B := by
    show (a.tw 1).ρ σ = _
    rw [WDRep.tw_ρ, deg_frob]
    simp only [Complex.ofReal_one, Complex.cpow_one, zpow_one]
    rfl
  rw [hT, LinearMap.det_smul, Module.finrank_fin_fun] at hdet
  have hB : LinearMap.det B ≠ 0 := by
    intro h0
    have h1 : B * a.ρ σ⁻¹ = 1 := by
      show a.ρ σ * a.ρ σ⁻¹ = 1
      rw [← map_mul, mul_inv_cancel, map_one]
    have := congrArg LinearMap.det h1
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have hq : ((normV w : ℕ) : ℂ) ^ n = 1 := by
    have := mul_right_cancel₀ hB (hdet.trans (one_mul _).symm)
    exact this
  have hq' : (normV w : ℕ) ^ n = 1 := by exact_mod_cast hq
  have h1q := one_lt_normV w
  have : 1 < (normV w : ℕ) ^ n := Nat.one_lt_pow hn.ne' h1q
  omega

end GlobalTheory
