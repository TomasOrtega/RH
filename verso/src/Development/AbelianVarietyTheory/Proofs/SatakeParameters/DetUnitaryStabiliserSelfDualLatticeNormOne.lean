import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralDetOfStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmulLatMatOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodIdealFgAndSelfDual
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain

namespace GlobalTheory.DetFields

open GlobalTheory.Mem.Col2.JetEx.VacEqPf

/- English proof (translation)
Rewrite using `[LinearEquiv.coe_det, ← LinearMap.det_toMatrix']`. Rewrite using `[show s.iE (LinearMap.toMatrix' (γ : Sp X.E n →ₗ[X.E] Sp X.E n)).det = _ from RingHom.map_det (s.iE : X.E →+* D.host.E) _]`. Use `congr 1`.
-/
theorem iE_det {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    s.iE ((LinearEquiv.det γ : X.Eˣ) : X.E) = (matOf s γ).det := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
  rw [show s.iE (LinearMap.toMatrix' (γ : Sp X.E n →ₗ[X.E] Sp X.E n)).det = _ from
    RingHom.map_det (s.iE : X.E →+* D.host.E) _]
  congr 1

/- English proof (translation)
Introduce `D X s χ hok hχ n N' hL γ hγ`. Establish `hd` using `iE_det s γ.1`. Establish `hSD : Formalism.MainNotions.StandardLatticesGL3.SD D (s.lat N')` using `hL`. Establish `hfg : (s.lat N').FG` using `hL.1`. Establish `hsp : Submodule.span D.host.E ((s.lat N' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤` using `hL.2.1`.

Establish `hU` using `matOf_unitary s hok γ`. Use `set M := matOf s γ.1 with hM`. Establish `hMM : GlobalTheory.RatEqui.adj D M * M = 1 ∧ M * GlobalTheory.RatEqui.adj D M = 1`. Use `letI := D.host.cmStar`. Establish `e : star M = GlobalTheory.RatEqui.adj D M`.

Use extensionality with `i j`. Simplify using `[GlobalTheory.RatEqui.adj, Matrix.star_apply, star_conj]`. Rewrite using `[← e]`. Conclude with `⟨Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU⟩`. Establish `hadj : M * GlobalTheory.RatEqui.adj D M = 1` using `hMM.2`.

Establish `hs : ∀ v, v ∈ s.lat N' ↔ M.mulVec v ∈ s.lat N'`. Introduce `v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Take `⟨x, hx, rfl⟩` from `(mem_lat s N' v).1 hv`.

Use `(mem_lat s N' _).2 ⟨γ.1 x, ?_, (matOf_mulVec s γ.1 x).symm⟩` and prove the remaining obligations. Rewrite using `[← hγ]`. Conclude with `⟨x, hx, rfl⟩`. Introduce `hv`. Take `⟨y, hy, hyv⟩` from `(mem_lat s N' _).1 hv`.

Rewrite `hy` using `[← hγ]`. Take `⟨x, hx, rfl⟩` from `hy`. Establish `hx' : M.mulVec (vec s x) = M.mulVec v`. Rewrite using `[← hyv]`. Conclude with `matOf_mulVec s γ.1 x`.

Establish `hinj : vec s x = v`. Use `congrArg (fun w => (GlobalTheory.RatEqui.adj D M).mulVec w) hx'` as an intermediate fact. Simplify `this` using `only [Matrix.mulVec_mulVec, hMM.1, Matrix.one_mulVec]`. Rewrite using `[← hinj]`. Conclude with `(mem_lat s N' _).2 ⟨x, hx, rfl⟩`.

Establish `hdet : M.det * D.host.conj M.det = 1`. Establish `h1 : (GlobalTheory.RatEqui.adj D M).det = D.host.conj M.det`. Unfold `GlobalTheory.RatEqui.adj`. Rewrite using `[Matrix.det_transpose]`. Conclude with `(RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) M).symm`.

Rewrite using `[← h1, ← Matrix.det_mul, hMM.2, Matrix.det_one]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Apply `s.iE.injective` to reduce the goal to its premises. Rewrite using `[map_mul, hok.2, hd, map_one]`. Conclude with `hdet`.

Establish `i1` using `GlobalTheory.DetStab.isIntegral_det_of_stable (s.lat N') hfg hsp M fun v hv => (hs v).1 hv`. Establish `i2 : IsIntegral ℤ M.det` using `isIntegral_trans (R := ℤ) _ i1`. Establish `i3` using `map_isIntegral_int s.iE.symm.toRingHom i2`. Rewrite `i3` using `[← hd]`. Simplify using `using i3`.

Rewrite using `[hd]`. Conclude with `GlobalTheory.DetStab.prod_emb_det_eq_one D χ hχ n (s.lat N') hSD M hadj hs`.
-/
theorem det_of_stab : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ), s.Ok → TaylorLogMetric.IsChi D χ → ∀ (n : ℕ) (N' : Submodule (𝓞 X.E) (Sp X.E n)), IsSDLat D.host.E n (s.lat N') → ∀ γ : UF X.E n, gmap γ.1 N' = N' → ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) * star ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 ∧ IsIntegral ℤ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ∧ ∏ τ, TaylorLogMetric.embT D τ (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) = 1 := by
  intro D X s χ hok hχ n N' hL γ hγ
  have hd := iE_det s γ.1
  have hSD : Formalism.MainNotions.StandardLatticesGL3.SD D (s.lat N') := hL
  have hfg : (s.lat N').FG := hL.1
  have hsp : Submodule.span D.host.E ((s.lat N' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := hL.2.1
  have hU := matOf_unitary s hok γ
  set M := matOf s γ.1 with hM

  have hMM : GlobalTheory.RatEqui.adj D M * M = 1 ∧ M * GlobalTheory.RatEqui.adj D M = 1 := by
    letI := D.host.cmStar
    have e : star M = GlobalTheory.RatEqui.adj D M := by
      ext i j
      simp [GlobalTheory.RatEqui.adj, Matrix.star_apply, star_conj]
    rw [← e]
    exact ⟨Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU⟩
  have hadj : M * GlobalTheory.RatEqui.adj D M = 1 := hMM.2

  have hs : ∀ v, v ∈ s.lat N' ↔ M.mulVec v ∈ s.lat N' := by
    intro v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := (mem_lat s N' v).1 hv
      refine (mem_lat s N' _).2 ⟨γ.1 x, ?_, (matOf_mulVec s γ.1 x).symm⟩
      rw [← hγ]
      exact ⟨x, hx, rfl⟩
    · intro hv
      obtain ⟨y, hy, hyv⟩ := (mem_lat s N' _).1 hv
      rw [← hγ] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hx' : M.mulVec (vec s x) = M.mulVec v := by
        rw [← hyv]
        exact matOf_mulVec s γ.1 x
      have hinj : vec s x = v := by
        have := congrArg (fun w => (GlobalTheory.RatEqui.adj D M).mulVec w) hx'
        simpa only [Matrix.mulVec_mulVec, hMM.1, Matrix.one_mulVec] using this
      rw [← hinj]
      exact (mem_lat s N' _).2 ⟨x, hx, rfl⟩

  have hdet : M.det * D.host.conj M.det = 1 := by
    have h1 : (GlobalTheory.RatEqui.adj D M).det = D.host.conj M.det := by
      unfold GlobalTheory.RatEqui.adj
      rw [Matrix.det_transpose]
      exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) M).symm
    rw [← h1, ← Matrix.det_mul, hMM.2, Matrix.det_one]
  refine ⟨?_, ?_, ?_⟩
  · apply s.iE.injective
    rw [map_mul, hok.2, hd, map_one]
    exact hdet
  · have i1 := GlobalTheory.DetStab.isIntegral_det_of_stable (s.lat N') hfg hsp M fun v hv => (hs v).1 hv
    have i2 : IsIntegral ℤ M.det := isIntegral_trans (R := ℤ) _ i1
    have i3 := map_isIntegral_int s.iE.symm.toRingHom i2
    rw [← hd] at i3
    simpa using i3
  · rw [hd]
    exact GlobalTheory.DetStab.prod_emb_det_eq_one D χ hχ n (s.lat N') hSD M hadj hs

end GlobalTheory.DetFields
