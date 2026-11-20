import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeLatticeComparisonRationalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

/- English proof (translation)
Introduce `D V hStd c S J χ pres lam c0 pair del hMap hTie hJ hχ f`. Take `⟨e, -, hcoef, -, hnab, -⟩` from `hTie`. Establish `hL` using `(GlobalTheory.T.translatedStdLattice_lattice_comparison_rational D V hStd).2.2`. Establish `key : ∀ h, ∃ (z : 𝓞 D.what₂.LL) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V (pres.decG h) γE ∧ pres.ext f.1 h = c0 ((z : D.what₂.LL) • rhoVr (labLL D) lam γE (e (f.1 (pres.decC h))))`. Introduce `h`.

Take `⟨z, hz⟩` from `hχ (pres.decK h)`. Choose the witnesses or unpack the hypotheses as in `⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat V (pres.decG h) γE := by`. Take `⟨g, hg⟩` from `(pres.decG h).2`. Conclude with `⟨g, hg.2.symm⟩`. Use `⟨z, γE, hγ, ?_⟩` and prove the remaining obligations.

Establish `a1 : pres.ext f.1 h = ((χ (pres.decK h) : ℂˣ) : ℂ) • c.coef.ρ (pres.decG h) (pres.coef (f.1 (pres.decC h)))` using `rfl`. Establish `a2 : c.coef.ρ (pres.decG h) (pres.coef (f.1 (pres.decC h))) = c0 (rhoVr (labLL D) lam γE (e (f.1 (pres.decC h))))`. Rewrite using `[hcoef]`. Conclude with `(hMap.1 _ _ hγ _).symm`. Establish `a3 : c0 ((z : D.what₂.LL) • rhoVr (labLL D) lam γE (e (f.1 (pres.decC h)))) = D.what₂.embLL (z : D.what₂.LL) • c0 (rhoVr (labLL D) lam γE (e (f.1 (pres.decC h))))` using `map_smulₛₗ c0 _ _`.

Use `a1.trans ((congrArg (fun w => ((χ (pres.decK h) : ℂˣ) : ℂ) • w) a2).trans ?_)` and prove the remaining obligations. Use `Eq.trans ?_ a3.symm` and prove the remaining obligations. Conclude with `congrArg (fun s : ℂ => s • c0 (rhoVr (labLL D) lam γE (e (f.1 (pres.decC h))))) hz.symm`. Use `⟨fun h => ?_, fun hf h => ?_⟩` and prove the remaining obligations. Take `⟨z, γE, -, hv⟩` from `key h`.

Conclude with `⟨_, hv.symm⟩`. Take `⟨z, γE, hγ, hv⟩` from `key h`. Use `⟨_, ?_, hv⟩` and prove the remaining obligations. Establish `hlat : Bridge.hLat V h = (Bridge.hLat V (pres.y (pres.decC h))).map ((Matrix.mulVecLin (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).restrictScalars (𝓞 D.host.E))`. Establish `h1 : Bridge.hLat V h = Bridge.hLat V (Bridge.ratF V (pres.decG h) * pres.y (pres.decC h))` using `by conv_lhs => rw [pres.dec_spec h]`.

Conclude with `hJ _ (pres.decK h).2 _`. Rewrite using `[h1]`. Use extensionality with `x`. Simplify using `only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Use `⟨((γE⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hL _ _ hγ, Matrix.mulVec_mulVec]`. Simplify using `using hx`. Rewrite using `[Matrix.mulVec_mulVec]`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `(hL _ _ hγ _ _).1 hy`. Establish `hmem : e (f.1 (pres.decC h)) ∈ nabAtr (labLL D) lam (Bridge.hLat V (pres.y (pres.decC h)))`. Rewrite using `[← hnab]`.

Conclude with `⟨_, hf _, rfl⟩`. Establish `hga` using `Formalism.L2.Col.nabAtr_gmap (labLL D) lam ((Formalism.L2.Col.toGLm D.host.E V.rank).symm γE) (Bridge.hLat V (pres.y (pres.decC h)))`. Rewrite `hga` using `[Formalism.L2.Col.gmap_eq_map, MulEquiv.apply_symm_apply]`. Rewrite using `[hlat, hga]`. Establish `h2 : rhoVr (labLL D) lam γE (e (f.1 (pres.decC h))) ∈ (nabAtr (labLL D) lam (Bridge.hLat V (pres.y (pres.decC h)))).map ((rhoVr (labLL D) lam γE).restrictScalars (𝓞 D.what₂.LL))` using `⟨_, hmem, rfl⟩`.

Use `first`. Consider the case `exact Submodule.smul_mem _ z h2`. Consider the case `exact (algebraMap_smul D.what₂.LL z _ ▸ Submodule.smul_mem _ z h2)`. Consider the case `simpa [Algebra.smul_def] using Submodule.smul_mem _ z h2`.
-/
theorem ext_vals : ∀ (D : D7) (V : HSp D), Seed.FrmC.StdLat V → ∀ (c : CoefA V) (S : CSD D.what₂.LL) (J : Subgroup (Bridge.Gf V)) (χ : J →* ℂˣ) (pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ J χ) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair del, Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → Bridge.CoefTie V c.coef pres lam c0 pair (nabAtr (labLL D) lam) del → (∀ k ∈ J, ∀ h, Bridge.hLat V (h * k) = Bridge.hLat V h) → (∀ k : J, ∃ z : 𝓞 D.what₂.LL, D.what₂.embLL (z : D.what₂.LL) = (χ k : ℂ)) → ∀ f : S.Forms, (∀ h, pres.ext f.1 h ∈ Set.range c0) ∧ ((∀ a, f.1 a ∈ S.Nab a) → ∀ h, ∃ v ∈ nabAtr (labLL D) lam (Bridge.hLat V h), pres.ext f.1 h = c0 v) := by
  intro D V hStd c S J χ pres lam c0 pair del hMap hTie hJ hχ f
  obtain ⟨e, -, hcoef, -, hnab, -⟩ := hTie
  have hL := (GlobalTheory.T.translatedStdLattice_lattice_comparison_rational D V hStd).2.2
  have key : ∀ h, ∃ (z : 𝓞 D.what₂.LL) (γE : GL (Fin V.rank) D.host.E),
      Bridge.IsRatMat V (pres.decG h) γE ∧
      pres.ext f.1 h = c0 ((z : D.what₂.LL) • rhoVr (labLL D) lam γE (e (f.1 (pres.decC h)))) := by
    intro h
    obtain ⟨z, hz⟩ := hχ (pres.decK h)
    obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat V (pres.decG h) γE := by
      obtain ⟨g, hg⟩ := (pres.decG h).2
      exact ⟨g, hg.2.symm⟩
    refine ⟨z, γE, hγ, ?_⟩
    have a1 : pres.ext f.1 h = ((χ (pres.decK h) : ℂˣ) : ℂ) • c.coef.ρ (pres.decG h) (pres.coef (f.1 (pres.decC h))) := rfl
    have a2 : c.coef.ρ (pres.decG h) (pres.coef (f.1 (pres.decC h))) =
        c0 (rhoVr (labLL D) lam γE (e (f.1 (pres.decC h)))) := by
      rw [hcoef]; exact (hMap.1 _ _ hγ _).symm
    have a3 : c0 ((z : D.what₂.LL) • rhoVr (labLL D) lam γE (e (f.1 (pres.decC h)))) =
        D.what₂.embLL (z : D.what₂.LL) • c0 (rhoVr (labLL D) lam γE (e (f.1 (pres.decC h)))) :=
      map_smulₛₗ c0 _ _
    refine a1.trans ((congrArg (fun w => ((χ (pres.decK h) : ℂˣ) : ℂ) • w) a2).trans ?_)
    refine Eq.trans ?_ a3.symm
    exact congrArg (fun s : ℂ => s • c0 (rhoVr (labLL D) lam γE (e (f.1 (pres.decC h))))) hz.symm
  refine ⟨fun h => ?_, fun hf h => ?_⟩
  · obtain ⟨z, γE, -, hv⟩ := key h
    exact ⟨_, hv.symm⟩
  obtain ⟨z, γE, hγ, hv⟩ := key h
  refine ⟨_, ?_, hv⟩

  have hlat : Bridge.hLat V h = (Bridge.hLat V (pres.y (pres.decC h))).map
      ((Matrix.mulVecLin (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).restrictScalars (𝓞 D.host.E)) := by
    have h1 : Bridge.hLat V h = Bridge.hLat V (Bridge.ratF V (pres.decG h) * pres.y (pres.decC h)) := by
      conv_lhs => rw [pres.dec_spec h]
      exact hJ _ (pres.decK h).2 _
    rw [h1]
    ext x
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
    constructor
    · intro hx
      refine ⟨((γE⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x, ?_, ?_⟩
      · rw [hL _ _ hγ, Matrix.mulVec_mulVec]
        simpa using hx
      · rw [Matrix.mulVec_mulVec]
        simp
    · rintro ⟨y, hy, rfl⟩
      exact (hL _ _ hγ _ _).1 hy
  have hmem : e (f.1 (pres.decC h)) ∈ nabAtr (labLL D) lam (Bridge.hLat V (pres.y (pres.decC h))) := by
    rw [← hnab]
    exact ⟨_, hf _, rfl⟩
  have hga := Formalism.L2.Col.nabAtr_gmap (labLL D) lam ((Formalism.L2.Col.toGLm D.host.E V.rank).symm γE)
    (Bridge.hLat V (pres.y (pres.decC h)))
  rw [Formalism.L2.Col.gmap_eq_map, MulEquiv.apply_symm_apply] at hga
  rw [hlat, hga]
  have h2 : rhoVr (labLL D) lam γE (e (f.1 (pres.decC h))) ∈ (nabAtr (labLL D) lam (Bridge.hLat V (pres.y (pres.decC h)))).map
      ((rhoVr (labLL D) lam γE).restrictScalars (𝓞 D.what₂.LL)) := ⟨_, hmem, rfl⟩
  first
    | exact Submodule.smul_mem _ z h2
    | exact (algebraMap_smul D.what₂.LL z _ ▸ Submodule.smul_mem _ z h2)
    | simpa [Algebra.smul_def] using Submodule.smul_mem _ z h2

end GlobalTheory.MtIn
