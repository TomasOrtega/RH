import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEmbExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.La1sqEqOfUnXEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChange
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.CuspFieldChange

open GlobalTheory.FieldBC GlobalTheory.SecFieldChange
open GlobalTheory.CoefChangeCompare (ValueWD HasBC hasBC_of evR_of_map)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

variable {c c₀ : Coeff l} (hle : c₀.F ≤ c.F)

/- English proof (translation)
Use function extensionality and compare the values at `q y`. Use `letI := resAlg hle q.R`. Rewrite using `[val_of_isBC hle hf'.1 h q (fun _ => rfl) y, Finset.sum_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.smul_def]`.

Both sides reduce to the same expression.
-/
theorem eq_sum_of_isBC {m : ℕ} {f' : Rul Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hf' : f' ∈ sec Xo c a n)
    {as : Fin m → c.F} {fs : Fin m → Rul Xo c₀} (h : IsBC hle f' as fs) : f' = ∑ i, as i • rulBC hle (fs i) := by
  funext q y
  letI := resAlg hle q.R
  rw [val_of_isBC hle hf'.1 h q (fun _ => rfl) y, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.smul_def]
  rfl

/- English proof (translation)
Use `le_antisymm (fun f' hf' => ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Take `⟨m, as, fs, hfs, h⟩` from `cuspBC_holds hle U a n f' hf'`. Rewrite using `[eq_sum_of_isBC hle (cusp_le_sec _ _ _ _ _ hf') h]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hfs i, rfl⟩)`. Introduce and unpack `_ ⟨f, hf, rfl⟩`.

Conclude with `(rulBC_cusp E H Dw l Xo c₀ c hle r U a n f (cusp_le_sec _ _ _ _ _ hf)).2.2 hf`.
-/
theorem cusp_unfBC_eq_span {r : ℕ} (U : ∀ σ : c₀.F →+* ℂ, Unf Xo c₀ σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    cusp Xo c (unfBC hle U) a n = Submodule.span c.F (rulBC hle '' (cusp Xo c₀ U a n : Set (Rul Xo c₀))) := by
  refine le_antisymm (fun f' hf' => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨m, as, fs, hfs, h⟩ := cuspBC_holds hle U a n f' hf'
    rw [eq_sum_of_isBC hle (cusp_le_sec _ _ _ _ _ hf') h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hfs i, rfl⟩)
  · rintro _ ⟨f, hf, rfl⟩
    exact (rulBC_cusp E H Dw l Xo c₀ c hle r U a n f (cusp_le_sec _ _ _ _ _ hf)).2.2 hf

/- English proof (translation)
Establish `hS` using `GlobalTheory.abelianSchemeLaws_all.1.secBaseChange`. Establish `hWD : ValueWD Xo c₀` using `evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c₀))`. Establish `hBC : HasBC Xo c₀` using `hasBC_of hS`. Use `letI alg : Algebra c₀.F c.F := (incF c₀ c hle).toAlgebra`. Rewrite `hi`, the goal using `[Fintype.linearIndependent_iff]`.

Introduce `g hg i`. Use `(Module.forall_dual_apply_eq_zero_iff c₀.F (g i)).1 fun lam => ?_` and prove the remaining obligations. Use `hi (fun j => lam (g j)) ?_ i` and prove the remaining obligations. Use function extensionality and compare the values at `p y`. Establish `hov : AlgOver c₀ c hle (Ext c₀.F c.F p.R)` using `fun x => ext_tower x`.

Take `⟨z, hz⟩` from `hBC p.R (Ext c₀.F c.F p.R) (inR c.F p.R) y`. Establish `h1` using `evR_sum_smul (z.ext hle hov) g (fun i => rulBC hle (v i))`. Establish `h0 : evR Xo c (0 : Rul Xo c) (z.ext hle hov) = 0` using `evalAt_zero _ _ _`. Rewrite `h1` using `[hg, h0]`. Establish `h2 : ∀ j, evR Xo c (rulBC hle (v j)) (z.ext hle hov) = inR c.F p.R (v j p y)` using `fun j => by`.

Rewrite using `[((rulBC_sec_val_linear E H Dw l Xo c₀ c hle).1 a n _ (hv j)).2 _ hov, FrPt.res_ext, evR_of_map hWD (hv j).1 hz]`. Simplify using `only [h2] at h1`. Establish `h3 : ∀ j, algebraMap c.F (Ext c₀.F c.F p.R) (g j) * inR c.F p.R (v j p y) = (TensorProduct.tmul c₀.F (g j) (v j p y) : TensorProduct c₀.F c.F p.R)` using `fun j => by show (TensorProduct.tmul c₀.F (g j) (1 : p.R) * TensorProduct.tmul c₀.F (1 : c.F) (v j p y) : TensorProduct c₀.F c.F p.R) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Establish `h4 : (0 : TensorProduct c₀.F c.F p.R) = ∑ j, TensorProduct.tmul c₀.F (g j) (v j p y)` using `h1.trans (Finset.sum_congr rfl fun j _ => h3 j)`.

Establish `h5` using `congrArg (coord lam p.R) h4`. Rewrite `h5` using `[map_zero, map_sum]`. Simplify using `only [coord_tmul] at h5`. Rewrite using `[Finset.sum_apply, Finset.sum_apply]`. Conclude with `h5.symm`.
-/
theorem linearIndependent_rulBC {a : (E →+* ℂ) × ℕ → ℕ} {n m : ℕ} {v : Fin m → Rul Xo c₀}
    (hv : ∀ i, v i ∈ sec Xo c₀ a n) (hi : LinearIndependent c₀.F v) :
    LinearIndependent c.F (fun i => rulBC hle (v i)) := by
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : ValueWD Xo c₀ :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c₀))
  have hBC : HasBC Xo c₀ := hasBC_of hS
  letI alg : Algebra c₀.F c.F := (incF c₀ c hle).toAlgebra
  rw [Fintype.linearIndependent_iff] at hi ⊢
  intro g hg i
  refine (Module.forall_dual_apply_eq_zero_iff c₀.F (g i)).1 fun lam => ?_
  refine hi (fun j => lam (g j)) ?_ i
  funext p y
  have hov : AlgOver c₀ c hle (Ext c₀.F c.F p.R) := fun x => ext_tower x
  obtain ⟨z, hz⟩ := hBC p.R (Ext c₀.F c.F p.R) (inR c.F p.R) y
  have h1 := evR_sum_smul (z.ext hle hov) g (fun i => rulBC hle (v i))
  have h0 : evR Xo c (0 : Rul Xo c) (z.ext hle hov) = 0 := evalAt_zero _ _ _
  rw [hg, h0] at h1
  have h2 : ∀ j, evR Xo c (rulBC hle (v j)) (z.ext hle hov) = inR c.F p.R (v j p y) := fun j => by
    rw [((rulBC_sec_val_linear E H Dw l Xo c₀ c hle).1 a n _ (hv j)).2 _ hov, FrPt.res_ext,
      evR_of_map hWD (hv j).1 hz]
  simp only [h2] at h1
  have h3 : ∀ j, algebraMap c.F (Ext c₀.F c.F p.R) (g j) * inR c.F p.R (v j p y) =
      (TensorProduct.tmul c₀.F (g j) (v j p y) : TensorProduct c₀.F c.F p.R) := fun j => by
    show (TensorProduct.tmul c₀.F (g j) (1 : p.R) * TensorProduct.tmul c₀.F (1 : c.F) (v j p y) :
      TensorProduct c₀.F c.F p.R) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h4 : (0 : TensorProduct c₀.F c.F p.R) = ∑ j, TensorProduct.tmul c₀.F (g j) (v j p y) :=
    h1.trans (Finset.sum_congr rfl fun j _ => h3 j)
  have h5 := congrArg (coord lam p.R) h4
  rw [map_zero, map_sum] at h5
  simp only [coord_tmul] at h5
  rw [Finset.sum_apply, Finset.sum_apply]
  exact h5.symm

end GlobalTheory.CuspFieldChange
