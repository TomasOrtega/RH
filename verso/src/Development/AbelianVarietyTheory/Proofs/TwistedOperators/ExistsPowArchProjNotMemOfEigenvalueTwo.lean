import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

namespace GlobalTheory.Twist

open scoped TensorProduct Matrix

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D V g x hx hg w K hK`. Use `set c : Fin V.rank → D.host.E := ⇑(V.frame.repr x) with hc_def`. Establish `hM : (g.1.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ c = (2 : D.host.E) • c`. Establish `h1` using `congrArg (fun y => ⇑(V.frame.repr y)) hg`. Simplify using `only [GlobalTheory.Cusp.ratAct, map_smul, Finsupp.coe_smul] at h1`.

Rewrite `h1` using `[← LinearMap.toMatrix_mulVec_repr V.frame V.frame, LinearMap.toMatrix_toLin]`. Conclude with `h1`. Establish `hMn : ∀ n : ℕ, ((g ^ n).1.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ c = (2 : D.host.E) ^ n • c`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, c j ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Apply `hx` to reduce the goal to its premises. Establish `: V.frame.repr x = 0` using `Finsupp.ext h`. Simplify using `using this`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual D.host.F D.host.E, φ (c j) ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hj ((Module.forall_dual_apply_eq_zero_iff _ _).1 h)`. Set `ι : D.host.E →+* w.Completion ⊗[D.host.F] D.host.E` to `inclR (F := D.host.F) w.Completion`. Set `Λ : w.Completion ⊗[D.host.F] D.host.E →ₗ[w.Completion] w.Completion` to `(TensorProduct.AlgebraTensorModule.rid D.host.F w.Completion w.Completion).toLinearMap ∘ₗ TensorProduct.AlgebraTensorModule.map LinearMap.id φ`.

Establish `hΛ1 : ∀ e : D.host.E, Λ (ι e) = algebraMap D.host.F w.Completion (φ e)`. Introduce `e`. Simplify using `[Λ, ι, inclR, Algebra.algebraMap_eq_smul_one]`. Establish `: IsModuleTopology w.Completion (w.Completion ⊗[D.host.F] D.host.E)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (w.Completion ⊗[D.host.F] D.host.E)` using `IsModuleTopology.isTopologicalRing w.Completion _`.

Establish `hΛ : Continuous Λ` using `IsModuleTopology.continuous_of_linearMap Λ`. Set `f : GArch D.sp.cm.sig V.gram w → w.Completion` to `fun h => Λ (((matHom _ D.sp.cm.sig V.gram h).val *ᵥ (fun i => ι (c i))) j)`. Establish `hm : Continuous fun h : GArch D.sp.cm.sig V.gram w => (matHom _ D.sp.cm.sig V.gram h).val` using `Units.continuous_val.comp (isEmbedding_matHom _ _ _).continuous`. Establish `hf : Continuous f` using `hΛ.comp ((continuous_apply j).comp (hm.matrix_mulVec continuous_const))`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hf.continuousOn`.

Establish `he : ∀ γ : GF V, (matHom _ D.sp.cm.sig V.gram (ratArch D.sp.cm.sig V.gram w γ)).val = (γ.1.1).map ι` using `fun γ => rfl`. Establish `hval : ∀ n : ℕ, f (ratArch D.sp.cm.sig V.gram w (g ^ n : GF V)) = algebraMap D.host.F w.Completion ((2 : D.host.F) ^ n * φ (c j))`. Introduce `n`. Establish `e1 : (matHom _ D.sp.cm.sig V.gram (ratArch D.sp.cm.sig V.gram w (g ^ n : GF V))).val = ((g ^ n).1.1).map ι` using `he (g ^ n)`. Simplify using `only [f]`.

Rewrite using `[e1, show (fun i => ι (c i)) = ⇑ι ∘ c from rfl, ← RingHom.map_mulVec, hMn n, Pi.smul_apply, smul_eq_mul, hΛ1]`. Use `congr 1`. Rewrite using `[show (2 : D.host.E) ^ n * c j = ((2 : D.host.F) ^ n) • c j by rw [Algebra.smul_def, map_pow, map_ofNat], map_smul, smul_eq_mul]`. Establish `hnorm : ∀ a : D.host.F, ‖algebraMap D.host.F w.Completion a‖ = w a` using `fun a => by`. Rewrite using `[show algebraMap D.host.F w.Completion a = ((a : D.host.F) : w.Completion) from rfl]`.

Simplify using `only [InfinitePlace.Completion.norm_ofCompletion, UniformSpace.Completion.norm_coe]`. Both sides reduce to the same expression. Establish `hpos : 0 < w (φ (c j))` using `(InfinitePlace.pos_iff).2 hφ`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (C / w (φ (c j))) (by norm_num : (1 : ℝ) < 2)`. Use `⟨n, fun hmem => ?_⟩` and prove the remaining obligations.

Rewrite `hmem` using `[show projArch D.sp.cm.sig V.gram w (rat V (g ^ n)) = ratArch D.sp.cm.sig V.gram w (g ^ n : GF V) from projArch_ratEmb _ _ w _]`. Establish `h1` using `hC _ hmem`. Rewrite `h1` using `[hval, hnorm, map_mul, map_pow]`. Establish `h2 : w (2 : D.host.F) = 2`. Rewrite using `[← InfinitePlace.norm_embedding_eq, map_ofNat]`.

Evaluate the numerical expressions. Rewrite `h1` using `[h2]`. Rewrite `hn` using `[div_lt_iff₀ hpos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_pow_projArch_not_mem_of_eigen_two : ∀ (D : D7) (V : HSp D) (g : GF V) (x : V.V), x ≠ 0 → GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E) • x → ∀ (w : InfinitePlace D.host.F) (K : Set (GArch D.sp.cm.sig V.gram w)), IsCompact K → ∃ n : ℕ, projArch D.sp.cm.sig V.gram w (rat V (g ^ n)) ∉ K := by
  intro D V g x hx hg w K hK
  classical
  set c : Fin V.rank → D.host.E := ⇑(V.frame.repr x) with hc_def
  have hM : (g.1.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ c = (2 : D.host.E) • c := by
    have h1 := congrArg (fun y => ⇑(V.frame.repr y)) hg
    simp only [GlobalTheory.Cusp.ratAct, map_smul, Finsupp.coe_smul] at h1
    rw [← LinearMap.toMatrix_mulVec_repr V.frame V.frame, LinearMap.toMatrix_toLin] at h1
    exact h1
  have hMn : ∀ n : ℕ, ((g ^ n).1.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ c = (2 : D.host.E) ^ n • c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul, ih, smul_smul,
        pow_succ, mul_comm]
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    have : V.frame.repr x = 0 := Finsupp.ext h
    simpa using this
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual D.host.F D.host.E, φ (c j) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hj ((Module.forall_dual_apply_eq_zero_iff _ _).1 h)

  let ι : D.host.E →+* w.Completion ⊗[D.host.F] D.host.E := inclR (F := D.host.F) w.Completion
  let Λ : w.Completion ⊗[D.host.F] D.host.E →ₗ[w.Completion] w.Completion :=
    (TensorProduct.AlgebraTensorModule.rid D.host.F w.Completion w.Completion).toLinearMap ∘ₗ
      TensorProduct.AlgebraTensorModule.map LinearMap.id φ
  have hΛ1 : ∀ e : D.host.E, Λ (ι e) = algebraMap D.host.F w.Completion (φ e) := by
    intro e
    simp [Λ, ι, inclR, Algebra.algebraMap_eq_smul_one]
  have : IsModuleTopology w.Completion (w.Completion ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (w.Completion ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing w.Completion _
  have hΛ : Continuous Λ := IsModuleTopology.continuous_of_linearMap Λ
  let f : GArch D.sp.cm.sig V.gram w → w.Completion := fun h =>
    Λ (((matHom _ D.sp.cm.sig V.gram h).val *ᵥ (fun i => ι (c i))) j)
  have hm : Continuous fun h : GArch D.sp.cm.sig V.gram w =>
      (matHom _ D.sp.cm.sig V.gram h).val :=
    Units.continuous_val.comp (isEmbedding_matHom _ _ _).continuous
  have hf : Continuous f := hΛ.comp ((continuous_apply j).comp (hm.matrix_mulVec continuous_const))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have he : ∀ γ : GF V, (matHom _ D.sp.cm.sig V.gram (ratArch D.sp.cm.sig V.gram w γ)).val = (γ.1.1).map ι :=
    fun γ => rfl
  have hval : ∀ n : ℕ, f (ratArch D.sp.cm.sig V.gram w (g ^ n : GF V)) =
      algebraMap D.host.F w.Completion ((2 : D.host.F) ^ n * φ (c j)) := by
    intro n
    have e1 : (matHom _ D.sp.cm.sig V.gram (ratArch D.sp.cm.sig V.gram w (g ^ n : GF V))).val = ((g ^ n).1.1).map ι := he (g ^ n)
    simp only [f]
    rw [e1, show (fun i => ι (c i)) = ⇑ι ∘ c from rfl, ← RingHom.map_mulVec, hMn n, Pi.smul_apply, smul_eq_mul, hΛ1]
    congr 1
    rw [show (2 : D.host.E) ^ n * c j = ((2 : D.host.F) ^ n) • c j by rw [Algebra.smul_def, map_pow, map_ofNat],
      map_smul, smul_eq_mul]
  have hnorm : ∀ a : D.host.F, ‖algebraMap D.host.F w.Completion a‖ = w a := fun a => by
    rw [show algebraMap D.host.F w.Completion a = ((a : D.host.F) : w.Completion) from rfl]
    simp only [InfinitePlace.Completion.norm_ofCompletion, UniformSpace.Completion.norm_coe]
    rfl
  have hpos : 0 < w (φ (c j)) := (InfinitePlace.pos_iff).2 hφ
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / w (φ (c j))) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, fun hmem => ?_⟩
  rw [show projArch D.sp.cm.sig V.gram w (rat V (g ^ n)) = ratArch D.sp.cm.sig V.gram w (g ^ n : GF V) from
    projArch_ratEmb _ _ w _] at hmem
  have h1 := hC _ hmem
  rw [hval, hnorm, map_mul, map_pow] at h1
  have h2 : w (2 : D.host.F) = 2 := by
    rw [← InfinitePlace.norm_embedding_eq, map_ofNat]; norm_num
  rw [h2] at h1
  rw [div_lt_iff₀ hpos] at hn
  linarith

end GlobalTheory.Twist
