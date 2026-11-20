import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdCharFromIsStd

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Introduce `u hu`. Establish `h1 : u.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)`. Use `show (u.1 * x, u.2 * 0) = ((0 : Ainf F), (0 : Af F))`. Rewrite using `[h1, zero_mul, mul_zero]`.
-/
theorem at_pairA (x : Ainf F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (pairA F x 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * x, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
  rw [h1, zero_mul, mul_zero]

/- English proof (translation)
The claim follows from `hψ.2.2 _ (at_pairA x)`.
-/
theorem psi_pairA {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : Ainf F) :
    ψ (pairA F x 0) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ)) :=
  hψ.2.2 _ (at_pairA x)

/- English proof (translation)
Establish `: -(2 * Real.pi * Complex.I) * (r : ℂ) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`.
-/
theorem norm_exp_real (r : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  have : -(2 * Real.pi * Complex.I) * (r : ℂ) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Rewrite using `[psi_pairA hψ]`. Conclude with `norm_exp_real _`.
-/
theorem norm_psi_inf {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : Ainf F) :
    ‖ψ (pairA F x 0)‖ = 1 := by
  rw [psi_pairA hψ]; exact norm_exp_real _

/- English proof (translation)
Use `show x = ((x.1 + 0 : Ainf F), (0 + x.2 : Af F))`. Rewrite using `[add_zero, zero_add]`. Both sides reduce to the same expression.
-/
theorem pairA_split (x : AF F) : x = pairA F x.1 0 + pairA F 0 x.2 := by
  show x = ((x.1 + 0 : Ainf F), (0 + x.2 : Af F))
  rw [add_zero, zero_add]
  rfl

/- English proof (translation)
Establish `hc : Continuous fun y : Af F => ‖ψ (pairA F 0 y)‖` using `(hψ.1.comp (continuous_const.prodMk continuous_id)).norm`. Establish `hcl : IsClosed {y : Af F | ‖ψ (pairA F 0 y)‖ = 1}` using `isClosed_eq hc continuous_const`. Establish `hrange : Set.range (algebraMap F (Af F)) ⊆ {y : Af F | ‖ψ (pairA F 0 y)‖ = 1}`. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `h1` using `hψ.2.1 a`.

Rewrite `h1` using `[GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul]`. Establish `h2` using `congrArg norm h1`. Rewrite `h2` using `[norm_mul, norm_psi_inf hψ, one_mul, norm_one]`. Conclude with `h2`. Use `hcl.closure_subset_iff.2 hrange` as an intermediate fact.

Rewrite `this` using `[GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range]`. Conclude with `this (Set.mem_univ y)`.
-/
theorem norm_psi_fin {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (y : Af F) :
    ‖ψ (pairA F 0 y)‖ = 1 := by
  have hc : Continuous fun y : Af F => ‖ψ (pairA F 0 y)‖ :=
    (hψ.1.comp (continuous_const.prodMk continuous_id)).norm
  have hcl : IsClosed {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := isClosed_eq hc continuous_const
  have hrange : Set.range (algebraMap F (Af F)) ⊆ {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_psi_inf hψ, one_mul, norm_one] at h2
    exact h2
  have := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at this
  exact this (Set.mem_univ y)

/- English proof (translation)
Rewrite using `[pairA_split x, AddChar.map_add_eq_mul, norm_mul, norm_psi_inf hψ, norm_psi_fin hψ, one_mul]`.
-/
theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  rw [pairA_split x, AddChar.map_add_eq_mul, norm_mul, norm_psi_inf hψ, norm_psi_fin hψ, one_mul]

/- English proof (translation)
Use `set n : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)`. Establish `hn : 0 < n` using `Module.finrank_pos`. Use `set t : ℝ := 1 / (2 * n)`. Use `⟨pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t)) 0, ?_⟩` and prove the remaining obligations. Rewrite using `[psi_pairA hψ, RingEquiv.apply_symm_apply, Algebra.trace_algebraMap]`.

Establish `hn' : (n : ℝ) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `eR : (n • t : ℝ) = 1 / 2`. Rewrite using `[nsmul_eq_mul]`. Simplify using `only [t]`. Rewrite using `[mul_one_div, div_eq_div_iff (by positivity) two_ne_zero]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e : ((n • t : ℝ) : ℂ) = 1 / 2`. Rewrite using `[eR]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Establish `: -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I)` using `by ring`. Rewrite using `[this, Complex.exp_neg, Complex.exp_pi_mul_I]`. Evaluate the numerical expressions.
-/
theorem exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : ∃ x, ψ x ≠ 1 := by
  set n : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)
  have hn : 0 < n := Module.finrank_pos
  set t : ℝ := 1 / (2 * n)
  refine ⟨pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t)) 0, ?_⟩
  rw [psi_pairA hψ, RingEquiv.apply_symm_apply, Algebra.trace_algebraMap]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have eR : (n • t : ℝ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    simp only [t]
    rw [mul_one_div, div_eq_div_iff (by positivity) two_ne_zero]
    ring
  have e : ((n • t : ℝ) : ℂ) = 1 / 2 := by
    rw [eR]; push_cast; ring
  rw [e]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/- English proof (translation)
Assemble the required witnesses or components as `⟨hψ.1, norm_psi hψ, hψ.2.1, exists_ne_one hψ⟩`.
-/
theorem isCharAF {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : IsCharAF F ψ :=
  ⟨hψ.1, norm_psi hψ, hψ.2.1, exists_ne_one hψ⟩

end GlobalTheory.StdCharFromIsStd

namespace GlobalTheory.StdCharFromIsStd

/- English proof (translation)
Introduce `D ψ hψ`. Use `⟨isCharAF hψ, GlobalTheory.DualPairCompare.exists_infFam D, fun θ hθ x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ψ (pairA D.host.F x 0) = _`. Rewrite using `[psi_pairA hψ, GlobalTheory.DualPairCompare.sum_infFam θ hθ, GlobalTheory.BaseGoodPlace.trInf_eq_trace]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isStdChar_of_isStd : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsStdChar D ψ (-1) := by
  intro D ψ hψ
  refine ⟨isCharAF hψ, GlobalTheory.DualPairCompare.exists_infFam D, fun θ hθ x => ?_⟩
  change ψ (pairA D.host.F x 0) = _
  rw [psi_pairA hψ, GlobalTheory.DualPairCompare.sum_infFam θ hθ, GlobalTheory.BaseGoodPlace.trInf_eq_trace]
  congr 1
  push_cast
  ring

end GlobalTheory.StdCharFromIsStd
