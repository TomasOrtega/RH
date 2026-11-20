import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.StdCharWeilDatum

section Char

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Introduce `u hu`. Establish `h1 : u.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)`. Use `show (u.1 * x, u.2 * 0) = ((0 : Ainf F), (0 : Af F))`. Rewrite using `[h1, zero_mul, mul_zero]`.
-/
theorem at_pairA (x : Ainf F) : At (evI F) (pairA F x 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * x, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
  rw [h1, zero_mul, mul_zero]

/- English proof (translation)
The claim follows from `hψ.2.2 _ (at_pairA x)`.
-/
theorem psi_pairA {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : Ainf F) :
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
theorem norm_psi_inf {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : Ainf F) : ‖ψ (pairA F x 0)‖ = 1 := by
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
theorem norm_psi_fin {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (y : Af F) : ‖ψ (pairA F 0 y)‖ = 1 := by
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
theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  rw [pairA_split x, AddChar.map_add_eq_mul, norm_mul, norm_psi_inf hψ, norm_psi_fin hψ, one_mul]

/- English proof (translation)
Use `set n : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)`. Establish `hn : 0 < n` using `Module.finrank_pos`. Use `set t : ℝ := 1 / (2 * n)`. Use `⟨pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t)) 0, ?_⟩` and prove the remaining obligations. Rewrite using `[psi_pairA hψ, RingEquiv.apply_symm_apply, Algebra.trace_algebraMap]`.

Establish `hn' : (n : ℝ) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `eR : (n • t : ℝ) = 1 / 2`. Rewrite using `[nsmul_eq_mul]`. Simplify using `only [t]`. Rewrite using `[mul_one_div, div_eq_div_iff (by positivity) two_ne_zero]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e : ((n • t : ℝ) : ℂ) = 1 / 2`. Rewrite using `[eR]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Establish `: -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I)` using `by ring`. Rewrite using `[this, Complex.exp_neg, Complex.exp_pi_mul_I]`. Evaluate the numerical expressions.
-/
theorem exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : ∃ x, ψ x ≠ 1 := by
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
theorem isCharAF {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : IsCharAF F ψ :=
  ⟨hψ.1, norm_psi hψ, hψ.2.1, exists_ne_one hψ⟩

end Char

section Trace

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite using `[Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]`. Simplify using `only [Algebra.trace_complex_apply]`. Rewrite using `[← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => w.IsReal)]`. Use `congr 1`. Use `Fintype.sum_congr _ _ fun w => ?_` and prove the remaining obligations.

Rewrite using `[InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2, Complex.ofReal_re]`. Simplify using the standard rewrite rules. Use `Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _ fun w => ?_` and prove the remaining obligations. Establish `h` using `InfinitePlace.mult_isComplex ⟨w.1, InfinitePlace.not_isReal_iff_isComplex.1 w.2⟩`. Simplify using `only at h`.

Rewrite using `[h]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem sum_eq_trace (x : Ainf F) :
    ∑ v : InfinitePlace F, (v.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding v (x v)).re =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [Algebra.trace_complex_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => w.IsReal)]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2,
      Complex.ofReal_re]
    simp
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _ fun w => ?_
    have h := InfinitePlace.mult_isComplex ⟨w.1, InfinitePlace.not_isReal_iff_isComplex.1 w.2⟩
    simp only at h
    rw [h]
    push_cast
    rfl

end Trace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Rewrite using `[← sum_eq_trace]`. Use `push_cast`. Use `Fintype.sum_congr _ _ fun w => ?_` and prove the remaining obligations. Establish `hv : w.IsReal` using `IsTotallyReal.isReal w`. Rewrite using `[GlobalTheory.DualPairCompare.gen_inf_val (B.emb w).1 w (B.emb w).2.symm (θ w) (hθ w) x, InfinitePlace.mult_isReal ⟨_, hv⟩, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv, Complex.ofReal_re]`.

Simplify using the standard rewrite rules.
-/
theorem sum_infFam [IsTotallyReal F] (B : Base F E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ))
    (hθ : Formalism.IndefR.DatumF.IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ) (x : Ainf F) :
    ∑ w, θ w (x ⊗ₜ[F] (1 : E)) =
      ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ) : ℂ) := by
  rw [← sum_eq_trace]
  push_cast
  refine Fintype.sum_congr _ _ fun w => ?_
  have hv : w.IsReal := IsTotallyReal.isReal w
  rw [GlobalTheory.DualPairCompare.gen_inf_val (B.emb w).1 w (B.emb w).2.symm (θ w) (hθ w) x,
    InfinitePlace.mult_isReal ⟨_, hv⟩, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv,
    Complex.ofReal_re]
  simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB`. Use `haveI : IsTotallyReal F := hB.cm.1`. Use `⟨isCharAF hB.std, ⟨?_, fun θ hθ x => ?_⟩⟩` and prove the remaining obligations. Use `choose θ hθ using fun w : InfinitePlace F => GlobalTheory.DualPairCompare.gen_inf_exists (B.emb w).1 w (B.emb w).2.symm`. Conclude with `⟨θ, hθ⟩`.

Use `show B.ψ (pairA F x 0) = _`. Rewrite using `[psi_pairA hB.std, sum_infFam B θ hθ x]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isStdCharF_of_isGood : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsTotallyReal F := hB.cm.1
  refine ⟨isCharAF hB.std, ⟨?_, fun θ hθ x => ?_⟩⟩
  · choose θ hθ using fun w : InfinitePlace F =>
      GlobalTheory.DualPairCompare.gen_inf_exists (B.emb w).1 w (B.emb w).2.symm
    exact ⟨θ, hθ⟩
  · show B.ψ (pairA F x 0) = _
    rw [psi_pairA hB.std, sum_infFam B θ hθ x]
    congr 1
    push_cast
    ring

end GlobalTheory.StdCharWeilDatum

end
