import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NormEmbeddingHostFormConstantEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicLawsModuliSchemeGoodLevel
import Formalism.LocalToGlobal.Divisibility.FramesLemmas

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.abelian₂.LamModel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.NormVectorIdentities.Items Formalism.L2.DIV
open scoped Matrix ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `h0 : GoodEmb c (goodOf c c.F.val.toRingHom)` using `goodEmb_goodOf c _`. Establish `hF : CuspFD Xo c U` using `(Formalism.L2.PjFree.cuspFD_ofPj U).1 (GlobalTheory.cuspForms_finiteDimensional_of_isUnf GlobalTheory.firstFiveLaws.1.secBaseChange _ H Dw l Xo c _ (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) _ h0 ((Formalism.L2.PjFree.isUnf_ofPj (U _)).2 (h.unf _ h0)))`. Use `haveI := hF a n hd`. Use `haveI : Module.Free c.F (cusp Xo c U a n) := Module.Free.of_divisionRing _ _`. Conclude with `⟨_, ⟨Module.finBasis c.F _⟩⟩`.
-/
theorem exists_basis {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r} {V : HSp D}
    {dict : ∀ σ : c.F →+* ℂ, GA D V → Σ k, Frame ((U σ).X k).Ψ D.R.r} (h : LevelLaws U V dict)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hd : Dom a n) :
    ∃ N : ℕ, Nonempty (Module.Basis (Fin N) c.F (cusp Xo c U a n)) := by
  have h0 : GoodEmb c (goodOf c c.F.val.toRingHom) := goodEmb_goodOf c _
  have hF : CuspFD Xo c U := (Formalism.L2.PjFree.cuspFD_ofPj U).1
    (GlobalTheory.cuspForms_finiteDimensional_of_isUnf GlobalTheory.firstFiveLaws.1.secBaseChange _ H Dw l Xo c _
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) _ h0 ((Formalism.L2.PjFree.isUnf_ofPj (U _)).2 (h.unf _ h0)))
  haveI := hF a n hd
  haveI : Module.Free c.F (cusp Xo c U a n) := Module.Free.of_divisionRing _ _
  exact ⟨_, ⟨Module.finBasis c.F _⟩⟩

/- English proof (translation)
Take `⟨l₀, -⟩` from `GlobalTheory.Member.Inhab.exists_ctx_ok_at_lift D j hj`. Set `l : Level (hostOfRecord D)` to `{ l₀ with A := 1, A_pos := one_pos }`. Take `⟨-, Xo, c, U, dict, h⟩` from `LevelModel.exists_levelLaws_at_lift D j hj l rfl`. Establish `h0 : (0 : ℝ) ≤ (absA (datumW D j hj) a : ℝ) + D.R.f * D.R.r * n` using `by positivity`. Take `⟨L, hL⟩` from `LevelModel.exists_sizeRows D l.M ((absA (datumW D j hj) a : ℝ) + D.R.f * D.R.r * n + 1) hf (by linarith)`.

Take `⟨N, hN⟩` from `exists_basis h a n hd`. Conclude with `⟨l, Xo, c, U, dict, _, L, N, h, hL, by linarith, hN⟩`.
-/
theorem hyps_inhabited (D : D7) (hf : 16 ≤ D.R.f) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hd : Dom a n) :
    ∃ (l : Level (hostOfRecord D)) (Xo : Moduli (datumW D j hj) l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
      (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (S L : ℝ) (N : ℕ),
      LevelLaws U (D.sp.W j) dict ∧ SizeRows D l.M S L ∧
        (absA (datumW D j hj) a : ℝ) + D.R.f * D.R.r * n ≤ S ∧
        Nonempty (Module.Basis (Fin N) c.F (cusp Xo c U a n)) := by
  obtain ⟨l₀, -⟩ := GlobalTheory.Member.Inhab.exists_ctx_ok_at_lift D j hj
  let l : Level (hostOfRecord D) := { l₀ with A := 1, A_pos := one_pos }
  obtain ⟨-, Xo, c, U, dict, h⟩ := LevelModel.exists_levelLaws_at_lift D j hj l rfl
  have h0 : (0 : ℝ) ≤ (absA (datumW D j hj) a : ℝ) + D.R.f * D.R.r * n := by positivity
  obtain ⟨L, hL⟩ := LevelModel.exists_sizeRows D l.M ((absA (datumW D j hj) a : ℝ) + D.R.f * D.R.r * n + 1) hf
    (by linarith)
  obtain ⟨N, hN⟩ := exists_basis h a n hd
  exact ⟨l, Xo, c, U, dict, _, L, N, h, hL, by linarith, hN⟩

/- English proof (translation)
Unfold `SizeData₂.logOm`. Rewrite using `[large₂.logDerivative_at_one_eq, Lg'.logDerivative_at_one_eq]`.
-/
theorem logOm_indep {D : D7} (large₂ Lg' : SizeData₂ D) : large₂.logOm = Lg'.logOm := by
  unfold SizeData₂.logOm
  rw [large₂.logDerivative_at_one_eq, Lg'.logDerivative_at_one_eq]

/- English proof (translation)
Take `⟨-, h⟩` from `frameOfSpec n (A v) hA`. Establish `hv : vecS (Pi.basisFun K (Fin n)) v x = fun i => v.embedding (x i)`. Use function extensionality and compare the values at `i`. Simplify using `[vecS]`. Use `conv_rhs => rw [← h, metOf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`.

Unfold `normS cnormS fcoordS`. Rewrite using `[Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity), hv]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.star_apply, Complex.star_def, Complex.conj_mul']`.
-/
theorem normS_sq_frameOf {K : Type} [Field K] [NumberField K] {n : ℕ}
    (A : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (hA : (A v).PosDef) (x : Fin n → K) :
    ((normS (Pi.basisFun K (Fin n)) (fun v => frameOf (A v)) v x ^ 2 : ℝ) : ℂ) =
      star (fun i => v.embedding (x i)) ⬝ᵥ (A v *ᵥ fun i => v.embedding (x i)) := by
  obtain ⟨-, h⟩ := frameOfSpec n (A v) hA
  have hv : vecS (Pi.basisFun K (Fin n)) v x = fun i => v.embedding (x i) := by
    funext i; simp [vecS]
  conv_rhs => rw [← h, metOf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  unfold normS cnormS fcoordS
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity), hv]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']

/- English proof (translation)
Introduce `h`. Take `⟨m, hm⟩` from `exists_nat_gt (Real.exp (|La| + 1))`. Establish `hm0 : (0 : ℝ) < m` using `(Real.exp_pos _).trans hm`. Establish `hmK : (m : K) ≠ 0`. Establish `: m ≠ 0` using `by rintro rfl; simp at hm0`.

Conclude with `this` after adjusting the coercions. Establish `h1` using `h (fun _ => (m : K)⁻¹) trivial (fun e => inv_ne_zero hmK (congrFun e 0))`. Establish `hn : ∀ v : InfinitePlace K, normS (Pi.basisFun K (Fin 1)) (fun _ => frameOf 1) v (fun _ => (m : K)⁻¹) ^ 2 = ((m : ℝ)⁻¹) ^ 2`. Introduce `v`. Use `normS_sq_frameOf (fun _ : InfinitePlace K => (1 : Matrix (Fin 1) (Fin 1) ℂ)) v Matrix.PosDef.one (fun _ => (m : K)⁻¹)` as an intermediate fact.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[this]`. Simplify using `[dotProduct, sq]`. Establish `hc : (0 : ℝ) < nPlS K`. Unfold `nPlS`.

Conclude with `Fintype.card_pos` after adjusting the coercions. Unfold `meanLogS at h1`. Simplify using `only [hn, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1`. Establish `e : (Fintype.card (InfinitePlace K) : ℝ) = nPlS K` using `rfl`. Rewrite `h1` using `[e, ← mul_assoc, one_div_mul_cancel hc.ne', one_mul, Real.log_pow, Real.log_inv]`.

Establish `h2 : |La| + 1 < Real.log m` using `(Real.lt_log_iff_exp_lt hm0).2 hm`. Use `le_abs_self La` as an intermediate fact. Move the coercions through the operations in `at h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_lamS_top (K : Type) [Field K] [NumberField K] [StarRing K] (La : ℝ) :
    ¬ LamS (⊤ : Submodule (𝓞 K) (Fin 1 → K)) (fun _ => frameOf 1) La := by
  intro h
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.exp (|La| + 1))
  have hm0 : (0 : ℝ) < m := (Real.exp_pos _).trans hm
  have hmK : (m : K) ≠ 0 := by
    have : m ≠ 0 := by rintro rfl; simp at hm0
    exact_mod_cast this
  have h1 := h (fun _ => (m : K)⁻¹) trivial (fun e => inv_ne_zero hmK (congrFun e 0))
  have hn : ∀ v : InfinitePlace K,
      normS (Pi.basisFun K (Fin 1)) (fun _ => frameOf 1) v (fun _ => (m : K)⁻¹) ^ 2 = ((m : ℝ)⁻¹) ^ 2 := by
    intro v
    have := normS_sq_frameOf (fun _ : InfinitePlace K => (1 : Matrix (Fin 1) (Fin 1) ℂ)) v Matrix.PosDef.one
      (fun _ => (m : K)⁻¹)
    apply Complex.ofReal_injective
    rw [this]
    simp [dotProduct, sq]
  have hc : (0 : ℝ) < nPlS K := by
    unfold nPlS; exact_mod_cast Fintype.card_pos
  unfold meanLogS at h1
  simp only [hn, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  have e : (Fintype.card (InfinitePlace K) : ℝ) = nPlS K := rfl
  rw [e, ← mul_assoc, one_div_mul_cancel hc.ne', one_mul, Real.log_pow, Real.log_inv] at h1
  have h2 : |La| + 1 < Real.log m := (Real.lt_log_iff_exp_lt hm0).2 hm
  have := le_abs_self La
  push_cast at h1
  linarith

/- English proof (translation)
Take `⟨hf, hL, hS, -⟩` from `h`. Establish `hf' : (0 : ℝ) < D.R.f` using `by exact_mod_cast lt_of_lt_of_le (by norm_num) hf`. Establish `hr : (0 : ℝ) < D.R.r`. Use `D.R.m_add_three_le_k` as an intermediate fact. Conclude with `(show 0 < D.R.r by unfold Ranks.r; omega)` after adjusting the coercions.

Establish `h1` using `Real.log_nonneg hS`. Establish `hL' : 0 < L` using `by linarith`. Establish `hS' : 0 < S` using `by linarith`. Unfold `lamConst`. Check the signs of the components of the expression.
-/
theorem lamConst_pos {D : D7} {M : ℕ} {S L C Om : ℝ} (hC : 0 < C) (h : SizeRows D M S L) :
    0 < lamConst C D.R.f D.R.r L (dE D.host.E) Om S := by
  obtain ⟨hf, hL, hS, -⟩ := h
  have hf' : (0 : ℝ) < D.R.f := by exact_mod_cast lt_of_lt_of_le (by norm_num) hf
  have hr : (0 : ℝ) < D.R.r := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (show 0 < D.R.r by unfold Ranks.r; omega)
  have h1 := Real.log_nonneg hS
  have hL' : 0 < L := by linarith
  have hS' : 0 < S := by linarith
  unfold lamConst
  positivity

end GlobalTheory.CompanionTheory.Ar.abelian₂.LamModel
