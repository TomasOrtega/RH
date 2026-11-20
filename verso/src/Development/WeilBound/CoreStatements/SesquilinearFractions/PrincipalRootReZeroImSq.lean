import Development.WeilBound.CoreStatements.SesquilinearFractions.CoefZeroOfPer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `h1` using `congrArg Complex.re H.sqrt_neg_disc_sq`. Establish `h2` using `congrArg Complex.im H.sqrt_neg_disc_sq`. Simplify using `[sq] at h1 h2`. Assume the negation of the conclusion as `h0`.

Establish `: H.rt0.im = 0`. Establish `: H.rt0.re * H.rt0.im = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left h0`. Rewrite `h1` using `[this]`. Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`.
-/
theorem principal_root_re_zero_im_sq : H.rt0.re = 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
  have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
  simp [sq] at h1 h2
  by_contra h0
  have : H.rt0.im = 0 := by
    have : H.rt0.re * H.rt0.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left h0
  rw [this] at h1
  nlinarith [mul_self_nonneg H.rt0.re]

/- English proof (translation)
Apply the tactic sequence `apply Complex.ext <;> simp [principal_root_re_zero_im_sq (H := H)]`.
-/
theorem rt0_conj_neg_ne_zero : conj H.rt0 = -H.rt0 := by
  apply Complex.ext <;> simp [principal_root_re_zero_im_sq (H := H)]

/- English proof (translation)
Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Break down `rt_cases (H := H) σ with h | h` into its components or cases. Rewrite using `[h, rt0_conj_neg_ne_zero]`. Simplify using `only [ne_eq, not_true_eq_false, iff_false]`. Conclude with `fun e => Host_rt0_ne_neg (H := H) e.symm`.

Rewrite using `[h, map_neg, rt0_conj_neg_ne_zero, neg_neg]`. Simplify using `only [true_iff]`. Conclude with `fun e => Host_rt0_ne_neg (H := H) e.symm`.
-/
theorem conjugate_rt (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ (H.rt : E) = H.rt0 ↔ σ (H.rt : E) ≠ H.rt0 := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases rt_cases (H := H) σ with h | h
  · rw [h, rt0_conj_neg_ne_zero]
    simp only [ne_eq, not_true_eq_false, iff_false]
    exact fun e => Host_rt0_ne_neg (H := H) e.symm
  · rw [h, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    simp only [true_iff]
    exact fun e => Host_rt0_ne_neg (H := H) e.symm

/- English proof (translation)
Rewrite using `[← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0)]`. Use `congr 1`. Use `Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `σ hσ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢`.

Conclude with `(conjugate_rt σ).2 hσ`. Introduce `σ hσ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢`. Conclude with `fun h' => ((conjugate_rt σ).1 h') hσ`. Introduce `σ _`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Introduce `σ _`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Introduce `σ _`. Simplify using the standard rewrite rules.
-/
theorem sum_split {M : Type} [AddCommMonoid M] (F : (E →+* ℂ) → M) :
    ∑ σ, F σ = ∑ σ ∈ Finset.univ.filter (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0), F σ +
      ∑ σ ∈ Finset.univ.filter (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0), F (ComplexEmbedding.conjugate σ) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0)]
  congr 1
  refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact (conjugate_rt σ).2 hσ
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact fun h' => ((conjugate_rt σ).1 h') hσ
  · intro σ _; ext x; simp
  · intro σ _; ext x; simp
  · intro σ _; simp

/- English proof (translation)
Set `F : (E →+* ℂ) → (𝓞 E →* ℂ)` to `fun σ => (σ.comp (algebraMap (𝓞 E) E)).toMonoidHom`. Establish `hF : Function.Injective F`. Introduce `σ σ' e`. Apply `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))` to reduce the goal to its premises. Use extensionality with `b`.

Conclude with `DFunLike.congr_fun e b`. Establish `li` using `(linearIndependent_monoidHom (𝓞 E) ℂ).comp F hF`. Use function extensionality and compare the values at `σ`. Use `Fintype.linearIndependent_iff.1 li l ?_ σ` and prove the remaining obligations. Use function extensionality and compare the values at `b`.

Simplify `h b` using `[F, Finset.sum_apply]`.
-/
theorem emb_indep (l : (E →+* ℂ) → ℂ) (h : ∀ b : 𝓞 E, ∑ σ, l σ * σ (b : E) = 0) : l = 0 := by
  let F : (E →+* ℂ) → (𝓞 E →* ℂ) := fun σ => (σ.comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hF : Function.Injective F := by
    intro σ σ' e
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext b
    exact DFunLike.congr_fun e b
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp F hF
  funext σ
  refine Fintype.linearIndependent_iff.1 li l ?_ σ
  funext b
  simpa [F, Finset.sum_apply] using h b

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hall : ∀ σ : E →+* ℂ, ‖σ (a : E)‖ < 1`. Introduce `σ`. Distinguish the cases in `hσ : σ (H.rt : E) = (if b then H.rt0 else -H.rt0)`.

Conclude with `hcon σ hσ`. Establish `h2 : ComplexEmbedding.conjugate σ (H.rt : E) = (if b then H.rt0 else -H.rt0)`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Apply the tactic sequence `rcases rt_cases (H := H) σ with h | h <;> cases b <;>`. Simplify using `[rt0_conj_neg_ne_zero (H := H)]`.

Use `hcon _ h2` as an intermediate fact. Rewrite `this` using `[ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]`. Then use the resulting hypothesis. Take `⟨σ₀⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hlt : ∏ σ : E →+* ℂ, ‖σ (a : E)‖ < 1`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ₀)]`.

Establish `h1 : ∏ σ ∈ Finset.univ.erase σ₀, ‖σ (a : E)‖ ≤ 1` using `Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun σ _ => (hall σ).le)`. Combine the equalities or inequalities in the displayed calculation. Establish `hge : 1 ≤ ∏ σ : E →+* ℂ, ‖σ (a : E)‖`. Establish `hN : Algebra.norm ℤ a ≠ 0` using `Algebra.norm_ne_zero_iff.2 ha`. Establish `e1` using `Algebra.norm_eq_prod_embeddings ℚ ℂ (a : E)`.

Rewrite `e1` using `[← Algebra.coe_norm_int]`. Establish `e2 : ∏ τ : E →ₐ[ℚ] ℂ, τ (a : E) = ∏ σ : E →+* ℂ, σ (a : E)` using `Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun τ => rfl)`. Rewrite `e1` using `[e2]`. Rewrite using `[← norm_prod, ← e1]`. Establish `: ((algebraMap ℚ ℂ) ((Algebra.norm ℤ a : ℤ) : ℚ)) = ((Algebra.norm ℤ a : ℤ) : ℂ)` using `by simp`.

Rewrite using `[this, Complex.norm_intCast]`. Conclude with `Int.one_le_abs hN` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_big (a : 𝓞 E) (ha : a ≠ 0) (b : Bool) :
    ∃ σ : E →+* ℂ, σ (H.rt : E) = (if b then H.rt0 else -H.rt0) ∧ 1 ≤ ‖σ (a : E)‖ := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ σ : E →+* ℂ, ‖σ (a : E)‖ < 1 := by
    intro σ
    by_cases hσ : σ (H.rt : E) = (if b then H.rt0 else -H.rt0)
    · exact hcon σ hσ
    · have h2 : ComplexEmbedding.conjugate σ (H.rt : E) = (if b then H.rt0 else -H.rt0) := by
        rw [ComplexEmbedding.conjugate_coe_eq]
        rcases rt_cases (H := H) σ with h | h <;> cases b <;>
          simp_all [rt0_conj_neg_ne_zero (H := H)]
      have := hcon _ h2
      rwa [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at this
  obtain ⟨σ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hlt : ∏ σ : E →+* ℂ, ‖σ (a : E)‖ < 1 := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ₀)]
    have h1 : ∏ σ ∈ Finset.univ.erase σ₀, ‖σ (a : E)‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun σ _ => (hall σ).le)
    calc ‖σ₀ (a : E)‖ * ∏ σ ∈ Finset.univ.erase σ₀, ‖σ (a : E)‖ ≤ ‖σ₀ (a : E)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ < 1 := by rw [_root_.mul_one]; exact hall σ₀
  have hge : 1 ≤ ∏ σ : E →+* ℂ, ‖σ (a : E)‖ := by
    have hN : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
    have e1 := Algebra.norm_eq_prod_embeddings ℚ ℂ (a : E)
    rw [← Algebra.coe_norm_int] at e1
    have e2 : ∏ τ : E →ₐ[ℚ] ℂ, τ (a : E) = ∏ σ : E →+* ℂ, σ (a : E) :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun τ => rfl)
    rw [e2] at e1
    rw [← norm_prod, ← e1]
    have : ((algebraMap ℚ ℂ) ((Algebra.norm ℤ a : ℤ) : ℚ)) = ((Algebra.norm ℤ a : ℤ) : ℂ) := by simp
    rw [this, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hN
  linarith

end PositivityTheory.Xgf.DPer

end
