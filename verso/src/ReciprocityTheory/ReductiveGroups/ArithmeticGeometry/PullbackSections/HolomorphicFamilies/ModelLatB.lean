import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA FractionalIdeal

variable {r : ℕ}

/- English proof (translation)
Establish `hsq : ∀ σ : D.host.E →+* ℂ, σ D.host.xi0 ^ 2 = 1 / (((Ideal.absNorm D.host.ccK : ℕ) : ℂ) ^ 2 * (-(D.host.d : ℂ)))`. Introduce `σ`. Establish `e : D.host.xi0 ^ 2 = 1 / (((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ^ 2 * (-(D.host.d : D.host.E)))`. Simplify using `only [Formalism.BasicNotions.Host.xi0]`. Rewrite using `[div_pow, mul_pow, D.host.sqrtMinusD_sq]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← map_pow, e]`. Simplify using the standard rewrite rules. Establish `e2 : ‖τ D.host.xi0‖ ^ 2 = ‖D.host.φ₀ D.host.xi0‖ ^ 2`. Rewrite using `[← norm_pow, ← norm_pow, hsq τ, hsq D.host.φ₀]`.

Establish `ha` using `norm_nonneg (τ D.host.xi0)`. Establish `hb` using `norm_nonneg (D.host.φ₀ D.host.xi0)`. Use `show ‖τ D.host.xi0‖ = ‖D.host.φ₀ D.host.xi0‖`. Conclude with `le_antisymm (by nlinarith) (by nlinarith)`.
-/
theorem norm_embedding_hostFormConstant_eq (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  have hsq : ∀ σ : D.host.E →+* ℂ, σ D.host.xi0 ^ 2 =
      1 / (((Ideal.absNorm D.host.ccK : ℕ) : ℂ) ^ 2 * (-(D.host.d : ℂ))) := by
    intro σ
    have e : D.host.xi0 ^ 2 =
        1 / (((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ^ 2 * (-(D.host.d : D.host.E))) := by
      simp only [Formalism.BasicNotions.Host.xi0]
      rw [div_pow, mul_pow, D.host.sqrtMinusD_sq]
      ring
    rw [← map_pow, e]
    simp
  have e2 : ‖τ D.host.xi0‖ ^ 2 = ‖D.host.φ₀ D.host.xi0‖ ^ 2 := by
    rw [← norm_pow, ← norm_pow, hsq τ, hsq D.host.φ₀]
  have ha := norm_nonneg (τ D.host.xi0)
  have hb := norm_nonneg (D.host.φ₀ D.host.xi0)
  show ‖τ D.host.xi0‖ = ‖D.host.φ₀ D.host.xi0‖
  exact le_antisymm (by nlinarith) (by nlinarith)

/- English proof (translation)
Establish `hx0 : D.host.xi0 ≠ 0` using `cmHost_imaginaryGenerator_ne_zero hP D`. Establish `hcξ : IsCMField.complexConj D.host.E X.ξ0 = -X.ξ0` using `X.ξ0_im`. Establish `hcx : IsCMField.complexConj D.host.E D.host.xi0 = -D.host.xi0` using `conj_xi0_alt D`. Establish `hcu : IsCMField.complexConj D.host.E (X.ξ0 / D.host.xi0) = X.ξ0 / D.host.xi0`. Rewrite using `[map_div₀, hcξ, hcx, neg_div_neg_eq]`.

Establish `hτx : D.host.φ₀ D.host.xi0 ≠ 0` using `(map_ne_zero D.host.φ₀).2 hx0`. Establish `hn : ‖D.host.φ₀ (X.ξ0 / D.host.xi0)‖ = 1`. Establish `e : ‖D.host.φ₀ D.host.xi0‖ = xiR D` using `rfl`. Rewrite using `[map_div₀, norm_div, hX D.host.φ₀, ← e, div_self (norm_ne_zero_iff.2 hτx)]`. Establish `hreal : starRingEnd ℂ (D.host.φ₀ (X.ξ0 / D.host.xi0)) = D.host.φ₀ (X.ξ0 / D.host.xi0)`.

Rewrite using `[← IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀, hcu]`. Establish `hsq : D.host.φ₀ (X.ξ0 / D.host.xi0) ^ 2 = 1`. Establish `h1` using `Complex.conj_eq_iff_re.1 hreal`. Rewrite `hn`, the goal using `[← h1]`. Rewrite `hn` using `[Complex.norm_real, Real.norm_eq_abs]`.

Establish `h2 : (D.host.φ₀ (X.ξ0 / D.host.xi0)).re ^ 2 = 1` using `by rw [← sq_abs, hn, one_pow]`. Conclude with `h2` after adjusting the coercions. Establish `hu2 : (X.ξ0 / D.host.xi0) ^ 2 = 1`. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[map_pow, hsq, map_one]`.

Establish `hfac : (X.ξ0 / D.host.xi0 - 1) * (X.ξ0 / D.host.xi0 + 1) = 0`. Establish `e : (X.ξ0 / D.host.xi0 - 1) * (X.ξ0 / D.host.xi0 + 1) = (X.ξ0 / D.host.xi0) ^ 2 - 1` using `by ring`. Rewrite using `[e, hu2, sub_self]`. Break down `mul_eq_zero.1 hfac with h | h` into its components or cases. Use `left`.

Conclude with `(div_eq_one_iff_eq hx0).1 (sub_eq_zero.1 h)`. Use `right`. Establish `h3 : X.ξ0 / D.host.xi0 = -1` using `eq_neg_of_add_eq_zero_left h`. Rewrite `h3` using `[div_eq_iff hx0]`. Rewrite using `[h3]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem xi_eq (hP : FactPrincipalDatum) (D : D7) (X : Data D.host.E r)
    (hX : ∀ τ : D.host.E →+* ℂ, ‖τ X.ξ0‖ = xiR D) : X.ξ0 = D.host.xi0 ∨ X.ξ0 = -D.host.xi0 := by
  have hx0 : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero hP D
  have hcξ : IsCMField.complexConj D.host.E X.ξ0 = -X.ξ0 := X.ξ0_im
  have hcx : IsCMField.complexConj D.host.E D.host.xi0 = -D.host.xi0 := conj_xi0_alt D
  have hcu : IsCMField.complexConj D.host.E (X.ξ0 / D.host.xi0) = X.ξ0 / D.host.xi0 := by
    rw [map_div₀, hcξ, hcx, neg_div_neg_eq]
  have hτx : D.host.φ₀ D.host.xi0 ≠ 0 := (map_ne_zero D.host.φ₀).2 hx0
  have hn : ‖D.host.φ₀ (X.ξ0 / D.host.xi0)‖ = 1 := by
    have e : ‖D.host.φ₀ D.host.xi0‖ = xiR D := rfl
    rw [map_div₀, norm_div, hX D.host.φ₀, ← e, div_self (norm_ne_zero_iff.2 hτx)]
  have hreal : starRingEnd ℂ (D.host.φ₀ (X.ξ0 / D.host.xi0)) = D.host.φ₀ (X.ξ0 / D.host.xi0) := by
    rw [← IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀, hcu]
  have hsq : D.host.φ₀ (X.ξ0 / D.host.xi0) ^ 2 = 1 := by
    have h1 := Complex.conj_eq_iff_re.1 hreal
    rw [← h1] at hn ⊢
    rw [Complex.norm_real, Real.norm_eq_abs] at hn
    have h2 : (D.host.φ₀ (X.ξ0 / D.host.xi0)).re ^ 2 = 1 := by rw [← sq_abs, hn, one_pow]
    exact_mod_cast h2
  have hu2 : (X.ξ0 / D.host.xi0) ^ 2 = 1 := by
    apply D.host.φ₀.injective
    rw [map_pow, hsq, map_one]
  have hfac : (X.ξ0 / D.host.xi0 - 1) * (X.ξ0 / D.host.xi0 + 1) = 0 := by
    have e : (X.ξ0 / D.host.xi0 - 1) * (X.ξ0 / D.host.xi0 + 1) = (X.ξ0 / D.host.xi0) ^ 2 - 1 := by ring
    rw [e, hu2, sub_self]
  rcases mul_eq_zero.1 hfac with h | h
  · left
    exact (div_eq_one_iff_eq hx0).1 (sub_eq_zero.1 h)
  · right
    have h3 : X.ξ0 / D.host.xi0 = -1 := eq_neg_of_add_eq_zero_left h
    rw [div_eq_iff hx0] at h3
    rw [h3]
    ring

/- English proof (translation)
Unfold `herm`. Simplify using `only [Matrix.vecMul, dotProduct]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[cc]`.

Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb, cc]`. Simplify using the standard rewrite rules.
-/
theorem herm_single (D : D7) (G : Matrix (Fin r) (Fin r) D.host.E) (w : Fin r → D.host.E) (i : Fin r) :
    herm G w (Pi.single i 1) = Matrix.vecMul w G i := by
  unfold herm
  simp only [Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [cc]
  · intro b _ hb
    simp [Pi.single_apply, hb, cc]
  · simp

/- English proof (translation)
Set `T : Submodule D.host.E (Fin r → D.host.E)` to `{ carrier := {v | herm X.Gm w v = 0} add_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Establish `e : herm X.Gm w (a + b) = herm X.Gm w a + herm X.Gm w b`. Simplify using `only [herm, Pi.add_apply, cc, map_add, mul_add, Finset.sum_add_distrib]`.

Rewrite using `[e, ha, hb, add_zero]`. Use the proof step `zero_mem' := by`. Simplify using `only [Set.mem_setOf_eq, herm, Pi.zero_apply, cc, map_zero, mul_zero, Finset.sum_const_zero]`. Use the proof step `smul_mem' := by`. Introduce `c v hv`.

Simplify using `only [Set.mem_setOf_eq] at hv ⊢`. Establish `e : herm X.Gm w (c • v) = cc c * herm X.Gm w v`. Simplify using `only [herm, Pi.smul_apply, smul_eq_mul, cc, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, hv, mul_zero] }`. Establish `hsp : Submodule.span D.host.E (X.Λ : Set (Fin r → D.host.E)) ≤ T` using `Submodule.span_le.mpr fun v hv => hw v hv`. Rewrite `hsp` using `[X.Λ_span]`. Establish `hvm : Matrix.vecMul w X.Gm = 0`. Use function extensionality and compare the values at `i`.

Establish `h1 : Pi.single i 1 ∈ T` using `hsp Submodule.mem_top`. Rewrite using `[← herm_single D X.Gm w i]`. Conclude with `h1`. Conclude with `Matrix.eq_zero_of_vecMul_eq_zero X.Gm_det hvm`.
-/
theorem eq_zero_of_herm (D : D7) (X : Data D.host.E r) {w : Fin r → D.host.E}
    (hw : ∀ v ∈ X.Λ, herm X.Gm w v = 0) : w = 0 := by
  let T : Submodule D.host.E (Fin r → D.host.E) :=
    { carrier := {v | herm X.Gm w v = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        have e : herm X.Gm w (a + b) = herm X.Gm w a + herm X.Gm w b := by
          simp only [herm, Pi.add_apply, cc, map_add, mul_add, Finset.sum_add_distrib]
        rw [e, ha, hb, add_zero]
      zero_mem' := by
        simp only [Set.mem_setOf_eq, herm, Pi.zero_apply, cc, map_zero, mul_zero, Finset.sum_const_zero]
      smul_mem' := by
        intro c v hv
        simp only [Set.mem_setOf_eq] at hv ⊢
        have e : herm X.Gm w (c • v) = cc c * herm X.Gm w v := by
          simp only [herm, Pi.smul_apply, smul_eq_mul, cc, map_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          ring
        rw [e, hv, mul_zero] }
  have hsp : Submodule.span D.host.E (X.Λ : Set (Fin r → D.host.E)) ≤ T :=
    Submodule.span_le.mpr fun v hv => hw v hv
  rw [X.Λ_span] at hsp
  have hvm : Matrix.vecMul w X.Gm = 0 := by
    funext i
    have h1 : Pi.single i 1 ∈ T := hsp Submodule.mem_top
    rw [← herm_single D X.Gm w i]
    exact h1
  exact Matrix.eq_zero_of_vecMul_eq_zero X.Gm_det hvm

/- English proof (translation)
Take `⟨-, -, -, -, -, gg, ee, F, ik, φ, hiso, -⟩` from `h.unf j hj σ hσ`. Establish `h1ne : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0` using `one_ne_zero`. Choose the witnesses or unpack the hypotheses as in `⟨ε, hε, htr⟩ : ∃ ε : ℤ, ε * ε = 1 ∧ ∀ u : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * u) = (ε : ℚ) * Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 * u) := by`. Break down `xi_eq hP D ((T.U j σ).X k) (h.xiAbs j hj σ hσ k) with hξ | hξ` into its components or cases. Use `⟨-1, by norm_num, fun u => ?_⟩` and prove the remaining obligations.

Rewrite using `[hξ, neg_mul, map_neg]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨1, by norm_num, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[hξ, neg_neg]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `htr' : ∀ u : D.host.E, Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 * u) = (ε : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 * u)`. Introduce `u`. Rewrite using `[htr u, ← mul_assoc]`.

Establish `: ((ε : ℚ) * ε) = 1` using `by exact_mod_cast hε`. Rewrite using `[this, one_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `hy z hz`. Rewrite using `[mem_dual h1ne]`.

Introduce `a ha`. Take `⟨c, rfl⟩` from `(mem_one_iff _).1 ha`. Rewrite using `[Algebra.traceForm_apply]`. Establish `hy' : (algebraMap (𝓞 D.host.E) D.host.E c) • y ∈ ((T.U j σ).X k).Λ`. Rewrite using `[algebraMap_smul]`.

Conclude with `Submodule.smul_mem _ c hy`. Establish `e : D.host.xi0 * herm ((T.U j σ).X k).Gm y z * algebraMap (𝓞 D.host.E) D.host.E c = D.host.xi0 * herm ((T.U j σ).X k).Gm ((algebraMap (𝓞 D.host.E) D.host.E c) • y) z`. Rewrite using `[herm_smul_left]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, htr]`.

Establish `hE` using `hiso k ((φ k).symm ⟨_, hy'⟩) ((φ k).symm ⟨z, hz⟩)`. Simplify using `only [LinearEquiv.apply_symm_apply] at hE`. Use `⟨ε * (F.Di (ik k)).EF ((φ k).symm ⟨_, hy'⟩) ((φ k).symm ⟨z, hz⟩), ?_⟩` and prove the remaining obligations. Rewrite using `[eq_intCast, Int.cast_mul, hE]`. Introduce `hy`.

Establish `hint : ∀ a : (F.Di (ik k)).La, ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm y (φ k a : Fin D.R.r → D.host.E))`. Introduce `a`. Establish `h2` using `(mem_dual h1ne).1 (hy _ (φ k a).2) 1 (one_mem_one _)`. Rewrite `h2` using `[Algebra.traceForm_apply, mul_one]`. Take `⟨n, hn⟩` from `h2`.

Use `⟨ε * n, ?_⟩` and prove the remaining obligations. Rewrite using `[htr', ← hn, eq_intCast, Int.cast_mul]`. Set `ψ : (F.Di (ik k)).La →+ ℤ` to `AddMonoidHom.mk' (fun a => Classical.choose (hint a)) (fun a b => by`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Establish `e1` using `Classical.choose_spec (hint (a + b))`.

Establish `e2` using `Classical.choose_spec (hint a)`. Establish `e3` using `Classical.choose_spec (hint b)`. Rewrite using `[Int.cast_add, e1, e2, e3, map_add, Submodule.coe_add, herm_add_right, mul_add, map_add])`. Take `⟨b, hb⟩` from `(F.Di (ik k)).unimod.2 ψ.toIntLinearMap`. Use `set w := y - (φ k b : Fin D.R.r → D.host.E) with hw`.

Establish `hzero : ∀ a : (F.Di (ik k)).La, Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm w (φ k a : Fin D.R.r → D.host.E)) = 0`. Introduce `a`. Establish `e1 : herm ((T.U j σ).X k).Gm y (φ k a : Fin D.R.r → D.host.E) = herm ((T.U j σ).X k).Gm w (φ k a) + herm ((T.U j σ).X k).Gm (φ k b) (φ k a)`. Rewrite using `[← herm_add_left, hw, sub_add_cancel]`. Establish `e2 : (((F.Di (ik k)).EF b a : ℤ) : ℚ) = (ψ a : ℚ)`.

Rewrite using `[hb]`. Both sides reduce to the same expression. Rewrite `e2` using `[hiso k b a]`. Establish `e3 : (ψ a : ℚ) = Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm y (φ k a : Fin D.R.r → D.host.E))` using `Classical.choose_spec (hint a)`. Rewrite `e3` using `[e1, mul_add, map_add, ← e2]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hperp : ∀ a : (F.Di (ik k)).La, herm ((T.U j σ).X k).Gm w (φ k a : Fin D.R.r → D.host.E) = 0`. Introduce `a`. Establish `hsep : -((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm w (φ k a : Fin D.R.r → D.host.E) = 0`. Apply `trace_sep D` to reduce the goal to its premises.

Introduce `c`. Set `c' : 𝓞 D.host.E` to `⟨cc (algebraMap (𝓞 D.host.E) D.host.E c), int_cc D (NumberField.RingOfIntegers.isIntegral_coe c)⟩`. Establish `e4` using `hzero (c' • a)`. Rewrite `e4` using `[LinearEquiv.map_smul, Submodule.coe_smul, ← algebraMap_smul D.host.E c', herm_smul_right]`. Establish `e5 : cc (algebraMap (𝓞 D.host.E) D.host.E c') = algebraMap (𝓞 D.host.E) D.host.E c` using `cc_cc D _`.

Rewrite `e4` using `[e5]`. Rewrite using `[← e4]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Break down `mul_eq_zero.1 hsep with h3 | h3` into its components or cases.

Conclude with `absurd (neg_eq_zero.1 h3) ((T.U j σ).X k).ξ0_ne`. Conclude with `h3`. Establish `hw0 : w = 0`. Apply `eq_zero_of_herm D ((T.U j σ).X k)` to reduce the goal to its premises. Introduce `v hv`.

Use `hperp ((φ k).symm ⟨v, hv⟩)` as an intermediate fact. Simplify using `using this`. Establish `: y = (φ k b : Fin D.R.r → D.host.E)`. Rewrite using `[← sub_eq_zero]`. Conclude with `hw0`.

Rewrite using `[this]`. Conclude with `(φ k b).2`.
-/
theorem lat_dual (hP : FactPrincipalDatum) {D : D7} (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ) (k : (T.U j σ).Comp) (y : Fin D.R.r → D.host.E) :
    y ∈ ((T.U j σ).X k).Λ ↔
      ∀ z ∈ ((T.U j σ).X k).Λ, D.host.xi0 * herm ((T.U j σ).X k).Gm y z ∈ Dinv D := by
  obtain ⟨-, -, -, -, -, gg, ee, F, ik, φ, hiso, -⟩ := h.unf j hj σ hσ
  have h1ne : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := one_ne_zero
  obtain ⟨ε, hε, htr⟩ : ∃ ε : ℤ, ε * ε = 1 ∧ ∀ u : D.host.E,
      Algebra.trace ℚ D.host.E (D.host.xi0 * u) =
        (ε : ℚ) * Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 * u) := by
    rcases xi_eq hP D ((T.U j σ).X k) (h.xiAbs j hj σ hσ k) with hξ | hξ
    · refine ⟨-1, by norm_num, fun u => ?_⟩
      rw [hξ, neg_mul, map_neg]
      push_cast
      ring
    · refine ⟨1, by norm_num, fun u => ?_⟩
      rw [hξ, neg_neg]
      push_cast
      ring
  have htr' : ∀ u : D.host.E, Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 * u) =
      (ε : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 * u) := by
    intro u
    rw [htr u, ← mul_assoc]
    have : ((ε : ℚ) * ε) = 1 := by exact_mod_cast hε
    rw [this, one_mul]
  constructor
  · intro hy z hz
    rw [mem_dual h1ne]
    intro a ha
    obtain ⟨c, rfl⟩ := (mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E c) • y ∈ ((T.U j σ).X k).Λ := by
      rw [algebraMap_smul]; exact Submodule.smul_mem _ c hy
    have e : D.host.xi0 * herm ((T.U j σ).X k).Gm y z * algebraMap (𝓞 D.host.E) D.host.E c =
        D.host.xi0 * herm ((T.U j σ).X k).Gm ((algebraMap (𝓞 D.host.E) D.host.E c) • y) z := by
      rw [herm_smul_left]; ring
    rw [e, htr]
    have hE := hiso k ((φ k).symm ⟨_, hy'⟩) ((φ k).symm ⟨z, hz⟩)
    simp only [LinearEquiv.apply_symm_apply] at hE
    refine ⟨ε * (F.Di (ik k)).EF ((φ k).symm ⟨_, hy'⟩) ((φ k).symm ⟨z, hz⟩), ?_⟩
    rw [eq_intCast, Int.cast_mul, hE]
  · intro hy
    have hint : ∀ a : (F.Di (ik k)).La, ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ D.host.E
        (-((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm y (φ k a : Fin D.R.r → D.host.E)) := by
      intro a
      have h2 := (mem_dual h1ne).1 (hy _ (φ k a).2) 1 (one_mem_one _)
      rw [Algebra.traceForm_apply, mul_one] at h2
      obtain ⟨n, hn⟩ := h2
      refine ⟨ε * n, ?_⟩
      rw [htr', ← hn, eq_intCast, Int.cast_mul]
    let ψ : (F.Di (ik k)).La →+ ℤ := AddMonoidHom.mk' (fun a => Classical.choose (hint a)) (fun a b => by
      apply Int.cast_injective (α := ℚ)
      have e1 := Classical.choose_spec (hint (a + b))
      have e2 := Classical.choose_spec (hint a)
      have e3 := Classical.choose_spec (hint b)
      rw [Int.cast_add, e1, e2, e3, map_add, Submodule.coe_add, herm_add_right, mul_add, map_add])
    obtain ⟨b, hb⟩ := (F.Di (ik k)).unimod.2 ψ.toIntLinearMap
    set w := y - (φ k b : Fin D.R.r → D.host.E) with hw
    have hzero : ∀ a : (F.Di (ik k)).La,
        Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 *
          herm ((T.U j σ).X k).Gm w (φ k a : Fin D.R.r → D.host.E)) = 0 := by
      intro a
      have e1 : herm ((T.U j σ).X k).Gm y (φ k a : Fin D.R.r → D.host.E) =
          herm ((T.U j σ).X k).Gm w (φ k a) + herm ((T.U j σ).X k).Gm (φ k b) (φ k a) := by
        rw [← herm_add_left, hw, sub_add_cancel]
      have e2 : (((F.Di (ik k)).EF b a : ℤ) : ℚ) = (ψ a : ℚ) := by
        rw [hb]; rfl
      rw [hiso k b a] at e2
      have e3 : (ψ a : ℚ) = Algebra.trace ℚ D.host.E
          (-((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm y (φ k a : Fin D.R.r → D.host.E)) :=
        Classical.choose_spec (hint a)
      rw [e1, mul_add, map_add, ← e2] at e3
      linarith
    have hperp : ∀ a : (F.Di (ik k)).La, herm ((T.U j σ).X k).Gm w (φ k a : Fin D.R.r → D.host.E) = 0 := by
      intro a
      have hsep : -((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm w (φ k a : Fin D.R.r → D.host.E) = 0 := by
        apply trace_sep D
        intro c
        let c' : 𝓞 D.host.E := ⟨cc (algebraMap (𝓞 D.host.E) D.host.E c),
          int_cc D (NumberField.RingOfIntegers.isIntegral_coe c)⟩
        have e4 := hzero (c' • a)
        rw [LinearEquiv.map_smul, Submodule.coe_smul, ← algebraMap_smul D.host.E c', herm_smul_right] at e4
        have e5 : cc (algebraMap (𝓞 D.host.E) D.host.E c') = algebraMap (𝓞 D.host.E) D.host.E c :=
          cc_cc D _
        rw [e5] at e4
        rw [← e4]
        congr 1
        ring
      rcases mul_eq_zero.1 hsep with h3 | h3
      · exact absurd (neg_eq_zero.1 h3) ((T.U j σ).X k).ξ0_ne
      · exact h3
    have hw0 : w = 0 := by
      apply eq_zero_of_herm D ((T.U j σ).X k)
      intro v hv
      have := hperp ((φ k).symm ⟨v, hv⟩)
      simpa using this
    have : y = (φ k b : Fin D.R.r → D.host.E) := by
      rw [← sub_eq_zero]; exact hw0
    rw [this]
    exact (φ k b).2

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB
