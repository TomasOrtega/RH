import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyLinear
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyFewColumnsLinear
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogShortFamilyNumbersLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Harm

open MvPolynomial

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hI : ∀ z : E, IsIntegral ℤ z ↔ z ∈ (algebraMap (𝓞 E) E).range` using `fun z => ⟨fun hz => ⟨⟨z, hz⟩, rfl⟩, fun ⟨o, ho⟩ => ho ▸ o.isIntegral_coe⟩`. Establish `hc : ∀ z : E, IsIntegral ℤ (IsCMField.complexConj E z) ↔ IsIntegral ℤ z`. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Use `hz.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom` as an intermediate fact. Simplify `this` using `[IsCMField.complexConj_apply_apply]`. Introduce `hz`. Conclude with `hz.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom`. Establish `key : ∀ y : Fin n → E, FD.herm 1 x y = IsCMField.complexConj E (∑ j, IsCMField.complexConj E (x j) * y j)`.

Introduce `y`. Simplify using `only [FD.herm, FD.cc, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, map_mul, IsCMField.complexConj_apply_apply]`. Rewrite using `[h x]`. Use `forall₂_congr fun y _ => ?_` and prove the remaining obligations. Rewrite using `[key y, hc, hI]`.
-/
theorem mem_iff_herm_of_unimod {n : ℕ} {Λ : GenLat E n} (h : Λ.Unimod) (x : Fin n → E) :
    x ∈ Λ.La ↔ ∀ y ∈ Λ.La, IsIntegral ℤ (FD.herm 1 x y) := by
  have hI : ∀ z : E, IsIntegral ℤ z ↔ z ∈ (algebraMap (𝓞 E) E).range := fun z =>
    ⟨fun hz => ⟨⟨z, hz⟩, rfl⟩, fun ⟨o, ho⟩ => ho ▸ o.isIntegral_coe⟩
  have hc : ∀ z : E, IsIntegral ℤ (IsCMField.complexConj E z) ↔ IsIntegral ℤ z := by
    intro z
    constructor
    · intro hz
      have := hz.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
      simpa [IsCMField.complexConj_apply_apply] using this
    · intro hz
      exact hz.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
  have key : ∀ y : Fin n → E, FD.herm 1 x y =
      IsCMField.complexConj E (∑ j, IsCMField.complexConj E (x j) * y j) := by
    intro y
    simp only [FD.herm, FD.cc, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, map_mul,
      IsCMField.complexConj_apply_apply]
  rw [h x]
  refine forall₂_congr fun y _ => ?_
  rw [key y, hc, hI]

/- English proof (translation)
Introduce and unpack `⟨h1, h2⟩`. Unfold `InPsi at h1 h2`. Rewrite `h2` using `[ComplexEmbedding.conjugate_coe_eq, h1]`. Establish `him : H.rt0.im = 0` using `Complex.conj_eq_iff_im.mp h2`. Establish `hre` using `congrArg Complex.re H.sqrt_neg_disc_sq`.

Simplify using `only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.natCast_re] at hre`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`.
-/
theorem not_inPsi_and_conjugate (H : Host E) (τ : E →+* ℂ) :
    ¬ (InPsi H τ ∧ InPsi H (ComplexEmbedding.conjugate τ)) := by
  rintro ⟨h1, h2⟩
  unfold InPsi at h1 h2
  rw [ComplexEmbedding.conjugate_coe_eq, h1] at h2
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp h2
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re,
    Complex.natCast_re] at hre
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [mul_self_nonneg H.rt0.re]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem coe_embF {H : Host E} {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : E) :
    ((embF c τ x : c.F) : ℂ) = τ x := rfl

/- English proof (translation)
Introduce and unpack `⟨⟨τ, hτ⟩, b⟩ ⟨⟨τ', hτ'⟩, b'⟩ h`. Establish `hx : ∀ x : E, (if b then ComplexEmbedding.conjugate τ else τ) x = (if b' then ComplexEmbedding.conjugate τ' else τ') x`. Introduce `x`. Use `congrArg (fun z : c.F => (z : ℂ)) (congrFun h x)` as an intermediate fact. Simplify using `only [coe_embF] at this`.

Apply the tactic sequence `cases b <;> cases b' <;>`. Simplify `this` using `[FD.cc, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]`. Establish `hf : (if b then ComplexEmbedding.conjugate τ else τ) = (if b' then ComplexEmbedding.conjugate τ' else τ')` using `RingHom.ext hx`. Apply the tactic sequence `cases b <;> cases b'`. Simplify using `only [Bool.false_eq_true, if_false] at hf`.

Substitute `hf` using the available equality. Both sides reduce to the same expression. Simplify using `only [Bool.false_eq_true, if_false, if_true] at hf`. Conclude with `absurd ⟨hτ', by rw [← hf]; exact hτ⟩ (not_inPsi_and_conjugate H τ')`. Simplify using `only [Bool.false_eq_true, if_false, if_true] at hf`.

Conclude with `absurd ⟨hτ, by rw [hf]; exact hτ'⟩ (not_inPsi_and_conjugate H τ)`. Simplify using `only [if_true] at hf`. Establish `h2` using `(ComplexEmbedding.involutive_conjugate E).injective hf`. Substitute `h2` using the available equality. Both sides reduce to the same expression.
-/
theorem injective_embF_inPsi {H : Host E} {l : Level H} (c : Coeff l) :
    Function.Injective fun s : {τ : E →+* ℂ // InPsi H τ} × Bool =>
      fun x : E => embF c s.1.1 (if s.2 then FD.cc x else x) := by
  rintro ⟨⟨τ, hτ⟩, b⟩ ⟨⟨τ', hτ'⟩, b'⟩ h
  have hx : ∀ x : E, (if b then ComplexEmbedding.conjugate τ else τ) x =
      (if b' then ComplexEmbedding.conjugate τ' else τ') x := by
    intro x
    have := congrArg (fun z : c.F => (z : ℂ)) (congrFun h x)
    simp only [coe_embF] at this
    cases b <;> cases b' <;>
      simpa [FD.cc, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
        using this
  have hf : (if b then ComplexEmbedding.conjugate τ else τ) =
      (if b' then ComplexEmbedding.conjugate τ' else τ') := RingHom.ext hx
  cases b <;> cases b'
  · simp only [Bool.false_eq_true, if_false] at hf
    subst hf
    rfl
  · simp only [Bool.false_eq_true, if_false, if_true] at hf
    exact absurd ⟨hτ', by rw [← hf]; exact hτ⟩ (not_inPsi_and_conjugate H τ')
  · simp only [Bool.false_eq_true, if_false, if_true] at hf
    exact absurd ⟨hτ, by rw [hf]; exact hτ'⟩ (not_inPsi_and_conjugate H τ)
  · simp only [if_true] at hf
    have h2 := (ComplexEmbedding.involutive_conjugate E).injective hf
    subst h2
    rfl

/- English proof (translation)
Rewrite using `[MvPolynomial.map_rename, MvPoly.l1Norm_rename_of_injective e.injective, MvPoly.l1Norm_map]`.
-/
theorem sum_norm_coeff_eq_l1Norm {K σ σ' : Type} [Field K] (e : σ ≃ σ') (f : K →+* ℂ)
    (Q : MvPolynomial σ K) :
    ∑ m ∈ Q.support, ‖f (Q.coeff m)‖ = MvPoly.l1Norm (MvPolynomial.map f (rename e Q)) := by
  rw [MvPolynomial.map_rename, MvPoly.l1Norm_rename_of_injective e.injective, MvPoly.l1Norm_map]

/- English proof (translation)
Break down `hx.eq_or_lt with h0 | hpos` into its components or cases. Rewrite using `[← h0, Real.log_zero]`. Conclude with `hB`. Conclude with `(Real.log_le_log hpos h).trans hy`.
-/
theorem log_le_of_le_of_log_le {x y B : ℝ} (hx : 0 ≤ x) (h : x ≤ y) (hy : Real.log y ≤ B)
    (hB : 0 ≤ B) : Real.log x ≤ B := by
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0, Real.log_zero]
    exact hB
  · exact (Real.log_le_log hpos h).trans hy

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `E _ _ _ H Dw l c n Λ hU hfg hn a L hL hrd hf hDF hnL`. Set `_ : Fintype {τ : E →+* ℂ // InPsi H τ}` to `Fintype.ofFinite _`. Take `⟨e, hsym, hHH⟩` from `theta_letter_dictionary E H Dw l c n`. Establish `hint : ∀ x ∈ Λ.La, ∀ y ∈ Λ.La, IsIntegral ℤ (FD.herm 1 x y)` using `fun x hx => (mem_iff_herm_of_unimod hU x).1 hx`. Establish `hdual : ∀ x, (∀ y ∈ Λ.La, IsIntegral ℤ (FD.herm 1 x y)) → x ∈ Λ.La` using `fun x hx => (mem_iff_herm_of_unimod hU x).2 hx`.

Establish `hre : ∀ M : MvPolynomial (GlobalTheory.Harm.Var {τ : E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n)) c.F, rename e (rename e.symm M) = M` using `fun M => by`. Rewrite using `[rename_rename, Equiv.self_comp_symm, rename_id_apply]`. Establish `hre' : ∀ P : MvPolynomial (LtN Dw n) c.F, rename e.symm (rename e P) = P` using `fun P => by`. Rewrite using `[rename_rename, Equiv.symm_comp_self, rename_id_apply]`. Break down `hHH a with hzero | ⟨k, k', hdeg, hiff⟩` into its components or cases.

Use `⟨∅, by simp, fun P hP => ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[hzero P hP]`. Conclude with `Submodule.zero_mem _`. Break down `Nat.eq_zero_or_pos (DF Dw a) with h0 | hpos` into its components or cases. Establish `hconst : ∀ P, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → P = C (P.coeff 0)`.

Introduce `P hP`. Establish `h1` using `isHomogeneous_of_mem_rowHighest ((hiff P).1 hP)`. Rewrite `h1` using `[hdeg, h0]`. Establish `h2 : (rename e P).totalDegree = 0` using `Nat.le_zero.1 h1.totalDegree_le`. Establish `h3 : P.totalDegree = 0`.

Use `totalDegree_rename_le e.symm (rename e P)` as an intermediate fact. Rewrite `this` using `[hre', h2]`. Conclude with `Nat.le_zero.1 this`. Conclude with `totalDegree_eq_zero_iff_eq_C.1 h3`. Distinguish the cases in `h1 : (1 : MvPolynomial (LtN Dw n) c.F) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))`.

Use `⟨{1}, fun Q hQ => ?_, fun P hP => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hQ` using `[Finset.mem_singleton]`. Substitute `hQ` using the available equality. Use `⟨⟨h1, Subring.one_mem _⟩, fun σ' => ?_⟩` and prove the remaining obligations. Simplify using `[h0]`.

Rewrite using `[hconst P hP, ← mul_one (C (P.coeff 0)), ← smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (by simp))`. Simplify using `[h0]`. Use `⟨∅, by simp, fun P hP => ?_, by simp⟩` and prove the remaining obligations. Distinguish the cases in `hr : P.coeff 0 = 0`.

Rewrite using `[hconst P hP, hr, C_0]`. Conclude with `Submodule.zero_mem _`. It suffices to derive a contradiction. Apply `h1` to reduce the goal to its premises. Establish `hmem` using `(hiff P).1 hP`.

Rewrite `hmem` using `[hconst P hP, rename_C]`. Establish `h1' : (1 : MvPolynomial (GlobalTheory.Harm.Var {τ : E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n)) c.F) = C ((P.coeff 0)⁻¹ * P.coeff 0)`. Rewrite using `[inv_mul_cancel₀ hr, C_1]`. Rewrite using `[hiff, map_one, h1', C_mul, ← smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hmem`.

Establish `ha1 : 1 ≤ typeDegree k k'` using `by rw [hdeg]; exact hpos`. Take `⟨S0, hHa, hspan, hnorm, hcard⟩` from `short_harmonic_family_few_columns E n Λ.La hfg hint hdual Dw.p Dw.q hn {τ : E →+* ℂ // InPsi H τ} k k' ha1`. Establish `hinj` using `injective_embF_inPsi (H := H) c`. Establish `hsp` using `hspan c.F (fun t => embF c t.1) hinj`. Use `⟨S0.image fun s => rename e.symm (minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk)) fun t b kk => embF c t.1 (FD.cc (s.2 b kk))), fun Q hQ => ?_, fun P hP => ?_, ?_⟩` and prove the remaining obligations.

Take `⟨s, hs, rfl⟩` from `Finset.mem_image.1 hQ`. Establish `hM : minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk)) (fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) ∈ rowHighest c.F k k'`. Rewrite using `[← hsp]`. Conclude with `Submodule.subset_span ⟨s, Finset.mem_coe.2 hs, rfl⟩`. Establish `hS : minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk)) (fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) ∈ GlobalTheory.Harm.symO Dw.p Dw.q (fun t : {τ : E →+* ℂ // InPsi H τ} => embF c t.1) Λ.La`.

Use `hHa c.F (fun t => embF c t.1) s hs` as an intermediate fact. Unfold `GlobalTheory.Harm.Ha at this`. Conclude with `(Subalgebra.mem_toSubmodule _).1 (Submodule.mem_inf.1 this).2`. Use `⟨⟨(hiff _).2 (by rw [hre]; exact hM), (hsym Λ _).2 (by rw [hre]; exact hS)⟩, fun σ' => ?_⟩` and prove the remaining obligations. Rewrite using `[sum_norm_coeff_eq_l1Norm e σ', hre, map_minorProd]`.

Establish `hb` using `hnorm (fun t => σ'.comp (embF c t.1)) s hs`. Use `log_le_of_le_of_log_le (MvPoly.l1Norm_nonneg _) hb ?_ ?_` and prove the remaining obligations. Rewrite using `[hdeg]`. Conclude with `log_shortFamilyNumbers_le (Dw.p + Dw.q) n (DF Dw a) (FD.fdeg E) (FD.rdE E) L (one_le_add_of_one_le_typeDegree ha1) hn hpos one_le_fdeg one_le_rdE hL hrd hf hDF hnL`. Establish `hL0 : (0 : ℝ) ≤ L` using `by linarith`.

Check the signs of the components of the expression. Establish `h1 : rename e P ∈ Submodule.span c.F ((fun s : (Fin Dw.p → Fin n → E) × (Fin Dw.q → Fin n → E) => minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk)) fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) '' ↑S0)`. Rewrite using `[hsp]`. Conclude with `(hiff P).1 hP`. Establish `h2` using `Submodule.mem_map_of_mem (f := (rename (R := c.F) (⇑e.symm)).toLinearMap) h1`.

Rewrite `h2` using `[Submodule.map_span, ← Set.image_comp]`. Rewrite using `[Finset.coe_image]`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `exact (hre' P).symm`.

Consider the case `simp`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_short_harmL_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n), Λ.Unimod → Λ.La.FG → Dw.p + Dw.q ≤ n → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (L : ℝ), 2 ≤ L → Real.log (FD.rdE E) ≤ 2 * L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log (1 + DF Dw a) ≤ 2 * L → Real.log n ≤ L → ∃ S : Finset (MvPolynomial (LtN Dw n) c.F), (∀ Q ∈ S, Q ∈ harmL c Λ a ∧ ∀ σ' : c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ 140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a) ∧ (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P ∈ Submodule.span c.F (S : Set (MvPolynomial (LtN Dw n) c.F))) ∧ S.card ≤ ((2 * (Dw.p + Dw.q) + 1) * DF Dw a + 1) ^ (2 * FD.fdeg E * n * (2 * Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l c n Λ hU hfg hn a L hL hrd hf hDF hnL
  classical
  let _ : Fintype {τ : E →+* ℂ // InPsi H τ} := Fintype.ofFinite _
  obtain ⟨e, hsym, hHH⟩ := theta_letter_dictionary E H Dw l c n
  have hint : ∀ x ∈ Λ.La, ∀ y ∈ Λ.La, IsIntegral ℤ (FD.herm 1 x y) := fun x hx =>
    (mem_iff_herm_of_unimod hU x).1 hx
  have hdual : ∀ x, (∀ y ∈ Λ.La, IsIntegral ℤ (FD.herm 1 x y)) → x ∈ Λ.La := fun x hx =>
    (mem_iff_herm_of_unimod hU x).2 hx
  have hre : ∀ M : MvPolynomial (GlobalTheory.Harm.Var {τ : E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n)) c.F,
      rename e (rename e.symm M) = M := fun M => by
    rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]
  have hre' : ∀ P : MvPolynomial (LtN Dw n) c.F, rename e.symm (rename e P) = P := fun P => by
    rw [rename_rename, Equiv.symm_comp_self, rename_id_apply]
  rcases hHH a with hzero | ⟨k, k', hdeg, hiff⟩
  · refine ⟨∅, by simp, fun P hP => ?_, by simp⟩
    rw [hzero P hP]
    exact Submodule.zero_mem _
  rcases Nat.eq_zero_or_pos (DF Dw a) with h0 | hpos
  ·
    have hconst : ∀ P, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H)
        (fun τ i => a (τ, i)) → P = C (P.coeff 0) := by
      intro P hP
      have h1 := isHomogeneous_of_mem_rowHighest ((hiff P).1 hP)
      rw [hdeg, h0] at h1
      have h2 : (rename e P).totalDegree = 0 := Nat.le_zero.1 h1.totalDegree_le
      have h3 : P.totalDegree = 0 := by
        have := totalDegree_rename_le e.symm (rename e P)
        rw [hre', h2] at this
        exact Nat.le_zero.1 this
      exact totalDegree_eq_zero_iff_eq_C.1 h3
    by_cases h1 : (1 : MvPolynomial (LtN Dw n) c.F) ∈
        HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
    · refine ⟨{1}, fun Q hQ => ?_, fun P hP => ?_, ?_⟩
      · rw [Finset.mem_singleton] at hQ
        subst hQ
        refine ⟨⟨h1, Subring.one_mem _⟩, fun σ' => ?_⟩
        simp [h0]
      · rw [hconst P hP, ← mul_one (C (P.coeff 0)), ← smul_eq_C_mul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · simp [h0]
    · refine ⟨∅, by simp, fun P hP => ?_, by simp⟩
      by_cases hr : P.coeff 0 = 0
      · rw [hconst P hP, hr, C_0]
        exact Submodule.zero_mem _
      · exfalso
        apply h1
        have hmem := (hiff P).1 hP
        rw [hconst P hP, rename_C] at hmem
        have h1' : (1 : MvPolynomial (GlobalTheory.Harm.Var {τ : E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n)) c.F)
            = C ((P.coeff 0)⁻¹ * P.coeff 0) := by
          rw [inv_mul_cancel₀ hr, C_1]
        rw [hiff, map_one, h1', C_mul, ← smul_eq_C_mul]
        exact Submodule.smul_mem _ _ hmem

  have ha1 : 1 ≤ typeDegree k k' := by rw [hdeg]; exact hpos
  obtain ⟨S0, hHa, hspan, hnorm, hcard⟩ := short_harmonic_family_few_columns E n Λ.La hfg hint
    hdual Dw.p Dw.q hn {τ : E →+* ℂ // InPsi H τ} k k' ha1
  have hinj := injective_embF_inPsi (H := H) c
  have hsp := hspan c.F (fun t => embF c t.1) hinj
  refine ⟨S0.image fun s => rename e.symm (minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
    fun t b kk => embF c t.1 (FD.cc (s.2 b kk))), fun Q hQ => ?_, fun P hP => ?_, ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hQ
    have hM : minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
        (fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) ∈ rowHighest c.F k k' := by
      rw [← hsp]
      exact Submodule.subset_span ⟨s, Finset.mem_coe.2 hs, rfl⟩
    have hS : minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
        (fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) ∈
        GlobalTheory.Harm.symO Dw.p Dw.q (fun t : {τ : E →+* ℂ // InPsi H τ} => embF c t.1) Λ.La := by
      have := hHa c.F (fun t => embF c t.1) s hs
      unfold GlobalTheory.Harm.Ha at this
      exact (Subalgebra.mem_toSubmodule _).1 (Submodule.mem_inf.1 this).2
    refine ⟨⟨(hiff _).2 (by rw [hre]; exact hM), (hsym Λ _).2 (by rw [hre]; exact hS)⟩,
      fun σ' => ?_⟩
    rw [sum_norm_coeff_eq_l1Norm e σ', hre, map_minorProd]
    have hb := hnorm (fun t => σ'.comp (embF c t.1)) s hs
    refine log_le_of_le_of_log_le (MvPoly.l1Norm_nonneg _) hb ?_ ?_
    · rw [hdeg]
      exact log_shortFamilyNumbers_le (Dw.p + Dw.q) n (DF Dw a) (FD.fdeg E) (FD.rdE E) L
        (one_le_add_of_one_le_typeDegree ha1) hn hpos one_le_fdeg one_le_rdE hL hrd hf hDF hnL
    · have hL0 : (0 : ℝ) ≤ L := by linarith
      positivity
  · have h1 : rename e P ∈ Submodule.span c.F ((fun s : (Fin Dw.p → Fin n → E) ×
        (Fin Dw.q → Fin n → E) => minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
          fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) '' ↑S0) := by
      rw [hsp]
      exact (hiff P).1 hP
    have h2 := Submodule.mem_map_of_mem
      (f := (rename (R := c.F) (⇑e.symm)).toLinearMap) h1
    rw [Submodule.map_span, ← Set.image_comp] at h2
    rw [Finset.coe_image]
    convert h2 using 1
    all_goals first
      | exact (hre' P).symm
      | simp
  · calc _ ≤ S0.card := Finset.card_image_le
      _ ≤ _ := by rw [← hdeg]; exact hcard

end GlobalTheory.Harm
