import Formalism.SatakeDualWeyl.StatementC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant

noncomputable section

open Matrix

namespace Formalism.UG.P

open Formalism.UG

section Stdform

variable {n : Type} [Fintype n] [DecidableEq n]

def stdformQ (M : Matrix n n ℂ) (y : n → ℂ) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (y i) * M i j * y j).re

/- English proof (translation)
Unfold `stdformQ`. Conclude with `Complex.continuous_re.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ((Complex.continuous_conj.comp (continuous_apply i)).mul continuous_const).mul (continuous_apply j))`.
-/
theorem stdform_continuous_Q (M : Matrix n n ℂ) : Continuous (stdformQ M) := by
  unfold stdformQ
  exact Complex.continuous_re.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((Complex.continuous_conj.comp (continuous_apply i)).mul continuous_const).mul (continuous_apply j))

/- English proof (translation)
Unfold `stdformQ`. Use `congr 1`. Simplify using `only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, mul_assoc]`.
-/
theorem stdform_Q_dot (M : Matrix n n ℂ) (y : n → ℂ) :
    stdformQ M y = (star y ⬝ᵥ (M *ᵥ y)).re := by
  unfold stdformQ
  congr 1
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, mul_assoc]

/- English proof (translation)
Unfold `stdformQ`. Use `congr 1`. Use `Fintype.sum_equiv e.symm _ _ (fun k => ?_)` and prove the remaining obligations. Use `Fintype.sum_equiv e.symm _ _ (fun l => ?_)` and prove the remaining obligations. Simplify using `[Matrix.reindex_apply]`.
-/
theorem stdform_Q_reindex {m : Type} [Fintype m] [DecidableEq m] (M : Matrix n n ℂ) (e : n ≃ m)
    (y : n → ℂ) : stdformQ (M.reindex e e) (fun k => y (e.symm k)) = stdformQ M y := by
  unfold stdformQ
  congr 1
  refine Fintype.sum_equiv e.symm _ _ (fun k => ?_)
  refine Fintype.sum_equiv e.symm _ _ (fun l => ?_)
  simp [Matrix.reindex_apply]

/- English proof (translation)
Unfold `stdformQ`. Simplify using `only [Complex.re_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[Complex.mul_re, Complex.mul_im, hM i j]`.
-/
theorem stdform_Q_real (M : Matrix n n ℂ) (hM : ∀ i j, (M i j).im = 0) (y : n → ℂ) :
    stdformQ M y = stdformQ M (fun i => ((y i).re : ℂ)) + stdformQ M (fun i => ((y i).im : ℂ)) := by
  unfold stdformQ
  simp only [Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re, Complex.mul_im, hM i j]

/- English proof (translation)
Rewrite using `[Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stdform_normSq (z : ℂ) : (star z * z).re = Complex.normSq z := by
  rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

section Emb

variable {E : Type} [Field E]

/- English proof (translation)
Introduce `y`. Establish `hcont : Continuous fun y => c * stdformQ M y` using `continuous_const.mul (stdform_continuous_Q M)`. Establish `hall : ∀ x : n → E, 0 ≤ c * stdformQ M (fun i => τ (x i))`. Introduce `x`. Distinguish the cases in `hx : x = 0`.

Substitute `hx` using the available equality. Simplify using `[stdformQ]`. Conclude with `(hpos x hx).le`. Establish `hcl : IsClosed {y : n → ℂ | 0 ≤ c * stdformQ M y}` using `isClosed_le continuous_const hcont`. Distinguish the cases in `hre : ∃ e : E, (τ e).im ≠ 0`.

Take `⟨e0, he0⟩` from `hre`. Establish `hsurj : Function.Surjective fun ab : ℝ × ℝ => (ab.1 : ℂ) + (ab.2 : ℂ) * τ e0`. Introduce `z`. Use `⟨(z.re - z.im / (τ e0).im * (τ e0).re, z.im / (τ e0).im), ?_⟩` and prove the remaining obligations. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Simplify using `[he0]`. Establish `hg : DenseRange fun ab : ℝ × ℝ => (ab.1 : ℂ) + (ab.2 : ℂ) * τ e0` using `hsurj.denseRange`. Establish `hq : DenseRange fun ab : ℚ × ℚ => ((ab.1 : ℝ), (ab.2 : ℝ))` using `Rat.denseRange_cast.prodMap Rat.denseRange_cast`. Establish `h1 : DenseRange fun ab : ℚ × ℚ => τ ((ab.1 : E) + (ab.2 : E) * e0)`.

Establish `h0` using `hg.comp hq ((Complex.continuous_ofReal.comp continuous_fst).add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))`. Use `h0 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `ab`. Simplify using `[map_add, map_mul, map_ratCast]`. Establish `h2 : DenseRange fun v : n → ℚ × ℚ => fun i => τ (((v i).1 : E) + ((v i).2 : E) * e0)` using `DenseRange.piMap (fun _ => h1)`.

Establish `hsub : closure (Set.range fun v : n → ℚ × ℚ => fun i => τ (((v i).1 : E) + ((v i).2 : E) * e0)) ⊆ {y : n → ℂ | 0 ≤ c * stdformQ M y}`. Rewrite using `[hcl.closure_subset_iff]`. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `hall fun i => ((v i).1 : E) + ((v i).2 : E) * e0`. Conclude with `hsub (by rw [h2.closure_range]; trivial)`.

Use `push_neg at hre`. Establish `hM' : ∀ i j, (M i j).im = 0` using `fun i j => by`. Take `⟨e, he⟩` from `hM i j`. Rewrite using `[← he]`. Conclude with `hre e`.

Establish `hR : ∀ r : n → ℝ, 0 ≤ c * stdformQ M (fun i => ((r i : ℝ) : ℂ))`. Establish `hclR : IsClosed {r : n → ℝ | 0 ≤ c * stdformQ M (fun i => ((r i : ℝ) : ℂ))}` using `isClosed_le continuous_const (continuous_const.mul ((stdform_continuous_Q M).comp (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))))`. Establish `hd : DenseRange fun v : n → ℚ => fun i => ((v i : ℚ) : ℝ)` using `DenseRange.piMap (fun _ => Rat.denseRange_cast)`. Establish `hsub : closure (Set.range fun v : n → ℚ => fun i => ((v i : ℚ) : ℝ)) ⊆ {r : n → ℝ | 0 ≤ c * stdformQ M (fun i => ((r i : ℝ) : ℂ))}`. Rewrite using `[hclR.closure_subset_iff]`.

Introduce and unpack `_ ⟨v, rfl⟩`. Establish `h3` using `hall fun i => ((v i : ℚ) : E)`. Simplify `h3` using `[map_ratCast]`. Introduce `r`. Conclude with `hsub (by rw [hd.closure_range]; trivial)`.

Rewrite using `[stdform_Q_real M hM' y, mul_add]`. Conclude with `add_nonneg (hR _) (hR _)`.
-/
theorem stdform_psd (τ : E →+* ℂ) (M : Matrix n n ℂ) (hM : ∀ i j, ∃ e, τ e = M i j) (c : ℝ)
    (hpos : ∀ x : n → E, x ≠ 0 → 0 < c * stdformQ M (fun i => τ (x i))) :
    ∀ y, 0 ≤ c * stdformQ M y := by
  intro y
  have hcont : Continuous fun y => c * stdformQ M y := continuous_const.mul (stdform_continuous_Q M)
  have hall : ∀ x : n → E, 0 ≤ c * stdformQ M (fun i => τ (x i)) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp [stdformQ]
    · exact (hpos x hx).le
  have hcl : IsClosed {y : n → ℂ | 0 ≤ c * stdformQ M y} := isClosed_le continuous_const hcont
  by_cases hre : ∃ e : E, (τ e).im ≠ 0
  · obtain ⟨e0, he0⟩ := hre
    have hsurj : Function.Surjective fun ab : ℝ × ℝ => (ab.1 : ℂ) + (ab.2 : ℂ) * τ e0 := by
      intro z
      refine ⟨(z.re - z.im / (τ e0).im * (τ e0).re, z.im / (τ e0).im), ?_⟩
      apply Complex.ext
      · simp
      · simp [he0]
    have hg : DenseRange fun ab : ℝ × ℝ => (ab.1 : ℂ) + (ab.2 : ℂ) * τ e0 := hsurj.denseRange
    have hq : DenseRange fun ab : ℚ × ℚ => ((ab.1 : ℝ), (ab.2 : ℝ)) :=
      Rat.denseRange_cast.prodMap Rat.denseRange_cast
    have h1 : DenseRange fun ab : ℚ × ℚ => τ ((ab.1 : E) + (ab.2 : E) * e0) := by
      have h0 := hg.comp hq ((Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
      convert h0 using 1
      funext ab
      simp [map_add, map_mul, map_ratCast]
    have h2 : DenseRange fun v : n → ℚ × ℚ => fun i => τ (((v i).1 : E) + ((v i).2 : E) * e0) :=
      DenseRange.piMap (fun _ => h1)
    have hsub : closure (Set.range fun v : n → ℚ × ℚ => fun i => τ (((v i).1 : E) + ((v i).2 : E) * e0)) ⊆
        {y : n → ℂ | 0 ≤ c * stdformQ M y} := by
      rw [hcl.closure_subset_iff]
      rintro _ ⟨v, rfl⟩
      exact hall fun i => ((v i).1 : E) + ((v i).2 : E) * e0
    exact hsub (by rw [h2.closure_range]; trivial)
  · push_neg at hre
    have hM' : ∀ i j, (M i j).im = 0 := fun i j => by
      obtain ⟨e, he⟩ := hM i j
      rw [← he]
      exact hre e
    have hR : ∀ r : n → ℝ, 0 ≤ c * stdformQ M (fun i => ((r i : ℝ) : ℂ)) := by
      have hclR : IsClosed {r : n → ℝ | 0 ≤ c * stdformQ M (fun i => ((r i : ℝ) : ℂ))} :=
        isClosed_le continuous_const (continuous_const.mul ((stdform_continuous_Q M).comp
          (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))))
      have hd : DenseRange fun v : n → ℚ => fun i => ((v i : ℚ) : ℝ) :=
        DenseRange.piMap (fun _ => Rat.denseRange_cast)
      have hsub : closure (Set.range fun v : n → ℚ => fun i => ((v i : ℚ) : ℝ)) ⊆
          {r : n → ℝ | 0 ≤ c * stdformQ M (fun i => ((r i : ℝ) : ℂ))} := by
        rw [hclR.closure_subset_iff]
        rintro _ ⟨v, rfl⟩
        have h3 := hall fun i => ((v i : ℚ) : E)
        simpa [map_ratCast] using h3
      intro r
      exact hsub (by rw [hd.closure_range]; trivial)
    rw [stdform_Q_real M hM' y, mul_add]
    exact add_nonneg (hR _) (hR _)

end Emb

end Stdform

/- English proof (translation)
Use `letI : Algebra F ℂ := ((algebraMap ℝ ℂ).comp ι).toAlgebra`. Use `haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.tower_top (K := ℚ) F`. Use `⟨(IsAlgClosed.lift : E →ₐ[F] ℂ).toRingHom, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Conclude with `(IsAlgClosed.lift : E →ₐ[F] ℂ).commutes x`.
-/
theorem stdform_ext {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (ι : F →+* ℝ) :
    ∃ τ : E →+* ℂ, τ.comp (algebraMap F E) = (algebraMap ℝ ℂ).comp ι := by
  letI : Algebra F ℂ := ((algebraMap ℝ ℂ).comp ι).toAlgebra
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  refine ⟨(IsAlgClosed.lift : E →ₐ[F] ℂ).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : E →ₐ[F] ℂ).commutes x

section Inv

variable {n : Type} [Fintype n] [DecidableEq n] {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Establish `h` using `RingHom.congr_fun hσ e`. Simplify using `using h`.
-/
theorem stdform_conj (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (e : E) :
    τ (σ e) = starRingEnd ℂ (τ e) := by
  have h := RingHom.congr_fun hσ e
  simpa using h

/- English proof (translation)
Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[stdform_conj σ τ hσ (σ e), stdform_conj σ τ hσ e, Complex.conj_conj]`.
-/
theorem stdform_invol (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (e : E) : σ (σ e) = e := by
  apply τ.injective
  rw [stdform_conj σ τ hσ (σ e), stdform_conj σ τ hσ e, Complex.conj_conj]

/- English proof (translation)
Simplify using `only [hform, map_sum, map_mul, Matrix.map_apply, AlgHom.coe_toRingHom, stdform_conj σ τ hσ]`.
-/
theorem stdform_hform_map (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (J : Matrix n n E) (x : n → E) :
    τ (hform (σ : E →+* E) J x x) =
      ∑ i, ∑ j, starRingEnd ℂ (τ (x i)) * (J.map τ) i j * τ (x j) := by
  simp only [hform, map_sum, map_mul, Matrix.map_apply, AlgHom.coe_toRingHom, stdform_conj σ τ hσ]

/- English proof (translation)
Unfold `IsHerm at hJ`. Establish `hJ' : ∀ i j, σ (J i j) = J j i` using `fun i j => by`. Establish `h` using `congrFun (congrFun hJ j) i`. Simplify `h` using `[cT]`. Simplify using `only [hform, map_sum, map_mul, AlgHom.coe_toRingHom, stdform_invol σ τ hσ, hJ']`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stdform_hform_fixed (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (J : Matrix n n E)
    (hJ : IsHerm (σ : E →+* E) J) (x : n → E) :
    σ (hform (σ : E →+* E) J x x) = hform (σ : E →+* E) J x x := by
  unfold IsHerm at hJ
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => by
    have h := congrFun (congrFun hJ j) i
    simpa [cT] using h
  simp only [hform, map_sum, map_mul, AlgHom.coe_toRingHom, stdform_invol σ τ hσ, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Use `show (∑ i, ∑ j, starRingEnd ℂ (τ (x i)) * (J.map τ) i j * τ (x j)).re = ι a`. Rewrite using `[← stdform_hform_map σ τ hσ J x, ← ha]`. Establish `h` using `RingHom.congr_fun hι a`. Simplify using `only [RingHom.comp_apply] at h`. Rewrite using `[h]`.

Simplify using the standard rewrite rules.
-/
theorem stdform_Q_eq (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (J : Matrix n n E) (ι : F →+* ℝ)
    (hι : τ.comp (algebraMap F E) = (algebraMap ℝ ℂ).comp ι) (x : n → E) (a : F)
    (ha : algebraMap F E a = hform (σ : E →+* E) J x x) :
    stdformQ (J.map τ) (fun i => τ (x i)) = ι a := by
  show (∑ i, ∑ j, starRingEnd ℂ (τ (x i)) * (J.map τ) i j * τ (x j)).re = ι a
  rw [← stdform_hform_map σ τ hσ J x, ← ha]
  have h := RingHom.congr_fun hι a
  simp only [RingHom.comp_apply] at h
  rw [h]
  simp

end Inv

section Sign

variable {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Rewrite using `[Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma re_conj_mul_self_eq_normSq (z : ℂ) : (starRingEnd ℂ z * z).re = Complex.normSq z := by
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

/- English proof (translation)
Establish `hPP : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hy' : (fun k => y (e.symm k)) = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ (((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ (fun k => y (e.symm k)))`. Rewrite using `[Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]`. Take `⟨x, hx⟩ : ∃ x, (fun k => y (e.symm k)) = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ x` from `⟨_, hy'⟩`.

Use `⟨x, ?_, ?_⟩` and prove the remaining obligations. Introduce `hy h0`. Apply `hy` to reduce the goal to its premises. Rewrite `hx` using `[h0, Matrix.mulVec_zero]`. Use function extensionality and compare the values at `i`.

Simplify using `using congrFun hx (e i)`. Rewrite using `[← stdform_Q_reindex M e y, stdform_Q_dot, hx, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP]`. Simplify using `[Jpq, dotProduct, Matrix.fromBlocks_mulVec, Fintype.sum_sum_type, Complex.re_sum, stdform_normSq, re_conj_mul_self_eq_normSq, sub_eq_add_neg, Matrix.neg_mulVec, Matrix.one_mulVec, Complex.normSq_apply, Complex.neg_re, Complex.neg_im, mul_neg, Finset.sum_neg_distrib]`.
-/
theorem stdform_sig_diag {p q : ℕ} (M : Matrix n n ℂ) (e : n ≃ Fin p ⊕ Fin q)
    (P : GL (Fin p ⊕ Fin q) ℂ)
    (hP : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * M.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q) (y : n → ℂ) :
    ∃ x : Fin p ⊕ Fin q → ℂ, (y ≠ 0 → x ≠ 0) ∧
      stdformQ M y = (∑ i, Complex.normSq (x (Sum.inl i))) - ∑ j, Complex.normSq (x (Sum.inr j)) := by
  have hPP : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hy' : (fun k => y (e.symm k)) = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ (((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ (fun k => y (e.symm k))) := by
    rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  obtain ⟨x, hx⟩ : ∃ x, (fun k => y (e.symm k)) = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ x := ⟨_, hy'⟩
  refine ⟨x, ?_, ?_⟩
  · intro hy h0
    apply hy
    rw [h0, Matrix.mulVec_zero] at hx
    funext i
    simpa using congrFun hx (e i)
  · rw [← stdform_Q_reindex M e y, stdform_Q_dot, hx, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP]
    simp [Jpq, dotProduct, Matrix.fromBlocks_mulVec, Fintype.sum_sum_type, Complex.re_sum, stdform_normSq,
      re_conj_mul_self_eq_normSq, sub_eq_add_neg, Matrix.neg_mulVec, Matrix.one_mulVec, Complex.normSq_apply,
      Complex.neg_re, Complex.neg_im, mul_neg, Finset.sum_neg_distrib]

/- English proof (translation)
Take `⟨e, P, hP⟩` from `hs`. Take `⟨x, hx0, hQ⟩` from `stdform_sig_diag M e P hP y`. Rewrite using `[hQ]`. Simplify using `only [Fin.sum_univ_zero, sub_zero]`. Take `⟨k, hk⟩` from `Function.ne_iff.mp (hx0 hy)`.

Break down `k with i | i` into its components or cases. Conclude with `Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hk⟩`. Conclude with `Fin.elim0 i`.
-/
theorem stdform_sig_pos {p : ℕ} (M : Matrix n n ℂ) (hs : HasSignature M p 0) (y : n → ℂ)
    (hy : y ≠ 0) : 0 < stdformQ M y := by
  obtain ⟨e, P, hP⟩ := hs
  obtain ⟨x, hx0, hQ⟩ := stdform_sig_diag M e P hP y
  rw [hQ]
  simp only [Fin.sum_univ_zero, sub_zero]
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (hx0 hy)
  rcases k with i | i
  · exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hk⟩
  · exact Fin.elim0 i

/- English proof (translation)
Take `⟨e, P, hP⟩` from `hs`. Take `⟨x, hx0, hQ⟩` from `stdform_sig_diag M e P hP y`. Rewrite using `[hQ]`. Simplify using `only [Fin.sum_univ_zero, zero_sub, neg_lt_zero]`. Take `⟨k, hk⟩` from `Function.ne_iff.mp (hx0 hy)`.

Break down `k with i | i` into its components or cases. Conclude with `Fin.elim0 i`. Conclude with `Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hk⟩`.
-/
theorem stdform_sig_neg {q : ℕ} (M : Matrix n n ℂ) (hs : HasSignature M 0 q) (y : n → ℂ)
    (hy : y ≠ 0) : stdformQ M y < 0 := by
  obtain ⟨e, P, hP⟩ := hs
  obtain ⟨x, hx0, hQ⟩ := stdform_sig_diag M e P hP y
  rw [hQ]
  simp only [Fin.sum_univ_zero, zero_sub, neg_lt_zero]
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (hx0 hy)
  rcases k with i | i
  · exact Fin.elim0 i
  · exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hk⟩

/- English proof (translation)
Use `⟨(Fintype.equivFin n).trans (Equiv.sumEmpty _ _).symm, 1, ?_⟩` and prove the remaining obligations. Simplify using `[Jpq, cT]`. Use extensionality with `(i | i) (j | j)`. Apply the tactic sequence `all_goals first | exact Fin.elim0 i | exact Fin.elim0 j | simp [Matrix.one_apply]`.
-/
theorem stdform_sig_one : HasSignature (1 : Matrix n n ℂ) (Fintype.card n) 0 := by
  refine ⟨(Fintype.equivFin n).trans (Equiv.sumEmpty _ _).symm, 1, ?_⟩
  simp [Jpq, cT]
  ext (i | i) (j | j)
  all_goals first | exact Fin.elim0 i | exact Fin.elim0 j | simp [Matrix.one_apply]

/- English proof (translation)
Use `⟨(Fintype.equivFin n).trans (Equiv.emptySum _ _).symm, 1, ?_⟩` and prove the remaining obligations. Simplify using `[Jpq, cT]`. Use extensionality with `(i | i) (j | j)`. Apply the tactic sequence `all_goals first | exact Fin.elim0 i | exact Fin.elim0 j | simp [Matrix.one_apply]`.
-/
theorem stdform_sig_neg_one : HasSignature (-1 : Matrix n n ℂ) 0 (Fintype.card n) := by
  refine ⟨(Fintype.equivFin n).trans (Equiv.emptySum _ _).symm, 1, ?_⟩
  simp [Jpq, cT]
  ext (i | i) (j | j)
  all_goals first | exact Fin.elim0 i | exact Fin.elim0 j | simp [Matrix.one_apply]

end Sign

/- English proof (translation)
Introduce `F E _ _ _ n _ _ σ J ι τ hσ hι hfix hJ hdet`. Establish `hfixed : ∀ x : n → E, ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x` using `fun x => hfix _ (stdform_hform_fixed σ τ hσ J hJ x)`. Establish `hτx : ∀ x : n → E, x ≠ 0 → (fun i => τ (x i)) ≠ 0`. Introduce `x hx h`. Apply `hx` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Use `congrFun h i` as an intermediate fact. Conclude with `τ.injective (by simpa using this)`. Prove the components needed by the constructor for the conclusion. Introduce `hdef`.

Establish `hMh : IsHerm (starRingEnd ℂ) (J.map τ)`. Establish `hJ' : ∀ i j, σ (J i j) = J j i` using `fun i j => by`. Use `congrFun (congrFun hJ j) i` as an intermediate fact. Simplify `this` using `[cT]`. Use extensionality with `i j`.

Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[← stdform_conj σ τ hσ, hJ']`. Establish `hMdet : IsUnit (J.map τ).det`. Establish `h` using `(RingHom.map_det τ J).symm`. Rewrite using `[show (J.map τ) = τ.mapMatrix J from rfl, h]`.

Conclude with `hdet.map τ`. Take `⟨p, q, hs⟩` from `signature_exists n (J.map τ) hMh hMdet`. Take `⟨hcard, Q, hQ⟩` from `sig_data (J.map τ) p q hs`. Establish `hM : ∀ i j, ∃ e, τ e = (J.map τ) i j` using `fun i j => ⟨J i j, rfl⟩`. Break down `hdef with hpos | hneg` into its components or cases.

Establish `hpsd` using `stdform_psd τ (J.map τ) hM 1 (fun x hx => by`. Take `⟨a, ha, hιa⟩` from `hpos x hx`. Rewrite using `[stdform_Q_eq σ τ hσ J ι hι x a ha, one_mul]`. Conclude with `hιa)`. Establish `hq : q = 0`.

Assume the negation of the conclusion as `hq0`. Establish `hv` using `sig_quad (J.map τ) Q hQ (Pi.single (Sum.inr ⟨0, Nat.pos_of_ne_zero hq0⟩) 1)`. Use `hpsd (Q *ᵥ Pi.single (Sum.inr ⟨0, Nat.pos_of_ne_zero hq0⟩) 1)` as an intermediate fact. Rewrite `this` using `[stdform_Q_dot, hv]`. Simplify using `[Pi.single_apply] at this`.

Evaluate the numerical expressions using `at this`. Substitute `hq` using the available equality. Establish `hp : p = Fintype.card n` using `by omega`. Substitute `hp` using the available equality. Conclude with `Or.inl hs`.

Establish `hpsd` using `stdform_psd τ (J.map τ) hM (-1) (fun x hx => by`. Take `⟨a, ha, hιa⟩` from `hneg x hx`. Rewrite using `[stdform_Q_eq σ τ hσ J ι hι x a ha]`. Use the proof step `linarith)`. Establish `hp : p = 0`.

Assume the negation of the conclusion as `hp0`. Establish `hv` using `sig_quad (J.map τ) Q hQ (Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hp0⟩) 1)`. Use `hpsd (Q *ᵥ Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hp0⟩) 1)` as an intermediate fact. Rewrite `this` using `[stdform_Q_dot, hv]`. Simplify using `[Pi.single_apply] at this`.

Evaluate the numerical expressions using `at this`. Substitute `hp` using the available equality. Establish `hq : q = Fintype.card n` using `by omega`. Substitute `hq` using the available equality. Conclude with `Or.inr hs`.

Introduce and unpack `(hs | hs)`. Use `left`. Introduce `x hx`. Take `⟨a, ha⟩` from `hfixed x`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations.

Rewrite using `[← stdform_Q_eq σ τ hσ J ι hι x a ha]`. Conclude with `stdform_sig_pos _ hs _ (hτx x hx)`. Use `right`. Introduce `x hx`. Take `⟨a, ha⟩` from `hfixed x`.

Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[← stdform_Q_eq σ τ hσ J ι hι x a ha]`. Conclude with `stdform_sig_neg _ hs _ (hτx x hx)`.
-/
theorem definite_form_signature : Formalism.UG.DefSig := by
  intro F E _ _ _ n _ _ σ J ι τ hσ hι hfix hJ hdet
  have hfixed : ∀ x : n → E, ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x :=
    fun x => hfix _ (stdform_hform_fixed σ τ hσ J hJ x)
  have hτx : ∀ x : n → E, x ≠ 0 → (fun i => τ (x i)) ≠ 0 := by
    intro x hx h
    apply hx
    funext i
    have := congrFun h i
    exact τ.injective (by simpa using this)
  constructor
  · intro hdef
    have hMh : IsHerm (starRingEnd ℂ) (J.map τ) := by
      have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => by
        have := congrFun (congrFun hJ j) i
        simpa [cT] using this
      ext i j
      simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
      rw [← stdform_conj σ τ hσ, hJ']
    have hMdet : IsUnit (J.map τ).det := by
      have h := (RingHom.map_det τ J).symm
      rw [show (J.map τ) = τ.mapMatrix J from rfl, h]
      exact hdet.map τ
    obtain ⟨p, q, hs⟩ := signature_exists n (J.map τ) hMh hMdet
    obtain ⟨hcard, Q, hQ⟩ := sig_data (J.map τ) p q hs
    have hM : ∀ i j, ∃ e, τ e = (J.map τ) i j := fun i j => ⟨J i j, rfl⟩
    rcases hdef with hpos | hneg
    · have hpsd := stdform_psd τ (J.map τ) hM 1 (fun x hx => by
        obtain ⟨a, ha, hιa⟩ := hpos x hx
        rw [stdform_Q_eq σ τ hσ J ι hι x a ha, one_mul]
        exact hιa)
      have hq : q = 0 := by
        by_contra hq0
        have hv := sig_quad (J.map τ) Q hQ (Pi.single (Sum.inr ⟨0, Nat.pos_of_ne_zero hq0⟩) 1)
        have := hpsd (Q *ᵥ Pi.single (Sum.inr ⟨0, Nat.pos_of_ne_zero hq0⟩) 1)
        rw [stdform_Q_dot, hv] at this
        simp [Pi.single_apply] at this
        norm_num at this
      subst hq
      have hp : p = Fintype.card n := by omega
      subst hp
      exact Or.inl hs
    · have hpsd := stdform_psd τ (J.map τ) hM (-1) (fun x hx => by
        obtain ⟨a, ha, hιa⟩ := hneg x hx
        rw [stdform_Q_eq σ τ hσ J ι hι x a ha]
        linarith)
      have hp : p = 0 := by
        by_contra hp0
        have hv := sig_quad (J.map τ) Q hQ (Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hp0⟩) 1)
        have := hpsd (Q *ᵥ Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hp0⟩) 1)
        rw [stdform_Q_dot, hv] at this
        simp [Pi.single_apply] at this
        norm_num at this
      subst hp
      have hq : q = Fintype.card n := by omega
      subst hq
      exact Or.inr hs
  · rintro (hs | hs)
    · left
      intro x hx
      obtain ⟨a, ha⟩ := hfixed x
      refine ⟨a, ha, ?_⟩
      rw [← stdform_Q_eq σ τ hσ J ι hι x a ha]
      exact stdform_sig_pos _ hs _ (hτx x hx)
    · right
      intro x hx
      obtain ⟨a, ha⟩ := hfixed x
      refine ⟨a, ha, ?_⟩
      rw [← stdform_Q_eq σ τ hσ J ι hι x a ha]
      exact stdform_sig_neg _ hs _ (hτx x hx)

/- English proof (translation)
Introduce `F E _ _ _ _ _ n _ _ σ hσ hfix hF`. Establish `hH1 : IsHerm (σ : E →+* E) (1 : Matrix n n E)` using `cT_one _`. Establish `hHm : IsHerm (σ : E →+* E) (-1 : Matrix n n E)`. Unfold `IsHerm cT`. Use extensionality with `i j`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[one_apply, h, Ne.symm h]`. Use `⟨hH1, ⟨hF, fun ι => ?_⟩, ⟨hF, fun ι => ?_⟩⟩` and prove the remaining obligations.

Take `⟨τ, hτ⟩` from `stdform_ext (E := E) ι`. Use `(definite_form_signature F E n σ 1 ι τ (hσ τ) hτ hfix hH1 (by simp)).mpr (Or.inl ?_)` and prove the remaining obligations. Rewrite using `[Matrix.map_one _ (map_zero τ) (map_one τ)]`. Conclude with `stdform_sig_one`. Take `⟨τ, hτ⟩` from `stdform_ext (E := E) ι`.

Use `(definite_form_signature F E n σ (-1) ι τ (hσ τ) hτ hfix hHm ((Matrix.isUnit_iff_isUnit_det _).mp isUnit_one.neg)).mpr (Or.inr ?_)` and prove the remaining obligations. Establish `: (-1 : Matrix n n E).map τ = -1`. Rewrite using `[Matrix.map_neg _ (map_neg τ), Matrix.map_one _ (map_zero τ) (map_one τ)]`. Rewrite using `[this]`. Conclude with `stdform_sig_neg_one`.
-/
theorem standard_hermitian_form_definite : Formalism.UG.StdFormDef := by
  intro F E _ _ _ _ _ n _ _ σ hσ hfix hF
  have hH1 : IsHerm (σ : E →+* E) (1 : Matrix n n E) := cT_one _
  have hHm : IsHerm (σ : E →+* E) (-1 : Matrix n n E) := by
    unfold IsHerm cT
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [one_apply, h, Ne.symm h]
  refine ⟨hH1, ⟨hF, fun ι => ?_⟩, ⟨hF, fun ι => ?_⟩⟩
  · obtain ⟨τ, hτ⟩ := stdform_ext (E := E) ι
    refine (definite_form_signature F E n σ 1 ι τ (hσ τ) hτ hfix hH1 (by simp)).mpr (Or.inl ?_)
    rw [Matrix.map_one _ (map_zero τ) (map_one τ)]
    exact stdform_sig_one
  · obtain ⟨τ, hτ⟩ := stdform_ext (E := E) ι
    refine (definite_form_signature F E n σ (-1) ι τ (hσ τ) hτ hfix hHm
      ((Matrix.isUnit_iff_isUnit_det _).mp isUnit_one.neg)).mpr (Or.inr ?_)
    have : (-1 : Matrix n n E).map τ = -1 := by
      rw [Matrix.map_neg _ (map_neg τ), Matrix.map_one _ (map_zero τ) (map_one τ)]
    rw [this]
    exact stdform_sig_neg_one

end Formalism.UG.P
