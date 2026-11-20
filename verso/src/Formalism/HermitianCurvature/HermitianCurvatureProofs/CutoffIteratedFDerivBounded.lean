import Formalism.HermitianCurvature.HermitianCurvatureProofs.DminStarPd

open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

/- English proof (translation)
Introduce `g hg`. Take `⟨f', hf', V, hV, hgV, hfe⟩` from `h g hg`. Use `⟨V, f', hV, hgV, (hf'.of_le ?_).contDiffOn, fun g' hg' hG => hfe g' hG hg'⟩` and prove the remaining obligations. Conclude with `WithTop.coe_le_coe.mpr le_top`.
-/
lemma ckOn_of_lss {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : Mat k r → E} {S : Set (Mat k r)}
    (h : LSS f S) (m : ℕ∞) : CkOn m S f := by
  intro g hg
  obtain ⟨f', hf', V, hV, hgV, hfe⟩ := h g hg
  refine ⟨V, f', hV, hgV, (hf'.of_le ?_).contDiffOn, fun g' hg' hG => hfe g' hG hg'⟩
  exact WithTop.coe_le_coe.mpr le_top

section fac

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Establish `hSG : S ⊆ GV k r` using `fun g hg => (hS g hg).1`. Introduce `es`. Proceed by induction on `es with`. Consider the case `nil`. Introduce `_`.

Establish `e0 : C6.Epart fib ([] : List (Fin nf × List (Mat k r))) = fun _ => 1`. Use function extensionality and compare the values at `g`. Simplify using `[C6.Epart]`. Rewrite using `[e0]`. Simplify using `using ubl_const (1 : C6.EndH Wp Wq) hSG n (3 * (r + 1))`.

Consider the case `cons e es ih`. Introduce `hes`. Establish `hA` using `ubl_fib D (fib e.1) (hfib e.1) hε hS e.2 (hes e (by simp)) n`. Establish `hB` using `ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))`. Establish `hL` using `ubl_clm ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ) hSG hA`.

Establish `hAB` using `ubl_app hSG hL hB`. Establish `e1 : C6.Epart fib (e :: es) = fun g => ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ (Rw e.2 (fib e.1) g)) (C6.Epart fib es g)`. Use function extensionality and compare the values at `g`. Simplify using `[C6.Epart]`. Rewrite using `[e1]`.

Use `hAB using 2` and compare the differences between its conclusion and the goal. Simplify using `only [List.map_cons, List.sum_cons]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma ubl_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)}
    (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (n : ℕ) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ X ∈ e.2, inLie k r X) →
      UBL (C6.Epart fib es) S n (3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  intro es
  induction es with
  | nil =>
    intro _
    have e0 : C6.Epart fib ([] : List (Fin nf × List (Mat k r))) = fun _ => 1 := by
      funext g
      simp [C6.Epart]
    rw [e0]
    simpa using ubl_const (1 : C6.EndH Wp Wq) hSG n (3 * (r + 1))
  | cons e es ih =>
    intro hes
    have hA := ubl_fib D (fib e.1) (hfib e.1) hε hS e.2 (hes e (by simp)) n
    have hB := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    have hL := ubl_clm ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ) hSG hA
    have hAB := ubl_app hSG hL hB
    have e1 : C6.Epart fib (e :: es) =
        fun g => ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ
          (Rw e.2 (fib e.1) g)) (C6.Epart fib es g) := by
      funext g
      simp [C6.Epart]
    rw [e1]
    convert hAB using 2
    simp only [List.map_cons, List.sum_cons]
    ring

/- English proof (translation)
Establish `hSG : S ⊆ GV k r` using `fun g hg => (hS g hg).1`. Establish `hP'` using `ubl_poly hP S hSG n (3 * (r + 1))`. Establish `hM` using `ubl_mono hSG (ubl_monoM D L a b c hab hSG hc₀ hSD hSGf n) le_rfl (show 2 * r + 2 ≤ 3 * (r + 1) by omega)`. Establish `hPM` using `ubl_mul hSG hP' hM`. Establish `hE` using `ubl_epart D fib hfib hε hS n es hes`.

Set `Lm : ℂ →L[ℝ] (C6.EndH Wp Wq →L[ℂ] C6.EndH Wp Wq)` to `(ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (ContinuousLinearMap.id ℂ (C6.EndH Wp Wq))).restrictScalars ℝ`. Establish `hA` using `ubl_clm Lm hSG hPM`. Establish `hAE` using `ubl_app hSG hA hE`. Establish `e1 : (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) = fun g => Lm (P g * C6.monoM D a b c g) (C6.Epart fib es g)`. Use function extensionality and compare the values at `g`.

Simplify using `[Lm]`. Rewrite using `[e1]`. Simplify using `using hAE`.
-/
lemma ubl_coefP (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) (L : Finset (Fin (r + 2))) {κ : ℕ} (P : Mat k r → ℂ)
    (a b : Fin (r + 2) → ℕ) (c : ℕ) (es : List (Fin nf × List (Mat k r))) (hP : U.IsPolyDeg κ P)
    (hab : ∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) (hes : ∀ e ∈ es, ∀ X ∈ e.2, inLie k r X)
    {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)} (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hSD : ∀ g ∈ S, ∀ l, (l ∈ L ∨ l = Fin.last (r + 1)) → c₀ ≤ Complex.normSq (Dmin k r D.z D.z' g l))
    (hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r D.z D.z' g : ℝ) : ℂ)) (n : ℕ) :
    UBL (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) S n
      (κ + 3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  have hP' := ubl_poly hP S hSG n (3 * (r + 1))
  have hM := ubl_mono hSG (ubl_monoM D L a b c hab hSG hc₀ hSD hSGf n) le_rfl
    (show 2 * r + 2 ≤ 3 * (r + 1) by omega)
  have hPM := ubl_mul hSG hP' hM
  have hE := ubl_epart D fib hfib hε hS n es hes
  let Lm : ℂ →L[ℝ] (C6.EndH Wp Wq →L[ℂ] C6.EndH Wp Wq) :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (ContinuousLinearMap.id ℂ (C6.EndH Wp Wq))).restrictScalars ℝ
  have hA := ubl_clm Lm hSG hPM
  have hAE := ubl_app hSG hA hE
  have e1 : (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) =
      fun g => Lm (P g * C6.monoM D a b c g) (C6.Epart fib es g) := by
    funext g
    simp [Lm]
  rw [e1]
  simpa using hAE

end fac

section cut

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Take `⟨q, -, hq⟩` from `hP`. Rewrite using `[show P = fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))) q from funext hq]`. Use `clear hq`. Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simpa using contDiff_const`.

Consider the case `add p q hp hq => simpa only [map_add] using hp.add hq`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, MvPolynomial.eval_X]`. Use `hp.mul ?_` and prove the remaining obligations. Break down `i with x | x` into its components or cases.

Conclude with `contDiff_apply_apply ℝ ℂ x.1 x.2`. Conclude with `Complex.conjCLE.contDiff.comp (contDiff_apply_apply ℝ ℂ x.1 x.2)`.
-/
private lemma contDiff_of_isPolyDeg {N κ : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg κ P) :
    ContDiff ℝ ∞ P := by
  obtain ⟨q, -, hq⟩ := hP
  rw [show P = fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2)
    (fun x => star (g x.1 x.2))) q from funext hq]
  clear hq
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    rcases i with x | x
    · exact contDiff_apply_apply ℝ ℂ x.1 x.2
    · exact Complex.conjCLE.contDiff.comp (contDiff_apply_apply ℝ ℂ x.1 x.2)

/- English proof (translation)
Take `⟨hs, ⟨δ, hδ, h0⟩, h1⟩` from `hχ`. Use `set Φ : ℂ → ℂ := fun y => ((χ₀ (Complex.normSq y / de) : ℝ) : ℂ) with hΦdef`. Establish `hns : ContDiff ℝ ∞ (fun y : ℂ => Complex.normSq y)`. Simplify using `only [Complex.normSq_apply]`. Conclude with `(Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)`.

Establish `hΦ : ContDiff ℝ ∞ Φ` using `Complex.ofRealCLM.contDiff.comp (hs.comp (hns.div_const de))`. Establish `hc : Continuous (iteratedFDeriv ℝ j Φ)` using `hΦ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (by exact_mod_cast le_top))`. Establish `hconst : ∀ (c x y : ℂ), iteratedFDeriv ℝ j (fun _ : ℂ => c) x = iteratedFDeriv ℝ j (fun _ : ℂ => c) y`. Introduce `c x y`. Break down `Nat.eq_zero_or_pos j with rfl | hj` into its components or cases.

Simplify using `[iteratedFDeriv_zero_eq_comp]`. Rewrite using `[iteratedFDeriv_const_of_ne hj.ne']`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨c, R, hR0, hloc⟩ : ∃ c : ℂ, ∃ R : ℝ, 0 ≤ R ∧ ∀ y : ℂ, R < ‖y‖ → Φ =ᶠ[nhds y] fun _ => c := by`. Break down `le_or_gt de 0 with hde | hde` into its components or cases.

Use `⟨0, 0, le_rfl, fun y _ => Filter.Eventually.of_forall fun z => ?_⟩` and prove the remaining obligations. Establish `hz : Complex.normSq z / de ≤ 0` using `div_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg z) hde`. Use `show ((χ₀ (Complex.normSq z / de) : ℝ) : ℂ) = 0`. Rewrite using `[h0 _ (by linarith)]`. Simplify using the standard rewrite rules.

Use `⟨1, de + 1, by linarith, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hopen : IsOpen {z : ℂ | de + 1 < ‖z‖}` using `isOpen_lt continuous_const continuous_norm`. Use `filter_upwards [hopen.mem_nhds hy] with z hz`. Establish `hz' : de + 1 < ‖z‖` using `hz`. Establish `hn : de ≤ Complex.normSq z`.

Rewrite using `[Complex.normSq_eq_norm_sq]`. Use polynomial arithmetic with `[norm_nonneg z]`. Establish `h1' : 1 ≤ Complex.normSq z / de`. Rewrite using `[le_div_iff₀ hde]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `show ((χ₀ (Complex.normSq z / de) : ℝ) : ℂ) = 1`. Rewrite using `[h1 _ h1']`. Simplify using the standard rewrite rules. Take `⟨B, hB⟩` from `(isCompact_closedBall (0 : ℂ) (R + 1)).exists_bound_of_continuousOn hc.continuousOn`. Establish `y0n : ‖((R + 1 : ℝ) : ℂ)‖ = R + 1`.

Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]`. Use `⟨B, fun y => ?_⟩` and prove the remaining obligations. Break down `le_or_gt ‖y‖ (R + 1) with hy | hy` into its components or cases. Conclude with `hB y (by rw [mem_closedBall_zero_iff]; exact hy)`. Establish `e1` using `((hloc y (by linarith)).iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds`.

Establish `e2` using `((hloc ((R + 1 : ℝ) : ℂ) (by rw [y0n]; linarith)).iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds`. Rewrite using `[e1, hconst c y ((R + 1 : ℝ) : ℂ), ← e2]`. Conclude with `hB _ (by rw [mem_closedBall_zero_iff, y0n])`.
-/
private lemma exists_bound_iteratedFDeriv_cutoff_normSq {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (j : ℕ) :
    ∃ B : ℝ, ∀ y : ℂ,
      ‖iteratedFDeriv ℝ j (fun y : ℂ => ((χ₀ (Complex.normSq y / de) : ℝ) : ℂ)) y‖ ≤ B := by
  obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
  set Φ : ℂ → ℂ := fun y => ((χ₀ (Complex.normSq y / de) : ℝ) : ℂ) with hΦdef
  have hns : ContDiff ℝ ∞ (fun y : ℂ => Complex.normSq y) := by
    simp only [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hΦ : ContDiff ℝ ∞ Φ := Complex.ofRealCLM.contDiff.comp (hs.comp (hns.div_const de))
  have hc : Continuous (iteratedFDeriv ℝ j Φ) :=
    hΦ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (by exact_mod_cast le_top))
  have hconst : ∀ (c x y : ℂ), iteratedFDeriv ℝ j (fun _ : ℂ => c) x =
      iteratedFDeriv ℝ j (fun _ : ℂ => c) y := by
    intro c x y
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [iteratedFDeriv_zero_eq_comp]
    · rw [iteratedFDeriv_const_of_ne hj.ne']
      rfl
  obtain ⟨c, R, hR0, hloc⟩ : ∃ c : ℂ, ∃ R : ℝ, 0 ≤ R ∧
      ∀ y : ℂ, R < ‖y‖ → Φ =ᶠ[nhds y] fun _ => c := by
    rcases le_or_gt de 0 with hde | hde
    · refine ⟨0, 0, le_rfl, fun y _ => Filter.Eventually.of_forall fun z => ?_⟩
      have hz : Complex.normSq z / de ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg z) hde
      show ((χ₀ (Complex.normSq z / de) : ℝ) : ℂ) = 0
      rw [h0 _ (by linarith)]
      simp
    · refine ⟨1, de + 1, by linarith, fun y hy => ?_⟩
      have hopen : IsOpen {z : ℂ | de + 1 < ‖z‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hy] with z hz
      have hz' : de + 1 < ‖z‖ := hz
      have hn : de ≤ Complex.normSq z := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg z]
      have h1' : 1 ≤ Complex.normSq z / de := by
        rw [le_div_iff₀ hde]
        linarith
      show ((χ₀ (Complex.normSq z / de) : ℝ) : ℂ) = 1
      rw [h1 _ h1']
      simp
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (R + 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have y0n : ‖((R + 1 : ℝ) : ℂ)‖ = R + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  refine ⟨B, fun y => ?_⟩
  rcases le_or_gt ‖y‖ (R + 1) with hy | hy
  · exact hB y (by rw [mem_closedBall_zero_iff]; exact hy)
  · have e1 := ((hloc y (by linarith)).iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds
    have e2 := ((hloc ((R + 1 : ℝ) : ℂ) (by rw [y0n]; linarith)).iteratedFDeriv
      (𝕜 := ℝ) j).eq_of_nhds
    rw [e1, hconst c y ((R + 1 : ℝ) : ℂ), ← e2]
    exact hB _ (by rw [mem_closedBall_zero_iff, y0n])

/- English proof (translation)
Establish `hSG : GV k r ⊆ GV k r` using `subset_rfl`. Establish `e0 : (fun g => ((C6.chiAll D χ₀ de L g : ℝ) : ℂ)) = fun g => ∏ l ∈ L, ((χ₀ (Complex.normSq (Dmin k r D.z D.z' g l) / de) : ℝ) : ℂ)`. Use function extensionality and compare the values at `g`. Simplify using `[C6.chiAll]`. Rewrite using `[e0]`.

Apply `ubl_prod hSG L` to reduce the goal to its premises. Introduce `l _`. Take `⟨C, hC0, hC⟩` from `(ubl_poly (dmin_pd k r D.z D.z' l) (GV k r) hSG n 0).1`. Establish `hns : ContDiff ℝ ∞ (fun y : ℂ => Complex.normSq y)`. Simplify using `only [Complex.normSq_apply]`.

Conclude with `(Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)`. Use `ubl_fdb (fun g => Dmin k r D.z D.z' g l) (contDiff_of_isPolyDeg (dmin_pd k r D.z D.z' l)) (GV k r) hSG Set.univ (fun _ _ => trivial) (2 * r + 2) n C ?_ (fun y : ℂ => ((χ₀ (Complex.normSq y / de) : ℝ) : ℂ)) (Complex.ofRealCLM.contDiff.comp (hχ.1.comp (hns.div_const de))) (fun j => …` and prove the remaining obligations. Introduce `w hw hne g hg`. Use `(hC w hw g hg).trans ?_` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_left _ hC0` to reduce the goal to its premises.

Apply `pow_le_pow_right₀ (gN_ge_one hg)` to reduce the goal to its premises. Establish `hl : 1 ≤ w.length`. Consider the cases of `w with`. Consider the case `nil => exact absurd rfl hne`. Consider the case `cons _ _ => simp`.

Simplify using `using Nat.le_mul_of_pos_right (2 * r + 2) hl`. Take `⟨B, hB⟩` from `exists_bound_iteratedFDeriv_cutoff_normSq hχ de j`. Conclude with `⟨B, fun y _ => hB y⟩`.
-/
lemma ubl_chi (D : RealPlaceData k r Wp Wq) {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (L : Finset (Fin (r + 2)))
    (n : ℕ) : UBL (fun g => ((C6.chiAll D χ₀ de L g : ℝ) : ℂ)) (GV k r) n 0 (2 * r + 2) := by
  have hSG : GV k r ⊆ GV k r := subset_rfl
  have e0 : (fun g => ((C6.chiAll D χ₀ de L g : ℝ) : ℂ)) =
      fun g => ∏ l ∈ L, ((χ₀ (Complex.normSq (Dmin k r D.z D.z' g l) / de) : ℝ) : ℂ) := by
    funext g
    simp [C6.chiAll]
  rw [e0]
  apply ubl_prod hSG L
  intro l _
  obtain ⟨C, hC0, hC⟩ := (ubl_poly (dmin_pd k r D.z D.z' l) (GV k r) hSG n 0).1
  have hns : ContDiff ℝ ∞ (fun y : ℂ => Complex.normSq y) := by
    simp only [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  refine ubl_fdb (fun g => Dmin k r D.z D.z' g l) (contDiff_of_isPolyDeg (dmin_pd k r D.z D.z' l)) (GV k r) hSG
    Set.univ (fun _ _ => trivial) (2 * r + 2) n C ?_
    (fun y : ℂ => ((χ₀ (Complex.normSq y / de) : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (hχ.1.comp (hns.div_const de))) (fun j => ?_)
  · intro w hw hne g hg
    refine (hC w hw g hg).trans ?_
    apply mul_le_mul_of_nonneg_left _ hC0
    apply pow_le_pow_right₀ (gN_ge_one hg)
    have hl : 1 ≤ w.length := by
      cases w with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    simpa using Nat.le_mul_of_pos_right (2 * r + 2) hl
  · obtain ⟨B, hB⟩ := exists_bound_iteratedFDeriv_cutoff_normSq hχ de j
    exact ⟨B, fun y _ => hB y⟩

end cut

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
