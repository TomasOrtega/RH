import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.CCA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

/- English proof (translation)
Establish `h1 : HasFDerivAt f (fderiv ℝ f g) (crv x g 0)` using `by rw [crv_zero]; exact (hf g).hasFDerivAt`. Establish `h2` using `h1.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)`. Establish `e : Dx x f g = fderiv ℝ f g (dirv x g)` using `by rw [Dx_eq]; exact h2.deriv`. Rewrite using `[e]`. Conclude with `h2`.
-/
lemma hasDx (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) (g : Mat k r) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (Dx x f g) 0 := by
  have h1 : HasFDerivAt f (fderiv ℝ f g) (crv x g 0) := by rw [crv_zero]; exact (hf g).hasFDerivAt
  have h2 := h1.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)
  have e : Dx x f g = fderiv ℝ f g (dirv x g) := by rw [Dx_eq]; exact h2.deriv
  rw [e]; exact h2

/- English proof (translation)
Use function extensionality and compare the values at `g`. Rewrite using `[dirL_apply, Dx_eq]`. Establish `h1 : HasFDerivAt f (fderiv ℝ f g) (crv x g 0)` using `by rw [crv_zero]; exact (hf g).hasFDerivAt`. Conclude with `(h1.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)).deriv`.
-/
lemma Dx_fd (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) :
    Dx x f = fun g => fderiv ℝ f g (dirL x g) := by
  funext g
  rw [dirL_apply, Dx_eq]
  have h1 : HasFDerivAt f (fderiv ℝ f g) (crv x g 0) := by rw [crv_zero]; exact (hf g).hasFDerivAt
  exact (h1.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)).deriv

/- English proof (translation)
Use `first`. Consider the case `exact hf.differentiable (by simp)`. Consider the case `exact hf.differentiable le_top`. Consider the case `exact hf.differentiable (by norm_num)`.
-/
lemma sm_diff {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  first
  | exact hf.differentiable (by simp)
  | exact hf.differentiable le_top
  | exact hf.differentiable (by norm_num)

/- English proof (translation)
Rewrite using `[Dx_fd x (sm_diff hf)]`. Use `first`. Consider the case `exact (hf.fderiv_right (m := ∞) le_rfl).clm_apply (dirL x).contDiff`. Consider the case `exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply (dirL x).contDiff`. Consider the case `exact (hf.fderiv_right (m := ∞) (by norm_num)).clm_apply (dirL x).contDiff`.
-/
lemma sm_Dx (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dx x f) := by
  rw [Dx_fd x (sm_diff hf)]
  first
  | exact (hf.fderiv_right (m := ∞) le_rfl).clm_apply (dirL x).contDiff
  | exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply (dirL x).contDiff
  | exact (hf.fderiv_right (m := ∞) (by norm_num)).clm_apply (dirL x).contDiff

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact hf`. Consider the case `cons x w ih => exact sm_Dx x ih`.
-/
lemma sm_Dw (w : List (Bool × Mat k r)) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dw w f) := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact sm_Dx x ih

/- English proof (translation)
Use function extensionality and compare the values at `g`. Conclude with `(hasDx x (h₁.add h₂) g).unique ((hasDx x h₁ g).add (hasDx x h₂ g))`.
-/
lemma Dx_add' (x : Bool × Mat k r) {f₁ f₂ : Mat k r → ℂ} (h₁ : Differentiable ℝ f₁)
    (h₂ : Differentiable ℝ f₂) : Dx x (fun g => f₁ g + f₂ g) = fun g => Dx x f₁ g + Dx x f₂ g := by
  funext g
  exact (hasDx x (h₁.add h₂) g).unique ((hasDx x h₁ g).add (hasDx x h₂ g))

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons x w ih => show Dx x (Dw w fun g => f₁ g + f₂ g) = _`. Rewrite using `[ih]`. Conclude with `Dx_add' x (sm_diff (sm_Dw w h₁)) (sm_diff (sm_Dw w h₂))`.
-/
lemma Dw_add' (w : List (Bool × Mat k r)) {f₁ f₂ : Mat k r → ℂ} (h₁ : ContDiff ℝ ∞ f₁)
    (h₂ : ContDiff ℝ ∞ f₂) : Dw w (fun g => f₁ g + f₂ g) = fun g => Dw w f₁ g + Dw w f₂ g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => f₁ g + f₂ g) = _
    rw [ih]
    exact Dx_add' x (sm_diff (sm_Dw w h₁)) (sm_diff (sm_Dw w h₂))

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `h0 : crv x g 0 = g` using `by simp [crv]`. Establish `h` using `(hasDx x ha g).mul (hasDx x hb g)`. Rewrite `h` using `[h0]`. Conclude with `(hasDx x (ha.mul hb) g).unique h`.
-/
lemma Dx_mul' (x : Bool × Mat k r) {a b : Mat k r → ℂ} (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) : Dx x (fun g => a g * b g) = fun g => Dx x a g * b g + a g * Dx x b g := by
  funext g
  have h0 : crv x g 0 = g := by simp [crv]
  have h := (hasDx x ha g).mul (hasDx x hb g)
  rw [h0] at h
  exact (hasDx x (ha.mul hb) g).unique h

/- English proof (translation)
Use function extensionality and compare the values at `g`. Conclude with `(hasDx x (L.differentiable.comp hf) g).unique (L.hasFDerivAt.comp_hasDerivAt _ (hasDx x hf g))`.
-/
lemma Dx_clm (x : Bool × Mat k r) (L : ℂ →L[ℝ] ℂ) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) :
    Dx x (fun g => L (f g)) = fun g => L (Dx x f g) := by
  funext g
  exact (hasDx x (L.differentiable.comp hf) g).unique (L.hasFDerivAt.comp_hasDerivAt _ (hasDx x hf g))

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons x w ih => show Dx x (Dw w fun g => L (f g)) = _`. Rewrite using `[ih]`. Conclude with `Dx_clm x L (sm_diff (sm_Dw w hf))`.
-/
lemma Dw_clm (w : List (Bool × Mat k r)) (L : ℂ →L[ℝ] ℂ) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) :
    Dw w (fun g => L (f g)) = fun g => L (Dw w f g) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => L (f g)) = _
    rw [ih]
    exact Dx_clm x L (sm_diff (sm_Dw w hf))

/- English proof (translation)
Unfold `Dw`. Rewrite using `[List.foldr_append]`. Both sides reduce to the same expression.
-/
lemma Dw_snoc (w : List (Bool × Mat k r)) (x : Bool × Mat k r) (f : Mat k r → ℂ) :
    Dw (w ++ [x]) f = Dw w (Dx x f) := by
  unfold Dw
  rw [List.foldr_append]
  rfl

/- English proof (translation)
Proceed by induction on `w using List.reverseRecOn with`. Consider the case `nil`. Introduce `a b ha hb M hM`. Simplify `hM [] [] (by simp) (by simp) (by simp)` using `[Dw, norm_mul]`. Consider the case `append_singleton w x ih`.

Introduce `a b ha hb M hM`. Rewrite using `[Dw_snoc, Dx_mul' x (sm_diff ha) (sm_diff hb), Dw_add' w ((sm_Dx x ha).mul hb) (ha.mul (sm_Dx x hb))]`. Establish `h1` using `ih (Dx x a) b (sm_Dx x ha) hb M (fun w₁ w₂ s1 s2 p => by`. Establish `e : w₁ ++ [x] ++ w₂ = w₁ ++ x :: w₂` using `by simp`. Establish `hp : (w₁ ++ [x] ++ w₂).Perm (w ++ [x])`.

Rewrite using `[e]`. Conclude with `List.perm_middle.trans ((p.cons x).trans (List.perm_append_singleton x w).symm)`. Use `hM (w₁ ++ [x]) w₂ (s1.append (List.Sublist.refl _)) (s2.trans (List.sublist_append_left _ _)) hp` as an intermediate fact. Rewrite using `[Dw_snoc] at this)` and apply the resulting hypothesis. Establish `h2` using `ih a (Dx x b) ha (sm_Dx x hb) M (fun w₁ w₂ s1 s2 p => by`.

Establish `hp : (w₁ ++ (w₂ ++ [x])).Perm (w ++ [x])`. Rewrite using `[← List.append_assoc]`. Conclude with `p.append_right [x]`. Use `hM w₁ (w₂ ++ [x]) (s1.trans (List.sublist_append_left _ _)) (s2.append (List.Sublist.refl _)) hp` as an intermediate fact. Rewrite using `[Dw_snoc] at this)` and apply the resulting hypothesis.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[List.length_append, List.length_singleton, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma leibC (g : Mat k r) (w : List (Bool × Mat k r)) :
    ∀ (a b : Mat k r → ℂ), ContDiff ℝ ∞ a → ContDiff ℝ ∞ b → ∀ M : ℝ,
      (∀ w₁ w₂ : List (Bool × Mat k r), w₁.Sublist w → w₂.Sublist w → (w₁ ++ w₂).Perm w →
        ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) →
      ‖Dw w (fun g => a g * b g) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a b ha hb M hM
    simpa [Dw, norm_mul] using hM [] [] (by simp) (by simp) (by simp)
  | append_singleton w x ih =>
    intro a b ha hb M hM
    rw [Dw_snoc, Dx_mul' x (sm_diff ha) (sm_diff hb),
      Dw_add' w ((sm_Dx x ha).mul hb) (ha.mul (sm_Dx x hb))]
    have h1 := ih (Dx x a) b (sm_Dx x ha) hb M (fun w₁ w₂ s1 s2 p => by
      have e : w₁ ++ [x] ++ w₂ = w₁ ++ x :: w₂ := by simp
      have hp : (w₁ ++ [x] ++ w₂).Perm (w ++ [x]) := by
        rw [e]
        exact List.perm_middle.trans ((p.cons x).trans (List.perm_append_singleton x w).symm)
      have := hM (w₁ ++ [x]) w₂ (s1.append (List.Sublist.refl _))
        (s2.trans (List.sublist_append_left _ _)) hp
      rwa [Dw_snoc] at this)
    have h2 := ih a (Dx x b) ha (sm_Dx x hb) M (fun w₁ w₂ s1 s2 p => by
      have hp : (w₁ ++ (w₂ ++ [x])).Perm (w ++ [x]) := by
        rw [← List.append_assoc]
        exact p.append_right [x]
      have := hM w₁ (w₂ ++ [x]) (s1.trans (List.sublist_append_left _ _))
        (s2.append (List.Sublist.refl _)) hp
      rwa [Dw_snoc] at this)
    calc _ ≤ ‖Dw w (fun g => Dx x a g * b g) g‖ + ‖Dw w (fun g => a g * Dx x b g) g‖ := norm_add_le _ _
      _ ≤ 2 ^ w.length * M + 2 ^ w.length * M := add_le_add h1 h2
      _ = 2 ^ (w ++ [x]).length * M := by
        rw [List.length_append, List.length_singleton, pow_succ]
        ring

def reC : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

def imC : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma reC_apply (z : ℂ) : reC z = (z.re : ℂ) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma imC_apply (z : ℂ) : imC z = (z.im : ℂ) := rfl

/- English proof (translation)
Rewrite using `[reC_apply, Complex.norm_real, Real.norm_eq_abs]`. Use `first`. Consider the case `exact Complex.abs_re_le_norm z`. Consider the case `exact Complex.abs_re_le_abs z`.
-/
lemma norm_reC (z : ℂ) : ‖reC z‖ ≤ ‖z‖ := by
  rw [reC_apply, Complex.norm_real, Real.norm_eq_abs]
  first
  | exact Complex.abs_re_le_norm z
  | exact Complex.abs_re_le_abs z

/- English proof (translation)
Rewrite using `[imC_apply, Complex.norm_real, Real.norm_eq_abs]`. Use `first`. Consider the case `exact Complex.abs_im_le_norm z`. Consider the case `exact Complex.abs_im_le_abs z`.
-/
lemma norm_imC (z : ℂ) : ‖imC z‖ ≤ ‖z‖ := by
  rw [imC_apply, Complex.norm_real, Real.norm_eq_abs]
  first
  | exact Complex.abs_im_le_norm z
  | exact Complex.abs_im_le_abs z

/- English proof (translation)
Establish `h : d = (d.re : ℝ) • (1 : ℂ) + (d.im : ℝ) • Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Use `conv_lhs => rw [h]`. Rewrite using `[map_add, map_smul, map_smul, reC_apply, imC_apply, Complex.real_smul, Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma clm_split (L : ℂ →L[ℝ] ℂ) (d : ℂ) : L d = L 1 * reC d + L Complex.I * imC d := by
  have h : d = (d.re : ℝ) • (1 : ℂ) + (d.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [h]
  rw [map_add, map_smul, map_smul, reC_apply, imC_apply, Complex.real_smul, Complex.real_smul]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `h0 : crv x g 0 = g` using `by simp [crv]`. Establish `hχd : Differentiable ℝ χ` using `by first`. Consider the case `exact hχ.differentiable (by simp)`. Consider the case `exact hχ.differentiable le_top`.

Consider the case `exact hχ.differentiable (by norm_num)`. Establish `h1` using `hasDx x (sm_diff hψ) g`. Establish `h2 : HasFDerivAt χ (fderiv ℝ χ (ψ g)) (ψ (crv x g 0))`. Rewrite using `[h0]`. Conclude with `(hχd (ψ g)).hasFDerivAt`.

Establish `h3` using `h2.comp_hasDerivAt (0 : ℝ) h1`. Establish `h4` using `hasDx x (sm_diff (hχ.comp hψ)) g`. Establish `h5 : Dx x (fun g => χ (ψ g)) g = fderiv ℝ χ (ψ g) (Dx x ψ g)` using `h4.unique h3`. Rewrite using `[h5, clm_split]`.
-/
lemma Dx_comp (x : Bool × Mat k r) {χ : ℂ → ℂ} {ψ : Mat k r → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hψ : ContDiff ℝ ∞ ψ) :
    Dx x (fun g => χ (ψ g)) = fun g => (fun z => fderiv ℝ χ z 1) (ψ g) * reC (Dx x ψ g)
      + (fun z => fderiv ℝ χ z Complex.I) (ψ g) * imC (Dx x ψ g) := by
  funext g
  have h0 : crv x g 0 = g := by simp [crv]
  have hχd : Differentiable ℝ χ := by
    first
    | exact hχ.differentiable (by simp)
    | exact hχ.differentiable le_top
    | exact hχ.differentiable (by norm_num)
  have h1 := hasDx x (sm_diff hψ) g
  have h2 : HasFDerivAt χ (fderiv ℝ χ (ψ g)) (ψ (crv x g 0)) := by
    rw [h0]; exact (hχd (ψ g)).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  have h4 := hasDx x (sm_diff (hχ.comp hψ)) g
  have h5 : Dx x (fun g => χ (ψ g)) g = fderiv ℝ χ (ψ g) (Dx x ψ g) := h4.unique h3
  rw [h5, clm_split]

/- English proof (translation)
Use `first`. Consider the case `exact (hχ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const`. Consider the case `exact (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const`. Consider the case `exact (hχ.fderiv_right (m := ∞) (by norm_num)).clm_apply contDiff_const`.
-/
lemma sm_fd {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ) (v : ℂ) : ContDiff ℝ ∞ (fun z => fderiv ℝ χ z v) := by
  first
  | exact (hχ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  | exact (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  | exact (hχ.fderiv_right (m := ∞) (by norm_num)).clm_apply contDiff_const

end PI.UnitaryCorollaryDerivatives.CCA
