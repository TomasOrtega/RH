import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory.IsotropicPartner

open scoped ComplexOrder

def hf {n : ℕ} (d : Fin n → ℂ) (x y : Fin n → ℂ) : ℂ := ∑ i, star (x i) * d i * y i

/- English proof (translation)
Simplify using `only [hf, star_sum, star_mul', star_star, hd]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
lemma hf_symm {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i, star (d i) = d i) (x y : Fin n → ℂ) :
    hf d y x = star (hf d x y) := by
  simp only [hf, star_sum, star_mul', star_star, hd]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Simplify using `only [hf, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
lemma hf_sub {n : ℕ} (d : Fin n → ℂ) (x y u w : Fin n → ℂ) (a b : ℂ) :
    hf d x (fun i => y i - a * u i - b * w i) = hf d x y - a * hf d x u - b * hf d x w := by
  simp only [hf, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Use `set d : Fin n → ℂ := fun a => if ε a then 1 else -1 with hd_def`. Establish `hJ : Jm ε = diagonal d` using `rfl`. Apply the tactic sequence `have hd : ∀ i, star (d i) = d i := by intro i; simp only [d]; split_ifs <;> simp`. Apply the tactic sequence `have hd2 : ∀ i, d i * d i = 1 := by intro i; simp only [d]; split_ifs <;> norm_num`. Use `set s : ℂ := ∑ i, star (e i) * e i with hs_def`.

Establish `hs : s ≠ 0`. Use `(dotProduct_star_self_eq_zero (v := e)).not.mpr he` as an intermediate fact. Conclude with `fun h0 => this h0`. Use `set c : ℂ := s⁻¹ with hc_def`. Use `set e' : Fin n → ℂ := fun i => c * (d i * e i) with he'_def`.

Establish `hee : hf d e e = 0`. Simplify `hiso` using `[hJ, hf, dotProduct, mulVec_diagonal, mul_assoc]`. Establish `hee' : hf d e e' = 1`. Establish `: hf d e e' = c * s`. Simplify using `only [hf, e', s, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => by linear_combination (c * star (e i) * e i) * hd2 i`. Rewrite using `[this, hc_def, inv_mul_cancel₀ hs]`. Establish `he'e' : hf d e' e' = 0`. Establish `: hf d e' e' = star c * c * hf d e e`. Simplify using `only [hf, e', Finset.mul_sum, star_mul', hd]`.

Conclude with `Finset.sum_congr rfl fun i _ => by`. Take the linear combination `(star c * c * star (e i) * d i * e i) * hd2 i`. Rewrite using `[this, hee, mul_zero]`. Establish `he'e : hf d e' e = 1` using `by rw [hf_symm d hd, hee', star_one]`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : ∃ p, e p ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `he (funext h)`. Use `set f : Fin n → ℂ := fun i => e' i - (e' p / e p) * e i with hf_def`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : ∃ q, f q ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `: hf d e e' = (e' p / e p) * hf d e e`. Simplify using `only [hf, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `h i` as an intermediate fact. Simplify using `only [f] at this`. Take the linear combination `(star (e i) * d i) * this`. Rewrite `this` using `[hee', hee, mul_zero]`. Conclude with `one_ne_zero this`.

Establish `hpq : p ≠ q`. Introduce and unpack `rfl`. Apply `hq` to reduce the goal to its premises. Simplify using `only [f]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Set `pr : (Fin n → ℂ) → (Fin n → ℂ)` to `fun y i => y i - hf d e' y * e i - hf d e y * e' i`. Establish `hpre : ∀ y, hf d e (pr y) = 0`. Introduce `y`. Simplify using `only [pr]`.

Rewrite using `[hf_sub, hee, hee']`. Expand and normalize the polynomial expressions, which then agree. Establish `hpre' : ∀ y, hf d e' (pr y) = 0`. Introduce `y`. Simplify using `only [pr]`.

Rewrite using `[hf_sub, he'e, he'e']`. Expand and normalize the polynomial expressions, which then agree. Establish `hpre_l : ∀ y, hf d (pr y) e = 0` using `by intro y; rw [hf_symm d hd, hpre, star_zero]`. Establish `hpre'_l : ∀ y, hf d (pr y) e' = 0` using `by intro y; rw [hf_symm d hd, hpre', star_zero]`. Set `col : Fin n → Fin n → ℂ` to `fun j => if j = p then e else if j = q then e' else pr (Pi.single j 1)`.

Set `P : Matrix (Fin n) (Fin n) ℂ` to `Matrix.of fun i j => col j i`. Establish `hPcol : ∀ j, P *ᵥ Pi.single j 1 = col j`. Introduce `j`. Use extensionality with `i`. Simplify using `[P, mulVec_single_one]`.

Establish `hgram : ∀ a b, (Pᴴ * Jm ε * P) a b = hf d (col a) (col b)`. Introduce `a b`. Rewrite using `[hJ, Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal]`. Simplify using `[hf, P, Matrix.conjTranspose_apply]`.

Establish `hcolp : col p = e` using `by simp [col]`. Establish `hcolq : col q = e'` using `by simp [col, hpq.symm]`. Establish `hcolr : ∀ r, r ≠ p → r ≠ q → col r = pr (Pi.single r 1)`. Introduce `r h1 h2`. Simplify using `[col, h1, h2]`.

Establish `hGram : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) → hf d (col a) (col b) = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0`. Introduce `a b hab`. Break down `eq_or_ne a p with rfl | hap` into its components or cases. Break down `eq_or_ne b a with rfl | hba` into its components or cases. Simplify using `[hcolp, hee, hpq]`.

Break down `eq_or_ne b q with rfl | hbq` into its components or cases. Simplify using `[hcolp, hcolq, hee']`. Simplify using `[hcolp, hcolr b hba hbq, hpre, hba, hbq]`. Break down `eq_or_ne a q with rfl | haq` into its components or cases. Break down `eq_or_ne b p with rfl | hbp` into its components or cases.

Simplify using `[hcolp, hcolq, he'e]`. Break down `eq_or_ne b a with rfl | hbq` into its components or cases. Simplify using `[hcolq, he'e', hap]`. Simplify using `[hcolq, hcolr b hbp hbq, hpre', hbp, hbq]`. Break down `hab with h | h | rfl | rfl` into its components or cases.

Conclude with `absurd h hap`. Conclude with `absurd h haq`. Simplify using `[hcolp, hcolr a hap haq, hpre_l, hap, haq]`. Simplify using `[hcolq, hcolr a hap haq, hpre'_l, hap, haq]`. Establish `key : ∀ x v, hf d x (P *ᵥ v) = ∑ j, v j * hf d x (col j)`.

Introduce `x v`. Simplify using `only [hf, mulVec, dotProduct, P, of_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring`. Establish `hecol : ∀ j, hf d e (col j) = if j = q then 1 else 0`.

Introduce `j`. Break down `eq_or_ne j p with rfl | hjp` into its components or cases. Simplify using `[hcolp, hee, hpq]`. Break down `eq_or_ne j q with rfl | hjq` into its components or cases. Simplify using `[hcolq, hee']`.

Simplify using `[hcolr j hjp hjq, hpre, hjq]`. Establish `he'col : ∀ j, hf d e' (col j) = if j = p then 1 else 0`. Introduce `j`. Break down `eq_or_ne j p with rfl | hjp` into its components or cases. Simplify using `[hcolp, he'e]`.

Break down `eq_or_ne j q with rfl | hjq` into its components or cases. Simplify using `[hcolq, he'e', hjp]`. Simplify using `[hcolr j hjp hjq, hpre', hjp]`. Establish `hsingle : ∀ x j, hf d x (Pi.single j 1) = star (x j) * d j`. Introduce `x j`.

Simplify using `[hf, Pi.single_apply]`. Establish `h0 : ∀ x, hf d x 0 = 0` using `by intro x; simp [hf]`. Establish `hker : ∀ v, P *ᵥ v = 0 → v = 0`. Introduce `v hv`. Establish `hvq : v q = 0`.

Use `key e v` as an intermediate fact. Rewrite `this` using `[hv, h0]`. Simplify using `only [hecol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`. Conclude with `this.symm`. Establish `hvp : v p = 0`.

Use `key e' v` as an intermediate fact. Rewrite `this` using `[hv, h0]`. Simplify using `only [he'col, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`. Conclude with `this.symm`. Establish `hPv : P *ᵥ v = pr v`.

Use extensionality with `i`. Establish `hterm : ∀ j, col j i * v j = pr (Pi.single j 1) i * v j`. Introduce `j`. Break down `eq_or_ne j p with rfl | hjp` into its components or cases. Simplify using `[hvp]`.

Break down `eq_or_ne j q with rfl | hjq` into its components or cases. Simplify using `[hvq]`. Rewrite using `[hcolr j hjp hjq]`. Simplify using `only [mulVec, dotProduct, P, of_apply]`. Rewrite using `[Finset.sum_congr rfl fun j _ => hterm j]`.

Simplify using `only [pr, hsingle]`. Establish `h1 : ∑ j, (Pi.single j (1:ℂ) : Fin n → ℂ) i * v j = v i` using `by simp [Pi.single_apply]`. Simplify using `only [sub_mul, Finset.sum_sub_distrib, h1]`. Rewrite using `[sub_sub, sub_sub]`. Use `congr 1`.

Simplify using `only [hf, Finset.sum_mul, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite `hv` using `[hPv]`. Establish `hvi : ∀ i, v i = hf d e' v * e i + hf d e v * e' i`. Introduce `i`.

Use `congrFun hv i` as an intermediate fact. Simplify using `only [pr, Pi.zero_apply] at this`. Take the linear combination `this`. Establish `hp0 : hf d e' v * e p + hf d e v * e' p = 0` using `by rw [← hvi p, hvp]`. Establish `hq0 : hf d e' v * e q + hf d e v * e' q = 0` using `by rw [← hvi q, hvq]`.

Establish `hβ : hf d e v = 0`. Establish `: hf d e v * f q = 0`. Simplify using `only [f]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e p * hq0 - e q * hp0`.

Conclude with `(mul_eq_zero.mp this).resolve_right hq`. Establish `hα : hf d e' v = 0`. Rewrite `hp0` using `[hβ, zero_mul, add_zero]`. Conclude with `(mul_eq_zero.mp hp0).resolve_right hp`. Use extensionality with `i`.

Rewrite using `[hvi, hα, hβ]`. Simplify using the standard rewrite rules. Establish `hunit : IsUnit P`. Use `(Matrix.mulVec_injective_iff_isUnit).mp fun v w h => ?_` and prove the remaining obligations. Use `hker (v - w) (by rw [Matrix.mulVec_sub, h, sub_self])` as an intermediate fact.

Conclude with `sub_eq_zero.mp this`. Use `⟨P, p, q, c, hunit, hpq, by rw [hPcol, hcolp], ?_, fun a b hab => by rw [hgram]; exact hGram a b hab⟩` and prove the remaining obligations. Rewrite using `[hPcol, hcolq]`. Use extensionality with `i`. Simplify using `[e', hJ, mulVec_diagonal]`.
-/
theorem exists_adapted_basis (n : ℕ) (ε : Fin n → Bool) (e : Fin n → ℂ) (he : e ≠ 0)
    (hiso : star e ⬝ᵥ (Jm ε *ᵥ e) = 0) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P ∧ p ≠ q ∧
      P *ᵥ Pi.single p 1 = e ∧ P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ e) ∧
      ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
        (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0 := by
  set d : Fin n → ℂ := fun a => if ε a then 1 else -1 with hd_def
  have hJ : Jm ε = diagonal d := rfl
  have hd : ∀ i, star (d i) = d i := by intro i; simp only [d]; split_ifs <;> simp
  have hd2 : ∀ i, d i * d i = 1 := by intro i; simp only [d]; split_ifs <;> norm_num
  set s : ℂ := ∑ i, star (e i) * e i with hs_def
  have hs : s ≠ 0 := by
    have := (dotProduct_star_self_eq_zero (v := e)).not.mpr he
    exact fun h0 => this h0
  set c : ℂ := s⁻¹ with hc_def
  set e' : Fin n → ℂ := fun i => c * (d i * e i) with he'_def
  have hee : hf d e e = 0 := by
    simpa [hJ, hf, dotProduct, mulVec_diagonal, mul_assoc] using hiso
  have hee' : hf d e e' = 1 := by
    have : hf d e e' = c * s := by
      simp only [hf, e', s, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by linear_combination (c * star (e i) * e i) * hd2 i
    rw [this, hc_def, inv_mul_cancel₀ hs]
  have he'e' : hf d e' e' = 0 := by
    have : hf d e' e' = star c * c * hf d e e := by
      simp only [hf, e', Finset.mul_sum, star_mul', hd]
      exact Finset.sum_congr rfl fun i _ => by
        linear_combination (star c * c * star (e i) * d i * e i) * hd2 i
    rw [this, hee, mul_zero]
  have he'e : hf d e' e = 1 := by rw [hf_symm d hd, hee', star_one]
  obtain ⟨p, hp⟩ : ∃ p, e p ≠ 0 := by
    by_contra h; push_neg at h; exact he (funext h)
  set f : Fin n → ℂ := fun i => e' i - (e' p / e p) * e i with hf_def
  obtain ⟨q, hq⟩ : ∃ q, f q ≠ 0 := by
    by_contra h; push_neg at h
    have : hf d e e' = (e' p / e p) * hf d e e := by
      simp only [hf, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := h i; simp only [f] at this
      linear_combination (star (e i) * d i) * this
    rw [hee', hee, mul_zero] at this; exact one_ne_zero this
  have hpq : p ≠ q := by
    rintro rfl; apply hq; simp only [f]; field_simp; ring
  let pr : (Fin n → ℂ) → (Fin n → ℂ) := fun y i => y i - hf d e' y * e i - hf d e y * e' i
  have hpre : ∀ y, hf d e (pr y) = 0 := by
    intro y; simp only [pr]; rw [hf_sub, hee, hee']; ring
  have hpre' : ∀ y, hf d e' (pr y) = 0 := by
    intro y; simp only [pr]; rw [hf_sub, he'e, he'e']; ring
  have hpre_l : ∀ y, hf d (pr y) e = 0 := by intro y; rw [hf_symm d hd, hpre, star_zero]
  have hpre'_l : ∀ y, hf d (pr y) e' = 0 := by intro y; rw [hf_symm d hd, hpre', star_zero]
  let col : Fin n → Fin n → ℂ := fun j => if j = p then e else if j = q then e' else pr (Pi.single j 1)
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => col j i
  have hPcol : ∀ j, P *ᵥ Pi.single j 1 = col j := by
    intro j; ext i; simp [P, mulVec_single_one]
  have hgram : ∀ a b, (Pᴴ * Jm ε * P) a b = hf d (col a) (col b) := by
    intro a b
    rw [hJ, Matrix.mul_apply]; simp only [Matrix.mul_diagonal]
    simp [hf, P, Matrix.conjTranspose_apply]
  have hcolp : col p = e := by simp [col]
  have hcolq : col q = e' := by simp [col, hpq.symm]
  have hcolr : ∀ r, r ≠ p → r ≠ q → col r = pr (Pi.single r 1) := by
    intro r h1 h2; simp [col, h1, h2]
  have hGram : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      hf d (col a) (col b) = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0 := by
    intro a b hab
    rcases eq_or_ne a p with rfl | hap
    · rcases eq_or_ne b a with rfl | hba
      · simp [hcolp, hee, hpq]
      rcases eq_or_ne b q with rfl | hbq
      · simp [hcolp, hcolq, hee']
      · simp [hcolp, hcolr b hba hbq, hpre, hba, hbq]
    rcases eq_or_ne a q with rfl | haq
    · rcases eq_or_ne b p with rfl | hbp
      · simp [hcolp, hcolq, he'e]
      rcases eq_or_ne b a with rfl | hbq
      · simp [hcolq, he'e', hap]
      · simp [hcolq, hcolr b hbp hbq, hpre', hbp, hbq]
    · rcases hab with h | h | rfl | rfl
      · exact absurd h hap
      · exact absurd h haq
      · simp [hcolp, hcolr a hap haq, hpre_l, hap, haq]
      · simp [hcolq, hcolr a hap haq, hpre'_l, hap, haq]
  have key : ∀ x v, hf d x (P *ᵥ v) = ∑ j, v j * hf d x (col j) := by
    intro x v
    simp only [hf, mulVec, dotProduct, P, of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hecol : ∀ j, hf d e (col j) = if j = q then 1 else 0 := by
    intro j
    rcases eq_or_ne j p with rfl | hjp
    · simp [hcolp, hee, hpq]
    rcases eq_or_ne j q with rfl | hjq
    · simp [hcolq, hee']
    · simp [hcolr j hjp hjq, hpre, hjq]
  have he'col : ∀ j, hf d e' (col j) = if j = p then 1 else 0 := by
    intro j
    rcases eq_or_ne j p with rfl | hjp
    · simp [hcolp, he'e]
    rcases eq_or_ne j q with rfl | hjq
    · simp [hcolq, he'e', hjp]
    · simp [hcolr j hjp hjq, hpre', hjp]
  have hsingle : ∀ x j, hf d x (Pi.single j 1) = star (x j) * d j := by
    intro x j; simp [hf, Pi.single_apply]
  have h0 : ∀ x, hf d x 0 = 0 := by intro x; simp [hf]
  have hker : ∀ v, P *ᵥ v = 0 → v = 0 := by
    intro v hv
    have hvq : v q = 0 := by
      have := key e v
      rw [hv, h0] at this
      simp only [hecol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact this.symm
    have hvp : v p = 0 := by
      have := key e' v
      rw [hv, h0] at this
      simp only [he'col, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact this.symm
    have hPv : P *ᵥ v = pr v := by
      ext i
      have hterm : ∀ j, col j i * v j = pr (Pi.single j 1) i * v j := by
        intro j
        rcases eq_or_ne j p with rfl | hjp
        · simp [hvp]
        rcases eq_or_ne j q with rfl | hjq
        · simp [hvq]
        rw [hcolr j hjp hjq]
      simp only [mulVec, dotProduct, P, of_apply]
      rw [Finset.sum_congr rfl fun j _ => hterm j]
      simp only [pr, hsingle]
      have h1 : ∑ j, (Pi.single j (1:ℂ) : Fin n → ℂ) i * v j = v i := by simp [Pi.single_apply]
      simp only [sub_mul, Finset.sum_sub_distrib, h1]
      rw [sub_sub, sub_sub]
      congr 1
      simp only [hf, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hPv] at hv
    have hvi : ∀ i, v i = hf d e' v * e i + hf d e v * e' i := by
      intro i; have := congrFun hv i; simp only [pr, Pi.zero_apply] at this
      linear_combination this
    have hp0 : hf d e' v * e p + hf d e v * e' p = 0 := by rw [← hvi p, hvp]
    have hq0 : hf d e' v * e q + hf d e v * e' q = 0 := by rw [← hvi q, hvq]
    have hβ : hf d e v = 0 := by
      have : hf d e v * f q = 0 := by
        simp only [f]; field_simp; linear_combination e p * hq0 - e q * hp0
      exact (mul_eq_zero.mp this).resolve_right hq
    have hα : hf d e' v = 0 := by
      rw [hβ, zero_mul, add_zero] at hp0; exact (mul_eq_zero.mp hp0).resolve_right hp
    ext i; rw [hvi, hα, hβ]; simp
  have hunit : IsUnit P := by
    refine (Matrix.mulVec_injective_iff_isUnit).mp fun v w h => ?_
    have := hker (v - w) (by rw [Matrix.mulVec_sub, h, sub_self])
    exact sub_eq_zero.mp this
  refine ⟨P, p, q, c, hunit, hpq, by rw [hPcol, hcolp], ?_, fun a b hab => by rw [hgram]; exact hGram a b hab⟩
  rw [hPcol, hcolq]; ext i; simp [e', hJ, mulVec_diagonal]

end GlobalTheory.IsotropicPartner
