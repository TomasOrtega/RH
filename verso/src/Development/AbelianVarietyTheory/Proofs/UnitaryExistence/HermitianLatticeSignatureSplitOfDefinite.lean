import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CmHostRootComplexEqPmSqrt
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
/- English proof (translation)
Introduce `h`. Establish `hd : H.d ≠ 0`. Use `H.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hpos : (0 : ℝ) < H.d` using `by exact_mod_cast Nat.pos_of_ne_zero hd`.

Use `congrArg Complex.re H.sqrt_neg_disc_sq` as an intermediate fact. Simplify using `[sq, Complex.mul_re, h] at this`. Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`.
-/
private theorem rt0_im_ne_zero (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.rt0.im ≠ 0 := by
  intro h
  have hd : H.d ≠ 0 := by
    have := H.2
    omega
  have hpos : (0 : ℝ) < H.d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have := congrArg Complex.re H.sqrt_neg_disc_sq
  simp [sq, Complex.mul_re, h] at this
  nlinarith [mul_self_nonneg H.rt0.re]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
/- English proof (translation)
Establish `hsq : ((H.rt : E)) ^ 2 = -(H.d : E)`. Use `congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `h2 : (τ H.rt) ^ 2 = H.rt0 ^ 2`.

Rewrite using `[← map_pow, hsq, H.sqrt_neg_disc_sq]`. Simplify using the standard rewrite rules. Conclude with `sq_eq_sq_iff_eq_or_eq_neg.1 h2`.
-/
private theorem embedding_rt_eq_or_eq_neg (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ H.rt = H.rt0 ∨ τ H.rt = -H.rt0 := by
  have hsq : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    push_cast at this
    exact this
  have h2 : (τ H.rt) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, hsq, H.sqrt_neg_disc_sq]
    simp
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h2

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
/- English proof (translation)
Take `⟨-, hinj, -, -, Hm, -, hpos, hform⟩` from `hP`. Establish `hPa : P a ≠ 0` using `fun h => ha (hinj (h.trans (map_zero P).symm))`. Use `⟨(_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (P a) (P a)).re, hpos _ hPa, ?_⟩` and prove the remaining obligations. Establish `h0 : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (P a) (P a)).im = 0`. Rewrite using `[hform, D.alt, Int.cast_zero]`.

Rewrite using `[← hform, hc]`. Simplify using `only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm] at h0 ⊢`. Rewrite using `[smul_dotProduct, smul_eq_mul, Complex.mul_im, h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_pos_form_rt_eq_im_mul {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {g : ℕ} {ty : Fin g → E →+* ℂ}
    {P : D.La →+ (Fin g → ℂ)} (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) (c : ℂ)
    (hc : ∀ x, P (H.rt • x) = c • P x) {a : D.La} (ha : a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ (((D.EF (H.rt • a)) a : ℤ) : ℝ) = c.im * r := by
  obtain ⟨-, hinj, -, -, Hm, -, hpos, hform⟩ := hP
  have hPa : P a ≠ 0 := fun h => ha (hinj (h.trans (map_zero P).symm))
  refine ⟨(_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (P a) (P a)).re, hpos _ hPa, ?_⟩
  have h0 : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (P a) (P a)).im = 0 := by
    rw [hform, D.alt, Int.cast_zero]
  rw [← hform, hc]
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm] at h0 ⊢
  rw [smul_dotProduct, smul_eq_mul, Complex.mul_im, h0]
  ring

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in

/- English proof (translation)
Introduce `E _ _ _ H D hpq`. Take `⟨g, ty, hty⟩` from `_root_.GlobalTheory.PureTypeModel.exists_isTypeFn H D.p D.q`. Take `⟨P, hP⟩` from `_root_.GlobalTheory.PeriodNonempty.exists_isPeriod E H D g ty hty`. Establish `hscal : ∀ c : ℂ, (∀ i, ty i H.rt = c) → ∀ x, P (H.rt • x) = c • P x`. Introduce `c hc x`.

Use function extensionality and compare the values at `i`. Rewrite using `[hP.1, hc]`. Both sides reduce to the same expression. Establish `hcard : ∀ i, Nat.card {j // ty j = ty i} ≠ 0`. Introduce `i`.

Use `haveI : Nonempty {j // ty j = ty i} := ⟨⟨i, rfl⟩⟩`. Conclude with `Nat.card_pos.ne'`. Establish `him` using `rt0_im_ne_zero H`. Establish `hsq` using `mul_self_pos.2 him`. Unfold `_root_.GlobalTheory.CompRat.SplitLat`.

Break down `hpq with hp | hq` into its components or cases. Establish `hc : ∀ i, ty i H.rt = -H.rt0`. Introduce `i`. Break down `embedding_rt_eq_or_eq_neg H (ty i) with h | h` into its components or cases. Conclude with `absurd ((hty (ty i)).1 h) (by rw [hp]; exact hcard i)`.

Conclude with `h`. Use `⟨⊥, ⊤, by simp, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha b _`. Rewrite using `[(Submodule.mem_bot _).1 ha]`. Simplify using the standard rewrite rules.

Rewrite using `[finrank_bot, hp]`. Rewrite using `[finrank_top, D.rank, hp, zero_add]`. Introduce `a ha h0`. Conclude with `absurd ((Submodule.mem_bot _).1 ha) h0`. Introduce `a _ ha0`.

Take `⟨r, hr, he⟩` from `exists_pos_form_rt_eq_im_mul hP _ (hscal _ hc) ha0`. Rewrite using `[he, Complex.neg_im]`. Use polynomial arithmetic with `[mul_pos hsq hr]`. Establish `hc : ∀ i, ty i H.rt = H.rt0`. Introduce `i`.

Assume the negation of the conclusion as `h`. Conclude with `absurd ((hty (ty i)).2 h) (by rw [hq]; exact hcard i)`. Use `⟨⊤, ⊥, by simp, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a _ b hb`. Rewrite using `[(Submodule.mem_bot _).1 hb]`.

Simplify using the standard rewrite rules. Rewrite using `[finrank_top, D.rank, hq, add_zero]`. Rewrite using `[finrank_bot, hq]`. Introduce `a _ ha0`. Take `⟨r, hr, he⟩` from `exists_pos_form_rt_eq_im_mul hP _ (hscal _ hc) ha0`.

Rewrite using `[he]`. Use polynomial arithmetic with `[mul_pos hsq hr]`. Introduce `a ha h0`. Conclude with `absurd ((Submodule.mem_bot _).1 ha) h0`.
-/
theorem _root_.GlobalTheory.CompRat.splitLat_of_definite : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H),
    D.p = 0 ∨ D.q = 0 → _root_.GlobalTheory.CompRat.SplitLat D := by
  intro E _ _ _ H D hpq
  obtain ⟨g, ty, hty⟩ := _root_.GlobalTheory.PureTypeModel.exists_isTypeFn H D.p D.q
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.PeriodNonempty.exists_isPeriod E H D g ty hty
  have hscal : ∀ c : ℂ, (∀ i, ty i H.rt = c) → ∀ x, P (H.rt • x) = c • P x := by
    intro c hc x
    funext i
    rw [hP.1, hc]
    rfl
  have hcard : ∀ i, Nat.card {j // ty j = ty i} ≠ 0 := by
    intro i
    haveI : Nonempty {j // ty j = ty i} := ⟨⟨i, rfl⟩⟩
    exact Nat.card_pos.ne'
  have him := rt0_im_ne_zero H
  have hsq := mul_self_pos.2 him
  unfold _root_.GlobalTheory.CompRat.SplitLat
  rcases hpq with hp | hq
  · have hc : ∀ i, ty i H.rt = -H.rt0 := by
      intro i
      rcases embedding_rt_eq_or_eq_neg H (ty i) with h | h
      · exact absurd ((hty (ty i)).1 h) (by rw [hp]; exact hcard i)
      · exact h
    refine ⟨⊥, ⊤, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha b _
      rw [(Submodule.mem_bot _).1 ha]
      simp
    · rw [finrank_bot, hp]
    · rw [finrank_top, D.rank, hp, zero_add]
    · intro a ha h0
      exact absurd ((Submodule.mem_bot _).1 ha) h0
    · intro a _ ha0
      obtain ⟨r, hr, he⟩ := exists_pos_form_rt_eq_im_mul hP _ (hscal _ hc) ha0
      rw [he, Complex.neg_im]
      nlinarith [mul_pos hsq hr]
  · have hc : ∀ i, ty i H.rt = H.rt0 := by
      intro i
      by_contra h
      exact absurd ((hty (ty i)).2 h) (by rw [hq]; exact hcard i)
    refine ⟨⊤, ⊥, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro a _ b hb
      rw [(Submodule.mem_bot _).1 hb]
      simp
    · rw [finrank_top, D.rank, hq, add_zero]
    · rw [finrank_bot, hq]
    · intro a _ ha0
      obtain ⟨r, hr, he⟩ := exists_pos_form_rt_eq_im_mul hP _ (hscal _ hc) ha0
      rw [he]
      nlinarith [mul_pos hsq hr]
    · intro a ha h0
      exact absurd ((Submodule.mem_bot _).1 ha) h0

end GlobalTheory.CompRat
