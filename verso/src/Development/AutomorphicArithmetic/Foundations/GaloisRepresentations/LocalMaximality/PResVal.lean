import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section ResValAux
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}

private noncomputable def mono (x : Fin (d + 1) → F) (a : Fin d → ℕ) : F := ∏ l, (x l.succ / x 0) ^ a l

/- English proof (translation)
Simplify using `[mono]`.
-/
private lemma mono_zero (x : Fin (d + 1) → F) : mono x 0 = 1 := by simp [mono]

/- English proof (translation)
Simplify using `[mono, pow_add, Finset.prod_mul_distrib]`.
-/
private lemma mono_add (x : Fin (d + 1) → F) (a b : Fin d → ℕ) : mono x (a + b) = mono x a * mono x b := by
  simp [mono, pow_add, Finset.prod_mul_distrib]

/- English proof (translation)
Proceed by induction on `hy using Submonoid.closure_induction with`. Consider the case `mem z hz`. Take `⟨i, hi, j, rfl⟩` from `hz`. Rewrite `hi` using `[Finset.mem_singleton]`. Substitute `hi` using the available equality.

Consider the cases of `j using Fin.cases with`. Consider the case `zero => exact ⟨0, by rw [mono_zero, div_self hx]⟩`. Consider the case `succ l`. Use `⟨Pi.single l 1, ?_⟩` and prove the remaining obligations. Simplify using `only [mono]`.

Rewrite using `[Finset.prod_eq_single l]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`. Simplify using the standard rewrite rules.

Consider the case `one => exact ⟨0, (mono_zero x).symm⟩`. Consider the case `mul y z _ _ hy hz`. Take `⟨a, rfl⟩` from `hy`. Take `⟨b, rfl⟩` from `hz`. Conclude with `⟨a + b, (mono_add x a b).symm⟩`.
-/
private lemma mono_closure (x : Fin (d + 1) → F) (hx : x 0 ≠ 0) (y : F)
    (hy : y ∈ Submonoid.closure {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = x j / x i}) :
    ∃ a, y = mono x a := by
  induction hy using Submonoid.closure_induction with
  | mem z hz =>
    obtain ⟨i, hi, j, rfl⟩ := hz
    rw [Finset.mem_singleton] at hi
    subst hi
    cases j using Fin.cases with
    | zero => exact ⟨0, by rw [mono_zero, div_self hx]⟩
    | succ l =>
      refine ⟨Pi.single l 1, ?_⟩
      simp only [mono]
      rw [Finset.prod_eq_single l]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
  | one => exact ⟨0, (mono_zero x).symm⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, (mono_add x a b).symm⟩

/- English proof (translation)
Take `⟨_, hρ2⟩` from `hρ`. Use `set m : Fin (d + 1) → ℤ := Fin.cons (-(∑ l, (a l : ℤ))) (fun l => (a l : ℤ)) with hm`. Establish `hsum : ∑ j, m j = 0`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `[hm]`.

Establish `hne : m ≠ 0`. Introduce `h`. Apply `ha` to reduce the goal to its premises. Use function extensionality and compare the values at `l`. Simplify `congrFun h l.succ` using `[hm]`.

Establish `heq : mono x a = ∏ j, x j ^ m j`. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `only [hm, Fin.cons_zero, Fin.cons_succ, zpow_natCast, zpow_neg, mono, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]`. Rewrite using `[show (∑ l, (a l : ℤ)) = ((∑ l, a l : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[heq]`. Conclude with `hρ2 m hsum hne`.
-/
private lemma rho_mono (x : Fin (d + 1) → F) (hx : x 0 ≠ 0) (ρ : F →ₗ[ℂ] ℂ) (hρ : IsRes ℂ x ρ) (a : Fin d → ℕ)
    (ha : a ≠ 0) : ρ (mono x a) = 0 := by
  obtain ⟨_, hρ2⟩ := hρ
  set m : Fin (d + 1) → ℤ := Fin.cons (-(∑ l, (a l : ℤ))) (fun l => (a l : ℤ)) with hm
  have hsum : ∑ j, m j = 0 := by
    rw [Fin.sum_univ_succ]
    simp [hm]
  have hne : m ≠ 0 := by
    intro h
    apply ha
    funext l
    simpa [hm] using congrFun h l.succ
  have heq : mono x a = ∏ j, x j ^ m j := by
    rw [Fin.prod_univ_succ]
    simp only [hm, Fin.cons_zero, Fin.cons_succ, zpow_natCast, zpow_neg, mono, div_pow,
      Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
    rw [show (∑ l, (a l : ℤ)) = ((∑ l, a l : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
    ring
  rw [heq]
  exact hρ2 m hsum hne

end ResValAux

/- English proof (translation)
Introduce `hval F K _ _ _ _ _ _ d x hfc ρ hρ e f hf`. Take `⟨_, _, hBval, _⟩` from `hval K (rB ℂ K (xv x) {0}) e.1`. Establish `hx0 : xv x 0 ≠ 0` using `(x 0).ne_zero`. Establish `hmemB : ∀ g ∈ rA ℂ (xv x) {0}, algebraMap F K g ∈ rB ℂ K (xv x) {0}`. Introduce `g hg`.

Conclude with `(isIntegral_algebraMap : IsIntegral (rA ℂ (xv x) {0}) (algebraMap (rA ℂ (xv x) {0}) K ⟨g, hg⟩))`. Establish `hspan : ∀ g, g ∈ rA ℂ (xv x) {0} ↔ g ∈ Submodule.span ℂ (Submonoid.closure {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = xv x j / xv x i} : Set F)`. Introduce `g`. Rewrite using `[← Algebra.adjoin_eq_span]`. Both sides reduce to the same expression.

Establish `hmono : ∀ (a : Fin d → ℕ) (h : algebraMap F K (mono (xv x) a) ∈ rB ℂ K (xv x) {0}), e.1 ⟨_, h⟩ = ρ (mono (xv x) a)`. Introduce `a h`. Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Establish `h1 : (⟨algebraMap F K (mono (xv x) 0), h⟩ : rB ℂ K (xv x) {0}) = 1` using `Subtype.ext (by simp [mono_zero])`.

Rewrite using `[h1, map_one, mono_zero, hρ.1]`. Rewrite using `[rho_mono (xv x) hx0 ρ hρ a ha]`. Establish `h1 : (⟨algebraMap F K (mono (xv x) a), h⟩ : rB ℂ K (xv x) {0}) = ∏ l, (⟨algebraMap F K (xv x l.succ / xv x 0), tco_mem ℂ K (xv x) l⟩ : rB ℂ K (xv x) {0}) ^ a l` using `Subtype.ext (by simp [mono, map_prod, map_pow])`. Rewrite using `[h1, map_prod]`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l, a l ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `ha (funext hc)`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ l) (by rw [map_pow, e.2 l, zero_pow hl])`. Establish `key : ∀ g (hg : g ∈ Submodule.span ℂ (Submonoid.closure {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = xv x j / xv x i} : Set F)) (h : algebraMap F K g ∈ rB ℂ K (xv x) {0}), e.1 ⟨_, h⟩ = ρ g`.

Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem y hy`. Introduce `h`. Take `⟨a, rfl⟩` from `mono_closure (xv x) hx0 y hy`.

Conclude with `hmono a h`. Consider the case `zero`. Introduce `h`. Establish `h1 : (⟨algebraMap F K 0, h⟩ : rB ℂ K (xv x) {0}) = 0` using `Subtype.ext (map_zero _)`. Rewrite using `[h1, map_zero, map_zero]`.

Consider the case `add y z hy hz ihy ihz`. Introduce `h`. Establish `hy'` using `hmemB y ((hspan y).2 hy)`. Establish `hz'` using `hmemB z ((hspan z).2 hz)`. Establish `h1 : (⟨algebraMap F K (y + z), h⟩ : rB ℂ K (xv x) {0}) = ⟨_, hy'⟩ + ⟨_, hz'⟩` using `Subtype.ext (map_add _ _ _)`.

Rewrite using `[h1, map_add, map_add, ihy hy', ihz hz']`. Consider the case `smul r y hy ihy`. Introduce `h`. Establish `hy'` using `hmemB y ((hspan y).2 hy)`. Establish `h1 : (⟨algebraMap F K (r • y), h⟩ : rB ℂ K (xv x) {0}) = r • ⟨_, hy'⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show algebraMap F K (r • y) = r • algebraMap F K y`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[h1, map_smul, map_smul, ihy hy']`. Establish `hfB` using `hmemB f hf`.

Establish `hv` using `hBval ⟨_, hfB⟩`. Rewrite `hv` using `[key f ((hspan f).1 hf) hfB]`. Conclude with `hv`.
-/
theorem UpperTheory.Gal.productCup_of_system.resVal_of :
    ValBasic → ResVal := by
  intro hval F K _ _ _ _ _ _ d x hfc ρ hρ e f hf
  obtain ⟨_, _, hBval, _⟩ := hval K (rB ℂ K (xv x) {0}) e.1
  have hx0 : xv x 0 ≠ 0 := (x 0).ne_zero
  have hmemB : ∀ g ∈ rA ℂ (xv x) {0}, algebraMap F K g ∈ rB ℂ K (xv x) {0} := by
    intro g hg
    exact (isIntegral_algebraMap : IsIntegral (rA ℂ (xv x) {0}) (algebraMap (rA ℂ (xv x) {0}) K ⟨g, hg⟩))
  have hspan : ∀ g, g ∈ rA ℂ (xv x) {0} ↔ g ∈ Submodule.span ℂ
      (Submonoid.closure {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = xv x j / xv x i} : Set F) := by
    intro g
    rw [← Algebra.adjoin_eq_span]
    rfl
  have hmono : ∀ (a : Fin d → ℕ) (h : algebraMap F K (mono (xv x) a) ∈ rB ℂ K (xv x) {0}),
      e.1 ⟨_, h⟩ = ρ (mono (xv x) a) := by
    intro a h
    by_cases ha : a = 0
    · subst ha
      have h1 : (⟨algebraMap F K (mono (xv x) 0), h⟩ : rB ℂ K (xv x) {0}) = 1 :=
        Subtype.ext (by simp [mono_zero])
      rw [h1, map_one, mono_zero, hρ.1]
    · rw [rho_mono (xv x) hx0 ρ hρ a ha]
      have h1 : (⟨algebraMap F K (mono (xv x) a), h⟩ : rB ℂ K (xv x) {0}) =
          ∏ l, (⟨algebraMap F K (xv x l.succ / xv x 0), tco_mem ℂ K (xv x) l⟩ : rB ℂ K (xv x) {0}) ^ a l :=
        Subtype.ext (by simp [mono, map_prod, map_pow])
      rw [h1, map_prod]
      obtain ⟨l, hl⟩ : ∃ l, a l ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact ha (funext hc)
      exact Finset.prod_eq_zero (Finset.mem_univ l) (by rw [map_pow, e.2 l, zero_pow hl])
  have key : ∀ g (hg : g ∈ Submodule.span ℂ
      (Submonoid.closure {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = xv x j / xv x i} : Set F))
      (h : algebraMap F K g ∈ rB ℂ K (xv x) {0}), e.1 ⟨_, h⟩ = ρ g := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem y hy =>
      intro h
      obtain ⟨a, rfl⟩ := mono_closure (xv x) hx0 y hy
      exact hmono a h
    | zero =>
      intro h
      have h1 : (⟨algebraMap F K 0, h⟩ : rB ℂ K (xv x) {0}) = 0 := Subtype.ext (map_zero _)
      rw [h1, map_zero, map_zero]
    | add y z hy hz ihy ihz =>
      intro h
      have hy' := hmemB y ((hspan y).2 hy)
      have hz' := hmemB z ((hspan z).2 hz)
      have h1 : (⟨algebraMap F K (y + z), h⟩ : rB ℂ K (xv x) {0}) = ⟨_, hy'⟩ + ⟨_, hz'⟩ :=
        Subtype.ext (map_add _ _ _)
      rw [h1, map_add, map_add, ihy hy', ihz hz']
    | smul r y hy ihy =>
      intro h
      have hy' := hmemB y ((hspan y).2 hy)
      have h1 : (⟨algebraMap F K (r • y), h⟩ : rB ℂ K (xv x) {0}) = r • ⟨_, hy'⟩ := by
        apply Subtype.ext
        show algebraMap F K (r • y) = r • algebraMap F K y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
      rw [h1, map_smul, map_smul, ihy hy']
  have hfB := hmemB f hf
  have hv := hBval ⟨_, hfB⟩
  rw [key f ((hspan f).1 hf) hfB] at hv
  exact hv
