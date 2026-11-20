import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Rewrite using `[AddMonoidAlgebra.coeff_mul, Finsupp.sum, Finset.sum_eq_single a]`. Rewrite using `[Finsupp.sum, Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `k₂ hk₂ hne`. Distinguish the cases in `ha : a ∈ f.coeff.support`.

Rewrite using `[if_neg]`. Introduce `he`. Conclude with `hne (h a ha k₂ hk₂ he).2`. Establish `: f.coeff a = 0` using `by simpa using ha`. Simplify using `[this]`.

Introduce `hb`. Establish `: g.coeff b = 0` using `by simpa using hb`. Simplify using `[this]`. Introduce `k₁ hk₁ hne`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `k₂ hk₂`. Simplify using `only`. Rewrite using `[if_neg]`. Introduce `he`. Conclude with `hne (h k₁ hk₁ k₂ hk₂ he).1`.

Introduce `ha`. Establish `: f.coeff a = 0` using `by simpa using ha`. Simplify using `[this]`.
-/
private theorem laurent_mul_coeff_of_unique_decomp {B : Type*} [CommRing B] (f g : LaurentPolynomial B) (a b : ℤ)
    (h : ∀ k₁ ∈ f.coeff.support, ∀ k₂ ∈ g.coeff.support, k₁ + k₂ = a + b → k₁ = a ∧ k₂ = b) :
    (f * g).coeff (a + b) = f.coeff a * g.coeff b := by
  classical
  rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum, Finset.sum_eq_single a]
  · rw [Finsupp.sum, Finset.sum_eq_single b]
    · simp
    · intro k₂ hk₂ hne
      by_cases ha : a ∈ f.coeff.support
      · rw [if_neg]; intro he; exact hne (h a ha k₂ hk₂ he).2
      · have : f.coeff a = 0 := by simpa using ha
        simp [this]
    · intro hb
      have : g.coeff b = 0 := by simpa using hb
      simp [this]
  · intro k₁ hk₁ hne
    apply Finset.sum_eq_zero
    intro k₂ hk₂
    dsimp only; rw [if_neg]; intro he; exact hne (h k₁ hk₁ k₂ hk₂ he).1
  · intro ha
    have : f.coeff a = 0 := by simpa using ha
    simp [this]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Break down `f.coeff.support.eq_empty_or_nonempty with hf | hf` into its components or cases. Rewrite using `[hf, Finset.inf_empty, top_add]`. Conclude with `le_top`. Break down `g.coeff.support.eq_empty_or_nonempty with hg | hg` into its components or cases.

Rewrite using `[hg, Finset.inf_empty, add_top]`. Conclude with `le_top`. Establish `hc` using `laurent_mul_coeff_of_unique_decomp f g (f.coeff.support.min' hf) (g.coeff.support.min' hg) (by`. Introduce `k₁ hk₁ k₂ hk₂ he`. Establish `h1` using `Finset.min'_le _ _ hk₁`.

Establish `h2` using `Finset.min'_le _ _ hk₂`. Use the proof step `omega)`. Establish `hmem : f.coeff.support.min' hf + g.coeff.support.min' hg ∈ (f * g).coeff.support`. Rewrite using `[Finsupp.mem_support_iff, hc]`. Conclude with `mul_ne_zero (Finsupp.mem_support_iff.mp (Finset.min'_mem _ hf)) (Finsupp.mem_support_iff.mp (Finset.min'_mem _ hg))`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `AddMonoidAlgebra.le_infDegree_mul { toFun := fun k : ℤ => (k : WithTop ℤ), map_add' := fun a b => WithTop.coe_add a b } f g`.
-/
theorem mul_laurent_inf {B : Type*} [CommRing B] [IsDomain B] (f g : LaurentPolynomial B) :
    ((f * g).coeff.support.inf fun k => (k : WithTop ℤ)) =
      (f.coeff.support.inf fun k => (k : WithTop ℤ)) + (g.coeff.support.inf fun k => (k : WithTop ℤ)) := by
  classical
  apply le_antisymm
  · rcases f.coeff.support.eq_empty_or_nonempty with hf | hf
    · rw [hf, Finset.inf_empty, top_add]; exact le_top
    rcases g.coeff.support.eq_empty_or_nonempty with hg | hg
    · rw [hg, Finset.inf_empty, add_top]; exact le_top
    have hc := laurent_mul_coeff_of_unique_decomp f g (f.coeff.support.min' hf) (g.coeff.support.min' hg) (by
      intro k₁ hk₁ k₂ hk₂ he
      have h1 := Finset.min'_le _ _ hk₁
      have h2 := Finset.min'_le _ _ hk₂
      omega)
    have hmem : f.coeff.support.min' hf + g.coeff.support.min' hg ∈ (f * g).coeff.support := by
      rw [Finsupp.mem_support_iff, hc]
      exact mul_ne_zero (Finsupp.mem_support_iff.mp (Finset.min'_mem _ hf))
        (Finsupp.mem_support_iff.mp (Finset.min'_mem _ hg))
    calc _ ≤ (((f.coeff.support.min' hf + g.coeff.support.min' hg : ℤ)) : WithTop ℤ) := Finset.inf_le hmem
      _ = ((f.coeff.support.min' hf : ℤ) : WithTop ℤ) + ((g.coeff.support.min' hg : ℤ) : WithTop ℤ) :=
        WithTop.coe_add _ _
      _ = _ := by simp only [Finset.min'_eq_inf', Finset.coe_inf']; rfl
  · exact AddMonoidAlgebra.le_infDegree_mul { toFun := fun k : ℤ => (k : WithTop ℤ), map_add' := fun a b => WithTop.coe_add a b } f g

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `AddMonoidAlgebra.supDegree_mul_le (D := fun k : ℤ => (k : WithBot ℤ)) (fun a b => WithBot.coe_add a b) (p := f) (q := g)`. Break down `f.coeff.support.eq_empty_or_nonempty with hf | hf` into its components or cases. Rewrite using `[hf, Finset.sup_empty, WithBot.bot_add]`. Conclude with `bot_le`.

Break down `g.coeff.support.eq_empty_or_nonempty with hg | hg` into its components or cases. Rewrite using `[hg, Finset.sup_empty, WithBot.add_bot]`. Conclude with `bot_le`. Establish `hc` using `laurent_mul_coeff_of_unique_decomp f g (f.coeff.support.max' hf) (g.coeff.support.max' hg) (by`. Introduce `k₁ hk₁ k₂ hk₂ he`.

Establish `h1` using `Finset.le_max' _ _ hk₁`. Establish `h2` using `Finset.le_max' _ _ hk₂`. Use the proof step `omega)`. Establish `hmem : f.coeff.support.max' hf + g.coeff.support.max' hg ∈ (f * g).coeff.support`. Rewrite using `[Finsupp.mem_support_iff, hc]`.

Conclude with `mul_ne_zero (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hf)) (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hg))`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.max'_eq_sup', Finset.coe_sup']`. Both sides reduce to the same expression. Use `_ = (((f.coeff.support.max' hf + g.coeff.support.max' hg : ℤ)) : WithBot ℤ) := (WithBot.coe_add _ _).symm`.

Use `_ ≤ _ := Finset.le_sup (f := fun k : ℤ => ((k : ℤ) : WithBot ℤ)) (b := f.coeff.support.max' hf + g.coeff.support.max' hg) hmem`.
-/
theorem mul_laurent_sup {B : Type*} [CommRing B] [IsDomain B] (f g : LaurentPolynomial B) :
    ((f * g).coeff.support.sup fun k => (k : WithBot ℤ)) =
      (f.coeff.support.sup fun k => (k : WithBot ℤ)) + (g.coeff.support.sup fun k => (k : WithBot ℤ)) := by
  classical
  apply le_antisymm
  · exact AddMonoidAlgebra.supDegree_mul_le (D := fun k : ℤ => (k : WithBot ℤ)) (fun a b => WithBot.coe_add a b) (p := f) (q := g)
  · rcases f.coeff.support.eq_empty_or_nonempty with hf | hf
    · rw [hf, Finset.sup_empty, WithBot.bot_add]; exact bot_le
    rcases g.coeff.support.eq_empty_or_nonempty with hg | hg
    · rw [hg, Finset.sup_empty, WithBot.add_bot]; exact bot_le
    have hc := laurent_mul_coeff_of_unique_decomp f g (f.coeff.support.max' hf) (g.coeff.support.max' hg) (by
      intro k₁ hk₁ k₂ hk₂ he
      have h1 := Finset.le_max' _ _ hk₁
      have h2 := Finset.le_max' _ _ hk₂
      omega)
    have hmem : f.coeff.support.max' hf + g.coeff.support.max' hg ∈ (f * g).coeff.support := by
      rw [Finsupp.mem_support_iff, hc]
      exact mul_ne_zero (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hf))
        (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hg))
    calc _ = ((f.coeff.support.max' hf : ℤ) : WithBot ℤ) + ((g.coeff.support.max' hg : ℤ) : WithBot ℤ) := by
          simp only [Finset.max'_eq_sup', Finset.coe_sup']; rfl
      _ = (((f.coeff.support.max' hf + g.coeff.support.max' hg : ℤ)) : WithBot ℤ) := (WithBot.coe_add _ _).symm
      _ ≤ _ := Finset.le_sup (f := fun k : ℤ => ((k : ℤ) : WithBot ℤ)) (b := f.coeff.support.max' hf + g.coeff.support.max' hg) hmem

def mul_Phi (σ A : Type*) [CommRing A] :
    MvPolynomial σ (LaurentPolynomial A) →+* LaurentPolynomial (MvPolynomial σ A) :=
  MvPolynomial.eval₂Hom (AddMonoidAlgebra.mapRingHom ℤ (C : A →+* MvPolynomial σ A))
    (fun i => LaurentPolynomial.C (X i))

/- English proof (translation)
Establish `hCc : ∀ j : ℤ, (LaurentPolynomial.C q).coeff j = if j = 0 then q else 0`. Introduce `j`. Simplify using `[LaurentPolynomial.C_apply, Finsupp.single_apply, eq_comm]`. Establish `h` using `laurent_mul_coeff_of_unique_decomp y (LaurentPolynomial.C q) k 0 (by`. Introduce `k₁ _ k₂ hk₂ he`.

Establish `: k₂ = 0`. Assume the negation of the conclusion as `hne`. Rewrite `hk₂` using `[Finsupp.mem_support_iff, hCc, if_neg hne]`. Conclude with `hk₂ rfl`. Use the proof step `omega)`.

Rewrite `h` using `[add_zero]`. Rewrite using `[h, hCc, if_pos rfl]`.
-/
private theorem laurent_mul_C_coeff {B : Type*} [CommRing B] (y : LaurentPolynomial B) (q : B) (k : ℤ) :
    (y * LaurentPolynomial.C q).coeff k = y.coeff k * q := by
  have hCc : ∀ j : ℤ, (LaurentPolynomial.C q).coeff j = if j = 0 then q else 0 := by
    intro j
    simp [LaurentPolynomial.C_apply, Finsupp.single_apply, eq_comm]
  have h := laurent_mul_coeff_of_unique_decomp y (LaurentPolynomial.C q) k 0 (by
    intro k₁ _ k₂ hk₂ he
    have : k₂ = 0 := by
      by_contra hne
      rw [Finsupp.mem_support_iff, hCc, if_neg hne] at hk₂
      exact hk₂ rfl
    omega)
  rw [add_zero] at h
  rw [h, hCc, if_pos rfl]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial m' c`. Simplify using `only [mul_Phi, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]`. Establish `hprod : (m'.prod fun i e => (LaurentPolynomial.C (X i) : LaurentPolynomial (MvPolynomial σ A)) ^ e) = LaurentPolynomial.C (monomial m' 1)`. Rewrite using `[MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, map_finsuppProd]`.

Simplify using `[map_pow]`. Rewrite using `[hprod, laurent_mul_C_coeff]`. Establish `hmap : (AddMonoidAlgebra.mapRingHom ℤ (C : A →+* MvPolynomial σ A) c).coeff k = C (c.coeff k)`. Simplify using `[AddMonoidAlgebra.mapRingHom]`. Rewrite using `[hmap, MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]`.

Apply the tactic sequence `split_ifs <;> simp`. Consider the case `add p q hp hq => simp [map_add, hp, hq]`.
-/
theorem mul_Phi_coeff {σ A : Type*} [CommRing A] (P : MvPolynomial σ (LaurentPolynomial A)) (m : σ →₀ ℕ) (k : ℤ) :
    coeff m ((mul_Phi σ A P).coeff k) = (coeff m P).coeff k := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m' c =>
    simp only [mul_Phi, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
    have hprod : (m'.prod fun i e => (LaurentPolynomial.C (X i) : LaurentPolynomial (MvPolynomial σ A)) ^ e) =
        LaurentPolynomial.C (monomial m' 1) := by
      rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, map_finsuppProd]
      simp [map_pow]
    rw [hprod, laurent_mul_C_coeff]
    have hmap : (AddMonoidAlgebra.mapRingHom ℤ (C : A →+* MvPolynomial σ A) c).coeff k = C (c.coeff k) := by
      simp [AddMonoidAlgebra.mapRingHom]
    rw [hmap, MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs <;> simp
  | add p q hp hq => simp [map_add, hp, hq]

def mul_degs {σ A : Type*} [CommRing A] (P : MvPolynomial σ (LaurentPolynomial A)) : Finset ℤ :=
  P.support.biUnion fun m => (P.coeff m).coeff.support

/- English proof (translation)
Use extensionality with `k`. Simplify using `only [mul_degs, Finset.mem_biUnion, MvPolynomial.mem_support_iff, Finsupp.mem_support_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, -, hm⟩ h`. Apply `hm` to reduce the goal to its premises.

Rewrite using `[← mul_Phi_coeff, h]`. Simplify using the standard rewrite rules. Introduce `h`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, coeff m ((mul_Phi σ A P).coeff k) ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `h (by ext m; simpa using hc m)`. Rewrite `hm` using `[mul_Phi_coeff]`. Conclude with `⟨m, fun h0 => hm (by rw [h0]; simp), hm⟩`.
-/
theorem mul_degs_eq {σ A : Type*} [CommRing A] (P : MvPolynomial σ (LaurentPolynomial A)) :
    mul_degs P = (mul_Phi σ A P).coeff.support := by
  classical
  ext k
  simp only [mul_degs, Finset.mem_biUnion, MvPolynomial.mem_support_iff, Finsupp.mem_support_iff]
  constructor
  · rintro ⟨m, -, hm⟩ h
    apply hm
    rw [← mul_Phi_coeff, h]
    simp
  · intro h
    obtain ⟨m, hm⟩ : ∃ m, coeff m ((mul_Phi σ A P).coeff k) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h (by ext m; simpa using hc m)
    rw [mul_Phi_coeff] at hm
    exact ⟨m, fun h0 => hm (by rw [h0]; simp), hm⟩

instance mul_domGL (R : Type*) [Field R] (n : ℕ) : IsDomain (GLCoord R n) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
    (Matrix.det_mvPolynomialX_ne_zero (Fin n) R))

/- English proof (translation)
Establish `key : ∀ H : MvPolynomial (ι × Fin n) R, valS LL S H = ((mul_Phi _ _ (twistSub LL S (lastIdx n) H)).coeff.support.inf fun k => (k : WithTop ℤ))`. Introduce `H`. Rewrite using `[← mul_degs_eq]`. Both sides reduce to the same expression. Rewrite using `[key, key, key, map_mul, map_mul, mul_laurent_inf]`.
-/
theorem mul_valS_mul {R : Type*} [Field R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : valS LL S (F * G) = valS LL S F + valS LL S G := by
  have key : ∀ H : MvPolynomial (ι × Fin n) R, valS LL S H =
      ((mul_Phi _ _ (twistSub LL S (lastIdx n) H)).coeff.support.inf fun k => (k : WithTop ℤ)) := by
    intro H; rw [← mul_degs_eq]; rfl
  rw [key, key, key, map_mul, map_mul, mul_laurent_inf]

/- English proof (translation)
Establish `key : ∀ H : MvPolynomial (ι × Fin n) R, lam1S LL S H = ((mul_Phi _ _ (twistSub LL S (0 : Fin n) H)).coeff.support.sup fun k => (k : WithBot ℤ))`. Introduce `H`. Rewrite using `[← mul_degs_eq]`. Both sides reduce to the same expression. Rewrite using `[key, key, key, map_mul, map_mul, mul_laurent_sup]`.
-/
theorem mul_lam1S_mul {R : Type*} [Field R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : lam1S LL S (F * G) = lam1S LL S F + lam1S LL S G := by
  have key : ∀ H : MvPolynomial (ι × Fin n) R, lam1S LL S H =
      ((mul_Phi _ _ (twistSub LL S (0 : Fin n) H)).coeff.support.sup fun k => (k : WithBot ℤ)) := by
    intro H; rw [← mul_degs_eq]; rfl
  rw [key, key, key, map_mul, map_mul, mul_laurent_sup]

end Formalism.MainNotions.G.GLWeightTheory
