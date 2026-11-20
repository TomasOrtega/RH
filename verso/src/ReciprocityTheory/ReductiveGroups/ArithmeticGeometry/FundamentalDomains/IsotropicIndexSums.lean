import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ExistsPerpHermitianReduction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.SemistableReduction.LatAll

namespace ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Sesq

variable (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

/- English proof (translation)
Simplify using `only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
private lemma hermC_add_left_eq_add (u v w : Fin r → ℂ) :
    hermC τ G (u + v) w = hermC τ G u w + hermC τ G v w := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`.
-/
private lemma hermC_add_right_eq_add (u v w : Fin r → ℂ) :
    hermC τ G u (v + w) = hermC τ G u v + hermC τ G u w := by
  simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hermC_const_smul_left (c : ℂ) (u w : Fin r → ℂ) :
    hermC τ G (c • u) w = c * hermC τ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hermC_smul_right_section (c : ℂ) (u w : Fin r → ℂ) :
    hermC τ G u (c • w) = conj c * hermC τ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hermC]`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hermC_add_right_eq_add, ih]`.
-/
lemma hC_sum_right {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) (u : Fin r → ℂ) :
    hermC τ G u (∑ i ∈ s, f i) = ∑ i ∈ s, hermC τ G u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermC]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hermC_add_right_eq_add, ih]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hermC]`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hermC_add_left_eq_add, ih]`.
-/
private lemma hermC_finset_sum_left_eq_sum {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, f i) w = ∑ i ∈ s, hermC τ G (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermC]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hermC_add_left_eq_add, ih]

/- English proof (translation)
Rewrite using `[hermC_finset_sum_left_eq_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hermC_const_smul_left, hC_sum_right, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[hermC_smul_right_section]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma hC_comb {n : ℕ} (c : Fin n → ℂ) (v : Fin n → Fin r → ℂ) :
    hermC τ G (∑ k, c k • v k) (∑ l, c l • v l) =
      ∑ k, ∑ l, c k * conj (c l) * hermC τ G (v k) (v l) := by
  rw [hermC_finset_sum_left_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hermC_const_smul_left, hC_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hermC_smul_right_section]
  ring

/- English proof (translation)
Rewrite using `[hC_comb, ReciprocityTheory.MultiplicativeHeights.jForm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [hf, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, ReciprocityTheory.MultiplicativeHeights.sgn]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
lemma hC_comb_ortho {n p : ℕ} (f : Fin n → Fin r → ℂ)
    (hf : ∀ k l, hermC τ G (f k) (f l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
    (b : Fin n → ℂ) :
    hermC τ G (∑ k, b k • f k) (∑ l, b l • f l) = ReciprocityTheory.MultiplicativeHeights.jForm p b b := by
  rw [hC_comb, ReciprocityTheory.MultiplicativeHeights.jForm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hf, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, ReciprocityTheory.MultiplicativeHeights.sgn]
  split_ifs <;> ring

/- English proof (translation)
Establish `key : ∀ (d : Fin n → ℂ) (m : Fin n), hermC τ G (∑ k, d k • f k) (f m) = d m * (if (m : ℕ) < p then 1 else -1)`. Introduce `d m`. Rewrite using `[hermC_finset_sum_left_eq_sum]`. Simplify using `only [hermC_const_smul_left, hf, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use function extensionality and compare the values at `m`.

Establish `e` using `congrArg (fun w => hermC τ G w (f m)) h`. Simplify using `only [key] at e`. Apply the tactic sequence `have hs : (if (m : ℕ) < p then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num`. Conclude with `mul_right_cancel₀ hs e`.
-/
lemma coeff_unique {n p : ℕ} (f : Fin n → Fin r → ℂ)
    (hf : ∀ k l, hermC τ G (f k) (f l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
    {b c : Fin n → ℂ} (h : ∑ k, b k • f k = ∑ k, c k • f k) : b = c := by
  have key : ∀ (d : Fin n → ℂ) (m : Fin n),
      hermC τ G (∑ k, d k • f k) (f m) = d m * (if (m : ℕ) < p then 1 else -1) := by
    intro d m
    rw [hermC_finset_sum_left_eq_sum]
    simp only [hermC_const_smul_left, hf, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  funext m
  have e := congrArg (fun w => hermC τ G w (f m)) h
  simp only [key] at e
  have hs : (if (m : ℕ) < p then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
  exact mul_right_cancel₀ hs e

/- English proof (translation)
Rewrite `h` using `[Finset.sum_congr rfl fun a _ => Complex.mul_conj (c a), ← Complex.ofReal_sum]`. Establish `h' : ∑ a, Complex.normSq (c a) = 0` using `by exact_mod_cast h`. Use function extensionality and compare the values at `a`. Use `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (c i))).1 h' a (Finset.mem_univ _)` as an intermediate fact. Simplify using `using this`.
-/
lemma sum_mul_conj_eq_zero {n : ℕ} {c : Fin n → ℂ} (h : ∑ a, c a * conj (c a) = 0) : c = 0 := by
  rw [Finset.sum_congr rfl fun a _ => Complex.mul_conj (c a), ← Complex.ofReal_sum] at h
  have h' : ∑ a, Complex.normSq (c a) = 0 := by exact_mod_cast h
  funext a
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (c i))).1 h' a
    (Finset.mem_univ _)
  simpa using this

end Sesq

section Sig

variable (X : Data E r)

/- English proof (translation)
Introduce `h`. Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Use `congrFun h a` as an intermediate fact. Simplify `this` using `[Data.emb]`.
-/
lemma emb_ne {ξ : Fin r → E} (hne : ξ ≠ 0) (τ : E →+* ℂ) : Data.emb τ ξ ≠ 0 := by
  intro h
  apply hne
  funext a
  have := congrFun h a
  simpa [Data.emb] using this

/- English proof (translation)
Take `⟨P, hP, hg⟩` from `X.signature τ`. Use `set w : Fin r → ℂ := Data.emb τ.1 ξ with hw`. Establish `hw0 : w ≠ 0` using `emb_ne hne τ.1`. Establish `hww : hermC τ.1 X.Gm w w = 0`. Establish `e : hermC τ.1 X.Gm w w = τ.1 (herm X.Gm ξ ξ)`.

Simplify using `only [hw, hermC, herm, Data.emb, map_sum, map_mul, cc, IsCMField.complexEmbedding_complexConj]`. Rewrite using `[e, hξ, map_zero]`. Use `set z : Fin r → ℂ := P⁻¹ *ᵥ w with hz`. Establish `hwz : w = ∑ k, z k • col P k`. Establish `h1 : P *ᵥ z = w`.

Rewrite using `[hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP), Matrix.one_mulVec]`. Use function extensionality and compare the values at `a`. Rewrite using `[← h1]`. Simplify using `[Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]`. Establish `hcol : ∀ k l, hermC τ.1 X.Gm (col P k) (col P l) = if k = l then (if (k : ℕ) < X.p0 then 1 else -1) else 0`.

Introduce `k l`. Establish `e` using `congrFun (congrFun hg k) l`. Simplify using `only [gram, Matrix.of_apply, Matrix.diagonal_apply, sgn] at e`. Rewrite using `[e]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hj` using `hC_comb_ortho τ.1 X.Gm (col P) hcol z`. Rewrite `hj` using `[← hwz, hww]`. Establish `hz0 : z ≠ 0`. Introduce `h0`. Apply `hw0` to reduce the goal to its premises.

Rewrite using `[hwz, h0]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the negation of the conclusion as `hlt`. Establish `hp : X.p0 = 0` using `by omega`.

Apply `hz0` to reduce the goal to its premises. Apply `sum_mul_conj_eq_zero` to reduce the goal to its premises. Establish `e : ReciprocityTheory.MultiplicativeHeights.jForm X.p0 z z = -∑ a, z a * conj (z a)`. Rewrite using `[ReciprocityTheory.MultiplicativeHeights.jForm, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Simplify using `only [ReciprocityTheory.MultiplicativeHeights.sgn, hp, Nat.not_lt_zero, if_false]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hj` using `[e]`. Take the linear combination `hj`. Assume the negation of the conclusion as `hle push Not at hle`.

Apply `hz0` to reduce the goal to its premises. Apply `sum_mul_conj_eq_zero` to reduce the goal to its premises. Establish `e : ReciprocityTheory.MultiplicativeHeights.jForm X.p0 z z = ∑ a, z a * conj (z a)`. Rewrite using `[ReciprocityTheory.MultiplicativeHeights.jForm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[ReciprocityTheory.MultiplicativeHeights.sgn, if_pos (lt_of_lt_of_le a.isLt hle)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hj` using `[e]`. Take the linear combination `-hj`.
-/
lemma isotropicIndex_bounds {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (hne : ξ ≠ 0) (τ : X.Ψ) :
    1 ≤ X.p0 ∧ X.p0 < r := by
  obtain ⟨P, hP, hg⟩ := X.signature τ
  set w : Fin r → ℂ := Data.emb τ.1 ξ with hw
  have hw0 : w ≠ 0 := emb_ne hne τ.1
  have hww : hermC τ.1 X.Gm w w = 0 := by
    have e : hermC τ.1 X.Gm w w = τ.1 (herm X.Gm ξ ξ) := by
      simp only [hw, hermC, herm, Data.emb, map_sum, map_mul, cc, IsCMField.complexEmbedding_complexConj]
    rw [e, hξ, map_zero]

  set z : Fin r → ℂ := P⁻¹ *ᵥ w with hz
  have hwz : w = ∑ k, z k • col P k := by
    have h1 : P *ᵥ z = w := by
      rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP), Matrix.one_mulVec]
    funext a
    rw [← h1]
    simp [Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]
  have hcol : ∀ k l, hermC τ.1 X.Gm (col P k) (col P l) =
      if k = l then (if (k : ℕ) < X.p0 then 1 else -1) else 0 := by
    intro k l
    have e := congrFun (congrFun hg k) l
    simp only [gram, Matrix.of_apply, Matrix.diagonal_apply, sgn] at e
    rw [e]
    split_ifs <;> simp
  have hj := hC_comb_ortho τ.1 X.Gm (col P) hcol z
  rw [← hwz, hww] at hj
  have hz0 : z ≠ 0 := by
    intro h0
    apply hw0
    rw [hwz, h0]
    simp
  constructor
  · by_contra hlt
    have hp : X.p0 = 0 := by omega
    apply hz0
    apply sum_mul_conj_eq_zero
    have e : ReciprocityTheory.MultiplicativeHeights.jForm X.p0 z z = -∑ a, z a * conj (z a) := by
      rw [ReciprocityTheory.MultiplicativeHeights.jForm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [ReciprocityTheory.MultiplicativeHeights.sgn, hp, Nat.not_lt_zero, if_false]
      ring
    rw [e] at hj
    linear_combination hj
  · by_contra hle
    push Not at hle
    apply hz0
    apply sum_mul_conj_eq_zero
    have e : ReciprocityTheory.MultiplicativeHeights.jForm X.p0 z z = ∑ a, z a * conj (z a) := by
      rw [ReciprocityTheory.MultiplicativeHeights.jForm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [ReciprocityTheory.MultiplicativeHeights.sgn, if_pos (lt_of_lt_of_le a.isLt hle)]
      ring
    rw [e] at hj
    linear_combination -hj

end Sig

section Ucomp

variable (X : Data E r)

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [Data.embV, Data.emb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]`.
-/
lemma embV_add_smul (v : Fin r → E) (e : E) (ξ : Fin r → E) (τ : X.Ψ) :
    X.embV (v + e • ξ) τ = X.embV v τ + τ.1 e • Data.emb τ.1 ξ := by
  funext a
  simp only [Data.embV, Data.emb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma ucomp_apply (x : Frame X.Ψ r) (ξ : Fin r → E) (U : X.Ψ → Fin r → ℂ) (τ : X.Ψ) :
    X.ucomp x ξ U τ = U τ - (X.Hf x τ (U τ) (Data.emb τ.1 ξ) /
      X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := rfl

/- English proof (translation)
Unfold `Data.ppos`. Rewrite using `[Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← add_smul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hermC_add_left_eq_add, hermC_const_smul_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma ppos_add_smul (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) (c : ℂ) :
    X.ppos x τ (u + c • w) = X.ppos x τ u + c • X.ppos x τ w := by
  unfold Data.ppos
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, ← add_smul, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hermC_add_left_eq_add, hermC_const_smul_left]
  ring

/- English proof (translation)
Establish `hw0 : Data.emb τ.1 ξ ≠ 0` using `emb_ne hne τ.1`. Establish `hH : X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0`. Rewrite using `[Data.Hf_self X hx]`. Conclude with `(Data.maj_pos X hx τ hw0).ne'` after adjusting the coercions. Establish `hlin : ∀ (u w : Fin r → ℂ) (c : ℂ), X.Hf x τ (u + c • w) (Data.emb τ.1 ξ) = X.Hf x τ u (Data.emb τ.1 ξ) + c * X.Hf x τ w (Data.emb τ.1 ξ)`.

Introduce `u w c`. Simplify using `only [Data.Hf, ppos_add_smul]`. Rewrite using `[show (2 : ℂ) • (X.ppos x τ u + c • X.ppos x τ w) - (u + c • w) = ((2 : ℂ) • X.ppos x τ u - u) + c • ((2 : ℂ) • X.ppos x τ w - w) by module]`. Rewrite using `[hermC_add_left_eq_add, hermC_const_smul_left]`. Rewrite using `[ucomp_apply, ucomp_apply, embV_add_smul, hlin, add_div, mul_div_cancel_right₀ _ hH, add_smul]`.

Normalize the expressions using the abelian group laws.
-/
lemma ucomp_drop {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hne : ξ ≠ 0)
    (v : Fin r → E) (e : E) (τ : X.Ψ) :
    X.ucomp x ξ (X.embV (v + e • ξ)) τ = X.ucomp x ξ (X.embV v) τ := by
  have hw0 : Data.emb τ.1 ξ ≠ 0 := emb_ne hne τ.1
  have hH : X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    rw [Data.Hf_self X hx]
    exact_mod_cast (Data.maj_pos X hx τ hw0).ne'
  have hlin : ∀ (u w : Fin r → ℂ) (c : ℂ), X.Hf x τ (u + c • w) (Data.emb τ.1 ξ) =
      X.Hf x τ u (Data.emb τ.1 ξ) + c * X.Hf x τ w (Data.emb τ.1 ξ) := by
    intro u w c
    simp only [Data.Hf, ppos_add_smul]
    rw [show (2 : ℂ) • (X.ppos x τ u + c • X.ppos x τ w) - (u + c • w) =
        ((2 : ℂ) • X.ppos x τ u - u) + c • ((2 : ℂ) • X.ppos x τ w - w) by module]
    rw [hermC_add_left_eq_add, hermC_const_smul_left]
  rw [ucomp_apply, ucomp_apply, embV_add_smul, hlin, add_div, mul_div_cancel_right₀ _ hH, add_smul]
  abel

end Ucomp

end

end ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
