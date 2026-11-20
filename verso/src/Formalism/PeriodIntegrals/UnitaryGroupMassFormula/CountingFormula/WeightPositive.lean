import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DefFinWOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountPositivity.CardLeOfNegFamily

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
The claim follows from `((VS D).herm.eq x y).symm`.
-/
theorem hswap (D : Formalism.BasicNotions.D7) (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := ((VS D).herm.eq x y).symm

/- English proof (translation)
Rewrite using `[hswap, h, star_zero]`.
-/
theorem hzero_swap (D : Formalism.BasicNotions.D7) {x y : (VS D).V} (h : (VS D).hT x y = 0) : (VS D).hT y x = 0 := by
  rw [hswap, h, star_zero]

/- English proof (translation)
Rewrite using `[hswap, D.sp.hyp_ef i' i]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem hFE (D : Formalism.BasicNotions.D7) (i i' : Fin D.R.rS) :
    (VS D).hT (D.sp.hypF i) (D.sp.hypE i') = if i' = i then 1 else 0 := by
  rw [hswap, D.sp.hyp_ef i' i]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[hswap, (D.sp.hyp_orthz i).1, star_zero]`.
-/
theorem hEz (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypE i) D.sp.zm = 0 := by
  rw [hswap, (D.sp.hyp_orthz i).1, star_zero]

/- English proof (translation)
Rewrite using `[hswap, (D.sp.hyp_orthz i).2, star_zero]`.
-/
theorem hFz (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypF i) D.sp.zm = 0 := by
  rw [hswap, (D.sp.hyp_orthz i).2, star_zero]

/- English proof (translation)
Establish `hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)` using `D.sp.cm.cmUnram.2.1 τ`. Establish `h1 : starRingEnd ℂ (τ ((VS D).hT w w)) = τ ((VS D).hT w w)`. Rewrite using `[← hτ, ← hswap]`. Establish `him : (τ ((VS D).hT w w)).im = 0` using `Complex.conj_eq_iff_im.1 h1`. Conclude with `Complex.ext (by simp) (by simp [him])`.
-/
theorem real_of_emb (D : Formalism.BasicNotions.D7) (τ : D.host.E →+* ℂ) (w : (VS D).V) :
    τ ((VS D).hT w w) = ((τ ((VS D).hT w w)).re : ℂ) := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  have h1 : starRingEnd ℂ (τ ((VS D).hT w w)) = τ ((VS D).hT w w) := by
    rw [← hτ, ← hswap]
  have him : (τ ((VS D).hT w w)).im = 0 := Complex.conj_eq_iff_im.1 h1
  exact Complex.ext (by simp) (by simp [him])

/- English proof (translation)
Establish `hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)` using `D.sp.cm.cmUnram.2.1 τ`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `hT0 : (0 : ℝ) < D.sp.T` using `by exact_mod_cast D.sp.T_prime.pos`. Set `wv : Fin D.R.rS ⊕ Bool → (VS D).V` to `Sum.elim (fun a => D.sp.hypE a - D.sp.hypF a) (fun b => if b then w else D.sp.zm)`.

Set `d : Fin D.R.rS ⊕ Bool → ℝ` to `Sum.elim (fun _ => -2) (fun b => if b then (τ ((VS D).hT w w)).re else -(D.sp.T : ℝ))`. Establish `hoff : ∀ i j, i ≠ j → (VS D).hT (wv i) (wv j) = 0`. Introduce `i j hij`. Apply the tactic sequence `rcases i with a | b <;> rcases j with a' | b'`. Establish `ha : a ≠ a'` using `fun h => hij (by rw [h])`.

Establish `ha' : a' ≠ a` using `fun h => ha h.symm`. Simplify using `only [wv, Sum.elim_inl, map_sub, LinearMap.sub_apply, D.sp.hyp_ee, D.sp.hyp_ff, D.sp.hyp_ef, hFE, if_neg ha, if_neg ha']`. Simplify using the standard rewrite rules. Consider the cases of `b'`. Simplify using `only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub, LinearMap.sub_apply, hEz, hFz, sub_zero]`.

Simplify using `only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, LinearMap.sub_apply, hE, hF, sub_zero]`. Consider the cases of `b`. Simplify using `only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub, (D.sp.hyp_orthz a').1, (D.sp.hyp_orthz a').2, sub_zero]`. Simplify using `only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, hzero_swap D (hE a'), hzero_swap D (hF a'), sub_zero]`. Apply the tactic sequence `cases b <;> cases b'`.

Conclude with `absurd rfl hij`. Simplify `hz` using `[wv]`. Simplify `hzero_swap D hz` using `[wv]`. Conclude with `absurd rfl hij`. Establish `hdiag : ∀ i, τ ((VS D).hT (wv i) (wv i)) = (d i : ℂ)`.

Introduce `i`. Break down `i with a | b` into its components or cases. Simplify using `only [wv, d, Sum.elim_inl, map_sub, LinearMap.sub_apply, D.sp.hyp_ee, D.sp.hyp_ff, D.sp.hyp_ef, hFE, if_true]`. Rewrite using `[map_zero, map_one]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Consider the cases of `b`. Simplify using `only [wv, d, Sum.elim_inr, Bool.false_eq_true, if_false, D.sp.zm_norm, map_neg, map_natCast] push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [wv, d, Sum.elim_inr, if_true]`.

Conclude with `real_of_emb D τ w`. Establish `hneg : ∀ i, d i < 0`. Introduce `i`. Break down `i with a | b` into its components or cases. Simplify using `[d]`.

Consider the cases of `b`. Simplify using `only [d, Sum.elim_inr, Bool.false_eq_true, if_false]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify `hlt` using `[d]`. Establish `hc` using `PI.CntNotPosW.card_le_of_negFamily (VS D) τ hτ (D.sp.Y_sig 0 τ) wv d hoff hdiag hneg`.

Establish `hq : ((D.sp.Y 0).sig τ).2 = D.R.rS + 1` using `by rw [D.sp.baseSpace_signature_eq τ]; rfl`. Rewrite `hc` using `[hq]`. Simplify using `only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] at hc`. Use linear arithmetic over natural numbers and integers.
-/
theorem semidef (D : Formalism.BasicNotions.D7) (w : (VS D).V) (hE : ∀ a, (VS D).hT (D.sp.hypE a) w = 0)
    (hF : ∀ a, (VS D).hT (D.sp.hypF a) w = 0) (hz : (VS D).hT D.sp.zm w = 0) (τ : D.host.E →+* ℂ) :
    0 ≤ (τ ((VS D).hT w w)).re := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  by_contra hlt
  rw [not_le] at hlt
  have hT0 : (0 : ℝ) < D.sp.T := by exact_mod_cast D.sp.T_prime.pos
  let wv : Fin D.R.rS ⊕ Bool → (VS D).V :=
    Sum.elim (fun a => D.sp.hypE a - D.sp.hypF a) (fun b => if b then w else D.sp.zm)
  let d : Fin D.R.rS ⊕ Bool → ℝ :=
    Sum.elim (fun _ => -2) (fun b => if b then (τ ((VS D).hT w w)).re else -(D.sp.T : ℝ))
  have hoff : ∀ i j, i ≠ j → (VS D).hT (wv i) (wv j) = 0 := by
    intro i j hij
    rcases i with a | b <;> rcases j with a' | b'
    · have ha : a ≠ a' := fun h => hij (by rw [h])
      have ha' : a' ≠ a := fun h => ha h.symm
      simp only [wv, Sum.elim_inl, map_sub, LinearMap.sub_apply, D.sp.hyp_ee, D.sp.hyp_ff, D.sp.hyp_ef,
        hFE, if_neg ha, if_neg ha']
      simp
    · cases b'
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub,
          LinearMap.sub_apply, hEz, hFz, sub_zero]
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, LinearMap.sub_apply, hE, hF,
          sub_zero]
    · cases b
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub,
          (D.sp.hyp_orthz a').1, (D.sp.hyp_orthz a').2, sub_zero]
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, hzero_swap D (hE a'),
          hzero_swap D (hF a'), sub_zero]
    · cases b <;> cases b'
      · exact absurd rfl hij
      · simpa [wv] using hz
      · simpa [wv] using hzero_swap D hz
      · exact absurd rfl hij
  have hdiag : ∀ i, τ ((VS D).hT (wv i) (wv i)) = (d i : ℂ) := by
    intro i
    rcases i with a | b
    · simp only [wv, d, Sum.elim_inl, map_sub, LinearMap.sub_apply, D.sp.hyp_ee, D.sp.hyp_ff,
        D.sp.hyp_ef, hFE, if_true]
      rw [map_zero, map_one]
      push_cast; ring
    · cases b
      · simp only [wv, d, Sum.elim_inr, Bool.false_eq_true, if_false, D.sp.zm_norm, map_neg,
          map_natCast]
        push_cast; ring
      · simp only [wv, d, Sum.elim_inr, if_true]
        exact real_of_emb D τ w
  have hneg : ∀ i, d i < 0 := by
    intro i
    rcases i with a | b
    · simp [d]
    · cases b
      · simp only [d, Sum.elim_inr, Bool.false_eq_true, if_false]; linarith
      · simpa [d] using hlt
  have hc := PI.CntNotPosW.card_le_of_negFamily (VS D) τ hτ (D.sp.Y_sig 0 τ) wv d hoff hdiag hneg
  have hq : ((D.sp.Y 0).sig τ).2 = D.R.rS + 1 := by rw [D.sp.baseSpace_signature_eq τ]; rfl
  rw [hq] at hc
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] at hc
  omega

/- English proof (translation)
Set `τ : D.host.E →+* ℂ` to `(IsAlgClosed.lift : D.host.E →ₐ[ℚ] ℂ).toRingHom`. Establish `hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)` using `D.sp.cm.cmUnram.2.1 τ`. Establish `orthW : ∀ y : (VS D).V, (∀ a, (VS D).hT (D.sp.hypE a) y = 0) → (∀ a, (VS D).hT (D.sp.hypF a) y = 0) → (VS D).hT D.sp.zm y = 0 → (VS D).hT w y = 0`. Introduce `y hyE hyF hyz`. Assume the negation of the conclusion as `hx`.

Use `set x := (VS D).hT w y with hxdef`. Establish `hτx : τ x ≠ 0` using `(map_ne_zero τ).2 hx`. Establish `hN : 0 < Complex.normSq (τ x)` using `Complex.normSq_pos.2 hτx`. Use `set y' : (VS D).V := star x • y with hy'`. Establish `hxx : τ (x * star x) = ((Complex.normSq (τ x) : ℝ) : ℂ)`.

Rewrite using `[map_mul, hτ, Complex.mul_conj]`. Establish `key : ∀ n : ℕ, 2 * n * Complex.normSq (τ x) ≤ (τ ((VS D).hT y' y')).re`. Introduce `n`. Use `set v : (VS D).V := (n : D.host.E) • w - y' with hv`. Establish `hvE : ∀ a, (VS D).hT (D.sp.hypE a) v = 0`.

Introduce `a`. Simplify using `[hv, hy', map_sub, map_smul, hE a, hyE a]`. Establish `hvF : ∀ a, (VS D).hT (D.sp.hypF a) v = 0`. Introduce `a`. Simplify using `[hv, hy', map_sub, map_smul, hF a, hyF a]`.

Establish `hvz : (VS D).hT D.sp.zm v = 0`. Simplify using `[hv, hy', map_sub, map_smul, hz, hyz]`. Establish `hs` using `semidef D v hvE hvF hvz τ`. Establish `hyw : (VS D).hT y w = star x` using `by rw [hswap]`. Establish `e1 : (VS D).hT v v = -(2 * (n : D.host.E)) * (x * star x) + (VS D).hT y' y'`.

Simplify using `only [hv, map_sub, LinearMap.sub_apply, map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_natCast, h0, hy', star_star, hyw, ← hxdef, RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (τ ((VS D).hT v v)).re = -(2 * n * Complex.normSq (τ x)) + (τ ((VS D).hT y' y')).re`. Rewrite using `[e1, map_add, map_mul, hxx, map_neg, map_mul, map_ofNat, map_natCast, Complex.add_re]`. Use `congr 1`.

Establish `: -(2 * (n : ℂ)) * ((Complex.normSq (τ x) : ℝ) : ℂ) = ((-(2 * n * Complex.normSq (τ x)) : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[this, Complex.ofReal_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨n, hn⟩` from `exists_nat_gt ((τ ((VS D).hT y' y')).re / (2 * Complex.normSq (τ x)))`. Establish `h2` using `key n`.

Rewrite `hn` using `[div_lt_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hzz : (VS D).hT D.sp.zm D.sp.zm ≠ 0`. Rewrite using `[D.sp.zm_norm, neg_ne_zero]`. Conclude with `D.sp.T_prime.ne_zero` after adjusting the coercions.

Apply `(VS D).nondeg.1 w` to reduce the goal to its premises. Introduce `x`. Use `set xW : (VS D).V := x - ∑ a, ((VS D).hT (D.sp.hypF a) x • D.sp.hypE a + (VS D).hT (D.sp.hypE a) x • D.sp.hypF a) - ((VS D).hT D.sp.zm x / (VS D).hT D.sp.zm D.sp.zm) • D.sp.zm with hxW`. Establish `hWE : ∀ b, (VS D).hT (D.sp.hypE b) xW = 0`. Introduce `b`.

Simplify using `[hxW, map_sub, map_sum, map_add, map_smul, D.sp.hyp_ee, D.sp.hyp_ef, hEz]`. Establish `hWF : ∀ b, (VS D).hT (D.sp.hypF b) xW = 0`. Introduce `b`. Simplify using `[hxW, map_sub, map_sum, map_add, map_smul, D.sp.hyp_ff, hFE, hFz]`. Establish `hWz : (VS D).hT D.sp.zm xW = 0`.

Simplify using `[hxW, map_sub, map_sum, map_add, map_smul, (D.sp.hyp_orthz _).1, (D.sp.hyp_orthz _).2, hzz]`. Establish `h1` using `orthW xW hWE hWF hWz`. Establish `hwE : ∀ a, (VS D).hT w (D.sp.hypE a) = 0` using `fun a => hzero_swap D (hE a)`. Establish `hwF : ∀ a, (VS D).hT w (D.sp.hypF a) = 0` using `fun a => hzero_swap D (hF a)`. Establish `hwz : (VS D).hT w D.sp.zm = 0` using `hzero_swap D hz`.

Simplify `h1` using `[hxW, map_sub, map_sum, map_add, map_smul, hwE, hwF, hwz]`.
-/
theorem isotropic_zero (D : Formalism.BasicNotions.D7) (w : (VS D).V) (hE : ∀ a, (VS D).hT (D.sp.hypE a) w = 0)
    (hF : ∀ a, (VS D).hT (D.sp.hypF a) w = 0) (hz : (VS D).hT D.sp.zm w = 0)
    (h0 : (VS D).hT w w = 0) : w = 0 := by
  let τ : D.host.E →+* ℂ := (IsAlgClosed.lift : D.host.E →ₐ[ℚ] ℂ).toRingHom
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ

  have orthW : ∀ y : (VS D).V, (∀ a, (VS D).hT (D.sp.hypE a) y = 0) →
      (∀ a, (VS D).hT (D.sp.hypF a) y = 0) → (VS D).hT D.sp.zm y = 0 → (VS D).hT w y = 0 := by
    intro y hyE hyF hyz
    by_contra hx
    set x := (VS D).hT w y with hxdef
    have hτx : τ x ≠ 0 := (map_ne_zero τ).2 hx
    have hN : 0 < Complex.normSq (τ x) := Complex.normSq_pos.2 hτx
    set y' : (VS D).V := star x • y with hy'
    have hxx : τ (x * star x) = ((Complex.normSq (τ x) : ℝ) : ℂ) := by
      rw [map_mul, hτ, Complex.mul_conj]
    have key : ∀ n : ℕ, 2 * n * Complex.normSq (τ x) ≤ (τ ((VS D).hT y' y')).re := by
      intro n
      set v : (VS D).V := (n : D.host.E) • w - y' with hv
      have hvE : ∀ a, (VS D).hT (D.sp.hypE a) v = 0 := by
        intro a; simp [hv, hy', map_sub, map_smul, hE a, hyE a]
      have hvF : ∀ a, (VS D).hT (D.sp.hypF a) v = 0 := by
        intro a; simp [hv, hy', map_sub, map_smul, hF a, hyF a]
      have hvz : (VS D).hT D.sp.zm v = 0 := by
        simp [hv, hy', map_sub, map_smul, hz, hyz]
      have hs := semidef D v hvE hvF hvz τ
      have hyw : (VS D).hT y w = star x := by rw [hswap]
      have e1 : (VS D).hT v v = -(2 * (n : D.host.E)) * (x * star x) + (VS D).hT y' y' := by
        simp only [hv, map_sub, LinearMap.sub_apply, map_smulₛₗ, map_smul, LinearMap.smul_apply,
          smul_eq_mul, starRingEnd_apply, star_natCast, h0, hy', star_star, hyw, ← hxdef, RingHom.id_apply]
        ring
      have e2 : (τ ((VS D).hT v v)).re =
          -(2 * n * Complex.normSq (τ x)) + (τ ((VS D).hT y' y')).re := by
        rw [e1, map_add, map_mul, hxx, map_neg, map_mul, map_ofNat, map_natCast, Complex.add_re]
        congr 1
        have : -(2 * (n : ℂ)) * ((Complex.normSq (τ x) : ℝ) : ℂ) =
            ((-(2 * n * Complex.normSq (τ x)) : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((τ ((VS D).hT y' y')).re / (2 * Complex.normSq (τ x)))
    have h2 := key n
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith

  have hzz : (VS D).hT D.sp.zm D.sp.zm ≠ 0 := by
    rw [D.sp.zm_norm, neg_ne_zero]
    exact_mod_cast D.sp.T_prime.ne_zero
  apply (VS D).nondeg.1 w
  intro x
  set xW : (VS D).V := x - ∑ a, ((VS D).hT (D.sp.hypF a) x • D.sp.hypE a + (VS D).hT (D.sp.hypE a) x • D.sp.hypF a) -
    ((VS D).hT D.sp.zm x / (VS D).hT D.sp.zm D.sp.zm) • D.sp.zm with hxW
  have hWE : ∀ b, (VS D).hT (D.sp.hypE b) xW = 0 := by
    intro b
    simp [hxW, map_sub, map_sum, map_add, map_smul, D.sp.hyp_ee, D.sp.hyp_ef, hEz]
  have hWF : ∀ b, (VS D).hT (D.sp.hypF b) xW = 0 := by
    intro b
    simp [hxW, map_sub, map_sum, map_add, map_smul, D.sp.hyp_ff, hFE, hFz]
  have hWz : (VS D).hT D.sp.zm xW = 0 := by
    simp [hxW, map_sub, map_sum, map_add, map_smul, (D.sp.hyp_orthz _).1, (D.sp.hyp_orthz _).2, hzz]
  have h1 := orthW xW hWE hWF hWz
  have hwE : ∀ a, (VS D).hT w (D.sp.hypE a) = 0 := fun a => hzero_swap D (hE a)
  have hwF : ∀ a, (VS D).hT w (D.sp.hypF a) = 0 := fun a => hzero_swap D (hF a)
  have hwz : (VS D).hT w D.sp.zm = 0 := hzero_swap D hz
  simpa [hxW, map_sub, map_sum, map_add, map_smul, hwE, hwF, hwz] using h1

/- English proof (translation)
Introduce `D w hE hF hz hw`. Establish `pos : ∀ τ : D.host.E →+* ℂ, 0 < (τ ((VS D).hT w w)).re`. Introduce `τ`. Use `lt_of_le_of_ne (semidef D w hE hF hz τ) fun h => hw ?_` and prove the remaining obligations. Apply `isotropic_zero D w hE hF hz` to reduce the goal to its premises.

Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[real_of_emb D τ w, ← h, Complex.ofReal_zero, map_zero]`. Use `haveI : Nonempty (D.host.E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩`. Establish `ht` using `trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) (E := ℂ) (x := (VS D).hT w w)`. Establish `hre` using `congrArg Complex.re ht`.

Rewrite `hre` using `[Complex.re_sum]`. Establish `hsum : 0 < ∑ σ : D.host.E →ₐ[ℚ] ℂ, (σ ((VS D).hT w w)).re` using `Finset.sum_pos (fun σ _ => pos σ.toRingHom) Finset.univ_nonempty`. Rewrite `hsum` using `[← hre]`. Establish `: ((Algebra.trace ℚ D.host.E ((VS D).hT w w) : ℚ) : ℝ) = (algebraMap ℚ ℂ (Algebra.trace ℚ D.host.E ((VS D).hT w w))).re` using `by simp`. Rewrite `hsum` using `[← this]`.

Conclude with `hsum` after adjusting the coercions.
-/
theorem weights_are_positive : WPos := by
  intro D w hE hF hz hw
  have pos : ∀ τ : D.host.E →+* ℂ, 0 < (τ ((VS D).hT w w)).re := by
    intro τ
    refine lt_of_le_of_ne (semidef D w hE hF hz τ) fun h => hw ?_
    apply isotropic_zero D w hE hF hz
    apply τ.injective
    rw [real_of_emb D τ w, ← h, Complex.ofReal_zero, map_zero]
  haveI : Nonempty (D.host.E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have ht := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) (E := ℂ) (x := (VS D).hT w w)
  have hre := congrArg Complex.re ht
  rw [Complex.re_sum] at hre
  have hsum : 0 < ∑ σ : D.host.E →ₐ[ℚ] ℂ, (σ ((VS D).hT w w)).re :=
    Finset.sum_pos (fun σ _ => pos σ.toRingHom) Finset.univ_nonempty
  rw [← hre] at hsum
  have : ((Algebra.trace ℚ D.host.E ((VS D).hT w w) : ℚ) : ℝ) =
      (algebraMap ℚ ℂ (Algebra.trace ℚ D.host.E ((VS D).hT w w))).re := by simp
  rw [← this] at hsum
  exact_mod_cast hsum

/- English proof (translation)
The claim follows from `defFinW_of weights_are_positive`.
-/
theorem definite_finite : DefFinW := defFinW_of weights_are_positive

end PI.UnitaryGroupMassFormula.CntFormula
