import Formalism.SharpRestriction.GrowthBounds.ObjPol

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

open Formalism.MainNotions.G

open Classical in

def vecDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) : ℕ :=
  ∑ v ∈ al.support, if v.1 ∈ S ∧ LL.vec v.1 = true then al v else 0

open Classical in

def covDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) : ℕ :=
  ∑ v ∈ al.support, if v.1 ∈ S ∧ LL.vec v.1 = false then al v else 0

structure flt_Fil (B : Type*) [CommRing B] where
  F : ℤ → AddSubgroup B
  mul_mem : ∀ {t u : ℤ} {a b : B}, a ∈ F t → b ∈ F u → a * b ∈ F (t + u)
  one_mem : (1 : B) ∈ F 0
  anti : ∀ {t u : ℤ}, t ≤ u → F u ≤ F t

def flt_L (A : Type*) [CommRing A] (e : ℤ) : flt_Fil (LaurentPolynomial A) where
  F t :=
    { carrier := {f | ∀ k : ℤ, f.coeff k ≠ 0 → t ≤ e * k}
      zero_mem' := by intro k hk; simp at hk
      add_mem' := by
        intro a b ha hb k hk
        by_cases h : a.coeff k = 0
        · apply hb k
          intro h'
          apply hk
          simp [AddMonoidAlgebra.coeff_add, h, h']
        · exact ha k h
      neg_mem' := by
        intro a ha k hk
        apply ha k
        intro h
        apply hk
        simp [AddMonoidAlgebra.coeff_neg, h] }
  mul_mem := by
    classical
    intro t u a b ha hb k hk
    have hk' : k ∈ (a * b).coeff.support := Finsupp.mem_support_iff.2 hk
    have := AddMonoidAlgebra.support_coeff_mul_subset a b hk'
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 this
    have h1 := ha x (Finsupp.mem_support_iff.1 hx)
    have h2 := hb y (Finsupp.mem_support_iff.1 hy)
    rw [mul_add]
    exact add_le_add h1 h2
  one_mem := by
    intro k hk
    have : k = 0 := by
      by_contra h
      apply hk
      rw [← LaurentPolynomial.T_zero, LaurentPolynomial.T_apply, if_neg (Ne.symm h)]
    simp [this]
  anti := by
    intro t u h f hf k hk
    exact h.trans (hf k hk)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem flt_L_mem {A : Type*} [CommRing A] {e t : ℤ} {f : LaurentPolynomial A} :
    f ∈ (flt_L A e).F t ↔ ∀ k : ℤ, f.coeff k ≠ 0 → t ≤ e * k := Iff.rfl

/- English proof (translation)
Rewrite using `[flt_L_mem]`. Introduce `k hk`. Distinguish the cases in `h : k = 0`. Simplify using `[h]`. It suffices to derive a contradiction.

Apply `hk` to reduce the goal to its premises. Rewrite using `[← LaurentPolynomial.single_eq_C]`. Simplify using `[Finsupp.single_apply, Ne.symm h]`. Introduce `h'`. Conclude with `absurd h' h`.
-/
theorem flt_L_C {A : Type*} [CommRing A] (e : ℤ) (a : A) : LaurentPolynomial.C a ∈ (flt_L A e).F 0 := by
  rw [flt_L_mem]
  intro k hk
  by_cases h : k = 0
  · simp [h]
  · exfalso
    apply hk
    rw [← LaurentPolynomial.single_eq_C]
    simp [Finsupp.single_apply, Ne.symm h]
    intro h'
    exact absurd h' h

/- English proof (translation)
Rewrite using `[flt_L_mem]`. Introduce `k' hk`. Rewrite `hk` using `[LaurentPolynomial.T_apply]`. Use `split_ifs at hk with h`. Rewrite using `[h]`.

Conclude with `absurd rfl hk`.
-/
theorem T_mem_laurentFiltration {A : Type*} [CommRing A] (e k : ℤ) : (LaurentPolynomial.T k : LaurentPolynomial A) ∈ (flt_L A e).F (e * k) := by
  rw [flt_L_mem]
  intro k' hk
  rw [LaurentPolynomial.T_apply] at hk
  split_ifs at hk with h
  · rw [h]
  · exact absurd rfl hk

def flt_lift {B : Type*} [CommRing B] {σ : Type*} (Fl : flt_Fil B) (wt : (σ →₀ ℕ) →+ ℤ) :
    flt_Fil (MvPolynomial σ B) where
  F t :=
    { carrier := {P | ∀ m, coeff m P ∈ Fl.F (t - wt m)}
      zero_mem' := by intro m; simp
      add_mem' := by
        intro a b ha hb m
        rw [coeff_add]
        exact (Fl.F _).add_mem (ha m) (hb m)
      neg_mem' := by
        intro a ha m
        rw [coeff_neg]
        exact (Fl.F _).neg_mem (ha m) }
  mul_mem := by
    classical
    intro t u a b ha hb m
    rw [coeff_mul]
    refine (Fl.F _).sum_mem fun x hx => ?_
    have hx' : x.1 + x.2 = m := by simpa using hx
    have := Fl.mul_mem (ha x.1) (hb x.2)
    have e1 : t - wt x.1 + (u - wt x.2) = t + u - wt m := by
      rw [← hx', map_add]; ring
    rwa [e1] at this
  one_mem := by
    classical
    intro m
    rw [coeff_one]
    split_ifs with h
    · subst h
      simpa using Fl.one_mem
    · exact (Fl.F _).zero_mem
  anti := by
    intro t u h P hP m
    exact Fl.anti (by linarith) (hP m)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem flt_lift_mem {B : Type*} [CommRing B] {σ : Type*} {Fl : flt_Fil B} {wt : (σ →₀ ℕ) →+ ℤ} {t : ℤ}
    {P : MvPolynomial σ B} : P ∈ (flt_lift Fl wt).F t ↔ ∀ m, coeff m P ∈ Fl.F (t - wt m) := Iff.rfl

/- English proof (translation)
Rewrite using `[flt_lift_mem]`. Introduce `m'`. Rewrite using `[coeff_monomial]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Conclude with `ha`. Conclude with `(Fl.F _).zero_mem`.
-/
theorem flt_monomial_mem {B : Type*} [CommRing B] {σ : Type*} {Fl : flt_Fil B} {wt : (σ →₀ ℕ) →+ ℤ} {t : ℤ}
    {m : σ →₀ ℕ} {a : B} (ha : a ∈ Fl.F (t - wt m)) : monomial m a ∈ (flt_lift Fl wt).F t := by
  classical
  rw [flt_lift_mem]
  intro m'
  rw [coeff_monomial]
  split_ifs with h
  · subst h; exact ha
  · exact (Fl.F _).zero_mem

/- English proof (translation)
Use `flt_monomial_mem (wt := wt) (m := 0) (a := a) (t := t) (by simpa using ha)` as an intermediate fact. Rewrite `this` using `[← C_apply]`. Then use the resulting hypothesis.
-/
theorem flt_C_mem {B : Type*} [CommRing B] {σ : Type*} {Fl : flt_Fil B} {wt : (σ →₀ ℕ) →+ ℤ} {t : ℤ}
    {a : B} (ha : a ∈ Fl.F t) : (C a : MvPolynomial σ B) ∈ (flt_lift Fl wt).F t := by
  have := flt_monomial_mem (wt := wt) (m := 0) (a := a) (t := t) (by simpa using ha)
  rwa [← C_apply] at this

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using Fl.one_mem`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Use `Fl.mul_mem ih ha` as an intermediate fact.

Establish `e : ((k : ℤ) * t + t) = ((k + 1 : ℕ) : ℤ) * t` using `by push_cast; ring`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem flt_pow_mem {B : Type*} [CommRing B] (Fl : flt_Fil B) {t : ℤ} {a : B} (ha : a ∈ Fl.F t) (k : ℕ) :
    a ^ k ∈ Fl.F (k * t) := by
  induction k with
  | zero => simpa using Fl.one_mem
  | succ k ih =>
    rw [pow_succ]
    have := Fl.mul_mem ih ha
    have e : ((k : ℤ) * t + t) = ((k + 1 : ℕ) : ℤ) * t := by push_cast; ring
    rwa [e] at this

/- English proof (translation)
Use `Finsupp.induction m ?_ ?_` and prove the remaining obligations. Simplify using `using Fl'.one_mem`. Introduce `a b f _ _ ih`. Establish `e : monomial (Finsupp.single a b + f) (1 : B₀) = monomial (Finsupp.single a b) 1 * monomial f 1`. Rewrite using `[monomial_mul, one_mul]`.

Rewrite using `[e, ← X_pow_eq_monomial, map_mul, map_pow, map_add]`. Use `Fl'.mul_mem ?_ ih` and prove the remaining obligations. Establish `hp` using `flt_pow_mem Fl' (hX a) b`. Establish `e2 : Finsupp.single a b = b • Finsupp.single a 1` using `by simp`. Rewrite using `[e2, map_nsmul, nsmul_eq_mul]`.

Conclude with `hp`.
-/
theorem flt_hom_monomial {B₀ B' : Type*} [CommRing B₀] [CommRing B'] {σ : Type*} (Fl' : flt_Fil B')
    (φ : MvPolynomial σ B₀ →+* B') (wt : (σ →₀ ℕ) →+ ℤ)
    (hX : ∀ w, φ (X w) ∈ Fl'.F (wt (Finsupp.single w 1))) (m : σ →₀ ℕ) :
    φ (monomial m 1) ∈ Fl'.F (wt m) := by
  classical
  refine Finsupp.induction m ?_ ?_
  · simpa using Fl'.one_mem
  · intro a b f _ _ ih
    have e : monomial (Finsupp.single a b + f) (1 : B₀) = monomial (Finsupp.single a b) 1 * monomial f 1 := by
      rw [monomial_mul, one_mul]
    rw [e, ← X_pow_eq_monomial, map_mul, map_pow, map_add]
    refine Fl'.mul_mem ?_ ih
    have hp := flt_pow_mem Fl' (hX a) b
    have e2 : Finsupp.single a b = b • Finsupp.single a 1 := by simp
    rw [e2, map_nsmul, nsmul_eq_mul]
    exact hp

/- English proof (translation)
Rewrite using `[P.as_sum, map_sum]`. Use `(Fl'.F t).sum_mem fun m _ => ?_` and prove the remaining obligations. Establish `e : monomial m (coeff m P) = C (coeff m P) * monomial m 1`. Rewrite using `[C_mul_monomial, mul_one]`. Rewrite using `[e, map_mul]`.

Use `Fl'.mul_mem (hC _ _ ((flt_lift_mem.1 hP) m)) (flt_hom_monomial Fl' φ wt hX m)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem flt_hom_mem {B₀ B' : Type*} [CommRing B₀] [CommRing B'] {σ : Type*} (Fl : flt_Fil B₀) (Fl' : flt_Fil B')
    (φ : MvPolynomial σ B₀ →+* B') (wt : (σ →₀ ℕ) →+ ℤ)
    (hC : ∀ (t : ℤ) (b : B₀), b ∈ Fl.F t → φ (C b) ∈ Fl'.F t)
    (hX : ∀ w, φ (X w) ∈ Fl'.F (wt (Finsupp.single w 1))) {t : ℤ} {P : MvPolynomial σ B₀}
    (hP : P ∈ (flt_lift Fl wt).F t) : φ P ∈ Fl'.F t := by
  classical
  rw [P.as_sum, map_sum]
  refine (Fl'.F t).sum_mem fun m _ => ?_
  have e : monomial m (coeff m P) = C (coeff m P) * monomial m 1 := by
    rw [C_mul_monomial, mul_one]
  rw [e, map_mul]
  have := Fl'.mul_mem (hC _ _ ((flt_lift_mem.1 hP) m)) (flt_hom_monomial Fl' φ wt hX m)
  rwa [sub_add_cancel] at this

abbrev laurentCoeffFiltration (R : Type*) [CommRing R] (n : ℕ) (σ : Type*) (e : ℤ) : flt_Fil (MvPolynomial σ (GLLaurent R n)) :=
  flt_lift (flt_L (GLCoord R n) e) 0

/- English proof (translation)
Unfold `sDegs`. Rewrite using `[Finset.mem_biUnion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, -, hk⟩`. Conclude with `⟨m, Finsupp.mem_support_iff.1 hk⟩`.

Introduce and unpack `⟨m, hm⟩`. Use `⟨m, ?_, Finsupp.mem_support_iff.2 hm⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_support_iff]`. Introduce `h`. Apply `hm` to reduce the goal to its premises.

Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem flt_mem_sDegs {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (G : MvPolynomial (ι × Fin n) R) (k : ℤ) :
    k ∈ sDegs LL S j G ↔ ∃ m, ((twistSub LL S j G).coeff m).coeff k ≠ 0 := by
  classical
  unfold sDegs
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨m, -, hk⟩
    exact ⟨m, Finsupp.mem_support_iff.1 hk⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_, Finsupp.mem_support_iff.2 hm⟩
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hm
    rw [h]
    rfl

/- English proof (translation)
Unfold `valS`. Rewrite using `[Finset.le_inf_iff, flt_lift_mem]`. Prove the components needed by the constructor for the conclusion. Introduce `h m`. Rewrite using `[flt_L_mem]`.

Introduce `k hk`. Use `h k ((flt_mem_sDegs LL S _ G k).2 ⟨m, hk⟩)` as an intermediate fact. Simplify using `only [AddMonoidHom.zero_apply, sub_zero, one_mul]`. Conclude with `WithTop.coe_le_coe.1 this`. Introduce `h k hk`.

Take `⟨m, hm⟩` from `(flt_mem_sDegs LL S _ G k).1 hk`. Use `(flt_L_mem.1 (h m)) k hm` as an intermediate fact. Simplify using `only [AddMonoidHom.zero_apply, sub_zero, one_mul] at this`. Conclude with `WithTop.coe_le_coe.2 this`.
-/
theorem flt_le_valS {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) (t : ℤ) :
    (t : WithTop ℤ) ≤ valS LL S G ↔ twistSub LL S (lastIdx n) G ∈ (laurentCoeffFiltration R n (ι × Fin n) 1).F t := by
  unfold valS
  rw [Finset.le_inf_iff, flt_lift_mem]
  constructor
  · intro h m
    rw [flt_L_mem]
    intro k hk
    have := h k ((flt_mem_sDegs LL S _ G k).2 ⟨m, hk⟩)
    simp only [AddMonoidHom.zero_apply, sub_zero, one_mul]
    exact WithTop.coe_le_coe.1 this
  · intro h k hk
    obtain ⟨m, hm⟩ := (flt_mem_sDegs LL S _ G k).1 hk
    have := (flt_L_mem.1 (h m)) k hm
    simp only [AddMonoidHom.zero_apply, sub_zero, one_mul] at this
    exact WithTop.coe_le_coe.2 this

/- English proof (translation)
Unfold `lam1S`. Rewrite using `[Finset.sup_le_iff, flt_lift_mem]`. Prove the components needed by the constructor for the conclusion. Introduce `h m`. Rewrite using `[flt_L_mem]`.

Introduce `k hk`. Use `WithBot.coe_le_coe.1 (h k ((flt_mem_sDegs LL S _ G k).2 ⟨m, hk⟩))` as an intermediate fact. Simplify using `only [AddMonoidHom.zero_apply, sub_zero, neg_one_mul, neg_le_neg_iff]`. Conclude with `this`. Introduce `h k hk`.

Take `⟨m, hm⟩` from `(flt_mem_sDegs LL S _ G k).1 hk`. Use `(flt_L_mem.1 (h m)) k hm` as an intermediate fact. Simplify using `only [AddMonoidHom.zero_apply, sub_zero, neg_one_mul, neg_le_neg_iff] at this`. Conclude with `WithBot.coe_le_coe.2 this`.
-/
theorem flt_lam1S_le {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) (M : ℤ) :
    lam1S LL S G ≤ (M : WithBot ℤ) ↔ twistSub LL S (0 : Fin n) G ∈ (laurentCoeffFiltration R n (ι × Fin n) (-1)).F (-M) := by
  unfold lam1S
  rw [Finset.sup_le_iff, flt_lift_mem]
  constructor
  · intro h m
    rw [flt_L_mem]
    intro k hk
    have := WithBot.coe_le_coe.1 (h k ((flt_mem_sDegs LL S _ G k).2 ⟨m, hk⟩))
    simp only [AddMonoidHom.zero_apply, sub_zero, neg_one_mul, neg_le_neg_iff]
    exact this
  · intro h k hk
    obtain ⟨m, hm⟩ := (flt_mem_sDegs LL S _ G k).1 hk
    have := (flt_L_mem.1 (h m)) k hm
    simp only [AddMonoidHom.zero_apply, sub_zero, neg_one_mul, neg_le_neg_iff] at this
    exact WithBot.coe_le_coe.2 this

/- English proof (translation)
Proceed by induction on `a using WithTop.recTopCoe with`. Consider the case `top`. Proceed by induction on `b using WithTop.recTopCoe with`. Consider the case `top => simp`. Consider the case `coe c`.

It suffices to derive a contradiction. Use `WithTop.coe_le_coe.1 (h (c + N + 1) le_top)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `coe x`. Establish `h1` using `h x le_rfl`.

Proceed by induction on `b using WithTop.recTopCoe with`. Consider the case `top => simp`. Consider the case `coe c`. Use `WithTop.coe_le_coe.1 h1` as an intermediate fact. Rewrite using `[← WithTop.coe_add, WithTop.coe_le_coe]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem flt_withTop_le {a b : WithTop ℤ} {N : ℤ}
    (h : ∀ t : ℤ, (t : WithTop ℤ) ≤ a → ((t - N : ℤ) : WithTop ℤ) ≤ b) : a ≤ b + (N : WithTop ℤ) := by
  induction a using WithTop.recTopCoe with
  | top =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe c =>
      exfalso
      have := WithTop.coe_le_coe.1 (h (c + N + 1) le_top)
      linarith
  | coe x =>
    have h1 := h x le_rfl
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe c =>
      have := WithTop.coe_le_coe.1 h1
      rw [← WithTop.coe_add, WithTop.coe_le_coe]
      linarith

/- English proof (translation)
Proceed by induction on `b using WithBot.recBotCoe with`. Consider the case `bot`. Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => simp`. Consider the case `coe x`.

It suffices to derive a contradiction. Use `WithBot.coe_le_coe.1 (h (x - N - 1) bot_le)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `coe c`. Use `h c le_rfl` as an intermediate fact.

Rewrite using `[← WithBot.coe_add]` and apply the resulting hypothesis.
-/
theorem flt_withBot_le {a b : WithBot ℤ} {N : ℤ}
    (h : ∀ M : ℤ, b ≤ (M : WithBot ℤ) → a ≤ ((M + N : ℤ) : WithBot ℤ)) : a ≤ b + (N : WithBot ℤ) := by
  induction b using WithBot.recBotCoe with
  | bot =>
    induction a using WithBot.recBotCoe with
    | bot => simp
    | coe x =>
      exfalso
      have := WithBot.coe_le_coe.1 (h (x - N - 1) bot_le)
      linarith
  | coe c =>
    have := h c le_rfl
    rwa [← WithBot.coe_add]

/- English proof (translation)
Proceed by induction on `a using WithTop.recTopCoe with`. Consider the case `top`. Proceed by induction on `c using WithTop.recTopCoe with`. Consider the case `top => exact le_top`. Consider the case `coe z`.

It suffices to derive a contradiction. Proceed by induction on `b using WithTop.recTopCoe with`. Consider the case `top`. Use `WithTop.coe_le_coe.1 (h (z + 1) 0 le_top le_top)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Consider the case `coe y`. Use `WithTop.coe_le_coe.1 (h (z - y + 1) y le_top le_rfl)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `coe x`. Proceed by induction on `b using WithTop.recTopCoe with`.

Consider the case `top`. Proceed by induction on `c using WithTop.recTopCoe with`. Consider the case `top => exact le_top`. Consider the case `coe z`. It suffices to derive a contradiction.

Use `WithTop.coe_le_coe.1 (h x (z - x + 1) le_rfl le_top)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `coe y`. Rewrite using `[← WithTop.coe_add]`. Conclude with `h x y le_rfl le_rfl`.
-/
theorem flt_withTop_add_le {a b c : WithTop ℤ}
    (h : ∀ t u : ℤ, (t : WithTop ℤ) ≤ a → (u : WithTop ℤ) ≤ b → ((t + u : ℤ) : WithTop ℤ) ≤ c) : a + b ≤ c := by
  induction a using WithTop.recTopCoe with
  | top =>
    induction c using WithTop.recTopCoe with
    | top => exact le_top
    | coe z =>
      exfalso
      induction b using WithTop.recTopCoe with
      | top =>
        have := WithTop.coe_le_coe.1 (h (z + 1) 0 le_top le_top)
        linarith
      | coe y =>
        have := WithTop.coe_le_coe.1 (h (z - y + 1) y le_top le_rfl)
        linarith
  | coe x =>
    induction b using WithTop.recTopCoe with
    | top =>
      induction c using WithTop.recTopCoe with
      | top => exact le_top
      | coe z =>
        exfalso
        have := WithTop.coe_le_coe.1 (h x (z - x + 1) le_rfl le_top)
        linarith
    | coe y =>
      rw [← WithTop.coe_add]
      exact h x y le_rfl le_rfl

/- English proof (translation)
Proceed by induction on `c using WithBot.recBotCoe with`. Consider the case `bot => exact bot_le`. Consider the case `coe z`. Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot`.

It suffices to derive a contradiction. Proceed by induction on `b using WithBot.recBotCoe with`. Consider the case `bot`. Use `WithBot.coe_le_coe.1 (h (z - 1) 0 bot_le bot_le)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Consider the case `coe y`. Use `WithBot.coe_le_coe.1 (h (z - y - 1) y bot_le le_rfl)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `coe x`. Proceed by induction on `b using WithBot.recBotCoe with`.

Consider the case `bot`. It suffices to derive a contradiction. Use `WithBot.coe_le_coe.1 (h x (z - x - 1) le_rfl bot_le)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `coe y`.

Rewrite using `[← WithBot.coe_add]`. Conclude with `h x y le_rfl le_rfl`.
-/
theorem flt_withBot_le_add {a b c : WithBot ℤ}
    (h : ∀ t u : ℤ, a ≤ (t : WithBot ℤ) → b ≤ (u : WithBot ℤ) → c ≤ ((t + u : ℤ) : WithBot ℤ)) : c ≤ a + b := by
  induction c using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe z =>
    induction a using WithBot.recBotCoe with
    | bot =>
      exfalso
      induction b using WithBot.recBotCoe with
      | bot =>
        have := WithBot.coe_le_coe.1 (h (z - 1) 0 bot_le bot_le)
        linarith
      | coe y =>
        have := WithBot.coe_le_coe.1 (h (z - y - 1) y bot_le le_rfl)
        linarith
    | coe x =>
      induction b using WithBot.recBotCoe with
      | bot =>
        exfalso
        have := WithBot.coe_le_coe.1 (h x (z - x - 1) le_rfl bot_le)
        linarith
      | coe y =>
        rw [← WithBot.coe_add]
        exact h x y le_rfl le_rfl

/- English proof (translation)
Establish `key` using `flt_withTop_le (a := min (valS LL S F) (valS LL S G)) (b := valS LL S (F + G)) (N := 0) ?_`. Simplify using `using key`. Introduce `t ht`. Take `⟨h1, h2⟩` from `le_min_iff.1 ht`. Simplify using `only [sub_zero]`.

Rewrite `h1`, `h2`, the goal using `[flt_le_valS]`. Rewrite using `[map_add]`. Conclude with `AddSubgroup.add_mem _ h1 h2`.
-/
theorem flt_valS_add {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : min (valS LL S F) (valS LL S G) ≤ valS LL S (F + G) := by
  have key := flt_withTop_le (a := min (valS LL S F) (valS LL S G)) (b := valS LL S (F + G)) (N := 0) ?_
  · simpa using key
  intro t ht
  obtain ⟨h1, h2⟩ := le_min_iff.1 ht
  simp only [sub_zero]
  rw [flt_le_valS] at h1 h2 ⊢
  rw [map_add]
  exact AddSubgroup.add_mem _ h1 h2

/- English proof (translation)
Establish `key` using `flt_withBot_le (a := lam1S LL S (F + G)) (b := max (lam1S LL S F) (lam1S LL S G)) (N := 0) ?_`. Simplify using `using key`. Introduce `M hM`. Take `⟨h1, h2⟩` from `max_le_iff.1 hM`. Simplify using `only [add_zero]`.

Rewrite `h1`, `h2`, the goal using `[flt_lam1S_le]`. Rewrite using `[map_add]`. Conclude with `AddSubgroup.add_mem _ h1 h2`.
-/
theorem flt_lam1S_add {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : lam1S LL S (F + G) ≤ max (lam1S LL S F) (lam1S LL S G) := by
  have key := flt_withBot_le (a := lam1S LL S (F + G)) (b := max (lam1S LL S F) (lam1S LL S G)) (N := 0) ?_
  · simpa using key
  intro M hM
  obtain ⟨h1, h2⟩ := max_le_iff.1 hM
  simp only [add_zero]
  rw [flt_lam1S_le] at h1 h2 ⊢
  rw [map_add]
  exact AddSubgroup.add_mem _ h1 h2

/- English proof (translation)
Apply `flt_withTop_add_le` to reduce the goal to its premises. Introduce `t u ht hu`. Rewrite `ht`, `hu`, the goal using `[flt_le_valS]`. Rewrite using `[map_mul]`. Conclude with `(laurentCoeffFiltration R n (ι × Fin n) 1).mul_mem ht hu`.
-/
theorem flt_valS_mul_ge {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : valS LL S F + valS LL S G ≤ valS LL S (F * G) := by
  apply flt_withTop_add_le
  intro t u ht hu
  rw [flt_le_valS] at ht hu ⊢
  rw [map_mul]
  exact (laurentCoeffFiltration R n (ι × Fin n) 1).mul_mem ht hu

/- English proof (translation)
Apply `flt_withBot_le_add` to reduce the goal to its premises. Introduce `t u ht hu`. Rewrite `ht`, `hu`, the goal using `[flt_lam1S_le]`. Rewrite using `[map_mul]`. Use `(laurentCoeffFiltration R n (ι × Fin n) (-1)).mul_mem ht hu` as an intermediate fact.

Rewrite using `[show -(t + u) = -t + -u by ring]` and apply the resulting hypothesis.
-/
theorem flt_lam1S_mul_le {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : lam1S LL S (F * G) ≤ lam1S LL S F + lam1S LL S G := by
  apply flt_withBot_le_add
  intro t u ht hu
  rw [flt_lam1S_le] at ht hu ⊢
  rw [map_mul]
  have := (laurentCoeffFiltration R n (ι × Fin n) (-1)).mul_mem ht hu
  rwa [show -(t + u) = -t + -u by ring]

end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
