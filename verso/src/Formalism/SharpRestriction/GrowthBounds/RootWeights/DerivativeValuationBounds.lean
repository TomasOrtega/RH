import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

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
Rewrite using `[flt_L_mem]`. Introduce `k hk`. Rewrite `hk` using `[LaurentPolynomial.C_apply]`. Use `split_ifs at hk with h`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Conclude with `absurd rfl hk`.
-/
theorem flt_L_C {A : Type*} [CommRing A] (e : ℤ) (a : A) : LaurentPolynomial.C a ∈ (flt_L A e).F 0 := by
  rw [flt_L_mem]
  intro k hk
  rw [LaurentPolynomial.C_apply] at hk
  split_ifs at hk with h
  · subst h; simp
  · exact absurd rfl hk

/- English proof (translation)
Rewrite using `[flt_L_mem]`. Introduce `m hm`. Rewrite `hm` using `[LaurentPolynomial.T_apply]`. Use `split_ifs at hm with h`. Rewrite using `[h]`.

Conclude with `absurd rfl hm`.
-/
theorem T_mem_laurentFiltration {A : Type*} [CommRing A] (e k : ℤ) : (LaurentPolynomial.T k : LaurentPolynomial A) ∈ (flt_L A e).F (e * k) := by
  rw [flt_L_mem]
  intro m hm
  rw [LaurentPolynomial.T_apply] at hm
  split_ifs at hm with h
  · rw [h]
  · exact absurd rfl hm

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
Rewrite using `[flt_lift_mem]`. Introduce `m'`. Rewrite using `[MvPolynomial.coeff_monomial]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Conclude with `ha`. Conclude with `(Fl.F _).zero_mem`.
-/
theorem flt_monomial_mem {B : Type*} [CommRing B] {σ : Type*} {Fl : flt_Fil B} {wt : (σ →₀ ℕ) →+ ℤ} {t : ℤ}
    {m : σ →₀ ℕ} {a : B} (ha : a ∈ Fl.F (t - wt m)) : monomial m a ∈ (flt_lift Fl wt).F t := by
  classical
  rw [flt_lift_mem]
  intro m'
  rw [MvPolynomial.coeff_monomial]
  split_ifs with h
  · subst h; exact ha
  · exact (Fl.F _).zero_mem

/- English proof (translation)
Rewrite using `[MvPolynomial.C_apply]`. Conclude with `flt_monomial_mem (by rw [_root_.map_zero, sub_zero]; exact ha)`.
-/
theorem flt_C_mem {B : Type*} [CommRing B] {σ : Type*} {Fl : flt_Fil B} {wt : (σ →₀ ℕ) →+ ℤ} {t : ℤ}
    {a : B} (ha : a ∈ Fl.F t) : (C a : MvPolynomial σ B) ∈ (flt_lift Fl wt).F t := by
  rw [MvPolynomial.C_apply]
  exact flt_monomial_mem (by rw [_root_.map_zero, sub_zero]; exact ha)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using Fl.one_mem`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Establish `e1 : ((k + 1 : ℕ) : ℤ) * t = (k : ℤ) * t + t` using `by push_cast; ring`.

Rewrite using `[e1]`. Conclude with `Fl.mul_mem ih ha`.
-/
theorem flt_pow_mem {B : Type*} [CommRing B] (Fl : flt_Fil B) {t : ℤ} {a : B} (ha : a ∈ Fl.F t) (k : ℕ) :
    a ^ k ∈ Fl.F (k * t) := by
  induction k with
  | zero => simpa using Fl.one_mem
  | succ k ih =>
    rw [pow_succ]
    have e1 : ((k + 1 : ℕ) : ℤ) * t = (k : ℤ) * t + t := by push_cast; ring
    rw [e1]
    exact Fl.mul_mem ih ha

/- English proof (translation)
Proceed by induction on `m using Finsupp.induction`. Use `next =>`. Rewrite using `[← MvPolynomial.C_apply, _root_.map_one, _root_.map_one, _root_.map_zero]`. Conclude with `Fl'.one_mem`. Use `next a k f _ _ ih =>`.

Establish `e1 : monomial (Finsupp.single a k + f) (1 : B₀) = X a ^ k * monomial f 1`. Rewrite using `[MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]`. Establish `e2 : wt (Finsupp.single a k) = (k : ℤ) * wt (Finsupp.single a 1)`. Rewrite using `[← nsmul_eq_mul, ← _root_.map_nsmul, Finsupp.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[e1, _root_.map_mul, _root_.map_pow, _root_.map_add, e2]`.

Conclude with `Fl'.mul_mem (flt_pow_mem Fl' (hX a) k) ih`.
-/
theorem flt_hom_monomial {B₀ B' : Type*} [CommRing B₀] [CommRing B'] {σ : Type*} (Fl' : flt_Fil B')
    (φ : MvPolynomial σ B₀ →+* B') (wt : (σ →₀ ℕ) →+ ℤ)
    (hX : ∀ w, φ (X w) ∈ Fl'.F (wt (Finsupp.single w 1))) (m : σ →₀ ℕ) :
    φ (monomial m 1) ∈ Fl'.F (wt m) := by
  induction m using Finsupp.induction
  next =>
    rw [← MvPolynomial.C_apply, _root_.map_one, _root_.map_one, _root_.map_zero]
    exact Fl'.one_mem
  next a k f _ _ ih =>
    have e1 : monomial (Finsupp.single a k + f) (1 : B₀) = X a ^ k * monomial f 1 := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
    have e2 : wt (Finsupp.single a k) = (k : ℤ) * wt (Finsupp.single a 1) := by
      rw [← nsmul_eq_mul, ← _root_.map_nsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e1, _root_.map_mul, _root_.map_pow, _root_.map_add, e2]
    exact Fl'.mul_mem (flt_pow_mem Fl' (hX a) k) ih

/- English proof (translation)
Rewrite using `[P.as_sum, _root_.map_sum]`. Use `(Fl'.F t).sum_mem fun m _ => ?_` and prove the remaining obligations. Establish `e : monomial m (coeff m P) = C (coeff m P) * monomial m 1`. Rewrite using `[MvPolynomial.C_mul_monomial, mul_one]`. Rewrite using `[e, _root_.map_mul]`.

Establish `h` using `Fl'.mul_mem (hC _ _ ((flt_lift_mem.1 hP) m)) (flt_hom_monomial Fl' φ wt hX m)`. Rewrite `h` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem flt_hom_mem {B₀ B' : Type*} [CommRing B₀] [CommRing B'] {σ : Type*} (Fl : flt_Fil B₀) (Fl' : flt_Fil B')
    (φ : MvPolynomial σ B₀ →+* B') (wt : (σ →₀ ℕ) →+ ℤ)
    (hC : ∀ (t : ℤ) (b : B₀), b ∈ Fl.F t → φ (C b) ∈ Fl'.F t)
    (hX : ∀ w, φ (X w) ∈ Fl'.F (wt (Finsupp.single w 1))) {t : ℤ} {P : MvPolynomial σ B₀}
    (hP : P ∈ (flt_lift Fl wt).F t) : φ P ∈ Fl'.F t := by
  rw [P.as_sum, _root_.map_sum]
  refine (Fl'.F t).sum_mem fun m _ => ?_
  have e : monomial m (coeff m P) = C (coeff m P) * monomial m 1 := by
    rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [e, _root_.map_mul]
  have h := Fl'.mul_mem (hC _ _ ((flt_lift_mem.1 hP) m)) (flt_hom_monomial Fl' φ wt hX m)
  rwa [sub_add_cancel] at h

abbrev laurentCoeffFiltration (R : Type*) [CommRing R] (n : ℕ) (σ : Type*) (e : ℤ) : flt_Fil (MvPolynomial σ (GLLaurent R n)) :=
  flt_lift (flt_L (GLCoord R n) e) 0

/- English proof (translation)
Simplify using `only [sDegs]`. Rewrite using `[Finset.mem_biUnion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, -, hk⟩`. Conclude with `⟨m, Finsupp.mem_support_iff.1 hk⟩`.

Introduce and unpack `⟨m, hm⟩`. Use `⟨m, ?_, Finsupp.mem_support_iff.2 hm⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_support_iff]`. Introduce `h0`. Apply `hm` to reduce the goal to its premises.

Rewrite using `[h0]`. Simplify using the standard rewrite rules.
-/
theorem flt_mem_sDegs {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (G : MvPolynomial (ι × Fin n) R) (k : ℤ) :
    k ∈ sDegs LL S j G ↔ ∃ m, ((twistSub LL S j G).coeff m).coeff k ≠ 0 := by
  simp only [sDegs]
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨m, -, hk⟩
    exact ⟨m, Finsupp.mem_support_iff.1 hk⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_, Finsupp.mem_support_iff.2 hm⟩
    rw [MvPolynomial.mem_support_iff]
    intro h0
    apply hm
    rw [h0]
    simp

/- English proof (translation)
Simplify using `only [valS]`. Rewrite using `[Finset.le_inf_iff]`. Simplify using `only [laurentCoeffFiltration, flt_lift_mem, flt_L_mem, AddMonoidHom.zero_apply, sub_zero, one_mul, WithTop.coe_le_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `h m k hk`.

Conclude with `h k ((flt_mem_sDegs LL S _ G k).2 ⟨m, hk⟩)`. Introduce `h k hk`. Take `⟨m, hm⟩` from `(flt_mem_sDegs LL S _ G k).1 hk`. Conclude with `h m k hm`.
-/
theorem flt_le_valS {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) (t : ℤ) :
    (t : WithTop ℤ) ≤ valS LL S G ↔ twistSub LL S (lastIdx n) G ∈ (laurentCoeffFiltration R n (ι × Fin n) 1).F t := by
  simp only [valS]
  rw [Finset.le_inf_iff]
  simp only [laurentCoeffFiltration, flt_lift_mem, flt_L_mem, AddMonoidHom.zero_apply, sub_zero, one_mul, WithTop.coe_le_coe]
  constructor
  · intro h m k hk
    exact h k ((flt_mem_sDegs LL S _ G k).2 ⟨m, hk⟩)
  · intro h k hk
    obtain ⟨m, hm⟩ := (flt_mem_sDegs LL S _ G k).1 hk
    exact h m k hm

/- English proof (translation)
Simplify using `only [lam1S]`. Rewrite using `[Finset.sup_le_iff]`. Simplify using `only [laurentCoeffFiltration, flt_lift_mem, flt_L_mem, AddMonoidHom.zero_apply, sub_zero, WithBot.coe_le_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `h m k hk`.

Establish `h1` using `h k ((flt_mem_sDegs LL S _ G k).2 ⟨m, hk⟩)`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h k hk`. Take `⟨m, hm⟩` from `(flt_mem_sDegs LL S _ G k).1 hk`. Establish `h1` using `h m k hm`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem flt_lam1S_le {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) (M : ℤ) :
    lam1S LL S G ≤ (M : WithBot ℤ) ↔ twistSub LL S (0 : Fin n) G ∈ (laurentCoeffFiltration R n (ι × Fin n) (-1)).F (-M) := by
  simp only [lam1S]
  rw [Finset.sup_le_iff]
  simp only [laurentCoeffFiltration, flt_lift_mem, flt_L_mem, AddMonoidHom.zero_apply, sub_zero, WithBot.coe_le_coe]
  constructor
  · intro h m k hk
    have h1 := h k ((flt_mem_sDegs LL S _ G k).2 ⟨m, hk⟩)
    linarith
  · intro h k hk
    obtain ⟨m, hm⟩ := (flt_mem_sDegs LL S _ G k).1 hk
    have h1 := h m k hm
    linarith

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `top`. Proceed by induction on `b with`. Consider the case `top => simp`. Consider the case `coe y`.

It suffices to derive a contradiction. Establish `h1` using `WithTop.coe_le_coe.1 (h (y + N + 1) le_top)`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `coe x`. Establish `hx` using `h x le_rfl`.

Proceed by induction on `b with`. Consider the case `top => simp`. Consider the case `coe y`. Rewrite using `[← WithTop.coe_add]`. Conclude with `WithTop.coe_le_coe.2 (by have h1 := WithTop.coe_le_coe.1 hx; linarith)`.
-/
theorem flt_withTop_le {a b : WithTop ℤ} {N : ℤ}
    (h : ∀ t : ℤ, (t : WithTop ℤ) ≤ a → ((t - N : ℤ) : WithTop ℤ) ≤ b) : a ≤ b + (N : WithTop ℤ) := by
  induction a with
  | top =>
    induction b with
    | top => simp
    | coe y =>
      exfalso
      have h1 := WithTop.coe_le_coe.1 (h (y + N + 1) le_top)
      linarith
  | coe x =>
    have hx := h x le_rfl
    induction b with
    | top => simp
    | coe y =>
      rw [← WithTop.coe_add]
      exact WithTop.coe_le_coe.2 (by have h1 := WithTop.coe_le_coe.1 hx; linarith)

/- English proof (translation)
Proceed by induction on `b with`. Consider the case `bot`. Proceed by induction on `a with`. Consider the case `bot => simp`. Consider the case `coe x`.

It suffices to derive a contradiction. Establish `h1` using `WithBot.coe_le_coe.1 (h (x - N - 1) bot_le)`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `coe y`. Establish `h1` using `h y le_rfl`.

Rewrite using `[← WithBot.coe_add]`. Conclude with `h1`.
-/
theorem flt_withBot_le {a b : WithBot ℤ} {N : ℤ}
    (h : ∀ M : ℤ, b ≤ (M : WithBot ℤ) → a ≤ ((M + N : ℤ) : WithBot ℤ)) : a ≤ b + (N : WithBot ℤ) := by
  induction b with
  | bot =>
    induction a with
    | bot => simp
    | coe x =>
      exfalso
      have h1 := WithBot.coe_le_coe.1 (h (x - N - 1) bot_le)
      linarith
  | coe y =>
    have h1 := h y le_rfl
    rw [← WithBot.coe_add]
    exact h1

/- English proof (translation)
Establish `key : (∀ s : ℤ, (s : WithTop ℤ) ≤ c) → c = ⊤`. Introduce `hs`. Proceed by induction on `c with`. Consider the case `top => rfl`. Consider the case `coe z`.

Establish `h1` using `WithTop.coe_le_coe.1 (hs (z + 1))`. Use linear arithmetic over natural numbers and integers. Proceed by induction on `a with`. Consider the case `top`. Establish `hc : c = ⊤` using `key fun s => by`.

Proceed by induction on `b with`. Consider the case `top => simpa using h s 0 le_top le_top`. Consider the case `coe y => simpa using h (s - y) y le_top le_rfl`. Simplify using `[hc]`. Consider the case `coe x`.

Proceed by induction on `b with`. Consider the case `top`. Establish `hc : c = ⊤` using `key fun s => by simpa using h x (s - x) le_rfl le_top`. Simplify using `[hc]`. Consider the case `coe y`.

Rewrite using `[← WithTop.coe_add]`. Conclude with `h x y le_rfl le_rfl`.
-/
theorem flt_withTop_add_le {a b c : WithTop ℤ}
    (h : ∀ t u : ℤ, (t : WithTop ℤ) ≤ a → (u : WithTop ℤ) ≤ b → ((t + u : ℤ) : WithTop ℤ) ≤ c) : a + b ≤ c := by
  have key : (∀ s : ℤ, (s : WithTop ℤ) ≤ c) → c = ⊤ := by
    intro hs
    induction c with
    | top => rfl
    | coe z =>
      have h1 := WithTop.coe_le_coe.1 (hs (z + 1))
      omega
  induction a with
  | top =>
    have hc : c = ⊤ := key fun s => by
      induction b with
      | top => simpa using h s 0 le_top le_top
      | coe y => simpa using h (s - y) y le_top le_rfl
    simp [hc]
  | coe x =>
    induction b with
    | top =>
      have hc : c = ⊤ := key fun s => by simpa using h x (s - x) le_rfl le_top
      simp [hc]
    | coe y =>
      rw [← WithTop.coe_add]
      exact h x y le_rfl le_rfl

/- English proof (translation)
Establish `key : (∀ s : ℤ, c ≤ (s : WithBot ℤ)) → c = ⊥`. Introduce `hs`. Proceed by induction on `c with`. Consider the case `bot => rfl`. Consider the case `coe z`.

Establish `h1` using `WithBot.coe_le_coe.1 (hs (z - 1))`. Use linear arithmetic over natural numbers and integers. Proceed by induction on `a with`. Consider the case `bot`. Establish `hc : c = ⊥` using `key fun s => by`.

Proceed by induction on `b with`. Consider the case `bot => simpa using h s 0 bot_le bot_le`. Consider the case `coe y => simpa using h (s - y) y bot_le le_rfl`. Simplify using `[hc]`. Consider the case `coe x`.

Proceed by induction on `b with`. Consider the case `bot`. Establish `hc : c = ⊥` using `key fun s => by simpa using h x (s - x) le_rfl bot_le`. Simplify using `[hc]`. Consider the case `coe y`.

Rewrite using `[← WithBot.coe_add]`. Conclude with `h x y le_rfl le_rfl`.
-/
theorem flt_withBot_le_add {a b c : WithBot ℤ}
    (h : ∀ t u : ℤ, a ≤ (t : WithBot ℤ) → b ≤ (u : WithBot ℤ) → c ≤ ((t + u : ℤ) : WithBot ℤ)) : c ≤ a + b := by
  have key : (∀ s : ℤ, c ≤ (s : WithBot ℤ)) → c = ⊥ := by
    intro hs
    induction c with
    | bot => rfl
    | coe z =>
      have h1 := WithBot.coe_le_coe.1 (hs (z - 1))
      omega
  induction a with
  | bot =>
    have hc : c = ⊥ := key fun s => by
      induction b with
      | bot => simpa using h s 0 bot_le bot_le
      | coe y => simpa using h (s - y) y bot_le le_rfl
    simp [hc]
  | coe x =>
    induction b with
    | bot =>
      have hc : c = ⊥ := key fun s => by simpa using h x (s - x) le_rfl bot_le
      simp [hc]
    | coe y =>
      rw [← WithBot.coe_add]
      exact h x y le_rfl le_rfl

/- English proof (translation)
Establish `h1` using `flt_withTop_le (a := min (valS LL S F) (valS LL S G)) (b := valS LL S (F + G)) (N := 0) fun t ht => by`. Rewrite using `[sub_zero, flt_le_valS, _root_.map_add]`. Conclude with `AddSubgroup.add_mem _ ((flt_le_valS LL S F t).1 (ht.trans (min_le_left _ _))) ((flt_le_valS LL S G t).1 (ht.trans (min_le_right _ _)))`. Simplify using `using h1`.
-/
theorem flt_valS_add {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : min (valS LL S F) (valS LL S G) ≤ valS LL S (F + G) := by
  have h1 := flt_withTop_le (a := min (valS LL S F) (valS LL S G)) (b := valS LL S (F + G)) (N := 0)
    fun t ht => by
      rw [sub_zero, flt_le_valS, _root_.map_add]
      exact AddSubgroup.add_mem _ ((flt_le_valS LL S F t).1 (ht.trans (min_le_left _ _)))
        ((flt_le_valS LL S G t).1 (ht.trans (min_le_right _ _)))
  simpa using h1

/- English proof (translation)
Establish `h1` using `flt_withBot_le (a := lam1S LL S (F + G)) (b := max (lam1S LL S F) (lam1S LL S G)) (N := 0) fun M hM => by`. Rewrite using `[add_zero, flt_lam1S_le, _root_.map_add]`. Conclude with `AddSubgroup.add_mem _ ((flt_lam1S_le LL S F M).1 ((le_max_left _ _).trans hM)) ((flt_lam1S_le LL S G M).1 ((le_max_right _ _).trans hM))`. Simplify using `using h1`.
-/
theorem flt_lam1S_add {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : lam1S LL S (F + G) ≤ max (lam1S LL S F) (lam1S LL S G) := by
  have h1 := flt_withBot_le (a := lam1S LL S (F + G)) (b := max (lam1S LL S F) (lam1S LL S G)) (N := 0)
    fun M hM => by
      rw [add_zero, flt_lam1S_le, _root_.map_add]
      exact AddSubgroup.add_mem _ ((flt_lam1S_le LL S F M).1 ((le_max_left _ _).trans hM))
        ((flt_lam1S_le LL S G M).1 ((le_max_right _ _).trans hM))
  simpa using h1

/- English proof (translation)
Use `flt_withTop_add_le fun t u ht hu => ?_` and prove the remaining obligations. Rewrite using `[flt_le_valS, _root_.map_mul]`. Conclude with `(laurentCoeffFiltration R n _ 1).mul_mem ((flt_le_valS LL S F t).1 ht) ((flt_le_valS LL S G u).1 hu)`.
-/
theorem flt_valS_mul_ge {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : valS LL S F + valS LL S G ≤ valS LL S (F * G) := by
  refine flt_withTop_add_le fun t u ht hu => ?_
  rw [flt_le_valS, _root_.map_mul]
  exact (laurentCoeffFiltration R n _ 1).mul_mem ((flt_le_valS LL S F t).1 ht) ((flt_le_valS LL S G u).1 hu)

/- English proof (translation)
Use `flt_withBot_le_add fun t u ht hu => ?_` and prove the remaining obligations. Rewrite using `[flt_lam1S_le, _root_.map_mul]`. Establish `h1` using `(laurentCoeffFiltration R n _ (-1)).mul_mem ((flt_lam1S_le LL S F t).1 ht) ((flt_lam1S_le LL S G u).1 hu)`. Rewrite `h1` using `[← neg_add]`. Then use the resulting hypothesis.
-/
theorem flt_lam1S_mul_le {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : lam1S LL S (F * G) ≤ lam1S LL S F + lam1S LL S G := by
  refine flt_withBot_le_add fun t u ht hu => ?_
  rw [flt_lam1S_le, _root_.map_mul]
  have h1 := (laurentCoeffFiltration R n _ (-1)).mul_mem ((flt_lam1S_le LL S F t).1 ht) ((flt_lam1S_le LL S G u).1 hu)
  rwa [← neg_add] at h1

/- English proof (translation)
Simplify using `only [twistMat]`. Rewrite using `[Matrix.mul_apply]`. Use `AddSubgroup.sum_mem _ fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_diagonal]`. Establish `h1 : gL R n b x ∈ (flt_L (GLCoord R n) e).F 0`.

Simplify using `only [gL, Matrix.map_apply]`. Conclude with `flt_L_C e _`. Establish `h3 : gLinv R n x c ∈ (flt_L (GLCoord R n) e).F 0`. Simplify using `only [gLinv, Matrix.map_apply]`. Conclude with `flt_L_C e _`.

Establish `h2 : (if x = j then LaurentPolynomial.T k else 1 : GLLaurent R n) ∈ (flt_L (GLCoord R n) e).F t` using `by split_ifs`. Conclude with `(flt_L _ e).anti hk (T_mem_laurentFiltration e k)`. Conclude with `(flt_L _ e).anti h0 (flt_L _ e).one_mem`. Establish `h4` using `(flt_L _ e).mul_mem ((flt_L _ e).mul_mem h1 h2) h3`. Rewrite `h4` using `[zero_add, add_zero]`.

Conclude with `h4`.
-/
theorem flt_twistMat_mem (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k e t : ℤ) (h0 : t ≤ 0) (hk : t ≤ e * k)
    (b c : Fin n) : twistMat R n j k b c ∈ (flt_L (GLCoord R n) e).F t := by
  simp only [twistMat]
  rw [Matrix.mul_apply]
  refine AddSubgroup.sum_mem _ fun x _ => ?_
  rw [Matrix.mul_diagonal]
  have h1 : gL R n b x ∈ (flt_L (GLCoord R n) e).F 0 := by
    simp only [gL, Matrix.map_apply]
    exact flt_L_C e _
  have h3 : gLinv R n x c ∈ (flt_L (GLCoord R n) e).F 0 := by
    simp only [gLinv, Matrix.map_apply]
    exact flt_L_C e _
  have h2 : (if x = j then LaurentPolynomial.T k else 1 : GLLaurent R n) ∈ (flt_L (GLCoord R n) e).F t := by
    split_ifs
    · exact (flt_L _ e).anti hk (T_mem_laurentFiltration e k)
    · exact (flt_L _ e).anti h0 (flt_L _ e).one_mem
  have h4 := (flt_L _ e).mul_mem ((flt_L _ e).mul_mem h1 h2) h3
  rw [zero_add, add_zero] at h4
  exact h4

open Classical in

def flt_cost {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (b : Bool) : (ι × Fin n →₀ ℕ) →+ ℤ :=
  Finsupp.liftAddHom fun v => if v.1 ∈ S ∧ LL.vec v.1 = b then Nat.castAddMonoidHom ℤ else 0

open Classical in
/- English proof (translation)
Simplify using `only [flt_cost, Finsupp.liftAddHom_apply_single]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem flt_cost_single {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (b : Bool) (v : ι × Fin n) (k : ℕ) :
    flt_cost LL S b (Finsupp.single v k) = if v.1 ∈ S ∧ LL.vec v.1 = b then (k : ℤ) else 0 := by
  simp only [flt_cost, Finsupp.liftAddHom_apply_single]
  split_ifs <;> simp

/- English proof (translation)
Simplify using `only [flt_cost, vecDeg, Finsupp.liftAddHom_apply, Finsupp.sum, Nat.cast_sum]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem flt_cost_vecDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) :
    flt_cost LL S true al = (vecDeg LL S al : ℤ) := by
  simp only [flt_cost, vecDeg, Finsupp.liftAddHom_apply, Finsupp.sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Simplify using `only [flt_cost, covDeg, Finsupp.liftAddHom_apply, Finsupp.sum, Nat.cast_sum]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem flt_cost_covDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) :
    flt_cost LL S false al = (covDeg LL S al : ℤ) := by
  simp only [flt_cost, covDeg, Finsupp.liftAddHom_apply, Finsupp.sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

def flt_compat (e : ℤ) (bm : Bool) : Prop := (e = 1 ∧ bm = false) ∨ (e = -1 ∧ bm = true)

/- English proof (translation)
Establish `hmon : ∀ (w : ι × Fin n) (a : GLLaurent R n) (s : ℤ), a ∈ (flt_L (GLCoord R n) e).F s → C a * X w ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F s`. Introduce `w a s ha`. Rewrite using `[MvPolynomial.C_mul_X_eq_monomial]`. Conclude with `flt_monomial_mem (by rw [AddMonoidHom.zero_apply, sub_zero]; exact ha)`. Simplify using `only [twistSub, eval₂Hom_X', AddMonoidHom.neg_apply, flt_cost_single]`.

Distinguish the cases in `hS : v.1 ∈ S`. Rewrite using `[if_pos hS]`. Consider the cases of `hv : LL.vec v.1`. Rewrite using `[if_neg Bool.false_ne_true]`. Use `AddSubgroup.sum_mem _ fun b _ => hmon _ _ _ (flt_twistMat_mem R n j (-1) e _ ?_ ?_ _ _)` and prove the remaining obligations.

Apply the tactic sequence `all_goals rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hS]`. Rewrite using `[if_pos rfl]`. Use `AddSubgroup.sum_mem _ fun b _ => hmon _ _ _ (flt_twistMat_mem R n j 1 e _ ?_ ?_ _ _)` and prove the remaining obligations. Apply the tactic sequence `all_goals rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hS]`. Rewrite using `[if_neg hS, if_neg (fun h' => hS h'.1), neg_zero]`.

Simplify using `using hmon v 1 0 (flt_L _ e).one_mem`.
-/
theorem flt_twistX_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) (v : ι × Fin n) :
    twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) ∈
      (laurentCoeffFiltration R n (ι × Fin n) e).F ((-flt_cost LL S bm) (Finsupp.single v 1)) := by
  have hmon : ∀ (w : ι × Fin n) (a : GLLaurent R n) (s : ℤ), a ∈ (flt_L (GLCoord R n) e).F s →
      C a * X w ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F s := by
    intro w a s ha
    rw [MvPolynomial.C_mul_X_eq_monomial]
    exact flt_monomial_mem (by rw [AddMonoidHom.zero_apply, sub_zero]; exact ha)
  simp only [twistSub, eval₂Hom_X', AddMonoidHom.neg_apply, flt_cost_single]
  by_cases hS : v.1 ∈ S
  · rw [if_pos hS]
    cases hv : LL.vec v.1
    · rw [if_neg Bool.false_ne_true]
      refine AddSubgroup.sum_mem _ fun b _ => hmon _ _ _ (flt_twistMat_mem R n j (-1) e _ ?_ ?_ _ _)
      all_goals rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hS]
    · rw [if_pos rfl]
      refine AddSubgroup.sum_mem _ fun b _ => hmon _ _ _ (flt_twistMat_mem R n j 1 e _ ?_ ?_ _ _)
      all_goals rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hS]
  · rw [if_neg hS, if_neg (fun h' => hS h'.1), neg_zero]
    simpa using hmon v 1 0 (flt_L _ e).one_mem

/- English proof (translation)
Establish `h1` using `flt_hom_monomial _ (twistSub (R := R) LL S j) (-flt_cost LL S bm) (flt_twistX_mem LL S j h) al`. Rewrite `h1` using `[AddMonoidHom.neg_apply]`. Then use the resulting hypothesis.
-/
theorem flt_twist_monomial_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) (al : ι × Fin n →₀ ℕ) :
    twistSub LL S j (monomial al (1 : R)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F (-flt_cost LL S bm al) := by
  have h1 := flt_hom_monomial _ (twistSub (R := R) LL S j) (-flt_cost LL S bm) (flt_twistX_mem LL S j h) al
  rwa [AddMonoidHom.neg_apply] at h1

/- English proof (translation)
Establish `key : ∀ a b, (gL R n * gLinv R n) a b = LaurentPolynomial.C (IsLocalization.Away.invSelf (genMat R n).det * algebraMap _ (GLCoord R n) ((genMat R n * (genMat R n).adjugate) a b))`. Introduce `a b`. Simplify using `only [gL, gLinv, Matrix.mul_apply, Matrix.map_apply, ← _root_.map_mul, _root_.map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[_root_.map_mul]`. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `a b`. Rewrite using `[key, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]`. Use `split_ifs`.

Rewrite using `[smul_eq_mul, mul_one, mul_comm, IsLocalization.Away.mul_invSelf, _root_.map_one]`. Rewrite using `[smul_zero, _root_.map_zero, mul_zero, _root_.map_zero]`.
-/
theorem flt_gL_mul_gLinv (R : Type*) [CommRing R] (n : ℕ) : gL R n * gLinv R n = 1 := by
  have key : ∀ a b, (gL R n * gLinv R n) a b = LaurentPolynomial.C
      (IsLocalization.Away.invSelf (genMat R n).det *
        algebraMap _ (GLCoord R n) ((genMat R n * (genMat R n).adjugate) a b)) := by
    intro a b
    simp only [gL, gLinv, Matrix.mul_apply, Matrix.map_apply, ← _root_.map_mul, _root_.map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [_root_.map_mul]
    ring
  ext a b
  rw [key, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [smul_eq_mul, mul_one, mul_comm, IsLocalization.Away.mul_invSelf, _root_.map_one]
  · rw [smul_zero, _root_.map_zero, mul_zero, _root_.map_zero]

/- English proof (translation)
Establish `key : ∀ a b, (gLinv R n * gL R n) a b = LaurentPolynomial.C (IsLocalization.Away.invSelf (genMat R n).det * algebraMap _ (GLCoord R n) (((genMat R n).adjugate * genMat R n) a b))`. Introduce `a b`. Simplify using `only [gL, gLinv, Matrix.mul_apply, Matrix.map_apply, ← _root_.map_mul, _root_.map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[_root_.map_mul]`. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `a b`. Rewrite using `[key, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]`. Use `split_ifs`.

Rewrite using `[smul_eq_mul, mul_one, mul_comm, IsLocalization.Away.mul_invSelf, _root_.map_one]`. Rewrite using `[smul_zero, _root_.map_zero, mul_zero, _root_.map_zero]`.
-/
theorem flt_gLinv_mul_gL (R : Type*) [CommRing R] (n : ℕ) : gLinv R n * gL R n = 1 := by
  have key : ∀ a b, (gLinv R n * gL R n) a b = LaurentPolynomial.C
      (IsLocalization.Away.invSelf (genMat R n).det *
        algebraMap _ (GLCoord R n) (((genMat R n).adjugate * genMat R n) a b)) := by
    intro a b
    simp only [gL, gLinv, Matrix.mul_apply, Matrix.map_apply, ← _root_.map_mul, _root_.map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [_root_.map_mul]
    ring
  ext a b
  rw [key, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [smul_eq_mul, mul_one, mul_comm, IsLocalization.Away.mul_invSelf, _root_.map_one]
  · rw [smul_zero, _root_.map_zero, mul_zero, _root_.map_zero]

/- English proof (translation)
Establish `hD : (Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T k else 1) * Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T (-k) else 1) : Matrix (Fin n) (Fin n) (GLLaurent R n)) = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Use `split_ifs`.

Rewrite using `[← LaurentPolynomial.T_add]`. Simplify using the standard rewrite rules. Rewrite using `[mul_one]`. Simplify using `only [twistMat, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (gLinv R n) (gL R n), flt_gLinv_mul_gL, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), hD, Matrix.one_mul, flt_gL_mul_gLinv]`.
-/
theorem flt_twistMat_mul (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k : ℤ) :
    twistMat R n j k * twistMat R n j (-k) = 1 := by
  have hD : (Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T k else 1) *
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T (-k) else 1) :
        Matrix (Fin n) (Fin n) (GLLaurent R n)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs
    · rw [← LaurentPolynomial.T_add]
      simp
    · rw [mul_one]
  simp only [twistMat, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (gLinv R n) (gL R n), flt_gLinv_mul_gL, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), hD, Matrix.one_mul, flt_gL_mul_gLinv]

def flt_tay (R : Type*) [CommRing R] (σ : Type*) : MvPolynomial σ R →+* MvPolynomial σ (MvPolynomial σ R) :=
  eval₂Hom (C.comp C) (fun v => C (X v) + X v)

def flt_g (R : Type*) [CommRing R] {σ : Type*} (m be : σ →₀ ℕ) : MvPolynomial σ R :=
  monomial (m - be) (((be.prod fun k j => (m k).choose j : ℕ)) : R)

open Classical in
/- English proof (translation)
Simplify using `only [flt_g]`. Establish `hX : ∀ (s : σ →₀ ℕ) (c : R), monomial s c * X a = monomial (s + Finsupp.single a 1) c` using `fun s c => by`. Rewrite using `[← pow_one (X a), MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, mul_one]`. Rewrite using `[hX]`. Distinguish the cases in `h : a ∈ be.support`.

Rewrite using `[if_pos h]`. Establish `hba : be a ≠ 0` using `Finsupp.mem_support_iff.1 h`. Take `⟨b, hb⟩ : ∃ b, be a = b + 1` from `⟨be a - 1, by omega⟩`. Take `⟨Q, hQ⟩ : ∃ Q, Q = ∏ k ∈ be.support.erase a, (m k).choose (be k)` from `⟨_, rfl⟩`. Establish `hP0 : (be.prod fun k j => ((m + Finsupp.single a 1 : σ →₀ ℕ) k).choose j) = (m a + 1).choose (be a) * Q`.

Rewrite using `[hQ]`. Simplify using `only [Finsupp.prod]`. Rewrite using `[← Finset.mul_prod_erase _ _ h]`. Use `congr 1`. Simplify using the standard rewrite rules.

Conclude with `Finset.prod_congr rfl fun k hk => by`. Establish `hka : a ≠ k` using `Ne.symm (Finset.ne_of_mem_erase hk)`. Simplify using `[Finsupp.single_apply, hka]`. Establish `hP1 : (be.prod fun k j => (m k).choose j) = (m a).choose (be a) * Q`. Rewrite using `[hQ]`.

Simplify using `only [Finsupp.prod]`. Rewrite using `[← Finset.mul_prod_erase _ _ h]`. Establish `hsub : (be - Finsupp.single a 1).support ⊆ be.support` using `fun k hk => Finsupp.mem_support_iff.2 fun h0 => (Finsupp.mem_support_iff.1 hk) (by simp [h0])`. Establish `hP2 : ((be - Finsupp.single a 1).prod fun k j => (m k).choose j) = (m a).choose (be a - 1) * Q`. Rewrite using `[hQ, Finsupp.prod_of_support_subset _ hsub _ (fun _ _ => Nat.choose_zero_right _), ← Finset.mul_prod_erase _ _ h]`.

Use `congr 1`. Simplify using the standard rewrite rules. Conclude with `Finset.prod_congr rfl fun k hk => by`. Establish `hka : a ≠ k` using `Ne.symm (Finset.ne_of_mem_erase hk)`. Simplify using `[Finsupp.single_apply, hka]`.

Establish `hle : Q ≠ 0 → ∀ k, k ≠ a → be k ≤ m k`. Introduce `hQ0 k hk`. Rewrite `hQ0` using `[hQ]`. Distinguish the cases in `hks : k ∈ be.support`. Establish `h1` using `(Finset.prod_ne_zero_iff.1 hQ0) k (Finset.mem_erase.2 ⟨hk, hks⟩)`.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Conclude with `h1 (Nat.choose_eq_zero_of_lt hlt)`. Establish `h0 : be k = 0`. Assume the negation of the conclusion as `h0`.

Conclude with `hks (Finsupp.mem_support_iff.2 h0)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hP0, hP1, hP2, hb, Nat.choose_succ_succ, Nat.add_sub_cancel]`. Distinguish the cases in `h1 : (m a).choose (b + 1) * Q = 0`. Rewrite using `[h1, Nat.cast_zero, MvPolynomial.monomial_zero, zero_add]`.

Distinguish the cases in `h2 : (m a).choose b * Q = 0`. Rewrite using `[add_mul, h1, h2]`. Simplify using the standard rewrite rules. Establish `hx : m + Finsupp.single a 1 - be = m - (be - Finsupp.single a 1)` using `Finsupp.ext fun k => by`. Simplify using `only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]`.

Use `split_ifs with hka`. Substitute `hka` using the available equality. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Establish `hc : ((m a).choose b + (m a).choose (b + 1)) * Q = (m a).choose b * Q`.

Rewrite using `[add_mul, h1, add_zero]`. Rewrite using `[hx, hc]`. Establish `hQ0 : Q ≠ 0` using `right_ne_zero_of_mul h1`. Establish `hab : b + 1 ≤ m a`. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Conclude with `h1 (by rw [Nat.choose_eq_zero_of_lt hlt, zero_mul])`. Establish `hx1 : m + Finsupp.single a 1 - be = m - be + Finsupp.single a 1` using `Finsupp.ext fun k => by`. Simplify using `only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]`. Use `split_ifs with hka`.

Substitute `hka` using the available equality. Use linear arithmetic over natural numbers and integers. Establish `h3` using `hle hQ0 k (Ne.symm hka)`. Use linear arithmetic over natural numbers and integers. Establish `hx2 : m - (be - Finsupp.single a 1) = m - be + Finsupp.single a 1` using `Finsupp.ext fun k => by`.

Simplify using `only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]`. Use `split_ifs with hka`. Substitute `hka` using the available equality. Use linear arithmetic over natural numbers and integers. Establish `h3` using `hle hQ0 k (Ne.symm hka)`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hx1, hx2, ← _root_.map_add (monomial (m - be + Finsupp.single a 1)), ← Nat.cast_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h, add_zero]`.

Establish `hba : be a = 0`. Assume the negation of the conclusion as `h0`. Conclude with `h (Finsupp.mem_support_iff.2 h0)`. Establish `hx : m + Finsupp.single a 1 - be = m - be + Finsupp.single a 1` using `Finsupp.ext fun k => by`. Simplify using `only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]`.

Use `split_ifs with hka`. Substitute `hka` using the available equality. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Establish `hp : (be.prod fun k j => ((m + Finsupp.single a 1 : σ →₀ ℕ) k).choose j) = be.prod fun k j => (m k).choose j`.

Simplify using `only [Finsupp.prod]`. Conclude with `Finset.prod_congr rfl fun k hk => by`. Establish `hka : a ≠ k` using `fun h' => h (by rw [h']; exact hk)`. Simplify using `[Finsupp.single_apply, hka]`. Rewrite using `[hx, hp]`.
-/
theorem flt_g_pascal (R : Type*) [CommRing R] {σ : Type*} (m be : σ →₀ ℕ) (a : σ) :
    flt_g R (m + Finsupp.single a 1) be =
      flt_g R m be * X a + (if a ∈ be.support then flt_g R m (be - Finsupp.single a 1) else 0) := by
  classical
  simp only [flt_g]
  have hX : ∀ (s : σ →₀ ℕ) (c : R), monomial s c * X a = monomial (s + Finsupp.single a 1) c := fun s c => by
    rw [← pow_one (X a), MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, mul_one]
  rw [hX]
  by_cases h : a ∈ be.support
  · rw [if_pos h]
    have hba : be a ≠ 0 := Finsupp.mem_support_iff.1 h
    obtain ⟨b, hb⟩ : ∃ b, be a = b + 1 := ⟨be a - 1, by omega⟩
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∏ k ∈ be.support.erase a, (m k).choose (be k) := ⟨_, rfl⟩
    have hP0 : (be.prod fun k j => ((m + Finsupp.single a 1 : σ →₀ ℕ) k).choose j) = (m a + 1).choose (be a) * Q := by
      rw [hQ]
      simp only [Finsupp.prod]
      rw [← Finset.mul_prod_erase _ _ h]
      congr 1
      · simp
      · exact Finset.prod_congr rfl fun k hk => by
          have hka : a ≠ k := Ne.symm (Finset.ne_of_mem_erase hk)
          simp [Finsupp.single_apply, hka]
    have hP1 : (be.prod fun k j => (m k).choose j) = (m a).choose (be a) * Q := by
      rw [hQ]
      simp only [Finsupp.prod]
      rw [← Finset.mul_prod_erase _ _ h]
    have hsub : (be - Finsupp.single a 1).support ⊆ be.support := fun k hk =>
      Finsupp.mem_support_iff.2 fun h0 => (Finsupp.mem_support_iff.1 hk) (by simp [h0])
    have hP2 : ((be - Finsupp.single a 1).prod fun k j => (m k).choose j) = (m a).choose (be a - 1) * Q := by
      rw [hQ, Finsupp.prod_of_support_subset _ hsub _ (fun _ _ => Nat.choose_zero_right _),
        ← Finset.mul_prod_erase _ _ h]
      congr 1
      · simp
      · exact Finset.prod_congr rfl fun k hk => by
          have hka : a ≠ k := Ne.symm (Finset.ne_of_mem_erase hk)
          simp [Finsupp.single_apply, hka]
    have hle : Q ≠ 0 → ∀ k, k ≠ a → be k ≤ m k := by
      intro hQ0 k hk
      rw [hQ] at hQ0
      by_cases hks : k ∈ be.support
      · have h1 := (Finset.prod_ne_zero_iff.1 hQ0) k (Finset.mem_erase.2 ⟨hk, hks⟩)
        by_contra hlt
        push_neg at hlt
        exact h1 (Nat.choose_eq_zero_of_lt hlt)
      · have h0 : be k = 0 := by
          by_contra h0
          exact hks (Finsupp.mem_support_iff.2 h0)
        omega
    rw [hP0, hP1, hP2, hb, Nat.choose_succ_succ, Nat.add_sub_cancel]
    by_cases h1 : (m a).choose (b + 1) * Q = 0
    · rw [h1, Nat.cast_zero, MvPolynomial.monomial_zero, zero_add]
      by_cases h2 : (m a).choose b * Q = 0
      · rw [add_mul, h1, h2]
        simp
      · have hx : m + Finsupp.single a 1 - be = m - (be - Finsupp.single a 1) := Finsupp.ext fun k => by
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
          split_ifs with hka
          · subst hka
            omega
          · omega
        have hc : ((m a).choose b + (m a).choose (b + 1)) * Q = (m a).choose b * Q := by
          rw [add_mul, h1, add_zero]
        rw [hx, hc]
    · have hQ0 : Q ≠ 0 := right_ne_zero_of_mul h1
      have hab : b + 1 ≤ m a := by
        by_contra hlt
        push_neg at hlt
        exact h1 (by rw [Nat.choose_eq_zero_of_lt hlt, zero_mul])
      have hx1 : m + Finsupp.single a 1 - be = m - be + Finsupp.single a 1 := Finsupp.ext fun k => by
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
        split_ifs with hka
        · subst hka
          omega
        · have h3 := hle hQ0 k (Ne.symm hka)
          omega
      have hx2 : m - (be - Finsupp.single a 1) = m - be + Finsupp.single a 1 := Finsupp.ext fun k => by
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
        split_ifs with hka
        · subst hka
          omega
        · have h3 := hle hQ0 k (Ne.symm hka)
          omega
      rw [hx1, hx2, ← _root_.map_add (monomial (m - be + Finsupp.single a 1)), ← Nat.cast_add]
      congr 2
      ring
  · rw [if_neg h, add_zero]
    have hba : be a = 0 := by
      by_contra h0
      exact h (Finsupp.mem_support_iff.2 h0)
    have hx : m + Finsupp.single a 1 - be = m - be + Finsupp.single a 1 := Finsupp.ext fun k => by
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with hka
      · subst hka
        omega
      · omega
    have hp : (be.prod fun k j => ((m + Finsupp.single a 1 : σ →₀ ℕ) k).choose j) = be.prod fun k j => (m k).choose j := by
      simp only [Finsupp.prod]
      exact Finset.prod_congr rfl fun k hk => by
        have hka : a ≠ k := fun h' => h (by rw [h']; exact hk)
        simp [Finsupp.single_apply, hka]
    rw [hx, hp]

/- English proof (translation)
It suffices to establish `H : ∀ d : ℕ, ∀ m : σ →₀ ℕ, (m.sum fun _ e => e) = d → ∀ be, coeff be (flt_tay R σ (monomial m 1)) = flt_g R m be from H _ m rfl`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `m hm be`.

Establish `hm0 : m = 0`. Use extensionality with `k`. Simplify using `only [Finsupp.coe_zero, Pi.zero_apply]`. Assume the negation of the conclusion as `hk`. Establish `h1 : m k ≤ m.sum fun _ e => e`.

Simplify using `only [Finsupp.sum]`. Conclude with `Finset.single_le_sum (f := fun k => m k) (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.2 hk)`. Use linear arithmetic over natural numbers and integers. Substitute `hm0` using the available equality. Rewrite using `[← MvPolynomial.C_apply, _root_.map_one, _root_.map_one, MvPolynomial.coeff_one, flt_g, zero_tsub]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `[← MvPolynomial.C_apply]`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, be k ≠ 0 := by`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Conclude with `h (by ext k; simp [hne k])`. Establish `h0 : (be.prod fun k j => ((0 : σ →₀ ℕ) k).choose j) = 0` using `Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hk) (by simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)])`. Rewrite using `[h0, Nat.cast_zero, MvPolynomial.monomial_zero]`. Consider the case `succ d ih`.

Introduce `m hm be`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, m a ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `h0 : m = 0` using `by ext k; simp [hne k]`.

Substitute `h0` using the available equality. Simplify using `at hm`. Establish `hm' : m - Finsupp.single a 1 + Finsupp.single a 1 = m`. Use extensionality with `k`. Simplify using `only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Establish `hsum : ((m - Finsupp.single a 1).sum fun _ e => e) = d`.

Establish `h1` using `hm`. Rewrite `h1` using `[← hm', Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]`. Use linear arithmetic over natural numbers and integers. Establish `e1 : monomial (m - Finsupp.single a 1 + Finsupp.single a 1) (1 : R) = monomial (m - Finsupp.single a 1) 1 * X a`. Rewrite using `[← pow_one (X a), MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]`.

Establish `e2 : flt_tay R σ (X a) = C (X a) + X a`. Simplify using `only [flt_tay, eval₂Hom_X']`. Rewrite using `[← hm', e1, _root_.map_mul, flt_g_pascal, e2, mul_add, MvPolynomial.coeff_add, mul_comm _ (C (X a)), MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X', ih _ hsum be, ih _ hsum (be - Finsupp.single a 1)]`. Apply the tactic sequence `all_goals (first | ring | (split_ifs <;> ring))`.
-/
theorem flt_tay_monomial (R : Type*) [CommRing R] {σ : Type*} (m : σ →₀ ℕ) :
    ∀ be, coeff be (flt_tay R σ (monomial m 1)) = flt_g R m be := by
  classical
  suffices H : ∀ d : ℕ, ∀ m : σ →₀ ℕ, (m.sum fun _ e => e) = d →
      ∀ be, coeff be (flt_tay R σ (monomial m 1)) = flt_g R m be from H _ m rfl
  intro d
  induction d with
  | zero =>
    intro m hm be
    have hm0 : m = 0 := by
      ext k
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      by_contra hk
      have h1 : m k ≤ m.sum fun _ e => e := by
        simp only [Finsupp.sum]
        exact Finset.single_le_sum (f := fun k => m k) (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.2 hk)
      omega
    subst hm0
    rw [← MvPolynomial.C_apply, _root_.map_one, _root_.map_one, MvPolynomial.coeff_one, flt_g, zero_tsub]
    split_ifs with h
    · subst h
      simp [← MvPolynomial.C_apply]
    · obtain ⟨k, hk⟩ : ∃ k, be k ≠ 0 := by
        by_contra hne
        push_neg at hne
        exact h (by ext k; simp [hne k])
      have h0 : (be.prod fun k j => ((0 : σ →₀ ℕ) k).choose j) = 0 :=
        Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hk)
          (by simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)])
      rw [h0, Nat.cast_zero, MvPolynomial.monomial_zero]
  | succ d ih =>
    intro m hm be
    obtain ⟨a, ha⟩ : ∃ a, m a ≠ 0 := by
      by_contra hne
      push_neg at hne
      have h0 : m = 0 := by ext k; simp [hne k]
      subst h0
      simp at hm
    have hm' : m - Finsupp.single a 1 + Finsupp.single a 1 = m := by
      ext k
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; omega
      · omega
    have hsum : ((m - Finsupp.single a 1).sum fun _ e => e) = d := by
      have h1 := hm
      rw [← hm', Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl] at h1
      omega
    have e1 : monomial (m - Finsupp.single a 1 + Finsupp.single a 1) (1 : R) =
        monomial (m - Finsupp.single a 1) 1 * X a := by
      rw [← pow_one (X a), MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
    have e2 : flt_tay R σ (X a) = C (X a) + X a := by
      simp only [flt_tay, eval₂Hom_X']
    rw [← hm', e1, _root_.map_mul, flt_g_pascal, e2, mul_add, MvPolynomial.coeff_add,
      mul_comm _ (C (X a)), MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X', ih _ hsum be, ih _ hsum (be - Finsupp.single a 1)]
    all_goals (first | ring | (split_ifs <;> ring))

/- English proof (translation)
Use `conv_lhs => rw [F.as_sum]`. Rewrite using `[_root_.map_sum, MvPolynomial.coeff_sum]`. Simplify using `only [divDer]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `e1 : monomial m (coeff m F) = C (coeff m F) * monomial m 1`.

Rewrite using `[MvPolynomial.C_mul_monomial, mul_one]`. Establish `e2 : flt_tay R σ (C (coeff m F)) = C (C (coeff m F))`. Simplify using `only [flt_tay, eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[e1, _root_.map_mul, e2, MvPolynomial.coeff_C_mul, flt_tay_monomial, flt_g, MvPolynomial.C_mul_monomial]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Establish `hex : ∃ k, m k < be k`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Conclude with `h fun k => hne k`.

Take `⟨k, hk⟩` from `hex`. Establish `h0 : (be.prod fun k j => (m k).choose j) = 0` using `Finset.prod_eq_zero (Finsupp.mem_support_iff.2 (by omega)) (Nat.choose_eq_zero_of_lt hk)`. Rewrite using `[h0, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]`.
-/
theorem flt_tay_coeff (R : Type*) [CommRing R] {σ : Type*} (F : MvPolynomial σ R) (be : σ →₀ ℕ) :
    coeff be (flt_tay R σ F) = divDer be F := by
  conv_lhs => rw [F.as_sum]
  rw [_root_.map_sum, MvPolynomial.coeff_sum]
  simp only [divDer]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e1 : monomial m (coeff m F) = C (coeff m F) * monomial m 1 := by
    rw [MvPolynomial.C_mul_monomial, mul_one]
  have e2 : flt_tay R σ (C (coeff m F)) = C (C (coeff m F)) := by
    simp only [flt_tay, eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]
  rw [e1, _root_.map_mul, e2, MvPolynomial.coeff_C_mul, flt_tay_monomial, flt_g, MvPolynomial.C_mul_monomial]
  split_ifs with h
  · rfl
  · have hex : ∃ k, m k < be k := by
      by_contra hne
      push_neg at hne
      exact h fun k => hne k
    obtain ⟨k, hk⟩ := hex
    have h0 : (be.prod fun k j => (m k).choose j) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.2 (by omega)) (Nat.choose_eq_zero_of_lt hk)
    rw [h0, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]

open Classical in

def flt_Th {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) :
    MvPolynomial (ι × Fin n) (GLLaurent R n) →+*
      MvPolynomial (ι × Fin n) (MvPolynomial (ι × Fin n) (GLLaurent R n)) :=
  eval₂Hom (C.comp C) fun w => C (X w) +
    (if w.1 ∈ S then
      (if LL.vec w.1 then ∑ c : Fin n, C (C (twistMat R n j (-1) c w.2)) * X (w.1, c)
       else ∑ c : Fin n, C (C (twistMat R n j 1 w.2 c)) * X (w.1, c))
     else X w)

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.mul_sum, Finset.sum_mul, _root_.map_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring`. Use `_ = ∑ c, C (C ((Q * P) c d)) * Y c := by`.

Simplify using `only [Matrix.mul_apply, _root_.map_sum]`. Use `_ = Y d := by`. Rewrite using `[h]`. Simplify using `[Matrix.one_apply]`.
-/
theorem sum_C_C_mul_sum_of_mul_eq_one {B : Type*} [CommRing B] {σ' σ'' : Type*} {n : ℕ} (P Q : Matrix (Fin n) (Fin n) B)
    (h : Q * P = 1) (Y : Fin n → MvPolynomial σ' (MvPolynomial σ'' B)) (d : Fin n) :
    ∑ b, C (C (P b d)) * ∑ c, C (C (Q c b)) * Y c = Y d := by
  calc ∑ b, C (C (P b d)) * ∑ c, C (C (Q c b)) * Y c
      = ∑ c, (∑ b, C (C (Q c b * P b d))) * Y c := by
        simp only [Finset.mul_sum, Finset.sum_mul, _root_.map_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ c, C (C ((Q * P) c d)) * Y c := by
        simp only [Matrix.mul_apply, _root_.map_sum]
    _ = Y d := by
        rw [h]
        simp [Matrix.one_apply]

/- English proof (translation)
Establish `h1 : twistMat R n j (-1) * twistMat R n j 1 = 1`. Simplify using `using flt_twistMat_mul R n j (-1)`. Establish `h2 : (twistMat R n j 1).transpose * (twistMat R n j (-1)).transpose = 1`. Rewrite using `[← Matrix.transpose_mul, h1, Matrix.transpose_one]`. Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply, flt_tay, flt_Th, twistSub, eval₂Hom_C, RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C]`. Simplify using `only [RingHom.comp_apply, flt_tay, eval₂Hom_X', _root_.map_add, MvPolynomial.map_C, MvPolynomial.map_X]`. Distinguish the cases in `hS : v.1 ∈ S`. Consider the cases of `hv : LL.vec v.1`. Establish `hT : twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) = ∑ b : Fin n, C (twistMat R n j (-1) v.2 b) * X (v.1, b)`.

Simplify using `only [twistSub, eval₂Hom_X', hS, hv, Bool.false_eq_true, ↓reduceIte]`. Establish `hTh : ∀ b : Fin n, flt_Th LL S j (C (twistMat R n j (-1) v.2 b) * X (v.1, b)) = C (C (twistMat R n j (-1) v.2 b)) * C (X (v.1, b)) + C (C (twistMat R n j (-1) v.2 b)) * ∑ c : Fin n, C (C (twistMat R n j 1 b c)) * X (v.1, c)`. Introduce `b`. Simplify using `only [flt_Th, _root_.map_mul, eval₂Hom_C, eval₂Hom_X', RingHom.coe_comp, Function.comp_apply, hS, hv, Bool.false_eq_true, ↓reduceIte, mul_add]`. Establish `hY` using `sum_C_C_mul_sum_of_mul_eq_one (twistMat R n j (-1)).transpose (twistMat R n j 1).transpose h2 (fun c => (X (v.1, c) : MvPolynomial (ι × Fin n) (MvPolynomial (ι × Fin n) (GLLaurent R n)))) v.2`.

Simplify using `only [Matrix.transpose_apply] at hY`. Rewrite using `[hT]`. Simplify using `only [_root_.map_sum, hTh, Finset.sum_add_distrib]`. Rewrite using `[hY]`. Simplify using `only [_root_.map_mul, Prod.mk.eta]`.

Establish `hT : twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) = ∑ b : Fin n, C (twistMat R n j 1 b v.2) * X (v.1, b)`. Simplify using `only [twistSub, eval₂Hom_X', hS, hv, ↓reduceIte]`. Establish `hTh : ∀ b : Fin n, flt_Th LL S j (C (twistMat R n j 1 b v.2) * X (v.1, b)) = C (C (twistMat R n j 1 b v.2)) * C (X (v.1, b)) + C (C (twistMat R n j 1 b v.2)) * ∑ c : Fin n, C (C (twistMat R n j (-1) c b)) * X (v.1, c)`. Introduce `b`. Simplify using `only [flt_Th, _root_.map_mul, eval₂Hom_C, eval₂Hom_X', RingHom.coe_comp, Function.comp_apply, hS, hv, ↓reduceIte, mul_add]`.

Establish `hY` using `sum_C_C_mul_sum_of_mul_eq_one (twistMat R n j 1) (twistMat R n j (-1)) h1 (fun c => (X (v.1, c) : MvPolynomial (ι × Fin n) (MvPolynomial (ι × Fin n) (GLLaurent R n)))) v.2`. Apply the tactic sequence `try dsimp only at hY`. Rewrite using `[hT]`. Simplify using `only [_root_.map_sum, hTh, Finset.sum_add_distrib]`. Rewrite using `[hY]`.

Simplify using `only [_root_.map_mul, Prod.mk.eta]`. Establish `hT : twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) = X v`. Simplify using `only [twistSub, eval₂Hom_X', hS, ↓reduceIte]`. Rewrite using `[hT]`. Simplify using `only [flt_Th, eval₂Hom_X', hS, ↓reduceIte]`.
-/
theorem flt_Th_twist {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) :
    (MvPolynomial.map (twistSub (R := R) LL S j)).comp (flt_tay R (ι × Fin n)) =
      (flt_Th LL S j).comp (twistSub (R := R) LL S j) := by
  have h1 : twistMat R n j (-1) * twistMat R n j 1 = 1 := by
    simpa using flt_twistMat_mul R n j (-1)
  have h2 : (twistMat R n j 1).transpose * (twistMat R n j (-1)).transpose = 1 := by
    rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
  · simp only [RingHom.comp_apply, flt_tay, flt_Th, twistSub, eval₂Hom_C, RingHom.coe_comp,
      Function.comp_apply, MvPolynomial.map_C]
  · simp only [RingHom.comp_apply, flt_tay, eval₂Hom_X', _root_.map_add, MvPolynomial.map_C, MvPolynomial.map_X]
    by_cases hS : v.1 ∈ S
    · cases hv : LL.vec v.1
      · have hT : twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) =
            ∑ b : Fin n, C (twistMat R n j (-1) v.2 b) * X (v.1, b) := by
          simp only [twistSub, eval₂Hom_X', hS, hv, Bool.false_eq_true, ↓reduceIte]
        have hTh : ∀ b : Fin n, flt_Th LL S j (C (twistMat R n j (-1) v.2 b) * X (v.1, b)) =
            C (C (twistMat R n j (-1) v.2 b)) * C (X (v.1, b)) +
            C (C (twistMat R n j (-1) v.2 b)) * ∑ c : Fin n, C (C (twistMat R n j 1 b c)) * X (v.1, c) := by
          intro b
          simp only [flt_Th, _root_.map_mul, eval₂Hom_C, eval₂Hom_X', RingHom.coe_comp, Function.comp_apply,
            hS, hv, Bool.false_eq_true, ↓reduceIte, mul_add]
        have hY := sum_C_C_mul_sum_of_mul_eq_one (twistMat R n j (-1)).transpose (twistMat R n j 1).transpose h2
          (fun c => (X (v.1, c) : MvPolynomial (ι × Fin n) (MvPolynomial (ι × Fin n) (GLLaurent R n)))) v.2
        simp only [Matrix.transpose_apply] at hY
        rw [hT]
        simp only [_root_.map_sum, hTh, Finset.sum_add_distrib]
        rw [hY]
        simp only [_root_.map_mul, Prod.mk.eta]
      · have hT : twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) =
            ∑ b : Fin n, C (twistMat R n j 1 b v.2) * X (v.1, b) := by
          simp only [twistSub, eval₂Hom_X', hS, hv, ↓reduceIte]
        have hTh : ∀ b : Fin n, flt_Th LL S j (C (twistMat R n j 1 b v.2) * X (v.1, b)) =
            C (C (twistMat R n j 1 b v.2)) * C (X (v.1, b)) +
            C (C (twistMat R n j 1 b v.2)) * ∑ c : Fin n, C (C (twistMat R n j (-1) c b)) * X (v.1, c) := by
          intro b
          simp only [flt_Th, _root_.map_mul, eval₂Hom_C, eval₂Hom_X', RingHom.coe_comp, Function.comp_apply,
            hS, hv, ↓reduceIte, mul_add]
        have hY := sum_C_C_mul_sum_of_mul_eq_one (twistMat R n j 1) (twistMat R n j (-1)) h1
          (fun c => (X (v.1, c) : MvPolynomial (ι × Fin n) (MvPolynomial (ι × Fin n) (GLLaurent R n)))) v.2
        try dsimp only at hY
        rw [hT]
        simp only [_root_.map_sum, hTh, Finset.sum_add_distrib]
        rw [hY]
        simp only [_root_.map_mul, Prod.mk.eta]
    · have hT : twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) = X v := by
        simp only [twistSub, eval₂Hom_X', hS, ↓reduceIte]
      rw [hT]
      simp only [flt_Th, eval₂Hom_X', hS, ↓reduceIte]

/- English proof (translation)
Establish `hmon2 : ∀ (u : ι × Fin n) (a : GLLaurent R n), a ∈ (flt_L (GLCoord R n) e).F (0 - flt_cost LL S (!bm) (Finsupp.single u 1)) → C (C a) * X u ∈ (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).F 0`. Introduce `u a ha`. Rewrite using `[MvPolynomial.C_mul_X_eq_monomial]`. Conclude with `flt_monomial_mem (flt_C_mem ha)`. Use `flt_hom_mem (flt_L (GLCoord R n) e) _ (flt_Th LL S j) 0 (fun s b hb => ?_) (fun w => ?_) hP` and prove the remaining obligations.

Establish `e1 : flt_Th LL S j (C b) = C (C b)`. Simplify using `only [flt_Th, eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[e1]`. Conclude with `flt_C_mem (flt_C_mem hb)`. Rewrite using `[AddMonoidHom.zero_apply]`.

Simplify using `only [flt_Th, eval₂Hom_X']`. Establish `hX1 : (X w : MvPolynomial (ι × Fin n) (GLLaurent R n)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F 0`. Establish `h1` using `flt_monomial_mem (Fl := flt_L (GLCoord R n) e) (wt := 0) (t := 0) (m := Finsupp.single w 1) (a := 1) (by simpa using (flt_L (GLCoord R n) e).one_mem)`. Rewrite `h1` using `[← MvPolynomial.C_mul_X_eq_monomial, _root_.map_one, one_mul]`. Then use the resulting hypothesis. Use `AddSubgroup.add_mem _ (flt_C_mem hX1) ?_` and prove the remaining obligations.

Distinguish the cases in `hS : w.1 ∈ S`. Rewrite using `[if_pos hS]`. Consider the cases of `hv : LL.vec w.1`. Rewrite using `[if_neg Bool.false_ne_true]`. Use `AddSubgroup.sum_mem _ fun c _ => hmon2 _ _ (flt_twistMat_mem R n j 1 e _ ?_ ?_ _ _)` and prove the remaining obligations.

Apply the tactic sequence `all_goals rw [flt_cost_single]; rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hS, hv]`. Rewrite using `[if_pos rfl]`. Use `AddSubgroup.sum_mem _ fun c _ => hmon2 _ _ (flt_twistMat_mem R n j (-1) e _ ?_ ?_ _ _)` and prove the remaining obligations. Apply the tactic sequence `all_goals rw [flt_cost_single]; rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hS, hv]`. Rewrite using `[if_neg hS]`.

Establish `h1 : (1 : GLLaurent R n) ∈ (flt_L (GLCoord R n) e).F (0 - flt_cost LL S (!bm) (Finsupp.single w 1))`. Rewrite using `[flt_cost_single, if_neg (fun h' => hS h'.1), sub_zero]`. Conclude with `(flt_L _ e).one_mem`. Simplify using `using hmon2 w 1 h1`.
-/
theorem flt_Th_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) {t : ℤ} {P : MvPolynomial (ι × Fin n) (GLLaurent R n)}
    (hP : P ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) :
    flt_Th LL S j P ∈ (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).F t := by
  have hmon2 : ∀ (u : ι × Fin n) (a : GLLaurent R n),
      a ∈ (flt_L (GLCoord R n) e).F (0 - flt_cost LL S (!bm) (Finsupp.single u 1)) →
      C (C a) * X u ∈ (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).F 0 := by
    intro u a ha
    rw [MvPolynomial.C_mul_X_eq_monomial]
    exact flt_monomial_mem (flt_C_mem ha)
  refine flt_hom_mem (flt_L (GLCoord R n) e) _ (flt_Th LL S j) 0 (fun s b hb => ?_) (fun w => ?_) hP
  · have e1 : flt_Th LL S j (C b) = C (C b) := by
      simp only [flt_Th, eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]
    rw [e1]
    exact flt_C_mem (flt_C_mem hb)
  · rw [AddMonoidHom.zero_apply]
    simp only [flt_Th, eval₂Hom_X']
    have hX1 : (X w : MvPolynomial (ι × Fin n) (GLLaurent R n)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F 0 := by
      have h1 := flt_monomial_mem (Fl := flt_L (GLCoord R n) e) (wt := 0) (t := 0)
        (m := Finsupp.single w 1) (a := 1) (by simpa using (flt_L (GLCoord R n) e).one_mem)
      rwa [← MvPolynomial.C_mul_X_eq_monomial, _root_.map_one, one_mul] at h1
    refine AddSubgroup.add_mem _ (flt_C_mem hX1) ?_
    by_cases hS : w.1 ∈ S
    · rw [if_pos hS]
      cases hv : LL.vec w.1
      · rw [if_neg Bool.false_ne_true]
        refine AddSubgroup.sum_mem _ fun c _ => hmon2 _ _ (flt_twistMat_mem R n j 1 e _ ?_ ?_ _ _)
        all_goals rw [flt_cost_single]; rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hS, hv]
      · rw [if_pos rfl]
        refine AddSubgroup.sum_mem _ fun c _ => hmon2 _ _ (flt_twistMat_mem R n j (-1) e _ ?_ ?_ _ _)
        all_goals rw [flt_cost_single]; rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hS, hv]
    · rw [if_neg hS]
      have h1 : (1 : GLLaurent R n) ∈ (flt_L (GLCoord R n) e).F (0 - flt_cost LL S (!bm) (Finsupp.single w 1)) := by
        rw [flt_cost_single, if_neg (fun h' => hS h'.1), sub_zero]
        exact (flt_L _ e).one_mem
      simpa using hmon2 w 1 h1

/- English proof (translation)
Establish `h1` using `flt_Th_mem LL S j h hF`. Establish `e1 : flt_Th LL S j (twistSub LL S j F) = MvPolynomial.map (twistSub LL S j) (flt_tay R (ι × Fin n) F)`. Establish `h2` using `RingHom.congr_fun (flt_Th_twist (R := R) LL S j) F`. Simplify `h2.symm` using `only [RingHom.comp_apply]`. Rewrite `h1` using `[e1]`.

Establish `h2` using `(flt_lift_mem.1 h1) be`. Rewrite `h2` using `[MvPolynomial.coeff_map, flt_tay_coeff]`. Then use the resulting hypothesis.
-/
theorem flt_divDer_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) {t : ℤ} {F : MvPolynomial (ι × Fin n) R}
    (hF : twistSub LL S j F ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) (be : ι × Fin n →₀ ℕ) :
    twistSub LL S j (divDer be F) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F (t - flt_cost LL S (!bm) be) := by
  have h1 := flt_Th_mem LL S j h hF
  have e1 : flt_Th LL S j (twistSub LL S j F) =
      MvPolynomial.map (twistSub LL S j) (flt_tay R (ι × Fin n) F) := by
    have h2 := RingHom.congr_fun (flt_Th_twist (R := R) LL S j) F
    simpa only [RingHom.comp_apply] using h2.symm
  rw [e1] at h1
  have h2 := (flt_lift_mem.1 h1) be
  rwa [MvPolynomial.coeff_map, flt_tay_coeff] at h2

/- English proof (translation)
Rewrite using `[_root_.map_mul]`. Establish `h1` using `(laurentCoeffFiltration R n _ e).mul_mem (flt_twist_monomial_mem (R := R) LL S j h al) (flt_divDer_mem LL S j h hF be)`. Establish `e2 : t - (flt_cost LL S bm al + flt_cost LL S (!bm) be) = -flt_cost LL S bm al + (t - flt_cost LL S (!bm) be)` using `by ring`. Rewrite using `[e2]`. Conclude with `h1`.
-/
theorem flt_op_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) {t : ℤ} {F : MvPolynomial (ι × Fin n) R}
    (hF : twistSub LL S j F ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) (al be : ι × Fin n →₀ ℕ) :
    twistSub LL S j (monomial al 1 * divDer be F) ∈
      (laurentCoeffFiltration R n (ι × Fin n) e).F (t - (flt_cost LL S bm al + flt_cost LL S (!bm) be)) := by
  rw [_root_.map_mul]
  have h1 := (laurentCoeffFiltration R n _ e).mul_mem (flt_twist_monomial_mem (R := R) LL S j h al) (flt_divDer_mem LL S j h hF be)
  have e2 : t - (flt_cost LL S bm al + flt_cost LL S (!bm) be) =
      -flt_cost LL S bm al + (t - flt_cost LL S (!bm) be) := by ring
  rw [e2]
  exact h1

/- English proof (translation)
Simplify using `only [vecDeg, Finsupp.sum]`. Apply the tactic sequence `exact Finset.sum_le_sum fun v _ => by split_ifs <;> simp`.
-/
theorem flt_vecDeg_le {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) :
    vecDeg LL S al ≤ al.sum fun _ k => k := by
  simp only [vecDeg, Finsupp.sum]
  exact Finset.sum_le_sum fun v _ => by split_ifs <;> simp

/- English proof (translation)
Simplify using `only [covDeg, Finsupp.sum]`. Apply the tactic sequence `exact Finset.sum_le_sum fun v _ => by split_ifs <;> simp`.
-/
theorem flt_covDeg_le {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) :
    covDeg LL S al ≤ al.sum fun _ k => k := by
  simp only [covDeg, Finsupp.sum]
  exact Finset.sum_le_sum fun v _ => by split_ifs <;> simp

/- English proof (translation)
Simplify using `only [covDeg, vecDeg, Finsupp.sum]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun v _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem flt_cov_add_vec_le {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) :
    covDeg LL S al + vecDeg LL S al ≤ al.sum fun _ k => k := by
  simp only [covDeg, vecDeg, Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  split_ifs <;> simp_all

/- English proof (translation)
Establish `hF` using `(flt_le_valS LL S F t).1 ht`. Establish `h1` using `flt_op_mem LL S (lastIdx n) (Or.inl ⟨rfl, rfl⟩ : flt_compat 1 false) hF al be`. Simplify using `only [flt_cost_covDeg, Bool.not_false, flt_cost_vecDeg] at h1`. Conclude with `(laurentCoeffFiltration R n _ 1).anti (by omega) h1`.
-/
theorem flt_op_mem_val {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    {F : MvPolynomial (ι × Fin n) R} {t : ℤ} (ht : (t : WithTop ℤ) ≤ valS LL S F) (al be : ι × Fin n →₀ ℕ)
    (N : ℕ) (hN : covDeg LL S al + vecDeg LL S be ≤ N) :
    twistSub LL S (lastIdx n) (monomial al 1 * divDer be F) ∈ (laurentCoeffFiltration R n (ι × Fin n) 1).F (t - N) := by
  have hF := (flt_le_valS LL S F t).1 ht
  have h1 := flt_op_mem LL S (lastIdx n) (Or.inl ⟨rfl, rfl⟩ : flt_compat 1 false) hF al be
  simp only [flt_cost_covDeg, Bool.not_false, flt_cost_vecDeg] at h1
  exact (laurentCoeffFiltration R n _ 1).anti (by omega) h1

/- English proof (translation)
Establish `hF` using `(flt_lam1S_le LL S F M).1 hM`. Establish `h1` using `flt_op_mem LL S (0 : Fin n) (Or.inr ⟨rfl, rfl⟩ : flt_compat (-1) true) hF al be`. Simplify using `only [flt_cost_vecDeg, Bool.not_true, flt_cost_covDeg] at h1`. Conclude with `(laurentCoeffFiltration R n _ (-1)).anti (by omega) h1`.
-/
theorem flt_op_mem_lam {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    {F : MvPolynomial (ι × Fin n) R} {M : ℤ} (hM : lam1S LL S F ≤ (M : WithBot ℤ)) (al be : ι × Fin n →₀ ℕ)
    (N : ℕ) (hN : vecDeg LL S al + covDeg LL S be ≤ N) :
    twistSub LL S (0 : Fin n) (monomial al 1 * divDer be F) ∈ (laurentCoeffFiltration R n (ι × Fin n) (-1)).F (-(M + N)) := by
  have hF := (flt_lam1S_le LL S F M).1 hM
  have h1 := flt_op_mem LL S (0 : Fin n) (Or.inr ⟨rfl, rfl⟩ : flt_compat (-1) true) hF al be
  simp only [flt_cost_vecDeg, Bool.not_true, flt_cost_covDeg] at h1
  exact (laurentCoeffFiltration R n _ (-1)).anti (by omega) h1

/- English proof (translation)
Use `flt_withTop_le fun t ht => ?_` and prove the remaining obligations. Rewrite using `[flt_le_valS]`. Conclude with `flt_op_mem_val LL S ht al be N hN`.
-/
theorem flt_op_valS {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R) (al be : ι × Fin n →₀ ℕ) (N : ℕ)
    (hN : covDeg LL S al + vecDeg LL S be ≤ N) :
    valS LL S F ≤ valS LL S (monomial al 1 * divDer be F) + ((N : ℤ) : WithTop ℤ) := by
  refine flt_withTop_le fun t ht => ?_
  rw [flt_le_valS]
  exact flt_op_mem_val LL S ht al be N hN

/- English proof (translation)
Use `flt_withBot_le fun M hM => ?_` and prove the remaining obligations. Rewrite using `[flt_lam1S_le]`. Conclude with `flt_op_mem_lam LL S hM al be N hN`.
-/
theorem flt_op_lam1S {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R) (al be : ι × Fin n →₀ ℕ) (N : ℕ)
    (hN : vecDeg LL S al + covDeg LL S be ≤ N) :
    lam1S LL S (monomial al 1 * divDer be F) ≤ lam1S LL S F + ((N : ℤ) : WithBot ℤ) := by
  refine flt_withBot_le fun M hM => ?_
  rw [flt_lam1S_le]
  exact flt_op_mem_lam LL S hM al be N hN

/- English proof (translation)
Unfold `DerivativeValuationBound`. Introduce `R _ ι _ LL n _ S F al be`. Conclude with `⟨flt_op_valS LL S F al be _ (add_le_add (flt_covDeg_le LL S al) (flt_vecDeg_le LL S be)), flt_op_lam1S LL S F al be _ (add_le_add (flt_vecDeg_le LL S al) (flt_covDeg_le LL S be)), flt_op_valS LL S F al be _ le_rfl, flt_op_lam1S LL S F al be _ le_rfl⟩`.
-/
theorem derivative_valuation_bound (D : Formalism.BasicNotions.D7) : DerivativeValuationBound D := by
  unfold DerivativeValuationBound
  intro R _ ι _ LL n _ S F al be
  exact ⟨flt_op_valS LL S F al be _ (add_le_add (flt_covDeg_le LL S al) (flt_vecDeg_le LL S be)),
    flt_op_lam1S LL S F al be _ (add_le_add (flt_vecDeg_le LL S al) (flt_covDeg_le LL S be)),
    flt_op_valS LL S F al be _ le_rfl, flt_op_lam1S LL S F al be _ le_rfl⟩

/- English proof (translation)
Simplify using `only [twistSub, eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]`. Use `flt_C_mem ?_` and prove the remaining obligations. Simplify using `only [coefL, RingHom.coe_comp, Function.comp_apply]`. Conclude with `flt_L_C e _`.
-/
theorem flt_twist_C_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (e : ℤ) (q : R) : twistSub LL S j (C q) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F 0 := by
  simp only [twistSub, eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]
  refine flt_C_mem ?_
  simp only [coefL, RingHom.coe_comp, Function.comp_apply]
  exact flt_L_C e _

/- English proof (translation)
Unfold `DegreeTruncationLemma`. Introduce `R _ ι _ LL n _ S c T hT q F`. Prove the components needed by the constructor for the conclusion. Use `flt_withTop_le fun t ht => ?_` and prove the remaining obligations. Rewrite using `[flt_le_valS, _root_.map_sum]`.

Use `AddSubgroup.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.smul_eq_C_mul, _root_.map_mul]`. Establish `h1` using `flt_twist_C_mem LL S (lastIdx n) 1 (q m)`. Establish `h2` using `flt_op_mem_val LL S ht m m (4 * c) ((flt_cov_add_vec_le LL S m).trans (hT m hm))`. Establish `h3` using `(laurentCoeffFiltration R n _ 1).mul_mem h1 h2`.

Rewrite `h3` using `[zero_add]`. Then use the resulting hypothesis. Use `flt_withBot_le fun M hM => ?_` and prove the remaining obligations. Rewrite using `[flt_lam1S_le, _root_.map_sum]`. Use `AddSubgroup.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.smul_eq_C_mul, _root_.map_mul]`.

Establish `h1` using `flt_twist_C_mem LL S (0 : Fin n) (-1) (q m)`. Establish `h2` using `flt_op_mem_lam LL S hM m m (4 * c) (by have h4 := flt_cov_add_vec_le LL S m; have h5 := hT m hm; omega)`. Establish `h3` using `(laurentCoeffFiltration R n _ (-1)).mul_mem h1 h2`. Rewrite `h3` using `[zero_add]`. Then use the resulting hypothesis.
-/
theorem degree_truncation (D : Formalism.BasicNotions.D7) : DegreeTruncationLemma D := by
  unfold DegreeTruncationLemma
  intro R _ ι _ LL n _ S c T hT q F
  constructor
  · refine flt_withTop_le fun t ht => ?_
    rw [flt_le_valS, _root_.map_sum]
    refine AddSubgroup.sum_mem _ fun m hm => ?_
    rw [MvPolynomial.smul_eq_C_mul, _root_.map_mul]
    have h1 := flt_twist_C_mem LL S (lastIdx n) 1 (q m)
    have h2 := flt_op_mem_val LL S ht m m (4 * c) ((flt_cov_add_vec_le LL S m).trans (hT m hm))
    have h3 := (laurentCoeffFiltration R n _ 1).mul_mem h1 h2
    rwa [zero_add] at h3
  · refine flt_withBot_le fun M hM => ?_
    rw [flt_lam1S_le, _root_.map_sum]
    refine AddSubgroup.sum_mem _ fun m hm => ?_
    rw [MvPolynomial.smul_eq_C_mul, _root_.map_mul]
    have h1 := flt_twist_C_mem LL S (0 : Fin n) (-1) (q m)
    have h2 := flt_op_mem_lam LL S hM m m (4 * c)
      (by have h4 := flt_cov_add_vec_le LL S m; have h5 := hT m hm; omega)
    have h3 := (laurentCoeffFiltration R n _ (-1)).mul_mem h1 h2
    rwa [zero_add] at h3

end Formalism.MainNotions.G.GLWeightTheory
