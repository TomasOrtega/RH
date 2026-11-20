import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubNSucc
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex

section Cube
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

/- English proof (translation)
Rewrite using `[h.s12, h.s01]`.
-/
theorem cub_rot (h : IsCub θ) (x y z : A) : θ x y z = θ z x y := by rw [h.s12, h.s01]

/- English proof (translation)
Establish `a` using `h.coc (p * q) r s z`. Establish `b` using `h.coc (p * r) q s z`. Establish `c` using `h.coc q p r z`. Rewrite `b` using `[mul_right_comm p r q]`. Rewrite `c` using `[mul_comm q p, h.s01 q p, h.s01 q (p * r)]`.

Use `replace a := congrArg Additive.ofMul a`. Use `replace b := congrArg Additive.ofMul b`. Use `replace c := congrArg Additive.ofMul c`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul] at a b c ⊢`.

Take the linear combination `(norm := abel) b - a + c`.
-/
theorem cub_four (h : IsCub θ) (p q r s z : A) :
    θ (p * q) (r * s) z * θ p q z * θ r s z = θ (p * r) (q * s) z * θ p r z * θ q s z := by
  have a := h.coc (p * q) r s z
  have b := h.coc (p * r) q s z
  have c := h.coc q p r z
  rw [mul_right_comm p r q] at b
  rw [mul_comm q p, h.s01 q p, h.s01 q (p * r)] at c
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a b c ⊢
  linear_combination (norm := abel) b - a + c

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simp [cubN, h.face]`. Consider the case `succ a ih`. Establish `f` using `cub_four h (x ^ a) (y ^ a) x y z`. Simplify using `only [CubeBalance.cubN_succ, mul_pow, pow_succ]`.

Use `replace ih := congrArg Additive.ofMul ih`. Use `replace f := congrArg Additive.ofMul f`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul] at ih f ⊢`. Take the linear combination `(norm := abel) ih + f`.
-/
theorem cubN_mul_point (h : IsCub θ) (a : ℕ) (x y z : A) :
    cubN θ a 1 (x * y) z * θ x y z ^ a = cubN θ a 1 x z * cubN θ a 1 y z * θ (x ^ a) (y ^ a) z := by
  induction a with
  | zero => simp [cubN, h.face]
  | succ a ih =>
    have f := cub_four h (x ^ a) (y ^ a) x y z
    simp only [CubeBalance.cubN_succ, mul_pow, pow_succ]
    replace ih := congrArg Additive.ofMul ih
    replace f := congrArg Additive.ofMul f
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at ih f ⊢
    linear_combination (norm := abel) ih + f

/- English proof (translation)
Rewrite using `[mulq, Finset.prod_range_succ, mulq]`.
-/
theorem mulq_succ (θ : A → A → A → U) (σ : A → U) (n : ℕ) (x : A) :
    mulq θ σ (n + 1) x = mulq θ σ n x * (cubN θ n 1 x x / dbl θ σ x ^ n) := by
  rw [mulq, Finset.prod_range_succ, mulq]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [mulq, cubN]`. Consider the case `succ m ih`. Establish `c` using `CubeBalance.cubN_add h m n x x`. Rewrite `c` using `[h.s12]`.

Rewrite using `[Nat.add_right_comm, mulq_succ, mulq_succ, CubeBalance.cubN_succ]`. Use `replace ih := congrArg Additive.ofMul ih`. Use `replace c := congrArg Additive.ofMul c`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_div, ofMul_pow] at ih c ⊢`.

Take the linear combination `(norm := module) ih + c`.
-/
theorem mulq_add (h : IsCub θ) (σ : A → U) (m n : ℕ) (x : A) :
    mulq θ σ (m + n) x * dbl θ σ x ^ (m * n) =
      mulq θ σ m x * mulq θ σ n x * (cubN θ m 1 x (x ^ n) * cubN θ n 1 x x ^ m) := by
  induction m with
  | zero => simp [mulq, cubN]
  | succ m ih =>
    have c := CubeBalance.cubN_add h m n x x
    rw [h.s12] at c
    rw [Nat.add_right_comm, mulq_succ, mulq_succ, CubeBalance.cubN_succ]
    replace ih := congrArg Additive.ofMul ih
    replace c := congrArg Additive.ofMul c
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih c ⊢
    linear_combination (norm := module) ih + c

end Cube

namespace NumB
variable {O : Type} [CommRing O] (B : NumB O)

/- English proof (translation)
Establish `a` using `B.cub.coc x y y⁻¹ x⁻¹`. Rewrite `a` using `[mul_inv_cancel, B.cub.face₂, one_mul, B.cub.s12, B.cub.s12 x y]`. Then use the resulting hypothesis.
-/
theorem θ_mul_inv_inv (x y : B.A) : B.θ (x * y) x⁻¹ y⁻¹ * B.θ x x⁻¹ y = B.θ y y⁻¹ x⁻¹ := by
  have a := B.cub.coc x y y⁻¹ x⁻¹
  rwa [mul_inv_cancel, B.cub.face₂, one_mul, B.cub.s12, B.cub.s12 x y] at a

/- English proof (translation)
Establish `a` using `B.θ_mul_inv_inv y x`. Establish `b` using `B.σ_mul x y`. Rewrite `a` using `[mul_comm y x, B.cub.s12]`. Rewrite `b` using `[← a, ← mul_assoc]`. Conclude with `mul_right_cancel b`.
-/
theorem σ_mul_symm (x y : B.A) : B.σ (x * y) * B.θ (x * y) x⁻¹ y⁻¹ = B.σ x * B.σ y := by
  have a := B.θ_mul_inv_inv y x
  have b := B.σ_mul x y
  rw [mul_comm y x, B.cub.s12] at a
  rw [← a, ← mul_assoc] at b
  exact mul_right_cancel b

/- English proof (translation)
Establish `c` using `B.cub.coc x y (x * y)⁻¹ (x * y)`. Establish `d` using `B.cub.coc y y⁻¹ x⁻¹ (x * y)`. Rewrite `c` using `[show y * (x * y)⁻¹ = x⁻¹ by rw [mul_inv, mul_comm, inv_mul_cancel_right], cub_rot B.cub x y]`. Rewrite `d` using `[mul_inv_cancel, B.cub.face, mul_comm y⁻¹, ← mul_inv, B.cub.s01 y⁻¹, cub_rot B.cub x⁻¹ y⁻¹]`. Establish `a` using `B.cub.compat x x⁻¹ x y`.

Establish `b` using `B.cub.compat y y⁻¹ x y`. Rewrite `a` using `[mul_inv_cancel, B.cub.face, B.cub.s01 x⁻¹ x y]`. Rewrite `b` using `[mul_inv_cancel, B.cub.face, B.cub.s12 y⁻¹ x y, B.cub.s01 y⁻¹ y x]`. Establish `E` using `fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e`. Establish `a` using `E a`.

Establish `b` using `E b`. Establish `c` using `E c`. Establish `d` using `E d`. Establish `s` using `E (B.σ_mul_symm x y)`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [dbl, ofMul_mul, ofMul_div, ofMul_one] at a b c d s ⊢`. Take the linear combination `(norm := abel) c - d - a - b - s`.
-/
theorem dbl_mul (x y : B.A) :
    dbl B.θ B.σ (x * y) * (B.θ (x * y) x y * B.θ x x y * B.θ y x y) =
      dbl B.θ B.σ x * dbl B.θ B.σ y := by
  have c := B.cub.coc x y (x * y)⁻¹ (x * y)
  have d := B.cub.coc y y⁻¹ x⁻¹ (x * y)
  rw [show y * (x * y)⁻¹ = x⁻¹ by rw [mul_inv, mul_comm, inv_mul_cancel_right], cub_rot B.cub x y] at c
  rw [mul_inv_cancel, B.cub.face, mul_comm y⁻¹, ← mul_inv, B.cub.s01 y⁻¹, cub_rot B.cub x⁻¹ y⁻¹] at d
  have a := B.cub.compat x x⁻¹ x y
  have b := B.cub.compat y y⁻¹ x y
  rw [mul_inv_cancel, B.cub.face, B.cub.s01 x⁻¹ x y] at a
  rw [mul_inv_cancel, B.cub.face, B.cub.s12 y⁻¹ x y, B.cub.s01 y⁻¹ y x] at b
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  have a := E a; have b := E b; have c := E c; have d := E d; have s := E (B.σ_mul_symm x y)
  apply Additive.ofMul.injective
  simp only [dbl, ofMul_mul, ofMul_div, ofMul_one] at a b c d s ⊢
  linear_combination (norm := abel) c - d - a - b - s

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simp [dbl, mulq, cubN, B.cub.face, B.σ_one]`. Consider the case `succ a ih`. Establish `d` using `B.dbl_mul (x ^ a) x`. Rewrite `d` using `[B.cub.s01 x (x ^ a), ← cub_rot B.cub (x ^ a) x]`.

Establish `n` using `B.cub.N_add a 1 x (x ^ a) x`. Rewrite `n` using `[B.cub.face, mul_one, one_mul, B.cub.s01 x (x ^ a)]`. Rewrite using `[mulq_succ, CubeBalance.cubN_succ, CubeBalance.cubN_succ, pow_succ x]`. Establish `E` using `fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e`. Establish `ih` using `E ih`.

Establish `d` using `E d`. Establish `n` using `E n`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_div, ofMul_pow] at ih d n ⊢`. Take the linear combination `(norm := module) ih + d + n`.
-/
theorem dbl_pow (a : ℕ) (x : B.A) :
    dbl B.θ B.σ (x ^ a) * (cubN B.θ a 1 x (x ^ a) * cubN B.θ a 1 x x ^ a) =
      dbl B.θ B.σ x ^ (a ^ 2) * mulq B.θ B.σ a x ^ 2 := by
  induction a with
  | zero => simp [dbl, mulq, cubN, B.cub.face, B.σ_one]
  | succ a ih =>
    have d := B.dbl_mul (x ^ a) x
    rw [B.cub.s01 x (x ^ a), ← cub_rot B.cub (x ^ a) x] at d
    have n := B.cub.N_add a 1 x (x ^ a) x
    rw [B.cub.face, mul_one, one_mul, B.cub.s01 x (x ^ a)] at n
    rw [mulq_succ, CubeBalance.cubN_succ, CubeBalance.cubN_succ, pow_succ x]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have d := E d; have n := E n
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih d n ⊢
    linear_combination (norm := module) ih + d + n

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simp [mulq]`. Consider the case `succ a ih`. Establish `m` using `mulq_add B.cub B.σ (a * b) b x`. Establish `c` using `CubeBalance.cubN_mul B.cub a b x (x ^ b)`.

Establish `d` using `B.dbl_pow b x`. Rewrite using `[Nat.succ_mul, mulq_succ]`. Establish `E` using `fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e`. Establish `ih` using `E ih`. Establish `m` using `E m`.

Establish `c` using `E c`. Establish `d` using `E d`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_div, ofMul_pow] at ih m c d ⊢`. Take the linear combination `(norm := module) ih + m + c + a • d`.
-/
theorem mulq_mul (a b : ℕ) (x : B.A) :
    mulq B.θ B.σ (a * b) x = mulq B.θ B.σ a (x ^ b) * mulq B.θ B.σ b x ^ (a ^ 2) := by
  induction a with
  | zero => simp [mulq]
  | succ a ih =>
    have m := mulq_add B.cub B.σ (a * b) b x
    have c := CubeBalance.cubN_mul B.cub a b x (x ^ b)
    have d := B.dbl_pow b x
    rw [Nat.succ_mul, mulq_succ]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have m := E m; have c := E c; have d := E d
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih m c d ⊢
    linear_combination (norm := module) ih + m + c + a • d

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simp [mulq, cubN]`. Consider the case `succ a ih`. Establish `d` using `B.dbl_mul x y`. Establish `f` using `cubN_mul_point B.cub a x y (x * y)`.

Establish `n₁` using `B.cub.N_add a 1 x x y`. Establish `n₂` using `B.cub.N_add a 1 y x y`. Establish `n₃` using `B.cub.N_add a 1 x (y ^ a) y`. Rewrite `n₁`, `n₂`, `n₃` using `[B.cub.face, mul_one, one_mul]`. Rewrite `f` using `[cub_rot B.cub x y]`.

Rewrite `n₃` using `[← cub_rot B.cub (y ^ a) y x]`. Establish `c₁` using `B.cub.compat (x ^ a) (y ^ a) x y`. Establish `c₂` using `B.cub.coc (x ^ a) (y ^ a) y x`. Rewrite `c₂` using `[B.cub.s12 (x ^ a * y ^ a), B.cub.s12 (x ^ a) (y ^ a * y)]`. Rewrite using `[mulq_succ, mulq_succ, mulq_succ, CubeBalance.cubN_succ, CubeBalance.cubN_succ, pow_succ y]`.

Establish `E` using `fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e`. Establish `ih` using `E ih`. Establish `d` using `E d`. Establish `f` using `E f`. Establish `n₁` using `E n₁`.

Establish `n₂` using `E n₂`. Establish `n₃` using `E n₃`. Establish `c₁` using `E c₁`. Establish `c₂` using `E c₂`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_div, ofMul_pow] at ih d f n₁ n₂ n₃ c₁ c₂ ⊢`. Take the linear combination `(norm := module) ih + f + n₁ + n₂ - n₃ - a • d - c₁ + c₂`.
-/
theorem mulq_mul_point (a : ℕ) (x y : B.A) :
    mulq B.θ B.σ a (x * y) = mulq B.θ B.σ a x * mulq B.θ B.σ a y *
      (cubN B.θ a 1 x (y ^ a) * cubN B.θ a 1 y x ^ a) := by
  induction a with
  | zero => simp [mulq, cubN]
  | succ a ih =>
    have d := B.dbl_mul x y
    have f := cubN_mul_point B.cub a x y (x * y)
    have n₁ := B.cub.N_add a 1 x x y
    have n₂ := B.cub.N_add a 1 y x y
    have n₃ := B.cub.N_add a 1 x (y ^ a) y
    rw [B.cub.face, mul_one, one_mul] at n₁ n₂ n₃
    rw [cub_rot B.cub x y] at f
    rw [← cub_rot B.cub (y ^ a) y x] at n₃
    have c₁ := B.cub.compat (x ^ a) (y ^ a) x y
    have c₂ := B.cub.coc (x ^ a) (y ^ a) y x
    rw [B.cub.s12 (x ^ a * y ^ a), B.cub.s12 (x ^ a) (y ^ a * y)] at c₂
    rw [mulq_succ, mulq_succ, mulq_succ, CubeBalance.cubN_succ, CubeBalance.cubN_succ, pow_succ y]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have d := E d; have f := E f; have n₁ := E n₁; have n₂ := E n₂; have n₃ := E n₃
    have c₁ := E c₁; have c₂ := E c₂
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih d f n₁ n₂ n₃ c₁ c₂ ⊢
    linear_combination (norm := module) ih + f + n₁ + n₂ - n₃ - a • d - c₁ + c₂

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simp [cubN, B.σ_one]`. Consider the case `succ a ih`. Establish `s` using `B.σ_cub (x ^ a) x x`. Establish `t` using `B.σ_cub x x x⁻¹`.

Establish `u` using `B.σ_inv x`. Rewrite `t` using `[inv_inv, mul_inv_cancel, mul_inv_cancel_right, B.σ_one, B.cub.s12 x⁻¹, B.cub.s12 x]`. Rewrite using `[CubeBalance.cubN_succ, CubeBalance.cubN_succ, inv_pow, pow_succ x]`. Establish `E` using `fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e`. Establish `ih` using `E ih`.

Establish `s` using `E s`. Establish `t` using `E t`. Establish `u` using `E u`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_pow, ofMul_one] at ih s t u ⊢`.

Take the linear combination `(norm := module) ih + s - t - u`.
-/
theorem cubN_inv_inv (a : ℕ) (x : B.A) :
    cubN B.θ a 1 x⁻¹ x⁻¹ * B.θ x x⁻¹ x ^ a * (B.σ x * B.σ (x ^ a)) =
      cubN B.θ a 1 x x * B.θ x⁻¹ x x⁻¹ ^ a * B.σ (x ^ a * x) := by
  induction a with
  | zero => simp [cubN, B.σ_one]
  | succ a ih =>
    have s := B.σ_cub (x ^ a) x x
    have t := B.σ_cub x x x⁻¹
    have u := B.σ_inv x
    rw [inv_inv, mul_inv_cancel, mul_inv_cancel_right, B.σ_one, B.cub.s12 x⁻¹, B.cub.s12 x] at t
    rw [CubeBalance.cubN_succ, CubeBalance.cubN_succ, inv_pow, pow_succ x]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have s := E s; have t := E t; have u := E u
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_one] at ih s t u ⊢
    linear_combination (norm := module) ih + s - t - u

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simp [mulq, B.σ_one]`. Consider the case `succ a ih`. Establish `g` using `B.cubN_inv_inv a x`. Establish `u` using `B.σ_inv x`.

Rewrite using `[mulq_succ, mulq_succ, pow_succ x]`. Establish `E` using `fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e`. Establish `ih` using `E ih`. Establish `g` using `E g`. Establish `u` using `E u`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [dbl, inv_inv, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at ih g u ⊢`. Take the linear combination `(norm := module) ih + g + a • u`.
-/
theorem mulq_inv (a : ℕ) (x : B.A) :
    mulq B.θ B.σ a x⁻¹ * B.σ x ^ (a ^ 2) = mulq B.θ B.σ a x * B.σ (x ^ a) := by
  induction a with
  | zero => simp [mulq, B.σ_one]
  | succ a ih =>
    have g := B.cubN_inv_inv a x
    have u := B.σ_inv x
    rw [mulq_succ, mulq_succ, pow_succ x]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have g := E g; have u := E u
    apply Additive.ofMul.injective
    simp only [dbl, inv_inv, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at ih g u ⊢
    linear_combination (norm := module) ih + g + a • u

end NumB

/- English proof (translation)
Introduce `_ _ B a b x y` and use `⟨B.mulq_mul a b x, B.mulq_mul_point a x y, B.dbl_pow a x, B.mulq_inv a x⟩`.
-/
theorem mulq_laws : ∀ (O : Type) [CommRing O] (B : NumB O) (a b : ℕ) (x y : B.A), mulq B.θ B.σ (a * b) x = mulq B.θ B.σ a (x ^ b) * mulq B.θ B.σ b x ^ (a ^ 2) ∧ mulq B.θ B.σ a (x * y) = mulq B.θ B.σ a x * mulq B.θ B.σ a y * (cubN B.θ a 1 x (y ^ a) * cubN B.θ a 1 y x ^ a) ∧ dbl B.θ B.σ (x ^ a) * (cubN B.θ a 1 x (x ^ a) * cubN B.θ a 1 x x ^ a) = dbl B.θ B.σ x ^ (a ^ 2) * mulq B.θ B.σ a x ^ 2 ∧ mulq B.θ B.σ a x⁻¹ * B.σ x ^ (a ^ 2) = mulq B.θ B.σ a x * B.σ (x ^ a) :=
  fun _ _ B a b x y => ⟨B.mulq_mul a b x, B.mulq_mul_point a x y, B.dbl_pow a x, B.mulq_inv a x⟩

end GlobalTheory.Ex
