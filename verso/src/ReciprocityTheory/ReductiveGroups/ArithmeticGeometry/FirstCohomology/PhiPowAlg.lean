import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

def hv (θ : A → A → A → U) (k : ℕ) (a B x : A) : U := cubN θ k a B x * (θ a x B)⁻¹

/- English proof (translation)
Conclude with `(h.s01 x y z).trans (h.s12 y x z)`.
-/
theorem cub_rot (h : IsCub θ) (x y z : A) : θ x y z = θ y z x := by
  exact (h.s01 x y z).trans (h.s12 y x z)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Finset.prod_range_succ, Finset.prod_range_succ, ih]`. Establish `e` using `h.coc a (M * b ^ k) b x`.

Rewrite `e` using `[← mul_assoc a M (b ^ k), mul_assoc M (b ^ k) b, ← pow_succ b k]`. Establish `hA : θ (a * M * b ^ k) b x = θ a (M * b ^ (k + 1)) x * θ (M * b ^ k) b x * (θ a (M * b ^ k) x)⁻¹`. Rewrite using `[← e, mul_inv_cancel_right]`. Rewrite using `[hA]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
private lemma prod_range_theta_mul_pow_eq_of_isCub (h : IsCub θ) (k : ℕ) (a M b x : A) :
    ∏ i ∈ Finset.range k, θ (a * M * b ^ i) b x =
      (∏ i ∈ Finset.range k, θ (M * b ^ i) b x) * θ a (M * b ^ k) x * (θ a M x)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
    have e := h.coc a (M * b ^ k) b x
    rw [← mul_assoc a M (b ^ k), mul_assoc M (b ^ k) b, ← pow_succ b k] at e
    have hA : θ (a * M * b ^ k) b x =
        θ a (M * b ^ (k + 1)) x * θ (M * b ^ k) b x * (θ a (M * b ^ k) x)⁻¹ := by
      rw [← e, mul_inv_cancel_right]
    rw [hA]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

/- English proof (translation)
Establish `hS : S = W⁻¹ * (T * G0)` using `by rw [c2, inv_mul_cancel_left]`. Establish `hP : P = T * V * R⁻¹` using `by rw [← c1, mul_inv_cancel_right]`. Substitute `hS hP` using the available equality. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, inv_inv]`.

Normalize the expressions using the abelian group laws.
-/
private lemma mul_inv_rearrange_of_two_relations (Q G' G0 P R S T V W : U) (c1 : P * R = T * V) (c2 : T * G0 = W * S) :
    Q * G' * G0⁻¹ * P⁻¹ * R⁻¹ * S = Q * V⁻¹ * (G' * W⁻¹) := by
  have hS : S = W⁻¹ * (T * G0) := by rw [c2, inv_mul_cancel_left]
  have hP : P = T * V * R⁻¹ := by rw [← c1, mul_inv_cancel_right]
  subst hS hP
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, inv_inv]
  abel

/- English proof (translation)
Establish `c1` using `h.coc a M x b`. Establish `c2 : θ a (M * x) b * θ a M x = θ a M (x * b) * θ a x b`. Establish `e` using `h.coc M x b a`. Rewrite `e` using `[← cub_rot h a (M * x) b, ← cub_rot h a M x, ← cub_rot h a M (x * b), ← cub_rot h a x b]`. Conclude with `e`.

Simplify using `only [hv, cubN]`. Rewrite using `[prod_range_theta_mul_pow_eq_of_isCub h]`. Conclude with `mul_inv_rearrange_of_two_relations _ _ _ _ _ _ _ _ _ c1 c2`.
-/
theorem hv_term (h : IsCub θ) (k : ℕ) (a M b x : A) :
    hv θ k (a * M) b x * (θ a M b)⁻¹ * θ a x b = hv θ k M b x * (θ a (M * b ^ k) x * (θ a M (x * b))⁻¹) := by
  have c1 := h.coc a M x b
  have c2 : θ a (M * x) b * θ a M x = θ a M (x * b) * θ a x b := by
    have e := h.coc M x b a
    rw [← cub_rot h a (M * x) b, ← cub_rot h a M x, ← cub_rot h a M (x * b), ← cub_rot h a x b] at e
    exact e
  simp only [hv, cubN]
  rw [prod_range_theta_mul_pow_eq_of_isCub h]
  exact mul_inv_rearrange_of_two_relations _ _ _ _ _ _ _ _ _ c1 c2

/- English proof (translation)
Rewrite using `[div_eq_mul_inv, ← e]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
private lemma eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq {X Y R S F1 F0 : U} (e : X * R⁻¹ * S = Y * (F1 * F0⁻¹)) :
    X = Y * (F1 / F0) * R * S⁻¹ := by
  rw [div_eq_mul_inv, ← e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- English proof (translation)
Establish `hf : ∀ i ∈ Finset.range k, hv θ k (a * (b ^ k) ^ i) b (b ^ (k - 1 - i)) = hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) * (θ a ((b ^ k) ^ (i + 1)) (b ^ (k - (i + 1))) / θ a ((b ^ k) ^ i) (b ^ (k - i))) * θ a ((b ^ k) ^ i) b * (θ a (b ^ (k - 1 - i)) b)⁻¹`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Establish `e` using `hv_term h k a ((b ^ k) ^ i) b (b ^ (k - 1 - i))`. Establish `e1 : (b ^ k) ^ i * b ^ k = (b ^ k) ^ (i + 1)` using `(pow_succ _ _).symm`.

Establish `e2 : b ^ (k - 1 - i) * b = b ^ (k - i)`. Rewrite using `[← pow_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `e3 : k - 1 - i = k - (i + 1)` using `by omega`.

Rewrite `e` using `[e1, e2]`. Rewrite using `[← e3]`. Conclude with `eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq e`. Establish `tel : ∏ i ∈ Finset.range k, (θ a ((b ^ k) ^ (i + 1)) (b ^ (k - (i + 1))) / θ a ((b ^ k) ^ i) (b ^ (k - i))) = θ a ((b ^ k) ^ k) (b ^ (k - k)) / θ a ((b ^ k) ^ 0) (b ^ (k - 0))` using `Finset.prod_range_div (fun j => θ a ((b ^ k) ^ j) (b ^ (k - j))) k`. Establish `f1 : θ a ((b ^ k) ^ k) (b ^ (k - k)) = 1`.

Rewrite using `[Nat.sub_self, pow_zero, ← cub_rot h 1 a, h.face]`. Establish `f0 : θ a ((b ^ k) ^ 0) (b ^ (k - 0)) = 1`. Rewrite using `[pow_zero, cub_rot h a 1, h.face]`. Establish `refl : ∏ i ∈ Finset.range k, θ a (b ^ (k - 1 - i)) b = ∏ i ∈ Finset.range k, θ a (b ^ i) b` using `Finset.prod_range_reflect (fun j => θ a (b ^ j) b) k`. Establish `cub : cubN θ k 1 b a = ∏ i ∈ Finset.range k, θ a (b ^ i) b`.

Simplify using `only [cubN]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[one_mul, cub_rot h a (b ^ i) b]`. Rewrite using `[Finset.prod_congr rfl hf, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, tel, refl, cub, f1, f0]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]`. Normalize the expressions using the abelian group laws.
-/
theorem phiPow_indep (h : IsCub θ) (k : ℕ) (a b : A) :
    (∏ i ∈ Finset.range k, hv θ k (a * (b ^ k) ^ i) b (b ^ (k - 1 - i))) * cubN θ k 1 b a *
        (∏ i ∈ Finset.range k, θ a ((b ^ k) ^ i) b)⁻¹ =
      ∏ i ∈ Finset.range k, hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) := by
  have hf : ∀ i ∈ Finset.range k, hv θ k (a * (b ^ k) ^ i) b (b ^ (k - 1 - i)) =
      hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) *
        (θ a ((b ^ k) ^ (i + 1)) (b ^ (k - (i + 1))) / θ a ((b ^ k) ^ i) (b ^ (k - i))) *
        θ a ((b ^ k) ^ i) b * (θ a (b ^ (k - 1 - i)) b)⁻¹ := by
    intro i hi
    rw [Finset.mem_range] at hi
    have e := hv_term h k a ((b ^ k) ^ i) b (b ^ (k - 1 - i))
    have e1 : (b ^ k) ^ i * b ^ k = (b ^ k) ^ (i + 1) := (pow_succ _ _).symm
    have e2 : b ^ (k - 1 - i) * b = b ^ (k - i) := by
      rw [← pow_succ]
      congr 1
      omega
    have e3 : k - 1 - i = k - (i + 1) := by omega
    rw [e1, e2] at e
    rw [← e3]
    exact eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq e
  have tel : ∏ i ∈ Finset.range k,
      (θ a ((b ^ k) ^ (i + 1)) (b ^ (k - (i + 1))) / θ a ((b ^ k) ^ i) (b ^ (k - i))) =
      θ a ((b ^ k) ^ k) (b ^ (k - k)) / θ a ((b ^ k) ^ 0) (b ^ (k - 0)) :=
    Finset.prod_range_div (fun j => θ a ((b ^ k) ^ j) (b ^ (k - j))) k
  have f1 : θ a ((b ^ k) ^ k) (b ^ (k - k)) = 1 := by
    rw [Nat.sub_self, pow_zero, ← cub_rot h 1 a, h.face]
  have f0 : θ a ((b ^ k) ^ 0) (b ^ (k - 0)) = 1 := by
    rw [pow_zero, cub_rot h a 1, h.face]
  have refl : ∏ i ∈ Finset.range k, θ a (b ^ (k - 1 - i)) b = ∏ i ∈ Finset.range k, θ a (b ^ i) b :=
    Finset.prod_range_reflect (fun j => θ a (b ^ j) b) k
  have cub : cubN θ k 1 b a = ∏ i ∈ Finset.range k, θ a (b ^ i) b := by
    simp only [cubN]
    apply Finset.prod_congr rfl
    intro i _
    rw [one_mul, cub_rot h a (b ^ i) b]
  rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_inv_distrib, tel, refl, cub, f1, f0]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
  abel

end ReciprocityTheory.ChartRestriction.G.H1
