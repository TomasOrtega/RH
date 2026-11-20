import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowAlg

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

/- English proof (translation)
Establish `c1` using `h.coc P B (q * b) x`. Establish `c2` using `h.coc B q b x`. Establish `c3` using `h.coc P q (B * b) x`. Establish `c4` using `h.coc q B b x`. Rewrite `c1` using `[mul_left_comm B q b]`.

Rewrite `c4` using `[mul_comm q B, h.s01 q B x]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem four (h : IsCub θ) (P q B b x : A) :
    θ (P * B) (q * b) x * θ P B x * θ q b x = θ (P * q) (B * b) x * θ P q x * θ B b x := by
  have c1 := h.coc P B (q * b) x
  have c2 := h.coc B q b x
  have c3 := h.coc P q (B * b) x
  have c4 := h.coc q B b x
  rw [mul_left_comm B q b] at c1
  rw [mul_comm q B, h.s01 q B x] at c4
  calc θ (P * B) (q * b) x * θ P B x * θ q b x
      = θ P (q * (B * b)) x * (θ B (q * b) x * θ q b x) := by rw [c1, mul_assoc]
    _ = θ P (q * (B * b)) x * (θ q (B * b) x * θ B b x) := by rw [← c2, c4]
    _ = θ (P * q) (B * b) x * θ P q x * θ B b x := by rw [c3, mul_assoc]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [cubN, h.face]`. Consider the case `succ k ih`. Establish `f` using `four h (B ^ k) (b ^ k) B b x`. Simplify using `only [cubN, one_mul] at ih ⊢`.

Rewrite using `[Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, pow_succ B, pow_succ b, pow_succ (θ B b x), mul_pow]`. Apply `mul_right_cancel (b := θ (B ^ k) (b ^ k) x)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cubic_norm_mul_identity (h : IsCub θ) (k : ℕ) (B b x : A) :
    θ (B ^ k) (b ^ k) x * cubN θ k 1 B x * cubN θ k 1 b x = cubN θ k 1 (B * b) x * θ B b x ^ k := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have f := four h (B ^ k) (b ^ k) B b x
    simp only [cubN, one_mul] at ih ⊢
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, pow_succ B, pow_succ b,
      pow_succ (θ B b x), mul_pow]
    apply mul_right_cancel (b := θ (B ^ k) (b ^ k) x)
    calc _ = (θ (B ^ k * B) (b ^ k * b) x * θ (B ^ k) B x * θ (b ^ k) b x) *
          (θ (B ^ k) (b ^ k) x * (∏ i ∈ Finset.range k, θ (B ^ i) B x) *
            ∏ i ∈ Finset.range k, θ (b ^ i) b x) := by ac_rfl
      _ = _ := by rw [f, ih]; ac_rfl

/- English proof (translation)
Establish `e1` using `cubic_norm_mul_identity h k B b x`. Establish `c` using `h.coc a (B ^ k) (b ^ k) x`. Rewrite using `[h.N_split k a B x, h.N_split k (a * B ^ k) b x, h.N_split k a (B * b) x, mul_pow, h.s12 B x b]`. Apply `mul_right_cancel (b := θ (B ^ k) (b ^ k) x * θ B b x ^ k)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

The two sides agree by associativity and commutativity. Use `_ = (θ a (B ^ k * b ^ k) x * θ (B ^ k) (b ^ k) x) * (cubN θ k 1 (B * b) x * θ B b x ^ k) := by`. Rewrite using `[c, e1, inv_mul_cancel, mul_one]`. Use `_ = _ := by ac_rfl`.
-/
theorem cubN_mul (h : IsCub θ) (k : ℕ) (a B b x : A) :
    cubN θ k a B x * cubN θ k (a * B ^ k) b x * (θ B x b ^ k)⁻¹ = cubN θ k a (B * b) x := by
  have e1 := cubic_norm_mul_identity h k B b x
  have c := h.coc a (B ^ k) (b ^ k) x
  rw [h.N_split k a B x, h.N_split k (a * B ^ k) b x, h.N_split k a (B * b) x, mul_pow, h.s12 B x b]
  apply mul_right_cancel (b := θ (B ^ k) (b ^ k) x * θ B b x ^ k)
  calc _ = (θ (a * B ^ k) (b ^ k) x * θ a (B ^ k) x) *
        (θ (B ^ k) (b ^ k) x * cubN θ k 1 B x * cubN θ k 1 b x) * ((θ B b x ^ k)⁻¹ * θ B b x ^ k) := by
        ac_rfl
    _ = (θ a (B ^ k * b ^ k) x * θ (B ^ k) (b ^ k) x) * (cubN θ k 1 (B * b) x * θ B b x ^ k) := by
        rw [c, e1, inv_mul_cancel, mul_one]
    _ = _ := by ac_rfl

/- English proof (translation)
Establish `n` using `h.N_add k a B x b`. Establish `m` using `cubN_mul h k a B b x`. Establish `t : ∀ u v, θ a u v = θ u v a` using `fun u v => (h.s01 a u v).trans (h.s12 u a v)`. Establish `key : θ a x b * θ a (x * b) B = θ a x (B * b) * θ a b B`. Establish `c` using `h.coc x b B a`.

Rewrite using `[t x b, t (x * b) B, t x (B * b), t b B, mul_comm B b, mul_comm (θ x b a)]`. Conclude with `c`. Simplify using `only [hv]`. Apply `mul_right_cancel (b := θ a x b * θ a (x * b) B * θ (a * B ^ k) x b * θ B x b ^ k)` to reduce the goal to its premises. Rewrite using `[← m]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[n, inv_mul_cancel, inv_mul_cancel, mul_one, mul_one]`. Use `_ = (cubN θ k a B x * cubN θ k (a * B ^ k) b x * cubN θ k a B b * θ (a * B ^ k) x b) * ((θ B x b ^ k)⁻¹ * θ B x b ^ k) * ((θ a x (B * b))⁻¹ * θ a x (B * b)) * ((θ a b B)⁻¹ * θ a b B) := by`. Rewrite using `[inv_mul_cancel, inv_mul_cancel, inv_mul_cancel, mul_one, mul_one, mul_one]`. The two sides agree by associativity and commutativity.

Use `_ = _ := by rw [key]; ac_rfl`.
-/
theorem hv_comp (h : IsCub θ) (k : ℕ) (a B b x : A) :
    hv θ k a B (x * b) * hv θ k (a * B ^ k) b x = hv θ k a (B * b) x * hv θ k a B b := by
  have n := h.N_add k a B x b
  have m := cubN_mul h k a B b x
  have t : ∀ u v, θ a u v = θ u v a := fun u v => (h.s01 a u v).trans (h.s12 u a v)
  have key : θ a x b * θ a (x * b) B = θ a x (B * b) * θ a b B := by
    have c := h.coc x b B a
    rw [t x b, t (x * b) B, t x (B * b), t b B, mul_comm B b, mul_comm (θ x b a)]
    exact c
  simp only [hv]
  apply mul_right_cancel (b := θ a x b * θ a (x * b) B * θ (a * B ^ k) x b * θ B x b ^ k)
  rw [← m]
  calc _ = (cubN θ k a B (x * b) * θ a x b * θ B x b ^ k) * cubN θ k (a * B ^ k) b x *
        ((θ a (x * b) B)⁻¹ * θ a (x * b) B) * ((θ (a * B ^ k) x b)⁻¹ * θ (a * B ^ k) x b) := by ac_rfl
    _ = θ (a * B ^ k) x b * cubN θ k a B x * cubN θ k a B b * cubN θ k (a * B ^ k) b x := by
        rw [n, inv_mul_cancel, inv_mul_cancel, mul_one, mul_one]
    _ = (cubN θ k a B x * cubN θ k (a * B ^ k) b x * cubN θ k a B b * θ (a * B ^ k) x b) *
        ((θ B x b ^ k)⁻¹ * θ B x b ^ k) * ((θ a x (B * b))⁻¹ * θ a x (B * b)) * ((θ a b B)⁻¹ * θ a b B) := by
        rw [inv_mul_cancel, inv_mul_cancel, inv_mul_cancel, mul_one, mul_one, mul_one]; ac_rfl
    _ = _ := by rw [key]; ac_rfl

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
