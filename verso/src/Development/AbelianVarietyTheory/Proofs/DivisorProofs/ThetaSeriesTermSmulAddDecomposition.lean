import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Use `set H := Subgroup.closure (Set.range N.c ∪ {h.b}) with hH`. Use `set T := S.toSubmonoid.units with hT`. Use `set π : Oˣ →* Oˣ ⧸ T := QuotientGroup.mk' T with hπ`. Establish `Hc : ∀ a, N.c a ∈ H` using `fun a => Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)`. Establish `Hb : h.b ∈ H` using `Subgroup.subset_closure (Or.inr rfl)`.

Establish `θ1 : ∀ x ∈ H, ∀ x' ∈ H, ∀ x'' ∈ H, π (N.θ x x' x'') = 1` using `fun x hx x' hx' x'' hx'' => (QuotientGroup.eq_one_iff _).2 ((Submonoid.mem_units_iff _ _).2 (hθ x hx x' hx' x'' hx''))`. Establish `σ1 : ∀ a, π (N.σ (N.c a)) = 1` using `fun a => (QuotientGroup.eq_one_iff _).2 ((Submonoid.mem_units_iff _ _).2 (hσ _ (Hc a)))`. Establish `Bl : ∀ a a' b, π (N.τ (a + a') b) = π (N.τ a b) * π (N.τ a' b)`. Introduce `a a' b`. Use `congrArg π (N.τ_add_left a a' b)` as an intermediate fact.

Rewrite `this` using `[map_mul, map_mul, θ1 _ (Hc a) _ (Hc a') _ (Hc b), mul_one]`. Then use the resulting hypothesis. Establish `Br : ∀ a b b', π (N.τ a (b + b')) = π (N.τ a b) * π (N.τ a b')`. Introduce `a b b'`. Use `congrArg π (N.τ_add_right a b b')` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, θ1 _ (Hc b) _ (Hc b') _ (Hc a), mul_one]`. Then use the resulting hypothesis.

Establish `fadd : ∀ a b, π (N.ψ (a + b)) = π (N.τ a b) * π (N.ψ a) * π (N.ψ b)`. Introduce `a b`. Rewrite using `[N.ψ_add, map_mul, map_mul]`. Establish `fneg : ∀ a, π (N.ψ (-a)) = π (N.ψ a)`. Introduce `a`.

Use `congrArg π (N.even a)` as an intermediate fact. Rewrite `this` using `[map_mul, σ1, mul_one]`. Then use the resulting hypothesis. Establish `Bnegr : ∀ a b, π (N.τ a (-b)) = (π (N.τ a b))⁻¹`. Introduce `a b`. Use `Br a b (-b)` as an intermediate fact.

Rewrite `this` using `[add_neg_cancel, N.τ_zero_right, map_one]`. Conclude with `eq_inv_of_mul_eq_one_right this.symm`. Establish `Bself : ∀ a, π (N.τ a a) = π (N.ψ a) ^ 2`. Introduce `a`. Use `fadd a (-a)` as an intermediate fact.

Rewrite `this` using `[add_neg_cancel, N.ψ_zero, map_one, fneg, Bnegr, mul_assoc, eq_comm, inv_mul_eq_one]`. Rewrite using `[sq]`. Conclude with `this`. Establish `Bsmul : ∀ (k : ℕ) a b, π (N.τ (k • a) b) = π (N.τ a b) ^ k`. Introduce `k a b`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [succ_nsmul, Bl, ih, pow_succ]`. Establish `Bsmulr : ∀ (k : ℕ) a b, π (N.τ a (k • b)) = π (N.τ a b) ^ k`. Introduce `k a b`.

Rewrite using `[N.τ_symm, Bsmul, N.τ_symm]`. Establish `fsmul : ∀ (k : ℕ) a, π (N.ψ (k • a)) = π (N.ψ a) ^ (k ^ 2)`. Introduce `k a`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Rewrite using `[succ_nsmul, fadd, ih, Bsmul, Bself, ← pow_mul, ← pow_add, ← pow_succ]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `Sadd : ∀ χ χ', π (h.s (χ + χ')) = π (h.s χ) * π (h.s χ')`.

Introduce `χ χ'`. Use `congrArg π (h.mult χ χ')` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, θ1 _ (Hc χ) _ (Hc χ') _ Hb, mul_one]`. Then use the resulting hypothesis. Establish `Ssmul : ∀ (k : ℕ) a, π (h.s (k • a)) = π (h.s a) ^ k`. Introduce `k a`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [succ_nsmul, Sadd, ih, pow_succ]`. Establish `Spow : π (h.s a) ^ m = π (N.τ a y)`. Use `congrArg π (h.pow_s m a)` as an intermediate fact.

Rewrite `this` using `[map_mul, map_pow, hy, GlobalTheory.Ex.NumD.io_s, N.τ_symm]`. Establish `hc : π (cubN N.θ m 1 h.b (N.c a)) = 1`. Unfold `cubN`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_eq_one fun i _ => θ1 _ (by rw [one_mul]; exact pow_mem Hb i) _ Hb _ (Hc a)`.

Rewrite `this` using `[hc, mul_one]`. Conclude with `this.symm`. Use `⟨N.ψ (m • a + b) * h.s (m • a + b) / (N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b)), ?_, ?_⟩` and prove the remaining obligations. Establish `e : π (N.ψ (m • a + b) * h.s (m • a + b) / (N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b))) = 1`. Rewrite using `[map_div, div_eq_one, map_mul, map_mul, map_mul, map_mul, map_pow, fadd, Sadd, fsmul, Bsmul, Br, Bsmulr, Ssmul, Spow]`.

The two sides agree by associativity and commutativity. Conclude with `((Submonoid.mem_units_iff _ _).1 ((QuotientGroup.eq_one_iff _).1 e)).1`. Conclude with `(fun (L X Y Z : Oˣ) => show L = L / (X * Y * Z) * X * Y * Z by`. Rewrite using `[mul_assoc (L / (X * Y * Z)) X Y, mul_assoc (L / (X * Y * Z)) (X * Y) Z, div_mul_cancel]) _ _ _ _`.
-/
theorem theta_term_smul_add (O : Type) [CommRing O] (N : GlobalTheory.Ex.NumD O) (S : Subring O) (m : ℕ) (h : N.Gt)
    (y : N.X) (hy : h ^ m = N.io y)
    (hθ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}),
      ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}),
        (N.θ x x' x'' : O) ∈ S ∧ (((N.θ x x' x'')⁻¹ : Oˣ) : O) ∈ S)
    (hσ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.σ x : O) ∈ S ∧ (((N.σ x)⁻¹ : Oˣ) : O) ∈ S)
    (a b : N.X) : ∃ w : Oˣ, (w : O) ∈ S ∧
      N.ψ (m • a + b) * h.s (m • a + b) = w * N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b) := by
  set H := Subgroup.closure (Set.range N.c ∪ {h.b}) with hH
  set T := S.toSubmonoid.units with hT
  set π : Oˣ →* Oˣ ⧸ T := QuotientGroup.mk' T with hπ
  have Hc : ∀ a, N.c a ∈ H := fun a => Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
  have Hb : h.b ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have θ1 : ∀ x ∈ H, ∀ x' ∈ H, ∀ x'' ∈ H, π (N.θ x x' x'') = 1 := fun x hx x' hx' x'' hx'' =>
    (QuotientGroup.eq_one_iff _).2 ((Submonoid.mem_units_iff _ _).2 (hθ x hx x' hx' x'' hx''))
  have σ1 : ∀ a, π (N.σ (N.c a)) = 1 := fun a =>
    (QuotientGroup.eq_one_iff _).2 ((Submonoid.mem_units_iff _ _).2 (hσ _ (Hc a)))
  have Bl : ∀ a a' b, π (N.τ (a + a') b) = π (N.τ a b) * π (N.τ a' b) := by
    intro a a' b
    have := congrArg π (N.τ_add_left a a' b)
    rwa [map_mul, map_mul, θ1 _ (Hc a) _ (Hc a') _ (Hc b), mul_one] at this
  have Br : ∀ a b b', π (N.τ a (b + b')) = π (N.τ a b) * π (N.τ a b') := by
    intro a b b'
    have := congrArg π (N.τ_add_right a b b')
    rwa [map_mul, map_mul, θ1 _ (Hc b) _ (Hc b') _ (Hc a), mul_one] at this
  have fadd : ∀ a b, π (N.ψ (a + b)) = π (N.τ a b) * π (N.ψ a) * π (N.ψ b) := by
    intro a b
    rw [N.ψ_add, map_mul, map_mul]
  have fneg : ∀ a, π (N.ψ (-a)) = π (N.ψ a) := by
    intro a
    have := congrArg π (N.even a)
    rwa [map_mul, σ1, mul_one] at this
  have Bnegr : ∀ a b, π (N.τ a (-b)) = (π (N.τ a b))⁻¹ := by
    intro a b
    have := Br a b (-b)
    rw [add_neg_cancel, N.τ_zero_right, map_one] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have Bself : ∀ a, π (N.τ a a) = π (N.ψ a) ^ 2 := by
    intro a
    have := fadd a (-a)
    rw [add_neg_cancel, N.ψ_zero, map_one, fneg, Bnegr, mul_assoc, eq_comm, inv_mul_eq_one] at this
    rw [sq]
    exact this
  have Bsmul : ∀ (k : ℕ) a b, π (N.τ (k • a) b) = π (N.τ a b) ^ k := by
    intro k a b
    induction k with
    | zero => simp
    | succ k ih => rw [succ_nsmul, Bl, ih, pow_succ]
  have Bsmulr : ∀ (k : ℕ) a b, π (N.τ a (k • b)) = π (N.τ a b) ^ k := by
    intro k a b
    rw [N.τ_symm, Bsmul, N.τ_symm]
  have fsmul : ∀ (k : ℕ) a, π (N.ψ (k • a)) = π (N.ψ a) ^ (k ^ 2) := by
    intro k a
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul, fadd, ih, Bsmul, Bself, ← pow_mul, ← pow_add, ← pow_succ]
      congr 1
      ring
  have Sadd : ∀ χ χ', π (h.s (χ + χ')) = π (h.s χ) * π (h.s χ') := by
    intro χ χ'
    have := congrArg π (h.mult χ χ')
    rwa [map_mul, map_mul, θ1 _ (Hc χ) _ (Hc χ') _ Hb, mul_one] at this
  have Ssmul : ∀ (k : ℕ) a, π (h.s (k • a)) = π (h.s a) ^ k := by
    intro k a
    induction k with
    | zero => simp
    | succ k ih => rw [succ_nsmul, Sadd, ih, pow_succ]
  have Spow : π (h.s a) ^ m = π (N.τ a y) := by
    have := congrArg π (h.pow_s m a)
    rw [map_mul, map_pow, hy, GlobalTheory.Ex.NumD.io_s, N.τ_symm] at this
    have hc : π (cubN N.θ m 1 h.b (N.c a)) = 1 := by
      unfold cubN
      rw [map_prod]
      exact Finset.prod_eq_one fun i _ => θ1 _ (by rw [one_mul]; exact pow_mem Hb i) _ Hb _ (Hc a)
    rw [hc, mul_one] at this
    exact this.symm
  refine ⟨N.ψ (m • a + b) * h.s (m • a + b) / (N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b)), ?_, ?_⟩
  · have e : π (N.ψ (m • a + b) * h.s (m • a + b) / (N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b))) = 1 := by
      rw [map_div, div_eq_one, map_mul, map_mul, map_mul, map_mul, map_pow, fadd, Sadd, fsmul, Bsmul, Br, Bsmulr,
        Ssmul, Spow]
      ac_rfl
    exact ((Submonoid.mem_units_iff _ _).1 ((QuotientGroup.eq_one_iff _).1 e)).1
  · exact (fun (L X Y Z : Oˣ) => show L = L / (X * Y * Z) * X * Y * Z by
      rw [mul_assoc (L / (X * Y * Z)) X Y, mul_assoc (L / (X * Y * Z)) (X * Y) Z, div_mul_cancel]) _ _ _ _

end GlobalTheory
