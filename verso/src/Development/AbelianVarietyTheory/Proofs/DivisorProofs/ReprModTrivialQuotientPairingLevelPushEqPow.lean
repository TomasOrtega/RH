import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WpQTrivRight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SympQ.PushPow

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [cubN]`. Consider the case `succ n ih`. Establish `e : cubN θ ((n + 1) * m) 1 b x = cubN θ (n * m) 1 b x * cubN θ m (b ^ (n * m)) b x`. Rewrite using `[Nat.succ_mul]`.

Simplify using `only [cubN, Finset.prod_range_add]`. Use `congrArg _ (Finset.prod_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[_root_.one_mul, pow_add]`. Establish `s1 : cubN θ (n + 1) 1 (b ^ m) x = cubN θ n 1 (b ^ m) x * θ ((b ^ m) ^ n) (b ^ m) x`. Simplify using `only [cubN, Finset.prod_range_succ, _root_.one_mul]`.

Rewrite using `[e, ih, h.N_split m (b ^ (n * m)) b x, s1, ← pow_mul' b n m, pow_succ (cubN θ m 1 b x) n]`. The two sides agree by associativity and commutativity.
-/
theorem cubN_mul_iter (h : IsCub θ) (n m : ℕ) (b x : A) :
    cubN θ (n * m) 1 b x = cubN θ n 1 (b ^ m) x * cubN θ m 1 b x ^ n := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have e : cubN θ ((n + 1) * m) 1 b x = cubN θ (n * m) 1 b x * cubN θ m (b ^ (n * m)) b x := by
      rw [Nat.succ_mul]
      simp only [cubN, Finset.prod_range_add]
      refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
      rw [_root_.one_mul, pow_add]
    have s1 : cubN θ (n + 1) 1 (b ^ m) x = cubN θ n 1 (b ^ m) x * θ ((b ^ m) ^ n) (b ^ m) x := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    rw [e, ih, h.N_split m (b ^ (n * m)) b x, s1, ← pow_mul' b n m, pow_succ (cubN θ m 1 b x) n]
    ac_rfl

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [cubN, h.face₃]`. Consider the case `succ m ih`. Establish `e` using `h.N_add k 1 b (x ^ m) x`. Rewrite `e` using `[h.face, _root_.mul_one, _root_.one_mul]`.

Establish `s1 : cubN θ (m + 1) 1 x b = cubN θ m 1 x b * θ (x ^ m) x b`. Simplify using `only [cubN, Finset.prod_range_succ, _root_.one_mul]`. Establish `s2 : cubN θ (m + 1) 1 x (b ^ k) = cubN θ m 1 x (b ^ k) * θ (x ^ m) x (b ^ k)`. Simplify using `only [cubN, Finset.prod_range_succ, _root_.one_mul]`. Establish `t1 : θ b (x ^ m) x = θ (x ^ m) x b` using `by rw [h.s01, h.s12]`.

Establish `t2 : θ (b ^ k) (x ^ m) x = θ (x ^ m) x (b ^ k)` using `by rw [h.s01, h.s12]`. Rewrite `e` using `[t1, t2]`. Rewrite using `[pow_succ x, s1, s2]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Use `replace e := congrArg Additive.ofMul e`.

Use `replace ih := congrArg Additive.ofMul ih`. Simplify using `only [ofMul_mul, ofMul_pow] at e ih ⊢`. Take the linear combination `(norm := module) e + ih`.
-/
theorem cubN_pow_right (h : IsCub θ) (k m : ℕ) (b x : A) :
    cubN θ k 1 b (x ^ m) * cubN θ m 1 x b ^ k = cubN θ k 1 b x ^ m * cubN θ m 1 x (b ^ k) := by
  induction m with
  | zero => simp [cubN, h.face₃]
  | succ m ih =>
    have e := h.N_add k 1 b (x ^ m) x
    rw [h.face, _root_.mul_one, _root_.one_mul] at e
    have s1 : cubN θ (m + 1) 1 x b = cubN θ m 1 x b * θ (x ^ m) x b := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have s2 : cubN θ (m + 1) 1 x (b ^ k) = cubN θ m 1 x (b ^ k) * θ (x ^ m) x (b ^ k) := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have t1 : θ b (x ^ m) x = θ (x ^ m) x b := by rw [h.s01, h.s12]
    have t2 : θ (b ^ k) (x ^ m) x = θ (x ^ m) x (b ^ k) := by rw [h.s01, h.s12]
    rw [t1, t2] at e
    rw [pow_succ x, s1, s2]
    apply Additive.ofMul.injective
    replace e := congrArg Additive.ofMul e
    replace ih := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_pow] at e ih ⊢
    linear_combination (norm := module) e + ih

variable {O : Type} [CommRing O] (N : NumD O)

/- English proof (translation)
Establish `hd : n ∣ n * m` using `dvd_mul_right n m`. Establish `hM : n * m / n = m` using `Nat.mul_div_cancel_left m hn`. Simplify using `only [NumD.wp, NumD.tk, pushRep_fst N hd, pushRep_snd N hd, hM, NumD.Gt.pow_b]`. Establish `ps1` using `NumD.Gt.pow_s p.1.2 m q.1.1.toAdd`. Establish `ps2` using `NumD.Gt.pow_s q.1.2 m p.1.1.toAdd`.

Rewrite `ps1` using `[← N.QT_pow_b q]`. Rewrite `ps2` using `[← N.QT_pow_b p]`. Establish `i1` using `cubN_mul_iter N.cub n m q.1.2.b p.1.2.b`. Establish `i2` using `cubN_mul_iter N.cub n m p.1.2.b q.1.2.b`. Establish `a` using `cubN_pow_right N.cub n m (p.1.2.b ^ m) q.1.2.b`.

Establish `b` using `cubN_pow_right N.cub n m (q.1.2.b ^ m) p.1.2.b`. Establish `c` using `cubN_pow_right N.cub m m q.1.2.b p.1.2.b`. Rewrite `a`, `b` using `[← pow_mul']`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Use `replace ps1 := congrArg Additive.ofMul ps1`.

Use `replace ps2 := congrArg Additive.ofMul ps2`. Use `replace i1 := congrArg Additive.ofMul i1`. Use `replace i2 := congrArg Additive.ofMul i2`. Use `replace a := congrArg Additive.ofMul a`. Use `replace b := congrArg Additive.ofMul b`.

Use `replace c := congrArg Additive.ofMul c`. Simplify using `only [ofMul_mul, ofMul_div, ofMul_pow] at ps1 ps2 i1 i2 a b c ⊢`. Take the linear combination `(norm := module) ps1 - ps2 - (m : ℤ) • i1 + (m : ℤ) • i2 + b - a + (n : ℤ) • c`.
-/
theorem wp_pushRep (n m : ℕ) (hn : 0 < n) (p q : N.QT (n * m)) :
    N.wp (pushRep N (n * m) n p) (pushRep N (n * m) n q) = N.wp p q ^ m := by
  have hd : n ∣ n * m := dvd_mul_right n m
  have hM : n * m / n = m := Nat.mul_div_cancel_left m hn
  simp only [NumD.wp, NumD.tk, pushRep_fst N hd, pushRep_snd N hd, hM, NumD.Gt.pow_b]
  have ps1 := NumD.Gt.pow_s p.1.2 m q.1.1.toAdd
  have ps2 := NumD.Gt.pow_s q.1.2 m p.1.1.toAdd
  rw [← N.QT_pow_b q] at ps1
  rw [← N.QT_pow_b p] at ps2
  have i1 := cubN_mul_iter N.cub n m q.1.2.b p.1.2.b
  have i2 := cubN_mul_iter N.cub n m p.1.2.b q.1.2.b
  have a := cubN_pow_right N.cub n m (p.1.2.b ^ m) q.1.2.b
  have b := cubN_pow_right N.cub n m (q.1.2.b ^ m) p.1.2.b
  have c := cubN_pow_right N.cub m m q.1.2.b p.1.2.b
  rw [← pow_mul'] at a b
  apply Additive.ofMul.injective
  replace ps1 := congrArg Additive.ofMul ps1
  replace ps2 := congrArg Additive.ofMul ps2
  replace i1 := congrArg Additive.ofMul i1
  replace i2 := congrArg Additive.ofMul i2
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at ps1 ps2 i1 i2 a b c ⊢
  linear_combination (norm := module) ps1 - ps2 - (m : ℤ) • i1 + (m : ℤ) • i2 + b - a + (n : ℤ) • c

end GlobalTheory.SympQ.PushPow

/- English proof (translation)
Introduce `R _ _ _ _ D F _ _ _ N ν n m hn hm p q`. Conclude with `GlobalTheory.SympQ.PushPow.wp_pushRep N n m hn p q`.
-/
theorem GlobalTheory.SympQ.wp_pushRep_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n m : ℕ), 0 < n → 0 < m → ∀ p q : N.QT (n * m), N.wp (GlobalTheory.SympQ.pushRep N (n * m) n p) (GlobalTheory.SympQ.pushRep N (n * m) n q) = N.wp p q ^ m := by
  intro R _ _ _ _ D F _ _ _ N ν n m hn hm p q
  exact GlobalTheory.SympQ.PushPow.wp_pushRep N n m hn p q
