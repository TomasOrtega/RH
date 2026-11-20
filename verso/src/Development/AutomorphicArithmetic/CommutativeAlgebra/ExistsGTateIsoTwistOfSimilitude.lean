import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.LevDefs

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen UpperTheory.Lev

namespace UpperTheory.Lev

section Twist

variable {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q}
  {e : ℕ → Q → Q → kˣ → Prop}

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Rewrite using `[I.add, (I.ker n hn (n • c)).2 ⟨c, rfl⟩, _root_.mul_one]`.
-/
private theorem ev_MN (I : GTateIso G k Q act e) {n : ℕ} (hn : 0 < n) {a b : G.La} (h : MN n a b) :
    I.ev n a = I.ev n b := by
  obtain ⟨c, rfl⟩ := h
  rw [I.add, (I.ker n hn (n • c)).2 ⟨c, rfl⟩, _root_.mul_one]

/- English proof (translation)
Take `⟨c, hc⟩` from `h`. Establish `hab : a = b + n * c` using `by linarith`. Rewrite using `[hab, zpow_add, zpow_mul, zpow_natCast, hu, one_zpow, _root_.mul_one]`.
-/
private theorem zpow_congr_of_dvd {u : kˣ} {n : ℕ} (hu : u ^ n = 1) {a b : ℤ} (h : (n : ℤ) ∣ a - b) :
    u ^ a = u ^ b := by
  obtain ⟨c, hc⟩ := h
  have hab : a = b + n * c := by linarith
  rw [hab, zpow_add, zpow_mul, zpow_natCast, hu, one_zpow, _root_.mul_one]

/- English proof (translation)
Conclude with `hu.zpow_of_gcd_eq_one v (Int.isCoprime_iff_gcd_eq_one.mp hc)`.
-/
private theorem prim_zpow {u : kˣ} {n : ℕ} (hu : IsPrimitiveRoot u n) {v : ℤ}
    (hc : IsCoprime v (n : ℤ)) : IsPrimitiveRoot (u ^ v) n := by
  exact hu.zpow_of_gcd_eq_one v (Int.isCoprime_iff_gcd_eq_one.mp hc)

end Twist

end UpperTheory.Lev

/- English proof (translation)
Introduce `G k _ Q _ act e I g`. Establish `hφadd : ∀ n, 0 < n → ∀ x y, I.ev n (g.f n (x + y)) = I.ev n (g.f n x) * I.ev n (g.f n y)` using `fun n hn x y => by rw [Lev.ev_MN I hn ((g.sim n hn).add x y), I.add]`. Establish `hφpow : ∀ n, 0 < n → ∀ (j : ℕ) y, I.ev n (g.f n (j • y)) = I.ev n (g.f n y) ^ j`. Introduce `n hn j y`. Proceed by induction on `j with`.

Consider the case `zero`. Rewrite using `[zero_smul, pow_zero]`. Establish `h0` using `hφadd n hn 0 0`. Rewrite `h0` using `[add_zero]`. Conclude with `(mul_eq_left.mp h0.symm)`.

Consider the case `succ j ih => rw [succ_nsmul, hφadd n hn, ih, pow_succ]`. Use `⟨⟨fun n => I.ζ n ^ g.ν n, ?_, ?_, fun n x => if n = 0 then I.ev 0 x else I.ev n (g.f n x), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `n hn`. Conclude with `Lev.prim_zpow (I.ζ_prim n hn) (g.sim n hn).cop`. Introduce `n m hn hm`.

Rewrite using `[← zpow_natCast, ← zpow_mul, mul_comm (g.ν _), zpow_mul, zpow_natCast, I.ζ_pow n m hn hm]`. Conclude with `Lev.zpow_congr_of_dvd (I.ζ_prim n hn).pow_eq_one (g.νtower n m hn hm)`. Introduce `n x y`. Distinguish the cases in `hn : n = 0`. Simplify using `only [hn, if_true, I.add]`.

Simplify using `only [hn, if_false]`. Conclude with `hφadd n (Nat.pos_of_ne_zero hn) x y`. Introduce `n b x`. Distinguish the cases in `hn : n = 0`. Simplify using `only [hn, if_true, I.lin]`.

Simplify using `only [hn, if_false]`. Rewrite using `[Lev.ev_MN I (Nat.pos_of_ne_zero hn) ((g.sim n (Nat.pos_of_ne_zero hn)).lin b x), I.lin]`. Introduce `n hn x`. Simplify using `only [hn.ne', if_false]`. Prove the components needed by the constructor for the conclusion.

Introduce `h1`. Take `⟨y, hy⟩` from `(I.ker n hn _).mp h1`. Take `⟨c, hc⟩` from `(g.sim n hn).inj x ⟨y, by rw [hy, zero_add]⟩`. Conclude with `⟨c, by rw [hc, zero_add]⟩`. Introduce and unpack `⟨y, rfl⟩`.

Rewrite using `[hφpow n hn]`. Conclude with `(I.onto n hn _).mpr ⟨_, rfl⟩`. Introduce `n hn q`. Simplify using `only [hn.ne', if_false]`. Rewrite using `[I.onto n hn]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Take `⟨x, hx⟩` from `(g.sim n hn).surj z`. Conclude with `⟨x, Lev.ev_MN I hn hx⟩`. Introduce and unpack `⟨x, rfl⟩`.

Conclude with `⟨_, rfl⟩`. Introduce `n m hn hm x`. Simplify using `only [(Nat.mul_pos hn hm).ne', hn.ne', if_false]`. Rewrite using `[I.tower n m hn hm, Lev.ev_MN I hn (g.tower n m hn hm x)]`. Introduce `n hn x y`.

Simplify using `only [hn.ne', if_false]`. Establish `h` using `I.isom n hn (g.f n x) (g.f n y)`. Establish `hd` using `((g.sim n hn).isom x y)`. Rewrite `h` using `[Lev.zpow_congr_of_dvd (I.ζ_prim n hn).pow_eq_one hd]`. Rewrite using `[← zpow_mul]`.

Conclude with `h`. Introduce `n hn x`. Simplify using `only [hn.ne', if_false]`.
-/
theorem UpperTheory.exists_gTateIso_twist_of_similitude :
    ∀ {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
        (I : GTateIso G k Q act e) (g : GSim G),
        ∃ I' : GTateIso G k Q act e, ∀ n, 0 < n → ∀ x, I'.ev n x = I.ev n (g.f n x) := by
  intro G k _ Q _ act e I g
  have hφadd : ∀ n, 0 < n → ∀ x y, I.ev n (g.f n (x + y)) = I.ev n (g.f n x) * I.ev n (g.f n y) :=
    fun n hn x y => by rw [Lev.ev_MN I hn ((g.sim n hn).add x y), I.add]
  have hφpow : ∀ n, 0 < n → ∀ (j : ℕ) y, I.ev n (g.f n (j • y)) = I.ev n (g.f n y) ^ j := by
    intro n hn j y
    induction j with
    | zero =>
      rw [zero_smul, pow_zero]
      have h0 := hφadd n hn 0 0
      rw [add_zero] at h0
      exact (mul_eq_left.mp h0.symm)
    | succ j ih => rw [succ_nsmul, hφadd n hn, ih, pow_succ]
  refine ⟨⟨fun n => I.ζ n ^ g.ν n, ?_, ?_, fun n x => if n = 0 then I.ev 0 x else I.ev n (g.f n x),
    ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n hn
    exact Lev.prim_zpow (I.ζ_prim n hn) (g.sim n hn).cop
  · intro n m hn hm
    rw [← zpow_natCast, ← zpow_mul, mul_comm (g.ν _), zpow_mul, zpow_natCast, I.ζ_pow n m hn hm]
    exact Lev.zpow_congr_of_dvd (I.ζ_prim n hn).pow_eq_one (g.νtower n m hn hm)
  · intro n x y
    by_cases hn : n = 0
    · simp only [hn, if_true, I.add]
    · simp only [hn, if_false]
      exact hφadd n (Nat.pos_of_ne_zero hn) x y
  · intro n b x
    by_cases hn : n = 0
    · simp only [hn, if_true, I.lin]
    · simp only [hn, if_false]
      rw [Lev.ev_MN I (Nat.pos_of_ne_zero hn) ((g.sim n (Nat.pos_of_ne_zero hn)).lin b x), I.lin]
  · intro n hn x
    simp only [hn.ne', if_false]
    constructor
    · intro h1
      obtain ⟨y, hy⟩ := (I.ker n hn _).mp h1
      obtain ⟨c, hc⟩ := (g.sim n hn).inj x ⟨y, by rw [hy, zero_add]⟩
      exact ⟨c, by rw [hc, zero_add]⟩
    · rintro ⟨y, rfl⟩
      rw [hφpow n hn]
      exact (I.onto n hn _).mpr ⟨_, rfl⟩
  · intro n hn q
    simp only [hn.ne', if_false]
    rw [I.onto n hn]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, hx⟩ := (g.sim n hn).surj z
      exact ⟨x, Lev.ev_MN I hn hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  · intro n m hn hm x
    simp only [(Nat.mul_pos hn hm).ne', hn.ne', if_false]
    rw [I.tower n m hn hm, Lev.ev_MN I hn (g.tower n m hn hm x)]
  · intro n hn x y
    simp only [hn.ne', if_false]
    have h := I.isom n hn (g.f n x) (g.f n y)
    have hd := ((g.sim n hn).isom x y)
    rw [Lev.zpow_congr_of_dvd (I.ζ_prim n hn).pow_eq_one hd] at h
    rw [← zpow_mul]
    exact h
  · intro n hn x
    simp only [hn.ne', if_false]
