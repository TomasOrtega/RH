import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.Span

/- English proof (translation)
Use `choose ν hν using hd`. Establish `: d = N • ν` using `by funext i; simp [hν i]`. Rewrite using `[this, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Conclude with `dvd_mul_right _ _`.
-/
lemma dvd_apply_of_coord {r : ℕ} (N : ℤ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (d z : Fin r → ℤ)
    (hd : ∀ i, N ∣ d i) : N ∣ b d z := by
  choose ν hν using hd
  have : d = N • ν := by funext i; simp [hν i]
  rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

/- English proof (translation)
Use `set c : Fin s → Fin r → ZMod N := fun u i => (y u i : ZMod N)`. Establish `hd : ∀ u i, (N : ℤ) ∣ y u i - μ c u i`. Introduce `u i`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`.

Rewrite using `[hμ]`. Simplify using `[c]`. Establish `key : qW W b y = qW W b y - qW W b (μ c)` using `by rw [h0]; ring`. Rewrite using `[key, qW, qW, ← Finset.sum_sub_distrib]`. Use `Finset.dvd_sum fun u _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.dvd_sum fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_sub]`. Use `dvd_mul_of_dvd_right ?_ _` and prove the remaining obligations. Establish `e : b (y u) (y v) - b (μ c u) (μ c v) = b (y u - μ c u) (y v) + b (y v - μ c v) (μ c u)`.

Rewrite using `[hb (y v - μ c v) (μ c u)]`. Simplify using `only [map_sub, LinearMap.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_add (dvd_apply_of_coord _ b _ _ fun i => by simpa using hd u i) (dvd_apply_of_coord _ b _ _ fun i => by simpa using hd v i)`.
-/
lemma qW_dvd {s r : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (N : ℕ) [NeZero N]
    (μ : (Fin s → Fin r → ZMod N) → (Fin s → Fin r → ℤ)) (hμ : ∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i)
    (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hb : ∀ x y, b x y = b y x) (h0 : ∀ c, qW W b (μ c) = 0)
    (y : Fin s → Fin r → ℤ) : (N : ℤ) ∣ qW W b y := by
  set c : Fin s → Fin r → ZMod N := fun u i => (y u i : ZMod N)
  have hd : ∀ u i, (N : ℤ) ∣ y u i - μ c u i := by
    intro u i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hμ]; simp [c]
  have key : qW W b y = qW W b y - qW W b (μ c) := by rw [h0]; ring
  rw [key, qW, qW, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun u _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun v _ => ?_
  rw [← mul_sub]
  refine dvd_mul_of_dvd_right ?_ _
  have e : b (y u) (y v) - b (μ c u) (μ c v) = b (y u - μ c u) (y v) + b (y v - μ c v) (μ c u) := by
    rw [hb (y v - μ c v) (μ c u)]
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [e]
  exact dvd_add (dvd_apply_of_coord _ b _ _ fun i => by simpa using hd u i)
    (dvd_apply_of_coord _ b _ _ fun i => by simpa using hd v i)

/- English proof (translation)
Take `⟨ε, hε⟩` from `hε`. Use `set q := ∑ u, ∑ v, W u v * ε u * ε v with hq`. Establish `hcop : IsCoprime (N : ℤ) q`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`. Use `Nat.Coprime.coprime_mul_left_right hε` as an intermediate fact.

Simplify `this` using `[Int.gcd]`. Establish `h2 : IsCoprime (N : ℤ) 2`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`. Use `Nat.Coprime.coprime_mul_right_right hε` as an intermediate fact. Simplify `this` using `[Int.gcd]`.

Establish `hxx : ∀ x, (N : ℤ) ∣ b x x`. Introduce `x`. Establish `h` using `qW_dvd W N μ hμ b hb h0 (fun u => ε u • x)`. Establish `e : qW W b (fun u => ε u • x) = q * b x x`. Simplify using `only [qW, map_smul, LinearMap.smul_apply, smul_eq_mul, hq, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring`. Rewrite `h` using `[e]`. Conclude with `hcop.dvd_of_dvd_mul_left h`. Introduce `x z`. Establish `e : 2 * b x z = b (x + z) (x + z) - b x x - b z z`.

Simplify using `only [map_add, LinearMap.add_apply, hb z x]`. Expand and normalize the polynomial expressions, which then agree. Establish `h : (N : ℤ) ∣ 2 * b x z`. Rewrite using `[e]`. Conclude with `dvd_sub (dvd_sub (hxx _) (hxx x)) (hxx z)`.

Conclude with `h2.dvd_of_dvd_mul_left h`.
-/
lemma dvd_all {s r : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (N : ℕ) [NeZero N]
    (hε : ∃ ε : Fin s → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs))
    (μ : (Fin s → Fin r → ZMod N) → (Fin s → Fin r → ℤ)) (hμ : ∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i)
    (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hb : ∀ x y, b x y = b y x) (h0 : ∀ c, qW W b (μ c) = 0) :
    ∀ x z, (N : ℤ) ∣ b x z := by
  obtain ⟨ε, hε⟩ := hε
  set q := ∑ u, ∑ v, W u v * ε u * ε v with hq
  have hcop : IsCoprime (N : ℤ) q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Nat.Coprime.coprime_mul_left_right hε
    simpa [Int.gcd] using this
  have h2 : IsCoprime (N : ℤ) 2 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Nat.Coprime.coprime_mul_right_right hε
    simpa [Int.gcd] using this
  have hxx : ∀ x, (N : ℤ) ∣ b x x := by
    intro x
    have h := qW_dvd W N μ hμ b hb h0 (fun u => ε u • x)
    have e : qW W b (fun u => ε u • x) = q * b x x := by
      simp only [qW, map_smul, LinearMap.smul_apply, smul_eq_mul, hq, Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    rw [e] at h
    exact hcop.dvd_of_dvd_mul_left h
  intro x z
  have e : 2 * b x z = b (x + z) (x + z) - b x x - b z z := by
    simp only [map_add, LinearMap.add_apply, hb z x]
    ring
  have h : (N : ℤ) ∣ 2 * b x z := by
    rw [e]; exact dvd_sub (dvd_sub (hxx _) (hxx x)) (hxx z)
  exact h2.dvd_of_dvd_mul_left h

end GlobalTheory.Poinc.Span

namespace GlobalTheory.Poinc.Span

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intros`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `b hb h0 x z`.

Establish `hd` using `dvd_all W N hε μ hμ b hb h0`. Set `b' : LinearMap.BilinForm ℤ (Fin r → ℤ)` to `LinearMap.mk₂ ℤ (fun x z => b x z / N) (fun m₁ m₂ n => by simp only [map_add, LinearMap.add_apply, Int.add_ediv_of_dvd_left (hd m₁ n)]) (fun c m n => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Int.mul_ediv_assoc c (hd m n)]) (fun m n₁ n₂ => by simp only [map_add, …`. Establish `hbb : ∀ x z, b x z = N * b' x z` using `fun x z => by`. Simplify using `only [b', LinearMap.mk₂_apply]`. Conclude with `(Int.mul_ediv_cancel' (hd x z)).symm`.

Establish `hb' : ∀ x z, b' x z = b' z x` using `fun x z => by simp only [b', LinearMap.mk₂_apply, hb x z]`. Establish `h0' : ∀ c, qW W b' (μ c) = 0`. Introduce `c`. Establish `e : qW W b (μ c) = N * qW W b' (μ c)`. Simplify using `only [qW, hbb, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring`. Use `h0 c` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `(mul_eq_zero.mp this).resolve_left (by exact_mod_cast NeZero.ne N)`. Rewrite using `[hbb, pow_succ, mul_comm ((N : ℤ) ^ k)]`.

Conclude with `mul_dvd_mul_left _ (ih b' hb' h0' x z)`.
-/
lemma pow_dvd_all {s r : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (N : ℕ) [NeZero N]
    (hε : ∃ ε : Fin s → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs))
    (μ : (Fin s → Fin r → ZMod N) → (Fin s → Fin r → ℤ)) (hμ : ∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i)
    (k : ℕ) : ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ c, qW W b (μ c) = 0) →
      ∀ x z, (N : ℤ) ^ k ∣ b x z := by
  induction k with
  | zero => intros; simp
  | succ k ih =>
    intro b hb h0 x z
    have hd := dvd_all W N hε μ hμ b hb h0
    let b' : LinearMap.BilinForm ℤ (Fin r → ℤ) := LinearMap.mk₂ ℤ (fun x z => b x z / N)
      (fun m₁ m₂ n => by simp only [map_add, LinearMap.add_apply, Int.add_ediv_of_dvd_left (hd m₁ n)])
      (fun c m n => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Int.mul_ediv_assoc c (hd m n)])
      (fun m n₁ n₂ => by simp only [map_add, Int.add_ediv_of_dvd_left (hd m n₁)])
      (fun c m n => by simp only [map_smul, smul_eq_mul, Int.mul_ediv_assoc c (hd m n)])
    have hbb : ∀ x z, b x z = N * b' x z := fun x z => by
      simp only [b', LinearMap.mk₂_apply]; exact (Int.mul_ediv_cancel' (hd x z)).symm
    have hb' : ∀ x z, b' x z = b' z x := fun x z => by simp only [b', LinearMap.mk₂_apply, hb x z]
    have h0' : ∀ c, qW W b' (μ c) = 0 := by
      intro c
      have e : qW W b (μ c) = N * qW W b' (μ c) := by
        simp only [qW, hbb, Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
      have := h0 c
      rw [e] at this
      exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast NeZero.ne N)
    rw [hbb, pow_succ, mul_comm ((N : ℤ) ^ k)]
    exact mul_dvd_mul_left _ (ih b' hb' h0' x z)

end GlobalTheory.Poinc.Span

/- English proof (translation)
Introduce `W _ N _ hN r hε μ hμ b hb h0`. Use `LinearMap.ext₂ fun x z => ?_` and prove the remaining obligations. Establish `h` using `GlobalTheory.Poinc.Span.pow_dvd_all W N hε μ hμ (b x z).natAbs b hb h0 x z`. Simplify using `only [LinearMap.zero_apply]`. Use `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_` and prove the remaining obligations.

Rewrite using `[Int.natAbs_pow, Int.natAbs_natCast]`. Conclude with `Nat.lt_pow_self (by omega)`.
-/
theorem GlobalTheory.Poinc.symm_eq_zero_of_qW_lifts :
    ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ,
      (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) →
      ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) →
      ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ c, qW W b (μ c) = 0) → b = 0 := by
  intro W _ N _ hN r hε μ hμ b hb h0
  refine LinearMap.ext₂ fun x z => ?_
  have h := GlobalTheory.Poinc.Span.pow_dvd_all W N hε μ hμ (b x z).natAbs b hb h0 x z
  simp only [LinearMap.zero_apply]
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)
