import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

namespace UpperTheory.Gal.FiniteEtaleModels

section Dv

variable {L : Type} [AddCommGroup L]

private def Dv (n : ℕ) (w : L) : Prop := ∃ z, w = n • z

/- English proof (translation)
Take `⟨z, rfl⟩` from `h`. Conclude with `⟨z, by abel⟩`.
-/
private theorem dv_of_eq {n : ℕ} {a b : L} (h : ∃ z, a = b + n • z) : Dv n (a - b) := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨z, by abel⟩

/- English proof (translation)
Take `⟨z, hz⟩` from `h`. Conclude with `⟨z, by rw [← hz]; abel⟩`.
-/
private theorem eq_of_dv {n : ℕ} {a b : L} (h : Dv n (a - b)) : ∃ z, a = b + n • z := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z, by rw [← hz]; abel⟩

/- English proof (translation)
Take `⟨z₁, rfl⟩` from `hv`. Take `⟨z₂, rfl⟩` from `hw`. Conclude with `⟨z₁ + z₂, by rw [smul_add]⟩`.
-/
private theorem Dv.add {n : ℕ} {v w : L} (hv : Dv n v) (hw : Dv n w) : Dv n (v + w) := by
  obtain ⟨z₁, rfl⟩ := hv
  obtain ⟨z₂, rfl⟩ := hw
  exact ⟨z₁ + z₂, by rw [smul_add]⟩

/- English proof (translation)
Take `⟨z₁, rfl⟩` from `hv`. Take `⟨z₂, rfl⟩` from `hw`. Conclude with `⟨z₁ - z₂, by rw [smul_sub]⟩`.
-/
private theorem Dv.sub {n : ℕ} {v w : L} (hv : Dv n v) (hw : Dv n w) : Dv n (v - w) := by
  obtain ⟨z₁, rfl⟩ := hv
  obtain ⟨z₂, rfl⟩ := hw
  exact ⟨z₁ - z₂, by rw [smul_sub]⟩

/- English proof (translation)
Take `⟨d, rfl⟩` from `h`. Take `⟨z, rfl⟩` from `hw`. Conclude with `⟨d • z, by rw [mul_smul]⟩`.
-/
private theorem Dv.of_dvd {n m : ℕ} {w : L} (h : n ∣ m) (hw : Dv m w) : Dv n w := by
  obtain ⟨d, rfl⟩ := h
  obtain ⟨z, rfl⟩ := hw
  exact ⟨d • z, by rw [mul_smul]⟩

/- English proof (translation)
Take `⟨d, rfl⟩` from `h`. Conclude with `⟨d • w, by rw [mul_smul, natCast_zsmul]⟩`.
-/
private theorem Dv.of_int {n : ℕ} {k : ℤ} (h : (n : ℤ) ∣ k) (w : L) : Dv n (k • w) := by
  obtain ⟨d, rfl⟩ := h
  exact ⟨d • w, by rw [mul_smul, natCast_zsmul]⟩

/- English proof (translation)
Take `⟨z, rfl⟩` from `h`. Conclude with `⟨k • z, by rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, mul_comm]⟩`.
-/
private theorem Dv.zsmul {n : ℕ} {w : L} (k : ℤ) (h : Dv n w) : Dv n (k • w) := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨k • z, by rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, mul_comm]⟩

/- English proof (translation)
Take `⟨z₁, h₁⟩` from `hP`. Take `⟨z₂, h₂⟩` from `hQ`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 h`. Establish `e₁ : w = (P : ℤ) • z₁` using `by rw [natCast_zsmul]; exact h₁`. Establish `e₂ : w = (Q : ℤ) • z₂` using `by rw [natCast_zsmul]; exact h₂`.

Use `⟨a • z₂ + b • z₁, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← natCast_zsmul]`. Use `push_cast`. Use `module`.
-/
private theorem Dv.comb {P Q : ℕ} {w : L} (h : Nat.Coprime P Q) (hP : Dv P w) (hQ : Dv Q w) : Dv (P * Q) w := by
  obtain ⟨z₁, h₁⟩ := hP
  obtain ⟨z₂, h₂⟩ := hQ
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e₁ : w = (P : ℤ) • z₁ := by rw [natCast_zsmul]; exact h₁
  have e₂ : w = (Q : ℤ) • z₂ := by rw [natCast_zsmul]; exact h₂
  refine ⟨a • z₂ + b • z₁, ?_⟩
  calc w = (a * P + b * Q : ℤ) • w := by rw [hab, one_smul]
    _ = a • ((P : ℤ) • w) + b • ((Q : ℤ) • w) := by rw [add_smul, mul_smul, mul_smul]
    _ = a • ((P : ℤ) • ((Q : ℤ) • z₂)) + b • ((Q : ℤ) • ((P : ℤ) • z₁)) := by rw [← e₂, ← e₁]
    _ = (P * Q) • (a • z₂ + b • z₁) := by
      rw [← natCast_zsmul]
      push_cast
      module

end Dv

/- English proof (translation)
Take `⟨t, ht⟩` from `hd`. Establish `hb : b = a + m * t` using `by rw [← ht]; ring`. Rewrite using `[hb]`. Conclude with `h.add_mul_left_left t`.
-/
private theorem isCoprime_of_dvd_sub {a b m : ℤ} (h : IsCoprime a m) (hd : m ∣ b - a) : IsCoprime b m := by
  obtain ⟨t, ht⟩ := hd
  have hb : b = a + m * t := by rw [← ht]; ring
  rw [hb]
  exact h.add_mul_left_left t

section Form

variable {G : GDatum}

/- English proof (translation)
Take `⟨z, rfl⟩` from `h`. Rewrite using `[map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]`. Conclude with `dvd_mul_right _ _`.
-/
private theorem dvd_EF_left {n : ℕ} {v : G.La} (h : Dv n v) (y : G.La) : (n : ℤ) ∣ G.EF v y := by
  obtain ⟨z, rfl⟩ := h
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  exact dvd_mul_right _ _

/- English proof (translation)
Take `⟨z, rfl⟩` from `h`. Rewrite using `[map_nsmul, nsmul_eq_mul]`. Conclude with `dvd_mul_right _ _`.
-/
private theorem dvd_EF_right {n : ℕ} {v : G.La} (h : Dv n v) (x : G.La) : (n : ℤ) ∣ G.EF x v := by
  obtain ⟨z, rfl⟩ := h
  rw [map_nsmul, nsmul_eq_mul]
  exact dvd_mul_right _ _

/- English proof (translation)
Establish `e : G.EF A B - G.EF A₀ B₀ = G.EF (A - A₀) B + G.EF A₀ (B - B₀)`. Simplify using `only [map_sub, LinearMap.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_add (dvd_EF_left hA B) (dvd_EF_right hB A₀)`.
-/
private theorem dvd_EF_sub {n : ℕ} {A A₀ B B₀ : G.La} (hA : Dv n (A - A₀)) (hB : Dv n (B - B₀)) :
    (n : ℤ) ∣ G.EF A B - G.EF A₀ B₀ := by
  have e : G.EF A B - G.EF A₀ B₀ = G.EF (A - A₀) B + G.EF A₀ (B - B₀) := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [e]
  exact dvd_add (dvd_EF_left hA B) (dvd_EF_right hB A₀)

end Form

/- English proof (translation)
Use `set f' : ℕ → G.La →+ G.La := fun n => (e₂ n * κ) • AddMonoidHom.id G.La + e₁ n • f (Q n)`. Use `set u' : ℕ → ℤ := fun n => e₂ n * c' + e₁ n * u (Q n)`. Establish `hf' : ∀ n x, f' n x = (e₂ n * κ) • x + e₁ n • f (Q n) x` using `fun n x => by simp [f']`. Rewrite `hs` using `[Sys.eq_1]`. Take `⟨s1, s2, s3, s4⟩` from `hs`.

Establish `he₂ : ∀ n, 0 < n → e₂ n = 1 - e₁ n` using `fun n hn => by linarith [he n hn]`. Establish `key : ∀ n, 0 < n → ∀ w : G.La, Dv (P n) w → Dv (Q n) w → Dv n w`. Introduce `n hn w h1 h2`. Use `Dv.comb (hcop n hn) h1 h2` as an intermediate fact. Rewrite `this` using `[hPQ n hn]`. Then use the resulting hypothesis.

Establish `keyZ : ∀ n, 0 < n → ∀ t : ℤ, (P n : ℤ) ∣ t → (Q n : ℤ) ∣ t → (n : ℤ) ∣ t`. Introduce `n hn t h1 h2`. Use `IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.2 (hcop n hn)) h1 h2` as an intermediate fact. Rewrite `this` using `[← Nat.cast_mul, hPQ n hn]`. Then use the resulting hypothesis. Establish `LP : ∀ n, 0 < n → ∀ x, Dv (P n) (f' n x - κ • x)`.

Introduce `n hn x`. Establish `e : f' n x - κ • x = e₁ n • (f (Q n) x - (κ : ℤ) • x)`. Rewrite using `[hf', he₂ n hn, ← natCast_zsmul]`. Use `module`. Rewrite using `[e]`.

Conclude with `Dv.of_int (hP n hn) _`. Establish `LQ : ∀ n, 0 < n → ∀ x, Dv (Q n) (f' n x - f (Q n) x)`. Introduce `n hn x`. Establish `e : f' n x - f (Q n) x = e₂ n • ((κ : ℤ) • x - f (Q n) x)`. Rewrite using `[hf', he₂ n hn]`.

Use `module`. Rewrite using `[e]`. Conclude with `Dv.of_int (hQ n hn) _`. Establish `UP : ∀ n, 0 < n → (P n : ℤ) ∣ u' n - c'`. Introduce `n hn`.

Establish `e : u' n - c' = e₁ n * (u (Q n) - c')`. Simplify using `only [u', he₂ n hn]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_mul_of_dvd_left (hP n hn) _`.

Establish `UQ : ∀ n, 0 < n → (Q n : ℤ) ∣ u' n - u (Q n)`. Introduce `n hn`. Establish `e : u' n - u (Q n) = e₂ n * (c' - u (Q n))`. Simplify using `only [u', he₂ n hn]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `dvd_mul_of_dvd_left (hQ n hn) _`. Use `⟨f', u', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Sys.eq_1]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `n hn _ a x`. Apply `eq_of_dv` to reduce the goal to its premises. Take `⟨z, hz⟩` from `s1 (Q n) (hQpos n hn) (hQp n hn) a x`. Establish `d : Dv (Q n) (f (Q n) (a • x) - a • f (Q n) x)` using `dv_of_eq ⟨z, hz⟩`. Establish `e : f' n (a • x) - a • f' n x = e₁ n • (f (Q n) (a • x) - a • f (Q n) x)`.

Rewrite using `[hf', hf', smul_add, smul_sub, smul_comm a (e₂ n * (κ : ℤ)) x, smul_comm a (e₁ n) (f (Q n) x)]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `key n hn _ (Dv.of_int (hP n hn) _) (Dv.zsmul _ d)`. Introduce `n m hn hm _`.

Establish `hnm : 0 < n * m` using `Nat.mul_pos hn hm`. Establish `hQnm : Q (n * m) = Q n * Q m` using `hQm n m hn hm`. Establish `hPd : P n ∣ P (n * m)`. Rewrite using `[hPm n m hn hm]`. Conclude with `dvd_mul_right _ _`.

Establish `hQd : Q n ∣ Q (n * m)`. Rewrite using `[hQnm]`. Conclude with `dvd_mul_right _ _`. Establish `cQ : (Q n * Q m).Coprime p` using `Nat.Coprime.mul (hQp n hn) (hQp m hm)`. Take `⟨s2a, s2b⟩` from `s2 (Q n) (Q m) (hQpos n hn) (hQpos m hm) cQ`.

Use `⟨fun x => eq_of_dv (key n hn _ ?_ ?_), keyZ n hn _ ?_ ?_⟩` and prove the remaining obligations. Establish `h` using `Dv.sub (Dv.of_dvd hPd (LP (n * m) hnm x)) (LP n hn x)`. Use `h using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Take `⟨z, hz⟩` from `s2a x`.

Establish `h1` using `Dv.of_dvd hQd (LQ (n * m) hnm x)`. Rewrite `h1` using `[hQnm]`. Establish `h2 : Dv (Q n) (f (Q n * Q m) x - f (Q n) x)` using `dv_of_eq ⟨z, hz⟩`. Establish `h` using `Dv.sub (Dv.add h1 h2) (LQ n hn x)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Normalize the expressions using the abelian group laws. Establish `h` using `dvd_sub (dvd_trans (Int.natCast_dvd_natCast.2 hPd) (UP _ hnm)) (UP n hn)`. Establish `e : u' (n * m) - u' n = (u' (n * m) - c') - (u' n - c')` using `by ring`. Rewrite using `[e]`. Conclude with `h`.

Establish `h1` using `dvd_trans (Int.natCast_dvd_natCast.2 hQd) (UQ _ hnm)`. Rewrite `h1` using `[hQnm]`. Establish `h` using `dvd_sub (dvd_add h1 s2b) (UQ n hn)`. Establish `e : u' (n * m) - u' n = (u' (n * m) - u (Q n * Q m)) + (u (Q n * Q m) - u (Q n)) - (u' n - u (Q n))` using `by ring`. Rewrite using `[e]`.

Conclude with `h`. Introduce `n hn _`. Take `⟨s3a, s3b⟩` from `s3 (Q n) (hQpos n hn) (hQp n hn)`. Use `⟨?_, fun x y => keyZ n hn _ ?_ ?_⟩` and prove the remaining obligations. Establish `hc1 : IsCoprime (u' n) (P n)` using `isCoprime_of_dvd_sub (hc' n hn) (UP n hn)`.

Establish `hc2 : IsCoprime (u' n) (Q n)` using `isCoprime_of_dvd_sub s3a (UQ n hn)`. Establish `h` using `hc1.mul_right hc2`. Rewrite `h` using `[← Nat.cast_mul, hPQ n hn]`. Then use the resulting hypothesis. Establish `hcc' : (c : ℤ) * c' = (κ : ℤ) ^ 2` using `by exact_mod_cast hcc`. Establish `hk : G.EF (κ • x) (κ • y) = (c : ℤ) * c' * G.EF x y`.

Rewrite using `[← natCast_zsmul, ← natCast_zsmul, LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, hcc']`. Expand and normalize the polynomial expressions, which then agree. Establish `t1` using `dvd_EF_sub (LP n hn x) (LP n hn y)`. Establish `t2 : (P n : ℤ) ∣ (c : ℤ) * (c' - u' n) * G.EF x y` using `Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_sub_comm.1 (UP n hn)) _) _`. Establish `e : G.EF (f' n x) (f' n y) - c * u' n * G.EF x y = (G.EF (f' n x) (f' n y) - G.EF (κ • x) (κ • y)) + (c : ℤ) * (c' - u' n) * G.EF x y`.

Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_add t1 t2`. Establish `t1` using `dvd_EF_sub (LQ n hn x) (LQ n hn y)`.

Establish `t3 : (Q n : ℤ) ∣ (c : ℤ) * (u (Q n) - u' n) * G.EF x y` using `Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_sub_comm.1 (UQ n hn)) _) _`. Establish `e : G.EF (f' n x) (f' n y) - c * u' n * G.EF x y = (G.EF (f' n x) (f' n y) - G.EF (f (Q n) x) (f (Q n) y)) + (G.EF (f (Q n) x) (f (Q n) y) - c * u (Q n) * G.EF x y) + (c : ℤ) * (u (Q n) - u' n) * G.EF x y` using `by ring`. Rewrite using `[e]`. Conclude with `dvd_add (dvd_add t1 (s3b x y)) t3`. Introduce `n hn _ x`.

Take `⟨y₀, z₀, hy⟩` from `s4 (Q n) (hQpos n hn) (hQp n hn) x`. Use `⟨e₁ n • y₀ + e₂ n • x, ?_⟩` and prove the remaining obligations. Apply `eq_of_dv` to reduce the goal to its premises. Apply `key n hn` to reduce the goal to its premises. Establish `h1` using `LP n hn (e₁ n • y₀ + e₂ n • x)`.

Establish `h2 : Dv (P n) (e₁ n • ((κ : ℤ) • (y₀ - x)))` using `Dv.of_int (hP n hn) _`. Use `Dv.add h1 h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[he₂ n hn, ← natCast_zsmul, ← natCast_zsmul]`. Use `module`. Establish `h1` using `LQ n hn (e₁ n • y₀ + e₂ n • x)`.

Establish `h2 : Dv (Q n) (e₂ n • f (Q n) (x - y₀))` using `Dv.of_int (hQ n hn) _`. Establish `h3 : Dv (Q n) (f (Q n) y₀ - κ • x)` using `dv_of_eq ⟨z₀, hy⟩`. Use `Dv.add (Dv.add h1 h2) h3 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_add, map_zsmul, map_sub, he₂ n hn]`. Use `module`.

Introduce `n hn hnp x`. Apply `eq_of_dv` to reduce the goal to its premises. Establish `h1` using `LQ n hn x`. Rewrite `h1` using `[hQn n hn hnp]`. Conclude with `h1`.
-/
private theorem sys_ext_of_split {G : GDatum} {p : ℕ} {f : ℕ → G.La →+ G.La} {u : ℕ → ℤ} {c c' κ : ℕ}
    (hcc : c * c' = κ ^ 2) (hs : Sys G p f u c κ) (P Q : ℕ → ℕ) (e₁ e₂ : ℕ → ℤ)
    (hPQ : ∀ n, 0 < n → P n * Q n = n) (hcop : ∀ n, 0 < n → Nat.Coprime (P n) (Q n))
    (he : ∀ n, 0 < n → e₁ n + e₂ n = 1) (hP : ∀ n, 0 < n → (P n : ℤ) ∣ e₁ n)
    (hQ : ∀ n, 0 < n → (Q n : ℤ) ∣ e₂ n) (hQpos : ∀ n, 0 < n → 0 < Q n)
    (hQp : ∀ n, 0 < n → (Q n).Coprime p)
    (hPm : ∀ n m, 0 < n → 0 < m → P (n * m) = P n * P m)
    (hQm : ∀ n m, 0 < n → 0 < m → Q (n * m) = Q n * Q m)
    (hc' : ∀ n, 0 < n → IsCoprime (c' : ℤ) (P n : ℤ))
    (hQn : ∀ n, 0 < n → n.Coprime p → Q n = n) :
    ∃ (f' : ℕ → G.La →+ G.La) (u' : ℕ → ℤ), Sys G 1 f' u' c κ ∧
      ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, f' n x = f n x + n • z := by
  set f' : ℕ → G.La →+ G.La := fun n => (e₂ n * κ) • AddMonoidHom.id G.La + e₁ n • f (Q n)
  set u' : ℕ → ℤ := fun n => e₂ n * c' + e₁ n * u (Q n)
  have hf' : ∀ n x, f' n x = (e₂ n * κ) • x + e₁ n • f (Q n) x := fun n x => by simp [f']
  rw [Sys.eq_1] at hs
  obtain ⟨s1, s2, s3, s4⟩ := hs
  have he₂ : ∀ n, 0 < n → e₂ n = 1 - e₁ n := fun n hn => by linarith [he n hn]
  have key : ∀ n, 0 < n → ∀ w : G.La, Dv (P n) w → Dv (Q n) w → Dv n w := by
    intro n hn w h1 h2
    have := Dv.comb (hcop n hn) h1 h2
    rwa [hPQ n hn] at this
  have keyZ : ∀ n, 0 < n → ∀ t : ℤ, (P n : ℤ) ∣ t → (Q n : ℤ) ∣ t → (n : ℤ) ∣ t := by
    intro n hn t h1 h2
    have := IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.2 (hcop n hn)) h1 h2
    rwa [← Nat.cast_mul, hPQ n hn] at this
  have LP : ∀ n, 0 < n → ∀ x, Dv (P n) (f' n x - κ • x) := by
    intro n hn x
    have e : f' n x - κ • x = e₁ n • (f (Q n) x - (κ : ℤ) • x) := by
      rw [hf', he₂ n hn, ← natCast_zsmul]
      module
    rw [e]
    exact Dv.of_int (hP n hn) _
  have LQ : ∀ n, 0 < n → ∀ x, Dv (Q n) (f' n x - f (Q n) x) := by
    intro n hn x
    have e : f' n x - f (Q n) x = e₂ n • ((κ : ℤ) • x - f (Q n) x) := by
      rw [hf', he₂ n hn]
      module
    rw [e]
    exact Dv.of_int (hQ n hn) _
  have UP : ∀ n, 0 < n → (P n : ℤ) ∣ u' n - c' := by
    intro n hn
    have e : u' n - c' = e₁ n * (u (Q n) - c') := by
      simp only [u', he₂ n hn]
      ring
    rw [e]
    exact dvd_mul_of_dvd_left (hP n hn) _
  have UQ : ∀ n, 0 < n → (Q n : ℤ) ∣ u' n - u (Q n) := by
    intro n hn
    have e : u' n - u (Q n) = e₂ n * (c' - u (Q n)) := by
      simp only [u', he₂ n hn]
      ring
    rw [e]
    exact dvd_mul_of_dvd_left (hQ n hn) _
  refine ⟨f', u', ?_, ?_⟩
  · rw [Sys.eq_1]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n hn _ a x
      apply eq_of_dv
      obtain ⟨z, hz⟩ := s1 (Q n) (hQpos n hn) (hQp n hn) a x
      have d : Dv (Q n) (f (Q n) (a • x) - a • f (Q n) x) := dv_of_eq ⟨z, hz⟩
      have e : f' n (a • x) - a • f' n x = e₁ n • (f (Q n) (a • x) - a • f (Q n) x) := by
        rw [hf', hf', smul_add, smul_sub, smul_comm a (e₂ n * (κ : ℤ)) x, smul_comm a (e₁ n) (f (Q n) x)]
        abel
      rw [e]
      exact key n hn _ (Dv.of_int (hP n hn) _) (Dv.zsmul _ d)
    · intro n m hn hm _
      have hnm : 0 < n * m := Nat.mul_pos hn hm
      have hQnm : Q (n * m) = Q n * Q m := hQm n m hn hm
      have hPd : P n ∣ P (n * m) := by
        rw [hPm n m hn hm]
        exact dvd_mul_right _ _
      have hQd : Q n ∣ Q (n * m) := by
        rw [hQnm]
        exact dvd_mul_right _ _
      have cQ : (Q n * Q m).Coprime p := Nat.Coprime.mul (hQp n hn) (hQp m hm)
      obtain ⟨s2a, s2b⟩ := s2 (Q n) (Q m) (hQpos n hn) (hQpos m hm) cQ
      refine ⟨fun x => eq_of_dv (key n hn _ ?_ ?_), keyZ n hn _ ?_ ?_⟩
      · have h := Dv.sub (Dv.of_dvd hPd (LP (n * m) hnm x)) (LP n hn x)
        convert h using 1
        abel
      · obtain ⟨z, hz⟩ := s2a x
        have h1 := Dv.of_dvd hQd (LQ (n * m) hnm x)
        rw [hQnm] at h1
        have h2 : Dv (Q n) (f (Q n * Q m) x - f (Q n) x) := dv_of_eq ⟨z, hz⟩
        have h := Dv.sub (Dv.add h1 h2) (LQ n hn x)
        convert h using 1
        abel
      · have h := dvd_sub (dvd_trans (Int.natCast_dvd_natCast.2 hPd) (UP _ hnm)) (UP n hn)
        have e : u' (n * m) - u' n = (u' (n * m) - c') - (u' n - c') := by ring
        rw [e]
        exact h
      · have h1 := dvd_trans (Int.natCast_dvd_natCast.2 hQd) (UQ _ hnm)
        rw [hQnm] at h1
        have h := dvd_sub (dvd_add h1 s2b) (UQ n hn)
        have e : u' (n * m) - u' n =
            (u' (n * m) - u (Q n * Q m)) + (u (Q n * Q m) - u (Q n)) - (u' n - u (Q n)) := by ring
        rw [e]
        exact h
    · intro n hn _
      obtain ⟨s3a, s3b⟩ := s3 (Q n) (hQpos n hn) (hQp n hn)
      refine ⟨?_, fun x y => keyZ n hn _ ?_ ?_⟩
      · have hc1 : IsCoprime (u' n) (P n) := isCoprime_of_dvd_sub (hc' n hn) (UP n hn)
        have hc2 : IsCoprime (u' n) (Q n) := isCoprime_of_dvd_sub s3a (UQ n hn)
        have h := hc1.mul_right hc2
        rwa [← Nat.cast_mul, hPQ n hn] at h
      · have hcc' : (c : ℤ) * c' = (κ : ℤ) ^ 2 := by exact_mod_cast hcc
        have hk : G.EF (κ • x) (κ • y) = (c : ℤ) * c' * G.EF x y := by
          rw [← natCast_zsmul, ← natCast_zsmul, LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul,
            smul_eq_mul, hcc']
          ring
        have t1 := dvd_EF_sub (LP n hn x) (LP n hn y)
        have t2 : (P n : ℤ) ∣ (c : ℤ) * (c' - u' n) * G.EF x y :=
          Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_sub_comm.1 (UP n hn)) _) _
        have e : G.EF (f' n x) (f' n y) - c * u' n * G.EF x y =
            (G.EF (f' n x) (f' n y) - G.EF (κ • x) (κ • y)) + (c : ℤ) * (c' - u' n) * G.EF x y := by
          rw [hk]
          ring
        rw [e]
        exact dvd_add t1 t2
      · have t1 := dvd_EF_sub (LQ n hn x) (LQ n hn y)
        have t3 : (Q n : ℤ) ∣ (c : ℤ) * (u (Q n) - u' n) * G.EF x y :=
          Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_sub_comm.1 (UQ n hn)) _) _
        have e : G.EF (f' n x) (f' n y) - c * u' n * G.EF x y =
            (G.EF (f' n x) (f' n y) - G.EF (f (Q n) x) (f (Q n) y)) +
              (G.EF (f (Q n) x) (f (Q n) y) - c * u (Q n) * G.EF x y) +
              (c : ℤ) * (u (Q n) - u' n) * G.EF x y := by ring
        rw [e]
        exact dvd_add (dvd_add t1 (s3b x y)) t3
    · intro n hn _ x
      obtain ⟨y₀, z₀, hy⟩ := s4 (Q n) (hQpos n hn) (hQp n hn) x
      refine ⟨e₁ n • y₀ + e₂ n • x, ?_⟩
      apply eq_of_dv
      apply key n hn
      · have h1 := LP n hn (e₁ n • y₀ + e₂ n • x)
        have h2 : Dv (P n) (e₁ n • ((κ : ℤ) • (y₀ - x))) := Dv.of_int (hP n hn) _
        convert Dv.add h1 h2 using 1
        rw [he₂ n hn, ← natCast_zsmul, ← natCast_zsmul]
        module
      · have h1 := LQ n hn (e₁ n • y₀ + e₂ n • x)
        have h2 : Dv (Q n) (e₂ n • f (Q n) (x - y₀)) := Dv.of_int (hQ n hn) _
        have h3 : Dv (Q n) (f (Q n) y₀ - κ • x) := dv_of_eq ⟨z₀, hy⟩
        convert Dv.add (Dv.add h1 h2) h3 using 1
        simp only [map_add, map_zsmul, map_sub, he₂ n hn]
        module
  · intro n hn hnp x
    apply eq_of_dv
    have h1 := LQ n hn x
    rw [hQn n hn hnp] at h1
    exact h1

end UpperTheory.Gal.FiniteEtaleModels

/- English proof (translation)
Rewrite using `[SysExt.eq_1]`. Introduce `G p hp f u c c' κ hcc hc'p hs`. Establish `cop : ∀ n, 0 < n → Nat.Coprime (p ^ n.factorization p) (n / p ^ n.factorization p)` using `fun n hn => Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn.ne')`. Use `sys_ext_of_split hcc hs (fun n => p ^ n.factorization p) (fun n => n / p ^ n.factorization p) (fun n => ((p ^ n.factorization p : ℕ) : ℤ) * Nat.gcdA (p ^ n.factorization p) (n / p ^ n.factorization p)) (fun n => ((n / p ^ n.factorization p : ℕ) : ℤ) * Nat.gcdB (p ^ n.factorizatio …` and prove the remaining obligations. Introduce `n _`.

Conclude with `Nat.ordProj_mul_ordCompl_eq_self n p`. Conclude with `cop`. Introduce `n hn`. Establish `h1` using `Nat.gcd_eq_gcd_ab (p ^ n.factorization p) (n / p ^ n.factorization p)`. Rewrite `h1` using `[Nat.Coprime.gcd_eq_one (cop n hn), Nat.cast_one]`.

Conclude with `h1.symm`. Introduce `n _`. Conclude with `dvd_mul_right _ _`. Introduce `n _`. Conclude with `dvd_mul_right _ _`.

Introduce `n hn`. Conclude with `Nat.ordCompl_pos p hn.ne'`. Introduce `n hn`. Conclude with `(Nat.coprime_ordCompl hp hn.ne').symm`. Introduce `n m hn hm`.

Conclude with `Nat.ordProj_mul p hn.ne' hm.ne'`. Introduce `n m _ _`. Conclude with `Nat.ordCompl_mul n m p`. Introduce `n _`. Conclude with `Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right _ hc'p)`.

Introduce `n _ hnp`. Establish `h0 : n.factorization p = 0` using `Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hnp.symm)`. Use `show n / p ^ n.factorization p = n`. Rewrite using `[h0, pow_zero, Nat.div_one]`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.sysExt_holds :
    SysExt := by
  rw [SysExt.eq_1]
  intro G p hp f u c c' κ hcc hc'p hs
  have cop : ∀ n, 0 < n → Nat.Coprime (p ^ n.factorization p) (n / p ^ n.factorization p) :=
    fun n hn => Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn.ne')
  refine sys_ext_of_split hcc hs (fun n => p ^ n.factorization p) (fun n => n / p ^ n.factorization p)
    (fun n => ((p ^ n.factorization p : ℕ) : ℤ) * Nat.gcdA (p ^ n.factorization p) (n / p ^ n.factorization p))
    (fun n => ((n / p ^ n.factorization p : ℕ) : ℤ) * Nat.gcdB (p ^ n.factorization p) (n / p ^ n.factorization p))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n _
    exact Nat.ordProj_mul_ordCompl_eq_self n p
  · exact cop
  · intro n hn
    have h1 := Nat.gcd_eq_gcd_ab (p ^ n.factorization p) (n / p ^ n.factorization p)
    rw [Nat.Coprime.gcd_eq_one (cop n hn), Nat.cast_one] at h1
    exact h1.symm
  · intro n _
    exact dvd_mul_right _ _
  · intro n _
    exact dvd_mul_right _ _
  · intro n hn
    exact Nat.ordCompl_pos p hn.ne'
  · intro n hn
    exact (Nat.coprime_ordCompl hp hn.ne').symm
  · intro n m hn hm
    exact Nat.ordProj_mul p hn.ne' hm.ne'
  · intro n m _ _
    exact Nat.ordCompl_mul n m p
  · intro n _
    exact Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right _ hc'p)
  · intro n _ hnp
    have h0 : n.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hnp.symm)
    show n / p ^ n.factorization p = n
    rw [h0, pow_zero, Nat.div_one]
