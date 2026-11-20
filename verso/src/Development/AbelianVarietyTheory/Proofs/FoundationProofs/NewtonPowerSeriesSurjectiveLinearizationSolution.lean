import Mathlib

open Polynomial

namespace GlobalTheory

/- English proof (translation)
Set `r` to `Function.surjInv hL`. Establish `hLr : ∀ v, L (r v) = v` using `Function.surjInv_eq hL`. Set `step : ℕ → (ι → PowerSeries k) → (ι → PowerSeries k)` to `fun m x i => x i + PowerSeries.X ^ m * PowerSeries.C (r (fun e => -PowerSeries.coeff m (G x e)) i)`. Set `sq : ℕ → (ι → PowerSeries k)` to `fun n => Nat.rec (motive := fun _ => ι → PowerSeries k) (fun i => PowerSeries.C (x₀ i)) (fun n x => step (n + 1) x) n`. Establish `sq_zero : sq 0 = fun i => PowerSeries.C (x₀ i)` using `rfl`.

Establish `sq_succ : ∀ n, sq (n + 1) = step (n + 1) (sq n)` using `fun n => rfl`. Establish `coeffXC : ∀ (m j : ℕ) (c : k), PowerSeries.coeff j ((PowerSeries.X : PowerSeries k) ^ m * PowerSeries.C c) = if j = m then c else 0`. Introduce `m j c`. Rewrite using `[mul_comm, PowerSeries.coeff_C_mul_X_pow]`. Establish `inv : ∀ n, (∀ i, PowerSeries.constantCoeff (sq n i) = x₀ i) ∧ ∀ e, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G (sq n) e`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Use `⟨fun i => by simp [sq_zero], fun e => ?_⟩` and prove the remaining obligations. Rewrite using `[zero_add, pow_one, PowerSeries.X_dvd_iff, sq_zero]`.

Conclude with `h0 e`. Consider the case `succ n ih`. Establish `hc : ∀ i, PowerSeries.constantCoeff (sq (n + 1) i) = x₀ i`. Introduce `i`. Simplify using `[sq_succ, step, ih.1 i]`.

Use `⟨hc, fun e => ?_⟩` and prove the remaining obligations. Use `set x := sq n with hx`. Use `set v : κ → k := fun e => -PowerSeries.coeff (n + 1) (G x e) with hv`. Establish `key` using `hG x (fun i => PowerSeries.C (r v i)) (n + 1) (by omega) ih.1 e`. Establish `hcv : (fun i => PowerSeries.constantCoeff (PowerSeries.C (r v i))) = r v`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite `key` using `[hcv, hLr]`. Establish `hs : sq (n + 1) = fun i => x i + PowerSeries.X ^ (n + 1) * PowerSeries.C (r v i)`. Rewrite using `[sq_succ]`.

Establish `h2 : (PowerSeries.X : PowerSeries k) ^ (n + 1 + 1) ∣ G x e + PowerSeries.X ^ (n + 1) * PowerSeries.C (v e)`. Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `j hj`. Rewrite using `[map_add, coeffXC]`. Break down `Nat.lt_or_ge j (n + 1) with hj' | hj'` into its components or cases.

Use `(PowerSeries.X_pow_dvd_iff.mp (ih.2 e)) j hj'` as an intermediate fact. Rewrite using `[this, if_neg (by omega), add_zero]`. Establish `hjn : j = n + 1` using `by omega`. Substitute `hjn` using the available equality. Simplify using `[hv]`.

Use `dvd_add key h2` as an intermediate fact. Rewrite using `[hs]`. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `stab : ∀ i j n, j ≤ n → PowerSeries.coeff j (sq n i) = PowerSeries.coeff j (sq j i)`.

Introduce `i j n hjn`. Proceed by induction on `n, hjn using Nat.le_induction with`. Consider the case `base => rfl`. Consider the case `succ n hjn ihn`. Rewrite using `[← ihn, sq_succ]`.

Simplify using `only [step, map_add]`. Rewrite using `[coeffXC, if_neg (by omega), add_zero]`. Set `xl : ι → PowerSeries k` to `fun i => PowerSeries.mk (fun j => PowerSeries.coeff j (sq j i))`. Establish `hdiff : ∀ n i, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ xl i - sq n i`. Introduce `n i`.

Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `j hj`. Simplify using `only [xl, map_sub, PowerSeries.coeff_mk]`. Rewrite using `[stab i j n (by omega), sub_self]`. Establish `hlim : ∀ n e, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G xl e`.

Introduce `n e`. Use `choose d hd using hdiff n`. Establish `hx : xl = fun i => sq n i + PowerSeries.X ^ (n + 1) * d i`. Use function extensionality and compare the values at `i`. Rewrite using `[← hd i]`.

Expand and normalize the polynomial expressions, which then agree. Establish `key` using `hG (sq n) d (n + 1) (by omega) (inv n).1 e`. Rewrite `key` using `[← hx]`. Establish `k1 : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G xl e - G (sq n) e`. Establish `h3 : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ (PowerSeries.X : PowerSeries k) ^ (n + 1 + 1)` using `pow_dvd_pow _ (by omega)`.

Use `dvd_add (h3.trans key) (dvd_mul_right ((PowerSeries.X : PowerSeries k) ^ (n + 1)) (PowerSeries.C (L (fun i => PowerSeries.constantCoeff (d i)) e)))` as an intermediate fact. Simplify using `using this`. Use `dvd_add k1 ((inv n).2 e)` as an intermediate fact. Simplify using `using this`. Use `⟨xl, fun i => ?_, fun e => ?_⟩` and prove the remaining obligations.

Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Simplify using `only [xl, PowerSeries.coeff_mk]`. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `(inv 0).1 i`. Use extensionality with `j`.

Rewrite using `[map_zero]`. Conclude with `PowerSeries.X_pow_dvd_iff.mp (hlim j e) j (by omega)`.
-/
theorem newton_powerSeries_of_surjective_linearisation (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ]
    (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k))
    (hL : Function.Surjective L)
    (h0 : ∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0)
    (hG : ∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
      (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e -
        PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) :
    ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 := by
  classical
  let r := Function.surjInv hL
  have hLr : ∀ v, L (r v) = v := Function.surjInv_eq hL
  let step : ℕ → (ι → PowerSeries k) → (ι → PowerSeries k) := fun m x i =>
    x i + PowerSeries.X ^ m * PowerSeries.C (r (fun e => -PowerSeries.coeff m (G x e)) i)
  let sq : ℕ → (ι → PowerSeries k) := fun n =>
    Nat.rec (motive := fun _ => ι → PowerSeries k) (fun i => PowerSeries.C (x₀ i)) (fun n x => step (n + 1) x) n
  have sq_zero : sq 0 = fun i => PowerSeries.C (x₀ i) := rfl
  have sq_succ : ∀ n, sq (n + 1) = step (n + 1) (sq n) := fun n => rfl
  have coeffXC : ∀ (m j : ℕ) (c : k),
      PowerSeries.coeff j ((PowerSeries.X : PowerSeries k) ^ m * PowerSeries.C c) = if j = m then c else 0 := by
    intro m j c
    rw [mul_comm, PowerSeries.coeff_C_mul_X_pow]
  have inv : ∀ n, (∀ i, PowerSeries.constantCoeff (sq n i) = x₀ i) ∧
      ∀ e, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G (sq n) e := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun i => by simp [sq_zero], fun e => ?_⟩
      rw [zero_add, pow_one, PowerSeries.X_dvd_iff, sq_zero]
      exact h0 e
    | succ n ih =>
      have hc : ∀ i, PowerSeries.constantCoeff (sq (n + 1) i) = x₀ i := by
        intro i
        simp [sq_succ, step, ih.1 i]
      refine ⟨hc, fun e => ?_⟩
      set x := sq n with hx
      set v : κ → k := fun e => -PowerSeries.coeff (n + 1) (G x e) with hv
      have key := hG x (fun i => PowerSeries.C (r v i)) (n + 1) (by omega) ih.1 e
      have hcv : (fun i => PowerSeries.constantCoeff (PowerSeries.C (r v i))) = r v := by
        funext i; simp
      rw [hcv, hLr] at key
      have hs : sq (n + 1) = fun i => x i + PowerSeries.X ^ (n + 1) * PowerSeries.C (r v i) := by
        rw [sq_succ]
      have h2 : (PowerSeries.X : PowerSeries k) ^ (n + 1 + 1) ∣
          G x e + PowerSeries.X ^ (n + 1) * PowerSeries.C (v e) := by
        rw [PowerSeries.X_pow_dvd_iff]
        intro j hj
        rw [map_add, coeffXC]
        rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
        · have := (PowerSeries.X_pow_dvd_iff.mp (ih.2 e)) j hj'
          rw [this, if_neg (by omega), add_zero]
        · have hjn : j = n + 1 := by omega
          subst hjn
          simp [hv]
      have := dvd_add key h2
      rw [hs]
      convert this using 1
      ring
  have stab : ∀ i j n, j ≤ n → PowerSeries.coeff j (sq n i) = PowerSeries.coeff j (sq j i) := by
    intro i j n hjn
    induction n, hjn using Nat.le_induction with
    | base => rfl
    | succ n hjn ihn =>
      rw [← ihn, sq_succ]
      simp only [step, map_add]
      rw [coeffXC, if_neg (by omega), add_zero]
  let xl : ι → PowerSeries k := fun i => PowerSeries.mk (fun j => PowerSeries.coeff j (sq j i))
  have hdiff : ∀ n i, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ xl i - sq n i := by
    intro n i
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    simp only [xl, map_sub, PowerSeries.coeff_mk]
    rw [stab i j n (by omega), sub_self]
  have hlim : ∀ n e, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G xl e := by
    intro n e
    choose d hd using hdiff n
    have hx : xl = fun i => sq n i + PowerSeries.X ^ (n + 1) * d i := by
      funext i; rw [← hd i]; ring
    have key := hG (sq n) d (n + 1) (by omega) (inv n).1 e
    rw [← hx] at key
    have k1 : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G xl e - G (sq n) e := by
      have h3 : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ (PowerSeries.X : PowerSeries k) ^ (n + 1 + 1) :=
        pow_dvd_pow _ (by omega)
      have := dvd_add (h3.trans key) (dvd_mul_right ((PowerSeries.X : PowerSeries k) ^ (n + 1))
        (PowerSeries.C (L (fun i => PowerSeries.constantCoeff (d i)) e)))
      simpa using this
    have := dvd_add k1 ((inv n).2 e)
    simpa using this
  refine ⟨xl, fun i => ?_, fun e => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [xl, PowerSeries.coeff_mk]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (inv 0).1 i
  · ext j
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.mp (hlim j e) j (by omega)

/- English proof (translation)
Introduce `k ι κ _ _ _ G x₀ L hL h0 hG` and use `newton_powerSeries_of_surjective_linearisation k ι κ G x₀ L hL h0 hG`.
-/
theorem newton_powerSeries_target : ∀ (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ] (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k)), Function.Surjective L →
 (∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0) →
 (∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
   (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e - PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) →
 ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 :=
  fun k ι κ _ _ _ G x₀ L hL h0 hG => newton_powerSeries_of_surjective_linearisation k ι κ G x₀ L hL h0 hG

end GlobalTheory
