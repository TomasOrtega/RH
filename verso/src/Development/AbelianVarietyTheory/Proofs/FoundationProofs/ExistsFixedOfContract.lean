import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GenusOneDatum

open PowerSeries in

/- English proof (translation)
Establish `hit : ∀ (n : ℕ) (x y : PowerSeries R), X ^ n ∣ T^[n] x - T^[n] y`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Introduce `x y`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply']`. Conclude with `hT n _ _ (ih x y)`. Set `L : PowerSeries R` to `PowerSeries.mk fun n => coeff n (T^[n + 1] 0)`. Establish `hL : ∀ n, X ^ n ∣ L - T^[n] 0`.

Introduce `n`. Rewrite using `[X_pow_dvd_iff]`. Introduce `m hm`. Take `⟨k, rfl⟩ : ∃ k, n = (m + 1) + k` from `⟨n - (m + 1), by omega⟩`. Use `X_pow_dvd_iff.1 (hit (m + 1) 0 (T^[k] 0)) m (by omega)` as an intermediate fact.

Rewrite `this` using `[← Function.iterate_add_apply]`. Simplify `this` using `[L]`. Use `⟨L, ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Establish `h1` using `hT n _ _ (hL n)`.

Establish `h2` using `hL (n + 1)`. Rewrite `h2` using `[Function.iterate_succ_apply']`. Establish `h3` using `dvd_sub h1 h2`. Establish `h4` using `X_pow_dvd_iff.1 h3 n (by omega)`. Rewrite `h4` using `[sub_sub_sub_cancel_right, map_sub, sub_eq_zero]`.

Conclude with `h4`.
-/
theorem exists_fixed_of_contract {R : Type*} [CommRing R] (T : PowerSeries R → PowerSeries R)
    (hT : ∀ (n : ℕ) (x y : PowerSeries R), X ^ n ∣ x - y → X ^ (n + 1) ∣ T x - T y) :
    ∃ x, T x = x := by
  have hit : ∀ (n : ℕ) (x y : PowerSeries R), X ^ n ∣ T^[n] x - T^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hT n _ _ (ih x y)
  let L : PowerSeries R := PowerSeries.mk fun n => coeff n (T^[n + 1] 0)
  have hL : ∀ n, X ^ n ∣ L - T^[n] 0 := by
    intro n
    rw [X_pow_dvd_iff]
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, n = (m + 1) + k := ⟨n - (m + 1), by omega⟩
    have := X_pow_dvd_iff.1 (hit (m + 1) 0 (T^[k] 0)) m (by omega)
    rw [← Function.iterate_add_apply] at this
    simpa [L] using this
  refine ⟨L, ?_⟩
  ext n
  have h1 := hT n _ _ (hL n)
  have h2 := hL (n + 1)
  rw [Function.iterate_succ_apply'] at h2
  have h3 := dvd_sub h1 h2
  have h4 := X_pow_dvd_iff.1 h3 n (by omega)
  rw [sub_sub_sub_cancel_right, map_sub, sub_eq_zero] at h4
  exact h4

/- English proof (translation)
Set `c` to `algebraMap ℂ_[p] (PowerSeries ℂ_[p])`. Set `X` to `(PowerSeries.X : PowerSeries ℂ_[p])`. Take `⟨w, hw⟩` from `exists_fixed_of_contract (fun wq : PowerSeries ℂ_[p] => 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 + c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3) (by`. Introduce and unpack `n x y ⟨z, hz⟩`. Use `⟨z * (c W.a₁ + c W.a₂ * X + (c W.a₃ * X ^ 2 + c W.a₄ * X ^ 3) * (x + y) + c W.a₆ * X ^ 5 * (x ^ 2 + x * y + y ^ 2)), ?_⟩` and prove the remaining obligations.

Establish `hz' : x - y = X ^ n * z` using `hz`. Express the relevant statement in the definitionally equal form `_ = X ^ (n + 1) * _`. Take the linear combination `(X * (c W.a₁ + c W.a₂ * X + (c W.a₃ * X ^ 2 + c W.a₄ * X ^ 3) * (x + y) + c W.a₆ * X ^ 5 * (x ^ 2 + x * y + y ^ 2))) * hz')`. Conclude with `⟨w, hw.symm⟩`.
-/
theorem exists_isWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) : ∃ wq, IsWq W wq := by
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  obtain ⟨w, hw⟩ := exists_fixed_of_contract (fun wq : PowerSeries ℂ_[p] =>
    1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3) (by
      rintro n x y ⟨z, hz⟩
      refine ⟨z * (c W.a₁ + c W.a₂ * X + (c W.a₃ * X ^ 2 + c W.a₄ * X ^ 3) * (x + y) +
        c W.a₆ * X ^ 5 * (x ^ 2 + x * y + y ^ 2)), ?_⟩
      have hz' : x - y = X ^ n * z := hz
      change _ = X ^ (n + 1) * _
      linear_combination (X * (c W.a₁ + c W.a₂ * X + (c W.a₃ * X ^ 2 + c W.a₄ * X ^ 3) * (x + y) +
        c W.a₆ * X ^ 5 * (x ^ 2 + x * y + y ^ 2))) * hz')
  exact ⟨w, hw.symm⟩

/- English proof (translation)
Establish `h'` using `congrArg PowerSeries.constantCoeff h`. Simplify using `using h'`.
-/
theorem constantCoeff_of_isWq {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]}
    {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) : PowerSeries.constantCoeff wq = 1 := by
  have h' := congrArg PowerSeries.constantCoeff h
  simpa using h'

/- English proof (translation)
Establish `h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2` using `map_ofNat _ 2`. Simplify using `[flog, omegaW, PowerSeries.constantCoeff_inv, constantCoeff_of_isWq h, h2]`.
-/
theorem coeff_one_flog {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]}
    {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) : PowerSeries.coeff 1 (flog W wq) = 1 := by
  have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  simp [flog, omegaW, PowerSeries.constantCoeff_inv, constantCoeff_of_isWq h, h2]

/- English proof (translation)
Simplify using `[flog]`.
-/
theorem constantCoeff_flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p])
    (wq : PowerSeries ℂ_[p]) : PowerSeries.constantCoeff (flog W wq) = 0 := by
  simp [flog]

/- English proof (translation)
Establish `hA : GlobalTheory.FormalInv.linearPart (fun _ : Unit => (l : MvPowerSeries Unit R)) = 1`. Use extensionality with `i j`. Conclude with `h1`. Take `⟨v, hv, h, -⟩` from `(GlobalTheory.FormalInv.exists_substInv_iff (u := fun _ : Unit => (l : MvPowerSeries Unit R)) (fun _ => h0)).2 (hA ▸ isUnit_one)`. Conclude with `⟨v (), hv (), h ()⟩`.
-/
theorem exists_subst_eq_X {R : Type*} [CommRing R] (l : PowerSeries R)
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1) :
    ∃ ex : PowerSeries R, PowerSeries.constantCoeff ex = 0 ∧
      PowerSeries.subst ex l = PowerSeries.X := by
  have hA : GlobalTheory.FormalInv.linearPart (fun _ : Unit => (l : MvPowerSeries Unit R)) = 1 := by
    ext i j
    exact h1
  obtain ⟨v, hv, h, -⟩ := (GlobalTheory.FormalInv.exists_substInv_iff
    (u := fun _ : Unit => (l : MvPowerSeries Unit R)) (fun _ => h0)).2 (hA ▸ isUnit_one)
  exact ⟨v (), hv (), h ()⟩

/- English proof (translation)
Introduce `D hm p _ lam cc δ hc hcop`. Take `⟨⟨C, hC⟩, -, hu⟩` from `hm p lam cc δ hc.1 hcop hc.2`. Take `⟨wq, hwq⟩` from `exists_isWq (C • wModel lam (lamOf D cc δ))`. Take `⟨ex, he0, he⟩` from `exists_subst_eq_X _ (constantCoeff_flog _ wq) (coeff_one_flog hwq)`. Conclude with `⟨⟨lam, lamOf D cc δ, C, wq, ex⟩, ⟨hc.1, hcop, hc.2, rfl, hC, hwq, he0, he⟩, rfl, hu C hC⟩`.
-/
theorem exists_genusOne_datum : ∀ (D : D7), GL3Theta.modelEx D → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → Nat.Coprime (Ideal.absNorm cc) p → ∃ g : GL3Theta.G1 p, GL3Theta.At D cc δ g ∧ g.lam = lam ∧ ‖((g.C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
  intro D hm p _ lam cc δ hc hcop
  obtain ⟨⟨C, hC⟩, -, hu⟩ := hm p lam cc δ hc.1 hcop hc.2
  obtain ⟨wq, hwq⟩ := exists_isWq (C • wModel lam (lamOf D cc δ))
  obtain ⟨ex, he0, he⟩ := exists_subst_eq_X _ (constantCoeff_flog _ wq) (coeff_one_flog hwq)
  exact ⟨⟨lam, lamOf D cc δ, C, wq, ex⟩, ⟨hc.1, hcop, hc.2, rfl, hC, hwq, he0, he⟩, rfl, hu C hC⟩

end GlobalTheory.GenusOneDatum
