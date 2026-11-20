import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGridSeparation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootGridLower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNormalLocusRep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace GridSeparation

/- English proof (translation)
Rewrite using `[eval_map, eval₂_eq]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_prod]`. Simplify using `[hζ]`.
-/
theorem norm_eval_le_of_torus {e : ℕ} (G : MvPolynomial (Fin e) ℤ) (ζ : Fin e → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1) :
    ‖eval ζ (map (Int.castRingHom ℂ) G)‖ ≤ ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) := by
  rw [eval_map, eval₂_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul, norm_prod]
  simp [hζ]

/- English proof (translation)
Establish `h1 : {x : ℂ | x ^ m = 1}.Finite` using `(Polynomial.nthRoots m (1 : ℂ)).toFinset.finite_toSet.subset fun x hx => by`. Simplify `hx` using `[Polynomial.mem_nthRoots hm]`. Use `Set.Finite.pi (t := fun _ : Fin e => {x : ℂ | x ^ m = 1}) fun _ => h1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `ζ`. Simplify using `[Set.mem_pi]`.
-/
theorem grid_finite (e m : ℕ) (hm : 0 < m) : {ζ : Fin e → ℂ | ∀ i, ζ i ^ m = 1}.Finite := by
  have h1 : {x : ℂ | x ^ m = 1}.Finite :=
    (Polynomial.nthRoots m (1 : ℂ)).toFinset.finite_toSet.subset fun x hx => by
      simpa [Polynomial.mem_nthRoots hm] using hx
  convert Set.Finite.pi (t := fun _ : Fin e => {x : ℂ | x ^ m = 1}) fun _ => h1 using 1
  ext ζ
  simp [Set.mem_pi]

/- English proof (translation)
The claim follows from `(pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').mp (by rw [← norm_pow, hx, norm_one])`.
-/
theorem norm_of_pow_eq_one {m : ℕ} (hm : 0 < m) {x : ℂ} (hx : x ^ m = 1) : ‖x‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').mp (by rw [← norm_pow, hx, norm_one])

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D A hV hBir hA`. Take `⟨df, f, hf, hfP, hrep⟩` from `hNL K ι Ω y D hV hBir`. Take `⟨n, c, B, G, Fib, hn, hB1, hG0, hFib, hnorm⟩` from `hFN K ι Ω y D A df f hV hBir hA hf hfP`. Use `set SG : ℝ := ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) + 1 with hSG`. Establish `hSG1 : 1 ≤ SG`.

Establish `: 0 ≤ ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ)` using `Finset.sum_nonneg fun d _ => by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX : 1 ≤ 2 * B * SG` using `by nlinarith`. Use `⟨Real.log (2 * B * SG), Real.log_nonneg hX, fun τ => ?_⟩` and prove the remaining obligations. Use `set m := G.totalDegree + c * (τ + 1) + 1 with hm`.

Establish `hm0 : 0 < m` using `by omega`. Use `set Z := ((grid_finite (D + 1) m hm0).toFinset.filter fun ζ => eval ζ (map (Int.castRingHom ℂ) G) ≠ 0).biUnion Fib with hZ`. Establish `hmem : ∀ ζ : Fin (D + 1) → ℂ, (∀ i, ζ i ^ m = 1) → eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 → ∀ z ∈ Fib ζ, z ∈ Z` using `fun ζ hζ hG z hz => Finset.mem_biUnion.mpr ⟨ζ, Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr hζ, hG⟩, hz⟩`. Establish `hZpt : ∀ z ∈ Z, z ∈ mcPts (mCoordIdeal y) ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0`. Introduce `z hz`.

Take `⟨ζ, hζ, hzζ⟩` from `Finset.mem_biUnion.mp hz`. Take `⟨hζg, hGζ⟩` from `Finset.mem_filter.mp hζ`. Establish `hζg' : ∀ i, ζ i ^ m = 1` using `(Set.Finite.mem_toFinset _).mp hζg`. Conclude with `hFib ζ (fun i => norm_of_pow_eq_one hm0 (hζg' i)) hGζ z hzζ`. Use `⟨Z, fun z hz => (hZpt z hz).1, fun s hs z hz => hrep A.a τ s hs z (hZpt z hz).1 (hZpt z hz).2, ?_⟩` and prove the remaining obligations.

Introduce `u hu hu0`. Take `⟨F, hF0, hFdeg, hFb⟩` from `hnorm τ u hu hu0`. Assume the negation of the conclusion as `hcon`. Take `⟨ζ, hζm, hζ1⟩` from `hRG (D + 1) m (G * F) (mul_ne_zero hG0 hF0) fun i => by`. Establish `h1` using `degreeOf_mul_le i G F`.

Establish `h2` using `degreeOf_le_totalDegree G i`. Establish `h3` using `hFdeg i`. Use linear arithmetic over natural numbers and integers. Establish `hζn : ∀ i, ‖ζ i‖ = 1` using `fun i => norm_of_pow_eq_one hm0 (hζm i)`. Rewrite `hζ1` using `[map_mul, eval_mul, norm_mul]`.

Establish `hGζ : eval ζ (map (Int.castRingHom ℂ) G) ≠ 0`. Introduce `h`. Rewrite `hζ1` using `[h, norm_zero, zero_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set E := Real.exp (-(Real.log (2 * B * SG) * ((τ : ℝ) + 1))) with hE`.

Establish `hE0 : 0 < E` using `Real.exp_pos _`. Establish `hFle` using `hFb ζ hζn hGζ E hE0.le fun z hz => by`. Take `⟨dg, dh, g, h, hg, hh, hd, hy, hz0⟩` from `hrep A.a τ u hu z (hFib ζ hζn hGζ z hz).1 (hFib ζ hζn hGζ z hz).2`. Use `⟨dg, dh, g, h, hg, hh, hd, hy, hz0, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Conclude with `hcon ⟨z, hmem ζ hζm hGζ z hz, dg, dh, g, h, hg, hh, hd, hy, hz0, (not_le.mp hlt).le⟩`. Establish `hEX : E * (2 * B * SG) ^ (τ + 1) = 1`. Establish `: -(Real.log (2 * B * SG) * ((τ : ℝ) + 1)) = ((τ + 1 : ℕ) : ℝ) * (-Real.log (2 * B * SG))`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hE, this, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by linarith), ← mul_pow, inv_mul_cancel₀ (by linarith), one_pow]`. Establish `hE1 : E ≤ 1`. Establish `: 1 ≤ (2 * B * SG) ^ (τ + 1)` using `one_le_pow₀ hX`. Use the polynomial consequences of the given equalities and inequalities. Establish `hEn : E ^ n ≤ E` using `pow_le_of_le_one hE0.le hE1 (by omega)`.

Establish `hGle : ‖eval ζ (map (Int.castRingHom ℂ) G)‖ ≤ SG`. Use `norm_eval_le_of_torus G ζ hζn` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpow : 2 * SG * B ^ (τ + 1) ≤ (2 * B * SG) ^ (τ + 1)`. Rewrite using `[show 2 * B * SG = (2 * SG) * B by ring, mul_pow]`.

Establish `hB0 : 0 ≤ B ^ (τ + 1)` using `pow_nonneg (by linarith) _`. Establish `: 2 * SG ≤ (2 * SG) ^ (τ + 1)` using `le_self_pow₀ (by linarith) (by omega)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hBp : 0 ≤ B ^ (τ + 1)` using `pow_nonneg (by linarith) _`. Establish `hFn : ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * E`.

Combine the equalities or inequalities in the displayed calculation. Establish `key : 2 * (SG * (B ^ (τ + 1) * E)) ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hFnn : 0 ≤ ‖eval ζ (map (Int.castRingHom ℂ) F)‖` using `norm_nonneg _`. Establish `: ‖eval ζ (map (Int.castRingHom ℂ) G)‖ * ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ SG * (B ^ (τ + 1) * E)` using `mul_le_mul hGle hFn hFnn (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem proof (hNL : NormalLocusRep.Statement) (hFN : FibreNormBound.Statement)
    (hRG : RootGridLower.Statement) : GridSeparation.Statement := by
  classical
  intro K _ ι _ Ω _ y D A hV hBir hA
  obtain ⟨df, f, hf, hfP, hrep⟩ := hNL K ι Ω y D hV hBir
  obtain ⟨n, c, B, G, Fib, hn, hB1, hG0, hFib, hnorm⟩ := hFN K ι Ω y D A df f hV hBir hA hf hfP
  set SG : ℝ := ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) + 1 with hSG
  have hSG1 : 1 ≤ SG := by
    have : 0 ≤ ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) := Finset.sum_nonneg fun d _ => by positivity
    linarith
  have hX : 1 ≤ 2 * B * SG := by nlinarith
  refine ⟨Real.log (2 * B * SG), Real.log_nonneg hX, fun τ => ?_⟩
  set m := G.totalDegree + c * (τ + 1) + 1 with hm
  have hm0 : 0 < m := by omega
  set Z := ((grid_finite (D + 1) m hm0).toFinset.filter
    fun ζ => eval ζ (map (Int.castRingHom ℂ) G) ≠ 0).biUnion Fib with hZ
  have hmem : ∀ ζ : Fin (D + 1) → ℂ, (∀ i, ζ i ^ m = 1) → eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
      ∀ z ∈ Fib ζ, z ∈ Z := fun ζ hζ hG z hz =>
    Finset.mem_biUnion.mpr ⟨ζ, Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr hζ, hG⟩, hz⟩
  have hZpt : ∀ z ∈ Z, z ∈ mcPts (mCoordIdeal y) ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0 := by
    intro z hz
    obtain ⟨ζ, hζ, hzζ⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hζg, hGζ⟩ := Finset.mem_filter.mp hζ
    have hζg' : ∀ i, ζ i ^ m = 1 := (Set.Finite.mem_toFinset _).mp hζg
    exact hFib ζ (fun i => norm_of_pow_eq_one hm0 (hζg' i)) hGζ z hzζ
  refine ⟨Z, fun z hz => (hZpt z hz).1, fun s hs z hz => hrep A.a τ s hs z (hZpt z hz).1 (hZpt z hz).2, ?_⟩
  intro u hu hu0
  obtain ⟨F, hF0, hFdeg, hFb⟩ := hnorm τ u hu hu0
  by_contra hcon
  obtain ⟨ζ, hζm, hζ1⟩ := hRG (D + 1) m (G * F) (mul_ne_zero hG0 hF0) fun i => by
    have h1 := degreeOf_mul_le i G F
    have h2 := degreeOf_le_totalDegree G i
    have h3 := hFdeg i
    omega
  have hζn : ∀ i, ‖ζ i‖ = 1 := fun i => norm_of_pow_eq_one hm0 (hζm i)
  rw [map_mul, eval_mul, norm_mul] at hζ1
  have hGζ : eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_mul] at hζ1
    linarith
  set E := Real.exp (-(Real.log (2 * B * SG) * ((τ : ℝ) + 1))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hFle := hFb ζ hζn hGζ E hE0.le fun z hz => by
    obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0⟩ :=
      hrep A.a τ u hu z (hFib ζ hζn hGζ z hz).1 (hFib ζ hζn hGζ z hz).2
    refine ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, ?_⟩
    by_contra hlt
    exact hcon ⟨z, hmem ζ hζm hGζ z hz, dg, dh, g, h, hg, hh, hd, hy, hz0, (not_le.mp hlt).le⟩
  have hEX : E * (2 * B * SG) ^ (τ + 1) = 1 := by
    have : -(Real.log (2 * B * SG) * ((τ : ℝ) + 1)) = ((τ + 1 : ℕ) : ℝ) * (-Real.log (2 * B * SG)) := by
      push_cast
      ring
    rw [hE, this, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by linarith), ← mul_pow,
      inv_mul_cancel₀ (by linarith), one_pow]
  have hE1 : E ≤ 1 := by
    have : 1 ≤ (2 * B * SG) ^ (τ + 1) := one_le_pow₀ hX
    nlinarith
  have hEn : E ^ n ≤ E := pow_le_of_le_one hE0.le hE1 (by omega)
  have hGle : ‖eval ζ (map (Int.castRingHom ℂ) G)‖ ≤ SG := by
    have := norm_eval_le_of_torus G ζ hζn
    linarith
  have hpow : 2 * SG * B ^ (τ + 1) ≤ (2 * B * SG) ^ (τ + 1) := by
    rw [show 2 * B * SG = (2 * SG) * B by ring, mul_pow]
    have hB0 : 0 ≤ B ^ (τ + 1) := pow_nonneg (by linarith) _
    have : 2 * SG ≤ (2 * SG) ^ (τ + 1) := le_self_pow₀ (by linarith) (by omega)
    nlinarith
  have hBp : 0 ≤ B ^ (τ + 1) := pow_nonneg (by linarith) _
  have hFn : ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * E := by
    calc _ ≤ B ^ (τ + 1) * E ^ n := hFle
      _ ≤ B ^ (τ + 1) * E := mul_le_mul_of_nonneg_left hEn hBp
  have key : 2 * (SG * (B ^ (τ + 1) * E)) ≤ 1 := by
    calc 2 * (SG * (B ^ (τ + 1) * E)) = (2 * SG * B ^ (τ + 1)) * E := by ring
      _ ≤ (2 * B * SG) ^ (τ + 1) * E := mul_le_mul_of_nonneg_right hpow hE0.le
      _ = 1 := by rw [mul_comm, hEX]
  have hFnn : 0 ≤ ‖eval ζ (map (Int.castRingHom ℂ) F)‖ := norm_nonneg _
  have : ‖eval ζ (map (Int.castRingHom ℂ) G)‖ * ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤
      SG * (B ^ (τ + 1) * E) :=
    mul_le_mul hGle hFn hFnn (by linarith)
  linarith

end GridSeparation

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
