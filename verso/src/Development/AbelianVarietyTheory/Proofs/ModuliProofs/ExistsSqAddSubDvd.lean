import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace SquareDensity

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, dvd_zero _, by simp⟩`. Consider the case `succ n ih`. Take `⟨w, ⟨c, hc⟩, hw⟩` from `ih`. Use `⟨x - w ^ 2, ⟨1 - c * w, by rw [hc]; ring⟩, ?_⟩` and prove the remaining obligations.

Establish `h : (x - w ^ 2) ^ 2 + (x - w ^ 2) - x = (w ^ 2 + w - x) * (x * (c * w - c - 1))`. Establish `: x * (c * w - c - 1) = w ^ 2 - w - x` using `by rw [hc]; ring`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, pow_succ]`.

Conclude with `mul_dvd_mul hw (dvd_mul_right _ _)`.
-/
theorem exists_sq_add_sub_dvd {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∃ w : R, x ∣ w ∧ x ^ n ∣ w ^ 2 + w - x := by
  induction n with
  | zero => exact ⟨0, dvd_zero _, by simp⟩
  | succ n ih =>
    obtain ⟨w, ⟨c, hc⟩, hw⟩ := ih
    refine ⟨x - w ^ 2, ⟨1 - c * w, by rw [hc]; ring⟩, ?_⟩
    have h : (x - w ^ 2) ^ 2 + (x - w ^ 2) - x = (w ^ 2 + w - x) * (x * (c * w - c - 1)) := by
      have : x * (c * w - c - 1) = w ^ 2 - w - x := by rw [hc]; ring
      rw [this]; ring
    rw [h, pow_succ]
    exact mul_dvd_mul hw (dvd_mul_right _ _)

/- English proof (translation)
Proceed by induction on `Φ using MvPolynomial.induction_on with`. Consider the case `C c => simp`. Consider the case `add p q hp hq`. Use `dvd_add hp hq` as an intermediate fact. Simplify using `only [map_add]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p i hp`. Use `dvd_add (hp.mul_right (a i)) ((h i).mul_left (MvPolynomial.aeval b p))` as an intermediate fact. Simplify using `only [map_mul, MvPolynomial.aeval_X]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dvd_aeval_sub_aeval {K S σ : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (Φ : MvPolynomial σ K) (s : S) (a b : σ → S) (h : ∀ i, s ∣ a i - b i) :
    s ∣ MvPolynomial.aeval a Φ - MvPolynomial.aeval b Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    have := dvd_add hp hq
    simp only [map_add]
    convert this using 1
    ring
  | mul_X p i hp =>
    have := dvd_add (hp.mul_right (a i)) ((h i).mul_left (MvPolynomial.aeval b p))
    simp only [map_mul, MvPolynomial.aeval_X]
    convert this using 1
    ring

/- English proof (translation)
Proceed by induction on `Φ using MvPolynomial.induction_on with`. Consider the case `C c => simp`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p i hp => simp [hp]`.
-/
theorem eval_aeval {K σ : Type*} [CommRing K] (Φ : MvPolynomial σ K) (a : σ → Polynomial K)
    (t : K) :
    (MvPolynomial.aeval a Φ).eval t = MvPolynomial.eval (fun i => (a i).eval t) Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/- English proof (translation)
Use `set x : Polynomial (Polynomial ℤ) := Polynomial.C Polynomial.X * (F - 1).map Polynomial.C with hx`. Take `⟨w, -, hw⟩` from `exists_sq_add_sub_dvd x (d + 1)`. Use `set y : Polynomial (Polynomial ℤ) := 1 + 2 * w with hy`. Take `⟨Φ, hd, hΦ⟩` from `hΨ (max F.natDegree (y ^ 2).natDegree + 1)`. Use `set a : Fin (max F.natDegree (y ^ 2).natDegree + 1) → Polynomial K := fun i => ((1 + 4 * x).coeff i).map (Int.castRingHom K) with ha`.

Use `set b : Fin (max F.natDegree (y ^ 2).natDegree + 1) → Polynomial K := fun i => ((y ^ 2).coeff i).map (Int.castRingHom K) with hb`. Establish `hai : ∀ i, a i = Polynomial.C (((1 : Polynomial ℤ).coeff i : ℤ) : K) + Polynomial.C (4 * (((F - 1).coeff i : ℤ) : K)) * Polynomial.X`. Introduce `i`. Establish `h4 : (4 : Polynomial (Polynomial ℤ)) = Polynomial.C 4` using `rfl`. Simplify using `only [ha, hx, h4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_map, Polynomial.coeff_one]`.

Apply the tactic sequence `split_ifs <;> simp [Polynomial.map_mul, map_ofNat] <;> ring`. Establish `hb0 : MvPolynomial.aeval b Φ = 0`. Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises. Use `Set.infinite_of_injective_forall_mem (f := fun k : ℤ => (k : K)) Int.cast_injective fun k => ?_` and prove the remaining obligations. Use `show (MvPolynomial.aeval b Φ).eval (k : K) = 0`.

Rewrite using `[eval_aeval, ← hsq (y.map (Polynomial.evalRingHom k)), ← Polynomial.map_pow, hΦ]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `only [hb, Polynomial.coeff_map, Polynomial.coe_evalRingHom]`. Conclude with `Polynomial.eval_intCast_map (Int.castRingHom K) _ k`.

Conclude with `lt_of_le_of_lt (Polynomial.natDegree_map_le.trans (le_max_right _ _)) (Nat.lt_succ_self _)`. Establish `hdvd : (Polynomial.X : Polynomial K) ^ (d + 1) ∣ MvPolynomial.aeval a Φ`. Rewrite using `[← sub_zero (MvPolynomial.aeval a Φ), ← hb0]`. Apply `dvd_aeval_sub_aeval` to reduce the goal to its premises. Introduce `i`.

Establish `h1 : Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (d + 1)) ∣ (1 + 4 * x) - y ^ 2`. Establish `h2 : (1 + 4 * x) - y ^ 2 = (w ^ 2 + w - x) * (-4)` using `by rw [hy]; ring`. Rewrite using `[h2, map_pow]`. Conclude with `((pow_dvd_pow_of_dvd (dvd_mul_right _ _) _).trans hw).mul_right _`. Establish `h3` using `(Polynomial.C_dvd_iff_dvd_coeff _ _).1 h1 i`.

Establish `h4` using `Polynomial.map_dvd (Int.castRingHom K) h3`. Simplify `h4` using `only [Polynomial.map_pow, Polynomial.map_X, Polynomial.coeff_sub, Polynomial.map_sub]`. Establish `hdeg : (MvPolynomial.aeval a Φ).natDegree ≤ d * 1`. Use `MvPolynomial.aeval_natDegree_le Φ hd a fun i => ?_` and prove the remaining obligations. Rewrite using `[hai]`.

Use `compute_degree`. Establish `ha0 : MvPolynomial.aeval a Φ = 0` using `Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd (by`. Rewrite using `[Polynomial.natDegree_X_pow]`. Use the proof step `omega)`. Establish `h` using `eval_aeval Φ a (1 / 4)`.

Rewrite `h` using `[ha0, Polynomial.eval_zero]`. Rewrite using `[hΦ F (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)), h]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Rewrite using `[hai]`.

Simplify using `only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.coeff_sub, Int.cast_sub]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eq_zero_of_sq {K : Type*} [Field K] [CharZero K] (Ψ : Polynomial ℤ → K) (d : ℕ)
    (hΨ : ∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) K, Φ.totalDegree ≤ d ∧
      ∀ F : Polynomial ℤ, F.natDegree < r →
        Ψ F = MvPolynomial.eval (fun i : Fin r => ((F.coeff i : ℤ) : K)) Φ)
    (hsq : ∀ G, Ψ (G ^ 2) = 0) (F : Polynomial ℤ) : Ψ F = 0 := by
  set x : Polynomial (Polynomial ℤ) :=
    Polynomial.C Polynomial.X * (F - 1).map Polynomial.C with hx
  obtain ⟨w, -, hw⟩ := exists_sq_add_sub_dvd x (d + 1)
  set y : Polynomial (Polynomial ℤ) := 1 + 2 * w with hy
  obtain ⟨Φ, hd, hΦ⟩ := hΨ (max F.natDegree (y ^ 2).natDegree + 1)
  set a : Fin (max F.natDegree (y ^ 2).natDegree + 1) → Polynomial K :=
    fun i => ((1 + 4 * x).coeff i).map (Int.castRingHom K) with ha
  set b : Fin (max F.natDegree (y ^ 2).natDegree + 1) → Polynomial K :=
    fun i => ((y ^ 2).coeff i).map (Int.castRingHom K) with hb
  have hai : ∀ i, a i = Polynomial.C (((1 : Polynomial ℤ).coeff i : ℤ) : K) +
      Polynomial.C (4 * (((F - 1).coeff i : ℤ) : K)) * Polynomial.X := by
    intro i
    have h4 : (4 : Polynomial (Polynomial ℤ)) = Polynomial.C 4 := rfl
    simp only [ha, hx, h4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Polynomial.coeff_one]
    split_ifs <;> simp [Polynomial.map_mul, map_ofNat] <;> ring
  have hb0 : MvPolynomial.aeval b Φ = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℤ => (k : K))
      Int.cast_injective fun k => ?_
    show (MvPolynomial.aeval b Φ).eval (k : K) = 0
    rw [eval_aeval, ← hsq (y.map (Polynomial.evalRingHom k)), ← Polynomial.map_pow, hΦ]
    · congr 2
      funext i
      simp only [hb, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
      exact Polynomial.eval_intCast_map (Int.castRingHom K) _ k
    · exact lt_of_le_of_lt (Polynomial.natDegree_map_le.trans (le_max_right _ _))
        (Nat.lt_succ_self _)
  have hdvd : (Polynomial.X : Polynomial K) ^ (d + 1) ∣ MvPolynomial.aeval a Φ := by
    rw [← sub_zero (MvPolynomial.aeval a Φ), ← hb0]
    apply dvd_aeval_sub_aeval
    intro i
    have h1 : Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (d + 1)) ∣ (1 + 4 * x) - y ^ 2 := by
      have h2 : (1 + 4 * x) - y ^ 2 = (w ^ 2 + w - x) * (-4) := by rw [hy]; ring
      rw [h2, map_pow]
      exact ((pow_dvd_pow_of_dvd (dvd_mul_right _ _) _).trans hw).mul_right _
    have h3 := (Polynomial.C_dvd_iff_dvd_coeff _ _).1 h1 i
    have h4 := Polynomial.map_dvd (Int.castRingHom K) h3
    simpa only [Polynomial.map_pow, Polynomial.map_X, Polynomial.coeff_sub,
      Polynomial.map_sub] using h4
  have hdeg : (MvPolynomial.aeval a Φ).natDegree ≤ d * 1 := by
    refine MvPolynomial.aeval_natDegree_le Φ hd a fun i => ?_
    rw [hai]
    compute_degree
  have ha0 : MvPolynomial.aeval a Φ = 0 :=
    Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd (by
      rw [Polynomial.natDegree_X_pow]; omega)
  have h := eval_aeval Φ a (1 / 4)
  rw [ha0, Polynomial.eval_zero] at h
  rw [hΦ F (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)), h]
  congr 2
  funext i
  rw [hai]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.coeff_sub, Int.cast_sub]
  ring

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (F.coeff i)) r]`. Conclude with `F.as_sum_range' r h`.
-/
theorem eq_sum_monomial (F : Polynomial ℤ) (r : ℕ) (h : F.natDegree < r) :
    F = ∑ i : Fin r, Polynomial.monomial (i : ℕ) (F.coeff i) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (F.coeff i)) r]
  exact F.as_sum_range' r h

/- English proof (translation)
Set `M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin r) K)` to `fun j k => ∑ i : Fin r, MvPolynomial.C (φ ((U ^ (i : ℕ)) j k)) * MvPolynomial.X i`. Establish `hM : ∀ j k, (M j k).IsHomogeneous 1` using `fun j k => MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (MvPolynomial.isHomogeneous_X K i).C_mul _`. Use `⟨M.det, ?_, fun F hF => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_apply']`. Use `MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_` and prove the remaining obligations.

Establish `h1` using `MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => M (σ i) i) (fun _ => 1) fun i _ => hM _ _`. Establish `h2` using `h1.C_mul (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K)`. Simplify using `using h2`. Rewrite using `[RingHom.map_det, RingHom.map_det]`. Use `congr 1`.

Use extensionality with `j k`. Rewrite using `[Polynomial.aeval_eq_sum_range' hF, ← Fin.sum_univ_eq_sum_range (fun i => F.coeff i • U ^ i) r]`. Express the relevant statement in the definitionally equal form `φ ((∑ i : Fin r, F.coeff i • U ^ (i : ℕ)) j k) = MvPolynomial.eval _ (∑ i : Fin r, MvPolynomial.C (φ ((U ^ (i : ℕ)) j k)) * MvPolynomial.X i)`. Rewrite using `[Matrix.sum_apply, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.smul_apply, map_zsmul, zsmul_eq_mul, mul_comm, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]`.
-/
theorem exists_det_polynomial {R K : Type*} [CommRing R] [CommRing K] (φ : R →+* K) {m : ℕ}
    (U : Matrix (Fin m) (Fin m) R) (r : ℕ) :
    ∃ Φ : MvPolynomial (Fin r) K, Φ.IsHomogeneous m ∧
      ∀ F : Polynomial ℤ, F.natDegree < r →
        φ (Polynomial.aeval U F).det =
          MvPolynomial.eval (fun i : Fin r => ((F.coeff i : ℤ) : K)) Φ := by
  let M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin r) K) := fun j k =>
    ∑ i : Fin r, MvPolynomial.C (φ ((U ^ (i : ℕ)) j k)) * MvPolynomial.X i
  have hM : ∀ j k, (M j k).IsHomogeneous 1 := fun j k =>
    MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (MvPolynomial.isHomogeneous_X K i).C_mul _
  refine ⟨M.det, ?_, fun F hF => ?_⟩
  · rw [Matrix.det_apply']
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
    have h1 := MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => M (σ i) i) (fun _ => 1)
      fun i _ => hM _ _
    have h2 := h1.C_mul (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K)
    simpa using h2
  · rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext j k
    rw [Polynomial.aeval_eq_sum_range' hF, ← Fin.sum_univ_eq_sum_range
      (fun i => F.coeff i • U ^ i) r]
    change φ ((∑ i : Fin r, F.coeff i • U ^ (i : ℕ)) j k) = MvPolynomial.eval _
      (∑ i : Fin r, MvPolynomial.C (φ ((U ^ (i : ℕ)) j k)) * MvPolynomial.X i)
    rw [Matrix.sum_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_apply, map_zsmul, zsmul_eq_mul, mul_comm, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X]

end SquareDensity

/- English proof (translation)
Introduce `l _ m g U D hD hsq _ F`. Use `sub_eq_zero.1 (SquareDensity.eq_zero_of_sq (fun F => ((D F ^ 2 : ℚ) : ℚ_[l]) - ((Polynomial.aeval U F).det : ℤ_[l])) (max (2 * g) m) (fun r => ?_) (fun G => ?_) F)` and prove the remaining obligations. Take `⟨Φ, hΦ, hDΦ⟩` from `hD r`. Take `⟨Θ, hΘ, hdet⟩` from `SquareDensity.exists_det_polynomial (PadicInt.Coe.ringHom (p := l)) U r`. Use `⟨(MvPolynomial.map (algebraMap ℚ ℚ_[l]) Φ) ^ 2 - Θ, ?_, fun F hF => ?_⟩` and prove the remaining obligations.

Use `(MvPolynomial.totalDegree_sub _ _).trans (max_le_max ?_ hΘ.totalDegree_le)` and prove the remaining obligations. Use `((hΦ.map (algebraMap ℚ ℚ_[l])).pow 2).totalDegree_le` as an intermediate fact. Rewrite `this` using `[mul_comm]`. Then use the resulting hypothesis. Rewrite using `[map_sub, map_pow, ← hdet F hF, Rat.cast_pow]`. Use `congr 2`.

Establish `h1` using `hDΦ fun i => F.coeff i`. Rewrite `h1` using `[← SquareDensity.eq_sum_monomial F r hF]`. Rewrite using `[h1, MvPolynomial.eval_map]`. Establish `h2` using `MvPolynomial.eval₂_comp_left (algebraMap ℚ ℚ_[l]) (RingHom.id ℚ) (fun i : Fin r => ((F.coeff i : ℤ) : ℚ)) Φ`. Simplify `h2` using `[Function.comp_def]`.

Simplify using `only [map_pow, Matrix.det_pow, Rat.cast_pow, hsq G, PadicInt.coe_pow, sub_self]`.
-/
theorem sq_eq_det_aeval_of_sq : ∀ (l : ℕ) [Fact l.Prime] (m g : ℕ) (U : Matrix (Fin m) (Fin m) ℤ_[l]) (D : Polynomial ℤ → ℚ), (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous g ∧ ∀ a : Fin r → ℤ, D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) → (∀ G, ((D (G ^ 2) : ℚ) : ℚ_[l]) = ((Polynomial.aeval U G).det : ℤ_[l])) → (∀ F H, Polynomial.aeval U H = 0 → D (F + H) = D F) → ∀ F, ((D F ^ 2 : ℚ) : ℚ_[l]) = ((Polynomial.aeval U F).det : ℤ_[l]) := by
  intro l _ m g U D hD hsq _ F
  refine sub_eq_zero.1 (SquareDensity.eq_zero_of_sq
    (fun F => ((D F ^ 2 : ℚ) : ℚ_[l]) - ((Polynomial.aeval U F).det : ℤ_[l]))
    (max (2 * g) m) (fun r => ?_) (fun G => ?_) F)
  · obtain ⟨Φ, hΦ, hDΦ⟩ := hD r
    obtain ⟨Θ, hΘ, hdet⟩ := SquareDensity.exists_det_polynomial (PadicInt.Coe.ringHom (p := l)) U r
    refine ⟨(MvPolynomial.map (algebraMap ℚ ℚ_[l]) Φ) ^ 2 - Θ, ?_, fun F hF => ?_⟩
    · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le_max ?_ hΘ.totalDegree_le)
      have := ((hΦ.map (algebraMap ℚ ℚ_[l])).pow 2).totalDegree_le
      rwa [mul_comm] at this
    · rw [map_sub, map_pow, ← hdet F hF, Rat.cast_pow]
      congr 2
      have h1 := hDΦ fun i => F.coeff i
      rw [← SquareDensity.eq_sum_monomial F r hF] at h1
      rw [h1, MvPolynomial.eval_map]
      have h2 := MvPolynomial.eval₂_comp_left (algebraMap ℚ ℚ_[l]) (RingHom.id ℚ)
        (fun i : Fin r => ((F.coeff i : ℤ) : ℚ)) Φ
      simpa [Function.comp_def] using h2
  · simp only [map_pow, Matrix.det_pow, Rat.cast_pow, hsq G, PadicInt.coe_pow, sub_self]

end GlobalTheory
