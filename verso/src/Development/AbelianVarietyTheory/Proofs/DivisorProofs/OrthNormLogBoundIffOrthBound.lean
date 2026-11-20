import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledCoisometryNorms

open scoped ComplexOrder Matrix
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.BrNormCompare

open GlobalTheory.IndefiniteRowSideFullHecke

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [OrthogonalNormSquareSum.gramSum, ScaledCoisometryNorms.sumGram, Matrix.of_apply]`. Distinguish the cases in `ha : a.1 < n`. Simplify using `[ha]`. Distinguish the cases in `hb : b.1 < n`.

Simplify using `[ha, hb]`. Establish `h1 : a = Br.iL hN` using `Fin.ext (by have := a.2; simp only [Br.iL]; omega)`. Establish `h2 : b = Br.iL hN` using `Fin.ext (by have := b.2; simp only [Br.iL]; omega)`. Rewrite using `[dif_neg ha, dif_neg ha, if_neg hb, if_neg hb, if_pos ⟨h1, h2⟩]`.
-/
theorem gramSum_eq_sumGram {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) (G' : Matrix (Fin n) (Fin n) K) (g : K) :
    OrthogonalNormSquareSum.gramSum hN G' g = ScaledCoisometryNorms.sumGram N G' g := by
  ext a b
  simp only [OrthogonalNormSquareSum.gramSum, ScaledCoisometryNorms.sumGram, Matrix.of_apply]
  by_cases ha : a.1 < n
  · simp [ha]
  · by_cases hb : b.1 < n
    · simp [ha, hb]
    · have h1 : a = Br.iL hN := Fin.ext (by have := a.2; simp only [Br.iL]; omega)
      have h2 : b = Br.iL hN := Fin.ext (by have := b.2; simp only [Br.iL]; omega)
      rw [dif_neg ha, dif_neg ha, if_neg hb, if_neg hb, if_pos ⟨h1, h2⟩]

/- English proof (translation)
Rewrite using `[map_mul, map_mul, hs, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]`. Simplify using `only [Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem length_eq {K : Type} [Field K] [StarRing K] (s : K →+* ℂ) (hs : ∀ x : K, s (star x) = star (s x)) (g t : K) :
    s (star t * g * t) = ((‖s t‖ ^ 2 : ℝ) : ℂ) * s g := by
  rw [map_mul, map_mul, hs, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

section

variable {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {N n : ℕ}

/- English proof (translation)
Apply the tactic sequence `unfold OrthogonalNormSquareSum.IsScaledCoisometry ScaledCoisometryNorms.IsScaledCoisometry`. Use `and_congr_left' ⟨fun h => pow_pos h 2, fun h => lt_of_le_of_ne hρ ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at h`.
-/
theorem isScaledCoisometry_iff (s : K →+* ℂ) (lam : ι → DomWeight N) (G : ι → Matrix (Fin N) (Fin N) K)
    (sg : ι → DomWeight n) (G' : ι → Matrix (Fin n) (Fin n) K) (P : VV K lam →ₗ[K] VV K sg) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    OrthogonalNormSquareSum.IsScaledCoisometry s lam G sg G' P ρ ↔ 0 < ρ ^ 2 ∧ ScaledCoisometryNorms.IsScaledCoisometry s lam sg G G' P (ρ ^ 2) := by
  unfold OrthogonalNormSquareSum.IsScaledCoisometry ScaledCoisometryNorms.IsScaledCoisometry
  refine and_congr_left' ⟨fun h => pow_pos h 2, fun h => lt_of_le_of_ne hρ ?_⟩
  rintro rfl
  simp at h

/- English proof (translation)
The claim follows from `mul_nonneg (mul_nonneg (Real.rpow_nonneg hT.le _) (abs_nonneg _)) (Real.sqrt_nonneg _)`.
-/
theorem factor_nonneg (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) {T : ℝ} (hT : 0 < T) :
    0 ≤ OrthogonalNormSquareSum.factor hN lam sg T :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg hT.le _) (abs_nonneg _)) (Real.sqrt_nonneg _)

/- English proof (translation)
Rewrite using `[← Finset.prod_pow]`. Conclude with `Finset.prod_congr rfl fun τ _ => OrthogonalNormSquareSum.factor_sq hN _ _ hT`.
-/
theorem prod_factor_sq (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) {T : ℝ} (hT : 0 < T) :
    (∏ τ, OrthogonalNormSquareSum.factor hN (lam τ) (sg τ) T) ^ 2 = ScaledCoisometryNorms.brSq hN lam sg T := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun τ _ => OrthogonalNormSquareSum.factor_sq hN _ _ hT

/- English proof (translation)
The claim follows from `(ScaledCoisometryNorms.brSq_eq hN lam sg hT).symm`.
-/
theorem const_eq (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) {T : ℝ} (hT : 0 < T) :
    T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * OrthogonalNormSquareSum.orthNormSq hN lam sg = ScaledCoisometryNorms.brSq hN lam sg T :=
  (ScaledCoisometryNorms.brSq_eq hN lam sg hT).symm

/- English proof (translation)
Rewrite using `[isScaledCoisometry_iff s lam G sg G' _ (Finset.prod_nonneg fun τ _ => factor_nonneg hN _ _ hT), prod_factor_sq hN lam sg hT, const_eq hN lam sg hT, and_assoc]`. Both sides reduce to the same expression.
-/
theorem whole_iff (s : K →+* ℂ) (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (G : ι → Matrix (Fin N) (Fin N) K) (G' : ι → Matrix (Fin n) (Fin n) K) (t : ι → K) {T : ℝ} (hT : 0 < T) :
    (OrthogonalNormSquareSum.IsScaledCoisometry s lam G sg G' (Br.brAt hN lam sg t) (∏ τ, OrthogonalNormSquareSum.factor hN (lam τ) (sg τ) T) ∧
      OrthogonalNormSquareSum.HasOpNormSq s lam G sg G' (Br.brAt hN lam sg t)
        (T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * OrthogonalNormSquareSum.orthNormSq hN lam sg)) ↔
    ScaledCoisometryNorms.NormConcl s hN lam sg G G' t T := by
  rw [isScaledCoisometry_iff s lam G sg G' _ (Finset.prod_nonneg fun τ _ => factor_nonneg hN _ _ hT),
    prod_factor_sq hN lam sg hT, const_eq hN lam sg hT, and_assoc]
  rfl

/- English proof (translation)
Rewrite using `[isScaledCoisometry_iff _ _ _ _ _ _ (factor_nonneg hN lam sg hT), ← prod_factor_sq hN _ _ hT]`. Simplify using the standard rewrite rules.
-/
theorem single_iff (s : K →+* ℂ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)
    (G : Matrix (Fin N) (Fin N) K) (G' : Matrix (Fin n) (Fin n) K) (t : K) {T : ℝ} (hT : 0 < T) :
    OrthogonalNormSquareSum.IsScaledCoisometry s (fun _ : Unit => lam) (fun _ => G) (fun _ : Unit => sg) (fun _ => G')
        (Br.brAt hN (fun _ : Unit => lam) (fun _ : Unit => sg) fun _ => t) (OrthogonalNormSquareSum.factor hN lam sg T) ↔
      0 < ScaledCoisometryNorms.brSq hN (fun _ : Unit => lam) (fun _ : Unit => sg) T ∧
        ScaledCoisometryNorms.IsScaledCoisometry s (fun _ : Unit => lam) (fun _ : Unit => sg) (fun _ => G) (fun _ => G')
          (Br.brAt hN (fun _ : Unit => lam) (fun _ : Unit => sg) fun _ => t)
          (ScaledCoisometryNorms.brSq hN (fun _ : Unit => lam) (fun _ : Unit => sg) T) := by
  rw [isScaledCoisometry_iff _ _ _ _ _ _ (factor_nonneg hN lam sg hT), ← prod_factor_sq hN _ _ hT]
  simp

end

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h K _ _ s hs ι _ N n hN lam sg h1 h2 G' hG g t T hT ht`. Use `(h K s hs ι N n hN lam sg h1 h2 G' hG T hT g t fun τ => by rw [length_eq s hs, ht τ]).2` as an intermediate fact. Rewrite `this` using `[whole_iff s hN lam sg _ G' t hT]`. Simplify `this` using `only [gramSum_eq_sumGram]`.

Introduce `h K _ _ s hs ι _ N n hN lam sg h1 h2 G' hG T hT g t ht`. Establish `ht' : ∀ τ, ((‖s (t τ)‖ ^ 2 : ℝ) : ℂ) * s (g τ) = (T : ℂ)` using `fun τ => by rw [← length_eq s hs, ht τ]`. Use `⟨fun τ => ?_, ?_⟩` and prove the remaining obligations. Use `h K s hs Unit N n hN (fun _ => lam τ) (fun _ => sg τ) (fun _ => h1 τ) (fun _ => h2 τ) (fun _ => G' τ) (fun _ => hG τ) (fun _ => g τ) (fun _ => t τ) T hT (fun _ => ht' τ)` as an intermediate fact. Rewrite using `[single_iff s hN _ _ _ _ _ hT, gramSum_eq_sumGram]`.

Conclude with `⟨this.1, this.2.1⟩`. Rewrite using `[whole_iff s hN lam sg _ G' t hT]`. Simplify `h K s hs ι N n hN lam sg h1 h2 G' hG g t T hT ht'` using `only [gramSum_eq_sumGram]`.
-/
theorem lastMapNorm_iff_brNorm : OrthogonalNormSquareSum.LastMapNorm ↔ ScaledCoisometryNorms.BrNorm := by
  constructor
  · intro h K _ _ s hs ι _ N n hN lam sg h1 h2 G' hG g t T hT ht
    have := (h K s hs ι N n hN lam sg h1 h2 G' hG T hT g t fun τ => by rw [length_eq s hs, ht τ]).2
    rw [whole_iff s hN lam sg _ G' t hT] at this
    simpa only [gramSum_eq_sumGram] using this
  · intro h K _ _ s hs ι _ N n hN lam sg h1 h2 G' hG T hT g t ht
    have ht' : ∀ τ, ((‖s (t τ)‖ ^ 2 : ℝ) : ℂ) * s (g τ) = (T : ℂ) := fun τ => by rw [← length_eq s hs, ht τ]
    refine ⟨fun τ => ?_, ?_⟩
    · have := h K s hs Unit N n hN (fun _ => lam τ) (fun _ => sg τ) (fun _ => h1 τ) (fun _ => h2 τ) (fun _ => G' τ)
        (fun _ => hG τ) (fun _ => g τ) (fun _ => t τ) T hT (fun _ => ht' τ)
      rw [single_iff s hN _ _ _ _ _ hT, gramSum_eq_sumGram]
      exact ⟨this.1, this.2.1⟩
    · rw [whole_iff s hN lam sg _ G' t hT]
      simpa only [gramSum_eq_sumGram] using h K s hs ι N n hN lam sg h1 h2 G' hG g t T hT ht'

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations. Establish `hd : (0 : ℤ) ≤ OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ)`. Use `Finset.sum_nonneg fun i _ => le_min ?_ (Finset.sum_nonneg fun j _ => (h1 τ j).1)` and prove the remaining obligations. Use `h1 τ i` as an intermediate fact.

Simplify using `only [Br.aBr, Br.bBr] at this`. Use linear arithmetic over natural numbers and integers. Establish `hs : (1 : ℤ) ≤ (lam τ).spread`. Establish `hpos : 0 < N` using `by omega`. Use `(lam τ).anti (show (⟨0, hpos⟩ : Fin N) ≤ ⟨N - 1, by omega⟩ from Fin.mk_le_mk.mpr (Nat.zero_le _))` as an intermediate fact.

Simplify using `only [DomWeight.spread, dif_pos hpos]`. Use linear arithmetic over natural numbers and integers. Establish `hd' : (0 : ℝ) ≤ ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ)` using `by exact_mod_cast hd`. Establish `hs' : (1 : ℝ) ≤ (((lam τ).spread : ℤ) : ℝ)` using `by exact_mod_cast hs`. Establish `hl : 0 ≤ Real.log (2 * a)` using `Real.log_nonneg (hs'.trans (ha τ))`.

Establish `hN0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg N`. Rewrite using `[← mul_assoc]`. Use `mul_le_mul_of_nonneg_right ?_ hl` and prove the remaining obligations. Use polynomial arithmetic with `[sq_nonneg (N : ℝ)]`.
-/
theorem last_ineq {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (h1 : ∀ τ, Br.Interlace hN (lam τ) (sg τ)) (a : ℝ) (ha : ∀ τ, (((lam τ).spread : ℤ) : ℝ) ≤ 2 * a) :
    ∑ τ, (2 * ((N : ℝ) - 1) * ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) * ((N : ℝ) - 1) / 2) * Real.log (2 * a) ≤
      2 * ∑ τ, ((N : ℝ) * ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) ^ 2) * Real.log (2 * a) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have hd : (0 : ℤ) ≤ OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) := by
    refine Finset.sum_nonneg fun i _ => le_min ?_ (Finset.sum_nonneg fun j _ => (h1 τ j).1)
    have := h1 τ i
    simp only [Br.aBr, Br.bBr] at this
    omega
  have hs : (1 : ℤ) ≤ (lam τ).spread := by
    have hpos : 0 < N := by omega
    have := (lam τ).anti (show (⟨0, hpos⟩ : Fin N) ≤ ⟨N - 1, by omega⟩ from Fin.mk_le_mk.mpr (Nat.zero_le _))
    simp only [DomWeight.spread, dif_pos hpos]
    omega
  have hd' : (0 : ℝ) ≤ ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) := by exact_mod_cast hd
  have hs' : (1 : ℝ) ≤ (((lam τ).spread : ℤ) : ℝ) := by exact_mod_cast hs
  have hl : 0 ≤ Real.log (2 * a) := Real.log_nonneg (hs'.trans (ha τ))
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hl
  nlinarith [sq_nonneg (N : ℝ)]

end GlobalTheory.BrNormCompare
