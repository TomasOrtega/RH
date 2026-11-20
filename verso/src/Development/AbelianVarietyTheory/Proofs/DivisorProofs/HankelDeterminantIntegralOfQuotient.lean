import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

open PowerSeries Finset

/- English proof (translation)
Establish `hi : (i : ℕ) + 1 ≤ n + 1` using `by omega`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun l => (if l ≤ (i : ℕ) then coeff ((i : ℕ) - l) E else 0) * coeff (l + s) Q) (n + 1)]`. Simplify using `only [ite_mul, zero_mul]`. Rewrite using `[← Finset.sum_filter]`. Establish `hf : (range (n + 1)).filter (fun l => l ≤ (i : ℕ)) = range ((i : ℕ) + 1)`.

Use extensionality with `l`. Simplify using `only [mem_filter, mem_range]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hf, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => coeff a (trunc ((i : ℕ) + 1) E : PowerSeries F) * coeff b Q)]`. Simplify using `only [Polynomial.coeff_coe, coeff_trunc, ite_mul, zero_mul]`.

Rewrite using `[← Finset.sum_filter]`. Establish `hg : (range ((i : ℕ) + s).succ).filter (fun a => a < (i : ℕ) + 1) = range ((i : ℕ) + 1)`. Use extensionality with `l`. Simplify using `only [mem_filter, mem_range, Nat.succ_eq_add_one]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hg, ← Finset.sum_range_reflect]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite `hl` using `[mem_range]`. Rewrite using `[show (i : ℕ) - ((i : ℕ) + 1 - 1 - l) = l by omega, show (i : ℕ) + 1 - 1 - l + s = (i : ℕ) + s - l by omega]`.
-/
theorem hankelInt_sumLemma {F : Type} [Field F] (E Q : PowerSeries F) (n : ℕ) (i : Fin (n + 1)) (s : ℕ) :
    ∑ l : Fin (n + 1), (if (l : ℕ) ≤ i then coeff ((i : ℕ) - l) E else 0) * coeff ((l : ℕ) + s) Q =
      coeff ((i : ℕ) + s) ((trunc ((i : ℕ) + 1) E : PowerSeries F) * Q) := by
  have hi : (i : ℕ) + 1 ≤ n + 1 := by omega
  rw [Fin.sum_univ_eq_sum_range (fun l => (if l ≤ (i : ℕ) then coeff ((i : ℕ) - l) E else 0) * coeff (l + s) Q) (n + 1)]
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hf : (range (n + 1)).filter (fun l => l ≤ (i : ℕ)) = range ((i : ℕ) + 1) := by
    ext l; simp only [mem_filter, mem_range]; omega
  rw [hf, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => coeff a (trunc ((i : ℕ) + 1) E : PowerSeries F) * coeff b Q)]
  simp only [Polynomial.coeff_coe, coeff_trunc, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hg : (range ((i : ℕ) + s).succ).filter (fun a => a < (i : ℕ) + 1) = range ((i : ℕ) + 1) := by
    ext l; simp only [mem_filter, mem_range, Nat.succ_eq_add_one]; omega
  rw [hg, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [mem_range] at hl
  rw [show (i : ℕ) - ((i : ℕ) + 1 - 1 - l) = l by omega, show (i : ℕ) + 1 - 1 - l + s = (i : ℕ) + s - l by omega]

/- English proof (translation)
Introduce `O F _ _ ι e ψ φ n h`. Use `set E := PowerSeries.map ι e with hE`. Use `set P : ℕ → PowerSeries F := fun i => (trunc (i + 1) E : PowerSeries F) with hP`. Set `N : Matrix (Fin (n + 1)) (Fin (n + 1)) O` to `Matrix.of fun i j => coeff ((i : ℕ) + j) ((trunc ((i : ℕ) + 1) e : PowerSeries O) * ψ - (e - (trunc ((j : ℕ) + 1) e : PowerSeries O)) * ψ)`. Set `T : Matrix (Fin (n + 1)) (Fin (n + 1)) F` to `Matrix.of fun i l => if (l : ℕ) ≤ i then coeff ((i : ℕ) - l) E else 0`.

Set `H : Matrix (Fin (n + 1)) (Fin (n + 1)) F` to `Matrix.of fun i j => coeff ((i : ℕ) + j) φ`. Establish `hmapP : ∀ k, PowerSeries.map ι (trunc k e : PowerSeries O) = (trunc k E : PowerSeries F)`. Apply the tactic sequence `intro k; ext m; simp only [hE, coeff_map, Polynomial.coeff_coe, coeff_trunc]; split_ifs <;> simp`. Establish `hX : ∀ i : ℕ, X ^ (i + 1) ∣ E - P i`. Introduce `i`.

Rewrite using `[X_pow_dvd_iff]`. Introduce `m hm`. Simplify using `[hP, Polynomial.coeff_coe, coeff_trunc, hm]`. Establish `hdiv : ∀ i j : ℕ, coeff (i + j) ((E - P i) * (E - P j) * φ) = 0`. Introduce `i j`.

Establish `h3 : X ^ (i + 1 + (j + 1)) ∣ (E - P i) * (E - P j) * φ`. Rewrite using `[pow_add]`. Conclude with `Dvd.dvd.mul_right (mul_dvd_mul (hX i) (hX j)) φ`. Conclude with `X_pow_dvd_iff.mp h3 _ (by omega)`. Establish `hent : N.map ι = T * H * T.transpose`.

Use extensionality with `i j`. Establish `inner : ∀ l : Fin (n + 1), ∑ m, H l m * T.transpose m j = coeff ((l : ℕ) + j) (P j * φ)`. Introduce `l`. Rewrite using `[Nat.add_comm (l : ℕ) (j : ℕ)]`. Use `Eq.trans ?_ (hankelInt_sumLemma E φ n j l)` and prove the remaining obligations.

Use `sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [H, T, Matrix.of_apply, Matrix.transpose_apply]`. Rewrite using `[mul_comm, add_comm (l : ℕ)]`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_apply]`. Simplify using `only [Matrix.mul_apply, inner]`.

Rewrite using `[show (∑ x, T i x * coeff ((x : ℕ) + j) (P j * φ)) = coeff ((i : ℕ) + j) (P i * (P j * φ)) from hankelInt_sumLemma E (P j * φ) n i j]`. Simplify using `only [Matrix.map_apply, N, Matrix.of_apply]`. Establish `key : PowerSeries.map ι ((trunc ((i : ℕ) + 1) e : PowerSeries O) * ψ - (e - (trunc ((j : ℕ) + 1) e : PowerSeries O)) * ψ) = P i * (P j * φ) - (E - P i) * (E - P j) * φ`. Rewrite using `[map_sub, map_mul, map_mul, map_sub, hmapP, hmapP, ← h, ← hE]`. Simplify using `only [hP]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← coeff_map, key, map_sub, hdiv, sub_zero]`. Establish `hT : T.det = ι (constantCoeff e) ^ (n + 1)`. Rewrite using `[Matrix.det_of_lowerTriangular T ?_]`. Simplify using `[T, E, Finset.prod_const]`.

Introduce `i j hij`. Establish `hij' : i < j` using `hij`. Establish `h1 : ¬ j ≤ i` using `not_le.mpr hij'`. Establish `h2 : ¬ ((j : ℕ) ≤ i)` using `h1`. Simplify using `[T, h1, h2]`.

Use `⟨N.det, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hent, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hT]`. Use `show _ = _ * H.det`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hankel_integral : ∀ (O F : Type) [CommRing O] [Field F] (ι : O →+* F) (e ψ : PowerSeries O) (φ : PowerSeries F) (n : ℕ), PowerSeries.map ι e * φ = PowerSeries.map ι ψ → ∃ z : O, ι z = ι (PowerSeries.constantCoeff e) ^ (2 * (n + 1)) * hankel (fun i => PowerSeries.coeff i φ) n := by
  intro O F _ _ ι e ψ φ n h
  set E := PowerSeries.map ι e with hE
  set P : ℕ → PowerSeries F := fun i => (trunc (i + 1) E : PowerSeries F) with hP
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) O := Matrix.of fun i j =>
    coeff ((i : ℕ) + j) ((trunc ((i : ℕ) + 1) e : PowerSeries O) * ψ - (e - (trunc ((j : ℕ) + 1) e : PowerSeries O)) * ψ)
  let T : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i l =>
    if (l : ℕ) ≤ i then coeff ((i : ℕ) - l) E else 0
  let H : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j => coeff ((i : ℕ) + j) φ
  have hmapP : ∀ k, PowerSeries.map ι (trunc k e : PowerSeries O) = (trunc k E : PowerSeries F) := by
    intro k; ext m; simp only [hE, coeff_map, Polynomial.coeff_coe, coeff_trunc]; split_ifs <;> simp
  have hX : ∀ i : ℕ, X ^ (i + 1) ∣ E - P i := by
    intro i; rw [X_pow_dvd_iff]; intro m hm
    simp [hP, Polynomial.coeff_coe, coeff_trunc, hm]
  have hdiv : ∀ i j : ℕ, coeff (i + j) ((E - P i) * (E - P j) * φ) = 0 := by
    intro i j
    have h3 : X ^ (i + 1 + (j + 1)) ∣ (E - P i) * (E - P j) * φ := by
      rw [pow_add]; exact Dvd.dvd.mul_right (mul_dvd_mul (hX i) (hX j)) φ
    exact X_pow_dvd_iff.mp h3 _ (by omega)
  have hent : N.map ι = T * H * T.transpose := by
    ext i j
    have inner : ∀ l : Fin (n + 1), ∑ m, H l m * T.transpose m j = coeff ((l : ℕ) + j) (P j * φ) := by
      intro l
      rw [Nat.add_comm (l : ℕ) (j : ℕ)]
      refine Eq.trans ?_ (hankelInt_sumLemma E φ n j l)
      refine sum_congr rfl fun m _ => ?_
      simp only [H, T, Matrix.of_apply, Matrix.transpose_apply]; rw [mul_comm, add_comm (l : ℕ)]
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.mul_apply, inner]
    rw [show (∑ x, T i x * coeff ((x : ℕ) + j) (P j * φ)) = coeff ((i : ℕ) + j) (P i * (P j * φ)) from hankelInt_sumLemma E (P j * φ) n i j]
    simp only [Matrix.map_apply, N, Matrix.of_apply]
    have key : PowerSeries.map ι ((trunc ((i : ℕ) + 1) e : PowerSeries O) * ψ - (e - (trunc ((j : ℕ) + 1) e : PowerSeries O)) * ψ)
        = P i * (P j * φ) - (E - P i) * (E - P j) * φ := by
      rw [map_sub, map_mul, map_mul, map_sub, hmapP, hmapP, ← h, ← hE]
      simp only [hP]; ring
    rw [← coeff_map, key, map_sub, hdiv, sub_zero]
  have hT : T.det = ι (constantCoeff e) ^ (n + 1) := by
    rw [Matrix.det_of_lowerTriangular T ?_]
    · simp [T, E, Finset.prod_const]
    · intro i j hij
      have hij' : i < j := hij
      have h1 : ¬ j ≤ i := not_le.mpr hij'
      have h2 : ¬ ((j : ℕ) ≤ i) := h1
      simp [T, h1, h2]
  refine ⟨N.det, ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hent, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hT]
  show _ = _ * H.det
  ring

end GlobalTheory.Nef
