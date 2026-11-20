import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory.JR

/- English proof (translation)
Establish `: CharZero F` using `h.charZero`. Establish `hsmul : ∀ (c : F) (z : E), star (c • z) = c • star z`. Introduce `c z`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, star_mul, h.star_fix, mul_comm]`. Take `⟨y, hy⟩` from `h.star_ne`.

Use `set u : E := y - star y with hu`. Establish `hsu : star u = -u` using `by rw [hu, star_sub, star_star, neg_sub]`. Establish `hu0 : u ≠ 0` using `sub_ne_zero.mpr (Ne.symm hy)`. Establish `key : ∀ s t : F, star (s • (1 : E) + t • u) = s • 1 + t • u → t = 0`. Introduce `s t hst`.

Rewrite `hst` using `[star_add, hsmul, hsmul, star_one, hsu, smul_neg, add_right_inj]`. Establish `h2 : (2 : F) • (t • u) = 0`. Rewrite using `[two_smul]`. Use `nth_rewrite 1 [← hst]`. Conclude with `neg_add_cancel _`.

Break down `smul_eq_zero.mp h2 with h2 | h2` into its components or cases. Conclude with `absurd h2 two_ne_zero`. Conclude with `(smul_eq_zero.mp h2).resolve_right hu0`. Establish `hli : LinearIndependent F ![(1 : E), u]`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `s t hst`. Establish `ht : t = 0` using `key s t (by rw [hst, star_zero])`. Use `⟨?_, ht⟩` and prove the remaining obligations. Rewrite `hst` using `[ht, zero_smul, add_zero]`. Conclude with `(smul_eq_zero.mp hst).resolve_right one_ne_zero`.

Establish `hcard : Fintype.card (Fin 2) = Module.finrank F E` using `by rw [Fintype.card_fin, h.finrank_eq]`. Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli hcard`. Establish `hb0 : b 0 = 1` using `by simp [b]`. Establish `hb1 : b 1 = u` using `by simp [b]`. Establish `hsum` using `b.sum_repr (u * u)`.

Rewrite `hsum` using `[Fin.sum_univ_two, hb0, hb1]`. Establish `hfix : star (b.repr (u * u) 0 • (1 : E) + b.repr (u * u) 1 • u) = b.repr (u * u) 0 • 1 + b.repr (u * u) 1 • u`. Rewrite using `[hsum, star_mul, hsu, neg_mul_neg]`. Establish `h1` using `key _ _ hfix`. Rewrite `hsum` using `[h1, zero_smul, add_zero]`.

Use `⟨b, b.repr (u * u) 0, hb0, by rw [hb1, hsu], ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hb1, Algebra.algebraMap_eq_smul_one]`. Conclude with `hsum.symm`. Introduce `hd`. Rewrite `hsum` using `[hd, zero_smul]`.

Conclude with `mul_self_ne_zero.mpr hu0 hsum.symm`.
-/
theorem Unram.exists_basis_antifixed (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [h : Unram F E] :
    ∃ (b : Module.Basis (Fin 2) F E) (d : F), b 0 = 1 ∧ star (b 1) = - b 1 ∧ b 1 * b 1 = algebraMap F E d ∧ d ≠ 0 := by
  have : CharZero F := h.charZero
  have hsmul : ∀ (c : F) (z : E), star (c • z) = c • star z := by
    intro c z
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, h.star_fix, mul_comm]
  obtain ⟨y, hy⟩ := h.star_ne
  set u : E := y - star y with hu
  have hsu : star u = -u := by rw [hu, star_sub, star_star, neg_sub]
  have hu0 : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have key : ∀ s t : F, star (s • (1 : E) + t • u) = s • 1 + t • u → t = 0 := by
    intro s t hst
    rw [star_add, hsmul, hsmul, star_one, hsu, smul_neg, add_right_inj] at hst
    have h2 : (2 : F) • (t • u) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hst]
      exact neg_add_cancel _
    rcases smul_eq_zero.mp h2 with h2 | h2
    · exact absurd h2 two_ne_zero
    · exact (smul_eq_zero.mp h2).resolve_right hu0
  have hli : LinearIndependent F ![(1 : E), u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := key s t (by rw [hst, star_zero])
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero] at hst
    exact (smul_eq_zero.mp hst).resolve_right one_ne_zero
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [Fintype.card_fin, h.finrank_eq]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = u := by simp [b]
  have hsum := b.sum_repr (u * u)
  rw [Fin.sum_univ_two, hb0, hb1] at hsum
  have hfix : star (b.repr (u * u) 0 • (1 : E) + b.repr (u * u) 1 • u) =
      b.repr (u * u) 0 • 1 + b.repr (u * u) 1 • u := by
    rw [hsum, star_mul, hsu, neg_mul_neg]
  have h1 := key _ _ hfix
  rw [h1, zero_smul, add_zero] at hsum
  refine ⟨b, b.repr (u * u) 0, hb0, by rw [hb1, hsu], ?_, ?_⟩
  · rw [hb1, Algebra.algebraMap_eq_smul_one]
    exact hsum.symm
  · intro hd
    rw [hd, zero_smul] at hsum
    exact mul_self_ne_zero.mpr hu0 hsum.symm

/- English proof (translation)
Establish `hrep0 : ∀ a c : K, b.repr (a • b 0 + c • b 1) 0 = a`. Introduce `a c`. Simplify using the standard rewrite rules. Establish `hrep1 : ∀ a c : K, b.repr (a • b 0 + c • b 1) 1 = c`. Introduce `a c`.

Simplify using the standard rewrite rules. Establish `hexp : ∀ y : L, y = b.repr y 0 • b 0 + b.repr y 1 • b 1`. Introduce `y`. Use `conv_lhs => rw [← b.sum_repr y]`. Rewrite using `[Fin.sum_univ_two]`.

Establish `hsmul : ∀ (c : K) (z : L), star (c • z) = c • star z`. Introduce `c z`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, star_mul, hK, mul_comm]`. Establish `hstar : ∀ y : L, star y = b.repr y 0 • b 0 + (-b.repr y 1) • b 1`. Introduce `y`.

Use `conv_lhs => rw [hexp y]`. Rewrite using `[star_add, hsmul, hsmul, hb0, star_one, hs, smul_neg, neg_smul]`. Establish `hmul : ∀ z : L, z * b 1 = (b.repr z 1 * d) • b 0 + b.repr z 0 • b 1`. Introduce `z`. Use `conv_lhs => rw [hexp z]`.

Simplify using `only [Algebra.smul_def, hb0, mul_one, map_mul, add_mul]`. Take the linear combination `(algebraMap K L (b.repr z 1)) * hd`. Establish `hc0 : ∀ z : L, b.repr (z * b 0) = b.repr z`. Introduce `z`. Rewrite using `[hb0, mul_one]`.

Establish `htr : ∀ z : L, Algebra.trace K L z = b.repr z 0 + b.repr z 0`. Introduce `z`. Rewrite using `[Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hc0, hmul, hrep1]`. Establish `hmap : ∀ x : K, algebraMap K L x = x • b 0`. Introduce `x`.

Rewrite using `[hb0, Algebra.algebraMap_eq_smul_one]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Rewrite `hx` using `[hmap]`.

Use `hrep0 x 0` as an intermediate fact. Rewrite `this` using `[zero_smul, add_zero, hx]`. Simplify using `at this`. Conclude with `this.symm`. Introduce `y`.

Rewrite using `[Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]`. Simplify using `only [Algebra.leftMulMatrix_eq_repr_mul, hc0, hmul, hrep0, hrep1]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Algebra.smul_def, hb0, mul_one, map_mul, map_sub, map_neg]`. Take the linear combination `(algebraMap K L (b.repr y 1) * algebraMap K L (b.repr y 1)) * hd`.

Use `_ = y * star y := by rw [← hexp y, ← hstar y]`. Introduce `y`. Rewrite using `[htr, hmap]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [add_smul, neg_smul]`.

Normalize the expressions using the abelian group laws. Use `_ = y + star y := by rw [← hexp y, ← hstar y]`. Introduce `y' hy'`. Establish `g1` using `hy' 1`. Establish `g2` using `hy' (b 1)`.

Rewrite `g1` using `[mul_one, htr, hstar, hrep0]`. Rewrite `g2` using `[hmul, htr, hrep0, hstar, hrep1]`. Establish `hp : b.repr y' 0 = 0`. Establish `h3 : (2 : K) * b.repr y' 0 = 0` using `by rw [two_mul]; exact g1`. Conclude with `h2.mul_right_eq_zero.mp h3`.

Establish `hq : b.repr y' 1 = 0`. Establish `h3 : (2 : K) * (b.repr y' 1 * d) = 0` using `by linear_combination -g2`. Conclude with `hdu.mul_left_eq_zero.mp (h2.mul_right_eq_zero.mp h3)`. Rewrite using `[hexp y', hp, hq, zero_smul, zero_smul, add_zero]`.
-/
theorem quadratic_star_structure {K L : Type} [CommRing K] [CommRing L] [StarRing L] [Algebra K L]
    (b : Module.Basis (Fin 2) K L) (d : K) (hb0 : b 0 = 1) (hs : star (b 1) = - b 1)
    (hd : b 1 * b 1 = algebraMap K L d) (hK : ∀ x : K, star (algebraMap K L x) = algebraMap K L x)
    (hdu : IsUnit d) (h2 : IsUnit (2 : K)) :
    Function.Injective (algebraMap K L) ∧ (∀ y : L, algebraMap K L (Algebra.norm K y) = y * star y) ∧
      (∀ y : L, algebraMap K L (Algebra.trace K L y) = y + star y) ∧
      (∀ y' : L, (∀ y : L, Algebra.trace K L (star y' * y) = 0) → y' = 0) := by
  have hrep0 : ∀ a c : K, b.repr (a • b 0 + c • b 1) 0 = a := by
    intro a c; simp
  have hrep1 : ∀ a c : K, b.repr (a • b 0 + c • b 1) 1 = c := by
    intro a c; simp
  have hexp : ∀ y : L, y = b.repr y 0 • b 0 + b.repr y 1 • b 1 := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    rw [Fin.sum_univ_two]
  have hsmul : ∀ (c : K) (z : L), star (c • z) = c • star z := by
    intro c z
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, hK, mul_comm]
  have hstar : ∀ y : L, star y = b.repr y 0 • b 0 + (-b.repr y 1) • b 1 := by
    intro y
    conv_lhs => rw [hexp y]
    rw [star_add, hsmul, hsmul, hb0, star_one, hs, smul_neg, neg_smul]
  have hmul : ∀ z : L, z * b 1 = (b.repr z 1 * d) • b 0 + b.repr z 0 • b 1 := by
    intro z
    conv_lhs => rw [hexp z]
    simp only [Algebra.smul_def, hb0, mul_one, map_mul, add_mul]
    linear_combination (algebraMap K L (b.repr z 1)) * hd
  have hc0 : ∀ z : L, b.repr (z * b 0) = b.repr z := by
    intro z; rw [hb0, mul_one]
  have htr : ∀ z : L, Algebra.trace K L z = b.repr z 0 + b.repr z 0 := by
    intro z
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul, hc0, hmul, hrep1]
  have hmap : ∀ x : K, algebraMap K L x = x • b 0 := by
    intro x; rw [hb0, Algebra.algebraMap_eq_smul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hmap] at hx
    have := hrep0 x 0
    rw [zero_smul, add_zero, hx] at this
    simp at this
    exact this.symm
  · intro y
    rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hc0, hmul, hrep0, hrep1]
    calc _ = (b.repr y 0 • b 0 + b.repr y 1 • b 1) * (b.repr y 0 • b 0 + (-b.repr y 1) • b 1) := by
          simp only [Algebra.smul_def, hb0, mul_one, map_mul, map_sub, map_neg]
          linear_combination (algebraMap K L (b.repr y 1) * algebraMap K L (b.repr y 1)) * hd
      _ = y * star y := by rw [← hexp y, ← hstar y]
  · intro y
    rw [htr, hmap]
    calc _ = (b.repr y 0 • b 0 + b.repr y 1 • b 1) + (b.repr y 0 • b 0 + (-b.repr y 1) • b 1) := by
          simp only [add_smul, neg_smul]; abel
      _ = y + star y := by rw [← hexp y, ← hstar y]
  · intro y' hy'
    have g1 := hy' 1
    have g2 := hy' (b 1)
    rw [mul_one, htr, hstar, hrep0] at g1
    rw [hmul, htr, hrep0, hstar, hrep1] at g2
    have hp : b.repr y' 0 = 0 := by
      have h3 : (2 : K) * b.repr y' 0 = 0 := by rw [two_mul]; exact g1
      exact h2.mul_right_eq_zero.mp h3
    have hq : b.repr y' 1 = 0 := by
      have h3 : (2 : K) * (b.repr y' 1 * d) = 0 := by linear_combination -g2
      exact hdu.mul_left_eq_zero.mp (h2.mul_right_eq_zero.mp h3)
    rw [hexp y', hp, hq, zero_smul, zero_smul, add_zero]

/- English proof (translation)
Introduce `F E _ _ _ _ hU A`. Establish `: CharZero F` using `hU.charZero`. Take `⟨b, d, hb0, hs, hd, hd0⟩` from `Unram.exists_basis_antifixed F E`. Set `B : Module.Basis (Fin 2) A.K A.L` to `A.push.symm.out.basis b`. Establish `hB : ∀ i, B i = algebraMap E A.L (b i)` using `fun i => by`.

Simplify using `[B, IsBaseChange.basis_apply]`. Establish `key` using `quadratic_star_structure B (algebraMap F A.K d) (by rw [hB, hb0, map_one]) (by rw [hB, A.star_E, hs, map_neg]) (by`. Rewrite using `[hB, ← map_mul, hd, ← IsScalarTower.algebraMap_apply F E A.L, ← IsScalarTower.algebraMap_apply F A.K A.L])`. Use the proof step `A.star_K ((isUnit_iff_ne_zero.mpr hd0).map _)`. Use the proof step `(by`.

Establish `h2F` using `(isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : F) ≠ 0)).map (algebraMap F A.K)`. Rewrite using `[map_ofNat] at h2F)` and apply the resulting hypothesis. Conclude with `⟨⟨B⟩, key.1, key.2.1, key.2.2.1, key.2.2.2⟩`.
-/
theorem Et.quadratic_structure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Nonempty (Module.Basis (Fin 2) A.K A.L) ∧ Function.Injective (algebraMap A.K A.L) ∧ (∀ y : A.L, algebraMap A.K A.L (A.NL y) = y * star y) ∧ (∀ y : A.L, algebraMap A.K A.L (Algebra.trace A.K A.L y) = y + star y) ∧ (∀ y' : A.L, (∀ y : A.L, Algebra.trace A.K A.L (star y' * y) = 0) → y' = 0) := by
  intro F E _ _ _ _ hU A
  have : CharZero F := hU.charZero
  obtain ⟨b, d, hb0, hs, hd, hd0⟩ := Unram.exists_basis_antifixed F E
  let B : Module.Basis (Fin 2) A.K A.L := A.push.symm.out.basis b
  have hB : ∀ i, B i = algebraMap E A.L (b i) := fun i => by
    simp [B, IsBaseChange.basis_apply]
  have key := quadratic_star_structure B (algebraMap F A.K d) (by rw [hB, hb0, map_one])
    (by rw [hB, A.star_E, hs, map_neg])
    (by
      rw [hB, ← map_mul, hd, ← IsScalarTower.algebraMap_apply F E A.L,
        ← IsScalarTower.algebraMap_apply F A.K A.L])
    A.star_K ((isUnit_iff_ne_zero.mpr hd0).map _)
    (by
      have h2F := (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : F) ≠ 0)).map (algebraMap F A.K)
      rwa [map_ofNat] at h2F)
  exact ⟨⟨B⟩, key.1, key.2.1, key.2.2.1, key.2.2.2⟩

end GlobalTheory.JR
