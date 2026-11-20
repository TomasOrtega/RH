import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.StarInvMulVecDotProductMulVecInvMulVec
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.QWDom

open Matrix in
/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ hA.1.eigenvalues i := by`. Break down `isEmpty_or_nonempty n with h | h` into its components or cases. Conclude with `⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩`. Take `⟨i0, -, hi0⟩` from `Finset.exists_min_image Finset.univ hA.1.eigenvalues Finset.univ_nonempty`. Conclude with `⟨_, hA.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ _)⟩`.

Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Establish `hs` using `hA.1.spectral_theorem`. Establish `h1 : c • (1 : Matrix n n ℝ) = Unitary.conjStarAlgAut ℝ _ hA.1.eigenvectorUnitary (c • 1)`. Rewrite using `[map_smul, map_one]`. Rewrite using `[h1]`.

Use `conv => arg 1`. Use `arg 1`. Rewrite using `[hs]`. Rewrite using `[← map_sub, Unitary.conjStarAlgAut_apply]`. Rewrite using `[Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff]`.

Rewrite using `[smul_one_eq_diagonal, diagonal_sub]`. Conclude with `PosSemidef.diagonal fun i => by simpa using hle i`.
-/
theorem exists_pos_posSemidef_sub_smul_one {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ (A - c • (1 : Matrix n n ℝ)).PosSemidef := by
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ hA.1.eigenvalues i := by
    rcases isEmpty_or_nonempty n with h | h
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ hA.1.eigenvalues Finset.univ_nonempty
      exact ⟨_, hA.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ _)⟩
  refine ⟨c, hc, ?_⟩
  have hs := hA.1.spectral_theorem
  have h1 : c • (1 : Matrix n n ℝ) = Unitary.conjStarAlgAut ℝ _ hA.1.eigenvectorUnitary (c • 1) := by
    rw [map_smul, map_one]
  rw [h1]
  conv => arg 1; arg 1; rw [hs]
  rw [← map_sub, Unitary.conjStarAlgAut_apply]
  rw [Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff]
  rw [smul_one_eq_diagonal, diagonal_sub]
  exact PosSemidef.diagonal fun i => by simpa using hle i

open Matrix in
/- English proof (translation)
Establish `h` using `hβ (∑ u, z u • y u)`. Simplify using `only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h`. Establish `e : ∑ u, ∑ v, z u * β (y u) (y v) * z v = ∑ x, z x * ∑ x1, z x1 * β (y x1) (y x)`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h`.
-/
theorem gram_nonneg_int {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hβ : ∀ y, 0 ≤ β y y)
    (y : Fin s → X) (z : Fin s → ℤ) : 0 ≤ ∑ u, ∑ v, z u * β (y u) (y v) * z v := by
  have h := hβ (∑ u, z u • y u)
  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h
  have e : ∑ u, ∑ v, z u * β (y u) (y v) * z v = ∑ x, z x * ∑ x1, z x1 * β (y x1) (y x) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [e]; exact h

open Matrix in
/- English proof (translation)
Use `set D : ℕ := ∏ u, (q u).den with hD`. Establish `hDpos : (0 : ℝ) < D`. Establish `: 0 < D` using `Finset.prod_pos fun u _ => (q u).den_pos`. Conclude with `this` after adjusting the coercions. Establish `hz : ∀ u, ∃ z : ℤ, (q u : ℝ) * D = z`.

Introduce `u`. Take `⟨k, hk⟩ : (q u).den ∣ D` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ u)`. Use `⟨(q u).num * k, ?_⟩` and prove the remaining obligations. Rewrite using `[hk]`. Establish `hq : (q u : ℝ) = (q u).num / (q u).den` using `by exact_mod_cast (Rat.num_div_den (q u)).symm`.

Establish `hd : ((q u).den : ℝ) ≠ 0` using `by exact_mod_cast (q u).den_nz`. Rewrite using `[hq]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use `choose z hz using hz`.

Establish `h0 : (0 : ℝ) ≤ ∑ u, ∑ v, (z u : ℝ) * (β (y u) (y v) : ℝ) * (z v : ℝ)`. Conclude with `gram_nonneg_int β hβ y z` after adjusting the coercions. Establish `: ∑ u, ∑ v, (z u : ℝ) * (β (y u) (y v) : ℝ) * (z v : ℝ) = (D : ℝ) ^ 2 * ∑ u, ∑ v, (q u : ℝ) * (β (y u) (y v) : ℝ) * (q v : ℝ)`. Simplify using `only [← hz, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h0` using `[this]`. Conclude with `(mul_nonneg_iff_of_pos_left (by positivity)).mp h0`.
-/
theorem gram_nonneg_rat {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hβ : ∀ y, 0 ≤ β y y)
    (y : Fin s → X) (q : Fin s → ℚ) :
    0 ≤ ∑ u, ∑ v, (q u : ℝ) * (β (y u) (y v) : ℝ) * (q v : ℝ) := by
  set D : ℕ := ∏ u, (q u).den with hD
  have hDpos : (0 : ℝ) < D := by
    have : 0 < D := Finset.prod_pos fun u _ => (q u).den_pos
    exact_mod_cast this
  have hz : ∀ u, ∃ z : ℤ, (q u : ℝ) * D = z := by
    intro u
    obtain ⟨k, hk⟩ : (q u).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ u)
    refine ⟨(q u).num * k, ?_⟩
    rw [hk]
    have hq : (q u : ℝ) = (q u).num / (q u).den := by exact_mod_cast (Rat.num_div_den (q u)).symm
    have hd : ((q u).den : ℝ) ≠ 0 := by exact_mod_cast (q u).den_nz
    rw [hq]; push_cast; field_simp
  choose z hz using hz
  have h0 : (0 : ℝ) ≤ ∑ u, ∑ v, (z u : ℝ) * (β (y u) (y v) : ℝ) * (z v : ℝ) := by
    exact_mod_cast gram_nonneg_int β hβ y z
  have : ∑ u, ∑ v, (z u : ℝ) * (β (y u) (y v) : ℝ) * (z v : ℝ) =
      (D : ℝ) ^ 2 * ∑ u, ∑ v, (q u : ℝ) * (β (y u) (y v) : ℝ) * (q v : ℝ) := by
    simp only [← hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [this] at h0
  exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h0

open Matrix in
/- English proof (translation)
Use `PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_` and prove the remaining obligations. Use extensionality with `u v`. Simplify using `[conjTranspose_apply, hsym (y u) (y v)]`. Establish `hcl : IsClosed {x : Fin s → ℝ | 0 ≤ ∑ u, ∑ v, x u * (β (y u) (y v) : ℝ) * x v}` using `isClosed_le continuous_const (by fun_prop)`. Establish `hx : 0 ≤ ∑ u, ∑ v, x u * (β (y u) (y v) : ℝ) * x v` using `(DenseRange.piMap fun _ => Rat.denseRange_cast (𝕜 := ℝ)).induction_on x hcl fun q => gram_nonneg_rat β hβ y q`.

Simplify using `only [star_trivial, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]`. Use `le_of_le_of_eq hx (Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_posSemidef {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (hsym : ∀ a b, β a b = β b a) (hβ : ∀ y, 0 ≤ β y y) (y : Fin s → X) :
    (Matrix.of fun u v => (β (y u) (y v) : ℝ)).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext u v
    simp [conjTranspose_apply, hsym (y u) (y v)]
  · have hcl : IsClosed {x : Fin s → ℝ | 0 ≤ ∑ u, ∑ v, x u * (β (y u) (y v) : ℝ) * x v} :=
      isClosed_le continuous_const (by fun_prop)
    have hx : 0 ≤ ∑ u, ∑ v, x u * (β (y u) (y v) : ℝ) * x v :=
      (DenseRange.piMap fun _ => Rat.denseRange_cast (𝕜 := ℝ)).induction_on x hcl
        fun q => gram_nonneg_rat β hβ y q
    simp only [star_trivial, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
    refine le_of_le_of_eq hx (Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_)
    ring

open Matrix in
/- English proof (translation)
Introduce `s W hW`. Take `⟨c, hc, hP⟩` from `exists_pos_posSemidef_sub_smul_one hW`. Use `⟨c / 2, by positivity, fun X _ β hsym hβ y => ?_⟩` and prove the remaining obligations. Establish `hM` using `gram_posSemidef β hsym hβ y`. Establish `ht` using `GlobalTheory.trace_mul_nonneg_of_posSemidef hP hM`.

Rewrite `ht` using `[Matrix.sub_mul, trace_sub, Matrix.smul_mul, Matrix.one_mul, trace_smul, sub_nonneg]`. Simplify using `only [trace, diag, mul_apply, Matrix.map_apply, Matrix.add_apply, transpose_apply, Matrix.of_apply, smul_eq_mul] at ht`. Establish `e : ∑ u, ∑ v, ((W u v + W v u : ℤ) : ℝ) * (β (y v) (y u) : ℝ) = 2 * (qW W β y : ℝ)`. Simplify using `only [qW, Int.cast_sum, Int.cast_mul, Int.cast_add, add_mul, Finset.sum_add_distrib]`. Rewrite using `[two_mul]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[hsym]`. Rewrite using `[Finset.sum_comm]`. Move the coercions through the operations in `at ht e ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem qW_ge : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∃ c : ℝ, 0 < c ∧ ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ y, 0 ≤ β y y) → ∀ y : Fin s → X, c * (∑ u, β (y u) (y u) : ℤ) ≤ (qW W β y : ℤ) := by
  intro s W hW
  obtain ⟨c, hc, hP⟩ := exists_pos_posSemidef_sub_smul_one hW
  refine ⟨c / 2, by positivity, fun X _ β hsym hβ y => ?_⟩
  have hM := gram_posSemidef β hsym hβ y
  have ht := GlobalTheory.trace_mul_nonneg_of_posSemidef hP hM
  rw [Matrix.sub_mul, trace_sub, Matrix.smul_mul, Matrix.one_mul, trace_smul, sub_nonneg] at ht
  simp only [trace, diag, mul_apply, Matrix.map_apply, Matrix.add_apply, transpose_apply, Matrix.of_apply,
    smul_eq_mul] at ht
  have e : ∑ u, ∑ v, ((W u v + W v u : ℤ) : ℝ) * (β (y v) (y u) : ℝ) = 2 * (qW W β y : ℝ) := by
    simp only [qW, Int.cast_sum, Int.cast_mul, Int.cast_add, add_mul, Finset.sum_add_distrib]
    rw [two_mul]
    congr 1
    · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [hsym]
    · rw [Finset.sum_comm]
  push_cast at ht e ⊢
  linarith

end GlobalTheory.Poinc.QWDom
