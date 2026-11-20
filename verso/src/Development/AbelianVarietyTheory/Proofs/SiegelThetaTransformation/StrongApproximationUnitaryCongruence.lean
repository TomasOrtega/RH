import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.UnApprox

open Filter Topology IsDedekindDomain

noncomputable section

section Algebra

variable {K : Type} [Field K] {r : ℕ}

def cay (S : Matrix (Fin r) (Fin r) K) : Matrix (Fin r) (Fin r) K := (1 + S)⁻¹ * (1 - S)

/- English proof (translation)
Establish `hu : IsUnit (1 + A).det` using `isUnit_iff_ne_zero.mpr hA`. Establish `h1 : (1 + A)⁻¹ * (1 + A) = 1` using `Matrix.nonsing_inv_mul _ hu`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_add, two_smul]`. Use `congr 1`.

Normalize the expressions using the abelian group laws. Use `_ = (2 : K) • (1 + A)⁻¹ := by rw [Matrix.mul_smul, Matrix.mul_one]`.
-/
theorem one_add_cay {A : Matrix (Fin r) (Fin r) K} (hA : (1 + A).det ≠ 0) :
    1 + cay A = (2 : K) • (1 + A)⁻¹ := by
  have hu : IsUnit (1 + A).det := isUnit_iff_ne_zero.mpr hA
  have h1 : (1 + A)⁻¹ * (1 + A) = 1 := Matrix.nonsing_inv_mul _ hu
  calc 1 + cay A = (1 + A)⁻¹ * (1 + A) + (1 + A)⁻¹ * (1 - A) := by rw [h1]; rfl
    _ = (1 + A)⁻¹ * ((2 : K) • (1 : Matrix (Fin r) (Fin r) K)) := by
        rw [← Matrix.mul_add, two_smul]; congr 1; abel
    _ = (2 : K) • (1 + A)⁻¹ := by rw [Matrix.mul_smul, Matrix.mul_one]

/- English proof (translation)
Rewrite using `[one_add_cay hA, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Conclude with `mul_ne_zero (pow_ne_zero _ two_ne_zero) (inv_ne_zero hA)`.
-/
theorem det_one_add_cay [CharZero K] {A : Matrix (Fin r) (Fin r) K} (hA : (1 + A).det ≠ 0) :
    (1 + cay A).det ≠ 0 := by
  rw [one_add_cay hA, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (inv_ne_zero hA)

/- English proof (translation)
Establish `hu : IsUnit (1 + A).det` using `isUnit_iff_ne_zero.mpr hA`. Establish `h1 : (1 + A)⁻¹ * (1 + A) = 1` using `Matrix.nonsing_inv_mul _ hu`. Establish `h2 : (1 + A) * (1 + A)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`. Establish `h20 : (2 : K) ≠ 0` using `two_ne_zero`. Establish `hinv : (1 + cay A)⁻¹ = (2 : K)⁻¹ • (1 + A)`.

Rewrite using `[one_add_cay hA]`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, h2, smul_smul, inv_mul_cancel₀ h20, one_smul]`. Establish `hsub : 1 - cay A = (2 : K) • ((1 + A)⁻¹ * A)`. Combine the equalities or inequalities in the displayed calculation.

Use `show (1 + cay A)⁻¹ * (1 - cay A) = A`. Rewrite using `[hinv, hsub, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ h20, one_smul, ← Matrix.mul_assoc, h2, Matrix.one_mul]`.
-/
theorem cay_cay [CharZero K] {A : Matrix (Fin r) (Fin r) K} (hA : (1 + A).det ≠ 0) : cay (cay A) = A := by
  have hu : IsUnit (1 + A).det := isUnit_iff_ne_zero.mpr hA
  have h1 : (1 + A)⁻¹ * (1 + A) = 1 := Matrix.nonsing_inv_mul _ hu
  have h2 : (1 + A) * (1 + A)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h20 : (2 : K) ≠ 0 := two_ne_zero
  have hinv : (1 + cay A)⁻¹ = (2 : K)⁻¹ • (1 + A) := by
    rw [one_add_cay hA]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, h2, smul_smul, inv_mul_cancel₀ h20, one_smul]
  have hsub : 1 - cay A = (2 : K) • ((1 + A)⁻¹ * A) := by
    calc 1 - cay A = (1 + A)⁻¹ * (1 + A) - (1 + A)⁻¹ * (1 - A) := by rw [h1]; rfl
      _ = (1 + A)⁻¹ * ((2 : K) • A) := by rw [← Matrix.mul_sub, two_smul]; congr 1; abel
      _ = _ := by rw [Matrix.mul_smul]
  show (1 + cay A)⁻¹ * (1 - cay A) = A
  rw [hinv, hsub, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ h20, one_smul,
    ← Matrix.mul_assoc, h2, Matrix.one_mul]

variable [StarRing K]

/- English proof (translation)
Establish `hu : IsUnit (1 + S).det` using `isUnit_iff_ne_zero.mpr hd`. Establish `h1 : (1 + S)⁻¹ * (1 + S) = 1` using `Matrix.nonsing_inv_mul _ hu`. Establish `hSG : S * G = -(G * Sᴴ)` using `eq_neg_of_add_eq_zero_left hS`. Establish `hM : (1 - S) * G = G * (1 + S)ᴴ`. Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.one_mul, hSG, Matrix.mul_add, Matrix.mul_one, sub_neg_eq_add]`.

Establish `hP : (1 + S) * G = G * (1 - S)ᴴ`. Rewrite using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.add_mul, Matrix.one_mul, hSG, Matrix.mul_sub, Matrix.mul_one, ← sub_eq_add_neg]`. Establish `hc : (1 + S)ᴴ * (1 - S)ᴴ = (1 - S)ᴴ * (1 + S)ᴴ`. Rewrite using `[← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul]`. Use `congr 1`.

Use `noncomm_ring`. Unfold `cay`. Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (1 - S) G, hM]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (1 + S)ᴴ (1 - S)ᴴ, hc]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc G (1 - S)ᴴ, ← hP]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc (1 + S)⁻¹ (1 + S), h1, Matrix.one_mul, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one, Matrix.mul_one]`.
-/
theorem cay_unitary {G S : Matrix (Fin r) (Fin r) K} (hS : S * G + G * Sᴴ = 0) (hd : (1 + S).det ≠ 0) :
    cay S * G * (cay S)ᴴ = G := by
  have hu : IsUnit (1 + S).det := isUnit_iff_ne_zero.mpr hd
  have h1 : (1 + S)⁻¹ * (1 + S) = 1 := Matrix.nonsing_inv_mul _ hu
  have hSG : S * G = -(G * Sᴴ) := eq_neg_of_add_eq_zero_left hS
  have hM : (1 - S) * G = G * (1 + S)ᴴ := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.one_mul, hSG,
      Matrix.mul_add, Matrix.mul_one, sub_neg_eq_add]
  have hP : (1 + S) * G = G * (1 - S)ᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.add_mul, Matrix.one_mul, hSG,
      Matrix.mul_sub, Matrix.mul_one, ← sub_eq_add_neg]
  have hc : (1 + S)ᴴ * (1 - S)ᴴ = (1 - S)ᴴ * (1 + S)ᴴ := by
    rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul]; congr 1; noncomm_ring
  unfold cay
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (1 - S) G, hM]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (1 + S)ᴴ (1 - S)ᴴ, hc]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc G (1 - S)ᴴ, ← hP]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (1 + S)⁻¹ (1 + S), h1, Matrix.one_mul, ← Matrix.conjTranspose_mul, h1,
    Matrix.conjTranspose_one, Matrix.mul_one]

def skew (G S : Matrix (Fin r) (Fin r) K) (e : K) : Matrix (Fin r) (Fin r) K :=
  e • S - star e • (G * Sᴴ * G⁻¹)

/- English proof (translation)
Establish `hu : IsUnit G.det` using `isUnit_iff_ne_zero.mpr hd`. Establish `h1 : G⁻¹ * G = 1` using `Matrix.nonsing_inv_mul _ hu`. Establish `hi : (G⁻¹)ᴴ = G⁻¹` using `by rw [Matrix.conjTranspose_nonsing_inv, hG]`. Unfold `skew`. Rewrite using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, star_star, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hi, hG]`.

Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hu]`. Normalize the expressions using the abelian group laws.
-/
theorem skew_skew {G : Matrix (Fin r) (Fin r) K} (hG : Gᴴ = G) (hd : G.det ≠ 0)
    (S : Matrix (Fin r) (Fin r) K) (e : K) : skew G S e * G + G * (skew G S e)ᴴ = 0 := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hd
  have h1 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hu
  have hi : (G⁻¹)ᴴ = G⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hG]
  unfold skew
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, star_star,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hi, hG]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, h1,
    Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  abel

def near (G A : Matrix (Fin r) (Fin r) K) (e : K) : Matrix (Fin r) (Fin r) K :=
  if (1 + skew G (cay A) e).det = 0 then 1 else cay (skew G (cay A) e)

/- English proof (translation)
Unfold `near`. Use `split_ifs with h`. Simplify using the standard rewrite rules. Conclude with `cay_unitary (skew_skew hG hd _ _) h`.
-/
theorem near_unitary {G : Matrix (Fin r) (Fin r) K} (hG : Gᴴ = G) (hd : G.det ≠ 0)
    (A : Matrix (Fin r) (Fin r) K) (e : K) : near G A e * G * (near G A e)ᴴ = G := by
  unfold near
  split_ifs with h
  · simp
  · exact cay_unitary (skew_skew hG hd _ _) h

/- English proof (translation)
Use `set C := cay A with hCdef`. Establish `hC1 : (1 + C).det ≠ 0` using `det_one_add_cay hA`. Establish `hT : Tendsto (fun k => skew G C (e k)) atTop (𝓝 C)`. Use `(h1.smul_const C).sub (h0.smul_const (G * Cᴴ * G⁻¹))` as an intermediate fact. Simplify `this` using `[skew]`.

Establish `hdet : Tendsto (fun k => (1 + skew G C (e k)).det) atTop (𝓝 (1 + C).det)` using `((Continuous.matrix_det continuous_id).tendsto (1 + C)).comp (tendsto_const_nhds.add hT)`. Establish `hev : ∀ᶠ k in atTop, (1 + skew G C (e k)).det ≠ 0` using `hdet.eventually_ne hC1`. Establish `hinv : ContinuousAt Inv.inv (1 + C)`. Apply `continuousAt_matrix_inv` to reduce the goal to its premises. Rewrite using `[Ring.inverse_eq_inv']`.

Conclude with `continuousAt_inv₀ hC1`. Establish `hlim : Tendsto (fun k => cay (skew G C (e k))) atTop (𝓝 (cay C))` using `(hinv.tendsto.comp (tendsto_const_nhds.add hT)).mul (tendsto_const_nhds.sub hT)`. Rewrite `hlim` using `[hCdef, cay_cay hA]`. Use `hlim.congr' ?_` and prove the remaining obligations. Use `filter_upwards [hev] with k hk`.

Simplify using `[near, hk, C]`.
-/
theorem near_tendsto [CharZero K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]
    (G : Matrix (Fin r) (Fin r) K) {A : Matrix (Fin r) (Fin r) K} (hA : (1 + A).det ≠ 0) {e : ℕ → K}
    (h1 : Tendsto e atTop (𝓝 1)) (h0 : Tendsto (fun k => star (e k)) atTop (𝓝 0)) :
    Tendsto (fun k => near G A (e k)) atTop (𝓝 A) := by
  set C := cay A with hCdef
  have hC1 : (1 + C).det ≠ 0 := det_one_add_cay hA
  have hT : Tendsto (fun k => skew G C (e k)) atTop (𝓝 C) := by
    have := (h1.smul_const C).sub (h0.smul_const (G * Cᴴ * G⁻¹))
    simpa [skew] using this
  have hdet : Tendsto (fun k => (1 + skew G C (e k)).det) atTop (𝓝 (1 + C).det) :=
    ((Continuous.matrix_det continuous_id).tendsto (1 + C)).comp (tendsto_const_nhds.add hT)
  have hev : ∀ᶠ k in atTop, (1 + skew G C (e k)).det ≠ 0 := hdet.eventually_ne hC1
  have hinv : ContinuousAt Inv.inv (1 + C) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hC1
  have hlim : Tendsto (fun k => cay (skew G C (e k))) atTop (𝓝 (cay C)) :=
    (hinv.tendsto.comp (tendsto_const_nhds.add hT)).mul (tendsto_const_nhds.sub hT)
  rw [hCdef, cay_cay hA] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev] with k hk
  simp [near, hk, C]

omit [StarRing K] in
/- English proof (translation)
Establish `hp : (-A).charpoly ≠ 0` using `(Matrix.charpoly_monic _).ne_zero`. Establish `: Infinite K` using `Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective`. Take `⟨c, hc⟩` from `Infinite.exists_notMem_finset (insert 0 (insert (-1) (-A).charpoly.roots.toFinset))`. Simplify using `only [Finset.mem_insert, Multiset.mem_toFinset, not_or] at hc`. Take `⟨hc0, hc1, hcr⟩` from `hc`.

Use `⟨c, hc0, fun h => hc1 (by linear_combination h), ?_⟩` and prove the remaining obligations. Establish `hev : (-A).charpoly.eval c ≠ 0` using `fun h => hcr ((Polynomial.mem_roots hp).mpr h)`. Rewrite `hev` using `[Matrix.eval_charpoly]`. Establish `hM : 1 + c⁻¹ • A = c⁻¹ • (Matrix.scalar (Fin r) c - -A)`. Rewrite using `[sub_neg_eq_add, smul_add, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_smul, inv_mul_cancel₀ hc0, one_smul]`.

Rewrite using `[hM, Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc0)) hev`.
-/
theorem exists_scalar [CharZero K] (A : Matrix (Fin r) (Fin r) K) :
    ∃ c : K, c ≠ 0 ∧ 1 + c ≠ 0 ∧ (1 + c⁻¹ • A).det ≠ 0 := by
  classical
  have hp : (-A).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (insert 0 (insert (-1) (-A).charpoly.roots.toFinset))
  simp only [Finset.mem_insert, Multiset.mem_toFinset, not_or] at hc
  obtain ⟨hc0, hc1, hcr⟩ := hc
  refine ⟨c, hc0, fun h => hc1 (by linear_combination h), ?_⟩
  have hev : (-A).charpoly.eval c ≠ 0 := fun h => hcr ((Polynomial.mem_roots hp).mpr h)
  rw [Matrix.eval_charpoly] at hev
  have hM : 1 + c⁻¹ • A = c⁻¹ • (Matrix.scalar (Fin r) c - -A) := by
    rw [sub_neg_eq_add, smul_add, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_smul,
      inv_mul_cancel₀ hc0, one_smul]
  rw [hM, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc0)) hev

/- English proof (translation)
Take `⟨c, hc0, hc1, hdet⟩` from `exists_scalar A`. Use `⟨fun k => near G (c • (1 : Matrix (Fin r) (Fin r) K)) (e k) * near G (c⁻¹ • A) (e k), ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Simplify using `only [Matrix.conjTranspose_mul]`. Rewrite using `[show ∀ U V W X : Matrix (Fin r) (Fin r) K, U * V * G * (W * X) = U * (V * G * W) * X by intros; simp only [Matrix.mul_assoc], near_unitary hG hd, near_unitary hG hd]`.

Introduce `w hw1 hw0 i j`. Set `_` to `w.toNormedField`. Establish `h1 : Tendsto e atTop (𝓝 1)` using `tendsto_iff_norm_sub_tendsto_zero.2 hw1`. Establish `h0 : Tendsto (fun k => star (e k)) atTop (𝓝 0)` using `tendsto_iff_norm_sub_tendsto_zero.2 (by simp only [sub_zero]; exact hw0)`. Establish `hs : (1 + c • (1 : Matrix (Fin r) (Fin r) K)).det ≠ 0`.

Rewrite using `[show (1 : Matrix (Fin r) (Fin r) K) + c • 1 = (1 + c) • 1 by rw [add_smul, one_smul], Matrix.det_smul, Matrix.det_one, _root_.mul_one]`. Conclude with `pow_ne_zero _ hc1`. Establish `hg` using `(near_tendsto G hs h1 h0).mul (near_tendsto G hdet h1 h0)`. Rewrite `hg` using `[Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hc0, one_smul]`. Establish `hij : Tendsto (fun k => (near G (c • (1 : Matrix (Fin r) (Fin r) K)) (e k) * near G (c⁻¹ • A) (e k)) i j) atTop (𝓝 (A i j))` using `((continuous_apply j).tendsto _).comp (((continuous_apply i).tendsto _).comp hg)`.

Conclude with `tendsto_iff_norm_sub_tendsto_zero.1 hij`.
-/
theorem exists_seq [CharZero K] {G : Matrix (Fin r) (Fin r) K} (hG : Gᴴ = G) (hd : G.det ≠ 0)
    (A : Matrix (Fin r) (Fin r) K) (e : ℕ → K) :
    ∃ g : ℕ → Matrix (Fin r) (Fin r) K, (∀ k, g k * G * (g k)ᴴ = G) ∧
      ∀ w : AbsoluteValue K ℝ, Tendsto (fun k => w (e k - 1)) atTop (𝓝 0) →
        Tendsto (fun k => w (star (e k))) atTop (𝓝 0) →
        ∀ i j, Tendsto (fun k => w (g k i j - A i j)) atTop (𝓝 0) := by
  obtain ⟨c, hc0, hc1, hdet⟩ := exists_scalar A
  refine ⟨fun k => near G (c • (1 : Matrix (Fin r) (Fin r) K)) (e k) * near G (c⁻¹ • A) (e k), ?_, ?_⟩
  · intro k
    simp only [Matrix.conjTranspose_mul]
    rw [show ∀ U V W X : Matrix (Fin r) (Fin r) K, U * V * G * (W * X) = U * (V * G * W) * X by
        intros; simp only [Matrix.mul_assoc], near_unitary hG hd, near_unitary hG hd]
  · intro w hw1 hw0 i j
    let _ := w.toNormedField
    have h1 : Tendsto e atTop (𝓝 1) := tendsto_iff_norm_sub_tendsto_zero.2 hw1
    have h0 : Tendsto (fun k => star (e k)) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.2 (by simp only [sub_zero]; exact hw0)
    have hs : (1 + c • (1 : Matrix (Fin r) (Fin r) K)).det ≠ 0 := by
      rw [show (1 : Matrix (Fin r) (Fin r) K) + c • 1 = (1 + c) • 1 by rw [add_smul, one_smul],
        Matrix.det_smul, Matrix.det_one, _root_.mul_one]
      exact pow_ne_zero _ hc1
    have hg := (near_tendsto G hs h1 h0).mul (near_tendsto G hdet h1 h0)
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hc0, one_smul] at hg
    have hij : Tendsto (fun k => (near G (c • (1 : Matrix (Fin r) (Fin r) K)) (e k) *
        near G (c⁻¹ • A) (e k)) i j) atTop (𝓝 (A i j)) :=
      ((continuous_apply j).tendsto _).comp (((continuous_apply i).tendsto _).comp hg)
    exact tendsto_iff_norm_sub_tendsto_zero.1 hij

end Algebra

section Arith

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hb` using `NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v`. Establish `hle : ∀ c : 𝓞 E, NumberField.HeightOneSpectrum.adicAbv E v (c : E) ≤ 1` using `fun c => IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := E) v hb c`. Establish `hq1 : NumberField.HeightOneSpectrum.adicAbv E v (a : E) < 1` using `(IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_lt_one_iff (K := E) v hb a).2 ha`. Establish `hq0 : 0 ≤ NumberField.HeightOneSpectrum.adicAbv E v (a : E)` using `AbsoluteValue.nonneg _ _`. Use `squeeze_zero (fun k => AbsoluteValue.nonneg _ _) (fun k => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)` and prove the remaining obligations.

Use `push_cast`. Rewrite using `[map_mul, map_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tendsto_abv {v : HeightOneSpectrum (𝓞 E)} {a : 𝓞 E} (ha : a ∈ v.asIdeal) (x : ℕ → 𝓞 E) :
    Tendsto (fun k => NumberField.HeightOneSpectrum.adicAbv E v ((x k * a ^ k : 𝓞 E) : E)) atTop (𝓝 0) := by
  have hb := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  have hle : ∀ c : 𝓞 E, NumberField.HeightOneSpectrum.adicAbv E v (c : E) ≤ 1 := fun c =>
    IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := E) v hb c
  have hq1 : NumberField.HeightOneSpectrum.adicAbv E v (a : E) < 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_lt_one_iff (K := E) v hb a).2 ha
  have hq0 : 0 ≤ NumberField.HeightOneSpectrum.adicAbv E v (a : E) := AbsoluteValue.nonneg _ _
  refine squeeze_zero (fun k => AbsoluteValue.nonneg _ _) (fun k => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
  push_cast
  rw [map_mul, map_pow]
  calc _ ≤ 1 * NumberField.HeightOneSpectrum.adicAbv E v (a : E) ^ k :=
        mul_le_mul_of_nonneg_right (hle _) (pow_nonneg hq0 k)
    _ = _ := _root_.one_mul _

/- English proof (translation)
Establish `hb` using `NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v`. Take `⟨a, ha, j, -, hj⟩` from `Ideal.exist_integer_multiples_notMem (K := E) v.isPrime.ne_top (Finset.univ : Finset (Option J)) (fun o => o.elim 1 y) (Finset.mem_univ none) one_ne_zero`. Take `⟨a', ha'⟩` from `ha none (Finset.mem_univ _)`. Establish `ha1 : a = (a' : E)` using `by simpa using ha'.symm`. Use `⟨a', fun hmem => hj ?_, fun i => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `ha j (Finset.mem_univ _)`. Use `(FractionalIdeal.mem_coeIdeal _).2 ⟨c, ?_, hc⟩` and prove the remaining obligations. Establish `hlt : NumberField.HeightOneSpectrum.adicAbv E v (a' : E) < 1` using `(IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_lt_one_iff (K := E) v hb a').2 hmem`. Establish `hfj : NumberField.HeightOneSpectrum.adicAbv E v ((fun o : Option J => o.elim 1 y) j) ≤ 1`. Consider the cases of `j with`.

Consider the case `none => simp`. Consider the case `some i => exact hy i`. Apply `(IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_lt_one_iff (K := E) v hb c).1` to reduce the goal to its premises. Use `show NumberField.HeightOneSpectrum.adicAbv E v (algebraMap (𝓞 E) E c) < 1`. Rewrite using `[hc, map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Use `ha (some i) (Finset.mem_univ _)` as an intermediate fact. Rewrite `this` using `[ha1]`. Conclude with `this`.
-/
private lemma exists_not_mem_mul_isInteger_of_adicAbv_le_one {E : Type} [Field E] [NumberField E] {J : Type} [Fintype J]
    (v : HeightOneSpectrum (𝓞 E)) (y : J → E)
    (hy : ∀ i, NumberField.HeightOneSpectrum.adicAbv E v (y i) ≤ 1) :
    ∃ b : 𝓞 E, b ∉ v.asIdeal ∧ ∀ i, IsLocalization.IsInteger (𝓞 E) ((b : E) * y i) := by
  classical
  have hb := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  obtain ⟨a, ha, j, -, hj⟩ := Ideal.exist_integer_multiples_notMem (K := E) v.isPrime.ne_top
    (Finset.univ : Finset (Option J)) (fun o => o.elim 1 y) (Finset.mem_univ none) one_ne_zero
  obtain ⟨a', ha'⟩ := ha none (Finset.mem_univ _)
  have ha1 : a = (a' : E) := by simpa using ha'.symm
  refine ⟨a', fun hmem => hj ?_, fun i => ?_⟩
  · obtain ⟨c, hc⟩ := ha j (Finset.mem_univ _)
    refine (FractionalIdeal.mem_coeIdeal _).2 ⟨c, ?_, hc⟩
    have hlt : NumberField.HeightOneSpectrum.adicAbv E v (a' : E) < 1 :=
      (IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_lt_one_iff (K := E) v hb a').2 hmem
    have hfj : NumberField.HeightOneSpectrum.adicAbv E v ((fun o : Option J => o.elim 1 y) j) ≤ 1 := by
      cases j with
      | none => simp
      | some i => exact hy i
    apply (IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_lt_one_iff (K := E) v hb c).1
    show NumberField.HeightOneSpectrum.adicAbv E v (algebraMap (𝓞 E) E c) < 1
    rw [hc, map_mul]
    calc _ ≤ NumberField.HeightOneSpectrum.adicAbv E v a * 1 :=
          mul_le_mul_of_nonneg_left hfj (AbsoluteValue.nonneg _ _)
      _ < 1 := by rw [_root_.mul_one, ha1]; exact hlt
  · have := ha (some i) (Finset.mem_univ _)
    rw [ha1] at this
    exact this

/- English proof (translation)
Set `Q : Ideal (𝓞 E)` to `{ carrier := {s | ∀ i, IsLocalization.IsInteger (𝓞 E) ((s : E) * y i)} add_mem' := fun {a b} ha hb i => by`. Use `IsLocalization.isInteger_add (ha i) (hb i)` as an intermediate fact. Use `push_cast`. Rewrite using `[add_mul]` and apply the resulting hypothesis. Use the proof step `zero_mem' := fun i => by`.

Simplify using `using (IsLocalization.isInteger_zero : IsLocalization.IsInteger (𝓞 E) (0 : E))`. Use the proof step `smul_mem' := fun c {s} hs i => by`. Use `IsLocalization.isInteger_smul (a := c) (hs i)` as an intermediate fact. Simplify using `only [smul_eq_mul]`. Use `push_cast`.

Rewrite `this` using `[Algebra.smul_def, ← _root_.mul_assoc]`. Conclude with `this }`. Establish `htop : Q ⊔ 𝔪 = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`.

Establish `hPbot : P ≠ ⊥` using `fun h => h𝔪 (eq_bot_iff.2 (h ▸ le_sup_right.trans hle))`. Set `v : HeightOneSpectrum (𝓞 E)` to `⟨P, hP.isPrime, hPbot⟩`. Establish `hv : v.asIdeal ∣ 𝔪` using `Ideal.dvd_iff_le.2 (le_sup_right.trans hle)`. Take `⟨b, hbv, hbi⟩` from `exists_not_mem_mul_isInteger_of_adicAbv_le_one v y (fun i => hy v hv i)`. Conclude with `hbv (hle (Ideal.mem_sup_left (show b ∈ Q from hbi)))`.

Establish `h1 : (1 : 𝓞 E) ∈ Q ⊔ 𝔪` using `by rw [htop]; exact Submodule.mem_top`. Take `⟨s, hs, m, hm, hsm⟩` from `Submodule.mem_sup.1 h1`. Use `⟨s, Ideal.isCoprime_iff_exists.2 ⟨s, Ideal.mem_span_singleton_self s, m, hm, hsm⟩, fun i => ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `hs i`. Conclude with `⟨b, hb.symm⟩`.
-/
theorem exists_denom {J : Type} [Fintype J] {𝔪 : Ideal (𝓞 E)} (h𝔪 : 𝔪 ≠ ⊥) (y : J → E)
    (hy : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔪 → ∀ i, NumberField.HeightOneSpectrum.adicAbv E v (y i) ≤ 1) :
    ∃ s : 𝓞 E, IsCoprime (Ideal.span {s}) 𝔪 ∧ ∀ i, ∃ b : 𝓞 E, (s : E) * y i = (b : E) := by
  classical
  let Q : Ideal (𝓞 E) :=
    { carrier := {s | ∀ i, IsLocalization.IsInteger (𝓞 E) ((s : E) * y i)}
      add_mem' := fun {a b} ha hb i => by
        have := IsLocalization.isInteger_add (ha i) (hb i)
        push_cast
        rwa [add_mul]
      zero_mem' := fun i => by
        simpa using (IsLocalization.isInteger_zero : IsLocalization.IsInteger (𝓞 E) (0 : E))
      smul_mem' := fun c {s} hs i => by
        have := IsLocalization.isInteger_smul (a := c) (hs i)
        simp only [smul_eq_mul]
        push_cast
        rw [Algebra.smul_def, ← _root_.mul_assoc] at this
        exact this }
  have htop : Q ⊔ 𝔪 = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have hPbot : P ≠ ⊥ := fun h => h𝔪 (eq_bot_iff.2 (h ▸ le_sup_right.trans hle))
    let v : HeightOneSpectrum (𝓞 E) := ⟨P, hP.isPrime, hPbot⟩
    have hv : v.asIdeal ∣ 𝔪 := Ideal.dvd_iff_le.2 (le_sup_right.trans hle)
    obtain ⟨b, hbv, hbi⟩ := exists_not_mem_mul_isInteger_of_adicAbv_le_one v y (fun i => hy v hv i)
    exact hbv (hle (Ideal.mem_sup_left (show b ∈ Q from hbi)))
  have h1 : (1 : 𝓞 E) ∈ Q ⊔ 𝔪 := by rw [htop]; exact Submodule.mem_top
  obtain ⟨s, hs, m, hm, hsm⟩ := Submodule.mem_sup.1 h1
  refine ⟨s, Ideal.isCoprime_iff_exists.2 ⟨s, Ideal.mem_span_singleton_self s, m, hm, hsm⟩, fun i => ?_⟩
  obtain ⟨b, hb⟩ := hs i
  exact ⟨b, hb.symm⟩

variable [IsCMField E]

/- English proof (translation)
Establish `hle : conjI 𝔪 ≤ 𝔪.comap (IsCMField.ringOfIntegersComplexConj E)`. Unfold `conjI`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `a ⟨b', hb', hab⟩`. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap]`.

Use `hb' using 1` and compare the differences between its conclusion and the goal. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj, hab]`. Conclude with `IsCMField.complexConj_apply_apply _ _`. Conclude with `hle hb`.
-/
theorem conj_mem {𝔪 : Ideal (𝓞 E)} {b : 𝓞 E} (hb : b ∈ conjI 𝔪) :
    IsCMField.ringOfIntegersComplexConj E b ∈ 𝔪 := by
  have hle : conjI 𝔪 ≤ 𝔪.comap (IsCMField.ringOfIntegersComplexConj E) := by
    unfold conjI
    rw [Ideal.span_le]
    rintro a ⟨b', hb', hab⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    convert hb' using 1
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, hab]
    exact IsCMField.complexConj_apply_apply _ _
  exact hle hb

/- English proof (translation)
Simplify using `only [herm, cc, dotProduct, mulVec, Finset.mul_sum, _root_.mul_assoc, Pi.star_apply]`. Both sides reduce to the same expression.
-/
theorem herm_eq {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ G *ᵥ star y := by
  simp only [herm, cc, dotProduct, mulVec, Finset.mul_sum, _root_.mul_assoc, Pi.star_apply]
  rfl

end Arith

/- English proof (translation)
Introduce `E _ _ _ r X 𝔪 h𝔪 hco A N`. Take `⟨m, hm, m', hm', hmm⟩` from `Ideal.isCoprime_iff_exists.1 hco`. Establish `hc : ∀ k : ℕ, IsCoprime (m ^ k) (m' ^ k)` using `fun k => (show IsCoprime m m' from ⟨1, 1, by rw [_root_.one_mul, _root_.one_mul, hmm]⟩).pow`. Use `choose u u' hu using hc`. Set `e : ℕ → E` to `fun k => ((u' k * m' ^ k : 𝓞 E) : E)`.

Establish `hG : X.Gmᴴ = X.Gm`. Use extensionality with `a b`. Rewrite using `[Matrix.conjTranspose_apply]`. Conclude with `X.Gm_herm b a`. Take `⟨h, hun, hconv⟩` from `exists_seq hG X.Gm_det ((A : Matrix (Fin r) (Fin r) E)ᵀ) e`.

Establish `hv1 : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔪 → ∀ i j, Tendsto (fun k => NumberField.HeightOneSpectrum.adicAbv E v (h k i j - (A : Matrix (Fin r) (Fin r) E)ᵀ i j)) atTop (𝓝 0)`. Introduce `v hv`. Establish `h𝔪v : 𝔪 ≤ v.asIdeal` using `Ideal.dvd_iff_le.1 hv`. Apply `hconv` to reduce the goal to its premises. Use `(tendsto_abv (v := v) (h𝔪v hm) (fun k => -u k)).congr (fun k => ?_)` and prove the remaining obligations.

Use `congr 1`. Use `congrArg (fun z : 𝓞 E => (z : E)) (hu k)` as an intermediate fact. Simplify using `only [e]`. Move the coercions through the operations in `at this ⊢`. Take the linear combination `(-1 : E) * this`.

Use `(tendsto_abv (v := v) (h𝔪v (conj_mem hm')) (fun k => IsCMField.ringOfIntegersComplexConj E (u' k))).congr (fun k => ?_)` and prove the remaining obligations. Use `congr 1`. Rewrite using `[← map_pow, ← map_mul, IsCMField.coe_ringOfIntegersComplexConj]`. Both sides reduce to the same expression. Establish `hN : 𝔪 ^ N ≠ ⊥`.

Rewrite using `[← Ideal.zero_eq_bot]`. Conclude with `pow_ne_zero N (by rwa [Ideal.zero_eq_bot])`. Take `⟨mu, hmu, hmu0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hN`. Establish `hmuE : (mu : E) ≠ 0` using `by exact_mod_cast hmu0`. Establish `hmupos : ∀ v : HeightOneSpectrum (𝓞 E), 0 < NumberField.HeightOneSpectrum.adicAbv E v (mu : E)` using `fun v => AbsoluteValue.pos _ hmuE`.

Establish `hfin` using `Ideal.finite_factors (R := 𝓞 E) (I := 𝔪) (by rwa [Ideal.zero_eq_bot])`. Establish `hev : ∀ᶠ k in atTop, ∀ v ∈ {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ 𝔪}, ∀ i j, NumberField.HeightOneSpectrum.adicAbv E v (h k i j - (A : Matrix (Fin r) (Fin r) E)ᵀ i j) < NumberField.HeightOneSpectrum.adicAbv E v (mu : E)`. Rewrite using `[Filter.eventually_all_finite hfin]`. Introduce `v hv`. Rewrite using `[Filter.eventually_all]`.

Introduce `i`. Rewrite using `[Filter.eventually_all]`. Introduce `j`. Conclude with `(tendsto_order.1 (hv1 v hv i j)).2 _ (hmupos v)`. Take `⟨k, hk⟩` from `hev.exists`.

Use `set g : Matrix (Fin r) (Fin r) E := (h k)ᵀ with hgdef`. Establish `hug : gᵀ * X.Gm * g.map star = X.Gm`. Rewrite using `[hgdef, Matrix.transpose_transpose]`. Conclude with `hun k`. Establish `hdet : g.det ≠ 0`.

Introduce `h0`. Use `congrArg Matrix.det hug` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul]`. Conclude with `X.Gm_det this.symm`. Establish `hstar : ∀ z : Fin r → E, star (g *ᵥ z) = g.map star *ᵥ star z`.

Introduce `z`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, star_sum, star_mul']`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g hdet, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y show herm X.Gm (g *ᵥ x) (g *ᵥ y) = herm X.Gm x y`.

Rewrite using `[herm_eq, herm_eq, hstar, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose g x, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hug]`. Set `y : Fin r × Fin r → E` to `fun p => (g p.1 p.2 - (A : Matrix (Fin r) (Fin r) E) p.1 p.2) / (mu : E)`. Establish `hy : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔪 → ∀ p, NumberField.HeightOneSpectrum.adicAbv E v (y p) ≤ 1`. Introduce `v hv p`. Simplify using `only [y, map_div₀]`.

Rewrite using `[div_le_one (hmupos v)]`. Conclude with `(hk v hv p.2 p.1).le`. Take `⟨s, hs, hsb⟩` from `exists_denom h𝔪 y hy`. Use `⟨s, hs, fun i j => ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `hsb (i, j)`.

Use `⟨b * mu, Ideal.mul_mem_left _ _ hmu, ?_⟩` and prove the remaining obligations. Use `show (s : E) * (g i j - (A : Matrix (Fin r) (Fin r) E) i j) = ((b * mu : 𝓞 E) : E)`. Use `push_cast`. Establish `hb' : (s : E) * ((g i j - (A : Matrix (Fin r) (Fin r) E) i j) / (mu : E)) = b` using `hb`. Rewrite `hb'` using `[mul_div_assoc', div_eq_iff hmuE]`.

Take the linear combination `hb'`.
-/
theorem weak_approx :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (conjI 𝔪) → ∀ (A : GL (Fin r) E) (N : ℕ), ∃ ga : GL (Fin r) E, IsUn X ga ∧ ∃ s : 𝓞 E, IsCoprime (Ideal.span {s}) 𝔪 ∧ ∀ i j, ∃ b ∈ 𝔪 ^ N, (s : E) * ((ga : Matrix (Fin r) (Fin r) E) i j - (A : Matrix (Fin r) (Fin r) E) i j) = (b : E) := by
  intro E _ _ _ r X 𝔪 h𝔪 hco A N
  classical
  obtain ⟨m, hm, m', hm', hmm⟩ := Ideal.isCoprime_iff_exists.1 hco
  have hc : ∀ k : ℕ, IsCoprime (m ^ k) (m' ^ k) := fun k =>
    (show IsCoprime m m' from ⟨1, 1, by rw [_root_.one_mul, _root_.one_mul, hmm]⟩).pow
  choose u u' hu using hc
  let e : ℕ → E := fun k => ((u' k * m' ^ k : 𝓞 E) : E)
  have hG : X.Gmᴴ = X.Gm := by
    ext a b
    rw [Matrix.conjTranspose_apply]
    exact X.Gm_herm b a
  obtain ⟨h, hun, hconv⟩ := exists_seq hG X.Gm_det ((A : Matrix (Fin r) (Fin r) E)ᵀ) e
  have hv1 : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔪 → ∀ i j,
      Tendsto (fun k => NumberField.HeightOneSpectrum.adicAbv E v
        (h k i j - (A : Matrix (Fin r) (Fin r) E)ᵀ i j)) atTop (𝓝 0) := by
    intro v hv
    have h𝔪v : 𝔪 ≤ v.asIdeal := Ideal.dvd_iff_le.1 hv
    apply hconv
    · refine (tendsto_abv (v := v) (h𝔪v hm) (fun k => -u k)).congr (fun k => ?_)
      congr 1
      have := congrArg (fun z : 𝓞 E => (z : E)) (hu k)
      simp only [e]
      push_cast at this ⊢
      linear_combination (-1 : E) * this
    · refine (tendsto_abv (v := v) (h𝔪v (conj_mem hm'))
        (fun k => IsCMField.ringOfIntegersComplexConj E (u' k))).congr (fun k => ?_)
      congr 1
      rw [← map_pow, ← map_mul, IsCMField.coe_ringOfIntegersComplexConj]
      rfl
  have hN : 𝔪 ^ N ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact pow_ne_zero N (by rwa [Ideal.zero_eq_bot])
  obtain ⟨mu, hmu, hmu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  have hmuE : (mu : E) ≠ 0 := by exact_mod_cast hmu0
  have hmupos : ∀ v : HeightOneSpectrum (𝓞 E), 0 < NumberField.HeightOneSpectrum.adicAbv E v (mu : E) :=
    fun v => AbsoluteValue.pos _ hmuE
  have hfin := Ideal.finite_factors (R := 𝓞 E) (I := 𝔪) (by rwa [Ideal.zero_eq_bot])
  have hev : ∀ᶠ k in atTop, ∀ v ∈ {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ 𝔪}, ∀ i j,
      NumberField.HeightOneSpectrum.adicAbv E v (h k i j - (A : Matrix (Fin r) (Fin r) E)ᵀ i j) <
        NumberField.HeightOneSpectrum.adicAbv E v (mu : E) := by
    rw [Filter.eventually_all_finite hfin]
    intro v hv
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    exact (tendsto_order.1 (hv1 v hv i j)).2 _ (hmupos v)
  obtain ⟨k, hk⟩ := hev.exists
  set g : Matrix (Fin r) (Fin r) E := (h k)ᵀ with hgdef
  have hug : gᵀ * X.Gm * g.map star = X.Gm := by
    rw [hgdef, Matrix.transpose_transpose]
    exact hun k
  have hdet : g.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hug
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at this
    exact X.Gm_det this.symm
  have hstar : ∀ z : Fin r → E, star (g *ᵥ z) = g.map star *ᵥ star z := by
    intro z
    ext i
    simp [Matrix.mulVec, dotProduct, star_sum, star_mul']
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g hdet, ?_, ?_⟩
  · intro x y
    show herm X.Gm (g *ᵥ x) (g *ᵥ y) = herm X.Gm x y
    rw [herm_eq, herm_eq, hstar, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose g x,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hug]
  · let y : Fin r × Fin r → E := fun p => (g p.1 p.2 - (A : Matrix (Fin r) (Fin r) E) p.1 p.2) / (mu : E)
    have hy : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔪 → ∀ p,
        NumberField.HeightOneSpectrum.adicAbv E v (y p) ≤ 1 := by
      intro v hv p
      simp only [y, map_div₀]
      rw [div_le_one (hmupos v)]
      exact (hk v hv p.2 p.1).le
    obtain ⟨s, hs, hsb⟩ := exists_denom h𝔪 y hy
    refine ⟨s, hs, fun i j => ?_⟩
    obtain ⟨b, hb⟩ := hsb (i, j)
    refine ⟨b * mu, Ideal.mul_mem_left _ _ hmu, ?_⟩
    show (s : E) * (g i j - (A : Matrix (Fin r) (Fin r) E) i j) = ((b * mu : 𝓞 E) : E)
    push_cast
    have hb' : (s : E) * ((g i j - (A : Matrix (Fin r) (Fin r) E) i j) / (mu : E)) = b := hb
    rw [mul_div_assoc', div_eq_iff hmuE] at hb'
    linear_combination hb'

end

end GlobalTheory.UnApprox
