import Mathlib

namespace GlobalTheory

open Matrix

/- English proof (translation)
Use `set G : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => (b (v i) (v j) : ℝ) with hG`. Establish `hint : ∀ m : Fin r → ℤ, 0 ≤ ∑ i, ∑ j, (m i : ℝ) * (m j : ℝ) * G i j`. Introduce `m`. Establish `key : (∑ i, ∑ j, m i * m j * b (v i) (v j) : ℤ) = b (∑ i, m i • v i) (∑ j, m j • v j)`. Simplify using `only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hsymm (v i) (v j)]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : (0:ℝ) ≤ ((∑ i, ∑ j, m i * m j * b (v i) (v j) : ℤ) : ℝ)`. Rewrite using `[key]`.

Conclude with `hpos _` after adjusting the coercions. Simplify `h0` using `[hG]`. Establish `hrat : ∀ c : Fin r → ℚ, 0 ≤ ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j`. Introduce `c`. Use `set N : ℕ := ∏ i, (c i).den with hN`.

Establish `hNpos : (0:ℝ) < N`. Establish `: 0 < N` using `Finset.prod_pos (fun i _ => (c i).den_pos)`. Conclude with `this` after adjusting the coercions. Establish `hm : ∀ i, ∃ k : ℤ, (k : ℝ) = N * (c i : ℝ)`. Introduce `i`.

Take `⟨t, ht⟩ : (c i).den ∣ N` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ i)`. Use `⟨(c i).num * t, ?_⟩` and prove the remaining obligations. Establish `h1 : ((c i).num : ℚ) = c i * (c i).den` using `(Rat.mul_den_eq_num (c i)).symm`. Establish `h2 : ((c i).num : ℝ) = (c i : ℝ) * (c i).den` using `by exact_mod_cast h1`. Rewrite using `[ht]`.

Use `push_cast`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree. Use `choose m hm using hm`. Establish `h3` using `hint m`.

Rewrite `h3` using `[hm]`. Establish `e : ∑ i, ∑ j, ((N:ℝ) * c i) * (N * c j) * G i j = (N:ℝ) ^ 2 * ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j`. Repeatedly rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h3` using `[e]`. Conclude with `(mul_nonneg_iff_of_pos_left (by positivity)).mp h3`. Establish `hreal : ∀ x : Fin r → ℝ, 0 ≤ ∑ i, ∑ j, x i * x j * G i j`. Introduce `x`. Establish `hd : DenseRange (Pi.map fun (_ : Fin r) (q : ℚ) => (q : ℝ))` using `DenseRange.piMap fun _ => Rat.denseRange_cast`.

Use `hd.induction_on (p := fun x : Fin r → ℝ => 0 ≤ ∑ i, ∑ j, x i * x j * G i j) x ?_ ?_` and prove the remaining obligations. Conclude with `isClosed_le continuous_const (by fun_prop)`. Introduce `c`. Simplify `hrat c` using `[Pi.map]`. Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_` and prove the remaining obligations.

Use extensionality with `i j`. Simplify using `[hG, Matrix.conjTranspose_apply, hsymm]`. Introduce `x`. Establish `e : star x ⬝ᵥ (G *ᵥ x) = ∑ i, ∑ j, x i * x j * G i j`. Simplify using `only [dotProduct, mulVec, star_trivial, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hreal x`.
-/
theorem gram_posSemidef_of_int_form {X : Type} [AddCommGroup X] {r : ℕ}
    (b : LinearMap.BilinForm ℤ X) (hsymm : ∀ y z, b y z = b z y) (hpos : ∀ y, 0 ≤ b y y)
    (v : Fin r → X) : (Matrix.of fun i j => (b (v i) (v j) : ℝ)).PosSemidef := by
  set G : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => (b (v i) (v j) : ℝ) with hG
  have hint : ∀ m : Fin r → ℤ, 0 ≤ ∑ i, ∑ j, (m i : ℝ) * (m j : ℝ) * G i j := by
    intro m
    have key : (∑ i, ∑ j, m i * m j * b (v i) (v j) : ℤ)
        = b (∑ i, m i • v i) (∑ j, m j • v j) := by
      simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsymm (v i) (v j)]; ring
    have h0 : (0:ℝ) ≤ ((∑ i, ∑ j, m i * m j * b (v i) (v j) : ℤ) : ℝ) := by
      rw [key]; exact_mod_cast hpos _
    simpa [hG] using h0
  have hrat : ∀ c : Fin r → ℚ, 0 ≤ ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j := by
    intro c
    set N : ℕ := ∏ i, (c i).den with hN
    have hNpos : (0:ℝ) < N := by
      have : 0 < N := Finset.prod_pos (fun i _ => (c i).den_pos)
      exact_mod_cast this
    have hm : ∀ i, ∃ k : ℤ, (k : ℝ) = N * (c i : ℝ) := by
      intro i
      obtain ⟨t, ht⟩ : (c i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      refine ⟨(c i).num * t, ?_⟩
      have h1 : ((c i).num : ℚ) = c i * (c i).den := (Rat.mul_den_eq_num (c i)).symm
      have h2 : ((c i).num : ℝ) = (c i : ℝ) * (c i).den := by exact_mod_cast h1
      rw [ht]; push_cast
      rw [h2]; ring
    choose m hm using hm
    have h3 := hint m
    simp_rw [hm] at h3
    have e : ∑ i, ∑ j, ((N:ℝ) * c i) * (N * c j) * G i j
        = (N:ℝ) ^ 2 * ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j := by
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e] at h3
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h3
  have hreal : ∀ x : Fin r → ℝ, 0 ≤ ∑ i, ∑ j, x i * x j * G i j := by
    intro x
    have hd : DenseRange (Pi.map fun (_ : Fin r) (q : ℚ) => (q : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hd.induction_on (p := fun x : Fin r → ℝ => 0 ≤ ∑ i, ∑ j, x i * x j * G i j) x ?_ ?_
    · exact isClosed_le continuous_const (by fun_prop)
    · intro c
      simpa [Pi.map] using hrat c
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [hG, Matrix.conjTranspose_apply, hsymm]
  · intro x
    have e : star x ⬝ᵥ (G *ᵥ x) = ∑ i, ∑ j, x i * x j * G i j := by
      simp only [dotProduct, mulVec, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]; exact hreal x

end GlobalTheory
