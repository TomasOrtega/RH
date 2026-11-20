import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

/- English proof (translation)
Take `⟨s, hs, hsker⟩` from `hker`. Use `choose a b ha hab using fun i => hfrac (x i)`. Use `set s0 : R := ∏ i, a i with hs0`. Establish `hs0ne : f s0 ≠ 0`. Rewrite using `[hs0, map_prod]`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun i _ => ha i`. Set `t : Fin N → R` to `fun i => b i * ∏ j ∈ Finset.univ.erase i, a j`. Establish `ht : ∀ i, f (t i) = x i * f s0`. Introduce `i`. Establish `h1 : s0 = a i * ∏ j ∈ Finset.univ.erase i, a j` using `(Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)).symm`.

Simplify using `only [t, map_mul, ← hab i]`. Rewrite using `[h1, map_mul, mul_assoc]`. Establish `hft : (f ∘ t) = f s0 • x`. Use function extensionality and compare the values at `i`. Simplify using `[ht i, mul_comm]`.

Establish `hFt : ∀ i, f ((F *ᵥ t) i) = 0`. Introduce `i`. Rewrite using `[RingHom.map_mulVec, hft, Matrix.mulVec_smul, hx]`. Simplify using the standard rewrite rules. Use `choose w hw using fun i => hsker _ (hFt i)`.

Establish `hw' : s • (F *ᵥ t) = ξ • w`. Use function extensionality and compare the values at `i`. Simplify using `using hw i`. Establish `hG : ξ • ((s * ν) • t) = ξ • (G *ᵥ w)`. Establish `h2 : G *ᵥ (s • (F *ᵥ t)) = G *ᵥ (ξ • w)` using `by rw [hw']`.

Rewrite `h2` using `[Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGF, Matrix.smul_mulVec, Matrix.one_mulVec]`. Rewrite using `[← h2]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcancel : ∀ i, (s * ν) * t i = (G *ᵥ w) i`. Introduce `i`. Establish `h3` using `congrFun hG i`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at h3`. Conclude with `(mul_cancel_left_mem_nonZeroDivisors hξ).mp h3`.

Use `⟨(f s * f ν * f s0)⁻¹ • (f ∘ w), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `h4 : f s * f ν * f s0 ≠ 0` using `mul_ne_zero (mul_ne_zero hs hν) hs0ne`. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← RingHom.map_mulVec, ← hcancel i, map_mul, map_mul, ht i]`. Clear the denominators using the available nonvanishing facts.
-/
theorem ker_map_subset_im_map (R C : Type) [CommRing R] [Field C] (f : R →+* C) (ξ ν : R) (N : ℕ)
    (F G : Matrix (Fin N) (Fin N) R) (hξ : ξ ∈ nonZeroDivisors R) (hν : f ν ≠ 0)
    (hfrac : ∀ c : C, ∃ s t : R, f s ≠ 0 ∧ c * f s = f t)
    (hker : ∃ s : R, f s ≠ 0 ∧ ∀ r : R, f r = 0 → ξ ∣ s * r)
    (hGF : G * F = (ξ * ν) • (1 : Matrix (Fin N) (Fin N) R))
    (x : Fin N → C) (hx : F.map f *ᵥ x = 0) : ∃ y : Fin N → C, x = G.map f *ᵥ y := by
  classical
  obtain ⟨s, hs, hsker⟩ := hker
  choose a b ha hab using fun i => hfrac (x i)

  set s0 : R := ∏ i, a i with hs0
  have hs0ne : f s0 ≠ 0 := by
    rw [hs0, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  let t : Fin N → R := fun i => b i * ∏ j ∈ Finset.univ.erase i, a j
  have ht : ∀ i, f (t i) = x i * f s0 := by
    intro i
    have h1 : s0 = a i * ∏ j ∈ Finset.univ.erase i, a j :=
      (Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)).symm
    simp only [t, map_mul, ← hab i]
    rw [h1, map_mul, mul_assoc]
  have hft : (f ∘ t) = f s0 • x := by
    funext i
    simp [ht i, mul_comm]

  have hFt : ∀ i, f ((F *ᵥ t) i) = 0 := by
    intro i
    rw [RingHom.map_mulVec, hft, Matrix.mulVec_smul, hx]
    simp
  choose w hw using fun i => hsker _ (hFt i)
  have hw' : s • (F *ᵥ t) = ξ • w := by
    funext i
    simpa using hw i

  have hG : ξ • ((s * ν) • t) = ξ • (G *ᵥ w) := by
    have h2 : G *ᵥ (s • (F *ᵥ t)) = G *ᵥ (ξ • w) := by rw [hw']
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGF, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h2
    rw [← h2]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hcancel : ∀ i, (s * ν) * t i = (G *ᵥ w) i := by
    intro i
    have h3 := congrFun hG i
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    exact (mul_cancel_left_mem_nonZeroDivisors hξ).mp h3

  refine ⟨(f s * f ν * f s0)⁻¹ • (f ∘ w), ?_⟩
  funext i
  have h4 : f s * f ν * f s0 ≠ 0 := mul_ne_zero (mul_ne_zero hs hν) hs0ne
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← RingHom.map_mulVec, ← hcancel i, map_mul,
    map_mul, ht i]
  field_simp

end GlobalTheory.DetInv
