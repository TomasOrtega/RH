import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PiNonunit

noncomputable section
open Matrix

namespace PI.SqPair.LCP

section Lin
variable {R : Type} [CommRing R] [StarRing R] {ι : Type} [Fintype ι]

/- English proof (translation)
Simplify using `only [hf, star_add, add_dotProduct]`.
-/
lemma sg_hf_add_left (A : Matrix ι ι R) (x x' y : ι → R) :
    hf A (x + x') y = hf A x y + hf A x' y := by
  simp only [hf, star_add, add_dotProduct]

/- English proof (translation)
Simplify using `only [hf, mulVec_add, dotProduct_add]`.
-/
lemma sg_hf_add_right (A : Matrix ι ι R) (x y y' : ι → R) :
    hf A x (y + y') = hf A x y + hf A x y' := by
  simp only [hf, mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `only [hf, dotProduct, mulVec, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sg_hf_smul_left (A : Matrix ι ι R) (c : R) (x y : ι → R) :
    hf A (c • x) y = star c * hf A x y := by
  simp only [hf, dotProduct, mulVec, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hf, mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
lemma sg_hf_smul_right (A : Matrix ι ι R) (c : R) (x y : ι → R) :
    hf A x (c • y) = c * hf A x y := by
  simp only [hf, mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Use `conv_rhs => rw [← hA]`. Simplify using `only [hf, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, conjTranspose_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sg_hf_star {A : Matrix ι ι R} (hA : Aᴴ = A) (x y : ι → R) :
    star (hf A x y) = hf A y x := by
  conv_rhs => rw [← hA]
  simp only [hf, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, conjTranspose_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Lin

/- English proof (translation)
Introduce `R _ _ R₀ _ ϖ hin κ _ _ A A' h k hP hnb`. Use `haveI := hin.dom`. Take `⟨a, x, y, ha0, hak, hxy, ⟨c, hc⟩, ⟨v, hv⟩, ⟨w, hw⟩⟩` from `h5 R R₀ ϖ hin (Fin 2 ⊕ κ) A A' h k hP hnb`. Establish `hA : Aᴴ = A` using `hP.1.1`. Establish `hsϖ : star ϖ = ϖ` using `(hin.fix ϖ).1 hin.pi_mem`.

Establish `hyx : hf A y x = 1` using `by rw [← sg_hf_star hA x y, hxy, star_one]`. Establish `hpow0 : ϖ ^ (2 * a) ≠ 0` using `pow_ne_zero _ hin.pi_ne`. Establish `hcR : c ∈ R₀`. Rewrite using `[hin.fix]`. Establish `h1` using `sg_hf_star hA x x`.

Rewrite `h1` using `[hc, star_mul, star_pow, hsϖ]`. Conclude with `mul_left_cancel₀ hpow0 (by rw [mul_comm, h1])`. Establish `hβR : hf A y y ∈ R₀` using `(hin.fix _).2 (sg_hf_star hA y y)`. Establish `hϖm : (⟨ϖ, hin.pi_mem⟩ : R₀) ∈ IsLocalRing.maximalIdeal R₀`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Introduce `hu`. Conclude with `hin.pi_nonunit (hu.map R₀.subtype)`. Establish `hmα : ϖ ^ (2 * a) * c ∈ R₀` using `R₀.mul_mem (R₀.pow_mem hin.pi_mem _) hcR`. Establish `hαm : (⟨ϖ ^ (2 * a) * c, hmα⟩ : R₀) ∈ IsLocalRing.maximalIdeal R₀`. Establish `e : (⟨ϖ ^ (2 * a) * c, hmα⟩ : R₀) = ⟨ϖ, hin.pi_mem⟩ ^ (2 * a) * ⟨c, hcR⟩` using `Subtype.ext (by simp)`.

Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖm _ (by omega))`. Take `⟨W, hWdet, hW, s', hs'⟩` from `h8 R R₀ ϖ hin ⟨ϖ ^ (2 * a) * c, hmα⟩ ⟨hf A y y, hβR⟩ hαm`. Establish `e00` using `congrFun (congrFun hW 0) 0`. Establish `e11` using `congrFun (congrFun hW 1) 1`.

Establish `e01` using `congrFun (congrFun hW 0) 1`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, hyp, conjTranspose_apply] at e00 e11 e01 hs'`. Establish `hk : ϖ ^ (k + a) = ϖ ^ (2 * a) * ϖ ^ (k - a)` using `by rw [← pow_add]; congr 1; omega`. Use `h6 R R₀ ϖ hin κ A A' h k a hP hak (W 0 0 • x + W 1 0 • y) (W 0 1 • x + W 1 1 • y) (W 0 0 • v + (s' * c) • w) ((W 0 1 * ϖ ^ (2 * a)) • v + W 1 1 • w) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using `only [sg_hf_add_left, sg_hf_add_right, sg_hf_smul_left, sg_hf_smul_right, hxy, hyx, hc]`.

Take the linear combination `e00`. Simplify using `only [sg_hf_add_left, sg_hf_add_right, sg_hf_smul_left, sg_hf_smul_right, hxy, hyx, hc]`. Take the linear combination `e11`. Simplify using `only [sg_hf_add_left, sg_hf_add_right, sg_hf_smul_left, sg_hf_smul_right, hxy, hyx, hc]`. Take the linear combination `e01`.

Rewrite using `[mulVec_add, mulVec_smul, mulVec_smul, hv, hw, hk, hs']`. Simplify using `only [smul_add, smul_smul]`. Apply the tactic sequence `congr 1 <;> congr 1 <;> ring`. Rewrite using `[mulVec_add, mulVec_smul, mulVec_smul, hv, hw, hk]`. Simplify using `only [smul_add, smul_smul]`.

Apply the tactic sequence `congr 1 <;> congr 1 <;> ring`.
-/
theorem step_of (h5 : Select) (h8 : Plane) (h6 : Split) : Step := by
  intro R _ _ R₀ _ ϖ hin κ _ _ A A' h k hP hnb
  haveI := hin.dom
  obtain ⟨a, x, y, ha0, hak, hxy, ⟨c, hc⟩, ⟨v, hv⟩, ⟨w, hw⟩⟩ := h5 R R₀ ϖ hin (Fin 2 ⊕ κ) A A' h k hP hnb
  have hA : Aᴴ = A := hP.1.1
  have hsϖ : star ϖ = ϖ := (hin.fix ϖ).1 hin.pi_mem
  have hyx : hf A y x = 1 := by rw [← sg_hf_star hA x y, hxy, star_one]
  have hpow0 : ϖ ^ (2 * a) ≠ 0 := pow_ne_zero _ hin.pi_ne
  have hcR : c ∈ R₀ := by
    rw [hin.fix]
    have h1 := sg_hf_star hA x x
    rw [hc, star_mul, star_pow, hsϖ] at h1
    exact mul_left_cancel₀ hpow0 (by rw [mul_comm, h1])
  have hβR : hf A y y ∈ R₀ := (hin.fix _).2 (sg_hf_star hA y y)
  have hϖm : (⟨ϖ, hin.pi_mem⟩ : R₀) ∈ IsLocalRing.maximalIdeal R₀ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hin.pi_nonunit (hu.map R₀.subtype)
  have hmα : ϖ ^ (2 * a) * c ∈ R₀ := R₀.mul_mem (R₀.pow_mem hin.pi_mem _) hcR
  have hαm : (⟨ϖ ^ (2 * a) * c, hmα⟩ : R₀) ∈ IsLocalRing.maximalIdeal R₀ := by
    have e : (⟨ϖ ^ (2 * a) * c, hmα⟩ : R₀) = ⟨ϖ, hin.pi_mem⟩ ^ (2 * a) * ⟨c, hcR⟩ := Subtype.ext (by simp)
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖm _ (by omega))
  obtain ⟨W, hWdet, hW, s', hs'⟩ := h8 R R₀ ϖ hin ⟨ϖ ^ (2 * a) * c, hmα⟩ ⟨hf A y y, hβR⟩ hαm
  have e00 := congrFun (congrFun hW 0) 0
  have e11 := congrFun (congrFun hW 1) 1
  have e01 := congrFun (congrFun hW 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, hyp, conjTranspose_apply] at e00 e11 e01 hs'
  have hk : ϖ ^ (k + a) = ϖ ^ (2 * a) * ϖ ^ (k - a) := by rw [← pow_add]; congr 1; omega

  refine h6 R R₀ ϖ hin κ A A' h k a hP hak (W 0 0 • x + W 1 0 • y) (W 0 1 • x + W 1 1 • y) (W 0 0 • v + (s' * c) • w) ((W 0 1 * ϖ ^ (2 * a)) • v + W 1 1 • w) ?_ ?_ ?_ ?_ ?_
  · simp only [sg_hf_add_left, sg_hf_add_right, sg_hf_smul_left, sg_hf_smul_right, hxy, hyx, hc]
    linear_combination e00
  · simp only [sg_hf_add_left, sg_hf_add_right, sg_hf_smul_left, sg_hf_smul_right, hxy, hyx, hc]
    linear_combination e11
  · simp only [sg_hf_add_left, sg_hf_add_right, sg_hf_smul_left, sg_hf_smul_right, hxy, hyx, hc]
    linear_combination e01
  · rw [mulVec_add, mulVec_smul, mulVec_smul, hv, hw, hk, hs']
    simp only [smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  · rw [mulVec_add, mulVec_smul, mulVec_smul, hv, hw, hk]
    simp only [smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring

end PI.SqPair.LCP
