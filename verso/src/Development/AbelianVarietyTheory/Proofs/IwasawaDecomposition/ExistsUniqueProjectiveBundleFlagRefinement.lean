import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle.StepLift

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

variable {ι : Type} {m k k' : ι → ℕ} {τ : ι} {K : Type} [Field K]

/- English proof (translation)
Establish `hz : ∀ l : {l : Fin (m τ) // ¬ k τ ≤ (l : ℕ)}, g τ a l.1 * h τ l.1 j.1 = 0`. Introduce `l`. Establish `hl : ¬ k τ ≤ (l.1 : ℕ)` using `l.2`. Establish `hj : k τ ≤ (j.1 : ℕ)` using `j.2`. Rewrite using `[(hh τ).2.2.2 l.1 j.1 (by omega) (by rw [Fin.lt_def]; omega), mul_zero]`.

Rewrite using `[Pi.mul_apply, Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype (fun l : Fin (m τ) => k τ ≤ (l : ℕ)), Finset.sum_eq_zero (fun l _ => hz l), add_zero]`.
-/
theorem mul_apply_rest {O : Subring K} (g : Mat m K) {h : Mat m K} (hh : Par k O h) (a : Fin (m τ))
    (j : Rest m k τ) : (g * h) τ a j.1 = ∑ l : Rest m k τ, g τ a l.1 * h τ l.1 j.1 := by
  have hz : ∀ l : {l : Fin (m τ) // ¬ k τ ≤ (l : ℕ)}, g τ a l.1 * h τ l.1 j.1 = 0 := by
    intro l
    have hl : ¬ k τ ≤ (l.1 : ℕ) := l.2
    have hj : k τ ≤ (j.1 : ℕ) := j.2
    rw [(hh τ).2.2.2 l.1 j.1 (by omega) (by rw [Fin.lt_def]; omega), mul_zero]
  rw [Pi.mul_apply, Matrix.mul_apply,
    ← Fintype.sum_subtype_add_sum_subtype (fun l : Fin (m τ) => k τ ≤ (l : ℕ)),
    Finset.sum_eq_zero (fun l _ => hz l), add_zero]

/- English proof (translation)
Establish `hd` using `Matrix.twoBlockTriangular_det (g σ) (fun i : Fin (m σ) => k σ ≤ (i : ℕ)) (by`. Introduce `i hi j hj`. Establish `hi' : ¬ k σ ≤ (i : ℕ)` using `hi`. Establish `hj' : k σ ≤ (j : ℕ)` using `hj`. Conclude with `(hg σ).2.2.2 i j (by omega) (by rw [Fin.lt_def]; omega))`.

Introduce `h0`. Apply `(hg σ).2.1` to reduce the goal to its premises. Rewrite using `[hd]`. Conclude with `mul_eq_zero_of_left h0 _`.
-/
private theorem det_submatrix_rest_ne_zero {O : Subring K} {g : Mat m K} (hg : Par k O g) (σ : ι) :
    ((g σ).submatrix (Subtype.val : Rest m k σ → Fin (m σ)) (Subtype.val : Rest m k σ → Fin (m σ))).det ≠ 0 := by
  have hd := Matrix.twoBlockTriangular_det (g σ) (fun i : Fin (m σ) => k σ ≤ (i : ℕ)) (by
    intro i hi j hj
    have hi' : ¬ k σ ≤ (i : ℕ) := hi
    have hj' : k σ ≤ (j : ℕ) := hj
    exact (hg σ).2.2.2 i j (by omega) (by rw [Fin.lt_def]; omega))
  intro h0
  apply (hg σ).2.1
  rw [hd]
  exact mul_eq_zero_of_left h0 _

/- English proof (translation)
Introduce `h0`. Conclude with `det_submatrix_rest_ne_zero hh τ (Matrix.det_eq_zero_of_row_eq_zero ⟨⟨k τ, hk⟩, le_refl _⟩ fun j => congrFun h0 j)`.
-/
theorem row_ne_zero {h : Mat m K} (hh : Par k ⊤ h) (hk : k τ < m τ) :
    (fun j : Rest m k τ => h τ ⟨k τ, hk⟩ j.1) ≠ 0 := by
  intro h0
  exact det_submatrix_rest_ne_zero hh τ (Matrix.det_eq_zero_of_row_eq_zero ⟨⟨k τ, hk⟩, le_refl _⟩ fun j => congrFun h0 j)

/- English proof (translation)
Establish `hX : Par k ⊤ (h * G⁻¹)` using `hh.mul hG.inv`. Establish `hXG : h * G⁻¹ * G = h` using `by rw [mul_assoc, Mat.inv_mul hG.det_ne, mul_one]`. Establish `hrow : ∀ j : Rest m k τ, h τ ⟨k τ, hk⟩ j.1 = ∑ l : Rest m k τ, (h * G⁻¹) τ ⟨k τ, hk⟩ l.1 * G τ l.1 j.1`. Introduce `j`. Rewrite using `[← mul_apply_rest (h * G⁻¹) hG, hXG]`.

Prove the components needed by the constructor for the conclusion. Introduce `hP`. Use `⟨(h * G⁻¹) τ ⟨k τ, hk⟩ ⟨k τ, hk⟩, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hrow j, Finset.sum_eq_single (⟨⟨k τ, hk⟩, le_refl _⟩ : Rest m k τ)]`. Introduce `l _ hl`.

Establish `hl2 : k τ ≤ (l.1 : ℕ)` using `l.2`. Establish `hl3 : (l.1 : ℕ) ≠ k τ` using `fun e => hl (Subtype.ext (Fin.ext e))`. Establish `hlt : (⟨k τ, hk⟩ : Fin (m τ)) < l.1` using `by rw [Fin.lt_def]; show k τ < (l.1 : ℕ); omega`. Rewrite using `[(hP τ).2.2.2 ⟨k τ, hk⟩ l.1 (by show k τ < k' τ; omega) hlt, zero_mul]`. Introduce `hn`.

Conclude with `absurd (Finset.mem_univ _) hn`. Introduce and unpack `⟨t, ht⟩`. Establish `hv : Matrix.vecMul (fun l : Rest m k τ => (h * G⁻¹) τ ⟨k τ, hk⟩ l.1 - if l = (⟨⟨k τ, hk⟩, le_refl _⟩ : Rest m k τ) then t else 0) ((G τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ))) = 0`. Use function extensionality and compare the values at `j`. Establish `e` using `hrow j`.

Rewrite `e` using `[ht j]`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[← e, sub_self]`. Establish `hv0` using `Matrix.eq_zero_of_vecMul_eq_zero (det_submatrix_rest_ne_zero hG τ) hv`. Introduce `σ`.

Use `⟨fun _ _ => Subring.mem_top _, hX.det_ne σ, Subring.mem_top _, ?_⟩` and prove the remaining obligations. Introduce `i j hi hij`. Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality. Distinguish the cases in `hik : (i : ℕ) < k σ`.

Conclude with `(hX σ).2.2.2 i j hik hij`. Establish `hi' : (i : ℕ) = k σ` using `by omega`. Establish `hj : k σ ≤ (j : ℕ)` using `by rw [Fin.lt_def] at hij; omega`. Establish `hne : (⟨j, hj⟩ : Rest m k σ) ≠ ⟨⟨k σ, hk⟩, le_refl _⟩`. Introduce `e`.

Establish `e'` using `congrArg (fun x : Rest m k σ => (x.1 : ℕ)) e`. Simplify using `only at e'`. Rewrite `hij` using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Establish `e` using `congrFun hv0 ⟨j, hj⟩`.

Simplify using `only [hne, if_false, sub_zero, Pi.zero_apply] at e`. Establish `hieq : i = ⟨k σ, hk⟩` using `Fin.ext hi'`. Substitute `hieq` using the available equality. Conclude with `e`. Conclude with `(hX σ).2.2.2 i j (by rw [← h2 σ hσ]; exact hi) hij`.
-/
theorem par_succ_iff {h G : Mat m K} (hh : Par k ⊤ h) (hG : Par k ⊤ G) (hk : k τ < m τ) (h1 : k' τ = k τ + 1)
    (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ') :
    Par k' ⊤ (h * G⁻¹) ↔ ∃ t : K, ∀ j : Rest m k τ, h τ ⟨k τ, hk⟩ j.1 = t * G τ ⟨k τ, hk⟩ j.1 := by
  have hX : Par k ⊤ (h * G⁻¹) := hh.mul hG.inv
  have hXG : h * G⁻¹ * G = h := by rw [mul_assoc, Mat.inv_mul hG.det_ne, mul_one]
  have hrow : ∀ j : Rest m k τ,
      h τ ⟨k τ, hk⟩ j.1 = ∑ l : Rest m k τ, (h * G⁻¹) τ ⟨k τ, hk⟩ l.1 * G τ l.1 j.1 := by
    intro j
    rw [← mul_apply_rest (h * G⁻¹) hG, hXG]
  constructor
  · intro hP
    refine ⟨(h * G⁻¹) τ ⟨k τ, hk⟩ ⟨k τ, hk⟩, fun j => ?_⟩
    rw [hrow j, Finset.sum_eq_single (⟨⟨k τ, hk⟩, le_refl _⟩ : Rest m k τ)]
    · intro l _ hl
      have hl2 : k τ ≤ (l.1 : ℕ) := l.2
      have hl3 : (l.1 : ℕ) ≠ k τ := fun e => hl (Subtype.ext (Fin.ext e))
      have hlt : (⟨k τ, hk⟩ : Fin (m τ)) < l.1 := by rw [Fin.lt_def]; show k τ < (l.1 : ℕ); omega
      rw [(hP τ).2.2.2 ⟨k τ, hk⟩ l.1 (by show k τ < k' τ; omega) hlt, zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rintro ⟨t, ht⟩
    have hv : Matrix.vecMul (fun l : Rest m k τ => (h * G⁻¹) τ ⟨k τ, hk⟩ l.1 -
        if l = (⟨⟨k τ, hk⟩, le_refl _⟩ : Rest m k τ) then t else 0)
        ((G τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ))) = 0 := by
      funext j
      have e := hrow j
      rw [ht j] at e
      simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, Pi.zero_apply, sub_mul,
        Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← e, sub_self]
    have hv0 := Matrix.eq_zero_of_vecMul_eq_zero (det_submatrix_rest_ne_zero hG τ) hv
    intro σ
    refine ⟨fun _ _ => Subring.mem_top _, hX.det_ne σ, Subring.mem_top _, ?_⟩
    intro i j hi hij
    by_cases hσ : σ = τ
    · subst hσ
      by_cases hik : (i : ℕ) < k σ
      · exact (hX σ).2.2.2 i j hik hij
      · have hi' : (i : ℕ) = k σ := by omega
        have hj : k σ ≤ (j : ℕ) := by rw [Fin.lt_def] at hij; omega
        have hne : (⟨j, hj⟩ : Rest m k σ) ≠ ⟨⟨k σ, hk⟩, le_refl _⟩ := by
          intro e
          have e' := congrArg (fun x : Rest m k σ => (x.1 : ℕ)) e
          simp only at e'
          rw [Fin.lt_def] at hij
          omega
        have e := congrFun hv0 ⟨j, hj⟩
        simp only [hne, if_false, sub_zero, Pi.zero_apply] at e
        have hieq : i = ⟨k σ, hk⟩ := Fin.ext hi'
        subst hieq
        exact e
    · exact (hX σ).2.2.2 i j (by rw [← h2 σ hσ]; exact hi) hij

variable {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

/- English proof (translation)
Establish `hPφ : Par k ⊤ ((A * A₀⁻¹).map φ)` using `hP.map (φ : Ω →+* Ω') fun _ _ => Subring.mem_top _`. Establish `hAφ : ∀ σ, (A.map φ σ).det ≠ 0` using `fun σ => by`. Rewrite using `[show (A.map φ σ).det = φ (A σ).det from Mat.det_map A (φ : Ω →+* Ω') σ]`. Conclude with `(map_ne_zero φ).2 (hA σ)`. Establish `hmap : (A * A₀⁻¹).map φ = A.map φ * (A₀.map φ)⁻¹`.

Rewrite using `[show (A * A₀⁻¹).map φ = A.map φ * A₀⁻¹.map φ from Mat.map_mul A A₀⁻¹ (φ : Ω →+* Ω'), show A₀⁻¹.map φ = (A₀.map φ)⁻¹ from Mat.map_inv A₀ (φ : Ω →+* Ω')]`. Establish `hZ : A' * (A.map φ)⁻¹ * (A * A₀⁻¹).map φ = A' * (A₀.map φ)⁻¹`. Rewrite using `[hmap, mul_assoc, ← mul_assoc (A.map φ)⁻¹, Mat.inv_mul hAφ, one_mul]`. Establish `hNd` using `det_submatrix_rest_ne_zero hPφ τ`. Establish `hrow : Matrix.vecMul (fun l : Rest m k τ => (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ l.1) ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ))) = a • s`.

Use function extensionality and compare the values at `j`. Rewrite using `[Pi.smul_apply, smul_eq_mul, ← ha j, ← hZ, mul_apply_rest _ hPφ]`. Both sides reduce to the same expression. Establish `hz : (fun l : Rest m k τ => (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ l.1) = a • Matrix.vecMul s ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹`. Rewrite using `[← Matrix.smul_vecMul, ← hrow, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hNd), Matrix.vecMul_one]`.

Establish `hmul : (((A * A₀⁻¹) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ))).map φ * (((A * A₀⁻¹) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹.map φ = 1`. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_submatrix_rest_ne_zero hP τ)), Matrix.map_one _ (map_zero φ) (map_one φ)]`. Establish `hinv : (((A * A₀⁻¹) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹.map φ = ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹` using `(Matrix.inv_eq_right_inv hmul).symm`. Establish `hfin : Matrix.vecMul s ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹ = Matrix.mulVec ((dualBlock k τ A₀ A).map φ) s`. Rewrite using `[← Matrix.mulVec_transpose, ← hinv]`.

Apply the tactic sequence `try rfl`. Rewrite using `[← hfin]`. Conclude with `congrFun hz j`.
-/
theorem row_eq {φ : Ω →ₐ[F] Ω'} {O : Subring Ω} (hk : k τ < m τ) {A₀ A : Mat m Ω} (hA : ∀ τ, (A τ).det ≠ 0)
    (hP : Par k O (A * A₀⁻¹)) (hd : (dualBlock k τ A₀ A).det ≠ 0) {s : Rest m k τ → Ω'} {A' : Mat m Ω'} {a : Ω'}
    (ha : ∀ j : Rest m k τ, (A' * (A₀.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1 = a * s j) (j : Rest m k τ) :
    (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1 = a * ((dualBlock k τ A₀ A).map φ).mulVec s j := by
  have hPφ : Par k ⊤ ((A * A₀⁻¹).map φ) := hP.map (φ : Ω →+* Ω') fun _ _ => Subring.mem_top _
  have hAφ : ∀ σ, (A.map φ σ).det ≠ 0 := fun σ => by
    rw [show (A.map φ σ).det = φ (A σ).det from Mat.det_map A (φ : Ω →+* Ω') σ]
    exact (map_ne_zero φ).2 (hA σ)
  have hmap : (A * A₀⁻¹).map φ = A.map φ * (A₀.map φ)⁻¹ := by
    rw [show (A * A₀⁻¹).map φ = A.map φ * A₀⁻¹.map φ from Mat.map_mul A A₀⁻¹ (φ : Ω →+* Ω'),
      show A₀⁻¹.map φ = (A₀.map φ)⁻¹ from Mat.map_inv A₀ (φ : Ω →+* Ω')]
  have hZ : A' * (A.map φ)⁻¹ * (A * A₀⁻¹).map φ = A' * (A₀.map φ)⁻¹ := by
    rw [hmap, mul_assoc, ← mul_assoc (A.map φ)⁻¹, Mat.inv_mul hAφ, one_mul]
  have hNd := det_submatrix_rest_ne_zero hPφ τ
  have hrow : Matrix.vecMul (fun l : Rest m k τ => (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ l.1)
      ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ))) = a • s := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul, ← ha j, ← hZ, mul_apply_rest _ hPφ]
    rfl
  have hz : (fun l : Rest m k τ => (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ l.1) =
      a • Matrix.vecMul s ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹ := by
    rw [← Matrix.smul_vecMul, ← hrow, Matrix.vecMul_vecMul,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hNd), Matrix.vecMul_one]
  have hmul : (((A * A₀⁻¹) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ))).map φ * (((A * A₀⁻¹) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_submatrix_rest_ne_zero hP τ)),
      Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hinv : (((A * A₀⁻¹) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹.map φ = ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹ := (Matrix.inv_eq_right_inv hmul).symm
  have hfin : Matrix.vecMul s ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹ = Matrix.mulVec ((dualBlock k τ A₀ A).map φ) s := by
    rw [← Matrix.mulVec_transpose, ← hinv]
    try rfl
  rw [← hfin]
  exact congrFun hz j

/- English proof (translation)
Establish `hB` using `hE _ A hA`. Establish `hA0P : Par k (M.O (genericPoint M.Z)).toSubring (A * A₀⁻¹)` using `(Fr.mem_iff hA₀).1 (Fr.mem_genericPoint hA)`. Establish `hc : (fun j : Rest m k τ => h τ ⟨k τ, hk⟩ j.1) ≠ 0` using `row_ne_zero hh hk`. Take `⟨p, ⟨hpf, hp⟩, huniq⟩` from `hP.lifts K x (dualBlock k τ A₀ A) hB.1 hB.2 _ hc`. Establish `key : ∀ q : Sp K ⟶ M'.Z, q ≫ f = x → (Bears S' φ A h q ↔ ∃ i, M'.Div (((dualBlock k τ A₀ A).map φ).mulVec s) i (q (IsLocalRing.closedPoint K)) ∧ ∀ j, h τ ⟨k τ, hk⟩ j.1 = h τ ⟨k τ, hk⟩ i.1 * M'.val q (((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s …`.

Introduce `q hqf`. Establish `hfq : f (q (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K)`. Rewrite using `[← hqf]`. Apply the tactic sequence `first | rfl | simp`. Establish `hsp : ∀ w, q w ⤳ q (IsLocalRing.closedPoint K)` using `RatModel.specializes_of_range_eq (RatModel.range_eq_singleton q _)`.

Establish `hunit : ∀ y : Ω', y ∈ M'.O (q (IsLocalRing.closedPoint K)) → (M'.val q y ≠ 0 ↔ y ≠ 0 ∧ y⁻¹ ∈ M'.O (q (IsLocalRing.closedPoint K)))` using `fun y hy => (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton q _) ⟨y, hy⟩).trans (RatModel.isUnit_O_iff _)`. Establish `hstep : ∀ A' ∈ S'.S (q (IsLocalRing.closedPoint K)), Par k (M'.O (q (IsLocalRing.closedPoint K))).toSubring (A' * (A.map φ)⁻¹) ∧ ∃ a : Ω', ∀ j : Rest m k τ, (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1 = a * ((dualBlock k τ A₀ A).map φ).mulVec s j`. Introduce `A' hA'`. Rewrite `hA'` using `[hS]`. Take `⟨hpar, a, ha⟩` from `hA'`.

Conclude with `⟨hpar A (by rw [hfq]; exact hA), a, fun j => row_eq hk (fun σ => Fr.det_ne hA σ) hA0P hB.1 ha j⟩`. Establish `hW : ∀ A' ∈ S'.S (q (IsLocalRing.closedPoint K)), Par k ⊤ ((A' * (A.map φ)⁻¹).map (M'.val q))` using `fun A' hA' => (hstep A' hA').1.map_of (M'.val q) (RatModel.valHom q (q (IsLocalRing.closedPoint K)) (RatModel.range_eq_singleton q _)) (fun y => (RatModel.valHom_apply _ _ _ y).symm)`. Unfold `Bears`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨A', hA', hpar⟩`.

Take `⟨hX, a, ha⟩` from `hstep A' hA'`. Establish `hmem : ∀ j : Rest m k τ, a * ((dualBlock k τ A₀ A).map φ).mulVec s j ∈ M'.O (q (IsLocalRing.closedPoint K))` using `fun j => by`. Establish `hj` using `(hX τ).1 ⟨k τ, hk⟩ j.1`. Rewrite `hj` using `[ha j]`. Conclude with `hj`.

Take `⟨t, ht⟩` from `(par_succ_iff hh (hW A' hA') hk h1 h2).1 hpar`. Take `⟨j₀, hj₀⟩` from `Function.ne_iff.1 (row_ne_zero (hW A' hA') hk)`. Establish `hu : M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀) ≠ 0`. Rewrite using `[← ha j₀]`. Conclude with `hj₀`.

Take `⟨hne0, hinv0⟩` from `(hunit _ (hmem j₀)).1 hu`. Establish `ha0 : a ≠ 0` using `left_ne_zero_of_mul hne0`. Establish `hv0 : ((dualBlock k τ A₀ A).map φ).mulVec s j₀ ≠ 0` using `right_ne_zero_of_mul hne0`. Establish `hdiv : ∀ j, ((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s j₀ ∈ M'.O (q (IsLocalRing.closedPoint K))` using `fun j => by`. Establish `e : ((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s j₀ = a * ((dualBlock k τ A₀ A).map φ).mulVec s j * (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀)⁻¹`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `mul_mem (hmem j) hinv0`. Use `⟨j₀, ⟨hv0, hdiv⟩, fun j => ?_⟩` and prove the remaining obligations. Establish `e2 : a * ((dualBlock k τ A₀ A).map φ).mulVec s j = a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀ * (((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s j₀)`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[ht j, ht j₀]`. Use `show t * M'.val q ((A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1) = t * M'.val q ((A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j₀.1) * _`. Rewrite using `[ha j, ha j₀, e2, RatModel.val_mul hsp (hmem j₀) (hdiv j), mul_assoc]`. Introduce and unpack `⟨i, ⟨hvi, hdivi⟩, hci⟩`.

Take `⟨A', hA'⟩` from `S'.nonempty (q (IsLocalRing.closedPoint K))`. Take `⟨hX, a, ha⟩` from `hstep A' hA'`. Establish `hmem : ∀ j : Rest m k τ, a * ((dualBlock k τ A₀ A).map φ).mulVec s j ∈ M'.O (q (IsLocalRing.closedPoint K))` using `fun j => by`. Establish `hj` using `(hX τ).1 ⟨k τ, hk⟩ j.1`. Rewrite `hj` using `[ha j]`.

Conclude with `hj`. Take `⟨j₀, hj₀⟩` from `Function.ne_iff.1 (row_ne_zero (hW A' hA') hk)`. Establish `hu : M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀) ≠ 0`. Rewrite using `[← ha j₀]`. Conclude with `hj₀`.

Take `⟨hne0, hinv0⟩` from `(hunit _ (hmem j₀)).1 hu`. Establish `ha0 : a ≠ 0` using `left_ne_zero_of_mul hne0`. Establish `hv0 : ((dualBlock k τ A₀ A).map φ).mulVec s j₀ ≠ 0` using `right_ne_zero_of_mul hne0`. Establish `e3 : (a * ((dualBlock k τ A₀ A).map φ).mulVec s i)⁻¹ = ((dualBlock k τ A₀ A).map φ).mulVec s j₀ / ((dualBlock k τ A₀ A).map φ).mulVec s i * (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀)⁻¹`. Clear the denominators using the available nonvanishing facts.

Establish `hinvi : (a * ((dualBlock k τ A₀ A).map φ).mulVec s i)⁻¹ ∈ M'.O (q (IsLocalRing.closedPoint K))`. Rewrite using `[e3]`. Conclude with `mul_mem (hdivi j₀) hinv0`. Establish `hui : M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s i) ≠ 0` using `(hunit _ (hmem i)).2 ⟨mul_ne_zero ha0 hvi, hinvi⟩`. Use `⟨A', hA', (par_succ_iff hh (hW A' hA') hk h1 h2).2 ⟨h τ ⟨k τ, hk⟩ i.1 / M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s i), fun j => ?_⟩⟩` and prove the remaining obligations.

Use `show h τ ⟨k τ, hk⟩ j.1 = h τ ⟨k τ, hk⟩ i.1 / M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s i) * M'.val q ((A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1)`. Establish `e2 : a * ((dualBlock k τ A₀ A).map φ).mulVec s j = a * ((dualBlock k τ A₀ A).map φ).mulVec s i * (((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s i)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[ha j, e2, RatModel.val_mul hsp (hmem i) (hdivi j), hci j, ← mul_assoc, div_mul_cancel₀ _ hui]`. Conclude with `⟨p, ⟨hpf, (key p hpf).2 hp⟩, fun q hq => huniq q ⟨hq.1, (key q hq.1).1 hq.2⟩⟩`.
-/
theorem existsUnique_bears (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι]
    (m k k' : ι → ℕ) (S : Fr M m k) (S' : Fr M' m k') (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω)
    (EE : M.Lat (Rest m k τ)) (s : Rest m k τ → Ω') (h1 : k' τ = k τ + 1) (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ')
    (hA₀ : A₀ ∈ S.S (genericPoint M.Z))
    (hE : ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧
      EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)))
    (hP : ProjPoints M EE M' φ f s) (hS : ∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z')
    (K : Type) [Field K] (x : Sp K ⟶ M.Z) (A : Mat m Ω) (hA : A ∈ S.S (x (IsLocalRing.closedPoint K)))
    (h : Mat m K) (hh : Par k ⊤ h) : ∃! p : Sp K ⟶ M'.Z, p ≫ f = x ∧ Bears S' φ A h p := by
  have hB := hE _ A hA
  have hA0P : Par k (M.O (genericPoint M.Z)).toSubring (A * A₀⁻¹) :=
    (Fr.mem_iff hA₀).1 (Fr.mem_genericPoint hA)
  have hc : (fun j : Rest m k τ => h τ ⟨k τ, hk⟩ j.1) ≠ 0 := row_ne_zero hh hk
  obtain ⟨p, ⟨hpf, hp⟩, huniq⟩ := hP.lifts K x (dualBlock k τ A₀ A) hB.1 hB.2 _ hc
  have key : ∀ q : Sp K ⟶ M'.Z, q ≫ f = x → (Bears S' φ A h q ↔
      ∃ i, M'.Div (((dualBlock k τ A₀ A).map φ).mulVec s) i (q (IsLocalRing.closedPoint K)) ∧
        ∀ j, h τ ⟨k τ, hk⟩ j.1 = h τ ⟨k τ, hk⟩ i.1 * M'.val q
          (((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s i)) := by
    intro q hqf
    have hfq : f (q (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K) := by
      rw [← hqf]
      first | rfl | simp
    have hsp : ∀ w, q w ⤳ q (IsLocalRing.closedPoint K) :=
      RatModel.specializes_of_range_eq (RatModel.range_eq_singleton q _)
    have hunit : ∀ y : Ω', y ∈ M'.O (q (IsLocalRing.closedPoint K)) →
        (M'.val q y ≠ 0 ↔ y ≠ 0 ∧ y⁻¹ ∈ M'.O (q (IsLocalRing.closedPoint K))) := fun y hy =>
      (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton q _) ⟨y, hy⟩).trans
        (RatModel.isUnit_O_iff _)
    have hstep : ∀ A' ∈ S'.S (q (IsLocalRing.closedPoint K)),
        Par k (M'.O (q (IsLocalRing.closedPoint K))).toSubring (A' * (A.map φ)⁻¹) ∧
        ∃ a : Ω', ∀ j : Rest m k τ, (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1 =
          a * ((dualBlock k τ A₀ A).map φ).mulVec s j := by
      intro A' hA'
      rw [hS] at hA'
      obtain ⟨hpar, a, ha⟩ := hA'
      exact ⟨hpar A (by rw [hfq]; exact hA), a,
        fun j => row_eq hk (fun σ => Fr.det_ne hA σ) hA0P hB.1 ha j⟩
    have hW : ∀ A' ∈ S'.S (q (IsLocalRing.closedPoint K)),
        Par k ⊤ ((A' * (A.map φ)⁻¹).map (M'.val q)) := fun A' hA' =>
      (hstep A' hA').1.map_of (M'.val q)
        (RatModel.valHom q (q (IsLocalRing.closedPoint K)) (RatModel.range_eq_singleton q _))
        (fun y => (RatModel.valHom_apply _ _ _ y).symm)
    unfold Bears
    constructor
    · rintro ⟨A', hA', hpar⟩
      obtain ⟨hX, a, ha⟩ := hstep A' hA'
      have hmem : ∀ j : Rest m k τ, a * ((dualBlock k τ A₀ A).map φ).mulVec s j ∈
          M'.O (q (IsLocalRing.closedPoint K)) := fun j => by
        have hj := (hX τ).1 ⟨k τ, hk⟩ j.1
        rw [ha j] at hj
        exact hj
      obtain ⟨t, ht⟩ := (par_succ_iff hh (hW A' hA') hk h1 h2).1 hpar
      obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 (row_ne_zero (hW A' hA') hk)
      have hu : M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀) ≠ 0 := by
        rw [← ha j₀]
        exact hj₀
      obtain ⟨hne0, hinv0⟩ := (hunit _ (hmem j₀)).1 hu
      have ha0 : a ≠ 0 := left_ne_zero_of_mul hne0
      have hv0 : ((dualBlock k τ A₀ A).map φ).mulVec s j₀ ≠ 0 := right_ne_zero_of_mul hne0
      have hdiv : ∀ j, ((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s j₀ ∈
          M'.O (q (IsLocalRing.closedPoint K)) := fun j => by
        have e : ((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s j₀ =
            a * ((dualBlock k τ A₀ A).map φ).mulVec s j * (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀)⁻¹ := by
          field_simp
        rw [e]
        exact mul_mem (hmem j) hinv0
      refine ⟨j₀, ⟨hv0, hdiv⟩, fun j => ?_⟩
      have e2 : a * ((dualBlock k τ A₀ A).map φ).mulVec s j = a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀ *
          (((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s j₀) := by
        field_simp
      rw [ht j, ht j₀]
      show t * M'.val q ((A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1) =
        t * M'.val q ((A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j₀.1) * _
      rw [ha j, ha j₀, e2, RatModel.val_mul hsp (hmem j₀) (hdiv j), mul_assoc]
    · rintro ⟨i, ⟨hvi, hdivi⟩, hci⟩
      obtain ⟨A', hA'⟩ := S'.nonempty (q (IsLocalRing.closedPoint K))
      obtain ⟨hX, a, ha⟩ := hstep A' hA'
      have hmem : ∀ j : Rest m k τ, a * ((dualBlock k τ A₀ A).map φ).mulVec s j ∈
          M'.O (q (IsLocalRing.closedPoint K)) := fun j => by
        have hj := (hX τ).1 ⟨k τ, hk⟩ j.1
        rw [ha j] at hj
        exact hj
      obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 (row_ne_zero (hW A' hA') hk)
      have hu : M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀) ≠ 0 := by
        rw [← ha j₀]
        exact hj₀
      obtain ⟨hne0, hinv0⟩ := (hunit _ (hmem j₀)).1 hu
      have ha0 : a ≠ 0 := left_ne_zero_of_mul hne0
      have hv0 : ((dualBlock k τ A₀ A).map φ).mulVec s j₀ ≠ 0 := right_ne_zero_of_mul hne0
      have e3 : (a * ((dualBlock k τ A₀ A).map φ).mulVec s i)⁻¹ =
          ((dualBlock k τ A₀ A).map φ).mulVec s j₀ / ((dualBlock k τ A₀ A).map φ).mulVec s i *
            (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀)⁻¹ := by
        field_simp
      have hinvi : (a * ((dualBlock k τ A₀ A).map φ).mulVec s i)⁻¹ ∈ M'.O (q (IsLocalRing.closedPoint K)) := by
        rw [e3]
        exact mul_mem (hdivi j₀) hinv0
      have hui : M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s i) ≠ 0 :=
        (hunit _ (hmem i)).2 ⟨mul_ne_zero ha0 hvi, hinvi⟩
      refine ⟨A', hA', (par_succ_iff hh (hW A' hA') hk h1 h2).2
        ⟨h τ ⟨k τ, hk⟩ i.1 / M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s i), fun j => ?_⟩⟩
      show h τ ⟨k τ, hk⟩ j.1 = h τ ⟨k τ, hk⟩ i.1 / M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s i) *
        M'.val q ((A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1)
      have e2 : a * ((dualBlock k τ A₀ A).map φ).mulVec s j = a * ((dualBlock k τ A₀ A).map φ).mulVec s i *
          (((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s i) := by
        field_simp
      rw [ha j, e2, RatModel.val_mul hsp (hmem i) (hdivi j), hci j, ← mul_assoc, div_mul_cancel₀ _ hui]
  exact ⟨p, ⟨hpf, (key p hpf).2 hp⟩, fun q hq => huniq q ⟨hq.1, (key q hq.1).1 hq.2⟩⟩

end GlobalTheory.FlagBundle.StepLift
