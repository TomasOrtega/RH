import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.TiK

open GroundTheory.Automorphic.Reduction (archCompact euclidNorm infAt_apply finAt_apply infAt_inv finAt_inv)

section Arch

variable {E : Type*} [NormedField E] {n : ℕ}

/- English proof (translation)
Establish `hsq : ∀ z : Fin n → ℝ, (z ᵥ* M) ⬝ᵥ (z ᵥ* M) = z ⬝ᵥ z`. Introduce `z`. Establish `h1` using `h z`. Establish `key : ∀ y : Fin n → ℝ, euclidNorm y ^ 2 = y ⬝ᵥ y`. Introduce `y`.

Rewrite using `[euclidNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]`. Simplify using `[dotProduct, sq]`. Rewrite using `[← key, ← key, h1]`. Establish `hpol : ∀ x y : Fin n → ℝ, (x ᵥ* M) ⬝ᵥ (y ᵥ* M) = x ⬝ᵥ y`. Introduce `x y`.

Establish `h1` using `hsq (x + y)`. Establish `h2` using `hsq x`. Establish `h3` using `hsq y`. Simplify using `only [Matrix.add_vecMul, add_dotProduct, dotProduct_add] at h1`. Rewrite `h1` using `[dotProduct_comm (y ᵥ* M) (x ᵥ* M), dotProduct_comm y x]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use extensionality with `i j`. Establish `h1` using `hpol (Pi.single i 1) (Pi.single j 1)`. Rewrite `h1` using `[single_one_vecMul, single_one_vecMul]`. Rewrite using `[Matrix.mul_apply', Matrix.one_apply]`.

Establish `h2 : (Pi.single i (1 : ℝ) : Fin n → ℝ) ⬝ᵥ Pi.single j 1 = if i = j then 1 else 0`. Simplify using `[Pi.single_apply, eq_comm]`. Rewrite using `[← h2, ← h1]`. Both sides reduce to the same expression.
-/
theorem mul_transpose_eq_one_of_norm {M : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ z : Fin n → ℝ, euclidNorm (z ᵥ* M) = euclidNorm z) : M * Mᵀ = 1 := by
  have hsq : ∀ z : Fin n → ℝ, (z ᵥ* M) ⬝ᵥ (z ᵥ* M) = z ⬝ᵥ z := by
    intro z
    have h1 := h z
    have key : ∀ y : Fin n → ℝ, euclidNorm y ^ 2 = y ⬝ᵥ y := by
      intro y
      rw [euclidNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
      simp [dotProduct, sq]
    rw [← key, ← key, h1]
  have hpol : ∀ x y : Fin n → ℝ, (x ᵥ* M) ⬝ᵥ (y ᵥ* M) = x ⬝ᵥ y := by
    intro x y
    have h1 := hsq (x + y)
    have h2 := hsq x
    have h3 := hsq y
    simp only [Matrix.add_vecMul, add_dotProduct, dotProduct_add] at h1
    rw [dotProduct_comm (y ᵥ* M) (x ᵥ* M), dotProduct_comm y x] at h1
    linarith
  ext i j
  have h1 := hpol (Pi.single i 1) (Pi.single j 1)
  rw [single_one_vecMul, single_one_vecMul] at h1
  rw [Matrix.mul_apply', Matrix.one_apply]
  have h2 : (Pi.single i (1 : ℝ) : Fin n → ℝ) ⬝ᵥ Pi.single j 1 = if i = j then 1 else 0 := by
    simp [Pi.single_apply, eq_comm]
  rw [← h2, ← h1]
  rfl

/- English proof (translation)
Establish `hmap : ∀ y : Fin n → E, (fun i => φ.toRingHom ((y ᵥ* k) i)) = (fun i => φ.toRingHom (y i)) ᵥ* (k.map φ)`. Introduce `y`. Use extensionality with `j`. Simplify using `[vecMul, dotProduct, map_sum, map_mul]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `hM : (k.map φ) * (k.map φ)ᵀ = 1`. Apply `mul_transpose_eq_one_of_norm` to reduce the goal to its premises. Introduce `z`. Establish `h1` using `h (fun i => φ.symm (z i))`.

Rewrite `h1` using `[← Reduction.euclidNorm_map φ.toRingHom hφ, ← Reduction.euclidNorm_map φ.toRingHom hφ (fun i => φ.symm (z i)), hmap]`. Simplify using `using h1`. Use extensionality with `i j`. Apply `φ.injective` to reduce the goal to its premises. Establish `h1` using `congrFun (congrFun hM i) j`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] at h1`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul]`. Rewrite using `[h1, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Introduce `h y`.

Establish `hU : (k.map φ) ∈ unitaryGroup (Fin n) ℝ`. Rewrite using `[mem_unitaryGroup_iff]`. Establish `: (k.map φ) * star (k.map φ) = (k * kᵀ).map φ`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.star_eq_conjTranspose, map_sum, map_mul]`.

Rewrite using `[this, h]`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`. Rewrite using `[← Reduction.euclidNorm_map φ.toRingHom hφ, hmap, Reduction.euclidNorm_vecMul_unitary hU, Reduction.euclidNorm_map φ.toRingHom hφ]`.
-/
theorem norm_preserving_iff (φ : E ≃+* ℝ) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (k : Matrix (Fin n) (Fin n) E) :
    (∀ y : Fin n → E, euclidNorm (y ᵥ* k) = euclidNorm y) ↔ k * kᵀ = 1 := by
  have hmap : ∀ y : Fin n → E, (fun i => φ.toRingHom ((y ᵥ* k) i)) =
      (fun i => φ.toRingHom (y i)) ᵥ* (k.map φ) := by
    intro y
    ext j
    simp [vecMul, dotProduct, map_sum, map_mul]
  constructor
  · intro h
    have hM : (k.map φ) * (k.map φ)ᵀ = 1 := by
      apply mul_transpose_eq_one_of_norm
      intro z
      have h1 := h (fun i => φ.symm (z i))
      rw [← Reduction.euclidNorm_map φ.toRingHom hφ, ← Reduction.euclidNorm_map φ.toRingHom hφ (fun i => φ.symm (z i)), hmap] at h1
      simpa using h1
    ext i j
    apply φ.injective
    have h1 := congrFun (congrFun hM i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] at h1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul]
    rw [h1, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro h y
    have hU : (k.map φ) ∈ unitaryGroup (Fin n) ℝ := by
      rw [mem_unitaryGroup_iff]
      have : (k.map φ) * star (k.map φ) = (k * kᵀ).map φ := by
        ext i j
        simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose, map_sum, map_mul]
      rw [this, h]
      ext i j
      simp [Matrix.one_apply]
    rw [← Reduction.euclidNorm_map φ.toRingHom hφ, hmap, Reduction.euclidNorm_vecMul_unitary hU,
      Reduction.euclidNorm_map φ.toRingHom hφ]

end Arch

section Adelic

variable {n : ℕ}

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((k⁻¹ : AdelicGLn.AdelicGL ℚ n) b a).1 w = ((infAt w k)⁻¹ : GL (Fin n) w.Completion) b a`. Rewrite using `[← infAt_inv]`. Both sides reduce to the same expression.
-/
theorem infAt_ti (w : InfinitePlace ℚ) (k : AdelicGLn.AdelicGL ℚ n) :
    infAt w (ti k) = ti (infAt w k) := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  change ((k⁻¹ : AdelicGLn.AdelicGL ℚ n) b a).1 w = ((infAt w k)⁻¹ : GL (Fin n) w.Completion) b a
  rw [← infAt_inv]
  rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((k⁻¹ : AdelicGLn.AdelicGL ℚ n) b a).2 v = ((finAt v k)⁻¹ : GL (Fin n) (v.adicCompletion ℚ)) b a`. Rewrite using `[← finAt_inv]`. Both sides reduce to the same expression.
-/
theorem finAt_ti (v : HeightOneSpectrum (𝓞 ℚ)) (k : AdelicGLn.AdelicGL ℚ n) :
    finAt v (ti k) = ti (finAt v k) := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  change ((k⁻¹ : AdelicGLn.AdelicGL ℚ n) b a).2 v = ((finAt v k)⁻¹ : GL (Fin n) (v.adicCompletion ℚ)) b a
  rw [← finAt_inv]
  rfl

/- English proof (translation)
Establish `hw : w.IsReal` using `RationalIdeles.isReal_infinitePlace w`. Rewrite using `[Reduction.mem_archCompact]`. Conclude with `norm_preserving_iff (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (fun x => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) x) k.val`.
-/
theorem mem_archCompact_iff (w : InfinitePlace ℚ) (k : GL (Fin n) w.Completion) :
    k ∈ archCompact w ↔ k.val * k.valᵀ = 1 := by
  have hw : w.IsReal := RationalIdeles.isReal_infinitePlace w
  rw [Reduction.mem_archCompact]
  exact norm_preserving_iff (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
    (fun x => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) x) k.val

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `k.inv.transpose = k.val`. Establish `h1 : k.inv = k.valᵀ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, Matrix.transpose_transpose]`.
-/
theorem ti_eq_self_of_orthogonal {R : Type*} [CommRing R] (k : GL (Fin n) R)
    (h : k.val * k.valᵀ = 1) : ti k = k := by
  apply Units.ext
  change k.inv.transpose = k.val
  have h1 : k.inv = k.valᵀ := by
    calc k.inv = k.inv * (k.val * k.valᵀ) := by rw [h, mul_one]
      _ = k.valᵀ := by rw [← mul_assoc, k.inv_val, one_mul]
  rw [h1, Matrix.transpose_transpose]

/- English proof (translation)
Take `⟨h1, h2⟩` from `Reduction.mem_maxCompact.1 hk`. Use `Reduction.mem_maxCompact.2 ⟨fun w => ?_, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[infAt_ti, ti_eq_self_of_orthogonal _ ((mem_archCompact_iff w _).1 (h1 w))]`. Conclude with `h1 w`. Rewrite using `[finAt_ti]`.

Take `⟨ha, hb⟩` from `(GLnLocal.mem_integralGL_iff _ _).1 (h2 v)`. Conclude with `(GLnLocal.mem_integralGL_iff _ _).2 ⟨fun i j => hb j i, fun i j => ha j i⟩`.
-/
theorem ti_mem_maxCompact {k : AdelicGLn.AdelicGL ℚ n}
    (hk : k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL ℚ n))) :
    ti k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL ℚ n)) := by
  obtain ⟨h1, h2⟩ := Reduction.mem_maxCompact.1 hk
  refine Reduction.mem_maxCompact.2 ⟨fun w => ?_, fun v => ?_⟩
  · rw [infAt_ti, ti_eq_self_of_orthogonal _ ((mem_archCompact_iff w _).1 (h1 w))]
    exact h1 w
  · rw [finAt_ti]
    obtain ⟨ha, hb⟩ := (GLnLocal.mem_integralGL_iff _ _).1 (h2 v)
    exact (GLnLocal.mem_integralGL_iff _ _).2 ⟨fun i j => hb j i, fun i j => ha j i⟩

/- English proof (translation)
Establish `hinv : ∀ i j, (γ⁻¹ : GL (Fin n) ℚ).val i j = γ.val j i` using `fun i j => by`. Express the relevant statement in the definitionally equal form `γ.inv i j = _`. Rewrite using `[h2]`. Both sides reduce to the same expression. Use `Reduction.mem_maxCompact.2 ⟨fun w => ?_, fun v => ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_archCompact_iff]`. Establish `hT : (infAt w (AdelicGLn.diagonal ℚ n γ)).valᵀ = (infAt w (AdelicGLn.diagonal ℚ n γ)).inv`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = ((infAt w (AdelicGLn.diagonal ℚ n γ))⁻¹ : GL (Fin n) w.Completion) a b`. Rewrite using `[← infAt_inv, ← map_inv]`.

Express the relevant statement in the definitionally equal form `(algebraMap ℚ 𝔸[ℚ] (γ.val b a)).1 w = (algebraMap ℚ 𝔸[ℚ] ((γ⁻¹ : GL (Fin n) ℚ).val a b)).1 w`. Rewrite using `[hinv]`. Rewrite using `[hT]`. Conclude with `Units.val_inv _`. Establish `hent : ∀ q : ℚ, (q = 0 ∨ q = 1 ∨ q = -1) → (algebraMap ℚ 𝔸[ℚ] q).2 v ∈ (ValuativeRel.valuation (v.adicCompletion ℚ)).integer`.

Introduce and unpack `q (rfl | rfl | rfl)`. Rewrite using `[map_zero]`. Conclude with `zero_mem (ValuativeRel.valuation (v.adicCompletion ℚ)).integer`. Simplify using the standard rewrite rules. Rewrite using `[map_neg, map_one]`.

Conclude with `neg_mem (one_mem (ValuativeRel.valuation (v.adicCompletion ℚ)).integer)`. Use `(GLnLocal.mem_integralGL_iff _ _).2 ⟨fun i j => hent _ (h1 i j), fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← finAt_inv, ← map_inv]`. Express the relevant statement in the definitionally equal form `(algebraMap ℚ 𝔸[ℚ] ((γ⁻¹ : GL (Fin n) ℚ).val i j)).2 v ∈ _`. Rewrite using `[hinv]`.

Conclude with `hent _ (h1 j i)`.
-/
theorem diagonal_mem_maxCompact (γ : GL (Fin n) ℚ)
    (h1 : ∀ i j, γ.val i j = 0 ∨ γ.val i j = 1 ∨ γ.val i j = -1) (h2 : γ.inv = γ.valᵀ) :
    AdelicGLn.diagonal ℚ n γ ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL ℚ n)) := by
  have hinv : ∀ i j, (γ⁻¹ : GL (Fin n) ℚ).val i j = γ.val j i := fun i j => by
    change γ.inv i j = _
    rw [h2]
    rfl
  refine Reduction.mem_maxCompact.2 ⟨fun w => ?_, fun v => ?_⟩
  · rw [mem_archCompact_iff]
    have hT : (infAt w (AdelicGLn.diagonal ℚ n γ)).valᵀ = (infAt w (AdelicGLn.diagonal ℚ n γ)).inv := by
      refine Matrix.ext fun a b => ?_
      change _ = ((infAt w (AdelicGLn.diagonal ℚ n γ))⁻¹ : GL (Fin n) w.Completion) a b
      rw [← infAt_inv, ← map_inv]
      change (algebraMap ℚ 𝔸[ℚ] (γ.val b a)).1 w = (algebraMap ℚ 𝔸[ℚ] ((γ⁻¹ : GL (Fin n) ℚ).val a b)).1 w
      rw [hinv]
    rw [hT]
    exact Units.val_inv _
  · have hent : ∀ q : ℚ, (q = 0 ∨ q = 1 ∨ q = -1) →
        (algebraMap ℚ 𝔸[ℚ] q).2 v ∈ (ValuativeRel.valuation (v.adicCompletion ℚ)).integer := by
      rintro q (rfl | rfl | rfl)
      · rw [map_zero]
        exact zero_mem (ValuativeRel.valuation (v.adicCompletion ℚ)).integer
      · simp
      · rw [map_neg, map_one]
        exact neg_mem (one_mem (ValuativeRel.valuation (v.adicCompletion ℚ)).integer)
    refine (GLnLocal.mem_integralGL_iff _ _).2 ⟨fun i j => hent _ (h1 i j), fun i j => ?_⟩
    rw [← finAt_inv, ← map_inv]
    change (algebraMap ℚ 𝔸[ℚ] ((γ⁻¹ : GL (Fin n) ℚ).val i j)).2 v ∈ _
    rw [hinv]
    exact hent _ (h1 j i)

end Adelic

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [w3]`.
-/
theorem weyl_eq_rational_GL3 : (w3 : G3) = dia w3 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w3]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [w2]`.
-/
theorem weyl_eq_rational_GL2 : (w2 : G2) = dia2 w2 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w2]

/- English proof (translation)
Use `diagonal_mem_maxCompact _ (fun i j => ?_) ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [w3]`. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;> simp [w3]`.
-/
theorem rational_weyl_mem_maxCompact_GL3 : dia w3 ∈ (maxCompact : Subgroup G3) := by
  refine diagonal_mem_maxCompact _ (fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp [w3]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [w3]

/- English proof (translation)
Use `diagonal_mem_maxCompact _ (fun i j => ?_) ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [w2]`. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;> simp [w2]`.
-/
theorem rational_weyl_mem_maxCompact_GL2 : dia2 w2 ∈ (maxCompact : Subgroup G2) := by
  refine diagonal_mem_maxCompact _ (fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp [w2]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [w2]

/- English proof (translation)
Use `diagonal_mem_maxCompact _ (fun i j => ?_) ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dl3, dg]`. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;> simp [dl3, dg]`.
-/
theorem rational_sign_mem_maxCompact_GL3 : dia dl3 ∈ (maxCompact : Subgroup G3) := by
  refine diagonal_mem_maxCompact _ (fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp [dl3, dg]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [dl3, dg]

/- English proof (translation)
Use `diagonal_mem_maxCompact _ (fun i j => ?_) ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dl2, dg2]`. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;> simp [dl2, dg2]`.
-/
theorem rational_sign_mem_maxCompact_GL2 : dia2 dl2 ∈ (maxCompact : Subgroup G2) := by
  refine diagonal_mem_maxCompact _ (fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp [dl2, dg2]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [dl2, dg2]

/- English proof (translation)
Assemble the required witnesses or components as `⟨weyl_eq_rational_GL3 ▸ rational_weyl_mem_maxCompact_GL3, rational_sign_mem_maxCompact_GL3, weyl_eq_rational_GL2 ▸ rational_weyl_mem_maxCompact_GL2, rational_sign_mem_maxCompact_GL2, fun _ hk => ti_mem_maxCompact hk, fun _ hk => ti_mem_maxCompact hk, weyl_eq_rational_GL3, weyl_eq …`.
-/
theorem weyl_delta_ti_maxCompact : (w3 : G3) ∈ (maxCompact : Subgroup G3) ∧ dia dl3 ∈ (maxCompact : Subgroup G3) ∧
    (w2 : G2) ∈ (maxCompact : Subgroup G2) ∧ dia2 dl2 ∈ (maxCompact : Subgroup G2) ∧
    (∀ k ∈ (maxCompact : Subgroup G3), ti k ∈ (maxCompact : Subgroup G3)) ∧
    (∀ k ∈ (maxCompact : Subgroup G2), ti k ∈ (maxCompact : Subgroup G2)) ∧
    (w3 : G3) = dia w3 ∧ (w2 : G2) = dia2 w2 :=
  ⟨weyl_eq_rational_GL3 ▸ rational_weyl_mem_maxCompact_GL3, rational_sign_mem_maxCompact_GL3, weyl_eq_rational_GL2 ▸ rational_weyl_mem_maxCompact_GL2, rational_sign_mem_maxCompact_GL2,
    fun _ hk => ti_mem_maxCompact hk, fun _ hk => ti_mem_maxCompact hk, weyl_eq_rational_GL3, weyl_eq_rational_GL2⟩

end GlobalTheory.CompanionTheory.UnfoldingAlt.TiK
