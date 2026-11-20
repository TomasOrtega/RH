import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.OverlapG
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.LowbdSmul

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.LocalOverlapAverage

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

def actEq (x : Gp L N) : HS L N ≃L[ℝ] HS L N where
  toLinearEquiv :=
    { toFun := actL x
      invFun := actL x⁻¹
      map_add' := (actL x).map_add
      map_smul' := (actL x).map_smul
      left_inv := fun h => by rw [← actL_mul, inv_mul_cancel, actL_one]
      right_inv := fun h => by rw [← actL_mul, mul_inv_cancel, actL_one] }
  continuous_toFun := (actL x).continuous
  continuous_invFun := (actL x⁻¹).continuous

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem actEq_apply (x : Gp L N) (h : HS L N) : actEq x h = actL x h := rfl

/- English proof (translation)
Introduce `h hh k hk a b ha hb hab w`. Rewrite using `[mat_add, mat_smul, mat_smul]`. Break down `ha.eq_or_lt with rfl | ha'` into its components or cases. Rewrite `hab` using `[zero_add]`. Substitute `hab` using the available equality.

Simplify using `using hk w`. Conclude with `((hh w).smul ha').add_posSemidef ((hk w).posSemidef.smul hb)`.
-/
theorem pos_convex : Convex ℝ (Pos L N) := by
  intro h hh k hk a b ha hb hab w
  rw [mat_add, mat_smul, mat_smul]
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    subst hab
    simpa using hk w
  · exact ((hh w).smul ha').add_posSemidef ((hk w).posSemidef.smul hb)

/- English proof (translation)
Introduce and unpack `p ⟨τ, hτ0, hτ1, y, hy, rfl⟩`. Conclude with `pos_convex.sum_mem (fun j _ => hτ0 j) hτ1 fun j _ => actL_pos (x j) (hB (hy j))`.
-/
theorem kset_sub {q : ℕ} (x : Fin (q + 1) → Gp L N) {B : Set (HS L N)} (hB : B ⊆ Pos L N) :
    Kset (fun j => actL (x j)) B ⊆ Pos L N := by
  rintro p ⟨τ, hτ0, hτ1, y, hy, rfl⟩
  exact pos_convex.sum_mem (fun j _ => hτ0 j) hτ1 fun j _ => actL_pos (x j) (hB (hy j))

/- English proof (translation)
Establish `hc : IsCompact ((stdSimplex ℝ (Fin (q + 1))) ×ˢ (Set.univ.pi fun _ : Fin (q + 1) => B))` using `IsCompact.prod (isCompact_stdSimplex ℝ (Fin (q + 1))) (isCompact_univ_pi fun _ => hB)`. Establish `hcont : Continuous fun p : (Fin (q + 1) → ℝ) × (Fin (q + 1) → V) => ∑ j, p.1 j • A j (p.2 j)` using `by fun_prop`. Establish `e : Kset A B = (fun p : (Fin (q + 1) → ℝ) × (Fin (q + 1) → V) => ∑ j, p.1 j • A j (p.2 j)) '' ((stdSimplex ℝ (Fin (q + 1))) ×ˢ (Set.univ.pi fun _ : Fin (q + 1) => B))`. Use extensionality with `p`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨τ, hτ0, hτ1, y, hy, rfl⟩`. Conclude with `⟨(τ, y), ⟨⟨hτ0, hτ1⟩, fun j _ => hy j⟩, rfl⟩`. Introduce and unpack `⟨⟨τ, y⟩, ⟨⟨hτ0, hτ1⟩, hy⟩, rfl⟩`. Conclude with `⟨τ, hτ0, hτ1, y, fun j => hy j (Set.mem_univ _), rfl⟩`. Rewrite using `[e]`.

Conclude with `hc.image hcont`.
-/
theorem isCompact_kset {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ℕ}
    (A : Fin (q + 1) → V →L[ℝ] V) {B : Set V} (hB : IsCompact B) : IsCompact (Kset A B) := by
  have hc : IsCompact ((stdSimplex ℝ (Fin (q + 1))) ×ˢ (Set.univ.pi fun _ : Fin (q + 1) => B)) :=
    IsCompact.prod (isCompact_stdSimplex ℝ (Fin (q + 1))) (isCompact_univ_pi fun _ => hB)
  have hcont : Continuous fun p : (Fin (q + 1) → ℝ) × (Fin (q + 1) → V) =>
      ∑ j, p.1 j • A j (p.2 j) := by fun_prop
  have e : Kset A B = (fun p : (Fin (q + 1) → ℝ) × (Fin (q + 1) → V) =>
      ∑ j, p.1 j • A j (p.2 j)) '' ((stdSimplex ℝ (Fin (q + 1))) ×ˢ (Set.univ.pi fun _ : Fin (q + 1) => B)) := by
    ext p
    constructor
    · rintro ⟨τ, hτ0, hτ1, y, hy, rfl⟩
      exact ⟨(τ, y), ⟨⟨hτ0, hτ1⟩, fun j _ => hy j⟩, rfl⟩
    · rintro ⟨⟨τ, y⟩, ⟨⟨hτ0, hτ1⟩, hy⟩, rfl⟩
      exact ⟨τ, hτ0, hτ1, y, fun j => hy j (Set.mem_univ _), rfl⟩
  rw [e]
  exact hc.image hcont

/- English proof (translation)
Establish `e : y 0 + ∑ j, t j • (y j.succ - y 0) = ∑ i, (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i • y i`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul, one_smul, ← Finset.sum_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Use `pos_convex.sum_mem (fun i _ => ?_) ?_ fun i _ => hy i` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `only [Fin.cons_zero]`. Combine the linear relations using `[ht.2]`. Simplify `ht.1 j` using `only [Fin.cons_succ]`.

Rewrite using `[Fin.sum_univ_succ]`. Simplify using the standard rewrite rules.
-/
theorem simplex_pos {q : ℕ} (y : Fin (q + 1) → HS L N) (hy : ∀ j, y j ∈ Pos L N) (t : Fin q → ℝ)
    (ht : (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1) : y 0 + ∑ j, t j • (y j.succ - y 0) ∈ Pos L N := by
  have e : y 0 + ∑ j, t j • (y j.succ - y 0) =
      ∑ i, (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i • y i := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul, one_smul,
      ← Finset.sum_smul]
    abel
  rw [e]
  refine pos_convex.sum_mem (fun i _ => ?_) ?_ fun i _ => hy i
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      linarith [ht.2]
    · simpa only [Fin.cons_succ] using ht.1 j
  · rw [Fin.sum_univ_succ]
    simp

/- English proof (translation)
Establish `: {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} = (⋂ j, {t : Fin q → ℝ | 0 ≤ t j}) ∩ {t | ∑ j, t j ≤ 1}`. Use extensionality with `t`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Use `(IsClosed.inter (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)) (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)).measurableSet` and prove the remaining obligations.
-/
theorem measurableSet_simplex (q : ℕ) :
    MeasurableSet {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} := by
  have : {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} =
      (⋂ j, {t : Fin q → ℝ | 0 ≤ t j}) ∩ {t | ∑ j, t j ≤ 1} := by
    ext t
    simp
  rw [this]
  refine (IsClosed.inter (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j))
    (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)).measurableSet

/- English proof (translation)
Simplify using `only [intP, intS]`. Use `setIntegral_congr_fun (measurableSet_simplex q) fun t ht => ?_` and prove the remaining obligations. Establish `hv : ∀ j, ((g • y j : Pos L N) : HS L N) = actL g (y j).1` using `fun j => rfl`. Simplify using `only [hv, ← map_sub, ← map_smul, ← map_sum, ← map_add]`. Establish `hp` using `simplex_pos (fun j => (y j).1) (fun j => (y j).2) t ht`.

Use `congrArg (fun f => f (fun j => (y j.succ).1 - (y 0).1)) (hg _ hp)` as an intermediate fact. Simplify `this` using `[Function.comp_def, map_sub]`.
-/
theorem intP_inv {q : ℕ} (ω : Form (HS L N) q) (g : Gp L N) (hg : FInv ω g)
    (y : Fin (q + 1) → Pos L N) : intP ω (fun j => g • y j) = intP ω y := by
  simp only [intP, intS]
  refine setIntegral_congr_fun (measurableSet_simplex q) fun t ht => ?_
  have hv : ∀ j, ((g • y j : Pos L N) : HS L N) = actL g (y j).1 := fun j => rfl
  simp only [hv, ← map_sub, ← map_smul, ← map_sum, ← map_add]
  have hp := simplex_pos (fun j => (y j).1) (fun j => (y j).2) t ht
  have := congrArg (fun f => f (fun j => (y j.succ).1 - (y 0).1)) (hg _ hp)
  simpa [Function.comp_def, map_sub] using this

/- English proof (translation)
Use `continuous_induced_rng.2 ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun x : Gp L N => fun w i j => ((((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ * mat v w * ((x w)⁻¹ : GL (Fin N) ℂ)) i j`. Use `continuous_pi fun w => continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Establish `hi : Continuous fun x : Gp L N => (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)` using `Units.continuous_coe_inv.comp (continuous_apply w)`. Conclude with `((hi.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hi).matrix_elem i j`.
-/
theorem cont_actL_apply (v : HS L N) : Continuous fun x : Gp L N => actL x v := by
  refine continuous_induced_rng.2 ?_
  change Continuous fun x : Gp L N => fun w i j =>
    ((((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ * mat v w *
      ((x w)⁻¹ : GL (Fin N) ℂ)) i j
  refine continuous_pi fun w => continuous_pi fun i => continuous_pi fun j => ?_
  have hi : Continuous fun x : Gp L N => (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) :=
    Units.continuous_coe_inv.comp (continuous_apply w)
  exact ((hi.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hi).matrix_elem i j

/- English proof (translation)
The claim follows from `continuous_clm_apply.2 fun v => cont_actL_apply v`.
-/
theorem cont_actL : Continuous fun x : Gp L N => actL x :=
  continuous_clm_apply.2 fun v => cont_actL_apply v

/- English proof (translation)
Establish `h1 : Continuous fun x : Gp L N => ω (actL x (one L N).1)` using `hω.comp_continuous (cont_actL_apply _) fun x => actL_pos x (one L N).2`. Conclude with `(ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp cont_actL).clm_apply h1`.
-/
theorem cont_fr {q : ℕ} (ω : Form (HS L N) q) (hω : ContinuousOn ω (Pos L N)) :
    Continuous (fr ω) := by
  have h1 : Continuous fun x : Gp L N => ω (actL x (one L N).1) :=
    hω.comp_continuous (cont_actL_apply _) fun x => actL_pos x (one L N).2
  exact (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp cont_actL).clm_apply h1

/- English proof (translation)
The claim follows from `continuous_pi fun w => Matrix.SpecialLinearGroup.continuous_toGL.comp (continuous_apply w)`.
-/
theorem cont_ofS : Continuous (ofS L N) :=
  continuous_pi fun w => Matrix.SpecialLinearGroup.continuous_toGL.comp (continuous_apply w)

/- English proof (translation)
Use extensionality with `v`. Establish `h` using `congrArg (fun f => f (fun i => actL x (v i))) (hg _ (actL_pos x (one L N).2))`. Simplify `h` using `[fr, actL_mul, Function.comp_def]`.
-/
theorem fr_mul {q : ℕ} (ω : Form (HS L N) q) (g x : Gp L N) (hg : FInv ω g) :
    fr ω (g * x) = fr ω x := by
  ext v
  have h := congrArg (fun f => f (fun i => actL x (v i))) (hg _ (actL_pos x (one L N).2))
  simpa [fr, actL_mul, Function.comp_def] using h

/- English proof (translation)
Take `⟨A, rfl⟩` from `hγ`. Use `⟨Matrix.SpecialLinearGroup.toGL A, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem ofS_lat {γ : Sp L N} (hγ : γ ∈ latS L N) : ∃ A : Gm L N, ofS L N γ = emb L N A := by
  obtain ⟨A, rfl⟩ := hγ
  refine ⟨Matrix.SpecialLinearGroup.toGL A, ?_⟩
  funext w
  ext i j
  rfl

/- English proof (translation)
Take `⟨c, hc, hev⟩` from `UpperTheory.V.KT.lowbd L N (one L N).1 (one L N).2`. Take `⟨ε, hε, hball⟩` from `Metric.eventually_nhds_iff.1 hev`. Use `⟨ε / 2, half_pos hε, fun k hk w => ?_⟩` and prove the remaining obligations. Establish `hk'` using `hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hk) (half_lt_self hε))`. Rewrite using `[posDef_iff_dotProduct_mulVec]`.

Use `⟨mat_herm k w, fun x hx => ?_⟩` and prove the remaining obligations. Set `z : VR L N` to `Pi.single w x`. Establish `hz : z ≠ 0` using `fun h => hx (by simpa [z] using congrFun h w)`. Establish `h1` using `hk' z`. Establish `h2 : qR k z = (star x ⬝ᵥ (mat k w *ᵥ x)).re`.

Simplify using `only [qR, z]`. Rewrite using `[Finset.sum_eq_single w]`. Simplify using the standard rewrite rules. Introduce `v _ hv`. Simplify using `[Pi.single_eq_of_ne hv]`.

Simplify using the standard rewrite rules. Establish `h3 : 0 < c * ‖z‖ ^ 2`. Establish `: 0 < ‖z‖` using `norm_pos_iff.2 hz`. Check the signs of the components of the expression. Rewrite using `[Complex.lt_def]`.

Use `⟨by simp only [Complex.zero_re]; linarith, ?_⟩` and prove the remaining obligations. Establish `h4` using `(mat_herm k w).im_star_dotProduct_mulVec_self x`. Simplify using `only [Complex.zero_im]`. Conclude with `h4.symm`.
-/
theorem ball_pos : ∃ r : ℝ, 0 < r ∧ Metric.closedBall (one L N).1 r ⊆ Pos L N := by
  classical
  obtain ⟨c, hc, hev⟩ := UpperTheory.V.KT.lowbd L N (one L N).1 (one L N).2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε / 2, half_pos hε, fun k hk w => ?_⟩
  have hk' := hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hk) (half_lt_self hε))
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨mat_herm k w, fun x hx => ?_⟩
  let z : VR L N := Pi.single w x
  have hz : z ≠ 0 := fun h => hx (by simpa [z] using congrFun h w)
  have h1 := hk' z
  have h2 : qR k z = (star x ⬝ᵥ (mat k w *ᵥ x)).re := by
    simp only [qR, z]
    rw [Finset.sum_eq_single w]
    · simp
    · intro v _ hv
      simp [Pi.single_eq_of_ne hv]
    · simp
  have h3 : 0 < c * ‖z‖ ^ 2 := by
    have : 0 < ‖z‖ := norm_pos_iff.2 hz
    positivity
  rw [Complex.lt_def]
  refine ⟨by simp only [Complex.zero_re]; linarith, ?_⟩
  have h4 := (mat_herm k w).im_star_dotProduct_mulVec_self x
  simp only [Complex.zero_im]
  exact h4.symm

end PositivityTheory.KB.LocalOverlapAverage

end
