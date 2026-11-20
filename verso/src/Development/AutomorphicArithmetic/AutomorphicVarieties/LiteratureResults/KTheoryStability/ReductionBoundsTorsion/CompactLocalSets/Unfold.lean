import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.OverlapG
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.UnfoldM

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped ENNReal NNReal ComplexOrder

namespace PositivityTheory.KB.LocalOverlapAverage

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ofS_apply (s : Sp L N) (w : InfinitePlace L) : ofS L N s w = SpecialLinearGroup.toGL (s w) := rfl

/- English proof (translation)
Rewrite using `[ofS_apply, ← map_inv]`. Both sides reduce to the same expression.
-/
theorem coe_ofS_inv (s : Sp L N) (w : InfinitePlace L) :
    (((ofS L N s w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (((s w)⁻¹ : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [ofS_apply, ← map_inv]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_ofS (s : Sp L N) (w : InfinitePlace L) :
    ((ofS L N s w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_actL (g : Gp L N) (h : HS L N) : (actL g h : HS L N).1 = fun w =>
    (((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ * mat h w * ((g w)⁻¹ : GL (Fin N) ℂ) := rfl

/- English proof (translation)
Use `continuous_induced_rng.2 ?_` and prove the remaining obligations. Establish `e : (fun p : Sp L N × HS L N => (actL (ofS L N p.1) p.2 : HS L N).1) = fun p w => (((p.1 w)⁻¹ : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ * mat p.2 w * (((p.1 w)⁻¹ : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)`. Use function extensionality and compare the values at `p`. Rewrite using `[val_actL]`. Use function extensionality and compare the values at `w`.

Rewrite using `[coe_ofS_inv]`. Apply the tactic sequence `try rfl`. Express the relevant statement in the definitionally equal form `Continuous (fun p : Sp L N × HS L N => (actL (ofS L N p.1) p.2 : HS L N).1)`. Rewrite using `[e]`. Use `continuous_pi fun w => ?_` and prove the remaining obligations.

Establish `h1 : Continuous fun p : Sp L N × HS L N => (((p.1 w)⁻¹ : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)` using `continuous_subtype_val.comp ((continuous_inv.comp (continuous_apply w)).comp continuous_fst)`. Establish `h2 : Continuous fun p : Sp L N × HS L N => mat p.2 w` using `(continuous_apply w).comp (continuous_subtype_val.comp continuous_snd)`. Conclude with `(h1.matrix_conjTranspose.matrix_mul h2).matrix_mul h1`.
-/
theorem cont_act : Continuous (fun p : Sp L N × HS L N => actL (ofS L N p.1) p.2) := by
  refine continuous_induced_rng.2 ?_
  have e : (fun p : Sp L N × HS L N => (actL (ofS L N p.1) p.2 : HS L N).1) = fun p w =>
      (((p.1 w)⁻¹ : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ * mat p.2 w *
        (((p.1 w)⁻¹ : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
    funext p
    rw [val_actL]
    funext w
    rw [coe_ofS_inv]
    try rfl
  change Continuous (fun p : Sp L N × HS L N => (actL (ofS L N p.1) p.2 : HS L N).1)
  rw [e]
  refine continuous_pi fun w => ?_
  have h1 : Continuous fun p : Sp L N × HS L N =>
      (((p.1 w)⁻¹ : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) :=
    continuous_subtype_val.comp ((continuous_inv.comp (continuous_apply w)).comp continuous_fst)
  have h2 : Continuous fun p : Sp L N × HS L N => mat p.2 w :=
    (continuous_apply w).comp (continuous_subtype_val.comp continuous_snd)
  exact (h1.matrix_conjTranspose.matrix_mul h2).matrix_mul h1

def actE (g : Gp L N) : HS L N ≃L[ℝ] HS L N :=
  ContinuousLinearEquiv.equivOfInverse (actL g) (actL g⁻¹)
    (fun h => by rw [← actL_mul, inv_mul_cancel, actL_one])
    (fun h => by rw [← actL_mul, mul_inv_cancel, actL_one])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem actE_apply (g : Gp L N) (h : HS L N) : actE g h = actL g h := rfl

/- English proof (translation)
Establish `h1 : Continuous fun s : Sp L N => ((s, h) : Sp L N × HS L N)` using `continuous_id.prodMk continuous_const`. Establish `h2` using `cont_act.comp h1`. Simplify `h2` using `only [Function.comp_def]`.
-/
theorem cont_act_at (h : HS L N) : Continuous fun s : Sp L N => actL (ofS L N s) h := by
  have h1 : Continuous fun s : Sp L N => ((s, h) : Sp L N × HS L N) := continuous_id.prodMk continuous_const
  have h2 := cont_act.comp h1
  simpa only [Function.comp_def] using h2

/- English proof (translation)
Rewrite using `[continuous_clm_apply]`. Conclude with `cont_act_at`.
-/
theorem cont_actCLM : Continuous (fun s : Sp L N => (actL (ofS L N s) : HS L N →L[ℝ] HS L N)) := by
  rw [continuous_clm_apply]
  exact cont_act_at

/- English proof (translation)
The claim follows from `ContinuousLinearMap.continuous_det.comp cont_actCLM`.
-/
theorem cont_det : Continuous (fun s : Sp L N =>
    LinearMap.det (((actE (ofS L N s) : HS L N →L[ℝ] HS L N)) : HS L N →ₗ[ℝ] HS L N)) :=
  ContinuousLinearMap.continuous_det.comp cont_actCLM

/- English proof (translation)
Use extensionality with `v`. Use `congrArg (fun f => f (fun i => actL x (v i))) (hc (actL x (one L N).1) (actL_pos x (one L N).2))` as an intermediate fact. Simplify using `only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at this`. Simplify using `only [fr, ContinuousAlternatingMap.compContinuousLinearMap_apply, actL_mul]`. Rewrite using `[show (⇑(actL (scal L N c * x)) ∘ v) = ⇑(actL (scal L N c)) ∘ fun i => actL x (v i) from`.

Use function extensionality and compare the values at `fun i => actL_mul _ _ _]`. Conclude with `this`.
-/
theorem fr_scal {q : ℕ} {ω : Form (HS L N) q} (c : InfinitePlace L → ℂˣ) (hc : FInv ω (scal L N c))
    (x : Gp L N) : fr ω (scal L N c * x) = fr ω x := by
  ext v
  have := congrArg (fun f => f (fun i => actL x (v i))) (hc (actL x (one L N).1) (actL_pos x (one L N).2))
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at this
  simp only [fr, ContinuousAlternatingMap.compContinuousLinearMap_apply, actL_mul]
  rw [show (⇑(actL (scal L N c * x)) ∘ v) = ⇑(actL (scal L N c)) ∘ fun i => actL x (v i) from
    funext fun i => actL_mul _ _ _]
  exact this

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [fr, ContinuousAlternatingMap.compContinuousLinearMap_apply]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Use `show v i = actL x (actL x⁻¹ (v i))`.

Rewrite using `[← actL_mul, mul_inv_cancel, actL_one]`.
-/
theorem om_fr {q : ℕ} (ω : Form (HS L N) q) (x : Gp L N) :
    ω (actL x (one L N).1) = (fr ω x).compContinuousLinearMap (actL x⁻¹) := by
  ext v
  simp only [fr, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  show v i = actL x (actL x⁻¹ (v i))
  rw [← actL_mul, mul_inv_cancel, actL_one]

/- English proof (translation)
Rewrite using `[om_fr ω x]`. Simplify using `using ContinuousAlternatingMap.norm_compContinuousLinearMap_le (fr ω x) (actL x⁻¹)`.
-/
theorem norm_om_le {q : ℕ} (ω : Form (HS L N) q) (x : Gp L N) :
    ‖ω (actL x (one L N).1)‖ ≤ ‖fr ω x‖ * ‖actL x⁻¹‖ ^ q := by
  rw [om_fr ω x]
  simpa using ContinuousAlternatingMap.norm_compContinuousLinearMap_le (fr ω x) (actL x⁻¹)

/- English proof (translation)
Rewrite using `[mul_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ((norm_nonneg _).trans (hA i k))`. Use `_ = n * (a * b) := by simp`.
-/
theorem entry_mul_le {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} {a b : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ a)
    (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin n) : ‖(A * B) i j‖ ≤ n * (a * b) := by
  rw [mul_apply]
  calc ‖∑ k, A i k * B k j‖ ≤ ∑ k : Fin n, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, a * b := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]; exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ((norm_nonneg _).trans (hA i k))
    _ = n * (a * b) := by simp

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem entry_le_norm (h : HS L N) (w : InfinitePlace L) (i j : Fin N) : ‖mat h w i j‖ ≤ ‖h‖ := by
  calc ‖mat h w i j‖ = ‖h.1 w i j‖ := rfl
    _ ≤ ‖h.1 w i‖ := norm_le_pi_norm _ _
    _ ≤ ‖h.1 w‖ := norm_le_pi_norm _ _
    _ ≤ ‖h.1‖ := norm_le_pi_norm _ _
    _ = ‖h‖ := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `‖h.1‖ ≤ r`. Use `(pi_norm_le_iff_of_nonneg hr).2 fun w => (pi_norm_le_iff_of_nonneg hr).2 fun i => (pi_norm_le_iff_of_nonneg hr).2 fun j => hh w i j` and prove the remaining obligations.
-/
theorem norm_le_of_entry (h : HS L N) (r : ℝ) (hr : 0 ≤ r) (hh : ∀ w i j, ‖mat h w i j‖ ≤ r) : ‖h‖ ≤ r := by
  change ‖h.1‖ ≤ r
  refine (pi_norm_le_iff_of_nonneg hr).2 fun w => (pi_norm_le_iff_of_nonneg hr).2 fun i =>
    (pi_norm_le_iff_of_nonneg hr).2 fun j => hh w i j

/- English proof (translation)
Use `ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_` and prove the remaining obligations. Apply the tactic sequence `refine norm_le_of_entry _ _ (by positivity) fun w i j => ?_`. Rewrite using `[mat_actL]`. Establish `h1 : ∀ i j, ‖((((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ) i j‖ ≤ r` using `fun i j => by`. Rewrite using `[conjTranspose_apply, norm_star]`.

Conclude with `hg w j i`. Establish `h2` using `entry_mul_le h1 (fun i j => entry_le_norm h w i j)`. Establish `h3` using `entry_mul_le h2 (hg w) i j`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_actL_le (g : Gp L N) (r : ℝ) (hr : 0 ≤ r)
    (hg : ∀ w i j, ‖(((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ r) :
    ‖actL g‖ ≤ N * (N * r * r) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  refine norm_le_of_entry _ _ (by positivity) fun w i j => ?_
  rw [mat_actL]
  have h1 : ∀ i j, ‖((((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ) i j‖ ≤ r := fun i j => by
    rw [conjTranspose_apply, norm_star]; exact hg w j i
  have h2 := entry_mul_le h1 (fun i j => entry_le_norm h w i j)
  have h3 := entry_mul_le h2 (hg w) i j
  calc _ ≤ _ := h3
    _ = N * (N * r * r) * ‖h‖ := by ring

/- English proof (translation)
Use function extensionality and compare the values at `w`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Pi.mul_apply, Units.val_mul, scal, GeneralLinearGroup.scalar]`. Use extensionality with `i j`. Simplify using `[mul_diagonal, diagonal_mul, mul_comm]`.
-/
theorem comm_scal (g : Gp L N) (c : InfinitePlace L → ℂˣ) : g * scal L N c = scal L N c * g := by
  funext w
  apply Units.ext
  simp only [Pi.mul_apply, Units.val_mul, scal, GeneralLinearGroup.scalar]
  ext i j
  simp [mul_diagonal, diagonal_mul, mul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_mul_ofS (s : Sp L N) (y : Gp L N) (w : InfinitePlace L) :
    (((ofS L N s * y) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * ((y w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := rfl

/- English proof (translation)
Use `set X : Gp L N := ofS L N s * (scal L N c * ofS L N t) with hXdef`. Establish `hXe : X = scal L N c * ofS L N (s * t)`. Rewrite using `[hXdef, ← mul_assoc, comm_scal, mul_assoc, map_mul]`. Rewrite using `[← actL_mul]`. Use `(norm_om_le ω X).trans ?_` and prove the remaining obligations.

Establish `h1 : ‖fr ω X‖ = ‖fr ω (ofS L N (s * t))‖` using `by rw [hXe, fr_scal c (hω c)]`. Establish `h2 : ‖actL X⁻¹‖ ≤ N * (N * B * B)`. Use `norm_actL_le X⁻¹ B hB fun w i j => ?_` and prove the remaining obligations. Simplify `hX w i j` using `[Pi.inv_apply, inv_inv]`. Rewrite using `[h1]`.

Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h2 q) (norm_nonneg _)`.
-/
theorem point_bd {q : ℕ} {ω : Form (HS L N) q} (hω : ∀ s, FInv ω (scal L N s))
    (c : InfinitePlace L → ℂˣ) (t s : Sp L N) (B : ℝ) (hB : 0 ≤ B)
    (hX : ∀ w i j, ‖(((ofS L N s * (scal L N c * ofS L N t)) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ B) :
    ‖ω (actL (ofS L N s) (actL (scal L N c * ofS L N t) (one L N).1))‖ ≤
      ‖fr ω (ofS L N (s * t))‖ * (N * (N * B * B)) ^ q := by
  set X : Gp L N := ofS L N s * (scal L N c * ofS L N t) with hXdef
  have hXe : X = scal L N c * ofS L N (s * t) := by
    rw [hXdef, ← mul_assoc, comm_scal, mul_assoc, map_mul]
  rw [← actL_mul]
  refine (norm_om_le ω X).trans ?_
  have h1 : ‖fr ω X‖ = ‖fr ω (ofS L N (s * t))‖ := by rw [hXe, fr_scal c (hω c)]
  have h2 : ‖actL X⁻¹‖ ≤ N * (N * B * B) := by
    refine norm_actL_le X⁻¹ B hB fun w i j => ?_
    simpa [Pi.inv_apply, inv_inv] using hX w i j
  rw [h1]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h2 q) (norm_nonneg _)

/- English proof (translation)
The claim follows from `(continuous_apply j).comp ((continuous_apply i).comp ((SpecialLinearGroup.isClosedEmbedding_val (n := Fin N) (R := ℂ)).continuous.comp (continuous_apply w)))`.
-/
theorem cont_entry (w : InfinitePlace L) (i j : Fin N) :
    Continuous fun s : Sp L N => ((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j :=
  (continuous_apply j).comp ((continuous_apply i).comp
    ((SpecialLinearGroup.isClosedEmbedding_val (n := Fin N) (R := ℂ)).continuous.comp (continuous_apply w)))

/- English proof (translation)
The claim follows from `(continuous_apply w).comp continuous_subtype_val`.
-/
theorem cont_mat (w : InfinitePlace L) : Continuous fun q : HS L N => mat q w :=
  (continuous_apply w).comp continuous_subtype_val

/- English proof (translation)
Introduce `q hq`. Use `ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations. Use `continuousAt_pi.2 fun w => continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_` and prove the remaining obligations. Establish `hd : ContinuousAt Ring.inverse (mat q w).det`. Rewrite using `[Ring.inverse_eq_inv']`.

Conclude with `continuousAt_inv₀ (hq w).det_pos.ne'`. Establish `hm : ContinuousAt (fun q' : HS L N => mat q' w) q` using `(cont_mat w).continuousAt`. Establish `hinv : ContinuousAt (fun q' : HS L N => (mat q' w)⁻¹) q` using `ContinuousAt.comp (f := fun q' : HS L N => mat q' w) (x := q) (continuousAt_matrix_inv (mat q w) hd) hm`. Use `show ContinuousAt (fun q' : HS L N => (mat q' w)⁻¹ i j) q`. Conclude with `(continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hinv)`.
-/
theorem contOn_inv : ContinuousOn (fun q : HS L N => fun w i j => (mat q w)⁻¹ i j) (Pos L N) := by
  intro q hq
  refine ContinuousAt.continuousWithinAt ?_
  refine continuousAt_pi.2 fun w => continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
  have hd : ContinuousAt Ring.inverse (mat q w).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hq w).det_pos.ne'
  have hm : ContinuousAt (fun q' : HS L N => mat q' w) q := (cont_mat w).continuousAt
  have hinv : ContinuousAt (fun q' : HS L N => (mat q' w)⁻¹) q :=
    ContinuousAt.comp (f := fun q' : HS L N => mat q' w) (x := q) (continuousAt_matrix_inv (mat q w) hd) hm
  show ContinuousAt (fun q' : HS L N => (mat q' w)⁻¹ i j) q
  exact (continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hinv)

/- English proof (translation)
The claim follows from `continuous_pi fun w => (cont_mat w).matrix_det`.
-/
theorem cont_detq : Continuous (fun q : HS L N => fun w => (mat q w).det) :=
  continuous_pi fun w => (cont_mat w).matrix_det

/- English proof (translation)
Take `⟨R2, hR2⟩` from `hK1.exists_bound_of_continuousOn (contOn_inv.mono hP)`. Take `⟨R3, hR3⟩` from `hK1.exists_bound_of_continuousOn (cont_detq (L := L) (N := N)).continuousOn`. Take `⟨R, hR0, hR⟩` from `dec_bdd hN R2 R3`. Use `⟨R, hR0, fun q hq => ?_⟩` and prove the remaining obligations. Establish `hb2 : ∀ w i j, ‖(mat q w)⁻¹ i j‖ ≤ R2` using `fun w i j => (norm_le_pi_norm (fun j => (mat q w)⁻¹ i j) j).trans ((norm_le_pi_norm (fun i j => (mat q w)⁻¹ i j) i).trans ((norm_le_pi_norm (fun w i j => (mat q w)⁻¹ i j) w).trans (hR2 q hq)))`.

Establish `hb3 : ∀ w, ‖(mat q w).det‖ ≤ R3` using `fun w => (norm_le_pi_norm (fun w => (mat q w).det) w).trans (hR3 q hq)`. Establish `key` using `fun w => hR (mat q w) (hP hq w) (hb2 w) (hb3 w)`. Use `choose c t h1 h2 h3 using key`. Use `⟨c, t, HS_ext fun w => ?_, h2, h3⟩` and prove the remaining obligations. Rewrite using `[mat_actL]`.

Establish `hone : mat (one L N).1 w = 1` using `rfl`. Rewrite using `[hone, Matrix.mul_one]`. Conclude with `h1 w`.
-/
theorem dec_K {K1 : Set (HS L N)} (hN : 1 ≤ N) (hK1 : IsCompact K1) (hP : K1 ⊆ Pos L N) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ q ∈ K1, ∃ (c : InfinitePlace L → ℂˣ) (t : Sp L N),
      actL (scal L N c * ofS L N t) (one L N).1 = q ∧
      (∀ w i j, ‖(((scal L N c * ofS L N t) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R) ∧
      ∀ w i j, ‖((t w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R := by
  obtain ⟨R2, hR2⟩ := hK1.exists_bound_of_continuousOn (contOn_inv.mono hP)
  obtain ⟨R3, hR3⟩ := hK1.exists_bound_of_continuousOn (cont_detq (L := L) (N := N)).continuousOn
  obtain ⟨R, hR0, hR⟩ := dec_bdd hN R2 R3
  refine ⟨R, hR0, fun q hq => ?_⟩
  have hb2 : ∀ w i j, ‖(mat q w)⁻¹ i j‖ ≤ R2 := fun w i j =>
    (norm_le_pi_norm (fun j => (mat q w)⁻¹ i j) j).trans
      ((norm_le_pi_norm (fun i j => (mat q w)⁻¹ i j) i).trans
        ((norm_le_pi_norm (fun w i j => (mat q w)⁻¹ i j) w).trans (hR2 q hq)))
  have hb3 : ∀ w, ‖(mat q w).det‖ ≤ R3 := fun w =>
    (norm_le_pi_norm (fun w => (mat q w).det) w).trans (hR3 q hq)
  have key := fun w => hR (mat q w) (hP hq w) (hb2 w) (hb3 w)
  choose c t h1 h2 h3 using key
  refine ⟨c, t, HS_ext fun w => ?_, h2, h3⟩
  rw [mat_actL]
  have hone : mat (one L N).1 w = 1 := rfl
  rw [hone, Matrix.mul_one]
  exact h1 w

def Wn (L : Type) [Field L] [NumberField L] (N : ℕ) : Set (Sp L N) :=
  {s | ∀ w i j, ‖((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j -
    (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ 1 / 2}

/- English proof (translation)
Simplify using `only [Wn, Set.ofPred_forall]`. Apply the tactic sequence `exact isClosed_iInter fun w => isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le ((cont_entry w i j).sub continuous_const).norm continuous_const`.
-/
theorem isClosed_Wn : IsClosed (Wn L N) := by
  simp only [Wn, Set.ofPred_forall]
  exact isClosed_iInter fun w => isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_le ((cont_entry w i j).sub continuous_const).norm continuous_const

/- English proof (translation)
Simplify using `only [Set.ofPred_forall]`. Apply the tactic sequence `exact isClosed_iInter fun w => isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le (cont_entry w i j).norm continuous_const`.
-/
theorem isClosed_bdd (R : ℝ) :
    IsClosed {x : Sp L N | ∀ w i j, ‖((x w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun w => isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_le (cont_entry w i j).norm continuous_const

/- English proof (translation)
Introduce `s hs w i j`. Establish `h1 : ‖(1 : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ 1`. Apply the tactic sequence `rw [one_apply]; split_ifs <;> simp`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Wn_bdd : ∀ s ∈ Wn L N, ∀ w i j,
    ‖((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ 3 / 2 := by
  intro s hs w i j
  have h1 : ‖(1 : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ 1 := by
    rw [one_apply]; split_ifs <;> simp
  calc _ = ‖(((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j -
        (1 : Matrix (Fin N) (Fin N) ℂ) i j) + (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ 1 / 2 + 1 := add_le_add (hs w i j) h1
    _ = 3 / 2 := by norm_num

/- English proof (translation)
The claim follows from `(isCompact_bddSL (ι := InfinitePlace L) (n := Fin N) (3 / 2)).of_isClosed_subset isClosed_Wn fun s hs => Wn_bdd s hs`.
-/
theorem isCompact_Wn : IsCompact (Wn L N) :=
  (isCompact_bddSL (ι := InfinitePlace L) (n := Fin N) (3 / 2)).of_isClosed_subset isClosed_Wn
    fun s hs => Wn_bdd s hs

/- English proof (translation)
Establish `hU : IsOpen {s : Sp L N | ∀ w i j, ‖((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ < 1 / 2}`. Simplify using `only [Set.ofPred_forall]`. Apply the tactic sequence `exact isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt ((cont_entry w i j).sub continuous_const).norm continuous_const`. Establish `h1 : (1 : Sp L N) ∈ {s : Sp L N | ∀ w i j, ‖((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ < 1 / 2}` using `fun w i j => by`. Simplify using the standard rewrite rules.

Conclude with `fun h0 => (hU.measure_ne_zero μ ⟨1, h1⟩) (measure_mono_null (fun s hs w i j => (hs w i j).le) h0)`.
-/
theorem Wn_pos (μ : Measure (Sp L N)) [μ.IsOpenPosMeasure] : μ (Wn L N) ≠ 0 := by
  have hU : IsOpen {s : Sp L N | ∀ w i j, ‖((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j -
      (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ < 1 / 2} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt ((cont_entry w i j).sub continuous_const).norm continuous_const
  have h1 : (1 : Sp L N) ∈ {s : Sp L N | ∀ w i j, ‖((s w : SpecialLinearGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ < 1 / 2} := fun w i j => by
    simp
  exact fun h0 => (hU.measure_ne_zero μ ⟨1, h1⟩) (measure_mono_null (fun s hs w i j => (hs w i j).le) h0)

/- English proof (translation)
Use `set h : G → ℝ≥0∞ := fun x => if x * t⁻¹ ∈ W then F x else 0 with hh`. Establish `e1 : ∫⁻ s in W, F (s * t) ∂μ = ∫⁻ s, h (s * t) ∂μ`. Rewrite using `[← lintegral_indicator hW]`. Use `congr 1`. Use function extensionality and compare the values at `s`.

Simplify using `[hh, Set.indicator, mul_inv_cancel_right]`. Rewrite using `[e1, lintegral_mul_right_eq_self h t, ← lintegral_indicator hK']`. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : x * t⁻¹ ∈ W`. Simplify using `[hh, h1, Set.indicator_of_mem (hWK x h1)]`.

Simplify using `[hh, h1]`.
-/
theorem right_trans_le {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulRightInvariant] (W K' : Set G) (hW : MeasurableSet W) (hK' : MeasurableSet K') (t : G)
    (hWK : ∀ x, x * t⁻¹ ∈ W → x ∈ K') (F : G → ℝ≥0∞) :
    ∫⁻ s in W, F (s * t) ∂μ ≤ ∫⁻ x in K', F x ∂μ := by
  classical
  set h : G → ℝ≥0∞ := fun x => if x * t⁻¹ ∈ W then F x else 0 with hh
  have e1 : ∫⁻ s in W, F (s * t) ∂μ = ∫⁻ s, h (s * t) ∂μ := by
    rw [← lintegral_indicator hW]
    congr 1
    funext s
    simp [hh, Set.indicator, mul_inv_cancel_right]
  rw [e1, lintegral_mul_right_eq_self h t, ← lintegral_indicator hK']
  refine lintegral_mono fun x => ?_
  by_cases h1 : x * t⁻¹ ∈ W
  · simp [hh, h1, Set.indicator_of_mem (hWK x h1)]
  · simp [hh, h1]

/- English proof (translation)
Introduce `L _ _ N q hN d μ _ K hK hKP`. Use `haveI := d.haar`. Use `haveI := d.right`. Use `set W := Wn L N with hWdef`. Establish `hWk : IsCompact W` using `isCompact_Wn`.

Establish `hWm : MeasurableSet W` using `isClosed_Wn.measurableSet`. Establish `hW0 : d.μ W ≠ 0` using `Wn_pos d.μ`. Establish `hWT : d.μ W ≠ ⊤` using `hWk.measure_lt_top.ne`. Establish `hcK : Continuous fun p : Sp L N × HS L N => actL (ofS L N p.1⁻¹) p.2`. Establish `h1 : Continuous fun p : Sp L N × HS L N => ((p.1⁻¹, p.2) : Sp L N × HS L N)` using `(continuous_inv.comp continuous_fst).prodMk continuous_snd`.

Establish `h2` using `cont_act.comp h1`. Simplify `h2` using `only [Function.comp_def]`. Use `set K1 : Set (HS L N) := (fun p : Sp L N × HS L N => actL (ofS L N p.1⁻¹) p.2) '' (W ×ˢ K) with hK1def`. Establish `hK1 : IsCompact K1` using `(hWk.prod hK).image hcK`. Establish `hK1P : K1 ⊆ Pos L N`.

Introduce and unpack `_ ⟨p, hp, rfl⟩`. Conclude with `actL_pos _ (hKP hp.2)`. Establish `hK1m : MeasurableSet K1` using `hK1.isClosed.measurableSet`. Establish `hK1T : μ K1 ≠ ⊤` using `hK1.measure_lt_top.ne`. Establish `hsub : ∀ s ∈ W, K ⊆ actE (ofS L N s) '' K1`.

Introduce `s hs p hp`. Use `⟨actL (ofS L N s⁻¹) p, ⟨(s, p), ⟨hs, hp⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[actE_apply, ← actL_mul, ← map_mul, mul_inv_cancel, map_one, actL_one]`. Take `⟨R, hR0, hR⟩` from `dec_K hN hK1 hK1P`. Use `set R' : ℝ := N * (3 / 2 * R) with hR'def`.

Establish `hR'0 : 0 ≤ R'` using `by positivity`. Use `set K' : Set (Sp L N) := {x | ∀ w i j, ‖((x w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R'} with hK'def`. Establish `hK'k : IsCompact K'` using `isCompact_bddSL (ι := InfinitePlace L) (n := Fin N) R'`. Establish `hK'm : MeasurableSet K'` using `(isClosed_bdd R').measurableSet`. Take `⟨Dm, hDm⟩` from `hWk.exists_bound_of_continuousOn (cont_det (L := L) (N := N)).continuousOn`.

Use `set D' : ℝ := max Dm 1 with hD'def`. Establish `hD'0 : 0 < D'` using `lt_of_lt_of_le one_pos (le_max_right _ _)`. Use `set m0 : ℝ≥0∞ := ENNReal.ofReal D'⁻¹ with hm0def`. Establish `hm0 : m0 ≠ 0` using `by simp [hm0def, hD'0]`. Use `set B0 : ℝ := ((N : ℝ) * (N * R' * R')) ^ q with hB0def`.

Establish `hB00 : 0 ≤ B0` using `by positivity`. Use `set Bd : ℝ≥0∞ := ENNReal.ofReal B0 with hBddef`. Use `⟨(m0 * d.μ W)⁻¹ * (Bd * μ K1), K', ?_, hK'k, fun ω hω hsc => ?_⟩` and prove the remaining obligations. Conclude with `ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (mul_ne_zero hm0 hW0)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK1T)`. Use `set G : HS L N → ℝ≥0∞ := fun p => (‖ω p‖₊ : ℝ≥0∞) with hGdef`.

Use `set Fr : Sp L N → ℝ≥0∞ := fun x => (‖fr ω (ofS L N x)‖₊ : ℝ≥0∞) with hFrdef`. Establish `st1 : ∀ s ∈ W, m0 * ∫⁻ p in K, G p ∂μ ≤ ∫⁻ p in K1, G (actL (ofS L N s) p) ∂μ`. Introduce `s hs`. Establish `h` using `lintegral_cle_ge μ (actE (ofS L N s)) K1 K (hsub s hs) G`. Simplify using `only [actE_apply] at h`.

Establish `hdet0 : LinearMap.det (((actE (ofS L N s) : HS L N →L[ℝ] HS L N)) : HS L N →ₗ[ℝ] HS L N) ≠ 0` using `(LinearEquiv.isUnit_det' (actE (ofS L N s)).toLinearEquiv).ne_zero`. Establish `hb : |LinearMap.det (((actE (ofS L N s) : HS L N →L[ℝ] HS L N)) : HS L N →ₗ[ℝ] HS L N)| ≤ D'`. Use `hDm s hs` as an intermediate fact. Rewrite `this` using `[Real.norm_eq_abs]`. Conclude with `this.trans (le_max_left _ _)`.

Establish `hm : m0 ≤ ENNReal.ofReal |(LinearMap.det (((actE (ofS L N s) : HS L N →L[ℝ] HS L N)) : HS L N →ₗ[ℝ] HS L N))⁻¹|`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Rewrite using `[abs_inv]`. Conclude with `inv_anti₀ (abs_pos.2 hdet0) hb`. Combine the equalities or inequalities in the displayed calculation.

Establish `st2 : (m0 * ∫⁻ p in K, G p ∂μ) * d.μ W ≤ ∫⁻ s in W, ∫⁻ p in K1, G (actL (ofS L N s) p) ∂μ ∂d.μ`. Rewrite using `[← setLIntegral_const]`. Conclude with `setLIntegral_mono' hWm st1`. Use `haveI : IsFiniteMeasure (d.μ.restrict W) := isFiniteMeasure_restrict.2 hWT`. Use `haveI : IsFiniteMeasure (μ.restrict K1) := isFiniteMeasure_restrict.2 hK1T`.

Establish `hmeas : AEMeasurable (Function.uncurry fun (s : Sp L N) (p : HS L N) => G (actL (ofS L N s) p)) ((d.μ.restrict W).prod (μ.restrict K1))`. Establish `e1 : d.μ.restrict W = (d.μ.restrict W).restrict W`. Rewrite using `[Measure.restrict_restrict hWm, Set.inter_self]`. Establish `e2 : μ.restrict K1 = (μ.restrict K1).restrict K1`. Rewrite using `[Measure.restrict_restrict hK1m, Set.inter_self]`.

Rewrite using `[e1, e2, Measure.prod_restrict]`. Use `ContinuousOn.aemeasurable ?_ (hWm.prod hK1m)` and prove the remaining obligations. Establish `hc : ContinuousOn (fun p : Sp L N × HS L N => ω (actL (ofS L N p.1) p.2)) (W ×ˢ K1)` using `hω.comp cont_act.continuousOn fun p hp => actL_pos _ (hK1P hp.2)`. Conclude with `(ENNReal.continuous_coe.comp continuous_nnnorm).comp_continuousOn hc`. Establish `st3` using `lintegral_lintegral_swap hmeas`.

Establish `st4 : ∀ p ∈ K1, ∫⁻ s in W, G (actL (ofS L N s) p) ∂d.μ ≤ Bd * ∫⁻ x in K', Fr x ∂d.μ`. Introduce `p hp`. Take `⟨c, t, hct, hy, ht⟩` from `hR p hp`. Establish `hpt : ∀ s ∈ W, G (actL (ofS L N s) p) ≤ Bd * Fr (s * t)`. Introduce `s hs`.

Establish `hX : ∀ w i j, ‖(((ofS L N s * (scal L N c * ofS L N t)) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R'`. Introduce `w i j`. Rewrite using `[coe_mul_ofS]`. Conclude with `entry_mul_le (Wn_bdd s hs w) (hy w) i j`. Establish `h` using `point_bd hsc c t s R' hR'0 hX`.

Rewrite `h` using `[hct]`. Simplify using `only [hGdef, hFrdef, hBddef, ENNReal.ofReal, ← ENNReal.coe_mul, ENNReal.coe_le_coe]`. Rewrite using `[← NNReal.coe_le_coe, NNReal.coe_mul, Real.coe_toNNReal _ hB00, coe_nnnorm, coe_nnnorm, mul_comm]`. Conclude with `h`. Establish `hts : ∀ x, x * t⁻¹ ∈ W → x ∈ K'`.

Introduce `x hx`. Take `⟨y, hyW, rfl⟩ : ∃ y ∈ W, y * t = x` from `⟨x * t⁻¹, hx, by group⟩`. Introduce `w i j`. Establish `e : (((y * t) w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = ((y w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * ((t w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)` using `rfl`. Use `entry_mul_le (Wn_bdd y hyW w) (ht w) i j` as an intermediate fact.

Rewrite `this` using `[← e]`. Conclude with `this`. Combine the equalities or inequalities in the displayed calculation. Establish `st5 : ∫⁻ p in K1, ∫⁻ s in W, G (actL (ofS L N s) p) ∂d.μ ∂μ ≤ (Bd * ∫⁻ x in K', Fr x ∂d.μ) * μ K1`. Rewrite using `[← setLIntegral_const]`.

Conclude with `setLIntegral_mono' hK1m st4`. Establish `hall : (m0 * ∫⁻ p in K, G p ∂μ) * d.μ W ≤ (Bd * ∫⁻ x in K', Fr x ∂d.μ) * μ K1` using `st2.trans (st3.le.trans st5)`. Establish `ha0 : m0 * d.μ W ≠ 0` using `mul_ne_zero hm0 hW0`. Establish `haT : m0 * d.μ W ≠ ⊤` using `ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWT`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, ENNReal.inv_mul_cancel ha0 haT, one_mul]`. Use `_ ≤ (m0 * d.μ W)⁻¹ * ((Bd * ∫⁻ x in K', Fr x ∂d.μ) * μ K1) := by`. Use `mul_le_mul_right ?_ _` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `_ = (m0 * d.μ W)⁻¹ * (Bd * μ K1) * ∫⁻ x in K', Fr x ∂d.μ := by ring`.
-/
theorem unfold_holds : Unfold := by
  intro L _ _ N q hN d μ _ K hK hKP
  haveI := d.haar
  haveI := d.right
  set W := Wn L N with hWdef
  have hWk : IsCompact W := isCompact_Wn
  have hWm : MeasurableSet W := isClosed_Wn.measurableSet
  have hW0 : d.μ W ≠ 0 := Wn_pos d.μ
  have hWT : d.μ W ≠ ⊤ := hWk.measure_lt_top.ne
  have hcK : Continuous fun p : Sp L N × HS L N => actL (ofS L N p.1⁻¹) p.2 := by
    have h1 : Continuous fun p : Sp L N × HS L N => ((p.1⁻¹, p.2) : Sp L N × HS L N) :=
      (continuous_inv.comp continuous_fst).prodMk continuous_snd
    have h2 := cont_act.comp h1
    simpa only [Function.comp_def] using h2
  set K1 : Set (HS L N) := (fun p : Sp L N × HS L N => actL (ofS L N p.1⁻¹) p.2) '' (W ×ˢ K) with hK1def
  have hK1 : IsCompact K1 := (hWk.prod hK).image hcK
  have hK1P : K1 ⊆ Pos L N := by
    rintro _ ⟨p, hp, rfl⟩
    exact actL_pos _ (hKP hp.2)
  have hK1m : MeasurableSet K1 := hK1.isClosed.measurableSet
  have hK1T : μ K1 ≠ ⊤ := hK1.measure_lt_top.ne
  have hsub : ∀ s ∈ W, K ⊆ actE (ofS L N s) '' K1 := by
    intro s hs p hp
    refine ⟨actL (ofS L N s⁻¹) p, ⟨(s, p), ⟨hs, hp⟩, rfl⟩, ?_⟩
    rw [actE_apply, ← actL_mul, ← map_mul, mul_inv_cancel, map_one, actL_one]
  obtain ⟨R, hR0, hR⟩ := dec_K hN hK1 hK1P
  set R' : ℝ := N * (3 / 2 * R) with hR'def
  have hR'0 : 0 ≤ R' := by positivity
  set K' : Set (Sp L N) :=
    {x | ∀ w i j, ‖((x w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R'} with hK'def
  have hK'k : IsCompact K' := isCompact_bddSL (ι := InfinitePlace L) (n := Fin N) R'
  have hK'm : MeasurableSet K' := (isClosed_bdd R').measurableSet
  obtain ⟨Dm, hDm⟩ := hWk.exists_bound_of_continuousOn (cont_det (L := L) (N := N)).continuousOn
  set D' : ℝ := max Dm 1 with hD'def
  have hD'0 : 0 < D' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set m0 : ℝ≥0∞ := ENNReal.ofReal D'⁻¹ with hm0def
  have hm0 : m0 ≠ 0 := by simp [hm0def, hD'0]
  set B0 : ℝ := ((N : ℝ) * (N * R' * R')) ^ q with hB0def
  have hB00 : 0 ≤ B0 := by positivity
  set Bd : ℝ≥0∞ := ENNReal.ofReal B0 with hBddef
  refine ⟨(m0 * d.μ W)⁻¹ * (Bd * μ K1), K', ?_, hK'k, fun ω hω hsc => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (mul_ne_zero hm0 hW0))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK1T)
  set G : HS L N → ℝ≥0∞ := fun p => (‖ω p‖₊ : ℝ≥0∞) with hGdef
  set Fr : Sp L N → ℝ≥0∞ := fun x => (‖fr ω (ofS L N x)‖₊ : ℝ≥0∞) with hFrdef
  have st1 : ∀ s ∈ W, m0 * ∫⁻ p in K, G p ∂μ ≤ ∫⁻ p in K1, G (actL (ofS L N s) p) ∂μ := by
    intro s hs
    have h := lintegral_cle_ge μ (actE (ofS L N s)) K1 K (hsub s hs) G
    simp only [actE_apply] at h
    have hdet0 : LinearMap.det (((actE (ofS L N s) : HS L N →L[ℝ] HS L N)) : HS L N →ₗ[ℝ] HS L N) ≠ 0 :=
      (LinearEquiv.isUnit_det' (actE (ofS L N s)).toLinearEquiv).ne_zero
    have hb : |LinearMap.det (((actE (ofS L N s) : HS L N →L[ℝ] HS L N)) : HS L N →ₗ[ℝ] HS L N)| ≤ D' := by
      have := hDm s hs
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    have hm : m0 ≤ ENNReal.ofReal
        |(LinearMap.det (((actE (ofS L N s) : HS L N →L[ℝ] HS L N)) : HS L N →ₗ[ℝ] HS L N))⁻¹| := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_inv]
      exact inv_anti₀ (abs_pos.2 hdet0) hb
    calc m0 * ∫⁻ p in K, G p ∂μ ≤ ENNReal.ofReal
          |(LinearMap.det (((actE (ofS L N s) : HS L N →L[ℝ] HS L N)) : HS L N →ₗ[ℝ] HS L N))⁻¹| *
            ∫⁻ p in K, G p ∂μ := by gcongr
      _ ≤ _ := h
  have st2 : (m0 * ∫⁻ p in K, G p ∂μ) * d.μ W ≤
      ∫⁻ s in W, ∫⁻ p in K1, G (actL (ofS L N s) p) ∂μ ∂d.μ := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' hWm st1
  haveI : IsFiniteMeasure (d.μ.restrict W) := isFiniteMeasure_restrict.2 hWT
  haveI : IsFiniteMeasure (μ.restrict K1) := isFiniteMeasure_restrict.2 hK1T
  have hmeas : AEMeasurable (Function.uncurry fun (s : Sp L N) (p : HS L N) => G (actL (ofS L N s) p))
      ((d.μ.restrict W).prod (μ.restrict K1)) := by
    have e1 : d.μ.restrict W = (d.μ.restrict W).restrict W := by
      rw [Measure.restrict_restrict hWm, Set.inter_self]
    have e2 : μ.restrict K1 = (μ.restrict K1).restrict K1 := by
      rw [Measure.restrict_restrict hK1m, Set.inter_self]
    rw [e1, e2, Measure.prod_restrict]
    refine ContinuousOn.aemeasurable ?_ (hWm.prod hK1m)
    have hc : ContinuousOn (fun p : Sp L N × HS L N => ω (actL (ofS L N p.1) p.2)) (W ×ˢ K1) :=
      hω.comp cont_act.continuousOn fun p hp => actL_pos _ (hK1P hp.2)
    exact (ENNReal.continuous_coe.comp continuous_nnnorm).comp_continuousOn hc
  have st3 := lintegral_lintegral_swap hmeas
  have st4 : ∀ p ∈ K1, ∫⁻ s in W, G (actL (ofS L N s) p) ∂d.μ ≤ Bd * ∫⁻ x in K', Fr x ∂d.μ := by
    intro p hp
    obtain ⟨c, t, hct, hy, ht⟩ := hR p hp
    have hpt : ∀ s ∈ W, G (actL (ofS L N s) p) ≤ Bd * Fr (s * t) := by
      intro s hs
      have hX : ∀ w i j, ‖(((ofS L N s * (scal L N c * ofS L N t)) w : GL (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R' := by
        intro w i j
        rw [coe_mul_ofS]
        exact entry_mul_le (Wn_bdd s hs w) (hy w) i j
      have h := point_bd hsc c t s R' hR'0 hX
      rw [hct] at h
      simp only [hGdef, hFrdef, hBddef, ENNReal.ofReal, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
      rw [← NNReal.coe_le_coe, NNReal.coe_mul, Real.coe_toNNReal _ hB00, coe_nnnorm, coe_nnnorm, mul_comm]
      exact h
    have hts : ∀ x, x * t⁻¹ ∈ W → x ∈ K' := by
      intro x hx
      obtain ⟨y, hyW, rfl⟩ : ∃ y ∈ W, y * t = x := ⟨x * t⁻¹, hx, by group⟩
      intro w i j
      have e : (((y * t) w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
          ((y w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
            ((t w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := rfl
      have := entry_mul_le (Wn_bdd y hyW w) (ht w) i j
      rw [← e] at this
      exact this
    calc ∫⁻ s in W, G (actL (ofS L N s) p) ∂d.μ ≤ ∫⁻ s in W, Bd * Fr (s * t) ∂d.μ :=
          setLIntegral_mono' hWm hpt
      _ = Bd * ∫⁻ s in W, Fr (s * t) ∂d.μ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ Bd * ∫⁻ x in K', Fr x ∂d.μ := mul_le_mul_right (right_trans_le d.μ W K' hWm hK'm t hts Fr) _
  have st5 : ∫⁻ p in K1, ∫⁻ s in W, G (actL (ofS L N s) p) ∂d.μ ∂μ ≤
      (Bd * ∫⁻ x in K', Fr x ∂d.μ) * μ K1 := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' hK1m st4
  have hall : (m0 * ∫⁻ p in K, G p ∂μ) * d.μ W ≤ (Bd * ∫⁻ x in K', Fr x ∂d.μ) * μ K1 :=
    st2.trans (st3.le.trans st5)
  have ha0 : m0 * d.μ W ≠ 0 := mul_ne_zero hm0 hW0
  have haT : m0 * d.μ W ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWT
  calc ∫⁻ p in K, G p ∂μ = (m0 * d.μ W)⁻¹ * ((m0 * d.μ W) * ∫⁻ p in K, G p ∂μ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 haT, one_mul]
    _ ≤ (m0 * d.μ W)⁻¹ * ((Bd * ∫⁻ x in K', Fr x ∂d.μ) * μ K1) := by
        refine mul_le_mul_right ?_ _
        calc (m0 * d.μ W) * ∫⁻ p in K, G p ∂μ = (m0 * ∫⁻ p in K, G p ∂μ) * d.μ W := by ring
          _ ≤ _ := hall
    _ = (m0 * d.μ W)⁻¹ * (Bd * μ K1) * ∫⁻ x in K', Fr x ∂d.μ := by ring

end PositivityTheory.KB.LocalOverlapAverage

end
