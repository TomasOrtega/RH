import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.ReNonnegPsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Locfin

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL PositivityTheory.KB PositivityTheory.KB.SmoothPartitionUnityBasic.BasicAux
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

/- English proof (translation)
Unfold `qR`. Rewrite using `[Finset.sum_eq_single w (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp) (fun hw => absurd (Finset.mem_univ w) hw), Pi.single_eq_same]`.
-/
private theorem b_qR_single {L : Type} [Field L] [NumberField L] {N : ℕ} [DecidableEq (InfinitePlace L)]
    (h : HS L N) (w : InfinitePlace L) (x : Fin N → ℂ) :
    qR h (Pi.single w x) = (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  unfold qR
  rw [Finset.sum_eq_single w (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
    (fun hw => absurd (Finset.mem_univ w) hw), Pi.single_eq_same]

/- English proof (translation)
The claim follows from `|(star x ⬝ᵥ (mat k w *ᵥ x)).re - (star x ⬝ᵥ (mat h w *ᵥ x)).re| ≤ δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re := by classical have := hcl (Pi.single w x) rwa [b_qR_single, b_qR_single] at this`.
-/
private theorem b_cl_at {L : Type} [Field L] [NumberField L] {N : ℕ} {δ : ℝ} {h k : HS L N}
    (hcl : Cl δ h k) (w : InfinitePlace L) (x : Fin N → ℂ) :
    |(star x ⬝ᵥ (mat k w *ᵥ x)).re - (star x ⬝ᵥ (mat h w *ᵥ x)).re| ≤ δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  classical
  have := hcl (Pi.single w x)
  rwa [b_qR_single, b_qR_single] at this

/- English proof (translation)
Take `⟨a, ha⟩` from `Function.ne_iff.1 hv`. Take `⟨w⟩ : Nonempty (InfinitePlace L)` from `inferInstance`. Introduce `h0`. Use `congrFun (congrFun h0 w) a` as an intermediate fact. Simplify using `only [toR, Pi.zero_apply] at this ha`.

Apply `ha` to reduce the goal to its premises. Simplify `this` using `[embO]`.
-/
private theorem b_toR_ne {L : Type} [Field L] [NumberField L] {N : ℕ} {v : Lat L N} (hv : v ≠ 0) :
    toR v ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hv
  obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
  intro h0
  have := congrFun (congrFun h0 w) a
  simp only [toR, Pi.zero_apply] at this ha
  apply ha
  simpa [embO] using this

/- English proof (translation)
Take `⟨c, hc, hev⟩` from `UpperTheory.V.KT.lowbd L N h hh`. Establish `h1` using `hev.self_of_nhds z`. Establish `: 0 < ‖z‖` using `norm_pos_iff.2 hz`. Establish `h2 : 0 < ‖z‖ ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem b_qR_pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N} (hh : h ∈ Pos L N)
    {z : VR L N} (hz : z ≠ 0) : 0 < qR h z := by
  obtain ⟨c, hc, hev⟩ := UpperTheory.V.KT.lowbd L N h hh
  have h1 := hev.self_of_nhds z
  have : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2 : 0 < ‖z‖ ^ 2 := by positivity
  nlinarith

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[emb, toP, toK, embO, Matrix.GeneralLinearGroup.map_apply]`.
-/
private theorem b_emb_val {L : Type} [Field L] [NumberField L] {N : ℕ} (γ : Gm L N) (w : InfinitePlace L) :
    (((emb L N γ) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  ext i j
  simp [emb, toP, toK, embO, Matrix.GeneralLinearGroup.map_apply]

/- English proof (translation)
Rewrite using `[← b_emb_val, map_inv, Pi.inv_apply]`.
-/
private theorem b_ginv {L : Type} [Field L] [NumberField L] {N : ℕ} (γ : Gm L N) (w : InfinitePlace L) :
    ((((emb L N γ) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  rw [← b_emb_val, map_inv, Pi.inv_apply]

/- English proof (translation)
Rewrite using `[star_star, mulVec_transpose, dotProduct_comm (star z), ← dotProduct_mulVec]`.
-/
private theorem b_transp {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → ℂ) :
    star z ⬝ᵥ (Mᵀ *ᵥ z) = star (star z) ⬝ᵥ (M *ᵥ star z) := by
  rw [star_star, mulVec_transpose, dotProduct_comm (star z), ← dotProduct_mulVec]

/- English proof (translation)
Introduce `L _ _ N hN`. Use `⟨?p1, ?p2, ?p3, ?p4, ?p5, ?p6⟩` and prove the remaining obligations. Introduce `h hh`. Establish `hfin : ∀ B : ℝ, {v : Lat L N | q h v ≤ B}.Finite` using `fun B => by`. Take `⟨S, hS, hev⟩` from `UpperTheory.V.KT.locfin L N h hh B`.

Use `hS.subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hvS`. Conclude with `absurd hv (not_le.2 (hev.self_of_nhds v hvS))`. Establish `hpos : ∀ v : Lat L N, v ≠ 0 → 0 < q h v` using `fun v hv => b_qR_pos hh (b_toR_ne hv)`. Choose the witnesses or unpack the hypotheses as in `⟨v0, hv0⟩ : ∃ v0 : Lat L N, v0 ≠ 0 := by`.

Use `⟨Pi.single (⟨0, hN⟩ : Fin N) 1, fun h0 => ?_⟩` and prove the remaining obligations. Use `congrFun h0 ⟨0, hN⟩` as an intermediate fact. Simplify using `at this`. Take `⟨vm, ⟨hvm0, -⟩, hvm⟩` from `Set.exists_min_image {v : Lat L N | v ≠ 0 ∧ q h v ≤ q h v0} (fun v => q h v) ((hfin (q h v0)).subset fun v hv => hv.2) ⟨v0, hv0, le_rfl⟩`. Establish `mlow : ∀ v : Lat L N, v ≠ 0 → q h vm ≤ q h v` using `fun v hv => by`.

Distinguish the cases in `hle : q h v ≤ q h v0`. Conclude with `hvm v ⟨hv, hle⟩`. Conclude with `(hvm v0 ⟨hv0, le_rfl⟩).trans (not_le.1 hle).le`. Use `haveI : Nonempty {y : Lat L N // y ≠ 0} := ⟨⟨v0, hv0⟩⟩`. Establish `hlam : lam h = q h vm`.

Unfold `lam`. Use `le_antisymm (ciInf_le ⟨q h vm, ?_⟩ (⟨vm, hvm0⟩ : {y : Lat L N // y ≠ 0})) (le_ciInf fun y => mlow y.1 y.2)` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `mlow y.1 y.2`. Use `⟨by rw [hlam]; exact hpos vm hvm0, fun v hv => by rw [hlam]; exact mlow v hv, ⟨vm, hvm0, hlam.symm⟩, fun w => ?_, hfin⟩` and prove the remaining obligations.

Conclude with `(hh w).inv.transpose`. Introduce `γ h v`. Simplify using `only [q, qR, ac, mat_actL, smul_lat, toR_mulVec, b_ginv]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]`.

Introduce `γ`. Set `γt : Gm L N` to `⟨(γ : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ, ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one], by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩`. Use `⟨γt⁻¹, fun h hh => HS_ext fun w => ?_⟩` and prove the remaining obligations. Simplify using `only [dualH, mat_mkHS, ac, mat_actL, b_ginv, inv_inv]`. Establish `hT : ((γt : Matrix (Fin N) (Fin N) (𝓞 L))).map (embO w) = ((γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w))ᵀ`.

Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[hT]`. Use `set M := (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hM`. Use `set G := ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hG`.

Establish `hMG : M * G = 1`. Rewrite using `[hM, hG, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hGinv : G⁻¹ = M` using `Matrix.inv_eq_left_inv hMG`. Establish `hCT : Mᴴᵀ = Mᵀᴴ` using `by ext i j; simp`. Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, hGinv, ← conjTranspose_nonsing_inv, hGinv, transpose_mul, transpose_mul, hCT]`.

Introduce `δ hδ hδ2 h hh k hcl`. Establish `hat` using `fun w x => b_cl_at hcl w x`. Establish `hk : k ∈ Pos L N` using `fun w => by`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos (mat_herm k w) (by` and prove the remaining obligations. Introduce `x hx`.

Establish `h1` using `(Complex.pos_iff.1 ((hh w).dotProduct_mulVec_pos hx)).1`. Establish `h2` using `(abs_le.1 (hat w x)).1`. Conclude with `Complex.pos_iff.2 ⟨by nlinarith, (herm_im _ (mat_herm k w) x).symm⟩)`. Use `⟨hk, fun z => ?_⟩` and prove the remaining obligations. Establish `per : ∀ w, |(star (z w) ⬝ᵥ (mat (dualH k) w *ᵥ z w)).re - (star (z w) ⬝ᵥ (mat (dualH h) w *ᵥ z w)).re| ≤ 2 * δ * (star (z w) ⬝ᵥ (mat (dualH h) w *ᵥ z w)).re`.

Introduce `w`. Simplify using `only [dualH, mat_mkHS]`. Rewrite using `[b_transp, b_transp]`. Establish `i1` using `invmono (mat h w) (mat k w) (hh w) (hk w) (1 - δ) (by linarith) (fun x => by have := (abs_le.1 (hat w x)).1; rw [sub_mul, one_mul]; linarith) (star (z w))`. Establish `i2` using `invmono (mat k w) (mat h w) (hk w) (hh w) (1 + δ)⁻¹ (by positivity) (fun x => by`.

Rewrite using `[inv_mul_le_iff₀ (by linarith)]`. Use `(abs_le.1 (hat w x)).2` as an intermediate fact. Rewrite using `[add_mul, one_mul]`. Use the proof step `linarith) (star (z w))`. Establish `hD` using `re_nonneg_psd (hh w).inv.posSemidef (star (z w))`.

Establish `i2'` using `mul_le_mul_of_nonneg_left i2 (by linarith : (0 : ℝ) ≤ 1 + δ)`. Rewrite `i2'` using `[← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul]`. Use `abs_le.2 ⟨by nlinarith [mul_nonneg hδ hD], by nlinarith [mul_nonneg hδ hD]⟩` and prove the remaining obligations. Unfold `qR`. Rewrite using `[← Finset.sum_sub_distrib, Finset.mul_sum]`.

Conclude with `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => per w)`. Introduce `δ hδ h hh k hcl w u v`. Establish `hat` using `fun x => b_cl_at hcl w x`. Establish `hA : (mat k w - mat h w).IsHermitian` using `(mat_herm k w).sub (mat_herm h w)`. Establish `hb : ∀ x : Fin N → ℂ, |(star x ⬝ᵥ ((mat k w - mat h w) *ᵥ x)).re| ≤ δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re`.

Introduce `x`. Rewrite using `[sub_mulVec, dotProduct_sub, Complex.sub_re]`. Conclude with `hat x`. Use `csq _ _ hA (hh w).posSemidef δ hδ hb u v` as an intermediate fact. Rewrite `this` using `[sub_mulVec, dotProduct_sub]`.

Establish `ha` using `re_nonneg_psd (hh w).posSemidef u`. Establish `hb'` using `re_nonneg_psd (hh w).posSemidef v`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg (sq_nonneg δ) ha) hb']`. Take `⟨P, hP⟩` from `Submodule.ClosedComplemented.of_finiteDimensional (𝕜 := ℝ) (HSsub L N)`. Establish `hent : ∀ w a b, ContDiff ℝ (⊤ : ℕ∞) (fun h : HS L N => mat h w a b)` using `fun w a b => by`.

Establish `e : (fun h : HS L N => mat h w a b) = (fun x : InfinitePlace L → Fin N → Fin N → ℂ => x w a b) ∘ (HSsub L N).subtypeL` using `rfl`. Rewrite using `[e]`. Conclude with `(contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id w) a) b).comp (HSsub L N).subtypeL.contDiff`. Establish `hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun h : HS L N => ((dualH h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ)) (Pos L N)`. Use `contDiffOn_pi' fun w => contDiffOn_pi' fun a => contDiffOn_pi' fun b => ?_` and prove the remaining obligations.

Introduce `h hh`. Establish `hdet : (mat h w).det ≠ 0` using `((hh w).det_pos).ne'`. Conclude with `(cd_inv (fun h : HS L N => mat h w) (fun i j => hent w i j) b a h hdet).contDiffWithinAt`. Establish `e : (dualH : HS L N → HS L N) = fun h => P ((dualH h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ)`. Use function extensionality and compare the values at `h`.

Conclude with `(hP (dualH h)).symm`. Rewrite using `[e]`. Conclude with `P.contDiff.comp_contDiffOn hF`.
-/
theorem pf_Basic : Basic := by
  intro L _ _ N hN
  classical
  refine ⟨?p1, ?p2, ?p3, ?p4, ?p5, ?p6⟩
  · intro h hh
    have hfin : ∀ B : ℝ, {v : Lat L N | q h v ≤ B}.Finite := fun B => by
      obtain ⟨S, hS, hev⟩ := UpperTheory.V.KT.locfin L N h hh B
      refine hS.subset fun v hv => ?_
      by_contra hvS
      exact absurd hv (not_le.2 (hev.self_of_nhds v hvS))
    have hpos : ∀ v : Lat L N, v ≠ 0 → 0 < q h v := fun v hv => b_qR_pos hh (b_toR_ne hv)
    obtain ⟨v0, hv0⟩ : ∃ v0 : Lat L N, v0 ≠ 0 := by
      refine ⟨Pi.single (⟨0, hN⟩ : Fin N) 1, fun h0 => ?_⟩
      have := congrFun h0 ⟨0, hN⟩
      simp at this
    obtain ⟨vm, ⟨hvm0, -⟩, hvm⟩ := Set.exists_min_image {v : Lat L N | v ≠ 0 ∧ q h v ≤ q h v0}
      (fun v => q h v) ((hfin (q h v0)).subset fun v hv => hv.2) ⟨v0, hv0, le_rfl⟩
    have mlow : ∀ v : Lat L N, v ≠ 0 → q h vm ≤ q h v := fun v hv => by
      by_cases hle : q h v ≤ q h v0
      · exact hvm v ⟨hv, hle⟩
      · exact (hvm v0 ⟨hv0, le_rfl⟩).trans (not_le.1 hle).le
    haveI : Nonempty {y : Lat L N // y ≠ 0} := ⟨⟨v0, hv0⟩⟩
    have hlam : lam h = q h vm := by
      unfold lam
      refine le_antisymm (ciInf_le ⟨q h vm, ?_⟩ (⟨vm, hvm0⟩ : {y : Lat L N // y ≠ 0}))
        (le_ciInf fun y => mlow y.1 y.2)
      rintro _ ⟨y, rfl⟩
      exact mlow y.1 y.2
    refine ⟨by rw [hlam]; exact hpos vm hvm0, fun v hv => by rw [hlam]; exact mlow v hv,
      ⟨vm, hvm0, hlam.symm⟩, fun w => ?_, hfin⟩
    exact (hh w).inv.transpose
  · intro γ h v
    simp only [q, qR, ac, mat_actL, smul_lat, toR_mulVec, b_ginv]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  · intro γ
    let γt : Gm L N := ⟨(γ : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ, ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ,
      by rw [← transpose_mul, Units.inv_mul, transpose_one],
      by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
    refine ⟨γt⁻¹, fun h hh => HS_ext fun w => ?_⟩
    simp only [dualH, mat_mkHS, ac, mat_actL, b_ginv, inv_inv]
    have hT : ((γt : Matrix (Fin N) (Fin N) (𝓞 L))).map (embO w) =
        ((γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w))ᵀ := by
      ext i j; rfl
    rw [hT]
    set M := (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hM
    set G := ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hG
    have hMG : M * G = 1 := by
      rw [hM, hG, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have hGinv : G⁻¹ = M := Matrix.inv_eq_left_inv hMG
    have hCT : Mᴴᵀ = Mᵀᴴ := by ext i j; simp
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hGinv, ← conjTranspose_nonsing_inv, hGinv,
      transpose_mul, transpose_mul, hCT]
  · intro δ hδ hδ2 h hh k hcl
    have hat := fun w x => b_cl_at hcl w x
    have hk : k ∈ Pos L N := fun w => by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos (mat_herm k w) (by
        intro x hx
        have h1 := (Complex.pos_iff.1 ((hh w).dotProduct_mulVec_pos hx)).1
        have h2 := (abs_le.1 (hat w x)).1
        exact Complex.pos_iff.2 ⟨by nlinarith, (herm_im _ (mat_herm k w) x).symm⟩)
    refine ⟨hk, fun z => ?_⟩
    have per : ∀ w, |(star (z w) ⬝ᵥ (mat (dualH k) w *ᵥ z w)).re -
        (star (z w) ⬝ᵥ (mat (dualH h) w *ᵥ z w)).re| ≤
        2 * δ * (star (z w) ⬝ᵥ (mat (dualH h) w *ᵥ z w)).re := by
      intro w
      simp only [dualH, mat_mkHS]
      rw [b_transp, b_transp]
      have i1 := invmono (mat h w) (mat k w) (hh w) (hk w) (1 - δ) (by linarith)
        (fun x => by have := (abs_le.1 (hat w x)).1; rw [sub_mul, one_mul]; linarith) (star (z w))
      have i2 := invmono (mat k w) (mat h w) (hk w) (hh w) (1 + δ)⁻¹ (by positivity)
        (fun x => by
          rw [inv_mul_le_iff₀ (by linarith)]
          have := (abs_le.1 (hat w x)).2
          rw [add_mul, one_mul]; linarith) (star (z w))
      have hD := re_nonneg_psd (hh w).inv.posSemidef (star (z w))
      have i2' := mul_le_mul_of_nonneg_left i2 (by linarith : (0 : ℝ) ≤ 1 + δ)
      rw [← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul] at i2'
      refine abs_le.2 ⟨by nlinarith [mul_nonneg hδ hD], by nlinarith [mul_nonneg hδ hD]⟩
    unfold qR
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => per w)
  · intro δ hδ h hh k hcl w u v
    have hat := fun x => b_cl_at hcl w x
    have hA : (mat k w - mat h w).IsHermitian := (mat_herm k w).sub (mat_herm h w)
    have hb : ∀ x : Fin N → ℂ, |(star x ⬝ᵥ ((mat k w - mat h w) *ᵥ x)).re| ≤
        δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
      intro x; rw [sub_mulVec, dotProduct_sub, Complex.sub_re]; exact hat x
    have := csq _ _ hA (hh w).posSemidef δ hδ hb u v
    rw [sub_mulVec, dotProduct_sub] at this
    have ha := re_nonneg_psd (hh w).posSemidef u
    have hb' := re_nonneg_psd (hh w).posSemidef v
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg δ) ha) hb']
  · obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional (𝕜 := ℝ) (HSsub L N)
    have hent : ∀ w a b, ContDiff ℝ (⊤ : ℕ∞) (fun h : HS L N => mat h w a b) := fun w a b => by
      have e : (fun h : HS L N => mat h w a b) =
          (fun x : InfinitePlace L → Fin N → Fin N → ℂ => x w a b) ∘ (HSsub L N).subtypeL := rfl
      rw [e]
      exact (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id w) a) b).comp
        (HSsub L N).subtypeL.contDiff
    have hF : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun h : HS L N => ((dualH h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ)) (Pos L N) := by
      refine contDiffOn_pi' fun w => contDiffOn_pi' fun a => contDiffOn_pi' fun b => ?_
      intro h hh
      have hdet : (mat h w).det ≠ 0 := ((hh w).det_pos).ne'
      exact (cd_inv (fun h : HS L N => mat h w) (fun i j => hent w i j) b a h hdet).contDiffWithinAt
    have e : (dualH : HS L N → HS L N) =
        fun h => P ((dualH h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ) := by
      funext h; exact (hP (dualH h)).symm
    rw [e]
    exact P.contDiff.comp_contDiffOn hF

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
