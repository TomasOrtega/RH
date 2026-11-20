import Formalism.LocalToGlobal.HermitianForms.TiedBrUnit
import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingNormalisedOfAdjoint

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions MvPolynomial

section Row

variable {ι : Type} [Fintype ι] {n : ℕ}

def blkRow (K : ι → Matrix (Fin n) (Fin n) ℂ) : MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  aeval fun v => ∑ c : Fin n, C (K v.1 v.2.1 c) * X (v.1, c, v.2.2)

/- English proof (translation)
Unfold `blkRow`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp => simp only [map_mul, hp, aeval_X, map_sum, eval_C, eval_X]`.
-/
theorem eval_blkRow (K : ι → Matrix (Fin n) (Fin n) ℂ) (x : ι × Fin n × Fin n → ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    eval x (blkRow K P) = eval (fun v => ∑ c : Fin n, K v.1 v.2.1 c * x (v.1, c, v.2.2)) P := by
  unfold blkRow
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, aeval_X, map_sum, eval_C, eval_X]

/- English proof (translation)
Establish `h : (blkRow K).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (K τ))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[blkRow, Formalism.GradedWeylDivisibility.rowAct, rename_X, map_sum]`. Conclude with `congrArg (fun F : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] _ => F f) h`.
-/
theorem blkRow_rename (K : ι → Matrix (Fin n) (Fin n) ℂ) (τ : ι) (f : MvPolynomial (Fin n × Fin n) ℂ) :
    blkRow K (rename (Prod.mk τ) f) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.rowAct ℂ (K τ) f) := by
  have h : (blkRow K).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (K τ)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [blkRow, Formalism.GradedWeylDivisibility.rowAct, rename_X, map_sum]
  exact congrArg (fun F : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] _ => F f) h

/- English proof (translation)
Unfold `CSpan at hP ⊢`. Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem p hp`. Take `⟨f, hf, rfl⟩` from `hp`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (K τ) (f τ), fun τ => Formalism.L2.GlobalTheoryTheory.TraceIntegrality.delSq_rowAct _ _ _ (hf τ), ?_⟩` and prove the remaining obligations. Unfold `ten`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_congr rfl fun τ _ => blkRow_rename K τ (f τ)`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem blkRow_mem (K : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) {P : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hP : P ∈ CSpan lam) : blkRow K P ∈ CSpan lam := by
  unfold CSpan at hP ⊢
  induction hP using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f, hf, rfl⟩ := hp
    apply Submodule.subset_span
    refine ⟨fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (K τ) (f τ), fun τ => Formalism.L2.GlobalTheoryTheory.TraceIntegrality.delSq_rowAct _ _ _ (hf τ), ?_⟩
    unfold ten
    rw [map_prod]
    exact Finset.prod_congr rfl fun τ _ => blkRow_rename K τ (f τ)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/- English proof (translation)
Use function extensionality and compare the values at `y`. Establish `hK : ∀ τ, M' τ * (M τ)⁻¹ * (M τ * y.1 τ) = M' τ * y.1 τ` using `fun τ => by`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (M τ)⁻¹, Matrix.nonsing_inv_mul _ (hM τ), Matrix.one_mul]`. Simplify using `only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, map_smul, eval_blkRow, Pi.smul_apply, smul_eq_mul, ← Matrix.mul_apply, hK]`. Establish `hd : ∀ τ, (M' τ * y.1 τ).det ^ s τ = (M' τ * (M τ)⁻¹).det ^ s τ * (M τ * y.1 τ).det ^ s τ` using `fun τ => by`.

Rewrite using `[← hK τ, Matrix.det_mul, mul_zpow]`. Rewrite using `[Finset.prod_congr rfl fun τ _ => hd τ, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fnOf_change (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M M' : ι → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ τ, IsUnit (M τ).det) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    fnOf G s M' P = fnOf G s M ((∏ τ, (M' τ * (M τ)⁻¹).det ^ s τ) • blkRow (fun τ => M' τ * (M τ)⁻¹) P) := by
  funext y
  have hK : ∀ τ, M' τ * (M τ)⁻¹ * (M τ * y.1 τ) = M' τ * y.1 τ := fun τ => by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (M τ)⁻¹, Matrix.nonsing_inv_mul _ (hM τ), Matrix.one_mul]
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, map_smul, eval_blkRow, Pi.smul_apply, smul_eq_mul, ← Matrix.mul_apply, hK]
  have hd : ∀ τ, (M' τ * y.1 τ).det ^ s τ = (M' τ * (M τ)⁻¹).det ^ s τ * (M τ * y.1 τ).det ^ s τ := fun τ => by
    rw [← hK τ, Matrix.det_mul, mul_zpow]
  rw [Finset.prod_congr rfl fun τ _ => hd τ, Finset.prod_mul_distrib]
  ring

/- English proof (translation)
Simplify using `only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Frames.tr, Pi.one_apply, Matrix.one_mul]`.
-/
theorem fnOf_tr (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ τ, IsUnit (g τ).det) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Frames G) :
    fnOf G s 1 P (y.tr g hg) = fnOf G s g P y := by
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Frames.tr, Pi.one_apply, Matrix.one_mul]

/- English proof (translation)
Use `⟨χ • ((∏ τ, (M' τ * (M τ)⁻¹).det ^ s τ) • blkRow (fun τ => M' τ * (M τ)⁻¹) P0), Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (blkRow_mem _ _ hP0)), fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, Pi.smul_apply, smul_eq_mul, ← fnOf_change G s M M' hM, fnOf_tr]`.
-/
theorem exists_rep (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M M' : ι → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ τ, IsUnit (M τ).det) (hM' : ∀ τ, IsUnit (M' τ).det) (P0 : MvPolynomial (ι × Fin n × Fin n) ℂ) (hP0 : P0 ∈ CSpan lam)
    (χ : ℂ) : ∃ P ∈ CSpan lam, ∀ y : Frames G, χ * fnOf G s 1 P0 (y.tr M' hM') = fnOf G s M P y := by
  refine ⟨χ • ((∏ τ, (M' τ * (M τ)⁻¹).det ^ s τ) • blkRow (fun τ => M' τ * (M τ)⁻¹) P0),
    Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (blkRow_mem _ _ hP0)), fun y => ?_⟩
  rw [map_smul, Pi.smul_apply, smul_eq_mul, ← fnOf_change G s M M' hM, fnOf_tr]

end Row

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Establish `hF` using `((Tf.val D.R.m le_rfl).Fi φ).1 hφ`. Take `⟨g, hg, hres⟩` from `Submodule.mem_map.1 hF`. Establish `hval` using `(Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) ((Tf.cls D.R.m le_rfl).y ((D.fm u).til c)) (Set.mem_univ _)`. Take `⟨P0, hP0, hfn⟩` from `Submodule.mem_map.1 hval`. Establish `hP0' : P0 ∈ CSpan ((D.fm u).lam D.R.m)`.

Use `CSpan_shW ((D.fm u).lam D.R.m) (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))` as an intermediate fact. Unfold `lamT at hP0`. Rewrite `hP0` using `[this]`. Conclude with `hP0`. Establish `hφv : ∀ z, φ ((D.fm u).til c) ((Tf.val D.R.m le_rfl).eY.symm z) = fnOf _ (shiftOf (lamT u D.R.m)) 1 P0 z`.

Introduce `z`. Use `congrFun (congrFun hres ((D.fm u).til c)) z` as an intermediate fact. Rewrite using `[← this, hfn]`. Both sides reduce to the same expression. Use `set ginv : GL (Fin (D.R.N D.R.m)) D.host.E := ((Tf.til.ga c).1)⁻¹`.

Use `set M' : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := atInf (embT D) (ginv : Matrix _ _ D.host.E)`. Establish `hB` using `mZ_isUnit (bZ_isUnit Tf)`. Take `⟨P, hP, hPy⟩` from `exists_rep ((D.fm u).lam D.R.m) _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) M' hB (isUnit_det_atInf (embT D) ginv) P0 hP0' ((((Tf.cls D.R.m le_rfl).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ)`. Use `⟨P, hP, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[Tf.evz φ c s ((Tf.val D.R.m le_rfl).eY.symm (((Tf.val D.R.m le_rfl).eY s).tr M' (isUnit_det_atInf (embT D) ginv)))]`.

Rewrite using `[hφv]`. Conclude with `hPy _`. Introduce `τ`. Simplify using `only [Equiv.apply_symm_apply]`. Use `show ((Tf.val D.R.m le_rfl).eY s).1 τ = atInf (embT D) (Tf.til.ga c).1.1 τ * (M' τ * ((Tf.val D.R.m le_rfl).eY s).1 τ)`.

Rewrite using `[← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]`.
-/
theorem val_rep (Tf : FormsTied D u) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) (c : (D.fm u).clsP) :
    ∃ P ∈ CSpan ((D.fm u).lam D.R.m), ∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl).eY s) := by
  have hF := ((Tf.val D.R.m le_rfl).Fi φ).1 hφ
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) ((Tf.cls D.R.m le_rfl).y ((D.fm u).til c)) (Set.mem_univ _)
  obtain ⟨P0, hP0, hfn⟩ := Submodule.mem_map.1 hval
  have hP0' : P0 ∈ CSpan ((D.fm u).lam D.R.m) := by
    have := CSpan_shW ((D.fm u).lam D.R.m) (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold lamT at hP0
    rw [this] at hP0
    exact hP0
  have hφv : ∀ z, φ ((D.fm u).til c) ((Tf.val D.R.m le_rfl).eY.symm z) =
      fnOf _ (shiftOf (lamT u D.R.m)) 1 P0 z := by
    intro z
    have := congrFun (congrFun hres ((D.fm u).til c)) z
    rw [← this, hfn]
    rfl
  set ginv : GL (Fin (D.R.N D.R.m)) D.host.E := ((Tf.til.ga c).1)⁻¹
  set M' : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := atInf (embT D) (ginv : Matrix _ _ D.host.E)
  have hB := mZ_isUnit (bZ_isUnit Tf)
  obtain ⟨P, hP, hPy⟩ := exists_rep ((D.fm u).lam D.R.m) _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) M' hB
    (isUnit_det_atInf (embT D) ginv) P0 hP0' ((((Tf.cls D.R.m le_rfl).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ)
  refine ⟨P, hP, fun s => ?_⟩
  rw [Tf.evz φ c s ((Tf.val D.R.m le_rfl).eY.symm (((Tf.val D.R.m le_rfl).eY s).tr M' (isUnit_det_atInf (embT D) ginv)))]
  · rw [hφv]; exact hPy _
  · intro τ
    simp only [Equiv.apply_symm_apply]
    show ((Tf.val D.R.m le_rfl).eY s).1 τ = atInf (embT D) (Tf.til.ga c).1.1 τ * (M' τ * ((Tf.val D.R.m le_rfl).eY s).1 τ)
    rw [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]

end Formalism.L2.Forms
