import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitCut

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Simplify using `only [incM, ← Matrix.map_mul, Units.mul_inv]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_mul_inv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  simp only [incM, ← Matrix.map_mul, Units.mul_inv]
  exact Matrix.map_one _ (map_zero _) (map_one _)
/- English proof (translation)
Simplify using `only [incM, ← Matrix.map_mul, Units.inv_mul]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_inv_mul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  simp only [incM, ← Matrix.map_mul, Units.inv_mul]
  exact Matrix.map_one _ (map_zero _) (map_one _)
/- English proof (translation)
Establish `h1` using `_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d`. Establish `e : mat2 (x * y) = mat2 x * mat2 y` using `rfl`. Simplify using `only [inFrame, e]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, Matrix.mul_one]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.
-/
theorem inFrame_mul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  have h1 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d
  have e : mat2 (x * y) = mat2 x * mat2 y := rfl
  simp only [inFrame, e]
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 y) * incM F d.b.1
      = incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 y * incM F d.b.1 := by
        rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]
/- English proof (translation)
Simplify using `only [inFrame, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.mul_one]`.
-/
theorem matrixRep_eq_frameConj_inFrame (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) : mat2 x = incM F d.b.1 * inFrame d.b x * incM F (d.b⁻¹).1 := by
  simp only [inFrame, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.one_mul]
  rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.mul_one]
/- English proof (translation)
Introduce `x y h`. Establish `: mat2 x = mat2 y` using `by rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.matrixRep_eq_frameConj_inFrame d x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.matrixRep_eq_frameConj_inFrame d y, h]`. Conclude with `Subtype.ext (Units.ext this)`.
-/
theorem inFrame_injective_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Function.Injective (inFrame (σ := σ) (Y := d.Y) d.b) := by
  intro x y h
  have : mat2 x = mat2 y := by rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.matrixRep_eq_frameConj_inFrame d x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.matrixRep_eq_frameConj_inFrame d y, h]
  exact Subtype.ext (Units.ext this)
/- English proof (translation)
The claim follows from `d.ok.dbl.weil.2.1.pres g Φ h`.
-/
theorem om_mem_sch_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om g Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres g Φ h
/- English proof (translation)
Simplify using `[_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, map_mul, Module.End.mul_apply]`.
-/
theorem constantTerm_mul_right (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) (g k : d.G) : d.sec0 Φ (g * k) = d.sec0 (d.om k Φ) g := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, map_mul, Module.End.mul_apply]
/- English proof (translation)
Take `⟨p, t, hp, k', hk', rfl⟩` from `d.ok.hgt.iwa g`. Rewrite using `[mul_assoc, d.ok.hgt.val p t hp _ (d.K.mul_mem hk' hk), d.ok.hgt.val p t hp _ hk']`.
-/
theorem a_mul_K_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g k : d.G) (hk : k ∈ d.K) : d.a (g * k) = d.a g := by
  obtain ⟨p, t, hp, k', hk', rfl⟩ := d.ok.hgt.iwa g
  rw [mul_assoc, d.ok.hgt.val p t hp _ (d.K.mul_mem hk' hk), d.ok.hgt.val p t hp _ hk']
/- English proof (translation)
Use `⟨_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d k hΦ.1, ?_⟩` and prove the remaining obligations. Establish `hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ))` using `hΦ.2`. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k', rfl⟩`. Use `Submodule.subset_span ⟨⟨k'.1 * k, d.K.mul_mem k'.2 hk⟩, ?_⟩` and prove the remaining obligations.

Simplify using `[map_mul, Module.End.mul_apply]`.
-/
theorem kfin_om_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ : d.Fn} (hΦ : d.KFin Φ) {k : d.G} (hk : k ∈ d.K) : d.KFin (d.om k Φ) := by
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d k hΦ.1, ?_⟩
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ)) := hΦ.2
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨k', rfl⟩
  refine Submodule.subset_span ⟨⟨k'.1 * k, d.K.mul_mem k'.2 hk⟩, ?_⟩
  simp [map_mul, Module.End.mul_apply]
section Forms
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
end Forms
local notation:70 X:70 " ⬝ " Y:71 => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid X Y
/- English proof (translation)
Take `⟨⟨ε, hε⟩, -⟩` from `d.ok.frame`. Use `⟨incM F (((ε : ℤ) : E) • (1 : Matrix (Fin d.n) (Fin d.n) E)), ?_⟩` and prove the remaining obligations. Establish `e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ)`. Use extensionality with `i j`. Simplify using `[incM, cA, inclR, Algebra.TensorProduct.map_tmul]`.

Establish `e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J)`. Simplify using `[dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]`. Establish `key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) = (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ)`. Simplify using `only [incM, Matrix.map_mul, Matrix.transpose_map]`. Rewrite using `[e1, e2, ← key, hε]`.

Simplify using `[incM, Matrix.fromBlocks_map]`.
-/
theorem frame_form_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ C' : Matrix (Fin d.n) (Fin d.n) (AE F E),
    (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) = Matrix.fromBlocks 0 1 C' 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  refine ⟨incM F (((ε : ℤ) : E) • (1 : Matrix (Fin d.n) (Fin d.n) E)), ?_⟩
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [e1, e2, ← key, hε]
  simp [incM, Matrix.fromBlocks_map]
/- English proof (translation)
Take `⟨-, tb, htb⟩` from `d.ok.frame`. Set `E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)` to `Matrix.fromRows 1 0`. Set `DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)` to `diagCols (Fin d.n)`. Establish `htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) ⬝ tb.1` using `htb`. Establish `hp' : mat2 p ⬝ DC = DC ⬝ t.1` using `hp`.

Establish `hcol : ∀ M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), M ⬝ E1 = M.toCols₁`. Introduce `M`. Use extensionality with `i j`. Simplify using `[E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]`. Establish `h1 : incM F d.b.1 ⬝ E1 = incM F (d.b.1.toCols₁)`.

Rewrite using `[hcol]`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) ⬝ tb.1) = DC ⬝ incM F tb.1`. Rewrite using `[incM_mul']`.

Use `congr 1`. Use extensionality with `i j`. Apply the tactic sequence `cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all`. Establish `hb : incM F d.b.1 ⬝ E1 = DC ⬝ incM F tb.1` using `h1.trans ((congrArg (incM F) htb').trans h2)`. Establish `hTb : incM F tb.1 ⬝ incM F (tb⁻¹).1 = 1`.

Rewrite using `[← incM_mul', Units.mul_inv]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hBB : incM F (d.b⁻¹).1 ⬝ incM F d.b.1 = 1` using `_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d`. Establish `hdc : DC = incM F d.b.1 ⬝ E1 ⬝ incM F (tb⁻¹).1`. Rewrite using `[hb, Matrix.mul_assoc, hTb, Matrix.mul_one]`.

Establish `key : inFrame d.b p ⬝ E1 = E1 ⬝ (incM F (tb⁻¹).1 ⬝ t.1 ⬝ incM F tb.1)`. Establish `e0 : inFrame d.b p = incM F (d.b⁻¹).1 ⬝ mat2 p ⬝ incM F d.b.1` using `rfl`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e0]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = incM F (d.b⁻¹).1 ⬝ ((mat2 p ⬝ DC) ⬝ incM F tb.1) := by`. Rewrite using `[hb, Matrix.mul_assoc]`. Use `_ = incM F (d.b⁻¹).1 ⬝ ((DC ⬝ t.1) ⬝ incM F tb.1) := by rw [hp']`. Use `_ = (incM F (d.b⁻¹).1 ⬝ incM F d.b.1) ⬝ E1 ⬝ (incM F (tb⁻¹).1 ⬝ t.1 ⬝ incM F tb.1) := by`. Rewrite using `[hdc]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hBB, Matrix.one_mul]`. Use extensionality with `i j`. Use `congrFun (congrFun key (Sum.inr i)) j` as an intermediate fact. Rewrite `this` using `[hcol]`.

Simplify `this` using `[E1, Matrix.toBlocks₂₁, Matrix.toCols₁, Matrix.mul_apply, Fintype.sum_sum_type]`.
-/
theorem parabolic_lowerLeft_block_zero (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    (inFrame d.b p).toBlocks₂₁ = 0 := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) ⬝ tb.1 := htb
  have hp' : mat2 p ⬝ DC = DC ⬝ t.1 := hp
  have hcol : ∀ M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), M ⬝ E1 = M.toCols₁ := by
    intro M
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 ⬝ E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) ⬝ tb.1) = DC ⬝ incM F tb.1 := by
    rw [incM_mul']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all
  have hb : incM F d.b.1 ⬝ E1 = DC ⬝ incM F tb.1 := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 ⬝ incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hBB : incM F (d.b⁻¹).1 ⬝ incM F d.b.1 = 1 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d
  have hdc : DC = incM F d.b.1 ⬝ E1 ⬝ incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have key : inFrame d.b p ⬝ E1 = E1 ⬝ (incM F (tb⁻¹).1 ⬝ t.1 ⬝ incM F tb.1) := by
    have e0 : inFrame d.b p = incM F (d.b⁻¹).1 ⬝ mat2 p ⬝ incM F d.b.1 := rfl
    calc inFrame d.b p ⬝ E1 = incM F (d.b⁻¹).1 ⬝ (mat2 p ⬝ (incM F d.b.1 ⬝ E1)) := by
          rw [e0]; simp only [Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 ⬝ ((mat2 p ⬝ DC) ⬝ incM F tb.1) := by
          rw [hb, Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 ⬝ ((DC ⬝ t.1) ⬝ incM F tb.1) := by rw [hp']
      _ = (incM F (d.b⁻¹).1 ⬝ incM F d.b.1) ⬝ E1 ⬝ (incM F (tb⁻¹).1 ⬝ t.1 ⬝ incM F tb.1) := by
          rw [hdc]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBB, Matrix.one_mul]
  ext i j
  have := congrFun (congrFun key (Sum.inr i)) j
  rw [hcol] at this
  simpa [E1, Matrix.toBlocks₂₁, Matrix.toCols₁, Matrix.mul_apply, Fintype.sum_sum_type] using this
/- English proof (translation)
Establish `h21` using `_root_.PositivityTheory.SiegelWeilFormula.KWhit.parabolic_lowerLeft_block_zero d p t hp`. Use `set g := inFrame d.b p with hg`. Use `set A := g.toBlocks₁₁`. Use `set B := g.toBlocks₁₂`. Use `set D := g.toBlocks₂₂`.

Establish `hgb : g = Matrix.fromBlocks A B 0 D` using `by rw [← h21, Matrix.fromBlocks_toBlocks]`. Establish `hBm : IsUnit (incM F d.b.1)` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.det_one]⟩)`. Establish `hBi : IsUnit (incM F (d.b⁻¹).1)` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.det_one]⟩)`. Establish `hug : IsUnit g` using `(hBi.mul (Units.isUnit p.1)).mul hBm`. Establish `hdet : IsUnit (A.det * D.det)`.

Rewrite using `[← Matrix.det_fromBlocks_zero₂₁ A B D, ← hgb]`. Conclude with `(Matrix.isUnit_iff_isUnit_det g).1 hug`. Establish `hA : IsUnit A.det` using `isUnit_of_mul_isUnit_left hdet`. Establish `hD : IsUnit D.det` using `isUnit_of_mul_isUnit_right hdet`. Use `set Md : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := Matrix.fromBlocks A 0 0 D with hMd_def`.

Establish `hMd : IsUnit Md` using `(Matrix.isUnit_iff_isUnit_det _).2 (by rw [hMd_def, Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hD)`. Take `⟨C', hC'⟩` from `_root_.PositivityTheory.SiegelWeilFormula.KWhit.frame_form_k d`. Establish `hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J)` using `p.2`. Establish `hgf` using `form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hP`. Establish `hC'' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0` using `hC'`.

Rewrite `hgf` using `[hC'']`. Establish `hgf' : gᵀ * Matrix.fromBlocks 0 1 C' 0 * g.map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0` using `hgf`. Rewrite `hgf'` using `[hgb]`. Establish `hMdf` using `block_diag_form (cA σ).toRingHom A B D C' hgf'`. Rewrite `hMdf` using `[← hC'']`.

Establish `hM0mem` using `form_conj_out (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hMdf`. Establish `hM0u : IsUnit (incM F d.b.1 * Md * incM F (d.b⁻¹).1)` using `(hBm.mul hMd).mul hBi`. Set `u : GL (Fin d.n ⊕ Fin d.n) (AE F E)` to `hM0u.unit`. Establish `hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = incM F d.b.1 * Md * incM F (d.b⁻¹).1` using `IsUnit.unit_spec hM0u`. Establish `hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J))` using `by show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)`.

Rewrite using `[hu]`. Conclude with `hM0mem`. Set `m0 : d.G` to `⟨u, hmem⟩`. Establish `hm0 : inFrame d.b m0 = Md` using `by show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = Md`. Rewrite using `[hu]`.

Simplify using `only [← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]`. Establish `hAu` using `(Matrix.isUnit_iff_isUnit_det A).2 hA`. Establish `hDu` using `(Matrix.isUnit_iff_isUnit_det D).2 hD`. Use `⟨p * m0⁻¹, m0, B * D⁻¹, ?_, ⟨hAu.unit, hDu.unit, ?_⟩, (inv_mul_cancel_right p m0).symm⟩` and prove the remaining obligations.

Establish `e` using `_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k d (p * m0⁻¹) m0`. Rewrite `e` using `[inv_mul_cancel_right, hm0]`. Apply `(hMd.mul_left_inj).1` to reduce the goal to its premises. Rewrite using `[← e, ← hg, hgb, hMd_def, Matrix.fromBlocks_multiply]`. Simplify using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]`.

Rewrite using `[hm0, IsUnit.unit_spec, IsUnit.unit_spec]`.
-/
theorem par_decomp_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    ∃ (n0 m0 : d.G) (β₀ : Mx F E d.n d.n), inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1 ∧ _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d m0 ∧ p = n0 * m0 := by
  have h21 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.parabolic_lowerLeft_block_zero d p t hp
  set g := inFrame d.b p with hg
  set A := g.toBlocks₁₁
  set B := g.toBlocks₁₂
  set D := g.toBlocks₂₂
  have hgb : g = Matrix.fromBlocks A B 0 D := by rw [← h21, Matrix.fromBlocks_toBlocks]
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.det_one]⟩)
  have hug : IsUnit g := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hdet : IsUnit (A.det * D.det) := by
    rw [← Matrix.det_fromBlocks_zero₂₁ A B D, ← hgb]
    exact (Matrix.isUnit_iff_isUnit_det g).1 hug
  have hA : IsUnit A.det := isUnit_of_mul_isUnit_left hdet
  have hD : IsUnit D.det := isUnit_of_mul_isUnit_right hdet
  set Md : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := Matrix.fromBlocks A 0 0 D with hMd_def
  have hMd : IsUnit Md := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hMd_def, Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hD)
  obtain ⟨C', hC'⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.frame_form_k d
  have hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J) := p.2
  have hgf := form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hP
  have hC'' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
      Matrix.fromBlocks 0 1 C' 0 := hC'
  rw [hC''] at hgf
  have hgf' : gᵀ * Matrix.fromBlocks 0 1 C' 0 * g.map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0 := hgf
  rw [hgb] at hgf'
  have hMdf := block_diag_form (cA σ).toRingHom A B D C' hgf'
  rw [← hC''] at hMdf
  have hM0mem := form_conj_out (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hMdf
  have hM0u : IsUnit (incM F d.b.1 * Md * incM F (d.b⁻¹).1) := (hBm.mul hMd).mul hBi
  let u : GL (Fin d.n ⊕ Fin d.n) (AE F E) := hM0u.unit
  have hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      incM F d.b.1 * Md * incM F (d.b⁻¹).1 := IsUnit.unit_spec hM0u
  have hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
      (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)
    rw [hu]
    exact hM0mem
  let m0 : d.G := ⟨u, hmem⟩
  have hm0 : inFrame d.b m0 = Md := by
    show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = Md
    rw [hu]
    simp only [← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.one_mul]
    rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]
  have hAu := (Matrix.isUnit_iff_isUnit_det A).2 hA
  have hDu := (Matrix.isUnit_iff_isUnit_det D).2 hD
  refine ⟨p * m0⁻¹, m0, B * D⁻¹, ?_, ⟨hAu.unit, hDu.unit, ?_⟩, (inv_mul_cancel_right p m0).symm⟩
  · have e := _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k d (p * m0⁻¹) m0
    rw [inv_mul_cancel_right, hm0] at e
    apply (hMd.mul_left_inj).1
    rw [← e, ← hg, hgb, hMd_def, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]
  · rw [hm0, IsUnit.unit_spec, IsUnit.unit_spec]
/- English proof (translation)
Establish `hg : (mat g⁻¹)ᵀ * incM F d.A.J * (mat g⁻¹).map (cA σ) = incM F d.A.J` using `(g⁻¹).2`. Establish `hm : (mat g⁻¹ * X).map (cA σ) = (mat g⁻¹).map (cA σ) * X.map (cA σ)` using `Matrix.map_mul (f := (cA σ).toRingHom)`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_mul, hm]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = _ := by rw [hg]`.
-/
theorem gram_mat_inv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g : UA σ d.A.J) (X : Mx F E d.m d.n) :
    d.gram (mat g⁻¹ * X) (mat g⁻¹ * X) = d.gram X X := by
  have hg : (mat g⁻¹)ᵀ * incM F d.A.J * (mat g⁻¹).map (cA σ) = incM F d.A.J := (g⁻¹).2
  have hm : (mat g⁻¹ * X).map (cA σ) = (mat g⁻¹).map (cA σ) * X.map (cA σ) :=
    Matrix.map_mul (f := (cA σ).toRingHom)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_mul, hm]
  calc Xᵀ * (mat g⁻¹)ᵀ * incM F d.A.J * ((mat g⁻¹).map (cA σ) * X.map (cA σ))
      = Xᵀ * ((mat g⁻¹)ᵀ * incM F d.A.J * (mat g⁻¹).map (cA σ)) * X.map (cA σ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg]
/- English proof (translation)
Establish `h1 : d.tt (β₀ * ((-2 : ℤ) • T)) = (-2 : AF F) * d.tt (T * β₀)`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.mul_smul, Matrix.trace_smul, map_zsmul, Matrix.trace_mul_comm β₀ T]`. Rewrite using `[zsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1, ← mul_assoc, mul_neg, invOf_mul_self, neg_one_mul, neg_neg]`.
-/
theorem phase_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T β₀ : Mx F E d.n d.n) :
    -(⅟(2 : AF F) * d.tt (β₀ * ((-2 : ℤ) • T))) = d.tt (T * β₀) := by
  have h1 : d.tt (β₀ * ((-2 : ℤ) • T)) = (-2 : AF F) * d.tt (T * β₀) := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.mul_smul, Matrix.trace_smul, map_zsmul, Matrix.trace_mul_comm β₀ T]
    rw [zsmul_eq_mul]
    push_cast
    ring
  rw [h1, ← mul_assoc, mul_neg, invOf_mul_self, neg_one_mul, neg_neg]
/- English proof (translation)
Establish `hP` using `(hT.2.1 F E σ d Ψ hΨ).1 n0 β₀ hn`. Establish `hpt : ∀ (g : UA σ d.A.J) (X : Matrix (Fin d.m) (Fin d.n) E), d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1 → d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.T Ψ (mat g⁻¹ * incM F X)`. Introduce `g X hX`. Rewrite using `[hP, _root_.PositivityTheory.SiegelWeilFormula.KWhit.gram_mat_inv_k, hX, _root_.PositivityTheory.SiegelWeilFormula.KWhit.phase_k]`. Establish `hs : ∀ g : UA σ d.A.J, (∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1}, d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X.1)) = d.B.ψ (d.tt (T.1.1 * β₀)) * ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} …`.

Introduce `g`. Rewrite using `[← tsum_mul_left]`. Conclude with `tsum_congr fun X => hpt g X.1 X.2`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.orb]`. Repeatedly rewrite using `[hs]`.

Simplify using `only [MeasureTheory.average]`. Conclude with `integral_const_mul _ _`.
-/
theorem orb_n_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) (n0 : d.G) (β₀ : Mx F E d.n d.n)
    (hn : inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1) :
    d.orb T (d.om n0 Ψ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T Ψ := by
  have hP := (hT.2.1 F E σ d Ψ hΨ).1 n0 β₀ hn
  have hpt : ∀ (g : UA σ d.A.J) (X : Matrix (Fin d.m) (Fin d.n) E),
      d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1 →
      d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.T Ψ (mat g⁻¹ * incM F X) := by
    intro g X hX
    rw [hP, _root_.PositivityTheory.SiegelWeilFormula.KWhit.gram_mat_inv_k, hX, _root_.PositivityTheory.SiegelWeilFormula.KWhit.phase_k]
  have hs : ∀ g : UA σ d.A.J,
      (∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
        d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X.1)) = d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
        d.T Ψ (mat g⁻¹ * incM F X.1) := by
    intro g
    rw [← tsum_mul_left]
    exact tsum_congr fun X => hpt g X.1 X.2
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.orb]
  simp_rw [hs]
  simp only [MeasureTheory.average]
  exact integral_const_mul _ _
/- English proof (translation)
Use `hcd.2.1` as an intermediate fact. Establish `hβ₀ : β₀ ∈ nA σ d.Y d.b` using `AddSubgroup.subset_closure ⟨n0, hn⟩`. Set `b₀ : nA σ d.Y d.b` to `⟨β₀, hβ₀⟩`. Establish `hnb : ∀ β, nb β * n0 = nb (b₀ + β)`. Introduce `β`.

Apply `_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_injective_k d` to reduce the goal to its premises. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hcd.1 β, hn, hcd.1 (b₀ + β)]`. Simplify using `[Matrix.fromBlocks_multiply, add_comm, b₀]`. Establish `htt : ∀ β : nA σ d.Y d.b, d.tt (T.1.1 * (b₀ + β).1) = d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1)`. Introduce `β`.

Simplify using `[_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.mul_add, Matrix.trace_add, map_add, b₀]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `β`. Simplify using `only`.

Rewrite using `[← hnb β, htt β, ← AddChar.map_add_eq_mul, show -(d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1)) + d.tt (T.1.1 * β₀) = -d.tt (T.1.1 * β.1) by abel]`. Simplify using `only [mul_assoc]`. Use `_ = ∫ β, f (w * nb β * m0) * (d.B.ψ (-d.tt (T.1.1 * β.1)) * d.B.ψ (d.tt (T.1.1 * β₀))) ∂lam := integral_add_left_haar lam b₀ (fun β' : nA σ d.Y d.b => f (w * nb β' * m0) * (d.B.ψ (-d.tt (T.1.1 * β'.1)) * d.B.ψ (d.tt (T.1.1 * β₀))))`. Use `_ = _ := by`. Rewrite using `[← integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `β`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem int_n_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b)) (𝓖 : Set (nA σ d.Y d.b))
    (hcd : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (w n0 m0 : d.G) (β₀ : Mx F E d.n d.n)
    (hn : inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1) (f : d.G → ℂ) :
    ∫ β, f (w * nb β * (n0 * m0)) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam =
      d.B.ψ (d.tt (T.1.1 * β₀)) * ∫ β, f (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
  have := hcd.2.1
  have hβ₀ : β₀ ∈ nA σ d.Y d.b := AddSubgroup.subset_closure ⟨n0, hn⟩
  let b₀ : nA σ d.Y d.b := ⟨β₀, hβ₀⟩
  have hnb : ∀ β, nb β * n0 = nb (b₀ + β) := by
    intro β
    apply _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_injective_k d
    rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hcd.1 β, hn, hcd.1 (b₀ + β)]
    simp [Matrix.fromBlocks_multiply, add_comm, b₀]
  have htt : ∀ β : nA σ d.Y d.b, d.tt (T.1.1 * (b₀ + β).1) = d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1) := by
    intro β
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.mul_add, Matrix.trace_add, map_add, b₀]
  calc ∫ β, f (w * nb β * (n0 * m0)) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam
      = ∫ β, (fun β' : nA σ d.Y d.b => f (w * nb β' * m0) * (d.B.ψ (-d.tt (T.1.1 * β'.1)) *
          d.B.ψ (d.tt (T.1.1 * β₀)))) (b₀ + β) ∂lam := by
        congr 1
        funext β
        dsimp only
        rw [← hnb β, htt β, ← AddChar.map_add_eq_mul,
          show -(d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1)) + d.tt (T.1.1 * β₀) = -d.tt (T.1.1 * β.1) by abel]
        simp only [mul_assoc]
    _ = ∫ β, f (w * nb β * m0) * (d.B.ψ (-d.tt (T.1.1 * β.1)) * d.B.ψ (d.tt (T.1.1 * β₀))) ∂lam :=
        integral_add_left_haar lam b₀ (fun β' : nA σ d.Y d.b => f (w * nb β' * m0) *
          (d.B.ψ (-d.tt (T.1.1 * β'.1)) * d.B.ψ (d.tt (T.1.1 * β₀))))
    _ = _ := by
        rw [← integral_const_mul]
        congr 1
        funext β
        ring
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
