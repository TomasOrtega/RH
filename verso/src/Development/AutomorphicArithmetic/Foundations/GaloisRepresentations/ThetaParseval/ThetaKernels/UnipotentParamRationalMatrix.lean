import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ExistsRationalMatrixUnipotent
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FrameSignEqInvolutionScalar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDict
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitRelAlg

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Assume the negation of the conclusion as `hy0`. Set `w : InfinitePlace F` to `Classical.arbitrary _`. Set `τ : E →+* ℂ` to `(d.B.emb w).1`. Establish `hτ : ∀ x, τ (σ x) = star (τ x)` using `d.ok.good.cm.2.2.2 τ`. Set `z : Fin d.m → ℂ` to `fun i => τ (y i)`.

Establish `hz : z ≠ 0`. Introduce `h`. Apply `hy0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Apply `τ.injective` to reduce the goal to its premises.

Simplify `congrFun h i` using `[z]`. Establish `key : τ (HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y) = τ η * (z ⬝ᵥ (d.A.J.map τ) *ᵥ star z)`. Simplify using `only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Finset.mul_sum, Pi …`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [z]`. Rewrite using `[show ((σ : E →+* E) (y j)) = σ (y j) from rfl, hτ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[hy, map_zero]`. Establish `hQ : z ⬝ᵥ (d.A.J.map τ) *ᵥ star z ≠ 0`.

Break down `d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩` into its components or cases. Conclude with `rel_definite _ (hA.sig w) d.ok.aniso z hz`. Establish `h1` using `rel_definite _ (hA.sig w) d.ok.aniso z hz`. Introduce `h0`. Apply `h1` to reduce the goal to its premises.

Simplify using `only [Matrix.smul_mulVec, dotProduct_smul]`. Express the relevant statement in the definitionally equal form `Complex.I • (z ⬝ᵥ d.A.J.map τ *ᵥ star z) = 0`. Rewrite using `[h0, smul_zero]`. Establish `hτη : τ η ≠ 0` using `(map_ne_zero τ).mpr hη`. Conclude with `(mul_ne_zero hτη hQ) key.symm`.
-/
theorem rel_aniso_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (hη : η ≠ 0) (y : Fin d.m → E)
    (hy : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y = 0) : y = 0 := by
  by_contra hy0
  let w : InfinitePlace F := Classical.arbitrary _
  let τ : E →+* ℂ := (d.B.emb w).1
  have hτ : ∀ x, τ (σ x) = star (τ x) := d.ok.good.cm.2.2.2 τ
  let z : Fin d.m → ℂ := fun i => τ (y i)
  have hz : z ≠ 0 := by
    intro h
    apply hy0
    funext i
    apply τ.injective
    simpa [z] using congrFun h i
  have key : τ (HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y) = τ η * (z ⬝ᵥ (d.A.J.map τ) *ᵥ star z) := by
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.mulVec, dotProduct, map_sum, map_mul,
      Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [z]
    rw [show ((σ : E →+* E) (y j)) = σ (y j) from rfl, hτ]
    ring
  rw [hy, map_zero] at key
  have hQ : z ⬝ᵥ (d.A.J.map τ) *ᵥ star z ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact rel_definite _ (hA.sig w) d.ok.aniso z hz
    · have h1 := rel_definite _ (hA.sig w) d.ok.aniso z hz
      intro h0
      apply h1
      simp only [Matrix.smul_mulVec, dotProduct_smul]
      change Complex.I • (z ⬝ᵥ d.A.J.map τ *ᵥ star z) = 0
      rw [h0, smul_zero]
  have hτη : τ η ≠ 0 := (map_ne_zero τ).mpr hη
  exact (mul_ne_zero hτη hQ) key.symm
/- English proof (translation)
Take `⟨T, hT⟩` from `T`. Proceed by induction on `hT using AddSubgroup.closure_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => exact ⟨0, by ext i j; simp [incM]⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨X, hX⟩` from `hx`. Take `⟨Y, hY⟩` from `hy`. Use `⟨X + Y, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x.1 + y.1 = _`. Rewrite using `[hX, hY]`.

Use extensionality with `i j`. Simplify using `[incM]`. Consider the case `neg x _ hx`. Take `⟨X, hX⟩` from `hx`. Use `⟨-X, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `-x.1 = _`. Rewrite using `[hX]`. Use extensionality with `i j`. Simplify using `[incM]`.
-/
theorem unipotentParam_rational_matrix (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) : ∃ T₀ : Matrix (Fin d.n) (Fin d.n) E, T.1.1 = incM F T₀ := by
  obtain ⟨T, hT⟩ := T
  induction hT using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, by ext i j; simp [incM]⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    refine ⟨X + Y, ?_⟩
    change x.1 + y.1 = _
    rw [hX, hY]
    ext i j
    simp [incM]
  | neg x _ hx =>
    obtain ⟨X, hX⟩ := hx
    refine ⟨-X, ?_⟩
    change -x.1 = _
    rw [hX]
    ext i j
    simp [incM]
def relH_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  -(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹ • β.1ᵀ)
/- English proof (translation)
Introduce `a b`. Establish `hn` using `congrFun (congrFun (_root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_nA_cond_k d ε hε β) a) b`. Simplify using `only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply] at hn`. Establish `he2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1`. Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]`.

Simplify using the standard rewrite rules. Establish `hinv : σ η⁻¹ = -(((ε : ℤ) : E) * η⁻¹)`. Rewrite using `[map_inv₀, hση, inv_neg, mul_inv, inv_eq_of_mul_eq_one_right he2]`. Establish `hc : ∀ x : E, cA σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F` using `F) (AF F) x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (σ x) := by`. Introduce `x`.

Simplify using `[cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]`. Rewrite using `[map_neg, map_mul, rel_sigR_eq_cA, rel_sigR_eq_cA, hc, hinv, map_neg, map_mul, map_intCast]`. Take the linear combination `(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹) * hn`.
-/
theorem relH_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (η : E) (hη : η ≠ 0)
    (hση : σ η = -(((ε : ℤ) : E) * η)) (β : nA σ d.Y d.b) :
    _root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k d η β ∈ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n := by
  intro a b
  have hn := congrFun (congrFun (_root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_nA_cond_k d ε hε β) a) b
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Matrix.zero_apply] at hn
  have he2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have hinv : σ η⁻¹ = -(((ε : ℤ) : E) * η⁻¹) := by
    rw [map_inv₀, hση, inv_neg, mul_inv, inv_eq_of_mul_eq_one_right he2]
  have hc : ∀ x : E, cA σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (σ x) := by
    intro x
    simp [cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
  rw [map_neg, map_mul, rel_sigR_eq_cA, rel_sigR_eq_cA, hc, hinv, map_neg, map_mul, map_intCast]
  linear_combination (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹) * hn
/- English proof (translation)
Establish `h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F` using `F) (E := E) (AF F) η * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) η⁻¹ = 1 := by`. Rewrite using `[← map_mul, mul_inv_cancel₀ hη, map_one]`. Use extensionality with `i j`. Simplify using `[_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k, incM, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, ← mul_assoc, h1]`. Rewrite using `[mul_comm (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹), h1, one_mul]`.
-/
theorem relH_eq_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (hη : η ≠ 0) (β : nA σ d.Y d.b) :
    β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * (_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k d η β)ᵀ) := by
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) η⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hη, map_one]
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k, incM, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, ← mul_assoc, h1]
  rw [mul_comm (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹), h1, one_mul]
/- English proof (translation)
Establish `hn` using `_root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_nA_cond_k d ε hε T.1`. Rewrite `hn` using `[h0, rel_cA_incM]`. Establish `hn' : incM F (T₀ᵀ + ((ε : ℤ) : E) • T₀.map σ) = incM F 0`. Establish `e0 : incM F (0 : Matrix (Fin d.n) (Fin d.n) E) = 0`. Use extensionality with `i j`.

Simplify using `[incM]`. Rewrite using `[e0, ← hn]`. Use extensionality with `i j`. Simplify using `[incM]`. Establish `hz` using `rel_incM_injective hn'`.

Use `⟨fun a b => ?_, ?_⟩` and prove the remaining obligations. Establish `he` using `congrFun (congrFun hz a) b`. Simplify using `only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply] at he`. Simplify using `only [Td, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[map_mul, map_mul, map_neg, map_ofNat, hση]`.

Take the linear combination `(2 * η) * he`. Establish `hdet : T₀.det ≠ 0`. Introduce `h`. Apply `hT` to reduce the goal to its premises. Use `show (T.1.1).det = 0`.

Rewrite using `[h0, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]`. Simplify using `only [Td, Matrix.det_transpose, Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hη)) hdet`.
-/
theorem rel_Td_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (η : E) (hη : η ≠ 0)
    (hση : σ η = -(((ε : ℤ) : E) * η)) (T : nF σ d.Y d.b) (hT : IsND T) (T₀ : Matrix (Fin d.n) (Fin d.n) E)
    (h0 : T.1.1 = incM F T₀) : (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧ (Td η T₀).det ≠ 0 := by
  have hn := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_nA_cond_k d ε hε T.1
  rw [h0, rel_cA_incM] at hn
  have hn' : incM F (T₀ᵀ + ((ε : ℤ) : E) • T₀.map σ) = incM F 0 := by
    have e0 : incM F (0 : Matrix (Fin d.n) (Fin d.n) E) = 0 := by
      ext i j
      simp [incM]
    rw [e0, ← hn]
    ext i j
    simp [incM]
  have hz := rel_incM_injective hn'
  refine ⟨fun a b => ?_, ?_⟩
  · have he := congrFun (congrFun hz a) b
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Matrix.zero_apply] at he
    simp only [Td, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    rw [map_mul, map_mul, map_neg, map_ofNat, hση]
    linear_combination (2 * η) * he
  · have hdet : T₀.det ≠ 0 := by
      intro h
      apply hT
      show (T.1.1).det = 0
      rw [h0, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
    simp only [Td, Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hη)) hdet
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d`. Take `⟨⟨ε, hε⟩, -⟩` from `d.ok.frame`. Take `⟨η, hη, hση, hherm⟩` from `_root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_eta_k d ε hε`. Use `⟨η, fun β => ⟨_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k d η β, _root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_mem_k d ε hε η hη hση β⟩, hη, hherm, fun β => _root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_eq_k d η hη β, fun y hy => _root_.PositivityTheory.S …` and prove the remaining obligations. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]`.

Conclude with `hherm j i`. Introduce `h0`. Take `⟨y, hy0, hy⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Apply `hy0` to reduce the goal to its premises. Apply `_root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_aniso_k d η hη y` to reduce the goal to its premises.

Establish `h2 : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y = ∑ i, σ (y i) * (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η *ᵥ y) i`. Simplify using `only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Both sides reduce to the same expression. Rewrite using `[h2, hy]`. Simplify using the standard rewrite rules.

Take `⟨T₀, h0⟩` from `_root_.PositivityTheory.SiegelWeilFormula.KWhit.unipotentParam_rational_matrix d T`. Conclude with `⟨T₀, h0, _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_Td_k d ε hε η hη hση T hT T₀ h0⟩`.
-/
theorem relAlg_pf_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.RelAlg_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨η, hη, hση, hherm⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_eta_k d ε hε
  refine ⟨η, fun β => ⟨_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k d η β, _root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_mem_k d ε hε η hη hση β⟩, hη, hherm, fun β => _root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_eq_k d η hη β,
    fun y hy => _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_aniso_k d η hη y hy, d.ok.good.cm, ⟨fun i j => ?_, ?_⟩, fun T hT => ?_⟩
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    exact hherm j i
  · intro h0
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hy0
    apply _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_aniso_k d η hη y
    have h2 : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y = ∑ i, σ (y i) * (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η *ᵥ y) i := by
      simp only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      rfl
    rw [h2, hy]
    simp
  · obtain ⟨T₀, h0⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.unipotentParam_rational_matrix d T
    exact ⟨T₀, h0, _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_Td_k d ε hε η hη hση T hT T₀ h0⟩
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
