import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneRestrictionPairThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairRestrictionGaussian

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedWForm

/- English proof (translation)
Establish `hf` using `d.form v u`. Rewrite `hf` using `[h]`. Use function extensionality and compare the values at `x`. Simplify using `only [Darboux.rho, schr, map_add, Prod.fst_add, Prod.snd_add]`. Rewrite using `[← mul_assoc, ← AddChar.map_add_eq_mul]`.

Use `congr 1`. Use `congr 1`. Establish `h2 : (2 : AF F) * ⅟(2 : AF F) = 1` using `mul_invOf_self 2`. Simplify using `only [add_dotProduct, dotProduct_add]`. Take the linear combination `(⅟(2 : AF F)) * hf - ((d.e u).1 ⬝ᵥ (d.e v).2) * h2`.

Use `congr 1`. Normalize the expressions using the abelian group laws.
-/
theorem rho_rho_of {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {Bf : W → W → AF F} {κ : Type} [Fintype κ] (d : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (u v : W) (h : Bf v u = 0)
    (φ : (κ → AF F) → ℂ) : d.rho ψ u (d.rho ψ v φ) = d.rho ψ (u + v) φ := by
  have hf := d.form v u
  rw [h] at hf
  funext x
  simp only [Darboux.rho, schr, map_add, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 1
  · congr 1
    have h2 : (2 : AF F) * ⅟(2 : AF F) = 1 := mul_invOf_self 2
    simp only [add_dotProduct, dotProduct_add]
    linear_combination (⅟(2 : AF F)) * hf - ((d.e u).1 ⬝ᵥ (d.e v).2) * h2
  · congr 1
    abel

section Tens

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/- English proof (translation)
Simplify using `[hTens, dbl, Fintype.sum_sum_type, Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_eq_add_neg]`.
-/
theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (a b a' b' : Matrix α β E) :
    hTens c JA (dbl JB) (Matrix.fromCols a b) (Matrix.fromCols a' b') = hTens c JA JB a a' - hTens c JA JB b b' := by
  simp [hTens, dbl, Fintype.sum_sum_type, Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_eq_add_neg]

/- English proof (translation)
Simplify using `[hTens]`.
-/
theorem hTens_zero_right (JA : Matrix α α E) (JB : Matrix β β E) (a : Matrix α β E) : hTens c JA JB a 0 = 0 := by
  simp [hTens]

end Tens

section Orth

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Simplify using `[cA, inclR]`.
-/
theorem cA_inclR (σ : E →ₐ[F] E) (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  simp [cA, inclR]

/- English proof (translation)
The claim follows from `funext fun i => (RingHom.map_mulVec _ A v i).symm`.
-/
theorem map_mulVec_incl {p q : Type} [Fintype q] (A : Matrix p q E) (v : q → E) :
    A.map (inclR (F := F) (AF F)) *ᵥ (fun i => inclR (F := F) (AF F) (v i)) = fun i => inclR (F := F) (AF F) ((A *ᵥ v) i) :=
  funext fun i => (RingHom.map_mulVec _ A v i).symm

/- English proof (translation)
Establish `hv : ιᵀ *ᵥ (J *ᵥ fun l => σ (x l)) = 0`. Use function extensionality and compare the values at `m`. Use `hx (Pi.single m 1)` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_single_one]`. Simplify `this` using `[form, Matrix.mulVec, dotProduct]`.

Establish `hw : (incM F ι)ᵀ *ᵥ (incM F J *ᵥ fun l => cA σ (incV F x l)) = 0`. Establish `e1 : (fun l => cA σ (incV F x l)) = fun l => inclR (F` using `F) (AF F) (σ (x l)) := funext fun l => cA_inclR σ _`. Simplify using `only [e1, incM]`. Rewrite using `[map_mulVec_incl, ← Matrix.transpose_map, map_mulVec_incl, hv]`. Use function extensionality and compare the values at `m`.

Simplify using the standard rewrite rules. Establish `key : ∀ i, ∑ j, (Z * (incM F ι)ᵀ) i j * ∑ l, incM F J j l * cA σ (incV F x l) = 0`. Introduce `i`. Use `congrFun (congrArg (Z *ᵥ ·) hw) i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec]`.

Simplify `this` using `[Matrix.mulVec, dotProduct]`. Simplify using `only [hTens]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.vecMulVec_apply, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = 0 := by simp [key]`.
-/
theorem hTens_orth (σ : E →ₐ[F] E) {n d d₁ : ℕ} (JX : Matrix (Fin n) (Fin n) (AE F E)) (J : Matrix (Fin d) (Fin d) E)
    (ι : Matrix (Fin d) (Fin d₁) E) (x : Fin d → E) (hx : ∀ u, form σ J (ι *ᵥ u) x = 0)
    (Z : Matrix (Fin n) (Fin d₁) (AE F E)) (y : Fin n → AE F E) :
    hTens (cA σ) JX (incM F J) (Z * (incM F ι)ᵀ) (Matrix.vecMulVec y (incV F x)) = 0 := by
  have hv : ιᵀ *ᵥ (J *ᵥ fun l => σ (x l)) = 0 := by
    funext m
    have := hx (Pi.single m 1)
    rw [Matrix.mulVec_single_one] at this
    simpa [form, Matrix.mulVec, dotProduct] using this
  have hw : (incM F ι)ᵀ *ᵥ (incM F J *ᵥ fun l => cA σ (incV F x l)) = 0 := by
    have e1 : (fun l => cA σ (incV F x l)) = fun l => inclR (F := F) (AF F) (σ (x l)) := funext fun l => cA_inclR σ _
    simp only [e1, incM]
    rw [map_mulVec_incl, ← Matrix.transpose_map, map_mulVec_incl, hv]
    funext m; simp
  have key : ∀ i, ∑ j, (Z * (incM F ι)ᵀ) i j * ∑ l, incM F J j l * cA σ (incV F x l) = 0 := by
    intro i
    have := congrFun (congrArg (Z *ᵥ ·) hw) i
    rw [Matrix.mulVec_mulVec] at this
    simpa [Matrix.mulVec, dotProduct] using this
  simp only [hTens]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_comm]
  calc _ = ∑ k, (JX i k * cA σ (y k)) * ∑ j, (Z * (incM F ι)ᵀ) i j * ∑ l, incM F J j l * cA σ (incV F x l) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        simp only [Matrix.vecMulVec_apply, map_mul]
        ring
    _ = 0 := by simp [key]

end Orth

section Diag

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

local instance measAfW : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
local instance borelAfW : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩

/- English proof (translation)
Simplify using `only [pureA, DiagForm.glue]`. Apply the tactic sequence `congr 2 <;> funext i <;> simp`.
-/
theorem pureA_glue (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (p : DiagForm.Vi F κ × DiagForm.Vf F κ) : pureA F f g (DiagForm.glue p) = f (DiagForm.eI F κ p.1) * g p.2 := by
  simp only [pureA, DiagForm.glue]
  congr 2 <;> funext i <;> simp

/- English proof (translation)
Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, g, hg, rfl⟩` from `hx`. Simplify using `only [pureA_glue]`. Conclude with `(f.continuous.comp ((DiagForm.eI F κ).continuous.comp continuous_fst)).mul (hg.1.continuous.comp continuous_snd)`.

Consider the case `zero => exact continuous_const`. Consider the case `add x y _ _ hx hy => exact hx.add hy`. Consider the case `smul c x _ hx => exact continuous_const.mul hx`.
-/
theorem continuous_glue_comp {a : (κ → AF F) → ℂ} (ha : a ∈ schA F κ) : Continuous fun p => a (DiagForm.glue p) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    simp only [pureA_glue]
    exact (f.continuous.comp ((DiagForm.eI F κ).continuous.comp continuous_fst)).mul (hg.1.continuous.comp continuous_snd)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact continuous_const.mul hx

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (DiagForm.eI F κ 0 i) = 0`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem glue_zero : DiagForm.glue (0 : DiagForm.Vi F κ × DiagForm.Vf F κ) = 0 := by
  funext i
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (DiagForm.eI F κ 0 i) = 0
    simp
  · rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨DiagForm.shiftOf x, by simpa [glue_zero] using DiagForm.glue_add_shiftOf (0 : DiagForm.Vi F κ × DiagForm.Vf F κ) x⟩`.
-/
theorem exists_glue_eq (x : κ → AF F) : ∃ p, DiagForm.glue p = x :=
  ⟨DiagForm.shiftOf x, by simpa [glue_zero] using DiagForm.glue_add_shiftOf (0 : DiagForm.Vi F κ × DiagForm.Vf F κ) x⟩

instance mu_openPos : (DiagForm.mu F κ).IsOpenPosMeasure := by unfold DiagForm.mu; infer_instance

/- English proof (translation)
Establish `hm` using `GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ a ha _ (GlobalTheory.SchAConj.star_mem_schA F κ a ha)`. Establish `hi` using `DiagForm.integrable_resD hm`. Establish `hr : DiagForm.resD F κ (boxFun a (fun x => star (a x))) = fun p => (((‖a (DiagForm.glue p)‖ ^ 2 : ℝ)) : ℂ)`. Use function extensionality and compare the values at `p`. Use `show a (DiagForm.glue p) * star (a (DiagForm.glue p)) = _`.

Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite using `[DiagForm.lDiag, LinearMap.comp_apply, DiagForm.Lext_apply _ hi, hr, integral_complex_ofReal]`. Rewrite `hi` using `[hr]`. Establish `hint : Integrable (fun p => ‖a (DiagForm.glue p)‖ ^ 2) (DiagForm.mu F κ)`. Conclude with `hi.re.congr (ae_of_all _ fun p => Complex.ofReal_re _)`.

Establish `hc : Continuous fun p => ‖a (DiagForm.glue p)‖ ^ 2` using `((continuous_glue_comp ha).norm).pow 2`. Use `Complex.ofReal_ne_zero.2 (ne_of_gt ?_)` and prove the remaining obligations. Rewrite using `[integral_pos_iff_support_of_nonneg (fun p => by positivity) hint]`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, a x ≠ 0 := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `h0 (funext hcon)`. Take `⟨p, rfl⟩` from `exists_glue_eq x`. Conclude with `hc.isOpen_support.measure_pos _ ⟨p, by simpa using hx⟩`.
-/
theorem lDiag_box_star_ne {a : (κ → AF F) → ℂ} (ha : a ∈ schA F κ) (h0 : a ≠ 0) :
    DiagForm.lDiag F κ (boxFun a (fun x => star (a x))) ≠ 0 := by
  have hm := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ a ha _ (GlobalTheory.SchAConj.star_mem_schA F κ a ha)
  have hi := DiagForm.integrable_resD hm
  have hr : DiagForm.resD F κ (boxFun a (fun x => star (a x))) =
      fun p => (((‖a (DiagForm.glue p)‖ ^ 2 : ℝ)) : ℂ) := by
    funext p
    show a (DiagForm.glue p) * star (a (DiagForm.glue p)) = _
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [DiagForm.lDiag, LinearMap.comp_apply, DiagForm.Lext_apply _ hi, hr, integral_complex_ofReal]
  rw [hr] at hi
  have hint : Integrable (fun p => ‖a (DiagForm.glue p)‖ ^ 2) (DiagForm.mu F κ) := by
    exact hi.re.congr (ae_of_all _ fun p => Complex.ofReal_re _)
  have hc : Continuous fun p => ‖a (DiagForm.glue p)‖ ^ 2 := ((continuous_glue_comp ha).norm).pow 2
  refine Complex.ofReal_ne_zero.2 (ne_of_gt ?_)
  rw [integral_pos_iff_support_of_nonneg (fun p => by positivity) hint]
  obtain ⟨x, hx⟩ : ∃ x, a x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact h0 (funext hcon)
  obtain ⟨p, rfl⟩ := exists_glue_eq x
  exact hc.isOpen_support.measure_pos _ ⟨p, by simpa using hx⟩

end Diag

end GlobalTheory.MixedWForm
