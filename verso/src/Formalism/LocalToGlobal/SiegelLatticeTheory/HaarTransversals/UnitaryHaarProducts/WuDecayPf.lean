import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.WuDecay

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.WuDecay
open scoped InnerProductSpace ENNReal NNReal
open Matrix

set_option linter.dupNamespace false

namespace Formalism.L2.SG.WuDecayPf

variable {D : D7} (X : HidaSetting D)

abbrev muS (u : D.what₂.Word) : Measure X.B.I.Ginf := ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)

abbrev mX : X.B.I.Ginf → ℂ := Formalism.L2.SG.ProjRows.mInf X.B.I X.B.σ X.B.w

abbrev coefV (v : InfinitePlace X.B.I.F) : Formalism.REAL.UJ (X.B.I.ε v) → ℂ :=
  fun g => ⟪X.B.w v, X.B.σ v (uMat g) (X.B.w v)⟫_ℂ

def WuDom (u : D.what₂.Word) : Prop :=
  ∃ (C : ℝ≥0∞) (x0 : X.B.I.Ginf), C ≠ ⊤ ∧
    ∀ x, ‖X.Wu u x‖ₑ ≤ C * ∫⁻ s, ‖mX X (x0⁻¹ * (s * x))‖ₑ ∂(muS X u)

def MuSOn (u : D.what₂.Word) : Prop := ∀ᵐ s ∂(muS X u), s ∈ X.SinfU u

def CoefWeighted : Prop :=
  ∀ v, ∫⁻ g, ‖coefV X v g‖ₑ * ENNReal.ofReal (opn (uMat g) ^ N1 X) ∂(Formalism.REAL.muG (X.B.I.ε v)) < ⊤

def MatrixCoefficientIntegrability : Prop := ∀ v, Integrable (coefV X v) (Formalism.REAL.muG (X.B.I.ε v))

/- English proof (translation)
Simplify using `[uMat]`.
-/
theorem uMat_mul' {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := by
  simp [uMat]

/- English proof (translation)
Unfold `opn`. Rewrite using `[map_mul]`. Conclude with `norm_mul_le _ _`.
-/
theorem opn_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : opn (A * B) ≤ opn A * opn B := by
  unfold opn; rw [map_mul]; exact norm_mul_le _ _

/- English proof (translation)
The claim follows from `norm_nonneg _`.
-/
theorem opn_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ opn A := norm_nonneg _

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem continuous_uMat {n : ℕ} {ε : Fin n → Bool} :
    Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
Unfold `opn`. Set `L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))` to `{ toFun := fun A => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A map_add' := fun A B => map_add _ A B map_smul' := fun c A => map_smul _ c A }`. Conclude with `continuous_norm.comp L.continuous_of_finiteDimensional`.
-/
theorem continuous_opn {n : ℕ} : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => opn A) := by
  unfold opn
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun A => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A
      map_add' := fun A B => map_add _ A B
      map_smul' := fun c A => map_smul _ c A }
  exact continuous_norm.comp L.continuous_of_finiteDimensional

/- English proof (translation)
Unfold `N1`. Check the signs of the components of the expression.
-/
theorem weight_exponent_nonneg : 0 ≤ N1 X := by
  unfold N1; positivity

/- English proof (translation)
The claim follows from `Finset.prod_nonneg fun _ _ => opn_nonneg _`.
-/
theorem normInf_nonneg (g : X.B.I.Ginf) : 0 ≤ normInf X g :=
  Finset.prod_nonneg fun _ _ => opn_nonneg _

/- English proof (translation)
Unfold `normInf`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_le_prod (fun v _ => opn_nonneg _) (fun v _ => ?_)` and prove the remaining obligations. Use `show opn (uMat (a v * b v)) ≤ _`. Rewrite using `[uMat_mul']`.

Conclude with `opn_mul_le _ _`.
-/
theorem normInf_mul_le (a b : X.B.I.Ginf) : normInf X (a * b) ≤ normInf X a * normInf X b := by
  unfold normInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => opn_nonneg _) (fun v _ => ?_)
  show opn (uMat (a v * b v)) ≤ _
  rw [uMat_mul']
  exact opn_mul_le _ _

/- English proof (translation)
Establish `hc` using `(X.ds v).2.2.1.2.2 (X.B.w v)`. Establish `h2 : Continuous fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g) (X.B.w v)` using `hc.comp_continuous continuous_uMat (fun g => g.2)`. Conclude with `continuous_const.inner h2`.
-/
theorem continuous_coefV (v : InfinitePlace X.B.I.F) : Continuous (coefV X v) := by
  have hc := (X.ds v).2.2.1.2.2 (X.B.w v)
  have h2 : Continuous fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g) (X.B.w v) :=
    hc.comp_continuous continuous_uMat (fun g => g.2)
  exact continuous_const.inner h2

def gW (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) : ℝ :=
  ‖coefV X v g‖ * opn (uMat g) ^ N1 X

/- English proof (translation)
The claim follows from `mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (opn_nonneg _) _)`.
-/
theorem gW_nonneg (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) : 0 ≤ gW X v g :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (opn_nonneg _) _)

/- English proof (translation)
Unfold `gW`. Conclude with `(continuous_coefV X v).norm.mul ((Real.continuous_rpow_const (weight_exponent_nonneg X)).comp (continuous_opn.comp continuous_uMat))`.
-/
theorem continuous_gW (v : InfinitePlace X.B.I.F) : Continuous (gW X v) := by
  unfold gW
  exact (continuous_coefV X v).norm.mul
    ((Real.continuous_rpow_const (weight_exponent_nonneg X)).comp (continuous_opn.comp continuous_uMat))

/- English proof (translation)
Use `⟨(continuous_gW X v).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Unfold `HasFiniteIntegral`. Use `lt_of_eq_of_lt (lintegral_congr fun g => ?_) (hC v)` and prove the remaining obligations. Rewrite using `[← ofReal_norm, Real.norm_of_nonneg (gW_nonneg X v g), gW, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]`.
-/
theorem integrable_gW (hC : CoefWeighted X) (v : InfinitePlace X.B.I.F) :
    Integrable (gW X v) (Formalism.REAL.muG (X.B.I.ε v)) := by
  refine ⟨(continuous_gW X v).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_eq_of_lt (lintegral_congr fun g => ?_) (hC v)
  rw [← ofReal_norm, Real.norm_of_nonneg (gW_nonneg X v g), gW,
    ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]

/- English proof (translation)
Rewrite using `[Real.enorm_eq_ofReal (Finset.prod_nonneg fun v _ => gW_nonneg X v (y v))]`. Rewrite using `[← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]`. Use `congr 1`. Unfold `gW normInf mX Formalism.L2.SG.ProjRows.mInf`. Rewrite using `[norm_prod, ← Real.finsetProd_rpow _ _ (fun v _ => opn_nonneg _), ← Finset.prod_mul_distrib]`.
-/
theorem F_eq (y : X.B.I.Ginf) :
    ‖mX X y‖ₑ * ENNReal.ofReal (normInf X y ^ N1 X) = ‖∏ v, gW X v (y v)‖ₑ := by
  rw [Real.enorm_eq_ofReal (Finset.prod_nonneg fun v _ => gW_nonneg X v (y v))]
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  unfold gW normInf mX Formalism.L2.SG.ProjRows.mInf
  rw [norm_prod, ← Real.finsetProd_rpow _ _ (fun v _ => opn_nonneg _), ← Finset.prod_mul_distrib]

/- English proof (translation)
Use `set F : X.B.I.Ginf → ℝ≥0∞ := fun y => ‖mX X y‖ₑ * ENNReal.ofReal (normInf X y ^ N1 X) with hF`. Use `set c : ℝ≥0∞ := ENNReal.ofReal (normInf X x0 ^ N1 X) with hc`. Establish `hle : ∀ y, ‖mX X (x0⁻¹ * y)‖ₑ * ENNReal.ofReal (normInf X y ^ N1 X) ≤ c * F (x0⁻¹ * y)`. Introduce `y`. Establish `h1 : normInf X y ≤ normInf X x0 * normInf X (x0⁻¹ * y)`.

Use `normInf_mul_le X x0 (x0⁻¹ * y)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis. Establish `h2 : normInf X y ^ N1 X ≤ normInf X x0 ^ N1 X * normInf X (x0⁻¹ * y) ^ N1 X`. Rewrite using `[← Real.mul_rpow (normInf_nonneg X _) (normInf_nonneg X _)]`. Conclude with `Real.rpow_le_rpow (normInf_nonneg X _) h1 (weight_exponent_nonneg X)`.

Establish `h3 : ENNReal.ofReal (normInf X y ^ N1 X) ≤ c * ENNReal.ofReal (normInf X (x0⁻¹ * y) ^ N1 X)`. Rewrite using `[hc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (normInf_nonneg X _) _)]`. Conclude with `ENNReal.ofReal_le_ofReal h2`. Combine the equalities or inequalities in the displayed calculation. Establish `hFin : ∫⁻ y, F y ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤`.

Establish `hI : Integrable (fun y : X.B.I.Ginf => ∏ v, gW X v (y v)) (Formalism.L2.SG.ProjRows.muInf X.B.I)` using `Integrable.fintype_prod_dep (fun v => integrable_gW X hC v)`. Use `hI.2` as an intermediate fact. Unfold `HasFiniteIntegral at this`. Use `lt_of_eq_of_lt (lintegral_congr fun y => ?_) this` and prove the remaining obligations. Conclude with `F_eq X y`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_mul_left_eq_self F x0⁻¹]`. Use `_ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFin`.
-/
theorem weighted_global (hC : CoefWeighted X) (x0 : X.B.I.Ginf) :
    ∫⁻ y, ‖mX X (x0⁻¹ * y)‖ₑ * ENNReal.ofReal (normInf X y ^ N1 X) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ := by
  set F : X.B.I.Ginf → ℝ≥0∞ := fun y => ‖mX X y‖ₑ * ENNReal.ofReal (normInf X y ^ N1 X) with hF
  set c : ℝ≥0∞ := ENNReal.ofReal (normInf X x0 ^ N1 X) with hc
  have hle : ∀ y, ‖mX X (x0⁻¹ * y)‖ₑ * ENNReal.ofReal (normInf X y ^ N1 X) ≤ c * F (x0⁻¹ * y) := by
    intro y
    have h1 : normInf X y ≤ normInf X x0 * normInf X (x0⁻¹ * y) := by
      have := normInf_mul_le X x0 (x0⁻¹ * y)
      rwa [mul_inv_cancel_left] at this
    have h2 : normInf X y ^ N1 X ≤ normInf X x0 ^ N1 X * normInf X (x0⁻¹ * y) ^ N1 X := by
      rw [← Real.mul_rpow (normInf_nonneg X _) (normInf_nonneg X _)]
      exact Real.rpow_le_rpow (normInf_nonneg X _) h1 (weight_exponent_nonneg X)
    have h3 : ENNReal.ofReal (normInf X y ^ N1 X) ≤
        c * ENNReal.ofReal (normInf X (x0⁻¹ * y) ^ N1 X) := by
      rw [hc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (normInf_nonneg X _) _)]
      exact ENNReal.ofReal_le_ofReal h2
    calc ‖mX X (x0⁻¹ * y)‖ₑ * ENNReal.ofReal (normInf X y ^ N1 X)
        ≤ ‖mX X (x0⁻¹ * y)‖ₑ * (c * ENNReal.ofReal (normInf X (x0⁻¹ * y) ^ N1 X)) := by gcongr
      _ = c * F (x0⁻¹ * y) := by rw [hF]; ring
  have hFin : ∫⁻ y, F y ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ := by
    have hI : Integrable (fun y : X.B.I.Ginf => ∏ v, gW X v (y v)) (Formalism.L2.SG.ProjRows.muInf X.B.I) :=
      Integrable.fintype_prod_dep (fun v => integrable_gW X hC v)
    have := hI.2
    unfold HasFiniteIntegral at this
    refine lt_of_eq_of_lt (lintegral_congr fun y => ?_) this
    exact F_eq X y
  calc ∫⁻ y, ‖mX X (x0⁻¹ * y)‖ₑ * ENNReal.ofReal (normInf X y ^ N1 X) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I)
      ≤ ∫⁻ y, c * F (x0⁻¹ * y) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := lintegral_mono hle
    _ = c * ∫⁻ y, F (x0⁻¹ * y) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = c * ∫⁻ y, F y ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
        rw [lintegral_mul_left_eq_self F x0⁻¹]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFin

/- English proof (translation)
Establish `hm : Integrable (mX X) (Formalism.L2.SG.ProjRows.muInf X.B.I)` using `Integrable.fintype_prod_dep (fun v => hC v)`. Establish `hs : Integrable (fun g => star (mX X g)) (Formalism.L2.SG.ProjRows.muInf X.B.I)` using `hm.mono (continuous_star.comp_aestronglyMeasurable hm.1) (ae_of_all _ fun g => by simp)`. Conclude with `hs.const_mul _`.
-/
theorem phInt_of (hC : MatrixCoefficientIntegrability X) : Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) := by
  have hm : Integrable (mX X) (Formalism.L2.SG.ProjRows.muInf X.B.I) :=
    Integrable.fintype_prod_dep (fun v => hC v)
  have hs : Integrable (fun g => star (mX X g)) (Formalism.L2.SG.ProjRows.muInf X.B.I) :=
    hm.mono (continuous_star.comp_aestronglyMeasurable hm.1) (ae_of_all _ fun g => by simp)
  exact hs.const_mul _

/- English proof (translation)
Rewrite using `[Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.sub_mulVec]`.
-/
theorem mulVec_fix {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (hx : B *ᵥ x = x) :
    (A * B - 1) *ᵥ x = (A - 1) *ᵥ x := by
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.sub_mulVec]

/- English proof (translation)
Introduce `v`. Establish `he : ∀ c, uMat (b v) *ᵥ rv X.B.I v (X.eR c) = rv X.B.I v (X.eR c)` using `fun c => hb v _ (Or.inl (Or.inl ⟨c, rfl⟩))`. Establish `hz : uMat (b v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)` using `hb v _ (Or.inr rfl)`. Take `⟨h1, h2⟩` from `(ha v).1`. Use `show InS _ _ (uMat (a v * b v))`.

Rewrite using `[uMat_mul']`. Use `⟨fun c => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mulVec_fix _ _ _ (he c)]`. Conclude with `h1 c`. Rewrite using `[mulVec_fix _ _ _ hz]`.

Conclude with `h2`.
-/
theorem mul_mem_sinfU (u : D.what₂.Word) (a b : X.B.I.Ginf) (ha : a ∈ X.NinfU u)
    (hb : b ∈ Hset X.B.I (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪
      Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)})) :
    a * b ∈ X.SinfU u := by
  intro v
  have he : ∀ c, uMat (b v) *ᵥ rv X.B.I v (X.eR c) = rv X.B.I v (X.eR c) :=
    fun c => hb v _ (Or.inl (Or.inl ⟨c, rfl⟩))
  have hz : uMat (b v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) := hb v _ (Or.inr rfl)
  obtain ⟨h1, h2⟩ := (ha v).1
  show InS _ _ (uMat (a v * b v))
  rw [uMat_mul']
  refine ⟨fun c => ?_, ?_⟩
  · rw [mulVec_fix _ _ _ (he c)]; exact h1 c
  · rw [mulVec_fix _ _ _ hz]; exact h2

/- English proof (translation)
Establish `hc : ∀ (x : Fin n → ℂ) (S : Submodule ℂ (Fin n → ℂ)), IsClosed {M : Matrix (Fin n) (Fin n) ℂ | (M - 1) *ᵥ x ∈ S}` using `fun x S => (Submodule.closed_of_finiteDimensional S).preimage ((continuous_id.sub continuous_const).matrix_mulVec continuous_const)`. Unfold `InS`. Rewrite using `[Set.ofPred_and, Set.ofPred_forall]`. Conclude with `(isClosed_iInter fun c => hc _ _).inter (hc _ _)`.
-/
theorem isClosed_inS {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    IsClosed {M : Matrix (Fin n) (Fin n) ℂ | InS e z M} := by
  have hc : ∀ (x : Fin n → ℂ) (S : Submodule ℂ (Fin n → ℂ)),
      IsClosed {M : Matrix (Fin n) (Fin n) ℂ | (M - 1) *ᵥ x ∈ S} := fun x S =>
    (Submodule.closed_of_finiteDimensional S).preimage
      ((continuous_id.sub continuous_const).matrix_mulVec continuous_const)
  unfold InS
  rw [Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun c => hc _ _).inter (hc _ _)

/- English proof (translation)
Establish `: X.SinfU u = ⋂ v, (fun s : X.B.I.Ginf => uMat (s v)) ⁻¹' {M | InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) M}`. Use extensionality with `s`. Simplify using `[HidaSetting.SinfU, Sinf]`. Rewrite using `[this]`. Conclude with `isClosed_iInter fun v => (isClosed_inS _ _).preimage (continuous_uMat.comp (continuous_apply v))`.
-/
theorem isClosed_sinfU (u : D.what₂.Word) : IsClosed (X.SinfU u) := by
  have : X.SinfU u = ⋂ v, (fun s : X.B.I.Ginf => uMat (s v)) ⁻¹'
      {M | InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) M} := by
    ext s; simp [HidaSetting.SinfU, Sinf]
  rw [this]
  exact isClosed_iInter fun v => (isClosed_inS _ _).preimage (continuous_uMat.comp (continuous_apply v))

/- English proof (translation)
Establish `: SigmaFinite (X.muN u)` using `(X.muN_haar u).1`. Establish `: SigmaFinite (X.muH u)` using `(X.muH_haar u).1`. Establish `hN0 : ∀ᵐ x ∂(X.muN u), x ∈ X.NinfU u` using `ae_iff.2 (X.muN_haar u).2.2.1`. Establish `hH0 : ∀ᵐ x ∂(X.muH u), x ∈ Hset X.B.I (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪ Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)})` using `ae_iff.2 (X.muH_haar u).2.2.1`. Establish `hN : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.1 ∈ X.NinfU u` using `Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst hN0`.

Establish `hH : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.2 ∈ Hset X.B.I (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪ Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)})` using `Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd hH0`. Unfold `MuSOn muS`. Use `(ae_map_iff measurable_mul.aemeasurable ?_).2 ?_` and prove the remaining obligations. Conclude with `(isClosed_sinfU X u).measurableSet`. Use `filter_upwards [hN, hH] with p h1 h2`.

Conclude with `mul_mem_sinfU X u _ _ h1 h2`.
-/
theorem muSOn (u : D.what₂.Word) : MuSOn X u := by
  have : SigmaFinite (X.muN u) := (X.muN_haar u).1
  have : SigmaFinite (X.muH u) := (X.muH_haar u).1
  have hN0 : ∀ᵐ x ∂(X.muN u), x ∈ X.NinfU u := ae_iff.2 (X.muN_haar u).2.2.1
  have hH0 : ∀ᵐ x ∂(X.muH u), x ∈ Hset X.B.I (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪
      Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) :=
    ae_iff.2 (X.muH_haar u).2.2.1
  have hN : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.1 ∈ X.NinfU u :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst hN0
  have hH : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.2 ∈ Hset X.B.I (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪
      Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd hH0
  unfold MuSOn muS
  refine (ae_map_iff measurable_mul.aemeasurable ?_).2 ?_
  · exact (isClosed_sinfU X u).measurableSet
  · filter_upwards [hN, hH] with p h1 h2
    exact mul_mem_sinfU X u _ _ h1 h2

/- English proof (translation)
Establish `hbb : b * b ≤ 1` using `by nlinarith`. Establish `h2 : b * (a * b * a) ≤ a * a`. Establish `: b * (a * b * a) = (b * b) * (a * a)` using `by ring`. Rewrite using `[this]`. Use polynomial arithmetic with `[mul_nonneg ha ha]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem real_key (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hb1 : b ≤ 1) (h : 1 ≤ b * (a * b * a)) : 1 ≤ a := by
  have hbb : b * b ≤ 1 := by nlinarith
  have h2 : b * (a * b * a) ≤ a * a := by
    have : b * (a * b * a) = (b * b) * (a * a) := by ring
    rw [this]; nlinarith [mul_nonneg ha ha]
  nlinarith

set_option maxHeartbeats 400000 in
/- English proof (translation)
Establish `hg : star (uMat g) * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε` using `g.2`. Establish `hid : Formalism.REAL.Jm ε * (star (uMat g) * Formalism.REAL.Jm ε * uMat g) = 1`. Rewrite using `[hg, Formalism.REAL.Jm_mul_self]`. Establish `hJ : star (Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε = 1`. Rewrite using `[Matrix.star_eq_conjTranspose, Formalism.REAL.Jm_conjTranspose, Formalism.REAL.Jm_mul_self]`.

Establish `h1` using `congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) hid`. Establish `h2` using `congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) hJ`. Rewrite `h1` using `[map_mul, map_mul, map_mul, map_star, map_one]`. Rewrite `h2` using `[map_mul, map_star, map_one]`. Establish `: Nonempty (Fin n)` using `⟨⟨0, hn⟩⟩`.

Establish `hS : ‖Matrix.toEuclideanCLM (𝕜` using `ℂ) (n := Fin n) (Formalism.REAL.Jm ε)‖ ≤ 1 := by`. Establish `h3` using `CStarRing.norm_star_mul_self (x := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε))`. Rewrite `h3` using `[h2, norm_one]`. Use polynomial arithmetic with `[norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε))]`. Establish `h5` using `congrArg norm h1`.

Rewrite `h5` using `[norm_one]`. Establish `h6` using `norm_mul_le (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε)) (star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g)) * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε) * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g))`. Establish `h7` using `norm_mul_le (star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g)) * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε)) (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g))`. Establish `h8` using `norm_mul_le (star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g))) (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε))`. Rewrite `h8` using `[norm_star]`.

Rewrite `h6` using `[h5]`. Establish `ha0` using `norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g))`. Establish `hb0` using `norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε))`. Unfold `opn`. Generalize the expression as in `‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g)‖ = a at *`.

Generalize the expression as in `‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε)‖ = b at *`. Generalize the expression as in `‖star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g)) * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε)‖ = c at *`. Generalize the expression as in `‖star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g)) * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε) * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g)‖ = d at *`. Conclude with `real_key a b ha0 hb0 hS (h6.trans (mul_le_mul_of_nonneg_left (h7.trans (mul_le_mul_of_nonneg_right h8 ha0)) hb0))`.
-/
theorem one_le_opn {n : ℕ} {ε : Fin n → Bool} (hn : 0 < n) (g : Formalism.REAL.UJ ε) : 1 ≤ opn (uMat g) := by
  have hg : star (uMat g) * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have hid : Formalism.REAL.Jm ε * (star (uMat g) * Formalism.REAL.Jm ε * uMat g) = 1 := by
    rw [hg, Formalism.REAL.Jm_mul_self]
  have hJ : star (Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε = 1 := by
    rw [Matrix.star_eq_conjTranspose, Formalism.REAL.Jm_conjTranspose, Formalism.REAL.Jm_mul_self]
  have h1 := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) hid
  have h2 := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) hJ
  rw [map_mul, map_mul, map_mul, map_star, map_one] at h1
  rw [map_mul, map_star, map_one] at h2
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hS : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε)‖ ≤ 1 := by
    have h3 := CStarRing.norm_star_mul_self (x := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε))
    rw [h2, norm_one] at h3
    nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε))]
  have h5 := congrArg norm h1
  rw [norm_one] at h5
  have h6 := norm_mul_le (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε))
    (star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g)) *
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε) * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g))
  have h7 := norm_mul_le (star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g)) *
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε)) (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g))
  have h8 := norm_mul_le (star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g)))
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε))
  rw [norm_star] at h8
  rw [h5] at h6
  have ha0 := norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g))
  have hb0 := norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε))
  unfold opn
  generalize ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g)‖ = a at *
  generalize ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε)‖ = b at *
  generalize ‖star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g)) *
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε)‖ = c at *
  generalize ‖star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g)) *
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (Formalism.REAL.Jm ε) * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (uMat g)‖ = d at *
  exact real_key a b ha0 hb0 hS
    (h6.trans (mul_le_mul_of_nonneg_left (h7.trans (mul_le_mul_of_nonneg_right h8 ha0)) hb0))

/- English proof (translation)
Break down `Nat.eq_zero_or_pos X.B.I.n with h | h` into its components or cases. Establish `h0 : N1 X = 0` using `by unfold N1; simp [h]`. Rewrite using `[h0, Real.rpow_zero]`. Conclude with `Real.one_le_rpow (one_le_opn h g) (weight_exponent_nonneg X)`.
-/
theorem one_le_weight (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) : 1 ≤ opn (uMat g) ^ N1 X := by
  rcases Nat.eq_zero_or_pos X.B.I.n with h | h
  · have h0 : N1 X = 0 := by unfold N1; simp [h]
    rw [h0, Real.rpow_zero]
  · exact Real.one_le_rpow (one_le_opn h g) (weight_exponent_nonneg X)

/- English proof (translation)
Introduce `v`. Use `⟨(continuous_coefV X v).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Use `lt_of_le_of_lt (lintegral_mono fun g => ?_) (hC v)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_one]`.

Conclude with `ENNReal.ofReal_le_ofReal (one_le_weight X v g)`.
-/
theorem coef_integrable_of_weighted (hC : CoefWeighted X) : MatrixCoefficientIntegrability X := by
  intro v
  refine ⟨(continuous_coefV X v).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) (hC v)
  calc ‖coefV X v g‖ₑ = ‖coefV X v g‖ₑ * 1 := (mul_one _).symm
    _ ≤ ‖coefV X v g‖ₑ * ENNReal.ofReal (opn (uMat g) ^ N1 X) := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (one_le_weight X v g)

/- English proof (translation)
The claim follows from `phInt_of X (coef_integrable_of_weighted X hC)`.
-/
theorem phInt_of_weighted (hC : CoefWeighted X) : Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) :=
  phInt_of X (coef_integrable_of_weighted X hC)

/- English proof (translation)
The claim follows from `Finset.prod_nonneg fun _ _ => norm_nonneg _`.
-/
theorem normInf_nonneg' (g : X.B.I.Ginf) : 0 ≤ normInf X g :=
  Finset.prod_nonneg fun _ _ => norm_nonneg _

/- English proof (translation)
The claim follows from `Real.iInf_nonneg fun _ => normInf_nonneg' X _`.
-/
theorem nuInf_nonneg (u : D.what₂.Word) (x : X.B.I.Ginf) : 0 ≤ nuInf X u x :=
  Real.iInf_nonneg fun _ => normInf_nonneg' X _

/- English proof (translation)
Unfold `nuInf`. Establish `hb : BddBelow (Set.range fun t : X.SinfU u => normInf X ((t : X.B.I.Ginf) * x))` using `⟨0, by rintro _ ⟨t, rfl⟩; exact normInf_nonneg' X _⟩`. Conclude with `ciInf_le hb (⟨s, hs⟩ : X.SinfU u)`.
-/
theorem nuInf_le (u : D.what₂.Word) (x s : X.B.I.Ginf) (hs : s ∈ X.SinfU u) :
    nuInf X u x ≤ normInf X (s * x) := by
  unfold nuInf
  have hb : BddBelow (Set.range fun t : X.SinfU u => normInf X ((t : X.B.I.Ginf) * x)) :=
    ⟨0, by rintro _ ⟨t, rfl⟩; exact normInf_nonneg' X _⟩
  exact ciInf_le hb (⟨s, hs⟩ : X.SinfU u)

/- English proof (translation)
Establish `hc` using `(X.ds v).2.2.1.2.2 (X.B.w v)`. Establish `hu : Continuous fun g : Formalism.REAL.UJ (X.B.I.ε v) => uMat g` using `Units.continuous_val.comp continuous_subtype_val`. Establish `h2 : Continuous fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g) (X.B.w v)` using `hc.comp_continuous hu fun g => g.2`. Conclude with `continuous_const.inner h2`.
-/
theorem coefV_continuous (v : InfinitePlace X.B.I.F) : Continuous (coefV X v) := by
  have hc := (X.ds v).2.2.1.2.2 (X.B.w v)
  have hu : Continuous fun g : Formalism.REAL.UJ (X.B.I.ε v) => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  have h2 : Continuous fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g) (X.B.w v) :=
    hc.comp_continuous hu fun g => g.2
  exact continuous_const.inner h2

/- English proof (translation)
Unfold `mX Formalism.L2.SG.ProjRows.mInf`. Conclude with `continuous_finsetProd _ fun v _ => (coefV_continuous X v).comp (continuous_apply v)`.
-/
theorem mX_continuous : Continuous (mX X) := by
  unfold mX Formalism.L2.SG.ProjRows.mInf
  exact continuous_finsetProd _ fun v _ => (coefV_continuous X v).comp (continuous_apply v)

/- English proof (translation)
Unfold `opn`. Establish `: Continuous fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.toEuclideanCLM (𝕜` using `ℂ) M := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional`. Conclude with `continuous_norm.comp this`.
-/
theorem opn_continuous {n : ℕ} : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => opn M := by
  unfold opn
  have : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) M :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact continuous_norm.comp this

/- English proof (translation)
Unfold `normInf`. Conclude with `continuous_finsetProd _ fun v _ => opn_continuous.comp ((Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v))`.
-/
theorem normInf_continuous : Continuous (normInf X) := by
  unfold normInf
  exact continuous_finsetProd _ fun v _ =>
    opn_continuous.comp ((Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v))

/- English proof (translation)
Take `⟨C, x0, hCt, hb⟩` from `hD`. Use `set F : X.B.I.Ginf → ℝ≥0∞ := fun y => ‖mX X (x0⁻¹ * y)‖ₑ * ENNReal.ofReal (normInf X y ^ N1 X) with hFdef`. Establish `hFm : Measurable F`. Establish `h1 : Measurable fun y : X.B.I.Ginf => ‖mX X (x0⁻¹ * y)‖ₑ` using `(continuous_enorm.comp ((mX_continuous X).comp (continuous_const_mul x0⁻¹))).measurable`. Establish `h2 : Measurable fun y : X.B.I.Ginf => ENNReal.ofReal (normInf X y ^ N1 X)` using `(ENNReal.continuous_ofReal.comp ((normInf_continuous X).rpow_const fun _ => Or.inr (weight_exponent_nonneg X))).measurable`.

Conclude with `h1.mul h2`. Establish `hpt : ∀ x, ‖X.Wu u x‖ₑ * ENNReal.ofReal (nuInf X u x ^ N1 X) ≤ C * ∫⁻ s, F (s * x) ∂(muS X u)`. Introduce `x`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]`.

Use `_ ≤ C * ∫⁻ s, F (s * x) ∂(muS X u) := by gcongr C * ?_`. Use `lintegral_mono_ae ?_` and prove the remaining obligations. Use `filter_upwards [hS] with s hs`. Simplify using `only [hFdef]`. Use `gcongr _ * ?_`.

Conclude with `ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (nuInf_nonneg X u x) (nuInf_le X u x s hs) (weight_exponent_nonneg X))`. Unfold `WuWeighted`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem wuWeighted_of (u : D.what₂.Word) (hD : WuDom X u) (hS : MuSOn X u) (hC : CoefWeighted X) :
    WuWeighted X u := by
  obtain ⟨C, x0, hCt, hb⟩ := hD
  set F : X.B.I.Ginf → ℝ≥0∞ := fun y => ‖mX X (x0⁻¹ * y)‖ₑ * ENNReal.ofReal (normInf X y ^ N1 X) with hFdef
  have hFm : Measurable F := by
    have h1 : Measurable fun y : X.B.I.Ginf => ‖mX X (x0⁻¹ * y)‖ₑ :=
      (continuous_enorm.comp ((mX_continuous X).comp (continuous_const_mul x0⁻¹))).measurable
    have h2 : Measurable fun y : X.B.I.Ginf => ENNReal.ofReal (normInf X y ^ N1 X) :=
      (ENNReal.continuous_ofReal.comp
        ((normInf_continuous X).rpow_const fun _ => Or.inr (weight_exponent_nonneg X))).measurable
    exact h1.mul h2
  have hpt : ∀ x, ‖X.Wu u x‖ₑ * ENNReal.ofReal (nuInf X u x ^ N1 X) ≤ C * ∫⁻ s, F (s * x) ∂(muS X u) := by
    intro x
    calc ‖X.Wu u x‖ₑ * ENNReal.ofReal (nuInf X u x ^ N1 X)
        ≤ (C * ∫⁻ s, ‖mX X (x0⁻¹ * (s * x))‖ₑ ∂(muS X u)) * ENNReal.ofReal (nuInf X u x ^ N1 X) :=
          by gcongr; exact hb x
      _ = C * ∫⁻ s, ‖mX X (x0⁻¹ * (s * x))‖ₑ * ENNReal.ofReal (nuInf X u x ^ N1 X) ∂(muS X u) := by
          rw [mul_assoc, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      _ ≤ C * ∫⁻ s, F (s * x) ∂(muS X u) := by
          gcongr C * ?_
          refine lintegral_mono_ae ?_
          filter_upwards [hS] with s hs
          simp only [hFdef]
          gcongr _ * ?_
          exact ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow (nuInf_nonneg X u x) (nuInf_le X u x s hs) (weight_exponent_nonneg X))
  unfold WuWeighted
  calc ∫⁻ x, ‖X.Wu u x‖ₑ * ENNReal.ofReal (nuInf X u x ^ N1 X) ∂(X.nuQ u)
      ≤ ∫⁻ x, C * ∫⁻ s, F (s * x) ∂(muS X u) ∂(X.nuQ u) := lintegral_mono hpt
    _ = C * ∫⁻ x, ∫⁻ s, F (s * x) ∂(muS X u) ∂(X.nuQ u) := lintegral_const_mul' _ _ hCt
    _ = C * ∫⁻ y, F y ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by rw [X.nuQ_weil u F hFm]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hCt) (weighted_global X hC x0)

/- English proof (translation)
The claim follows from `wuWeighted_of X u hD (muSOn X u) hC`.
-/
theorem wuWeighted_of' (u : D.what₂.Word) (hD : WuDom X u) (hC : CoefWeighted X) : WuWeighted X u :=
  wuWeighted_of X u hD (muSOn X u) hC

end Formalism.L2.SG.WuDecayPf
