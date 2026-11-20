import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.HomCommTrivial
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ElementarySubgroupInvariance

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent
open GroundTheory.Automorphic.FourierWhittaker

noncomputable section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.VanishingCoefficients

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem vn (q : A E) : (nU q).val = !![1, q; 0, 1] := rfl

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]`.
-/
private theorem n_add (x y : A E) : gl (nU (x + y)) = gl (nU x) * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [vn]`.
-/
private theorem n_zero : gl (nU (0 : A E)) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn]

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine continuous_matrix fun i j => ?_ fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop`. Establish `e : ∀ q : A E, (gl (nU q))⁻¹ = gl (nU (-q))` using `fun q => inv_eq_of_mul_eq_one_right (by rw [← n_add, add_neg_cancel, n_zero])`. Simplify using `only [e]`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop`.
-/
private theorem cont_n : Continuous fun q : A E => gl (nU q) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop
  · have e : ∀ q : A E, (gl (nU q))⁻¹ = gl (nU (-q)) := fun q =>
      inv_eq_of_mul_eq_one_right (by rw [← n_add, add_neg_cancel, n_zero])
    simp only [e]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop

/- English proof (translation)
Use `⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `algebraMap E (A E) (!![1, k; 0, 1] i j) = _`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [vn]`.
-/
private theorem rat_n (k : E) : ∃ γ : GL (Fin 2) E, ratGL E 2 γ = gl (nU (rt k)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap E (A E) (!![1, k; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [vn]

/- English proof (translation)
Use `⟨Matrix.SpecialLinearGroup.toGL ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `algebraMap E (A E) (!![0, 1; -1, 0] i j) = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (A E)) i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
private theorem rat_w : ∃ γ : GL (Fin 2) E, ratGL E 2 γ = gl (wW E) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap E (A E) (!![0, 1; -1, 0] i j) = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (A E)) i j
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Simplify using `[ψ, AddChar.map_add_eq_mul]`.
-/
private theorem ψ_add (x y : A ℚ) : ψ (x + y) = ψ x * ψ y := by simp [ψ, AddChar.map_add_eq_mul]

/- English proof (translation)
Simplify using `[ψ, adelicChar_algebraMap]`.
-/
private theorem ψ_rt (k : ℚ) : ψ (rt k) = 1 := by simp [ψ, adelicChar_algebraMap]

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [vn, aE, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
private theorem n_aE (t : (A E)ˣ) (y : A E) : gl (nU ((t : A E) * y)) * aE t = aE t * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, aE, Matrix.mul_apply, Fin.sum_univ_two]

private def Fh (D : Dat ℚ E) (Φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) (x : Fin 2 → A ℚ) : ℂ :=
  Φ (gl (nU (D.mkE (x 0) (x 1))) * h)

/- English proof (translation)
The claim follows from `hΦ.comp ((cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))).mul continuous_const)`.
-/
private theorem cont_Fh (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hΦ : Continuous Φ) (h : GL (Fin 2) (A E)) :
    Continuous (Fh D Φ h) :=
  hΦ.comp ((cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))).mul continuous_const)

/- English proof (translation)
Introduce `l hl x`. Take `⟨η, rfl⟩` from `mem_vecLattice.1 hl`. Take `⟨γ, hγ⟩` from `rat_n (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ)`. Simplify using `only [Fh, Pi.add_apply]`. Rewrite using `[D.mkE_add, n_add]`.

Express the relevant statement in the definitionally equal form `Φ (gl (nU (D.mkE (rt (η 0)) (rt (η 1)))) * gl (nU (D.mkE (x 0) (x 1))) * h) = _`. Rewrite using `[D.mkE_rt, ← hγ, mul_assoc, hL]`.
-/
private theorem per_Fh (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (h : GL (Fin 2) (A E)) : ∀ l ∈ vecLattice ℚ (Fin 2), ∀ x, Fh D Φ h (l + x) = Fh D Φ h x := by
  intro l hl x
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hl
  obtain ⟨γ, hγ⟩ := rat_n (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ)
  simp only [Fh, Pi.add_apply]
  rw [D.mkE_add, n_add]
  change Φ (gl (nU (D.mkE (rt (η 0)) (rt (η 1)))) * gl (nU (D.mkE (x 0) (x 1))) * h) = _
  rw [D.mkE_rt, ← hγ, mul_assoc, hL]

/- English proof (translation)
Introduce `h0`. Establish `h1 : algebraMap ℚ E a - algebraMap ℚ E b * D.θ = 0`. Establish `e` using `congrArg D.σ h0`. Simplify `e` using `[D.conj, sub_eq_add_neg]`. Establish `ha : algebraMap ℚ E a = 0` using `by linear_combination (h0 + h1) / 2`.

Establish `hb : algebraMap ℚ E b * D.θ = 0` using `by linear_combination (h0 - h1) / 2`. Establish `inj` using `(algebraMap ℚ E).injective`. Break down `h with h | h` into its components or cases. Conclude with `h (inj (by rw [ha, map_zero]))`. Use `h (inj ?_)` and prove the remaining obligations.

Rewrite using `[map_zero]`. Conclude with `(mul_eq_zero.1 hb).resolve_right D.θ_ne_zero`.
-/
private theorem lin_ne (D : Dat ℚ E) {a b : ℚ} (h : a ≠ 0 ∨ b ≠ 0) : algebraMap ℚ E a + algebraMap ℚ E b * D.θ ≠ 0 := by
  intro h0
  have h1 : algebraMap ℚ E a - algebraMap ℚ E b * D.θ = 0 := by
    have e := congrArg D.σ h0
    simpa [D.conj, sub_eq_add_neg] using e
  have ha : algebraMap ℚ E a = 0 := by linear_combination (h0 + h1) / 2
  have hb : algebraMap ℚ E b * D.θ = 0 := by linear_combination (h0 - h1) / 2
  have inj := (algebraMap ℚ E).injective
  rcases h with h | h
  · exact h (inj (by rw [ha, map_zero]))
  · refine h (inj ?_)
    rw [map_zero]
    exact (mul_eq_zero.1 hb).resolve_right D.θ_ne_zero

/- English proof (translation)
Introduce `h0`. Establish `e : (algebraMap ℚ E a + algebraMap ℚ E b * D.θ) * (algebraMap ℚ E a + algebraMap ℚ E (-b) * D.θ) = algebraMap ℚ E (a * a - D.δ * b * b)`. Establish `hs` using `D.sq`. Simplify using `only [map_sub, map_mul, map_neg]`. Take the linear combination `(-(algebraMap ℚ E b) ^ 2) * hs`.

Rewrite `e` using `[h0, map_zero]`. Conclude with `mul_ne_zero (lin_ne D h) (lin_ne D (a := a) (b := -b) (by simpa using h)) e`.
-/
private theorem norm_ne (D : Dat ℚ E) {a b : ℚ} (h : a ≠ 0 ∨ b ≠ 0) : a * a - D.δ * b * b ≠ 0 := by
  intro h0
  have e : (algebraMap ℚ E a + algebraMap ℚ E b * D.θ) * (algebraMap ℚ E a + algebraMap ℚ E (-b) * D.θ) =
      algebraMap ℚ E (a * a - D.δ * b * b) := by
    have hs := D.sq
    simp only [map_sub, map_mul, map_neg]
    linear_combination (-(algebraMap ℚ E b) ^ 2) * hs
  rw [h0, map_zero] at e
  exact mul_ne_zero (lin_ne D h) (lin_ne D (a := a) (b := -b) (by simpa using h)) e

/- English proof (translation)
Rewrite using `[matVec_apply, Fin.sum_univ_two]`. Both sides reduce to the same expression.
-/
private theorem mat0 (a b d : ℚ) (x : Fin 2 → A ℚ) :
    matVec !![a, d; b, a] x 0 = UpperTheory.ConvolutionTheory.R2.rt a * x 0 + UpperTheory.ConvolutionTheory.R2.rt d * x 1 := by
  rw [matVec_apply, Fin.sum_univ_two]; rfl

/- English proof (translation)
Rewrite using `[matVec_apply, Fin.sum_univ_two]`. Both sides reduce to the same expression.
-/
private theorem mat1 (a b d : ℚ) (x : Fin 2 → A ℚ) :
    matVec !![a, d; b, a] x 1 = UpperTheory.ConvolutionTheory.R2.rt b * x 0 + UpperTheory.ConvolutionTheory.R2.rt a * x 1 := by
  rw [matVec_apply, Fin.sum_univ_two]; rfl

private def Gh (D : Dat ℚ E) (Φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) (u : Fin 2 → A ℚ) : ℂ :=
  Fh D Φ h u * ψ (2 * u 0)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem int_Gh (D : Dat ℚ E) (Φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) :
    ∫ x in vecDomain ℚ (Fin 2), Gh D Φ h x ∂vecMeasure ℚ (Fin 2) = WE D Φ h := rfl

/- English proof (translation)
Introduce `l hl x`. Establish `e1` using `per_Fh D hL h l hl x`. Take `⟨η, rfl⟩` from `mem_vecLattice.1 hl`. Establish `e2 : (2 : A ℚ) * ((fun i => algebraMap ℚ (A ℚ) (η i)) + x) 0 = UpperTheory.ConvolutionTheory.R2.rt (2 * η 0) + 2 * x 0`. Simplify using `only [UpperTheory.ConvolutionTheory.R2.rt, map_mul, map_ofNat, mul_add, Pi.add_apply]`.

Simplify using `only [Gh]`. Rewrite using `[e1, e2, ψ_add, ψ_rt, one_mul]`.
-/
private theorem per_Gh (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (h : GL (Fin 2) (A E)) : ∀ l ∈ vecLattice ℚ (Fin 2), ∀ x, Gh D Φ h (l + x) = Gh D Φ h x := by
  intro l hl x
  have e1 := per_Fh D hL h l hl x
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hl
  have e2 : (2 : A ℚ) * ((fun i => algebraMap ℚ (A ℚ) (η i)) + x) 0 = UpperTheory.ConvolutionTheory.R2.rt (2 * η 0) + 2 * x 0 := by
    simp only [UpperTheory.ConvolutionTheory.R2.rt, map_mul, map_ofNat, mul_add, Pi.add_apply]
  simp only [Gh]
  rw [e1, e2, ψ_add, ψ_rt, one_mul]

/- English proof (translation)
Take `⟨γ, hγ⟩` from `hγ`. Establish `e : UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) = UpperTheory.ConvolutionTheory.R2.rt D.δ * UpperTheory.ConvolutionTheory.R2.rt b` using `map_mul _ _ _`. Establish `k1 : D.mkE (matVec !![a, D.δ * b; b, a] x 0) (matVec !![a, D.δ * b; b, a] x 1) = (t : A E) * D.mkE (x 0) (x 1)`. Rewrite using `[ht, D.mkE_mul, mat0, mat1, e]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Gh, Fh]`. Rewrite using `[k1, mat0, ← mul_assoc, n_aE, ← hγ, mul_assoc, hL]`.
-/
private theorem pt_id (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (h : GL (Fin 2) (A E)) (a b : ℚ) (t : (A E)ˣ) (ht : (t : A E) = D.mkE (UpperTheory.ConvolutionTheory.R2.rt a) (UpperTheory.ConvolutionTheory.R2.rt b))
    (hγ : ∃ γ, ratGL E 2 γ = aE t) (x : Fin 2 → A ℚ) :
    Gh D Φ (aE t * h) (matVec !![a, D.δ * b; b, a] x) = Fh D Φ h x * ψ (2 * (UpperTheory.ConvolutionTheory.R2.rt a * x 0 + UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) * x 1)) := by
  obtain ⟨γ, hγ⟩ := hγ
  have e : UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) = UpperTheory.ConvolutionTheory.R2.rt D.δ * UpperTheory.ConvolutionTheory.R2.rt b := map_mul _ _ _
  have k1 : D.mkE (matVec !![a, D.δ * b; b, a] x 0) (matVec !![a, D.δ * b; b, a] x 1) =
      (t : A E) * D.mkE (x 0) (x 1) := by
    rw [ht, D.mkE_mul, mat0, mat1, e]
    congr 1
    · ring
    · ring
  simp only [Gh, Fh]
  rw [k1, mat0, ← mul_assoc, n_aE, ← hγ, mul_assoc, hL]

/- English proof (translation)
Establish `hδ` using `D.δ_ne_zero`. Take `⟨a, ha⟩ : ∃ a : ℚ, 2 * a = -ξ 0` from `⟨-ξ 0 / 2, by ring⟩`. Take `⟨b, hb⟩ : ∃ b : ℚ, 2 * (D.δ * b) = -ξ 1` from `⟨-ξ 1 / (2 * D.δ), by field_simp⟩`. Establish `hab : a ≠ 0 ∨ b ≠ 0`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Take `⟨h1, h2⟩` from `hc`. Use `hξ (funext fun i => ?_)` and prove the remaining obligations. Use `fin_cases i`. Simplify `ha.symm` using `[h1]`.

Simplify `hb.symm` using `[h2]`. Take `⟨M, hM⟩ : ∃ M : GL (Fin 2) ℚ, (M : Matrix (Fin 2) (Fin 2) ℚ) = !![a, D.δ * b; b, a]` from `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, D.δ * b; b, a] (by rw [Matrix.det_fin_two_of]; exact norm_ne D hab), rfl⟩`. Take `⟨t, ht, hγ⟩ : ∃ t : (A E)ˣ, (t : A E) = D.mkE (UpperTheory.ConvolutionTheory.R2.rt a) (UpperTheory.ConvolutionTheory.R2.rt b) ∧ ∃ γ, ratGL E 2 γ = aE t` from `⟨IdeleGroup.diagonal E (Units.mk0 _ (lin_ne D hab)), (D.mkE_rt a b).symm, exists_ratGL_aE _⟩`. Establish `h1` using `setIntegral_comp_matVec M (per_Gh D hL (aE t * h))`. Rewrite `h1` using `[int_Gh, hW, hM]`.

Rewrite using `[vecCoeff, ← h1]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Establish `k2 : (2 : A ℚ) * (UpperTheory.ConvolutionTheory.R2.rt a * x 0 + UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) * x 1) = -pair ξ x`. Establish `e2 : (2 : A ℚ) = UpperTheory.ConvolutionTheory.R2.rt (2 : ℚ)` using `(map_ofNat _ 2).symm`. Establish `e0 : (2 : A ℚ) * UpperTheory.ConvolutionTheory.R2.rt a = -UpperTheory.ConvolutionTheory.R2.rt (ξ 0)`.

Rewrite using `[← map_neg, ← ha, e2]`. Conclude with `(map_mul _ _ _).symm`. Establish `e1 : (2 : A ℚ) * UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) = -UpperTheory.ConvolutionTheory.R2.rt (ξ 1)`. Rewrite using `[← map_neg, ← hb, e2]`. Conclude with `(map_mul _ _ _).symm`.

Rewrite using `[pair, Fin.sum_univ_two]`. Take the linear combination `(x 0) * e0 + (x 1) * e1`. Use `beta_reduce`. Rewrite using `[pt_id D hL h a b t ht hγ x, k2]`. Both sides reduce to the same expression.
-/
private theorem coef_zero (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (hW : ∀ h, WE D Φ h = 0) (h : GL (Fin 2) (A E)) (ξ : Fin 2 → ℚ) (hξ : ξ ≠ 0) :
    vecCoeff (Fh D Φ h) ξ = 0 := by
  have hδ := D.δ_ne_zero
  obtain ⟨a, ha⟩ : ∃ a : ℚ, 2 * a = -ξ 0 := ⟨-ξ 0 / 2, by ring⟩
  obtain ⟨b, hb⟩ : ∃ b : ℚ, 2 * (D.δ * b) = -ξ 1 := ⟨-ξ 1 / (2 * D.δ), by field_simp⟩
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    refine hξ (funext fun i => ?_)
    fin_cases i
    · simpa [h1] using ha.symm
    · simpa [h2] using hb.symm
  obtain ⟨M, hM⟩ : ∃ M : GL (Fin 2) ℚ, (M : Matrix (Fin 2) (Fin 2) ℚ) = !![a, D.δ * b; b, a] :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, D.δ * b; b, a]
      (by rw [Matrix.det_fin_two_of]; exact norm_ne D hab), rfl⟩
  obtain ⟨t, ht, hγ⟩ : ∃ t : (A E)ˣ, (t : A E) = D.mkE (UpperTheory.ConvolutionTheory.R2.rt a) (UpperTheory.ConvolutionTheory.R2.rt b) ∧ ∃ γ, ratGL E 2 γ = aE t :=
    ⟨IdeleGroup.diagonal E (Units.mk0 _ (lin_ne D hab)), (D.mkE_rt a b).symm, exists_ratGL_aE _⟩
  have h1 := setIntegral_comp_matVec M (per_Gh D hL (aE t * h))
  rw [int_Gh, hW, hM] at h1
  rw [vecCoeff, ← h1]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have k2 : (2 : A ℚ) * (UpperTheory.ConvolutionTheory.R2.rt a * x 0 + UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) * x 1) = -pair ξ x := by
    have e2 : (2 : A ℚ) = UpperTheory.ConvolutionTheory.R2.rt (2 : ℚ) := (map_ofNat _ 2).symm
    have e0 : (2 : A ℚ) * UpperTheory.ConvolutionTheory.R2.rt a = -UpperTheory.ConvolutionTheory.R2.rt (ξ 0) := by
      rw [← map_neg, ← ha, e2]; exact (map_mul _ _ _).symm
    have e1 : (2 : A ℚ) * UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) = -UpperTheory.ConvolutionTheory.R2.rt (ξ 1) := by
      rw [← map_neg, ← hb, e2]; exact (map_mul _ _ _).symm
    rw [pair, Fin.sum_univ_two]
    linear_combination (x 0) * e0 + (x 1) * e1
  beta_reduce
  rw [pt_id D hL h a b t ht hγ x, k2]
  rfl

/- English proof (translation)
Take `⟨u, v, rfl⟩` from `D.exists_mkE b`. Use `set F := Fh D Φ h with hF`. Establish `hFc : Continuous F` using `cont_Fh D hΦ h`. Establish `hFper : ∀ l ∈ vecLattice ℚ (Fin 2), ∀ x, F (l + x) = F x` using `per_Fh D hL h`. Use `set a : Fin 2 → A ℚ := ![u, v] with ha`.

Establish `hTper : ∀ ξ ∈ vecLattice ℚ (Fin 2), ∀ x, F (ξ + x + a) = F (x + a)` using `fun ξ hξ x => by`. Rewrite using `[add_assoc, hFper ξ hξ]`. Use `set G : (Fin 2 → A ℚ) → ℂ := fun y => F (y + a) - F y with hG`. Establish `hGc : Continuous G` using `(hFc.comp (continuous_id.add continuous_const)).sub hFc`. Establish `hGper : ∀ ξ ∈ vecLattice ℚ (Fin 2), ∀ x, G (ξ + x) = G x` using `fun ξ hξ x => by`.

Simplify using `only [hG]`. Rewrite using `[hTper ξ hξ, hFper ξ hξ]`. Establish `hint : ∀ (f : (Fin 2 → A ℚ) → ℂ), Continuous f → ∀ ξ : Fin 2 → ℚ, IntegrableOn (fun x => f x * (adelicChar ℚ (-pair ξ x) : ℂ)) (vecDomain ℚ (Fin 2)) (vecMeasure ℚ (Fin 2))` using `fun f hf ξ => ((hf.mul (continuous_adelicChar_neg_pair ξ)).continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure`. Establish `hcoef : ∀ ξ, vecCoeff G ξ = 0`. Introduce `ξ`.

Establish `e1 : vecCoeff G ξ = vecCoeff (fun x => F (x + a)) ξ - vecCoeff F ξ`. Unfold `vecCoeff`. Use `Eq.trans ?_ (integral_sub (hint _ (hFc.comp (continuous_id.add continuous_const) : Continuous fun x => F (x + a)) ξ) (hint _ hFc ξ))` and prove the remaining obligations. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Use `show (F (x + a) - F x) * _ = F (x + a) * _ - F x * _`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, vecCoeff_translate hFper]`. Distinguish the cases in `h1 : ξ = 0`. Establish `hp : pair ξ a = 0`. Simplify using `[pair, h1]`.

Rewrite using `[hp, AddChar.map_zero_eq_one, Circle.coe_one, one_mul, sub_self]`. Rewrite using `[coef_zero D hL hW h ξ h1, mul_zero, sub_zero]`. Establish `hG0` using `congrFun (GlobalTheory.CompanionTheory.AdelicFourier.eq_zero_of_vecCoeff_eq_zero hGc hGper hcoef) 0`. Establish `h1 : F (0 + a) = F 0` using `sub_eq_zero.1 hG0`. Establish `e2 : F (0 + a) = Φ (gl (nU (D.mkE u v)) * h)`.

Simplify using `[hF, Fh, ha]`. Establish `e3 : F 0 = Φ h`. Simplify using `only [hF, Fh, Pi.zero_apply]`. Rewrite using `[D.mkE_zero, n_zero, one_mul]`. Rewrite using `[← e2, h1, e3]`.
-/
private theorem n_inv (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hΦ : Continuous Φ)
    (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g) (hW : ∀ h, WE D Φ h = 0) (b : A E) (h : GL (Fin 2) (A E)) :
    Φ (gl (nU b) * h) = Φ h := by
  obtain ⟨u, v, rfl⟩ := D.exists_mkE b
  set F := Fh D Φ h with hF
  have hFc : Continuous F := cont_Fh D hΦ h
  have hFper : ∀ l ∈ vecLattice ℚ (Fin 2), ∀ x, F (l + x) = F x := per_Fh D hL h
  set a : Fin 2 → A ℚ := ![u, v] with ha
  have hTper : ∀ ξ ∈ vecLattice ℚ (Fin 2), ∀ x, F (ξ + x + a) = F (x + a) := fun ξ hξ x => by
    rw [add_assoc, hFper ξ hξ]
  set G : (Fin 2 → A ℚ) → ℂ := fun y => F (y + a) - F y with hG
  have hGc : Continuous G := (hFc.comp (continuous_id.add continuous_const)).sub hFc
  have hGper : ∀ ξ ∈ vecLattice ℚ (Fin 2), ∀ x, G (ξ + x) = G x := fun ξ hξ x => by
    simp only [hG]
    rw [hTper ξ hξ, hFper ξ hξ]
  have hint : ∀ (f : (Fin 2 → A ℚ) → ℂ), Continuous f → ∀ ξ : Fin 2 → ℚ,
      IntegrableOn (fun x => f x * (adelicChar ℚ (-pair ξ x) : ℂ)) (vecDomain ℚ (Fin 2))
        (vecMeasure ℚ (Fin 2)) := fun f hf ξ =>
    ((hf.mul (continuous_adelicChar_neg_pair ξ)).continuousOn.integrableOn_compact
      isCompact_closure_vecDomain).mono_set subset_closure
  have hcoef : ∀ ξ, vecCoeff G ξ = 0 := by
    intro ξ
    have e1 : vecCoeff G ξ = vecCoeff (fun x => F (x + a)) ξ - vecCoeff F ξ := by
      unfold vecCoeff
      refine Eq.trans ?_ (integral_sub (hint _ (hFc.comp (continuous_id.add continuous_const) :
        Continuous fun x => F (x + a)) ξ) (hint _ hFc ξ))
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show (F (x + a) - F x) * _ = F (x + a) * _ - F x * _
      ring
    rw [e1, vecCoeff_translate hFper]
    by_cases h1 : ξ = 0
    · have hp : pair ξ a = 0 := by
        simp [pair, h1]
      rw [hp, AddChar.map_zero_eq_one, Circle.coe_one, one_mul, sub_self]
    · rw [coef_zero D hL hW h ξ h1, mul_zero, sub_zero]
  have hG0 := congrFun (GlobalTheory.CompanionTheory.AdelicFourier.eq_zero_of_vecCoeff_eq_zero hGc hGper hcoef) 0
  have h1 : F (0 + a) = F 0 := sub_eq_zero.1 hG0
  have e2 : F (0 + a) = Φ (gl (nU (D.mkE u v)) * h) := by
    simp [hF, Fh, ha]
  have e3 : F 0 = Φ h := by
    simp only [hF, Fh, Pi.zero_apply]
    rw [D.mkE_zero, n_zero, one_mul]
  rw [← e2, h1, e3]

end UpperTheory.ConvolutionTheory.RankTwoDescent.VanishingCoefficients

end

open UpperTheory.ConvolutionTheory.RankTwoDescent.VanishingCoefficients in
/- English proof (translation)
Introduce `E _ _ D Φ hΦ hL hW h g`. Establish `gm : ∀ x y : G1 E, gl (x * y) = gl x * gl y` using `fun _ _ => Units.ext rfl`. Establish `g1 : gl (1 : G1 E) = 1` using `Units.ext rfl`. Set `H : Subgroup (G1 E)` to `{ carrier := {s | ∀ g, Φ (gl s * g) = Φ g} mul_mem' := fun {x y} hx hy g => by`. Rewrite using `[gm, mul_assoc, hx, hy]`.

Use the proof step `one_mem' := fun g => by rw [g1, one_mul]`. Use the proof step `inv_mem' := fun {x} hx g => by`. Rewrite using `[← hx (gl x⁻¹ * g), ← mul_assoc, ← gm, mul_inv_cancel, g1, one_mul] }`. Establish `hH : H = ⊤` using `eq_top_of_nU_wW H (fun b g => n_inv D hΦ hL hW b g) (fun g => by`. Take `⟨γ, hγ⟩` from `rat_w (E := E)`.

Rewrite using `[← hγ, hL])`. Establish `: h ∈ H` using `hH ▸ Subgroup.mem_top h`. Conclude with `this g`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.killW :
    KillW := by
  intro E _ _ D Φ hΦ hL hW h g
  have gm : ∀ x y : G1 E, gl (x * y) = gl x * gl y := fun _ _ => Units.ext rfl
  have g1 : gl (1 : G1 E) = 1 := Units.ext rfl
  let H : Subgroup (G1 E) :=
    { carrier := {s | ∀ g, Φ (gl s * g) = Φ g}
      mul_mem' := fun {x y} hx hy g => by
        rw [gm, mul_assoc, hx, hy]
      one_mem' := fun g => by rw [g1, one_mul]
      inv_mem' := fun {x} hx g => by
        rw [← hx (gl x⁻¹ * g), ← mul_assoc, ← gm, mul_inv_cancel, g1, one_mul] }
  have hH : H = ⊤ := eq_top_of_nU_wW H (fun b g => n_inv D hΦ hL hW b g) (fun g => by
    obtain ⟨γ, hγ⟩ := rat_w (E := E)
    rw [← hγ, hL])
  have : h ∈ H := hH ▸ Subgroup.mem_top h
  exact this g
