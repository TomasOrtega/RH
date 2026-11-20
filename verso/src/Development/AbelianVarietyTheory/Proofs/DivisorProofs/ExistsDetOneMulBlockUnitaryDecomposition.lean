import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitary
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.DetNormOneGen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DetDecomp

open GlobalTheory.UTrans

/- English proof (translation)
Simplify using `[hf, Pi.single_apply]`.
-/
theorem hf_single {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    hf σ M (Pi.single i 1) (Pi.single j 1) = M i j := by
  simp [hf, Pi.single_apply]

/- English proof (translation)
Use extensionality with `i j`. Use `h (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[hf_single]`. Rewrite using `[← this]`. Simplify using `only [hf, Matrix.mulVec_single_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.col_apply, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`.
-/
theorem isU_mat {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (M γ : Matrix (Fin n) (Fin n) R)
    (h : IsU σ M γ) : γᵀ * M * γ.map σ = M := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hf_single] at this
  rw [← this]
  simp only [hf, Matrix.mulVec_single_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.col_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Use `set x : Fin n → K := Pi.single i 1`. Use `set y : Fin n → K := Pi.single j 1`. Establish `hm0 : hf σ M x y ≠ 0` using `by rw [hf_single]; exact hij`.

Establish `hc` using `Calc.hf_conj σ M hσ hM x y`. Establish `e : hf σ M (x + hf σ M x y • y) (x + hf σ M x y • y) = hf σ M x x + σ (hf σ M x y) * hf σ M x y + hf σ M x y * hf σ M y x + hf σ M x y * σ (hf σ M x y) * hf σ M y y`. Simplify using `only [Calc.hf_add_left, Calc.hf_add_right, Calc.hf_smul_left, Calc.hf_smul_right]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `e` using `[hno, hno x, hno y, ← hc]`.

Establish `hs : σ (hf σ M x y) ≠ 0` using `(map_ne_zero σ).2 hm0`. Establish `: (2 : K) * (σ (hf σ M x y) * hf σ M x y) = 0` using `by linear_combination -e`. Break down `mul_eq_zero.1 this with h2 | h2` into its components or cases. Conclude with `two_ne_zero h2`. Conclude with `mul_ne_zero hs hm0 h2`.
-/
theorem exists_aniso {K : Type} [Field K] [CharZero K] {n : ℕ} (σ : K →+* K) (hσ : ∀ a, σ (σ a) = a)
    (M : Matrix (Fin n) (Fin n) K) (hM : ∀ a b, σ (M a b) = M b a) {i j : Fin n} (hij : M i j ≠ 0) :
    ∃ x : Fin n → K, hf σ M x x ≠ 0 := by
  by_contra hno
  push_neg at hno
  set x : Fin n → K := Pi.single i 1
  set y : Fin n → K := Pi.single j 1
  have hm0 : hf σ M x y ≠ 0 := by rw [hf_single]; exact hij
  have hc := Calc.hf_conj σ M hσ hM x y
  have e : hf σ M (x + hf σ M x y • y) (x + hf σ M x y • y) = hf σ M x x + σ (hf σ M x y) * hf σ M x y
      + hf σ M x y * hf σ M y x + hf σ M x y * σ (hf σ M x y) * hf σ M y y := by
    simp only [Calc.hf_add_left, Calc.hf_add_right, Calc.hf_smul_left, Calc.hf_smul_right]
    ring
  rw [hno, hno x, hno y, ← hc] at e
  have hs : σ (hf σ M x y) ≠ 0 := (map_ne_zero σ).2 hm0
  have : (2 : K) * (σ (hf σ M x y) * hf σ M x y) = 0 := by linear_combination -e
  rcases mul_eq_zero.1 this with h2 | h2
  · exact two_ne_zero h2
  · exact mul_ne_zero hs hm0 h2

/- English proof (translation)
Use `⟨Calc.isU_tv σ M hσ hM x _ ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hQ, map_mul, map_sub, map_one, hcr]`. Take the linear combination `r * hz + (z - 1) * (σ z - 1) * r * hrQ`. Rewrite using `[Calc.tv_det, hQ]`. Take the linear combination `(z - 1) * hrQ`.
-/
theorem refl_isU_det {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a)
    (M : Matrix (Fin n) (Fin n) R) (hM : ∀ a b, σ (M a b) = M b a) (x : Fin n → R) {Q r z : R}
    (hQ : hf σ M x x = Q) (hrQ : r * Q = 1) (hcr : σ r = r) (hz : z * σ z = 1) :
    IsU σ M (tv σ M x ((z - 1) * r)) ∧ (tv σ M x ((z - 1) * r)).det = z := by
  refine ⟨Calc.isU_tv σ M hσ hM x _ ?_, ?_⟩
  · rw [hQ, map_mul, map_sub, map_one, hcr]
    linear_combination r * hz + (z - 1) * (σ z - 1) * r * hrQ
  · rw [Calc.tv_det, hQ]
    linear_combination (z - 1) * hrQ

variable {D : D7}

/- English proof (translation)
Simplify using `only [hf, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, starRingEnd_apply]`.
-/
theorem hf_incA (V : HSp D) (x0 : Fin V.rank → D.host.E) :
    hf (cA D) (V.gram.map (incA D))ᵀ (fun a => incA D (x0 a)) (fun a => incA D (x0 a)) =
      incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0) := by
  simp only [hf, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA,
    starRingEnd_apply]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij⟩ : ∃ i j, V.gramᵀ i j ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Apply `GlobalTheory.LevelSubgroup.gram_det_ne_zero V` to reduce the goal to its premises. Establish `h0 : V.gram = 0` using `Matrix.ext fun a b => hne b a`.

Rewrite using `[h0]`. Use `haveI : Nonempty (Fin V.rank) := ⟨⟨0, hV⟩⟩`. Conclude with `Matrix.det_zero`. Conclude with `exists_aniso _ (fun a => star_star a) _ (fun a b => GlobalTheory.DualPairCheck.gram_star V b a) hij`.
-/
theorem exists_aniso_gram (V : HSp D) (hV : 0 < V.rank) :
    ∃ x0 : Fin V.rank → D.host.E, hf (starRingEnd D.host.E) V.gramᵀ x0 x0 ≠ 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, V.gramᵀ i j ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply GlobalTheory.LevelSubgroup.gram_det_ne_zero V
    have h0 : V.gram = 0 := Matrix.ext fun a b => hne b a
    rw [h0]
    haveI : Nonempty (Fin V.rank) := ⟨⟨0, hV⟩⟩
    exact Matrix.det_zero
  exact exists_aniso _ (fun a => star_star a) _ (fun a b => GlobalTheory.DualPairCheck.gram_star V b a) hij

/- English proof (translation)
Take `⟨x0, hx0⟩` from `exists_aniso_gram V hV`. Establish `hqs : star (hf (starRingEnd D.host.E) V.gramᵀ x0 x0) = hf (starRingEnd D.host.E) V.gramᵀ x0 x0` using `Calc.hf_conj (starRingEnd D.host.E) V.gramᵀ (fun a => star_star a) (fun a b => GlobalTheory.DualPairCheck.gram_star V b a) x0 x0`. Establish `hrQ : incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹ * incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hx0, map_one]`. Establish `hcr : cA D (incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹) = incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹`.

Rewrite using `[GlobalTheory.DualPairCheck.cA_incA, star_inv₀, hqs]`. Establish `hMA : ∀ a b, cA D ((V.gram.map (incA D))ᵀ a b) = (V.gram.map (incA D))ᵀ b a` using `fun a b => by`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]`. Take `⟨hU, hdet⟩` from `refl_isU_det (cA D) GlobalTheory.DualPairCheck.cA_cA _ hMA _ (hf_incA V x0) hrQ hcr hz`. Generalize the expression as in `tv (cA D) ((HSpace.gram V).map ⇑(incA D))ᵀ (fun a ↦ (incA D) (x0 a)) ((z - 1) * (incA D) (hf (starRingEnd D.host.E) (HSpace.gram V)ᵀ x0 x0)⁻¹) = γ at hU hdet`.

Establish `hzu : IsUnit z` using `⟨⟨z, cA D z, hz, by rw [mul_comm]; exact hz⟩, rfl⟩`. Establish `hmat` using `congrArg Matrix.transpose (isU_mat (cA D) _ _ hU)`. Rewrite `hmat` using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose, ← Matrix.mul_assoc]`. Establish `hunit` using `(Matrix.isUnit_iff_isUnit_det γ).2 (by rw [hdet]; exact hzu)`. Use `⟨⟨hunit.unit, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) hunit.unit.1 * JR (AF D.host.F) V.gram * hunit.unit.1 = JR (AF D.host.F) V.gram`. Rewrite using `[IsUnit.unit_spec]`. Conclude with `hmat`. Use `show (hunit.unit.1).det = z`. Rewrite using `[IsUnit.unit_spec]`.

Conclude with `hdet`.
-/
theorem exists_det_eq (V : HSp D) (hV : 0 < V.rank) (z : Formalism.L2.Theta.AE D) (hz : z * cA D z = 1) :
    ∃ g : GA D V, (mt V g).det = z := by
  obtain ⟨x0, hx0⟩ := exists_aniso_gram V hV
  have hqs : star (hf (starRingEnd D.host.E) V.gramᵀ x0 x0) = hf (starRingEnd D.host.E) V.gramᵀ x0 x0 :=
    Calc.hf_conj (starRingEnd D.host.E) V.gramᵀ (fun a => star_star a) (fun a b => GlobalTheory.DualPairCheck.gram_star V b a) x0 x0
  have hrQ : incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹ * incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  have hcr : cA D (incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹) =
      incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹ := by
    rw [GlobalTheory.DualPairCheck.cA_incA, star_inv₀, hqs]
  have hMA : ∀ a b, cA D ((V.gram.map (incA D))ᵀ a b) = (V.gram.map (incA D))ᵀ b a := fun a b => by
    simp only [Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  obtain ⟨hU, hdet⟩ := refl_isU_det (cA D) GlobalTheory.DualPairCheck.cA_cA _ hMA _ (hf_incA V x0) hrQ hcr hz
  generalize tv (cA D) ((HSpace.gram V).map ⇑(incA D))ᵀ (fun a ↦ (incA D) (x0 a))
    ((z - 1) * (incA D) (hf (starRingEnd D.host.E) (HSpace.gram V)ᵀ x0 x0)⁻¹) = γ at hU hdet
  have hzu : IsUnit z := ⟨⟨z, cA D z, hz, by rw [mul_comm]; exact hz⟩, rfl⟩
  have hmat := congrArg Matrix.transpose (isU_mat (cA D) _ _ hU)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
    ← Matrix.mul_assoc] at hmat
  have hunit := (Matrix.isUnit_iff_isUnit_det γ).2 (by rw [hdet]; exact hzu)
  refine ⟨⟨hunit.unit, ?_⟩, ?_⟩
  · show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) hunit.unit.1 * JR (AF D.host.F) V.gram * hunit.unit.1 =
      JR (AF D.host.F) V.gram
    rw [IsUnit.unit_spec]
    exact hmat
  · show (hunit.unit.1).det = z
    rw [IsUnit.unit_spec]
    exact hdet

/- English proof (translation)
Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]`.
-/
theorem det_blk {R : Type} [CommRing R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (P : Matrix (Fin p) (Fin p) R)
    (Q : Matrix (Fin q) (Fin q) R) : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e P Q).det = P.det * Q.det := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

/- English proof (translation)
Rewrite using `[skewGram, Matrix.det_smul, det_blk, Matrix.det_transpose, Matrix.det_transpose]`. Conclude with `mul_ne_zero (pow_ne_zero _ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero) (mul_ne_zero (GlobalTheory.LevelSubgroup.gram_det_ne_zero A) (GlobalTheory.LevelSubgroup.gram_det_ne_zero B))`.
-/
theorem skewGram_det_ne (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) :
    (skewGram A B e).det ≠ 0 := by
  rw [skewGram, Matrix.det_smul, det_blk, Matrix.det_transpose, Matrix.det_transpose]
  exact mul_ne_zero (pow_ne_zero _ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
    (mul_ne_zero (GlobalTheory.LevelSubgroup.gram_det_ne_zero A) (GlobalTheory.LevelSubgroup.gram_det_ne_zero B))

/- English proof (translation)
Establish `hx : (mat x)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (mat x).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J` using `x.2`. Establish `hd` using `congrArg Matrix.det hx`. Establish `hm : ((mat x).map (cA D)).det = cA D (mat x).det` using `(RingHom.map_det (cA D) (mat x)).symm`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hm]`. Establish `hJ : IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J).det`.

Establish `hm' : (J.map (incA D)).det = incA D J.det` using `(RingHom.map_det (incA D) J).symm`. Use `show IsUnit (J.map (incA D)).det`. Rewrite using `[hm']`. Establish `h0 : J.det ≠ 0` using `h ▸ skewGram_det_ne A B e`. Use `⟨⟨incA D J.det, incA D J.det⁻¹, ?_, ?_⟩, rfl⟩` and prove the remaining obligations.

Rewrite using `[← map_mul, mul_inv_cancel₀ h0, map_one]`. Rewrite using `[← map_mul, inv_mul_cancel₀ h0, map_one]`. Apply `hJ.mul_right_injective` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[mul_one]`.

Take the linear combination `hd`.
-/
theorem det_mul_conj (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = skewGram A B e) (x : UB J) : (mat x).det * cA D (mat x).det = 1 := by
  have hx : (mat x)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (mat x).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := x.2
  have hd := congrArg Matrix.det hx
  have hm : ((mat x).map (cA D)).det = cA D (mat x).det := (RingHom.map_det (cA D) (mat x)).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hm] at hd
  have hJ : IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J).det := by
    have hm' : (J.map (incA D)).det = incA D J.det := (RingHom.map_det (incA D) J).symm
    show IsUnit (J.map (incA D)).det
    rw [hm']
    have h0 : J.det ≠ 0 := h ▸ skewGram_det_ne A B e
    refine ⟨⟨incA D J.det, incA D J.det⁻¹, ?_, ?_⟩, rfl⟩
    · rw [← map_mul, mul_inv_cancel₀ h0, map_one]
    · rw [← map_mul, inv_mul_cancel₀ h0, map_one]
  apply hJ.mul_right_injective
  simp only
  rw [mul_one]
  linear_combination hd

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_blkU (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = skewGram A B e) (g : GA D A × GA D B) :
    mat (blkU A B e h g) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (mt A g.1) (mt B g.2) := rfl

/- English proof (translation)
Simplify using `[Formalism.L2.Theta.mt]`.
-/
theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

/- English proof (translation)
Introduce `D A B d e J h hd x`. Establish `hz` using `det_mul_conj A B e h x`. Establish `hzu : IsUnit (mat x).det` using `⟨⟨_, _, hz, by rw [mul_comm]; exact hz⟩, rfl⟩`. Establish `hcard : A.rank + B.rank = d` using `by simpa using Fintype.card_congr e`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g : GA D A × GA D B, (mat (blkU A B e h g)).det = (mat x).det := by`.

Break down `Nat.eq_zero_or_pos A.rank with hA | hA` into its components or cases. Take `⟨g, hg⟩` from `exists_det_eq B (by omega) _ hz`. Conclude with `⟨(1, g), by rw [mat_blkU, det_blk, mt_one, Matrix.det_one, one_mul, hg]⟩`. Take `⟨g, hg⟩` from `exists_det_eq A hA _ hz`. Conclude with `⟨(g, 1), by rw [mat_blkU, det_blk, mt_one, Matrix.det_one, mul_one, hg]⟩`.

Use `⟨x * (blkU A B e h g)⁻¹, g, ?_, (inv_mul_cancel_right x _).symm⟩` and prove the remaining obligations. Establish `hm : mat x = mat (x * (blkU A B e h g)⁻¹) * mat (blkU A B e h g)` using `by conv_lhs => rw [← inv_mul_cancel_right x (blkU A B e h g)]`. Both sides reduce to the same expression. Establish `hd2` using `congrArg Matrix.det hm`. Rewrite `hd2` using `[Matrix.det_mul, hg]`.

Apply `hzu.mul_left_injective` to reduce the goal to its premises. Simplify using `only [one_mul]`. Conclude with `hd2.symm`.
-/
theorem exists_detOne_mul_blkU : ∀ {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = skewGram A B e), 0 < d → ∀ x : UB J, ∃ (s : UB J) (g : GA D A × GA D B), (mat s).det = 1 ∧ x = s * blkU A B e h g := by
  intro D A B d e J h hd x
  have hz := det_mul_conj A B e h x
  have hzu : IsUnit (mat x).det := ⟨⟨_, _, hz, by rw [mul_comm]; exact hz⟩, rfl⟩
  have hcard : A.rank + B.rank = d := by simpa using Fintype.card_congr e
  obtain ⟨g, hg⟩ : ∃ g : GA D A × GA D B, (mat (blkU A B e h g)).det = (mat x).det := by
    rcases Nat.eq_zero_or_pos A.rank with hA | hA
    · obtain ⟨g, hg⟩ := exists_det_eq B (by omega) _ hz
      exact ⟨(1, g), by rw [mat_blkU, det_blk, mt_one, Matrix.det_one, one_mul, hg]⟩
    · obtain ⟨g, hg⟩ := exists_det_eq A hA _ hz
      exact ⟨(g, 1), by rw [mat_blkU, det_blk, mt_one, Matrix.det_one, mul_one, hg]⟩
  refine ⟨x * (blkU A B e h g)⁻¹, g, ?_, (inv_mul_cancel_right x _).symm⟩
  have hm : mat x = mat (x * (blkU A B e h g)⁻¹) * mat (blkU A B e h g) := by
    conv_lhs => rw [← inv_mul_cancel_right x (blkU A B e h g)]
    rfl
  have hd2 := congrArg Matrix.det hm
  rw [Matrix.det_mul, hg] at hd2
  apply hzu.mul_left_injective
  simp only [one_mul]
  exact hd2.symm

end GlobalTheory.DetDecomp
