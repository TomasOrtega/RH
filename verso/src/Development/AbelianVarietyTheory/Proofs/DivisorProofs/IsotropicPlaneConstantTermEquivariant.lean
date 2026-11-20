import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviIsoPlaneUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.DescB.GenSmooth

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

/- English proof (translation)
Use `haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _`. Use `haveI : CompleteSpace (Matrix (Fin n₁) (Fin n₁) ℂ) := FiniteDimensional.complete ℝ _`. Establish `h' : ∀ X : Matrix (Fin n₁) (Fin n) ℂ, R * (ι * X) = X` using `fun X => by rw [← Matrix.mul_assoc, h, Matrix.one_mul]`. Set `f : Matrix (Fin n₁) (Fin n₁) ℂ × ℂ →+* Matrix (Fin n) (Fin n) ℂ` to `{ toFun := fun p => ι * p.1 * R + p.2 • (1 - ι * R) map_one' := by simp map_mul' := fun p q => by`. Simplify using `only [Prod.fst_mul, Prod.snd_mul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h', Matrix.one_mul, Matrix.mul_one, sub_self, smul_zero, smul_smul, sub_zero, add_zero, zero_add]`.

Use `module`. Use the proof step `map_zero' := by simp`. Use the proof step `map_add' := fun p q => by`. Simplify using `only [Prod.fst_add, Prod.snd_add, Matrix.add_mul, Matrix.mul_add, add_smul]`. Use `abel }`.

Establish `hf : Continuous f` using `((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).add (continuous_snd.smul continuous_const)`. Establish `e` using `NormedSpace.map_exp f hf (A, 0)`. Establish `e1 : f (A, 0) = ι * A * R` using `by simp [f]`. Rewrite `e` using `[e1]`. Use `e.symm.trans ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `ι * (NormedSpace.exp (A, (0 : ℂ))).1 * R + (NormedSpace.exp (A, (0 : ℂ))).2 • (1 - ι * R) = _`. Establish `f1 : (NormedSpace.exp (A, (0 : ℂ))).1 = NormedSpace.exp A` using `Prod.fst_exp (A, (0 : ℂ))`. Establish `f2 : (NormedSpace.exp (A, (0 : ℂ))).2 = NormedSpace.exp 0` using `Prod.snd_exp (A, (0 : ℂ))`. Rewrite using `[f1, f2, NormedSpace.exp_zero, one_smul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws.
-/
theorem exp_sandwich {n n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) ℂ) (R : Matrix (Fin n₁) (Fin n) ℂ) (h : R * ι = 1)
    (A : Matrix (Fin n₁) (Fin n₁) ℂ) : NormedSpace.exp (ι * A * R) = 1 + ι * (NormedSpace.exp A - 1) * R := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  haveI : CompleteSpace (Matrix (Fin n₁) (Fin n₁) ℂ) := FiniteDimensional.complete ℝ _
  have h' : ∀ X : Matrix (Fin n₁) (Fin n) ℂ, R * (ι * X) = X := fun X => by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  let f : Matrix (Fin n₁) (Fin n₁) ℂ × ℂ →+* Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun p => ι * p.1 * R + p.2 • (1 - ι * R)
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h', Matrix.one_mul, Matrix.mul_one, sub_self, smul_zero,
          smul_smul, sub_zero, add_zero, zero_add]
        module
      map_zero' := by simp
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.add_mul, Matrix.mul_add, add_smul]; abel }
  have hf : Continuous f :=
    ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).add (continuous_snd.smul continuous_const)
  have e := NormedSpace.map_exp f hf (A, 0)
  have e1 : f (A, 0) = ι * A * R := by simp [f]
  rw [e1] at e
  refine e.symm.trans ?_
  change ι * (NormedSpace.exp (A, (0 : ℂ))).1 * R + (NormedSpace.exp (A, (0 : ℂ))).2 • (1 - ι * R) = _
  have f1 : (NormedSpace.exp (A, (0 : ℂ))).1 = NormedSpace.exp A := Prod.fst_exp (A, (0 : ℂ))
  have f2 : (NormedSpace.exp (A, (0 : ℂ))).2 = NormedSpace.exp 0 := Prod.snd_exp (A, (0 : ℂ))
  rw [f1, f2, NormedSpace.exp_zero, one_smul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField F] [NumberField E] in

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `congrArg σ (h (Pi.single i 1))` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_single_one]`. Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, map_zero, Finset.mul_sum] at this`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul, Pi.zero_apply]`.

Rewrite using `[Finset.sum_comm, ← this]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Simplify using `[mul_assoc]`.
-/
theorem form_zero (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E)
    (z : Fin n → E) (h : ∀ u, form σ J (ι *ᵥ u) z = 0) : ((ι.map σ)ᵀ * J.map σ) *ᵥ z = 0 := by
  funext i
  have := congrArg σ (h (Pi.single i 1))
  rw [Matrix.mulVec_single_one] at this
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, map_zero, Finset.mul_sum] at this
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul, Pi.zero_apply]
  rw [Finset.sum_comm, ← this]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  simp [mul_assoc]

/- English proof (translation)
Take `⟨hn, hxx, hyy, hxy, horth, hgram, -, hcart⟩` from `hP`. Substitute `hn` using the available equality. Establish `hadd : ∀ a b c, form σ Y.J (a + b) c = form σ Y.J a c + form σ Y.J b c` using `fun a b c => by`. Simplify using `[form, add_dotProduct]`. Establish `hsmul : ∀ (s : E) a c, form σ Y.J (s • a) c = s * form σ Y.J a c` using `fun s a c => by`.

Simplify using `[form, smul_dotProduct]`. Establish `hzero : ∀ c, form σ Y.J 0 c = 0` using `fun c => by simp [form]`. Establish `hyx : form σ Y.J H.y H.x = -1`. Use `GlobalTheory.LeviUniqueCartan.form_swap σ hσ Y.J hJ H.x H.y` as an intermediate fact. Rewrite `this` using `[hxy, map_one]`.

Take the linear combination `this`. Establish `hdet : Y₁.J.det ≠ 0`. Take `⟨w⟩` from `(inferInstance : Nonempty (InfinitePlace F))`. Conclude with `GlobalTheory.LeviUniqueCartan.det_ne_zero_of_isCartan _ _ _ (hcart w)`. Set `Φ : E × (Fin n₁ → E) × E →ₗ[E] (Fin (n₁ + 2) → E)` to `(LinearMap.smulRight LinearMap.id H.x).comp (LinearMap.fst E E ((Fin n₁ → E) × E)) + (Matrix.mulVecLin H.ι).comp ((LinearMap.fst E (Fin n₁ → E) E).comp (LinearMap.snd E E ((Fin n₁ → E) × E))) + (LinearMap.smulRight LinearMap.id H.y).comp ((LinearMap.snd E (Fin n₁ → E) E).comp (Li …`.

Establish `hΦ : ∀ s u r, Φ (s, u, r) = s • H.x + H.ι *ᵥ u + r • H.y` using `fun s u r => by`. Simplify using `[Φ]`. Establish `hinj : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce and unpack `⟨s, u, r⟩ h`.

Rewrite `h` using `[hΦ]`. Establish `e1` using `congrArg (fun z => form σ Y.J z H.y) h`. Simplify using `only [hadd, hsmul, hxy, hyy, (horth u).2, hzero] at e1`. Establish `hs : s = 0` using `by simpa using e1`. Substitute `hs` using the available equality.

Establish `e2` using `congrArg (fun z => form σ Y.J z H.x) h`. Simplify using `only [hadd, hsmul, hxx, hyx, (horth u).1, hzero] at e2`. Establish `hr : r = 0` using `by simpa using e2`. Substitute `hr` using the available equality. Establish `hu0 : H.ι *ᵥ u = 0` using `by simpa using h`.

Establish `hu : u ᵥ* Y₁.J = 0`. Rewrite using `[← hgram, Matrix.mul_assoc, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hu0, Matrix.zero_vecMul]`. Establish `: u = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨u, hne, hu⟩)`.

Substitute `this` using the available equality. Both sides reduce to the same expression. Establish `hsurj : Function.Surjective Φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp; omega)).mp hinj`. Use `choose p hp using fun j => hsurj (Pi.single j 1)`. Set `R : Matrix (Fin n₁) (Fin (n₁ + 2)) E` to `Matrix.of fun i j => (p j).2.1 i`.

Establish `hdec : H.ι * R + Matrix.vecMulVec H.x (fun j => (p j).1) + Matrix.vecMulVec H.y (fun j => (p j).2.2) = 1`. Use extensionality with `i j`. Use `congrFun ((hΦ (p j).1 (p j).2.1 (p j).2.2).symm.trans (hp j)) i` as an intermediate fact. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.single_apply] at this`. Simplify using `only [Matrix.add_apply, Matrix.mul_apply, Matrix.vecMulVec_apply, R, Matrix.of_apply, Matrix.one_apply]`.

Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hz` using `form_zero hσ Y.J H.ι`. Establish `hg : (H.ι.map σ)ᵀ * Y.J.map σ * H.ι = Y₁.J.map σ`. Rewrite using `[← hgram]`.

Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, hσ]`. Use `⟨R, _, _, hdec, ?_, ?_⟩` and prove the remaining obligations. Use `Matrix.ext_iff_mulVec.2 fun u => ?_` and prove the remaining obligations. Establish `h1` using `congrArg (· *ᵥ (H.ι *ᵥ u)) hdec`.

Simplify using `only [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h1`. Establish `h2 : Φ ((fun j => (p j).1) ⬝ᵥ H.ι *ᵥ u, R *ᵥ H.ι *ᵥ u, (fun j => (p j).2.2) ⬝ᵥ H.ι *ᵥ u) = Φ (0, u, 0)`. Rewrite using `[hΦ, hΦ, zero_smul, zero_smul, zero_add, add_zero]`. Use `conv_rhs => rw [← h1]`. Normalize the expressions using the abelian group laws.

Rewrite using `[← Matrix.mulVec_mulVec, Matrix.one_mulVec]`. Conclude with `congrArg (fun q => q.2.1) (hinj h2)`. Use `conv_lhs => rw [← Matrix.mul_one ((H.ι.map σ)ᵀ * Y.J.map σ), ← hdec]`. Rewrite using `[Matrix.mul_add, Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hz _ fun u => (horth u).1, hz _ fun u => (horth u).2, ← Matrix.mul_assoc, hg]`. Simplify using the standard rewrite rules.
-/
theorem exists_proj (B : Base F E) {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁}
    (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (Y.J j i) = -Y.J i j) (hP : IsIsoPlane σ B H Y Y₁) :
    ∃ (R : Matrix (Fin n₁) (Fin n) E) (s r : Fin n → E),
      H.ι * R + Matrix.vecMulVec H.x s + Matrix.vecMulVec H.y r = 1 ∧ R * H.ι = 1 ∧
      (H.ι.map σ)ᵀ * Y.J.map σ = Y₁.J.map σ * R := by
  obtain ⟨hn, hxx, hyy, hxy, horth, hgram, -, hcart⟩ := hP
  subst hn
  have hadd : ∀ a b c, form σ Y.J (a + b) c = form σ Y.J a c + form σ Y.J b c := fun a b c => by
    simp [form, add_dotProduct]
  have hsmul : ∀ (s : E) a c, form σ Y.J (s • a) c = s * form σ Y.J a c := fun s a c => by
    simp [form, smul_dotProduct]
  have hzero : ∀ c, form σ Y.J 0 c = 0 := fun c => by simp [form]
  have hyx : form σ Y.J H.y H.x = -1 := by
    have := GlobalTheory.LeviUniqueCartan.form_swap σ hσ Y.J hJ H.x H.y
    rw [hxy, map_one] at this
    linear_combination this
  have hdet : Y₁.J.det ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact GlobalTheory.LeviUniqueCartan.det_ne_zero_of_isCartan _ _ _ (hcart w)
  let Φ : E × (Fin n₁ → E) × E →ₗ[E] (Fin (n₁ + 2) → E) :=
    (LinearMap.smulRight LinearMap.id H.x).comp (LinearMap.fst E E ((Fin n₁ → E) × E)) +
    (Matrix.mulVecLin H.ι).comp ((LinearMap.fst E (Fin n₁ → E) E).comp (LinearMap.snd E E ((Fin n₁ → E) × E))) +
    (LinearMap.smulRight LinearMap.id H.y).comp ((LinearMap.snd E (Fin n₁ → E) E).comp (LinearMap.snd E E ((Fin n₁ → E) × E)))
  have hΦ : ∀ s u r, Φ (s, u, r) = s • H.x + H.ι *ᵥ u + r • H.y := fun s u r => by
    simp [Φ]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, u, r⟩ h
    rw [hΦ] at h
    have e1 := congrArg (fun z => form σ Y.J z H.y) h
    simp only [hadd, hsmul, hxy, hyy, (horth u).2, hzero] at e1
    have hs : s = 0 := by simpa using e1
    subst hs
    have e2 := congrArg (fun z => form σ Y.J z H.x) h
    simp only [hadd, hsmul, hxx, hyx, (horth u).1, hzero] at e2
    have hr : r = 0 := by simpa using e2
    subst hr
    have hu0 : H.ι *ᵥ u = 0 := by simpa using h
    have hu : u ᵥ* Y₁.J = 0 := by
      rw [← hgram, Matrix.mul_assoc, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hu0, Matrix.zero_vecMul]
    have : u = 0 := by
      by_contra hne
      exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨u, hne, hu⟩)
    subst this
    rfl
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp; omega)).mp hinj
  choose p hp using fun j => hsurj (Pi.single j 1)
  let R : Matrix (Fin n₁) (Fin (n₁ + 2)) E := Matrix.of fun i j => (p j).2.1 i
  have hdec : H.ι * R + Matrix.vecMulVec H.x (fun j => (p j).1) + Matrix.vecMulVec H.y (fun j => (p j).2.2) = 1 := by
    ext i j
    have := congrFun ((hΦ (p j).1 (p j).2.1 (p j).2.2).symm.trans (hp j)) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.single_apply] at this
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.vecMulVec_apply, R, Matrix.of_apply, Matrix.one_apply]
    rw [← this]; ring
  have hz := form_zero hσ Y.J H.ι
  have hg : (H.ι.map σ)ᵀ * Y.J.map σ * H.ι = Y₁.J.map σ := by
    rw [← hgram]
    ext i j
    simp [Matrix.mul_apply, hσ]
  refine ⟨R, _, _, hdec, ?_, ?_⟩
  · refine Matrix.ext_iff_mulVec.2 fun u => ?_
    have h1 := congrArg (· *ᵥ (H.ι *ᵥ u)) hdec
    simp only [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h1
    have h2 : Φ ((fun j => (p j).1) ⬝ᵥ H.ι *ᵥ u, R *ᵥ H.ι *ᵥ u, (fun j => (p j).2.2) ⬝ᵥ H.ι *ᵥ u) = Φ (0, u, 0) := by
      rw [hΦ, hΦ, zero_smul, zero_smul, zero_add, add_zero]
      conv_rhs => rw [← h1]
      abel
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    exact congrArg (fun q => q.2.1) (hinj h2)
  · conv_lhs => rw [← Matrix.mul_one ((H.ι.map σ)ᵀ * Y.J.map σ), ← hdec]
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hz _ fun u => (horth u).1,
      hz _ fun u => (horth u).2, ← Matrix.mul_assoc, hg]
    simp

/- English proof (translation)
Establish `hd' : incM F H.ι * incM F R + Matrix.vecMulVec (incV F H.x) (incV F s) + Matrix.vecMulVec (incV F H.y) (incV F r) = 1`. Use `congrArg (incM F) hd` as an intermediate fact. Rewrite `this` using `[incM, incM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), Matrix.map_mul]`. Rewrite using `[← this]`. Apply the tactic sequence `congr 2 <;> ext i j <;> simp [incV, Matrix.vecMulVec_apply]`.

Take `⟨h1, h2, h3⟩` from `hm`. Rewrite `h1` using `[Units.val_one, one_smul]`. Rewrite `h2` using `[inv_one, Units.val_one, map_one, one_smul]`. Use `conv_lhs => rw [← Matrix.mul_one (mat m), ← hd']`. Rewrite using `[Matrix.mul_add, Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, h1, h2, ← Matrix.mul_assoc, h3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]`.

Use `conv_rhs => rw [← hd']`. Normalize the expressions using the abelian group laws.
-/
theorem mat_levi {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {R : Matrix (Fin n₁) (Fin n) E} {s r : Fin n → E}
    (hd : H.ι * R + Matrix.vecMulVec H.x s + Matrix.vecMulVec H.y r = 1) {h₁ : UA σ Y₁.J} {m : UA σ Y.J}
    (hm : IsLevi (W₁ := Y₁) H 1 h₁ m) : mat m = 1 + incM F H.ι * (mat h₁ - 1) * incM F R := by
  have hd' : incM F H.ι * incM F R + Matrix.vecMulVec (incV F H.x) (incV F s) + Matrix.vecMulVec (incV F H.y) (incV F r) = 1 := by
    have := congrArg (incM F) hd
    rw [incM, incM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _),
      Matrix.map_mul] at this
    rw [← this]
    congr 2 <;> ext i j <;> simp [incV, Matrix.vecMulVec_apply]
  obtain ⟨h1, h2, h3⟩ := hm
  rw [Units.val_one, one_smul] at h1
  rw [inv_one, Units.val_one, map_one, one_smul] at h2
  conv_lhs => rw [← Matrix.mul_one (mat m), ← hd']
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, h1, h2, ← Matrix.mul_assoc, h3,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  conv_rhs => rw [← hd']
  abel

/- English proof (translation)
Take `⟨R, s, r, hd, hR, hA⟩` from `exists_proj B hσ hJ hP`. Take `⟨w, τ, Z, hZ, hγ⟩` from `hγ`. Establish `hτ : ∀ x, τ.1 (σ x) = star (τ.1 x)` using `hcm.2.2.2 τ.1`. Establish `key : ∀ (S : Type) [CommRing S] (φ : AE F E →+* S) (t : ℝ), (mat (m t)).map φ = 1 + (incM F H.ι).map φ * ((mat ((toGAd hσ Y₁.J hc).symm (γ t))).map φ - 1) * (incM F R).map φ` using `fun S _ φ t => by`. Rewrite using `[mat_levi hd (hm t), Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `hRc : R.map τ.1 * H.ι.map τ.1 = 1` using `by rw [← Matrix.map_mul, hR, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `⟨w, τ, H.ι.map τ.1 * Z * R.map τ.1, ?_, fun t => ⟨projArch σ _ w (toGAd hσ Y.J hc (m t)), ?_, ?_⟩⟩` and prove the remaining obligations. Establish `hQ : ((c • Y.J.map σ).map τ.1)ᴴ = (c • Y.J.map σ).map τ.1`. Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ← hτ, map_mul σ, hσ, hc']`.

Rewrite using `[hJ j i, mul_neg, neg_mul]`. Establish `hA' : (H.ι.map τ.1)ᴴ * (c • Y.J.map σ).map τ.1 = (c • Y₁.J.map σ).map τ.1 * R.map τ.1`. Rewrite using `[← Matrix.map_mul, Matrix.smul_mul, ← hA, ← Matrix.mul_smul, Matrix.map_mul]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[hτ]`. Generalize the expression as in `(c • Y.J.map σ).map τ.1 = Q at hQ hA' ⊢`. Generalize the expression as in `(c • Y₁.J.map σ).map τ.1 = Q₁ at hZ hA'`. Generalize the expression as in `H.ι.map τ.1 = ι at hA' hRc ⊢`. Generalize the expression as in `R.map τ.1 = R' at hA' hRc ⊢`.

Establish `e1 : Q₁ = ιᴴ * Q * ι` using `by rw [hA', Matrix.mul_assoc, hRc, Matrix.mul_one]`. Establish `e2 : Q₁ᴴ = Q₁`. Rewrite using `[e1]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQ, Matrix.mul_assoc]`. Establish `e3 : Q * ι = R'ᴴ * Q₁`.

Use `congrArg Matrix.conjTranspose hA'` as an intermediate fact. Simplify `this` using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQ, e2]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = R'ᴴ * (Zᴴ * Q₁ + Q₁ * Z) * R' := by`.

Rewrite using `[hA', e3]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Use `_ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]`. Take `⟨y, e1, -⟩` from `hγ t`. Use `GAd_ext σ _ (fun u => ?_) fun v => ?_` and prove the remaining obligations.

Distinguish the cases in `e : u = w`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[projArch_embArch_ne σ _ e]`. Establish `h1 : projArch σ _ u (γ t) = 1` using `by rw [e1, projArch_embArch_ne σ _ e]`.

Establish `h2 : (mat ((toGAd hσ Y₁.J hc).symm (γ t))).map (compInf F E u) = 1` using `congrArg (fun x => (matHom _ σ _ x).1) h1`. Establish `h3` using `key _ (compInf F E u) t`. Rewrite `h3` using `[h2, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]`. Conclude with `matHom_injective _ σ _ (Units.ext h3)`. Rewrite using `[proj_embArch]`.

Establish `h1 : proj σ _ v (γ t) = 1` using `by rw [e1, proj_embArch]`. Establish `h2 : (mat ((toGAd hσ Y₁.J hc).symm (γ t))).map (compFin F E v) = 1` using `congrArg (fun x => (matHom _ σ _ x).1) h1`. Establish `h3` using `key _ (compFin F E v) t`. Rewrite `h3` using `[h2, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]`. Conclude with `matHom_injective _ σ _ (Units.ext h3)`.

Take `⟨y, e1, e2⟩` from `hγ t`. Set `φ` to `(infEmb τ).comp (compInf F E w)`. Establish `h0 : ∀ x : E, φ (inclR (F` using `F) (AF F) x) = τ.1 x := fun x => by`. Express the relevant statement in the definitionally equal form `infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _`. Simplify using the standard rewrite rules.

Establish `h1 : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) E), (incM F X).map φ = X.map τ.1` using `fun X => Matrix.ext fun i j => h0 _`. Establish `h2 : (mat ((toGAd hσ Y₁.J hc).symm (γ t))).map φ = NormedSpace.exp (t • Z)`. Rewrite using `[← e2, ← projArch_embArch_self σ _ w y, ← e1]`. Both sides reduce to the same expression. Establish `h3` using `key _ φ t`.

Rewrite `h3` using `[h1, h1, h2, ← exp_sandwich _ _ hRc, Matrix.mul_smul, Matrix.smul_mul]`. Conclude with `h3`.
-/
theorem isRealLine_levi (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (hcm : IsCMExt F E σ) {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {H : Plane E n n₁} (hJ : ∀ i j, σ (Y.J j i) = -Y.J i j) (hP : IsIsoPlane σ B H Y Y₁) {c : E} (hc : c ≠ 0) (hc' : σ c = -c)
    {γ : ℝ → GAd σ (c • Y₁.J.map σ)} (hγ : IsRealLine σ (c • Y₁.J.map σ) γ) {m : ℝ → UA σ Y.J}
    (hm : ∀ t, IsLevi (W₁ := Y₁) H 1 ((toGAd hσ Y₁.J hc).symm (γ t)) (m t)) :
    IsRealLine σ (c • Y.J.map σ) fun t => toGAd hσ Y.J hc (m t) := by
  obtain ⟨R, s, r, hd, hR, hA⟩ := exists_proj B hσ hJ hP
  obtain ⟨w, τ, Z, hZ, hγ⟩ := hγ
  have hτ : ∀ x, τ.1 (σ x) = star (τ.1 x) := hcm.2.2.2 τ.1
  have key : ∀ (S : Type) [CommRing S] (φ : AE F E →+* S) (t : ℝ), (mat (m t)).map φ =
      1 + (incM F H.ι).map φ * ((mat ((toGAd hσ Y₁.J hc).symm (γ t))).map φ - 1) * (incM F R).map φ := fun S _ φ t => by
    rw [mat_levi hd (hm t), Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub _),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
  have hRc : R.map τ.1 * H.ι.map τ.1 = 1 := by rw [← Matrix.map_mul, hR, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨w, τ, H.ι.map τ.1 * Z * R.map τ.1, ?_, fun t => ⟨projArch σ _ w (toGAd hσ Y.J hc (m t)), ?_, ?_⟩⟩
  · have hQ : ((c • Y.J.map σ).map τ.1)ᴴ = (c • Y.J.map σ).map τ.1 := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ← hτ, map_mul σ, hσ, hc']
      rw [hJ j i, mul_neg, neg_mul]
    have hA' : (H.ι.map τ.1)ᴴ * (c • Y.J.map σ).map τ.1 = (c • Y₁.J.map σ).map τ.1 * R.map τ.1 := by
      rw [← Matrix.map_mul, Matrix.smul_mul, ← hA, ← Matrix.mul_smul, Matrix.map_mul]
      congr 1
      ext i j
      simp [hτ]
    generalize (c • Y.J.map σ).map τ.1 = Q at hQ hA' ⊢
    generalize (c • Y₁.J.map σ).map τ.1 = Q₁ at hZ hA'
    generalize H.ι.map τ.1 = ι at hA' hRc ⊢
    generalize R.map τ.1 = R' at hA' hRc ⊢
    have e1 : Q₁ = ιᴴ * Q * ι := by rw [hA', Matrix.mul_assoc, hRc, Matrix.mul_one]
    have e2 : Q₁ᴴ = Q₁ := by
      rw [e1]; simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQ, Matrix.mul_assoc]
    have e3 : Q * ι = R'ᴴ * Q₁ := by
      have := congrArg Matrix.conjTranspose hA'
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQ, e2] using this
    calc (ι * Z * R')ᴴ * Q + Q * (ι * Z * R') = R'ᴴ * Zᴴ * (ιᴴ * Q) + (Q * ι) * Z * R' := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = R'ᴴ * (Zᴴ * Q₁ + Q₁ * Z) * R' := by
          rw [hA', e3]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨y, e1, -⟩ := hγ t
    refine GAd_ext σ _ (fun u => ?_) fun v => ?_
    · by_cases e : u = w
      · subst e; simp
      · rw [projArch_embArch_ne σ _ e]
        have h1 : projArch σ _ u (γ t) = 1 := by rw [e1, projArch_embArch_ne σ _ e]
        have h2 : (mat ((toGAd hσ Y₁.J hc).symm (γ t))).map (compInf F E u) = 1 :=
          congrArg (fun x => (matHom _ σ _ x).1) h1
        have h3 := key _ (compInf F E u) t
        rw [h2, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero] at h3
        exact matHom_injective _ σ _ (Units.ext h3)
    · rw [proj_embArch]
      have h1 : proj σ _ v (γ t) = 1 := by rw [e1, proj_embArch]
      have h2 : (mat ((toGAd hσ Y₁.J hc).symm (γ t))).map (compFin F E v) = 1 :=
        congrArg (fun x => (matHom _ σ _ x).1) h1
      have h3 := key _ (compFin F E v) t
      rw [h2, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero] at h3
      exact matHom_injective _ σ _ (Units.ext h3)
  · obtain ⟨y, e1, e2⟩ := hγ t
    let φ := (infEmb τ).comp (compInf F E w)
    have h0 : ∀ x : E, φ (inclR (F := F) (AF F) x) = τ.1 x := fun x => by
      change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
      simp
    have h1 : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) E), (incM F X).map φ = X.map τ.1 := fun X => Matrix.ext fun i j => h0 _
    have h2 : (mat ((toGAd hσ Y₁.J hc).symm (γ t))).map φ = NormedSpace.exp (t • Z) := by
      rw [← e2, ← projArch_embArch_self σ _ w y, ← e1]; rfl
    have h3 := key _ φ t
    rw [h1, h1, h2, ← exp_sandwich _ _ hRc, Matrix.mul_smul, Matrix.smul_mul] at h3
    exact h3

/- English proof (translation)
Establish `e : mat (m * m') = mat m * mat m'` using `rfl`. Establish `e1 : mat (γ * h₁) = mat γ * mat h₁` using `rfl`. Take `⟨h1, h2, h3⟩` from `h`. Take `⟨h1', h2', h3'⟩` from `h'`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, ← Matrix.mulVec_mulVec, h1', Matrix.mulVec_smul, h1, smul_smul, Units.val_one, one_mul]`. Rewrite using `[e, ← Matrix.mulVec_mulVec, h2', Matrix.mulVec_smul, h2, smul_smul, inv_one, Units.val_one, map_one, one_mul]`. Rewrite using `[e, e1, Matrix.mul_assoc, h3', ← Matrix.mul_assoc, h3, Matrix.mul_assoc]`.
-/
theorem isLevi_mul_one {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {γ h₁ : UA σ Y₁.J}
    {m m' : UA σ Y.J} (h : IsLevi (W₁ := Y₁) H 1 γ m) (h' : IsLevi (W₁ := Y₁) H 1 h₁ m') :
    IsLevi (W₁ := Y₁) H 1 (γ * h₁) (m * m') := by
  have e : mat (m * m') = mat m * mat m' := rfl
  have e1 : mat (γ * h₁) = mat γ * mat h₁ := rfl
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [e, ← Matrix.mulVec_mulVec, h1', Matrix.mulVec_smul, h1, smul_smul, Units.val_one, one_mul]
  · rw [e, ← Matrix.mulVec_mulVec, h2', Matrix.mulVec_smul, h2, smul_smul, inv_one, Units.val_one, map_one, one_mul]
  · rw [e, e1, Matrix.mul_assoc, h3', ← Matrix.mul_assoc, h3, Matrix.mul_assoc]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ B hB n n₁ Y Y₁ P hJ hP c hc hc' fa hfa h _ hex g hg k γ hγ x`. Establish `h1K : (1 : UA σ Y.J) ∈ KInf σ Y B.emb`. Use `⟨fun u _ => by simp [mat], fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `Commute.one_left _`.

Establish `hsm` using `GlobalTheory.EisCont.CentreFinite.isSm_mul_right hB.cm (hfa ⊥ fun y hy => by rw [Subgroup.mem_bot.1 hy, map_one]; exact h1K).smooth (toGAd hσ Y.J hc h)`. Use `choose m hm using hex`. Establish `hl : ∀ (l : List (GAd σ (c • Y₁.J.map σ))), IsLevi (W₁` using `Y₁) P 1 ((toGAd hσ Y₁.J hc).symm l.prod) ((toGAd hσ Y.J hc).symm (l.map fun y => toGAd hσ Y.J hc (m ((toGAd hσ Y₁.J hc).symm y))).prod) := fun l => by`. Proceed by induction on `l with`. Consider the case `nil => simpa using PrimeSplit.isLevi_one (σ := σ) (W := Y) (W₁ := Y₁) P`.

Consider the case `cons y l ih`. Rewrite using `[List.map_cons, List.prod_cons, List.prod_cons, map_mul, map_mul, MulEquiv.symm_apply_apply]`. Simplify `GlobalTheory.ThK.DescB.GenSmooth.isLevi_mul_one (hm _) ih` using `only [mul_one]`. Use `hsm k (fun i t => toGAd hσ Y.J hc (m ((toGAd hσ Y₁.J hc).symm (γ i t)))) (fun i => isRealLine_levi hσ B hB.cm hJ hP hc hc' (hγ i) fun t => hm _) (toGAd hσ Y.J hc (m ((toGAd hσ Y₁.J hc).symm x)))` as an intermediate fact. Use `this using 2 with t` and compare the differences between its conclusion and the goal.

Establish `e` using `hl (List.ofFn fun i => γ i (t i))`. Rewrite `e` using `[List.map_ofFn]`. Simplify using `only [map_mul, MulEquiv.symm_apply_apply]`. Conclude with `hg _ _ (GlobalTheory.ThK.DescB.GenSmooth.isLevi_mul_one (hm _) e)`.
-/
theorem contDiff_gen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (P : Plane E n n₁), (∀ i j, σ (Y.J j i) = -Y.J i j) →
      IsIsoPlane σ B P Y Y₁ →
      ∀ (c : E) (hc : c ≠ 0), σ c = -c →
      ∀ fa : UA σ Y.J → ℂ, (∀ K : Subgroup (GAd σ (c • Y.J.map σ)), (∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb) →
        IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => fa ((toGAd hσ Y.J hc).symm x))) →
      ∀ h ∈ finK σ Y B.emb, (∀ h₁ : UA σ Y₁.J, ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) P 1 h₁ m) →
      ∀ g : UA σ Y₁.J → ℂ, (∀ h₁ m, IsLevi (W₁ := Y₁) P 1 h₁ m → g h₁ = fa (m * h)) →
      ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ (c • Y₁.J.map σ)), (∀ i, IsRealLine σ (c • Y₁.J.map σ) (γ i)) → ∀ x,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => (fun x => g ((toGAd hσ Y₁.J hc).symm x)) (x * (List.ofFn fun i => γ i (t i)).prod) := by
  intro F E _ _ _ _ _ σ hσ B hB n n₁ Y Y₁ P hJ hP c hc hc' fa hfa h _ hex g hg k γ hγ x
  have h1K : (1 : UA σ Y.J) ∈ KInf σ Y B.emb := by
    refine ⟨fun u _ => by simp [mat], fun w => ?_⟩
    rw [show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Commute.one_left _
  have hsm := GlobalTheory.EisCont.CentreFinite.isSm_mul_right hB.cm
    (hfa ⊥ fun y hy => by rw [Subgroup.mem_bot.1 hy, map_one]; exact h1K).smooth (toGAd hσ Y.J hc h)
  choose m hm using hex
  have hl : ∀ (l : List (GAd σ (c • Y₁.J.map σ))), IsLevi (W₁ := Y₁) P 1 ((toGAd hσ Y₁.J hc).symm l.prod)
      ((toGAd hσ Y.J hc).symm (l.map fun y => toGAd hσ Y.J hc (m ((toGAd hσ Y₁.J hc).symm y))).prod) := fun l => by
    induction l with
    | nil => simpa using PrimeSplit.isLevi_one (σ := σ) (W := Y) (W₁ := Y₁) P
    | cons y l ih =>
      rw [List.map_cons, List.prod_cons, List.prod_cons, map_mul, map_mul, MulEquiv.symm_apply_apply]
      simpa only [mul_one] using GlobalTheory.ThK.DescB.GenSmooth.isLevi_mul_one (hm _) ih
  have := hsm k (fun i t => toGAd hσ Y.J hc (m ((toGAd hσ Y₁.J hc).symm (γ i t))))
    (fun i => isRealLine_levi hσ B hB.cm hJ hP hc hc' (hγ i) fun t => hm _) (toGAd hσ Y.J hc (m ((toGAd hσ Y₁.J hc).symm x)))
  convert this using 2 with t
  have e := hl (List.ofFn fun i => γ i (t i))
  rw [List.map_ofFn] at e
  simp only [map_mul, MulEquiv.symm_apply_apply]
  exact hg _ _ (GlobalTheory.ThK.DescB.GenSmooth.isLevi_mul_one (hm _) e)

end GlobalTheory.ThK.DescB.GenSmooth

end
