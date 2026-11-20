import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

noncomputable section

namespace GlobalTheory.ColAction

/- English proof (translation)
Simplify using `[sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, Finset.sum_neg_distrib, mul_comm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sympl_eq_neg_dotProduct {l : Type} [Fintype l] [DecidableEq l] (u v : l ⊕ l → ℝ) :
    sympl u v = -(u ⬝ᵥ (Matrix.J l ℝ *ᵥ v)) := by
  simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.one_apply, Finset.sum_neg_distrib, mul_comm]
  ring

/- English proof (translation)
Rewrite using `[SymplecticGroup.mem_iff']`. Use extensionality with `a b`. Establish `key : ∀ u v, (M *ᵥ u) ⬝ᵥ (Matrix.J l ℝ *ᵥ (M *ᵥ v)) = u ⬝ᵥ ((Mᵀ * Matrix.J l ℝ * M) *ᵥ v)`. Introduce `u v`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Mᵀ, Matrix.vecMul_transpose]`.

Use `h (Pi.single a 1) (Pi.single b 1)` as an intermediate fact. Rewrite `this` using `[sympl_eq_neg_dotProduct, sympl_eq_neg_dotProduct, neg_inj, key]`. Simplify `this` using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem mem_symplecticGroup_of_sympl {l : Type} [Fintype l] [DecidableEq l] (M : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ u v, sympl (M *ᵥ u) (M *ᵥ v) = sympl u v) : M ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff']
  ext a b
  have key : ∀ u v, (M *ᵥ u) ⬝ᵥ (Matrix.J l ℝ *ᵥ (M *ᵥ v)) = u ⬝ᵥ ((Mᵀ * Matrix.J l ℝ * M) *ᵥ v) := by
    intro u v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Mᵀ, Matrix.vecMul_transpose]
  have := h (Pi.single a 1) (Pi.single b 1)
  rw [sympl_eq_neg_dotProduct, sympl_eq_neg_dotProduct, neg_inj, key] at this
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

/- English proof (translation)
Establish `e : Jm P Q * X * Jm R S = Matrix.of fun a b => ((fun _ => (1 : ℂ)) ⊕ᵥ fun _ => -1) a * X a b * ((fun _ => (1 : ℂ)) ⊕ᵥ fun _ => -1) b`. Use extensionality with `a b`. Simplify using `[Jm, Formalism.UG.P.Jpq_eq_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]`. Rewrite using `[e]`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]`.

Simplify using `[Fintype.sum_sum_type, lineSign]`.
-/
theorem signed_sum_eq_trace {P Q R S : ℕ} (X Y : Matrix (Ix P Q) (Ix R S) ℂ) :
    ∑ a, ∑ b, lineSign a b * X a b * star (Y a b) = Matrix.trace (Jm P Q * X * Jm R S * Yᴴ) := by
  have e : Jm P Q * X * Jm R S =
      Matrix.of fun a b => ((fun _ => (1 : ℂ)) ⊕ᵥ fun _ => -1) a * X a b * ((fun _ => (1 : ℂ)) ⊕ᵥ fun _ => -1) b := by
    ext a b
    simp [Jm, Formalism.UG.P.Jpq_eq_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [e]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [Fintype.sum_sum_type, lineSign]

/- English proof (translation)
Establish `hJ : (Jm R S)ᵀ = Jm R S`. Simplify using `[Jm, Formalism.UG.P.Jpq_eq_diagonal]`. Establish `e : (kᵀ)ᴴ = k.map star` using `by ext i j; simp`. Establish `hk' : kᵀ * Jm R S * (kᵀ)ᴴ = Jm R S`. Use `congrArg Matrix.transpose hk` as an intermediate fact.

Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_mul, hJ, Matrix.conjTranspose_transpose]`. Rewrite using `[e, Matrix.mul_assoc, this]`. Rewrite using `[signed_sum_eq_trace, signed_sum_eq_trace, Matrix.conjTranspose_mul]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hk']`.
-/
theorem signed_sum_mul_transpose {P Q R S : ℕ} (X Y : Matrix (Ix P Q) (Ix R S) ℂ) (k : Mat R S)
    (hk : kᴴ * Jm R S * k = Jm R S) :
    ∑ a, ∑ b, lineSign a b * (X * kᵀ) a b * star ((Y * kᵀ) a b) = ∑ a, ∑ b, lineSign a b * X a b * star (Y a b) := by
  have hJ : (Jm R S)ᵀ = Jm R S := by
    simp [Jm, Formalism.UG.P.Jpq_eq_diagonal]
  have e : (kᵀ)ᴴ = k.map star := by ext i j; simp
  have hk' : kᵀ * Jm R S * (kᵀ)ᴴ = Jm R S := by
    have := congrArg Matrix.transpose hk
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hJ, Matrix.conjTranspose_transpose] at this
    rw [e, Matrix.mul_assoc, this]
  rw [signed_sum_eq_trace, signed_sum_eq_trace, Matrix.conjTranspose_mul]
  congr 1
  calc Jm P Q * (X * kᵀ) * Jm R S * ((kᵀ)ᴴ * Yᴴ) = Jm P Q * X * (kᵀ * Jm R S * (kᵀ)ᴴ) * Yᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hk']

/- English proof (translation)
Introduce `ι l _ _ _ _ P Q R S φ hφ G _ _ k hk hkJ`. Set `A : G → (ι → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (ι → Matrix (Ix P Q) (Ix R S) ℂ)` to `fun g => { toFun := fun c w => c w * (k g w)ᵀ map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul] map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }`. Set `T : G → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)` to `fun g => φ.toLinearMap ∘ₗ A g ∘ₗ φ.symm.toLinearMap`. Establish `hT : ∀ g c, T g (φ c) = φ (fun w => c w * (k g w)ᵀ)` using `fun g c => by simp [T, A]`. Establish `hsy : ∀ g u v, sympl (T g u) (T g v) = sympl u v`.

Introduce `g u v`. Take `⟨c, rfl⟩` from `φ.surjective u`. Take `⟨c', rfl⟩` from `φ.surjective v`. Rewrite using `[hT, hT, hφ, hφ]`. Simplify using `only [signed_sum_mul_transpose _ _ _ (hkJ g _)]`.

Establish `hmem : ∀ g, LinearMap.toMatrix' (T g) ∈ Matrix.symplecticGroup l ℝ` using `fun g => mem_symplecticGroup_of_sympl _ (fun u v => by simpa only [LinearMap.toMatrix'_mulVec] using hsy g u v)`. Establish `hTmul : ∀ g h, T (g * h) = T g ∘ₗ T h`. Introduce `g h`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `u`.

Take `⟨c, rfl⟩` from `φ.surjective u`. Use `show T (g * h) (φ c) = T g (T h (φ c))`. Rewrite using `[hT, hT, hT]`. Use `congr 1`. Use extensionality with `w : 1`.

Simplify using `[map_mul, Pi.mul_apply, Matrix.transpose_mul, Matrix.mul_assoc]`. Establish `hT1 : T 1 = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `u`. Take `⟨c, rfl⟩` from `φ.surjective u`.

Rewrite using `[hT]`. Simplify using the standard rewrite rules. Set `s : G →* Matrix.symplecticGroup l ℝ` to `{ toFun := fun g => ⟨LinearMap.toMatrix' (T g), hmem g⟩ map_one' := by`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [hT1, LinearMap.toMatrix'_id]`.

Both sides reduce to the same expression. Use the proof step `map_mul' := fun g h => by`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [hTmul, LinearMap.toMatrix'_comp]`. Use `rfl }`.

Use `⟨s, ?_, fun g c => ?_⟩` and prove the remaining obligations. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Establish `e : ∀ g, LinearMap.toMatrix' (T g) a b = φ (fun w => φ.symm (Pi.single b 1) w * (k g w)ᵀ) a`. Introduce `g`.

Rewrite using `[LinearMap.toMatrix'_apply, ← hT, φ.apply_symm_apply]`. Simplify using `only [e]`. Conclude with `(continuous_apply a).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp (continuous_pi fun w => continuous_const.matrix_mul ((continuous_apply w).comp hk).matrix_transpose))`. Use `show LinearMap.toMatrix' (T g) *ᵥ φ c = _`. Rewrite using `[LinearMap.toMatrix'_mulVec, hT]`.
-/
theorem exists_symplectic_hom_of_unitary : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ G _ _ k hk hkJ
  let A : G → (ι → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (ι → Matrix (Ix P Q) (Ix R S) ℂ) := fun g =>
    { toFun := fun c w => c w * (k g w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  let T : G → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ) := fun g => φ.toLinearMap ∘ₗ A g ∘ₗ φ.symm.toLinearMap
  have hT : ∀ g c, T g (φ c) = φ (fun w => c w * (k g w)ᵀ) := fun g c => by simp [T, A]
  have hsy : ∀ g u v, sympl (T g u) (T g v) = sympl u v := by
    intro g u v
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    rw [hT, hT, hφ, hφ]
    simp only [signed_sum_mul_transpose _ _ _ (hkJ g _)]
  have hmem : ∀ g, LinearMap.toMatrix' (T g) ∈ Matrix.symplecticGroup l ℝ := fun g =>
    mem_symplecticGroup_of_sympl _ (fun u v => by simpa only [LinearMap.toMatrix'_mulVec] using hsy g u v)
  have hTmul : ∀ g h, T (g * h) = T g ∘ₗ T h := by
    intro g h
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    show T (g * h) (φ c) = T g (T h (φ c))
    rw [hT, hT, hT]
    congr 1
    ext w : 1
    simp [map_mul, Pi.mul_apply, Matrix.transpose_mul, Matrix.mul_assoc]
  have hT1 : T 1 = LinearMap.id := by
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    rw [hT]
    simp
  let s : G →* Matrix.symplecticGroup l ℝ :=
    { toFun := fun g => ⟨LinearMap.toMatrix' (T g), hmem g⟩
      map_one' := by
        apply Subtype.ext
        simp only [hT1, LinearMap.toMatrix'_id]
        rfl
      map_mul' := fun g h => by
        apply Subtype.ext
        simp only [hTmul, LinearMap.toMatrix'_comp]
        rfl }
  refine ⟨s, ?_, fun g c => ?_⟩
  · apply Continuous.subtype_mk
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have e : ∀ g, LinearMap.toMatrix' (T g) a b = φ (fun w => φ.symm (Pi.single b 1) w * (k g w)ᵀ) a := by
      intro g
      rw [LinearMap.toMatrix'_apply, ← hT, φ.apply_symm_apply]
    simp only [e]
    exact (continuous_apply a).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      (continuous_pi fun w => continuous_const.matrix_mul ((continuous_apply w).comp hk).matrix_transpose))
  · show LinearMap.toMatrix' (T g) *ᵥ φ c = _
    rw [LinearMap.toMatrix'_mulVec, hT]

end GlobalTheory.ColAction
