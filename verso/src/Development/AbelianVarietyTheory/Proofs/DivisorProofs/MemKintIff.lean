import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/- English proof (translation)
Establish `h : ((intR p K r : Subring (Kn p K r)) : Set (Kn p K r)) = (Subtype.val : Kn p K r → PadicAlgCl p) ⁻¹' Metric.closedBall 0 1`. Use extensionality with `x`. Simplify using `only [intR, Subring.coe_comap, Set.mem_preimage, SetLike.mem_coe, Metric.mem_closedBall, dist_zero_right]`. Conclude with `mem_Obar_iff`. Rewrite using `[h]`.

Conclude with `(IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage continuous_subtype_val`.
-/
theorem isOpen_intR (r : ℕ) : IsOpen ((intR p K r : Subring (Kn p K r)) : Set (Kn p K r)) := by
  have h : ((intR p K r : Subring (Kn p K r)) : Set (Kn p K r)) =
      (Subtype.val : Kn p K r → PadicAlgCl p) ⁻¹' Metric.closedBall 0 1 := by
    ext x
    simp only [intR, Subring.coe_comap, Set.mem_preimage, SetLike.mem_coe, Metric.mem_closedBall, dist_zero_right]
    exact mem_Obar_iff
  rw [h]
  exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage continuous_subtype_val

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, rfl⟩`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Simplify using `[GeneralLinearGroup.map]`. Rewrite using `[← map_inv]`.

Simplify using `[GeneralLinearGroup.map]`. Introduce and unpack `⟨h1, h2⟩`. Set `A : Matrix (Fin n) (Fin n) (intR p K r)` to `Matrix.of fun i j => ⟨_, h1 i j⟩`. Set `B : Matrix (Fin n) (Fin n) (intR p K r)` to `Matrix.of fun i j => ⟨_, h2 i j⟩`. Establish `hA : A.map (intR p K r).subtype = (g : Matrix (Fin n) (Fin n) (Kn p K r))`.

Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hB : B.map (intR p K r).subtype = ((g⁻¹ : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r))`. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) (intR p K r) => M.map (intR p K r).subtype)` using `Matrix.map_injective Subtype.val_injective`. Establish `hAB : A * B = 1`. Apply `inj` to reduce the goal to its premises. Simplify using `only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `g.mul_inv`.

Establish `hBA : B * A = 1`. Apply `inj` to reduce the goal to its premises. Simplify using `only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `g.inv_mul`. Use `⟨⟨A, B, hAB, hBA⟩, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem mem_Kint_iff (n r : ℕ) (g : GL (Fin n) (Kn p K r)) :
    g ∈ Kint p K n r ↔ (∀ i j, (g : Matrix (Fin n) (Fin n) (Kn p K r)) i j ∈ intR p K r) ∧
      ∀ i j, ((g⁻¹ : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) i j ∈ intR p K r := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simp [GeneralLinearGroup.map]
    · rw [← map_inv]
      simp [GeneralLinearGroup.map]
  · rintro ⟨h1, h2⟩
    let A : Matrix (Fin n) (Fin n) (intR p K r) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) (intR p K r) := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hA : A.map (intR p K r).subtype = (g : Matrix (Fin n) (Fin n) (Kn p K r)) := by
      ext i j; rfl
    have hB : B.map (intR p K r).subtype = ((g⁻¹ : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) := by
      ext i j; rfl
    have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) (intR p K r) => M.map (intR p K r).subtype) :=
      Matrix.map_injective Subtype.val_injective
    have hAB : A * B = 1 := by
      apply inj
      simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    have hBA : B * A = 1 := by
      apply inj
      simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    rfl

/- English proof (translation)
Introduce `p _ K n r`. Establish `hS : IsOpen {M : Matrix (Fin n) (Fin n) (Kn p K r) | ∀ i j, M i j ∈ intR p K r}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (isOpen_intR p K r).preimage ((continuous_apply j).comp (continuous_apply i))`. Establish `hS' : IsOpen {M : (Matrix (Fin n) (Fin n) (Kn p K r))ᵐᵒᵖ | ∀ i j, (MulOpposite.unop M) i j ∈ intR p K r}` using `hS.preimage MulOpposite.continuous_unop`.

Establish `h : (Kint p K n r : Set (GL (Fin n) (Kn p K r))) = Units.embedProduct _ ⁻¹' ( {M : Matrix (Fin n) (Fin n) (Kn p K r) | ∀ i j, M i j ∈ intR p K r} ×ˢ {M : (Matrix (Fin n) (Fin n) (Kn p K r))ᵐᵒᵖ | ∀ i j, (MulOpposite.unop M) i j ∈ intR p K r})`. Use extensionality with `g`. Rewrite using `[SetLike.mem_coe, mem_Kint_iff]`. Both sides reduce to the same expression. Rewrite using `[h]`.

Conclude with `(hS.prod hS').preimage Units.continuous_embedProduct`.
-/
theorem isOpen_Kint : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ),
    IsOpen (Kint p K n r : Set (GL (Fin n) (Kn p K r))) := by
  intro p _ K n r
  have hS : IsOpen {M : Matrix (Fin n) (Fin n) (Kn p K r) | ∀ i j, M i j ∈ intR p K r} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_intR p K r).preimage ((continuous_apply j).comp (continuous_apply i))
  have hS' : IsOpen {M : (Matrix (Fin n) (Fin n) (Kn p K r))ᵐᵒᵖ | ∀ i j, (MulOpposite.unop M) i j ∈ intR p K r} :=
    hS.preimage MulOpposite.continuous_unop
  have h : (Kint p K n r : Set (GL (Fin n) (Kn p K r))) = Units.embedProduct _ ⁻¹' (
      {M : Matrix (Fin n) (Fin n) (Kn p K r) | ∀ i j, M i j ∈ intR p K r} ×ˢ
      {M : (Matrix (Fin n) (Fin n) (Kn p K r))ᵐᵒᵖ | ∀ i j, (MulOpposite.unop M) i j ∈ intR p K r}) := by
    ext g
    rw [SetLike.mem_coe, mem_Kint_iff]
    rfl
  rw [h]
  exact (hS.prod hS').preimage Units.continuous_embedProduct

end GlobalTheory.LKLoc
