import Mathlib

noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.GeoA

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Type) [CommRing R] [Algebra k R]

def act (σ : Ω ≃ₐ[k] Ω) : (Ω ⊗[k] R) ≃ₐ[k] (Ω ⊗[k] R) := Algebra.TensorProduct.congr σ AlgEquiv.refl

def actHom : (Ω ≃ₐ[k] Ω) →* RingAut (Ω ⊗[k] R) where
  toFun σ := (act R σ).toRingEquiv
  map_one' := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => simp [act]
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  map_mul' σ τ := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => simp [act]
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem act_tmul (σ : Ω ≃ₐ[k] Ω) (a : Ω) (r : R) : act R σ (a ⊗ₜ r) = σ a ⊗ₜ r := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a r => rw [TensorProduct.smul_tmul', act_tmul, AlgEquiv.smul_def]`. Consider the case `add x y hx hy => rw [smul_add, hx, hy, map_add]`.
-/
theorem smul_eq_act (σ : Ω ≃ₐ[k] Ω) (x : Ω ⊗[k] R) : σ • x = act R σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r => rw [TensorProduct.smul_tmul', act_tmul, AlgEquiv.smul_def]
  | add x y hx hy => rw [smul_add, hx, hy, map_add]

scoped instance instAct : MulSemiringAction (Ω ≃ₐ[k] Ω) (Ω ⊗[k] R) :=
  { TensorProduct.leftDistribMulAction with
    smul_one := fun σ => by rw [smul_eq_act, map_one]
    smul_mul := fun σ x y => by rw [smul_eq_act, smul_eq_act, smul_eq_act, map_mul] }

/- English proof (translation)
The claim follows from `smul_eq_act R σ x`.
-/
theorem smul_def (σ : Ω ≃ₐ[k] Ω) (x : Ω ⊗[k] R) : σ • x = act R σ x := smul_eq_act R σ x

attribute [local instance] Algebra.TensorProduct.rightAlgebra

scoped instance smulComm : SMulCommClass (Ω ≃ₐ[k] Ω) R (Ω ⊗[k] R) where
  smul_comm σ r x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_def, smul_def, map_mul]
    congr 1
    change act R σ (1 ⊗ₜ r) = 1 ⊗ₜ r
    simp

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a r`. Simplify using `only [act_tmul, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgEquiv.commutes]`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`.
-/
theorem repr_act {ι : Type} (b : Module.Basis ι k R) (σ : Ω ≃ₐ[k] Ω) (x : Ω ⊗[k] R) (i : ι) :
    (Algebra.TensorProduct.basis Ω b).repr (act R σ x) i = σ ((Algebra.TensorProduct.basis Ω b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r =>
    simp only [act_tmul, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, map_mul, AlgEquiv.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

variable [IsGalois k Ω]

open Classical in
/- English proof (translation)
Set `b` to `Module.Free.chooseBasis k R`. Set `B` to `Algebra.TensorProduct.basis Ω b`. Establish `hc : ∀ i, ∃ c : k, algebraMap k Ω c = B.repr x i` using `fun i => (InfiniteGalois.mem_range_algebraMap_iff_fixed (B.repr x i)).2 fun σ => by`. Rewrite using `[← repr_act R b σ x]`. Conclude with `congrArg (fun y => B.repr y i) (hx σ)`.

Set `φ : Ω → k` to `fun ω => if h : ∃ c : k, algebraMap k Ω c = ω then h.choose else 0`. Establish `hφ0 : φ 0 = 0`. Simplify using `only [φ]`. Use `split_ifs with h`. Conclude with `(algebraMap k Ω).injective (h.choose_spec.trans (map_zero _).symm)`.

Both sides reduce to the same expression. Establish `hφ : ∀ i, algebraMap k Ω (φ (B.repr x i)) = B.repr x i` using `fun i => by`. Simplify using `only [φ, dif_pos (hc i)]`. Conclude with `(hc i).choose_spec`. Set `f : Module.Free.ChooseBasisIndex k R →₀ k` to `Finsupp.mapRange φ hφ0 (B.repr x)`.

Use `⟨b.repr.symm f, B.repr.injective ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Express the relevant statement in the definitionally equal form `B.repr (1 ⊗ₜ (b.repr.symm f)) i = _`. Rewrite using `[Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply, Module.Basis.repr_symm_apply, Module.Basis.repr_linearCombination]`. Conclude with `hφ i`.
-/
theorem isInvariant : Algebra.IsInvariant R (Ω ⊗[k] R) (Ω ≃ₐ[k] Ω) where
  isInvariant x hx := by
    let b := Module.Free.chooseBasis k R
    let B := Algebra.TensorProduct.basis Ω b
    have hc : ∀ i, ∃ c : k, algebraMap k Ω c = B.repr x i := fun i =>
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (B.repr x i)).2 fun σ => by
        rw [← repr_act R b σ x]
        exact congrArg (fun y => B.repr y i) (hx σ)
    let φ : Ω → k := fun ω => if h : ∃ c : k, algebraMap k Ω c = ω then h.choose else 0
    have hφ0 : φ 0 = 0 := by
      simp only [φ]
      split_ifs with h
      · exact (algebraMap k Ω).injective (h.choose_spec.trans (map_zero _).symm)
      · rfl
    have hφ : ∀ i, algebraMap k Ω (φ (B.repr x i)) = B.repr x i := fun i => by
      simp only [φ, dif_pos (hc i)]
      exact (hc i).choose_spec
    let f : Module.Free.ChooseBasisIndex k R →₀ k := Finsupp.mapRange φ hφ0 (B.repr x)
    refine ⟨b.repr.symm f, B.repr.injective ?_⟩
    ext i
    change B.repr (1 ⊗ₜ (b.repr.symm f)) i = _
    rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply, Module.Basis.repr_symm_apply,
      Module.Basis.repr_linearCombination]
    exact hφ i

omit [IsGalois k Ω] in
/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero`. Use `Subgroup.isOpen_mono (H₁ := ⊤) (fun σ _ => by rw [MulAction.mem_stabilizer_iff, smul_zero]) ?_` and prove the remaining obligations. Rewrite using `[Subgroup.coe_top]`. Conclude with `isOpen_univ`.

Consider the case `tmul a r`. Use `Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (Ω ≃ₐ[k] Ω) a) ?_ (stabilizer_isOpen_of_isIntegral a)` and prove the remaining obligations. Introduce `σ hσ`. Rewrite `hσ`, the goal using `[MulAction.mem_stabilizer_iff]`. Rewrite using `[smul_def, act_tmul]`.

Conclude with `congrArg (· ⊗ₜ[k] r) hσ`. Consider the case `add x y hx hy`. Use `Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (Ω ≃ₐ[k] Ω) x ⊓ MulAction.stabilizer (Ω ≃ₐ[k] Ω) y) ?_ (by rw [Subgroup.coe_inf]; exact hx.inter hy)` and prove the remaining obligations. Introduce `σ hσ`. Rewrite using `[MulAction.mem_stabilizer_iff]`.

Rewrite using `[smul_add, MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hσ).1, MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hσ).2]`.
-/
theorem isOpen_stabilizer [Algebra.IsIntegral k Ω] (x : Ω ⊗[k] R) :
    IsOpen (MulAction.stabilizer (Ω ≃ₐ[k] Ω) x : Set (Ω ≃ₐ[k] Ω)) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    refine Subgroup.isOpen_mono (H₁ := ⊤) (fun σ _ => by rw [MulAction.mem_stabilizer_iff, smul_zero]) ?_
    rw [Subgroup.coe_top]; exact isOpen_univ
  | tmul a r =>
    refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (Ω ≃ₐ[k] Ω) a) ?_ (stabilizer_isOpen_of_isIntegral a)
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff] at hσ ⊢
    rw [smul_def, act_tmul]
    exact congrArg (· ⊗ₜ[k] r) hσ
  | add x y hx hy =>
    refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (Ω ≃ₐ[k] Ω) x ⊓ MulAction.stabilizer (Ω ≃ₐ[k] Ω) y)
      ?_ (by rw [Subgroup.coe_inf]; exact hx.inter hy)
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff]
    rw [smul_add, MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hσ).1,
      MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hσ).2]

/- English proof (translation)
Set `_ : TopologicalSpace (Ω ⊗[k] R)` to `⊥`. Establish `: DiscreteTopology (Ω ⊗[k] R)` using `⟨rfl⟩`. Establish `: ContinuousSMul (Ω ≃ₐ[k] Ω) (Ω ⊗[k] R)`. Rewrite using `[continuousSMul_iff_stabilizer_isOpen]`. Conclude with `isOpen_stabilizer R`.

Use `isInvariant (k := k) (Ω := Ω) R` as an intermediate fact. Use `smulComm (k := k) (Ω := Ω) R` as an intermediate fact. Take `⟨g, hg⟩` from `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := R) (G := Ω ≃ₐ[k] Ω) P Q h`. Use `⟨g⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[hg, Ideal.pointwise_smul_eq_comap]`.

Use extensionality with `x`. Simplify using `only [Ideal.mem_comap]`. Establish `e : (MulSemiringAction.toRingAut (Ω ≃ₐ[k] Ω) (Ω ⊗[k] R) g).symm x = act R g⁻¹ x`. Rewrite using `[← smul_def]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem exists_comap_eq (P Q : Ideal (Ω ⊗[k] R)) [P.IsPrime] [Q.IsPrime]
    (h : P.comap (Algebra.TensorProduct.includeRight : R →ₐ[k] Ω ⊗[k] R).toRingHom =
      Q.comap (Algebra.TensorProduct.includeRight : R →ₐ[k] Ω ⊗[k] R).toRingHom) :
    ∃ σ : Ω ≃ₐ[k] Ω, Q = P.comap (act R σ).toRingEquiv.toRingHom := by
  let _ : TopologicalSpace (Ω ⊗[k] R) := ⊥
  have : DiscreteTopology (Ω ⊗[k] R) := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[k] Ω) (Ω ⊗[k] R) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    exact isOpen_stabilizer R
  have := isInvariant (k := k) (Ω := Ω) R
  have := smulComm (k := k) (Ω := Ω) R
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := R) (G := Ω ≃ₐ[k] Ω) P Q h
  refine ⟨g⁻¹, ?_⟩
  rw [hg, Ideal.pointwise_smul_eq_comap]
  ext x
  simp only [Ideal.mem_comap]
  have e : (MulSemiringAction.toRingAut (Ω ≃ₐ[k] Ω) (Ω ⊗[k] R) g).symm x = act R g⁻¹ x := by
    rw [← smul_def]; rfl
  rw [e]; rfl

end CrystallineSemistableComparison.GeoA
