import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAsAlgebraHomEq

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace ℂ V`. Set `F` to `TensorProduct.equivFinsuppOfBasisLeft (N := B) b`. Establish `key : ∀ (j : _) (y : V ⊗[ℂ] B), F y j = TensorProduct.lid ℂ B (LinearMap.rTensor B (b.coord j) y)`. Introduce `j y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul v w => simp [F, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`. Apply `F.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Use extensionality with `j`. Rewrite using `[key, h]`. Simplify using the standard rewrite rules.
-/
private theorem tens_sep {V B : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup B] [Module ℂ B]
    (z : V ⊗[ℂ] B)
    (h : ∀ φ : Module.Dual ℂ V, TensorProduct.lid ℂ B (LinearMap.rTensor B φ z) = 0) : z = 0 := by
  let b := Module.Basis.ofVectorSpace ℂ V
  let F := TensorProduct.equivFinsuppOfBasisLeft (N := B) b
  have key : ∀ (j : _) (y : V ⊗[ℂ] B),
      F y j = TensorProduct.lid ℂ B (LinearMap.rTensor B (b.coord j) y) := by
    intro j y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [F, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply F.injective
  rw [map_zero]
  ext j
  rw [key, h]
  simp

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v w => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
private theorem comm_ext {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (X : Representation ℂ G V) (T : Representation ℂ H W)
    (g : H × G) (z : V ⊗[ℂ] W) :
    TensorProduct.comm ℂ V W (extTensor X T (g.2, g.1) z) =
      extTensor T X g (TensorProduct.comm ℂ V W z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp
  | add x y hx hy => simp only [map_add, hx, hy]

private noncomputable def swapSub {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (X : Representation ℂ G V) (T : Representation ℂ H W)
    (S : Subrepresentation (extTensor X T)) : Subrepresentation (extTensor T X) where
  toSubmodule := S.toSubmodule.map (TensorProduct.comm ℂ V W).toLinearMap
  apply_mem_toSubmodule g := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨extTensor X T (g.2, g.1) z, S.apply_mem_toSubmodule _ hz, comm_ext X T g z⟩

/- English proof (translation)
Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨y, hy, rfl⟩, rfl⟩`. Simplify using `using hy`.

Introduce `hz`. Conclude with `⟨TensorProduct.comm ℂ V W z, ⟨z, hz, rfl⟩, by simp⟩`.
-/
private theorem swapSub_swapSub {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (X : Representation ℂ G V) (T : Representation ℂ H W)
    (S : Subrepresentation (extTensor X T)) : swapSub T X (swapSub X T S) = S := by
  apply Subrepresentation.toSubmodule_injective
  ext z
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa using hy
  · intro hz
    exact ⟨TensorProduct.comm ℂ V W z, ⟨z, hz, rfl⟩, by simp⟩

private noncomputable def swapIso {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (X : Representation ℂ G V) (T : Representation ℂ H W) :
    Subrepresentation (extTensor X T) ≃o Subrepresentation (extTensor T X) where
  toFun := swapSub X T
  invFun := swapSub T X
  left_inv := swapSub_swapSub X T
  right_inv := swapSub_swapSub T X
  map_rel_iff' := by
    intro S S'
    constructor
    · intro h z hz
      obtain ⟨y, hy, e⟩ := h (show TensorProduct.comm ℂ V W z ∈ (swapSub X T S).toSubmodule from
        ⟨z, hz, rfl⟩)
      have e' : y = z := (TensorProduct.comm ℂ V W).injective e
      exact e' ▸ hy
    · rintro h _ ⟨z, hz, rfl⟩
      exact ⟨z, h hz, rfl⟩

/- English proof (translation)
Introduce `T hT`. Take `⟨b₀, hb₀⟩` from `exists_ne (0 : B)`. Choose the witnesses or unpack the hypotheses as in `⟨β, hβ⟩ : ∃ β : Module.Dual ℂ B, β b₀ = 1 := by`. Take `⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ B, φ b₀ ≠ 0` from `by by_contra! h`. Conclude with `hb₀ ((Module.forall_dual_apply_eq_zero_iff ℂ b₀).1 h)`.

Conclude with `⟨(φ b₀)⁻¹ • φ, by simp [hφ]⟩`. Set `L : Module.Dual ℂ V → (V ⊗[ℂ] B →ₗ[ℂ] B)` to `fun φ => (TensorProduct.lid ℂ B).toLinearMap ∘ₗ LinearMap.rTensor B φ`. Set `R : V ⊗[ℂ] B →ₗ[ℂ] V` to `(TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V β`. Establish `hLt : ∀ φ x y, L φ (x ⊗ₜ y) = φ x • y` using `fun φ x y => by simp [L]`. Establish `hRt : ∀ x y, R (x ⊗ₜ y) = β y • x` using `fun x y => by simp [R]`.

Establish `hL : ∀ φ c z, L φ (extTensor σ m (1, c) z) = m c (L φ z)`. Introduce `φ c z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [hLt]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `hR : ∀ g z, R (extTensor σ m (g, 1) z) = σ g (R z)`. Introduce `g z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x y => simp [hRt]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `hLR : ∀ (φ : Module.Dual ℂ V) z, φ (R z) = β (L φ z)`. Introduce `φ z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul x y => simp [hLt, hRt, mul_comm]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Set `S : V →ₗ[ℂ] V` to `R ∘ₗ T ∘ₗ (TensorProduct.mk ℂ V B).flip b₀`. Establish `hS : ∀ v, S v = R (T (v ⊗ₜ b₀))` using `fun v => rfl`.

Establish `hpure : ∀ v b, T (v ⊗ₜ b) = S v ⊗ₜ b`. Introduce `v b`. Rewrite using `[← sub_eq_zero]`. Apply `tens_sep` to reduce the goal to its premises. Introduce `φ`.

Take `⟨c, hc⟩` from `hm (L φ ∘ₗ T ∘ₗ TensorProduct.mk ℂ V B v) (by`. Introduce `c y`. Establish `h1 : v ⊗ₜ[ℂ] m c y = extTensor σ m (1, c) (v ⊗ₜ y)` using `by simp`. Simplify using `only [LinearMap.comp_apply, TensorProduct.mk_apply]`. Rewrite using `[h1, hT, hL])`.

Establish `hc' : ∀ y, L φ (T (v ⊗ₜ y)) = c • y` using `hc`. Establish `hφS : φ (S v) = c`. Rewrite using `[hS, hLR, hc', map_smul, hβ, smul_eq_mul, mul_one]`. Express the relevant statement in the definitionally equal form `L φ (T (v ⊗ₜ b) - S v ⊗ₜ b) = 0`. Rewrite using `[map_sub, hc', hLt, hφS, sub_self]`.

Take `⟨c, hc⟩` from `hσ S (by`. Introduce `g v`. Establish `h1 : σ g v ⊗ₜ[ℂ] b₀ = extTensor σ m (g, 1) (v ⊗ₜ b₀)` using `by simp`. Rewrite using `[hS, h1, hT, hR, ← hS])`. Use `⟨c, fun z => ?_⟩` and prove the remaining obligations.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => rw [hpure, hc, TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, smul_add]`.
-/
private theorem schur_ext {G Γ V B : Type} [Group G] [Group Γ] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup B] [Module ℂ B] [Nontrivial B] (σ : Representation ℂ G V)
    (m : Representation ℂ Γ B) (hσ : Schur σ) (hm : Schur m) : Schur (extTensor σ m) := by
  intro T hT
  obtain ⟨b₀, hb₀⟩ := exists_ne (0 : B)
  obtain ⟨β, hβ⟩ : ∃ β : Module.Dual ℂ B, β b₀ = 1 := by
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ B, φ b₀ ≠ 0 := by
      by_contra! h
      exact hb₀ ((Module.forall_dual_apply_eq_zero_iff ℂ b₀).1 h)
    exact ⟨(φ b₀)⁻¹ • φ, by simp [hφ]⟩
  let L : Module.Dual ℂ V → (V ⊗[ℂ] B →ₗ[ℂ] B) := fun φ =>
    (TensorProduct.lid ℂ B).toLinearMap ∘ₗ LinearMap.rTensor B φ
  let R : V ⊗[ℂ] B →ₗ[ℂ] V := (TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V β
  have hLt : ∀ φ x y, L φ (x ⊗ₜ y) = φ x • y := fun φ x y => by simp [L]
  have hRt : ∀ x y, R (x ⊗ₜ y) = β y • x := fun x y => by simp [R]
  have hL : ∀ φ c z, L φ (extTensor σ m (1, c) z) = m c (L φ z) := by
    intro φ c z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hLt]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hR : ∀ g z, R (extTensor σ m (g, 1) z) = σ g (R z) := by
    intro g z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hRt]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hLR : ∀ (φ : Module.Dual ℂ V) z, φ (R z) = β (L φ z) := by
    intro φ z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hLt, hRt, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  let S : V →ₗ[ℂ] V := R ∘ₗ T ∘ₗ (TensorProduct.mk ℂ V B).flip b₀
  have hS : ∀ v, S v = R (T (v ⊗ₜ b₀)) := fun v => rfl
  have hpure : ∀ v b, T (v ⊗ₜ b) = S v ⊗ₜ b := by
    intro v b
    rw [← sub_eq_zero]
    apply tens_sep
    intro φ
    obtain ⟨c, hc⟩ := hm (L φ ∘ₗ T ∘ₗ TensorProduct.mk ℂ V B v) (by
      intro c y
      have h1 : v ⊗ₜ[ℂ] m c y = extTensor σ m (1, c) (v ⊗ₜ y) := by simp
      simp only [LinearMap.comp_apply, TensorProduct.mk_apply]
      rw [h1, hT, hL])
    have hc' : ∀ y, L φ (T (v ⊗ₜ y)) = c • y := hc
    have hφS : φ (S v) = c := by
      rw [hS, hLR, hc', map_smul, hβ, smul_eq_mul, mul_one]
    change L φ (T (v ⊗ₜ b) - S v ⊗ₜ b) = 0
    rw [map_sub, hc', hLt, hφS, sub_self]
  obtain ⟨c, hc⟩ := hσ S (by
    intro g v
    have h1 : σ g v ⊗ₜ[ℂ] b₀ = extTensor σ m (g, 1) (v ⊗ₜ b₀) := by simp
    rw [hS, h1, hT, hR, ← hS])
  refine ⟨c, fun z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [hpure, hc, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/- English proof (translation)
Introduce `G _ Γ _ V _ _ B _ _ σ m hσ hs hm`. Use `haveI : Nontrivial B := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hm`. Establish `hsc : ∀ A : Module.End ℂ V, (∀ g, A * σ g = σ g * A) → ∃ c : ℂ, A = c • 1`. Introduce `A hA`. Take `⟨c, hc⟩` from `hs A fun g v => congrArg (fun F : Module.End ℂ V => F v) (hA g)`.

Conclude with `⟨c, LinearMap.ext fun v => by simpa using hc v⟩`. Use `⟨?_, schur_ext σ m hs⟩` and prove the remaining obligations. Establish `h1 : IsSimpleOrder (Subrepresentation (extTensor m σ))` using `(GlobalTheory.ExtTensorSub.orderIso m σ hσ hsc).isSimpleOrder_iff.1 hm`. Conclude with `(swapIso σ m).isSimpleOrder_iff.2 h1`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.tensSimple :
    ∀ {G : Type} [Group G] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] {B : Type} [AddCommGroup B] [Module ℂ B] (σ : Representation ℂ G V) (m : Representation ℂ Γ B), σ.IsIrreducible → Schur σ → m.IsIrreducible →
      (extTensor σ m).IsIrreducible ∧ (Schur m → Schur (extTensor σ m)) := by
  intro G _ Γ _ V _ _ B _ _ σ m hσ hs hm
  haveI : Nontrivial B := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hm
  have hsc : ∀ A : Module.End ℂ V, (∀ g, A * σ g = σ g * A) → ∃ c : ℂ, A = c • 1 := by
    intro A hA
    obtain ⟨c, hc⟩ := hs A fun g v => congrArg (fun F : Module.End ℂ V => F v) (hA g)
    exact ⟨c, LinearMap.ext fun v => by simpa using hc v⟩
  refine ⟨?_, schur_ext σ m hs⟩
  have h1 : IsSimpleOrder (Subrepresentation (extTensor m σ)) :=
    (GlobalTheory.ExtTensorSub.orderIso m σ hσ hsc).isSimpleOrder_iff.1 hm
  exact (swapIso σ m).isSimpleOrder_iff.2 h1
