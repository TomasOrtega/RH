import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar GlobalTheory.DblEval
open GlobalTheory.Doubling (absE)

open scoped Classical
attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

namespace GlobalTheory.TensorGlue

/- English proof (translation)
Establish `hk : LinearMap.ker P ≤ LinearMap.ker Q` using `fun t ht => h t ht`. Take `⟨H, hH⟩` from `LinearMap.exists_extend (((LinearMap.ker P).liftQ Q hk) ∘ₗ (P.quotKerEquivRange.symm : LinearMap.range P →ₗ[ℂ] _))`. Use `⟨H, fun t => ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun hH ⟨P t, LinearMap.mem_range_self P t⟩` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply] at this`.

Conclude with `this`.
-/
theorem exists_factor {U M N : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (P : U →ₗ[ℂ] M) (Q : U →ₗ[ℂ] N) (h : ∀ t, P t = 0 → Q t = 0) :
    ∃ H : M →ₗ[ℂ] N, ∀ t, H (P t) = Q t := by
  have hk : LinearMap.ker P ≤ LinearMap.ker Q := fun t ht => h t ht
  obtain ⟨H, hH⟩ := LinearMap.exists_extend
    (((LinearMap.ker P).liftQ Q hk) ∘ₗ (P.quotKerEquivRange.symm : LinearMap.range P →ₗ[ℂ] _))
  refine ⟨H, fun t => ?_⟩
  have := LinearMap.congr_fun hH ⟨P t, LinearMap.mem_range_self P t⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply] at this
  exact this

/- English proof (translation)
Set `P : V ⊗[ℂ] (Y → ℂ) →ₗ[ℂ] (Z → ℂ)` to `TensorProduct.lift (LinearMap.mk₂ ℂ (fun f g => fun z => e f (p z) * g (q z)) (by intros; ext; simp [add_mul]) (by intros; ext; simp [mul_assoc]) (by intros; ext; simp [mul_add]) (by intros; ext; simp [mul_left_comm]))`. Establish `hP : ∀ f g, P (f ⊗ₜ g) = fun z => e f (p z) * g (q z)` using `fun _ _ => rfl`. Set `L : Y → V ⊗[ℂ] (Y → ℂ) →ₗ[ℂ] V` to `fun y => TensorProduct.lift (LinearMap.mk₂ ℂ (fun f g => g y • f) (by intros; simp) (by intros; rw [smul_comm]) (by intros; simp [add_smul]) (by intros; simp [mul_smul]))`. Establish `hL : ∀ y f g, L y (f ⊗ₜ g) = g y • f` using `fun _ _ _ => rfl`. Set `R : X → V ⊗[ℂ] (Y → ℂ) →ₗ[ℂ] (Y → ℂ)` to `fun x => TensorProduct.lift (LinearMap.mk₂ ℂ (fun f g => e (A f) x • g) (by intros; simp [add_smul]) (by intros; simp [mul_smul]) (by intros; simp) (by intros; rw [smul_comm]))`.

Establish `hR : ∀ x f g, R x (f ⊗ₜ g) = e (A f) x • g` using `fun _ _ _ => rfl`. Establish `h1 : ∀ t z, P t z = e (L (q z) t) (p z)`. Introduce `t z`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul f g => simp [hP, hL, mul_comm]`. Consider the case `add a b ha hb => simp [ha, hb]`. Establish `h2 : ∀ t x y, R x t y = e (A (L y t)) x`. Introduce `t x y`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul f g => simp [hR, hL, mul_comm]`. Consider the case `add a b ha hb => simp [ha, hb]`. Establish `h3 : ∀ t z, P (TensorProduct.map A B t) z = B (R (p z) t) (q z)`. Introduce `t z`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul f g => simp [hR, hP]`. Consider the case `add a b ha hb => simp [ha, hb]`. Take `⟨H, hH⟩` from `exists_factor P (P ∘ₗ TensorProduct.map A B) (by`.

Introduce `t ht`. Establish `hLt : ∀ y, L y t = 0`. Introduce `y`. Apply `he` to reduce the goal to its premises. Use extensionality with `x`.

Take `⟨z, rfl, rfl⟩` from `hpq x y`. Rewrite using `[← h1, ht]`. Simplify using the standard rewrite rules. Establish `hRt : ∀ x, R x t = 0`. Introduce `x`.

Use extensionality with `y`. Rewrite using `[h2, hLt]`. Simplify using the standard rewrite rules. Use extensionality with `z`. Rewrite using `[LinearMap.comp_apply, h3, hRt]`.

Use the proof step `simp)`. Use `⟨H, fun f g => ?_⟩` and prove the remaining obligations. Use `hH (f ⊗ₜ g)` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, TensorProduct.map_tmul, hP, hP]`. Then use the resulting hypothesis.
-/
theorem exists_glue {V X Y Z : Type*} [AddCommGroup V] [Module ℂ V] (e : V →ₗ[ℂ] (X → ℂ))
    (he : Function.Injective e) (p : Z → X) (q : Z → Y) (hpq : ∀ x y, ∃ z, p z = x ∧ q z = y)
    (A : V →ₗ[ℂ] V) (B : (Y → ℂ) →ₗ[ℂ] (Y → ℂ)) :
    ∃ H : (Z → ℂ) →ₗ[ℂ] (Z → ℂ), ∀ (f : V) (g : Y → ℂ),
      H (fun z => e f (p z) * g (q z)) = fun z => e (A f) (p z) * B g (q z) := by
  let P : V ⊗[ℂ] (Y → ℂ) →ₗ[ℂ] (Z → ℂ) := TensorProduct.lift
    (LinearMap.mk₂ ℂ (fun f g => fun z => e f (p z) * g (q z))
      (by intros; ext; simp [add_mul]) (by intros; ext; simp [mul_assoc])
      (by intros; ext; simp [mul_add]) (by intros; ext; simp [mul_left_comm]))
  have hP : ∀ f g, P (f ⊗ₜ g) = fun z => e f (p z) * g (q z) := fun _ _ => rfl
  let L : Y → V ⊗[ℂ] (Y → ℂ) →ₗ[ℂ] V := fun y => TensorProduct.lift
    (LinearMap.mk₂ ℂ (fun f g => g y • f)
      (by intros; simp) (by intros; rw [smul_comm])
      (by intros; simp [add_smul]) (by intros; simp [mul_smul]))
  have hL : ∀ y f g, L y (f ⊗ₜ g) = g y • f := fun _ _ _ => rfl
  let R : X → V ⊗[ℂ] (Y → ℂ) →ₗ[ℂ] (Y → ℂ) := fun x => TensorProduct.lift
    (LinearMap.mk₂ ℂ (fun f g => e (A f) x • g)
      (by intros; simp [add_smul]) (by intros; simp [mul_smul])
      (by intros; simp) (by intros; rw [smul_comm]))
  have hR : ∀ x f g, R x (f ⊗ₜ g) = e (A f) x • g := fun _ _ _ => rfl
  have h1 : ∀ t z, P t z = e (L (q z) t) (p z) := by
    intro t z
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp [hP, hL, mul_comm]
    | add a b ha hb => simp [ha, hb]
  have h2 : ∀ t x y, R x t y = e (A (L y t)) x := by
    intro t x y
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp [hR, hL, mul_comm]
    | add a b ha hb => simp [ha, hb]
  have h3 : ∀ t z, P (TensorProduct.map A B t) z = B (R (p z) t) (q z) := by
    intro t z
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp [hR, hP]
    | add a b ha hb => simp [ha, hb]
  obtain ⟨H, hH⟩ := exists_factor P (P ∘ₗ TensorProduct.map A B) (by
    intro t ht
    have hLt : ∀ y, L y t = 0 := by
      intro y
      apply he
      ext x
      obtain ⟨z, rfl, rfl⟩ := hpq x y
      rw [← h1, ht]; simp
    have hRt : ∀ x, R x t = 0 := by
      intro x
      ext y
      rw [h2, hLt]; simp
    ext z
    rw [LinearMap.comp_apply, h3, hRt]; simp)
  refine ⟨H, fun f g => ?_⟩
  have := hH (f ⊗ₜ g)
  rwa [LinearMap.comp_apply, TensorProduct.map_tmul, hP, hP] at this

/- English proof (translation)
Introduce `F _ _ ι _ A B`. Set `e : SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] ((ι → mixedEmbedding.mixedSpace F) → ℂ)` to `{ toFun := fun f => f map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Conclude with `exists_glue (Z := ι → AF F) e DFunLike.coe_injective (fun x i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) (fun x i => (x i).2) (fun x y => ⟨fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i),`. Use function extensionality and compare the values at `fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x i), rfl⟩) A B`.
-/
theorem exists_pure_operator : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    (A : SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ)
    (B : ((ι → FiniteAdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((ι → FiniteAdeleRing (𝓞 F) F) → ℂ)),
    ∃ H : ((ι → AF F) → ℂ) →ₗ[ℂ] ((ι → AF F) → ℂ),
      ∀ (f : SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ) (g : (ι → FiniteAdeleRing (𝓞 F) F) → ℂ),
        H (pureA F f g) = pureA F (A f) (B g) := by
  intro F _ _ ι _ A B
  let e : SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] ((ι → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact exists_glue (Z := ι → AF F) e DFunLike.coe_injective
    (fun x i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) (fun x i => (x i).2)
    (fun x y => ⟨fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i),
      funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x i), rfl⟩) A B

end GlobalTheory.TensorGlue
