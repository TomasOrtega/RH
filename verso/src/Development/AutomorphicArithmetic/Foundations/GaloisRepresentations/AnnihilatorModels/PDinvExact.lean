import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul u b => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
private lemma UpperTheory.Gal.crystallineComparison.map_id_eq_rTensor {F B L U V : Type} [Field F] [AddCommGroup B] [Module F B]
    [Field L] [Algebra F L] [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] (f : U →ₗ[L] V) (x : U ⊗[F] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) x = LinearMap.rTensor B (f.restrictScalars F) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul u b => simp [hf g u]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
private lemma UpperTheory.Gal.crystallineComparison.inter_map {F G B L U V : Type} [Field F] [Group G] [AddCommGroup B] [Module F B]
    (σ : G → End F B) [Field L] [Algebra F L] [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    {ρ : Representation L G U} {ρ' : Representation L G V} {f : U →ₗ[L] V} (hf : Inter ρ ρ' f) (g : G) (x : U ⊗[F] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) (AlgebraTensorModule.map (ρ g) (σ g) x) =
      AlgebraTensorModule.map (ρ' g) (σ g) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u b => simp [hf g u]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Introduce `F G B _ _ _ _ σ L _ _ U V W _ _ _ _ _ _ _ _ _ _ _ _ ρU ρV ρW i p hi hp hinj hex hfin`. Establish `hI : Function.Injective (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B))`. Establish `h` using `Module.Flat.rTensor_preserves_injective_linearMap (M := B) (i.restrictScalars F) hinj`. Introduce `x y hxy`. Apply `h` to reduce the goal to its premises.

Rewrite using `[← map_id_eq_rTensor, ← map_id_eq_rTensor]`. Conclude with `hxy`. Establish `hE : Function.Exact (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B)) (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B))`. Establish `h` using `Module.Flat.rTensor_exact (f := i.restrictScalars F) (g := p.restrictScalars F) B hex`. Establish `e1 : (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B) : U ⊗[F] B → V ⊗[F] B) = LinearMap.rTensor B (i.restrictScalars F)` using `funext (map_id_eq_rTensor i)`.

Establish `e2 : (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) : V ⊗[F] B → W ⊗[F] B) = LinearMap.rTensor B (p.restrictScalars F)` using `funext (map_id_eq_rTensor p)`. Rewrite using `[e1, e2]`. Conclude with `h`. Establish `key : (Dinv σ ρU).map (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B)) = Dinv σ ρV ⊓ LinearMap.ker (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B))`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(mem_Dinv σ).2 fun g => ?_` and prove the remaining obligations. Rewrite using `[← inter_map σ hi, (mem_Dinv σ).1 hx g]`.

Conclude with `(hE _).2 ⟨x, rfl⟩`. Introduce and unpack `⟨hy, hk⟩`. Take `⟨x, rfl⟩` from `(hE y).1 hk`. Use `⟨x, (mem_Dinv σ).2 fun g => hI ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[inter_map σ hi, (mem_Dinv σ).1 hy g]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `(mem_Dinv σ).2 fun g => ?_` and prove the remaining obligations. Rewrite using `[← inter_map σ hp, (mem_Dinv σ).1 hx g]`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker ((AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)).domRestrict (Dinv σ ρV))`.

Rewrite `h1` using `[LinearMap.range_domRestrict, LinearMap.ker_domRestrict]`. Establish `h2 : finrank L (Submodule.comap (Dinv σ ρV).subtype (LinearMap.ker (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)))) = finrank L (Dinv σ ρU)`. Rewrite using `[← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, ← key]`. Conclude with `(LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hI _)).symm`. Rewrite `h1` using `[h2]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.Gal.crystallineComparison.dinvExact_of :
    DinvExact := by
  intro F G B _ _ _ _ σ L _ _ U V W _ _ _ _ _ _ _ _ _ _ _ _ ρU ρV ρW i p hi hp hinj hex hfin
  have hI : Function.Injective (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B)) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := B) (i.restrictScalars F) hinj
    intro x y hxy
    apply h
    rw [← map_id_eq_rTensor, ← map_id_eq_rTensor]
    exact hxy
  have hE : Function.Exact (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B))
      (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) := by
    have h := Module.Flat.rTensor_exact (f := i.restrictScalars F) (g := p.restrictScalars F) B hex
    have e1 : (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B) : U ⊗[F] B → V ⊗[F] B) =
        LinearMap.rTensor B (i.restrictScalars F) := funext (map_id_eq_rTensor i)
    have e2 : (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) : V ⊗[F] B → W ⊗[F] B) =
        LinearMap.rTensor B (p.restrictScalars F) := funext (map_id_eq_rTensor p)
    rw [e1, e2]
    exact h
  have key : (Dinv σ ρU).map (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B)) =
      Dinv σ ρV ⊓ LinearMap.ker (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · refine (mem_Dinv σ).2 fun g => ?_
        rw [← inter_map σ hi, (mem_Dinv σ).1 hx g]
      · exact (hE _).2 ⟨x, rfl⟩
    · rintro ⟨hy, hk⟩
      obtain ⟨x, rfl⟩ := (hE y).1 hk
      refine ⟨x, (mem_Dinv σ).2 fun g => hI ?_, rfl⟩
      rw [inter_map σ hi, (mem_Dinv σ).1 hy g]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine (mem_Dinv σ).2 fun g => ?_
    rw [← inter_map σ hp, (mem_Dinv σ).1 hx g]
  · have h1 := LinearMap.finrank_range_add_finrank_ker
      ((AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)).domRestrict (Dinv σ ρV))
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
    have h2 : finrank L (Submodule.comap (Dinv σ ρV).subtype
        (LinearMap.ker (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)))) =
        finrank L (Dinv σ ρU) := by
      rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, ← key]
      exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hI _)).symm
    rw [h2] at h1
    omega
