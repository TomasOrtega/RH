import Mathlib
import GroundTheory.TateCohomology.AugmentationSES
import GroundTheory.TateCohomology.CohTrivialBasic
set_option maxSynthPendingDepth 1

open CategoryTheory groupCohomology Rep

namespace GroundTheory.GroupCoh

universe u

variable (k G : Type u) [CommRing k] [Group G]

noncomputable def augHom : Rep.leftRegular k G ⟶ Rep.trivial k G k :=
  Rep.ofHom ⟨augmentation k G, fun g => LinearMap.ext fun x => by
    change augmentation k G ((Rep.leftRegular k G).ρ g x) = augmentation k G x
    exact augmentation_ρ g x⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem augHom_apply (x : Rep.leftRegular k G) :
    (augHom k G).hom x = augmentation k G x := rfl

/- English proof (translation)
Use extensionality with `x`. Conclude with `LinearMap.mem_ker.1 x.2`.
-/
theorem augIdealι_augHom : augIdealι k G ≫ augHom k G = 0 := by
  ext x
  exact LinearMap.mem_ker.1 x.2

noncomputable def augTrivSES : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (augIdealι k G) (augHom k G) (augIdealι_augHom k G)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem augTrivSES_X₁ : (augTrivSES k G).X₁ = augIdeal k G := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem augTrivSES_X₂ : (augTrivSES k G).X₂ = Rep.leftRegular k G := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem augTrivSES_X₃ : (augTrivSES k G).X₃ = Rep.trivial k G k := rfl

/- English proof (translation)
Use `shortExact_of_linear (fun a b h => Subtype.ext h) (fun r => ⟨MonoidAlgebra.single (1 : G) (show k from r), ?_⟩) (fun y hy => ⟨⟨y, LinearMap.mem_ker.2 hy⟩, rfl⟩)` and prove the remaining obligations. Conclude with `augmentation_single (k := k) (1 : G) (show k from r)`.
-/
theorem augTrivSES_shortExact : (augTrivSES k G).ShortExact := by
  refine shortExact_of_linear (fun a b h => Subtype.ext h)
    (fun r => ⟨MonoidAlgebra.single (1 : G) (show k from r), ?_⟩)
    (fun y hy => ⟨⟨y, LinearMap.mem_ker.2 hy⟩, rfl⟩)
  exact augmentation_single (k := k) (1 : G) (show k from r)

/- English proof (translation)
Use `cohTrivial_of_sum_eq _ coeffOneProj fun m => ?_` and prove the remaining obligations. Proceed by induction on `m using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]`. Consider the case `single h c`.

Rewrite using `[Fintype.sum_eq_single h]`. Simplify using `[coeffOneProj_apply]`. Introduce `g hg`. Establish `: g⁻¹ * h ≠ 1` using `fun e => hg (inv_mul_eq_one.mp e)`. Simplify using `[coeffOneProj_apply, this]`.
-/
theorem cohTrivial_leftRegular [Fintype G] : CohTrivial (Rep.leftRegular k G) := by
  refine cohTrivial_of_sum_eq _ coeffOneProj fun m => ?_
  induction m using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]
  | single h c =>
    rw [Fintype.sum_eq_single h]
    · simp [coeffOneProj_apply]
    · intro g hg
      have : g⁻¹ * h ≠ 1 := fun e => hg (inv_mul_eq_one.mp e)
      simp [coeffOneProj_apply, this]

variable {k G}

noncomputable def augIdealSubOne (g : G) : augIdeal k G :=
  ⟨MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1, by
    rw [LinearMap.mem_ker, map_sub, augmentation_single, augmentation_single, sub_self]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem augIdealSubOne_val (g : G) :
    ((augIdealSubOne g : augIdeal k G) : MonoidAlgebra k G) =
      MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1 := rfl

section Cocycle

variable {A : Rep.{u} k G}

noncomputable def cocycleLinear (f : cocycles₁ A) : MonoidAlgebra k G →ₗ[k] A.V :=
  Finsupp.linearCombination k (fun g => f g) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

/- English proof (translation)
Simplify using `[cocycleLinear]`.
-/
theorem cocycleLinear_single (f : cocycles₁ A) (g : G) (r : k) :
    cocycleLinear f (MonoidAlgebra.single g r) = r • f g := by
  simp [cocycleLinear]

/- English proof (translation)
Proceed by induction on `x using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, add_smul]`. Normalize the expressions using the abelian group laws. Consider the case `single g r`.

Establish `hf : f (s * g) = A.ρ s (f g) + f s` using `(mem_cocycles₁_iff _).1 f.2 s g`. Rewrite using `[Representation.ofMulAction_single, smul_eq_mul, cocycleLinear_single, cocycleLinear_single, augmentation_single, map_smul, hf, smul_add]`.
-/
theorem cocycleLinear_ρ (f : cocycles₁ A) (s : G) (x : MonoidAlgebra k G) :
    cocycleLinear f ((Rep.leftRegular k G).ρ s x) =
      A.ρ s (cocycleLinear f x) + augmentation k G x • f s := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_smul]; abel
  | single g r =>
    have hf : f (s * g) = A.ρ s (f g) + f s := (mem_cocycles₁_iff _).1 f.2 s g
    rw [Representation.ofMulAction_single, smul_eq_mul, cocycleLinear_single, cocycleLinear_single,
      augmentation_single, map_smul, hf, smul_add]

noncomputable def cocycleHom (f : cocycles₁ A) : augIdeal k G ⟶ A :=
  Rep.ofHom ⟨cocycleLinear f ∘ₗ (LinearMap.ker (augmentation k G)).subtype, fun s =>
    LinearMap.ext fun x => by
      have hx : augmentation k G x.1 = 0 := LinearMap.mem_ker.1 x.2
      change cocycleLinear f ((Rep.leftRegular k G).ρ s x.1) = A.ρ s (cocycleLinear f x.1)
      rw [cocycleLinear_ρ, hx, zero_smul, add_zero]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cocycleHom_apply (f : cocycles₁ A) (x : augIdeal k G) :
    (cocycleHom f).hom x = cocycleLinear f x.1 := rfl

/- English proof (translation)
Rewrite using `[cocycleHom_apply, augIdealSubOne_val, map_sub, cocycleLinear_single, cocycleLinear_single, cocycles₁_map_one, smul_zero, sub_zero, one_smul]`.
-/
theorem cocycleHom_augIdealSubOne (f : cocycles₁ A) (g : G) :
    (cocycleHom f).hom (augIdealSubOne g) = f g := by
  rw [cocycleHom_apply, augIdealSubOne_val, map_sub, cocycleLinear_single, cocycleLinear_single,
    cocycles₁_map_one, smul_zero, sub_zero, one_smul]

end Cocycle

section Restrict

variable (k) {H : Type u} [Group H] (φ : H →* G)

noncomputable def augCocycle : cocycles₁ (Rep.res φ (augIdeal k G)) :=
  ⟨fun h => augIdealSubOne (φ h), (mem_cocycles₁_iff _).2 fun a b => by
    apply Subtype.ext
    change MonoidAlgebra.single (φ (a * b)) (1 : k) - MonoidAlgebra.single 1 1 =
      (Rep.leftRegular k G).ρ (φ a) (MonoidAlgebra.single (φ b) 1 - MonoidAlgebra.single 1 1) +
        (MonoidAlgebra.single (φ a) 1 - MonoidAlgebra.single 1 1)
    rw [map_sub, Representation.ofMulAction_single, Representation.ofMulAction_single, smul_eq_mul,
      smul_eq_mul, mul_one, map_mul]
    abel⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem augCocycle_apply (h : H) : augCocycle k φ h = augIdealSubOne (φ h) := rfl

/- English proof (translation)
The claim follows from `(shortExact_res φ).2 (augTrivSES_shortExact k G)`.
-/
theorem augTrivSES_res_shortExact : ((augTrivSES k G).map (resFunctor φ)).ShortExact :=
  (shortExact_res φ).2 (augTrivSES_shortExact k G)

def oneInvariant : (Rep.res φ (Rep.trivial k G k)).ρ.invariants :=
  ⟨(1 : k), fun _ => rfl⟩

/- English proof (translation)
Establish `hx : ((augTrivSES k G).map (resFunctor φ)).f.hom ∘ (fun h => augIdealSubOne (φ h)) = d₀₁ ((augTrivSES k G).map (resFunctor φ)).X₂ (MonoidAlgebra.single (1 : G) (1 : k))`. Use function extensionality and compare the values at `h`. Express the relevant statement in the definitionally equal form `MonoidAlgebra.single (φ h) (1 : k) - MonoidAlgebra.single 1 1 = (Rep.leftRegular k G).ρ (φ h) (MonoidAlgebra.single 1 1) - MonoidAlgebra.single 1 1`. Rewrite using `[Representation.ofMulAction_single, smul_eq_mul, mul_one]`. Conclude with `δ₀_apply (augTrivSES_res_shortExact k φ) (oneInvariant k φ) (MonoidAlgebra.single (1 : G) (1 : k)) (by exact augmentation_single (k := k) (1 : G) (1 : k)) _ hx`.
-/
theorem δ₀_augTrivSES_res :
    δ (augTrivSES_res_shortExact k φ) 0 1 rfl ((H0Iso _).inv (oneInvariant k φ)) =
      H1π _ (augCocycle k φ) := by
  have hx : ((augTrivSES k G).map (resFunctor φ)).f.hom ∘ (fun h => augIdealSubOne (φ h)) =
      d₀₁ ((augTrivSES k G).map (resFunctor φ)).X₂ (MonoidAlgebra.single (1 : G) (1 : k)) := by
    funext h
    change MonoidAlgebra.single (φ h) (1 : k) - MonoidAlgebra.single 1 1 =
      (Rep.leftRegular k G).ρ (φ h) (MonoidAlgebra.single 1 1) - MonoidAlgebra.single 1 1
    rw [Representation.ofMulAction_single, smul_eq_mul, mul_one]
  exact δ₀_apply (augTrivSES_res_shortExact k φ) (oneInvariant k φ)
    (MonoidAlgebra.single (1 : G) (1 : k)) (by exact augmentation_single (k := k) (1 : G) (1 : k)) _ hx

end Restrict

end GroundTheory.GroupCoh
