import Mathlib

namespace GroundTheory.ProfCoh

open CategoryTheory

universe w u v

variable {k : Type u} {G : Type v} [CommRing k] [Group G]

def stabilizer {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply]

@[simp]
/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_stabilizer {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (v : V) (g : G) : g ∈ stabilizer ρ v ↔ ρ g v = v :=
  Iff.rfl

variable [TopologicalSpace G]

class IsDiscreteRep (A : Rep.{w} k G) : Prop where
  isOpen_stabilizer : ∀ a : A, IsOpen (stabilizer A.ρ a : Set G)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isOpen_stabilizer (A : Rep.{w} k G) [IsDiscreteRep A] (a : A) :
    IsOpen (stabilizer A.ρ a : Set G) :=
  IsDiscreteRep.isOpen_stabilizer a

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem isDiscreteRep_iff (A : Rep.{w} k G) :
    IsDiscreteRep A ↔ ∀ a : A, IsOpen (stabilizer A.ρ a : Set G) :=
  ⟨fun h => h.isOpen_stabilizer, fun h => ⟨h⟩⟩

variable (k G) in

def isDiscreteRep : ObjectProperty (Rep.{w} k G) := fun A => IsDiscreteRep A

@[simp]
/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem isDiscreteRep_apply (A : Rep.{w} k G) : isDiscreteRep k G A ↔ IsDiscreteRep A :=
  Iff.rfl

variable (k G) in

abbrev DiscreteRep := (isDiscreteRep.{w} k G).FullSubcategory

instance (A : DiscreteRep.{w} k G) : IsDiscreteRep A.obj := A.property

end GroundTheory.ProfCoh
