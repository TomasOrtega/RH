import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V.Kum

namespace UpperTheory.V.Stick

section Act

variable (K : Type) [Field K] [NumberField K]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem clMap_refl (c : ClassGroup (𝓞 K)) : clMap (RingEquiv.refl K) c = c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0]
  congr 1
  exact Subtype.ext (Ideal.map_id I.1)

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem clMap_trans {K K' K'' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K'']
    (τ : K ≃+* K') (τ' : K' ≃+* K'') (c : ClassGroup (𝓞 K)) : clMap (τ.trans τ') c = clMap τ' (clMap τ c) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0, class_map_mk0, class_map_mk0]
  congr 1
  exact Subtype.ext (Ideal.map_map (I := I.1) (RingOfIntegers.mapRingEquiv τ).toRingHom
    (RingOfIntegers.mapRingEquiv τ').toRingHom).symm

def clRep : Representation ℤ Gal(K/ℚ) (Additive (ClassGroup (𝓞 K))) where
  toFun σ := (MonoidHom.toAdditive (clMap σ.toRingEquiv)).toIntLinearMap
  map_one' := LinearMap.ext fun c => congrArg Additive.ofMul (clMap_refl K c.toMul)
  map_mul' σ τ := LinearMap.ext fun c => congrArg Additive.ofMul (clMap_trans τ.toRingEquiv σ.toRingEquiv c.toMul)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem clRep_apply (σ : Gal(K/ℚ)) (c : ClassGroup (𝓞 K)) :
    clRep K σ (Additive.ofMul c) = Additive.ofMul (clMap σ.toRingEquiv c) := rfl

def toQ (G : Type) [Monoid G] : MonoidAlgebra ℤ G →+* MonoidAlgebra ℚ G :=
  MonoidAlgebra.mapRingHom G (Int.castRingHom ℚ)

end Act

variable (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]

def sg : (ZMod M)ˣ ≃* Gal(K/ℚ) := (IsCyclotomicExtension.Rat.galEquivZMod M K).symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem sg_apply (b : (ZMod M)ˣ) {x : K} (hx : x ^ M = 1) : sg M K b x = x ^ (b : ZMod M).val := by
  rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq M K _ hx, sg, MulEquiv.apply_symm_apply]

def sgO (b : (ZMod M)ˣ) : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv (sg M K b).toRingEquiv

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem sgO_apply (b : (ZMod M)ˣ) {x : 𝓞 K} (hx : x ^ M = 1) : sgO M K b x = x ^ (b : ZMod M).val := by
  apply Subtype.ext
  exact sg_apply M K b (x := x.1) (congrArg Subtype.val hx)

def theta : MonoidAlgebra ℚ Gal(K/ℚ) :=
  ∑ b : (ZMod M)ˣ, MonoidAlgebra.single (sg M K b)⁻¹ ((((b : ZMod M).val : ℕ) : ℚ) / M)

def conjI (P : Ideal (𝓞 K)) (b : (ZMod M)ˣ) : Ideal (𝓞 K) := P.comap (sgO M K b)

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_conjI (P : Ideal (𝓞 K)) (b : (ZMod M)ˣ) (x : 𝓞 K) : x ∈ conjI M K P b ↔ sgO M K b x ∈ P := Iff.rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem idMap_inv (I : nonZeroDivisors (Ideal (𝓞 K))) (b : (ZMod M)ˣ) :
    (idMap (sg M K b)⁻¹.toRingEquiv I).1 = conjI M K I.1 b :=
  Ideal.map_symm (sgO M K b)

omit [NeZero M] in

def carry (a b : ZMod M) : ℕ := if M ≤ a.val + b.val then 1 else 0

def StickelbergerAt : Prop :=
  ∀ β γ : MonoidAlgebra ℤ Gal(K/ℚ), toQ _ γ = toQ _ β * theta M K → (clRep K).asAlgebraHom γ = 0

end UpperTheory.V.Stick

end
