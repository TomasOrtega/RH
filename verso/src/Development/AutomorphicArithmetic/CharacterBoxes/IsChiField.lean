import Development.AutomorphicArithmetic.CharacterBoxes.TwistForm

open Formalism.HC UpperTheory.Top

/- English proof (authored)
Use the host cyclotomic embedding and its primitive root of order equal to the product of the three modulus factors. The tower and character moduli divide this product by the host assumptions and the kernel criterion. If an automorphism sends the primitive root to its ath power, preservation of primitivity implies that a is coprime to the order. Reduce a modulo the order to obtain the corresponding unit, which acts on the root by the same power. The host reciprocity formula identifies the induced action on the embedded host with the associated Artin element. The embedding is injective, so this action fixes the host pointwise exactly when the Artin element is trivial. Substitute the prescribed description of its kernel.
-/
theorem UpperTheory.Top.isChiField :
    ∀ (ψ : PChar) (φ : Frame) (H : HostRaw φ), KerChi ψ H → IsChiField ψ φ.e H.q H.d H.E := by
  intro ψ φ H h
  obtain ⟨hψ, hart⟩ := h
  have hyp := H.hyp
  unfold Formalism.FrobeniusOrbits.HostHyp at hyp
  have hq := hyp.1.pos
  have hd := hyp.2.1.pos
  have hQS := H.QS_pos
  have hNpos : 0 < H.QS * H.q * H.d := Nat.mul_pos (Nat.mul_pos hQS hq) hd
  haveI : NeZero (H.QS * H.q * H.d) := ⟨hNpos.ne'⟩
  have hζ := H.cycZeta_prim
  refine ⟨H.QS * H.q * H.d, inferInstance, H.cycEmb, H.cycZeta, ?_, ?_, ?_, ?_, hζ, ?_⟩
  · exact dvd_trans H.tower_dvd (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _))
  · exact dvd_trans hψ (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _))
  · exact dvd_trans (dvd_mul_left _ _) (dvd_mul_right _ _)
  · exact dvd_mul_left _ _
  · intro τ a hτ
    have hprim : IsPrimitiveRoot (H.cycZeta ^ a) (H.QS * H.q * H.d) := by
      rw [← hτ]
      exact hζ.map_of_injective τ.injective
    have hcop : a.Coprime (H.QS * H.q * H.d) := (hζ.pow_iff_coprime hNpos a).mp hprim
    have hcop' : a.Coprime H.condN := hcop
    rw [← hart a hcop']
    set u := ZMod.unitOfCoprime a hcop' with hu
    have hτu : τ H.cycZeta = H.cycZeta ^ (u : ZMod (H.QS * H.q * H.d)).val := by
      rw [hτ]
      have hv : (u : ZMod (H.QS * H.q * H.d)).val = a % (H.QS * H.q * H.d) := by
        rw [hu, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      rw [hv]
      conv_lhs => rw [← Nat.mod_add_div a (H.QS * H.q * H.d)]
      rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    have hspec := H.art_spec u τ hτu
    constructor
    · intro hfix
      have hg : H.gal.symm (H.art u) = 1 := by
        ext x
        apply H.cycEmb.injective
        exact (hspec x).trans (hfix x)
      have h1 := congrArg H.gal hg
      rw [MulEquiv.apply_symm_apply, map_one] at h1
      exact h1
    · intro h1 x
      have h2 := hspec x
      rw [h1, map_one] at h2
      rw [← h2]
      rfl
