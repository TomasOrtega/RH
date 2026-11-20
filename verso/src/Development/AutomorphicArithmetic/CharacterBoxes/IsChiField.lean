import Development.AutomorphicArithmetic.CharacterBoxes.TwistForm

open Formalism.HC UpperTheory.Top

/- English proof (translation)
Introduce `ψ φ H h`. Take `⟨hψ, hart⟩` from `h`. Establish `hyp` using `H.hyp`. Unfold `Formalism.FrobeniusOrbits.HostHyp at hyp`. Establish `hq` using `hyp.1.pos`.

Establish `hd` using `hyp.2.1.pos`. Establish `hQS` using `H.QS_pos`. Establish `hNpos : 0 < H.QS * H.q * H.d` using `Nat.mul_pos (Nat.mul_pos hQS hq) hd`. Use `haveI : NeZero (H.QS * H.q * H.d) := ⟨hNpos.ne'⟩`. Establish `hζ` using `H.cycZeta_prim`.

Use `⟨H.QS * H.q * H.d, inferInstance, H.cycEmb, H.cycZeta, ?_, ?_, ?_, ?_, hζ, ?_⟩` and prove the remaining obligations. Conclude with `dvd_trans H.tower_dvd (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _))`. Conclude with `dvd_trans hψ (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _))`. Conclude with `dvd_trans (dvd_mul_left _ _) (dvd_mul_right _ _)`. Conclude with `dvd_mul_left _ _`.

Introduce `τ a hτ`. Establish `hprim : IsPrimitiveRoot (H.cycZeta ^ a) (H.QS * H.q * H.d)`. Rewrite using `[← hτ]`. Conclude with `hζ.map_of_injective τ.injective`. Establish `hcop : a.Coprime (H.QS * H.q * H.d)` using `(hζ.pow_iff_coprime hNpos a).mp hprim`.

Establish `hcop' : a.Coprime H.condN` using `hcop`. Rewrite using `[← hart a hcop']`. Use `set u := ZMod.unitOfCoprime a hcop' with hu`. Establish `hτu : τ H.cycZeta = H.cycZeta ^ (u : ZMod (H.QS * H.q * H.d)).val`. Rewrite using `[hτ]`.

Establish `hv : (u : ZMod (H.QS * H.q * H.d)).val = a % (H.QS * H.q * H.d)`. Rewrite using `[hu, ZMod.coe_unitOfCoprime, ZMod.val_natCast]`. Rewrite using `[hv]`. Use `conv_lhs => rw [← Nat.mod_add_div a (H.QS * H.q * H.d)]`. Rewrite using `[pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]`.

Establish `hspec` using `H.art_spec u τ hτu`. Prove the components needed by the constructor for the conclusion. Introduce `hfix`. Establish `hg : H.gal.symm (H.art u) = 1`. Use extensionality with `x`.

Apply `H.cycEmb.injective` to reduce the goal to its premises. Conclude with `(hspec x).trans (hfix x)`. Establish `h1` using `congrArg H.gal hg`. Rewrite `h1` using `[MulEquiv.apply_symm_apply, map_one]`. Conclude with `h1`.

Introduce `h1 x`. Establish `h2` using `hspec x`. Rewrite `h2` using `[h1, map_one]`. Rewrite using `[← h2]`. Both sides reduce to the same expression.
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
