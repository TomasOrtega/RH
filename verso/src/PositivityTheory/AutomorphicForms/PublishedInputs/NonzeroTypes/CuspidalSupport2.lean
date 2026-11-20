import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.CuspidalSupport₂

variable {k : Type} [Field k]

/- English proof (translation)
Establish `h : GlobalTheory.SmGL.detChar (Fin 1) η * GlobalTheory.SmGL.detChar (Fin 1) χ = GlobalTheory.SmGL.detChar (R` using `k) (Fin 1) (η * χ) := by`. Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Simplify using `only [MonoidHom.mul_apply, GlobalTheory.SmGL.detChar_apply]`. Unfold `GlobalTheory.SmGL.detRep GlobalTheory.SmGL.ofChar`. Rewrite using `[GlobalTheory.SmGL.twist_twist, h]`.
-/
theorem twist_detRep_one (χ η : kˣ →* ℂˣ) :
    twist (detRep (Fin 1) χ) (detChar (Fin 1) η) = detRep (Fin 1) (η * χ) := by
  have h : GlobalTheory.SmGL.detChar (Fin 1) η * GlobalTheory.SmGL.detChar (Fin 1) χ =
      GlobalTheory.SmGL.detChar (R := k) (Fin 1) (η * χ) := by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.mul_apply, GlobalTheory.SmGL.detChar_apply]
  unfold GlobalTheory.SmGL.detRep GlobalTheory.SmGL.ofChar
  rw [GlobalTheory.SmGL.twist_twist, h]

/- English proof (translation)
Establish `h : GlobalTheory.SmGL.detChar (Fin d) η * GlobalTheory.SmGL.detChar (Fin d) η⁻¹ = (1 : GL (Fin d) k →* ℂˣ)`. Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Simplify using `only [MonoidHom.mul_apply, GlobalTheory.SmGL.detChar_apply, MonoidHom.inv_apply, mul_inv_cancel, MonoidHom.one_apply]`. Rewrite using `[GlobalTheory.SmGL.twist_twist, h, GlobalTheory.SmGL.twist_one]`.
-/
theorem twist_twist_inv {d : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ (GL (Fin d) k) X) (η : kˣ →* ℂˣ) :
    twist (twist σ (detChar (Fin d) η⁻¹)) (detChar (Fin d) η) = σ := by
  have h : GlobalTheory.SmGL.detChar (Fin d) η * GlobalTheory.SmGL.detChar (Fin d) η⁻¹ =
      (1 : GL (Fin d) k →* ℂˣ) := by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.mul_apply, GlobalTheory.SmGL.detChar_apply, MonoidHom.inv_apply,
      mul_inv_cancel, MonoidHom.one_apply]
  rw [GlobalTheory.SmGL.twist_twist, h, GlobalTheory.SmGL.twist_one]

end UpperTheory.TNZ.CuspidalSupport₂

namespace UpperTheory.TNZ

open CuspidalSupport₂ in
/- English proof (translation)
Introduce `hL k _ _ _ _ d X _ _ σ hs hi η hη hdv`. Take `⟨v, hv0, hv⟩` from `hdv`. Use `set τ := twist σ (detChar (Fin d) η⁻¹) with hτ`. Establish `hτs : IsSmooth τ` using `isSmooth_twist hs hη.inv.detChar`. Establish `hτi : τ.IsIrreducible` using `isIrreducible_twist hi _`.

Establish `hadm : IsAdmissible τ` using `(hL.bz k).1 (Fin d) X τ hτs hτi`. Establish `hI : fixed τ (iwahori k (Fin d)) ≠ ⊥`. Use `(Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩` and prove the remaining obligations. Establish `hg` using `hv h.1 (iwahori_le_KO k _ h.2)`. Rewrite using `[MonoidHom.one_apply, Units.val_one, one_smul]`.

Use `show (detChar (Fin d) η⁻¹ h.1 : ℂ) • σ h.1 v = v`. Rewrite using `[hg, smul_smul, detChar_apply, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]`. Take `⟨α, hα⟩` from `GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm hτi hI`. Set `χ : Fin d → kˣ →* ℂˣ` to `fun i => unrChar k (α i)`. Establish `h1` using `hα.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k d χ)`.

Establish `h2` using `isSubquotient_twist h1 (detChar (Fin d) η)`. Rewrite `h2` using `[hτ, twist_twist_inv]`. Establish `hχs : ∀ i, IsSmoothChar (χ i)` using `fun i => isSmoothChar_of_isUnram (isUnram_unrChar (k := k) (α i))`. Set `φ` to `multiProdTwistEquiv (Equiv.sigmaUnique (Fin d) fun _ => Fin 1) (fun i => detRep (Fin 1) (χ i)) hη`. Establish `h3` using `h2.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)`.

Establish `hfam : (fun i => twist (detRep (Fin 1) (χ i)) (detChar (Fin 1) η)) = fun i => detRep (Fin 1) (η * χ i)` using `funext fun i => twist_detRep_one _ _`. Rewrite `h3` using `[hfam]`. Use `⟨fun j => η * χ j, fun j => ⟨hη.mul (hχs j), fun u hu => ?_⟩, hi, fun j => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hη.mul (hχs j))⟩, _, h3⟩` and prove the remaining obligations. Use `show η u * unrChar k (α j) u = η u`. Rewrite using `[isUnram_unrChar (k := k) (α j) u hu, mul_one]`.
-/
theorem step_cuspSupp : CuspidalSupportProp := by
  intro hL k _ _ _ _ d X _ _ σ hs hi η hη hdv
  obtain ⟨v, hv0, hv⟩ := hdv
  set τ := twist σ (detChar (Fin d) η⁻¹) with hτ
  have hτs : IsSmooth τ := isSmooth_twist hs hη.inv.detChar
  have hτi : τ.IsIrreducible := isIrreducible_twist hi _
  have hadm : IsAdmissible τ := (hL.bz k).1 (Fin d) X τ hτs hτi
  have hI : fixed τ (iwahori k (Fin d)) ≠ ⊥ := by
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    have hg := hv h.1 (iwahori_le_KO k _ h.2)
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    show (detChar (Fin d) η⁻¹ h.1 : ℂ) • σ h.1 v = v
    rw [hg, smul_smul, detChar_apply, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_smul]
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm hτi hI
  let χ : Fin d → kˣ →* ℂˣ := fun i => unrChar k (α i)
  have h1 := hα.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k d χ)
  have h2 := isSubquotient_twist h1 (detChar (Fin d) η)
  rw [hτ, twist_twist_inv] at h2
  have hχs : ∀ i, IsSmoothChar (χ i) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar (k := k) (α i))
  let φ := multiProdTwistEquiv (Equiv.sigmaUnique (Fin d) fun _ => Fin 1)
    (fun i => detRep (Fin 1) (χ i)) hη
  have h3 := h2.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have hfam : (fun i => twist (detRep (Fin 1) (χ i)) (detChar (Fin 1) η)) =
      fun i => detRep (Fin 1) (η * χ i) := funext fun i => twist_detRep_one _ _
  rw [hfam] at h3
  refine ⟨fun j => η * χ j, fun j => ⟨hη.mul (hχs j), fun u hu => ?_⟩, hi,
    fun j => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hη.mul (hχs j))⟩, _, h3⟩
  show η u * unrChar k (α j) u = η u
  rw [isUnram_unrChar (k := k) (α j) u hu, mul_one]

end UpperTheory.TNZ
