import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
import GroundTheory.PAdicHodge.ACrisBdRGalois

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCSig

variable {p : ℕ} [Fact p.Prime] {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)}

/- English proof (translation)
Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Use `UniformSpace.Completion.induction_on x (isClosed_eq (continuous_galCp σ) (continuous_galCp τ)) fun a => ?_` and prove the remaining obligations. Use `show galCp σ (a : ℂ_[p]) = galCp τ (a : ℂ_[p])`. Rewrite using `[galCp_coe, galCp_coe, h]`.
-/
theorem galCp_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : (galCp σ : ℂ_[p] →+* ℂ_[p]) = (galCp τ : ℂ_[p] →+* ℂ_[p]) := by
  refine RingHom.ext fun x => ?_
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_galCp σ) (continuous_galCp τ)) fun a => ?_
  show galCp σ (a : ℂ_[p]) = galCp τ (a : ℂ_[p])
  rw [galCp_coe, galCp_coe, h]

/- English proof (translation)
The claim follows from `AInf.map_congr (galCp_congr σ τ h) _ _`.
-/
theorem galMap_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : AInf.galMap σ = AInf.galMap τ :=
  AInf.map_congr (galCp_congr σ τ h) _ _

/- English proof (translation)
The claim follows from `IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt (normInteger ℂ_[p]) p))) (RingHom.ext fun w => by simp only [RingHom.comp_apply, galAway_algebraMap] rw [AInf.gal_smul_def, AInf.gal_smul_def, galMap_congr σ τ h])`.
-/
theorem galAway_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : galAway σ = galAway τ :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt (normInteger ℂ_[p]) p)))
    (RingHom.ext fun w => by
      simp only [RingHom.comp_apply, galAway_algebraMap]
      rw [AInf.gal_smul_def, AInf.gal_smul_def, galMap_congr σ τ h])

/- English proof (translation)
The claim follows from `Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by simp only [RingHom.comp_apply, galQuot_mk] rw [galAway_congr σ τ h])`.
-/
theorem galQuot_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) (n : ℕ) : galQuot σ n = galQuot τ n :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by
    simp only [RingHom.comp_apply, galQuot_mk]
    rw [galAway_congr σ τ h])

/- English proof (translation)
The claim follows from `RingHom.ext fun x => IsPerfectoidField.evalB_ext fun n => by rw [evalB_galBdRHom, evalB_galBdRHom, galQuot_congr σ τ h]`.
-/
theorem galBdRHom_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : galBdRHom σ = galBdRHom τ :=
  RingHom.ext fun x => IsPerfectoidField.evalB_ext fun n => by
    rw [evalB_galBdRHom, evalB_galBdRHom, galQuot_congr σ τ h]

/- English proof (translation)
Establish `h` using `ACris.iota_gal_smul (IntermediateField.fixingSubgroupEquiv K g) c`. Rewrite `h` using `[ACris.gal_smul_def, gal_smul_bdR_def]`. Rewrite using `[h]`. Conclude with `congrArg (fun f => f (ACris.iota ℂ_[l] l c)) (galBdRHom_congr (toBot g.1) (IntermediateField.fixingSubgroupEquiv K g) fun y => rfl)`.
-/
theorem gP_iota {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (g : K.fixingSubgroup) (c : Acris l) :
    gP l g (ACris.iota ℂ_[l] l c) =
      ACris.iota ℂ_[l] l (ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) c) := by
  have h := ACris.iota_gal_smul (IntermediateField.fixingSubgroupEquiv K g) c
  rw [ACris.gal_smul_def, gal_smul_bdR_def] at h
  rw [h]
  exact congrArg (fun f => f (ACris.iota ℂ_[l] l c))
    (galBdRHom_congr (toBot g.1) (IntermediateField.fixingSubgroupEquiv K g) fun y => rfl)

/- English proof (translation)
Introduce `l _ K M h k g c`. Apply `ι_injective (fk l k) (xi0 l) l M` to reduce the goal to its premises. Use `show gB h k g (pk l k (ACris.iota ℂ_[l] l c)) = pk l k (ACris.iota ℂ_[l] l (ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) c))`. Rewrite using `[← gP_iota]`. Conclude with `Ideal.quotientMap_mk`.
-/
theorem sig_lam : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ), ∀ g c,
    (lev h k).σA g ((lev h k).lam c) = (lev h k).lam ((per l K).σA g c) := by
  intro l _ K M h k g c
  apply ι_injective (fk l k) (xi0 l) l M
  show gB h k g (pk l k (ACris.iota ℂ_[l] l c)) =
    pk l k (ACris.iota ℂ_[l] l (ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) c))
  rw [← gP_iota]
  exact Ideal.quotientMap_mk

end GlobalTheory.CompanionTheory.LatCSig
