import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPushforwardCoherentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemPullbackStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperSupportPullbackSystemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardClosedSystemUnseenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPullbackSystemQuasicoherentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonemptyOpenIdealNotNilpotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerKillsSystemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalClosedSystemStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

/- English proof (translation)
Introduce `A _ _ I _ X _ _ _ _ J _ Z _ hZ ψ hψ hover W hW hiso E hE S hS hK hP`. Establish `hln : IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))`. Establish `hcs : CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))`. Establish `hφ : IsProper (ψ ≫ J.subschemeι)` using `by haveI := hψ infer_instance`. Establish `hcl` using `GlobalTheory.T.closed_system_pullback I (ψ ≫ J.subschemeι) hover hE hS`.

Establish `hps` using `GlobalTheory.T.proper_support_pullback_system I (ψ ≫ J.subschemeι) hφ hover hE hS hP`. Establish `hEZ` using `isCoherent_pullback (ψ ≫ J.subschemeι) hE`. Take `⟨B, hBq, hBP, hB⟩` from `hZ _ hEZ _ hcl (fun e U a ha x => by`. Establish `ha0 : a = 0` using `by simpa using ha`. Substitute `ha0` using the available equality.

Conclude with `⟨0, by rw [map_zero, zero_smul]⟩) hps`. Use `hEZ.1` as an intermediate fact. Establish `hG : IsCoherent (cokernel B.arrow)` using `isCoherent_cokernel B.arrow hEZ`. Establish `hP'` using `GlobalTheory.T.proper_pushforward_coherent (ψ ≫ J.subschemeι) hφ hG`. Use `hP'.1` as an intermediate fact.

Establish `hE1` using `hE.1`. Establish `hDq : ((adjKer (ψ ≫ J.subschemeι) B : Subobject E) : X.Modules).IsQuasicoherent` using `(SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (kernelSubobjectIso (adjMap (ψ ≫ J.subschemeι) B)).symm (isCoherent_kernel (adjMap (ψ ≫ J.subschemeι) B) hE).1`. Take `⟨c, hc⟩` from `GlobalTheory.T.proper_pullback_system_quasicoherent I (ψ ≫ J.subschemeι) hφ hover hE hS B hBq hB`. Take `⟨J₀, hJ₀, hJ₀J⟩` from `GlobalTheory.T.nonempty_open_ideal_not_nilpotent J W hW`. Take `⟨m, hm⟩` from `GlobalTheory.T.ideal_power_kills_system hE (adjKer (ψ ≫ J.subschemeι) B) hDq S hS.qcoh J₀ (fun V f hf x hx => GlobalTheory.T.proper_birational_closed_system I J ψ hψ hover W hiso hE hS hK B hB V f (hJ₀ V f hf) x hx)`.

Use `⟨adjKer (ψ ≫ J.subschemeι) B, c, J ⊔ powIdeal J₀ m, hDq, GlobalTheory.T.pushforward_closed_system_auxiliary (ψ ≫ J.subschemeι) hφ hover B hBP, hc, ?_, ?_⟩` and prove the remaining obligations. Conclude with `lt_of_le_of_ne le_sup_left (fun h => hJ₀J m (h ▸ le_sup_right))`. Introduce `n U a ha x hx`. Take `⟨a₁, h₁, a₂, h₂, rfl⟩` from `Submodule.mem_sup.1 ha`. Rewrite using `[add_smul]`.

Take `⟨y, rfl⟩` from `hx`. Conclude with `(secsSub (S n) U).add_mem (hK n U a₁ h₁ _) (hm n U a₂ h₂ _ ⟨y, rfl⟩)`.
-/
theorem core_integral_step : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (J : X.IdealSheafData) [IsIntegral J.subscheme] {Z : Scheme.{0}} [Z.Over (Spec (.of A))], Statement I (⊥ : Z.IdealSheafData) → ∀ (ψ : Z ⟶ J.subscheme), IsProper ψ → (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (W : J.subscheme.Opens), (W : Set J.subscheme).Nonempty → IsIso (ψ ∣_ W) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → (∀ e, Killed J (S e)) → PropSupp A (S 0) → ∃ (D : Subobject E) (c : ℕ) (J' : X.IdealSheafData), (D : X.Modules).IsQuasicoherent ∧ PropSupp A D ∧ (∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1)) ∧ J < J' ∧ ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J'.ideal U → ∀ x ∈ secs D U, a • x ∈ secs (S n) U := by
  intro A _ _ I _ X _ _ _ _ J _ Z _ hZ ψ hψ hover W hW hiso E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have hφ : IsProper (ψ ≫ J.subschemeι) := by
    haveI := hψ
    infer_instance
  have hcl := GlobalTheory.T.closed_system_pullback I (ψ ≫ J.subschemeι) hover hE hS
  have hps := GlobalTheory.T.proper_support_pullback_system I (ψ ≫ J.subschemeι) hφ hover hE hS hP
  have hEZ := isCoherent_pullback (ψ ≫ J.subschemeι) hE
  obtain ⟨B, hBq, hBP, hB⟩ := hZ _ hEZ _ hcl (fun e U a ha x => by
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    exact ⟨0, by rw [map_zero, zero_smul]⟩) hps
  have := hEZ.1
  have hG : IsCoherent (cokernel B.arrow) := isCoherent_cokernel B.arrow hEZ
  have hP' := GlobalTheory.T.proper_pushforward_coherent (ψ ≫ J.subschemeι) hφ hG
  have := hP'.1
  have hE1 := hE.1
  have hDq : ((adjKer (ψ ≫ J.subschemeι) B : Subobject E) : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (kernelSubobjectIso (adjMap (ψ ≫ J.subschemeι) B)).symm
      (isCoherent_kernel (adjMap (ψ ≫ J.subschemeι) B) hE).1
  obtain ⟨c, hc⟩ := GlobalTheory.T.proper_pullback_system_quasicoherent I (ψ ≫ J.subschemeι) hφ hover hE hS B hBq hB
  obtain ⟨J₀, hJ₀, hJ₀J⟩ := GlobalTheory.T.nonempty_open_ideal_not_nilpotent J W hW
  obtain ⟨m, hm⟩ := GlobalTheory.T.ideal_power_kills_system hE (adjKer (ψ ≫ J.subschemeι) B) hDq S hS.qcoh J₀
    (fun V f hf x hx => GlobalTheory.T.proper_birational_closed_system I J ψ hψ hover W hiso hE hS hK B hB V f (hJ₀ V f hf) x hx)
  refine ⟨adjKer (ψ ≫ J.subschemeι) B, c, J ⊔ powIdeal J₀ m, hDq,
    GlobalTheory.T.pushforward_closed_system_auxiliary (ψ ≫ J.subschemeι) hφ hover B hBP, hc, ?_, ?_⟩
  · exact lt_of_le_of_ne le_sup_left (fun h => hJ₀J m (h ▸ le_sup_right))
  · intro n U a ha x hx
    obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := Submodule.mem_sup.1 ha
    rw [add_smul]
    obtain ⟨y, rfl⟩ := hx
    exact (secsSub (S n) U).add_mem (hK n U a₁ h₁ _) (hm n U a₂ h₂ _ ⟨y, rfl⟩)

end GlobalTheory.CompanionTheory.GE
