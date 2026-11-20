import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharIdem
import Formalism.PadicSubsetSums.StableGradedCounts.CentralIdempotentsSumOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepIsoOfSimpleOfCentralIdempotentEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSimpleModuleOfFinrankEnd
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

namespace GlobalTheory.SerOSys.ZSum

variable {Γ : Type} [Group Γ] [Fintype Γ]

/- English proof (translation)
Unfold `zIdem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem`. Use `Finset.sum_congr rfl fun γ _ => ?_` and prove the remaining obligations. Rewrite using `[MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]`. Both sides reduce to the same expression.
-/
theorem zIdem_eq_centralIdem (τ : FDRep ℂ Γ) : zIdem τ = Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem τ.ρ := by
  unfold zIdem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  rfl

/- English proof (translation)
Unfold `zIdem PI.CharIdem.charIdem`. Both sides reduce to the same expression.
-/
theorem zIdem_eq_charIdem' (τ : FDRep ℂ Γ) : zIdem τ = PI.CharIdem.charIdem τ := by
  unfold zIdem PI.CharIdem.charIdem
  rfl

/- English proof (translation)
Use `haveI := h`. Establish `hc : (Nat.card Γ : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Establish `: Invertible (Nat.card Γ : ℂ)` using `invertibleOfNonzero hc`. Apply `GlobalTheory.AbsIrrDescent.isIrreducible_of_norm_one` to reduce the goal to its premises. Establish `hs` using `FDRep.char_orthonormal τ τ`.

Rewrite `hs` using `[if_pos ⟨Iso.refl _⟩, inv_mul_eq_one₀ hc]`. Conclude with `hs.symm`.
-/
theorem isIrreducible_of_simple (τ : FDRep ℂ Γ) (h : Simple τ) : Representation.IsIrreducible τ.ρ := by
  haveI := h
  have hc : (Nat.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : Invertible (Nat.card Γ : ℂ) := invertibleOfNonzero hc
  apply GlobalTheory.AbsIrrDescent.isIrreducible_of_norm_one
  have hs := FDRep.char_orthonormal τ τ
  rw [if_pos ⟨Iso.refl _⟩, inv_mul_eq_one₀ hc] at hs
  exact hs.symm

/- English proof (translation)
The claim follows from `Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum.isIrr_of_isIrreducible _ (isIrreducible_of_simple τ h)`.
-/
theorem isIrr_of_simple (τ : FDRep ℂ Γ) (h : Simple τ) : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr τ.ρ :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum.isIrr_of_isIrreducible _ (isIrreducible_of_simple τ h)

/- English proof (translation)
Take `⟨hnt, hW⟩` from `h`. Use `{ exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }` and prove the remaining obligations. Establish `h1` using `congrArg Subrepresentation.toSubmodule e`. Conclude with `(bot_ne_top : (⊥ : Submodule ℂ W) ≠ ⊤) h1`. Break down `hW U.toSubmodule (fun g x hx => U.apply_mem_toSubmodule g hx) with h1 | h1` into its components or cases.

Use `left`. Conclude with `Subrepresentation.toSubmodule_injective h1`. Use `right`. Conclude with `Subrepresentation.toSubmodule_injective h1`.
-/
theorem isIrreducible_of_isIrr {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ Γ W)
    (h : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr σ) : σ.IsIrreducible := by
  obtain ⟨hnt, hW⟩ := h
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · have h1 := congrArg Subrepresentation.toSubmodule e
    exact (bot_ne_top : (⊥ : Submodule ℂ W) ≠ ⊤) h1
  · rcases hW U.toSubmodule (fun g x hx => U.apply_mem_toSubmodule g hx) with h1 | h1
    · left; exact Subrepresentation.toSubmodule_injective h1
    · right; exact Subrepresentation.toSubmodule_injective h1

/- English proof (translation)
Establish `h1 : τ.character = τ'.character` using `FDRep.char_iso i`. Establish `h2 : Module.finrank ℂ τ = Module.finrank ℂ τ'` using `(FDRep.isoToLinearEquiv i).finrank_eq`. Express the relevant statement in the definitionally equal form `∑ γ : Γ, MonoidAlgebra.single γ ((Module.finrank ℂ τ : ℂ) / Fintype.card Γ * τ.character γ⁻¹) = ∑ γ : Γ, MonoidAlgebra.single γ ((Module.finrank ℂ τ' : ℂ) / Fintype.card Γ * τ'.character γ⁻¹)`. Rewrite using `[h1, h2]`.
-/
theorem zIdem_eq_of_iso {τ τ' : FDRep ℂ Γ} (i : τ ≅ τ') : zIdem τ = zIdem τ' := by
  have h1 : τ.character = τ'.character := FDRep.char_iso i
  have h2 : Module.finrank ℂ τ = Module.finrank ℂ τ' := (FDRep.isoToLinearEquiv i).finrank_eq
  change ∑ γ : Γ, MonoidAlgebra.single γ ((Module.finrank ℂ τ : ℂ) / Fintype.card Γ * τ.character γ⁻¹) =
    ∑ γ : Γ, MonoidAlgebra.single γ ((Module.finrank ℂ τ' : ℂ) / Fintype.card Γ * τ'.character γ⁻¹)
  rw [h1, h2]

/- English proof (translation)
Establish `h2 : Module.finrank ℂ τ = Module.finrank ℂ τ'` using `φ.finrank_eq`. Establish `h1 : ∀ g, LinearMap.trace ℂ τ' (τ'.ρ g) = LinearMap.trace ℂ τ (τ.ρ g)`. Introduce `g`. Establish `: τ'.ρ g = φ.conj (τ.ρ g)`. Use extensionality with `x`.

Simplify using `[LinearEquiv.conj_apply, hφ]`. Rewrite using `[this, LinearMap.trace_conj']`. Unfold `zIdem`. Simplify using `only [h1, h2]`.
-/
theorem zIdem_eq_of_equiv (τ τ' : FDRep ℂ Γ) (φ : τ ≃ₗ[ℂ] τ') (hφ : ∀ g x, φ (τ.ρ g x) = τ'.ρ g (φ x)) :
    zIdem τ = zIdem τ' := by
  have h2 : Module.finrank ℂ τ = Module.finrank ℂ τ' := φ.finrank_eq
  have h1 : ∀ g, LinearMap.trace ℂ τ' (τ'.ρ g) = LinearMap.trace ℂ τ (τ.ρ g) := by
    intro g
    have : τ'.ρ g = φ.conj (τ.ρ g) := by
      ext x; simp [LinearEquiv.conj_apply, hφ]
    rw [this, LinearMap.trace_conj']
  unfold zIdem
  simp only [h1, h2]

/- English proof (translation)
Introduce `h0`. Establish `ha` using `(orthogonalCentral Γ τ τ h h).1`. Rewrite `ha` using `[← zIdem_eq_charIdem', h0, map_zero]`. Take `⟨hnt, -⟩` from `isIrr_of_simple τ h`. Take `⟨v, hv⟩` from `exists_ne (0 : τ)`.

Conclude with `hv (by simpa using (LinearMap.congr_fun ha v).symm)`.
-/
theorem zIdem_ne_zero (τ : FDRep ℂ Γ) (h : Simple τ) : zIdem τ ≠ 0 := by
  intro h0
  have ha := (orthogonalCentral Γ τ τ h h).1
  rw [← zIdem_eq_charIdem', h0, map_zero] at ha
  obtain ⟨hnt, -⟩ := isIrr_of_simple τ h
  obtain ⟨v, hv⟩ := exists_ne (0 : τ)
  exact hv (by simpa using (LinearMap.congr_fun ha v).symm)

/- English proof (translation)
Use `(orthogonalCentral Γ τ τ h h).2.2.1` as an intermediate fact. Rewrite using `[zIdem_eq_charIdem']`. Conclude with `this`.
-/
theorem zIdem_mul_self (τ : FDRep ℂ Γ) (h : Simple τ) : zIdem τ * zIdem τ = zIdem τ := by
  have := (orthogonalCentral Γ τ τ h h).2.2.1
  rw [zIdem_eq_charIdem']; exact this

/- English proof (translation)
Use `(orthogonalCentral Γ τ τ' h h').2.2.2.2 ⟨fun i => hne (zIdem_eq_of_iso i)⟩` as an intermediate fact. Rewrite using `[zIdem_eq_charIdem', zIdem_eq_charIdem']`. Conclude with `this`.
-/
theorem zIdem_mul_of_ne (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ') (hne : zIdem τ ≠ zIdem τ') :
    zIdem τ * zIdem τ' = 0 := by
  have := (orthogonalCentral Γ τ τ' h h').2.2.2.2 ⟨fun i => hne (zIdem_eq_of_iso i)⟩
  rw [zIdem_eq_charIdem', zIdem_eq_charIdem']; exact this

end GlobalTheory.SerOSys.ZSum

namespace GlobalTheory.SerOSys.ZSum

variable {Γ : Type} [Group Γ] [Fintype Γ]

/- English proof (translation)
Use `set S := {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}`. Establish `hli : LinearIndependent ℂ (fun z : S => (z : MonoidAlgebra ℂ Γ))`. Rewrite using `[linearIndependent_iff']`. Introduce `s c hs j hj`. Take `⟨τ, hτ, hτz⟩` from `j.2`.

Establish `hmul` using `congrArg (· * (j : MonoidAlgebra ℂ Γ)) hs`. Simplify using `only [Finset.sum_mul, zero_mul, smul_mul_assoc] at hmul`. Rewrite `hmul` using `[Finset.sum_eq_single j]`. Rewrite `hmul` using `[← hτz, zIdem_mul_self τ hτ]`. Conclude with `(smul_eq_zero.1 hmul).resolve_right (zIdem_ne_zero τ hτ)`.

Introduce `i _ hij`. Take `⟨σ, hσ, hσz⟩` from `i.2`. Establish `hne : zIdem σ ≠ zIdem τ`. Rewrite using `[hσz, hτz]`. Conclude with `fun e => hij (Subtype.ext e)`.

Rewrite using `[← hσz, ← hτz, zIdem_mul_of_ne σ τ hσ hτ hne, smul_zero]`. Introduce `hn`. Conclude with `absurd hj hn`. Conclude with `Set.finite_coe_iff.1 hli.finite`.
-/
theorem zIdem_set_finite :
    {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite := by
  set S := {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}
  have hli : LinearIndependent ℂ (fun z : S => (z : MonoidAlgebra ℂ Γ)) := by
    rw [linearIndependent_iff']
    intro s c hs j hj
    obtain ⟨τ, hτ, hτz⟩ := j.2
    have hmul := congrArg (· * (j : MonoidAlgebra ℂ Γ)) hs
    simp only [Finset.sum_mul, zero_mul, smul_mul_assoc] at hmul
    rw [Finset.sum_eq_single j] at hmul
    · rw [← hτz, zIdem_mul_self τ hτ] at hmul
      exact (smul_eq_zero.1 hmul).resolve_right (zIdem_ne_zero τ hτ)
    · intro i _ hij
      obtain ⟨σ, hσ, hσz⟩ := i.2
      have hne : zIdem σ ≠ zIdem τ := by
        rw [hσz, hτz]; exact fun e => hij (Subtype.ext e)
      rw [← hσz, ← hτz, zIdem_mul_of_ne σ τ hσ hτ hne, smul_zero]
    · intro hn; exact absurd hj hn
  exact Set.finite_coe_iff.1 hli.finite

/- English proof (translation)
Use `set S := {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z} with hS`. Establish `hfin : S.Finite` using `zIdem_set_finite`. Use `letI : Fintype S := hfin.fintype`. Use `choose τ hτ hτz using fun z : S => z.2`. Establish `key` using `Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotents_sum_one Γ S (fun z => (τ z : Type)) (fun z => (τ z).ρ) (fun z => isIrr_of_simple (τ z) (hτ z)) (fun i j ⟨φ, hφ⟩ => Subtype.ext ((hτz i).symm.trans ((zIdem_eq_of_equiv (τ i) (τ j) φ hφ).trans (hτz j)))) ( …`.

Establish `hs : Simple (FDRep.of σ)` using `PI.GreenLabelSurjWork.simple_of_irr σ`. Set `i : S` to `⟨zIdem (FDRep.of σ), FDRep.of σ, hs, rfl⟩`. Take `⟨e, he⟩` from `repIso_of_zIdem_eq_of_simple (FDRep.of σ) (τ i) hs (hτ i) (hτz i).symm`. Conclude with `⟨i, e, fun g x => he g x⟩)`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_subtype hfin.toFinset (fun x => Set.Finite.mem_toFinset hfin) (fun z => z), ← key]`.

Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Rewrite using `[← zIdem_eq_centralIdem, hτz z]`.
-/
theorem zIdem_set_finsum :
    ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 := by
  classical
  set S := {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z} with hS
  have hfin : S.Finite := zIdem_set_finite
  letI : Fintype S := hfin.fintype
  choose τ hτ hτz using fun z : S => z.2
  have key := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotents_sum_one Γ S (fun z => (τ z : Type)) (fun z => (τ z).ρ)
    (fun z => isIrr_of_simple (τ z) (hτ z))
    (fun i j ⟨φ, hφ⟩ => Subtype.ext ((hτz i).symm.trans ((zIdem_eq_of_equiv (τ i) (τ j) φ hφ).trans (hτz j))))
    (fun W _ _ _ σ hσ => by
      haveI := isIrreducible_of_isIrr σ hσ
      have hs : Simple (FDRep.of σ) := PI.GreenLabelSurjWork.simple_of_irr σ
      let i : S := ⟨zIdem (FDRep.of σ), FDRep.of σ, hs, rfl⟩
      obtain ⟨e, he⟩ := repIso_of_zIdem_eq_of_simple (FDRep.of σ) (τ i) hs (hτ i) (hτz i).symm
      exact ⟨i, e, fun g x => he g x⟩)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_subtype hfin.toFinset (fun x => Set.Finite.mem_toFinset hfin) (fun z => z), ← key]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← zIdem_eq_centralIdem, hτz z]

end GlobalTheory.SerOSys.ZSum

namespace GlobalTheory.SerOSys

/- English proof (translation)
Introduce `_ _ _` and use `⟨ZSum.zIdem_set_finite, ZSum.zIdem_set_finsum⟩`.
-/
theorem zIdem_finite_and_finsum_eq_one : ∀ (Γ : Type) [Group Γ] [Fintype Γ],
    {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite ∧
      ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 :=
  fun _ _ _ => ⟨ZSum.zIdem_set_finite, ZSum.zIdem_set_finsum⟩

end GlobalTheory.SerOSys
