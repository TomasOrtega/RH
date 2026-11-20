import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoBlockEqZeroIff
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentIsCentralIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentMulEqZeroOfNeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepIsoOfSimpleOfCentralIdempotentEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentsSimpleFDRepFiniteFinsumEqOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockIdempotentFixedVector

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerSys
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys

/- English proof (translation)
The claim follows from `GlobalTheory.T.simpleRepCentralIdempotent_isCentralIdempotent τ h`.
-/
theorem zIdem_idem_central {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (h : Simple τ) :
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := GlobalTheory.T.simpleRepCentralIdempotent_isCentralIdempotent τ h

/- English proof (translation)
The claim follows from `GlobalTheory.T.simpleRepCentralIdempotent_mul_eq_zero_of_ne τ τ' h h' hne`.
-/
theorem zIdem_mul_eq_zero {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ')
    (hne : zIdem τ ≠ zIdem τ') : zIdem τ * zIdem τ' = 0 := GlobalTheory.T.simpleRepCentralIdempotent_mul_eq_zero_of_ne τ τ' h h' hne

/- English proof (translation)
The claim follows from `GlobalTheory.T.repIso_of_simple_of_centralIdempotent_eq τ τ' h h' he`.
-/
theorem repIso_of_zIdem_eq {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ')
    (he : zIdem τ = zIdem τ') : RepIso τ.ρ τ'.ρ := GlobalTheory.T.repIso_of_simple_of_centralIdempotent_eq τ τ' h h' he

/- English proof (translation)
The claim follows from `GlobalTheory.T.centralIdempotents_simpleFDRep_finite_finsum_eq_one Γ`.
-/
theorem zIdem_finite_sum (Γ : Type) [Group Γ] [Fintype Γ] :
    {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite ∧
      ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 := GlobalTheory.T.centralIdempotents_simpleFDRep_finite_finsum_eq_one Γ

section Main

variable {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C)

def Zall (g n : ℕ) [Fact g.Prime] : Set (MonoidAlgebra ℂ (GL (Fin n) (ZMod g))) :=
  {z | ∃ τ : FDRep ℂ (GL (Fin n) (ZMod g)), Simple τ ∧ zIdem τ = z}

def Zl (n : ℕ) (f : (ZMod g)[X]) : Set (MonoidAlgebra ℂ (GL (Fin n) (ZMod g))) :=
  {z | ∃ τ : FDRep ℂ (GL (Fin n) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f}

/- English proof (translation)
Introduce `_ ⟨τ, h1, h2, _⟩` and use `⟨τ, h1, h2⟩`.
-/
theorem Zl_sub (n : ℕ) (f : (ZMod g)[X]) : Zl O n f ⊆ Zall g n := fun _ ⟨τ, h1, h2, _⟩ => ⟨τ, h1, h2⟩

/- English proof (translation)
The claim follows from `(zIdem_finite_sum (GL (Fin n) (ZMod g))).1`.
-/
theorem Zall_finite (n : ℕ) : (Zall g n).Finite := (zIdem_finite_sum (GL (Fin n) (ZMod g))).1

/- English proof (translation)
The claim follows from `(Zall_finite n).subset (Zl_sub O n f)`.
-/
theorem Zl_finite (n : ℕ) (f : (ZMod g)[X]) : (Zl O n f).Finite := (Zall_finite n).subset (Zl_sub O n f)

/- English proof (translation)
Rewrite using `[← finsum_mem_eq_finite_toFinset_sum (fun z => z) (Zl_finite O n f)]`. Both sides reduce to the same expression.
-/
theorem eSerO_eq_sum (n : ℕ) (f : (ZMod g)[X]) : eSerO O n f = ∑ z ∈ (Zl_finite O n f).toFinset, z := by
  rw [← finsum_mem_eq_finite_toFinset_sum (fun z => z) (Zl_finite O n f)]
  rfl

/- English proof (translation)
Take `⟨τ, hτ, rfl⟩` from `hz`. Take `⟨τ', hτ', rfl⟩` from `hz'`. Use `split_ifs with h`. Rewrite using `[← h]`. Conclude with `(zIdem_idem_central τ hτ).1`.

Conclude with `zIdem_mul_eq_zero τ τ' hτ hτ' h`.
-/
theorem mul_of_mem {n : ℕ} {z z' : MonoidAlgebra ℂ (GL (Fin n) (ZMod g))} (hz : z ∈ Zall g n)
    (hz' : z' ∈ Zall g n) : z * z' = if z = z' then z' else 0 := by
  obtain ⟨τ, hτ, rfl⟩ := hz
  obtain ⟨τ', hτ', rfl⟩ := hz'
  split_ifs with h
  · rw [← h]; exact (zIdem_idem_central τ hτ).1
  · exact zIdem_mul_eq_zero τ τ' hτ hτ' h

/- English proof (translation)
Take `⟨φ, hφ, hne⟩` from `h`. Take `⟨e, he⟩` from `e`. Establish `hφ' : ∀ γ, φ ∘ₗ τ.ρ γ = ρ γ ∘ₗ φ` using `hφ`. Use `⟨φ ∘ₗ (e : (τ' : Type) →ₗ[ℂ] (τ : Type)), fun γ => LinearMap.ext fun x => ?_, fun h0 => hne ?_⟩` and prove the remaining obligations. Use `show φ (e (τ'.ρ γ x)) = ρ γ (φ (e x))`.

Rewrite using `[he]`. Conclude with `LinearMap.congr_fun (hφ' γ) (e x)`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Use `LinearMap.congr_fun h0 (e.symm x)` as an intermediate fact. Simplify using `using this`.
-/
theorem isConstituent_of_repIso_left {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {τ τ' : FDRep ℂ Γ}
    {ρ : Representation ℂ Γ V} (h : IsConstituent τ ρ) (e : RepIso τ'.ρ τ.ρ) : IsConstituent τ' ρ := by
  obtain ⟨φ, hφ, hne⟩ := h
  obtain ⟨e, he⟩ := e
  have hφ' : ∀ γ, φ ∘ₗ τ.ρ γ = ρ γ ∘ₗ φ := hφ
  refine ⟨φ ∘ₗ (e : (τ' : Type) →ₗ[ℂ] (τ : Type)), fun γ => LinearMap.ext fun x => ?_, fun h0 => hne ?_⟩
  · show φ (e (τ'.ρ γ x)) = ρ γ (φ (e x))
    rw [he]
    exact LinearMap.congr_fun (hφ' γ) (e x)
  · refine LinearMap.ext fun x => ?_
    have := LinearMap.congr_fun h0 (e.symm x)
    simpa using this

/- English proof (translation)
Take `⟨s, b, lam, hb, hl, hc, hf⟩` from `h`. Conclude with `⟨s, b, lam, hb, hl, isConstituent_of_repIso_left hc e, hf⟩`.
-/
theorem hasLabelO_of_repIso {n : ℕ} {τ τ' : FDRep ℂ (GL (Fin n) (ZMod g))} {f : (ZMod g)[X]}
    (h : HasLabelO O τ f) (e : RepIso τ'.ρ τ.ρ) : HasLabelO O τ' f := by
  obtain ⟨s, b, lam, hb, hl, hc, hf⟩ := h
  exact ⟨s, b, lam, hb, hl, isConstituent_of_repIso_left hc e, hf⟩

end Main

end GlobalTheory.SerOSys
