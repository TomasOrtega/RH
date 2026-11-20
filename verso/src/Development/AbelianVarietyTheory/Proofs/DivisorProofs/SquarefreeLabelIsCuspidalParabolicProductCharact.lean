import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HarishChandraLabels.Basics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrrRepHarishChandraDistinctCuspidalLabelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionCuspidalParabolicProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonotoneBlocksSameHarishChandraCharacterStatement

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.SqfreeCuspProd

/- English proof (translation)
The claim follows from `(O.lab_spec _ _ (Nat.succ_le_of_lt Fintype.card_pos) (Formalism.L2.PT.simple_transp _ hs) (Formalism.L2.PT.isCuspidal_transp _ hc)).2.1`.
-/
theorem labO_irreducible {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K}
    (O : LabelMap K C) {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {σ : FDRep ℂ (GL κ K)} (hs : Simple σ) (hc : IsCuspidal K σ) : Irreducible (labO O σ) :=
  (O.lab_spec _ _ (Nat.succ_le_of_lt Fintype.card_pos) (Formalism.L2.PT.simple_transp _ hs)
    (Formalism.L2.PT.isCuspidal_transp _ hc)).2.1

/- English proof (translation)
Introduce `c c' h`. Assume the negation of the conclusion as `hne`. Establish `hd : F c * F c' ∣ ∏ x, F x`. Rewrite using `[← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ c), ← Finset.mul_prod_erase (Finset.univ.erase c) F (Finset.mem_erase.2 ⟨fun h' => hne h'.symm, Finset.mem_univ c'⟩), ← mul_assoc]`. Conclude with `dvd_mul_right _ _`.

Rewrite `hd` using `[h]`. Conclude with `(hF c').not_isUnit (hsq _ hd)`.
-/
theorem injective_of_squarefree {R : Type} [CommMonoid R] {s : ℕ} (F : Fin s → R)
    (hF : ∀ c, Irreducible (F c)) (hsq : Squarefree (∏ c, F c)) : Function.Injective F := by
  intro c c' h
  by_contra hne
  have hd : F c * F c' ∣ ∏ x, F x := by
    rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ c),
      ← Finset.mul_prod_erase (Finset.univ.erase c) F
        (Finset.mem_erase.2 ⟨fun h' => hne h'.symm, Finset.mem_univ c'⟩), ← mul_assoc]
    exact dvd_mul_right _ _
  rw [h] at hd
  exact (hF c').not_isUnit (hsq _ hd)

/- English proof (translation)
Take `⟨φ, hφ, hne⟩` from `hc`. Establish `hirr` using `(PI.GreenHCLabel.simple_irreducible Γ τ).1 hτ`. Establish `hker : LinearMap.ker φ = ⊥`. Break down `hirr.2 (LinearMap.ker φ) (fun g v hv => by` into its components or cases. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`.

Use `congrArg (fun k => k v) (hφ g)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply] at this`. Rewrite using `[this, hv, map_zero]) with h | h`. Conclude with `h`. Conclude with `absurd (LinearMap.ker_eq_top.1 h) hne`.

Establish `hran : LinearMap.range φ = ⊤`. Break down `hρ.2 (LinearMap.range φ) (fun g v hv => by` into its components or cases. Take `⟨y, rfl⟩` from `hv`. Conclude with `⟨τ.ρ g y, by simpa using congrArg (fun k => k y) (hφ g)⟩) with h | h`. Conclude with `absurd (LinearMap.range_eq_bot.1 h) hne`.

Conclude with `h`. Set `e : τ ≃ₗ[ℂ] V` to `LinearEquiv.ofBijective φ ⟨LinearMap.ker_eq_bot.1 hker, LinearMap.range_eq_top.1 hran⟩`. Use `haveI : Module.Finite ℂ V := Module.Finite.equiv e`. Establish `hconj : e.conj (τ.ρ x) = ρ x`. Use extensionality with `v`.

Take `⟨w, rfl⟩` from `e.surjective v`. Rewrite using `[LinearEquiv.conj_apply]`. Use `show e (τ.ρ x (e.symm (e w))) = ρ x (e w)`. Rewrite using `[e.symm_apply_apply]`. Conclude with `congrArg (fun k => k w) (hφ x)`.

Rewrite using `[FDRep.character, ← hconj, LinearMap.trace_conj']`.
-/
theorem character_eq_of_constituent {Γ : Type} [Group Γ] (τ : FDRep ℂ Γ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ Γ V) (hτ : Simple τ) (hρ : IsIrrRep ρ) (hc : IsConstituent τ ρ)
    (x : Γ) : τ.character x = LinearMap.trace ℂ V (ρ x) := by
  obtain ⟨φ, hφ, hne⟩ := hc
  have hirr := (PI.GreenHCLabel.simple_irreducible Γ τ).1 hτ
  have hker : LinearMap.ker φ = ⊥ := by
    rcases hirr.2 (LinearMap.ker φ) (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      have := congrArg (fun k => k v) (hφ g)
      simp only [LinearMap.comp_apply] at this
      rw [this, hv, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hne
  have hran : LinearMap.range φ = ⊤ := by
    rcases hρ.2 (LinearMap.range φ) (fun g v hv => by
      obtain ⟨y, rfl⟩ := hv
      exact ⟨τ.ρ g y, by simpa using congrArg (fun k => k y) (hφ g)⟩) with h | h
    · exact absurd (LinearMap.range_eq_bot.1 h) hne
    · exact h
  let e : τ ≃ₗ[ℂ] V :=
    LinearEquiv.ofBijective φ ⟨LinearMap.ker_eq_bot.1 hker, LinearMap.range_eq_top.1 hran⟩
  haveI : Module.Finite ℂ V := Module.Finite.equiv e
  have hconj : e.conj (τ.ρ x) = ρ x := by
    ext v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply]
    show e (τ.ρ x (e.symm (e w))) = ρ x (e w)
    rw [e.symm_apply_apply]
    exact congrArg (fun k => k w) (hφ x)
  rw [FDRep.character, ← hconj, LinearMap.trace_conj']

/- English proof (translation)
Introduce `K _ _ _ C O r τ f hτ hL hsq`. Take `⟨s, b, lam, hb, hl, hc, rfl⟩` from `hL`. Establish `hirrF : ∀ c, Irreducible (labO O (lam c))` using `fun c => by`. Take `⟨i, hi⟩` from `hb c`. Use `haveI : Nonempty {i // b i = c} := ⟨⟨i, hi⟩⟩`.

Conclude with `labO_irreducible O (hl c).1 (hl c).2`. Establish `hinj` using `injective_of_squarefree _ hirrF hsq`. Establish `hirr` using `GlobalTheory.T.isIrrRep_harishChandra_distinct_cuspidal_labels K r s b lam hb hl C O hinj`. Take `⟨b', lam', hb', hl', hmono, htr⟩` from `GlobalTheory.T.exists_monotone_blocks_same_harishChandra_character K r s b lam hb hl`. Establish `hcp` using `GlobalTheory.T.harishChandraInduction_cuspidalParabolicProduct K r s b' lam' hb' hl' hmono`.

Establish `hfun : (fun x : GL (Fin r) K => τ.character x) = fun x => LinearMap.trace ℂ (hcSpace K b' lam') (hcRep K b' lam' x)`. Use function extensionality and compare the values at `x`. Rewrite using `[htr x]`. Conclude with `character_eq_of_constituent τ _ hτ hirr hc x`. Rewrite using `[hfun]`.

Conclude with `hcp`.
-/
theorem isCuspProdChar_of_squarefree : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K)
    (O : LabelMap K C) (r : ℕ) (τ : FDRep ℂ (GL (Fin r) K)) (f : K[X]), Simple τ → HasLabelO O τ f →
    Squarefree f → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => τ.character x) := by
  intro K _ _ _ C O r τ f hτ hL hsq
  obtain ⟨s, b, lam, hb, hl, hc, rfl⟩ := hL
  have hirrF : ∀ c, Irreducible (labO O (lam c)) := fun c => by
    obtain ⟨i, hi⟩ := hb c
    haveI : Nonempty {i // b i = c} := ⟨⟨i, hi⟩⟩
    exact labO_irreducible O (hl c).1 (hl c).2
  have hinj := injective_of_squarefree _ hirrF hsq
  have hirr := GlobalTheory.T.isIrrRep_harishChandra_distinct_cuspidal_labels K r s b lam hb hl C O hinj
  obtain ⟨b', lam', hb', hl', hmono, htr⟩ := GlobalTheory.T.exists_monotone_blocks_same_harishChandra_character K r s b lam hb hl
  have hcp := GlobalTheory.T.harishChandraInduction_cuspidalParabolicProduct K r s b' lam' hb' hl' hmono
  have hfun : (fun x : GL (Fin r) K => τ.character x) =
      fun x => LinearMap.trace ℂ (hcSpace K b' lam') (hcRep K b' lam' x) := by
    funext x
    rw [htr x]
    exact character_eq_of_constituent τ _ hτ hirr hc x
  rw [hfun]
  exact hcp

end GlobalTheory.SqfreeCuspProd
