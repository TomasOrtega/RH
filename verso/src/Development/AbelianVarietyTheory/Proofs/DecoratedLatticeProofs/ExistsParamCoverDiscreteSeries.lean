import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverExhaust

variable {p q n : ℕ}

/- English proof (translation)
Use `⟨fun i => by simp, fun j => by simp, ?_⟩` and prove the remaining obligations. Introduce and unpack `(a | a) (b | b) hab`. Conclude with `hab`. Conclude with `hab.elim`. Conclude with `hab.elim`.

Conclude with `Nat.add_lt_add_left hab p`.
-/
theorem blockOrd_std (p q : ℕ) :
    BlockOrd (finSumFinEquiv : Ix p q ≃ Fin (p + q)) fun i => (finSumFinEquiv.symm i).isLeft := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · exact hab
  · exact hab.elim
  · exact hab.elim
  · exact Nat.add_lt_add_left hab p

/- English proof (translation)
Use `⟨fun i => by simpa using h.1 i, fun j => by simpa using h.2.1 j, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Take `⟨hlt, hε⟩` from `(h.posC_iff a b).1 hab`. Simplify using `only [Equiv.trans_apply]`. Break down `lt_trichotomy (s.symm (e a)) (s.symm (e b)) with h1 | h1 | h1` into its components or cases.

Conclude with `h1`. Conclude with `absurd (s.symm.injective h1) (ne_of_lt hlt)`. Establish `h2` using `hs _ _ h1 (by simp only [Equiv.apply_symm_apply]; exact hε.symm)`. Simplify using `only [Equiv.apply_symm_apply] at h2`. Conclude with `absurd h2 (not_lt.2 hlt.le)`.
-/
theorem blockOrd_perm {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (s : Equiv.Perm (Fin n))
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) : BlockOrd (e.trans s.symm) (ε ∘ s) := by
  refine ⟨fun i => by simpa using h.1 i, fun j => by simpa using h.2.1 j, ?_⟩
  intro a b hab
  obtain ⟨hlt, hε⟩ := (h.posC_iff a b).1 hab
  simp only [Equiv.trans_apply]
  rcases lt_trichotomy (s.symm (e a)) (s.symm (e b)) with h1 | h1 | h1
  · exact h1
  · exact absurd (s.symm.injective h1) (ne_of_lt hlt)
  · have h2 := hs _ _ h1 (by simp only [Equiv.apply_symm_apply]; exact hε.symm)
    simp only [Equiv.apply_symm_apply] at h2
    exact absurd h2 (not_lt.2 hlt.le)

/- English proof (translation)
Take `⟨σ, hF⟩` from `exists_factors R.U (finSumFinEquiv : Ix p q ≃ Fin (p + q)) k`. Establish `hB0` using `blockOrd_std p q`. Establish `hIrr : GlobalTheory.Dec.IsSqIntIrr (fun i : Fin (p + q) => (finSumFinEquiv.symm i).isLeft) σ` using `⟨R.U.cs, R.nontriv, (GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q (p + q) _ _ T R σ hB0 hF).1, (GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q (p + q) _ _ T R σ hB0 hF).2, GlobalTheory.T.block_ordered_square_integrable p q (p + q) _ _ T R σ hB0 hF⟩`. Take `⟨s, mu, hc, hs, hDS⟩` from `hE (p + q) _ R.U.H σ hIrr`. Set `P : SignedPar (p + q)` to `⟨mu, (fun i : Fin (p + q) => (finSumFinEquiv.symm i).isLeft) ∘ s, hc⟩`.

Establish `hB : BlockOrd ((finSumFinEquiv : Ix p q ≃ Fin (p + q)).trans s.symm) P.sgn` using `blockOrd_perm hB0 s hs`. Establish `hF' : Factors R.U ((finSumFinEquiv : Ix p q ≃ Fin (p + q)).trans s.symm) (fun g => σ (g.submatrix s.symm s.symm))`. Introduce `x`. Rewrite using `[hF x]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[Matrix.reindex_apply, Matrix.submatrix_apply]`. Conclude with `⟨P, _, hB, (hasParam_iff_isDSPar R P hB hF').2 hDS⟩`.
-/
theorem exists_param_of_trivial (hE : GlobalTheory.Dec.DSExhaust) {T : GrpData p q} (R : DSRep T)
    (k : ∀ x, T.cov x = 1 → R.U.π x = 1) :
    ∃ (P : SignedPar (p + q)) (e : Ix p q ≃ Fin (p + q)), BlockOrd e P.sgn ∧ HasParam R (blockPar P e) := by
  obtain ⟨σ, hF⟩ := exists_factors R.U (finSumFinEquiv : Ix p q ≃ Fin (p + q)) k
  have hB0 := blockOrd_std p q
  have hIrr : GlobalTheory.Dec.IsSqIntIrr (fun i : Fin (p + q) => (finSumFinEquiv.symm i).isLeft) σ :=
    ⟨R.U.cs, R.nontriv,
      (GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q (p + q) _ _ T R σ hB0 hF).1,
      (GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q (p + q) _ _ T R σ hB0 hF).2,
      GlobalTheory.T.block_ordered_square_integrable p q (p + q) _ _ T R σ hB0 hF⟩
  obtain ⟨s, mu, hc, hs, hDS⟩ := hE (p + q) _ R.U.H σ hIrr
  let P : SignedPar (p + q) := ⟨mu, (fun i : Fin (p + q) => (finSumFinEquiv.symm i).isLeft) ∘ s, hc⟩
  have hB : BlockOrd ((finSumFinEquiv : Ix p q ≃ Fin (p + q)).trans s.symm) P.sgn := blockOrd_perm hB0 s hs
  have hF' : Factors R.U ((finSumFinEquiv : Ix p q ≃ Fin (p + q)).trans s.symm)
      (fun g => σ (g.submatrix s.symm s.symm)) := by
    intro x
    rw [hF x]
    congr 1
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact ⟨P, _, hB, (hasParam_iff_isDSPar R P hB hF').2 hDS⟩

/- English proof (translation)
Introduce `hE p q _ T R`. Break down `Cover.trivial_or_twist R with k | k` into its components or cases. Take `⟨P, e, h1, h2⟩` from `exists_param_of_trivial hE R k`. Conclude with `⟨_, isParam_blockPar P h1, h2⟩`. Take `⟨P, e, h1, h2⟩` from `exists_param_of_trivial hE (Cover.twist R) k`.

Conclude with `⟨_, isParam_half P h1, (Cover.hasParam_twist R _).1 h2⟩`.
-/
theorem exists_param : GlobalTheory.Dec.DSExhaust → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T), ∃ lam, IsParam lam ∧ HasParam R lam := by
  intro hE p q _ T R
  rcases Cover.trivial_or_twist R with k | k
  · obtain ⟨P, e, h1, h2⟩ := exists_param_of_trivial hE R k
    exact ⟨_, isParam_blockPar P h1, h2⟩
  · obtain ⟨P, e, h1, h2⟩ := exists_param_of_trivial hE (Cover.twist R) k
    exact ⟨_, isParam_half P h1, (Cover.hasParam_twist R _).1 h2⟩

end GlobalTheory.CoverExhaust
