import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDepthCat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDimFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaEquidim

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `L B _ _ _ _ _ _ _ M _ _ _ _ _ _ r e y hL hy hq hfree hfin`. Use `⟨exists_isRegular_of_free_quotient L B M r e y hL hy hq hfree, ?_⟩` and prove the remaining obligations. Take `⟨xs, hlen, hxs, hreg⟩` from `exists_isRegular_of_free_quotient L B M r e y hL hy hq hfree`. Establish `hys : ∀ z ∈ List.ofFn y, z ∈ maximalIdeal B`. Introduce `z hz`.

Take `⟨i, rfl⟩` from `List.mem_ofFn.mp hz`. Conclude with `hy i`. Establish `h1` using `GlobalTheory.supportDim_le_supportDim_quotient_add_length (M := M) hys`. Rewrite `h1` using `[GlobalTheory.ofList_ofFn_eq_span_range, List.length_ofFn]`. Establish `h2` using `supportDim_le_of_finite L B (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M))`.

Rewrite `h2` using `[hL]`. Establish `hdim : Module.supportDim B M ≤ ((xs.length : ℕ) : WithBot ℕ∞)`. Use `h1.trans ?_` and prove the remaining obligations. Rewrite using `[hlen]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[add_comm]`. Use `norm_cast`. Introduce `Z hZ`. Use `dim_minimalPrime_eq B M xs hxs hreg.toIsWeaklyRegular hdim Z hZ` as an intermediate fact. Rewrite using `[this, hlen]`.
-/
theorem UpperTheory.V.AlgebraTools.patched_depth_dim :
    ∀ (L B : Type) [CommRing L] [IsRegularLocalRing L] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra L B] [IsLocalHom (algebraMap L B)] (M : Type) [AddCommGroup M] [Module B M] [Module L M]
      [IsScalarTower L B M] [Module.Finite B M] [Nontrivial M] (r e : ℕ) (y : Fin r → B),
      ringKrullDim L = e → (∀ i, y i ∈ maximalIdeal B) → GlobalTheory.IsQuasiRegularSeq M y →
      Module.Free L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      Module.Finite L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      (∃ xs : List B, xs.length = r + e ∧ (∀ x ∈ xs, x ∈ maximalIdeal B) ∧ RingTheory.Sequence.IsRegular M xs) ∧
      ∀ Z ∈ (Module.annihilator B M).minimalPrimes, ringKrullDim (B ⧸ Z) = ((r + e : ℕ) : WithBot ℕ∞) := by
  intro L B _ _ _ _ _ _ _ M _ _ _ _ _ _ r e y hL hy hq hfree hfin
  refine ⟨exists_isRegular_of_free_quotient L B M r e y hL hy hq hfree, ?_⟩
  obtain ⟨xs, hlen, hxs, hreg⟩ := exists_isRegular_of_free_quotient L B M r e y hL hy hq hfree
  have hys : ∀ z ∈ List.ofFn y, z ∈ maximalIdeal B := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hy i
  have h1 := GlobalTheory.supportDim_le_supportDim_quotient_add_length (M := M) hys
  rw [GlobalTheory.ofList_ofFn_eq_span_range, List.length_ofFn] at h1
  have h2 := supportDim_le_of_finite L B (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M))
  rw [hL] at h2
  have hdim : Module.supportDim B M ≤ ((xs.length : ℕ) : WithBot ℕ∞) := by
    refine h1.trans ?_
    rw [hlen]
    calc Module.supportDim B (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) + ((r : ℕ) : WithBot ℕ∞)
        ≤ ((e : ℕ) : WithBot ℕ∞) + ((r : ℕ) : WithBot ℕ∞) := by gcongr
      _ = ((r + e : ℕ) : WithBot ℕ∞) := by
        rw [add_comm]; norm_cast
  intro Z hZ
  have := dim_minimalPrime_eq B M xs hxs hreg.toIsWeaklyRegular hdim Z hZ
  rw [this, hlen]
