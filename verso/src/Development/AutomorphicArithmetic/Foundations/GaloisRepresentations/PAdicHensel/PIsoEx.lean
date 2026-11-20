import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenKGLInvEntries
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

/- English proof (translation)
Introduce `hN hB E _ _ _ A n hn`. Take `⟨m, rfl⟩` from `hn`. Take `⟨x, y, hxy, hint⟩` from `hN E A`. Establish `hinv : ∀ z, cF E (cF E z) = z` using `fun z => GlobalTheory.CompanionTheory.OnlyStab.conjFin_invol z`. Establish `hfix : cF E (algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E)) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E)`.

Use `(conjFin_algebraMap _ _).trans (congrArg _ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsCMField.complexConj E (A.c : E) = (A.c : E)`. Rewrite using `[← A.bar_eq, A.c_real]`. Take `⟨a, ha, hS⟩` from `hB _ (cF E) hinv _ x y hfix hxy m`. Use `⟨a, ?_, ?_⟩` and prove the remaining obligations.

Establish `hd : (Matrix.diagonal fun i => ((A.dg (2 * m + 1) i : 𝓞 E) : E)).map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) = Matrix.diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then 1 else algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E))`. Rewrite using `[Matrix.diagonal_map (map_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, Arith.dg]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[hd]`. Conclude with `ha`. Introduce `w q hq hg hqw`. Take `⟨h1, h2, h3, h4⟩` from `hint w q hq hg hqw`.

Establish `hc : algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) ∈ (w.adicCompletionIntegers E).toSubring.comap (pLoc E w)`. Express the relevant statement in the definitionally equal form `Valued.v (algebraMap E (w.adicCompletion E) (A.c : E)) ≤ 1`. Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (A.c : E)).trans_le (HeightOneSpectrum.valuation_le_one w A.c)`. Establish `hall` using `hS ((w.adicCompletionIntegers E).toSubring.comap (pLoc E w)) h1 h2 h3 h4 hc`. Rewrite using `[GlobalTheory.HenQ.Basic.mem_KGL_iff]`.

Use `⟨fun i j => (hall i j).1, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `(hall i j).2`.
-/
theorem UpperTheory.Gal.G1.pIsoEx :
    NormTwo → BlockMat → IsoEx := by
  intro hN hB E _ _ _ A n hn
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨x, y, hxy, hint⟩ := hN E A
  have hinv : ∀ z, cF E (cF E z) = z := fun z => GlobalTheory.CompanionTheory.OnlyStab.conjFin_invol z
  have hfix : cF E (algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E)) =
      algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) := by
    refine (conjFin_algebraMap _ _).trans (congrArg _ ?_)
    change IsCMField.complexConj E (A.c : E) = (A.c : E)
    rw [← A.bar_eq, A.c_real]
  obtain ⟨a, ha, hS⟩ := hB _ (cF E) hinv _ x y hfix hxy m
  refine ⟨a, ?_, ?_⟩
  · have hd : (Matrix.diagonal fun i => ((A.dg (2 * m + 1) i : 𝓞 E) : E)).map
        (algebraMap E (FiniteAdeleRing (𝓞 E) E)) =
        Matrix.diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then 1 else
          algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E)) := by
      rw [Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      simp only [Function.comp_apply, Arith.dg]
      split_ifs <;> simp
    rw [hd]
    exact ha
  · intro w q hq hg hqw
    obtain ⟨h1, h2, h3, h4⟩ := hint w q hq hg hqw
    have hc : algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) ∈
        (w.adicCompletionIntegers E).toSubring.comap (pLoc E w) := by
      change Valued.v (algebraMap E (w.adicCompletion E) (A.c : E)) ≤ 1
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (A.c : E)).trans_le
        (HeightOneSpectrum.valuation_le_one w A.c)
    have hall := hS ((w.adicCompletionIntegers E).toSubring.comap (pLoc E w)) h1 h2 h3 h4 hc
    rw [GlobalTheory.HenQ.Basic.mem_KGL_iff]
    refine ⟨fun i j => (hall i j).1, fun i j => ?_⟩
    rw [← map_inv]
    exact (hall i j).2
