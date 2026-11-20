import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

open NumberField.InfinitePlace in
/- English proof (translation)
Set `m : mixedEmbedding.mixedSpace L` to `(0, fun w => z w.1)`. Set `c` to `(mixedEmbedding.latticeBasis L).repr m`. Use `⟨fun i => c i, fun w => ?_⟩` and prove the remaining obligations. Establish `hw : w.IsComplex` using `IsTotallyComplex.isComplex w`. Establish `hsum` using `(mixedEmbedding.latticeBasis L).sum_repr m`.

Establish `h2` using `congrArg (fun p : mixedEmbedding.mixedSpace L => p.2 ⟨w, hw⟩) hsum`. Simplify using `only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply, mixedEmbedding.latticeBasis_apply, mixedEmbedding.mixedEmbedding_apply_isComplex, integralBasis_apply, Complex.real_smul, m] at h2`. Rewrite using `[← h2]`. Both sides reduce to the same expression.
-/
private theorem one_coord (L : Type) [Field L] [NumberField L] [IsTotallyComplex L]
    (z : InfinitePlace L → ℂ) :
    ∃ x : BI L → ℝ, ∀ w, ∑ i, (x i : ℂ) * embO w (RingOfIntegers.basis L i) = z w := by
  classical
  let m : mixedEmbedding.mixedSpace L := (0, fun w => z w.1)
  let c := (mixedEmbedding.latticeBasis L).repr m
  refine ⟨fun i => c i, fun w => ?_⟩
  have hw : w.IsComplex := IsTotallyComplex.isComplex w
  have hsum := (mixedEmbedding.latticeBasis L).sum_repr m
  have h2 := congrArg (fun p : mixedEmbedding.mixedSpace L => p.2 ⟨w, hw⟩) hsum
  simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply,
    mixedEmbedding.latticeBasis_apply, mixedEmbedding.mixedEmbedding_apply_isComplex,
    integralBasis_apply, Complex.real_smul, m] at h2
  rw [← h2]
  rfl

/- English proof (translation)
Introduce `L _ _ _ N z`. Use `choose x hx using fun a : Fin N => one_coord L (fun w => z w a)`. Conclude with `⟨fun s => x s.1 s.2, funext fun w => funext fun a => hx a w⟩`.
-/
theorem UpperTheory.V.KT.realsurj :
    ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ),
    Function.Surjective (realVec : (Fin N × BI L → ℝ) → VR L N) := by
  intro L _ _ _ N z
  choose x hx using fun a : Fin N => one_coord L (fun w => z w a)
  exact ⟨fun s => x s.1 s.2, funext fun w => funext fun a => hx a w⟩
