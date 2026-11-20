import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitDivisibleOfVanishingLevelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfLseqFirstStatement
import ReciprocityTheory.GroupCohomology.FinGen

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerLim

/- English proof (translation)
Introduce `W _ l _ S S' L h1`. Establish `hfl` using `GlobalTheory.T.finite_length_of_lseq_first W l S S' L h1`. Establish `hart : ∀ n, IsArtinian W (S.M n)` using `fun n => (isFiniteLength_iff_isNoetherian_isArtinian.1 (hfl n)).2`. Establish `hinj` using `GlobalTheory.T.limit_divisible_of_vanishing_level W l S S' L hart`. Establish `hvan : ∀ n, (Ideal.span {(l : W)} ^ n • (⊤ : Submodule W S.lim)) ≤ LinearMap.ker (pr S n)`.

Introduce `n`. Use `Submodule.smul_le.2 fun r hr m _ => ?_` and prove the remaining obligations. Rewrite `hr` using `[Ideal.span_singleton_pow]`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hr`. Rewrite using `[LinearMap.mem_ker, map_smul, mul_smul]`.

Rewrite using `[L.kill n, smul_zero]`. Establish `hH : IsHausdorff (Ideal.span {(l : W)}) S.lim`. Use `⟨fun x hx => Subtype.ext (funext fun n => ?_)⟩` and prove the remaining obligations. Establish `hm : x ∈ (Ideal.span {(l : W)} ^ n • (⊤ : Submodule W S.lim))`. Simplify `hx n` using `[SModEq.zero]`.

Conclude with `hvan n hm`. Establish `hmem1 : ∀ x : S.lim, pr S 1 x = 0 → x ∈ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)`. Introduce `x hx`. Take `⟨y, hy⟩` from `hinj 1 x hx`. Rewrite using `[hy, pow_one]`.

Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial`. Establish `hle : Ideal.span {(l : W)} • (⊤ : Submodule W S.lim) ≤ LinearMap.ker (pr S 1)`. Simplify using `using hvan 1`. Set `q` to `(Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)).liftQ (pr S 1) hle`. Establish `hq : Function.Injective q`.

Use `(injective_iff_map_eq_zero _).2 fun z hz => ?_` and prove the remaining obligations. Proceed by induction on `z using Submodule.Quotient.induction_on with`. Consider the case `H x`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `hmem1 x hz`.

Establish `: IsNoetherian W (S.M 1)` using `(isFiniteLength_iff_isNoetherian_isArtinian.1 h1).1`. Establish `: Module.Finite W (S.lim ⧸ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim))` using `Module.Finite.of_injective q hq`. Take `⟨r, s, hs⟩` from `Module.Finite.exists_fin (R := W) (M := S.lim ⧸ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim))`. Use `choose s' hs' using fun i => Submodule.Quotient.mk_surjective _ (s i)`. Establish `: IsPrecomplete (Ideal.span {(l : W)}) (Fin r → W)` using `ReciprocityTheory.Coh.isPrecomplete_pi _`.

Establish `hsurj : Function.Surjective ((Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)).mkQ ∘ₗ Fintype.linearCombination W s')`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨Pi.single i 1, by simp [hs']⟩`. Conclude with `Module.Finite.of_surjective _ (surjective_of_mkQ_comp_surjective hsurj)`.
-/
theorem module_finite_lim : ∀ (W : Type) [CommRing W] (l : ℕ) [IsAdicComplete (Ideal.span {(l : W)}) W]
    (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → Module.Finite W S.lim := by
  intro W _ l _ S S' L h1
  have hfl := GlobalTheory.T.finite_length_of_lseq_first W l S S' L h1
  have hart : ∀ n, IsArtinian W (S.M n) := fun n =>
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (hfl n)).2
  have hinj := GlobalTheory.T.limit_divisible_of_vanishing_level W l S S' L hart

  have hvan : ∀ n, (Ideal.span {(l : W)} ^ n • (⊤ : Submodule W S.lim)) ≤ LinearMap.ker (pr S n) := by
    intro n
    refine Submodule.smul_le.2 fun r hr m _ => ?_
    rw [Ideal.span_singleton_pow] at hr
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [LinearMap.mem_ker, map_smul, mul_smul]
    rw [L.kill n, smul_zero]
  have hH : IsHausdorff (Ideal.span {(l : W)}) S.lim := by
    refine ⟨fun x hx => Subtype.ext (funext fun n => ?_)⟩
    have hm : x ∈ (Ideal.span {(l : W)} ^ n • (⊤ : Submodule W S.lim)) := by
      simpa [SModEq.zero] using hx n
    exact hvan n hm
  have hmem1 : ∀ x : S.lim, pr S 1 x = 0 → x ∈ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim) := by
    intro x hx
    obtain ⟨y, hy⟩ := hinj 1 x hx
    rw [hy, pow_one]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  have hle : Ideal.span {(l : W)} • (⊤ : Submodule W S.lim) ≤ LinearMap.ker (pr S 1) := by
    simpa using hvan 1
  let q := (Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)).liftQ (pr S 1) hle
  have hq : Function.Injective q := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.Quotient.mk_eq_zero]
      exact hmem1 x hz
  have : IsNoetherian W (S.M 1) := (isFiniteLength_iff_isNoetherian_isArtinian.1 h1).1
  have : Module.Finite W (S.lim ⧸ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)) :=
    Module.Finite.of_injective q hq
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := W)
    (M := S.lim ⧸ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim))
  choose s' hs' using fun i => Submodule.Quotient.mk_surjective _ (s i)
  have : IsPrecomplete (Ideal.span {(l : W)}) (Fin r → W) := ReciprocityTheory.Coh.isPrecomplete_pi _
  have hsurj : Function.Surjective ((Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)).mkQ ∘ₗ
      Fintype.linearCombination W s') := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, by simp [hs']⟩
  exact Module.Finite.of_surjective _ (surjective_of_mkQ_comp_surjective hsurj)

end GlobalTheory.CompanionTheory.TowerLim
