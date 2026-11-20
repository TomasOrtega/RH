import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)

namespace GlobalTheory.FibreDim

/- English proof (translation)
Introduce `R _ X g hs h`. Use `choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom`. Establish `hn : ∀ x, n x = g` using `fun x => by`. Set `p : PrimeSpectrum R` to `X.hom x`. Establish `hk` using `h p.asIdeal.ResidueField`.

Set `t` to `spMap (algebraMap R p.asIdeal.ResidueField)`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R p.asIdeal.ResidueField)) := by`. Use `⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩` and prove the remaining obligations. Conclude with `Ideal.ker_algebraMap_residueField p.asIdeal`. Use `smoothOfRelativeDimension_isStableUnderBaseChange.{0} (n x)` as an intermediate fact.

Establish `h1 : SmoothOfRelativeDimension (n x) (Limits.pullback.snd ((W x).ι ≫ X.hom) t)` using `this.of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t) (hd x)`. Establish `h2 : SmoothOfRelativeDimension (0 + (0 + g)) (Limits.pullback.snd ((W x).ι ≫ X.hom) t)`. Rewrite using `[← Limits.pullbackRightPullbackFstIso_inv_snd_snd]`. Use `infer_instance`. Take `⟨z, -⟩` from `Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t) ⟨x, hW x⟩ y hy.symm`.

Simplify using `using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2 z`. Establish `: IsZariskiLocalAtSource (@SmoothOfRelativeDimension g)` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_` and prove the remaining obligations. Rewrite using `[← hn x]`. Conclude with `hd x`.
-/
theorem smoothOfRelativeDimension_of_forall_field : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (g : ℕ), Smooth X.hom → (∀ (k : Type) [Field k] [Algebra R k], SmoothOfRelativeDimension g (Limits.pullback.snd X.hom (spMap (algebraMap R k)))) → SmoothOfRelativeDimension g X.hom := by
  intro R _ X g hs h
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom
  have hn : ∀ x, n x = g := fun x => by
    let p : PrimeSpectrum R := X.hom x
    have hk := h p.asIdeal.ResidueField
    let t := spMap (algebraMap R p.asIdeal.ResidueField)
    obtain ⟨y, hy⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R p.asIdeal.ResidueField)) := by
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
      exact Ideal.ker_algebraMap_residueField p.asIdeal
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} (n x)
    have h1 : SmoothOfRelativeDimension (n x) (Limits.pullback.snd ((W x).ι ≫ X.hom) t) :=
      this.of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t) (hd x)
    have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (Limits.pullback.snd ((W x).ι ≫ X.hom) t) := by
      rw [← Limits.pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance
    obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t)
      ⟨x, hW x⟩ y hy.symm
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2 z
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  rw [← hn x]; exact hd x

end GlobalTheory.FibreDim
