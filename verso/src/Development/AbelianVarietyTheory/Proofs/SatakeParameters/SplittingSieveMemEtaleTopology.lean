import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfPullbackSndStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFibreFieldPointsCardLEOfIsFiniteIsAffineStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsEmptyOfFibreFieldPointsCardLEZeroStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfIsEmptyPullbackStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemEtaleTopologyOfPullbackFiniteEtaleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsPullbackSndOfSplitsDiagonalComplementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibreFieldPointsCardLEDiagonalComplementSecondPrStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagonalComplementSecondProjectionIsFiniteEtaleStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `Z X f _ _ h`. Establish `: IsEmpty Z` using `GlobalTheory.T.isEmpty_of_fibreFieldPointsCardLE_zero f h`.

Establish `hs : Splits f (𝟙 X ≫ 𝟙 X)` using `GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback f _ (Function.isEmpty (pullback.fst f (𝟙 X ≫ 𝟙 X)))`. Establish `hmem : splitSieve f (𝟙 X) (𝟙 X)` using `⟨X, 𝟙 X, 𝟙 X, hs, Category.id_comp _⟩`. Rewrite `hmem` using `[Sieve.id_mem_iff_eq_top]`. Rewrite using `[hmem]`. Conclude with `(Scheme.etaleTopology).top_mem X`.

Consider the case `succ n ih`. Introduce `Z X f _ _ h`. Take `⟨hfin, het⟩` from `GlobalTheory.T.diagonalComplementSecondProjection_isFinite_etale f`. Establish `hg` using `ih (diagComplHom f) (GlobalTheory.T.fibreFieldPointsCardLE_diagonalComplementSecondProjection f n h)`. Use `GlobalTheory.T.mem_etaleTopology_of_pullback_finite_etale f _ ?_ (fun {V} v hv => ?_)` and prove the remaining obligations.

Use `(Scheme.etaleTopology).superset_covering ?_ hg` and prove the remaining obligations. Introduce and unpack `V u ⟨W, w, v, hv, rfl⟩`. Establish `h1 : Splits (pullback.snd f f) (v ≫ 𝟙 Z)` using `GlobalTheory.T.splits_pullbackSnd_of_splits_diagonalComplement f _ hv`. Establish `h2 : Splits f ((v ≫ 𝟙 Z) ≫ f)` using `GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd f f _ h1`. Conclude with `⟨W, w, v ≫ f, by simpa using h2, by simp⟩`.

Conclude with `⟨V, 𝟙 V, v, by simpa using GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback f v hv, Category.id_comp _⟩`.
-/
theorem splitSieve_mem_of_fibrePointsLE : ∀ (n : ℕ) {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f],
    FibrePointsLE f n → splitSieve f (𝟙 X) ∈ Scheme.etaleTopology X := by
  intro n
  induction n with
  | zero =>
    intro Z X f _ _ h
    have : IsEmpty Z := GlobalTheory.T.isEmpty_of_fibreFieldPointsCardLE_zero f h
    have hs : Splits f (𝟙 X ≫ 𝟙 X) := GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback f _ (Function.isEmpty (pullback.fst f (𝟙 X ≫ 𝟙 X)))
    have hmem : splitSieve f (𝟙 X) (𝟙 X) := ⟨X, 𝟙 X, 𝟙 X, hs, Category.id_comp _⟩
    rw [Sieve.id_mem_iff_eq_top] at hmem
    rw [hmem]; exact (Scheme.etaleTopology).top_mem X
  | succ n ih =>
    intro Z X f _ _ h
    obtain ⟨hfin, het⟩ := GlobalTheory.T.diagonalComplementSecondProjection_isFinite_etale f
    have hg := ih (diagComplHom f) (GlobalTheory.T.fibreFieldPointsCardLE_diagonalComplementSecondProjection f n h)
    refine GlobalTheory.T.mem_etaleTopology_of_pullback_finite_etale f _ ?_ (fun {V} v hv => ?_)
    · refine (Scheme.etaleTopology).superset_covering ?_ hg
      rintro V u ⟨W, w, v, hv, rfl⟩
      have h1 : Splits (pullback.snd f f) (v ≫ 𝟙 Z) := GlobalTheory.T.splits_pullbackSnd_of_splits_diagonalComplement f _ hv
      have h2 : Splits f ((v ≫ 𝟙 Z) ≫ f) := GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd f f _ h1
      exact ⟨W, w, v ≫ f, by simpa using h2, by simp⟩
    · exact ⟨V, 𝟙 V, v, by simpa using GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback f v hv, Category.id_comp _⟩

/- English proof (translation)
Introduce `Z X S f _ _ x`. Set `𝒰` to `S.affineCover`. Establish `hU : Sieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.etaleTopology S` using `Scheme.zariskiTopology_le_etaleTopology _ (𝒰.mem_grothendieckTopology)`. Use `(Scheme.etaleTopology).transitive hU _ ?_` and prove the remaining obligations. Introduce and unpack `Y u ⟨W, w, _, ⟨i⟩, rfl⟩`.

Rewrite using `[Sieve.pullback_comp]`. Use `(Scheme.etaleTopology).pullback_stable w ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `GlobalTheory.T.exists_fibreFieldPointsCardLE_of_isFinite_isAffine (pullback.snd f (𝒰.f i ≫ x))`. Establish `hi` using `splitSieve_mem_of_fibrePointsLE n (pullback.snd f (𝒰.f i ≫ x)) hn`. Use `(Scheme.etaleTopology).superset_covering ?_ hi` and prove the remaining obligations.

Introduce and unpack `V u ⟨W', w', v, hv, rfl⟩`. Establish `h1` using `GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd f (𝒰.f i ≫ x) (v ≫ 𝟙 _) hv`. Conclude with `⟨W', w', v ≫ 𝒰.f i, by simpa using h1, by simp⟩`.
-/
theorem splitSieve_mem : ∀ {Z X S : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (x : S ⟶ X),
    splitSieve f x ∈ Scheme.etaleTopology S := by
  intro Z X S f _ _ x
  let 𝒰 := S.affineCover
  have hU : Sieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.etaleTopology S :=
    Scheme.zariskiTopology_le_etaleTopology _ (𝒰.mem_grothendieckTopology)
  refine (Scheme.etaleTopology).transitive hU _ ?_
  rintro Y u ⟨W, w, _, ⟨i⟩, rfl⟩
  rw [Sieve.pullback_comp]
  refine (Scheme.etaleTopology).pullback_stable w ?_
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_fibreFieldPointsCardLE_of_isFinite_isAffine (pullback.snd f (𝒰.f i ≫ x))
  have hi := splitSieve_mem_of_fibrePointsLE n (pullback.snd f (𝒰.f i ≫ x)) hn
  refine (Scheme.etaleTopology).superset_covering ?_ hi
  rintro V u ⟨W', w', v, hv, rfl⟩
  have h1 := GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd f (𝒰.f i ≫ x) (v ≫ 𝟙 _) hv
  exact ⟨W', w', v ≫ 𝒰.f i, by simpa using h1, by simp⟩

end GlobalTheory.EtC.Tr
