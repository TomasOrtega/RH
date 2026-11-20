import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
import Formalism.RealPlaceAnalysis.QuotientSettingHolds

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

/- English proof (translation)
Establish `hOF : OrthogonalFamily ℂ (fun i => A i) fun i => (A i).subtypeₗᵢ` using `fun i j hij v w => horth i j hij _ v.2 _ w.2`. Establish `hind : iSupIndep A` using `by first`. Consider the case `exact hOF.independent`. Consider the case `exact hOF.iSupIndep`. Establish `hint : DirectSum.IsInternal A` using `by first`.

Consider the case `exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top A).mpr ⟨hind, htop⟩`. Consider the case `exact (DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top A).mpr ⟨hind, htop⟩`. Rewrite using `[Module.finrank_eq_card_basis (hint.collectedBasis fun i => Module.finBasis ℂ (A i)), Fintype.card_sigma]`. Simplify using the standard rewrite rules.
-/
theorem finrank_eq_sum_of_orth {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {m : ℕ} (A : Fin m → Submodule ℂ V)
    (horth : ∀ i i', i ≠ i' → ∀ y ∈ A i, ∀ z ∈ A i', ⟪y, z⟫_ℂ = 0) (htop : (⨆ i, A i) = ⊤) :
    Module.finrank ℂ V = ∑ i, Module.finrank ℂ (A i) := by
  classical
  have hOF : OrthogonalFamily ℂ (fun i => A i) fun i => (A i).subtypeₗᵢ :=
    fun i j hij v w => horth i j hij _ v.2 _ w.2
  have hind : iSupIndep A := by
    first
      | exact hOF.independent
      | exact hOF.iSupIndep
  have hint : DirectSum.IsInternal A := by
    first
      | exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top A).mpr ⟨hind, htop⟩
      | exact (DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top A).mpr ⟨hind, htop⟩
  rw [Module.finrank_eq_card_basis (hint.collectedBasis fun i => Module.finBasis ℂ (A i)),
    Fintype.card_sigma]
  simp

/- English proof (translation)
Introduce `n ε R`. Take `⟨hrel, hunit⟩` from `hR n ε R`. Take `⟨m, x, μ, hx, horth, htop⟩` from `Formalism.REAL.kDecomp R.V n ε R.units ⊤ inferInstance hrel hunit (fun a b _ v _ => Submodule.mem_top)`. Use `⟨m, x, μ, fun i => ⟨(hx i).2.1, (hx i).2.2⟩, horth, htop, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `finrank_eq_sum_of_orth _ horth htop`.

Introduce `i k v hv`. Conclude with `(hS n ε R _).mpr (Formalism.REAL.isCompactInvariant_compactSpan (x i)) k v hv`. Introduce `i`. Take `⟨T, φ, h1, h2, h3⟩` from `hP n ε R (μ i) (x i) (hx i).2.1 (hx i).2.2`. Conclude with `⟨T, φ, φ.toLinearEquiv.finrank_eq, h1, h2, h3⟩`.
-/
theorem compRed_of (hR : KRepRelStatement) (hS : KRepStableStatement) (hP : KRepPieceStatement) :
    CompRedStatement := by
  intro n ε R
  obtain ⟨hrel, hunit⟩ := hR n ε R
  obtain ⟨m, x, μ, hx, horth, htop⟩ :=
    Formalism.REAL.kDecomp R.V n ε R.units ⊤ inferInstance hrel hunit (fun a b _ v _ => Submodule.mem_top)
  refine ⟨m, x, μ, fun i => ⟨(hx i).2.1, (hx i).2.2⟩, horth, htop, ?_, ?_, ?_⟩
  · exact finrank_eq_sum_of_orth _ horth htop
  · intro i k v hv
    exact (hS n ε R _).mpr (Formalism.REAL.isCompactInvariant_compactSpan (x i)) k v hv
  · intro i
    obtain ⟨T, φ, h1, h2, h3⟩ := hP n ε R (μ i) (x i) (hx i).2.1 (hx i).2.2
    exact ⟨T, φ, φ.toLinearEquiv.finrank_eq, h1, h2, h3⟩

end ReciprocityTheory.ChartRestriction.DS.HW
