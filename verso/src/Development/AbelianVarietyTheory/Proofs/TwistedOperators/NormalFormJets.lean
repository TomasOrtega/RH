import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePureDataOfCosetIndicatorExpansionsDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestChoiceDatumSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedDefiniteKernelEntriesIsAlgebraicStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

noncomputable section

namespace GlobalTheory.NFJetProof

/- English proof (translation)
Use `haveI : Finite E := hE.to_subtype`. Use `⟨IntermediateField.adjoin ℚ E, IntermediateField.finiteDimensional_adjoin fun z hz => (hA z hz).isIntegral, fun z hz => ⟨⟨z, IntermediateField.subset_adjoin ℚ E hz⟩, rfl⟩⟩` and prove the remaining obligations.
-/
theorem exists_nf_of_finite (E : Set ℂ) (hE : E.Finite) (hA : ∀ z ∈ E, IsAlgebraic ℚ z) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ E ⊆ Set.range (algebraMap M ℂ) := by
  haveI : Finite E := hE.to_subtype
  refine ⟨IntermediateField.adjoin ℚ E, IntermediateField.finiteDimensional_adjoin fun z hz => (hA z hz).isIntegral,
    fun z hz => ⟨⟨z, IntermediateField.subset_adjoin ℚ E hz⟩, rfl⟩⟩

def dset {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ) : Set (PureDat G t) :=
  {d | ∃ τ, IsCosetExpansion S t Φ β k τ ∧ d ∈ τ.support}

end GlobalTheory.NFJetProof

namespace GlobalTheory.NFJetProof

/- English proof (translation)
Establish `hok' : ∀ t Φ, ch.S.SumOK t Φ` using `fun t Φ => by`. Take `⟨a, rfl⟩` from `GlobalTheory.T.rowTestChoice_datum_surjective large₂ F hS ch hch Φ`. Conclude with `hok t a`. Use `haveI : Finite T := hS.fin`. Use `haveI : Finite ch.G.Datum := Finite.of_surjective ch.Phi fun Φ => GlobalTheory.T.rowTestChoice_datum_surjective large₂ F hS ch hch Φ`.

Use `set S := ch.S.toGridChoice with hSdef`. Set `E : Set ℂ` to `⋃ t, ⋃ Φ, ⋃ β ∈ S.supp t Φ, ⋃ d ∈ dset S t Φ β (expDepth S t Φ β), ⋃ c : S.Classes t Φ β, ((⋃ j : Fin D.R.m, ⋃ a, ⋃ b, {S.Z.kk (d.1 j) (S.ptTop c j) (S.ptTop c (j + 1)) a b}) ∪ (⋃ i : Fin D.R.m, ⋃ a, ⋃ b, {S.Z.kk (d.2 i) (S.ptRow c i) (S.ptRow c (i + 1)) a b}))`. Establish `hE : E.Finite`. Use `Set.finite_iUnion fun t => Set.finite_iUnion fun Φ => Set.Finite.biUnion (hok' t Φ).fin fun β _ => Set.Finite.biUnion (GlobalTheory.T.finite_pureData_of_cosetIndicatorExpansions_depth S t Φ β _) fun d _ => ?_` and prove the remaining obligations. Use `haveI := (hok' t Φ).cls β`.

Conclude with `Set.finite_iUnion fun c => Set.Finite.union (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _) (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _)`. Establish `hA : ∀ z ∈ E, IsAlgebraic ℚ z`. Introduce `z hz`. Simplify using `only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop] at hz`. Take `⟨t, Φ, β, hβ, d, ⟨τ, hτ, hdτ⟩, c, h⟩` from `hz`.

Take `⟨hk, hexp, hcos⟩` from `hτ`. Take `⟨e, -, hP, -⟩` from `id hexp`. Establish `hw` using `(hok' t Φ).wts`. Establish `hv` using `(hok' t Φ).vec β τ hexp d hdτ`. Break down `h with ⟨j, a, b, rfl⟩ | ⟨i, a, b, rfl⟩` into its components or cases.

Conclude with `GlobalTheory.T.normalisedDefiniteKernel_entries_isAlgebraic large₂ F hS ch hch hI hD t (.top t j) (show (j : ℕ) + 1 ≤ D.R.m from j.2) (hw j j.2).1 _ (d.1 j) hk ((hcos d hdτ).1 j) ((hP d hdτ).1 j).2.2 ((hP d hdτ).1 j).1 (hv.1 j) _ _ a b`. Conclude with `GlobalTheory.T.normalisedDefiniteKernel_entries_isAlgebraic large₂ F hS ch hch hI hD t (.chi i D.R.m) (show (i : ℕ) + 1 ≤ D.R.m ∧ D.R.m = D.R.m from ⟨i.2, rfl⟩) (hw i i.2).2 _ (d.2 i) hk ((hcos d hdτ).2 i) ((hP d hdτ).2 i).2.2 ((hP d hdτ).2 i).1 (hv.2 i) _ _ a b`. Take `⟨M, hM, hsub⟩` from `exists_nf_of_finite E hE hA`. Use `⟨M, hM, fun t Φ β hβ τ hτ d hd c => ⟨fun j a b => hsub ?_, fun i a b => hsub ?_⟩⟩` and prove the remaining obligations. Simplify using `only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop]`.

Conclude with `⟨t, Φ, β, hβ, d, ⟨τ, hτ, hd⟩, c, Or.inl ⟨j, a, b, rfl⟩⟩`. Simplify using `only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop]`. Conclude with `⟨t, Φ, β, hβ, d, ⟨τ, hτ, hd⟩, c, Or.inr ⟨i, a, b, rfl⟩⟩`.
-/
theorem jetCl_of_choice {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A)
    (hS : HidaSetting large₂ R F) (ch : Choice R) (hch : ch.Is) (hI : GlobalTheory.NormSum.Inp D) (hok : ∀ t a, ch.S.SumOK t (ch.Phi a))
    (hD : GlobalTheory.SumSize.DictAt ch) : InNF fun _ σ => JetCl σ ch.S.toGridChoice := by
  have hok' : ∀ t Φ, ch.S.SumOK t Φ := fun t Φ => by
    obtain ⟨a, rfl⟩ := GlobalTheory.T.rowTestChoice_datum_surjective large₂ F hS ch hch Φ
    exact hok t a
  haveI : Finite T := hS.fin
  haveI : Finite ch.G.Datum := Finite.of_surjective ch.Phi fun Φ => GlobalTheory.T.rowTestChoice_datum_surjective large₂ F hS ch hch Φ
  set S := ch.S.toGridChoice with hSdef
  let E : Set ℂ := ⋃ t, ⋃ Φ, ⋃ β ∈ S.supp t Φ, ⋃ d ∈ dset S t Φ β (expDepth S t Φ β), ⋃ c : S.Classes t Φ β,
    ((⋃ j : Fin D.R.m, ⋃ a, ⋃ b, {S.Z.kk (d.1 j) (S.ptTop c j) (S.ptTop c (j + 1)) a b}) ∪
      (⋃ i : Fin D.R.m, ⋃ a, ⋃ b, {S.Z.kk (d.2 i) (S.ptRow c i) (S.ptRow c (i + 1)) a b}))
  have hE : E.Finite := by
    refine Set.finite_iUnion fun t => Set.finite_iUnion fun Φ => Set.Finite.biUnion (hok' t Φ).fin fun β _ =>
      Set.Finite.biUnion (GlobalTheory.T.finite_pureData_of_cosetIndicatorExpansions_depth S t Φ β _) fun d _ => ?_
    haveI := (hok' t Φ).cls β
    exact Set.finite_iUnion fun c => Set.Finite.union
      (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _)
      (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _)
  have hA : ∀ z ∈ E, IsAlgebraic ℚ z := by
    intro z hz
    simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop] at hz
    obtain ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hdτ⟩, c, h⟩ := hz
    obtain ⟨hk, hexp, hcos⟩ := hτ
    obtain ⟨e, -, hP, -⟩ := id hexp
    have hw := (hok' t Φ).wts
    have hv := (hok' t Φ).vec β τ hexp d hdτ
    rcases h with ⟨j, a, b, rfl⟩ | ⟨i, a, b, rfl⟩
    · exact GlobalTheory.T.normalisedDefiniteKernel_entries_isAlgebraic large₂ F hS ch hch hI hD t (.top t j) (show (j : ℕ) + 1 ≤ D.R.m from j.2) (hw j j.2).1 _ (d.1 j) hk
        ((hcos d hdτ).1 j) ((hP d hdτ).1 j).2.2 ((hP d hdτ).1 j).1 (hv.1 j) _ _ a b
    · exact GlobalTheory.T.normalisedDefiniteKernel_entries_isAlgebraic large₂ F hS ch hch hI hD t (.chi i D.R.m) (show (i : ℕ) + 1 ≤ D.R.m ∧ D.R.m = D.R.m from ⟨i.2, rfl⟩) (hw i i.2).2 _
        (d.2 i) hk ((hcos d hdτ).2 i) ((hP d hdτ).2 i).2.2 ((hP d hdτ).2 i).1 (hv.2 i) _ _ a b
  obtain ⟨M, hM, hsub⟩ := exists_nf_of_finite E hE hA
  refine ⟨M, hM, fun t Φ β hβ τ hτ d hd c => ⟨fun j a b => hsub ?_, fun i a b => hsub ?_⟩⟩
  · simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop]
    exact ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hd⟩, c, Or.inl ⟨j, a, b, rfl⟩⟩
  · simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop]
    exact ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hd⟩, c, Or.inr ⟨i, a, b, rfl⟩⟩

/- English proof (translation)
Introduce `h1 h2 h3`. Take `⟨C, hC⟩` from `Big.and h1 h3`. Use `⟨C, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hC ε CF hCF`. Conclude with `⟨x, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => jetCl_of_choice large₂ F hS ch hch (h2 D) (hx D large₂ he hxx Γ Pl0 T A Ks R F hS ch hch hsc).1 (hx D large₂ he hxx Γ Pl0 T A Ks R F hS ch hch hsc).2⟩`.
-/
theorem nfJet_holds : SumOKK → (∀ D, GlobalTheory.NormSum.Inp D) → (Big fun ch => GlobalTheory.SumSize.DictAt ch) → NFJet := by
  intro h1 h2 h3
  obtain ⟨C, hC⟩ := Big.and h1 h3
  refine ⟨C, fun ε CF hCF => ?_⟩
  obtain ⟨x, hx⟩ := hC ε CF hCF
  exact ⟨x, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc =>
    jetCl_of_choice large₂ F hS ch hch (h2 D) (hx D large₂ he hxx Γ Pl0 T A Ks R F hS ch hch hsc).1
      (hx D large₂ he hxx Γ Pl0 T A Ks R F hS ch hch hsc).2⟩

end GlobalTheory.NFJetProof
