import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitRowAt

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open Classical

namespace GlobalTheory.SplitDecl

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem embTypeUc_iff (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    EmbeddingTypes.EmbTypeUc τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i false w hw τ := by
  constructor
  · rintro ⟨h1, φ, hφ, h2⟩
    refine ⟨h1, (starRingEnd ℂ).comp φ, ?_, fun x y hy => by simpa using h2 x y hy⟩
    show ((starRingEnd ℂ).comp φ).comp (D.host.conj : D.host.E →+* D.host.E) ∈
      D.host.cmType
    have : ((starRingEnd ℂ).comp φ).comp (D.host.conj : D.host.E →+* D.host.E) = φ := by
      ext1 x
      simp [GlobalTheory.SplitRowProbe.conj_sqrt]
    rw [this]; exact hφ
  · rintro ⟨h1, ψ, hψ, h2⟩
    refine ⟨h1, ψ.comp (D.host.conj : D.host.E →+* D.host.E), hψ, fun x y hy => ?_⟩
    rw [h2 x y hy]
    simp [GlobalTheory.SplitRowProbe.conj_sqrt]

/- English proof (translation)
Split into cases according to the possible forms of the given data. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem embTypeUe_iff (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    EmbeddingTypes.EmbTypeUe ep τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i ep w hw τ := by
  cases ep
  · simp only [EmbeddingTypes.EmbTypeUe, Bool.false_eq_true, if_false]
    exact embTypeUc_iff τ
  · simp only [EmbeddingTypes.EmbTypeUe, if_true]
    rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem plTypeUe_iff (ep : Bool) :
    EmbeddingTypes.PlTypeUe i w hw ep ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.PlIn (N := D.nd) D.nbr i ep w hw := by
  constructor
  · intro h
    exact ⟨GlobalTheory.SplitRowProbe.nonempty_emb D i w hw, fun τ => (embTypeUe_iff ep τ).1 (h τ)⟩
  · intro h τ
    exact (embTypeUe_iff ep τ).2 (h.2 τ)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem placesOver_finite (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

def decl (D : D7) (i : D.nd.Loc) (hl : D.nd.l i ≠ 0) (ep : Bool) : TruncatedSeriesCountingIdentities.Decl D i where
  row := (placesOver_finite D.host.E (D.nd.l i) hl).toFinset.filter
    (fun v => v ∉ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep)
  col := (placesOver_finite D.host.E (D.nd.l i) hl).toFinset.filter
    (fun v => v ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep)
  disj := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    exact (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
  cover := by
    intro v
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    tauto

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_col (D : D7) (i : D.nd.Loc) (hl : D.nd.l i ≠ 0) (ep : Bool) (v) :
    v ∈ (decl D i hl ep).col ↔ v ∈ placesOver D.host.E (D.nd.l i) ∧
      v ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep := by
  simp [decl]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_row (D : D7) (i : D.nd.Loc) (hl : D.nd.l i ≠ 0) (ep : Bool) (v) :
    v ∈ (decl D i hl ep).row ↔ v ∈ placesOver D.host.E (D.nd.l i) ∧
      v ∉ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep := by
  simp [decl]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem main : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) →
    (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.hypL i := by
  intro D i ep hs
  obtain ⟨hPl, hTy⟩ := GlobalTheory.SplitRowAll.splitRow_at D
  have hP := hPl _ hs
  have hT := hTy i hs
  have hl : D.nd.l i ≠ 0 := hs.1.ne_zero
  refine ⟨⟨decl D i hl ep, ?_, ?_⟩, ?_⟩
  · intro v hv
    rw [mem_col, plTypeUe_iff]
    constructor
    · rintro ⟨-, hv', h⟩
      exact h
    · intro h
      exact ⟨hv, hv, h⟩
  · intro v
    rw [mem_row]
    constructor
    · rintro ⟨hv, hnc⟩
      obtain ⟨-, ⟨v', hv', hc⟩, -⟩ := hP v hv
      have hx := (hT.2.2.2 ep).1 v hv v' hc
      have hv'c : v' ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep := by
        rcases hx with h | h
        · exact absurd h.1 hnc
        · exact h.1
      exact ⟨v', (mem_col D i hl ep v').2 ⟨hv', hv'c⟩, GlobalTheory.Proof.ConjugatePlaces.isConjPl_symm hc⟩
    · rintro ⟨u, hu, hc⟩
      obtain ⟨hu, huc⟩ := (mem_col D i hl ep u).1 hu
      obtain ⟨-, ⟨u', hu', hc'⟩, -⟩ := hP u hu
      have he : v = u' := GlobalTheory.Proof.ConjugatePlaces.isConjPl_unique hc hc'
      subst he
      refine ⟨hu', fun hvc => ?_⟩
      rcases (hT.2.2.2 ep).1 u hu v hc with h | h
      · exact h.2 hvc
      · exact h.2 huc
  · obtain ⟨-, h5, -, -, hg, hcls⟩ := hs
    exact ⟨le_trans (by norm_num) h5, Or.inl hcls, fun _ v hv => (hP v hv).1, hg 0, hg 1⟩

end GlobalTheory.SplitDecl

end
