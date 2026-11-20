import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameConjugateFieldsAgree
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapResMap
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.FlagGen
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFrameConjugateFieldsAgree.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.frame_conjugate_fields_agree : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {c : Coeff l} {X : Scheme.{0}} (t : SAB H X) (ty : (E →+* ℂ) → Finset ℕ), (∀ τ k, k ≤ Dw.mult τ → k ∈ ty τ) →
    ∀ {k K Ω : Type} [Field k] [Field K] [Field Ω] (r : k →+* K) (yk : Sp k ⟶ X) (cu : c.F →+* K) (u : Vecs Dw t K),
    GlobalTheory.LocM.IsFrame t cu (spMap r ≫ yk) u →
    ∀ (σ ι : K →+* Ω), σ.comp r = ι.comp r → σ.comp cu = ι.comp cu →
    ∀ (s : ∀ τ, Low (Dw.mult τ) → Ω) (v : Vecs Dw t Ω),
    (∀ τ i, IsCombAtG t (spMap (ι.comp r) ≫ yk) ((u.bc ι) τ) (fun j => uni (s τ) j i) (v τ i)) →
    GlobalTheory.LocM.SameFlag ty t (spMap (ι.comp r) ≫ yk) (u.bc σ) v →
    ∀ τ q, s τ q ∈ Subfield.closure (Set.range ι ∪ Set.range σ) := by
  first | exact @GlobalTheory.FlagField.mem_closure | exact GlobalTheory.FlagField.mem_closure | (intros; apply GlobalTheory.FlagField.mem_closure <;> assumption)
