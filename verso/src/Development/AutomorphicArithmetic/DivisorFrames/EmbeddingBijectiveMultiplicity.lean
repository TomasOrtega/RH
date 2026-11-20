import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCmHostRootNeSelf
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Split into cases according to the possible forms of the given data. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem UpperTheory.embedding_bijective_multiplicity :
    ∀ (D : D7) (O : Setup D), Function.Bijective (fun a : D.what₂.Tau × Bool => (cond a.2 (DV.tauEmb D a.1) (conjEmb (DV.tauEmb D a.1)) : D.host.E →+* ℂ)) ∧ ∀ a : D.what₂.Tau × Bool, O.S.Dw.mult (cond a.2 (DV.tauEmb D a.1) (conjEmb (DV.tauEmb D a.1))) = rkB D.what₂.Tau O.N O.j a := by
  intro D O
  have hc : ∀ t, conjEmb (DV.tauEmb D t) (O.A.H.rt : D.host.E) = (starRingEnd ℂ) O.A.H.rt0 := fun t => by
    simp only [conjEmb, RingHom.coe_comp, Function.comp_apply, O.A.cm t]
  have hne : ∀ t, conjEmb (DV.tauEmb D t) (O.A.H.rt : D.host.E) ≠ O.A.H.rt0 := fun t h =>
    GlobalTheory.CovTop.WtRead.conj_cmHostRoot_ne_self O.A.H ((hc t).symm.trans h)
  have hst : ∀ s t, conjEmb (DV.tauEmb D s) ≠ DV.tauEmb D t := fun s t h =>
    hne s (by rw [h]; exact O.A.cm t)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨s, b⟩ ⟨t, c⟩ h
    cases b <;> cases c
    · have h' : conjEmb (DV.tauEmb D s) = conjEmb (DV.tauEmb D t) := h
      have h2 : DV.tauEmb D s = DV.tauEmb D t := by
        ext x
        have := congrArg (fun σ : D.host.E →+* ℂ => σ x) h'
        simp only [conjEmb, RingHom.coe_comp, Function.comp_apply] at this
        exact (starRingEnd ℂ).injective this
      rw [GlobalTheory.WeightExponents.tauEmb_injective D h2]
    · exact absurd h (hst s t)
    · exact absurd h.symm (hst t s)
    · have h2 : DV.tauEmb D s = DV.tauEmb D t := h
      rw [GlobalTheory.WeightExponents.tauEmb_injective D h2]
  · intro τ
    obtain ⟨t, h | h⟩ := GlobalTheory.CovTop.WtRead.exists_of_places D τ
    · exact ⟨(t, true), h⟩
    · exact ⟨(t, false), h⟩
  · rintro ⟨t, b⟩
    have h1 := O.S.p_eq
    have h2 := O.S.rank_eq
    cases b
    · show O.S.Dw.mult (conjEmb (DV.tauEmb D t)) = _
      unfold Datum.mult
      rw [if_neg (hne t)]
      simp only [rkB, cond_false]
      omega
    · show O.S.Dw.mult (DV.tauEmb D t) = _
      unfold Datum.mult
      rw [if_pos (O.A.cm t)]
      simp only [rkB, cond_true]
      omega
