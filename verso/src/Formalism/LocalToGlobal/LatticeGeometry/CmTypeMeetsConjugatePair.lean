import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace Formalism.L2.Geo

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem emb_mul_cc_comp {R : Ranks} (H : Host R) (g : R.GG) :
    H.emb (g * R.cc) = (H.emb g).comp (H.conj : H.E →+* H.E) := by
  refine RingHom.ext fun x => ?_
  show H.φ₀ (H.sigmaOf (g * R.cc) x) = H.φ₀ (H.sigmaOf g (H.conj x))
  have : H.sigmaOf (g * R.cc) = H.sigmaOf g * H.conj :=
    map_mul (H.gal).symm g (R.cc)
  rw [this]; rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem mem_Psi_iff_mul_cc_notMem {φ : Formalism.HC.Frame} (g : φ.GG) :
    g ∈ φ.Psi ↔ g * φ.cc ∉ φ.Psi := by
  rw [Formalism.HC.Frame.mem_Psi_iff, Formalism.HC.Frame.mem_Psi_iff]
  show g.1.2 = 1 ↔ ¬ g.1.2 * (-1) = 1
  rcases Int.units_eq_one_or g.1.2 with h | h <;> rw [h] <;> decide

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_tauEmb_iff (D : D7) (g : D.R.GG) :
    (∃ τ0 : D.what₂.Tau, D.host.emb g = DV.tauEmb D τ0) ↔ g ∈ D.R.Psi := by
  constructor
  · rintro ⟨τ0, h⟩
    have := (factEmb D.R D.host).1.1 h
    rw [this]; exact (D.eTau τ0).2
  · intro hg
    refine ⟨D.eTau.symm ⟨g, hg⟩, ?_⟩
    unfold DV.tauEmb
    rw [Equiv.apply_symm_apply]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cm_type_meets_conjugate_pair {D : D7} (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ) (τ : DV.Emb D p) :
    τ ∈ DV.PsiOf D jc ↔ DV.cEmb D τ ∉ DV.PsiOf D jc := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 (jc.comp τ)
  have h1 : τ ∈ DV.PsiOf D jc ↔ g ∈ D.R.Psi := by
    rw [← exists_tauEmb_iff D g, hg]; rfl
  have hc : jc.comp (DV.cEmb D τ) = D.host.emb (g * D.R.cc) := by
    rw [emb_mul_cc_comp, hg]; rfl
  have h2 : DV.cEmb D τ ∈ DV.PsiOf D jc ↔ g * D.R.cc ∈ D.R.Psi := by
    rw [← exists_tauEmb_iff D (g * D.R.cc), ← hc]; rfl
  rw [h1, h2]
  exact mem_Psi_iff_mul_cc_notMem g

end Formalism.L2.Geo
