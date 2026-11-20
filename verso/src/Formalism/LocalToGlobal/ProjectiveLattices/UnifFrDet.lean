import Formalism.LocalToGlobal.ProjectiveLattices.UnifGam

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem perFr_pos (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (ρ : X.Ψ) (i : ℕ)
    (hi : X.p0 + i < r) :
    perFr X x v ρ.1 i = ((mat x ρ)⁻¹ *ᵥ ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 v) ⟨X.p0 + i, hi⟩ := by
  unfold perFr
  rw [dif_pos ρ.2, dif_pos hi]

/- English proof (translation)
Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Substitute using the available equality. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem perFr_neg (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ)
    (hτ : τ ∉ X.Ψ) (ρ : X.Ψ) (hρ : ρ.1 = conjEmb τ) (i : ℕ) (hi : X.p0 - 1 - i < r) :
    perFr X x v τ i = hermC ρ.1 X.Gm (col (mat x ρ) ⟨X.p0 - 1 - i, hi⟩) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 v) := by
  obtain ⟨ρ1, hρ1⟩ := ρ
  simp only at hρ
  subst hρ
  unfold perFr
  rw [dif_neg hτ, dif_pos hρ1, dif_pos hi]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem emb_smul_single (τ : E →+* ℂ) (t : 𝓞 E) (c : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (t • (Pi.single c 1 : Fin r → E)) = τ (t : E) • (Pi.single c 1 : Fin r → ℂ) := by
  funext a
  simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp [Algebra.smul_def]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem hermC_single (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u : Fin r → ℂ) (t : 𝓞 E) (b : Fin r) :
    hermC τ G u (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (t • (Pi.single b 1 : Fin r → E))) =
      (∑ a, u a * τ (G a b)) * (starRingEnd ℂ) (τ (t : E)) := by
  rw [emb_smul_single]
  unfold ReciprocityTheory.ChartRestriction.G.FD.hermC
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single b]
  · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro b' _ hb'
    simp [Pi.single_apply, hb']
  · intro h
    exact absurd (Finset.mem_univ b) h

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mulVec_smul_single (A : Matrix (Fin r) (Fin r) ℂ) (s : ℂ) (b a : Fin r) :
    (A *ᵥ (s • (Pi.single b 1 : Fin r → ℂ))) a = s * A a b := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem conjEmb_conjEmb (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext x
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem conjEmb_eq (τ : E →+* ℂ) : conjEmb τ = ComplexEmbedding.conjugate τ := by
  ext x
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb, NumberField.ComplexEmbedding.conjugate_coe_eq]

end Mat

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Fam

section Final

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Final

section Rows

variable {D : D7}

end Rows

end Formalism.L2.Pj
