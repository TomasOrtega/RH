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
Unfold `perFr`. Rewrite using `[dif_pos ρ.2, dif_pos hi]`.
-/
theorem perFr_pos (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (ρ : X.Ψ) (i : ℕ)
    (hi : X.p0 + i < r) :
    perFr X x v ρ.1 i = ((mat x ρ)⁻¹ *ᵥ ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 v) ⟨X.p0 + i, hi⟩ := by
  unfold perFr
  rw [dif_pos ρ.2, dif_pos hi]

/- English proof (translation)
Take `⟨ρ1, hρ1⟩` from `ρ`. Simplify using `only at hρ`. Substitute `hρ` using the available equality. Unfold `perFr`. Rewrite using `[dif_neg hτ, dif_pos hρ1, dif_pos hi]`.
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
Use function extensionality and compare the values at `a`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Pi.smul_apply, Pi.single_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp [Algebra.smul_def]`.
-/
theorem emb_smul_single (τ : E →+* ℂ) (t : 𝓞 E) (c : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (t • (Pi.single c 1 : Fin r → E)) = τ (t : E) • (Pi.single c 1 : Fin r → ℂ) := by
  funext a
  simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp [Algebra.smul_def]

/- English proof (translation)
Rewrite using `[emb_smul_single]`. Unfold `ReciprocityTheory.ChartRestriction.G.FD.hermC`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single b]`.

Simplify using `only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]`. Introduce `b' _ hb'`. Simplify using `[Pi.single_apply, hb']`. Introduce `h`. Conclude with `absurd (Finset.mem_univ b) h`.
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
Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]`.
-/
theorem mulVec_smul_single (A : Matrix (Fin r) (Fin r) ℂ) (s : ℂ) (b a : Fin r) :
    (A *ᵥ (s • (Pi.single b 1 : Fin r → ℂ))) a = s * A a b := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb]`.
-/
theorem conjEmb_conjEmb (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext x
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb, NumberField.ComplexEmbedding.conjugate_coe_eq]`.
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
