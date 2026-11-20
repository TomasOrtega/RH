import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartSingleton
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AffCurveSum

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] [IsAffine Y] {q : Y ⟶ Sp k}

def evTop (y : Σ σ : k →+* ℂ, CxPts q σ) : Γ(Y, ⊤) →+* ℂ := evHom (y := y.2) mem_ptsIn_top

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem evTop_apply (y : Σ σ : k →+* ℂ, CxPts q σ) (b : Γ(Y, ⊤)) :
    evTop y b = ev q y.1 ⊤ b y.2 := (ev_eq mem_ptsIn_top b).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem evTop_bijective : Function.Bijective (evTop (q := q)) := by
  constructor
  · rintro ⟨σ, y⟩ ⟨σ', y'⟩ h
    have hσ : σ = σ' := RingHom.ext fun a => by
      have := congrArg (fun φ : Γ(Y, ⊤) →+* ℂ => φ (algX q ⊤ a)) h
      simp only [evTop_apply, ev_algX mem_ptsIn_top] at this
      exact this
    subst hσ
    have hy : y = y' := Subtype.ext (Points.ext_of_valR (isAffineOpen_top Y)
      (mem_ptsIn_top : y ∈ ptsIn q σ ⊤) (mem_ptsIn_top : y' ∈ ptsIn q σ ⊤) fun f => by
        have := congrArg (fun φ : Γ(Y, ⊤) →+* ℂ => φ f) h
        simp only [evTop_apply] at this
        exact this)
    rw [hy]
  · intro τ
    refine ⟨⟨τ.comp (algX q ⊤), ofHom (p := q) (σ := τ.comp (algX q ⊤)) (isAffineOpen_top Y) τ
      (fun _ => rfl)⟩, ?_⟩
    ext f
    rw [evTop_apply]
    exact ev_ofHom (p := q) (σ := τ.comp (algX q ⊤)) (isAffineOpen_top Y) τ (fun _ => rfl) f

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem main : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsAffine Y] (q : Y ⟶ Sp k),
    IsArithVar q 0 → ∀ b : Γ(Y, ⊤), ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ,
      Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ =
        ∑ᶠ τ : Γ(Y, ⊤) →+* ℂ, Real.log ‖τ b‖ := by
  intro k _ Y _ _ q hq b
  have := hq.finite_emb
  have (σ : k →+* ℂ) := ArchDimZero.finite_cxPts hq σ
  let := Fintype.ofFinite (k →+* ℂ)
  let (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  let e := Equiv.ofBijective _ (evTop_bijective (q := q))
  have : Finite (Γ(Y, ⊤) →+* ℂ) := .of_equiv _ e
  let := Fintype.ofFinite (Γ(Y, ⊤) →+* ℂ)
  have hv (σ : k →+* ℂ) (y : CxPts q σ) :
      ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y = evTop ⟨σ, y⟩ b := by
    exact (ratVal_fnOf mem_ptsIn_top _ b).trans (evTop_apply ⟨σ, y⟩ b).symm
  simp only [hv, finsum_eq_sum_of_fintype]
  rw [← Fintype.sum_sigma (fun x : (Σ σ : k →+* ℂ, CxPts q σ) => Real.log ‖evTop x b‖)]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

end GlobalTheory.AffCurveSum
