import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj.RatLin

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac MvPolynomial

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frac_smul {N : ℕ} (V : (PSpace ℂ N).Opens) (f g : MvPolynomial (Fin (N + 1)) ℂ)
    (hf : f ∈ grading ℂ N 1) (hg : g ∈ grading ℂ N 1) (hV : V ≤ Proj.basicOpen (grading ℂ N) g) (c : ℂ)
    (hcf : c • f ∈ grading ℂ N 1) :
    frac (grading ℂ N) V (c • f) g hcf hg hV =
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (PSpace.str ℂ N).appLE ⊤ V le_top).hom c *
        frac (grading ℂ N) V f g hf hg hV := by
  rw [← algebraMap_sections_eq]
  refine ext fun x hx => ?_
  obtain ⟨i, hi⟩ := exists_mem_chart ℂ N x
  have hW : V ⊓ chart ℂ N i ≤ V := inf_le_left
  have hxW : x ∈ V ⊓ chart ℂ N i := ⟨hx, hi⟩
  rw [← ev_resG hW x hxW, ← ev_resG hW x hxW, map_mul, resG_algebraMap, resG_frac, resG_frac,
    ← formOn_C (hi := (inf_le_right : V ⊓ chart ℂ N i ≤ chart ℂ N i)), formOn]
  congr 1
  refine (frac_mul_eq ?_).symm
  rw [smul_eq_C_mul]
  ring

/- English proof (translation)
Substitute using the available equality. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem app_const {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N : ℕ} (ι : X ⟶ PSpace ℂ N) (hι : ι ≫ PSpace.str ℂ N = p)
    (V : (PSpace ℂ N).Opens) (c : ℂ) :
    (ι.app V).hom (((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (PSpace.str ℂ N).appLE ⊤ V le_top).hom c) =
      algebraMap ℂ (Sec p (ι ⁻¹ᵁ V)) c := by
  subst hι
  change _ = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (ι ≫ PSpace.str ℂ N).appLE ⊤ (ι ⁻¹ᵁ V) _).hom c
  rw [Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fRatio_add {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace ℂ N) (f₁ f₂ g : MvPolynomial (Fin (N + 1)) ℂ)
    (h₁ : f₁ ∈ grading ℂ N 1) (h₂ : f₂ ∈ grading ℂ N 1) (h : f₁ + f₂ ∈ grading ℂ N 1)
    (hg : g ∈ grading ℂ N 1) :
    fRatio ι (f₁ + f₂) g h hg = fRatio ι f₁ g h₁ hg + fRatio ι f₂ g h₂ hg := by
  unfold fRatio
  rw [frac_add (ha := h₁) (ha₂ := h₂)]
  exact map_add _ _ _

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fRatio_zero {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace ℂ N) (g : MvPolynomial (Fin (N + 1)) ℂ)
    (h : (0 : MvPolynomial (Fin (N + 1)) ℂ) ∈ grading ℂ N 1) (hg : g ∈ grading ℂ N 1) :
    fRatio ι 0 g h hg = 0 := by
  unfold fRatio
  rw [frac_zero]
  exact map_zero _

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem fRatio_smul {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N : ℕ} (ι : X ⟶ PSpace ℂ N)
    (hι : ι ≫ PSpace.str ℂ N = p) (f g : MvPolynomial (Fin (N + 1)) ℂ) (c : ℂ)
    (hf : f ∈ grading ℂ N 1) (h : c • f ∈ grading ℂ N 1) (hg : g ∈ grading ℂ N 1) :
    (show Sec p (fOpen ι g) from fRatio ι (c • f) g h hg) = c • (show Sec p (fOpen ι g) from fRatio ι f g hf hg) := by
  have e := app_const p ι hι (Proj.basicOpen (grading ℂ N) g) c
  refine Eq.trans ?_ (Algebra.smul_def (A := Sec p (fOpen ι g)) c _).symm
  refine Eq.trans ?_ (congrArg (· * (show Sec p (fOpen ι g) from fRatio ι f g hf hg)) e)
  unfold fRatio
  rw [frac_smul _ f g hf hg le_rfl c h]
  exact map_mul _ _ _

end GlobalTheory.EtProj.RatLin

open GlobalTheory.EtProj.RatLin in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem GlobalTheory.EtProj.fRatio_linear : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N), ι ≫ PSpace.str ℂ N = p → ∀ (g : MvPolynomial (Fin (N + 1)) ℂ) (hg : g ∈ GlobalTheory.ProjSpace.grading ℂ N 1) (c : Fin (N + 1) → ℂ) (hf : (∑ l, c l • MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1), let U := GlobalTheory.EtProj.fOpen ι g; let q : Sec p U := GlobalTheory.EtProj.fRatio ι (∑ l, c l • MvPolynomial.X l) g hf hg; let r : Fin (N + 1) → Sec p U := fun l => GlobalTheory.EtProj.fRatio ι (MvPolynomial.X l) g (GlobalTheory.ProjSpace.X_mem ℂ N l) hg; q = ∑ l, c l • r l := by
  intro X p N ι hι g hg c hf U q r
  have key : ∀ (s : Finset (Fin (N + 1)))
      (h : (∑ l ∈ s, c l • MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1),
      (show Sec p U from GlobalTheory.EtProj.fRatio ι (∑ l ∈ s, c l • MvPolynomial.X l) g h hg) = ∑ l ∈ s, c l • r l := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro h
      simp only [Finset.sum_empty]
      exact fRatio_zero ι g _ hg
    | insert a s ha ih =>
      intro h
      have hs : (∑ l ∈ s, c l • MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1 :=
        Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (GlobalTheory.ProjSpace.X_mem ℂ N l)
      have ha' : (c a • MvPolynomial.X a : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1 :=
        Submodule.smul_mem _ _ (GlobalTheory.ProjSpace.X_mem ℂ N a)
      simp only [Finset.sum_insert ha]
      rw [fRatio_add ι _ _ g ha' hs _ hg, ← ih hs]
      congr 1
      exact fRatio_smul p ι hι _ g (c a) (GlobalTheory.ProjSpace.X_mem ℂ N a) ha' hg
  exact key Finset.univ hf
