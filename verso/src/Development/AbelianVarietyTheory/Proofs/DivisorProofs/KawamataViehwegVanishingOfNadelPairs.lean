import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Cartier GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NadelApp

/- English proof (translation)
Establish `h0 : toSubscheme I = 0` using `by haveI : IsEmpty I.subscheme := ⟨fun z => h _ (I.range_subschemeι.le ⟨z, rfl⟩)⟩`. Use extensionality with `V t`. Establish `e : I.subschemeι ⁻¹ᵁ V = ⊥` using `eq_bot_iff.2 fun z _ => isEmptyElim z`. Establish `: Subsingleton Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V)`. Rewrite using `[e]`.

Use `infer_instance`. Conclude with `this.elim _ _`. Conclude with `kernel.ι_of_zero h0`.
-/
theorem isIso_idealModuleι_of_forall_notMem {X : Scheme.{0}} (I : X.IdealSheafData)
    (h : ∀ x, x ∉ I.support) : IsIso (idealModuleι I) := by
  have h0 : toSubscheme I = 0 := by
    haveI : IsEmpty I.subscheme := ⟨fun z => h _ (I.range_subschemeι.le ⟨z, rfl⟩)⟩
    ext V t
    have e : I.subschemeι ⁻¹ᵁ V = ⊥ := eq_bot_iff.2 fun z _ => isEmptyElim z
    have : Subsingleton Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) := by
      rw [e]
      infer_instance
    exact this.elim _ _
  exact kernel.ι_of_zero h0

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `: (0 : CartierDiv X).mult z = 0`. Rewrite using `[(CartierDiv.isEqn_zero z).mult_eq]`. Distinguish the cases in `hz : Order.coheight z = 1`. Conclude with `(Scheme.ord_eq_iff hz one_ne_zero).2 (by simp)`.

Conclude with `Scheme.ord_eq_zero_of_coheight_neq_one hz _`. Simplify using `[qWeil, this]`.
-/
theorem qWeil_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (m : ℕ) :
    qWeil (0 : CartierDiv X) m = 0 := by
  funext z
  have : (0 : CartierDiv X).mult z = 0 := by
    rw [(CartierDiv.isEqn_zero z).mult_eq]
    by_cases hz : Order.coheight z = 1
    · exact (Scheme.ord_eq_iff hz one_ne_zero).2 (by simp)
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hz _
  simp [qWeil, this]

/- English proof (translation)
Introduce `hN X p D _ hproj _ K N hnef hbig q hq`. Use `letI := algebraΓOfHom p`. Use `haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hproj`. Take `⟨J, hJ, hv⟩` from `nadel_canonical_add hN X p D hproj K N N hnef.isLB 0 1 1 one_pos one_pos CartierDiv.eff_zero hnef hbig (fun C _ => by`. Rewrite using `[interNumRed_one_eq_zero (isLB_toLB 0) (by rw [← toPic_apply, map_zero])]`.

Use the proof step `simp)`. Use `haveI := isIso_idealModuleι_of_forall_notMem J fun x hx => (hJ x).1 hx (by`. Rewrite using `[qWeil_zero]`. Conclude with `kltAt_zero_of_smooth (topologicalKrullDim_eq_of_smooth X p D) x)`. Conclude with `@Function.Injective.subsingleton _ _ _ (cohOn.mapIso Γ(X, ⊤) ⊤ q ((twistFunctor (tens K.bundle N)).mapIso (asIso (idealModuleι J)))).symm.injective (hv q hq)`.
-/
theorem kawamataViehweg_complex : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → IsIntegral X → ∀ (K : CanonLB p D) (N : LB X), (letI := algebraΓOfHom p; IsNef ℂ N) → (letI := algebraΓOfHom p; IsBig ℂ N) → ∀ q : ℕ, 0 < q → Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  intro hN X p D _ hproj _ K N hnef hbig q hq
  letI := algebraΓOfHom p
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hproj
  obtain ⟨J, hJ, hv⟩ := nadel_canonical_add hN X p D hproj K N N hnef.isLB 0 1 1 one_pos one_pos
    CartierDiv.eff_zero hnef hbig (fun C _ => by
      rw [interNumRed_one_eq_zero (isLB_toLB 0) (by rw [← toPic_apply, map_zero])]
      simp)
  haveI := isIso_idealModuleι_of_forall_notMem J fun x hx => (hJ x).1 hx (by
    rw [qWeil_zero]
    exact kltAt_zero_of_smooth (topologicalKrullDim_eq_of_smooth X p D) x)
  exact @Function.Injective.subsingleton _ _ _ (cohOn.mapIso Γ(X, ⊤) ⊤ q
    ((twistFunctor (tens K.bundle N)).mapIso (asIso (idealModuleι J)))).symm.injective (hv q hq)

end GlobalTheory.NadelApp
