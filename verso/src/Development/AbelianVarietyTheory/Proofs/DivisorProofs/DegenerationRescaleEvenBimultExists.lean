import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalFunctionOfHomomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescalePsiEvenTauBimultIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomEvenDefectBimultiplicativePeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfRankOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationRescaleTauBimultExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalFunctionLiftUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiScalingIntegralRescaleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.UnitPsi

/- English proof (translation)
Unfold `GlobalTheory.PolDeg.rescale`. Use `congr 1`. Use function extensionality and compare the values at `χ`. Unfold `GlobalTheory.UU.scaleGen`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Establish `hu : unitOn (g' χ * g χ) = unitOn (g' χ) * unitOn (g χ)` using `map_mul _ _ _`. Express the relevant statement in the definitionally equal form `_ * (_ * (D.psi χ).s j) = _`. Rewrite using `[hu, map_mul, _root_.mul_assoc]`.
-/
theorem rescale_rescale {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (g' : (GlobalTheory.PolDeg.rescale D g).X → (FractionRing R)ˣ) :
    GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) g' = GlobalTheory.PolDeg.rescale D (fun χ => g' χ * g χ) := by
  unfold GlobalTheory.PolDeg.rescale
  congr 1
  funext χ
  unfold GlobalTheory.UU.scaleGen
  congr 1
  funext j
  have hu : unitOn (g' χ * g χ) = unitOn (g' χ) * unitOn (g χ) := map_mul _ _ _
  change _ * (_ * (D.psi χ).s j) = _
  rw [hu, map_mul, _root_.mul_assoc]

/- English proof (translation)
Take `⟨h, hh, hE⟩` from `GlobalTheory.DefectHom.exists_evenDefect_hom R D hB`. Take `⟨k, hk3, hkn⟩` from `GlobalTheory.T.cubical_function_of_homomorphism D.X (FractionRing R)ˣ (fun a => (h a)⁻¹) (fun a b => by rw [hh, mul_inv])`. Use `⟨k, ?_, ((GlobalTheory.T.rescale_psi_even_tau_bimult_iff R D k).2 hB).2 hk3⟩` and prove the remaining obligations. Establish `e` using `GlobalTheory.PolDeg.evenDefect_rescale D h k hE`. Establish `e1 : (fun χ : D.X => h χ * k (-χ) * (k χ)⁻¹) = fun _ => 1`.

Use function extensionality and compare the values at `χ`. Rewrite using `[hkn χ, mul_inv_cancel_left, mul_inv_cancel]`. Rewrite `e` using `[e1]`. Conclude with `(GlobalTheory.PolDeg.evenDefect_one_iff _).1 e`.
-/
theorem even_step (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R) (hB : D.TauBimult) :
    ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).PsiEven ∧ (GlobalTheory.PolDeg.rescale D g).TauBimult := by
  obtain ⟨h, hh, hE⟩ := GlobalTheory.DefectHom.exists_evenDefect_hom R D hB
  obtain ⟨k, hk3, hkn⟩ := GlobalTheory.T.cubical_function_of_homomorphism D.X (FractionRing R)ˣ (fun a => (h a)⁻¹) (fun a b => by rw [hh, mul_inv])
  refine ⟨k, ?_, ((GlobalTheory.T.rescale_psi_even_tau_bimult_iff R D k).2 hB).2 hk3⟩
  have e := GlobalTheory.PolDeg.evenDefect_rescale D h k hE
  have e1 : (fun χ : D.X => h χ * k (-χ) * (k χ)⁻¹) = fun _ => 1 := by
    funext χ
    rw [hkn χ, mul_inv_cancel_left, mul_inv_cancel]
  rw [e1] at e
  exact (GlobalTheory.PolDeg.evenDefect_one_iff _).1 e

/- English proof (translation)
Take `⟨ga, a, hs⟩` from `GlobalTheory.exists_psiScal R D`. Take `⟨h3, h2⟩` from `GlobalTheory.PsiScalUnit.main R D ga a hs`. Set `e : Rˣ →* (FractionRing R)ˣ` to `Units.map (algebraMap R (FractionRing R)).toMonoidHom`. Establish `he : Function.Injective e` using `fun u v e => Units.ext (IsFractionRing.injective R (FractionRing R) (congrArg Units.val e))`. Take `⟨c, hc3, hce, hci⟩` from `GlobalTheory.T.cubical_function_lift_units D.X Rˣ (FractionRing R)ˣ e he a (fun x y w => by`.

Take `⟨u, hu⟩` from `h3 hB x y w`. Conclude with `⟨u, Units.ext (by rw [Units.val_mul]; exact hu)⟩)`. Use the proof step `(fun x => by`. Take `⟨u, hu⟩` from `h2 hE x`. Conclude with `⟨u, Units.ext (by rw [Units.val_mul]; exact hu)⟩)`.

Conclude with `⟨c, ((GlobalTheory.T.rescale_psi_even_tau_bimult_iff R D c).1 hE).2 hce, ((GlobalTheory.T.rescale_psi_even_tau_bimult_iff R D c).2 hB).2 hc3, GlobalTheory.T.psi_scaling_integral_rescale R D ga a hs c hci⟩`.
-/
theorem top_step (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (hE : D.PsiEven)
    (hB : D.TauBimult) : ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).PsiEven ∧
      (GlobalTheory.PolDeg.rescale D g).TauBimult ∧ Nonempty (PsiOn (GlobalTheory.PolDeg.rescale D g) ⊤) := by
  obtain ⟨ga, a, hs⟩ := GlobalTheory.exists_psiScal R D
  obtain ⟨h3, h2⟩ := GlobalTheory.PsiScalUnit.main R D ga a hs
  let e : Rˣ →* (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom
  have he : Function.Injective e := fun u v e =>
    Units.ext (IsFractionRing.injective R (FractionRing R) (congrArg Units.val e))
  obtain ⟨c, hc3, hce, hci⟩ := GlobalTheory.T.cubical_function_lift_units D.X Rˣ (FractionRing R)ˣ e he a
    (fun x y w => by
      obtain ⟨u, hu⟩ := h3 hB x y w
      exact ⟨u, Units.ext (by rw [Units.val_mul]; exact hu)⟩)
    (fun x => by
      obtain ⟨u, hu⟩ := h2 hE x
      exact ⟨u, Units.ext (by rw [Units.val_mul]; exact hu)⟩)
  exact ⟨c, ((GlobalTheory.T.rescale_psi_even_tau_bimult_iff R D c).1 hE).2 hce, ((GlobalTheory.T.rescale_psi_even_tau_bimult_iff R D c).2 hB).2 hc3,
    GlobalTheory.T.psi_scaling_integral_rescale R D ga a hs c hci⟩

/- English proof (translation)
Introduce `R _ _ _ _ D`. Take `⟨g₁, h₁⟩` from `GlobalTheory.T.degeneration_rescale_tau_bimult_exists R D`. Take `⟨g₂, e₂, b₂⟩` from `even_step R (GlobalTheory.PolDeg.rescale D g₁) h₁`. Take `⟨g₃, e₃, b₃, p₃⟩` from `top_step R _ e₂ b₂`. Use `⟨fun χ => g₃ χ * g₂ χ * g₁ χ, ?_⟩` and prove the remaining obligations.

Rewrite `e₃`, `b₃`, `p₃` using `[rescale_rescale, rescale_rescale]`. Conclude with `⟨e₃, b₃, p₃⟩`.
-/
theorem exists_rescale_even_bimult_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D : DegPre R), ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).PsiEven ∧
      (GlobalTheory.PolDeg.rescale D g).TauBimult ∧ Nonempty (PsiOn (GlobalTheory.PolDeg.rescale D g) ⊤) := by
  intro R _ _ _ _ D
  obtain ⟨g₁, h₁⟩ := GlobalTheory.T.degeneration_rescale_tau_bimult_exists R D
  obtain ⟨g₂, e₂, b₂⟩ := even_step R (GlobalTheory.PolDeg.rescale D g₁) h₁
  obtain ⟨g₃, e₃, b₃, p₃⟩ := top_step R _ e₂ b₂
  refine ⟨fun χ => g₃ χ * g₂ χ * g₁ χ, ?_⟩
  rw [rescale_rescale, rescale_rescale] at e₃ b₃ p₃
  exact ⟨e₃, b₃, p₃⟩

end GlobalTheory.UnitPsi
