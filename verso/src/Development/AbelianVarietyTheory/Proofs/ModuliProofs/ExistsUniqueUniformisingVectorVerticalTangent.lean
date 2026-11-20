import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationOfFibreOfKillsBaseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationUniformisedAbelianVarietyUniqueVecStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.VertFamily

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem valAt'_add' {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (W : X.Opens) (f f' : Γ(X, W)) :
    valAt' y W (f + f') = valAt' y W f + valAt' y W f' := by
  unfold valAt' valAt
  split_ifs <;> simp

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem valAt'_mul_of_top_le_preimage_open {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (W : X.Opens) (f f' : Γ(X, W)) :
    valAt' y W (f * f') = valAt' y W f * valAt' y W f' := by
  unfold valAt' valAt
  split_ifs <;> simp

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.
-/
private theorem valAt'_resG {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W W' : X.Opens} (hle : W' ≤ W)
    (h : ⊤ ≤ y ⁻¹ᵁ W') (f : Γ(X, W)) : valAt' y W' (resG X hle f) = valAt' y W f := by
  have hW : ⊤ ≤ y ⁻¹ᵁ W := fun x hx => hle (h hx)
  unfold valAt' valAt
  rw [dif_pos h, dif_pos hW]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem valAt'_constFn_top {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (p : X ⟶ Sp ℂ) (hp : y ≫ p = 𝟙 _) (a : ℂ) :
    valAt' y ⊤ (constFn p ⊤ a) = a := by
  have hq : ∀ (q : Sp ℂ ⟶ Sp ℂ) (e : ⊤ ≤ q ⁻¹ᵁ ⊤), q = 𝟙 _ →
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((q.appLE ⊤ ⊤ e).hom
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) = a := by
    rintro q e rfl
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (((Sp ℂ).presheaf.map (𝟙 (Opposite.op (⊤ : (Sp ℂ).Opens)))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) = a
    simp
  have e0 : ⊤ ≤ y ⁻¹ᵁ (⊤ : X.Opens) := fun _ _ => trivial
  unfold valAt' valAt constFn
  rw [dif_pos e0]
  refine Eq.trans ?_ (hq (y ≫ p) (fun _ _ => trivial) hp)
  congr 1
  rw [← CommRingCat.comp_apply]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE y p ⊤ ⊤ ⊤ _ e0)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ex_over (z : Fin g → ℂ) : (u.ex z).left ≫ A.hom = 𝟙 _ := by
  exact (Over.w (u.ex z)).trans (by simp)

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem differentiableAt_val (z : Fin g → ℂ) (O : A.left.Opens) (f : Γ(A.left, O)) (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ O) :
    DifferentiableAt ℂ (fun z' => valAt' (u.ex z').left O f) z := by
  obtain ⟨hO, hD⟩ := u.hol O f
  exact hD.differentiableAt (hO.mem_nhds h)

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem ptDer_fderiv (z w : Fin g → ℂ) :
    PtDer (u.ex z).left (fun O f => fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w) where
  add O h f f' := by
    have e : (fun z' => valAt' (u.ex z').left O (f + f')) =
        (fun z' => valAt' (u.ex z').left O f) + fun z' => valAt' (u.ex z').left O f' := by
      funext z'
      exact valAt'_add' _ _ _ _
    rw [e, fderiv_add (differentiableAt_val u z O f h) (differentiableAt_val u z O f' h)]
    rfl
  mul O h f f' := by
    have e : (fun z' => valAt' (u.ex z').left O (f * f')) =
        (fun z' => valAt' (u.ex z').left O f) * fun z' => valAt' (u.ex z').left O f' := by
      funext z'
      exact valAt'_mul_of_top_le_preimage_open _ _ _ _
    rw [e, fderiv_mul (differentiableAt_val u z O f h) (differentiableAt_val u z O f' h)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  res O O' hle h f := by
    have hev : (fun z' => valAt' (u.ex z').left O' (resG A.left hle f)) =ᶠ[nhds z]
        fun z' => valAt' (u.ex z').left O f := by
      filter_upwards [(u.hol O' (resG A.left hle f)).1.mem_nhds h] with z' hz'
      exact valAt'_resG _ hle hz' f
    rw [hev.fderiv_eq]

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem fderiv_constFn (z w : Fin g → ℂ) (a : ℂ) :
    fderiv ℂ (fun z' => valAt' (u.ex z').left ⊤ (constFn A.hom ⊤ a)) z w = 0 := by
  have e : (fun z' => valAt' (u.ex z').left ⊤ (constFn A.hom ⊤ a)) = fun _ => a := by
    funext z'
    exact valAt'_constFn_top _ _ (ex_over u z') a
  rw [e]
  simp

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities.
-/
theorem fn_eq {X : Scheme.{0}} (m : A.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    fn u m W f = fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  funext z'
  unfold fn valAt' valAt
  by_cases h : ⊤ ≤ ((u.ex z').left ≫ m) ⁻¹ᵁ W
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (u.ex z').left ⁻¹ᵁ (m ⁻¹ᵁ W) from h)]
    congr 1
  · rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (u.ex z').left ⁻¹ᵁ (m ⁻¹ᵁ W) from h)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion.

Establish an intermediate fact. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem existsUnique_vector : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z δ, PtDer ((u.ex z).left ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃! w, ∀ W f, z ∈ dom u m W → δ W f = fderiv ℂ (fn u m W f) z w := by
  intro P₀ u Hm χ hG R _ x₀ X p m _ hpb z δ hδ hc
  obtain ⟨hex, huniq⟩ := GlobalTheory.T.germDerivation_of_fibre_of_kills_base P₀.A R x₀ X p m hpb (u.ex z).left (ex_over u z)
  obtain ⟨δ₀, hδ₀, hc₀, hδδ₀⟩ := hex δ hδ hc
  obtain ⟨w, hw, hwu⟩ := GlobalTheory.T.germDerivation_uniformised_abelianVariety_unique_vector P₀ u Hm χ hG z δ₀ hδ₀ hc₀
  refine ⟨w, fun W f hz => ?_, fun w' hw' => hwu w' fun O f hO => ?_⟩
  · rw [hδδ₀ W f hz, hw (m ⁻¹ᵁ W) ((m.app W).hom f) hz, fn_eq]
  · have hD := ptDer_fderiv u z w'
    have hpt : PtDer (u.ex z).left
        (fun O f => δ₀ O f - fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w') := by
      refine ⟨fun V hV f f' => ?_, fun V hV f f' => ?_, fun V V' hle hV f => ?_⟩
      · have h1 := hδ₀.add V hV f f'
        have h2 := hD.add V hV f f'
        linear_combination h1 - h2
      · have h1 := hδ₀.mul V hV f f'
        have h2 := hD.mul V hV f f'
        linear_combination h1 - h2
      · have h1 := hδ₀.res V V' hle hV f
        have h2 := hD.res V V' hle hV f
        linear_combination h1 - h2
    have key := huniq _ hpt (fun a => by
        have h1 := hc₀ a
        have h2 := fderiv_constFn u z w' a
        linear_combination h1 - h2)
      (fun V f hV => by
        have h1 := hδδ₀ V f hV
        have h2 := hw' V f hV
        rw [fn_eq] at h2
        linear_combination h2 - h1) O f hO
    exact sub_eq_zero.mp key

end GlobalTheory.KS.VertFamily
