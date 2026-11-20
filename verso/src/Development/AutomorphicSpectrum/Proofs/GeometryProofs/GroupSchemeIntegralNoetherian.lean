import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TopLeOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThickKer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

/- English proof (translation)
Set `j : Spec (CommRingCat.of (V ⧸ J)) ⟶ Spec (CommRingCat.of V)` to `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))`. Set `f` to `pullback.fst π j`. Set `g` to `pullback.snd π j`. Establish `e1` using `Scheme.Hom.appLE_comp_appLE f π ⊤ U (f ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl`. Establish `e0 : ∀ e : ⊤ ≤ j ⁻¹ᵁ ⊤, (j.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) = 0`.

Introduce `e`. Establish `a1 : j.appLE ⊤ ⊤ e = j.appTop` using `Scheme.Hom.appLE_eq_app (f := j) (U := ⊤)`. Establish `a2` using `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))`. Establish `a3 : j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) = (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv.hom (Ideal.Quotient.mk J r)` using `(congrArg (fun q => q.hom r) a2).symm`. Rewrite using `[a1, a3, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]`.

Establish `key : ∀ (w : pullback π j ⟶ Spec (CommRingCat.of V)) (_ : w = g ≫ j) (e : f ⁻¹ᵁ U ≤ w ⁻¹ᵁ ⊤), (w.appLE ⊤ (f ⁻¹ᵁ U) e).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) = 0`. Introduce and unpack `_ rfl e`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE g j ⊤ ⊤ (f ⁻¹ᵁ U) (fun _ _ => trivial) (fun _ _ => trivial), CommRingCat.comp_apply]`. Conclude with `(congrArg _ (e0 (fun _ _ => trivial))).trans (map_zero _)`. Establish `h` using `key (f ≫ π) pullback.condition (fun _ _ => trivial)`.

Rewrite `h` using `[← e1, CommRingCat.comp_apply]`. Establish `e2 : f.appLE U (f ⁻¹ᵁ U) le_rfl = f.app U` using `Scheme.Hom.appLE_eq_app (f := f) (U := U)`. Rewrite `h` using `[e2]`. Conclude with `h`.
-/
theorem app_fst_sc_eq_zero {V : Type} [CommRing V] {X : Scheme.{0}} (π : X ⟶ Sp V) (J : Ideal V) (U : X.Opens)
    {r : V} (hr : r ∈ J) :
    ((pullback.fst π (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).app U).hom (sc π U r) = 0 := by
  let j : Spec (CommRingCat.of (V ⧸ J)) ⟶ Spec (CommRingCat.of V) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let f := pullback.fst π j
  let g := pullback.snd π j
  have e1 := Scheme.Hom.appLE_comp_appLE f π ⊤ U (f ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl
  have e0 : ∀ e : ⊤ ≤ j ⁻¹ᵁ ⊤, (j.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) = 0 := by
    intro e
    have a1 : j.appLE ⊤ ⊤ e = j.appTop := Scheme.Hom.appLE_eq_app (f := j) (U := ⊤)
    have a2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))
    have a3 : j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) =
        (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv.hom (Ideal.Quotient.mk J r) :=
      (congrArg (fun q => q.hom r) a2).symm
    rw [a1, a3, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  have key : ∀ (w : pullback π j ⟶ Spec (CommRingCat.of V)) (_ : w = g ≫ j) (e : f ⁻¹ᵁ U ≤ w ⁻¹ᵁ ⊤),
      (w.appLE ⊤ (f ⁻¹ᵁ U) e).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) = 0 := by
    rintro _ rfl e
    rw [← Scheme.Hom.appLE_comp_appLE g j ⊤ ⊤ (f ⁻¹ᵁ U) (fun _ _ => trivial) (fun _ _ => trivial),
      CommRingCat.comp_apply]
    exact (congrArg _ (e0 (fun _ _ => trivial))).trans (map_zero _)
  have h := key (f ≫ π) pullback.condition (fun _ _ => trivial)
  rw [← e1, CommRingCat.comp_apply] at h
  have e2 : f.appLE U (f ⁻¹ᵁ U) le_rfl = f.app U := Scheme.Hom.appLE_eq_app (f := f) (U := U)
  rw [e2] at h
  exact h

/- English proof (translation)
Introduce `L _ _ G _ _ hG`. Use `hG.smooth` as an intermediate fact. Use `hG.geomConnected` as an intermediate fact. Establish `hgi : GeometricallyIntegral G.hom` using `GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G`. Establish `: IsNoetherianRing (𝓞 L)` using `inferInstance`.

Establish `: IsLocallyNoetherian (Sp (𝓞 L))` using `inferInstance`. Establish `hI : IsIntegral G.left` using `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom`. Establish `hN : IsLocallyNoetherian G.left` using `LocallyOfFiniteType.isLocallyNoetherian G.hom`. Use `⟨hI, fun W hW => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `IsLocallyNoetherian.component_noetherian ⟨W, hW⟩`.

Establish `h1 : (G.hom.appLE ⊤ W (fun _ _ => trivial)).hom.FiniteType` using `HasRingHomProperty.appLE (P := @LocallyOfFiniteType) G.hom inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)`. Establish `h2 : (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv.hom.FiniteType` using `RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv).2`. Conclude with `h1.comp h2`. Introduce `p hp a b hab`. Use `letI : Field (𝓞 L ⧸ p) := Ideal.Quotient.field p`.

Set `j : Spec (CommRingCat.of (𝓞 L ⧸ p)) ⟶ Sp (𝓞 L)` to `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p))`. Establish `hY : IsIntegral (pullback G.hom j)` using `GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback G.hom j)`. Set `f` to `pullback.fst G.hom j`. Establish `hker : p.map (sc G.hom W) ≤ RingHom.ker (f.app W).hom` using `Ideal.map_le_iff_le_comap.2 fun r hr => app_fst_sc_eq_zero G.hom p W hr`. Establish `hz : (f.app W).hom a * (f.app W).hom b = 0`.

Rewrite using `[← map_mul]`. Conclude with `hker hab`. Establish `hab' : (f.app W).hom a = 0 ∨ (f.app W).hom b = 0`. Distinguish the cases in `hne : Nonempty (f ⁻¹ᵁ W)`. Conclude with `mul_eq_zero.1 hz`.

Establish `hb : f ⁻¹ᵁ W = ⊥`. Use extensionality with `x`. Simplify using `only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]`. Conclude with `fun hx => hne ⟨⟨x, hx⟩⟩`. Establish `: Subsingleton Γ(pullback G.hom j, f ⁻¹ᵁ W)`.

Rewrite using `[hb]`. Use `infer_instance`. Conclude with `Or.inl (Subsingleton.elim _ _)`. Break down `hab' with h | h` into its components or cases. Conclude with `Or.inl (DVR.mem_map_of_app_fst_eq_zero G.hom p hW a h)`.

Conclude with `Or.inr (DVR.mem_map_of_app_fst_eq_zero G.hom p hW b h)`.
-/
theorem semiAb_props : ∀ (L : Type) [Field L] [NumberField L] (G : Over (Sp (𝓞 L))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsIntegral G.left ∧ ∀ W : G.left.Opens, IsAffineOpen W → IsNoetherianRing Γ(G.left, W) ∧ (sc G.hom W).FiniteType ∧ ∀ p : Ideal (𝓞 L), p.IsMaximal → ∀ a b : Γ(G.left, W), a * b ∈ p.map (sc G.hom W) → a ∈ p.map (sc G.hom W) ∨ b ∈ p.map (sc G.hom W) := by
  intro L _ _ G _ _ hG
  have := hG.smooth
  have := hG.geomConnected
  have hgi : GeometricallyIntegral G.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  have : IsNoetherianRing (𝓞 L) := inferInstance
  have : IsLocallyNoetherian (Sp (𝓞 L)) := inferInstance
  have hI : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have hN : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  refine ⟨hI, fun W hW => ⟨?_, ?_, ?_⟩⟩
  · exact IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  · have h1 : (G.hom.appLE ⊤ W (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) G.hom inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv).2
    exact h1.comp h2
  · intro p hp a b hab
    letI : Field (𝓞 L ⧸ p) := Ideal.Quotient.field p
    let j : Spec (CommRingCat.of (𝓞 L ⧸ p)) ⟶ Sp (𝓞 L) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p))
    have hY : IsIntegral (pullback G.hom j) :=
      GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback G.hom j)
    let f := pullback.fst G.hom j
    have hker : p.map (sc G.hom W) ≤ RingHom.ker (f.app W).hom :=
      Ideal.map_le_iff_le_comap.2 fun r hr => app_fst_sc_eq_zero G.hom p W hr
    have hz : (f.app W).hom a * (f.app W).hom b = 0 := by
      rw [← map_mul]
      exact hker hab
    have hab' : (f.app W).hom a = 0 ∨ (f.app W).hom b = 0 := by
      by_cases hne : Nonempty (f ⁻¹ᵁ W)
      · exact mul_eq_zero.1 hz
      · have hb : f ⁻¹ᵁ W = ⊥ := by
          ext x
          simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
          exact fun hx => hne ⟨⟨x, hx⟩⟩
        have : Subsingleton Γ(pullback G.hom j, f ⁻¹ᵁ W) := by
          rw [hb]
          infer_instance
        exact Or.inl (Subsingleton.elim _ _)
    rcases hab' with h | h
    · exact Or.inl (DVR.mem_map_of_app_fst_eq_zero G.hom p hW a h)
    · exact Or.inr (DVR.mem_map_of_app_fst_eq_zero G.hom p hW b h)

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
