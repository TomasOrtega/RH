import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealSheafFiniteOpenClosedImageStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.NormDown

/- English proof (translation)
Break down `ValuationRing.dvd_total x y with hd | ⟨c, rfl⟩` into its components or cases. Conclude with `hd`. Distinguish the cases in `hy : y = 0`. Simplify using `[hy]`. Take `⟨e, he⟩` from `hxy`.

Establish `hy' : h y ≠ 0` using `fun h0 => hy (hi (by rw [h0, map_zero]))`. Establish `h1 : h y * 1 = h y * (h c * e)` using `by rw [mul_one, ← mul_assoc, ← map_mul, ← he]`. Establish `hu : IsUnit (h c)` using `isUnit_iff_exists_inv.2 ⟨e, (mul_left_cancel₀ hy' h1).symm⟩`. Establish `hc : IsUnit c` using `(isUnit_map_iff h c).1 hu`. Conclude with `⟨↑hc.unit⁻¹, by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]⟩`.
-/
theorem dvd_of_map_dvd {V V' : Type} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing V'] [IsDomain V']
    (h : V →+* V') (hi : Function.Injective h) [IsLocalHom h] {x y : V} (hxy : h x ∣ h y) : x ∣ y := by
  rcases ValuationRing.dvd_total x y with hd | ⟨c, rfl⟩
  · exact hd
  · by_cases hy : y = 0
    · simp [hy]
    obtain ⟨e, he⟩ := hxy
    have hy' : h y ≠ 0 := fun h0 => hy (hi (by rw [h0, map_zero]))
    have h1 : h y * 1 = h y * (h c * e) := by rw [mul_one, ← mul_assoc, ← map_mul, ← he]
    have hu : IsUnit (h c) := isUnit_iff_exists_inv.2 ⟨e, (mul_left_cancel₀ hy' h1).symm⟩
    have hc : IsUnit c := (isUnit_map_iff h c).1 hu
    exact ⟨↑hc.unit⁻¹, by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]⟩

/- English proof (translation)
Take `⟨x, rfl⟩ : ∃ x, I = Ideal.span {x}` from `⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩`. Take `⟨y, rfl⟩ : ∃ y, I' = Ideal.span {y}` from `⟨_, (Submodule.IsPrincipal.span_singleton_generator I').symm⟩`. Rewrite `e` using `[Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, Ideal.span_singleton_eq_span_singleton]`. Rewrite using `[Ideal.span_singleton_eq_span_singleton]`. Conclude with `associated_of_dvd_dvd (dvd_of_map_dvd h hi e.dvd) (dvd_of_map_dvd h hi e.symm.dvd)`.
-/
theorem map_injective {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    (h : V →+* V') (hi : Function.Injective h) [IsLocalHom h] {I I' : Ideal V} (e : I.map h = I'.map h) : I = I' := by
  obtain ⟨x, rfl⟩ : ∃ x, I = Ideal.span {x} := ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  obtain ⟨y, rfl⟩ : ∃ y, I' = Ideal.span {y} := ⟨_, (Submodule.IsPrincipal.span_singleton_generator I').symm⟩
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    Ideal.span_singleton_eq_span_singleton] at e
  rw [Ideal.span_singleton_eq_span_singleton]
  exact associated_of_dvd_dvd (dvd_of_map_dvd h hi e.dvd) (dvd_of_map_dvd h hi e.symm.dvd)

/- English proof (translation)
Simplify using `only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use extensionality with `a`. Conclude with `(hc a).symm`.
-/
theorem jK_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (fK : FractionRing R →+* FractionRing S)
    (hc : ∀ a, fK (algebraMap R _ a) = algebraMap S _ (f a)) : jK S ≫ spMap f = spMap fK ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  exact (hc a).symm

/- English proof (translation)
Introduce `g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord`. Establish `hne : ((⊤ : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty` using `Set.univ_nonempty`. Use `haveI : CharZero X₁.Ω₁ := X₁.ar.char`. Use `haveI hchar : CharZero Γ(X₁.M.Z, ⊤) := RingHom.charZero (X₁.M.res ⊤ hne)`. Use `haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded`.

Use `haveI := X₁.M.lft`. Establish `hLN : IsLocallyNoetherian X₁.M.Z` using `LocallyOfFiniteType.isLocallyNoetherian X₁.M.s`. Take `⟨d, J, hd, hJs, hJl⟩` from `GlobalTheory.T.norm_descent_idealSheaf_finite_open_closed_image X₁.M.Z Z X₁.π X₁.fin inferInstance hLN X₁.normal hZ.2.1 (by rw [hπ]; exact hWc.isOpen) hchar J₁`. Use `⟨d, J, hd, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `hJs x hx`.

Conclude with `⟨hπ ▸ ⟨y, rfl⟩, hsupp y hy⟩`. Introduce `T ξ₁ hgen`. Take `⟨V', _, _, _, _, f, ψ, hc', hfi, hfl, hψ, hprod⟩` from `hJl T.V T.complete (ξ₁ ≫ X₁.π) ⟨ξ₁ (closedPoint T.V), rfl⟩`. Set `fK : FractionRing T.V →+* FractionRing V'` to `IsLocalization.map (FractionRing V') f (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi)`. Establish `hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a)` using `fun a => IsLocalization.map_eq _ a`.

Establish `hB : GlobalTheory.Mum.Base V'` using `⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩`. Take `⟨T₂, f₂, fK₂, hi₂, hl₂, -, hc₂, hy₂⟩` from `GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ _ F V' hB inferInstance (spMap fK ≫ T.y)`. Establish `hover : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π → jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π = T₂.y ≫ i`. Introduce `χ hχ`. Rewrite using `[Category.assoc, hχ, ← Category.assoc, jK_spMap f₂ fK₂ hc₂, Category.assoc, ← Category.assoc (jK V'), jK_spMap f fK hfK, Category.assoc, hgen, hy₂]`.

Simplify using `only [Category.assoc]`. Take `⟨a₀, ha₀, h₀⟩` from `hord T₂ _ (hover (spMap f ≫ ξ₁) (Category.assoc _ _ _))`. Establish `hj : ∀ j, idlAlong J₁ (spMap f₂ ≫ ψ j) = Ideal.span {T₂.ϖ ^ a₀}`. Introduce `j`. Take `⟨a, ha, h⟩` from `hord T₂ _ (hover (ψ j) (hψ j))`.

Rewrite using `[h, show a = a₀ from by exact_mod_cast ha.trans ha₀.symm]`. Establish `hcomp : spMap (f₂.comp f) = spMap f₂ ≫ spMap f`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `haveI : IsLocalHom (f₂.comp f) := RingHom.isLocalHom_comp f₂ f`. Apply `map_injective (f₂.comp f) (hi₂.comp hfi)` to reduce the goal to its premises.

Establish `hmp` using `map_prod (Ideal.mapHom f₂) (fun j => idlAlong J₁ (ψ j)) Finset.univ`. Simplify using `only [Ideal.mapHom_apply] at hmp`. Rewrite using `[← Ideal.map_map, hprod, Ideal.map_pow, ← GlobalTheory.TraitOrder.idlAlong_comp, hcomp, Category.assoc, h₀, hmp]`. Simplify using `only [← GlobalTheory.TraitOrder.idlAlong_comp, hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem normDescent : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (k : ℕ) (J : Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  intro g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  have hne : ((⊤ : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := Set.univ_nonempty
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI hchar : CharZero Γ(X₁.M.Z, ⊤) := RingHom.charZero (X₁.M.res ⊤ hne)
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  have hLN : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  obtain ⟨d, J, hd, hJs, hJl⟩ := GlobalTheory.T.norm_descent_idealSheaf_finite_open_closed_image X₁.M.Z Z X₁.π X₁.fin inferInstance hLN X₁.normal hZ.2.1
    (by rw [hπ]; exact hWc.isOpen) hchar J₁
  refine ⟨d, J, hd, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hJs x hx
    exact ⟨hπ ▸ ⟨y, rfl⟩, hsupp y hy⟩
  intro T ξ₁ hgen
  obtain ⟨V', _, _, _, _, f, ψ, hc', hfi, hfl, hψ, hprod⟩ :=
    hJl T.V T.complete (ξ₁ ≫ X₁.π) ⟨ξ₁ (closedPoint T.V), rfl⟩
  let fK : FractionRing T.V →+* FractionRing V' :=
    IsLocalization.map (FractionRing V') f (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi)
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq _ a
  have hB : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
  obtain ⟨T₂, f₂, fK₂, hi₂, hl₂, -, hc₂, hy₂⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ _ F V' hB inferInstance (spMap fK ≫ T.y)

  have hover : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π = T₂.y ≫ i := by
    intro χ hχ
    rw [Category.assoc, hχ, ← Category.assoc, jK_spMap f₂ fK₂ hc₂, Category.assoc, ← Category.assoc (jK V'),
      jK_spMap f fK hfK, Category.assoc, hgen, hy₂]
    simp only [Category.assoc]
  obtain ⟨a₀, ha₀, h₀⟩ := hord T₂ _ (hover (spMap f ≫ ξ₁) (Category.assoc _ _ _))
  have hj : ∀ j, idlAlong J₁ (spMap f₂ ≫ ψ j) = Ideal.span {T₂.ϖ ^ a₀} := by
    intro j
    obtain ⟨a, ha, h⟩ := hord T₂ _ (hover (ψ j) (hψ j))
    rw [h, show a = a₀ from by exact_mod_cast ha.trans ha₀.symm]
  have hcomp : spMap (f₂.comp f) = spMap f₂ ≫ spMap f := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI : IsLocalHom (f₂.comp f) := RingHom.isLocalHom_comp f₂ f
  apply map_injective (f₂.comp f) (hi₂.comp hfi)
  have hmp := map_prod (Ideal.mapHom f₂) (fun j => idlAlong J₁ (ψ j)) Finset.univ
  simp only [Ideal.mapHom_apply] at hmp
  rw [← Ideal.map_map, hprod, Ideal.map_pow, ← GlobalTheory.TraitOrder.idlAlong_comp, hcomp, Category.assoc, h₀, hmp]
  simp only [← GlobalTheory.TraitOrder.idlAlong_comp, hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.NormDown
