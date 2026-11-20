import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealSheafFiniteOpenClosedImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UNormDown

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
Introduce `E _ _ _ H Dw hpq φ hφ l Xo c C A hAc hAi hAm X₁ ι J₁ hι hπ hsupp hv`. Establish `hne : ((⊤ : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty` using `Set.univ_nonempty`. Use `haveI : CharZero X₁.Ω₁ := X₁.ar.char`. Use `haveI hchar : CharZero Γ(X₁.M.Z, ⊤) := RingHom.charZero (X₁.M.res ⊤ hne)`. Use `haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded`.

Use `haveI := X₁.M.lft`. Establish `hLN : IsLocallyNoetherian X₁.M.Z` using `LocallyOfFiniteType.isLocallyNoetherian X₁.M.s`. Take `⟨d, J, hd, hJs, hJl⟩` from `GlobalTheory.T.norm_descent_idealSheaf_finite_open_closed_image X₁.M.Z C.Z X₁.π X₁.fin inferInstance hLN X₁.normal C.normal (by rw [hπ]; exact hAc.isOpen) hchar J₁`. Use `⟨d, J, hd, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `hJs x hx`.

Conclude with `⟨hπ ▸ ⟨y, rfl⟩, hsupp y hy⟩`. Introduce `T ξ₁ hgen`. Take `⟨hdvr, hcpl, hch⟩` from `(GlobalTheory.LN.cDvr_iff T.V).1 T.cdvr`. Take `⟨V', _, _, _, _, f, ψ, hc', hfi, hfl, hψ, hprod⟩` from `hJl T.V hcpl (ξ₁ ≫ X₁.π) ⟨ξ₁ (closedPoint T.V), rfl⟩`. Set `fK : FractionRing T.V →+* FractionRing V'` to `IsLocalization.map (FractionRing V') f (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi)`.

Establish `hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a)` using `fun a => IsLocalization.map_eq _ a`. Establish `hB : GlobalTheory.Mum.Base V'` using `⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩`. Take `⟨T₂, f₂, fK₂, hi₂, hl₂, -, hc₂, hy₂⟩` from `GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c V' hB inferInstance (spMap fK ≫ T.y)`. Establish `hover : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π → T₂.y ≫ C.i = jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π`. Introduce `χ hχ`.

Establish `e1 : jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π = (jK T₂.V ≫ spMap f₂) ≫ (χ ≫ X₁.π)`. Simplify using `only [Category.assoc]`. Establish `e2 : (jK V' ≫ spMap f) ≫ ξ₁ ≫ X₁.π = spMap fK ≫ T.y ≫ C.i`. Rewrite using `[jK_spMap f fK hfK, Category.assoc, hgen]`. Rewrite using `[e1, hχ, jK_spMap f₂ fK₂ hc₂, Category.assoc, ← Category.assoc (jK V'), e2, hy₂]`.

Simplify using `only [Category.assoc]`. Establish `hord : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T₂.be ∧ idlAlong J₁ (spMap f₂ ≫ χ) = Ideal.span {T₂.ϖ ^ a}`. Introduce `χ hχ`. Take `⟨tK, h1, h2⟩` from `T₂.gen`. Conclude with `hv T₂.V T₂.cdvr T₂.ϖ T₂.irr (spMap f₂ ≫ χ) T₂.y (hover χ hχ) trivial T₂.t tK h1 h2 T₂.P T₂.be T₂.lev T₂.mono`.

Take `⟨a₀, ha₀, h₀⟩` from `hord (spMap f ≫ ξ₁) (Category.assoc _ _ _)`. Establish `hj : ∀ j, idlAlong J₁ (spMap f₂ ≫ ψ j) = Ideal.span {T₂.ϖ ^ a₀}`. Introduce `j`. Take `⟨a, ha, h⟩` from `hord (ψ j) (hψ j)`. Rewrite using `[h, show a = a₀ from by exact_mod_cast ha.trans ha₀.symm]`.

Establish `hcomp : spMap (f₂.comp f) = spMap f₂ ≫ spMap f`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `haveI : IsLocalHom (f₂.comp f) := RingHom.isLocalHom_comp f₂ f`. Apply `GlobalTheory.TraitOrder.map_injective (f₂.comp f) (hi₂.comp hfi)` to reduce the goal to its premises. Establish `hmp` using `map_prod (Ideal.mapHom f₂) (fun j => idlAlong J₁ (ψ j)) Finset.univ`.

Simplify using `only [Ideal.mapHom_apply] at hmp`. Rewrite using `[← Ideal.map_map, hprod, Ideal.map_pow, ← GlobalTheory.TraitOrder.idlAlong_comp, hcomp, Category.assoc, h₀, hmp]`. Simplify using `only [← GlobalTheory.TraitOrder.idlAlong_comp, hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem normDescent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∀ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = A → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) → UValThru Xo c C.i X₁.π Set.univ φ J₁ ι → ∃ (k : ℕ) (J : C.Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ A ∧ x ∉ Set.range C.i) ∧ ∀ (T : UTrait Xo c) (ξ₁ : Sp T.V ⟶ X₁.M.Z), T.y ≫ C.i = jK T.V ≫ ξ₁ ≫ X₁.π → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C A hAc hAi hAm X₁ ι J₁ hι hπ hsupp hv
  have hne : ((⊤ : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := Set.univ_nonempty
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI hchar : CharZero Γ(X₁.M.Z, ⊤) := RingHom.charZero (X₁.M.res ⊤ hne)
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  have hLN : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  obtain ⟨d, J, hd, hJs, hJl⟩ := GlobalTheory.T.norm_descent_idealSheaf_finite_open_closed_image X₁.M.Z C.Z X₁.π X₁.fin inferInstance hLN X₁.normal C.normal
    (by rw [hπ]; exact hAc.isOpen) hchar J₁
  refine ⟨d, J, hd, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hJs x hx
    exact ⟨hπ ▸ ⟨y, rfl⟩, hsupp y hy⟩
  intro T ξ₁ hgen
  obtain ⟨hdvr, hcpl, hch⟩ := (GlobalTheory.LN.cDvr_iff T.V).1 T.cdvr
  obtain ⟨V', _, _, _, _, f, ψ, hc', hfi, hfl, hψ, hprod⟩ :=
    hJl T.V hcpl (ξ₁ ≫ X₁.π) ⟨ξ₁ (closedPoint T.V), rfl⟩
  let fK : FractionRing T.V →+* FractionRing V' :=
    IsLocalization.map (FractionRing V') f (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi)
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq _ a
  have hB : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
  obtain ⟨T₂, f₂, fK₂, hi₂, hl₂, -, hc₂, hy₂⟩ := GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c V' hB inferInstance (spMap fK ≫ T.y)

  have hover : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      T₂.y ≫ C.i = jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π := by
    intro χ hχ
    have e1 : jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π = (jK T₂.V ≫ spMap f₂) ≫ (χ ≫ X₁.π) := by
      simp only [Category.assoc]
    have e2 : (jK V' ≫ spMap f) ≫ ξ₁ ≫ X₁.π = spMap fK ≫ T.y ≫ C.i := by
      rw [jK_spMap f fK hfK, Category.assoc, hgen]
    rw [e1, hχ, jK_spMap f₂ fK₂ hc₂, Category.assoc, ← Category.assoc (jK V'), e2, hy₂]
    simp only [Category.assoc]
  have hord : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T₂.be ∧ idlAlong J₁ (spMap f₂ ≫ χ) = Ideal.span {T₂.ϖ ^ a} := by
    intro χ hχ
    obtain ⟨tK, h1, h2⟩ := T₂.gen
    exact hv T₂.V T₂.cdvr T₂.ϖ T₂.irr (spMap f₂ ≫ χ) T₂.y (hover χ hχ) trivial T₂.t tK h1 h2 T₂.P T₂.be T₂.lev
      T₂.mono
  obtain ⟨a₀, ha₀, h₀⟩ := hord (spMap f ≫ ξ₁) (Category.assoc _ _ _)
  have hj : ∀ j, idlAlong J₁ (spMap f₂ ≫ ψ j) = Ideal.span {T₂.ϖ ^ a₀} := by
    intro j
    obtain ⟨a, ha, h⟩ := hord (ψ j) (hψ j)
    rw [h, show a = a₀ from by exact_mod_cast ha.trans ha₀.symm]
  have hcomp : spMap (f₂.comp f) = spMap f₂ ≫ spMap f := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI : IsLocalHom (f₂.comp f) := RingHom.isLocalHom_comp f₂ f
  apply GlobalTheory.TraitOrder.map_injective (f₂.comp f) (hi₂.comp hfi)
  have hmp := map_prod (Ideal.mapHom f₂) (fun j => idlAlong J₁ (ψ j)) Finset.univ
  simp only [Ideal.mapHom_apply] at hmp
  rw [← Ideal.map_map, hprod, Ideal.map_pow, ← GlobalTheory.TraitOrder.idlAlong_comp, hcomp, Category.assoc, h₀, hmp]
  simp only [← GlobalTheory.TraitOrder.idlAlong_comp, hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.UPoinc.UNormDown
