import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `hd U s hs u hu`. Set `C : irreducibleComponents Z` to `⟨_, irreducibleComponent_mem_irreducibleComponents u⟩`. Take `⟨_, ⟨W, hW, rfl⟩, huW, hWle⟩` from `Z.isBasis_affineOpens.exists_subset_of_mem_open (show u ∈ ((U ⊓ IsNormalScheme.component C : Z.Opens) : Set Z) from ⟨hu, mem_irreducibleComponent⟩) (U ⊓ IsNormalScheme.component C).isOpen`. Establish `hWU : W ≤ U` using `fun x hx ↦ (hWle hx).1`. Use `⟨W, hWU, huW, ?_⟩` and prove the remaining obligations.

Establish `hWirr : IsIrreducible (W : Set Z)` using `⟨⟨u, huW⟩, C.2.1.2.open_subset W.isOpen fun x hx ↦ (hWle hx).2⟩`. Take `⟨_, _⟩` from `IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible hWirr`. Take `⟨x, hxW, hfr, hgen⟩ : ∃ (x : Z) (hxW : x ∈ W), (letI` from `Z.presheaf.algebra_section_stalk (U := W) ⟨x, hxW⟩; IsFractionRing Γ(Z, W) (Z.presheaf.stalk x)) ∧ ∀ w ∈ W, x ⤳ w := by`. Set `P : Spec Γ(Z, W)` to `⟨⊥, Ideal.isPrime_bot⟩`. Establish `hxW : hW.fromSpec P ∈ W` using `hW.range_fromSpec.le ⟨P, rfl⟩`.

Use `⟨_, hxW, ?_, ?_⟩` and prove the remaining obligations. Set `_` to `Z.presheaf.algebra_section_stalk (U := W) ⟨_, hxW⟩`. Establish `h` using `hW.isLocalization_stalk' P hxW`. Establish `e : P.asIdeal.primeCompl = nonZeroDivisors Γ(Z, W)`. Use extensionality with `a`.

Simplify using `[P, Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]`. Unfold `IsLocalization.AtPrime at h`. Rewrite `h` using `[e]`. Conclude with `h`. Introduce `w hw`.

Take `⟨q, rfl⟩ : w ∈ Set.range hW.fromSpec` from `hW.range_fromSpec.ge hw`. Conclude with `((PrimeSpectrum.le_iff_specializes P q).mp bot_le).map hW.fromSpec.continuous`. Choose the witnesses or unpack the hypotheses as in `⟨y, rfl⟩ : x ∈ Set.range j := by`. Take `⟨w, hw, hwr⟩` from `hd.inter_open_nonempty _ W.isOpen ⟨u, huW⟩`. Conclude with `(hgen w hw).mem_open j.isOpenEmbedding.isOpen_range hwr`.

Set `_` to `Z.presheaf.algebra_section_stalk (U := W) ⟨_, hxW⟩`. Set `_ : Algebra Γ(Z, W) Γ(T, j ⁻¹ᵁ W)` to `(j.app W).hom.toAlgebra`. Establish `hyW : y ∈ j ⁻¹ᵁ W` using `hxW`. Establish `hnat : (T.presheaf.map (homOfLE (j.preimage_mono hWU)).op).hom.comp (j.app U).hom = (algebraMap Γ(Z, W) Γ(T, j ⁻¹ᵁ W)).comp (Z.presheaf.map (homOfLE hWU).op).hom`. Express the relevant statement in the definitionally equal form `_ = (j.app W).hom.comp _`.

Rewrite using `[← CommRingCat.hom_comp, ← CommRingCat.hom_comp, j.naturality]`. Both sides reduce to the same expression. Establish `hs₁ : IsIntegral Γ(Z, W) (T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s)`. Take `⟨p, hp, hps⟩` from `hs`. Use `⟨p.map (Z.presheaf.map (homOfLE hWU).op).hom, hp.map _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.eval₂_map, ← hnat, ← Polynomial.hom_eval₂, hps, map_zero]`. Establish `hgerm (a : Γ(Z, W)) : j.stalkMap y (Z.presheaf.germ W (j y) hxW a) = T.presheaf.germ (j ⁻¹ᵁ W) y hyW (j.app W a)` using `j.germ_stalkMap_apply W y hxW a`. Establish `hbij : Function.Bijective (j.stalkMap y)` using `ConcreteCategory.bijective_of_isIso _`. Set `φ : Γ(T, j ⁻¹ᵁ W) ⟶ Z.presheaf.stalk (j y)` to `T.presheaf.germ (j ⁻¹ᵁ W) y hyW ≫ inv (j.stalkMap y)`. Establish `hφ (c : Γ(T, j ⁻¹ᵁ W)) : j.stalkMap y (φ c) = T.presheaf.germ (j ⁻¹ᵁ W) y hyW c`.

Rewrite using `[← CommRingCat.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]`. Set `ψ : Γ(T, j ⁻¹ᵁ W) →ₐ[Γ(Z, W)] Z.presheaf.stalk (j y)` to `{ φ.hom with commutes' := fun a ↦ hbij.1 ((hφ _).trans (hgerm a).symm) }`. Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.map ψ hs₁)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `hg : T.presheaf.germ (j ⁻¹ᵁ W) y hyW (j.app W a - T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) = 0`.

Rewrite using `[map_sub, ← hgerm, ← hφ, sub_eq_zero]`. Conclude with `congr(j.stalkMap y $ha)`. Establish `: IsReduced T` using `isReduced_of_isOpenImmersion j`. Rewrite using `[← sub_eq_zero]`. Apply `eq_zero_of_basicOpen_eq_bot` to reduce the goal to its premises.

Rewrite using `[eq_bot_iff]`. Introduce `t ht`. Establish `hyt : y ⤳ t` using `j.isOpenEmbedding.isInducing.specializes_iff.mp (hgen _ (T.basicOpen_le _ ht))`. Establish `hy : y ∈ T.basicOpen (j.app W a - T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s)` using `hyt.mem_open (T.basicOpen _).isOpen ht`. Rewrite `hy` using `[Scheme.mem_basicOpen _ _ _ hyW, hg]`.

Conclude with `(not_isUnit_zero hy).elim`.
-/
theorem exists_section_of_isIntegralElem_of_isOpenImmersion {T Z : Scheme.{0}}
    [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z] (j : T ⟶ Z) [IsOpenImmersion j] :
    Dense (Set.range j) → ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (j.app U).hom.IsIntegralElem s →
    ∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s := by
  intro hd U s hs u hu
  let C : irreducibleComponents Z := ⟨_, irreducibleComponent_mem_irreducibleComponents u⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, huW, hWle⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (show u ∈ ((U ⊓ IsNormalScheme.component C : Z.Opens) : Set Z) from
      ⟨hu, mem_irreducibleComponent⟩)
    (U ⊓ IsNormalScheme.component C).isOpen
  have hWU : W ≤ U := fun x hx ↦ (hWle hx).1
  refine ⟨W, hWU, huW, ?_⟩
  have hWirr : IsIrreducible (W : Set Z) :=
    ⟨⟨u, huW⟩, C.2.1.2.open_subset W.isOpen fun x hx ↦ (hWle hx).2⟩
  obtain ⟨_, _⟩ := IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible hWirr
  obtain ⟨x, hxW, hfr, hgen⟩ : ∃ (x : Z) (hxW : x ∈ W),
      (letI := Z.presheaf.algebra_section_stalk (U := W) ⟨x, hxW⟩;
        IsFractionRing Γ(Z, W) (Z.presheaf.stalk x)) ∧ ∀ w ∈ W, x ⤳ w := by
    let P : Spec Γ(Z, W) := ⟨⊥, Ideal.isPrime_bot⟩
    have hxW : hW.fromSpec P ∈ W := hW.range_fromSpec.le ⟨P, rfl⟩
    refine ⟨_, hxW, ?_, ?_⟩
    · let _ := Z.presheaf.algebra_section_stalk (U := W) ⟨_, hxW⟩
      have h := hW.isLocalization_stalk' P hxW
      have e : P.asIdeal.primeCompl = nonZeroDivisors Γ(Z, W) := by
        ext a
        simp [P, Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
      unfold IsLocalization.AtPrime at h
      rw [e] at h
      exact h
    · intro w hw
      obtain ⟨q, rfl⟩ : w ∈ Set.range hW.fromSpec := hW.range_fromSpec.ge hw
      exact ((PrimeSpectrum.le_iff_specializes P q).mp bot_le).map hW.fromSpec.continuous
  obtain ⟨y, rfl⟩ : x ∈ Set.range j := by
    obtain ⟨w, hw, hwr⟩ := hd.inter_open_nonempty _ W.isOpen ⟨u, huW⟩
    exact (hgen w hw).mem_open j.isOpenEmbedding.isOpen_range hwr
  let _ := Z.presheaf.algebra_section_stalk (U := W) ⟨_, hxW⟩
  let _ : Algebra Γ(Z, W) Γ(T, j ⁻¹ᵁ W) := (j.app W).hom.toAlgebra
  have hyW : y ∈ j ⁻¹ᵁ W := hxW
  have hnat : (T.presheaf.map (homOfLE (j.preimage_mono hWU)).op).hom.comp (j.app U).hom =
      (algebraMap Γ(Z, W) Γ(T, j ⁻¹ᵁ W)).comp (Z.presheaf.map (homOfLE hWU).op).hom := by
    change _ = (j.app W).hom.comp _
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, j.naturality]
    rfl
  have hs₁ : IsIntegral Γ(Z, W) (T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) := by
    obtain ⟨p, hp, hps⟩ := hs
    refine ⟨p.map (Z.presheaf.map (homOfLE hWU).op).hom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hnat, ← Polynomial.hom_eval₂, hps, map_zero]
  have hgerm (a : Γ(Z, W)) : j.stalkMap y (Z.presheaf.germ W (j y) hxW a) =
      T.presheaf.germ (j ⁻¹ᵁ W) y hyW (j.app W a) :=
    j.germ_stalkMap_apply W y hxW a
  have hbij : Function.Bijective (j.stalkMap y) := ConcreteCategory.bijective_of_isIso _
  let φ : Γ(T, j ⁻¹ᵁ W) ⟶ Z.presheaf.stalk (j y) :=
    T.presheaf.germ (j ⁻¹ᵁ W) y hyW ≫ inv (j.stalkMap y)
  have hφ (c : Γ(T, j ⁻¹ᵁ W)) : j.stalkMap y (φ c) = T.presheaf.germ (j ⁻¹ᵁ W) y hyW c := by
    rw [← CommRingCat.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let ψ : Γ(T, j ⁻¹ᵁ W) →ₐ[Γ(Z, W)] Z.presheaf.stalk (j y) :=
    { φ.hom with commutes' := fun a ↦ hbij.1 ((hφ _).trans (hgerm a).symm) }
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.map ψ hs₁)
  refine ⟨a, ?_⟩
  have hg : T.presheaf.germ (j ⁻¹ᵁ W) y hyW
      (j.app W a - T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) = 0 := by
    rw [map_sub, ← hgerm, ← hφ, sub_eq_zero]
    exact congr(j.stalkMap y $ha)
  have : IsReduced T := isReduced_of_isOpenImmersion j
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro t ht
  have hyt : y ⤳ t :=
    j.isOpenEmbedding.isInducing.specializes_iff.mp (hgen _ (T.basicOpen_le _ ht))
  have hy : y ∈ T.basicOpen
      (j.app W a - T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) :=
    hyt.mem_open (T.basicOpen _).isOpen ht
  rw [Scheme.mem_basicOpen _ _ _ hyW, hg] at hy
  exact (not_isUnit_zero hy).elim

end GlobalTheory
