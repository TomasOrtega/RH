import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultA
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero

open AlgebraicGeometry CategoryTheory ReciprocityTheory.AnForm.R

namespace GlobalTheory

/- English proof (translation)
Introduce `Y _ I y hreg n r T hR hI`. Use `⟨hreg, ?_⟩` and prove the remaining obligations. Use `choose O hO t ht using fun i => TopCat.Presheaf.exists_germ_eq Y.presheaf (r i)`. Establish `hSo : IsOpen (⋂ i, (O i : Set Y))` using `isOpen_iInter_of_finite fun i => (O i).2`. Take `⟨_, ⟨V, hV, rfl⟩, hyV, hVS⟩` from `Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_iInter.2 hO) hSo`.

Establish `hle : ∀ i, V ≤ O i` using `fun i z hz => Set.mem_iInter.1 (hVS hz) i`. Set `f : Fin n → Γ(Y, V)` to `fun i => Y.presheaf.map (homOfLE (hle i)).op (t i)`. Establish `hgf : ∀ i, Y.presheaf.germ V y hyV (f i) = r i` using `fun i => by`. Simplify using `only [f]`. Rewrite using `[TopCat.Presheaf.germ_res_apply]`.

Conclude with `ht i`. Set `a : Γ(Y, V)` to `∏ i ∈ T, f i`. Establish `hga : Y.presheaf.germ V y hyV a = ∏ i ∈ T, r i`. Simplify using `only [a, map_prod, hgf]`. Set `V' : Y.affineOpens` to `⟨V, hV⟩`.

Use `haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian V'`. Establish `hmap` using `WMult.stalkId_eq_map_germ I y V' hyV`. Rewrite `hmap` using `[hI]`. Take `⟨h₂, hu₂, hm₂⟩` from `IrreducibleComponentPreimages.exists_unit_mul_mem_of_germ_mem hV y hyV (I.ideal V') (t := a) (by show _ ∈ Ideal.map (Y.presheaf.germ V y hyV).hom (I.ideal V')`. Rewrite using `[← hmap, hga]`.

Conclude with `Ideal.mem_span_singleton_self _)`. Take `⟨s, hs⟩` from `(IsNoetherian.noetherian (I.ideal V') : (I.ideal V').FG)`. Establish `hgen : ∀ g : s, ∃ d : Γ(Y, V), IsUnit (Y.presheaf.germ V y hyV d) ∧ d * g.1 ∈ Ideal.span {a}`. Introduce `g`. Apply `IrreducibleComponentPreimages.exists_unit_mul_mem_of_germ_mem hV y hyV` to reduce the goal to its premises.

Establish `hg : g.1 ∈ I.ideal V'` using `hs ▸ Submodule.subset_span g.2`. Establish `: Y.presheaf.germ V y hyV g.1 ∈ Ideal.map (Y.presheaf.germ V y hyV).hom (I.ideal V')` using `Ideal.mem_map_of_mem _ hg`. Rewrite `this` using `[← hmap, ← hga, ← Set.image_singleton, ← Ideal.map_span]`. Conclude with `this`. Use `choose d hdu hdm using hgen`.

Set `h₁ : Γ(Y, V)` to `∏ g : s, d g`. Establish `hu₁ : IsUnit (Y.presheaf.germ V y hyV h₁)`. Simplify using `only [h₁, map_prod]`. Conclude with `Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun g _ => hdu g`. Establish `hcol : I.ideal V' ≤ Submodule.comap (LinearMap.mulLeft Γ(Y, V) h₁) (Ideal.span {a})`.

Rewrite using `[← hs, Submodule.span_le]`. Introduce `g hg`. Use `show h₁ * g ∈ Ideal.span {a}`. Establish `e : h₁ = (∏ g' ∈ Finset.univ.erase (⟨g, hg⟩ : s), d g') * d ⟨g, hg⟩` using `(Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm`. Rewrite using `[e, mul_assoc]`.

Conclude with `Ideal.mul_mem_left _ _ (hdm ⟨g, hg⟩)`. Set `h : Γ(Y, V)` to `h₁ * h₂`. Establish `hyD : y ∈ Y.basicOpen h` using `(Y.mem_basicOpen h y hyV).2 (by`. Simplify using `only [h, map_mul]`. Conclude with `hu₁.mul hu₂)`.

Set `D : Y.affineOpens` to `Y.affineBasicOpen (U := V') h`. Set `ρ` to `Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op`. Establish `hρ : IsUnit (ρ h)` using `Y.toRingedSpace.isUnit_res_basicOpen h`. Establish `hρ₁ : IsUnit (ρ h₁)`. Simplify using `only [h, map_mul] at hρ`.

Conclude with `isUnit_of_mul_isUnit_left hρ`. Establish `hρ₂ : IsUnit (ρ h₂)`. Simplify using `only [h, map_mul] at hρ`. Conclude with `isUnit_of_mul_isUnit_right hρ`. Use `⟨D, hyD, n, fun i => ρ (f i), T, ?_, ?_⟩` and prove the remaining obligations.

Establish `e : (fun i => Y.presheaf.germ D.1 y hyD (ρ (f i))) = r`. Use function extensionality and compare the values at `i`. Use `show Y.presheaf.germ (Y.basicOpen h) y hyD (ρ (f i)) = r i`. Rewrite using `[TopCat.Presheaf.germ_res_apply]`. Conclude with `hgf i`.

Rewrite using `[e]`. Conclude with `hR`. Rewrite using `[← I.map_ideal' (U := D) (V := V') (homOfLE (Y.basicOpen_le h)).op] show Ideal.map ρ.hom (I.ideal V') = Ideal.span {∏ i ∈ T, ρ (f i)}`. Establish `ha : ∏ i ∈ T, ρ (f i) = ρ a` using `by simp only [a, map_prod]`. Rewrite using `[ha]`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Establish `h1 : h₁ * x ∈ Ideal.span {a}` using `hcol hx`. Establish `h2 : ρ (h₁ * x) ∈ Ideal.span {ρ a}`.

Rewrite using `[← Set.image_singleton, ← Ideal.map_span]`. Conclude with `Ideal.mem_map_of_mem _ h1`. Rewrite `h2` using `[map_mul, Ideal.unit_mul_mem_iff_mem _ hρ₁]`. Conclude with `h2`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`.

Establish `h2 : ρ (h₂ * a) ∈ Ideal.map ρ.hom (I.ideal V')` using `Ideal.mem_map_of_mem _ hm₂`. Rewrite `h2` using `[map_mul, Ideal.unit_mul_mem_iff_mem _ hρ₂]`. Conclude with `h2`.
-/
theorem sncAt_of_stalkId_eq_span_prod : ∀ (Y : Scheme.{0}) [IsLocallyNoetherian Y] (I : Y.IdealSheafData) (y : Y),
    IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (n : ℕ) (r : Fin n → Y.presheaf.stalk y) (T : Finset (Fin n)),
    FinalTheorems.Rsp (Y.presheaf.stalk y) n r → FinalTheorems.stalkId I y = Ideal.span {∏ i ∈ T, r i} → FinalTheorems.SncAt I y := by
  intro Y _ I y hreg n r T hR hI
  refine ⟨hreg, ?_⟩
  choose O hO t ht using fun i => TopCat.Presheaf.exists_germ_eq Y.presheaf (r i)
  have hSo : IsOpen (⋂ i, (O i : Set Y)) := isOpen_iInter_of_finite fun i => (O i).2
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVS⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_iInter.2 hO) hSo
  have hle : ∀ i, V ≤ O i := fun i z hz => Set.mem_iInter.1 (hVS hz) i
  let f : Fin n → Γ(Y, V) := fun i => Y.presheaf.map (homOfLE (hle i)).op (t i)
  have hgf : ∀ i, Y.presheaf.germ V y hyV (f i) = r i := fun i => by
    simp only [f]; rw [TopCat.Presheaf.germ_res_apply]; exact ht i
  let a : Γ(Y, V) := ∏ i ∈ T, f i
  have hga : Y.presheaf.germ V y hyV a = ∏ i ∈ T, r i := by
    simp only [a, map_prod, hgf]
  let V' : Y.affineOpens := ⟨V, hV⟩
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian V'
  have hmap := WMult.stalkId_eq_map_germ I y V' hyV
  rw [hI] at hmap

  obtain ⟨h₂, hu₂, hm₂⟩ := IrreducibleComponentPreimages.exists_unit_mul_mem_of_germ_mem hV y hyV (I.ideal V') (t := a)
    (by show _ ∈ Ideal.map (Y.presheaf.germ V y hyV).hom (I.ideal V')
        rw [← hmap, hga]; exact Ideal.mem_span_singleton_self _)

  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (I.ideal V') : (I.ideal V').FG)
  have hgen : ∀ g : s, ∃ d : Γ(Y, V), IsUnit (Y.presheaf.germ V y hyV d) ∧ d * g.1 ∈ Ideal.span {a} := by
    intro g
    apply IrreducibleComponentPreimages.exists_unit_mul_mem_of_germ_mem hV y hyV
    have hg : g.1 ∈ I.ideal V' := hs ▸ Submodule.subset_span g.2
    have : Y.presheaf.germ V y hyV g.1 ∈ Ideal.map (Y.presheaf.germ V y hyV).hom (I.ideal V') :=
      Ideal.mem_map_of_mem _ hg
    rw [← hmap, ← hga, ← Set.image_singleton, ← Ideal.map_span] at this
    exact this
  choose d hdu hdm using hgen
  let h₁ : Γ(Y, V) := ∏ g : s, d g
  have hu₁ : IsUnit (Y.presheaf.germ V y hyV h₁) := by
    simp only [h₁, map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun g _ => hdu g
  have hcol : I.ideal V' ≤ Submodule.comap (LinearMap.mulLeft Γ(Y, V) h₁) (Ideal.span {a}) := by
    rw [← hs, Submodule.span_le]
    classical
    intro g hg
    show h₁ * g ∈ Ideal.span {a}
    have e : h₁ = (∏ g' ∈ Finset.univ.erase (⟨g, hg⟩ : s), d g') * d ⟨g, hg⟩ :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
    rw [e, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hdm ⟨g, hg⟩)
  let h : Γ(Y, V) := h₁ * h₂
  have hyD : y ∈ Y.basicOpen h := (Y.mem_basicOpen h y hyV).2 (by
    simp only [h, map_mul]; exact hu₁.mul hu₂)
  let D : Y.affineOpens := Y.affineBasicOpen (U := V') h
  let ρ := Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op
  have hρ : IsUnit (ρ h) := Y.toRingedSpace.isUnit_res_basicOpen h
  have hρ₁ : IsUnit (ρ h₁) := by
    simp only [h, map_mul] at hρ; exact isUnit_of_mul_isUnit_left hρ
  have hρ₂ : IsUnit (ρ h₂) := by
    simp only [h, map_mul] at hρ; exact isUnit_of_mul_isUnit_right hρ
  refine ⟨D, hyD, n, fun i => ρ (f i), T, ?_, ?_⟩
  · have e : (fun i => Y.presheaf.germ D.1 y hyD (ρ (f i))) = r := by
      funext i
      show Y.presheaf.germ (Y.basicOpen h) y hyD (ρ (f i)) = r i
      rw [TopCat.Presheaf.germ_res_apply]
      exact hgf i
    rw [e]; exact hR
  · rw [← I.map_ideal' (U := D) (V := V') (homOfLE (Y.basicOpen_le h)).op]
    show Ideal.map ρ.hom (I.ideal V') = Ideal.span {∏ i ∈ T, ρ (f i)}
    have ha : ∏ i ∈ T, ρ (f i) = ρ a := by simp only [a, map_prod]
    rw [ha]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h1 : h₁ * x ∈ Ideal.span {a} := hcol hx
      have h2 : ρ (h₁ * x) ∈ Ideal.span {ρ a} := by
        rw [← Set.image_singleton, ← Ideal.map_span]; exact Ideal.mem_map_of_mem _ h1
      rw [map_mul, Ideal.unit_mul_mem_iff_mem _ hρ₁] at h2
      exact h2
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have h2 : ρ (h₂ * a) ∈ Ideal.map ρ.hom (I.ideal V') := Ideal.mem_map_of_mem _ hm₂
      rw [map_mul, Ideal.unit_mul_mem_iff_mem _ hρ₂] at h2
      exact h2
end GlobalTheory
