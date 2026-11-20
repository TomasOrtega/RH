import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

/- English proof (translation)
Introduce `k Ω o _ _ _ _ M n g e hP z`. Take `⟨τ, -, H⟩` from `hP`. Take `⟨c, hc⟩` from `GlobalTheory.ProjSpace.exists_mem_chart o n (g z)`. Set `W : M.Z.Opens` to `g ⁻¹ᵁ GlobalTheory.ProjSpace.chart o n c`. Establish `hzW : z ∈ W` using `hc`.

Establish `hW : ⊤ ≤ M.pt ⁻¹ᵁ W` using `M.top_le_preimage_pt ⟨z, hzW⟩`. Set `j : PUnit → (GlobalTheory.ProjSpace.O1 o n).ι` to `fun _ => c`. Set `V` to `((GlobalTheory.ProjSpace.O1 o n).pull (M.pt ≫ g)).U j`. Establish `hV : V ≤ (M.pt ≫ g) ⁻¹ᵁ (GlobalTheory.ProjSpace.O1 o n).U (j PUnit.unit)` using `LB.wchart_le (GlobalTheory.ProjSpace.O1 o n) (fun _ => M.pt ≫ g) j PUnit.unit`. Establish `hV' : ⊤ ≤ V` using `fun y _ => Set.mem_iInter.2 fun _ => hW (Set.mem_univ y)`.

Set `ev : Γ(Sp Ω, V) →+* Ω` to `(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp ((Sp Ω).presheaf.map (homOfLE hV').op).hom`. Establish `hconst : ∀ a : Ω, ev (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom a)) = a`. Introduce `a`. Express the relevant statement in the definitionally equal form `(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (((Sp Ω).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ (Sp Ω).presheaf.map (homOfLE hV').op).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom a)) = a`. Rewrite using `[← Functor.map_comp]`.

Establish `: ((homOfLE (le_top : V ≤ ⊤)).op ≫ (homOfLE hV').op : Opposite.op (⊤ : (Sp Ω).Opens) ⟶ _) = 𝟙 _` using `Subsingleton.elim _ _`. Rewrite using `[this, CategoryTheory.Functor.map_id]`. Conclude with `(Scheme.ΓSpecIso (CommRingCat.of Ω)).inv_hom_id_apply a`. Establish `hval : ∀ i, ev (((M.pt ≫ g).appLE _ _ hV).hom ((GlobalTheory.ProjSpace.coord o n i).f (j PUnit.unit))) = valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i)`. Introduce `i`.

Rewrite using `[valF, dif_pos hW]`. Express the relevant statement in the definitionally equal form `(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (resG (Sp Ω) hV' _) = _`. Rewrite using `[GlobalTheory.ProjSpace.resG_appLE, GlobalTheory.ProjSpace.pullRatio, GlobalTheory.ProjSpace.appLE_appLE]`. Both sides reduce to the same expression. Establish `key : ∀ i, valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i) = e i * ev (τ.s j).val`.

Introduce `i`. Rewrite using `[← hval, H i j hV, map_mul, hconst]`. Establish `h1 : e c * ev (τ.s j).val = 1`. Rewrite using `[← key c, GlobalTheory.ProjSpace.pullRatio_self, ← M.res_apply W ⟨z, hzW⟩, map_one]`. Establish `hc0 : e c ≠ 0` using `left_ne_zero_of_mul_eq_one h1`.

Use `⟨c, hc0, fun i => ?_⟩` and prove the remaining obligations. Establish `e1 : e i / e c = valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i)`. Rewrite using `[key i, eq_inv_of_mul_eq_one_right h1, div_eq_mul_inv]`. Rewrite using `[e1]`. Conclude with `RatModel.valF_mem_O hzW _`.
-/
theorem hasDiv_of_pCrd_pt : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω)
    (n : ℕ) (g : M.Z ⟶ PSpace o n) (e : Fin (n + 1) → Ω), PCrd (M.pt ≫ g) e → M.HasDiv e := by
  intro k Ω o _ _ _ _ M n g e hP z
  obtain ⟨τ, -, H⟩ := hP
  obtain ⟨c, hc⟩ := GlobalTheory.ProjSpace.exists_mem_chart o n (g z)
  let W : M.Z.Opens := g ⁻¹ᵁ GlobalTheory.ProjSpace.chart o n c
  have hzW : z ∈ W := hc
  have hW : ⊤ ≤ M.pt ⁻¹ᵁ W := M.top_le_preimage_pt ⟨z, hzW⟩
  let j : PUnit → (GlobalTheory.ProjSpace.O1 o n).ι := fun _ => c
  let V := ((GlobalTheory.ProjSpace.O1 o n).pull (M.pt ≫ g)).U j
  have hV : V ≤ (M.pt ≫ g) ⁻¹ᵁ (GlobalTheory.ProjSpace.O1 o n).U (j PUnit.unit) :=
    LB.wchart_le (GlobalTheory.ProjSpace.O1 o n) (fun _ => M.pt ≫ g) j PUnit.unit
  have hV' : ⊤ ≤ V := fun y _ => Set.mem_iInter.2 fun _ => hW (Set.mem_univ y)
  let ev : Γ(Sp Ω, V) →+* Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp ((Sp Ω).presheaf.map (homOfLE hV').op).hom
  have hconst : ∀ a : Ω, ev (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom a)) = a := by
    intro a
    change (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (((Sp Ω).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫
      (Sp Ω).presheaf.map (homOfLE hV').op).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom a)) = a
    rw [← Functor.map_comp]
    have : ((homOfLE (le_top : V ≤ ⊤)).op ≫ (homOfLE hV').op : Opposite.op (⊤ : (Sp Ω).Opens) ⟶ _) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]
    exact (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv_hom_id_apply a
  have hval : ∀ i, ev (((M.pt ≫ g).appLE _ _ hV).hom ((GlobalTheory.ProjSpace.coord o n i).f (j PUnit.unit))) =
      valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i) := by
    intro i
    rw [valF, dif_pos hW]
    change (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (resG (Sp Ω) hV' _) = _
    rw [GlobalTheory.ProjSpace.resG_appLE, GlobalTheory.ProjSpace.pullRatio, GlobalTheory.ProjSpace.appLE_appLE]
    rfl
  have key : ∀ i, valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i) = e i * ev (τ.s j).val := by
    intro i
    rw [← hval, H i j hV, map_mul, hconst]
  have h1 : e c * ev (τ.s j).val = 1 := by
    rw [← key c, GlobalTheory.ProjSpace.pullRatio_self, ← M.res_apply W ⟨z, hzW⟩, map_one]
  have hc0 : e c ≠ 0 := left_ne_zero_of_mul_eq_one h1
  refine ⟨c, hc0, fun i => ?_⟩
  have e1 : e i / e c = valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i) := by
    rw [key i, eq_inv_of_mul_eq_one_right h1, div_eq_mul_inv]
  rw [e1]
  exact RatModel.valF_mem_O hzW _

end GlobalTheory.UMin
