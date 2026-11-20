import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigPull

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun f hf => ?_` and prove the remaining obligations. Take `⟨σ, rfl⟩` from `(H0.bijective_ofSec_top (p := p) (B := B)).2 f`. Assume the negation of the conclusion as `hne`. Establish `hσ : σ ≠ 0` using `fun h => hne (by rw [h, map_zero])`. Establish `hgen` using `(sec_ne_zero_iff σ).1 hσ`.

Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, g y ∈ nonzeroLocus σ := by`. Take `⟨_, hy, ⟨y, rfl⟩⟩` from `hg.inter_open_nonempty _ (nonzeroLocus σ).isOpen ⟨_, hgen⟩`. Conclude with `⟨y, hy⟩`. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 (hB.cover.ge (trivial : g y ∈ (⊤ : X.Opens)))`. Establish `hj : y ∈ (B.pull g).U (fun _ => i)` using `mem_pull.2 hi`.

Establish `e` using `H0.germ_pull (p := p) (B := B) (O := ⊤) g (W := ⊤) le_top (fun _ => i) y trivial hj (H0.ofSec p ⊤ σ)`. Rewrite `e` using `[hf, map_zero]`. Establish `hu : IsUnit ((g.stalkMap y).hom (H0.germ (p` using `p) (O := ⊤) i (g y) (show g y ∈ (⊤ : X.Opens) from trivial) hi (H0.ofSec p ⊤ σ))) := IsUnit.map _ ((H0.germ_ofSec (p := p) (O := ⊤) _ _ (show g y ∈ (⊤ : X.Opens) from trivial) hi σ).symm ▸ (isUnit_ger_iff σ hi).2 hy)`. Rewrite `hu` using `[← e]`. Conclude with `not_isUnit_zero hu`.
-/
theorem pull_top_injective {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ Sp k) (g : Y ⟶ X) (hg : Dense (Set.range g)) (B : LB X) (hB : B.IsLB) :
    Function.Injective (H0.pull (p := p) (B := B) (O := ⊤) g (W := ⊤) le_top) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  obtain ⟨σ, rfl⟩ := (H0.bijective_ofSec_top (p := p) (B := B)).2 f
  by_contra hne
  have hσ : σ ≠ 0 := fun h => hne (by rw [h, map_zero])
  have hgen := (sec_ne_zero_iff σ).1 hσ
  obtain ⟨y, hy⟩ : ∃ y, g y ∈ nonzeroLocus σ := by
    obtain ⟨_, hy, ⟨y, rfl⟩⟩ := hg.inter_open_nonempty _ (nonzeroLocus σ).isOpen ⟨_, hgen⟩
    exact ⟨y, hy⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hB.cover.ge (trivial : g y ∈ (⊤ : X.Opens)))
  have hj : y ∈ (B.pull g).U (fun _ => i) := mem_pull.2 hi
  have e := H0.germ_pull (p := p) (B := B) (O := ⊤) g (W := ⊤) le_top (fun _ => i) y trivial hj
    (H0.ofSec p ⊤ σ)
  rw [hf, map_zero] at e
  have hu : IsUnit ((g.stalkMap y).hom (H0.germ (p := p) (O := ⊤) i (g y) (show g y ∈ (⊤ : X.Opens) from trivial) hi (H0.ofSec p ⊤ σ))) :=
    IsUnit.map _ ((H0.germ_ofSec (p := p) (O := ⊤) _ _ (show g y ∈ (⊤ : X.Opens) from trivial) hi σ).symm ▸ (isUnit_ger_iff σ hi).2 hy)
  rw [← e] at hu
  exact not_isUnit_zero hu

/- English proof (translation)
Use `letI := algebraΓOfHom p`. Introduce `h`. Use `letI : Module E B.Sec := Module.compHom _ (algebraMap E Γ(Y, ⊤))`. Use `haveI : IsScalarTower E Γ(Y, ⊤) B.Sec := IsScalarTower.of_compHom _ _ _`. Establish `e (c : E) : algebraMap E Γ(Y, ⊤) c = algX p ⊤ c`.

Express the relevant statement in the definitionally equal form `p.appTop _ = _`. Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression. Conclude with `Module.Finite.equiv (((cohZeroTwistEquiv B).restrictScalars E).trans (LinearEquiv.ofBijective { H0.ofSec p ⊤ with map_smul' := fun c σ => (e c ▸ H0.ofSec_smul c σ :) } H0.bijective_ofSec_top))`.
-/
theorem finite_H0_top {E : Type} [Field E] {Y : Scheme.{0}} (p : Y ⟶ Sp E) (B : LB Y) :
    letI := algebraΓOfHom p
    Module.Finite E (coh (twist (structureModule Y) B) 0) → Module.Finite E (H0 p B ⊤) := by
  letI := algebraΓOfHom p
  intro h
  letI : Module E B.Sec := Module.compHom _ (algebraMap E Γ(Y, ⊤))
  haveI : IsScalarTower E Γ(Y, ⊤) B.Sec := IsScalarTower.of_compHom _ _ _
  have e (c : E) : algebraMap E Γ(Y, ⊤) c = algX p ⊤ c := by
    change p.appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  exact Module.Finite.equiv (((cohZeroTwistEquiv B).restrictScalars E).trans
    (LinearEquiv.ofBijective { H0.ofSec p ⊤ with
      map_smul' := fun c σ => (e c ▸ H0.ofSec_smul c σ :) } H0.bijective_ofSec_top))

/- English proof (translation)
Introduce `k _ X Y _ p g hp hd hg N hN`. Use `letI := algebraΓOfHom p`. Use `letI := algebraΓOfHom (g ≫ p)`. Establish `hL : ∀ m, (lbPow (N.pull g) m).IsLB` using `fun m => isLB_lbPow (LB.isLB_pull hN.isLB g) m`. Establish `hfin : ∀ m, Module.Finite k (coh (twist (structureModule Y) (lbPow (N.pull g) m)) 0)` using `fun m => finite_coh_zero_twist_of_isProjOver (fun _ => rfl) hp (hL m)`.

Establish `hle : ∀ m, lbH0 k (lbPow N m) ≤ lbH0 k (lbPow (N.pull g) m)`. Introduce `m`. Establish `hB` using `isLB_lbPow hN.isLB m`. Establish `hB'` using `LB.isLB_pull hB g`. Establish `ec` using `(cls_eq_iff (hL m) hB').2 (lbIso_lbPow_pull hN.isLB g m)`.

Rewrite using `[lineBundleGlobalSectionsDim_congr_picardClass (hL m) hB' ec, ← H0.finrank_top p, ← H0.finrank_top (g ≫ p)]`. Use `haveI := finite_H0_top (g ≫ p) ((lbPow N m).pull g) (finite_coh_zero_twist_congr hB' (hL m) ec.symm (hfin m))`. Conclude with `LinearMap.finrank_le_finrank_of_injective (pull_top_injective p g hg _ hB)`. Take `⟨D, hD, c, hc, hm⟩` from `hN.growth`. Conclude with `⟨LB.isLB_pull hN.isLB g, hfin, D, hd.trans hD, c, hc, hm.mono fun m h => h.trans (by exact_mod_cast hle m)⟩`.
-/
theorem isBig_pull : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (g : Y ⟶ X), IsProjOver (g ≫ p) → topologicalKrullDim Y = topologicalKrullDim X →
    Dense (Set.range g) → ∀ N : LB X, (letI := algebraΓOfHom p; IsBig k N) →
    (letI := algebraΓOfHom (g ≫ p); IsBig k (N.pull g)) := by
  intro k _ X Y _ p g hp hd hg N hN
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (g ≫ p)
  have hL : ∀ m, (lbPow (N.pull g) m).IsLB := fun m => isLB_lbPow (LB.isLB_pull hN.isLB g) m
  have hfin : ∀ m, Module.Finite k (coh (twist (structureModule Y) (lbPow (N.pull g) m)) 0) :=
    fun m => finite_coh_zero_twist_of_isProjOver (fun _ => rfl) hp (hL m)
  have hle : ∀ m, lbH0 k (lbPow N m) ≤ lbH0 k (lbPow (N.pull g) m) := by
    intro m
    have hB := isLB_lbPow hN.isLB m
    have hB' := LB.isLB_pull hB g
    have ec := (cls_eq_iff (hL m) hB').2 (lbIso_lbPow_pull hN.isLB g m)
    rw [lineBundleGlobalSectionsDim_congr_picardClass (hL m) hB' ec, ← H0.finrank_top p, ← H0.finrank_top (g ≫ p)]
    haveI := finite_H0_top (g ≫ p) ((lbPow N m).pull g)
      (finite_coh_zero_twist_congr hB' (hL m) ec.symm (hfin m))
    exact LinearMap.finrank_le_finrank_of_injective (pull_top_injective p g hg _ hB)
  obtain ⟨D, hD, c, hc, hm⟩ := hN.growth
  exact ⟨LB.isLB_pull hN.isLB g, hfin, D, hd.trans hD, c, hc,
    hm.mono fun m h => h.trans (by exact_mod_cast hle m)⟩

end GlobalTheory.BigPull
