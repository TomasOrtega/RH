import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardAutLzGmap

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section W3

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

/- English proof (translation)
Rewrite using `[FlagG.X, X.Fu_e]`. Both sides reduce to the same expression.
-/
theorem fuX : (X.Fu u).X = Xs X := by
  rw [FlagG.X, X.Fu_e]
  rfl

/- English proof (translation)
Take `⟨hi, he, -, hz, -⟩` from `hγ`. Use `⟨hi, fun j => ?_, ?_⟩` and prove the remaining obligations. Unfold `Formalism.MainNotions.S.FlagG.Xa`. Rewrite using `[Submodule.map_span, Set.image_image]`. Use `congr 1`.

Apply `Set.image_congr` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[X.Fu_e u]`. Conclude with `he a`. Use `show γ (X.Fu u).z = (X.Fu u).z`.

Rewrite using `[X.flagZVector u]`. Conclude with `hz`.
-/
theorem AH_stab {Λ : Submodule (𝓞 D.host.E) (VS D).V} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hγ : γ ∈ AH X u Λ) : γ ∈ stabF D (X.Fu u) := by
  obtain ⟨hi, he, -, hz, -⟩ := hγ
  refine ⟨hi, fun j => ?_, ?_⟩
  · unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro a _
    rw [X.Fu_e u]
    exact he a
  · show γ (X.Fu u).z = (X.Fu u).z
    rw [X.flagZVector u]
    exact hz

def indA (Λ : Submodule (𝓞 D.host.E) (VS D).V) (γ : ↥(AH X u Λ)) : WbQ D (X.Fu u) → WbQ D (X.Fu u) :=
  ind (X.Fu u) (AH_stab X u γ.2)

/- English proof (translation)
Introduce `x hx`. Rewrite `hx` using `[fuX]`. Conclude with `hT_Xs_prV X hx v`.
-/
theorem prV_perp (v : (VS D).V) : prV X v ∈ perpS (VS D) (X.Fu u).X := by
  intro x hx
  rw [fuX] at hx
  exact hT_Xs_prV X hx v

/- English proof (translation)
Rewrite using `[prV_apply]`. Simplify using `[he, hf]`.
-/
theorem prV_fix (w : (VS D).V) (he : ∀ a, (VS D).hT (X.eX a) w = 0) (hf : ∀ a, (VS D).hT (X.fY a) w = 0) :
    prV X w = w := by
  rw [prV_apply]
  simp [he, hf]

/- English proof (translation)
Establish `h1 : ∀ a, (VS D).hT (X.eX a) (g (prV X v)) = 0` using `fun a => by`. Rewrite using `[← hge a, hgi, hT_e_prV]`. Establish `h2 : ∀ a, (VS D).hT (X.fY a) (g (prV X v)) = 0` using `fun a => by`. Rewrite using `[← hgf a, hgi, hT_f_prV]`. Conclude with `prV_fix X _ h1 h2`.
-/
theorem prV_of_fix (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hgi : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hge : ∀ a, g (X.eX a) = X.eX a) (hgf : ∀ a, g (X.fY a) = X.fY a) (v : (VS D).V) :
    prV X (g (prV X v)) = g (prV X v) := by
  have h1 : ∀ a, (VS D).hT (X.eX a) (g (prV X v)) = 0 := fun a => by
    rw [← hge a, hgi, hT_e_prV]
  have h2 : ∀ a, (VS D).hT (X.fY a) (g (prV X v)) = 0 := fun a => by
    rw [← hgf a, hgi, hT_f_prV]
  exact prV_fix X _ h1 h2

/- English proof (translation)
Rewrite using `[sub_prV_eq]`. Simplify using `[map_sum, map_smul, hge, hgf]`.
-/
theorem fix_sub_prV (g : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hge : ∀ a, g (X.eX a) = X.eX a) (hgf : ∀ a, g (X.fY a) = X.fY a) (v : (VS D).V) :
    g (v - prV X v) = v - prV X v := by
  rw [sub_prV_eq]
  simp [map_sum, map_smul, hge, hgf]

/- English proof (translation)
Introduce `γ γ' hγγ`. Take `⟨hi, he, hf, -, -⟩` from `γ.2`. Take `⟨hi', he', hf', -, -⟩` from `γ'.2`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearEquiv.ext` to reduce the goal to its premises.

Introduce `y`. Establish `hq` using `congrFun hγγ (Submodule.Quotient.mk ⟨prV X y, prV_perp X u y⟩)`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = Submodule.Quotient.mk _ at hq`. Rewrite `hq` using `[Submodule.Quotient.eq]`. Establish `hd : γ.1 (prV X y) - γ'.1 (prV X y) ∈ Xs X`.

Rewrite using `[← fuX X u]`. Conclude with `hq`. Establish `h0` using `prV_Xs X hd`. Rewrite `h0` using `[map_sub, prV_of_fix X γ.1 hi he hf, prV_of_fix X γ'.1 hi' he' hf', sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[fix_sub_prV X γ.1 he hf, fix_sub_prV X γ'.1 he' hf', h0]`. Use `_ = γ'.1 y := by rw [← map_add, sub_add_cancel]`.
-/
theorem indA_inj (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Function.Injective (indA X u Λ) := by
  intro γ γ' hγγ
  obtain ⟨hi, he, hf, -, -⟩ := γ.2
  obtain ⟨hi', he', hf', -, -⟩ := γ'.2
  apply Subtype.ext
  apply LinearEquiv.ext
  intro y
  have hq := congrFun hγγ (Submodule.Quotient.mk ⟨prV X y, prV_perp X u y⟩)
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ at hq
  rw [Submodule.Quotient.eq] at hq
  have hd : γ.1 (prV X y) - γ'.1 (prV X y) ∈ Xs X := by
    rw [← fuX X u]
    exact hq
  have h0 := prV_Xs X hd
  rw [map_sub, prV_of_fix X γ.1 hi he hf, prV_of_fix X γ'.1 hi' he' hf', sub_eq_zero] at h0
  calc γ.1 y = γ.1 (y - prV X y) + γ.1 (prV X y) := by rw [← map_add, sub_add_cancel]
    _ = γ'.1 (y - prV X y) + γ'.1 (prV X y) := by
        rw [fix_sub_prV X γ.1 he hf, fix_sub_prV X γ'.1 he' hf', h0]
    _ = γ'.1 y := by rw [← map_add, sub_add_cancel]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `y hy`. Rewrite `hy`, the goal using `[← lat_coe]`. Rewrite using `[SetLike.mem_coe, ← hΛ, mem_gmap, LinearEquiv.symm_apply_apply]`. Conclude with `hy`.

Introduce `y hy`. Rewrite `hy`, the goal using `[← lat_coe]`. Rewrite `hy` using `[SetLike.mem_coe, ← hΛ, mem_gmap]`. Conclude with `hy`.
-/
theorem mem_lat_gmap (h : Hfin X u) {γ0 : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hΛ : Formalism.HermitianLatticesTheory.gmap γ0 (lat X u h) = lat X u h) :
    (∀ y ∈ latOf X u h, γ0 y ∈ latOf X u h) ∧ (∀ y ∈ latOf X u h, γ0.symm y ∈ latOf X u h) := by
  constructor
  · intro y hy
    rw [← lat_coe] at hy ⊢
    rw [SetLike.mem_coe, ← hΛ, mem_gmap, LinearEquiv.symm_apply_apply]
    exact hy
  · intro y hy
    rw [← lat_coe] at hy ⊢
    rw [SetLike.mem_coe, ← hΛ, mem_gmap] at hy
    exact hy

/- English proof (translation)
Use extensionality with `φ`. Rewrite using `[autLz_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ0, hγ0, hΛ, rfl⟩`. Establish `hinv : γ0⁻¹ ∈ stabF D (X.Fu u)` using `st_inv (X.Fu u) hγ0`.

Set `γ : (VS D).V ≃ₗ[D.host.E] (VS D).V` to `LinearEquiv.ofLinear (gW X γ0) (gW X γ0⁻¹) (LinearMap.ext fun y => gW_gW X u hγ0 hinv (fun w => LinearEquiv.apply_symm_apply γ0 w) y) (LinearMap.ext fun y => gW_gW X u hinv hγ0 (fun w => LinearEquiv.symm_apply_apply γ0 w) y)`. Establish `hm` using `mem_lat_gmap X u h hΛ`. Establish `hAH : γ ∈ AH X u (lat X u h)`. Use `⟨fun x y => gW_isom X u hγ0 x y, fun a => gW_e X a, fun a => gW_f X a, stabilizer_fix_anisotropic X u hγ0, ?_⟩` and prove the remaining obligations. Use extensionality with `y`.

Rewrite using `[mem_gmap]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Rewrite `hy`, the goal using `[← SetLike.mem_coe, lat_coe]`. Use `gW_mem X u h h hm.1 hy` as an intermediate fact.

Establish `e : gW X γ0 (γ.symm y) = y` using `gW_gW X u hγ0 hinv (fun w => LinearEquiv.apply_symm_apply γ0 w) y`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Introduce `hy`. Rewrite `hy`, the goal using `[← SetLike.mem_coe, lat_coe]`. Conclude with `gW_mem X u h h (fun w hw => hm.2 w hw) hy`.

Use `⟨⟨γ, hAH⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Use `Submodule.Quotient.induction_on _ q (fun x => ?_)` and prove the remaining obligations. Use `show ind (X.Fu u) (AH_stab X u hAH) (Submodule.Quotient.mk x) = ind (X.Fu u) hγ0 (Submodule.Quotient.mk x)`. Rewrite using `[ind_mk, ind_mk, Submodule.Quotient.eq]`.

Use `show gW X γ0 x.1 - γ0 x.1 ∈ (X.Fu u).X`. Apply `(show Xs X ≤ (X.Fu u).X from (fuX X u).ge)` to reduce the goal to its premises. Establish `hx : ∀ a, (VS D).hT (X.eX a) x.1 = 0` using `fun a => x.2 _ (by rw [fuX X u]; exact eX_mem_Xs X a)`. Establish `h1` using `sub_prV_mem_Xs X hx`. Establish `h2` using `stab_Xs X u hγ0 h1`.

Establish `h3` using `stab_perp X u hγ0 x.1`. Establish `e : gW X γ0 x.1 - γ0 x.1 = (x.1 - prV X x.1) - γ0 (x.1 - prV X x.1) - (γ0 (prV X x.1) - prV X (γ0 (prV X x.1)))`. Rewrite using `[gW_apply, map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) h3`. Introduce and unpack `⟨γ, rfl⟩`. Conclude with `⟨γ.1, AH_stab X u γ.2, γ.2.2.2.2.2, rfl⟩`.
-/
theorem autLz_range (h : Hfin X u) : autLz D (X.Fu u) (lat X u h) = Set.range (indA X u (lat X u h)) := by
  ext φ
  rw [autLz_iff]
  constructor
  · rintro ⟨γ0, hγ0, hΛ, rfl⟩
    have hinv : γ0⁻¹ ∈ stabF D (X.Fu u) := st_inv (X.Fu u) hγ0
    let γ : (VS D).V ≃ₗ[D.host.E] (VS D).V := LinearEquiv.ofLinear (gW X γ0) (gW X γ0⁻¹)
      (LinearMap.ext fun y => gW_gW X u hγ0 hinv (fun w => LinearEquiv.apply_symm_apply γ0 w) y)
      (LinearMap.ext fun y => gW_gW X u hinv hγ0 (fun w => LinearEquiv.symm_apply_apply γ0 w) y)
    have hm := mem_lat_gmap X u h hΛ
    have hAH : γ ∈ AH X u (lat X u h) := by
      refine ⟨fun x y => gW_isom X u hγ0 x y, fun a => gW_e X a, fun a => gW_f X a, stabilizer_fix_anisotropic X u hγ0, ?_⟩
      ext y
      rw [mem_gmap]
      constructor
      · intro hy
        rw [← SetLike.mem_coe, lat_coe] at hy ⊢
        have := gW_mem X u h h hm.1 hy
        have e : gW X γ0 (γ.symm y) = y := gW_gW X u hγ0 hinv (fun w => LinearEquiv.apply_symm_apply γ0 w) y
        rwa [e] at this
      · intro hy
        rw [← SetLike.mem_coe, lat_coe] at hy ⊢
        exact gW_mem X u h h (fun w hw => hm.2 w hw) hy
    refine ⟨⟨γ, hAH⟩, ?_⟩
    funext q
    refine Submodule.Quotient.induction_on _ q (fun x => ?_)
    show ind (X.Fu u) (AH_stab X u hAH) (Submodule.Quotient.mk x) = ind (X.Fu u) hγ0 (Submodule.Quotient.mk x)
    rw [ind_mk, ind_mk, Submodule.Quotient.eq]
    show gW X γ0 x.1 - γ0 x.1 ∈ (X.Fu u).X
    apply (show Xs X ≤ (X.Fu u).X from (fuX X u).ge)
    have hx : ∀ a, (VS D).hT (X.eX a) x.1 = 0 := fun a => x.2 _ (by rw [fuX X u]; exact eX_mem_Xs X a)
    have h1 := sub_prV_mem_Xs X hx
    have h2 := stab_Xs X u hγ0 h1
    have h3 := stab_perp X u hγ0 x.1
    have e : gW X γ0 x.1 - γ0 x.1 =
        (x.1 - prV X x.1) - γ0 (x.1 - prV X x.1) - (γ0 (prV X x.1) - prV X (γ0 (prV X x.1))) := by
      rw [gW_apply, map_sub]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) h3
  · rintro ⟨γ, rfl⟩
    exact ⟨γ.1, AH_stab X u γ.2, γ.2.2.2.2.2, rfl⟩

/- English proof (translation)
Rewrite using `[autLz_range]`. Conclude with `(Nat.card_range_of_injective (indA_inj X u _)).symm`.
-/
theorem card_AH (h : Hfin X u) :
    Nat.card ↥(AH X u (lat X u h)) = Nat.card ↥(autLz D (X.Fu u) (lat X u h)) := by
  rw [autLz_range]
  exact (Nat.card_range_of_injective (indA_inj X u _)).symm

end W3

end Formalism.L2.SG.RhoPf
