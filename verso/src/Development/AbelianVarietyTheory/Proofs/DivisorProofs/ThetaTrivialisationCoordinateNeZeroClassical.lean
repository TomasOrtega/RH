import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.CoordNe

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

/- English proof (translation)
Use `(AddSubgroup.eq_bot_iff_forall _).2 fun a ha => ?_` and prove the remaining obligations. Establish `ha' : ∀ h : S.Gam, eStd S.g _ a h = 0` using `fun h => ha h trivial`. Use function extensionality and compare the values at `k`. Break down `k with i | i` into its components or cases. Use `ha' (Pi.single (Sum.inr i) 1)` as an intermediate fact.

Simplify `this` using `[eStd, Pi.single_apply]`. Use `ha' (Pi.single (Sum.inl i) 1)` as an intermediate fact. Simplify `this` using `[eStd, Pi.single_apply]`.
-/
theorem perp_top (S : ThetaSys o Ω) : S.perp ⊤ = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun a ha => ?_
  have ha' : ∀ h : S.Gam, eStd S.g _ a h = 0 := fun h => ha h trivial
  funext k
  rcases k with i | i
  · have := ha' (Pi.single (Sum.inr i) 1)
    simpa [eStd, Pi.single_apply] using this
  · have := ha' (Pi.single (Sum.inl i) 1)
    simpa [eStd, Pi.single_apply] using this

/- English proof (translation)
Establish `h : S.supI M z = {x | S.th x ≠ 0}`. Use `Set.ext fun x => ⟨fun hx => hx.1, fun hx => ⟨hx, fun i => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[div_eq_mul_inv]`. Conclude with `RatModel.ringOn_le_O hz (mul_mem (hO.le (S.th_mem i)) (hO.th_unit x hx))`. Unfold `ThetaSys.TT ThetaSys.HH`.

Rewrite using `[h, S.supp, perp_top]`.
-/
theorem TT_eq_bot {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {z : M.Z} (hz : z ∈ U₀) :
    S.TT M z = ⊥ := by
  have h : S.supI M z = {x | S.th x ≠ 0} := by
    refine Set.ext fun x => ⟨fun hx => hx.1, fun hx => ⟨hx, fun i => ?_⟩⟩
    rw [div_eq_mul_inv]
    exact RatModel.ringOn_le_O hz (mul_mem (hO.le (S.th_mem i)) (hO.th_unit x hx))
  unfold ThetaSys.TT ThetaSys.HH
  rw [h, S.supp, perp_top]

/- English proof (translation)
Establish `: NeZero (S.r * S.N)` using `⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩`. Establish `: Finite S.Gam` using `inferInstance`. Use `isOpen_iff_forall_mem_open.2 fun z hz => ⟨⋂ x ∈ S.supI M z, {w | M.Div S.th x w}, fun w hw => ?_, (Set.toFinite _).isOpen_biInter fun x _ => M.isOpen_setOf_div S.th x, Set.mem_iInter₂.2 fun x hx => hx⟩` and prove the remaining obligations. Establish `hsup : S.supI M z ⊆ S.supI M w` using `fun x hx => Set.mem_iInter₂.1 hw x hx`. Establish `h : S.TT M w ≤ S.TT M z` using `fun a ha x hx => ha x (AddSubgroup.closure_mono hsup hx)`.

Conclude with `le_bot_iff.1 (h.trans (le_of_eq hz))`.
-/
theorem isOpen_TT (S : ThetaSys o Ω) (M : RatModel o Ω) : IsOpen {z | S.TT M z = ⊥} := by
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have : Finite S.Gam := inferInstance
  refine isOpen_iff_forall_mem_open.2 fun z hz => ⟨⋂ x ∈ S.supI M z, {w | M.Div S.th x w}, fun w hw => ?_,
    (Set.toFinite _).isOpen_biInter fun x _ => M.isOpen_setOf_div S.th x, Set.mem_iInter₂.2 fun x hx => hx⟩
  have hsup : S.supI M z ⊆ S.supI M w := fun x hx => Set.mem_iInter₂.1 hw x hx
  have h : S.TT M w ≤ S.TT M z := fun a ha x hx => ha x (AddSubgroup.closure_mono hsup hx)
  exact le_bot_iff.1 (h.trans (le_of_eq hz))

/- English proof (translation)
Introduce `o' Ω _ _ _ S ρ M U₀ EE FinalForm hO x R _ _ _ j D hPsi p _ y ev hCen hfac α s hs h0`. Set `w : Sp (PadicAlgCl p)` to `(⊥ : PrimeSpectrum (PadicAlgCl p))`. Establish `hW : IsOpen ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)`. Use `IsOpen.preimage (spMap j ≫ M.Z.fromSpecStalk x).continuous ?_` and prove the remaining obligations. Rewrite using `[FinalForm.ab]`.

Conclude with `isOpen_TT S M`. Establish `hp : spMap ev (gPt p w) ∈ (spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G`. Rewrite using `[Set.mem_preimage, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hfac, FinalForm.ab]`. Conclude with `TT_eq_bot hO (hCen.2 ⟨w, rfl⟩)`. Apply `GlobalTheory.PsiCoordLocal.not_mem_of_coord hW hp (hPsi α) hs` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(ev s : PadicAlgCl p) ∈ (⊥ : Ideal (PadicAlgCl p))`. Conclude with `h0`.
-/
theorem coord_ne_zero : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (x : M.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R) (D : DegData R (maximalIdeal R)), (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ α s, PsiCoord D.toPre α s → (ev s : PadicAlgCl p) ≠ 0 := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm hO x R _ _ _ j D hPsi p _ y ev hCen hfac α s hs h0
  let w : Sp (PadicAlgCl p) := (⊥ : PrimeSpectrum (PadicAlgCl p))
  have hW : IsOpen ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G) := by
    refine IsOpen.preimage (spMap j ≫ M.Z.fromSpecStalk x).continuous ?_
    rw [FinalForm.ab]
    exact isOpen_TT S M
  have hp : spMap ev (gPt p w) ∈ (spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G := by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hfac, FinalForm.ab]
    exact TT_eq_bot hO (hCen.2 ⟨w, rfl⟩)
  apply GlobalTheory.PsiCoordLocal.not_mem_of_coord hW hp (hPsi α) hs
  change (ev s : PadicAlgCl p) ∈ (⊥ : Ideal (PadicAlgCl p))
  exact h0

end GlobalTheory.Poinc.CoordNe
