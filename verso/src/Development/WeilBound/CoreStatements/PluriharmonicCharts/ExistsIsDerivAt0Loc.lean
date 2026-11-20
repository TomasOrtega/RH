import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_period

open GlobalTheory GlobalTheory.FibreDeriv GlobalTheory.VerticalDeriv

/- English proof (translation)
Take `⟨U, hU, hxU, -⟩` from `exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤) (x := e 0 (default : PrimeSpectrum ℂ)) trivial`. Establish `h0 : ⊤ ≤ e 0 ⁻¹ᵁ U` using `(top_le_preimage_iff_mem _ U).2 hxU`. Establish `hd` using `LocalLift.hol_differentiableAt hol hB h0`. Set `J : Γ(Z, U) →+* DualNumber ℂ` to `{ toFun := fun f => jet w (fun z => valAt' (e z) U f) map_one' := by`. Establish `: (fun z => valAt' (e z) U 1) =ᶠ[nhds 0] fun _ => 1` using `by filter_upwards [LocalLift.hol_eventually_mem hol hB h0] with z hz`.

Conclude with `valAt'_one _ hz.2`. Rewrite using `[jet_congr w this, jet_const, map_one]`. Use the proof step `map_zero' := by`. Simplify using `only [valAt'_zero]`. Rewrite using `[jet_const, map_zero]`.

Use the proof step `map_add' := fun f f' => by`. Simplify using `only [valAt'_add]`. Conclude with `jet_add w (hd f) (hd f')`. Use the proof step `map_mul' := fun f f' => by`. Simplify using `only [valAt'_mul]`.

Conclude with `jet_mul w (hd f) (hd f') }`. Take `⟨v, hv, hve⟩` from `TangentOrigin.exists_evalPt_eq hU J`. Use `⟨v, isDerivAt0_of_affine ?_ hU hv fun a => ⟨hd a, DFunLike.congr_fun hve a⟩⟩` and prove the remaining obligations. Use `TangentOrigin.ext_evalPt hU ((TangentOrigin.top_le_preimage_iff v U).1 hv) h0 (RingHom.ext fun f => ?_)` and prove the remaining obligations. Use `(TangentOrigin.evalPt_spMap_comp TangentOrigin.fstC v U hv _ f).trans ?_` and prove the remaining obligations.

Rewrite using `[hve, ← TangentOrigin.valAt'_eq_evalPt]`. Conclude with `fst_jet w (fun z => valAt' (e z) U f)`.
-/
theorem exists_isDerivAt0_loc {g : ℕ} {Z : Scheme.{0}} {B : Set (Fin g → ℂ)} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)}
    (hol : IsHolTo B e) (hB : 0 ∈ B) (w : Fin g → ℂ) :
    ∃ v : Sp (DualNumber ℂ) ⟶ Z, IsDerivAt0 e w v := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := e 0 (default : PrimeSpectrum ℂ)) trivial
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ U).2 hxU
  have hd := LocalLift.hol_differentiableAt hol hB h0
  let J : Γ(Z, U) →+* DualNumber ℂ :=
    { toFun := fun f => jet w (fun z => valAt' (e z) U f)
      map_one' := by
        have : (fun z => valAt' (e z) U 1) =ᶠ[nhds 0] fun _ => 1 := by
          filter_upwards [LocalLift.hol_eventually_mem hol hB h0] with z hz
          exact valAt'_one _ hz.2
        rw [jet_congr w this, jet_const, map_one]
      map_zero' := by
        simp only [valAt'_zero]
        rw [jet_const, map_zero]
      map_add' := fun f f' => by
        simp only [valAt'_add]
        exact jet_add w (hd f) (hd f')
      map_mul' := fun f f' => by
        simp only [valAt'_mul]
        exact jet_mul w (hd f) (hd f') }
  obtain ⟨v, hv, hve⟩ := TangentOrigin.exists_evalPt_eq hU J
  refine ⟨v, isDerivAt0_of_affine ?_ hU hv fun a => ⟨hd a, DFunLike.congr_fun hve a⟩⟩
  refine TangentOrigin.ext_evalPt hU ((TangentOrigin.top_le_preimage_iff v U).1 hv) h0 (RingHom.ext fun f => ?_)
  refine (TangentOrigin.evalPt_spMap_comp TangentOrigin.fstC v U hv _ f).trans ?_
  rw [hve, ← TangentOrigin.valAt'_eq_evalPt]
  exact fst_jet w (fun z => valAt' (e z) U f)

end PositivityTheory.Xgp.c_bm_exists_period
