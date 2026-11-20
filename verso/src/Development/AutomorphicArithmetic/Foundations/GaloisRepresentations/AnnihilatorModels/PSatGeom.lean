import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Use `show B.bind (fun b => {(b : ℂ)}) = _`. Conclude with `Multiset.bind_singleton B _`.
-/
private theorem coe_bind (B : Multiset ℂˣ) :
    (do let a ← B; pure (a : ℂ) : Multiset ℂ) = B.map fun b : ℂˣ => (b : ℂ) := by
  show B.bind (fun b => {(b : ℂ)}) = _
  exact Multiset.bind_singleton B _

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h a B`. Establish `h0 : (0 : ℂ) ∉ B.map (fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ))`. Simplify using the standard rewrite rules. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show ((WD.lpUnr h _).lpTw _).unr`.

Rewrite using `[WD.unr_tw]`. Conclude with `(WD.lpUnr_spec _ h0).1`. Introduce `g hg`. Use `show ((WD.lpUnr h _).lpTw _).charPol g = _`. Unfold `WD.lpUnr`.

Rewrite using `[WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.diag_ρ, hg, coe_bind]`. Establish `hsm : ∀ (s : ℂ) {ι : Type} (f : ι → ℂ), s • diagEnd f = diagEnd (fun i => s * f i)`. Introduce `s ι f`. Use extensionality with `v i`. Simplify using `[diagEnd, mul_assoc]`.

Rewrite using `[hsm, charpoly_diagEnd, Finset.prod_eq_multiset_prod]`. Use `set s : ℂ := (↑(normV w) ^ (((1 - (a : ℝ)) / 2 : ℝ) : ℂ)) ^ (-1 : ℤ) with hs`. Use `(congrArg Multiset.prod (Multiset.map_univ (B.map (fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ))) (fun x => Polynomial.X - Polynomial.C (s * ↑(WD.unitOf x) ^ (-1 : ℤ))))).trans ?_` and prove the remaining obligations. Unfold `rootPol`. Rewrite using `[Multiset.map_map, Multiset.map_map, Multiset.map_map]`.

Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `b _`. Simplify using `only [Function.comp_apply]`. Establish `hs' : s = (normV w : ℂ) ^ (((a : ℂ) - 1) / 2)`.

Rewrite using `[hs, zpow_neg_one, ← Complex.cpow_neg]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[WD.coe_unitOf (Units.ne_zero _), Units.val_inv_eq_inv_val, zpow_neg_one, inv_inv, hs']`.
-/
theorem UpperTheory.Gal.crystallineComparison.satGeom_of :
    SatGeom := by
  intro E Ω _ _ _ _ _ A w h a B
  have h0 : (0 : ℂ) ∉ B.map (fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ)) := by
    simp
  refine ⟨?_, ?_⟩
  · show ((WD.lpUnr h _).lpTw _).unr
    rw [WD.unr_tw]
    exact (WD.lpUnr_spec _ h0).1
  intro g hg
  show ((WD.lpUnr h _).lpTw _).charPol g = _
  unfold WD.lpUnr
  rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.diag_ρ, hg, coe_bind]
  have hsm : ∀ (s : ℂ) {ι : Type} (f : ι → ℂ), s • diagEnd f = diagEnd (fun i => s * f i) := by
    intro s ι f
    ext v i
    simp [diagEnd, mul_assoc]
  rw [hsm, charpoly_diagEnd, Finset.prod_eq_multiset_prod]
  set s : ℂ := (↑(normV w) ^ (((1 - (a : ℝ)) / 2 : ℝ) : ℂ)) ^ (-1 : ℤ) with hs
  refine (congrArg Multiset.prod (Multiset.map_univ (B.map (fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ)))
    (fun x => Polynomial.X - Polynomial.C (s * ↑(WD.unitOf x) ^ (-1 : ℤ))))).trans ?_
  unfold rootPol
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro b _
  simp only [Function.comp_apply]
  have hs' : s = (normV w : ℂ) ^ (((a : ℂ) - 1) / 2) := by
    rw [hs, zpow_neg_one, ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  rw [WD.coe_unitOf (Units.ne_zero _), Units.val_inv_eq_inv_val, zpow_neg_one, inv_inv, hs']
