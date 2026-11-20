import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepInclStepProj
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.FlagChi Matrix

namespace GlobalTheory.FlagChi

/- English proof (translation)
Introduce `Z _ N A l L r hr hL hA hB`. Use `GlobalTheory.QCoh.epi_of_locally_app_surjective _ fun W x hxW => ?_` and prove the remaining obligations. Take `⟨c₀, hc₀⟩` from `Semi.LB.mem_of_cover hL x`. Take `⟨B, hBt, hreg, -, hunit⟩` from `hB x`. Take `⟨V₁, hx₁, hV₁⟩` from `(hunit c₀ hc₀).exists_nhds`.

Use `choose U' hxU' f hf using fun a => (hreg a l).exists_fnOf`. Set `U : Z.Opens` to `W ⊓ L.U c₀ ⊓ V₁ ⊓ Finset.univ.inf U'`. Establish `hxI : x ∈ Finset.univ.inf U'` using `Finset.inf_induction (p := fun V : Z.Opens => x ∈ V) trivial (fun _ ha _ hb => ⟨ha, hb⟩) fun a _ => hxU' a`. Establish `hxU : x ∈ U` using `⟨⟨⟨hxW, hc₀⟩, hx₁⟩, hxI⟩`. Establish `hUW : U ≤ W` using `inf_le_left.trans (inf_le_left.trans inf_le_left)`.

Establish `hU0 : U ≤ L.U c₀` using `inf_le_left.trans (inf_le_left.trans inf_le_right)`. Establish `hU1 : U ≤ V₁` using `inf_le_left.trans inf_le_right`. Establish `hUa : ∀ a, U ≤ U' a` using `fun a => inf_le_right.trans (Finset.inf_le (Finset.mem_univ a))`. Use `⟨U, hxU, hUW, fun t => ?_⟩` and prove the remaining obligations. Establish `hg : genericPoint Z ∈ U` using `gen_mem hxU`.

Establish `hg0 : genericPoint Z ∈ U ⊓ L.U c₀` using `⟨hg, hU0 hg⟩`. Use `set u : Z.functionField := fnOf _ hg0 (LB.coord t c₀) with hu`. Use `set d : Z.functionField := B l l * r c₀ with hd`. Establish `hd0 : d ≠ 0` using `(hV₁ x hx₁).ne_zero`. Establish `hBll : B l l ≠ 0` using `fun h => hd0 (by rw [hd, h, zero_mul])`.

Establish `hcoord : ∀ c (h : genericPoint Z ∈ U ⊓ L.U c), fnOf _ h (LB.coord t c) = B l l * (u / d) * r c`. Introduce `c h`. Establish `e` using `congrArg (fnOf _ h) (LB.coord_rel t c₀ c (W := U ⊓ L.U c) (le_inf inf_le_left (inf_le_left.trans hU0)) le_rfl (le_inf (inf_le_left.trans hU0) inf_le_right))`. Rewrite `e` using `[fnOf_resG, map_mul, fnOf_resG, fnOf_resG]`. Establish `e'` using `hr c₀ c (memInf (hU0 h.1) h.2)`.

Establish `hG : fnOf _ (memInf (hU0 h.1) h.2) ((L.g c₀ c : Γ(Z, L.U c₀ ⊓ L.U c))) ≠ 0` using `((L.g c₀ c).isUnit.map (fnOf _ (memInf (hU0 h.1) h.2))).ne_zero`. Establish `hrc : (r c : Z.functionField) ≠ 0` using `(r c).ne_zero`. Rewrite using `[hd, hu, e, e']`. Clear the denominators using the available nonvanishing facts. Establish `hregv : ∀ a, ∀ y ∈ U, RegAt y ((A * B) a l * u / d)`.

Introduce `a y hy`. Rewrite using `[div_eq_mul_inv]`. Use `((?_ : RegAt y ((A * B) a l)).mul ?_).mul (hV₁ y (hU1 hy)).inv.regAt` and prove the remaining obligations. Rewrite using `[← hf a]`. Conclude with `regAt_fnOf (hUa a hy) _ _`.

Conclude with `regAt_fnOf (memInf hy (hU0 hy)) _ _`. Set `v : Fin N → Γ(Z, U)` to `fun a => ofRat U _ (hregv a)`. Establish `hgv : ∀ h : genericPoint Z ∈ U, A⁻¹ *ᵥ genVec h v = fun k => B k l * (u / d)`. Introduce `h`. Establish `e1 : genVec h v = A *ᵥ fun k => B k l * (u / d)`.

Use function extensionality and compare the values at `a`. Simplify using `only [genVec, v, fnOf_ofRat, Matrix.mulVec, dotProduct, Matrix.mul_apply]`. Rewrite using `[mul_div_assoc, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _)`. Rewrite using `[e1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]`.

Establish `hv : v ∈ vsec (quotC A⁻¹ l L r) U`. Introduce `h y hy`. Use `⟨fun k hk => ?_, fun c hc => ?_⟩` and prove the remaining obligations. Rewrite using `[hgv h]`. Establish `hlk : l < k` using `by rw [Fin.lt_def]; omega`.

Use `show B k l * (u / d) = 0`. Rewrite using `[hBt hlk, zero_mul]`. Rewrite using `[hgv h, ← hcoord c (memInf h (gen_mem hc))]`. Conclude with `regAt_fnOf (memInf hy hc) _ _`. Use `⟨mk v hv, LB.sec_ext fun c => Cartier.fn_ext fun h => ?_⟩` and prove the remaining obligations.

Rewrite using `[stepProj, fnOf_coord_vproj, coordFn_apply, vec_mk, hgv h.1, hcoord c h]`.
-/
theorem epi_stepProj : ∀ (Z : Scheme.{0}) [IsIntegral Z] (N : ℕ) (A : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) (L : LB Z) (r : L.ι → Z.functionFieldˣ) (hr : IsRatSec L r), L.IsLB → IsUnit A.det → (∀ z : Z, ∃ B : Matrix (Fin N) (Fin N) Z.functionField, B.BlockTriangular id ∧ (∀ a b, RegAt z ((A * B) a b)) ∧ UnitAt z (A * B).det ∧ ∀ c, z ∈ L.U c → UnitAt z (B l l * r c)) → Epi (stepProj A⁻¹ l hr) := by
  intro Z _ N A l L r hr hL hA hB
  refine GlobalTheory.QCoh.epi_of_locally_app_surjective _ fun W x hxW => ?_
  obtain ⟨c₀, hc₀⟩ := Semi.LB.mem_of_cover hL x
  obtain ⟨B, hBt, hreg, -, hunit⟩ := hB x
  obtain ⟨V₁, hx₁, hV₁⟩ := (hunit c₀ hc₀).exists_nhds
  choose U' hxU' f hf using fun a => (hreg a l).exists_fnOf
  let U : Z.Opens := W ⊓ L.U c₀ ⊓ V₁ ⊓ Finset.univ.inf U'
  have hxI : x ∈ Finset.univ.inf U' :=
    Finset.inf_induction (p := fun V : Z.Opens => x ∈ V) trivial (fun _ ha _ hb => ⟨ha, hb⟩)
      fun a _ => hxU' a
  have hxU : x ∈ U := ⟨⟨⟨hxW, hc₀⟩, hx₁⟩, hxI⟩
  have hUW : U ≤ W := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hU0 : U ≤ L.U c₀ := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hU1 : U ≤ V₁ := inf_le_left.trans inf_le_right
  have hUa : ∀ a, U ≤ U' a := fun a => inf_le_right.trans (Finset.inf_le (Finset.mem_univ a))
  refine ⟨U, hxU, hUW, fun t => ?_⟩
  have hg : genericPoint Z ∈ U := gen_mem hxU
  have hg0 : genericPoint Z ∈ U ⊓ L.U c₀ := ⟨hg, hU0 hg⟩
  set u : Z.functionField := fnOf _ hg0 (LB.coord t c₀) with hu
  set d : Z.functionField := B l l * r c₀ with hd
  have hd0 : d ≠ 0 := (hV₁ x hx₁).ne_zero
  have hBll : B l l ≠ 0 := fun h => hd0 (by rw [hd, h, zero_mul])

  have hcoord : ∀ c (h : genericPoint Z ∈ U ⊓ L.U c),
      fnOf _ h (LB.coord t c) = B l l * (u / d) * r c := by
    intro c h
    have e := congrArg (fnOf _ h) (LB.coord_rel t c₀ c (W := U ⊓ L.U c)
      (le_inf inf_le_left (inf_le_left.trans hU0)) le_rfl
      (le_inf (inf_le_left.trans hU0) inf_le_right))
    rw [fnOf_resG, map_mul, fnOf_resG, fnOf_resG] at e
    have e' := hr c₀ c (memInf (hU0 h.1) h.2)
    have hG : fnOf _ (memInf (hU0 h.1) h.2) ((L.g c₀ c : Γ(Z, L.U c₀ ⊓ L.U c))) ≠ 0 :=
      ((L.g c₀ c).isUnit.map (fnOf _ (memInf (hU0 h.1) h.2))).ne_zero
    have hrc : (r c : Z.functionField) ≠ 0 := (r c).ne_zero
    rw [hd, hu, e, e']
    field_simp

  have hregv : ∀ a, ∀ y ∈ U, RegAt y ((A * B) a l * u / d) := by
    intro a y hy
    rw [div_eq_mul_inv]
    refine ((?_ : RegAt y ((A * B) a l)).mul ?_).mul (hV₁ y (hU1 hy)).inv.regAt
    · rw [← hf a]; exact regAt_fnOf (hUa a hy) _ _
    · exact regAt_fnOf (memInf hy (hU0 hy)) _ _
  let v : Fin N → Γ(Z, U) := fun a => ofRat U _ (hregv a)
  have hgv : ∀ h : genericPoint Z ∈ U, A⁻¹ *ᵥ genVec h v = fun k => B k l * (u / d) := by
    intro h
    have e1 : genVec h v = A *ᵥ fun k => B k l * (u / d) := by
      funext a
      simp only [genVec, v, fnOf_ofRat, Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [mul_div_assoc, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _)
    rw [e1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]
  have hv : v ∈ vsec (quotC A⁻¹ l L r) U := by
    intro h y hy
    refine ⟨fun k hk => ?_, fun c hc => ?_⟩
    · rw [hgv h]
      have hlk : l < k := by rw [Fin.lt_def]; omega
      show B k l * (u / d) = 0
      rw [hBt hlk, zero_mul]
    · rw [hgv h, ← hcoord c (memInf h (gen_mem hc))]
      exact regAt_fnOf (memInf hy hc) _ _
  refine ⟨mk v hv, LB.sec_ext fun c => Cartier.fn_ext fun h => ?_⟩
  rw [stepProj, fnOf_coord_vproj, coordFn_apply, vec_mk, hgv h.1, hcoord c h]

end GlobalTheory.FlagChi
