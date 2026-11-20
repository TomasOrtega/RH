import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CircleHomEqZpow
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealPointUnitaryWithComponents
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitCharExp

/- English proof (translation)
Establish `hu : Continuous (Circle.toUnits : Circle →* ℂˣ)`. Use `Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩` and prove the remaining obligations. Conclude with `(continuous_subtype_val.comp (continuous_inv (G := Circle))).congr fun u => by simp [Function.comp, Circle.coe_inv]`. Take `⟨k, hk⟩` from `GlobalTheory.circle_hom_eq_zpow (ψ.comp Circle.toUnits) (hc.comp hu)`. Use `⟨k, fun z => ?_⟩` and prove the remaining obligations.

Establish `h0 : 0 < ‖(z : ℂ)‖` using `norm_pos_iff.2 z.ne_zero`. Establish `h1 : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast h0.ne'`. Establish `hs : ((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (Real.sqrt_pos.2 h0).ne'`. Set `u : Circle` to `⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by`. Simplify using `[Submonoid.unitSphere, h0.ne']⟩`.

Establish `hu' : (u : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ)` using `rfl`. Establish `e : z = Circle.toUnits u * (Units.mk0 _ hs * Units.mk0 _ hs)`. Apply `Units.ext` to reduce the goal to its premises. Use `show (z : ℂ) = (u : ℂ) * (((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ) * ((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ))`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt h0.le, hu', div_mul_cancel₀ _ h1]`.

Establish `e2 : ψ z = u ^ k`. Rewrite using `[e, map_mul, h _ (Complex.conj_ofReal _), mul_one]`. Conclude with `hk u`. Rewrite using `[e2, ← hu', Circle.coe_zpow]`.
-/
theorem exists_zpow_of_trivial (ψ : ℂˣ →* Circle) (hc : Continuous ψ)
    (h : ∀ s : ℂˣ, starRingEnd ℂ (s : ℂ) = s → ψ (s * s) = 1) :
    ∃ k : ℤ, ∀ z : ℂˣ, ((ψ z : Circle) : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ k := by
  have hu : Continuous (Circle.toUnits : Circle →* ℂˣ) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    exact (continuous_subtype_val.comp (continuous_inv (G := Circle))).congr fun u => by simp [Function.comp, Circle.coe_inv]
  obtain ⟨k, hk⟩ := GlobalTheory.circle_hom_eq_zpow (ψ.comp Circle.toUnits) (hc.comp hu)
  refine ⟨k, fun z => ?_⟩
  have h0 : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 z.ne_zero
  have h1 : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have hs : ((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 h0).ne'
  let u : Circle := ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
    simp [Submonoid.unitSphere, h0.ne']⟩
  have hu' : (u : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := rfl
  have e : z = Circle.toUnits u * (Units.mk0 _ hs * Units.mk0 _ hs) := by
    apply Units.ext
    show (z : ℂ) = (u : ℂ) * (((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ) * ((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ))
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0.le, hu', div_mul_cancel₀ _ h1]
  have e2 : ψ z = u ^ k := by
    rw [e, map_mul, h _ (Complex.conj_ofReal _), mul_one]
    exact hk u
  rw [e2, ← hu', Circle.coe_zpow]

variable {D : D7} {θ : InfFam D}

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `h.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_sub, RingHom.map_sub, h2, sub_self]`.
-/
theorem ext_of_chart {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) {a b : AE D}
    (h1 : finPart D a = finPart D b) (h2 : ∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) : a = b := by
  rw [← sub_eq_zero]
  refine h.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => ?_
  rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]

/- English proof (translation)
Establish `a1 : ∀ z, finPart D (1 + σ (z - 1)) = 1` using `fun z => by rw [RingHom.map_add, h.fin, add_zero, RingHom.map_one]`. Establish `a2 : ∀ z τ, θ τ (infPart D (1 + σ (z - 1))) = z τ` using `fun z τ => by`. Rewrite using `[RingHom.map_add, RingHom.map_add, h.comp, RingHom.map_one, RingHom.map_one]`. Simplify using the standard rewrite rules. Use `⟨{ toFun := fun z => 1 + σ (z - 1) map_one' := by rw [sub_self, σ.map_zero, add_zero] map_mul' := fun z w => ext_of_chart h (by rw [RingHom.map_mul, a1, a1, a1, mul_one]) fun τ => by` and prove the remaining obligations.

Rewrite using `[RingHom.map_mul, RingHom.map_mul, a2, a2, a2, Pi.mul_apply] }, ?_, a1, a2⟩`. Conclude with `continuous_const.add (h.cont.comp (continuous_id.sub continuous_const))`.
-/
theorem exists_real_hom {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) :
    ∃ e : (D.what₂.Tau → ℂ) →* AE D, Continuous e ∧ (∀ z, finPart D (e z) = 1) ∧
      ∀ z τ, θ τ (infPart D (e z)) = z τ := by
  have a1 : ∀ z, finPart D (1 + σ (z - 1)) = 1 := fun z => by rw [RingHom.map_add, h.fin, add_zero, RingHom.map_one]
  have a2 : ∀ z τ, θ τ (infPart D (1 + σ (z - 1))) = z τ := fun z τ => by
    rw [RingHom.map_add, RingHom.map_add, h.comp, RingHom.map_one, RingHom.map_one]; simp
  refine ⟨{ toFun := fun z => 1 + σ (z - 1)
            map_one' := by rw [sub_self, σ.map_zero, add_zero]
            map_mul' := fun z w => ext_of_chart h (by rw [RingHom.map_mul, a1, a1, a1, mul_one]) fun τ => by
              rw [RingHom.map_mul, RingHom.map_mul, a2, a2, a2, Pi.mul_apply] }, ?_, a1, a2⟩
  exact continuous_const.add (h.cont.comp (continuous_id.sub continuous_const))

/- English proof (translation)
Take `⟨⟨η, hη⟩, h⟩` from `hχ`. Take `⟨-, -, hN, -⟩` from `GlobalTheory.VolHeckeCompare.exists_form D`. Establish `e : idF D (GlobalTheory.VolHeckeCompare.normU D y) = y * y`. Use `(hN y).trans (Units.ext ?_)` and prove the remaining obligations. Use `show (y : AE D) * cA D (y : AE D) = (y : AE D) * y`.

Rewrite using `[hy]`. Rewrite using `[← e, h η hη, hη.2.2.1 y, one_pow]`.
-/
theorem map_sq_eq_one {χ : (AE D)ˣ →* Circle} {n : ℕ} (hχ : ResEta D χ n) (y : (AE D)ˣ)
    (hy : cA D (y : AE D) = y) : χ (y * y) = 1 := by
  obtain ⟨⟨η, hη⟩, h⟩ := hχ
  obtain ⟨-, -, hN, -⟩ := GlobalTheory.VolHeckeCompare.exists_form D
  have e : idF D (GlobalTheory.VolHeckeCompare.normU D y) = y * y := by
    refine (hN y).trans (Units.ext ?_)
    show (y : AE D) * cA D (y : AE D) = (y : AE D) * y
    rw [hy]
  rw [← e, h η hη, hη.2.2.1 y, one_pow]

/- English proof (translation)
Introduce `D θ χ n τ hθ hχ hr`. Take `⟨σ, h⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`. Take `⟨e, ec, e1, e2⟩` from `exists_real_hom h`. Set `f : ℂ →* AE D` to `e.comp (MonoidHom.mulSingle (fun _ : D.what₂.Tau => ℂ) τ)`. Establish `fc : Continuous f` using `ec.comp (continuous_mulSingle (A := fun _ : D.what₂.Tau => ℂ) τ)`.

Establish `f1 : ∀ z, finPart D (f z) = 1` using `fun z => e1 _`. Establish `f2 : ∀ z τ', θ τ' (infPart D (f z)) = (Pi.mulSingle τ z : D.what₂.Tau → ℂ) τ'` using `fun z τ' => e2 _ τ'`. Take `⟨k, hk⟩` from `exists_zpow_of_trivial (χ.comp (Units.map f)) (hχ.1.comp (fc.units_map f)) fun s hs => by`. Rewrite using `[MonoidHom.comp_apply, MonoidHom.map_mul]`. Use `map_sq_eq_one hr _ (ext_of_chart h ?_ fun τ' => ?_)` and prove the remaining obligations.

Establish `e3 : finPart D (cA D (f s)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (f s))` using `GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (f s) show finPart D (cA D (f s)) = finPart D (f s)`. Rewrite using `[e3, f1, RingHom.map_one]`. Use `show θ τ' (infPart D (cA D (f s))) = θ τ' (infPart D (f s))`. Rewrite using `[GlobalTheory.FockCompare.comp_cA hθ, f2]`. Distinguish the cases in `ht : τ' = τ`.

Rewrite using `[ht, Pi.mulSingle_eq_same, hs]`. Rewrite using `[Pi.mulSingle_eq_of_ne ht, RingHom.map_one]`. Use `⟨(k : ℚ) / 2, k, by ring, ⟨θ, hθ⟩, fun θ' hθ' x x1 x2 => ?_⟩` and prove the remaining obligations. Take `rfl` from `GlobalTheory.VolHeckeCompare.infFam_unique hθ hθ'`. Set `z : ℂˣ` to `Units.map ((θ τ).comp (infPart D)).toMonoidHom x`.

Establish `hz : (z : ℂ) = θ τ (infPart D (x : AE D))` using `rfl`. Establish `ex : Units.map f z = x`. Use `Units.ext (ext_of_chart h ((f1 z).trans x1.symm) fun τ' => (f2 z τ').trans ?_)` and prove the remaining obligations. Distinguish the cases in `ht : τ' = τ`. Rewrite using `[ht, Pi.mulSingle_eq_same, hz]`.

Rewrite using `[Pi.mulSingle_eq_of_ne ht, x2 τ' ht]`. Use `hk z` as an intermediate fact. Rewrite `this` using `[MonoidHom.comp_apply, ex, hz]`. Then use the resulting hypothesis.
-/
theorem exists_hasInfExp : ∀ (D : D7) (θ : InfFam D) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau),
    IsInfFam θ → IsHeckeChar D χ → ResEta D χ n → ∃ a : ℚ, HasInfExp D χ τ a := by
  intro D θ χ n τ hθ hχ hr
  classical
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, ec, e1, e2⟩ := exists_real_hom h
  let f : ℂ →* AE D := e.comp (MonoidHom.mulSingle (fun _ : D.what₂.Tau => ℂ) τ)
  have fc : Continuous f := ec.comp (continuous_mulSingle (A := fun _ : D.what₂.Tau => ℂ) τ)
  have f1 : ∀ z, finPart D (f z) = 1 := fun z => e1 _
  have f2 : ∀ z τ', θ τ' (infPart D (f z)) = (Pi.mulSingle τ z : D.what₂.Tau → ℂ) τ' := fun z τ' => e2 _ τ'
  obtain ⟨k, hk⟩ := exists_zpow_of_trivial (χ.comp (Units.map f)) (hχ.1.comp (fc.units_map f)) fun s hs => by
    rw [MonoidHom.comp_apply, MonoidHom.map_mul]
    refine map_sq_eq_one hr _ (ext_of_chart h ?_ fun τ' => ?_)
    · have e3 : finPart D (cA D (f s)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (f s)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (f s)
      show finPart D (cA D (f s)) = finPart D (f s)
      rw [e3, f1, RingHom.map_one]
    · show θ τ' (infPart D (cA D (f s))) = θ τ' (infPart D (f s))
      rw [GlobalTheory.FockCompare.comp_cA hθ, f2]
      by_cases ht : τ' = τ
      · rw [ht, Pi.mulSingle_eq_same, hs]
      · rw [Pi.mulSingle_eq_of_ne ht, RingHom.map_one]
  refine ⟨(k : ℚ) / 2, k, by ring, ⟨θ, hθ⟩, fun θ' hθ' x x1 x2 => ?_⟩
  obtain rfl := GlobalTheory.VolHeckeCompare.infFam_unique hθ hθ'
  let z : ℂˣ := Units.map ((θ τ).comp (infPart D)).toMonoidHom x
  have hz : (z : ℂ) = θ τ (infPart D (x : AE D)) := rfl
  have ex : Units.map f z = x := by
    refine Units.ext (ext_of_chart h ((f1 z).trans x1.symm) fun τ' => (f2 z τ').trans ?_)
    by_cases ht : τ' = τ
    · rw [ht, Pi.mulSingle_eq_same, hz]
    · rw [Pi.mulSingle_eq_of_ne ht, x2 τ' ht]
  have := hk z
  rwa [MonoidHom.comp_apply, ex, hz] at this

end GlobalTheory.SplitCharExp

end
