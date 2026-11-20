import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.ChainOnto

/- English proof (translation)
Take the linear combination `(A - 1) * (B - 1) * he + e * hAB`.
-/
theorem one_add_idem_mul {R : Type} [CommRing R] {e A B : R} (he : e * e = e) (hAB : A * B = 1) :
    (1 + e * (A - 1)) * (1 + e * (B - 1)) = 1 := by
  linear_combination (A - 1) * (B - 1) * he + e * hAB

/- English proof (translation)
Expand and normalize the polynomial expressions, which then agree.
-/
theorem one_add_idem_mul_eq {R : Type} [CommRing R] (e A : R) : 1 + e * (A - 1) = e * A + (1 - e) := by ring

/- English proof (translation)
Establish `h3 : incA D z * incA D z⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel₀ hz, map_one]`. Conclude with `one_add_idem_mul he h3`.
-/
theorem locE_mul_inv (D : D7) {e : AE D} (he : e * e = e) {z : D.host.E} (hz : z ≠ 0) :
    Formalism.L2.JoinChr.locE D e z * Formalism.L2.JoinChr.locE D e z⁻¹ = 1 := by
  have h3 : incA D z * incA D z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  exact one_add_idem_mul he h3

/- English proof (translation)
The claim follows from `one_add_idem_mul_eq _ _`.
-/
theorem locE_eq (D : D7) (e : AE D) (z : D.host.E) : Formalism.L2.JoinChr.locE D e z = e * incA D z + (1 - e) :=
  one_add_idem_mul_eq _ _

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV in
set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D k _ _ _ _ q PP hI π' hπ hR c hc hP j hj1 hj2 μ hμ hC`. Introduce `s u x hu hx`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)`. Establish `hoa : ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = toEAf D (incA D (a : D.host.E))` using `rfl`. Establish `hψa : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E a) = q.pr (incA D (a : D.host.E))`.

Rewrite using `[RingHom.comp_apply, Subring.coe_subtype, hoa, hπ]`. Establish `hres : Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E a) = u`. Rewrite using `[Formalism.L2.DIV.resS_oToS, ha]`. Establish `h1 : valuation k (q.pr (incA D (a : D.host.E))) = 1`. Rewrite using `[← hψa, ← hR.isUnit_iff, hres]`.

Conclude with `u.isUnit`. Establish `h2 : valuation k ((x : k) - q.pr (incA D (a : D.host.E))) < 1`. Rewrite using `[← hψa, hx, ← map_sub]`. Use `(hR.ker _).1 ?_` and prove the remaining obligations. Rewrite using `[map_sub, hres, ← hu, sub_self]`.

Establish `hp0 : q.pr (incA D (a : D.host.E)) ≠ 0` using `fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1`. Establish `hμx : μ x = μ (Units.mk0 _ hp0)`. Establish `: μ (x * (Units.mk0 _ hp0)⁻¹) = 1` using `hμ _ (by`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_inv_cancel₀ hp0, ← sub_mul, map_mul, map_inv₀, h1, inv_one, mul_one]`. Conclude with `h2)`.

Rewrite `this` using `[map_mul, map_inv, mul_inv_eq_one]`. Conclude with `this`. Establish `ha0 : (a : D.host.E) ≠ 0` using `fun h => by rw [h, map_zero, map_zero] at h1; exact zero_ne_one h1`. Establish `hee : q.e * q.e = q.e` using `hI.1.1`. Set `y : (AE D)ˣ` to `⟨Formalism.L2.JoinChr.locE D q.e (a : D.host.E), Formalism.L2.JoinChr.locE D q.e (a : D.host.E)⁻¹, GlobalTheory.ChainOnto.locE_mul_inv D hee ha0, by rw [mul_comm]; exact GlobalTheory.ChainOnto.locE_mul_inv D hee ha0⟩`.

Establish `hyι : (y : AE D) = (ofSplit q).ι ((Units.mk0 _ hp0 : kˣ) : k) + (1 - (ofSplit q).e)` using `by show Formalism.L2.JoinChr.locE D q.e (a : D.host.E) = q.sec (q.pr (incA D (a : D.host.E))) + (1 - q.e)`. Rewrite using `[q.sec_pr, GlobalTheory.ChainOnto.locE_eq]`. Establish `hcomp` using `hC _ y hyι`. Establish `hinf : infPart D q.e = 0` using `(GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) hI).1`. Establish `hint : ∀ z : D.host.E, valuation k (q.pr (incA D z)) = 1 → finPart D (Formalism.L2.JoinChr.locE D q.e z) ∈ intAE D`.

Introduce `z hz`. Rewrite using `[GlobalTheory.ChainOnto.locE_eq, ← q.sec_pr, (finPart D).map_add, (finPart D).map_sub, (finPart D).map_one]`. Use `add_mem ((q.int_iff _).1 ?_) (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1)) (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, hee])))` and prove the remaining obligations. Conclude with `(Valuation.mem_integer_iff _ _).2 hz.le`. Establish `hinv : q.pr (incA D (a : D.host.E)⁻¹) = (q.pr (incA D (a : D.host.E)))⁻¹` using `map_inv₀ (q.pr.comp (incA D)) _`.

Establish `hη : c.η y = 1` using `hc.chars.2.1 y (by show infPart D (Formalism.L2.JoinChr.locE D q.e (a : D.host.E)) = 1`. Rewrite using `[GlobalTheory.ChainOnto.locE_eq, (infPart D).map_add, (infPart D).map_mul, (infPart D).map_sub, (infPart D).map_one, hinf, zero_mul, zero_add, sub_zero])`. Use the proof step `(hint _ h1) (hint _ (by rw [hinv, map_inv₀, h1, inv_one]))`. Establish `hS : c.chS j y = c.μ j y`. Unfold `GlobalTheory.ChainOnto.Com.chS Formalism.IndefR.Lift.chrStep`.

Apply the tactic sequence `split_ifs <;> simp [hη]`. Take `⟨H, hH1, hH2⟩` from `hc.res ⟨j - 1, by omega⟩`. Establish `hj : j - 1 + 1 = j` using `Nat.sub_add_cancel hj1`. Simplify using `only at hH1 hH2`. Rewrite `hH1`, `hH2` using `[hj]`.

Establish `hIP : Formalism.L2.JoinChr.IsPlIdem D q.e PP`. Take `⟨h1', h2', v, ε, h3', h4'⟩` from `hI.1`. Conclude with `⟨h1', ⟨v, ε, h3', Or.inl ⟨h2', h4'⟩⟩, hI.2⟩`. Establish `e1` using `hH1.2 PP q.e hIP (Units.mk0 _ ha0) y rfl`. Establish `e2` using `hH2 PP hP a (Units.mk0 _ ha0) u rfl ha.symm`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hμx, hcomp, MonoidHom.inv_apply, Circle.coe_inv, hS, e1, ← e2, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]`.
-/
theorem chi_compat_of_isComp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ π' : EAf D →+* k, (∀ a, π' (toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ c : GlobalTheory.ChainOnto.Com D, c.Is → PP ∈ c.Pg → ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ μ : kˣ →* ℂˣ, IsTame μ → (ofSplit q).IsComp (c.chS j)⁻¹ μ → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (c.chi j PP) μ := by
  intro D k _ _ _ _ q PP hI π' hπ hR c hc hP j hj1 hj2 μ hμ hC
  intro s u x hu hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)
  have hoa : ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (incA D (a : D.host.E)) := rfl
  have hψa : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E a) =
      q.pr (incA D (a : D.host.E)) := by
    rw [RingHom.comp_apply, Subring.coe_subtype, hoa, hπ]
  have hres : Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E a) = u := by
    rw [Formalism.L2.DIV.resS_oToS, ha]
  have h1 : valuation k (q.pr (incA D (a : D.host.E))) = 1 := by
    rw [← hψa, ← hR.isUnit_iff, hres]; exact u.isUnit
  have h2 : valuation k ((x : k) - q.pr (incA D (a : D.host.E))) < 1 := by
    rw [← hψa, hx, ← map_sub]
    refine (hR.ker _).1 ?_
    rw [map_sub, hres, ← hu, sub_self]
  have hp0 : q.pr (incA D (a : D.host.E)) ≠ 0 := fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1
  have hμx : μ x = μ (Units.mk0 _ hp0) := by
    have : μ (x * (Units.mk0 _ hp0)⁻¹) = 1 := hμ _ (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_inv_cancel₀ hp0, ← sub_mul, map_mul, map_inv₀, h1,
        inv_one, mul_one]
      exact h2)
    rw [map_mul, map_inv, mul_inv_eq_one] at this; exact this
  have ha0 : (a : D.host.E) ≠ 0 := fun h => by rw [h, map_zero, map_zero] at h1; exact zero_ne_one h1
  have hee : q.e * q.e = q.e := hI.1.1
  let y : (AE D)ˣ := ⟨Formalism.L2.JoinChr.locE D q.e (a : D.host.E), Formalism.L2.JoinChr.locE D q.e (a : D.host.E)⁻¹,
    GlobalTheory.ChainOnto.locE_mul_inv D hee ha0, by rw [mul_comm]; exact GlobalTheory.ChainOnto.locE_mul_inv D hee ha0⟩
  have hyι : (y : AE D) = (ofSplit q).ι ((Units.mk0 _ hp0 : kˣ) : k) + (1 - (ofSplit q).e) := by
    show Formalism.L2.JoinChr.locE D q.e (a : D.host.E) = q.sec (q.pr (incA D (a : D.host.E))) + (1 - q.e)
    rw [q.sec_pr, GlobalTheory.ChainOnto.locE_eq]
  have hcomp := hC _ y hyι
  have hinf : infPart D q.e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) hI).1
  have hint : ∀ z : D.host.E, valuation k (q.pr (incA D z)) = 1 →
      finPart D (Formalism.L2.JoinChr.locE D q.e z) ∈ intAE D := by
    intro z hz
    rw [GlobalTheory.ChainOnto.locE_eq, ← q.sec_pr, (finPart D).map_add, (finPart D).map_sub, (finPart D).map_one]
    refine add_mem ((q.int_iff _).1 ?_) (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1))
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, hee])))
    exact (Valuation.mem_integer_iff _ _).2 hz.le
  have hinv : q.pr (incA D (a : D.host.E)⁻¹) = (q.pr (incA D (a : D.host.E)))⁻¹ := map_inv₀ (q.pr.comp (incA D)) _
  have hη : c.η y = 1 := hc.chars.2.1 y (by
      show infPart D (Formalism.L2.JoinChr.locE D q.e (a : D.host.E)) = 1
      rw [GlobalTheory.ChainOnto.locE_eq, (infPart D).map_add, (infPart D).map_mul, (infPart D).map_sub, (infPart D).map_one, hinf,
        zero_mul, zero_add, sub_zero])
    (hint _ h1) (hint _ (by rw [hinv, map_inv₀, h1, inv_one]))
  have hS : c.chS j y = c.μ j y := by
    unfold GlobalTheory.ChainOnto.Com.chS Formalism.IndefR.Lift.chrStep
    split_ifs <;> simp [hη]
  obtain ⟨H, hH1, hH2⟩ := hc.res ⟨j - 1, by omega⟩
  have hj : j - 1 + 1 = j := Nat.sub_add_cancel hj1
  dsimp only at hH1 hH2
  rw [hj] at hH1 hH2
  have hIP : Formalism.L2.JoinChr.IsPlIdem D q.e PP := by
    obtain ⟨h1', h2', v, ε, h3', h4'⟩ := hI.1
    exact ⟨h1', ⟨v, ε, h3', Or.inl ⟨h2', h4'⟩⟩, hI.2⟩
  have e1 := hH1.2 PP q.e hIP (Units.mk0 _ ha0) y rfl
  have e2 := hH2 PP hP a (Units.mk0 _ ha0) u rfl ha.symm
  apply Units.ext
  rw [hμx, hcomp, MonoidHom.inv_apply, Circle.coe_inv, hS, e1, ← e2, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]

end GlobalTheory.ChainOnto

end
