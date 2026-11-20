import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesSubringEqGeneratorSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedTwoVariableSubringSubsetGeneratorSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobSdCongrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemPPSetCongrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteDividedPowerSeriesSubringPrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteDividedTwoVariableSubringStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittPowerSeriesMemDividedPowerSeriesGeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEisensteinMemPrimeMulDividedPowerSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorShiftFrobeniusMemDividedTwoVariableGeneratStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialMulCoeffMemDividedPowerSeriesSubringStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineEvalRingHomFrobeniusTaylorStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ sh φ₂ hsh hφC hφsh`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective`. Establish `hlp : l.Prime` using `Fact.out`. Establish `hlK : (l : K) ≠ 0` using `Nat.cast_ne_zero.2 hlp.ne_zero`. Establish `hl1 : (l : K⟦X⟧) ≠ 0` using `natCast_ne_zero_ps hlK`.

Establish `hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0` using `natCast_ne_zero_ps hl1`. Establish `tf1 : ∀ x : ZMod a → K⟦X⟧, (l : ZMod a → K⟦X⟧) * x = 0 → x = 0` using `tf_pi hl1`. Establish `tf2 : ∀ x : ZMod a → K⟦X⟧⟦X⟧, (l : ZMod a → K⟦X⟧⟦X⟧) * x = 0 → x = 0` using `tf_pi hl2`. Establish `tfS : ∀ x : ↥(Sd t K e), (l : ↥(Sd t K e)) * x = 0 → x = 0` using `tf_sub _ tf1`. Establish `tfP : ∀ x : ↥(PPd t K e), (l : ↥(PPd t K e)) * x = 0 → x = 0` using `tf_sub _ tf2`.

Use `haveI hcS := GlobalTheory.T.isAdicComplete_dividedPowerSeriesSubring_prime l a e O K t`. Use `haveI hcP := GlobalTheory.T.isAdicComplete_dividedTwoVariableSubring l a e O K t`. Establish `hSd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e` using `GlobalTheory.T.mem_sdSet_of_mem_sd l a e O K t`. Establish `hPd : ∀ F ∈ PPd t K e, F ∈ PPSet t K e` using `GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t`. Set `φS : ↥(Sd t K e) →+* ↥(Sd t K e)` to `(frobTot K a l).toRingHom.restrict (Sd t K e) (Sd t K e) fun F hF => Subring.subset_closure (GlobalTheory.T.frobTot_mem_SdSet_and_eq_pow_add_mul l a e O K t F (hSd F hF)).1`.

Establish `hφS : ∀ F : ↥(Sd t K e), ∃ B, φS F = F ^ l + (l : ↥(Sd t K e)) * B` using `fun F => by`. Take `⟨B, hB, h⟩` from `(GlobalTheory.T.frobTot_mem_SdSet_and_eq_pow_add_mul l a e O K t F (hSd F F.2)).2`. Conclude with `⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext h⟩`. Set `DS : Delta l ↥(Sd t K e)` to `Delta.ofLift l φS tfS hφS`. Set `φP : ↥(PPd t K e) →+* ↥(PPd t K e)` to `(frob2 φ₂).restrict (PPd t K e) (PPd t K e) fun F hF => Subring.subset_closure (GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul l a e O K t sh hsh φ₂ hφC hφsh F (hPd F hF)).1`.

Establish `hφP : ∀ F : ↥(PPd t K e), ∃ B, φP F = F ^ l + (l : ↥(PPd t K e)) * B` using `fun F => by`. Take `⟨B, hB, h⟩` from `(GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul l a e O K t sh hsh φ₂ hφC hφsh F (hPd F F.2)).2`. Conclude with `⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext h⟩`. Set `DP : Delta l ↥(PPd t K e)` to `Delta.ofLift l φP tfP hφP`. Set `i0 : (Wq l a)⟦X⟧ →+* ↥(Sd t K e)` to `((inclS t K).comp (frobS l a)).codRestrict (Sd t K e) fun x => Subring.subset_closure (GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet l a e O K t _)`.

Set `iP0 : (Wq l a)⟦X⟧ →+* ↥(PPd t K e)` to `((constP a K).comp ((inclS t K).comp (frobS l a))).codRestrict (PPd t K e) fun x => Subring.subset_closure (constP_mem t e (GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet l a e O K t _))`. Set `iP1 : (Wq l a)⟦X⟧ →+* ↥(PPd t K e)` to `((shP a sh).comp ((inclS t K).comp (frobS l a))).codRestrict (PPd t K e) fun x => Subring.subset_closure (GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet l a e O K t sh hsh x).1`. Set `dg : ↥(PPd t K e) →+* ↥(Sd t K e)` to `(diag a K).restrict (PPd t K e) (Sd t K e) fun F hF => Subring.subset_closure (diag_mem t e (hPd F hF))`. Establish `hdg0 : ∀ x, dg (iP0 x) = i0 x` using `fun x => Subtype.ext (funext fun τ => constantCoeff_C _)`. Take `⟨BE, hBE, hE⟩` from `GlobalTheory.T.frobenius_eisenstein_mem_prime_mul_dividedPowerSeries l a e O K t`.

Establish `hE0 : i0 (eis l a e) = (l : ↥(Sd t K e)) * ⟨BE, Subring.subset_closure hBE⟩` using `Subtype.ext hE`. Establish `hEP0 : iP0 (eis l a e) = (l : ↥(PPd t K e)) * ⟨constP a K BE, Subring.subset_closure (constP_mem t e hBE)⟩` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `constP a K (inclS t K (frobS l a (eis l a e))) = _`. Rewrite using `[hE, map_mul, map_natCast]`. Use the proof step `rfl)`.

Establish `hdiff : ∀ x, iP1 x - iP0 x ∈ Ideal.span {(l : ↥(PPd t K e))}` using `fun x => by`. Take `⟨B, hB, h⟩` from `(GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet l a e O K t sh hsh x).2`. Use `Ideal.mem_span_singleton'.2 ⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `B * (l : ZMod a → K⟦X⟧⟦X⟧) = _ - _`. Rewrite using `[mul_comm]`.

Conclude with `h.symm`. Establish `hmemS : ∀ x ∈ Ideal.span {eis l a e}, i0 x ∈ Ideal.span {(l : ↥(Sd t K e))}` using `fun x hx => by`. Take `⟨y, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Rewrite using `[map_mul, hE0]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))`.

Establish `hmemP0 : ∀ x ∈ Ideal.span {eis l a e}, iP0 x ∈ Ideal.span {(l : ↥(PPd t K e))}` using `fun x hx => by`. Take `⟨y, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Rewrite using `[map_mul, hEP0]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))`. Establish `hmemP1 : ∀ x ∈ Ideal.span {eis l a e}, iP1 x ∈ Ideal.span {(l : ↥(PPd t K e))}` using `fun x hx => by`.

Establish `h` using `Ideal.add_mem _ (hdiff x) (hmemP0 x hx)`. Rewrite `h` using `[sub_add_cancel]`. Then use the resulting hypothesis. Set `str0 : ↥(OL (ϖ.field a)) →+* ↥(Sd t K e) ⧸ Ideal.span {(l : ↥(Sd t K e))}` to `(Ideal.Quotient.lift (Ideal.span {eis l a e}) ((Ideal.Quotient.mk _).comp i0) fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (hmemS x hx)).comp (ϖ.strMap a)`. Set `strP : ↥(OL (ϖ.field a)) →+* ↥(PPd t K e) ⧸ Ideal.span {(l : ↥(PPd t K e))}` to `(Ideal.Quotient.lift (Ideal.span {eis l a e}) ((Ideal.Quotient.mk _).comp iP0) fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (hmemP0 x hx)).comp (ϖ.strMap a)`. Set `S₀ : Obj l ↥(OL (ϖ.field a))` to `Obj.ofDistinguished hlp.pos DS (l : ↥(Sd t K e)) (nzd_of_tf tfS) (isUnit_delta_l DS tfS) (by rw [sup_idem]; exact hcS) (bdd_self l) str0`.

Set `PP : Obj l ↥(OL (ϖ.field a))` to `Obj.ofDistinguished hlp.pos DP (l : ↥(PPd t K e)) (nzd_of_tf tfP) (isUnit_delta_l DP tfP) (by rw [sup_idem]; exact hcP) (bdd_self l) strP`. Establish `hlift : ∀ r : ↥(OL (ϖ.field a)), ∃ x : (Wq l a)⟦X⟧, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r` using `fun r => Ideal.Quotient.mk_surjective _`. Establish `hstrP : ∀ r x, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r → strP r = Ideal.Quotient.mk _ (iP0 x)` using `fun r x h => by simp only [strP, RingHom.comp_apply, ← h, Ideal.Quotient.lift_mk]`. Establish `hstr0 : ∀ r x, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r → str0 r = Ideal.Quotient.mk _ (i0 x)` using `fun r x h => by simp only [str0, RingHom.comp_apply, ← h, Ideal.Quotient.lift_mk]`. Set `p₀ : GlobalTheory.Prism.Hom (ϖ.prism a) PP` to `{ f := iP0 f_δ := (deltaS l a).map_δ_of_map_φ DP tfP iP0 fun x => Subtype.ext (funext fun τ => by`.

Express the relevant statement in the definitionally equal form `C (toAc t K (frobS l a (frobS l a x)) τ : K⟦X⟧) = φ₂ (C (toAc t K (frobS l a x) (τ - 1) : K⟦X⟧))`. Rewrite using `[hφC, frob_toAc])`. Use `f_I := hmemP0`. Use `f_str := fun r x h => (hstrP r x h).symm }`. Set `p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP` to `{ f := iP1 f_δ := (deltaS l a).map_δ_of_map_φ DP tfP iP1 fun x => Subtype.ext (funext fun τ => by`.

Express the relevant statement in the definitionally equal form `sh (toAc t K (frobS l a (frobS l a x)) τ : K⟦X⟧) = φ₂ (sh (toAc t K (frobS l a x) (τ - 1) : K⟦X⟧))`. Rewrite using `[hφsh, frob_toAc])`. Use `f_I := hmemP1`. Use `f_str := fun r x h => by`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) (iP1 x) = strP r`.

Rewrite using `[hstrP r x h, Ideal.Quotient.eq]`. Conclude with `hdiff x }`. Set `δ : GlobalTheory.Prism.Hom PP S₀` to `{ f := dg f_δ := DP.map_δ_of_map_φ DS tfS dg fun y => Subtype.ext (funext fun τ => by`. Express the relevant statement in the definitionally equal form `constantCoeff (φ₂ (y.1 (τ - 1))) = frob K l (constantCoeff (y.1 (τ - 1)))`. Conclude with `constantCoeff_φ₂ sh hsh l φ₂ hφC hφsh _)`.

Use `f_I := fun y hy => by`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Conclude with `(show ∀ c' : ↥(PPd t K e), dg (c' * (l : ↥(PPd t K e))) ∈ Ideal.span {(l : ↥(Sd t K e))} from fun c' => by rw [map_mul, map_natCast]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) c`. Use `f_str := fun r y h => by`. Take `⟨x, hx⟩` from `hlift r`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y = strP r at h`. Rewrite `h` using `[hstrP r x hx]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.span {(l : ↥(Sd t K e))}) (dg y) = str0 r`. Rewrite using `[hstr0 r x hx, ← hdg0]`. Conclude with `(show ∀ y' : ↥(PPd t K e), Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y' = Ideal.Quotient.mk _ (iP0 x) → Ideal.Quotient.mk (Ideal.span {(l : ↥(Sd t K e))}) (dg y') = Ideal.Quotient.mk _ (dg (iP0 x)) from fun y' h' => by`.

Rewrite `h'`, the goal using `[Ideal.Quotient.eq]`. Rewrite using `[← map_sub]`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 h'`. Rewrite using `[← hc, map_mul, map_natCast]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) y h }`.

Set `j : ZMod a → ↥(PPd t K e) →+* K⟦X⟧⟦X⟧` to `fun τ => (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧⟦X⟧) τ).comp (PPd t K e).subtype`. Set `j₀ : ZMod a → ↥(Sd t K e) →+* K⟦X⟧` to `fun τ => (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧) τ).comp (Sd t K e).subtype`. Establish `hS1 : ∀ τ (y : ↥(PPd t K e)) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (j τ y) ∈ S O K e` using `fun τ y i => GlobalTheory.T.factorial_mul_coeff_mem_dividedPowerSeriesSubring l a e O K t y.1 (hPd _ y.2) τ i`. Establish `hS : ∀ τ (y : ↥(PPd t K e)) (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (j τ y)) ∈ S O K e` using `fun τ y i => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ HasU.X_mem i) (hS1 τ y i)`. Use `⟨PP, S₀, p₀, p₁, δ, j, j₀, rfl, ?_, fun τ y => rfl, fun τ x => ⟨rfl, rfl⟩, fun τ y => rfl, hS, hS1, ?_⟩` and prove the remaining obligations.

Conclude with `Hom.ext' (RingHom.ext fun x => Subtype.ext (funext fun τ => by`. Express the relevant statement in the definitionally equal form `constantCoeff (C (toAc t K (frobS l a x) τ : K⟦X⟧)) = constantCoeff (sh (toAc t K (frobS l a x) τ : K⟦X⟧))`. Rewrite using `[constantCoeff_C, constantCoeff_sh sh hsh]))`. Introduce `Cr eC h hCI hCφ hh g`. Take `⟨E, hEa, hEb, hEc, hEd⟩` from `GlobalTheory.T.crystallineEval_ringHom_frobenius_taylor l a e O K t ϖ sh hsh φ₂ hφC hφsh g`.

Establish `tfC : ∀ x : Cr.A, (l : Cr.A) * x = 0 → x = 0` using `fun x hx => eC.injective (by`. Establish `h1` using `congrArg eC hx`. Rewrite `h1` using `[map_mul, map_natCast, map_zero]`. Rewrite using `[map_zero]`. Conclude with `acris_nat_cancel hlp.ne_zero h1)`.

Establish `hev0 : ∀ x, eC.symm (E (iP0 x)) = h.f ((ϖ.toAinf a).f x)` using `fun x => eC.injective (by`. Rewrite using `[RingEquiv.apply_symm_apply]`. Conclude with `(hEa x _).trans (hh _).symm)`. Set `ev : GlobalTheory.Prism.Hom PP Cr` to `{ f := eC.symm.toRingHom.comp E f_δ := DP.map_δ_of_map_φ Cr.D tfC _ fun y => eC.injective (by`. Express the relevant statement in the definitionally equal form `eC (eC.symm (E (φP y))) = eC (Cr.D.φ (eC.symm (E y)))`.

Rewrite using `[hCφ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`. Conclude with `hEc y.1 y.2 _)`. Use `f_I := fun y hy => by`. Rewrite using `[hCI]`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`.

Conclude with `(show ∀ c' : ↥(PPd t K e), eC.symm (E (c' * (l : ↥(PPd t K e)))) ∈ Ideal.span {(l : Cr.A)} from fun c' => by`. Rewrite using `[map_mul, map_mul, map_natCast, map_natCast]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) c`. Use `f_str := fun r y hy => by`. Take `⟨x, hx⟩` from `hlift r`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y = strP r at hy`. Rewrite `hy` using `[hstrP r x hx]`. Establish `h2` using `(h.comp (ϖ.toAinf a)).f_str r x hx`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk Cr.I (h.f ((ϖ.toAinf a).f x)) = Cr.str r at h2`. Rewrite using `[← h2, ← hev0]`.

Conclude with `(show ∀ y' : ↥(PPd t K e), Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y' = Ideal.Quotient.mk _ (iP0 x) → Ideal.Quotient.mk Cr.I (eC.symm (E y')) = Ideal.Quotient.mk Cr.I (eC.symm (E (iP0 x))) from fun y' h' => by`. Rewrite `h'`, the goal using `[Ideal.Quotient.eq]`. Rewrite using `[← map_sub, ← map_sub, hCI]`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 h'`. Rewrite using `[← hc, map_mul, map_mul, map_natCast, map_natCast]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) y hy }`. Use `⟨ev, Hom.ext' (RingHom.ext fun x => hev0 x), Hom.ext' (RingHom.ext fun x => eC.injective ?_), fun y r => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `eC (eC.symm (E (iP1 x))) = eC (h.f ((ainfHom (ϖ.field a) g).f ((ϖ.toAinf a).f x)))`. Rewrite using `[RingEquiv.apply_symm_apply]`. Conclude with `(hEb x _).trans (hh _).symm`.

Express the relevant statement in the definitionally equal form `∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] eC (eC.symm (E y)) - _`. Rewrite using `[RingEquiv.apply_symm_apply]`. Conclude with `hEd y.1 y.2 (hS · y) r`.
-/
theorem exists_crys_prisms : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∃ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (j₀ : ZMod a → S₀.A →+* K⟦X⟧), PP.I = Ideal.span {(l : PP.A)} ∧ δ.comp p₀ = δ.comp p₁ ∧ (∀ τ y, j₀ τ (δ.f y) = PowerSeries.constantCoeff (j τ y)) ∧ (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) ∧ (∀ τ y, j τ (PP.D.φ y) = φ₂ (j (τ - 1) y)) ∧ ∃ hS : ∀ τ y (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (j τ y)) ∈ S O K e, (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (j τ y) ∈ S O K e) ∧ ∀ (Cr : Obj l ↥(OL (ϖ.field a))) (eC : Cr.A ≃+* Per.Acris l) (h : GlobalTheory.Prism.Hom (ainfObj (ϖ.field a)) Cr), Cr.I = Ideal.span {(l : Cr.A)} → (∀ x, eC (Cr.D.φ x) = frobC l (eC x)) → (∀ x : Ainf l, eC (h.f x) = ainfToAcris l (WittVector.frobenius x)) → ∀ g : ↥(GK (ϖ.field a)), ∃ ev : GlobalTheory.Prism.Hom PP Cr, ev.comp p₀ = h.comp (ϖ.toAinf a) ∧ ev.comp p₁ = (h.comp (ainfHom (ϖ.field a) g)).comp (ϖ.toAinf a) ∧ ∀ (y : PP.A) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] eC (ev.f y) - ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K fun τ => ⟨_, hS τ y i⟩ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ sh φ₂ hsh hφC hφsh
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hlp : l.Prime := Fact.out
  have hlK : (l : K) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hl1 : (l : K⟦X⟧) ≠ 0 := natCast_ne_zero_ps hlK
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := natCast_ne_zero_ps hl1
  have tf1 : ∀ x : ZMod a → K⟦X⟧, (l : ZMod a → K⟦X⟧) * x = 0 → x = 0 := tf_pi hl1
  have tf2 : ∀ x : ZMod a → K⟦X⟧⟦X⟧, (l : ZMod a → K⟦X⟧⟦X⟧) * x = 0 → x = 0 := tf_pi hl2
  have tfS : ∀ x : ↥(Sd t K e), (l : ↥(Sd t K e)) * x = 0 → x = 0 := tf_sub _ tf1
  have tfP : ∀ x : ↥(PPd t K e), (l : ↥(PPd t K e)) * x = 0 → x = 0 := tf_sub _ tf2
  haveI hcS := GlobalTheory.T.isAdicComplete_dividedPowerSeriesSubring_prime l a e O K t
  haveI hcP := GlobalTheory.T.isAdicComplete_dividedTwoVariableSubring l a e O K t
  have hSd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e := GlobalTheory.T.mem_sdSet_of_mem_sd l a e O K t
  have hPd : ∀ F ∈ PPd t K e, F ∈ PPSet t K e := GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t

  let φS : ↥(Sd t K e) →+* ↥(Sd t K e) := (frobTot K a l).toRingHom.restrict (Sd t K e) (Sd t K e)
    fun F hF => Subring.subset_closure (GlobalTheory.T.frobTot_mem_SdSet_and_eq_pow_add_mul l a e O K t F (hSd F hF)).1
  have hφS : ∀ F : ↥(Sd t K e), ∃ B, φS F = F ^ l + (l : ↥(Sd t K e)) * B := fun F => by
    obtain ⟨B, hB, h⟩ := (GlobalTheory.T.frobTot_mem_SdSet_and_eq_pow_add_mul l a e O K t F (hSd F F.2)).2
    exact ⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext h⟩
  let DS : Delta l ↥(Sd t K e) := Delta.ofLift l φS tfS hφS
  let φP : ↥(PPd t K e) →+* ↥(PPd t K e) := (frob2 φ₂).restrict (PPd t K e) (PPd t K e)
    fun F hF => Subring.subset_closure (GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul l a e O K t sh hsh φ₂ hφC hφsh F (hPd F hF)).1
  have hφP : ∀ F : ↥(PPd t K e), ∃ B, φP F = F ^ l + (l : ↥(PPd t K e)) * B := fun F => by
    obtain ⟨B, hB, h⟩ := (GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul l a e O K t sh hsh φ₂ hφC hφsh F (hPd F F.2)).2
    exact ⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext h⟩
  let DP : Delta l ↥(PPd t K e) := Delta.ofLift l φP tfP hφP

  let i0 : (Wq l a)⟦X⟧ →+* ↥(Sd t K e) := ((inclS t K).comp (frobS l a)).codRestrict (Sd t K e)
    fun x => Subring.subset_closure (GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet l a e O K t _)
  let iP0 : (Wq l a)⟦X⟧ →+* ↥(PPd t K e) := ((constP a K).comp ((inclS t K).comp (frobS l a))).codRestrict
    (PPd t K e) fun x => Subring.subset_closure (constP_mem t e (GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet l a e O K t _))
  let iP1 : (Wq l a)⟦X⟧ →+* ↥(PPd t K e) := ((shP a sh).comp ((inclS t K).comp (frobS l a))).codRestrict
    (PPd t K e) fun x => Subring.subset_closure (GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet l a e O K t sh hsh x).1
  let dg : ↥(PPd t K e) →+* ↥(Sd t K e) := (diag a K).restrict (PPd t K e) (Sd t K e)
    fun F hF => Subring.subset_closure (diag_mem t e (hPd F hF))
  have hdg0 : ∀ x, dg (iP0 x) = i0 x := fun x => Subtype.ext (funext fun τ => constantCoeff_C _)
  obtain ⟨BE, hBE, hE⟩ := GlobalTheory.T.frobenius_eisenstein_mem_prime_mul_dividedPowerSeries l a e O K t
  have hE0 : i0 (eis l a e) = (l : ↥(Sd t K e)) * ⟨BE, Subring.subset_closure hBE⟩ := Subtype.ext hE
  have hEP0 : iP0 (eis l a e) = (l : ↥(PPd t K e)) * ⟨constP a K BE, Subring.subset_closure (constP_mem t e hBE)⟩ :=
    Subtype.ext (by
      change constP a K (inclS t K (frobS l a (eis l a e))) = _
      rw [hE, map_mul, map_natCast]; rfl)
  have hdiff : ∀ x, iP1 x - iP0 x ∈ Ideal.span {(l : ↥(PPd t K e))} := fun x => by
    obtain ⟨B, hB, h⟩ := (GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet l a e O K t sh hsh x).2
    refine Ideal.mem_span_singleton'.2 ⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext ?_⟩
    change B * (l : ZMod a → K⟦X⟧⟦X⟧) = _ - _
    rw [mul_comm]; exact h.symm
  have hmemS : ∀ x ∈ Ideal.span {eis l a e}, i0 x ∈ Ideal.span {(l : ↥(Sd t K e))} := fun x hx => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, hE0]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hmemP0 : ∀ x ∈ Ideal.span {eis l a e}, iP0 x ∈ Ideal.span {(l : ↥(PPd t K e))} := fun x hx => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, hEP0]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hmemP1 : ∀ x ∈ Ideal.span {eis l a e}, iP1 x ∈ Ideal.span {(l : ↥(PPd t K e))} := fun x hx => by
    have h := Ideal.add_mem _ (hdiff x) (hmemP0 x hx)
    rwa [sub_add_cancel] at h

  let str0 : ↥(OL (ϖ.field a)) →+* ↥(Sd t K e) ⧸ Ideal.span {(l : ↥(Sd t K e))} :=
    (Ideal.Quotient.lift (Ideal.span {eis l a e}) ((Ideal.Quotient.mk _).comp i0)
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (hmemS x hx)).comp (ϖ.strMap a)
  let strP : ↥(OL (ϖ.field a)) →+* ↥(PPd t K e) ⧸ Ideal.span {(l : ↥(PPd t K e))} :=
    (Ideal.Quotient.lift (Ideal.span {eis l a e}) ((Ideal.Quotient.mk _).comp iP0)
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (hmemP0 x hx)).comp (ϖ.strMap a)
  let S₀ : Obj l ↥(OL (ϖ.field a)) := Obj.ofDistinguished hlp.pos DS (l : ↥(Sd t K e)) (nzd_of_tf tfS)
    (isUnit_delta_l DS tfS) (by rw [sup_idem]; exact hcS) (bdd_self l) str0
  let PP : Obj l ↥(OL (ϖ.field a)) := Obj.ofDistinguished hlp.pos DP (l : ↥(PPd t K e)) (nzd_of_tf tfP)
    (isUnit_delta_l DP tfP) (by rw [sup_idem]; exact hcP) (bdd_self l) strP

  have hlift : ∀ r : ↥(OL (ϖ.field a)), ∃ x : (Wq l a)⟦X⟧, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r :=
    fun r => Ideal.Quotient.mk_surjective _
  have hstrP : ∀ r x, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r → strP r = Ideal.Quotient.mk _ (iP0 x) :=
    fun r x h => by simp only [strP, RingHom.comp_apply, ← h, Ideal.Quotient.lift_mk]
  have hstr0 : ∀ r x, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r → str0 r = Ideal.Quotient.mk _ (i0 x) :=
    fun r x h => by simp only [str0, RingHom.comp_apply, ← h, Ideal.Quotient.lift_mk]

  let p₀ : GlobalTheory.Prism.Hom (ϖ.prism a) PP :=
    { f := iP0
      f_δ := (deltaS l a).map_δ_of_map_φ DP tfP iP0 fun x => Subtype.ext (funext fun τ => by
        change C (toAc t K (frobS l a (frobS l a x)) τ : K⟦X⟧) = φ₂ (C (toAc t K (frobS l a x) (τ - 1) : K⟦X⟧))
        rw [hφC, frob_toAc])
      f_I := hmemP0
      f_str := fun r x h => (hstrP r x h).symm }
  let p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP :=
    { f := iP1
      f_δ := (deltaS l a).map_δ_of_map_φ DP tfP iP1 fun x => Subtype.ext (funext fun τ => by
        change sh (toAc t K (frobS l a (frobS l a x)) τ : K⟦X⟧) = φ₂ (sh (toAc t K (frobS l a x) (τ - 1) : K⟦X⟧))
        rw [hφsh, frob_toAc])
      f_I := hmemP1
      f_str := fun r x h => by
        change Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) (iP1 x) = strP r
        rw [hstrP r x h, Ideal.Quotient.eq]
        exact hdiff x }
  let δ : GlobalTheory.Prism.Hom PP S₀ :=
    { f := dg
      f_δ := DP.map_δ_of_map_φ DS tfS dg fun y => Subtype.ext (funext fun τ => by
        change constantCoeff (φ₂ (y.1 (τ - 1))) = frob K l (constantCoeff (y.1 (τ - 1)))
        exact constantCoeff_φ₂ sh hsh l φ₂ hφC hφsh _)
      f_I := fun y hy => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
        exact (show ∀ c' : ↥(PPd t K e), dg (c' * (l : ↥(PPd t K e))) ∈ Ideal.span {(l : ↥(Sd t K e))} from
          fun c' => by rw [map_mul, map_natCast]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) c
      f_str := fun r y h => by
        obtain ⟨x, hx⟩ := hlift r
        change Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y = strP r at h
        rw [hstrP r x hx] at h
        change Ideal.Quotient.mk (Ideal.span {(l : ↥(Sd t K e))}) (dg y) = str0 r
        rw [hstr0 r x hx, ← hdg0]
        exact (show ∀ y' : ↥(PPd t K e), Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y' =
            Ideal.Quotient.mk _ (iP0 x) → Ideal.Quotient.mk (Ideal.span {(l : ↥(Sd t K e))}) (dg y') =
            Ideal.Quotient.mk _ (dg (iP0 x)) from fun y' h' => by
          rw [Ideal.Quotient.eq] at h' ⊢
          rw [← map_sub]
          obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h'
          rw [← hc, map_mul, map_natCast]
          exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) y h }
  let j : ZMod a → ↥(PPd t K e) →+* K⟦X⟧⟦X⟧ := fun τ =>
    (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧⟦X⟧) τ).comp (PPd t K e).subtype
  let j₀ : ZMod a → ↥(Sd t K e) →+* K⟦X⟧ := fun τ =>
    (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧) τ).comp (Sd t K e).subtype
  have hS1 : ∀ τ (y : ↥(PPd t K e)) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (j τ y) ∈ S O K e :=
    fun τ y i => GlobalTheory.T.factorial_mul_coeff_mem_dividedPowerSeriesSubring l a e O K t y.1 (hPd _ y.2) τ i
  have hS : ∀ τ (y : ↥(PPd t K e)) (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (j τ y)) ∈ S O K e :=
    fun τ y i => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ HasU.X_mem i) (hS1 τ y i)
  refine ⟨PP, S₀, p₀, p₁, δ, j, j₀, rfl, ?_, fun τ y => rfl, fun τ x => ⟨rfl, rfl⟩, fun τ y => rfl, hS, hS1, ?_⟩
  · exact Hom.ext' (RingHom.ext fun x => Subtype.ext (funext fun τ => by
      change constantCoeff (C (toAc t K (frobS l a x) τ : K⟦X⟧)) = constantCoeff (sh (toAc t K (frobS l a x) τ : K⟦X⟧))
      rw [constantCoeff_C, constantCoeff_sh sh hsh]))
  · intro Cr eC h hCI hCφ hh g
    obtain ⟨E, hEa, hEb, hEc, hEd⟩ := GlobalTheory.T.crystallineEval_ringHom_frobenius_taylor l a e O K t ϖ sh hsh φ₂ hφC hφsh g
    have tfC : ∀ x : Cr.A, (l : Cr.A) * x = 0 → x = 0 := fun x hx => eC.injective (by
      have h1 := congrArg eC hx
      rw [map_mul, map_natCast, map_zero] at h1
      rw [map_zero]; exact acris_nat_cancel hlp.ne_zero h1)
    have hev0 : ∀ x, eC.symm (E (iP0 x)) = h.f ((ϖ.toAinf a).f x) := fun x => eC.injective (by
      rw [RingEquiv.apply_symm_apply]; exact (hEa x _).trans (hh _).symm)
    let ev : GlobalTheory.Prism.Hom PP Cr :=
      { f := eC.symm.toRingHom.comp E
        f_δ := DP.map_δ_of_map_φ Cr.D tfC _ fun y => eC.injective (by
          change eC (eC.symm (E (φP y))) = eC (Cr.D.φ (eC.symm (E y)))
          rw [hCφ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
          exact hEc y.1 y.2 _)
        f_I := fun y hy => by
          rw [hCI]
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
          exact (show ∀ c' : ↥(PPd t K e), eC.symm (E (c' * (l : ↥(PPd t K e)))) ∈ Ideal.span {(l : Cr.A)} from
            fun c' => by
              rw [map_mul, map_mul, map_natCast, map_natCast]
              exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) c
        f_str := fun r y hy => by
          obtain ⟨x, hx⟩ := hlift r
          change Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y = strP r at hy
          rw [hstrP r x hx] at hy
          have h2 := (h.comp (ϖ.toAinf a)).f_str r x hx
          change Ideal.Quotient.mk Cr.I (h.f ((ϖ.toAinf a).f x)) = Cr.str r at h2
          rw [← h2, ← hev0]
          exact (show ∀ y' : ↥(PPd t K e), Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y' =
              Ideal.Quotient.mk _ (iP0 x) → Ideal.Quotient.mk Cr.I (eC.symm (E y')) =
              Ideal.Quotient.mk Cr.I (eC.symm (E (iP0 x))) from fun y' h' => by
            rw [Ideal.Quotient.eq] at h' ⊢
            rw [← map_sub, ← map_sub, hCI]
            obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h'
            rw [← hc, map_mul, map_mul, map_natCast, map_natCast]
            exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) y hy }
    refine ⟨ev, Hom.ext' (RingHom.ext fun x => hev0 x), Hom.ext' (RingHom.ext fun x => eC.injective ?_), fun y r => ?_⟩
    · change eC (eC.symm (E (iP1 x))) = eC (h.f ((ainfHom (ϖ.field a) g).f ((ϖ.toAinf a).f x)))
      rw [RingEquiv.apply_symm_apply]
      exact (hEb x _).trans (hh _).symm
    · change ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] eC (eC.symm (E y)) - _
      rw [RingEquiv.apply_symm_apply]
      exact hEd y.1 y.2 (hS · y) r

end GlobalTheory.CrysPrism
