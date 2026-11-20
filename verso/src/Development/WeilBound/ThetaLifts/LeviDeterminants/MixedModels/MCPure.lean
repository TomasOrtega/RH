import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PureSt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdeleCongruenceUnitCriterion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsNhdsInvariant
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissible

noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.KCo

variable {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ]

/- English proof (translation)
Establish `hl` using `GlobalTheory.CompanionTheory.AdelicHeis.isLocallyConstant_fin (ψ.compAddMonoidHom (AddMonoidHom.inr (Ainf F) (Af F))) (hψ.1.comp (continuous_const.prodMk continuous_id)) fun x => GlobalTheory.StdCharFromIsStd.norm_psi hψ _`. Take `⟨M, hM, h⟩` from `GlobalTheory.IdeleCharLevel.exists_level F _ ((hl.isOpen_fiber 1).mem_nhds (AddChar.map_zero_eq_one _))`. Establish `h0 : Ideal.span {(M : 𝓞 F)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `Nat.cast_ne_zero.2 hM`.

Use `⟨(Ideal.finite_factors h0).toFinset, fun b h1 h2 => h b fun v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ (Ideal.finite_factors h0).toFinset`. Establish `: b v = 0` using `h1 v hv`. Rewrite using `[this, map_zero]`. Conclude with `zero_le'`.

Establish `e : v.intValuation (M : 𝓞 F) = 1`. Assume the negation of the conclusion as `e`. Conclude with `hv ((Set.Finite.mem_toFinset _).2 ((v.intValuation_lt_one_iff_dvd _).1 (lt_of_le_of_ne (v.intValuation_le_one (M : 𝓞 F)) e)))`. Rewrite using `[e]`. Conclude with `h2 v`.
-/
theorem exists_triv (hψ : IsStd ψ) : ∃ T : Finset (Pl F), ∀ b : Af F,
    (∀ v ∈ T, evalV F v b = 0) → (∀ v, evalV F v b ∈ v.adicCompletionIntegers F) → ψ ((0 : Ainf F), b) = 1 := by
  have hl := GlobalTheory.CompanionTheory.AdelicHeis.isLocallyConstant_fin (ψ.compAddMonoidHom (AddMonoidHom.inr (Ainf F) (Af F)))
    (hψ.1.comp (continuous_const.prodMk continuous_id)) fun x => GlobalTheory.StdCharFromIsStd.norm_psi hψ _
  obtain ⟨M, hM, h⟩ := GlobalTheory.IdeleCharLevel.exists_level F _ ((hl.isOpen_fiber 1).mem_nhds (AddChar.map_zero_eq_one _))
  have h0 : Ideal.span {(M : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.2 hM
  refine ⟨(Ideal.finite_factors h0).toFinset, fun b h1 h2 => h b fun v => ?_⟩
  by_cases hv : v ∈ (Ideal.finite_factors h0).toFinset
  · have : b v = 0 := h1 v hv
    rw [this, map_zero]; exact zero_le'
  · have e : v.intValuation (M : 𝓞 F) = 1 := by
      by_contra e
      exact hv ((Set.Finite.mem_toFinset _).2
        ((v.intValuation_lt_one_iff_dvd _).1 (lt_of_le_of_ne (v.intValuation_le_one (M : 𝓞 F)) e)))
    rw [e]; exact h2 v

/- English proof (translation)
Take `⟨T, hT⟩` from `exists_triv hψ`. Use `filter_upwards [T.eventually_cofinite_notMem] with v hv y hy`. Use `hT (singleFin v y) (fun u hu => evalV_singleFin_ne (fun e : u = v => hv (e ▸ hu)) y) fun u => ?_` and prove the remaining obligations. Break down `eq_or_ne u v with rfl | e` into its components or cases. Rewrite using `[evalV_singleFin_self]` and apply the resulting hypothesis.

Rewrite using `[evalV_singleFin_ne e]`. Conclude with `zero_mem _`.
-/
theorem psiV_int (hψ : IsStd ψ) : ∀ᶠ v : Pl F in cofinite, ∀ y ∈ v.adicCompletionIntegers F, psiV ψ v y = 1 := by
  obtain ⟨T, hT⟩ := exists_triv hψ
  filter_upwards [T.eventually_cofinite_notMem] with v hv y hy
  refine hT (singleFin v y) (fun u hu => evalV_singleFin_ne (fun e : u = v => hv (e ▸ hu)) y) fun u => ?_
  rcases eq_or_ne u v with rfl | e
  · rwa [evalV_singleFin_self]
  · rw [evalV_singleFin_ne e]; exact zero_mem _

/- English proof (translation)
Use `filter_upwards [psiV_int hψ, (a.2.2 : ∀ᶠ v : Pl F in cofinite, evFin F v a ∈ v.adicCompletionIntegers F)] with v h1 h2`. Conclude with `h1 _ h2`.
-/
theorem psiV_ev (hψ : IsStd ψ) (a : AF F) : ∀ᶠ v : Pl F in cofinite, psiV ψ v (evFin F v a) = 1 := by
  filter_upwards [psiV_int hψ, (a.2.2 : ∀ᶠ v : Pl F in cofinite, evFin F v a ∈ v.adicCompletionIntegers F)] with v h1 h2
  exact h1 _ h2

/- English proof (translation)
Take `⟨T, hT⟩` from `exists_triv hψ`. Establish `hfin : {v : Pl F | ¬ (v ∉ T ∧ psiV ψ v (evFin F v a) = 1 ∧ evFin F v a ∈ v.adicCompletionIntegers F)}.Finite` using `eventually_cofinite.1 (T.eventually_cofinite_notMem.and ((psiV_ev hψ a).and a.2.2))`. Use `set U := hfin.toFinset`. Establish `hU : ∀ v ∉ U, v ∉ T ∧ psiV ψ v (evFin F v a) = 1 ∧ evFin F v a ∈ v.adicCompletionIntegers F` using `fun v hv => not_not.1 fun e => hv (hfin.mem_toFinset.2 e)`. Set `s : Af F` to `∑ v ∈ U, singleFin v (evFin F v a)`.

Establish `hs : ∀ u, evalV F u s = if u ∈ U then evFin F u a else 0` using `fun u => by`. Rewrite using `[map_sum]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single u (fun v _ e => evalV_singleFin_ne (Ne.symm e) _) (fun e => (e h).elim), evalV_singleFin_self]`. Conclude with `Finset.sum_eq_zero fun v hv => evalV_singleFin_ne (fun e : u = v => h (e ▸ hv)) _`.

Establish `h1 : ψ ((0 : Ainf F), a.2 - s) = 1` using `hT _ (fun v hv => by`. Establish `: v ∈ U` using `by by_contra e; exact (hU v e).1 hv`. Rewrite using `[map_sub, hs, if_pos this]; exact sub_self _) fun v => by`. Rewrite using `[map_sub, hs]`. Use `split_ifs with h`.

Conclude with `(sub_self (evFin F v a)).symm ▸ zero_mem _`. Rewrite using `[sub_zero]`. Conclude with `(hU v h).2.2`. Set `χ : AddChar (Af F) ℂ` to `ψ.compAddMonoidHom (AddMonoidHom.inr (Ainf F) (Af F))`. Establish `h2 : χ s = ∏ v ∈ U, psiV ψ v (evFin F v a)`.

Establish `: ∀ V : Finset (Pl F), χ (∑ v ∈ V, singleFin v (evFin F v a)) = ∏ v ∈ V, psiV ψ v (evFin F v a)` using `fun V => by`. Proceed by induction on `V using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert v V hv ih => rw [Finset.sum_insert hv, Finset.prod_insert hv, AddChar.map_add_eq_mul, ih]`. Both sides reduce to the same expression.

Conclude with `this U`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ (s := U) fun v hv => by`. Assume the negation of the conclusion as `e`. Conclude with `hv (hU v e).2.1, ← h2]`. Express the relevant statement in the definitionally equal form `χ a.2 = _`.

Rewrite using `[← sub_add_cancel a.2 s, AddChar.map_add_eq_mul]`. Conclude with `(congrArg (· * χ s) h1).trans (one_mul _)`.
-/
theorem psi_fin (hψ : IsStd ψ) (a : AF F) : ψ ((0 : Ainf F), a.2) = ∏ᶠ v, psiV ψ v (evFin F v a) := by
  classical
  obtain ⟨T, hT⟩ := exists_triv hψ
  have hfin : {v : Pl F | ¬ (v ∉ T ∧ psiV ψ v (evFin F v a) = 1 ∧ evFin F v a ∈ v.adicCompletionIntegers F)}.Finite :=
    eventually_cofinite.1 (T.eventually_cofinite_notMem.and ((psiV_ev hψ a).and a.2.2))
  set U := hfin.toFinset
  have hU : ∀ v ∉ U, v ∉ T ∧ psiV ψ v (evFin F v a) = 1 ∧ evFin F v a ∈ v.adicCompletionIntegers F := fun v hv =>
    not_not.1 fun e => hv (hfin.mem_toFinset.2 e)
  let s : Af F := ∑ v ∈ U, singleFin v (evFin F v a)
  have hs : ∀ u, evalV F u s = if u ∈ U then evFin F u a else 0 := fun u => by
    rw [map_sum]
    split_ifs with h
    · rw [Finset.sum_eq_single u (fun v _ e => evalV_singleFin_ne (Ne.symm e) _) (fun e => (e h).elim), evalV_singleFin_self]
    · exact Finset.sum_eq_zero fun v hv => evalV_singleFin_ne (fun e : u = v => h (e ▸ hv)) _
  have h1 : ψ ((0 : Ainf F), a.2 - s) = 1 := hT _ (fun v hv => by
      have : v ∈ U := by by_contra e; exact (hU v e).1 hv
      rw [map_sub, hs, if_pos this]; exact sub_self _) fun v => by
    rw [map_sub, hs]
    split_ifs with h
    · exact (sub_self (evFin F v a)).symm ▸ zero_mem _
    · rw [sub_zero]; exact (hU v h).2.2
  let χ : AddChar (Af F) ℂ := ψ.compAddMonoidHom (AddMonoidHom.inr (Ainf F) (Af F))
  have h2 : χ s = ∏ v ∈ U, psiV ψ v (evFin F v a) := by
    have : ∀ V : Finset (Pl F), χ (∑ v ∈ V, singleFin v (evFin F v a)) = ∏ v ∈ V, psiV ψ v (evFin F v a) := fun V => by
      induction V using Finset.induction_on with
      | empty => simp
      | insert v V hv ih => rw [Finset.sum_insert hv, Finset.prod_insert hv, AddChar.map_add_eq_mul, ih]; rfl
    exact this U
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := U) fun v hv => by
    by_contra e; exact hv (hU v e).2.1, ← h2]
  change χ a.2 = _
  rw [← sub_add_cancel a.2 s, AddChar.map_add_eq_mul]
  exact (congrArg (· * χ s) h1).trans (one_mul _)

/- English proof (translation)
Establish `e : a = ((a.1, (0 : Af F)) : AF F) + (((0 : Ainf F), a.2) : AF F)` using `Prod.ext (add_zero _).symm (zero_add _).symm`. Establish `h` using `hψ.2.2 ((a.1, (0 : Af F)) : AF F) fun u hu => by`. Establish `: u.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu`. Conclude with `Prod.ext (show u.1 * a.1 = 0 by rw [this, zero_mul]) (mul_zero u.2)`. Rewrite using `[← psi_fin hψ]`.

Conclude with `(congrArg ψ e).trans ((ψ.map_add_eq_mul (pairA F a.1 0) (pairA F 0 a.2)).trans (congrArg (· * _) h))`.
-/
theorem psi_prod (hψ : IsStd ψ) (a : AF F) : ψ a = Complex.exp (-(2 * Real.pi * Complex.I) *
    (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) : ℝ)) * ∏ᶠ v, psiV ψ v (evFin F v a) := by
  have e : a = ((a.1, (0 : Af F)) : AF F) + (((0 : Ainf F), a.2) : AF F) := Prod.ext (add_zero _).symm (zero_add _).symm
  have h := hψ.2.2 ((a.1, (0 : Af F)) : AF F) fun u hu => by
    have : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
    exact Prod.ext (show u.1 * a.1 = 0 by rw [this, zero_mul]) (mul_zero u.2)
  rw [← psi_fin hψ]
  exact (congrArg ψ e).trans ((ψ.map_add_eq_mul (pairA F a.1 0) (pairA F 0 a.2)).trans (congrArg (· * _) h))

def evIH (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

/- English proof (translation)
Use `(invOf_eq_right_inv ?_).symm` and prove the remaining obligations. Rewrite using `[← map_ofNat f 2, ← map_mul, mul_invOf_self, map_one]`.
-/
theorem map_half {R S : Type} [CommRing R] [CommRing S] [Invertible (2 : R)] [Invertible (2 : S)] (f : R →+* S) :
    f (⅟2) = ⅟2 := by
  refine (invOf_eq_right_inv ?_).symm
  rw [← map_ofNat f 2, ← map_mul, mul_invOf_self, map_one]

open scoped Classical in
/- English proof (translation)
Set `c : (κ → mixedEmbedding.mixedSpace F) → ℂ` to `fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((beta F κ x (infV w.2) : ℝ) : ℂ))`. Establish `hb : Continuous fun x : κ → mixedEmbedding.mixedSpace F => beta F κ x (infV w.2)` using `(Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).continuous_of_finiteDimensional.comp (by unfold dotProduct; fun_prop)`. Establish `hT : Function.HasTemperateGrowth c` using `GlobalTheory.CompanionTheory.AdelicHeis.temperate_char c (by fun_prop) (fun t => by simp [c, Complex.norm_exp]) (by simp [c, beta]) fun s t => by`. Simplify using `only [c, beta, add_dotProduct, map_add, Complex.ofReal_add, mul_add, Complex.exp_add]`. Use `⟨Complex.exp (-(2 * Real.pi * Complex.I) * ((beta F κ (infV w.1) (infV w.2) / 2 : ℝ) : ℂ)) • SchwartzMap.smulLeftCLM ℂ c (SchwartzMap.compSubConstCLM ℂ (-infV w.1) f), fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hT, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, Complex.ofReal_add, mul_add, Complex.exp_add]`. Simplify using `only [c, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_isTr (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) : ∃ g, IsTr w f g := by
  let c : (κ → mixedEmbedding.mixedSpace F) → ℂ := fun x =>
    Complex.exp (-(2 * Real.pi * Complex.I) * ((beta F κ x (infV w.2) : ℝ) : ℂ))
  have hb : Continuous fun x : κ → mixedEmbedding.mixedSpace F => beta F κ x (infV w.2) :=
    (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).continuous_of_finiteDimensional.comp (by unfold dotProduct; fun_prop)
  have hT : Function.HasTemperateGrowth c := GlobalTheory.CompanionTheory.AdelicHeis.temperate_char c (by fun_prop)
    (fun t => by simp [c, Complex.norm_exp]) (by simp [c, beta]) fun s t => by
      simp only [c, beta, add_dotProduct, map_add, Complex.ofReal_add, mul_add, Complex.exp_add]
  refine ⟨Complex.exp (-(2 * Real.pi * Complex.I) * ((beta F κ (infV w.1) (infV w.2) / 2 : ℝ) : ℂ)) •
    SchwartzMap.smulLeftCLM ℂ c (SchwartzMap.compSubConstCLM ℂ (-infV w.1) f), fun x => ?_⟩
  rw [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hT, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add,
    Complex.ofReal_add, mul_add, Complex.exp_add]
  simp only [c, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _ w f`. Use `⟨exists_isTr w f, fun φ hφ => ⟨?_, fun g hg => funext fun x => ?_⟩⟩` and prove the remaining obligations. Establish `h1 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (w.1 i) ∈ v.adicCompletionIntegers F` using `eventually_all.2 fun i => (w.1 i).2.2`. Establish `h2 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (w.2 i) ∈ v.adicCompletionIntegers F` using `eventually_all.2 fun i => (w.2 i).2.2`. Establish `h3 : ∀ᶠ v : Pl F in cofinite, evFin F v (⅟2) ∈ v.adicCompletionIntegers F` using `(⅟2 : AF F).2.2`.

Use `filter_upwards [hφ, h1, h2, h3, psiV_int hψ] with v e e1 e2 e3 e4`. Rewrite `e3` using `[show evFin F v (⅟2) = ⅟2 from map_half (evFin F v).toRingHom]`. Use function extensionality and compare the values at `y`. Rewrite using `[e, schr]`. Distinguish the cases in `hy : ∀ i, y i ∈ v.adicCompletionIntegers F`.

Rewrite using `[Set.indicator_of_mem (show y + (locW v w).1 ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => add_mem (hy i) (e1 i)), Set.indicator_of_mem (show y ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy), e4 (y ⬝ᵥ (locW v w).2 + ⅟2 * ((locW v w) …`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem (show y + (locW v w).1 ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun h => hy fun i => by simpa [locW] using sub_mem (h i) (e1 i)), Set.indicator_of_notMem (show y ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy), m …`. Set `a : AF F` to `x ⬝ᵥ w.2 + ⅟2 * (w.1 ⬝ᵥ w.2)`. Establish `e1 : ∀ v, schr (psiV ψ v) (locW v w) (φ v) (fun i => evFin F v (x i)) = psiV ψ v (evFin F v a) * φ v fun i => evFin F v ((x + w.1) i)` using `fun v => by`.

Establish `hh : evFin F v (⅟2) = ⅟2` using `map_half (evFin F v).toRingHom`. Simplify using `only [schr, a, locW, dotProduct, map_add, map_mul, map_sum, hh, Pi.add_apply]`. Both sides reduce to the same expression. Establish `e2 : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) = beta F κ (fun i => evI F (x i)) (infV w.2) + beta F κ (infV w.1) (infV w.2) / 2`. Establish `h2 : evIH F (⅟2) = algebraMap ℝ _ (1 / 2)`.

Establish `: evIH F (⅟2) * algebraMap ℝ _ 2 = 1` using `by rw [map_ofNat, ← map_ofNat (evIH F) 2, ← map_mul, invOf_mul_self, map_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, ← map_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, map_one, mul_one]`. Use `_ = _ := by rw [this, one_mul]`. Express the relevant statement in the definitionally equal form `Algebra.trace ℝ _ (evIH F a) = _`.

Simplify using `only [a, map_add, map_mul, h2, ← Algebra.smul_def, map_smul, dotProduct, map_sum, beta, smul_eq_mul]`. Conclude with `congrArg₂ (· + ·) rfl ((one_div_mul_eq_div _ _).trans rfl)`. Establish `e3 : (fun i => evI F ((x + w.1) i)) = (fun i => evI F (x i)) + infV w.1` using `funext fun i => map_add (evIH F) _ _`. Express the relevant statement in the definitionally equal form `ψ a * _ = _`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, e1]`.

Rewrite using `[finprod_mul_distrib (eventually_cofinite.1 (psiV_ev hψ a)) (GlobalTheory.CompanionTheory.Ar.RT.Move.finite_mulSupport (vac := φ) hφ (Eventually.of_forall fun _ => rfl) (x + w.1)), hg, psi_prod hψ, e2, e3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pure_tensor_estimates_holds : PureSt := by
  intro F _ _ ψ hψ κ _ w f
  refine ⟨exists_isTr w f, fun φ hφ => ⟨?_, fun g hg => funext fun x => ?_⟩⟩
  · have h1 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (w.1 i) ∈ v.adicCompletionIntegers F := eventually_all.2 fun i => (w.1 i).2.2
    have h2 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (w.2 i) ∈ v.adicCompletionIntegers F := eventually_all.2 fun i => (w.2 i).2.2
    have h3 : ∀ᶠ v : Pl F in cofinite, evFin F v (⅟2) ∈ v.adicCompletionIntegers F := (⅟2 : AF F).2.2
    filter_upwards [hφ, h1, h2, h3, psiV_int hψ] with v e e1 e2 e3 e4
    rw [show evFin F v (⅟2) = ⅟2 from map_half (evFin F v).toRingHom] at e3
    funext y
    rw [e, schr]
    by_cases hy : ∀ i, y i ∈ v.adicCompletionIntegers F
    · rw [Set.indicator_of_mem (show y + (locW v w).1 ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        fun i => add_mem (hy i) (e1 i)), Set.indicator_of_mem (show y ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy),
        e4 (y ⬝ᵥ (locW v w).2 + ⅟2 * ((locW v w).1 ⬝ᵥ (locW v w).2)) (add_mem (sum_mem fun i _ => mul_mem (hy i) (e2 i)) (mul_mem e3 (sum_mem fun i _ => mul_mem (e1 i) (e2 i))))]
      simp
    · rw [Set.indicator_of_notMem (show y + (locW v w).1 ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        fun h => hy fun i => by simpa [locW] using sub_mem (h i) (e1 i)),
        Set.indicator_of_notMem (show y ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy), mul_zero]
  · let a : AF F := x ⬝ᵥ w.2 + ⅟2 * (w.1 ⬝ᵥ w.2)
    have e1 : ∀ v, schr (psiV ψ v) (locW v w) (φ v) (fun i => evFin F v (x i)) =
        psiV ψ v (evFin F v a) * φ v fun i => evFin F v ((x + w.1) i) := fun v => by
      have hh : evFin F v (⅟2) = ⅟2 := map_half (evFin F v).toRingHom
      simp only [schr, a, locW, dotProduct, map_add, map_mul, map_sum, hh, Pi.add_apply]
      rfl
    have e2 : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) =
        beta F κ (fun i => evI F (x i)) (infV w.2) + beta F κ (infV w.1) (infV w.2) / 2 := by
      have h2 : evIH F (⅟2) = algebraMap ℝ _ (1 / 2) := by
        have : evIH F (⅟2) * algebraMap ℝ _ 2 = 1 := by rw [map_ofNat, ← map_ofNat (evIH F) 2, ← map_mul, invOf_mul_self, map_one]
        calc evIH F (⅟2) = evIH F (⅟2) * algebraMap ℝ _ 2 * algebraMap ℝ _ (1 / 2) := by
              rw [mul_assoc, ← map_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, map_one, mul_one]
          _ = _ := by rw [this, one_mul]
      change Algebra.trace ℝ _ (evIH F a) = _
      simp only [a, map_add, map_mul, h2, ← Algebra.smul_def, map_smul, dotProduct, map_sum, beta, smul_eq_mul]
      exact congrArg₂ (· + ·) rfl ((one_div_mul_eq_div _ _).trans rfl)
    have e3 : (fun i => evI F ((x + w.1) i)) = (fun i => evI F (x i)) + infV w.1 := funext fun i => map_add (evIH F) _ _
    change ψ a * _ = _
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, e1]
    rw [finprod_mul_distrib (eventually_cofinite.1 (psiV_ev hψ a))
      (GlobalTheory.CompanionTheory.Ar.RT.Move.finite_mulSupport (vac := φ) hφ (Eventually.of_forall fun _ => rfl) (x + w.1)), hg, psi_prod hψ, e2, e3]
    ring

end PositivityTheory.Mix
