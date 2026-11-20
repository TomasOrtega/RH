import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SInternal
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesEvalOfPowMem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MonicNormLtOne

section Gen

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Rewrite using `[← MvPolynomial.coe_monomial, GlobalTheory.algHom_coe_mvPolynomial, MvPolynomial.aeval_monomial, map_one, one_mul]`.
-/
private theorem ts_monomial {O σ S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (f : MvPowerSeries σ O →ₐ[O] S) (m : σ →₀ ℕ) :
    f (monomial m 1) = m.prod fun s k => f (MvPowerSeries.X s) ^ k := by
  rw [← MvPolynomial.coe_monomial, GlobalTheory.algHom_coe_mvPolynomial, MvPolynomial.aeval_monomial, map_one, one_mul]

/- English proof (translation)
Proceed by induction on `d using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg`. Rewrite using `[Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), hf, hg, map_add, ofAdd_add, map_mul, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `single i k`. Rewrite using `[Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp), Finsupp.weight_single, ofAdd_nsmul, map_pow, Units.val_pow_eq_pow_val, mul_pow]`.
-/
private theorem ts_prod {X σ S : Type} [AddCommGroup X] [CommRing S] (wt : σ → X)
    (t : Multiplicative X →* Sˣ) (x : σ → S) (d : σ →₀ ℕ) :
    (d.prod fun i k => ((t (Multiplicative.ofAdd (wt i)) : S) * x i) ^ k) =
      (t (Multiplicative.ofAdd (Finsupp.weight wt d)) : S) * d.prod fun i k => x i ^ k := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), hf, hg, map_add, ofAdd_add,
      map_mul, Units.val_mul]
    ring
  | single i k =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
      Finsupp.weight_single, ofAdd_nsmul, map_pow, Units.val_pow_eq_pow_val, mul_pow]

/- English proof (translation)
Use `⟨(truncTotal n F).support.image (Finsupp.weight wt), nat_le_order fun d hd => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_sum]`. Simplify using `only [coeff_wcomp]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with h`.

Conclude with `sub_self _`. Rewrite using `[sub_zero]`. Assume the negation of the conclusion as `h0`. Use `h (Finset.mem_image_of_mem _ (MvPolynomial.mem_support_iff.2 ?_))` and prove the remaining obligations. Rewrite using `[coeff_truncTotal _ hd]` and apply the resulting hypothesis.
-/
private theorem ts_approx {O X σ : Type} [CommRing O] [AddCommGroup X] [Finite σ] (wt : σ → X)
    (F : MvPowerSeries σ O) (n : ℕ) :
    ∃ s : Finset X, (n : ℕ∞) ≤ (F - ∑ j ∈ s, wcomp O wt j F).order := by
  classical
  refine ⟨(truncTotal n F).support.image (Finsupp.weight wt), nat_le_order fun d hd => ?_⟩
  rw [map_sub, map_sum]
  simp only [coeff_wcomp]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    by_contra h0
    refine h (Finset.mem_image_of_mem _ (MvPolynomial.mem_support_iff.2 ?_))
    rwa [coeff_truncTotal _ hd]

/- English proof (translation)
Use `GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun n => ?_` and prove the remaining obligations. Take `⟨s, hs⟩` from `ts_approx wt F n`. Use `GlobalTheory.algHom_mem_pow_of_le_order φ hφ hs` as an intermediate fact. Simplify `this` using `[h]`.
-/
private theorem ts_vanish {O X σ S : Type} [CommRing O] [AddCommGroup X] [Finite σ] [CommRing S]
    [Algebra O S] (wt : σ → X) (J : Ideal S) [IsHausdorff J S] (φ : MvPowerSeries σ O →ₐ[O] S)
    (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ J) (F : MvPowerSeries σ O) (h : ∀ j, φ (wcomp O wt j F) = 0) :
    φ F = 0 := by
  refine GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun n => ?_
  obtain ⟨s, hs⟩ := ts_approx wt F n
  have := GlobalTheory.algHom_mem_pow_of_le_order φ hφ hs
  simpa [h] using this

section Core

variable {O X R K : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
  [CommRing K] [Algebra O K] (ξ : W.A →ₐ[O] K)

/- English proof (translation)
Rewrite using `[ts_monomial]`. Conclude with `map_finsuppProd W.A.val _ _`.
-/
private theorem ts_zprod (m : W.σ →₀ ℕ) :
    ((m.prod fun s k => W.zA s ^ k : W.A) : R) = W.π (monomial m 1) := by
  rw [ts_monomial]
  exact map_finsuppProd W.A.val _ _

variable [Module.Free ℤ X] [Module.Finite ℤ X] {B : Type} [CommRing B] [Algebra O B] (ι : B →ₐ[O] K)
  (t : Multiplicative X →* Kˣ) (g : MvPowerSeries W.σ O →ₐ[O] B)

/- English proof (translation)
Take `⟨μ, hμ, h⟩` from `part_span O R X W S j hS`. Take `⟨b, hb, rfl⟩` from `h F hF`. Set `β : (W.σ →₀ ℕ) → W.A` to `fun m => ⟨W.π (b m), W.part_le_A ⟨b m, hb m, rfl⟩⟩`. Use `choose c hc hc' using fun m => hI (b m) (hb m) (β m) rfl`. Establish `hx' : x = ∑ m ∈ μ, β m * m.prod fun s k => W.zA s ^ k`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hx, map_sum, AddSubmonoidClass.coe_finset_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Subalgebra.coe_mul, ts_zprod, map_mul]`. Use `⟨∑ m ∈ μ, c m * g (monomial m 1), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hx', map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hc, ts_monomial, map_finsuppProd, map_finsuppProd]`. Simplify using `only [map_pow, hg]`. Rewrite using `[ts_prod W.wt t (fun s => ξ (W.zA s)), hS m (hμ hm)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_sum, ← Finset.sum_sub_distrib]`. Use `Ideal.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← sub_mul]`. Conclude with `Ideal.mul_mem_mul (hc' m) (hJ m (hμ hm))`.
-/
private theorem ts_step (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (I J : Ideal B) (S : Set (W.σ →₀ ℕ)) (j : X) (hS : ∀ n ∈ S, Finsupp.weight W.wt n = j)
    (hJ : ∀ n ∈ S, g (monomial n 1) ∈ J)
    (hI : ∀ b, b ∈ wtPart O W.wt 0 → ∀ x : W.A, (x : R) = W.π b → ∃ c, ι c = ξ x ∧ g b - c ∈ I)
    (F : MvPowerSeries W.σ O) (hF : ∀ n, n ∉ S → coeff n F = 0) (x : W.A) (hx : (x : R) = W.π F) :
    ∃ c, ι c = t (Multiplicative.ofAdd j) * ξ x ∧ g F - c ∈ I * J := by
  obtain ⟨μ, hμ, h⟩ := part_span O R X W S j hS
  obtain ⟨b, hb, rfl⟩ := h F hF
  let β : (W.σ →₀ ℕ) → W.A := fun m => ⟨W.π (b m), W.part_le_A ⟨b m, hb m, rfl⟩⟩
  choose c hc hc' using fun m => hI (b m) (hb m) (β m) rfl
  have hx' : x = ∑ m ∈ μ, β m * m.prod fun s k => W.zA s ^ k := by
    apply Subtype.ext
    rw [hx, map_sum, AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Subalgebra.coe_mul, ts_zprod, map_mul]
  refine ⟨∑ m ∈ μ, c m * g (monomial m 1), ?_, ?_⟩
  · rw [hx', map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [map_mul, map_mul, hc, ts_monomial, map_finsuppProd, map_finsuppProd]
    simp only [map_pow, hg]
    rw [ts_prod W.wt t (fun s => ξ (W.zA s)), hS m (hμ hm)]
    ring
  · rw [map_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun m hm => ?_
    rw [map_mul, ← sub_mul]
    exact Ideal.mul_mem_mul (hc' m) (hJ m (hμ hm))

/- English proof (translation)
Establish `hQ : ∀ N : ℕ, ∀ b, b ∈ wtPart O W.wt 0 → ∀ x : W.A, (x : R) = W.π b → ∃ c, ι c = ξ x ∧ g b - c ∈ J ^ N`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `b hb x hx`.

Take `⟨c, hc⟩` from `h0 x ⟨b, hb, hx.symm⟩`. Conclude with `⟨c, hc, by simp⟩`. Consider the case `succ N ih`. Introduce `b hb x hx`. Take `⟨c, hc, hc'⟩` from `ts_step W ξ ι t g hg (J ^ N) J {n | Finsupp.weight W.wt n = 0 ∧ n ≠ 0} 0 (fun n hn => hn.1) (fun n hn => by`.

Use `GlobalTheory.algHom_sub_constantCoeff_mem g hJ (monomial n 1)` as an intermediate fact. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg hn.2.symm, map_zero, sub_zero] at this) ih` and apply the resulting hypothesis. Use the proof step `(b - algebraMap O _ (constantCoeff b)) (fun n hn => by`. Rewrite using `[map_sub, MvPowerSeries.algebraMap_apply, coeff_C]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[sub_zero]`. Conclude with `hb n fun h' => hn ⟨h', h⟩)`. Use the proof step `(x - algebraMap O _ (constantCoeff b)) (by`.

Rewrite using `[map_sub, AlgHom.commutes, ← hx]`. Use the proof step `rfl)`. Use `⟨c + algebraMap O B (constantCoeff b), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hc, AlgHom.commutes, map_sub, AlgHom.commutes]`. Simplify using the standard rewrite rules.

Rewrite `hc'` using `[map_sub, AlgHom.commutes, sub_sub, add_comm]`. Rewrite using `[pow_succ]` and apply the resulting hypothesis. Take `⟨c, hc, hc'⟩` from `ts_step W ξ ι t g hg ⊥ ⊤ {n | Finsupp.weight W.wt n = j} j (fun n hn => hn) (fun _ _ => trivial) (fun b hb x hx => by`. Take `⟨c, hc, -⟩` from `hQ 0 b hb x hx`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations.

Rewrite using `[Ideal.mem_bot, sub_eq_zero]`. Use `GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun N => ?_` and prove the remaining obligations. Take `⟨c', hc1, hc2⟩` from `hQ N b hb x hx`. Rewrite using `[hι (hc.trans hc1.symm)]) F hF x hx` and apply the resulting hypothesis. Rewrite `hc'` using `[Ideal.bot_mul, Ideal.mem_bot, sub_eq_zero]`.

Rewrite using `[hc', hc]`.
-/
private theorem ts_agree (hι : Function.Injective ι)
    (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (J : Ideal B) [IsHausdorff J B] (hJ : ∀ s, g (MvPowerSeries.X s) ∈ J)
    (h0 : ∀ x ∈ W.gr 0, ∃ c, ι c = ξ x) (j : X) (F : MvPowerSeries W.σ O) (hF : F ∈ wtPart O W.wt j)
    (x : W.A) (hx : (x : R) = W.π F) : ι (g F) = t (Multiplicative.ofAdd j) * ξ x := by
  classical
  have hQ : ∀ N : ℕ, ∀ b, b ∈ wtPart O W.wt 0 → ∀ x : W.A, (x : R) = W.π b →
      ∃ c, ι c = ξ x ∧ g b - c ∈ J ^ N := by
    intro N
    induction N with
    | zero =>
      intro b hb x hx
      obtain ⟨c, hc⟩ := h0 x ⟨b, hb, hx.symm⟩
      exact ⟨c, hc, by simp⟩
    | succ N ih =>
      intro b hb x hx
      obtain ⟨c, hc, hc'⟩ := ts_step W ξ ι t g hg (J ^ N) J {n | Finsupp.weight W.wt n = 0 ∧ n ≠ 0} 0
        (fun n hn => hn.1) (fun n hn => by
          have := GlobalTheory.algHom_sub_constantCoeff_mem g hJ (monomial n 1)
          rwa [← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg hn.2.symm, map_zero,
            sub_zero] at this) ih
        (b - algebraMap O _ (constantCoeff b)) (fun n hn => by
          rw [map_sub, MvPowerSeries.algebraMap_apply, coeff_C]
          split_ifs with h
          · subst h; simp
          · rw [sub_zero]
            exact hb n fun h' => hn ⟨h', h⟩)
        (x - algebraMap O _ (constantCoeff b)) (by
          rw [map_sub, AlgHom.commutes, ← hx]; rfl)
      refine ⟨c + algebraMap O B (constantCoeff b), ?_, ?_⟩
      · rw [map_add, hc, AlgHom.commutes, map_sub, AlgHom.commutes]
        simp
      · rw [map_sub, AlgHom.commutes, sub_sub, add_comm] at hc'
        rwa [pow_succ]
  obtain ⟨c, hc, hc'⟩ := ts_step W ξ ι t g hg ⊥ ⊤ {n | Finsupp.weight W.wt n = j} j (fun n hn => hn)
    (fun _ _ => trivial) (fun b hb x hx => by
      obtain ⟨c, hc, -⟩ := hQ 0 b hb x hx
      refine ⟨c, hc, ?_⟩
      rw [Ideal.mem_bot, sub_eq_zero]
      refine GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun N => ?_
      obtain ⟨c', hc1, hc2⟩ := hQ N b hb x hx
      rwa [hι (hc.trans hc1.symm)]) F hF x hx
  rw [Ideal.bot_mul, Ideal.mem_bot, sub_eq_zero] at hc'
  rw [hc', hc]

/- English proof (translation)
Establish `key` using `ts_agree W ξ ι t g hι hg J hJ h0`. Establish `hker : ∀ F ∈ RingHom.ker W.π, g F = 0`. Introduce `F hF`. Use `ts_vanish W.wt J g hJ F fun j => hι ?_` and prove the remaining obligations. Establish `h1 : W.π (wcomp O W.wt j F) = 0` using `W.homog F hF j`.

Rewrite using `[key j _ (wcomp_mem O W.wt j F) 0 h1.symm, map_zero, map_zero, mul_zero]`. Set `f : R →ₐ[O] B` to `(Ideal.Quotient.liftₐ (RingHom.ker W.π) g hker).comp (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom`. Establish `hf : ∀ F, f (W.π F) = g F`. Introduce `F`. Establish `: (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π F) = Ideal.Quotient.mk _ F`.

Rewrite using `[AlgEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `only [f, AlgHom.comp_apply, AlgEquiv.coe_algHom]`. Use `erw [this]`. Both sides reduce to the same expression.

Use `⟨f, AlgHom.ext fun x => ?_⟩` and prove the remaining obligations. Proceed by induction on `x using DirectSum.Decomposition.inductionOn W.gr with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`. Consider the case `@homogeneous j x`.

Take `⟨x, hx⟩` from `x`. Rewrite using `[act_of_mem W.gr t ξ hx]`. Take `⟨F, hF, hFx⟩` from `hx`. Establish `hFx' : (x : R) = W.π F` using `hFx.symm`. Rewrite using `[← key j F hF x hFx', ← hf, ← hFx']`.

Both sides reduce to the same expression.
-/
private theorem ts_factor [DecidableEq X] (hι : Function.Injective ι)
    (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (J : Ideal B) [IsHausdorff J B] (hJ : ∀ s, g (MvPowerSeries.X s) ∈ J)
    (h0 : ∀ x ∈ W.gr 0, ∃ c, ι c = ξ x) :
    ∃ f : R →ₐ[O] B, (ι.comp f).comp W.A.val = act W.gr t ξ := by
  have key := ts_agree W ξ ι t g hι hg J hJ h0
  have hker : ∀ F ∈ RingHom.ker W.π, g F = 0 := by
    intro F hF
    refine ts_vanish W.wt J g hJ F fun j => hι ?_
    have h1 : W.π (wcomp O W.wt j F) = 0 := W.homog F hF j
    rw [key j _ (wcomp_mem O W.wt j F) 0 h1.symm, map_zero, map_zero, mul_zero]
  let f : R →ₐ[O] B := (Ideal.Quotient.liftₐ (RingHom.ker W.π) g hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom
  have hf : ∀ F, f (W.π F) = g F := by
    intro F
    have : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π F) = Ideal.Quotient.mk _ F := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    simp only [f, AlgHom.comp_apply, AlgEquiv.coe_algHom]
    erw [this]
    rfl
  refine ⟨f, AlgHom.ext fun x => ?_⟩
  induction x using DirectSum.Decomposition.inductionOn W.gr with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | @homogeneous j x =>
    obtain ⟨x, hx⟩ := x
    rw [act_of_mem W.gr t ξ hx]
    obtain ⟨F, hF, hFx⟩ := hx
    have hFx' : (x : R) = W.π F := hFx.symm
    rw [← key j F hF x hFx', ← hf, ← hFx']
    rfl

end Core

end Gen

section SlopeTestRemainingChoices

open IsLocalRing Polynomial

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Establish `h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x)` using `rfl`. Rewrite using `[h0, spectralValue_le_one_iff (minpoly.monic hi)]`. Prove the components needed by the constructor for the conclusion. Introduce `h n`.

Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]`. Conclude with `PadicInt.norm_le_one _`. Introduce `h`. Establish `hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l])` using `(lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)`.

Conclude with `⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩`.
-/
private theorem ts_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.MonicNormLtOne.mc_norm_lt y a ha`.
-/
private theorem ts_norm_lt {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]
    (y : R →ₐ[ℤ_[l]] PadicAlgCl l) (a : R) (ha : a ∈ maximalIdeal R) : ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.MonicNormLtOne.mc_norm_lt y a ha

end SlopeTestRemainingChoices

section Ext

open IsLocalRing UpperTheory.V.Alg

/- English proof (translation)
Establish `hw' : ∀ x : DualNumber K, ‖x.fst‖ ≤ 1 → IsIntegral O x` using `fun x hx => by`. Rewrite using `[← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]`. Use `IsIntegral.add ((hw _ hx).map (TrivSqZeroExt.inlAlgHom O K K)) ?_` and prove the remaining obligations. Conclude with `⟨Polynomial.X ^ 2, Polynomial.monic_X_pow 2, by simp [pow_two]⟩`. Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible O`.

Establish `hp0 : algebraMap O K p ≠ 0` using `(map_ne_zero_iff _ hinj).2 hp.ne_zero`. Set `y : W.σ → DualNumber K` to `fun s => ξ (W.zA s)`. Establish `hc : ∀ s, ∃ n : ℕ, IsIntegral O ((algebraMap O K p)⁻¹ • y s ^ n)` using `fun s => by`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (norm_pos_iff.2 hp0) (hz s)`. Use `⟨n, hw' _ ?_⟩` and prove the remaining obligations.

Rewrite using `[TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_pow, smul_eq_mul, norm_mul, norm_inv, norm_pow, ← div_eq_inv_mul]`. Conclude with `div_le_one_of_le₀ hn.le (norm_nonneg _)`. Use `choose e he using hc`. Take `⟨T, hT⟩` from `id hfg`. Set `G : Set (DualNumber K)` to `(T : Set _) ∪ Set.range y ∪ Set.range fun s => (algebraMap O K p)⁻¹ • y s ^ e s`.

Establish `hG : G.Finite` using `(T.finite_toSet.union (Set.finite_range _)).union (Set.finite_range _)`. Establish `hGi : ∀ x ∈ G, IsIntegral O x`. Introduce and unpack `x ((hx | ⟨s, rfl⟩) | ⟨s, rfl⟩)`. Establish `: x ∈ (W.gr 0).map ξ.toLinearMap` using `hT ▸ Submodule.subset_span hx`. Take `⟨a, -, rfl⟩` from `this`.

Conclude with `hw' _ (h1 a)`. Conclude with `hw' _ (hz s).le`. Conclude with `he s`. Set `B : Subalgebra O (DualNumber K)` to `Algebra.adjoin O G`. Use `haveI : Module.Finite O B := Algebra.finite_adjoin_of_finite_of_isIntegral hG hGi`.

Use `haveI : IsNoetherianRing B := IsNoetherianRing.of_finite O B`. Use `haveI := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal O) B`. Set `J : Ideal B` to `((maximalIdeal O).map (algebraMap O B)).radical`. Take `⟨N, hN⟩` from `Ideal.exists_radical_pow_le_of_fg ((maximalIdeal O).map (algebraMap O B)) (IsNoetherian.noetherian _)`. Use `haveI : IsAdicComplete J B := { toIsHausdorff := GlobalTheory.NilpotentEval.isHausdorff_of_pow_le hN toIsPrecomplete := GlobalTheory.NilpotentEval.isPrecomplete_of_pow_le hN Ideal.le_radical }`.

Set `yB : W.σ → B` to `fun s => ⟨y s, Algebra.subset_adjoin (Or.inl (Or.inr ⟨s, rfl⟩))⟩`. Establish `hyB : ∀ s, yB s ∈ J` using `fun s => by`. Use `⟨e s, ?_⟩` and prove the remaining obligations. Establish `: yB s ^ e s = algebraMap O B p * ⟨(algebraMap O K p)⁻¹ • y s ^ e s, Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show y s ^ e s = algebraMap O (DualNumber K) p * ((algebraMap O K p)⁻¹ • y s ^ e s)`. Rewrite using `[← Algebra.smul_def, ← algebraMap_smul K p, smul_inv_smul₀ hp0]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp.not_isUnit)`. Take `⟨f, hf⟩` from `ts_factor W ξ B.val 1 (GlobalTheory.mvEvalAdic O J yB hyB) Subtype.val_injective (fun s => by rw [GlobalTheory.mvEvalAdic_X]; simp [yB, y]) J (fun s => by rw [GlobalTheory.mvEvalAdic_X]; exact hyB s) (fun x hx => by`.

Establish `h1 : ξ x ∈ Submodule.span O (T : Set (DualNumber K))` using `hT ▸ Submodule.mem_map_of_mem hx`. Establish `h2 : Submodule.span O (T : Set (DualNumber K)) ≤ B.toSubmodule` using `Submodule.span_le.2 fun a ha => Algebra.subset_adjoin (Or.inl (Or.inl ha))`. Conclude with `⟨⟨ξ x, h2 h1⟩, rfl⟩)`. Use `⟨B.val.comp f, fun x => ?_⟩` and prove the remaining obligations. Establish `h2 : (B.val.comp f) x = act W.gr 1 ξ x` using `DFunLike.congr_fun hf x`.

Rewrite using `[h2]`. Use `clear h2`. Proceed by induction on `x using DirectSum.Decomposition.inductionOn W.gr with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.

Consider the case `@homogeneous j x => rw [act_of_mem W.gr 1 ξ x.2]`. Simplify using the standard rewrite rules.
-/
private theorem ts_ext {O X R K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X]
    [CommRing R] [Algebra O R] (W : WPres O X R) [NormedField K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) (hw : ∀ x : K, ‖x‖ ≤ 1 → IsIntegral O x)
    (ξ : W.A →ₐ[O] DualNumber K) (h1 : ∀ x, ‖(ξ x).fst‖ ≤ 1) (hz : ∀ s, ‖(ξ (W.zA s)).fst‖ < 1)
    (hfg : ((W.gr 0).map ξ.toLinearMap).FG) :
    ∃ Ξ : R →ₐ[O] DualNumber K, ∀ x : W.A, Ξ x = ξ x := by
  have hw' : ∀ x : DualNumber K, ‖x.fst‖ ≤ 1 → IsIntegral O x := fun x hx => by
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    refine IsIntegral.add ((hw _ hx).map (TrivSqZeroExt.inlAlgHom O K K)) ?_
    exact ⟨Polynomial.X ^ 2, Polynomial.monic_X_pow 2, by simp [pow_two]⟩
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp0 : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ hinj).2 hp.ne_zero
  let y : W.σ → DualNumber K := fun s => ξ (W.zA s)
  have hc : ∀ s, ∃ n : ℕ, IsIntegral O ((algebraMap O K p)⁻¹ • y s ^ n) := fun s => by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hp0) (hz s)
    refine ⟨n, hw' _ ?_⟩
    rw [TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_pow, smul_eq_mul, norm_mul, norm_inv, norm_pow, ← div_eq_inv_mul]
    exact div_le_one_of_le₀ hn.le (norm_nonneg _)
  choose e he using hc
  obtain ⟨T, hT⟩ := id hfg
  let G : Set (DualNumber K) := (T : Set _) ∪ Set.range y ∪ Set.range fun s => (algebraMap O K p)⁻¹ • y s ^ e s
  have hG : G.Finite := (T.finite_toSet.union (Set.finite_range _)).union (Set.finite_range _)
  have hGi : ∀ x ∈ G, IsIntegral O x := by
    rintro x ((hx | ⟨s, rfl⟩) | ⟨s, rfl⟩)
    · have : x ∈ (W.gr 0).map ξ.toLinearMap := hT ▸ Submodule.subset_span hx
      obtain ⟨a, -, rfl⟩ := this
      exact hw' _ (h1 a)
    · exact hw' _ (hz s).le
    · exact he s
  let B : Subalgebra O (DualNumber K) := Algebra.adjoin O G
  haveI : Module.Finite O B := Algebra.finite_adjoin_of_finite_of_isIntegral hG hGi
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite O B
  haveI := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal O) B
  let J : Ideal B := ((maximalIdeal O).map (algebraMap O B)).radical
  obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg ((maximalIdeal O).map (algebraMap O B))
    (IsNoetherian.noetherian _)
  haveI : IsAdicComplete J B :=
    { toIsHausdorff := GlobalTheory.NilpotentEval.isHausdorff_of_pow_le hN
      toIsPrecomplete := GlobalTheory.NilpotentEval.isPrecomplete_of_pow_le hN Ideal.le_radical }
  let yB : W.σ → B := fun s => ⟨y s, Algebra.subset_adjoin (Or.inl (Or.inr ⟨s, rfl⟩))⟩
  have hyB : ∀ s, yB s ∈ J := fun s => by
    refine ⟨e s, ?_⟩
    have : yB s ^ e s = algebraMap O B p *
        ⟨(algebraMap O K p)⁻¹ • y s ^ e s, Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)⟩ := by
      apply Subtype.ext
      show y s ^ e s = algebraMap O (DualNumber K) p * ((algebraMap O K p)⁻¹ • y s ^ e s)
      rw [← Algebra.smul_def, ← algebraMap_smul K p, smul_inv_smul₀ hp0]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp.not_isUnit)
  obtain ⟨f, hf⟩ := ts_factor W ξ B.val 1 (GlobalTheory.mvEvalAdic O J yB hyB) Subtype.val_injective
    (fun s => by rw [GlobalTheory.mvEvalAdic_X]; simp [yB, y]) J (fun s => by rw [GlobalTheory.mvEvalAdic_X]; exact hyB s)
    (fun x hx => by
      have h1 : ξ x ∈ Submodule.span O (T : Set (DualNumber K)) := hT ▸ Submodule.mem_map_of_mem hx
      have h2 : Submodule.span O (T : Set (DualNumber K)) ≤ B.toSubmodule :=
        Submodule.span_le.2 fun a ha => Algebra.subset_adjoin (Or.inl (Or.inl ha))
      exact ⟨⟨ξ x, h2 h1⟩, rfl⟩)
  refine ⟨B.val.comp f, fun x => ?_⟩
  have h2 : (B.val.comp f) x = act W.gr 1 ξ x := DFunLike.congr_fun hf x
  rw [h2]
  clear h2
  induction x using DirectSum.Decomposition.inductionOn W.gr with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | @homogeneous j x => rw [act_of_mem W.gr 1 ξ x.2]; simp

private def ts_near {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] (hO : ∀ a : O, ‖algebraMap O K a‖ ≤ 1) (A : Subalgebra O R) (m : Ideal R) (f : A →ₐ[O] K) :
    Subalgebra O A where
  carrier := {x | ∃ a : O, (x : R) - algebraMap O R a ∈ m ∧ ‖f x - algebraMap O K a‖ < 1}
  add_mem' := by
    rintro x y ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩
    refine ⟨a + b, ?_, ?_⟩
    · convert add_mem ha hb using 1
      rw [map_add, Subalgebra.coe_add]; ring
    · have : f (x + y) - algebraMap O K (a + b) = (f x - algebraMap O K a) + (f y - algebraMap O K b) := by
        rw [map_add, map_add]; ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha' hb')
  mul_mem' := by
    rintro x y ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩
    refine ⟨a * b, ?_, ?_⟩
    · convert add_mem (m.mul_mem_right (y : R) ha) (m.mul_mem_left (algebraMap O R a) hb) using 1
      rw [map_mul, Subalgebra.coe_mul]; ring
    · have : f (x * y) - algebraMap O K (a * b) =
          (f x - algebraMap O K a) * f y + algebraMap O K a * (f y - algebraMap O K b) := by
        rw [map_mul, map_mul]; ring
      have hy : ‖f y‖ ≤ 1 := by
        rw [← sub_add_cancel (f y) (algebraMap O K b)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb'.le (hO b))
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans_lt ha'
      · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (hO a)).trans_lt hb'
  algebraMap_mem' a := ⟨a, by simp, by simp⟩

end Ext

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD M hF ξ hξ`. Take `⟨-, -, WS, hWS, hz⟩` from `sInternal D hD M`. Establish `hsp` using `spanMono D hD M hF`. Establish `hO : ∀ a : c.O, ‖algebraMap c.O (PadicAlgCl l) a‖ ≤ 1` using `fun a => (ts_intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map c.O.val)`. Establish `hO' : ∀ a ∈ maximalIdeal c.O, ‖algebraMap c.O (PadicAlgCl l) a‖ < 1` using `ts_norm_lt c.O.val`.

Set `f : M.SS →ₐ[c.O] PadicAlgCl l` to `(TrivSqZeroExt.fstHom c.O _ _).comp ξ`. Set `N` to `ts_near hO M.SS (maximalIdeal M.S) f`. Establish `hent : ∀ g i j, M.ru.hom g i j ∈ N.map M.SS.val` using `fun g i j => by`. Use `⟨M.ent g i j, ⟨D.r0 g i j, ?_, hξ g i j⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[← res_eq_zero_iff c.O, map_sub, AlgHom.commutes, sub_eq_zero]`.

Conclude with `M.ru.red g i j`. Establish `hN : ∀ x : M.SS, x ∈ N` using `fun x => by`. Establish `h1 : (⨆ w, M.sPart w) ≤ (N.map M.SS.val).toSubmodule`. Use `iSup_le fun w => ?_` and prove the remaining obligations. Rewrite using `[hsp w, Submodule.span_le]`.

Introduce and unpack `_ ⟨L, -, rfl⟩`. Use `Subalgebra.list_prod_mem _ fun y hy => ?_` and prove the remaining obligations. Take `⟨a, -, rfl⟩` from `List.mem_map.1 hy`. Conclude with `hent _ _ _`. Take `⟨y, hy, hyx⟩` from `h1 x.2`.

Rewrite using `[← (Subtype.ext hyx : y = x)]` and apply the resulting hypothesis. Establish `hle : WS.A ≤ M.SS` using `fun x hx => iSup_mono (fun w => (hWS w).le) hx`. Establish `hge : M.SS ≤ WS.A` using `fun x hx => iSup_mono (fun w => (hWS w).ge) hx`. Establish `hfg : (WS.part 0).FG` using `by haveI := hF M.S M.ru M.pt`. Establish `h1 : (Algebra.adjoin c.O (mono M.ru.hom 0)).toSubmodule.FG` using `Module.Finite.iff_fg.1 this`.

Use `h1.of_le ?_` and prove the remaining obligations. Rewrite using `[hWS, hsp, Submodule.span_le]`. Conclude with `Algebra.subset_adjoin`. Take `⟨Ξ, hΞ⟩` from `ts_ext WS (K := PadicAlgCl l) Subtype.val_injective (fun x hx => ((ts_intIff x).2 hx).tower_top) (ξ.comp (Subalgebra.inclusion hle)) (fun x => by`. Take `⟨a, -, ha⟩` from `hN (Subalgebra.inclusion hle x)`.

Use `show ‖f (Subalgebra.inclusion hle x)‖ ≤ 1`. Rewrite using `[← sub_add_cancel (f _) (algebraMap c.O _ a)]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha.le (hO a)))`. Use the proof step `(fun s => by`. Take `⟨a, ha0, ha⟩` from `hN (Subalgebra.inclusion hle (WS.zA s))`.

Establish `h1 : algebraMap c.O M.S a ∈ maximalIdeal M.S`. Use `Ideal.sub_mem _ (hz s) ha0` as an intermediate fact. Rewrite `this` using `[show WS.z s - (((Subalgebra.inclusion hle (WS.zA s) : M.SS) : M.S) - algebraMap c.O M.S a) = algebraMap c.O M.S a from sub_sub_cancel _ _]`. Then use the resulting hypothesis. Establish `h2 : a ∈ maximalIdeal c.O` using `fun hu => h1 (hu.map _)`. Use `show ‖f (Subalgebra.inclusion hle (WS.zA s))‖ < 1`.

Rewrite using `[← sub_add_cancel (f _) (algebraMap c.O _ a)]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha (hO' a h2)))`. Use the proof step `(Submodule.FG.map _ (Submodule.fg_of_fg_map_injective WS.A.val.toLinearMap Subtype.val_injective (by`. Use `hfg.of_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Conclude with `hx)))`. Use `⟨M.S, _, _, _, M.ru, Ξ, M.pt, ?_⟩` and prove the remaining obligations. Use `ext1 g`. Use `ext1 i j`. Conclude with `(hΞ ⟨_, hge (M.ent g i j).2⟩).symm`.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.tanScale :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, D.Fin0 → ∀ ξ : M.SS →ₐ[c.O] DualNumber (PadicAlgCl l), (∀ g i j, ‖(M.rep ξ g i j).fst - D.r0E g i j‖ < 1) → D.PtIn _ (M.rep ξ) := by
  intro Ω _ _ _ l _ c D hD M hF ξ hξ
  obtain ⟨-, -, WS, hWS, hz⟩ := sInternal D hD M
  have hsp := spanMono D hD M hF
  have hO : ∀ a : c.O, ‖algebraMap c.O (PadicAlgCl l) a‖ ≤ 1 := fun a =>
    (ts_intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map c.O.val)
  have hO' : ∀ a ∈ maximalIdeal c.O, ‖algebraMap c.O (PadicAlgCl l) a‖ < 1 := ts_norm_lt c.O.val
  let f : M.SS →ₐ[c.O] PadicAlgCl l := (TrivSqZeroExt.fstHom c.O _ _).comp ξ
  let N := ts_near hO M.SS (maximalIdeal M.S) f
  have hent : ∀ g i j, M.ru.hom g i j ∈ N.map M.SS.val := fun g i j => by
    refine ⟨M.ent g i j, ⟨D.r0 g i j, ?_, hξ g i j⟩, rfl⟩
    rw [← res_eq_zero_iff c.O, map_sub, AlgHom.commutes, sub_eq_zero]
    exact M.ru.red g i j
  have hN : ∀ x : M.SS, x ∈ N := fun x => by
    have h1 : (⨆ w, M.sPart w) ≤ (N.map M.SS.val).toSubmodule := by
      refine iSup_le fun w => ?_
      rw [hsp w, Submodule.span_le]
      rintro _ ⟨L, -, rfl⟩
      refine Subalgebra.list_prod_mem _ fun y hy => ?_
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy
      exact hent _ _ _
    obtain ⟨y, hy, hyx⟩ := h1 x.2
    rwa [← (Subtype.ext hyx : y = x)]
  have hle : WS.A ≤ M.SS := fun x hx => iSup_mono (fun w => (hWS w).le) hx
  have hge : M.SS ≤ WS.A := fun x hx => iSup_mono (fun w => (hWS w).ge) hx
  have hfg : (WS.part 0).FG := by
    haveI := hF M.S M.ru M.pt
    have h1 : (Algebra.adjoin c.O (mono M.ru.hom 0)).toSubmodule.FG := Module.Finite.iff_fg.1 this
    refine h1.of_le ?_
    rw [hWS, hsp, Submodule.span_le]
    exact Algebra.subset_adjoin
  obtain ⟨Ξ, hΞ⟩ := ts_ext WS (K := PadicAlgCl l) Subtype.val_injective
    (fun x hx => ((ts_intIff x).2 hx).tower_top) (ξ.comp (Subalgebra.inclusion hle))
    (fun x => by
      obtain ⟨a, -, ha⟩ := hN (Subalgebra.inclusion hle x)
      show ‖f (Subalgebra.inclusion hle x)‖ ≤ 1
      rw [← sub_add_cancel (f _) (algebraMap c.O _ a)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha.le (hO a)))
    (fun s => by
      obtain ⟨a, ha0, ha⟩ := hN (Subalgebra.inclusion hle (WS.zA s))
      have h1 : algebraMap c.O M.S a ∈ maximalIdeal M.S := by
        have := Ideal.sub_mem _ (hz s) ha0
        rwa [show WS.z s - (((Subalgebra.inclusion hle (WS.zA s) : M.SS) : M.S) - algebraMap c.O M.S a) =
          algebraMap c.O M.S a from sub_sub_cancel _ _] at this
      have h2 : a ∈ maximalIdeal c.O := fun hu => h1 (hu.map _)
      show ‖f (Subalgebra.inclusion hle (WS.zA s))‖ < 1
      rw [← sub_add_cancel (f _) (algebraMap c.O _ a)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha (hO' a h2)))
    (Submodule.FG.map _ (Submodule.fg_of_fg_map_injective WS.A.val.toLinearMap Subtype.val_injective (by
      refine hfg.of_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hx)))
  refine ⟨M.S, _, _, _, M.ru, Ξ, M.pt, ?_⟩
  ext1 g
  ext1 i j
  exact (hΞ ⟨_, hge (M.ent g i j).2⟩).symm
