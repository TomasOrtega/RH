import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.BaseChangeNorms.PropMHol
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Hypotheses4Z
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THolLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Base UpperTheory.V.Sd
section SlopeTestRemainingChoices
variable {l : ℕ} [Fact l.Prime]
/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)`.
-/
private theorem sm_add {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)
/- English proof (translation)
Rewrite using `[sub_eq_add_neg]; exact sm_add hx (by rwa [norm_neg])`.
-/
private theorem sm_sub {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]; exact sm_add hx (by rwa [norm_neg])
/- English proof (translation)
Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hx).trans_lt hy`.
-/
private theorem sm_mul {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ < 1) : ‖x * y‖ < 1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans_lt hy
/- English proof (translation)
Use `IsUltrametricDist.norm_add_le_max (x - y) y` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Conclude with `this.trans (max_le h.le hy)`.
-/
private theorem le_of_cong {x y : Qbar l} (h : ‖x - y‖ < 1) (hy : ‖y‖ ≤ 1) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - y) y
  rw [sub_add_cancel] at this
  exact this.trans (max_le h.le hy)
/- English proof (translation)
Use `le_antisymm (le_of_cong h hy.le) (not_lt.1 fun hx => ?_)` and prove the remaining obligations. Use `sm_sub hx h` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel, hy]`. Conclude with `lt_irrefl _ this`.
-/
private theorem eq_of_cong {x y : Qbar l} (h : ‖x - y‖ < 1) (hy : ‖y‖ = 1) : ‖x‖ = 1 := by
  refine le_antisymm (le_of_cong h hy.le) (not_lt.1 fun hx => ?_)
  have := sm_sub hx h
  rw [sub_sub_cancel, hy] at this
  exact lt_irrefl _ this
/- English proof (translation)
Establish `h1` using `eq_of_cong h norm_one`. Rewrite `h1` using `[norm_inv, inv_eq_one]`. Establish `h0 : x ≠ 0` using `by rintro rfl; simp at h1`. Use `sm_mul h1.le h` as an intermediate fact. Rewrite `this` using `[mul_sub, mul_inv_cancel₀ h0, mul_one, norm_sub_rev]`.

Conclude with `this`.
-/
private theorem inv_cong {x : Qbar l} (h : ‖x⁻¹ - 1‖ < 1) : ‖x - 1‖ < 1 := by
  have h1 := eq_of_cong h norm_one
  rw [norm_inv, inv_eq_one] at h1
  have h0 : x ≠ 0 := by rintro rfl; simp at h1
  have := sm_mul h1.le h
  rw [mul_sub, mul_inv_cancel₀ h0, mul_one, norm_sub_rev] at this
  exact this
/- English proof (translation)
Take `⟨m, rfl⟩` from `h`. Rewrite using `[Nat.cast_mul, mul_comm]`. Use `sm_mul (IsUltrametricDist.norm_natCast_le_one _ _) ?_` and prove the remaining obligations. Rewrite using `[← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]`. Conclude with `Padic.norm_p_lt_one`.
-/
private theorem norm_nat_lt {n : ℕ} (h : l ∣ n) : ‖(n : Qbar l)‖ < 1 := by
  obtain ⟨m, rfl⟩ := h
  rw [Nat.cast_mul, mul_comm]
  refine sm_mul (IsUltrametricDist.norm_natCast_le_one _ _) ?_
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one
/- English proof (translation)
Take `⟨m, rfl⟩` from `hk`. Establish `hp : l.Prime` using `Fact.out`. Establish `h1 : n ^ (l - 1) ≡ 1 [MOD l]`. Rewrite using `[← Nat.totient_prime hp]`. Conclude with `Nat.ModEq.pow_totient ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm`.

Establish `h2 : n ^ ((l - 1) * m) ≡ 1 [MOD l]`. Rewrite using `[pow_mul]`. Simplify using `using h1.pow m`. Establish `h0 : 1 ≤ n ^ ((l - 1) * m)` using `Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by rintro rfl; simp at h))`. Use `norm_nat_lt ((Nat.modEq_iff_dvd' h0).1 h2.symm)` as an intermediate fact.

Rewrite `this` using `[Nat.cast_sub h0, Nat.cast_pow, Nat.cast_one]`. Then use the resulting hypothesis.
-/
private theorem pow_cong {n k : ℕ} (h : ¬ l ∣ n) (hk : l - 1 ∣ k) : ‖(n : Qbar l) ^ k - 1‖ < 1 := by
  obtain ⟨m, rfl⟩ := hk
  have hp : l.Prime := Fact.out
  have h1 : n ^ (l - 1) ≡ 1 [MOD l] := by
    rw [← Nat.totient_prime hp]
    exact Nat.ModEq.pow_totient ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm
  have h2 : n ^ ((l - 1) * m) ≡ 1 [MOD l] := by
    rw [pow_mul]; simpa using h1.pow m
  have h0 : 1 ≤ n ^ ((l - 1) * m) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by rintro rfl; simp at h))
  have := norm_nat_lt ((Nat.modEq_iff_dvd' h0).1 h2.symm)
  rwa [Nat.cast_sub h0, Nat.cast_pow, Nat.cast_one] at this
variable {F : Type} [Field F] [NumberField F]
/- English proof (translation)
Use `w.isMaximal` as an intermediate fact. Use `letI := Ideal.Quotient.field w.asIdeal`. Establish `: Finite (𝓞 F ⧸ w.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot`. Use `letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)`. Rewrite using `[normV, Nat.card_eq_fintype_card, ← prime_dvd_char_iff_dvd_card, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]`.

Establish `hq : (ringChar (𝓞 F ⧸ w.asIdeal)).Prime` using `CharP.prime_ringChar _`. Rewrite using `[Nat.prime_dvd_prime_iff_eq Fact.out hq, Nat.prime_dvd_prime_iff_eq hq Fact.out, eq_comm]`.
-/
private theorem dvd_normV (w : Pl F) : l ∣ normV w ↔ ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  have : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  rw [normV, Nat.card_eq_fintype_card, ← prime_dvd_char_iff_dvd_card, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
    ringChar.spec]
  have hq : (ringChar (𝓞 F ⧸ w.asIdeal)).Prime := CharP.prime_ringChar _
  rw [Nat.prime_dvd_prime_iff_eq Fact.out hq, Nat.prime_dvd_prime_iff_eq hq Fact.out, eq_comm]
/- English proof (translation)
Take `⟨m, hm, e⟩` from `isOfFinOrder_iff_pow_eq_one.1 h`. Establish `e1 : η.1 x ^ m = 1` using `DFunLike.congr_fun (congrArg Subtype.val e) x`. Establish `e2 : ‖ι.symm (η.1 x : ℂˣ)‖ ^ m = 1`. Rewrite using `[← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, e1, Units.val_one, map_one, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e2`.
-/
private theorem norm_val (ι : Qbar l ≃+* ℂ) {η : HChar F} (h : IsOfFinOrder η) (x : Ideles F) :
    ‖ι.symm (η.1 x : ℂˣ)‖ = 1 := by
  obtain ⟨m, hm, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : η.1 x ^ m = 1 := DFunLike.congr_fun (congrArg Subtype.val e) x
  have e2 : ‖ι.symm (η.1 x : ℂˣ)‖ ^ m = 1 := by
    rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, e1, Units.val_one, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e2
/- English proof (translation)
Rewrite using `[chiI, finprod_eq_single _ w]`. Rewrite using `[ordI, Associates.count_self w.associates_irreducible, pow_one]`. Introduce `v hv`. Rewrite using `[ordI, Associates.count_eq_zero_of_ne v.associates_irreducible w.associates_irreducible, pow_zero]`. Introduce `e`.

Conclude with `hv (HeightOneSpectrum.ext (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 e)))`.
-/
private theorem chiI_prime (ω : HChar F) (c : Pl F → ℕ) (w : Pl F) :
    chiI ω c w.asIdeal = if c w = 0 then ((ω.val w : ℂˣ) : ℂ) else 0 := by
  classical
  rw [chiI, finprod_eq_single _ w]
  · rw [ordI, Associates.count_self w.associates_irreducible, pow_one]
  · intro v hv
    rw [ordI, Associates.count_eq_zero_of_ne v.associates_irreducible w.associates_irreducible, pow_zero]
    intro e
    exact hv (HeightOneSpectrum.ext (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 e)))
/- English proof (translation)
Take `⟨art, ha⟩` from `hA F (AlgebraicClosure F)`. Take `⟨m₁, hm₁, e₁⟩` from `isOfFinOrder_iff_pow_eq_one.1 h₁`. Take `⟨m₂, hm₂, e₂⟩` from `isOfFinOrder_iff_pow_eq_one.1 h₂`. Take `⟨δ₁, c₁, L₁⟩` from `ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η₁) hm₁ e₁)`. Take `⟨δ₂, c₂, L₂⟩` from `ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η₂) hm₂ e₂)`.

Establish `hcl : IsClosed ((fun σ => (δ₁ σ : Qbar l)) ⁻¹' Metric.ball 1 1 ∪ (fun σ => (δ₂ σ : Qbar l)) ⁻¹' Metric.ball 1 1)` using `((IsUltrametricDist.isClosed_ball _ _).preimage (Units.continuous_val.comp c₁)).union ((IsUltrametricDist.isClosed_ball _ _).preimage (Units.continuous_val.comp c₂))`. Take `⟨σ, hσ⟩` from `toAb_surjective (art x)`. Establish `hd` using `GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := AlgebraicClosure F) GlobalTheory.Published.chebotarevDegreeOne' hS`. Establish `hm` using `hcl.closure_subset_iff.2 ?_ (hd σ)`. Establish `f₁` using `L₁ x σ hσ.symm`.

Establish `f₂` using `L₂ x σ hσ.symm`. Rewrite `f₁`, `f₂` using `[infPow_zero, lPow_zero, inv_one, mul_one, mul_one]`. Simplify `hm` using `only [Set.mem_union, Set.mem_preimage, mem_ball_iff_norm, f₁, f₂]`. Introduce and unpack `τ ⟨v, hv, -, B, hB, hτ⟩`. Take `⟨u₁, u₂, hh⟩` from `h v hv`.

Simplify using `only [Set.mem_union, Set.mem_preimage, mem_ball_iff_norm, L₁.frob_unr ha (Or.inr rfl) u₁ hB hτ, L₂.frob_unr ha (Or.inr rfl) u₂ hB hτ]`. Conclude with `hh.imp (fun t => inv_cong (by rwa [inv_inv])) fun t => inv_cong (by rwa [inv_inv])`.
-/
private theorem gal_of (hA : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {η₁ η₂ : HChar F} (h₁ : IsOfFinOrder η₁)
    (h₂ : IsOfFinOrder η₂) {S : Set (Pl F)} (hS : S.Finite)
    (h : ∀ w ∉ S, η₁.UnrAt w ∧ η₂.UnrAt w ∧ (‖ι.symm (η₁.val w : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.val w : ℂˣ) - 1‖ < 1))
    (x : Ideles F) : ‖ι.symm (η₁.1 x : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.1 x : ℂˣ) - 1‖ < 1 := by
  obtain ⟨art, ha⟩ := hA F (AlgebraicClosure F)
  obtain ⟨m₁, hm₁, e₁⟩ := isOfFinOrder_iff_pow_eq_one.1 h₁
  obtain ⟨m₂, hm₂, e₂⟩ := isOfFinOrder_iff_pow_eq_one.1 h₂
  obtain ⟨δ₁, c₁, L₁⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η₁) hm₁ e₁)
  obtain ⟨δ₂, c₂, L₂⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η₂) hm₂ e₂)
  have hcl : IsClosed ((fun σ => (δ₁ σ : Qbar l)) ⁻¹' Metric.ball 1 1 ∪ (fun σ => (δ₂ σ : Qbar l)) ⁻¹' Metric.ball 1 1) :=
    ((IsUltrametricDist.isClosed_ball _ _).preimage (Units.continuous_val.comp c₁)).union
      ((IsUltrametricDist.isClosed_ball _ _).preimage (Units.continuous_val.comp c₂))
  obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
  have hd := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := AlgebraicClosure F) GlobalTheory.Published.chebotarevDegreeOne' hS
  have hm := hcl.closure_subset_iff.2 ?_ (hd σ)
  · have f₁ := L₁ x σ hσ.symm
    have f₂ := L₂ x σ hσ.symm
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one] at f₁ f₂
    simpa only [Set.mem_union, Set.mem_preimage, mem_ball_iff_norm, f₁, f₂] using hm
  · rintro τ ⟨v, hv, -, B, hB, hτ⟩
    obtain ⟨u₁, u₂, hh⟩ := h v hv
    simp only [Set.mem_union, Set.mem_preimage, mem_ball_iff_norm, L₁.frob_unr ha (Or.inr rfl) u₁ hB hτ,
      L₂.frob_unr ha (Or.inr rfl) u₂ hB hτ]
    exact hh.imp (fun t => inv_cong (by rwa [inv_inv])) fun t => inv_cong (by rwa [inv_inv])
end SlopeTestRemainingChoices
/- English proof (translation)
Introduce `PP F _ _ _ l _ hl ι ω c hω hodd hc hne hcl P hP hQ B`. Establish `hp : l.Prime` using `Fact.out`. Take `⟨v, hvP, hvl, hv⟩` from `hP`. Take `⟨v', hvQ, hvl', hv'⟩` from `hQ`. Take `⟨φ, a, hφ, eφ, a1, aint, aeig⟩` from `emix PP.eis F l ι ω c hω hodd hc hne hcl P ⟨v, hvP, hvl⟩`.

Establish `hl1 : 0 < l - 1` using `Nat.sub_pos_of_lt hp.one_lt`. Take `⟨k, hkB, hk0, hkd', ψ, d₀, b, hψ, eψ, hd, hb⟩` from `PP.one F l hl ι B`. Take `⟨χ, a', hχ, eχ, ha'⟩` from `holMul F l ι 1 k (levL l c) ω hω φ ψ a d₀ b hφ hψ eφ eψ aint hd hb`. Rewrite `hχ`, `eχ` using `[add_comm 1 k]`. Simplify using `only [map_sub] at ha'`.

Establish `hfin : {w | levL l c w ≠ 0}.Finite`. Establish `h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0`. Simplify `hp.ne_zero` using `[Ideal.span_singleton_eq_bot]`. Use `((Ideal.finite_factors h0).union (GlobalTheory.Mem.UnrAe.unr_ae_and_level F ω).1).subset fun w hw => ?_` and prove the remaining obligations. Distinguish the cases in `h : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal`.

Conclude with `Or.inl (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h))`. Use `Or.inr fun hu => hw ?_` and prove the remaining obligations. Rewrite using `[levL, if_neg h]`. Conclude with `Nat.le_zero.1 ((hc w).2 fun x hx _ => hu x hx)`. Establish `hL0 : ∀ w, levL l c w = 0 → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal ∧ c w = 0` using `fun w hw => by`.

Distinguish the cases in `h : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal`. Rewrite `hw` using `[levL, if_pos h]`. Conclude with `absurd hw one_ne_zero`. Rewrite `hw` using `[levL, if_neg h]`. Conclude with `⟨h, hw⟩`.

Establish `nval : ∀ {η : HChar F}, IsOfFinOrder η → ∀ w, ‖ι.symm (η.val w : ℂˣ)‖ = 1` using `fun h w => norm_val ι h _`. Establish `hpow : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖(normV w : Qbar l) ^ k - 1‖ < 1` using `fun w hw => pow_cong (mt (dvd_normV w).1 hw) hkd'`. Establish `ht : ∀ w, ‖ι.symm (eisT l ω c P w)‖ ≤ 1` using `fun w => by`. Rewrite using `[eisT]`. Use `split_ifs`.

Conclude with `(nval hω w).le`. Simplify using the standard rewrite rules. Rewrite using `[map_add, map_one]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le norm_one.le (nval hω w).le)`. Simplify using the standard rewrite rules.

Take `⟨g, lam, hg, hlam⟩` from `_root_.UpperTheory.V.Sd.holLift_alt PP.h F l ι (k + 1) (Nat.le_add_left _ _) (levL l c) hfin ω hω χ 0 a' (eisT l ω c P) hχ eχ (fun 𝔪 h => le_of_cong (ha' 𝔪 h) (aint 𝔪 h)) (eq_of_cong (ha' ⊤ top_ne_bot) (by rw [a1, map_one, norm_one])) ht (fun w 𝔪 h𝔪 => by`. Establish `e` using `aeig w 𝔪 h𝔪`. Establish `h1` using `ha' _ (mul_ne_zero w.ne_bot h𝔪)`. Establish `h2` using `sm_mul (ht w) (ha' 𝔪 h𝔪)`. Establish `h3 : ‖ι.symm (coefDiv a w.asIdeal 𝔪)‖ ≤ 1 ∧ ‖ι.symm (coefDiv a' w.asIdeal 𝔪) - ι.symm (coefDiv a w.asIdeal 𝔪)‖ < 1`.

Unfold `coefDiv`. Use `split_ifs with h`. Establish `h0 : h.choose ≠ ⊥` using `fun h0 => h𝔪 (by rw [h.choose_spec, h0, Ideal.mul_bot])`. Conclude with `⟨aint _ h0, ha' _ h0⟩`. Simplify using the standard rewrite rules.

Rewrite `e` using `[hkCoef, chiI_prime, Nat.sub_self, pow_zero, mul_one]`. Establish `e'` using `congrArg ι.symm e`. Rewrite using `[hkCoef, chiI_prime, Nat.add_sub_cancel]`. Use `split_ifs at e' ⊢ with h0`. Establish `h4` using `sm_mul (nval hω w).le (sm_add (sm_mul (le_of_cong (hpow w (hL0 w h0).1) norm_one.le) h3.2) (sm_mul h3.1 (hpow w (hL0 w h0).1)))`.

Use `sm_add (sm_sub h1 h2) h4 using 2` and compare the differences between its conclusion and the goal. Simplify using `only [map_add, map_sub, map_mul, map_pow, map_natCast] at e' ⊢`. Take the linear combination `e'`. Use `sm_sub h1 h2 using 2` and compare the differences between its conclusion and the goal. Simplify using `only [map_add, map_sub, map_mul, map_pow, map_natCast, map_zero] at e' ⊢`.

Take the linear combination `e')`. Use `⟨k, hkB, hkd', g, lam, hg, ?_, hlam⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcusp`. Take `⟨η₁, η₂, f₁, f₂, rfl, hu, hr⟩` from `holEis F (k + 1) (Nat.le_add_left _ _) (levL l c) hfin ω hω g lam hg hcusp`. Simplify using `only [map_sub, Nat.add_sub_cancel] at hlam hu hr`.

Establish `key` using `gal_of PP.h.litN.aut.art ι f₁ f₂ hfin fun w hw => by`. Establish `h0 : levL l c w = 0` using `not_not.1 hw`. Take `⟨u₁, u₂, e⟩` from `hu w h0`. Use `⟨u₁, u₂, ?_⟩` and prove the remaining obligations. Establish `h1` using `hlam w`.

Rewrite `h1` using `[e, eisT, if_neg (hL0 w h0).1, if_pos (hL0 w h0).2, HChar.val_mul]`. Establish `h2` using `sm_sub (sm_mul (nval f₂ w).le (hpow w (hL0 w h0).1)) h1`. Establish `h3 : ‖ι.symm (η₁.val w : ℂˣ) - 1‖ * ‖ι.symm (η₂.val w : ℂˣ) - 1‖ < 1`. Rewrite using `[← norm_mul]`. Use `h2 using 2` and compare the differences between its conclusion and the goal.

Simplify using `only [map_add, map_mul, map_pow, map_natCast, map_one, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_or, not_lt, not_lt]`. Conclude with `h3.not_ge (one_le_mul_of_one_le_of_one_le hn.1 hn.2)`.

Establish `hab : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ‖ι.symm (eisT l (η₁ * η₂) c P w)‖ = 1 → ‖ι.symm (η₁.val w : ℂˣ) - ι.symm (eisT l (η₁ * η₂) c P w)‖ < 1` using `fun w hw h1 => by`. Establish `h2` using `eq_of_cong (hlam w) h1`. Break down `hr w (fun h0 => (hL0 w h0).1 hw) with e | ⟨-, e⟩ | ⟨-, e⟩` into its components or cases. Simplify using `[e] at h2`. Conclude with `e ▸ hlam w`.

Rewrite `h2` using `[e, map_mul, map_pow, map_natCast, ← Nat.cast_pow]`. Conclude with `absurd h2 (sm_mul (nval f₂ w).le (norm_nat_lt (dvd_pow ((dvd_normV w).2 hw) hk0.ne'))).ne`. Establish `e₁ : eisT l (η₁ * η₂) c P v = ((η₁ * η₂).val v : ℂˣ)` using `by rw [eisT, if_pos hvl, if_pos hvP]`. Establish `e₂ : eisT l (η₁ * η₂) c P v' = 1` using `by rw [eisT, if_pos hvl', if_neg hvQ]`. Establish `a₁` using `hab v hvl (by rw [e₁]; exact nval hω v)`.

Establish `a₂` using `hab v' hvl' (by rw [e₂, map_one, norm_one])`. Rewrite `a₁` using `[e₁]`. Rewrite `a₂` using `[e₂, map_one]`. Establish `kk : ‖ι.symm (η₁.val v * η₁.val v' : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.val v * η₂.val v' : ℂˣ) - 1‖ < 1`. Use `key (localIdele F v (atFin v (unif v)) * localIdele F v' (atFin v' (unif v')))` as an intermediate fact.

Rewrite `this` using `[map_mul η₁.1, map_mul η₂.1]`. Conclude with `this`. Simplify using `only [HChar.val_mul, Units.val_mul, map_mul] at kk a₁ hv hv'`. Establish `n₁` using `nval f₁ v`. Establish `n₂` using `nval f₂ v`.

Establish `n₃` using `nval f₁ v'`. Establish `n₄` using `nval f₂ v'`. Generalize the expression as in `ι.symm (η₁.val v : ℂˣ) = x at *`. Generalize the expression as in `ι.symm (η₂.val v : ℂˣ) = y at *`. Generalize the expression as in `ι.symm (η₁.val v' : ℂˣ) = x' at *`.

Generalize the expression as in `ι.symm (η₂.val v' : ℂˣ) = y' at *`. Establish `hy : ‖y - 1‖ < 1`. Rewrite `a₁` using `[← mul_one_sub, norm_mul, n₁, one_mul, norm_sub_rev]`. Then use the resulting hypothesis. Break down `kk with h | h` into its components or cases. Use `hv ?_` and prove the remaining obligations.

Use `sm_sub (sm_sub h (sm_mul n₁.le a₂)) a₁ using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `hv' ?_` and prove the remaining obligations. Use `sm_add (sm_sub h (sm_mul n₄.le hy)) (sm_mul n₄.le a₂) using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.Bc.propMHolZ_alt :
    _root_.UpperTheory.V.Z.Bc.Hypotheses4Z' → UpperTheory.V.Sd.PropMHol := by
  intro PP F _ _ _ l _ hl ι ω c hω hodd hc hne hcl P hP hQ B
  have hp : l.Prime := Fact.out
  obtain ⟨v, hvP, hvl, hv⟩ := hP
  obtain ⟨v', hvQ, hvl', hv'⟩ := hQ
  obtain ⟨φ, a, hφ, eφ, a1, aint, aeig⟩ := emix PP.eis F l ι ω c hω hodd hc hne hcl P ⟨v, hvP, hvl⟩
  have hl1 : 0 < l - 1 := Nat.sub_pos_of_lt hp.one_lt
  obtain ⟨k, hkB, hk0, hkd', ψ, d₀, b, hψ, eψ, hd, hb⟩ := PP.one F l hl ι B
  obtain ⟨χ, a', hχ, eχ, ha'⟩ := holMul F l ι 1 k (levL l c) ω hω φ ψ a d₀ b hφ hψ eφ eψ aint hd hb
  rw [add_comm 1 k] at hχ eχ
  simp only [map_sub] at ha'
  have hfin : {w | levL l c w ≠ 0}.Finite := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
    refine ((Ideal.finite_factors h0).union (GlobalTheory.Mem.UnrAe.unr_ae_and_level F ω).1).subset fun w hw => ?_
    by_cases h : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · exact Or.inl (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h))
    · refine Or.inr fun hu => hw ?_
      rw [levL, if_neg h]
      exact Nat.le_zero.1 ((hc w).2 fun x hx _ => hu x hx)
  have hL0 : ∀ w, levL l c w = 0 → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal ∧ c w = 0 := fun w hw => by
    by_cases h : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · rw [levL, if_pos h] at hw; exact absurd hw one_ne_zero
    · rw [levL, if_neg h] at hw; exact ⟨h, hw⟩
  have nval : ∀ {η : HChar F}, IsOfFinOrder η → ∀ w, ‖ι.symm (η.val w : ℂˣ)‖ = 1 := fun h w => norm_val ι h _
  have hpow : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖(normV w : Qbar l) ^ k - 1‖ < 1 := fun w hw =>
    pow_cong (mt (dvd_normV w).1 hw) hkd'
  have ht : ∀ w, ‖ι.symm (eisT l ω c P w)‖ ≤ 1 := fun w => by
    rw [eisT]
    split_ifs
    · exact (nval hω w).le
    · simp
    · rw [map_add, map_one]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le norm_one.le (nval hω w).le)
    · simp
  obtain ⟨g, lam, hg, hlam⟩ := _root_.UpperTheory.V.Sd.holLift_alt PP.h F l ι (k + 1) (Nat.le_add_left _ _) (levL l c) hfin ω hω χ 0 a'
    (eisT l ω c P) hχ eχ (fun 𝔪 h => le_of_cong (ha' 𝔪 h) (aint 𝔪 h))
    (eq_of_cong (ha' ⊤ top_ne_bot) (by rw [a1, map_one, norm_one])) ht (fun w 𝔪 h𝔪 => by
      have e := aeig w 𝔪 h𝔪
      have h1 := ha' _ (mul_ne_zero w.ne_bot h𝔪)
      have h2 := sm_mul (ht w) (ha' 𝔪 h𝔪)
      have h3 : ‖ι.symm (coefDiv a w.asIdeal 𝔪)‖ ≤ 1 ∧
          ‖ι.symm (coefDiv a' w.asIdeal 𝔪) - ι.symm (coefDiv a w.asIdeal 𝔪)‖ < 1 := by
        unfold coefDiv
        split_ifs with h
        · have h0 : h.choose ≠ ⊥ := fun h0 => h𝔪 (by rw [h.choose_spec, h0, Ideal.mul_bot])
          exact ⟨aint _ h0, ha' _ h0⟩
        · simp
      rw [hkCoef, chiI_prime, Nat.sub_self, pow_zero, mul_one] at e
      have e' := congrArg ι.symm e
      rw [hkCoef, chiI_prime, Nat.add_sub_cancel]
      split_ifs at e' ⊢ with h0
      · have h4 := sm_mul (nval hω w).le (sm_add (sm_mul (le_of_cong (hpow w (hL0 w h0).1) norm_one.le) h3.2)
          (sm_mul h3.1 (hpow w (hL0 w h0).1)))
        convert sm_add (sm_sub h1 h2) h4 using 2
        simp only [map_add, map_sub, map_mul, map_pow, map_natCast] at e' ⊢
        linear_combination e'
      · convert sm_sub h1 h2 using 2
        simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_zero] at e' ⊢
        linear_combination e')
  refine ⟨k, hkB, hkd', g, lam, hg, ?_, hlam⟩
  by_contra hcusp
  obtain ⟨η₁, η₂, f₁, f₂, rfl, hu, hr⟩ := holEis F (k + 1) (Nat.le_add_left _ _) (levL l c) hfin ω hω g lam hg hcusp
  simp only [map_sub, Nat.add_sub_cancel] at hlam hu hr
  have key := gal_of PP.h.litN.aut.art ι f₁ f₂ hfin fun w hw => by
    have h0 : levL l c w = 0 := not_not.1 hw
    obtain ⟨u₁, u₂, e⟩ := hu w h0
    refine ⟨u₁, u₂, ?_⟩
    have h1 := hlam w
    rw [e, eisT, if_neg (hL0 w h0).1, if_pos (hL0 w h0).2, HChar.val_mul] at h1
    have h2 := sm_sub (sm_mul (nval f₂ w).le (hpow w (hL0 w h0).1)) h1
    have h3 : ‖ι.symm (η₁.val w : ℂˣ) - 1‖ * ‖ι.symm (η₂.val w : ℂˣ) - 1‖ < 1 := by
      rw [← norm_mul]
      convert h2 using 2
      simp only [map_add, map_mul, map_pow, map_natCast, map_one, Units.val_mul]
      ring
    by_contra hn
    rw [not_or, not_lt, not_lt] at hn
    exact h3.not_ge (one_le_mul_of_one_le_of_one_le hn.1 hn.2)
  have hab : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ‖ι.symm (eisT l (η₁ * η₂) c P w)‖ = 1 →
      ‖ι.symm (η₁.val w : ℂˣ) - ι.symm (eisT l (η₁ * η₂) c P w)‖ < 1 := fun w hw h1 => by
    have h2 := eq_of_cong (hlam w) h1
    rcases hr w (fun h0 => (hL0 w h0).1 hw) with e | ⟨-, e⟩ | ⟨-, e⟩
    · simp [e] at h2
    · exact e ▸ hlam w
    · rw [e, map_mul, map_pow, map_natCast, ← Nat.cast_pow] at h2
      exact absurd h2 (sm_mul (nval f₂ w).le (norm_nat_lt (dvd_pow ((dvd_normV w).2 hw) hk0.ne'))).ne
  have e₁ : eisT l (η₁ * η₂) c P v = ((η₁ * η₂).val v : ℂˣ) := by rw [eisT, if_pos hvl, if_pos hvP]
  have e₂ : eisT l (η₁ * η₂) c P v' = 1 := by rw [eisT, if_pos hvl', if_neg hvQ]
  have a₁ := hab v hvl (by rw [e₁]; exact nval hω v)
  have a₂ := hab v' hvl' (by rw [e₂, map_one, norm_one])
  rw [e₁] at a₁
  rw [e₂, map_one] at a₂
  have kk : ‖ι.symm (η₁.val v * η₁.val v' : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.val v * η₂.val v' : ℂˣ) - 1‖ < 1 := by
    have := key (localIdele F v (atFin v (unif v)) * localIdele F v' (atFin v' (unif v')))
    rw [map_mul η₁.1, map_mul η₂.1] at this
    exact this
  simp only [HChar.val_mul, Units.val_mul, map_mul] at kk a₁ hv hv'
  have n₁ := nval f₁ v
  have n₂ := nval f₂ v
  have n₃ := nval f₁ v'
  have n₄ := nval f₂ v'
  generalize ι.symm (η₁.val v : ℂˣ) = x at *
  generalize ι.symm (η₂.val v : ℂˣ) = y at *
  generalize ι.symm (η₁.val v' : ℂˣ) = x' at *
  generalize ι.symm (η₂.val v' : ℂˣ) = y' at *
  have hy : ‖y - 1‖ < 1 := by
    rwa [← mul_one_sub, norm_mul, n₁, one_mul, norm_sub_rev] at a₁
  rcases kk with h | h
  · refine hv ?_
    convert sm_sub (sm_sub h (sm_mul n₁.le a₂)) a₁ using 2
    ring
  · refine hv' ?_
    convert sm_add (sm_sub h (sm_mul n₄.le hy)) (sm_mul n₄.le a₂) using 2
    ring
end
