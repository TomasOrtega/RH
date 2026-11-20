import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.BaseChangeNorms.Hypotheses4Z
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.NotDvdMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolEis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

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
