import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KronRatio

open GlobalTheory.KroneckerCongruence

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `h : IsIntegral V x` using `hx.tower_top`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := V) (K := Ω)).1 h`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem mem_of_isIntegral_int (V : ValuationSubring Ω) {x : Ω} (hx : IsIntegral ℤ x) : x ∈ V := by
  have h : IsIntegral V x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := Ω)).1 h
  rw [← hy]; exact y.2

/- English proof (translation)
Establish `hcop : IsCoprime (q : ℤ) (D : ℤ)`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hq).2 hD`. Take `⟨a, b, hab⟩` from `hcop`. Establish `hle : ∀ n : ℤ, V.valuation (n : Ω) ≤ 1` using `fun n => (V.valuation_le_one_iff _).2 (intCast_mem V n)`.

Establish `hq1 : V.valuation (q : Ω) < 1` using `V.mem_nonunits_iff.1 hqV`. Assume the negation of the conclusion as `hne`. Establish `hD1 : V.valuation (D : Ω) < 1` using `lt_of_le_of_ne ((V.valuation_le_one_iff _).2 (natCast_mem V D)) hne`. Establish `h1 : (1 : Ω) = (a : Ω) * (q : Ω) + (b : Ω) * (D : Ω)`. Use `congrArg (fun z : ℤ => (z : Ω)) hab` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this.symm`. Establish `h2 : V.valuation (1 : Ω) < 1`. Rewrite using `[h1]`. Use `lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)` and prove the remaining obligations.

Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hle a)) hq1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hle b)) hD1`. Simplify using `at h2`.
-/
theorem valuation_natCast_eq_one (V : ValuationSubring Ω) {q D : ℕ} (hq : q.Prime)
    (hqV : ((q : ℕ) : Ω) ∈ V.nonunits) (hD : ¬ q ∣ D) : V.valuation (D : Ω) = 1 := by
  have hcop : IsCoprime (q : ℤ) (D : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hq).2 hD
  obtain ⟨a, b, hab⟩ := hcop
  have hle : ∀ n : ℤ, V.valuation (n : Ω) ≤ 1 := fun n => (V.valuation_le_one_iff _).2 (intCast_mem V n)
  have hq1 : V.valuation (q : Ω) < 1 := V.mem_nonunits_iff.1 hqV
  by_contra hne
  have hD1 : V.valuation (D : Ω) < 1 := lt_of_le_of_ne ((V.valuation_le_one_iff _).2 (natCast_mem V D)) hne
  have h1 : (1 : Ω) = (a : Ω) * (q : Ω) + (b : Ω) * (D : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hab
    push_cast at this
    exact this.symm
  have h2 : V.valuation (1 : Ω) < 1 := by
    rw [h1]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle a)) hq1
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle b)) hD1
  simp at h2

/- English proof (translation)
Take `⟨k, hk⟩` from `h`. Establish `h1` using `mem_of_isIntegral_int V hk`. Establish `hv` using `valuation_natCast_eq_one V hq hqV hD`. Rewrite `h1`, the goal using `[← V.valuation_le_one_iff]`. Rewrite `h1` using `[map_mul, map_pow, hv, one_pow, one_mul]`. Then use the resulting hypothesis.
-/
theorem mem_of_bdd (V : ValuationSubring Ω) {q D : ℕ} (hq : q.Prime) (hqV : ((q : ℕ) : Ω) ∈ V.nonunits)
    (hD : ¬ q ∣ D) {a : Ω} (h : ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * a)) : a ∈ V := by
  obtain ⟨k, hk⟩ := h
  have h1 := mem_of_isIntegral_int V hk
  have hv := valuation_natCast_eq_one V hq hqV hD
  rw [← V.valuation_le_one_iff] at h1 ⊢
  rwa [map_mul, map_pow, hv, one_pow, one_mul] at h1

/- English proof (translation)
Establish `he : x * y = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx * liftV V y hy)`. Rewrite using `[map_mul, map_liftV, map_liftV]`. Rewrite using `[he, hahnSeriesCoeffRingHomMap_coeff]`. Conclude with `(_ : V).2`.
-/
theorem coeff_mul_mem (V : ValuationSubring Ω) (x y : HahnSeries ℚ Ω) (hx : ∀ r, x.coeff r ∈ V)
    (hy : ∀ r, y.coeff r ∈ V) (r : ℚ) : (x * y).coeff r ∈ V := by
  have he : x * y = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx * liftV V y hy) := by
    rw [map_mul, map_liftV, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff]; exact (_ : V).2

/- English proof (translation)
Establish `he : x ^ n = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx ^ n)`. Rewrite using `[map_pow, map_liftV]`. Rewrite using `[he, hahnSeriesCoeffRingHomMap_coeff]`. Conclude with `(_ : V).2`.
-/
theorem coeff_pow_mem (V : ValuationSubring Ω) (x : HahnSeries ℚ Ω) (hx : ∀ r, x.coeff r ∈ V) (n : ℕ)
    (r : ℚ) : (x ^ n).coeff r ∈ V := by
  have he : x ^ n = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx ^ n) := by
    rw [map_pow, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff]; exact (_ : V).2

/- English proof (translation)
Establish `hx' : ∀ r, x.coeff r ∈ V` using `fun r => (V.valuation_le_one_iff _).1 (le_of_lt (V.mem_nonunits_iff.1 (hx r)))`. Use `set ρ := IsLocalRing.residue V with hρ_def`. Establish `hρ0 : ∀ z : V, ρ z = 0 ↔ V.valuation (z : Ω) < 1` using `fun z => by`. Rewrite using `[hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]`. Establish `hX : hahnSeriesCoeffRingHomMap ρ (liftV V x hx') = 0`.

Use extensionality with `t`. Rewrite using `[hahnSeriesCoeffRingHomMap_coeff]`. Conclude with `(hρ0 _).2 (V.mem_nonunits_iff.1 (hx t))`. Establish `he : x * y = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx' * liftV V y hy)`. Rewrite using `[map_mul, map_liftV, map_liftV]`.

Rewrite using `[he, hahnSeriesCoeffRingHomMap_coeff, ValuationSubring.mem_nonunits_iff]`. Use `(hρ0 ((liftV V x hx' * liftV V y hy).coeff r)).1 ?_` and prove the remaining obligations. Rewrite using `[← hahnSeriesCoeffRingHomMap_coeff, map_mul, hX, zero_mul]`. Both sides reduce to the same expression.
-/
theorem coeff_mul_mem_nonunits (V : ValuationSubring Ω) (x y : HahnSeries ℚ Ω)
    (hx : ∀ r, x.coeff r ∈ V.nonunits) (hy : ∀ r, y.coeff r ∈ V) (r : ℚ) : (x * y).coeff r ∈ V.nonunits := by
  have hx' : ∀ r, x.coeff r ∈ V := fun r =>
    (V.valuation_le_one_iff _).1 (le_of_lt (V.mem_nonunits_iff.1 (hx r)))
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ z : V, ρ z = 0 ↔ V.valuation (z : Ω) < 1 := fun z => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  have hX : hahnSeriesCoeffRingHomMap ρ (liftV V x hx') = 0 := by
    ext t
    rw [hahnSeriesCoeffRingHomMap_coeff]
    exact (hρ0 _).2 (V.mem_nonunits_iff.1 (hx t))
  have he : x * y = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx' * liftV V y hy) := by
    rw [map_mul, map_liftV, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff, ValuationSubring.mem_nonunits_iff]
  refine (hρ0 ((liftV V x hx' * liftV V y hy).coeff r)).1 ?_
  rw [← hahnSeriesCoeffRingHomMap_coeff, map_mul, hX, zero_mul]
  rfl

end GlobalTheory.KronRatio

namespace GlobalTheory.KZ

open GlobalTheory.KroneckerCongruence GlobalTheory.KronRatio in

/- English proof (translation)
Introduce `Ω _ _ _ ε X hε hj M f hM hf`. Use `haveI : NeZero M := ⟨hM.ne'⟩`. Set `red : SL(2, ℤ) →* SL(2, ZMod M)` to `Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))`. Set `F : SL(2, ZMod M) → X.K` to `fun τ => if h : ∃ σ, red σ = τ then X.sl (ofSL h.choose) (f : X.K) else (f : X.K)`. Establish `hF : ∀ σ : SL(2, ℤ), X.sl (ofSL σ) (f : X.K) = F (red σ)`.

Introduce `σ`. Establish `h : ∃ σ', red σ' = red σ` using `⟨σ, rfl⟩`. Establish `e : F (red σ) = X.sl (ofSL h.choose) (f : X.K)` using `dif_pos h`. Establish `hσ' : red h.choose = red σ` using `h.choose_spec`. Establish `hγ : σ * h.choose⁻¹ ∈ CongruenceSubgroup.Gamma M`.

Establish `: σ * h.choose⁻¹ ∈ red.ker`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, hσ', mul_inv_cancel]`. Conclude with `this`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[inv_mul_cancel_right]`. Use `_ = X.sl (ofSL h.choose) (X.sl (ofSL (σ * h.choose⁻¹)) (f : X.K)) := by rw [map_mul, X.sl_mul]`. Use `_ = _ := by rw [hf _ hγ]`. Use `choose D hD0 hD using X.bdd`. Set `P : X.K → Finset ℕ` to `fun g => (D g).primeFactors ∪ (D g⁻¹).primeFactors`.

Use `⟨M.primeFactors ∪ P f ∪ Finset.univ.biUnion (fun τ => P (F τ)), ?_⟩` and prove the remaining obligations. Introduce `q hq hqS V s hqV hs σ hσ W hW hdom`. Establish `hn : ∀ h : X.K, q ∉ (D h).primeFactors → ∀ r, (X.exp h).coeff r ∈ V` using `fun h hh r => mem_of_bdd V hq hqV (fun hd => hh (Nat.mem_primeFactors.2 ⟨hq, hd, (hD0 h).ne'⟩)) (hD h r)`. Establish `hint : ∀ g : X.K, q ∉ P g → (∀ r, (X.exp g).coeff r ∈ V) ∧ (∀ r, (X.exp g⁻¹).coeff r ∈ V)` using `fun g hg => ⟨hn g fun h => hg (Finset.mem_union_left _ h), hn _ fun h => hg (Finset.mem_union_right _ h)⟩`. Establish `hqM : q ∉ M.primeFactors` using `fun h => hqS (Finset.mem_union_left _ (Finset.mem_union_left _ h))`.

Establish `hqf : q ∉ P f` using `fun h => hqS (Finset.mem_union_left _ (Finset.mem_union_right _ h))`. Establish `hqF : q ∉ P (F (red σ))` using `fun h => hqS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩))`. Take `⟨hf1, hf2⟩` from `hint _ hqf`. Rewrite `hqF` using `[← hF σ]`. Take `⟨hs1, hs2⟩` from `hint _ hqF`.

Establish `hcop : Nat.Coprime q M` using `(Nat.Prime.coprime_iff_not_dvd hq).2 fun hd => hqM (Nat.mem_primeFactors.2 ⟨hq, hd, hM.ne'⟩)`. Establish `hK` using `kronecker_congruence_tower ε X hε hj M q (f : X.K) hM hq hcop hf σ ⟨hσ.2.1, hσ.2.2⟩ V s hqV hs hf1 hs1`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Generalize the expression as in `(∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = A at hK ⊢`. Establish `hB0 : X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q ≠ 0` using `mul_ne_zero ((map_ne_zero _).2 f.ne_zero) (pow_ne_zero _ ((map_ne_zero _).2 ((map_ne_zero _).2 f.ne_zero)))`.

Establish `hBinv : ∀ r, (X.exp (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q)⁻¹).coeff r ∈ V`. Introduce `r`. Rewrite using `[mul_inv, ← inv_pow, ← map_inv₀, ← map_inv₀ (X.gal s.symm), map_mul, map_pow]`. Use `coeff_mul_mem V _ _ (fun t => ?_) (coeff_pow_mem V _ (fun t => ?_) q) r` and prove the remaining obligations. Rewrite using `[X.gal_exp]`.

Conclude with `(hs _ (hf2 t)).1`. Rewrite using `[X.gal_exp]`. Conclude with `(hs _ (hs2 t)).2.1`. Generalize the expression as in `X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q = B at hK hB0 hBinv ⊢`. Establish `hge : algebraMap Ω X.K 1 * A / B - 1 = (A - B) * B⁻¹`.

Rewrite using `[map_one, one_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hge]`. Establish `hgc : ∀ r, (X.exp ((A - B) * B⁻¹)).coeff r ∈ V.nonunits`. Introduce `r`.

Rewrite using `[map_mul]`. Conclude with `coeff_mul_mem_nonunits V _ _ hK hBinv r`. Generalize the expression as in `(A - B) * B⁻¹ = g at hgc ⊢`. Establish `hgV : ∀ r, (X.exp g).coeff r ∈ V` using `fun r => (V.valuation_le_one_iff _).1 (le_of_lt (V.mem_nonunits_iff.1 (hgc r)))`. Establish `h1` using `hdom g hgV fun r _ => hgc r`.

Establish `hcV` using `V.mem_nonunits_iff.1 (hgc 0)`. Establish `hcm` using `hgV 0`. Generalize the expression as in `(X.exp g).coeff 0 = c at h1 hcV hcm`. Establish `h2 : W.valuation (algebraMap Ω X.K c) < 1`. Distinguish the cases in `hc0 : c = 0`.

Rewrite using `[hc0, map_zero, map_zero]`. Conclude with `zero_lt_one`. Use `lt_of_le_of_ne ((W.valuation_le_one_iff _).2 ((hW c).2 hcm)) fun heq => ?_` and prove the remaining obligations. Establish `hinv : algebraMap Ω X.K c⁻¹ ∈ W`. Rewrite using `[← W.valuation_le_one_iff, map_inv₀, map_inv₀, heq, inv_one]`.

Establish `h3 : V.valuation c⁻¹ ≤ 1` using `(V.valuation_le_one_iff _).2 ((hW _).1 hinv)`. Establish `h4 : V.valuation (c⁻¹ * c) < 1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' h3) hcV`. Rewrite `h4` using `[inv_mul_cancel₀ hc0, map_one]`.

Conclude with `lt_irrefl _ h4`. Establish `h5` using `lt_of_le_of_lt (W.valuation.map_add _ _) (max_lt h1 h2)`. Rewrite `h5` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem kronecker_ratio_reduces_to_const : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (M : ℕ) (f : X.Kˣ), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), ((q : ℕ) : Ω) ∈ V.nonunits → (∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1) → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ W : ValuationSubring X.K, (∀ a : Ω, algebraMap Ω X.K a ∈ W ↔ a ∈ V) → (∀ g : X.K, (∀ r, (X.exp g).coeff r ∈ V) → (∀ r, r ≠ 0 → (X.exp g).coeff r ∈ V.nonunits) → W.valuation (g - algebraMap Ω X.K ((X.exp g).coeff 0)) < 1) → ∃ κ : Ω, κ ≠ 0 ∧ W.valuation (algebraMap Ω X.K κ * ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K)) / (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q) - 1) < 1 := by
  intro Ω _ _ _ ε X hε hj M f hM hf
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  let F : SL(2, ZMod M) → X.K := fun τ =>
    if h : ∃ σ, red σ = τ then X.sl (ofSL h.choose) (f : X.K) else (f : X.K)
  have hF : ∀ σ : SL(2, ℤ), X.sl (ofSL σ) (f : X.K) = F (red σ) := by
    intro σ
    have h : ∃ σ', red σ' = red σ := ⟨σ, rfl⟩
    have e : F (red σ) = X.sl (ofSL h.choose) (f : X.K) := dif_pos h
    have hσ' : red h.choose = red σ := h.choose_spec
    have hγ : σ * h.choose⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      have : σ * h.choose⁻¹ ∈ red.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ', mul_inv_cancel]
      exact this
    rw [e]
    calc X.sl (ofSL σ) (f : X.K) = X.sl (ofSL (σ * h.choose⁻¹ * h.choose)) (f : X.K) := by
          rw [inv_mul_cancel_right]
      _ = X.sl (ofSL h.choose) (X.sl (ofSL (σ * h.choose⁻¹)) (f : X.K)) := by rw [map_mul, X.sl_mul]
      _ = _ := by rw [hf _ hγ]
  choose D hD0 hD using X.bdd
  let P : X.K → Finset ℕ := fun g => (D g).primeFactors ∪ (D g⁻¹).primeFactors
  refine ⟨M.primeFactors ∪ P f ∪ Finset.univ.biUnion (fun τ => P (F τ)), ?_⟩
  intro q hq hqS V s hqV hs σ hσ W hW hdom
  have hn : ∀ h : X.K, q ∉ (D h).primeFactors → ∀ r, (X.exp h).coeff r ∈ V := fun h hh r =>
    mem_of_bdd V hq hqV (fun hd => hh (Nat.mem_primeFactors.2 ⟨hq, hd, (hD0 h).ne'⟩)) (hD h r)
  have hint : ∀ g : X.K, q ∉ P g → (∀ r, (X.exp g).coeff r ∈ V) ∧ (∀ r, (X.exp g⁻¹).coeff r ∈ V) := fun g hg =>
    ⟨hn g fun h => hg (Finset.mem_union_left _ h), hn _ fun h => hg (Finset.mem_union_right _ h)⟩
  have hqM : q ∉ M.primeFactors := fun h => hqS (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hqf : q ∉ P f := fun h => hqS (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hqF : q ∉ P (F (red σ)) := fun h =>
    hqS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩))
  obtain ⟨hf1, hf2⟩ := hint _ hqf
  rw [← hF σ] at hqF
  obtain ⟨hs1, hs2⟩ := hint _ hqF
  have hcop : Nat.Coprime q M :=
    (Nat.Prime.coprime_iff_not_dvd hq).2 fun hd => hqM (Nat.mem_primeFactors.2 ⟨hq, hd, hM.ne'⟩)
  have hK := kronecker_congruence_tower ε X hε hj M q (f : X.K) hM hq hcop hf σ ⟨hσ.2.1, hσ.2.2⟩ V s hqV hs hf1 hs1
  refine ⟨1, one_ne_zero, ?_⟩
  generalize (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) *
    X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = A at hK ⊢
  have hB0 : X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q ≠ 0 :=
    mul_ne_zero ((map_ne_zero _).2 f.ne_zero)
      (pow_ne_zero _ ((map_ne_zero _).2 ((map_ne_zero _).2 f.ne_zero)))
  have hBinv : ∀ r, (X.exp (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q)⁻¹).coeff r ∈ V := by
    intro r
    rw [mul_inv, ← inv_pow, ← map_inv₀, ← map_inv₀ (X.gal s.symm), map_mul, map_pow]
    refine coeff_mul_mem V _ _ (fun t => ?_) (coeff_pow_mem V _ (fun t => ?_) q) r
    · rw [X.gal_exp]; exact (hs _ (hf2 t)).1
    · rw [X.gal_exp]; exact (hs _ (hs2 t)).2.1
  generalize X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q = B at hK hB0 hBinv ⊢
  have hge : algebraMap Ω X.K 1 * A / B - 1 = (A - B) * B⁻¹ := by
    rw [map_one, one_mul]; field_simp
  rw [hge]
  have hgc : ∀ r, (X.exp ((A - B) * B⁻¹)).coeff r ∈ V.nonunits := by
    intro r; rw [map_mul]; exact coeff_mul_mem_nonunits V _ _ hK hBinv r
  generalize (A - B) * B⁻¹ = g at hgc ⊢
  have hgV : ∀ r, (X.exp g).coeff r ∈ V := fun r =>
    (V.valuation_le_one_iff _).1 (le_of_lt (V.mem_nonunits_iff.1 (hgc r)))
  have h1 := hdom g hgV fun r _ => hgc r
  have hcV := V.mem_nonunits_iff.1 (hgc 0)
  have hcm := hgV 0
  generalize (X.exp g).coeff 0 = c at h1 hcV hcm
  have h2 : W.valuation (algebraMap Ω X.K c) < 1 := by
    by_cases hc0 : c = 0
    · rw [hc0, map_zero, map_zero]; exact zero_lt_one
    refine lt_of_le_of_ne ((W.valuation_le_one_iff _).2 ((hW c).2 hcm)) fun heq => ?_
    have hinv : algebraMap Ω X.K c⁻¹ ∈ W := by
      rw [← W.valuation_le_one_iff, map_inv₀, map_inv₀, heq, inv_one]
    have h3 : V.valuation c⁻¹ ≤ 1 := (V.valuation_le_one_iff _).2 ((hW _).1 hinv)
    have h4 : V.valuation (c⁻¹ * c) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' h3) hcV
    rw [inv_mul_cancel₀ hc0, map_one] at h4
    exact lt_irrefl _ h4
  have h5 := lt_of_le_of_lt (W.valuation.map_add _ _) (max_lt h1 h2)
  rwa [sub_add_cancel] at h5

end GlobalTheory.KZ
