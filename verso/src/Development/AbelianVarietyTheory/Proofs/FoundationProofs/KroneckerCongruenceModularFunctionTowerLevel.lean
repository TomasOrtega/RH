import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NqSubGalSmall
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceFrobeniusDiagStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTranslateNormProductEqOfDvdStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveQuotientLevelPrimeToStatement

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Establish `h1` using `(V.valuation_le_one_iff x).2 hx`. Establish `h2` using `(V.valuation_le_one_iff x⁻¹).2 hi`. Rewrite `h2` using `[map_inv₀]`. Establish `hne : V.valuation x ≠ 0` using `by simpa using h0`. Conclude with `le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 h2)`.
-/
theorem kc_val_one_of_inv {V : ValuationSubring Ω} {x : Ω} (hx : x ∈ V) (hi : x⁻¹ ∈ V) (h0 : x ≠ 0) :
    V.valuation x = 1 := by
  have h1 := (V.valuation_le_one_iff x).2 hx
  have h2 := (V.valuation_le_one_iff x⁻¹).2 hi
  rw [map_inv₀] at h2
  have hne : V.valuation x ≠ 0 := by simpa using h0
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 h2)

/- English proof (translation)
Establish `h0 : x ≠ 0` using `by rintro rfl; simp at h`. Use `⟨(V.valuation_le_one_iff x).1 h.le, (V.valuation_le_one_iff x⁻¹).1 ?_, h0⟩` and prove the remaining obligations. Rewrite using `[map_inv₀, h, inv_one]`.
-/
theorem kc_inv_of_val_one {V : ValuationSubring Ω} {x : Ω} (h : V.valuation x = 1) :
    x ∈ V ∧ x⁻¹ ∈ V ∧ x ≠ 0 := by
  have h0 : x ≠ 0 := by rintro rfl; simp at h
  refine ⟨(V.valuation_le_one_iff x).1 h.le, (V.valuation_le_one_iff x⁻¹).1 ?_, h0⟩
  rw [map_inv₀, h, inv_one]

/- English proof (translation)
Take `⟨hI, r, hr⟩` from `ha`. Use `⟨fun r' => by rw [X.gal_exp]; exact hs _ (hI r'), r, ?_⟩` and prove the remaining obligations. Rewrite using `[X.gal_exp]`. Take `⟨h1, h2, h3⟩` from `kc_inv_of_val_one hr`. Conclude with `kc_val_one_of_inv (hs _ h1) (by rw [← map_inv₀]; exact hs _ h2) (by simpa using h3)`.
-/
theorem kc_prim_gal (X : Tower Ω ε) (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x ∈ V, s x ∈ V)
    {a : X.K} (ha : Prim X V a) : Prim X V (X.gal s a) := by
  obtain ⟨hI, r, hr⟩ := ha
  refine ⟨fun r' => by rw [X.gal_exp]; exact hs _ (hI r'), r, ?_⟩
  rw [X.gal_exp]
  obtain ⟨h1, h2, h3⟩ := kc_inv_of_val_one hr
  exact kc_val_one_of_inv (hs _ h1) (by rw [← map_inv₀]; exact hs _ h2) (by simpa using h3)

/- English proof (translation)
Introduce and unpack `rfl`. Take `⟨_, r, hr⟩` from `ha`. Simplify using `at hr`.
-/
theorem kc_ne_zero_of_prim {X : Tower Ω ε} {V : ValuationSubring Ω} {a : X.K} (ha : Prim X V a) : a ≠ 0 := by
  rintro rfl
  obtain ⟨_, r, hr⟩ := ha
  simp at hr

/- English proof (translation)
Simplify using `only [Nq, map_mul, Finset.prod_mul_distrib]`.
-/
theorem kc_Nq_mul (X : Tower Ω ε) (M q : ℕ) (f g : X.K) : Nq X M q (f * g) = Nq X M q f * Nq X M q g := by
  simp only [Nq, map_mul, Finset.prod_mul_distrib]

/- English proof (translation)
Simplify using `only [Nq, map_mul, AlgEquiv.commutes, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]`.
-/
theorem kc_Nq_const (X : Tower Ω ε) (M q : ℕ) (c : Ω) (a : X.K) :
    Nq X M q (algebraMap Ω X.K c * a) = algebraMap Ω X.K c ^ q * Nq X M q a := by
  simp only [Nq, map_mul, AlgEquiv.commutes, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/- English proof (translation)
Simplify using `only [Nq]`. Conclude with `Finset.prod_ne_zero_iff.2 fun j _ => by simpa using hf`.
-/
theorem kc_Nq_ne_zero (X : Tower Ω ε) (M q : ℕ) {f : X.K} (hf : f ≠ 0) : Nq X M q f ≠ 0 := by
  simp only [Nq]
  exact Finset.prod_ne_zero_iff.2 fun j _ => by simpa using hf

/- English proof (translation)
Apply `(X.exp : X.K →+* HahnSeries ℚ Ω).injective` to reduce the goal to its premises. Use extensionality with `r`. Use `show (X.exp (X.gal s (algebraMap Ω X.K c))).coeff r = (X.exp (algebraMap Ω X.K (s c))).coeff r`. Rewrite using `[X.gal_exp, AlgHom.commutes, AlgHom.commutes]`. Establish `e : ∀ x : Ω, (algebraMap Ω (HahnSeries ℚ Ω) x).coeff r = if r = 0 then x else 0`.

Introduce `x`. Rewrite using `[HahnSeries.algebraMap_apply']`. Establish `: algebraMap Ω (PowerSeries Ω) x = PowerSeries.C x` using `rfl`. Rewrite using `[this, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]`. Simplify using the standard rewrite rules.

Rewrite using `[e, e]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem kc_gal_const (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  show (X.exp (X.gal s (algebraMap Ω X.K c))).coeff r = (X.exp (algebraMap Ω X.K (s c))).coeff r
  rw [X.gal_exp, AlgHom.commutes, AlgHom.commutes]
  have e : ∀ x : Ω, (algebraMap Ω (HahnSeries ℚ Ω) x).coeff r = if r = 0 then x else 0 := by
    intro x
    rw [HahnSeries.algebraMap_apply']
    have : algebraMap Ω (PowerSeries Ω) x = PowerSeries.C x := rfl
    rw [this, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]
    simp
  rw [e, e]
  split_ifs <;> simp

/- English proof (translation)
Establish `hy0 : y ≠ 0` using `by rintro rfl; simp at hy`. Rewrite using `[show x / y - 1 = (x - y) / y by field_simp, map_div₀, hy, div_one]`. Conclude with `h`.
-/
theorem kc_div_sub_one {L : Type} [Field L] (W : ValuationSubring L) {x y : L} (hy : W.valuation y = 1)
    (h : W.valuation (x - y) < 1) : W.valuation (x / y - 1) < 1 := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  rw [show x / y - 1 = (x - y) / y by field_simp, map_div₀, hy, div_one]
  exact h

/- English proof (translation)
Establish `hy1 : W.valuation y = 1`. Use `Valuation.map_one_add_of_lt W.valuation hy` as an intermediate fact. Simplify using `using this`. Apply `kc_div_sub_one W hy1` to reduce the goal to its premises. Establish `e : x - y = (x - 1) - (y - 1)` using `by ring`.

Rewrite using `[e]`. Conclude with `lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hx hy)`.
-/
theorem kc_quot_one {L : Type} [Field L] (W : ValuationSubring L) {x y : L} (hx : W.valuation (x - 1) < 1)
    (hy : W.valuation (y - 1) < 1) : W.valuation (x / y - 1) < 1 := by
  have hy1 : W.valuation y = 1 := by
    have := Valuation.map_one_add_of_lt W.valuation hy
    simpa using this
  apply kc_div_sub_one W hy1
  have e : x - y = (x - 1) - (y - 1) := by ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hx hy)

/- English proof (translation)
Introduce `Ω _ _ _ ε X hj l M₀ hl hM₀`. Take `⟨S, hS⟩` from `GlobalTheory.T.exists_primitive_quotient_level_prime_to ε X hj l M₀ hl hM₀`. Use `⟨S, fun q hq hqS V s hF W hD k f hf hlev => ?_⟩` and prove the remaining obligations. Take `⟨M', a, b, c, hM', hcop, hdvd, hla, hlb, hpa, hpb, hc, hfb⟩` from `hS q hq hqS V hF.1 k f hf hlev`. Establish `ha0` using `kc_ne_zero_of_prim hpa`.

Establish `hb0` using `kc_ne_zero_of_prim hpb`. Establish `hsV : ∀ x ∈ V, s x ∈ V` using `fun x hx => (hF.2 x hx).1`. Establish `hsV' : ∀ x ∈ V, s.symm x ∈ V` using `fun x hx => (hF.2 x hx).2.1`. Establish `hC : algebraMap Ω X.K c ≠ 0` using `(_root_.map_ne_zero _).2 hc`. Establish `hgal : ∀ (t : Ω ≃ₐ[ℚ] Ω) (g : X.K), g ≠ 0 → X.gal t g ≠ 0` using `fun t g hg => by simpa using hg`.

Establish `hE : ∀ t : Ω ≃ₐ[ℚ] Ω, X.gal t f = algebraMap Ω X.K (t c) * X.gal t a / X.gal t b` using `fun t => by`. Rewrite using `[eq_div_iff (hgal t b hb0), ← map_mul, hfb, map_mul, kc_gal_const]`. Establish `hC' : ∀ t : Ω ≃ₐ[ℚ] Ω, algebraMap Ω X.K (t c) ≠ 0` using `fun t => (_root_.map_ne_zero _).2 (by simpa using hc)`. Prove the components needed by the constructor for the conclusion. Use `⟨s c / c ^ q, ?_⟩` and prove the remaining obligations.

Establish `hN : Nq X (M₀ * l ^ k) q f = Nq X M' q f` using `GlobalTheory.T.heckeTranslateNormProduct_eq_of_dvd ε X _ _ q f hq.pos hdvd hcop hlev`. Establish `A1` using `kc_div_sub_one W (hD.2.2 _ (kc_prim_gal X V s hsV hpa)) (hD.2.1 _ (GlobalTheory.KZ.ES.nq_sub_gal_small ε X M' q hM' hq V s hF a hla hpa.1))`. Establish `B1` using `kc_div_sub_one W (hD.2.2 _ (kc_prim_gal X V s hsV hpb)) (hD.2.1 _ (GlobalTheory.KZ.ES.nq_sub_gal_small ε X M' q hM' hq V s hF b hlb hpb.1))`. Establish `hNb` using `kc_Nq_ne_zero X M' q hb0`. Establish `E1 : Nq X M' q f = algebraMap Ω X.K c ^ q * Nq X M' q a / Nq X M' q b`.

Rewrite using `[eq_div_iff hNb, ← kc_Nq_mul, hfb, kc_Nq_const]`. Establish `key : algebraMap Ω X.K (s c / c ^ q) * Nq X (M₀ * l ^ k) q f / X.gal s f = (Nq X M' q a / X.gal s a) / (Nq X M' q b / X.gal s b)`. Establish `h1` using `hgal s a ha0`. Establish `h2` using `hgal s b hb0`. Establish `h3` using `hC' s`.

Rewrite using `[hN, E1, hE s, map_div₀, map_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`. Conclude with `kc_quot_one W A1 B1`. Use `⟨(s.symm c) ^ q / c, ?_⟩` and prove the remaining obligations.

Establish `A1` using `kc_div_sub_one W (by rw [map_pow, hD.2.2 _ (kc_prim_gal X V s.symm hsV' hpa), one_pow]) (hD.2.1 _ (GlobalTheory.T.kronecker_congruence_frobenius_diag ε X q hq V s hF a hpa.1))`. Establish `B1` using `kc_div_sub_one W (by rw [map_pow, hD.2.2 _ (kc_prim_gal X V s.symm hsV' hpb), one_pow]) (hD.2.1 _ (GlobalTheory.T.kronecker_congruence_frobenius_diag ε X q hq V s hF b hpb.1))`. Generalize the expression as in `toGQ !![(q : ℤ), 0; 0, 1] = T at A1 B1 ⊢`. Establish `hTb : X.sl T b ≠ 0` using `by simpa using hb0`. Establish `E1 : X.sl T f = algebraMap Ω X.K c * X.sl T a / X.sl T b`.

Rewrite using `[eq_div_iff hTb, ← map_mul, hfb, map_mul, AlgEquiv.commutes]`. Establish `key : algebraMap Ω X.K ((s.symm c) ^ q / c) * X.sl T f / (X.gal s.symm f) ^ q = (X.sl T a / (X.gal s.symm a) ^ q) / (X.sl T b / (X.gal s.symm b) ^ q)`. Establish `h1` using `hgal s.symm a ha0`. Establish `h2` using `hgal s.symm b hb0`. Establish `h3` using `hC' s.symm`.

Rewrite using `[E1, hE s.symm, map_div₀, map_pow, div_pow, mul_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`. Conclude with `kc_quot_one W A1 B1`.
-/
theorem kron_cong_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ W : ValuationSubring X.K, Dom X V W → ∀ (k : ℕ) (f : X.K), f ≠ 0 → Lev X (M₀ * l ^ k) f → (∃ c : Ω, W.valuation (algebraMap Ω X.K c * Nq X (M₀ * l ^ k) q f / X.gal s f - 1) < 1) ∧ ∃ c : Ω, W.valuation (algebraMap Ω X.K c * X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f / (X.gal s.symm f) ^ q - 1) < 1 := by
  intro Ω _ _ _ ε X hj l M₀ hl hM₀
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_primitive_quotient_level_prime_to ε X hj l M₀ hl hM₀
  refine ⟨S, fun q hq hqS V s hF W hD k f hf hlev => ?_⟩
  obtain ⟨M', a, b, c, hM', hcop, hdvd, hla, hlb, hpa, hpb, hc, hfb⟩ := hS q hq hqS V hF.1 k f hf hlev
  have ha0 := kc_ne_zero_of_prim hpa
  have hb0 := kc_ne_zero_of_prim hpb
  have hsV : ∀ x ∈ V, s x ∈ V := fun x hx => (hF.2 x hx).1
  have hsV' : ∀ x ∈ V, s.symm x ∈ V := fun x hx => (hF.2 x hx).2.1
  have hC : algebraMap Ω X.K c ≠ 0 := (_root_.map_ne_zero _).2 hc
  have hgal : ∀ (t : Ω ≃ₐ[ℚ] Ω) (g : X.K), g ≠ 0 → X.gal t g ≠ 0 := fun t g hg => by simpa using hg
  have hE : ∀ t : Ω ≃ₐ[ℚ] Ω, X.gal t f = algebraMap Ω X.K (t c) * X.gal t a / X.gal t b := fun t => by
    rw [eq_div_iff (hgal t b hb0), ← map_mul, hfb, map_mul, kc_gal_const]
  have hC' : ∀ t : Ω ≃ₐ[ℚ] Ω, algebraMap Ω X.K (t c) ≠ 0 := fun t => (_root_.map_ne_zero _).2 (by simpa using hc)
  constructor
  · refine ⟨s c / c ^ q, ?_⟩
    have hN : Nq X (M₀ * l ^ k) q f = Nq X M' q f := GlobalTheory.T.heckeTranslateNormProduct_eq_of_dvd ε X _ _ q f hq.pos hdvd hcop hlev
    have A1 := kc_div_sub_one W (hD.2.2 _ (kc_prim_gal X V s hsV hpa))
      (hD.2.1 _ (GlobalTheory.KZ.ES.nq_sub_gal_small ε X M' q hM' hq V s hF a hla hpa.1))
    have B1 := kc_div_sub_one W (hD.2.2 _ (kc_prim_gal X V s hsV hpb))
      (hD.2.1 _ (GlobalTheory.KZ.ES.nq_sub_gal_small ε X M' q hM' hq V s hF b hlb hpb.1))
    have hNb := kc_Nq_ne_zero X M' q hb0
    have E1 : Nq X M' q f = algebraMap Ω X.K c ^ q * Nq X M' q a / Nq X M' q b := by
      rw [eq_div_iff hNb, ← kc_Nq_mul, hfb, kc_Nq_const]
    have key : algebraMap Ω X.K (s c / c ^ q) * Nq X (M₀ * l ^ k) q f / X.gal s f
        = (Nq X M' q a / X.gal s a) / (Nq X M' q b / X.gal s b) := by
      have h1 := hgal s a ha0
      have h2 := hgal s b hb0
      have h3 := hC' s
      rw [hN, E1, hE s, map_div₀, map_pow]
      field_simp
    rw [key]
    exact kc_quot_one W A1 B1
  · refine ⟨(s.symm c) ^ q / c, ?_⟩
    have A1 := kc_div_sub_one W (by rw [map_pow, hD.2.2 _ (kc_prim_gal X V s.symm hsV' hpa), one_pow])
      (hD.2.1 _ (GlobalTheory.T.kronecker_congruence_frobenius_diag ε X q hq V s hF a hpa.1))
    have B1 := kc_div_sub_one W (by rw [map_pow, hD.2.2 _ (kc_prim_gal X V s.symm hsV' hpb), one_pow])
      (hD.2.1 _ (GlobalTheory.T.kronecker_congruence_frobenius_diag ε X q hq V s hF b hpb.1))
    generalize toGQ !![(q : ℤ), 0; 0, 1] = T at A1 B1 ⊢
    have hTb : X.sl T b ≠ 0 := by simpa using hb0
    have E1 : X.sl T f = algebraMap Ω X.K c * X.sl T a / X.sl T b := by
      rw [eq_div_iff hTb, ← map_mul, hfb, map_mul, AlgEquiv.commutes]
    have key : algebraMap Ω X.K ((s.symm c) ^ q / c) * X.sl T f / (X.gal s.symm f) ^ q
        = (X.sl T a / (X.gal s.symm a) ^ q) / (X.sl T b / (X.gal s.symm b) ^ q) := by
      have h1 := hgal s.symm a ha0
      have h2 := hgal s.symm b hb0
      have h3 := hC' s.symm
      rw [E1, hE s.symm, map_div₀, map_pow, div_pow, mul_pow]
      field_simp
    rw [key]
    exact kc_quot_one W A1 B1

end GlobalTheory.KZ.ES
