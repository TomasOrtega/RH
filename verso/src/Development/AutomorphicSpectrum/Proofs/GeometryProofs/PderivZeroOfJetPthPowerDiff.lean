import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FramesCompatibleEventuallyOfGerm
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc

/- English proof (translation)
Introduce `e he`. Rewrite using `[MvPolynomial.coeff_mul]`. Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `h2 : x.2.degree ≤ e.degree`.

Rewrite using `[← hx, map_add]`. Conclude with `Nat.le_add_left _ _`. Rewrite using `[ha x.2 (lt_of_le_of_lt h2 he), mul_zero]`.
-/
private theorem coeff_mul_eq_zero_of_order_two_of_degree_le_two {σ k : Type} [CommRing k] (j : ℕ) (q a : MvPolynomial σ k)
    (ha : ∀ e : σ →₀ ℕ, e.degree < j → MvPolynomial.coeff e a = 0) :
    ∀ e : σ →₀ ℕ, e.degree < j → MvPolynomial.coeff e (q * a) = 0 := by
  classical
  intro e he
  rw [MvPolynomial.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h2 : x.2.degree ≤ e.degree := by
    rw [← hx, map_add]; exact Nat.le_add_left _ _
  rw [ha x.2 (lt_of_le_of_lt h2 he), mul_zero]

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro P _ e he`. Conclude with `absurd he (Nat.not_lt_zero _)`. Consider the case `succ j ih`.

Set `K : Ideal (MvPolynomial σ k)` to `{ carrier := {P | ∀ e : σ →₀ ℕ, e.degree < j + 1 → MvPolynomial.coeff e P = 0} add_mem' := fun {a b} ha hb e he => by rw [MvPolynomial.coeff_add, ha e he, hb e he, add_zero] zero_mem' := fun e _ => MvPolynomial.coeff_zero e smul_mem' := fun c a ha => coeff_mul_eq_zero_of_order_tw …`. Establish `hle : Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) ^ (j + 1) ≤ K`. Rewrite using `[pow_succ, Ideal.mul_le]`. Introduce `r hr s hs`. Use `Submodule.span_induction (p := fun s _ => r * s ∈ K) ?_ ?_ ?_ ?_ hs` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩ show ∀ e : σ →₀ ℕ, e.degree < j + 1 → MvPolynomial.coeff e (r * MvPolynomial.X i) = 0`. Introduce `e he`. Rewrite using `[MvPolynomial.coeff_mul]`. Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Rewrite using `[MvPolynomial.coeff_X']`. Use `split_ifs with hxi`. Establish `hx1 : x.1.degree + 1 = e.degree`. Rewrite using `[← hx, map_add, ← hxi, Finsupp.degree_single]`. Rewrite using `[ih r hr x.1 (by omega), zero_mul]`.

Rewrite using `[mul_zero]`. Rewrite using `[mul_zero]`. Conclude with `K.zero_mem`. Introduce `a b _ _ ha hb`. Rewrite using `[mul_add]`.

Conclude with `K.add_mem ha hb`. Introduce `c a _ ha`. Rewrite using `[smul_eq_mul, mul_left_comm]`. Conclude with `K.mul_mem_left c ha`. Conclude with `fun P hP => hle hP`.
-/
private theorem coeff_eq_zero_of_mem_span_X_pow_of_degree_lt {σ k : Type} [CommRing k] :
    ∀ (j : ℕ) (P : MvPolynomial σ k), P ∈ Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) ^ j →
      ∀ e : σ →₀ ℕ, e.degree < j → MvPolynomial.coeff e P = 0 := by
  classical
  intro j
  induction j with
  | zero => intro P _ e he; exact absurd he (Nat.not_lt_zero _)
  | succ j ih =>
    let K : Ideal (MvPolynomial σ k) :=
      { carrier := {P | ∀ e : σ →₀ ℕ, e.degree < j + 1 → MvPolynomial.coeff e P = 0}
        add_mem' := fun {a b} ha hb e he => by rw [MvPolynomial.coeff_add, ha e he, hb e he, add_zero]
        zero_mem' := fun e _ => MvPolynomial.coeff_zero e
        smul_mem' := fun c a ha => coeff_mul_eq_zero_of_order_two_of_degree_le_two (j + 1) c a ha }
    have hle : Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) ^ (j + 1) ≤ K := by
      rw [pow_succ, Ideal.mul_le]
      intro r hr s hs
      refine Submodule.span_induction (p := fun s _ => r * s ∈ K) ?_ ?_ ?_ ?_ hs
      · rintro _ ⟨i, rfl⟩
        show ∀ e : σ →₀ ℕ, e.degree < j + 1 → MvPolynomial.coeff e (r * MvPolynomial.X i) = 0
        intro e he
        rw [MvPolynomial.coeff_mul]
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [MvPolynomial.coeff_X']
        split_ifs with hxi
        · have hx1 : x.1.degree + 1 = e.degree := by
            rw [← hx, map_add, ← hxi, Finsupp.degree_single]
          rw [ih r hr x.1 (by omega), zero_mul]
        · rw [mul_zero]
      · rw [mul_zero]; exact K.zero_mem
      · intro a b _ _ ha hb; rw [mul_add]; exact K.add_mem ha hb
      · intro c a _ ha; rw [smul_eq_mul, mul_left_comm]; exact K.mul_mem_left c ha
    exact fun P hP => hle hP

/- English proof (translation)
Introduce `k _ p _ _ d F f hf hF q`. Use extensionality with `e`. Take `⟨v, hv⟩` from `hF (e.degree + 1)`. Take `⟨P, rfl⟩` from `Ideal.Quotient.mk_surjective v`. Establish `hmem : psTrunc (e.degree + 1) F + psTrunc (e.degree + 1) f - P ^ p ∈ orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1)`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, map_pow]`. Establish `h1 : psJet (e.degree + 1) F = Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1)) (psTrunc (e.degree + 1) F)` using `rfl`. Establish `h2 : psJet (e.degree + 1) f = Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1)) (psTrunc (e.degree + 1) f)` using `rfl`. Rewrite using `[← h1, ← h2, hv]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hdeg : (e + Finsupp.single q 1).degree < e.degree + 1 + 1`. Rewrite using `[map_add, Finsupp.degree_single]`. Use linear arithmetic over natural numbers and integers. Establish `hz` using `coeff_eq_zero_of_mem_span_X_pow_of_degree_lt (e.degree + 1 + 1) _ hmem (e + Finsupp.single q 1) hdeg`. Establish `hbd : ∀ i, (e + Finsupp.single q 1 : Fin 1 × Fin d →₀ ℕ) i ≤ (e + Finsupp.single q 1).degree`.

Introduce `i`. Conclude with `Finsupp.le_degree i _`. Establish `hin : e + Finsupp.single q 1 ∈ degLE (e.degree + 1)`. Simplify using `only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion.

Use `⟨fun i => ⟨(e + Finsupp.single q 1 : Fin 1 × Fin d →₀ ℕ) i, ?_⟩, ?_⟩` and prove the remaining obligations. Use `hbd i` as an intermediate fact. Rewrite `this` using `[map_add, Finsupp.degree_single]`. Use linear arithmetic over natural numbers and integers. Use extensionality with `i`.

Simplify using the standard rewrite rules. Use `show (e + Finsupp.single q 1).degree ≤ e.degree + 1`. Rewrite using `[map_add, Finsupp.degree_single]`. Establish `htr : ∀ g : MvPowerSeries (Fin 1 × Fin d) k, MvPolynomial.coeff (e + Finsupp.single q 1) (psTrunc (e.degree + 1) g) = MvPowerSeries.coeff (e + Finsupp.single q 1) g`. Introduce `g`.

Simplify using `[psTrunc, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hin]`. Establish `hpow : MvPowerSeries.pderiv k q ((P ^ p : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries (Fin 1 × Fin d) k) = 0`. Rewrite using `[MvPolynomial.coe_pow, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]`. Establish `hG : MvPowerSeries.pderiv k q F = MvPowerSeries.pderiv k q (F + f - ((P ^ p : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries (Fin 1 × Fin d) k))`. Rewrite using `[map_sub, map_add, hf q, hpow, add_zero, sub_zero]`.

Rewrite using `[hG, MvPowerSeries.coeff_pderiv, map_zero, map_sub, map_add, MvPolynomial.coeff_coe, ← htr F, ← htr f, ← MvPolynomial.coeff_add, ← MvPolynomial.coeff_sub, hz, zero_mul]`.
-/
theorem pderiv_eq_zero_of_jet_pow_sub : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d : ℕ) (F f : MvPowerSeries (Fin 1 × Fin d) k), (∀ q, MvPowerSeries.pderiv k q f = 0) → (∀ m, ∃ v : Jet k (Fin 1 × Fin d) m, psJet m F = v ^ p - psJet m f) → ∀ q, MvPowerSeries.pderiv k q F = 0 := by
  intro k _ p _ _ d F f hf hF q
  classical
  ext e
  obtain ⟨v, hv⟩ := hF (e.degree + 1)
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hmem : psTrunc (e.degree + 1) F + psTrunc (e.degree + 1) f - P ^ p ∈
      orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, map_pow]
    have h1 : psJet (e.degree + 1) F =
        Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1)) (psTrunc (e.degree + 1) F) := rfl
    have h2 : psJet (e.degree + 1) f =
        Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1)) (psTrunc (e.degree + 1) f) := rfl
    rw [← h1, ← h2, hv]; ring
  have hdeg : (e + Finsupp.single q 1).degree < e.degree + 1 + 1 := by
    rw [map_add, Finsupp.degree_single]; omega
  have hz := coeff_eq_zero_of_mem_span_X_pow_of_degree_lt (e.degree + 1 + 1) _ hmem (e + Finsupp.single q 1) hdeg
  have hbd : ∀ i, (e + Finsupp.single q 1 : Fin 1 × Fin d →₀ ℕ) i ≤ (e + Finsupp.single q 1).degree := by
    intro i
    exact Finsupp.le_degree i _
  have hin : e + Finsupp.single q 1 ∈ degLE (e.degree + 1) := by
    simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · refine ⟨fun i => ⟨(e + Finsupp.single q 1 : Fin 1 × Fin d →₀ ℕ) i, ?_⟩, ?_⟩
      · have := hbd i
        rw [map_add, Finsupp.degree_single] at this
        omega
      · ext i; simp
    · show (e + Finsupp.single q 1).degree ≤ e.degree + 1
      rw [map_add, Finsupp.degree_single]
  have htr : ∀ g : MvPowerSeries (Fin 1 × Fin d) k,
      MvPolynomial.coeff (e + Finsupp.single q 1) (psTrunc (e.degree + 1) g) =
        MvPowerSeries.coeff (e + Finsupp.single q 1) g := by
    intro g
    simp [psTrunc, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hin]
  have hpow : MvPowerSeries.pderiv k q ((P ^ p : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries (Fin 1 × Fin d) k) = 0 := by
    rw [MvPolynomial.coe_pow, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  have hG : MvPowerSeries.pderiv k q F = MvPowerSeries.pderiv k q
      (F + f - ((P ^ p : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries (Fin 1 × Fin d) k)) := by
    rw [map_sub, map_add, hf q, hpow, add_zero, sub_zero]
  rw [hG, MvPowerSeries.coeff_pderiv, map_zero, map_sub, map_add, MvPolynomial.coeff_coe, ← htr F, ← htr f,
    ← MvPolynomial.coeff_add, ← MvPolynomial.coeff_sub, hz, zero_mul]

end GlobalTheory.CompanionTheory.Ar.Coc
