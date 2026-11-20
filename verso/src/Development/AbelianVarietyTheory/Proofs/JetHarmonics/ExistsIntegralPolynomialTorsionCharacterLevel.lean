import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosureStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesEvalTsumOpenPolydiscPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralPolyOfCharacterStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralCoeffInterpolationBivariateSeriesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupTorsionTowerExactOrderStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesEvalOpenDiscPropertiesStatement

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

/- English proof (translation)
Take `⟨-, halg, hC, -⟩` from `GlobalTheory.T.mvPowerSeriesEvalTsum_openPolydisc_properties K σ x hx`. Take `⟨-, -, hpow, -⟩` from `GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ`. Establish `hB : Bdd S` using `(hpow S 0).2.2 hS`. Proceed by induction on `k with`. Consider the case `zero => simpa using hC 1`.

Consider the case `succ k ih => rw [pow_succ, (halg _ _ ((hpow S k).2.1 hB) hB).2.2, ih, pow_succ]`.
-/
theorem ev_pow_of_intg (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (σ : Type) [Fintype σ] (x : σ → K) (hx : ∀ i, ‖x i‖ < 1) (S : MvPowerSeries σ K)
    (hS : Intg S) (k : ℕ) : ev (S ^ k) x = ev S x ^ k := by
  obtain ⟨-, halg, hC, -⟩ := GlobalTheory.T.mvPowerSeriesEvalTsum_openPolydisc_properties K σ x hx
  obtain ⟨-, -, hpow, -⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ
  have hB : Bdd S := (hpow S 0).2.2 hS
  induction k with
  | zero => simpa using hC 1
  | succ k ih => rw [pow_succ, (halg _ _ ((hpow S k).2.1 hB) hB).2.2, ih, pow_succ]

/- English proof (translation)
Use `haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩`. Establish `hord` using `(GlobalTheory.T.formalGroup_torsionTower_exact_order K p F hF t ht h0 h1 hp).2.2 n`. Take `⟨-, -, hnorm, hadd, -⟩` from `(GlobalTheory.T.formalGroupNatMulSeries_eval_openDisc_properties K F hF).2 (t n) (ht n)`. Use `set x : ZMod (p ^ n) → K := fun i => ev1 (nMul F i.val) (t n) with hx`. Establish `hxlt : ∀ i, ‖x i‖ < 1` using `fun i => (hnorm i.val).1.trans_lt (ht n)`.

Establish `hinj : Function.Injective x`. Introduce `i j hij`. Use `(hord _ _).1 hij` as an intermediate fact. Establish `h2` using `(ZMod.natCast_eq_natCast_iff _ _ _).2 this`. Simplify using `using h2`.

Establish `hxadd : ∀ i j, x (i + j) = ev F.toPowerSeries ![x i, x j]`. Introduce `i j`. Simplify using `only [hx]`. Rewrite using `[hadd, hord, ZMod.val_add]`. Conclude with `Nat.mod_modEq _ _`.

Establish `hχ : ∀ i j : ZMod (p ^ n), ζ ^ (i + j).val = ζ ^ i.val * ζ ^ j.val`. Introduce `i j`. Rewrite using `[ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hζ]`. Establish `hcard : (Finset.univ.image x).card = Fintype.card (ZMod (p ^ n))`. Rewrite using `[Finset.card_image_of_injective _ hinj, Finset.card_univ]`.

Take `⟨g, hg, hgx⟩` from `GlobalTheory.T.exists_integral_poly_of_character' K (ZMod (p ^ n)) x (fun i => ζ ^ i.val) hinj hχ (by`. Introduce `k`. Establish `hc` using `GlobalTheory.T.exists_integral_coeff_interpolation_bivariate_series K (Finset.univ.image x) (F.toPowerSeries ^ (k : ℕ)) (by`. Introduce `y hy`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hy`.

Conclude with `hxlt i)`. Use the proof step `(((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K (Fin 2)).2.2.1 _ _).1 hF)`. Rewrite `hc` using `[hcard]`. Take `⟨c, hc1, hc2⟩` from `hc`. Use `⟨c, hc1, fun i j => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hc2 _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)) _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)), hxadd, ev_pow_of_intg K (Fin 2) _ _ _ hF]`. Introduce `l`. Use `fin_cases l`. Conclude with `hxlt i`. Conclude with `hxlt j)`.

Use `⟨g, hg, fun j => ?_⟩` and prove the remaining obligations. Use `hgx (j : ZMod (p ^ n))` as an intermediate fact. Simplify using `only [hx, ZMod.val_natCast] at this`. Rewrite `this` using `[← pow_eq_pow_mod _ hζ]`. Rewrite using `[← this, (hord j (j % p ^ n)).2 (Nat.mod_modEq _ _).symm]`.
-/
theorem exists_intg_polynomial_level (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K) (hF : Intg F.toPowerSeries)
    (t : ℕ → K) (ht : ∀ n, ‖t n‖ < 1) (h0 : t 0 = 0) (h1 : t 1 ≠ 0)
    (hp : ∀ n, ev1 (nMul F p) (t (n + 1)) = t n) (n : ℕ) (ζ : K) (hζ : ζ ^ (p ^ n) = 1) :
    ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧
      ∀ j : ℕ, g.eval (ev1 (nMul F j) (t n)) = ζ ^ j := by
  classical
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hord := (GlobalTheory.T.formalGroup_torsionTower_exact_order K p F hF t ht h0 h1 hp).2.2 n
  obtain ⟨-, -, hnorm, hadd, -⟩ := (GlobalTheory.T.formalGroupNatMulSeries_eval_openDisc_properties K F hF).2 (t n) (ht n)
  set x : ZMod (p ^ n) → K := fun i => ev1 (nMul F i.val) (t n) with hx
  have hxlt : ∀ i, ‖x i‖ < 1 := fun i => (hnorm i.val).1.trans_lt (ht n)
  have hinj : Function.Injective x := by
    intro i j hij
    have := (hord _ _).1 hij
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 this
    simpa using h2
  have hxadd : ∀ i j, x (i + j) = ev F.toPowerSeries ![x i, x j] := by
    intro i j
    simp only [hx]
    rw [hadd, hord, ZMod.val_add]
    exact Nat.mod_modEq _ _
  have hχ : ∀ i j : ZMod (p ^ n), ζ ^ (i + j).val = ζ ^ i.val * ζ ^ j.val := by
    intro i j
    rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hζ]
  have hcard : (Finset.univ.image x).card = Fintype.card (ZMod (p ^ n)) := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  obtain ⟨g, hg, hgx⟩ := GlobalTheory.T.exists_integral_poly_of_character' K (ZMod (p ^ n)) x (fun i => ζ ^ i.val) hinj hχ (by
    intro k
    have hc := GlobalTheory.T.exists_integral_coeff_interpolation_bivariate_series K (Finset.univ.image x) (F.toPowerSeries ^ (k : ℕ))
      (by
        intro y hy
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
        exact hxlt i)
      (((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K (Fin 2)).2.2.1 _ _).1 hF)
    rw [hcard] at hc
    obtain ⟨c, hc1, hc2⟩ := hc
    refine ⟨c, hc1, fun i j => ?_⟩
    rw [← hc2 _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)) _
      (Finset.mem_image_of_mem _ (Finset.mem_univ j)), hxadd,
      ev_pow_of_intg K (Fin 2) _ _ _ hF]
    intro l
    fin_cases l
    · exact hxlt i
    · exact hxlt j)
  refine ⟨g, hg, fun j => ?_⟩
  have := hgx (j : ZMod (p ^ n))
  simp only [hx, ZMod.val_natCast] at this
  rw [← pow_eq_pow_mod _ hζ] at this
  rw [← this, (hord j (j % p ^ n)).2 (Nat.mod_modEq _ _).symm]

end GlobalTheory.ConvSer
