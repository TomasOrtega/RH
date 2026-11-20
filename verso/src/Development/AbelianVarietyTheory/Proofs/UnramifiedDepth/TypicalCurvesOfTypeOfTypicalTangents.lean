import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

namespace GlobalTheory.TypicalCurve

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

/- English proof (translation)
Establish `h1 : ∀ y : C, y ^ (p ^ h - 1) = 1 → y ^ (p ^ h) = y`. Introduce `y hy`. Establish `: p ^ h = (p ^ h - 1) + 1` using `(Nat.sub_add_cancel (Nat.one_le_pow _ _ hp)).symm`. Rewrite using `[this, pow_succ, hy, one_mul]`. Establish `h2 : ∀ k : ℕ, ζ ^ ((p ^ h) ^ k) = ζ`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, pow_mul, ih, h1 ζ hζ]`. Use `conv_lhs => rw [← Nat.div_add_mod e h, pow_add, pow_mul, pow_mul, h2]`.
-/
theorem pow_pow_mod {p h : ℕ} (hp : 0 < p) {ζ : C} (hζ : ζ ^ (p ^ h - 1) = 1) (e : ℕ) :
    ζ ^ (p ^ e) = ζ ^ (p ^ (e % h)) := by
  have h1 : ∀ y : C, y ^ (p ^ h - 1) = 1 → y ^ (p ^ h) = y := by
    intro y hy
    have : p ^ h = (p ^ h - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ hp)).symm
    rw [this, pow_succ, hy, one_mul]
  have h2 : ∀ k : ℕ, ζ ^ ((p ^ h) ^ k) = ζ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, h1 ζ hζ]
  conv_lhs => rw [← Nat.div_add_mod e h, pow_add, pow_mul, pow_mul, h2]

/- English proof (translation)
Establish `hp0 : 0 < p` using `by omega`. Establish `hN : p ^ h - 1 ≠ 0`. Use `Nat.one_lt_pow hh.ne' hp` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hζ0 : ζ ≠ 0` using `hζ.ne_zero hN`.

Rewrite using `[ZMod.natCast_eq_natCast_iff', pow_pow_mod hp0 hζ.pow_eq_one e, pow_pow_mod hp0 hζ.pow_eq_one e']`. Use `⟨fun H => ?_, fun H => by rw [H]⟩` and prove the remaining obligations. Establish `key : ∀ a, a < h → p ^ a - 1 < p ^ h - 1` using `fun a ha => by`. Establish `h1` using `Nat.pow_lt_pow_right hp ha`. Establish `h2` using `Nat.one_le_pow a p hp0`.

Use linear arithmetic over natural numbers and integers. Establish `s : ∀ a, ζ ^ (p ^ a) = ζ ^ (p ^ a - 1) * ζ` using `fun a => by`. Rewrite using `[← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp0)]`. Rewrite `H` using `[s, s]`. Establish `H2` using `hζ.pow_inj (key _ (Nat.mod_lt _ hh)) (key _ (Nat.mod_lt _ hh)) (mul_right_cancel₀ hζ0 H)`.

Establish `h1` using `Nat.one_le_pow (e % h) p hp0`. Establish `h2` using `Nat.one_le_pow (e' % h) p hp0`. Conclude with `Nat.pow_right_injective hp (show p ^ (e % h) = p ^ (e' % h) by omega)`.
-/
theorem pow_pow_eq_iff {p h : ℕ} (hp : 1 < p) (hh : 0 < h) {ζ : C}
    (hζ : IsPrimitiveRoot ζ (p ^ h - 1)) (e e' : ℕ) :
    ζ ^ (p ^ e) = ζ ^ (p ^ e') ↔ (e : ZMod h) = (e' : ZMod h) := by
  have hp0 : 0 < p := by omega
  have hN : p ^ h - 1 ≠ 0 := by
    have := Nat.one_lt_pow hh.ne' hp
    omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
  rw [ZMod.natCast_eq_natCast_iff', pow_pow_mod hp0 hζ.pow_eq_one e,
    pow_pow_mod hp0 hζ.pow_eq_one e']
  refine ⟨fun H => ?_, fun H => by rw [H]⟩
  have key : ∀ a, a < h → p ^ a - 1 < p ^ h - 1 := fun a ha => by
    have h1 := Nat.pow_lt_pow_right hp ha
    have h2 := Nat.one_le_pow a p hp0
    omega
  have s : ∀ a, ζ ^ (p ^ a) = ζ ^ (p ^ a - 1) * ζ := fun a => by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp0)]
  rw [s, s] at H
  have H2 := hζ.pow_inj (key _ (Nat.mod_lt _ hh)) (key _ (Nat.mod_lt _ hh))
    (mul_right_cancel₀ hζ0 H)
  have h1 := Nat.one_le_pow (e % h) p hp0
  have h2 := Nat.one_le_pow (e' % h) p hp0
  exact Nat.pow_right_injective hp (show p ^ (e % h) = p ^ (e' % h) by omega)

/- English proof (translation)
The claim follows from `| 0 => isCurve_zero | n + 1 => isCurve_add G h (isCurve_nsmulF G h n)`.
-/
theorem isCurve_nsmulF (G : LogFGL v d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) :
    ∀ n, IsCurve v (G.nsmulF n ga)
  | 0 => isCurve_zero
  | n + 1 => isCurve_add G h (isCurve_nsmulF G h n)

/- English proof (translation)
The claim follows from `| 0, a => by rw [Nat.cast_zero, zero_smul]; exact lgCurve_zero G a | n + 1, a => by rw [LogFGL.nsmulF, lgCurve_add G (fun b => (h b).1) (fun b => (isCurve_nsmulF G h n b).1), lgCurve_nsmulF G h n a, Nat.cast_succ, add_smul, one_smul, add_comm]`.
-/
theorem lgCurve_nsmulF (G : LogFGL v d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) :
    ∀ n a, G.lgCurve (G.nsmulF n ga) a = (n : C) • G.lgCurve ga a
  | 0, a => by
    rw [Nat.cast_zero, zero_smul]; exact lgCurve_zero G a
  | n + 1, a => by
    rw [LogFGL.nsmulF, lgCurve_add G (fun b => (h b).1) (fun b => (isCurve_nsmulF G h n b).1),
      lgCurve_nsmulF G h n a, Nat.cast_succ, add_smul, one_smul, add_comm]

def muCurve {G : LogFGL v d} {p h : ℕ} {ty : Fin d → ZMod h} (μ : MuAction G p h ty) (z : C)
    (ga : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => subst ga (μ.mul z a)

/- English proof (translation)
Introduce `a` and use `⟨constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun b => (hga b).1) (fun b => (hga b).1) (μ.mul_const z a), psIsInt_iff.2 (mvIsInt_subst v (μ.mul_int z hz a) (fun b => psIsInt_iff.1 (hga b).2) (fun b => (hga b).1))⟩`.
-/
theorem isCurve_muCurve {G : LogFGL v d} {p h : ℕ} {ty : Fin d → ZMod h} (μ : MuAction G p h ty)
    {z : C} (hz : z ^ (p ^ h - 1) = 1) {ga : Fin d → PowerSeries C} (hga : IsCurve v ga) :
    IsCurve v (muCurve μ z ga) := fun a =>
  ⟨constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun b => (hga b).1)
      (fun b => (hga b).1) (μ.mul_const z a),
    psIsInt_iff.2 (mvIsInt_subst v (μ.mul_int z hz a) (fun b => psIsInt_iff.1 (hga b).2)
      (fun b => (hga b).1))⟩

/- English proof (translation)
Establish `hs : HasSubst ga` using `hasSubst_of_constantCoeff_zero fun b => (hga b).1`. Establish `hm : HasSubst (μ.mul z)` using `hasSubst_of_constantCoeff_zero (μ.mul_const z)`. Establish `e` using `subst_comp_subst_apply hm hs (G.lg a)`. Rewrite `e` using `[μ.lg_mul z hz a, subst_smul hs]`. Conclude with `e.symm`.
-/
theorem lgCurve_muCurve {G : LogFGL v d} {p h : ℕ} {ty : Fin d → ZMod h} (μ : MuAction G p h ty)
    {z : C} (hz : z ^ (p ^ h - 1) = 1) {ga : Fin d → PowerSeries C} (hga : IsCurve v ga)
    (a : Fin d) :
    G.lgCurve (muCurve μ z ga) a = (z ^ (p ^ (ty a).val)) • G.lgCurve ga a := by
  have hs : HasSubst ga := hasSubst_of_constantCoeff_zero fun b => (hga b).1
  have hm : HasSubst (μ.mul z) := hasSubst_of_constantCoeff_zero (μ.mul_const z)
  have e := subst_comp_subst_apply hm hs (G.lg a)
  rw [μ.lg_mul z hz a, subst_smul hs] at e
  exact e.symm

/- English proof (translation)
Introduce `H C _ _ _ v p hp hv d h hh ty G μ i u hu hui`. Take `⟨γ, hγ, hγt, hγu⟩` from `H C v p hp hv d G u hu`. Establish `: NeZero h` using `⟨hh.ne'⟩`. Establish `hN : p ^ h - 1 ≠ 0`. Use `Nat.one_lt_pow hh.ne' hp.one_lt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hpN : ¬ p ∣ p ^ h - 1`. Introduce `hd`. Establish `h1 : p ∣ p ^ h` using `dvd_pow_self p hh.ne'`. Establish `h2` using `Nat.dvd_sub h1 hd`.

Rewrite `h2` using `[Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)]`. Conclude with `hp.one_lt.ne' (Nat.dvd_one.1 h2)`. Establish `hN0 : ((p ^ h - 1 : ℕ) : C) ≠ 0` using `Nat.cast_ne_zero.2 hN`. Establish `: NeZero ((p ^ h - 1 : ℕ) : C)` using `⟨hN0⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot C (p ^ h - 1)`.

Establish `hζ0 : ζ ≠ 0` using `hζ.ne_zero hN`. Establish `hpow : ∀ y : C, y ^ (p ^ h - 1) = 1 → ∀ j : ℕ, (y ^ j) ^ (p ^ h - 1) = 1` using `fun y hy j => by`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hy, one_pow]`. Establish `hζi : ζ⁻¹ ^ (p ^ h - 1) = 1` using `by rw [inv_pow, hζ.pow_eq_one, inv_one]`. Set `x : ℕ → C` to `fun j => (ζ⁻¹ ^ (p ^ i.val)) ^ j`.

Establish `hx : ∀ j, IsIntV v (x j)` using `fun j => by`. Unfold `IsIntV`. Rewrite using `[v_eq_zero_of_pow_eq_one hN (hpow _ (hpow _ hζi _) j)]`. Set `g : Fin (p ^ h - 1) → Fin d → PowerSeries C` to `fun j => muCurve μ (ζ ^ (j : ℕ)) (rescaleCurve (x j) γ)`. Establish `hg : ∀ j, IsCurve v (g j)` using `fun j => isCurve_muCurve μ (hpow _ hζ.pow_eq_one _) (isCurve_rescale (hx j) hγ)`.

Take `⟨ε, ⟨hε, hεe⟩, -⟩` from `pt1 C v p hp hv d G (p ^ h - 1) hpN (G.sumF g) (isCurve_sumF G g hg)`. Establish `hlg : ∀ a m, ((p ^ h - 1 : ℕ) : C) * PowerSeries.coeff m (G.lgCurve ε a) = (∑ j ∈ Finset.range (p ^ h - 1), (ζ ^ (p ^ (ty a).val) * ζ⁻¹ ^ (p ^ i.val * m)) ^ j) * PowerSeries.coeff m (G.lgCurve γ a)`. Introduce `a m`. Establish `e` using `congrArg (PowerSeries.coeff m) (lgCurve_nsmulF G hε (p ^ h - 1) a)`. Rewrite `e` using `[hεe, lgCurve_sumF G g hg, map_sum, PowerSeries.coeff_smul, smul_eq_mul]`.

Rewrite using `[← e, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [g]`. Rewrite using `[lgCurve_muCurve μ (hpow _ hζ.pow_eq_one _) (isCurve_rescale (hx j) hγ), lgCurve_rescale G _ (fun b => (hγ b).1), PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_rescale]`. Simplify using `only [x]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hlc : ∀ a n, G.lc p ε n a = if ty a = i + (n : ZMod h) then G.lc p γ n a else 0`. Introduce `a n`. Establish `e` using `hlg a (p ^ n)`. Rewrite `e` using `[← pow_add]`.

Establish `hiff` using `pow_pow_eq_iff hp.one_lt hh hζ (ty a).val (i.val + n)`. Rewrite `hiff` using `[Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]`. Establish `hne : ζ ^ (p ^ (i.val + n)) ≠ 0` using `pow_ne_zero _ hζ0`. Use `split_ifs with hc`. Rewrite `e` using `[hiff.2 hc, inv_pow, mul_inv_cancel₀ hne]`.

Simplify using `only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at e`. Conclude with `mul_left_cancel₀ hN0 e`. Establish `h1 : ζ ^ (p ^ (ty a).val) * ζ⁻¹ ^ (p ^ (i.val + n)) ≠ 1`. Introduce `h1`. Rewrite `h1` using `[inv_pow, mul_inv_eq_one₀ hne]`.

Conclude with `hc (hiff.1 h1)`. Rewrite `e` using `[geom_sum_eq h1, mul_pow, hpow _ hζ.pow_eq_one, hpow _ hζi, mul_one, sub_self, zero_div, zero_mul]`. Conclude with `(mul_eq_zero.1 e).resolve_left hN0`. Use `⟨ε, hε, ⟨fun a m hm => ?_, fun n a ha => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e` using `hlg a m`.

Rewrite `e` using `[hγt a m hm, mul_zero]`. Conclude with `(mul_eq_zero.1 e).resolve_left hN0`. Rewrite using `[hlc, if_neg ha]`. Rewrite using `[tangent_eq_lc_zero G p (fun b => (hε b).1)]`. Use function extensionality and compare the values at `a`.

Rewrite using `[hlc, ← tangent_eq_lc_zero G p (fun b => (hγ b).1), hγu, Nat.cast_zero, add_zero]`. Use `split_ifs with hc`. Both sides reduce to the same expression. Conclude with `(hui a hc).symm`.
-/
theorem typicalCurves_of_type_of_typical_tangents :
  (∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d : ℕ) (G : LogFGL v d) (u : Fin d → C), (∀ a, IsIntV v (u a)) → ∃ γ : Fin d → PowerSeries C, IsCurve v γ ∧ G.IsPTypical p γ ∧ tangent γ = u) →
  TypicalCurveEigenspace := by
  intro H C _ _ _ v p hp hv d h hh ty G μ i u hu hui
  obtain ⟨γ, hγ, hγt, hγu⟩ := H C v p hp hv d G u hu
  have : NeZero h := ⟨hh.ne'⟩
  have hN : p ^ h - 1 ≠ 0 := by
    have := Nat.one_lt_pow hh.ne' hp.one_lt
    omega
  have hpN : ¬ p ∣ p ^ h - 1 := by
    intro hd
    have h1 : p ∣ p ^ h := dvd_pow_self p hh.ne'
    have h2 := Nat.dvd_sub h1 hd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hN0 : ((p ^ h - 1 : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.2 hN
  have : NeZero ((p ^ h - 1 : ℕ) : C) := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C (p ^ h - 1)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
  have hpow : ∀ y : C, y ^ (p ^ h - 1) = 1 → ∀ j : ℕ, (y ^ j) ^ (p ^ h - 1) = 1 := fun y hy j => by
    rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have hζi : ζ⁻¹ ^ (p ^ h - 1) = 1 := by rw [inv_pow, hζ.pow_eq_one, inv_one]
  let x : ℕ → C := fun j => (ζ⁻¹ ^ (p ^ i.val)) ^ j
  have hx : ∀ j, IsIntV v (x j) := fun j => by
    unfold IsIntV
    rw [v_eq_zero_of_pow_eq_one hN (hpow _ (hpow _ hζi _) j)]
  let g : Fin (p ^ h - 1) → Fin d → PowerSeries C := fun j =>
    muCurve μ (ζ ^ (j : ℕ)) (rescaleCurve (x j) γ)
  have hg : ∀ j, IsCurve v (g j) := fun j =>
    isCurve_muCurve μ (hpow _ hζ.pow_eq_one _) (isCurve_rescale (hx j) hγ)
  obtain ⟨ε, ⟨hε, hεe⟩, -⟩ := pt1 C v p hp hv d G (p ^ h - 1) hpN (G.sumF g) (isCurve_sumF G g hg)
  have hlg : ∀ a m, ((p ^ h - 1 : ℕ) : C) * PowerSeries.coeff m (G.lgCurve ε a) =
      (∑ j ∈ Finset.range (p ^ h - 1), (ζ ^ (p ^ (ty a).val) * ζ⁻¹ ^ (p ^ i.val * m)) ^ j) *
        PowerSeries.coeff m (G.lgCurve γ a) := by
    intro a m
    have e := congrArg (PowerSeries.coeff m) (lgCurve_nsmulF G hε (p ^ h - 1) a)
    rw [hεe, lgCurve_sumF G g hg, map_sum, PowerSeries.coeff_smul, smul_eq_mul] at e
    rw [← e, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [g]
    rw [lgCurve_muCurve μ (hpow _ hζ.pow_eq_one _) (isCurve_rescale (hx j) hγ),
      lgCurve_rescale G _ (fun b => (hγ b).1), PowerSeries.coeff_smul, smul_eq_mul,
      PowerSeries.coeff_rescale]
    simp only [x]
    ring
  have hlc : ∀ a n, G.lc p ε n a = if ty a = i + (n : ZMod h) then G.lc p γ n a else 0 := by
    intro a n
    have e := hlg a (p ^ n)
    rw [← pow_add] at e
    have hiff := pow_pow_eq_iff hp.one_lt hh hζ (ty a).val (i.val + n)
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hiff
    have hne : ζ ^ (p ^ (i.val + n)) ≠ 0 := pow_ne_zero _ hζ0
    split_ifs with hc
    · rw [hiff.2 hc, inv_pow, mul_inv_cancel₀ hne] at e
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at e
      exact mul_left_cancel₀ hN0 e
    · have h1 : ζ ^ (p ^ (ty a).val) * ζ⁻¹ ^ (p ^ (i.val + n)) ≠ 1 := by
        intro h1
        rw [inv_pow, mul_inv_eq_one₀ hne] at h1
        exact hc (hiff.1 h1)
      rw [geom_sum_eq h1, mul_pow, hpow _ hζ.pow_eq_one, hpow _ hζi, mul_one, sub_self, zero_div,
        zero_mul] at e
      exact (mul_eq_zero.1 e).resolve_left hN0
  refine ⟨ε, hε, ⟨fun a m hm => ?_, fun n a ha => ?_⟩, ?_⟩
  · have e := hlg a m
    rw [hγt a m hm, mul_zero] at e
    exact (mul_eq_zero.1 e).resolve_left hN0
  · rw [hlc, if_neg ha]
  · rw [tangent_eq_lc_zero G p (fun b => (hε b).1)]
    funext a
    rw [hlc, ← tangent_eq_lc_zero G p (fun b => (hγ b).1), hγu, Nat.cast_zero, add_zero]
    split_ifs with hc
    · rfl
    · exact (hui a hc).symm

end

end GlobalTheory.TypicalCurve
