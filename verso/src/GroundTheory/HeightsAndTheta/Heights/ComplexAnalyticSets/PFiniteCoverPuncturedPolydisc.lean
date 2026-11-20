import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteCoverPuncturedPolydisc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology Complex
open scoped Real

noncomputable section

namespace FiniteCoverPuncturedPolydisc

variable {e : ℕ}

def strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) : Set (Fin (e + 1) → ℂ) :=
  {u | (u 0).re < Real.log ρ ∧ ∀ i, i ≠ 0 → dist (u i) (c i) < ρ}

/- English proof (translation)
Introduce `x hx y hy a b ha hb hab`. Use `⟨?_, fun i hi => ?_⟩` and prove the remaining obligations. Use `convex_halfSpace_re_lt (r := Real.log ρ) hx.1 hy.1 ha hb hab` as an intermediate fact. Simplify using `using this`. Use `convex_ball (c i) ρ (hx.2 i hi) (hy.2 i hi) ha hb hab` as an intermediate fact.

Simplify `this` using `[Metric.mem_ball]`.
-/
theorem convex_strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) : Convex ℝ (strip c ρ) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, fun i hi => ?_⟩
  · have := convex_halfSpace_re_lt (r := Real.log ρ) hx.1 hy.1 ha hb hab
    simpa using this
  · have := convex_ball (c i) ρ (hx.2 i hi) (hy.2 i hi) ha hb hab
    simpa [Metric.mem_ball] using this

/- English proof (translation)
Establish `h1 : IsOpen {u : Fin (e + 1) → ℂ | (u 0).re < Real.log ρ}` using `isOpen_lt (continuous_re.comp (continuous_apply 0)) continuous_const`. Establish `h2 : IsOpen {u : Fin (e + 1) → ℂ | ∀ i, i ≠ 0 → dist (u i) (c i) < ρ}`. Establish `: {u : Fin (e + 1) → ℂ | ∀ i, i ≠ 0 → dist (u i) (c i) < ρ} = ⋂ i ∈ ({0}ᶜ : Finset (Fin (e + 1))), {u | dist (u i) (c i) < ρ}`. Use extensionality with `u`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `isOpen_biInter_finset fun i _ => isOpen_lt ((continuous_apply i).dist continuous_const) continuous_const`. Conclude with `h1.inter h2`.
-/
theorem isOpen_strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) : IsOpen (strip c ρ) := by
  have h1 : IsOpen {u : Fin (e + 1) → ℂ | (u 0).re < Real.log ρ} :=
    isOpen_lt (continuous_re.comp (continuous_apply 0)) continuous_const
  have h2 : IsOpen {u : Fin (e + 1) → ℂ | ∀ i, i ≠ 0 → dist (u i) (c i) < ρ} := by
    have : {u : Fin (e + 1) → ℂ | ∀ i, i ≠ 0 → dist (u i) (c i) < ρ} =
        ⋂ i ∈ ({0}ᶜ : Finset (Fin (e + 1))), {u | dist (u i) (c i) < ρ} := by
      ext u; simp
    rw [this]
    exact isOpen_biInter_finset fun i _ =>
      isOpen_lt ((continuous_apply i).dist continuous_const) continuous_const
  exact h1.inter h2

/- English proof (translation)
Use `⟨by simp, fun i hi => ?_⟩` and prove the remaining obligations. Simplify using `[Function.update_of_ne hi, hρ]`.
-/
theorem base_mem_strip (c : Fin (e + 1) → ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Function.update c 0 ((Real.log ρ - 1 : ℝ) : ℂ) ∈ strip c ρ := by
  refine ⟨by simp, fun i hi => ?_⟩
  simp [Function.update_of_ne hi, hρ]

instance simplyConnected_strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) [Fact (0 < ρ)] :
    SimplyConnectedSpace (strip c ρ) := by
  have := (convex_strip c ρ).contractibleSpace ⟨_, base_mem_strip c (Fact.out : 0 < ρ)⟩
  infer_instance

instance locPathConnected_strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) :
    LocallyPathConnectedSpace (strip c ρ) :=
  (isOpen_strip c ρ).locallyPathConnectedSpace

def shift (c : Fin (e + 1) → ℂ) (ρ : ℝ) (k : ℤ) (u : strip c ρ) : strip c ρ :=
  ⟨Function.update u.1 0 (u.1 0 + k * (2 * π * I)), by
    refine ⟨by simpa using u.2.1, fun i hi => ?_⟩
    rw [Function.update_of_ne hi]
    exact u.2.2 i hi⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shift_val (c : Fin (e + 1) → ℂ) (ρ : ℝ) (k : ℤ) (u : strip c ρ) :
    (shift c ρ k u).1 = Function.update u.1 0 (u.1 0 + k * (2 * π * I)) := rfl

/- English proof (translation)
Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Conclude with `continuous_subtype_val.update 0 (((continuous_apply 0).comp continuous_subtype_val).add continuous_const)`.
-/
theorem continuous_shift (c : Fin (e + 1) → ℂ) (ρ : ℝ) (k : ℤ) : Continuous (shift c ρ k) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_subtype_val.update 0
    (((continuous_apply 0).comp continuous_subtype_val).add continuous_const)

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [shift_val, Function.update_self, Function.update_idem]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shift_shift (c : Fin (e + 1) → ℂ) (ρ : ℝ) (k l : ℤ) (u : strip c ρ) :
    shift c ρ k (shift c ρ l u) = shift c ρ (k + l) u := by
  apply Subtype.ext
  simp only [shift_val, Function.update_self, Function.update_idem]
  congr 1
  push_cast; ring

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[shift_val]`.
-/
theorem shift_zero (c : Fin (e + 1) → ℂ) (ρ : ℝ) (u : strip c ρ) : shift c ρ 0 u = u := by
  apply Subtype.ext
  simp [shift_val]

variable {c : Fin (e + 1) → ℂ} {r : ℝ}

/- English proof (translation)
Use `⟨?_, by simp [exp_ne_zero]⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_ball, dist_pi_lt_iff (hρ.trans_le hρr)]`. Introduce `i`. Break down `eq_or_ne i 0 with rfl | hi` into its components or cases. Simplify using `only [Function.update_self, hc, dist_zero_right, norm_exp]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Function.update_of_ne hi]`. Conclude with `(u.2.2 i hi).trans_le hρr`.
-/
theorem expMap_mem (hc : c 0 = 0) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (u : strip c ρ) :
    Function.update u.1 0 (exp (u.1 0)) ∈ Metric.ball c r ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0} := by
  refine ⟨?_, by simp [exp_ne_zero]⟩
  rw [Metric.mem_ball, dist_pi_lt_iff (hρ.trans_le hρr)]
  intro i
  rcases eq_or_ne i 0 with rfl | hi
  · simp only [Function.update_self, hc, dist_zero_right, norm_exp]
    calc Real.exp (u.1 0).re < Real.exp (Real.log ρ) := Real.exp_lt_exp.2 u.2.1
      _ = ρ := Real.exp_log hρ
      _ ≤ r := hρr
  · rw [Function.update_of_ne hi]
    exact (u.2.2 i hi).trans_le hρr

def expMap (hc : c 0 = 0) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    C(strip c ρ, ↥(Metric.ball c r ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0})) where
  toFun u := ⟨Function.update u.1 0 (exp (u.1 0)), expMap_mem hc hρ hρr u⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.update 0 (((continuous_apply 0).comp continuous_subtype_val).cexp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem expMap_val (hc : c 0 = 0) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (u : strip c ρ) :
    ((expMap hc hρ hρr u : _) : Fin (e + 1) → ℂ) = Function.update u.1 0 (exp (u.1 0)) := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[expMap_val, expMap_val, shift_val]`. Simplify using `only [Function.update_self, Function.update_idem, exp_add, exp_int_mul_two_pi_mul_I, mul_one]`.
-/
theorem expMap_shift (hc : c 0 = 0) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (k : ℤ) (u : strip c ρ) :
    expMap hc hρ hρr (shift c ρ k u) = expMap hc hρ hρr u := by
  apply Subtype.ext
  rw [expMap_val, expMap_val, shift_val]
  simp only [Function.update_self, Function.update_idem, exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/- English proof (translation)
Establish `ht0 : t 0 ≠ 0` using `hw ▸ exp_ne_zero w`. Establish `hnorm : ‖t 0‖ < ρ`. Use `(dist_le_pi_dist t c 0).trans_lt ht` as an intermediate fact. Simplify `this` using `[hc]`. Establish `hre : w.re = Real.log ‖t 0‖` using `by rw [← hw, norm_exp, Real.log_exp]`.

Establish `hlog : Real.log ‖t 0‖ < Real.log ρ` using `Real.log_lt_log (norm_pos_iff.2 ht0) hnorm`. Establish `hlogρ : Real.log ρ ≤ 0` using `Real.log_nonpos hρ0.le hρ1`. Use `⟨?_, fun i hi => ?_⟩` and prove the remaining obligations. Simplify using `only [Function.update_self, mul_re, natCast_re, natCast_im, zero_mul, sub_zero, hre]`. Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`.

Use polynomial arithmetic with `[mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hk') (hlog.trans_le hlogρ).le]`. Rewrite using `[Function.update_of_ne hi]`. Conclude with `(dist_le_pi_dist t c i).trans_lt ht`.
-/
theorem mem_strip_of_exp (hc : c 0 = 0) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {t : Fin (e + 1) → ℂ}
    (ht : t ∈ Metric.ball c ρ) {w : ℂ} (hw : exp w = t 0) {k : ℕ} (hk : 1 ≤ k) :
    Function.update t 0 (k * w) ∈ strip c ρ := by
  have ht0 : t 0 ≠ 0 := hw ▸ exp_ne_zero w
  have hnorm : ‖t 0‖ < ρ := by
    have := (dist_le_pi_dist t c 0).trans_lt ht
    simpa [hc] using this
  have hre : w.re = Real.log ‖t 0‖ := by rw [← hw, norm_exp, Real.log_exp]
  have hlog : Real.log ‖t 0‖ < Real.log ρ := Real.log_lt_log (norm_pos_iff.2 ht0) hnorm
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [Function.update_self, mul_re, natCast_re, natCast_im, zero_mul, sub_zero, hre]
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hk') (hlog.trans_le hlogρ).le]
  · rw [Function.update_of_ne hi]
    exact (dist_le_pi_dist t c i).trans_lt ht

end FiniteCoverPuncturedPolydisc

open FiniteCoverPuncturedPolydisc in

/- English proof (translation)
Introduce `e N c r Y _ p hr hc hcov hfib`. Take `⟨ρ, hρ0, hρr, hρ1⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ρ ≤ 1` from `⟨min r 1, lt_min hr one_pos, min_le_left _ _, min_le_right _ _⟩`. Establish `: Fact (0 < ρ)` using `⟨hρ0⟩`. Set `E` to `expMap hc hρ0 hρr`. Set `u₀ : strip c ρ` to `⟨_, base_mem_strip c hρ0⟩`.

Establish `hlift : ∀ (a : strip c ρ) (y : Y), p y = E a → ∃ G : C(strip c ρ, Y), G a = y ∧ p ∘ G = E` using `fun a y h => (hcov.existsUnique_continuousMap_lifts E a y h).exists`. Establish `huniq : ∀ G₁ G₂ : C(strip c ρ, Y), p ∘ G₁ = E → p ∘ G₂ = E → ∀ a, G₁ a = G₂ a → G₁ = G₂` using `fun G₁ G₂ h1 h2 a ha => ContinuousMap.ext (congrFun (hcov.eq_of_comp_eq G₁.continuous G₂.continuous (h1.trans h2.symm) a ha))`. Set `F : Set Y` to `p ⁻¹' {E u₀}`. Establish `hFfin : F.Finite` using `Set.finite_of_encard_eq_coe (hfib (E u₀))`. Establish `: Finite F` using `hFfin.to_subtype`.

Use `letI : Fintype F := Fintype.ofFinite F`. Establish `hcardF : Nat.card F = N`. Rewrite using `[Nat.card_coe_set_eq, Set.ncard_def, hfib]`. Simplify using the standard rewrite rules. Set `L : F → C(strip c ρ, Y)` to `fun y => Classical.choose (hlift u₀ y.1 y.2)`.

Establish `hL0 : ∀ y : F, L y u₀ = y.1` using `fun y => (Classical.choose_spec (hlift u₀ y.1 y.2)).1`. Establish `hLp : ∀ y : F, p ∘ L y = E` using `fun y => (Classical.choose_spec (hlift u₀ y.1 y.2)).2`. Establish `hLp' : ∀ y : F, ∀ a, p (L y a) = E a` using `fun y a => congrFun (hLp y) a`. Establish `hLinj : ∀ y y' : F, ∀ a, L y a = L y' a → y = y'`. Introduce `y y' a h`.

Use `huniq (L y) (L y') (hLp y) (hLp y') a h` as an intermediate fact. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hL0 y, ← hL0 y', this]`. Establish `hfibre : ∀ a (y : Y), p y = E a → ∃ y' : F, L y' a = y`. Introduce `a y h`.

Take `⟨G, hGa, hGp⟩` from `hlift a y h`. Establish `hG0 : G u₀ ∈ F` using `by show p (G u₀) ∈ ({E u₀} : Set _)`. Rewrite using `[← Function.comp_apply (f := p), hGp]`. Both sides reduce to the same expression. Use `⟨⟨G u₀, hG0⟩, ?_⟩` and prove the remaining obligations.

Use `huniq G (L ⟨G u₀, hG0⟩) hGp (hLp _) u₀ (hL0 ⟨G u₀, hG0⟩).symm` as an intermediate fact. Rewrite using `[← this, hGa]`. Establish `hEshift : ∀ k a, E (shift c ρ k a) = E a` using `expMap_shift hc hρ0 hρr`. Establish `hs_mem : ∀ y : F, L y (shift c ρ 1 u₀) ∈ F`. Introduce `y`.

Use `show p _ ∈ ({E u₀} : Set _)`. Rewrite using `[hLp', hEshift]`. Both sides reduce to the same expression. Set `s : F → F` to `fun y => ⟨_, hs_mem y⟩`. Establish `hLs : ∀ y : F, ∀ a, L y (shift c ρ 1 a) = L (s y) a`.

Introduce `y a`. Use `huniq ((L y).comp ⟨shift c ρ 1, continuous_shift c ρ 1⟩) (L (s y)) (by funext a; simp [hLp', hEshift]) (hLp _) u₀ (by rw [hL0]; rfl)` as an intermediate fact. Conclude with `DFunLike.congr_fun this a`. Establish `hs_inj : Function.Injective s`. Introduce `y y' h`.

Apply `hLinj y y' u₀` to reduce the goal to its premises. Establish `e1 : shift c ρ 1 (shift c ρ (-1) u₀) = u₀`. Rewrite using `[shift_shift]`. Simplify using `[shift_zero]`. Rewrite using `[← e1, hLs, hLs, h]`.

Set `σ : Equiv.Perm F` to `Equiv.ofBijective s (Finite.injective_iff_bijective.mp hs_inj)`. Establish `hσ : ∀ y, σ y = s y` using `fun y => rfl`. Establish `hLσ : ∀ k : ℤ, ∀ y : F, ∀ a, L y (shift c ρ k a) = L ((σ ^ k) y) a`. Introduce `k`. Proceed by induction on `k using Int.induction_on with`.

Consider the case `zero => intro y a`. Simplify using `[shift_zero]`. Consider the case `succ k ih`. Introduce `y a`. Use `conv_lhs => rw [show ((k : ℤ) + 1) = 1 + k by ring, ← shift_shift c ρ 1 k]`.

Rewrite using `[hLs, ih, zpow_add_one, Equiv.Perm.mul_apply, hσ]`. Consider the case `pred k ih`. Introduce `y a`. Establish `hy : y = s (σ⁻¹ y)` using `by rw [← hσ]; simp`. Use `conv_lhs => rw [hy]`.

Rewrite using `[← hLs, shift_shift, show (1 : ℤ) + (-↑k - 1) = -↑k by ring, ih, zpow_sub_one, Equiv.Perm.mul_apply]`. Set `Q` to `MulAction.orbitRel.Quotient (Subgroup.zpowers σ) F`. Use `letI : Fintype Q := Fintype.ofFinite Q`. Set `m` to `Nat.card Q`. Set `eQ : Fin m ≃ Q` to `(Finite.equivFin Q).symm`.

Set `rep : Fin m → F` to `fun b => (eQ b).out`. Set `ord : Fin m → ℕ` to `fun b => Function.minimalPeriod (σ • ·) (rep b)`. Establish `hper : ∀ b (k : ℤ), (σ ^ k) (rep b) = rep b ↔ (ord b : ℤ) ∣ k`. Introduce `b k`. Rewrite using `[← Equiv.Perm.smul_def]`.

Conclude with `MulAction.zpow_smul_eq_iff_minimalPeriod_dvd`. Establish `hord : ∀ b, 1 ≤ ord b`. Introduce `b`. Establish `: Finite (MulAction.orbit (Subgroup.zpowers σ) (rep b))` using `Subtype.finite`. Conclude with `Nat.one_le_iff_ne_zero.2 (NeZero.ne (Function.minimalPeriod (σ • ·) (rep b)))`.

Establish `hsame : ∀ b b' (k : ℤ), rep b = (σ ^ k) (rep b') → b = b'`. Introduce `b b' k h`. Apply `eQ.injective` to reduce the goal to its premises. Rewrite using `[← Quotient.out_eq (eQ b), ← Quotient.out_eq (eQ b')]`. Apply `Quotient.sound` to reduce the goal to its premises.

Use `show MulAction.orbitRel _ _ (rep b) (rep b')`. Rewrite using `[MulAction.orbitRel_apply, MulAction.mem_orbit_iff]`. Conclude with `⟨⟨σ ^ k, Subgroup.zpow_mem_zpowers σ k⟩, h.symm⟩`. Establish `hrep : ∀ y : F, ∃ b, ∃ k : ℤ, y = (σ ^ k) (rep b)`. Introduce `y`.

Use `⟨eQ.symm ⟦y⟧, ?_⟩` and prove the remaining obligations. Establish `h1 : rep (eQ.symm ⟦y⟧) = (⟦y⟧ : Q).out` using `by simp [rep]`. Establish `h2` using `Quotient.mk_out (s := MulAction.orbitRel (Subgroup.zpowers σ) F) y`. Establish `h3 : (⟦y⟧ : Q).out ∈ MulAction.orbit (Subgroup.zpowers σ) y`. Rewrite using `[← MulAction.orbitRel_apply]`.

Conclude with `h2`. Take `⟨⟨g, hg⟩, hgy⟩` from `MulAction.mem_orbit_iff.1 h3`. Take `⟨j, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hg`. Use `⟨-j, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, ← hgy]`.

Simplify using `[zpow_neg, Equiv.Perm.smul_def]`. Establish `hsum : ∑ b, ord b = N`. Rewrite using `[← hcardF]`. Establish `h1 : ∑ b, ord b = ∑ q : Q, Function.minimalPeriod (σ • ·) q.out` using `Equiv.sum_comp eQ (fun q => Function.minimalPeriod (σ • ·) q.out)`. Establish `h2 : ∀ q : Q, Function.minimalPeriod (σ • ·) q.out = Nat.card (MulAction.orbit (Subgroup.zpowers σ) q.out)`.

Introduce `q`. Rewrite using `[MulAction.minimalPeriod_eq_card, Nat.card_eq_fintype_card]`. Rewrite using `[h1, Finset.sum_congr rfl (fun q _ => h2 q), Nat.card_congr (MulAction.selfEquivSigmaOrbits (Subgroup.zpowers σ) F), Nat.card_sigma]`. Establish `hpt : ∀ b (t : ↥(Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0})) (w : ℂ), exp w = t.1 0 → Function.update t.1 0 (ord b * w) ∈ strip c ρ` using `fun b t w hw => mem_strip_of_exp hc hρ0 hρ1 t.2.1 hw (hord b)`. Set `ψ : Fin m → ↥(Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0}) → Y` to `fun b t => L (rep b) ⟨_, hpt b t (log (t.1 0)) (exp_log t.2.2)⟩`.

Establish `hψw : ∀ b t w (hw : exp w = t.1 0), ψ b t = L (rep b) ⟨_, hpt b t w hw⟩`. Introduce `b t w hw`. Take `⟨n, hn⟩` from `exp_eq_exp_iff_exists_int.1 (hw.trans (exp_log t.2.2).symm)`. Establish `hsh : (⟨_, hpt b t w hw⟩ : strip c ρ) = shift c ρ (ord b * n) ⟨_, hpt b t (log (t.1 0)) (exp_log t.2.2)⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [shift_val, Function.update_self, Function.update_idem, hn]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsh, hLσ, (hper b _).2 (dvd_mul_right _ _)]`.

Establish `hψcont : ∀ b, Continuous (ψ b)`. Introduce `b`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `t₁`. Establish `hz : t₁.1 0 ≠ 0` using `t₁.2.2`.

Establish `hw : ∀ t : ↥(Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0}), exp (log (t₁.1 0) + log (t.1 0 / t₁.1 0)) = t.1 0`. Introduce `t`. Rewrite using `[exp_add, exp_log hz, exp_log (div_ne_zero t.2.2 hz)]`. Clear the denominators using the available nonvanishing facts. Establish `heq : ψ b = fun t => L (rep b) ⟨_, hpt b t _ (hw t)⟩` using `funext fun t => hψw b t _ (hw t)`.

Rewrite using `[heq]`. Apply `(L (rep b)).continuous.continuousAt.comp` to reduce the goal to its premises. Rewrite using `[Topology.IsInducing.subtypeVal.continuousAt_iff]`. Apply `continuousAt_subtype_val.update 0` to reduce the goal to its premises. Apply `continuousAt_const.mul` to reduce the goal to its premises.

Apply `continuousAt_const.add` to reduce the goal to its premises. Apply `ContinuousAt.clog` to reduce the goal to its premises. Conclude with `(((continuous_apply 0).comp continuous_subtype_val).div_const _).continuousAt`. Simplify using `[div_self hz]`. Establish `hpψ : ∀ b t, ((p (ψ b t) : Fin (e + 1) → ℂ)) = Function.update t.1 0 (t.1 0 ^ ord b)`.

Introduce `b t`. Use `show ((p (L (rep b) _) : Fin (e + 1) → ℂ)) = _`. Rewrite using `[hLp', expMap_val]`. Simplify using `only [Function.update_self, Function.update_idem, exp_nat_mul, exp_log t.2.2]`. Establish `hrest : ∀ b b' t t', ψ b t = ψ b' t' → (∀ i, i ≠ 0 → t.1 i = t'.1 i) ∧ t.1 0 ^ ord b = t'.1 0 ^ ord b'`.

Introduce `b b' t t' h`. Establish `hp` using `congrArg (fun y => ((p y : Fin (e + 1) → ℂ))) h`. Simplify using `only [hpψ] at hp`. Use `⟨fun i hi => ?_, by simpa using congrFun hp 0⟩` and prove the remaining obligations. Use `congrFun hp i` as an intermediate fact.

Simplify `this` using `[Function.update_of_ne hi]`. Establish `hmeet : ∀ b b' t t', ψ b t = ψ b' t' → ∃ n : ℤ, (ord b' : ℂ) * log (t'.1 0) = ord b * log (t.1 0) + n * (2 * π * I) ∧ rep b = (σ ^ n) (rep b')`. Introduce `b b' t t' h`. Take `⟨hr', h0⟩` from `hrest b b' t t' h`. Establish `hexp : exp (ord b' * log (t'.1 0)) = exp (ord b * log (t.1 0))`.

Rewrite using `[exp_nat_mul, exp_nat_mul, exp_log t.2.2, exp_log t'.2.2, h0]`. Take `⟨n, hn⟩` from `exp_eq_exp_iff_exists_int.1 hexp`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Establish `hsh : (⟨_, hpt b' t' (log (t'.1 0)) (exp_log t'.2.2)⟩ : strip c ρ) = shift c ρ n ⟨_, hpt b t (log (t.1 0)) (exp_log t.2.2)⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Break down `eq_or_ne i 0 with rfl | hi` into its components or cases. Simplify using `[shift_val, hn]`. Simplify using `[shift_val, Function.update_of_ne hi, hr' i hi]`. Establish `h2 : ψ b' t' = L ((σ ^ n) (rep b')) ⟨_, hpt b t _ (exp_log t.2.2)⟩` using `by show L (rep b') _ = _`.

Rewrite using `[hsh, hLσ]`. Conclude with `hLinj (rep b) ((σ ^ n) (rep b')) _ (h.trans h2)`. Establish `hψinj : ∀ b, Function.Injective (ψ b)`. Introduce `b t t' h`. Take `⟨hr', -⟩` from `hrest b b t t' h`.

Take `⟨n, hn, h3⟩` from `hmeet b b t t' h`. Take `⟨j, hj⟩` from `(hper b n).1 h3.symm`. Establish `hm0 : (ord b : ℂ) ≠ 0`. Establish `: ord b ≠ 0` using `Nat.one_le_iff_ne_zero.1 (hord b)`. Conclude with `this` after adjusting the coercions.

Establish `hlog : log (t'.1 0) = log (t.1 0) + j * (2 * π * I)`. Apply `mul_left_cancel₀ hm0` to reduce the goal to its premises. Rewrite using `[hn, hj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Break down `eq_or_ne i 0 with rfl | hi` into its components or cases. Rewrite using `[← exp_log t.2.2, ← exp_log t'.2.2, hlog, exp_add, exp_int_mul_two_pi_mul_I, mul_one]`. Conclude with `hr' i hi`.

Establish `hψdisj : ∀ b b', b ≠ b' → ∀ t t', ψ b t ≠ ψ b' t'`. Introduce `b b' hbb t t' h`. Take `⟨n, -, h3⟩` from `hmeet b b' t t' h`. Conclude with `hbb (hsame b b' n h3)`. Establish `hcover : ∀ y, dist ((p y : Fin (e + 1) → ℂ)) c < ρ ^ N → ∃ b t, ψ b t = y`.

Introduce `y hy`. Establish `hs0 : (p y : Fin (e + 1) → ℂ) 0 ≠ 0` using `(p y).2.2`. Establish `hN : N ≠ 0`. Introduce `hN0`. Use `hfib (p y)` as an intermediate fact.

Rewrite `this` using `[hN0, Nat.cast_zero, Set.encard_eq_zero]`. Conclude with `(Set.eq_empty_iff_forall_notMem.1 this) y rfl`. Establish `hρN : ρ ^ N ≤ ρ` using `pow_le_of_le_one hρ0.le hρ1 hN`. Establish `hsball : (p y : Fin (e + 1) → ℂ) ∈ Metric.ball c ρ` using `Metric.mem_ball.2 (hy.trans_le hρN)`. Set `a : strip c ρ` to `⟨_, mem_strip_of_exp hc hρ0 hρ1 hsball (exp_log hs0) le_rfl⟩`.

Establish `hEa : p y = E a`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[expMap_val]`. Simplify using `[a, exp_log hs0]`. Take `⟨y', hy'⟩` from `hfibre a y hEa`.

Take `⟨b, k, hk⟩` from `hrep y'`. Establish `hm1` using `hord b`. Establish `hm0 : (ord b : ℂ) ≠ 0`. Establish `: ord b ≠ 0` using `Nat.one_le_iff_ne_zero.1 hm1`. Conclude with `this` after adjusting the coercions.

Set `w : ℂ` to `(log ((p y : Fin (e + 1) → ℂ) 0) + k * (2 * π * I)) / ord b`. Establish `hmw : (ord b : ℂ) * w = log ((p y : Fin (e + 1) → ℂ) 0) + k * (2 * π * I)`. Simplify using `only [w]`. Clear the denominators using the available nonvanishing facts. Set `t : Fin (e + 1) → ℂ` to `Function.update (p y : Fin (e + 1) → ℂ) 0 (exp w)`.

Establish `hmN : ord b ≤ N` using `hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)`. Establish `ht : t ∈ Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0}`. Use `⟨?_, by simp [t, exp_ne_zero]⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_ball, dist_pi_lt_iff hρ0]`. Introduce `i`.

Break down `eq_or_ne i 0 with rfl | hi` into its components or cases. Simplify using `only [t, Function.update_self, hc, dist_zero_right, norm_exp]`. Establish `hre : (ord b : ℝ) * w.re = Real.log ‖(p y : Fin (e + 1) → ℂ) 0‖`. Use `congrArg re hmw` as an intermediate fact. Simplify `this` using `[mul_re, log_re]`.

Establish `hsn : ‖(p y : Fin (e + 1) → ℂ) 0‖ < ρ ^ N`. Simplify `(dist_le_pi_dist _ c 0).trans_lt hy` using `[hc]`. Establish `hl : Real.log ‖(p y : Fin (e + 1) → ℂ) 0‖ < N * Real.log ρ`. Rewrite using `[← Real.log_pow]`. Conclude with `Real.log_lt_log (norm_pos_iff.2 hs0) hsn`.

Establish `hlogρ : Real.log ρ ≤ 0` using `Real.log_nonpos hρ0.le hρ1`. Establish `hmpos : (0 : ℝ) < ord b` using `by exact_mod_cast hm1`. Establish `hmN' : (ord b : ℝ) ≤ N` using `by exact_mod_cast hmN`. Establish `hlt : w.re < Real.log ρ`. Assume the negation of the conclusion as `hcon`.

Use `replace hcon := not_lt.1 hcon`. Use polynomial arithmetic with `[mul_le_mul_of_nonpos_right hmN' hlogρ, mul_le_mul_of_nonneg_left hcon hmpos.le]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [t, Function.update_of_ne hi]`. Conclude with `((dist_le_pi_dist _ c i).trans_lt hy).trans_le hρN`.

Use `⟨b, ⟨t, ht⟩, ?_⟩` and prove the remaining obligations. Establish `hwt : exp w = (⟨t, ht⟩ : ↥(Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0})).1 0`. Simplify using `[t]`. Rewrite using `[hψw b ⟨t, ht⟩ w hwt]`. Establish `hsh : (⟨_, hpt b ⟨t, ht⟩ w hwt⟩ : strip c ρ) = shift c ρ k a`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [shift_val, a, t, Function.update_idem, Function.update_self, hmw, Nat.cast_one, one_mul]`. Rewrite using `[hsh, hLσ, ← hk, hy']`. Conclude with `⟨m, ord, ρ, ψ, hρ0, hρ1, hsum, hord, hψcont, hpψ, hψinj, hψdisj, hcover⟩`.
-/
theorem FiniteCoverPuncturedPolydisc.proof : FiniteCoverPuncturedPolydisc.Statement := by
  intro e N c r Y _ p hr hc hcov hfib
  classical
  obtain ⟨ρ, hρ0, hρr, hρ1⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ρ ≤ 1 :=
    ⟨min r 1, lt_min hr one_pos, min_le_left _ _, min_le_right _ _⟩
  have : Fact (0 < ρ) := ⟨hρ0⟩
  let E := expMap hc hρ0 hρr
  let u₀ : strip c ρ := ⟨_, base_mem_strip c hρ0⟩

  have hlift : ∀ (a : strip c ρ) (y : Y), p y = E a →
      ∃ G : C(strip c ρ, Y), G a = y ∧ p ∘ G = E :=
    fun a y h => (hcov.existsUnique_continuousMap_lifts E a y h).exists
  have huniq : ∀ G₁ G₂ : C(strip c ρ, Y), p ∘ G₁ = E → p ∘ G₂ = E → ∀ a, G₁ a = G₂ a → G₁ = G₂ :=
    fun G₁ G₂ h1 h2 a ha => ContinuousMap.ext
      (congrFun (hcov.eq_of_comp_eq G₁.continuous G₂.continuous (h1.trans h2.symm) a ha))

  let F : Set Y := p ⁻¹' {E u₀}
  have hFfin : F.Finite := Set.finite_of_encard_eq_coe (hfib (E u₀))
  have : Finite F := hFfin.to_subtype
  letI : Fintype F := Fintype.ofFinite F
  have hcardF : Nat.card F = N := by
    rw [Nat.card_coe_set_eq, Set.ncard_def, hfib]
    simp
  let L : F → C(strip c ρ, Y) := fun y => Classical.choose (hlift u₀ y.1 y.2)
  have hL0 : ∀ y : F, L y u₀ = y.1 := fun y => (Classical.choose_spec (hlift u₀ y.1 y.2)).1
  have hLp : ∀ y : F, p ∘ L y = E := fun y => (Classical.choose_spec (hlift u₀ y.1 y.2)).2
  have hLp' : ∀ y : F, ∀ a, p (L y a) = E a := fun y a => congrFun (hLp y) a
  have hLinj : ∀ y y' : F, ∀ a, L y a = L y' a → y = y' := by
    intro y y' a h
    have := huniq (L y) (L y') (hLp y) (hLp y') a h
    apply Subtype.ext
    rw [← hL0 y, ← hL0 y', this]
  have hfibre : ∀ a (y : Y), p y = E a → ∃ y' : F, L y' a = y := by
    intro a y h
    obtain ⟨G, hGa, hGp⟩ := hlift a y h
    have hG0 : G u₀ ∈ F := by
      show p (G u₀) ∈ ({E u₀} : Set _)
      rw [← Function.comp_apply (f := p), hGp]
      rfl
    refine ⟨⟨G u₀, hG0⟩, ?_⟩
    have := huniq G (L ⟨G u₀, hG0⟩) hGp (hLp _) u₀ (hL0 ⟨G u₀, hG0⟩).symm
    rw [← this, hGa]
  have hEshift : ∀ k a, E (shift c ρ k a) = E a := expMap_shift hc hρ0 hρr

  have hs_mem : ∀ y : F, L y (shift c ρ 1 u₀) ∈ F := by
    intro y
    show p _ ∈ ({E u₀} : Set _)
    rw [hLp', hEshift]
    rfl
  let s : F → F := fun y => ⟨_, hs_mem y⟩
  have hLs : ∀ y : F, ∀ a, L y (shift c ρ 1 a) = L (s y) a := by
    intro y a
    have := huniq ((L y).comp ⟨shift c ρ 1, continuous_shift c ρ 1⟩) (L (s y))
      (by funext a; simp [hLp', hEshift]) (hLp _) u₀ (by rw [hL0]; rfl)
    exact DFunLike.congr_fun this a
  have hs_inj : Function.Injective s := by
    intro y y' h
    apply hLinj y y' u₀
    have e1 : shift c ρ 1 (shift c ρ (-1) u₀) = u₀ := by
      rw [shift_shift]
      simp [shift_zero]
    rw [← e1, hLs, hLs, h]
  let σ : Equiv.Perm F := Equiv.ofBijective s (Finite.injective_iff_bijective.mp hs_inj)
  have hσ : ∀ y, σ y = s y := fun y => rfl
  have hLσ : ∀ k : ℤ, ∀ y : F, ∀ a, L y (shift c ρ k a) = L ((σ ^ k) y) a := by
    intro k
    induction k using Int.induction_on with
    | zero => intro y a; simp [shift_zero]
    | succ k ih =>
      intro y a
      conv_lhs => rw [show ((k : ℤ) + 1) = 1 + k by ring, ← shift_shift c ρ 1 k]
      rw [hLs, ih, zpow_add_one, Equiv.Perm.mul_apply, hσ]
    | pred k ih =>
      intro y a
      have hy : y = s (σ⁻¹ y) := by rw [← hσ]; simp
      conv_lhs => rw [hy]
      rw [← hLs, shift_shift, show (1 : ℤ) + (-↑k - 1) = -↑k by ring, ih, zpow_sub_one,
        Equiv.Perm.mul_apply]

  let Q := MulAction.orbitRel.Quotient (Subgroup.zpowers σ) F
  letI : Fintype Q := Fintype.ofFinite Q
  let m := Nat.card Q
  let eQ : Fin m ≃ Q := (Finite.equivFin Q).symm
  let rep : Fin m → F := fun b => (eQ b).out
  let ord : Fin m → ℕ := fun b => Function.minimalPeriod (σ • ·) (rep b)
  have hper : ∀ b (k : ℤ), (σ ^ k) (rep b) = rep b ↔ (ord b : ℤ) ∣ k := by
    intro b k
    rw [← Equiv.Perm.smul_def]
    exact MulAction.zpow_smul_eq_iff_minimalPeriod_dvd
  have hord : ∀ b, 1 ≤ ord b := by
    intro b
    have : Finite (MulAction.orbit (Subgroup.zpowers σ) (rep b)) := Subtype.finite
    exact Nat.one_le_iff_ne_zero.2 (NeZero.ne (Function.minimalPeriod (σ • ·) (rep b)))
  have hsame : ∀ b b' (k : ℤ), rep b = (σ ^ k) (rep b') → b = b' := by
    intro b b' k h
    apply eQ.injective
    rw [← Quotient.out_eq (eQ b), ← Quotient.out_eq (eQ b')]
    apply Quotient.sound
    show MulAction.orbitRel _ _ (rep b) (rep b')
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨⟨σ ^ k, Subgroup.zpow_mem_zpowers σ k⟩, h.symm⟩
  have hrep : ∀ y : F, ∃ b, ∃ k : ℤ, y = (σ ^ k) (rep b) := by
    intro y
    refine ⟨eQ.symm ⟦y⟧, ?_⟩
    have h1 : rep (eQ.symm ⟦y⟧) = (⟦y⟧ : Q).out := by simp [rep]
    have h2 := Quotient.mk_out (s := MulAction.orbitRel (Subgroup.zpowers σ) F) y
    have h3 : (⟦y⟧ : Q).out ∈ MulAction.orbit (Subgroup.zpowers σ) y := by
      rw [← MulAction.orbitRel_apply]; exact h2
    obtain ⟨⟨g, hg⟩, hgy⟩ := MulAction.mem_orbit_iff.1 h3
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨-j, ?_⟩
    rw [h1, ← hgy]
    simp [zpow_neg, Equiv.Perm.smul_def]
  have hsum : ∑ b, ord b = N := by
    rw [← hcardF]
    have h1 : ∑ b, ord b = ∑ q : Q, Function.minimalPeriod (σ • ·) q.out :=
      Equiv.sum_comp eQ (fun q => Function.minimalPeriod (σ • ·) q.out)
    have h2 : ∀ q : Q, Function.minimalPeriod (σ • ·) q.out =
        Nat.card (MulAction.orbit (Subgroup.zpowers σ) q.out) := by
      intro q
      rw [MulAction.minimalPeriod_eq_card, Nat.card_eq_fintype_card]
    rw [h1, Finset.sum_congr rfl (fun q _ => h2 q),
      Nat.card_congr (MulAction.selfEquivSigmaOrbits (Subgroup.zpowers σ) F), Nat.card_sigma]

  have hpt : ∀ b (t : ↥(Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0})) (w : ℂ), exp w = t.1 0 →
      Function.update t.1 0 (ord b * w) ∈ strip c ρ :=
    fun b t w hw => mem_strip_of_exp hc hρ0 hρ1 t.2.1 hw (hord b)
  let ψ : Fin m → ↥(Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0}) → Y :=
    fun b t => L (rep b) ⟨_, hpt b t (log (t.1 0)) (exp_log t.2.2)⟩
  have hψw : ∀ b t w (hw : exp w = t.1 0), ψ b t = L (rep b) ⟨_, hpt b t w hw⟩ := by
    intro b t w hw
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 (hw.trans (exp_log t.2.2).symm)
    have hsh : (⟨_, hpt b t w hw⟩ : strip c ρ) =
        shift c ρ (ord b * n) ⟨_, hpt b t (log (t.1 0)) (exp_log t.2.2)⟩ := by
      apply Subtype.ext
      simp only [shift_val, Function.update_self, Function.update_idem, hn]
      congr 1
      push_cast
      ring
    rw [hsh, hLσ, (hper b _).2 (dvd_mul_right _ _)]
  have hψcont : ∀ b, Continuous (ψ b) := by
    intro b
    rw [continuous_iff_continuousAt]
    intro t₁
    have hz : t₁.1 0 ≠ 0 := t₁.2.2
    have hw : ∀ t : ↥(Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0}),
        exp (log (t₁.1 0) + log (t.1 0 / t₁.1 0)) = t.1 0 := by
      intro t
      rw [exp_add, exp_log hz, exp_log (div_ne_zero t.2.2 hz)]
      field_simp
    have heq : ψ b = fun t => L (rep b) ⟨_, hpt b t _ (hw t)⟩ := funext fun t => hψw b t _ (hw t)
    rw [heq]
    apply (L (rep b)).continuous.continuousAt.comp
    rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
    apply continuousAt_subtype_val.update 0
    apply continuousAt_const.mul
    apply continuousAt_const.add
    apply ContinuousAt.clog
    · exact (((continuous_apply 0).comp continuous_subtype_val).div_const _).continuousAt
    · simp [div_self hz]
  have hpψ : ∀ b t, ((p (ψ b t) : Fin (e + 1) → ℂ)) = Function.update t.1 0 (t.1 0 ^ ord b) := by
    intro b t
    show ((p (L (rep b) _) : Fin (e + 1) → ℂ)) = _
    rw [hLp', expMap_val]
    simp only [Function.update_self, Function.update_idem, exp_nat_mul, exp_log t.2.2]
  have hrest : ∀ b b' t t', ψ b t = ψ b' t' → (∀ i, i ≠ 0 → t.1 i = t'.1 i) ∧
      t.1 0 ^ ord b = t'.1 0 ^ ord b' := by
    intro b b' t t' h
    have hp := congrArg (fun y => ((p y : Fin (e + 1) → ℂ))) h
    simp only [hpψ] at hp
    refine ⟨fun i hi => ?_, by simpa using congrFun hp 0⟩
    have := congrFun hp i
    simpa [Function.update_of_ne hi] using this

  have hmeet : ∀ b b' t t', ψ b t = ψ b' t' → ∃ n : ℤ,
      (ord b' : ℂ) * log (t'.1 0) = ord b * log (t.1 0) + n * (2 * π * I) ∧
      rep b = (σ ^ n) (rep b') := by
    intro b b' t t' h
    obtain ⟨hr', h0⟩ := hrest b b' t t' h
    have hexp : exp (ord b' * log (t'.1 0)) = exp (ord b * log (t.1 0)) := by
      rw [exp_nat_mul, exp_nat_mul, exp_log t.2.2, exp_log t'.2.2, h0]
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 hexp
    refine ⟨n, hn, ?_⟩
    have hsh : (⟨_, hpt b' t' (log (t'.1 0)) (exp_log t'.2.2)⟩ : strip c ρ) =
        shift c ρ n ⟨_, hpt b t (log (t.1 0)) (exp_log t.2.2)⟩ := by
      apply Subtype.ext
      funext i
      rcases eq_or_ne i 0 with rfl | hi
      · simp [shift_val, hn]
      · simp [shift_val, Function.update_of_ne hi, hr' i hi]
    have h2 : ψ b' t' = L ((σ ^ n) (rep b')) ⟨_, hpt b t _ (exp_log t.2.2)⟩ := by
      show L (rep b') _ = _
      rw [hsh, hLσ]
    exact hLinj (rep b) ((σ ^ n) (rep b')) _ (h.trans h2)
  have hψinj : ∀ b, Function.Injective (ψ b) := by
    intro b t t' h
    obtain ⟨hr', -⟩ := hrest b b t t' h
    obtain ⟨n, hn, h3⟩ := hmeet b b t t' h
    obtain ⟨j, hj⟩ := (hper b n).1 h3.symm
    have hm0 : (ord b : ℂ) ≠ 0 := by
      have : ord b ≠ 0 := Nat.one_le_iff_ne_zero.1 (hord b)
      exact_mod_cast this
    have hlog : log (t'.1 0) = log (t.1 0) + j * (2 * π * I) := by
      apply mul_left_cancel₀ hm0
      rw [hn, hj]
      push_cast
      ring
    apply Subtype.ext
    funext i
    rcases eq_or_ne i 0 with rfl | hi
    · rw [← exp_log t.2.2, ← exp_log t'.2.2, hlog, exp_add, exp_int_mul_two_pi_mul_I, mul_one]
    · exact hr' i hi
  have hψdisj : ∀ b b', b ≠ b' → ∀ t t', ψ b t ≠ ψ b' t' := by
    intro b b' hbb t t' h
    obtain ⟨n, -, h3⟩ := hmeet b b' t t' h
    exact hbb (hsame b b' n h3)
  have hcover : ∀ y, dist ((p y : Fin (e + 1) → ℂ)) c < ρ ^ N → ∃ b t, ψ b t = y := by
    intro y hy
    have hs0 : (p y : Fin (e + 1) → ℂ) 0 ≠ 0 := (p y).2.2
    have hN : N ≠ 0 := by
      intro hN0
      have := hfib (p y)
      rw [hN0, Nat.cast_zero, Set.encard_eq_zero] at this
      exact (Set.eq_empty_iff_forall_notMem.1 this) y rfl
    have hρN : ρ ^ N ≤ ρ := pow_le_of_le_one hρ0.le hρ1 hN
    have hsball : (p y : Fin (e + 1) → ℂ) ∈ Metric.ball c ρ := Metric.mem_ball.2 (hy.trans_le hρN)
    let a : strip c ρ := ⟨_, mem_strip_of_exp hc hρ0 hρ1 hsball (exp_log hs0) le_rfl⟩
    have hEa : p y = E a := by
      apply Subtype.ext
      rw [expMap_val]
      simp [a, exp_log hs0]
    obtain ⟨y', hy'⟩ := hfibre a y hEa
    obtain ⟨b, k, hk⟩ := hrep y'
    have hm1 := hord b
    have hm0 : (ord b : ℂ) ≠ 0 := by
      have : ord b ≠ 0 := Nat.one_le_iff_ne_zero.1 hm1
      exact_mod_cast this
    let w : ℂ := (log ((p y : Fin (e + 1) → ℂ) 0) + k * (2 * π * I)) / ord b
    have hmw : (ord b : ℂ) * w = log ((p y : Fin (e + 1) → ℂ) 0) + k * (2 * π * I) := by
      simp only [w]
      field_simp
    let t : Fin (e + 1) → ℂ := Function.update (p y : Fin (e + 1) → ℂ) 0 (exp w)
    have hmN : ord b ≤ N :=
      hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    have ht : t ∈ Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0} := by
      refine ⟨?_, by simp [t, exp_ne_zero]⟩
      rw [Metric.mem_ball, dist_pi_lt_iff hρ0]
      intro i
      rcases eq_or_ne i 0 with rfl | hi
      · simp only [t, Function.update_self, hc, dist_zero_right, norm_exp]
        have hre : (ord b : ℝ) * w.re = Real.log ‖(p y : Fin (e + 1) → ℂ) 0‖ := by
          have := congrArg re hmw
          simpa [mul_re, log_re] using this
        have hsn : ‖(p y : Fin (e + 1) → ℂ) 0‖ < ρ ^ N := by
          simpa [hc] using (dist_le_pi_dist _ c 0).trans_lt hy
        have hl : Real.log ‖(p y : Fin (e + 1) → ℂ) 0‖ < N * Real.log ρ := by
          rw [← Real.log_pow]
          exact Real.log_lt_log (norm_pos_iff.2 hs0) hsn
        have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
        have hmpos : (0 : ℝ) < ord b := by exact_mod_cast hm1
        have hmN' : (ord b : ℝ) ≤ N := by exact_mod_cast hmN
        have hlt : w.re < Real.log ρ := by
          by_contra hcon
          replace hcon := not_lt.1 hcon
          nlinarith [mul_le_mul_of_nonpos_right hmN' hlogρ, mul_le_mul_of_nonneg_left hcon hmpos.le]
        calc Real.exp w.re < Real.exp (Real.log ρ) := Real.exp_lt_exp.2 hlt
          _ = ρ := Real.exp_log hρ0
      · simp only [t, Function.update_of_ne hi]
        exact ((dist_le_pi_dist _ c i).trans_lt hy).trans_le hρN
    refine ⟨b, ⟨t, ht⟩, ?_⟩
    have hwt : exp w = (⟨t, ht⟩ : ↥(Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0})).1 0 := by
      simp [t]
    rw [hψw b ⟨t, ht⟩ w hwt]
    have hsh : (⟨_, hpt b ⟨t, ht⟩ w hwt⟩ : strip c ρ) = shift c ρ k a := by
      apply Subtype.ext
      simp only [shift_val, a, t, Function.update_idem, Function.update_self, hmw, Nat.cast_one,
        one_mul]
    rw [hsh, hLσ, ← hk, hy']
  exact ⟨m, ord, ρ, ψ, hρ0, hρ1, hsum, hord, hψcont, hpψ, hψinj, hψdisj, hcover⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
