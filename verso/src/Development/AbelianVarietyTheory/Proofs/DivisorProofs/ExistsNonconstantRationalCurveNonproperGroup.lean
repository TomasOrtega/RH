import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.InfiniteTorsionOrCocharacterOfArcAtInfinity
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SS.ArcInf
variable {k : Type} [Field k] [IsAlgClosed k]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hp (Polynomial.funext fun t => by rw [h t, Polynomial.eval_zero])`.
-/
theorem exists_eval_ne_zero_of_ne_zero {p : Polynomial k} (hp : p ≠ 0) : ∃ t, p.eval t ≠ 0 := by
  by_contra h
  push_neg at h
  exact hp (Polynomial.funext fun t => by rw [h t, Polynomial.eval_zero])

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[Polynomial.comp_eq_zero_iff]`. Break down `h with h | ⟨-, h⟩` into its components or cases. Conclude with `hp h`. Use `congrArg (Polynomial.coeff · 1) h` as an intermediate fact.

Simplify using `only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_one, Polynomial.coeff_C, one_ne_zero, if_false, mul_one, add_zero] at this`. Conclude with `hc (by simpa using this)`.
-/
theorem comp_linear_ne_zero {p : Polynomial k} (hp : p ≠ 0) {c e : k} (hc : c ≠ 0) :
    p.comp (Polynomial.C c * Polynomial.X + Polynomial.C e) ≠ 0 := by
  intro h
  rw [Polynomial.comp_eq_zero_iff] at h
  rcases h with h | ⟨-, h⟩
  · exact hp h
  · have := congrArg (Polynomial.coeff · 1) h
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_one, Polynomial.coeff_C,
      one_ne_zero, if_false, mul_one, add_zero] at this
    exact hc (by simpa using this)

/- English proof (translation)
Take `⟨A, _, _, j, ε, r, f, hc⟩` from `GlobalTheory.T.exists_affineUnitChart_smoothGroupScheme k G hG`. Take `⟨h, d, hd1, hh1, ht⟩` from `GlobalTheory.T.exists_arcQuotient_twoVariable_coords k G A j ε r f hc a`. Establish `hsep` using `hG.2.2.1`. Establish `hXd` using `mt ((GlobalTheory.T.subst_two_variables_identities_alt k).1 d).1.1 hd1`. Establish `hXh` using `fun i => ((GlobalTheory.T.subst_two_variables_identities_alt k).1 (h i)).1.2 (hh1 i)`.

Establish `hd' : (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) ≠ 0` using `fun e => hXd (e ▸ dvd_zero _)`. Establish `hd : d ≠ 0`. Introduce and unpack `rfl`. Apply `hd1` to reduce the goal to its premises. Apply the tactic sequence `rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> exact PowerSeries.constantCoeff_X), map_zero]`.

Distinguish the cases in `hQ : ∀ i, MvPowerSeries.weightedOrder (![1, 1] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) < MvPowerSeries.weightedOrder (![1, 1] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPow …`. It suffices to derive a contradiction. Take `⟨Pd, P, ψ, hPd, hP, hg⟩` from `ht.shear hc hd' le_rfl le_rfl (fun i => (hQ i).le)`. Take `⟨ch1, ch2⟩` from `GlobalTheory.T.relation_of_gen_of_order_eq k (fun z w => Rel a z w 1) (fun m n => ∀ z : PowerSeries k, z.order = (m : ℕ∞) → ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → Rel a z (PowerSeries.C t * PowerSeries.X ^ n) 1) (fun z w h => by simpa using h.symm) (fun x y z h h' => by simpa using …`. Establish `g11` using `ch1 1 1 (fun z hz => by`.

Establish `hz0` using `coeff_ne_of_order hz`. Use `⟨insert 0 ((fun t => (t + 1) * PowerSeries.coeff 1 z) '' {t | Pd.IsRoot t}), ((Polynomial.finite_setOfPred_isRoot hPd).image _).insert _, fun t hS => ?_⟩` and prove the remaining obligations. Establish `e : t / PowerSeries.coeff 1 z * PowerSeries.coeff 1 z = t` using `div_mul_cancel₀ _ hz0`. Establish `ht0 : t ≠ 0` using `fun e => hS (Or.inl e)`. Establish `hp : Pd.eval (t / PowerSeries.coeff 1 z - 1) ≠ 0` using `fun e' => hS (Or.inr ⟨_, e', by simp only [sub_add_cancel, e]⟩)`.

Take `⟨h1, h2⟩` from `mul_step le_rfl hg z hz _ (div_ne_zero ht0 hz0) hp`. Establish `: ψ (t / PowerSeries.coeff 1 z - 1) = ε` using `hc.hom_ext fun i => by`. Use `h1 i` as an intermediate fact. Rewrite `this` using `[(hP i).2 (hQ i), Polynomial.eval_zero, mul_eq_zero]`. Rewrite using `[hc.2.2.2, this.resolve_right hp]`.

Rewrite using `[this, hc.2.1, e] at h2)` and apply the resulting hypothesis. Take `⟨-, s2, s3, s4⟩` from `GlobalTheory.T.weightedOrder_slope_comparison_alt k r h d hd _ (fun _ _ => Iff.rfl)`. Take `⟨m₀, hm₀⟩` from `s2 (ht.lt_of_rel hc hd le_rfl le_rfl g11)`. Establish `all` using `ch2 (m₀ + 1) fun m hm => ht.gen_of_lt hc hd (m := m) (n := m + 1) (by omega) (by omega) (hm₀ m (by omega))`. Use `hna (GlobalTheory.T.arc_extends_of_regular_second_axis k G A j ε r f hc a h d hd ht (s4 fun n hn => ?_))` and prove the remaining obligations.

Use `(s3 1 n (m₀ + 1) (by omega)).1 (ht.lt_of_rel hc hd (by omega) (Nat.mul_pos (by omega) hn) ?_)` and prove the remaining obligations. Introduce `z w hz hw`. Conclude with `all _ _ z w (by omega) (Nat.le_mul_of_pos_right _ hn) hz hw`. Take `⟨m, n, hm, hmn, hle, i, hi⟩` from `(GlobalTheory.T.weightedOrder_slope_comparison_alt k r (fun i => (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))) _ hd' _ (fun _ _ => Iff.rfl)).1 hXh hXd ⟨1, 1, le_rfl, le_rfl, hQ⟩`. Take `⟨Pd, P, ψ, hPd, hP, hg⟩` from `ht.shear hc hd' hm (hm.trans hmn) hle`.

Establish `hPi : P i ≠ 0` using `fun e => ((hP i).1 e).ne hi`. Establish `triv : ∀ t, Pd.eval t ≠ 0 → (∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) → algOverHom (ψ t) ≫ j = 1 → (P i).eval t = 0` using `fun t ht h1 h => by`. Establish `e : ψ t = ε` using `eq_of_comp_eq hc.1 (h.trans hc.2.1.symm)`. Rewrite using `[← h1 i, e, hc.2.2.2 i, zero_mul]`. Break down `hmn.lt_or_eq with hlt | rfl` into its components or cases.

Establish `hψ : ∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t` using `fun t ht => (add_step hlt hg 0 t ht).1`. Establish `hmul : ∀ t t', Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t + t') ≠ 0 → (algOverHom (ψ t) ≫ j) * (algOverHom (ψ t') ≫ j) = algOverHom (ψ (t + t')) ≫ j`. Introduce `t t' h1 h2 h3`. Establish `e1` using `(add_step hlt hg 0 t' h2).2`. Establish `e2` using `(add_step hlt hg (t' + 0) t h1).2`.

Establish `e3` using `(add_step hlt hg 0 (t + t') h3).2`. Rewrite `e3` using `[_root_.add_assoc]`. Conclude with `Red.unique hsep (e1.trans e2) e3`. Take `⟨t', ht'⟩` from `exists_eval_ne_zero_of_ne_zero hPd`. Take `⟨t, ht⟩` from `exists_eval_ne_zero_of_ne_zero (mul_ne_zero (mul_ne_zero hPd hPi) (comp_linear_ne_zero hPd (one_ne_zero (α := k)) (e := t')))`.

Simplify using `only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, _root_.one_mul, ne_eq, mul_eq_zero, not_or] at ht`. Take `⟨⟨hpt, hpi⟩, hpt2⟩` from `ht`. Use `⟨A, _, _, j, ε, r, f, Pd, P, ψ, t + t', t', hc, hPd, hψ, hpt2, ht', fun e => hpi ?_⟩` and prove the remaining obligations. Establish `h` using `hmul t t' hpt ht' hpt2`. Rewrite `h` using `[e]`.

Conclude with `triv t hpt (hψ t hpt) (mul_eq_right.1 h)`. Establish `ev : ∀ (q : Polynomial k) (t : k), (q.comp (Polynomial.X - Polynomial.C 1)).eval t = q.eval (t - 1)` using `fun q t => by simp`. Establish `hψ : ∀ t, t ≠ 0 → Pd.eval (t - 1) ≠ 0 → ∀ i, ψ (t - 1) (f i) * Pd.eval (t - 1) = (P i).eval (t - 1)` using `fun t h0 h1 => (mul_step hm hg _ (order_mon one_ne_zero m) t h0 h1).1`. Establish `hmul : ∀ t t', t ≠ 0 → t' ≠ 0 → Pd.eval (t - 1) ≠ 0 → Pd.eval (t' - 1) ≠ 0 → Pd.eval (t * t' - 1) ≠ 0 → (algOverHom (ψ (t - 1)) ≫ j) * (algOverHom (ψ (t' - 1)) ≫ j) = algOverHom (ψ (t * t' - 1)) ≫ j`. Introduce `t t' h0 h0' h1 h2 h3`.

Establish `e1` using `(mul_step hm hg _ (order_mon one_ne_zero m) t' h0' h2).2`. Establish `e3` using `(mul_step hm hg _ (order_mon one_ne_zero m) _ (mul_ne_zero h0 h0') h3).2`. Rewrite `e1`, `e3` using `[coeff_mon, _root_.mul_one]`. Establish `e2` using `(mul_step hm hg _ (order_mon h0' m) t h0 h1).2`. Rewrite `e2` using `[coeff_mon]`.

Conclude with `Red.unique hsep (e1.trans e2) e3`. Establish `hQ1 : Pd.comp (Polynomial.C 1 * Polynomial.X + Polynomial.C (-1)) ≠ 0` using `comp_linear_ne_zero hPd one_ne_zero`. Establish `hQ2 : (P i).comp (Polynomial.C 1 * Polynomial.X + Polynomial.C (-1)) ≠ 0` using `comp_linear_ne_zero hPi one_ne_zero`. Take `⟨t', ht'⟩` from `exists_eval_ne_zero_of_ne_zero (mul_ne_zero Polynomial.X_ne_zero hQ1)`. Simplify using `only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, _root_.one_mul, ne_eq, mul_eq_zero, not_or, ← sub_eq_add_neg] at ht'`.

Take `⟨h0', hpt'⟩` from `ht'`. Take `⟨t, ht⟩` from `exists_eval_ne_zero_of_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero Polynomial.X_ne_zero hQ1) hQ2) (comp_linear_ne_zero hPd h0' (e := -1)))`. Simplify using `only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, _root_.one_mul, ne_eq, mul_eq_zero, not_or, ← sub_eq_add_neg] at ht`. Take `⟨⟨⟨h0, hpt⟩, hpi⟩, hpt2⟩` from `ht`. Rewrite `hpt2` using `[mul_comm t' t]`.

Use `⟨A, _, _, j, ε, r, f, Polynomial.X * Pd.comp (Polynomial.X - Polynomial.C 1), fun i => Polynomial.X * (P i).comp (Polynomial.X - Polynomial.C 1), fun t => ψ (t - 1), t * t', t', hc, mul_ne_zero Polynomial.X_ne_zero (mt comp_sub_one_eq_zero.1 hPd), fun s hs i => ?_, ?_, ?_, fun e …` and prove the remaining obligations. Rewrite `hs` using `[Polynomial.eval_mul, Polynomial.eval_X, ev]`. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_X, ev, ev, ← hψ s (left_ne_zero_of_mul hs) (right_ne_zero_of_mul hs) i]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_X, ev]`.

Conclude with `mul_ne_zero (mul_ne_zero h0 h0') hpt2`. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_X, ev]`. Conclude with `mul_ne_zero h0' hpt'`. Establish `h` using `hmul t t' h0 h0' hpt hpt' hpt2`. Establish `e' : ψ (t * t' - 1) = ψ (t' - 1)` using `e`.

Rewrite `h` using `[e']`. Conclude with `triv (t - 1) hpt (hψ t h0 hpt) (mul_eq_right.1 h)`.
-/
theorem exists_rational_family {G : Over (Sp k)} [GrpObj G] (hG : SmConn G)
    (a : algOver k (FractionRing (PowerSeries k)) ⟶ G)
    (hna : ¬ ∃ b : algOver k (PowerSeries k) ⟶ G, algOverHom (toK k) ≫ b = a) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ)
      (f : Fin r → A) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)) (t₁ t₂ : k),
      IsChart G j ε f ∧ Pd ≠ 0 ∧ (∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) ∧
      Pd.eval t₁ ≠ 0 ∧ Pd.eval t₂ ≠ 0 ∧ ψ t₁ ≠ ψ t₂ := by
  obtain ⟨A, _, _, j, ε, r, f, hc⟩ := GlobalTheory.T.exists_affineUnitChart_smoothGroupScheme k G hG
  obtain ⟨h, d, hd1, hh1, ht⟩ := GlobalTheory.T.exists_arcQuotient_twoVariable_coords k G A j ε r f hc a
  have hsep := hG.2.2.1
  have hXd := mt ((GlobalTheory.T.subst_two_variables_identities_alt k).1 d).1.1 hd1
  have hXh := fun i => ((GlobalTheory.T.subst_two_variables_identities_alt k).1 (h i)).1.2 (hh1 i)
  have hd' : (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) ≠ 0 := fun e => hXd (e ▸ dvd_zero _)
  have hd : d ≠ 0 := by
    rintro rfl
    apply hd1
    rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
      fun i => by fin_cases i <;> exact PowerSeries.constantCoeff_X), map_zero]
  by_cases hQ : ∀ i, MvPowerSeries.weightedOrder (![1, 1] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) < MvPowerSeries.weightedOrder (![1, 1] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))
  · exfalso
    obtain ⟨Pd, P, ψ, hPd, hP, hg⟩ := ht.shear hc hd' le_rfl le_rfl (fun i => (hQ i).le)
    obtain ⟨ch1, ch2⟩ := GlobalTheory.T.relation_of_gen_of_order_eq k (fun z w => Rel a z w 1)
      (fun m n => ∀ z : PowerSeries k, z.order = (m : ℕ∞) →
        ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → Rel a z (PowerSeries.C t * PowerSeries.X ^ n) 1)
      (fun z w h => by simpa using h.symm) (fun x y z h h' => by simpa using h.trans h') (fun _ _ h => h)
    have g11 := ch1 1 1 (fun z hz => by
      have hz0 := coeff_ne_of_order hz
      refine ⟨insert 0 ((fun t => (t + 1) * PowerSeries.coeff 1 z) '' {t | Pd.IsRoot t}),
        ((Polynomial.finite_setOfPred_isRoot hPd).image _).insert _, fun t hS => ?_⟩
      have e : t / PowerSeries.coeff 1 z * PowerSeries.coeff 1 z = t := div_mul_cancel₀ _ hz0
      have ht0 : t ≠ 0 := fun e => hS (Or.inl e)
      have hp : Pd.eval (t / PowerSeries.coeff 1 z - 1) ≠ 0 := fun e' =>
        hS (Or.inr ⟨_, e', by simp only [sub_add_cancel, e]⟩)
      obtain ⟨h1, h2⟩ := mul_step le_rfl hg z hz _ (div_ne_zero ht0 hz0) hp
      have : ψ (t / PowerSeries.coeff 1 z - 1) = ε := hc.hom_ext fun i => by
        have := h1 i
        rw [(hP i).2 (hQ i), Polynomial.eval_zero, mul_eq_zero] at this
        rw [hc.2.2.2, this.resolve_right hp]
      rwa [this, hc.2.1, e] at h2)
    obtain ⟨-, s2, s3, s4⟩ := GlobalTheory.T.weightedOrder_slope_comparison_alt k r h d hd _ (fun _ _ => Iff.rfl)
    obtain ⟨m₀, hm₀⟩ := s2 (ht.lt_of_rel hc hd le_rfl le_rfl g11)
    have all := ch2 (m₀ + 1) fun m hm =>
      ht.gen_of_lt hc hd (m := m) (n := m + 1) (by omega) (by omega) (hm₀ m (by omega))
    refine hna (GlobalTheory.T.arc_extends_of_regular_second_axis k G A j ε r f hc a h d hd ht (s4 fun n hn => ?_))
    refine (s3 1 n (m₀ + 1) (by omega)).1 (ht.lt_of_rel hc hd (by omega) (Nat.mul_pos (by omega) hn) ?_)
    intro z w hz hw
    exact all _ _ z w (by omega) (Nat.le_mul_of_pos_right _ hn) hz hw
  · obtain ⟨m, n, hm, hmn, hle, i, hi⟩ := (GlobalTheory.T.weightedOrder_slope_comparison_alt k r (fun i => (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))) _ hd' _
      (fun _ _ => Iff.rfl)).1 hXh hXd ⟨1, 1, le_rfl, le_rfl, hQ⟩
    obtain ⟨Pd, P, ψ, hPd, hP, hg⟩ := ht.shear hc hd' hm (hm.trans hmn) hle
    have hPi : P i ≠ 0 := fun e => ((hP i).1 e).ne hi
    have triv : ∀ t, Pd.eval t ≠ 0 → (∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) →
        algOverHom (ψ t) ≫ j = 1 → (P i).eval t = 0 := fun t ht h1 h => by
      have e : ψ t = ε := eq_of_comp_eq hc.1 (h.trans hc.2.1.symm)
      rw [← h1 i, e, hc.2.2.2 i, zero_mul]
    rcases hmn.lt_or_eq with hlt | rfl
    · have hψ : ∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t :=
        fun t ht => (add_step hlt hg 0 t ht).1
      have hmul : ∀ t t', Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t + t') ≠ 0 →
          (algOverHom (ψ t) ≫ j) * (algOverHom (ψ t') ≫ j) = algOverHom (ψ (t + t')) ≫ j := by
        intro t t' h1 h2 h3
        have e1 := (add_step hlt hg 0 t' h2).2
        have e2 := (add_step hlt hg (t' + 0) t h1).2
        have e3 := (add_step hlt hg 0 (t + t') h3).2
        rw [_root_.add_assoc] at e3
        exact Red.unique hsep (e1.trans e2) e3
      obtain ⟨t', ht'⟩ := exists_eval_ne_zero_of_ne_zero hPd
      obtain ⟨t, ht⟩ := exists_eval_ne_zero_of_ne_zero (mul_ne_zero (mul_ne_zero hPd hPi)
        (comp_linear_ne_zero hPd (one_ne_zero (α := k)) (e := t')))
      simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X, _root_.one_mul, ne_eq, mul_eq_zero, not_or] at ht
      obtain ⟨⟨hpt, hpi⟩, hpt2⟩ := ht
      refine ⟨A, _, _, j, ε, r, f, Pd, P, ψ, t + t', t', hc, hPd, hψ, hpt2, ht', fun e => hpi ?_⟩
      have h := hmul t t' hpt ht' hpt2
      rw [e] at h
      exact triv t hpt (hψ t hpt) (mul_eq_right.1 h)
    · have ev : ∀ (q : Polynomial k) (t : k), (q.comp (Polynomial.X - Polynomial.C 1)).eval t = q.eval (t - 1) :=
        fun q t => by simp
      have hψ : ∀ t, t ≠ 0 → Pd.eval (t - 1) ≠ 0 → ∀ i, ψ (t - 1) (f i) * Pd.eval (t - 1) = (P i).eval (t - 1) :=
        fun t h0 h1 => (mul_step hm hg _ (order_mon one_ne_zero m) t h0 h1).1
      have hmul : ∀ t t', t ≠ 0 → t' ≠ 0 → Pd.eval (t - 1) ≠ 0 → Pd.eval (t' - 1) ≠ 0 → Pd.eval (t * t' - 1) ≠ 0 →
          (algOverHom (ψ (t - 1)) ≫ j) * (algOverHom (ψ (t' - 1)) ≫ j) = algOverHom (ψ (t * t' - 1)) ≫ j := by
        intro t t' h0 h0' h1 h2 h3
        have e1 := (mul_step hm hg _ (order_mon one_ne_zero m) t' h0' h2).2
        have e3 := (mul_step hm hg _ (order_mon one_ne_zero m) _ (mul_ne_zero h0 h0') h3).2
        rw [coeff_mon, _root_.mul_one] at e1 e3
        have e2 := (mul_step hm hg _ (order_mon h0' m) t h0 h1).2
        rw [coeff_mon] at e2
        exact Red.unique hsep (e1.trans e2) e3
      have hQ1 : Pd.comp (Polynomial.C 1 * Polynomial.X + Polynomial.C (-1)) ≠ 0 :=
        comp_linear_ne_zero hPd one_ne_zero
      have hQ2 : (P i).comp (Polynomial.C 1 * Polynomial.X + Polynomial.C (-1)) ≠ 0 :=
        comp_linear_ne_zero hPi one_ne_zero
      obtain ⟨t', ht'⟩ := exists_eval_ne_zero_of_ne_zero (mul_ne_zero Polynomial.X_ne_zero hQ1)
      simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X, _root_.one_mul, ne_eq, mul_eq_zero, not_or, ← sub_eq_add_neg] at ht'
      obtain ⟨h0', hpt'⟩ := ht'
      obtain ⟨t, ht⟩ := exists_eval_ne_zero_of_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        Polynomial.X_ne_zero hQ1) hQ2) (comp_linear_ne_zero hPd h0' (e := -1)))
      simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X, _root_.one_mul, ne_eq, mul_eq_zero, not_or, ← sub_eq_add_neg] at ht
      obtain ⟨⟨⟨h0, hpt⟩, hpi⟩, hpt2⟩ := ht
      rw [mul_comm t' t] at hpt2
      refine ⟨A, _, _, j, ε, r, f, Polynomial.X * Pd.comp (Polynomial.X - Polynomial.C 1),
        fun i => Polynomial.X * (P i).comp (Polynomial.X - Polynomial.C 1), fun t => ψ (t - 1), t * t', t', hc,
        mul_ne_zero Polynomial.X_ne_zero (mt comp_sub_one_eq_zero.1 hPd), fun s hs i => ?_, ?_, ?_, fun e => hpi ?_⟩
      · rw [Polynomial.eval_mul, Polynomial.eval_X, ev] at hs
        rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_X, ev, ev,
          ← hψ s (left_ne_zero_of_mul hs) (right_ne_zero_of_mul hs) i]
        ring
      · rw [Polynomial.eval_mul, Polynomial.eval_X, ev]
        exact mul_ne_zero (mul_ne_zero h0 h0') hpt2
      · rw [Polynomial.eval_mul, Polynomial.eval_X, ev]
        exact mul_ne_zero h0' hpt'
      · have h := hmul t t' h0 h0' hpt hpt' hpt2
        have e' : ψ (t * t' - 1) = ψ (t' - 1) := e
        rw [e'] at h
        exact triv (t - 1) hpt (hψ t h0 hpt) (mul_eq_right.1 h)

end GlobalTheory.SS.ArcInf

noncomputable section
namespace GlobalTheory.RatCurve
open GlobalTheory.SS GlobalTheory.SS.ArcInf

section Curve
variable {k : Type} [Field k]

def evAway (Pd : Polynomial k) (t : k) (ht : Pd.eval t ≠ 0) : Localization.Away Pd →ₐ[k] k :=
  { IsLocalization.Away.lift Pd (g := Polynomial.evalRingHom t) (IsUnit.mk0 _ ht) with
    commutes' := fun c => by
      show IsLocalization.Away.lift Pd _ (algebraMap k (Localization.Away Pd) c) = c
      rw [IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away Pd)]
      simp [IsLocalization.Away.lift] }

/- English proof (translation)
Simplify using `[evAway, IsLocalization.Away.lift]`.
-/
theorem evAway_alg (Pd : Polynomial k) (t : k) (ht : Pd.eval t ≠ 0) (q : Polynomial k) :
    evAway Pd t ht (algebraMap _ _ q) = q.eval t := by
  simp [evAway, IsLocalization.Away.lift]

/- English proof (translation)
Establish `h` using `congrArg (evAway Pd t ht) (IsLocalization.Away.mul_invSelf (S := Localization.Away Pd) Pd)`. Rewrite `h` using `[map_mul, evAway_alg, map_one]`. Conclude with `eq_inv_of_mul_eq_one_right h`.
-/
theorem evAway_invSelf (Pd : Polynomial k) (t : k) (ht : Pd.eval t ≠ 0) :
    evAway Pd t ht (IsLocalization.Away.invSelf Pd) = (Pd.eval t)⁻¹ := by
  have h := congrArg (evAway Pd t ht) (IsLocalization.Away.mul_invSelf (S := Localization.Away Pd) Pd)
  rw [map_mul, evAway_alg, map_one] at h
  exact eq_inv_of_mul_eq_one_right h

/- English proof (translation)
Take `⟨⟨Q, ⟨_, n, rfl⟩⟩, hQ⟩` from `IsLocalization.surj (Submonoid.powers Pd) x`. Establish `hQ0 : Q * Pd = 0`. Use `Polynomial.funext fun t => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_zero]`. Distinguish the cases in `ht : Pd.eval t = 0`.

Rewrite using `[ht, mul_zero]`. Use `congrArg (evAway Pd t ht) hQ` as an intermediate fact. Simplify using `only [map_mul, evAway_alg, hx t ht, zero_mul] at this`. Rewrite using `[← this, zero_mul]`. Establish `hQ' : Q = 0` using `(mul_eq_zero.1 hQ0).resolve_right hPd`.

Simplify using `only [hQ', map_zero] at hQ`. Conclude with `(IsLocalization.map_units (Localization.Away Pd) (⟨Pd ^ n, n, rfl⟩ : Submonoid.powers Pd)).mul_left_eq_zero.1 hQ`.
-/
theorem eq_zero_of_evAway [Infinite k] {Pd : Polynomial k} (hPd : Pd ≠ 0) (x : Localization.Away Pd)
    (hx : ∀ t (ht : Pd.eval t ≠ 0), evAway Pd t ht x = 0) : x = 0 := by
  obtain ⟨⟨Q, ⟨_, n, rfl⟩⟩, hQ⟩ := IsLocalization.surj (Submonoid.powers Pd) x
  have hQ0 : Q * Pd = 0 := by
    refine Polynomial.funext fun t => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_zero]
    by_cases ht : Pd.eval t = 0
    · rw [ht, mul_zero]
    · have := congrArg (evAway Pd t ht) hQ
      simp only [map_mul, evAway_alg, hx t ht, zero_mul] at this
      rw [← this, zero_mul]
  have hQ' : Q = 0 := (mul_eq_zero.1 hQ0).resolve_right hPd
  simp only [hQ', map_zero] at hQ
  exact (IsLocalization.map_units (Localization.Away Pd) (⟨Pd ^ n, n, rfl⟩ : Submonoid.powers Pd)).mul_left_eq_zero.1 hQ

variable [Infinite k] {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A]
  {j : algOver k A ⟶ G} {ε : A →ₐ[k] k} {r : ℕ} {f : Fin r → A}

/- English proof (translation)
Set `g : Fin r → Localization.Away Pd` to `fun i => algebraMap (Polynomial k) _ (P i) * IsLocalization.Away.invSelf Pd`. Establish `hg : ∀ t (ht : Pd.eval t ≠ 0) i, evAway Pd t ht (g i) = ψ t (f i)` using `fun t ht i => by`. Simplify using `only [g, map_mul, evAway_alg, evAway_invSelf]`. Rewrite using `[← hψ t ht i, mul_inv_cancel_right₀ ht]`. Set `φ : MvPolynomial (Fin r) k →ₐ[k] A` to `MvPolynomial.aeval f`.

Establish `hsurj : Function.Surjective φ`. Rewrite using `[← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]`. Conclude with `hc.2.2.1`. Set `Φ : MvPolynomial (Fin r) k →ₐ[k] Localization.Away Pd` to `MvPolynomial.aeval g`. Establish `hev : ∀ t (ht : Pd.eval t ≠ 0), (evAway Pd t ht).comp Φ = (ψ t).comp φ` using `fun t ht => by`.

Rewrite using `[MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]`. Conclude with `congrArg _ (funext (hg t ht))`. Establish `hker : RingHom.ker φ ≤ RingHom.ker Φ` using `fun p hp => by`. Rewrite `hp`, the goal using `[RingHom.mem_ker]`. Use `eq_zero_of_evAway hPd _ fun t ht => ?_` and prove the remaining obligations.

Use `AlgHom.congr_fun (hev t ht) p` as an intermediate fact. Rewrite `this` using `[AlgHom.comp_apply, AlgHom.comp_apply]`. Rewrite using `[this, show φ p = 0 from hp, map_zero]`. Set `e` to `Ideal.quotientKerAlgEquivOfSurjective hsurj`. Set `Ψ : A →ₐ[k] Localization.Away Pd` to `(Ideal.Quotient.liftₐ (RingHom.ker φ) Φ fun p hp => hker hp).comp e.symm.toAlgHom`.

Establish `hΨ : Ψ.comp φ = Φ`. Use extensionality with `p`. Simplify using `only [Ψ, AlgHom.comp_apply]`. Establish `: e.symm (φ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (MvPolynomial.X p)`. Rewrite using `[AlgEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(Ideal.Quotient.liftₐ (RingHom.ker φ) Φ _) (e.symm (φ (MvPolynomial.X p))) = _`. Rewrite using `[this]`. Both sides reduce to the same expression. Use `⟨Ψ, fun t ht => ?_⟩` and prove the remaining obligations.

Use `AlgHom.ext fun x => ?_` and prove the remaining obligations. Take `⟨p, rfl⟩` from `hsurj x`. Use `AlgHom.congr_fun (hev t ht) p` as an intermediate fact. Rewrite `this` using `[← hΨ]`. Simplify `this` using `only [AlgHom.comp_apply]`.
-/
theorem exists_algHom_of_family (hc : IsChart G j ε f) {Pd : Polynomial k} (hPd : Pd ≠ 0)
    (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k))
    (hψ : ∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) :
    ∃ Ψ : A →ₐ[k] Localization.Away Pd, ∀ t (ht : Pd.eval t ≠ 0), (evAway Pd t ht).comp Ψ = ψ t := by
  let g : Fin r → Localization.Away Pd := fun i =>
    algebraMap (Polynomial k) _ (P i) * IsLocalization.Away.invSelf Pd
  have hg : ∀ t (ht : Pd.eval t ≠ 0) i, evAway Pd t ht (g i) = ψ t (f i) := fun t ht i => by
    simp only [g, map_mul, evAway_alg, evAway_invSelf]
    rw [← hψ t ht i, mul_inv_cancel_right₀ ht]
  let φ : MvPolynomial (Fin r) k →ₐ[k] A := MvPolynomial.aeval f
  have hsurj : Function.Surjective φ := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    exact hc.2.2.1
  let Φ : MvPolynomial (Fin r) k →ₐ[k] Localization.Away Pd := MvPolynomial.aeval g
  have hev : ∀ t (ht : Pd.eval t ≠ 0), (evAway Pd t ht).comp Φ = (ψ t).comp φ := fun t ht => by
    rw [MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]
    exact congrArg _ (funext (hg t ht))
  have hker : RingHom.ker φ ≤ RingHom.ker Φ := fun p hp => by
    rw [RingHom.mem_ker] at hp ⊢
    refine eq_zero_of_evAway hPd _ fun t ht => ?_
    have := AlgHom.congr_fun (hev t ht) p
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at this
    rw [this, show φ p = 0 from hp, map_zero]
  let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let Ψ : A →ₐ[k] Localization.Away Pd :=
    (Ideal.Quotient.liftₐ (RingHom.ker φ) Φ fun p hp => hker hp).comp e.symm.toAlgHom
  have hΨ : Ψ.comp φ = Φ := by
    ext p
    simp only [Ψ, AlgHom.comp_apply]
    have : e.symm (φ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (MvPolynomial.X p) := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    change (Ideal.Quotient.liftₐ (RingHom.ker φ) Φ _) (e.symm (φ (MvPolynomial.X p))) = _
    rw [this]
    rfl
  refine ⟨Ψ, fun t ht => ?_⟩
  refine AlgHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := hsurj x
  have := AlgHom.congr_fun (hev t ht) p
  rw [← hΨ] at this
  simpa only [AlgHom.comp_apply] using this

/- English proof (translation)
Take `⟨Ψ, hΨ⟩` from `exists_algHom_of_family hc hPd P ψ hψ`. Use `⟨Pd, hPd, (algOverHom Ψ ≫ j).left, evAway Pd t₁ h₁, evAway Pd t₂ h₂, Over.w _, fun e => hne ?_⟩` and prove the remaining obligations. Establish `key : ∀ t (ht : Pd.eval t ≠ 0), spMap (evAway Pd t ht).toRingHom ≫ (algOverHom Ψ ≫ j).left = (algOverHom (ψ t) ≫ j).left` using `fun t ht => by`. Rewrite using `[← hΨ t ht, algOverHom_comp, Over.comp_left, Over.comp_left, Over.comp_left, algOverHom_left]`. Both sides reduce to the same expression.

Rewrite `e` using `[key, key]`. Conclude with `eq_of_comp_eq hc.1 (Over.OverMorphism.ext e)`.
-/
theorem curve_of_family (hc : IsChart G j ε f) {Pd : Polynomial k} (hPd : Pd ≠ 0)
    (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k))
    (hψ : ∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) {t₁ t₂ : k}
    (h₁ : Pd.eval t₁ ≠ 0) (h₂ : Pd.eval t₂ ≠ 0) (hne : ψ t₁ ≠ ψ t₂) :
    ∃ (P : Polynomial k) (_ : P ≠ 0) (u : Sp (Localization.Away P) ⟶ G.left)
      (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) ∧
      spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u := by
  obtain ⟨Ψ, hΨ⟩ := exists_algHom_of_family hc hPd P ψ hψ
  refine ⟨Pd, hPd, (algOverHom Ψ ≫ j).left, evAway Pd t₁ h₁, evAway Pd t₂ h₂, Over.w _, fun e => hne ?_⟩
  have key : ∀ t (ht : Pd.eval t ≠ 0), spMap (evAway Pd t ht).toRingHom ≫ (algOverHom Ψ ≫ j).left =
      (algOverHom (ψ t) ≫ j).left := fun t ht => by
    rw [← hΨ t ht, algOverHom_comp, Over.comp_left, Over.comp_left, Over.comp_left, algOverHom_left]
    rfl
  rw [key, key] at e
  exact eq_of_comp_eq hc.1 (Over.OverMorphism.ext e)

end Curve
end GlobalTheory.RatCurve

namespace GlobalTheory.RatCurve
open GlobalTheory.SS GlobalTheory.SS.ArcInf

/- English proof (translation)
Introduce `k _ _ G _ hG hnp`. Establish `: Smooth G.hom` using `hG.2.1`. Establish `: GeometricallyConnected G.hom` using `hG.2.2.2.2`. Establish `: IsIntegral G.left` using `GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected G.hom`. Establish `harc : ∃ a : Sp (FractionRing (PowerSeries k)) ⟶ G.left, a ≫ G.hom = spMap (algebraMap k (FractionRing (PowerSeries k))) ∧ ¬ ∃ b : Sp (PowerSeries k) ⟶ G.left, spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a`.

Assume the negation of the conclusion as `hno`. Use `hnp (GlobalTheory.ArcProper.isProper_of_arcs k G hG.2.2.1 inferInstance hG.2.2.2.1 fun a ha => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hb`. Conclude with `hno ⟨a, ha, hb⟩`. Take `⟨a, ha, hna⟩` from `harc`.

Take `⟨A, _, _, j, ε, r, f, Pd, P, ψ, t₁, t₂, hc, hPd, hψ, h₁, h₂, hne⟩` from `exists_rational_family hG (Over.homMk a ha) (by`. Introduce and unpack `⟨b, hb⟩`. Conclude with `hna ⟨b.left, congrArg (fun x => x.left) hb⟩)`. Conclude with `curve_of_family hc hPd P ψ hψ h₁ h₂ hne`.
-/
theorem exists_rational_curve : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G],
    GlobalTheory.SS.SmConn G → ¬ IsProper G.hom → ∃ (P : Polynomial k) (_ : P ≠ 0) (u : Sp (Localization.Away P) ⟶ G.left)
      (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) ∧
      spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u := by
  intro k _ _ G _ hG hnp
  have : Smooth G.hom := hG.2.1
  have : GeometricallyConnected G.hom := hG.2.2.2.2
  have : IsIntegral G.left := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected G.hom
  have harc : ∃ a : Sp (FractionRing (PowerSeries k)) ⟶ G.left,
      a ≫ G.hom = spMap (algebraMap k (FractionRing (PowerSeries k))) ∧
      ¬ ∃ b : Sp (PowerSeries k) ⟶ G.left, spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a := by
    by_contra hno
    refine hnp (GlobalTheory.ArcProper.isProper_of_arcs k G hG.2.2.1 inferInstance hG.2.2.2.1 fun a ha => ?_)
    by_contra hb
    exact hno ⟨a, ha, hb⟩
  obtain ⟨a, ha, hna⟩ := harc
  obtain ⟨A, _, _, j, ε, r, f, Pd, P, ψ, t₁, t₂, hc, hPd, hψ, h₁, h₂, hne⟩ :=
    exists_rational_family hG (Over.homMk a ha) (by
      rintro ⟨b, hb⟩
      exact hna ⟨b.left, congrArg (fun x => x.left) hb⟩)
  exact curve_of_family hc hPd P ψ hψ h₁ h₂ hne

end GlobalTheory.RatCurve
