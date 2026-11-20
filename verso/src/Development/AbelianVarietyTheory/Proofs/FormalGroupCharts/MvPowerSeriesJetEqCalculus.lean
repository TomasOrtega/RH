import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp.JCalc

variable {R : Type} [CommRing R] {σ : Type} {m : ℕ}

/- English proof (translation)
Introduce `_ _` and use `rfl`.
-/
theorem jeq_refl (f : MvPowerSeries σ R) : JEq m f f := fun _ _ => rfl

/- English proof (translation)
Introduce `e he` and use `by rw [map_add, map_add, h e he, k e he]`.
-/
theorem jeq_add {f f' g g' : MvPowerSeries σ R} (h : JEq m f f') (k : JEq m g g') : JEq m (f + g) (f' + g') :=
  fun e he => by rw [map_add, map_add, h e he, k e he]

/- English proof (translation)
Introduce `e he` and use `by rw [map_sub, map_sub, h e he, k e he]`.
-/
theorem jeq_sub {f f' g g' : MvPowerSeries σ R} (h : JEq m f f') (k : JEq m g g') : JEq m (f - g) (f' - g') :=
  fun e he => by rw [map_sub, map_sub, h e he, k e he]

/- English proof (translation)
Introduce `e he`. Rewrite using `[MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hsum` using `congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)`. Rewrite `hsum` using `[map_add]`.

Rewrite using `[h p.1 (by omega), k p.2 (by omega)]`.
-/
theorem jeq_mul {f f' g g' : MvPowerSeries σ R} (h : JEq m f f') (k : JEq m g g') : JEq m (f * g) (f' * g') := by
  classical
  intro e he
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hsum := congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)
  rw [map_add] at hsum
  rw [h p.1 (by omega), k p.2 (by omega)]

/- English proof (translation)
Take `⟨c, hc⟩` from `hu`. Establish `h1` using `MvPowerSeries.mul_invOfUnit u c hc.symm`. Use `jeq_mul h (jeq_refl (MvPowerSeries.invOfUnit u c))` as an intermediate fact. Rewrite `this` using `[_root_.mul_assoc, _root_.mul_assoc, h1, _root_.mul_one, _root_.mul_one]`. Then use the resulting hypothesis.
-/
theorem jeq_cancel {f g u : MvPowerSeries σ R} (hu : IsUnit (MvPowerSeries.constantCoeff u))
    (h : JEq m (f * u) (g * u)) : JEq m f g := by
  obtain ⟨c, hc⟩ := hu
  have h1 := MvPowerSeries.mul_invOfUnit u c hc.symm
  have := jeq_mul h (jeq_refl (MvPowerSeries.invOfUnit u c))
  rwa [_root_.mul_assoc, _root_.mul_assoc, h1, _root_.mul_one, _root_.mul_one] at this

/- English proof (translation)
Introduce `e he` and use `by rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, h e he]`.
-/
theorem jeq_map {R' : Type} [CommRing R'] (β : R →+* R') {f g : MvPowerSeries σ R} (h : JEq m f g) :
    JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g) :=
  fun e he => by rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, h e he]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `e`. Distinguish the cases in `he : e.degree ≤ m`. Rewrite using `[MvPowerSeries.coeff_truncTotal _ (by omega), MvPowerSeries.coeff_truncTotal _ (by omega), h e he]`.

Rewrite using `[MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega), MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega)]`. Introduce `h e he`. Rewrite using `[← MvPowerSeries.coeff_truncTotal (n := m + 1) f (by omega), ← MvPowerSeries.coeff_truncTotal (n := m + 1) g (by omega), h]`.
-/
theorem jeq_iff_truncTotal [Finite σ] (f g : MvPowerSeries σ R) :
    JEq m f g ↔ MvPowerSeries.truncTotal (m + 1) f = MvPowerSeries.truncTotal (m + 1) g := by
  constructor
  · intro h
    ext e
    by_cases he : e.degree ≤ m
    · rw [MvPowerSeries.coeff_truncTotal _ (by omega), MvPowerSeries.coeff_truncTotal _ (by omega), h e he]
    · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega), MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega)]
  · intro h e he
    rw [← MvPowerSeries.coeff_truncTotal (n := m + 1) f (by omega),
      ← MvPowerSeries.coeff_truncTotal (n := m + 1) g (by omega), h]

/- English proof (translation)
Rewrite `k`, the goal using `[jeq_iff_truncTotal]`. Simplify using `only [jeq_iff_truncTotal] at h`. Rewrite using `[MvPowerSeries.truncTotal_subst ha, MvPowerSeries.truncTotal_subst ha', k]`. Simplify using `only [h]`.
-/
theorem jeq_subst [Finite σ] {τ : Type} [Finite τ] {a a' : σ → MvPowerSeries τ R} {f g : MvPowerSeries σ R}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha' : ∀ i, MvPowerSeries.constantCoeff (a' i) = 0)
    (h : ∀ i, JEq m (a i) (a' i)) (k : JEq m f g) :
    JEq m (MvPowerSeries.subst a f) (MvPowerSeries.subst a' g) := by
  rw [jeq_iff_truncTotal] at k ⊢
  simp only [jeq_iff_truncTotal] at h
  rw [MvPowerSeries.truncTotal_subst ha, MvPowerSeries.truncTotal_subst ha', k]
  simp only [h]

/- English proof (translation)
Establish `h : orig R σ = MvPolynomial.idealOfVars σ R` using `rfl`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, h, MvPolynomial.mem_pow_idealOfVars_iff']`. Simplify using `[Nat.lt_succ_iff]`.
-/
theorem jet_mk_eq_zero_iff (p : MvPolynomial σ R) :
    (Ideal.Quotient.mk _ p : Jet R σ m) = 0 ↔ ∀ e : σ →₀ ℕ, e.degree ≤ m → p.coeff e = 0 := by
  have h : orig R σ = MvPolynomial.idealOfVars σ R := rfl
  rw [Ideal.Quotient.eq_zero_iff_mem, h, MvPolynomial.mem_pow_idealOfVars_iff']
  simp [Nat.lt_succ_iff]

/- English proof (translation)
Unfold `degLE`. Rewrite using `[Finset.mem_filter]`. Establish `hd : (e.sum fun _ k => k) = e.degree` using `rfl`. Rewrite using `[hd]`. Use `⟨fun h => h.2, fun h => ⟨?_, h⟩⟩` and prove the remaining obligations.

Use `Finset.mem_image.2 ⟨fun i => ⟨e i, Nat.lt_succ_of_le ((Finsupp.le_degree i e).trans h)⟩, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem mem_degLE_iff [Fintype σ] [DecidableEq σ] (e : σ →₀ ℕ) : e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter]
  have hd : (e.sum fun _ k => k) = e.degree := rfl
  rw [hd]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  refine Finset.mem_image.2 ⟨fun i => ⟨e i, Nat.lt_succ_of_le ((Finsupp.le_degree i e).trans h)⟩,
    Finset.mem_univ _, ?_⟩
  ext i
  simp

/- English proof (translation)
Unfold `psTrunc`. Rewrite using `[MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Simplify using `[mem_degLE_iff]`.
-/
theorem coeff_psTrunc_ite [Fintype σ] [DecidableEq σ] (f : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    (psTrunc m f).coeff e = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [mem_degLE_iff]

/- English proof (translation)
Rewrite using `[← sub_eq_zero (a := psJet m f), psJet, psJet, ← map_sub, jet_mk_eq_zero_iff]`. Use `forall_congr' fun e => forall_congr' fun he => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_sub, coeff_psTrunc_ite, coeff_psTrunc_ite, if_pos he, if_pos he, sub_eq_zero]`.
-/
theorem jeq_iff_psJet [Fintype σ] [DecidableEq σ] (f g : MvPowerSeries σ R) :
    JEq m f g ↔ psJet m f = psJet m g := by
  rw [← sub_eq_zero (a := psJet m f), psJet, psJet, ← map_sub, jet_mk_eq_zero_iff]
  refine forall_congr' fun e => forall_congr' fun he => ?_
  rw [MvPolynomial.coeff_sub, coeff_psTrunc_ite, coeff_psTrunc_ite, if_pos he, if_pos he, sub_eq_zero]

/- English proof (translation)
The claim follows from `MvPowerSeries.ext fun e => h _ e le_rfl`.
-/
theorem eq_of_jeq {f g : MvPowerSeries σ R} (h : ∀ m', JEq m' f g) : f = g :=
  MvPowerSeries.ext fun e => h _ e le_rfl

/- English proof (translation)
Introduce `_ _ _` and use `⟨fun _ _ _ _ _ h k => ⟨jeq_add h k, jeq_sub h k, jeq_mul h k⟩, fun _ _ _ _ hu h => jeq_cancel hu h, fun _ _ _ β _ _ h => jeq_map β h, fun _ _ _ _ _ _ _ ha ha' h k => jeq_subst (fun p => ha p.1 p.2) (fun p => ha' p.1 p.2) (fun p => h p.1 p.2) k, fun _ _ _ f g => jeq_iff_psJet f g, …`.
-/
theorem jeq_calculus : ∀ (R : Type) [CommRing R] (m : ℕ), (∀ (σ : Type) (f f' g g' : MvPowerSeries σ R), JEq m f f' → JEq m g g' → JEq m (f + g) (f' + g') ∧ JEq m (f - g) (f' - g') ∧ JEq m (f * g) (f' * g')) ∧ (∀ (σ : Type) (f g u : MvPowerSeries σ R), IsUnit (MvPowerSeries.constantCoeff u) → JEq m (f * u) (g * u) → JEq m f g) ∧ (∀ (σ R' : Type) [CommRing R'] (β : R →+* R') (f g : MvPowerSeries σ R), JEq m f g → JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g)) ∧ (∀ (d n n' : ℕ) (a a' : Fin n → Pt R n' d) (f g : PS R n d), (∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) → (∀ i j, MvPowerSeries.constantCoeff (a' i j) = 0) → (∀ i j, JEq m (a i j) (a' i j)) → JEq m f g → JEq m (ev a f) (ev a' g)) ∧ (∀ (σ : Type) [Fintype σ] [DecidableEq σ] (f g : MvPowerSeries σ R), JEq m f g ↔ psJet m f = psJet m g) ∧ (∀ (σ : Type) (f g : MvPowerSeries σ R), (∀ m', JEq m' f g) → f = g) :=
  fun _ _ _ =>
  ⟨fun _ _ _ _ _ h k => ⟨jeq_add h k, jeq_sub h k, jeq_mul h k⟩,
    fun _ _ _ _ hu h => jeq_cancel hu h,
    fun _ _ _ β _ _ h => jeq_map β h,
    fun _ _ _ _ _ _ _ ha ha' h k => jeq_subst (fun p => ha p.1 p.2) (fun p => ha' p.1 p.2) (fun p => h p.1 p.2) k,
    fun _ _ _ f g => jeq_iff_psJet f g,
    fun _ _ _ h => eq_of_jeq h⟩

end GlobalTheory.ChartCmp.JCalc
