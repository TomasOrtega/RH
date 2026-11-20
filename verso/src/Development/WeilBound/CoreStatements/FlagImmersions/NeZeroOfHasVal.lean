import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosedStatement

noncomputable section

namespace RootFieldNumerics.Bh

open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

/- English proof (translation)
Establish `hc0 : (∏ k, y ⟨k, c k⟩) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => hc k`. Establish `hle : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤ chartRingZ y c`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Use `show (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩ ∈ chartRingZ y c`.

Rewrite using `[← Finset.prod_div_distrib]`. Conclude with `Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩`. Establish `hge : chartRingZ y c ≤ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨k, i⟩, rfl⟩`.

Use `Algebra.subset_adjoin ⟨Function.update c k i, ?_⟩` and prove the remaining obligations. Use `show (∏ k', y ⟨k', Function.update c k i k'⟩) / ∏ k, y ⟨k, c k⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩`. Rewrite using `[← Finset.prod_div_distrib, Finset.prod_eq_single k]`. Rewrite using `[Function.update_self]`. Introduce `k' _ h`.

Rewrite using `[Function.update_of_ne h, div_self (hc k')]`. Simplify using the standard rewrite rules. Establish `hmem : a ∈ chartRingZ y c`. Use `hle ((T.ring c hc0 a).2 fun q hq => ?_)` and prove the remaining obligations. Take `⟨h1, -, h3⟩` from `GlobalTheory.T.regAt_fraction_noetherian_closed X Ω ξ T.gen q`.

Establish `h4` using `h3 (hn q.1).2`. Set `φ : chartRingZ y c →+* regAt ξ q` to `(algebraMap (chartRingZ y c) Ω).codRestrict _ fun r => (T.ring c hc0 r).1 (hge r.2) q hq`. Establish `h5 : IsIntegral (regAt ξ q) a` using `IsIntegral.map_of_comp_eq φ (RingHom.id Ω) rfl ha`. Take `⟨r, rfl⟩` from `(isIntegrallyClosed_iff Ω).1 h4 h5`. Conclude with `r.2`.

Unfold `chartRingZ at hmem`. Rewrite `hmem` using `[Algebra.adjoin_range_eq_range_aeval]`. Conclude with `hmem`.
-/
theorem exists_poly (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (hn : IsNormalScheme X)
    (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : Ω} (ha : a ∈ integralClosure (chartRingZ y c) Ω) :
    ∃ p : MRing J, aeval (fun q : Σ k, J k => y q / y ⟨q.1, c q.1⟩) p = a := by
  classical
  have hc0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have hle : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤ chartRingZ y c := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    show (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩ ∈ chartRingZ y c
    rw [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
  have hge : chartRingZ y c ≤ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    refine Algebra.subset_adjoin ⟨Function.update c k i, ?_⟩
    show (∏ k', y ⟨k', Function.update c k i k'⟩) / ∏ k, y ⟨k, c k⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · rw [Function.update_self]
    · intro k' _ h
      rw [Function.update_of_ne h, div_self (hc k')]
    · simp
  have hmem : a ∈ chartRingZ y c := by
    refine hle ((T.ring c hc0 a).2 fun q hq => ?_)
    obtain ⟨h1, -, h3⟩ := GlobalTheory.T.regAt_fraction_noetherian_closed X Ω ξ T.gen q
    have h4 := h3 (hn q.1).2
    let φ : chartRingZ y c →+* regAt ξ q :=
      (algebraMap (chartRingZ y c) Ω).codRestrict _ fun r => (T.ring c hc0 r).1 (hge r.2) q hq
    have h5 : IsIntegral (regAt ξ q) a := IsIntegral.map_of_comp_eq φ (RingHom.id Ω) rfl ha
    obtain ⟨r, rfl⟩ := (isIntegrallyClosed_iff Ω).1 h4 h5
    exact r.2
  unfold chartRingZ at hmem
  rw [Algebra.adjoin_range_eq_range_aeval] at hmem
  exact hmem

variable {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ}

/- English proof (translation)
Take `⟨r, hr, e⟩` from `(h.2 k c (IsUnit.mk0 _ hc)).2 i`. Rewrite using `[e, mul_div_cancel_right₀ _ hc]` and apply the resulting hypothesis.
-/
theorem val_ratio (h : CoordsAt ξ y z w) (k : K) (i c : J k) (hc : w ⟨k, c⟩ ≠ 0) :
    ValAt ξ z (y ⟨k, i⟩ / y ⟨k, c⟩) (w ⟨k, i⟩ / w ⟨k, c⟩) := by
  obtain ⟨r, hr, e⟩ := (h.2 k c (IsUnit.mk0 _ hc)).2 i
  rwa [e, mul_div_cancel_right₀ _ hc]

/- English proof (translation)
Establish `: ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, a k) (∏ k ∈ s, r k)` using `fun s => by`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using CxVal.one hz`. Consider the case `insert k s hk ih`. Rewrite using `[Finset.prod_insert hk, Finset.prod_insert hk]`.

Conclude with `CxVal.mul (h k) ih`. Conclude with `this _`.
-/
theorem val_prod (hz : genPt ξ ⤳ centre z) {a : K → Ω} {r : K → ℂ} (h : ∀ k, ValAt ξ z (a k) (r k)) :
    ValAt ξ z (∏ k, a k) (∏ k, r k) := by
  classical
  have : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, a k) (∏ k ∈ s, r k) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using CxVal.one hz
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact CxVal.mul (h k) ih
  exact this _

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using CxVal.one hz`. Consider the case `succ n ih => rw [pow_succ, pow_succ]`. Conclude with `CxVal.mul ih h`.
-/
theorem val_pow (hz : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  induction n with
  | zero => simpa using CxVal.one hz
  | succ n ih => rw [pow_succ, pow_succ]; exact CxVal.mul ih h

def fn (y : (Σ k, J k) → Ω) (s : Ω) (m : ℕ) (k₀ : K) (i₀ : J k₀) (c : (k : K) → J k) : Ω :=
  s * (∏ k, y ⟨k, c k⟩) / y ⟨k₀, i₀⟩ ^ m

/- English proof (translation)
Establish `h1` using `CxVal.aeval hz (fun q : Σ k, J k => val_ratio h q.1 q.2 (c' q.1) (hc q.1)) p`. Establish `h2` using `val_prod hz fun k => val_ratio h k (c k) (c' k) (hc k)`. Establish `h3` using `val_pow hz (val_ratio h k₀ (c' k₀) i₀ hi) m`. Establish `hy` using `fun k => (h.2 k (c' k) (IsUnit.mk0 _ (hc k))).1`. Establish `hy0` using `(h.2 k₀ i₀ (IsUnit.mk0 _ hi)).1`.

Establish `hP : (∏ k, y ⟨k, c' k⟩) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => hy k`. Establish `hk` using `hy k₀`. Use `CxVal.mul (CxVal.mul h1 h2) h3 using 1` and compare the differences between its conclusion and the goal. Establish `hp' : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c' q.1⟩) p = fn y s m k₀ (c' k₀) c'` using `hp`. Rewrite using `[hp', Finset.prod_div_distrib, div_pow]`.

Unfold `fn`. Clear the denominators using the available nonvanishing facts.
-/
theorem val_fn (hz : genPt ξ ⤳ centre z) (h : CoordsAt ξ y z w) {s : Ω} {m : ℕ} {k₀ : K} (i₀ : J k₀) (c c' : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c' k⟩ ≠ 0) (hi : w ⟨k₀, i₀⟩ ≠ 0) {p : MRing J}
    (hp : aeval (fun q : Σ k, J k => y q / y ⟨q.1, c' q.1⟩) p = fn y s m k₀ (c' k₀) c') :
    ValAt ξ z (fn y s m k₀ i₀ c) (aeval (fun q : Σ k, J k => w q / w ⟨q.1, c' q.1⟩) p * (∏ k, w ⟨k, c k⟩ / w ⟨k, c' k⟩) *
      (w ⟨k₀, c' k₀⟩ / w ⟨k₀, i₀⟩) ^ m) := by
  have h1 := CxVal.aeval hz (fun q : Σ k, J k => val_ratio h q.1 q.2 (c' q.1) (hc q.1)) p
  have h2 := val_prod hz fun k => val_ratio h k (c k) (c' k) (hc k)
  have h3 := val_pow hz (val_ratio h k₀ (c' k₀) i₀ hi) m
  have hy := fun k => (h.2 k (c' k) (IsUnit.mk0 _ (hc k))).1
  have hy0 := (h.2 k₀ i₀ (IsUnit.mk0 _ hi)).1
  have hP : (∏ k, y ⟨k, c' k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  have hk := hy k₀
  convert CxVal.mul (CxVal.mul h1 h2) h3 using 1
  have hp' : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c' q.1⟩) p = fn y s m k₀ (c' k₀) c' := hp
  rw [hp', Finset.prod_div_distrib, div_pow]
  unfold fn
  field_simp

/- English proof (translation)
Establish `e : ∀ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k - 1)) = y ⟨k, c k⟩ / y ⟨k, c k⟩ ^ ((m : ℤ) * a k)` using `fun k => by`. Rewrite using `[neg_sub, zpow_sub₀ (hc k), zpow_one]`. Simplify using `only [e, Finset.prod_div_distrib]`. Rewrite using `[Finset.prod_eq_single k₀ (f := fun k => y ⟨k, c k⟩ ^ ((m : ℤ) * a k))]`. Rewrite using `[ha.1, mul_one, zpow_natCast, fn, mul_div_assoc]`.

Introduce `k _ h`. Rewrite using `[ha.2 k h, mul_zero, zpow_zero]`. Simplify using the standard rewrite rules.
-/
theorem fn_eq [DecidableEq K] {s : Ω} {m : ℕ} {k₀ : K} {a : K → ℤ} (ha : a k₀ = 1 ∧ ∀ k, k ≠ k₀ → a k = 0)
    (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    s * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k - 1)) = fn y s m k₀ (c k₀) c := by
  have e : ∀ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k - 1)) = y ⟨k, c k⟩ / y ⟨k, c k⟩ ^ ((m : ℤ) * a k) := fun k => by
    rw [neg_sub, zpow_sub₀ (hc k), zpow_one]
  simp only [e, Finset.prod_div_distrib]
  rw [Finset.prod_eq_single k₀ (f := fun k => y ⟨k, c k⟩ ^ ((m : ℤ) * a k))]
  · rw [ha.1, mul_one, zpow_natCast, fn, mul_div_assoc]
  · intro k _ h
    rw [ha.2 k h, mul_zero, zpow_zero]
  · simp

/- English proof (translation)
Take `⟨dg, dh, g, h', hg, hh, hd, e1, hne, e2⟩` from `hs`. Establish `hy` using `fun k => (h.2 k (c k) (IsUnit.mk0 _ (hc k))).1`. Establish `V` using `fun f : MRing J => CxVal.aeval hz (fun q : Σ k, J k => val_ratio h q.1 q.2 (c q.1) (hc q.1)) f`. Establish `ey : y = fun q => y ⟨q.1, c q.1⟩ * (y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩)`. Use function extensionality and compare the values at `fun q => (mul_div_cancel₀ _ (hy q.1)).symm`.

Establish `ew : w = fun q => w ⟨q.1, c q.1⟩ * (w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩)`. Use function extensionality and compare the values at `fun q => (mul_div_cancel₀ _ (hc q.1)).symm`. Establish `g1` using `aeval_blockScale hg (fun k => y ⟨k, c k⟩) fun q => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩`. Establish `g2` using `aeval_blockScale hh (fun k => y ⟨k, c k⟩) fun q => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩`. Establish `g3` using `aeval_blockScale hg (fun k => w ⟨k, c k⟩) fun q => w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩`.

Rewrite `g1`, `g2` using `[← ey]`. Rewrite `g3` using `[← ew]`. Establish `key : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) g = aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) p * aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) h'`. Establish `hp' : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) p = s * ∏ k, y ⟨k, c k⟩ ^ (-a k)` using `hp`. Establish `h0 : (∏ k, y ⟨k, c k⟩ ^ dg k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)`.

Establish `h1 : (∏ k, y ⟨k, c k⟩ ^ dg k) * ∏ k, y ⟨k, c k⟩ ^ (-a k) = ∏ k, y ⟨k, c k⟩ ^ dh k`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k), hd k]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `mul_left_cancel₀ h0 ?_` and prove the remaining obligations. Rewrite using `[← g1, e1, g2, hp', ← h1]`. Expand and normalize the polynomial expressions, which then agree. Establish `e3` using `CxVal.unique (key ▸ V g) (CxVal.mul (V p) (V h'))`.

Introduce `h0`. Establish `h0' : aeval (fun q : Σ k, J k => w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩) p = 0` using `h0`. Rewrite `e3` using `[h0', zero_mul]`. Rewrite `g3` using `[e3, mul_zero, e2]`. Conclude with `mul_ne_zero hv hne g3`.
-/
theorem ne_zero_of_hasVal (hz : genPt ξ ⤳ centre z) (h : CoordsAt ξ y z w) {s : Ω} {a : K → ℤ} (c : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) {p : MRing J}
    (hp : aeval (fun q : Σ k, J k => y q / y ⟨q.1, c q.1⟩) p = s * ∏ k, y ⟨k, c k⟩ ^ (-a k)) {v : ℂ} (hv : v ≠ 0)
    (hs : Small.HasVal y a s w v) : aeval (fun q : Σ k, J k => w q / w ⟨q.1, c q.1⟩) p ≠ 0 := by
  obtain ⟨dg, dh, g, h', hg, hh, hd, e1, hne, e2⟩ := hs
  have hy := fun k => (h.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  have V := fun f : MRing J => CxVal.aeval hz (fun q : Σ k, J k => val_ratio h q.1 q.2 (c q.1) (hc q.1)) f
  have ey : y = fun q => y ⟨q.1, c q.1⟩ * (y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) :=
    funext fun q => (mul_div_cancel₀ _ (hy q.1)).symm
  have ew : w = fun q => w ⟨q.1, c q.1⟩ * (w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩) :=
    funext fun q => (mul_div_cancel₀ _ (hc q.1)).symm
  have g1 := aeval_blockScale hg (fun k => y ⟨k, c k⟩) fun q => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩
  have g2 := aeval_blockScale hh (fun k => y ⟨k, c k⟩) fun q => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩
  have g3 := aeval_blockScale hg (fun k => w ⟨k, c k⟩) fun q => w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩
  rw [← ey] at g1 g2
  rw [← ew] at g3
  have key : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) g =
      aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) p *
        aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) h' := by
    have hp' : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) p = s * ∏ k, y ⟨k, c k⟩ ^ (-a k) := hp
    have h0 : (∏ k, y ⟨k, c k⟩ ^ dg k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
    have h1 : (∏ k, y ⟨k, c k⟩ ^ dg k) * ∏ k, y ⟨k, c k⟩ ^ (-a k) = ∏ k, y ⟨k, c k⟩ ^ dh k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k), hd k]
      congr 1
      ring
    refine mul_left_cancel₀ h0 ?_
    rw [← g1, e1, g2, hp', ← h1]
    ring
  have e3 := CxVal.unique (key ▸ V g) (CxVal.mul (V p) (V h'))
  intro h0
  have h0' : aeval (fun q : Σ k, J k => w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩) p = 0 := h0
  rw [h0', zero_mul] at e3
  rw [e3, mul_zero, e2] at g3
  exact mul_ne_zero hv hne g3

end RootFieldNumerics.Bh
