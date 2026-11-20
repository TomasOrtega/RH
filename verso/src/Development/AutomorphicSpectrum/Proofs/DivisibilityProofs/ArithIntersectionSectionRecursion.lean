import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import Development.WeilBound.CoreStatements.FlagImmersions.PointsIntegralSectionSnoc
import Development.WeilBound.CoreStatements.HodgeTatePoints.GfForms
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.EffLat

open PositivityTheory.HtPt.Gf (hom_mul hom_add hom_mon hom_of_eq hom_sub aeval_mon mon_not_mem mem_mCoordIdeal mon)
open GroundTheory.Heights₂.Heights.NumbersDVR (length_localizedQuot_ne_top mem_minimalPrimes_sup_span_mul
  length_localizedQuot_sup_span_mul localizedQuot_subsingleton_of_not_le)

/- English proof (translation)
Establish `hPW : P ≤ W` using `le_sup_left.trans hW.1.2`. Establish `htP : t ∉ P` using `fun h' => ht (hPW h')`. Establish `hrP : r ∉ P`. Introduce `hr`. Establish `h1 : t * g ∈ P`.

Use `P.add_mem hrel (P.mul_mem_right h hr)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Conclude with `(hP.mem_or_mem h1).elim htP hg`. Establish `hm` using `mem_minimalPrimes_sup_span_mul (P := P) (x := h) (y := r) hrP hW`. Establish `heq : P ⊔ Ideal.span {h * r} = P ⊔ Ideal.span {t * g}`.

Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)` and prove the remaining obligations. Establish `e : h * r = t * g - (t * g - r * h)` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hrel)`.

Use `sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)` and prove the remaining obligations. Establish `e : t * g = (t * g - r * h) + h * r` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left hrel) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Rewrite `hm` using `[heq]`.

Establish `htg : t * g ∈ W` using `hm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Establish `hgW : g ∈ W` using `(hWp.mem_or_mem htg).resolve_left ht`. Establish `hWg : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes`. Use `⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hgW)⟩, fun Q hQ hQW => ?_⟩` and prove the remaining obligations. Use `hm.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ hQW` and prove the remaining obligations.

Conclude with `Q.mul_mem_left t (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))`. Use `⟨hWg, ?_⟩` and prove the remaining obligations. Establish `e1` using `length_localizedQuot_sup_span_mul P W (x := t) g htP`. Establish `e2` using `length_localizedQuot_sup_span_mul P W (x := r) h hrP`. Establish `heq' : P ⊔ Ideal.span {r * h} = P ⊔ Ideal.span {t * g}` using `by rw [mul_comm r h, heq]`.

Rewrite `e2` using `[heq']`. Establish `ht0 : Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {t}))) = 0`. Establish `hnle : ¬ (P ⊔ Ideal.span {t}) ≤ W` using `fun h' => ht (h' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))`. Use `localizedQuot_subsingleton_of_not_le (P ⊔ Ideal.span {t}) W hnle` as an intermediate fact. Conclude with `Module.length_eq_zero_iff.mpr this`.

Rewrite `e1` using `[ht0, add_zero]`. Establish `hfin` using `length_localizedQuot_ne_top _ W hm`. Rewrite `hfin`, `e2` using `[e1]`. Use `ENat.toNat_le_toNat ?_ hfin` and prove the remaining obligations. Rewrite using `[e2]`.

Conclude with `le_self_add`.
-/
theorem len_le_of_rel {A : Type*} [CommRing A] [IsNoetherianRing A] {P W : Ideal A} [hP : P.IsPrime]
    [hWp : W.IsPrime] {g h t r : A} (hg : g ∉ P) (ht : t ∉ W) (hrel : t * g - r * h ∈ P)
    (hW : W ∈ (P ⊔ Ideal.span {h}).minimalPrimes) :
    W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧
      (Module.length (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {h})))).toNat ≤
      (Module.length (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {g})))).toNat := by
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have htP : t ∉ P := fun h' => ht (hPW h')
  have hrP : r ∉ P := by
    intro hr
    have h1 : t * g ∈ P := by
      have := P.add_mem hrel (P.mul_mem_right h hr)
      rwa [sub_add_cancel] at this
    exact (hP.mem_or_mem h1).elim htP hg
  have hm := mem_minimalPrimes_sup_span_mul (P := P) (x := h) (y := r) hrP hW
  have heq : P ⊔ Ideal.span {h * r} = P ⊔ Ideal.span {t * g} := by
    apply le_antisymm
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : h * r = t * g - (t * g - r * h) := by ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        (Ideal.mem_sup_left hrel)
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : t * g = (t * g - r * h) + h * r := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hrel)
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [heq] at hm
  have htg : t * g ∈ W := hm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hgW : g ∈ W := (hWp.mem_or_mem htg).resolve_left ht
  have hWg : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes := by
    refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hgW)⟩, fun Q hQ hQW => ?_⟩
    refine hm.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2)
      ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ hQW
    exact Q.mul_mem_left t (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  refine ⟨hWg, ?_⟩
  have e1 := length_localizedQuot_sup_span_mul P W (x := t) g htP
  have e2 := length_localizedQuot_sup_span_mul P W (x := r) h hrP
  have heq' : P ⊔ Ideal.span {r * h} = P ⊔ Ideal.span {t * g} := by rw [mul_comm r h, heq]
  rw [heq'] at e2
  have ht0 : Module.length (Localization.AtPrime W)
      (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {t}))) = 0 := by
    have hnle : ¬ (P ⊔ Ideal.span {t}) ≤ W := fun h' =>
      ht (h' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    have := localizedQuot_subsingleton_of_not_le (P ⊔ Ideal.span {t}) W hnle
    exact Module.length_eq_zero_iff.mpr this
  rw [ht0, add_zero] at e1
  have hfin := length_localizedQuot_ne_top _ W hm
  rw [e1] at hfin e2
  refine ENat.toNat_le_toNat ?_ hfin
  rw [e2]
  exact le_self_add

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Introduce `h0`. Apply `h` to reduce the goal to its premises. Rewrite using `[mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]`.
-/
theorem y_ne_of_not_mem {y : (Σ k, ι k) → Ω} {p : Σ k, ι k}
    (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [mConeMap]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, hp]`.

Use `congr 1`. Simplify using `[mConeMap]`.
-/
theorem eval_one_coneMap (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    eval (fun _ => (1 : Ω)) (mConeMap y f) = aeval y f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    simp [mConeMap]

/- English proof (translation)
Introduce `h`. Apply `hf` to reduce the goal to its premises. Rewrite using `[← eval_one_coneMap]`. Establish `h0 : mConeMap y f = 0` using `h`. Rewrite using `[h0, map_zero]`.
-/
theorem not_mem_of_aeval_ne {y : (Σ k, ι k) → Ω} {f : MRing ι} (hf : aeval y f ≠ 0) :
    f ∉ mCoordIdeal y := by
  intro h
  apply hf
  rw [← eval_one_coneMap]
  have h0 : mConeMap y f = 0 := h
  rw [h0, map_zero]

/- English proof (translation)
Simplify using `only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]`.
-/
theorem prod_pow_add (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a b : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (a + b) k = (∏ k, y ⟨k, c k⟩ ^ a k) * ∏ k, y ⟨k, c k⟩ ^ b k := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]

/- English proof (translation)
Unfold `chartRingZ at ht`. Proceed by induction on `ht using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨p, rfl⟩` from `hx`. Use `⟨Pi.single p.1 1, X p, ?_, ?_⟩` and prove the remaining obligations.

Introduce `m hm k`. Rewrite `hm` using `[support_X]`. Rewrite using `[Finset.mem_singleton.mp hm]`. Take `⟨k0, i0⟩` from `p`. Distinguish the cases in `hk : k = k0`.

Substitute `hk` using the available equality. Simplify using `[Finsupp.single_apply]`. Establish `: ∀ i, (Finsupp.single (⟨k0, i0⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩ = 0`. Introduce `i`. Rewrite using `[Finsupp.single_apply, if_neg]`.

Introduce `h`. Conclude with `hk (congrArg Sigma.fst h).symm`. Simplify using `[this, Pi.single_eq_of_ne hk]`. Establish `hprod : ∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 1 : K → ℕ) k = y ⟨p.1, c p.1⟩`. Rewrite using `[Finset.prod_eq_single p.1 (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]`.

Simplify using the standard rewrite rules. Rewrite using `[hprod, aeval_X, div_mul_cancel₀ _ (hc _)]`. Consider the case `algebraMap n`. Use `⟨0, C n, ?_, by simp⟩` and prove the remaining obligations. Introduce `m hm k`.

Rewrite `hm` using `[C_apply]`. Rewrite using `[Finset.mem_singleton.mp (support_monomial_subset hm)]`. Simplify using the standard rewrite rules. Consider the case `add a b _ _ h1 h2`. Take `⟨N1, r1, hr1, e1⟩` from `h1`.

Take `⟨N2, r2, hr2, e2⟩` from `h2`. Use `⟨N1 + N2, r1 * mon c N2 + r2 * mon c N1, hom_add (hom_mul hr1 (hom_mon c N2)) (hom_of_eq (hom_mul hr2 (hom_mon c N1)) fun k => by simp [add_comm]), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, aeval_mon, aeval_mon, e1, e2, prod_pow_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul a b _ _ h1 h2`.

Take `⟨N1, r1, hr1, e1⟩` from `h1`. Take `⟨N2, r2, hr2, e2⟩` from `h2`. Use `⟨N1 + N2, r1 * r2, hom_mul hr1 hr2, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, e1, e2, prod_pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_form_of_mem_chart {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {t : Ω} (ht : t ∈ chartRingZ y c) :
    ∃ (N : K → ℕ) (r : MRing ι), IsMultiHomog r N ∧ aeval y r = t * ∏ k, y ⟨k, c k⟩ ^ N k := by
  classical
  unfold chartRingZ at ht
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨Pi.single p.1 1, X p, ?_, ?_⟩
    · intro m hm k
      rw [support_X] at hm
      rw [Finset.mem_singleton.mp hm]
      obtain ⟨k0, i0⟩ := p
      by_cases hk : k = k0
      · subst hk
        simp [Finsupp.single_apply]
      · have : ∀ i, (Finsupp.single (⟨k0, i0⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩ = 0 := by
          intro i
          rw [Finsupp.single_apply, if_neg]
          intro h
          exact hk (congrArg Sigma.fst h).symm
        simp [this, Pi.single_eq_of_ne hk]
    · have hprod : ∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 1 : K → ℕ) k = y ⟨p.1, c p.1⟩ := by
        rw [Finset.prod_eq_single p.1 (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
        simp
      rw [hprod, aeval_X, div_mul_cancel₀ _ (hc _)]
  | algebraMap n =>
    refine ⟨0, C n, ?_, by simp⟩
    intro m hm k
    rw [C_apply] at hm
    rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
    simp
  | add a b _ _ h1 h2 =>
    obtain ⟨N1, r1, hr1, e1⟩ := h1
    obtain ⟨N2, r2, hr2, e2⟩ := h2
    refine ⟨N1 + N2, r1 * mon c N2 + r2 * mon c N1, hom_add (hom_mul hr1 (hom_mon c N2))
      (hom_of_eq (hom_mul hr2 (hom_mon c N1)) fun k => by simp [add_comm]), ?_⟩
    rw [map_add, map_mul, map_mul, aeval_mon, aeval_mon, e1, e2, prod_pow_add]
    ring
  | mul a b _ _ h1 h2 =>
    obtain ⟨N1, r1, hr1, e1⟩ := h1
    obtain ⟨N2, r2, hr2, e2⟩ := h2
    refine ⟨N1 + N2, r1 * r2, hom_mul hr1 hr2, ?_⟩
    rw [map_mul, e1, e2, prod_pow_add]
    ring

/- English proof (translation)
Take `⟨N, r, hr, er⟩` from `exists_form_of_mem_chart hc hs`. Set `v : K → ℕ` to `fun k => (a k).toNat`. Set `u : K → ℕ` to `fun k => N k + (-a k).toNat`. Use `⟨u, r * mon c v, mem_mCoordIdeal (d := u + dg) (hom_sub (hom_mul (hom_mon c u) hg) (hom_of_eq (hom_mul (hom_mul hr (hom_mon c v)) hh) ?_)) ?_⟩` and prove the remaining obligations. Introduce `k`.

Use `hd k` as an intermediate fact. Simplify using `only [Pi.add_apply, u, v]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[map_sub, map_mul, map_mul, map_mul, aeval_mon, aeval_mon, e, er, sub_eq_zero]`. Establish `key : ∏ k, y ⟨k, c k⟩ ^ u k = (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) * (∏ k, y ⟨k, c k⟩ ^ N k) * ∏ k, y ⟨k, c k⟩ ^ v k`.

Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hy` using `hc k`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hy, ← zpow_add₀ hy]`. Use `congr 1`.

Simplify using `only [u, v]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chart_rel {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : K → ℤ} {s : Ω}
    (hs : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ chartRingZ y c) {g h : MRing ι}
    {dg dh : K → ℕ} (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh)
    (hd : ∀ k, (dg k : ℤ) = dh k + a k) (e : aeval y g = s * aeval y h) :
    ∃ (u : K → ℕ) (r : MRing ι), mon c u * g - r * h ∈ mCoordIdeal y := by
  obtain ⟨N, r, hr, er⟩ := exists_form_of_mem_chart hc hs
  let v : K → ℕ := fun k => (a k).toNat
  let u : K → ℕ := fun k => N k + (-a k).toNat
  refine ⟨u, r * mon c v, mem_mCoordIdeal (d := u + dg) (hom_sub (hom_mul (hom_mon c u) hg)
    (hom_of_eq (hom_mul (hom_mul hr (hom_mon c v)) hh) ?_)) ?_⟩
  · intro k
    have := hd k
    simp only [Pi.add_apply, u, v]
    omega
  · rw [map_sub, map_mul, map_mul, map_mul, aeval_mon, aeval_mon, e, er, sub_eq_zero]
    have key : ∏ k, y ⟨k, c k⟩ ^ u k = (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) *
        (∏ k, y ⟨k, c k⟩ ^ N k) * ∏ k, y ⟨k, c k⟩ ^ v k := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hy := hc k
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hy, ← zpow_add₀ hy]
      congr 1
      simp only [u, v]
      push_cast
      omega
    rw [key]
    ring

/- English proof (translation)
Take `⟨d, g0, h0, hg, hh, hne, e⟩` from `hb (s * ∏ k, y ⟨k, c k⟩ ^ (-a k))`. Use `⟨mon c (fun k => (a k).toNat) * g0, mon c (fun k => (-a k).toNat) * h0, _, _, hom_mul (hom_mon c _) hg, hom_mul (hom_mon c _) hh, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Simplify using `only [Pi.add_apply]`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[map_mul, aeval_mon]`. Conclude with `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)) hne`. Rewrite using `[map_mul, map_mul, aeval_mon, aeval_mon, e]`. Establish `key : (∏ k, y ⟨k, c k⟩ ^ (a k).toNat) * ∏ k, y ⟨k, c k⟩ ^ (-a k) = ∏ k, y ⟨k, c k⟩ ^ (-a k).toNat`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hy` using `hc k`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hy]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_rep {y : (Σ k, ι k) → Ω} (hb : Birational y) {c : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ) (s : Ω) :
    ∃ (g h : MRing ι) (dg dh : K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
      (∀ k, (dg k : ℤ) = dh k + a k) ∧ aeval y h ≠ 0 ∧ aeval y g = s * aeval y h := by
  obtain ⟨d, g0, h0, hg, hh, hne, e⟩ := hb (s * ∏ k, y ⟨k, c k⟩ ^ (-a k))
  refine ⟨mon c (fun k => (a k).toNat) * g0, mon c (fun k => (-a k).toNat) * h0, _, _,
    hom_mul (hom_mon c _) hg, hom_mul (hom_mon c _) hh, ?_, ?_, ?_⟩
  · intro k
    simp only [Pi.add_apply]
    push_cast
    omega
  · rw [map_mul, aeval_mon]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)) hne
  · rw [map_mul, map_mul, aeval_mon, aeval_mon, e]
    have key : (∏ k, y ⟨k, c k⟩ ^ (a k).toNat) * ∏ k, y ⟨k, c k⟩ ^ (-a k) =
        ∏ k, y ⟨k, c k⟩ ^ (-a k).toNat := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hy := hc k
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hy]
      congr 1
      omega
    rw [← key]
    ring

/- English proof (translation)
Use `set O : HermLine ι := HermLine.ofWeight (fun _ => (-1 : ℝ)) (fun _ _ _ => rfl) with hO`. Establish `hOs : IsSmoothHerm O` using `RootFieldNumerics.smooth_constLine _`. Establish `key : ∀ Y : HermLine ι, IsSmoothHerm Y → II K ι P (e + 2) (Fin.snoc (Fin.snoc L O : Fin (e + 1) → HermLine ι) Y) = ptsIntegral P (fun j z => Real.log (((Fin.snoc L Y : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1)`. Introduce `Y hY`. Establish `h1` using `RootFieldNumerics.intersection_constant_metric_line II hII.1 K ι P (e + 1) (Fin.snoc L Y) (-1) hP (RootFieldNumerics.smooth_snoc hL hY)`.

Rewrite `h1` using `[neg_neg, one_mul, ← hO, RootFieldNumerics.snoc_snoc_swap, (hII.1 K ι).1 P (e + 2) _ _ hP (RootFieldNumerics.smooth_snoc (RootFieldNumerics.smooth_snoc hL hOs) hY)]`. Conclude with `h1`. Rewrite using `[← key _ (isSmoothHerm_tensor hA hB), ← key _ hA, ← key _ hB]`. Conclude with `(hII.1 K ι).2.1 P (e + 1) _ A B hP (RootFieldNumerics.smooth_snoc hL hOs) hA hB`.
-/
theorem deg_tensor (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A B : HermLine ι)
    (hP : IsArithVar P (e + 2)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hB : IsSmoothHerm B) :
    ptsIntegral P (fun j z => Real.log (((Fin.snoc L (A.tensor B) : Fin (e + 1) → HermLine ι) j).h z))
        (fun _ => 1) =
      ptsIntegral P (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z))
        (fun _ => 1) +
      ptsIntegral P (fun j z => Real.log (((Fin.snoc L B : Fin (e + 1) → HermLine ι) j).h z))
        (fun _ => 1) := by
  set O : HermLine ι := HermLine.ofWeight (fun _ => (-1 : ℝ)) (fun _ _ _ => rfl) with hO
  have hOs : IsSmoothHerm O := RootFieldNumerics.smooth_constLine _
  have key : ∀ Y : HermLine ι, IsSmoothHerm Y →
      II K ι P (e + 2) (Fin.snoc (Fin.snoc L O : Fin (e + 1) → HermLine ι) Y) =
        ptsIntegral P (fun j z => Real.log (((Fin.snoc L Y : Fin (e + 1) → HermLine ι) j).h z))
          (fun _ => 1) := by
    intro Y hY
    have h1 := RootFieldNumerics.intersection_constant_metric_line II hII.1 K ι P (e + 1) (Fin.snoc L Y) (-1) hP
      (RootFieldNumerics.smooth_snoc hL hY)
    rw [neg_neg, one_mul, ← hO, RootFieldNumerics.snoc_snoc_swap,
      (hII.1 K ι).1 P (e + 2) _ _ hP (RootFieldNumerics.smooth_snoc (RootFieldNumerics.smooth_snoc hL hOs) hY)] at h1
    exact h1
  rw [← key _ (isSmoothHerm_tensor hA hB), ← key _ hA, ← key _ hB]
  exact (hII.1 K ι).2.1 P (e + 1) _ A B hP (RootFieldNumerics.smooth_snoc hL hOs) hA hB

end GlobalTheory.CompanionTheory.Ar.Top.EffLat

open GlobalTheory.CompanionTheory.Ar.Top.EffLat PositivityTheory.HtPt.Gf in

/- English proof (translation)
Introduce `II hII hD K _ ι _ Ω _ y e L A s hP hbir hL hA hs0 hs hnef`. Use `haveI hPp : (mCoordIdeal y).IsPrime := hP.2.1.1`. Use `choose c0 hc0 using hP.2.1.2.2`. Establish `hy0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0` using `fun k => y_ne_of_not_mem (hc0 k)`. Take `⟨g, h, dg, dh, hg, hh, hd, hhne, e1⟩` from `exists_rep hbir hy0 A.a s`.

Establish `hgne : aeval y g ≠ 0`. Rewrite using `[e1]`. Conclude with `mul_ne_zero hs0 hhne`. Establish `hgP` using `not_mem_of_aeval_ne hgne`. Establish `hhP` using `not_mem_of_aeval_ne hhne`.

Establish `hHs : IsSmoothHerm (HermLine.sqMetric (ι` using `ι) dh) := isSmoothHerm_sqMetric dh`. Establish `hGs` using `isSmoothHerm_tensor hA hHs`. Establish `secH : IsSectionOn (mCoordIdeal y) (HermLine.sqMetric (ι` using `ι) dh) h := ⟨dh, fun _ => rfl, hh, hhP⟩`. Establish `secG : IsSectionOn (mCoordIdeal y) (A.tensor (HermLine.sqMetric (ι` using `ι) dh)) g := by`. Use `⟨dg, fun k => ?_, hg, hgP⟩` and prove the remaining obligations.

Establish `: (A.tensor (HermLine.sqMetric (ι` using `ι) dh)).a k = A.a k + dh k := rfl`. Rewrite using `[this, hd k]`. Expand and normalize the polynomial expressions, which then agree. Establish `cutG` using `RootFieldNumerics.points_integral_section_snoc II hII hD K ι (mCoordIdeal y) e L _ g hP hL hGs secG`. Establish `cutH` using `RootFieldNumerics.points_integral_section_snoc II hII hD K ι (mCoordIdeal y) e L _ h hP hL hHs secH`.

Establish `hadd` using `deg_tensor II hII (mCoordIdeal y) e L A _ hP hL hA hHs`. Establish `hfin : ∀ f : MRing ι, ({W | W ∈ divSupp (mCoordIdeal y) f ∧ IsHorizontal W}).Finite` using `fun f => (divSupp_finite _ f).subset fun W hW => hW.1`. Establish `hInn : ∀ W, W ∈ divSupp (mCoordIdeal y) g → IsHorizontal W → 0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1)` using `fun W hW hh' => hnef W ((hD K ι _ (e + 1) _ g W hP secG hW).1 hh') (le_sup_left.trans hW.1.1.2)`. Establish `hkey : ∀ W, W ∈ divSupp (mCoordIdeal y) h → IsHorizontal W → W ∈ divSupp (mCoordIdeal y) g ∧ multAt (mCoordIdeal y ⊔ Ideal.span {h}) W ≤ multAt (mCoordIdeal y ⊔ Ideal.span {g}) W`. Introduce `W hW _`.

Take `⟨hWmin, hWrel⟩` from `hW`. Establish `hrel'` using `hWrel`. Use `choose c hcW using hWrel`. Establish `hPW : mCoordIdeal y ≤ W` using `le_sup_left.trans hWmin.1.2`. Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => y_ne_of_not_mem fun h' => hcW k (hPW h')`.

Establish `hsc : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * A.a k)) ∈ chartRingZ y c` using `hs c hyc`. Take `⟨u, r, hrel⟩` from `chart_rel hyc hsc hg hh hd e1`. Use `haveI hWp : W.IsPrime := hWmin.1.1`. Take `⟨hm, hle⟩` from `len_le_of_rel hgP (mon_not_mem hWp hcW u) hrel hWmin`. Use `⟨⟨hm, hrel'⟩, ?_⟩` and prove the remaining obligations.

Unfold `multAt`. Rewrite using `[dif_pos hWp, dif_pos hWp]`. Conclude with `hle`. Establish `cmp : (∑ᶠ (W) (_ : W ∈ divSupp (mCoordIdeal y) h ∧ IsHorizontal W), (multAt (mCoordIdeal y ⊔ Ideal.span {h}) W : ℝ) * ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1)) ≤ ∑ᶠ (W) (_ : W ∈ divSupp (mCoordIdeal y) g ∧ IsHorizontal W), (multAt (mCoordIdeal y ⊔ Ideal.span { …`. Express the relevant statement in the definitionally equal form `(∑ᶠ W ∈ {W | W ∈ divSupp (mCoordIdeal y) h ∧ IsHorizontal W}, _) ≤ ∑ᶠ W ∈ {W | W ∈ divSupp (mCoordIdeal y) g ∧ IsHorizontal W}, _`.

Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ (hfin h), finsum_mem_eq_finite_toFinset_sum _ (hfin g)]`. Use `(Finset.sum_le_sum fun W hW => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg (fun W hW => ?_) fun W hW _ => ?_)` and prove the remaining obligations. Rewrite `hW` using `[Set.Finite.mem_toFinset]`. Establish `h2` using `hkey W hW.1 hW.2`. Conclude with `mul_le_mul_of_nonneg_right (Nat.cast_le.2 h2.2) (hInn W h2.1 hW.2)`.

Rewrite `hW`, the goal using `[Set.Finite.mem_toFinset]`. Conclude with `⟨(hkey W hW.1 hW.2).1, hW.2⟩`. Rewrite `hW` using `[Set.Finite.mem_toFinset]`. Conclude with `mul_nonneg (Nat.cast_nonneg _) (hInn W hW.1 hW.2)`. Rewrite `hadd` using `[cutG, cutH]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem GlobalTheory.CompanionTheory.Ar.Top.eff_lat : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : Ω), IsArithVar (mCoordIdeal y) (e + 2) → Birational y → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → s ≠ 0 → s ∈ chartLat y A.a 1 → (∀ W, IsArithVar W (e + 1) → mCoordIdeal y ≤ W → 0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1)) → 0 ≤ ptsIntegral (mCoordIdeal y) (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) := by
  classical
  intro II hII hD K _ ι _ Ω _ y e L A s hP hbir hL hA hs0 hs hnef
  haveI hPp : (mCoordIdeal y).IsPrime := hP.2.1.1
  choose c0 hc0 using hP.2.1.2.2
  have hy0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0 := fun k => y_ne_of_not_mem (hc0 k)
  obtain ⟨g, h, dg, dh, hg, hh, hd, hhne, e1⟩ := exists_rep hbir hy0 A.a s
  have hgne : aeval y g ≠ 0 := by
    rw [e1]
    exact mul_ne_zero hs0 hhne
  have hgP := not_mem_of_aeval_ne hgne
  have hhP := not_mem_of_aeval_ne hhne
  have hHs : IsSmoothHerm (HermLine.sqMetric (ι := ι) dh) := isSmoothHerm_sqMetric dh
  have hGs := isSmoothHerm_tensor hA hHs
  have secH : IsSectionOn (mCoordIdeal y) (HermLine.sqMetric (ι := ι) dh) h :=
    ⟨dh, fun _ => rfl, hh, hhP⟩
  have secG : IsSectionOn (mCoordIdeal y) (A.tensor (HermLine.sqMetric (ι := ι) dh)) g := by
    refine ⟨dg, fun k => ?_, hg, hgP⟩
    have : (A.tensor (HermLine.sqMetric (ι := ι) dh)).a k = A.a k + dh k := rfl
    rw [this, hd k]
    ring
  have cutG := RootFieldNumerics.points_integral_section_snoc II hII hD K ι (mCoordIdeal y) e L _ g hP hL hGs secG
  have cutH := RootFieldNumerics.points_integral_section_snoc II hII hD K ι (mCoordIdeal y) e L _ h hP hL hHs secH
  have hadd := deg_tensor II hII (mCoordIdeal y) e L A _ hP hL hA hHs
  have hfin : ∀ f : MRing ι, ({W | W ∈ divSupp (mCoordIdeal y) f ∧ IsHorizontal W}).Finite :=
    fun f => (divSupp_finite _ f).subset fun W hW => hW.1
  have hInn : ∀ W, W ∈ divSupp (mCoordIdeal y) g → IsHorizontal W →
      0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) := fun W hW hh' =>
    hnef W ((hD K ι _ (e + 1) _ g W hP secG hW).1 hh') (le_sup_left.trans hW.1.1.2)
  have hkey : ∀ W, W ∈ divSupp (mCoordIdeal y) h → IsHorizontal W →
      W ∈ divSupp (mCoordIdeal y) g ∧
        multAt (mCoordIdeal y ⊔ Ideal.span {h}) W ≤ multAt (mCoordIdeal y ⊔ Ideal.span {g}) W := by
    intro W hW _
    obtain ⟨hWmin, hWrel⟩ := hW
    have hrel' := hWrel
    choose c hcW using hWrel
    have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hWmin.1.2
    have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => y_ne_of_not_mem fun h' => hcW k (hPW h')
    have hsc : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * A.a k)) ∈ chartRingZ y c := hs c hyc
    obtain ⟨u, r, hrel⟩ := chart_rel hyc hsc hg hh hd e1
    haveI hWp : W.IsPrime := hWmin.1.1
    obtain ⟨hm, hle⟩ := len_le_of_rel hgP (mon_not_mem hWp hcW u) hrel hWmin
    refine ⟨⟨hm, hrel'⟩, ?_⟩
    unfold multAt
    rw [dif_pos hWp, dif_pos hWp]
    exact hle
  have cmp : (∑ᶠ (W) (_ : W ∈ divSupp (mCoordIdeal y) h ∧ IsHorizontal W),
        (multAt (mCoordIdeal y ⊔ Ideal.span {h}) W : ℝ) *
          ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1)) ≤
      ∑ᶠ (W) (_ : W ∈ divSupp (mCoordIdeal y) g ∧ IsHorizontal W),
        (multAt (mCoordIdeal y ⊔ Ideal.span {g}) W : ℝ) *
          ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
    change (∑ᶠ W ∈ {W | W ∈ divSupp (mCoordIdeal y) h ∧ IsHorizontal W}, _) ≤
      ∑ᶠ W ∈ {W | W ∈ divSupp (mCoordIdeal y) g ∧ IsHorizontal W}, _
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin h), finsum_mem_eq_finite_toFinset_sum _ (hfin g)]
    refine (Finset.sum_le_sum fun W hW => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (fun W hW => ?_) fun W hW _ => ?_)
    · rw [Set.Finite.mem_toFinset] at hW
      have h2 := hkey W hW.1 hW.2
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 h2.2) (hInn W h2.1 hW.2)
    · rw [Set.Finite.mem_toFinset] at hW ⊢
      exact ⟨(hkey W hW.1 hW.2).1, hW.2⟩
    · rw [Set.Finite.mem_toFinset] at hW
      exact mul_nonneg (Nat.cast_nonneg _) (hInn W hW.1 hW.2)
  rw [cutG, cutH] at hadd
  linarith
