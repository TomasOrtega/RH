import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitSectionDivisorEq
import GroundTheory.HeightsAndTheta.Heights.Intersections.PGeoNumCut

open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.TiePrimes

namespace LevelTowerAlt

namespace N1

section

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `h` using `homog_add ha (homog_mul (homog_C (J := J) (-1)) hb |> fun h => (zero_add d) ▸ h)`. Establish `e : a + C (-1) * b = a - b` using `by simp [sub_eq_add_neg]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem homog_sub {a b : MRing J} {d : K → ℕ} (ha : IsMultiHomog a d) (hb : IsMultiHomog b d) :
    IsMultiHomog (a - b) d := by
  have h := homog_add ha (homog_mul (homog_C (J := J) (-1)) hb |> fun h => (zero_add d) ▸ h)
  have e : a + C (-1) * b = a - b := by simp [sub_eq_add_neg]
  rwa [e] at h

/- English proof (translation)
Introduce `h`. Take `⟨k, -, hk⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := hW)).1 h`. Conclude with `hc k (hW.mem_of_pow_mem _ hk)`.
-/
theorem cMon_notMem {W : Ideal (MRing J)} (hW : W.IsPrime) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    (d : K → ℕ) : cMon c d ∉ W := by
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hW)).1 h
  exact hc k (hW.mem_of_pow_mem _ hk)

/- English proof (translation)
Simplify using `[cMon]`.
-/
theorem aeval_cMon (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (d : K → ℕ) :
    aeval y (cMon c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [cMon]

/- English proof (translation)
Take `⟨f, hf⟩` from `h1`. Take `⟨f', hf'⟩` from `h2`. Take `⟨D, g, hg, e⟩` from `exists_form_dh hc f`. Take `⟨D', g', hg', e'⟩` from `exists_form_dh hc f'`. Use `replace e : dh y c g = lam * ∏ k, y ⟨k, c k⟩ ^ (-b k) := e.trans hf`.

Use `replace e' : dh y c g' = (lam * ∏ k, y ⟨k, c k⟩ ^ (-b k))⁻¹ := e'.trans hf'`. Establish `hw : lam * ∏ k, y ⟨k, c k⟩ ^ (-b k) ≠ 0` using `mul_ne_zero hl (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k))`. Use `⟨g * cMon c (fun k => (b k).toNat), cMon c (D + fun k => (-b k).toNat), D + fun k => (b k).toNat, _, homog_mul hg (homog_cMon _ _), homog_cMon _ _, fun k => ?_, ?_, fun W hW hP hX => ⟨fun h => ?_, cMon_notMem hW hX _⟩⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[map_mul, aeval_eq_dh_mul y c hc hg, e, aeval_cMon, aeval_cMon, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k), ← zpow_add₀ (hc k)]`.

Use `congr 1`. Simplify using `only [Pi.add_apply]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Establish `hgW : g ∈ W` using `(hW.mem_or_mem h).resolve_right (cMon_notMem hW hX _)`.

Establish `hm : g * g' - cMon c (D + D') ∈ mCoordIdeal y`. Rewrite using `[mem_coord_iff y (homog_sub (homog_mul hg hg') (homog_cMon _ _)), map_sub, map_mul, aeval_eq_dh_mul y c hc hg, aeval_eq_dh_mul y c hc hg', e, e', aeval_cMon, mul_mul_mul_comm, mul_inv_cancel₀ hw, one_mul, ← Finset.prod_mul_distrib]`. Simplify using `[pow_add]`. Use `cMon_notMem hW hX (D + D') ?_` and prove the remaining obligations. Establish `: cMon c (D + D') = g * g' - (g * g' - cMon c (D + D'))` using `by ring`.

Rewrite using `[this]`. Conclude with `W.sub_mem (W.mul_mem_right _ hgW) (hP hm)`.
-/
theorem exists_rep (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (lam : Ω) (hl : lam ≠ 0) (b : K → ℤ)
    (h1 : lam * ∏ k, y ⟨k, c k⟩ ^ (-b k) ∈ (dh y c).range) (h2 : (lam * ∏ k, y ⟨k, c k⟩ ^ (-b k))⁻¹ ∈ (dh y c).range) :
    ∃ (F G : MRing J) (dF dG : K → ℕ), IsMultiHomog F dF ∧ IsMultiHomog G dG ∧ (∀ k, (dF k : ℤ) = dG k + b k) ∧
      aeval y F = lam * aeval y G ∧
      ∀ W : Ideal (MRing J), W.IsPrime → mCoordIdeal y ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) → F ∉ W ∧ G ∉ W := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨f', hf'⟩ := h2
  obtain ⟨D, g, hg, e⟩ := exists_form_dh hc f
  obtain ⟨D', g', hg', e'⟩ := exists_form_dh hc f'
  replace e : dh y c g = lam * ∏ k, y ⟨k, c k⟩ ^ (-b k) := e.trans hf
  replace e' : dh y c g' = (lam * ∏ k, y ⟨k, c k⟩ ^ (-b k))⁻¹ := e'.trans hf'
  have hw : lam * ∏ k, y ⟨k, c k⟩ ^ (-b k) ≠ 0 :=
    mul_ne_zero hl (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k))
  refine ⟨g * cMon c (fun k => (b k).toNat), cMon c (D + fun k => (-b k).toNat), D + fun k => (b k).toNat, _,
    homog_mul hg (homog_cMon _ _), homog_cMon _ _, fun k => ?_, ?_, fun W hW hP hX => ⟨fun h => ?_, cMon_notMem hW hX _⟩⟩
  · simp only [Pi.add_apply]; push_cast; omega
  · rw [map_mul, aeval_eq_dh_mul y c hc hg, e, aeval_cMon, aeval_cMon, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k), ← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]; push_cast; omega
  · have hgW : g ∈ W := (hW.mem_or_mem h).resolve_right (cMon_notMem hW hX _)
    have hm : g * g' - cMon c (D + D') ∈ mCoordIdeal y := by
      rw [mem_coord_iff y (homog_sub (homog_mul hg hg') (homog_cMon _ _)), map_sub, map_mul,
        aeval_eq_dh_mul y c hc hg, aeval_eq_dh_mul y c hc hg', e, e', aeval_cMon, mul_mul_mul_comm,
        mul_inv_cancel₀ hw, one_mul, ← Finset.prod_mul_distrib]
      simp [pow_add]
    refine cMon_notMem hW hX (D + D') ?_
    have : cMon c (D + D') = g * g' - (g * g' - cMon c (D + D')) := by ring
    rw [this]
    exact W.sub_mem (W.mul_mem_right _ hgW) (hP hm)

/- English proof (translation)
Simplify using `only [geoNum]`. Use `split_ifs with h`. Simplify using `only [Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Simplify using the standard rewrite rules.
-/
theorem geoNum_one_add (W : Ideal (MRing J)) (a b : K → ℤ) :
    geoNum 1 W (fun _ => a + b) = geoNum 1 W (fun _ => a) + geoNum 1 W (fun _ => b) := by
  simp only [geoNum]
  split_ifs with h
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  · simp

/- English proof (translation)
Establish `rep : ∀ U : Ideal (MRing J), U.IsPrime → mCoordIdeal y ≤ U → IsRelevant U → ∃ (F G : MRing J) (dF dG : K → ℕ), IsMultiHomog F dF ∧ IsMultiHomog G dG ∧ (∀ k, (dF k : ℤ) = dG k + b k) ∧ aeval y F = lam * aeval y G ∧ F ∉ U ∧ G ∉ U`. Introduce `U hU hPU hr`. Use `choose c hc using hr`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k h0 => hc k (hPU ((mem_coord_iff y (homog_X ⟨k, c k⟩)).2 (by simpa using h0)))`. Take `⟨F, G, dF, dG, h1, h2, h3, h4, h5⟩` from `exists_rep y c hy lam hl b (h c hy).1 (h c hy).2`.

Conclude with `⟨F, G, dF, dG, h1, h2, h3, h4, h5 U hU hPU hc⟩`. Take `⟨F, G, dF, dG, hF, hG, hd, hFG, hFW, hGW⟩` from `rep W hW.1 hP hW.2.2`. Establish `hu : Flat.IsUnitSec W F G`. Introduce `U hU hWU hr`. Take `⟨F', G', dF', dG', hF', hG', hd', hFG', hFU, hGU⟩` from `rep U hU (hP.trans hWU) hr`.

Use `⟨G', F', hGU, hFU, hP ?_⟩` and prove the remaining obligations. Establish `e : dF' + dG = dG' + dF` using `funext fun k => by`. Use `hd k` as an intermediate fact. Use `hd' k` as an intermediate fact. Simplify using `only [Pi.add_apply]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[mem_coord_iff y (homog_sub (homog_mul hG' hF) (e ▸ homog_mul hF' hG)), map_sub, map_mul, map_mul, hFG, hFG']`. Expand and normalize the polynomial expressions, which then agree. Take `⟨hs, hm, -⟩` from `Flat.cycles_eq_of_isUnitSec K J W F G hu`. Establish `hp` using `PB.prime_charOf_of_ne_zero hW.1 hch`.

Establish `hD : ∀ (d : K → ℕ) (s : MRing J), IsMultiHomog s d → s ∉ W → geoNum 1 W (fun _ => fun k => (d k : ℤ)) = ∑ᶠ U ∈ divSupp W s, (multAt (W ⊔ Ideal.span {s}) U : ℤ) * geoNum 0 U (Fin.elim0 : Fin 0 → K → ℤ)`. Introduce `d s hs hsW`. Establish `hcut` using `GroundTheory.Heights₂.Heights.Inter.GeoNumCut.full K J W 0 Fin.elim0 d s hW hp (by rw [hdim]) hs hsW`. Establish `hsn : (Fin.snoc (Fin.elim0 : Fin 0 → K → ℤ) (fun k => (d k : ℤ)) : Fin 1 → K → ℤ) = fun _ => fun k => (d k : ℤ)`. Use function extensionality and compare the values at `i`.

Rewrite using `[Fin.fin_one_eq_zero i]`. Simplify using `[Fin.snoc]`. Rewrite `hcut` using `[hsn]`. Then use the resulting hypothesis. Establish `e1 : geoNum 1 W (fun _ => fun k => (dF k : ℤ)) = geoNum 1 W (fun _ => fun k => (dG k : ℤ))`. Rewrite using `[hD dF F hF hFW, hD dG G hG hGW, ← hs]`.

Conclude with `finsum_mem_congr rfl fun U hU => by rw [hm U hU]`. Establish `e2 : (fun k => (dF k : ℤ)) = (fun k => (dG k : ℤ)) + b` using `funext hd`. Rewrite `e1` using `[e2, geoNum_one_add]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem geoNum_eq_zero (y : (Σ k, J k) → Ω) (lam : Ω) (hl : lam ≠ 0) (b : K → ℤ)
    (h : ∀ c : ∀ k, J k, (∀ k, y ⟨k, c k⟩ ≠ 0) → lam * ∏ k, y ⟨k, c k⟩ ^ (-b k) ∈ (dh y c).range ∧
      (lam * ∏ k, y ⟨k, c k⟩ ^ (-b k))⁻¹ ∈ (dh y c).range)
    (W : Ideal (MRing J)) (hW : IsMultiProjPrime W) (hP : mCoordIdeal y ≤ W) (hch : charOf W ≠ 0)
    (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    geoNum 1 W (fun _ => b) = 0 := by
  classical
  have rep : ∀ U : Ideal (MRing J), U.IsPrime → mCoordIdeal y ≤ U → IsRelevant U →
      ∃ (F G : MRing J) (dF dG : K → ℕ), IsMultiHomog F dF ∧ IsMultiHomog G dG ∧ (∀ k, (dF k : ℤ) = dG k + b k) ∧
      aeval y F = lam * aeval y G ∧ F ∉ U ∧ G ∉ U := by
    intro U hU hPU hr
    choose c hc using hr
    have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (hPU ((mem_coord_iff y (homog_X ⟨k, c k⟩)).2 (by simpa using h0)))
    obtain ⟨F, G, dF, dG, h1, h2, h3, h4, h5⟩ := exists_rep y c hy lam hl b (h c hy).1 (h c hy).2
    exact ⟨F, G, dF, dG, h1, h2, h3, h4, h5 U hU hPU hc⟩
  obtain ⟨F, G, dF, dG, hF, hG, hd, hFG, hFW, hGW⟩ := rep W hW.1 hP hW.2.2
  have hu : Flat.IsUnitSec W F G := by
    intro U hU hWU hr
    obtain ⟨F', G', dF', dG', hF', hG', hd', hFG', hFU, hGU⟩ := rep U hU (hP.trans hWU) hr
    refine ⟨G', F', hGU, hFU, hP ?_⟩
    have e : dF' + dG = dG' + dF := funext fun k => by
      have := hd k; have := hd' k; simp only [Pi.add_apply]; omega
    rw [mem_coord_iff y (homog_sub (homog_mul hG' hF) (e ▸ homog_mul hF' hG)), map_sub, map_mul, map_mul, hFG, hFG']
    ring
  obtain ⟨hs, hm, -⟩ := Flat.cycles_eq_of_isUnitSec K J W F G hu
  have hp := PB.prime_charOf_of_ne_zero hW.1 hch
  have hD : ∀ (d : K → ℕ) (s : MRing J), IsMultiHomog s d → s ∉ W →
      geoNum 1 W (fun _ => fun k => (d k : ℤ)) =
        ∑ᶠ U ∈ divSupp W s, (multAt (W ⊔ Ideal.span {s}) U : ℤ) * geoNum 0 U (Fin.elim0 : Fin 0 → K → ℤ) := by
    intro d s hs hsW
    have hcut := GroundTheory.Heights₂.Heights.Inter.GeoNumCut.full K J W 0 Fin.elim0 d s hW hp (by rw [hdim]) hs hsW
    have hsn : (Fin.snoc (Fin.elim0 : Fin 0 → K → ℤ) (fun k => (d k : ℤ)) : Fin 1 → K → ℤ) =
        fun _ => fun k => (d k : ℤ) := by
      funext i
      rw [Fin.fin_one_eq_zero i]
      simp [Fin.snoc]
    rwa [hsn] at hcut
  have e1 : geoNum 1 W (fun _ => fun k => (dF k : ℤ)) = geoNum 1 W (fun _ => fun k => (dG k : ℤ)) := by
    rw [hD dF F hF hFW, hD dG G hG hGW, ← hs]
    exact finsum_mem_congr rfl fun U hU => by rw [hm U hU]
  have e2 : (fun k => (dF k : ℤ)) = (fun k => (dG k : ℤ)) + b := funext hd
  rw [e2, geoNum_one_add] at e1
  linarith

end

end N1

open N1

/- English proof (translation)
Introduce `_ X Ω _ _ K _ J _ y ξ L a a' e e' u tie hu h h' hnef W hW hP hch hdim`. Establish `hl : u * e / e' ≠ 0` using `div_ne_zero (mul_ne_zero hu h.1) h'.1`. Establish `h0` using `geoNum_eq_zero y (u * e / e') hl (a' - a) (fun c hc => ?_) W hW hP hch hdim`. Establish `e2 : a' = a + (a' - a)` using `by abel`. Rewrite using `[e2, geoNum_one_add, h0, add_zero]`.

Conclude with `hnef W hW hP hch hdim`. Establish `key : ∀ p : Cpt ξ, InChart ξ (seg y) c p → u * e / e' * ∏ k, y ⟨k, c k⟩ ^ (-(a' - a) k) ∈ regAt ξ p ∧ (u * e / e' * ∏ k, y ⟨k, c k⟩ ^ (-(a' - a) k))⁻¹ ∈ regAt ξ p`. Introduce `p hp`. Establish `e1` using `h.2 p trivial c hp`. Establish `e2` using `h'.2 p trivial c hp`.

Establish `e3 : Submodule.span (regAt ξ p) {u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e)} = Submodule.span (regAt ξ p) {(∏ k, y ⟨k, c k⟩ ^ a' k) * e'}`. Rewrite using `[← smul_eq_mul (∏ k, y ⟨k, c k⟩ ^ a' k), ← e2, Lat.scale, Lat.map, e1, Submodule.map_span, Set.image_singleton]`. Both sides reduce to the same expression. Establish `n1 : ∏ k, y ⟨k, c k⟩ ^ a k ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)`. Establish `n2 : ∏ k, y ⟨k, c k⟩ ^ a' k ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)`.

Establish `e4 : ∏ k, y ⟨k, c k⟩ ^ (-(a' - a) k) = (∏ k, y ⟨k, c k⟩ ^ a k) / ∏ k, y ⟨k, c k⟩ ^ a' k`. Rewrite using `[← Finset.prod_div_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [← zpow_sub₀ (hc k)]; simp`. Establish `he` using `h.1`. Establish `he'` using `h'.1`.

Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.1 (e3 ▸ Submodule.mem_span_singleton_self _ : u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e) ∈ Submodule.span (regAt ξ p) {(∏ k, y ⟨k, c k⟩ ^ a' k) * e'})`. Take `⟨r', hr'⟩` from `Submodule.mem_span_singleton.1 (e3.symm ▸ Submodule.mem_span_singleton_self _ : (∏ k, y ⟨k, c k⟩ ^ a' k) * e' ∈ Submodule.span (regAt ξ p) {u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e)})`. Use `replace hr : (r : Ω) * ((∏ k, y ⟨k, c k⟩ ^ a' k) * e') = u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e) := hr`. Use `replace hr' : (r' : Ω) * (u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) = (∏ k, y ⟨k, c k⟩ ^ a' k) * e' := hr'`. Rewrite using `[e4]`.

Prove the components needed by the constructor for the conclusion. Use `r.2 using 1` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts. Take the linear combination `-hr`. Use `r'.2 using 1` and compare the differences between its conclusion and the goal.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-hr'`. Rewrite using `[← adjoin_eq hc]`. Conclude with `⟨(tie.ring c (seg_ne hc) _).2 fun p hp => (key p hp).1, (tie.ring c (seg_ne hc) _).2 fun p hp => (key p hp).2⟩`.
-/
theorem nef_fibres_scaled_lattice : PB.Inputs → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (L : Lat ξ Ω) (a a' : K → ℤ) (e e' u : Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → u ≠ 0 → L.IsDegOn Set.univ y a e → (L.scale u).IsDegOn Set.univ y a' e' → NefOnFibres (mCoordIdeal y) a → NefOnFibres (mCoordIdeal y) a' := by
  intro _ X Ω _ _ K _ J _ y ξ L a a' e e' u tie hu h h' hnef W hW hP hch hdim
  have hl : u * e / e' ≠ 0 := div_ne_zero (mul_ne_zero hu h.1) h'.1
  have h0 := geoNum_eq_zero y (u * e / e') hl (a' - a) (fun c hc => ?_) W hW hP hch hdim
  · have e2 : a' = a + (a' - a) := by abel
    rw [e2, geoNum_one_add, h0, add_zero]
    exact hnef W hW hP hch hdim
  have key : ∀ p : Cpt ξ, InChart ξ (seg y) c p →
      u * e / e' * ∏ k, y ⟨k, c k⟩ ^ (-(a' - a) k) ∈ regAt ξ p ∧
        (u * e / e' * ∏ k, y ⟨k, c k⟩ ^ (-(a' - a) k))⁻¹ ∈ regAt ξ p := by
    intro p hp
    have e1 := h.2 p trivial c hp
    have e2 := h'.2 p trivial c hp
    have e3 : Submodule.span (regAt ξ p) {u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e)} =
        Submodule.span (regAt ξ p) {(∏ k, y ⟨k, c k⟩ ^ a' k) * e'} := by
      rw [← smul_eq_mul (∏ k, y ⟨k, c k⟩ ^ a' k), ← e2, Lat.scale, Lat.map, e1, Submodule.map_span, Set.image_singleton]
      rfl
    have n1 : ∏ k, y ⟨k, c k⟩ ^ a k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)
    have n2 : ∏ k, y ⟨k, c k⟩ ^ a' k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)
    have e4 : ∏ k, y ⟨k, c k⟩ ^ (-(a' - a) k) = (∏ k, y ⟨k, c k⟩ ^ a k) / ∏ k, y ⟨k, c k⟩ ^ a' k := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [← zpow_sub₀ (hc k)]; simp
    have he := h.1
    have he' := h'.1
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (e3 ▸ Submodule.mem_span_singleton_self _ :
      u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e) ∈ Submodule.span (regAt ξ p) {(∏ k, y ⟨k, c k⟩ ^ a' k) * e'})
    obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.1 (e3.symm ▸ Submodule.mem_span_singleton_self _ :
      (∏ k, y ⟨k, c k⟩ ^ a' k) * e' ∈ Submodule.span (regAt ξ p) {u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e)})
    replace hr : (r : Ω) * ((∏ k, y ⟨k, c k⟩ ^ a' k) * e') = u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e) := hr
    replace hr' : (r' : Ω) * (u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) = (∏ k, y ⟨k, c k⟩ ^ a' k) * e' := hr'
    rw [e4]
    constructor
    · convert r.2 using 1
      field_simp
      linear_combination -hr
    · convert r'.2 using 1
      field_simp
      linear_combination -hr'
  rw [← adjoin_eq hc]
  exact ⟨(tie.ring c (seg_ne hc) _).2 fun p hp => (key p hp).1, (tie.ring c (seg_ne hc) _).2 fun p hp => (key p hp).2⟩

end LevelTowerAlt
