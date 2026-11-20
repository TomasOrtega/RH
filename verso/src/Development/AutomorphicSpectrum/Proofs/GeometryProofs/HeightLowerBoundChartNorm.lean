import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.SecLow

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp
  GlobalTheory.CompanionTheory.Ar.Ht GlobalTheory.CompanionTheory.Ar.Flat.UnitChart GlobalTheory.CompanionTheory.Ar.Flat.CptIn.Intr

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Set `φw : MRing ι →+* L` to `(aeval (fun p : Σ k, ι k => w p / w ⟨p.1, c p.1⟩) : MRing ι →ₐ[ℤ] L).toRingHom`. Establish `hker : RingHom.ker (ratMap y c).toRingHom ≤ RingHom.ker φw`. Introduce `g hg`. Take `⟨m, G, hG, e⟩` from `exists_form c g`. Establish `hy0 : aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g = 0`.

Rewrite using `[← ratMap_coe]`. Establish `: ratMap y c g = 0` using `hg`. Simplify using `[this]`. Establish `hG0 : aeval y G = 0` using `by rw [← e Ω y hc, hy0, zero_mul]`. Establish `hmem : G ∈ mCoordIdeal y` using `mem_of_aeval_eq_zero hG hG0`.

Establish `hwG : aeval w G = 0` using `hw.2 G hmem`. Establish `hprod : ∏ k, w ⟨k, c k⟩ ^ m k ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hwc k)`. Rewrite `hwG` using `[← e L w hwc]`. Conclude with `(mul_eq_zero.1 hwG).resolve_right hprod`. Use `⟨(ratMap y c).toRingHom.liftOfSurjective (ratMap_surjective y c) ⟨φw, hker⟩, fun g => ?_⟩` and prove the remaining obligations.

Conclude with `RingHom.liftOfRightInverse_comp_apply _ _ _ _ g`.
-/
theorem exists_chart_eval {L : Type} [Field L] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (w : (Σ k, ι k) → L) (hw : w ∈ ptsOver L (mCoordIdeal y))
    (hwc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    ∃ e : chartRingZ y c →+* L, ∀ g : MRing ι,
      e (ratMap y c g) = aeval (fun p : Σ k, ι k => w p / w ⟨p.1, c p.1⟩) g := by
  let φw : MRing ι →+* L :=
    (aeval (fun p : Σ k, ι k => w p / w ⟨p.1, c p.1⟩) : MRing ι →ₐ[ℤ] L).toRingHom
  have hker : RingHom.ker (ratMap y c).toRingHom ≤ RingHom.ker φw := by
    intro g hg
    obtain ⟨m, G, hG, e⟩ := exists_form c g
    have hy0 : aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g = 0 := by
      rw [← ratMap_coe]
      have : ratMap y c g = 0 := hg
      simp [this]
    have hG0 : aeval y G = 0 := by rw [← e Ω y hc, hy0, zero_mul]
    have hmem : G ∈ mCoordIdeal y := mem_of_aeval_eq_zero hG hG0
    have hwG : aeval w G = 0 := hw.2 G hmem
    have hprod : ∏ k, w ⟨k, c k⟩ ^ m k ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hwc k)
    rw [← e L w hwc] at hwG
    exact (mul_eq_zero.1 hwG).resolve_right hprod
  refine ⟨(ratMap y c).toRingHom.liftOfSurjective (ratMap_surjective y c) ⟨φw, hker⟩, fun g => ?_⟩
  exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ g

/- English proof (translation)
Simplify `aeval_scaled_homog v (fun k => (v ⟨k, c k⟩)⁻¹) hG` using `only [div_eq_mul_inv]`.
-/
theorem aeval_ratio {F : Type} [Field F] (v : (Σ k, ι k) → F) (c : ∀ k, ι k) {G : MRing ι} {d : K → ℕ}
    (hG : IsMultiHomog G d) :
    aeval (fun p : Σ k, ι k => v p / v ⟨p.1, c p.1⟩) G = aeval v G * ∏ k, (v ⟨k, c k⟩)⁻¹ ^ d k := by
  simpa only [div_eq_mul_inv] using aeval_scaled_homog v (fun k => (v ⟨k, c k⟩)⁻¹) hG

/- English proof (translation)
Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[inv_pow, inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_neg, ← zpow_add₀ (hx k), hd k]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_inv_pow {F : Type} [Field F] (x : K → F) (hx : ∀ k, x k ≠ 0) (dg dh : K → ℕ) (b : K → ℤ)
    (hd : ∀ k, (dg k : ℤ) = dh k + b k) :
    (∏ k, (x k)⁻¹ ^ dh k) * ∏ k, x k ^ (-(b k)) = ∏ k, (x k)⁻¹ ^ dg k := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [inv_pow, inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_neg, ← zpow_add₀ (hx k), hd k]
  congr 1
  ring

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C n => simpa using intCast_mem O n`. Consider the case `add a b ha hb => simpa using add_mem ha hb`. Consider the case `mul_X a p ha => simpa using mul_mem ha (hx p)`.
-/
theorem aeval_mem_of_ratio {L : Type} [Field L] (O : ValuationSubring L) (x : (Σ k, ι k) → L)
    (hx : ∀ p, x p ∈ O) (g : MRing ι) : aeval x g ∈ O := by
  induction g using MvPolynomial.induction_on with
  | C n => simpa using intCast_mem O n
  | add a b ha hb => simpa using add_mem ha hb
  | mul_X a p ha => simpa using mul_mem ha (hx p)

/- English proof (translation)
Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Introduce `k h0`. Establish `hmem : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y` using `mem_of_aeval_eq_zero (homog_X (ι := ι) ⟨k, c k⟩) (by simpa using h0)`. Use `hz.2 _ hmem` as an intermediate fact. Conclude with `hzc k (by simpa using this)`.

Take `⟨dg, dh, g, h, hg, hh, hd, hgh, hzh, hzg⟩` from `hv`. Establish `hyh : aeval y h ≠ 0` using `fun h0 => hzh (hz.2 h (mem_of_aeval_eq_zero hh h0))`. Take `⟨e, he⟩` from `exists_chart_eval y c hyc z hz hzc`. Use `set t : Ω := s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) with ht`. Establish `hint : IsIntegral (chartRingZ y c) t` using `hs c hyc`.

Take `⟨P, hPm, hP⟩` from `hint`. Use `set T : L := v * ∏ k, z ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) with hT`. Use `set hh' : chartRingZ y c := ratMap y c h with hhh`. Use `set gg : chartRingZ y c := ratMap y c g with hgg`. Establish `key : algebraMap (chartRingZ y c) Ω hh' * t = algebraMap (chartRingZ y c) Ω gg`.

Express the relevant statement in the definitionally equal form `(hh' : Ω) * t = (gg : Ω)`. Rewrite using `[hhh, hgg, ratMap_coe, ratMap_coe, aeval_ratio y c hh, aeval_ratio y c hg, hgh, ht, ← prod_inv_pow (fun k => y ⟨k, c k⟩) hyc dg dh (fun k => (τ : ℤ) * a k) hd]`. Expand and normalize the polynomial expressions, which then agree. Establish `heh : e hh' = aeval z h * ∏ k, (z ⟨k, c k⟩)⁻¹ ^ dh k`. Rewrite using `[hhh, he, aeval_ratio z c hh]`.

Establish `heg : e gg = aeval z g * ∏ k, (z ⟨k, c k⟩)⁻¹ ^ dg k`. Rewrite using `[hgg, he, aeval_ratio z c hg]`. Establish `hehne : e hh' ≠ 0`. Rewrite using `[heh]`. Conclude with `mul_ne_zero hzh (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (hzc k)))`.

Establish `keyT : e hh' * T = e gg`. Rewrite using `[heh, heg, hzg, hT, ← prod_inv_pow (fun k => z ⟨k, c k⟩) hzc dg dh (fun k => (τ : ℤ) * a k) hd]`. Expand and normalize the polynomial expressions, which then agree. Establish `hQ : Polynomial.eval gg (Polynomial.scaleRoots P hh') = 0`. Establish `h1` using `Polynomial.scaleRoots_eval₂_mul (algebraMap (chartRingZ y c) Ω) t hh' (p := P)`.

Rewrite `h1` using `[key, Polynomial.eval₂_at_apply]`. Establish `h2 : Polynomial.eval₂ (algebraMap (chartRingZ y c) Ω) t P = 0` using `hP`. Rewrite `h1` using `[h2, mul_zero]`. Conclude with `Subtype.ext (by simpa using h1)`. Establish `hPT : Polynomial.eval₂ e T P = 0`.

Establish `h1` using `Polynomial.scaleRoots_eval₂_mul e T hh' (p := P)`. Rewrite `h1` using `[keyT, Polynomial.eval₂_at_apply, hQ, map_zero]`. Conclude with `(mul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ hehne)`. Establish `hrange : ∀ r, e r ∈ O`. Introduce `r`.

Take `⟨g', rfl⟩` from `ratMap_surjective y c r`. Rewrite using `[he]`. Conclude with `aeval_mem_of_ratio O _ hO g'`. Set `e' : chartRingZ y c →+* O` to `e.codRestrict O hrange`. Establish `hTint : IsIntegral O T`.

Use `⟨P.map e', hPm.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`. Conclude with `hPT`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hTint`. Rewrite using `[← hr]`.

Conclude with `r.2`.
-/
theorem value_mem {L : Type} [Field L] (O : ValuationSubring L) (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (s : Ω)
    (hs : s ∈ chartLatNm y a τ) (z : (Σ k, ι k) → L) (hz : z ∈ ptsOver L (mCoordIdeal y)) (c : ∀ k, ι k)
    (hzc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hO : ∀ p : Σ k, ι k, z p / z ⟨p.1, c p.1⟩ ∈ O) {v : L}
    (hv : HasVal y (fun k => (τ : ℤ) * a k) s z v) :
    v * ∏ k, z ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ O := by
  classical
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    have hmem : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y :=
      mem_of_aeval_eq_zero (homog_X (ι := ι) ⟨k, c k⟩) (by simpa using h0)
    have := hz.2 _ hmem
    exact hzc k (by simpa using this)
  obtain ⟨dg, dh, g, h, hg, hh, hd, hgh, hzh, hzg⟩ := hv
  have hyh : aeval y h ≠ 0 := fun h0 => hzh (hz.2 h (mem_of_aeval_eq_zero hh h0))
  obtain ⟨e, he⟩ := exists_chart_eval y c hyc z hz hzc
  set t : Ω := s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) with ht
  have hint : IsIntegral (chartRingZ y c) t := hs c hyc
  obtain ⟨P, hPm, hP⟩ := hint
  set T : L := v * ∏ k, z ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) with hT
  set hh' : chartRingZ y c := ratMap y c h with hhh
  set gg : chartRingZ y c := ratMap y c g with hgg
  have key : algebraMap (chartRingZ y c) Ω hh' * t = algebraMap (chartRingZ y c) Ω gg := by
    change (hh' : Ω) * t = (gg : Ω)
    rw [hhh, hgg, ratMap_coe, ratMap_coe, aeval_ratio y c hh, aeval_ratio y c hg, hgh, ht,
      ← prod_inv_pow (fun k => y ⟨k, c k⟩) hyc dg dh (fun k => (τ : ℤ) * a k) hd]
    ring
  have heh : e hh' = aeval z h * ∏ k, (z ⟨k, c k⟩)⁻¹ ^ dh k := by
    rw [hhh, he, aeval_ratio z c hh]
  have heg : e gg = aeval z g * ∏ k, (z ⟨k, c k⟩)⁻¹ ^ dg k := by
    rw [hgg, he, aeval_ratio z c hg]
  have hehne : e hh' ≠ 0 := by
    rw [heh]
    exact mul_ne_zero hzh (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (hzc k)))
  have keyT : e hh' * T = e gg := by
    rw [heh, heg, hzg, hT, ← prod_inv_pow (fun k => z ⟨k, c k⟩) hzc dg dh (fun k => (τ : ℤ) * a k) hd]
    ring
  have hQ : Polynomial.eval gg (Polynomial.scaleRoots P hh') = 0 := by
    have h1 := Polynomial.scaleRoots_eval₂_mul (algebraMap (chartRingZ y c) Ω) t hh' (p := P)
    rw [key, Polynomial.eval₂_at_apply] at h1
    have h2 : Polynomial.eval₂ (algebraMap (chartRingZ y c) Ω) t P = 0 := hP
    rw [h2, mul_zero] at h1
    exact Subtype.ext (by simpa using h1)
  have hPT : Polynomial.eval₂ e T P = 0 := by
    have h1 := Polynomial.scaleRoots_eval₂_mul e T hh' (p := P)
    rw [keyT, Polynomial.eval₂_at_apply, hQ, map_zero] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ hehne)
  have hrange : ∀ r, e r ∈ O := by
    intro r
    obtain ⟨g', rfl⟩ := ratMap_surjective y c r
    rw [he]
    exact aeval_mem_of_ratio O _ hO g'
  let e' : chartRingZ y c →+* O := e.codRestrict O hrange
  have hTint : IsIntegral O T := by
    refine ⟨P.map e', hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hPT
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hTint
  rw [← hr]
  exact r.2

variable {L : Type} [Field L] [NumberField L]

def placeRing (v : FinitePlace L) : ValuationSubring L where
  carrier := {x | v x ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_mul] at *
    exact mul_le_one₀ ha (apply_nonneg v b) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    exact (FinitePlace.add_le v a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at *
    have : v (-a) = v a := v.1.map_neg a
    rwa [this]
  mem_or_inv_mem' := fun x => by
    change v x ≤ 1 ∨ v x⁻¹ ≤ 1
    rw [map_inv₀]
    rcases le_total (v x) 1 with h | h
    · exact Or.inl h
    · exact Or.inr (inv_le_one_of_one_le₀ h)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_placeRing (v : FinitePlace L) (x : L) : x ∈ placeRing v ↔ v x ≤ 1 := Iff.rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using (homog_zero_deg_one (K := K) (ι := ι))`. Consider the case `succ n ih`. Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `homog_mul ih hg`.
-/
theorem homog_pow' {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (n : ℕ) :
    IsMultiHomog (g ^ n) (n • d) := by
  induction n with
  | zero => simpa using (homog_zero_deg_one (K := K) (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact homog_mul ih hg

/- English proof (translation)
Take `⟨dg, dh, g, h, hg, hh, hd, hgh, hzh, hzg⟩` from `hv`. Use `⟨0 + q • dg, q • dh, C (m : ℤ) * g ^ q, h ^ q, homog_mul (homog_C _) (homog_pow' hg q), homog_pow' hh q, fun k => ?_, ?_, (by rw [map_pow]; exact pow_ne_zero _ hzh), ?_⟩` and prove the remaining obligations. Simplify using `[hd k]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hgh, mul_pow]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[hzg, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasVal_mul_pow (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) (q m : ℕ) {𝕜 : Type} [Field 𝕜]
    (z : (Σ k, ι k) → 𝕜) {val : 𝕜} (hv : HasVal y a u z val) :
    HasVal y (fun k => (q : ℤ) * a k) ((m : Ω) * u ^ q) z ((m : 𝕜) * val ^ q) := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, hgh, hzh, hzg⟩ := hv
  refine ⟨0 + q • dg, q • dh, C (m : ℤ) * g ^ q, h ^ q, homog_mul (homog_C _) (homog_pow' hg q),
    homog_pow' hh q, fun k => ?_, ?_, (by rw [map_pow]; exact pow_ne_zero _ hzh), ?_⟩
  · simp [hd k]
    ring
  · simp [hgh, mul_pow]
    ring
  · simp [hzg, mul_pow]
    ring

/- English proof (translation)
Establish `hne : ∀ k, Nonempty (ι k)` using `fun k => let ⟨i, _⟩ := hw.1 k`. Use the proof step `⟨i⟩`. Establish `hmax : ∀ k, ∃ c : ι k, ∀ i, v (w ⟨k, i⟩) ≤ v (w ⟨k, c⟩)` using `fun k => by haveI := hne k`. Conclude with `Finite.exists_max fun i => v (w ⟨k, i⟩)`. Use `choose c hc using hmax`.

Establish `hzc : ∀ k, w ⟨k, c k⟩ ≠ 0`. Introduce `k h0`. Take `⟨i, hi⟩` from `hw.1 k`. Establish `h1` using `hc k i`. Rewrite `h1` using `[h0, map_zero]`.

Conclude with `absurd h1 (not_le.2 (FinitePlace.pos_iff.2 hi))`. Establish `hpos : ∀ k, 0 < v (w ⟨k, c k⟩)` using `fun k => FinitePlace.pos_iff.2 (hzc k)`. Establish `hsup : ∀ k, (⨆ i, v (w ⟨k, i⟩)) = v (w ⟨k, c k⟩)` using `fun k => by haveI := hne k`. Conclude with `le_antisymm (ciSup_le (hc k)) (le_ciSup (f := fun i => v (w ⟨k, i⟩)) (Set.finite_range _).bddAbove (c k))`. Establish `hO : ∀ p : Σ k, ι k, w p / w ⟨p.1, c p.1⟩ ∈ placeRing v`.

Introduce and unpack `⟨k, i⟩`. Rewrite using `[mem_placeRing, map_div₀]`. Conclude with `div_le_one_of_le₀ (hc k i) (hpos k).le`. Establish `hmem` using `value_mem (placeRing v) y a q _ hu w hw c hzc hO (hasVal_mul_pow y a u q m w hv)`. Rewrite `hmem` using `[mem_placeRing, map_mul, map_mul, map_pow, map_prod]`.

Establish `hm0 : (m : L) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Establish `hmp : 0 < v (m : L)` using `FinitePlace.pos_iff.2 hm0`. Establish `hvp : 0 < v val` using `FinitePlace.pos_iff.2 hval`. Establish `hprodpos : ∀ k ∈ Finset.univ, v (w ⟨k, c k⟩ ^ (-((q : ℤ) * a k))) ≠ 0` using `fun k _ => by`. Rewrite using `[map_zpow₀]`.

Conclude with `(zpow_pos (hpos k) _).ne'`. Establish `hprod : 0 < ∏ k, v (w ⟨k, c k⟩ ^ (-((q : ℤ) * a k)))` using `Finset.prod_pos fun k hk => lt_of_le_of_ne (apply_nonneg v _) (hprodpos k hk).symm`. Establish `hlog` using `Real.log_nonpos (mul_pos (mul_pos hmp (pow_pos hvp q)) hprod).le hmem`. Rewrite `hlog` using `[Real.log_mul (mul_pos hmp (pow_pos hvp q)).ne' hprod.ne', Real.log_mul hmp.ne' (pow_pos hvp q).ne', Real.log_pow, Real.log_prod hprodpos]`. Establish `hsum : ∑ k, Real.log (v (w ⟨k, c k⟩ ^ (-((q : ℤ) * a k)))) = -(q * ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)))`.

Rewrite using `[Finset.mul_sum, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_zpow₀, Real.log_zpow, hsup k]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hlog` using `[hsum]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem local_bound (v : FinitePlace L) (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) (q m : ℕ) (hm : 0 < m)
    (hu : (m : Ω) * u ^ q ∈ chartLatNm y a q) (w : (Σ k, ι k) → L) (hw : w ∈ ptsOver L (mCoordIdeal y))
    {val : L} (hval : val ≠ 0) (hv : HasVal y a u w val) :
    Real.log (v (m : L)) + q * Real.log (v val) ≤
      q * ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) := by
  have hne : ∀ k, Nonempty (ι k) := fun k => let ⟨i, _⟩ := hw.1 k; ⟨i⟩
  have hmax : ∀ k, ∃ c : ι k, ∀ i, v (w ⟨k, i⟩) ≤ v (w ⟨k, c⟩) := fun k => by
    haveI := hne k
    exact Finite.exists_max fun i => v (w ⟨k, i⟩)
  choose c hc using hmax
  have hzc : ∀ k, w ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    obtain ⟨i, hi⟩ := hw.1 k
    have h1 := hc k i
    rw [h0, map_zero] at h1
    exact absurd h1 (not_le.2 (FinitePlace.pos_iff.2 hi))
  have hpos : ∀ k, 0 < v (w ⟨k, c k⟩) := fun k => FinitePlace.pos_iff.2 (hzc k)
  have hsup : ∀ k, (⨆ i, v (w ⟨k, i⟩)) = v (w ⟨k, c k⟩) := fun k => by
    haveI := hne k
    exact le_antisymm (ciSup_le (hc k)) (le_ciSup (f := fun i => v (w ⟨k, i⟩)) (Set.finite_range _).bddAbove (c k))
  have hO : ∀ p : Σ k, ι k, w p / w ⟨p.1, c p.1⟩ ∈ placeRing v := by
    rintro ⟨k, i⟩
    rw [mem_placeRing, map_div₀]
    exact div_le_one_of_le₀ (hc k i) (hpos k).le
  have hmem := value_mem (placeRing v) y a q _ hu w hw c hzc hO (hasVal_mul_pow y a u q m w hv)
  rw [mem_placeRing, map_mul, map_mul, map_pow, map_prod] at hmem
  have hm0 : (m : L) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hmp : 0 < v (m : L) := FinitePlace.pos_iff.2 hm0
  have hvp : 0 < v val := FinitePlace.pos_iff.2 hval
  have hprodpos : ∀ k ∈ Finset.univ, v (w ⟨k, c k⟩ ^ (-((q : ℤ) * a k))) ≠ 0 := fun k _ => by
    rw [map_zpow₀]
    exact (zpow_pos (hpos k) _).ne'
  have hprod : 0 < ∏ k, v (w ⟨k, c k⟩ ^ (-((q : ℤ) * a k))) :=
    Finset.prod_pos fun k hk => lt_of_le_of_ne (apply_nonneg v _) (hprodpos k hk).symm
  have hlog := Real.log_nonpos (mul_pos (mul_pos hmp (pow_pos hvp q)) hprod).le hmem
  rw [Real.log_mul (mul_pos hmp (pow_pos hvp q)).ne' hprod.ne', Real.log_mul hmp.ne' (pow_pos hvp q).ne',
    Real.log_pow, Real.log_prod hprodpos] at hlog
  have hsum : ∑ k, Real.log (v (w ⟨k, c k⟩ ^ (-((q : ℤ) * a k)))) =
      -(q * ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zpow₀, Real.log_zpow, hsup k]
    push_cast
    ring
  rw [hsum] at hlog
  linarith

/- English proof (translation)
Establish `hS : (⋃ p : {p : Σ k, ι k // w p ≠ 0}, Function.mulSupport fun v : FinitePlace L => v (w p.1)).Finite` using `Set.finite_iUnion fun p => FinitePlace.hasFiniteMulSupport p.2`. Use `hS.subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hnot`. Establish `hone : ∀ p, w p ≠ 0 → v (w p) = 1` using `fun p hp => by`. Assume the negation of the conclusion as `h1`.

Conclude with `hnot (Set.mem_iUnion.2 ⟨⟨p, hp⟩, h1⟩)`. Use `hv (Finset.sum_eq_zero fun k _ => ?_)` and prove the remaining obligations. Take `⟨i, hi⟩` from `hw k`. Use `haveI : Nonempty (ι k) := ⟨i⟩`. Establish `h1 : (⨆ i, v (w ⟨k, i⟩)) = 1`.

Use `le_antisymm (ciSup_le fun j => ?_) ?_` and prove the remaining obligations. Distinguish the cases in `hj : w ⟨k, j⟩ = 0`. Simplify using `[hj]`. Conclude with `(hone _ hj).le`. Conclude with `(hone _ hi).ge.trans (le_ciSup (f := fun i => v (w ⟨k, i⟩)) (Set.finite_range _).bddAbove i)`.

Simplify using `[h1]`.
-/
theorem support_finite (w : (Σ k, ι k) → L) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (a : K → ℝ) :
    (Function.support fun v : FinitePlace L => ∑ k, a k * Real.log (⨆ i, v (w ⟨k, i⟩))).Finite := by
  classical
  have hS : (⋃ p : {p : Σ k, ι k // w p ≠ 0},
      Function.mulSupport fun v : FinitePlace L => v (w p.1)).Finite :=
    Set.finite_iUnion fun p => FinitePlace.hasFiniteMulSupport p.2
  refine hS.subset fun v hv => ?_
  by_contra hnot
  have hone : ∀ p, w p ≠ 0 → v (w p) = 1 := fun p hp => by
    by_contra h1
    exact hnot (Set.mem_iUnion.2 ⟨⟨p, hp⟩, h1⟩)
  refine hv (Finset.sum_eq_zero fun k _ => ?_)
  obtain ⟨i, hi⟩ := hw k
  haveI : Nonempty (ι k) := ⟨i⟩
  have h1 : (⨆ i, v (w ⟨k, i⟩)) = 1 := by
    refine le_antisymm (ciSup_le fun j => ?_) ?_
    · by_cases hj : w ⟨k, j⟩ = 0
      · simp [hj]
      · exact (hone _ hj).le
    · exact (hone _ hi).ge.trans (le_ciSup (f := fun i => v (w ⟨k, i⟩)) (Set.finite_range _).bddAbove i)
  simp [h1]

/- English proof (translation)
Establish `hmul : (Function.mulSupport fun v : FinitePlace L => v κ).Finite` using `FinitePlace.hasFiniteMulSupport hκ`. Establish `h1 : ∑ᶠ v : FinitePlace L, Real.log (v κ) = Real.log (∏ᶠ v : FinitePlace L, v κ)`. Rewrite using `[finsum_eq_sum_of_support_subset (s := hmul.toFinset), finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp), Real.log_prod (fun v _ => (FinitePlace.pos_iff.2 hκ).ne')]`. Introduce `v hv`. Simplify using `only [Set.Finite.coe_toFinset, Function.mem_mulSupport]`.

Introduce `h1`. Apply `hv` to reduce the goal to its premises. Simplify using `[h1]`. Establish `h2 : ∑ φ : L →+* ℂ, Real.log ‖φ κ‖ = Real.log |Algebra.norm ℚ κ|`. Rewrite using `[← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hκ))]`.

Use `congr 1`. Use `congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ κ)` as an intermediate fact. Rewrite `this` using `[norm_prod]`. Rewrite using `[Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) (fun φ => ‖φ κ‖) (fun φ => ‖φ κ‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]`. Rewrite using `[eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]`.

Rewrite using `[h1, h2, FinitePlace.prod_eq_inv_abs_norm hκ]`. Use `push_cast`. Rewrite using `[Real.log_inv]`.
-/
theorem product_formula (κ : L) (hκ : κ ≠ 0) :
    ∑ᶠ v : FinitePlace L, Real.log (v κ) = -∑ σ : L →+* ℂ, Real.log ‖σ κ‖ := by
  have hmul : (Function.mulSupport fun v : FinitePlace L => v κ).Finite :=
    FinitePlace.hasFiniteMulSupport hκ
  have h1 : ∑ᶠ v : FinitePlace L, Real.log (v κ) = Real.log (∏ᶠ v : FinitePlace L, v κ) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun v _ => (FinitePlace.pos_iff.2 hκ).ne')]
    intro v hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hv
    simp [h1]
  have h2 : ∑ φ : L →+* ℂ, Real.log ‖φ κ‖ = Real.log |Algebra.norm ℚ κ| := by
    rw [← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hκ))]
    congr 1
    have := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ κ)
    rw [norm_prod] at this
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) (fun φ => ‖φ κ‖) (fun φ => ‖φ κ‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]
    rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hκ]
  push_cast
  rw [Real.log_inv]

/- English proof (translation)
Use `(show (Function.mulSupport fun v : FinitePlace L => v κ).Finite from FinitePlace.hasFiniteMulSupport hκ).subset fun v hv h1 => hv ?_` and prove the remaining obligations. Simplify using `[show v κ = 1 from h1]`.
-/
theorem log_support_finite {κ : L} (hκ : κ ≠ 0) :
    (Function.support fun v : FinitePlace L => Real.log (v κ)).Finite := by
  refine (show (Function.mulSupport fun v : FinitePlace L => v κ).Finite from
    FinitePlace.hasFiniteMulSupport hκ).subset fun v hv h1 => hv ?_
  simp [show v κ = 1 from h1]

/- English proof (translation)
Introduce `K _ ι _ Ω _ y d _ _ a u q m hq hm hu φ L _ _ w hw val hval hv`. Establish `hm0 : (m : L) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Use `set F : FinitePlace L → ℝ := fun v => ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) with hF`. Establish `hFs : (Function.support F).Finite` using `support_finite w hw.1 _`. Establish `hms` using `log_support_finite hm0`.

Establish `hvs` using `log_support_finite hval`. Use `set T : Finset (FinitePlace L) := hFs.toFinset ∪ hms.toFinset ∪ hvs.toFinset with hT`. Establish `eF : ∑ᶠ v, F v = ∑ v ∈ T, F v` using `finsum_eq_sum_of_support_subset _ (by`. Introduce `v hv'`. Simplify using `only [Finset.coe_union, Set.mem_union, Finset.mem_coe, hT]`.

Conclude with `Or.inl (Or.inl (hFs.mem_toFinset.2 hv')))`. Establish `eM : ∑ᶠ v : FinitePlace L, Real.log (v (m : L)) = ∑ v ∈ T, Real.log (v (m : L))` using `finsum_eq_sum_of_support_subset _ (by`. Introduce `v hv'`. Simplify using `only [Finset.coe_union, Set.mem_union, Finset.mem_coe, hT]`. Conclude with `Or.inl (Or.inr (hms.mem_toFinset.2 hv')))`.

Establish `eV : ∑ᶠ v : FinitePlace L, Real.log (v val) = ∑ v ∈ T, Real.log (v val)` using `finsum_eq_sum_of_support_subset _ (by`. Introduce `v hv'`. Simplify using `only [Finset.coe_union, Set.mem_union, Finset.mem_coe, hT]`. Conclude with `Or.inr (hvs.mem_toFinset.2 hv'))`. Establish `hsum : ∑ᶠ v : FinitePlace L, Real.log (v (m : L)) + q * ∑ᶠ v : FinitePlace L, Real.log (v val) ≤ q * ∑ᶠ v, F v`.

Rewrite using `[eF, eM, eV, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_le_sum fun v _ => local_bound v y a u q m hm hu w hw hval hv`. Establish `hn : (0 : ℝ) < (Module.finrank ℚ L : ℝ)` using `by exact_mod_cast Module.finrank_pos`. Establish `hqr : (0 : ℝ) < q` using `by exact_mod_cast hq`. Establish `hcard : ∑ σ : L →+* ℂ, Real.log ‖σ (m : L)‖ = Module.finrank ℚ L * Real.log m`.

Simplify using `[Finset.card_univ, NumberField.Embeddings.card]`. Rewrite `hsum` using `[product_formula _ hm0, product_formula _ hval, hcard]`. Unfold `ptHt`. Use `beta_reduce`. Rewrite using `[Finset.sum_sub_distrib]`.

Use `set Φ := ∑ σ : L →+* ℂ, φ fun p => σ (w p)`. Use `set Λ := ∑ σ : L →+* ℂ, Real.log ‖σ val‖`. Use `set n : ℝ := (Module.finrank ℚ L : ℝ)`. Establish `hF' : ∑ᶠ v : FinitePlace L, ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) = ∑ᶠ v, F v` using `rfl`. Rewrite using `[hF']`.

Use `set S := ∑ᶠ v, F v`. Establish `h3 : S - (-Λ - n * Real.log m / q) = (q * S - (-(n * Real.log m) + q * -Λ)) / q`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h3' : 0 ≤ S - (-Λ - n * Real.log m / q)`.

Rewrite using `[h3]`. Conclude with `div_nonneg (sub_nonneg.2 hsum) hqr.le`. Establish `h4 : n⁻¹ * (S + Φ) - (n⁻¹ * (Φ - Λ) - Real.log m / q) = n⁻¹ * (S - (-Λ - n * Real.log m / q))`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `h5` using `mul_nonneg (inv_pos.2 hn).le h3'`. Rewrite `h5` using `[← h4]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem height_ge_of_section : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y →
    ∀ (a : K → ℤ) (u : Ω) (q m : ℕ), 0 < q → 0 < m → (m : Ω) * u ^ q ∈ chartLatNm y a q →
    ∀ (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L],
    ∀ w ∈ ptsOver L (mCoordIdeal y), ∀ val : L, val ≠ 0 → HasVal y a u w val →
      (Module.finrank ℚ L : ℝ)⁻¹ * (∑ σ : L →+* ℂ, (φ (fun p => σ (w p)) - Real.log ‖σ val‖)) -
        Real.log m / q ≤ ptHt (fun k => (a k : ℝ)) φ L w := by
  intro K _ ι _ Ω _ y d _ _ a u q m hq hm hu φ L _ _ w hw val hval hv
  have hm0 : (m : L) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  set F : FinitePlace L → ℝ := fun v => ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) with hF
  have hFs : (Function.support F).Finite := support_finite w hw.1 _
  have hms := log_support_finite hm0
  have hvs := log_support_finite hval
  classical
  set T : Finset (FinitePlace L) := hFs.toFinset ∪ hms.toFinset ∪ hvs.toFinset with hT
  have eF : ∑ᶠ v, F v = ∑ v ∈ T, F v := finsum_eq_sum_of_support_subset _ (by
    intro v hv'; simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, hT]
    exact Or.inl (Or.inl (hFs.mem_toFinset.2 hv')))
  have eM : ∑ᶠ v : FinitePlace L, Real.log (v (m : L)) = ∑ v ∈ T, Real.log (v (m : L)) :=
    finsum_eq_sum_of_support_subset _ (by
      intro v hv'; simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, hT]
      exact Or.inl (Or.inr (hms.mem_toFinset.2 hv')))
  have eV : ∑ᶠ v : FinitePlace L, Real.log (v val) = ∑ v ∈ T, Real.log (v val) :=
    finsum_eq_sum_of_support_subset _ (by
      intro v hv'; simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, hT]
      exact Or.inr (hvs.mem_toFinset.2 hv'))
  have hsum : ∑ᶠ v : FinitePlace L, Real.log (v (m : L)) + q * ∑ᶠ v : FinitePlace L, Real.log (v val) ≤
      q * ∑ᶠ v, F v := by
    rw [eF, eM, eV, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v _ => local_bound v y a u q m hm hu w hw hval hv
  have hn : (0 : ℝ) < (Module.finrank ℚ L : ℝ) := by exact_mod_cast Module.finrank_pos
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hcard : ∑ σ : L →+* ℂ, Real.log ‖σ (m : L)‖ = Module.finrank ℚ L * Real.log m := by
    simp [Finset.card_univ, NumberField.Embeddings.card]
  rw [product_formula _ hm0, product_formula _ hval, hcard] at hsum
  unfold ptHt
  beta_reduce
  rw [Finset.sum_sub_distrib]
  set Φ := ∑ σ : L →+* ℂ, φ fun p => σ (w p)
  set Λ := ∑ σ : L →+* ℂ, Real.log ‖σ val‖
  set n : ℝ := (Module.finrank ℚ L : ℝ)
  have hF' : ∑ᶠ v : FinitePlace L, ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) = ∑ᶠ v, F v := rfl
  rw [hF']
  set S := ∑ᶠ v, F v
  have h3 : S - (-Λ - n * Real.log m / q) = (q * S - (-(n * Real.log m) + q * -Λ)) / q := by
    field_simp
    ring
  have h3' : 0 ≤ S - (-Λ - n * Real.log m / q) := by
    rw [h3]
    exact div_nonneg (sub_nonneg.2 hsum) hqr.le
  have h4 : n⁻¹ * (S + Φ) - (n⁻¹ * (Φ - Λ) - Real.log m / q) =
      n⁻¹ * (S - (-Λ - n * Real.log m / q)) := by
    field_simp
    ring
  have h5 := mul_nonneg (inv_pos.2 hn).le h3'
  rw [← h4] at h5
  linarith

end GlobalTheory.CompanionTheory.Ar.Ht.SecLow
