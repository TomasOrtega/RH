import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK
open GlobalTheory.Prism IsLocalRing
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LTPeriodKerSq

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

/- English proof (translation)
Take `⟨n, hn⟩` from `GlobalTheory.AinfK.exists_l_dvd_pow hπ`. Establish `h1` using `map_dvd (intToOC K) hn`. Rewrite `h1` using `[map_natCast, map_pow]`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`.

Conclude with `(inferInstance : Fact ¬IsUnit ((l : ℕ) : OC l)).out (isUnit_of_dvd_unit h1 (h.pow _))`.
-/
theorem intToOC_mem_max {π : ↥(OL K)} (hπ : Irreducible π) : intToOC K π ∈ maximalIdeal (OC l) := by
  obtain ⟨n, hn⟩ := GlobalTheory.AinfK.exists_l_dvd_pow hπ
  have h1 := map_dvd (intToOC K) hn
  rw [map_natCast, map_pow] at h1
  by_contra h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h
  exact (inferInstance : Fact ¬IsUnit ((l : ℕ) : OC l)).out (isUnit_of_dvd_unit h1 (h.pow _))

/- English proof (translation)
Establish `hϖm` using `intToOC_mem_max hπ`. Take `⟨c, hc⟩` from `hs`. Establish `hθ : intToOC K π + thetaK K u ^ (r + 1) = 0`. Use `congrArg (thetaK K) hc` as an intermediate fact. Rewrite `this` using `[map_add, map_pow, thetaK_inO, map_mul, map_pow, thetaK_eta hp, zero_pow two_ne_zero, zero_mul]`. Then use the resulting hypothesis.

Establish `hre : red K (eta π p) = p`. Rewrite using `[eta, map_sub, red_teich, red_inO_eq_zero hπ.not_isUnit, sub_zero]`. Establish `hr : red K v ^ ((r + 2) * (r + 1)) = p ^ 2 * red K c`. Use `congrArg (red K) hc` as an intermediate fact. Rewrite `this` using `[map_add, red_inO_eq_zero hπ.not_isUnit, zero_add, map_pow, hu, map_add, map_mul, red_inO_eq_zero hπ.not_isUnit, zero_mul, zero_add, map_pow, map_mul, map_pow, hre, ← pow_mul]`.

Conclude with `this`. Establish `ha : (red K v).untilt ^ ((r + 2) * (r + 1)) = intToOC K π ^ 2 * (red K c).untilt`. Use `congrArg PreTilt.untilt hr` as an intermediate fact. Rewrite `this` using `[map_pow, map_mul, map_pow, hp]`. Then use the resulting hypothesis. Take `⟨d, hd⟩` from `dvd_thetaK_sub hπ v`.

Establish `hz1 : thetaK K u = intToOC K π * thetaK K v + thetaK K v ^ (r + 2)`. Rewrite using `[hu, map_add, map_mul, thetaK_inO, map_pow]`. Establish `hmp : (maximalIdeal (OC l)).IsPrime` using `inferInstance`. Establish `ham : (red K v).untilt ∈ maximalIdeal (OC l)` using `hmp.mem_of_pow_mem ((r + 2) * (r + 1)) (by`. Rewrite using `[ha]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖm 2 two_pos))`. Establish `hz2m : thetaK K v ∈ maximalIdeal (OC l)`. Rewrite using `[show thetaK K v = (red K v).untilt + intToOC K π * d by linear_combination hd]`. Conclude with `Ideal.add_mem _ ham (Ideal.mul_mem_right _ _ hϖm)`. Establish `hS : (∑ i ∈ Finset.range (r + 2), thetaK K v ^ i * (red K v).untilt ^ (r + 2 - 1 - i)) ∈ maximalIdeal (OC l)` using `Ideal.sum_mem _ fun i _ => by`.

Break down `Nat.eq_zero_or_pos i with rfl | hi0` into its components or cases. Conclude with `Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ham _ (by omega))`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hz2m _ hi0)`. Establish `e1` using `geom_sum₂_mul (thetaK K v) (red K v).untilt (r + 2)`. Establish `e2` using `geom_sum₂_mul (thetaK K u) ((red K v).untilt ^ (r + 2)) (r + 1)`.

Establish `ha' : ((red K v).untilt ^ (r + 2)) ^ (r + 1) = intToOC K π ^ 2 * (red K c).untilt`. Rewrite using `[← pow_mul, ha]`. Use `set S := ∑ i ∈ Finset.range (r + 2), thetaK K v ^ i * (red K v).untilt ^ (r + 2 - 1 - i)`. Use `set S' := ∑ i ∈ Finset.range (r + 1), thetaK K u ^ i * ((red K v).untilt ^ (r + 2)) ^ (r + 1 - 1 - i)`. Establish `key : intToOC K π * (1 + intToOC K π * (red K c).untilt + S' * (thetaK K v + S * d)) = 0`.

Take the linear combination `hθ + e2 - ha' - S' * hz1 + S' * e1 - S' * S * hd`. Establish `hϖ0 : intToOC K π ≠ 0` using `(map_ne_zero_iff _ (GlobalTheory.BKReal.intToOC_injective K)).2 hπ.ne_zero`. Establish `h1` using `(mul_eq_zero.1 key).resolve_left hϖ0`. Establish `hmem : (1 : OC l) ∈ maximalIdeal (OC l)`. Rewrite using `[show (1 : OC l) = -(intToOC K π * (red K c).untilt + S' * (thetaK K v + S * d)) by`.

Take the linear combination `h1]`. Conclude with `neg_mem (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hϖm) (Ideal.mul_mem_left _ _ (Ideal.add_mem _ hz2m (Ideal.mul_mem_right _ _ hS))))`. Conclude with `(maximalIdeal.isMaximal (OC l)).ne_top ((Ideal.eq_top_iff_one _).2 hmem)`.
-/
theorem not_sq_dvd {π : ↥(OL K)} (hπ : Irreducible π) {p : PreTilt (OC l) l} (hp : p.untilt = intToOC K π)
    (r : ℕ) {u v : AK K} (hu : u = inO K π * v + v ^ (r + 2))
    (hs : eta π p ^ 2 ∣ inO K π + u ^ (r + 1)) : False := by
  have hϖm := intToOC_mem_max hπ
  obtain ⟨c, hc⟩ := hs
  have hθ : intToOC K π + thetaK K u ^ (r + 1) = 0 := by
    have := congrArg (thetaK K) hc
    rwa [map_add, map_pow, thetaK_inO, map_mul, map_pow, thetaK_eta hp, zero_pow two_ne_zero, zero_mul] at this
  have hre : red K (eta π p) = p := by
    rw [eta, map_sub, red_teich, red_inO_eq_zero hπ.not_isUnit, sub_zero]
  have hr : red K v ^ ((r + 2) * (r + 1)) = p ^ 2 * red K c := by
    have := congrArg (red K) hc
    rw [map_add, red_inO_eq_zero hπ.not_isUnit, zero_add, map_pow, hu, map_add, map_mul,
      red_inO_eq_zero hπ.not_isUnit, zero_mul, zero_add, map_pow, map_mul, map_pow, hre, ← pow_mul] at this
    exact this
  have ha : (red K v).untilt ^ ((r + 2) * (r + 1)) = intToOC K π ^ 2 * (red K c).untilt := by
    have := congrArg PreTilt.untilt hr
    rwa [map_pow, map_mul, map_pow, hp] at this
  obtain ⟨d, hd⟩ := dvd_thetaK_sub hπ v
  have hz1 : thetaK K u = intToOC K π * thetaK K v + thetaK K v ^ (r + 2) := by
    rw [hu, map_add, map_mul, thetaK_inO, map_pow]
  have hmp : (maximalIdeal (OC l)).IsPrime := inferInstance
  have ham : (red K v).untilt ∈ maximalIdeal (OC l) :=
    hmp.mem_of_pow_mem ((r + 2) * (r + 1)) (by
      rw [ha]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖm 2 two_pos))
  have hz2m : thetaK K v ∈ maximalIdeal (OC l) := by
    rw [show thetaK K v = (red K v).untilt + intToOC K π * d by linear_combination hd]
    exact Ideal.add_mem _ ham (Ideal.mul_mem_right _ _ hϖm)
  have hS : (∑ i ∈ Finset.range (r + 2), thetaK K v ^ i * (red K v).untilt ^ (r + 2 - 1 - i)) ∈
      maximalIdeal (OC l) := Ideal.sum_mem _ fun i _ => by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ham _ (by omega))
    · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hz2m _ hi0)
  have e1 := geom_sum₂_mul (thetaK K v) (red K v).untilt (r + 2)
  have e2 := geom_sum₂_mul (thetaK K u) ((red K v).untilt ^ (r + 2)) (r + 1)
  have ha' : ((red K v).untilt ^ (r + 2)) ^ (r + 1) = intToOC K π ^ 2 * (red K c).untilt := by
    rw [← pow_mul, ha]
  set S := ∑ i ∈ Finset.range (r + 2), thetaK K v ^ i * (red K v).untilt ^ (r + 2 - 1 - i)
  set S' := ∑ i ∈ Finset.range (r + 1), thetaK K u ^ i * ((red K v).untilt ^ (r + 2)) ^ (r + 1 - 1 - i)
  have key : intToOC K π * (1 + intToOC K π * (red K c).untilt + S' * (thetaK K v + S * d)) = 0 := by
    linear_combination hθ + e2 - ha' - S' * hz1 + S' * e1 - S' * S * hd
  have hϖ0 : intToOC K π ≠ 0 := (map_ne_zero_iff _ (GlobalTheory.BKReal.intToOC_injective K)).2 hπ.ne_zero
  have h1 := (mul_eq_zero.1 key).resolve_left hϖ0
  have hmem : (1 : OC l) ∈ maximalIdeal (OC l) := by
    rw [show (1 : OC l) = -(intToOC K π * (red K c).untilt + S' * (thetaK K v + S * d)) by
      linear_combination h1]
    exact neg_mem (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hϖm)
      (Ideal.mul_mem_left _ _ (Ideal.add_mem _ hz2m (Ideal.mul_mem_right _ _ hS))))
  exact (maximalIdeal.isMaximal (OC l)).ne_top ((Ideal.eq_top_iff_one _).2 hmem)

/- English proof (translation)
Use `complete_pi hπ` as an intermediate fact. Establish `hπ0 : inO K π ≠ 0` using `fun h => one_ne_zero (eq_zero_of_mul_pi hπ 1 (by rw [h, mul_zero]))`. Establish `key : ∀ n : ℕ, inO K π ^ (n + 1) ∣ ω` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero`.

Rewrite using `[zero_add, pow_one, ← Ideal.mem_span_singleton, ← ker_red hπ]`. Conclude with `h0`. Consider the case `succ n ih`. Take `⟨y, rfl⟩` from `ih`. Take `⟨x, hx⟩` from `(frobq_bijective K).2 (y + inO K π ^ (n * r + n + r) * y ^ (r + 2))`.

Rewrite `hF` using `[map_mul, map_pow, frobq_inO]`. Establish `h1 : frobq K y = frobq K (inO K π * x)`. Use `mul_left_cancel₀ (pow_ne_zero (n + 1) hπ0) ?_` and prove the remaining obligations. Rewrite using `[hF, map_mul, frobq_inO, hx]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `⟨x, by rw [(frobq_bijective K).1 h1]; ring⟩`. Conclude with `GlobalTheory.Per.AinfComplete.eq_zero_of_haus (inO K π) ω fun n => Ideal.mem_span_singleton.2 ((pow_dvd_pow _ n.le_succ).trans (key n))`.
-/
theorem eq_zero_of_red {π : ↥(OL K)} (hπ : Irreducible π) (r : ℕ) {ω : AK K}
    (hF : frobq K ω = inO K π * ω + ω ^ (r + 2)) (h0 : red K ω = 0) : ω = 0 := by
  have := complete_pi hπ
  have hπ0 : inO K π ≠ 0 := fun h => one_ne_zero (eq_zero_of_mul_pi hπ 1 (by rw [h, mul_zero]))
  have key : ∀ n : ℕ, inO K π ^ (n + 1) ∣ ω := fun n => by
    induction n with
    | zero =>
      rw [zero_add, pow_one, ← Ideal.mem_span_singleton, ← ker_red hπ]
      exact h0
    | succ n ih =>
      obtain ⟨y, rfl⟩ := ih
      obtain ⟨x, hx⟩ := (frobq_bijective K).2 (y + inO K π ^ (n * r + n + r) * y ^ (r + 2))
      rw [map_mul, map_pow, frobq_inO] at hF
      have h1 : frobq K y = frobq K (inO K π * x) := by
        refine mul_left_cancel₀ (pow_ne_zero (n + 1) hπ0) ?_
        rw [hF, map_mul, frobq_inO, hx]
        ring
      exact ⟨x, by rw [(frobq_bijective K).1 h1]; ring⟩
  exact GlobalTheory.Per.AinfComplete.eq_zero_of_haus (inO K π) ω fun n =>
    Ideal.mem_span_singleton.2 ((pow_dvd_pow _ n.le_succ).trans (key n))

open GlobalTheory.Per.AinfComplete in

/- English proof (translation)
Introduce `hω2`. Take `⟨p, hp⟩` from `GlobalTheory.MemLoc.FundOnto.untilt_surjective l (intToOC K π)`. Establish `hker` using `ker_thetaK hπ hp`. Establish `hq : 2 ≤ resCard K` using `hl.out.two_le.trans (Nat.le_self_pow (card_res' K).1 l)`. Take `⟨r, hr⟩ : ∃ r, resCard K = r + 2` from `⟨resCard K - 2, by omega⟩`.

Establish `hr' : l ^ fK K = r + 2` using `hr`. Rewrite `hF` using `[hr]`. Establish `hdiv : ∀ x, thetaK K x = 0 ↔ eta π p ∣ x` using `fun x => by`. Rewrite using `[← RingHom.mem_ker, hker, Ideal.mem_span_singleton]`. Establish `hη0 : eta π p ≠ 0` using `fun h => hω0 (zero_dvd_iff.1 (h ▸ (hdiv ω).1 hθ))`.

Establish `hηp : Prime (eta π p)`. Rewrite using `[← Ideal.span_singleton_prime hη0, ← hker]`. Conclude with `RingHom.ker_isPrime _`. Establish `hϖ0 : intToOC K π ≠ 0` using `(map_ne_zero_iff _ (GlobalTheory.BKReal.intToOC_injective K)).2 hπ.ne_zero`. Rewrite `hω2` using `[hker, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.

Take `⟨G, hG⟩` from `(frobq_bijective K).2.hasRightInverse`. Set `w : ℕ → AK K` to `fun n => G^[n] ω`. Establish `hw : ∀ n, frobq K (w (n + 1)) = w n` using `fun n => by`. Simplify using `only [w, Function.iterate_succ_apply']`. Conclude with `hG _`.

Establish `hFw : ∀ n, frobq K (w n) = inO K π * w n + w n ^ (r + 2)` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => exact hF`. Consider the case `succ n ih`. Use `(frobq_bijective K).1 ?_` and prove the remaining obligations.

Rewrite using `[map_add, map_mul, map_pow, frobq_inO, hw, ih]`. Establish `hrec : ∀ n, w n = inO K π * w (n + 1) + w (n + 1) ^ (r + 2)` using `fun n => by rw [← hFw, hw]`. Establish `hall : ∀ n, eta π p ^ 2 ∣ w n` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => exact hω2`.

Consider the case `succ n ih`. Rewrite `ih` using `[hrec n]`. Distinguish the cases in `hu : eta π p ∣ w (n + 1)`. Take `⟨a, ha⟩` from `hu`. Rewrite `ih` using `[ha, show inO K π * (eta π p * a) + (eta π p * a) ^ (r + 2) = eta π p * (inO K π * a + eta π p * (eta π p ^ r * a ^ (r + 2))) by ring, sq, mul_dvd_mul_iff_left hη0, dvd_add_left (dvd_mul_right _ _)]`.

Break down `hηp.dvd_or_dvd ih with h | h` into its components or cases. Conclude with `absurd (thetaK_inO π ▸ (hdiv _).2 h) hϖ0`. Rewrite using `[ha, sq]`. Conclude with `mul_dvd_mul_left _ h`. Rewrite `ih` using `[show inO K π * w (n + 1) + w (n + 1) ^ (r + 2) = w (n + 1) * (inO K π + w (n + 1) ^ (r + 1)) by ring]`.

Conclude with `(not_sq_dvd hπ hp r (hrec (n + 1)) (hηp.pow_dvd_of_dvd_mul_left 2 hu ih)).elim`. Establish `hre : red K (eta π p) = p`. Rewrite using `[eta, map_sub, red_teich, red_inO_eq_zero hπ.not_isUnit, sub_zero]`. Establish `hred : ∀ n, red K ω = red K (w n) ^ (r + 2) ^ n` using `fun n => by`. Proceed by induction on `n with`.

Consider the case `zero => simp [w]`. Consider the case `succ n ih => rw [ih, ← hw n, red_frobq, hr', ← pow_mul, ← pow_succ']`. Establish `hpu : ¬ IsUnit p` using `fun h => intToOC_mem_max hπ (hp ▸ h.map PreTilt.untilt)`. Establish `h1 : IsNilpotent (Perfection.coeff (ModP (OC l) l) l 0 p)` using `nilpotent_of_not_isUnit l _ fun h => hpu (perfection_isUnit _ h)`. Use `hω0 (eq_zero_of_red hπ r hF (perfection_haus (p := l) (R := ModP (OC l) l) h1 (red K ω) fun n => ?_))` and prove the remaining obligations.

Establish `h2 : p ∣ red K (w n)`. Rewrite using `[← hre]`. Conclude with `map_dvd _ ((dvd_pow_self _ two_ne_zero).trans (hall n))`. Establish `h3 : p ^ n ∣ red K ω`. Rewrite using `[hred n]`.

Conclude with `(pow_dvd_pow p (Nat.lt_pow_self (by omega)).le).trans (pow_dvd_pow_of_dvd h2 _)`. Conclude with `h3`.
-/
theorem not_mem_sq {π : ↥(OL K)} (hπ : Irreducible π) {ω : AK K} (hω0 : ω ≠ 0) (hθ : thetaK K ω = 0)
    (hF : frobq K ω = inO K π * ω + ω ^ resCard K) : ω ∉ RingHom.ker (thetaK K) ^ 2 := by
  intro hω2
  obtain ⟨p, hp⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (intToOC K π)
  have hker := ker_thetaK hπ hp
  have hq : 2 ≤ resCard K :=
    hl.out.two_le.trans (Nat.le_self_pow (card_res' K).1 l)
  obtain ⟨r, hr⟩ : ∃ r, resCard K = r + 2 := ⟨resCard K - 2, by omega⟩
  have hr' : l ^ fK K = r + 2 := hr
  rw [hr] at hF
  have hdiv : ∀ x, thetaK K x = 0 ↔ eta π p ∣ x := fun x => by
    rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton]
  have hη0 : eta π p ≠ 0 := fun h => hω0 (zero_dvd_iff.1 (h ▸ (hdiv ω).1 hθ))
  have hηp : Prime (eta π p) := by
    rw [← Ideal.span_singleton_prime hη0, ← hker]
    exact RingHom.ker_isPrime _
  have hϖ0 : intToOC K π ≠ 0 := (map_ne_zero_iff _ (GlobalTheory.BKReal.intToOC_injective K)).2 hπ.ne_zero
  rw [hker, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hω2
  obtain ⟨G, hG⟩ := (frobq_bijective K).2.hasRightInverse
  let w : ℕ → AK K := fun n => G^[n] ω
  have hw : ∀ n, frobq K (w (n + 1)) = w n := fun n => by
    simp only [w, Function.iterate_succ_apply']
    exact hG _
  have hFw : ∀ n, frobq K (w n) = inO K π * w n + w n ^ (r + 2) := fun n => by
    induction n with
    | zero => exact hF
    | succ n ih =>
      refine (frobq_bijective K).1 ?_
      rw [map_add, map_mul, map_pow, frobq_inO, hw, ih]
  have hrec : ∀ n, w n = inO K π * w (n + 1) + w (n + 1) ^ (r + 2) := fun n => by rw [← hFw, hw]
  have hall : ∀ n, eta π p ^ 2 ∣ w n := fun n => by
    induction n with
    | zero => exact hω2
    | succ n ih =>
      rw [hrec n] at ih
      by_cases hu : eta π p ∣ w (n + 1)
      · obtain ⟨a, ha⟩ := hu
        rw [ha, show inO K π * (eta π p * a) + (eta π p * a) ^ (r + 2) =
          eta π p * (inO K π * a + eta π p * (eta π p ^ r * a ^ (r + 2))) by ring, sq,
          mul_dvd_mul_iff_left hη0, dvd_add_left (dvd_mul_right _ _)] at ih
        rcases hηp.dvd_or_dvd ih with h | h
        · exact absurd (thetaK_inO π ▸ (hdiv _).2 h) hϖ0
        · rw [ha, sq]
          exact mul_dvd_mul_left _ h
      · rw [show inO K π * w (n + 1) + w (n + 1) ^ (r + 2) =
          w (n + 1) * (inO K π + w (n + 1) ^ (r + 1)) by ring] at ih
        exact (not_sq_dvd hπ hp r (hrec (n + 1)) (hηp.pow_dvd_of_dvd_mul_left 2 hu ih)).elim
  have hre : red K (eta π p) = p := by
    rw [eta, map_sub, red_teich, red_inO_eq_zero hπ.not_isUnit, sub_zero]
  have hred : ∀ n, red K ω = red K (w n) ^ (r + 2) ^ n := fun n => by
    induction n with
    | zero => simp [w]
    | succ n ih => rw [ih, ← hw n, red_frobq, hr', ← pow_mul, ← pow_succ']
  have hpu : ¬ IsUnit p := fun h => intToOC_mem_max hπ (hp ▸ h.map PreTilt.untilt)
  have h1 : IsNilpotent (Perfection.coeff (ModP (OC l) l) l 0 p) :=
    nilpotent_of_not_isUnit l _ fun h => hpu (perfection_isUnit _ h)
  refine hω0 (eq_zero_of_red hπ r hF (perfection_haus (p := l) (R := ModP (OC l) l) h1 (red K ω) fun n => ?_))
  have h2 : p ∣ red K (w n) := by
    rw [← hre]
    exact map_dvd _ ((dvd_pow_self _ two_ne_zero).trans (hall n))
  have h3 : p ^ n ∣ red K ω := by
    rw [hred n]
    exact (pow_dvd_pow p (Nat.lt_pow_self (by omega)).le).trans (pow_dvd_pow_of_dvd h2 _)
  exact h3

/- English proof (translation)
Introduce `l _ K χ π z hLT ω hω0 hθ hF _`. Conclude with `not_mem_sq hLT.1 hω0 hθ hF`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∀ ω : AK K, ω ≠ 0 → thetaK K ω = 0 → frobq K ω = inO K π * ω + ω ^ resCard K →
      (∀ (g : ↥(GK K)) (a : ↥(OL K)) (φ : PowerSeries ↥(OL K)), (a : ↥K.1) = (χ g : ↥K.1) → IsLTEndo K π a φ →
        ∀ n : ℕ, gal K g ω - ∑ j ∈ Finset.range n, inO K (PowerSeries.coeff j φ) * ω ^ j ∈ RingHom.ker (thetaK K) ^ n) →
      ω ∉ RingHom.ker (thetaK K) ^ 2 := by
  intro l _ K χ π z hLT ω hω0 hθ hF _
  exact not_mem_sq hLT.1 hω0 hθ hF

end GlobalTheory.LTPeriodKerSq
