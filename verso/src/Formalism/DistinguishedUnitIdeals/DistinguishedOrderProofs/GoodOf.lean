import Mathlib
import Formalism.DistinguishedUnitIdeals.FrobeniusDiffBijective
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.RhoMapFunctorial
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GroundTheory

noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

namespace GoodPlacesAlt

open IdempotentNormalFormsRhoFacts

section ring
variable {O : Type} [CommRing O]

/- English proof (translation)
The claim follows from `(AlgHom.coe_pow f k).symm`.
-/
theorem it_eq (f : PowerSeries O →ₐ[O] PowerSeries O) (k : ℕ) : (⇑f)^[k] = ⇑(f ^ k) :=
  (AlgHom.coe_pow f k).symm

/- English proof (translation)
Rewrite using `[it_eq, map_mul]`.
-/
theorem it_mul (f : PowerSeries O →ₐ[O] PowerSeries O) (k : ℕ) (a b : PowerSeries O) :
    (⇑f)^[k] (a * b) = (⇑f)^[k] a * (⇑f)^[k] b := by
  rw [it_eq, map_mul]

/- English proof (translation)
Rewrite using `[it_eq, map_add]`.
-/
theorem it_add (f : PowerSeries O →ₐ[O] PowerSeries O) (k : ℕ) (a b : PowerSeries O) :
    (⇑f)^[k] (a + b) = (⇑f)^[k] a + (⇑f)^[k] b := by
  rw [it_eq, map_add]

/- English proof (translation)
Rewrite using `[it_eq]`. Conclude with `map_dvd _ h`.
-/
theorem it_dvd (f : PowerSeries O →ₐ[O] PowerSeries O) (k : ℕ) {a b : PowerSeries O}
    (h : a ∣ b) : (⇑f)^[k] a ∣ (⇑f)^[k] b := by
  rw [it_eq]
  exact map_dvd _ h

/- English proof (translation)
Simplify using `only [Base.p, Function.iterate_succ_apply']`.
-/
theorem φ_p (B : Base O) (s : ℕ) : B.φ (B.p s) = B.p (s + 1) := by
  simp only [Base.p, Function.iterate_succ_apply']

/- English proof (translation)
Simplify using `only [Base.p]`. Rewrite using `[← Function.iterate_add_apply, add_comm]`.
-/
theorem it_p (B : Base O) (k s : ℕ) : (⇑B.φ)^[k] (B.p s) = B.p (s + k) := by
  simp only [Base.p]
  rw [← Function.iterate_add_apply, add_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem p_zero (B : Base O) : B.p 0 = B.q := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem it_q (B : Base O) (k : ℕ) : (⇑B.φ)^[k] B.q = B.p k := rfl

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← B.comm, ih]`.
-/
theorem γ_it (B : Base O) (k : ℕ) (a : PowerSeries O) :
    B.γ ((⇑B.φ)^[k] a) = (⇑B.φ)^[k] (B.γ a) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← B.comm, ih]

/- English proof (translation)
Rewrite using `[map_prod]`. Conclude with `Finset.prod_congr rfl fun s _ => by rw [map_pow, φ_p]`.
-/
theorem φ_prod_p (B : Base O) (k : ℕ) (e : ℕ → ℕ) :
    B.φ (∏ s ∈ Finset.range k, B.p s ^ e s) = ∏ s ∈ Finset.range k, B.p (s + 1) ^ e s := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun s _ => by rw [map_pow, φ_p]

/- English proof (translation)
Take `⟨u₀, hu₀⟩` from `h`. Proceed by induction on `j with`. Consider the case `zero => exact ⟨1, by simp⟩`. Consider the case `succ j ih`. Take `⟨u, hu⟩` from `ih`.

Use `⟨Units.map (B.φ : PowerSeries O →* PowerSeries O) u * u₀, ?_⟩` and prove the remaining obligations. Rewrite using `[Function.iterate_succ_apply', hu, map_mul, map_mul, hu₀, φ_prod_p, Finset.prod_range_succ', p_zero]`. Simplify using `only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem e3it (B : Base O) (h : B.E3) (j : ℕ) : B.E3it j := by
  obtain ⟨u₀, hu₀⟩ := h
  induction j with
  | zero => exact ⟨1, by simp⟩
  | succ j ih =>
    obtain ⟨u, hu⟩ := ih
    refine ⟨Units.map (B.φ : PowerSeries O →* PowerSeries O) u * u₀, ?_⟩
    rw [Function.iterate_succ_apply', hu, map_mul, map_mul, hu₀, φ_prod_p,
      Finset.prod_range_succ', p_zero]
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
    ring

/- English proof (translation)
Take `⟨c, d, rfl⟩` from `Ideal.mem_span_pair.1 h`. Take `⟨w, hw⟩` from `sub_dvd_pow_sub_pow (c * a + d * t) (d * t) N`. Use `Ideal.mem_span_pair.2 ⟨c * w, d ^ N, ?_⟩` and prove the remaining obligations. Establish `: (c * a + d * t) ^ N = (c * a + d * t - d * t) * w + (d * t) ^ N` using `by rw [← hw]; ring`. Rewrite using `[this, mul_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pow_mem_pair {a t y : PowerSeries O} (h : y ∈ Ideal.span {a, t}) (N : ℕ) :
    y ^ N ∈ Ideal.span {a, t ^ N} := by
  obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.1 h
  obtain ⟨w, hw⟩ := sub_dvd_pow_sub_pow (c * a + d * t) (d * t) N
  refine Ideal.mem_span_pair.2 ⟨c * w, d ^ N, ?_⟩
  have : (c * a + d * t) ^ N = (c * a + d * t - d * t) * w + (d * t) ^ N := by rw [← hw]; ring
  rw [this, mul_pow]
  ring

/- English proof (translation)
Take `⟨u, hu⟩` from `h`. Establish `hq : B.q ∈ Ideal.span {B.lc, (X : PowerSeries O)}` using `Ideal.mem_span_pair.2 ⟨1, 1, by simp [Base.q, Base.lc, add_comm]⟩`. Take `⟨c, d, hcd⟩` from `Ideal.mem_span_pair.1 (pow_mem_pair hq (B.ℓ - 1))`. Use `Ideal.mem_span_pair.2 ⟨(u : PowerSeries O) * X * c, (u : PowerSeries O) * d, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, ← hcd]`.

Take `⟨m, hm⟩ : ∃ m, B.ℓ = m + 1` from `⟨B.ℓ - 1, by omega⟩`. Rewrite using `[hm, Nat.add_sub_cancel, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem φX_mem (B : Base O) (hl : 1 ≤ B.ℓ) (h : B.E3) :
    B.φ X ∈ Ideal.span {B.lc, (X : PowerSeries O) ^ B.ℓ} := by
  obtain ⟨u, hu⟩ := h
  have hq : B.q ∈ Ideal.span {B.lc, (X : PowerSeries O)} :=
    Ideal.mem_span_pair.2 ⟨1, 1, by simp [Base.q, Base.lc, add_comm]⟩
  obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.1 (pow_mem_pair hq (B.ℓ - 1))
  refine Ideal.mem_span_pair.2 ⟨(u : PowerSeries O) * X * c, (u : PowerSeries O) * d, ?_⟩
  rw [hu, ← hcd]
  obtain ⟨m, hm⟩ : ∃ m, B.ℓ = m + 1 := ⟨B.ℓ - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel, pow_succ]
  ring

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => exact Ideal.mem_span_pair.2 ⟨0, 1, by simp⟩`. Consider the case `succ s ih`. Take `⟨c, d, hcd⟩` from `Ideal.mem_span_pair.1 ih`. Take `⟨c', d', hcd'⟩` from `Ideal.mem_span_pair.1 (pow_mem_pair (φX_mem B hl h) (B.ℓ ^ s))`.

Use `Ideal.mem_span_pair.2 ⟨B.φ c + B.φ d * c', B.φ d * d', ?_⟩` and prove the remaining obligations. Rewrite using `[Function.iterate_succ_apply', ← hcd, map_add, map_mul, map_mul, map_pow, ← hcd']`. Establish `: B.φ B.lc = B.lc` using `alg_C B.φ _`. Rewrite using `[this, pow_succ, pow_mul', ← pow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem itX_mem (B : Base O) (hl : 1 ≤ B.ℓ) (h : B.E3) (s : ℕ) :
    (⇑B.φ)^[s] X ∈ Ideal.span {B.lc, (X : PowerSeries O) ^ (B.ℓ ^ s)} := by
  induction s with
  | zero => exact Ideal.mem_span_pair.2 ⟨0, 1, by simp⟩
  | succ s ih =>
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.1 ih
    obtain ⟨c', d', hcd'⟩ := Ideal.mem_span_pair.1 (pow_mem_pair (φX_mem B hl h) (B.ℓ ^ s))
    refine Ideal.mem_span_pair.2 ⟨B.φ c + B.φ d * c', B.φ d * d', ?_⟩
    rw [Function.iterate_succ_apply', ← hcd, map_add, map_mul, map_mul, map_pow, ← hcd']
    have : B.φ B.lc = B.lc := alg_C B.φ _
    rw [this, pow_succ, pow_mul', ← pow_mul]
    ring

/- English proof (translation)
Establish `: B.p s = (⇑B.φ)^[s] X + B.lc`. Simplify using `only [Base.p, Base.q, Base.lc]`. Rewrite using `[it_add, it_C]`. Rewrite using `[Base.E2, this]`. Conclude with `Ideal.add_mem _ (itX_mem B hl h s) (Ideal.subset_span (by simp))`.
-/
theorem e2 (B : Base O) (hl : 1 ≤ B.ℓ) (h : B.E3) (s : ℕ) : B.E2 s := by
  have : B.p s = (⇑B.φ)^[s] X + B.lc := by
    simp only [Base.p, Base.q, Base.lc]
    rw [it_add, it_C]
  rw [Base.E2, this]
  exact Ideal.add_mem _ (itX_mem B hl h s) (Ideal.subset_span (by simp))

/- English proof (translation)
Take `⟨e, he⟩` from `h`. Use `⟨1 + (e : PowerSeries O) * X, ?_⟩` and prove the remaining obligations. Establish `: B.γ B.q = B.γ X + C (B.ℓ : O)`. Simplify using `only [Base.q]`. Rewrite using `[map_add, alg_C]`.

Rewrite using `[this, he]`. Simplify using `only [Base.q]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem q_dvd_γq (B : Base O) (h : B.E4) : B.q ∣ B.γ B.q := by
  obtain ⟨e, he⟩ := h
  refine ⟨1 + (e : PowerSeries O) * X, ?_⟩
  have : B.γ B.q = B.γ X + C (B.ℓ : O) := by
    simp only [Base.q]
    rw [map_add, alg_C]
  rw [this, he]
  simp only [Base.q]
  ring

/- English proof (translation)
Simplify using `only [Base.p]`. Rewrite using `[γ_it]`. Conclude with `it_dvd _ _ (q_dvd_γq B h)`.
-/
theorem p_dvd_γp (B : Base O) (h : B.E4) (s : ℕ) : B.p s ∣ B.γ (B.p s) := by
  simp only [Base.p]
  rw [γ_it]
  exact it_dvd _ _ (q_dvd_γq B h)

end ring

end GoodPlacesAlt

open GoodPlacesAlt IdempotentNormalFormsRhoFacts

/- English proof (translation)
Introduce `_ _ B h j` and use `e3it B h j`.
-/
theorem iterated_third_estimate_holds : E3itOf := fun _ _ B h j => e3it B h j

/- English proof (translation)
Introduce `_ _ B hl h s` and use `e2 B hl h s`.
-/
theorem second_estimate_holds : LevelFactorMemSpanOf := fun _ _ B hl h s => e2 B hl h s

/- English proof (translation)
Introduce `O _ B j M g h3 h4 hM`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `h4`. Rewrite using `[he]`. Conclude with `Ideal.mem_span_singleton.2 ⟨_, rfl⟩`.

Rewrite using `[Ideal.mem_span_singleton]`. Simplify using `only [Base.ff]`. Rewrite using `[map_mul, map_pow, map_prod]`. Use `mul_dvd_mul (pow_dvd_pow_of_dvd ?_ _) (Finset.prod_dvd_prod_of_dvd _ _ fun s _ => ?_)` and prove the remaining obligations. Take `⟨e, he⟩` from `h4`.

Rewrite using `[he]`. Conclude with `⟨_, rfl⟩`. Rewrite using `[map_pow]`. Conclude with `pow_dvd_pow_of_dvd (p_dvd_γp B h4 s) _`. Take `⟨u, hu⟩` from `e3it B h3 j`.

Rewrite using `[Ideal.mem_span_singleton, hu, mul_pow, mul_pow, mul_assoc]`. Use `Dvd.dvd.mul_left ?_ _` and prove the remaining obligations. Simplify using `only [Base.ff]`. Use `mul_dvd_mul dvd_rfl ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_pow]`.

Use `Finset.prod_dvd_prod_of_dvd _ _ fun s _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_mul]`. Conclude with `pow_dvd_pow _ hM`.
-/
theorem base_ring_good_holds : BaseGoodOf := by
  intro O _ B j M g h3 h4 hM
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨e, he⟩ := h4
    rw [he]
    exact Ideal.mem_span_singleton.2 ⟨_, rfl⟩
  · rw [Ideal.mem_span_singleton]
    simp only [Base.ff]
    rw [map_mul, map_pow, map_prod]
    refine mul_dvd_mul (pow_dvd_pow_of_dvd ?_ _) (Finset.prod_dvd_prod_of_dvd _ _ fun s _ => ?_)
    · obtain ⟨e, he⟩ := h4
      rw [he]
      exact ⟨_, rfl⟩
    · rw [map_pow]
      exact pow_dvd_pow_of_dvd (p_dvd_γp B h4 s) _
  · obtain ⟨u, hu⟩ := e3it B h3 j
    rw [Ideal.mem_span_singleton, hu, mul_pow, mul_pow, mul_assoc]
    refine Dvd.dvd.mul_left ?_ _
    simp only [Base.ff]
    refine mul_dvd_mul dvd_rfl ?_
    rw [← Finset.prod_pow]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun s _ => ?_
    rw [← pow_mul]
    exact pow_dvd_pow _ hM

namespace GoodPlacesAlt

section lat
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] (L : Lat B n V)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_dv {a : PowerSeries O} {S : Submodule (PowerSeries O) V} {v : V} :
    v ∈ dv a S ↔ a • v ∈ S := Iff.rfl

/- English proof (translation)
Introduce `v hv`. Take `⟨u, hu, rfl⟩` from `mem_sm.1 hv`. Conclude with `h hu`.
-/
theorem sm_le_of_le_dv {a : PowerSeries O} {S T : Submodule (PowerSeries O) V}
    (h : S ≤ dv a T) : sm a S ≤ T := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := mem_sm.1 hv
  exact h hu

/- English proof (translation)
Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun s hs => ?_` and prove the remaining obligations. Rewrite using `[← pow_add, Nat.sub_add_cancel (h s (Finset.mem_range.1 hs))]`.
-/
theorem prod_split (p : ℕ → PowerSeries O) (k : ℕ) (e e' : ℕ → ℕ) (h : ∀ s < k, e s ≤ e' s) :
    ∏ s ∈ Finset.range k, p s ^ e' s =
      (∏ s ∈ Finset.range k, p s ^ (e' s - e s)) * ∏ s ∈ Finset.range k, p s ^ e s := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s hs => ?_
  rw [← pow_add, Nat.sub_add_cancel (h s (Finset.mem_range.1 hs))]

/- English proof (translation)
Introduce `v hv`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Rewrite using `[add_comm, pow_add, mul_smul]`. Conclude with `(L.N i).smul_mem _ (h v hv)`.
-/
theorem lattice_exponent_property_mono {i : ZMod n} {m m' : ℕ} (h : L.P5M i m) (hm : m ≤ m') : L.P5M i m' := by
  intro v hv
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm, pow_add, mul_smul]
  exact (L.N i).smul_mem _ (h v hv)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa [Lat.phiIt] using hv`. Consider the case `succ k ih`. Establish `ih'` using `ih (by omega)`. Establish `e : c + ((k + 1 : ℕ) : ZMod n) - 1 = c + (k : ZMod n)`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h5` using `h (k + 1) (by omega) hk ((∏ s ∈ Finset.range k, B.p s ^ G) • L.phiIt c k v) (by rw [e]; exact ih')`. Rewrite `h5` using `[L.φ_semi, φ_prod_p, smul_smul]`. Rewrite using `[Finset.prod_range_succ', p_zero, mul_comm]`.

Conclude with `h5`.
-/
theorem phi_iterate_mem_lattice {c : ZMod n} {j G : ℕ}
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ j → L.P5M (c + (k : ZMod n)) G) (k : ℕ) (hk : k ≤ j) {v : V}
    (hv : v ∈ L.N c) :
    (∏ s ∈ Finset.range k, B.p s ^ G) • L.phiIt c k v ∈ L.N (c + (k : ZMod n)) := by
  induction k with
  | zero => simpa [Lat.phiIt] using hv
  | succ k ih =>
    have ih' := ih (by omega)
    have e : c + ((k + 1 : ℕ) : ZMod n) - 1 = c + (k : ZMod n) := by
      push_cast
      ring
    have h5 := h (k + 1) (by omega) hk ((∏ s ∈ Finset.range k, B.p s ^ G) • L.phiIt c k v)
      (by rw [e]; exact ih')
    rw [L.φ_semi, φ_prod_p, smul_smul] at h5
    rw [Finset.prod_range_succ', p_zero, mul_comm]
    exact h5

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [Lat.phiIt]`. Consider the case `succ k ih`. Establish `e : i + ((k + 1 + 1 : ℕ) : ZMod n) = i + 1 + ((k + 1 : ℕ) : ZMod n)`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e, ih]`. Use `_ = L.phiIt (i + 1) (k + 1) (L.φ (i + 1) v) := rfl`.
-/
theorem phiIt_succ' (i : ZMod n) (k : ℕ) (v : V) :
    L.phiIt i (k + 1) v = L.phiIt (i + 1) k (L.φ (i + 1) v) := by
  induction k with
  | zero => simp [Lat.phiIt]
  | succ k ih =>
    have e : i + ((k + 1 + 1 : ℕ) : ZMod n) = i + 1 + ((k + 1 : ℕ) : ZMod n) := by
      push_cast
      ring
    calc L.phiIt i (k + 1 + 1) v = L.φ (i + ((k + 1 + 1 : ℕ) : ZMod n)) (L.phiIt i (k + 1) v) := rfl
      _ = L.φ (i + 1 + ((k + 1 : ℕ) : ZMod n)) (L.phiIt (i + 1) k (L.φ (i + 1) v)) := by
        rw [e, ih]
      _ = L.phiIt (i + 1) (k + 1) (L.φ (i + 1) v) := rfl

/- English proof (translation)
Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, hw, rfl⟩` from `hx`. Rewrite using `[← phiIt_succ']`. Conclude with `phiIt_mem_pull L _ hw`.

Consider the case `zero => rw [phiIt_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [phiIt_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [phiIt_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem phiIt_span (i : ZMod n) (k : ℕ) {t : V}
    (ht : t ∈ Submodule.span (PowerSeries O) (L.φ (i + 1) '' (L.N i : Set V))) :
    L.phiIt (i + 1) k t ∈ L.pull i (k + 1) := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [← phiIt_succ']
    exact phiIt_mem_pull L _ hw
  | zero => rw [phiIt_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [phiIt_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [phiIt_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, hw, rfl⟩` from `hx`. Establish `h5'` using `h5 w hw`. Rewrite `h5'` using `[add_sub_cancel_right]`.

Use `phiIt_span L i k h5'` as an intermediate fact. Rewrite `this` using `[phiIt_smul, it_pow, it_q]`. Then use the resulting hypothesis. Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem pullback_smul_mem_next (i : ZMod n) (k h : ℕ) (h5 : L.FrobeniusCobounded (i + 1) h) {y : V}
    (hy : y ∈ L.pull (i + 1) k) : B.p k ^ h • y ∈ L.pull i (k + 1) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    have h5' := h5 w hw
    rw [add_sub_cancel_right] at h5'
    have := phiIt_span L i k h5'
    rwa [phiIt_smul, it_pow, it_q] at this
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Establish `: x ∈ L.N (c - ((0 : ℕ) : ZMod n))` using `by simpa using hx`. Simplify `phiIt_mem_pull L 0 this` using `[Lat.phiIt]`. Consider the case `succ k ih`.

Establish `e : c - ((k + 1 : ℕ) : ZMod n) + 1 = c - (k : ZMod n)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h5` using `h k (by omega)`. Establish `ih'` using `ih (by omega)`.

Rewrite `h5`, `ih'` using `[← e]`. Rewrite using `[Finset.prod_range_succ, mul_comm, mul_smul]`. Conclude with `pullback_smul_mem_next L _ k _ h5 ih'`.
-/
theorem product_smul_mem_pullback {c : ZMod n} {ell : ℕ} {hh : ℕ → ℕ}
    (h : ∀ s < ell, L.FrobeniusCobounded (c - (s : ZMod n)) (hh s)) (k : ℕ) (hk : k ≤ ell) {x : V}
    (hx : x ∈ L.N c) :
    (∏ s ∈ Finset.range k, B.p s ^ hh s) • x ∈ L.pull (c - (k : ZMod n)) k := by
  induction k with
  | zero =>
    have : x ∈ L.N (c - ((0 : ℕ) : ZMod n)) := by simpa using hx
    simpa [Lat.phiIt] using phiIt_mem_pull L 0 this
  | succ k ih =>
    have e : c - ((k + 1 : ℕ) : ZMod n) + 1 = c - (k : ZMod n) := by
      push_cast
      ring
    have h5 := h k (by omega)
    have ih' := ih (by omega)
    rw [← e] at h5 ih'
    rw [Finset.prod_range_succ, mul_comm, mul_smul]
    exact pullback_smul_mem_next L _ k _ h5 ih'

end lat

end GoodPlacesAlt

/- English proof (translation)
Introduce `O _ B n _ j M g G V _ _ L c hG h`. Apply `sm_le_of_le_dv` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Express the relevant statement in the definitionally equal form `B.ff j M g • L.phiIt c j v ∈ sm (X ^ M) (L.N (c + (j : ZMod n)))`.

Establish `h1` using `phi_iterate_mem_lattice L h j le_rfl hv`. Simplify using `only [Base.ff]`. Rewrite using `[prod_split B.p j (fun _ => G) (fun _ => 3 * g) (fun _ _ => hG), mul_smul, mul_smul]`. Conclude with `smul_mem_sm _ (Submodule.smul_mem _ _ h1)`.
-/
theorem lattice_induction_lemma_holds : TruncSpanLe := by
  intro O _ B n _ j M g G V _ _ L c hG h
  apply sm_le_of_le_dv
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  change B.ff j M g • L.phiIt c j v ∈ sm (X ^ M) (L.N (c + (j : ZMod n)))
  have h1 := phi_iterate_mem_lattice L h j le_rfl hv
  simp only [Base.ff]
  rw [prod_split B.p j (fun _ => G) (fun _ => 3 * g) (fun _ _ => hG), mul_smul, mul_smul]
  exact smul_mem_sm _ (Submodule.smul_mem _ _ h1)

/- English proof (translation)
Introduce `O _ B n _ M V _ _ L Mi h3 h5 hM`. Establish `key : L.FrobeniusMapsXPow M`. Introduce `i v hv`. Take `⟨w, hw, rfl⟩` from `mem_sm.1 hv`. Take `⟨u, hu⟩` from `h3`.

Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_lt (hM i)`. Establish `h5'` using `h5 i w hw`. Establish `: B.φ (X ^ M) = (X ^ M * B.q) * ((u : PowerSeries O) ^ M * B.q ^ d * B.q ^ Mi i)`. Rewrite using `[map_pow, hu, mul_pow, mul_pow, ← pow_mul, hd]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[L.φ_semi, this, mul_smul (X ^ M * B.q), mul_smul ((u : PowerSeries O) ^ M * B.q ^ d)]`. Conclude with `smul_mem_sm _ (Submodule.smul_mem _ _ h5')`. Use `⟨key, fun i v hv => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, hw'⟩` from `mem_sm.1 (key i v hv)`. Rewrite using `[← hw', mul_smul]`.

Conclude with `smul_mem_sm _ (Submodule.smul_mem _ _ hw)`.
-/
theorem lattice_filtration_first_form : FrobeniusMapsXPowOf := by
  intro O _ B n _ M V _ _ L Mi h3 h5 hM
  have key : L.FrobeniusMapsXPow M := by
    intro i v hv
    obtain ⟨w, hw, rfl⟩ := mem_sm.1 hv
    obtain ⟨u, hu⟩ := h3
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (hM i)
    have h5' := h5 i w hw
    have : B.φ (X ^ M) = (X ^ M * B.q) * ((u : PowerSeries O) ^ M * B.q ^ d * B.q ^ Mi i) := by
      rw [map_pow, hu, mul_pow, mul_pow, ← pow_mul, hd]
      ring
    rw [L.φ_semi, this, mul_smul (X ^ M * B.q), mul_smul ((u : PowerSeries O) ^ M * B.q ^ d)]
    exact smul_mem_sm _ (Submodule.smul_mem _ _ h5')
  refine ⟨key, fun i v hv => ?_⟩
  obtain ⟨w, hw, hw'⟩ := mem_sm.1 (key i v hv)
  rw [← hw', mul_smul]
  exact smul_mem_sm _ (Submodule.smul_mem _ _ hw)

/- English proof (translation)
Introduce `O _ B n _ V _ _ L c ell hh H h5 hH x hx`. Rewrite using `[mem_dv, prod_split B.p ell hh H hH, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (product_smul_mem_pullback L h5 ell le_rfl hx)`.
-/
theorem pullback_lemma_holds : LatticeLeArcSpan := by
  intro O _ B n _ V _ _ L c ell hh H h5 hH x hx
  rw [mem_dv, prod_split B.p ell hh H hH, mul_smul]
  exact Submodule.smul_mem _ _ (product_smul_mem_pullback L h5 ell le_rfl hx)

namespace GoodPlacesAlt

/- English proof (translation)
Establish `hlD : 0 ≤ lam * D` using `by positivity`. Establish `h1 : lam * D * (lam * a) ≤ lam * D * ((lam + 1) * r)` using `mul_le_mul_of_nonneg_left ha hlD`. Establish `h1' : D * lam ^ 2 * (sg + 1) ≤ D * lam ^ 2 * a` using `mul_le_mul_of_nonneg_left hsa (by positivity)`. Establish `h2 : M ≤ D * (lam * r - y)`. Establish `h3 : (lam + 1) * (y * D + M) ≤ (lam + 1) * (lam * D * r)` using `by nlinarith`.

Use `le_of_mul_le_mul_left h3 (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc : 0 ≤ lam ^ 2 - lam - 1` using `by nlinarith`. Establish `h4 : (lam ^ 2 - lam - 1) * M ≤ (lam ^ 2 - lam - 1) * (D * (lam * r - y))` using `mul_le_mul_of_nonneg_left h2 hc`. Establish `h5 : lam ^ 2 * M ≤ lam ^ 2 * (D * (lam * r - y - a + sg))` using `by nlinarith`.

Conclude with `le_of_mul_le_mul_left h5 (by positivity)`.
-/
theorem tr_arithZ (lam D y M r a sg : ℤ) (hl : 2 ≤ lam) (hD : 1 ≤ D)
    (hs : (y * D + M) * (lam + 1) ≤ sg * (D * lam ^ 2)) (ha : lam * a ≤ (lam + 1) * r)
    (hsa : sg + 1 ≤ a) : M ≤ D * (lam * r - y - a + sg) := by
  have hlD : 0 ≤ lam * D := by positivity
  have h1 : lam * D * (lam * a) ≤ lam * D * ((lam + 1) * r) := mul_le_mul_of_nonneg_left ha hlD
  have h1' : D * lam ^ 2 * (sg + 1) ≤ D * lam ^ 2 * a :=
    mul_le_mul_of_nonneg_left hsa (by positivity)
  have h2 : M ≤ D * (lam * r - y) := by
    have h3 : (lam + 1) * (y * D + M) ≤ (lam + 1) * (lam * D * r) := by nlinarith
    have := le_of_mul_le_mul_left h3 (by linarith)
    linarith
  have hc : 0 ≤ lam ^ 2 - lam - 1 := by nlinarith
  have h4 : (lam ^ 2 - lam - 1) * M ≤ (lam ^ 2 - lam - 1) * (D * (lam * r - y)) :=
    mul_le_mul_of_nonneg_left h2 hc
  have h5 : lam ^ 2 * M ≤ lam ^ 2 * (D * (lam * r - y - a + sg)) := by nlinarith
  exact le_of_mul_le_mul_left h5 (by positivity)

/- English proof (translation)
Take `⟨lam, rfl⟩ : ∃ lam, l = lam + 1` from `⟨l - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel] at hs ha ⊢`. Establish `hz` using `tr_arithZ lam D y M r a sg (by exact_mod_cast (by omega : 2 ≤ lam)) (by exact_mod_cast hD) (by exact_mod_cast hs) (by exact_mod_cast ha) (by exact_mod_cast hsa)`. Establish `hZ : (0 : ℤ) ≤ (lam : ℤ) * r - y - a + sg`. Assume the negation of the conclusion as `hneg`.

Use `replace hneg := not_le.mp hneg`. Establish `: (D : ℤ) * ((lam : ℤ) * r - y - a + sg) < 0` using `mul_neg_of_pos_of_neg (by exact_mod_cast hD) hneg`. Establish `hM : (0 : ℤ) ≤ M` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨e, he⟩` from `Int.eq_ofNat_of_zero_le hZ`.

Use `⟨e, ?_, ?_⟩` and prove the remaining obligations. Establish `: ((lam * r : ℕ) : ℤ) = ((y + ((a - sg) + e) : ℕ) : ℤ)`. Move the coercions through the operations in `[Nat.cast_sub hsa.le]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions.

Rewrite `hz` using `[he]`. Conclude with `hz` after adjusting the coercions.
-/
theorem tr_arithN (l D y M r a sg : ℕ) (hl : 3 ≤ l) (hD : 1 ≤ D)
    (hs : (y * D + M) * l ≤ sg * (D * (l - 1) ^ 2)) (ha : (l - 1) * a ≤ l * r) (hsa : sg < a) :
    ∃ e : ℕ, (l - 1) * r = y + ((a - sg) + e) ∧ M ≤ D * e := by
  obtain ⟨lam, rfl⟩ : ∃ lam, l = lam + 1 := ⟨l - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hs ha ⊢
  have hz := tr_arithZ lam D y M r a sg (by exact_mod_cast (by omega : 2 ≤ lam))
    (by exact_mod_cast hD) (by exact_mod_cast hs) (by exact_mod_cast ha) (by exact_mod_cast hsa)
  have hZ : (0 : ℤ) ≤ (lam : ℤ) * r - y - a + sg := by
    by_contra hneg
    replace hneg := not_le.mp hneg
    have : (D : ℤ) * ((lam : ℤ) * r - y - a + sg) < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast hD) hneg
    have hM : (0 : ℤ) ≤ M := by positivity
    linarith
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le hZ
  refine ⟨e, ?_, ?_⟩
  · have : ((lam * r : ℕ) : ℤ) = ((y + ((a - sg) + e) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hsa.le]
      linarith
    exact_mod_cast this
  · rw [he] at hz
    exact_mod_cast hz

/- English proof (translation)
Establish `h1 : p ^ (t + e) ∈ (Ideal.span {c} ⊔ Ideal.span {x}) ^ (t + e)`. Apply `Ideal.pow_mem_pow` to reduce the goal to its premises. Rewrite using `[← Ideal.span_insert]` and apply the resulting hypothesis. Establish `h2` using `Ideal.sup_pow_add_le_pow_sup_pow h1`. Rewrite `h2` using `[Ideal.span_singleton_pow, Ideal.span_singleton_pow]`.

Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 h2`. Take `⟨α, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Take `⟨β, rfl⟩` from `Ideal.mem_span_singleton'.1 hb`. Conclude with `⟨α, β, by rw [← hab]; ring⟩`.
-/
theorem tr_split {A : Type} [CommRing A] (c x p : A) (hp : p ∈ Ideal.span {c, x}) (t e : ℕ) :
    ∃ α β : A, p ^ (t + e) = c ^ t * α + x ^ e * β := by
  have h1 : p ^ (t + e) ∈ (Ideal.span {c} ⊔ Ideal.span {x}) ^ (t + e) := by
    apply Ideal.pow_mem_pow
    rwa [← Ideal.span_insert]
  have h2 := Ideal.sup_pow_add_le_pow_sup_pow h1
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h2
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h2
  obtain ⟨α, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨β, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  exact ⟨α, β, by rw [← hab]; ring⟩

/- English proof (translation)
Introduce `r a ha`. Distinguish the cases in `hsa : a ≤ sig`. Use `⟨B.lc ^ (sig - a) * ((⇑B.φ)^[j] X) ^ r, ?_⟩` and prove the remaining obligations. Establish `: B.lc ^ sig * ((⇑B.φ)^[j] X) ^ r - B.lc ^ a * (B.lc ^ (sig - a) * ((⇑B.φ)^[j] X) ^ r) = 0`. Rewrite using `[← mul_assoc, ← pow_add, Nat.add_sub_cancel' hsa, sub_self]`.

Rewrite using `[this]`. Conclude with `Ideal.zero_mem _`. Use `replace hsa := not_le.mp hsa`. Take `⟨e, he1, he2⟩` from `tr_arithN B.ℓ (B.ℓ ^ (j - 1)) (3 * g) M r a sig h3 (Nat.one_le_pow _ _ (by omega)) hs ha hsa`. Take `⟨u, hu⟩` from `hE3`.

Take `⟨α, β, hαβ⟩` from `tr_split B.lc (X ^ (B.ℓ ^ (j - 1))) (B.p (j - 1)) hE2 (a - sig) e`. Take `⟨e', he'⟩` from `Nat.exists_eq_add_of_le he2`. Take `⟨j', rfl⟩ : ∃ j', j = j' + 1` from `⟨j - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel] at hαβ he'`. Use `set P : PowerSeries O := ∏ k ∈ Finset.range (j' + 1), B.p k ^ (3 * g) with hP`.

Use `set Q : PowerSeries O := ∏ k ∈ Finset.range j', B.p k ^ ((a - sig) + e) with hQ`. Establish `hprod : (∏ k ∈ Finset.range (j' + 1), B.p k ^ (B.ℓ - 1)) ^ r = P * (Q * B.p j' ^ ((a - sig) + e))`. Rewrite using `[hP, hQ, ← Finset.prod_range_succ (fun k => B.p k ^ ((a - sig) + e)), ← Finset.prod_mul_distrib, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, he1, pow_add]`.

Establish `hXe : ((X : PowerSeries O) ^ (B.ℓ ^ j')) ^ e = X ^ M * X ^ e'`. Rewrite using `[← pow_mul, he', pow_add]`. Establish `hla : B.lc ^ a = B.lc ^ sig * B.lc ^ (a - sig)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hsa.le]`. Use `⟨(u : PowerSeries O) ^ r * X ^ r * P * Q * α, ?_⟩` and prove the remaining obligations.

Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨B.lc ^ sig * (u : PowerSeries O) ^ r * X ^ r * Q * X ^ e' * β, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, mul_pow, mul_pow, hprod, hαβ, hXe, hla, Base.ff, ← hP]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trunc_of {O : Type} [CommRing O] (B : Base O) (j M g sig : ℕ) (h3 : 3 ≤ B.ℓ)
    (hj : 1 ≤ j) (hE3 : B.E3it j) (hE2 : B.E2 (j - 1)) (hs : SigOK B.ℓ j M g sig) :
    B.Trunc j M g sig := by
  intro r a ha
  by_cases hsa : a ≤ sig
  · refine ⟨B.lc ^ (sig - a) * ((⇑B.φ)^[j] X) ^ r, ?_⟩
    have : B.lc ^ sig * ((⇑B.φ)^[j] X) ^ r - B.lc ^ a * (B.lc ^ (sig - a) * ((⇑B.φ)^[j] X) ^ r)
        = 0 := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hsa, sub_self]
    rw [this]
    exact Ideal.zero_mem _
  · replace hsa := not_le.mp hsa
    obtain ⟨e, he1, he2⟩ := tr_arithN B.ℓ (B.ℓ ^ (j - 1)) (3 * g) M r a sig h3
      (Nat.one_le_pow _ _ (by omega)) hs ha hsa
    obtain ⟨u, hu⟩ := hE3
    obtain ⟨α, β, hαβ⟩ := tr_split B.lc (X ^ (B.ℓ ^ (j - 1))) (B.p (j - 1)) hE2 (a - sig) e
    obtain ⟨e', he'⟩ := Nat.exists_eq_add_of_le he2
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hαβ he'
    set P : PowerSeries O := ∏ k ∈ Finset.range (j' + 1), B.p k ^ (3 * g) with hP
    set Q : PowerSeries O := ∏ k ∈ Finset.range j', B.p k ^ ((a - sig) + e) with hQ
    have hprod : (∏ k ∈ Finset.range (j' + 1), B.p k ^ (B.ℓ - 1)) ^ r
        = P * (Q * B.p j' ^ ((a - sig) + e)) := by
      rw [hP, hQ, ← Finset.prod_range_succ (fun k => B.p k ^ ((a - sig) + e)),
        ← Finset.prod_mul_distrib, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← pow_mul, he1, pow_add]
    have hXe : ((X : PowerSeries O) ^ (B.ℓ ^ j')) ^ e = X ^ M * X ^ e' := by
      rw [← pow_mul, he', pow_add]
    have hla : B.lc ^ a = B.lc ^ sig * B.lc ^ (a - sig) := by
      rw [← pow_add, Nat.add_sub_cancel' hsa.le]
    refine ⟨(u : PowerSeries O) ^ r * X ^ r * P * Q * α, ?_⟩
    rw [Ideal.mem_span_singleton']
    refine ⟨B.lc ^ sig * (u : PowerSeries O) ^ r * X ^ r * Q * X ^ e' * β, ?_⟩
    rw [hu, mul_pow, mul_pow, hprod, hαβ, hXe, hla, Base.ff, ← hP]
    ring

/- English proof (translation)
Establish `hC0 : (C ϖ : PowerSeries O) ≠ 0`. Introduce `h0`. Use `congrArg (coeff 0) h0` as an intermediate fact. Rewrite `this` using `[coeff_C, if_pos rfl, map_zero]`. Conclude with `hϖ0 this`.

Proceed by induction on `N with`. Consider the case `zero => intro z hz`. Simplify using `using hz`. Consider the case `succ N ih`. Introduce `z hz`.

Apply `ih` to reduce the goal to its premises. Rewrite `hz`, the goal using `[Ideal.mem_span_singleton]`. Take `⟨w, hw⟩` from `hz`. Establish `hdvd : C ϖ ∣ f * w` using `⟨C (ϖ ^ N) * z, by rw [← hw, pow_succ, map_mul]; ring⟩`. Take `⟨w', rfl⟩` from `Formalism.ExponentWindows.C_dvd_of_C_dvd_mul ϖ f w hf hdvd`.

Use `⟨w', ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hC0` to reduce the goal to its premises. Rewrite `hw` using `[pow_succ, map_mul]`. Take the linear combination `hw`.
-/
theorem sa_sat {O : Type} [CommRing O] [IsDomain O] (ϖ : O) [(Ideal.span {ϖ}).IsMaximal]
    (hϖ0 : ϖ ≠ 0) (f : PowerSeries O)
    (hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f ≠ 0) (N : ℕ) :
    ∀ z : PowerSeries O, C (ϖ ^ N) * z ∈ Ideal.span {f} → z ∈ Ideal.span {f} := by
  have hC0 : (C ϖ : PowerSeries O) ≠ 0 := by
    intro h0
    have := congrArg (coeff 0) h0
    rw [coeff_C, if_pos rfl, map_zero] at this
    exact hϖ0 this
  induction N with
  | zero => intro z hz; simpa using hz
  | succ N ih =>
    intro z hz
    apply ih
    rw [Ideal.mem_span_singleton] at hz ⊢
    obtain ⟨w, hw⟩ := hz
    have hdvd : C ϖ ∣ f * w := ⟨C (ϖ ^ N) * z, by rw [← hw, pow_succ, map_mul]; ring⟩
    obtain ⟨w', rfl⟩ := Formalism.ExponentWindows.C_dvd_of_C_dvd_mul ϖ f w hf hdvd
    refine ⟨w', ?_⟩
    apply mul_left_cancel₀ hC0
    rw [pow_succ, map_mul] at hw
    linear_combination hw

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_add]`.
-/
theorem sa_it_add {O : Type} [CommRing O] (f : PowerSeries O →ₐ[O] PowerSeries O) (k : ℕ)
    (a b : PowerSeries O) : (⇑f)^[k] (a + b) = (⇑f)^[k] a + (⇑f)^[k] b := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_add]

/- English proof (translation)
Establish `: IsDomain (O ⧸ Ideal.span {ϖ})` using `Ideal.Quotient.isDomain _`. Proceed by induction on `s using Nat.strong_induction_on with`. Consider the case `_ s ih`. Take `⟨u, hu⟩` from `hE3 s`. Establish `hl : Ideal.Quotient.mk (Ideal.span {ϖ}) (B.ℓ : O) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)`.

Establish `hp : B.p s = (u : PowerSeries O) * X * ∏ k ∈ Finset.range s, B.p k ^ (B.ℓ - 1) + C (B.ℓ : O)`. Rewrite using `[Base.p, Base.q, sa_it_add, IdempotentNormalFormsRhoFacts.it_C, hu]`. Rewrite using `[hp, map_add, PowerSeries.map_C, hl, map_zero, add_zero, map_mul, map_mul, map_prod, PowerSeries.map_X]`. Use `mul_ne_zero (mul_ne_zero ?_ X_ne_zero) ?_` and prove the remaining obligations. Conclude with `(u.isUnit.map (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})))).ne_zero`.

Use `Finset.prod_ne_zero_iff.mpr fun k hk => ?_` and prove the remaining obligations. Rewrite using `[map_pow]`. Conclude with `pow_ne_zero _ (ih k (Finset.mem_range.mp hk))`.
-/
theorem sa_p_ne {O : Type} [CommRing O] [IsDomain O] (ϖ : O) [(Ideal.span {ϖ}).IsMaximal]
    (B : Base O) (hd : ϖ ∣ (B.ℓ : O)) (hE3 : ∀ s, B.E3it s) (s : ℕ) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (B.p s) ≠ 0 := by
  have : IsDomain (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.isDomain _
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    obtain ⟨u, hu⟩ := hE3 s
    have hl : Ideal.Quotient.mk (Ideal.span {ϖ}) (B.ℓ : O) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)
    have hp : B.p s = (u : PowerSeries O) * X * ∏ k ∈ Finset.range s, B.p k ^ (B.ℓ - 1)
        + C (B.ℓ : O) := by
      rw [Base.p, Base.q, sa_it_add, IdempotentNormalFormsRhoFacts.it_C, hu]
    rw [hp, map_add, PowerSeries.map_C, hl, map_zero, add_zero, map_mul, map_mul, map_prod,
      PowerSeries.map_X]
    refine mul_ne_zero (mul_ne_zero ?_ X_ne_zero) ?_
    · exact (u.isUnit.map (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})))).ne_zero
    · refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
      rw [map_pow]
      exact pow_ne_zero _ (ih k (Finset.mem_range.mp hk))

/- English proof (translation)
Establish `: (Ideal.span {ϖ}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible hϖ`. Establish `: IsDomain (O ⧸ Ideal.span {ϖ})` using `Ideal.Quotient.isDomain _`. Establish `hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (B.ff j M g) ≠ 0`. Rewrite using `[Base.ff, map_mul, map_pow, PowerSeries.map_X, map_prod]`. Use `mul_ne_zero (pow_ne_zero _ X_ne_zero) (Finset.prod_ne_zero_iff.mpr fun k _ => ?_)` and prove the remaining obligations.

Rewrite using `[map_pow]`. Conclude with `pow_ne_zero _ (sa_p_ne ϖ B hd hE3 k)`. Introduce `K a ha`. Take `⟨e, he⟩` from `IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ`. Take `⟨w, hw⟩` from `he`.

Establish `h1 : C (ϖ ^ (e * K)) * a ∈ Ideal.span {B.ff j M g}`. Establish `: (C (ϖ ^ (e * K)) : PowerSeries O) * a = C ((w : O) ^ K) * (B.lc ^ K * a)`. Rewrite using `[pow_mul, ← hw, mul_pow, IdempotentNormalFormsRhoFacts.lc_pow, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `Ideal.mul_mem_left _ _ ha`. Conclude with `sa_sat ϖ hϖ.ne_zero _ hf _ a h1`.
-/
theorem satA_of {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (B : Base O) (j M g : ℕ) (hϖ : Irreducible ϖ) (hd : ϖ ∣ (B.ℓ : O)) (h0 : (B.ℓ : O) ≠ 0)
    (hE3 : ∀ s, B.E3it s) : B.Sat (B.ff j M g) := by
  have : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  have : IsDomain (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.isDomain _
  have hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (B.ff j M g) ≠ 0 := by
    rw [Base.ff, map_mul, map_pow, PowerSeries.map_X, map_prod]
    refine mul_ne_zero (pow_ne_zero _ X_ne_zero) (Finset.prod_ne_zero_iff.mpr fun k _ => ?_)
    rw [map_pow]
    exact pow_ne_zero _ (sa_p_ne ϖ B hd hE3 k)
  intro K a ha
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ
  obtain ⟨w, hw⟩ := he

  have h1 : C (ϖ ^ (e * K)) * a ∈ Ideal.span {B.ff j M g} := by
    have : (C (ϖ ^ (e * K)) : PowerSeries O) * a = C ((w : O) ^ K) * (B.lc ^ K * a) := by
      rw [pow_mul, ← hw, mul_pow, IdempotentNormalFormsRhoFacts.lc_pow, map_mul]
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ ha
  exact sa_sat ϖ hϖ.ne_zero _ hf _ a h1

end GoodPlacesAlt

namespace GoodPlacesAlt

open IdempotentNormalFormsRhoFacts

section sat
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] (L : Lat B n V)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Establish `hv' : v ∈ Submodule.span (PowerSeries O) (Set.range e)` using `by rw [he]; exact hv`. Proceed by induction on `hv' using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨a, rfl⟩`. Consider the case `zero => rw [phiIt_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y hx hy ihx ihy`. Rewrite using `[phiIt_add]`. Conclude with `Submodule.add_mem _ (ihx (by rw [← he]; exact hx)) (ihy (by rw [← he]; exact hy))`. Consider the case `smul a x hx ihx`. Rewrite using `[phiIt_smul]`.

Conclude with `Submodule.smul_mem _ _ (ihx (by rw [← he]; exact hx))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `phiIt_mem_pull L k (by rw [← he]; exact Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem sat_pull_eq {c : ZMod n} {k r : ℕ} {e : Fin r → V}
    (he : Submodule.span (PowerSeries O) (Set.range e) = L.N c) :
    L.pull c k = Submodule.span (PowerSeries O) (Set.range fun a => L.phiIt c k (e a)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ Submodule.span (PowerSeries O) (Set.range e) := by rw [he]; exact hv
    induction hv' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span ⟨a, rfl⟩
    | zero => rw [phiIt_zero]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      rw [phiIt_add]
      exact Submodule.add_mem _ (ihx (by rw [← he]; exact hx)) (ihy (by rw [← he]; exact hy))
    | smul a x hx ihx =>
      rw [phiIt_smul]
      exact Submodule.smul_mem _ _ (ihx (by rw [← he]; exact hx))
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact phiIt_mem_pull L k (by rw [← he]; exact Submodule.subset_span ⟨a, rfl⟩)

def satP (i : ZMod n) (k : ℕ) {r : ℕ} (b : Fin r → PowerSeries O) (x : V) : Prop :=
  ∃ m : Fin r → V, (∀ t, m t ∈ L.N i) ∧ x = ∑ t, b t • L.phiIt i k (m t)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => 0, fun _ => Submodule.zero_mem _, by simp [phiIt_zero]⟩`.
-/
theorem isPhiCombination_zero (i : ZMod n) (k : ℕ) {r : ℕ} (b : Fin r → PowerSeries O) :
    satP L i k b 0 :=
  ⟨fun _ => 0, fun _ => Submodule.zero_mem _, by simp [phiIt_zero]⟩

/- English proof (translation)
Take `⟨m, hm, rfl⟩` from `hx`. Take `⟨m', hm', rfl⟩` from `hy`. Use `⟨fun t => m t + m' t, fun t => Submodule.add_mem _ (hm t) (hm' t), ?_⟩` and prove the remaining obligations. Simplify using `only [phiIt_add, smul_add, Finset.sum_add_distrib]`.
-/
theorem isPhiCombination_add {i : ZMod n} {k : ℕ} {r : ℕ} {b : Fin r → PowerSeries O} {x y : V}
    (hx : satP L i k b x) (hy : satP L i k b y) : satP L i k b (x + y) := by
  obtain ⟨m, hm, rfl⟩ := hx
  obtain ⟨m', hm', rfl⟩ := hy
  refine ⟨fun t => m t + m' t, fun t => Submodule.add_mem _ (hm t) (hm' t), ?_⟩
  simp only [phiIt_add, smul_add, Finset.sum_add_distrib]

/- English proof (translation)
Take `⟨a', ha'⟩` from `hb a`. Use `⟨fun t => a' t • v, fun t => Submodule.smul_mem _ _ hv, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [ha']`. Simplify using `only [phiIt_smul, Finset.sum_smul, mul_smul]`.
-/
theorem isPhiCombination_smul_phiIterate {i : ZMod n} {k : ℕ} {r : ℕ} {b : Fin r → PowerSeries O}
    (hb : ∀ a : PowerSeries O, ∃ a' : Fin r → PowerSeries O, a = ∑ t, b t * (⇑B.φ)^[k] (a' t))
    (a : PowerSeries O) {v : V} (hv : v ∈ L.N i) : satP L i k b (a • L.phiIt i k v) := by
  obtain ⟨a', ha'⟩ := hb a
  refine ⟨fun t => a' t • v, fun t => Submodule.smul_mem _ _ hv, ?_⟩
  conv_lhs => rw [ha']
  simp only [phiIt_smul, Finset.sum_smul, mul_smul]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, hv, rfl⟩` from `hx`. Simplify using `using isPhiCombination_smul_phiIterate L hb 1 hv`. Consider the case `zero => exact isPhiCombination_zero L i k b`.

Consider the case `add x y _ _ hx hy => exact isPhiCombination_add L hx hy`. Consider the case `smul a x _ hx`. Take `⟨m, hm, rfl⟩` from `hx`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_induction _ (satP L i k b) (fun _ _ => isPhiCombination_add L) (isPhiCombination_zero L i k b) ?_` and prove the remaining obligations.

Introduce `t _`. Rewrite using `[smul_smul]`. Conclude with `isPhiCombination_smul_phiIterate L hb _ (hm t)`.
-/
theorem isPhiCombination_of_mem_pull {i : ZMod n} {k : ℕ} {r : ℕ} {b : Fin r → PowerSeries O}
    (hb : ∀ a : PowerSeries O, ∃ a' : Fin r → PowerSeries O, a = ∑ t, b t * (⇑B.φ)^[k] (a' t))
    {x : V} (hx : x ∈ L.pull i k) : satP L i k b x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    simpa using isPhiCombination_smul_phiIterate L hb 1 hv
  | zero => exact isPhiCombination_zero L i k b
  | add x y _ _ hx hy => exact isPhiCombination_add L hx hy
  | smul a x _ hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [Finset.smul_sum]
    refine Finset.sum_induction _ (satP L i k b) (fun _ _ => isPhiCombination_add L) (isPhiCombination_zero L i k b) ?_
    intro t _
    rw [smul_smul]
    exact isPhiCombination_smul_phiIterate L hb _ (hm t)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using h0`. Consider the case `succ k ih`. Apply `ih` to reduce the goal to its premises. Apply `h i _ (Submodule.smul_mem _ _ hv)` to reduce the goal to its premises.

Rewrite using `[smul_smul, ← pow_succ']`. Conclude with `h0`.
-/
theorem sat_xreg_pow (h : L.XReg) (i : ZMod n) (k : ℕ) {v : V} (hv : v ∈ L.N i)
    (h0 : (X : PowerSeries O) ^ k • v = 0) : v = 0 := by
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    apply ih
    apply h i _ (Submodule.smul_mem _ _ hv)
    rw [smul_smul, ← pow_succ']
    exact h0

end sat

end GoodPlacesAlt

open GoodPlacesAlt IdempotentNormalFormsRhoFacts

/- English proof (translation)
Introduce `O _ B n _ j f V _ _ L c hS hF K v hv hKv`. Take `⟨r, e, he, hLI⟩` from `hF`. Rewrite `hv`, `hKv`, the goal using `[sat_pull_eq L he]`. Take `⟨w, hw, hwe⟩` from `mem_sm.1 hKv`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hv`.

Take `⟨d, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hw`. Establish `hz : ∑ t, (B.lc ^ K * a t - f * d t) • L.phiIt c j (e t) = 0`. Simplify using `only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]`. Rewrite using `[hwe, sub_self]`. Establish `hco` using `Fintype.linearIndependent_iff.1 hLI _ hz`.

Establish `hdiv : ∀ t, ∃ q : PowerSeries O, a t = f * q`. Introduce `t`. Establish `h1 : B.lc ^ K * a t ∈ Ideal.span {f}`. Rewrite using `[sub_eq_zero.1 (hco t)]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)`.

Take `⟨q, hq⟩` from `Ideal.mem_span_singleton'.1 (hS K _ h1)`. Conclude with `⟨q, by rw [← hq, mul_comm]⟩`. Use `choose q hq using hdiv`. Use `mem_sm.2 ⟨∑ t, q t • L.phiIt c j (e t), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Submodule.mem_span_range_iff_exists_fun _).2 ⟨q, rfl⟩`.

Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← hq t]`.
-/
theorem saturation_holds_alt : SatOf := by
  intro O _ B n _ j f V _ _ L c hS hF K v hv hKv
  obtain ⟨r, e, he, hLI⟩ := hF
  rw [sat_pull_eq L he] at hv hKv ⊢
  obtain ⟨w, hw, hwe⟩ := mem_sm.1 hKv
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hw
  have hz : ∑ t, (B.lc ^ K * a t - f * d t) • L.phiIt c j (e t) = 0 := by
    simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
    rw [hwe, sub_self]
  have hco := Fintype.linearIndependent_iff.1 hLI _ hz
  have hdiv : ∀ t, ∃ q : PowerSeries O, a t = f * q := by
    intro t
    have h1 : B.lc ^ K * a t ∈ Ideal.span {f} := by
      rw [sub_eq_zero.1 (hco t)]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 (hS K _ h1)
    exact ⟨q, by rw [← hq, mul_comm]⟩
  choose q hq using hdiv
  refine mem_sm.2 ⟨∑ t, q t • L.phiIt c j (e t), ?_, ?_⟩
  · exact (Submodule.mem_span_range_iff_exists_fun _).2 ⟨q, rfl⟩
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_smul, ← hq t]

/- English proof (translation)
Introduce `O _ B n _ V₂ V₀ _ _ _ _ L₂ L₀ Y h6 hX i k u hu`. Take `⟨y, hy, hyu⟩` from `mem_sm.1 hu`. Establish `hπ : Y.π.f y = 0`. Apply `sat_xreg_pow L₀ hX i k (Y.π.map_N i y hy)` to reduce the goal to its premises. Rewrite using `[← map_smul, hyu]`.

Conclude with `(Y.exact _).2 ⟨u, rfl⟩`. Take `⟨u', rfl⟩` from `(Y.exact _).1 hπ`. Use `mem_sm.2 ⟨u', h6 i u' hy, ?_⟩` and prove the remaining obligations. Apply `Y.ι_inj` to reduce the goal to its premises. Rewrite using `[map_smul, hyu]`.
-/
theorem extension_complete_holds : ExtCOf := by
  intro O _ B n _ V₂ V₀ _ _ _ _ L₂ L₀ Y h6 hX i k u hu
  obtain ⟨y, hy, hyu⟩ := mem_sm.1 hu
  have hπ : Y.π.f y = 0 := by
    apply sat_xreg_pow L₀ hX i k (Y.π.map_N i y hy)
    rw [← map_smul, hyu]
    exact (Y.exact _).2 ⟨u, rfl⟩
  obtain ⟨u', rfl⟩ := (Y.exact _).1 hπ
  refine mem_sm.2 ⟨u', h6 i u' hy, ?_⟩
  apply Y.ι_inj
  rw [map_smul, hyu]

/- English proof (translation)
Introduce `O _ B n _ V₂ V₀ _ _ _ _ L₂ L₀ Y i k lam h6 hF u hu`. Take `⟨r, b, hb, hind⟩` from `hF`. Establish `hu' : Y.ι.f (lam • u) ∈ Y.LY.pull i k`. Rewrite using `[map_smul]`. Conclude with `hu`.

Take `⟨m, hm, hme⟩` from `isPhiCombination_of_mem_pull Y.LY hb hu'`. Establish `h0 : ∑ t, b t • L₀.phiIt i k (Y.π.f (m t)) = 0`. Establish `h1 : Y.π.f (Y.ι.f (lam • u)) = 0` using `(Y.exact _).2 ⟨_, rfl⟩`. Rewrite `h1` using `[hme, map_sum]`. Simplify `h1` using `only [map_smul, hom_phiIt]`.

Establish `hm0` using `hind (fun t => Y.π.f (m t)) (fun t => Y.π.map_N i _ (hm t)) h0`. Establish `hex : ∀ t, ∃ w : V₂, Y.ι.f w = m t` using `fun t => (Y.exact _).1 (hm0 t)`. Use `choose w hw using hex`. Establish `hwN : ∀ t, w t ∈ L₂.N i` using `fun t => h6 i (w t) (by rw [hw t]; exact hm t)`. Establish `heq : lam • u = ∑ t, b t • L₂.phiIt i k (w t)`.

Apply `Y.ι_inj` to reduce the goal to its premises. Rewrite using `[hme, map_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hom_phiIt, hw t]`. Use `show lam • u ∈ L₂.pull i k`.

Rewrite using `[heq]`. Conclude with `Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (phiIt_mem_pull L₂ k (hwN t))`.
-/
theorem extension_generated_holds : ExtGOf := by
  intro O _ B n _ V₂ V₀ _ _ _ _ L₂ L₀ Y i k lam h6 hF u hu
  obtain ⟨r, b, hb, hind⟩ := hF
  have hu' : Y.ι.f (lam • u) ∈ Y.LY.pull i k := by
    rw [map_smul]
    exact hu
  obtain ⟨m, hm, hme⟩ := isPhiCombination_of_mem_pull Y.LY hb hu'
  have h0 : ∑ t, b t • L₀.phiIt i k (Y.π.f (m t)) = 0 := by
    have h1 : Y.π.f (Y.ι.f (lam • u)) = 0 := (Y.exact _).2 ⟨_, rfl⟩
    rw [hme, map_sum] at h1
    simpa only [map_smul, hom_phiIt] using h1
  have hm0 := hind (fun t => Y.π.f (m t)) (fun t => Y.π.map_N i _ (hm t)) h0
  have hex : ∀ t, ∃ w : V₂, Y.ι.f w = m t := fun t => (Y.exact _).1 (hm0 t)
  choose w hw using hex
  have hwN : ∀ t, w t ∈ L₂.N i := fun t => h6 i (w t) (by rw [hw t]; exact hm t)
  have heq : lam • u = ∑ t, b t • L₂.phiIt i k (w t) := by
    apply Y.ι_inj
    rw [hme, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_smul, hom_phiIt, hw t]
  show lam • u ∈ L₂.pull i k
  rw [heq]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (phiIt_mem_pull L₂ k (hwN t))

namespace GoodPlacesAlt

open IdempotentNormalFormsRhoFacts

section hh
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] (L : Lat B n V)

/- English proof (translation)
Introduce `v hv`. Take `⟨u, hu, rfl⟩` from `mem_sm.1 hv`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le h`. Rewrite using `[pow_add, mul_smul]`. Conclude with `smul_mem_sm _ (S.smul_mem _ hu)`.
-/
theorem hh_sm_pow_mono {S : Submodule (PowerSeries O) V} {m M : ℕ} (h : m ≤ M) :
    sm ((X : PowerSeries O) ^ M) S ≤ sm (X ^ m) S := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := mem_sm.1 hv
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, mul_smul]
  exact smul_mem_sm _ (S.smul_mem _ hu)

/- English proof (translation)
Take `⟨a, ha⟩` from `hu`. Take `⟨x', hx', hxx⟩` from `mem_sm.1 (h9 c x hx)`. Establish `hγx : L.γ c x = x + (X : PowerSeries O) • x'` using `by rw [hxx]; abel`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, (C u₁ + X * a) ^ r = C (u₁ ^ r) + X * b := by`. Take `⟨d, hd⟩` from `sub_dvd_pow_sub_pow (C u₁ + X * a) (C u₁) r`.

Use `⟨a * d, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow]`. Take the linear combination `hd`. Establish `: L.γ c ((X : PowerSeries O) ^ r • x) - C (u₁ ^ r) • (X : PowerSeries O) ^ r • x = (X : PowerSeries O) ^ (r + 1) • (b • x + C (u₁ ^ r) • x' + (X * b) • x')`. Rewrite using `[L.γ_semi, map_pow, ha, mul_pow, hb, hγx]`.

Establish `e1 : (X : PowerSeries O) ^ r * (C (u₁ ^ r) + X * b) = C (u₁ ^ r) * X ^ r + X ^ (r + 1) * b`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (X : PowerSeries O) ^ r * (C (u₁ ^ r) + X * b) * X = X ^ (r + 1) * C (u₁ ^ r) + X ^ (r + 1) * (X * b)` using `by ring`. Rewrite using `[smul_add, smul_smul _ X, e2, e1, add_smul, add_smul, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[this]`. Conclude with `smul_mem_sm _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.smul_mem _ _ hx')) (Submodule.smul_mem _ _ hx'))`.
-/
theorem hh_gr {u₁ : O} (hu : ∃ a : PowerSeries O, B.γ X = X * (C u₁ + X * a)) (h9 : L.P9)
    (c : ZMod n) (r : ℕ) {x : V} (hx : x ∈ L.N c) :
    L.γ c ((X : PowerSeries O) ^ r • x) - C (u₁ ^ r) • (X : PowerSeries O) ^ r • x ∈
      sm (X ^ (r + 1)) (L.N c) := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨x', hx', hxx⟩ := mem_sm.1 (h9 c x hx)
  have hγx : L.γ c x = x + (X : PowerSeries O) • x' := by rw [hxx]; abel
  obtain ⟨b, hb⟩ : ∃ b, (C u₁ + X * a) ^ r = C (u₁ ^ r) + X * b := by
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (C u₁ + X * a) (C u₁) r
    refine ⟨a * d, ?_⟩
    rw [map_pow]
    linear_combination hd
  have : L.γ c ((X : PowerSeries O) ^ r • x) - C (u₁ ^ r) • (X : PowerSeries O) ^ r • x =
      (X : PowerSeries O) ^ (r + 1) • (b • x + C (u₁ ^ r) • x' + (X * b) • x') := by
    rw [L.γ_semi, map_pow, ha, mul_pow, hb, hγx]
    have e1 : (X : PowerSeries O) ^ r * (C (u₁ ^ r) + X * b) = C (u₁ ^ r) * X ^ r + X ^ (r + 1) * b := by
      ring
    have e2 : (X : PowerSeries O) ^ r * (C (u₁ ^ r) + X * b) * X =
        X ^ (r + 1) * C (u₁ ^ r) + X ^ (r + 1) * (X * b) := by ring
    rw [smul_add, smul_smul _ X, e2, e1, add_smul, add_smul, smul_add, smul_add, smul_smul,
      smul_smul, smul_smul, smul_smul]
    abel
  rw [this]
  exact smul_mem_sm _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hx)
    (Submodule.smul_mem _ _ hx')) (Submodule.smul_mem _ _ hx'))

def hhA (ℓ : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => hhA ℓ r + (1 + padicValNat ℓ (r + 1))

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => simp [hhA]`. Consider the case `succ r ih`. Rewrite using `[hhA, ih, Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero r)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem hhA_eq (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) : hhA ℓ r = r + padicValNat ℓ r.factorial := by
  induction r with
  | zero => simp [hhA]
  | succ r ih =>
    rw [hhA, ih, Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero r)]
    omega

/- English proof (translation)
Use `Fact.mk hℓ` as an intermediate fact. Rewrite using `[hhA_eq, mul_add, sub_one_mul_padicValNat_factorial]`. Establish `h1 : 1 ≤ ℓ` using `hℓ.one_le`. Take `⟨t, rfl⟩ : ∃ t, ℓ = t + 1` from `⟨ℓ - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`.

Establish `h2 : (t + 1) * r = t * r + r` using `by ring`. Use linear arithmetic over natural numbers and integers.
-/
theorem hhA_le (ℓ : ℕ) (hℓ : ℓ.Prime) (r : ℕ) : (ℓ - 1) * hhA ℓ r ≤ ℓ * r := by
  have := Fact.mk hℓ
  rw [hhA_eq, mul_add, sub_one_mul_padicValNat_factorial]
  have h1 : 1 ≤ ℓ := hℓ.one_le
  obtain ⟨t, rfl⟩ : ∃ t, ℓ = t + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h2 : (t + 1) * r = t * r + r := by ring
  omega

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [phiIt_zero]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, phiIt_add, ih]`.
-/
theorem hh_phiIt_sum (i : ZMod n) (k : ℕ) {ι : Type} (s : Finset ι) (f : ι → V) :
    L.phiIt i k (∑ r ∈ s, f r) = ∑ r ∈ s, L.phiIt i k (f r) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phiIt_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, phiIt_add, ih]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Use `⟨fun _ => 0, fun _ => 0, fun r h1 h2 => by omega, ?_⟩` and prove the remaining obligations. Simplify `hz` using `[hhA]`. Consider the case `succ k ih`.

Take `⟨b, d, hbd, hres⟩` from `ih`. Use `set v := ∑ r ∈ Finset.Ico 1 (k + 1), (B.lc ^ b r * X ^ r) • d r with hv`. Take `⟨ρ, hρ, hρe⟩` from `mem_sm.1 hres`. Take `⟨ε, hε⟩` from `hE.2 (k + 1) (by omega)`. Use `set e := 1 + padicValNat B.ℓ (k + 1) with he`.

Use `set εi : O := ((ε⁻¹ : Oˣ) : O) with hεi`. Establish `hρ' : -(C εi • ρ) ∈ L.N c` using `Submodule.neg_mem _ (Submodule.smul_mem _ _ hρ)`. Use `⟨fun r => if r = k + 1 then 0 else b r + e, fun r => if r = k + 1 then -(C εi • ρ) else d r, ?_, ?_⟩` and prove the remaining obligations. Introduce `r h1 h2`. Distinguish the cases in `hr : r = k + 1`.

Substitute `hr` using the available equality. Simplify using `using hρ'`. Simplify using `only [if_neg hr]`. Take `⟨h3, h4⟩` from `hbd r h1 (by omega)`. Use `⟨?_, h4⟩` and prove the remaining obligations.

Rewrite using `[hhA]`. Use linear arithmetic over natural numbers and integers. Establish `hsum : ∑ r ∈ Finset.Ico 1 (k + 1 + 1), (B.lc ^ (if r = k + 1 then 0 else b r + e) * X ^ r) • (if r = k + 1 then -(C εi • ρ) else d r) = B.lc ^ e • v + (X : PowerSeries O) ^ (k + 1) • (-(C εi • ρ))`. Rewrite using `[Finset.sum_Ico_succ_top (by omega)]`. Use `congr 1`.

Rewrite using `[hv, Finset.smul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `r hr`. Establish `hne : r ≠ k + 1`. Use `Finset.mem_Ico.1 hr` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using `only [if_neg hne]`. Rewrite using `[smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Rewrite using `[hsum]`. Take `⟨w, hw, hwe⟩` from `mem_sm.1 (hh_gr L hE.1 h9 c (k + 1) hρ)`. Establish `hγ' : L.γ c ((X : PowerSeries O) ^ (k + 1) • (-(C εi • ρ))) = -(C εi • L.γ c ((X : PowerSeries O) ^ (k + 1) • ρ))`. Rewrite using `[smul_neg, map_neg, smul_comm, γ_C]`.

Establish `hc : (C εi : PowerSeries O) * (C (u₁ ^ (k + 1)) - 1) = B.lc ^ e`. Rewrite using `[lc_pow, ← map_one (C (R := O)), ← map_sub, ← map_mul, hε, ← mul_assoc, hεi, Units.inv_mul, one_mul]`. Establish `hP : ((C εi : PowerSeries O) * (C (u₁ ^ (k + 1)) - 1)) • (X : PowerSeries O) ^ (k + 1) • ρ = B.lc ^ e • (X : PowerSeries O) ^ (k + 1) • ρ` using `by rw [hc]`. Establish `hfin : (L.γ c (B.lc ^ e • v + (X : PowerSeries O) ^ (k + 1) • (-(C εi • ρ))) - (B.lc ^ e • v + (X : PowerSeries O) ^ (k + 1) • (-(C εi • ρ)))) - B.lc ^ hhA B.ℓ (k + 1) • z = (X : PowerSeries O) ^ (k + 1 + 1) • (-(C εi • w))`. Establish `hG : L.γ c ((X : PowerSeries O) ^ (k + 1) • ρ) = (X : PowerSeries O) ^ (k + 1 + 1) • w + C (u₁ ^ (k + 1)) • (X : PowerSeries O) ^ (k + 1) • ρ` using `by rw [hwe]; abel`.

Establish `hγv : L.γ c v = (X : PowerSeries O) ^ (k + 1) • ρ + v + B.lc ^ hhA B.ℓ k • z`. Rewrite using `[hρe]`. Normalize the expressions using the abelian group laws. Establish `hP' : B.lc ^ e • (X : PowerSeries O) ^ (k + 1) • ρ = C εi • C (u₁ ^ (k + 1)) • (X : PowerSeries O) ^ (k + 1) • ρ - C εi • (X : PowerSeries O) ^ (k + 1) • ρ`. Rewrite using `[← hP, mul_sub, mul_one, sub_smul, mul_smul]`.

Establish `hA : hhA B.ℓ (k + 1) = hhA B.ℓ k + e` using `rfl`. Rewrite using `[map_add, γ_lc, hγ', hA, pow_add B.lc (hhA B.ℓ k) e, hG, hγv, smul_neg, smul_comm _ (C εi) ρ, smul_add, smul_add, hP']`. Generalize the expression as in `(X : PowerSeries O) ^ (k + 1) • ρ = P`. Simplify using `only [smul_add, smul_neg, smul_smul, mul_comm]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hfin]`. Conclude with `smul_mem_sm _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ hw))`.
-/
theorem hh_main {u₁ : O} (hE : B.GammaXUnitShape u₁) (h9 : L.P9) (c : ZMod n) {z : V}
    (hz : z ∈ sm X (L.N c)) (k : ℕ) :
    ∃ (b : ℕ → ℕ) (d : ℕ → V),
      (∀ r, 1 ≤ r → r ≤ k → hhA B.ℓ r + b r = hhA B.ℓ k ∧ d r ∈ L.N c) ∧
      (L.γ c (∑ r ∈ Finset.Ico 1 (k + 1), (B.lc ^ b r * X ^ r) • d r) -
        ∑ r ∈ Finset.Ico 1 (k + 1), (B.lc ^ b r * X ^ r) • d r) - B.lc ^ hhA B.ℓ k • z ∈
        sm (X ^ (k + 1)) (L.N c) := by
  induction k with
  | zero =>
    refine ⟨fun _ => 0, fun _ => 0, fun r h1 h2 => by omega, ?_⟩
    simpa [hhA] using hz
  | succ k ih =>
    obtain ⟨b, d, hbd, hres⟩ := ih
    set v := ∑ r ∈ Finset.Ico 1 (k + 1), (B.lc ^ b r * X ^ r) • d r with hv
    obtain ⟨ρ, hρ, hρe⟩ := mem_sm.1 hres
    obtain ⟨ε, hε⟩ := hE.2 (k + 1) (by omega)
    set e := 1 + padicValNat B.ℓ (k + 1) with he
    set εi : O := ((ε⁻¹ : Oˣ) : O) with hεi
    have hρ' : -(C εi • ρ) ∈ L.N c := Submodule.neg_mem _ (Submodule.smul_mem _ _ hρ)
    refine ⟨fun r => if r = k + 1 then 0 else b r + e,
      fun r => if r = k + 1 then -(C εi • ρ) else d r, ?_, ?_⟩
    · intro r h1 h2
      by_cases hr : r = k + 1
      · subst hr
        simpa using hρ'
      · simp only [if_neg hr]
        obtain ⟨h3, h4⟩ := hbd r h1 (by omega)
        refine ⟨?_, h4⟩
        rw [hhA]
        omega
    · have hsum : ∑ r ∈ Finset.Ico 1 (k + 1 + 1),
          (B.lc ^ (if r = k + 1 then 0 else b r + e) * X ^ r) •
            (if r = k + 1 then -(C εi • ρ) else d r) =
          B.lc ^ e • v + (X : PowerSeries O) ^ (k + 1) • (-(C εi • ρ)) := by
        rw [Finset.sum_Ico_succ_top (by omega)]
        congr 1
        · rw [hv, Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          have hne : r ≠ k + 1 := by
            have := Finset.mem_Ico.1 hr
            omega
          simp only [if_neg hne]
          rw [smul_smul]
          congr 1
          ring
        · simp
      rw [hsum]
      obtain ⟨w, hw, hwe⟩ := mem_sm.1 (hh_gr L hE.1 h9 c (k + 1) hρ)
      have hγ' : L.γ c ((X : PowerSeries O) ^ (k + 1) • (-(C εi • ρ))) =
          -(C εi • L.γ c ((X : PowerSeries O) ^ (k + 1) • ρ)) := by
        rw [smul_neg, map_neg, smul_comm, γ_C]
      have hc : (C εi : PowerSeries O) * (C (u₁ ^ (k + 1)) - 1) = B.lc ^ e := by
        rw [lc_pow, ← map_one (C (R := O)), ← map_sub, ← map_mul, hε, ← mul_assoc, hεi,
          Units.inv_mul, one_mul]
      have hP : ((C εi : PowerSeries O) * (C (u₁ ^ (k + 1)) - 1)) • (X : PowerSeries O) ^ (k + 1) • ρ
          = B.lc ^ e • (X : PowerSeries O) ^ (k + 1) • ρ := by rw [hc]
      have hfin : (L.γ c (B.lc ^ e • v + (X : PowerSeries O) ^ (k + 1) • (-(C εi • ρ))) -
          (B.lc ^ e • v + (X : PowerSeries O) ^ (k + 1) • (-(C εi • ρ)))) -
          B.lc ^ hhA B.ℓ (k + 1) • z = (X : PowerSeries O) ^ (k + 1 + 1) • (-(C εi • w)) := by
        have hG : L.γ c ((X : PowerSeries O) ^ (k + 1) • ρ) = (X : PowerSeries O) ^ (k + 1 + 1) • w +
            C (u₁ ^ (k + 1)) • (X : PowerSeries O) ^ (k + 1) • ρ := by rw [hwe]; abel
        have hγv : L.γ c v = (X : PowerSeries O) ^ (k + 1) • ρ + v + B.lc ^ hhA B.ℓ k • z := by
          rw [hρe]; abel
        have hP' : B.lc ^ e • (X : PowerSeries O) ^ (k + 1) • ρ =
            C εi • C (u₁ ^ (k + 1)) • (X : PowerSeries O) ^ (k + 1) • ρ -
              C εi • (X : PowerSeries O) ^ (k + 1) • ρ := by
          rw [← hP, mul_sub, mul_one, sub_smul, mul_smul]
        have hA : hhA B.ℓ (k + 1) = hhA B.ℓ k + e := rfl
        rw [map_add, γ_lc, hγ', hA, pow_add B.lc (hhA B.ℓ k) e, hG, hγv, smul_neg, smul_comm _ (C εi) ρ, smul_add,
          smul_add, hP']
        generalize (X : PowerSeries O) ^ (k + 1) • ρ = P
        simp only [smul_add, smul_neg, smul_smul, mul_comm]
        abel
      rw [hfin]
      exact smul_mem_sm _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ hw))

end hh

end GoodPlacesAlt

open IdempotentNormalFormsRhoFacts GoodPlacesAlt

/- English proof (translation)
Introduce `O _ B u₁ n _ M V _ _ L c hE h9 v hv hγ`. Take `⟨hu, hpow⟩` from `hE`. Establish `key : ∀ m, m ≤ M → ∃ K : ℕ, B.lc ^ K • v ∈ sm (X ^ m) (L.N c)`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => intro _; exact ⟨0, mem_sm.2 ⟨v, sm_le _ _ hv, by simp⟩⟩`. Consider the case `succ m ih`. Introduce `hm`. Break down `Nat.eq_zero_or_pos m with rfl | hm0` into its components or cases. Conclude with `⟨0, by simpa using hv⟩`.

Take `⟨K, hK⟩` from `ih (by omega)`. Take `⟨x, hx, hxe⟩` from `mem_sm.1 hK`. Take `⟨ε, hε⟩` from `hpow m hm0`. Establish `h1` using `hh_gr L hu h9 c m hx`. Establish `h2 : L.γ c ((X : PowerSeries O) ^ m • x) - (X : PowerSeries O) ^ m • x ∈ sm (X ^ (m + 1)) (L.N c)`.

Rewrite using `[hxe, γ_lc, ← smul_sub]`. Conclude with `Submodule.smul_mem _ _ (hh_sm_pow_mono hm hγ)`. Establish `h3 : C (u₁ ^ m - 1) • (X : PowerSeries O) ^ m • x ∈ sm (X ^ (m + 1)) (L.N c)`. Use `Submodule.sub_mem _ h2 h1` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_sub, map_one, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Use `⟨1 + padicValNat B.ℓ m + K, ?_⟩` and prove the remaining obligations. Establish `h4` using `Submodule.smul_mem _ (C ((ε⁻¹ : Oˣ) : O)) h3`. Use `h4 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[hxe, hε, smul_smul, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, pow_add, mul_smul, lc_pow]`. Conclude with `key M le_rfl`.
-/
theorem gamma_injective_holds : GamInjOf := by
  intro O _ B u₁ n _ M V _ _ L c hE h9 v hv hγ
  obtain ⟨hu, hpow⟩ := hE
  have key : ∀ m, m ≤ M → ∃ K : ℕ, B.lc ^ K • v ∈ sm (X ^ m) (L.N c) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨0, mem_sm.2 ⟨v, sm_le _ _ hv, by simp⟩⟩
    | succ m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · exact ⟨0, by simpa using hv⟩
      obtain ⟨K, hK⟩ := ih (by omega)
      obtain ⟨x, hx, hxe⟩ := mem_sm.1 hK
      obtain ⟨ε, hε⟩ := hpow m hm0
      have h1 := hh_gr L hu h9 c m hx
      have h2 : L.γ c ((X : PowerSeries O) ^ m • x) - (X : PowerSeries O) ^ m • x ∈
          sm (X ^ (m + 1)) (L.N c) := by
        rw [hxe, γ_lc, ← smul_sub]
        exact Submodule.smul_mem _ _ (hh_sm_pow_mono hm hγ)
      have h3 : C (u₁ ^ m - 1) • (X : PowerSeries O) ^ m • x ∈ sm (X ^ (m + 1)) (L.N c) := by
        have := Submodule.sub_mem _ h2 h1
        convert this using 1
        rw [map_sub, map_one, sub_smul, one_smul]
        abel
      refine ⟨1 + padicValNat B.ℓ m + K, ?_⟩
      have h4 := Submodule.smul_mem _ (C ((ε⁻¹ : Oˣ) : O)) h3
      convert h4 using 1
      rw [hxe, hε, smul_smul, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, pow_add, mul_smul,
        lc_pow]
  exact key M le_rfl

/- English proof (translation)
Introduce `O _ B u₁ n _ M V _ _ L c hℓ hE h9 z hz`. Break down `Nat.eq_zero_or_pos M with rfl | hM` into its components or cases. Use `⟨0, fun _ => 0, fun _ => 0, fun _ => 0, fun r h1 h2 => by omega, ?_⟩` and prove the remaining obligations. Use `mem_sm.2 ⟨-z, Submodule.neg_mem _ (sm_le _ _ hz), by simp⟩` and prove the remaining obligations. Take `⟨k, rfl⟩ : ∃ k, M = k + 1` from `⟨M - 1, by omega⟩`.

Take `⟨b, d, hbd, hres⟩` from `hh_main L hE h9 c hz k`. Use `⟨hhA B.ℓ k, hhA B.ℓ, b, d, fun r h1 h2 => ?_, hres⟩` and prove the remaining obligations. Take `⟨h3, h4⟩` from `hbd r h1 (by omega)`. Conclude with `⟨h3, hhA_le _ hℓ r, h4⟩`.
-/
theorem height_bound_holds : HOf := by
  intro O _ B u₁ n _ M V _ _ L c hℓ hE h9 z hz
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · refine ⟨0, fun _ => 0, fun _ => 0, fun _ => 0, fun r h1 h2 => by omega, ?_⟩
    refine mem_sm.2 ⟨-z, Submodule.neg_mem _ (sm_le _ _ hz), by simp⟩
  · obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    obtain ⟨b, d, hbd, hres⟩ := hh_main L hE h9 c hz k
    refine ⟨hhA B.ℓ k, hhA B.ℓ, b, d, fun r h1 h2 => ?_, hres⟩
    obtain ⟨h3, h4⟩ := hbd r h1 (by omega)
    exact ⟨h3, hhA_le _ hℓ r, h4⟩

/- English proof (translation)
Introduce `O _ B n _ j M g sig V _ _ L c hT hH z hz`. Take `⟨K, a, b, d, habd, hres⟩` from `hH z hz`. Establish `hx : ∀ r, ∃ x y : PowerSeries O, 1 ≤ r → r < M → B.lc ^ sig * ((⇑B.φ)^[j] X) ^ r - B.lc ^ a r * x = y * B.ff j M g`. Introduce `r`. Distinguish the cases in `hr : 1 ≤ r ∧ r < M`.

Take `⟨x, hx⟩` from `hT r (a r) (habd r hr.1 hr.2).2.1`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 hx`. Conclude with `⟨x, y, fun _ _ => hy.symm⟩`. Conclude with `⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ hr⟩`. Use `choose x y hxy using hx`.

Use `⟨∑ r ∈ Finset.Ico 1 M, x r • L.phiIt c j (d r), ?_, K, ∑ r ∈ Finset.Ico 1 M, (B.lc ^ b r * X ^ r) • d r, ?_, hres, ?_⟩` and prove the remaining obligations. Use `Submodule.sum_mem _ fun r hr => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `Finset.mem_Ico.1 hr`. Conclude with `phiIt_mem_pull L j (habd r h1 h2).2.2`. Use `Submodule.sum_mem _ fun r hr => ?_` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `Finset.mem_Ico.1 hr`. Take `⟨t, rfl⟩ : ∃ t, r = t + 1` from `⟨r - 1, by omega⟩`. Establish `: (B.lc ^ b (t + 1) * X ^ (t + 1)) • d (t + 1) = (X : PowerSeries O) • ((B.lc ^ b (t + 1) * X ^ t) • d (t + 1))`. Rewrite using `[smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `smul_mem_sm _ (Submodule.smul_mem _ _ (habd _ h1 h2).2.2)`. Rewrite using `[hh_phiIt_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun r hr => ?_` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `Finset.mem_Ico.1 hr`. Take `⟨hK, -, hd⟩` from `habd r h1 h2`. Establish `h` using `hxy r h1 h2`. Establish `: B.lc ^ K • x r • L.phiIt c j (d r) - B.lc ^ sig • L.phiIt c j ((B.lc ^ b r * X ^ r) • d r) = B.ff j M g • ((-(B.lc ^ b r * y r)) • L.phiIt c j (d r))`. Rewrite using `[mul_smul, phiIt_lc, phiIt_smul, it_pow, ← hK, smul_smul, smul_smul, smul_smul, smul_smul, ← sub_smul]`.

Use `congr 1`. Take the linear combination `(-(B.lc ^ b r)) * h`. Rewrite using `[this]`. Conclude with `smul_mem_sm _ (Submodule.smul_mem _ _ (phiIt_mem_pull L j hd))`.
-/
theorem second_rule_first_form : ExistsTransport := by
  intro O _ B n _ j M g sig V _ _ L c hT hH z hz
  obtain ⟨K, a, b, d, habd, hres⟩ := hH z hz
  have hx : ∀ r, ∃ x y : PowerSeries O, 1 ≤ r → r < M →
      B.lc ^ sig * ((⇑B.φ)^[j] X) ^ r - B.lc ^ a r * x = y * B.ff j M g := by
    intro r
    by_cases hr : 1 ≤ r ∧ r < M
    · obtain ⟨x, hx⟩ := hT r (a r) (habd r hr.1 hr.2).2.1
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
      exact ⟨x, y, fun _ _ => hy.symm⟩
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ hr⟩
  choose x y hxy using hx
  refine ⟨∑ r ∈ Finset.Ico 1 M, x r • L.phiIt c j (d r), ?_, K,
    ∑ r ∈ Finset.Ico 1 M, (B.lc ^ b r * X ^ r) • d r, ?_, hres, ?_⟩
  · refine Submodule.sum_mem _ fun r hr => Submodule.smul_mem _ _ ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hr
    exact phiIt_mem_pull L j (habd r h1 h2).2.2
  · refine Submodule.sum_mem _ fun r hr => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hr
    obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
    have : (B.lc ^ b (t + 1) * X ^ (t + 1)) • d (t + 1) =
        (X : PowerSeries O) • ((B.lc ^ b (t + 1) * X ^ t) • d (t + 1)) := by
      rw [smul_smul]
      congr 1
      ring
    rw [this]
    exact smul_mem_sm _ (Submodule.smul_mem _ _ (habd _ h1 h2).2.2)
  · rw [hh_phiIt_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun r hr => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hr
    obtain ⟨hK, -, hd⟩ := habd r h1 h2
    have h := hxy r h1 h2
    have : B.lc ^ K • x r • L.phiIt c j (d r) -
        B.lc ^ sig • L.phiIt c j ((B.lc ^ b r * X ^ r) • d r) =
        B.ff j M g • ((-(B.lc ^ b r * y r)) • L.phiIt c j (d r)) := by
      rw [mul_smul, phiIt_lc, phiIt_smul, it_pow, ← hK, smul_smul, smul_smul, smul_smul, smul_smul,
        ← sub_smul]
      congr 1
      linear_combination (-(B.lc ^ b r)) * h
    rw [this]
    exact smul_mem_sm _ (Submodule.smul_mem _ _ (phiIt_mem_pull L j hd))

namespace GoodPlacesAlt

open IdempotentNormalFormsRhoFacts

section f1b_abs
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

/- English proof (translation)
Establish `e : (I • (⊤ : Submodule R S)).map S.subtype = I • S`. Rewrite using `[Submodule.map_smul'', Submodule.map_subtype_top]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← e]`.

Conclude with `Submodule.mem_map_of_mem (f := S.subtype) h`. Introduce `h`. Rewrite `h` using `[← e]`. Take `⟨y, hy, hxy⟩` from `Submodule.mem_map.1 h`. Establish `: y = x` using `Subtype.ext hxy`.

Conclude with `this ▸ hy`.
-/
theorem mem_ideal_smul_top_iff (I : Ideal R) (S : Submodule R V) (x : S) :
    x ∈ I • (⊤ : Submodule R S) ↔ (x : V) ∈ I • S := by
  have e : (I • (⊤ : Submodule R S)).map S.subtype = I • S := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  constructor
  · intro h
    rw [← e]
    exact Submodule.mem_map_of_mem (f := S.subtype) h
  · intro h
    rw [← e] at h
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.1 h
    have : y = x := Subtype.ext hxy
    exact this ▸ hy

/- English proof (translation)
The claim follows from `Submodule.smul_le_right`.
-/
theorem ideal_smul_submodule_le (I : Ideal R) (S : Submodule R V) : I • S ≤ S := Submodule.smul_le_right

/- English proof (translation)
Establish `hv : v ∈ S` using `ideal_smul_submodule_le _ _ (h 0)`. Establish `: (⟨v, hv⟩ : S) = 0`. Apply `IsHausdorff.haus (I := I) inferInstance` to reduce the goal to its premises. Introduce `k`. Rewrite using `[SModEq.zero, mem_ideal_smul_top_iff]`.

Conclude with `h k`. Conclude with `congrArg Subtype.val this`.
-/
theorem hausdorff_mem_all_powers_zero (I : Ideal R) (S : Submodule R V) [IsHausdorff I S] {v : V}
    (h : ∀ k : ℕ, v ∈ I ^ k • S) : v = 0 := by
  have hv : v ∈ S := ideal_smul_submodule_le _ _ (h 0)
  have : (⟨v, hv⟩ : S) = 0 := by
    apply IsHausdorff.haus (I := I) inferInstance
    intro k
    rw [SModEq.zero, mem_ideal_smul_top_iff]
    exact h k
  exact congrArg Subtype.val this

/- English proof (translation)
Take `⟨y, hy⟩` from `IsPrecomplete.prec (I := I) (M := S) inferInstance (f := fun k => (⟨f k, hf k⟩ : S)) (by`. Introduce `m n hmn`. Rewrite using `[SModEq.sub_mem, mem_ideal_smul_top_iff]`. Conclude with `hc m n hmn)`. Use `⟨y, y.2, fun k => ?_⟩` and prove the remaining obligations.

Use `hy k` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, mem_ideal_smul_top_iff]`. Conclude with `this`.
-/
theorem precomplete_cauchy_limit_exists (I : Ideal R) (S : Submodule R V) [IsPrecomplete I S] (f : ℕ → V)
    (hf : ∀ k, f k ∈ S) (hc : ∀ m n, m ≤ n → f m - f n ∈ I ^ m • S) :
    ∃ y ∈ S, ∀ k, f k - y ∈ I ^ k • S := by
  obtain ⟨y, hy⟩ := IsPrecomplete.prec (I := I) (M := S) inferInstance
    (f := fun k => (⟨f k, hf k⟩ : S)) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_ideal_smul_top_iff]
      exact hc m n hmn)
  refine ⟨y, y.2, fun k => ?_⟩
  have := hy k
  rw [SModEq.sub_mem, mem_ideal_smul_top_iff] at this
  exact this

end f1b_abs

section f1b_lat
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] (L : Lat B n V)

/- English proof (translation)
Unfold `Base.q Base.mm`. Conclude with `Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp [Base.lc]))`.
-/
theorem uniformizer_mem_maximal_ideal : B.q ∈ B.mm := by
  unfold Base.q Base.mm
  exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp [Base.lc]))

/- English proof (translation)
Establish `h1 : B.mm ≤ Ideal.comap B.φ B.mm`. Unfold `Base.mm`. Rewrite using `[Ideal.span_le]`. Introduce `x hx`. Break down `hx with rfl | hx` into its components or cases.

Rewrite using `[SetLike.mem_coe, Ideal.mem_comap, Base.lc, alg_C]`. Conclude with `Ideal.subset_span (by simp)`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap]`.

Take `⟨u, hu⟩` from `h3`. Rewrite using `[hu, mul_assoc, mul_comm X, ← mul_assoc]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))`. Establish `h2 : B.mm ^ k ≤ Ideal.comap B.φ (B.mm ^ k)` using `(Ideal.pow_right_mono h1 k).trans (Ideal.le_comap_pow _ _)`. Conclude with `h2 ha`.
-/
theorem frobenius_preserves_maximal_power (h3 : B.E3) (k : ℕ) {a : PowerSeries O} (ha : a ∈ B.mm ^ k) :
    B.φ a ∈ B.mm ^ k := by
  have h1 : B.mm ≤ Ideal.comap B.φ B.mm := by
    unfold Base.mm
    rw [Ideal.span_le]
    intro x hx
    rcases hx with rfl | hx
    · rw [SetLike.mem_coe, Ideal.mem_comap, Base.lc, alg_C]
      exact Ideal.subset_span (by simp)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [SetLike.mem_coe, Ideal.mem_comap]
      obtain ⟨u, hu⟩ := h3
      rw [hu, mul_assoc, mul_comm X, ← mul_assoc]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  have h2 : B.mm ^ k ≤ Ideal.comap B.φ (B.mm ^ k) :=
    (Ideal.pow_right_mono h1 k).trans (Ideal.le_comap_pow _ _)
  exact h2 ha

/- English proof (translation)
Proceed by induction on `hw using Submodule.smul_induction_on' with`. Consider the case `smul a ha x hx`. Take `⟨y, hy, hyx⟩` from `mem_sm.1 (hq i _ (smul_mem_sm (X ^ M) hx))`. Establish `e : L.φ i ((X : PowerSeries O) ^ M • a • x) = (X : PowerSeries O) ^ M • (B.φ a * B.q) • y`. Rewrite using `[smul_comm, L.φ_semi, ← hyx, ← mul_smul, ← mul_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Apply `smul_mem_sm` to reduce the goal to its premises. Apply `Submodule.smul_mem_smul _ hy` to reduce the goal to its premises.

Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul (frobenius_preserves_maximal_power h3 k ha) uniformizer_mem_maximal_ideal`. Consider the case `add x _ y _ hx hy`. Rewrite using `[smul_add, map_add]`. Conclude with `Submodule.add_mem _ hx hy`.
-/
theorem phi_maps_filtered_lattice (h3 : B.E3) {M : ℕ} (hq : L.FrobeniusMapsXPow M) (i : ZMod n) (k : ℕ) {w : V}
    (hw : w ∈ B.mm ^ k • L.N (i - 1)) :
    L.φ i ((X : PowerSeries O) ^ M • w) ∈ sm (X ^ M) (B.mm ^ (k + 1) • L.N i) := by
  induction hw using Submodule.smul_induction_on' with
  | smul a ha x hx =>
    obtain ⟨y, hy, hyx⟩ := mem_sm.1 (hq i _ (smul_mem_sm (X ^ M) hx))
    have e : L.φ i ((X : PowerSeries O) ^ M • a • x) =
        (X : PowerSeries O) ^ M • (B.φ a * B.q) • y := by
      rw [smul_comm, L.φ_semi, ← hyx, ← mul_smul, ← mul_smul]
      congr 1
      ring
    rw [e]
    apply smul_mem_sm
    apply Submodule.smul_mem_smul _ hy
    rw [pow_succ]
    exact Ideal.mul_mem_mul (frobenius_preserves_maximal_power h3 k ha) uniformizer_mem_maximal_ideal
  | add x _ y _ hx hy =>
    rw [smul_add, map_add]
    exact Submodule.add_mem _ hx hy

/- English proof (translation)
Proceed by induction on `M with`. Consider the case `zero => simpa using h`. Consider the case `succ M ih`. Apply `ih` to reduce the goal to its premises. Apply `hX i _ ((L.N i).smul_mem _ hw)` to reduce the goal to its premises.

Rewrite using `[← mul_smul, ← pow_succ']`. Conclude with `h`.
-/
theorem power_series_X_cancel (hX : L.XReg) (i : ZMod n) (M : ℕ) {w : V} (hw : w ∈ L.N i)
    (h : (X : PowerSeries O) ^ M • w = 0) : w = 0 := by
  induction M with
  | zero => simpa using h
  | succ M ih =>
    apply ih
    apply hX i _ ((L.N i).smul_mem _ hw)
    rw [← mul_smul, ← pow_succ']
    exact h

/- English proof (translation)
Take `⟨w, hw, rfl⟩` from `mem_sm.1 (h 0)`. Establish `hwN : w ∈ L.N i` using `ideal_smul_submodule_le _ _ hw`. Establish `: IsAdicComplete B.mm (L.N i)` using `hC i`. Establish `hw0 : w = 0`. Apply `hausdorff_mem_all_powers_zero B.mm (L.N i)` to reduce the goal to its premises.

Introduce `k`. Take `⟨w', hw', e⟩` from `mem_sm.1 (h k)`. Establish `: w' - w = 0`. Apply `power_series_X_cancel L hX i M ((L.N i).sub_mem (ideal_smul_submodule_le _ _ hw') hwN)` to reduce the goal to its premises. Rewrite using `[smul_sub, e, sub_self]`.

Rewrite using `[← sub_eq_zero.1 this]`. Conclude with `hw'`. Rewrite using `[hw0, smul_zero]`.
-/
theorem mem_all_filtered_powers_zero (hC : L.Complete) (hX : L.XReg) (i : ZMod n) (M : ℕ) {v : V}
    (h : ∀ k : ℕ, v ∈ sm (X ^ M) (B.mm ^ k • L.N i)) : v = 0 := by
  obtain ⟨w, hw, rfl⟩ := mem_sm.1 (h 0)
  have hwN : w ∈ L.N i := ideal_smul_submodule_le _ _ hw
  have : IsAdicComplete B.mm (L.N i) := hC i
  have hw0 : w = 0 := by
    apply hausdorff_mem_all_powers_zero B.mm (L.N i)
    intro k
    obtain ⟨w', hw', e⟩ := mem_sm.1 (h k)
    have : w' - w = 0 := by
      apply power_series_X_cancel L hX i M ((L.N i).sub_mem (ideal_smul_submodule_le _ _ hw') hwN)
      rw [smul_sub, e, sub_self]
    rw [← sub_eq_zero.1 this]
    exact hw'
  rw [hw0, smul_zero]

/- English proof (translation)
The claim follows from `Submodule.map_mono h`.
-/
theorem power_series_smul_map_mono {a : PowerSeries O} {S T : Submodule (PowerSeries O) V} (h : S ≤ T) :
    sm a S ≤ sm a T := Submodule.map_mono h

/- English proof (translation)
The claim follows from `Submodule.smul_mono_left (Ideal.pow_le_pow_right h)`.
-/
theorem maximal_power_smul_antitone (i : ZMod n) {k m : ℕ} (h : k ≤ m) :
    B.mm ^ m • L.N i ≤ B.mm ^ k • L.N i :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

/- English proof (translation)
Rewrite using `[pow_zero, Ideal.one_eq_top, Submodule.top_smul]`.
-/
theorem maximal_power_zero_smul (i : ZMod n) : B.mm ^ 0 • L.N i = L.N i := by
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]

def f1bIt (t : ZMod n → V) : ℕ → ZMod n → V
  | 0 => t
  | k + 1 => fun i => L.φ i (f1bIt t k (i - 1))

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro i`. Rewrite using `[maximal_power_zero_smul]`. Conclude with `ht i`. Consider the case `succ k ih`.

Introduce `i`. Take `⟨w, hw, e⟩` from `mem_sm.1 (ih (i - 1))`. Use `show L.φ i (f1bIt L t k (i - 1)) ∈ _`. Rewrite using `[← e]`. Conclude with `phi_maps_filtered_lattice L h3 hq i k hw`.
-/
theorem iterate_mem_filtered_lattice (h3 : B.E3) {M : ℕ} (hq : L.FrobeniusMapsXPow M) {t : ZMod n → V}
    (ht : ∀ i, t i ∈ sm (X ^ M) (L.N i)) (k : ℕ) :
    ∀ i, f1bIt L t k i ∈ sm (X ^ M) (B.mm ^ k • L.N i) := by
  induction k with
  | zero => intro i; rw [maximal_power_zero_smul]; exact ht i
  | succ k ih =>
    intro i
    obtain ⟨w, hw, e⟩ := mem_sm.1 (ih (i - 1))
    show L.φ i (f1bIt L t k (i - 1)) ∈ _
    rw [← e]
    exact phi_maps_filtered_lattice L h3 hq i k hw

end f1b_lat

end GoodPlacesAlt

open GoodPlacesAlt IdempotentNormalFormsRhoFacts in
/- English proof (translation)
Introduce `O _ B n _ M V _ _ L h3 hq hC hX t ht`. Establish `huniq : ∀ z : ZMod n → V, (∀ i, z i ∈ sm (X ^ M) (L.N i)) → L.dφ z = 0 → z = 0`. Introduce `z hz h0`. Establish `hfix : ∀ i, L.φ i (z (i - 1)) = z i` using `fun i => sub_eq_zero.1 (congrFun h0 i)`. Establish `hk : ∀ k : ℕ, ∀ i, z i ∈ sm (X ^ M) (B.mm ^ k • L.N i)`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro i`. Rewrite using `[maximal_power_zero_smul]`. Conclude with `hz i`.

Consider the case `succ k ih`. Introduce `i`. Take `⟨w, hw, e⟩` from `mem_sm.1 (ih (i - 1))`. Rewrite using `[← hfix i, ← e]`. Conclude with `phi_maps_filtered_lattice L h3 hq i k hw`.

Use function extensionality and compare the values at `i`. Conclude with `mem_all_filtered_powers_zero L hC hX i M (fun k => hk k i)`. Establish `hit` using `iterate_mem_filtered_lattice L h3 hq ht`. Use `choose w hw hwe using fun (k : ℕ) (i : ZMod n) => mem_sm.1 (hit k i)`. Establish `hlim : ∀ i, ∃ y ∈ L.N i, ∀ K, (∑ k ∈ Finset.range K, w k i) - y ∈ B.mm ^ K • L.N i`.

Introduce `i`. Establish `: IsAdicComplete B.mm (L.N i)` using `hC i`. Apply `precomplete_cauchy_limit_exists B.mm (L.N i)` to reduce the goal to its premises. Introduce `K`. Conclude with `Submodule.sum_mem _ (fun k _ => ideal_smul_submodule_le _ _ (hw k i))`.

Introduce `m n' hmn`. Rewrite using `[← neg_sub, ← Finset.sum_sdiff (Finset.range_subset_range.2 hmn), add_sub_cancel_right]`. Apply `Submodule.neg_mem` to reduce the goal to its premises. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `k hk`.

Establish `hmk : m ≤ k`. Simplify using `only [Finset.mem_sdiff, Finset.mem_range, not_lt] at hk`. Conclude with `hk.2`. Conclude with `maximal_power_smul_antitone L i hmk (hw k i)`. Use `choose y hy hyK using hlim`.

Establish `hex : L.dφ (fun i => -((X : PowerSeries O) ^ M • y i)) = t`. Use function extensionality and compare the values at `i`. Rewrite using `[← sub_eq_zero]`. Apply `mem_all_filtered_powers_zero L hC hX i M` to reduce the goal to its premises. Introduce `K`.

Establish `e1 : L.φ i ((X : PowerSeries O) ^ M • y (i - 1)) = (∑ k ∈ Finset.range K, f1bIt L t (k + 1) i) - L.φ i ((X : PowerSeries O) ^ M • ((∑ k ∈ Finset.range K, w k (i - 1)) - y (i - 1)))`. Rewrite using `[smul_sub, map_sub, Finset.smul_sum, map_sum]`. Simplify using `only [hwe]`. Simplify using `[f1bIt]`. Establish `e2 : (X : PowerSeries O) ^ M • y i = (∑ k ∈ Finset.range K, f1bIt L t k i) - (X : PowerSeries O) ^ M • ((∑ k ∈ Finset.range K, w k i) - y i)`.

Rewrite using `[smul_sub, Finset.smul_sum]`. Simplify using `only [hwe]`. Normalize the expressions using the abelian group laws. Establish `e3 : (∑ k ∈ Finset.range K, f1bIt L t (k + 1) i) = (∑ k ∈ Finset.range K, f1bIt L t k i) + f1bIt L t K i - t i`. Rewrite using `[← Finset.sum_range_succ, Finset.sum_range_succ']`.

Simplify using `[f1bIt]`. Establish `e4 : L.dφ (fun i => -((X : PowerSeries O) ^ M • y i)) i - t i = L.φ i ((X : PowerSeries O) ^ M • ((∑ k ∈ Finset.range K, w k (i - 1)) - y (i - 1))) - f1bIt L t K i - (X : PowerSeries O) ^ M • ((∑ k ∈ Finset.range K, w k i) - y i)` using `by show L.φ i (-((X : PowerSeries O) ^ M • y (i - 1))) - -((X : PowerSeries O) ^ M • y i) - t i = _`. Rewrite using `[map_neg, e1, e3]`. Use `nth_rewrite 1 [e2]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e4]`. Use `Submodule.sub_mem _ (Submodule.sub_mem _ ?_ (hit K i)) (smul_mem_sm _ (hyK i K))` and prove the remaining obligations. Conclude with `power_series_smul_map_mono (maximal_power_smul_antitone L i (Nat.le_succ K)) (phi_maps_filtered_lattice L h3 hq i K (hyK (i - 1) K))`. Use `⟨fun i => -((X : PowerSeries O) ^ M • y i), ⟨fun i => ?_, hex⟩, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.neg_mem _ (smul_mem_sm _ (hy i))`.

Introduce and unpack `z ⟨hz, hzt⟩`. Rewrite using `[← sub_eq_zero]`. Apply `huniq` to reduce the goal to its premises. Introduce `i`. Conclude with `Submodule.sub_mem _ (hz i) (Submodule.neg_mem _ (smul_mem_sm _ (hy i)))`.

Rewrite using `[dφ_sub, hzt, hex, sub_self]`.
-/
theorem lattice_filtration_second_form : FrobeniusDiffBijective := by
  intro O _ B n _ M V _ _ L h3 hq hC hX t ht

  have huniq : ∀ z : ZMod n → V, (∀ i, z i ∈ sm (X ^ M) (L.N i)) → L.dφ z = 0 → z = 0 := by
    intro z hz h0
    have hfix : ∀ i, L.φ i (z (i - 1)) = z i := fun i => sub_eq_zero.1 (congrFun h0 i)
    have hk : ∀ k : ℕ, ∀ i, z i ∈ sm (X ^ M) (B.mm ^ k • L.N i) := by
      intro k
      induction k with
      | zero => intro i; rw [maximal_power_zero_smul]; exact hz i
      | succ k ih =>
        intro i
        obtain ⟨w, hw, e⟩ := mem_sm.1 (ih (i - 1))
        rw [← hfix i, ← e]
        exact phi_maps_filtered_lattice L h3 hq i k hw
    funext i
    exact mem_all_filtered_powers_zero L hC hX i M (fun k => hk k i)

  have hit := iterate_mem_filtered_lattice L h3 hq ht
  choose w hw hwe using fun (k : ℕ) (i : ZMod n) => mem_sm.1 (hit k i)
  have hlim : ∀ i, ∃ y ∈ L.N i, ∀ K, (∑ k ∈ Finset.range K, w k i) - y ∈ B.mm ^ K • L.N i := by
    intro i
    have : IsAdicComplete B.mm (L.N i) := hC i
    apply precomplete_cauchy_limit_exists B.mm (L.N i)
    · intro K
      exact Submodule.sum_mem _ (fun k _ => ideal_smul_submodule_le _ _ (hw k i))
    · intro m n' hmn
      rw [← neg_sub, ← Finset.sum_sdiff (Finset.range_subset_range.2 hmn), add_sub_cancel_right]
      apply Submodule.neg_mem
      apply Submodule.sum_mem
      intro k hk
      have hmk : m ≤ k := by
        simp only [Finset.mem_sdiff, Finset.mem_range, not_lt] at hk
        exact hk.2
      exact maximal_power_smul_antitone L i hmk (hw k i)
  choose y hy hyK using hlim
  have hex : L.dφ (fun i => -((X : PowerSeries O) ^ M • y i)) = t := by
    funext i
    rw [← sub_eq_zero]
    apply mem_all_filtered_powers_zero L hC hX i M
    intro K

    have e1 : L.φ i ((X : PowerSeries O) ^ M • y (i - 1)) =
        (∑ k ∈ Finset.range K, f1bIt L t (k + 1) i) -
          L.φ i ((X : PowerSeries O) ^ M • ((∑ k ∈ Finset.range K, w k (i - 1)) - y (i - 1))) := by
      rw [smul_sub, map_sub, Finset.smul_sum, map_sum]
      simp only [hwe]
      simp [f1bIt]
    have e2 : (X : PowerSeries O) ^ M • y i = (∑ k ∈ Finset.range K, f1bIt L t k i) -
        (X : PowerSeries O) ^ M • ((∑ k ∈ Finset.range K, w k i) - y i) := by
      rw [smul_sub, Finset.smul_sum]
      simp only [hwe]
      abel
    have e3 : (∑ k ∈ Finset.range K, f1bIt L t (k + 1) i) =
        (∑ k ∈ Finset.range K, f1bIt L t k i) + f1bIt L t K i - t i := by
      rw [← Finset.sum_range_succ, Finset.sum_range_succ']
      simp [f1bIt]
    have e4 : L.dφ (fun i => -((X : PowerSeries O) ^ M • y i)) i - t i =
        L.φ i ((X : PowerSeries O) ^ M • ((∑ k ∈ Finset.range K, w k (i - 1)) - y (i - 1))) -
          f1bIt L t K i -
          (X : PowerSeries O) ^ M • ((∑ k ∈ Finset.range K, w k i) - y i) := by
      show L.φ i (-((X : PowerSeries O) ^ M • y (i - 1))) - -((X : PowerSeries O) ^ M • y i) - t i
        = _
      rw [map_neg, e1, e3]
      nth_rewrite 1 [e2]
      abel
    rw [e4]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ (hit K i)) (smul_mem_sm _ (hyK i K))
    exact power_series_smul_map_mono (maximal_power_smul_antitone L i (Nat.le_succ K)) (phi_maps_filtered_lattice L h3 hq i K (hyK (i - 1) K))
  refine ⟨fun i => -((X : PowerSeries O) ^ M • y i), ⟨fun i => ?_, hex⟩, ?_⟩
  · exact Submodule.neg_mem _ (smul_mem_sm _ (hy i))
  · rintro z ⟨hz, hzt⟩
    rw [← sub_eq_zero]
    apply huniq
    · intro i
      exact Submodule.sub_mem _ (hz i) (Submodule.neg_mem _ (smul_mem_sm _ (hy i)))
    · rw [dφ_sub, hzt, hex, sub_self]

namespace GoodPlacesAlt

section e4u
variable {R : Type} [CommRing R]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ i ih`. Take `⟨c, hc⟩` from `ih`. Use `⟨(i : R) + c + c * t, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ, hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem one_add_pow_expansion (t : R) (i : ℕ) : ∃ c : R, (1 + t) ^ i = 1 + (i : R) * t + t ^ 2 * c := by
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨(i : R) + c + c * t, ?_⟩
    rw [pow_succ, hc]
    push_cast
    ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ n ih`. Take `⟨c, hc⟩` from `ih`. Take `⟨d, hd⟩` from `one_add_pow_expansion t n`.

Use `⟨c + d, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ, hc, hd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem geom_sum_one_add_expansion (t : R) (n : ℕ) : ∃ c : R, ∑ i ∈ Finset.range n, (1 + t) ^ i =
    (n : R) + ((∑ i ∈ Finset.range n, i : ℕ) : R) * t + t ^ 2 * c := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := one_add_pow_expansion t n
    refine ⟨c + d, ?_⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hc, hd]
    push_cast
    ring

/- English proof (translation)
Use `mul_geom_sum (1 + t) n` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_left]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem one_add_pow_eq_geom_sum (t : R) (n : ℕ) :
    (1 + t) ^ n = 1 + t * ∑ i ∈ Finset.range n, (1 + t) ^ i := by
  have := mul_geom_sum (1 + t) n
  rw [add_sub_cancel_left] at this
  rw [this]
  ring

variable [IsLocalRing R]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `h2 : ¬IsUnit (-(l * y))`. Rewrite using `[IsUnit.neg_iff]`. Conclude with `not_isUnit_of_not_isUnit_dvd hl ⟨y, rfl⟩`. Use `IsLocalRing.nonunits_add h h2` as an intermediate fact.

Rewrite `this` using `[add_neg_cancel_right]`. Conclude with `this hx`.
-/
theorem unit_add_nonunit_mul_isUnit {x l : R} (hx : IsUnit x) (hl : ¬IsUnit l) (y : R) :
    IsUnit (x + l * y) := by
  by_contra h
  have h2 : ¬IsUnit (-(l * y)) := by
    rw [IsUnit.neg_iff]
    exact not_isUnit_of_not_isUnit_dvd hl ⟨y, rfl⟩
  have := IsLocalRing.nonunits_add h h2
  rw [add_neg_cancel_right] at this
  exact this hx

/- English proof (translation)
Establish `h1 : IsCoprime (r : ℤ) (ℓ : ℤ)` using `Nat.isCoprime_iff_coprime.2 hr`. Take `⟨a, b, hab⟩` from `h1`. Establish `h2 : (a : R) * (r : R) + (b : R) * (ℓ : R) = 1`. Conclude with `congrArg (Int.cast : ℤ → R) hab` after adjusting the coercions. Establish `h3 : (a : R) * (r : R) = 1 + (ℓ : R) * (-(b : R))` using `by linear_combination h2`.

Establish `h4 : IsUnit ((a : R) * (r : R))`. Rewrite using `[h3]`. Conclude with `unit_add_nonunit_mul_isUnit isUnit_one hl _`. Conclude with `isUnit_of_mul_isUnit_right h4`.
-/
theorem cast_coprime_isUnit {ℓ r : ℕ} (hl : ¬IsUnit (ℓ : R)) (hr : Nat.Coprime r ℓ) :
    IsUnit (r : R) := by
  have h1 : IsCoprime (r : ℤ) (ℓ : ℤ) := Nat.isCoprime_iff_coprime.2 hr
  obtain ⟨a, b, hab⟩ := h1
  have h2 : (a : R) * (r : R) + (b : R) * (ℓ : R) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → R) hab
  have h3 : (a : R) * (r : R) = 1 + (ℓ : R) * (-(b : R)) := by linear_combination h2
  have h4 : IsUnit ((a : R) * (r : R)) := by
    rw [h3]
    exact unit_add_nonunit_mul_isUnit isUnit_one hl _
  exact isUnit_of_mul_isUnit_right h4

/- English proof (translation)
Take `⟨c, hc⟩` from `geom_sum_one_add_expansion ((ℓ : R) ^ (k + 1) * x) r`. Use `set S : R := ((∑ i ∈ Finset.range r, i : ℕ) : R) with hS`. Use `⟨x * ((r : R) + (ℓ : R) * ((ℓ : R) ^ k * x * S + (ℓ : R) ^ k * x * ((ℓ : R) ^ (k + 1) * x) * c)), ?_, ?_⟩` and prove the remaining obligations. Conclude with `hx.mul (unit_add_nonunit_mul_isUnit (cast_coprime_isUnit hl hr) hl _)`. Rewrite using `[one_add_pow_eq_geom_sum, hc]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem one_add_pow_coprime_unit {ℓ r : ℕ} (hl : ¬IsUnit (ℓ : R)) (hr : Nat.Coprime r ℓ) (k : ℕ) {x : R}
    (hx : IsUnit x) :
    ∃ x' : R, IsUnit x' ∧ (1 + (ℓ : R) ^ (k + 1) * x) ^ r = 1 + (ℓ : R) ^ (k + 1) * x' := by
  obtain ⟨c, hc⟩ := geom_sum_one_add_expansion ((ℓ : R) ^ (k + 1) * x) r
  set S : R := ((∑ i ∈ Finset.range r, i : ℕ) : R) with hS
  refine ⟨x * ((r : R) + (ℓ : R) * ((ℓ : R) ^ k * x * S +
    (ℓ : R) ^ k * x * ((ℓ : R) ^ (k + 1) * x) * c)), ?_, ?_⟩
  · exact hx.mul (unit_add_nonunit_mul_isUnit (cast_coprime_isUnit hl hr) hl _)
  · rw [one_add_pow_eq_geom_sum, hc]
    ring

/- English proof (translation)
Take `⟨m, hm⟩` from `hodd`. Take `⟨c, hc⟩` from `geom_sum_one_add_expansion ((ℓ : R) ^ (k + 1) * x) ℓ`. Establish `hsum : (∑ i ∈ Finset.range ℓ, i : ℕ) = ℓ * m`. Establish `h2` using `Finset.sum_range_id_mul_two ℓ`. Establish `h3 : ℓ - 1 = m * 2` using `by omega`.

Rewrite `h2` using `[h3, ← mul_assoc]`. Conclude with `Nat.eq_of_mul_eq_mul_right (by norm_num) h2`. Rewrite `hc` using `[hsum]`. Use `⟨x * (1 + (ℓ : R) * ((m : R) * ((ℓ : R) ^ k * x) + (ℓ : R) ^ k * x * ((ℓ : R) ^ k * x) * c)), ?_, ?_⟩` and prove the remaining obligations. Conclude with `hx.mul (unit_add_nonunit_mul_isUnit isUnit_one hl _)`.

Rewrite using `[one_add_pow_eq_geom_sum, hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem one_add_pow_prime_unit {ℓ : ℕ} (hl : ¬IsUnit (ℓ : R)) (hodd : Odd ℓ) (k : ℕ) {x : R}
    (hx : IsUnit x) :
    ∃ x' : R, IsUnit x' ∧ (1 + (ℓ : R) ^ (k + 1) * x) ^ ℓ = 1 + (ℓ : R) ^ (k + 2) * x' := by
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨c, hc⟩ := geom_sum_one_add_expansion ((ℓ : R) ^ (k + 1) * x) ℓ
  have hsum : (∑ i ∈ Finset.range ℓ, i : ℕ) = ℓ * m := by
    have h2 := Finset.sum_range_id_mul_two ℓ
    have h3 : ℓ - 1 = m * 2 := by omega
    rw [h3, ← mul_assoc] at h2
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  rw [hsum] at hc
  refine ⟨x * (1 + (ℓ : R) * ((m : R) * ((ℓ : R) ^ k * x) +
    (ℓ : R) ^ k * x * ((ℓ : R) ^ k * x) * c)), ?_, ?_⟩
  · exact hx.mul (unit_add_nonunit_mul_isUnit isUnit_one hl _)
  · rw [one_add_pow_eq_geom_sum, hc]
    push_cast
    ring

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => exact ⟨x, hx, by simp⟩`. Consider the case `succ a ih`. Take `⟨y, hy, hya⟩` from `ih`. Take `⟨z, hz, hza⟩` from `one_add_pow_prime_unit hl hodd a hy`.

Conclude with `⟨z, hz, by rw [pow_succ, pow_mul, hya, hza]⟩`.
-/
theorem one_add_pow_prime_power_unit {ℓ : ℕ} (hl : ¬IsUnit (ℓ : R)) (hodd : Odd ℓ) {x : R} (hx : IsUnit x)
    (a : ℕ) :
    ∃ x' : R, IsUnit x' ∧ (1 + (ℓ : R) * x) ^ (ℓ ^ a) = 1 + (ℓ : R) ^ (a + 1) * x' := by
  induction a with
  | zero => exact ⟨x, hx, by simp⟩
  | succ a ih =>
    obtain ⟨y, hy, hya⟩ := ih
    obtain ⟨z, hz, hza⟩ := one_add_pow_prime_unit hl hodd a hy
    exact ⟨z, hz, by rw [pow_succ, pow_mul, hya, hza]⟩

/- English proof (translation)
Establish `: Fact ℓ.Prime` using `⟨hp⟩`. Establish `hodd : Odd ℓ` using `hp.odd_of_ne_two (by omega)`. Take `⟨a, r', hr', rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (by omega : r ≠ 0) ℓ hp.ne_one`. Establish `hr0 : r' ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hr' (dvd_zero _)`. Establish `hv : padicValNat ℓ (ℓ ^ a * r') = a`. Rewrite using `[padicValNat.mul (pow_ne_zero _ hp.ne_zero) hr0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hr', add_zero]`. Establish `hco : Nat.Coprime r' ℓ` using `((Nat.Prime.coprime_iff_not_dvd hp).2 hr').symm`. Take `⟨y, hy, hya⟩` from `one_add_pow_prime_power_unit hl hodd hx a`.

Take `⟨z, hz, hza⟩` from `one_add_pow_coprime_unit hl hco a hy`. Use `⟨hz.unit, ?_⟩` and prove the remaining obligations. Rewrite using `[hv, pow_mul, hya, hza, IsUnit.unit_spec, add_comm 1 a]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem one_add_pow_sub_one_valuation {ℓ : ℕ} (hp : ℓ.Prime) (h3 : 3 ≤ ℓ) (hl : ¬IsUnit (ℓ : R)) {x : R}
    (hx : IsUnit x) (r : ℕ) (hr : 1 ≤ r) :
    ∃ ε : Rˣ, (1 + (ℓ : R) * x) ^ r - 1 = (ε : R) * (ℓ : R) ^ (1 + padicValNat ℓ r) := by
  have : Fact ℓ.Prime := ⟨hp⟩
  have hodd : Odd ℓ := hp.odd_of_ne_two (by omega)
  obtain ⟨a, r', hr', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : r ≠ 0) ℓ hp.ne_one
  have hr0 : r' ≠ 0 := by
    rintro rfl
    exact hr' (dvd_zero _)
  have hv : padicValNat ℓ (ℓ ^ a * r') = a := by
    rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hr0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hr', add_zero]
  have hco : Nat.Coprime r' ℓ := ((Nat.Prime.coprime_iff_not_dvd hp).2 hr').symm
  obtain ⟨y, hy, hya⟩ := one_add_pow_prime_power_unit hl hodd hx a
  obtain ⟨z, hz, hza⟩ := one_add_pow_coprime_unit hl hco a hy
  refine ⟨hz.unit, ?_⟩
  rw [hv, pow_mul, hya, hza, IsUnit.unit_spec, add_comm 1 a]
  ring

end e4u

end GoodPlacesAlt

open GoodPlacesAlt IdempotentNormalFormsRhoFacts

/- English proof (translation)
Introduce `O _ _ _ ϖ B hϖ hd hp h3 h4`. Take `⟨e, he⟩` from `h4`. Establish `hl : ¬IsUnit (B.ℓ : O)` using `not_isUnit_of_not_isUnit_dvd hϖ.not_isUnit hd`. Establish `he0 : IsUnit (constantCoeff (e : PowerSeries O))` using `e.isUnit.map constantCoeff`. Use `⟨1 + (B.ℓ : O) * constantCoeff (e : PowerSeries O), ?_, one_add_pow_sub_one_valuation hp h3 hl he0⟩` and prove the remaining obligations.

Establish `hX : (X : PowerSeries O) ∣ (e : PowerSeries O) - C (constantCoeff (e : PowerSeries O))`. Rewrite using `[X_dvd_iff]`. Simplify using the standard rewrite rules. Take `⟨e', he'⟩` from `hX`. Use `⟨C (constantCoeff (e : PowerSeries O)) + e' * X + e' * C (B.ℓ : O), ?_⟩` and prove the remaining obligations.

Establish `h5 : (e : PowerSeries O) = C (constantCoeff (e : PowerSeries O)) + X * e'`. Rewrite using `[← he']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Use `conv_lhs => rw [h5]`.

Simplify using `only [Base.q, map_add, map_mul, map_one, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem one_add_unit_pow_formula : ExistsGammaXUnitShape := by
  intro O _ _ _ ϖ B hϖ hd hp h3 h4
  obtain ⟨e, he⟩ := h4
  have hl : ¬IsUnit (B.ℓ : O) := not_isUnit_of_not_isUnit_dvd hϖ.not_isUnit hd
  have he0 : IsUnit (constantCoeff (e : PowerSeries O)) := e.isUnit.map constantCoeff
  refine ⟨1 + (B.ℓ : O) * constantCoeff (e : PowerSeries O), ?_, one_add_pow_sub_one_valuation hp h3 hl he0⟩
  have hX : (X : PowerSeries O) ∣ (e : PowerSeries O) - C (constantCoeff (e : PowerSeries O)) := by
    rw [X_dvd_iff]
    simp
  obtain ⟨e', he'⟩ := hX
  refine ⟨C (constantCoeff (e : PowerSeries O)) + e' * X + e' * C (B.ℓ : O), ?_⟩
  have h5 : (e : PowerSeries O) = C (constantCoeff (e : PowerSeries O)) + X * e' := by
    rw [← he']
    ring
  rw [he]
  conv_lhs => rw [h5]
  simp only [Base.q, map_add, map_mul, map_one, map_natCast]
  ring

namespace GoodPlacesAlt

section cp
variable {O : Type} [CommRing O]

def cpI (l : O) (m : ℕ) : Ideal (PowerSeries O) where
  carrier := {f | ∀ k, k < m → l ^ (m - k) ∣ coeff k f}
  add_mem' := fun ha hb k hk => by rw [map_add]; exact dvd_add (ha k hk) (hb k hk)
  zero_mem' := fun k _ => by simp
  smul_mem' := fun a f hf k hk => by
    rw [smul_eq_mul, coeff_mul]
    refine Finset.dvd_sum fun p hp => ?_
    have h2 : p.2 ≤ k := by
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      omega
    exact Dvd.dvd.mul_left ((pow_dvd_pow l (by omega)).trans (hf p.2 (by omega))) _

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem cp_mem_cpI {l : O} {m : ℕ} {f : PowerSeries O} :
    f ∈ cpI l m ↔ ∀ k, k < m → l ^ (m - k) ∣ coeff k f := Iff.rfl

/- English proof (translation)
Introduce `k hk`. Rewrite using `[coeff_C_mul]`. Distinguish the cases in `hkm : k < m`. Establish `: m + 1 - k = (m - k) + 1` using `by omega`. Rewrite using `[this, pow_succ']`.

Conclude with `mul_dvd_mul_left _ (hs k hkm)`. Establish `: m + 1 - k = 1` using `by omega`. Rewrite using `[this, pow_one]`. Conclude with `Dvd.intro _ rfl`.
-/
theorem cp_C_mul {l : O} {m : ℕ} {s : PowerSeries O} (hs : s ∈ cpI l m) :
    C l * s ∈ cpI l (m + 1) := by
  intro k hk
  rw [coeff_C_mul]
  by_cases hkm : k < m
  · have : m + 1 - k = (m - k) + 1 := by omega
    rw [this, pow_succ']
    exact mul_dvd_mul_left _ (hs k hkm)
  · have : m + 1 - k = 1 := by omega
    rw [this, pow_one]
    exact Dvd.intro _ rfl

/- English proof (translation)
Introduce `k hk`. Consider the cases of `k with`. Consider the case `zero => rw [coeff_zero_X_mul]`. Conclude with `dvd_zero _`. Consider the case `succ k`.

Rewrite using `[coeff_succ_X_mul, Nat.add_sub_add_right]`. Conclude with `hs k (by omega)`.
-/
theorem cp_X_mul {l : O} {m : ℕ} {s : PowerSeries O} (hs : s ∈ cpI l m) :
    X * s ∈ cpI l (m + 1) := by
  intro k hk
  cases k with
  | zero => rw [coeff_zero_X_mul]; exact dvd_zero _
  | succ k =>
    rw [coeff_succ_X_mul, Nat.add_sub_add_right]
    exact hs k (by omega)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro f _ k hk`. Use linear arithmetic over natural numbers and integers. Consider the case `succ m ih`. Rewrite using `[pow_succ']`.

Use `Ideal.mul_le.2 fun a ha s hs => ?_` and prove the remaining obligations. Take `⟨c, d, rfl⟩` from `Ideal.mem_span_pair.1 ha`. Establish `: (c * C l + d * X) * s = c * (C l * s) + d * (X * s)` using `by ring`. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ (cp_C_mul (ih hs))) (Ideal.mul_mem_left _ _ (cp_X_mul (ih hs)))`.
-/
theorem cp_pow_le (l : O) (m : ℕ) :
    (Ideal.span {C l, X} : Ideal (PowerSeries O)) ^ m ≤ cpI l m := by
  induction m with
  | zero => intro f _ k hk; omega
  | succ m ih =>
    rw [pow_succ']
    refine Ideal.mul_le.2 fun a ha s hs => ?_
    obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.1 ha
    have : (c * C l + d * X) * s = c * (C l * s) + d * (X * s) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (cp_C_mul (ih hs)))
      (Ideal.mul_mem_left _ _ (cp_X_mul (ih hs)))

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro f _`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `f hf`.

Establish `hC : (C l : PowerSeries O) ∈ (Ideal.span {C l, X} : Ideal (PowerSeries O))` using `Ideal.subset_span (by simp)`. Establish `hX : (X : PowerSeries O) ∈ (Ideal.span {C l, X} : Ideal (PowerSeries O))` using `Ideal.subset_span (by simp)`. Rewrite using `[eq_X_mul_shift_add_const f]`. Use `Ideal.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[pow_succ']`.

Use `Ideal.mul_mem_mul hX (ih ?_)` and prove the remaining obligations. Introduce `k hk`. Rewrite using `[coeff_mk]`. Use `hf (k + 1) (by omega)` as an intermediate fact. Rewrite `this` using `[Nat.add_sub_add_right]`. Then use the resulting hypothesis.

Take `⟨c, hc⟩` from `hf 0 (by omega)`. Rewrite `hc` using `[coeff_zero_eq_constantCoeff_apply, Nat.sub_zero]`. Rewrite using `[hc, map_mul, map_pow]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hC _)`.
-/
theorem cp_le_pow (l : O) (m : ℕ) :
    cpI l m ≤ (Ideal.span {C l, X} : Ideal (PowerSeries O)) ^ m := by
  induction m with
  | zero => intro f _; simp
  | succ m ih =>
    intro f hf
    have hC : (C l : PowerSeries O) ∈ (Ideal.span {C l, X} : Ideal (PowerSeries O)) :=
      Ideal.subset_span (by simp)
    have hX : (X : PowerSeries O) ∈ (Ideal.span {C l, X} : Ideal (PowerSeries O)) :=
      Ideal.subset_span (by simp)
    rw [eq_X_mul_shift_add_const f]
    refine Ideal.add_mem _ ?_ ?_
    · rw [pow_succ']
      refine Ideal.mul_mem_mul hX (ih ?_)
      intro k hk
      rw [coeff_mk]
      have := hf (k + 1) (by omega)
      rwa [Nat.add_sub_add_right] at this
    · obtain ⟨c, hc⟩ := hf 0 (by omega)
      rw [coeff_zero_eq_constantCoeff_apply, Nat.sub_zero] at hc
      rw [hc, map_mul, map_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hC _)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => cp_pow_le l m h, fun h => cp_le_pow l m h⟩`.
-/
theorem cp_mem_pow_iff (l : O) (m : ℕ) (f : PowerSeries O) :
    f ∈ (Ideal.span {C l, X} : Ideal (PowerSeries O)) ^ m ↔
      ∀ k, k < m → l ^ (m - k) ∣ coeff k f :=
  ⟨fun h => cp_pow_le l m h, fun h => cp_le_pow l m h⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.smul_induction_on' with`. Consider the case `smul a ha y _`. Introduce `t`.

Rewrite using `[map_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ ha`. Consider the case `add y _ z _ hy hz`. Introduce `t`. Rewrite using `[map_add, Pi.add_apply]`.

Conclude with `Ideal.add_mem _ (hy t) (hz t)`. Introduce `h`. Establish `h1 : Φ x = ∑ t, Φ x t • (Pi.single t (1 : R) : Fin r → R)`. Use extensionality with `s`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Establish `h2 : x = ∑ t, Φ x t • Φ.symm (Pi.single t (1 : R))`. Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[map_sum]`. Simplify `h1` using `only [map_smul, LinearEquiv.apply_symm_apply]`. Rewrite using `[h2]`.

Conclude with `Submodule.sum_mem _ fun t _ => Submodule.smul_mem_smul (h t) trivial`.
-/
theorem cp_mem_equiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (J : Ideal R)
    {r : ℕ} (Φ : M ≃ₗ[R] (Fin r → R)) (x : M) :
    x ∈ (J • ⊤ : Submodule R M) ↔ ∀ t, Φ x t ∈ J := by
  constructor
  · intro hx
    induction hx using Submodule.smul_induction_on' with
    | smul a ha y _ =>
      intro t
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ ha
    | add y _ z _ hy hz =>
      intro t
      rw [map_add, Pi.add_apply]
      exact Ideal.add_mem _ (hy t) (hz t)
  · intro h
    have h1 : Φ x = ∑ t, Φ x t • (Pi.single t (1 : R) : Fin r → R) := by
      ext s
      simp [Finset.sum_apply, Pi.single_apply]
    have h2 : x = ∑ t, Φ x t • Φ.symm (Pi.single t (1 : R)) := by
      apply Φ.injective
      rw [map_sum]
      simpa only [map_smul, LinearEquiv.apply_symm_apply] using h1
    rw [h2]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem_smul (h t) trivial

/- English proof (translation)
Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.
-/
theorem cp_O_mem (l : O) (n : ℕ) (x : O) :
    x ∈ ((Ideal.span {l}) ^ n • ⊤ : Submodule O O) ↔ l ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/- English proof (translation)
The claim follows from `hO.toIsHausdorff.haus' x fun n => by rw [SModEq.zero, cp_O_mem] exact h n`.
-/
theorem cp_O_haus {l : O} (hO : IsAdicComplete (Ideal.span {l}) O) {x : O}
    (h : ∀ n, l ^ n ∣ x) : x = 0 :=
  hO.toIsHausdorff.haus' x fun n => by
    rw [SModEq.zero, cp_O_mem]
    exact h n

/- English proof (translation)
Take `⟨a, ha⟩` from `hO.toIsPrecomplete.prec' g (fun {m n} hmn => by`. Rewrite using `[SModEq.sub_mem, cp_O_mem]`. Conclude with `h m n hmn)`. Use `⟨a, fun n => ?_⟩` and prove the remaining obligations. Use `ha n` as an intermediate fact.

Rewrite `this` using `[SModEq.sub_mem, cp_O_mem]`. Then use the resulting hypothesis.
-/
theorem cp_O_prec {l : O} (hO : IsAdicComplete (Ideal.span {l}) O) (g : ℕ → O)
    (h : ∀ m n, m ≤ n → l ^ m ∣ g m - g n) : ∃ a : O, ∀ n, l ^ n ∣ g n - a := by
  obtain ⟨a, ha⟩ := hO.toIsPrecomplete.prec' g (fun {m n} hmn => by
    rw [SModEq.sub_mem, cp_O_mem]
    exact h m n hmn)
  refine ⟨a, fun n => ?_⟩
  have := ha n
  rwa [SModEq.sub_mem, cp_O_mem] at this

/- English proof (translation)
Introduce `x hx`. Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use function extensionality and compare the values at `t`. Use extensionality with `k`.

Rewrite using `[Pi.zero_apply, map_zero]`. Apply `cp_O_haus hO` to reduce the goal to its premises. Introduce `n`. Establish `h1` using `hx (n + k + 1)`. Rewrite `h1` using `[SModEq.zero, cp_mem_equiv _ Φ]`.

Establish `h2` using `(cp_mem_pow_iff l _ _).1 (h1 t) k (by omega)`. Conclude with `(pow_dvd_pow l (by omega)).trans h2`. Use the proof step `prec' := by`. Introduce `f hf`. Establish `hc : ∀ (t : Fin r) (k m n : ℕ), m ≤ n → k < m → l ^ (m - k) ∣ coeff k (Φ (f m) t) - coeff k (Φ (f n) t)`.

Introduce `t k m n hmn hk`. Establish `h1` using `hf hmn`. Rewrite `h1` using `[SModEq.sub_mem, cp_mem_equiv _ Φ]`. Establish `h2` using `(cp_mem_pow_iff l _ _).1 (h1 t) k hk`. Rewrite `h2` using `[map_sub, Pi.sub_apply, map_sub]`. Then use the resulting hypothesis.

Establish `hlim : ∀ (t : Fin r) (k : ℕ), ∃ a : O, ∀ s, l ^ s ∣ coeff k (Φ (f (s + k)) t) - a`. Introduce `t k`. Apply `cp_O_prec hO (fun s => coeff k (Φ (f (s + k)) t))` to reduce the goal to its premises. Introduce `m n hmn`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases.

Rewrite using `[pow_zero]`. Conclude with `one_dvd _`. Use `hc t k (m + k) (n + k) (by omega) (by omega)` as an intermediate fact. Rewrite `this` using `[Nat.add_sub_cancel]`. Then use the resulting hypothesis. Use `choose a ha using hlim`.

Use `⟨Φ.symm fun t => PowerSeries.mk (a t), fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, cp_mem_equiv _ Φ]`. Introduce `t`. Rewrite using `[cp_mem_pow_iff]`. Introduce `k hk`.

Rewrite using `[map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply, map_sub, coeff_mk]`. Use `ha t k (n - k)` as an intermediate fact. Rewrite `this` using `[Nat.sub_add_cancel hk.le]`. Then use the resulting hypothesis.
-/
theorem cp_complete (l : O) (hO : IsAdicComplete (Ideal.span {l}) O) {M : Type}
    [AddCommGroup M] [Module (PowerSeries O) M] {r : ℕ}
    (Φ : M ≃ₗ[PowerSeries O] (Fin r → PowerSeries O)) :
    IsAdicComplete (Ideal.span {C l, X} : Ideal (PowerSeries O)) M where
  haus' := by
    intro x hx
    apply Φ.injective
    rw [map_zero]
    funext t
    ext k
    rw [Pi.zero_apply, map_zero]
    apply cp_O_haus hO
    intro n
    have h1 := hx (n + k + 1)
    rw [SModEq.zero, cp_mem_equiv _ Φ] at h1
    have h2 := (cp_mem_pow_iff l _ _).1 (h1 t) k (by omega)
    exact (pow_dvd_pow l (by omega)).trans h2
  prec' := by
    intro f hf
    have hc : ∀ (t : Fin r) (k m n : ℕ), m ≤ n → k < m →
        l ^ (m - k) ∣ coeff k (Φ (f m) t) - coeff k (Φ (f n) t) := by
      intro t k m n hmn hk
      have h1 := hf hmn
      rw [SModEq.sub_mem, cp_mem_equiv _ Φ] at h1
      have h2 := (cp_mem_pow_iff l _ _).1 (h1 t) k hk
      rwa [map_sub, Pi.sub_apply, map_sub] at h2
    have hlim : ∀ (t : Fin r) (k : ℕ), ∃ a : O, ∀ s, l ^ s ∣ coeff k (Φ (f (s + k)) t) - a := by
      intro t k
      apply cp_O_prec hO (fun s => coeff k (Φ (f (s + k)) t))
      intro m n hmn
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [pow_zero]
        exact one_dvd _
      · have := hc t k (m + k) (n + k) (by omega) (by omega)
        rwa [Nat.add_sub_cancel] at this
    choose a ha using hlim
    refine ⟨Φ.symm fun t => PowerSeries.mk (a t), fun n => ?_⟩
    rw [SModEq.sub_mem, cp_mem_equiv _ Φ]
    intro t
    rw [cp_mem_pow_iff]
    intro k hk
    rw [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply, map_sub, coeff_mk]
    have := ha t k (n - k)
    rwa [Nat.sub_add_cancel hk.le] at this

end cp

section cplat
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

/- English proof (translation)
Take `⟨r, e, hLI, he⟩` from `h`. Conclude with `⟨r, ⟨(LinearEquiv.ofEq _ _ he.symm).trans (Module.Basis.span hLI).equivFun⟩⟩`.
-/
theorem cp_coord (L : Lat B n V) {i : ZMod n} (h : L.Free i) :
    ∃ r : ℕ, Nonempty ((L.N i) ≃ₗ[PowerSeries O] (Fin r → PowerSeries O)) := by
  obtain ⟨r, e, hLI, he⟩ := h
  exact ⟨r, ⟨(LinearEquiv.ofEq _ _ he.symm).trans (Module.Basis.span hLI).equivFun⟩⟩

end cplat

end GoodPlacesAlt

open GoodPlacesAlt IdempotentNormalFormsRhoFacts

/- English proof (translation)
Introduce `O _ B n _ V _ _ L hO hF i`. Take `⟨r, ⟨Φ⟩⟩` from `cp_coord L (hF i)`. Conclude with `cp_complete (B.ℓ : O) hO Φ`.
-/
theorem completion_holds : CompleteOf := by
  intro O _ B n _ V _ _ L hO hF i
  obtain ⟨r, ⟨Φ⟩⟩ := cp_coord L (hF i)
  exact cp_complete (B.ℓ : O) hO Φ

/- English proof (translation)
Introduce `O _ B n _ V _ _ L hF i v hv h0`. Take `⟨r, ⟨Φ⟩⟩` from `cp_coord L (hF i)`. Establish `h1 : Φ ⟨v, hv⟩ = 0`. Establish `h2 : (X : PowerSeries O) • Φ ⟨v, hv⟩ = 0`. Rewrite using `[← map_smul]`.

Establish `: (X : PowerSeries O) • (⟨v, hv⟩ : L.N i) = 0` using `Subtype.ext h0`. Rewrite using `[this, map_zero]`. Use function extensionality and compare the values at `t`. Use extensionality with `k`. Establish `h3` using `congrArg (coeff (k + 1)) (congrFun h2 t)`.

Rewrite `h3` using `[Pi.smul_apply, smul_eq_mul, coeff_succ_X_mul]`. Then use the resulting hypothesis. Establish `h4 : (⟨v, hv⟩ : L.N i) = 0` using `Φ.injective (by rw [h1, map_zero])`. Conclude with `congrArg Subtype.val h4`.
-/
theorem X_regular_on_lattice : XRegOf := by
  intro O _ B n _ V _ _ L hF i v hv h0
  obtain ⟨r, ⟨Φ⟩⟩ := cp_coord L (hF i)
  have h1 : Φ ⟨v, hv⟩ = 0 := by
    have h2 : (X : PowerSeries O) • Φ ⟨v, hv⟩ = 0 := by
      rw [← map_smul]
      have : (X : PowerSeries O) • (⟨v, hv⟩ : L.N i) = 0 := Subtype.ext h0
      rw [this, map_zero]
    funext t
    ext k
    have h3 := congrArg (coeff (k + 1)) (congrFun h2 t)
    rwa [Pi.smul_apply, smul_eq_mul, coeff_succ_X_mul] at h3
  have h4 : (⟨v, hv⟩ : L.N i) = 0 := Φ.injective (by rw [h1, map_zero])
  exact congrArg Subtype.val h4

open GoodPlacesAlt IdempotentNormalFormsRhoFacts

/- English proof (translation)
Introduce `_ _ _ _ ϖ B j M g hϖ hd h0 h3` and use `satA_of ϖ B j M g hϖ hd h0 (e3it B h3)`.
-/
theorem saturation_first_form_holds : SatAOf :=
  fun _ _ _ _ ϖ B j M g hϖ hd h0 h3 => satA_of ϖ B j M g hϖ hd h0 (e3it B h3)

/- English proof (translation)
Introduce `_ _ B j M g sig hl hj h3 hs` and use `trunc_of B j M g sig hl hj (e3it B h3 j) (e2 B (by omega) h3 (j - 1)) hs`.
-/
theorem truncation_holds : TruncOf :=
  fun _ _ B j M g sig hl hj h3 hs =>
    trunc_of B j M g sig hl hj (e3it B h3 j) (e2 B (by omega) h3 (j - 1)) hs

/- English proof (translation)
Introduce `O _ _ _ ϖ B u₁ n _ Cu j M g G sig Mi V _ _ L hϖ hd h0 hp hl hj h3 h4u hG hs hP9 hP5 hMi hthin hfree hcomp hxreg hlt`. Establish `hF1` using `lattice_filtration_first_form O B n M V L Mi h3 hP5 hMi`. Establish `hsat` using `saturation_first_form_holds O ϖ B j M g hϖ hd h0 h3`. Establish `htr` using `truncation_holds O B j M g sig hl hj h3 hs`. Conclude with `⟨hP9, hF1.2, lattice_filtration_second_form O B n M V L h3 hF1.1 hcomp hxreg, fun c hc => lattice_induction_lemma_holds O B n j M g G V L c (by omega) (fun k h1 h2 => lattice_exponent_property_mono L (hP5 _) (hthin c hc k h1 h2)), fun c _ => second_rule_first_form O B n j M g sig …`.
-/
theorem good_lattice_holds : LatGoodOf := by
  intro O _ _ _ ϖ B u₁ n _ Cu j M g G sig Mi V _ _ L hϖ hd h0 hp hl hj h3 h4u hG hs hP9 hP5 hMi
    hthin hfree hcomp hxreg hlt
  have hF1 := lattice_filtration_first_form O B n M V L Mi h3 hP5 hMi
  have hsat := saturation_first_form_holds O ϖ B j M g hϖ hd h0 h3
  have htr := truncation_holds O B j M g sig hl hj h3 hs
  exact ⟨hP9, hF1.2, lattice_filtration_second_form O B n M V L h3 hF1.1 hcomp hxreg,
    fun c hc => lattice_induction_lemma_holds O B n j M g G V L c (by omega)
      (fun k h1 h2 => lattice_exponent_property_mono L (hP5 _) (hthin c hc k h1 h2)),
    fun c _ => second_rule_first_form O B n j M g sig V L c htr (height_bound_holds O B u₁ n M V L c hp h4u hP9),
    fun c _ => gamma_injective_holds O B u₁ n M V L c h4u hP9,
    fun c hc => saturation_holds_alt O B n j _ V L c hsat (hfree c hc), hlt⟩

/- English proof (translation)
Introduce `O _ _ _ ϖ B n _ Cu j M g G sig Mi V _ _ L hϖ hd h0 hp hl hj hO h3 h4 hG hs hP9 hP5 hMi hthin hfree hF hlt`. Take `⟨u₁, h4u⟩` from `one_add_unit_pow_formula O ϖ B hϖ hd hp hl h4`. Conclude with `good_lattice_holds O ϖ B u₁ n Cu j M g G sig Mi V L hϖ hd h0 hp hl hj h3 h4u hG hs hP9 hP5 hMi hthin hfree (completion_holds O B n V L hO hF) (X_regular_on_lattice O B n V L hF) hlt`.
-/
theorem good_lattice_primitive : LatGoodPrim := by
  intro O _ _ _ ϖ B n _ Cu j M g G sig Mi V _ _ L hϖ hd h0 hp hl hj hO h3 h4 hG hs hP9 hP5 hMi
    hthin hfree hF hlt
  obtain ⟨u₁, h4u⟩ := one_add_unit_pow_formula O ϖ B hϖ hd hp hl h4
  exact good_lattice_holds O ϖ B u₁ n Cu j M g G sig Mi V L hϖ hd h0 hp hl hj h3 h4u hG hs hP9 hP5
    hMi hthin hfree (completion_holds O B n V L hO hF) (X_regular_on_lattice O B n V L hF) hlt

/- English proof (translation)
Introduce `O _ _ _ ϖ B n _ Cu j M g G rr Mi hi H V₂ V₀ _ _ _ _ L₂ L₀ e₀ Y hϖ hd h0 h3 hG hlift hP9 hP6 hX hM5 hh5 hthin hH hfree hfrob`. Establish `hsat` using `saturation_first_form_holds O ϖ B j M g hϖ hd h0 h3`. Conclude with `⟨hlift, hP9, extension_complete_holds O B n V₂ V₀ L₂ L₀ Y hP6 hX, fun c hc => lattice_induction_lemma_holds O B n j M g G Y.VY Y.LY c (by omega) (fun k h1 h2 => lattice_exponent_property_mono Y.LY (hM5 _) (hthin c hc k h1 h2)), fun c hc => saturation_holds_alt O B n j _ Y.VY Y.LY …`.
-/
theorem extension_good_holds : ExtGoodOf := by
  intro O _ _ _ ϖ B n _ Cu j M g G rr Mi hi H V₂ V₀ _ _ _ _ L₂ L₀ e₀ Y hϖ hd h0 h3 hG hlift hP9
    hP6 hX hM5 hh5 hthin hH hfree hfrob
  have hsat := saturation_first_form_holds O ϖ B j M g hϖ hd h0 h3
  exact ⟨hlift, hP9, extension_complete_holds O B n V₂ V₀ L₂ L₀ Y hP6 hX,
    fun c hc => lattice_induction_lemma_holds O B n j M g G Y.VY Y.LY c (by omega)
      (fun k h1 h2 => lattice_exponent_property_mono Y.LY (hM5 _) (hthin c hc k h1 h2)),
    fun c hc => saturation_holds_alt O B n j _ Y.VY Y.LY c hsat (hfree c hc),
    fun c hc => pullback_lemma_holds O B n Y.VY Y.LY c (Cu.ell c) (fun s => hi (c - (s : ZMod n))) (H c)
      (fun s _ => hh5 _) (hH c hc),
    fun c hc => extension_generated_holds O B n V₂ V₀ L₂ L₀ Y _ _ _ hP6 (hfrob c hc)⟩

end Formalism.ExponentWindows.E
