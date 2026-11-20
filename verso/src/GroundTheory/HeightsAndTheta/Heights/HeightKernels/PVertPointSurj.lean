import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace VerticalPointSurjective

variable {T : Type} [Fintype T]

omit [Fintype T] in

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp only [aeval_C]`. Rewrite using `[eq_intCast, eq_intCast, map_intCast]`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p n hp => simp [hp]`.
-/
theorem ringHom_aeval {A A' : Type*} [CommRing A] [CommRing A'] [Algebra ℤ A] (f : A →+* A')
    (z : (Σ _ : Unit, T) → A) (g : MRing (fun _ : Unit => T)) :
    f (aeval z g) = aeval (fun p => f (z p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; rw [eq_intCast, eq_intCast, map_intCast]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

/- English proof (translation)
Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`.

Establish `hdeg : ∑ p : (Σ _ : Unit, T), m p = d`. Rewrite using `[Fintype.sum_sigma, Fintype.sum_unique]`. Conclude with `hg m hm default`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_smul_of_homog {S : Type*} [CommRing S] {g : MRing (fun _ : Unit => T)} {d : ℕ}
    (hg : IsMultiHomog g (fun _ => d)) (c : S) (z : (Σ _ : Unit, T) → S) :
    aeval (fun p => c * z p) g = c ^ d * aeval z g := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have hdeg : ∑ p : (Σ _ : Unit, T), m p = d := by
    rw [Fintype.sum_sigma, Fintype.sum_unique]
    exact hg m hm default
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

variable {K' : Type} [Field K']

/- English proof (translation)
Establish `h` using `aeval_smul_of_homog hg (y ⟨(), t⟩)⁻¹ y`. Rewrite using `[show (fun p => y p / y ⟨(), t⟩) = fun p => (y ⟨(), t⟩)⁻¹ * y p from`. Use function extensionality and compare the values at `fun p => by rw [div_eq_inv_mul], h, inv_pow, div_eq_inv_mul]`.
-/
theorem aeval_ratio_of_homog (y : (Σ _ : Unit, T) → K') (t : T) {g : MRing (fun _ : Unit => T)}
    {d : ℕ} (hg : IsMultiHomog g (fun _ => d)) :
    aeval (fun p => y p / y ⟨(), t⟩) g = aeval y g / y ⟨(), t⟩ ^ d := by
  have h := aeval_smul_of_homog hg (y ⟨(), t⟩)⁻¹ y
  rw [show (fun p => y p / y ⟨(), t⟩) = fun p => (y ⟨(), t⟩)⁻¹ * y p from
    funext fun p => by rw [div_eq_inv_mul], h, inv_pow, div_eq_inv_mul]

/- English proof (translation)
Rewrite using `[mCoordIdeal, RingHom.mem_ker, HilbertSamuel.SectionBounded.mConeMap_homog y hg, mul_eq_zero, C_eq_zero]`. Conclude with `or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))`.
-/
theorem mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ _ : Unit, T) → Ω)
    {g : MRing (fun _ : Unit => T)} {d : ℕ} (hg : IsMultiHomog g (fun _ => d)) :
    g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  rw [mCoordIdeal, RingHom.mem_ker, HilbertSamuel.SectionBounded.mConeMap_homog y hg, mul_eq_zero,
    C_eq_zero]
  exact or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))

/- English proof (translation)
Rewrite using `[mem_mCoordIdeal_iff y (HilbertSamuel.SectionBounded.homog_sub hf hg), map_sub, h, sub_self]`.
-/
theorem sub_mem_mCoordIdeal {Ω : Type} [Field Ω] (y : (Σ _ : Unit, T) → Ω)
    {f g : MRing (fun _ : Unit => T)} {d : ℕ} (hf : IsMultiHomog f (fun _ => d))
    (hg : IsMultiHomog g (fun _ => d)) (h : aeval y f = aeval y g) : f - g ∈ mCoordIdeal y := by
  rw [mem_mCoordIdeal_iff y (HilbertSamuel.SectionBounded.homog_sub hf hg), map_sub, h, sub_self]

/- English proof (translation)
The claim follows from `HilbertSamuel.SectionBounded.homog_congr hf fun _ => h`.
-/
theorem homogDeg {f : MRing (fun _ : Unit => T)} {a b : ℕ} (hf : IsMultiHomog f (fun _ => a))
    (h : a = b) : IsMultiHomog f (fun _ => b) :=
  HilbertSamuel.SectionBounded.homog_congr hf fun _ => h

/- English proof (translation)
The claim follows from `HilbertSamuel.SectionBounded.homog_congr (HilbertSamuel.SectionBounded.homog_mul hf hg) fun _ => rfl`.
-/
theorem homogMul {f g : MRing (fun _ : Unit => T)} {a b : ℕ} (hf : IsMultiHomog f (fun _ => a))
    (hg : IsMultiHomog g (fun _ => b)) : IsMultiHomog (f * g) (fun _ => a + b) :=
  HilbertSamuel.SectionBounded.homog_congr (HilbertSamuel.SectionBounded.homog_mul hf hg) fun _ => rfl

/- English proof (translation)
The claim follows from `HilbertSamuel.SectionBounded.homog_congr (HilbertSamuel.SectionBounded.homog_X _) fun k => by cases k; simp`.
-/
theorem homogXt (t : T) : IsMultiHomog (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) (fun _ => 1) :=
  HilbertSamuel.SectionBounded.homog_congr (HilbertSamuel.SectionBounded.homog_X _) fun k => by
    cases k; simp

/- English proof (translation)
The claim follows from `HilbertSamuel.SectionBounded.homog_congr (HilbertSamuel.SectionBounded.homog_pow (homogXt t) n) fun _ => by simp`.
-/
theorem homogXtPow (t : T) (n : ℕ) :
    IsMultiHomog ((X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ^ n) (fun _ => n) :=
  HilbertSamuel.SectionBounded.homog_congr (HilbertSamuel.SectionBounded.homog_pow (homogXt t) n)
    fun _ => by simp

/- English proof (translation)
Establish `hc : (c : K') ∈ chartRingZ y (fun _ => t)` using `mem_curveRing.mp c.2 (fun _ => t) (fun _ => ht)`. Take `⟨δ, g, hg, hgy⟩` from `HilbertSamuel.SectionBounded.exists_form_of_mem_chartRingZ y (fun _ => t) (fun _ => ht) hc`. Use `⟨δ (), g, HilbertSamuel.SectionBounded.homog_congr hg fun k => by cases k; rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[hgy, Fintype.prod_unique]`.
-/
theorem exists_form (y : (Σ _ : Unit, T) → K') (t : T) (ht : y ⟨(), t⟩ ≠ 0) (c : curveRing y) :
    ∃ (e : ℕ) (g : MRing (fun _ : Unit => T)), IsMultiHomog g (fun _ => e) ∧
      aeval y g = (c : K') * y ⟨(), t⟩ ^ e := by
  have hc : (c : K') ∈ chartRingZ y (fun _ => t) := mem_curveRing.mp c.2 (fun _ => t) (fun _ => ht)
  obtain ⟨δ, g, hg, hgy⟩ :=
    HilbertSamuel.SectionBounded.exists_form_of_mem_chartRingZ y (fun _ => t) (fun _ => ht) hc
  refine ⟨δ (), g, HilbertSamuel.SectionBounded.homog_congr hg fun k => by cases k; rfl, ?_⟩
  rw [hgy, Fintype.prod_unique]

def formSet (y : (Σ _ : Unit, T) → K') (t : T) (Q : Ideal (MRing (fun _ : Unit => T))) :
    Set (curveRing y) :=
  {c | ∃ (e : ℕ) (g : MRing (fun _ : Unit => T)), IsMultiHomog g (fun _ => e) ∧
    aeval y g = (c : K') * y ⟨(), t⟩ ^ e ∧ g ∈ Q}

/- English proof (translation)
Rewrite using `[formSet, Set.mem_ofPred_eq]`. Conclude with `⟨e, g, hg, hv, hgQ⟩`.
-/
theorem mem_formSet_of {y : (Σ _ : Unit, T) → K'} {t : T} {Q : Ideal (MRing (fun _ : Unit => T))}
    {c : curveRing y} (e : ℕ) {g : MRing (fun _ : Unit => T)} (hg : IsMultiHomog g (fun _ => e))
    (hv : aeval y g = (c : K') * y ⟨(), t⟩ ^ e) (hgQ : g ∈ Q) : c ∈ formSet y t Q := by
  rw [formSet, Set.mem_ofPred_eq]
  exact ⟨e, g, hg, hv, hgQ⟩

/- English proof (translation)
Take `⟨e1, g1, hg1, hv1, hQ1⟩` from `h1`. Take `⟨e2, g2, hg2, hv2, hQ2⟩` from `h2`. Establish `H1` using `homogMul hg1 (homogXtPow t e2)`. Establish `H2` using `homogDeg (homogMul hg2 (homogXtPow t e1)) (show e2 + e1 = e1 + e2 by omega)`. Establish `H3` using `HilbertSamuel.SectionBounded.homog_add H1 H2`.

Rewrite using `[formSet, Set.mem_ofPred_eq]`. Use `⟨e1 + e2, _, H3, ?_, Q.add_mem (Q.mul_mem_right _ hQ1) (Q.mul_mem_right _ hQ2)⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, map_pow, map_pow, aeval_X, hv1, hv2, Subring.coe_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem formSet_add (y : (Σ _ : Unit, T) → K') (t : T) (Q : Ideal (MRing (fun _ : Unit => T)))
    {c1 c2 : curveRing y} (h1 : c1 ∈ formSet y t Q) (h2 : c2 ∈ formSet y t Q) :
    c1 + c2 ∈ formSet y t Q := by
  obtain ⟨e1, g1, hg1, hv1, hQ1⟩ := h1
  obtain ⟨e2, g2, hg2, hv2, hQ2⟩ := h2
  have H1 := homogMul hg1 (homogXtPow t e2)
  have H2 := homogDeg (homogMul hg2 (homogXtPow t e1)) (show e2 + e1 = e1 + e2 by omega)
  have H3 := HilbertSamuel.SectionBounded.homog_add H1 H2
  rw [formSet, Set.mem_ofPred_eq]
  refine ⟨e1 + e2, _, H3, ?_, Q.add_mem (Q.mul_mem_right _ hQ1) (Q.mul_mem_right _ hQ2)⟩
  rw [map_add, map_mul, map_mul, map_pow, map_pow, aeval_X, hv1, hv2, Subring.coe_add]
  ring

/- English proof (translation)
Rewrite using `[formSet, Set.mem_ofPred_eq]`. Conclude with `⟨0, 0, HilbertSamuel.SectionBounded.homog_zero _, by simp, Q.zero_mem⟩`.
-/
theorem formSet_zero (y : (Σ _ : Unit, T) → K') (t : T) (Q : Ideal (MRing (fun _ : Unit => T))) :
    (0 : curveRing y) ∈ formSet y t Q := by
  rw [formSet, Set.mem_ofPred_eq]
  exact ⟨0, 0, HilbertSamuel.SectionBounded.homog_zero _, by simp, Q.zero_mem⟩

/- English proof (translation)
Take `⟨e2, g2, hg2, hv2, hQ2⟩` from `h2`. Take `⟨e, h, hh, hv⟩` from `exists_form y t ht c`. Establish `H` using `homogMul hh hg2`. Rewrite using `[formSet, Set.mem_ofPred_eq]`. Use `⟨e + e2, _, H, ?_, Q.mul_mem_left _ hQ2⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hv, hv2, Subring.coe_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem formSet_mul (y : (Σ _ : Unit, T) → K') (t : T) (ht : y ⟨(), t⟩ ≠ 0)
    (Q : Ideal (MRing (fun _ : Unit => T))) (c : curveRing y) {c2 : curveRing y}
    (h2 : c2 ∈ formSet y t Q) : c * c2 ∈ formSet y t Q := by
  obtain ⟨e2, g2, hg2, hv2, hQ2⟩ := h2
  obtain ⟨e, h, hh, hv⟩ := exists_form y t ht c
  have H := homogMul hh hg2
  rw [formSet, Set.mem_ofPred_eq]
  refine ⟨e + e2, _, H, ?_, Q.mul_mem_left _ hQ2⟩
  rw [map_mul, hv, hv2, Subring.coe_mul]
  ring

def formIdeal (y : (Σ _ : Unit, T) → K') (t : T) (ht : y ⟨(), t⟩ ≠ 0)
    (Q : Ideal (MRing (fun _ : Unit => T))) : Ideal (curveRing y) where
  carrier := formSet y t Q
  add_mem' := fun h1 h2 => formSet_add y t Q h1 h2
  zero_mem' := formSet_zero y t Q
  smul_mem' := fun c _ h2 => formSet_mul y t ht Q c h2

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_formIdeal {y : (Σ _ : Unit, T) → K'} {t : T} {ht : y ⟨(), t⟩ ≠ 0}
    {Q : Ideal (MRing (fun _ : Unit => T))} {c : curveRing y} :
    c ∈ formIdeal y t ht Q ↔ c ∈ formSet y t Q :=
  Iff.rfl

/- English proof (translation)
Establish `hXtpowQ : ∀ n, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ^ n ∉ Q` using `fun n h => hXt (hQW (hQ.mem_of_pow_mem _ h))`. Establish `htr : ∀ {f g : MRing (fun _ : Unit => T)} {n : ℕ}, IsMultiHomog f (fun _ => n) → IsMultiHomog g (fun _ => n) → aeval y f = aeval y g → g ∈ Q → f ∈ Q`. Introduce `f g n hf hg he hgQ`. Establish `h1` using `Q.add_mem (hPQ (sub_mem_mCoordIdeal y hf hg he)) hgQ`. Rewrite `h1` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Establish `hIQm : formIdeal y t ht Q ≤ m`. Introduce `c hc`. Take `⟨e, g, hg, hv, hgQ⟩` from `mem_formIdeal.mp hc`. Conclude with `(hWB c hg hv).mp (hQW hgQ)`. Establish `haIQ : a ∈ formIdeal y t ht Q`.

Take `⟨e, h, hh, hv⟩` from `exists_form y t ht b`. Use `mem_formIdeal.mpr (mem_formSet_of (e + 1) (homogMul hh hs) ?_ (Q.mul_mem_left _ hsQ))` and prove the remaining obligations. Rewrite using `[map_mul, hv]`. Take the linear combination `(y ⟨(), t⟩ ^ e) * hbx`. Establish `hIQprime : (formIdeal y t ht Q).IsPrime`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.eq_top_iff_one]`. Introduce `h1`. Take `⟨e, g, hg, hv, hgQ⟩` from `mem_formIdeal.mp h1`. Use `hXtpowQ e (htr (homogXtPow t e) hg ?_ hgQ)` and prove the remaining obligations.

Rewrite using `[map_pow, aeval_X, hv]`. Simplify using the standard rewrite rules. Introduce `c1 c2 h12`. Take `⟨e, g, hg, hv, hgQ⟩` from `mem_formIdeal.mp h12`. Take `⟨e1, h1, hh1, hv1⟩` from `exists_form y t ht c1`.

Take `⟨e2, h2, hh2, hv2⟩` from `exists_form y t ht c2`. Establish `hf : h1 * h2 * X ⟨(), t⟩ ^ e ∈ Q`. Use `htr (homogMul (homogMul hh1 hh2) (homogXtPow t e)) (homogDeg (homogMul hg (homogXtPow t (e1 + e2))) (by omega)) ?_ (Q.mul_mem_right _ hgQ)` and prove the remaining obligations. Simplify using `only [map_mul, map_pow, aeval_X, hv1, hv2, hv]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Break down `hQ.mem_or_mem hf with h12 | h3` into its components or cases. Break down `hQ.mem_or_mem h12 with h1Q | h2Q` into its components or cases. Conclude with `Or.inl (mem_formIdeal.mpr (mem_formSet_of e1 hh1 hv1 h1Q))`. Conclude with `Or.inr (mem_formIdeal.mpr (mem_formSet_of e2 hh2 hv2 h2Q))`.

Conclude with `absurd h3 (hXtpowQ e)`. Establish `hIQmax : (formIdeal y t ht Q).IsMaximal`. Establish `hcomap : (formIdeal y t ht Q).comap (algebraMap ℤ (curveRing y)) ≠ ⊥` using `Ideal.comap_ne_bot_of_integral_mem ha0 haIQ (Algebra.IsIntegral.isIntegral a)`. Establish `: ((formIdeal y t ht Q).comap (algebraMap ℤ (curveRing y))).IsPrime` using `Ideal.IsPrime.comap _`. Conclude with `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (IsPrime.to_maximal_ideal hcomap)`.

Establish `hIQeq : formIdeal y t ht Q = m` using `hIQmax.eq_of_le hm.ne_top hIQm`. Take `⟨S, hS, hWS⟩` from `hWforms`. Introduce `f hfW`. Rewrite `hfW` using `[hWS]`. Use `(Ideal.span_le.mpr ?_) hfW` and prove the remaining obligations.

Introduce `f hf`. Take `⟨δ, hδ⟩` from `hS f hf`. Establish `hf' : IsMultiHomog f (fun _ => δ ())` using `HilbertSamuel.SectionBounded.homog_congr hδ fun k => by cases k; rfl`. Establish `hfW' : f ∈ W` using `by rw [hWS]; exact Ideal.subset_span hf`. Take `⟨a', b', ha'm, hb'm, hv'⟩` from `hWfrac hf' hfW'`.

Establish `ha'IQ : a' ∈ formIdeal y t ht Q` using `by rw [hIQeq]; exact ha'm`. Take `⟨ea, ga, hga, hva, hgaQ⟩` from `mem_formIdeal.mp ha'IQ`. Take `⟨eb, hb, hhb, hvb⟩` from `exists_form y t ht b'`. Establish `hbQ : hb ∉ Q`. Introduce `h`.

Establish `hbIQ : b' ∈ formIdeal y t ht Q` using `mem_formIdeal.mpr (mem_formSet_of eb hhb hvb h)`. Rewrite `hbIQ` using `[hIQeq]`. Conclude with `hb'm hbIQ`. Establish `h1 : hb * f * X ⟨(), t⟩ ^ ea ∈ Q`. Use `htr (homogMul (homogMul hhb hf') (homogXtPow t ea)) (homogDeg (homogMul hga (homogXtPow t (eb + δ ()))) (by omega)) ?_ (Q.mul_mem_right _ hgaQ)` and prove the remaining obligations.

Simplify using `only [map_mul, map_pow, aeval_X, hvb, hva]`. Take the linear combination `(y ⟨(), t⟩ ^ (eb + ea)) * hv'`. Break down `hQ.mem_or_mem h1 with h2 | h3` into its components or cases. Break down `hQ.mem_or_mem h2 with h4 | h5` into its components or cases. Conclude with `absurd h4 hbQ`.

Conclude with `h5`. Conclude with `absurd h3 (hXtpowQ ea)`.
-/
theorem le_of_minimal_prime_over_coord (y : (Σ _ : Unit, T) → K') (t : T) (ht : y ⟨(), t⟩ ≠ 0)
    (hfin : Module.Finite ℤ (curveRing y)) (m : Ideal (curveRing y)) (hm : m.IsMaximal)
    (W Q : Ideal (MRing (fun _ : Unit => T))) (hQ : Q.IsPrime) (hPQ : mCoordIdeal y ≤ Q) (hQW : Q ≤ W)
    (hXt : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W)
    (hWB : ∀ {g : MRing (fun _ : Unit => T)} {d : ℕ} (c : curveRing y),
      IsMultiHomog g (fun _ => d) → aeval y g = (c : K') * y ⟨(), t⟩ ^ d → (g ∈ W ↔ c ∈ m))
    (hWfrac : ∀ {f : MRing (fun _ : Unit => T)} {n : ℕ}, IsMultiHomog f (fun _ => n) →
      f ∈ W → ∃ a' b' : curveRing y, a' ∈ m ∧ b' ∉ m ∧
        ((b' : curveRing y) : K') * aeval y f = (a' : K') * y ⟨(), t⟩ ^ n)
    (hWforms : IsMultiHomogIdeal W) {a b : curveRing y} (ha0 : a ≠ 0)
    {s : MRing (fun _ : Unit => T)} (hs : IsMultiHomog s (fun _ => 1)) (hsQ : s ∈ Q)
    (hbx : (b : K') * aeval y s = (a : K') * y ⟨(), t⟩) : W ≤ Q := by
  have hXtpowQ : ∀ n, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ^ n ∉ Q :=
    fun n h => hXt (hQW (hQ.mem_of_pow_mem _ h))
  have htr : ∀ {f g : MRing (fun _ : Unit => T)} {n : ℕ}, IsMultiHomog f (fun _ => n) →
      IsMultiHomog g (fun _ => n) → aeval y f = aeval y g → g ∈ Q → f ∈ Q := by
    intro f g n hf hg he hgQ
    have h1 := Q.add_mem (hPQ (sub_mem_mCoordIdeal y hf hg he)) hgQ
    rwa [sub_add_cancel] at h1
  have hIQm : formIdeal y t ht Q ≤ m := by
    intro c hc
    obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp hc
    exact (hWB c hg hv).mp (hQW hgQ)
  have haIQ : a ∈ formIdeal y t ht Q := by
    obtain ⟨e, h, hh, hv⟩ := exists_form y t ht b
    refine mem_formIdeal.mpr (mem_formSet_of (e + 1) (homogMul hh hs) ?_ (Q.mul_mem_left _ hsQ))
    rw [map_mul, hv]
    linear_combination (y ⟨(), t⟩ ^ e) * hbx
  have hIQprime : (formIdeal y t ht Q).IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one]
      intro h1
      obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp h1
      refine hXtpowQ e (htr (homogXtPow t e) hg ?_ hgQ)
      rw [map_pow, aeval_X, hv]
      simp
    · intro c1 c2 h12
      obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp h12
      obtain ⟨e1, h1, hh1, hv1⟩ := exists_form y t ht c1
      obtain ⟨e2, h2, hh2, hv2⟩ := exists_form y t ht c2
      have hf : h1 * h2 * X ⟨(), t⟩ ^ e ∈ Q := by
        refine htr (homogMul (homogMul hh1 hh2) (homogXtPow t e))
          (homogDeg (homogMul hg (homogXtPow t (e1 + e2))) (by omega)) ?_ (Q.mul_mem_right _ hgQ)
        simp only [map_mul, map_pow, aeval_X, hv1, hv2, hv]
        push_cast
        ring
      rcases hQ.mem_or_mem hf with h12 | h3
      · rcases hQ.mem_or_mem h12 with h1Q | h2Q
        · exact Or.inl (mem_formIdeal.mpr (mem_formSet_of e1 hh1 hv1 h1Q))
        · exact Or.inr (mem_formIdeal.mpr (mem_formSet_of e2 hh2 hv2 h2Q))
      · exact absurd h3 (hXtpowQ e)
  have hIQmax : (formIdeal y t ht Q).IsMaximal := by
    have hcomap : (formIdeal y t ht Q).comap (algebraMap ℤ (curveRing y)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha0 haIQ (Algebra.IsIntegral.isIntegral a)
    have : ((formIdeal y t ht Q).comap (algebraMap ℤ (curveRing y))).IsPrime := Ideal.IsPrime.comap _
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (IsPrime.to_maximal_ideal hcomap)
  have hIQeq : formIdeal y t ht Q = m := hIQmax.eq_of_le hm.ne_top hIQm

  obtain ⟨S, hS, hWS⟩ := hWforms
  intro f hfW
  rw [hWS] at hfW
  refine (Ideal.span_le.mpr ?_) hfW
  intro f hf
  obtain ⟨δ, hδ⟩ := hS f hf
  have hf' : IsMultiHomog f (fun _ => δ ()) :=
    HilbertSamuel.SectionBounded.homog_congr hδ fun k => by cases k; rfl
  have hfW' : f ∈ W := by rw [hWS]; exact Ideal.subset_span hf
  obtain ⟨a', b', ha'm, hb'm, hv'⟩ := hWfrac hf' hfW'
  have ha'IQ : a' ∈ formIdeal y t ht Q := by rw [hIQeq]; exact ha'm
  obtain ⟨ea, ga, hga, hva, hgaQ⟩ := mem_formIdeal.mp ha'IQ
  obtain ⟨eb, hb, hhb, hvb⟩ := exists_form y t ht b'
  have hbQ : hb ∉ Q := by
    intro h
    have hbIQ : b' ∈ formIdeal y t ht Q := mem_formIdeal.mpr (mem_formSet_of eb hhb hvb h)
    rw [hIQeq] at hbIQ
    exact hb'm hbIQ
  have h1 : hb * f * X ⟨(), t⟩ ^ ea ∈ Q := by
    refine htr (homogMul (homogMul hhb hf') (homogXtPow t ea))
      (homogDeg (homogMul hga (homogXtPow t (eb + δ ()))) (by omega)) ?_ (Q.mul_mem_right _ hgaQ)
    simp only [map_mul, map_pow, aeval_X, hvb, hva]
    linear_combination (y ⟨(), t⟩ ^ (eb + ea)) * hv'
  rcases hQ.mem_or_mem h1 with h2 | h3
  · rcases hQ.mem_or_mem h2 with h4 | h5
    · exact absurd h4 hbQ
    · exact h5
  · exact absurd h3 (hXtpowQ ea)

/- English proof (translation)
Establish `key : ∀ w : LocalizedModule m.primeCompl (R ⧸ Ideal.span {a}), w = 0`. Introduce `w`. Proceed by induction on `w using LocalizedModule.induction_on with`. Consider the case `h c s`. Rewrite using `[← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]`.

Use `⟨⟨a, ha⟩, ?_⟩` and prove the remaining obligations. Take `⟨c', rfl⟩` from `Ideal.Quotient.mk_surjective c`. Rewrite using `[smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)`. Establish `hsub : Subsingleton (LocalizedModule m.primeCompl (R ⧸ Ideal.span {a}))` using `⟨fun u v => by rw [key u, key v]⟩`.

Rewrite using `[locLen, dif_pos ‹m.IsPrime›, Module.length_eq_zero_iff.mpr hsub]`. Both sides reduce to the same expression.
-/
theorem locLen_quot_eq_zero {R : Type*} [CommRing R] (m : Ideal R) [m.IsPrime] {a : R} (ha : a ∉ m) :
    locLen m (R ⧸ Ideal.span {a}) = 0 := by
  have key : ∀ w : LocalizedModule m.primeCompl (R ⧸ Ideal.span {a}), w = 0 := by
    intro w
    induction w using LocalizedModule.induction_on with
    | h c s =>
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
      refine ⟨⟨a, ha⟩, ?_⟩
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def,
        Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
  have hsub : Subsingleton (LocalizedModule m.primeCompl (R ⧸ Ideal.span {a})) :=
    ⟨fun u v => by rw [key u, key v]⟩
  rw [locLen, dif_pos ‹m.IsPrime›, Module.length_eq_zero_iff.mpr hsub]
  rfl

end VerticalPointSurjective

open VerticalPointSurjective in

/- English proof (translation)
Introduce `T _ K' _ _ y s hP hs hsP m hm hlen`. Take `⟨hfin, -, hch⟩` from `hC T K' y hP`. Take `⟨t, hyt, hrat⟩` from `hch m hm`. Establish `hrat'` using `hrat`. Establish `: m.IsPrime` using `hm.isPrime`.

Establish `hunit : ∀ b : m.primeCompl, IsUnit ((curveRing y).subtype (b : curveRing y))`. Introduce `b`. Use `isUnit_iff_ne_zero.mpr fun h => b.2 ?_` and prove the remaining obligations. Establish `hb0 : (b : curveRing y) = 0` using `Subtype.ext h`. Rewrite using `[hb0]`.

Conclude with `m.zero_mem`. Set `L` to `Localization.AtPrime m`. Set `ι : L →+* K'` to `IsLocalization.lift hunit`. Establish `hinj0 : Function.Injective (algebraMap (curveRing y) L)` using `IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors m)`. Establish `hιinj : Function.Injective ι` using `(IsLocalization.lift_injective_iff hunit).mpr fun c c' => ⟨fun h => by rw [hinj0 h], fun h => by rw [Subtype.val_injective h]⟩`.

Establish `hιB : ∀ c : curveRing y, ι (algebraMap _ L c) = c` using `fun c => IsLocalization.lift_eq hunit c`. Establish `hιmk : ∀ (a : curveRing y) (b : m.primeCompl) (v : K'), ι (IsLocalization.mk' L a b) = v ↔ (a : K') = ((b : curveRing y) : K') * v` using `fun a b v => IsLocalization.lift_mk'_spec hunit a v b`. Use `choose α β hβ hαβ using hrat`. Set `ρ : (Σ _ : Unit, T) → L` to `fun p => IsLocalization.mk' L (α p.2) (⟨β p.2, hβ p.2⟩ : m.primeCompl)`. Establish `hιρ : ∀ p, ι (ρ p) = y p / y ⟨(), t⟩`.

Introduce and unpack `⟨⟨⟩, u⟩`. Conclude with `(hιmk _ _ _).mpr (hαβ u).symm`. Establish `hιev : ∀ {g : MRing (fun _ : Unit => T)} {d : ℕ}, IsMultiHomog g (fun _ => d) → ι (aeval ρ g) = aeval y g / y ⟨(), t⟩ ^ d`. Introduce `g d hg`. Rewrite using `[ringHom_aeval ι ρ g, show (fun p => ι (ρ p)) = fun p => y p / y ⟨(), t⟩ from funext hιρ]`.

Conclude with `aeval_ratio_of_homog y t hg`. Establish `hevB : ∀ {g : MRing (fun _ : Unit => T)} {d : ℕ} (c : curveRing y), IsMultiHomog g (fun _ => d) → aeval y g = (c : K') * y ⟨(), t⟩ ^ d → aeval ρ g = algebraMap _ L c`. Introduce `g d c hg hgc`. Apply `hιinj` to reduce the goal to its premises. Rewrite using `[hιev hg, hιB, hgc, mul_div_assoc, div_self (pow_ne_zero _ hyt), mul_one]`.

Set `r : (Σ _ : Unit, T) → IsLocalRing.ResidueField L` to `fun p => IsLocalRing.residue L (ρ p)`. Establish `hWform : ∀ {g : MRing (fun _ : Unit => T)} {d : ℕ}, IsMultiHomog g (fun _ => d) → (g ∈ mCoordIdeal r ↔ aeval ρ g ∈ IsLocalRing.maximalIdeal L)`. Introduce `g d hg`. Rewrite using `[mem_mCoordIdeal_iff r hg, ← IsLocalRing.residue_eq_zero_iff, ringHom_aeval]`. Establish `hWB : ∀ {g : MRing (fun _ : Unit => T)} {d : ℕ} (c : curveRing y), IsMultiHomog g (fun _ => d) → aeval y g = (c : K') * y ⟨(), t⟩ ^ d → (g ∈ mCoordIdeal r ↔ c ∈ m)`.

Introduce `g d c hg hgc`. Rewrite using `[hWform hg, hevB c hg hgc]`. Conclude with `IsLocalization.AtPrime.to_map_mem_maximal_iff L m c`. Establish `hXt : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ mCoordIdeal r`. Rewrite using `[hWB 1 (homogXt t) (by simp)]`.

Conclude with `fun h => hm.ne_top ((Ideal.eq_top_iff_one m).mpr h)`. Establish `hWprime : (mCoordIdeal r).IsPrime` using `RingHom.ker_isPrime _`. Establish `hPW : mCoordIdeal y ≤ mCoordIdeal r`. Take `⟨S, hS, hPS⟩` from `CoordinateConeArithVar.isMultiHomogIdeal y`. Introduce `f hfP`.

Rewrite `hfP` using `[hPS]`. Use `(Ideal.span_le.mpr ?_) hfP` and prove the remaining obligations. Introduce `f hf`. Take `⟨a, ha⟩` from `hS f hf`. Establish `ha' : IsMultiHomog f (fun _ => a ())` using `HilbertSamuel.SectionBounded.homog_congr ha fun k => by cases k; rfl`.

Establish `hfP' : f ∈ mCoordIdeal y` using `by rw [hPS]; exact Ideal.subset_span hf`. Establish `hf0 : aeval y f = ((0 : curveRing y) : K') * y ⟨(), t⟩ ^ a ()`. Rewrite using `[(mem_mCoordIdeal_iff y ha').mp hfP']`. Simplify using the standard rewrite rules. Conclude with `(hWB 0 ha' hf0).mpr m.zero_mem`.

Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.mk'_surjective m.primeCompl (aeval ρ s)`. Simplify using `only at hab`. Establish `hbx : ((b : curveRing y) : K') * aeval y s = (a : K') * y ⟨(), t⟩`. Establish `h1` using `hιev (d := 1) hs`. Rewrite `h1` using `[← hab, pow_one]`.

Rewrite using `[(hιmk a b _).mp h1]`. Clear the denominators using the available nonvanishing facts. Establish `hlenA : locLen m (curveRing y ⧸ Ideal.span {a}) ≠ 0`. Rewrite using `[← hSQ T K' y s hP hs hsP m t hm.isPrime hrat' a b b.2 hbx]` and apply the resulting hypothesis. Establish `ham : a ∈ m`.

Assume the negation of the conclusion as `h`. Conclude with `hlenA (locLen_quot_eq_zero m h)`. Establish `hsW : s ∈ mCoordIdeal r`. Rewrite using `[hWform hs, ← hab]`. Conclude with `(IsLocalization.AtPrime.mk'_mem_maximal_iff L m a b).mpr ham`.

Establish `hJW : mCoordIdeal y ⊔ Ideal.span {s} ≤ mCoordIdeal r` using `sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)`. Establish `hcurve : curvePtIdeal y (mCoordIdeal r) = m`. Apply `le_antisymm` to reduce the goal to its premises. Use `Ideal.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `c ⟨d, g, h, hg, hh, hgW, hhW, hc⟩`.

Establish `hg' : IsMultiHomog g (fun _ => d ())` using `HilbertSamuel.SectionBounded.homog_congr hg fun k => by cases k; rfl`. Establish `hh' : IsMultiHomog h (fun _ => d ())` using `HilbertSamuel.SectionBounded.homog_congr hh fun k => by cases k; rfl`. Establish `heq : algebraMap _ L c * aeval ρ h = aeval ρ g`. Apply `hιinj` to reduce the goal to its premises. Rewrite using `[map_mul, hιB, hιev hh', hιev hg', ← hc, mul_div_assoc]`.

Establish `hmem : algebraMap _ L c * aeval ρ h ∈ IsLocalRing.maximalIdeal L`. Rewrite using `[heq]`. Conclude with `(hWform hg').mp hgW`. Break down `(IsLocalRing.maximalIdeal.isMaximal L).isPrime.mem_or_mem hmem with h1 | h1` into its components or cases. Conclude with `(IsLocalization.AtPrime.to_map_mem_maximal_iff L m c).mp h1`.

Conclude with `absurd ((hWform hh').mpr h1) hhW`. Introduce `c hc`. Take `⟨e, g, hg, hgc⟩` from `exists_form y t hyt c`. Establish `hgW : g ∈ mCoordIdeal r` using `(hWB c hg hgc).mpr hc`. Establish `hXW : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ^ e ∉ mCoordIdeal r` using `fun h => hXt (hWprime.mem_of_pow_mem _ h)`.

Establish `hval : (c : K') * aeval y ((X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ^ e) = aeval y g`. Rewrite using `[map_pow, aeval_X, hgc]`. Establish `key : ∀ h : MRing (fun _ : Unit => T), IsMultiHomog h (fun _ => e) → h ∉ mCoordIdeal r → (c : K') * aeval y h = aeval y g → c ∈ {b : curveRing y | ∃ (d : Unit → ℕ) (g h : MRing (fun _ : Unit => T)), IsMultiHomog g d ∧ IsMultiHomog h d ∧ g ∈ mCoordIdeal r ∧ h ∉ mCoordIdeal r ∧ (b …` using `fun h hh hhW hv => ⟨fun _ => e, g, h, hg, hh, hgW, hhW, hv⟩`. Conclude with `Ideal.subset_span (key _ (homogXtPow t e) hXW hval)`. Establish `ha0 : a ≠ 0`.

Introduce `h0`. Establish `hx0 : aeval y s ≠ 0` using `fun h => hsP ((mem_mCoordIdeal_iff y hs).mpr h)`. Establish `hb0 : ((b : curveRing y) : K') ≠ 0`. Introduce `h`. Apply `b.2` to reduce the goal to its premises.

Rewrite using `[show (b : curveRing y) = 0 from Subtype.ext h]`. Conclude with `m.zero_mem`. Establish `h2` using `hbx`. Rewrite `h2` using `[h0, ZeroMemClass.coe_zero, zero_mul]`. Conclude with `mul_ne_zero hb0 hx0 h2`.

Establish `hWfrac : ∀ {f : MRing (fun _ : Unit => T)} {n : ℕ}, IsMultiHomog f (fun _ => n) → f ∈ mCoordIdeal r → ∃ a' b' : curveRing y, a' ∈ m ∧ b' ∉ m ∧ ((b' : curveRing y) : K') * aeval y f = (a' : K') * y ⟨(), t⟩ ^ n`. Introduce `f n hf hfW`. Take `⟨⟨a', b'⟩, hab'⟩` from `IsLocalization.mk'_surjective m.primeCompl (aeval ρ f)`. Simplify using `only at hab'`. Use `⟨a', b', ?_, b'.2, ?_⟩` and prove the remaining obligations.

Establish `h1` using `(hWform hf).mp hfW`. Rewrite `h1` using `[← hab']`. Conclude with `(IsLocalization.AtPrime.mk'_mem_maximal_iff L m a' b').mp h1`. Establish `h1` using `hιev hf`. Rewrite `h1` using `[← hab']`.

Rewrite using `[(hιmk a' b' _).mp h1]`. Clear the denominators using the available nonvanishing facts. Establish `hmin : ∀ Q : Ideal (MRing (fun _ : Unit => T)), Q.IsPrime → mCoordIdeal y ⊔ Ideal.span {s} ≤ Q → Q ≤ mCoordIdeal r → mCoordIdeal r ≤ Q`. Introduce `Q hQ hJQ hQW`. Establish `hPQ : mCoordIdeal y ≤ Q` using `le_trans le_sup_left hJQ`.

Establish `hsQ : s ∈ Q` using `hJQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))`. Conclude with `le_of_minimal_prime_over_coord y t hyt hfin m hm (mCoordIdeal r) Q hQ hPQ hQW hXt hWB hWfrac (CoordinateConeArithVar.isMultiHomogIdeal r) ha0 hs hsQ hbx`. Establish `hmp : mCoordIdeal r ∈ (mCoordIdeal y ⊔ Ideal.span {s}).minimalPrimes` using `⟨⟨hWprime, hJW⟩, fun Q hQ hQW => hmin Q hQ.1 hQ.2 hQW⟩`. Establish `hD : mCoordIdeal r ∈ divSupp (mCoordIdeal y) s`. Rewrite using `[divSupp, Set.mem_ofPred_eq]`.

Conclude with `⟨hmp, fun _ => ⟨t, hXt⟩⟩`. Conclude with `⟨mCoordIdeal r, hD, hcurve⟩`.
-/
theorem VertPointSurj.proof (hC : CurveCharts.Statement) (hSQ : SectionQuotLocal.Statement) :
    VertPointSurj.Statement := by
  classical
  intro T _ K' _ _ y s hP hs hsP m hm hlen
  obtain ⟨hfin, -, hch⟩ := hC T K' y hP
  obtain ⟨t, hyt, hrat⟩ := hch m hm
  have hrat' := hrat
  have : m.IsPrime := hm.isPrime

  have hunit : ∀ b : m.primeCompl, IsUnit ((curveRing y).subtype (b : curveRing y)) := by
    intro b
    refine isUnit_iff_ne_zero.mpr fun h => b.2 ?_
    have hb0 : (b : curveRing y) = 0 := Subtype.ext h
    rw [hb0]
    exact m.zero_mem
  let L := Localization.AtPrime m
  let ι : L →+* K' := IsLocalization.lift hunit
  have hinj0 : Function.Injective (algebraMap (curveRing y) L) :=
    IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors m)
  have hιinj : Function.Injective ι :=
    (IsLocalization.lift_injective_iff hunit).mpr fun c c' =>
      ⟨fun h => by rw [hinj0 h], fun h => by rw [Subtype.val_injective h]⟩
  have hιB : ∀ c : curveRing y, ι (algebraMap _ L c) = c := fun c => IsLocalization.lift_eq hunit c
  have hιmk : ∀ (a : curveRing y) (b : m.primeCompl) (v : K'),
      ι (IsLocalization.mk' L a b) = v ↔ (a : K') = ((b : curveRing y) : K') * v :=
    fun a b v => IsLocalization.lift_mk'_spec hunit a v b

  choose α β hβ hαβ using hrat
  let ρ : (Σ _ : Unit, T) → L := fun p => IsLocalization.mk' L (α p.2) (⟨β p.2, hβ p.2⟩ : m.primeCompl)
  have hιρ : ∀ p, ι (ρ p) = y p / y ⟨(), t⟩ := by
    rintro ⟨⟨⟩, u⟩
    exact (hιmk _ _ _).mpr (hαβ u).symm
  have hιev : ∀ {g : MRing (fun _ : Unit => T)} {d : ℕ}, IsMultiHomog g (fun _ => d) →
      ι (aeval ρ g) = aeval y g / y ⟨(), t⟩ ^ d := by
    intro g d hg
    rw [ringHom_aeval ι ρ g, show (fun p => ι (ρ p)) = fun p => y p / y ⟨(), t⟩ from funext hιρ]
    exact aeval_ratio_of_homog y t hg
  have hevB : ∀ {g : MRing (fun _ : Unit => T)} {d : ℕ} (c : curveRing y),
      IsMultiHomog g (fun _ => d) → aeval y g = (c : K') * y ⟨(), t⟩ ^ d →
        aeval ρ g = algebraMap _ L c := by
    intro g d c hg hgc
    apply hιinj
    rw [hιev hg, hιB, hgc, mul_div_assoc, div_self (pow_ne_zero _ hyt), mul_one]

  let r : (Σ _ : Unit, T) → IsLocalRing.ResidueField L := fun p => IsLocalRing.residue L (ρ p)
  have hWform : ∀ {g : MRing (fun _ : Unit => T)} {d : ℕ}, IsMultiHomog g (fun _ => d) →
      (g ∈ mCoordIdeal r ↔ aeval ρ g ∈ IsLocalRing.maximalIdeal L) := by
    intro g d hg
    rw [mem_mCoordIdeal_iff r hg, ← IsLocalRing.residue_eq_zero_iff, ringHom_aeval]
  have hWB : ∀ {g : MRing (fun _ : Unit => T)} {d : ℕ} (c : curveRing y),
      IsMultiHomog g (fun _ => d) → aeval y g = (c : K') * y ⟨(), t⟩ ^ d →
        (g ∈ mCoordIdeal r ↔ c ∈ m) := by
    intro g d c hg hgc
    rw [hWform hg, hevB c hg hgc]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff L m c
  have hXt : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ mCoordIdeal r := by
    rw [hWB 1 (homogXt t) (by simp)]
    exact fun h => hm.ne_top ((Ideal.eq_top_iff_one m).mpr h)
  have hWprime : (mCoordIdeal r).IsPrime := RingHom.ker_isPrime _
  have hPW : mCoordIdeal y ≤ mCoordIdeal r := by
    obtain ⟨S, hS, hPS⟩ := CoordinateConeArithVar.isMultiHomogIdeal y
    intro f hfP
    rw [hPS] at hfP
    refine (Ideal.span_le.mpr ?_) hfP
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have ha' : IsMultiHomog f (fun _ => a ()) :=
      HilbertSamuel.SectionBounded.homog_congr ha fun k => by cases k; rfl
    have hfP' : f ∈ mCoordIdeal y := by rw [hPS]; exact Ideal.subset_span hf
    have hf0 : aeval y f = ((0 : curveRing y) : K') * y ⟨(), t⟩ ^ a () := by
      rw [(mem_mCoordIdeal_iff y ha').mp hfP']
      simp
    exact (hWB 0 ha' hf0).mpr m.zero_mem

  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective m.primeCompl (aeval ρ s)
  dsimp only at hab
  have hbx : ((b : curveRing y) : K') * aeval y s = (a : K') * y ⟨(), t⟩ := by
    have h1 := hιev (d := 1) hs
    rw [← hab, pow_one] at h1
    rw [(hιmk a b _).mp h1]
    field_simp
  have hlenA : locLen m (curveRing y ⧸ Ideal.span {a}) ≠ 0 := by
    rwa [← hSQ T K' y s hP hs hsP m t hm.isPrime hrat' a b b.2 hbx]
  have ham : a ∈ m := by
    by_contra h
    exact hlenA (locLen_quot_eq_zero m h)
  have hsW : s ∈ mCoordIdeal r := by
    rw [hWform hs, ← hab]
    exact (IsLocalization.AtPrime.mk'_mem_maximal_iff L m a b).mpr ham
  have hJW : mCoordIdeal y ⊔ Ideal.span {s} ≤ mCoordIdeal r :=
    sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)

  have hcurve : curvePtIdeal y (mCoordIdeal r) = m := by
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro c ⟨d, g, h, hg, hh, hgW, hhW, hc⟩
      have hg' : IsMultiHomog g (fun _ => d ()) :=
        HilbertSamuel.SectionBounded.homog_congr hg fun k => by cases k; rfl
      have hh' : IsMultiHomog h (fun _ => d ()) :=
        HilbertSamuel.SectionBounded.homog_congr hh fun k => by cases k; rfl
      have heq : algebraMap _ L c * aeval ρ h = aeval ρ g := by
        apply hιinj
        rw [map_mul, hιB, hιev hh', hιev hg', ← hc, mul_div_assoc]
      have hmem : algebraMap _ L c * aeval ρ h ∈ IsLocalRing.maximalIdeal L := by
        rw [heq]
        exact (hWform hg').mp hgW
      rcases (IsLocalRing.maximalIdeal.isMaximal L).isPrime.mem_or_mem hmem with h1 | h1
      · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L m c).mp h1
      · exact absurd ((hWform hh').mpr h1) hhW
    · intro c hc
      obtain ⟨e, g, hg, hgc⟩ := exists_form y t hyt c
      have hgW : g ∈ mCoordIdeal r := (hWB c hg hgc).mpr hc
      have hXW : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ^ e ∉ mCoordIdeal r :=
        fun h => hXt (hWprime.mem_of_pow_mem _ h)
      have hval : (c : K') * aeval y ((X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ^ e) = aeval y g := by
        rw [map_pow, aeval_X, hgc]
      have key : ∀ h : MRing (fun _ : Unit => T), IsMultiHomog h (fun _ => e) → h ∉ mCoordIdeal r →
          (c : K') * aeval y h = aeval y g →
          c ∈ {b : curveRing y | ∃ (d : Unit → ℕ) (g h : MRing (fun _ : Unit => T)),
            IsMultiHomog g d ∧ IsMultiHomog h d ∧ g ∈ mCoordIdeal r ∧ h ∉ mCoordIdeal r ∧
              (b : K') * aeval y h = aeval y g} :=
        fun h hh hhW hv => ⟨fun _ => e, g, h, hg, hh, hgW, hhW, hv⟩
      exact Ideal.subset_span (key _ (homogXtPow t e) hXW hval)
  have ha0 : a ≠ 0 := by
    intro h0
    have hx0 : aeval y s ≠ 0 := fun h => hsP ((mem_mCoordIdeal_iff y hs).mpr h)
    have hb0 : ((b : curveRing y) : K') ≠ 0 := by
      intro h
      apply b.2
      rw [show (b : curveRing y) = 0 from Subtype.ext h]
      exact m.zero_mem
    have h2 := hbx
    rw [h0, ZeroMemClass.coe_zero, zero_mul] at h2
    exact mul_ne_zero hb0 hx0 h2
  have hWfrac : ∀ {f : MRing (fun _ : Unit => T)} {n : ℕ}, IsMultiHomog f (fun _ => n) →
      f ∈ mCoordIdeal r → ∃ a' b' : curveRing y, a' ∈ m ∧ b' ∉ m ∧
        ((b' : curveRing y) : K') * aeval y f = (a' : K') * y ⟨(), t⟩ ^ n := by
    intro f n hf hfW
    obtain ⟨⟨a', b'⟩, hab'⟩ := IsLocalization.mk'_surjective m.primeCompl (aeval ρ f)
    dsimp only at hab'
    refine ⟨a', b', ?_, b'.2, ?_⟩
    · have h1 := (hWform hf).mp hfW
      rw [← hab'] at h1
      exact (IsLocalization.AtPrime.mk'_mem_maximal_iff L m a' b').mp h1
    · have h1 := hιev hf
      rw [← hab'] at h1
      rw [(hιmk a' b' _).mp h1]
      field_simp

  have hmin : ∀ Q : Ideal (MRing (fun _ : Unit => T)), Q.IsPrime → mCoordIdeal y ⊔ Ideal.span {s} ≤ Q →
      Q ≤ mCoordIdeal r → mCoordIdeal r ≤ Q := by
    intro Q hQ hJQ hQW
    have hPQ : mCoordIdeal y ≤ Q := le_trans le_sup_left hJQ
    have hsQ : s ∈ Q := hJQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    exact le_of_minimal_prime_over_coord y t hyt hfin m hm (mCoordIdeal r) Q hQ hPQ hQW hXt hWB hWfrac
      (CoordinateConeArithVar.isMultiHomogIdeal r) ha0 hs hsQ hbx
  have hmp : mCoordIdeal r ∈ (mCoordIdeal y ⊔ Ideal.span {s}).minimalPrimes :=
    ⟨⟨hWprime, hJW⟩, fun Q hQ hQW => hmin Q hQ.1 hQ.2 hQW⟩
  have hD : mCoordIdeal r ∈ divSupp (mCoordIdeal y) s := by
    rw [divSupp, Set.mem_ofPred_eq]
    exact ⟨hmp, fun _ => ⟨t, hXt⟩⟩
  exact ⟨mCoordIdeal r, hD, hcurve⟩

end

end GroundTheory.Heights₂.Heights
