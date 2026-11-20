import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointLengthSteps
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo HilbertSamuel.SectionBounded

noncomputable section

namespace CurveVerticalPointSurjective

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp only [aeval_C]`. Rewrite using `[eq_intCast, eq_intCast, map_intCast]`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p n hp => simp [hp]`.
-/
theorem ringHom_aeval {A A' : Type*} [CommRing A] [CommRing A'] [Algebra ℤ A] (f : A →+* A')
    (z : (Σ k, ι k) → A) (g : MRing ι) : f (aeval z g) = aeval (fun p => f (z p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; rw [eq_intCast, eq_intCast, map_intCast]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

/- English proof (translation)
Rewrite using `[mCoordIdeal, RingHom.mem_ker, mConeMap_homog y hg, mul_eq_zero, C_eq_zero]`. Conclude with `or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))`.
-/
theorem mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) : g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap_homog y hg, mul_eq_zero, C_eq_zero]
  exact or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))

/- English proof (translation)
Rewrite using `[mem_mCoordIdeal_iff y (homog_sub hf hg), map_sub, h, sub_self]`.
-/
theorem sub_mem_mCoordIdeal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {f g : MRing ι} {d : K → ℕ}
    (hf : IsMultiHomog f d) (hg : IsMultiHomog g d) (h : aeval y f = aeval y g) :
    f - g ∈ mCoordIdeal y := by
  rw [mem_mCoordIdeal_iff y (homog_sub hf hg), map_sub, h, sub_self]

omit [Fintype K] in

/- English proof (translation)
The claim follows from `h ▸ hf`.
-/
theorem homogD {f : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (h : a = b) : IsMultiHomog f b :=
  h ▸ hf

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]`.
-/
theorem prod_pow_add {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e₁ e₂ : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (e₁ + e₂) k = (∏ k, y ⟨k, c k⟩ ^ e₁ k) * ∏ k, y ⟨k, c k⟩ ^ e₂ k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[chartMon]`. Take `⟨k, -, hk⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := hQ)).mp h`. Conclude with `hc k (hQ.mem_of_pow_mem _ hk)`.
-/
theorem chartMon_notMem {Q : Ideal (MRing ι)} (hQ : Q.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ Q) (n : K → ℕ) : chartMon c n ∉ Q := by
  intro h
  rw [chartMon] at h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hQ)).mp h
  exact hc k (hQ.mem_of_pow_mem _ hk)

/- English proof (translation)
The claim follows from `exists_form_of_mem_chartRingZ y c hc (mem_curveRing.mp b.2 c hc)`.
-/
theorem exists_form {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (b : curveRing y) :
    ∃ (e : K → ℕ) (g : MRing ι), IsMultiHomog g e ∧ aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k :=
  exists_form_of_mem_chartRingZ y c hc (mem_curveRing.mp b.2 c hc)

def formSet {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (Q : Ideal (MRing ι)) :
    Set (curveRing y) :=
  {b | ∃ (e : K → ℕ) (g : MRing ι), IsMultiHomog g e ∧
    aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k ∧ g ∈ Q}

def formIdeal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (Q : Ideal (MRing ι)) : Ideal (curveRing y) where
  carrier := formSet y c Q
  add_mem' := by
    classical
    rintro b₁ b₂ ⟨e₁, g₁, hg₁, hv₁, hQ₁⟩ ⟨e₂, g₂, hg₂, hv₂, hQ₂⟩
    refine ⟨e₁ + e₂, g₁ * chartMon c e₂ + g₂ * chartMon c e₁,
      homog_add (homog_mul hg₁ (homog_chartMon c e₂))
        (homogD (homog_mul hg₂ (homog_chartMon c e₁)) (add_comm _ _)), ?_,
      Q.add_mem (Q.mul_mem_right _ hQ₁) (Q.mul_mem_right _ hQ₂)⟩
    rw [map_add, map_mul, map_mul, aeval_chartMon, aeval_chartMon, hv₁, hv₂, prod_pow_add,
      Subring.coe_add]
    ring
  zero_mem' := ⟨0, 0, homog_zero _, by simp, Q.zero_mem⟩
  smul_mem' := by
    rintro b b₂ ⟨e₂, g₂, hg₂, hv₂, hQ₂⟩
    obtain ⟨e, h, hh, hv⟩ := exists_form y c hc b
    refine ⟨e + e₂, h * g₂, homog_mul hh hg₂, ?_, Q.mul_mem_left _ hQ₂⟩
    rw [map_mul, hv, hv₂, prod_pow_add, smul_eq_mul, Subring.coe_mul]
    ring

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_formIdeal {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {hc : ∀ k, y ⟨k, c k⟩ ≠ 0}
    {Q : Ideal (MRing ι)} {b : curveRing y} :
    b ∈ formIdeal y c hc Q ↔ ∃ (e : K → ℕ) (g : MRing ι), IsMultiHomog g e ∧
      aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k ∧ g ∈ Q :=
  Iff.rfl

/- English proof (translation)
Establish `hmonQ : ∀ n, chartMon c n ∉ Q` using `chartMon_notMem hQ fun k h => hXc k (hQW h)`. Establish `htr : ∀ {f g : MRing ι} {n : K → ℕ}, IsMultiHomog f n → IsMultiHomog g n → aeval y f = aeval y g → g ∈ Q → f ∈ Q`. Introduce `f g n hf hg he hgQ`. Establish `h1` using `Q.add_mem (hPQ (sub_mem_mCoordIdeal y hf hg he)) hgQ`. Rewrite `h1` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Establish `hIQm : formIdeal y c hc Q ≤ m`. Introduce `x hx`. Take `⟨e, g, hg, hv, hgQ⟩` from `mem_formIdeal.mp hx`. Conclude with `(hWB x hg hv).mp (hQW hgQ)`. Establish `haIQ : a ∈ formIdeal y c hc Q`.

Take `⟨e, h, hh, hv⟩` from `exists_form y c hc b`. Use `mem_formIdeal.mpr ⟨e + d, h * s, homog_mul hh hs, ?_, Q.mul_mem_left _ hsQ⟩` and prove the remaining obligations. Rewrite using `[map_mul, hv, prod_pow_add]`. Take the linear combination `(∏ k, y ⟨k, c k⟩ ^ e k) * hbx`. Establish `hIQprime : (formIdeal y c hc Q).IsPrime`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.eq_top_iff_one]`. Introduce `h1`. Take `⟨e, g, hg, hv, hgQ⟩` from `mem_formIdeal.mp h1`. Use `hmonQ e (htr (homog_chartMon c e) hg ?_ hgQ)` and prove the remaining obligations.

Rewrite using `[aeval_chartMon, hv]`. Simplify using the standard rewrite rules. Introduce `x₁ x₂ h12`. Take `⟨e, g, hg, hv, hgQ⟩` from `mem_formIdeal.mp h12`. Take `⟨e₁, h₁, hh₁, hv₁⟩` from `exists_form y c hc x₁`.

Take `⟨e₂, h₂, hh₂, hv₂⟩` from `exists_form y c hc x₂`. Establish `hf : h₁ * h₂ * chartMon c e ∈ Q`. Use `htr (homog_mul (homog_mul hh₁ hh₂) (homog_chartMon c e)) (homogD (homog_mul hg (homog_chartMon c (e₁ + e₂))) (add_comm _ _)) ?_ (Q.mul_mem_right (chartMon c (e₁ + e₂)) hgQ)` and prove the remaining obligations. Simplify using `only [map_mul, aeval_chartMon, hv₁, hv₂, hv, prod_pow_add, Subring.coe_mul]`. Expand and normalize the polynomial expressions, which then agree.

Break down `hQ.mem_or_mem hf with h12 | h3` into its components or cases. Break down `hQ.mem_or_mem h12 with h1Q | h2Q` into its components or cases. Conclude with `Or.inl (mem_formIdeal.mpr ⟨e₁, h₁, hh₁, hv₁, h1Q⟩)`. Conclude with `Or.inr (mem_formIdeal.mpr ⟨e₂, h₂, hh₂, hv₂, h2Q⟩)`. Conclude with `absurd h3 (hmonQ e)`.

Establish `hIQmax : (formIdeal y c hc Q).IsMaximal`. Establish `: Algebra.IsIntegral ℤ (curveRing y)` using `Algebra.IsIntegral.of_finite ℤ _`. Establish `hcomap : (formIdeal y c hc Q).comap (algebraMap ℤ (curveRing y)) ≠ ⊥` using `Ideal.comap_ne_bot_of_integral_mem ha0 haIQ (Algebra.IsIntegral.isIntegral a)`. Establish `: ((formIdeal y c hc Q).comap (algebraMap ℤ (curveRing y))).IsPrime` using `Ideal.IsPrime.comap _`. Conclude with `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (IsPrime.to_maximal_ideal hcomap)`.

Establish `hIQeq : formIdeal y c hc Q = m` using `hIQmax.eq_of_le hm.ne_top hIQm`. Take `⟨S, hS, hWS⟩` from `hWforms`. Introduce `f hfW`. Rewrite `hfW` using `[hWS]`. Use `(Ideal.span_le.mpr ?_) hfW` and prove the remaining obligations.

Introduce `f hf`. Take `⟨δ, hδ⟩` from `hS f hf`. Establish `hfW' : f ∈ W` using `by rw [hWS]; exact Ideal.subset_span hf`. Take `⟨a', b', ha'm, hb'm, hv'⟩` from `hWfrac hδ hfW'`. Establish `ha'IQ : a' ∈ formIdeal y c hc Q` using `by rw [hIQeq]; exact ha'm`.

Take `⟨ea, ga, hga, hva, hgaQ⟩` from `mem_formIdeal.mp ha'IQ`. Take `⟨eb, hb, hhb, hvb⟩` from `exists_form y c hc b'`. Establish `hbQ : hb ∉ Q`. Introduce `h`. Establish `hbIQ : b' ∈ formIdeal y c hc Q` using `mem_formIdeal.mpr ⟨eb, hb, hhb, hvb, h⟩`.

Rewrite `hbIQ` using `[hIQeq]`. Conclude with `hb'm hbIQ`. Establish `h1 : hb * f * chartMon c ea ∈ Q`. Use `htr (homog_mul (homog_mul hhb hδ) (homog_chartMon c ea)) (homogD (homog_mul hga (homog_chartMon c (eb + δ))) (add_comm _ _)) ?_ (Q.mul_mem_right (chartMon c (eb + δ)) hgaQ)` and prove the remaining obligations. Simplify using `only [map_mul, aeval_chartMon, hvb, hva, prod_pow_add]`.

Take the linear combination `(∏ k, y ⟨k, c k⟩ ^ eb k) * (∏ k, y ⟨k, c k⟩ ^ ea k) * hv'`. Break down `hQ.mem_or_mem h1 with h2 | h3` into its components or cases. Break down `hQ.mem_or_mem h2 with h4 | h5` into its components or cases. Conclude with `absurd h4 hbQ`. Conclude with `h5`.

Conclude with `absurd h3 (hmonQ ea)`.
-/
theorem le_of_minimal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hfin : Module.Finite ℤ (curveRing y)) (m : Ideal (curveRing y)) (hm : m.IsMaximal)
    (W Q : Ideal (MRing ι)) (hQ : Q.IsPrime) (hPQ : mCoordIdeal y ≤ Q) (hQW : Q ≤ W)
    (hXc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hWB : ∀ {g : MRing ι} {e : K → ℕ} (b : curveRing y), IsMultiHomog g e →
      aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k → (g ∈ W ↔ b ∈ m))
    (hWfrac : ∀ {f : MRing ι} {n : K → ℕ}, IsMultiHomog f n → f ∈ W →
      ∃ a' b' : curveRing y, a' ∈ m ∧ b' ∉ m ∧ (b' : Ω) * aeval y f = (a' : Ω) * ∏ k, y ⟨k, c k⟩ ^ n k)
    (hWforms : IsMultiHomogIdeal W) {a b : curveRing y} (ha0 : a ≠ 0) {s : MRing ι} {d : K → ℕ}
    (hs : IsMultiHomog s d) (hsQ : s ∈ Q) (hbx : (b : Ω) * aeval y s = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ d k) :
    W ≤ Q := by
  classical
  have hmonQ : ∀ n, chartMon c n ∉ Q := chartMon_notMem hQ fun k h => hXc k (hQW h)
  have htr : ∀ {f g : MRing ι} {n : K → ℕ}, IsMultiHomog f n → IsMultiHomog g n →
      aeval y f = aeval y g → g ∈ Q → f ∈ Q := by
    intro f g n hf hg he hgQ
    have h1 := Q.add_mem (hPQ (sub_mem_mCoordIdeal y hf hg he)) hgQ
    rwa [sub_add_cancel] at h1
  have hIQm : formIdeal y c hc Q ≤ m := by
    intro x hx
    obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp hx
    exact (hWB x hg hv).mp (hQW hgQ)
  have haIQ : a ∈ formIdeal y c hc Q := by
    obtain ⟨e, h, hh, hv⟩ := exists_form y c hc b
    refine mem_formIdeal.mpr ⟨e + d, h * s, homog_mul hh hs, ?_, Q.mul_mem_left _ hsQ⟩
    rw [map_mul, hv, prod_pow_add]
    linear_combination (∏ k, y ⟨k, c k⟩ ^ e k) * hbx
  have hIQprime : (formIdeal y c hc Q).IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one]
      intro h1
      obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp h1
      refine hmonQ e (htr (homog_chartMon c e) hg ?_ hgQ)
      rw [aeval_chartMon, hv]
      simp
    · intro x₁ x₂ h12
      obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp h12
      obtain ⟨e₁, h₁, hh₁, hv₁⟩ := exists_form y c hc x₁
      obtain ⟨e₂, h₂, hh₂, hv₂⟩ := exists_form y c hc x₂
      have hf : h₁ * h₂ * chartMon c e ∈ Q := by
        refine htr (homog_mul (homog_mul hh₁ hh₂) (homog_chartMon c e))
          (homogD (homog_mul hg (homog_chartMon c (e₁ + e₂))) (add_comm _ _)) ?_ (Q.mul_mem_right (chartMon c (e₁ + e₂)) hgQ)
        simp only [map_mul, aeval_chartMon, hv₁, hv₂, hv, prod_pow_add, Subring.coe_mul]
        ring
      rcases hQ.mem_or_mem hf with h12 | h3
      · rcases hQ.mem_or_mem h12 with h1Q | h2Q
        · exact Or.inl (mem_formIdeal.mpr ⟨e₁, h₁, hh₁, hv₁, h1Q⟩)
        · exact Or.inr (mem_formIdeal.mpr ⟨e₂, h₂, hh₂, hv₂, h2Q⟩)
      · exact absurd h3 (hmonQ e)
  have hIQmax : (formIdeal y c hc Q).IsMaximal := by
    have : Algebra.IsIntegral ℤ (curveRing y) := Algebra.IsIntegral.of_finite ℤ _
    have hcomap : (formIdeal y c hc Q).comap (algebraMap ℤ (curveRing y)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha0 haIQ (Algebra.IsIntegral.isIntegral a)
    have : ((formIdeal y c hc Q).comap (algebraMap ℤ (curveRing y))).IsPrime := Ideal.IsPrime.comap _
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (IsPrime.to_maximal_ideal hcomap)
  have hIQeq : formIdeal y c hc Q = m := hIQmax.eq_of_le hm.ne_top hIQm

  obtain ⟨S, hS, hWS⟩ := hWforms
  intro f hfW
  rw [hWS] at hfW
  refine (Ideal.span_le.mpr ?_) hfW
  intro f hf
  obtain ⟨δ, hδ⟩ := hS f hf
  have hfW' : f ∈ W := by rw [hWS]; exact Ideal.subset_span hf
  obtain ⟨a', b', ha'm, hb'm, hv'⟩ := hWfrac hδ hfW'
  have ha'IQ : a' ∈ formIdeal y c hc Q := by rw [hIQeq]; exact ha'm
  obtain ⟨ea, ga, hga, hva, hgaQ⟩ := mem_formIdeal.mp ha'IQ
  obtain ⟨eb, hb, hhb, hvb⟩ := exists_form y c hc b'
  have hbQ : hb ∉ Q := by
    intro h
    have hbIQ : b' ∈ formIdeal y c hc Q := mem_formIdeal.mpr ⟨eb, hb, hhb, hvb, h⟩
    rw [hIQeq] at hbIQ
    exact hb'm hbIQ
  have h1 : hb * f * chartMon c ea ∈ Q := by
    refine htr (homog_mul (homog_mul hhb hδ) (homog_chartMon c ea))
      (homogD (homog_mul hga (homog_chartMon c (eb + δ))) (add_comm _ _)) ?_ (Q.mul_mem_right (chartMon c (eb + δ)) hgaQ)
    simp only [map_mul, aeval_chartMon, hvb, hva, prod_pow_add]
    linear_combination (∏ k, y ⟨k, c k⟩ ^ eb k) * (∏ k, y ⟨k, c k⟩ ^ ea k) * hv'
  rcases hQ.mem_or_mem h1 with h2 | h3
  · rcases hQ.mem_or_mem h2 with h4 | h5
    · exact absurd h4 hbQ
    · exact h5
  · exact absurd h3 (hmonQ ea)

/- English proof (translation)
Establish `key : ∀ w : LocalizedModule m.primeCompl (R ⧸ Ideal.span {a}), w = 0`. Introduce `w`. Proceed by induction on `w using LocalizedModule.induction_on with`. Consider the case `h x t`. Rewrite using `[← LocalizedModule.zero_mk t, LocalizedModule.mk_eq]`.

Use `⟨⟨a, ha⟩, ?_⟩` and prove the remaining obligations. Take `⟨x', rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)`. Establish `hsub : Subsingleton (LocalizedModule m.primeCompl (R ⧸ Ideal.span {a}))` using `⟨fun u v => by rw [key u, key v]⟩`.

Rewrite using `[locLen, dif_pos ‹m.IsPrime›, Module.length_eq_zero_iff.mpr hsub]`. Both sides reduce to the same expression.
-/
theorem locLen_quot_eq_zero {R : Type*} [CommRing R] (m : Ideal R) [m.IsPrime] {a : R} (ha : a ∉ m) :
    locLen m (R ⧸ Ideal.span {a}) = 0 := by
  have key : ∀ w : LocalizedModule m.primeCompl (R ⧸ Ideal.span {a}), w = 0 := by
    intro w
    induction w using LocalizedModule.induction_on with
    | h x t =>
      rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq]
      refine ⟨⟨a, ha⟩, ?_⟩
      obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def,
        Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
  have hsub : Subsingleton (LocalizedModule m.primeCompl (R ⧸ Ideal.span {a})) :=
    ⟨fun u v => by rw [key u, key v]⟩
  rw [locLen, dif_pos ‹m.IsPrime›, Module.length_eq_zero_iff.mpr hsub]
  rfl

end CurveVerticalPointSurjective

end

end GroundTheory.Heights₂.Heights.Targets
