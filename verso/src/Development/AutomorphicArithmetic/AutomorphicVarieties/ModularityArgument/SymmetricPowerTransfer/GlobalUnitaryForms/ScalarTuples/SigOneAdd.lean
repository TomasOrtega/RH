import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.HsHasse
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LocNorm
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.TendstoUnderCofinite

open QuadraticAlgebra NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.V.Z.Sym.Glob.GlobalDataExistence

/- English proof (translation)
Take `⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩` from `d`. Establish `h1 : p0 ^ 2 - Δ * q0 ^ 2 - (p1 ^ 2 - Δ * q1 ^ 2) = 0`. Use `congrArg (fun z : EL Δ τ => z.re.re) hd` as an intermediate fact. Simplify using `[sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at this`. Take the linear combination `this`.

Establish `h2 : 2 * (p0 * p1 - Δ * q0 * q1) + τ * (p1 ^ 2 - Δ * q1 ^ 2) = 1`. Use `congrArg (fun z : EL Δ τ => z.im.re) hd` as an intermediate fact. Simplify using `[sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at this`. Take the linear combination `this`. Establish `g1` using `congrArg f h1`.

Establish `g2` using `congrArg f h2`. Simplify using `only [map_sub, map_add, map_mul, map_pow, map_zero, map_one, map_ofNat] at g1 g2`. Conclude with `⟨f p0 + f p1 * a, f q0 + f q1 * a, by linear_combination g1 + a * g2 + (f p1 ^ 2 - f Δ * f q1 ^ 2) * ha⟩`.
-/
private theorem sq_of_norm {K R : Type} [Field K] [Field R] (f : K →+* R) {Δ τ : K} (a : R) (ha : a ^ 2 = f τ * a - 1)
    (d : EL Δ τ) (hd : d * sigL d = ofE Δ (ω : Etau K τ)) : ∃ x y : R, x ^ 2 - f Δ * y ^ 2 = a := by
  obtain ⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩ := d
  have h1 : p0 ^ 2 - Δ * q0 ^ 2 - (p1 ^ 2 - Δ * q1 ^ 2) = 0 := by
    have := congrArg (fun z : EL Δ τ => z.re.re) hd
    simp [sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at this
    linear_combination this
  have h2 : 2 * (p0 * p1 - Δ * q0 * q1) + τ * (p1 ^ 2 - Δ * q1 ^ 2) = 1 := by
    have := congrArg (fun z : EL Δ τ => z.im.re) hd
    simp [sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at this
    linear_combination this
  have g1 := congrArg f h1
  have g2 := congrArg f h2
  simp only [map_sub, map_add, map_mul, map_pow, map_zero, map_one, map_ofNat] at g1 g2
  exact ⟨f p0 + f p1 * a, f q0 + f q1 * a, by linear_combination g1 + a * g2 + (f p1 ^ 2 - f Δ * f q1 ^ 2) * ha⟩

/- English proof (translation)
Take `⟨p0, p1⟩` from `x`. Take `⟨q0, q1⟩` from `y`. Establish `h1` using `congrArg QuadraticAlgebra.re h`. Establish `h2` using `congrArg QuadraticAlgebra.im h`. Simplify using `[pow_two] at h1 h2`.

Use `⟨⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]`. Take the linear combination `h1`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `h2`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem norm_of_sq {K : Type} [Field K] {Δ τ : K} (x y : Etau K τ)
    (h : x ^ 2 - algebraMap K (Etau K τ) Δ * y ^ 2 = ω) : ∃ d : EL Δ τ, d * sigL d = ofE Δ (ω : Etau K τ) := by
  obtain ⟨p0, p1⟩ := x
  obtain ⟨q0, q1⟩ := y
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp [pow_two] at h1 h2
  refine ⟨⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩, ?_⟩
  ext <;> simp [sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · linear_combination h1
  · ring
  · linear_combination h2
  · ring

/- English proof (translation)
Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at ha`. Establish `key : hs (algebraMap F E Δ) a = 1`. Use `hsHasse E _ a ((map_ne_zero _).2 hΔ) ha0 (fun σ => ?_) fun w => ?_` and prove the remaining obligations.

It suffices to derive a contradiction. Establish `h1` using `hτ (σ.comp (algebraMap F E))`. Establish `h2` using `congrArg σ ha`. Simplify using `only [map_sub, map_mul, map_pow, map_one, map_ofNat, RingHom.comp_apply] at h1 h2`. Use polynomial arithmetic with `[sq_nonneg (2 * σ a - σ (algebraMap F E τ))]`.

Set `v : Pl F` to `w.under (𝓞 F) haveI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩`. Establish `hf : ∀ x : F, KStar.Choice.complMap v w (cv v x) = cv w (algebraMap F E x)` using `KStar.Choice.complMap_algebraMap v w`. Unfold `hs`. Rewrite using `[if_pos]`. Distinguish the cases in `hv : v ∈ D.Sg`.

Take `⟨s, hs⟩` from `h.split v hv`. Establish `e` using `congrArg (KStar.Choice.complMap v w) hs`. Rewrite `e` using `[hf, map_mul]`. Use `set r := KStar.Choice.complMap v w s`. Establish `hr : r ≠ 0`.

Introduce and unpack `h0`. Rewrite `e` using `[h0, mul_zero, map_eq_zero, map_eq_zero]`. Conclude with `hΔ e`. Use `haveI : CharZero (Kv w) := algebraRat.charZero _`. Use `⟨(cv w a + 1) / 2, (cv w a - 1) / (2 * r), ?_⟩` and prove the remaining obligations.

Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨d, hd⟩` from `locNorm (Ov v) (Kv v) (cv v Δ) (cv v τ) (h.off v hv) (hi v hv)`. Rewrite using `[← hf]`.

Use `sq_of_norm _ _ ?_ d hd` and prove the remaining obligations. Rewrite using `[hf, ← map_pow, ha, map_sub, map_mul, map_one]`. Unfold `hs at key`. Assume the negation of the conclusion as `hn`. Rewrite `key` using `[if_neg hn]`.

Evaluate the numerical expressions using `at key`.
-/
private theorem hasse {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (h : D.Ok) (τ : F) (hτ : IsCM τ)
    (hi : ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range) (hΔ : Δ ≠ 0)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (a : E) (ha : a ^ 2 = algebraMap F E τ * a - 1) :
    ∃ x y : E, x ^ 2 - algebraMap F E Δ * y ^ 2 = a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have key : hs (algebraMap F E Δ) a = 1 := by
    refine hsHasse E _ a ((map_ne_zero _).2 hΔ) ha0 (fun σ => ?_) fun w => ?_
    · exfalso
      have h1 := hτ (σ.comp (algebraMap F E))
      have h2 := congrArg σ ha
      simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, RingHom.comp_apply] at h1 h2
      nlinarith [sq_nonneg (2 * σ a - σ (algebraMap F E τ))]
    · let v : Pl F := w.under (𝓞 F)
      haveI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
      have hf : ∀ x : F, KStar.Choice.complMap v w (cv v x) = cv w (algebraMap F E x) :=
        KStar.Choice.complMap_algebraMap v w
      unfold hs
      rw [if_pos]
      by_cases hv : v ∈ D.Sg
      · obtain ⟨s, hs⟩ := h.split v hv
        have e := congrArg (KStar.Choice.complMap v w) hs
        rw [hf, map_mul] at e
        set r := KStar.Choice.complMap v w s
        have hr : r ≠ 0 := by
          rintro h0
          rw [h0, mul_zero, map_eq_zero, map_eq_zero] at e
          exact hΔ e
        haveI : CharZero (Kv w) := algebraRat.charZero _
        refine ⟨(cv w a + 1) / 2, (cv w a - 1) / (2 * r), ?_⟩
        rw [e]
        field_simp
        ring
      · obtain ⟨d, hd⟩ := locNorm (Ov v) (Kv v) (cv v Δ) (cv v τ) (h.off v hv) (hi v hv)
        rw [← hf]
        refine sq_of_norm _ _ ?_ d hd
        rw [hf, ← map_pow, ha, map_sub, map_mul, map_one]
  unfold hs at key
  by_contra hn
  rw [if_neg hn] at key
  norm_num at key

/- English proof (translation)
Establish `hΔ : Δ ≠ 0` using `fun h0 => by simpa [h0] using h.neg σ`. Use `haveI : Fact (∀ r : F, r ^ 2 ≠ -1 + τ * r) := ⟨fun r hr => by`. Establish `h1` using `hτ σ`. Establish `h2` using `congrArg σ hr`. Simplify using `only [map_sub, map_add, map_neg, map_mul, map_pow, map_one, map_ofNat] at h1 h2`.

Use polynomial arithmetic with `[sq_nonneg (2 * σ r - σ τ)]⟩`. Use `haveI : NumberField (Etau F τ) := NumberField.of_module_finite F _`. Apply the tactic sequence `obtain ⟨x, y, hxy⟩ := hasse D h τ hτ hi hΔ (Etau F τ) ω (by ext <;> simp [pow_two, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])`. Conclude with `norm_of_sq x y hxy`.
-/
private theorem d_ex {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (h : D.Ok) (τ : F) (hτ : IsCM τ)
    (hi : ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range) (σ : F →+* ℝ) :
    ∃ d : EL Δ τ, d * sigL d = ofE Δ (ω : Etau F τ) := by
  have hΔ : Δ ≠ 0 := fun h0 => by simpa [h0] using h.neg σ
  haveI : Fact (∀ r : F, r ^ 2 ≠ -1 + τ * r) := ⟨fun r hr => by
    have h1 := hτ σ
    have h2 := congrArg σ hr
    simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_one, map_ofNat] at h1 h2
    nlinarith [sq_nonneg (2 * σ r - σ τ)]⟩
  haveI : NumberField (Etau F τ) := NumberField.of_module_finite F _
  obtain ⟨x, y, hxy⟩ := hasse D h τ hτ hi hΔ (Etau F τ) ω (by ext <;> simp [pow_two, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])
  exact norm_of_sq x y hxy

/- English proof (translation)
Take `⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩` from `y`. Simplify using `[sigL, QuadraticAlgebra.trace_def, two_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem tr_re {K : Type} [Field K] {Δ τ : K} (y : EL Δ τ) :
    (QuadraticAlgebra.trace (y * star (sigL y))).re =
      2 * (y.re.re ^ 2 + τ * y.re.re * y.im.re + y.im.re ^ 2) - 2 * Δ * (y.re.im ^ 2 + τ * y.re.im * y.im.im + y.im.im ^ 2) := by
  obtain ⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩ := y
  simp [sigL, QuadraticAlgebra.trace_def, two_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  ring

/- English proof (translation)
Use polynomial arithmetic with `[sq_nonneg (2 * p + t * q), mul_nonneg (sub_nonneg.2 (show t ^ 2 ≤ 4 by linarith)) (sq_nonneg q)]`.
-/
private theorem q_nonneg {t : ℝ} (ht : t ^ 2 - 4 < 0) (p q : ℝ) : 0 ≤ p ^ 2 + t * p * q + q ^ 2 := by
  nlinarith [sq_nonneg (2 * p + t * q), mul_nonneg (sub_nonneg.2 (show t ^ 2 ≤ 4 by linarith)) (sq_nonneg q)]

/- English proof (translation)
Establish `hq : q = 0`. Assume the negation of the conclusion as `hq`. Use polynomial arithmetic with `[sq_nonneg (2 * p + t * q), mul_pos (sub_pos.2 (show t ^ 2 < 4 by linarith)) (sq_pos_of_ne_zero hq)]`. Substitute `hq` using the available equality. Conclude with `⟨by simpa using h, rfl⟩`.
-/
private theorem q_zero {t : ℝ} (ht : t ^ 2 - 4 < 0) {p q : ℝ} (h : p ^ 2 + t * p * q + q ^ 2 = 0) : p = 0 ∧ q = 0 := by
  have hq : q = 0 := by
    by_contra hq
    nlinarith [sq_nonneg (2 * p + t * q), mul_pos (sub_pos.2 (show t ^ 2 < 4 by linarith)) (sq_pos_of_ne_zero hq)]
  subst hq
  exact ⟨by simpa using h, rfl⟩

/- English proof (translation)
Rewrite using `[tr_re]`. Simplify using `only [map_sub, map_add, map_mul, map_pow, map_ofNat] at hτ ⊢`. Establish `h1` using `q_nonneg hτ (σ y.re.re) (σ y.im.re)`. Establish `h2` using `q_nonneg hτ (σ y.re.im) (σ y.im.im)`. Establish `h3` using `mul_nonneg (neg_pos.2 hΔ).le h2`.

Use `⟨by linarith, fun hy => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Establish `e1` using `q_zero hτ (le_antisymm (by linarith) h1)`. Establish `e2` using `q_zero hτ ((mul_eq_zero.1 (le_antisymm (by linarith) h3)).resolve_left (neg_pos.2 hΔ).ne')`. Simplify using `only [map_eq_zero] at e1 e2`.

Apply the tactic sequence `exact hy (by ext <;> simp [e1.1, e1.2, e2.1, e2.2])`.
-/
private theorem tr_pos {K : Type} [Field K] {Δ τ : K} (σ : K →+* ℝ) (hΔ : σ Δ < 0) (hτ : σ (τ ^ 2 - 4) < 0) (y : EL Δ τ) :
    0 ≤ σ (QuadraticAlgebra.trace (y * star (sigL y))).re ∧ (y ≠ 0 → 0 < σ (QuadraticAlgebra.trace (y * star (sigL y))).re) := by
  rw [tr_re]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at hτ ⊢
  have h1 := q_nonneg hτ (σ y.re.re) (σ y.im.re)
  have h2 := q_nonneg hτ (σ y.re.im) (σ y.im.im)
  have h3 := mul_nonneg (neg_pos.2 hΔ).le h2
  refine ⟨by linarith, fun hy => ?_⟩
  by_contra hn
  have e1 := q_zero hτ (le_antisymm (by linarith) h1)
  have e2 := q_zero hτ ((mul_eq_zero.1 (le_antisymm (by linarith) h3)).resolve_left (neg_pos.2 hΔ).ne')
  simp only [map_eq_zero] at e1 e2
  exact hy (by ext <;> simp [e1.1, e1.2, e2.1, e2.2])

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [sigL] <;> ring`.
-/
private theorem sig_mul {K : Type} [Field K] {Δ τ : K} (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL] <;> ring

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [sigL]`.
-/
private theorem sig_sig {K : Type} [Field K] {Δ τ : K} (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [sigL]`.
-/
private theorem sig_star {K : Type} [Field K] {Δ τ : K} (x : EL Δ τ) : sigL (star x) = star (sigL x) := by
  ext <;> simp [sigL]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]`.
-/
private theorem sig_one_add {K : Type} [Field K] {Δ τ : K} (x : EL Δ τ) : sigL (1 + x) = 1 + sigL x := by
  ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/- English proof (translation)
Introduce and unpack `⟨⟨p, q⟩, x⟩ hx σ`. Establish `e : (1 + sigL d * star d) * x * star (sigL x) = x * star (sigL x) + (sigL d * x) * star (sigL (sigL d * x))`. Rewrite using `[sig_mul, sig_sig, star_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (herm 1 (1 + sigL d * star d) (⟨p, q⟩, x) (⟨p, q⟩, x)).re = p ^ 2 - Δ * q ^ 2 + ((QuadraticAlgebra.trace (x * star (sigL x))).re + (QuadraticAlgebra.trace ((sigL d * x) * star (sigL (sigL d * x)))).re)`.

Simplify using `only [herm]`. Rewrite using `[e, map_add, map_one, one_mul]`. Simplify using `only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`.

Establish `h1` using `tr_pos σ (hΔ σ) (hτ σ) x`. Establish `h2` using `(tr_pos σ (hΔ σ) (hτ σ) (sigL d * x)).1`. Simplify using `only [map_add σ, map_sub σ, map_mul σ, map_pow σ]`. Establish `h3` using `mul_nonneg (neg_pos.2 (hΔ σ)).le (sq_nonneg (σ q))`. Establish `h4` using `sq_nonneg (σ p)`.

Distinguish the cases in `h0 : x = 0`. Assume the negation of the conclusion as `hn`. Establish `hp : σ p ^ 2 = 0` using `le_antisymm (by linarith [h1.1]) h4`. Establish `hq : σ q ^ 2 = 0` using `(mul_eq_zero.1 (le_antisymm (by linarith [h1.1]) h3)).resolve_left (neg_pos.2 (hΔ σ)).ne'`. Simplify using `only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, map_eq_zero] at hp hq`.

Conclude with `hx (by rw [hp, hq, h0]; rfl)`. Combine the linear relations using `[h1.2 h0]`.
-/
private theorem posF {F : Type} [Field F] {Δ τ : F} (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (hτ : IsCM τ) (d : EL Δ τ) :
    PosF 1 (1 + sigL d * star d) := by
  rintro ⟨⟨p, q⟩, x⟩ hx σ
  have e : (1 + sigL d * star d) * x * star (sigL x) = x * star (sigL x) + (sigL d * x) * star (sigL (sigL d * x)) := by
    rw [sig_mul, sig_sig, star_mul]
    ring
  have e2 : (herm 1 (1 + sigL d * star d) (⟨p, q⟩, x) (⟨p, q⟩, x)).re = p ^ 2 - Δ * q ^ 2 +
      ((QuadraticAlgebra.trace (x * star (sigL x))).re + (QuadraticAlgebra.trace ((sigL d * x) * star (sigL (sigL d * x)))).re) := by
    simp only [herm]
    rw [e, map_add, map_one, one_mul]
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    ring
  rw [e2]
  have h1 := tr_pos σ (hΔ σ) (hτ σ) x
  have h2 := (tr_pos σ (hΔ σ) (hτ σ) (sigL d * x)).1
  simp only [map_add σ, map_sub σ, map_mul σ, map_pow σ]
  have h3 := mul_nonneg (neg_pos.2 (hΔ σ)).le (sq_nonneg (σ q))
  have h4 := sq_nonneg (σ p)
  by_cases h0 : x = 0
  · by_contra hn
    have hp : σ p ^ 2 = 0 := le_antisymm (by linarith [h1.1]) h4
    have hq : σ q ^ 2 = 0 := (mul_eq_zero.1 (le_antisymm (by linarith [h1.1]) h3)).resolve_left (neg_pos.2 (hΔ σ)).ne'
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, map_eq_zero] at hp hq
    exact hx (by rw [hp, hq, h0]; rfl)
  · linarith [h1.2 h0]

end UpperTheory.V.Z.Sym.Glob.GlobalDataExistence

open UpperTheory.V.Z.Sym.Glob.GlobalDataExistence in
/- English proof (translation)
Introduce `F _ _ Δ D h τ hτ hi`. Use `haveI := h.real`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Set `σ : F →+* ℝ` to `InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)`. Take `⟨d, hd⟩` from `d_ex D h τ hτ hi σ`.

Establish `hp` using `posF h.neg hτ d`. Use `⟨d, _, ⟨fun h0 => by simpa [h0] using hτ σ, one_ne_zero, hd, ?_, ?_, ?_⟩, hp⟩` and prove the remaining obligations. Use `haveI : Module.Finite F (EL Δ τ) := Module.Finite.trans (Lsq F Δ) _ haveI : IsArtinianRing (EL Δ τ) := IsArtinianRing.of_finite F _`. Use `IsArtinianRing.isUnit_iff_mem_nonZeroDivisors.2 (mem_nonZeroDivisors_iff_left.2 fun x hx => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h0`.

Use `hp (0, x) (fun e => h0 (congrArg Prod.snd e)) σ` as an intermediate fact. Simplify using `[herm, hx] at this`. Rewrite using `[sig_one_add, sig_mul, sig_sig, sig_star, star_add, star_one, star_mul, star_star]`. Establish `e : (d * sigL d) * star (d * sigL d) = 1`. Rewrite using `[hd]`.

Apply the tactic sequence `ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]`. Rewrite `e` using `[star_mul]`. Rewrite using `[sig_one_add, sig_mul, sig_sig, sig_star]`. Take the linear combination `-e`.
-/
theorem UpperTheory.V.Z.Sym.Glob.datEx :
    UpperTheory.V.Z.Sym.Glob.DatEx := by
  intro F _ _ Δ D h τ hτ hi
  haveI := h.real
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  let σ : F →+* ℝ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
  obtain ⟨d, hd⟩ := d_ex D h τ hτ hi σ
  have hp := posF h.neg hτ d
  refine ⟨d, _, ⟨fun h0 => by simpa [h0] using hτ σ, one_ne_zero, hd, ?_, ?_, ?_⟩, hp⟩
  · haveI : Module.Finite F (EL Δ τ) := Module.Finite.trans (Lsq F Δ) _
    haveI : IsArtinianRing (EL Δ τ) := IsArtinianRing.of_finite F _
    refine IsArtinianRing.isUnit_iff_mem_nonZeroDivisors.2 (mem_nonZeroDivisors_iff_left.2 fun x hx => ?_)
    by_contra h0
    have := hp (0, x) (fun e => h0 (congrArg Prod.snd e)) σ
    simp [herm, hx] at this
  · rw [sig_one_add, sig_mul, sig_sig, sig_star, star_add, star_one, star_mul, star_star]
  · have e : (d * sigL d) * star (d * sigL d) = 1 := by
      rw [hd]
      ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    rw [star_mul] at e
    rw [sig_one_add, sig_mul, sig_sig, sig_star]
    linear_combination -e
