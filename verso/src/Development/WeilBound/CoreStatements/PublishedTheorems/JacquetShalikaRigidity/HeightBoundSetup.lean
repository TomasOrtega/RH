import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace HeightBoundSetup

variable {G Γ : Type*} [MeasurableSpace G]

def bnd (D : G → ℝ) (a b : ℝ) : Set G := {g | a ≤ D g ∧ D g < b}

structure Setup (ν : Measure G) (D : G → ℝ) (H : G → ℂ) (T : ℝ → G → G) (r : Γ → G → G) (c C : ℝ) : Prop where
  mD : Measurable D
  mH : Measurable H
  pos : ∀ g, 0 < D g
  DT : ∀ t g, D (T t g) = Real.exp (c * t) * D g
  HT : ∀ t g, H (T t g) = H g
  Dr : ∀ γ g, D (r γ g) = D g
  Hr : ∀ γ g, H (r γ g) = H g
  bdd : ∀ g, ‖H g‖ ≤ C
  nonneg : 0 ≤ C
  cpos : 0 < c
  shift : ∀ (t : ℝ) (Φ : G → ℂ), Measurable Φ → (∀ γ g, Φ (r γ g) = Φ g) → Integrable Φ ν →
    ∫ g, Φ (T t g) ∂ν = ∫ g, Φ g ∂ν
  int : ∀ ε : ℝ, 0 < ε → Integrable (fun g => min (D g) (D g)⁻¹ ^ ε) ν
  band : ν (bnd D 1 (Real.exp c)) < ⊤

/- English proof (translation)
Rewrite using `[Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le]`.
-/
theorem cpow_pos {x : ℝ} (hx : 0 < x) (z : ℂ) : (x : ℂ) ^ z = Complex.exp (Real.log x * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le]

/- English proof (translation)
Rewrite using `[mul_neg, Real.exp_neg, inv_mul_lt_iff₀ (Real.exp_pos _)]`.
-/
theorem exp_neg_mul_lt {c a x y : ℝ} : Real.exp (c * -a) * x < y ↔ x < Real.exp (c * a) * y := by
  rw [mul_neg, Real.exp_neg, inv_mul_lt_iff₀ (Real.exp_pos _)]

/- English proof (translation)
Rewrite using `[mul_neg, Real.exp_neg, le_inv_mul_iff₀ (Real.exp_pos _)]`.
-/
theorem le_exp_neg_mul {c a x y : ℝ} : y ≤ Real.exp (c * -a) * x ↔ Real.exp (c * a) * y ≤ x := by
  rw [mul_neg, Real.exp_neg, le_inv_mul_iff₀ (Real.exp_pos _)]

variable {ν : Measure G} {D : G → ℝ} {H : G → ℂ} {T : ℝ → G → G} {r : Γ → G → G} {c C : ℝ}

namespace Setup

variable (S : Setup ν D H T r c C)
include S

/- English proof (translation)
The claim follows from `measurableSet_lt S.mD measurable_const`.
-/
theorem mset_lt (x : ℝ) : MeasurableSet {g | D g < x} := measurableSet_lt S.mD measurable_const

/- English proof (translation)
The claim follows from `(measurableSet_le measurable_const S.mD).inter (measurableSet_lt S.mD measurable_const)`.
-/
theorem mset_bnd (a b : ℝ) : MeasurableSet (bnd D a b) :=
  (measurableSet_le measurable_const S.mD).inter (measurableSet_lt S.mD measurable_const)

/- English proof (translation)
Introduce `_ ⟨h1, h2⟩` and use `⟨ha.trans h1, h2.trans_le hb⟩`.
-/
theorem bnd_sub {a b : ℝ} (ha : 1 ≤ a) (hb : b ≤ Real.exp c) : bnd D a b ⊆ bnd D 1 (Real.exp c) :=
  fun _ ⟨h1, h2⟩ => ⟨ha.trans h1, h2.trans_le hb⟩

/- English proof (translation)
The claim follows from `(measure_mono hsub).trans_lt S.band`.
-/
theorem fin_sub {s : Set G} (hsub : s ⊆ bnd D 1 (Real.exp c)) : ν s < ⊤ :=
  (measure_mono hsub).trans_lt S.band

/- English proof (translation)
The claim follows from `Measure.integrableOn_of_bounded (M := K) (S.fin_sub hsub).ne hΦ.aestronglyMeasurable ((ae_restrict_iff' hs).2 (Eventually.of_forall hK))`.
-/
theorem intOn {Φ : G → ℂ} (hΦ : Measurable Φ) {s : Set G} (hs : MeasurableSet s)
    (hsub : s ⊆ bnd D 1 (Real.exp c)) {K : ℝ} (hK : ∀ g ∈ s, ‖Φ g‖ ≤ K) : IntegrableOn Φ s ν :=
  Measure.integrableOn_of_bounded (M := K) (S.fin_sub hsub).ne hΦ.aestronglyMeasurable
    ((ae_restrict_iff' hs).2 (Eventually.of_forall hK))

/- English proof (translation)
The claim follows from `S.mH.mul ((Complex.measurable_ofReal.comp S.mD).pow_const z)`.
-/
theorem mw (z : ℂ) : Measurable fun g => H g * (D g : ℂ) ^ z :=
  S.mH.mul ((Complex.measurable_ofReal.comp S.mD).pow_const z)

/- English proof (translation)
Use `Integrable.mono' ((S.int z.re hz).const_mul C) ((S.mw z).indicator (S.mset_lt 1)).aestronglyMeasurable (Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Establish `hm : 0 ≤ min (D g) (D g)⁻¹ ^ z.re` using `Real.rpow_nonneg (le_min (S.pos g).le (inv_nonneg.2 (S.pos g).le)) _`. Distinguish the cases in `hg : g ∈ {g | D g < 1}`. Establish `hg' : D g < 1` using `hg`. Rewrite using `[Set.indicator_of_mem hg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (S.pos g)]`.

Establish `: min (D g) (D g)⁻¹ = D g` using `min_eq_left (hg'.le.trans ((one_le_inv₀ (S.pos g)).2 hg'.le))`. Rewrite using `[this]`. Conclude with `mul_le_mul_of_nonneg_right (S.bdd g) (Real.rpow_nonneg (S.pos g).le _)`. Rewrite using `[Set.indicator_of_notMem hg, norm_zero]`. Conclude with `mul_nonneg S.nonneg hm`.
-/
theorem intJ {z : ℂ} (hz : 0 < z.re) :
    Integrable ({g | D g < 1}.indicator fun g => H g * (D g : ℂ) ^ z) ν := by
  refine Integrable.mono' ((S.int z.re hz).const_mul C) ((S.mw z).indicator (S.mset_lt 1)).aestronglyMeasurable
    (Eventually.of_forall fun g => ?_)
  have hm : 0 ≤ min (D g) (D g)⁻¹ ^ z.re :=
    Real.rpow_nonneg (le_min (S.pos g).le (inv_nonneg.2 (S.pos g).le)) _
  by_cases hg : g ∈ {g | D g < 1}
  · have hg' : D g < 1 := hg
    rw [Set.indicator_of_mem hg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (S.pos g)]
    have : min (D g) (D g)⁻¹ = D g := min_eq_left (hg'.le.trans ((one_le_inv₀ (S.pos g)).2 hg'.le))
    rw [this]
    exact mul_le_mul_of_nonneg_right (S.bdd g) (Real.rpow_nonneg (S.pos g).le _)
  · rw [Set.indicator_of_notMem hg, norm_zero]; exact mul_nonneg S.nonneg hm

/- English proof (translation)
Establish `hpt : ∀ g, {g | D g < Real.exp (c * τ)}.indicator (fun g => H g * (D g : ℂ) ^ z) g = Complex.exp (((c * τ : ℝ) : ℂ) * z) * {g | D g < 1}.indicator (fun g => H g * (D g : ℂ) ^ z) (T (-τ) g)`. Introduce `g`. Establish `hiff : T (-τ) g ∈ {g | D g < 1} ↔ g ∈ {g | D g < Real.exp (c * τ)}`. Simplify using `only [Set.mem_ofPred_eq, S.DT, exp_neg_mul_lt, mul_one]`. Distinguish the cases in `hg : g ∈ {g | D g < Real.exp (c * τ)}`.

Rewrite using `[Set.indicator_of_mem hg, Set.indicator_of_mem (hiff.2 hg), S.HT, S.DT, cpow_pos (S.pos g), cpow_pos (mul_pos (Real.exp_pos _) (S.pos g)), Real.log_mul (Real.exp_pos _).ne' (S.pos g).ne', Real.log_exp, mul_left_comm, ← Complex.exp_add]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hiff.1 h)), mul_zero]`.

Rewrite using `[← integral_indicator (S.mset_lt _), ← integral_indicator (S.mset_lt _)]`. Repeatedly rewrite using `[hpt]`. Rewrite using `[integral_const_mul, S.shift (-τ) _ ((S.mw z).indicator (S.mset_lt 1)) ?_ hJ]`. Introduce `γ g`. Simplify using `only [Set.indicator, Set.mem_ofPred_eq, S.Dr, S.Hr]`.
-/
theorem shift_J (z : ℂ) (hJ : Integrable ({g | D g < 1}.indicator fun g => H g * (D g : ℂ) ^ z) ν) (τ : ℝ) :
    ∫ g in {g | D g < Real.exp (c * τ)}, H g * (D g : ℂ) ^ z ∂ν =
      Complex.exp (((c * τ : ℝ) : ℂ) * z) * ∫ g in {g | D g < 1}, H g * (D g : ℂ) ^ z ∂ν := by
  have hpt : ∀ g, {g | D g < Real.exp (c * τ)}.indicator (fun g => H g * (D g : ℂ) ^ z) g =
      Complex.exp (((c * τ : ℝ) : ℂ) * z) *
        {g | D g < 1}.indicator (fun g => H g * (D g : ℂ) ^ z) (T (-τ) g) := by
    intro g
    have hiff : T (-τ) g ∈ {g | D g < 1} ↔ g ∈ {g | D g < Real.exp (c * τ)} := by
      simp only [Set.mem_ofPred_eq, S.DT, exp_neg_mul_lt, mul_one]
    by_cases hg : g ∈ {g | D g < Real.exp (c * τ)}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hiff.2 hg), S.HT, S.DT, cpow_pos (S.pos g),
        cpow_pos (mul_pos (Real.exp_pos _) (S.pos g)), Real.log_mul (Real.exp_pos _).ne' (S.pos g).ne',
        Real.log_exp, mul_left_comm, ← Complex.exp_add]
      congr 2; push_cast; ring
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hiff.1 h)), mul_zero]
  rw [← integral_indicator (S.mset_lt _), ← integral_indicator (S.mset_lt _)]
  simp_rw [hpt]
  rw [integral_const_mul, S.shift (-τ) _ ((S.mw z).indicator (S.mset_lt 1)) ?_ hJ]
  intro γ g; simp only [Set.indicator, Set.mem_ofPred_eq, S.Dr, S.Hr]

/- English proof (translation)
Establish `hc` using `S.cpos`. Establish `hle : Real.exp (c * τ) ≤ Real.exp c` using `Real.exp_le_exp.2 (by nlinarith)`. Establish `hset : {g | D g < Real.exp (c * τ)} = {g | D g < 1} ∪ bnd D 1 (Real.exp (c * τ))`. Use extensionality with `g`. Simplify using `only [bnd, Set.mem_union, Set.mem_ofPred_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Distinguish the cases in `h' : D g < 1`. Conclude with `Or.inl h'`. Conclude with `Or.inr ⟨not_lt.1 h', h⟩`.

Introduce and unpack `(h | ⟨_, h⟩)`. Conclude with `h.trans_le (Real.one_le_exp (by positivity))`. Conclude with `h`. Establish `hdisj : Disjoint {g | D g < 1} (bnd D 1 (Real.exp (c * τ)))`. Rewrite using `[Set.disjoint_left]`.

Introduce and unpack `g h ⟨h3, _⟩`. Conclude with `absurd h3 (not_le.2 h)`. Establish `hB : IntegrableOn (fun g => H g * (D g : ℂ) ^ z) (bnd D 1 (Real.exp (c * τ))) ν`. Use `S.intOn (S.mw z) (S.mset_bnd _ _) (S.bnd_sub le_rfl hle) (K := C * Real.exp c ^ z.re) ?_` and prove the remaining obligations. Introduce and unpack `g ⟨_, h2⟩`.

Rewrite using `[norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (S.pos g)]`. Conclude with `mul_le_mul (S.bdd g) (Real.rpow_le_rpow (S.pos g).le (h2.le.trans hle) hz.le) (Real.rpow_nonneg (S.pos g).le _) S.nonneg`. Establish `hA : IntegrableOn (fun g => H g * (D g : ℂ) ^ z) {g | D g < 1} ν` using `(integrable_indicator_iff (S.mset_lt 1)).1 (S.intJ hz)`. Use `S.shift_J z (S.intJ hz) τ` as an intermediate fact. Rewrite `this` using `[hset, setIntegral_union hdisj (S.mset_bnd _ _) hA hB]`.

Take the linear combination `this`.
-/
theorem band_w {z : ℂ} (hz : 0 < z.re) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    ∫ g in bnd D 1 (Real.exp (c * τ)), H g * (D g : ℂ) ^ z ∂ν =
      (Complex.exp (((c * τ : ℝ) : ℂ) * z) - 1) * ∫ g in {g | D g < 1}, H g * (D g : ℂ) ^ z ∂ν := by
  have hc := S.cpos
  have hle : Real.exp (c * τ) ≤ Real.exp c := Real.exp_le_exp.2 (by nlinarith)
  have hset : {g | D g < Real.exp (c * τ)} = {g | D g < 1} ∪ bnd D 1 (Real.exp (c * τ)) := by
    ext g; simp only [bnd, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro h; by_cases h' : D g < 1
      · exact Or.inl h'
      · exact Or.inr ⟨not_lt.1 h', h⟩
    · rintro (h | ⟨_, h⟩)
      · exact h.trans_le (Real.one_le_exp (by positivity))
      · exact h
  have hdisj : Disjoint {g | D g < 1} (bnd D 1 (Real.exp (c * τ))) := by
    rw [Set.disjoint_left]; rintro g h ⟨h3, _⟩; exact absurd h3 (not_le.2 h)
  have hB : IntegrableOn (fun g => H g * (D g : ℂ) ^ z) (bnd D 1 (Real.exp (c * τ))) ν := by
    refine S.intOn (S.mw z) (S.mset_bnd _ _) (S.bnd_sub le_rfl hle) (K := C * Real.exp c ^ z.re) ?_
    rintro g ⟨_, h2⟩
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (S.pos g)]
    exact mul_le_mul (S.bdd g) (Real.rpow_le_rpow (S.pos g).le (h2.le.trans hle) hz.le)
      (Real.rpow_nonneg (S.pos g).le _) S.nonneg
  have hA : IntegrableOn (fun g => H g * (D g : ℂ) ^ z) {g | D g < 1} ν :=
    (integrable_indicator_iff (S.mset_lt 1)).1 (S.intJ hz)
  have := S.shift_J z (S.intJ hz) τ
  rw [hset, setIntegral_union hdisj (S.mset_bnd _ _) hA hB] at this
  linear_combination this

/- English proof (translation)
Establish `hc` using `S.cpos`. Establish `e1 : Real.exp (c * a) * Real.exp (c * b) = Real.exp (c * (a + b))`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Establish `hexp1 : ∀ x, 0 ≤ x → x ≤ 1 → Real.exp (c * x) ≤ Real.exp c` using `fun x _ h1 => Real.exp_le_exp.2 (by nlinarith)`.

Establish `hone : ∀ x, 0 ≤ x → 1 ≤ Real.exp (c * x)` using `fun x h0 => Real.one_le_exp (by positivity)`. Establish `hsplit : bnd D 1 (Real.exp (c * (a + b))) = bnd D 1 (Real.exp (c * a)) ∪ bnd D (Real.exp (c * a)) (Real.exp (c * (a + b)))`. Use extensionality with `g`. Simplify using `only [bnd, Set.mem_union, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Distinguish the cases in `h : D g < Real.exp (c * a)`. Conclude with `Or.inl ⟨h1, h⟩`. Conclude with `Or.inr ⟨not_lt.1 h, h2⟩`. Introduce and unpack `(⟨h1, h2⟩ | ⟨h1, h2⟩)`.

Conclude with `⟨h1, h2.trans_le (Real.exp_le_exp.2 (by nlinarith))⟩`. Conclude with `⟨(hone a ha).trans h1, h2⟩`. Establish `hdisj : Disjoint (bnd D 1 (Real.exp (c * a))) (bnd D (Real.exp (c * a)) (Real.exp (c * (a + b))))`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `g ⟨_, h2⟩ ⟨h3, _⟩`.

Conclude with `absurd h3 (not_le.2 h2)`. Rewrite using `[hsplit, setIntegral_union hdisj (S.mset_bnd _ _) (S.intOn hm (S.mset_bnd _ _) (S.bnd_sub le_rfl (hexp1 a ha (by linarith))) (fun g _ => hK g)) (S.intOn hm (S.mset_bnd _ _) (S.bnd_sub (hone a ha) (hexp1 _ (by linarith) hab)) (fun g _ => hK g))]`. Use `congr 1`. Establish `hpt : ∀ g, (bnd D (Real.exp (c * a)) (Real.exp (c * (a + b)))).indicator Hh g = (bnd D 1 (Real.exp (c * b))).indicator Hh (T (-a) g)`. Introduce `g`.

Establish `hiff : T (-a) g ∈ bnd D 1 (Real.exp (c * b)) ↔ g ∈ bnd D (Real.exp (c * a)) (Real.exp (c * (a + b)))`. Simplify using `only [bnd, Set.mem_ofPred_eq, S.DT, le_exp_neg_mul, exp_neg_mul_lt, mul_one, e1]`. Distinguish the cases in `hg : g ∈ bnd D (Real.exp (c * a)) (Real.exp (c * (a + b)))`. Rewrite using `[Set.indicator_of_mem hg, Set.indicator_of_mem (hiff.2 hg), hT]`. Rewrite using `[Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hiff.1 h))]`.

Rewrite using `[← integral_indicator (S.mset_bnd _ _), ← integral_indicator (S.mset_bnd _ _)]`. Repeatedly rewrite using `[hpt]`. Use `S.shift (-a) _ (hm.indicator (S.mset_bnd _ _)) ?_ ?_` and prove the remaining obligations. Introduce `γ g`. Simplify using `only [Set.indicator, bnd, Set.mem_ofPred_eq, S.Dr, hr]`.

Reduce the equality to equality of the corresponding arguments. Conclude with `(integrable_indicator_iff (S.mset_bnd _ _)).2 (S.intOn hm (S.mset_bnd _ _) (S.bnd_sub le_rfl (hexp1 b hb (by linarith))) (fun g _ => hK g))`.
-/
theorem add_band {Hh : G → ℂ} (hm : Measurable Hh) (hT : ∀ t g, Hh (T t g) = Hh g)
    (hr : ∀ γ g, Hh (r γ g) = Hh g) {K : ℝ} (hK : ∀ g, ‖Hh g‖ ≤ K) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) :
    ∫ g in bnd D 1 (Real.exp (c * (a + b))), Hh g ∂ν =
      (∫ g in bnd D 1 (Real.exp (c * a)), Hh g ∂ν) + ∫ g in bnd D 1 (Real.exp (c * b)), Hh g ∂ν := by
  have hc := S.cpos
  have e1 : Real.exp (c * a) * Real.exp (c * b) = Real.exp (c * (a + b)) := by
    rw [← Real.exp_add]; ring_nf
  have hexp1 : ∀ x, 0 ≤ x → x ≤ 1 → Real.exp (c * x) ≤ Real.exp c :=
    fun x _ h1 => Real.exp_le_exp.2 (by nlinarith)
  have hone : ∀ x, 0 ≤ x → 1 ≤ Real.exp (c * x) := fun x h0 => Real.one_le_exp (by positivity)
  have hsplit : bnd D 1 (Real.exp (c * (a + b))) =
      bnd D 1 (Real.exp (c * a)) ∪ bnd D (Real.exp (c * a)) (Real.exp (c * (a + b))) := by
    ext g; simp only [bnd, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : D g < Real.exp (c * a)
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨not_lt.1 h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2.trans_le (Real.exp_le_exp.2 (by nlinarith))⟩
      · exact ⟨(hone a ha).trans h1, h2⟩
  have hdisj : Disjoint (bnd D 1 (Real.exp (c * a))) (bnd D (Real.exp (c * a)) (Real.exp (c * (a + b)))) := by
    rw [Set.disjoint_left]; rintro g ⟨_, h2⟩ ⟨h3, _⟩; exact absurd h3 (not_le.2 h2)
  rw [hsplit, setIntegral_union hdisj (S.mset_bnd _ _)
    (S.intOn hm (S.mset_bnd _ _) (S.bnd_sub le_rfl (hexp1 a ha (by linarith))) (fun g _ => hK g))
    (S.intOn hm (S.mset_bnd _ _) (S.bnd_sub (hone a ha) (hexp1 _ (by linarith) hab)) (fun g _ => hK g))]
  congr 1
  have hpt : ∀ g, (bnd D (Real.exp (c * a)) (Real.exp (c * (a + b)))).indicator Hh g =
      (bnd D 1 (Real.exp (c * b))).indicator Hh (T (-a) g) := by
    intro g
    have hiff : T (-a) g ∈ bnd D 1 (Real.exp (c * b)) ↔ g ∈ bnd D (Real.exp (c * a)) (Real.exp (c * (a + b))) := by
      simp only [bnd, Set.mem_ofPred_eq, S.DT, le_exp_neg_mul, exp_neg_mul_lt, mul_one, e1]
    by_cases hg : g ∈ bnd D (Real.exp (c * a)) (Real.exp (c * (a + b)))
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hiff.2 hg), hT]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hiff.1 h))]
  rw [← integral_indicator (S.mset_bnd _ _), ← integral_indicator (S.mset_bnd _ _)]
  simp_rw [hpt]
  refine S.shift (-a) _ (hm.indicator (S.mset_bnd _ _)) ?_ ?_
  · intro γ g; simp only [Set.indicator, bnd, Set.mem_ofPred_eq, S.Dr, hr]; congr
  · exact (integrable_indicator_iff (S.mset_bnd _ _)).2
      (S.intOn hm (S.mset_bnd _ _) (S.bnd_sub le_rfl (hexp1 b hb (by linarith))) (fun g _ => hK g))

/- English proof (translation)
Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `key : ∀ j : ℕ, j ≤ n → ∫ g in bnd D 1 (Real.exp (c * (j / n))), Hh g ∂ν = j * ∫ g in bnd D 1 (Real.exp (c * (1 / n))), Hh g ∂ν`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`.

Introduce `_`. Establish `: bnd D 1 (Real.exp (c * ((0 : ℕ) / n))) = ∅`. Use extensionality with `g`. Simplify using `only [bnd, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt, Nat.cast_zero, zero_div, mul_zero, Real.exp_zero]`. Conclude with `id`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Consider the case `succ j ih`. Introduce `hj`. Establish `h1 : ((j + 1 : ℕ) : ℝ) / n = j / n + 1 / n` using `by push_cast; ring`.

Establish `h2 : (j : ℝ) / n + 1 / n ≤ 1`. Rewrite using `[← h1]; exact (div_le_one hn').2 (by exact_mod_cast hj)`. Rewrite using `[h1, S.add_band hm hT hr hK (by positivity) (by positivity) h2, ih (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `key n le_rfl` as an intermediate fact. Rewrite `this` using `[div_self hn'.ne', mul_one]`. Then use the resulting hypothesis.
-/
theorem frac_band {Hh : G → ℂ} (hm : Measurable Hh) (hT : ∀ t g, Hh (T t g) = Hh g)
    (hr : ∀ γ g, Hh (r γ g) = Hh g) {K : ℝ} (hK : ∀ g, ‖Hh g‖ ≤ K) (n : ℕ) (hn : 0 < n) :
    ∫ g in bnd D 1 (Real.exp c), Hh g ∂ν = n * ∫ g in bnd D 1 (Real.exp (c * (1 / n))), Hh g ∂ν := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ j : ℕ, j ≤ n → ∫ g in bnd D 1 (Real.exp (c * (j / n))), Hh g ∂ν =
      j * ∫ g in bnd D 1 (Real.exp (c * (1 / n))), Hh g ∂ν := by
    intro j
    induction j with
    | zero =>
      intro _
      have : bnd D 1 (Real.exp (c * ((0 : ℕ) / n))) = ∅ := by
        ext g; simp only [bnd, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt,
          Nat.cast_zero, zero_div, mul_zero, Real.exp_zero]
        exact id
      rw [this]; simp
    | succ j ih =>
      intro hj
      have h1 : ((j + 1 : ℕ) : ℝ) / n = j / n + 1 / n := by push_cast; ring
      have h2 : (j : ℝ) / n + 1 / n ≤ 1 := by
        rw [← h1]; exact (div_le_one hn').2 (by exact_mod_cast hj)
      rw [h1, S.add_band hm hT hr hK (by positivity) (by positivity) h2, ih (by omega)]
      push_cast; ring
  have := key n le_rfl
  rwa [div_self hn'.ne', mul_one] at this

/- English proof (translation)
Use `set J := ∫ g in {g | D g < 1}, H g * (D g : ℂ) ^ z ∂ν with hJ`. Use `set I := ∫ g in bnd D 1 (Real.exp c), H g ∂ν with hI`. Use `set V := ν.real (bnd D 1 (Real.exp c)) with hV`. Establish `hc` using `S.cpos`. Establish `hc' : (c : ℂ) ≠ 0` using `by exact_mod_cast hc.ne'`.

Establish `key : ∀ n : ℕ, 0 < n → c * ‖z‖ ≤ n → ‖(c : ℂ) * z * J - I‖ ≤ (‖(c : ℂ) * z‖ ^ 2 * ‖J‖ + 2 * C * c * ‖z‖ * V) / n`. Introduce `n hn hnz`. Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Use `set τ : ℝ := 1 / n with hτ`. Establish `hτ0 : 0 ≤ τ` using `by positivity`.

Establish `hτ1 : τ ≤ 1` using `by rw [hτ]; exact (div_le_one hn').2 (by exact_mod_cast hn)`. Establish `hτz : c * τ * ‖z‖ ≤ 1`. Rewrite using `[hτ, mul_one_div, div_mul_eq_mul_div, div_le_one hn']`. Conclude with `hnz`. Establish `hle : Real.exp (c * τ) ≤ Real.exp c` using `Real.exp_le_exp.2 (by nlinarith)`.

Establish `hB` using `S.band_w hz hτ0 hτ1`. Establish `hHn : I = n * ∫ g in bnd D 1 (Real.exp (c * τ)), H g ∂ν` using `S.frac_band S.mH S.HT S.Hr S.bdd n hn`. Establish `hVn : V = n * ν.real (bnd D 1 (Real.exp (c * τ)))`. Use `S.frac_band (Hh := fun _ => (1 : ℂ)) measurable_const (fun _ _ => rfl) (fun _ _ => rfl) (K := 1) (fun _ => by simp) n hn` as an intermediate fact. Simplify using `only [setIntegral_const, Complex.real_smul, mul_one] at this`.

Conclude with `this` after adjusting the coercions. Establish `hBw : IntegrableOn (fun g => H g * (D g : ℂ) ^ z) (bnd D 1 (Real.exp (c * τ))) ν`. Use `S.intOn (S.mw z) (S.mset_bnd _ _) (S.bnd_sub le_rfl hle) (K := C * Real.exp c ^ z.re) ?_` and prove the remaining obligations. Introduce and unpack `g ⟨_, h2⟩`. Rewrite using `[norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (S.pos g)]`.

Conclude with `mul_le_mul (S.bdd g) (Real.rpow_le_rpow (S.pos g).le (h2.le.trans hle) hz.le) (Real.rpow_nonneg (S.pos g).le _) S.nonneg`. Establish `hBH : IntegrableOn H (bnd D 1 (Real.exp (c * τ))) ν` using `S.intOn S.mH (S.mset_bnd _ _) (S.bnd_sub le_rfl hle) (fun g _ => S.bdd g)`. Establish `herr : ‖(∫ g in bnd D 1 (Real.exp (c * τ)), H g * (D g : ℂ) ^ z ∂ν) - ∫ g in bnd D 1 (Real.exp (c * τ)), H g ∂ν‖ ≤ C * (2 * (c * τ * ‖z‖)) * ν.real (bnd D 1 (Real.exp (c * τ)))`. Rewrite using `[← integral_sub hBw hBH]`. Use `norm_setIntegral_le_of_norm_le_const (S.fin_sub (S.bnd_sub le_rfl hle)) ?_` and prove the remaining obligations.

Introduce and unpack `g ⟨h1, h2⟩`. Establish `hl0 : 0 ≤ Real.log (D g)` using `Real.log_nonneg h1`. Establish `hl1 : Real.log (D g) < c * τ` using `(Real.log_lt_iff_lt_exp (S.pos g)).2 h2`. Establish `hx : ‖(Real.log (D g) : ℂ) * z‖ ≤ c * τ * ‖z‖`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl0]`.

Conclude with `mul_le_mul_of_nonneg_right hl1.le (norm_nonneg _)`. Establish `: H g * (D g : ℂ) ^ z - H g = H g * (Complex.exp (Real.log (D g) * z) - 1)`. Rewrite using `[cpow_pos (S.pos g)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, norm_mul]`.

Conclude with `mul_le_mul (S.bdd g) ((Complex.norm_exp_sub_one_le (hx.trans hτz)).trans (by linarith)) (norm_nonneg _) S.nonneg`. Establish `hfac : ‖(c : ℂ) * z - n * (Complex.exp (((c * τ : ℝ) : ℂ) * z) - 1)‖ ≤ ‖(c : ℂ) * z‖ ^ 2 / n`. Establish `hnx : (n : ℂ) * (((c * τ : ℝ) : ℂ) * z) = c * z`. Establish `hnC : (n : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`. Rewrite using `[hτ]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hxn : ‖((c * τ : ℝ) : ℂ) * z‖ = ‖(c : ℂ) * z‖ / n`. Rewrite using `[← hnx, norm_mul (n : ℂ), Complex.norm_natCast]`. Clear the denominators using the available nonvanishing facts.

Establish `hx1 : ‖((c * τ : ℝ) : ℂ) * z‖ ≤ 1`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hτz`. Establish `: (c : ℂ) * z - n * (Complex.exp (((c * τ : ℝ) : ℂ) * z) - 1) = -(n * (Complex.exp (((c * τ : ℝ) : ℂ) * z) - 1 - ((c * τ : ℝ) : ℂ) * z))`. Rewrite using `[← hnx]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, norm_neg, norm_mul, Complex.norm_natCast]`. Combine the equalities or inequalities in the displayed calculation. Establish `hid : (c : ℂ) * z * J - I = ((c : ℂ) * z - n * (Complex.exp (((c * τ : ℝ) : ℂ) * z) - 1)) * J + n * ((∫ g in bnd D 1 (Real.exp (c * τ)), H g * (D g : ℂ) ^ z ∂ν) - ∫ g in bnd D 1 (Real.exp (c * τ)), H g ∂ν)`. Rewrite using `[hHn]`. Take the linear combination `(-(n : ℂ)) * hB`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hid]`. Use `(norm_add_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, Complex.norm_natCast]`. Use `_ ≤ ‖(c : ℂ) * z‖ ^ 2 / n * ‖J‖ + n * (C * (2 * (c * τ * ‖z‖)) * ν.real (bnd D 1 (Real.exp (c * τ)))) := by gcongr`.

Use `_ = (‖(c : ℂ) * z‖ ^ 2 * ‖J‖ + 2 * C * c * ‖z‖ * V) / n := by`. Rewrite using `[hVn, hτ]`. Clear the denominators using the available nonvanishing facts. Establish `hle : ‖(c : ℂ) * z * J - I‖ ≤ 0`. Take `⟨N, hN⟩` from `exists_nat_ge (c * ‖z‖)`.

Use `ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat (‖(c : ℂ) * z‖ ^ 2 * ‖J‖ + 2 * C * c * ‖z‖ * V)) ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop (max N 1)] with n hn`. Conclude with `key n (lt_of_lt_of_le Nat.one_pos ((le_max_right _ _).trans hn)) (hN.trans (by exact_mod_cast (le_max_left _ _).trans hn))`. Establish `h0 : (c : ℂ) * z * J = I` using `sub_eq_zero.1 (norm_le_zero_iff.1 hle)`. Rewrite using `[← h0]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem main {z : ℂ} (hz : 0 < z.re) :
    z * ∫ g in {g | D g < 1}, H g * (D g : ℂ) ^ z ∂ν = (c : ℂ)⁻¹ * ∫ g in bnd D 1 (Real.exp c), H g ∂ν := by
  set J := ∫ g in {g | D g < 1}, H g * (D g : ℂ) ^ z ∂ν with hJ
  set I := ∫ g in bnd D 1 (Real.exp c), H g ∂ν with hI
  set V := ν.real (bnd D 1 (Real.exp c)) with hV
  have hc := S.cpos
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have key : ∀ n : ℕ, 0 < n → c * ‖z‖ ≤ n →
      ‖(c : ℂ) * z * J - I‖ ≤ (‖(c : ℂ) * z‖ ^ 2 * ‖J‖ + 2 * C * c * ‖z‖ * V) / n := by
    intro n hn hnz
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set τ : ℝ := 1 / n with hτ
    have hτ0 : 0 ≤ τ := by positivity
    have hτ1 : τ ≤ 1 := by rw [hτ]; exact (div_le_one hn').2 (by exact_mod_cast hn)
    have hτz : c * τ * ‖z‖ ≤ 1 := by
      rw [hτ, mul_one_div, div_mul_eq_mul_div, div_le_one hn']; exact hnz
    have hle : Real.exp (c * τ) ≤ Real.exp c := Real.exp_le_exp.2 (by nlinarith)
    have hB := S.band_w hz hτ0 hτ1
    have hHn : I = n * ∫ g in bnd D 1 (Real.exp (c * τ)), H g ∂ν := S.frac_band S.mH S.HT S.Hr S.bdd n hn
    have hVn : V = n * ν.real (bnd D 1 (Real.exp (c * τ))) := by
      have := S.frac_band (Hh := fun _ => (1 : ℂ)) measurable_const (fun _ _ => rfl) (fun _ _ => rfl)
        (K := 1) (fun _ => by simp) n hn
      simp only [setIntegral_const, Complex.real_smul, mul_one] at this
      exact_mod_cast this

    have hBw : IntegrableOn (fun g => H g * (D g : ℂ) ^ z) (bnd D 1 (Real.exp (c * τ))) ν := by
      refine S.intOn (S.mw z) (S.mset_bnd _ _) (S.bnd_sub le_rfl hle) (K := C * Real.exp c ^ z.re) ?_
      rintro g ⟨_, h2⟩
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (S.pos g)]
      exact mul_le_mul (S.bdd g) (Real.rpow_le_rpow (S.pos g).le (h2.le.trans hle) hz.le)
        (Real.rpow_nonneg (S.pos g).le _) S.nonneg
    have hBH : IntegrableOn H (bnd D 1 (Real.exp (c * τ))) ν :=
      S.intOn S.mH (S.mset_bnd _ _) (S.bnd_sub le_rfl hle) (fun g _ => S.bdd g)
    have herr : ‖(∫ g in bnd D 1 (Real.exp (c * τ)), H g * (D g : ℂ) ^ z ∂ν) -
        ∫ g in bnd D 1 (Real.exp (c * τ)), H g ∂ν‖ ≤
          C * (2 * (c * τ * ‖z‖)) * ν.real (bnd D 1 (Real.exp (c * τ))) := by
      rw [← integral_sub hBw hBH]
      refine norm_setIntegral_le_of_norm_le_const (S.fin_sub (S.bnd_sub le_rfl hle)) ?_
      rintro g ⟨h1, h2⟩
      have hl0 : 0 ≤ Real.log (D g) := Real.log_nonneg h1
      have hl1 : Real.log (D g) < c * τ := (Real.log_lt_iff_lt_exp (S.pos g)).2 h2
      have hx : ‖(Real.log (D g) : ℂ) * z‖ ≤ c * τ * ‖z‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl0]
        exact mul_le_mul_of_nonneg_right hl1.le (norm_nonneg _)
      have : H g * (D g : ℂ) ^ z - H g = H g * (Complex.exp (Real.log (D g) * z) - 1) := by
        rw [cpow_pos (S.pos g)]; ring
      rw [this, norm_mul]
      exact mul_le_mul (S.bdd g) ((Complex.norm_exp_sub_one_le (hx.trans hτz)).trans (by linarith))
        (norm_nonneg _) S.nonneg

    have hfac : ‖(c : ℂ) * z - n * (Complex.exp (((c * τ : ℝ) : ℂ) * z) - 1)‖ ≤ ‖(c : ℂ) * z‖ ^ 2 / n := by
      have hnx : (n : ℂ) * (((c * τ : ℝ) : ℂ) * z) = c * z := by
        have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
        rw [hτ]; push_cast; field_simp
      have hxn : ‖((c * τ : ℝ) : ℂ) * z‖ = ‖(c : ℂ) * z‖ / n := by
        rw [← hnx, norm_mul (n : ℂ), Complex.norm_natCast]; field_simp
      have hx1 : ‖((c * τ : ℝ) : ℂ) * z‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hτz
      have : (c : ℂ) * z - n * (Complex.exp (((c * τ : ℝ) : ℂ) * z) - 1) =
          -(n * (Complex.exp (((c * τ : ℝ) : ℂ) * z) - 1 - ((c * τ : ℝ) : ℂ) * z)) := by
        rw [← hnx]; ring
      rw [this, norm_neg, norm_mul, Complex.norm_natCast]
      calc (n : ℝ) * ‖Complex.exp (((c * τ : ℝ) : ℂ) * z) - 1 - ((c * τ : ℝ) : ℂ) * z‖
          ≤ n * ‖((c * τ : ℝ) : ℂ) * z‖ ^ 2 := by gcongr; exact Complex.norm_exp_sub_one_sub_id_le hx1
        _ = ‖(c : ℂ) * z‖ ^ 2 / n := by rw [hxn]; field_simp
    have hid : (c : ℂ) * z * J - I = ((c : ℂ) * z - n * (Complex.exp (((c * τ : ℝ) : ℂ) * z) - 1)) * J +
        n * ((∫ g in bnd D 1 (Real.exp (c * τ)), H g * (D g : ℂ) ^ z ∂ν) -
          ∫ g in bnd D 1 (Real.exp (c * τ)), H g ∂ν) := by
      rw [hHn]; linear_combination (-(n : ℂ)) * hB
    calc ‖(c : ℂ) * z * J - I‖
        ≤ ‖(c : ℂ) * z - n * (Complex.exp (((c * τ : ℝ) : ℂ) * z) - 1)‖ * ‖J‖ +
          n * ‖(∫ g in bnd D 1 (Real.exp (c * τ)), H g * (D g : ℂ) ^ z ∂ν) -
            ∫ g in bnd D 1 (Real.exp (c * τ)), H g ∂ν‖ := by
          rw [hid]; refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_mul, norm_mul, Complex.norm_natCast]
      _ ≤ ‖(c : ℂ) * z‖ ^ 2 / n * ‖J‖ + n * (C * (2 * (c * τ * ‖z‖)) * ν.real (bnd D 1 (Real.exp (c * τ)))) := by
          gcongr
      _ = (‖(c : ℂ) * z‖ ^ 2 * ‖J‖ + 2 * C * c * ‖z‖ * V) / n := by
          rw [hVn, hτ]; field_simp
  have hle : ‖(c : ℂ) * z * J - I‖ ≤ 0 := by
    obtain ⟨N, hN⟩ := exists_nat_ge (c * ‖z‖)
    refine ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat
      (‖(c : ℂ) * z‖ ^ 2 * ‖J‖ + 2 * C * c * ‖z‖ * V)) ?_
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    exact key n (lt_of_lt_of_le Nat.one_pos ((le_max_right _ _).trans hn))
      (hN.trans (by exact_mod_cast (le_max_left _ _).trans hn))
  have h0 : (c : ℂ) * z * J = I := sub_eq_zero.1 (norm_le_zero_iff.1 hle)
  rw [← h0]; field_simp

end Setup

end HeightBoundSetup

/- English proof (translation)
Introduce `hD hW hV E _ _ _ k μ _ hk β hβ H₀ hm hr hc hb z hz`. Take `⟨hpos, hmul, hcont, hrat, -, -, hsc, -, -, -, -⟩` from `hD E k`. Take `⟨-, hshift, hint⟩` from `hV E k μ hk β hβ`. Establish `hband` using `(hW E k μ hk).2 β hβ`. Take `⟨C, hC⟩` from `hb`.

Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC 1)`. Establish `hcpos : (0 : ℝ) < k * Module.finrank ℚ E`. Establish `: 0 < Module.finrank ℚ E` using `Module.finrank_pos`. Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Check the signs of the components of the expression.

Establish `hb' : band E k = HeightBoundSetup.bnd Dt 1 (Real.exp ((k : ℝ) * Module.finrank ℚ E))`. Use extensionality with `g`. Simplify using `[band, HeightBoundSetup.bnd, hsc]`. Establish `S : HeightBoundSetup.Setup (μ.withDensity β) (Dt : GA E k → ℝ) H₀ (fun t g => splitCentre E k t * g) (fun γ g => ratGL E k γ * g) ((k : ℝ) * Module.finrank ℚ E) C` using `{ mD := hcont.measurable mH := hm pos := hpos DT := fun t g => by rw [hmul, hsc] HT := fun t g => hc t g Dr := fun γ g => by rw [hmul, hrat, one_mul] Hr := fun γ g => hr γ g bdd := hC nonneg := hC0 cpos := hcpos shift := fun t Φ hΦ hΦr hΦi => hshift t Φ hΦ hΦr hΦi int := hint ban …`. Use `S.main hz` as an intermediate fact.

Rewrite using `[hb', this]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem height_bound_of_weights : D0 → W0 → V1 → E1 := by
  intro hD hW hV E _ _ _ k μ _ hk β hβ H₀ hm hr hc hb z hz
  obtain ⟨hpos, hmul, hcont, hrat, -, -, hsc, -, -, -, -⟩ := hD E k
  obtain ⟨-, hshift, hint⟩ := hV E k μ hk β hβ
  have hband := (hW E k μ hk).2 β hβ
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  have hcpos : (0 : ℝ) < k * Module.finrank ℚ E := by
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  have hb' : band E k = HeightBoundSetup.bnd Dt 1 (Real.exp ((k : ℝ) * Module.finrank ℚ E)) := by
    ext g; simp [band, HeightBoundSetup.bnd, hsc]
  have S : HeightBoundSetup.Setup (μ.withDensity β) (Dt : GA E k → ℝ) H₀ (fun t g => splitCentre E k t * g)
      (fun γ g => ratGL E k γ * g) ((k : ℝ) * Module.finrank ℚ E) C :=
    { mD := hcont.measurable
      mH := hm
      pos := hpos
      DT := fun t g => by rw [hmul, hsc]
      HT := fun t g => hc t g
      Dr := fun γ g => by rw [hmul, hrat, one_mul]
      Hr := fun γ g => hr γ g
      bdd := hC
      nonneg := hC0
      cpos := hcpos
      shift := fun t Φ hΦ hΦr hΦi => hshift t Φ hΦ hΦr hΦi
      int := hint
      band := by rw [← hb']; exact hband }
  have := S.main hz
  rw [hb', this]
  congr 1
  push_cast
  ring

end PositivityTheory.AdelicQuotientData

end
