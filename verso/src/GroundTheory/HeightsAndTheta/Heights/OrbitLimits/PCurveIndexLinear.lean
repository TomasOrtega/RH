import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveIndexLinear
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveRingFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveClosedPointChart
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsInvertibleIndexMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace CurveIndexLinearAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def cu (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ a k

omit [∀ k, Fintype (ι k)] in
/- English proof (translation)
Simplify using `[chartUnit, cu]`.
-/
theorem chartUnit_one (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) : chartUnit y c a 1 = cu y c a := by
  simp [chartUnit, cu]

omit [∀ k, Fintype (ι k)] in
/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)`.
-/
theorem cu_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ) :
    cu y c a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)

omit [∀ k, Fintype (ι k)] in
/- English proof (translation)
Rewrite using `[cu, cu, cu, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => zpow_add₀ (hc k) _ _`.
-/
theorem cu_add {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a a' : K → ℤ) :
    cu y c (a + a') = cu y c a * cu y c a' := by
  rw [cu, cu, cu, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => zpow_add₀ (hc k) _ _

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[cu, cu, ← Finset.prod_div_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => (div_zpow _ _ _).symm`.
-/
theorem cu_div (y : (Σ k, ι k) → Ω) (c c' : ∀ k, ι k) (a : K → ℤ) :
    cu y c' a / cu y c a = ∏ k, (y ⟨k, c' k⟩ / y ⟨k, c k⟩) ^ a k := by
  rw [cu, cu, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun k _ => (div_zpow _ _ _).symm

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `e : ∀ c : ∀ k, ι k, ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) = (cu y c a)⁻¹`. Introduce `c`. Simplify using `[cu, zpow_neg, Finset.prod_inv_distrib]`. Use `show (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ chartRingZ y c) ↔ _`. Simplify using `only [e, div_eq_mul_inv]`.
-/
theorem mem_chartLat_one {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} :
    s ∈ chartLat y a 1 ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → s / cu y c a ∈ chartRingZ y c := by
  have e : ∀ c : ∀ k, ι k, ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) = (cu y c a)⁻¹ := by
    intro c
    simp [cu, zpow_neg, Finset.prod_inv_distrib]
  show (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ chartRingZ y c) ↔ _
  simp only [e, div_eq_mul_inv]

def secIdeal (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) : AddSubgroup Ω :=
  (chartLat y a 1).map (AddMonoidHom.mulLeft (cu y c a)⁻¹)

def gen (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (c' : ∀ k, ι k) : Ω :=
  cu y c' a / cu y c a

omit [∀ k, Fintype (ι k)] in
/- English proof (translation)
The claim follows from `div_ne_zero (cu_ne_zero hc' a) (cu_ne_zero hc a)`.
-/
theorem gen_ne_zero {y : (Σ k, ι k) → Ω} {c c' : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) (a : K → ℤ) : gen y c a c' ≠ 0 :=
  div_ne_zero (cu_ne_zero hc' a) (cu_ne_zero hc a)

omit [∀ k, Fintype (ι k)] in
/- English proof (translation)
Rewrite using `[gen, gen, gen, cu_add hc, cu_add hc', mul_div_mul_comm]`.
-/
theorem gen_add {y : (Σ k, ι k) → Ω} {c c' : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) (a a' : K → ℤ) : gen y c (a + a') c' = gen y c a c' * gen y c a' c' := by
  rw [gen, gen, gen, cu_add hc, cu_add hc', mul_div_mul_comm]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `hu` using `cu_ne_zero hc a`. Rewrite using `[secIdeal, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩ c' hc'`. Establish `hu'` using `cu_ne_zero hc' a`.

Use `mem_chartLat_one.mp hx c' hc' using 1` and compare the differences between its conclusion and the goal. Simplify using `only [AddMonoidHom.coe_mulLeft, gen]`. Clear the denominators using the available nonvanishing facts. Introduce `h`. Use `⟨z * cu y c a, mem_chartLat_one.mpr fun c' hc' => ?_, ?_⟩` and prove the remaining obligations.

Establish `hu'` using `cu_ne_zero hc' a`. Use `h c' hc' using 1` and compare the differences between its conclusion and the goal. Simplify using `only [gen]`. Clear the denominators using the available nonvanishing facts. Use `show (cu y c a)⁻¹ * (z * cu y c a) = z`.

Rewrite using `[mul_comm z, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]`.
-/
theorem mem_secIdeal {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : K → ℤ} {z : Ω} :
    z ∈ secIdeal y c a ↔ ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) → z / gen y c a c' ∈ chartRingZ y c' := by
  have hu := cu_ne_zero hc a
  rw [secIdeal, AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩ c' hc'
    have hu' := cu_ne_zero hc' a
    convert mem_chartLat_one.mp hx c' hc' using 1
    simp only [AddMonoidHom.coe_mulLeft, gen]
    field_simp
  · intro h
    refine ⟨z * cu y c a, mem_chartLat_one.mpr fun c' hc' => ?_, ?_⟩
    · have hu' := cu_ne_zero hc' a
      convert h c' hc' using 1
      simp only [gen]
      field_simp
    · show (cu y c a)⁻¹ * (z * cu y c a) = z
      rw [mul_comm z, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `b hb z hz`. Rewrite `hz`, the goal using `[mem_secIdeal hc]`. Introduce `c' hc'`. Rewrite using `[mul_div_assoc]`. Conclude with `(chartRingZ y c').mul_mem (mem_curveRing.mp hb c' hc') (hz c' hc')`.
-/
theorem mul_mem_secIdeal {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : K → ℤ} :
    ∀ b ∈ curveRing y, ∀ z ∈ secIdeal y c a, b * z ∈ secIdeal y c a := by
  intro b hb z hz
  rw [mem_secIdeal hc] at hz ⊢
  intro c' hc'
  rw [mul_div_assoc]
  exact (chartRingZ y c').mul_mem (mem_curveRing.mp hb c' hc') (hz c' hc')

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `hu` using `cu_ne_zero hc a`. Establish `hinj : Function.Injective (AddMonoidHom.mulLeft (cu y c a)⁻¹)` using `fun x x' h => mul_right_injective₀ (inv_ne_zero hu) h`. Establish `hB : (curveRing y).toAddSubgroup = (curveMul y (cu y c a)).map (AddMonoidHom.mulLeft (cu y c a)⁻¹)`. Rewrite using `[curveMul, AddSubgroup.map_map]`. Establish `e : (AddMonoidHom.mulLeft (cu y c a)⁻¹).comp (AddMonoidHom.mulLeft (cu y c a)) = AddMonoidHom.id Ω`.

Use extensionality with `x`. Simplify using `[hu]`. Rewrite using `[e, AddSubgroup.map_id]`. Rewrite using `[chartIndexLog, chartUnit_one, hB, secIdeal, genIndex, genIndex, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]`.
-/
theorem chartIndexLog_eq {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ) :
    chartIndexLog y c a 1 = Real.log (genIndex (secIdeal y c a) (curveRing y).toAddSubgroup) := by
  have hu := cu_ne_zero hc a
  have hinj : Function.Injective (AddMonoidHom.mulLeft (cu y c a)⁻¹) := fun x x' h =>
    mul_right_injective₀ (inv_ne_zero hu) h
  have hB : (curveRing y).toAddSubgroup =
      (curveMul y (cu y c a)).map (AddMonoidHom.mulLeft (cu y c a)⁻¹) := by
    rw [curveMul, AddSubgroup.map_map]
    have e : (AddMonoidHom.mulLeft (cu y c a)⁻¹).comp (AddMonoidHom.mulLeft (cu y c a)) = AddMonoidHom.id Ω := by
      ext x
      simp [hu]
    rw [e, AddSubgroup.map_id]
  rw [chartIndexLog, chartUnit_one, hB, secIdeal, genIndex, genIndex,
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]

def locRing {y : (Σ k, ι k) → Ω} (m : Ideal (curveRing y)) (hm : m.IsPrime) (S : Subring Ω)
    (hS : ∀ b : curveRing y, (b : Ω) ∈ S) : Subring Ω where
  carrier := {r | ∃ b : curveRing y, b ∉ m ∧ (b : Ω) * r ∈ S}
  mul_mem' := by
    rintro r s ⟨b, hb, hbr⟩ ⟨b', hb', hbs⟩
    refine ⟨b * b', fun h => (hm.mem_or_mem h).elim hb hb', ?_⟩
    have := S.mul_mem hbr hbs
    convert this using 1
    push_cast
    ring
  one_mem' := ⟨1, fun h => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  add_mem' := by
    rintro r s ⟨b, hb, hbr⟩ ⟨b', hb', hbs⟩
    refine ⟨b * b', fun h => (hm.mem_or_mem h).elim hb hb', ?_⟩
    have := S.add_mem (S.mul_mem (hS b') hbr) (S.mul_mem (hS b) hbs)
    convert this using 1
    push_cast
    ring
  zero_mem' := ⟨1, fun h => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  neg_mem' := by
    rintro r ⟨b, hb, hbr⟩
    exact ⟨b, hb, by rw [mul_neg]; exact S.neg_mem hbr⟩

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]`. Conclude with `S.pow_mem hx n`. Consider the case `negSucc n => rw [zpow_negSucc, ← inv_pow]`. Conclude with `S.pow_mem hx' _`.
-/
theorem zpow_mem_of {S : Subring Ω} {x : Ω} (hx : x ∈ S) (hx' : x⁻¹ ∈ S) (n : ℤ) : x ^ n ∈ S := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact S.pow_mem hx n
  | negSucc n => rw [zpow_negSucc, ← inv_pow]; exact S.pow_mem hx' _

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `hle : chartRingZ y c' ≤ subalgebraOfSubring (locRing m hm (curveRing y) fun b => b.2)`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩`. Take `⟨α, β, hβ, e⟩` from `hr p`. Conclude with `mem_subalgebraOfSubring.mpr ⟨β, hβ, by rw [e]; exact α.2⟩`.

Conclude with `mem_subalgebraOfSubring.mp (hle hrc)`.
-/
theorem chartRingZ_le_loc {y : (Σ k, ι k) → Ω} {m : Ideal (curveRing y)} (hm : m.IsPrime) {c' : ∀ k, ι k}
    (hr : ∀ p : Σ k, ι k, ∃ α β : curveRing y, β ∉ m ∧ (β : Ω) * (y p / y ⟨p.1, c' p.1⟩) = α) {r : Ω}
    (hrc : r ∈ chartRingZ y c') : ∃ b : curveRing y, b ∉ m ∧ (b : Ω) * r ∈ curveRing y := by
  have hle : chartRingZ y c' ≤ subalgebraOfSubring (locRing m hm (curveRing y) fun b => b.2) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨p, rfl⟩
    obtain ⟨α, β, hβ, e⟩ := hr p
    exact mem_subalgebraOfSubring.mpr ⟨β, hβ, by rw [e]; exact α.2⟩
  exact mem_subalgebraOfSubring.mp (hle hrc)

/- English proof (translation)
Use `choose f hf using h`. Set `F : (∀ k, ι k) → curveRing y` to `fun c'' => if h : (∀ k, y ⟨k, c'' k⟩ ≠ 0) then f c'' h else 1`. Establish `hF : ∀ c'', F c'' ∈ m.primeCompl`. Introduce `c''`. Distinguish the cases in `h : ∀ k, y ⟨k, c'' k⟩ ≠ 0`.

Simplify using `only [F, dif_pos h]`. Conclude with `(hf c'' h).1`. Simplify using `only [F, dif_neg h]`. Conclude with `m.primeCompl.one_mem`. Use `⟨∏ c'', F c'', Submonoid.prod_mem _ fun c'' _ => hF c'', fun c'' hc'' => ?_⟩` and prove the remaining obligations.

Take `⟨q, hq⟩ : F c'' ∣ ∏ c, F c` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ _)`. Rewrite using `[hq]`. Establish `h2 : (F c'' : Ω) * r c'' ∈ chartRingZ y c''` using `by simpa [F, dif_pos hc''] using (hf c'' hc'').2`. Establish `h3 : (q : Ω) ∈ chartRingZ y c''` using `mem_curveRing.mp q.2 c'' hc''`. Use `(chartRingZ y c'').mul_mem h3 h2` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem uniform_denom {y : (Σ k, ι k) → Ω} {m : Ideal (curveRing y)} (hm : m.IsPrime) (r : (∀ k, ι k) → Ω)
    (h : ∀ c'' : ∀ k, ι k, (∀ k, y ⟨k, c'' k⟩ ≠ 0) →
      ∃ b : curveRing y, b ∉ m ∧ (b : Ω) * r c'' ∈ chartRingZ y c'') :
    ∃ b : curveRing y, b ∉ m ∧ ∀ c'' : ∀ k, ι k, (∀ k, y ⟨k, c'' k⟩ ≠ 0) →
      (b : Ω) * r c'' ∈ chartRingZ y c'' := by
  classical
  choose f hf using h
  let F : (∀ k, ι k) → curveRing y := fun c'' => if h : (∀ k, y ⟨k, c'' k⟩ ≠ 0) then f c'' h else 1
  have hF : ∀ c'', F c'' ∈ m.primeCompl := by
    intro c''
    by_cases h : ∀ k, y ⟨k, c'' k⟩ ≠ 0
    · simp only [F, dif_pos h]; exact (hf c'' h).1
    · simp only [F, dif_neg h]; exact m.primeCompl.one_mem
  refine ⟨∏ c'', F c'', Submonoid.prod_mem _ fun c'' _ => hF c'', fun c'' hc'' => ?_⟩
  obtain ⟨q, hq⟩ : F c'' ∣ ∏ c, F c := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
  rw [hq]
  have h2 : (F c'' : Ω) * r c'' ∈ chartRingZ y c'' := by simpa [F, dif_pos hc''] using (hf c'' hc'').2
  have h3 : (q : Ω) ∈ chartRingZ y c'' := mem_curveRing.mp q.2 c'' hc''
  have := (chartRingZ y c'').mul_mem h3 h2
  convert this using 1
  push_cast
  ring

/- English proof (translation)
Establish `hg` using `gen_ne_zero hc hc' a`. Use `⟨?_, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hloc : ∀ c'' : ∀ k, ι k, (∀ k, y ⟨k, c'' k⟩ ≠ 0) → ∃ b : curveRing y, b ∉ m ∧ (b : Ω) * (cu y c' a / cu y c'' a) ∈ chartRingZ y c''`. Introduce `c'' hc''`. Establish `hS : ∀ b : curveRing y, (b : Ω) ∈ (chartRingZ y c'').toSubring` using `fun b => mem_curveRing.mp b.2 c'' hc''`.

Set `T` to `locRing m hm (chartRingZ y c'').toSubring hS`. Establish `hT : cu y c' a / cu y c'' a ∈ T`. Rewrite using `[cu_div]`. Use `prod_mem fun k _ => zpow_mem_of ?_ ?_ _` and prove the remaining obligations. Use `⟨1, fun h => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h), ?_⟩` and prove the remaining obligations.

Rewrite using `[OneMemClass.coe_one, one_mul]`. Conclude with `Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩`. Take `⟨α, β, hβ, e⟩` from `hr ⟨k, c'' k⟩`. Use `⟨β, hβ, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_div, e]`.

Conclude with `hS α`. Conclude with `hT`. Take `⟨b, hb, hb'⟩` from `uniform_denom hm _ hloc`. Use `⟨b, hb, (mem_secIdeal hc).mpr fun c'' hc'' => ?_⟩` and prove the remaining obligations. Establish `hu''` using `cu_ne_zero hc'' a`.

Establish `hu` using `cu_ne_zero hc a`. Use `hb' c'' hc'' using 1` and compare the differences between its conclusion and the goal. Simplify using `only [gen]`. Clear the denominators using the available nonvanishing facts. Establish `h1` using `(mem_secIdeal hc).mp hz c' hc'`.

Take `⟨b, hb, hb'⟩` from `chartRingZ_le_loc hm hr h1`. Use `⟨b, ⟨_, hb'⟩, hb, ?_⟩` and prove the remaining obligations. Simplify using `only`. Clear the denominators using the available nonvanishing facts.
-/
theorem local_gen {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {m : Ideal (curveRing y)}
    (hm : m.IsPrime) {c' : ∀ k, ι k} (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0)
    (hr : ∀ p : Σ k, ι k, ∃ α β : curveRing y, β ∉ m ∧ (β : Ω) * (y p / y ⟨p.1, c' p.1⟩) = α) (a : K → ℤ) :
    (∃ b : curveRing y, b ∉ m ∧ (b : Ω) * gen y c a c' ∈ secIdeal y c a) ∧
      ∀ z ∈ secIdeal y c a, ∃ b e : curveRing y, b ∉ m ∧ (b : Ω) * z = e * gen y c a c' := by
  have hg := gen_ne_zero hc hc' a
  refine ⟨?_, fun z hz => ?_⟩
  · have hloc : ∀ c'' : ∀ k, ι k, (∀ k, y ⟨k, c'' k⟩ ≠ 0) →
        ∃ b : curveRing y, b ∉ m ∧ (b : Ω) * (cu y c' a / cu y c'' a) ∈ chartRingZ y c'' := by
      intro c'' hc''
      have hS : ∀ b : curveRing y, (b : Ω) ∈ (chartRingZ y c'').toSubring := fun b => mem_curveRing.mp b.2 c'' hc''
      let T := locRing m hm (chartRingZ y c'').toSubring hS
      have hT : cu y c' a / cu y c'' a ∈ T := by
        rw [cu_div]
        refine prod_mem fun k _ => zpow_mem_of ?_ ?_ _
        · refine ⟨1, fun h => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h), ?_⟩
          rw [OneMemClass.coe_one, one_mul]
          exact Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩
        · obtain ⟨α, β, hβ, e⟩ := hr ⟨k, c'' k⟩
          refine ⟨β, hβ, ?_⟩
          rw [inv_div, e]
          exact hS α
      exact hT
    obtain ⟨b, hb, hb'⟩ := uniform_denom hm _ hloc
    refine ⟨b, hb, (mem_secIdeal hc).mpr fun c'' hc'' => ?_⟩
    have hu'' := cu_ne_zero hc'' a
    have hu := cu_ne_zero hc a
    convert hb' c'' hc'' using 1
    simp only [gen]
    field_simp
  · have h1 := (mem_secIdeal hc).mp hz c' hc'
    obtain ⟨b, hb, hb'⟩ := chartRingZ_le_loc hm hr h1
    refine ⟨b, ⟨_, hb'⟩, hb, ?_⟩
    simp only
    field_simp

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use `set S := Subfield.closure (curveRing y : Set Ω) with hSdef`. Establish `hB : ∀ b ∈ curveRing y, b ∈ S` using `fun b hb => Subfield.subset_closure hb`. Establish `hrat : ∀ p : Σ k, ι k, y p / y ⟨p.1, c0 p.1⟩ ∈ S`. Introduce `p`. Take `⟨α, β, hβ, e⟩` from `hr p`.

Establish `hβ0 : (β : Ω) ≠ 0` using `fun h0 => hβ (by`. Establish `: β = 0` using `Subtype.ext h0`. Rewrite using `[this]`. Conclude with `m.zero_mem)`. Establish `: y p / y ⟨p.1, c0 p.1⟩ = α / β` using `by rw [← e]; field_simp`.

Rewrite using `[this]`. Conclude with `S.div_mem (hB _ α.2) (hB _ β.2)`. Establish `hx : gen y c a c' ∈ S`. Rewrite using `[gen, cu_div]`. Use `prod_mem fun k _ => S.zpow_mem ?_ _` and prove the remaining obligations.

Establish `e : y ⟨k, c' k⟩ / y ⟨k, c k⟩ = (y ⟨k, c' k⟩ / y ⟨k, c0 k⟩) / (y ⟨k, c k⟩ / y ⟨k, c0 k⟩)` using `(div_div_div_cancel_right₀ (hc0 k) _ _).symm`. Rewrite using `[e]`. Conclude with `S.div_mem (hrat ⟨k, c' k⟩) (hrat ⟨k, c k⟩)`. Take `⟨u, hu, v, hv, huv⟩` from `Subfield.mem_closure_iff.mp hx`. Rewrite `hu`, `hv` using `[Subring.closure_eq]`.

Establish `hv0 : v ≠ 0`. Introduce and unpack `rfl`. Rewrite `huv` using `[div_zero]`. Conclude with `gen_ne_zero hc hc' a huv.symm`. Use `⟨v, hv, hv0, ?_⟩` and prove the remaining obligations.

Rewrite using `[← huv, mul_div_cancel₀ _ hv0]`. Conclude with `hu`.
-/
theorem gen_frac {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {m : Ideal (curveRing y)}
    {c0 : ∀ k, ι k} (hc0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0)
    (hr : ∀ p : Σ k, ι k, ∃ α β : curveRing y, β ∉ m ∧ (β : Ω) * (y p / y ⟨p.1, c0 p.1⟩) = α)
    (c' : ∀ k, ι k) (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) (a : K → ℤ) :
    ∃ d ∈ curveRing y, d ≠ 0 ∧ d * gen y c a c' ∈ curveRing y := by
  set S := Subfield.closure (curveRing y : Set Ω) with hSdef
  have hB : ∀ b ∈ curveRing y, b ∈ S := fun b hb => Subfield.subset_closure hb
  have hrat : ∀ p : Σ k, ι k, y p / y ⟨p.1, c0 p.1⟩ ∈ S := by
    intro p
    obtain ⟨α, β, hβ, e⟩ := hr p
    have hβ0 : (β : Ω) ≠ 0 := fun h0 => hβ (by
      have : β = 0 := Subtype.ext h0
      rw [this]; exact m.zero_mem)
    have : y p / y ⟨p.1, c0 p.1⟩ = α / β := by rw [← e]; field_simp
    rw [this]
    exact S.div_mem (hB _ α.2) (hB _ β.2)
  have hx : gen y c a c' ∈ S := by
    rw [gen, cu_div]
    refine prod_mem fun k _ => S.zpow_mem ?_ _
    have e : y ⟨k, c' k⟩ / y ⟨k, c k⟩ =
        (y ⟨k, c' k⟩ / y ⟨k, c0 k⟩) / (y ⟨k, c k⟩ / y ⟨k, c0 k⟩) :=
      (div_div_div_cancel_right₀ (hc0 k) _ _).symm
    rw [e]
    exact S.div_mem (hrat ⟨k, c' k⟩) (hrat ⟨k, c k⟩)
  obtain ⟨u, hu, v, hv, huv⟩ := Subfield.mem_closure_iff.mp hx
  rw [Subring.closure_eq] at hu hv
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [div_zero] at huv
    exact gen_ne_zero hc hc' a huv.symm
  refine ⟨v, hv, hv0, ?_⟩
  rw [← huv, mul_div_cancel₀ _ hv0]
  exact hu

end CurveIndexLinearAlt

open CurveIndexLinearAlt in

/- English proof (translation)
Rewrite using `[chartIndexLog_eq hc, chartIndexLog_eq hc, chartIndexLog_eq hc]`. Take `⟨m0, hm0⟩` from `Ideal.exists_maximal (curveRing y)`. Take `⟨c0, hc0, hr0⟩` from `hC K ι Ω y hP m0 hm0`. Establish `hfrac : ∀ (b : K → ℤ) (i : {c' : ∀ k, ι k // ∀ k, y ⟨k, c' k⟩ ≠ 0}), ∃ d ∈ curveRing y, d ≠ 0 ∧ d * gen y c b i.1 ∈ curveRing y` using `fun b i => gen_frac hc hc0 hr0 i.1 i.2 b`. Take `⟨h1, h2, h3⟩` from `hI Ω (curveRing y) (secIdeal y c a) (secIdeal y c a') (secIdeal y c (a + a')) {c' : ∀ k, ι k // ∀ k, y ⟨k, c' k⟩ ≠ 0} (fun i => gen y c a i.1) (fun i => gen y c a' i.1) (hF K ι Ω y hP) (mul_mem_secIdeal hc) (mul_mem_secIdeal hc) (mul_mem_secIdeal hc) (fun i => gen_ne_zero hc i.2 …`.

Take `⟨c', hc', hr⟩` from `hC K ι Ω y hP m hm`. Use `⟨⟨c', hc'⟩, local_gen hc hm.isPrime hc' hr a, local_gen hc hm.isPrime hc' hr a', ?_⟩` and prove the remaining obligations. Simplify using `only [← gen_add hc hc']`. Conclude with `local_gen hc hm.isPrime hc' hr (a + a'))`. Rewrite using `[h3, Real.log_mul h1.ne' h2.ne']`.
-/
theorem CurveIndexLinear.add (hF : CurveRingFinite.Statement) (hC : CurveClosedPointChart.Statement)
    (hI : InvertibleIndexMul.Statement) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hP : IsArithVar (mCoordIdeal y) 1)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a a' : K → ℤ) :
    chartIndexLog y c (a + a') 1 = chartIndexLog y c a 1 + chartIndexLog y c a' 1 := by
  classical
  rw [chartIndexLog_eq hc, chartIndexLog_eq hc, chartIndexLog_eq hc]
  obtain ⟨m0, hm0⟩ := Ideal.exists_maximal (curveRing y)
  obtain ⟨c0, hc0, hr0⟩ := hC K ι Ω y hP m0 hm0
  have hfrac : ∀ (b : K → ℤ) (i : {c' : ∀ k, ι k // ∀ k, y ⟨k, c' k⟩ ≠ 0}),
      ∃ d ∈ curveRing y, d ≠ 0 ∧ d * gen y c b i.1 ∈ curveRing y :=
    fun b i => gen_frac hc hc0 hr0 i.1 i.2 b
  obtain ⟨h1, h2, h3⟩ := hI Ω (curveRing y) (secIdeal y c a) (secIdeal y c a') (secIdeal y c (a + a'))
    {c' : ∀ k, ι k // ∀ k, y ⟨k, c' k⟩ ≠ 0} (fun i => gen y c a i.1) (fun i => gen y c a' i.1)
    (hF K ι Ω y hP) (mul_mem_secIdeal hc) (mul_mem_secIdeal hc) (mul_mem_secIdeal hc)
    (fun i => gen_ne_zero hc i.2 a) (fun i => gen_ne_zero hc i.2 a') (hfrac a) (hfrac a') (fun m hm => by
      obtain ⟨c', hc', hr⟩ := hC K ι Ω y hP m hm
      refine ⟨⟨c', hc'⟩, local_gen hc hm.isPrime hc' hr a, local_gen hc hm.isPrime hc' hr a', ?_⟩
      simp only [← gen_add hc hc']
      exact local_gen hc hm.isPrime hc' hr (a + a'))
  rw [h3, Real.log_mul h1.ne' h2.ne']

/- English proof (translation)
Introduce `K _ ι _ Ω _ y c hP hc`. Establish `hadd` using `CurveIndexLinear.add hF hC hI hP hc`. Use `⟨hadd, fun a τ => ?_⟩` and prove the remaining obligations. Establish `hτ : chartIndexLog y c a τ = chartIndexLog y c (fun k => (τ : ℤ) * a k) 1`. Establish `e1 : chartLat y a τ = chartLat y (fun k => (τ : ℤ) * a k) 1`.

Use extensionality with `s`. Use `show (∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) → s * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k)) ∈ chartRingZ y c') ↔ (∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) → s * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * ((τ : ℤ) * a k))) ∈ chartRingZ y c')`. Simplify using `only [Nat.cast_one, one_mul]`. Establish `e2 : chartUnit y c a τ = chartUnit y c (fun k => (τ : ℤ) * a k) 1`. Simplify using `[chartUnit]`.

Rewrite using `[chartIndexLog, chartIndexLog, e1, e2]`. Rewrite using `[hτ]`. Use `clear hτ`. Proceed by induction on `τ with`. Consider the case `zero`.

Establish `h0` using `hadd 0 0`. Rewrite `h0` using `[add_zero]`. Establish `e : (fun k => ((0 : ℕ) : ℤ) * a k) = 0` using `funext fun k => by simp`. Rewrite using `[e]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ n ih`. Establish `e : (fun k => ((n + 1 : ℕ) : ℤ) * a k) = (fun k => (n : ℤ) * a k) + a`. Use function extensionality and compare the values at `fun k => by simp only [Pi.add_apply]; push_cast; ring`. Rewrite using `[e, hadd, ih]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem CurveIndexLinear.proof (hF : CurveRingFinite.Statement) (hC : CurveClosedPointChart.Statement)
    (hI : InvertibleIndexMul.Statement) : CurveIndexLinear.Statement := by
  intro K _ ι _ Ω _ y c hP hc
  have hadd := CurveIndexLinear.add hF hC hI hP hc
  refine ⟨hadd, fun a τ => ?_⟩
  have hτ : chartIndexLog y c a τ = chartIndexLog y c (fun k => (τ : ℤ) * a k) 1 := by
    have e1 : chartLat y a τ = chartLat y (fun k => (τ : ℤ) * a k) 1 := by
      ext s
      show (∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
          s * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k)) ∈ chartRingZ y c') ↔
        (∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
          s * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * ((τ : ℤ) * a k))) ∈ chartRingZ y c')
      simp only [Nat.cast_one, one_mul]
    have e2 : chartUnit y c a τ = chartUnit y c (fun k => (τ : ℤ) * a k) 1 := by
      simp [chartUnit]
    rw [chartIndexLog, chartIndexLog, e1, e2]
  rw [hτ]
  clear hτ
  induction τ with
  | zero =>
    have h0 := hadd 0 0
    rw [add_zero] at h0
    have e : (fun k => ((0 : ℕ) : ℤ) * a k) = 0 := funext fun k => by simp
    rw [e]
    push_cast
    linarith
  | succ n ih =>
    have e : (fun k => ((n + 1 : ℕ) : ℤ) * a k) = (fun k => (n : ℤ) * a k) + a :=
      funext fun k => by simp only [Pi.add_apply]; push_cast; ring
    rw [e, hadd, ih]
    push_cast
    ring

end

end GroundTheory.Heights₂.Heights.Targets
