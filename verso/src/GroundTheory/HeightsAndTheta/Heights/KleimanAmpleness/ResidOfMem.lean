import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestLast
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.EqZeroOrIsHomogeneousOfMemPolyPiece
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

noncomputable section

section RestrictGenAux

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {K' : Type} [Field K'] [Algebra F K']
  (R : Subalgebra F Ω) (σ : R →ₐ[F] K')

open Classical in

def RestrictGen.resid (a : Ω) : K' := if h : a ∈ R then σ ⟨a, h⟩ else 0

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem RestrictGen.resid_of_mem {a : Ω} (h : a ∈ R) : RestrictGen.resid R σ a = σ ⟨a, h⟩ := dif_pos h

/- English proof (translation)
Rewrite using `[RestrictGen.resid_of_mem R σ (zero_mem R)]`. Conclude with `map_zero σ`.
-/
theorem RestrictGen.resid_zero : RestrictGen.resid R σ 0 = 0 := by
  rw [RestrictGen.resid_of_mem R σ (zero_mem R)]
  exact map_zero σ

/- English proof (translation)
Rewrite using `[RestrictGen.resid_of_mem R σ ha, RestrictGen.resid_of_mem R σ hb, RestrictGen.resid_of_mem R σ (add_mem ha hb), ← map_add]`. Both sides reduce to the same expression.
-/
theorem RestrictGen.resid_add {a b : Ω} (ha : a ∈ R) (hb : b ∈ R) :
    RestrictGen.resid R σ (a + b) = RestrictGen.resid R σ a + RestrictGen.resid R σ b := by
  rw [RestrictGen.resid_of_mem R σ ha, RestrictGen.resid_of_mem R σ hb,
    RestrictGen.resid_of_mem R σ (add_mem ha hb), ← map_add]
  rfl

/- English proof (translation)
Rewrite using `[RestrictGen.resid_of_mem R σ ha, RestrictGen.resid_of_mem R σ hb, RestrictGen.resid_of_mem R σ (mul_mem ha hb), ← map_mul]`. Both sides reduce to the same expression.
-/
theorem RestrictGen.resid_mul {a b : Ω} (ha : a ∈ R) (hb : b ∈ R) :
    RestrictGen.resid R σ (a * b) = RestrictGen.resid R σ a * RestrictGen.resid R σ b := by
  rw [RestrictGen.resid_of_mem R σ ha, RestrictGen.resid_of_mem R σ hb,
    RestrictGen.resid_of_mem R σ (mul_mem ha hb), ← map_mul]
  rfl

end RestrictGenAux

open RestrictGen in

/- English proof (translation)
Introduce `F _ N Ω _ _ x K' _ _ x' hxy R σ hσ Q Q' c H ρ w w' hw' hQ hQ' hH`. Establish `hσ' : ∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m → aeval x' g ≠ 0 → aeval x f / aeval x g ∈ R ∧ resid R σ (aeval x f / aeval x g) = aeval x' f / aeval x' g`. Introduce `f g m hf hg hg'`. Take `⟨h, e⟩` from `hσ f g m hf hg hg'`. Conclude with `⟨h, by rw [resid_of_mem R σ h, e]⟩`.

Distinguish the cases in `hx' : ∃ j, x' j ≠ 0`. Use `swap`. Simplify using `only [not_exists, not_not] at hx'`. Establish `hI : IsEmpty (Kleiman.Chart x')` using `⟨fun I => by`. Take `⟨i, hi⟩` from `I.2.1`.

Conclude with `(Kleiman.mem_support x').mp (I.2.2 hi) (hx' i)⟩`. Conclude with `⟨0, ⟨fun I => hI.elim I, fun I => hI.elim I, fun I => hI.elim I, fun I => hI.elim I⟩⟩`. Take `⟨j, hj⟩` from `hx'`. Establish `hxj : x j ≠ 0` using `hxy j hj`. Use `set r : Ω → K' := fun q => resid R σ (q * x j ^ c * w) / (x' j ^ c * w') with hr`.

Establish `hrat : ∀ i, x' i ≠ 0 → (x j / x i) ^ c ∈ R ∧ resid R σ ((x j / x i) ^ c) = (x' j / x' i) ^ c`. Introduce `i hi`. Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg c`. Use `hσ' (X j ^ n) (X i ^ n) n (isHomogeneous_X_pow (R := F) j n) (isHomogeneous_X_pow (R := F) i n) (by simpa using pow_ne_zero n hi)` as an intermediate fact. Simplify using `only [map_pow, aeval_X] at this`.

Simplify `this` using `[zpow_natCast, div_pow]`. Use `hσ' (X i ^ n) (X j ^ n) n (isHomogeneous_X_pow (R := F) i n) (isHomogeneous_X_pow (R := F) j n) (by simpa using pow_ne_zero n hj)` as an intermediate fact. Simplify using `only [map_pow, aeval_X] at this`. Simplify `this` using `[zpow_neg, zpow_natCast, div_pow, inv_div]`. Establish `hchart : ∀ (I : Kleiman.Chart x') (a : Ω), a ∈ Kleiman.chartRing F x (Kleiman.liftChart hxy I) → a ∈ R ∧ resid R σ a ∈ Kleiman.chartRing F x' I`.

Introduce and unpack `I a ⟨f, s, e, hs, hf, hse, rfl⟩`. Take `⟨h1, h2⟩` from `hσ' f s e hf hse (Kleiman.eval_ne_zero_of_mem_monos I hs)`. Conclude with `⟨h1, h2 ▸ ⟨f, s, e, hs, hf, hse, rfl⟩⟩`. Establish `hspan : ∀ (I : Kleiman.Chart x') (z : Ω), z ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.liftChart hxy I)) H → z * w ∈ R ∧ resid R σ (z * w) / w' ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H)`. Introduce `I z hz`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem h hh`. Take `⟨hm, e⟩` from `hH h hh`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Rewrite using `[resid_of_mem R σ hm, e, mul_div_cancel_right₀ _ hw']`.

Conclude with `Submodule.subset_span ⟨h, hh, rfl⟩`. Consider the case `zero`. Rewrite using `[zero_mul, resid_zero, zero_div]`. Conclude with `⟨zero_mem R, zero_mem _⟩`. Consider the case `add a b _ _ ha hb`.

Use `⟨by rw [add_mul]; exact add_mem ha.1 hb.1, ?_⟩` and prove the remaining obligations. Rewrite using `[add_mul, resid_add R σ ha.1 hb.1, add_div]`. Conclude with `add_mem ha.2 hb.2`. Consider the case `smul a z _ hz`. Take `⟨ha1, ha2⟩` from `hchart I a a.2`.

Rewrite using `[Kleiman.chartRing_smul_def, mul_assoc]`. Use `⟨mul_mem ha1 hz.1, ?_⟩` and prove the remaining obligations. Rewrite using `[resid_mul R σ ha1 hz.1, mul_div_assoc]`. Conclude with `Submodule.smul_mem _ (⟨_, ha2⟩ : Kleiman.chartRing F x' I) hz.2`. Establish `hkey : ∀ (I : Kleiman.Chart x') (i : Fin (N + 1)), i ∈ I.1 → ∀ q ∈ Q.sub (Kleiman.liftChart hxy I), q * x j ^ c * w ∈ R ∧ r q * x' i ^ c = resid R σ (x i ^ c * q * w) / w' ∧ resid R σ (x i ^ c * q * w) / w' ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H)`.

Introduce `I i hi q hq`. Establish `hx'i : x' i ≠ 0` using `(Kleiman.mem_support x').mp (I.2.2 hi)`. Establish `hxi : x i ≠ 0` using `hxy i hx'i`. Establish `hz : x i ^ c * q ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.liftChart hxy I)) H`. Rewrite using `[← hQ (Kleiman.liftChart hxy I)]`.

Conclude with `(TranslateEq.mem_twist_twistSys_iff Q.toSubSystem c (Kleiman.liftChart hxy I) hi _).mpr ⟨q, hq, rfl⟩`. Take `⟨hz1, hz2⟩` from `hspan I _ hz`. Take `⟨hr1, hr2⟩` from `hrat i hx'i`. Establish `heq : q * x j ^ c * w = (x j / x i) ^ c * (x i ^ c * q * w)`. Rewrite using `[div_zpow]`.

Clear the denominators using the available nonvanishing facts. Use `⟨heq ▸ mul_mem hr1 hz1, ?_, hz2⟩` and prove the remaining obligations. Rewrite using `[hr]`. Simplify using `only`. Rewrite using `[heq, resid_mul R σ hr1 hz1, hr2, div_zpow]`.

Clear the denominators using the available nonvanishing facts. Establish `hmem : ∀ (I : Kleiman.Chart x'), ∀ q ∈ Q.sub (Kleiman.liftChart hxy I), r q ∈ Q'.sub I`. Introduce `I q hq`. Take `⟨i, hi⟩` from `I.2.1`. Take `⟨-, e, hm⟩` from `hkey I i hi q hq`.

Establish `hx'i : x' i ≠ 0` using `(Kleiman.mem_support x').mp (I.2.2 hi)`. Rewrite `hm` using `[← hQ' I]`. Take `⟨y, hy, hy'⟩` from `(TranslateEq.mem_twist_twistSys_iff Q'.toSubSystem c I hi _).mp hm`. Establish `h' : r q * x' i ^ c = y * x' i ^ c`. Rewrite using `[e, hy', smul_eq_mul, mul_comm]`.

Rewrite using `[mul_right_cancel₀ (zpow_ne_zero c hx'i) h']`. Conclude with `hy`. Use `⟨r, ⟨hmem, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `I q hq q' hq'`. Take `⟨i, hi⟩` from `I.2.1`.

Establish `h1` using `(hkey I i hi q hq).1`. Establish `h2` using `(hkey I i hi q' hq').1`. Rewrite using `[hr]`. Simplify using `only`. Rewrite using `[add_mul, add_mul, resid_add R σ h1 h2, add_div]`.

Introduce `I q hq f s e hs hf hse`. Take `⟨i, hi⟩` from `I.2.1`. Establish `h1` using `(hkey I i hi q hq).1`. Take `⟨ha1, ha2⟩` from `hσ' f s e hf hse (Kleiman.eval_ne_zero_of_mem_monos I hs)`. Establish `hm : aeval x f / aeval x s * q * x j ^ c * w = aeval x f / aeval x s * (q * x j ^ c * w)` using `by ring`.

Rewrite using `[hr]`. Simplify using `only`. Rewrite using `[hm, resid_mul R σ ha1 h1, ha2, mul_div_assoc]`. Introduce `I`. Take `⟨i, hi⟩` from `I.2.1`.

Establish `hx'i : x' i ≠ 0` using `(Kleiman.mem_support x').mp (I.2.2 hi)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨q, hq, rfl⟩`. Conclude with `hmem I q hq`.

Introduce `t ht`. Establish `ht' : x' i ^ c * t ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H)`. Rewrite using `[← hQ' I]`. Conclude with `(TranslateEq.mem_twist_twistSys_iff Q'.toSubSystem c I hi _).mpr ⟨t, ht, rfl⟩`. Establish `hall : ∀ u ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H), x' i ^ (-c) * u ∈ Submodule.span (Kleiman.chartRing F x' I) (r '' Q.sub (Kleiman.liftChart hxy I))`.

Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu`. Take `⟨h, hh, rfl⟩` from `hu`. Establish `hh' : h ∈ (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub (Kleiman.liftChart hxy I)`.

Rewrite using `[hQ]`. Conclude with `Submodule.subset_span hh`. Take `⟨y, hy, rfl⟩` from `(TranslateEq.mem_twist_twistSys_iff Q.toSubSystem c (Kleiman.liftChart hxy I) hi _).mp hh'`. Take `⟨hm, e⟩` from `hH _ hh`. Take `⟨-, e', -⟩` from `hkey I i hi y hy`.

Establish `e'' : resid R σ (x i ^ c * y * w) = ρ (x i ^ c • y) * w'` using `(resid_of_mem R σ hm).trans e`. Rewrite `e'` using `[e'', mul_div_cancel_right₀ _ hw']`. Establish `: x' i ^ (-c) * ρ (x i ^ c • y) = r y`. Rewrite using `[← e', zpow_neg]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [mul_add]`.

Conclude with `add_mem ha hb`. Consider the case `smul a u _ hu`. Rewrite using `[Kleiman.chartRing_smul_def, mul_left_comm]`. Conclude with `Submodule.smul_mem _ a hu`. Use `hall _ ht'` as an intermediate fact.

Rewrite `this` using `[← mul_assoc, ← zpow_add₀ hx'i, neg_add_cancel, zpow_zero, one_mul]`. Then use the resulting hypothesis.
-/
theorem RestrictGen.proof : RestrictGen.Statement := by
  intro F _ N Ω _ _ x K' _ _ x' hxy R σ hσ Q Q' c H ρ w w' hw' hQ hQ' hH
  classical
  have hσ' : ∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m → aeval x' g ≠ 0 →
      aeval x f / aeval x g ∈ R ∧ resid R σ (aeval x f / aeval x g) = aeval x' f / aeval x' g := by
    intro f g m hf hg hg'
    obtain ⟨h, e⟩ := hσ f g m hf hg hg'
    exact ⟨h, by rw [resid_of_mem R σ h, e]⟩
  by_cases hx' : ∃ j, x' j ≠ 0
  swap
  · simp only [not_exists, not_not] at hx'
    have hI : IsEmpty (Kleiman.Chart x') := ⟨fun I => by
      obtain ⟨i, hi⟩ := I.2.1
      exact (Kleiman.mem_support x').mp (I.2.2 hi) (hx' i)⟩
    exact ⟨0, ⟨fun I => hI.elim I, fun I => hI.elim I, fun I => hI.elim I, fun I => hI.elim I⟩⟩
  obtain ⟨j, hj⟩ := hx'
  have hxj : x j ≠ 0 := hxy j hj
  set r : Ω → K' := fun q => resid R σ (q * x j ^ c * w) / (x' j ^ c * w') with hr

  have hrat : ∀ i, x' i ≠ 0 → (x j / x i) ^ c ∈ R ∧ resid R σ ((x j / x i) ^ c) = (x' j / x' i) ^ c := by
    intro i hi
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · have := hσ' (X j ^ n) (X i ^ n) n (isHomogeneous_X_pow (R := F) j n) (isHomogeneous_X_pow (R := F) i n)
        (by simpa using pow_ne_zero n hi)
      simp only [map_pow, aeval_X] at this
      simpa [zpow_natCast, div_pow] using this
    · have := hσ' (X i ^ n) (X j ^ n) n (isHomogeneous_X_pow (R := F) i n) (isHomogeneous_X_pow (R := F) j n)
        (by simpa using pow_ne_zero n hj)
      simp only [map_pow, aeval_X] at this
      simpa [zpow_neg, zpow_natCast, div_pow, inv_div] using this

  have hchart : ∀ (I : Kleiman.Chart x') (a : Ω), a ∈ Kleiman.chartRing F x (Kleiman.liftChart hxy I) →
      a ∈ R ∧ resid R σ a ∈ Kleiman.chartRing F x' I := by
    rintro I a ⟨f, s, e, hs, hf, hse, rfl⟩
    obtain ⟨h1, h2⟩ := hσ' f s e hf hse (Kleiman.eval_ne_zero_of_mem_monos I hs)
    exact ⟨h1, h2 ▸ ⟨f, s, e, hs, hf, hse, rfl⟩⟩

  have hspan : ∀ (I : Kleiman.Chart x') (z : Ω),
      z ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.liftChart hxy I)) H →
      z * w ∈ R ∧ resid R σ (z * w) / w' ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
    intro I z hz
    induction hz using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨hm, e⟩ := hH h hh
      refine ⟨hm, ?_⟩
      rw [resid_of_mem R σ hm, e, mul_div_cancel_right₀ _ hw']
      exact Submodule.subset_span ⟨h, hh, rfl⟩
    | zero =>
      rw [zero_mul, resid_zero, zero_div]
      exact ⟨zero_mem R, zero_mem _⟩
    | add a b _ _ ha hb =>
      refine ⟨by rw [add_mul]; exact add_mem ha.1 hb.1, ?_⟩
      rw [add_mul, resid_add R σ ha.1 hb.1, add_div]
      exact add_mem ha.2 hb.2
    | smul a z _ hz =>
      obtain ⟨ha1, ha2⟩ := hchart I a a.2
      rw [Kleiman.chartRing_smul_def, mul_assoc]
      refine ⟨mul_mem ha1 hz.1, ?_⟩
      rw [resid_mul R σ ha1 hz.1, mul_div_assoc]
      exact Submodule.smul_mem _ (⟨_, ha2⟩ : Kleiman.chartRing F x' I) hz.2

  have hkey : ∀ (I : Kleiman.Chart x') (i : Fin (N + 1)), i ∈ I.1 → ∀ q ∈ Q.sub (Kleiman.liftChart hxy I),
      q * x j ^ c * w ∈ R ∧ r q * x' i ^ c = resid R σ (x i ^ c * q * w) / w' ∧
      resid R σ (x i ^ c * q * w) / w' ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
    intro I i hi q hq
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    have hxi : x i ≠ 0 := hxy i hx'i
    have hz : x i ^ c * q ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.liftChart hxy I)) H := by
      rw [← hQ (Kleiman.liftChart hxy I)]
      exact (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem c (Kleiman.liftChart hxy I) hi _).mpr ⟨q, hq, rfl⟩
    obtain ⟨hz1, hz2⟩ := hspan I _ hz
    obtain ⟨hr1, hr2⟩ := hrat i hx'i
    have heq : q * x j ^ c * w = (x j / x i) ^ c * (x i ^ c * q * w) := by
      rw [div_zpow]
      field_simp
    refine ⟨heq ▸ mul_mem hr1 hz1, ?_, hz2⟩
    rw [hr]
    dsimp only
    rw [heq, resid_mul R σ hr1 hz1, hr2, div_zpow]
    field_simp
  have hmem : ∀ (I : Kleiman.Chart x'), ∀ q ∈ Q.sub (Kleiman.liftChart hxy I), r q ∈ Q'.sub I := by
    intro I q hq
    obtain ⟨i, hi⟩ := I.2.1
    obtain ⟨-, e, hm⟩ := hkey I i hi q hq
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    rw [← hQ' I] at hm
    obtain ⟨y, hy, hy'⟩ := (TranslateEq.mem_twist_twistSys_iff Q'.toSubSystem c I hi _).mp hm
    have h' : r q * x' i ^ c = y * x' i ^ c := by
      rw [e, hy', smul_eq_mul, mul_comm]
    rw [mul_right_cancel₀ (zpow_ne_zero c hx'i) h']
    exact hy
  refine ⟨r, ⟨hmem, ?_, ?_, ?_⟩⟩
  · intro I q hq q' hq'
    obtain ⟨i, hi⟩ := I.2.1
    have h1 := (hkey I i hi q hq).1
    have h2 := (hkey I i hi q' hq').1
    rw [hr]
    dsimp only
    rw [add_mul, add_mul, resid_add R σ h1 h2, add_div]
  · intro I q hq f s e hs hf hse
    obtain ⟨i, hi⟩ := I.2.1
    have h1 := (hkey I i hi q hq).1
    obtain ⟨ha1, ha2⟩ := hσ' f s e hf hse (Kleiman.eval_ne_zero_of_mem_monos I hs)
    have hm : aeval x f / aeval x s * q * x j ^ c * w = aeval x f / aeval x s * (q * x j ^ c * w) := by ring
    rw [hr]
    dsimp only
    rw [hm, resid_mul R σ ha1 h1, ha2, mul_div_assoc]
  · intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨q, hq, rfl⟩
      exact hmem I q hq
    · intro t ht
      have ht' : x' i ^ c * t ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
        rw [← hQ' I]
        exact (TranslateEq.mem_twist_twistSys_iff Q'.toSubSystem c I hi _).mpr ⟨t, ht, rfl⟩
      have hall : ∀ u ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H),
          x' i ^ (-c) * u ∈ Submodule.span (Kleiman.chartRing F x' I) (r '' Q.sub (Kleiman.liftChart hxy I)) := by
        intro u hu
        induction hu using Submodule.span_induction with
        | mem u hu =>
          obtain ⟨h, hh, rfl⟩ := hu
          have hh' : h ∈ (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub (Kleiman.liftChart hxy I) := by
            rw [hQ]
            exact Submodule.subset_span hh
          obtain ⟨y, hy, rfl⟩ :=
            (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem c (Kleiman.liftChart hxy I) hi _).mp hh'
          obtain ⟨hm, e⟩ := hH _ hh
          obtain ⟨-, e', -⟩ := hkey I i hi y hy
          have e'' : resid R σ (x i ^ c * y * w) = ρ (x i ^ c • y) * w' := (resid_of_mem R σ hm).trans e
          rw [e'', mul_div_cancel_right₀ _ hw'] at e'
          have : x' i ^ (-c) * ρ (x i ^ c • y) = r y := by
            rw [← e', zpow_neg]
            field_simp
          rw [this]
          exact Submodule.subset_span ⟨y, hy, rfl⟩
        | zero => rw [mul_zero]; exact zero_mem _
        | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
        | smul a u _ hu =>
          rw [Kleiman.chartRing_smul_def, mul_left_comm]
          exact Submodule.smul_mem _ a hu
      have := hall _ ht'
      rwa [← mul_assoc, ← zpow_add₀ hx'i, neg_add_cancel, zpow_zero, one_mul] at this

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
