import Mathlib
import Formalism.TameInertiaTowers.StatementField

open NumberField

noncomputable section

namespace Formalism.TwoAdicCyclotomicDecomposition

namespace UnitConjugation

/- English proof (translation)
Establish `h1 : ‖z‖ = 1` using `Complex.norm_eq_one_of_pow_eq_one hz hm`. Rewrite using `[Complex.inv_def, Complex.normSq_eq_norm_sq, h1]`. Simplify using the standard rewrite rules.
-/
lemma conj_eq_inv_of_pow_eq_one {z : ℂ} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) :
    starRingEnd ℂ z = z⁻¹ := by
  have h1 : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hm
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]
  simp

/- English proof (translation)
Establish `hζ0 : ζ ≠ 0` using `hζ.ne_zero (NeZero.ne m)`. Establish `e : ζ ^ k = ζ⁻¹ ↔ ζ ^ k * ζ = 1` using `⟨fun h => by rw [h, inv_mul_cancel₀ hζ0], fun h => eq_inv_of_mul_eq_one_left h⟩`. Rewrite using `[e, ← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]`. Use `push_cast`. Conclude with `add_eq_zero_iff_eq_neg`.
-/
lemma pow_eq_inv_iff {K : Type*} [Field K] {m : ℕ} [NeZero m] {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (k : ℕ) : ζ ^ k = ζ⁻¹ ↔ (k : ZMod m) = -1 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne m)
  have e : ζ ^ k = ζ⁻¹ ↔ ζ ^ k * ζ = 1 :=
    ⟨fun h => by rw [h, inv_mul_cancel₀ hζ0], fun h => eq_inv_of_mul_eq_one_left h⟩
  rw [e, ← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
  push_cast
  exact add_eq_zero_iff_eq_neg

variable {n q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

/- English proof (translation)
Introduce `h0`. Rewrite `ha` using `[h0, zero_pow two_ne_zero, zero_eq_neg]`. Conclude with `hq.ne' (by exact_mod_cast ha)`.
-/
lemma ne_zero_of_sq (hq : 0 < q) (ha : a ^ 2 = -(q : L)) : a ≠ 0 := by
  intro h0
  rw [h0, zero_pow two_ne_zero, zero_eq_neg] at ha
  exact hq.ne' (by exact_mod_cast ha)

/- English proof (translation)
Use `set z := φ a with hzdef`. Establish `hz : z ^ 2 = -(q : ℂ)`. Rewrite using `[hzdef, ← map_pow, ha, map_neg, map_natCast]`. Establish `h1 : (starRingEnd ℂ z) ^ 2 = z ^ 2`. Rewrite using `[← map_pow, hz, map_neg, map_natCast]`.

Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2` into its components or cases. It suffices to derive a contradiction. Establish `hre` using `Complex.conj_eq_iff_re.1 h2`. Establish `h3 : ((z.re ^ 2 : ℝ) : ℂ) = ((-(q : ℝ) : ℝ) : ℂ)` using `by push_cast; rw [hre]; exact hz`. Establish `h4` using `Complex.ofReal_injective h3`.

Establish `h5 : (0 : ℝ) < q` using `by exact_mod_cast hq`. Use polynomial arithmetic with `[sq_nonneg z.re]`. Conclude with `h2`.
-/
lemma phi_conj (hq : 0 < q) (ha : a ^ 2 = -(q : L)) (φ : L →+* ℂ) :
    starRingEnd ℂ (φ a) = -φ a := by
  set z := φ a with hzdef
  have hz : z ^ 2 = -(q : ℂ) := by
    rw [hzdef, ← map_pow, ha, map_neg, map_natCast]
  have h1 : (starRingEnd ℂ z) ^ 2 = z ^ 2 := by
    rw [← map_pow, hz, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exfalso
    have hre := Complex.conj_eq_iff_re.1 h2
    have h3 : ((z.re ^ 2 : ℝ) : ℂ) = ((-(q : ℝ) : ℝ) : ℂ) := by
      push_cast; rw [hre]; exact hz
    have h4 := Complex.ofReal_injective h3
    have h5 : (0 : ℝ) < q := by exact_mod_cast hq
    nlinarith [sq_nonneg z.re]
  · exact h2

/- English proof (translation)
Establish `ha0` using `ne_zero_of_sq hq ha`. Establish `hsq : σ a ^ 2 = a ^ 2`. Rewrite using `[← map_pow, ha, map_neg, map_natCast]`. Unfold `sgn`. Use `split_ifs with hc`.

Prove the components needed by the constructor for the conclusion. Introduce `h; exact absurd h (by decide)`. Introduce `h`. It suffices to derive a contradiction. Establish `h3 : (2 : L) * a = 0` using `by linear_combination h - hc`.

Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases. Conclude with `two_ne_zero h4`. Conclude with `ha0 h4`. Simplify using `only [true_iff]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h1 | h1` into its components or cases.

Conclude with `absurd h1 hc`. Conclude with `h1`.
-/
lemma sgn_eq_neg_one_iff (hq : 0 < q) (ha : a ^ 2 = -(q : L)) (σ : Gal(L/ℚ)) :
    sgn σ a = -1 ↔ σ a = -a := by
  have ha0 := ne_zero_of_sq hq ha
  have hsq : σ a ^ 2 = a ^ 2 := by
    rw [← map_pow, ha, map_neg, map_natCast]
  unfold sgn
  split_ifs with hc
  · constructor
    · intro h; exact absurd h (by decide)
    · intro h
      exfalso
      have h3 : (2 : L) * a = 0 := by linear_combination h - hc
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact two_ne_zero h4
      · exact ha0 h4
  · simp only [true_iff]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h1 | h1
    · exact absurd h1 hc
    · exact h1

/- English proof (translation)
Rewrite using `[← hζ.autToPow_spec ℚ σ, pow_eq_inv_iff hζ, ZMod.natCast_val, ZMod.cast_id, Units.ext_iff, Units.val_neg, Units.val_one]`.
-/
lemma autToPow_eq_neg_one_iff (hζ : IsPrimitiveRoot ζ (2 ^ n)) (σ : Gal(L/ℚ)) :
    hζ.autToPow ℚ σ = -1 ↔ σ ζ = ζ⁻¹ := by
  rw [← hζ.autToPow_spec ℚ σ, pow_eq_inv_iff hζ, ZMod.natCast_val, ZMod.cast_id, Units.ext_iff,
    Units.val_neg, Units.val_one]

/- English proof (translation)
Simplify using `only [galMap, JJ, Prod.mk.injEq]`.
-/
lemma galMap_eq_JJ_iff (hζ : IsPrimitiveRoot ζ (2 ^ n)) (σ : Gal(L/ℚ)) :
    galMap hζ a b σ = JJ n ↔ hζ.autToPow ℚ σ = -1 ∧ sgn σ a = -1 ∧ sgn σ b = -1 := by
  simp only [galMap, JJ, Prod.mk.injEq]

/- English proof (translation)
Rewrite using `[← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), h.2.2.2]`. Both sides reduce to the same expression.
-/
lemma algAdjoin_eq_top (h : IsLayer n q d ζ a b) : Algebra.adjoin ℚ ({ζ, a, b} : Set L) = ⊤ := by
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), h.2.2.2]
  rfl

/- English proof (translation)
Take `⟨hζ, ha, hb, _⟩` from `h`. Establish `hφζ : (φ ζ) ^ (2 ^ n) = 1` using `by rw [← map_pow, hζ.pow_eq_one, map_one]`. Establish `hconj : starRingEnd ℂ (φ ζ) = φ (ζ⁻¹)`. Rewrite using `[map_inv₀, conj_eq_inv_of_pow_eq_one (pow_ne_zero n two_ne_zero) hφζ]`. Rewrite using `[galMap_eq_JJ_iff, autToPow_eq_neg_one_iff, sgn_eq_neg_one_iff hq ha, sgn_eq_neg_one_iff hd hb]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨φ.injective ?_, φ.injective ?_, φ.injective ?_⟩` and prove the remaining obligations. Rewrite using `[hx, hconj]`. Rewrite using `[hx, map_neg, phi_conj hq ha]`.

Rewrite using `[hx, map_neg, phi_conj hd hb]`. Introduce and unpack `⟨h1, h2, h3⟩`. Establish `heq : (φ.comp (σ : L →+* L)).toRatAlgHom = ((starRingEnd ℂ).comp φ).toRatAlgHom`. Apply `AlgHom.ext_of_adjoin_eq_top (algAdjoin_eq_top ⟨hζ, ha, hb, ‹_›⟩)` to reduce the goal to its premises. Introduce `x hx`.

Simplify using `only [RingHom.toRatAlgHom_apply, RingHom.coe_comp, Function.comp_apply]`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx`. Express the relevant statement in the definitionally equal form `φ (σ x) = starRingEnd ℂ (φ x)`. Break down `hx with rfl | rfl | rfl` into its components or cases. Rewrite using `[h1, hconj]`.

Rewrite using `[h2, map_neg, phi_conj hq ha]`. Rewrite using `[h3, map_neg, phi_conj hd hb]`. Introduce `x`. Use `congrArg (fun f => f x) heq` as an intermediate fact. Simplify using `using this`.
-/
theorem conj_iff (hq : 0 < q) (hd : 0 < d) (h : IsLayer n q d ζ a b) (φ : L →+* ℂ)
    (σ : Gal(L/ℚ)) :
    (∀ x : L, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galMap h.1 a b σ = JJ n := by
  obtain ⟨hζ, ha, hb, _⟩ := h
  have hφζ : (φ ζ) ^ (2 ^ n) = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hconj : starRingEnd ℂ (φ ζ) = φ (ζ⁻¹) := by
    rw [map_inv₀, conj_eq_inv_of_pow_eq_one (pow_ne_zero n two_ne_zero) hφζ]
  rw [galMap_eq_JJ_iff, autToPow_eq_neg_one_iff, sgn_eq_neg_one_iff hq ha,
    sgn_eq_neg_one_iff hd hb]
  constructor
  · intro hx
    refine ⟨φ.injective ?_, φ.injective ?_, φ.injective ?_⟩
    · rw [hx, hconj]
    · rw [hx, map_neg, phi_conj hq ha]
    · rw [hx, map_neg, phi_conj hd hb]
  · rintro ⟨h1, h2, h3⟩
    have heq : (φ.comp (σ : L →+* L)).toRatAlgHom = ((starRingEnd ℂ).comp φ).toRatAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top (algAdjoin_eq_top ⟨hζ, ha, hb, ‹_›⟩)
      intro x hx
      simp only [RingHom.toRatAlgHom_apply, RingHom.coe_comp, Function.comp_apply]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      change φ (σ x) = starRingEnd ℂ (φ x)
      rcases hx with rfl | rfl | rfl
      · rw [h1, hconj]
      · rw [h2, map_neg, phi_conj hq ha]
      · rw [h3, map_neg, phi_conj hd hb]
    intro x
    have := congrArg (fun f => f x) heq
    simpa using this

end UnitConjugation

open UnitConjugation

/- English proof (translation)
Introduce `n q d _ hqd L _ _ ζ a b h φ σ`. Conclude with `conj_iff hqd.1.pos hqd.2.1.pos h φ σ`.
-/
theorem layerConj_of (_hG : LayerGalois) : LayerConj := by
  intro n q d _ hqd L _ _ ζ a b h φ σ
  exact conj_iff hqd.1.pos hqd.2.1.pos h φ σ

/- English proof (translation)
Introduce `n q d hn hqd L _ _ ζ a b h`. Take `⟨hGal, hfin, _hmul, hbij⟩` from `hG n q d hn hqd L ζ a b h`. Establish `h1 : ∀ (φ : L →+* ℂ) (σ : Gal(L/ℚ)), (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galMap h.1 a b σ = JJ n` using `fun φ σ => hC n q d hn hqd L ζ a b h φ σ`. Establish `hq : 0 < q` using `hqd.1.pos`. Take `⟨σc, hσc⟩` from `hbij.2 (JJ n)`.

Establish `hTC : IsTotallyComplex L`. Use `⟨fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]`. Introduce `hw`. Establish `h2` using `RingHom.congr_fun hw a`.

Rewrite `h2` using `[ComplexEmbedding.conjugate_coe_eq, phi_conj hq h.2.1]`. Establish `h3 : (2 : ℂ) * w.embedding a = 0` using `by linear_combination -h2`. Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases. Conclude with `two_ne_zero h4`. Conclude with `(map_ne_zero _).2 (ne_zero_of_sq hq h.2.1) h4`.

Establish `hCM : IsCMField L`. Use `IsCMField.of_forall_isConj L (σ := σc) (fun φ => ?_)` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `((h1 φ σc).2 hσc x).symm`.

Establish `h5 : ∀ x : L, x ∈ maximalRealSubfield L ↔ ∀ σ : Gal(L/ℚ), galMap h.1 a b σ = JJ n → σ x = x`. Introduce `x`. Rewrite using `[mem_maximalRealSubfield_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hx σ hσ`.

Set `φ : L →+* ℂ` to `Classical.choice (inferInstance : Nonempty _)`. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[(h1 φ σ).2 hσ x]`. Conclude with `hx φ`. Introduce `hx φ`.

Use `(h1 φ σc).2 hσc x` as an intermediate fact. Rewrite `this` using `[hx σc hσc]`. Conclude with `this.symm`. Establish `h4 : Module.finrank ℚ (maximalRealSubfield L) = 2 ^ n`. Establish `h` using `Module.finrank_mul_finrank ℚ (maximalRealSubfield L) L`.

Rewrite `h` using `[Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L, hfin, pow_succ]`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨hCM, h5, h4⟩`.
-/
theorem layerReal_of (hG : LayerGalois) (hC : LayerConj) : LayerReal := by
  intro n q d hn hqd L _ _ ζ a b h
  obtain ⟨hGal, hfin, _hmul, hbij⟩ := hG n q d hn hqd L ζ a b h
  have h1 : ∀ (φ : L →+* ℂ) (σ : Gal(L/ℚ)),
      (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galMap h.1 a b σ = JJ n :=
    fun φ σ => hC n q d hn hqd L ζ a b h φ σ
  have hq : 0 < q := hqd.1.pos
  obtain ⟨σc, hσc⟩ := hbij.2 (JJ n)
  have hTC : IsTotallyComplex L := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]
    intro hw
    have h2 := RingHom.congr_fun hw a
    rw [ComplexEmbedding.conjugate_coe_eq, phi_conj hq h.2.1] at h2
    have h3 : (2 : ℂ) * w.embedding a = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact (map_ne_zero _).2 (ne_zero_of_sq hq h.2.1) h4
  have hCM : IsCMField L := by
    refine IsCMField.of_forall_isConj L (σ := σc) (fun φ => ?_)
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact ((h1 φ σc).2 hσc x).symm
  have h5 : ∀ x : L, x ∈ maximalRealSubfield L ↔
      ∀ σ : Gal(L/ℚ), galMap h.1 a b σ = JJ n → σ x = x := by
    intro x
    rw [mem_maximalRealSubfield_iff]
    constructor
    · intro hx σ hσ
      let φ : L →+* ℂ := Classical.choice (inferInstance : Nonempty _)
      apply φ.injective
      rw [(h1 φ σ).2 hσ x]
      exact hx φ
    · intro hx φ
      have := (h1 φ σc).2 hσc x
      rw [hx σc hσc] at this
      exact this.symm
  have h4 : Module.finrank ℚ (maximalRealSubfield L) = 2 ^ n := by
    have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield L) L
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L, hfin,
      pow_succ] at h
    omega
  exact ⟨hCM, h5, h4⟩

end Formalism.TwoAdicCyclotomicDecomposition
