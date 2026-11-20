import Mathlib
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.Columns.TwQCmp
import Formalism.LocalToGlobal.Columns.HeckeInertLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertNbr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IdemOf (F : Type) [Field F] [NumberField F] [Algebra F E] (Q : Pl E) (ε : E ⊗[F] Formalism.L2.Herm.Af F) : Prop :=
  ε * ε = ε ∧ ∀ x : 𝓞 E, x ≠ 0 → (x ∈ Q.asIdeal ↔ ε * iA F E ((x : E)⁻¹) ∉ Formalism.L2.Herm.intAf F E)

namespace IdemOf

variable {Q : Pl E} {ε : E ⊗[F] Formalism.L2.Herm.Af F} (h : IdemOf F Q ε)
include h

/- English proof (translation)
Establish `t0 : t ≠ 0` using `fun h0 => ht (h0 ▸ Q.asIdeal.zero_mem)`. Assume the negation of the conclusion as `hn`. Conclude with `ht ((h.2 t t0).2 hn)`.
-/
theorem div_mem {t : 𝓞 E} (ht : t ∉ Q.asIdeal) : ε * iA F E ((t : E)⁻¹) ∈ Formalism.L2.Herm.intAf F E := by
  have t0 : t ≠ 0 := fun h0 => ht (h0 ▸ Q.asIdeal.zero_mem)
  by_contra hn
  exact ht ((h.2 t t0).2 hn)

/- English proof (translation)
Use `h.div_mem (one_notMem Q)` as an intermediate fact. Simplify using `using this`.
-/
theorem mem : ε ∈ Formalism.L2.Herm.intAf F E := by
  have := h.div_mem (one_notMem Q)
  simpa using this

/- English proof (translation)
The claim follows from `sub_mem (one_mem _) h.mem`.
-/
theorem one_sub_mem : 1 - ε ∈ Formalism.L2.Herm.intAf F E := sub_mem (one_mem _) h.mem

/- English proof (translation)
Rewrite using `[mul_sub, h.1, mul_one, sub_self]`.
-/
theorem mul_one_sub : ε * (1 - ε) = 0 := by rw [mul_sub, h.1, mul_one, sub_self]

/- English proof (translation)
Take `⟨a, t, ht, e⟩` from `qsp_frac Q x hx`. Establish `t0 : (t : E) ≠ 0` using `fun h0 => ht (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)`. Establish `e2 : x = (t : E)⁻¹ * algebraMap (𝓞 E) E a`. Rewrite using `[← e]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e2, map_mul, ← mul_assoc]`. Conclude with `mul_mem (h.div_mem ht) (iA_mem a)`.
-/
theorem mul_mem_of_val {x : E} (hx : Q.valuation E x ≤ 1) : ε * iA F E x ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨a, t, ht, e⟩ := qsp_frac Q x hx
  have t0 : (t : E) ≠ 0 := fun h0 => ht (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  have e2 : x = (t : E)⁻¹ * algebraMap (𝓞 E) E a := by
    rw [← e]; field_simp
  rw [e2, map_mul, ← mul_assoc]
  exact mul_mem (h.div_mem ht) (iA_mem a)

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨t, htw, htQ⟩ : ∃ t ∈ w.asIdeal, t ∉ Q.asIdeal := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Conclude with `hw (HeightOneSpectrum.ext (w.isMaximal.eq_of_le Q.isPrime.ne_top hn))`. Establish `t0 : (t : E) ≠ 0` using `fun h0 => htQ (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)`.

Establish `e : (⟨ε * a, ha⟩ : Formalism.L2.Herm.intAf F E) = oToS F E t * (⟨_, h.div_mem htQ⟩ * ⟨ε * a, ha⟩)`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ε * a = iA F E (t : E) * (ε * iA F E ((t : E)⁻¹) * (ε * a))`. Establish `: iA F E (t : E) * iA F E ((t : E)⁻¹) = 1` using `by rw [← map_mul, mul_inv_cancel₀ t0, map_one]`. Take the linear combination `(-(ε * a) * ε) * this - a * h.1`.

Rewrite using `[e, map_mul, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 htw, zero_mul]`.
-/
theorem resS_eq_zero {w : Pl E} (hw : w ≠ Q) {a : E ⊗[F] Formalism.L2.Herm.Af F} (ha : ε * a ∈ Formalism.L2.Herm.intAf F E) :
    resS F w ⟨ε * a, ha⟩ = 0 := by
  obtain ⟨t, htw, htQ⟩ : ∃ t ∈ w.asIdeal, t ∉ Q.asIdeal := by
    by_contra hn
    push Not at hn
    exact hw (HeightOneSpectrum.ext (w.isMaximal.eq_of_le Q.isPrime.ne_top hn))
  have t0 : (t : E) ≠ 0 := fun h0 => htQ (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  have e : (⟨ε * a, ha⟩ : Formalism.L2.Herm.intAf F E) = oToS F E t * (⟨_, h.div_mem htQ⟩ * ⟨ε * a, ha⟩) := by
    apply Subtype.ext
    show ε * a = iA F E (t : E) * (ε * iA F E ((t : E)⁻¹) * (ε * a))
    have : iA F E (t : E) * iA F E ((t : E)⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ t0, map_one]
    linear_combination (-(ε * a) * ε) * this - a * h.1
  rw [e, map_mul, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 htw, zero_mul]

omit h in
/- English proof (translation)
Rewrite using `[show (ϖ : E) = algebraMap (𝓞 E) E ϖ from rfl, HeightOneSpectrum.valuation_of_algebraMap]`. Establish `a1` using `(Q.intValuation_le_pow_iff_mem ϖ 1).2 (by rwa [pow_one])`. Establish `a2` using `(Q.intValuation_le_pow_iff_mem ϖ 2).not.2 h2`. Establish `h0 : Q.intValuation ϖ ≠ 0` using `fun h0 => a2 (by rw [h0]; exact zero_le)`. Rewrite `a1`, `a2` using `[← WithZero.exp_log h0, WithZero.exp_le_exp]`.

Rewrite using `[← WithZero.exp_log h0]`. Use `congr 1`. Move the coercions through the operations in `at a1 a2`. Use linear arithmetic over natural numbers and integers.
-/
theorem val_unif {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) :
    Q.valuation E (ϖ : E) = WithZero.exp (-1 : ℤ) := by
  rw [show (ϖ : E) = algebraMap (𝓞 E) E ϖ from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  have a1 := (Q.intValuation_le_pow_iff_mem ϖ 1).2 (by rwa [pow_one])
  have a2 := (Q.intValuation_le_pow_iff_mem ϖ 2).not.2 h2
  have h0 : Q.intValuation ϖ ≠ 0 := fun h0 => a2 (by rw [h0]; exact zero_le)
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at a1 a2
  rw [← WithZero.exp_log h0]
  congr 1
  push_cast at a1 a2
  omega

omit h in
/- English proof (translation)
Introduce `h0` and use `h2 (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)`.
-/
theorem unif_ne {ϖ : 𝓞 E} (h2 : ϖ ∉ Q.asIdeal ^ 2) : (ϖ : E) ≠ 0 := fun h0 =>
  h2 (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)

/- English proof (translation)
Use `Submodule.span_induction (p := fun (a : Formalism.L2.Herm.intAf F E) _ => ε * iA F E (((ϖ : E) ^ m)⁻¹) * (a : E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.intAf F E) ?_ ?_ ?_ ?_ ha` and prove the remaining obligations. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Rewrite using `[← iA_coe, mul_assoc, ← map_mul]`. Use `h.mul_mem_of_val ?_` and prove the remaining obligations. Establish `a1` using `(Q.intValuation_le_pow_iff_mem p m).2 hp`.

Rewrite using `[map_mul, map_inv₀, map_pow, val_unif h1 h2, HeightOneSpectrum.valuation_of_algebraMap, ← WithZero.exp_nsmul, inv_mul_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), mul_one]`. Simplify using `using a1`. Simplify using the standard rewrite rules. Introduce `a b _ _ ha hb`. Rewrite using `[Subring.coe_add, mul_add]`.

Conclude with `add_mem ha hb`. Introduce `c a _ ha`. Rewrite using `[smul_eq_mul, Subring.coe_mul, mul_left_comm]`. Conclude with `mul_mem c.2 ha`.
-/
theorem div_pow_mem {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) (m : ℕ) {a : Formalism.L2.Herm.intAf F E}
    (ha : a ∈ idS F (Q.asIdeal ^ m)) :
    ε * iA F E (((ϖ : E) ^ m)⁻¹) * a ∈ Formalism.L2.Herm.intAf F E := by
  refine Submodule.span_induction
    (p := fun (a : Formalism.L2.Herm.intAf F E) _ => ε * iA F E (((ϖ : E) ^ m)⁻¹) * (a : E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.intAf F E) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨p, hp, rfl⟩
    rw [← iA_coe, mul_assoc, ← map_mul]
    refine h.mul_mem_of_val ?_
    have a1 := (Q.intValuation_le_pow_iff_mem p m).2 hp
    rw [map_mul, map_inv₀, map_pow, val_unif h1 h2, HeightOneSpectrum.valuation_of_algebraMap, ← WithZero.exp_nsmul,
      inv_mul_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), mul_one]
    simpa using a1
  · simp
  · intro a b _ _ ha hb
    rw [Subring.coe_add, mul_add]; exact add_mem ha hb
  · intro c a _ ha
    rw [smul_eq_mul, Subring.coe_mul, mul_left_comm]; exact mul_mem c.2 ha

/- English proof (translation)
Take `⟨ϖ, h1, h2⟩` from `Ideal.exists_mem_pow_notMem_pow_succ Q.asIdeal Q.ne_bot Q.isPrime.ne_top 1`. Rewrite `h1` using `[pow_one]`. Establish `hi : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) * ⟨ε, h.mem⟩ = 0` using `Subtype.ext (by show (1 - ε) * ε = 0; rw [mul_comm, h.mul_one_sub])`. Establish `h3 : resS F Q ⟨1 - ε, h.one_sub_mem⟩ = 0`. Use `congrArg (resS F Q) hi` as an intermediate fact.

Rewrite `this` using `[map_mul, map_zero]`. Use `(mul_eq_zero.1 this).resolve_right fun h0 => ?_` and prove the remaining obligations. Establish `h4` using `h.div_pow_mem h1 h2 1 (a := ⟨ε, h.mem⟩) (by rw [pow_one]; exact mem_idS_of_resS h0)`. Establish `ϖ0 : ϖ ≠ 0` using `fun h0 => h2 (h0 ▸ zero_mem _)`. Use `(h.2 ϖ ϖ0).1 h1 ?_` and prove the remaining obligations.

Rewrite `h4` using `[pow_one, mul_right_comm, h.1]`. Then use the resulting hypothesis. Establish `h5` using `Ideal.pow_mem_pow (mem_idS_of_resS h3) m`. Establish `h6 : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) * ⟨1 - ε, h.one_sub_mem⟩ = ⟨1 - ε, h.one_sub_mem⟩` using `Subtype.ext (by show (1 - ε) * (1 - ε) = 1 - ε; linear_combination h.1)`. Break down `m with _ | m` into its components or cases. Unfold `idS`.

Rewrite using `[pow_zero, Ideal.one_eq_top, Ideal.map_top]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `h5` using `[IsIdempotentElem.pow_succ_eq m h6]`. Unfold `idS at h5 ⊢`. Rewrite using `[Ideal.map_pow]` and apply the resulting hypothesis.
-/
theorem one_sub_mem_idS [StarRing E] (m : ℕ) : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) ∈ idS F (Q.asIdeal ^ m) := by
  obtain ⟨ϖ, h1, h2⟩ := Ideal.exists_mem_pow_notMem_pow_succ Q.asIdeal Q.ne_bot Q.isPrime.ne_top 1
  rw [pow_one] at h1
  have hi : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) * ⟨ε, h.mem⟩ = 0 :=
    Subtype.ext (by show (1 - ε) * ε = 0; rw [mul_comm, h.mul_one_sub])
  have h3 : resS F Q ⟨1 - ε, h.one_sub_mem⟩ = 0 := by
    have := congrArg (resS F Q) hi
    rw [map_mul, map_zero] at this
    refine (mul_eq_zero.1 this).resolve_right fun h0 => ?_
    have h4 := h.div_pow_mem h1 h2 1 (a := ⟨ε, h.mem⟩) (by rw [pow_one]; exact mem_idS_of_resS h0)
    have ϖ0 : ϖ ≠ 0 := fun h0 => h2 (h0 ▸ zero_mem _)
    refine (h.2 ϖ ϖ0).1 h1 ?_
    rwa [pow_one, mul_right_comm, h.1] at h4
  have h5 := Ideal.pow_mem_pow (mem_idS_of_resS h3) m
  have h6 : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) * ⟨1 - ε, h.one_sub_mem⟩ = ⟨1 - ε, h.one_sub_mem⟩ :=
    Subtype.ext (by show (1 - ε) * (1 - ε) = 1 - ε; linear_combination h.1)
  rcases m with _ | m
  · unfold idS
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; trivial
  · rw [IsIdempotentElem.pow_succ_eq m h6] at h5
    unfold idS at h5 ⊢
    rwa [Ideal.map_pow]

/- English proof (translation)
Use `⟨h.div_pow_mem h1 h2 m, fun ha => ?_⟩` and prove the remaining obligations. Establish `e : a = oToS F E (ϖ ^ m) * ⟨_, ha⟩ + ⟨1 - ε, h.one_sub_mem⟩ * a`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (a : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E (algebraMap (𝓞 E) E (ϖ ^ m)) * (ε * iA F E (((ϖ : E) ^ m)⁻¹) * a) + (1 - ε) * a`. Establish `: iA F E (algebraMap (𝓞 E) E (ϖ ^ m)) * iA F E (((ϖ : E) ^ m)⁻¹) = 1`.

Rewrite using `[← map_mul, map_pow, mul_inv_cancel₀ (pow_ne_zero _ (unif_ne h2)), map_one]`. Take the linear combination `(-(ε * (a : E ⊗[F] Formalism.L2.Herm.Af F))) * this`. Rewrite using `[e]`. Conclude with `add_mem (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow h1 m))) (Ideal.mul_mem_right _ _ (h.one_sub_mem_idS m))`.
-/
theorem mem_idS_pow_iff [StarRing E] {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) (m : ℕ) (a : Formalism.L2.Herm.intAf F E) :
    a ∈ idS F (Q.asIdeal ^ m) ↔ ε * iA F E (((ϖ : E) ^ m)⁻¹) * a ∈ Formalism.L2.Herm.intAf F E := by
  refine ⟨h.div_pow_mem h1 h2 m, fun ha => ?_⟩
  have e : a = oToS F E (ϖ ^ m) * ⟨_, ha⟩ + ⟨1 - ε, h.one_sub_mem⟩ * a := by
    apply Subtype.ext
    show (a : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E (algebraMap (𝓞 E) E (ϖ ^ m)) * (ε * iA F E (((ϖ : E) ^ m)⁻¹) * a) + (1 - ε) * a
    have : iA F E (algebraMap (𝓞 E) E (ϖ ^ m)) * iA F E (((ϖ : E) ^ m)⁻¹) = 1 := by
      rw [← map_mul, map_pow, mul_inv_cancel₀ (pow_ne_zero _ (unif_ne h2)), map_one]
    linear_combination (-(ε * (a : E ⊗[F] Formalism.L2.Herm.Af F))) * this
  rw [e]
  exact add_mem (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow h1 m)))
    (Ideal.mul_mem_right _ _ (h.one_sub_mem_idS m))

end IdemOf

end GlobalTheory.InertNbr
