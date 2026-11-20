import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

open Formalism.UG Formalism.UG.P Inhab

/- English proof (translation)
Generalize the expression as in `he : μ * ψ m = e at hidem hjac`. Establish `hb : Ideal.span {ψ m} * 𝔞.map ψ ⊔ Ideal.span {ψ a} = 𝔞.map ψ` using `by conv_rhs => rw [← ha]`. Rewrite using `[Ideal.map_sup, Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]`. Establish `haa : a ∈ 𝔞`. Rewrite using `[← ha]`.

Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)`. Establish `ha' : ψ a ∈ 𝔞.map ψ` using `Ideal.mem_map_of_mem ψ haa`. Establish `he' : e ∈ 𝔞.map ψ`. Rewrite using `[← he]`. Conclude with `Ideal.mul_mem_left _ μ (Ideal.mem_map_of_mem ψ hm)`.

Use `⟨e + (1 - e) * ψ a, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Establish `h1 : e ∈ Ideal.span {e + (1 - e) * ψ a}` using `Ideal.mem_span_singleton'.2 ⟨e, by linear_combination (1 - ψ a) * hidem⟩`. Establish `h2 : (1 - e) * ψ a ∈ Ideal.span {e + (1 - e) * ψ a}` using `Ideal.mem_span_singleton'.2 ⟨1 - e, by linear_combination (ψ a - 1) * hidem⟩`. Use `Submodule.le_of_le_smul_of_le_jacobson_bot (hfg.map ψ) ((Ideal.span_singleton_le_iff_mem _).2 hjac) ?_` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx` using `[← hb]`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx`. Take `⟨w, hw, rfl⟩` from `Ideal.mem_span_singleton_mul.1 hy`. Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton'.1 hz`. Use `Submodule.mem_sup.2 ⟨e * (ψ m * w + s * ψ a) + s * ((1 - e) * ψ a), ?_, ((1 - e) * ψ m) • w, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hw, ?_⟩` and prove the remaining obligations.

Conclude with `add_mem (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h2)`. Rewrite using `[smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Conclude with `add_mem he' (Ideal.mul_mem_left _ _ ha')`.
-/
theorem map_eq_span_of_idem {O S : Type} [CommRing O] [CommRing S] (ψ : O →+* S) (𝔞 : Ideal O) (hfg : 𝔞.FG)
    (m a : O) (hm : m ∈ 𝔞) (ha : Ideal.span {m} * 𝔞 ⊔ Ideal.span {a} = 𝔞) (μ : S)
    (hidem : (μ * ψ m) * (μ * ψ m) = μ * ψ m)
    (hjac : (1 - μ * ψ m) * ψ m ∈ Ideal.jacobson (⊥ : Ideal S)) :
    ∃ t : S, 𝔞.map ψ = Ideal.span {t} := by
  generalize he : μ * ψ m = e at hidem hjac
  have hb : Ideal.span {ψ m} * 𝔞.map ψ ⊔ Ideal.span {ψ a} = 𝔞.map ψ := by
    conv_rhs => rw [← ha]
    rw [Ideal.map_sup, Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_singleton]
  have haa : a ∈ 𝔞 := by
    rw [← ha]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have ha' : ψ a ∈ 𝔞.map ψ := Ideal.mem_map_of_mem ψ haa
  have he' : e ∈ 𝔞.map ψ := by
    rw [← he]
    exact Ideal.mul_mem_left _ μ (Ideal.mem_map_of_mem ψ hm)
  refine ⟨e + (1 - e) * ψ a, le_antisymm ?_ ?_⟩
  · have h1 : e ∈ Ideal.span {e + (1 - e) * ψ a} :=
      Ideal.mem_span_singleton'.2 ⟨e, by linear_combination (1 - ψ a) * hidem⟩
    have h2 : (1 - e) * ψ a ∈ Ideal.span {e + (1 - e) * ψ a} :=
      Ideal.mem_span_singleton'.2 ⟨1 - e, by linear_combination (ψ a - 1) * hidem⟩
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (hfg.map ψ)
      ((Ideal.span_singleton_le_iff_mem _).2 hjac) ?_
    intro x hx
    rw [← hb] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨w, hw, rfl⟩ := Ideal.mem_span_singleton_mul.1 hy
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    refine Submodule.mem_sup.2 ⟨e * (ψ m * w + s * ψ a) + s * ((1 - e) * ψ a), ?_,
      ((1 - e) * ψ m) • w, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hw, ?_⟩
    · exact add_mem (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h2)
    · rw [smul_eq_mul]
      ring
  · rw [Ideal.span_singleton_le_iff_mem]
    exact add_mem he' (Ideal.mul_mem_left _ _ ha')

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hmem : ∀ v, f v ∈ v.adicCompletionIntegers F` using `fun v => by`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `hf v`. Conclude with `⟨⟨⟨f, Filter.Eventually.of_forall hmem⟩, hmem⟩, fun _ => rfl⟩`.
-/
theorem exists_intAd (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, Valued.v (f v) ≤ 1) : ∃ x : intAd F, ∀ v, (x : Af F) v = f v := by
  have hmem : ∀ v, f v ∈ v.adicCompletionIntegers F := fun v => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hf v
  exact ⟨⟨⟨f, Filter.Eventually.of_forall hmem⟩, hmem⟩, fun _ => rfl⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `DFunLike.ext _ _ h`.
-/
theorem intAd_ext {x y : intAd F} (h : ∀ v, (x : Af F) v = (y : Af F) v) : x = y := by
  apply Subtype.ext
  exact DFunLike.ext _ _ h

/- English proof (translation)
Establish `hne : ∀ v, (x : Af F) v ≠ 0` using `fun v h0 => by simpa [h0] using hx v`. Take `⟨y, hy⟩` from `exists_intAd (fun v => ((x : Af F) v)⁻¹) (fun v => by rw [map_inv₀, hx v, inv_one])`. Establish `hxy : x * y = 1`. Use `intAd_ext fun v => ?_` and prove the remaining obligations. Use `show (x : Af F) v * (y : Af F) v = (1 : Af F) v`.

Rewrite using `[hy v, mul_inv_cancel₀ (hne v)]`. Both sides reduce to the same expression. Conclude with `⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩`.
-/
theorem isUnit_intAd (x : intAd F) (hx : ∀ v, Valued.v ((x : Af F) v) = 1) : IsUnit x := by
  have hne : ∀ v, (x : Af F) v ≠ 0 := fun v h0 => by simpa [h0] using hx v
  obtain ⟨y, hy⟩ := exists_intAd (fun v => ((x : Af F) v)⁻¹)
    (fun v => by rw [map_inv₀, hx v, inv_one])
  have hxy : x * y = 1 := by
    refine intAd_ext fun v => ?_
    show (x : Af F) v * (y : Af F) v = (1 : Af F) v
    rw [hy v, mul_inv_cancel₀ (hne v)]
    rfl
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

/- English proof (translation)
Establish `hx2 : ∀ v, (x : Af F) v ∈ v.adicCompletionIntegers F` using `x.2`. Establish `hle : ∀ v, Valued.v ((x : Af F) v) ≤ 1` using `fun v => by`. Use `hx2 v` as an intermediate fact. Rewrite `this` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Then use the resulting hypothesis. Take `⟨μ, hμ⟩` from `exists_intAd (fun v => if Valued.v ((x : Af F) v) = 1 then ((x : Af F) v)⁻¹ else 0) (fun v => by split_ifs with h`.

Rewrite using `[map_inv₀, h, inv_one]`. Rewrite using `[map_zero]`. Conclude with `zero_le)`. Establish `hprod : ∀ v, ((μ * x : intAd F) : Af F) v = if Valued.v ((x : Af F) v) = 1 then 1 else 0`. Introduce `v`.

Use `show (μ : Af F) v * (x : Af F) v = _`. Rewrite using `[hμ v]`. Use `split_ifs with h`. Use `inv_mul_cancel₀ fun h0 => ?_` and prove the remaining obligations. Rewrite `h` using `[h0, map_zero]`.

Conclude with `zero_ne_one h`. Conclude with `zero_mul _`. Use `⟨μ, intAd_ext fun v => ?_, Ideal.mem_jacobson_bot.2 fun y => isUnit_intAd _ fun v => ?_⟩` and prove the remaining obligations. Use `show ((μ * x : intAd F) : Af F) v * ((μ * x : intAd F) : Af F) v = ((μ * x : intAd F) : Af F) v`. Rewrite using `[hprod v]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hy2 : ∀ w, (y : Af F) w ∈ w.adicCompletionIntegers F` using `y.2`. Establish `hyle : Valued.v ((y : Af F) v) ≤ 1`. Use `hy2 v` as an intermediate fact. Rewrite `this` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Then use the resulting hypothesis.

Use `show Valued.v ((1 - ((μ * x : intAd F) : Af F) v) * (x : Af F) v * (y : Af F) v + 1) = 1`. Distinguish the cases in `h : Valued.v ((x : Af F) v) = 1`. Rewrite using `[hprod v, if_pos h, sub_self, zero_mul, zero_mul, zero_add, map_one]`. Rewrite using `[hprod v, if_neg h, sub_zero, one_mul, add_comm]`. Apply `Valuation.map_one_add_of_lt` to reduce the goal to its premises.

Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_one]`. Conclude with `lt_of_le_of_ne (hle v) h`.
-/
theorem exists_idem_intAd (x : intAd F) : ∃ μ : intAd F, (μ * x) * (μ * x) = μ * x ∧
    (1 - μ * x) * x ∈ Ideal.jacobson (⊥ : Ideal (intAd F)) := by
  classical
  have hx2 : ∀ v, (x : Af F) v ∈ v.adicCompletionIntegers F := x.2
  have hle : ∀ v, Valued.v ((x : Af F) v) ≤ 1 := fun v => by
    have := hx2 v
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this
  obtain ⟨μ, hμ⟩ := exists_intAd
    (fun v => if Valued.v ((x : Af F) v) = 1 then ((x : Af F) v)⁻¹ else 0)
    (fun v => by
      split_ifs with h
      · rw [map_inv₀, h, inv_one]
      · rw [map_zero]
        exact zero_le)
  have hprod : ∀ v, ((μ * x : intAd F) : Af F) v =
      if Valued.v ((x : Af F) v) = 1 then 1 else 0 := by
    intro v
    show (μ : Af F) v * (x : Af F) v = _
    rw [hμ v]
    split_ifs with h
    · refine inv_mul_cancel₀ fun h0 => ?_
      rw [h0, map_zero] at h
      exact zero_ne_one h
    · exact zero_mul _
  refine ⟨μ, intAd_ext fun v => ?_, Ideal.mem_jacobson_bot.2 fun y => isUnit_intAd _ fun v => ?_⟩
  · show ((μ * x : intAd F) : Af F) v * ((μ * x : intAd F) : Af F) v = ((μ * x : intAd F) : Af F) v
    rw [hprod v]
    split_ifs <;> simp
  · have hy2 : ∀ w, (y : Af F) w ∈ w.adicCompletionIntegers F := y.2
    have hyle : Valued.v ((y : Af F) v) ≤ 1 := by
      have := hy2 v
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this
    show Valued.v ((1 - ((μ * x : intAd F) : Af F) v) * (x : Af F) v * (y : Af F) v + 1) = 1
    by_cases h : Valued.v ((x : Af F) v) = 1
    · rw [hprod v, if_pos h, sub_self, zero_mul, zero_mul, zero_add, map_one]
    · rw [hprod v, if_neg h, sub_zero, one_mul, add_comm]
      apply Valuation.map_one_add_of_lt
      rw [map_mul]
      calc Valued.v ((x : Af F) v) * Valued.v ((y : Af F) v) ≤ Valued.v ((x : Af F) v) * 1 :=
            by gcongr
        _ < 1 := by
            rw [mul_one]
            exact lt_of_le_of_ne (hle v) h

noncomputable def intAdIncl (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    intAd F →+* IntAf F E :=
  ((Algebra.TensorProduct.includeRight : Af F →ₐ[F] E ⊗[F] Af F).toRingHom.comp (intAd F).subtype).codRestrict _
    fun y => Subring.subset_closure (Or.inr ⟨y, rfl⟩)

/- English proof (translation)
Set `_ : Algebra (intAd F) (IntAf F E)` to `(intAdIncl F E).toAlgebra`. Establish `hpsi : ∀ b : 𝓞 E, IsIntegral (intAd F) (psi F E b)`. Introduce `b`. Take `⟨p, hp, hpb⟩` from `RingOfIntegers.isIntegral b`. Use `⟨p.map (Int.castRingHom (intAd F)), hp.map _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.eval₂_map, RingHom.ext_int ((algebraMap (intAd F) (IntAf F E)).comp (Int.castRingHom (intAd F))) ((psi F E).comp (algebraMap ℤ (𝓞 E))), ← Polynomial.hom_eval₂, hpb, map_zero]`. Set `T : Subring (E ⊗[F] Af F)` to `(integralClosure (intAd F) (IntAf F E)).toSubring.map (IntAf F E).subtype`. Establish `hle : IntAf F E ≤ T` using `by show Formalism.UG.tensInt (F := F) (Af F) (Formalism.UG.intOE E) (Formalism.UG.intAd F) ≤ T`. Unfold `Formalism.UG.tensInt`. Rewrite using `[Subring.closure_le]`.

Introduce and unpack `z (⟨⟨_, hb⟩, rfl⟩ | ⟨y, rfl⟩)`. Take `⟨b, rfl⟩` from `RingHom.mem_range.1 hb`. Conclude with `⟨psi F E b, hpsi b, rfl⟩`. Conclude with `⟨algebraMap (intAd F) (IntAf F E) y, isIntegral_algebraMap, rfl⟩`. Introduce `x`.

Take `⟨y, hy, hyx⟩` from `hle x.2`. Rewrite using `[show x = y from Subtype.ext hyx.symm]`. Conclude with `hy`.
-/
theorem intAdIncl_isIntegral : (intAdIncl F E).IsIntegral := by
  let _ : Algebra (intAd F) (IntAf F E) := (intAdIncl F E).toAlgebra
  have hpsi : ∀ b : 𝓞 E, IsIntegral (intAd F) (psi F E b) := by
    intro b
    obtain ⟨p, hp, hpb⟩ := RingOfIntegers.isIntegral b
    refine ⟨p.map (Int.castRingHom (intAd F)), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap (intAd F) (IntAf F E)).comp (Int.castRingHom (intAd F)))
        ((psi F E).comp (algebraMap ℤ (𝓞 E))),
      ← Polynomial.hom_eval₂, hpb, map_zero]
  let T : Subring (E ⊗[F] Af F) :=
    (integralClosure (intAd F) (IntAf F E)).toSubring.map (IntAf F E).subtype
  have hle : IntAf F E ≤ T := by
    show Formalism.UG.tensInt (F := F) (Af F) (Formalism.UG.intOE E) (Formalism.UG.intAd F) ≤ T
    unfold Formalism.UG.tensInt
    rw [Subring.closure_le]
    rintro z (⟨⟨_, hb⟩, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨b, rfl⟩ := RingHom.mem_range.1 hb
      exact ⟨psi F E b, hpsi b, rfl⟩
    · exact ⟨algebraMap (intAd F) (IntAf F E) y, isIntegral_algebraMap, rfl⟩
  intro x
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rw [show x = y from Subtype.ext hyx.symm]
  exact hy

/- English proof (translation)
Unfold `Ideal.jacobson at hx ⊢`. Rewrite `hx`, the goal using `[Submodule.mem_sInf]`. Introduce and unpack `M ⟨-, hM⟩`. Use `hM` as an intermediate fact. Conclude with `hx _ ⟨bot_le, Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ intAdIncl_isIntegral M⟩`.
-/
theorem intAdIncl_jacobson {x : intAd F} (hx : x ∈ Ideal.jacobson (⊥ : Ideal (intAd F))) :
    intAdIncl F E x ∈ Ideal.jacobson (⊥ : Ideal (IntAf F E)) := by
  unfold Ideal.jacobson at hx ⊢
  rw [Submodule.mem_sInf] at hx ⊢
  rintro M ⟨-, hM⟩
  have := hM
  exact hx _ ⟨bot_le, Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ intAdIncl_isIntegral M⟩

/- English proof (translation)
Establish `hN0 : Ideal.absNorm 𝔞 ≠ 0` using `fun h0 => h (Ideal.absNorm_eq_zero_iff.1 h0)`. Establish `hNmem : ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) ∈ 𝔞` using `Ideal.absNorm_mem 𝔞`. Establish `hNne : ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) ≠ 0`. Introduce `h0`. Apply `hN0` to reduce the goal to its premises.

Use `congrArg (algebraMap (𝓞 E) E) h0` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`. Conclude with `this` after adjusting the coercions. Establish `hI : Ideal.span {((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E)} * 𝔞 ≠ 0`. Rewrite using `[Ne, Submodule.zero_eq_bot, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]`.

Conclude with `⟨hNne, h⟩`. Take `⟨a, ha⟩` from `IsDedekindDomain.exists_sup_span_eq (J := 𝔞) (Ideal.mul_le.2 fun _ _ _ hy => Ideal.mul_mem_left _ _ hy) hI`. Take `⟨μ₀, hidem, hjac⟩` from `exists_idem_intAd (F := F) ((Ideal.absNorm 𝔞 : ℕ) : intAd F)`. Take `⟨t, ht⟩` from `map_eq_span_of_idem (psi F E) 𝔞 (IsNoetherian.noetherian 𝔞) _ a hNmem ha (intAdIncl F E μ₀) (by simpa [map_mul] using congrArg (intAdIncl F E) hidem) (by simpa [map_mul, map_sub] using intAdIncl_jacobson (E := E) hjac)`. Use `⟨t, ?_, ht⟩` and prove the remaining obligations.

Establish `hmem : psi F E ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) ∈ Ideal.span {t}`. Rewrite using `[← ht]`. Conclude with `Ideal.mem_map_of_mem _ hNmem`. Take `⟨s, hs⟩` from `Ideal.mem_span_singleton'.1 hmem`. Establish `hu : IsUnit ((psi F E ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) : IntAf F E) : E ⊗[F] Af F)`.

Rewrite using `[map_natCast, SubringClass.coe_natCast, ← map_natCast (algebraMap F (E ⊗[F] Af F))]`. Conclude with `(IsUnit.mk0 _ (Nat.cast_ne_zero.2 hN0)).map _`. Rewrite `hu` using `[← hs, Subring.coe_mul]`. Conclude with `isUnit_of_mul_isUnit_right hu`.
-/
theorem exists_map_psi_eq_span (𝔞 : Ideal (𝓞 E)) (h : 𝔞 ≠ ⊥) :
    ∃ t : IntAf F E, IsUnit (t : E ⊗[F] Af F) ∧ 𝔞.map (psi F E) = Ideal.span {t} := by
  have hN0 : Ideal.absNorm 𝔞 ≠ 0 := fun h0 => h (Ideal.absNorm_eq_zero_iff.1 h0)
  have hNmem : ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) ∈ 𝔞 := Ideal.absNorm_mem 𝔞
  have hNne : ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) ≠ 0 := by
    intro h0
    apply hN0
    have := congrArg (algebraMap (𝓞 E) E) h0
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  have hI : Ideal.span {((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E)} * 𝔞 ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    exact ⟨hNne, h⟩
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (J := 𝔞)
    (Ideal.mul_le.2 fun _ _ _ hy => Ideal.mul_mem_left _ _ hy) hI
  obtain ⟨μ₀, hidem, hjac⟩ := exists_idem_intAd (F := F) ((Ideal.absNorm 𝔞 : ℕ) : intAd F)
  obtain ⟨t, ht⟩ := map_eq_span_of_idem (psi F E) 𝔞 (IsNoetherian.noetherian 𝔞) _ a hNmem ha
    (intAdIncl F E μ₀)
    (by simpa [map_mul] using congrArg (intAdIncl F E) hidem)
    (by simpa [map_mul, map_sub] using intAdIncl_jacobson (E := E) hjac)
  refine ⟨t, ?_, ht⟩
  have hmem : psi F E ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) ∈ Ideal.span {t} := by
    rw [← ht]
    exact Ideal.mem_map_of_mem _ hNmem
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hmem
  have hu : IsUnit ((psi F E ((Ideal.absNorm 𝔞 : ℕ) : 𝓞 E) : IntAf F E) : E ⊗[F] Af F) := by
    rw [map_natCast, SubringClass.coe_natCast, ← map_natCast (algebraMap F (E ⊗[F] Af F))]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hN0)).map _
  rw [← hs, Subring.coe_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

/- English proof (translation)
Use `⟨fun ha => ?_, fun ha => Ideal.mem_map_of_mem _ ha⟩` and prove the remaining obligations. Take `⟨c, hc, hc0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`. Take `⟨𝔟, h𝔟⟩` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hc)`. Establish `h𝔟0 : 𝔟 ≠ 0`. Introduce and unpack `rfl`.

Rewrite `h𝔟` using `[mul_zero, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hc0 h𝔟`. Establish `hcE : algebraMap (𝓞 E) E c ≠ 0` using `fun h0 => hc0 (RingOfIntegers.coe_injective (h0.trans (map_zero _).symm))`. Establish `key : Ideal.span {a} * 𝔟 ≤ 𝔞 * 𝔟`. Rewrite using `[← h𝔟, Ideal.span_singleton_mul_le_iff]`.

Introduce `b hb`. Establish `h1 : psi F E (a * b) ∈ Ideal.span {psi F E c}`. Establish `h2 : psi F E (a * b) ∈ (𝔞 * 𝔟).map (psi F E)`. Rewrite using `[map_mul, Ideal.map_mul]`. Conclude with `Ideal.mul_mem_mul ha (Ideal.mem_map_of_mem _ hb)`.

Rewrite `h2` using `[← h𝔟, Ideal.map_span, Set.image_singleton]`. Then use the resulting hypothesis. Take `⟨s, hs⟩` from `Ideal.mem_span_singleton'.1 h1`. Establish `hpsi : ∀ z : 𝓞 E, ((psi F E z : IntAf F E) : E ⊗[F] Af F) = inclE (F` using `F) (Af F) (algebraMap (𝓞 E) E z) := fun _ => rfl`. Establish `e1` using `congrArg (fun z : IntAf F E => (z : E ⊗[F] Af F)) hs`. Simplify using `only [Subring.coe_mul, hpsi] at e1`.

Establish `hq : inclE (F` using `F) (Af F) (algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c) = (s : E ⊗[F] Af F) := by`. Establish `hu : IsUnit (inclE (F` using `F) (Af F) (algebraMap (𝓞 E) E c)) := (IsUnit.mk0 _ hcE).map _`. Apply `hu.mul_right_cancel` to reduce the goal to its premises. Rewrite using `[e1, ← map_mul, div_mul_cancel₀ _ hcE]`. Establish `hint : IsIntegral ℤ (algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c)` using `Formalism.UG.P.csGlob_int (F := F) _ (by rw [hq]; exact s.2)`.

Establish `hint' : algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c ∈ integralClosure ℤ E` using `hint`. Take `⟨k, hk⟩ : ∃ k : 𝓞 E, algebraMap (𝓞 E) E k = algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c` from `⟨⟨_, hint'⟩, rfl⟩`. Use `Ideal.mem_span_singleton'.2 ⟨k, RingOfIntegers.coe_injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hk]`. Conclude with `div_mul_cancel₀ _ hcE`.

Rewrite `key` using `[← Ideal.dvd_iff_le, mul_dvd_mul_iff_right h𝔟0, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `key`.
-/
theorem psi_mem_map_iff (𝔞 : Ideal (𝓞 E)) (h : 𝔞 ≠ ⊥) (a : 𝓞 E) :
    psi F E a ∈ 𝔞.map (psi F E) ↔ a ∈ 𝔞 := by
  refine ⟨fun ha => ?_, fun ha => Ideal.mem_map_of_mem _ ha⟩
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨𝔟, h𝔟⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hc)
  have h𝔟0 : 𝔟 ≠ 0 := by
    rintro rfl
    rw [mul_zero, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot] at h𝔟
    exact hc0 h𝔟
  have hcE : algebraMap (𝓞 E) E c ≠ 0 := fun h0 => hc0 (RingOfIntegers.coe_injective (h0.trans (map_zero _).symm))
  have key : Ideal.span {a} * 𝔟 ≤ 𝔞 * 𝔟 := by
    rw [← h𝔟, Ideal.span_singleton_mul_le_iff]
    intro b hb
    have h1 : psi F E (a * b) ∈ Ideal.span {psi F E c} := by
      have h2 : psi F E (a * b) ∈ (𝔞 * 𝔟).map (psi F E) := by
        rw [map_mul, Ideal.map_mul]
        exact Ideal.mul_mem_mul ha (Ideal.mem_map_of_mem _ hb)
      rwa [← h𝔟, Ideal.map_span, Set.image_singleton] at h2
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 h1
    have hpsi : ∀ z : 𝓞 E, ((psi F E z : IntAf F E) : E ⊗[F] Af F) =
        inclE (F := F) (Af F) (algebraMap (𝓞 E) E z) := fun _ => rfl
    have e1 := congrArg (fun z : IntAf F E => (z : E ⊗[F] Af F)) hs
    simp only [Subring.coe_mul, hpsi] at e1
    have hq : inclE (F := F) (Af F) (algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c) =
        (s : E ⊗[F] Af F) := by
      have hu : IsUnit (inclE (F := F) (Af F) (algebraMap (𝓞 E) E c)) := (IsUnit.mk0 _ hcE).map _
      apply hu.mul_right_cancel
      rw [e1, ← map_mul, div_mul_cancel₀ _ hcE]
    have hint : IsIntegral ℤ (algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c) :=
      Formalism.UG.P.csGlob_int (F := F) _ (by rw [hq]; exact s.2)
    have hint' : algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c ∈ integralClosure ℤ E := hint
    obtain ⟨k, hk⟩ : ∃ k : 𝓞 E,
        algebraMap (𝓞 E) E k = algebraMap (𝓞 E) E (a * b) / algebraMap (𝓞 E) E c :=
      ⟨⟨_, hint'⟩, rfl⟩
    refine Ideal.mem_span_singleton'.2 ⟨k, RingOfIntegers.coe_injective ?_⟩
    rw [map_mul, hk]
    exact div_mul_cancel₀ _ hcE
  rw [← Ideal.dvd_iff_le, mul_dvd_mul_iff_right h𝔟0, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_iff_mem] at key
  exact key

end

/- English proof (translation)
Unfold `extId Ideal.map`. Use `congr 1`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, hz⟩`.

Conclude with `⟨a, ha, (Subtype.ext hz).symm⟩`. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨a, ha, rfl⟩`.
-/
theorem extId_eq_map (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (psi I.F I.E) := by
  unfold extId Ideal.map
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, hz⟩
    exact ⟨a, ha, (Subtype.ext hz).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

/- English proof (translation)
Introduce `I 𝔞 h𝔞`. Rewrite using `[extId_eq_map]`. Conclude with `⟨exists_map_psi_eq_span 𝔞 h𝔞, fun a _ => psi_mem_map_iff 𝔞 h𝔞 a⟩`.
-/
theorem extId_principal_and_inter : ∀ (I : AutInst) (𝔞 : Ideal (𝓞 I.E)), 𝔞 ≠ ⊥ → (∃ t : IntAf I.F I.E, IsUnit (t : (I.E ⊗[I.F] Af I.F)) ∧ extId I 𝔞 = Ideal.span {t}) ∧ ∀ (a : 𝓞 I.E) (h : Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) ∈ IntAf I.F I.E), (⟨_, h⟩ : IntAf I.F I.E) ∈ extId I 𝔞 ↔ a ∈ 𝔞 := by
  intro I 𝔞 h𝔞
  rw [extId_eq_map]
  exact ⟨exists_map_psi_eq_span 𝔞 h𝔞, fun a _ => psi_mem_map_iff 𝔞 h𝔞 a⟩

end GlobalTheory.RowLev
