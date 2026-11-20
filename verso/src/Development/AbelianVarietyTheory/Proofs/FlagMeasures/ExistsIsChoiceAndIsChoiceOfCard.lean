import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemConjSmulOfAdjoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSubMemPow

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.SplitChoice

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow`. Consider the case `exact _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow`. Consider the case `(apply _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow ..)`.
-/
theorem exists_int_sub_mem_pow {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 E))
    (hP : P.IsMaximal) (hm : (p : 𝓞 E) ∈ P) (hN : Ideal.absNorm P = p) (h2 : (p : 𝓞 E) ∉ P ^ 2) (k : ℕ)
    (a : 𝓞 E) : ∃ m : ℤ, a - m ∈ P ^ k := by
  first
  | exact @_root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow
  | exact _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow
  | (apply _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow ..)

/- English proof (translation)
Introduce `h`. Set `st : 𝓞 I.E →+* 𝓞 I.E` to `RingOfIntegers.mapRingHom (starRingEnd I.E)`. Establish `hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E)` using `fun a => rfl`. Establish `hmap : v.asIdeal.map st ≤ v.asIdeal` using `Ideal.map_le_iff_le_comap.2 fun a ha => (h a (st a) (hst a)).1 ha`. Establish `hfix : ∀ a, st a = a` using `fun a => by`.

Establish `hall : ∀ k, st a - a ∈ v.asIdeal ^ k` using `fun k => by`. Take `⟨m, hm'⟩` from `exists_int_sub_mem_pow hp v.asIdeal v.isMaximal hm hN h2 k a`. Establish `h3 : st (a - m) ∈ v.asIdeal ^ k`. Use `Ideal.mem_map_of_mem st hm'` as an intermediate fact. Rewrite `this` using `[Ideal.map_pow]`.

Conclude with `Ideal.pow_right_mono hmap k this`. Rewrite `h3` using `[map_sub, map_intCast]`. Simplify using `using sub_mem h3 hm'`. Use `Ideal.iInf_pow_eq_bot_of_isDomain v.asIdeal v.isPrime.ne_top` as an intermediate fact. Establish `h4 : st a - a ∈ (⊥ : Ideal (𝓞 I.E))` using `this ▸ Ideal.mem_iInf.2 hall`.

Conclude with `sub_eq_zero.1 h4`. Establish `hfixE : ∀ x : I.E, star x = x` using `fun x => by`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 I.E) x`. Establish `ha : star (algebraMap (𝓞 I.E) I.E a) = algebraMap (𝓞 I.E) I.E a`. Rewrite using `[← hst a, hfix]`.

Establish `hb : star (algebraMap (𝓞 I.E) I.E b) = algebraMap (𝓞 I.E) I.E b`. Rewrite using `[← hst b, hfix]`. Rewrite using `[star_div₀, ha, hb]`. Establish `hsurj : Function.Surjective (algebraMap I.F I.E)` using `fun x => (I.cm.fixed x).1 (hfixE x)`. Establish `h1 : Module.finrank I.F I.E = 1` using `Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap I.F I.E).injective, hsurj⟩`.

Use `I.cm.deg2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem not_isConj_self (I : AutInst) {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 I.E))
    (hm : (p : 𝓞 I.E) ∈ v.asIdeal) (hN : Ideal.absNorm v.asIdeal = p) (h2 : (p : 𝓞 I.E) ∉ v.asIdeal ^ 2) :
    ¬ IsConj I v v := by
  intro h
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hmap : v.asIdeal.map st ≤ v.asIdeal :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (h a (st a) (hst a)).1 ha
  have hfix : ∀ a, st a = a := fun a => by
    have hall : ∀ k, st a - a ∈ v.asIdeal ^ k := fun k => by
      obtain ⟨m, hm'⟩ := exists_int_sub_mem_pow hp v.asIdeal v.isMaximal hm hN h2 k a
      have h3 : st (a - m) ∈ v.asIdeal ^ k := by
        have := Ideal.mem_map_of_mem st hm'
        rw [Ideal.map_pow] at this
        exact Ideal.pow_right_mono hmap k this
      rw [map_sub, map_intCast] at h3
      simpa using sub_mem h3 hm'
    have := Ideal.iInf_pow_eq_bot_of_isDomain v.asIdeal v.isPrime.ne_top
    have h4 : st a - a ∈ (⊥ : Ideal (𝓞 I.E)) := this ▸ Ideal.mem_iInf.2 hall
    exact sub_eq_zero.1 h4
  have hfixE : ∀ x : I.E, star x = x := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 I.E) x
    have ha : star (algebraMap (𝓞 I.E) I.E a) = algebraMap (𝓞 I.E) I.E a := by
      rw [← hst a, hfix]
    have hb : star (algebraMap (𝓞 I.E) I.E b) = algebraMap (𝓞 I.E) I.E b := by
      rw [← hst b, hfix]
    rw [star_div₀, ha, hb]
  have hsurj : Function.Surjective (algebraMap I.F I.E) := fun x => (I.cm.fixed x).1 (hfixE x)
  have h1 : Module.finrank I.F I.E = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap I.F I.E).injective, hsurj⟩
  have := I.cm.deg2
  omega

/- English proof (translation)
Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Establish `hp0 : Ideal.span {(p : ℤ)} ≠ ⊥`. Simplify `hp.ne_zero` using `[Ideal.span_singleton_eq_bot]`. Establish `hpr : (Ideal.span {(p : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ`. Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `hpr.isMaximal hp0`.

Rewrite using `[← Set.ncard_image_of_injective _ (fun _ _ h => HeightOneSpectrum.ext h : Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 E) → _))]`. Use `congr 1`. Use extensionality with `P`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`.

Use `⟨v.isPrime, ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]`. Conclude with `hv`. Introduce and unpack `⟨hP, hl⟩`. Use `⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩, ?_, rfl⟩` and prove the remaining obligations.

Establish `: (p : ℤ) ∈ P.under ℤ` using `hl.over ▸ Ideal.mem_span_singleton_self _`. Rewrite `this` using `[Ideal.mem_comap, map_natCast]`. Conclude with `this`.
-/
theorem ncard_places_eq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 E) | (p : 𝓞 E) ∈ v.asIdeal}.ncard =
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hpr.isMaximal hp0
  rw [← Set.ncard_image_of_injective _ (fun _ _ h => HeightOneSpectrum.ext h :
    Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 E) → _))]
  congr 1
  ext P
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hv
  · rintro ⟨hP, hl⟩
    refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩, ?_, rfl⟩
    have : (p : ℤ) ∈ P.under ℤ := hl.over ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at this
    exact this

/- English proof (translation)
Introduce `I g hg hne h`. Establish `hdeg : Module.finrank ℚ I.E = 2 * I.f`. Rewrite using `[← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2, AutInst.f, mul_comm]`. Use `GlobalTheory.Mem.RowsBundle.isChoice_of_card I g hg hne (fun k v hv => ?_) Module.finrank_pos fun k => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `h k v.asIdeal v.isMaximal hv`.

Conclude with `⟨h1, h2, not_isConj_self I (hg k) v hv h1 h2⟩`. Rewrite using `[ncard_places_eq (hg k), GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq I.E (g k) (hg k) (h k), hdeg]`.
-/
theorem exists_isChoice_and_isChoice_of_card : ∀ (I : AutInst) (g : Fin 2 → ℕ), (∀ k, (g k).Prime) → g 0 ≠ g 1 → (∀ k (P : Ideal (𝓞 I.E)), P.IsMaximal → ((g k : ℕ) : 𝓞 I.E) ∈ P → Ideal.absNorm P = g k ∧ ((g k : ℕ) : 𝓞 I.E) ∉ P ^ 2) → (∃ w : ∀ _ : Fin 2, Fin I.f → HeightOneSpectrum (𝓞 I.E), IsChoice I g (fun _ => Fin I.f) w) ∧ ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)), (∀ k, Fintype.card (Pl k) = I.f) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) → (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
  intro I g hg hne h
  have hdeg : Module.finrank ℚ I.E = 2 * I.f := by
    rw [← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2, AutInst.f, mul_comm]
  refine GlobalTheory.Mem.RowsBundle.isChoice_of_card I g hg hne (fun k v hv => ?_) Module.finrank_pos fun k => ?_
  · obtain ⟨h1, h2⟩ := h k v.asIdeal v.isMaximal hv
    exact ⟨h1, h2, not_isConj_self I (hg k) v hv h1 h2⟩
  · rw [ncard_places_eq (hg k),
      GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq I.E (g k) (hg k) (h k), hdeg]

end GlobalTheory.SplitChoice
