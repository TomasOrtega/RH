import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox

open NumberField IsDedekindDomain

namespace GlobalTheory.WeakApprox

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Take `⟨y, hy⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v : HeightOneSpectrum (𝓞 L) => v.asIdeal) (fun v => multiplicity v.asIdeal (Ideal.span {t v}) + 1) (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => t v)`. Use `⟨y, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h1` using `(v.intValuation_le_pow_iff_mem _ _).2 (hy v hv)`. Establish `h2` using `v.intValuation_eq_exp_neg_multiplicity (ht v hv)`. Establish `e1 : ((y : L) - (t v : L)) = algebraMap (𝓞 L) L (y - t v)` using `by simp`.

Establish `e2 : ((t v : L)) = algebraMap (𝓞 L) L (t v)` using `rfl`. Rewrite using `[e1, e2, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, h2, ← WithZero.exp_add]`. Use `h1.trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_int_approx (S : Finset (HeightOneSpectrum (𝓞 L))) (t : HeightOneSpectrum (𝓞 L) → 𝓞 L)
    (ht : ∀ v ∈ S, t v ≠ 0) : ∃ y : 𝓞 L, ∀ v ∈ S,
      v.valuation L ((y : L) - (t v : L)) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (t v : L) := by
  classical
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun v : HeightOneSpectrum (𝓞 L) => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {t v}) + 1)
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => t v)
  refine ⟨y, fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v hv)
  have h2 := v.intValuation_eq_exp_neg_multiplicity (ht v hv)
  have e1 : ((y : L) - (t v : L)) = algebraMap (𝓞 L) L (y - t v) := by simp
  have e2 : ((t v : L)) = algebraMap (𝓞 L) L (t v) := rfl
  rw [e1, e2, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    h2, ← WithZero.exp_add]
  refine h1.trans (le_of_eq ?_)
  congr 1
  push_cast
  ring

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.algebraMap_adicCompletion]`. Simplify using the standard rewrite rules.
-/
private lemma valued_algebraMap_adicCompletion_eq_valuation (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (a : K) :
    Valued.v (algebraMap K (P.adicCompletion K) a) = P.valuation K a := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  simp

/- English proof (translation)
Establish `h : WithZero.exp (-1 : ℤ) < 1`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions. Simplify using `using mul_lt_mul_of_pos_right h (zero_lt_iff.2 hx)`.
-/
private lemma exp_neg_one_mul_lt_of_ne_zero {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) : WithZero.exp (-1 : ℤ) * x < x := by
  have h : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  simpa using mul_lt_mul_of_pos_right h (zero_lt_iff.2 hx)

/- English proof (translation)
Introduce `L _ _ R z hz`. Establish `happ : ∀ P, ∃ a : L, P ∈ R → Valued.v (z P - algebraMap L (P.adicCompletion L) a) < WithZero.exp (-1 : ℤ) * Valued.v (z P)`. Introduce `P`. Distinguish the cases in `hP : P ∈ R`. Take `⟨π, hπ⟩` from `P.valuation_exists_uniformizer L`.

Establish `hπ0 : π ≠ 0`. Introduce `h`. Rewrite `hπ` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hπ.symm`. Establish `hc : algebraMap L (P.adicCompletion L) π * z P ≠ 0` using `mul_ne_zero ((map_ne_zero _).2 hπ0) (hz P hP)`.

Take `⟨a, ha⟩` from `GlobalTheory.adicCompletion_exists_approx_lt L P (z P) _ hc`. Use `⟨a, fun _ => ?_⟩` and prove the remaining obligations. Rewrite `ha` using `[map_mul, valued_algebraMap_adicCompletion_eq_valuation, hπ]`. Then use the resulting hypothesis. Conclude with `⟨0, fun h => absurd h hP⟩`. Use `choose a ha using happ`.

Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 L)) R a`. Establish `hint : ∀ P, ∃ r : 𝓞 L, P ∈ R → algebraMap (𝓞 L) L r = (d : 𝓞 L) • a P`. Introduce `P`. Distinguish the cases in `hP : P ∈ R`. Take `⟨r, hr⟩` from `hd P hP`.

Conclude with `⟨r, fun _ => hr⟩`. Conclude with `⟨0, fun h => absurd h hP⟩`. Use `choose t ht using hint`. Use `set D : L := algebraMap (𝓞 L) L d with hDdef`. Establish `hD : D ≠ 0` using `(map_ne_zero_iff (algebraMap (𝓞 L) L) (IsFractionRing.injective (𝓞 L) L)).2 (nonZeroDivisors.coe_ne_zero d)`.

Establish `htP : ∀ P ∈ R, algebraMap (𝓞 L) L (t P) = D * a P` using `fun P hP => by`. Rewrite using `[ht P hP, Algebra.smul_def]`. Establish `ha0 : ∀ P ∈ R, a P ≠ 0`. Introduce `P hP h`. Establish `h'` using `ha P hP`.

Rewrite `h'` using `[h, map_zero, sub_zero]`. Conclude with `lt_irrefl _ (h'.trans (exp_neg_one_mul_lt_of_ne_zero ((Valuation.ne_zero_iff _).2 (hz P hP))))`. Establish `ht0 : ∀ P ∈ R, t P ≠ 0`. Introduce `P hP h`. Establish `h'` using `htP P hP`.

Rewrite `h'` using `[h, map_zero]`. Conclude with `mul_ne_zero hD (ha0 P hP) h'.symm`. Take `⟨y, hy⟩` from `exists_int_approx (L := L) R t ht0`. Establish `hy' : ∀ P ∈ R, P.valuation L (algebraMap (𝓞 L) L y - algebraMap (𝓞 L) L (t P)) ≤ WithZero.exp (-1 : ℤ) * P.valuation L (algebraMap (𝓞 L) L (t P))` using `hy`. Break down `R.eq_empty_or_nonempty with hR | ⟨P0, hP0⟩` into its components or cases.

Conclude with `⟨1, by simp [hR]⟩`. Establish `hy0 : algebraMap (𝓞 L) L y ≠ 0`. Introduce `h`. Establish `h'` using `hy' P0 hP0`. Rewrite `h'` using `[h, zero_sub, Valuation.map_neg]`.

Establish `hv : P0.valuation L (algebraMap (𝓞 L) L (t P0)) ≠ 0` using `(Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 (ht0 P0 hP0))`. Conclude with `lt_irrefl _ (h'.trans_lt (exp_neg_one_mul_lt_of_ne_zero hv))`. Use `⟨Units.mk0 (algebraMap (𝓞 L) L y / D) (div_ne_zero hy0 hD), fun P hP => ?_⟩` and prove the remaining obligations. Simplify using `only [Units.val_mk0]`. Establish `hA` using `ha P hP`.

Establish `hza : Valued.v (algebraMap L (P.adicCompletion L) (a P)) = Valued.v (z P)`. Apply `Valuation.map_eq_of_sub_lt` to reduce the goal to its premises. Rewrite using `[Valuation.map_sub_swap]`. Conclude with `hA.trans (exp_neg_one_mul_lt_of_ne_zero ((Valuation.ne_zero_iff _).2 (hz P hP)))`. Establish `hsplit : z P - algebraMap L (P.adicCompletion L) (algebraMap (𝓞 L) L y / D) = (z P - algebraMap L _ (a P)) + algebraMap L _ (a P - algebraMap (𝓞 L) L y / D)`.

Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`. Use `Valuation.map_add_le _ hA.le ?_` and prove the remaining obligations. Rewrite using `[valued_algebraMap_adicCompletion_eq_valuation, ← hza, valued_algebraMap_adicCompletion_eq_valuation]`.

Establish `e : a P - algebraMap (𝓞 L) L y / D = (algebraMap (𝓞 L) L (t P) - algebraMap (𝓞 L) L y) / D`. Rewrite using `[htP P hP]`. Clear the denominators using the available nonvanishing facts. Establish `hDv : P.valuation L D ≠ 0` using `(Valuation.ne_zero_iff _).2 hD`. Rewrite using `[e, map_div₀, Valuation.map_sub_swap, div_le_iff₀ (zero_lt_iff.2 hDv)]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_units_approx :
    ∀ (L : Type) [Field L] [NumberField L] (R : Finset (HeightOneSpectrum (𝓞 L)))
      (z : ∀ P : HeightOneSpectrum (𝓞 L), P.adicCompletion L), (∀ P ∈ R, z P ≠ 0) →
      ∃ k : Lˣ, ∀ P ∈ R, Valued.v (z P - algebraMap L (P.adicCompletion L) (k : L)) ≤
        WithZero.exp (-1 : ℤ) * Valued.v (z P) := by
  intro L _ _ R z hz
  classical

  have happ : ∀ P, ∃ a : L, P ∈ R →
      Valued.v (z P - algebraMap L (P.adicCompletion L) a) < WithZero.exp (-1 : ℤ) * Valued.v (z P) := by
    intro P
    by_cases hP : P ∈ R
    · obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer L
      have hπ0 : π ≠ 0 := by
        intro h
        rw [h, map_zero] at hπ
        exact WithZero.exp_ne_zero hπ.symm
      have hc : algebraMap L (P.adicCompletion L) π * z P ≠ 0 :=
        mul_ne_zero ((map_ne_zero _).2 hπ0) (hz P hP)
      obtain ⟨a, ha⟩ := GlobalTheory.adicCompletion_exists_approx_lt L P (z P) _ hc
      refine ⟨a, fun _ => ?_⟩
      rwa [map_mul, valued_algebraMap_adicCompletion_eq_valuation, hπ] at ha
    · exact ⟨0, fun h => absurd h hP⟩
  choose a ha using happ

  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 L)) R a
  have hint : ∀ P, ∃ r : 𝓞 L, P ∈ R → algebraMap (𝓞 L) L r = (d : 𝓞 L) • a P := by
    intro P
    by_cases hP : P ∈ R
    · obtain ⟨r, hr⟩ := hd P hP
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose t ht using hint
  set D : L := algebraMap (𝓞 L) L d with hDdef
  have hD : D ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 L) L) (IsFractionRing.injective (𝓞 L) L)).2
      (nonZeroDivisors.coe_ne_zero d)
  have htP : ∀ P ∈ R, algebraMap (𝓞 L) L (t P) = D * a P := fun P hP => by
    rw [ht P hP, Algebra.smul_def]
  have ha0 : ∀ P ∈ R, a P ≠ 0 := by
    intro P hP h
    have h' := ha P hP
    rw [h, map_zero, sub_zero] at h'
    exact lt_irrefl _ (h'.trans (exp_neg_one_mul_lt_of_ne_zero ((Valuation.ne_zero_iff _).2 (hz P hP))))
  have ht0 : ∀ P ∈ R, t P ≠ 0 := by
    intro P hP h
    have h' := htP P hP
    rw [h, map_zero] at h'
    exact mul_ne_zero hD (ha0 P hP) h'.symm

  obtain ⟨y, hy⟩ := exists_int_approx (L := L) R t ht0
  have hy' : ∀ P ∈ R, P.valuation L (algebraMap (𝓞 L) L y - algebraMap (𝓞 L) L (t P)) ≤
      WithZero.exp (-1 : ℤ) * P.valuation L (algebraMap (𝓞 L) L (t P)) := hy
  rcases R.eq_empty_or_nonempty with hR | ⟨P0, hP0⟩
  · exact ⟨1, by simp [hR]⟩
  have hy0 : algebraMap (𝓞 L) L y ≠ 0 := by
    intro h
    have h' := hy' P0 hP0
    rw [h, zero_sub, Valuation.map_neg] at h'
    have hv : P0.valuation L (algebraMap (𝓞 L) L (t P0)) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 (ht0 P0 hP0))
    exact lt_irrefl _ (h'.trans_lt (exp_neg_one_mul_lt_of_ne_zero hv))
  refine ⟨Units.mk0 (algebraMap (𝓞 L) L y / D) (div_ne_zero hy0 hD), fun P hP => ?_⟩
  simp only [Units.val_mk0]
  have hA := ha P hP
  have hza : Valued.v (algebraMap L (P.adicCompletion L) (a P)) = Valued.v (z P) := by
    apply Valuation.map_eq_of_sub_lt
    rw [Valuation.map_sub_swap]
    exact hA.trans (exp_neg_one_mul_lt_of_ne_zero ((Valuation.ne_zero_iff _).2 (hz P hP)))
  have hsplit : z P - algebraMap L (P.adicCompletion L) (algebraMap (𝓞 L) L y / D) =
      (z P - algebraMap L _ (a P)) + algebraMap L _ (a P - algebraMap (𝓞 L) L y / D) := by
    rw [map_sub]; ring
  rw [hsplit]
  refine Valuation.map_add_le _ hA.le ?_
  rw [valued_algebraMap_adicCompletion_eq_valuation, ← hza, valued_algebraMap_adicCompletion_eq_valuation]
  have e : a P - algebraMap (𝓞 L) L y / D =
      (algebraMap (𝓞 L) L (t P) - algebraMap (𝓞 L) L y) / D := by
    rw [htP P hP]; field_simp
  have hDv : P.valuation L D ≠ 0 := (Valuation.ne_zero_iff _).2 hD
  rw [e, map_div₀, Valuation.map_sub_swap, div_le_iff₀ (zero_lt_iff.2 hDv)]
  calc _ ≤ WithZero.exp (-1 : ℤ) * P.valuation L (algebraMap (𝓞 L) L (t P)) := hy' P hP
    _ = _ := by rw [htP P hP, map_mul]; ac_rfl

end GlobalTheory.WeakApprox
