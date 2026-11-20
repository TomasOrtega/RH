import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef

open IsDedekindDomain ValuativeRel nonZeroDivisors

namespace UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset

/- English proof (translation)
Establish `hv : valuation K c ≠ 0` using `(Valuation.ne_zero_iff _).2 hc`. Establish `hn : {z | valuation K (z - b) < (Units.mk0 _ hv : (ValueGroupWithZero K)ˣ)} ∈ nhds b` using `IsValuativeTopology.mem_nhds_iff'.2 ⟨_, subset_rfl⟩`. Take `⟨a, ha⟩` from `hd.mem_nhds hn`. Conclude with `⟨a, le_of_lt ha⟩`.
-/
private lemma approx_one {F K : Type*} [Field F] [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsValuativeTopology K] (ι : F →+* K) (hd : DenseRange ι) (b c : K) (hc : c ≠ 0) :
    ∃ a : F, valuation K (ι a - b) ≤ valuation K c := by
  have hv : valuation K c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  have hn : {z | valuation K (z - b) < (Units.mk0 _ hv : (ValueGroupWithZero K)ˣ)} ∈ nhds b :=
    IsValuativeTopology.mem_nhds_iff'.2 ⟨_, subset_rfl⟩
  obtain ⟨a, ha⟩ := hd.mem_nhds hn
  exact ⟨a, le_of_lt ha⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, by rw [HeightOneSpectrum.valuation_of_algebraMap, q.intValuation_if_neg hr]⟩`.
-/
private lemma val_eq_exp {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (q : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    ∃ n : ℕ, q.valuation K (algebraMap R K r) = WithZero.exp (-(n : ℤ)) :=
  ⟨_, by rw [HeightOneSpectrum.valuation_of_algebraMap, q.intValuation_if_neg hr]⟩

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(q.intValuation_le_pow_iff_mem r n).2 h`.
-/
private lemma val_le_of_mem {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (q : HeightOneSpectrum R) {r : R} {n : ℕ} (h : r ∈ q.asIdeal ^ n) :
    q.valuation K (algebraMap R K r) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (q.intValuation_le_pow_iff_mem r n).2 h

/- English proof (translation)
Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples R⁰ S a`. Establish `hd0 : (d : R) ≠ 0` using `nonZeroDivisors.ne_zero d.2`. Establish `hdK : algebraMap R K (d : R) ≠ 0`. Simplify using `using hd0`. Establish `hcd : c * (d : R) ≠ 0` using `mul_ne_zero hc hd0`.

Use `choose x hx using fun i : S => hd i.1 i.2`. Use `choose m hm using fun q : HeightOneSpectrum R => val_eq_exp (K := K) q hcd`. Use `choose m' hm' using fun q : HeightOneSpectrum R => val_eq_exp (K := K) q hd0`. Establish `hI : (Ideal.span {(d : R)} : Ideal R) ≠ 0`. Simplify using `using hd0`.

Set `T : Finset (HeightOneSpectrum R)` to `S ∪ (Ideal.finite_factors hI).toFinset`. Set `e : HeightOneSpectrum R → ℕ` to `fun q => if q ∈ S then m q else m' q`. Set `t : T → R` to `fun i => if h : i.1 ∈ S then x ⟨i.1, h⟩ else 0`. Take `⟨y, hy⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun q : HeightOneSpectrum R => q.asIdeal) e (fun q _ => q.prime) (fun q _ q' _ hne h => hne (HeightOneSpectrum.ext h)) t`. Use `⟨algebraMap R K y / algebraMap R K (d : R), fun p hp => ?_, fun p hp => ?_⟩` and prove the remaining obligations.

Establish `hpT : p ∈ T` using `Finset.mem_union_left _ hp`. Establish `h1` using `hy p hpT`. Establish `ht : t ⟨p, hpT⟩ = x ⟨p, hp⟩` using `by simp [t, hp]`. Establish `he : e p = m p` using `by simp [e, hp]`. Rewrite `h1` using `[ht, he]`.

Establish `h2` using `val_le_of_mem (K := K) p h1`. Rewrite `h2` using `[← hm p, map_mul, map_mul, map_sub]`. Establish `hxa : algebraMap R K (x ⟨p, hp⟩) = algebraMap R K (d : R) * a p`. Rewrite using `[hx ⟨p, hp⟩, Algebra.smul_def]`. Establish `hf : algebraMap R K y / algebraMap R K (d : R) - a p = (algebraMap R K y - algebraMap R K (x ⟨p, hp⟩)) / algebraMap R K (d : R)`.

Rewrite using `[hxa]`. Clear the denominators using the available nonvanishing facts. Establish `hvd : p.valuation K (algebraMap R K (d : R)) ≠ 0` using `(Valuation.ne_zero_iff _).2 hdK`. Rewrite using `[hf, map_div₀]`. Conclude with `div_le_of_le_mul₀ (zero_le') (zero_le') h2`.

Rewrite using `[map_div₀]`. Establish `hvd : p.valuation K (algebraMap R K (d : R)) ≠ 0` using `(Valuation.ne_zero_iff _).2 hdK`. Distinguish the cases in `hpT : p ∈ T`. Establish `h1` using `hy p hpT`. Establish `ht : t ⟨p, hpT⟩ = 0` using `by simp [t, hp]`.

Establish `he : e p = m' p` using `by simp [e, hp]`. Rewrite `h1` using `[ht, he, sub_zero]`. Establish `h2` using `val_le_of_mem (K := K) p h1`. Rewrite `h2` using `[← hm' p]`. Conclude with `div_le_one_of_le₀ h2 zero_le'`.

Establish `hnd : ¬ (p.asIdeal ∣ Ideal.span {(d : R)})`. Introduce `h`. Conclude with `hpT (Finset.mem_union_right _ (by simpa using h))`. Establish `hmem : (d : R) ∉ p.asIdeal`. Introduce `h`.

Conclude with `hnd (Ideal.dvd_span_singleton.2 h)`. Establish `hone : p.valuation K (algebraMap R K (d : R)) = 1` using `le_antisymm (p.valuation_le_one _) (not_lt.1 (fun h => hmem ((p.valuation_lt_one_iff_mem _).1 h)))`. Rewrite using `[hone, div_one]`. Conclude with `p.valuation_le_one _`.
-/
private lemma core {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (S : Finset (HeightOneSpectrum R)) (c : R) (hc : c ≠ 0)
    (a : HeightOneSpectrum R → K) :
    ∃ f : K, (∀ p ∈ S, p.valuation K (f - a p) ≤ p.valuation K (algebraMap R K c)) ∧
      ∀ p ∉ S, p.valuation K f ≤ 1 := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples R⁰ S a
  have hd0 : (d : R) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hdK : algebraMap R K (d : R) ≠ 0 := by
    simpa using hd0
  have hcd : c * (d : R) ≠ 0 := mul_ne_zero hc hd0
  choose x hx using fun i : S => hd i.1 i.2
  choose m hm using fun q : HeightOneSpectrum R => val_eq_exp (K := K) q hcd
  choose m' hm' using fun q : HeightOneSpectrum R => val_eq_exp (K := K) q hd0
  have hI : (Ideal.span {(d : R)} : Ideal R) ≠ 0 := by
    simpa using hd0
  let T : Finset (HeightOneSpectrum R) := S ∪ (Ideal.finite_factors hI).toFinset
  let e : HeightOneSpectrum R → ℕ := fun q => if q ∈ S then m q else m' q
  let t : T → R := fun i => if h : i.1 ∈ S then x ⟨i.1, h⟩ else 0
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun q : HeightOneSpectrum R => q.asIdeal) e (fun q _ => q.prime)
    (fun q _ q' _ hne h => hne (HeightOneSpectrum.ext h)) t
  refine ⟨algebraMap R K y / algebraMap R K (d : R), fun p hp => ?_, fun p hp => ?_⟩
  · have hpT : p ∈ T := Finset.mem_union_left _ hp
    have h1 := hy p hpT
    have ht : t ⟨p, hpT⟩ = x ⟨p, hp⟩ := by simp [t, hp]
    have he : e p = m p := by simp [e, hp]
    rw [ht, he] at h1
    have h2 := val_le_of_mem (K := K) p h1
    rw [← hm p, map_mul, map_mul, map_sub] at h2
    have hxa : algebraMap R K (x ⟨p, hp⟩) = algebraMap R K (d : R) * a p := by
      rw [hx ⟨p, hp⟩, Algebra.smul_def]
    have hf : algebraMap R K y / algebraMap R K (d : R) - a p =
        (algebraMap R K y - algebraMap R K (x ⟨p, hp⟩)) / algebraMap R K (d : R) := by
      rw [hxa]; field_simp
    have hvd : p.valuation K (algebraMap R K (d : R)) ≠ 0 := (Valuation.ne_zero_iff _).2 hdK
    rw [hf, map_div₀]
    exact div_le_of_le_mul₀ (zero_le') (zero_le') h2
  · rw [map_div₀]
    have hvd : p.valuation K (algebraMap R K (d : R)) ≠ 0 := (Valuation.ne_zero_iff _).2 hdK
    by_cases hpT : p ∈ T
    · have h1 := hy p hpT
      have ht : t ⟨p, hpT⟩ = 0 := by simp [t, hp]
      have he : e p = m' p := by simp [e, hp]
      rw [ht, he, sub_zero] at h1
      have h2 := val_le_of_mem (K := K) p h1
      rw [← hm' p] at h2
      exact div_le_one_of_le₀ h2 zero_le'
    · have hnd : ¬ (p.asIdeal ∣ Ideal.span {(d : R)}) := by
        intro h
        exact hpT (Finset.mem_union_right _ (by simpa using h))
      have hmem : (d : R) ∉ p.asIdeal := by
        intro h
        exact hnd (Ideal.dvd_span_singleton.2 h)
      have hone : p.valuation K (algebraMap R K (d : R)) = 1 :=
        le_antisymm (p.valuation_le_one _)
          (not_lt.1 (fun h => hmem ((p.valuation_lt_one_iff_mem _).1 h)))
      rw [hone, div_one]
      exact p.valuation_le_one _

end UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig A S c hc b`. Establish `hc' : ∀ p, (A p).ιF (algebraMap (NumberField.RingOfIntegers F) F c) ≠ 0` using `fun p => by`. Simplify using `using hc`. Establish `happ : ∀ p, ∃ a : F, valuation (A p).Fp ((A p).ιF a - b p) ≤ valuation (A p).Fp ((A p).ιF (algebraMap (NumberField.RingOfIntegers F) F c))` using `fun p => by haveI := (A p).lf`. Conclude with `UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset.approx_one (A p).ιF (A p).dense (b p) _ (hc' p)`.

Use `choose a ha using happ`. Take `⟨f, hf1, hf2⟩` from `UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset.core (K := F) S c hc a`. Use `⟨f, fun p hp => ?_, fun p hp => ?_⟩` and prove the remaining obligations. Establish `h1` using `((A p).val _ _).2 (hf1 p hp)`. Rewrite `h1` using `[(valuation (A p).Fp).vle_iff_le, map_sub]`.

Establish `h2 : (A p).ιF f - b p = ((A p).ιF f - (A p).ιF (a p)) + ((A p).ιF (a p) - b p)` using `by ring`. Express the relevant statement in the definitionally equal form `valuation (A p).Fp ((A p).ιF f - b p) ≤ valuation (A p).Fp ((A p).ιF (algebraMap (NumberField.RingOfIntegers F) F c))`. Rewrite using `[h2]`. Conclude with `Valuation.map_add_le _ h1 (ha p)`. Establish `h1 : p.valuation F f ≤ p.valuation F 1` using `by simpa using hf2 p hp`.

Establish `h2` using `((A p).val _ _).2 h1`. Rewrite `h2` using `[(valuation (A p).Fp).vle_iff_le, map_one, map_one]`. Conclude with `h2`.
-/
theorem UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset.approxF :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {sig : E →ₐ[F] E}
      (A : (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → Formalism.MainNotions.S.Loc.LocAt F E sig p)
      (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (c : NumberField.RingOfIntegers F),
      c ≠ (0 : NumberField.RingOfIntegers F) →
        ∀ (b : (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → (A p).Fp),
          ∃ (f : F),
            (∀ p ∈ S,
                (ValuativeRel.valuation (A p).Fp : (A p).Fp → ValuativeRel.ValueGroupWithZero (A p).Fp)
                    (((A p).ιF : F → (A p).Fp) f - b p) ≤
                  (ValuativeRel.valuation (A p).Fp : (A p).Fp → ValuativeRel.ValueGroupWithZero (A p).Fp)
                    (((A p).ιF : F → (A p).Fp)
                      ((Algebra.algebraMap (NumberField.RingOfIntegers F) F : NumberField.RingOfIntegers F → F) c))) ∧
              ∀ p ∉ S, ((A p).ιF : F → (A p).Fp) f ∈ (ValuativeRel.valuation (A p).Fp).integer := by
  intro F E _ _ _ _ _ sig A S c hc b
  have hc' : ∀ p, (A p).ιF (algebraMap (NumberField.RingOfIntegers F) F c) ≠ 0 := fun p => by
    simpa using hc
  have happ : ∀ p, ∃ a : F, valuation (A p).Fp ((A p).ιF a - b p) ≤
      valuation (A p).Fp ((A p).ιF (algebraMap (NumberField.RingOfIntegers F) F c)) := fun p => by
    haveI := (A p).lf
    exact UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset.approx_one (A p).ιF (A p).dense (b p) _ (hc' p)
  choose a ha using happ
  obtain ⟨f, hf1, hf2⟩ := UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset.core (K := F) S c hc a
  refine ⟨f, fun p hp => ?_, fun p hp => ?_⟩
  · have h1 := ((A p).val _ _).2 (hf1 p hp)
    rw [(valuation (A p).Fp).vle_iff_le, map_sub] at h1
    have h2 : (A p).ιF f - b p = ((A p).ιF f - (A p).ιF (a p)) + ((A p).ιF (a p) - b p) := by ring
    change valuation (A p).Fp ((A p).ιF f - b p) ≤
      valuation (A p).Fp ((A p).ιF (algebraMap (NumberField.RingOfIntegers F) F c))
    rw [h2]
    exact Valuation.map_add_le _ h1 (ha p)
  · have h1 : p.valuation F f ≤ p.valuation F 1 := by simpa using hf2 p hp
    have h2 := ((A p).val _ _).2 h1
    rw [(valuation (A p).Fp).vle_iff_le, map_one, map_one] at h2
    exact h2
