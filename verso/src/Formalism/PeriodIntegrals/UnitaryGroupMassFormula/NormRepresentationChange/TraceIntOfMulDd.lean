import Mathlib
import Formalism.PeriodIntegrals.PairValDefs
import Formalism.PeriodIntegrals.NormRepChange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `show D.host.g 0 * D.host.g 1 ≠ 0`. Conclude with `mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero`.
-/
theorem gS_ne_zero (D : D7) : gS D ≠ 0 := by
  show D.host.g 0 * D.host.g 1 ≠ 0
  exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_algebraMap_OF (D : D7) (δ : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) δ : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (δ : D.host.F) := rfl

/- English proof (translation)
Establish `ha : ∀ δ ∈ differentIdeal ℤ (𝓞 D.host.F), ∃ a : 𝓞 D.host.F, (a : D.host.F) = (δ : D.host.F) * Algebra.trace D.host.F D.host.E x`. Introduce `δ hδ`. Establish `hmem : algebraMap D.host.F D.host.E (δ : D.host.F) ∈ ddS D`. Unfold `ddS`. Rewrite using `[FractionalIdeal.mem_coeIdeal]`.

Conclude with `⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) δ, Ideal.mem_map_of_mem _ hδ, coe_algebraMap_OF D δ⟩`. Take `⟨o, ho⟩` from `hx _ hmem`. Establish `htr : Algebra.trace D.host.F D.host.E (o : D.host.E) = (δ : D.host.F) * Algebra.trace D.host.F D.host.E x`. Rewrite using `[ho, mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]`. Establish `hint : IsIntegral ℤ (Algebra.trace D.host.F D.host.E (o : D.host.E))` using `Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)`.

Rewrite `hint` using `[htr]`. Conclude with `⟨⟨_, hint⟩, rfl⟩`. Establish `hdual : Algebra.trace D.host.F D.host.E x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)`. Rewrite using `[← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)), ← coeIdeal_differentIdeal ℤ ℚ D.host.F, FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot)]`. Introduce `y hy`.

Take `⟨y', hy', rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).mp hy`. Take `⟨a, ha'⟩` from `ha y' hy'`. Rewrite using `[FractionalIdeal.mem_one_iff]`. Conclude with `⟨a, by rw [mul_comm]; exact ha'⟩`. Rewrite `hdual` using `[FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0)]`.

Take `⟨k, hk⟩` from `hdual 1 (FractionalIdeal.one_mem_one _)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `h1 : Algebra.traceForm ℚ D.host.F (Algebra.trace D.host.F D.host.E x) 1 = Algebra.trace ℚ D.host.F (Algebra.trace D.host.F D.host.E x)`. Rewrite using `[Algebra.traceForm_apply, mul_one]`. Rewrite using `[← Algebra.trace_trace (S := D.host.F), ← h1, ← hk]`.

Simplify using the standard rewrite rules.
-/
theorem trace_int_of_mul_dd (D : D7) (x : D.host.E)
    (hx : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * δ) :
    ∃ k : ℤ, Algebra.trace ℚ D.host.E x = k := by
  have ha : ∀ δ ∈ differentIdeal ℤ (𝓞 D.host.F),
      ∃ a : 𝓞 D.host.F, (a : D.host.F) = (δ : D.host.F) * Algebra.trace D.host.F D.host.E x := by
    intro δ hδ
    have hmem : algebraMap D.host.F D.host.E (δ : D.host.F) ∈ ddS D := by
      unfold ddS
      rw [FractionalIdeal.mem_coeIdeal]
      exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) δ, Ideal.mem_map_of_mem _ hδ, coe_algebraMap_OF D δ⟩
    obtain ⟨o, ho⟩ := hx _ hmem
    have htr : Algebra.trace D.host.F D.host.E (o : D.host.E) = (δ : D.host.F) * Algebra.trace D.host.F D.host.E x := by
      rw [ho, mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
    have hint : IsIntegral ℤ (Algebra.trace D.host.F D.host.E (o : D.host.E)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
    rw [htr] at hint
    exact ⟨⟨_, hint⟩, rfl⟩
  have hdual : Algebra.trace D.host.F D.host.E x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) := by
    rw [← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)), ← coeIdeal_differentIdeal ℤ ℚ D.host.F,
      FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot)]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    obtain ⟨a, ha'⟩ := ha y' hy'
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨a, by rw [mul_comm]; exact ha'⟩
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0)] at hdual
  obtain ⟨k, hk⟩ := hdual 1 (FractionalIdeal.one_mem_one _)
  refine ⟨k, ?_⟩
  have h1 : Algebra.traceForm ℚ D.host.F (Algebra.trace D.host.F D.host.E x) 1 = Algebra.trace ℚ D.host.F (Algebra.trace D.host.F D.host.E x) := by
    rw [Algebra.traceForm_apply, mul_one]
  rw [← Algebra.trace_trace (S := D.host.F), ← h1, ← hk]
  simp

/- English proof (translation)
Introduce `y hy hP`. Establish `hg0 : (gS D : D.host.E) ≠ 0` using `by exact_mod_cast gS_ne_zero D`. Establish `hint : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = y / (gS D : D.host.E) * δ`. Introduce `δ hδ`. Take `⟨o, ho⟩` from `hy δ hδ`.

Establish `hδint : ∃ d' : 𝓞 D.host.E, (d' : D.host.E) = δ`. Unfold `ddS at hδ`. Take `⟨d', -, hd'⟩` from `(FractionalIdeal.mem_coeIdeal _).mp hδ`. Conclude with `⟨d', hd'⟩`. Take `⟨d', rfl⟩` from `hδint`.

Establish `hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.valuation D.host.E (y / (gS D : D.host.E) * d') ≤ 1`. Introduce `P`. Distinguish the cases in `hPg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal`. Rewrite using `[map_mul]`. Conclude with `mul_le_one' (hP P hPg) (P.valuation_le_one d')`.

Establish `h1 : P.valuation D.host.E ((gS D : ℕ) : D.host.E) = 1`. Establish `h2` using `(P.valuation_eq_one_iff_notMem (K := D.host.E)).mpr hPg`. Simplify using `using h2`. Establish `e : y / (gS D : D.host.E) * d' = (y * d') / (gS D : D.host.E)` using `by ring`. Rewrite using `[e, map_div₀, h1, div_one, ← ho]`.

Conclude with `P.valuation_le_one o`. Take `⟨o', ho'⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (h := hval)`. Conclude with `⟨o', ho'⟩`. Take `⟨k, hk⟩` from `trace_int_of_mul_dd D (y / (gS D : D.host.E)) hint`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Establish `e : y = ((gS D : ℚ)) • (y / (gS D : D.host.E))`. Rewrite using `[Algebra.smul_def, map_natCast]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, LinearMap.map_smul, hk, smul_eq_mul]`.
-/
theorem stepTr (D : D7) : StepTr D := by
  intro y hy hP
  have hg0 : (gS D : D.host.E) ≠ 0 := by exact_mod_cast gS_ne_zero D
  have hint : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = y / (gS D : D.host.E) * δ := by
    intro δ hδ
    obtain ⟨o, ho⟩ := hy δ hδ
    have hδint : ∃ d' : 𝓞 D.host.E, (d' : D.host.E) = δ := by
      unfold ddS at hδ
      obtain ⟨d', -, hd'⟩ := (FractionalIdeal.mem_coeIdeal _).mp hδ
      exact ⟨d', hd'⟩
    obtain ⟨d', rfl⟩ := hδint
    have hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
        P.valuation D.host.E (y / (gS D : D.host.E) * d') ≤ 1 := by
      intro P
      by_cases hPg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
      · rw [map_mul]
        exact mul_le_one' (hP P hPg) (P.valuation_le_one d')
      · have h1 : P.valuation D.host.E ((gS D : ℕ) : D.host.E) = 1 := by
          have h2 := (P.valuation_eq_one_iff_notMem (K := D.host.E)).mpr hPg
          simpa using h2
        have e : y / (gS D : D.host.E) * d' = (y * d') / (gS D : D.host.E) := by ring
        rw [e, map_div₀, h1, div_one, ← ho]
        exact P.valuation_le_one o
    obtain ⟨o', ho'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (h := hval)
    exact ⟨o', ho'⟩
  obtain ⟨k, hk⟩ := trace_int_of_mul_dd D (y / (gS D : D.host.E)) hint
  refine ⟨k, ?_⟩
  have e : y = ((gS D : ℚ)) • (y / (gS D : D.host.E)) := by
    rw [Algebra.smul_def, map_natCast]
    field_simp
  rw [e, LinearMap.map_smul, hk, smul_eq_mul]

end PI.NRCW
