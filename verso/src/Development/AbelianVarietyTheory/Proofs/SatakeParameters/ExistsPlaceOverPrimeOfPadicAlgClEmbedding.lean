import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LocPlace

/- English proof (translation)
Establish `h : x ∈ (NormedField.valuation (K` using `C)).integer := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top`. Rewrite `h` using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`. Conclude with `h` after adjusting the coercions.
-/
theorem norm_le_one_of_isIntegral' {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

/- English proof (translation)
The claim follows from `norm_le_one_of_isIntegral' (map_isIntegral_int c x.isIntegral_coe)`.
-/
theorem norm_int_le_one (l : ℕ) [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' (map_isIntegral_int c x.isIntegral_coe)

/- English proof (translation)
Establish `h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[h, PadicAlgCl.norm_extends, Padic.norm_p]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)`.
-/
theorem norm_natCast_prime_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

def ballIdeal (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : Ideal (𝓞 E) where
  carrier := {x | ‖c (x : E)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    have e : ((a + b : 𝓞 E) : E) = (a : E) + (b : E) := by simp
    rw [e, map_add]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := by
    intro a b hb
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    push_cast
    rw [map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le_one l c a)) hb

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_ballIdeal (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : x ∈ ballIdeal l E c ↔ ‖c (x : E)‖ < 1 := Iff.rfl

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `h1 : (1 : 𝓞 E) ∈ ballIdeal l E c` using `h ▸ Submodule.mem_top`. Rewrite `h1` using `[mem_ballIdeal]`. Simplify using `at h1`.

Introduce `a b hab`. Rewrite `*` using `[mem_ballIdeal, mem_ballIdeal]`. Move the coercions through the operations in `at hab`. Rewrite `hab` using `[map_mul, norm_mul]`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `ha` using `le_antisymm (norm_int_le_one l c a) hcon.1`. Establish `hb` using `le_antisymm (norm_int_le_one l c b) hcon.2`. Rewrite `hab` using `[ha, hb]`. Evaluate the numerical expressions using `at hab`.
-/
theorem ballIdeal_isPrime (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : (ballIdeal l E c).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : 𝓞 E) ∈ ballIdeal l E c := h ▸ Submodule.mem_top
    rw [mem_ballIdeal] at h1
    simp at h1
  · intro a b hab
    rw [mem_ballIdeal, mem_ballIdeal] at *
    push_cast at hab
    rw [map_mul, norm_mul] at hab
    by_contra hcon
    push_neg at hcon
    have ha := le_antisymm (norm_int_le_one l c a) hcon.1
    have hb := le_antisymm (norm_int_le_one l c b) hcon.2
    rw [ha, hb] at hab
    norm_num at hab

/- English proof (translation)
Rewrite using `[mem_ballIdeal]`. Use `push_cast`. Rewrite using `[map_natCast]`. Conclude with `norm_natCast_prime_lt_one l`.
-/
theorem natCast_mem_ballIdeal (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : ((l : ℕ) : 𝓞 E) ∈ ballIdeal l E c := by
  rw [mem_ballIdeal]
  push_cast
  rw [map_natCast]
  exact norm_natCast_prime_lt_one l

/- English proof (translation)
Introduce `h`. Establish `h1` using `natCast_mem_ballIdeal l E c`. Rewrite `h1` using `[h, Ideal.mem_bot]`. Establish `h2 : ((l : ℕ) : E) = 0` using `by exact_mod_cast congrArg (fun y : 𝓞 E => (y : E)) h1`. Conclude with `(Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)`.
-/
theorem ballIdeal_ne_bot (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : ballIdeal l E c ≠ ⊥ := by
  intro h
  have h1 := natCast_mem_ballIdeal l E c
  rw [h, Ideal.mem_bot] at h1
  have h2 : ((l : ℕ) : E) = 0 := by exact_mod_cast congrArg (fun y : 𝓞 E => (y : E)) h1
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)

/- English proof (translation)
Introduce `l _ E _ _ c`. Use `⟨⟨ballIdeal l E c, ballIdeal_isPrime l E c, ballIdeal_ne_bot l E c⟩, ?_, fun x => Iff.rfl⟩` and prove the remaining obligations. Conclude with `natCast_mem_ballIdeal l E c`.
-/
theorem exists_place_of_emb : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l), ∃ v : HeightOneSpectrum (𝓞 E), v ∈ placesOver E l ∧
      ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1 := by
  intro l _ E _ _ c
  refine ⟨⟨ballIdeal l E c, ballIdeal_isPrime l E c, ballIdeal_ne_bot l E c⟩, ?_, fun x => Iff.rfl⟩
  exact natCast_mem_ballIdeal l E c

end GlobalTheory.LocPlace
