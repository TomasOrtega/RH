import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.DenseSurj

namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)`.
-/
theorem norm_natCast_lt_one (l : ℕ) [hl : Fact l.Prime] : ‖((l : ℕ) : Om l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]`. Conclude with `inv_pos.2 (by exact_mod_cast hl.out.pos)`.
-/
theorem norm_natCast_pos (l : ℕ) [hl : Fact l.Prime] : 0 < ‖((l : ℕ) : Om l)‖ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_pos.2 (by exact_mod_cast hl.out.pos)

/- English proof (translation)
Establish `hv` using `Valuation.integer.integers (Valued.v : Valuation (Om l) NNReal)`. Establish `h1 : IsIntegral ℤ (φ (x : E))` using `(RingOfIntegers.isIntegral_coe x).map φ.toIntAlgHom`. Establish `h2 : IsIntegral (Valued.v : Valuation (Om l) NNReal).integer (φ (x : E))` using `h1.tower_top`. Establish `h3` using `(hv.isIntegral_iff_v_le_one).1 h2`. Rewrite `h3` using `[PadicAlgCl.valuation_def]`.

Conclude with `h3` after adjusting the coercions.
-/
theorem norm_le_one_of_integer {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) (x : 𝓞 E) : ‖φ (x : E)‖ ≤ 1 := by
  have hv := Valuation.integer.integers (Valued.v : Valuation (Om l) NNReal)
  have h1 : IsIntegral ℤ (φ (x : E)) := (RingOfIntegers.isIntegral_coe x).map φ.toIntAlgHom
  have h2 : IsIntegral (Valued.v : Valuation (Om l) NNReal).integer (φ (x : E)) := h1.tower_top
  have h3 := (hv.isIntegral_iff_v_le_one).1 h2
  rw [PadicAlgCl.valuation_def] at h3
  exact_mod_cast h3

def plIdeal {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* Om l) :
    Ideal (𝓞 E) where
  carrier := {x | ‖φ (x : E)‖ < 1}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    change ‖φ (algebraMap (𝓞 E) E (a + b))‖ < 1
    change ‖φ (algebraMap (𝓞 E) E a)‖ < 1 at ha
    change ‖φ (algebraMap (𝓞 E) E b)‖ < 1 at hb
    rw [map_add, map_add]
    exact lt_of_le_of_lt (PadicAlgCl.isNonarchimedean l _ _) (max_lt ha hb)
  smul_mem' c {a} ha := by
    change ‖φ (algebraMap (𝓞 E) E (c * a))‖ < 1
    change ‖φ (algebraMap (𝓞 E) E a)‖ < 1 at ha
    rw [map_mul, map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_integer φ c)) ha

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_plIdeal {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* Om l)
    (x : 𝓞 E) : x ∈ plIdeal φ ↔ ‖φ (x : E)‖ < 1 := Iff.rfl

/- English proof (translation)
Rewrite using `[mem_plIdeal]`. Simplify using `using norm_natCast_lt_one l`.
-/
theorem natCast_mem_plIdeal {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) : ((l : ℕ) : 𝓞 E) ∈ plIdeal φ := by
  rw [mem_plIdeal]
  simpa using norm_natCast_lt_one l

/- English proof (translation)
Establish `: (1 : 𝓞 E) ∈ plIdeal φ` using `h ▸ Submodule.mem_top`. Rewrite `this` using `[mem_plIdeal]`. Simplify using `at this`. Use the proof step `mem_or_mem' {a b} hab := by`. Simplify using `only [mem_plIdeal, RingOfIntegers.coe_eq_algebraMap, map_mul, norm_mul] at *`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Use `mul_le_mul h.1 h.2 zero_le_one (norm_nonneg _)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem plIdeal_isPrime {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) : (plIdeal φ).IsPrime where
  ne_top' h := by
    have : (1 : 𝓞 E) ∈ plIdeal φ := h ▸ Submodule.mem_top
    rw [mem_plIdeal] at this
    simp at this
  mem_or_mem' {a b} hab := by
    simp only [mem_plIdeal, RingOfIntegers.coe_eq_algebraMap, map_mul, norm_mul] at *
    by_contra h
    push Not at h
    have := mul_le_mul h.1 h.2 zero_le_one (norm_nonneg _)
    linarith

/- English proof (translation)
Introduce `h`. Establish `h1` using `natCast_mem_plIdeal (E := E) φ`. Rewrite `h1` using `[h, Ideal.mem_bot]`. Establish `: ((l : ℕ) : E) = 0` using `by exact_mod_cast congrArg (fun y : 𝓞 E => (y : E)) h1`. Conclude with `hl.out.ne_zero (by exact_mod_cast this)`.
-/
theorem plIdeal_ne_bot {l : ℕ} [hl : Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) : plIdeal φ ≠ ⊥ := by
  intro h
  have h1 := natCast_mem_plIdeal (E := E) φ
  rw [h, Ideal.mem_bot] at h1
  have : ((l : ℕ) : E) = 0 := by exact_mod_cast congrArg (fun y : 𝓞 E => (y : E)) h1
  exact hl.out.ne_zero (by exact_mod_cast this)

def plOf {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* Om l) :
    HeightOneSpectrum (𝓞 E) :=
  ⟨plIdeal φ, plIdeal_isPrime φ, plIdeal_ne_bot φ⟩

/- English proof (translation)
Introduce `l _ E _ _ φ`. Use `⟨plOf φ, natCast_mem_plIdeal φ, fun x => ⟨norm_le_one_of_integer φ x, Iff.rfl⟩⟩` and prove the remaining obligations.
-/
theorem placeProp : PlaceProp := by
  intro l _ E _ _ φ
  refine ⟨plOf φ, natCast_mem_plIdeal φ, fun x => ⟨norm_le_one_of_integer φ x, Iff.rfl⟩⟩

end PI.CompDegEF
