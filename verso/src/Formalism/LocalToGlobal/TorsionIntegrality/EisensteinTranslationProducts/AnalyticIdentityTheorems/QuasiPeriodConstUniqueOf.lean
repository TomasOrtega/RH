import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroLogDerivative

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace PeriodAreaSignLemmas

def det (L : PeriodPair) : ℝ := (conj L.ω₁ * L.ω₂).im

def sgn (L : PeriodPair) : ℤ := if 0 < (L.ω₂ / L.ω₁).im then 1 else -1

/- English proof (translation)
Simplify using `[det, Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma det_eq (L : PeriodPair) : det L = L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re := by
  simp [det, Complex.mul_im]
  ring

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[det_eq]`. Establish `key` using `LinearIndependent.pair_iff.mp L.indep`. Establish `h1` using `key L.ω₂.im (-L.ω₁.im) (by`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using the standard rewrite rules. Use the proof step `ring)`. Establish `h2` using `key L.ω₂.re (-L.ω₁.re) (by`.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Use the proof step `linarith)`.

Establish `h3 : L.ω₁ = 0`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `using h2.2`. Simplify using `using h1.2`. Establish `h4` using `key 1 0 (by simp [h3])`.

Conclude with `one_ne_zero h4.1`.
-/
lemma det_ne_zero (L : PeriodPair) : det L ≠ 0 := by
  intro h
  rw [det_eq] at h
  have key := LinearIndependent.pair_iff.mp L.indep
  have h1 := key L.ω₂.im (-L.ω₁.im) (by
    apply Complex.ext
    · simp; linarith
    · simp; ring)
  have h2 := key L.ω₂.re (-L.ω₁.re) (by
    apply Complex.ext
    · simp; ring
    · simp; linarith)
  have h3 : L.ω₁ = 0 := by
    apply Complex.ext
    · simpa using h2.2
    · simpa using h1.2
  have h4 := key 1 0 (by simp [h3])
  exact one_ne_zero h4.1

/- English proof (translation)
Introduce `h`. Apply `det_ne_zero L` to reduce the goal to its premises. Simplify using `[det, h]`.
-/
lemma ω₁_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  intro h
  apply det_ne_zero L
  simp [det, h]

/- English proof (translation)
Rewrite using `[Complex.div_im, det_eq]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma div_im (L : PeriodPair) : (L.ω₂ / L.ω₁).im = det L / Complex.normSq L.ω₁ := by
  rw [Complex.div_im, det_eq]; ring

/- English proof (translation)
Establish `hn : 0 < Complex.normSq L.ω₁` using `Complex.normSq_pos.mpr (ω₁_ne_zero L)`. Rewrite using `[div_im, div_pos_iff_of_pos_right hn]`.
-/
lemma div_im_pos_iff (L : PeriodPair) : 0 < (L.ω₂ / L.ω₁).im ↔ 0 < det L := by
  have hn : 0 < Complex.normSq L.ω₁ := Complex.normSq_pos.mpr (ω₁_ne_zero L)
  rw [div_im, div_pos_iff_of_pos_right hn]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma area_eq (L : PeriodPair) : area L = |det L| := rfl

/- English proof (translation)
The claim follows from `abs_pos.mpr (det_ne_zero L)`.
-/
lemma area_pos (L : PeriodPair) : 0 < area L := abs_pos.mpr (det_ne_zero L)

/- English proof (translation)
Rewrite using `[area_eq, sgn]`. Use `split_ifs with h`. Rewrite using `[abs_of_pos ((div_im_pos_iff L).mp h)]`. Simplify using the standard rewrite rules. Establish `: det L < 0` using `lt_of_le_of_ne (not_lt.mp (fun h' => h ((div_im_pos_iff L).mpr h'))) (det_ne_zero L)`.

Rewrite using `[abs_of_neg this]`. Simplify using the standard rewrite rules.
-/
lemma det_eq_sgn_mul (L : PeriodPair) : det L = (sgn L : ℝ) * area L := by
  rw [area_eq, sgn]
  split_ifs with h
  · rw [abs_of_pos ((div_im_pos_iff L).mp h)]; simp
  · have : det L < 0 := lt_of_le_of_ne (not_lt.mp (fun h' => h ((div_im_pos_iff L).mpr h')))
      (det_ne_zero L)
    rw [abs_of_neg this]; simp

/- English proof (translation)
Apply the tactic sequence `rw [sgn]; split_ifs <;> decide`.
-/
lemma sgn_odd (L : PeriodPair) : ¬ Even (sgn L) := by
  rw [sgn]; split_ifs <;> decide

/- English proof (translation)
Rewrite using `[det_eq]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma disc_eq (L : PeriodPair) :
    L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁ = -(2 * Complex.I * (det L : ℂ)) := by
  rw [det_eq]
  apply Complex.ext
  · simp; ring
  · simp; ring

/- English proof (translation)
Rewrite using `[disc_eq]`. Establish `: (det L : ℂ) ≠ 0` using `by exact_mod_cast det_ne_zero L`. Simplify using `[this]`.
-/
lemma disc_ne_zero (L : PeriodPair) : L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁ ≠ 0 := by
  rw [disc_eq]
  have : (det L : ℂ) ≠ 0 := by exact_mod_cast det_ne_zero L
  simp [this]

/- English proof (translation)
Use `⟨L.basis.repr x 0, L.basis.repr x 1, ?_⟩` and prove the remaining obligations. Use `L.basis.sum_repr x` as an intermediate fact. Rewrite `this` using `[Fin.sum_univ_two]`. Simplify using `using this.symm`.
-/
lemma exists_coord (L : PeriodPair) (x : ℂ) : ∃ a b : ℝ, x = (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ := by
  refine ⟨L.basis.repr x 0, L.basis.repr x 1, ?_⟩
  have := L.basis.sum_repr x
  rw [Fin.sum_univ_two] at this
  simpa using this.symm

/- English proof (translation)
Establish `: (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ = a • L.ω₁ + b • L.ω₂` using `by simp`. Rewrite using `[this, map_add, map_smul, map_smul]`. Simplify using the standard rewrite rules.
-/
lemma wEta_coord (L : PeriodPair) (a b : ℝ) :
    wEta L ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) = (a : ℂ) * wEta L L.ω₁ + (b : ℂ) * wEta L L.ω₂ := by
  have : (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ = a • L.ω₁ + b • L.ω₂ := by simp
  rw [this, map_add, map_smul, map_smul]; simp

end PeriodAreaSignLemmas

open PeriodAreaSignLemmas

/- English proof (translation)
Introduce `L` and use `area_pos L`.
-/
theorem areaPos_thm : AreaPos := fun L => area_pos L

/- English proof (translation)
Introduce `L x`. Establish `hL` using `h L`. Establish `hs : ((if 0 < (L.ω₂ / L.ω₁).im then 1 else -1 : ℂ)) = ((sgn L : ℤ) : ℂ)`. Apply the tactic sequence `rw [sgn]; split_ifs <;> simp`. Rewrite `hL` using `[hs]`.

Establish `hA : (area L : ℂ) ≠ 0` using `by exact_mod_cast (area_pos L).ne'`. Establish `hD` using `disc_ne_zero L`. Establish `hDe` using `disc_eq L`. Establish `hdet : (det L : ℂ) = ((sgn L : ℤ) : ℂ) * (area L : ℂ)`. Conclude with `det_eq_sgn_mul L` after adjusting the coercions.

Use `set D := L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁ with hDdef`. Establish `hpi : ((Real.pi : ℂ) / (area L : ℂ)) * D = -(((sgn L : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))`. Rewrite using `[hDe, hdet]`. Clear the denominators using the available nonvanishing facts. Establish `hs2 : s2 L * D = wEta L L.ω₁ * conj L.ω₂ - wEta L L.ω₂ * conj L.ω₁`.

Rewrite using `[s2, ← hDdef]`. Clear the denominators using the available nonvanishing facts. Establish `e1 : wEta L L.ω₁ = s2 L * L.ω₁ + ((Real.pi : ℂ) / (area L : ℂ)) * conj L.ω₁`. Apply `mul_right_cancel₀ hD` to reduce the goal to its premises. Take the linear combination `(-L.ω₁) * hs2 - (conj L.ω₁) * hpi - (conj L.ω₁) * hL + wEta L L.ω₁ * hDdef`.

Establish `e2 : wEta L L.ω₂ = s2 L * L.ω₂ + ((Real.pi : ℂ) / (area L : ℂ)) * conj L.ω₂`. Apply `mul_right_cancel₀ hD` to reduce the goal to its premises. Take the linear combination `(-L.ω₂) * hs2 - (conj L.ω₂) * hpi - (conj L.ω₂) * hL + wEta L L.ω₂ * hDdef`. Take `⟨a, b, rfl⟩` from `exists_coord L x`. Rewrite using `[wEta_coord]`.

Simplify using `only [map_add, map_mul, Complex.conj_ofReal]`. Take the linear combination `(a : ℂ) * e1 + (b : ℂ) * e2`.
-/
theorem etaSplit_of (h : Legendre) : EtaSplit := by
  intro L x
  have hL := h L
  have hs : ((if 0 < (L.ω₂ / L.ω₁).im then 1 else -1 : ℂ)) = ((sgn L : ℤ) : ℂ) := by
    rw [sgn]; split_ifs <;> simp
  rw [hs] at hL
  have hA : (area L : ℂ) ≠ 0 := by exact_mod_cast (area_pos L).ne'
  have hD := disc_ne_zero L
  have hDe := disc_eq L
  have hdet : (det L : ℂ) = ((sgn L : ℤ) : ℂ) * (area L : ℂ) := by
    exact_mod_cast det_eq_sgn_mul L
  set D := L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁ with hDdef
  have hpi : ((Real.pi : ℂ) / (area L : ℂ)) * D
      = -(((sgn L : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    rw [hDe, hdet]; field_simp
  have hs2 : s2 L * D = wEta L L.ω₁ * conj L.ω₂ - wEta L L.ω₂ * conj L.ω₁ := by
    rw [s2, ← hDdef]; field_simp
  have e1 : wEta L L.ω₁ = s2 L * L.ω₁ + ((Real.pi : ℂ) / (area L : ℂ)) * conj L.ω₁ := by
    apply mul_right_cancel₀ hD
    linear_combination (-L.ω₁) * hs2 - (conj L.ω₁) * hpi - (conj L.ω₁) * hL + wEta L L.ω₁ * hDdef
  have e2 : wEta L L.ω₂ = s2 L * L.ω₂ + ((Real.pi : ℂ) / (area L : ℂ)) * conj L.ω₂ := by
    apply mul_right_cancel₀ hD
    linear_combination (-L.ω₂) * hs2 - (conj L.ω₂) * hpi - (conj L.ω₂) * hL + wEta L L.ω₂ * hDdef
  obtain ⟨a, b, rfl⟩ := exists_coord L x
  rw [wEta_coord]
  simp only [map_add, map_mul, Complex.conj_ofReal]
  linear_combination (a : ℂ) * e1 + (b : ℂ) * e2

namespace PeriodAreaSignLemmas

/- English proof (translation)
Establish `hA : area L ≠ 0` using `(area_pos L).ne'`. Rewrite using `[altE, herm, Complex.div_ofReal_im, div_eq_iff hA]`. Establish `h1 : (((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) * conj ((m' : ℂ) * L.ω₁ + (n' : ℂ) * L.ω₂)).im = -((m * n' - n * m' : ℝ) * det L)`. Rewrite using `[det_eq]`. Simplify using `[Complex.mul_im, Complex.mul_re]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, det_eq_sgn_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma altE_coord (L : PeriodPair) (m n m' n' : ℤ) :
    altE L ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ((m' : ℂ) * L.ω₁ + (n' : ℂ) * L.ω₂)
      = ((-(sgn L * (m * n' - n * m')) : ℤ) : ℝ) := by
  have hA : area L ≠ 0 := (area_pos L).ne'
  rw [altE, herm, Complex.div_ofReal_im, div_eq_iff hA]
  have h1 : (((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) * conj ((m' : ℂ) * L.ω₁ + (n' : ℂ) * L.ω₂)).im
      = -((m * n' - n * m' : ℝ) * det L) := by
    rw [det_eq]
    simp [Complex.mul_im, Complex.mul_re]
    ring
  rw [h1, det_eq_sgn_mul]
  push_cast
  ring

/- English proof (translation)
Establish `key : ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) / 2 ∈ L.lattice ↔ Even m ∧ Even n`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨a, b, e⟩` from `PeriodPair.mem_lattice.mp hx`. Use `LinearIndependent.pair_iff.mp L.indep ((m : ℝ) - 2 * a) ((n : ℝ) - 2 * b) (by` as an intermediate fact.

Simplify using `only [Complex.real_smul]`. Use `push_cast`. Take the linear combination `(-2 : ℂ) * e)`. Use `⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩` and prove the remaining obligations. Establish `h1 : (m : ℝ) = 2 * a` using `by linarith [this.1]`.

Establish `: m = 2 * a` using `by exact_mod_cast h1`. Use linear arithmetic over natural numbers and integers. Establish `h1 : (n : ℝ) = 2 * b` using `by linarith [this.2]`. Establish `: n = 2 * b` using `by exact_mod_cast h1`. Use linear arithmetic over natural numbers and integers.

Introduce and unpack `⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩`. Use `PeriodPair.mem_lattice.mpr ⟨a, b, ?_⟩` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[semiChar]`.

Simplify using `only [key]`.
-/
lemma semiChar_coord (L : PeriodPair) (m n : ℤ) :
    semiChar L ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) = if Even m ∧ Even n then 1 else -1 := by
  have key : ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) / 2 ∈ L.lattice ↔ Even m ∧ Even n := by
    constructor
    · intro hx
      obtain ⟨a, b, e⟩ := PeriodPair.mem_lattice.mp hx
      have := LinearIndependent.pair_iff.mp L.indep ((m : ℝ) - 2 * a) ((n : ℝ) - 2 * b) (by
        simp only [Complex.real_smul]
        push_cast
        linear_combination (-2 : ℂ) * e)
      refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩
      · have h1 : (m : ℝ) = 2 * a := by linarith [this.1]
        have : m = 2 * a := by exact_mod_cast h1
        omega
      · have h1 : (n : ℝ) = 2 * b := by linarith [this.2]
        have : n = 2 * b := by exact_mod_cast h1
        omega
    · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
      refine PeriodPair.mem_lattice.mpr ⟨a, b, ?_⟩
      push_cast
      ring
  rw [semiChar]
  simp only [key]

/- English proof (translation)
Establish `: (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ) = (k : ℂ) * ((Real.pi : ℂ) * Complex.I)` using `by push_cast; ring`. Rewrite using `[this, Complex.exp_int_mul, Complex.exp_pi_mul_I]`. Use `split_ifs with h`. Conclude with `h.neg_one_zpow`. Conclude with `(Int.not_even_iff_odd.mp h).neg_one_zpow`.
-/
lemma exp_pi_int (k : ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ)) = if Even k then 1 else -1 := by
  have : (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ) = (k : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  split_ifs with h
  · exact h.neg_one_zpow
  · exact (Int.not_even_iff_odd.mp h).neg_one_zpow

end PeriodAreaSignLemmas

/- English proof (translation)
Introduce `L x y hx hy`. Take `⟨m, n, rfl⟩` from `PeriodPair.mem_lattice.mp hx`. Take `⟨m', n', rfl⟩` from `PeriodPair.mem_lattice.mp hy`. Conclude with `⟨_, altE_coord L m n m' n'⟩`.
-/
theorem alternating_form_integral : AltEInt := by
  intro L x y hx hy
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hx
  obtain ⟨m', n', rfl⟩ := PeriodPair.mem_lattice.mp hy
  exact ⟨_, altE_coord L m n m' n'⟩

/- English proof (translation)
Introduce `L`. Use `altE_coord L 1 0 0 1` as an intermediate fact. Simplify using `only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero, zero_add] at this`. Rewrite using `[this, sgn]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem alternating_form_basis : AltEBasis := by
  intro L
  have := altE_coord L 1 0 0 1
  simp only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero, zero_add] at this
  rw [this, sgn]
  split_ifs <;> simp

/- English proof (translation)
Introduce `L x y hx hy`. Take `⟨m, n, rfl⟩` from `PeriodPair.mem_lattice.mp hx`. Take `⟨m', n', rfl⟩` from `PeriodPair.mem_lattice.mp hy`. Establish `hadd : (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ + ((m' : ℂ) * L.ω₁ + (n' : ℂ) * L.ω₂) = ((m + m' : ℤ) : ℂ) * L.ω₁ + ((n + n' : ℤ) : ℂ) * L.ω₂` using `by push_cast; ring`. Rewrite using `[hadd, semiChar_coord, semiChar_coord, semiChar_coord, altE_coord, exp_pi_int]`.

Establish `hsg` using `sgn_odd L`. Apply the tactic sequence `by_cases h1 : Even m <;> by_cases h2 : Even n <;> by_cases h3 : Even m' <;>`. Apply the tactic sequence `by_cases h4 : Even n' <;>`. Simplify using `[Int.even_add, Int.even_sub, Int.even_mul, h1, h2, h3, h4, hsg]`.
-/
theorem semi_character_mul : SemiCharMul := by
  intro L x y hx hy
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hx
  obtain ⟨m', n', rfl⟩ := PeriodPair.mem_lattice.mp hy
  have hadd : (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ + ((m' : ℂ) * L.ω₁ + (n' : ℂ) * L.ω₂)
      = ((m + m' : ℤ) : ℂ) * L.ω₁ + ((n + n' : ℤ) : ℂ) * L.ω₂ := by
    push_cast; ring
  rw [hadd, semiChar_coord, semiChar_coord, semiChar_coord, altE_coord, exp_pi_int]
  have hsg := sgn_odd L
  by_cases h1 : Even m <;> by_cases h2 : Even n <;> by_cases h3 : Even m' <;>
    by_cases h4 : Even n' <;>
    simp [Int.even_add, Int.even_sub, Int.even_mul, h1, h2, h3, h4, hsg]

end Formalism.L2.Th1.F
