import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtLeafSt

namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mem_vRing_iff {Ω : Type*} [Field Ω] (v : AddValuation Ω (WithTop ℤ)) (x : Ω) :
    x ∈ vRing v ↔ 0 ≤ v x := by
  rfl

/- English proof (translation)
Proceed by induction on `x using WithTop.recTopCoe with`. Consider the case `top => exact le_top`. Consider the case `coe n`. Establish `h0 : (0 : ℤ) < n` using `by exact_mod_cast h`. Conclude with `(show (1 : ℤ) ≤ n by omega)` after adjusting the coercions.
-/
theorem one_le_of_pos {x : WithTop ℤ} (h : 0 < x) : 1 ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe n =>
    have h0 : (0 : ℤ) < n := by exact_mod_cast h
    exact_mod_cast (show (1 : ℤ) ≤ n by omega)

/- English proof (translation)
Establish `h0 : 0 ≤ v (x : Ω)` using `x.2`. Break down `h0.lt_or_eq with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Apply `hx` to reduce the goal to its premises.

Establish `hx0 : (x : Ω) ≠ 0`. Introduce `h'`. Rewrite `h` using `[h', AddValuation.map_zero]`. Conclude with `WithTop.top_ne_zero h.symm`. Establish `hinv : (x : Ω)⁻¹ ∈ vRing v` using `by show 0 ≤ v ((x : Ω)⁻¹)`.

Rewrite using `[AddValuation.map_inv, ← h, neg_zero]`. Conclude with `⟨⟨x, ⟨(x : Ω)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩`.
-/
theorem pos_of_not_isUnit {Ω : Type*} [Field Ω] (v : AddValuation Ω (WithTop ℤ))
    (x : vRing v) (hx : ¬ IsUnit x) : 0 < v (x : Ω) := by
  have h0 : 0 ≤ v (x : Ω) := x.2
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    have hx0 : (x : Ω) ≠ 0 := by
      intro h'
      rw [h', AddValuation.map_zero] at h
      exact WithTop.top_ne_zero h.symm
    have hinv : (x : Ω)⁻¹ ∈ vRing v := by
      show 0 ≤ v ((x : Ω)⁻¹)
      rw [AddValuation.map_inv, ← h, neg_zero]
    exact ⟨⟨x, ⟨(x : Ω)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

/- English proof (translation)
Unfold `ratio`. Establish `hex : ∃ a : Ω, f = a • g` using `⟨a, h⟩`. Rewrite using `[dif_pos hex]`. Establish `h2` using `hex.choose_spec`. Conclude with `smul_left_injective Ω hg (h.symm.trans h2).symm`.
-/
theorem ratio_eq_of {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f g : V} {a : Ω}
    (hg : g ≠ 0) (h : f = a • g) : ratio f g = a := by
  unfold ratio
  have hex : ∃ a : Ω, f = a • g := ⟨a, h⟩
  rw [dif_pos hex]
  have h2 := hex.choose_spec
  exact smul_left_injective Ω hg (h.symm.trans h2).symm

/- English proof (translation)
Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' (⟨g, hg⟩ : l) (by simpa using hg0)).mp h1 ⟨f, hf⟩`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg Subtype.val hc`. Simplify using `using h2.symm`.
-/
theorem exists_smul_of_line {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    {l : Submodule Ω V} (h1 : Module.finrank Ω l = 1) {f g : V} (hf : f ∈ l) (hg : g ∈ l)
    (hg0 : g ≠ 0) : ∃ a : Ω, f = a • g := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨g, hg⟩ : l) (by simpa using hg0)).mp h1 ⟨f, hf⟩
  refine ⟨c, ?_⟩
  have h2 := congrArg Subtype.val hc
  simpa using h2.symm

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hlt : Q < P` using `lt_of_le_of_ne hle hne`. Establish `hP1 : P.height ≤ ((1 : ℕ) : ℕ∞)` using `by rw [hP]; rfl`. Establish `h1 : Q.height < ((1 : ℕ) : ℕ∞)` using `(Ideal.height_le_iff.mp hP1) Q inferInstance hlt`. Establish `h2 : Q.height = 0` using `ENat.lt_one_iff_eq_zero.mp (by exact_mod_cast h1)`.

Establish `hmin` using `Ideal.height_eq_zero_iff.mp h2`. Establish `hbot : Q ≤ ⊥` using `hmin.2 ⟨Ideal.bot_prime, le_refl _⟩ bot_le`. Conclude with `hQ (le_bot_iff.mp hbot)`.
-/
theorem eq_of_le_ht {R : Type*} [CommRing R] [IsDomain R] {Q P : Ideal R} [Q.IsPrime]
    [P.IsPrime] (hP : P.height = 1) (hQ : Q ≠ ⊥) (hle : Q ≤ P) : Q = P := by
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hle hne
  have hP1 : P.height ≤ ((1 : ℕ) : ℕ∞) := by rw [hP]; rfl
  have h1 : Q.height < ((1 : ℕ) : ℕ∞) := (Ideal.height_le_iff.mp hP1) Q inferInstance hlt
  have h2 : Q.height = 0 := ENat.lt_one_iff_eq_zero.mp (by exact_mod_cast h1)
  have hmin := Ideal.height_eq_zero_iff.mp h2
  have hbot : Q ≤ ⊥ := hmin.2 ⟨Ideal.bot_prime, le_refl _⟩ bot_le
  exact hQ (le_bot_iff.mp hbot)

/- English proof (translation)
The claim follows from `Fin.insertNth_apply_same (α := fun _ => α) i x f`.
-/
theorem sac_same {α : Type*} {n : ℕ} (i : Fin (n + 1)) (x : α) (f : Fin n → α) :
    Fin.succAboveCases (α := fun _ => α) i x f i = x := Fin.insertNth_apply_same (α := fun _ => α) i x f

/- English proof (translation)
The claim follows from `Fin.insertNth_apply_succAbove (α := fun _ => α) i x f k`.
-/
theorem sac_succAbove {α : Type*} {n : ℕ} (i : Fin (n + 1)) (x : α) (f : Fin n → α)
    (k : Fin n) : Fin.succAboveCases (α := fun _ => α) i x f (i.succAbove k) = f k := Fin.insertNth_apply_succAbove (α := fun _ => α) i x f k

end GaussValuationUniqueness
