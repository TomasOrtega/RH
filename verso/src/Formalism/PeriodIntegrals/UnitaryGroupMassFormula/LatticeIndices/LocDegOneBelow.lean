import Mathlib
import ReciprocityTheory.GaloisValuations.ArithOfA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ValNatCastOf

noncomputable section

namespace MassDataIdxRes

open NumberField IsDedekindDomain Ideal

section K

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `hfin` using `Formalism.L2.SG.TypedSets.finite_over K l hl.out.ne_zero`. Use `set T := hfin.toFinset with hTdef`. Establish `hT : ∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 K) ∈ v.asIdeal` using `fun v => by`. Rewrite using `[hTdef, Set.Finite.mem_toFinset]`. Both sides reduce to the same expression.

Establish `hsum` using `ReciprocityTheory.Gal.sum_locDegree l T hT`. Establish `hcard : T.card = Module.finrank ℚ K` using `by rw [← h, Set.ncard_eq_toFinset_card _ hfin]`. Establish `hpos : ∀ v ∈ T, (fun _ => 1) v ≤ ReciprocityTheory.Gal.locDegree v` using `fun v _ => Nat.mul_pos (Ideal.ramificationIdx_pos v.asIdeal ℤ) (Ideal.inertiaDeg_pos v.asIdeal ℤ)`. Establish `hall` using `(Finset.sum_eq_sum_iff_of_le hpos).1 (by`. Simplify using `only [Finset.sum_const, smul_eq_mul, mul_one]`.

Rewrite using `[hsum, hcard])`. Establish `hm : w.asIdeal.ramificationIdx ℤ * w.asIdeal.inertiaDeg ℤ = 1` using `(hall w ((hT w).2 hw)).symm`. Conclude with `⟨Nat.eq_one_of_mul_eq_one_right hm, Nat.eq_one_of_mul_eq_one_left hm⟩`.
-/
theorem locDeg_one (l : ℕ) [hl : Fact l.Prime]
    (h : {w : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard = Module.finrank ℚ K)
    (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    w.asIdeal.ramificationIdx ℤ = 1 ∧ w.asIdeal.inertiaDeg ℤ = 1 := by
  have hfin := Formalism.L2.SG.TypedSets.finite_over K l hl.out.ne_zero
  set T := hfin.toFinset with hTdef
  have hT : ∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := fun v => by
    rw [hTdef, Set.Finite.mem_toFinset]; rfl
  have hsum := ReciprocityTheory.Gal.sum_locDegree l T hT
  have hcard : T.card = Module.finrank ℚ K := by rw [← h, Set.ncard_eq_toFinset_card _ hfin]
  have hpos : ∀ v ∈ T, (fun _ => 1) v ≤ ReciprocityTheory.Gal.locDegree v := fun v _ =>
    Nat.mul_pos (Ideal.ramificationIdx_pos v.asIdeal ℤ) (Ideal.inertiaDeg_pos v.asIdeal ℤ)
  have hall := (Finset.sum_eq_sum_iff_of_le hpos).1 (by
    simp only [Finset.sum_const, smul_eq_mul, mul_one]; rw [hsum, hcard])
  have hm : w.asIdeal.ramificationIdx ℤ * w.asIdeal.inertiaDeg ℤ = 1 := (hall w ((hT w).2 hw)).symm
  exact ⟨Nat.eq_one_of_mul_eq_one_right hm, Nat.eq_one_of_mul_eq_one_left hm⟩

end K

section FE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `p.isMaximal` as an intermediate fact. Take `⟨Q, hQm, hQo⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) p.asIdeal`. Establish `hQ0 : Q ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q`. Set `w : HeightOneSpectrum (𝓞 E)` to `⟨Q, hQm.isPrime, hQ0⟩`. Establish `hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal`.

Use `(Ideal.mem_of_liesOver Q p.asIdeal ((l : ℕ) : 𝓞 F)).1 hp` as an intermediate fact. Simplify using `using this`. Take `⟨he, hf⟩` from `locDeg_one l h w hw`. Establish `hQp : Q.IsPrime` using `hQm.isPrime`. Establish `h1 : p.asIdeal.ramificationIdx ℤ ≤ Q.ramificationIdx ℤ` using `Ideal.ramificationIdx_below_le (R := ℤ) (q := p.asIdeal) (r := Q)`.

Establish `h2 : p.asIdeal.inertiaDeg ℤ ≤ Q.inertiaDeg ℤ` using `Ideal.inertiaDeg_below_le (R := ℤ) (q := p.asIdeal) (r := Q)`. Establish `h3` using `Ideal.ramificationIdx_pos p.asIdeal ℤ`. Establish `h4` using `Ideal.inertiaDeg_pos p.asIdeal ℤ`. Express the relevant statement in the definitionally equal form `Q.ramificationIdx ℤ = 1 at he`. Express the relevant statement in the definitionally equal form `Q.inertiaDeg ℤ = 1 at hf`.

Use linear arithmetic over natural numbers and integers.
-/
theorem locDeg_one_below (l : ℕ) [hl : Fact l.Prime]
    (h : {w : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (p : HeightOneSpectrum (𝓞 F)) (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) :
    p.asIdeal.ramificationIdx ℤ = 1 ∧ p.asIdeal.inertiaDeg ℤ = 1 := by
  have := p.isMaximal
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) p.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q
  let w : HeightOneSpectrum (𝓞 E) := ⟨Q, hQm.isPrime, hQ0⟩
  have hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    have := (Ideal.mem_of_liesOver Q p.asIdeal ((l : ℕ) : 𝓞 F)).1 hp
    simpa using this
  obtain ⟨he, hf⟩ := locDeg_one l h w hw
  have hQp : Q.IsPrime := hQm.isPrime
  have h1 : p.asIdeal.ramificationIdx ℤ ≤ Q.ramificationIdx ℤ :=
    Ideal.ramificationIdx_below_le (R := ℤ) (q := p.asIdeal) (r := Q)
  have h2 : p.asIdeal.inertiaDeg ℤ ≤ Q.inertiaDeg ℤ :=
    Ideal.inertiaDeg_below_le (R := ℤ) (q := p.asIdeal) (r := Q)
  have h3 := Ideal.ramificationIdx_pos p.asIdeal ℤ
  have h4 := Ideal.inertiaDeg_pos p.asIdeal ℤ
  change Q.ramificationIdx ℤ = 1 at he
  change Q.inertiaDeg ℤ = 1 at hf
  omega

end FE

section Arith

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `hlo : p.asIdeal.LiesOver (Ideal.span {(l : ℤ)})` using `(ReciprocityTheory.Gal.liesOver_span_iff l p.asIdeal).2 hp`. Prove the components needed by the constructor for the conclusion. Use `Ideal.pow_inertiaDeg l p.asIdeal` as an intermediate fact. Rewrite `this` using `[hf, pow_one]`. Rewrite using `[this, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Introduce `h2`. Establish `hmap : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 F)) = Ideal.span {((l : ℕ) : 𝓞 F)}`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Simplify using the standard rewrite rules. Establish `hne : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 F)) ≠ ⊥`.

Rewrite using `[hmap, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hl.out.ne_zero` after adjusting the coercions. Establish `hm` using `IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {(l : ℤ)}) p.asIdeal hne`. Rewrite `hm` using `[he, hmap]`. Establish `hdvd : p.asIdeal ^ 2 ∣ Ideal.span {((l : ℕ) : 𝓞 F)}` using `Ideal.dvd_span_singleton.2 h2`.

Establish `hfin : FiniteMultiplicity p.asIdeal (Ideal.span {((l : ℕ) : 𝓞 F)})`. Apply `FiniteMultiplicity.of_not_isUnit` to reduce the goal to its premises. Rewrite using `[Ideal.isUnit_iff]`. Conclude with `p.isPrime.ne_top`. Rewrite using `[Ne, Ideal.zero_eq_bot, ← hmap]`.

Conclude with `hne`. Use `hfin.le_multiplicity_of_pow_dvd hdvd` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem arith_of_loc (l : ℕ) [hl : Fact l.Prime] (p : HeightOneSpectrum (𝓞 F))
    (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) (he : p.asIdeal.ramificationIdx ℤ = 1)
    (hf : p.asIdeal.inertiaDeg ℤ = 1) :
    Nat.card (𝓞 F ⧸ p.asIdeal) = l ∧ ((l : ℕ) : 𝓞 F) ∉ p.asIdeal ^ 2 := by
  have hlo : p.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := (ReciprocityTheory.Gal.liesOver_span_iff l p.asIdeal).2 hp
  constructor
  · have := Ideal.pow_inertiaDeg l p.asIdeal
    rw [hf, pow_one] at this
    rw [this, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · intro h2
    have hmap : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 F)) = Ideal.span {((l : ℕ) : 𝓞 F)} := by
      rw [Ideal.map_span, Set.image_singleton]; simp
    have hne : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 F)) ≠ ⊥ := by
      rw [hmap, Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hl.out.ne_zero
    have hm := IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {(l : ℤ)}) p.asIdeal hne
    rw [he, hmap] at hm
    have hdvd : p.asIdeal ^ 2 ∣ Ideal.span {((l : ℕ) : 𝓞 F)} := Ideal.dvd_span_singleton.2 h2
    have hfin : FiniteMultiplicity p.asIdeal (Ideal.span {((l : ℕ) : 𝓞 F)}) := by
      apply FiniteMultiplicity.of_not_isUnit
      · rw [Ideal.isUnit_iff]; exact p.isPrime.ne_top
      · rw [Ne, Ideal.zero_eq_bot, ← hmap]; exact hne
    have := hfin.le_multiplicity_of_pow_dvd hdvd
    omega

end Arith

end MassDataIdxRes
