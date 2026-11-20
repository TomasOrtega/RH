import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.IsMaximalComapCj

noncomputable section
open NumberField Matrix

namespace PI.SqPairLocal

open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← sub_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem scal_sq (ε : 𝓞 E) :
    (ε : E) • (1 : Matrix (Fin N) (Fin N) E) * (ε : E) • 1 - (ε : E) • 1 =
      ((ε * (ε - 1) : 𝓞 E) : E) • (1 : Matrix (Fin N) (Fin N) E) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← sub_smul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Establish `hc0 : ((cj E ε : 𝓞 E) : E) = star (ε : E)` using `rfl`. Establish `hc : ((ε + cj E ε - 1 : 𝓞 E) : E) = (ε : E) + star (ε : E) - 1`. Use `push_cast`. Conclude with `congrArg (fun z => (ε : E) + z - 1) hc0`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hc, sub_smul, add_smul, one_smul]`.
-/
theorem scal_adj (ε : 𝓞 E) :
    (ε : E) • (1 : Matrix (Fin N) (Fin N) E) + ((ε : E) • (1 : Matrix (Fin N) (Fin N) E))ᴴ - 1 =
      ((ε + cj E ε - 1 : 𝓞 E) : E) • (1 : Matrix (Fin N) (Fin N) E) := by
  have hc0 : ((cj E ε : 𝓞 E) : E) = star (ε : E) := rfl
  have hc : ((ε + cj E ε - 1 : 𝓞 E) : E) = (ε : E) + star (ε : E) - 1 := by
    push_cast
    exact congrArg (fun z => (ε : E) + z - 1) hc0
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hc, sub_smul, add_smul, one_smul]

/- English proof (translation)
Unfold `Dv at h`. Unfold `SmallAt`. Introduce `y hy`. Take `⟨s, hs, w, hw⟩` from `h`. Use `⟨s, hs, w • y, L.smul_mem w hy, ?_⟩` and prove the remaining obligations.

Establish `key : ∀ (r : 𝓞 E) (z : Fin N → E), r • z = (r : E) • z` using `fun r z => rfl`. Simplify using `only [Matrix.smul_mulVec, Matrix.one_mulVec, key, smul_smul]`. Use `congr 1`. Conclude with `hw` after adjusting the coercions.
-/
private lemma smallAt_smul_one_of_dv {Q : Ideal (𝓞 E)} {c a : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}
    (h : Dv Q c a) : SmallAt Q c L (((a : 𝓞 E) : E) • (1 : Matrix (Fin N) (Fin N) E)) := by
  unfold Dv at h
  unfold SmallAt
  intro y hy
  obtain ⟨s, hs, w, hw⟩ := h
  refine ⟨s, hs, w • y, L.smul_mem w hy, ?_⟩
  have key : ∀ (r : 𝓞 E) (z : Fin N → E), r • z = (r : E) • z := fun r z => rfl
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, key, smul_smul]
  congr 1
  exact_mod_cast hw

/- English proof (translation)
Unfold `Good`. Rewrite using `[scal_sq, scal_adj]`. Use the proof step `repeat' constructor`. Apply the tactic sequence `all_goals first | exact smallAt_smul_one_of_dv h1 | exact smallAt_smul_one_of_dv h2`.
-/
theorem good_scal {Q : Ideal (𝓞 E)} [Q.IsPrime] {c : 𝓞 E} {L' L'' : Submodule (𝓞 E) (Fin N → E)}
    {ε : 𝓞 E} (h1 : Dv Q c (ε * (ε - 1))) (h2 : Dv Q c (ε + cj E ε - 1)) :
    Good Q c L' L'' ((ε : E) • (1 : Matrix (Fin N) (Fin N) E)) := by
  unfold Good
  rw [scal_sq, scal_adj]
  repeat' constructor
  all_goals first | exact smallAt_smul_one_of_dv h1 | exact smallAt_smul_one_of_dv h2

/- English proof (translation)
Unfold `Pres`. Introduce `y hy`. Establish `key : ∀ (r : 𝓞 E) (z : Fin N → E), r • z = (r : E) • z` using `fun r z => rfl`. Establish `he : ((ε : E) • (1 : Matrix (Fin N) (Fin N) E)) *ᵥ y = ε • y`. Rewrite using `[key]`.

Simplify using `only [Matrix.smul_mulVec, Matrix.one_mulVec]`. Rewrite using `[he]`. Conclude with `L.smul_mem ε hy`.
-/
private lemma pres_integer_smul_one {L : Submodule (𝓞 E) (Fin N → E)} (ε : 𝓞 E) :
    Pres L ((ε : E) • (1 : Matrix (Fin N) (Fin N) E)) := by
  unfold Pres
  intro y hy
  have key : ∀ (r : 𝓞 E) (z : Fin N → E), r • z = (r : E) • z := fun r z => rfl
  have he : ((ε : E) • (1 : Matrix (Fin N) (Fin N) E)) *ᵥ y = ε • y := by
    rw [key]
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [he]
  exact L.smul_mem ε hy

/- English proof (translation)
Introduce `E _ _ _ _ N L' L'' _ _ _ Q hQ hne c hc`. Establish `cjcj : ∀ x : 𝓞 E, cj E (cj E x) = x` using `fun x => by`. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Use `show star (star (x : E)) = (x : E)`. Conclude with `star_star _`.

Use `set Q' := Ideal.comap (cj E) Q with hQ'def`. Establish `hsurj : Function.Surjective (cj E)` using `fun y => ⟨cj E y, cjcj y⟩`. Use `haveI := hQ`. Establish `hQ' : Q'.IsMaximal` using `Ideal.comap_isMaximal_of_surjective (cj E) hsurj`. Establish `hcc : Ideal.comap (cj E) Q' = Q`.

Use extensionality with `x`. Rewrite using `[hQ'def, Ideal.mem_comap, Ideal.mem_comap, cjcj]`. Establish `hsup : Q ⊔ Q' = ⊤`. Assume the negation of the conclusion as `h`. Establish `h1 : Q = Q ⊔ Q'` using `hQ.eq_of_le h le_sup_left`.

Establish `h2 : Q' = Q ⊔ Q'` using `hQ'.eq_of_le h le_sup_right`. Conclude with `hne (h2.trans h1.symm)`. Take `⟨K, hK⟩` from `hP E Q hQ c hc`. Take `⟨K', hK'⟩` from `hP E Q' hQ' c hc`. Use `set M := max K K'`.

Establish `h1top : (1 : 𝓞 E) ∈ Q ^ M ⊔ Q' ^ M`. Rewrite using `[Ideal.pow_sup_pow_eq_top hsup]`. Conclude with `Submodule.mem_top`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp h1top`. Establish `hb1 : b - 1 ∈ Q ^ M`.

Establish `hba : b - 1 = -a`. Rewrite using `[← hab]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hba]`. Conclude with `(Q ^ M).neg_mem ha`.

Establish `toQ' : ∀ x, x ∈ Q ^ M → cj E x ∈ Q' ^ M` using `fun x hx => by`. Establish `hle : Q ^ M ≤ Ideal.comap (cj E) (Q' ^ M)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Ideal.mem_comap.mp (hle hx)`. Establish `toQ : ∀ x, x ∈ Q' ^ M → cj E x ∈ Q ^ M` using `fun x hx => by`.

Establish `hle : Q' ^ M ≤ Ideal.comap (cj E) (Q ^ M)` using `Ideal.le_comap_pow _ M`. Conclude with `Ideal.mem_comap.mp (hle hx)`. Establish `hcb1 : cj E b - 1 ∈ Q' ^ M`. Establish `h` using `toQ' _ hb1`. Rewrite `h` using `[map_sub, map_one]`. Then use the resulting hypothesis.

Establish `hcb : cj E b ∈ Q ^ M` using `toQ _ hb`. Establish `dvQ : ∀ x, x ∈ Q ^ M → Dv Q c x` using `fun x hx => hK x (Ideal.pow_le_pow_right (le_max_left K K') hx)`. Establish `dvQ' : ∀ x, x ∈ Q' ^ M → Dv Q' c x` using `fun x hx => hK' x (Ideal.pow_le_pow_right (le_max_right K K') hx)`. Use `haveI := hQ.isPrime`. Use `haveI := hQ'.isPrime`.

Use `⟨(b : E) • (1 : Matrix (Fin N) (Fin N) E), pres_integer_smul_one b, pres_integer_smul_one b, ?_, ?_⟩` and prove the remaining obligations. Apply `good_scal` to reduce the goal to its premises. Conclude with `dvQ _ (Ideal.mul_mem_left _ b hb1)`. Establish `hr : b + cj E b - 1 = (b - 1) + cj E b` using `by ring`. Rewrite using `[hr]`.

Conclude with `dvQ _ (Ideal.add_mem _ hb1 hcb)`. Apply `good_scal` to reduce the goal to its premises. Conclude with `dvQ' _ (Ideal.mul_mem_right _ _ hb)`. Establish `hr : b + cj E b - 1 = b + (cj E b - 1)` using `by ring`. Rewrite using `[hr]`.

Conclude with `dvQ' _ (Ideal.add_mem _ hb hcb1)`.
-/
theorem splitPlace_of (hP : PowLoc) : SplitPlace := by
  intro E _ _ _ _ N L' L'' _ _ _ Q hQ hne c hc
  have cjcj : ∀ x : 𝓞 E, cj E (cj E x) = x := fun x => by
    apply NumberField.RingOfIntegers.ext
    show star (star (x : E)) = (x : E)
    exact star_star _
  set Q' := Ideal.comap (cj E) Q with hQ'def
  have hsurj : Function.Surjective (cj E) := fun y => ⟨cj E y, cjcj y⟩
  haveI := hQ
  have hQ' : Q'.IsMaximal := Ideal.comap_isMaximal_of_surjective (cj E) hsurj
  have hcc : Ideal.comap (cj E) Q' = Q := by
    ext x
    rw [hQ'def, Ideal.mem_comap, Ideal.mem_comap, cjcj]
  have hsup : Q ⊔ Q' = ⊤ := by
    by_contra h
    have h1 : Q = Q ⊔ Q' := hQ.eq_of_le h le_sup_left
    have h2 : Q' = Q ⊔ Q' := hQ'.eq_of_le h le_sup_right
    exact hne (h2.trans h1.symm)
  obtain ⟨K, hK⟩ := hP E Q hQ c hc
  obtain ⟨K', hK'⟩ := hP E Q' hQ' c hc
  set M := max K K'
  have h1top : (1 : 𝓞 E) ∈ Q ^ M ⊔ Q' ^ M := by
    rw [Ideal.pow_sup_pow_eq_top hsup]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1top
  have hb1 : b - 1 ∈ Q ^ M := by
    have hba : b - 1 = -a := by
      rw [← hab]
      ring
    rw [hba]
    exact (Q ^ M).neg_mem ha
  have toQ' : ∀ x, x ∈ Q ^ M → cj E x ∈ Q' ^ M := fun x hx => by
    have hle : Q ^ M ≤ Ideal.comap (cj E) (Q' ^ M) := by
      calc Q ^ M = (Ideal.comap (cj E) Q') ^ M := by rw [hcc]
        _ ≤ Ideal.comap (cj E) (Q' ^ M) := Ideal.le_comap_pow _ M
    exact Ideal.mem_comap.mp (hle hx)
  have toQ : ∀ x, x ∈ Q' ^ M → cj E x ∈ Q ^ M := fun x hx => by
    have hle : Q' ^ M ≤ Ideal.comap (cj E) (Q ^ M) := Ideal.le_comap_pow _ M
    exact Ideal.mem_comap.mp (hle hx)
  have hcb1 : cj E b - 1 ∈ Q' ^ M := by
    have h := toQ' _ hb1
    rwa [map_sub, map_one] at h
  have hcb : cj E b ∈ Q ^ M := toQ _ hb
  have dvQ : ∀ x, x ∈ Q ^ M → Dv Q c x := fun x hx =>
    hK x (Ideal.pow_le_pow_right (le_max_left K K') hx)
  have dvQ' : ∀ x, x ∈ Q' ^ M → Dv Q' c x := fun x hx =>
    hK' x (Ideal.pow_le_pow_right (le_max_right K K') hx)
  haveI := hQ.isPrime
  haveI := hQ'.isPrime
  refine ⟨(b : E) • (1 : Matrix (Fin N) (Fin N) E), pres_integer_smul_one b, pres_integer_smul_one b, ?_, ?_⟩
  · apply good_scal
    · exact dvQ _ (Ideal.mul_mem_left _ b hb1)
    · have hr : b + cj E b - 1 = (b - 1) + cj E b := by ring
      rw [hr]
      exact dvQ _ (Ideal.add_mem _ hb1 hcb)
  · apply good_scal
    · exact dvQ' _ (Ideal.mul_mem_right _ _ hb)
    · have hr : b + cj E b - 1 = b + (cj E b - 1) := by ring
      rw [hr]
      exact dvQ' _ (Ideal.add_mem _ hb hcb1)

end PI.SqPairLocal
