import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqOneOfForallPrimeMaximal

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => ring`. Consider the case `succ n ih`. Rewrite using `[pow_succ, ih]`. Take the linear combination `(a ^ n * a + b ^ n * b - a ^ n * b - b ^ n * a) * hg.eq`.
-/
theorem pow_idempotent_combination {R : Type} [CommRing R] {g : R} (hg : IsIdempotentElem g)
    (a b : R) (n : ℕ) : (g * a + (1 - g) * b) ^ n = g * a ^ n + (1 - g) * b ^ n := by
  induction n with
  | zero => ring
  | succ n ih =>
    rw [pow_succ, ih]
    linear_combination (a ^ n * a + b ^ n * b - a ^ n * b - b ^ n * a) * hg.eq

/- English proof (translation)
Introduce `R _ _ q hq hqu u hloc`. Establish `hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal` using `fun P hP => hP.isMaximal'`. Set `S : Set R` to `{g | IsIdempotentElem g ∧ ∃ x : R, IsNilpotent (g * (x ^ q - u))}`. Establish `hjoin : ∀ g ∈ S, ∀ h ∈ S, g + h - g * h ∈ S`. Introduce and unpack `g ⟨hg, x, hx⟩ h ⟨hh, z, hz⟩`.

Use `⟨?_, g * x + (1 - g) * z, ?_⟩` and prove the remaining obligations. Use `show (g + h - g * h) * (g + h - g * h) = g + h - g * h`. Take the linear combination `(1 - 2 * h + h ^ 2) * hg.eq + (1 - g) * hh.eq`. Establish `key : (g + h - g * h) * ((g * x + (1 - g) * z) ^ q - u) = g * (x ^ q - u) + (1 - g) * (h * (z ^ q - u))`. Rewrite using `[pow_idempotent_combination hg]`.

Take the linear combination `(x ^ q - z ^ q - h * x ^ q + h * z ^ q) * hg.eq`. Rewrite using `[key]`. Conclude with `Commute.isNilpotent_add (Commute.all _ _) hx ((Commute.all _ _).isNilpotent_mul_left (show IsNilpotent (h * (z ^ q - u)) from hz))`. Establish `hcover : ∀ m : Ideal R, m.IsMaximal → ∃ g ∈ S, g ∉ m`. Introduce `m hm`.

Take `⟨x, hx⟩` from `hloc m hm`. Take `⟨e, b, he, hab, hep⟩` from `exists_isIdempotentElem_mul_of_forall_isMaximal hR (x ^ q - u)`. Use `⟨1 - e, ⟨he.one_sub, x, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[nilpotent_iff_mem_prime]`. Introduce `p hp`.

Distinguish the cases in `ha : x ^ q - (u : R) ∈ p`. Conclude with `p.mul_mem_left _ ha`. Establish `hep'` using `hep p hp ha`. Establish `h0 : e * (1 - e) ∈ p`. Establish `: e * (1 - e) = 0` using `by linear_combination -he.eq`.

Rewrite using `[this]`. Conclude with `p.zero_mem`. Break down `hp.mem_or_mem h0 with h | h` into its components or cases. Conclude with `absurd h hep'`. Conclude with `p.mul_mem_right _ h`.

Introduce `h`. Establish `hem : e ∈ m` using `hab ▸ m.mul_mem_right b hx`. Apply `hm.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Simplify using `using m.add_mem h hem`.

Establish `hspan : Ideal.span S = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`. Take `⟨g, hgS, hgm⟩` from `hcover m hm`. Conclude with `hgm (hle (Ideal.subset_span hgS))`.

Establish `hfin : ∀ T : Finset R, (↑T ⊆ S) → ∃ G ∈ S, ∀ g ∈ T, g * G = g` using `by classical`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `_`.

Conclude with `⟨0, ⟨IsIdempotentElem.zero, 0, by simp⟩, by simp⟩`. Consider the case `insert a T ha ih`. Introduce `hT`. Establish `haS : a ∈ S` using `hT (by simp)`. Take `⟨G, hG, hGT⟩` from `ih (fun y hy => hT (by simp [hy]))`.

Use `⟨a + G - a * G, hjoin a haS G hG, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Break down `Finset.mem_insert.mp hg with rfl | hg` into its components or cases. Take the linear combination `(1 - G) * haS.1.eq`. Use `hGT g hg` as an intermediate fact.

Take the linear combination `(1 - a) * this`. Establish `h1 : (1 : R) ∈ Ideal.span S` using `by rw [hspan]; trivial`. Take `⟨n, f, g, hf⟩` from `Submodule.mem_span_set'.mp h1`. Take `⟨G, hG, hGT⟩` from `hfin (Finset.univ.image fun i => (g i : R)) (by`. Introduce `y hy`.

Simplify using `only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy`. Take `⟨i, rfl⟩` from `hy`. Conclude with `(g i).2)`. Establish `hG1 : G = 1`. Establish `: (∑ i, f i • (g i : R)) * G = ∑ i, f i • (g i : R)`.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, hGT _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))]`. Rewrite `this` using `[hf, one_mul]`. Conclude with `this`.

Take `⟨x, hx⟩` from `hG.2`. Rewrite `hx` using `[hG1, one_mul]`. Establish `hxq : IsUnit (x ^ q)`. Use `hx.isUnit_add_left_of_commute u.isUnit (Commute.all _ _)` as an intermediate fact. Simplify using `using this`.

Establish `hxu : IsUnit x` using `(isUnit_pow_iff hq.ne').mp hxq`. Set `P : Polynomial R` to `Polynomial.X ^ q - Polynomial.C (u : R)`. Establish `hP : ∀ y : R, Polynomial.aeval y P = y ^ q - u`. Introduce `y`. Simplify using `[P]`.

Establish `hdP : Polynomial.aeval x (Polynomial.derivative P) = (q : R) * x ^ (q - 1)`. Simplify using `[P, Polynomial.derivative_X_pow]`. Take `⟨v, ⟨-, hv⟩, -⟩` from `Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero (P := P) (x := x) (by rw [hP]; exact hx) (by rw [hdP]; exact hqu.mul (hxu.pow _))`. Rewrite `hv` using `[hP, sub_eq_zero]`. Establish `hvu : IsUnit v` using `(isUnit_pow_iff hq.ne').mp (hv ▸ u.isUnit)`.

Conclude with `⟨hvu.unit, Units.ext (by simp [hv])⟩`.
-/
theorem exists_unit_pow_eq_of_krullDimLE_zero : ∀ (R : Type) [CommRing R] [Ring.KrullDimLE 0 R]
    (q : ℕ), 0 < q → IsUnit (q : R) → ∀ u : Rˣ,
    (∀ m : Ideal R, m.IsMaximal → ∃ x : R, x ^ q - (u : R) ∈ m) → ∃ v : Rˣ, v ^ q = u := by
  intro R _ _ q hq hqu u hloc
  have hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal := fun P hP => hP.isMaximal'
  let S : Set R := {g | IsIdempotentElem g ∧ ∃ x : R, IsNilpotent (g * (x ^ q - u))}
  have hjoin : ∀ g ∈ S, ∀ h ∈ S, g + h - g * h ∈ S := by
    rintro g ⟨hg, x, hx⟩ h ⟨hh, z, hz⟩
    refine ⟨?_, g * x + (1 - g) * z, ?_⟩
    · show (g + h - g * h) * (g + h - g * h) = g + h - g * h
      linear_combination (1 - 2 * h + h ^ 2) * hg.eq + (1 - g) * hh.eq
    · have key : (g + h - g * h) * ((g * x + (1 - g) * z) ^ q - u)
          = g * (x ^ q - u) + (1 - g) * (h * (z ^ q - u)) := by
        rw [pow_idempotent_combination hg]
        linear_combination (x ^ q - z ^ q - h * x ^ q + h * z ^ q) * hg.eq
      rw [key]
      exact Commute.isNilpotent_add (Commute.all _ _) hx ((Commute.all _ _).isNilpotent_mul_left (show IsNilpotent (h * (z ^ q - u)) from hz))
  have hcover : ∀ m : Ideal R, m.IsMaximal → ∃ g ∈ S, g ∉ m := by
    intro m hm
    obtain ⟨x, hx⟩ := hloc m hm
    obtain ⟨e, b, he, hab, hep⟩ := exists_isIdempotentElem_mul_of_forall_isMaximal hR (x ^ q - u)
    refine ⟨1 - e, ⟨he.one_sub, x, ?_⟩, ?_⟩
    · rw [nilpotent_iff_mem_prime]
      intro p hp
      by_cases ha : x ^ q - (u : R) ∈ p
      · exact p.mul_mem_left _ ha
      · have hep' := hep p hp ha
        have h0 : e * (1 - e) ∈ p := by
          have : e * (1 - e) = 0 := by linear_combination -he.eq
          rw [this]; exact p.zero_mem
        rcases hp.mem_or_mem h0 with h | h
        · exact absurd h hep'
        · exact p.mul_mem_right _ h
    · intro h
      have hem : e ∈ m := hab ▸ m.mul_mem_right b hx
      apply hm.ne_top
      rw [Ideal.eq_top_iff_one]
      simpa using m.add_mem h hem
  have hspan : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hgS, hgm⟩ := hcover m hm
    exact hgm (hle (Ideal.subset_span hgS))
  have hfin : ∀ T : Finset R, (↑T ⊆ S) → ∃ G ∈ S, ∀ g ∈ T, g * G = g := by
    classical
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨0, ⟨IsIdempotentElem.zero, 0, by simp⟩, by simp⟩
    | insert a T ha ih =>
      intro hT
      have haS : a ∈ S := hT (by simp)
      obtain ⟨G, hG, hGT⟩ := ih (fun y hy => hT (by simp [hy]))
      refine ⟨a + G - a * G, hjoin a haS G hG, ?_⟩
      intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · linear_combination (1 - G) * haS.1.eq
      · have := hGT g hg
        linear_combination (1 - a) * this
  have h1 : (1 : R) ∈ Ideal.span S := by rw [hspan]; trivial
  obtain ⟨n, f, g, hf⟩ := Submodule.mem_span_set'.mp h1
  classical
  obtain ⟨G, hG, hGT⟩ := hfin (Finset.univ.image fun i => (g i : R)) (by
    intro y hy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    exact (g i).2)
  have hG1 : G = 1 := by
    have : (∑ i, f i • (g i : R)) * G = ∑ i, f i • (g i : R) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, hGT _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))]
    rw [hf, one_mul] at this
    exact this
  obtain ⟨x, hx⟩ := hG.2
  rw [hG1, one_mul] at hx
  have hxq : IsUnit (x ^ q) := by
    have := hx.isUnit_add_left_of_commute u.isUnit (Commute.all _ _)
    simpa using this
  have hxu : IsUnit x := (isUnit_pow_iff hq.ne').mp hxq
  let P : Polynomial R := Polynomial.X ^ q - Polynomial.C (u : R)
  have hP : ∀ y : R, Polynomial.aeval y P = y ^ q - u := by
    intro y; simp [P]
  have hdP : Polynomial.aeval x (Polynomial.derivative P) = (q : R) * x ^ (q - 1) := by
    simp [P, Polynomial.derivative_X_pow]
  obtain ⟨v, ⟨-, hv⟩, -⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero (P := P) (x := x)
    (by rw [hP]; exact hx) (by rw [hdP]; exact hqu.mul (hxu.pow _))
  rw [hP, sub_eq_zero] at hv
  have hvu : IsUnit v := (isUnit_pow_iff hq.ne').mp (hv ▸ u.isUnit)
  exact ⟨hvu.unit, Units.ext (by simp [hv])⟩

end GlobalTheory
