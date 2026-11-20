import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMEulerProducts.StepRegroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDegreeEquality.FinrankEqTwo

open NumberField

noncomputable section

namespace CMEulFib

open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory

/- English proof (translation)
The claim follows from `σ.symm_apply_eq.mpr (hinv x).symm`.
-/
theorem symm_eq {B : Type*} [CommRing B] (σ : B ≃+* B) (hinv : ∀ x, σ (σ x) = x) (x : B) :
    σ.symm x = σ x :=
  σ.symm_apply_eq.mpr (hinv x).symm

/- English proof (translation)
Rewrite using `[← Ideal.symm_apply_mem_of_equiv_iff, symm_eq σ hinv]`.
-/
theorem mem_map_iff {B : Type*} [CommRing B] (σ : B ≃+* B) (hinv : ∀ x, σ (σ x) = x)
    (P : Ideal B) (y : B) : y ∈ P.map σ ↔ σ y ∈ P := by
  rw [← Ideal.symm_apply_mem_of_equiv_iff, symm_eq σ hinv]

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[mem_map_iff σ hinv, mem_map_iff σ hinv, hinv]`.
-/
theorem map_map_self {B : Type*} [CommRing B] (σ : B ≃+* B) (hinv : ∀ x, σ (σ x) = x)
    (P : Ideal B) : (P.map σ).map σ = P := by
  ext y
  rw [mem_map_iff σ hinv, mem_map_iff σ hinv, hinv]

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, mem_map_iff σ hinv, hfix]`.
-/
theorem comap_map_eq {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (σ : B ≃+* B)
    (hinv : ∀ x, σ (σ x) = x) (hfix : ∀ y : A, σ (algebraMap A B y) = algebraMap A B y)
    (P : Ideal B) : (P.map σ).comap (algebraMap A B) = P.comap (algebraMap A B) := by
  ext y
  rw [Ideal.mem_comap, Ideal.mem_comap, mem_map_iff σ hinv, hfix]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Take `⟨h1, h2⟩` from `h`. Establish `hσP : (P.map σ).IsMaximal` using `Ideal.map_isMaximal_of_equiv σ`. Establish `ha : ¬ Q ≤ P` using `fun hle => h1 (hQ.eq_of_le hP.ne_top hle)`.

Establish `hb : ¬ Q ≤ P.map σ` using `fun hle => h2 (hQ.eq_of_le hσP.ne_top hle)`. Take `⟨a, haQ, haP⟩` from `SetLike.not_le_iff_exists.mp ha`. Take `⟨b, hbQ, hbP⟩` from `SetLike.not_le_iff_exists.mp hb`. Choose the witnesses or unpack the hypotheses as in `⟨x, hxQ, hxP, hxσ⟩ : ∃ x ∈ Q, x ∉ P ∧ x ∉ P.map σ := by`. Distinguish the cases in `h3 : a ∈ P.map σ`.

Distinguish the cases in `h4 : b ∈ P`. Use `⟨a + b, Q.add_mem haQ hbQ, fun h => haP ?_, fun h => hbP ?_⟩` and prove the remaining obligations. Simplify using `using P.sub_mem h h4`. Simplify using `using (P.map σ).sub_mem h h3`. Conclude with `⟨b, hbQ, h4, hbP⟩`.

Conclude with `⟨a, haQ, haP, h3⟩`. Establish `hfx : σ (x * σ x) = x * σ x` using `by rw [map_mul, hinv, mul_comm]`. Take `⟨y, hy⟩` from `hfix _ hfx`. Establish `hyQ : y ∈ Q.comap (algebraMap A B)`. Rewrite using `[Ideal.mem_comap, hy]`.

Conclude with `Q.mul_mem_right _ hxQ`. Rewrite `hyQ` using `[hPQ, Ideal.mem_comap, hy]`. Break down `hP.isPrime.mem_or_mem hyQ with h5 | h5` into its components or cases. Conclude with `hxP h5`. Conclude with `hxσ ((mem_map_iff σ hinv P x).mpr h5)`.
-/
theorem eq_or_eq_map {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (σ : B ≃+* B)
    (hinv : ∀ x, σ (σ x) = x) (hfix : ∀ x : B, σ x = x → x ∈ Set.range (algebraMap A B))
    (P Q : Ideal B) [hP : P.IsMaximal] [hQ : Q.IsMaximal]
    (hPQ : Q.comap (algebraMap A B) = P.comap (algebraMap A B)) :
    Q = P ∨ Q = P.map σ := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hσP : (P.map σ).IsMaximal := Ideal.map_isMaximal_of_equiv σ
  have ha : ¬ Q ≤ P := fun hle => h1 (hQ.eq_of_le hP.ne_top hle)
  have hb : ¬ Q ≤ P.map σ := fun hle => h2 (hQ.eq_of_le hσP.ne_top hle)
  obtain ⟨a, haQ, haP⟩ := SetLike.not_le_iff_exists.mp ha
  obtain ⟨b, hbQ, hbP⟩ := SetLike.not_le_iff_exists.mp hb
  obtain ⟨x, hxQ, hxP, hxσ⟩ : ∃ x ∈ Q, x ∉ P ∧ x ∉ P.map σ := by
    by_cases h3 : a ∈ P.map σ
    · by_cases h4 : b ∈ P
      · refine ⟨a + b, Q.add_mem haQ hbQ, fun h => haP ?_, fun h => hbP ?_⟩
        · simpa using P.sub_mem h h4
        · simpa using (P.map σ).sub_mem h h3
      · exact ⟨b, hbQ, h4, hbP⟩
    · exact ⟨a, haQ, haP, h3⟩
  have hfx : σ (x * σ x) = x * σ x := by rw [map_mul, hinv, mul_comm]
  obtain ⟨y, hy⟩ := hfix _ hfx
  have hyQ : y ∈ Q.comap (algebraMap A B) := by
    rw [Ideal.mem_comap, hy]
    exact Q.mul_mem_right _ hxQ
  rw [hPQ, Ideal.mem_comap, hy] at hyQ
  rcases hP.isPrime.mem_or_mem hyQ with h5 | h5
  · exact hxP h5
  · exact hxσ ((mem_map_iff σ hinv P x).mpr h5)

end CMEulFib

namespace CMEulFib

open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory

/- English proof (translation)
Establish `hfixA : ∀ y : 𝓞 F, σ (algebraMap (𝓞 F) (𝓞 E) y) = algebraMap (𝓞 F) (𝓞 E) y` using `fun y => (hrange _).mpr ⟨y, rfl⟩`. Establish `hfix : ∀ x : 𝓞 E, σ x = x → x ∈ Set.range (algebraMap (𝓞 F) (𝓞 E))` using `fun x hx => (hrange x).mp hx`. Establish `hdeg : Module.finrank (𝓞 F) (𝓞 E) = 2`. Rewrite using `[← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]`. Conclude with `CMDeg.finrank_eq_two hFE`.

Take `⟨P, hPmax, hPv⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v`. Establish `hPc : P.comap (algebraMap (𝓞 F) (𝓞 E)) = v` using `hPv.over.symm`. Establish `: Fintype (v.primesOver (𝓞 E))` using `Fintype.ofFinite _`. Establish `hsum` using `Ideal.sum_ramification_inertia_eq_finrank v (𝓞 E)`. Rewrite `hsum` using `[hdeg]`.

Establish `hmem : ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v → Q = P ∨ Q = P.map σ`. Introduce `Q hQ hQv`. Conclude with `eq_or_eq_map σ hinv hfix P Q (by rw [hQv, hPc])`. Establish `hσPc : (P.map σ).comap (algebraMap (𝓞 F) (𝓞 E)) = v`. Rewrite using `[comap_map_eq σ hinv hfixA, hPc]`.

Establish `hσPmax : (P.map σ).IsMaximal` using `Ideal.map_isMaximal_of_equiv σ`. Establish `hσPv : (P.map σ).LiesOver v` using `⟨hσPc.symm⟩`. Establish `hpos : ∀ q : v.primesOver (𝓞 E), 1 ≤ q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F)`. Introduce `q`. Use `q.2.1` as an intermediate fact.

Conclude with `Nat.mul_pos (Ideal.ramificationIdx_pos q.1 (𝓞 F)) (Ideal.inertiaDeg_pos q.1 (𝓞 F))`. Set `p0 : v.primesOver (𝓞 E)` to `⟨P, hPmax.isPrime, hPv⟩`. Distinguish the cases in `hfixP : P.map σ = P`. Use `left`. Establish `hone : ∀ q : v.primesOver (𝓞 E), q = p0`.

Introduce and unpack `⟨q, hq1, hq2⟩`. Use `hq1` as an intermediate fact. Use `hq2` as an intermediate fact. Establish `hqmax : q.IsMaximal` using `Ideal.IsMaximal.of_liesOver_isMaximal q v`. Apply `Subtype.ext` to reduce the goal to its premises.

Break down `hmem q hqmax hq2.over.symm with h | h` into its components or cases. Conclude with `h`. Conclude with `h.trans hfixP`. Establish `h2 : P.ramificationIdx (𝓞 F) * P.inertiaDeg (𝓞 F) = 2`. Rewrite using `[← hsum, Fintype.sum_eq_single p0 (fun q hq => absurd (hone q) hq)]`.

Establish `hf1 : P.inertiaDeg (𝓞 F) ≠ 1`. Introduce `hf`. Set `: Field (𝓞 F ⧸ v)` to `Ideal.Quotient.field v`. Set `: Field (𝓞 E ⧸ P)` to `Ideal.Quotient.field P`. Rewrite `hf` using `[Ideal.inertiaDeg_eq_of_isMaximal v P]`.

Establish `hbij` using `(Algebra.finrank_eq_one_iff_bijective_algebraMap).mp hf`. Take `⟨θ, hθ⟩` from `hunr P hPmax`. Take `⟨a, ha⟩` from `hbij.2 (Ideal.Quotient.mk P θ)`. Take `⟨a', rfl⟩` from `Ideal.Quotient.mk_surjective a`. Rewrite `ha` using `[Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.eq]`.

Establish `hz : θ - algebraMap (𝓞 F) (𝓞 E) a' ∈ P`. Use `P.neg_mem ha` as an intermediate fact. Simplify using `using this`. Establish `hz' : σ (θ - algebraMap (𝓞 F) (𝓞 E) a') ∈ P`. Rewrite using `[← mem_map_iff σ hinv, hfixP]`.

Conclude with `hz`. Rewrite `hz'` using `[map_sub, hfixA]`. Apply `hθ` to reduce the goal to its premises. Use `P.sub_mem hz hz'` as an intermediate fact. Simplify using `using this`.

Establish `hfpos : 0 < P.inertiaDeg (𝓞 F)` using `Ideal.inertiaDeg_pos P (𝓞 F)`. Establish `hfle : P.inertiaDeg (𝓞 F) ≤ 2` using `Nat.le_of_dvd (by norm_num) (Dvd.intro_left _ h2)`. Establish `hf2 : P.inertiaDeg (𝓞 F) = 2` using `by omega`. Use `⟨P, hPmax, hPc, by rw [hconj, hfixP], ?_, fun Q hQ hQv => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.absNorm_pow_inertiaDeg v P, hf2]`.

Break down `hmem Q hQ hQv with h | h` into its components or cases. Conclude with `h`. Conclude with `h.trans hfixP`. Use `right`. Set `p1 : v.primesOver (𝓞 E)` to `⟨P.map σ, hσPmax.isPrime, hσPv⟩`.

Establish `hne : p0 ≠ p1` using `fun h => hfixP (congrArg Subtype.val h).symm`. Establish `hle : (p0.1.ramificationIdx (𝓞 F) * p0.1.inertiaDeg (𝓞 F)) + (p1.1.ramificationIdx (𝓞 F) * p1.1.inertiaDeg (𝓞 F)) ≤ 2`. Rewrite using `[← hsum, ← Finset.sum_pair (f := fun q : v.primesOver (𝓞 E) => q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F)) hne]`. Conclude with `Finset.sum_le_sum_of_subset (Finset.subset_univ _)`. Establish `h0` using `hpos p0`.

Establish `h1` using `hpos p1`. Establish `hf0 : p0.1.inertiaDeg (𝓞 F) = 1`. Establish `hm : p0.1.ramificationIdx (𝓞 F) * p0.1.inertiaDeg (𝓞 F) = 1` using `by omega`. Use `Nat.le_of_dvd one_pos (Dvd.intro_left _ hm)` as an intermediate fact. Use `Ideal.inertiaDeg_pos p0.1 (𝓞 F)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hf1 : p1.1.inertiaDeg (𝓞 F) = 1`. Establish `hm : p1.1.ramificationIdx (𝓞 F) * p1.1.inertiaDeg (𝓞 F) = 1` using `by omega`. Use `Nat.le_of_dvd one_pos (Dvd.intro_left _ hm)` as an intermediate fact. Use `Ideal.inertiaDeg_pos p1.1 (𝓞 F)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `⟨P, P.map σ, hPmax, hσPmax, hPc, hσPc, Ne.symm hfixP, hconj P, by rw [hconj, map_map_self σ hinv], ?_, ?_, fun R hR hRv => hmem R hR hRv⟩` and prove the remaining obligations. Rewrite using `[← Ideal.absNorm_pow_inertiaDeg v P]`. Simplify using `only [p0] at hf0`. Rewrite using `[hf0, pow_one]`.

Rewrite using `[← Ideal.absNorm_pow_inertiaDeg v (P.map σ)]`. Simplify using `only [p1] at hf1`. Rewrite using `[hf1, pow_one]`.
-/
theorem fibreShape_of (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hFE : IsCMPair F E) (σ : 𝓞 E ≃+* 𝓞 E)
    (hinv : ∀ x : 𝓞 E, σ (σ x) = x)
    (hconj : ∀ P : Ideal (𝓞 E), conjIdeal (K := E) P = P.map σ)
    (hrange : ∀ x : 𝓞 E, σ x = x ↔ x ∈ Set.range (algebraMap (𝓞 F) (𝓞 E)))
    (hunr : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ : 𝓞 E, θ - σ θ ∉ P)
    (v : Ideal (𝓞 F)) (hv : v.IsMaximal) : CMEul.FibreShape F E v := by
  classical
  have hfixA : ∀ y : 𝓞 F, σ (algebraMap (𝓞 F) (𝓞 E) y) = algebraMap (𝓞 F) (𝓞 E) y :=
    fun y => (hrange _).mpr ⟨y, rfl⟩
  have hfix : ∀ x : 𝓞 E, σ x = x → x ∈ Set.range (algebraMap (𝓞 F) (𝓞 E)) :=
    fun x hx => (hrange x).mp hx
  have hdeg : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact CMDeg.finrank_eq_two hFE
  obtain ⟨P, hPmax, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v
  have hPc : P.comap (algebraMap (𝓞 F) (𝓞 E)) = v := hPv.over.symm
  have : Fintype (v.primesOver (𝓞 E)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v (𝓞 E)
  rw [hdeg] at hsum
  have hmem : ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v →
      Q = P ∨ Q = P.map σ := by
    intro Q hQ hQv
    exact eq_or_eq_map σ hinv hfix P Q (by rw [hQv, hPc])
  have hσPc : (P.map σ).comap (algebraMap (𝓞 F) (𝓞 E)) = v := by
    rw [comap_map_eq σ hinv hfixA, hPc]
  have hσPmax : (P.map σ).IsMaximal := Ideal.map_isMaximal_of_equiv σ
  have hσPv : (P.map σ).LiesOver v := ⟨hσPc.symm⟩
  have hpos : ∀ q : v.primesOver (𝓞 E),
      1 ≤ q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) := by
    intro q
    have := q.2.1
    exact Nat.mul_pos (Ideal.ramificationIdx_pos q.1 (𝓞 F)) (Ideal.inertiaDeg_pos q.1 (𝓞 F))
  let p0 : v.primesOver (𝓞 E) := ⟨P, hPmax.isPrime, hPv⟩
  by_cases hfixP : P.map σ = P
  · left
    have hone : ∀ q : v.primesOver (𝓞 E), q = p0 := by
      rintro ⟨q, hq1, hq2⟩
      have := hq1
      have := hq2
      have hqmax : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q v
      apply Subtype.ext
      rcases hmem q hqmax hq2.over.symm with h | h
      · exact h
      · exact h.trans hfixP
    have h2 : P.ramificationIdx (𝓞 F) * P.inertiaDeg (𝓞 F) = 2 := by
      rw [← hsum, Fintype.sum_eq_single p0 (fun q hq => absurd (hone q) hq)]
    have hf1 : P.inertiaDeg (𝓞 F) ≠ 1 := by
      intro hf
      let : Field (𝓞 F ⧸ v) := Ideal.Quotient.field v
      let : Field (𝓞 E ⧸ P) := Ideal.Quotient.field P
      rw [Ideal.inertiaDeg_eq_of_isMaximal v P] at hf
      have hbij := (Algebra.finrank_eq_one_iff_bijective_algebraMap).mp hf
      obtain ⟨θ, hθ⟩ := hunr P hPmax
      obtain ⟨a, ha⟩ := hbij.2 (Ideal.Quotient.mk P θ)
      obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.eq] at ha
      have hz : θ - algebraMap (𝓞 F) (𝓞 E) a' ∈ P := by
        have := P.neg_mem ha
        simpa using this
      have hz' : σ (θ - algebraMap (𝓞 F) (𝓞 E) a') ∈ P := by
        rw [← mem_map_iff σ hinv, hfixP]
        exact hz
      rw [map_sub, hfixA] at hz'
      apply hθ
      have := P.sub_mem hz hz'
      simpa using this
    have hfpos : 0 < P.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos P (𝓞 F)
    have hfle : P.inertiaDeg (𝓞 F) ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (Dvd.intro_left _ h2)
    have hf2 : P.inertiaDeg (𝓞 F) = 2 := by omega
    refine ⟨P, hPmax, hPc, by rw [hconj, hfixP], ?_, fun Q hQ hQv => ?_⟩
    · rw [← Ideal.absNorm_pow_inertiaDeg v P, hf2]
    · rcases hmem Q hQ hQv with h | h
      · exact h
      · exact h.trans hfixP
  · right
    let p1 : v.primesOver (𝓞 E) := ⟨P.map σ, hσPmax.isPrime, hσPv⟩
    have hne : p0 ≠ p1 := fun h => hfixP (congrArg Subtype.val h).symm
    have hle : (p0.1.ramificationIdx (𝓞 F) * p0.1.inertiaDeg (𝓞 F)) +
        (p1.1.ramificationIdx (𝓞 F) * p1.1.inertiaDeg (𝓞 F)) ≤ 2 := by
      rw [← hsum, ← Finset.sum_pair (f := fun q : v.primesOver (𝓞 E) =>
        q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F)) hne]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h0 := hpos p0
    have h1 := hpos p1
    have hf0 : p0.1.inertiaDeg (𝓞 F) = 1 := by
      have hm : p0.1.ramificationIdx (𝓞 F) * p0.1.inertiaDeg (𝓞 F) = 1 := by omega
      have := Nat.le_of_dvd one_pos (Dvd.intro_left _ hm)
      have := Ideal.inertiaDeg_pos p0.1 (𝓞 F)
      omega
    have hf1 : p1.1.inertiaDeg (𝓞 F) = 1 := by
      have hm : p1.1.ramificationIdx (𝓞 F) * p1.1.inertiaDeg (𝓞 F) = 1 := by omega
      have := Nat.le_of_dvd one_pos (Dvd.intro_left _ hm)
      have := Ideal.inertiaDeg_pos p1.1 (𝓞 F)
      omega
    refine ⟨P, P.map σ, hPmax, hσPmax, hPc, hσPc, Ne.symm hfixP, hconj P,
      by rw [hconj, map_map_self σ hinv], ?_, ?_, fun R hR hRv => hmem R hR hRv⟩
    · rw [← Ideal.absNorm_pow_inertiaDeg v P]
      simp only [p0] at hf0
      rw [hf0, pow_one]
    · rw [← Ideal.absNorm_pow_inertiaDeg v (P.map σ)]
      simp only [p1] at hf1
      rw [hf1, pow_one]

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hFE v hv`. Take `⟨σ, -, hinv, hconj, hrange, hunr⟩` from `h F E hFE`. Conclude with `fibreShape_of F E hFE σ hinv hconj hrange hunr v hv`.
-/
theorem stepFib_of (h : CMEul.StepConj) : CMEul.StepFib := by
  intro F E _ _ _ _ _ _ hFE v hv
  obtain ⟨σ, -, hinv, hconj, hrange, hunr⟩ := h F E hFE
  exact fibreShape_of F E hFE σ hinv hconj hrange hunr v hv

end CMEulFib
