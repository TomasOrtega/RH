import Mathlib
import Lemmata.GeneralBFactSecondVariant.Imports

namespace Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_second_variant.goal1 .. | (apply Bl.general_b_fact_second_variant.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_variant.goal1 <;> assumption)`.
-/
theorem card_eq_sq_fixed {k : Type*} [Field k] (τ : k →+* k) (hτ : ∀ x, τ (τ x) = x) (θ : k)
    (hθ : θ - τ θ ≠ 0) : Nat.card k = Nat.card {x : k // τ x = x} ^ 2 := by
  first | exact Bl.general_b_fact_second_variant.goal1 .. | (apply Bl.general_b_fact_second_variant.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_variant.goal1 <;> assumption)

variable {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} {σ : B →+* B}

/- English proof (translation)
Introduce `y` and use `⟨σ y, hσ y⟩`.
-/
theorem surj_of_invol (hσ : ∀ x, σ (σ x) = x) : Function.Surjective σ := fun y => ⟨σ y, hσ y⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Ideal.mem_comap, hσ]`.
-/
theorem comap_comap_invol (hσ : ∀ x, σ (σ x) = x) (P : Ideal B) : (P.comap σ).comap σ = P := by
  ext x
  simp only [Ideal.mem_comap, hσ]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Ideal.mem_comap, Ideal.mem_map_iff_of_surjective σ (surj_of_invol hσ)]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun hx => ⟨σ x, hx, hσ x⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Rewrite using `[hσ]` and apply the resulting hypothesis.
-/
theorem comap_eq_map_invol (hσ : ∀ x, σ (σ x) = x) (P : Ideal B) : P.comap σ = P.map σ := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_map_iff_of_surjective σ (surj_of_invol hσ)]
  constructor
  · exact fun hx => ⟨σ x, hx, hσ x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [hσ]

/- English proof (translation)
The claim follows from `Ideal.comap_isMaximal_of_surjective σ (surj_of_invol hσ)`.
-/
theorem comap_isMaximal_invol (hσ : ∀ x, σ (σ x) = x) {P : Ideal B} (hP : P.IsMaximal) :
    (P.comap σ).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective σ (surj_of_invol hσ)

/- English proof (translation)
Set `e : B ≃+* B` to `RingEquiv.ofBijective σ ⟨Function.Involutive.injective hσ, surj_of_invol hσ⟩`. Use `Nat.card_congr (Ideal.quotientEquiv (P.comap σ) P e ?_).toEquiv` and prove the remaining obligations. Conclude with `(Ideal.map_comap_of_surjective σ (surj_of_invol hσ) P).symm`.
-/
theorem card_quot_comap_invol (hσ : ∀ x, σ (σ x) = x) (P : Ideal B) :
    Nat.card (B ⧸ P.comap σ) = Nat.card (B ⧸ P) := by
  let e : B ≃+* B := RingEquiv.ofBijective σ
    ⟨Function.Involutive.injective hσ, surj_of_invol hσ⟩
  refine Nat.card_congr (Ideal.quotientEquiv (P.comap σ) P e ?_).toEquiv
  exact (Ideal.map_comap_of_surjective σ (surj_of_invol hσ) P).symm

/- English proof (translation)
The claim follows from `(hfix _).2 ⟨a, rfl⟩`.
-/
theorem fix_ι (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι) (a : A) : σ (ι a) = ι a :=
  (hfix _).2 ⟨a, rfl⟩

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [Ideal.mem_comap, fix_ι hfix]`.
-/
theorem comap_ι_comap (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι) (P : Ideal B) :
    (P.comap σ).comap ι = P.comap ι := by
  ext a
  simp only [Ideal.mem_comap, fix_ι hfix]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hP' : (P.comap σ).IsMaximal` using `comap_isMaximal_invol hσ hP`.

Establish `hout : ∀ R : Ideal B, R.IsMaximal → Q ≠ R → ∃ y ∈ Q, y ∉ R`. Introduce `R hR hQR`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hQR (hQ.eq_of_le hR.ne_top hc)`.

Take `⟨y, hyQ, hyP⟩` from `hout P hP hne.1`. Take `⟨z, hzQ, hzP'⟩` from `hout _ hP' hne.2`. Establish `hx : ∃ x ∈ Q, x ∉ P ∧ x ∉ P.comap σ`. Distinguish the cases in `hy' : y ∈ P.comap σ`. Distinguish the cases in `hz' : z ∈ P`.

Use `⟨y + z, Q.add_mem hyQ hzQ, fun h' => hyP ?_, fun h' => hzP' ?_⟩` and prove the remaining obligations. Simplify using `using P.sub_mem h' hz'`. Simplify using `using (P.comap σ).sub_mem h' hy'`. Conclude with `⟨z, hzQ, hz', hzP'⟩`. Conclude with `⟨y, hyQ, hyP, hy'⟩`.

Take `⟨x, hxQ, hxP, hxP'⟩` from `hx`. Establish `hfx : σ (x * σ x) = x * σ x` using `by rw [map_mul, hσ, mul_comm]`. Take `⟨a, ha⟩` from `(hfix _).1 hfx`. Establish `haQ : a ∈ Q.comap ι`. Rewrite using `[Ideal.mem_comap, ha]`.

Conclude with `Q.mul_mem_right _ hxQ`. Rewrite `haQ` using `[← h, Ideal.mem_comap, ha]`. Break down `hP.isPrime.mem_or_mem haQ with h1 | h1` into its components or cases. Conclude with `hxP h1`. Conclude with `hxP' h1`.

Introduce and unpack `(rfl | rfl)`. Both sides reduce to the same expression. Conclude with `(comap_ι_comap hfix P).symm`.
-/
theorem comap_eq_comap_iff (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P Q : Ideal B} (hP : P.IsMaximal) (hQ : Q.IsMaximal) :
    P.comap ι = Q.comap ι ↔ Q = P ∨ Q = P.comap σ := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have hP' : (P.comap σ).IsMaximal := comap_isMaximal_invol hσ hP

    have hout : ∀ R : Ideal B, R.IsMaximal → Q ≠ R → ∃ y ∈ Q, y ∉ R := by
      intro R hR hQR
      by_contra hc
      push_neg at hc
      exact hQR (hQ.eq_of_le hR.ne_top hc)
    obtain ⟨y, hyQ, hyP⟩ := hout P hP hne.1
    obtain ⟨z, hzQ, hzP'⟩ := hout _ hP' hne.2

    have hx : ∃ x ∈ Q, x ∉ P ∧ x ∉ P.comap σ := by
      by_cases hy' : y ∈ P.comap σ
      · by_cases hz' : z ∈ P
        · refine ⟨y + z, Q.add_mem hyQ hzQ, fun h' => hyP ?_, fun h' => hzP' ?_⟩
          · simpa using P.sub_mem h' hz'
          · simpa using (P.comap σ).sub_mem h' hy'
        · exact ⟨z, hzQ, hz', hzP'⟩
      · exact ⟨y, hyQ, hyP, hy'⟩
    obtain ⟨x, hxQ, hxP, hxP'⟩ := hx
    have hfx : σ (x * σ x) = x * σ x := by rw [map_mul, hσ, mul_comm]
    obtain ⟨a, ha⟩ := (hfix _).1 hfx
    have haQ : a ∈ Q.comap ι := by
      rw [Ideal.mem_comap, ha]
      exact Q.mul_mem_right _ hxQ
    rw [← h, Ideal.mem_comap, ha] at haQ
    rcases hP.isPrime.mem_or_mem haQ with h1 | h1
    · exact hxP h1
    · exact hxP' h1
  · rintro (rfl | rfl)
    · rfl
    · exact (comap_ι_comap hfix P).symm

/- English proof (translation)
Establish `hP' : (P.comap σ).IsMaximal` using `comap_isMaximal_invol hσ hP`. Establish `hsup : P ⊔ P.comap σ = ⊤`. Conclude with `Ideal.IsMaximal.coprime_of_ne hP hP' (Ne.symm hc)`. Take `⟨u, hu, v, hv, huv⟩` from `Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : B) ∈ P ⊔ P.comap σ)`. Rewrite `hv` using `[Ideal.mem_comap]`.

Establish `hfx : σ (b * v + σ (b * v)) = b * v + σ (b * v)` using `by rw [map_add, hσ, add_comm]`. Take `⟨a, ha⟩` from `(hfix _).1 hfx`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `hv' : v = 1 - u` using `by rw [← huv]; ring`. Establish `: b - ι a = b * u - σ b * σ v` using `by rw [ha, hv']; simp only [map_mul, map_sub, map_one]; ring`.

Rewrite using `[this]`. Conclude with `P.sub_mem (P.mul_mem_left _ hu) (P.mul_mem_left _ hv)`.
-/
theorem exists_sub_mem_of_split (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) (b : B) : ∃ a : A, b - ι a ∈ P := by
  have hP' : (P.comap σ).IsMaximal := comap_isMaximal_invol hσ hP
  have hsup : P ⊔ P.comap σ = ⊤ := by
    exact Ideal.IsMaximal.coprime_of_ne hP hP' (Ne.symm hc)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : B) ∈ P ⊔ P.comap σ)
  rw [Ideal.mem_comap] at hv
  have hfx : σ (b * v + σ (b * v)) = b * v + σ (b * v) := by rw [map_add, hσ, add_comm]
  obtain ⟨a, ha⟩ := (hfix _).1 hfx
  refine ⟨a, ?_⟩
  have hv' : v = 1 - u := by rw [← huv]; ring
  have : b - ι a = b * u - σ b * σ v := by rw [ha, hv']; simp only [map_mul, map_sub, map_one]; ring
  rw [this]
  exact P.sub_mem (P.mul_mem_left _ hu) (P.mul_mem_left _ hv)

/- English proof (translation)
Set `f : A ⧸ P.comap ι →+* B ⧸ P` to `Ideal.quotientMap P ι le_rfl`. Establish `hinj : Function.Injective f` using `Ideal.quotientMap_injective`. Establish `hsurj : Function.Surjective f`. Introduce `y`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Take `⟨a, ha⟩` from `exists_sub_mem_of_split hσ hfix hP hc b`. Use `⟨Ideal.Quotient.mk _ a, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.quotientMap_mk, Ideal.Quotient.eq]`. Simplify using `using P.neg_mem ha`. Conclude with `Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)`.
-/
theorem card_quot_split (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) :
    Nat.card (A ⧸ P.comap ι) = Nat.card (B ⧸ P) := by
  let f : A ⧸ P.comap ι →+* B ⧸ P := Ideal.quotientMap P ι le_rfl
  have hinj : Function.Injective f := Ideal.quotientMap_injective
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_sub_mem_of_split hσ hfix hP hc b
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    simpa using P.neg_mem ha
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

/- English proof (translation)
Introduce `hpr`. Establish `hP' : (P.comap σ).IsMaximal` using `comap_isMaximal_invol hσ hP`. Establish `hsup : P ⊔ P.comap σ = ⊤`. Conclude with `Ideal.IsMaximal.coprime_of_ne hP hP' (Ne.symm hc)`. Take `⟨u, hu, v, hv, huv⟩` from `Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : B) ∈ P ⊔ P.comap σ)`.

Establish `hu' : u ∉ P.comap σ`. Introduce `h`. Conclude with `hP'.ne_top ((Ideal.eq_top_iff_one _).2 (huv ▸ (P.comap σ).add_mem h hv))`. Establish `hle1 : (P.comap ι).map ι ≤ P` using `Ideal.map_comap_le`. Establish `hle2 : (P.comap ι).map ι ≤ P.comap σ`.

Rewrite using `[← comap_ι_comap hfix P]`. Conclude with `Ideal.map_comap_le`. Establish `hfx : σ (u * σ u) = u * σ u` using `by rw [map_mul, hσ, mul_comm]`. Take `⟨a, ha⟩` from `(hfix _).1 hfx`. Establish `hmem : u * σ u ∈ (P.comap ι).map ι`.

Rewrite using `[← ha]`. Use `Ideal.mem_map_of_mem _ ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, ha]`. Conclude with `P.mul_mem_right _ hu`. Break down `hpr.mem_or_mem hmem with h1 | h1` into its components or cases.

Conclude with `hu' (hle2 h1)`. Conclude with `hu' (by rw [Ideal.mem_comap]; exact hle1 h1)`.
-/
theorem not_isPrime_map_of_split (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) : ¬ ((P.comap ι).map ι).IsPrime := by
  intro hpr
  have hP' : (P.comap σ).IsMaximal := comap_isMaximal_invol hσ hP
  have hsup : P ⊔ P.comap σ = ⊤ := by
    exact Ideal.IsMaximal.coprime_of_ne hP hP' (Ne.symm hc)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : B) ∈ P ⊔ P.comap σ)
  have hu' : u ∉ P.comap σ := by
    intro h
    exact hP'.ne_top ((Ideal.eq_top_iff_one _).2 (huv ▸ (P.comap σ).add_mem h hv))
  have hle1 : (P.comap ι).map ι ≤ P := Ideal.map_comap_le
  have hle2 : (P.comap ι).map ι ≤ P.comap σ := by
    rw [← comap_ι_comap hfix P]
    exact Ideal.map_comap_le
  have hfx : σ (u * σ u) = u * σ u := by rw [map_mul, hσ, mul_comm]
  obtain ⟨a, ha⟩ := (hfix _).1 hfx
  have hmem : u * σ u ∈ (P.comap ι).map ι := by
    rw [← ha]
    refine Ideal.mem_map_of_mem _ ?_
    rw [Ideal.mem_comap, ha]
    exact P.mul_mem_right _ hu
  rcases hpr.mem_or_mem hmem with h1 | h1
  · exact hu' (hle2 h1)
  · exact hu' (by rw [Ideal.mem_comap]; exact hle1 h1)

end Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
