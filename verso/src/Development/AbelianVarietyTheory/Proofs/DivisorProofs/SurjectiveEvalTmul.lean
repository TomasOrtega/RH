import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SurjTens

variable {O σ ι : Type} [CommRing O]

open Classical in

def pushVars (j : σ → ι) (f : MvPowerSeries σ O) : MvPowerSeries ι O :=
  fun β => if h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β then coeff h.choose f else 0

/- English proof (translation)
Establish `h : ∃ α' : σ →₀ ℕ, Finsupp.mapDomain j α' = Finsupp.mapDomain j α` using `⟨α, rfl⟩`. Rewrite using `[coeff_apply]`. Unfold `pushVars`. Rewrite using `[dif_pos h, Finsupp.mapDomain_injective hj h.choose_spec]`.
-/
theorem coeff_pushVars_mapDomain {j : σ → ι} (hj : Function.Injective j) (f : MvPowerSeries σ O)
    (α : σ →₀ ℕ) : coeff (Finsupp.mapDomain j α) (pushVars j f) = coeff α f := by
  have h : ∃ α' : σ →₀ ℕ, Finsupp.mapDomain j α' = Finsupp.mapDomain j α := ⟨α, rfl⟩
  rw [coeff_apply]
  unfold pushVars
  rw [dif_pos h, Finsupp.mapDomain_injective hj h.choose_spec]

/- English proof (translation)
Rewrite using `[coeff_apply]`. Unfold `pushVars`. Rewrite using `[dif_neg h]`.
-/
theorem coeff_pushVars_of_not {j : σ → ι} (f : MvPowerSeries σ O) (β : ι →₀ ℕ)
    (h : ¬∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β) : coeff β (pushVars j f) = 0 := by
  rw [coeff_apply]
  unfold pushVars
  rw [dif_neg h]

/- English proof (translation)
Use extensionality with `β`. Distinguish the cases in `h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β`. Take `⟨α, rfl⟩` from `h`. Simplify using `only [map_add, coeff_pushVars_mapDomain hj]`. Simplify using `only [map_add, coeff_pushVars_of_not _ _ h, add_zero]`.
-/
theorem pushVars_add {j : σ → ι} (hj : Function.Injective j) (f g : MvPowerSeries σ O) :
    pushVars j (f + g) = pushVars j f + pushVars j g := by
  ext β
  by_cases h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β
  · obtain ⟨α, rfl⟩ := h
    simp only [map_add, coeff_pushVars_mapDomain hj]
  · simp only [map_add, coeff_pushVars_of_not _ _ h, add_zero]

/- English proof (translation)
Use extensionality with `β`. Distinguish the cases in `h : ∃ α' : σ →₀ ℕ, Finsupp.mapDomain j α' = β`. Take `⟨α', rfl⟩` from `h`. Rewrite using `[coeff_pushVars_mapDomain hj, coeff_monomial, coeff_monomial]`. Simplify using `only [(Finsupp.mapDomain_injective hj).eq_iff]`.

Rewrite using `[coeff_pushVars_of_not _ _ h, coeff_monomial, if_neg]`. Introduce and unpack `rfl`. Conclude with `h ⟨α, rfl⟩`.
-/
theorem pushVars_monomial {j : σ → ι} (hj : Function.Injective j) (α : σ →₀ ℕ) (c : O) :
    pushVars j (monomial α c) = monomial (Finsupp.mapDomain j α) c := by
  classical
  ext β
  by_cases h : ∃ α' : σ →₀ ℕ, Finsupp.mapDomain j α' = β
  · obtain ⟨α', rfl⟩ := h
    rw [coeff_pushVars_mapDomain hj, coeff_monomial, coeff_monomial]
    simp only [(Finsupp.mapDomain_injective hj).eq_iff]
  · rw [coeff_pushVars_of_not _ _ h, coeff_monomial, if_neg]
    rintro rfl
    exact h ⟨α, rfl⟩

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Rewrite using `[MvPolynomial.coe_monomial, MvPolynomial.rename_monomial, MvPolynomial.coe_monomial, pushVars_monomial hj]`. Consider the case `add P Q hP hQ`. Rewrite using `[MvPolynomial.coe_add, pushVars_add hj, hP, hQ, map_add, MvPolynomial.coe_add]`.
-/
theorem pushVars_coe {j : σ → ι} (hj : Function.Injective j) (P : MvPolynomial σ O) :
    pushVars j (P : MvPowerSeries σ O) = ((MvPolynomial.rename j P : MvPolynomial ι O) : MvPowerSeries ι O) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [MvPolynomial.coe_monomial, MvPolynomial.rename_monomial, MvPolynomial.coe_monomial,
      pushVars_monomial hj]
  | add P Q hP hQ =>
    rw [MvPolynomial.coe_add, pushVars_add hj, hP, hQ, map_add, MvPolynomial.coe_add]

/- English proof (translation)
Establish `h : E.comp (MvPolynomial.coeToMvPowerSeries.algHom R) = MvPolynomial.aeval z`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `[MvPolynomial.coeToMvPowerSeries.algHom_apply, hE i]`. Use `congrArg (fun φ => φ P) h` as an intermediate fact.

Simplify `this` using `[MvPolynomial.coeToMvPowerSeries.algHom_apply]`.
-/
theorem eval_coe {R A κ : Type} [CommRing R] [CommRing A] [Algebra R A] (z : κ → A)
    (E : MvPowerSeries κ R →ₐ[R] A) (hE : ∀ i, E (X i) = z i) (P : MvPolynomial κ R) :
    E (P : MvPowerSeries κ R) = MvPolynomial.aeval z P := by
  have h : E.comp (MvPolynomial.coeToMvPowerSeries.algHom R) = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, hE i]
  have := congrArg (fun φ => φ P) h
  simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this

/- English proof (translation)
Establish `hpoly : ∀ P : MvPolynomial σ O, E (pushVars j (P : MvPowerSeries σ O)) = φ (evA P)`. Introduce `P`. Rewrite using `[pushVars_coe hj, eval_coe z E hE.1, eval_coe x evA hA.1, MvPolynomial.aeval_rename]`. Rewrite using `[← AlgHom.comp_apply, MvPolynomial.comp_aeval]`. Establish `hzj : z ∘ j = fun i => φ (x i)` using `funext hz`.

Rewrite using `[hzj]`. Use `sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {(p : C)}) inferInstance _ fun m => ?_)` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨N1, hN1⟩` from `hE.2 m`. Take `⟨N2, hN2⟩` from `hA.2 m`.

Use `set N := max N1 N2`. Use `set n : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N`. Use `set P : MvPolynomial σ O := trunc' O n f`. Use `set g : MvPowerSeries σ O := f - (P : MvPowerSeries σ O)`. Establish `hg : ∀ α : σ →₀ ℕ, α.degree < N → coeff α g = 0`.

Introduce `α hα`. Establish `hle : α ≤ n`. Introduce `i`. Establish `h1 : α i ≤ α.degree`. Rewrite using `[Finsupp.degree]`.

Distinguish the cases in `hi : i ∈ α.support`. Conclude with `Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi`. Simplify using `[Finsupp.notMem_support_iff.1 hi]`. Use `show α i ≤ N`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos hle, sub_self]`. Establish `hgA : (p : A) ^ m ∣ evA g` using `hN2 g fun α hα => hg α (lt_of_lt_of_le hα (le_max_right _ _))`. Establish `hgE : (p : C) ^ m ∣ E (pushVars j g)`. Apply `hN1` to reduce the goal to its premises. Introduce `β hβ`.

Distinguish the cases in `h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β`. Take `⟨α, rfl⟩` from `h`. Rewrite using `[coeff_pushVars_mapDomain hj]`. Apply `hg` to reduce the goal to its premises. Rewrite `hβ` using `[Finsupp.degree_mapDomain]`.

Conclude with `lt_of_lt_of_le hβ (le_max_left _ _)`. Conclude with `coeff_pushVars_of_not _ _ h`. Establish `hgφ : (p : C) ^ m ∣ φ (evA g)`. Use `map_dvd φ hgA` as an intermediate fact. Simplify `this` using `only [map_pow, map_natCast]`.

Establish `hf : f = g + (P : MvPowerSeries σ O)` using `by simp [g]`. Establish `key : E (pushVars j f) - φ (evA f) = E (pushVars j g) - φ (evA g)`. Rewrite using `[hf, pushVars_add hj, map_add, map_add, map_add, hpoly P]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Conclude with `dvd_sub hgE hgφ`.
-/
theorem exists_eval_pushVars (p : ℕ) {A C : Type} [CommRing A] [CommRing C] [Algebra O A] [Algebra O C]
    [Fintype σ] [IsHausdorff (Ideal.span {(p : C)}) C] (j : σ → ι) (hj : Function.Injective j)
    (x : σ → A) (z : ι → C) (φ : A →ₐ[O] C) (evA : MvPowerSeries σ O →ₐ[O] A)
    (E : MvPowerSeries ι O →ₐ[O] C) (hA : IsEval p x evA) (hE : IsEval p z E)
    (hz : ∀ i, z (j i) = φ (x i)) (f : MvPowerSeries σ O) :
    E (pushVars j f) = φ (evA f) := by
  classical
  have hpoly : ∀ P : MvPolynomial σ O, E (pushVars j (P : MvPowerSeries σ O)) = φ (evA P) := by
    intro P
    rw [pushVars_coe hj, eval_coe z E hE.1, eval_coe x evA hA.1, MvPolynomial.aeval_rename]
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have hzj : z ∘ j = fun i => φ (x i) := funext hz
    rw [hzj]
  refine sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {(p : C)}) inferInstance _ fun m => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨N1, hN1⟩ := hE.2 m
  obtain ⟨N2, hN2⟩ := hA.2 m
  set N := max N1 N2
  set n : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  set P : MvPolynomial σ O := trunc' O n f
  set g : MvPowerSeries σ O := f - (P : MvPowerSeries σ O)
  have hg : ∀ α : σ →₀ ℕ, α.degree < N → coeff α g = 0 := by
    intro α hα
    have hle : α ≤ n := by
      intro i
      have h1 : α i ≤ α.degree := by
        rw [Finsupp.degree]
        by_cases hi : i ∈ α.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · simp [Finsupp.notMem_support_iff.1 hi]
      show α i ≤ N
      omega
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos hle, sub_self]
  have hgA : (p : A) ^ m ∣ evA g := hN2 g fun α hα => hg α (lt_of_lt_of_le hα (le_max_right _ _))
  have hgE : (p : C) ^ m ∣ E (pushVars j g) := by
    apply hN1
    intro β hβ
    by_cases h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β
    · obtain ⟨α, rfl⟩ := h
      rw [coeff_pushVars_mapDomain hj]
      apply hg
      rw [Finsupp.degree_mapDomain] at hβ
      exact lt_of_lt_of_le hβ (le_max_left _ _)
    · exact coeff_pushVars_of_not _ _ h
  have hgφ : (p : C) ^ m ∣ φ (evA g) := by
    have := map_dvd φ hgA
    simpa only [map_pow, map_natCast] using this
  have hf : f = g + (P : MvPowerSeries σ O) := by simp [g]
  have key : E (pushVars j f) - φ (evA f) = E (pushVars j g) - φ (evA g) := by
    rw [hf, pushVars_add hj, map_add, map_add, map_add, hpoly P]
    ring
  rw [key]
  exact dvd_sub hgE hgφ

/- English proof (translation)
Introduce `p O A B σ τ _ _ _ _ _ _ _ _ x y evA evB E hA hB hE sA sB`. Establish `hl : ∀ a : A, a ⊗ₜ[O] (1 : B) ∈ E.range`. Introduce `a`. Take `⟨f, rfl⟩` from `sA a`. Use `⟨pushVars Sum.inl f, ?_⟩` and prove the remaining obligations.

Use `exists_eval_pushVars p Sum.inl Sum.inl_injective x _ Algebra.TensorProduct.includeLeft evA E hA hE (fun i => by simp) f` as an intermediate fact. Simplify using `using this`. Establish `hr : ∀ b : B, (1 : A) ⊗ₜ[O] b ∈ E.range`. Introduce `b`. Take `⟨g, rfl⟩` from `sB b`.

Use `⟨pushVars Sum.inr g, ?_⟩` and prove the remaining obligations. Use `exists_eval_pushVars p Sum.inr Sum.inr_injective y _ Algebra.TensorProduct.includeRight evB E hB hE (fun i => by simp) g` as an intermediate fact. Simplify using `using this`. Introduce `t`. Establish `: t ∈ E.range`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact Subalgebra.zero_mem _`. Consider the case `tmul a b`. Establish `h` using `Subalgebra.mul_mem _ (hl a) (hr b)`. Rewrite `h` using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Then use the resulting hypothesis.

Consider the case `add s t hs ht => exact Subalgebra.add_mem _ hs ht`. Conclude with `this`.
-/
theorem surjective_eval_tmul : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] [IsHausdorff (Ideal.span {(p : A ⊗[O] B)}) (A ⊗[O] B)] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → Function.Surjective E := by
  intro p O A B σ τ _ _ _ _ _ _ _ _ x y evA evB E hA hB hE sA sB
  have hl : ∀ a : A, a ⊗ₜ[O] (1 : B) ∈ E.range := by
    intro a
    obtain ⟨f, rfl⟩ := sA a
    refine ⟨pushVars Sum.inl f, ?_⟩
    have := exists_eval_pushVars p Sum.inl Sum.inl_injective x _ Algebra.TensorProduct.includeLeft
      evA E hA hE (fun i => by simp) f
    simpa using this
  have hr : ∀ b : B, (1 : A) ⊗ₜ[O] b ∈ E.range := by
    intro b
    obtain ⟨g, rfl⟩ := sB b
    refine ⟨pushVars Sum.inr g, ?_⟩
    have := exists_eval_pushVars p Sum.inr Sum.inr_injective y _ Algebra.TensorProduct.includeRight
      evB E hB hE (fun i => by simp) g
    simpa using this
  intro t
  have : t ∈ E.range := by
    induction t using TensorProduct.induction_on with
    | zero => exact Subalgebra.zero_mem _
    | tmul a b =>
      have h := Subalgebra.mul_mem _ (hl a) (hr b)
      rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h
    | add s t hs ht => exact Subalgebra.add_mem _ hs ht
  exact this

end GlobalTheory.SurjTens
