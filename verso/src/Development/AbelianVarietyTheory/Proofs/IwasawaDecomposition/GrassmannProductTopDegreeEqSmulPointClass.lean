import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleFormEqMulPointClassValueStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTopDim

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/- English proof (translation)
Apply `Ideal.homogeneous_span` to reduce the goal to its premises. Introduce and unpack `x ((⟨τ, rfl⟩ | ⟨τ, k, -, rfl⟩) | ⟨τ, k, -, rfl⟩)`. Use `⟨0, ?_⟩` and prove the remaining obligations. Use `sub_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mem_weightedHomogeneousSubmodule]`.

Conclude with `isWeightedHomogeneous_X ℝ Prod.snd (τ, 0)`. Rewrite using `[mem_weightedHomogeneousSubmodule]`. Conclude with `isWeightedHomogeneous_one ℝ Prod.snd`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_weightedHomogeneousSubmodule]`.

Conclude with `isWeightedHomogeneous_X ℝ Prod.snd (τ, k)`. Use `⟨k, Submodule.sum_mem _ fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_weightedHomogeneousSubmodule]`. Establish `ha' : a ≤ k` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)`. Establish `h` using `((isWeightedHomogeneous_C Prod.snd ((-1 : ℝ) ^ (k - a))).mul (isWeightedHomogeneous_X ℝ Prod.snd (τ.1, a))).mul (isWeightedHomogeneous_X ℝ Prod.snd (conjEmb τ.1, k - a))`.

Use `h using 1` and compare the differences between its conclusion and the goal. Simplify using `only [zero_add]`. Use linear arithmetic over natural numbers and integers.
-/
theorem relIdeal_isHomogeneous (H : Host E) (Dw : Datum H) :
    (relIdeal H Dw).IsHomogeneous
      (weightedHomogeneousSubmodule ℝ (Prod.snd : (E →+* ℂ) × ℕ → ℕ)) := by
  apply Ideal.homogeneous_span
  rintro x ((⟨τ, rfl⟩ | ⟨τ, k, -, rfl⟩) | ⟨τ, k, -, rfl⟩)
  · refine ⟨0, ?_⟩
    refine sub_mem ?_ ?_
    · rw [mem_weightedHomogeneousSubmodule]
      exact isWeightedHomogeneous_X ℝ Prod.snd (τ, 0)
    · rw [mem_weightedHomogeneousSubmodule]
      exact isWeightedHomogeneous_one ℝ Prod.snd
  · refine ⟨k, ?_⟩
    rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_X ℝ Prod.snd (τ, k)
  · refine ⟨k, Submodule.sum_mem _ fun a ha => ?_⟩
    rw [mem_weightedHomogeneousSubmodule]
    have ha' : a ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    have h := ((isWeightedHomogeneous_C Prod.snd ((-1 : ℝ) ^ (k - a))).mul
      (isWeightedHomogeneous_X ℝ Prod.snd (τ.1, a))).mul
      (isWeightedHomogeneous_X ℝ Prod.snd (conjEmb τ.1, k - a))
    convert h using 1
    simp only [zero_add]
    omega

/- English proof (translation)
Establish `h : ∀ τ ∈ (Finset.univ : Finset (GlobalTheory.AllWt.Psi H)), IsWeightedHomogeneous Prod.snd ((C ((-1 : ℝ) ^ Dw.mult τ.1) * X (τ.1, Dw.mult τ.1)) ^ (Dw.p + Dw.q - Dw.mult τ.1)) (Dw.p * Dw.q)`. Introduce `τ _`. Establish `hm : Dw.mult τ.1 = Dw.p` using `GlobalTheory.PointChern.mult_of_mem Dw τ.2`. Establish `h1` using `((isWeightedHomogeneous_C Prod.snd ((-1 : ℝ) ^ Dw.mult τ.1)).mul (isWeightedHomogeneous_X ℝ Prod.snd (τ.1, Dw.mult τ.1))).pow (Dw.p + Dw.q - Dw.mult τ.1)`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [hm, zero_add, Nat.add_sub_cancel_left]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `IsWeightedHomogeneous.prod Finset.univ _ _ h`. Rewrite using `[pointPoly]`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Simplify using `[Finset.sum_const, Finset.card_univ, smul_eq_mul]`.
-/
theorem pointPoly_isWeightedHomogeneous (H : Host E) (Dw : Datum H) :
    IsWeightedHomogeneous Prod.snd (pointPoly H Dw) (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) := by
  have h : ∀ τ ∈ (Finset.univ : Finset (GlobalTheory.AllWt.Psi H)), IsWeightedHomogeneous Prod.snd
      ((C ((-1 : ℝ) ^ Dw.mult τ.1) * X (τ.1, Dw.mult τ.1)) ^ (Dw.p + Dw.q - Dw.mult τ.1)) (Dw.p * Dw.q) := by
    intro τ _
    have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
    have h1 := ((isWeightedHomogeneous_C Prod.snd ((-1 : ℝ) ^ Dw.mult τ.1)).mul
      (isWeightedHomogeneous_X ℝ Prod.snd (τ.1, Dw.mult τ.1))).pow (Dw.p + Dw.q - Dw.mult τ.1)
    convert h1 using 1
    simp only [hm, zero_add, Nat.add_sub_cancel_left]
    ring
  have h2 := IsWeightedHomogeneous.prod Finset.univ _ _ h
  rw [pointPoly]
  convert h2 using 1
  simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/- English proof (translation)
Use `(Module.forall_dual_apply_eq_zero_iff ℝ (S.mkQ v)).1 h` as an intermediate fact. Simplify `this` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.
-/
theorem mem_of_forall_dual {V : Type} [AddCommGroup V] [Module ℝ V] (S : Submodule ℝ V) (v : V)
    (h : ∀ f : Module.Dual ℝ (V ⧸ S), f (S.mkQ v) = 0) : v ∈ S := by
  have := (Module.forall_dual_apply_eq_zero_iff ℝ (S.mkQ v)).1 h
  simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using this

/- English proof (translation)
Introduce `E _ _ _ H Dw Q hQ`. Take `⟨β, hβ⟩` from `GlobalTheory.T.admissible_form_eq_mul_point_class_value E H Dw Q`. Use `set D := Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) with hD`. Set `N : Submodule ℝ (MvPolynomial ((E →+* ℂ) × ℕ) ℝ)` to `Submodule.span ℝ {f | ∃ d : (E →+* ℂ) × ℕ →₀ ℕ, (d.sum fun x i => x.2 * i) ≠ D ∧ f = monomial d 1}`. Set `S` to `(relIdeal H Dw).restrictScalars ℝ ⊔ N`.

Establish `hS : Q - C β * pointPoly H Dw ∈ S`. Apply `mem_of_forall_dual` to reduce the goal to its premises. Introduce `f`. Set `Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ` to `f ∘ₗ S.mkQ`. Establish `hker : ∀ x ∈ S, Θ x = 0` using `fun x hx => by`.

Simplify using `[Θ, (Submodule.Quotient.mk_eq_zero _).2 hx]`. Establish `hrel : ∀ x ∈ relIdeal H Dw, Θ x = 0` using `fun x hx => hker x (Submodule.mem_sup_left (by simpa using hx))`. Establish `hadm : GlobalTheory.Schubert.admitted H Dw Θ`. Use `⟨fun τ k hk P => hrel _ ?_, fun τ P => hrel _ ?_, fun τ k hk P => hrel _ ?_, fun d hd => hker _ (Submodule.mem_sup_right (Submodule.subset_span ⟨d, hd, rfl⟩))⟩` and prove the remaining obligations. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inr ⟨τ, k, hk, rfl⟩))`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inl (Or.inl ⟨τ, rfl⟩)))`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inl (Or.inr ⟨τ, k, hk, rfl⟩)))`. Use `show Θ (Q - C β * pointPoly H Dw) = 0`. Rewrite using `[map_sub, hβ Θ hadm, C_mul', map_smul, smul_eq_mul, sub_self]`. Take `⟨r, hr, n, hn, hrn⟩` from `Submodule.mem_sup.1 hS`.

Establish `hn0 : ∀ n ∈ N, weightedHomogeneousComponent Prod.snd D n = 0`. Introduce `n hn`. Proceed by induction on `hn using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨d, hd, rfl⟩` from `hx`.

Use `weightedHomogeneousComponent_eq_zero' _ _ fun d' hd' => ?_` and prove the remaining obligations. Rewrite `hd'` using `[support_monomial, if_neg one_ne_zero, Finset.mem_singleton]`. Substitute `hd'` using the available equality. Rewrite using `[Finsupp.weight_apply]`. Introduce `h`.

Apply `hd` to reduce the goal to its premises. Rewrite using `[← h]`. Conclude with `Finsupp.sum_congr fun x _ => by rw [smul_eq_mul, mul_comm]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`.

Consider the case `smul c x _ hx => rw [map_smul, hx, smul_zero]`. Establish `hhom : IsWeightedHomogeneous Prod.snd (Q - C β * pointPoly H Dw) D`. Establish `h1 : Q ∈ weightedHomogeneousSubmodule ℝ Prod.snd D` using `(mem_weightedHomogeneousSubmodule _ _ _ _).2 hQ`. Establish `h2 : pointPoly H Dw ∈ weightedHomogeneousSubmodule ℝ Prod.snd D` using `(mem_weightedHomogeneousSubmodule _ _ _ _).2 (pointPoly_isWeightedHomogeneous H Dw)`. Rewrite using `[← mem_weightedHomogeneousSubmodule, C_mul']`.

Conclude with `sub_mem h1 (Submodule.smul_mem _ β h2)`. Use `⟨β, ?_⟩` and prove the remaining obligations. Rewrite using `[← hhom.weightedHomogeneousComponent_same, ← hrn, map_add, hn0 n hn, add_zero]`. Conclude with `weightedHomogeneousComponent_mem_of_mem ℝ Prod.snd (relIdeal_isHomogeneous H Dw) (by simpa using hr) D`.
-/
theorem top_eq_smul_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ),
    IsWeightedHomogeneous Prod.snd Q (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) →
      ∃ c : ℝ, Q - C c * pointPoly H Dw ∈ relIdeal H Dw := by
  intro E _ _ _ H Dw Q hQ
  obtain ⟨β, hβ⟩ := GlobalTheory.T.admissible_form_eq_mul_point_class_value E H Dw Q
  set D := Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) with hD
  let N : Submodule ℝ (MvPolynomial ((E →+* ℂ) × ℕ) ℝ) := Submodule.span ℝ
    {f | ∃ d : (E →+* ℂ) × ℕ →₀ ℕ, (d.sum fun x i => x.2 * i) ≠ D ∧ f = monomial d 1}
  let S := (relIdeal H Dw).restrictScalars ℝ ⊔ N
  have hS : Q - C β * pointPoly H Dw ∈ S := by
    apply mem_of_forall_dual
    intro f
    let Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ := f ∘ₗ S.mkQ
    have hker : ∀ x ∈ S, Θ x = 0 := fun x hx => by
      simp [Θ, (Submodule.Quotient.mk_eq_zero _).2 hx]
    have hrel : ∀ x ∈ relIdeal H Dw, Θ x = 0 := fun x hx =>
      hker x (Submodule.mem_sup_left (by simpa using hx))
    have hadm : GlobalTheory.Schubert.admitted H Dw Θ := by
      refine ⟨fun τ k hk P => hrel _ ?_, fun τ P => hrel _ ?_, fun τ k hk P => hrel _ ?_,
        fun d hd => hker _ (Submodule.mem_sup_right (Submodule.subset_span ⟨d, hd, rfl⟩))⟩
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inr ⟨τ, k, hk, rfl⟩))
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inl (Or.inl ⟨τ, rfl⟩)))
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inl (Or.inr ⟨τ, k, hk, rfl⟩)))
    show Θ (Q - C β * pointPoly H Dw) = 0
    rw [map_sub, hβ Θ hadm, C_mul', map_smul, smul_eq_mul, sub_self]
  obtain ⟨r, hr, n, hn, hrn⟩ := Submodule.mem_sup.1 hS
  have hn0 : ∀ n ∈ N, weightedHomogeneousComponent Prod.snd D n = 0 := by
    intro n hn
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      refine weightedHomogeneousComponent_eq_zero' _ _ fun d' hd' => ?_
      rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hd'
      subst hd'
      rw [Finsupp.weight_apply]
      intro h
      apply hd
      rw [← h]
      exact Finsupp.sum_congr fun x _ => by rw [smul_eq_mul, mul_comm]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  have hhom : IsWeightedHomogeneous Prod.snd (Q - C β * pointPoly H Dw) D := by
    have h1 : Q ∈ weightedHomogeneousSubmodule ℝ Prod.snd D := (mem_weightedHomogeneousSubmodule _ _ _ _).2 hQ
    have h2 : pointPoly H Dw ∈ weightedHomogeneousSubmodule ℝ Prod.snd D :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).2 (pointPoly_isWeightedHomogeneous H Dw)
    rw [← mem_weightedHomogeneousSubmodule, C_mul']
    exact sub_mem h1 (Submodule.smul_mem _ β h2)
  refine ⟨β, ?_⟩
  rw [← hhom.weightedHomogeneousComponent_same, ← hrn, map_add, hn0 n hn, add_zero]
  exact weightedHomogeneousComponent_mem_of_mem ℝ Prod.snd (relIdeal_isHomogeneous H Dw) (by simpa using hr) D

end GlobalTheory.GrassTopDim
