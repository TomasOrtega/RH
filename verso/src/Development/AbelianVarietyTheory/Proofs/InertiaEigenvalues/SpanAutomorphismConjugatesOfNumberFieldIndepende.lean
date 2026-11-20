import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallRingEquivFixed

namespace GlobalTheory.ConjSpan

/- English proof (translation)
Use `letI : Algebra K ℂ := σ.toAlgebra`. Use `haveI : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq (fun q => by simp)`. Establish `hzK : Transcendental K z` using `fun h => hz (h.restrictScalars ℚ)`. Establish `hind : AlgebraicIndepOn K id ({z} : Set ℂ)`. Rewrite using `[AlgebraicIndepOn, algebraicIndependent_unique_type_iff]`.

Simplify using `using hzK`. Take `⟨B, hzB, hB⟩` from `exists_isTranscendenceBasis_superset hind`. Establish `hzB' : z ∈ B` using `hzB rfl`. Set `` to `IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB`. Set `n : MvPolynomial B K ≃ₐ[K] MvPolynomial B K` to `AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => - MvPolynomial.X i) (MvPolynomial.aeval fun i => - MvPolynomial.X i) (by ext; simp) (by ext; simp)`.

Set `e` to `hB.1.aevalEquiv.symm.trans (n.trans hB.1.aevalEquiv)`. Use `⟨IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Establish `hx : σ x = algebraMap K ℂ x` using `rfl`. Rewrite using `[hx, IsScalarTower.algebraMap_apply K (Algebra.adjoin K (Set.range ((↑) : B → ℂ))) ℂ, IsAlgClosure.equivOfEquiv_algebraMap]`.

Simplify using the standard rewrite rules. Establish `h1 : algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.X ⟨z, hzB'⟩)) = z`. Rewrite using `[hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_X]`. Establish `h2 : IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv z = -z` using `by conv_lhs => rw [← h1]`. Rewrite using `[IsAlgClosure.equivOfEquiv_algebraMap]`.

Establish `: e.toRingEquiv (hB.1.aevalEquiv (MvPolynomial.X ⟨z, hzB'⟩)) = hB.1.aevalEquiv (- MvPolynomial.X ⟨z, hzB'⟩)`. Simplify using `[e, n]`. Rewrite using `[this, map_neg, map_neg, h1]`. Rewrite using `[h2]`. Introduce `h`.

Establish `hz0 : z = 0` using `by linear_combination (-1/2 : ℂ) * h`. Conclude with `hz (hz0 ▸ isAlgebraic_zero)`.
-/
theorem exists_ringEquiv_fix_ne (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (z : ℂ)
    (hz : Transcendental ℚ z) : ∃ τ : ℂ ≃+* ℂ, (∀ x, τ (σ x) = σ x) ∧ τ z ≠ z := by
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq (fun q => by simp)
  have hzK : Transcendental K z := fun h => hz (h.restrictScalars ℚ)
  have hind : AlgebraicIndepOn K id ({z} : Set ℂ) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using hzK
  obtain ⟨B, hzB, hB⟩ := exists_isTranscendenceBasis_superset hind
  have hzB' : z ∈ B := hzB rfl
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB
  let n : MvPolynomial B K ≃ₐ[K] MvPolynomial B K :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => - MvPolynomial.X i)
      (MvPolynomial.aeval fun i => - MvPolynomial.X i) (by ext; simp) (by ext; simp)
  let e := hB.1.aevalEquiv.symm.trans (n.trans hB.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv, ?_, ?_⟩
  · intro x
    have hx : σ x = algebraMap K ℂ x := rfl
    rw [hx, IsScalarTower.algebraMap_apply K (Algebra.adjoin K (Set.range ((↑) : B → ℂ))) ℂ,
      IsAlgClosure.equivOfEquiv_algebraMap]
    simp
  have h1 : algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.X ⟨z, hzB'⟩)) = z := by
    rw [hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  have h2 : IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv z = -z := by
    conv_lhs => rw [← h1]
    rw [IsAlgClosure.equivOfEquiv_algebraMap]
    have : e.toRingEquiv (hB.1.aevalEquiv (MvPolynomial.X ⟨z, hzB'⟩))
        = hB.1.aevalEquiv (- MvPolynomial.X ⟨z, hzB'⟩) := by
      simp [e, n]
    rw [this, map_neg, map_neg, h1]
  rw [h2]
  intro h
  have hz0 : z = 0 := by linear_combination (-1/2 : ℂ) * h
  exact hz (hz0 ▸ isAlgebraic_zero)

/- English proof (translation)
Distinguish the cases in `ha : IsAlgebraic ℚ z`. Use `GlobalTheory.FixedAlgebraic.mem_of_forall_ringEquiv_fixed σ.fieldRange z ha (fun τ hτ => hz τ (fun x => hτ _ ⟨x, rfl⟩))` as an intermediate fact. Simplify using `using this`. Take `⟨τ, hτ, hne⟩` from `exists_ringEquiv_fix_ne K σ z ha`. Conclude with `absurd (hz τ hτ) hne`.
-/
theorem exists_eq_of_forall_fixed (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (z : ℂ)
    (hz : ∀ τ : ℂ ≃+* ℂ, (∀ x, τ (σ x) = σ x) → τ z = z) : ∃ c : K, σ c = z := by
  by_cases ha : IsAlgebraic ℚ z
  · have := GlobalTheory.FixedAlgebraic.mem_of_forall_ringEquiv_fixed σ.fieldRange z ha (fun τ hτ => hz τ
      (fun x => hτ _ ⟨x, rfl⟩))
    simpa using this
  · obtain ⟨τ, hτ, hne⟩ := exists_ringEquiv_fix_ne K σ z ha
    exact absurd (hz τ hτ) hne

/- English proof (translation)
Introduce `K _ _ σ ι _ e he`. Set `R : Submodule ℂ (ι → ℂ)` to `{ carrier := {z | ∀ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) → ∑ i, z i * φ (e i) = 0} add_mem' := by`. Introduce `a b ha hb φ hφ`. Simplify using `only [Set.mem_setOf_eq, Pi.add_apply, add_mul, Finset.sum_add_distrib, ha φ hφ, hb φ hφ, add_zero]`. Use the proof step `zero_mem' := by intro φ hφ; simp`.

Use the proof step `smul_mem' := by`. Introduce `c a ha φ hφ`. Simplify using `only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, ha φ hφ, mul_zero] }`. Establish `hRmem : ∀ z, z ∈ R ↔ ∀ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) → ∑ i, z i * φ (e i) = 0` using `fun z => Iff.rfl`. Establish `key : ∀ n, ∀ z ∈ R, (Finset.univ.filter (fun i => z i ≠ 0)).card = n → z = 0`.

Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `z hz hcard`. Assume the negation of the conclusion as `hne`.

Choose the witnesses or unpack the hypotheses as in `⟨i0, hi0⟩ : ∃ i, z i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne (funext h)`. Use `set z' := (z i0)⁻¹ • z with hz'`.

Establish `hz'R : z' ∈ R` using `R.smul_mem _ hz`. Establish `hz'i0 : z' i0 = 1` using `by simp [z', hi0]`. Establish `hsupp : (Finset.univ.filter (fun i => z' i ≠ 0)) = Finset.univ.filter (fun i => z i ≠ 0)`. Use extensionality with `i`. Simplify using `[z', hi0]`.

Establish `hfix : ∀ ψ : ℂ ≃+* ℂ, (∀ x, ψ (σ x) = σ x) → ∀ i, ψ (z' i) = z' i`. Introduce `ψ hψ`. Establish `hw : (fun i => ψ (z' i)) - z' ∈ R`. Use `R.sub_mem ?_ hz'R` and prove the remaining obligations. Rewrite using `[hRmem]`.

Introduce `φ hφ`. Establish `h1` using `(hRmem z').1 hz'R (φ.trans ψ.symm) (by`. Introduce `x`. Rewrite using `[RingEquiv.trans_apply, hφ, RingEquiv.symm_apply_eq, hψ])`. Establish `h2` using `congrArg ψ h1`.

Simplify `h2` using `[map_sum, map_mul]`. Establish `hlt : (Finset.univ.filter (fun i => ((fun i => ψ (z' i)) - z') i ≠ 0)).card < n`. Rewrite using `[← hcard, ← hsupp]`. Apply `Finset.card_lt_card` to reduce the goal to its premises. Rewrite using `[Finset.ssubset_iff_of_subset]`.

Conclude with `⟨i0, by simp [hz'i0], by simp [hz'i0]⟩`. Introduce `i hi`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, ne_eq] at hi ⊢`. Introduce `h`. Apply `hi` to reduce the goal to its premises.

Simplify using `[h]`. Establish `h3` using `ih _ hlt _ hw rfl`. Introduce `i`. Establish `h4` using `congrFun h3 i`. Simplify `h4` using `[sub_eq_zero]`.

Use `choose c hc using fun i => exists_eq_of_forall_fixed K σ (z' i) (fun τ hτ => hfix τ hτ i)`. Establish `hc0` using `he c (by`. Establish `h5` using `(hRmem z').1 hz'R (RingEquiv.refl ℂ) (fun x => rfl)`. Simplify `h5)` using `[hc]`. Establish `h6 : z' i0 = 0` using `by rw [← hc i0, hc0]; simp`.

Rewrite `h6` using `[hz'i0]`. Conclude with `one_ne_zero h6`. Assume the negation of the conclusion as `hS`. Take `⟨f, hf0, hf⟩` from `Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hS) inferInstance`. Set `z : ι → ℂ` to `fun i => f (fun j => if i = j then 1 else 0)`.

Establish `hzR : z ∈ R`. Rewrite using `[hRmem]`. Introduce `φ hφ`. Establish `hmem : (fun i => φ (e i)) ∈ Submodule.span ℂ {v : ι → ℂ | ∃ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) ∧ v = fun i => φ (e i)}` using `Submodule.subset_span ⟨φ, hφ, rfl⟩`. Establish `h7 : f (fun i => φ (e i)) = 0`.

Establish `h8` using `Submodule.mem_map_of_mem (f := f) hmem`. Rewrite `h8` using `[hf, Submodule.mem_bot]`. Conclude with `h8`. Rewrite `h7` using `[LinearMap.pi_apply_eq_sum_univ]`. Simplify `h7` using `[z, smul_eq_mul, mul_comm]`.

Establish `hz0` using `key _ z hzR rfl`. Apply `hf0` to reduce the goal to its premises. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.pi_apply_eq_sum_univ]`. Establish `: ∀ i, f (fun j => if i = j then 1 else 0) = 0` using `fun i => congrFun hz0 i`.

Simplify using `[this]`.
-/
theorem span_conj_eq_top : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (ι : Type) [Fintype ι]
    (e : ι → ℂ), (∀ c : ι → K, ∑ i, σ (c i) * e i = 0 → c = 0) →
    Submodule.span ℂ {v : ι → ℂ | ∃ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) ∧ v = fun i => φ (e i)} = ⊤ := by
  intro K _ _ σ ι _ e he
  classical
  let R : Submodule ℂ (ι → ℂ) :=
    { carrier := {z | ∀ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) → ∑ i, z i * φ (e i) = 0}
      add_mem' := by
        intro a b ha hb φ hφ
        simp only [Set.mem_setOf_eq, Pi.add_apply, add_mul, Finset.sum_add_distrib, ha φ hφ,
          hb φ hφ, add_zero]
      zero_mem' := by intro φ hφ; simp
      smul_mem' := by
        intro c a ha φ hφ
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum,
          ha φ hφ, mul_zero] }
  have hRmem : ∀ z, z ∈ R ↔ ∀ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) → ∑ i, z i * φ (e i) = 0 :=
    fun z => Iff.rfl
  have key : ∀ n, ∀ z ∈ R, (Finset.univ.filter (fun i => z i ≠ 0)).card = n → z = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro z hz hcard
    by_contra hne
    obtain ⟨i0, hi0⟩ : ∃ i, z i ≠ 0 := by
      by_contra h; push_neg at h; exact hne (funext h)
    set z' := (z i0)⁻¹ • z with hz'
    have hz'R : z' ∈ R := R.smul_mem _ hz
    have hz'i0 : z' i0 = 1 := by simp [z', hi0]
    have hsupp : (Finset.univ.filter (fun i => z' i ≠ 0))
        = Finset.univ.filter (fun i => z i ≠ 0) := by
      ext i; simp [z', hi0]
    have hfix : ∀ ψ : ℂ ≃+* ℂ, (∀ x, ψ (σ x) = σ x) → ∀ i, ψ (z' i) = z' i := by
      intro ψ hψ
      have hw : (fun i => ψ (z' i)) - z' ∈ R := by
        refine R.sub_mem ?_ hz'R
        rw [hRmem]
        intro φ hφ
        have h1 := (hRmem z').1 hz'R (φ.trans ψ.symm) (by
          intro x
          rw [RingEquiv.trans_apply, hφ, RingEquiv.symm_apply_eq, hψ])
        have h2 := congrArg ψ h1
        simpa [map_sum, map_mul] using h2
      have hlt : (Finset.univ.filter (fun i => ((fun i => ψ (z' i)) - z') i ≠ 0)).card < n := by
        rw [← hcard, ← hsupp]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨i0, by simp [hz'i0], by simp [hz'i0]⟩
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, ne_eq] at hi ⊢
          intro h
          apply hi
          simp [h]
      have h3 := ih _ hlt _ hw rfl
      intro i
      have h4 := congrFun h3 i
      simpa [sub_eq_zero] using h4
    choose c hc using fun i => exists_eq_of_forall_fixed K σ (z' i) (fun τ hτ => hfix τ hτ i)
    have hc0 := he c (by
      have h5 := (hRmem z').1 hz'R (RingEquiv.refl ℂ) (fun x => rfl)
      simpa [hc] using h5)
    have h6 : z' i0 = 0 := by rw [← hc i0, hc0]; simp
    rw [hz'i0] at h6
    exact one_ne_zero h6
  by_contra hS
  obtain ⟨f, hf0, hf⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hS) inferInstance
  let z : ι → ℂ := fun i => f (fun j => if i = j then 1 else 0)
  have hzR : z ∈ R := by
    rw [hRmem]
    intro φ hφ
    have hmem : (fun i => φ (e i)) ∈ Submodule.span ℂ
        {v : ι → ℂ | ∃ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) ∧ v = fun i => φ (e i)} :=
      Submodule.subset_span ⟨φ, hφ, rfl⟩
    have h7 : f (fun i => φ (e i)) = 0 := by
      have h8 := Submodule.mem_map_of_mem (f := f) hmem
      rw [hf, Submodule.mem_bot] at h8
      exact h8
    rw [LinearMap.pi_apply_eq_sum_univ] at h7
    simpa [z, smul_eq_mul, mul_comm] using h7
  have hz0 := key _ z hzR rfl
  apply hf0
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.pi_apply_eq_sum_univ]
  have : ∀ i, f (fun j => if i = j then 1 else 0) = 0 := fun i => congrFun hz0 i
  simp [this]

end GlobalTheory.ConjSpan
