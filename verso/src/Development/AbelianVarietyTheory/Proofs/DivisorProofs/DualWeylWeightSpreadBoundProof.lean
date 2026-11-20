import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylEqEvalAtOneSmulExtremalOfRowWeight

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

/- English proof (translation)
Establish `: (rename (Prod.map σ id) : MvPolynomial (Fin N × Fin N) ℚ →ₐ[ℚ] _) = rowAct ℚ (Matrix.of fun a b => if b = σ a then (1 : ℚ) else 0)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, s⟩`. Simplify using `[rowAct, rename_X]`. Rewrite using `[this]`.
-/
theorem nablaBdd_rename_eq_rowAct {N : ℕ} (σ : Equiv.Perm (Fin N)) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    rename (Prod.map σ id) f = rowAct ℚ (Matrix.of fun a b => if b = σ a then (1 : ℚ) else 0) f := by
  classical
  have : (rename (Prod.map σ id) : MvPolynomial (Fin N × Fin N) ℚ →ₐ[ℚ] _) =
      rowAct ℚ (Matrix.of fun a b => if b = σ a then (1 : ℚ) else 0) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [rowAct, rename_X]
  rw [this]

/- English proof (translation)
Establish `key : ∀ σ : Equiv.Perm (Fin (M + 1)), rename (Prod.map σ id) f ∈ dualWeyl ℚ (M + 1) (M + 1) ν ∧ Finsupp.mapDomain (Prod.map σ id) m ∈ (rename (Prod.map σ id) f).support ∧ rowDeg (Finsupp.mapDomain (Prod.map σ id) m) (σ c) = rowDeg m c`. Introduce `σ`. Establish `hinj : Function.Injective (Prod.map σ (id : Fin (M + 1) → Fin (M + 1)))` using `σ.injective.prodMap Function.injective_id`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[nablaBdd_rename_eq_rowAct]`.

Conclude with `Formalism.GradedWeylDivisibility.dualWeylRowStable ℚ _ _ ν _ f hf`. Rewrite using `[mem_support_iff, coeff_rename_mapDomain _ hinj]`. Conclude with `mem_support_iff.mp hm`. Unfold `rowDeg`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Conclude with `Finsupp.mapDomain_apply hinj m (c, s)`. Prove the components needed by the constructor for the conclusion. Take `⟨h1, h2, h3⟩` from `key (Equiv.swap c 0)`. Establish `dom` using `(GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν _ h1 _ h2).1 1`. Establish `e : (Finset.univ.filter fun a : Fin (M + 1) => a.val < 1) = {0}`.

Use extensionality with `a`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, Fin.val_zero]`. Use linear arithmetic over natural numbers and integers. Rewrite `dom` using `[e, Finset.sum_singleton, Finset.sum_singleton]`. Rewrite `h3` using `[Equiv.swap_apply_left]`.

Use linear arithmetic over natural numbers and integers. Take `⟨h1, h2, h3⟩` from `key (Equiv.swap c (Fin.last M))`. Establish `dom` using `GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν _ h1 _ h2`. Establish `e2 : ∀ g : Fin (M + 1) → ℕ, ∑ a, g a = (∑ a : Fin (M + 1) with a.val < M, g a) + g (Fin.last M)`. Introduce `g`.

Rewrite using `[← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Fin (M + 1) => a.val < M) g]`. Use `congr 1`. Establish `: (Finset.univ.filter fun a : Fin (M + 1) => ¬ a.val < M) = {Fin.last M}`. Use extensionality with `a`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, Fin.val_last]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[this, Finset.sum_singleton]`. Establish `d1` using `dom.1 M`. Establish `d2` using `dom.2`. Rewrite `d2` using `[e2, e2]`.

Rewrite `h3` using `[Equiv.swap_apply_left]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nablaBdd_rowDeg_bounds {M : ℕ} (ν : Fin (M + 1) → ℕ) (f : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ)
    (hf : f ∈ dualWeyl ℚ (M + 1) (M + 1) ν) (m : Fin (M + 1) × Fin (M + 1) →₀ ℕ) (hm : m ∈ f.support)
    (c : Fin (M + 1)) : rowDeg m c ≤ ν 0 ∧ ν (Fin.last M) ≤ rowDeg m c := by
  classical
  have key : ∀ σ : Equiv.Perm (Fin (M + 1)), rename (Prod.map σ id) f ∈ dualWeyl ℚ (M + 1) (M + 1) ν ∧
      Finsupp.mapDomain (Prod.map σ id) m ∈ (rename (Prod.map σ id) f).support ∧
      rowDeg (Finsupp.mapDomain (Prod.map σ id) m) (σ c) = rowDeg m c := by
    intro σ
    have hinj : Function.Injective (Prod.map σ (id : Fin (M + 1) → Fin (M + 1))) :=
      σ.injective.prodMap Function.injective_id
    refine ⟨?_, ?_, ?_⟩
    · rw [nablaBdd_rename_eq_rowAct]
      exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℚ _ _ ν _ f hf
    · rw [mem_support_iff, coeff_rename_mapDomain _ hinj]
      exact mem_support_iff.mp hm
    · unfold rowDeg
      refine Finset.sum_congr rfl fun s _ => ?_
      exact Finsupp.mapDomain_apply hinj m (c, s)
  constructor
  · obtain ⟨h1, h2, h3⟩ := key (Equiv.swap c 0)
    have dom := (GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν _ h1 _ h2).1 1
    have e : (Finset.univ.filter fun a : Fin (M + 1) => a.val < 1) = {0} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, Fin.val_zero]
      omega
    rw [e, Finset.sum_singleton, Finset.sum_singleton] at dom
    rw [Equiv.swap_apply_left] at h3
    omega
  · obtain ⟨h1, h2, h3⟩ := key (Equiv.swap c (Fin.last M))
    have dom := GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν _ h1 _ h2
    have e2 : ∀ g : Fin (M + 1) → ℕ, ∑ a, g a = (∑ a : Fin (M + 1) with a.val < M, g a) + g (Fin.last M) := by
      intro g
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Fin (M + 1) => a.val < M) g]
      congr 1
      have : (Finset.univ.filter fun a : Fin (M + 1) => ¬ a.val < M) = {Fin.last M} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, Fin.val_last]
        omega
      rw [this, Finset.sum_singleton]
    have d1 := dom.1 M
    have d2 := dom.2
    rw [e2, e2] at d2
    rw [Equiv.swap_apply_left] at h3
    omega

/- English proof (translation)
Introduce `N ν _ K hK a ha b hb n x hx hn`. Assume the negation of the conclusion as `hx0`. Establish `hx0' : (x : MvPolynomial (Fin N × Fin N) ℚ) ≠ 0` using `fun h => hx0 (Subtype.ext h)`. Take `⟨m, hm⟩` from `support_nonempty.mpr hx0'`. Take `⟨M, rfl⟩ : ∃ M, N = M + 1` from `⟨N - 1, by omega⟩`.

Establish `hea : ∀ (c : ℕ) (hc : c < M + 1) (y : dualWeyl ℚ (M + 1) (M + 1) ν), ((eV (M + 1) ν c c y : dualWeyl ℚ (M + 1) (M + 1) ν) : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ) = Formalism.CohomologicalDescent.LR.der (M + 1) (M + 1) ⟨c, hc⟩ ⟨c, hc⟩ (y : MvPolynomial (Fin (M + 1) × Fin (M …`. Introduce `c hc y`. Unfold `eV`. Rewrite using `[dif_pos ⟨hc, hc⟩]`. Both sides reduce to the same expression.

Establish `hc` using `congrArg (fun y : dualWeyl ℚ (M + 1) (M + 1) ν => coeff m (y : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ)) hx`. Simplify using `only [Submodule.coe_sub, Submodule.coe_smul, hea a ha, hea b hb, coeff_sub, Formalism.CohomologicalDescent.LR.coeff_der_diag, coeff_smul, smul_eq_mul, Formalism.GradedWeylDivisibility.ldrow_weight_rowW] at hc`. Establish `hne : coeff m (x : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ) ≠ 0` using `mem_support_iff.mp hm`. Establish `key : (((rowDeg m ⟨a, ha⟩ : ℕ) : ℚ) - ((rowDeg m ⟨b, hb⟩ : ℕ) : ℚ)) = (n : ℚ)`. Apply `mul_right_cancel₀ hne` to reduce the goal to its premises.

Rewrite using `[sub_mul]`. Conclude with `hc`. Establish `key' : ((rowDeg m ⟨a, ha⟩ : ℕ) : ℤ) - ((rowDeg m ⟨b, hb⟩ : ℕ) : ℤ) = n` using `by exact_mod_cast key`. Establish `B1` using `(nablaBdd_rowDeg_bounds ν _ x.2 m hm ⟨a, ha⟩).1`. Establish `B2` using `(nablaBdd_rowDeg_bounds ν _ x.2 m hm ⟨b, hb⟩).2`.

Establish `B3` using `hK 0 (Fin.last M)`. Use linear arithmetic over natural numbers and integers.
-/
theorem nablaBdd : NablaBdd := by
  intro N ν _ K hK a ha b hb n x hx hn
  by_contra hx0
  have hx0' : (x : MvPolynomial (Fin N × Fin N) ℚ) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨m, hm⟩ := support_nonempty.mpr hx0'
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hea : ∀ (c : ℕ) (hc : c < M + 1) (y : dualWeyl ℚ (M + 1) (M + 1) ν),
      ((eV (M + 1) ν c c y : dualWeyl ℚ (M + 1) (M + 1) ν) : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ) =
        Formalism.CohomologicalDescent.LR.der (M + 1) (M + 1) ⟨c, hc⟩ ⟨c, hc⟩ (y : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ) := by
    intro c hc y
    unfold eV
    rw [dif_pos ⟨hc, hc⟩]
    rfl
  have hc := congrArg (fun y : dualWeyl ℚ (M + 1) (M + 1) ν => coeff m (y : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ)) hx
  simp only [Submodule.coe_sub, Submodule.coe_smul, hea a ha, hea b hb, coeff_sub,
    Formalism.CohomologicalDescent.LR.coeff_der_diag, coeff_smul, smul_eq_mul, Formalism.GradedWeylDivisibility.ldrow_weight_rowW] at hc
  have hne : coeff m (x : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ) ≠ 0 := mem_support_iff.mp hm
  have key : (((rowDeg m ⟨a, ha⟩ : ℕ) : ℚ) - ((rowDeg m ⟨b, hb⟩ : ℕ) : ℚ)) = (n : ℚ) := by
    apply mul_right_cancel₀ hne
    rw [sub_mul]
    exact hc
  have key' : ((rowDeg m ⟨a, ha⟩ : ℕ) : ℤ) - ((rowDeg m ⟨b, hb⟩ : ℕ) : ℤ) = n := by exact_mod_cast key
  have B1 := (nablaBdd_rowDeg_bounds ν _ x.2 m hm ⟨a, ha⟩).1
  have B2 := (nablaBdd_rowDeg_bounds ν _ x.2 m hm ⟨b, hb⟩).2
  have B3 := hK 0 (Fin.last M)
  omega

end GlobalTheory.LeviCut
