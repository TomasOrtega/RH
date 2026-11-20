import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Formalism.DegreeFormula.FlagDegFormula
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

/- English proof (translation)
Introduce `x y hxy`. Simplify using `only [Prod.mk.injEq] at hxy`. Conclude with `Prod.ext (σ.injective hxy.1) hxy.2`.
-/
theorem pa_relabel_injective {Ψ : Type} {N : ℕ} (σ : Equiv.Perm Ψ) :
    Function.Injective (fun x : Ψ × Fin N => (σ x.1, x.2)) := by
  intro x y hxy
  simp only [Prod.mk.injEq] at hxy
  exact Prod.ext (σ.injective hxy.1) hxy.2

/- English proof (translation)
Establish `hinj` using `pa_relabel_injective (N := N) σ`. Establish `hexp : ∀ ρ : Ψ → Equiv.Perm (Fin N), permExp ρ = Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (permExp (fun t => ρ (σ t)))`. Introduce `ρ`. Use extensionality with `⟨t, i⟩`. Establish `ht : ((t, i) : Ψ × Fin N) = (fun x : Ψ × Fin N => (σ x.1, x.2)) (σ.symm t, i)` using `by simp`.

Rewrite using `[ht, Finsupp.mapDomain_apply hinj]`. Simplify using `[permExp]`. Unfold `degFl`. Use `congr 1`. Establish `hterm : ∀ ρ : Ψ → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) * (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F).coeff (permExp ρ) = (fun ρ' : Ψ → Equiv.Perm (Fin N) => (∏ τ, ((Equiv.Perm.sign (ρ' τ) : ℤ) : ℝ)) * F.coeff (permExp ρ')) (fun t => ρ (σ t))`.

Introduce `ρ`. Rewrite using `[hexp ρ, coeff_rename_mapDomain _ hinj]`. Use `congr 1`. Conclude with `(Equiv.prod_comp σ (fun τ => ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ))).symm`. Rewrite using `[Finset.sum_congr rfl (fun ρ _ => hterm ρ)]`.

Conclude with `Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Equiv.Perm (Fin N)))) (fun ρ' : Ψ → Equiv.Perm (Fin N) => (∏ τ, ((Equiv.Perm.sign (ρ' τ) : ℤ) : ℝ)) * F.coeff (permExp ρ'))`.
-/
theorem pa_degFl_relabel {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (σ : Equiv.Perm Ψ) (F : RP Ψ N) :
    degFl (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = degFl F := by
  have hinj := pa_relabel_injective (N := N) σ
  have hexp : ∀ ρ : Ψ → Equiv.Perm (Fin N), permExp ρ =
      Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (permExp (fun t => ρ (σ t))) := by
    intro ρ
    ext ⟨t, i⟩
    have ht : ((t, i) : Ψ × Fin N) = (fun x : Ψ × Fin N => (σ x.1, x.2)) (σ.symm t, i) := by simp
    rw [ht, Finsupp.mapDomain_apply hinj]
    simp [permExp]
  unfold degFl
  congr 1
  have hterm : ∀ ρ : Ψ → Equiv.Perm (Fin N),
      (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) *
          (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F).coeff (permExp ρ) =
        (fun ρ' : Ψ → Equiv.Perm (Fin N) =>
          (∏ τ, ((Equiv.Perm.sign (ρ' τ) : ℤ) : ℝ)) * F.coeff (permExp ρ')) (fun t => ρ (σ t)) := by
    intro ρ
    rw [hexp ρ, coeff_rename_mapDomain _ hinj]
    congr 1
    exact (Equiv.prod_comp σ (fun τ => ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ))).symm
  rw [Finset.sum_congr rfl (fun ρ _ => hterm ρ)]
  exact Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Equiv.Perm (Fin N))))
    (fun ρ' : Ψ → Equiv.Perm (Fin N) =>
      (∏ τ, ((Equiv.Perm.sign (ρ' τ) : ℤ) : ℝ)) * F.coeff (permExp ρ'))

/- English proof (translation)
Introduce `Ψ _ _ N`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `τ a b F hab`. Establish `hinv : ∀ x : Ψ × Fin N, (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) ((fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) x) = x`. Introduce and unpack `⟨t, i⟩`.

Apply the tactic sequence `by_cases ht : t = τ <;> simp [ht]`. Establish `hinj : Function.Injective (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x)`. Introduce `x y hxy`. Conclude with `(hinv x).symm.trans ((congrArg (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) hxy).trans (hinv y))`. Establish `hexp : ∀ ρ : Ψ → Equiv.Perm (Fin N), permExp ρ = Finsupp.mapDomain (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) (permExp (ρ * Pi.mulSingle τ (Equiv.swap a b)))`.

Introduce `ρ`. Use extensionality with `y`. Use `conv_rhs => rw [← hinv y]`. Rewrite using `[Finsupp.mapDomain_apply hinj]`. Break down `y with ⟨t, i⟩` into its components or cases.

Distinguish the cases in `ht : t = τ`. Substitute `ht` using the available equality. Simplify using `[permExp]`. Simplify using `[permExp, ht, Pi.mulSingle_apply]`. Establish `hsgn : ∀ ρ : Ψ → Equiv.Perm (Fin N), (∏ t, ((Equiv.Perm.sign ((ρ * Pi.mulSingle τ (Equiv.swap a b) : Ψ → Equiv.Perm (Fin N)) t) : ℤ) : ℝ)) = -∏ t, ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ)`.

Introduce `ρ`. Establish `hfac : ∀ t, ((Equiv.Perm.sign ((ρ * Pi.mulSingle τ (Equiv.swap a b) : Ψ → Equiv.Perm (Fin N)) t) : ℤ) : ℝ) = ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ) * (if t = τ then -1 else 1)`. Introduce `t`. Distinguish the cases in `ht : t = τ`. Substitute `ht` using the available equality.

Simplify using `[Equiv.Perm.sign_swap hab]`. Simplify using `[ht]`. Rewrite using `[Finset.prod_congr rfl (fun t _ => hfac t), Finset.prod_mul_distrib]`. Simplify using the standard rewrite rules. Unfold `degFl`.

Rewrite using `[← mul_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`. Rewrite using `[← Equiv.sum_comp (Equiv.mulRight (Pi.mulSingle τ (Equiv.swap a b))) (fun ρ => -((∏ t, ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ)) * F.coeff (permExp ρ)))]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `ρ _`.

Simplify using `only [Equiv.coe_mulRight]`. Rewrite using `[hexp ρ, coeff_rename_mapDomain _ hinj, hsgn ρ]`. Expand and normalize the polynomial expressions, which then agree. Introduce `σ F`. Establish `hinj` using `pa_relabel_injective (N := N) σ`.

Use `⟨pa_degFl_relabel σ F, fun j τ => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Unfold `Sh conv_rhs => rw [← pa_degFl_relabel σ]`. Rewrite using `[map_sum]`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `i _`. Conclude with `pderiv_rename hinj (τ, i) F`. Unfold `Tot conv_rhs => rw [← pa_degFl_relabel σ]`. Rewrite using `[map_sum]`. Use `congr 1`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Conclude with `pderiv_rename hinj (τ, i) F`.
-/
theorem degFl_symmetry_invariance : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), (∀ (τ : Ψ) (a b : Fin N) (F : RP Ψ N), a ≠ b → degFl (rename (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) F) = -degFl F) ∧ ∀ (σ : Equiv.Perm Ψ) (F : RP Ψ N), degFl (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = degFl F ∧ ∀ (j : ℕ) (τ : Ψ), Sh j (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Sh j τ F ∧ Tot (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Tot τ F := by
  intro Ψ _ _ N
  refine ⟨?_, ?_⟩
  · intro τ a b F hab
    have hinv : ∀ x : Ψ × Fin N,
        (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x)
          ((fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) x) = x := by
      rintro ⟨t, i⟩
      by_cases ht : t = τ <;> simp [ht]
    have hinj : Function.Injective
        (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) := by
      intro x y hxy
      exact (hinv x).symm.trans ((congrArg
        (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) hxy).trans (hinv y))
    have hexp : ∀ ρ : Ψ → Equiv.Perm (Fin N), permExp ρ =
        Finsupp.mapDomain (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x)
          (permExp (ρ * Pi.mulSingle τ (Equiv.swap a b))) := by
      intro ρ
      ext y
      conv_rhs => rw [← hinv y]
      rw [Finsupp.mapDomain_apply hinj]
      rcases y with ⟨t, i⟩
      by_cases ht : t = τ
      · subst ht
        simp [permExp]
      · simp [permExp, ht, Pi.mulSingle_apply]
    have hsgn : ∀ ρ : Ψ → Equiv.Perm (Fin N),
        (∏ t, ((Equiv.Perm.sign ((ρ * Pi.mulSingle τ (Equiv.swap a b) : Ψ → Equiv.Perm (Fin N)) t) : ℤ) : ℝ)) =
          -∏ t, ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ) := by
      intro ρ
      have hfac : ∀ t, ((Equiv.Perm.sign ((ρ * Pi.mulSingle τ (Equiv.swap a b) : Ψ → Equiv.Perm (Fin N)) t) : ℤ) : ℝ) =
          ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ) * (if t = τ then -1 else 1) := by
        intro t
        by_cases ht : t = τ
        · subst ht
          simp [Equiv.Perm.sign_swap hab]
        · simp [ht]
      rw [Finset.prod_congr rfl (fun t _ => hfac t), Finset.prod_mul_distrib]
      simp
    unfold degFl
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    rw [← Equiv.sum_comp (Equiv.mulRight (Pi.mulSingle τ (Equiv.swap a b)))
      (fun ρ => -((∏ t, ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ)) * F.coeff (permExp ρ)))]
    apply Finset.sum_congr rfl
    intro ρ _
    simp only [Equiv.coe_mulRight]
    rw [hexp ρ, coeff_rename_mapDomain _ hinj, hsgn ρ]
    ring
  · intro σ F
    have hinj := pa_relabel_injective (N := N) σ
    refine ⟨pa_degFl_relabel σ F, fun j τ => ⟨?_, ?_⟩⟩
    · unfold Sh
      conv_rhs => rw [← pa_degFl_relabel σ]
      rw [map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact pderiv_rename hinj (τ, i) F
    · unfold Tot
      conv_rhs => rw [← pa_degFl_relabel σ]
      rw [map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact pderiv_rename hinj (τ, i) F

end RootFieldNumerics
