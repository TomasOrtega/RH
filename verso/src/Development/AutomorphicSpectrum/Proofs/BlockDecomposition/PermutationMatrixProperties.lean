import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

namespace GlobalTheory.CompanionTheory.TyFin.Pm

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Use `show (Matrix.permMatrixHom (n := ι) (R := K) σ) i j = _`. Rewrite using `[Matrix.permMatrixHom_apply]`. Use `show (σ⁻¹ : Equiv.Perm ι).toPEquiv.toMatrix i j = _`. Rewrite using `[PEquiv.toMatrix_apply]`. Distinguish the cases in `h : i = σ j`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h' : j ≠ σ.symm i` using `fun e => h (by rw [e, Equiv.apply_symm_apply])`. Simplify using `[h, Ne.symm h']`.
-/
theorem pm_apply (σ : Equiv.Perm ι) (i j : ι) :
    (pm K σ : Matrix ι ι K) i j = if i = σ j then 1 else 0 := by
  show (Matrix.permMatrixHom (n := ι) (R := K) σ) i j = _
  rw [Matrix.permMatrixHom_apply]
  show (σ⁻¹ : Equiv.Perm ι).toPEquiv.toMatrix i j = _
  rw [PEquiv.toMatrix_apply]
  by_cases h : i = σ j
  · subst h
    simp
  · have h' : j ≠ σ.symm i := fun e => h (by rw [e, Equiv.apply_symm_apply])
    simp [h, Ne.symm h']

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem glEquiv_apply {κ : Type} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (g : GL ι K) (i j : κ) :
    (glEquiv K e g : Matrix κ κ K) i j = (g : Matrix ι ι K) (e.symm i) (e.symm j) := rfl

/- English proof (translation)
Rewrite using `[mul_inv_eq_iff_eq_mul]`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `only [Units.val_mul, Matrix.mul_apply, pm_apply, glEquiv_apply]`. Rewrite using `[Finset.sum_eq_single (σ.symm i), Finset.sum_eq_single (σ j)]`.

Simplify using the standard rewrite rules. Introduce `x _ hx`. Simplify using `[hx]`. Simplify using the standard rewrite rules. Introduce `x _ hx`.

Establish `: i ≠ σ x` using `fun h => hx (by rw [h]; simp)`. Simplify using `[this]`. Simplify using the standard rewrite rules.
-/
theorem pm_conj (σ : Equiv.Perm ι) (g : GL ι K) :
    pm K σ * g * (pm K σ)⁻¹ = glEquiv K σ g := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, pm_apply, glEquiv_apply]
  rw [Finset.sum_eq_single (σ.symm i), Finset.sum_eq_single (σ j)]
  · simp
  · intro x _ hx
    simp [hx]
  · simp
  · intro x _ hx
    have : i ≠ σ x := fun h => hx (by rw [h]; simp)
    simp [this]
  · simp

omit [Fintype K] [DecidableEq K] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H i j hlt`. Use `H (σ i) (σ j) hlt` as an intermediate fact. Simplify `this` using `[glEquiv_apply]`. Introduce `H i j hlt`.

Rewrite using `[glEquiv_apply]`. Conclude with `H _ _ (by simpa using hlt)`.
-/
theorem isBlockUT_glEquiv {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) (g : GL ι K) :
    IsBlockUT K b (glEquiv K σ g : Matrix ι ι K) ↔ IsBlockUT K (b ∘ σ) (g : Matrix ι ι K) := by
  constructor
  · intro H i j hlt
    have := H (σ i) (σ j) hlt
    simpa [glEquiv_apply] using this
  · intro H i j hlt
    rw [glEquiv_apply]
    exact H _ _ (by simpa using hlt)

/- English proof (translation)
Use `show (IsBlockUT K b _ ∧ IsBlockUT K b _) ↔ (IsBlockUT K (b ∘ σ) _ ∧ IsBlockUT K (b ∘ σ) _)`. Rewrite using `[← map_inv, isBlockUT_glEquiv, isBlockUT_glEquiv]`.
-/
theorem glEquiv_mem_parab {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) (g : GL ι K) :
    glEquiv K σ g ∈ parab K b ↔ g ∈ parab K (b ∘ σ) := by
  show (IsBlockUT K b _ ∧ IsBlockUT K b _) ↔ (IsBlockUT K (b ∘ σ) _ ∧ IsBlockUT K (b ∘ σ) _)
  rw [← map_inv, isBlockUT_glEquiv, isBlockUT_glEquiv]

/- English proof (translation)
Use extensionality with `h`. Rewrite using `[mem_cj, pm_conj, glEquiv_mem_parab]`.
-/
theorem cj_pm_parab {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) :
    cj (pm K σ) (parab K b) = parab K (b ∘ σ) := by
  ext h
  rw [mem_cj, pm_conj, glEquiv_mem_parab]

/- English proof (translation)
Unfold `blkGL`. Distinguish the cases in `h : g ∈ parab K (b ∘ σ)`. Rewrite using `[dif_pos h, dif_pos ((glEquiv_mem_parab b σ g).2 h)]`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `⟨i, hi⟩ ⟨j, hj⟩`.

Rewrite using `[glEquiv_apply]`. Establish `key : ∀ y : {j // b j = c}, ((e.symm y : {i // (b ∘ σ) i = c}) : ι) = σ.symm y`. Introduce `y`. Rewrite using `[Equiv.eq_symm_apply, ← he, Equiv.apply_symm_apply]`. Use `show (glEquiv K σ g : Matrix ι ι K) i j = (g : Matrix ι ι K) _ _`.

Rewrite using `[glEquiv_apply]`. Conclude with `congrArg₂ (g : Matrix ι ι K) (key ⟨i, hi⟩).symm (key ⟨j, hj⟩).symm`. Rewrite using `[dif_neg h, dif_neg (fun h' => h ((glEquiv_mem_parab b σ g).1 h')), map_one]`.
-/
theorem blkGL_glEquiv {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) (c : Fin s) (g : GL ι K)
    (e : {i // (b ∘ σ) i = c} ≃ {j // b j = c})
    (he : ∀ x, (e x : ι) = σ x) :
    blkGL b c (glEquiv K σ g) = glEquiv K e (blkGL (b ∘ σ) c g) := by
  unfold blkGL
  by_cases h : g ∈ parab K (b ∘ σ)
  · rw [dif_pos h, dif_pos ((glEquiv_mem_parab b σ g).2 h)]
    apply Units.ext
    ext ⟨i, hi⟩ ⟨j, hj⟩
    rw [glEquiv_apply]
    have key : ∀ y : {j // b j = c}, ((e.symm y : {i // (b ∘ σ) i = c}) : ι) = σ.symm y := by
      intro y
      rw [Equiv.eq_symm_apply, ← he, Equiv.apply_symm_apply]
    show (glEquiv K σ g : Matrix ι ι K) i j = (g : Matrix ι ι K) _ _
    rw [glEquiv_apply]
    exact congrArg₂ (g : Matrix ι ι K) (key ⟨i, hi⟩).symm (key ⟨j, hj⟩).symm
  · rw [dif_neg h, dif_neg (fun h' => h ((glEquiv_mem_parab b σ g).1 h')), map_one]

/- English proof (translation)
Introduce `K _ _ _ ι _ _ σ`. Use `⟨pm_apply σ, pm_conj σ, fun s b => cj_pm_parab b σ, ?_⟩` and prove the remaining obligations. Introduce `s b χ g`. Unfold `hcFun`. Conclude with `Finset.prod_congr rfl fun c _ => congrArg (χ c) (blkGL_glEquiv b σ c g (σ.subtypeEquiv (p := fun i => (b ∘ σ) i = c) (q := fun j => b j = c) fun _ => Iff.rfl) fun _ => rfl)`.
-/
theorem pmFacts : ReciprocityTheory.Ty.Fin.St.PmFacts := by
  intro K _ _ _ ι _ _ σ
  refine ⟨pm_apply σ, pm_conj σ, fun s b => cj_pm_parab b σ, ?_⟩
  intro s b χ g
  unfold hcFun
  exact Finset.prod_congr rfl fun c _ => congrArg (χ c) (blkGL_glEquiv b σ c g
    (σ.subtypeEquiv (p := fun i => (b ∘ σ) i = c) (q := fun j => b j = c) fun _ => Iff.rfl) fun _ => rfl)

end GlobalTheory.CompanionTheory.TyFin.Pm
