import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Rodier.RootElt

def elemGL {k : Type} [Field k] {N : ℕ} (i j : Fin N) (hij : i ≠ j) (t : k) : GL (Fin N) k where
  val := Matrix.transvection i j t
  inv := Matrix.transvection i j (-t)
  val_inv := by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp
  inv_val := by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp

/- English proof (translation)
Use `show Matrix.transvection i j t a b = _`. Rewrite using `[Matrix.transvection, Matrix.add_apply, Matrix.single_apply]`. Use `congr 1`. Distinguish the cases in `h : a = i ∧ b = j`. Rewrite using `[if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]`.

Rewrite using `[if_neg h, if_neg fun e => h ⟨e.1.symm, e.2.symm⟩]`.
-/
theorem elemGL_apply {k : Type} [Field k] {N : ℕ} (i j : Fin N) (hij : i ≠ j) (t : k) (a b : Fin N) :
    (elemGL i j hij t).val a b = (1 : Matrix (Fin N) (Fin N) k) a b + if a = i ∧ b = j then t else 0 := by
  show Matrix.transvection i j t a b = _
  rw [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
  congr 1
  by_cases h : a = i ∧ b = j
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
  · rw [if_neg h, if_neg fun e => h ⟨e.1.symm, e.2.symm⟩]

/- English proof (translation)
Rewrite using `[← map_inv, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply, Units.val_mul, GroundTheory.Automorphic.permGL_mul_apply]`.
-/
theorem conj_pm_apply {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (g : GL (Fin N) k) (a b : Fin N) :
    (GroundTheory.Automorphic.permGL k w * g * (GroundTheory.Automorphic.permGL k w)⁻¹).val a b = g.val (w⁻¹ a) (w⁻¹ b) := by
  rw [← map_inv, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply, Units.val_mul,
    GroundTheory.Automorphic.permGL_mul_apply]

/- English proof (translation)
Introduce `k _ _ _ _ ψ h N d hd w i j hij hb t`. Establish `hne : i ≠ j` using `fun e => by rw [e] at hij; omega`. Establish `hlt : i < j` using `Fin.lt_def.2 (by omega)`. Establish `hu : elemGL i j hne t ∈ unipB k (Fin N)`. Use `(mem_unipB k).2 ⟨fun a b hba => ?_, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[elemGL_apply, Matrix.one_apply_ne hba.ne', if_neg fun e => ?_, add_zero]`. Rewrite `hba` using `[e.1, e.2]`. Conclude with `absurd hba hlt.not_gt`. Rewrite using `[elemGL_apply, Matrix.one_apply_eq, if_neg fun e => hne (e.1.symm.trans e.2), add_zero]`. Use `⟨elemGL i j hne t, hu, ?_, ?_⟩` and prove the remaining obligations.

Use `show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, (elemGL i j hne t).val p.1 p.2)) = _`. Use `congr 2`. Rewrite using `[Finset.sum_eq_single_of_mem (i, j) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩)]`. Rewrite using `[elemGL_apply, Matrix.one_apply_ne hne, if_pos ⟨rfl, rfl⟩, zero_add]`. Introduce and unpack `⟨a, b⟩ hp hpne`.

Establish `hab : (b : ℕ) = a + 1` using `(Finset.mem_filter.1 hp).2`. Establish `hne' : a ≠ b` using `fun e => by rw [e] at hab; omega`. Rewrite using `[elemGL_apply, Matrix.one_apply_ne hne', if_neg fun e => hpne (Prod.ext e.1 e.2), add_zero]`. Establish `hent : ∀ a b : Fin N, (pm k w * elemGL i j hne t * (pm k w)⁻¹).val a b = (1 : Matrix (Fin N) (Fin N) k) a b + if a = w i ∧ b = w j then t else 0`. Introduce `a b`.

Rewrite using `[conj_pm_apply, elemGL_apply]`. Use `congr 1`. Distinguish the cases in `e : a = b`. Rewrite using `[e, Matrix.one_apply_eq, Matrix.one_apply_eq]`. Rewrite using `[Matrix.one_apply_ne e, Matrix.one_apply_ne fun e' => e (w⁻¹.injective e')]`.

Simplify using `only [Equiv.Perm.inv_eq_iff_eq]`. Use `mem_unipRad.2 ⟨mem_parab.2 fun a b hab => ?_, fun c x y => ?_⟩` and prove the remaining obligations. Establish `hne' : a ≠ b` using `fun e => by rw [e] at hab; exact lt_irrefl _ hab`. Rewrite using `[hent, Matrix.one_apply_ne hne', if_neg fun e => ?_, add_zero]`. Rewrite `hab` using `[e.1, e.2]`.

Conclude with `lt_asymm hab hb`. Rewrite using `[hent, if_neg fun e => ?_, add_zero]`. Distinguish the cases in `e : x = y`. Rewrite using `[e, Matrix.one_apply_eq, Matrix.one_apply_eq]`. Rewrite using `[Matrix.one_apply_ne e, Matrix.one_apply_ne fun e' => e (by simpa using (stdBlocks d hd).injective e')]`.

Establish `h1` using `blk_apply (stdBlocks d hd) c x`. Establish `h2` using `blk_apply (stdBlocks d hd) c y`. Rewrite `h1` using `[e.1]`. Rewrite `h2` using `[e.2]`. Rewrite `hb` using `[h1, h2]`.

Conclude with `lt_irrefl _ hb`.
-/
theorem exists_root_conj_mem_unipRad : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (w : Equiv.Perm (Fin N)) (i j : Fin N), (j : ℕ) = i + 1 → blk (stdBlocks d hd) (w i) < blk (stdBlocks d hd) (w j) → ∀ t : k, ∃ (u : GL (Fin N) k) (hu : u ∈ unipB k (Fin N)), whitChar ψ N ⟨u, hu⟩ = Circle.toUnits (ψ t) ∧ pm k w * u * (pm k w)⁻¹ ∈ unipRad k (stdBlocks d hd) := by
  intro k _ _ _ _ ψ h N d hd w i j hij hb t
  have hne : i ≠ j := fun e => by rw [e] at hij; omega
  have hlt : i < j := Fin.lt_def.2 (by omega)
  have hu : elemGL i j hne t ∈ unipB k (Fin N) := by
    refine (mem_unipB k).2 ⟨fun a b hba => ?_, fun a => ?_⟩
    · rw [elemGL_apply, Matrix.one_apply_ne hba.ne', if_neg fun e => ?_, add_zero]
      rw [e.1, e.2] at hba
      exact absurd hba hlt.not_gt
    · rw [elemGL_apply, Matrix.one_apply_eq, if_neg fun e => hne (e.1.symm.trans e.2), add_zero]
  refine ⟨elemGL i j hne t, hu, ?_, ?_⟩
  · show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, (elemGL i j hne t).val p.1 p.2)) = _
    congr 2
    rw [Finset.sum_eq_single_of_mem (i, j) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩)]
    · rw [elemGL_apply, Matrix.one_apply_ne hne, if_pos ⟨rfl, rfl⟩, zero_add]
    · rintro ⟨a, b⟩ hp hpne
      have hab : (b : ℕ) = a + 1 := (Finset.mem_filter.1 hp).2
      have hne' : a ≠ b := fun e => by rw [e] at hab; omega
      rw [elemGL_apply, Matrix.one_apply_ne hne', if_neg fun e => hpne (Prod.ext e.1 e.2), add_zero]
  · have hent : ∀ a b : Fin N, (pm k w * elemGL i j hne t * (pm k w)⁻¹).val a b =
        (1 : Matrix (Fin N) (Fin N) k) a b + if a = w i ∧ b = w j then t else 0 := by
      intro a b
      rw [conj_pm_apply, elemGL_apply]
      congr 1
      · by_cases e : a = b
        · rw [e, Matrix.one_apply_eq, Matrix.one_apply_eq]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne fun e' => e (w⁻¹.injective e')]
      · simp only [Equiv.Perm.inv_eq_iff_eq]
    refine mem_unipRad.2 ⟨mem_parab.2 fun a b hab => ?_, fun c x y => ?_⟩
    · have hne' : a ≠ b := fun e => by rw [e] at hab; exact lt_irrefl _ hab
      rw [hent, Matrix.one_apply_ne hne', if_neg fun e => ?_, add_zero]
      rw [e.1, e.2] at hab
      exact lt_asymm hab hb
    · rw [hent, if_neg fun e => ?_, add_zero]
      · by_cases e : x = y
        · rw [e, Matrix.one_apply_eq, Matrix.one_apply_eq]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne fun e' => e (by simpa using (stdBlocks d hd).injective e')]
      · have h1 := blk_apply (stdBlocks d hd) c x
        have h2 := blk_apply (stdBlocks d hd) c y
        rw [e.1] at h1
        rw [e.2] at h2
        rw [h1, h2] at hb
        exact lt_irrefl _ hb

end GlobalTheory.CompanionTheory.Rodier.RootElt
