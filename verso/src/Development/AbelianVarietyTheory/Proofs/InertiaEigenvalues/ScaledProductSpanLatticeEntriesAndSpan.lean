import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TupMemLatT
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.TraceConjugationCover

/- English proof (translation)
Introduce `l _ Γ _ a m ρs L t M hρ ht hspan`. Establish `hsm : ∀ k (c : ℤ_[l]) (y : Om l), y ∈ (L k).1 → c • y ∈ (L k).1`. Introduce `k c y hy`. Rewrite using `[← IsScalarTower.algebraMap_smul ℚ_[l] c y]`. Conclude with `(L k).1.smul_mem hy`.

Set `S : Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l))` to `{ carrier := {x | ∀ k i j, x k i j ∈ (L k).1} add_mem' := fun {x y} hx hy k i j => by`. Simplify using `using (L k).1.add_mem (hx k i j) (hy k i j)`. Use the proof step `zero_mem' := fun k i j => by simpa using (L k).1.zero_mem`. Use the proof step `smul_mem' := fun c x hx k i j => by`. Simplify using `using hsm k c _ (hx k i j) }`.

Establish `hlM : ∀ k, ((l : Om l) ^ M) ∈ (L k).1` using `fun k => pow_mem (by simpa using (L k).1.natCast_mem l) M`. Establish `hsingle : ∀ k (y : Matrix (Fin a) (Fin a) (Om l)), (∀ i j, y i j ∈ (L k).1) → Pi.single k y ∈ S`. Introduce `k y hy k' i j`. Distinguish the cases in `h : k' = k`. Substitute `h` using the available equality.

Simplify using `using hy i j`. Simplify using `[Pi.single_apply, h, (L k').1.zero_mem]`. Establish `hle : latT ρs t M ≤ S`. Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨g, rfl⟩ k i j`. Conclude with `hρ k g i j`. Rewrite using `[latL, Submodule.span_le]`. Introduce `z hz`. Simplify using `only [Set.mem_iUnion, Set.mem_image] at hz`.

Take `⟨k, y, hy, rfl⟩` from `hz`. Use `hsingle k _ fun i j => ?_` and prove the remaining obligations. Simplify using `using (L k).1.mul_mem (hlM k) (ht k y hy i j)`. Use `⟨fun x hx => hle hx, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Establish `hsing : ∀ k, ∀ y ∈ t k, Pi.single k y ∈ Submodule.span ℚ_[l] (latT ρs t M : Set (Fin m → Matrix (Fin a) (Fin a) (Om l)))`. Introduce `k y hy`. Establish `hne : ((l : ℚ_[l]) ^ M) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)`. Establish `hmem : Pi.single k ((l : Om l) ^ M • y) ∈ latT ρs t M` using `Submodule.mem_sup_right (Submodule.subset_span (Set.mem_iUnion.2 ⟨k, y, hy, rfl⟩))`. Establish `heq : (l : Om l) ^ M • y = ((l : ℚ_[l]) ^ M) • y`.

Rewrite using `[← algebraMap_smul (Om l) ((l : ℚ_[l]) ^ M) y]`. Simplify using the standard rewrite rules. Establish `: (Pi.single k y : Fin m → Matrix (Fin a) (Fin a) (Om l)) = ((l : ℚ_[l]) ^ M)⁻¹ • (Pi.single k ((l : Om l) ^ M • y) : Fin m → Matrix (Fin a) (Fin a) (Om l))`. Rewrite using `[heq, Pi.single_smul', inv_smul_smul₀ hne]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`. Establish `hk : ∀ k, Pi.single k (x k) ∈ Submodule.span ℚ_[l] (latT ρs t M : Set (Fin m → Matrix (Fin a) (Fin a) (Om l)))`. Introduce `k`. Establish `h1` using `hspan k (x k) (hx k)`. Establish `h2 : LinearMap.single ℚ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k (x k) ∈ Submodule.map (LinearMap.single ℚ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k) (Submodule.span ℚ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))))` using `Submodule.mem_map_of_mem h1`.

Rewrite `h2` using `[Submodule.map_span]`. Use `(Submodule.span_le.2 ?_) h2` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hsing k y hy`. Rewrite using `[← Finset.univ_sum_single x]`.

Conclude with `Submodule.sum_mem _ fun k _ => hk k`.
-/
theorem latT_entries_and_span : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (L : Fin m → FinExt l) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k g i j, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ (L k).1) → (∀ k, ∀ x ∈ t k, ∀ i j, x i j ∈ (L k).1) → (∀ k (x : Matrix (Fin a) (Fin a) (Om l)), (∀ i j, x i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l)))) → (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∀ k i j, x k i j ∈ (L k).1) ∧ ∀ x : Fin m → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (GlobalTheory.TraceConjugationCover.latT ρs t M : Set (Fin m → Matrix (Fin a) (Fin a) (Om l))) := by
  intro l _ Γ _ a m ρs L t M hρ ht hspan

  have hsm : ∀ k (c : ℤ_[l]) (y : Om l), y ∈ (L k).1 → c • y ∈ (L k).1 := by
    intro k c y hy
    rw [← IsScalarTower.algebraMap_smul ℚ_[l] c y]
    exact (L k).1.smul_mem hy
  let S : Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l)) :=
    { carrier := {x | ∀ k i j, x k i j ∈ (L k).1}
      add_mem' := fun {x y} hx hy k i j => by
        simpa using (L k).1.add_mem (hx k i j) (hy k i j)
      zero_mem' := fun k i j => by simpa using (L k).1.zero_mem
      smul_mem' := fun c x hx k i j => by
        simpa using hsm k c _ (hx k i j) }
  have hlM : ∀ k, ((l : Om l) ^ M) ∈ (L k).1 := fun k =>
    pow_mem (by simpa using (L k).1.natCast_mem l) M
  have hsingle : ∀ k (y : Matrix (Fin a) (Fin a) (Om l)), (∀ i j, y i j ∈ (L k).1) →
      Pi.single k y ∈ S := by
    intro k y hy k' i j
    by_cases h : k' = k
    · subst h; simpa using hy i j
    · simp [Pi.single_apply, h, (L k').1.zero_mem]
  have hle : latT ρs t M ≤ S := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩ k i j
      exact hρ k g i j
    · rw [latL, Submodule.span_le]
      intro z hz
      simp only [Set.mem_iUnion, Set.mem_image] at hz
      obtain ⟨k, y, hy, rfl⟩ := hz
      refine hsingle k _ fun i j => ?_
      simpa using (L k).1.mul_mem (hlM k) (ht k y hy i j)
  refine ⟨fun x hx => hle hx, ?_⟩
  intro x hx
  have hsing : ∀ k, ∀ y ∈ t k, Pi.single k y ∈
      Submodule.span ℚ_[l] (latT ρs t M : Set (Fin m → Matrix (Fin a) (Fin a) (Om l))) := by
    intro k y hy
    have hne : ((l : ℚ_[l]) ^ M) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    have hmem : Pi.single k ((l : Om l) ^ M • y) ∈ latT ρs t M :=
      Submodule.mem_sup_right (Submodule.subset_span (Set.mem_iUnion.2 ⟨k, y, hy, rfl⟩))
    have heq : (l : Om l) ^ M • y = ((l : ℚ_[l]) ^ M) • y := by
      rw [← algebraMap_smul (Om l) ((l : ℚ_[l]) ^ M) y]
      simp
    have : (Pi.single k y : Fin m → Matrix (Fin a) (Fin a) (Om l)) = ((l : ℚ_[l]) ^ M)⁻¹ • (Pi.single k ((l : Om l) ^ M • y) : Fin m → Matrix (Fin a) (Fin a) (Om l)) := by
      rw [heq, Pi.single_smul', inv_smul_smul₀ hne]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have hk : ∀ k, Pi.single k (x k) ∈
      Submodule.span ℚ_[l] (latT ρs t M : Set (Fin m → Matrix (Fin a) (Fin a) (Om l))) := by
    intro k
    have h1 := hspan k (x k) (hx k)
    have h2 : LinearMap.single ℚ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k (x k) ∈
        Submodule.map (LinearMap.single ℚ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k)
          (Submodule.span ℚ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l)))) :=
      Submodule.mem_map_of_mem h1
    rw [Submodule.map_span] at h2
    refine (Submodule.span_le.2 ?_) h2
    rintro _ ⟨y, hy, rfl⟩
    exact hsing k y hy
  rw [← Finset.univ_sum_single x]
  exact Submodule.sum_mem _ fun k _ => hk k

end GlobalTheory.TraceConjugationCover
