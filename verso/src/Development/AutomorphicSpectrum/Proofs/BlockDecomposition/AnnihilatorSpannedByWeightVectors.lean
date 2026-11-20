import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.EigenvectorsSumZeroEqZero

noncomputable section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.P6.r14a.GlobalTheory.CompanionTheory.PresRho.eq_zero_of_sum_weightVec T f hf s`.
-/
theorem eq_zero_of_sum_weightVec {ι κ A : Type} [DecidableEq ι] [AddCommGroup A] [Module ℂ A]
    (T : κ → Module.End ℂ A) (f : ι → κ → ℂ) (hf : Function.Injective f) (s : Finset ι) :
    ∀ v : ι → A, (∀ i ∈ s, ∀ k, T k (v i) = f i k • v i) → ∑ i ∈ s, v i = 0 →
      ∀ i ∈ s, v i = 0 :=
  _root_.UpperTheory.Reformulated.B.P6.r14a.GlobalTheory.CompanionTheory.PresRho.eq_zero_of_sum_weightVec T f hf s

def wtPart {n : ℕ} (x : U n) (w : Fin n → ℤ) : U n :=
  ∑ m ∈ (pbw.repr x).support.filter (fun m => wt m = w), pbw.repr x m • canon m

/- English proof (translation)
Introduce `k`. Simplify using `only [wtPart, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub, (Finset.mem_filter.1 hm).2, smul_comm]`.
-/
theorem isAdW_wtPart {n : ℕ} (x : U n) (w : Fin n → ℤ) : IsAdW w (wtPart x w) := by
  intro k
  simp only [wtPart, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub,
    (Finset.mem_filter.1 hm).2, smul_comm]

/- English proof (translation)
Simplify using `only [wtPart]`. Rewrite using `[Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm)]`. Conclude with `sum_repr_canon x`.
-/
theorem sum_wtPart {n : ℕ} (x : U n) :
    ∑ w ∈ (pbw.repr x).support.image wt, wtPart x w = x := by
  simp only [wtPart]
  rw [Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm)]
  exact sum_repr_canon x

/- English proof (translation)
Establish `hinj : Function.Injective (fun (w : Fin n → ℤ) (k : Fin n) => rhoVec n k + (w k : ℂ))`. Introduce `w w' h`. Use function extensionality and compare the values at `k`. Use `congrFun h k` as an intermediate fact. Simplify using `using this`.

Establish `hz` using `eq_zero_of_sum_weightVec (fun k : Fin n => φ (e (k, k))) (fun (w : Fin n → ℤ) k => rhoVec n k + (w k : ℂ)) hinj ((pbw.repr x).support.image wt) (fun w => φ (wtPart x w) t) (fun w _ k => by`. Establish `h1 : e (k, k) * wtPart x w = wtPart x w * e (k, k) + (w k : ℂ) • wtPart x w`. Rewrite using `[← isAdW_wtPart x w k]`. Normalize the expressions using the abelian group laws. Establish `h2` using `congrArg (fun u => φ u t) h1`.

Simplify using `only [map_mul, map_add, map_smul, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, hd k, add_smul] at h2 ⊢`. Rewrite using `[h2])`. Use the proof step `(by`. Establish `h3` using `congrArg (fun u => φ u t) (sum_wtPart x)`. Simplify using `only [map_sum, LinearMap.sum_apply] at h3`.

Rewrite using `[h3, hx])`. Rewrite using `[← sum_wtPart x]`. Conclude with `Submodule.sum_mem _ fun w hw => Submodule.subset_span ⟨w, isAdW_wtPart x w, hz w hw⟩`.
-/
theorem mem_span_isAdW_of_kills {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (x : U n) (hx : φ x t = 0) :
    x ∈ Submodule.span ℂ {y : U n | ∃ μ : Fin n → ℤ, IsAdW μ y ∧ φ y t = 0} := by
  classical
  have hinj : Function.Injective (fun (w : Fin n → ℤ) (k : Fin n) => rhoVec n k + (w k : ℂ)) := by
    intro w w' h
    funext k
    have := congrFun h k
    simpa using this
  have hz := eq_zero_of_sum_weightVec (fun k : Fin n => φ (e (k, k)))
    (fun (w : Fin n → ℤ) k => rhoVec n k + (w k : ℂ)) hinj ((pbw.repr x).support.image wt)
    (fun w => φ (wtPart x w) t)
    (fun w _ k => by
      have h1 : e (k, k) * wtPart x w = wtPart x w * e (k, k) + (w k : ℂ) • wtPart x w := by
        rw [← isAdW_wtPart x w k]; abel
      have h2 := congrArg (fun u => φ u t) h1
      simp only [map_mul, map_add, map_smul, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.smul_apply, hd k, add_smul] at h2 ⊢
      rw [h2])
    (by
      have h3 := congrArg (fun u => φ u t) (sum_wtPart x)
      simp only [map_sum, LinearMap.sum_apply] at h3
      rw [h3, hx])
  rw [← sum_wtPart x]
  exact Submodule.sum_mem _ fun w hw => Submodule.subset_span ⟨w, isAdW_wtPart x w, hz w hw⟩

end GlobalTheory.CompanionTheory.PresRho
