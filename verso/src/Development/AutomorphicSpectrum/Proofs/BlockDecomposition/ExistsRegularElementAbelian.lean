import Mathlib
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.IwaGen

/- English proof (translation)
Introduce `n 𝔞 U`. Set `L : Fin n × Fin n → (↥𝔞 →ₗ[ℝ] ℂ)` to `fun p => { toFun := fun A => (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.1 p.1 - (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.2 p.2 map_add' := by`. Introduce `A B`. Simplify using `only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Use the proof step `map_smul' := by`. Introduce `c A`. Simplify using `only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, RingHom.id_apply, smul_sub] }`. Establish `hL : ∀ (p : Fin n × Fin n) (A : ↥𝔞), L p A = (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.1 p.1 - (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.2 p.2` using `fun _ _ => rfl`. Set `s : Finset (Submodule ℝ ↥𝔞)` to `(Finset.univ.image fun p => LinearMap.ker (L p)).erase ⊤`.

Establish `hs : (⊤ : Submodule ℝ ↥𝔞) ∉ s` using `Finset.notMem_erase _ _`. Take `⟨H, hH⟩` from `(Set.ne_univ_iff_exists_notMem _).1 (Subspace.biUnion_ne_univ_of_top_notMem hs)`. Use `⟨H, H.2, fun i j hij A hA => ?_⟩` and prove the remaining obligations. Establish `hker : H ∈ LinearMap.ker (L (i, j))`. Rewrite using `[LinearMap.mem_ker, hL]`.

Conclude with `sub_eq_zero.2 hij`. Establish `htop : LinearMap.ker (L (i, j)) = ⊤`. Assume the negation of the conclusion as `hne`. Apply `hH` to reduce the goal to its premises. Use `Set.mem_biUnion (x := LinearMap.ker (L (i, j))) ?_ hker` and prove the remaining obligations.

Conclude with `Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hne, Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩⟩)`. Establish `hA' : (⟨A, hA⟩ : ↥𝔞) ∈ LinearMap.ker (L (i, j))`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`. Rewrite `hA'` using `[LinearMap.mem_ker, hL]`.

Conclude with `sub_eq_zero.1 hA'`.
-/
theorem exists_regular_point : ∀ {n : ℕ} (𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (U : Matrix (Fin n) (Fin n) ℂ), ∃ H ∈ 𝔞, ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j →
      ∀ A ∈ 𝔞, (Uᴴ * A * U) i i = (Uᴴ * A * U) j j := by
  classical
  intro n 𝔞 U
  let L : Fin n × Fin n → (↥𝔞 →ₗ[ℝ] ℂ) := fun p =>
    { toFun := fun A => (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.1 p.1
        - (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.2 p.2
      map_add' := by
        intro A B
        simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
        ring
      map_smul' := by
        intro c A
        simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
          RingHom.id_apply, smul_sub] }
  have hL : ∀ (p : Fin n × Fin n) (A : ↥𝔞), L p A =
      (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.1 p.1
        - (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.2 p.2 := fun _ _ => rfl
  let s : Finset (Submodule ℝ ↥𝔞) :=
    (Finset.univ.image fun p => LinearMap.ker (L p)).erase ⊤
  have hs : (⊤ : Submodule ℝ ↥𝔞) ∉ s := Finset.notMem_erase _ _
  obtain ⟨H, hH⟩ := (Set.ne_univ_iff_exists_notMem _).1
    (Subspace.biUnion_ne_univ_of_top_notMem hs)
  refine ⟨H, H.2, fun i j hij A hA => ?_⟩
  have hker : H ∈ LinearMap.ker (L (i, j)) := by
    rw [LinearMap.mem_ker, hL]
    exact sub_eq_zero.2 hij
  have htop : LinearMap.ker (L (i, j)) = ⊤ := by
    by_contra hne
    apply hH
    refine Set.mem_biUnion (x := LinearMap.ker (L (i, j))) ?_ hker
    exact Finset.mem_coe.2 (Finset.mem_erase.2
      ⟨hne, Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩⟩)
  have hA' : (⟨A, hA⟩ : ↥𝔞) ∈ LinearMap.ker (L (i, j)) := by
    rw [htop]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker, hL] at hA'
  exact sub_eq_zero.1 hA'

end GlobalTheory.CompanionTheory.IwaGen
