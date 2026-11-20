import Mathlib

/- English proof (translation)
Introduce `Q ι _ _ _ f hf v`. Use `Fintype.ofFinite ι` as an intermediate fact. Establish `hs : Function.Surjective (LinearMap.pi f : Q →ₗ[ℂ] (ι → ℂ))`. Rewrite using `[← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]`. Introduce `φ hφ`.

Establish `hsum : ∑ i, φ (fun j => if i = j then 1 else 0) • f i = 0`. Use extensionality with `q`. Establish `h1 : φ (LinearMap.pi f q) = 0` using `LinearMap.congr_fun hφ q`. Rewrite `h1` using `[LinearMap.pi_apply_eq_sum_univ]`. Simplify `h1` using `[LinearMap.sum_apply, mul_comm]`.

Establish `h0` using `Fintype.linearIndependent_iff.1 hf _ hsum`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.pi_apply_eq_sum_univ]`. Simplify using `[h0]`. Take `⟨q, hq⟩` from `hs v`.

Conclude with `⟨q, fun i => congrFun hq i⟩`.
-/
theorem UpperTheory.Reformulated.B.Qe54.exists_of_li :
    ∀ {Q ι : Type} [inst : AddCommGroup Q]
    [inst_1 : _root_.Module ℂ Q] [Finite ι] (f : ι → Q →ₗ[ℂ] ℂ),
    LinearIndependent ℂ f → ∀ (v : ι → ℂ), ∃ (q : Q), ∀ (i : ι), (f i : Q → ℂ) q = v i := by
  intro Q ι _ _ _ f hf v
  classical
  have := Fintype.ofFinite ι
  have hs : Function.Surjective (LinearMap.pi f : Q →ₗ[ℂ] (ι → ℂ)) := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro φ hφ
    have hsum : ∑ i, φ (fun j => if i = j then 1 else 0) • f i = 0 := by
      ext q
      have h1 : φ (LinearMap.pi f q) = 0 := LinearMap.congr_fun hφ q
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      simpa [LinearMap.sum_apply, mul_comm] using h1
    have h0 := Fintype.linearIndependent_iff.1 hf _ hsum
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp [h0]
  obtain ⟨q, hq⟩ := hs v
  exact ⟨q, fun i => congrFun hq i⟩
