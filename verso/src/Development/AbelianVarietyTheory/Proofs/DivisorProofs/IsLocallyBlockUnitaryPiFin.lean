import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

/- English proof (translation)
Introduce `ι M _ _ _ _ s F hF n t`. Take `⟨U, htU, hfd, hst, ip, hsym, hpos, hadj⟩` from `hF (t.biUnion fun x => Finset.univ.image x)`. Establish `hmem : ∀ x ∈ t, ∀ i, x i ∈ U` using `fun x hx i => htU _ (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)`. Set `U' : Submodule ℂ (Fin n → M)` to `Submodule.pi Set.univ (fun _ => U)`. Set `ip' : (Fin n → M) →ₗ⋆[ℂ] (Fin n → M) →ₗ[ℂ] ℂ` to `∑ i : Fin n, (ip ∘ₛₗ (LinearMap.proj i : (Fin n → M) →ₗ[ℂ] M)).compl₂ (LinearMap.proj i : (Fin n → M) →ₗ[ℂ] M)`.

Establish `hip' : ∀ x y, ip' x y = ∑ i, ip (x i) (y i)`. Introduce `x y`. Simplify using `[ip', LinearMap.sum_apply]`. Use `⟨U', fun x hx i _ => hmem x hx i, ?_, ?_, ip', ?_, ?_, ?_⟩` and prove the remaining obligations. Set `g : (Fin n → U) →ₗ[ℂ] (Fin n → M)` to `LinearMap.pi fun i => U.subtype ∘ₗ LinearMap.proj i`.

Establish `hle : U' ≤ LinearMap.range g`. Introduce `x hx`. Conclude with `⟨fun i => ⟨x i, hx i (Set.mem_univ _)⟩, by ext i; rfl⟩`. Conclude with `Submodule.finiteDimensional_of_le hle`. Introduce `a b hab u hu i _`.

Conclude with `hst a b hab (u i) (hu i (Set.mem_univ _))`. Introduce `x hx y hy`. Rewrite using `[hip', hip', star_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => hsym _ (hx i (Set.mem_univ _)) _ (hy i (Set.mem_univ _))`. Introduce `x hx hx0`.

Rewrite using `[hip', Complex.re_sum]`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, x j ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx0 (funext h)`.

Establish `hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (ip (x i) (x i)).re`. Introduce `i _`. Distinguish the cases in `h : x i = 0`. Simplify using `[h]`. Conclude with `(hpos _ (hx i (Set.mem_univ _)) h).le`.

Conclude with `Finset.sum_pos' hnn ⟨j, Finset.mem_univ _, hpos _ (hx j (Set.mem_univ _)) hj⟩`. Introduce `a b hab x hx y hy`. Rewrite using `[hip', hip']`. Conclude with `Finset.sum_congr rfl fun i _ => hadj a b hab _ (hx i (Set.mem_univ _)) _ (hy i (Set.mem_univ _))`.
-/
theorem locU_pi_fin : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), LocU s F → ∀ n : ℕ, LocU s (fun a b => (LinearMap.pi fun i : Fin n => F a b ∘ₗ LinearMap.proj i : Module.End ℂ (Fin n → M))) := by
  intro ι M _ _ _ _ s F hF n t
  classical
  obtain ⟨U, htU, hfd, hst, ip, hsym, hpos, hadj⟩ := hF (t.biUnion fun x => Finset.univ.image x)
  have hmem : ∀ x ∈ t, ∀ i, x i ∈ U := fun x hx i =>
    htU _ (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
  let U' : Submodule ℂ (Fin n → M) := Submodule.pi Set.univ (fun _ => U)
  let ip' : (Fin n → M) →ₗ⋆[ℂ] (Fin n → M) →ₗ[ℂ] ℂ :=
    ∑ i : Fin n, (ip ∘ₛₗ (LinearMap.proj i : (Fin n → M) →ₗ[ℂ] M)).compl₂ (LinearMap.proj i : (Fin n → M) →ₗ[ℂ] M)
  have hip' : ∀ x y, ip' x y = ∑ i, ip (x i) (y i) := by
    intro x y
    simp [ip', LinearMap.sum_apply]
  refine ⟨U', fun x hx i _ => hmem x hx i, ?_, ?_, ip', ?_, ?_, ?_⟩
  · let g : (Fin n → U) →ₗ[ℂ] (Fin n → M) := LinearMap.pi fun i => U.subtype ∘ₗ LinearMap.proj i
    have hle : U' ≤ LinearMap.range g := by
      intro x hx
      exact ⟨fun i => ⟨x i, hx i (Set.mem_univ _)⟩, by ext i; rfl⟩
    exact Submodule.finiteDimensional_of_le hle
  · intro a b hab u hu i _
    exact hst a b hab (u i) (hu i (Set.mem_univ _))
  · intro x hx y hy
    rw [hip', hip', star_sum]
    exact Finset.sum_congr rfl fun i _ => hsym _ (hx i (Set.mem_univ _)) _ (hy i (Set.mem_univ _))
  · intro x hx hx0
    rw [hip', Complex.re_sum]
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (funext h)
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (ip (x i) (x i)).re := by
      intro i _
      by_cases h : x i = 0
      · simp [h]
      · exact (hpos _ (hx i (Set.mem_univ _)) h).le
    exact Finset.sum_pos' hnn ⟨j, Finset.mem_univ _, hpos _ (hx j (Set.mem_univ _)) hj⟩
  · intro a b hab x hx y hy
    rw [hip', hip']
    exact Finset.sum_congr rfl fun i _ => hadj a b hab _ (hx i (Set.mem_univ _)) _ (hy i (Set.mem_univ _))

end GlobalTheory.HoweR
