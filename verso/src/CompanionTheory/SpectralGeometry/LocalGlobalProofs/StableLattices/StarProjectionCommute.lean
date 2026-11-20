import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CyclicScalar

/- English proof (translation)
The claim follows from `(LinearIsometry.mk (σ g).toLinearMap (hσ g)).inner_map_map x y`.
-/
theorem inner_map_map {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (g : G) (x y : H) :
    ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (σ g).toLinearMap (hσ g)).inner_map_map x y

/- English proof (translation)
Establish `h : σ g * σ g⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Conclude with `DFunLike.congr_fun h x`.
-/
theorem map_inv_map {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (g : G) (x : H) : σ g (σ g⁻¹ x) = x := by
  have h : σ g * σ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact DFunLike.congr_fun h x

/- English proof (translation)
Rewrite `hv`, the goal using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Rewrite using `[← map_inv_map σ g u, inner_map_map σ hσ]`. Conclude with `hv _ (hU _ _ hu)`.
-/
theorem orthogonal_stable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (U : Submodule ℂ H)
    (hU : ∀ g, ∀ v ∈ U, σ g v ∈ U) (g : G) (v : H) (hv : v ∈ Uᗮ) : σ g v ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  rw [← map_inv_map σ g u, inner_map_map σ hσ]
  exact hv _ (hU _ _ hu)

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [ContinuousLinearMap.mul_apply]`. Establish `h1 : U.starProjection v ∈ U` using `Submodule.starProjection_apply_mem U v`. Establish `h2 : v - U.starProjection v ∈ Uᗮ` using `Submodule.sub_starProjection_mem_orthogonal v`. Establish `h3 : σ g v = σ g (U.starProjection v) + σ g (v - U.starProjection v)`.

Rewrite using `[← map_add]`. Simplify using the standard rewrite rules. Rewrite using `[h3, map_add, Submodule.starProjection_eq_self_iff.2 (hU g _ h1), (Submodule.starProjection_apply_eq_zero_iff U).2 (orthogonal_stable σ hσ U hU g _ h2), add_zero]`.
-/
theorem starProjection_commute {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (U : Submodule ℂ H)
    [U.HasOrthogonalProjection] (hU : ∀ g, ∀ v ∈ U, σ g v ∈ U) (g : G) :
    U.starProjection * σ g = σ g * U.starProjection := by
  ext v
  simp only [ContinuousLinearMap.mul_apply]
  have h1 : U.starProjection v ∈ U := Submodule.starProjection_apply_mem U v
  have h2 : v - U.starProjection v ∈ Uᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have h3 : σ g v = σ g (U.starProjection v) + σ g (v - U.starProjection v) := by
    rw [← map_add]; simp
  rw [h3, map_add, Submodule.starProjection_eq_self_iff.2 (hU g _ h1),
    (Submodule.starProjection_apply_eq_zero_iff U).2 (orthogonal_stable σ hσ U hU g _ h2), add_zero]

/- English proof (translation)
Introduce `G H _ _ _ _ σ hσ Q ξ hQ hξQ hξ hcomm hscal`. Use `haveI : CompleteSpace Q := hQ.completeSpace_coe`. Set `S : Submodule ℂ H` to `Submodule.span ℂ (Set.range fun g => σ g ξ)`. Establish `hSstable : ∀ g, ∀ v ∈ S, σ g v ∈ S`. Introduce `g v hv`.

Establish `: S ≤ S.comap (σ g : H →ₗ[ℂ] H)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, rfl⟩`. Use `Submodule.subset_span ⟨g * h, ?_⟩` and prove the remaining obligations. Simplify using `[map_mul]`.

Conclude with `this hv`. Establish `hW : IsSubrep σ S.topologicalClosure` using `isSubrep_topologicalClosure hSstable`. Establish `horbit : ∀ g, σ g ξ ∈ S.topologicalClosure` using `fun g => S.le_topologicalClosure (Submodule.subset_span ⟨g, rfl⟩)`. Establish `hξW : ξ ∈ S.topologicalClosure` using `by simpa using horbit 1`. Establish `hmin : ∀ A : Submodule ℂ H, IsClosed (A : Set H) → (∀ g, σ g ξ ∈ A) → S.topologicalClosure ≤ A`.

Introduce `A hA h`. Use `Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) hA` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `h g`. Establish `hline : ∀ w ∈ S.topologicalClosure, Q.starProjection w ∈ (ℂ ∙ ξ)`.

Establish `hclosed : IsClosed (((ℂ ∙ ξ).comap (Q.starProjection : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H)` using `(Submodule.closed_of_finiteDimensional (ℂ ∙ ξ)).preimage Q.starProjection.continuous`. Use `fun w hw => hmin _ hclosed (fun g => ?_) hw` and prove the remaining obligations. Take `⟨c, hc⟩` from `hscal g`. Establish `e : σ g ξ = c • ξ + (σ g ξ - c • ξ)` using `by abel`. Express the relevant statement in the definitionally equal form `Q.starProjection (σ g ξ) ∈ (ℂ ∙ ξ)`.

Rewrite using `[e, map_add, (Submodule.starProjection_apply_eq_zero_iff Q).2 hc, add_zero, map_smul, Submodule.starProjection_eq_self_iff.2 hξQ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self ξ)`. Use `⟨S.topologicalClosure, hW, fun h => hξ (by simpa [h] using hξW), fun U hUW hU => ?_⟩` and prove the remaining obligations. Use `haveI : CompleteSpace U := hU.1.completeSpace_coe`. Establish `hPc` using `starProjection_commute σ hσ U hU.2`.

Establish `hPQ : U.starProjection ξ ∈ Q` using `hcomm _ hPc ξ hξQ`. Establish `hPU : U.starProjection ξ ∈ U` using `Submodule.starProjection_apply_mem U ξ`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ℂ, c • ξ = U.starProjection ξ := by`. Use `hline _ (hUW hPU)` as an intermediate fact. Rewrite `this` using `[Submodule.starProjection_eq_self_iff.2 hPQ]`.

Conclude with `Submodule.mem_span_singleton.1 this`. Establish `hcc : c * c = c`. Establish `h1 : U.starProjection (c • ξ) = c • ξ`. Rewrite using `[hc]`. Conclude with `Submodule.starProjection_eq_self_iff.2 hPU`.

Rewrite `h1` using `[map_smul, ← hc, smul_smul]`. Establish `h2 : (c * c - c) • ξ = 0` using `by rw [sub_smul, h1, sub_self]`. Conclude with `sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hξ)`. Establish `hc01 : c = 0 ∨ c = 1`. Establish `: c * (c - 1) = 0` using `by rw [mul_sub, hcc]; ring`.

Conclude with `(mul_eq_zero.1 this).imp id sub_eq_zero.1`. Break down `hc01 with rfl | rfl` into its components or cases. Use `left`. Establish `hP0 : U.starProjection ξ = 0` using `by rw [← hc, zero_smul]`. Establish `hle : S.topologicalClosure ≤ Uᗮ`.

Use `hmin _ (Submodule.isClosed_orthogonal U) fun g => ?_` and prove the remaining obligations. Use `(Submodule.starProjection_apply_eq_zero_iff U).1 ?_` and prove the remaining obligations. Use `DFunLike.congr_fun (hPc g) ξ` as an intermediate fact. Simplify `this` using `[hP0]`. Use `(Submodule.eq_bot_iff U).2 fun x hx => ?_` and prove the remaining obligations.

Conclude with `inner_self_eq_zero.1 ((Submodule.mem_orthogonal U x).1 (hle (hUW hx)) x hx)`. Use `right`. Establish `hξU : ξ ∈ U`. Rewrite `hc` using `[one_smul]`. Rewrite using `[hc]`.

Conclude with `hPU`. Conclude with `le_antisymm hUW (hmin _ hU.1 fun g => hU.2 g ξ hξU)`.
-/
theorem exists_isIrredSubrep : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (Q : Submodule ℂ H) (ξ : H), IsClosed (Q : Set H) → ξ ∈ Q → ξ ≠ 0 →
    (∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → ∀ v ∈ Q, T v ∈ Q) →
    (∀ g, ∃ c : ℂ, σ g ξ - c • ξ ∈ Qᗮ) → ∃ W, IsIrredSubrep σ W := by
  intro G H _ _ _ _ σ hσ Q ξ hQ hξQ hξ hcomm hscal
  haveI : CompleteSpace Q := hQ.completeSpace_coe

  let S : Submodule ℂ H := Submodule.span ℂ (Set.range fun g => σ g ξ)
  have hSstable : ∀ g, ∀ v ∈ S, σ g v ∈ S := by
    intro g v hv
    have : S ≤ S.comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, rfl⟩
      refine Submodule.subset_span ⟨g * h, ?_⟩
      simp [map_mul]
    exact this hv
  have hW : IsSubrep σ S.topologicalClosure := isSubrep_topologicalClosure hSstable
  have horbit : ∀ g, σ g ξ ∈ S.topologicalClosure := fun g =>
    S.le_topologicalClosure (Submodule.subset_span ⟨g, rfl⟩)
  have hξW : ξ ∈ S.topologicalClosure := by simpa using horbit 1

  have hmin : ∀ A : Submodule ℂ H, IsClosed (A : Set H) → (∀ g, σ g ξ ∈ A) → S.topologicalClosure ≤ A := by
    intro A hA h
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) hA
    rintro _ ⟨g, rfl⟩
    exact h g

  have hline : ∀ w ∈ S.topologicalClosure, Q.starProjection w ∈ (ℂ ∙ ξ) := by
    have hclosed : IsClosed (((ℂ ∙ ξ).comap (Q.starProjection : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) :=
      (Submodule.closed_of_finiteDimensional (ℂ ∙ ξ)).preimage Q.starProjection.continuous
    refine fun w hw => hmin _ hclosed (fun g => ?_) hw
    obtain ⟨c, hc⟩ := hscal g
    have e : σ g ξ = c • ξ + (σ g ξ - c • ξ) := by abel
    change Q.starProjection (σ g ξ) ∈ (ℂ ∙ ξ)
    rw [e, map_add, (Submodule.starProjection_apply_eq_zero_iff Q).2 hc, add_zero, map_smul,
      Submodule.starProjection_eq_self_iff.2 hξQ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self ξ)
  refine ⟨S.topologicalClosure, hW, fun h => hξ (by simpa [h] using hξW), fun U hUW hU => ?_⟩
  haveI : CompleteSpace U := hU.1.completeSpace_coe
  have hPc := starProjection_commute σ hσ U hU.2
  have hPQ : U.starProjection ξ ∈ Q := hcomm _ hPc ξ hξQ
  have hPU : U.starProjection ξ ∈ U := Submodule.starProjection_apply_mem U ξ
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ξ = U.starProjection ξ := by
    have := hline _ (hUW hPU)
    rw [Submodule.starProjection_eq_self_iff.2 hPQ] at this
    exact Submodule.mem_span_singleton.1 this
  have hcc : c * c = c := by
    have h1 : U.starProjection (c • ξ) = c • ξ := by
      rw [hc]; exact Submodule.starProjection_eq_self_iff.2 hPU
    rw [map_smul, ← hc, smul_smul] at h1
    have h2 : (c * c - c) • ξ = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hξ)
  have hc01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by rw [mul_sub, hcc]; ring
    exact (mul_eq_zero.1 this).imp id sub_eq_zero.1
  rcases hc01 with rfl | rfl
  · left
    have hP0 : U.starProjection ξ = 0 := by rw [← hc, zero_smul]
    have hle : S.topologicalClosure ≤ Uᗮ := by
      refine hmin _ (Submodule.isClosed_orthogonal U) fun g => ?_
      refine (Submodule.starProjection_apply_eq_zero_iff U).1 ?_
      have := DFunLike.congr_fun (hPc g) ξ
      simpa [hP0] using this
    refine (Submodule.eq_bot_iff U).2 fun x hx => ?_
    exact inner_self_eq_zero.1 ((Submodule.mem_orthogonal U x).1 (hle (hUW hx)) x hx)
  · right
    have hξU : ξ ∈ U := by
      rw [one_smul] at hc
      rw [hc]; exact hPU
    exact le_antisymm hUW (hmin _ hU.1 fun g => hU.2 g ξ hξU)

end GlobalTheory.CompanionTheory.CyclicScalar
