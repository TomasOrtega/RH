import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed

open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DirectFactor

/- English proof (translation)
Introduce `G G₁ H _ _ _ _ π hπ j p hp hc x y hy hy0 hxy`. Set `W₀ : Submodule ℂ H` to `Submodule.span ℂ (Set.range fun q : G₁ × H => π (j q.1) (y q.2))`. Establish `hgen : ∀ (g' : G₁) (h : H), π (j g') (y h) ∈ W₀` using `fun g' h => Submodule.subset_span ⟨(g', h), rfl⟩`. Establish `hinv : ∀ g, ∀ v ∈ W₀, π g v ∈ W₀`. Introduce `g v hv`.

Take `⟨k, hk, hg⟩ : ∃ k, p k = 1 ∧ g = j (p g) * k` from `⟨(j (p g))⁻¹ * g, by simp [hp], by simp⟩`. Establish `hpg : π g = π (j (p g)) * π k`. Use `congrArg π hg` as an intermediate fact. Rewrite `this` using `[map_mul]`. Then use the resulting hypothesis. Establish `hKB : ∀ g', π k * π (j g') = π (j g') * π k` using `fun g' => by`.

Rewrite using `[← map_mul, ← map_mul, (hc g' k hk).eq]`. Establish `hKy : π k * y = y * π k` using `hy (π k) hKB`. Establish `a1 : ∀ v, π k (y v) = y (π k v)` using `fun v => DFunLike.congr_fun hKy v`. Establish `a2 : ∀ g' v, π k (π (j g') v) = π (j g') (π k v)` using `fun g' v => DFunLike.congr_fun (hKB g') v`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem v hv`. Take `⟨⟨g', h⟩, rfl⟩` from `hv`. Establish `e : π g (π (j g') (y h)) = π (j (p g * g')) (y (π k h))`. Rewrite using `[hpg, map_mul, map_mul]`. Simplify using `only [ContinuousLinearMap.mul_apply, a1, a2]`.

Simplify `hgen (p g * g') (π k h)` using `only [e]`. Consider the case `zero => simp`. Consider the case `add u w _ _ hu hw => simpa only [map_add] using W₀.add_mem hu hw`. Consider the case `smul c u _ hu => simpa only [map_smul] using W₀.smul_mem c hu`. Establish `hker : W₀.topologicalClosure ≤ LinearMap.ker (x : H →ₗ[ℂ] H)`.

Use `Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker x)` and prove the remaining obligations. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨g', h⟩, rfl⟩`. Conclude with `DFunLike.congr_fun (hxy g') h`. Break down `hπ.2 _ (isSubrep_topologicalClosure hinv) with hbot | htop` into its components or cases.

It suffices to derive a contradiction. Apply `hy0` to reduce the goal to its premises. Use extensionality with `h`. Establish `hm : y h ∈ W₀.topologicalClosure`. Apply `Submodule.le_topologicalClosure` to reduce the goal to its premises.

Simplify using `using hgen 1 h`. Rewrite `hm` using `[hbot]`. Simplify using `using hm`. Use extensionality with `h`. Establish `hm : h ∈ W₀.topologicalClosure` using `by rw [htop]; trivial`.

Simplify using `using hker hm`.
-/
theorem bicommutant_restriction_prime :
    ∀ (G G₁ H : Type) [Group G] [Group G₁] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)), IsTopIrreducible π → ∀ (j : G₁ →* G) (p : G →* G₁),
    (∀ x, p (j x) = x) → (∀ x g, p g = 1 → Commute (j x) g) → ∀ x y : H →L[ℂ] H,
    (∀ T : H →L[ℂ] H, (∀ g, T * π (j g) = π (j g) * T) → T * y = y * T) → y ≠ 0 →
    (∀ g, x * π (j g) * y = 0) → x = 0 := by
  intro G G₁ H _ _ _ _ π hπ j p hp hc x y hy hy0 hxy
  let W₀ : Submodule ℂ H := Submodule.span ℂ (Set.range fun q : G₁ × H => π (j q.1) (y q.2))
  have hgen : ∀ (g' : G₁) (h : H), π (j g') (y h) ∈ W₀ := fun g' h =>
    Submodule.subset_span ⟨(g', h), rfl⟩
  have hinv : ∀ g, ∀ v ∈ W₀, π g v ∈ W₀ := by
    intro g v hv
    obtain ⟨k, hk, hg⟩ : ∃ k, p k = 1 ∧ g = j (p g) * k :=
      ⟨(j (p g))⁻¹ * g, by simp [hp], by simp⟩
    have hpg : π g = π (j (p g)) * π k := by
      have := congrArg π hg
      rwa [map_mul] at this
    have hKB : ∀ g', π k * π (j g') = π (j g') * π k := fun g' => by
      rw [← map_mul, ← map_mul, (hc g' k hk).eq]
    have hKy : π k * y = y * π k := hy (π k) hKB
    have a1 : ∀ v, π k (y v) = y (π k v) := fun v => DFunLike.congr_fun hKy v
    have a2 : ∀ g' v, π k (π (j g') v) = π (j g') (π k v) := fun g' v =>
      DFunLike.congr_fun (hKB g') v
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨g', h⟩, rfl⟩ := hv
      have e : π g (π (j g') (y h)) = π (j (p g * g')) (y (π k h)) := by
        rw [hpg, map_mul, map_mul]
        simp only [ContinuousLinearMap.mul_apply, a1, a2]
      simpa only [e] using hgen (p g * g') (π k h)
    | zero => simp
    | add u w _ _ hu hw => simpa only [map_add] using W₀.add_mem hu hw
    | smul c u _ hu => simpa only [map_smul] using W₀.smul_mem c hu
  have hker : W₀.topologicalClosure ≤ LinearMap.ker (x : H →ₗ[ℂ] H) := by
    refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker x)
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g', h⟩, rfl⟩
    exact DFunLike.congr_fun (hxy g') h
  rcases hπ.2 _ (isSubrep_topologicalClosure hinv) with hbot | htop
  · exfalso
    apply hy0
    ext h
    have hm : y h ∈ W₀.topologicalClosure := by
      apply Submodule.le_topologicalClosure
      simpa using hgen 1 h
    rw [hbot] at hm
    simpa using hm
  · ext h
    have hm : h ∈ W₀.topologicalClosure := by rw [htop]; trivial
    simpa using hker hm

end GlobalTheory.CompanionTheory.DirectFactor
