import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite

noncomputable section

open CompanionTheory.Rg.Fl GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AutMult

namespace GlobalTheory.CompanionTheory.FactorIso

/- English proof (translation)
Introduce `G G₁ H _ _ _ _ _ _ π hπ j p hj hpj hc W hW`. Use `haveI := hπ.complete`. Establish `hu : IsUnitaryRep (π.comp j)` using `isUnitaryRep_comp hπ.unitary hj`. Use `⟨⟨W, hW.1.rep, isIrrUnitary_rep hu hW⟩, ?_⟩` and prove the remaining obligations. Use `show isoPart hW.1.rep (π.comp j) ⊤ = ⊤`.

Establish `hsub : IsSubrep (π.comp j) (isoPart hW.1.rep (π.comp j) ⊤)` using `isSubrep_isoPart`. Establish `hker : ∀ k, p k = 1 → ∀ v ∈ isoPart hW.1.rep (π.comp j) ⊤, π k v ∈ isoPart hW.1.rep (π.comp j) ⊤`. Introduce `k hk v hv`. Establish `hle : isoPart hW.1.rep (π.comp j) ⊤ ≤ (isoPart hW.1.rep (π.comp j) ⊤).comap (π k : H →ₗ[ℂ] H)` using `isoPart_le (hsub.1.preimage (π k).continuous) fun T hT x => apply_mem_isoPart (T := (π k).comp T) (mem_homIn_top.2 fun g y => by`. Establish `hcomm : π k * π (j g) = π (j g) * π k`.

Rewrite using `[← map_mul, ← map_mul, (hc g k hk).eq]`. Establish `hT'` using `hT.2 g y`. Simplify using `only [ContinuousLinearMap.comp_apply, hT', MonoidHom.comp_apply]`. Conclude with `DFunLike.congr_fun hcomm (T y)) x`. Conclude with `hle hv`.

Establish `hinv : IsSubrep π (isoPart hW.1.rep (π.comp j) ⊤)`. Use `⟨hsub.1, fun g v hv => ?_⟩` and prove the remaining obligations. Establish `hg : g = j (p g) * ((j (p g))⁻¹ * g)` using `by group`. Establish `h1` using `hsub.2 (p g) _ (hker ((j (p g))⁻¹ * g) (by simp [hpj]) v hv)`. Rewrite using `[hg, map_mul]`.

Simplify using `using h1`. Break down `hπ.irred.2 _ hinv with h | h` into its components or cases. It suffices to derive a contradiction. Apply `hW.2.1` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`.

Introduce `w hw`. Establish `hm : W.subtypeL ∈ homIn hW.1.rep (π.comp j) ⊤` using `mem_homIn_top.2 fun _ _ => rfl`. Use `apply_mem_isoPart hm ⟨w, hw⟩` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `using this`.

Conclude with `h`.
-/
theorem stIso : StIso := by
  intro G G₁ H _ _ _ _ _ _ π hπ j p hj hpj hc W hW
  haveI := hπ.complete
  have hu : IsUnitaryRep (π.comp j) := isUnitaryRep_comp hπ.unitary hj
  refine ⟨⟨W, hW.1.rep, isIrrUnitary_rep hu hW⟩, ?_⟩
  show isoPart hW.1.rep (π.comp j) ⊤ = ⊤
  have hsub : IsSubrep (π.comp j) (isoPart hW.1.rep (π.comp j) ⊤) := isSubrep_isoPart
  have hker : ∀ k, p k = 1 → ∀ v ∈ isoPart hW.1.rep (π.comp j) ⊤,
      π k v ∈ isoPart hW.1.rep (π.comp j) ⊤ := by
    intro k hk v hv
    have hle : isoPart hW.1.rep (π.comp j) ⊤ ≤
        (isoPart hW.1.rep (π.comp j) ⊤).comap (π k : H →ₗ[ℂ] H) :=
      isoPart_le (hsub.1.preimage (π k).continuous) fun T hT x =>
        apply_mem_isoPart (T := (π k).comp T) (mem_homIn_top.2 fun g y => by
          have hcomm : π k * π (j g) = π (j g) * π k := by
            rw [← map_mul, ← map_mul, (hc g k hk).eq]
          have hT' := hT.2 g y
          simp only [ContinuousLinearMap.comp_apply, hT', MonoidHom.comp_apply]
          exact DFunLike.congr_fun hcomm (T y)) x
    exact hle hv
  have hinv : IsSubrep π (isoPart hW.1.rep (π.comp j) ⊤) := by
    refine ⟨hsub.1, fun g v hv => ?_⟩
    have hg : g = j (p g) * ((j (p g))⁻¹ * g) := by group
    have h1 := hsub.2 (p g) _ (hker ((j (p g))⁻¹ * g) (by simp [hpj]) v hv)
    rw [hg, map_mul]
    simpa using h1
  rcases hπ.irred.2 _ hinv with h | h
  · exfalso
    apply hW.2.1
    rw [eq_bot_iff]
    intro w hw
    have hm : W.subtypeL ∈ homIn hW.1.rep (π.comp j) ⊤ := mem_homIn_top.2 fun _ _ => rfl
    have := apply_mem_isoPart hm ⟨w, hw⟩
    rw [h] at this
    simpa using this
  · exact h

end GlobalTheory.CompanionTheory.FactorIso

end
