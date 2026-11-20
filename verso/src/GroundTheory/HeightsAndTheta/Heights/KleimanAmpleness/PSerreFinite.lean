import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsPres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

/- English proof (translation)
Introduce `S _ _ N`. Establish `key : ∀ (k : ℕ) (M : Type (max u v)) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M] (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M → ∀ i, N + 1 ≤ i + k → ∀ c : ℤ, Module.Finite S (cohom 𝓜 i c)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Introduce `M _ _ _ _ 𝓜 _ i hi c`. Use `hTop S N M 𝓜 i c (by omega)` as an intermediate fact. Conclude with `⟨by rw [Subsingleton.elim (⊤ : Submodule S (cohom 𝓜 i c)) ⊥]; exact Submodule.fg_bot⟩`. Consider the case `succ k ih`. Introduce `M _ _ _ _ 𝓜 hM i hi c`.

Take `⟨F, _, _, _, _, K, _, _, _, _, 𝓕, 𝓚, r, b, d, f, g, hb, hK, hf, hg, hfg⟩` from `hPres S N M 𝓜 hM`. Establish `hF : Module.Finite S (cohom 𝓕 i c)` using `(hFree S N F 𝓕 r b d hb).1 i c`. Establish `hKf : Module.Finite S (cohom 𝓚 (i + 1) c)` using `ih K 𝓚 hK (i + 1) (by omega) c`. Take `⟨-, δ, hδ, -⟩` from `(hExact S N K F M 𝓚 𝓕 𝓜 f g hf hg hfg c).2 i`. Use `⟨Submodule.fg_of_fg_map_of_fg_inf_ker δ (IsNoetherian.noetherian _) ?_⟩` and prove the remaining obligations.

Rewrite using `[top_inf_eq, LinearMap.exact_iff.mp hδ, LinearMap.range_eq_map]`. Conclude with `hF.fg_top.map _`. Introduce `M _ _ _ _ 𝓜 hM i c`. Take `⟨M', _, _, _, _, 𝓜', f, g, hgf, hfg⟩` from `hLift S N M 𝓜`. Establish `hM' : Module.Finite (Poly S N) M'` using `Module.Finite.of_surjective f.toLin fun y => ⟨g.toLin y, hfg y⟩`.

Use `key (N + 1) M' 𝓜' hM' i (by omega) c` as an intermediate fact. Conclude with `Module.Finite.of_injective (cohomMap f i c) (hRet S N M M' 𝓜 𝓜' f g hgf i c)`.
-/
theorem SerreFinite.proof (hExact : CechExact.Statement.{u, max u v})
    (hTop : CechTop.Statement.{u, max u v}) (hFree : SerreFree.Statement.{u, max u v})
    (hPres : GradedPres.Statement.{u, v}) (hLift : GradedULift.Statement.{u, v})
    (hRet : CohomRetract.Statement.{u, v, max u v}) : SerreFinite.Statement.{u, v} := by
  intro S _ _ N

  have key : ∀ (k : ℕ) (M : Type (max u v)) [AddCommGroup M] [Module (Poly S N) M] [Module S M]
      [IsScalarTower S (Poly S N) M] (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
      ∀ i, N + 1 ≤ i + k → ∀ c : ℤ, Module.Finite S (cohom 𝓜 i c) := by
    intro k
    induction k with
    | zero =>
      intro M _ _ _ _ 𝓜 _ i hi c
      have := hTop S N M 𝓜 i c (by omega)
      exact ⟨by rw [Subsingleton.elim (⊤ : Submodule S (cohom 𝓜 i c)) ⊥]; exact Submodule.fg_bot⟩
    | succ k ih =>
      intro M _ _ _ _ 𝓜 hM i hi c
      obtain ⟨F, _, _, _, _, K, _, _, _, _, 𝓕, 𝓚, r, b, d, f, g, hb, hK, hf, hg, hfg⟩ :=
        hPres S N M 𝓜 hM
      have hF : Module.Finite S (cohom 𝓕 i c) := (hFree S N F 𝓕 r b d hb).1 i c
      have hKf : Module.Finite S (cohom 𝓚 (i + 1) c) := ih K 𝓚 hK (i + 1) (by omega) c
      obtain ⟨-, δ, hδ, -⟩ := (hExact S N K F M 𝓚 𝓕 𝓜 f g hf hg hfg c).2 i
      refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker δ (IsNoetherian.noetherian _) ?_⟩
      rw [top_inf_eq, LinearMap.exact_iff.mp hδ, LinearMap.range_eq_map]
      exact hF.fg_top.map _
  intro M _ _ _ _ 𝓜 hM i c
  obtain ⟨M', _, _, _, _, 𝓜', f, g, hgf, hfg⟩ := hLift S N M 𝓜
  have hM' : Module.Finite (Poly S N) M' :=
    Module.Finite.of_surjective f.toLin fun y => ⟨g.toLin y, hfg y⟩
  have := key (N + 1) M' 𝓜' hM' i (by omega) c
  exact Module.Finite.of_injective (cohomMap f i c) (hRet S N M M' 𝓜 𝓜' f g hgf i c)

end

end GroundTheory.Heights₂.Heights.Kleiman
