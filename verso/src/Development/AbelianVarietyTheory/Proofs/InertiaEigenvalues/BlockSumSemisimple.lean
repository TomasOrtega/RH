import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfSimpleSSup
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

/- English proof (translation)
Use `isSS_of_sSup_irreducible_eq_top _ ({LinearMap.range (LinearMap.inl k (Fin r → k) (Fin t → k))} ∪ Set.range fun c : Fin t => Submodule.span k {((0, Pi.single c 1) : (Fin r → k) × (Fin t → k))}) ?_ ?_` and prove the remaining obligations. Introduce and unpack `U (rfl | ⟨c, rfl⟩)`. Establish `key : ∀ g (v : Fin r → k), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum ρ χ g (LinearMap.inl k (Fin r → k) (Fin t → k) v) = LinearMap.inl k (Fin r → k) (Fin t → k) (matRep ρ g v)`. Introduce `g v`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum_apply]`.

Use `Prod.ext rfl (funext fun c => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `⟨?_, fun U' hle hU' => ?_⟩` and prove the remaining obligations. Introduce and unpack `g _ ⟨v, rfl⟩`. Conclude with `⟨_, (key g v).symm⟩`.

Establish `hst : Stable (matRep ρ) (U'.comap (LinearMap.inl k (Fin r → k) (Fin t → k)))`. Introduce `g v hv`. Rewrite using `[Submodule.mem_comap, ← key]`. Conclude with `hU' g _ hv`. Establish `hmap` using `Submodule.map_comap_eq_self hle`.

Break down `hρ.2 _ hst with h | h` into its components or cases. Use `left`. Rewrite using `[← hmap, h, Submodule.map_bot]`. Use `right`. Rewrite using `[← hmap, h, Submodule.map_top]`.

Use `⟨?_, fun U' hle _ => ?_⟩` and prove the remaining obligations. Introduce `g v hv`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hv`. Use `Submodule.mem_span_singleton.2 ⟨a * ((χ c g : kˣ) : k), ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum_apply]`.

Use `Prod.ext ?_ (funext fun c' => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Distinguish the cases in `h : c' = c`. Substitute `h` using the available equality. Simplify using `[mul_comm]`.

Simplify using `[h]`. Establish `hne : ((0, Pi.single c 1) : (Fin r → k) × (Fin t → k)) ≠ 0`. Introduce `h`. Use `congrFun (congrArg Prod.snd h) c` as an intermediate fact. Simplify using `at this`.

Conclude with `(nonzero_span_atom _ hne).le_iff.1 hle`. Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨v, w⟩ -`. Establish `hdec : ((v, w) : (Fin r → k) × (Fin t → k)) = LinearMap.inl k (Fin r → k) (Fin t → k) v + ∑ c : Fin t, w c • ((0, Pi.single c 1) : (Fin r → k) × (Fin t → k))`. Use `Prod.ext ?_ (funext fun c' => ?_)` and prove the remaining obligations.

Simplify using `[Prod.fst_sum]`. Simplify using `[Prod.snd_sum, Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hdec]`. Use `Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_)` and prove the remaining obligations. Conclude with `Submodule.mem_sSup.2 fun N hN => hN _ (Or.inl rfl) ⟨v, rfl⟩`.

Conclude with `Submodule.mem_sSup.2 fun N hN => hN _ (Or.inr ⟨c, rfl⟩) (Submodule.mem_span_singleton_self _)`.
-/
theorem isSS_blockSum_of_isIrred {k Γ : Type} [Field k] [Group Γ] {r t : ℕ}
    (ρ : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → (Γ →* kˣ))
    (hρ : GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsIrred (matRep ρ)) : IsSS (GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum ρ χ) := by
  classical
  refine isSS_of_sSup_irreducible_eq_top _
    ({LinearMap.range (LinearMap.inl k (Fin r → k) (Fin t → k))} ∪
      Set.range fun c : Fin t =>
        Submodule.span k {((0, Pi.single c 1) : (Fin r → k) × (Fin t → k))}) ?_ ?_
  · rintro U (rfl | ⟨c, rfl⟩)
    · have key : ∀ g (v : Fin r → k), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum ρ χ g
          (LinearMap.inl k (Fin r → k) (Fin t → k) v) =
          LinearMap.inl k (Fin r → k) (Fin t → k) (matRep ρ g v) := by
        intro g v
        rw [GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum_apply]
        refine Prod.ext rfl (funext fun c => ?_)
        simp
      refine ⟨?_, fun U' hle hU' => ?_⟩
      · rintro g _ ⟨v, rfl⟩
        exact ⟨_, (key g v).symm⟩
      · have hst : Stable (matRep ρ) (U'.comap (LinearMap.inl k (Fin r → k) (Fin t → k))) := by
          intro g v hv
          rw [Submodule.mem_comap, ← key]
          exact hU' g _ hv
        have hmap := Submodule.map_comap_eq_self hle
        rcases hρ.2 _ hst with h | h
        · left
          rw [← hmap, h, Submodule.map_bot]
        · right
          rw [← hmap, h, Submodule.map_top]
    · refine ⟨?_, fun U' hle _ => ?_⟩
      · intro g v hv
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
        refine Submodule.mem_span_singleton.2 ⟨a * ((χ c g : kˣ) : k), ?_⟩
        rw [GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum_apply]
        refine Prod.ext ?_ (funext fun c' => ?_)
        · simp
        · by_cases h : c' = c
          · subst h
            simp [mul_comm]
          · simp [h]
      · have hne : ((0, Pi.single c 1) : (Fin r → k) × (Fin t → k)) ≠ 0 := by
          intro h
          have := congrFun (congrArg Prod.snd h) c
          simp at this
        exact (nonzero_span_atom _ hne).le_iff.1 hle
  · rw [eq_top_iff]
    rintro ⟨v, w⟩ -
    have hdec : ((v, w) : (Fin r → k) × (Fin t → k)) =
        LinearMap.inl k (Fin r → k) (Fin t → k) v +
          ∑ c : Fin t, w c • ((0, Pi.single c 1) : (Fin r → k) × (Fin t → k)) := by
      refine Prod.ext ?_ (funext fun c' => ?_)
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [hdec]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_)
    · exact Submodule.mem_sSup.2 fun N hN => hN _ (Or.inl rfl) ⟨v, rfl⟩
    · exact Submodule.mem_sSup.2 fun N hN =>
        hN _ (Or.inr ⟨c, rfl⟩) (Submodule.mem_span_singleton_self _)

end GlobalTheory
