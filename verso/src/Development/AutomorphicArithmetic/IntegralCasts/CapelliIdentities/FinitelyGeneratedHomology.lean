import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsCompactUnitaryPointsAtPlaceFstMemCompact

/- English proof (translation)
Introduce `A K _ _ _ E _ _ c p R N Ω _ _ _ _ D σ`. Establish `hZ : (LinearMap.range D.h.toIntLinearMap).FG` using `Submodule.fg_range _`. Establish `hA : (Submodule.span A (Set.range D.h)).FG`. Take `⟨S, hS⟩` from `hZ`. Use `⟨S, ?_⟩` and prove the remaining obligations.

Establish `h1 : Set.range D.h = (Submodule.span ℤ (S : Set Ω) : Set Ω)`. Rewrite using `[hS]`. Both sides reduce to the same expression. Rewrite using `[h1, Submodule.span_span_of_tower]`. Conclude with `(hA.sup (D.om_lat.fg.map _)).map _`.
-/
theorem UpperTheory.Reformulated.B.FinitelyGeneratedHomology.omHT_fg :
    ∀ {A K : Type} [inst : CommRing A] [inst_1 : Field K] [inst_2 : Algebra A K] {E : Type} [inst_3 : Field E]
      [inst_4 : NumberField E] {c : E ≃+* E} {p R N : ℕ} {Ω : Type} [inst_5 : AddCommGroup Ω] [inst_6 : _root_.Module K Ω]
      [inst_7 : _root_.Module A Ω] [inst_8 : IsScalarTower A K Ω] (D : GlobalTheory.CompanionTheory.Ar.HT.HTChart A K c p R N Ω) (σ : E →+* K),
      (D.omHT σ).FG := by
  intro A K _ _ _ E _ _ c p R N Ω _ _ _ _ D σ
  have hZ : (LinearMap.range D.h.toIntLinearMap).FG := Submodule.fg_range _
  have hA : (Submodule.span A (Set.range D.h)).FG := by
    obtain ⟨S, hS⟩ := hZ
    refine ⟨S, ?_⟩
    have h1 : Set.range D.h = (Submodule.span ℤ (S : Set Ω) : Set Ω) := by
      rw [hS]; rfl
    rw [h1, Submodule.span_span_of_tower]
  exact (hA.sup (D.om_lat.fg.map _)).map _
