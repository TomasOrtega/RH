import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace GlobalTheory.RecT

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative.
-/
theorem GoodCusp.tw {y : IrrGL k} (hy : GoodCusp y) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    GoodCusp (y.tw χ hχ) := by
  rcases hy with h1 | ⟨hf, y₀, χ₀, hχ₀, hfix, rfl⟩
  · exact Or.inl h1
  · exact Or.inr ⟨hf, y₀, χ₀ * χ, hχ₀.mul hχ, hfix, IrrGL.tw_tw _ _ _ _ _⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem Good.tw {x : IrrGL k} (hx : Good x) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Good (x.tw χ hχ) := by
  obtain ⟨s, hs, hg⟩ := hx
  refine ⟨s.map (·.tw χ hχ), (hs.tw χ hχ).of_equiv (x.twEquiv χ hχ), ?_⟩
  intro y hy
  obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
  exact (hg y' hy').tw χ hχ

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem Toral.tw {x : IrrGL k} (hx : Toral x) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Toral (x.tw χ hχ) := by
  obtain ⟨s, hs, hg⟩ := hx
  refine ⟨s.map (·.tw χ hχ), (hs.tw χ hχ).of_equiv (x.twEquiv χ hχ), ?_⟩
  intro y hy
  obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
  exact hg y' hy'

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem good_tw_iff (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Good (x.tw χ hχ) ↔ Good x :=
  ⟨fun h => by simpa only [IrrGL.tw_tw_inv] using h.tw χ⁻¹ hχ.inv, fun h => h.tw χ hχ⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem good_nu_iff (x : IrrGL k) (s : ℂ) : Good (x.nu s) ↔ Good x := good_tw_iff x _ _

end GlobalTheory.RecT

end
