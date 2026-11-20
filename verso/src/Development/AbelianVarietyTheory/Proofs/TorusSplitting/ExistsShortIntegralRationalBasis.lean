import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

/- English proof (translation)
Introduce `hex E _ _ _`. Take `⟨n, ω, hωB, hsp⟩` from `hex E`. Establish `htop : Submodule.span ℚ (Set.range fun j => (ω j : E)) = ⊤`. Rewrite using `[eq_top_iff, ← (NumberField.integralBasis E).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Rewrite using `[NumberField.integralBasis_apply]`. Conclude with `hsp _`. Take `⟨b, hbS, hbspan, hbli⟩` from `exists_linearIndependent ℚ (Set.range fun j => (ω j : E))`. Establish `hbfin : b.Finite` using `hbli.setFinite`. Use `hbfin.fintype` as an intermediate fact.

Establish `hcard : Fintype.card b = Module.finrank ℚ E`. Establish `h` using `finrank_span_eq_card hbli`. Rewrite `h` using `[Subtype.range_coe, hbspan, htop, finrank_top]`. Rewrite using `[h]`. Set `e : Fin (Module.finrank ℚ E) ≃ b` to `(Fintype.equivFinOfCardEq hcard).symm`.

Establish `hmem : ∀ x : b, ∃ j, (ω j : E) = x` using `fun x => hbS x.2`. Use `choose idx hidx using hmem`. Use `⟨fun i => ω (idx (e i)), ?_, fun i τ => hωB _ τ⟩` and prove the remaining obligations. Establish `: (fun i => ((ω (idx (e i)) : 𝓞 E) : E)) = (fun x : b => (x : E)) ∘ e`. Use function extensionality and compare the values at `i`.

Simplify using `[hidx]`. Rewrite using `[this]`. Conclude with `(linearIndependent_equiv e).mpr hbli`.
-/
theorem exists_short_integral_rational_basis :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ (n : ℕ) (ω : Fin n → 𝓞 E),
      (∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ omStar (E := E)) ∧
      ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E))) →
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
      ∃ ω : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun j => (ω j : E)) ∧
        ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ omStar (E := E)) := by
  intro hex E _ _ _
  classical
  obtain ⟨n, ω, hωB, hsp⟩ := hex E
  have htop : Submodule.span ℚ (Set.range fun j => (ω j : E)) = ⊤ := by
    rw [eq_top_iff, ← (NumberField.integralBasis E).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [NumberField.integralBasis_apply]
    exact hsp _
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℚ (Set.range fun j => (ω j : E))
  have hbfin : b.Finite := hbli.setFinite
  have := hbfin.fintype
  have hcard : Fintype.card b = Module.finrank ℚ E := by
    have h := finrank_span_eq_card hbli
    rw [Subtype.range_coe, hbspan, htop, finrank_top] at h
    rw [h]
  let e : Fin (Module.finrank ℚ E) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ x : b, ∃ j, (ω j : E) = x := fun x => hbS x.2
  choose idx hidx using hmem
  refine ⟨fun i => ω (idx (e i)), ?_, fun i τ => hωB _ τ⟩
  have : (fun i => ((ω (idx (e i)) : 𝓞 E) : E)) = (fun x : b => (x : E)) ∘ e := by
    funext i; simp [hidx]
  rw [this]
  exact (linearIndependent_equiv e).mpr hbli

end GlobalTheory
