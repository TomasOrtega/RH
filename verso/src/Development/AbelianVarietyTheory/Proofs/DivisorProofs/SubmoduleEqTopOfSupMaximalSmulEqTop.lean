import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ N _ _ _ M h`. Establish `hQ : ∀ m : Ideal R, m.IsMaximal → (⊤ : Submodule R (N ⧸ M)) ≤ m • ⊤`. Introduce `m hm`. Establish `h1` using `congrArg (Submodule.map M.mkQ) (h m hm)`. Rewrite `h1` using `[Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]`.

Establish `h2 : Submodule.map M.mkQ M = ⊥` using `Submodule.mkQ_map_self M`. Rewrite `h1` using `[h2, bot_sup_eq]`. Rewrite using `[h1]`. Establish `hfg : (⊤ : Submodule R (N ⧸ M)).FG` using `Module.Finite.fg_top`. Establish `hann : Module.annihilator R (N ⧸ M) = ⊤`.

Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`. Take `⟨r, hr1, hr⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤ hfg (hQ m hm)`. Establish `hrm : r ∈ m` using `hle (Module.mem_annihilator.mpr fun q => hr q Submodule.mem_top)`. Establish `: (1 : R) ∈ m`.

Use `m.sub_mem hrm hr1` as an intermediate fact. Simplify using `using this`. Conclude with `hm.ne_top ((Ideal.eq_top_iff_one m).mpr this)`. Rewrite using `[eq_top_iff]`. Introduce `n _`.

Establish `h1 : (1 : R) ∈ Module.annihilator R (N ⧸ M)` using `hann ▸ Submodule.mem_top`. Establish `h0 : (Submodule.Quotient.mk n : N ⧸ M) = 0`. Simplify using `using Module.mem_annihilator.mp h1 (Submodule.Quotient.mk n)`. Conclude with `(Submodule.Quotient.mk_eq_zero M).mp h0`.
-/
theorem submodule_eq_top_of_sup_maximal_smul_eq_top :
    ∀ (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N]
      (M : Submodule R N), (∀ m : Ideal R, m.IsMaximal → M ⊔ m • ⊤ = ⊤) → M = ⊤ := by
  intro R _ N _ _ _ M h

  have hQ : ∀ m : Ideal R, m.IsMaximal → (⊤ : Submodule R (N ⧸ M)) ≤ m • ⊤ := by
    intro m hm
    have h1 := congrArg (Submodule.map M.mkQ) (h m hm)
    rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h1
    have h2 : Submodule.map M.mkQ M = ⊥ := Submodule.mkQ_map_self M
    rw [h2, bot_sup_eq] at h1
    rw [h1]
  have hfg : (⊤ : Submodule R (N ⧸ M)).FG := Module.Finite.fg_top
  have hann : Module.annihilator R (N ⧸ M) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤ hfg (hQ m hm)
    have hrm : r ∈ m := hle (Module.mem_annihilator.mpr fun q => hr q Submodule.mem_top)
    have : (1 : R) ∈ m := by
      have := m.sub_mem hrm hr1
      simpa using this
    exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr this)
  rw [eq_top_iff]
  intro n _
  have h1 : (1 : R) ∈ Module.annihilator R (N ⧸ M) := hann ▸ Submodule.mem_top
  have h0 : (Submodule.Quotient.mk n : N ⧸ M) = 0 := by
    simpa using Module.mem_annihilator.mp h1 (Submodule.Quotient.mk n)
  exact (Submodule.Quotient.mk_eq_zero M).mp h0

end GlobalTheory
