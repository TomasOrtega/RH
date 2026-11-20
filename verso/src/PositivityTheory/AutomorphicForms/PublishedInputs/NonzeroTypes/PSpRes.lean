import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroBasicTwistOfSpecialForm

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spRes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hu : valuation k ((unitIncl k u : kˣ) : k) = 1` using `valuation_eq_one_iff.mpr ⟨u, rfl⟩`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[val_absPow, nabs_eq_one (k := k) hu]`. Simplify using the standard rewrite rules.
-/
theorem absPow_unitIncl (z : ℂ) (u : 𝒪[k]ˣ) : absPow k z (unitIncl k u) = 1 := by
  have hu : valuation k ((unitIncl k u : kˣ) : k) = 1 := valuation_eq_one_iff.mpr ⟨u, rfl⟩
  apply Units.ext
  rw [val_absPow, nabs_eq_one (k := k) hu]
  simp

end P_spRes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} (G : Grp k n)

open P_spRes in

/- English proof (translation)
Introduce `ν hν i`. Use `MonoidHom.ext fun u => ?_` and prove the remaining obligations. Establish `h1` using `DFunLike.congr_fun (hν (G.e.symm i).1 (G.e.symm i).2) u`. Simplify using `only [res, MonoidHom.comp_apply] at h1`. Simplify using `only [res, cOf, chi, bl, MonoidHom.comp_apply, MonoidHom.mul_apply, absPow_unitIncl, mul_one]`.

Conclude with `h1`.
-/
theorem step_spRes : G.SpecialRestrictionProp := by
  intro ν hν i
  refine MonoidHom.ext fun u => ?_
  have h1 := DFunLike.congr_fun (hν (G.e.symm i).1 (G.e.symm i).2) u
  simp only [res, MonoidHom.comp_apply] at h1
  simp only [res, cOf, chi, bl, MonoidHom.comp_apply, MonoidHom.mul_apply, absPow_unitIncl, mul_one]
  exact h1

end UpperTheory.TNZ.Grp
