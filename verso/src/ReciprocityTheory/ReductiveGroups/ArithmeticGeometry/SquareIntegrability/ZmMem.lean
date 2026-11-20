import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZeroModePointwiseBound

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zm_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    ZM.zmB hI s ∈ (Col.YB hI hP 1).Sec 1 :=
  zeroMode_mem_sections hI hP hs

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zm_pt {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) (w : Vsp X.dim) (T M : ℝ)
    (hT : ∀ F : Finset (Vsp X.dim), (∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) →
      ∑ y ∈ F, Real.exp (-Real.pi * ‖uMap I w - y‖ ^ 2) ≤ T)
    (hM : ∀ t, (Col.YB hI hP 1).ptN2 1 (ZM.zmB hI s) t ≤ M) :
    Real.sqrt (X.ptN2 1 s fun _ => w) ≤ Real.sqrt M * T :=
  zeroMode_pointwise_bound hI hP hs w T M hT hM

end ReciprocityTheory.ChartRestriction.G.I2
