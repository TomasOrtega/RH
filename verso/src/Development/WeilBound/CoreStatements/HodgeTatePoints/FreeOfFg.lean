import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwoMulFinrank

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Gd

/- English proof (translation)
Use `haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj`. Use `haveI : ValuationRing O := ValuationRing.of_integers v hv`. Use `haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL`. Use `haveI : Module.Flat O L := by`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`.

Introduce `x hx`. Take `⟨a, ha⟩` from `(Submodule.mem_torsion_iff x).mp hx`. Establish `hx0 : (a : O) • (x : Ω) = 0`. Use `congrArg Subtype.val ha` as an intermediate fact. Simplify `this` using `[Submonoid.smul_def]`.

Rewrite `hx0` using `[← algebraMap_smul C (a : O) (x : Ω), smul_eq_zero]`. Break down `hx0 with h | h` into its components or cases. Conclude with `absurd (hv.hom_inj (h.trans (map_zero _).symm)) (nonZeroDivisors.coe_ne_zero a)`. Conclude with `(Submodule.mem_bot O).mpr (Subtype.ext (by simpa using h))`. Conclude with `Module.free_of_flat_of_isLocalRing`.
-/
theorem free_of_fg {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    (hv : v.Integers O) {Ω : Type} [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
    (L : Submodule O Ω) (hL : L.FG) : Module.Free O L := by
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL
  haveI : Module.Flat O L := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    have hx0 : (a : O) • (x : Ω) = 0 := by
      have := congrArg Subtype.val ha
      simpa [Submonoid.smul_def] using this
    rw [← algebraMap_smul C (a : O) (x : Ω), smul_eq_zero] at hx0
    rcases hx0 with h | h
    · exact absurd (hv.hom_inj (h.trans (map_zero _).symm)) (nonZeroDivisors.coe_ne_zero a)
    · exact (Submodule.mem_bot O).mpr (Subtype.ext (by simpa using h))
  exact Module.free_of_flat_of_isLocalRing

end PositivityTheory.HtPt.Gd
