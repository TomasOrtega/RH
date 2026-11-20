import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolume
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeMassEqFinprodLocal
open NumberField GlobalTheory.HL
open scoped Pointwise Classical

namespace GlobalTheory.HL.CommInt

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig A r k G hk Λ hΛ`. Take `⟨-, hlat, -⟩` from `GlobalTheory.T.numberField_lattice_determined_by_local_lattices A (k + 2 * r + 1) Λ hΛ`. Take `⟨hfin, -⟩` from `GlobalTheory.HL.MassProduct.mass_eq_finprod A r k G hk Λ hΛ`. Set `U : ∀ p, Subgroup (G.S p).GLV` to `fun p => (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ)`. Set `K : ∀ p, Subgroup (G.S p).GLV` to `fun p => (G.S p).K0`.

Establish `hidx : ∀ p, (K p).relIndex (U p) ≠ 0 ∧ (U p).relIndex (K p) ≠ 0`. Introduce `p`. Use `haveI := (A.loc p).lf`. Use `haveI := (A.loc p).char0`. Take `⟨a, b, -⟩` from `(GlobalTheory.HL.volSt (A.L p) r k (G.S p)).1 (A.lat p Λ) (hlat p)`.

Conclude with `⟨a, b⟩`. Establish `hKU : {p | K p ≠ U p}.Finite` using `hfin.subset fun p hp h => hp h.symm`. Take `⟨h1, h2, -⟩` from `GlobalTheory.T.haarInvVolumeRelIndex_pi_univ_eq_finprod K U hKU hidx`. Set `φ` to `GlobalTheory.HL.MassProduct.extHom A (k + 2 * r + 1)`. Establish `e1 : G.K0 = (Subgroup.pi Set.univ K).comap φ` using `(GlobalTheory.HL.MassProduct.comap_pi A _ K).symm`.

Establish `e2 : G.stabL Λ = (Subgroup.pi Set.univ U).comap φ` using `(GlobalTheory.HL.MassProduct.comap_pi A _ U).symm`. Rewrite using `[e1, e2, Subgroup.relIndex_comap, Subgroup.relIndex_comap]`. Conclude with `⟨fun h0 => h2 (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0), fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0)⟩`.
-/
theorem stabL_relIndex_K0_ne_zero_of_four_mul_add_seven_le : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ Λ : G.Lt, Submodule.IsLattice E Λ → (G.stabL Λ).relIndex G.K0 ≠ 0 ∧ G.K0.relIndex (G.stabL Λ) ≠ 0 := by
  intro F E _ _ _ _ _ sig A r k G hk Λ hΛ
  obtain ⟨-, hlat, -⟩ := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A (k + 2 * r + 1) Λ hΛ
  obtain ⟨hfin, -⟩ := GlobalTheory.HL.MassProduct.mass_eq_finprod A r k G hk Λ hΛ
  let U : ∀ p, Subgroup (G.S p).GLV :=
    fun p => (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ)
  let K : ∀ p, Subgroup (G.S p).GLV := fun p => (G.S p).K0
  have hidx : ∀ p, (K p).relIndex (U p) ≠ 0 ∧ (U p).relIndex (K p) ≠ 0 := by
    intro p
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    obtain ⟨a, b, -⟩ := (GlobalTheory.HL.volSt (A.L p) r k (G.S p)).1 (A.lat p Λ) (hlat p)
    exact ⟨a, b⟩
  have hKU : {p | K p ≠ U p}.Finite := hfin.subset fun p hp h => hp h.symm
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.haarInvVolumeRelIndex_pi_univ_eq_finprod K U hKU hidx
  let φ := GlobalTheory.HL.MassProduct.extHom A (k + 2 * r + 1)
  have e1 : G.K0 = (Subgroup.pi Set.univ K).comap φ := (GlobalTheory.HL.MassProduct.comap_pi A _ K).symm
  have e2 : G.stabL Λ = (Subgroup.pi Set.univ U).comap φ := (GlobalTheory.HL.MassProduct.comap_pi A _ U).symm
  rw [e1, e2, Subgroup.relIndex_comap, Subgroup.relIndex_comap]
  exact ⟨fun h0 => h2 (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0),
    fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0)⟩

end GlobalTheory.HL.CommInt
