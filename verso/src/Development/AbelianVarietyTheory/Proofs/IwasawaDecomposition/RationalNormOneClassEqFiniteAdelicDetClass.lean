import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.FullDt

/- English proof (translation)
Introduce `R H SQ z x hx`. Take `⟨k, hk⟩` from `exists_eq_div_conj H z`. Rewrite using `[← isUnitaryPointsMap_unitaryRationalPointsFiner H SQ k z hk]`. Use `symm`. Apply `normOneFiniteAdeleDetClass_of_isDetLift` to reduce the goal to its premises.

Unfold `IsDetLift`. Rewrite using `[hx]`. Establish `hf : finAf H.F H.E (Neutral.B1.diagUnits H.E k) = Units.map (Formalism.UG.inclE (F` using `H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k := by`. Apply `Units.ext` to reduce the goal to its premises. Apply `(afIso H.F H.E).injective` to reduce the goal to its premises.

Rewrite using `[afIso_finAf]`. Use `show _ = afIso H.F H.E ((k : H.E) ⊗ₜ[H.F] 1)`. Rewrite using `[afIso_tmul_one]`. Both sides reduce to the same expression. Rewrite using `[hf]`.

Establish `key : Formalism.L2.Herm.unitaryOneRationalAdele H.F z * conjId (host_cmData R H).sig (Units.map (Formalism.UG.inclE (F` using `H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k) = Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k := by`. Apply `Units.ext` to reduce the goal to its premises. Use `show Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (z : H.E) * Formalism.UG.sigR (host_cmData R H).sig _ (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (k : H.E)) = Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (k : H.E)`. Rewrite using `[sigR_inclE, ← map_mul, bridge_star_holds R H, hk]`. Rewrite using `[h90, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_iff_eq_mul]`.

Conclude with `key.symm`.
-/
theorem e1Q_eq_u1Dt_of_det_eq : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (z : unitary H.E) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), Matrix.GeneralLinearGroup.det x.1 = Formalism.L2.Herm.unitaryOneRationalAdele H.F z → e1Q H SQ z = u1Dt H SQ x := by
  intro R H SQ z x hx
  obtain ⟨k, hk⟩ := exists_eq_div_conj H z
  rw [← isUnitaryPointsMap_unitaryRationalPointsFiner H SQ k z hk]
  symm
  apply normOneFiniteAdeleDetClass_of_isDetLift
  unfold IsDetLift
  rw [hx]
  have hf : finAf H.F H.E (Neutral.B1.diagUnits H.E k) = Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k := by
    apply Units.ext
    apply (afIso H.F H.E).injective
    rw [afIso_finAf]
    show _ = afIso H.F H.E ((k : H.E) ⊗ₜ[H.F] 1)
    rw [afIso_tmul_one]
    rfl
  rw [hf]
  have key : Formalism.L2.Herm.unitaryOneRationalAdele H.F z * conjId (host_cmData R H).sig
      (Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k) =
      Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k := by
    apply Units.ext
    show Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (z : H.E) *
      Formalism.UG.sigR (host_cmData R H).sig _ (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (k : H.E)) =
      Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (k : H.E)
    rw [sigR_inclE, ← map_mul, bridge_star_holds R H, hk]
  rw [h90, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_iff_eq_mul]
  exact key.symm

end GlobalTheory.Mem.Col2.FullDt
