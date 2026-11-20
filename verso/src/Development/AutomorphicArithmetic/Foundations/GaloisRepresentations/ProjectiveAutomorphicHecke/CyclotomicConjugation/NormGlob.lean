import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConjAlt

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂

private noncomputable abbrev sn (K : Type) [Field K] [NumberField K] : GroundTheory.Global.IdeleGroup K →* (Af K)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

private noncomputable abbrev fi (K : Type) [Field K] [NumberField K] : (Af K)ˣ →* GroundTheory.Global.IdeleGroup K :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `v`. Conclude with `(GroundTheory.Global.ideleNorm_snd x v).trans (GroundTheory.Global.ideleNorm_snd (fi L (sn L x)) v).symm`.
-/
private theorem sn_norm (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (x : GroundTheory.Global.IdeleGroup L) :
    sn K (GroundTheory.Global.ideleNorm K L x) = fN K L (sn L x) := by
  apply Units.ext
  apply RestrictedProduct.ext
  intro v
  exact (GroundTheory.Global.ideleNorm_snd x v).trans (GroundTheory.Global.ideleNorm_snd (fi L (sn L x)) v).symm

/- English proof (translation)
The claim follows from `Continuous.units_map _ continuous_snd`.
-/
private theorem continuous_sn (K : Type) [Field K] [NumberField K] : Continuous (sn K) :=
  Continuous.units_map _ continuous_snd

/- English proof (translation)
The claim follows from `Continuous.units_map _ (continuous_const.prodMk continuous_id)`.
-/
private theorem continuous_fi (K : Type) [Field K] [NumberField K] : Continuous (fi K) :=
  Continuous.units_map _ (continuous_const.prodMk continuous_id)

/- English proof (translation)
Introduce `K L _ _ _ _ _`. Use `⟨(continuous_sn K).comp (GroundTheory.Global.continuous_ideleNorm.comp (continuous_fi L)), fun k => ?_, ?_⟩` and prove the remaining obligations. Establish `h : diagF L k = sn L (GroundTheory.Global.IdeleGroup.diagonal L k)`. Apply `Units.ext` to reduce the goal to its premises. Both sides reduce to the same expression.

Rewrite using `[h, ← sn_norm, GroundTheory.Global.ideleNorm_diagonal]`. Both sides reduce to the same expression. Introduce `M _ _ _ _ _ y`. Establish `h` using `sn_norm K L (GroundTheory.Global.ideleNorm L M (fi M y))`. Rewrite `h` using `[GroundTheory.Global.ideleNorm_ideleNorm]`.

Conclude with `h.symm`.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.normGlob :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.NormGlob := by
  intro K L _ _ _ _ _
  refine ⟨(continuous_sn K).comp (GroundTheory.Global.continuous_ideleNorm.comp (continuous_fi L)), fun k => ?_, ?_⟩
  · have h : diagF L k = sn L (GroundTheory.Global.IdeleGroup.diagonal L k) := by
      apply Units.ext
      rfl
    rw [h, ← sn_norm, GroundTheory.Global.ideleNorm_diagonal]
    rfl
  · intro M _ _ _ _ _ y
    have h := sn_norm K L (GroundTheory.Global.ideleNorm L M (fi M y))
    rw [GroundTheory.Global.ideleNorm_ideleNorm] at h
    exact h.symm
