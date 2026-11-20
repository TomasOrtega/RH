import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
import Development.EtaleCohomology.WeilConjectures.AbsContPf
import Development.EtaleCohomology.WeilConjectures.ChevPf

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

/- English proof (translation)
Introduce `hst l _ k Ω _ _ _ _ X p hqc hqs n i hfin v μ`. Establish `habs` using `LateralTheory.EWeil.AbsContPf.AbsCont_of LateralTheory.EWeil.ChevPf.Chev_of`. Establish `key : ∀ (φ : Hl l (sch.obj (geom Ω p)) n i →ₗ[ℤ_[l]] ℚ_[l]) (x : Hl l (sch.obj (geom Ω p)) n i), Continuous fun σ : Gal(Ω/k) => φ (galHl l Ω p n i σ x)`. Introduce `φ x`. Use `habs l Gal(Ω/k) (Hl l (sch.obj (geom Ω p)) n i) (galHl l Ω p n i) (fun m => LinearMap.ker (LateralTheory.EWeil.ContinCut.evk l (sch.obj (geom Ω p)) n i m)) (LateralTheory.EWeil.ContinCut.evk_anti l _ n i) ?_ ?_ φ x` and prove the remaining obligations.

Introduce `y hy`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `m`. Simplify `hy m` using `[LateralTheory.EWeil.ContinCut.evk]`. Introduce `y m`.

Establish `hset : {σ : Gal(Ω/k) | (galHl l Ω p n i σ) y - y ∈ LinearMap.ker (LateralTheory.EWeil.ContinCut.evk l (sch.obj (geom Ω p)) n i m)} = {σ | (galHl l Ω p n i σ y).1 m = y.1 m}`. Use extensionality with `σ`. Simplify using `[LateralTheory.EWeil.ContinCut.evk, sub_eq_zero]`. Rewrite using `[hset]`. Conclude with `hst l k Ω p hqc hqs n i y m`.

Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simpa using continuous_const`. Consider the case `tmul q x`. Establish `hφ` using `key ((μ.restrictScalars ℤ_[l]) ∘ₗ (TensorProduct.mk ℤ_[l] ℚ_[l] _ 1)) x`. Use `(Continuous.mul (continuous_const : Continuous fun _ : Gal(Ω/k) => q) hφ).congr ?_` and prove the remaining obligations.

Introduce `σ`. Establish `e : galHQ l Ω p n i σ (q ⊗ₜ x) = q • ((1 : ℚ_[l]) ⊗ₜ (galHl l Ω p n i σ x))`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Simplify using `[GlobalTheory.EtC.galHQ]`. Rewrite using `[e, map_smul, smul_eq_mul]`.

Both sides reduce to the same expression. Consider the case `add a b ha hb`. Conclude with `(ha.add hb).congr fun σ => by simp only [map_add, Pi.add_apply]`.
-/
theorem UpperTheory.Gal.Int.Geo.degCont_of :
    StabOpen → DegCont := by
  intro hst l _ k Ω _ _ _ _ X p hqc hqs n i hfin v μ
  have habs := LateralTheory.EWeil.AbsContPf.AbsCont_of LateralTheory.EWeil.ChevPf.Chev_of
  have key : ∀ (φ : Hl l (sch.obj (geom Ω p)) n i →ₗ[ℤ_[l]] ℚ_[l]) (x : Hl l (sch.obj (geom Ω p)) n i),
      Continuous fun σ : Gal(Ω/k) => φ (galHl l Ω p n i σ x) := by
    intro φ x
    refine habs l Gal(Ω/k) (Hl l (sch.obj (geom Ω p)) n i) (galHl l Ω p n i)
      (fun m => LinearMap.ker (LateralTheory.EWeil.ContinCut.evk l (sch.obj (geom Ω p)) n i m))
      (LateralTheory.EWeil.ContinCut.evk_anti l _ n i) ?_ ?_ φ x
    · intro y hy
      apply Subtype.ext
      funext m
      simpa [LateralTheory.EWeil.ContinCut.evk] using hy m
    · intro y m
      have hset : {σ : Gal(Ω/k) | (galHl l Ω p n i σ) y - y ∈
          LinearMap.ker (LateralTheory.EWeil.ContinCut.evk l (sch.obj (geom Ω p)) n i m)} =
          {σ | (galHl l Ω p n i σ y).1 m = y.1 m} := by
        ext σ
        simp [LateralTheory.EWeil.ContinCut.evk, sub_eq_zero]
      rw [hset]
      exact hst l k Ω p hqc hqs n i y m
  induction v using TensorProduct.induction_on with
  | zero => simpa using continuous_const
  | tmul q x =>
    have hφ := key ((μ.restrictScalars ℤ_[l]) ∘ₗ (TensorProduct.mk ℤ_[l] ℚ_[l] _ 1)) x
    refine (Continuous.mul (continuous_const : Continuous fun _ : Gal(Ω/k) => q) hφ).congr ?_
    intro σ
    have e : galHQ l Ω p n i σ (q ⊗ₜ x) = q • ((1 : ℚ_[l]) ⊗ₜ (galHl l Ω p n i σ x)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [GlobalTheory.EtC.galHQ]
    rw [e, map_smul, smul_eq_mul]
    rfl
  | add a b ha hb =>
    exact (ha.add hb).congr fun σ => by simp only [map_add, Pi.add_apply]
