import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResInjective
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open UpperTheory.Gal.Int.Core
open scoped Pointwise

open GlobalTheory.RealGal.AttConj in

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ ι a sat r g c hc hsurj h`. Establish `hcs : ∀ s y, c s y = g (s ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y))` using `fun s y => DFunLike.congr_fun (hc s) y`. Establish `hfwd : ∀ x : K, ∃ y : K, algebraMap K Ω y = g (algebraMap K Ω x)` using `fun x => by`. Apply `exists_of_fixed` to reduce the goal to its premises. Introduce `t`.

Take `⟨s, rfl⟩` from `hsurj t`. Rewrite using `[hcs, inv_apply_apply, s.commutes]`. Establish `hbwd : ∀ x : K, ∃ y : K, algebraMap K Ω y = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x)` using `fun x => by`. Apply `exists_of_fixed` to reduce the goal to its premises. Introduce `t`.

Establish `h1` using `hcs t (algebraMap K Ω x)`. Rewrite `h1` using `[(c t).commutes]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨γ, hγ⟩` from `exists_ringEquiv g hfwd hbwd`. Establish `hγinv : ∀ x : K, algebraMap K Ω (γ.symm x) = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x)` using `fun x => by`.

Establish `h1` using `hγ (γ.symm x)`. Rewrite `h1` using `[RingEquiv.apply_symm_apply]`. Rewrite using `[h1, inv_apply_apply]`. Establish `hγF : ∀ x : F, γ.symm (algebraMap F K x) = algebraMap F K x` using `fun x => by`. Apply `(algebraMap K Ω).injective` to reduce the goal to its premises.

Rewrite using `[hγinv, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]`. Use `set e : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv γ with he`. Establish `heγ : ∀ y : 𝓞 K, ((e.symm y : 𝓞 K) : K) = γ.symm (y : K)` using `fun y => rfl`. Set `P : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K)` to `fun w => w.comap (e.symm : 𝓞 K →+* 𝓞 K) e.symm.surjective`. Establish `hPmem : ∀ w y, y ∈ (P w).asIdeal ↔ e.symm y ∈ w.asIdeal` using `fun _ _ => Iff.rfl`.

Establish `hPinj : Function.Injective P`. Introduce `w1 w2 h12`. Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Establish `h3` using `congrArg (fun w : HeightOneSpectrum (𝓞 K) => e x ∈ w.asIdeal) h12`. Simplify using `only [hPmem, RingEquiv.symm_apply_apply] at h3`.

Conclude with `Iff.of_eq h3`. Establish `hPunder : ∀ w, (P w).under (𝓞 F) = w.under (𝓞 F)`. Introduce `w`. Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Use `show algebraMap (𝓞 F) (𝓞 K) x ∈ (P w).asIdeal ↔ algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal`.

Rewrite using `[hPmem]`. Establish `h4 : e.symm (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x` using `RingOfIntegers.ext (by rw [heγ]; exact hγF x)`. Rewrite using `[h4]`. Establish `hPnorm : ∀ w, normV (P w) = normV w`. Introduce `w`.

Unfold `normV`. Use `Nat.card_congr (Ideal.quotientEquiv (P w).asIdeal w.asIdeal e.symm ?_).toEquiv` and prove the remaining obligations. Conclude with `(Ideal.map_comap_of_surjective _ e.symm.surjective w.asIdeal).symm`. Establish `hPplace : ∀ w (A : ValuationSubring Ω), IsPlaceOver A w → IsPlaceOver (g • A) (P w)`. Introduce `w A hA y`.

Rewrite using `[val_lt_one_smul, hPmem, ← hA (e.symm y), heγ, hγinv]`. Unfold `AttOne at h ⊢`. Use `filter_upwards [hPinj.tendsto_cofinite.eventually h] with w hw hp`. Take `⟨B, hB, hE⟩` from `hw (by rw [hPnorm]; exact hp)`. Rewrite `hB` using `[hPunder]`.

Rewrite `hE` using `[hPnorm]`. Use `⟨B, hB, fun A hA => ?_⟩` and prove the remaining obligations. Take `⟨hI, hF⟩` from `hE (g • A) (hPplace w A hA)`. Use `⟨fun s hs => hI (c s) (ine_conj g c hc A s hs), fun σ hσ => ?_⟩` and prove the remaining obligations. Establish `h5` using `hF (c σ) (by rw [hPnorm]; exact frob_conj g c hc A _ σ hσ)`.

Rewrite using `[MonoidHom.comp_apply, map_inv]`. Conclude with `h5`.
-/
theorem UpperTheory.Gal.Int.Core.oneConj_holds :
    OneConj := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ ι a sat r g c hc hsurj h
  have hcs : ∀ s y, c s y = g (s ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y)) := fun s y => DFunLike.congr_fun (hc s) y
  have hfwd : ∀ x : K, ∃ y : K, algebraMap K Ω y = g (algebraMap K Ω x) := fun x => by
    apply exists_of_fixed
    intro t
    obtain ⟨s, rfl⟩ := hsurj t
    rw [hcs, inv_apply_apply, s.commutes]
  have hbwd : ∀ x : K, ∃ y : K, algebraMap K Ω y = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x) := fun x => by
    apply exists_of_fixed
    intro t
    have h1 := hcs t (algebraMap K Ω x)
    rw [(c t).commutes] at h1
    calc t ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x))
        = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (g (t ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x)))) := (inv_apply_apply _ _).symm
      _ = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x) := by rw [← h1]
  obtain ⟨γ, hγ⟩ := exists_ringEquiv g hfwd hbwd
  have hγinv : ∀ x : K, algebraMap K Ω (γ.symm x) = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x) := fun x => by
    have h1 := hγ (γ.symm x)
    rw [RingEquiv.apply_symm_apply] at h1
    rw [h1, inv_apply_apply]
  have hγF : ∀ x : F, γ.symm (algebraMap F K x) = algebraMap F K x := fun x => by
    apply (algebraMap K Ω).injective
    rw [hγinv, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  set e : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv γ with he
  have heγ : ∀ y : 𝓞 K, ((e.symm y : 𝓞 K) : K) = γ.symm (y : K) := fun y => rfl
  let P : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K) :=
    fun w => w.comap (e.symm : 𝓞 K →+* 𝓞 K) e.symm.surjective
  have hPmem : ∀ w y, y ∈ (P w).asIdeal ↔ e.symm y ∈ w.asIdeal := fun _ _ => Iff.rfl
  have hPinj : Function.Injective P := by
    intro w1 w2 h12
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    have h3 := congrArg (fun w : HeightOneSpectrum (𝓞 K) => e x ∈ w.asIdeal) h12
    simp only [hPmem, RingEquiv.symm_apply_apply] at h3
    exact Iff.of_eq h3
  have hPunder : ∀ w, (P w).under (𝓞 F) = w.under (𝓞 F) := by
    intro w
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    show algebraMap (𝓞 F) (𝓞 K) x ∈ (P w).asIdeal ↔ algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal
    rw [hPmem]
    have h4 : e.symm (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x :=
      RingOfIntegers.ext (by rw [heγ]; exact hγF x)
    rw [h4]
  have hPnorm : ∀ w, normV (P w) = normV w := by
    intro w
    unfold normV
    refine Nat.card_congr (Ideal.quotientEquiv (P w).asIdeal w.asIdeal e.symm ?_).toEquiv
    exact (Ideal.map_comap_of_surjective _ e.symm.surjective w.asIdeal).symm
  have hPplace : ∀ w (A : ValuationSubring Ω), IsPlaceOver A w → IsPlaceOver (g • A) (P w) := by
    intro w A hA y
    rw [val_lt_one_smul, hPmem, ← hA (e.symm y), heγ, hγinv]
  unfold AttOne at h ⊢
  filter_upwards [hPinj.tendsto_cofinite.eventually h] with w hw hp
  obtain ⟨B, hB, hE⟩ := hw (by rw [hPnorm]; exact hp)
  rw [hPunder] at hB
  rw [hPnorm] at hE
  refine ⟨B, hB, fun A hA => ?_⟩
  obtain ⟨hI, hF⟩ := hE (g • A) (hPplace w A hA)
  refine ⟨fun s hs => hI (c s) (ine_conj g c hc A s hs), fun σ hσ => ?_⟩
  have h5 := hF (c σ) (by rw [hPnorm]; exact frob_conj g c hc A _ σ hσ)
  rw [MonoidHom.comp_apply, map_inv]
  exact h5
