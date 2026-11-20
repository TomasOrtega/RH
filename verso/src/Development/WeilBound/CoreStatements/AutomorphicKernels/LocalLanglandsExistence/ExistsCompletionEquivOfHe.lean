import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.KernelCondGlob
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.WeilEquivOfLocalDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
import GroundTheory.GlobalFields.CompletionAtPlace.Degree

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions.RamifiedPlaceLift

/- English proof (translation)
Use `continuous_of_continuousAt_zero ι.symm.toAddMonoidHom ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero]`. Introduce `s hs`. Rewrite using `[Filter.mem_map]`. Take `⟨γ, hγ⟩` from `Valued.mem_nhds_zero.1 hs`.

Take `⟨x, hx⟩ : ∃ x : v.adicCompletion K, Valued.v.restrict x = γ.1` from `MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective _ γ.1`. Establish `hx0 : Valued.v x ≠ 0`. Introduce `h0`. Apply `γ.ne_zero` to reduce the goal to its premises. Rewrite using `[← hx]`.

Simplify using `using h0`. Establish `hy0 : Valued.v.restrict (ι x) ≠ 0`. Simplify `hx0` using `[hv]`. Use `Valued.mem_nhds_zero.2 ⟨Units.mk0 _ hy0, fun y hy => hγ ?_⟩` and prove the remaining obligations. Establish `h1 : Valued.v y < Valued.v (ι x)`.

Simplify using `using hy`. Establish `h2 : Valued.v (ι.symm y) < Valued.v x`. Rewrite using `[← hv (ι.symm y), ← hv x, RingEquiv.apply_symm_apply]`. Conclude with `h1`. Use `show Valued.v.restrict (ι.symm y) < γ`.

Rewrite using `[← hx]`. Simplify using `using h2`.
-/
theorem continuous_symm_of_valued_eq {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 F)}
    (ι : v.adicCompletion K ≃+* w.adicCompletion F) (hv : ∀ x, Valued.v (ι x) = Valued.v x) :
    Continuous ι.symm := by
  refine continuous_of_continuousAt_zero ι.symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  obtain ⟨x, hx⟩ : ∃ x : v.adicCompletion K, Valued.v.restrict x = γ.1 :=
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective _ γ.1
  have hx0 : Valued.v x ≠ 0 := by
    intro h0
    apply γ.ne_zero
    rw [← hx]
    simpa using h0
  have hy0 : Valued.v.restrict (ι x) ≠ 0 := by
    simpa [hv] using hx0
  refine Valued.mem_nhds_zero.2 ⟨Units.mk0 _ hy0, fun y hy => hγ ?_⟩
  have h1 : Valued.v y < Valued.v (ι x) := by
    simpa using hy
  have h2 : Valued.v (ι.symm y) < Valued.v x := by
    rw [← hv (ι.symm y), ← hv x, RingEquiv.apply_symm_apply]
    exact h1
  show Valued.v.restrict (ι.symm y) < γ
  rw [← hx]
  simpa using h2

section Pair

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
  {K F : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] [Algebra K F] [IsScalarTower K F Ω]
  {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 F)}

omit [IsAlgClosure F Ω] in

/- English proof (translation)
Establish `: w.asIdeal.LiesOver v.asIdeal` using `⟨(GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h').symm⟩`. Establish `hn` using `normV_eq_of_localDegreeOne h h' hloc`. Establish `hf : normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 K)`. Simplify using `only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]`. Conclude with `(Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm`.

Rewrite `hf` using `[hn]`. Conclude with `Nat.pow_right_injective (one_lt_normV v) (hf.symm.trans (pow_one _).symm)`.
-/
theorem inertiaDeg_eq_one (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    (hloc : ∀ (σ : Weil h) (x : F), (σ : G K Ω) (algebraMap F Ω x) = algebraMap F Ω x) :
    w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have : w.asIdeal.LiesOver v.asIdeal := ⟨(GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h').symm⟩
  have hn := normV_eq_of_localDegreeOne h h' hloc
  have hf : normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 K) := by
    simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm
  rw [hn] at hf
  exact Nat.pow_right_injective (one_lt_normV v) (hf.symm.trans (pow_one _).symm)

omit [IsAlgClosure F Ω] in

/- English proof (translation)
Establish `: w.asIdeal.LiesOver v.asIdeal` using `⟨(GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h').symm⟩`. Set `_ : Algebra (v.adicCompletion K) (w.adicCompletion F)` to `(GroundTheory.Global.adicCompletionMap v w).toAlgebra`. Establish `: IsScalarTower K (v.adicCompletion K) (w.adicCompletion F)` using `.of_algebraMap_eq fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply K F (w.adicCompletion F)]`. Conclude with `(GroundTheory.Global.adicCompletionMap_algebraMap v w x).symm`.

Establish `: ContinuousSMul (v.adicCompletion K) (w.adicCompletion F)` using `continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v w)`. Establish `hfin : Module.finrank (v.adicCompletion K) (w.adicCompletion F) = 1`. Rewrite using `[GroundTheory.Global.finrank_adicCompletion v w, he, inertiaDeg_eq_one h h' hloc]`. Establish `hbij : Function.Bijective (algebraMap (v.adicCompletion K) (w.adicCompletion F))`. Use `⟨(algebraMap (v.adicCompletion K) (w.adicCompletion F)).injective, fun y => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' (K := v.adicCompletion K) (1 : w.adicCompletion F) one_ne_zero).1 hfin y`. Conclude with `⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩`. Set `ι` to `RingEquiv.ofBijective (algebraMap (v.adicCompletion K) (w.adicCompletion F)) hbij`. Establish `hv : ∀ x, Valued.v (ι x) = Valued.v x` using `fun x => by`. Use `GroundTheory.Global.valued_algebraMap_adicCompletion v w x` as an intermediate fact.

Rewrite `this` using `[he, pow_one]`. Conclude with `this`. Conclude with `⟨ι, GroundTheory.Global.continuous_adicCompletionMap v w, continuous_symm_of_valued_eq ι hv, GroundTheory.Global.adicCompletionMap_algebraMap v w, hv⟩`.
-/
theorem exists_completionEquiv_of_he (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    (hloc : ∀ (σ : Weil h) (x : F), (σ : G K Ω) (algebraMap F Ω x) = algebraMap F Ω x)
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    ∃ ι : v.adicCompletion K ≃+* w.adicCompletion F, Continuous ι ∧ Continuous ι.symm ∧
      (∀ x : K, ι (algebraMap K _ x) = algebraMap F _ (algebraMap K F x)) ∧
      ∀ x, Valued.v (ι x) = Valued.v x := by
  have : w.asIdeal.LiesOver v.asIdeal := ⟨(GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h').symm⟩
  let _ : Algebra (v.adicCompletion K) (w.adicCompletion F) := (GroundTheory.Global.adicCompletionMap v w).toAlgebra
  have : IsScalarTower K (v.adicCompletion K) (w.adicCompletion F) :=
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply K F (w.adicCompletion F)]
      exact (GroundTheory.Global.adicCompletionMap_algebraMap v w x).symm
  have : ContinuousSMul (v.adicCompletion K) (w.adicCompletion F) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v w)
  have hfin : Module.finrank (v.adicCompletion K) (w.adicCompletion F) = 1 := by
    rw [GroundTheory.Global.finrank_adicCompletion v w, he, inertiaDeg_eq_one h h' hloc]
  have hbij : Function.Bijective (algebraMap (v.adicCompletion K) (w.adicCompletion F)) := by
    refine ⟨(algebraMap (v.adicCompletion K) (w.adicCompletion F)).injective, fun y => ?_⟩
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := v.adicCompletion K) (1 : w.adicCompletion F)
      one_ne_zero).1 hfin y
    exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩
  let ι := RingEquiv.ofBijective (algebraMap (v.adicCompletion K) (w.adicCompletion F)) hbij
  have hv : ∀ x, Valued.v (ι x) = Valued.v x := fun x => by
    have := GroundTheory.Global.valued_algebraMap_adicCompletion v w x
    rw [he, pow_one] at this
    exact this
  exact ⟨ι, GroundTheory.Global.continuous_adicCompletionMap v w, continuous_symm_of_valued_eq ι hv,
    GroundTheory.Global.adicCompletionMap_algebraMap v w, hv⟩

end Pair

end PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions.RamifiedPlaceLift

end
