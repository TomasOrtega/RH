import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacOfMemFockA
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ResAniso.VacSchwartz

open Classical in

/- English proof (translation)
Introduce `h0`. Take `⟨a, ha, hinf⟩` from `GlobalTheory.AdeleCharConductor.exists_scaling hψ`. Establish `hbij` using `GlobalTheory.CMTypePlaces.places_bijective D`. Set `w : D.what₂.Tau → InfinitePlace D.host.F` to `fun τ => InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))`. Establish `hemb : ∀ τ, (w τ).embedding = (tauE D τ).comp (algebraMap D.host.F D.host.E)` using `fun τ => InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))`.

Establish `hθ' : ∀ τ (x : Ainf D.host.F), θ τ (x ⊗ₜ[D.host.F] (1 : D.host.E)) = InfinitePlace.Completion.extensionEmbedding (w τ) (x (w τ))` using `fun τ => congrFun ((InfiniteAdeleRing.denseRange_algebraMap D.host.F).equalizer (hθ τ).2 ((InfinitePlace.Completion.isometry_extensionEmbedding (w τ)).continuous.comp (continuous_apply (w τ))) (funext fun b => by show θ τ (algebraMap D.host.F (Ainf D.host.F) b ⊗ₜ[D.host.F] (1 : D …`. Rewrite using `[GlobalTheory.StdRat.tmul_one_eq, (hθ τ).1, Function.comp_apply]`. Use `erw [GlobalTheory.AdeleCharConductor.extensionEmbedding_algebraMap (w τ) b, hemb]`. Use the proof step `rfl))`. Use `set e : ℝ := ((w τ₀).embedding a).re with he`.

Establish `hre : ((w τ₀).embedding a).im = 0`. Establish `hr : NumberField.ComplexEmbedding.IsReal (w τ₀).embedding` using `InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal _)`. Use `congrArg (fun φ : D.host.F →+* ℂ => φ a) hr` as an intermediate fact. Conclude with `Complex.conj_eq_iff_im.1 this`. Establish `he0 : e ≠ 0`.

Introduce `h`. Apply `ha` to reduce the goal to its premises. Establish `: (w τ₀).embedding a = 0` using `Complex.ext (by simpa [he] using h) (by simpa using hre)`. Conclude with `(map_eq_zero_iff _ (w τ₀).embedding.injective).1 this`. Take `⟨x, hx⟩` from `GlobalTheory.StdUnn.RealPar.exists_real_point hθ τ₀ (1 / (2 * e))`.

Establish `e1` using `hl x`. Simplify using `only [hx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, h0, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at e1`. Establish `e2` using `hinf x`. Establish `hsum : ∑ u : InfinitePlace D.host.F, (u.embedding a).re * (InfinitePlace.Completion.extensionEmbedding u (x u)).re = e * (1 / (2 * e))`. Rewrite using `[← hbij.sum_comp (fun u : InfinitePlace D.host.F => (u.embedding a).re * (InfinitePlace.Completion.extensionEmbedding u (x u)).re)]`.

Establish `hterm : ∀ τ, ((w τ).embedding a).re * (InfinitePlace.Completion.extensionEmbedding (w τ) (x (w τ))).re = if τ = τ₀ then e * (1 / (2 * e)) else 0` using `fun τ => by`. Rewrite using `[← hθ' τ x, hx τ]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `[he]`.

Simplify using the standard rewrite rules. Use `(Finset.sum_congr rfl fun τ _ => hterm τ).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite `e2` using `[hsum, e1]`. Establish `h2 : e * (1 / (2 * e)) = 1 / 2` using `by field_simp`.

Rewrite `e2` using `[h2]`. Establish `h3 : (2 * Real.pi * Complex.I * (((1 / 2 : ℝ)) : ℂ)) = Real.pi * Complex.I` using `by push_cast; ring`. Rewrite `e2` using `[h3, Complex.exp_pi_mul_I]`. Evaluate the numerical expressions using `at e2`.
-/
theorem realPar_ne_zero (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsCharAF D.host.F ψ) (l : D.what₂.Tau → ℝ) (hl : StdUnn.HasRealPar ψ θ l) (τ₀ : D.what₂.Tau) : l τ₀ ≠ 0 := by
  intro h0
  obtain ⟨a, ha, hinf⟩ := GlobalTheory.AdeleCharConductor.exists_scaling hψ
  have hbij := GlobalTheory.CMTypePlaces.places_bijective D
  let w : D.what₂.Tau → InfinitePlace D.host.F := fun τ =>
    InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))
  have hemb : ∀ τ, (w τ).embedding = (tauE D τ).comp (algebraMap D.host.F D.host.E) := fun τ =>
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))
  have hθ' : ∀ τ (x : Ainf D.host.F), θ τ (x ⊗ₜ[D.host.F] (1 : D.host.E)) =
      InfinitePlace.Completion.extensionEmbedding (w τ) (x (w τ)) := fun τ =>
    congrFun ((InfiniteAdeleRing.denseRange_algebraMap D.host.F).equalizer (hθ τ).2
      ((InfinitePlace.Completion.isometry_extensionEmbedding (w τ)).continuous.comp (continuous_apply (w τ)))
      (funext fun b => by
        show θ τ (algebraMap D.host.F (Ainf D.host.F) b ⊗ₜ[D.host.F] (1 : D.host.E)) = _
        rw [GlobalTheory.StdRat.tmul_one_eq, (hθ τ).1, Function.comp_apply]
        erw [GlobalTheory.AdeleCharConductor.extensionEmbedding_algebraMap (w τ) b, hemb]
        rfl))
  set e : ℝ := ((w τ₀).embedding a).re with he
  have hre : ((w τ₀).embedding a).im = 0 := by
    have hr : NumberField.ComplexEmbedding.IsReal (w τ₀).embedding :=
      InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal _)
    have := congrArg (fun φ : D.host.F →+* ℂ => φ a) hr
    exact Complex.conj_eq_iff_im.1 this
  have he0 : e ≠ 0 := by
    intro h
    apply ha
    have : (w τ₀).embedding a = 0 := Complex.ext (by simpa [he] using h) (by simpa using hre)
    exact (map_eq_zero_iff _ (w τ₀).embedding.injective).1 this
  obtain ⟨x, hx⟩ := GlobalTheory.StdUnn.RealPar.exists_real_point hθ τ₀ (1 / (2 * e))
  have e1 := hl x
  simp only [hx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, h0, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero] at e1
  have e2 := hinf x
  have hsum : ∑ u : InfinitePlace D.host.F, (u.embedding a).re *
      (InfinitePlace.Completion.extensionEmbedding u (x u)).re = e * (1 / (2 * e)) := by
    rw [← hbij.sum_comp (fun u : InfinitePlace D.host.F => (u.embedding a).re *
      (InfinitePlace.Completion.extensionEmbedding u (x u)).re)]
    have hterm : ∀ τ, ((w τ).embedding a).re * (InfinitePlace.Completion.extensionEmbedding (w τ) (x (w τ))).re =
        if τ = τ₀ then e * (1 / (2 * e)) else 0 := fun τ => by
      rw [← hθ' τ x, hx τ]
      split_ifs with h
      · subst h; simp [he]
      · simp
    refine (Finset.sum_congr rfl fun τ _ => hterm τ).trans ?_
    simp
  rw [hsum, e1] at e2
  have h2 : e * (1 / (2 * e)) = 1 / 2 := by field_simp
  rw [h2] at e2
  have h3 : (2 * Real.pi * Complex.I * (((1 / 2 : ℝ)) : ℂ)) = Real.pi * Complex.I := by push_cast; ring
  rw [h3, Complex.exp_pi_mul_I] at e2
  norm_num at e2

end GlobalTheory.ResAniso.VacSchwartz
end
