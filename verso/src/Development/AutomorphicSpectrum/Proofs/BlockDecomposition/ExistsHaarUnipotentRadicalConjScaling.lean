import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalHaarFromProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSkewMatricesConjScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerImageNoDualComponent
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.QKAvg.RadMeas

variable {D : D7} {B W : HSp D} {t : ℕ}

/- English proof (translation)
Establish `h : mt B (m : GA D B) ⬝ d.jX = d.jX ⬝ a.1`. Rewrite using `[hm, mt_mul, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]`. Establish `e : GlobalTheory.RegSW.onX d m = a` using `Units.ext ((GlobalTheory.RegSW.eq_of_mul_jX d (GlobalTheory.RegSW.mul_jX d m)).trans (GlobalTheory.RegSW.eq_of_mul_jX d h).symm)`. Simplify using `only [GlobalTheory.RegSW.absDet, MonoidHom.comp_apply, e]`.
-/
theorem absDet_eq (d : HypDec B W t) (m : GlobalTheory.RegSW.stab d) (g : GA D W) (a : GL (Fin t) (AE D))
    (hm : (m : GA D B) = d.emb0 g * d.levi a) :
    GlobalTheory.RegSW.absDet d m = absA D (Matrix.GeneralLinearGroup.det a) := by
  have h : mt B (m : GA D B) ⬝ d.jX = d.jX ⬝ a.1 := by
    rw [hm, mt_mul, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]
  have e : GlobalTheory.RegSW.onX d m = a :=
    Units.ext ((GlobalTheory.RegSW.eq_of_mul_jX d (GlobalTheory.RegSW.mul_jX d m)).trans (GlobalTheory.RegSW.eq_of_mul_jX d h).symm)
  simp only [GlobalTheory.RegSW.absDet, MonoidHom.comp_apply, e]

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem regular_of_haar {A : Type} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] : μ.Regular := inferInstance

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem sFinite_of_haar {A : Type} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] : SFinite μ := inferInstance

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨i1, i2, i3, i4, -, -⟩` from `lattice_Mx D t n`. Use `haveI : IsTopologicalAddGroup (Mx D t n) := i1`. Use `haveI : LocallyCompactSpace (Mx D t n) := i2`. Use `haveI : SecondCountableTopology (Mx D t n) := i3`. Use `haveI : T2Space (Mx D t n) := i4`.

Use `haveI : BorelSpace (Mx D t n) := ⟨rfl⟩`. Use `haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)`. Set `φ` to `GlobalTheory.ModuLR.lrCE a h`. Establish `hc : addEquivAddHaarChar φ = absA D (Matrix.GeneralLinearGroup.det a) ^ n * absA D (Matrix.GeneralLinearGroup.det h) ^ t` using `GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) t n a h`. Rewrite `hc` using `[hh, one_pow, mul_one]`.

Establish `e : (fun b : Mx D t n => (a.1 ⬝ b ⬝ h.1 : Mx D t n)) = φ`. Use function extensionality and compare the values at `fun y => (GlobalTheory.ModuLR.lrCE_apply a h y).symm`. Establish `hA : absA D (Matrix.GeneralLinearGroup.det a) ^ n ≠ 0` using `pow_ne_zero _ ((Group.isUnit _).map (absA D)).ne_zero`. Use `haveI := regular_of_haar β`. Establish `key` using `addEquivAddHaarChar_smul_map β φ`.

Rewrite using `[e, ← hc]`. Rewrite `hA` using `[← hc]`. Use `conv_rhs => rw [← key]`. Rewrite using `[smul_smul, inv_mul_cancel₀ hA, one_smul]`.
-/
theorem map_lr {n : ℕ} (a : GL (Fin t) (AE D)) (h : GL (Fin n) (AE D))
    (hh : absA D (Matrix.GeneralLinearGroup.det h) = 1) (β : Measure (Mx D t n)) (hβ : β.IsAddHaarMeasure) :
    β.map (fun b : Mx D t n => (a.1 ⬝ b ⬝ h.1 : Mx D t n)) =
      ((absA D (Matrix.GeneralLinearGroup.det a) ^ n)⁻¹ : ℝ≥0) • β := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D t n
  haveI : IsTopologicalAddGroup (Mx D t n) := i1
  haveI : LocallyCompactSpace (Mx D t n) := i2
  haveI : SecondCountableTopology (Mx D t n) := i3
  haveI : T2Space (Mx D t n) := i4
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE a h
  have hc : addEquivAddHaarChar φ = absA D (Matrix.GeneralLinearGroup.det a) ^ n *
      absA D (Matrix.GeneralLinearGroup.det h) ^ t :=
    GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) t n a h
  rw [hh, one_pow, mul_one] at hc
  have e : (fun b : Mx D t n => (a.1 ⬝ b ⬝ h.1 : Mx D t n)) = φ :=
    funext fun y => (GlobalTheory.ModuLR.lrCE_apply a h y).symm
  have hA : absA D (Matrix.GeneralLinearGroup.det a) ^ n ≠ 0 := pow_ne_zero _ ((Group.isUnit _).map (absA D)).ne_zero
  haveI := regular_of_haar β
  have key := addEquivAddHaarChar_smul_map β φ
  rw [e, ← hc]
  rw [← hc] at hA
  conv_rhs => rw [← key]
  rw [smul_smul, inv_mul_cancel₀ hA, one_smul]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨i1, i2, i3, i4, -, -⟩` from `lattice_Mx D t W.rank`. Take `⟨j1, j2, j3, j4, -, -⟩` from `lattice_Mx D t t`. Use `haveI : IsTopologicalAddGroup (Mx D t W.rank) := i1`. Use `haveI : LocallyCompactSpace (Mx D t W.rank) := i2`. Use `haveI : SecondCountableTopology (Mx D t W.rank) := i3`.

Use `haveI : T2Space (Mx D t W.rank) := i4`. Use `haveI : BorelSpace (Mx D t W.rank) := ⟨rfl⟩`. Use `haveI : IsTopologicalAddGroup (Mx D t t) := j1`. Use `haveI : LocallyCompactSpace (Mx D t t) := j2`. Use `haveI : SecondCountableTopology (Mx D t t) := j3`.

Use `haveI : T2Space (Mx D t t) := j4`. Use `haveI : BorelSpace (Mx D t t) := ⟨rfl⟩`. Use `haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)`. Establish `hcl : IsClosed (skewA D t : Set (Mx D t t))` using `isClosed_eq continuous_adj continuous_neg`. Use `haveI : LocallyCompactSpace (skewA D t) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`.

Use `haveI : BorelSpace (skewA D t) := Subtype.borelSpace _`. Use `haveI : T2Space (skewA D t) := inferInstance`. Use `haveI : SecondCountableTopology (skewA D t) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology`. Set `κ : Measure (skewA D t)` to `Measure.addHaar`. Set `β : Measure (Mx D t W.rank)` to `Measure.addHaar`.

Use `haveI hκ : κ.IsAddHaarMeasure := inferInstance`. Use `haveI hβ : β.IsAddHaarMeasure := inferInstance`. Use `haveI := sFinite_of_haar κ`. Use `haveI := sFinite_of_haar β`. Take `⟨Ψ, hΨ, hH, hR⟩` from `GlobalTheory.T.unipotent_radical_haar_from_product D B W t d κ β hκ hβ`.

Use `⟨(κ.prod β).map Ψ, hH, hR, ?_⟩` and prove the remaining obligations. Introduce and unpack `m ⟨g, a, hm⟩`. Set `f₁ : skewA D t → skewA D t` to `skewConj a.1`. Set `f₂ : Mx D t W.rank → Mx D t W.rank` to `fun b => (a.1 ⬝ b ⬝ (matHom W g⁻¹).1 : Mx D t W.rank)`. Establish `hf₁ : Continuous f₁` using `Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _`.

Establish `hf₂ : Continuous f₂` using `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Establish `hL : ∀ n : radN d, (((MulAut.conjNormal m n : radN d) : GlobalTheory.RegSW.stab d) : GA D B) = (m : GA D B) * ((n : GlobalTheory.RegSW.stab d) : GA D B) * (m : GA D B)⁻¹` using `fun n => by`. Rewrite using `[MulAut.conjNormal_apply]`. Both sides reduce to the same expression. Establish `hconj : ∀ p, MulAut.conjNormal m (Ψ p) = Ψ (Prod.map f₁ f₂ p)`.

Introduce and unpack `⟨c, b⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use `(hL _).trans ?_` and prove the remaining obligations. Rewrite using `[hΨ (c, b), hΨ (Prod.map f₁ f₂ (c, b)), hm]`.

Conclude with `conj_coord d g a c b`. Establish `hcm : Measurable fun n : radN d => MulAut.conjNormal m n`. Establish `: (fun n : radN d => MulAut.conjNormal m n) = Ψ ∘ Prod.map f₁ f₂ ∘ Ψ.symm`. Use function extensionality and compare the values at `n`. Simplify using `only [Function.comp]`.

Rewrite using `[← hconj, Ψ.apply_symm_apply]`. Rewrite using `[this]`. Conclude with `(Ψ.continuous.comp ((hf₁.prodMap hf₂).comp Ψ.symm.continuous)).measurable`. Establish `hk` using `GlobalTheory.T.haar_skew_matrices_conj_scaling D t κ hκ a`. Establish `hb` using `map_lr a (matHom W g⁻¹) (GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw.absA_det_matHom g⁻¹) β hβ`.

Rewrite using `[Measure.map_map hcm Ψ.continuous.measurable]`. Establish `hc : (fun n : radN d => MulAut.conjNormal m n) ∘ Ψ = Ψ ∘ Prod.map f₁ f₂`. Use function extensionality and compare the values at `p`. Conclude with `hconj p`. Rewrite using `[hc, ← Measure.map_map Ψ.continuous.measurable (hf₁.prodMap hf₂).measurable, ← Measure.map_prod_map κ β hf₁.measurable hf₂.measurable]`.

Express the relevant statement in the definitionally equal form `(((κ.map (skewConj a.1)).prod (β.map _)).map Ψ) = _`. Rewrite using `[hk, hb, Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul, Measure.map_smul, smul_smul, absDet_eq d m g a hm, pow_add, mul_inv, mul_comm]`.
-/
theorem exists_radN_measure (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)] :
    ∃ νN : Measure (radN d), νN.IsHaarMeasure ∧ νN.IsMulRightInvariant ∧ ∀ m ∈ levM d,
      νN.map (fun n : radN d => MulAut.conjNormal m n) =
        ((GlobalTheory.RegSW.absDet d m ^ (W.rank + t))⁻¹ : ℝ≥0) • νN := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D t W.rank
  obtain ⟨j1, j2, j3, j4, -, -⟩ := lattice_Mx D t t
  haveI : IsTopologicalAddGroup (Mx D t W.rank) := i1
  haveI : LocallyCompactSpace (Mx D t W.rank) := i2
  haveI : SecondCountableTopology (Mx D t W.rank) := i3
  haveI : T2Space (Mx D t W.rank) := i4
  haveI : BorelSpace (Mx D t W.rank) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx D t t) := j1
  haveI : LocallyCompactSpace (Mx D t t) := j2
  haveI : SecondCountableTopology (Mx D t t) := j3
  haveI : T2Space (Mx D t t) := j4
  haveI : BorelSpace (Mx D t t) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hcl : IsClosed (skewA D t : Set (Mx D t t)) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D t) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : BorelSpace (skewA D t) := Subtype.borelSpace _
  haveI : T2Space (skewA D t) := inferInstance
  haveI : SecondCountableTopology (skewA D t) :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let κ : Measure (skewA D t) := Measure.addHaar
  let β : Measure (Mx D t W.rank) := Measure.addHaar
  haveI hκ : κ.IsAddHaarMeasure := inferInstance
  haveI hβ : β.IsAddHaarMeasure := inferInstance
  haveI := sFinite_of_haar κ
  haveI := sFinite_of_haar β
  obtain ⟨Ψ, hΨ, hH, hR⟩ := GlobalTheory.T.unipotent_radical_haar_from_product D B W t d κ β hκ hβ
  refine ⟨(κ.prod β).map Ψ, hH, hR, ?_⟩
  rintro m ⟨g, a, hm⟩
  let f₁ : skewA D t → skewA D t := skewConj a.1
  let f₂ : Mx D t W.rank → Mx D t W.rank := fun b => (a.1 ⬝ b ⬝ (matHom W g⁻¹).1 : Mx D t W.rank)
  have hf₁ : Continuous f₁ := Continuous.subtype_mk
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  have hf₂ : Continuous f₂ := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hL : ∀ n : radN d, (((MulAut.conjNormal m n : radN d) : GlobalTheory.RegSW.stab d) : GA D B) =
      (m : GA D B) * ((n : GlobalTheory.RegSW.stab d) : GA D B) * (m : GA D B)⁻¹ := fun n => by
    rw [MulAut.conjNormal_apply]
    rfl
  have hconj : ∀ p, MulAut.conjNormal m (Ψ p) = Ψ (Prod.map f₁ f₂ p) := by
    rintro ⟨c, b⟩
    apply Subtype.ext
    apply Subtype.ext
    refine (hL _).trans ?_
    rw [hΨ (c, b), hΨ (Prod.map f₁ f₂ (c, b)), hm]
    exact conj_coord d g a c b
  have hcm : Measurable fun n : radN d => MulAut.conjNormal m n := by
    have : (fun n : radN d => MulAut.conjNormal m n) = Ψ ∘ Prod.map f₁ f₂ ∘ Ψ.symm := by
      funext n
      simp only [Function.comp]
      rw [← hconj, Ψ.apply_symm_apply]
    rw [this]
    exact (Ψ.continuous.comp ((hf₁.prodMap hf₂).comp Ψ.symm.continuous)).measurable
  have hk := GlobalTheory.T.haar_skew_matrices_conj_scaling D t κ hκ a
  have hb := map_lr a (matHom W g⁻¹) (GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw.absA_det_matHom g⁻¹) β hβ
  rw [Measure.map_map hcm Ψ.continuous.measurable]
  have hc : (fun n : radN d => MulAut.conjNormal m n) ∘ Ψ = Ψ ∘ Prod.map f₁ f₂ := by
    funext p
    exact hconj p
  rw [hc, ← Measure.map_map Ψ.continuous.measurable (hf₁.prodMap hf₂).measurable,
    ← Measure.map_prod_map κ β hf₁.measurable hf₂.measurable]
  change (((κ.map (skewConj a.1)).prod (β.map _)).map Ψ) = _
  rw [hk, hb, Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul, Measure.map_smul, smul_smul,
    absDet_eq d m g a hm, pow_add, mul_inv, mul_comm]

end GlobalTheory.CompanionTheory.QKAvg.RadMeas
