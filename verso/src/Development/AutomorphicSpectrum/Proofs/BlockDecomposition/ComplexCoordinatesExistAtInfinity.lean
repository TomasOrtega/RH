import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hc'` using `h.2.1`. Use `IsTotallyComplex.complexEmbedding_not_isReal τ ?_` and prove the remaining obligations.

Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `y`. Use `h.2.2.2 τ y` as an intermediate fact. Rewrite `this` using `[hc y]`. Simplify using `using this.symm`.
-/
theorem exists_moved (h : IsCMExt F E σ) : ∃ θ : E, σ θ ≠ θ := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hc' := h.2.1
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have := h.2.2.2 τ y
  rw [hc y] at this
  simpa using this.symm

/- English proof (translation)
Introduce `h0`. Apply `hθ` to reduce the goal to its premises. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2]`. Conclude with `Complex.conj_eq_iff_im.2 h0`.
-/
theorem im_ne_zero (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) (τ : E →+* ℂ) : (τ θ).im ≠ 0 := by
  intro h0
  apply hθ
  apply τ.injective
  rw [h.2.2.2]
  exact Complex.conj_eq_iff_im.2 h0

/- English proof (translation)
Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Establish `h1 : s • (1 : E) + t • σ θ = 0`. Use `congrArg σ hst` as an intermediate fact. Simplify using `only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, map_zero] at this ⊢`.

Conclude with `this`. Establish `h2 : t • (σ θ - θ) = 0`. Rewrite using `[smul_sub, sub_eq_zero]`. Conclude with `add_left_cancel (h1.trans hst.symm)`. Establish `ht : t = 0`.

Break down `smul_eq_zero.1 h2 with h3 | h3` into its components or cases. Conclude with `h3`. Conclude with `absurd (sub_eq_zero.1 h3) hθ`. Substitute `ht` using the available equality. Use `⟨?_, rfl⟩` and prove the remaining obligations.

Simplify using `using hst`.
-/
theorem linInd_one (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) :
    LinearIndependent F ![(1 : E), θ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : s • (1 : E) + t • σ θ = 0 := by
    have := congrArg σ hst
    simp only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, map_zero] at this ⊢
    exact this
  have h2 : t • (σ θ - θ) = 0 := by
    rw [smul_sub, sub_eq_zero]
    exact add_left_cancel (h1.trans hst.symm)
  have ht : t = 0 := by
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.1 h3) hθ
  subst ht
  refine ⟨?_, rfl⟩
  simpa using hst

def basisOne (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) : Module.Basis (Fin 2) F E :=
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
  basisOfLinearIndependentOfCardEqFinrank (linInd_one h hθ) (by rw [h.2.2.1]; simp)

/- English proof (translation)
Simplify using `[basisOne]`.
-/
theorem basisOne_zero (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) : basisOne h hθ 0 = 1 := by
  simp [basisOne]

/- English proof (translation)
Simplify using `[basisOne]`.
-/
theorem basisOne_one (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) : basisOne h hθ 1 = θ := by
  simp [basisOne]

end Field

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def coordHomeo (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) : (R ⊗[F] E) ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { (Algebra.TensorProduct.basis R b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

def planeHomeo {W : Type} (t : W → ℂ) (ht : ∀ w, (t w).im ≠ 0) : (Fin 2 → W → ℝ) ≃ₜ (W → ℂ) where
  toFun f w := (f 0 w : ℂ) + (f 1 w : ℂ) * t w
  invFun g := ![fun w => (g w).re - (g w).im / (t w).im * (t w).re, fun w => (g w).im / (t w).im]
  left_inv f := by
    funext k w
    have := ht w
    fin_cases k
    · simp
      field_simp
      ring
    · simp
      field_simp
  right_inv g := by
    funext w
    have := ht w
    apply Complex.ext
    · simp
    · simp
      field_simp
  continuous_toFun := by
    refine continuous_pi fun w => ?_
    have h0 : Continuous fun f : Fin 2 → W → ℝ => f 0 w := (continuous_apply w).comp (continuous_apply 0)
    have h1 : Continuous fun f : Fin 2 → W → ℝ => f 1 w := (continuous_apply w).comp (continuous_apply 1)
    exact (Complex.continuous_ofReal.comp h0).add ((Complex.continuous_ofReal.comp h1).mul continuous_const)
  continuous_invFun := by
    refine continuous_pi fun k => continuous_pi fun w => ?_
    have hr : Continuous fun g : W → ℂ => (g w).re := Complex.continuous_re.comp (continuous_apply w)
    have hi : Continuous fun g : W → ℂ => (g w).im := Complex.continuous_im.comp (continuous_apply w)
    fin_cases k
    · exact hr.sub ((hi.div_const _).mul continuous_const)
    · exact hi.div_const _

end Top

section Map

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Use `letI : Algebra F (InfinitePlace F → ℂ) := (Pi.ringHom fun w => (τ w).comp (algebraMap F E)).toAlgebra`. Set `fA : Ainf F →ₐ[F] (InfinitePlace F → ℂ)` to `{ toRingHom := Pi.ringHom fun w => Complex.ofRealHom.comp ((Pi.evalRingHom (fun _ => ℝ) w).comp (e : Ainf F →+* (InfinitePlace F → ℝ))) commutes' := fun x => funext fun w => hc x w }`. Set `fE : E →ₐ[F] (InfinitePlace F → ℂ)` to `{ toRingHom := Pi.ringHom τ commutes' := fun _ => rfl }`. Conclude with `⟨(Algebra.TensorProduct.productMap fA fE).toRingHom, fun a x w => by`. Simplify using `[Algebra.TensorProduct.productMap_apply_tmul, fA, fE]`.

Use the proof step `rfl⟩`.
-/
theorem exists_hom (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
    (hc : ∀ x w, ((e (algebraMap F (Ainf F) x) w : ℝ) : ℂ) = τ w (algebraMap F E x)) :
    ∃ Θ : Ainf F ⊗[F] E →+* (InfinitePlace F → ℂ),
      ∀ a x w, Θ (a ⊗ₜ[F] x) w = (e a w : ℂ) * τ w x := by
  letI : Algebra F (InfinitePlace F → ℂ) :=
    (Pi.ringHom fun w => (τ w).comp (algebraMap F E)).toAlgebra
  let fA : Ainf F →ₐ[F] (InfinitePlace F → ℂ) :=
    { toRingHom := Pi.ringHom fun w =>
        Complex.ofRealHom.comp ((Pi.evalRingHom (fun _ => ℝ) w).comp (e : Ainf F →+* (InfinitePlace F → ℝ)))
      commutes' := fun x => funext fun w => hc x w }
  let fE : E →ₐ[F] (InfinitePlace F → ℂ) :=
    { toRingHom := Pi.ringHom τ
      commutes' := fun _ => rfl }
  exact ⟨(Algebra.TensorProduct.productMap fA fE).toRingHom, fun a x w => by
    simp [Algebra.TensorProduct.productMap_apply_tmul, fA, fE]
    rfl⟩

end Map

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h ρ e hρ he hx`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)`. Establish `hex : ∀ w : InfinitePlace F, ∃ t : E →+* ℂ, ∀ x, t (algebraMap F E x) = w.embedding x`. Introduce `w`. Use `letI : Algebra F ℂ := w.embedding.toAlgebra`.

Set `t : E →ₐ[F] ℂ` to `IsAlgClosed.lift`. Conclude with `⟨t, fun x => t.commutes x⟩`. Use `choose τ hτ using hex`. Take `⟨θ, hθ⟩` from `exists_moved h`. Take `⟨Θ, hΘ⟩` from `exists_hom e τ (fun x w => by rw [hx, hρ, hτ])`.

Set `eH : Ainf F ≃ₜ (InfinitePlace F → ℝ)` to `he.homeomorph`. Set `b` to `basisOne h hθ`. Set `H : (Ainf F ⊗[F] E) ≃ₜ (InfinitePlace F → ℂ)` to `(coordHomeo (Ainf F) b).trans ((Homeomorph.piCongrRight fun _ => eH).trans (planeHomeo (fun w => τ w θ) (fun w => im_ne_zero h hθ (τ w))))`. Establish `hH : ∀ y, H y = Θ y`. Introduce `y`.

Establish `hy : y = (Algebra.TensorProduct.basis (Ainf F) b).repr y 0 ⊗ₜ[F] (1 : E) + (Algebra.TensorProduct.basis (Ainf F) b).repr y 1 ⊗ₜ[F] θ` using `by conv_lhs => rw [← (Algebra.TensorProduct.basis (Ainf F) b).sum_repr y]`. Rewrite using `[Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, basisOne_zero, basisOne_one, TensorProduct.smul_tmul', TensorProduct.smul_tmul']`. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `w`. Use `conv_rhs => rw [hy, map_add, Pi.add_apply, hΘ, hΘ, map_one, mul_one]`.

Both sides reduce to the same expression. Establish `hbij : Function.Bijective Θ`. Establish `: (Θ : Ainf F ⊗[F] E → _) = H` using `funext fun y => (hH y).symm`. Rewrite using `[this]`. Conclude with `H.bijective`.

Use `⟨τ, RingEquiv.ofBijective Θ hbij, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: ((RingEquiv.ofBijective Θ hbij : Ainf F ⊗[F] E ≃+* _) : Ainf F ⊗[F] E → _) = H`. Use function extensionality and compare the values at `fun y => (hH y).symm`. Rewrite using `[this]`. Conclude with `H.isHomeomorph`.

Introduce `z w`. Simplify using `only [RingEquiv.ofBijective_apply]`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x`.

Establish `: sigR (Ainf F) σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x` using `by simp [sigR]`. Rewrite using `[this, hΘ, hΘ, h.2.2.2, map_mul, Complex.conj_ofReal]`. Both sides reduce to the same expression. Consider the case `add y y' hy hy' => simp only [map_add, Pi.add_apply, hy, hy']`. Introduce `x w`.

Simplify using `only [RingEquiv.ofBijective_apply]`. Rewrite using `[hΘ, map_one]`. Simplify using the standard rewrite rules. Introduce `z w`. Simplify using `only [RingEquiv.ofBijective_apply]`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x`. Establish `h1 : τ w x + conj (τ w x) = ((ρ w (Algebra.trace F E x) : ℝ) : ℂ)`. Rewrite using `[hρ, ← hτ, ← GlobalTheory.GaussMean.OneVec.add_sigma h, map_add, h.2.2.2]`.

Both sides reduce to the same expression. Rewrite using `[GlobalTheory.GaussMean.OneVec.trace_tmul, map_mul, Pi.mul_apply, hx, hΘ, map_mul, Complex.conj_ofReal, Complex.ofReal_mul, ← h1]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add y y' hy hy'`. Simplify using `only [map_add, Pi.add_apply, Complex.ofReal_add, hy, hy']`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_isCoord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)),
  (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) →
  ∃ (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)),
    IsCoord σ e τ Θ := by
  intro F E _ _ _ _ _ σ h ρ e hρ he hx
  classical
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
  have hex : ∀ w : InfinitePlace F, ∃ t : E →+* ℂ, ∀ x, t (algebraMap F E x) = w.embedding x := by
    intro w
    letI : Algebra F ℂ := w.embedding.toAlgebra
    let t : E →ₐ[F] ℂ := IsAlgClosed.lift
    exact ⟨t, fun x => t.commutes x⟩
  choose τ hτ using hex
  obtain ⟨θ, hθ⟩ := exists_moved h
  obtain ⟨Θ, hΘ⟩ := exists_hom e τ (fun x w => by rw [hx, hρ, hτ])
  let eH : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph
  let b := basisOne h hθ
  let H : (Ainf F ⊗[F] E) ≃ₜ (InfinitePlace F → ℂ) :=
    (coordHomeo (Ainf F) b).trans ((Homeomorph.piCongrRight fun _ => eH).trans
      (planeHomeo (fun w => τ w θ) (fun w => im_ne_zero h hθ (τ w))))
  have hH : ∀ y, H y = Θ y := by
    intro y
    have hy : y = (Algebra.TensorProduct.basis (Ainf F) b).repr y 0 ⊗ₜ[F] (1 : E) +
        (Algebra.TensorProduct.basis (Ainf F) b).repr y 1 ⊗ₜ[F] θ := by
      conv_lhs => rw [← (Algebra.TensorProduct.basis (Ainf F) b).sum_repr y]
      rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
        basisOne_zero, basisOne_one, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      simp
    funext w
    conv_rhs => rw [hy, map_add, Pi.add_apply, hΘ, hΘ, map_one, mul_one]
    rfl
  have hbij : Function.Bijective Θ := by
    have : (Θ : Ainf F ⊗[F] E → _) = H := funext fun y => (hH y).symm
    rw [this]
    exact H.bijective
  refine ⟨τ, RingEquiv.ofBijective Θ hbij, ?_, ?_, ?_, ?_⟩
  · have : ((RingEquiv.ofBijective Θ hbij : Ainf F ⊗[F] E ≃+* _) : Ainf F ⊗[F] E → _) = H :=
      funext fun y => (hH y).symm
    rw [this]
    exact H.isHomeomorph
  · intro z w
    simp only [RingEquiv.ofBijective_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have : sigR (Ainf F) σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := by simp [sigR]
      rw [this, hΘ, hΘ, h.2.2.2, map_mul, Complex.conj_ofReal]
      rfl
    | add y y' hy hy' => simp only [map_add, Pi.add_apply, hy, hy']
  · intro x w
    simp only [RingEquiv.ofBijective_apply]
    rw [hΘ, map_one]
    simp
  · intro z w
    simp only [RingEquiv.ofBijective_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have h1 : τ w x + conj (τ w x) = ((ρ w (Algebra.trace F E x) : ℝ) : ℂ) := by
        rw [hρ, ← hτ, ← GlobalTheory.GaussMean.OneVec.add_sigma h, map_add, h.2.2.2]
        rfl
      rw [GlobalTheory.GaussMean.OneVec.trace_tmul, map_mul, Pi.mul_apply, hx, hΘ, map_mul, Complex.conj_ofReal,
        Complex.ofReal_mul, ← h1]
      ring
    | add y y' hy hy' =>
      simp only [map_add, Pi.add_apply, Complex.ofReal_add, hy, hy']
      ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
