import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.NuBridgeA

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform ComplexConjugate
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

section Gen

variable {V : Type} [Fintype V] {n m : ℕ}

def reimVE : (V → Matrix (Fin n) (Fin m) ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (V × Fin n × Fin m × Bool) where
  toFun M := reimV M
  invFun y := fun v i j => ⟨y (v, i, j, true), y (v, i, j, false)⟩
  map_add' M N := by
    ext p
    rcases p with ⟨v, i, j, s⟩
    cases s <;> simp [reimV]
  map_smul' c M := by
    ext p
    rcases p with ⟨v, i, j, s⟩
    cases s <;> simp [reimV]
  left_inv M := by
    funext v i j
    apply Complex.ext <;> simp [reimV]
  right_inv y := by
    ext p
    rcases p with ⟨v, i, j, s⟩
    cases s <;> simp [reimV]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem reimVE_apply (M : V → Matrix (Fin n) (Fin m) ℂ) : reimVE M = reimV M := rfl

/- English proof (translation)
Rewrite using `[PiLp.inner_apply, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_bool]`. Simplify using `[reimV, mul_comm]`.
-/
theorem inner_reimV (M N : V → Matrix (Fin n) (Fin m) ℂ) :
    ⟪reimV M, reimV N⟫ = ∑ v, ∑ i, ∑ j, ((M v i j).re * (N v i j).re + (M v i j).im * (N v i j).im) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp [reimV, mul_comm]

/- English proof (translation)
Rewrite using `[← real_inner_self_eq_norm_sq, inner_reimV]`. Use `Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`.
-/
theorem norm_reimV_sq (M : V → Matrix (Fin n) (Fin m) ℂ) :
    ‖reimV M‖ ^ 2 = ∑ v, ∑ i, ∑ j, ‖M v i j‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_reimV]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]

variable (V m) in

def hermFam : Submodule ℝ (V → Matrix (Fin m) (Fin m) ℂ) where
  carrier := {M | ∀ v, (M v)ᴴ = M v}
  add_mem' {M N} hM hN v := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Pi.add_apply, Matrix.conjTranspose_add, hM v, hN v]
  zero_mem' v := by simp
  smul_mem' c M hM v := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Pi.smul_apply, Matrix.conjTranspose_smul, hM v, star_trivial]

end Gen

/- English proof (translation)
The claim follows from `(Algebra.TensorProduct.map (AlgHom.id X.B.I.F (Ainf X.B.I.F)) X.B.I.cm.sig).commutes q`.
-/
theorem sigR_alg {D : D7} (X : HidaSetting D) (q : X.B.I.F) :
    sigR (Ainf X.B.I.F) X.B.I.cm.sig (algebraMap X.B.I.F (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) q) =
      algebraMap X.B.I.F (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) q :=
  (Algebra.TensorProduct.map (AlgHom.id X.B.I.F (Ainf X.B.I.F)) X.B.I.cm.sig).commutes q

/- English proof (translation)
Rewrite using `[Complex.add_conj]`. Simplify using the standard rewrite rules.
-/
theorem half_re (w : ℂ) : ((1 / 2 : ℂ) * (w + conj w)).re = w.re := by
  rw [Complex.add_conj]
  simp

/- English proof (translation)
Rewrite using `[map_div₀, map_one, map_ofNat]`.
-/
theorem half_emb {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) : v.embedding (1 / 2) = (1 / 2 : ℂ) := by
  rw [map_div₀, map_one, map_ofNat]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `D X u' ψ hT μinf νinf fibInf hP`. Use `haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X`. Use `haveI : BorelSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) := ⟨rfl⟩`. Set `Kr : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace X.B.I.F × Fin (D.R.rS + 1 + D.R.rS) × Fin (D.R.rS + 1 + D.R.rS) × Bool))` to `(hermFam (InfinitePlace X.B.I.F) (D.R.rS + 1 + D.R.rS)).map (reimVE : _ ≃ₗ[ℝ] _).toLinearMap`. Set `bK` to `stdOrthonormalBasis ℝ Kr`.

Set `Hh : EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)) →ₗ[ℝ] (InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ)` to `(reimVE : _ ≃ₗ[ℝ] _).symm.toLinearMap ∘ₗ Kr.subtype ∘ₗ bK.repr.symm.toLinearEquiv.toLinearMap`. Establish `hHh : ∀ s, Hh s = (reimVE : _ ≃ₗ[ℝ] _).symm (bK.repr.symm s : _)` using `fun s => rfl`. Set `thH : HmI X → InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ` to `fun S v => S.1.map (PI.AprimeInfU.thetaInf X v)`. Establish `thH_herm : ∀ S, thH S ∈ hermFam (InfinitePlace X.B.I.F) (D.R.rS + 1 + D.R.rS)`. Introduce `S v`.

Establish `hS : ∀ a b, sigR (Ainf X.B.I.F) X.B.I.cm.sig (S.1 b a) = S.1 a b` using `S.2`. Use extensionality with `i j`. Simplify using `only [thH, Matrix.conjTranspose_apply, Matrix.map_apply]`. Rewrite using `[show star (PI.AprimeInfU.thetaInf X v (S.1 j i)) = conj (PI.AprimeInfU.thetaInf X v (S.1 j i)) from rfl, ← NuB.theta_sigR X v, hS i j]`. Establish `memK : ∀ S, (reimVE : _ ≃ₗ[ℝ] _) (thH S) ∈ Kr` using `fun S => Submodule.mem_map_of_mem (thH_herm S)`.

Set `TcF : HmI X → EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr))` to `fun S => bK.repr ⟨_, memK S⟩`. Establish `hHT : ∀ S, Hh (TcF S) = thH S`. Introduce `S`. Rewrite using `[hHh, LinearIsometryEquiv.symm_apply_apply]`. Conclude with `(reimVE : _ ≃ₗ[ℝ] _).symm_apply_apply (thH S)`.

Establish `thH_add : ∀ S T, thH (S + T) = thH S + thH T`. Introduce `S T`. Use function extensionality and compare the values at `v i j`. Simplify using `[thH, Matrix.map_apply, map_add]`. Establish `TcF_add : ∀ S T, TcF (S + T) = TcF S + TcF T`.

Introduce `S T`. Establish `e : (⟨_, memK (S + T)⟩ : Kr) = ⟨_, memK S⟩ + ⟨_, memK T⟩` using `Subtype.ext (by show (reimVE : _ ≃ₗ[ℝ] _) (thH (S + T)) = (reimVE : _ ≃ₗ[ℝ] _) (thH S) + (reimVE : _ ≃ₗ[ℝ] _) (thH T)`. Rewrite using `[thH_add, map_add])`. Conclude with `(congrArg bK.repr e).trans (map_add bK.repr _ _)`. Establish `hθc : ∀ v i j, Continuous fun S : HmI X => PI.AprimeInfU.thetaInf X v (S.1 i j)` using `fun v i j => (continuous_thetaInf X v).comp (continuous_subtype_val.matrix_elem i j)`.

Establish `hcont : Continuous TcF`. Use `bK.repr.continuous.comp (Continuous.subtype_mk ?_ _)` and prove the remaining obligations. Use `show Continuous fun S => (EuclideanSpace.equiv _ ℝ).symm (fun p : InfinitePlace X.B.I.F × Fin (D.R.rS + 1 + D.R.rS) × Fin (D.R.rS + 1 + D.R.rS) × Bool => if p.2.2.2 then (thH S p.1 p.2.1 p.2.2.1).re else (thH S p.1 p.2.1 p.2.2.1).im)`. Use `(EuclideanSpace.equiv _ ℝ).symm.continuous.comp (continuous_pi fun p => ?_)` and prove the remaining obligations. Break down `p with ⟨v, i, j, s⟩` into its components or cases.

Consider the cases of `s`. Conclude with `Complex.continuous_im.comp (hθc v i j)`. Conclude with `Complex.continuous_re.comp (hθc v i j)`. Establish `hinj : Function.Injective TcF`. Introduce `S T h`.

Establish `h1 : thH S = thH T` using `by rw [← hHT S, ← hHT T, h]`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `a b`. Apply `sub_eq_zero.1` to reduce the goal to its premises. Apply `thetaInf_inj X` to reduce the goal to its premises.

Introduce `v`. Use `congrFun (congrFun (congrFun h1 v) a) b` as an intermediate fact. Simplify using `only [thH, Matrix.map_apply] at this`. Rewrite using `[map_sub, this, sub_self]`. Establish `hsurj : Function.Surjective TcF`.

Introduce `s`. Take `⟨M, hM, hMs⟩` from `Submodule.mem_map.1 (bK.repr.symm s).2`. Use `choose y hy using fun a b : Fin (D.R.rS + 1 + D.R.rS) => NuB.theta_surj X (fun v => M v a b)`. Set `h2` to `algebraMap X.B.I.F (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) (1 / 2)`. Set `Sm : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)` to `fun a b => h2 * (y a b + sigR (Ainf X.B.I.F) X.B.I.cm.sig (y b a))`.

Establish `hSm : Sm ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)` using `by show ∀ a b, sigR (Ainf X.B.I.F) X.B.I.cm.sig (Sm b a) = Sm a b`. Introduce `a b`. Simplify using `only [Sm, h2, map_mul, map_add, sigR_invP _ _ (sig_invI X), sigR_alg]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨⟨Sm, hSm⟩, ?_⟩` and prove the remaining obligations.

Establish `e : thH ⟨Sm, hSm⟩ = M`. Use function extensionality and compare the values at `v a b`. Establish `hMh : conj (M v b a) = M v a b`. Use `congrFun (congrFun (hM v) a) b` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_apply]`.

Simplify using `only [thH, Matrix.map_apply, Sm, h2, map_mul, map_add, NuB.theta_alg, NuB.theta_sigR, hy, hMh, half_emb]`. Expand and normalize the polynomial expressions, which then agree. Use `show bK.repr _ = s`. Rewrite using `[← bK.repr.apply_symm_apply s]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show (reimVE : _ ≃ₗ[ℝ] _) (thH ⟨Sm, hSm⟩) = _`. Rewrite using `[e]`. Conclude with `hMs`. Set `Ψa : Wh X →+ EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr))` to `AddMonoidHom.mk' (fun x => TcF ((hermCoord X).symm x)) (fun x y => by rw [hermCoord_symm_add, TcF_add])`.

Set `Ψc : Wh X →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr))` to `AddMonoidHom.toRealLinearMap Ψa (hcont.comp (hermCoord X).symm.continuous)`. Establish `hΨ : ∀ x, Ψc x = TcF ((hermCoord X).symm x)` using `fun x => rfl`. Establish `hΨb : Function.Bijective Ψc`. Use `⟨fun x y h => (hermCoord X).symm.injective (hinj (by rw [← hΨ, ← hΨ, h])), fun s => ?_⟩` and prove the remaining obligations. Take `⟨S, hS⟩` from `hsurj s`.

Conclude with `⟨hermCoord X S, by rw [hΨ, Homeomorph.symm_apply_apply, hS]⟩`. Set `Ψe : Wh X ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr))` to `(LinearEquiv.ofBijective (Ψc : Wh X →ₗ[ℝ] _) hΨb).toContinuousLinearEquiv`. Set `Tc : HmI X ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr))` to `(hermCoord X).trans Ψe.toHomeomorph`. Establish `hTc : ∀ S, Tc S = TcF S`. Introduce `S`.

Use `show Ψc (hermCoord X S) = TcF S`. Rewrite using `[hΨ, Homeomorph.symm_apply_apply]`. Establish `key : ∀ S T : HmI X, sumReI X (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T) = ⟪TcF S, TcF T⟫`. Introduce `S T`. Establish `e1 : ⟪TcF S, TcF T⟫ = ⟪reimV (thH S), reimV (thH T)⟫`.

Simplify using `only [TcF, LinearIsometryEquiv.inner_map_map]`. Both sides reduce to the same expression. Establish `hTh : ∀ v a b, PI.AprimeInfU.thetaInf X v (T.1 b a) = conj (PI.AprimeInfU.thetaInf X v (T.1 a b))`. Introduce `v a b`. Establish `hT' : ∀ a b, sigR (Ainf X.B.I.F) X.B.I.cm.sig (T.1 b a) = T.1 a b` using `T.2`.

Rewrite using `[← NuB.theta_sigR X v, hT' b a]`. Rewrite using `[e1, inner_reimV]`. Simplify using `only [sumReI]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Use `show (PI.AprimeInfU.evInf X v (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)).re = _`.

Rewrite using `[pairHerm, map_mul, NuB.evInf_alg, NuB.evInf_trace, half_emb, half_re, map_sum, Complex.re_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, Complex.re_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hTh v a b]`.

Simplify using `only [thH, Matrix.map_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree. Establish `hS` using `hP.2.2.1`. Establish `hν : SelfDual νinf (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T))` using `hP.2.2.2.2.2.1`. Establish `h1 : ∀ x y : EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)), (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)) (Tc.symm x) (Tc.symm y) = ((𝐞 (⟪x, y⟫) : Circle) : ℂ)`.

Introduce `x y`. Take `⟨S, rfl⟩` from `Tc.surjective x`. Take `⟨T, rfl⟩` from `Tc.surjective y`. Establish `e1 : Tc.symm (Tc S) = S` using `Tc.symm_apply_apply S`. Establish `e2 : Tc.symm (Tc T) = T` using `Tc.symm_apply_apply T`.

Establish `e3 : ⟪Tc S, Tc T⟫ = sumReI X (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)`. Rewrite using `[hTc S, hTc T, key]`. Use `show psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) (Tc.symm (Tc S)) (Tc.symm (Tc T))) = _`. Rewrite using `[e1, e2, e3]`. Simplify using `only [sumReI]`.

Rewrite using `[psiInf_eq ψ hS, Real.fourierChar_apply]`. Use `push_cast`. Put the polynomial expressions in normal form. Establish `hd` using `PI.AprimeInfW.GenericDensity.dens_generic νinf _ hν Tc (fun S T => by rw [hTc, hTc, hTc, TcF_add]) (fun x y => ⟪x, y⟫) h1 (fun x x' y => inner_add_left x x' y) (fun x y y' => inner_add_right x y y') (fun y => continuous_id.inner continuous_const) (fun x => continuous_const.inner …`. Establish `hI : (Matrix.of fun i j => ⟪EuclideanSpace.basisFun (Fin (Module.finrank ℝ Kr)) ℝ i, EuclideanSpace.basisFun (Fin (Module.finrank ℝ Kr)) ℝ j⟫) = 1`.

Use extensionality with `i j`. Rewrite using `[Matrix.of_apply, orthonormal_iff_ite.1 (EuclideanSpace.basisFun _ ℝ).orthonormal i j, Matrix.one_apply]`. Rewrite `hd` using `[hI, Matrix.det_one, abs_one, Real.sqrt_one, ENNReal.ofReal_one, one_smul]`. Use `⟨Fin (Module.finrank ℝ Kr), inferInstance, Hh, Tc, ?_, ?_, ?_, fun S T => by rw [hTc, hTc, hTc, TcF_add], fun S v => by rw [hTc, hHT], hd⟩` and prove the remaining obligations. Introduce `s v`.

Take `⟨M, hM, hMs⟩` from `Submodule.mem_map.1 (bK.repr.symm s).2`. Establish `: Hh s = M`. Rewrite using `[hHh, ← hMs]`. Conclude with `(reimVE : _ ≃ₗ[ℝ] _).symm_apply_apply M`. Rewrite using `[this]`.

Conclude with `hM v`. Introduce `s`. Rewrite using `[← norm_reimV_sq, ← reimVE_apply, hHh, LinearEquiv.apply_symm_apply]`. Conclude with `congrArg (· ^ 2) (bK.repr.symm.norm_map s)`. Introduce `M hM`.

Use `⟨bK.repr ⟨(reimVE : _ ≃ₗ[ℝ] _) M, Submodule.mem_map_of_mem (show M ∈ hermFam _ _ from hM)⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hHh, LinearIsometryEquiv.symm_apply_apply]`. Conclude with `(reimVE : _ ≃ₗ[ℝ] _).symm_apply_apply M`.
-/
theorem nuBridge : NuBridge := by
  classical
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) := ⟨rfl⟩
  let Kr : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace X.B.I.F × Fin (D.R.rS + 1 + D.R.rS) ×
      Fin (D.R.rS + 1 + D.R.rS) × Bool)) :=
    (hermFam (InfinitePlace X.B.I.F) (D.R.rS + 1 + D.R.rS)).map (reimVE : _ ≃ₗ[ℝ] _).toLinearMap
  let bK := stdOrthonormalBasis ℝ Kr
  let Hh : EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)) →ₗ[ℝ]
      (InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ) :=
    (reimVE : _ ≃ₗ[ℝ] _).symm.toLinearMap ∘ₗ Kr.subtype ∘ₗ bK.repr.symm.toLinearEquiv.toLinearMap
  have hHh : ∀ s, Hh s = (reimVE : _ ≃ₗ[ℝ] _).symm (bK.repr.symm s : _) := fun s => rfl
  let thH : HmI X → InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ :=
    fun S v => S.1.map (PI.AprimeInfU.thetaInf X v)
  have thH_herm : ∀ S, thH S ∈ hermFam (InfinitePlace X.B.I.F) (D.R.rS + 1 + D.R.rS) := by
    intro S v
    have hS : ∀ a b, sigR (Ainf X.B.I.F) X.B.I.cm.sig (S.1 b a) = S.1 a b := S.2
    ext i j
    simp only [thH, Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [show star (PI.AprimeInfU.thetaInf X v (S.1 j i)) =
      conj (PI.AprimeInfU.thetaInf X v (S.1 j i)) from rfl, ← NuB.theta_sigR X v, hS i j]
  have memK : ∀ S, (reimVE : _ ≃ₗ[ℝ] _) (thH S) ∈ Kr := fun S => Submodule.mem_map_of_mem (thH_herm S)
  let TcF : HmI X → EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)) := fun S => bK.repr ⟨_, memK S⟩
  have hHT : ∀ S, Hh (TcF S) = thH S := by
    intro S
    rw [hHh, LinearIsometryEquiv.symm_apply_apply]
    exact (reimVE : _ ≃ₗ[ℝ] _).symm_apply_apply (thH S)
  have thH_add : ∀ S T, thH (S + T) = thH S + thH T := by
    intro S T
    funext v i j
    simp [thH, Matrix.map_apply, map_add]
  have TcF_add : ∀ S T, TcF (S + T) = TcF S + TcF T := by
    intro S T
    have e : (⟨_, memK (S + T)⟩ : Kr) = ⟨_, memK S⟩ + ⟨_, memK T⟩ := Subtype.ext (by
      show (reimVE : _ ≃ₗ[ℝ] _) (thH (S + T)) = (reimVE : _ ≃ₗ[ℝ] _) (thH S) + (reimVE : _ ≃ₗ[ℝ] _) (thH T)
      rw [thH_add, map_add])
    exact (congrArg bK.repr e).trans (map_add bK.repr _ _)
  have hθc : ∀ v i j, Continuous fun S : HmI X => PI.AprimeInfU.thetaInf X v (S.1 i j) :=
    fun v i j => (continuous_thetaInf X v).comp (continuous_subtype_val.matrix_elem i j)
  have hcont : Continuous TcF := by
    refine bK.repr.continuous.comp (Continuous.subtype_mk ?_ _)
    show Continuous fun S => (EuclideanSpace.equiv _ ℝ).symm (fun p : InfinitePlace X.B.I.F × Fin (D.R.rS + 1 + D.R.rS) ×
      Fin (D.R.rS + 1 + D.R.rS) × Bool => if p.2.2.2 then (thH S p.1 p.2.1 p.2.2.1).re else (thH S p.1 p.2.1 p.2.2.1).im)
    refine (EuclideanSpace.equiv _ ℝ).symm.continuous.comp (continuous_pi fun p => ?_)
    rcases p with ⟨v, i, j, s⟩
    cases s
    · exact Complex.continuous_im.comp (hθc v i j)
    · exact Complex.continuous_re.comp (hθc v i j)
  have hinj : Function.Injective TcF := by
    intro S T h
    have h1 : thH S = thH T := by rw [← hHT S, ← hHT T, h]
    apply Subtype.ext
    ext a b
    apply sub_eq_zero.1
    apply thetaInf_inj X
    intro v
    have := congrFun (congrFun (congrFun h1 v) a) b
    simp only [thH, Matrix.map_apply] at this
    rw [map_sub, this, sub_self]
  have hsurj : Function.Surjective TcF := by
    intro s
    obtain ⟨M, hM, hMs⟩ := Submodule.mem_map.1 (bK.repr.symm s).2
    choose y hy using fun a b : Fin (D.R.rS + 1 + D.R.rS) => NuB.theta_surj X (fun v => M v a b)
    let h2 := algebraMap X.B.I.F (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) (1 / 2)
    let Sm : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
      fun a b => h2 * (y a b + sigR (Ainf X.B.I.F) X.B.I.cm.sig (y b a))
    have hSm : Sm ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) := by
      show ∀ a b, sigR (Ainf X.B.I.F) X.B.I.cm.sig (Sm b a) = Sm a b
      intro a b
      simp only [Sm, h2, map_mul, map_add, sigR_invP _ _ (sig_invI X), sigR_alg]
      ring
    refine ⟨⟨Sm, hSm⟩, ?_⟩
    have e : thH ⟨Sm, hSm⟩ = M := by
      funext v a b
      have hMh : conj (M v b a) = M v a b := by
        have := congrFun (congrFun (hM v) a) b
        simpa [Matrix.conjTranspose_apply] using this
      simp only [thH, Matrix.map_apply, Sm, h2, map_mul, map_add, NuB.theta_alg, NuB.theta_sigR, hy, hMh,
        half_emb]
      ring
    show bK.repr _ = s
    rw [← bK.repr.apply_symm_apply s]
    congr 1
    apply Subtype.ext
    show (reimVE : _ ≃ₗ[ℝ] _) (thH ⟨Sm, hSm⟩) = _
    rw [e]
    exact hMs
  let Ψa : Wh X →+ EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)) :=
    AddMonoidHom.mk' (fun x => TcF ((hermCoord X).symm x)) (fun x y => by rw [hermCoord_symm_add, TcF_add])
  let Ψc : Wh X →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)) :=
    AddMonoidHom.toRealLinearMap Ψa (hcont.comp (hermCoord X).symm.continuous)
  have hΨ : ∀ x, Ψc x = TcF ((hermCoord X).symm x) := fun x => rfl
  have hΨb : Function.Bijective Ψc := by
    refine ⟨fun x y h => (hermCoord X).symm.injective (hinj (by rw [← hΨ, ← hΨ, h])), fun s => ?_⟩
    obtain ⟨S, hS⟩ := hsurj s
    exact ⟨hermCoord X S, by rw [hΨ, Homeomorph.symm_apply_apply, hS]⟩
  let Ψe : Wh X ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)) :=
    (LinearEquiv.ofBijective (Ψc : Wh X →ₗ[ℝ] _) hΨb).toContinuousLinearEquiv
  let Tc : HmI X ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)) := (hermCoord X).trans Ψe.toHomeomorph
  have hTc : ∀ S, Tc S = TcF S := by
    intro S
    show Ψc (hermCoord X S) = TcF S
    rw [hΨ, Homeomorph.symm_apply_apply]
  have key : ∀ S T : HmI X, sumReI X (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T) =
      ⟪TcF S, TcF T⟫ := by
    intro S T
    have e1 : ⟪TcF S, TcF T⟫ = ⟪reimV (thH S), reimV (thH T)⟫ := by
      simp only [TcF, LinearIsometryEquiv.inner_map_map]
      rfl
    have hTh : ∀ v a b, PI.AprimeInfU.thetaInf X v (T.1 b a) =
        conj (PI.AprimeInfU.thetaInf X v (T.1 a b)) := by
      intro v a b
      have hT' : ∀ a b, sigR (Ainf X.B.I.F) X.B.I.cm.sig (T.1 b a) = T.1 a b := T.2
      rw [← NuB.theta_sigR X v, hT' b a]
    rw [e1, inner_reimV]
    simp only [sumReI]
    refine Finset.sum_congr rfl fun v _ => ?_
    show (PI.AprimeInfU.evInf X v (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)).re = _
    rw [pairHerm, map_mul, NuB.evInf_alg, NuB.evInf_trace, half_emb, half_re, map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, hTh v a b]
    simp only [thH, Matrix.map_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hS := hP.2.2.1
  have hν : SelfDual νinf (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) =>
      psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)) := hP.2.2.2.2.2.1
  have h1 : ∀ x y : EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)),
      (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) =>
        psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)) (Tc.symm x) (Tc.symm y) =
        ((𝐞 (⟪x, y⟫) : Circle) : ℂ) := by
    intro x y
    obtain ⟨S, rfl⟩ := Tc.surjective x
    obtain ⟨T, rfl⟩ := Tc.surjective y
    have e1 : Tc.symm (Tc S) = S := Tc.symm_apply_apply S
    have e2 : Tc.symm (Tc T) = T := Tc.symm_apply_apply T
    have e3 : ⟪Tc S, Tc T⟫ = sumReI X (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T) := by
      rw [hTc S, hTc T, key]
    show psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) (Tc.symm (Tc S))
      (Tc.symm (Tc T))) = _
    rw [e1, e2, e3]
    simp only [sumReI]
    rw [psiInf_eq ψ hS, Real.fourierChar_apply]
    push_cast
    ring_nf
  have hd := PI.AprimeInfW.GenericDensity.dens_generic νinf _ hν Tc (fun S T => by rw [hTc, hTc, hTc, TcF_add])
    (fun x y => ⟪x, y⟫) h1 (fun x x' y => inner_add_left x x' y) (fun x y y' => inner_add_right x y y')
    (fun y => continuous_id.inner continuous_const) (fun x => continuous_const.inner continuous_id)
    (fun x y => real_inner_comm y x) (EuclideanSpace.basisFun (Fin (Module.finrank ℝ Kr)) ℝ)
  have hI : (Matrix.of fun i j => ⟪EuclideanSpace.basisFun (Fin (Module.finrank ℝ Kr)) ℝ i,
      EuclideanSpace.basisFun (Fin (Module.finrank ℝ Kr)) ℝ j⟫) = 1 := by
    ext i j
    rw [Matrix.of_apply, orthonormal_iff_ite.1 (EuclideanSpace.basisFun _ ℝ).orthonormal i j, Matrix.one_apply]
  rw [hI, Matrix.det_one, abs_one, Real.sqrt_one, ENNReal.ofReal_one, one_smul] at hd
  refine ⟨Fin (Module.finrank ℝ Kr), inferInstance, Hh, Tc, ?_, ?_, ?_, fun S T => by rw [hTc, hTc, hTc, TcF_add],
    fun S v => by rw [hTc, hHT], hd⟩
  · intro s v
    obtain ⟨M, hM, hMs⟩ := Submodule.mem_map.1 (bK.repr.symm s).2
    have : Hh s = M := by
      rw [hHh, ← hMs]
      exact (reimVE : _ ≃ₗ[ℝ] _).symm_apply_apply M
    rw [this]
    exact hM v
  · intro s
    rw [← norm_reimV_sq, ← reimVE_apply, hHh, LinearEquiv.apply_symm_apply]
    exact congrArg (· ^ 2) (bK.repr.symm.norm_map s)
  · intro M hM
    refine ⟨bK.repr ⟨(reimVE : _ ≃ₗ[ℝ] _) M, Submodule.mem_map_of_mem (show M ∈ hermFam _ _ from hM)⟩, ?_⟩
    rw [hHh, LinearIsometryEquiv.symm_apply_apply]
    exact (reimVE : _ ≃ₗ[ℝ] _).symm_apply_apply M

end PI.AprimeInfW
