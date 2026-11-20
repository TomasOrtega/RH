import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommuteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalForallMapMemStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearMapTensorOfPairing

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta GlobalTheory.PairingTensor Matrix

namespace GlobalTheory.InvPairingTensor

variable {p q : ℕ}

/- English proof (translation)
Unfold `Jm Formalism.UG.Jpq`. Use extensionality with `a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp`.
-/
theorem Jm_diag (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  unfold Jm Formalism.UG.Jpq
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, Matrix.diagonal_apply] <;>
    split_ifs <;> simp

/- English proof (translation)
Rewrite using `[Jm_diag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `rcases a with a | a <;> simp`.
-/
theorem Jm_mul_self (p q : ℕ) : Jm p q * Jm p q = 1 := by
  rw [Jm_diag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rcases a with a | a <;> simp

/- English proof (translation)
Establish `hsym : ∀ a b : Ix p q, ¬ sameBlock a b → ¬ sameBlock b a`. Introduce `a b h h'`. Apply `h` to reduce the goal to its premises. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]`. Use `⟨(1 / 2 : ℂ) • (Z - Jm p q * Zᴴ * Jm p q), (-Complex.I / 2) • (Z + Jm p q * Zᴴ * Jm p q), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show _ * _ + _ * _ = 0`. Rewrite using `[Jm_diag]`. Use extensionality with `a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`. Apply the tactic sequence `simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] <;> ring`.

Use `show _ * _ + _ * _ = 0`. Rewrite using `[Jm_diag]`. Use extensionality with `a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`. Apply the tactic sequence `simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] <;> ring`.

Introduce `hZ`. Establish `hZ' : ∀ a b, ¬ sameBlock a b → (Jm p q * Zᴴ * Jm p q) a b = 0`. Introduce `a b hab`. Rewrite using `[Jm_diag, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, hZ b a (hsym a b hab)]`. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Simplify using `[Matrix.sub_apply, hZ a b hab, hZ' a b hab]`. Introduce `a b hab`. Simplify using `[Matrix.add_apply, hZ a b hab, hZ' a b hab]`.

Use extensionality with `a b`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_real_parts (Z : Mat p q) :
    ∃ X Y : Mat p q, X ∈ upq p q ∧ Y ∈ upq p q ∧ (IsKC Z → IsKC X ∧ IsKC Y) ∧
      Z = X + Complex.I • Y := by
  have hsym : ∀ a b : Ix p q, ¬ sameBlock a b → ¬ sameBlock b a := by
    intro a b h h'
    apply h
    rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]
  refine ⟨(1 / 2 : ℂ) • (Z - Jm p q * Zᴴ * Jm p q), (-Complex.I / 2) • (Z + Jm p q * Zᴴ * Jm p q),
    ?_, ?_, ?_, ?_⟩
  · show _ * _ + _ * _ = 0
    rw [Jm_diag]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] <;> ring
  · show _ * _ + _ * _ = 0
    rw [Jm_diag]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] <;> ring
  · intro hZ
    have hZ' : ∀ a b, ¬ sameBlock a b → (Jm p q * Zᴴ * Jm p q) a b = 0 := by
      intro a b hab
      rw [Jm_diag, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
        hZ b a (hsym a b hab)]
      simp
    constructor
    · intro a b hab
      simp [Matrix.sub_apply, hZ a b hab, hZ' a b hab]
    · intro a b hab
      simp [Matrix.add_apply, hZ a b hab, hZ' a b hab]
  · ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring

/- English proof (translation)
Set `L : U.H →ₗᵢ[ℂ] U.H` to `⟨(U.π g).toLinearMap, U.isom g⟩`. Conclude with `L.inner_map_map x y`.
-/
private theorem inner_pi_apply_pi_apply {T : GrpData p q} (U : URep T) (g : T.G) (x y : U.H) :
    inner ℂ (U.π g x) (U.π g y) = inner ℂ x y := by
  let L : U.H →ₗᵢ[ℂ] U.H := ⟨(U.π g).toLinearMap, U.isom g⟩
  exact L.inner_map_map x y

/- English proof (translation)
Establish `hv` using `D.der X hX v`. Establish `hw` using `D.der X hX w`. Establish `h` using `hv.inner ℂ hw`. Establish `hc : (fun t : ℝ => inner ℂ ((D.U.π (T.expt (t • X))) (D.ι v)) ((D.U.π (T.expt (t • X))) (D.ι w))) = fun _ => inner ℂ (D.ι v) (D.ι w)`. Use function extensionality and compare the values at `t`.

Conclude with `inner_pi_apply_pi_apply D.U _ _ _`. Rewrite `h` using `[hc]`. Establish `h0` using `h.unique (hasDerivAt_const (0 : ℝ) (inner ℂ (D.ι v) (D.ι w)))`. Simplify `h0` using `[T.expt_zero]`.
-/
theorem inner_act_skew {T : GrpData p q} (D : DSRep T) {X : Mat p q} (hX : X ∈ upq p q)
    (v w : D.HK.V) :
    inner ℂ (D.ι v) (D.ι (D.HK.act X w)) + inner ℂ (D.ι (D.HK.act X v)) (D.ι w) = 0 := by
  have hv := D.der X hX v
  have hw := D.der X hX w
  have h := hv.inner ℂ hw
  have hc : (fun t : ℝ => inner ℂ ((D.U.π (T.expt (t • X))) (D.ι v))
      ((D.U.π (T.expt (t • X))) (D.ι w))) = fun _ => inner ℂ (D.ι v) (D.ι w) := by
    funext t
    exact inner_pi_apply_pi_apply D.U _ _ _
  rw [hc] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) (inner ℂ (D.ι v) (D.ι w)))
  simpa [T.expt_zero] using h0

section Frame
variable {A H : Type} [AddCommGroup A] [Module ℂ A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Set `F : Submodule ℂ H` to `E.map i`. Set `bF` to `stdOrthonormalBasis ℂ F`. Establish `hb : ∀ j, ∃ a, a ∈ E ∧ i a = (bF j : H)` using `fun j => Submodule.mem_map.mp (bF j).2`. Use `choose a haE hia using hb`. Use `⟨Module.finrank ℂ F, a, haE, fun x hx => ?_⟩` and prove the remaining obligations.

Apply `hi` to reduce the goal to its premises. Establish `hxF : i x ∈ F` using `Submodule.mem_map_of_mem hx`. Establish `key` using `congrArg Subtype.val (bF.sum_repr' (⟨i x, hxF⟩ : F))`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at key`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul, hia]`. Conclude with `key`.
-/
theorem exists_frame (i : A →ₗ[ℂ] H) (hi : Function.Injective i) (E : Submodule ℂ A)
    [FiniteDimensional ℂ E] :
    ∃ (n : ℕ) (a : Fin n → A), (∀ j, a j ∈ E) ∧
      ∀ x ∈ E, ∑ j, inner ℂ (i (a j)) (i x) • a j = x := by
  classical
  let F : Submodule ℂ H := E.map i
  let bF := stdOrthonormalBasis ℂ F
  have hb : ∀ j, ∃ a, a ∈ E ∧ i a = (bF j : H) := fun j =>
    Submodule.mem_map.mp (bF j).2
  choose a haE hia using hb
  refine ⟨Module.finrank ℂ F, a, haE, fun x hx => ?_⟩
  apply hi
  have hxF : i x ∈ F := Submodule.mem_map_of_mem hx
  have key := congrArg Subtype.val (bF.sum_repr' (⟨i x, hxF⟩ : F))
  simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at key
  rw [map_sum]
  simp only [map_smul, hia]
  exact key

end Frame

/- English proof (translation)
Take `⟨⟨W, hWfd, hPW, hWK⟩, -⟩` from `(GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).2 P`. Establish `hwt : ∀ v ∈ W, v ∈ ⨆ μ : Ix r s → ℚ, wtSub (fockAct2 p q r s) μ` using `fun v _ => ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).2 v).2`. Establish `hlie : IsKLieAct (fockAct2 p q r s)`. Unfold `IsKLieAct`. Introduce `Y Z _ _`.

Conclude with `(GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.2.1 Y Z`. Take `⟨E, hEfd, hE⟩` from `GlobalTheory.T.exists_finiteDimensional_forall_map_mem' r s R₂.HK hA (Pol p q r s) (fockAct2 p q r s) hlie W hWfd hWK hwt`. Use `⟨E, hEfd, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `l`.

Take `⟨Y, hYfd, hyY, hYK⟩` from `R₂.HK.kfin y`. Use `haveI := hYfd`. Take `⟨n, b, hbY, hfr⟩` from `exists_frame R₂.ι R₂.ι_inj Y`. Set `φ : Pol p q r s →ₗ[ℂ] R₂.HK.V` to `{ toFun := fun Q => ∑ j, l (B Q (b j)) • b j map_add' := fun Q Q' => by`. Simplify using `only [map_add, LinearMap.add_apply, add_smul, Finset.sum_add_distrib]`.

Use the proof step `map_smul' := fun c Q => by`. Simplify using `only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }`. Establish `hφ : ∀ Q, φ Q = ∑ j, l (B Q (b j)) • b j` using `fun Q => rfl`. Establish `hφY : ∀ Q, φ Q ∈ Y` using `fun Q => by`. Rewrite using `[hφ]`.

Conclude with `Y.sum_mem fun j _ => Y.smul_mem _ (hbY j)`. Establish `hrep : ∀ Q, ∀ z ∈ Y, inner ℂ (R₂.ι z) (R₂.ι (φ Q)) = l (B Q z)`. Introduce `Q z hz`. Use `conv_rhs => rw [← hfr z hz]`. Rewrite using `[hφ]`.

Simplify using `only [map_sum, map_smul, LinearMap.map_smulₛₗ, inner_sum, inner_smul_right, smul_eq_mul, inner_conj_symm]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Establish `hsep : ∀ u ∈ Y, ∀ u' ∈ Y, (∀ z ∈ Y, inner ℂ (R₂.ι z) (R₂.ι u) = inner ℂ (R₂.ι z) (R₂.ι u')) → u = u'`. Introduce `u hu u' hu' h`. Establish `h0` using `h (u - u') (Y.sub_mem hu hu')`.

Rewrite `h0` using `[← sub_eq_zero, ← inner_sub_right, ← map_sub, inner_self_eq_zero, ← map_zero R₂.ι]`. Conclude with `sub_eq_zero.mp (R₂.ι_inj h0)`. Establish `hequ1 : ∀ Z ∈ upq r s, IsKC Z → ∀ Q, φ (fockAct2 p q r s Z Q) = R₂.HK.act Z (φ Q)`. Introduce `Z hZ hKZ Q`. Use `hsep _ (hφY _) _ (hYK Z hKZ _ (hφY Q)) fun z hz => ?_` and prove the remaining obligations.

Rewrite using `[hrep _ z hz, eq_neg_of_add_eq_zero_left (hB Z hZ Q z), map_neg, ← hrep Q _ (hYK Z hKZ z hz)]`. Conclude with `(eq_neg_of_add_eq_zero_left (inner_act_skew R₂ hZ z (φ Q))).symm`. Establish `hequ : ∀ Z, IsKC Z → ∀ Q, φ (fockAct2 p q r s Z Q) = R₂.HK.act Z (φ Q)`. Introduce `Z hKZ Q`. Take `⟨X1, Y1, hX1, hY1, hK, rfl⟩` from `exists_real_parts Z`.

Take `⟨hKX, hKY⟩` from `hK hKZ`. Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hequ1 X1 hX1 hKX, hequ1 Y1 hY1 hKY]`. Establish `hφE : φ P ∈ E` using `hE φ hequ P hPW`. Rewrite using `[← hrep P y hyY]`. Conclude with `hy _ hφE`.
-/
theorem exists_finiteDimensional_kill {r s : ℕ} {T₂ : GrpData r s} (R₂ : DSRep T₂)
    (hA : AdmGK R₂.HK) {N : Type} [AddCommGroup N] [Module ℂ N]
    (B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] N)
    (hB : ∀ Z ∈ upq r s, ∀ P y, B (fockAct2 p q r s Z P) y + B P (R₂.HK.act Z y) = 0)
    (P : Pol p q r s) :
    ∃ E : Submodule ℂ R₂.HK.V, FiniteDimensional ℂ E ∧
      ∀ y, (∀ x ∈ E, inner ℂ (R₂.ι y) (R₂.ι x) = 0) → B P y = 0 := by
  classical
  obtain ⟨⟨W, hWfd, hPW, hWK⟩, -⟩ := (GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).2 P
  have hwt : ∀ v ∈ W, v ∈ ⨆ μ : Ix r s → ℚ, wtSub (fockAct2 p q r s) μ :=
    fun v _ => ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).2 v).2
  have hlie : IsKLieAct (fockAct2 p q r s) := by
    unfold IsKLieAct
    intro Y Z _ _
    exact (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.2.1 Y Z
  obtain ⟨E, hEfd, hE⟩ :=
    GlobalTheory.T.exists_finiteDimensional_forall_map_mem' r s R₂.HK hA (Pol p q r s) (fockAct2 p q r s) hlie W hWfd hWK hwt
  refine ⟨E, hEfd, fun y hy => ?_⟩
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  obtain ⟨Y, hYfd, hyY, hYK⟩ := R₂.HK.kfin y
  haveI := hYfd
  obtain ⟨n, b, hbY, hfr⟩ := exists_frame R₂.ι R₂.ι_inj Y
  let φ : Pol p q r s →ₗ[ℂ] R₂.HK.V :=
    { toFun := fun Q => ∑ j, l (B Q (b j)) • b j
      map_add' := fun Q Q' => by
        simp only [map_add, LinearMap.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c Q => by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
          mul_smul] }
  have hφ : ∀ Q, φ Q = ∑ j, l (B Q (b j)) • b j := fun Q => rfl
  have hφY : ∀ Q, φ Q ∈ Y := fun Q => by
    rw [hφ]
    exact Y.sum_mem fun j _ => Y.smul_mem _ (hbY j)
  have hrep : ∀ Q, ∀ z ∈ Y, inner ℂ (R₂.ι z) (R₂.ι (φ Q)) = l (B Q z) := by
    intro Q z hz
    conv_rhs => rw [← hfr z hz]
    rw [hφ]
    simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, inner_sum, inner_smul_right, smul_eq_mul,
      inner_conj_symm]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hsep : ∀ u ∈ Y, ∀ u' ∈ Y,
      (∀ z ∈ Y, inner ℂ (R₂.ι z) (R₂.ι u) = inner ℂ (R₂.ι z) (R₂.ι u')) → u = u' := by
    intro u hu u' hu' h
    have h0 := h (u - u') (Y.sub_mem hu hu')
    rw [← sub_eq_zero, ← inner_sub_right, ← map_sub, inner_self_eq_zero, ← map_zero R₂.ι] at h0
    exact sub_eq_zero.mp (R₂.ι_inj h0)
  have hequ1 : ∀ Z ∈ upq r s, IsKC Z → ∀ Q, φ (fockAct2 p q r s Z Q) = R₂.HK.act Z (φ Q) := by
    intro Z hZ hKZ Q
    refine hsep _ (hφY _) _ (hYK Z hKZ _ (hφY Q)) fun z hz => ?_
    rw [hrep _ z hz, eq_neg_of_add_eq_zero_left (hB Z hZ Q z), map_neg,
      ← hrep Q _ (hYK Z hKZ z hz)]
    exact (eq_neg_of_add_eq_zero_left (inner_act_skew R₂ hZ z (φ Q))).symm
  have hequ : ∀ Z, IsKC Z → ∀ Q, φ (fockAct2 p q r s Z Q) = R₂.HK.act Z (φ Q) := by
    intro Z hKZ Q
    obtain ⟨X1, Y1, hX1, hY1, hK, rfl⟩ := exists_real_parts Z
    obtain ⟨hKX, hKY⟩ := hK hKZ
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hequ1 X1 hX1 hKX,
      hequ1 Y1 hY1 hKY]
  have hφE : φ P ∈ E := hE φ hequ P hPW
  rw [← hrep P y hyY]
  exact hy _ hφE

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => simp`. Consider the case `add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add]`.
-/
private theorem contrR_map_id {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] (l : B →ₗ[ℂ] ℂ) (b : Module.End ℂ B) (z : TensorProduct ℂ A B) :
    contrR l (TensorProduct.map LinearMap.id b z) = contrR (l ∘ₗ b) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => simp [neg_smul]`. Consider the case `add z z' hz hz' => rw [map_add, map_add, hz, hz', neg_add]`.
-/
private theorem contrR_neg' {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] (l : B →ₗ[ℂ] ℂ) (z : TensorProduct ℂ A B) :
    contrR (-l) z = -contrR l z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [neg_smul]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', neg_add]

/- English proof (translation)
Introduce `p q r s T₂ R₂ hA N _ _ B hB`. Set `m : R₂.HK.V → R₂.HK.V →ₗ[ℂ] ℂ` to `fun y => innerₛₗ ℂ (R₂.ι y) ∘ₗ R₂.ι`. Establish `hm : ∀ y x, m y x = inner ℂ (R₂.ι y) (R₂.ι x)` using `fun _ _ => rfl`. Establish `huniq : ∀ t t' : TensorProduct ℂ N R₂.HK.V, (∀ y, contrR (m y) t = contrR (m y) t') → t = t'`. Introduce `t t' h`.

Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_contrR m (fun x hx => ?_) _ (fun y => ?_)` and prove the remaining obligations. Establish `h1` using `hx x`. Rewrite `h1` using `[hm, inner_self_eq_zero, ← map_zero R₂.ι]`. Conclude with `R₂.ι_inj h1`.

Rewrite using `[map_sub, h y, sub_self]`. Establish `hex : ∀ P, ∃ t : TensorProduct ℂ N R₂.HK.V, ∀ y, B P y = contrR (m y) t`. Introduce `P`. Take `⟨E, hEfd, hE⟩` from `exists_finiteDimensional_kill R₂ hA B hB P`. Use `haveI := hEfd`.

Take `⟨n, a, haE, hfr⟩` from `exists_frame R₂.ι R₂.ι_inj E`. Use `⟨∑ j, B P (a j) ⊗ₜ[ℂ] a j, fun y => ?_⟩` and prove the remaining obligations. Establish `hperp : B P (y - ∑ j, inner ℂ (R₂.ι (a j)) (R₂.ι y) • a j) = 0`. Apply `hE` to reduce the goal to its premises. Introduce `x hx`.

Establish `e1 : inner ℂ (R₂.ι y) (R₂.ι x) = ∑ j, inner ℂ (R₂.ι (a j)) (R₂.ι x) * inner ℂ (R₂.ι y) (R₂.ι (a j))` using `by conv_lhs => rw [← hfr x hx]`. Simplify using `only [map_sum, map_smul, inner_sum, inner_smul_right]`. Rewrite using `[map_sub, inner_sub_left, e1]`. Simplify using `only [map_sum, map_smul, sum_inner, inner_smul_left, inner_conj_symm]`. Rewrite using `[sub_eq_zero]`.

Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Rewrite `hperp` using `[map_sub, sub_eq_zero]`. Rewrite using `[hperp, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, contrR_tmul, hm, inner_conj_symm]`.

Use `choose F hF using hex`. Establish `hadd : ∀ P Q, F (P + Q) = F P + F Q` using `fun P Q => huniq _ _ fun y => by`. Rewrite using `[map_add, ← hF, ← hF, ← hF, map_add, LinearMap.add_apply]`. Establish `hsmul : ∀ (c : ℂ) P, F (c • P) = c • F P` using `fun c P => huniq _ _ fun y => by`. Rewrite using `[map_smul, ← hF, ← hF, map_smul, LinearMap.smul_apply]`.

Set `f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ N R₂.HK.V` to `{ toFun := F, map_add' := hadd, map_smul' := fun c P => by simpa using hsmul c P }`. Establish `hf : ∀ P, f P = F P` using `fun _ => rfl`. Establish `hupq : ∀ Y ∈ upq r s, ∀ P, F (fockAct2 p q r s Y P) = TensorProduct.map LinearMap.id (R₂.HK.act Y) (F P)`. Introduce `Y hY P`. Use `huniq _ _ fun y => ?_` and prove the remaining obligations.

Rewrite using `[← hF, contrR_map_id]`. Establish `hl : m y ∘ₗ R₂.HK.act Y = -m (R₂.HK.act Y y)`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.neg_apply, hm, hm]`. Conclude with `eq_neg_of_add_eq_zero_left (inner_act_skew R₂ hY y x)`.

Rewrite using `[hl, contrR_neg', ← hF]`. Conclude with `eq_neg_of_add_eq_zero_left (hB Y hY P y)`. Use `⟨f, fun Y => ?_, fun P y => hF P y, fun c a hca => ?_⟩` and prove the remaining obligations. Take `⟨X1, Y1, hX1, hY1, -, hY⟩` from `exists_real_parts Y`. Use `LinearMap.ext fun P => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hf, hf, hY, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hadd, hsmul, hupq X1 hX1, hupq Y1 hY1, map_add, map_smul, TensorProduct.map_add_right, TensorProduct.map_smul_right, LinearMap.add_apply, LinearMap.smul_apply]`. Use `LinearMap.ext fun P => huniq _ _ fun y => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hf, hf, ← hF, contrR_map, ← hF, hca]`.
-/
theorem exists_tensor_map : ∀ (p q r s : ℕ) (T₂ : GrpData r s) (R₂ : DSRep T₂), AdmGK R₂.HK → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] N), (∀ Z ∈ upq r s, ∀ P y, B (fockAct2 p q r s Z P) y + B P (R₂.HK.act Z y) = 0) → ∃ f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ N R₂.HK.V, (∀ Y, f ∘ₗ fockAct2 p q r s Y = TensorProduct.map LinearMap.id (R₂.HK.act Y) ∘ₗ f) ∧ (∀ P y, B P y = TensorProduct.rid ℂ N (TensorProduct.map LinearMap.id (innerₛₗ ℂ (R₂.ι y) ∘ₗ R₂.ι) (f P))) ∧ ∀ (c : Module.End ℂ (Pol p q r s)) (a : Module.End ℂ N), (∀ P y, B (c P) y = a (B P y)) → f ∘ₗ c = TensorProduct.map a LinearMap.id ∘ₗ f := by
  intro p q r s T₂ R₂ hA N _ _ B hB
  classical
  let m : R₂.HK.V → R₂.HK.V →ₗ[ℂ] ℂ := fun y => innerₛₗ ℂ (R₂.ι y) ∘ₗ R₂.ι
  have hm : ∀ y x, m y x = inner ℂ (R₂.ι y) (R₂.ι x) := fun _ _ => rfl
  have huniq : ∀ t t' : TensorProduct ℂ N R₂.HK.V,
      (∀ y, contrR (m y) t = contrR (m y) t') → t = t' := by
    intro t t' h
    rw [← sub_eq_zero]
    refine eq_zero_of_contrR m (fun x hx => ?_) _ (fun y => ?_)
    · have h1 := hx x
      rw [hm, inner_self_eq_zero, ← map_zero R₂.ι] at h1
      exact R₂.ι_inj h1
    · rw [map_sub, h y, sub_self]
  have hex : ∀ P, ∃ t : TensorProduct ℂ N R₂.HK.V, ∀ y, B P y = contrR (m y) t := by
    intro P
    obtain ⟨E, hEfd, hE⟩ := exists_finiteDimensional_kill R₂ hA B hB P
    haveI := hEfd
    obtain ⟨n, a, haE, hfr⟩ := exists_frame R₂.ι R₂.ι_inj E
    refine ⟨∑ j, B P (a j) ⊗ₜ[ℂ] a j, fun y => ?_⟩
    have hperp : B P (y - ∑ j, inner ℂ (R₂.ι (a j)) (R₂.ι y) • a j) = 0 := by
      apply hE
      intro x hx
      have e1 : inner ℂ (R₂.ι y) (R₂.ι x) =
          ∑ j, inner ℂ (R₂.ι (a j)) (R₂.ι x) * inner ℂ (R₂.ι y) (R₂.ι (a j)) := by
        conv_lhs => rw [← hfr x hx]
        simp only [map_sum, map_smul, inner_sum, inner_smul_right]
      rw [map_sub, inner_sub_left, e1]
      simp only [map_sum, map_smul, sum_inner, inner_smul_left, inner_conj_symm]
      rw [sub_eq_zero]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [map_sub, sub_eq_zero] at hperp
    rw [hperp, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smulₛₗ, contrR_tmul, hm, inner_conj_symm]
  choose F hF using hex
  have hadd : ∀ P Q, F (P + Q) = F P + F Q := fun P Q => huniq _ _ fun y => by
    rw [map_add, ← hF, ← hF, ← hF, map_add, LinearMap.add_apply]
  have hsmul : ∀ (c : ℂ) P, F (c • P) = c • F P := fun c P => huniq _ _ fun y => by
    rw [map_smul, ← hF, ← hF, map_smul, LinearMap.smul_apply]
  let f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ N R₂.HK.V :=
    { toFun := F, map_add' := hadd, map_smul' := fun c P => by simpa using hsmul c P }
  have hf : ∀ P, f P = F P := fun _ => rfl
  have hupq : ∀ Y ∈ upq r s, ∀ P,
      F (fockAct2 p q r s Y P) = TensorProduct.map LinearMap.id (R₂.HK.act Y) (F P) := by
    intro Y hY P
    refine huniq _ _ fun y => ?_
    rw [← hF, contrR_map_id]
    have hl : m y ∘ₗ R₂.HK.act Y = -m (R₂.HK.act Y y) := by
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.comp_apply, LinearMap.neg_apply, hm, hm]
      exact eq_neg_of_add_eq_zero_left (inner_act_skew R₂ hY y x)
    rw [hl, contrR_neg', ← hF]
    exact eq_neg_of_add_eq_zero_left (hB Y hY P y)
  refine ⟨f, fun Y => ?_, fun P y => hF P y, fun c a hca => ?_⟩
  · obtain ⟨X1, Y1, hX1, hY1, -, hY⟩ := exists_real_parts Y
    refine LinearMap.ext fun P => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hf, hf, hY, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, hadd, hsmul, hupq X1 hX1, hupq Y1 hY1, map_add,
      map_smul, TensorProduct.map_add_right, TensorProduct.map_smul_right, LinearMap.add_apply,
      LinearMap.smul_apply]
  · refine LinearMap.ext fun P => huniq _ _ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hf, hf, ← hF, contrR_map, ← hF, hca]

end GlobalTheory.InvPairingTensor
