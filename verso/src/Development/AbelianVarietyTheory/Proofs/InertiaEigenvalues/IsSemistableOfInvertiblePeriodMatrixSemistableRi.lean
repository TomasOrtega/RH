import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodRingGaloisInvariantsIffConstStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

open Matrix

/- English proof (translation)
Introduce `l _ P AI T n _ _ K V _ _ b ρ Q hQ`. Use `haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K`. Use `haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := haveI := K.2 FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))`. Choose the witnesses or unpack the hypotheses as in `⟨crd, hcrd⟩ : ∃ crd : V ⊗[ℚ_[l]] Bst P ≃ₗ[ℚ_[l]] (n → Bst P), ∀ v c, crd (v ⊗ₜ c) = fun i => b.repr v i • c := by`. Use `⟨(TensorProduct.congr b.equivFun (LinearEquiv.refl _ _)) ≪≫ₗ TensorProduct.comm _ _ _ ≪≫ₗ TensorProduct.piScalarRight ℚ_[l] ℚ_[l] (Bst P) n, fun v c => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Take `⟨ι, hι⟩ : ∃ ι : ↥(K0 K) →ₗ[ℚ_[l]] Bst P, ∀ c, ι c = Polynomial.C (algebraMap ↥(K0 K) P.R.B c)` from `⟨(Polynomial.CAlgHom.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B)).toLinearMap, fun _ => rfl⟩`. Use `set M : ↥(GK K) → Matrix n n (Bst P) := fun g => (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] (Bst P)) with hM`. Establish `hact : ∀ g x, crd (stRep P ρ g x) = M g *ᵥ (fun i => actSt P (g : GQ l) (crd x i))`.

Introduce `g x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero`. Use function extensionality and compare the values at `i`. Simplify using `only [map_zero, Pi.zero_apply]`.

Rewrite using `[show (fun _ : n => (0 : Bst P)) = 0 from rfl, Matrix.mulVec_zero, Pi.zero_apply]`. Consider the case `tmul v c`. Use function extensionality and compare the values at `i`. Rewrite using `[stRep_tmul, hcrd, hcrd, ← LinearMap.toMatrix_mulVec_repr b b (ρ g) v]`. Simplify using `only [hM, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, map_mul, AlgHom.commutes, map_sum, Finset.sum_mul, mul_assoc]`.

Consider the case `add x y hx hy`. Rewrite using `[map_add, map_add, hx, hy, ← Matrix.mulVec_add]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[map_add]`.

Establish `hmv : ∀ (g : ↥(GK K)) (w : n → Bst P), (fun i => actSt P (g : GQ l) (((Q : Matrix n n (Bst P)) *ᵥ w) i)) = (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) *ᵥ (fun i => actSt P (g : GQ l) (w i))`. Introduce `g w`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec ((actSt P (g : GQ l)) : Bst P →+* Bst P) _ w i`. Establish `hQinv : ∀ w : n → Bst P, ((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ ((Q : Matrix n n (Bst P)) *ᵥ w) = w`.

Introduce `w`. Rewrite using `[Matrix.mulVec_mulVec, Q.inv_mul, Matrix.one_mulVec]`. Establish `hQinv' : ∀ w : n → Bst P, (Q : Matrix n n (Bst P)) *ᵥ (((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ w) = w`. Introduce `w`. Rewrite using `[Matrix.mulVec_mulVec, Q.mul_inv, Matrix.one_mulVec]`.

Set `f : (n → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P` to `crd.symm.toLinearMap ∘ₗ (((Q : Matrix n n (Bst P)).mulVecLin).restrictScalars ℚ_[l]) ∘ₗ LinearMap.compLeft ι n`. Establish `hf : ∀ c, crd (f c) = (Q : Matrix n n (Bst P)) *ᵥ (fun i => ι (c i))`. Introduce `c`. Simplify using `[f, LinearMap.compLeft]`. Both sides reduce to the same expression.

Establish `hinj : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `c hc`. Establish `h1 : (fun i => ι (c i)) = 0`. Use `hf c` as an intermediate fact.

Rewrite `this` using `[hc, map_zero]`. Rewrite using `[← hQinv (fun i => ι (c i)), ← this, Matrix.mulVec_zero]`. Use function extensionality and compare the values at `i`. Establish `h2` using `congrFun h1 i`. Rewrite `h2` using `[hι, Pi.zero_apply, Polynomial.C_eq_zero]`.

Conclude with `(algebraMap ↥(K0 K) P.R.B).injective (h2.trans (map_zero _).symm)`. Establish `hrange : LinearMap.range f = Dst P ρ`. Use extensionality with `x`. Rewrite using `[mem_Dst, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, rfl⟩ g`. Apply `crd.injective` to reduce the goal to its premises. Rewrite using `[hact, hf, hmv, Matrix.mulVec_mulVec, hQ g]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `((GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const l P AI T K (ι (c i))).mpr ⟨c i, hι _⟩) g`. Introduce `hx set z := ((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ crd x with hz`. Establish `hy : crd x = (Q : Matrix n n (Bst P)) *ᵥ z` using `(hQinv' _).symm`. Establish `hinv : ∀ i g, actSt P ((g : ↥(GK K)) : GQ l) (z i) = z i`. Introduce `i g`.

Establish `h1` using `congrArg crd (hx g)`. Rewrite `h1` using `[hact, hy, hmv, Matrix.mulVec_mulVec, hQ g]`. Establish `h2` using `congrArg (fun w => ((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ w) h1`. Simplify using `only [hQinv] at h2`. Conclude with `congrFun h2 i`.

Use `choose c hc using fun i => (GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const l P AI T K (z i)).mp (hinv i)`. Use `⟨c, crd.injective ?_⟩` and prove the remaining obligations. Rewrite using `[hf, hy]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[hι, hc i]`. Unfold `IsSst`. Rewrite using `[← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, Module.finrank_eq_card_basis b, mul_comm]`.
-/
theorem isSst_of_periodMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (Q : GL n (Bst P)),
    (∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] (Bst P)) *
      (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) → IsSst P ρ := by
  intro l _ P AI T n _ _ K V _ _ b ρ Q hQ
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    haveI := K.2
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  obtain ⟨crd, hcrd⟩ : ∃ crd : V ⊗[ℚ_[l]] Bst P ≃ₗ[ℚ_[l]] (n → Bst P),
      ∀ v c, crd (v ⊗ₜ c) = fun i => b.repr v i • c := by
    refine ⟨(TensorProduct.congr b.equivFun (LinearEquiv.refl _ _)) ≪≫ₗ TensorProduct.comm _ _ _ ≪≫ₗ
      TensorProduct.piScalarRight ℚ_[l] ℚ_[l] (Bst P) n, fun v c => ?_⟩
    funext i
    simp
  obtain ⟨ι, hι⟩ : ∃ ι : ↥(K0 K) →ₗ[ℚ_[l]] Bst P, ∀ c, ι c = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) :=
    ⟨(Polynomial.CAlgHom.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B)).toLinearMap, fun _ => rfl⟩
  set M : ↥(GK K) → Matrix n n (Bst P) := fun g => (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] (Bst P))
    with hM

  have hact : ∀ g x, crd (stRep P ρ g x) = M g *ᵥ (fun i => actSt P (g : GQ l) (crd x i)) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero =>
      funext i
      simp only [map_zero, Pi.zero_apply]
      rw [show (fun _ : n => (0 : Bst P)) = 0 from rfl, Matrix.mulVec_zero, Pi.zero_apply]
    | tmul v c =>
      funext i
      rw [stRep_tmul, hcrd, hcrd, ← LinearMap.toMatrix_mulVec_repr b b (ρ g) v]
      simp only [hM, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, map_mul, AlgHom.commutes,
        map_sum, Finset.sum_mul, mul_assoc]
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, ← Matrix.mulVec_add]
      congr 1
      funext i
      simp [map_add]

  have hmv : ∀ (g : ↥(GK K)) (w : n → Bst P),
      (fun i => actSt P (g : GQ l) (((Q : Matrix n n (Bst P)) *ᵥ w) i)) =
        (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) *ᵥ (fun i => actSt P (g : GQ l) (w i)) := by
    intro g w
    funext i
    exact RingHom.map_mulVec ((actSt P (g : GQ l)) : Bst P →+* Bst P) _ w i
  have hQinv : ∀ w : n → Bst P, ((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ ((Q : Matrix n n (Bst P)) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, Q.inv_mul, Matrix.one_mulVec]
  have hQinv' : ∀ w : n → Bst P, (Q : Matrix n n (Bst P)) *ᵥ (((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, Q.mul_inv, Matrix.one_mulVec]
  let f : (n → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P :=
    crd.symm.toLinearMap ∘ₗ (((Q : Matrix n n (Bst P)).mulVecLin).restrictScalars ℚ_[l]) ∘ₗ LinearMap.compLeft ι n
  have hf : ∀ c, crd (f c) = (Q : Matrix n n (Bst P)) *ᵥ (fun i => ι (c i)) := by
    intro c
    simp [f, LinearMap.compLeft]
    rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h1 : (fun i => ι (c i)) = 0 := by
      have := hf c
      rw [hc, map_zero] at this
      rw [← hQinv (fun i => ι (c i)), ← this, Matrix.mulVec_zero]
    funext i
    have h2 := congrFun h1 i
    rw [hι, Pi.zero_apply, Polynomial.C_eq_zero] at h2
    exact (algebraMap ↥(K0 K) P.R.B).injective (h2.trans (map_zero _).symm)
  have hrange : LinearMap.range f = Dst P ρ := by
    ext x
    rw [mem_Dst, LinearMap.mem_range]
    constructor
    · rintro ⟨c, rfl⟩ g
      apply crd.injective
      rw [hact, hf, hmv, Matrix.mulVec_mulVec, hQ g]
      congr 1
      funext i
      exact ((GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const l P AI T K (ι (c i))).mpr ⟨c i, hι _⟩) g
    · intro hx
      set z := ((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ crd x with hz
      have hy : crd x = (Q : Matrix n n (Bst P)) *ᵥ z := (hQinv' _).symm
      have hinv : ∀ i g, actSt P ((g : ↥(GK K)) : GQ l) (z i) = z i := by
        intro i g
        have h1 := congrArg crd (hx g)
        rw [hact, hy, hmv, Matrix.mulVec_mulVec, hQ g] at h1
        have h2 := congrArg (fun w => ((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ w) h1
        simp only [hQinv] at h2
        exact congrFun h2 i
      choose c hc using fun i => (GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const l P AI T K (z i)).mp (hinv i)
      refine ⟨c, crd.injective ?_⟩
      rw [hf, hy]
      congr 1
      funext i
      rw [hι, hc i]
  unfold IsSst
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Module.finrank_eq_card_basis b, mul_comm]

end GlobalTheory.PMon
