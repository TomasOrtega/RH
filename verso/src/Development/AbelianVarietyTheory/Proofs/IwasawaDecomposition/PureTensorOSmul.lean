import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtremalUnitVectorSameHighestImageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinorProductTorusWeightBlockTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothVectorsIsKStableStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsInjectiveNonzeroVacuumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitutStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchrodingerIntertwinerInjectiveSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLiftStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IoExtremal

variable {D : D7}

/- English proof (translation)
Take `⟨hv, e, he, ⟨Tm, hTm⟩, hall⟩` from `h`. Establish `h0 : f₀ ≠ 0`. Introduce and unpack `rfl`. Take `⟨⟨p, hp⟩, h2⟩` from `hv.2.norm`. Use `h2 p hp` as an intermediate fact.

Simplify using `[nrm2] at this`. Establish `ho` using `GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he`. Establish `hinf` using `ho.conj.infPart_eq`. Rewrite using `[hall Tm hTm]`. Take `⟨x, h1, h2, h3⟩` from `GlobalTheory.T.exists_nonvanishing_finite_datum_definite_lift D S T βS βT Pg Q _ ξ e hr he (fun PP h => Finset.mem_union_left _ h) fun PP h => Finset.mem_union_right _ h`.

Use `GlobalTheory.T.schrodingerIntertwiner_injective_schwartzBruhat D ψ S T ΛS ΛT _ f₀ _ Tm hv.1 hS hT ho.conj.idem (by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, he.2]) hinf hTm h0 (GlobalTheory.PlaceVec.isSBHalf_of_red hS.1 hT.1 hinf (frMapAdj S T βS βT) (GlobalTheory.PlaceVec. …` and prove the remaining obligations. Rewrite using `[GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP), GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)])`. Use `fun hz => h3 ?_`. Use `congrFun hz x` as an intermediate fact. Rewrite `this` using `[if_pos ⟨h1, h2⟩]`. Then use the resulting hypothesis.
-/
theorem thPVec_ne_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {Pg Q : Finset (Pl D.host.E)}
    {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hr : T.rank ≤ S.rank) (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) : f ≠ 0 := by
  classical
  obtain ⟨hv, e, he, ⟨Tm, hTm⟩, hall⟩ := h
  have h0 : f₀ ≠ 0 := by
    rintro rfl
    obtain ⟨⟨p, hp⟩, h2⟩ := hv.2.norm
    have := h2 p hp
    simp [nrm2] at this
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hinf := ho.conj.infPart_eq
  rw [hall Tm hTm]
  obtain ⟨x, h1, h2, h3⟩ := GlobalTheory.T.exists_nonvanishing_finite_datum_definite_lift D S T βS βT Pg Q _ ξ e hr he (fun PP h => Finset.mem_union_left _ h)
    fun PP h => Finset.mem_union_right _ h
  refine GlobalTheory.T.schrodingerIntertwiner_injective_schwartzBruhat D ψ S T ΛS ΛT _ f₀ _ Tm hv.1 hS hT ho.conj.idem
    (by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, he.2]) hinf hTm h0
    (GlobalTheory.PlaceVec.isSBHalf_of_red hS.1 hT.1 hinf (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)
      (GlobalTheory.PlaceVec.frMapAdj_up S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_down S T βS βT) (Pg ∪ Q)
      (fun y => omegaK Pg y * omegaQ Q T.rank ξ (-1) y) fun y y' h => by
        rw [GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
          GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)])
    fun hz => h3 ?_
  have := congrFun hz x
  rwa [if_pos ⟨h1, h2⟩] at this

abbrev sub {m n : ℕ} (c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : PolF D m n →ₐ[ℂ] PolF D m n :=
  MvPolynomial.aeval fun v : FVar D m n => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : PolF D m n)

/- English proof (translation)
Proceed by induction on `y using MvPolynomial.induction_on' with`. Consider the case `monomial k c`. Establish `: MvPolynomial.aeval (fun v => t v • (MvPolynomial.X v : MvPolynomial ι ℂ)) (MvPolynomial.monomial k c) = MvPolynomial.monomial k ((k.prod fun v k => t v ^ k) * c)`. Rewrite using `[MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]`. Simplify using `only [MvPolynomial.smul_eq_C_mul, mul_pow, Finsupp.prod_mul, map_mul, map_finsuppProd, map_pow, MvPolynomial.algebraMap_eq]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]`. Use `split_ifs with h`. Rewrite using `[h]`. Rewrite using `[mul_zero]`.

Consider the case `add p q hp hq => rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]`.
-/
theorem coeff_scale {ι : Type} (t : ι → ℂ) (s : ι →₀ ℕ) (y : MvPolynomial ι ℂ) :
    MvPolynomial.coeff s (MvPolynomial.aeval (fun v => t v • (MvPolynomial.X v : MvPolynomial ι ℂ)) y) =
      (s.prod fun v k => t v ^ k) * MvPolynomial.coeff s y := by
  classical
  induction y using MvPolynomial.induction_on' with
  | monomial k c =>
    have : MvPolynomial.aeval (fun v => t v • (MvPolynomial.X v : MvPolynomial ι ℂ)) (MvPolynomial.monomial k c) =
        MvPolynomial.monomial k ((k.prod fun v k => t v ^ k) * c) := by
      rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
      simp only [MvPolynomial.smul_eq_C_mul, mul_pow, Finsupp.prod_mul, map_mul, map_finsuppProd, map_pow,
        MvPolynomial.algebraMap_eq]
      ring
    rw [this, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]
  | add p q hp hq => rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hd : a - b ≠ 0` using `sub_ne_zero.2 hne`. Establish `h1` using `h (Real.pi / (a - b))`. Establish `e : Real.pi / (a - b) * a = Real.pi / (a - b) * b + Real.pi` using `by field_simp; ring`. Rewrite `h1` using `[e, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]`.

Establish `h2` using `Complex.exp_ne_zero (((Real.pi / (a - b) * b : ℝ) : ℂ) * Complex.I)`. Apply `h2` to reduce the goal to its premises. Take the linear combination `(-1 / 2) * h1`.
-/
theorem eq_of_exp_eq {a b : ℝ} (h : ∀ s : ℝ, Complex.exp (((s * a : ℝ) : ℂ) * Complex.I) =
    Complex.exp (((s * b : ℝ) : ℂ) * Complex.I)) : a = b := by
  by_contra hne
  have hd : a - b ≠ 0 := sub_ne_zero.2 hne
  have h1 := h (Real.pi / (a - b))
  have e : Real.pi / (a - b) * a = Real.pi / (a - b) * b + Real.pi := by field_simp; ring
  rw [e, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I] at h1
  have h2 := Complex.exp_ne_zero (((Real.pi / (a - b) * b : ℝ) : ℂ) * Complex.I)
  apply h2
  linear_combination (-1 / 2) * h1

def tw {m : ℕ} (ε : Fin m → Bool) (k : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun b a => if ε a then k b a else starRingEnd ℂ (k b a)

/- English proof (translation)
Use extensionality with `b a`. Simplify using `only [tw, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem tw_one {m : ℕ} (ε : Fin m → Bool) : tw ε 1 = 1 := by
  ext b a
  simp only [tw, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `b a`. Simplify using `only [tw, diagonal_apply]`. Apply the tactic sequence `split_ifs with h1 h2 h3 h4 h5 <;> simp_all [← Complex.exp_conj]`.
-/
theorem tw_diag {m : ℕ} (ε : Fin m → Bool) (t : Fin m → ℝ) :
    tw ε (diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) =
      diagonal fun a => Complex.exp ((((if ε a then 1 else -1) * t a : ℝ) : ℂ) * Complex.I) := by
  ext b a
  simp only [tw, diagonal_apply]
  split_ifs with h1 h2 h3 h4 h5 <;> simp_all [← Complex.exp_conj]

/- English proof (translation)
Establish `h` using `congrFun (congrFun hk.2 b) a`. Establish `e1 : ε a = false` using `by simp [hε, ha]`. Establish `e2 : ε b = true` using `by simp [hε, hb]`. Simplify using `only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul, e1, e2] at h`. Establish `: k b a = 0`.

Simplify using `only [Bool.false_eq_true, if_false, if_true] at h`. Take the linear combination `(-1 / 2) * h`. Simplify using `[tw, this]`.
-/
theorem tw_block {m p : ℕ} {ε : Fin m → Bool} (hε : ∀ a, ε a = decide ((a : ℕ) < p)) {k : Matrix (Fin m) (Fin m) ℂ}
    (hk : k ∈ Formalism.REAL.Kset ε) (a b : Fin m) (hb : (b : ℕ) < p) (ha : p ≤ (a : ℕ)) : tw ε k b a = 0 := by
  have h := congrFun (congrFun hk.2 b) a
  have e1 : ε a = false := by simp [hε, ha]
  have e2 : ε b = true := by simp [hε, hb]
  simp only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul, e1, e2] at h
  have : k b a = 0 := by
    simp only [Bool.false_eq_true, if_false, if_true] at h
    linear_combination (-1 / 2) * h
  simp [tw, this]

/- English proof (translation)
Establish `h : pureTensorL A (c • f) = c • pureTensorL A f`. Use `(MvPolynomial.basisMonomials ι ℂ).ext fun k => ?_` and prove the remaining obligations. Unfold `pureTensorL`. Rewrite using `[LinearMap.smul_apply, Module.Basis.constr_basis, Module.Basis.constr_basis]`. Unfold `opPow`.

Proceed by induction on `(Multiset.toList (Finsupp.toMultiset k)) with`. Consider the case `nil => rfl`. Consider the case `cons a l ih => rw [List.foldr_cons, List.foldr_cons, ih, hA]`. Rewrite using `[h, LinearMap.smul_apply]`.
-/
theorem pureTensorL_smul {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (c : ℂ) (hA : ∀ k g, A k (c • g) = c • A k g)
    (f : X → ℂ) (P : MvPolynomial ι ℂ) : pureTensorL A (c • f) P = c • pureTensorL A f P := by
  have h : pureTensorL A (c • f) = c • pureTensorL A f := by
    refine (MvPolynomial.basisMonomials ι ℂ).ext fun k => ?_
    unfold pureTensorL
    rw [LinearMap.smul_apply, Module.Basis.constr_basis, Module.Basis.constr_basis]
    unfold opPow
    induction (Multiset.toList (Finsupp.toMultiset k)) with
    | nil => rfl
    | cons a l ih => rw [List.foldr_cons, List.foldr_cons, ih, hA]
  rw [h, LinearMap.smul_apply]

/- English proof (translation)
Establish `hd : ∀ τ z (g : WO S T → ℂ), Datum.dRho (heisO ψ S T) θ τ z (c • g) = c • Datum.dRho (heisO ψ S T) θ τ z g`. Introduce `τ z g`. Use function extensionality and compare the values at `x`. Simplify using `only [Datum.dRho, Pi.smul_apply, smul_eq_mul, heisO]`. Rewrite using `[← deriv_const_mul_field]`.

Use `congr 1`. Use function extensionality and compare the values at `t`. Expand and normalize the polynomial expressions, which then agree. Use `pureTensorL_smul _ c (fun k g => ?_) f P` and prove the remaining obligations. Unfold `aPlusAll aPlus crea`.

Rewrite using `[hd, hd, smul_comm Complex.I c, ← smul_sub, smul_comm]`.
-/
theorem pureTensorO_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (c : ℂ) (f : WO S T → ℂ) (P : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  have hd : ∀ τ z (g : WO S T → ℂ), Datum.dRho (heisO ψ S T) θ τ z (c • g) = c • Datum.dRho (heisO ψ S T) θ τ z g := by
    intro τ z g
    funext x
    simp only [Datum.dRho, Pi.smul_apply, smul_eq_mul, heisO]
    rw [← deriv_const_mul_field]
    congr 1
    funext t
    ring
  refine pureTensorL_smul _ c (fun k g => ?_) f P
  unfold aPlusAll aPlus crea
  rw [hd, hd, smul_comm Complex.I c, ← smul_sub, smul_comm]

/- English proof (translation)
Establish `hu` using `(Matrix.isUnit_iff_isUnit_det _).1 hP`. Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`. Establish `h2 : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul _ hu`. Establish `e : (1 / 2 : ℂ) • (1 + P⁻¹ * diagonal j * P) * (P⁻¹ * diagonal d * P) + (1 / 2 : ℂ) • (1 - P⁻¹ * diagonal j * P) = P⁻¹ * diagonal (fun a => (1 + j a) / 2 * d a + (1 - j a) / 2) * P`. Establish `e1 : P⁻¹ * diagonal j * P * (P⁻¹ * diagonal d * P) = P⁻¹ * (diagonal j * diagonal d) * P`.

Combine the equalities or inequalities in the displayed calculation. Establish `e2 : diagonal (fun a => (1 + j a) / 2 * d a + (1 - j a) / 2) = (1 / 2 : ℂ) • (diagonal d + diagonal j * diagonal d) + (1 / 2 : ℂ) • (1 - diagonal j)`. Use extensionality with `a b`. Simplify using `only [diagonal_mul_diagonal, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, diagonal_apply, Matrix.one_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> ring`.

Rewrite using `[e2, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, e1]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2]`. Rewrite using `[e, det_mul, det_mul, det_diagonal, mul_right_comm, ← det_mul, h2, det_one, one_mul]`.
-/
theorem det_half {m : ℕ} {P : Matrix (Fin m) (Fin m) ℂ} (hP : IsUnit P) (j d : Fin m → ℂ) :
    ((1 / 2 : ℂ) • (1 + P⁻¹ * diagonal j * P) * (P⁻¹ * diagonal d * P) + (1 / 2 : ℂ) • (1 - P⁻¹ * diagonal j * P)).det =
      ∏ a, ((1 + j a) / 2 * d a + (1 - j a) / 2) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  have e : (1 / 2 : ℂ) • (1 + P⁻¹ * diagonal j * P) * (P⁻¹ * diagonal d * P) + (1 / 2 : ℂ) • (1 - P⁻¹ * diagonal j * P) =
      P⁻¹ * diagonal (fun a => (1 + j a) / 2 * d a + (1 - j a) / 2) * P := by
    have e1 : P⁻¹ * diagonal j * P * (P⁻¹ * diagonal d * P) = P⁻¹ * (diagonal j * diagonal d) * P := by
      calc _ = P⁻¹ * (diagonal j * (P * P⁻¹) * diagonal d) * P := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.mul_one]
    have e2 : diagonal (fun a => (1 + j a) / 2 * d a + (1 - j a) / 2) =
        (1 / 2 : ℂ) • (diagonal d + diagonal j * diagonal d) + (1 / 2 : ℂ) • (1 - diagonal j) := by
      ext a b
      simp only [diagonal_mul_diagonal, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, diagonal_apply,
        Matrix.one_apply, smul_eq_mul]
      split_ifs <;> ring
    rw [e2, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, e1]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, h2]
  rw [e, det_mul, det_mul, det_diagonal, mul_right_comm, ← det_mul, h2, det_one, one_mul]

/- English proof (translation)
Establish `e : (1 / 2 : ℂ) • (1 + s) + (1 / 2 : ℂ) • (1 - s) = 1` using `by module`. Rewrite using `[Matrix.mul_one, Matrix.mul_one, e, add_comm, e, det_one]`. Conclude with `⟨rfl, rfl⟩`.
-/
theorem half_one {m : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) :
    ((1 / 2 : ℂ) • (1 + s) * 1 + (1 / 2 : ℂ) • (1 - s)).det = 1 ∧
      ((1 / 2 : ℂ) • (1 - s) * 1 + (1 / 2 : ℂ) • (1 + s)).det = 1 := by
  have e : (1 / 2 : ℂ) • (1 + s) + (1 / 2 : ℂ) • (1 - s) = 1 := by module
  rw [Matrix.mul_one, Matrix.mul_one, e, add_comm, e, det_one]
  exact ⟨rfl, rfl⟩

/- English proof (translation)
Establish `h2` using `det_half hP (fun a => -(if ε a then (1 : ℂ) else -1)) fun a => Complex.exp ((t a : ℂ) * Complex.I)`. Rewrite `h2` using `[← diagonal_neg, Matrix.mul_neg, Matrix.neg_mul, ← sub_eq_add_neg, sub_neg_eq_add]`. Unfold `Formalism.REAL.Jm`. Rewrite using `[det_half hP, h2, ← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_mul_distrib, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `cases ε a <;> simp [← Complex.exp_int_mul, mul_assoc]`.
-/
theorem det_pow {m : ℕ} {P : Matrix (Fin m) (Fin m) ℂ} (hP : IsUnit P) (ε : Fin m → Bool) (t : Fin m → ℝ) (x y : ℤ) :
    ((1 / 2 : ℂ) • (1 + P⁻¹ * Formalism.REAL.Jm ε * P) *
        (P⁻¹ * (diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) * P) +
        (1 / 2 : ℂ) • (1 - P⁻¹ * Formalism.REAL.Jm ε * P)).det ^ x *
      ((1 / 2 : ℂ) • (1 - P⁻¹ * Formalism.REAL.Jm ε * P) *
        (P⁻¹ * (diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) * P) +
        (1 / 2 : ℂ) • (1 + P⁻¹ * Formalism.REAL.Jm ε * P)).det ^ y =
      Complex.exp (((∑ a, (if ε a then (x : ℝ) else y) * t a : ℝ) : ℂ) * Complex.I) := by
  have h2 := det_half hP (fun a => -(if ε a then (1 : ℂ) else -1)) fun a => Complex.exp ((t a : ℂ) * Complex.I)
  rw [← diagonal_neg, Matrix.mul_neg, Matrix.neg_mul, ← sub_eq_add_neg, sub_neg_eq_add] at h2
  unfold Formalism.REAL.Jm
  rw [det_half hP, h2, ← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_mul_distrib, Complex.ofReal_sum,
    Finset.sum_mul, Complex.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  cases ε a <;> simp [← Complex.exp_int_mul, mul_assoc]

open Classical in

/- English proof (translation)
Take `⟨x₁, x₂, y₁, y₂, h⟩` from `GlobalTheory.T.maximalCompact_acts_on_realVacua_by_detPowers D ψ θ S T χS χT om hW hθ kS kT (fun _ => 1) (cart M) hS (GlobalTheory.Chain.VacVec.cart_isCartanInv M)`. Use `⟨fun k => ((1 / 2 : ℂ) • (1 + cart M τ) * ((M.fr τ)⁻¹ * k * M.fr τ) + (1 / 2 : ℂ) • (1 - cart M τ)).det ^ x₁ τ * ((1 / 2 : ℂ) • (1 - cart M τ) * ((M.fr τ)⁻¹ * k * M.fr τ) + (1 / 2 : ℂ) • (1 + cart M τ)).det ^ x₂ τ, x₁ τ, x₂ τ, fun t => det_pow (M.fr_unit τ) _ t _ _, fun k hk P => …` and prove the remaining obligations. Establish `hu` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Establish `h1 : M.fr τ * (M.fr τ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`. Establish `hU : (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ)`.

Establish `hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ)` using `kset_uj hk`. Establish `h3 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1` using `by rw [← conjTranspose_mul, h1, conjTranspose_one]`. Use `show _ᴴ * _ * _ = _`. Rewrite using `[← M.fr_gram τ]`. Combine the equalities or inequalities in the displayed calculation.

Establish `ha : atTau θ T τ ((M.fr τ)⁻¹ * k * M.fr τ) ∈ GinfC T ∧ compAt θ τ (mt T (atTau θ T τ ((M.fr τ)⁻¹ * k * M.fr τ))) = (M.fr τ)⁻¹ * k * M.fr τ ∧ ∀ ρ, ρ ≠ τ → compAt θ ρ (mt T (atTau θ T τ ((M.fr τ)⁻¹ * k * M.fr τ))) = 1` using `GlobalTheory.PointAtPlaceHom.atTau_spec hθ T τ hU`. Generalize the expression as in `atTau θ T τ ((M.fr τ)⁻¹ * k * M.fr τ) = g at ha ⊢`. Take `⟨a1, a2, a3⟩` from `ha`. Establish `e1 : ∀ ρ, compAt θ ρ (mt S 1) = 1` using `fun ρ => GlobalTheory.PointAtPlaceHom.infMat_one S _`. Establish `hc : ∀ ρ, cart M ρ * compAt θ ρ (mt T g) = compAt θ ρ (mt T g) * cart M ρ`.

Introduce `ρ`. Distinguish the cases in `e : ρ = τ`. Substitute `e` using the available equality. Rewrite using `[a2]`. Unfold `cart`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (M.fr ρ)⁻¹ * (k * (M.fr ρ * (M.fr ρ)⁻¹) * Formalism.REAL.Jm (M.ε ρ)) * M.fr ρ := by`. Rewrite using `[h1, Matrix.mul_one, Matrix.mul_one, hk.2]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.

Rewrite using `[a3 ρ e, Matrix.mul_one, Matrix.one_mul]`. Establish `hone : ∀ ρ, (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) ∈ Formalism.REAL.Kset (M.ε ρ)` using `fun ρ => ⟨one_mem _, by rw [Matrix.mul_one, Matrix.one_mul]⟩`. Rewrite using `[(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ (fun _ => 1) (fun _ => 1) BS BS (cart M) (cart M) (onb M) (fun ρ => onb M ρ * Function.update (fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) τ k ρ) 1 g (fun ρ => by rw [e1]) hc (fun ρ => by rw [e1, Matrix.on …`. Use `congr 1`. Rewrite using `[Finset.prod_eq_single τ (fun ρ _ e => ?_) (fun e => (e (Finset.mem_univ _)).elim)]`.

Rewrite using `[e1, a2, (half_one _).1, (half_one _).2, _root_.one_zpow, _root_.one_zpow, mul_one, mul_one]`. Rewrite using `[e1, a3 ρ e, (half_one _).1, (half_one _).2, (half_one _).1, (half_one _).2]`. Simplify using the standard rewrite rules. Distinguish the cases in `e : ρ = τ`. Substitute `e` using the available equality.

Rewrite using `[Function.update_self]` and apply the resulting hypothesis. Rewrite using `[Function.update_of_ne e]`. Conclude with `hone ρ`. Distinguish the cases in `e : ρ = τ`. Substitute `e` using the available equality.

Rewrite using `[Function.update_self, Function.update_self]`. Both sides reduce to the same expression. Rewrite using `[Function.update_of_ne e, Function.update_of_ne e]`. Conclude with `(congrFun (congrFun (tw_one (M.ε ρ)) b) a).symm`. Distinguish the cases in `e : ρ = τ`.

Substitute `e` using the available equality. Rewrite using `[Function.update_self, a2, onb, Matrix.mul_assoc, h1, Matrix.mul_one]`. Rewrite using `[Function.update_of_ne e, a3 ρ e, Matrix.mul_one, Matrix.one_mul]`.
-/
theorem om_pt {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (kS : S.SigOK) (kT : T.SigOK) {S' : D.what₂.Tau → SPar} (M : DSModel T S')
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (hS : ∀ τ, IsCartanInv (gramAt D S τ) 1)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f)
    (τ : D.what₂.Tau) : ∃ (χ : Matrix (Fin T.rank) (Fin T.rank) ℂ → ℂ) (x y : ℝ),
      (∀ t : Fin T.rank → ℝ, χ (diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) =
        Complex.exp (((∑ a, (if M.ε τ a then x else y) * t a : ℝ) : ℂ) * Complex.I)) ∧
      ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ P, om (1, atTau θ T τ ((M.fr τ)⁻¹ * k * M.fr τ))
          (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P) =
        pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f
          (χ k • sub (Function.update (fun _ => 1) τ (tw (M.ε τ) k)) P) := by
  obtain ⟨x₁, x₂, y₁, y₂, h⟩ := GlobalTheory.T.maximalCompact_acts_on_realVacua_by_detPowers D ψ θ S T χS χT om hW hθ kS kT (fun _ => 1) (cart M) hS
    (GlobalTheory.Chain.VacVec.cart_isCartanInv M)
  refine ⟨fun k => ((1 / 2 : ℂ) • (1 + cart M τ) * ((M.fr τ)⁻¹ * k * M.fr τ) + (1 / 2 : ℂ) • (1 - cart M τ)).det ^ x₁ τ *
    ((1 / 2 : ℂ) • (1 - cart M τ) * ((M.fr τ)⁻¹ * k * M.fr τ) + (1 / 2 : ℂ) • (1 + cart M τ)).det ^ x₂ τ, x₁ τ, x₂ τ,
    fun t => det_pow (M.fr_unit τ) _ t _ _, fun k hk P => ?_⟩
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hU : (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
    have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
    have h3 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
    show _ᴴ * _ * _ = _
    rw [← M.fr_gram τ]
    calc _ = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
          M.fr τ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1, h3, Matrix.mul_one, Matrix.mul_one, hk']
  have ha : atTau θ T τ ((M.fr τ)⁻¹ * k * M.fr τ) ∈ GinfC T ∧
      compAt θ τ (mt T (atTau θ T τ ((M.fr τ)⁻¹ * k * M.fr τ))) = (M.fr τ)⁻¹ * k * M.fr τ ∧
      ∀ ρ, ρ ≠ τ → compAt θ ρ (mt T (atTau θ T τ ((M.fr τ)⁻¹ * k * M.fr τ))) = 1 :=
    GlobalTheory.PointAtPlaceHom.atTau_spec hθ T τ hU
  generalize atTau θ T τ ((M.fr τ)⁻¹ * k * M.fr τ) = g at ha ⊢
  obtain ⟨a1, a2, a3⟩ := ha
  have e1 : ∀ ρ, compAt θ ρ (mt S 1) = 1 := fun ρ => GlobalTheory.PointAtPlaceHom.infMat_one S _
  have hc : ∀ ρ, cart M ρ * compAt θ ρ (mt T g) = compAt θ ρ (mt T g) * cart M ρ := by
    intro ρ
    by_cases e : ρ = τ
    · subst e
      rw [a2]
      unfold cart
      calc _ = (M.fr ρ)⁻¹ * (Formalism.REAL.Jm (M.ε ρ) * (M.fr ρ * (M.fr ρ)⁻¹) * k) * M.fr ρ := by
            simp only [Matrix.mul_assoc]
        _ = (M.fr ρ)⁻¹ * (k * (M.fr ρ * (M.fr ρ)⁻¹) * Formalism.REAL.Jm (M.ε ρ)) * M.fr ρ := by
            rw [h1, Matrix.mul_one, Matrix.mul_one, hk.2]
        _ = _ := by simp only [Matrix.mul_assoc]
    · rw [a3 ρ e, Matrix.mul_one, Matrix.one_mul]
  have hone : ∀ ρ, (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) ∈ Formalism.REAL.Kset (M.ε ρ) := fun ρ =>
    ⟨one_mem _, by rw [Matrix.mul_one, Matrix.one_mul]⟩
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ (fun _ => 1) (fun _ => 1) BS BS (cart M) (cart M)
      (onb M) (fun ρ => onb M ρ * Function.update (fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) τ k ρ) 1 g (fun ρ => by rw [e1]) hc
      (fun ρ => by rw [e1, Matrix.one_mul]) (fun ρ => ?_) f hf P).2,
    h f hf hv 1 (one_mem _) g a1 (fun ρ => by rw [e1]) hc, pureTensorO_smul, map_smul,
    GlobalTheory.T.fockPolynomialVector_maximalCompact_basis_substitution D ψ θ S T S' M BS f _ (Function.update (fun _ => 1) τ (tw (M.ε τ) k)) hW.std hθ hS hf (fun ρ => ?_)
      (fun ρ a b => ?_)]
  · congr 1
    rw [Finset.prod_eq_single τ (fun ρ _ e => ?_) (fun e => (e (Finset.mem_univ _)).elim)]
    · rw [e1, a2, (half_one _).1, (half_one _).2, _root_.one_zpow, _root_.one_zpow, mul_one, mul_one]
    · rw [e1, a3 ρ e, (half_one _).1, (half_one _).2, (half_one _).1, (half_one _).2]
      simp
  · by_cases e : ρ = τ
    · subst e; rwa [Function.update_self]
    · rw [Function.update_of_ne e]; exact hone ρ
  · by_cases e : ρ = τ
    · subst e; rw [Function.update_self, Function.update_self]; rfl
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact (congrFun (congrFun (tw_one (M.ε ρ)) b) a).symm
  · by_cases e : ρ = τ
    · subst e
      rw [Function.update_self, a2, onb, Matrix.mul_assoc, h1, Matrix.mul_one]
    · rw [Function.update_of_ne e, a3 ρ e, Matrix.mul_one, Matrix.one_mul]

open Classical in
/- English proof (translation)
Use `MvPolynomial.algHom_ext fun ⟨ρ, a, j⟩ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.aeval_X, MvPolynomial.aeval_X]`. Simplify using `only`. Distinguish the cases in `e : ρ = τ`. Substitute `e` using the available equality.

Rewrite using `[Function.update_self, if_pos rfl, Finset.sum_eq_single a (fun b _ hb => by rw [diagonal_apply_ne _ hb, zero_smul]) (fun h => (h (Finset.mem_univ _)).elim), diagonal_apply_eq]`. Rewrite using `[Function.update_of_ne e, if_neg e, Finset.sum_eq_single a (fun b _ hb => by rw [Matrix.one_apply_ne hb, zero_smul]) (fun h => (h (Finset.mem_univ _)).elim), Matrix.one_apply_eq]`.
-/
theorem sub_diag {m n : ℕ} (τ : D.what₂.Tau) (l : Fin m → ℂ) :
    (sub (Function.update (fun _ => 1) τ (diagonal l)) : PolF D m n →ₐ[ℂ] PolF D m n) =
      MvPolynomial.aeval fun v : FVar D m n => (if v.1 = τ then l v.2.1 else 1) • (MvPolynomial.X v : PolF D m n) := by
  refine MvPolynomial.algHom_ext fun ⟨ρ, a, j⟩ => ?_
  rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  dsimp only
  by_cases e : ρ = τ
  · subst e
    rw [Function.update_self, if_pos rfl, Finset.sum_eq_single a (fun b _ hb => by rw [diagonal_apply_ne _ hb, zero_smul])
      (fun h => (h (Finset.mem_univ _)).elim), diagonal_apply_eq]
  · rw [Function.update_of_ne e, if_neg e, Finset.sum_eq_single a (fun b _ hb => by rw [Matrix.one_apply_ne hb, zero_smul])
      (fun h => (h (Finset.mem_univ _)).elim), Matrix.one_apply_eq]

open Classical in

/- English proof (translation)
Take `⟨e, h1, h2⟩` from `GlobalTheory.T.minorProduct_torusWeight_block_translates D m n p q ap am τ`. Use `⟨fun a => κ a + (if ε a then 1 else -1) * e a, fun t => ?_, fun ν y hy hy0 hw => ?_⟩` and prove the remaining obligations. Rewrite using `[hπ, tw_diag, h1 _ _ (fun ρ hρ => Function.update_of_ne hρ _ _) (Function.update_self _ _ _), hχ, smul_smul]`. Use `congr 1`. Simplify using `only [← Complex.exp_nat_mul]`.

Rewrite using `[← Complex.exp_sum, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Simplify using `only [Finset.sum_mul, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun a _ => by ring`.

Take `⟨s, hs⟩` from `MvPolynomial.ne_zero_iff.1 hy0`. Establish `hb : ∑ a : Fin m, (a : ℕ) * e a ≤ ∑ a : Fin m, ∑ j : Fin n, (a : ℕ) * s (τ, a, j)`. Assume the negation of the conclusion as `hn`. Use `hs ?_` and prove the remaining obligations. Use `clear hs hw hy0`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨k, hk, rfl⟩` from `hz`. Rewrite using `[hπ, MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.1 fun h => hn (h2 _ (fun ρ hρ => Function.update_of_ne hρ _ _) (fun a b hb ha => by rw [Function.update_self]; exact tw_block hε hk a b hb ha) s h), smul_zero]`. Consider the case `zero => rfl`.

Consider the case `add a b _ _ ha hb => rw [MvPolynomial.coeff_add, ha, hb, add_zero]`. Consider the case `smul c a _ ha => rw [MvPolynomial.coeff_smul, ha, smul_zero]`. Establish `key : ∑ a : Fin m, ν a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)) = ∑ a : Fin m, κ a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)) - ((∑ a : Fin m, ∑ j : Fin n, (a : ℕ) * s (τ, a, j) : ℕ) : ℝ)`. Use `eq_of_exp_eq fun r => ?_` and prove the remaining obligations. Establish `h` using `congrArg (MvPolynomial.coeff s) (hw fun a => r * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)))`.

Rewrite `h` using `[hπ, tw_diag, sub_diag, hχ, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, coeff_scale, smul_eq_mul, smul_eq_mul, ← mul_assoc]`. Establish `h'` using `mul_right_cancel₀ hs h`. Rewrite `h'` using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Finset.prod_eq_single τ (fun ρ _ hρ => by simp [hρ]) (fun h => (h (Finset.mem_univ _)).elim), Fintype.prod_prod_type]`. Simplify using `only [if_true, ← Complex.exp_nat_mul, ← Complex.exp_sum, ← Complex.exp_add] at h'`. Use `Eq.trans ?_ (h'.symm.trans ?_)` and prove the remaining obligations.

Simplify using `only [Finset.mul_sum, mul_left_comm]`. Use `congr 1`. Use `push_cast`. Simplify using `only [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `cases ε a <;> simp <;> ring`. Rewrite using `[key]`. Establish `hb' : ((∑ a : Fin m, (a : ℕ) * e a : ℕ) : ℝ) ≤ _` using `Nat.cast_le.2 hb`. Use `(sub_le_sub_left hb' _).trans_eq ?_` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `cases ε a <;> simp <;> ring`.
-/
theorem delta_weights {m n : ℕ} (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (τ : D.what₂.Tau) {ε : Fin m → Bool}
    (hε : ∀ a, ε a = decide ((a : ℕ) < p τ)) (χ : Matrix (Fin m) (Fin m) ℂ → ℂ) (κ : Fin m → ℝ)
    (hχ : ∀ t : Fin m → ℝ, χ (diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) =
      Complex.exp (((∑ a, κ a * t a : ℝ) : ℂ) * Complex.I))
    (π : Matrix (Fin m) (Fin m) ℂ → PolF D m n →ₗ[ℂ] PolF D m n)
    (hπ : ∀ k P, π k P = χ k • sub (Function.update (fun _ => 1) τ (tw ε k)) P) :
    ∃ μ : Fin m → ℝ, (∀ t : Fin m → ℝ, π (diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) (delta p q ap am) =
        Complex.exp (((∑ a, μ a * t a : ℝ) : ℂ) * Complex.I) • delta p q ap am) ∧
      ∀ (ν : Fin m → ℝ) (y : PolF D m n),
        y ∈ Submodule.span ℂ {z | ∃ k ∈ Formalism.REAL.Kset ε, z = π k (delta p q ap am)} → y ≠ 0 →
        (∀ t : Fin m → ℝ, π (diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) y =
          Complex.exp (((∑ a, ν a * t a : ℝ) : ℂ) * Complex.I) • y) →
        ∑ a : Fin m, ν a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)) ≤
          ∑ a : Fin m, μ a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)) := by
  obtain ⟨e, h1, h2⟩ := GlobalTheory.T.minorProduct_torusWeight_block_translates D m n p q ap am τ
  refine ⟨fun a => κ a + (if ε a then 1 else -1) * e a, fun t => ?_, fun ν y hy hy0 hw => ?_⟩
  · rw [hπ, tw_diag, h1 _ _ (fun ρ hρ => Function.update_of_ne hρ _ _) (Function.update_self _ _ _), hχ, smul_smul]
    congr 1
    simp only [← Complex.exp_nat_mul]
    rw [← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  · obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.1 hy0
    have hb : ∑ a : Fin m, (a : ℕ) * e a ≤ ∑ a : Fin m, ∑ j : Fin n, (a : ℕ) * s (τ, a, j) := by
      by_contra hn
      refine hs ?_
      clear hs hw hy0
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨k, hk, rfl⟩ := hz
        rw [hπ, MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.1 fun h => hn (h2 _
          (fun ρ hρ => Function.update_of_ne hρ _ _)
          (fun a b hb ha => by rw [Function.update_self]; exact tw_block hε hk a b hb ha) s h), smul_zero]
      | zero => rfl
      | add a b _ _ ha hb => rw [MvPolynomial.coeff_add, ha, hb, add_zero]
      | smul c a _ ha => rw [MvPolynomial.coeff_smul, ha, smul_zero]
    have key : ∑ a : Fin m, ν a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)) =
        ∑ a : Fin m, κ a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)) -
          ((∑ a : Fin m, ∑ j : Fin n, (a : ℕ) * s (τ, a, j) : ℕ) : ℝ) := by
      refine eq_of_exp_eq fun r => ?_
      have h := congrArg (MvPolynomial.coeff s) (hw fun a => r * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)))
      rw [hπ, tw_diag, sub_diag, hχ, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, coeff_scale, smul_eq_mul,
        smul_eq_mul, ← mul_assoc] at h
      have h' := mul_right_cancel₀ hs h
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
        Finset.prod_eq_single τ (fun ρ _ hρ => by simp [hρ]) (fun h => (h (Finset.mem_univ _)).elim),
        Fintype.prod_prod_type] at h'
      simp only [if_true, ← Complex.exp_nat_mul, ← Complex.exp_sum, ← Complex.exp_add] at h'
      refine Eq.trans ?_ (h'.symm.trans ?_)
      · simp only [Finset.mul_sum, mul_left_comm]
      · congr 1
        push_cast
        simp only [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
        congr 1
        · ring
        · refine Finset.sum_congr rfl fun j _ => ?_
          cases ε a <;> simp <;> ring
    rw [key]
    have hb' : ((∑ a : Fin m, (a : ℕ) * e a : ℕ) : ℝ) ≤ _ := Nat.cast_le.2 hb
    refine (sub_le_sub_left hb' _).trans_eq ?_
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    cases ε a <;> simp <;> ring

open scoped ComplexOrder in
/- English proof (translation)
Take `⟨ε, h1, h2, -⟩` from `h`. Establish `e : Bᴴ * G * B = 1`. Rewrite using `[h2, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Break down `h1 a with h | h` into its components or cases. Rewrite using `[h.1, Complex.ofReal_one]`. Conclude with `absurd a.2 (not_lt.2 h.2)`. Establish `hB : IsUnit B` using `(Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse e)`. Use `⟨Matrix.mul_one _, by simp, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mul_one, ← Matrix.IsUnit.posDef_star_left_conjugate_iff hB, star_eq_conjTranspose, e]`. Conclude with `Matrix.PosDef.one`.
-/
theorem cartan_one {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : IsCartanInv G 1 := by
  obtain ⟨ε, h1, h2, -⟩ := h
  have e : Bᴴ * G * B = 1 := by
    rw [h2, ← diagonal_one]
    congr 1
    funext a
    rcases h1 a with h | h
    · rw [h.1, Complex.ofReal_one]
    · exact absurd a.2 (not_lt.2 h.2)
  have hB : IsUnit B := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse e)
  refine ⟨Matrix.mul_one _, by simp, ?_⟩
  rw [Matrix.mul_one, ← Matrix.IsUnit.posDef_star_left_conjugate_iff hB, star_eq_conjTranspose, e]
  exact Matrix.PosDef.one

open Classical in

/- English proof (translation)
Set `ι : lowT M τ →ₗ[ℂ] M.H τ` to `(M.sm τ).subtype ∘ₗ (lowT M τ).subtype`. Establish `hι : Function.Injective ι` using `Subtype.val_injective.comp Subtype.val_injective`. Set `φ₀ : lowT M τ →ₗ[ℂ] PolF D W.rank V.rank` to `io.flip w ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v τ`. Establish `h0 : ∀ u, φ₀ u = io (PiTensorProduct.tprod ℂ (Function.update v τ u)) w` using `fun _ => rfl`. Take `⟨r, hr⟩` from `ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hι)`.

Establish `hφ : ∀ u, (φ₀ ∘ₗ r) (ι u) = φ₀ u` using `fun u => congrArg φ₀ (LinearMap.congr_fun hr u)`. Establish `hL : ∀ x ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ⊓ M.sm τ, ∃ u, ι u = x` using `fun x hx => ⟨⟨⟨x, hx.2⟩, hx.1⟩, rfl⟩`. Establish `hd : (φ₀ ∘ₗ r) (ι (v τ)) = delta p q ap am` using `by rw [hφ, h0, Function.update_eq_self, h]`. Set `π : Matrix (Fin W.rank) (Fin W.rank) ℂ → PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank` to `fun k => χ k • (sub (Function.update (fun _ => 1) τ (tw (M.ε τ) k))).toLinearMap`. Take `⟨μ, h1, h2⟩` from `delta_weights (n := V.rank) p q ap am τ hε χ κ hχ π fun _ _ => rfl`.

Rewrite `h1`, `h2` using `[← hd]`. Take `⟨x, hx, x1, x2, x3⟩` from `GlobalTheory.T.exists_extremalUnitVector_same_highestImage _ _ _ (M.ε τ) (M.lam τ) μ (M.σ τ) π _ (φ₀ ∘ₗ r) (ι (v τ)) (M.ds τ).2.2.1 inf_le_left (GlobalTheory.T.lowestKType_smoothVectors_isKStable D W S' M τ) (fun k hk x hx => by`. Take `⟨u', hu'⟩` from `hL _ (GlobalTheory.T.lowestKType_smoothVectors_isKStable D W S' M τ k hk x hx)`. Take `⟨u, rfl⟩` from `hL x hx`. Rewrite using `[← hu', hφ, hφ]`.

Apply `hinj` to reduce the goal to its premises. Establish `e` using `hio.2.1 τ k hk (Function.update v τ u) u' (by rw [Function.update_self]; exact hu') w`. Rewrite `e` using `[Function.update_idem, hom k hk]`. Conclude with `e.symm) ⟨(v τ).2, (v τ).1.2⟩ hv h1 h2`. Take `⟨u, rfl⟩` from `hL x hx`.

Conclude with `⟨u, x1, x2, by rw [← h0, ← hφ, x3, hd]⟩`.
-/
theorem replace_at {V W : HSp D} {S' : D.what₂.Tau → SPar} {θ : InfFam D} (M : DSModel W S') {c : CoefA V}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)}
    (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank}
    (hio : IsIoW θ M c ω pt (delta p q ap am) io) (hinj : Function.Injective pt) (τ : D.what₂.Tau)
    (hε : ∀ a, M.ε τ a = decide ((a : ℕ) < p τ)) (χ : Matrix (Fin W.rank) (Fin W.rank) ℂ → ℂ) (κ : Fin W.rank → ℝ)
    (hχ : ∀ t : Fin W.rank → ℝ, χ (diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) =
      Complex.exp (((∑ a, κ a * t a : ℝ) : ℂ) * Complex.I))
    (hom : ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ P, ω (1, atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)) (pt P) =
      pt (χ k • sub (Function.update (fun _ => 1) τ (tw (M.ε τ) k)) P))
    (v : ∀ ρ, lowT M ρ) (w : c.W) (hv : ‖((v τ : M.sm τ) : M.H τ)‖ = 1)
    (h : io (PiTensorProduct.tprod ℂ v) w = delta p q ap am) :
    ∃ u : lowT M τ, ‖((u : M.sm τ) : M.H τ)‖ = 1 ∧
      IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) (extWt M τ) ((u : M.sm τ) : M.H τ) ∧
      io (PiTensorProduct.tprod ℂ (Function.update v τ u)) w = delta p q ap am := by
  let ι : lowT M τ →ₗ[ℂ] M.H τ := (M.sm τ).subtype ∘ₗ (lowT M τ).subtype
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  let φ₀ : lowT M τ →ₗ[ℂ] PolF D W.rank V.rank := io.flip w ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v τ
  have h0 : ∀ u, φ₀ u = io (PiTensorProduct.tprod ℂ (Function.update v τ u)) w := fun _ => rfl
  obtain ⟨r, hr⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hι)
  have hφ : ∀ u, (φ₀ ∘ₗ r) (ι u) = φ₀ u := fun u => congrArg φ₀ (LinearMap.congr_fun hr u)
  have hL : ∀ x ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ⊓ M.sm τ, ∃ u, ι u = x := fun x hx => ⟨⟨⟨x, hx.2⟩, hx.1⟩, rfl⟩
  have hd : (φ₀ ∘ₗ r) (ι (v τ)) = delta p q ap am := by rw [hφ, h0, Function.update_eq_self, h]
  let π : Matrix (Fin W.rank) (Fin W.rank) ℂ → PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank := fun k =>
    χ k • (sub (Function.update (fun _ => 1) τ (tw (M.ε τ) k))).toLinearMap
  obtain ⟨μ, h1, h2⟩ := delta_weights (n := V.rank) p q ap am τ hε χ κ hχ π fun _ _ => rfl
  rw [← hd] at h1 h2
  obtain ⟨x, hx, x1, x2, x3⟩ := GlobalTheory.T.exists_extremalUnitVector_same_highestImage _ _ _ (M.ε τ) (M.lam τ) μ (M.σ τ) π _ (φ₀ ∘ₗ r) (ι (v τ)) (M.ds τ).2.2.1
    inf_le_left (GlobalTheory.T.lowestKType_smoothVectors_isKStable D W S' M τ) (fun k hk x hx => by
      obtain ⟨u', hu'⟩ := hL _ (GlobalTheory.T.lowestKType_smoothVectors_isKStable D W S' M τ k hk x hx)
      obtain ⟨u, rfl⟩ := hL x hx
      rw [← hu', hφ, hφ]
      apply hinj
      have e := hio.2.1 τ k hk (Function.update v τ u) u' (by rw [Function.update_self]; exact hu') w
      rw [Function.update_idem, hom k hk] at e
      exact e.symm) ⟨(v τ).2, (v τ).1.2⟩ hv h1 h2
  obtain ⟨u, rfl⟩ := hL x hx
  exact ⟨u, x1, x2, by rw [← h0, ← hφ, x3, hd]⟩

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R hL _ hM hP i`. Establish `hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i A.μ0)`. Establish `h` using `hP.pt_theta i A.μ0 1`. Establish `e : R.ptP i A.μ0 1 = R.vP i A.μ0`. Unfold `RealDat.ptP pureTensorO pureTensorL`.

Rewrite using `[show (1 : PolF D (Wc D i).rank (Vc D i).rank) = MvPolynomial.basisMonomials _ ℂ 0 from rfl, Module.Basis.constr_basis]`. Simplify using `[opPow]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Establish `hv` using `GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hP.vP i A.μ0) hf`. Establish `hne : R.vP i A.μ0 ≠ 0` using `thPVec_ne_zero (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)) (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) ((rank_Wc i).trans_le (r_le_V i)) (hP.vP i A.μ0)`.

Establish `hS` using `fun τ => cartan_one (hM.BV i τ)`. Establish `hinj` using `GlobalTheory.T.fockPolynomialVectors_injective_nonzero_vacuum D R.ψ R.θ _ _ _ (R.MW i (sg0 D A)) (R.BV i) _ (hP.ωP i A.μ0).std hM.inf hS (hM.BV i) hf hne hv`. Establish `hio` using `hP.ioP i A.μ0`. Take `⟨v₀, w, h1, hw, h2⟩` from `hio.2.2`. Establish `ind : ∀ s : Finset D.what₂.Tau, ∃ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ‖((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)‖ = 1) ∧ (∀ ρ ∈ s, IsWtOn (Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε ρ)) ((R.MW i (sg0 D A)).σ ρ) (extWt (R.MW i (sg0 D A)) ρ) ((v ρ : (R.MW i (s …`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨v₀, h1, fun ρ h => (Finset.notMem_empty ρ h).elim, h2⟩`. Consider the case `insert τ s _ ih`. Take `⟨v, a1, a2, a3⟩` from `ih`.

Take `⟨χ, x, y, c1, c2⟩` from `om_pt (hP.ωP i A.μ0) hM.inf (D.sp.V_sig _) (D.sp.W_sig _) (R.MW i (sg0 D A)) (R.BV i) hS hf hv τ`. Take `⟨u, u1, u2, u3⟩` from `replace_at (R.MW i (sg0 D A)) _ _ _ _ hio hinj τ (hM.order i τ) χ _ c1 c2 v w (a1 τ) a3`. Use `⟨Function.update v τ u, fun ρ => ?_, fun ρ hρ => ?_, u3⟩` and prove the remaining obligations. Distinguish the cases in `e : ρ = τ`. Substitute `e` using the available equality.

Rewrite using `[Function.update_self]` and apply the resulting hypothesis. Rewrite using `[Function.update_of_ne e]`. Conclude with `a1 ρ`. Distinguish the cases in `e : ρ = τ`. Substitute `e` using the available equality.

Rewrite using `[Function.update_self]` and apply the resulting hypothesis. Rewrite using `[Function.update_of_ne e]`. Conclude with `a2 ρ ((Finset.mem_insert.1 hρ).resolve_left e)`. Take `⟨v, a1, a2, a3⟩` from `ind Finset.univ`. Conclude with `⟨fun ρ => v ρ, fun ρ => ⟨a1 ρ, (v ρ).2, a2 ρ (Finset.mem_univ ρ)⟩, v, w, fun _ => rfl, hw, a3⟩`.
-/
theorem ioExt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsThP → IoExt R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL _ hM hP i
  classical
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i A.μ0) := by
    have h := hP.pt_theta i A.μ0 1
    have e : R.ptP i A.μ0 1 = R.vP i A.μ0 := by
      unfold RealDat.ptP pureTensorO pureTensorL
      rw [show (1 : PolF D (Wc D i).rank (Vc D i).rank) = MvPolynomial.basisMonomials _ ℂ 0 from rfl,
        Module.Basis.constr_basis]
      simp [opPow]
    rwa [e] at h
  have hv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hP.vP i A.μ0) hf
  have hne : R.vP i A.μ0 ≠ 0 := thPVec_ne_zero (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)) (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i))
    ((rank_Wc i).trans_le (r_le_V i)) (hP.vP i A.μ0)
  have hS := fun τ => cartan_one (hM.BV i τ)
  have hinj := GlobalTheory.T.fockPolynomialVectors_injective_nonzero_vacuum D R.ψ R.θ _ _ _ (R.MW i (sg0 D A)) (R.BV i) _ (hP.ωP i A.μ0).std hM.inf hS (hM.BV i) hf hne hv
  have hio := hP.ioP i A.μ0
  obtain ⟨v₀, w, h1, hw, h2⟩ := hio.2.2
  have ind : ∀ s : Finset D.what₂.Tau, ∃ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
      (∀ ρ, ‖((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)‖ = 1) ∧
      (∀ ρ ∈ s, IsWtOn (Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε ρ)) ((R.MW i (sg0 D A)).σ ρ) (extWt (R.MW i (sg0 D A)) ρ)
        ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)) ∧
      R.ioP i (PiTensorProduct.tprod ℂ v) w = RealDat.Delta i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨v₀, h1, fun ρ h => (Finset.notMem_empty ρ h).elim, h2⟩
    | insert τ s _ ih =>
      obtain ⟨v, a1, a2, a3⟩ := ih
      obtain ⟨χ, x, y, c1, c2⟩ := om_pt (hP.ωP i A.μ0) hM.inf (D.sp.V_sig _) (D.sp.W_sig _) (R.MW i (sg0 D A)) (R.BV i)
        hS hf hv τ
      obtain ⟨u, u1, u2, u3⟩ := replace_at (R.MW i (sg0 D A)) _ _ _ _ hio hinj τ (hM.order i τ) χ _ c1 c2 v w (a1 τ) a3
      refine ⟨Function.update v τ u, fun ρ => ?_, fun ρ hρ => ?_, u3⟩
      · by_cases e : ρ = τ
        · subst e; rwa [Function.update_self]
        · rw [Function.update_of_ne e]; exact a1 ρ
      · by_cases e : ρ = τ
        · subst e; rwa [Function.update_self]
        · rw [Function.update_of_ne e]; exact a2 ρ ((Finset.mem_insert.1 hρ).resolve_left e)
  obtain ⟨v, a1, a2, a3⟩ := ind Finset.univ
  exact ⟨fun ρ => v ρ, fun ρ => ⟨a1 ρ, (v ρ).2, a2 ρ (Finset.mem_univ ρ)⟩, v, w, fun _ => rfl, hw, a3⟩

end GlobalTheory.IoExtremal

end
