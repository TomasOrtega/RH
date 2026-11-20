import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TaylorStrat

def idl (K : Type) [Field K] : Ideal K⟦X⟧⟦X⟧ := Ideal.span {C (X : K⟦X⟧), X}

/- English proof (translation)
Introduce `h`. Establish `hle : idl K ≤ RingHom.ker ((constantCoeff : K⟦X⟧ →+* K).comp (constantCoeff : K⟦X⟧⟦X⟧ →+* K⟦X⟧))`. Rewrite using `[idl, Ideal.span_le]`. Apply the tactic sequence `rintro x (rfl | rfl) <;> simp`. Establish `h1` using `hle (h ▸ Submodule.mem_top : (1 : K⟦X⟧⟦X⟧) ∈ idl K)`.

Simplify using `at h1`.
-/
theorem idl_ne_top (K : Type) [Field K] : idl K ≠ ⊤ := by
  intro h
  have hle : idl K ≤ RingHom.ker ((constantCoeff : K⟦X⟧ →+* K).comp (constantCoeff : K⟦X⟧⟦X⟧ →+* K⟦X⟧)) := by
    rw [idl, Ideal.span_le]
    rintro x (rfl | rfl) <;> simp
  have h1 := hle (h ▸ Submodule.mem_top : (1 : K⟦X⟧⟦X⟧) ∈ idl K)
  simp at h1

/- English proof (translation)
Use `Ideal.iInf_pow_eq_bot_of_isDomain (idl K) (idl_ne_top K)` as an intermediate fact. Rewrite using `[← Ideal.mem_bot, ← this, Ideal.mem_iInf]`. Conclude with `h`.
-/
theorem eq_zero_of_forall_mem {K : Type} [Field K] {g : K⟦X⟧⟦X⟧} (h : ∀ m, g ∈ idl K ^ m) : g = 0 := by
  have := Ideal.iInf_pow_eq_bot_of_isDomain (idl K) (idl_ne_top K)
  rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]
  exact h

/- English proof (translation)
Take `⟨c, rfl⟩` from `X_dvd_iff.2 h`. Conclude with `Ideal.mul_mem_right c _ (Ideal.subset_span (by simp))`.
-/
theorem mem_idl_of_constantCoeff {K : Type} [Field K] {g : K⟦X⟧⟦X⟧} (h : constantCoeff g = 0) :
    g ∈ idl K := by
  obtain ⟨c, rfl⟩ := X_dvd_iff.2 h
  exact Ideal.mul_mem_right c _ (Ideal.subset_span (by simp))

/- English proof (translation)
Use `ext1 i`. Break down `i with _ | i` into its components or cases. Simplify using `using hsh f 0`. Establish `h` using `hsh f (i + 1)`. Rewrite `h` using `[Function.iterate_succ_apply, hf, Function.iterate_fixed (map_zero _)]`.

Establish `hne : ((i + 1).factorial : K⟦X⟧) ≠ 0`. Introduce `h0`. Use `congrArg (constantCoeff : K⟦X⟧ →+* K) h0` as an intermediate fact. Simplify using `[Nat.factorial_ne_zero] at this`. Rewrite using `[coeff_C, if_neg (by omega)]`.

Conclude with `(mul_eq_zero.1 h).resolve_left hne`.
-/
theorem taylor_eq_C {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f)
    (f : K⟦X⟧) (hf : PowerSeries.derivative K f = 0) : sh f = C f := by
  ext1 i
  rcases i with _ | i
  · simpa using hsh f 0
  · have h := hsh f (i + 1)
    rw [Function.iterate_succ_apply, hf, Function.iterate_fixed (map_zero _)] at h
    have hne : ((i + 1).factorial : K⟦X⟧) ≠ 0 := by
      intro h0
      have := congrArg (constantCoeff : K⟦X⟧ →+* K) h0
      simp [Nat.factorial_ne_zero] at this
    rw [coeff_C, if_neg (by omega)]
    exact (mul_eq_zero.1 h).resolve_left hne

/- English proof (translation)
Use `ext1 i`. Break down `i with _ | _ | i` into its components or cases. Simplify using `using hsh X 0`. Simplify using `using hsh X 1`. Establish `h` using `hsh X (i + 2)`.

Rewrite `h` using `[Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_X, Derivation.map_one_eq_zero, Function.iterate_fixed (map_zero _)]`. Establish `hne : ((i + 2).factorial : K⟦X⟧) ≠ 0`. Introduce `h0`. Use `congrArg (constantCoeff : K⟦X⟧ →+* K) h0` as an intermediate fact. Simplify using `[Nat.factorial_ne_zero] at this`.

Rewrite using `[map_add, coeff_C, coeff_X, if_neg (by omega), if_neg (by omega), add_zero]`. Conclude with `(mul_eq_zero.1 h).resolve_left hne`.
-/
theorem taylor_X {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) :
    sh X = C X + X := by
  ext1 i
  rcases i with _ | _ | i
  · simpa using hsh X 0
  · simpa using hsh X 1
  · have h := hsh X (i + 2)
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_X, Derivation.map_one_eq_zero,
      Function.iterate_fixed (map_zero _)] at h
    have hne : ((i + 2).factorial : K⟦X⟧) ≠ 0 := by
      intro h0
      have := congrArg (constantCoeff : K⟦X⟧ →+* K) h0
      simp [Nat.factorial_ne_zero] at this
    rw [map_add, coeff_C, coeff_X, if_neg (by omega), if_neg (by omega), add_zero]
    exact (mul_eq_zero.1 h).resolve_left hne

end GlobalTheory.TaylorStrat

namespace GlobalTheory.TaylorStrat

/- English proof (translation)
Establish `hCm : (C (X : K⟦X⟧) : K⟦X⟧⟦X⟧) ∈ idl K` using `Ideal.subset_span (by simp)`. Establish `hXm : (X : K⟦X⟧⟦X⟧) ∈ idl K` using `Ideal.subset_span (by simp)`. Establish `h1 : (idl K).map φ₂ ≤ idl K ^ l`. Rewrite using `[Ideal.map_le_iff_le_comap, idl, Ideal.span_le]`. Apply the tactic sequence `rintro x (rfl | rfl) <;> simp only [SetLike.mem_coe, Ideal.mem_comap]`.

Rewrite using `[hC]`. Conclude with `Ideal.pow_mem_pow hCm l`. Establish `hφX : φ₂ (X : K⟦X⟧⟦X⟧) = (C X + X) ^ l - C X ^ l` using `(congrArg φ₂ (by rw [hshX]; ring : (X : K⟦X⟧⟦X⟧) = sh X - C X)).trans (by rw [map_sub, hsh, hC, hshX])`. Rewrite using `[hφX]`. Conclude with `sub_mem (Ideal.pow_mem_pow (add_mem hCm hXm) l) (Ideal.pow_mem_pow hCm l)`.

Establish `h2` using `Ideal.mem_map_of_mem φ₂ hg`. Rewrite `h2` using `[Ideal.map_pow]`. Rewrite using `[pow_mul]`. Conclude with `Ideal.pow_right_mono h1 m h2`.
-/
theorem map_idl_pow_le {K : Type} [Field K] (l : ℕ) (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hshX : sh X = C X + X) (hC : φ₂ (C X) = C X ^ l) (hsh : φ₂ (sh X) = sh X ^ l)
    (m : ℕ) {g : K⟦X⟧⟦X⟧} (hg : g ∈ idl K ^ m) : φ₂ g ∈ idl K ^ (l * m) := by
  have hCm : (C (X : K⟦X⟧) : K⟦X⟧⟦X⟧) ∈ idl K := Ideal.subset_span (by simp)
  have hXm : (X : K⟦X⟧⟦X⟧) ∈ idl K := Ideal.subset_span (by simp)
  have h1 : (idl K).map φ₂ ≤ idl K ^ l := by
    rw [Ideal.map_le_iff_le_comap, idl, Ideal.span_le]
    rintro x (rfl | rfl) <;> simp only [SetLike.mem_coe, Ideal.mem_comap]
    · rw [hC]
      exact Ideal.pow_mem_pow hCm l
    · have hφX : φ₂ (X : K⟦X⟧⟦X⟧) = (C X + X) ^ l - C X ^ l :=
        (congrArg φ₂ (by rw [hshX]; ring : (X : K⟦X⟧⟦X⟧) = sh X - C X)).trans
          (by rw [map_sub, hsh, hC, hshX])
      rw [hφX]
      exact sub_mem (Ideal.pow_mem_pow (add_mem hCm hXm) l) (Ideal.pow_mem_pow hCm l)
  have h2 := Ideal.mem_map_of_mem φ₂ hg
  rw [Ideal.map_pow] at h2
  rw [pow_mul]
  exact Ideal.pow_right_mono h1 m h2

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `J.sum_mem fun k _ => J.mul_mem_right _ ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Conclude with `J.sum_mem fun p _ => J.mul_mem_left _ (hN p k)`.
-/
theorem mul_mul_mem {R : Type} [CommRing R] {ι : Type} [Fintype ι] (J : Ideal R) (A N B : Matrix ι ι R)
    (hN : ∀ i j, N i j ∈ J) (i j : ι) : (A * N * B) i j ∈ J := by
  rw [Matrix.mul_apply]
  refine J.sum_mem fun k _ => J.mul_mem_right _ ?_
  rw [Matrix.mul_apply]
  exact J.sum_mem fun p _ => J.mul_mem_left _ (hN p k)

end GlobalTheory.TaylorStrat

open GlobalTheory.TaylorStrat in

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P sh φ₂ hsh hφC hφsh ε hε0 hε τ n i j`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective`. Establish `hl2 : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hshX` using `taylor_X sh hsh`. Establish `hshC : ∀ c : K, sh (C c) = C (C c)` using `fun c => taylor_eq_C sh hsh _ (by simp)`.

Establish `hcc : ∀ f, constantCoeff (sh f) = f` using `fun f => by simpa using hsh f 0`. Establish `hCX : φ₂ (C X) = C X ^ l` using `by rw [hφC, frob_X, map_pow]`. Establish `hshl : φ₂ (sh X) = sh X ^ l` using `by rw [hφsh, frob_X, map_pow]`. Establish `hXi : ∀ τ, P.xiMat τ * (P.xiMat τ)⁻¹ = 1` using `fun τ => Matrix.mul_nonsing_inv _ (P.isUnit_det_xiMat τ)`. Set `W : ZMod a → Matrix ι ι K⟦X⟧` to `fun τ => (P.xiMat τ)⁻¹ * P.mx τ`.

Set `Y : ZMod a → Matrix ι ι K⟦X⟧` to `fun τ => P.mxInv τ * P.xiMat τ`. Set `ε₀ : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧` to `fun τ => (Y τ).map C * (W τ).map sh`. Establish `hYW : ∀ τ, Y τ * W τ = 1`. Introduce `τ`. Simplify using `only [Y, W]`.

Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (P.xiMat τ), hXi, Matrix.one_mul, P.mxInv_mul_mx]`. Establish `h00 : ∀ τ, (ε₀ τ).map constantCoeff = 1`. Introduce `τ`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `congrFun (congrFun (hYW τ) i) j` as an intermediate fact.

Simplify `this` using `[ε₀, Matrix.mul_apply, hcc]`. Establish `hrel : ∀ τ, ε₀ τ * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map C * (ε₀ (τ - 1)).map φ₂`. Introduce `τ`. Establish `F1 : ∀ M : Matrix ι ι K⟦X⟧, φ₂.mapMatrix (C.mapMatrix M) = C.mapMatrix ((frob K l).mapMatrix M)`. Introduce `M`.

Use `ext1 p q`. Simplify using `[hφC]`. Establish `F2 : ∀ M : Matrix ι ι K⟦X⟧, φ₂.mapMatrix (sh.mapMatrix M) = sh.mapMatrix ((frob K l).mapMatrix M)`. Introduce `M`. Use `ext1 p q`.

Simplify using `[hφsh]`. Establish `F3 : ∀ M : Matrix ι ι K, sh.mapMatrix ((C : K →+* K⟦X⟧).mapMatrix M) = (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((C : K →+* K⟦X⟧).mapMatrix M)`. Introduce `M`. Use `ext1 p q`. Simplify using `[hshC]`.

Establish `hM` using `P.mx_mul_xiMat τ`. Rewrite `hM` using `[← AlgHom.mapMatrix_apply, ← RingHom.mapMatrix_apply]`. Establish `hFXi : (frob K l).mapMatrix (P.xiMat (τ - 1)) * (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ = 1`. Rewrite using `[← map_mul, hXi, map_one]`. Establish `hW : W τ = (C : K →+* K⟦X⟧).mapMatrix (P.mx0 τ) * (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, hFXi, Matrix.mul_one]`. Use `_ = _ := by`. Rewrite using `[hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (P.isUnit_det_xiMat τ), Matrix.one_mul]`. Establish `hY : Y τ = (frob K l).mapMatrix (P.xiMat (τ - 1)) * (C : K →+* K⟦X⟧).mapMatrix ((P.mxInv τ).map constantCoeff)`.

Establish `h1 : P.xiMat τ = P.mx τ * (frob K l).mapMatrix (P.xiMat (τ - 1)) * (C : K →+* K⟦X⟧).mapMatrix ((P.mxInv τ).map constantCoeff)`. Rewrite using `[hM, Matrix.mul_assoc, ← map_mul, P.matrix_mul_inv_const_eq_one, map_one, Matrix.mul_one]`. Use `show P.mxInv τ * P.xiMat τ = _`. Rewrite using `[h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, P.mxInv_mul_mx, Matrix.one_mul]`. Simplify using `only [ε₀, ← RingHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply]`.

Rewrite using `[hW, hY]`. Simplify using `only [Y, W, map_mul, F1, F2, Matrix.mul_assoc]`. Rewrite using `[F3, ← Matrix.mul_assoc ((C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((C : K →+* K⟦X⟧).mapMatrix _)), ← map_mul, ← map_mul, P.inv_const_mul_matrix_eq_one, map_one, map_one, Matrix.one_mul, ← Matrix.mul_assoc ((C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mx _)))]`. Establish `hc : (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mx (τ - 1))) * (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mxInv (τ - 1))) = 1`. Rewrite using `[← map_mul, ← map_mul, P.mx_mul_mxInv, map_one, map_one]`.

Rewrite using `[hc, Matrix.one_mul]`. Establish `hinv : ∀ τ, ((P.mx (τ - 1)).map (frob K l)).map sh * ((P.mxInv (τ - 1)).map (frob K l)).map sh = 1`. Introduce `τ`. Rewrite using `[← Matrix.map_mul, ← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, P.mx_mul_mxInv, map_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hδ : ∀ τ, ε τ - ε₀ τ = ((P.mx (τ - 1)).map (frob K l)).map C * (ε (τ - 1) - ε₀ (τ - 1)).map φ₂ * ((P.mxInv (τ - 1)).map (frob K l)).map sh`.

Introduce `τ`. Establish `h1 : (ε τ - ε₀ τ) * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map C * (ε (τ - 1) - ε₀ (τ - 1)).map φ₂`. Rewrite using `[Matrix.sub_mul, hε, hrel, ← Matrix.mul_sub, Matrix.map_sub _ (map_sub φ₂)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hmem : ∀ m τ i j, (ε τ - ε₀ τ) i j ∈ idl K ^ (m + 1)`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `τ i j`. Rewrite using `[zero_add, pow_one]`.

Apply `mem_idl_of_constantCoeff` to reduce the goal to its premises. Establish `h1` using `congrFun (congrFun (hε0 τ) i) j`. Establish `h2` using `congrFun (congrFun (h00 τ) i) j`. Simplify using `only [Matrix.map_apply] at h1 h2`. Rewrite using `[Matrix.sub_apply, map_sub, h1, h2, sub_self]`.

Consider the case `succ m ih`. Introduce `τ i j`. Rewrite using `[hδ τ]`. Apply `mul_mul_mem` to reduce the goal to its premises. Introduce `p q`.

Rewrite using `[Matrix.map_apply]`. Conclude with `Ideal.pow_le_pow_right (by nlinarith) (map_idl_pow_le l sh φ₂ hshX hCX hshl (m + 1) (ih (τ - 1) p q))`. Establish `key : ε τ = ε₀ τ`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Conclude with `sub_eq_zero.1 (eq_zero_of_forall_mem fun m => Ideal.pow_le_pow_right (Nat.le_succ m) (hmem m τ i j))`.

Establish `hphi : P.phi (bas j) = P.xiExt (fun τ => W τ *ᵥ Pi.single j 1)` using `by ext1 τ`. Rewrite using `[P.phi_apply, P.xiExt_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hXi, Matrix.one_mul]`. Use `congr 1`. Use `ext1 k`. Simplify using `[bas, Pi.single_apply]`.

Establish `hnab : ∀ (n : ℕ) (w : Vec K a ι), (P.nabla ^ n) (P.xiExt w) = P.xiExt (fun τ i => (PowerSeries.derivative K)^[n] (w τ i))`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro w`. Both sides reduce to the same expression.

Consider the case `succ n ih`. Introduce `w`. Rewrite using `[pow_succ, Module.End.mul_apply, P.nabla_xiExt, ih]`. Both sides reduce to the same expression. Rewrite using `[hphi, hnab, P.xiExt_apply, Matrix.mulVec_mulVec, key]`.

Use `show (n.factorial : K⟦X⟧) * coeff n (((Y τ).map C * (W τ).map sh) i j) = (Y τ *ᵥ fun k => (PowerSeries.derivative K)^[n] ((W τ *ᵥ Pi.single j 1) k)) i`. Rewrite using `[Matrix.mul_apply, map_sum, Finset.mul_sum, Matrix.mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, Matrix.map_apply, coeff_C_mul, mul_left_comm, hsh, Matrix.mulVec_single_one]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.TaylorStrat.stratification_coeff_eq_nabla_pow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) → (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) → ∀ (τ : ZMod a) (n : ℕ) (i j : ι), (n.factorial : K⟦X⟧) * coeff n (ε τ i j) = (P.mxInv τ *ᵥ (P.nabla ^ n) (P.phi (bas j)) τ) i := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P sh φ₂ hsh hφC hφsh ε hε0 hε τ n i j
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hshX := taylor_X sh hsh
  have hshC : ∀ c : K, sh (C c) = C (C c) := fun c => taylor_eq_C sh hsh _ (by simp)
  have hcc : ∀ f, constantCoeff (sh f) = f := fun f => by simpa using hsh f 0
  have hCX : φ₂ (C X) = C X ^ l := by rw [hφC, frob_X, map_pow]
  have hshl : φ₂ (sh X) = sh X ^ l := by rw [hφsh, frob_X, map_pow]
  have hXi : ∀ τ, P.xiMat τ * (P.xiMat τ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (P.isUnit_det_xiMat τ)
  let W : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => (P.xiMat τ)⁻¹ * P.mx τ
  let Y : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => P.mxInv τ * P.xiMat τ
  let ε₀ : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧ := fun τ => (Y τ).map C * (W τ).map sh
  have hYW : ∀ τ, Y τ * W τ = 1 := by
    intro τ
    simp only [Y, W]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (P.xiMat τ), hXi, Matrix.one_mul, P.mxInv_mul_mx]
  have h00 : ∀ τ, (ε₀ τ).map constantCoeff = 1 := by
    intro τ
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hYW τ) i) j
    simpa [ε₀, Matrix.mul_apply, hcc] using this
  have hrel : ∀ τ, ε₀ τ * ((P.mx (τ - 1)).map (frob K l)).map sh =
      ((P.mx (τ - 1)).map (frob K l)).map C * (ε₀ (τ - 1)).map φ₂ := by
    intro τ
    have F1 : ∀ M : Matrix ι ι K⟦X⟧, φ₂.mapMatrix (C.mapMatrix M) = C.mapMatrix ((frob K l).mapMatrix M) := by
      intro M; ext1 p q; simp [hφC]
    have F2 : ∀ M : Matrix ι ι K⟦X⟧, φ₂.mapMatrix (sh.mapMatrix M) = sh.mapMatrix ((frob K l).mapMatrix M) := by
      intro M; ext1 p q; simp [hφsh]
    have F3 : ∀ M : Matrix ι ι K, sh.mapMatrix ((C : K →+* K⟦X⟧).mapMatrix M) =
        (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((C : K →+* K⟦X⟧).mapMatrix M) := by
      intro M; ext1 p q; simp [hshC]
    have hM := P.mx_mul_xiMat τ
    rw [← AlgHom.mapMatrix_apply, ← RingHom.mapMatrix_apply] at hM
    have hFXi : (frob K l).mapMatrix (P.xiMat (τ - 1)) * (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ = 1 := by
      rw [← map_mul, hXi, map_one]
    have hW : W τ = (C : K →+* K⟦X⟧).mapMatrix (P.mx0 τ) * (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ := by
      calc W τ = (P.xiMat τ)⁻¹ * (P.mx τ * (frob K l).mapMatrix (P.xiMat (τ - 1))) *
            (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hFXi, Matrix.mul_one]
        _ = _ := by
          rw [hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (P.isUnit_det_xiMat τ), Matrix.one_mul]
    have hY : Y τ = (frob K l).mapMatrix (P.xiMat (τ - 1)) *
        (C : K →+* K⟦X⟧).mapMatrix ((P.mxInv τ).map constantCoeff) := by
      have h1 : P.xiMat τ = P.mx τ * (frob K l).mapMatrix (P.xiMat (τ - 1)) *
          (C : K →+* K⟦X⟧).mapMatrix ((P.mxInv τ).map constantCoeff) := by
        rw [hM, Matrix.mul_assoc, ← map_mul, P.matrix_mul_inv_const_eq_one, map_one, Matrix.mul_one]
      show P.mxInv τ * P.xiMat τ = _
      rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, P.mxInv_mul_mx, Matrix.one_mul]
    simp only [ε₀, ← RingHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply]
    rw [hW, hY]
    simp only [Y, W, map_mul, F1, F2, Matrix.mul_assoc]
    rw [F3, ← Matrix.mul_assoc ((C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((C : K →+* K⟦X⟧).mapMatrix _)), ← map_mul,
      ← map_mul, P.inv_const_mul_matrix_eq_one, map_one, map_one, Matrix.one_mul,
      ← Matrix.mul_assoc ((C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mx _)))]
    have hc : (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mx (τ - 1))) *
        (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mxInv (τ - 1))) = 1 := by
      rw [← map_mul, ← map_mul, P.mx_mul_mxInv, map_one, map_one]
    rw [hc, Matrix.one_mul]
  have hinv : ∀ τ, ((P.mx (τ - 1)).map (frob K l)).map sh * ((P.mxInv (τ - 1)).map (frob K l)).map sh = 1 := by
    intro τ
    rw [← Matrix.map_mul, ← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, P.mx_mul_mxInv, map_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hδ : ∀ τ, ε τ - ε₀ τ = ((P.mx (τ - 1)).map (frob K l)).map C * (ε (τ - 1) - ε₀ (τ - 1)).map φ₂ *
      ((P.mxInv (τ - 1)).map (frob K l)).map sh := by
    intro τ
    have h1 : (ε τ - ε₀ τ) * ((P.mx (τ - 1)).map (frob K l)).map sh =
        ((P.mx (τ - 1)).map (frob K l)).map C * (ε (τ - 1) - ε₀ (τ - 1)).map φ₂ := by
      rw [Matrix.sub_mul, hε, hrel, ← Matrix.mul_sub, Matrix.map_sub _ (map_sub φ₂)]
    calc ε τ - ε₀ τ = (ε τ - ε₀ τ) * (((P.mx (τ - 1)).map (frob K l)).map sh *
          ((P.mxInv (τ - 1)).map (frob K l)).map sh) := by rw [hinv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1]
  have hmem : ∀ m τ i j, (ε τ - ε₀ τ) i j ∈ idl K ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      intro τ i j
      rw [zero_add, pow_one]
      apply mem_idl_of_constantCoeff
      have h1 := congrFun (congrFun (hε0 τ) i) j
      have h2 := congrFun (congrFun (h00 τ) i) j
      simp only [Matrix.map_apply] at h1 h2
      rw [Matrix.sub_apply, map_sub, h1, h2, sub_self]
    | succ m ih =>
      intro τ i j
      rw [hδ τ]
      apply mul_mul_mem
      intro p q
      rw [Matrix.map_apply]
      exact Ideal.pow_le_pow_right (by nlinarith) (map_idl_pow_le l sh φ₂ hshX hCX hshl (m + 1) (ih (τ - 1) p q))
  have key : ε τ = ε₀ τ := by
    refine Matrix.ext fun i j => ?_
    exact sub_eq_zero.1 (eq_zero_of_forall_mem fun m => Ideal.pow_le_pow_right (Nat.le_succ m) (hmem m τ i j))
  have hphi : P.phi (bas j) = P.xiExt (fun τ => W τ *ᵥ Pi.single j 1) := by
    ext1 τ
    rw [P.phi_apply, P.xiExt_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hXi, Matrix.one_mul]
    congr 1
    ext1 k
    simp [bas, Pi.single_apply]
  have hnab : ∀ (n : ℕ) (w : Vec K a ι), (P.nabla ^ n) (P.xiExt w) =
      P.xiExt (fun τ i => (PowerSeries.derivative K)^[n] (w τ i)) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, P.nabla_xiExt, ih]
      rfl
  rw [hphi, hnab, P.xiExt_apply, Matrix.mulVec_mulVec, key]
  show (n.factorial : K⟦X⟧) * coeff n (((Y τ).map C * (W τ).map sh) i j) =
    (Y τ *ᵥ fun k => (PowerSeries.derivative K)^[n] ((W τ *ᵥ Pi.single j 1) k)) i
  rw [Matrix.mul_apply, map_sum, Finset.mul_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, coeff_C_mul, mul_left_comm, hsh, Matrix.mulVec_single_one]
  rfl
