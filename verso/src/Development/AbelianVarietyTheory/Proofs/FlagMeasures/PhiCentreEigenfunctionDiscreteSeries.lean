import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdPartialZpow
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HWDiag
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero

open Matrix Finset Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec

noncomputable section

namespace GlobalTheory.PhiEigenfun

variable {n : ℕ}

/- English proof (translation)
Establish `key : ∀ j i : Fin n, ∑ c, algebraMap ℂ A (Q j c * P c i) = if j = i then 1 else 0`. Introduce `j i`. Rewrite using `[← map_sum]`. Establish `hji` using `congrFun (congrFun h j) i`. Rewrite `hji` using `[Matrix.mul_apply]`.

Rewrite using `[hji, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `step : ∀ c j i, algebraMap ℂ A (P c i) * N i j * algebraMap ℂ A (Q j c) = N i j * algebraMap ℂ A (Q j c * P c i)`. Introduce `c j i`. Rewrite using `[Algebra.commutes, mul_assoc, ← map_mul, mul_comm (P c i)]`.

Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, step]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun c i => N i _ * _)]`. Simplify using `only [← Finset.mul_sum, key, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_comm]`.

Simplify using the standard rewrite rules.
-/
private lemma trace_conj_map_algebraMap {A : Type} [Ring A] [Algebra ℂ A] (N : Matrix (Fin n) (Fin n) A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (h : Q * P = 1) :
    ∑ c, (P.map (algebraMap ℂ A) * N * Q.map (algebraMap ℂ A)) c c = ∑ c, N c c := by
  have key : ∀ j i : Fin n, ∑ c, algebraMap ℂ A (Q j c * P c i) = if j = i then 1 else 0 := by
    intro j i
    rw [← map_sum]
    have hji := congrFun (congrFun h j) i
    rw [Matrix.mul_apply] at hji
    rw [hji, Matrix.one_apply]
    split_ifs <;> simp
  have step : ∀ c j i, algebraMap ℂ A (P c i) * N i j * algebraMap ℂ A (Q j c) =
      N i j * algebraMap ℂ A (Q j c * P c i) := by
    intro c j i
    rw [Algebra.commutes, mul_assoc, ← map_mul, mul_comm (P c i)]
  simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, step]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun c i => N i _ * _)]
  simp only [← Finset.mul_sum, key, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[pow_succ, ih, pow_succ M (j + 1)]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[show Q * (P * (M * Q)) = M * Q by rw [← Matrix.mul_assoc, h, Matrix.one_mul]]`.
-/
private lemma conj_pow_succ {A : Type} [Ring A] (P Q M : Matrix (Fin n) (Fin n) A) (h : Q * P = 1)
    (m : ℕ) : (P * M * Q) ^ (m + 1) = P * M ^ (m + 1) * Q := by
  induction m with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ih, pow_succ M (j + 1)]
    simp only [Matrix.mul_assoc]
    rw [show Q * (P * (M * Q)) = M * Q by rw [← Matrix.mul_assoc, h, Matrix.one_mul]]

/- English proof (translation)
Establish `hQP : Q.map (algebraMap ℂ A) * P.map (algebraMap ℂ A) = 1`. Rewrite using `[← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[conj_pow_succ _ _ _ hQP, trace_conj_map_algebraMap _ P Q h]`.
-/
lemma trace_pow_conj {A : Type} [Ring A] [Algebra ℂ A] (M : Matrix (Fin n) (Fin n) A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (h : Q * P = 1) (m : ℕ) :
    ∑ c, ((P.map (algebraMap ℂ A) * M * Q.map (algebraMap ℂ A)) ^ (m + 1)) c c = ∑ c, (M ^ (m + 1)) c c := by
  have hQP : Q.map (algebraMap ℂ A) * P.map (algebraMap ℂ A) = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [conj_pow_succ _ _ _ hQP, trace_conj_map_algebraMap _ P Q h]

/- English proof (translation)
Proceed by induction on `k generalizing a b with`. Consider the case `zero => simp [epow, Matrix.one_apply]`. Consider the case `succ k ih => simp only [epow, pow_succ, Matrix.mul_apply, ih, Matrix.of_apply]`.
-/
lemma epow_eq {A : Type} [Ring A] (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    epow E k a b = (Matrix.of E ^ k) a b := by
  induction k generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ k ih => simp only [epow, pow_succ, Matrix.mul_apply, ih, Matrix.of_apply]

/- English proof (translation)
Proceed by induction on `k generalizing a with`. Consider the case `zero => simp [TrPow_m, Matrix.one_apply]`. Consider the case `succ k ih`. Establish `hsplit : ∀ c, Amat l a c * TrPow_m l k c = (if a = c then l a * TrPow_m l k c else 0) + (if a < c then -TrPow_m l k c else 0)`. Introduce `c`.

Simplify using `only [Amat, Matrix.of_apply]`. Distinguish the cases in `h1 : a = c`. Substitute `h1` using the available equality. Simplify using the standard rewrite rules. Apply the tactic sequence `by_cases h2 : a < c <;> simp [h1, h2]`.

Rewrite using `[pow_succ']`. Simplify using `only [Matrix.mul_apply]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.mul_sum, ← ih, hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, TrPow_m, Finset.sum_filter, sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma trPow_eq (l : Fin n → ℂ) (k : ℕ) (a : Fin n) : TrPow_m l k a = ∑ b, (Amat l ^ k) a b := by
  induction k generalizing a with
  | zero => simp [TrPow_m, Matrix.one_apply]
  | succ k ih =>
    have hsplit : ∀ c, Amat l a c * TrPow_m l k c =
        (if a = c then l a * TrPow_m l k c else 0) + (if a < c then -TrPow_m l k c else 0) := by
      intro c
      simp only [Amat, Matrix.of_apply]
      by_cases h1 : a = c
      · subst h1; simp
      · by_cases h2 : a < c <;> simp [h1, h2]
    rw [pow_succ']
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ← ih, hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, TrPow_m, Finset.sum_filter, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp

/- English proof (translation)
Rewrite using `[LinearMap.sum_apply, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← epow_eq, TrPow_diag generatorPowDiagRecursion_holds E ν v hE hv k c, trPow_eq]`.
-/
lemma trace_pow_hw {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V) (hE : GlRel E) (hv : IsHW E ν v) (k : ℕ) :
    (∑ c, (Matrix.of E ^ k) c c) v = (∑ a, ∑ b, (Amat (lsh ν) ^ k) a b) • v := by
  rw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← epow_eq, TrPow_diag generatorPowDiagRecursion_holds E ν v hE hv k c, trPow_eq]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro x y`. Simplify using `[Fin.snoc]`. Consider the case `succ m ih`.

Introduce `x y`. Rewrite using `[pow_succ', Matrix.mul_apply, ← (Fin.consEquiv fun _ : Fin (m + 1) => Fin n).sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun b0 _ => ?_` and prove the remaining obligations. Rewrite using `[← ih b0 y, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b' _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `try simp only [Fin.consEquiv_apply]`. Apply the tactic sequence `try dsimp only [Fin.consEquiv, Equiv.coe_fn_mk]`. Rewrite using `[← Fin.cons_snoc_eq_snoc_cons, List.ofFn_succ, List.prod_cons]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, Matrix.of_apply]`.
-/
private lemma sum_paths_list_prod {A : Type} [Ring A] (E : Fin n → Fin n → A) :
    ∀ (m : ℕ) (x y : Fin n), ∑ b : Fin m → Fin n,
      (List.ofFn fun i : Fin (m + 1) => E (Fin.cons (α := fun _ => Fin n) x b i) (Fin.snoc (α := fun _ => Fin n) b y i)).prod =
        (Matrix.of E ^ (m + 1)) x y := by
  intro m
  induction m with
  | zero => intro x y; simp [Fin.snoc]
  | succ m ih =>
    intro x y
    rw [pow_succ', Matrix.mul_apply, ← (Fin.consEquiv fun _ : Fin (m + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b0 _ => ?_
    rw [← ih b0 y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    try simp only [Fin.consEquiv_apply]
    try dsimp only [Fin.consEquiv, Equiv.coe_fn_mk]
    rw [← Fin.cons_snoc_eq_snoc_cons, List.ofFn_succ, List.prod_cons]
    simp only [Fin.cons_zero, Fin.cons_succ, Matrix.of_apply]

/- English proof (translation)
Rewrite using `[← (Fin.consEquiv fun _ : Fin (m + 1) => Fin n).sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[← sum_paths_list_prod E m x x]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.consEquiv_apply, cycWord, List.map_ofFn]`.

Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp]`. Use `congr 1`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations.

Rewrite using `[finRotate_last, Fin.snoc_last, Fin.cons_zero]`. Rewrite using `[finRotate_succ_apply, Fin.coeSucc_eq_succ, Fin.cons_succ, Fin.snoc_castSucc]`.
-/
lemma sum_cycWord {A : Type} [Ring A] (E : Fin n → Fin n → A) (m : ℕ) :
    ∑ a : Fin (m + 1) → Fin n, ((cycWord a).map fun p => E p.1 p.2).prod = ∑ c, (Matrix.of E ^ (m + 1)) c c := by
  rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← sum_paths_list_prod E m x x]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Fin.consEquiv_apply, cycWord, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp]
  congr 1
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [finRotate_last, Fin.snoc_last, Fin.cons_zero]
  · rw [finRotate_succ_apply, Fin.coeSucc_eq_succ, Fin.cons_succ, Fin.snoc_castSucc]

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

/- English proof (translation)
Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℂ) X (0 : ℂ)`. Rewrite `h` using `[zero_smul, NormedSpace.exp_zero, one_mul]`. Conclude with `hasDerivAt_iff_tendsto_slope.1 h`.
-/
lemma slope_exp (X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℂ => NormedSpace.exp (t • X)) 0) (𝓝[≠] 0) (𝓝 X) := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) X (0 : ℂ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact hasDerivAt_iff_tendsto_slope.1 h

end Linfty

section General
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def holSpace (U : Set E) : Submodule ℂ (E → ℂ) where
  carrier := {F | AnalyticOnNhd ℂ F U ∧ ∀ z ∉ U, F z = 0}
  add_mem' := fun hF hG => ⟨hF.1.add hG.1, fun z hz => by simp [hF.2 z hz, hG.2 z hz]⟩
  zero_mem' := ⟨analyticOnNhd_const, fun _ _ => rfl⟩
  smul_mem' := fun c F hF => ⟨fun z hz => (hF.1 z hz).const_smul, fun z hz => by simp [hF.2 z hz]⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Distinguish the cases in `hz : z ∈ U`. Conclude with `h z hz`. Rewrite using `[F.2.2 z hz, G.2.2 z hz]`.
-/
lemma hol_ext {U : Set E} {F G : holSpace U} (h : ∀ z ∈ U, F.1 z = G.1 z) : F = G := by
  apply Subtype.ext
  funext z
  by_cases hz : z ∈ U
  · exact h z hz
  · rw [F.2.2 z hz, G.2.2 z hz]

def mk {U : Set E} (hU : IsOpen U) (F : E → ℂ) (hF : AnalyticOnNhd ℂ F U) : holSpace U :=
  ⟨U.indicator F, fun z hz => (hF z hz).congr
    (by filter_upwards [hU.mem_nhds hz] with y hy using (Set.indicator_of_mem hy F).symm),
    fun z hz => Set.indicator_of_notMem hz F⟩

/- English proof (translation)
Use `show U.indicator F z = F z`. Conclude with `Set.indicator_of_mem hz F`.
-/
lemma mk_apply {U : Set E} (hU : IsOpen U) (F : E → ℂ)
    (hF : AnalyticOnNhd ℂ F U) {z : E} (hz : z ∈ U) : (mk hU F hF).1 z = F z := by
  show U.indicator F z = F z
  exact Set.indicator_of_mem hz F

variable [FiniteDimensional ℂ E]

/- English proof (translation)
Establish `hB` using `(ContinuousLinearMap.apply ℂ ℂ : E →L[ℂ] (E →L[ℂ] ℂ) →L[ℂ] ℂ).analyticAt_bilinear (T z, fderiv ℂ F z)`. Establish `hpair : AnalyticAt ℂ (fun y => (T y, fderiv ℂ F y)) z` using `((LinearMap.toContinuousLinearMap T).analyticAt z).prod hF.fderiv`. Conclude with `hB.comp_of_eq hpair rfl`.
-/
lemma analytic_vec {F : E → ℂ} {z : E} (hF : AnalyticAt ℂ F z)
    (T : E →ₗ[ℂ] E) : AnalyticAt ℂ (fun y => fderiv ℂ F y (T y)) z := by
  have hB := (ContinuousLinearMap.apply ℂ ℂ : E →L[ℂ] (E →L[ℂ] ℂ) →L[ℂ] ℂ).analyticAt_bilinear (T z, fderiv ℂ F z)
  have hpair : AnalyticAt ℂ (fun y => (T y, fderiv ℂ F y)) z :=
    ((LinearMap.toContinuousLinearMap T).analyticAt z).prod hF.fderiv
  exact hB.comp_of_eq hpair rfl

def vec {U : Set E} (hU : IsOpen U) : (E →ₗ[ℂ] E) →ₗ[ℂ] Module.End ℂ (holSpace U) :=
  LinearMap.mk₂ ℂ (fun T F => mk hU (fun y => fderiv ℂ F.1 y (T y)) fun z hz => analytic_vec (F.2.1 z hz) T)
    (fun X Y F => hol_ext fun z hz => by simp [mk, hz])
    (fun c X F => hol_ext fun z hz => by simp [mk, hz])
    (fun X F G => hol_ext fun z hz => by
      simp [mk, hz, fderiv_add (F.2.1 z hz).differentiableAt (G.2.1 z hz).differentiableAt])
    (fun c X F => hol_ext fun z hz => by
      simp [mk, hz, fderiv_const_smul (F.2.1 z hz).differentiableAt])

/- English proof (translation)
Simplify using `only [vec, LinearMap.mk₂_apply]`. Conclude with `mk_apply hU _ _ hz`.
-/
lemma vec_apply {U : Set E} (hU : IsOpen U) (T : E →ₗ[ℂ] E)
    (F : holSpace U) {z : E} (hz : z ∈ U) : (vec hU T F).1 z = fderiv ℂ F.1 z (T z) := by
  simp only [vec, LinearMap.mk₂_apply]
  exact mk_apply hU _ _ hz

/- English proof (translation)
Establish `hF : AnalyticAt ℂ F.1 z` using `F.2.1 z hz`. Rewrite using `[vec_apply hU S _ hz]`. Establish `heq : (vec hU T F).1 =ᶠ[𝓝 z] fun y => fderiv ℂ F.1 y (T y)` using `by filter_upwards [hU.mem_nhds hz] with y hy using vec_apply hU T F hy`. Rewrite using `[heq.fderiv_eq]`. Establish `hT : HasFDerivAt (fun y => T y) (LinearMap.toContinuousLinearMap T) z`.

Simplify using `using (LinearMap.toContinuousLinearMap T).hasFDerivAt`. Establish `h1 : DifferentiableAt ℂ (fderiv ℂ F.1) z` using `hF.fderiv.differentiableAt`. Rewrite using `[fderiv_clm_apply h1 hT.differentiableAt, hT.fderiv]`. Simplify using `only [_root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, LinearMap.coe_toContinuousLinearMap']`. Rewrite using `[add_comm]`.
-/
lemma vec_vec {U : Set E} (hU : IsOpen U) (S T : E →ₗ[ℂ] E) (F : holSpace U) {z : E} (hz : z ∈ U) :
    (vec hU S (vec hU T F)).1 z =
      fderiv ℂ (fderiv ℂ F.1) z (S z) (T z) + fderiv ℂ F.1 z (T (S z)) := by
  have hF : AnalyticAt ℂ F.1 z := F.2.1 z hz
  rw [vec_apply hU S _ hz]
  have heq : (vec hU T F).1 =ᶠ[𝓝 z] fun y => fderiv ℂ F.1 y (T y) := by
    filter_upwards [hU.mem_nhds hz] with y hy using vec_apply hU T F hy
  rw [heq.fderiv_eq]
  have hT : HasFDerivAt (fun y => T y) (LinearMap.toContinuousLinearMap T) z := by
    simpa using (LinearMap.toContinuousLinearMap T).hasFDerivAt
  have h1 : DifferentiableAt ℂ (fderiv ℂ F.1) z := hF.fderiv.differentiableAt
  rw [fderiv_clm_apply h1 hT.differentiableAt, hT.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, LinearMap.coe_toContinuousLinearMap']
  rw [add_comm]

/- English proof (translation)
Use `LinearMap.ext fun F => hol_ext fun z hz => ?_` and prove the remaining obligations. Establish `hF : AnalyticAt ℂ F.1 z` using `F.2.1 z hz`. Establish `hsymm` using `(hF.contDiffAt (n := ⊤)).isSymmSndFDerivAt le_top`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply]`. Rewrite using `[vec_vec hU S T F hz, vec_vec hU T S F hz, vec_apply hU _ F hz, vec_apply hU _ F hz, hsymm (S z) (T z)]`.

Simplify using `only [LinearMap.comp_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma vec_comm {U : Set E} (hU : IsOpen U) (S T : E →ₗ[ℂ] E) :
    vec hU S * vec hU T - vec hU T * vec hU S = vec hU (T ∘ₗ S) - vec hU (S ∘ₗ T) := by
  refine LinearMap.ext fun F => hol_ext fun z hz => ?_
  have hF : AnalyticAt ℂ F.1 z := F.2.1 z hz
  have hsymm := (hF.contDiffAt (n := ⊤)).isSymmSndFDerivAt le_top
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply]
  rw [vec_vec hU S T F hz, vec_vec hU T S F hz, vec_apply hU _ F hz, vec_apply hU _ F hz,
    hsymm (S z) (T z)]
  simp only [LinearMap.comp_apply]
  ring

/- English proof (translation)
Rewrite using `[vec_apply hU T F hz]`. Establish `hF : AnalyticAt ℂ F.1 z` using `F.2.1 z hz`. Establish `heq : f =ᶠ[𝓝 z] F.1` using `by filter_upwards [hU.mem_nhds hz] with y hy using (h y hy).symm`. Establish `hf : HasFDerivAt f (fderiv ℂ F.1 z) z` using `hF.differentiableAt.hasFDerivAt.congr_of_eventuallyEq heq`. Establish `hf0 : HasFDerivAt f (fderiv ℂ F.1 z) (γ 0)` using `by rw [h0]; exact hf`.

Conclude with `((hf0.comp_hasDerivAt 0 hγ).deriv).symm`.
-/
lemma vec_eq_deriv {U : Set E} (hU : IsOpen U) (T : E →ₗ[ℂ] E) (F : holSpace U) {f : E → ℂ}
    (h : ∀ z ∈ U, F.1 z = f z) {z : E} (hz : z ∈ U) {γ : ℂ → E} (h0 : γ 0 = z) (hγ : HasDerivAt γ (T z) 0) :
    (vec hU T F).1 z = deriv (fun t => f (γ t)) 0 := by
  rw [vec_apply hU T F hz]
  have hF : AnalyticAt ℂ F.1 z := F.2.1 z hz
  have heq : f =ᶠ[𝓝 z] F.1 := by
    filter_upwards [hU.mem_nhds hz] with y hy using (h y hy).symm
  have hf : HasFDerivAt f (fderiv ℂ F.1 z) z :=
    hF.differentiableAt.hasFDerivAt.congr_of_eventuallyEq heq
  have hf0 : HasFDerivAt f (fderiv ℂ F.1 z) (γ 0) := by rw [h0]; exact hf
  exact ((hf0.comp_hasDerivAt 0 hγ).deriv).symm

end General

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `h` using `(slope_exp X).const_mul g`. Establish `h' : Tendsto (slope (fun t : ℂ => g * NormedSpace.exp (t • X)) 0) (𝓝[≠] 0) (𝓝 (g * X))`. Use `h.congr' ?_` and prove the remaining obligations. Use `filter_upwards with t`. Simplify using `only [slope_def_module, Matrix.mul_smul, Matrix.mul_sub]`.

Conclude with `hasDerivAt_iff_tendsto_slope.2 h'`.
-/
lemma hasDerivAt_curve (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℂ => g * NormedSpace.exp (t • X)) (g * X) 0 := by
  have h := (slope_exp X).const_mul g
  have h' : Tendsto (slope (fun t : ℂ => g * NormedSpace.exp (t • X)) 0) (𝓝[≠] 0) (𝓝 (g * X)) := by
    refine h.congr' ?_
    filter_upwards with t
    simp only [slope_def_module, Matrix.mul_smul, Matrix.mul_sub]
  exact hasDerivAt_iff_tendsto_slope.2 h'

def der {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (holSpace U) :=
  vec hU ∘ₗ (LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip

/- English proof (translation)
Establish `e1 : (LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip Y ∘ₗ (LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip X = (LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip (X * Y)` using `LinearMap.ext fun y => by simp [Matrix.mul_assoc]`. Establish `e2 : (LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip X ∘ₗ (LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip Y = (LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip (Y * X)` using `LinearMap.ext fun y => by simp [Matrix.mul_assoc]`. Simplify using `only [der, LinearMap.comp_apply]`. Rewrite using `[← e1, ← e2]`. Conclude with `vec_comm hU _ _`.
-/
lemma der_comm {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    der hU X * der hU Y - der hU Y * der hU X = der hU (X * Y) - der hU (Y * X) := by
  have e1 : (LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip Y ∘ₗ (LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip X =
      (LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip (X * Y) :=
    LinearMap.ext fun y => by simp [Matrix.mul_assoc]
  have e2 : (LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip X ∘ₗ (LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip Y =
      (LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip (Y * X) :=
    LinearMap.ext fun y => by simp [Matrix.mul_assoc]
  simp only [der, LinearMap.comp_apply]
  rw [← e1, ← e2]
  exact vec_comm hU _ _

/- English proof (translation)
Introduce `a b c d`. Simplify using `only`. Rewrite using `[der_comm]`. Establish `hmul : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, k * X * k' * (k * Y * k') = k * (X * Y) * k'`. Introduce `X Y`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc k' k, h, Matrix.one_mul]`. Establish `hs : ∀ a b c d : Fin n, Matrix.single a b (1 : ℂ) * Matrix.single c d 1 = if b = c then Matrix.single a d 1 else 0`. Introduce `a b c d`. Use `split_ifs with hbc`.

Substitute `hbc` using the available equality. Simplify using `[Matrix.single_mul_single_same]`. Simplify using `[Matrix.single_mul_single_of_ne, hbc]`. Rewrite using `[hmul, hmul, hs, hs]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma glRel_conj {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U) (k k' : Matrix (Fin n) (Fin n) ℂ)
    (h : k' * k = 1) : GlRel (fun a b => der hU (k * Matrix.single a b 1 * k')) := by
  intro a b c d
  simp only
  rw [der_comm]
  have hmul : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, k * X * k' * (k * Y * k') = k * (X * Y) * k' := by
    intro X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc k' k, h, Matrix.one_mul]
  have hs : ∀ a b c d : Fin n, Matrix.single a b (1 : ℂ) * Matrix.single c d 1 =
      if b = c then Matrix.single a d 1 else 0 := by
    intro a b c d
    split_ifs with hbc
    · subst hbc; simp [Matrix.single_mul_single_same]
    · simp [Matrix.single_mul_single_of_ne, hbc]
  rw [hmul, hmul, hs, hs]
  split_ifs <;> simp

/- English proof (translation)
Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Establish `hk : k * Matrix.single a b (1 : ℂ) * k' = ∑ j, ∑ i, (k i a * k' b j) • Matrix.single i j (1 : ℂ)`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']`. Simplify using `only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul]`.

Rewrite using `[hk, map_sum]`. Simplify using `only [map_sum, map_smul, Finset.smul_sum, smul_smul]`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
lemma of_conj {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U) (k k' : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.of (fun a b => der hU (k * Matrix.single a b 1 * k')) =
      kᵀ.map (algebraMap ℂ _) * Matrix.of (fun a b => der hU (Matrix.single a b 1)) * k'ᵀ.map (algebraMap ℂ _) := by
  refine Matrix.ext fun a b => ?_
  have hk : k * Matrix.single a b (1 : ℂ) * k' =
      ∑ j, ∑ i, (k i a * k' b j) • Matrix.single i j (1 : ℂ) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and, ite_mul, Finset.sum_ite_eq,
      Finset.sum_ite_eq']
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
    smul_smul]
  rw [hk, map_sum]
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => intro z hz`. Simplify `h z hz` using `[RholW]`. Consider the case `cons p w ih`. Introduce `z hz`.

Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply]`. Conclude with `vec_eq_deriv hU ((LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip (Matrix.single p.1 p.2 1)) _ ih hz (γ := fun t => z * NormedSpace.exp (t • Matrix.single p.1 p.2 (1 : ℂ))) (by simp) (hasDerivAt_curve z _)`.
-/
lemma rholW_apply {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U) (w : List (Fin n × Fin n))
    (F : holSpace U) {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ z ∈ U, F.1 z = f z) :
    ∀ z ∈ U, ((w.map fun p => der hU (Matrix.single p.1 p.2 1)).prod F).1 z = RholW w f z := by
  induction w with
  | nil => intro z hz; simpa [RholW] using h z hz
  | cons p w ih =>
    intro z hz
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact vec_eq_deriv hU ((LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip (Matrix.single p.1 p.2 1)) _ ih hz
      (γ := fun t => z * NormedSpace.exp (t • Matrix.single p.1 p.2 (1 : ℂ))) (by simp) (hasDerivAt_curve z _)

/- English proof (translation)
Establish `hco : ∀ x w : Fin n, AnalyticAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => y x w) z` using `fun x w => ((ContinuousLinearMap.proj w).comp (ContinuousLinearMap.proj x : (Fin n → Fin n → ℂ) →L[ℂ] (Fin n → ℂ))).analyticAt z`. Establish `hent : ∀ p q : Fin n, AnalyticAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => (k' * y * k) p q) z`. Introduce `p q`. Establish `H` using `Finset.analyticAt_sum (𝕜 := ℂ) (c := z) Finset.univ (fun w _ => (Finset.analyticAt_sum (𝕜 := ℂ) (c := z) Finset.univ (fun x _ => (analyticAt_const (v := k' p x)).mul (hco x w))).mul (analyticAt_const (v := k w q)))`. Use `H.congr (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Simplify using `[Matrix.mul_apply, Finset.sum_apply]`. Unfold `leadMinor`. Simplify using `only [Matrix.det_apply', Matrix.submatrix_apply]`. Establish `H` using `Finset.analyticAt_sum (𝕜 := ℂ) (c := z) Finset.univ (fun σ _ => (analyticAt_const (v := (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ))).mul (Finset.analyticAt_prod (c := z) Finset.univ fun i _ => hent (Fin.castLE hl (σ i)) (Fin.castLE hl i)))`. Use `H.congr (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Simplify using `[Finset.sum_apply, Finset.prod_apply]`.
-/
lemma analytic_minor (k k' : Matrix (Fin n) (Fin n) ℂ) (l : ℕ) (hl : l ≤ n) (z : Matrix (Fin n) (Fin n) ℂ) :
    AnalyticAt ℂ (fun y => leadMinor (k' * y * k) l hl) z := by
  have hco : ∀ x w : Fin n, AnalyticAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => y x w) z := fun x w =>
    ((ContinuousLinearMap.proj w).comp
      (ContinuousLinearMap.proj x : (Fin n → Fin n → ℂ) →L[ℂ] (Fin n → ℂ))).analyticAt z
  have hent : ∀ p q : Fin n, AnalyticAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => (k' * y * k) p q) z := by
    intro p q
    have H := Finset.analyticAt_sum (𝕜 := ℂ) (c := z) Finset.univ (fun w _ =>
      (Finset.analyticAt_sum (𝕜 := ℂ) (c := z) Finset.univ
        (fun x _ => (analyticAt_const (v := k' p x)).mul (hco x w))).mul (analyticAt_const (v := k w q)))
    refine H.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [Matrix.mul_apply, Finset.sum_apply]
  unfold leadMinor
  simp only [Matrix.det_apply', Matrix.submatrix_apply]
  have H := Finset.analyticAt_sum (𝕜 := ℂ) (c := z) Finset.univ (fun σ _ =>
    (analyticAt_const (v := (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ))).mul
      (Finset.analyticAt_prod (c := z) Finset.univ fun i _ => hent (Fin.castLE hl (σ i)) (Fin.castLE hl i)))
  refine H.congr (Filter.Eventually.of_forall fun y => ?_)
  simp [Finset.sum_apply, Finset.prod_apply]

/- English proof (translation)
Establish `hset : {y | k' * y * k ∈ Omega n} = ⋂ i : Fin n, {y | leadMinor (k' * y * k) (i.val + 1) i.isLt ≠ 0}`. Use extensionality with `y`. Simplify using `[Omega]`. Rewrite using `[hset]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_iff_continuousAt.2 fun z => (analytic_minor k k' _ _ z).continuousAt) continuous_const`.
-/
lemma isOpen_conj (k k' : Matrix (Fin n) (Fin n) ℂ) : IsOpen {y | k' * y * k ∈ Omega n} := by
  have hset : {y | k' * y * k ∈ Omega n} =
      ⋂ i : Fin n, {y | leadMinor (k' * y * k) (i.val + 1) i.isLt ≠ 0} := by
    ext y; simp [Omega]
  rw [hset]
  exact isOpen_iInter_of_finite fun i => isOpen_ne_fun
    (continuous_iff_continuousAt.2 fun z => (analytic_minor k k' _ _ z).continuousAt) continuous_const

/- English proof (translation)
Introduce `z hz`. Establish `hz' : ∀ i : Fin n, leadMinor (k' * z * k) (i.val + 1) i.isLt ≠ 0` using `hz`. Unfold `Phi`. Establish `H` using `Finset.analyticAt_prod (c := z) Finset.univ fun i _ => (analytic_minor k k' (i.val + 1) i.isLt z).zpow (hz' i) (n := -(sInt lam i))`. Use `H.congr (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Simplify using `[Finset.prod_apply]`.
-/
lemma analytic_Phi (lam : Fin n → ℝ) (k k' : Matrix (Fin n) (Fin n) ℂ) :
    AnalyticOnNhd ℂ (fun y => Phi lam (k' * y * k)) {y | k' * y * k ∈ Omega n} := by
  intro z hz
  have hz' : ∀ i : Fin n, leadMinor (k' * z * k) (i.val + 1) i.isLt ≠ 0 := hz
  unfold Phi
  have H := Finset.analyticAt_prod (c := z) Finset.univ fun i _ =>
    (analytic_minor k k' (i.val + 1) i.isLt z).zpow (hz' i) (n := -(sInt lam i))
  refine H.congr (Filter.Eventually.of_forall fun y => ?_)
  simp [Finset.prod_apply]

/- English proof (translation)
Establish `hup : IsUp (1 + t • Matrix.single a b (1 : ℂ))`. Introduce `i j hji`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne hji.ne', Matrix.smul_apply, Matrix.single_apply, if_neg]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `absurd hab (not_le.2 hji)`. Establish `hlo : IsLo (1 : Matrix (Fin n) (Fin n) ℂ)` using `fun i j hij => Matrix.one_apply_ne hij.ne`. Establish `hdiag : ∀ l, (1 + t • Matrix.single a b (1 : ℂ)) l l = if a = b ∧ l = a then 1 + t else 1`. Introduce `l`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, Matrix.single_apply]`.

Establish `hiff : (a = l ∧ b = l) ↔ (a = b ∧ l = a)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `⟨rfl, rfl⟩`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `⟨rfl, rfl⟩`. Distinguish the cases in `hc : a = b ∧ l = a`. Rewrite using `[if_pos (hiff.2 hc), if_pos hc]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun h5 => hc (hiff.1 h5)), if_neg hc]`.

Simplify using the standard rewrite rules. Establish `hne : ∀ l, (1 : Matrix (Fin n) (Fin n) ℂ) l l ≠ 0 ∧ (1 + t • Matrix.single a b (1 : ℂ)) l l ≠ 0`. Introduce `l`. Use `⟨by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[hdiag]`.

Use `split_ifs`. Conclude with `ht`. Conclude with `one_ne_zero`. Take `⟨-, hP⟩` from `GlobalTheory.PhiTriangular.phiTri n lam 1 z (1 + t • Matrix.single a b 1) hlo hup hne hz`. Rewrite `hP` using `[Matrix.one_mul]`.

Rewrite using `[hP]`. Use `congr 1`. Simplify using `only [Matrix.one_apply_eq, one_mul, hdiag]`. Distinguish the cases in `hab' : a = b`. Substitute `hab'` using the available equality.

Simplify using `only [true_and, if_true]`. Rewrite using `[Finset.prod_eq_single a (fun l _ hl => by simp [hl]) (by simp)]`. Simplify using the standard rewrite rules. Simplify using `[hab']`.
-/
lemma Phi_mul_single (lam : Fin n → ℝ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Omega n) {a b : Fin n}
    (hab : a ≤ b) {t : ℂ} (ht : 1 + t ≠ 0) :
    Phi lam (z * (1 + t • Matrix.single a b 1)) =
      (if a = b then (1 + t) ^ (-(muInt lam a)) else 1) * Phi lam z := by
  have hup : IsUp (1 + t • Matrix.single a b (1 : ℂ)) := by
    intro i j hji
    rw [Matrix.add_apply, Matrix.one_apply_ne hji.ne', Matrix.smul_apply, Matrix.single_apply, if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩
      exact absurd hab (not_le.2 hji)
  have hlo : IsLo (1 : Matrix (Fin n) (Fin n) ℂ) := fun i j hij => Matrix.one_apply_ne hij.ne
  have hdiag : ∀ l, (1 + t • Matrix.single a b (1 : ℂ)) l l = if a = b ∧ l = a then 1 + t else 1 := by
    intro l
    rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, Matrix.single_apply]
    have hiff : (a = l ∧ b = l) ↔ (a = b ∧ l = a) := by
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    by_cases hc : a = b ∧ l = a
    · rw [if_pos (hiff.2 hc), if_pos hc]; simp
    · rw [if_neg (fun h5 => hc (hiff.1 h5)), if_neg hc]; simp
  have hne : ∀ l, (1 : Matrix (Fin n) (Fin n) ℂ) l l ≠ 0 ∧ (1 + t • Matrix.single a b (1 : ℂ)) l l ≠ 0 := by
    intro l
    refine ⟨by simp, ?_⟩
    rw [hdiag]
    split_ifs
    · exact ht
    · exact one_ne_zero
  obtain ⟨-, hP⟩ := GlobalTheory.PhiTriangular.phiTri n lam 1 z (1 + t • Matrix.single a b 1) hlo hup hne hz
  rw [Matrix.one_mul] at hP
  rw [hP]
  congr 1
  simp only [Matrix.one_apply_eq, one_mul, hdiag]
  by_cases hab' : a = b
  · subst hab'
    simp only [true_and, if_true]
    rw [Finset.prod_eq_single a (fun l _ hl => by simp [hl]) (by simp)]
    simp
  · simp [hab']

/- English proof (translation)
Apply `hol_ext` to reduce the goal to its premises. Introduce `z hz`. Establish `hz' : k' * z * k ∈ Omega n` using `hz`. Simplify using `only [der, LinearMap.comp_apply]`. Establish `hγ : HasDerivAt (fun t : ℂ => z + t • (z * (k * Matrix.single a b (1 : ℂ) * k'))) (((LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip (k * Matrix.single a b 1 * k')) z) 0`.

Establish `h3` using `((hasDerivAt_id (0 : ℂ)).smul_const (z * (k * Matrix.single a b (1 : ℂ) * k'))).const_add z`. Rewrite `h3` using `[one_smul]`. Conclude with `h3`. Use `Eq.trans (vec_eq_deriv (isOpen_conj k k') _ _ (f := fun y => Phi lam (k' * y * k)) (fun y hy => mk_apply _ _ _ hy) hz (by simp) hγ) ?_` and prove the remaining obligations. Establish `hm : (mk (isOpen_conj k k') _ (analytic_Phi lam k k')).1 z = Phi lam (k' * z * k)` using `mk_apply _ _ _ hz`.

Rewrite using `[Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hm]`. Establish `hfun : (fun t : ℂ => Phi lam (k' * (z + t • (z * (k * Matrix.single a b (1 : ℂ) * k'))) * k)) = fun t => Phi lam (k' * z * k * (1 + t • Matrix.single a b 1))`. Use function extensionality and compare the values at `t`. Use `congr 1`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h, Matrix.mul_one]`.

Rewrite using `[hfun]`. Establish `hev : (fun t : ℂ => Phi lam (k' * z * k * (1 + t • Matrix.single a b 1))) =ᶠ[𝓝 0] fun t => (if a = b then (1 + t) ^ (-(muInt lam a)) else 1) * Phi lam (k' * z * k)`. Establish `hc : ∀ᶠ t in 𝓝 (0 : ℂ), 1 + t ≠ 0`. Establish `hcont : ContinuousAt (fun t : ℂ => 1 + t) 0` using `by fun_prop`. Conclude with `hcont.eventually_ne (by norm_num)`.

Use `filter_upwards [hc] with t ht using Phi_mul_single lam hz' hab ht`. Rewrite using `[hev.deriv_eq]`. Distinguish the cases in `hab' : a = b`. Substitute `hab'` using the available equality. Simplify using `only [if_true]`.

Establish `hd : HasDerivAt (fun t : ℂ => (1 + t) ^ (-(muInt lam a))) (((-(muInt lam a) : ℤ) : ℂ) * (1 + 0) ^ (-(muInt lam a) - 1) * 1) 0` using `(hasDerivAt_zpow (-(muInt lam a)) (1 + 0 : ℂ) (Or.inl (by norm_num))).comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_add 1)`. Rewrite using `[(hd.mul_const (Phi lam (k' * z * k))).deriv]`. Simplify using the standard rewrite rules. Simplify using `[hab']`.
-/
lemma der_Phi (lam : Fin n → ℝ) (k k' : Matrix (Fin n) (Fin n) ℂ) (h : k' * k = 1) {a b : Fin n} (hab : a ≤ b) :
    der (isOpen_conj k k') (k * Matrix.single a b 1 * k') (mk (isOpen_conj k k') _ (analytic_Phi lam k k')) =
      (if a = b then -(muInt lam a : ℂ) else 0) • mk (isOpen_conj k k') _ (analytic_Phi lam k k') := by
  apply hol_ext
  intro z hz
  have hz' : k' * z * k ∈ Omega n := hz
  simp only [der, LinearMap.comp_apply]
  have hγ : HasDerivAt (fun t : ℂ => z + t • (z * (k * Matrix.single a b (1 : ℂ) * k')))
      (((LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip (k * Matrix.single a b 1 * k')) z) 0 := by
    have h3 := ((hasDerivAt_id (0 : ℂ)).smul_const (z * (k * Matrix.single a b (1 : ℂ) * k'))).const_add z
    rw [one_smul] at h3
    exact h3
  refine Eq.trans (vec_eq_deriv (isOpen_conj k k') _ _ (f := fun y => Phi lam (k' * y * k))
    (fun y hy => mk_apply _ _ _ hy) hz (by simp) hγ) ?_
  have hm : (mk (isOpen_conj k k') _ (analytic_Phi lam k k')).1 z = Phi lam (k' * z * k) := mk_apply _ _ _ hz
  rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hm]
  have hfun : (fun t : ℂ => Phi lam (k' * (z + t • (z * (k * Matrix.single a b (1 : ℂ) * k'))) * k)) =
      fun t => Phi lam (k' * z * k * (1 + t • Matrix.single a b 1)) := by
    funext t
    congr 1
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h,
      Matrix.mul_one]
  rw [hfun]
  have hev : (fun t : ℂ => Phi lam (k' * z * k * (1 + t • Matrix.single a b 1))) =ᶠ[𝓝 0]
      fun t => (if a = b then (1 + t) ^ (-(muInt lam a)) else 1) * Phi lam (k' * z * k) := by
    have hc : ∀ᶠ t in 𝓝 (0 : ℂ), 1 + t ≠ 0 := by
      have hcont : ContinuousAt (fun t : ℂ => 1 + t) 0 := by fun_prop
      exact hcont.eventually_ne (by norm_num)
    filter_upwards [hc] with t ht using Phi_mul_single lam hz' hab ht
  rw [hev.deriv_eq]
  by_cases hab' : a = b
  · subst hab'
    simp only [if_true]
    have hd : HasDerivAt (fun t : ℂ => (1 + t) ^ (-(muInt lam a)))
        (((-(muInt lam a) : ℤ) : ℂ) * (1 + 0) ^ (-(muInt lam a) - 1) * 1) 0 :=
      (hasDerivAt_zpow (-(muInt lam a)) (1 + 0 : ℂ) (Or.inl (by norm_num))).comp (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).const_add 1)
    rw [(hd.mul_const (Phi lam (k' * z * k))).deriv]
    simp
  · simp [hab']

/- English proof (translation)
Introduce `n lam hlam k z hk hz m`. Establish `hdet : IsUnit k.det` using `(Matrix.isUnit_iff_isUnit_det k).1 hk`. Establish `h1 : k⁻¹ * k = 1` using `Matrix.nonsing_inv_mul k hdet`. Establish `h2 : k * k⁻¹ = 1` using `Matrix.mul_nonsing_inv k hdet`. Establish `hzU : z ∈ {y | k⁻¹ * y * k ∈ Omega n}` using `hz`.

Establish `hmk : ∀ y ∈ {y | k⁻¹ * y * k ∈ Omega n}, (mk (isOpen_conj k k⁻¹) _ (analytic_Phi lam k k⁻¹)).1 y = Phi lam (k⁻¹ * y * k)` using `fun y hy => mk_apply _ _ _ hy`. Establish `step1 : gelfH m (fun y => Phi lam (k⁻¹ * y * k)) z = ((∑ c, (Matrix.of (fun a b => der (isOpen_conj k k⁻¹) (Matrix.single a b (1 : ℂ))) ^ (m + 1)) c c) (mk (isOpen_conj k k⁻¹) _ (analytic_Phi lam k k⁻¹))).1 z`. Rewrite using `[← sum_cycWord, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]`. Simplify using `only [gelfH]`. Conclude with `Finset.sum_congr rfl fun a _ => (rholW_apply _ _ _ hmk z hzU).symm`.

Establish `step2 : (∑ c, (Matrix.of (fun a b => der (isOpen_conj k k⁻¹) (Matrix.single a b (1 : ℂ))) ^ (m + 1)) c c) = ∑ c, (Matrix.of (fun a b => der (isOpen_conj k k⁻¹) (k * Matrix.single a b (1 : ℂ) * k⁻¹)) ^ (m + 1)) c c`. Rewrite using `[of_conj]`. Conclude with `(trace_pow_conj _ _ _ (by rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]) m).symm`. Establish `hglr` using `glRel_conj (isOpen_conj k k⁻¹) k k⁻¹ h1`. Establish `hv : IsHW (fun a b => der (isOpen_conj k k⁻¹) (k * Matrix.single a b (1 : ℂ) * k⁻¹)) (fun a => -(muInt lam a : ℂ)) (mk (isOpen_conj k k⁻¹) _ (analytic_Phi lam k k⁻¹))`.

Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Establish `h3` using `der_Phi lam k k⁻¹ h1 (le_refl a)`. Rewrite `h3` using `[if_pos rfl]`. Conclude with `h3`. Establish `h3` using `der_Phi lam k k⁻¹ h1 hab.le`.

Rewrite `h3` using `[if_neg hab.ne, zero_smul]`. Conclude with `h3`. Establish `hl : lsh (fun a => -(muInt lam a : ℂ)) = fun c => -(lam c : ℂ) + ((n : ℂ) - 1) / 2`. Use function extensionality and compare the values at `c`. Take `⟨mc, hm⟩` from `hlam.2 c`.

Establish `hfl : muInt lam c = mc + ((n : ℤ) - 1 - ((c : ℕ) : ℤ))`. Unfold `muInt Formalism.QuantumDeterminants.rhoStd`. Rewrite using `[Int.floor_eq_iff]`. Use `push_cast`. Apply the tactic sequence `constructor <;> linarith`.

Establish `hmC : (lam c : ℂ) = mc + ((n : ℂ) - 1) / 2`. Establish `h4` using `congrArg (fun x : ℝ => (x : ℂ)) (show lam c = mc + ((n : ℝ) - 1) / 2 by linarith)`. Move the coercions through the operations in `at h4`. Conclude with `h4`. Simplify using `only [lsh, hfl, hmC]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[step1, step2, trace_pow_hw _ _ _ hglr hv, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hmk z hzU, hl]`. Both sides reduce to the same expression.
-/
theorem phiEigen : PhiEigen := by
  intro n lam hlam k z hk hz m
  have hdet : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det k).1 hk
  have h1 : k⁻¹ * k = 1 := Matrix.nonsing_inv_mul k hdet
  have h2 : k * k⁻¹ = 1 := Matrix.mul_nonsing_inv k hdet
  have hzU : z ∈ {y | k⁻¹ * y * k ∈ Omega n} := hz
  have hmk : ∀ y ∈ {y | k⁻¹ * y * k ∈ Omega n},
      (mk (isOpen_conj k k⁻¹) _ (analytic_Phi lam k k⁻¹)).1 y = Phi lam (k⁻¹ * y * k) :=
    fun y hy => mk_apply _ _ _ hy
  have step1 : gelfH m (fun y => Phi lam (k⁻¹ * y * k)) z =
      ((∑ c, (Matrix.of (fun a b => der (isOpen_conj k k⁻¹) (Matrix.single a b (1 : ℂ))) ^ (m + 1)) c c)
        (mk (isOpen_conj k k⁻¹) _ (analytic_Phi lam k k⁻¹))).1 z := by
    rw [← sum_cycWord, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    simp only [gelfH]
    exact Finset.sum_congr rfl fun a _ => (rholW_apply _ _ _ hmk z hzU).symm
  have step2 : (∑ c, (Matrix.of (fun a b => der (isOpen_conj k k⁻¹) (Matrix.single a b (1 : ℂ))) ^ (m + 1)) c c) =
      ∑ c, (Matrix.of (fun a b => der (isOpen_conj k k⁻¹) (k * Matrix.single a b (1 : ℂ) * k⁻¹)) ^ (m + 1)) c c := by
    rw [of_conj]
    exact (trace_pow_conj _ _ _ (by rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]) m).symm
  have hglr := glRel_conj (isOpen_conj k k⁻¹) k k⁻¹ h1
  have hv : IsHW (fun a b => der (isOpen_conj k k⁻¹) (k * Matrix.single a b (1 : ℂ) * k⁻¹))
      (fun a => -(muInt lam a : ℂ)) (mk (isOpen_conj k k⁻¹) _ (analytic_Phi lam k k⁻¹)) := by
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · have h3 := der_Phi lam k k⁻¹ h1 (le_refl a)
      rw [if_pos rfl] at h3
      exact h3
    · have h3 := der_Phi lam k k⁻¹ h1 hab.le
      rw [if_neg hab.ne, zero_smul] at h3
      exact h3
  have hl : lsh (fun a => -(muInt lam a : ℂ)) = fun c => -(lam c : ℂ) + ((n : ℂ) - 1) / 2 := by
    funext c
    obtain ⟨mc, hm⟩ := hlam.2 c
    have hfl : muInt lam c = mc + ((n : ℤ) - 1 - ((c : ℕ) : ℤ)) := by
      unfold muInt Formalism.QuantumDeterminants.rhoStd
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    have hmC : (lam c : ℂ) = mc + ((n : ℂ) - 1) / 2 := by
      have h4 := congrArg (fun x : ℝ => (x : ℂ)) (show lam c = mc + ((n : ℝ) - 1) / 2 by linarith)
      push_cast at h4
      exact h4
    simp only [lsh, hfl, hmC]
    push_cast
    ring
  rw [step1, step2, trace_pow_hw _ _ _ hglr hv, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hmk z hzU, hl]
  rfl

end GlobalTheory.PhiEigenfun
