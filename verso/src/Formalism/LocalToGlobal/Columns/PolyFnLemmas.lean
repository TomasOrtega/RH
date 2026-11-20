import Formalism.LocalToGlobal.Columns.PolyFn
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Forms Matrix MvPolynomial Formalism.L2.DIV
open Formalism.REAL (fockF)
open Formalism.GradedWeylDivisibility (blockAct)
open scoped ComplexOrder Pointwise

section Fock

variable {K : Type} [Field K] [StarRing K] {σ : Type}

/- English proof (translation)
Unfold `Formalism.REAL.fockF`. Use `Finset.sum_subset ht ?_` and prove the remaining obligations. Introduce `m _ hm`. Establish `hc : f.coeff m = 0` using `by simpa [MvPolynomial.mem_support_iff] using hm`. Simplify using `[hc]`.
-/
theorem fockF_eq_sum (f g : MvPolynomial σ ℂ) (t : Finset (σ →₀ ℕ)) (ht : f.support ⊆ t) :
    fockF f g = ∑ m ∈ t, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  refine Finset.sum_subset ht ?_
  intro m _ hm
  have hc : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [hc]

/- English proof (translation)
Unfold `fockS`. Establish `hsf : f.support ⊆ f.support ∪ g.support` using `fun x hx => Finset.mem_union_left _ hx`. Establish `hsg : (MvPolynomial.map s g).support ⊆ f.support ∪ g.support` using `fun x hx => Finset.mem_union_right _ (MvPolynomial.support_map_subset _ _ hx)`. Rewrite using `[fockF_eq_sum _ _ _ hsg, map_sum, Finset.sum_subset hsf ?_]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Simplify using `only [MvPolynomial.coeff_map, map_mul, hf m, map_natCast, mfact, Finsupp.prod]`. Expand and normalize the polynomial expressions, which then agree. Introduce `m _ hm`. Establish `hc : f.coeff m = 0` using `by simpa [MvPolynomial.mem_support_iff] using hm`. Simplify using `[hc]`.
-/
theorem map_fockS (s : K →+* ℂ) (f g : MvPolynomial σ K) (hf : ∀ m, s (star (f.coeff m)) = star (s (f.coeff m))) :
    s (fockS f g) = fockF (MvPolynomial.map s g) (MvPolynomial.map s f) := by
  classical
  unfold fockS
  have hsf : f.support ⊆ f.support ∪ g.support := fun x hx => Finset.mem_union_left _ hx
  have hsg : (MvPolynomial.map s g).support ⊆ f.support ∪ g.support :=
    fun x hx => Finset.mem_union_right _ (MvPolynomial.support_map_subset _ _ hx)
  rw [fockF_eq_sum _ _ _ hsg, map_sum, Finset.sum_subset hsf ?_]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp only [MvPolynomial.coeff_map, map_mul, hf m, map_natCast, mfact, Finsupp.prod]
    ring
  · intro m _ hm
    have hc : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
    simp [hc]

end Fock

section Block

variable {ι : Type} [Fintype ι] {n : ℕ}

open Classical in

def bigM (g : ι → Matrix (Fin n) (Fin n) ℂ) : Matrix (ι × Fin n × Fin n) (ι × Fin n × Fin n) ℂ :=
  fun x y => if x.1 = y.1 ∧ x.2.2 = y.2.2 then g x.1 x.2.1 y.2.1 else 0

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, b, c⟩`. Simplify using `only [Formalism.GradedWeylDivisibility.blockAct, Formalism.GradedWeylDivisibility.sub, MvPolynomial.aeval_X]`. Use `symm`. Rewrite using `[Fintype.sum_prod_type, Fintype.sum_eq_single a, Fintype.sum_prod_type]`.

Use `Finset.sum_congr rfl fun b' _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_eq_single c]`. Simplify using `[bigM]`. Introduce `c' hc'`. Simplify using `[bigM, Ne.symm hc']`.

Introduce `a' ha'`. Use `Finset.sum_eq_zero fun p _ => ?_` and prove the remaining obligations. Simplify using `[bigM, Ne.symm ha']`.
-/
theorem blockAct_eq_sub (g : ι → Matrix (Fin n) (Fin n) ℂ) : blockAct ℂ (n := n) g = Formalism.GradedWeylDivisibility.sub (bigM g) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨a, b, c⟩
  simp only [Formalism.GradedWeylDivisibility.blockAct, Formalism.GradedWeylDivisibility.sub, MvPolynomial.aeval_X]
  symm
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single a, Fintype.sum_prod_type]
  · refine Finset.sum_congr rfl fun b' _ => ?_
    rw [Fintype.sum_eq_single c]
    · simp [bigM]
    · intro c' hc'
      simp [bigM, Ne.symm hc']
  · intro a' ha'
    refine Finset.sum_eq_zero fun p _ => ?_
    simp [bigM, Ne.symm ha']

/- English proof (translation)
Use extensionality with `x y`. Rewrite using `[Matrix.conjTranspose_apply]`. Simplify using `only [bigM]`. Distinguish the cases in `h : x.1 = y.1 ∧ x.2.2 = y.2.2`. Establish `h' : y.1 = x.1 ∧ y.2.2 = x.2.2` using `⟨h.1.symm, h.2.symm⟩`.

Rewrite using `[if_pos h', if_pos h, Matrix.conjTranspose_apply, h.1]`. Establish `h' : ¬ (y.1 = x.1 ∧ y.2.2 = x.2.2)` using `fun h' => h ⟨h'.1.symm, h'.2.symm⟩`. Rewrite using `[if_neg h', if_neg h, star_zero]`.
-/
theorem bigM_conjTranspose (g : ι → Matrix (Fin n) (Fin n) ℂ) : (bigM g)ᴴ = bigM fun τ => (g τ)ᴴ := by
  ext x y
  rw [Matrix.conjTranspose_apply]
  simp only [bigM]
  by_cases h : x.1 = y.1 ∧ x.2.2 = y.2.2
  · have h' : y.1 = x.1 ∧ y.2.2 = x.2.2 := ⟨h.1.symm, h.2.symm⟩
    rw [if_pos h', if_pos h, Matrix.conjTranspose_apply, h.1]
  · have h' : ¬ (y.1 = x.1 ∧ y.2.2 = x.2.2) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
    rw [if_neg h', if_neg h, star_zero]

/- English proof (translation)
Rewrite using `[blockAct_eq_sub, blockAct_eq_sub, ← bigM_conjTranspose]`. Conclude with `Formalism.GradedWeylDivisibility.fockSubAdj _ _ _ _`.
-/
theorem fockF_blockAct (g : ι → Matrix (Fin n) (Fin n) ℂ) (f h : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    fockF (blockAct ℂ g f) h = fockF f (blockAct ℂ (fun τ => (g τ)ᴴ) h) := by
  classical
  rw [blockAct_eq_sub, blockAct_eq_sub, ← bigM_conjTranspose]
  exact Formalism.GradedWeylDivisibility.fockSubAdj _ _ _ _

/- English proof (translation)
Establish `key : (MvPolynomial.map s).comp (blockAct K (n` using `n) g).toRingHom = (blockAct ℂ (n := n) (fun τ => (g τ).map s)).toRingHom.comp (MvPolynomial.map s) := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[MvPolynomial.algHom_C]`. Introduce `i`.

Simplify using `[Formalism.GradedWeylDivisibility.blockAct, Matrix.map_apply]`. Conclude with `DFunLike.congr_fun key P`.
-/
theorem map_blockAct {K : Type} [Field K] (s : K →+* ℂ) (g : ι → Matrix (Fin n) (Fin n) K)
    (P : MvPolynomial (ι × Fin n × Fin n) K) :
    MvPolynomial.map s (blockAct K g P) = blockAct ℂ (fun τ => (g τ).map s) (MvPolynomial.map s P) := by
  have key : (MvPolynomial.map s).comp (blockAct K (n := n) g).toRingHom =
      (blockAct ℂ (n := n) (fun τ => (g τ).map s)).toRingHom.comp (MvPolynomial.map s) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [MvPolynomial.algHom_C]
    · intro i
      simp [Formalism.GradedWeylDivisibility.blockAct, Matrix.map_apply]
  exact DFunLike.congr_fun key P

/- English proof (translation)
Establish `key : (eval fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2).comp (blockAct ℂ (n` using `n) g).toRingHom = eval fun x : ι × Fin n × Fin n => (g x.1 * y x.1) x.2.1 x.2.2 := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[MvPolynomial.algHom_C]`. Introduce and unpack `⟨a, b, c⟩`.

Simplify using `[Formalism.GradedWeylDivisibility.blockAct, Matrix.mul_apply]`. Conclude with `DFunLike.congr_fun key P`.
-/
theorem eval_blockAct (g y : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) (blockAct ℂ g P) =
      eval (fun x : ι × Fin n × Fin n => (g x.1 * y x.1) x.2.1 x.2.2) P := by
  have key : (eval fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2).comp (blockAct ℂ (n := n) g).toRingHom =
      eval fun x : ι × Fin n × Fin n => (g x.1 * y x.1) x.2.1 x.2.2 := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [MvPolynomial.algHom_C]
    · rintro ⟨a, b, c⟩
      simp [Formalism.GradedWeylDivisibility.blockAct, Matrix.mul_apply]
  exact DFunLike.congr_fun key P

end Block

section Pair

variable {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Unfold `extremal Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, RingHom.map_det]`. Use `congr 2`.

Use extensionality with `p q`. Simplify using `[Matrix.map_apply]`.
-/
theorem map_extremal (s : K →+* ℂ) (lam : DomWeight n) :
    MvPolynomial.map s (extremal K n lam) = extremal ℂ n lam := by
  unfold extremal Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext p q
  simp [Matrix.map_apply]

/- English proof (translation)
Establish `key : ∀ {r k : ℕ} (h : k ≤ r) (ν : Fin k → ℕ), (Formalism.GradedWeylDivisibility.hw K h ν : MvPolynomial (Fin r × Fin k) K) = MvPolynomial.map (Int.castRingHom K) (Formalism.GradedWeylDivisibility.hw ℤ h ν)`. Introduce `r k h ν`. Unfold `Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_pow, RingHom.map_det]`. Use `congr 2`. Use extensionality with `p q`. Simplify using `[Matrix.map_apply]`. Unfold `extremal`.

Rewrite using `[key, MvPolynomial.coeff_map, eq_intCast, star_intCast, map_intCast, star_intCast]`.
-/
theorem star_coeff_extremal (s : K →+* ℂ) (lam : DomWeight n) (m : Fin n × Fin n →₀ ℕ) :
    s (star ((extremal K n lam).coeff m)) = star (s ((extremal K n lam).coeff m)) := by
  have key : ∀ {r k : ℕ} (h : k ≤ r) (ν : Fin k → ℕ), (Formalism.GradedWeylDivisibility.hw K h ν : MvPolynomial (Fin r × Fin k) K) =
      MvPolynomial.map (Int.castRingHom K) (Formalism.GradedWeylDivisibility.hw ℤ h ν) := by
    intro r k h ν
    unfold Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, RingHom.map_det]
    congr 2
    ext p q
    simp [Matrix.map_apply]
  unfold extremal
  rw [key, MvPolynomial.coeff_map, eq_intCast, star_intCast, map_intCast, star_intCast]

/- English proof (translation)
Unfold `extNorm`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_fockS s _ _ (star_coeff_extremal s (lam τ)), map_extremal]`.
-/
theorem map_extNorm (s : K →+* ℂ) (lam : ι → DomWeight n) :
    s (extNorm K lam) = ∏ τ, fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ)) := by
  unfold extNorm
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_fockS s _ _ (star_coeff_extremal s (lam τ)), map_extremal]

/- English proof (translation)
Establish `e1 : pairP lam Gd F F' = gramTw lam Gd / extNorm K lam * fockS F (blockAct K (fun τ => (Gd τ)ᵀ) F')` using `rfl`. Establish `e2 : (fun τ => ((Gd τ)ᵀ).map s) = fun τ => B τ * (B τ)ᴴ`. Use function extensionality and compare the values at `τ`. Rewrite using `[← hB τ, transpose_map]`. Establish `e3 : blockAct ℂ (n` using `n) (fun τ => B τ * (B τ)ᴴ) = (blockAct ℂ fun τ => (B τ)ᴴ).comp (blockAct ℂ B) := (blockAct_comp _ _).symm`.

Establish `e4 : s (gramTw lam Gd) = ∏ τ, ((Gd τ).map s).det ^ (lam τ).detShift`. Rewrite using `[gramTw, map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]`. Rewrite using `[e1, map_mul, map_div₀, map_fockS s _ _ hF, map_blockAct, e2, e3, AlgHom.comp_apply, fockF_blockAct, map_extNorm, e4, nfAll]`.

Simplify using `only [conjTranspose_conjTranspose]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_pairP (s : K →+* ℂ) (lam : ι → DomWeight n) (Gd : ι → Matrix (Fin n) (Fin n) K)
    (B : ι → Matrix (Fin n) (Fin n) ℂ) (hB : ∀ τ, ((Gd τ).map s)ᵀ = B τ * (B τ)ᴴ)
    (F F' : MvPolynomial (ι × Fin n × Fin n) K) (hF : ∀ m, s (star (F.coeff m)) = star (s (F.coeff m))) :
    s (pairP lam Gd F F') = (∏ τ, ((Gd τ).map s).det ^ (lam τ).detShift) *
      nfAll lam (blockAct ℂ B (MvPolynomial.map s F')) (blockAct ℂ B (MvPolynomial.map s F)) := by
  have e1 : pairP lam Gd F F' = gramTw lam Gd / extNorm K lam * fockS F (blockAct K (fun τ => (Gd τ)ᵀ) F') := rfl
  have e2 : (fun τ => ((Gd τ)ᵀ).map s) = fun τ => B τ * (B τ)ᴴ := by
    funext τ; rw [← hB τ, transpose_map]
  have e3 : blockAct ℂ (n := n) (fun τ => B τ * (B τ)ᴴ) = (blockAct ℂ fun τ => (B τ)ᴴ).comp (blockAct ℂ B) :=
    (blockAct_comp _ _).symm
  have e4 : s (gramTw lam Gd) = ∏ τ, ((Gd τ).map s).det ^ (lam τ).detShift := by
    rw [gramTw, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]
  rw [e1, map_mul, map_div₀, map_fockS s _ _ hF, map_blockAct, e2, e3, AlgHom.comp_apply, fockF_blockAct, map_extNorm, e4, nfAll]
  simp only [conjTranspose_conjTranspose]
  ring

end Pair

section Act

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Unfold `actP evFr detTwK trAct mapS`. Use function extensionality and compare the values at `y`. Simplify using `only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_blockAct]`. Simplify using `only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.eval_mul, MvPolynomial.eval_C, Pi.one_apply, Matrix.one_mul]`.

Rewrite using `[eval_blockAct]`. Simplify using `only [Matrix.transpose_map, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, map_prod]`. Unfold `detPow`. Simplify using `only [shiftOf, Units.val_zpow_eq_zpow_val, map_zpow₀, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, Matrix.det_transpose, RingHom.mapMatrix_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evFr_actP (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : K →+* ℂ) (lam : ι → DomWeight n) (g : ι → GL (Fin n) K)
    (F : MvPolynomial (ι × Fin n × Fin n) K) :
    evFr G (shiftOf lam) s (actP lam g F) =
      fnOf G (shiftOf lam) (fun τ => (((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map s)ᵀ) (MvPolynomial.map s F) := by
  unfold actP evFr detTwK trAct mapS
  funext y
  simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_blockAct]
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.eval_mul, MvPolynomial.eval_C, Pi.one_apply,
    Matrix.one_mul]
  rw [eval_blockAct]
  simp only [Matrix.transpose_map, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, map_prod]
  unfold detPow
  simp only [shiftOf, Units.val_zpow_eq_zpow_val, map_zpow₀, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det,
    Matrix.det_transpose, RingHom.mapMatrix_apply]
  ring

/- English proof (translation)
Establish `comp : ∀ (A B : ι → Matrix (Fin n) (Fin n) K) (q : MvPolynomial (ι × Fin n × Fin n) K), blockAct K (n` using `n) A (blockAct K (n := n) B q) = blockAct K (n := n) (fun τ => B τ * A τ) q := by`. Introduce `A B q`. Establish `key : (blockAct K (n` using `n) A).comp (blockAct K (n := n) B) = blockAct K (n := n) (fun τ => B τ * A τ) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, b, c⟩`.

Simplify using `only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]`. Simplify using `only [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_mul, ← map_sum, Matrix.mul_apply]`. Conclude with `DFunLike.congr_fun key q`.

Establish `hid : ∀ q : MvPolynomial (ι × Fin n × Fin n) K, blockAct K (n` using `n) (fun _ => (1 : Matrix (Fin n) (Fin n) K)) q = q := by`. Introduce `q`. Establish `key : blockAct K (n` using `n) (fun (_ : ι) => (1 : Matrix (Fin n) (Fin n) K)) = AlgHom.id K _ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, b, c⟩`.

Simplify using `[Formalism.GradedWeylDivisibility.blockAct, Matrix.one_apply]`. Rewrite using `[key]`. Both sides reduce to the same expression. Establish `hinv : actP lam g (actP lam g⁻¹ F) = F`. Unfold `actP detTwK trAct`.

Simplify using `only [LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, comp, smul_smul]`. Establish `hm : (fun τ => ((↑(g⁻¹ τ) : Matrix (Fin n) (Fin n) K))ᵀ * (↑(g τ) : Matrix (Fin n) (Fin n) K)ᵀ) = fun _ => 1`. Use function extensionality and compare the values at `τ`. Rewrite using `[← Matrix.transpose_mul, Pi.inv_apply, Units.mul_inv, Matrix.transpose_one]`. Establish `hc : (∏ τ, detPow K n (g⁻¹ τ) (lam τ).detShift) * (∏ τ, detPow K n (g τ) (lam τ).detShift) = 1`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun τ _ => ?_` and prove the remaining obligations. Unfold `detPow`. Rewrite using `[← Units.val_mul, ← mul_zpow, ← map_mul, Pi.inv_apply, _root_.inv_mul_cancel, map_one, _root_.one_zpow, Units.val_one]`. Rewrite using `[hm, hid, hc, one_smul]`.

Use `conv_lhs => rw [← hinv]`. Conclude with `evFr_actP G s lam g (actP lam g⁻¹ F)`.
-/
theorem evFr_coord (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : K →+* ℂ) (lam : ι → DomWeight n) (g : ι → GL (Fin n) K)
    (F : MvPolynomial (ι × Fin n × Fin n) K) :
    evFr G (shiftOf lam) s F =
      fnOf G (shiftOf lam) (fun τ => (((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map s)ᵀ)
        (MvPolynomial.map s (actP lam g⁻¹ F)) := by
  have comp : ∀ (A B : ι → Matrix (Fin n) (Fin n) K) (q : MvPolynomial (ι × Fin n × Fin n) K),
      blockAct K (n := n) A (blockAct K (n := n) B q) = blockAct K (n := n) (fun τ => B τ * A τ) q := by
    intro A B q
    have key : (blockAct K (n := n) A).comp (blockAct K (n := n) B) = blockAct K (n := n) (fun τ => B τ * A τ) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨a, b, c⟩
      simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_X, map_sum, map_mul,
        MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
      simp only [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← map_sum, Matrix.mul_apply]
    exact DFunLike.congr_fun key q
  have hid : ∀ q : MvPolynomial (ι × Fin n × Fin n) K,
      blockAct K (n := n) (fun _ => (1 : Matrix (Fin n) (Fin n) K)) q = q := by
    intro q
    have key : blockAct K (n := n) (fun (_ : ι) => (1 : Matrix (Fin n) (Fin n) K)) = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      rintro ⟨a, b, c⟩
      simp [Formalism.GradedWeylDivisibility.blockAct, Matrix.one_apply]
    rw [key]
    rfl
  have hinv : actP lam g (actP lam g⁻¹ F) = F := by
    unfold actP detTwK trAct
    simp only [LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, comp, smul_smul]
    have hm : (fun τ => ((↑(g⁻¹ τ) : Matrix (Fin n) (Fin n) K))ᵀ * (↑(g τ) : Matrix (Fin n) (Fin n) K)ᵀ) =
        fun _ => 1 := by
      funext τ
      rw [← Matrix.transpose_mul, Pi.inv_apply, Units.mul_inv, Matrix.transpose_one]
    have hc : (∏ τ, detPow K n (g⁻¹ τ) (lam τ).detShift) * (∏ τ, detPow K n (g τ) (lam τ).detShift) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun τ _ => ?_
      unfold detPow
      rw [← Units.val_mul, ← mul_zpow, ← map_mul, Pi.inv_apply, _root_.inv_mul_cancel, map_one, _root_.one_zpow,
        Units.val_one]
    rw [hm, hid, hc, one_smul]
  conv_lhs => rw [← hinv]
  exact evFr_actP G s lam g (actP lam g⁻¹ F)

/- English proof (translation)
Establish `hdet : (A.map s).det = s A.det` using `(RingHom.map_det s A).symm`. Establish `hadj : (A.map s).adjugate = A.adjugate.map s` using `(RingHom.map_adjugate s A).symm`. Rewrite using `[Matrix.inv_def, Matrix.inv_def, hdet, hadj]`. Use extensionality with `i j`. Simplify using `[Ring.inverse_eq_inv', map_inv₀]`.
-/
theorem map_inv_matrix {K L : Type} [Field K] [Field L] (s : K →+* L) (A : Matrix (Fin n) (Fin n) K) :
    (A⁻¹).map s = (A.map s)⁻¹ := by
  have hdet : (A.map s).det = s A.det := (RingHom.map_det s A).symm
  have hadj : (A.map s).adjugate = A.adjugate.map s := (RingHom.map_adjugate s A).symm
  rw [Matrix.inv_def, Matrix.inv_def, hdet, hadj]
  ext i j
  simp [Ring.inverse_eq_inv', map_inv₀]

/- English proof (translation)
Simplify using `only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, h, Matrix.mul_assoc]`.
-/
theorem fnOf_tr {G G' : ι → Matrix (Fin n) (Fin n) ℂ} (sh : ι → ℤ) (M N : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Frames G) (y' : Frames G') (h : ∀ τ, y.1 τ = N τ * y'.1 τ) :
    fnOf G sh M P y = fnOf G' sh (fun τ => M τ * N τ) P y' := by
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, h, Matrix.mul_assoc]

end Act

section ESide

variable {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Establish `h` using `evFr_actP (gramC J (embAt s emb)) s lam (invTrK (embGL emb γ)) F.1`. Establish `e : (fun τ => (((invTrK (embGL emb γ) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map s)ᵀ) = atInf (embAt s emb) ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)`. Use function extensionality and compare the values at `τ`. Use extensionality with `a b`. Simplify using `only [invTrK, inside₂, embGL, atInf, embAt, Formalism.UG.bc, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.pi_apply, transpose_apply, map_apply, RingHom.comp_apply, ← map_inv]`.

Both sides reduce to the same expression. Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem evV_rhoVr (emb : ι → E →+* K) (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (γ : GL (Fin n) E) (F : VV K lam) :
    evV emb J lam s (rhoVr emb lam γ F) =
      fnOf _ (shiftOf lam) (atInf (embAt s emb) ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) (MvPolynomial.map s F.1) := by
  have h := evFr_actP (gramC J (embAt s emb)) s lam (invTrK (embGL emb γ)) F.1
  have e : (fun τ => (((invTrK (embGL emb γ) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map s)ᵀ) =
      atInf (embAt s emb) ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
    funext τ
    ext a b
    simp only [invTrK, inside₂, embGL, atInf, embAt, Formalism.UG.bc, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.pi_apply,
      transpose_apply, map_apply, RingHom.comp_apply, ← map_inv]
    rfl
  rw [e] at h
  exact h

/- English proof (translation)
Rewrite using `[evV_rhoVr]`. Unfold `IsTr at h`. Rewrite using `[fnOf_tr (shiftOf lam) _ _ _ y y' h]`. Establish `hM : ∀ τ, atInf (embAt s emb) ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * atInf (embAt s emb) (γ : Matrix (Fin n) (Fin n) E) τ = 1`. Introduce `τ`.

Unfold `atInf`. Rewrite using `[← Matrix.map_mul, Units.inv_mul]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Simplify using `only [hM]`. Both sides reduce to the same expression.
-/
theorem evV_rhoVr_tr (emb : ι → E →+* K) (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (γ : GL (Fin n) E) (F : VV K lam) (y y' : Frames (gramC J (embAt s emb)))
    (h : IsTr (atInf (embAt s emb) (γ : Matrix (Fin n) (Fin n) E)) y' y) :
    evV emb J lam s (rhoVr emb lam γ F) y = evV emb J lam s F y' := by
  rw [evV_rhoVr]
  unfold IsTr at h
  rw [fnOf_tr (shiftOf lam) _ _ _ y y' h]
  have hM : ∀ τ, atInf (embAt s emb) ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ *
      atInf (embAt s emb) (γ : Matrix (Fin n) (Fin n) E) τ = 1 := by
    intro τ
    unfold atInf
    rw [← Matrix.map_mul, Units.inv_mul]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  simp only [hM]
  rfl

end ESide

section EPair

variable {E K : Type} [Field E] [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Establish `hu : IsUnit o.det` using `Matrix.isUnit_det_of_left_inverse h`. Establish `h1 : o * (oᴴ * G) = 1`. Rewrite using `[← Matrix.inv_eq_left_inv h]`. Conclude with `Matrix.mul_nonsing_inv o hu`. Establish `h2 : o * oᴴ * G = 1` using `by rw [Matrix.mul_assoc]; exact h1`.

Establish `hu2 : IsUnit (o * oᴴ).det` using `Matrix.isUnit_det_of_right_inverse h2`. Rewrite using `[← Matrix.inv_eq_right_inv h2, Matrix.nonsing_inv_nonsing_inv _ hu2]`.
-/
theorem inv_eq_of_frame (G o : Matrix (Fin n) (Fin n) ℂ) (h : oᴴ * G * o = 1) : G⁻¹ = o * oᴴ := by
  have hu : IsUnit o.det := Matrix.isUnit_det_of_left_inverse h
  have h1 : o * (oᴴ * G) = 1 := by
    rw [← Matrix.inv_eq_left_inv h]
    exact Matrix.mul_nonsing_inv o hu
  have h2 : o * oᴴ * G = 1 := by rw [Matrix.mul_assoc]; exact h1
  have hu2 : IsUnit (o * oᴴ).det := Matrix.isUnit_det_of_right_inverse h2
  rw [← Matrix.inv_eq_right_inv h2, Matrix.nonsing_inv_nonsing_inv _ hu2]

/- English proof (translation)
Establish `hu : IsUnit o.det` using `Matrix.isUnit_det_of_left_inverse h`. Establish `h1 : o * (oᴴ * G) = 1`. Rewrite using `[← Matrix.inv_eq_left_inv h]`. Conclude with `Matrix.mul_nonsing_inv o hu`. Establish `h2 : o * oᴴ * G = 1` using `by rw [Matrix.mul_assoc]; exact h1`.

Rewrite using `[← Matrix.mul_inv_rev]`. Conclude with `(Matrix.inv_eq_right_inv h2).symm`.
-/
theorem eq_of_frame (G o : Matrix (Fin n) (Fin n) ℂ) (h : oᴴ * G * o = 1) : G = (oᴴ)⁻¹ * o⁻¹ := by
  have hu : IsUnit o.det := Matrix.isUnit_det_of_left_inverse h
  have h1 : o * (oᴴ * G) = 1 := by
    rw [← Matrix.inv_eq_left_inv h]
    exact Matrix.mul_nonsing_inv o hu
  have h2 : o * oᴴ * G = 1 := by rw [Matrix.mul_assoc]; exact h1
  rw [← Matrix.mul_inv_rev]
  exact (Matrix.inv_eq_right_inv h2).symm

/- English proof (translation)
Rewrite using `[inv_eq_of_frame G o h, Matrix.det_mul, Matrix.det_conjTranspose]`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.
-/
theorem det_inv_of_frame (G o : Matrix (Fin n) (Fin n) ℂ) (h : oᴴ * G * o = 1) :
    (G⁻¹).det = ((‖o.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [inv_eq_of_frame G o h, Matrix.det_mul, Matrix.det_conjTranspose]
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Establish `e0 : ∀ τ, (gramKd emb J τ).map s = ((gramC J (embAt s emb) τ)⁻¹)ᵀ` using `fun τ => by`. Rewrite using `[gramKd, transpose_map, map_inv_matrix, gramC, embAt, Matrix.map_map]`. Both sides reduce to the same expression. Establish `h` using `map_pairP s lam (gramKd emb J) o.1 (fun τ => by`. Rewrite using `[e0, transpose_transpose, inv_eq_of_frame _ _ (ho τ)]) F.1 F'.1 hF`.

Establish `e1 : pairVr emb lam J F F' = pairP lam (gramKd emb J) F.1 F'.1` using `rfl`. Rewrite using `[e1, h]`. Use `congr 1`. Rewrite using `[Complex.ofReal_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[e0, det_transpose, det_inv_of_frame _ _ (ho τ), shiftOf, _root_.zpow_mul, Complex.ofReal_zpow]`. Use `congr 1`.
-/
theorem pairVr_nfAll (emb : ι → E →+* K) (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (o : Frames (gramC J (embAt s emb))) (ho : ∀ τ, (o.1 τ)ᴴ * gramC J (embAt s emb) τ * o.1 τ = 1)
    (F F' : VV K lam) (hF : ∀ m, s (star (F.1.coeff m)) = star (s (F.1.coeff m))) :
    s (pairVr emb lam J F F') = ((∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf lam τ) : ℝ) : ℂ) *
      nfAll lam (blockAct ℂ o.1 (MvPolynomial.map s F'.1)) (blockAct ℂ o.1 (MvPolynomial.map s F.1)) := by
  have e0 : ∀ τ, (gramKd emb J τ).map s = ((gramC J (embAt s emb) τ)⁻¹)ᵀ := fun τ => by
    rw [gramKd, transpose_map, map_inv_matrix, gramC, embAt, Matrix.map_map]
    rfl
  have h := map_pairP s lam (gramKd emb J) o.1 (fun τ => by
    rw [e0, transpose_transpose, inv_eq_of_frame _ _ (ho τ)]) F.1 F'.1 hF
  have e1 : pairVr emb lam J F F' = pairP lam (gramKd emb J) F.1 F'.1 := rfl
  rw [e1, h]
  congr 1
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [e0, det_transpose, det_inv_of_frame _ _ (ho τ), shiftOf, _root_.zpow_mul, Complex.ofReal_zpow]
  congr 1

/- English proof (translation)
Establish `e0 : ∀ τ, (gramK emb J τ).map s = gramC J (embAt s emb) τ` using `fun τ => by`. Rewrite using `[gramK, gramC, embAt, Matrix.map_map]`. Both sides reduce to the same expression. Establish `h` using `map_pairP s lam (gramK emb J) (fun τ => ((o.1 τ)⁻¹)ᵀ) (fun τ => by`. Rewrite using `[e0, eq_of_frame _ _ (ho τ), transpose_mul, ← conjTranspose_nonsing_inv]`.

Use `congr 1) F.1 F'.1 hF`. Establish `e1 : pairV emb lam J F F' = pairP lam (gramK emb J) F.1 F'.1` using `rfl`. Rewrite using `[e1, h]`. Use `congr 1`. Rewrite using `[Complex.ofReal_prod]`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `e2 : (gramC J (embAt s emb) τ).det = (((‖(o.1 τ).det‖ ^ 2 : ℝ) : ℂ))⁻¹`. Rewrite using `[← det_inv_of_frame _ _ (ho τ), det_nonsing_inv, Ring.inverse_eq_inv', inv_inv]`. Rewrite using `[e0, e2, shiftOf, _root_.zpow_neg, _root_.zpow_mul, Complex.ofReal_inv, Complex.ofReal_zpow, _root_.inv_zpow]`. Use `congr 2`.
-/
theorem pairV_nfAll (emb : ι → E →+* K) (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (o : Frames (gramC J (embAt s emb))) (ho : ∀ τ, (o.1 τ)ᴴ * gramC J (embAt s emb) τ * o.1 τ = 1)
    (F F' : VV K lam) (hF : ∀ m, s (star (F.1.coeff m)) = star (s (F.1.coeff m))) :
    s (pairV emb lam J F F') = ((∏ τ, ‖(o.1 τ).det‖ ^ (-(2 * shiftOf lam τ)) : ℝ) : ℂ) *
      nfAll lam (blockAct ℂ (fun τ => ((o.1 τ)⁻¹)ᵀ) (MvPolynomial.map s F'.1))
        (blockAct ℂ (fun τ => ((o.1 τ)⁻¹)ᵀ) (MvPolynomial.map s F.1)) := by
  have e0 : ∀ τ, (gramK emb J τ).map s = gramC J (embAt s emb) τ := fun τ => by
    rw [gramK, gramC, embAt, Matrix.map_map]
    rfl
  have h := map_pairP s lam (gramK emb J) (fun τ => ((o.1 τ)⁻¹)ᵀ) (fun τ => by
    rw [e0, eq_of_frame _ _ (ho τ), transpose_mul, ← conjTranspose_nonsing_inv]
    congr 1) F.1 F'.1 hF
  have e1 : pairV emb lam J F F' = pairP lam (gramK emb J) F.1 F'.1 := rfl
  rw [e1, h]
  congr 1
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have e2 : (gramC J (embAt s emb) τ).det = (((‖(o.1 τ).det‖ ^ 2 : ℝ) : ℂ))⁻¹ := by
    rw [← det_inv_of_frame _ _ (ho τ), det_nonsing_inv, Ring.inverse_eq_inv', inv_inv]
  rw [e0, e2, shiftOf, _root_.zpow_neg, _root_.zpow_mul, Complex.ofReal_inv, Complex.ofReal_zpow, _root_.inv_zpow]
  congr 2

end EPair

section Pos

variable {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Break down `hy τ with h | h` into its components or cases. Conclude with `h`. Establish `hp : ((y.1 τ)ᴴ * G τ * y.1 τ).PosSemidef` using `hG.conjTranspose_mul_mul_same (y.1 τ)`. Rewrite `hp` using `[h]`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases.

Substitute `hn` using the available equality. Conclude with `Subsingleton.elim _ _`. It suffices to derive a contradiction. Establish `ht` using `hp.trace_nonneg`. Rewrite `ht` using `[Matrix.trace_neg, Matrix.trace_one, Complex.le_def]`.

Apply the tactic sequence `simp at ht <;> omega`.
-/
theorem frame_pos {G : ι → Matrix (Fin n) (Fin n) ℂ} (y : Frames G) (hy : y.IsON) (τ : ι) (hG : (G τ).PosSemidef) :
    (y.1 τ)ᴴ * G τ * y.1 τ = 1 := by
  rcases hy τ with h | h
  · exact h
  · have hp : ((y.1 τ)ᴴ * G τ * y.1 τ).PosSemidef := hG.conjTranspose_mul_mul_same (y.1 τ)
    rw [h] at hp
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact Subsingleton.elim _ _
    · exfalso
      have ht := hp.trace_nonneg
      rw [Matrix.trace_neg, Matrix.trace_one, Complex.le_def] at ht
      simp at ht <;> omega

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Simplify using `only [gramC]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem gramC_one {E : Type} [Field E] (emb : ι → E →+* ℂ) :
    gramC (1 : Matrix (Fin n) (Fin n) E) emb = fun _ => 1 := by
  funext τ
  simp only [gramC]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Use `frame_pos y hy τ ?_` and prove the remaining obligations. Simplify using `only [gramC_one]`. Conclude with `Matrix.PosSemidef.one`.
-/
theorem frame_std {E : Type} [Field E] (emb : ι → E →+* ℂ) (y : Frames (gramC (1 : Matrix (Fin n) (Fin n) E) emb))
    (hy : y.IsON) (τ : ι) :
    (y.1 τ)ᴴ * gramC (1 : Matrix (Fin n) (Fin n) E) emb τ * y.1 τ = 1 := by
  refine frame_pos y hy τ ?_
  simp only [gramC_one]
  exact Matrix.PosSemidef.one

/- English proof (translation)
Establish `h` using `frame_std emb y hy τ`. Simplify using `only [gramC_one, Matrix.mul_one] at h`. Establish `hd` using `congrArg Matrix.det h`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one]`. Establish `h2 : ‖(y.1 τ).det‖ * ‖(y.1 τ).det‖ = 1`.

Simplify `congrArg norm hd` using `[norm_mul, norm_star]`. Establish `h0 : 0 ≤ ‖(y.1 τ).det‖` using `norm_nonneg _`. Use `show ‖(y.1 τ).det‖ = 1`. Use polynomial arithmetic with `[h2, h0]`.
-/
theorem norm_deFr_std {E : Type} [Field E] (emb : ι → E →+* ℂ) (y : Frames (gramC (1 : Matrix (Fin n) (Fin n) E) emb))
    (hy : y.IsON) (τ : ι) :
    ‖deFr y τ‖ = 1 := by
  have h := frame_std emb y hy τ
  simp only [gramC_one, Matrix.mul_one] at h
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at hd
  have h2 : ‖(y.1 τ).det‖ * ‖(y.1 τ).det‖ = 1 := by
    simpa [norm_mul, norm_star] using congrArg norm hd
  have h0 : 0 ≤ ‖(y.1 τ).det‖ := norm_nonneg _
  show ‖(y.1 τ).det‖ = 1
  nlinarith [h2, h0]

end Pos

section Image

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.weyl at hf ⊢`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨w, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem map_mem_weyl {S : Type} [CommRing S] {r m : ℕ} (hm : m ≤ r) (ν : Fin m → ℕ)
    (f : MvPolynomial (Fin r × Fin m) ℤ) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl ℤ r m hm ν) :
    MvPolynomial.map (Int.castRingHom S) f ∈ Formalism.GradedWeylDivisibility.weyl S r m hm ν := by
  unfold Formalism.GradedWeylDivisibility.weyl at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨w, ?_⟩
    simp only
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Use `le_antisymm ?_ (Formalism.GradedWeylDivisibility.weylLeDual K r m hm ν hν)` and prove the remaining obligations. Take `⟨b, hb, hb2⟩` from `Formalism.GradedWeylDivisibility.sSBasis K r m ν`. Rewrite using `[← hb.2.1, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨-, -, N, sz, hsz, I, hsh, -, hbi⟩` from `hb2 i`.

Establish `h1 : Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ r m ν`. Rewrite using `[← hsh]`. Conclude with `Formalism.GradedWeylDivisibility.bidetMem ℤ r m N sz hsz I`. Take `⟨c, hc, h2⟩` from `Formalism.GradedWeylDivisibility.weylRational r m hm ν hν _ h1`. Establish `h3` using `map_mem_weyl (S := K) hm ν _ h2`.

Rewrite `h3` using `[map_zsmul, Formalism.GradedWeylDivisibility.ldlat_map_bidet, ← hbi, ← Int.cast_smul_eq_zsmul K]`. Establish `hc' : (c : K) ≠ 0` using `Int.cast_ne_zero.mpr hc`. Use `Submodule.smul_mem _ ((c : K)⁻¹) h3` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hc', one_smul]`. Then use the resulting hypothesis.
-/
theorem dualWeyl_eq_weyl (K : Type) [Field K] [CharZero K] {r m : ℕ} (hm : m ≤ r) (ν : Fin m → ℕ) (hν : Antitone ν) :
    Formalism.GradedWeylDivisibility.dualWeyl K r m ν = Formalism.GradedWeylDivisibility.weyl K r m hm ν := by
  refine le_antisymm ?_ (Formalism.GradedWeylDivisibility.weylLeDual K r m hm ν hν)
  obtain ⟨b, hb, hb2⟩ := Formalism.GradedWeylDivisibility.sSBasis K r m ν
  rw [← hb.2.1, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨-, -, N, sz, hsz, I, hsh, -, hbi⟩ := hb2 i
  have h1 : Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ r m ν := by
    rw [← hsh]; exact Formalism.GradedWeylDivisibility.bidetMem ℤ r m N sz hsz I
  obtain ⟨c, hc, h2⟩ := Formalism.GradedWeylDivisibility.weylRational r m hm ν hν _ h1
  have h3 := map_mem_weyl (S := K) hm ν _ h2
  rw [map_zsmul, Formalism.GradedWeylDivisibility.ldlat_map_bidet, ← hbi, ← Int.cast_smul_eq_zsmul K] at h3
  have hc' : (c : K) ≠ 0 := Int.cast_ne_zero.mpr hc
  have := Submodule.smul_mem _ ((c : K)⁻¹) h3
  rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this

/- English proof (translation)
The claim follows from `dualWeyl_eq_weyl K le_rfl _ (natW_anti lam)`.
-/
theorem nablaSq_eq_delSq (K : Type) [Field K] [CharZero K] (lam : DomWeight n) : nablaSq K n lam = delSq K n lam :=
  dualWeyl_eq_weyl K le_rfl _ (natW_anti lam)

omit [CharZero K] in
/- English proof (translation)
Unfold `Formalism.L2.Forms.ten`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `only [Formalism.GradedWeylDivisibility.blockEmb]`. Rewrite using `[MvPolynomial.map_rename]`.
-/
theorem map_ten (s : K →+* ℂ) (f : ι → MvPolynomial (Fin n × Fin n) K) :
    MvPolynomial.map s (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) = Forms.ten fun τ => MvPolynomial.map s (f τ) := by
  unfold Formalism.L2.Forms.ten
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [Formalism.GradedWeylDivisibility.blockEmb]
  rw [MvPolynomial.map_rename]

omit [CharZero K] in

/- English proof (translation)
Unfold `VV Formalism.GradedWeylDivisibility.tensorLat at hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, hf, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨fun τ => MvPolynomial.map s (f τ), fun τ => ?_, map_ten s f⟩` and prove the remaining obligations.

Rewrite using `[← nablaSq_eq_delSq]`. Conclude with `Formalism.GradedWeylDivisibility.dualWeylMap K ℂ s n n _ _ (hf τ)`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem map_mem_CSpan (s : K →+* ℂ) (lam : ι → DomWeight n) (F : MvPolynomial (ι × Fin n × Fin n) K) (hF : F ∈ VV K lam) :
    MvPolynomial.map s F ∈ CSpan lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun τ => MvPolynomial.map s (f τ), fun τ => ?_, map_ten s f⟩
    rw [← nablaSq_eq_delSq]
    exact Formalism.GradedWeylDivisibility.dualWeylMap K ℂ s n n _ _ (hf τ)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

end Image

section Image2

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on t ?_ ?_` and prove the remaining obligations. Introduce `_`. Rewrite using `[Finset.prod_empty, Finset.prod_empty]`. Conclude with `Submodule.one_le.mp le_rfl`.

Introduce `a t ha ih h`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha]`. Conclude with `Submodule.mul_mem_mul (h a (Finset.mem_insert_self a t)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem prod_mem_prod_sub {R A : Type} [CommSemiring R] [CommSemiring A] [Algebra R A] {κ : Type} (t : Finset κ)
    (M : κ → Submodule R A) (x : κ → A) (h : ∀ i ∈ t, x i ∈ M i) : ∏ i ∈ t, x i ∈ ∏ i ∈ t, M i := by
  classical
  revert h
  refine Finset.induction_on t ?_ ?_
  · intro _
    rw [Finset.prod_empty, Finset.prod_empty]
    exact Submodule.one_le.mp le_rfl
  · intro a t ha ih h
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Submodule.mul_mem_mul (h a (Finset.mem_insert_self a t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Unfold `CSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Set `S : ι → Set (MvPolynomial (ι × Fin n × Fin n) ℂ)` to `fun τ => Set.range fun w : List (Fin n × Fin n × ℕ) => rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.applyWord ℂ w (Formalism.GradedWeylDivisibility.hw ℂ le_rfl (lam τ).natW))`. Establish `h1 : ∀ τ, rename (Prod.mk τ) (f τ) ∈ Submodule.span ℂ (S τ)`.

Introduce `τ`. Establish `h` using `Submodule.mem_map_of_mem (f := (rename (R := ℂ) (Prod.mk τ : Fin n × Fin n → ι × Fin n × Fin n)).toLinearMap) (hf τ)`. Unfold `delSq Formalism.GradedWeylDivisibility.weyl at h`. Rewrite `h` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `h`.

Establish `h2 : Forms.ten f ∈ Submodule.span ℂ (∏ τ, S τ)`. Rewrite using `[← Submodule.prod_span]`. Conclude with `prod_mem_prod_sub _ _ _ fun τ _ => h1 τ`. Use `Submodule.span_mono ?_ h2` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx` using `[Set.mem_finsetProd]`. Take `⟨g, hg, rfl⟩` from `hx`. Establish `hg' : ∀ τ, ∃ w : List (Fin n × Fin n × ℕ), rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.applyWord ℂ w (Formalism.GradedWeylDivisibility.hw ℂ le_rfl (lam τ).natW)) = g τ` using `fun τ => hg (Finset.mem_univ τ)`. Use `choose w hw using hg'`. Use `⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K (w τ) (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW)), ?_, ?_⟩` and prove the remaining obligations.

Use `Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩` and prove the remaining obligations. Conclude with `Formalism.GradedWeylDivisibility.weylLeDual K n n le_rfl _ (natW_anti (lam τ)) (Submodule.subset_span ⟨w τ, rfl⟩)`. Simplify using `only`. Rewrite using `[map_ten, Forms.ten]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[← hw τ, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]`.
-/
theorem CSpan_le_span (s : K →+* ℂ) (lam : ι → DomWeight n) :
    CSpan lam ≤ Submodule.span ℂ ((fun P => MvPolynomial.map s P) '' (VV K lam : Set (MvPolynomial (ι × Fin n × Fin n) K))) := by
  unfold CSpan
  rw [Submodule.span_le]
  rintro _ ⟨f, hf, rfl⟩
  let S : ι → Set (MvPolynomial (ι × Fin n × Fin n) ℂ) := fun τ =>
    Set.range fun w : List (Fin n × Fin n × ℕ) =>
      rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.applyWord ℂ w (Formalism.GradedWeylDivisibility.hw ℂ le_rfl (lam τ).natW))
  have h1 : ∀ τ, rename (Prod.mk τ) (f τ) ∈ Submodule.span ℂ (S τ) := by
    intro τ
    have h := Submodule.mem_map_of_mem (f := (rename (R := ℂ) (Prod.mk τ : Fin n × Fin n → ι × Fin n × Fin n)).toLinearMap) (hf τ)
    unfold delSq Formalism.GradedWeylDivisibility.weyl at h
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  have h2 : Forms.ten f ∈ Submodule.span ℂ (∏ τ, S τ) := by
    rw [← Submodule.prod_span]
    exact prod_mem_prod_sub _ _ _ fun τ _ => h1 τ
  refine Submodule.span_mono ?_ h2
  intro x hx
  rw [Set.mem_finsetProd] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  have hg' : ∀ τ, ∃ w : List (Fin n × Fin n × ℕ),
      rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.applyWord ℂ w (Formalism.GradedWeylDivisibility.hw ℂ le_rfl (lam τ).natW)) = g τ := fun τ => hg (Finset.mem_univ τ)
  choose w hw using hg'
  refine ⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K (w τ) (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW)), ?_, ?_⟩
  · refine Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩
    exact Formalism.GradedWeylDivisibility.weylLeDual K n n le_rfl _ (natW_anti (lam τ)) (Submodule.subset_span ⟨w τ, rfl⟩)
  · simp only
    rw [map_ten, Forms.ten]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← hw τ, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

/- English proof (translation)
Use `letI : Algebra K ℂ := s.toAlgebra`. Establish `B : Module.Basis _ K ℂ` using `Module.Basis.ofVectorSpace K ℂ`. Rewrite `hv`, the goal using `[linearIndependent_iff']`. Introduce `t g hg i hi`. Establish `key : ∀ b, ∀ j ∈ t, B.repr (g j) b = 0`.

Introduce `b`. Apply `hv t (fun j => B.repr (g j) b)` to reduce the goal to its premises. Use extensionality with `m`. Establish `hm` using `congrArg (MvPolynomial.coeff m) hg`. Simplify using `only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, MvPolynomial.coeff_zero] at hm ⊢`.

Establish `hm' : ∑ j ∈ t, (MvPolynomial.coeff m (v j)) • g j = 0`. Use `Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hm` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`. Both sides reduce to the same expression. Establish `h2 : ∑ j ∈ t, (MvPolynomial.coeff m (v j)) * B.repr (g j) b = 0`.

Establish `h3` using `congrArg (fun z => B.repr z b) hm'`. Simplify `h3` using `only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply]`. Conclude with `(Finset.sum_congr rfl fun j _ => mul_comm _ _).trans h2`. Establish `h4 : B.repr (g i) = 0`. Use extensionality with `b`.

Rewrite using `[Finsupp.coe_zero, Pi.zero_apply]`. Conclude with `key b i hi`. Conclude with `B.repr.map_eq_zero_iff.mp h4`.
-/
theorem linearIndependent_map {σ κ : Type} (s : K →+* ℂ) (v : κ → MvPolynomial σ K) (hv : LinearIndependent K v) :
    LinearIndependent ℂ fun i => MvPolynomial.map s (v i) := by
  classical
  letI : Algebra K ℂ := s.toAlgebra
  have B : Module.Basis _ K ℂ := Module.Basis.ofVectorSpace K ℂ
  rw [linearIndependent_iff'] at hv ⊢
  intro t g hg i hi
  have key : ∀ b, ∀ j ∈ t, B.repr (g j) b = 0 := by
    intro b
    apply hv t (fun j => B.repr (g j) b)
    ext m
    have hm := congrArg (MvPolynomial.coeff m) hg
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul,
      MvPolynomial.coeff_zero] at hm ⊢
    have hm' : ∑ j ∈ t, (MvPolynomial.coeff m (v j)) • g j = 0 := by
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hm
      rw [Algebra.smul_def, mul_comm]
      rfl
    have h2 : ∑ j ∈ t, (MvPolynomial.coeff m (v j)) * B.repr (g j) b = 0 := by
      have h3 := congrArg (fun z => B.repr z b) hm'
      simpa only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
        smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] using h3
    exact (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans h2
  have h4 : B.repr (g i) = 0 := by
    ext b
    rw [Finsupp.coe_zero, Pi.zero_apply]
    exact key b i hi
  exact B.repr.map_eq_zero_iff.mp h4

end Image2

section Image3

variable {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Unfold `ValC`. Conclude with `Submodule.mem_map.mpr ⟨_, map_mem_CSpan s lam F.1 F.2, rfl⟩`.
-/
theorem evV_mem_ValC (emb : ι → E →+* K) (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (F : VV K lam) : evV emb J lam s F ∈ ValC (gramC J (embAt s emb)) lam := by
  unfold ValC
  exact Submodule.mem_map.mpr ⟨_, map_mem_CSpan s lam F.1 F.2, rfl⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨F, rfl⟩`. Conclude with `evV_mem_ValC emb J lam s F`. Unfold `ValC`.

Use `(Submodule.map_mono (CSpan_le_span s lam)).trans ?_` and prove the remaining obligations. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨P, ⟨Q, hQ, rfl⟩, rfl⟩`. Conclude with `Submodule.subset_span ⟨⟨Q, hQ⟩, rfl⟩`.
-/
theorem span_evV (emb : ι → E →+* K) (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (s : K →+* ℂ) :
    Submodule.span ℂ (Set.range (evV emb J lam s)) = ValC (gramC J (embAt s emb)) lam := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    exact evV_mem_ValC emb J lam s F
  · unfold ValC
    refine (Submodule.map_mono (CSpan_le_span s lam)).trans ?_
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨P, ⟨Q, hQ, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨⟨Q, hQ⟩, rfl⟩

/- English proof (translation)
Establish `h1 : LinearIndependent K fun i => (b i).1` using `hb.map' (VV K lam).subtype (Submodule.ker_subtype _)`. Establish `h2` using `linearIndependent_map s _ h1`. Conclude with `h2.map' (fnOf _ (shiftOf lam) 1) (LinearMap.ker_eq_bot.mpr (fnOf_injective _ _ 1 (fun _ => by simp) o))`.
-/
theorem evV_linearIndependent (emb : ι → E →+* K) (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (o : Frames (gramC J (embAt s emb))) {κ : Type} (b : κ → VV K lam) (hb : LinearIndependent K b) :
    LinearIndependent ℂ fun i => evV emb J lam s (b i) := by
  have h1 : LinearIndependent K fun i => (b i).1 := hb.map' (VV K lam).subtype (Submodule.ker_subtype _)
  have h2 := linearIndependent_map s _ h1
  exact h2.map' (fnOf _ (shiftOf lam) 1) (LinearMap.ker_eq_bot.mpr (fnOf_injective _ _ 1 (fun _ => by simp) o))

/- English proof (translation)
Establish `hmin : ∀ {r k : ℕ} (t : ℕ) (hr : t ≤ r) (hk : t ≤ k), Formalism.GradedWeylDivisibility.lpMinor K t hr hk ≠ 0`. Introduce `r k t hr hk`. Establish `e : Formalism.GradedWeylDivisibility.lpMinor K t hr hk = MvPolynomial.rename (fun pq : Fin t × Fin t => (Fin.castLE hr pq.1, Fin.castLE hk pq.2)) (Matrix.mvPolynomialX (Fin t) (Fin t) K).det`. Unfold `Formalism.GradedWeylDivisibility.lpMinor`. Rewrite using `[AlgHom.map_det]`.

Use `congr 1`. Use extensionality with `p q`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Use `(map_ne_zero_iff _ (MvPolynomial.rename_injective _ ?_)).mpr (Matrix.det_mvPolynomialX_ne_zero _ _)` and prove the remaining obligations.

Introduce `a b hab`. Simplify using `only [Prod.mk.injEq] at hab`. Conclude with `Prod.ext (Fin.castLE_injective hr hab.1) (Fin.castLE_injective hk hab.2)`. Establish `hext : ∀ τ, extremal K n (lam τ) ≠ 0`. Introduce `τ`.

Unfold `extremal Formalism.GradedWeylDivisibility.hw`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i _`. Conclude with `pow_ne_zero _ (hmin _ _ _)`. Unfold `extV`.

Introduce `h`. Establish `h2 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K (k` using `n) (n := n) τ (extremal K n (lam τ)) : MvPolynomial (ι × Fin n × Fin n) K) = 0 := congrArg Subtype.val h`. Use `Finset.prod_ne_zero_iff.mpr (fun τ _ => ?_) h2` and prove the remaining obligations. Establish `hinj : Function.Injective (Formalism.GradedWeylDivisibility.blockEmb K (k` using `n) (n := n) τ) := MvPolynomial.rename_injective _ (fun a b hab => (Prod.mk.inj hab).2)`. Conclude with `(map_ne_zero_iff _ hinj).mpr (hext τ)`.
-/
theorem extV_ne_zero (lam : ι → DomWeight n) : extV K lam ≠ 0 := by
  have hmin : ∀ {r k : ℕ} (t : ℕ) (hr : t ≤ r) (hk : t ≤ k), Formalism.GradedWeylDivisibility.lpMinor K t hr hk ≠ 0 := by
    intro r k t hr hk
    have e : Formalism.GradedWeylDivisibility.lpMinor K t hr hk =
        MvPolynomial.rename (fun pq : Fin t × Fin t => (Fin.castLE hr pq.1, Fin.castLE hk pq.2))
          (Matrix.mvPolynomialX (Fin t) (Fin t) K).det := by
      unfold Formalism.GradedWeylDivisibility.lpMinor
      rw [AlgHom.map_det]
      congr 1
      ext p q
      simp
    rw [e]
    refine (map_ne_zero_iff _ (MvPolynomial.rename_injective _ ?_)).mpr (Matrix.det_mvPolynomialX_ne_zero _ _)
    intro a b hab
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext (Fin.castLE_injective hr hab.1) (Fin.castLE_injective hk hab.2)
  have hext : ∀ τ, extremal K n (lam τ) ≠ 0 := by
    intro τ
    unfold extremal Formalism.GradedWeylDivisibility.hw
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact pow_ne_zero _ (hmin _ _ _)
  unfold extV
  intro h
  have h2 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ (extremal K n (lam τ)) :
      MvPolynomial (ι × Fin n × Fin n) K) = 0 := congrArg Subtype.val h
  refine Finset.prod_ne_zero_iff.mpr (fun τ _ => ?_) h2
  have hinj : Function.Injective (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ) :=
    MvPolynomial.rename_injective _ (fun a b hab => (Prod.mk.inj hab).2)
  exact (map_ne_zero_iff _ hinj).mpr (hext τ)

/- English proof (translation)
Establish `hli : LinearIndependent K (fun _ : Unit => extV K lam)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Rewrite `hg` using `[Fintype.sum_unique]`. Consider the cases of `i`.

Conclude with `(smul_eq_zero.mp hg).resolve_right (extV_ne_zero lam)`. Establish `h` using `evV_linearIndependent emb J lam s o (fun _ : Unit => extV K lam) hli`. Conclude with `h.ne_zero ()`.
-/
theorem evV_extV_ne_zero (emb : ι → E →+* K) (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (o : Frames (gramC J (embAt s emb))) : evV emb J lam s (extV K lam) ≠ 0 := by
  have hli : LinearIndependent K (fun _ : Unit => extV K lam) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fintype.sum_unique] at hg
    cases i
    exact (smul_eq_zero.mp hg).resolve_right (extV_ne_zero lam)
  have h := evV_linearIndependent emb J lam s o (fun _ : Unit => extV K lam) hli
  exact h.ne_zero ()

end Image3

section Metric

variable {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.smul_eval]`. Rewrite using `[eval_blockAct u (fun τ => M τ * y.1 τ) P]`. Simplify using `only [Matrix.mul_assoc, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fnOf_mul (G : ι → Matrix (Fin n) (Fin n) ℂ) (sh : ι → ℤ) (u M : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    fnOf G sh (fun τ => u τ * M τ) P = fnOf G sh M ((∏ τ, (u τ).det ^ sh τ) • blockAct ℂ u P) := by
  funext y
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.smul_eval]
  rw [eval_blockAct u (fun τ => M τ * y.1 τ) P]
  simp only [Matrix.mul_assoc, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

/- English proof (translation)
Establish `key : (blockAct ℂ (n` using `n) (fun τ => (u τ)ᴴ)).comp (blockAct ℂ (n := n) u) = AlgHom.id ℂ _ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, b, c⟩`. Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply, Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]`. Simplify using `only [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_mul, ← map_sum]`. Establish `hmul : ∀ d, ∑ x : Fin n, u a b x * (u a)ᴴ x d = (1 : Matrix (Fin n) (Fin n) ℂ) b d`. Introduce `d`. Rewrite using `[← hu a, Matrix.mul_apply]`.

Simplify using `only [hmul, Matrix.one_apply]`. Simplify using the standard rewrite rules. Establish `comp : ∀ q, blockAct ℂ (n` using `n) (fun τ => (u τ)ᴴ) (blockAct ℂ (n := n) u q) = q := fun q => DFunLike.congr_fun key q`. Unfold `nfAll`. Rewrite using `[fockF_blockAct, comp]`.
-/
theorem nfAll_blockAct (lam : ι → DomWeight n) (u : ι → Matrix (Fin n) (Fin n) ℂ) (hu : ∀ τ, u τ * (u τ)ᴴ = 1)
    (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam (blockAct ℂ u p) (blockAct ℂ u q) = nfAll lam p q := by
  have key : (blockAct ℂ (n := n) (fun τ => (u τ)ᴴ)).comp (blockAct ℂ (n := n) u) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, b, c⟩
    simp only [AlgHom.comp_apply, AlgHom.id_apply, Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_X, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    simp only [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← map_sum]
    have hmul : ∀ d, ∑ x : Fin n, u a b x * (u a)ᴴ x d = (1 : Matrix (Fin n) (Fin n) ℂ) b d := by
      intro d
      rw [← hu a, Matrix.mul_apply]
    simp only [hmul, Matrix.one_apply]
    simp
  have comp : ∀ q, blockAct ℂ (n := n) (fun τ => (u τ)ᴴ) (blockAct ℂ (n := n) u q) = q := fun q =>
    DFunLike.congr_fun key q
  unfold nfAll
  rw [fockF_blockAct, comp]

/- English proof (translation)
Use `set u : ι → Matrix (Fin n) (Fin n) ℂ := fun τ => (o'.1 τ)⁻¹ * o.1 τ with hu`. Establish `e1 : (fun τ => (o'.1 τ)⁻¹) = fun τ => u τ * (o.1 τ)⁻¹`. Use function extensionality and compare the values at `τ`. Rewrite using `[hu, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det_fr o τ), Matrix.mul_one]`. Establish `hu1 : ∀ τ, (u τ)ᴴ * u τ = 1`.

Introduce `τ`. Establish `h1` using `ho τ`. Rewrite `h1` using `[eq_of_frame _ _ (ho' τ)]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hu, conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc]`.

Use `_ = 1 := h1`. Establish `hu2 : ∀ τ, u τ * (u τ)ᴴ = 1` using `fun τ => mul_eq_one_comm.mp (hu1 τ)`. Establish `hc : (∏ τ, (u τ).det ^ shiftOf lam τ) * star (∏ τ, (u τ).det ^ shiftOf lam τ) = 1`. Rewrite using `[star_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[star_zpow₀, ← mul_zpow, ← det_conjTranspose, ← det_mul, hu2, det_one, _root_.one_zpow]`. Rewrite using `[e1, fnOf_mul, fnOf_mul, ipFr_apply, polOf_fnOf, polOf_fnOf, ← nfL_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, nfL_apply, nfAll_blockAct lam u hu2, smul_smul, starRingEnd_apply, hc, one_smul]`.
-/
theorem ipFr_fnOf (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (o o' : Frames G)
    (ho : ∀ τ, (o.1 τ)ᴴ * G τ * o.1 τ = 1) (ho' : ∀ τ, (o'.1 τ)ᴴ * G τ * o'.1 τ = 1)
    (P Q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    ipFr G lam o (fnOf G (shiftOf lam) (fun τ => (o'.1 τ)⁻¹) P) (fnOf G (shiftOf lam) (fun τ => (o'.1 τ)⁻¹) Q) =
      nfAll lam Q P := by
  set u : ι → Matrix (Fin n) (Fin n) ℂ := fun τ => (o'.1 τ)⁻¹ * o.1 τ with hu
  have e1 : (fun τ => (o'.1 τ)⁻¹) = fun τ => u τ * (o.1 τ)⁻¹ := by
    funext τ
    rw [hu, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det_fr o τ), Matrix.mul_one]
  have hu1 : ∀ τ, (u τ)ᴴ * u τ = 1 := by
    intro τ
    have h1 := ho τ
    rw [eq_of_frame _ _ (ho' τ)] at h1
    calc (u τ)ᴴ * u τ = (o.1 τ)ᴴ * (((o'.1 τ)ᴴ)⁻¹ * (o'.1 τ)⁻¹) * o.1 τ := by
          simp only [hu, conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc]
      _ = 1 := h1
  have hu2 : ∀ τ, u τ * (u τ)ᴴ = 1 := fun τ => mul_eq_one_comm.mp (hu1 τ)
  have hc : (∏ τ, (u τ).det ^ shiftOf lam τ) * star (∏ τ, (u τ).det ^ shiftOf lam τ) = 1 := by
    rw [star_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [star_zpow₀, ← mul_zpow, ← det_conjTranspose, ← det_mul, hu2, det_one, _root_.one_zpow]
  rw [e1, fnOf_mul, fnOf_mul, ipFr_apply, polOf_fnOf, polOf_fnOf, ← nfL_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply,
    nfL_apply, nfAll_blockAct lam u hu2, smul_smul, starRingEnd_apply, hc, one_smul]

end Metric

section Metric2

variable {E K : Type} [Field E] [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Establish `e1 : (1 : ι → Matrix (Fin n) (Fin n) ℂ) = fun τ => o.1 τ * (o.1 τ)⁻¹`. Use function extensionality and compare the values at `τ`. Rewrite using `[Matrix.mul_nonsing_inv _ (isUnit_det_fr o τ)]`. Both sides reduce to the same expression. Establish `hc : (∏ τ, (o.1 τ).det ^ shiftOf lam τ) * star (∏ τ, (o.1 τ).det ^ shiftOf lam τ) = ((∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf lam τ) : ℝ) : ℂ)`.

Rewrite using `[star_prod, ← Finset.prod_mul_distrib, Complex.ofReal_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[star_zpow₀, ← mul_zpow, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, _root_.zpow_mul, Complex.ofReal_zpow]`. Use `congr 1`. Rewrite using `[pairVr_nfAll emb J lam s o ho F F' hF, evV_apply, evV_apply, e1, fnOf_mul, fnOf_mul, ipFr_apply, polOf_fnOf, polOf_fnOf, ← nfL_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, nfL_apply, smul_smul, starRingEnd_apply, hc, smul_eq_mul]`.
-/
theorem ipFr_evV (emb : ι → E →+* K) (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (o : Frames (gramC J (embAt s emb))) (ho : ∀ τ, (o.1 τ)ᴴ * gramC J (embAt s emb) τ * o.1 τ = 1)
    (F F' : VV K lam) (hF : ∀ m, s (star (F.1.coeff m)) = star (s (F.1.coeff m))) :
    ipFr (gramC J (embAt s emb)) lam o (evV emb J lam s F) (evV emb J lam s F') = s (pairVr emb lam J F F') := by
  have e1 : (1 : ι → Matrix (Fin n) (Fin n) ℂ) = fun τ => o.1 τ * (o.1 τ)⁻¹ := by
    funext τ
    rw [Matrix.mul_nonsing_inv _ (isUnit_det_fr o τ)]
    rfl
  have hc : (∏ τ, (o.1 τ).det ^ shiftOf lam τ) * star (∏ τ, (o.1 τ).det ^ shiftOf lam τ) =
      ((∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf lam τ) : ℝ) : ℂ) := by
    rw [star_prod, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [star_zpow₀, ← mul_zpow, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, _root_.zpow_mul,
      Complex.ofReal_zpow]
    congr 1
  rw [pairVr_nfAll emb J lam s o ho F F' hF, evV_apply, evV_apply, e1, fnOf_mul, fnOf_mul, ipFr_apply, polOf_fnOf, polOf_fnOf,
    ← nfL_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, nfL_apply, smul_smul, starRingEnd_apply, hc, smul_eq_mul]

end Metric2

section Examples

/- English proof (translation)
Rewrite using `[evFr_apply]`. Simplify using `[stdFr]`.
-/
example (τ : Unit) (s : ℚ →+* ℂ) :
    evFr (fun _ : Unit => (1 : Matrix (Fin 2) (Fin 2) ℂ)) (fun _ => -3) s (X (τ, 0, 0)) stdFr = 1 := by
  rw [evFr_apply]
  simp [stdFr]

/- English proof (translation)
Rewrite using `[evFr_apply]`. Simplify using `[stdFr]`.
-/
example (τ : Unit) (s : ℚ →+* ℂ) :
    evFr (fun _ : Unit => (1 : Matrix (Fin 2) (Fin 2) ℂ)) (fun _ => -3) s (X (τ, 0, 1)) stdFr = 0 := by
  rw [evFr_apply]
  simp [stdFr]

end Examples

end Formalism.L2.Col
