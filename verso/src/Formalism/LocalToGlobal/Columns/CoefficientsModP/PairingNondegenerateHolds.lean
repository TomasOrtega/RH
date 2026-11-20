import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

open MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

open scoped MatrixOrder in

/- English proof (translation)
Establish `h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ T` using `Matrix.nonneg_iff_posSemidef.2 hT.posSemidef`. Use `⟨CFC.sqrt T, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `hz`. Establish `hdet` using `hT.det_pos`.

Rewrite `hdet` using `[← CFC.sqrt_mul_sqrt_self T h0, Matrix.det_mul, hz, zero_mul]`. Conclude with `lt_irrefl _ hdet`. Establish `hsa : (CFC.sqrt T)ᴴ = CFC.sqrt T` using `(CFC.sqrt_nonneg T).isSelfAdjoint.star_eq`. Rewrite using `[hsa, CFC.sqrt_mul_sqrt_self T h0]`.
-/
theorem ps_factor {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ T = B * Bᴴ := by
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ T := Matrix.nonneg_iff_posSemidef.2 hT.posSemidef
  refine ⟨CFC.sqrt T, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero]
    intro hz
    have hdet := hT.det_pos
    rw [← CFC.sqrt_mul_sqrt_self T h0, Matrix.det_mul, hz, zero_mul] at hdet
    exact lt_irrefl _ hdet
  · have hsa : (CFC.sqrt T)ᴴ = CFC.sqrt T := (CFC.sqrt_nonneg T).isSelfAdjoint.star_eq
    rw [hsa, CFC.sqrt_mul_sqrt_self T h0]

/- English proof (translation)
Set `Bi : ι → Matrix (Fin n) (Fin n) K` to `fun τ => (B τ)⁻¹`. Establish `hcomp : (Formalism.GradedWeylDivisibility.blockAct K (n` using `n) Bi).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) B) = AlgHom.id K _ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨τ, a, j⟩`. Establish `hBB : B τ * Bi τ = 1` using `Matrix.mul_nonsing_inv _ (hB τ)`.

Simplify using `only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_sum, map_mul, aeval_C, AlgHom.id_apply, MvPolynomial.algebraMap_eq]`. Simplify using `only [Finset.mul_sum, ← mul_assoc, ← map_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_mul, ← map_sum]`. Establish `hc : ∀ c : Fin n, ∑ b : Fin n, B τ a b * Bi τ b c = (1 : Matrix (Fin n) (Fin n) K) a c`.

Introduce `c`. Rewrite using `[← hBB, Matrix.mul_apply]`. Simplify using `only [hc, Matrix.one_apply]`. Simplify using `[apply_ite C, ite_mul]`. Introduce `x y hxy`.

Use `congrArg (Formalism.GradedWeylDivisibility.blockAct K (n := n) Bi) hxy` as an intermediate fact. Rewrite `this` using `[← AlgHom.comp_apply, ← AlgHom.comp_apply, hcomp]`. Simplify using `using this`.
-/
theorem ps_blockAct_injective {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}
    (B : ι → Matrix (Fin n) (Fin n) K) (hB : ∀ τ, IsUnit (B τ).det) :
    Function.Injective (Formalism.GradedWeylDivisibility.blockAct K (n := n) B) := by
  classical
  let Bi : ι → Matrix (Fin n) (Fin n) K := fun τ => (B τ)⁻¹
  have hcomp : (Formalism.GradedWeylDivisibility.blockAct K (n := n) Bi).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) B) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, a, j⟩
    have hBB : B τ * Bi τ = 1 := Matrix.mul_nonsing_inv _ (hB τ)
    simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_sum, map_mul, aeval_C, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq]
    simp only [Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← map_sum]
    have hc : ∀ c : Fin n, ∑ b : Fin n, B τ a b * Bi τ b c = (1 : Matrix (Fin n) (Fin n) K) a c := by
      intro c
      rw [← hBB, Matrix.mul_apply]
    simp only [hc, Matrix.one_apply]
    simp [apply_ite C, ite_mul]
  intro x y hxy
  have := congrArg (Formalism.GradedWeylDivisibility.blockAct K (n := n) Bi) hxy
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, hcomp] at this
  simpa using this

/- English proof (translation)
Unfold `Formalism.REAL.fockF`. Establish `hne : f.support.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]`. Conclude with `hf`. Apply `Finset.sum_pos _ hne` to reduce the goal to its premises.

Introduce `m hm`. Establish `hc : f.coeff m ≠ 0` using `MvPolynomial.mem_support_iff.1 hm`. Establish `h1 : f.coeff m * star (f.coeff m) = ((Complex.normSq (f.coeff m) : ℝ) : ℂ)`. Rewrite using `[Complex.star_def, Complex.mul_conj]`. Rewrite using `[h1]`.

Establish `h2 : (0 : ℝ) < Complex.normSq (f.coeff m)` using `Complex.normSq_pos.2 hc`. Establish `h3 : (0 : ℝ) < ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ)`. Conclude with `Finset.prod_pos fun k _ => Nat.factorial_pos _` after adjusting the coercions. Establish `e : ((Complex.normSq (f.coeff m) : ℝ) : ℂ) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) = ((Complex.normSq (f.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) : ℝ) : ℂ)`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Complex.zero_lt_real.2 (mul_pos h2 h3)`.
-/
theorem ps_fockF_pos {σ : Type} (f : MvPolynomial σ ℂ) (hf : f ≠ 0) : 0 < Formalism.REAL.fockF f f := by
  unfold Formalism.REAL.fockF
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hf
  apply Finset.sum_pos _ hne
  intro m hm
  have hc : f.coeff m ≠ 0 := MvPolynomial.mem_support_iff.1 hm
  have h1 : f.coeff m * star (f.coeff m) = ((Complex.normSq (f.coeff m) : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  rw [h1]
  have h2 : (0 : ℝ) < Complex.normSq (f.coeff m) := Complex.normSq_pos.2 hc
  have h3 : (0 : ℝ) < ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
  have e : ((Complex.normSq (f.coeff m) : ℝ) : ℂ) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) =
      ((Complex.normSq (f.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e]
  exact Complex.zero_lt_real.2 (mul_pos h2 h3)

/- English proof (translation)
Rewrite using `[Formalism.L2.Col.nfL_apply, Formalism.L2.Forms.nfAll]`. Use `div_pos (ps_fockF_pos F hF) (Finset.prod_pos fun τ _ => ?_)` and prove the remaining obligations. Conclude with `ps_fockF_pos _ (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _)`.
-/
theorem ps_nfL_pos {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hF : F ≠ 0) : 0 < Formalism.L2.Col.nfL lam F F := by
  rw [Formalism.L2.Col.nfL_apply, Formalism.L2.Forms.nfAll]
  refine div_pos (ps_fockF_pos F hF) (Finset.prod_pos fun τ _ => ?_)
  exact ps_fockF_pos _ (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _)

/- English proof (translation)
Rewrite using `[Formalism.L2.Col.nfL_apply, Formalism.L2.Col.nfL_apply, Formalism.L2.Forms.nfAll, Formalism.L2.Forms.nfAll, star_div₀, ← Formalism.GradedWeylDivisibility.fockHerm, star_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Conclude with `(Formalism.GradedWeylDivisibility.fockHerm _ _ _).symm`.
-/
theorem ps_nfL_symm {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F F' : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    star (Formalism.L2.Col.nfL lam F F') = Formalism.L2.Col.nfL lam F' F := by
  rw [Formalism.L2.Col.nfL_apply, Formalism.L2.Col.nfL_apply, Formalism.L2.Forms.nfAll, Formalism.L2.Forms.nfAll, star_div₀,
    ← Formalism.GradedWeylDivisibility.fockHerm, star_prod]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact (Formalism.GradedWeylDivisibility.fockHerm _ _ _).symm

/- English proof (translation)
Introduce `K _ _ ι _ n lam G φ hG`. Use `choose B hBu hB using fun τ => ps_factor (hG τ).transpose`. Use `set P : VVIdx lam → MvPolynomial (ι × Fin n × Fin n) ℂ := fun i => Formalism.GradedWeylDivisibility.blockAct ℂ B (map φ (bVVfun K lam i)) with hP`. Use `set c : ℂ := ∏ τ, ((G τ).map φ).det ^ (lam τ).detShift with hc`. Establish `hM : ∀ i j, φ (pairK lam G (bVV K lam i) (bVV K lam j)) = c * Formalism.L2.Col.nfL lam (P i) (P j)`.

Introduce `i j`. Rewrite using `[pairK_apply, bVV_coe, bVV_coe, Formalism.L2.Col.map_pairP φ lam G B hB _ _ ?_, Formalism.L2.Col.nfL_apply]`. Introduce `m`. Take `⟨Q, hQ⟩` from `bVVfun_int K lam i`. Rewrite using `[hQ, coeff_map]`.

Simplify using the standard rewrite rules. Establish `hli : LinearIndependent ℂ P`. Establish `h1` using `Formalism.L2.Col.linearIndependent_map φ (bVVfun K lam) (bVVfun_spec K lam).1`. Conclude with `h1.map' (Formalism.GradedWeylDivisibility.blockAct ℂ B).toLinearMap (LinearMap.ker_eq_bot.mpr (ps_blockAct_injective B hBu))`. Establish `hcpos : 0 < c` using `Finset.prod_pos fun τ _ => zpow_pos (hG τ).det_pos _`.

Establish `hcs : star c = c` using `(IsSelfAdjoint.of_nonneg hcpos.le).star_eq`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, hM, hM, star_mul', hcs, ps_nfL_symm]`. Introduce `x hx`.

Establish `e : star x ⬝ᵥ (Matrix.of fun i j : VVIdx lam => φ (pairK lam G (bVV K lam i) (bVV K lam j))) *ᵥ x = c * Formalism.L2.Col.nfL lam (∑ i, x i • P i) (∑ j, x j • P j)`. Simplify using `only [dotProduct, Matrix.mulVec, Matrix.of_apply, hM, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, Pi.star_apply, starRingEnd_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `mul_pos hcpos (ps_nfL_pos lam _ ?_)` and prove the remaining obligations. Introduce `h0`. Conclude with `hx (funext fun i => Fintype.linearIndependent_iff.mp hli x h0 i)`.
-/
theorem pairingPositive_holds : PairPos := by
  classical
  intro K _ _ ι _ n lam G φ hG
  choose B hBu hB using fun τ => ps_factor (hG τ).transpose
  set P : VVIdx lam → MvPolynomial (ι × Fin n × Fin n) ℂ :=
    fun i => Formalism.GradedWeylDivisibility.blockAct ℂ B (map φ (bVVfun K lam i)) with hP
  set c : ℂ := ∏ τ, ((G τ).map φ).det ^ (lam τ).detShift with hc
  have hM : ∀ i j, φ (pairK lam G (bVV K lam i) (bVV K lam j)) = c * Formalism.L2.Col.nfL lam (P i) (P j) := by
    intro i j
    rw [pairK_apply, bVV_coe, bVV_coe, Formalism.L2.Col.map_pairP φ lam G B hB _ _ ?_, Formalism.L2.Col.nfL_apply]
    intro m
    obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
    rw [hQ, coeff_map]
    simp
  have hli : LinearIndependent ℂ P := by
    have h1 := Formalism.L2.Col.linearIndependent_map φ (bVVfun K lam) (bVVfun_spec K lam).1
    exact h1.map' (Formalism.GradedWeylDivisibility.blockAct ℂ B).toLinearMap (LinearMap.ker_eq_bot.mpr (ps_blockAct_injective B hBu))
  have hcpos : 0 < c := Finset.prod_pos fun τ _ => zpow_pos (hG τ).det_pos _
  have hcs : star c = c := (IsSelfAdjoint.of_nonneg hcpos.le).star_eq
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, hM, hM, star_mul', hcs, ps_nfL_symm]
  · intro x hx
    have e : star x ⬝ᵥ (Matrix.of fun i j : VVIdx lam => φ (pairK lam G (bVV K lam i) (bVV K lam j))) *ᵥ x =
        c * Formalism.L2.Col.nfL lam (∑ i, x i • P i) (∑ j, x j • P j) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, hM, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
        LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, Pi.star_apply, starRingEnd_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]
    refine mul_pos hcpos (ps_nfL_pos lam _ ?_)
    intro h0
    exact hx (funext fun i => Fintype.linearIndependent_iff.mp hli x h0 i)

/- English proof (translation)
Use `show Formalism.L2.DIV.fockS f g = Formalism.GradedWeylDivisibility.fockQ f g`. Unfold `Formalism.L2.DIV.fockS Formalism.GradedWeylDivisibility.fockQ`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [star_trivial]`. Both sides reduce to the same expression.
-/
theorem ps_fockL_rat {σ : Type} (f g : MvPolynomial σ ℚ) : fockL f g = Formalism.GradedWeylDivisibility.fockQ f g := by
  show Formalism.L2.DIV.fockS f g = Formalism.GradedWeylDivisibility.fockQ f g
  unfold Formalism.L2.DIV.fockS Formalism.GradedWeylDivisibility.fockQ
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_trivial]
  rfl

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.fockQ`. Use `Finset.sum_subset hs fun m _ hm => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.notMem_support_iff.1 hm]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma fockQ_eq_sum_coeff_mul_factorial {σ : Type} (f g : MvPolynomial σ ℚ) (s : Finset (σ →₀ ℕ)) (hs : f.support ⊆ s) :
    Formalism.GradedWeylDivisibility.fockQ f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold Formalism.GradedWeylDivisibility.fockQ
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm]
  ring

/- English proof (translation)
Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet`. Use `set S : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun i => (q i).support with hS`. Use `set w : (σ →₀ ℕ) → ℚ := fun m => ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) with hw`. Use `set p : MvPolynomial σ ℚ := ∑ j, v j • q j with hp`.

Establish `hpc : ∀ m, p.coeff m = ∑ j, v j * (q j).coeff m`. Introduce `m`. Simplify using `[hp, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul]`. Establish `hsub : ∀ i, (q i).support ⊆ S` using `fun i => Finset.subset_biUnion_of_mem (fun j => (q j).support) (Finset.mem_univ i)`. Establish `hwpos : ∀ m, 0 < w m` using `fun m => by`.

Simplify using `only [hw]`. Conclude with `Finset.prod_pos fun k _ => Nat.factorial_pos _` after adjusting the coercions. Establish `e1 : ∀ i, ∑ j, Formalism.GradedWeylDivisibility.fockQ (q i) (q j) * v j = 0`. Introduce `i`. Use `congrFun hv i` as an intermediate fact.

Simplify `this` using `[Matrix.mulVec, dotProduct]`. Establish `hexp : ∀ m, p.coeff m * p.coeff m * w m = ∑ i, ∑ j, v i * (q i).coeff m * (v j * (q j).coeff m) * w m`. Introduce `m`. Rewrite using `[hpc, Finset.sum_mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_mul]`. Establish `hkey : ∑ m ∈ S, p.coeff m * p.coeff m * w m = 0`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[fockQ_eq_sum_coeff_mul_factorial (q i) (q j) S (hsub i), Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [hw]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = 0 := by simp [e1]`. Establish `hzero : ∀ m ∈ S, p.coeff m = 0`. Establish `hnn : ∀ m ∈ S, 0 ≤ p.coeff m * p.coeff m * w m` using `fun m _ => mul_nonneg (mul_self_nonneg _) (hwpos m).le`. Introduce `m hm`. Establish `h0` using `(Finset.sum_eq_zero_iff_of_nonneg hnn).1 hkey m hm`.

Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `mul_self_eq_zero.1 h`. Conclude with `absurd h (hwpos m).ne'`. Establish `hp0 : p = 0`. Use extensionality with `m`.

Distinguish the cases in `hm : m ∈ S`. Simplify using `using hzero m hm`. Rewrite using `[hpc, MvPolynomial.coeff_zero]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `hj : m ∉ (q j).support` using `fun h => hm (hsub j h)`.

Rewrite using `[MvPolynomial.notMem_support_iff.1 hj, mul_zero]`. Establish `hv'` using `(Fintype.linearIndependent_iff.1 hq) v (by rw [← hp]; exact hp0)`. Conclude with `hv0 (funext hv')`.
-/
theorem ps_gram_det_ne {σ κ : Type} [Fintype κ] [DecidableEq κ] (q : κ → MvPolynomial σ ℚ)
    (hq : LinearIndependent ℚ q) : (Matrix.of fun i j => Formalism.GradedWeylDivisibility.fockQ (q i) (q j)).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set S : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun i => (q i).support with hS
  set w : (σ →₀ ℕ) → ℚ := fun m => ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) with hw
  set p : MvPolynomial σ ℚ := ∑ j, v j • q j with hp
  have hpc : ∀ m, p.coeff m = ∑ j, v j * (q j).coeff m := by
    intro m
    simp [hp, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul]
  have hsub : ∀ i, (q i).support ⊆ S := fun i =>
    Finset.subset_biUnion_of_mem (fun j => (q j).support) (Finset.mem_univ i)
  have hwpos : ∀ m, 0 < w m := fun m => by
    simp only [hw]
    exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
  have e1 : ∀ i, ∑ j, Formalism.GradedWeylDivisibility.fockQ (q i) (q j) * v j = 0 := by
    intro i
    have := congrFun hv i
    simpa [Matrix.mulVec, dotProduct] using this
  have hexp : ∀ m, p.coeff m * p.coeff m * w m =
      ∑ i, ∑ j, v i * (q i).coeff m * (v j * (q j).coeff m) * w m := by
    intro m
    rw [hpc, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  have hkey : ∑ m ∈ S, p.coeff m * p.coeff m * w m = 0 := by
    calc ∑ m ∈ S, p.coeff m * p.coeff m * w m
        = ∑ m ∈ S, ∑ i, ∑ j, v i * (q i).coeff m * (v j * (q j).coeff m) * w m :=
          Finset.sum_congr rfl fun m _ => hexp m
      _ = ∑ i, ∑ m ∈ S, ∑ j, v i * (q i).coeff m * (v j * (q j).coeff m) * w m := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ m ∈ S, v i * (q i).coeff m * (v j * (q j).coeff m) * w m :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, v i * ∑ j, Formalism.GradedWeylDivisibility.fockQ (q i) (q j) * v j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [fockQ_eq_sum_coeff_mul_factorial (q i) (q j) S (hsub i), Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          simp only [hw]
          ring
      _ = 0 := by simp [e1]
  have hzero : ∀ m ∈ S, p.coeff m = 0 := by
    have hnn : ∀ m ∈ S, 0 ≤ p.coeff m * p.coeff m * w m :=
      fun m _ => mul_nonneg (mul_self_nonneg _) (hwpos m).le
    intro m hm
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hkey m hm
    rcases mul_eq_zero.1 h0 with h | h
    · exact mul_self_eq_zero.1 h
    · exact absurd h (hwpos m).ne'
  have hp0 : p = 0 := by
    ext m
    by_cases hm : m ∈ S
    · simpa using hzero m hm
    · rw [hpc, MvPolynomial.coeff_zero]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hj : m ∉ (q j).support := fun h => hm (hsub j h)
      rw [MvPolynomial.notMem_support_iff.1 hj, mul_zero]
  have hv' := (Fintype.linearIndependent_iff.1 hq) v (by rw [← hp]; exact hp0)
  exact hv0 (funext hv')

/- English proof (translation)
Take `⟨P, hP⟩` from `bVVfun_int K lam i`. Use `⟨map (Int.castRingHom ℚ) P, ?_⟩` and prove the remaining obligations. Rewrite using `[hP, map_map]`. Establish `e : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K` using `RingHom.ext_int _ _`. Rewrite using `[e]`.
-/
theorem ps_bVVfun_rat (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (i : VVIdx lam) : ∃ q : MvPolynomial (ι × Fin n × Fin n) ℚ, bVVfun K lam i = map (algebraMap ℚ K) q := by
  obtain ⟨P, hP⟩ := bVVfun_int K lam i
  refine ⟨map (Int.castRingHom ℚ) P, ?_⟩
  rw [hP, map_map]
  have e : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K := RingHom.ext_int _ _
  rw [e]

/- English proof (translation)
Use `choose q hq using ps_bVVfun_rat K lam`. Establish `hli : LinearIndependent ℚ q`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Establish `h1` using `congrArg (map (algebraMap ℚ K)) hg`.

Simplify using `only [map_sum, smul_eq_C_mul, map_mul, map_C, ← hq, map_zero] at h1`. Simplify using `only [← smul_eq_C_mul] at h1`. Establish `h2` using `Fintype.linearIndependent_iff.mp (bVVfun_spec K lam).1 (fun i => algebraMap ℚ K (g i)) h1 i`. Conclude with `(map_eq_zero (algebraMap ℚ K)).mp h2`. Establish `hdet` using `ps_gram_det_ne q hli`.

Use `set Q : Matrix (VVIdx lam) (VVIdx lam) ℚ := Matrix.of fun i j => Formalism.GradedWeylDivisibility.fockQ (q i) (q j) with hQ`. Establish `hdetK : ((algebraMap ℚ K).mapMatrix Q).det ≠ 0`. Rewrite using `[← RingHom.map_det]`. Conclude with `(map_ne_zero (algebraMap ℚ K)).mpr hdet`. Use `set c := (bVV K lam).repr ⟨x, hx⟩ with hc`.

Establish `hxc : x = ∑ i, c i • bVVfun K lam i`. Establish `h1` using `(bVV K lam).sum_repr ⟨x, hx⟩`. Establish `h2` using `congrArg (Subtype.val) h1`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe] at h2`. Conclude with `h2.symm`.

Establish `hv : (fun i => star (c i)) ᵥ* ((algebraMap ℚ K).mapMatrix Q) = 0`. Use function extensionality and compare the values at `j`. Establish `h1` using `h (bVVfun K lam j) (by rw [← bVV_coe]; exact (bVV K lam j).2)`. Rewrite `h1` using `[hxc]`. Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at h1`.

Simplify using `only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, hQ, Matrix.of_apply, Pi.zero_apply]`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hq i, hq j, fockL_apply, fockSQ K]`. Establish `hc0` using `Matrix.eq_zero_of_vecMul_eq_zero hdetK hv`.

Rewrite using `[hxc]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `: star (c i) = 0` using `congrFun hc0 i`. Rewrite using `[star_eq_zero.mp this, zero_smul]`.
-/
theorem ps_fock_sep {K : Type} [Field K] [StarRing K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (x : Pol K ι n) (hx : x ∈ VV K lam) (h : ∀ y ∈ VV K lam, fockL x y = 0) : x = 0 := by
  classical
  choose q hq using ps_bVVfun_rat K lam
  have hli : LinearIndependent ℚ q := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrArg (map (algebraMap ℚ K)) hg
    simp only [map_sum, smul_eq_C_mul, map_mul, map_C, ← hq, map_zero] at h1
    simp only [← smul_eq_C_mul] at h1
    have h2 := Fintype.linearIndependent_iff.mp (bVVfun_spec K lam).1 (fun i => algebraMap ℚ K (g i)) h1 i
    exact (map_eq_zero (algebraMap ℚ K)).mp h2
  have hdet := ps_gram_det_ne q hli
  set Q : Matrix (VVIdx lam) (VVIdx lam) ℚ := Matrix.of fun i j => Formalism.GradedWeylDivisibility.fockQ (q i) (q j) with hQ
  have hdetK : ((algebraMap ℚ K).mapMatrix Q).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact (map_ne_zero (algebraMap ℚ K)).mpr hdet
  set c := (bVV K lam).repr ⟨x, hx⟩ with hc
  have hxc : x = ∑ i, c i • bVVfun K lam i := by
    have h1 := (bVV K lam).sum_repr ⟨x, hx⟩
    have h2 := congrArg (Subtype.val) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe] at h2
    exact h2.symm
  have hv : (fun i => star (c i)) ᵥ* ((algebraMap ℚ K).mapMatrix Q) = 0 := by
    funext j
    have h1 := h (bVVfun K lam j) (by rw [← bVV_coe]; exact (bVV K lam j).2)
    rw [hxc] at h1
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply] at h1
    simp only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, hQ, Matrix.of_apply, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hq i, hq j, fockL_apply, fockSQ K]
  have hc0 := Matrix.eq_zero_of_vecMul_eq_zero hdetK hv
  rw [hxc]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : star (c i) = 0 := congrFun hc0 i
  rw [star_eq_zero.mp this, zero_smul]

/- English proof (translation)
The claim follows from `(Formalism.GradedWeylDivisibility.blockActTensor K K ι n n U).2 (fun τ => nablaSq K n (lam τ)) (fun τ => nablaSq K n (lam τ)) (fun _ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable K n n _ _ f hf) F hF`.
-/
theorem ps_blockAct_mem_VV {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (U : ι → Matrix (Fin n) (Fin n) K) {F : Pol K ι n} (hF : F ∈ VV K lam) :
    Formalism.GradedWeylDivisibility.blockAct K U F ∈ VV K lam :=
  (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n U).2 (fun τ => nablaSq K n (lam τ)) (fun τ => nablaSq K n (lam τ))
    (fun _ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable K n n _ _ f hf) F hF

/- English proof (translation)
Introduce `K _ _ _ ι _ n lam G hG`. Establish `hGt : ∀ τ, IsUnit ((G τ)ᵀ).det` using `fun τ => by rw [Matrix.det_transpose]; exact hG τ`. Establish `hc : gramTw lam G / extNorm K lam ≠ 0`. Take `⟨r, hr, he⟩` from `extNormPos K ι n lam`. Use `div_ne_zero ?_ ?_` and prove the remaining obligations.

Unfold `gramTw`. Conclude with `Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hG τ).ne_zero`. Rewrite using `[he]`. Conclude with `(map_ne_zero (algebraMap ℚ K)).mpr hr.ne'`. Establish `e : (Formalism.GradedWeylDivisibility.blockAct K (n` using `n) fun τ => (G τ)ᵀ).comp (Formalism.GradedWeylDivisibility.blockAct K fun τ => ((G τ)ᵀ)⁻¹) = AlgHom.id K _ := by`.

Rewrite using `[blockAct_comp, ← blockAct_one]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Conclude with `Matrix.nonsing_inv_mul _ (hGt τ)`. Prove the components needed by the constructor for the conclusion.

Introduce `x hx`. Apply `Subtype.ext` to reduce the goal to its premises. Use `ps_fock_sep lam x.1 x.2 fun y hy => ?_` and prove the remaining obligations. Establish `h1` using `hx ⟨Formalism.GradedWeylDivisibility.blockAct K (fun τ => ((G τ)ᵀ)⁻¹) y, ps_blockAct_mem_VV lam _ hy⟩`. Rewrite `h1` using `[pairK_apply, pairP_apply, ← AlgHom.comp_apply, e]`.

Conclude with `(mul_eq_zero.mp h1).resolve_left hc`. Introduce `y hy`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h0 : Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y.1 = 0`. Use `ps_fock_sep lam _ (ps_blockAct_mem_VV lam _ y.2) fun x hx => ?_` and prove the remaining obligations.

Establish `h1` using `hy ⟨x, hx⟩`. Rewrite `h1` using `[pairK_apply, pairP_apply]`. Rewrite using `[fockL_symm, (mul_eq_zero.mp h1).resolve_left hc, star_zero]`. Conclude with `ps_blockAct_injective _ hGt (by rw [h0, Submodule.coe_zero, map_zero])`.
-/
theorem pairingNondegenerate_holds : PairNondeg := by
  intro K _ _ _ ι _ n lam G hG
  have hGt : ∀ τ, IsUnit ((G τ)ᵀ).det := fun τ => by rw [Matrix.det_transpose]; exact hG τ
  have hc : gramTw lam G / extNorm K lam ≠ 0 := by
    obtain ⟨r, hr, he⟩ := extNormPos K ι n lam
    refine div_ne_zero ?_ ?_
    · unfold gramTw
      exact Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hG τ).ne_zero
    · rw [he]
      exact (map_ne_zero (algebraMap ℚ K)).mpr hr.ne'
  have e : (Formalism.GradedWeylDivisibility.blockAct K (n := n) fun τ => (G τ)ᵀ).comp (Formalism.GradedWeylDivisibility.blockAct K fun τ => ((G τ)ᵀ)⁻¹) =
      AlgHom.id K _ := by
    rw [blockAct_comp, ← blockAct_one]
    congr 1
    funext τ
    exact Matrix.nonsing_inv_mul _ (hGt τ)
  constructor
  · intro x hx
    apply Subtype.ext
    refine ps_fock_sep lam x.1 x.2 fun y hy => ?_
    have h1 := hx ⟨Formalism.GradedWeylDivisibility.blockAct K (fun τ => ((G τ)ᵀ)⁻¹) y, ps_blockAct_mem_VV lam _ hy⟩
    rw [pairK_apply, pairP_apply, ← AlgHom.comp_apply, e] at h1
    exact (mul_eq_zero.mp h1).resolve_left hc
  · intro y hy
    apply Subtype.ext
    have h0 : Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y.1 = 0 := by
      refine ps_fock_sep lam _ (ps_blockAct_mem_VV lam _ y.2) fun x hx => ?_
      have h1 := hy ⟨x, hx⟩
      rw [pairK_apply, pairP_apply] at h1
      rw [fockL_symm, (mul_eq_zero.mp h1).resolve_left hc, star_zero]
    exact ps_blockAct_injective _ hGt (by rw [h0, Submodule.coe_zero, map_zero])

end Formalism.L2.DIV
