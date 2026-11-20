import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Statement
import Formalism.GradedWeylDivisibility.FinalD
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SqCharA

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS.S7

def sq_ssEquiv (k : ℕ) (ν : Fin k → ℕ) :
    ↥(Formalism.GradedWeylDivisibility.ssIdx k k ν) ≃ sq_SSZ k (fun t => (ν t : ℤ)) :=
  Equiv.subtypeEquiv (Finsupp.equivFunOnFinite.trans (Equiv.curry (Fin k) (Fin k) ℕ)) (by
    intro m
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun l j hlj a => ?_, fun t => ?_⟩
      · have := h1 l j hlj a
        rw [zero_add] at this
        exact this
      · exact congrArg Nat.cast (h2 t)
    · rintro ⟨h1, h2⟩
      refine ⟨fun l j hlj a => ?_, fun t => ?_⟩
      · rw [zero_add]
        exact h1 l j hlj a
      · exact Nat.cast_injective (R := ℤ) (h2 t))

/- English proof (translation)
Simplify using `[wsum, Finset.sum_add_distrib]`.
-/
theorem sq_wsum_add {n : ℕ} (lam : Fin n → ℤ) (c : ℤ) :
    wsum (fun i => lam i + c) = wsum lam + n * c := by
  simp [wsum, Finset.sum_add_distrib]

def sq_shiftEmb {n : ℕ} (c : ℤ) : (Fin n → ℤ) ↪ (Fin n → ℤ) :=
  ⟨fun mu i => mu i + c, fun x y h => funext fun i => by simpa using congrFun h i⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sq_shiftEmb_apply {n : ℕ} (c : ℤ) (mu : Fin n → ℤ) : sq_shiftEmb c mu = fun i => mu i + c := rfl

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro lam c t _`. Simplify using `[gtChar]`. Consider the case `succ n ih`.

Introduce `lam c t ht`. Establish `himg : interl (fun i => lam i + c) = (interl lam).map (sq_shiftEmb c)`. Use extensionality with `mu`. Simplify using `only [mem_map, sq_mem_interl, sq_shiftEmb_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨fun i => mu i - c, fun i => ⟨by linarith [(h i).1], by linarith [(h i).2]⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨a, ha, rfl⟩ i`.

Conclude with `⟨by linarith [(ha i).1], by linarith [(ha i).2]⟩`. Rewrite using `[gtChar, gtChar, himg, sum_map, mul_sum]`. Use `sum_congr rfl fun mu _ => ?_` and prove the remaining obligations. Rewrite using `[sq_shiftEmb_apply, ih mu c _ (fun i => ht _), sq_wsum_add, sq_wsum_add, Fin.prod_univ_castSucc, mul_zpow]`. Establish `e : wsum lam + ((n + 1 : ℕ) : ℤ) * c - (wsum mu + (n : ℤ) * c) = (wsum lam - wsum mu) + c` using `by push_cast; ring`.

Rewrite using `[e, zpow_add₀ (ht _)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sq_gt_shift {K : Type*} [Field K] : ∀ (n : ℕ) (lam : Fin n → ℤ) (c : ℤ) (t : Fin n → K),
    (∀ i, t i ≠ 0) → gtChar n (fun i => lam i + c) t = (∏ i, t i) ^ c * gtChar n lam t := by
  intro n
  induction n with
  | zero => intro lam c t _; simp [gtChar]
  | succ n ih =>
    intro lam c t ht
    have himg : interl (fun i => lam i + c) = (interl lam).map (sq_shiftEmb c) := by
      ext mu
      simp only [mem_map, sq_mem_interl, sq_shiftEmb_apply]
      constructor
      · intro h
        refine ⟨fun i => mu i - c, fun i => ⟨by linarith [(h i).1], by linarith [(h i).2]⟩, ?_⟩
        funext i
        ring
      · rintro ⟨a, ha, rfl⟩ i
        exact ⟨by linarith [(ha i).1], by linarith [(ha i).2]⟩
    rw [gtChar, gtChar, himg, sum_map, mul_sum]
    refine sum_congr rfl fun mu _ => ?_
    rw [sq_shiftEmb_apply, ih mu c _ (fun i => ht _), sq_wsum_add, sq_wsum_add, Fin.prod_univ_castSucc, mul_zpow]
    have e : wsum lam + ((n + 1 : ℕ) : ℤ) * c - (wsum mu + (n : ℤ) * c) = (wsum lam - wsum mu) + c := by
      push_cast; ring
    rw [e, zpow_add₀ (ht _)]
    ring

/- English proof (translation)
Establish `: Fintype (sq_SSZ N (fun i => (ν i : ℤ)))` using `@Fintype.ofFinite _ (sq_SSZ_finite N _)`. Use `(Fintype.sum_equiv (sq_ssEquiv N ν) _ (fun g => sq_mono t g.1) (fun m => rfl)).trans ?_` and prove the remaining obligations. Conclude with `sq_gt_sum N _ (fun s => Int.natCast_nonneg _) t`.
-/
theorem sq_ss_sum {K : Type*} [Field K] (N : ℕ) (ν : Fin N → ℕ) [Fintype ↥(Formalism.GradedWeylDivisibility.ssIdx N N ν)]
    (t : Fin N → K) :
    ∑ m : ↥(Formalism.GradedWeylDivisibility.ssIdx N N ν), ∏ a, t a ^ Formalism.GradedWeylDivisibility.rowWt m.1 a = gtChar N (fun i => (ν i : ℤ)) t := by
  have : Fintype (sq_SSZ N (fun i => (ν i : ℤ))) := @Fintype.ofFinite _ (sq_SSZ_finite N _)
  refine (Fintype.sum_equiv (sq_ssEquiv N ν) _ (fun g => sq_mono t g.1) (fun m => rfl)).trans ?_
  exact sq_gt_sum N _ (fun s => Int.natCast_nonneg _) t

/- English proof (translation)
Introduce `N lam g t hg`. Establish `hdet : (g : Matrix (Fin N) (Fin N) ℂ).det ≠ 0`. Rewrite using `[← Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `Units.ne_zero _`. Establish `ht : ∀ a, t a ≠ 0`.

Introduce `a h`. Rewrite `hdet` using `[hg, Matrix.det_diagonal]`. Conclude with `hdet (Finset.prod_eq_zero (mem_univ a) h)`. Take `⟨b, ⟨hli, hspan, hhom⟩, -⟩` from `Formalism.GradedWeylDivisibility.sSBasis ℂ N N lam.natW`. Establish `: Fintype ↥(Formalism.GradedWeylDivisibility.ssIdx N N lam.natW)` using `(Formalism.GradedWeylDivisibility.sSIdxFinite N N lam.natW).fintype`.

Set `B : Module.Basis ↥(Formalism.GradedWeylDivisibility.ssIdx N N lam.natW) ℂ (Formalism.BasicNotions.nablaSq ℂ N lam)` to `(Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)`. Establish `hB : ∀ m, (B m : MvPolynomial (Fin N × Fin N) ℂ) = b m`. Introduce `m`. Simplify using `only [B, Module.Basis.map_apply, Module.Basis.span_apply]`. Both sides reduce to the same expression.

Set `c : ℂ` to `Formalism.BasicNotions.detPow ℂ N g lam.detShift`. Set `w : ↥(Formalism.GradedWeylDivisibility.ssIdx N N lam.natW) → ℂ` to `fun m => ∏ a, t a ^ Formalism.GradedWeylDivisibility.rowWt m.1 a`. Set `f : Formalism.BasicNotions.nablaSq ℂ N lam →ₗ[ℂ] Formalism.BasicNotions.nablaSq ℂ N lam` to `B.constr ℂ (fun m => (c * w m) • B m)`. Establish `hact : ∀ x : MvPolynomial (Fin N × Fin N) ℂ, Formalism.BasicNotions.sqAct ℂ N lam g x = c • Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal t) x`. Introduce `x`.

Simplify using `only [Formalism.BasicNotions.sqAct, hg, Matrix.diagonal_transpose, c]`. Use `⟨f, ?_, ?_⟩` and prove the remaining obligations. Establish `hL : (Formalism.BasicNotions.nablaSq ℂ N lam).subtype ∘ₗ f = (c • (Formalism.GradedWeylDivisibility.rowAct ℂ (n` using `N) (Matrix.diagonal t)).toLinearMap) ∘ₗ (Formalism.BasicNotions.nablaSq ℂ N lam).subtype := by`. Use `B.ext fun m => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply, f, Module.Basis.constr_basis, LinearMap.smul_apply, AlgHom.toLinearMap_apply, hB]`.

Rewrite using `[Submodule.coe_smul, hB, Formalism.GradedWeylDivisibility.rowActDiagWeight ℂ N N t (Formalism.GradedWeylDivisibility.rowWt m.1) (b m) (hhom m), smul_smul]`. Introduce `x`. Rewrite using `[hact]`. Conclude with `LinearMap.congr_fun hL x`. Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ B, Matrix.trace]`.

Establish `hdiag : ∀ m, Matrix.diag (LinearMap.toMatrix B B f) m = c * w m`. Introduce `m`. Rewrite using `[Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.constr_basis, map_smul, Module.Basis.repr_self, Finsupp.smul_single, Finsupp.single_eq_same, smul_eq_mul, mul_one]`. Simplify using `only [hdiag, ← Finset.mul_sum]`. Rewrite using `[sq_ss_sum N lam.natW t]`.

Establish `hw : lam.w = fun i => ((lam.natW i : ℕ) : ℤ) + lam.detShift`. Use function extensionality and compare the values at `i`. Establish `hle : lam.detShift ≤ lam.w i`. Establish `hN : 0 < N` using `lt_of_le_of_lt (Nat.zero_le _) i.isLt`. Unfold `Formalism.BasicNotions.DomWeight.detShift`.

Rewrite using `[dif_pos hN]`. Conclude with `lam.anti (by rw [Fin.le_iff_val_le_val]; dsimp only; omega)`. Simplify using `only [Formalism.BasicNotions.DomWeight.natW]`. Rewrite using `[Int.toNat_of_nonneg (by omega)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hw, sq_gt_shift N _ _ t ht]`. Use `congr 1`. Simplify using `only [c, Formalism.BasicNotions.detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, hg, Matrix.det_diagonal]`.
-/
theorem sqChar : SqCharStatement := by
  intro N lam g t hg
  classical
  have hdet : (g : Matrix (Fin N) (Fin N) ℂ).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have ht : ∀ a, t a ≠ 0 := by
    intro a h
    rw [hg, Matrix.det_diagonal] at hdet
    exact hdet (Finset.prod_eq_zero (mem_univ a) h)
  obtain ⟨b, ⟨hli, hspan, hhom⟩, -⟩ := Formalism.GradedWeylDivisibility.sSBasis ℂ N N lam.natW
  have : Fintype ↥(Formalism.GradedWeylDivisibility.ssIdx N N lam.natW) := (Formalism.GradedWeylDivisibility.sSIdxFinite N N lam.natW).fintype
  let B : Module.Basis ↥(Formalism.GradedWeylDivisibility.ssIdx N N lam.natW) ℂ (Formalism.BasicNotions.nablaSq ℂ N lam) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  have hB : ∀ m, (B m : MvPolynomial (Fin N × Fin N) ℂ) = b m := by
    intro m
    simp only [B, Module.Basis.map_apply, Module.Basis.span_apply]
    rfl
  let c : ℂ := Formalism.BasicNotions.detPow ℂ N g lam.detShift
  let w : ↥(Formalism.GradedWeylDivisibility.ssIdx N N lam.natW) → ℂ := fun m => ∏ a, t a ^ Formalism.GradedWeylDivisibility.rowWt m.1 a
  let f : Formalism.BasicNotions.nablaSq ℂ N lam →ₗ[ℂ] Formalism.BasicNotions.nablaSq ℂ N lam := B.constr ℂ (fun m => (c * w m) • B m)
  have hact : ∀ x : MvPolynomial (Fin N × Fin N) ℂ,
      Formalism.BasicNotions.sqAct ℂ N lam g x = c • Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal t) x := by
    intro x
    simp only [Formalism.BasicNotions.sqAct, hg, Matrix.diagonal_transpose, c]
  refine ⟨f, ?_, ?_⟩
  · have hL : (Formalism.BasicNotions.nablaSq ℂ N lam).subtype ∘ₗ f =
        (c • (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal t)).toLinearMap) ∘ₗ
          (Formalism.BasicNotions.nablaSq ℂ N lam).subtype := by
      refine B.ext fun m => ?_
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, f, Module.Basis.constr_basis,
        LinearMap.smul_apply, AlgHom.toLinearMap_apply, hB]
      rw [Submodule.coe_smul, hB, Formalism.GradedWeylDivisibility.rowActDiagWeight ℂ N N t (Formalism.GradedWeylDivisibility.rowWt m.1) (b m) (hhom m),
        smul_smul]
    intro x
    rw [hact]
    exact LinearMap.congr_fun hL x
  · rw [LinearMap.trace_eq_matrix_trace ℂ B, Matrix.trace]
    have hdiag : ∀ m, Matrix.diag (LinearMap.toMatrix B B f) m = c * w m := by
      intro m
      rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.constr_basis, map_smul,
        Module.Basis.repr_self, Finsupp.smul_single, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    simp only [hdiag, ← Finset.mul_sum]
    rw [sq_ss_sum N lam.natW t]
    have hw : lam.w = fun i => ((lam.natW i : ℕ) : ℤ) + lam.detShift := by
      funext i
      have hle : lam.detShift ≤ lam.w i := by
        have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.isLt
        unfold Formalism.BasicNotions.DomWeight.detShift
        rw [dif_pos hN]
        exact lam.anti (by rw [Fin.le_iff_val_le_val]; dsimp only; omega)
      simp only [Formalism.BasicNotions.DomWeight.natW]
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    rw [hw, sq_gt_shift N _ _ t ht]
    congr 1
    simp only [c, Formalism.BasicNotions.detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply,
      hg, Matrix.det_diagonal]

end ReciprocityTheory.ChartRestriction.TR.Weyl
