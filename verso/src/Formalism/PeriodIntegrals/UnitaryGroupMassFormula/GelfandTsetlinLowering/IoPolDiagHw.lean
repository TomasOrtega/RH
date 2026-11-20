import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliShift
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.IoExistsOfCap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.BCRowGenMonomial

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

/- English proof (translation)
Introduce `i j hij`. Use `mu.anti hij` as an intermediate fact. Use `show (mu.w j - mu.detShift).toNat ≤ (mu.w i - mu.detShift).toNat`. Conclude with `Int.toNat_le_toNat (by linarith)`.
-/
theorem io_natW_anti {k : ℕ} (mu : DomWeight k) : Antitone mu.natW := by
  intro i j hij
  have := mu.anti hij
  show (mu.w j - mu.detShift).toNat ≤ (mu.w i - mu.detShift).toNat
  exact Int.toNat_le_toNat (by linarith)

/- English proof (translation)
Establish `hk : 0 < k` using `Fin.pos a`. Establish `ha` using `a.isLt`. Establish `hd : mu.detShift = mu.w ⟨k - 1, by omega⟩`. Unfold `DomWeight.detShift`. Rewrite using `[dif_pos hk]`.

Establish `hle : mu.w ⟨k - 1, by omega⟩ ≤ mu.w a` using `mu.anti (by`. Rewrite using `[Fin.le_iff_val_le_val]`. Use `show (a : ℕ) ≤ k - 1`. Use the proof step `omega)`. Establish `h0 : 0 ≤ mu.w a - mu.detShift` using `by omega`.

Use `show (((mu.w a - mu.detShift).toNat : ℕ) : ℂ) = _`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg h0]`.
-/
theorem io_natW_cast {k : ℕ} (mu : DomWeight k) (a : Fin k) :
    ((mu.natW a : ℕ) : ℂ) = ((mu.w a - mu.detShift : ℤ) : ℂ) := by
  have hk : 0 < k := Fin.pos a
  have ha := a.isLt
  have hd : mu.detShift = mu.w ⟨k - 1, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos hk]
  have hle : mu.w ⟨k - 1, by omega⟩ ≤ mu.w a := mu.anti (by
    rw [Fin.le_iff_val_le_val]
    show (a : ℕ) ≤ k - 1
    omega)
  have h0 : 0 ≤ mu.w a - mu.detShift := by omega
  show (((mu.w a - mu.detShift).toNat : ℕ) : ℂ) = _
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]

/- English proof (translation)
Establish `euler : ∀ (f : MvPolynomial (Fin k × Fin k) ℂ) (d : Fin k → ℕ), IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW k k) f d → ∑ s : Fin k, X (a, s) * pderiv (a, s) f = ((d a : ℕ) : ℂ) • f`. Introduce `f d hf`. Rewrite using `[f.as_sum]`. Simplify using `only [map_sum, Finset.mul_sum, MvPolynomial.X_mul_pderiv_monomial, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun m hm => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul, Nat.cast_smul_eq_nsmul]`. Use `congr 1`. Establish `hw'` using `congrFun (hf (mem_support_iff.mp hm)) a`. Rewrite using `[← hw']`.

Simplify using `[Finsupp.weight_apply, Finsupp.sum_fintype, Formalism.GradedWeylDivisibility.rowW, Pi.single_apply, Fintype.sum_prod_type]`. Use `symm`. Rewrite using `[Fintype.sum_eq_single a (fun x hx => by simp [Ne.symm hx])]`. Simplify using the standard rewrite rules. Establish `hH` using `Formalism.GradedWeylDivisibility.hwRowWeight ℂ k k (le_refl k) ν hν`.

Establish `hra : Formalism.GradedWeylDivisibility.rowNu (r` using `k) ν a = ν a := by`. Unfold `Formalism.GradedWeylDivisibility.rowNu`. Rewrite using `[dif_pos a.isLt]`. Rewrite using `[pol_apply, euler _ _ hH, hra]`.
-/
theorem io_pol_diag_hw {k : ℕ} (ν : Fin k → ℕ) (hν : Antitone ν) (a : Fin k) :
    pol ℂ a a (hw ℂ (le_refl k) ν) = ((ν a : ℕ) : ℂ) • hw ℂ (le_refl k) ν := by
  have euler : ∀ (f : MvPolynomial (Fin k × Fin k) ℂ) (d : Fin k → ℕ),
      IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW k k) f d →
      ∑ s : Fin k, X (a, s) * pderiv (a, s) f = ((d a : ℕ) : ℂ) • f := by
    intro f d hf
    rw [f.as_sum]
    simp only [map_sum, Finset.mul_sum, MvPolynomial.X_mul_pderiv_monomial, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [← Finset.sum_smul, Nat.cast_smul_eq_nsmul]
    congr 1
    have hw' := congrFun (hf (mem_support_iff.mp hm)) a
    rw [← hw']
    simp [Finsupp.weight_apply, Finsupp.sum_fintype, Formalism.GradedWeylDivisibility.rowW, Pi.single_apply,
      Fintype.sum_prod_type]
    symm
    rw [Fintype.sum_eq_single a (fun x hx => by simp [Ne.symm hx])]
    simp
  have hH := Formalism.GradedWeylDivisibility.hwRowWeight ℂ k k (le_refl k) ν hν
  have hra : Formalism.GradedWeylDivisibility.rowNu (r := k) ν a = ν a := by
    unfold Formalism.GradedWeylDivisibility.rowNu
    rw [dif_pos a.isLt]
  rw [pol_apply, euler _ _ hH, hra]

/- English proof (translation)
Establish `hgl` using `capE_glRel h lam`. Establish `hcent : ∀ a b, Formalism.REAL.qdet (capE h lam) u * capE h lam a b = capE h lam a b * Formalism.REAL.qdet (capE h lam) u` using `fun a b => Formalism.REAL.qDetCentral_of Formalism.REAL.quantumMinorRowSkew_holds Formalism.REAL.quantumMinorColSkew_holds _ n (capE h lam) hgl u a b`. Use `set Q := Formalism.REAL.qdet (capE h lam) u with hQ`. Use `set p : ℂ := ∏ k : Fin n, (u - (k : ℂ) + (mu.w k : ℂ)) with hp`. Establish `hφpol : ∀ a b, ∀ s ∈ nablaSq ℂ n mu, φ (pol ℂ a b s) = capE h lam a b (φ s) - (if a = b then (mu.detShift : ℂ) • φ s else 0)`.

Introduce `a b s hs`. Rewrite using `[capE_apply, eq_sub_iff_add_eq, eqv_pol h mu lam φ hφ a b s hs]`. Set `M : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ)` to `nablaSq ℂ n mu ⊓ LinearMap.ker ((Q - p • LinearMap.id) ∘ₗ φ)`. Establish `memM : ∀ s, s ∈ M ↔ s ∈ nablaSq ℂ n mu ∧ Q (φ s) = p • φ s`. Introduce `s`.

Simplify using `only [M, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Establish `hpolM : ∀ a b, ∀ s ∈ M, pol ℂ a b s ∈ M`. Introduce `a b s hs`. Rewrite `hs`, the goal using `[memM]`. Use `⟨pol_mem_dualWeyl ℂ _ a b s hs.1, ?_⟩` and prove the remaining obligations.

Establish `hc : Q (capE h lam a b (φ s)) = capE h lam a b (Q (φ s))`. Use `congrArg (fun T : Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) => T (φ s)) (hcent a b)` as an intermediate fact. Simplify `this` using `only [Module.End.mul_apply]`. Rewrite using `[hφpol a b s hs.1, map_sub, hc, hs.2, map_smul, smul_sub]`. Use `split_ifs`.

Rewrite using `[map_smul, hs.2, smul_comm]`. Rewrite using `[map_zero, smul_zero]`. Establish `hdivM : ∀ a b k, ∀ s ∈ M, rowDiv ℂ a b k s ∈ M`. Introduce `a b k`. Proceed by induction on `k with`.

Consider the case `zero => intro s hs`. Rewrite using `[rowDiv_zero]` and apply the resulting hypothesis. Consider the case `succ k ih`. Introduce `s hs`. Establish `hrec` using `rowDiv_succ ℂ a b k s`.

Establish `hk : ∀ (j : ℕ) (x : MvPolynomial (Fin n × Fin n) ℂ), x * (j : MvPolynomial (Fin n × Fin n) ℂ) = (j : ℂ) • x`. Introduce `j x`. Rewrite using `[MvPolynomial.smul_eq_C_mul, mul_comm x, map_natCast]`. Rewrite `hrec` using `[← Nat.cast_succ]`. Simplify using `only [hk] at hrec`.

Establish `hc0 : ((k + 1 : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)`. Establish `e1 : rowDiv ℂ a b (k + 1) s = ((k + 1 : ℕ) : ℂ)⁻¹ • (rowDiv ℂ a b k (pol ℂ a b s) - if a = b then (k : ℂ) • rowDiv ℂ a b k s else 0)`. Rewrite using `[← hrec, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Rewrite using `[e1]`. Use `Submodule.smul_mem _ _ (Submodule.sub_mem _ (ih _ (hpolM a b s hs)) ?_)` and prove the remaining obligations.

Use `split_ifs`. Conclude with `Submodule.smul_mem _ _ (ih s hs)`. Conclude with `M.zero_mem`. Establish `hext` using `io_extremal_mem h3 n mu`. Establish `hextM : extremal ℂ n mu ∈ M`.

Rewrite using `[memM]`. Use `⟨hext, ?_⟩` and prove the remaining obligations. Establish `hHW : Formalism.REAL.IsHW (capE h lam) (fun k => (mu.w k : ℂ)) (φ (extremal ℂ n mu))`. Prove the components needed by the constructor for the conclusion. Introduce `a`.

Establish `e` using `hφpol a a _ hext`. Rewrite `e` using `[if_pos rfl, eq_sub_iff_add_eq]`. Rewrite using `[← e]`. Use `show φ (pol ℂ a a (hw ℂ le_rfl mu.natW)) + _ = _`. Rewrite using `[io_pol_diag_hw _ (io_natW_anti mu), map_smul, io_natW_cast]`.

Express the relevant statement in the definitionally equal form `((mu.w a - mu.detShift : ℤ) : ℂ) • φ (extremal ℂ n mu) + (mu.detShift : ℂ) • φ (extremal ℂ n mu) = (mu.w a : ℂ) • φ (extremal ℂ n mu)`. Rewrite using `[← add_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Introduce `a b hab`. Establish `e` using `hφpol a b _ hext`. Rewrite `e` using `[if_neg (ne_of_lt hab), sub_zero]`. Rewrite using `[← e, pol_eq_rowDiv]`. Use `show φ (rowDiv ℂ a b 1 (hw ℂ le_rfl mu.natW)) = 0`.

Rewrite using `[Formalism.GradedWeylDivisibility.hwRaise ℂ n n le_rfl mu.natW a b 1 hab le_rfl, map_zero]`. Conclude with `Formalism.REAL.quantumDetHighestWeight_holds _ n (capE h lam) _ _ hgl hHW u`. Establish `hall : delSq ℂ n mu ≤ M` using `by show Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl mu.natW ≤ M`. Unfold `Formalism.GradedWeylDivisibility.weyl`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨w, rfl⟩`. Proceed by induction on `w with`. Consider the case `nil => exact hextM`. Consider the case `cons x w ih => exact hdivM x.1 x.2.1 x.2.2 _ ih`. Rewrite `hs` using `[(h3 n mu).1]`.

Conclude with `((memM s).mp (hall hs)).2`.
-/
theorem capScalar (h3 : PI.HwIrred) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) (u : ℂ) :
    Formalism.REAL.qdet (capE h lam) u (φ s) = (∏ k : Fin n, (u - (k : ℂ) + (mu.w k : ℂ))) • φ s := by
  have hgl := capE_glRel h lam
  have hcent : ∀ a b, Formalism.REAL.qdet (capE h lam) u * capE h lam a b =
      capE h lam a b * Formalism.REAL.qdet (capE h lam) u := fun a b =>
    Formalism.REAL.qDetCentral_of Formalism.REAL.quantumMinorRowSkew_holds Formalism.REAL.quantumMinorColSkew_holds _ n (capE h lam) hgl u a b
  set Q := Formalism.REAL.qdet (capE h lam) u with hQ
  set p : ℂ := ∏ k : Fin n, (u - (k : ℂ) + (mu.w k : ℂ)) with hp
  have hφpol : ∀ a b, ∀ s ∈ nablaSq ℂ n mu, φ (pol ℂ a b s) =
      capE h lam a b (φ s) - (if a = b then (mu.detShift : ℂ) • φ s else 0) := by
    intro a b s hs
    rw [capE_apply, eq_sub_iff_add_eq, eqv_pol h mu lam φ hφ a b s hs]
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) :=
    nablaSq ℂ n mu ⊓ LinearMap.ker ((Q - p • LinearMap.id) ∘ₗ φ)
  have memM : ∀ s, s ∈ M ↔ s ∈ nablaSq ℂ n mu ∧ Q (φ s) = p • φ s := by
    intro s
    simp only [M, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  have hpolM : ∀ a b, ∀ s ∈ M, pol ℂ a b s ∈ M := by
    intro a b s hs
    rw [memM] at hs ⊢
    refine ⟨pol_mem_dualWeyl ℂ _ a b s hs.1, ?_⟩
    have hc : Q (capE h lam a b (φ s)) = capE h lam a b (Q (φ s)) := by
      have := congrArg (fun T : Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) => T (φ s)) (hcent a b)
      simpa only [Module.End.mul_apply] using this
    rw [hφpol a b s hs.1, map_sub, hc, hs.2, map_smul, smul_sub]
    split_ifs
    · rw [map_smul, hs.2, smul_comm]
    · rw [map_zero, smul_zero]
  have hdivM : ∀ a b k, ∀ s ∈ M, rowDiv ℂ a b k s ∈ M := by
    intro a b k
    induction k with
    | zero => intro s hs; rwa [rowDiv_zero]
    | succ k ih =>
      intro s hs
      have hrec := rowDiv_succ ℂ a b k s
      have hk : ∀ (j : ℕ) (x : MvPolynomial (Fin n × Fin n) ℂ),
          x * (j : MvPolynomial (Fin n × Fin n) ℂ) = (j : ℂ) • x := by
        intro j x; rw [MvPolynomial.smul_eq_C_mul, mul_comm x, map_natCast]
      rw [← Nat.cast_succ] at hrec
      simp only [hk] at hrec
      have hc0 : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      have e1 : rowDiv ℂ a b (k + 1) s = ((k + 1 : ℕ) : ℂ)⁻¹ • (rowDiv ℂ a b k (pol ℂ a b s) -
          if a = b then (k : ℂ) • rowDiv ℂ a b k s else 0) := by
        rw [← hrec, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [e1]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ (ih _ (hpolM a b s hs)) ?_)
      split_ifs
      · exact Submodule.smul_mem _ _ (ih s hs)
      · exact M.zero_mem
  have hext := io_extremal_mem h3 n mu
  have hextM : extremal ℂ n mu ∈ M := by
    rw [memM]
    refine ⟨hext, ?_⟩
    have hHW : Formalism.REAL.IsHW (capE h lam) (fun k => (mu.w k : ℂ)) (φ (extremal ℂ n mu)) := by
      constructor
      · intro a
        have e := hφpol a a _ hext
        rw [if_pos rfl, eq_sub_iff_add_eq] at e
        rw [← e]
        show φ (pol ℂ a a (hw ℂ le_rfl mu.natW)) + _ = _
        rw [io_pol_diag_hw _ (io_natW_anti mu), map_smul, io_natW_cast]
        change ((mu.w a - mu.detShift : ℤ) : ℂ) • φ (extremal ℂ n mu) + (mu.detShift : ℂ) • φ (extremal ℂ n mu) =
          (mu.w a : ℂ) • φ (extremal ℂ n mu)
        rw [← add_smul]
        congr 1
        push_cast
        ring
      · intro a b hab
        have e := hφpol a b _ hext
        rw [if_neg (ne_of_lt hab), sub_zero] at e
        rw [← e, pol_eq_rowDiv]
        show φ (rowDiv ℂ a b 1 (hw ℂ le_rfl mu.natW)) = 0
        rw [Formalism.GradedWeylDivisibility.hwRaise ℂ n n le_rfl mu.natW a b 1 hab le_rfl, map_zero]
    exact Formalism.REAL.quantumDetHighestWeight_holds _ n (capE h lam) _ _ hgl hHW u
  have hall : delSq ℂ n mu ≤ M := by
    show Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl mu.natW ≤ M
    unfold Formalism.GradedWeylDivisibility.weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    induction w with
    | nil => exact hextM
    | cons x w ih => exact hdivM x.1 x.2.1 x.2.2 _ ih
  rw [(h3 n mu).1] at hs
  exact ((memM s).mp (hall hs)).2

end PI.WGL
