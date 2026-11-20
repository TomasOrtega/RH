import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RowActCoefPolyAndUnitaryDense

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

/- English proof (translation)
Rewrite using `[← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]`. Introduce `l hl`. Take `⟨P, hP⟩` from `exists_poly_rowAct_coef n k f l`. Establish `h0 : P = 0` using `eq_zero_of_vanish_unitaryGroup n P fun u hu => by`. Rewrite using `[← hP]`.

Conclude with `(Submodule.mem_dualAnnihilator l).1 hl _ (hM u hu f hf)`. Rewrite using `[hP, h0, map_zero]`.
-/
theorem rowAct_mem_of_unitary_stable {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M)
    (g : Matrix (Fin n) (Fin n) ℂ) (f : MvPolynomial (Fin n × Fin k) ℂ) (hf : f ∈ M) : rowAct ℂ g f ∈ M := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  obtain ⟨P, hP⟩ := exists_poly_rowAct_coef n k f l
  have h0 : P = 0 := eq_zero_of_vanish_unitaryGroup n P fun u hu => by
    rw [← hP]
    exact (Submodule.mem_dualAnnihilator l).1 hl _ (hM u hu f hf)
  rw [hP, h0, map_zero]

/- English proof (translation)
Introduce `a b j p hp`. Rewrite using `[← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]`. Introduce `l hl`. Use `set N := (rowGen ℂ a b p).natDegree + j + 1 with hN`. Establish `h1 : (rowGen ℂ a b p).natDegree < N` using `by omega`.

Establish `hk : j ∈ Finset.range N` using `Finset.mem_range.mpr (by omega)`. Use `set P : Polynomial ℂ := ∑ i ∈ Finset.range N, Polynomial.monomial i (l (rowDiv ℂ a b i p)) with hP`. Establish `hP0 : P = 0`. Apply `Polynomial.funext` to reduce the goal to its premises. Introduce `c`.

Simplify using `only [hP, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]`. Establish `e` using `(Submodule.mem_dualAnnihilator l).1 hl _ (hM (lfockq_mat a b c) p hp)`. Rewrite `e` using `[← lfockq_eval_rowGen, lfockq_eval_C _ N h1, map_sum]`. Rewrite using `[← e]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression. Use `congrArg (fun p => Polynomial.coeff p j) hP0` as an intermediate fact. Simplify using `only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', if_pos hk, Polynomial.coeff_zero] at this`. Conclude with `this`.
-/
theorem rowDivClosed_of_rowAct_stable {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : ∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ f ∈ M, rowAct ℂ g f ∈ M) : RowDivClosed M := by
  intro a b j p hp
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  set N := (rowGen ℂ a b p).natDegree + j + 1 with hN
  have h1 : (rowGen ℂ a b p).natDegree < N := by omega
  have hk : j ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  set P : Polynomial ℂ := ∑ i ∈ Finset.range N, Polynomial.monomial i (l (rowDiv ℂ a b i p)) with hP
  have hP0 : P = 0 := by
    apply Polynomial.funext
    intro c
    simp only [hP, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
    have e := (Submodule.mem_dualAnnihilator l).1 hl _ (hM (lfockq_mat a b c) p hp)
    rw [← lfockq_eval_rowGen, lfockq_eval_C _ N h1, map_sum] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
    rfl
  have := congrArg (fun p => Polynomial.coeff p j) hP0
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq',
    if_pos hk, Polynomial.coeff_zero] at this
  exact this

/- English proof (translation)
Introduce `e he`. Establish `hs : rowDiv ℂ a b j f = ∑ d ∈ f.support, (rowGen ℂ a b (monomial d (coeff d f))).coeff j`. Unfold `rowDiv`. Use `conv_lhs => rw [f.as_sum]`. Rewrite using `[map_sum, Polynomial.finsetSum_coeff]`.

Rewrite `he` using `[mem_support_iff, hs, coeff_sum]`. Take `⟨d, hd, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero he`. Establish `h1` using `lhwinShift_rowGen_monomial ℂ a b d (coeff d f) j hne`. Establish `h2` using `hf d hd`. Use linear arithmetic over natural numbers and integers.
-/
theorem height_rowDiv_le {n k : ℕ} (H : ℤ) (a b : Fin n) (j : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ)
    (hf : ∀ d ∈ f.support, Finsupp.weight (lhwinHt n k) d ≤ H) :
    ∀ d ∈ (rowDiv ℂ a b j f).support, Finsupp.weight (lhwinHt n k) d ≤ H + j * ((a.val : ℤ) - b.val) := by
  intro e he
  have hs : rowDiv ℂ a b j f = ∑ d ∈ f.support, (rowGen ℂ a b (monomial d (coeff d f))).coeff j := by
    unfold rowDiv
    conv_lhs => rw [f.as_sum]
    rw [map_sum, Polynomial.finsetSum_coeff]
  rw [mem_support_iff, hs, coeff_sum] at he
  obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have h1 := lhwinShift_rowGen_monomial ℂ a b d (coeff d f) j hne
  have h2 := hf d hd
  omega

/- English proof (translation)
Establish `hex : ∃ N : ℕ, ∃ v ∈ M, v ≠ 0 ∧ ∀ d ∈ v.support, Finsupp.weight (lhwinHt n k) d ≤ (N : ℤ)`. Take `⟨f, hfM, hf0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Use `⟨f.support.sup fun d => (Finsupp.weight (lhwinHt n k) d).toNat, f, hfM, hf0, fun d hd => ?_⟩` and prove the remaining obligations. Use `Finset.le_sup (f := fun d => (Finsupp.weight (lhwinHt n k) d).toNat) hd` as an intermediate fact. Establish `h2 : ((Finsupp.weight (lhwinHt n k) d).toNat : ℤ) ≤ _` using `Int.ofNat_le.2 this`.

Conclude with `(Int.self_le_toNat _).trans h2`. Take `⟨v, hvM, hv0, hvH⟩` from `Nat.find_spec hex`. Use `⟨v, hvM, hv0, fun a b hab j hj => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne'`. Establish `hH` using `height_rowDiv_le _ a b j v hvH`.

Take `⟨d, hd⟩` from `ne_zero_iff.mp hne'`. Establish `hnn` using `(lhwin_weight_nonneg d).trans (hH d (mem_support_iff.2 hd))`. Establish `hab' : (a.val : ℤ) < b.val` using `by exact_mod_cast (Fin.lt_def.mp hab)`. Establish `hk' : (1 : ℤ) ≤ j` using `by exact_mod_cast hj`. Establish `hlt : ((Nat.find hex : ℕ) : ℤ) + j * ((a.val : ℤ) - b.val) < (Nat.find hex : ℕ)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hmin` using `Nat.find_min hex (m := (((Nat.find hex : ℕ) : ℤ) + j * ((a.val : ℤ) - b.val)).toNat) (by omega)`. Apply `hmin` to reduce the goal to its premises. Use `⟨_, hM a b j v hvM, hne', ?_⟩` and prove the remaining obligations. Rewrite using `[Int.toNat_of_nonneg hnn]`.

Conclude with `hH`.
-/
theorem exists_killed_of_rowDivClosed {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : RowDivClosed M) (hne : M ≠ ⊥) :
    ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin n, a < b → ∀ j : ℕ, 1 ≤ j → rowDiv ℂ a b j v = 0 := by
  classical
  have hex : ∃ N : ℕ, ∃ v ∈ M, v ≠ 0 ∧ ∀ d ∈ v.support, Finsupp.weight (lhwinHt n k) d ≤ (N : ℤ) := by
    obtain ⟨f, hfM, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨f.support.sup fun d => (Finsupp.weight (lhwinHt n k) d).toNat, f, hfM, hf0, fun d hd => ?_⟩
    have := Finset.le_sup (f := fun d => (Finsupp.weight (lhwinHt n k) d).toNat) hd
    have h2 : ((Finsupp.weight (lhwinHt n k) d).toNat : ℤ) ≤ _ := Int.ofNat_le.2 this
    exact (Int.self_le_toNat _).trans h2
  obtain ⟨v, hvM, hv0, hvH⟩ := Nat.find_spec hex
  refine ⟨v, hvM, hv0, fun a b hab j hj => ?_⟩
  by_contra hne'
  have hH := height_rowDiv_le _ a b j v hvH
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hne'
  have hnn := (lhwin_weight_nonneg d).trans (hH d (mem_support_iff.2 hd))
  have hab' : (a.val : ℤ) < b.val := by exact_mod_cast (Fin.lt_def.mp hab)
  have hk' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have hlt : ((Nat.find hex : ℕ) : ℤ) + j * ((a.val : ℤ) - b.val) < (Nat.find hex : ℕ) := by
    nlinarith
  have hmin := Nat.find_min hex (m := (((Nat.find hex : ℕ) : ℤ) + j * ((a.val : ℤ) - b.val)).toNat)
    (by omega)
  apply hmin
  refine ⟨_, hM a b j v hvM, hne', ?_⟩
  rw [Int.toNat_of_nonneg hnn]
  exact hH

/- English proof (translation)
Take `⟨v, hvM, hv0, hkill⟩` from `exists_killed_of_rowDivClosed M hM hne`. Take `⟨c, hc⟩` from `hwLine ℂ r n hn ν hν v (hle hvM) hkill`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Conclude with `hv0 (by simpa using hc)`.

Establish `e : hw ℂ hn ν = c⁻¹ • v`. Rewrite using `[hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Establish `hhw : hw ℂ hn ν ∈ M` using `e ▸ M.smul_mem _ hvM`. Use `(Formalism.BranchingDeterminantCap.bs_dual_le_weyl hn ν hν).trans ?_` and prove the remaining obligations. Unfold `weyl`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, rfl⟩`. Proceed by induction on `w with`. Consider the case `nil => exact hhw`. Consider the case `cons x w ih => exact hM _ _ _ _ ih`.
-/
theorem dualWeyl_le_of_rowDivClosed {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hle : M ≤ dualWeyl ℂ r n ν) (hM : RowDivClosed M)
    (hne : M ≠ ⊥) : dualWeyl ℂ r n ν ≤ M := by
  obtain ⟨v, hvM, hv0, hkill⟩ := exists_killed_of_rowDivClosed M hM hne
  obtain ⟨c, hc⟩ := hwLine ℂ r n hn ν hν v (hle hvM) hkill
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hv0 (by simpa using hc)
  have e : hw ℂ hn ν = c⁻¹ • v := by
    rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hhw : hw ℂ hn ν ∈ M := e ▸ M.smul_mem _ hvM
  refine (Formalism.BranchingDeterminantCap.bs_dual_le_weyl hn ν hν).trans ?_
  unfold weyl
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact hhw
  | cons x w ih => exact hM _ _ _ _ ih

/- English proof (translation)
Establish `hnt : Nontrivial (Subrepresentation (smallRep (unitaryIncl n) mu))` using `⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩`. Use `⟨fun S => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hS : S.toSubmodule = ⊥`. Conclude with `Or.inl (Subrepresentation.ext hS)`. Use `Or.inr (Subrepresentation.ext ?_)` and prove the remaining obligations.

Set `M : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ)` to `S.toSubmodule.map (nablaSq ℂ n mu).subtype`. Establish `hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M`. Introduce and unpack `u hu _ ⟨f, hf, rfl⟩`. Set `t : Matrix.unitaryGroup (Fin n) ℂ` to `Matrix.UnitaryGroup.transpose ⟨u, hu⟩`. Establish `h1 : (smallRep (unitaryIncl n) mu t f : MvPolynomial (Fin n × Fin n) ℂ) ∈ M` using `⟨_, S.apply_mem_toSubmodule t hf, rfl⟩`.

Establish `h2 : (smallRep (unitaryIncl n) mu t f : MvPolynomial (Fin n × Fin n) ℂ) = detPow ℂ n (unitaryIncl n t) mu.detShift • rowAct ℂ u f` using `rfl`. Rewrite `h1` using `[h2]`. Conclude with `(M.smul_mem_iff (Units.ne_zero _)).1 h1`. Establish `hcl` using `rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)`. Establish `hne : M ≠ ⊥` using `fun e => hS (Submodule.map_injective_of_injective (nablaSq ℂ n mu).injective_subtype (e.trans (Submodule.map_bot _).symm))`.

Establish `hle` using `dualWeyl_le_of_rowDivClosed le_rfl mu.natW (factNatW n mu).1 M (Submodule.map_subtype_le (nablaSq ℂ n mu) _) hcl hne`. Use `eq_top_iff.2 fun f _ => ?_` and prove the remaining obligations. Take `⟨g, hg, e⟩` from `hle f.2`. Rewrite using `[← Subtype.ext e]` and apply the resulting hypothesis.
-/
theorem isIrreducible_smallRep_unitary (n : ℕ) (mu : DomWeight n) :
    (smallRep (unitaryIncl n) mu).IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation (smallRep (unitaryIncl n) mu)) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.ext hS)
  refine Or.inr (Subrepresentation.ext ?_)
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) := S.toSubmodule.map (nablaSq ℂ n mu).subtype
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M := by
    rintro u hu _ ⟨f, hf, rfl⟩
    let t : Matrix.unitaryGroup (Fin n) ℂ := Matrix.UnitaryGroup.transpose ⟨u, hu⟩
    have h1 : (smallRep (unitaryIncl n) mu t f : MvPolynomial (Fin n × Fin n) ℂ) ∈ M :=
      ⟨_, S.apply_mem_toSubmodule t hf, rfl⟩
    have h2 : (smallRep (unitaryIncl n) mu t f : MvPolynomial (Fin n × Fin n) ℂ) =
        detPow ℂ n (unitaryIncl n t) mu.detShift • rowAct ℂ u f := rfl
    rw [h2] at h1
    exact (M.smul_mem_iff (Units.ne_zero _)).1 h1
  have hcl := rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)
  have hne : M ≠ ⊥ := fun e => hS (Submodule.map_injective_of_injective (nablaSq ℂ n mu).injective_subtype
    (e.trans (Submodule.map_bot _).symm))
  have hle := dualWeyl_le_of_rowDivClosed le_rfl mu.natW (factNatW n mu).1 M
    (Submodule.map_subtype_le (nablaSq ℂ n mu) _) hcl hne
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨g, hg, e⟩ := hle f.2
  rwa [← Subtype.ext e]

end GlobalTheory.Branching
