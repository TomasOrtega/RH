import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacExGoodOfN
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GNonneg

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.PF

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries

/- English proof (translation)
Establish `hK : Fintype.card {m : Fin (2 * r + k + 1) // Formalism.QuantumDeterminants.GBasic.epsK k r m = true} = r + k`. Rewrite using `[Fintype.card_subtype]`. Establish `hf : (Finset.univ.filter fun i : Fin (2 * r + k + 1) => Formalism.QuantumDeterminants.GBasic.epsK k r i = true) = Finset.univ.filter fun i : Fin (2 * r + k + 1) => (i : ℕ) < r + k`. Use extensionality with `i`. Simplify using `[Formalism.QuantumDeterminants.GBasic.epsK]`.

Rewrite using `[hf, Fin.card_filter_val_lt]`. Use linear arithmetic over natural numbers and integers. Establish `hKf : Fintype.card {m : Fin (2 * r + k + 1) // Formalism.QuantumDeterminants.GBasic.epsK k r m = false} = r + 1`. Establish `h` using `Fintype.card_subtype_compl (fun m : Fin (2 * r + k + 1) => Formalism.QuantumDeterminants.GBasic.epsK k r m = true)`. Rewrite `h` using `[hK, Fintype.card_fin]`.

Rewrite using `[← Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp) : {m : Fin (2 * r + k + 1) // ¬ Formalism.QuantumDeterminants.GBasic.epsK k r m = true} ≃ {m : Fin (2 * r + k + 1) // Formalism.QuantumDeterminants.GBasic.epsK k r m = false}), h]`. Use linear arithmetic over natural numbers and integers. Establish `hE : Fintype.card {m : Fin (2 * r + k + 1) // ε m = false} = r + 1`. Rewrite using `[Fintype.card_subtype]`. Conclude with `hs`.

Establish `h1 : Fintype.card {m : Fin (2 * r + k + 1) // Formalism.QuantumDeterminants.GBasic.epsK k r m = false} = Fintype.card {m : Fin (2 * r + k + 1) // ε m = false}` using `by rw [hKf, hE]`. Establish `h2 : Fintype.card {m : Fin (2 * r + k + 1) // ¬ Formalism.QuantumDeterminants.GBasic.epsK k r m = false} = Fintype.card {m : Fin (2 * r + k + 1) // ¬ ε m = false}`. Rewrite using `[Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]`. Set `e` to `Fintype.equivOfCardEq h1`. Set `f` to `Fintype.equivOfCardEq h2`.

Use `⟨Equiv.subtypeCongr e f, fun m => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hm : Formalism.QuantumDeterminants.GBasic.epsK k r m = false`. Establish `: Equiv.subtypeCongr e f m = e ⟨m, hm⟩`. Simplify using `only [Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos (p := fun x => Formalism.QuantumDeterminants.GBasic.epsK k r x = false) hm, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]`. Rewrite using `[this, hm]`.

Conclude with `(e ⟨m, hm⟩).2`. Establish `: Equiv.subtypeCongr e f m = f ⟨m, hm⟩`. Simplify using `only [Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg (p := fun x => Formalism.QuantumDeterminants.GBasic.epsK k r x = false) hm, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]`. Rewrite using `[this]`. Establish `h3` using `(f ⟨m, hm⟩).2`.

Simplify using `only [Bool.not_eq_false] at hm h3`. Rewrite using `[hm, h3]`.
-/
theorem exists_perm {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool)
    (hs : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) :
    ∃ σ : Equiv.Perm (Fin (2 * r + k + 1)), ∀ m, ε (σ m) = Formalism.QuantumDeterminants.GBasic.epsK k r m := by
  have hK : Fintype.card {m : Fin (2 * r + k + 1) // Formalism.QuantumDeterminants.GBasic.epsK k r m = true} = r + k := by
    rw [Fintype.card_subtype]
    have hf : (Finset.univ.filter fun i : Fin (2 * r + k + 1) => Formalism.QuantumDeterminants.GBasic.epsK k r i = true) =
        Finset.univ.filter fun i : Fin (2 * r + k + 1) => (i : ℕ) < r + k := by
      ext i; simp [Formalism.QuantumDeterminants.GBasic.epsK]
    rw [hf, Fin.card_filter_val_lt]
    omega
  have hKf : Fintype.card {m : Fin (2 * r + k + 1) // Formalism.QuantumDeterminants.GBasic.epsK k r m = false} = r + 1 := by
    have h := Fintype.card_subtype_compl (fun m : Fin (2 * r + k + 1) => Formalism.QuantumDeterminants.GBasic.epsK k r m = true)
    rw [hK, Fintype.card_fin] at h
    rw [← Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp) :
      {m : Fin (2 * r + k + 1) // ¬ Formalism.QuantumDeterminants.GBasic.epsK k r m = true} ≃
        {m : Fin (2 * r + k + 1) // Formalism.QuantumDeterminants.GBasic.epsK k r m = false}), h]
    omega
  have hE : Fintype.card {m : Fin (2 * r + k + 1) // ε m = false} = r + 1 := by
    rw [Fintype.card_subtype]; exact hs
  have h1 : Fintype.card {m : Fin (2 * r + k + 1) // Formalism.QuantumDeterminants.GBasic.epsK k r m = false} =
      Fintype.card {m : Fin (2 * r + k + 1) // ε m = false} := by rw [hKf, hE]
  have h2 : Fintype.card {m : Fin (2 * r + k + 1) // ¬ Formalism.QuantumDeterminants.GBasic.epsK k r m = false} =
      Fintype.card {m : Fin (2 * r + k + 1) // ¬ ε m = false} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  let e := Fintype.equivOfCardEq h1
  let f := Fintype.equivOfCardEq h2
  refine ⟨Equiv.subtypeCongr e f, fun m => ?_⟩
  by_cases hm : Formalism.QuantumDeterminants.GBasic.epsK k r m = false
  · have : Equiv.subtypeCongr e f m = e ⟨m, hm⟩ := by
      simp only [Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos (p := fun x => Formalism.QuantumDeterminants.GBasic.epsK k r x = false) hm, Equiv.sumCongr_apply,
        Sum.map_inl, Equiv.sumCompl_apply_inl]
    rw [this, hm]; exact (e ⟨m, hm⟩).2
  · have : Equiv.subtypeCongr e f m = f ⟨m, hm⟩ := by
      simp only [Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg (p := fun x => Formalism.QuantumDeterminants.GBasic.epsK k r x = false) hm, Equiv.sumCongr_apply,
        Sum.map_inr, Equiv.sumCompl_apply_inr]
    rw [this]
    have h3 := (f ⟨m, hm⟩).2
    simp only [Bool.not_eq_false] at hm h3
    rw [hm, h3]

/- English proof (translation)
Take `⟨σ, hσ⟩` from `exists_perm ε hs`. Use `⟨Matrix.of fun i j => Formalism.QuantumDeterminants.GBasic.Pk k r (σ.symm i) j, ?_⟩` and prove the remaining obligations. Rewrite using `[← Formalism.QuantumDeterminants.GBasic.PJP k r]`. Use extensionality with `a b`. Rewrite using `[mul_apply, mul_apply]`.

Simplify using `only [Formalism.REAL.Jm, mul_diagonal, conjTranspose_apply, of_apply]`. Use `(Fintype.sum_equiv σ _ _ (fun m => ?_)).symm` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply, hσ m]`.
-/
theorem exists_Q {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool)
    (hs : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) :
    ∃ Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r := by
  obtain ⟨σ, hσ⟩ := exists_perm ε hs
  refine ⟨Matrix.of fun i j => Formalism.QuantumDeterminants.GBasic.Pk k r (σ.symm i) j, ?_⟩
  rw [← Formalism.QuantumDeterminants.GBasic.PJP k r]
  ext a b
  rw [mul_apply, mul_apply]
  simp only [Formalism.REAL.Jm, mul_diagonal, conjTranspose_apply, of_apply]
  refine (Fintype.sum_equiv σ _ _ (fun m => ?_)).symm
  simp only [Equiv.symm_apply_apply, hσ m]

/- English proof (translation)
Rewrite using `[hJ_mulVec, hP]`.
-/
theorem hJ_P {n : ℕ} (ε : Fin n → Bool) (P H : Matrix (Fin n) (Fin n) ℂ) (hP : Pᴴ * Formalism.REAL.Jm ε * P = H)
    (x y : Fin n → ℂ) : hJ ε (P *ᵥ x) (P *ᵥ y) = star x ⬝ᵥ (H *ᵥ y) := by
  rw [hJ_mulVec, hP]

/- English proof (translation)
Simplify using `[Formalism.QuantumDeterminants.bvec, dotProduct, mulVec, Pi.single_apply]`.
-/
theorem dot_bvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    star (Formalism.QuantumDeterminants.bvec i) ⬝ᵥ (M *ᵥ Formalism.QuantumDeterminants.bvec j) = M i j := by
  simp [Formalism.QuantumDeterminants.bvec, dotProduct, mulVec, Pi.single_apply]

/- English proof (translation)
Simplify using `[Formalism.QuantumDeterminants.bvec, dotProduct, Pi.single_apply]`.
-/
theorem dot_bvec' {n : ℕ} (v : Fin n → ℂ) (i : Fin n) : star (Formalism.QuantumDeterminants.bvec i) ⬝ᵥ v = v i := by
  simp [Formalism.QuantumDeterminants.bvec, dotProduct, Pi.single_apply]

section Hpk
variable (k r : ℕ)

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Unfold `Formalism.QuantumDeterminants.Hpk Formalism.QuantumDeterminants.eI`. Simplify using `only [Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem Hpk_ee (a b : Fin r) : Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.eI k r b) = 0 := by
  have ha := a.isLt; have hb := b.isLt
  unfold Formalism.QuantumDeterminants.Hpk Formalism.QuantumDeterminants.eI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Unfold `Formalism.QuantumDeterminants.Hpk Formalism.QuantumDeterminants.esI`. Simplify using `only [Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem Hpk_ss (a b : Fin r) : Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.esI k r a) (Formalism.QuantumDeterminants.esI k r b) = 0 := by
  have ha := a.isLt; have hb := b.isLt
  unfold Formalism.QuantumDeterminants.Hpk Formalism.QuantumDeterminants.esI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Unfold `Formalism.QuantumDeterminants.Hpk Formalism.QuantumDeterminants.esI Formalism.QuantumDeterminants.eI`. Simplify using `only [Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem Hpk_es (a b : Fin r) :
    Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.esI k r b) = if a = b then 1 else 0 := by
  have ha := a.isLt; have hb := b.isLt
  unfold Formalism.QuantumDeterminants.Hpk Formalism.QuantumDeterminants.esI Formalism.QuantumDeterminants.eI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Establish `ha` using `a.isLt`. Rewrite using `[Formalism.QuantumDeterminants.gn_Hpk_mulVec, dif_pos (Or.inr (by simp only [Formalism.QuantumDeterminants.esI]; omega))]`. Use `congr 1`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [Formalism.QuantumDeterminants.esI, Formalism.QuantumDeterminants.eI]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem Hpk_mulVec_es (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) (Formalism.QuantumDeterminants.esI k r a) = v (Formalism.QuantumDeterminants.eI k r a) := by
  have ha := a.isLt
  rw [Formalism.QuantumDeterminants.gn_Hpk_mulVec, dif_pos (Or.inr (by simp only [Formalism.QuantumDeterminants.esI]; omega))]
  congr 1
  apply Fin.ext
  simp only [Formalism.QuantumDeterminants.esI, Formalism.QuantumDeterminants.eI]
  omega

/- English proof (translation)
Establish `ha` using `a.isLt`. Rewrite using `[Formalism.QuantumDeterminants.gn_Hpk_mulVec, dif_pos (Or.inl (by simp only [Formalism.QuantumDeterminants.eI]; omega))]`. Use `congr 1`.
-/
theorem Hpk_mulVec_e (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) (Formalism.QuantumDeterminants.eI k r a) = v (Formalism.QuantumDeterminants.esI k r a) := by
  have ha := a.isLt
  rw [Formalism.QuantumDeterminants.gn_Hpk_mulVec, dif_pos (Or.inl (by simp only [Formalism.QuantumDeterminants.eI]; omega))]
  congr 1

end Hpk

def hypG (r : ℕ) (i j : Fin (r + r)) : ℂ :=
  Fin.append (fun a => Fin.append (fun b => if a = b then (2 : ℂ) else 0) (fun _ => 0) j)
    (fun a => Fin.append (fun _ => 0) (fun b => if a = b then (-2 : ℂ) else 0) j) i

/- English proof (translation)
Unfold `hypG`. Use `revert hij`. Apply the tactic sequence `refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>`. Apply the tactic sequence `refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;> intro hij <;>`. Apply the tactic sequence `simp only [Fin.append_left, Fin.append_right] <;>`.

Apply the tactic sequence `(try split_ifs with h) <;> first | rfl | exact (hij (by subst h; rfl)).elim`.
-/
theorem hypG_ne (r : ℕ) (i j : Fin (r + r)) (hij : i ≠ j) : hypG r i j = 0 := by
  unfold hypG
  revert hij
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;> intro hij <;>
    simp only [Fin.append_left, Fin.append_right] <;>
    (try split_ifs with h) <;> first | rfl | exact (hij (by subst h; rfl)).elim

/- English proof (translation)
Unfold `hypG`. Apply the tactic sequence `refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> simp only [Fin.append_left, Fin.append_right] <;> simp`.
-/
theorem hypG_self (r : ℕ) (i : Fin (r + r)) : hypG r i i ≠ 0 := by
  unfold hypG
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> simp only [Fin.append_left, Fin.append_right] <;> simp

/- English proof (translation)
Establish `hyx : ∀ a b, hJ ε (y a) (x b) = if a = b then 1 else 0`. Introduce `a b`. Rewrite using `[hJ_conj, hxy]`. Distinguish the cases in `h : b = a`. Rewrite using `[if_pos h, if_pos h.symm]`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg (Ne.symm h)]`. Simplify using the standard rewrite rules. Introduce `i j`. Unfold `hypG`.

Apply the tactic sequence `refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>`. Apply the tactic sequence `refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>`. Apply the tactic sequence `simp only [Fin.append_left, Fin.append_right, hJ_add_left, hJ_add_right, hJ_sub_left, hJ_sub_right, hxx, hxy, hyx, hyy] <;>`. Apply the tactic sequence `(try split_ifs) <;> ring`.
-/
theorem hyp_gram {n r : ℕ} (ε : Fin n → Bool) (x y : Fin r → Fin n → ℂ) (hxx : ∀ a b, hJ ε (x a) (x b) = 0)
    (hxy : ∀ a b, hJ ε (x a) (y b) = if a = b then 1 else 0) (hyy : ∀ a b, hJ ε (y a) (y b) = 0) :
    ∀ i j : Fin (r + r), hJ ε (Fin.append (fun a => x a + y a) (fun a => x a - y a) i)
        (Fin.append (fun a => x a + y a) (fun a => x a - y a) j) = hypG r i j := by
  have hyx : ∀ a b, hJ ε (y a) (x b) = if a = b then 1 else 0 := by
    intro a b
    rw [hJ_conj, hxy]
    by_cases h : b = a
    · rw [if_pos h, if_pos h.symm]; simp
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  intro i j
  unfold hypG
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
    simp only [Fin.append_left, Fin.append_right, hJ_add_left, hJ_add_right, hJ_sub_left, hJ_sub_right,
      hxx, hxy, hyx, hyy] <;>
    (try split_ifs) <;> ring

/- English proof (translation)
Introduce `r k ε e z z' T T' hF hG`. Take `⟨f, hef, hff, hfz⟩` from `hG`. Take `⟨Q, hQ⟩` from `exists_Q (k := k) ε hF.sig`. Establish `hqq : ∀ i j, hJ ε (Q *ᵥ Formalism.QuantumDeterminants.bvec i) (Q *ᵥ Formalism.QuantumDeterminants.bvec j) = Formalism.QuantumDeterminants.Hpk k r i j` using `fun i j => by rw [hJ_P ε Q _ hQ, dot_bvec]`. Set `x : Fin r → Fin (2 * r + k + 1) → ℂ` to `fun a => Q *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)`.

Set `y : Fin r → Fin (2 * r + k + 1) → ℂ` to `fun a => Q *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)`. Establish `G1` using `hyp_gram ε x y (fun a b => by simp only [x]; rw [hqq, Hpk_ee]) (fun a b => by simp only [x, y]; rw [hqq, Hpk_es]) (fun a b => by simp only [y]; rw [hqq, Hpk_ss])`. Establish `G2` using `hyp_gram ε e f hF.ee hef hff`. Take `⟨g, hg, hgd⟩` from `witt_orth ε (Fin.append (fun a => x a + y a) (fun a => x a - y a)) (Fin.append (fun a => e a + f a) (fun a => e a - f a)) (fun i j => by rw [G1, G2]) (fun i j hij => by rw [G1]; exact hypG_ne r i j hij) (fun i => by rw [G1]; exact hypG_self r i)`. Establish `hge : ∀ a, g *ᵥ x a = e a ∧ g *ᵥ y a = f a`.

Introduce `a`. Establish `h1` using `hgd (Fin.castAdd r a)`. Establish `h2` using `hgd (Fin.natAdd r a)`. Rewrite `h1` using `[Fin.append_left, Fin.append_left, mulVec_add]`. Rewrite `h2` using `[Fin.append_right, Fin.append_right, mulVec_sub]`.

Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `t`. Establish `c1` using `congrFun h1 t`. Establish `c2` using `congrFun h2 t`. Simplify using `only [Pi.add_apply, Pi.sub_apply] at c1 c2`.

Take the linear combination `(c1 + c2) / 2`. Use function extensionality and compare the values at `t`. Establish `c1` using `congrFun h1 t`. Establish `c2` using `congrFun h2 t`. Simplify using `only [Pi.add_apply, Pi.sub_apply] at c1 c2`.

Take the linear combination `(c1 - c2) / 2`. Establish `hgJ : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε` using `inUJ_of_isIsom ε hg`. Establish `hPJP : (g * Q)ᴴ * Formalism.REAL.Jm ε * (g * Q) = Formalism.QuantumDeterminants.Hpk k r`. Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hgJ, hQ]`. Establish `hdet : IsUnit (g * Q).det`. Apply `isUnit_det_of_left_inverse (B := Formalism.QuantumDeterminants.Hpk k r * (g * Q)ᴴ * Formalism.REAL.Jm ε)` to reduce the goal to its premises. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (g * Q)ᴴ, hPJP, Formalism.QuantumDeterminants.GBasic.Hpk_sq]`.

Establish `hPe : ∀ a, (g * Q) *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a` using `fun a => by`. Rewrite using `[← mulVec_mulVec]`. Conclude with `(hge a).1`. Establish `hPf : ∀ a, (g * Q) *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a) = f a` using `fun a => by`. Rewrite using `[← mulVec_mulVec]`.

Conclude with `(hge a).2`. Establish `pull : ∀ w : Fin (2 * r + k + 1) → ℂ, (∀ a, hJ ε (e a) w = 0) → (∀ a, hJ ε (f a) w = 0) → Formalism.QuantumDeterminants.inWb k r ((g * Q)⁻¹ *ᵥ w) ∧ (g * Q) *ᵥ ((g * Q)⁻¹ *ᵥ w) = w ∧ Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) ((g * Q)⁻¹ *ᵥ w) ((g * …`. Introduce `w hew hfw`. Establish `hPP : (g * Q) *ᵥ ((g * Q)⁻¹ *ᵥ w) = w`. Rewrite using `[mulVec_mulVec, mul_nonsing_inv (g * Q) hdet, one_mulVec]`.

Establish `key : ∀ i, (Formalism.QuantumDeterminants.Hpk k r *ᵥ ((g * Q)⁻¹ *ᵥ w)) i = hJ ε ((g * Q) *ᵥ Formalism.QuantumDeterminants.bvec i) w` using `fun i => by rw [← dot_bvec' (Formalism.QuantumDeterminants.Hpk k r *ᵥ ((g * Q)⁻¹ *ᵥ w)) i, ← hJ_P ε (g * Q) _ hPJP, hPP]`. Use `⟨fun i hi => ?_, hPP, ?_⟩` and prove the remaining obligations. Establish `hi'` using `i.isLt`. Break down `hi with hlo | hhi` into its components or cases. Establish `hi2 : i = Formalism.QuantumDeterminants.eI k r ⟨i.val, hlo⟩` using `Fin.ext rfl`.

Rewrite using `[hi2, ← Hpk_mulVec_es k r ((g * Q)⁻¹ *ᵥ w), key, hPf, hfw]`. Establish `hi2 : i = Formalism.QuantumDeterminants.esI k r ⟨2 * r + k - i.val, by omega⟩`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [Formalism.QuantumDeterminants.esI]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hi2, ← Hpk_mulVec_e k r ((g * Q)⁻¹ *ᵥ w), key, hPe, hew]`. Unfold `Formalism.QuantumDeterminants.herm`. Rewrite using `[← hJ_P ε (g * Q) _ hPJP, hPP]`. Take `⟨hz1, hz2, hz3⟩` from `pull z hF.ez (fun a => (hfz a).1)`. Take `⟨hz1', hz2', hz3'⟩` from `pull z' hF.ez' (fun a => (hfz a).2)`.

Use `⟨g * Q, hPJP, hdet, hPe, (g * Q)⁻¹ *ᵥ z, (g * Q)⁻¹ *ᵥ z', hz1, hz1', hz2, hz2', ?_, ?_⟩` and prove the remaining obligations. Unfold `Formalism.QuantumDeterminants.Tz`. Rewrite using `[hz3, hF.zz]`. Simplify using the standard rewrite rules. Unfold `Formalism.QuantumDeterminants.Tz`.

Rewrite using `[hz3', hF.zz']`. Simplify using the standard rewrite rules.
-/
theorem pFrame_holds : PFrame := by
  intro r k ε e z z' T T' hF hG
  obtain ⟨f, hef, hff, hfz⟩ := hG
  obtain ⟨Q, hQ⟩ := exists_Q (k := k) ε hF.sig
  have hqq : ∀ i j, hJ ε (Q *ᵥ Formalism.QuantumDeterminants.bvec i) (Q *ᵥ Formalism.QuantumDeterminants.bvec j) = Formalism.QuantumDeterminants.Hpk k r i j :=
    fun i j => by rw [hJ_P ε Q _ hQ, dot_bvec]
  let x : Fin r → Fin (2 * r + k + 1) → ℂ := fun a => Q *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)
  let y : Fin r → Fin (2 * r + k + 1) → ℂ := fun a => Q *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)
  have G1 := hyp_gram ε x y (fun a b => by simp only [x]; rw [hqq, Hpk_ee])
    (fun a b => by simp only [x, y]; rw [hqq, Hpk_es]) (fun a b => by simp only [y]; rw [hqq, Hpk_ss])
  have G2 := hyp_gram ε e f hF.ee hef hff
  obtain ⟨g, hg, hgd⟩ := witt_orth ε (Fin.append (fun a => x a + y a) (fun a => x a - y a))
    (Fin.append (fun a => e a + f a) (fun a => e a - f a)) (fun i j => by rw [G1, G2])
    (fun i j hij => by rw [G1]; exact hypG_ne r i j hij) (fun i => by rw [G1]; exact hypG_self r i)
  have hge : ∀ a, g *ᵥ x a = e a ∧ g *ᵥ y a = f a := by
    intro a
    have h1 := hgd (Fin.castAdd r a)
    have h2 := hgd (Fin.natAdd r a)
    rw [Fin.append_left, Fin.append_left, mulVec_add] at h1
    rw [Fin.append_right, Fin.append_right, mulVec_sub] at h2
    constructor
    · funext t
      have c1 := congrFun h1 t
      have c2 := congrFun h2 t
      simp only [Pi.add_apply, Pi.sub_apply] at c1 c2
      linear_combination (c1 + c2) / 2
    · funext t
      have c1 := congrFun h1 t
      have c2 := congrFun h2 t
      simp only [Pi.add_apply, Pi.sub_apply] at c1 c2
      linear_combination (c1 - c2) / 2
  have hgJ : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := inUJ_of_isIsom ε hg
  have hPJP : (g * Q)ᴴ * Formalism.REAL.Jm ε * (g * Q) = Formalism.QuantumDeterminants.Hpk k r := by
    rw [conjTranspose_mul]
    calc Qᴴ * gᴴ * Formalism.REAL.Jm ε * (g * Q) = Qᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * Q := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hgJ, hQ]
  have hdet : IsUnit (g * Q).det := by
    apply isUnit_det_of_left_inverse (B := Formalism.QuantumDeterminants.Hpk k r * (g * Q)ᴴ * Formalism.REAL.Jm ε)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (g * Q)ᴴ, hPJP, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  have hPe : ∀ a, (g * Q) *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a := fun a => by
    rw [← mulVec_mulVec]; exact (hge a).1
  have hPf : ∀ a, (g * Q) *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a) = f a := fun a => by
    rw [← mulVec_mulVec]; exact (hge a).2

  have pull : ∀ w : Fin (2 * r + k + 1) → ℂ, (∀ a, hJ ε (e a) w = 0) → (∀ a, hJ ε (f a) w = 0) →
      Formalism.QuantumDeterminants.inWb k r ((g * Q)⁻¹ *ᵥ w) ∧ (g * Q) *ᵥ ((g * Q)⁻¹ *ᵥ w) = w ∧
        Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) ((g * Q)⁻¹ *ᵥ w) ((g * Q)⁻¹ *ᵥ w) = hJ ε w w := by
    intro w hew hfw
    have hPP : (g * Q) *ᵥ ((g * Q)⁻¹ *ᵥ w) = w := by
      rw [mulVec_mulVec, mul_nonsing_inv (g * Q) hdet, one_mulVec]
    have key : ∀ i, (Formalism.QuantumDeterminants.Hpk k r *ᵥ ((g * Q)⁻¹ *ᵥ w)) i = hJ ε ((g * Q) *ᵥ Formalism.QuantumDeterminants.bvec i) w :=
      fun i => by rw [← dot_bvec' (Formalism.QuantumDeterminants.Hpk k r *ᵥ ((g * Q)⁻¹ *ᵥ w)) i, ← hJ_P ε (g * Q) _ hPJP, hPP]
    refine ⟨fun i hi => ?_, hPP, ?_⟩
    · have hi' := i.isLt
      rcases hi with hlo | hhi
      · have hi2 : i = Formalism.QuantumDeterminants.eI k r ⟨i.val, hlo⟩ := Fin.ext rfl
        rw [hi2, ← Hpk_mulVec_es k r ((g * Q)⁻¹ *ᵥ w), key, hPf, hfw]
      · have hi2 : i = Formalism.QuantumDeterminants.esI k r ⟨2 * r + k - i.val, by omega⟩ := by
          apply Fin.ext; simp only [Formalism.QuantumDeterminants.esI]; omega
        rw [hi2, ← Hpk_mulVec_e k r ((g * Q)⁻¹ *ᵥ w), key, hPe, hew]
    · unfold Formalism.QuantumDeterminants.herm
      rw [← hJ_P ε (g * Q) _ hPJP, hPP]
  obtain ⟨hz1, hz2, hz3⟩ := pull z hF.ez (fun a => (hfz a).1)
  obtain ⟨hz1', hz2', hz3'⟩ := pull z' hF.ez' (fun a => (hfz a).2)
  refine ⟨g * Q, hPJP, hdet, hPe, (g * Q)⁻¹ *ᵥ z, (g * Q)⁻¹ *ᵥ z', hz1, hz1', hz2, hz2', ?_, ?_⟩
  · unfold Formalism.QuantumDeterminants.Tz; rw [hz3, hF.zz]; simp
  · unfold Formalism.QuantumDeterminants.Tz; rw [hz3', hF.zz']; simp

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.PF

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

/- English proof (translation)
The claim follows from `PF.pFrame_holds`.
-/
theorem pFrame_holds : PFrame := PF.pFrame_holds

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
