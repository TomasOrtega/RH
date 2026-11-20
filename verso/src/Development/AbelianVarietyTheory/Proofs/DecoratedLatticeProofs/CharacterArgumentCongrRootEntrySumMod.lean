import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FlagChi

open Formalism.L2.SG.Pf.unitaryCongruence

/- English proof (translation)
Take `rfl : n = ρ + (k + (ρ + 1))` from `by omega`. Unfold `rootSum`. Rewrite using `[Fin.sum_univ_add, Fin.sum_univ_add, ← add_assoc]`. Establish `h3 : ∀ x y z : A, z = 0 → x = y → x + z = y`. Introduce `x y z hz hx`.

Rewrite using `[hz, hx, add_zero]`. Use `h3 _ _ _ (Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun j _ => ?_) ?_` and prove the remaining obligations. Simplify using `only [Fin.val_natAdd]`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `ha` using `a.2`. Apply the tactic sequence `rw [Finset.sum_eq_single (⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by split_ifs <;> omega⟩ : Fin (ρ + (k + (ρ + 1))))]`. Rewrite using `[if_pos]`. Both sides reduce to the same expression.

Apply the tactic sequence `simp only [Fin.val_castAdd] split_ifs <;> omega`. Introduce `j _ hj`. Establish `hj' : j.1 ≠ if a.1 + 1 < ρ then a.1 + 1 else ρ + k` using `fun h => hj (Fin.ext h)`. Simplify using `only [Fin.val_castAdd]`. Apply the tactic sequence `rw [if_neg (by split_ifs at hj' <;> omega), if_neg (by omega)]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hi` using `i.2`. Distinguish the cases in `h : i.1 + 1 < k`.

Rewrite using `[dif_pos h, Finset.sum_eq_single (⟨ρ + (i.1 + 1), by omega⟩ : Fin (ρ + (k + (ρ + 1))))]`. Rewrite using `[if_neg, if_pos]`. Both sides reduce to the same expression. Simplify using `only [Fin.val_natAdd, Fin.val_castAdd]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [Fin.val_natAdd, Fin.val_castAdd]`. Use linear arithmetic over natural numbers and integers. Introduce `j _ hj`. Establish `hj' : j.1 ≠ ρ + (i.1 + 1)` using `fun h => hj (Fin.ext h)`. Simplify using `only [Fin.val_natAdd, Fin.val_castAdd]`.

Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[dif_neg h]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Fin.val_natAdd, Fin.val_castAdd]`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`.
-/
theorem rootSum_eq {A : Type} [CommRing A] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (ε : A) (m : Matrix (Fin n) (Fin n) A) :
    rootSum ρ k ε m =
      (∑ a : Fin ρ, m ⟨a.1, by omega⟩ ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by split_ifs <;> omega⟩) +
      ∑ i : Fin k, if h : i.1 + 1 < k then ε * m ⟨ρ + i.1, by omega⟩ ⟨ρ + (i.1 + 1), by omega⟩ else 0 := by
  obtain rfl : n = ρ + (k + (ρ + 1)) := by omega
  unfold rootSum
  rw [Fin.sum_univ_add, Fin.sum_univ_add, ← add_assoc]
  have h3 : ∀ x y z : A, z = 0 → x = y → x + z = y := by
    intro x y z hz hx; rw [hz, hx, add_zero]
  refine h3 _ _ _ (Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun j _ => ?_) ?_
  · simp only [Fin.val_natAdd]
    rw [if_neg (by omega), if_neg (by omega)]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have ha := a.2
    rw [Finset.sum_eq_single (⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by split_ifs <;> omega⟩ : Fin (ρ + (k + (ρ + 1))))]
    · rw [if_pos]
      · rfl
      · simp only [Fin.val_castAdd]
        split_ifs <;> omega
    · intro j _ hj
      have hj' : j.1 ≠ if a.1 + 1 < ρ then a.1 + 1 else ρ + k := fun h => hj (Fin.ext h)
      simp only [Fin.val_castAdd]
      rw [if_neg (by split_ifs at hj' <;> omega), if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.2
    by_cases h : i.1 + 1 < k
    · rw [dif_pos h, Finset.sum_eq_single (⟨ρ + (i.1 + 1), by omega⟩ : Fin (ρ + (k + (ρ + 1))))]
      · rw [if_neg, if_pos]
        · rfl
        · simp only [Fin.val_natAdd, Fin.val_castAdd]
          omega
        · simp only [Fin.val_natAdd, Fin.val_castAdd]
          omega
      · intro j _ hj
        have hj' : j.1 ≠ ρ + (i.1 + 1) := fun h => hj (Fin.ext h)
        simp only [Fin.val_natAdd, Fin.val_castAdd]
        rw [if_neg (by omega), if_neg (by omega)]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg h]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [Fin.val_natAdd, Fin.val_castAdd]
      rw [if_neg (by omega), if_neg (by omega)]

/- English proof (translation)
Use `show Submodule.span _ _ = Submodule.span _ _`. Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`.

Conclude with `⟨⟨z, hz⟩, rfl⟩`. Introduce and unpack `⟨z, rfl⟩`. Conclude with `⟨z.1, z.2, rfl⟩`.
-/
theorem hatL_eq_Lf (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.1, z.2, rfl⟩

def colOf (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (j : Fin I.n) : VA I :=
  fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j

/- English proof (translation)
Take `⟨y, hy⟩` from `hx`. Establish `hconj : β⁻¹ * frGL β y * β = intGL I.F I.E I.n y`. Simplify using `only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Use `group`. Rewrite `hconj` using `[hy]`.

Unfold `matIn`. Rewrite using `[hconj]`. Conclude with `((y : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) i j).2`.
-/
theorem matIn_int (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} {x : I.Gf}
    (hx : (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β) (i j : Fin I.n) :
    matIn I β x i j ∈ IntAf I.F I.E := by
  obtain ⟨y, hy⟩ := hx
  have hconj : β⁻¹ * frGL β y * β = intGL I.F I.E I.n y := by
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hy] at hconj
  unfold matIn
  rw [hconj]
  exact ((y : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) i j).2

/- English proof (translation)
Unfold `matIn`. Rewrite using `[← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Use `group`.
-/
theorem mul_matIn (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (x : I.Gf) :
    (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * matIn I β x =
      I.fmat x * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) := by
  unfold matIn
  rw [← Units.val_mul, ← Units.val_mul]
  congr 1
  group

/- English proof (translation)
Rewrite `hv`, the goal using `[← hatL_eq_Lf]`. Use `(hβ _).2 fun i => ?_` and prove the remaining obligations. Establish `h` using `(hβ v).1 hv`. Establish `e : ((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *ᵥ (I.fmat x *ᵥ v) = matIn I β x *ᵥ (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E …`. Unfold `matIn`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]`. Use `congr 2`. Use `group`. Rewrite using `[e, Matrix.mulVec, dotProduct]`. Conclude with `Subring.sum_mem _ fun l _ => Subring.mul_mem _ (matIn_int I hx i l) (h l)`.
-/
theorem mulVec_mem_Lf (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hβ : IsFrame β I.L) {x : I.Gf}
    (hx : (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β) {v : VA I} (hv : v ∈ I.Lf) : I.fmat x *ᵥ v ∈ I.Lf := by
  rw [← hatL_eq_Lf] at hv ⊢
  refine (hβ _).2 fun i => ?_
  have h := (hβ v).1 hv
  have e : ((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *ᵥ
      (I.fmat x *ᵥ v) = matIn I β x *ᵥ
      (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *ᵥ v) := by
    unfold matIn
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  rw [e, Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (matIn_int I hx i l) (h l)

/- English proof (translation)
Rewrite using `[← hatL_eq_Lf]`. Use `(hβ _).2 fun i => ?_` and prove the remaining obligations. Use `show (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))) i j ∈ _`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]`. Use `split_ifs`.

Conclude with `Subring.one_mem _`. Conclude with `Subring.zero_mem _`.
-/
theorem col_mem_Lf (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hβ : IsFrame β I.L) (j : Fin I.n) :
    colOf I β j ∈ I.Lf := by
  rw [← hatL_eq_Lf]
  refine (hβ _).2 fun i => ?_
  show (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *
      (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))) i j ∈ _
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

/- English proof (translation)
The claim follows from `Submodule.span_le.2 (by rintro _ ⟨y, hy, rfl⟩ exact I.Lf.smul_mem (⟨(g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), natCast_mem _ g⟩ : IntAf I.F I.E) hy)`.
-/
theorem mL_le_Lf (I : AutInst) (g : ℕ) : mL I g ≤ I.Lf :=
  Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact I.Lf.smul_mem (⟨(g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), natCast_mem _ g⟩ : IntAf I.F I.E) hy)

/- English proof (translation)
Establish `: mL I g ≤ (mL I g).comap (mvO I M)` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `mL_mv I hM g le_rfl y hy)`. Conclude with `this hv`.
-/
theorem mulVec_mem_mL (I : AutInst) (g : ℕ) {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)}
    (hM : ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf) {v : VA I} (hv : v ∈ mL I g) : M *ᵥ v ∈ mL I g := by
  have : mL I g ≤ (mL I g).comap (mvO I M) := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact mL_mv I hM g le_rfl y hy)
  exact this hv

/- English proof (translation)
Establish `e : I.fmat x *ᵥ colOf I β q = ∑ l, matIn I β x l q • colOf I β l`. Use function extensionality and compare the values at `i`. Use `congrFun (congrFun (mul_matIn I β x) i) q` as an intermediate fact. Rewrite using `[Finset.sum_apply]`. Use `Eq.trans this.symm ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun l _ => mul_comm _ _`. Rewrite using `[e, ← hL_apply, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[hL_apply, hA_smul_right]`.

Both sides reduce to the same expression.
-/
theorem hA_col (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (x : I.Gf) (p q : Fin I.n) :
    hA I (colOf I β p) (I.fmat x *ᵥ colOf I β q) = ∑ l, matIn I β x l q * gramIn I β p l := by
  have e : I.fmat x *ᵥ colOf I β q = ∑ l, matIn I β x l q • colOf I β l := by
    funext i
    have := congrFun (congrFun (mul_matIn I β x) i) q
    rw [Finset.sum_apply]
    refine Eq.trans this.symm ?_
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [e, ← hL_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hL_apply, hA_smul_right]
  rfl

/- English proof (translation)
Establish `hM : ∀ y ∈ I.Lf, I.fmat x *ᵥ y ∈ I.Lf` using `fun y hy => mulVec_mem_Lf I hβ.1 hx hy`. Establish `hp' : colOf I β p - b p.1 ∈ mL I g` using `hβ.2 p`. Establish `hq' : colOf I β q - b q.1 ∈ mL I g` using `hβ.2 q`. Establish `hbp : b p.1 ∈ I.Lf`. Use `sub_mem (col_mem_Lf I hβ.1 p) (mL_le_Lf I g hp')` as an intermediate fact.

Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Establish `h1 : ZMod' I g (hA I (b p.1) (I.fmat x *ᵥ (colOf I β q - b q.1)))` using `mL_Qs I g hbp (mulVec_mem_mL I g hM hq')`. Establish `h2 : ZMod' I g (hA I (colOf I β p - b p.1) (I.fmat x *ᵥ colOf I β q))`. Rewrite using `[hA_symm]`. Conclude with `Z_sig I g (mL_Qs I g (hM _ (col_mem_Lf I hβ.1 q)) hp')`.

Establish `h3 : ZMod' I g (∑ l, matIn I β x l q * (gramIn I β p l - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k p l))` using `Z_sum I g _ _ fun l _ => Z_smul I g (matIn_int I hx l q) (hG p l)`. Establish `e1 : ∑ l, matIn I β x l q * flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k p l = matIn I β x t q`. Rewrite using `[Finset.sum_eq_single t]`. Unfold `flagGram`. Rewrite using `[if_pos ht, if_neg hp, mul_one]`.

Introduce `l _ hl`. Unfold `flagGram`. Rewrite using `[if_neg (fun h => hl (Fin.ext (h.trans ht.symm))), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Simplify using `only [mul_sub] at h3`. Rewrite `h3` using `[Finset.sum_sub_distrib, e1, ← hA_col]`. Establish `e2 : hA I (colOf I β p) (I.fmat x *ᵥ colOf I β q) = hA I (colOf I β p - b p.1) (I.fmat x *ᵥ colOf I β q) + hA I (b p.1) (I.fmat x *ᵥ colOf I β q)`. Rewrite using `[← hA_add_left, sub_add_cancel]`. Rewrite `h1` using `[Matrix.mulVec_sub, hA_sub_right]`.

Rewrite `h3` using `[e2]`. Use `Z_sub I g (Z_sub I g h3 h2) h1 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_zmod (I : AutInst) (g ρ k : ℕ) (b : ℕ → VA I) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))
    (hβ : IsLiftFrame I g b β)
    (hG : ∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) (x : I.Gf)
    (hx : (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β) (p q t : Fin I.n) (hp : p.1 ≠ ρ + k)
    (ht : t.1 = dualIdx ρ k p.1) : ZMod' I g (hA I (b p.1) (I.fmat x *ᵥ b q.1) - matIn I β x t q) := by
  have hM : ∀ y ∈ I.Lf, I.fmat x *ᵥ y ∈ I.Lf := fun y hy => mulVec_mem_Lf I hβ.1 hx hy
  have hp' : colOf I β p - b p.1 ∈ mL I g := hβ.2 p
  have hq' : colOf I β q - b q.1 ∈ mL I g := hβ.2 q
  have hbp : b p.1 ∈ I.Lf := by
    have := sub_mem (col_mem_Lf I hβ.1 p) (mL_le_Lf I g hp')
    rwa [sub_sub_cancel] at this
  have h1 : ZMod' I g (hA I (b p.1) (I.fmat x *ᵥ (colOf I β q - b q.1))) :=
    mL_Qs I g hbp (mulVec_mem_mL I g hM hq')
  have h2 : ZMod' I g (hA I (colOf I β p - b p.1) (I.fmat x *ᵥ colOf I β q)) := by
    rw [hA_symm]
    exact Z_sig I g (mL_Qs I g (hM _ (col_mem_Lf I hβ.1 q)) hp')
  have h3 : ZMod' I g (∑ l, matIn I β x l q * (gramIn I β p l - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k p l)) :=
    Z_sum I g _ _ fun l _ => Z_smul I g (matIn_int I hx l q) (hG p l)
  have e1 : ∑ l, matIn I β x l q * flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k p l = matIn I β x t q := by
    rw [Finset.sum_eq_single t]
    · unfold flagGram
      rw [if_pos ht, if_neg hp, mul_one]
    · intro l _ hl
      unfold flagGram
      rw [if_neg (fun h => hl (Fin.ext (h.trans ht.symm))), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [mul_sub] at h3
  rw [Finset.sum_sub_distrib, e1, ← hA_col] at h3
  have e2 : hA I (colOf I β p) (I.fmat x *ᵥ colOf I β q) =
      hA I (colOf I β p - b p.1) (I.fmat x *ᵥ colOf I β q) + hA I (b p.1) (I.fmat x *ᵥ colOf I β q) := by
    rw [← hA_add_left, sub_add_cancel]
  rw [Matrix.mulVec_sub, hA_sub_right] at h1
  rw [e2] at h3
  convert Z_sub I g (Z_sub I g h3 h2) h1 using 1
  ring

/- English proof (translation)
Introduce `I g ρ k e0 f0 z0 bw bwd ew hF hn β hβ hG x hx`. Take `⟨-, -, -, -, ⟨hid, hor, hint, -⟩, ⟨hw, hwd⟩, -, -⟩` from `hF`. Rewrite using `[rootSum_eq hn]`. Unfold `chiArg`. Rewrite using `[add_sub_add_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]`.

Use `Z_add I g (Z_sum I g _ _ fun a _ => ?_) (Z_sum I g _ _ fun i _ => ?_)` and prove the remaining obligations. Establish `ha` using `a.2`. Apply the tactic sequence `have key := pair_zmod I g ρ k _ β hβ hG x hx ⟨2 * ρ + k - a.1, by omega⟩ ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by split_ifs <;> omega⟩ ⟨a.1, by omega⟩ (by show 2 * ρ + k - a.1 ≠ _; omega) (by show a.1 = dualIdx ρ k (2 * ρ + k - a.1); unfold dualIdx; split_ifs <;> omega)`. Establish `e1 : flagVec e0 f0 z0 bw bwd (2 * ρ + k - a.1) = f0 a`. Unfold `flagVec`.

Rewrite using `[dif_neg (by omega), dif_neg (by omega), if_neg (by omega), dif_pos (by omega)]`. Use `congr 1`. Apply `Fin.ext` to reduce the goal to its premises. Use `show 2 * ρ + k - (2 * ρ + k - a.1) = a.1`. Use linear arithmetic over natural numbers and integers.

Establish `e2 : flagVec e0 f0 z0 bw bwd (if a.1 + 1 < ρ then a.1 + 1 else ρ + k) = nxt e0 z0 a`. Unfold `nxt`. Distinguish the cases in `h : a.1 + 1 < ρ`. Rewrite using `[if_pos h, dif_pos h]`. Unfold `flagVec`.

Rewrite using `[dif_pos h]`. Rewrite using `[if_neg h, dif_neg h]`. Unfold `flagVec`. Rewrite using `[dif_neg (by omega), dif_neg (by omega), if_pos rfl]`. Rewrite using `[← e1, ← e2]`.

Conclude with `key`. Establish `hi` using `i.2`. Distinguish the cases in `h : i.1 + 1 < k`. Use `swap`. Rewrite using `[dif_neg h, dif_neg h, sub_zero]`.

Conclude with `Z_zero I g`. Rewrite using `[dif_pos h, dif_pos h]`. Apply the tactic sequence `have key := pair_zmod I g ρ k _ β hβ hG x hx ⟨ρ + (k - (i.1 + 1)), by omega⟩ ⟨ρ + (i.1 + 1), by omega⟩ ⟨ρ + i.1, by omega⟩ (by show ρ + (k - (i.1 + 1)) ≠ _; omega) (by show ρ + i.1 = dualIdx ρ k (ρ + (k - (i.1 + 1))); unfold dualIdx; split_ifs <;> omega)`. Establish `c : ∀ l : Fin k, flagVec e0 f0 z0 bw bwd (ρ + l.1) = bw l + bwd (Fin.rev l)`. Introduce `l`.

Establish `hl` using `l.2`. Establish `: (⟨ρ + l.1 - ρ, by omega⟩ : Fin k) = l` using `Fin.ext (by show ρ + l.1 - ρ = l.1; omega)`. Unfold `flagVec`. Rewrite using `[dif_neg (by omega), dif_pos (by omega), this]`. Establish `e1 : bwd i = sigA I ew • flagVec e0 f0 z0 bw bwd (ρ + (k - (i.1 + 1)))`.

Use `c (Fin.rev i)` as an intermediate fact. Rewrite `this` using `[Fin.val_rev, Fin.rev_rev]`. Rewrite using `[this, smul_add, hw, smul_smul, mul_comm, hor, zero_smul, zero_add]`. Conclude with `hwd i`. Establish `e2 : bw ⟨i.1 + 1, h⟩ = ew • flagVec e0 f0 z0 bw bwd (ρ + (i.1 + 1))`.

Rewrite using `[c ⟨i.1 + 1, h⟩, smul_add, hwd, smul_smul, hor, zero_smul, add_zero]`. Conclude with `hw _`. Rewrite using `[e1, e2, Matrix.mulVec_smul, hA_smul_left, hA_smul_right, sigA_sigA, ← mul_assoc, hid, ← mul_sub]`. Conclude with `Z_smul I g hint key`.
-/
theorem chiArg_sub_rootSum : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β → (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) → ∀ x : I.Gf, (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β → ZMod' I g (chiArg I e0 f0 z0 bw bwd x - rootSum ρ k ew (matIn I β x)) := by
  intro I g ρ k e0 f0 z0 bw bwd ew hF hn β hβ hG x hx
  obtain ⟨-, -, -, -, ⟨hid, hor, hint, -⟩, ⟨hw, hwd⟩, -, -⟩ := hF
  rw [rootSum_eq hn]
  unfold chiArg
  rw [add_sub_add_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Z_add I g (Z_sum I g _ _ fun a _ => ?_) (Z_sum I g _ _ fun i _ => ?_)
  · have ha := a.2
    have key := pair_zmod I g ρ k _ β hβ hG x hx ⟨2 * ρ + k - a.1, by omega⟩
      ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by split_ifs <;> omega⟩ ⟨a.1, by omega⟩ (by show 2 * ρ + k - a.1 ≠ _; omega)
      (by show a.1 = dualIdx ρ k (2 * ρ + k - a.1); unfold dualIdx; split_ifs <;> omega)
    have e1 : flagVec e0 f0 z0 bw bwd (2 * ρ + k - a.1) = f0 a := by
      unfold flagVec
      rw [dif_neg (by omega), dif_neg (by omega), if_neg (by omega), dif_pos (by omega)]
      congr 1
      apply Fin.ext
      show 2 * ρ + k - (2 * ρ + k - a.1) = a.1
      omega
    have e2 : flagVec e0 f0 z0 bw bwd (if a.1 + 1 < ρ then a.1 + 1 else ρ + k) = nxt e0 z0 a := by
      unfold nxt
      by_cases h : a.1 + 1 < ρ
      · rw [if_pos h, dif_pos h]
        unfold flagVec
        rw [dif_pos h]
      · rw [if_neg h, dif_neg h]
        unfold flagVec
        rw [dif_neg (by omega), dif_neg (by omega), if_pos rfl]
    rw [← e1, ← e2]
    exact key
  · have hi := i.2
    by_cases h : i.1 + 1 < k
    swap
    · rw [dif_neg h, dif_neg h, sub_zero]
      exact Z_zero I g
    rw [dif_pos h, dif_pos h]
    have key := pair_zmod I g ρ k _ β hβ hG x hx ⟨ρ + (k - (i.1 + 1)), by omega⟩
      ⟨ρ + (i.1 + 1), by omega⟩ ⟨ρ + i.1, by omega⟩ (by show ρ + (k - (i.1 + 1)) ≠ _; omega)
      (by show ρ + i.1 = dualIdx ρ k (ρ + (k - (i.1 + 1))); unfold dualIdx; split_ifs <;> omega)
    have c : ∀ l : Fin k, flagVec e0 f0 z0 bw bwd (ρ + l.1) = bw l + bwd (Fin.rev l) := by
      intro l
      have hl := l.2
      have : (⟨ρ + l.1 - ρ, by omega⟩ : Fin k) = l := Fin.ext (by show ρ + l.1 - ρ = l.1; omega)
      unfold flagVec
      rw [dif_neg (by omega), dif_pos (by omega), this]
    have e1 : bwd i = sigA I ew • flagVec e0 f0 z0 bw bwd (ρ + (k - (i.1 + 1))) := by
      have := c (Fin.rev i)
      rw [Fin.val_rev, Fin.rev_rev] at this
      rw [this, smul_add, hw, smul_smul, mul_comm, hor, zero_smul, zero_add]
      exact hwd i
    have e2 : bw ⟨i.1 + 1, h⟩ = ew • flagVec e0 f0 z0 bw bwd (ρ + (i.1 + 1)) := by
      rw [c ⟨i.1 + 1, h⟩, smul_add, hwd, smul_smul, hor, zero_smul, add_zero]
      exact hw _
    rw [e1, e2, Matrix.mulVec_smul, hA_smul_left, hA_smul_right, sigA_sigA, ← mul_assoc, hid, ← mul_sub]
    exact Z_smul I g hint key

end GlobalTheory.FlagChi

end
