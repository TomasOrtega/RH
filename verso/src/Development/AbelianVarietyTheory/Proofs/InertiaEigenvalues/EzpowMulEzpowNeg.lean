import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinXiExtMemRigidTensorIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensor

noncomputable section

open PowerSeries Matrix GlobalTheory.BK GlobalTheory.BKGal.JumpDR

namespace GlobalTheory.BKGal.JumpDR.Horiz

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

variable (O K l e) in

def cterm (x : Ahat O K l e) : AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K)) :=
  PowerSeries.constantCoeff ((AhatEq.equivAhat O K l e).symm x)

variable (O l e) in
open Classical in

def hatR (f : K⟦X⟧) : Ahat O K l e := if h : f ∈ Rpi O K l e then toHat O K l e ⟨f, h⟩ else 0

/- English proof (translation)
Unfold `hatR`. Rewrite using `[dif_pos h]`.
-/
theorem hatR_of_mem {f : K⟦X⟧} (h : f ∈ Rpi O K l e) : hatR O l e f = toHat O K l e ⟨f, h⟩ := by
  unfold hatR
  rw [dif_pos h]

variable (K a) in

def dvec (k : ι) : ZMod a → ι → K := fun _ => Pi.single k 1

variable (ι) in

def idx : Fin (Fintype.card ι) → ι := (Fintype.equivFin ι).symm

def xiVec (P : PhiMod O K l e a ι) (k : Fin (Fintype.card ι)) : Vec K a ι := P.xi (dvec K a (idx ι k))

def coordHat (P : PhiMod O K l e a ι) (y : Vec K a ι) (k : Fin (Fintype.card ι)) : ZMod a → Ahat O K l e :=
  fun τ => hatR O l e (P.xiExt.symm y τ (idx ι k))

def constPart (P : PhiMod O K l e a ι) (y : Vec K a ι) : ZMod a → ι → AhatE O K l e :=
  hsum P (fun k => kLift O (fun τ => cterm O K l e (coordHat P y k τ))) (xiVec P)

/- English proof (translation)
Establish `hc : cst (dvec K a (idx ι k)) τ = Pi.single (idx ι k) (1 : K⟦X⟧)`. Use function extensionality and compare the values at `j`. Rewrite using `[cst_apply]`. Simplify using `only [dvec, Pi.single_apply]`. Use `split_ifs`.

Conclude with `map_one _`. Conclude with `map_zero _`. Use `show (P.xi (dvec K a (idx ι k))) τ i = _`. Rewrite using `[P.xi_apply, P.xiExt_apply, hc, Matrix.mulVec_single_one]`. Both sides reduce to the same expression.
-/
theorem xiVec_apply (P : PhiMod O K l e a ι) (k : Fin (Fintype.card ι)) (τ : ZMod a) (i : ι) :
    xiVec P k τ i = P.xiMat τ i (idx ι k) := by
  have hc : cst (dvec K a (idx ι k)) τ = Pi.single (idx ι k) (1 : K⟦X⟧) := by
    funext j
    rw [cst_apply]
    simp only [dvec, Pi.single_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  show (P.xi (dvec K a (idx ι k))) τ i = _
  rw [P.xi_apply, P.xiExt_apply, hc, Matrix.mulVec_single_one]
  rfl

end GlobalTheory.BKGal.JumpDR.Horiz

namespace GlobalTheory.BKGal.JumpDR.Horiz

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `he : (0 : ℝ) < e` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Apply `one_div_lt_one_div_of_lt he` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_div_lt (l e : ℕ) [Fact l.Prime] [NeZero e] : 1 / ((e : ℝ) * l) < 1 / e := by
  have he : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  apply one_div_lt_one_div_of_lt he
  nlinarith

/- English proof (translation)
Use `mem_tot.2 fun τ => mem_vecs.2 fun m => ?_` and prove the remaining obligations. Rewrite using `[cst_apply]`. Simplify using `only [dvec, Pi.single_apply]`. Use `split_ifs`. Rewrite using `[map_one]`.

Conclude with `one_mem B`. Rewrite using `[map_zero]`. Conclude with `zero_mem B`.
-/
private theorem cst_dvec_mem_Mext (P : PhiMod O K l e a ι) (B : Subalgebra O K⟦X⟧) (j : ι) :
    cst (dvec K a j) ∈ P.Mext B := by
  refine mem_tot.2 fun τ => mem_vecs.2 fun m => ?_
  rw [cst_apply]
  simp only [dvec, Pi.single_apply]
  split_ifs
  · rw [map_one]
    exact one_mem B
  · rw [map_zero]
    exact zero_mem B

/- English proof (translation)
The claim follows from `((xi_trivialises_invL_S O K l e a ι P).2 _).2 (cst_dvec_mem_Mext P _ j)`.
-/
private theorem xiExt_cst_dvec_mem_MMl [NeZero a] (P : PhiMod O K l e a ι) (j : ι) :
    P.xiExt (cst (dvec K a j)) ∈ P.MMl :=
  ((xi_trivialises_invL_S O K l e a ι P).2 _).2 (cst_dvec_mem_Mext P _ j)

/- English proof (translation)
Establish `hcol` using `xiVec_apply P (Fintype.equivFin ι j) τ i`. Simplify using `only [idx, Equiv.symm_apply_apply] at hcol`. Rewrite using `[← hcol]`. Establish `hk : P.xiExt (cst (dvec K a j)) ∈ tot (P.extc (invL l (S O K e)))` using `xiExt_cst_dvec_mem_MMl P j`. Take `⟨m, hm, hmeq⟩` from `P.mem_extc.1 (mem_tot.1 hk τ)`.

Establish `hx : xiVec P (Fintype.equivFin ι j) τ i = P.xiExt (cst (dvec K a j)) τ i` using `by show P.xiExt (cst (dvec K a (idx ι (Fintype.equivFin ι j)))) τ i = _`. Simplify using `only [idx, Equiv.symm_apply_apply]`. Rewrite using `[hx, hmeq]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Subalgebra.sum_mem _ fun c _ => Subalgebra.mul_mem _ ?_ ?_` and prove the remaining obligations.

Conclude with `invE_A_le_RpiE (O := O) (K := K) (l := l) (e := e) (P.mx_mem τ i c)`. Conclude with `invE_invL_S_le_RpiE (O := O) (K := K) (l := l) (e := e) (le_away _ _ (mem_vecs.1 hm c))`.
-/
theorem xiMat_mem_RpiE [NeZero a] (P : PhiMod O K l e a ι) (τ : ZMod a) (i j : ι) :
    P.xiMat τ i j ∈ RpiE O K l e := by
  have hcol := xiVec_apply P (Fintype.equivFin ι j) τ i
  simp only [idx, Equiv.symm_apply_apply] at hcol
  rw [← hcol]
  have hk : P.xiExt (cst (dvec K a j)) ∈ tot (P.extc (invL l (S O K e))) := xiExt_cst_dvec_mem_MMl P j
  obtain ⟨m, hm, hmeq⟩ := P.mem_extc.1 (mem_tot.1 hk τ)
  have hx : xiVec P (Fintype.equivFin ι j) τ i = P.xiExt (cst (dvec K a j)) τ i := by
    show P.xiExt (cst (dvec K a (idx ι (Fintype.equivFin ι j)))) τ i = _
    simp only [idx, Equiv.symm_apply_apply]
  rw [hx, hmeq]
  simp only [Matrix.mulVec, dotProduct]
  refine Subalgebra.sum_mem _ fun c _ => Subalgebra.mul_mem _ ?_ ?_
  · exact invE_A_le_RpiE (O := O) (K := K) (l := l) (e := e) (P.mx_mem τ i c)
  · exact invE_invL_S_le_RpiE (O := O) (K := K) (l := l) (e := e) (le_away _ _ (mem_vecs.1 hm c))

/- English proof (translation)
Unfold `RpiE`. Conclude with `le_away _ _`.
-/
private theorem Rpi_le_RpiE : Rpi O K l e ≤ RpiE O K l e := by
  unfold RpiE
  exact le_away _ _

/- English proof (translation)
Rewrite using `[hat_of_mem (l := l) (e := e) (zero_mem _)]`. Conclude with `map_zero _`.
-/
private theorem hat_zero' : hat O l e (0 : K⟦X⟧) = 0 := by
  rw [hat_of_mem (l := l) (e := e) (zero_mem _)]
  exact map_zero _

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Rewrite using `[Finset.sum_empty, Finset.sum_empty]`. Conclude with `hat_zero'`. Introduce `j s hj ih hg`.

Establish `h1` using `hg j (Finset.mem_insert_self j s)`. Establish `h2 : ∀ x ∈ s, g x ∈ RpiE O K l e` using `fun x hx => hg x (Finset.mem_insert_of_mem hx)`. Rewrite using `[Finset.sum_insert hj, Finset.sum_insert hj, hat_add (l := l) (e := e) h1 (Subalgebra.sum_mem _ h2), ih h2]`.
-/
private theorem hat_sum' {g : ι → K⟦X⟧} (s : Finset ι) :
    (∀ j ∈ s, g j ∈ RpiE O K l e) → hat O l e (∑ j ∈ s, g j) = ∑ j ∈ s, hat O l e (g j) := by
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty, Finset.sum_empty]
    exact hat_zero'
  · intro j s hj ih hg
    have h1 := hg j (Finset.mem_insert_self j s)
    have h2 : ∀ x ∈ s, g x ∈ RpiE O K l e := fun x hx => hg x (Finset.mem_insert_of_mem hx)
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      hat_add (l := l) (e := e) h1 (Subalgebra.sum_mem _ h2), ih h2]

/- English proof (translation)
Establish `hw : ∀ σ j, P.xiExt.symm y σ j ∈ Rpi O K l e` using `fun σ j => mem_vecs.1 (mem_tot.1 hy σ) j`. Use function extensionality and compare the values at `τ i`. Use `show hat O l e (y τ i) = ∑ k, algebraMap _ _ (coordHat P y k τ) * P.hatTot (xiVec P k) τ i`. Establish `hy' : y τ i = ∑ j, P.xiMat τ i j * P.xiExt.symm y τ j` using `by conv_lhs => rw [← P.xiExt.apply_symm_apply y]`. Rewrite using `[P.xiExt_apply]`.

Both sides reduce to the same expression. Rewrite using `[hy', hat_sum' _ fun j _ => Subalgebra.mul_mem _ (xiMat_mem_RpiE P τ i j) (Rpi_le_RpiE (hw τ j))]`. Rewrite using `[← (Fintype.equivFin ι).symm.sum_comp]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `e1 : algebraMap _ _ (coordHat P y k τ) = hat O l e (P.xiExt.symm y τ (idx ι k))` using `by show algebraMap _ _ (hatR O l e (P.xiExt.symm y τ (idx ι k))) = _`.

Rewrite using `[hatR_of_mem (hw τ _)]`. Conclude with `(hat_coe_Rpi (l := l) (e := e) ⟨_, hw τ _⟩).symm`. Establish `e2 : P.hatTot (xiVec P k) τ i = hat O l e (P.xiMat τ i (idx ι k))` using `by show hat O l e (xiVec P k τ i) = _`. Rewrite using `[xiVec_apply]`. Rewrite using `[e1, e2]`.

Conclude with `(hat_mul (l := l) (e := e) (xiMat_mem_RpiE P τ i _) (Rpi_le_RpiE (hw τ _))).trans (mul_comm _ _)`.
-/
theorem hatTot_eq_hsum [NeZero a] (P : PhiMod O K l e a ι) {y : Vec K a ι}
    (hy : P.xiExt.symm y ∈ P.Mext (Rpi O K l e)) :
    P.hatTot y = hsum P (coordHat P y) (xiVec P) := by
  have hw : ∀ σ j, P.xiExt.symm y σ j ∈ Rpi O K l e := fun σ j => mem_vecs.1 (mem_tot.1 hy σ) j
  funext τ i
  show hat O l e (y τ i) = ∑ k, algebraMap _ _ (coordHat P y k τ) * P.hatTot (xiVec P k) τ i
  have hy' : y τ i = ∑ j, P.xiMat τ i j * P.xiExt.symm y τ j := by
    conv_lhs => rw [← P.xiExt.apply_symm_apply y]
    rw [P.xiExt_apply]
    rfl
  rw [hy', hat_sum' _ fun j _ => Subalgebra.mul_mem _ (xiMat_mem_RpiE P τ i j)
    (Rpi_le_RpiE (hw τ j))]
  rw [← (Fintype.equivFin ι).symm.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : algebraMap _ _ (coordHat P y k τ) = hat O l e (P.xiExt.symm y τ (idx ι k)) := by
    show algebraMap _ _ (hatR O l e (P.xiExt.symm y τ (idx ι k))) = _
    rw [hatR_of_mem (hw τ _)]
    exact (hat_coe_Rpi (l := l) (e := e) ⟨_, hw τ _⟩).symm
  have e2 : P.hatTot (xiVec P k) τ i = hat O l e (P.xiMat τ i (idx ι k)) := by
    show hat O l e (xiVec P k τ i) = _
    rw [xiVec_apply]
  rw [e1, e2]
  exact (hat_mul (l := l) (e := e) (xiMat_mem_RpiE P τ i _) (Rpi_le_RpiE (hw τ _))).trans
    (mul_comm _ _)

end GlobalTheory.BKGal.JumpDR.Horiz

namespace GlobalTheory.BKGal.JumpDR.Horiz

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `hy' : y ∈ tot (P.extc B)` using `hy`. Use `show y ∈ tot (P.extc B')`. Use `mem_tot.2 fun τ => ?_` and prove the remaining obligations. Take `⟨m, hm, hmeq⟩` from `P.mem_extc.1 (mem_tot.1 hy' τ)`. Rewrite using `[hmeq]`.

Conclude with `P.mem_extc.2 ⟨m, mem_vecs.2 fun j => h (mem_vecs.1 hm j), rfl⟩`.
-/
theorem ext_mono (P : PhiMod O K l e a ι) {B B' : Subalgebra O K⟦X⟧} (h : B ≤ B') {y : Vec K a ι}
    (hy : y ∈ P.ext B) : y ∈ P.ext B' := by
  have hy' : y ∈ tot (P.extc B) := hy
  show y ∈ tot (P.extc B')
  refine mem_tot.2 fun τ => ?_
  obtain ⟨m, hm, hmeq⟩ := P.mem_extc.1 (mem_tot.1 hy' τ)
  rw [hmeq]
  exact P.mem_extc.2 ⟨m, mem_vecs.2 fun j => h (mem_vecs.1 hm j), rfl⟩

/- English proof (translation)
Unfold `Rpi`. Conclude with `invL_le l (S_le_R l e)`.
-/
private theorem invL_S_le_Rpi' : invL l (S O K e) ≤ Rpi O K l e := by
  unfold Rpi
  exact invL_le l (S_le_R l e)

/- English proof (translation)
Establish `hAS : invL l (A O K) ≤ invL l (S O K e)` using `away_mono (A_le_S (O := O) (K := K) l e) (by simp)`. Establish `h1 : y ∈ P.MMl` using `ext_mono P hAS hy`. Establish `h2 : P.xiExt.symm y ∈ P.Mext (invL l (S O K e))` using `((xi_trivialises_invL_S O K l e a ι P).2 _).1 (by rwa [LinearEquiv.apply_symm_apply])`. Conclude with `P.Mext_mono invL_S_le_Rpi' h2`.
-/
theorem xiExt_symm_mem [NeZero a] (P : PhiMod O K l e a ι) {y : Vec K a ι}
    (hy : y ∈ P.ext (invL l (A O K))) : P.xiExt.symm y ∈ P.Mext (Rpi O K l e) := by
  have hAS : invL l (A O K) ≤ invL l (S O K e) :=
    away_mono (A_le_S (O := O) (K := K) l e) (by simp)
  have h1 : y ∈ P.MMl := ext_mono P hAS hy
  have h2 : P.xiExt.symm y ∈ P.Mext (invL l (S O K e)) :=
    ((xi_trivialises_invL_S O K l e a ι P).2 _).1 (by rwa [LinearEquiv.apply_symm_apply])
  exact P.Mext_mono invL_S_le_Rpi' h2

/- English proof (translation)
Establish `he : (0 : ℝ) < 1 / (e : ℝ)` using `one_div_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e))`. Unfold `Rpi`. Conclude with `invL_le l (A_le_R l he)`.
-/
private theorem invL_A_le_Rpi' : invL l (A O K) ≤ Rpi O K l e := by
  have he : (0 : ℝ) < 1 / (e : ℝ) :=
    one_div_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e))
  unfold Rpi
  exact invL_le l (A_le_R l he)

/- English proof (translation)
Establish `hz : ∀ τ j, Ezpow K l e (-i) * y τ j ∈ Rpi O K l e` using `fun τ j => invL_A_le_Rpi' (mem_vecs.1 (mem_tot.1 hy τ) j)`. Establish `hN : 0 ≤ i + ((-i).toNat : ℤ)`. Use `Int.self_le_toNat (-i)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨(-i).toNat, hN, fun τ j => ?_⟩` and prove the remaining obligations.

Establish `hm : (((i + ((-i).toNat : ℤ)).toNat : ℕ) : ℤ) = i + ((-i).toNat : ℤ)` using `Int.toNat_of_nonneg hN`. Establish `key : E K l e ^ (i + ((-i).toNat : ℤ)).toNat * (Ezpow K l e (-i) * y τ j) = E K l e ^ (-i).toNat * y τ j`. Rewrite using `[← mul_assoc, ← Ezpow_natCast (K := K) l e, ← Ezpow_add (K := K) l e, ← Ezpow_natCast (K := K) l e (-i).toNat]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers.

Establish `hyE : y τ j ∈ RpiE O K l e`. Unfold `RpiE`. Use `mem_away.2 ⟨(-i).toNat, ?_⟩` and prove the remaining obligations. Rewrite using `[coe_EIn, ← key]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (E_mem l e _) _) (hz τ j)`.

Use `⟨toHat O K l e ⟨_, hz τ j⟩, ?_⟩` and prove the remaining obligations. Establish `e1 : algebraMap (Ahat O K l e) (AhatE O K l e) (toHat O K l e ⟨_, hz τ j⟩) = hat O l e (Ezpow K l e (-i) * y τ j)` using `(hat_coe_Rpi (l := l) (e := e) ⟨_, hz τ j⟩).symm`. Establish `e2` using `hat_E_pow_mul (O := O) l e (i + ((-i).toNat : ℤ)).toNat (Rpi_le_RpiE (hz τ j))`. Establish `e3` using `hat_E_pow_mul (O := O) l e (-i).toNat hyE`. Rewrite using `[map_mul, e1, ← e2, key, e3]`.

Both sides reduce to the same expression.
-/
theorem inEhat_hatTot (P : PhiMod O K l e a ι) {i : ℤ} {y : Vec K a ι}
    (hy : Ezpow K l e (-i) • y ∈ P.Mext (invL l (A O K))) : InEhat O K l e i (P.hatTot y) := by
  have hz : ∀ τ j, Ezpow K l e (-i) * y τ j ∈ Rpi O K l e :=
    fun τ j => invL_A_le_Rpi' (mem_vecs.1 (mem_tot.1 hy τ) j)
  have hN : 0 ≤ i + ((-i).toNat : ℤ) := by
    have := Int.self_le_toNat (-i)
    omega
  refine ⟨(-i).toNat, hN, fun τ j => ?_⟩
  have hm : (((i + ((-i).toNat : ℤ)).toNat : ℕ) : ℤ) = i + ((-i).toNat : ℤ) := Int.toNat_of_nonneg hN
  have key : E K l e ^ (i + ((-i).toNat : ℤ)).toNat * (Ezpow K l e (-i) * y τ j) =
      E K l e ^ (-i).toNat * y τ j := by
    rw [← mul_assoc, ← Ezpow_natCast (K := K) l e, ← Ezpow_add (K := K) l e,
      ← Ezpow_natCast (K := K) l e (-i).toNat]
    congr 2
    omega
  have hyE : y τ j ∈ RpiE O K l e := by
    unfold RpiE
    refine mem_away.2 ⟨(-i).toNat, ?_⟩
    rw [coe_EIn, ← key]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (E_mem l e _) _) (hz τ j)
  refine ⟨toHat O K l e ⟨_, hz τ j⟩, ?_⟩
  have e1 : algebraMap (Ahat O K l e) (AhatE O K l e) (toHat O K l e ⟨_, hz τ j⟩) =
      hat O l e (Ezpow K l e (-i) * y τ j) := (hat_coe_Rpi (l := l) (e := e) ⟨_, hz τ j⟩).symm
  have e2 := hat_E_pow_mul (O := O) l e (i + ((-i).toNat : ℤ)).toNat (Rpi_le_RpiE (hz τ j))
  have e3 := hat_E_pow_mul (O := O) l e (-i).toNat hyE
  rw [map_mul, e1, ← e2, key, e3]
  rfl

end GlobalTheory.BKGal.JumpDR.Horiz

namespace GlobalTheory.BKGal.JumpDR.Horiz

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Rewrite using `[P.xi_apply]`. Conclude with `xiExt_cst_dvec_mem_MMl P _`.
-/
theorem xiVec_mem_MMl [NeZero a] (P : PhiMod O K l e a ι) (k : Fin (Fintype.card ι)) :
    P.xi (dvec K a (idx ι k)) ∈ P.MMl := by
  rw [P.xi_apply]
  exact xiExt_cst_dvec_mem_MMl P _

/- English proof (translation)
Introduce `y hy`. Rewrite `hy`, the goal using `[mem_shiftE]`. Establish `hEz : Ezpow K l e (-i) = E K l e * Ezpow K l e (-(i + 1))`. Establish `h1` using `Ezpow_natCast (K := K) l e 1`. Rewrite `h1` using `[pow_one, Nat.cast_one]`.

Rewrite using `[← h1, ← Ezpow_add (K := K) l e]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hEz, mul_smul]`. Use `mem_tot.2 fun τ => mem_vecs.2 fun j => ?_` and prove the remaining obligations.

Conclude with `Subalgebra.mul_mem _ (E_mem l e _) (mem_vecs.1 (mem_tot.1 hy τ) j)`.
-/
theorem shiftE_succ_le (P : PhiMod O K l e a ι) (i : ℤ) :
    shiftE l e (i + 1) (P.Mext (invL l (A O K))) ≤ shiftE l e i (P.Mext (invL l (A O K))) := by
  intro y hy
  rw [mem_shiftE] at hy ⊢
  have hEz : Ezpow K l e (-i) = E K l e * Ezpow K l e (-(i + 1)) := by
    have h1 := Ezpow_natCast (K := K) l e 1
    rw [pow_one, Nat.cast_one] at h1
    rw [← h1, ← Ezpow_add (K := K) l e]
    congr 1
    ring
  rw [hEz, mul_smul]
  refine mem_tot.2 fun τ => mem_vecs.2 fun j => ?_
  exact Subalgebra.mul_mem _ (E_mem l e _) (mem_vecs.1 (mem_tot.1 hy τ) j)

/- English proof (translation)
Establish `hne : P.filL (i + 1) ≠ P.filL i` using `hi`. Establish `hle : P.filL (i + 1) ≤ P.filL i`. Unfold `PhiMod.filL`. Conclude with `sup_le_sup_right (inf_le_inf_left _ (shiftE_succ_le P i)) _`. Take `⟨x, hx, hnx⟩` from `SetLike.exists_of_lt (lt_of_le_of_ne hle hne)`.

Establish `hx' : x ∈ (P.ext (invL l (A O K)) ⊓ shiftE l e i (P.Mext (invL l (A O K)))) ⊔ shiftE l e 1 (P.ext (invL l (A O K)))` using `hx`. Take `⟨u, hu, v, hv, rfl⟩` from `Submodule.mem_sup.1 hx'`. Take `⟨hu1, hu2⟩` from `Submodule.mem_inf.1 hu`. Use `⟨u, hu1, mem_shiftE.1 hu2, fun hu' => hnx ?_⟩` and prove the remaining obligations. Establish `hv' : v ∈ P.filL (i + 1)` using `Submodule.mem_sup_right hv`.

Conclude with `Submodule.add_mem _ hu' hv'`.
-/
theorem exists_of_mem_jumps (P : PhiMod O K l e a ι) {i : ℤ} (hi : i ∈ P.jumps) :
    ∃ y, y ∈ P.ext (invL l (A O K)) ∧ Ezpow K l e (-i) • y ∈ P.Mext (invL l (A O K)) ∧
      y ∉ P.filL (i + 1) := by
  have hne : P.filL (i + 1) ≠ P.filL i := hi
  have hle : P.filL (i + 1) ≤ P.filL i := by
    unfold PhiMod.filL
    exact sup_le_sup_right (inf_le_inf_left _ (shiftE_succ_le P i)) _
  obtain ⟨x, hx, hnx⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have hx' : x ∈ (P.ext (invL l (A O K)) ⊓ shiftE l e i (P.Mext (invL l (A O K)))) ⊔
      shiftE l e 1 (P.ext (invL l (A O K))) := hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hx'
  obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.1 hu
  refine ⟨u, hu1, mem_shiftE.1 hu2, fun hu' => hnx ?_⟩
  have hv' : v ∈ P.filL (i + 1) := Submodule.mem_sup_right hv
  exact Submodule.add_mem _ hu' hv'

end GlobalTheory.BKGal.JumpDR.Horiz
