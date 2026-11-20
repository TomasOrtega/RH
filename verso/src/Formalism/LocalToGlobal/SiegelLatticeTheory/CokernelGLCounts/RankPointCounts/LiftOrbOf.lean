import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MulVecInj

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

set_option maxHeartbeats 1600000

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hOK m Z Z' ⟨φ⟩ hκ`. Use `set e : Fin (m + 1) → M.R := Pi.single (Fin.last m) 1 with he`. Establish `hmkZ : ∀ x : Fin (m + 1) → M.R, (Submodule.Quotient.mk (Z.Z.mulVec x) : M.Cok Z) = 0` using `fun x => (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩`. Establish `hmkZ' : ∀ x : Fin (m + 1) → M.R, (Submodule.Quotient.mk (Z'.Z.mulVec x) : M.Cok Z') = 0` using `fun x => (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩`. Establish `hcol : ∀ j : Fin (m + 1), ∃ w : Fin (m + 1) → M.R, (Submodule.Quotient.mk w : M.Cok Z') = φ.1 (Submodule.Quotient.mk (Pi.single j 1)) ∧ mu M Z' w = mu M Z (Pi.single j 1) ∧ (j = Fin.last m → w = e)`.

Introduce `j`. Distinguish the cases in `hj : j = Fin.last m`. Substitute `hj` using the available equality. Use `⟨e, φ.2.1.symm, ?_, fun _ => rfl⟩` and prove the remaining obligations. Rewrite using `[he, mu_e, mu_e, hκ]`.

Take `⟨v, hv⟩` from `Submodule.Quotient.mk_surjective _ (φ.1 (Submodule.Quotient.mk (Pi.single j 1)))`. Establish `hl` using `φ.2.2 (Submodule.Quotient.mk (Pi.single j 1))`. Rewrite `hl` using `[← hv, lam_mk, lam_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Take `⟨t, ht⟩` from `hl`. Use `⟨v - Z'.Z.mulVec (t • e), ?_, ?_, fun h => absurd h hj⟩` and prove the remaining obligations.

Rewrite using `[Submodule.Quotient.mk_sub, hmkZ', sub_zero, hv]`. Establish `ht' : ((t : M.R) : E) = mu M Z' v - mu M Z (Pi.single j 1)` using `ht`. Rewrite using `[sub_eq_add_neg, ← Matrix.mulVec_neg, mu_add, mu_Z]`. Simplify using `only [Pi.neg_apply, Pi.smul_apply, he, Pi.single_eq_same, smul_eq_mul, mul_one, NegMemClass.coe_neg]`. Rewrite using `[ht']`.

Expand and normalize the polynomial expressions, which then agree. Use `choose w hw1 hw2 hw3 using hcol`. Use `set l₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) M.R := Matrix.of fun i j => w j i with hl₁`. Establish `hl₁v : ∀ x, l₁.mulVec x = ∑ j, x j • w j`. Introduce `x`.

Use function extensionality and compare the values at `i`. Simplify using `[hl₁, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Establish `hx : ∀ x : Fin (m + 1) → M.R, ∑ j, x j • (Pi.single j 1 : Fin (m + 1) → M.R) = x`. Introduce `x`. Use function extensionality and compare the values at `i`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `hP1 : ∀ x, (Submodule.Quotient.mk (l₁.mulVec x) : M.Cok Z') = φ.1 (Submodule.Quotient.mk x)`. Introduce `x`. Use `conv_rhs => rw [← hx x]`. Rewrite using `[hl₁v]`.

Establish `e1 : (Submodule.Quotient.mk (∑ j, x j • w j) : M.Cok Z') = ∑ j, x j • (Submodule.Quotient.mk (w j) : M.Cok Z')`. Rewrite using `[← Submodule.mkQ_apply, map_sum]`. Simplify using the standard rewrite rules. Establish `e2 : (Submodule.Quotient.mk (∑ j, x j • (Pi.single j 1 : Fin (m + 1) → M.R)) : M.Cok Z) = ∑ j, x j • (Submodule.Quotient.mk (Pi.single j 1) : M.Cok Z)`. Rewrite using `[← Submodule.mkQ_apply, map_sum]`.

Simplify using the standard rewrite rules. Rewrite using `[e1, e2, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hw1 j]`. Establish `hP2 : ∀ x, mu M Z' (l₁.mulVec x) = mu M Z x`.

Introduce `x`. Use `conv_rhs => rw [← hx x]`. Rewrite using `[hl₁v, mu_sum, mu_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mu_smul, mu_smul, hw2 j]`.

Establish `hl₁e : ∀ i, l₁ i (Fin.last m) = if i = Fin.last m then 1 else 0`. Introduce `i`. Simplify using `only [hl₁, Matrix.of_apply, hw3 _ rfl, he, Pi.single_apply]`. Establish `hK1 : ∀ y ∈ headK M Z', (Submodule.Quotient.mk y : M.Cok Z') = 0`. Introduce `y hy`.

Take `⟨x, -, rfl⟩` from `(mem_headK M Z').1 hy`. Conclude with `hmkZ' x`. Establish `hK2 : ∀ y ∈ headK M Z', mu M Z' y = 0`. Introduce `y hy`. Take `⟨x, hx0, rfl⟩` from `(mem_headK M Z').1 hy`.

Rewrite using `[mu_Z, hx0]`. Simplify using the standard rewrite rules. Establish `hb : ∃ y₀, Z'.Z.mulVec y₀ = l₁.mulVec (Z.Z.mulVec e) ∧ y₀ (Fin.last m) = 1`. Establish `h0 : (Submodule.Quotient.mk (l₁.mulVec (Z.Z.mulVec e)) : M.Cok Z') = 0`. Rewrite using `[hP1, hmkZ, map_zero]`.

Take `⟨y₀, hy₀⟩` from `(Submodule.Quotient.mk_eq_zero _).1 h0`. Establish `hy₀' : Z'.Z.mulVec y₀ = l₁.mulVec (Z.Z.mulVec e)` using `hy₀`. Use `⟨y₀, hy₀', ?_⟩` and prove the remaining obligations. Use `hP2 (Z.Z.mulVec e)` as an intermediate fact. Rewrite `this` using `[← hy₀', mu_Z, mu_Z, he, Pi.single_eq_same]`.

Conclude with `Subtype.ext (by simpa using this)`. Take `⟨y₀, hy₀, hy₀l⟩` from `hb`. Establish `hspan : ∀ v : Fin (m + 1) → M.R, ∃ x, v - l₁.mulVec x ∈ headK M Z'`. Introduce `v`. Take `⟨x₀, hx₀⟩` from `Submodule.Quotient.mk_surjective _ (φ.1.symm (Submodule.Quotient.mk v))`.

Establish `h1 : (Submodule.Quotient.mk (v - l₁.mulVec x₀) : M.Cok Z') = 0`. Rewrite using `[Submodule.Quotient.mk_sub, hP1, hx₀, LinearEquiv.apply_symm_apply, sub_self]`. Take `⟨y, hy⟩` from `(Submodule.Quotient.mk_eq_zero _).1 h1`. Simplify using `only [Matrix.mulVecLin_apply] at hy`. Use `⟨x₀ + y (Fin.last m) • Z.Z.mulVec e, (mem_headK M Z').2 ⟨y - y (Fin.last m) • y₀, ?_, ?_⟩⟩` and prove the remaining obligations.

Simplify using `[hy₀l]`. Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_smul, hy₀, hy, Matrix.mulVec_add, Matrix.mulVec_smul]`. Normalize the expressions using the abelian group laws. Take `⟨H, hHK, hHl, hdet⟩` from `hSR M hOK m l₁ (headK M Z') hl₁e hspan`. Use `set l := l₁ + H with hl`.

Establish `hHx : ∀ x, H.mulVec x ∈ headK M Z'`. Introduce `x`. Establish `: H.mulVec x = ∑ j, x j • (fun i => H i j)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.

Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hHK j)`. Establish `hQ1 : ∀ x, (Submodule.Quotient.mk (l.mulVec x) : M.Cok Z') = φ.1 (Submodule.Quotient.mk x)`. Introduce `x`. Rewrite using `[hl, Matrix.add_mulVec, Submodule.Quotient.mk_add, hK1 _ (hHx x), add_zero, hP1]`.

Establish `hQ2 : ∀ x, mu M Z' (l.mulVec x) = mu M Z x`. Introduce `x`. Rewrite using `[hl, Matrix.add_mulVec, mu_add, hK2 _ (hHx x), add_zero, hP2]`. Establish `hle : ∀ i, l i (Fin.last m) = if i = Fin.last m then 1 else 0`. Introduce `i`.

Rewrite using `[hl, Matrix.add_apply, hl₁e, hHl, add_zero]`. Establish `hcolρ : ∀ j, ∃ x, Z'.Z.mulVec x = l.mulVec (Z.Z.mulVec (Pi.single j 1))`. Introduce `j`. Establish `h0 : (Submodule.Quotient.mk (l.mulVec (Z.Z.mulVec (Pi.single j 1))) : M.Cok Z') = 0`. Rewrite using `[hQ1, hmkZ, map_zero]`.

Conclude with `(Submodule.Quotient.mk_eq_zero _).1 h0`. Use `choose xs hxs using hcolρ`. Use `set ρ₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) M.R := Matrix.of fun i j => xs j i with hρ₀`. Establish `hZρ : Z'.Z * ρ₀ = l * Z.Z`. Use extensionality with `i j`.

Establish `h1 : (Z'.Z * ρ₀) i j = (Z'.Z.mulVec (xs j)) i`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, hρ₀]`. Establish `h2 : (l * Z.Z) i j = (l.mulVec (Z.Z.mulVec (Pi.single j 1))) i`. Rewrite using `[Matrix.mulVec_mulVec]`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.

Rewrite using `[h1, h2, hxs j]`. Establish `hρl : ∀ j, ρ₀ (Fin.last m) j = if j = Fin.last m then 1 else 0`. Introduce `j`. Use `hQ2 (Z.Z.mulVec (Pi.single j 1))` as an intermediate fact. Rewrite `this` using `[← hxs j, mu_Z, mu_Z]`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [hρ₀, Matrix.of_apply]`. Rewrite using `[this]`. Distinguish the cases in `h : j = Fin.last m`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h, Ne.symm h]`. Establish `hlu : IsUnit (l.det)` using `hdet`. Establish `honto : ∀ x, ∃ y, ρ₀.mulVec y = x`. Introduce `x`.

Use `set u := l⁻¹.mulVec (Z'.Z.mulVec x) with hu`. Establish `hlu' : l.mulVec u = Z'.Z.mulVec x`. Rewrite using `[hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hlu, Matrix.one_mulVec]`. Establish `hmu : (Submodule.Quotient.mk u : M.Cok Z) = 0`. Establish `h1` using `hQ1 u`.

Rewrite `h1` using `[hlu', hmkZ']`. Conclude with `(φ.1.map_eq_zero_iff).1 h1.symm`. Take `⟨y, hy⟩` from `(Submodule.Quotient.mk_eq_zero _).1 hmu`. Simplify using `only [Matrix.mulVecLin_apply] at hy`. Use `⟨y, mulVec_inj M Z' ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_mulVec, hZρ, ← Matrix.mulVec_mulVec, hy, hlu']`. Use `choose ys hys using fun i : Fin (m + 1) => honto (Pi.single i 1)`. Establish `hright : ρ₀ * (Matrix.of fun i j => ys j i) = 1`. Use extensionality with `i j`. Use `congrFun (hys j) i` as an intermediate fact.

Simplify using `only [Matrix.mulVec, dotProduct] at this`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[this, Matrix.one_apply, Pi.single_apply]`. Establish `hρu : IsUnit ρ₀.det`.

Use `congrArg Matrix.det hright` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `isUnit_iff_exists_inv.2 ⟨_, this⟩`. Use `⟨l, ρ₀⁻¹, hlu, (Matrix.isUnit_nonsing_inv_det_iff).2 hρu, hle, fun j => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Matrix.vecMul e ρ₀ = e`.

Use function extensionality and compare the values at `j`. Simplify using `only [Matrix.vecMul, dotProduct, he, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[hρl]`. Establish `h2 : Matrix.vecMul e ρ₀⁻¹ = e` using `by conv_lhs => rw [← h1]`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hρu, Matrix.vecMul_one]`.

Use `congrFun h2 j` as an intermediate fact. Simplify using `only [Matrix.vecMul, dotProduct, he, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`. Rewrite using `[this]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem liftOrb_of (hSR : SRLift) : LiftOrb := by
  intro F _ _ _ E _ _ _ _ M hOK m Z Z' ⟨φ⟩ hκ
  classical
  set e : Fin (m + 1) → M.R := Pi.single (Fin.last m) 1 with he
  have hmkZ : ∀ x : Fin (m + 1) → M.R, (Submodule.Quotient.mk (Z.Z.mulVec x) : M.Cok Z) = 0 :=
    fun x => (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hmkZ' : ∀ x : Fin (m + 1) → M.R, (Submodule.Quotient.mk (Z'.Z.mulVec x) : M.Cok Z') = 0 :=
    fun x => (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩

  have hcol : ∀ j : Fin (m + 1), ∃ w : Fin (m + 1) → M.R,
      (Submodule.Quotient.mk w : M.Cok Z') = φ.1 (Submodule.Quotient.mk (Pi.single j 1)) ∧
      mu M Z' w = mu M Z (Pi.single j 1) ∧ (j = Fin.last m → w = e) := by
    intro j
    by_cases hj : j = Fin.last m
    · subst hj
      refine ⟨e, φ.2.1.symm, ?_, fun _ => rfl⟩
      rw [he, mu_e, mu_e, hκ]
    · obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (φ.1 (Submodule.Quotient.mk (Pi.single j 1)))
      have hl := φ.2.2 (Submodule.Quotient.mk (Pi.single j 1))
      rw [← hv, lam_mk, lam_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hl
      obtain ⟨t, ht⟩ := hl
      refine ⟨v - Z'.Z.mulVec (t • e), ?_, ?_, fun h => absurd h hj⟩
      · rw [Submodule.Quotient.mk_sub, hmkZ', sub_zero, hv]
      · have ht' : ((t : M.R) : E) = mu M Z' v - mu M Z (Pi.single j 1) := ht
        rw [sub_eq_add_neg, ← Matrix.mulVec_neg, mu_add, mu_Z]
        simp only [Pi.neg_apply, Pi.smul_apply, he, Pi.single_eq_same, smul_eq_mul, mul_one, NegMemClass.coe_neg]
        rw [ht']
        ring
  choose w hw1 hw2 hw3 using hcol
  set l₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) M.R := Matrix.of fun i j => w j i with hl₁
  have hl₁v : ∀ x, l₁.mulVec x = ∑ j, x j • w j := by
    intro x; funext i
    simp [hl₁, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hx : ∀ x : Fin (m + 1) → M.R, ∑ j, x j • (Pi.single j 1 : Fin (m + 1) → M.R) = x := by
    intro x; funext i; simp [Finset.sum_apply, Pi.single_apply]
  have hP1 : ∀ x, (Submodule.Quotient.mk (l₁.mulVec x) : M.Cok Z') = φ.1 (Submodule.Quotient.mk x) := by
    intro x
    conv_rhs => rw [← hx x]
    rw [hl₁v]
    have e1 : (Submodule.Quotient.mk (∑ j, x j • w j) : M.Cok Z') =
        ∑ j, x j • (Submodule.Quotient.mk (w j) : M.Cok Z') := by
      rw [← Submodule.mkQ_apply, map_sum]; simp
    have e2 : (Submodule.Quotient.mk (∑ j, x j • (Pi.single j 1 : Fin (m + 1) → M.R)) : M.Cok Z) =
        ∑ j, x j • (Submodule.Quotient.mk (Pi.single j 1) : M.Cok Z) := by
      rw [← Submodule.mkQ_apply, map_sum]; simp
    rw [e1, e2, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hw1 j]
  have hP2 : ∀ x, mu M Z' (l₁.mulVec x) = mu M Z x := by
    intro x
    conv_rhs => rw [← hx x]
    rw [hl₁v, mu_sum, mu_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mu_smul, mu_smul, hw2 j]
  have hl₁e : ∀ i, l₁ i (Fin.last m) = if i = Fin.last m then 1 else 0 := by
    intro i
    simp only [hl₁, Matrix.of_apply, hw3 _ rfl, he, Pi.single_apply]

  have hK1 : ∀ y ∈ headK M Z', (Submodule.Quotient.mk y : M.Cok Z') = 0 := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := (mem_headK M Z').1 hy
    exact hmkZ' x
  have hK2 : ∀ y ∈ headK M Z', mu M Z' y = 0 := by
    intro y hy
    obtain ⟨x, hx0, rfl⟩ := (mem_headK M Z').1 hy
    rw [mu_Z, hx0]; simp

  have hb : ∃ y₀, Z'.Z.mulVec y₀ = l₁.mulVec (Z.Z.mulVec e) ∧ y₀ (Fin.last m) = 1 := by
    have h0 : (Submodule.Quotient.mk (l₁.mulVec (Z.Z.mulVec e)) : M.Cok Z') = 0 := by
      rw [hP1, hmkZ, map_zero]
    obtain ⟨y₀, hy₀⟩ := (Submodule.Quotient.mk_eq_zero _).1 h0
    have hy₀' : Z'.Z.mulVec y₀ = l₁.mulVec (Z.Z.mulVec e) := hy₀
    refine ⟨y₀, hy₀', ?_⟩
    have := hP2 (Z.Z.mulVec e)
    rw [← hy₀', mu_Z, mu_Z, he, Pi.single_eq_same] at this
    exact Subtype.ext (by simpa using this)
  obtain ⟨y₀, hy₀, hy₀l⟩ := hb
  have hspan : ∀ v : Fin (m + 1) → M.R, ∃ x, v - l₁.mulVec x ∈ headK M Z' := by
    intro v
    obtain ⟨x₀, hx₀⟩ := Submodule.Quotient.mk_surjective _ (φ.1.symm (Submodule.Quotient.mk v))
    have h1 : (Submodule.Quotient.mk (v - l₁.mulVec x₀) : M.Cok Z') = 0 := by
      rw [Submodule.Quotient.mk_sub, hP1, hx₀, LinearEquiv.apply_symm_apply, sub_self]
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).1 h1
    simp only [Matrix.mulVecLin_apply] at hy
    refine ⟨x₀ + y (Fin.last m) • Z.Z.mulVec e, (mem_headK M Z').2 ⟨y - y (Fin.last m) • y₀, ?_, ?_⟩⟩
    · simp [hy₀l]
    · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hy₀, hy, Matrix.mulVec_add, Matrix.mulVec_smul]
      abel
  obtain ⟨H, hHK, hHl, hdet⟩ := hSR M hOK m l₁ (headK M Z') hl₁e hspan
  set l := l₁ + H with hl
  have hHx : ∀ x, H.mulVec x ∈ headK M Z' := by
    intro x
    have : H.mulVec x = ∑ j, x j • (fun i => H i j) := by
      funext i; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hHK j)
  have hQ1 : ∀ x, (Submodule.Quotient.mk (l.mulVec x) : M.Cok Z') = φ.1 (Submodule.Quotient.mk x) := by
    intro x
    rw [hl, Matrix.add_mulVec, Submodule.Quotient.mk_add, hK1 _ (hHx x), add_zero, hP1]
  have hQ2 : ∀ x, mu M Z' (l.mulVec x) = mu M Z x := by
    intro x
    rw [hl, Matrix.add_mulVec, mu_add, hK2 _ (hHx x), add_zero, hP2]
  have hle : ∀ i, l i (Fin.last m) = if i = Fin.last m then 1 else 0 := by
    intro i; rw [hl, Matrix.add_apply, hl₁e, hHl, add_zero]

  have hcolρ : ∀ j, ∃ x, Z'.Z.mulVec x = l.mulVec (Z.Z.mulVec (Pi.single j 1)) := by
    intro j
    have h0 : (Submodule.Quotient.mk (l.mulVec (Z.Z.mulVec (Pi.single j 1))) : M.Cok Z') = 0 := by
      rw [hQ1, hmkZ, map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).1 h0
  choose xs hxs using hcolρ
  set ρ₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) M.R := Matrix.of fun i j => xs j i with hρ₀
  have hZρ : Z'.Z * ρ₀ = l * Z.Z := by
    ext i j
    have h1 : (Z'.Z * ρ₀) i j = (Z'.Z.mulVec (xs j)) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hρ₀]
    have h2 : (l * Z.Z) i j = (l.mulVec (Z.Z.mulVec (Pi.single j 1))) i := by
      rw [Matrix.mulVec_mulVec]; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h1, h2, hxs j]
  have hρl : ∀ j, ρ₀ (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
    intro j
    have := hQ2 (Z.Z.mulVec (Pi.single j 1))
    rw [← hxs j, mu_Z, mu_Z] at this
    apply Subtype.ext
    simp only [hρ₀, Matrix.of_apply]
    rw [this]
    by_cases h : j = Fin.last m
    · subst h; simp
    · simp [Pi.single_apply, h, Ne.symm h]

  have hlu : IsUnit (l.det) := hdet
  have honto : ∀ x, ∃ y, ρ₀.mulVec y = x := by
    intro x
    set u := l⁻¹.mulVec (Z'.Z.mulVec x) with hu
    have hlu' : l.mulVec u = Z'.Z.mulVec x := by
      rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hlu, Matrix.one_mulVec]
    have hmu : (Submodule.Quotient.mk u : M.Cok Z) = 0 := by
      have h1 := hQ1 u
      rw [hlu', hmkZ'] at h1
      exact (φ.1.map_eq_zero_iff).1 h1.symm
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).1 hmu
    simp only [Matrix.mulVecLin_apply] at hy
    refine ⟨y, mulVec_inj M Z' ?_⟩
    rw [Matrix.mulVec_mulVec, hZρ, ← Matrix.mulVec_mulVec, hy, hlu']
  choose ys hys using fun i : Fin (m + 1) => honto (Pi.single i 1)
  have hright : ρ₀ * (Matrix.of fun i j => ys j i) = 1 := by
    ext i j
    have := congrFun (hys j) i
    simp only [Matrix.mulVec, dotProduct] at this
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [this, Matrix.one_apply, Pi.single_apply]
  have hρu : IsUnit ρ₀.det := by
    have := congrArg Matrix.det hright
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_iff_exists_inv.2 ⟨_, this⟩
  refine ⟨l, ρ₀⁻¹, hlu, (Matrix.isUnit_nonsing_inv_det_iff).2 hρu, hle, fun j => ?_, ?_⟩
  · have h1 : Matrix.vecMul e ρ₀ = e := by
      funext j
      simp only [Matrix.vecMul, dotProduct, he, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      rw [hρl]
    have h2 : Matrix.vecMul e ρ₀⁻¹ = e := by
      conv_lhs => rw [← h1]
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hρu, Matrix.vecMul_one]
    have := congrFun h2 j
    simp only [Matrix.vecMul, dotProduct, he, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at this
    rw [this]
  · calc Z'.Z = Z'.Z * ρ₀ * ρ₀⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hρu, Matrix.mul_one]
      _ = l * Z.Z * ρ₀⁻¹ := by rw [hZρ]

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
