import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacLocOfHpk
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix
open scoped ComplexOrder

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

section Lin

variable {n : ℕ} (ε : Fin n → Bool)

/- English proof (translation)
Set `A : Matrix (Fin n) ι ℂ` to `Matrix.of fun p i => u i p`. Establish `hA : ∀ c : ι → ℂ, A *ᵥ c = ∑ i, c i • u i`. Introduce `c`. Use extensionality with `p`. Simplify using `only [A, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.

Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Establish `hinj : Function.Injective A.mulVec`. Introduce `c d hcd`. Establish `h0 : ∑ i, (c - d) i • u i = 0`. Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]`.

Rewrite using `[← hA, ← hA]`. Conclude with `sub_eq_zero.2 hcd`. Use function extensionality and compare the values at `i`. Conclude with `sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hu _ h0 i)`. Establish `hpd` using `Matrix.PosDef.conjTranspose_mul_self A hinj`.

Establish `hdet : IsUnit (Aᴴ * A).det` using `(Matrix.isUnit_iff_isUnit_det _).1 hpd.isUnit`. Use `⟨Formalism.REAL.Jm ε *ᵥ (A *ᵥ ((Aᴴ * A)⁻¹ *ᵥ t)), fun i => ?_⟩` and prove the remaining obligations. Establish `key : ∀ w : Fin n → ℂ, star (u i) ⬝ᵥ w = (Aᴴ *ᵥ w) i`. Introduce `w`. Simplify using `only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, A, Matrix.of_apply, Pi.star_apply]`.

Unfold `hJ`. Rewrite using `[Matrix.mulVec_mulVec, Formalism.REAL.Jm_mul_self, Matrix.one_mulVec, key, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]`.
-/
theorem exists_dualVec {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → ℂ) (hu : LinearIndependent ℂ u)
    (t : ι → ℂ) : ∃ v, ∀ i, hJ ε (u i) v = t i := by
  let A : Matrix (Fin n) ι ℂ := Matrix.of fun p i => u i p
  have hA : ∀ c : ι → ℂ, A *ᵥ c = ∑ i, c i • u i := by
    intro c
    ext p
    simp only [A, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hinj : Function.Injective A.mulVec := by
    intro c d hcd
    have h0 : ∑ i, (c - d) i • u i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      rw [← hA, ← hA]
      exact sub_eq_zero.2 hcd
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hu _ h0 i)
  have hpd := Matrix.PosDef.conjTranspose_mul_self A hinj
  have hdet : IsUnit (Aᴴ * A).det := (Matrix.isUnit_iff_isUnit_det _).1 hpd.isUnit
  refine ⟨Formalism.REAL.Jm ε *ᵥ (A *ᵥ ((Aᴴ * A)⁻¹ *ᵥ t)), fun i => ?_⟩
  have key : ∀ w : Fin n → ℂ, star (u i) ⬝ᵥ w = (Aᴴ *ᵥ w) i := by
    intro w
    simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, A, Matrix.of_apply, Pi.star_apply]
  unfold hJ
  rw [Matrix.mulVec_mulVec, Formalism.REAL.Jm_mul_self, Matrix.one_mulVec, key, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/- English proof (translation)
Use `set g : Fin r → Fin n → ℂ := fun b => f b - ∑ c, ((1 / 2 : ℂ) * hJ ε (f c) (f b)) • e c with hg`. Establish `hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0`. Introduce `a b`. Rewrite using `[UnitaryIsometries.hJ_conj, hef]`. Apply the tactic sequence `split_ifs <;> simp`.

Use `⟨g, fun a b => ?_, fun a b => ?_, fun a => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hg]`. Simplify using `only [UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, hee, mul_zero, Finset.sum_const_zero, sub_zero, hef]`. Rewrite using `[hg]`. Simplify using `only [UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_sum_right, UnitaryIsometries.hJ_sum_left, hee, hfe, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, UnitaryIsome …`.

Simplify using `only [hef, ite_mul, zero_mul, one_mul, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul]`. Rewrite using `[← UnitaryIsometries.hJ_conj ε (f a) (f b)]`. Simplify using `only [map_div₀, map_one, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hg]`.

Simplify using `only [UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_sum_left, hez, mul_zero, Finset.sum_const_zero, sub_zero]`. Rewrite using `[UnitaryIsometries.hJ_conj, hfz, map_zero]`. Rewrite using `[hg]`. Simplify using `only [UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_sum_left, hez'', mul_zero, Finset.sum_const_zero, sub_zero]`. Rewrite using `[UnitaryIsometries.hJ_conj, hfz'', map_zero]`.
-/
theorem goodPos_of_dual {r : ℕ} (e f : Fin r → Fin n → ℂ) (z z'' : Fin n → ℂ) (hee : ∀ a b, hJ ε (e a) (e b) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hez'' : ∀ a, hJ ε (e a) z'' = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) (hfz : ∀ b, hJ ε z (f b) = 0)
    (hfz'' : ∀ b, hJ ε z'' (f b) = 0) : GoodPos ε e z z'' := by
  set g : Fin r → Fin n → ℂ := fun b => f b - ∑ c, ((1 / 2 : ℂ) * hJ ε (f c) (f b)) • e c with hg
  have hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0 := by
    intro a b
    rw [UnitaryIsometries.hJ_conj, hef]
    split_ifs <;> simp
  refine ⟨g, fun a b => ?_, fun a b => ?_, fun a => ⟨?_, ?_⟩⟩
  · rw [hg]
    simp only [UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, hee, mul_zero, Finset.sum_const_zero, sub_zero, hef]
  · rw [hg]
    simp only [UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_sum_right, UnitaryIsometries.hJ_sum_left, hee, hfe, mul_zero,
      Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, UnitaryIsometries.hJ_sum_left]
    simp only [hef, ite_mul, zero_mul, one_mul, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, map_mul]
    rw [← UnitaryIsometries.hJ_conj ε (f a) (f b)]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  · rw [hg]
    simp only [UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_sum_left, hez, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [UnitaryIsometries.hJ_conj, hfz, map_zero]
  · rw [hg]
    simp only [UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_sum_left, hez'', mul_zero, Finset.sum_const_zero, sub_zero]
    rw [UnitaryIsometries.hJ_conj, hfz'', map_zero]

def eiL (x v : Fin n → ℂ) (q : ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun w := w + hJ ε x w • v - (hJ ε v w + q * hJ ε x w) • x
  map_add' w w' := by
    simp only [UnitaryIsometries.hJ_add_right, mul_add, add_smul]
    abel
  map_smul' a w := by
    simp only [UnitaryIsometries.hJ_smul_right, RingHom.id_apply, smul_sub, smul_add, smul_smul]
    congr 2
    ring_nf

def ei (x v : Fin n → ℂ) (q : ℂ) : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (eiL ε x v q)

/- English proof (translation)
Rewrite using `[ei, LinearMap.toMatrix'_mulVec]`. Both sides reduce to the same expression.
-/
theorem ei_apply (x v : Fin n → ℂ) (q : ℂ) (w : Fin n → ℂ) :
    ei ε x v q *ᵥ w = w + hJ ε x w • v - (hJ ε v w + q * hJ ε x w) • x := by
  rw [ei, LinearMap.toMatrix'_mulVec]
  rfl

/- English proof (translation)
Introduce `w w'`. Establish `hvx : hJ ε v x = 0` using `by rw [UnitaryIsometries.hJ_conj, hxv, map_zero]`. Rewrite using `[ei_apply, ei_apply]`. Simplify using `only [UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_smul_right, map_add, map_mul, hxx, hxv, hvx]`. Rewrite using `[UnitaryIsometries.hJ_conj ε w v, UnitaryIsometries.hJ_conj ε w x]`.

Take the linear combination `(-(conj (hJ ε x w) * hJ ε x w')) * hq`.
-/
theorem ei_isIsom (x v : Fin n → ℂ) (q : ℂ) (hxx : hJ ε x x = 0) (hxv : hJ ε x v = 0)
    (hq : q + conj q = hJ ε v v) : UnitaryIsometries.IsIsom ε (ei ε x v q) := by
  intro w w'
  have hvx : hJ ε v x = 0 := by rw [UnitaryIsometries.hJ_conj, hxv, map_zero]
  rw [ei_apply, ei_apply]
  simp only [UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_sub_right,
    UnitaryIsometries.hJ_smul_right, map_add, map_mul, hxx, hxv, hvx]
  rw [UnitaryIsometries.hJ_conj ε w v, UnitaryIsometries.hJ_conj ε w x]
  linear_combination (-(conj (hJ ε x w) * hJ ε x w')) * hq

end Lin

section Frame

variable {n r k : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T T' : ℝ}

/- English proof (translation)
Rewrite using `[UnitaryIsometries.hJ_sum_left]`. Simplify using `[h]`.
-/
theorem hJ_comb_left (d : Fin r → ℂ) (y : Fin n → ℂ) (h : ∀ a, hJ ε (e a) y = 0) :
    hJ ε (∑ a, d a • e a) y = 0 := by
  rw [UnitaryIsometries.hJ_sum_left]
  simp [h]

/- English proof (translation)
Rewrite using `[UnitaryIsometries.hJ_sum_right]`. Simplify using `[h]`.
-/
theorem hJ_comb_right (d : Fin r → ℂ) (y : Fin n → ℂ) (h : ∀ a, hJ ε y (e a) = 0) :
    hJ ε y (∑ a, d a • e a) = 0 := by
  rw [UnitaryIsometries.hJ_sum_right]
  simp [h]

/- English proof (translation)
Introduce `hz`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 hz`. Establish `h0 : hJ ε z z = hJ ε (∑ a, c a • e a) z` using `by rw [hc]`. Establish `h1 : (-(T : ℂ)) = 0` using `by rw [← hF.zz, h0, hJ_comb_left c z hF.ez]`. Conclude with `hF.T_pos.ne' (Complex.ofReal_eq_zero.1 (neg_eq_zero.1 h1))`.
-/
theorem z_not_mem_span (hF : FrameLoc ε k e z z' T T') : z ∉ Submodule.span ℂ (Set.range e) := by
  intro hz
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hz
  have h0 : hJ ε z z = hJ ε (∑ a, c a • e a) z := by rw [hc]
  have h1 : (-(T : ℂ)) = 0 := by rw [← hF.zz, h0, hJ_comb_left c z hF.ez]
  exact hF.T_pos.ne' (Complex.ofReal_eq_zero.1 (neg_eq_zero.1 h1))

/- English proof (translation)
Establish `hLI : LinearIndependent ℂ (fam e z)`. Unfold `fam`. Conclude with `linearIndependent_finSnoc.2 ⟨hF.e_li, z_not_mem_span hF⟩`. Distinguish the cases in `hc : z' ∈ Submodule.span ℂ (Set.range (fam e z))`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 hc`.

Use `⟨fun a => -c (Fin.castSucc a), ?_⟩` and prove the remaining obligations. Establish `hz'' : z' + ∑ a, (-c (Fin.castSucc a)) • e a = c (Fin.last r) • z`. Rewrite using `[← hc, Fin.sum_univ_castSucc]`. Simplify using `only [fam, Fin.snoc_castSucc, Fin.snoc_last, neg_smul, Finset.sum_neg_distrib]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hz'']`. Establish `hd` using `fun b : Fin r => exists_dualVec ε (fam e z) hLI (fun i => if i = Fin.castSucc b then 1 else 0)`. Use `choose f hf using hd`. Use `goodPos_of_dual ε e f z _ hF.ee hF.ez (fun a => ?_) (fun a b => ?_) (fun b => ?_) (fun b => ?_)` and prove the remaining obligations. Rewrite using `[UnitaryIsometries.hJ_smul_right, hF.ez, mul_zero]`.

Establish `h1` using `hf b (Fin.castSucc a)`. Simplify using `only [fam, Fin.snoc_castSucc] at h1`. Rewrite using `[h1]`. Simplify using `only [Fin.castSucc_inj]`. Establish `h1` using `hf b (Fin.last r)`.

Simplify using `only [fam, Fin.snoc_last] at h1`. Rewrite using `[h1, if_neg (Fin.castSucc_lt_last b).ne']`. Establish `h1` using `hf b (Fin.last r)`. Simplify using `only [fam, Fin.snoc_last] at h1`. Rewrite using `[UnitaryIsometries.hJ_smul_left, h1, if_neg (Fin.castSucc_lt_last b).ne', mul_zero]`.

Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]`. Establish `hLI2 : LinearIndependent ℂ (Fin.snoc (α` using `fun _ => Fin n → ℂ) (fam e z) z') := linearIndependent_finSnoc.2 ⟨hLI, hc⟩`. Establish `hd` using `fun b : Fin r => exists_dualVec ε (Fin.snoc (α := fun _ => Fin n → ℂ) (fam e z) z') hLI2 (fun i => if i = Fin.castSucc (Fin.castSucc b) then 1 else 0)`. Use `choose f hf using hd`.

Use `goodPos_of_dual ε e f z z' hF.ee hF.ez hF.ez' (fun a b => ?_) (fun b => ?_) (fun b => ?_)` and prove the remaining obligations. Establish `h1` using `hf b (Fin.castSucc (Fin.castSucc a))`. Simplify using `only [fam, Fin.snoc_castSucc] at h1`. Rewrite using `[h1]`. Simplify using `only [Fin.castSucc_inj]`.

Establish `h1` using `hf b (Fin.castSucc (Fin.last r))`. Simplify using `only [fam, Fin.snoc_castSucc, Fin.snoc_last] at h1`. Rewrite using `[h1, if_neg]`. Introduce `h`. Conclude with `(Fin.castSucc_lt_last b).ne' (Fin.castSucc_injective _ h)`.

Establish `h1` using `hf b (Fin.last (r + 1))`. Simplify using `only [Fin.snoc_last] at h1`. Rewrite using `[h1, if_neg (Fin.castSucc_lt_last _).ne']`.
-/
theorem goodPos_shift (hF : FrameLoc ε k e z z' T T') :
    ∃ d : Fin r → ℂ, GoodPos ε e z (z' + ∑ a, d a • e a) := by
  have hLI : LinearIndependent ℂ (fam e z) := by
    unfold fam
    exact linearIndependent_finSnoc.2 ⟨hF.e_li, z_not_mem_span hF⟩
  by_cases hc : z' ∈ Submodule.span ℂ (Set.range (fam e z))
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hc
    refine ⟨fun a => -c (Fin.castSucc a), ?_⟩
    have hz'' : z' + ∑ a, (-c (Fin.castSucc a)) • e a = c (Fin.last r) • z := by
      rw [← hc, Fin.sum_univ_castSucc]
      simp only [fam, Fin.snoc_castSucc, Fin.snoc_last, neg_smul, Finset.sum_neg_distrib]
      abel
    rw [hz'']
    have hd := fun b : Fin r => exists_dualVec ε (fam e z) hLI (fun i => if i = Fin.castSucc b then 1 else 0)
    choose f hf using hd
    refine goodPos_of_dual ε e f z _ hF.ee hF.ez (fun a => ?_) (fun a b => ?_) (fun b => ?_) (fun b => ?_)
    · rw [UnitaryIsometries.hJ_smul_right, hF.ez, mul_zero]
    · have h1 := hf b (Fin.castSucc a)
      simp only [fam, Fin.snoc_castSucc] at h1
      rw [h1]
      simp only [Fin.castSucc_inj]
    · have h1 := hf b (Fin.last r)
      simp only [fam, Fin.snoc_last] at h1
      rw [h1, if_neg (Fin.castSucc_lt_last b).ne']
    · have h1 := hf b (Fin.last r)
      simp only [fam, Fin.snoc_last] at h1
      rw [UnitaryIsometries.hJ_smul_left, h1, if_neg (Fin.castSucc_lt_last b).ne', mul_zero]
  · refine ⟨0, ?_⟩
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    have hLI2 : LinearIndependent ℂ (Fin.snoc (α := fun _ => Fin n → ℂ) (fam e z) z') :=
      linearIndependent_finSnoc.2 ⟨hLI, hc⟩
    have hd := fun b : Fin r => exists_dualVec ε (Fin.snoc (α := fun _ => Fin n → ℂ) (fam e z) z') hLI2
      (fun i => if i = Fin.castSucc (Fin.castSucc b) then 1 else 0)
    choose f hf using hd
    refine goodPos_of_dual ε e f z z' hF.ee hF.ez hF.ez' (fun a b => ?_) (fun b => ?_) (fun b => ?_)
    · have h1 := hf b (Fin.castSucc (Fin.castSucc a))
      simp only [fam, Fin.snoc_castSucc] at h1
      rw [h1]
      simp only [Fin.castSucc_inj]
    · have h1 := hf b (Fin.castSucc (Fin.last r))
      simp only [fam, Fin.snoc_castSucc, Fin.snoc_last] at h1
      rw [h1, if_neg]
      intro h
      exact (Fin.castSucc_lt_last b).ne' (Fin.castSucc_injective _ h)
    · have h1 := hf b (Fin.last (r + 1))
      simp only [Fin.snoc_last] at h1
      rw [h1, if_neg (Fin.castSucc_lt_last _).ne']

/- English proof (translation)
Establish `hz'e : ∀ a, hJ ε z' (e a) = 0` using `fun a => by rw [UnitaryIsometries.hJ_conj, hF.ez', map_zero]`. Use `exact`. Use the proof step `{ dim := hF.dim, k_pos := hF.k_pos, sig := hF.sig, e_li := hF.e_li, ee := hF.ee, ez := hF.ez, ez' := fun a => by rw [UnitaryIsometries.hJ_add_right, hF.ez', hJ_comb_right d _ (fun b => hF.ee a b), add_zero], zz := hF.zz, zz' := by`. Rewrite using `[UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_add_right, hF.zz', hJ_comb_right d _ hz'e, hJ_comb_left d _ hF.ez', hJ_comb_left d _ (fun b => hJ_comb_right d _ (fun a => hF.ee b a))]`. Use the proof step `simp,`.

Use `T_pos := hF.T_pos, T'_pos := hF.T'_pos }`.
-/
theorem frameLoc_shift (hF : FrameLoc ε k e z z' T T') (d : Fin r → ℂ) :
    FrameLoc ε k e z (z' + ∑ a, d a • e a) T T' := by
  have hz'e : ∀ a, hJ ε z' (e a) = 0 := fun a => by rw [UnitaryIsometries.hJ_conj, hF.ez', map_zero]
  exact
  { dim := hF.dim, k_pos := hF.k_pos, sig := hF.sig, e_li := hF.e_li, ee := hF.ee, ez := hF.ez,
    ez' := fun a => by rw [UnitaryIsometries.hJ_add_right, hF.ez', hJ_comb_right d _ (fun b => hF.ee a b), add_zero],
    zz := hF.zz,
    zz' := by
      rw [UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_add_right, hF.zz', hJ_comb_right d _ hz'e,
        hJ_comb_left d _ hF.ez', hJ_comb_left d _ (fun b => hJ_comb_right d _ (fun a => hF.ee b a))]
      simp,
    T_pos := hF.T_pos, T'_pos := hF.T'_pos }

/- English proof (translation)
Use `set x := ∑ a, d a • e a with hx`. Use `set v : Fin n → ℂ := ((1 / T' : ℝ) : ℂ) • z' with hv`. Use `set q : ℂ := ((-(1 / (2 * T')) : ℝ) : ℂ) with hqd`. Establish `hxe : ∀ a, hJ ε x (e a) = 0` using `fun a => hJ_comb_left d _ (fun b => hF.ee b a)`. Establish `hxz' : hJ ε x z' = 0` using `hJ_comb_left d _ hF.ez'`.

Establish `hxx : hJ ε x x = 0` using `hJ_comb_left d _ (fun b => hJ_comb_right d _ (fun a => hF.ee b a))`. Establish `hxv : hJ ε x v = 0` using `by rw [hv, UnitaryIsometries.hJ_smul_right, hxz', mul_zero]`. Establish `hvx : hJ ε v x = 0` using `by rw [UnitaryIsometries.hJ_conj, hxv, map_zero]`. Establish `hve : ∀ a, hJ ε v (e a) = 0` using `fun a => by`. Rewrite using `[UnitaryIsometries.hJ_conj, hv, UnitaryIsometries.hJ_smul_right, hF.ez', mul_zero, map_zero]`.

Establish `hT' : (T' : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hF.T'_pos.ne'`. Establish `hvz' : hJ ε v z' = -1`. Rewrite using `[hv, UnitaryIsometries.hJ_smul_left, Complex.conj_ofReal, hF.zz']`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Establish `hq : q + conj q = hJ ε v v`. Rewrite using `[hqd, hv, Complex.conj_ofReal, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, Complex.conj_ofReal, hF.zz']`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hI` using `ei_isIsom ε x v q hxx hxv hq`. Apply the tactic sequence `refine ⟨UnitaryIsometries.toUJ ε hI, fun a => ?_, ?_, ?_⟩ <;> rw [UnitaryIsometries.uMat_toUJ, ei_apply]`. Rewrite using `[hxe, hve]`. Simplify using the standard rewrite rules. Rewrite using `[hxz', hvz']`.

Simplify using the standard rewrite rules. Rewrite using `[hxx, hvx]`. Simplify using the standard rewrite rules.
-/
theorem exists_pow_mul_pred_ge (hF : FrameLoc ε k e z z' T T') (d : Fin r → ℂ) :
    ∃ n0 : Formalism.REAL.UJ ε, (∀ a, uMat n0 *ᵥ e a = e a) ∧ uMat n0 *ᵥ z' = z' + ∑ a, d a • e a ∧
      uMat n0 *ᵥ (∑ a, d a • e a) = ∑ a, d a • e a := by
  set x := ∑ a, d a • e a with hx
  set v : Fin n → ℂ := ((1 / T' : ℝ) : ℂ) • z' with hv
  set q : ℂ := ((-(1 / (2 * T')) : ℝ) : ℂ) with hqd
  have hxe : ∀ a, hJ ε x (e a) = 0 := fun a => hJ_comb_left d _ (fun b => hF.ee b a)
  have hxz' : hJ ε x z' = 0 := hJ_comb_left d _ hF.ez'
  have hxx : hJ ε x x = 0 := hJ_comb_left d _ (fun b => hJ_comb_right d _ (fun a => hF.ee b a))
  have hxv : hJ ε x v = 0 := by rw [hv, UnitaryIsometries.hJ_smul_right, hxz', mul_zero]
  have hvx : hJ ε v x = 0 := by rw [UnitaryIsometries.hJ_conj, hxv, map_zero]
  have hve : ∀ a, hJ ε v (e a) = 0 := fun a => by
    rw [UnitaryIsometries.hJ_conj, hv, UnitaryIsometries.hJ_smul_right, hF.ez', mul_zero, map_zero]
  have hT' : (T' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hF.T'_pos.ne'
  have hvz' : hJ ε v z' = -1 := by
    rw [hv, UnitaryIsometries.hJ_smul_left, Complex.conj_ofReal, hF.zz']
    push_cast
    field_simp
  have hq : q + conj q = hJ ε v v := by
    rw [hqd, hv, Complex.conj_ofReal, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, Complex.conj_ofReal, hF.zz']
    push_cast
    field_simp
    ring
  have hI := ei_isIsom ε x v q hxx hxv hq
  refine ⟨UnitaryIsometries.toUJ ε hI, fun a => ?_, ?_, ?_⟩ <;> rw [UnitaryIsometries.uMat_toUJ, ei_apply]
  · rw [hxe, hve]
    simp
  · rw [hxz', hvz']
    simp
  · rw [hxx, hvx]
    simp

/- English proof (translation)
The claim follows from `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, a.2, rfl⟩)`.
-/
theorem comb_mem_spanLt (d : Fin r → ℂ) : ∑ a, d a • e a ∈ spanLt e r :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, a.2, rfl⟩)

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun b _ => b.2)`.
-/
theorem spanLt_le_top (a : ℕ) : spanLt e a ≤ spanLt e r :=
  Submodule.span_mono (Set.image_mono fun b _ => b.2)

/- English proof (translation)
Rewrite using `[Matrix.mulVec_sum]`. Conclude with `Submodule.sum_mem _ fun a _ => by`. Rewrite using `[Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ _ (spanLt_le_top _ (hg a))`.
-/
theorem sub_one_comb (g : Matrix (Fin n) (Fin n) ℂ) (hg : ∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1)
    (d : Fin r → ℂ) : (g - 1) *ᵥ ∑ a, d a • e a ∈ spanLt e r := by
  rw [Matrix.mulVec_sum]
  exact Submodule.sum_mem _ fun a _ => by
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (spanLt_le_top _ (hg a))

/- English proof (translation)
Use extensionality with `g`. Simplify using `only [SLoc, Set.mem_setOf_eq, InS]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Establish `h3` using `Submodule.sub_mem _ h2 (sub_one_comb _ h1 d)`. Rewrite `h3` using `[Matrix.mulVec_add, add_sub_cancel_right]`. Then use the resulting hypothesis. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_add]`.

Conclude with `Submodule.add_mem _ h2 (sub_one_comb _ h1 d)`.
-/
theorem sLoc_shift (d : Fin r → ℂ) : SLoc ε e (z' + ∑ a, d a • e a) = SLoc ε e z' := by
  ext g
  simp only [SLoc, Set.mem_setOf_eq, InS]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h3 := Submodule.sub_mem _ h2 (sub_one_comb _ h1 d)
    rwa [Matrix.mulVec_add, add_sub_cancel_right] at h3
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ h2 (sub_one_comb _ h1 d)

/- English proof (translation)
Consider the cases of `b using Fin.lastCases with`. Consider the case `last => simp only [famSc, fam, Matrix.mulVec_smul, Fin.snoc_last, hz]`. Consider the case `cast a => simp only [famSc, fam, Matrix.mulVec_smul, Fin.snoc_castSucc, he]`.
-/
theorem famSc_shift (g : Formalism.REAL.UJ ε) (z'' : Fin n → ℂ) (he : ∀ a, uMat g *ᵥ e a = e a)
    (hz : uMat g *ᵥ z' = z'') (sc : ℝ) (b : Fin (r + 1)) : uMat g *ᵥ famSc sc e z' b = famSc sc e z'' b := by
  cases b using Fin.lastCases with
  | last => simp only [famSc, fam, Matrix.mulVec_smul, Fin.snoc_last, hz]
  | cast a => simp only [famSc, fam, Matrix.mulVec_smul, Fin.snoc_castSucc, he]

end Frame

/- English proof (translation)
Introduce `hR hG n r k ε e z z' T T' sc hF hsc`. Take `⟨d, hGP⟩` from `goodPos_shift hF`. Establish `hF''` using `frameLoc_shift hF d`. Take `⟨h'', hsec, hJ''⟩` from `hG n r k ε e z (z' + ∑ a, d a • e a) T T' sc hF'' hGP hsc`. Take `⟨n0, hn0e, hn0z, hn0x⟩` from `exists_pow_mul_pred_ge hF d`.

Establish `hinv : ∀ w, uMat n0⁻¹ *ᵥ (uMat n0 *ᵥ w) = w`. Introduce `w`. Rewrite using `[Matrix.mulVec_mulVec, show uMat n0⁻¹ * uMat n0 = 1 by simp [uMat], Matrix.one_mulVec]`. Establish `hn0i : n0⁻¹ ∈ SLoc ε e z'` using `by show InS e z' (uMat n0⁻¹)`. Use `⟨fun a => ?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `hinv (e a)`. Rewrite `h1` using `[hn0e a]`. Rewrite using `[Matrix.sub_mulVec, h1, Matrix.one_mulVec, sub_self]`. Conclude with `Submodule.zero_mem _`. Establish `h1` using `hinv (∑ a, d a • e a)`.

Rewrite `h1` using `[hn0x]`. Establish `h2` using `hinv z'`. Rewrite `h2` using `[hn0z, Matrix.mulVec_add, h1]`. Establish `h3 : uMat n0⁻¹ *ᵥ z' = z' - ∑ a, d a • e a` using `eq_sub_of_add_eq h2`. Rewrite using `[Matrix.sub_mulVec, h3, Matrix.one_mulVec, sub_sub_cancel_left]`.

Conclude with `Submodule.neg_mem _ (comb_mem_spanLt d)`. Establish `hfam : ∀ b, uMat n0 *ᵥ famSc sc e z' b = famSc sc e (z' + ∑ a, d a • e a) b` using `famSc_shift n0 _ hn0e hn0z sc`. Use `⟨fun c => h'' c * n0, fun c hc => ?_, fun μS μS' hS hS' => ?_⟩` and prove the remaining obligations. Rewrite using `[← hsec c hc]`. Use extensionality with `a b`.

Use `show hJ ε _ (uMat (h'' c * n0) *ᵥ _) = hJ ε _ (uMat (h'' c) *ᵥ _)`. Rewrite using `[show uMat (h'' c * n0) = uMat (h'' c) * uMat n0 from rfl, ← Matrix.mulVec_mulVec, hfam b]`. Establish `hS'' : IsHaarS (SLoc ε e (z' + ∑ a, d a • e a)) μS'`. Rewrite using `[sLoc_shift]`. Conclude with `hS'`.

Take `⟨C, hC, hD⟩` from `hJ'' μS μS' hS hS''`. Use `⟨C, hC, fun φ hφ => ?_⟩` and prove the remaining obligations. Rewrite using `[hD φ hφ]`. Use `lintegral_congr (fun c => ?_)` and prove the remaining obligations. Use `congr 1`.

Use `lintegral_congr (fun s => ?_)` and prove the remaining obligations. Establish `hRi` using `hR n r k ε e z' z T' T (frameLoc_swap hF) μS' hS' n0⁻¹ hn0i`. Establish `h1` using `lintegral_mul_right_of_map μS' n0⁻¹ hRi (fun x => φ (s * h'' c * x⁻¹))`. Use `h1.symm.trans (lintegral_congr (fun s' => ?_))` and prove the remaining obligations. Use `congr 1`.

Use `group`.
-/
theorem degRed_holds : DegRed := by
  intro hR hG n r k ε e z z' T T' sc hF hsc
  obtain ⟨d, hGP⟩ := goodPos_shift hF
  have hF'' := frameLoc_shift hF d
  obtain ⟨h'', hsec, hJ''⟩ := hG n r k ε e z (z' + ∑ a, d a • e a) T T' sc hF'' hGP hsc
  obtain ⟨n0, hn0e, hn0z, hn0x⟩ := exists_pow_mul_pred_ge hF d
  have hinv : ∀ w, uMat n0⁻¹ *ᵥ (uMat n0 *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, show uMat n0⁻¹ * uMat n0 = 1 by simp [uMat], Matrix.one_mulVec]
  have hn0i : n0⁻¹ ∈ SLoc ε e z' := by
    show InS e z' (uMat n0⁻¹)
    refine ⟨fun a => ?_, ?_⟩
    · have h1 := hinv (e a)
      rw [hn0e a] at h1
      rw [Matrix.sub_mulVec, h1, Matrix.one_mulVec, sub_self]
      exact Submodule.zero_mem _
    · have h1 := hinv (∑ a, d a • e a)
      rw [hn0x] at h1
      have h2 := hinv z'
      rw [hn0z, Matrix.mulVec_add, h1] at h2
      have h3 : uMat n0⁻¹ *ᵥ z' = z' - ∑ a, d a • e a := eq_sub_of_add_eq h2
      rw [Matrix.sub_mulVec, h3, Matrix.one_mulVec, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (comb_mem_spanLt d)
  have hfam : ∀ b, uMat n0 *ᵥ famSc sc e z' b = famSc sc e (z' + ∑ a, d a • e a) b :=
    famSc_shift n0 _ hn0e hn0z sc
  refine ⟨fun c => h'' c * n0, fun c hc => ?_, fun μS μS' hS hS' => ?_⟩
  · rw [← hsec c hc]
    ext a b
    show hJ ε _ (uMat (h'' c * n0) *ᵥ _) = hJ ε _ (uMat (h'' c) *ᵥ _)
    rw [show uMat (h'' c * n0) = uMat (h'' c) * uMat n0 from rfl, ← Matrix.mulVec_mulVec, hfam b]
  · have hS'' : IsHaarS (SLoc ε e (z' + ∑ a, d a • e a)) μS' := by
      rw [sLoc_shift]
      exact hS'
    obtain ⟨C, hC, hD⟩ := hJ'' μS μS' hS hS''
    refine ⟨C, hC, fun φ hφ => ?_⟩
    rw [hD φ hφ]
    refine lintegral_congr (fun c => ?_)
    congr 1
    refine lintegral_congr (fun s => ?_)
    have hRi := hR n r k ε e z' z T' T (frameLoc_swap hF) μS' hS' n0⁻¹ hn0i
    have h1 := lintegral_mul_right_of_map μS' n0⁻¹ hRi (fun x => φ (s * h'' c * x⁻¹))
    refine h1.symm.trans (lintegral_congr (fun s' => ?_))
    congr 1
    group

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
