import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.FormalDegreeBessel.FinalWR
import Formalism.FormalDegreeBessel.FinalG

open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Qx2

section Triples

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [pbOp, wirtBar, Pi.neg_apply]`. Rewrite using `[fderiv_neg]`. Apply the tactic sequence `split_ifs <;> simp [smul_add, smul_neg, neg_add, add_comm]`.
-/
theorem pbOp_neg (l : Fin m) (f : (Fin m → ℂ) → E) : pbOp l (-f) = -pbOp l f := by
  funext x
  simp only [pbOp, wirtBar, Pi.neg_apply]
  rw [fderiv_neg]
  split_ifs <;> simp [smul_add, smul_neg, neg_add, add_comm]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[cbiOp]`.
-/
theorem cbiOp_neg (l : Fin m) (f : (Fin m → ℂ) → E) : cbiOp l (-f) = -cbiOp l f := by
  funext x
  simp [cbiOp]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[cbiOp, smul_add]`.
-/
theorem cbiOp_add (l : Fin m) (f g : (Fin m → ℂ) → E) : cbiOp l (f + g) = cbiOp l f + cbiOp l g := by
  funext x
  simp [cbiOp, smul_add]

/- English proof (translation)
Establish `h1 : cbiOp l f ∈ WSm m E` using `presOps m E l 5 f hf`. Establish `h2 : pbOp l (cbiOp l f) ∈ WSm m E` using `presOps m E l 3 _ h1`. Take `⟨-, -, -, hA, -, -⟩` from `weylFun m E l f hf`. Take `⟨-, -, -, -, -, hC⟩` from `weylFun m E l _ h1`. Take `⟨-, -, -, -, hB, -⟩` from `weylFun m E l _ h2`.

Rewrite `hC` using `[hA]`. Rewrite using `[hC, cbiOp_add, hB]`. Normalize the expressions using the abelian group laws.
-/
theorem pb_cbi (l : Fin m) {f : (Fin m → ℂ) → E} (hf : f ∈ WSm m E) :
    pbOp l (cbiOp l f) = cbiOp l (pbOp l f) - cbiOp l f := by
  have h1 : cbiOp l f ∈ WSm m E := presOps m E l 5 f hf
  have h2 : pbOp l (cbiOp l f) ∈ WSm m E := presOps m E l 3 _ h1
  obtain ⟨-, -, -, hA, -, -⟩ := weylFun m E l f hf
  obtain ⟨-, -, -, -, -, hC⟩ := weylFun m E l _ h1
  obtain ⟨-, -, -, -, hB, -⟩ := weylFun m E l _ h2
  rw [hA] at hC
  rw [hC, cbiOp_add, hB]
  abel

end Triples

section Lie

variable {k r : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Distinguish the cases in `hm : r ≤ a.val ∧ a.val ≤ r + k`.

Rewrite using `[Finset.sum_eq_single a]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl]`. Simplify using `only [Hpk, eq_self_iff_true, and_true]`.

Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega`. Rewrite using `[if_neg hab]`. Establish `hab' : a.val ≠ b.val` using `fun e => hab (Fin.ext e)`. Simplify using `only [Hpk]`. Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega`.

Introduce `c _ hc`. Establish `hc' : c.val ≠ a.val` using `fun e => hc (Fin.ext e)`. Simplify using `only [Hpk]`. Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Take `⟨c₀, hc₀⟩ : ∃ c₀ : Fin (2 * r + k + 1), c₀.val = 2 * r + k - a.val` from `⟨⟨2 * r + k - a.val, by omega⟩, rfl⟩`. Rewrite using `[Finset.sum_eq_single c₀]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Rewrite using `[if_pos rfl]`. Simplify using `only [Hpk, eq_self_iff_true, and_true]`. Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega`. Rewrite using `[if_neg hab]`. Establish `hab' : a.val ≠ b.val` using `fun e => hab (Fin.ext e)`.

Simplify using `only [Hpk]`. Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega`. Introduce `c _ hc`. Establish `hc' : c.val ≠ c₀.val` using `fun e => hc (Fin.ext e)`. Simplify using `only [Hpk]`.

Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem hpk_sq' : Hpk k r * Hpk k r = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have ha := a.isLt
  have hb := b.isLt
  by_cases hm : r ≤ a.val ∧ a.val ≤ r + k
  · rw [Finset.sum_eq_single a]
    · by_cases hab : a = b
      · subst hab
        rw [if_pos rfl]
        simp only [Hpk, eq_self_iff_true, and_true]
        split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega
      · rw [if_neg hab]
        have hab' : a.val ≠ b.val := fun e => hab (Fin.ext e)
        simp only [Hpk]
        split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega
    · intro c _ hc
      have hc' : c.val ≠ a.val := fun e => hc (Fin.ext e)
      simp only [Hpk]
      split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  · obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Fin (2 * r + k + 1), c₀.val = 2 * r + k - a.val :=
      ⟨⟨2 * r + k - a.val, by omega⟩, rfl⟩
    rw [Finset.sum_eq_single c₀]
    · by_cases hab : a = b
      · subst hab
        rw [if_pos rfl]
        simp only [Hpk, eq_self_iff_true, and_true]
        split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega
      · rw [if_neg hab]
        have hab' : a.val ≠ b.val := fun e => hab (Fin.ext e)
        simp only [Hpk]
        split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega
    · intro c _ hc
      have hc' : c.val ≠ c₀.val := fun e => hc (Fin.ext e)
      simp only [Hpk]
      split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega
    · intro h
      exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.conjTranspose_apply]`. Simplify using `only [Hpk]`. Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega`.
-/
theorem hpk_h : (Hpk k r)ᴴ = Hpk k r := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  simp only [Hpk]
  split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | omega

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv hpk_sq'`.
-/
theorem hpk_inv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hpk_sq'

/- English proof (translation)
Establish `hH : (Hpk k r)ᴴ = Hpk k r` using `hpk_h`. Establish `hS' : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hpk_sq', Matrix.one_mul]`. Establish `hc : star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Rewrite using `[hpart1, hpk_inv, Matrix.conjTranspose_smul, hc, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH]`.

Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hpk_sq', hS', Matrix.mul_one]`. Use `module`.
-/
theorem hpart1_lie (Z : Mx k r) :
    (hpart1 (Hpk k r) Z)ᴴ * Hpk k r + Hpk k r * hpart1 (Hpk k r) Z = 0 := by
  have hH : (Hpk k r)ᴴ = Hpk k r := hpk_h
  have hS' : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hpk_sq', Matrix.one_mul]
  have hc : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [hpart1, hpk_inv, Matrix.conjTranspose_smul, hc, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hpk_sq', hS',
    Matrix.mul_one]
  module

/- English proof (translation)
Establish `hH : (Hpk k r)ᴴ = Hpk k r` using `hpk_h`. Establish `hS' : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hpk_sq', Matrix.one_mul]`. Establish `hc : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I))` using `by simp`. Rewrite using `[hpart2, hpk_inv, Matrix.conjTranspose_smul, hc, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH]`.

Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hpk_sq', hS', Matrix.mul_one]`. Use `module`.
-/
theorem hpart2_lie (Z : Mx k r) :
    (hpart2 (Hpk k r) Z)ᴴ * Hpk k r + Hpk k r * hpart2 (Hpk k r) Z = 0 := by
  have hH : (Hpk k r)ᴴ = Hpk k r := hpk_h
  have hS' : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hpk_sq', Matrix.one_mul]
  have hc : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp
  rw [hpart2, hpk_inv, Matrix.conjTranspose_smul, hc, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hpk_sq', hS',
    Matrix.mul_one]
  module

def inV (k r : ℕ) (i : Fin (r + 1)) (p : Fin (2 * r + k + 1)) : Prop :=
  i.val ≤ p.val ∧ p.val + i.val ≤ 2 * r + k

/- English proof (translation)
Establish `h1` using `j.isLt`. Establish `h2` using `i.isLt`. Unfold `mdim at h1`. Use `show i.val ≤ j.val + i.val ∧ j.val + i.val + i.val ≤ 2 * r + k`. Use linear arithmetic over natural numbers and integers.
-/
theorem inV_posL (i : Fin (r + 1)) (j : Fin (mdim k r i)) : inV k r i (posL k r i j) := by
  have h1 := j.isLt
  have h2 := i.isLt
  unfold mdim at h1
  show i.val ≤ j.val + i.val ∧ j.val + i.val + i.val ≤ 2 * r + k
  omega

/- English proof (translation)
Introduce `a b e`. Apply `Fin.ext` to reduce the goal to its premises. Establish `h : a.val + i.val = b.val + i.val` using `congrArg Fin.val e`. Use linear arithmetic over natural numbers and integers.
-/
theorem posL_inj (i : Fin (r + 1)) : Function.Injective (posL k r i) := by
  intro a b e
  apply Fin.ext
  have h : a.val + i.val = b.val + i.val := congrArg Fin.val e
  omega

/- English proof (translation)
Unfold `inV at hp`. Take `⟨h1, h2⟩` from `hp`. Establish `h3` using `i.isLt`. Use `⟨⟨p.val - i.val, by unfold mdim; omega⟩, ?_⟩` and prove the remaining obligations. Apply `Fin.ext` to reduce the goal to its premises.

Use `show p.val - i.val + i.val = p.val`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_posL {i : Fin (r + 1)} {p : Fin (2 * r + k + 1)} (hp : inV k r i p) :
    ∃ j, posL k r i j = p := by
  unfold inV at hp
  obtain ⟨h1, h2⟩ := hp
  have h3 := i.isLt
  refine ⟨⟨p.val - i.val, by unfold mdim; omega⟩, ?_⟩
  apply Fin.ext
  show p.val - i.val + i.val = p.val
  omega

/- English proof (translation)
Unfold `inV at ha hp`. Simplify using `only [Hpk]`. Apply the tactic sequence `split_ifs with h1 h2 h3 <;> simp_all <;> omega`.
-/
theorem hpk_out {i : Fin (r + 1)} {a p : Fin (2 * r + k + 1)} (ha : inV k r i a) (hp : ¬ inV k r i p) :
    Hpk k r a p = 0 := by
  unfold inV at ha hp
  simp only [Hpk]
  split_ifs with h1 h2 h3 <;> simp_all <;> omega

/- English proof (translation)
Introduce `h`. Unfold `inV at h`. Establish `h1` using `h.1`. Express the relevant statement in the definitionally equal form `i.val ≤ a.val at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_inV_eI {i : Fin (r + 1)} {a : Fin r} (ha : a.val < i.val) : ¬ inV k r i (eI k r a) := by
  intro h
  unfold inV at h
  have h1 := h.1
  change i.val ≤ a.val at h1
  omega

/- English proof (translation)
Introduce `h`. Unfold `inV at h`. Establish `h1` using `h.2`. Express the relevant statement in the definitionally equal form `2 * r + k - a.val + i.val ≤ 2 * r + k at h1`. Use `a.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem not_inV_esI {i : Fin (r + 1)} {a : Fin r} (ha : a.val < i.val) : ¬ inV k r i (esI k r a) := by
  intro h
  unfold inV at h
  have h1 := h.2
  change 2 * r + k - a.val + i.val ≤ 2 * r + k at h1
  have := a.isLt
  omega

/- English proof (translation)
Establish `hbp : b ≠ p` using `fun e => hp (e ▸ hb)`. Use extensionality with `q`. Simplify using `[bvec, Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, hbp]`.
-/
theorem unit_col {i : Fin (r + 1)} {a b p : Fin (2 * r + k + 1)} (hb : inV k r i b) (hp : ¬ inV k r i p) :
    (Matrix.single a b (1 : ℂ) : Mx k r) *ᵥ bvec p = 0 := by
  have hbp : b ≠ p := fun e => hp (e ▸ hb)
  ext q
  simp [bvec, Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, hbp]

/- English proof (translation)
Establish `h0 : Hpk k r a p = 0` using `hpk_out ha hp`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Establish `h1 : (Matrix.single a b (1 : ℂ) : Mx k r)ᴴ *ᵥ (Hpk k r *ᵥ bvec p) = 0`. Use extensionality with `q`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.single_apply, bvec, Pi.single_apply, h0]`.

Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Use `split_ifs with hc`. Rewrite using `[← hc.1]`. Conclude with `h0`. Both sides reduce to the same expression.

Rewrite using `[h1, Matrix.mulVec_zero]`.
-/
theorem unit_col' {i : Fin (r + 1)} {a b p : Fin (2 * r + k + 1)} (ha : inV k r i a) (hp : ¬ inV k r i p) :
    (Hpk k r * (Matrix.single a b (1 : ℂ) : Mx k r)ᴴ * Hpk k r) *ᵥ bvec p = 0 := by
  have h0 : Hpk k r a p = 0 := hpk_out ha hp
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h1 : (Matrix.single a b (1 : ℂ) : Mx k r)ᴴ *ᵥ (Hpk k r *ᵥ bvec p) = 0 := by
    ext q
    simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.single_apply, bvec,
      Pi.single_apply, h0]
    refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs with hc
    · rw [← hc.1]
      exact h0
    · rfl
  rw [h1, Matrix.mulVec_zero]

/- English proof (translation)
Establish `hb` using `inV_posL i b`. Establish `ha'` using `inV_posL i a`. Establish `hs : ∀ (c : ℂ) (A : Mx k r) (v : Fin (2 * r + k + 1) → ℂ), (c • A) *ᵥ v = c • (A *ᵥ v)` using `fun c A v => by`. Use extensionality with `q`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`.

Establish `e1 : ∀ p, ¬ inV k r i p → hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ bvec p = 0`. Introduce `p hp`. Rewrite using `[hpart1, hpk_inv, hs, Matrix.sub_mulVec, unit_col hb hp, unit_col' ha' hp, sub_zero, smul_zero]`. Establish `e2 : ∀ p, ¬ inV k r i p → hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ bvec p = 0`. Introduce `p hp`.

Rewrite using `[hpart2, hpk_inv, hs, Matrix.add_mulVec, unit_col hb hp, unit_col' ha' hp, add_zero, smul_zero]`. Conclude with `⟨⟨hpart1_lie _, fun c hc => ⟨e1 _ (not_inV_eI hc), e1 _ (not_inV_esI hc)⟩⟩, ⟨hpart2_lie _, fun c hc => ⟨e2 _ (not_inV_eI hc), e2 _ (not_inV_esI hc)⟩⟩⟩`.
-/
theorem hpart_lev (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) ∧
      inLieLev k r i (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  have hb := inV_posL i b
  have ha' := inV_posL i a
  have hs : ∀ (c : ℂ) (A : Mx k r) (v : Fin (2 * r + k + 1) → ℂ), (c • A) *ᵥ v = c • (A *ᵥ v) :=
    fun c A v => by
      ext q
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have e1 : ∀ p, ¬ inV k r i p →
      hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ bvec p = 0 := by
    intro p hp
    rw [hpart1, hpk_inv, hs, Matrix.sub_mulVec, unit_col hb hp, unit_col' ha' hp,
      sub_zero, smul_zero]
  have e2 : ∀ p, ¬ inV k r i p →
      hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ bvec p = 0 := by
    intro p hp
    rw [hpart2, hpk_inv, hs, Matrix.add_mulVec, unit_col hb hp, unit_col' ha' hp,
      add_zero, smul_zero]
  exact ⟨⟨hpart1_lie _, fun c hc => ⟨e1 _ (not_inV_eI hc), e1 _ (not_inV_esI hc)⟩⟩,
    ⟨hpart2_lie _, fun c hc => ⟨e2 _ (not_inV_eI hc), e2 _ (not_inV_esI hc)⟩⟩⟩

def evalV (v : Fin (2 * r + k + 1) → ℂ) : Mx k r →L[ℝ] (Fin (2 * r + k + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => by
        ext q
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] }

/- English proof (translation)
Establish `hd : ∀ t₀ : ℝ, HasDerivAt (fun t : ℝ => evalV v (1 * NormedSpace.exp ((t : ℂ) • X))) 0 t₀`. Introduce `t₀`. Establish `h` using `(evalV v).hasFDerivAt.comp_hasDerivAt t₀ (B5.curve_hasDerivAt (1 : Mx k r) X t₀)`. Establish `e : evalV v (1 * NormedSpace.exp ((t₀ : ℂ) • X) * X) = 0` using `by show (1 * NormedSpace.exp ((t₀ : ℂ) • X) * X) *ᵥ v = 0`. Rewrite using `[← Matrix.mulVec_mulVec, hX, Matrix.mulVec_zero]`.

Conclude with `h.congr_deriv e`. Establish `hc` using `is_const_of_deriv_eq_zero (fun t₀ => (hd t₀).differentiableAt) (fun t₀ => (hd t₀).deriv) t 0`. Establish `hc' : (1 * NormedSpace.exp ((t : ℂ) • X)) *ᵥ v = (1 * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) *ᵥ v` using `hc`. Simplify `hc'` using `[NormedSpace.exp_zero]`.
-/
theorem exp_fix {X : Mx k r} {v : Fin (2 * r + k + 1) → ℂ} (hX : X *ᵥ v = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) *ᵥ v = v := by
  have hd : ∀ t₀ : ℝ, HasDerivAt (fun t : ℝ => evalV v (1 * NormedSpace.exp ((t : ℂ) • X))) 0 t₀ := by
    intro t₀
    have h := (evalV v).hasFDerivAt.comp_hasDerivAt t₀ (B5.curve_hasDerivAt (1 : Mx k r) X t₀)
    have e : evalV v (1 * NormedSpace.exp ((t₀ : ℂ) • X) * X) = 0 := by
      show (1 * NormedSpace.exp ((t₀ : ℂ) • X) * X) *ᵥ v = 0
      rw [← Matrix.mulVec_mulVec, hX, Matrix.mulVec_zero]
    exact h.congr_deriv e
  have hc := is_const_of_deriv_eq_zero (fun t₀ => (hd t₀).differentiableAt) (fun t₀ => (hd t₀).deriv) t 0
  have hc' : (1 * NormedSpace.exp ((t : ℂ) • X)) *ᵥ v = (1 * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) *ᵥ v := hc
  simpa [NormedSpace.exp_zero] using hc'

/- English proof (translation)
Use `⟨WeylGroupFacts.uh_mul hg.1 (B5.exp_mem hX.1 t), fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, exp_fix (hX.2 a ha).1, (hg.2 a ha).1]`. Rewrite using `[← Matrix.mulVec_mulVec, exp_fix (hX.2 a ha).2, (hg.2 a ha).2]`.
-/
theorem curve_lev {i : Fin (r + 1)} {g X : Mx k r} (hg : g ∈ Glev k r i) (hX : inLieLev k r i X) (t : ℝ) :
    g * NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  refine ⟨WeylGroupFacts.uh_mul hg.1 (B5.exp_mem hX.1 t), fun a ha => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mulVec_mulVec, exp_fix (hX.2 a ha).1, (hg.2 a ha).1]
  · rw [← Matrix.mulVec_mulVec, exp_fix (hX.2 a ha).2, (hg.2 a ha).2]

end Lie

section Analysis

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

/- English proof (translation)
Establish `hγ` using `hasDerivAt_mul_exp_smul_zero g X`. Establish `hγ0` using `B5.curve_zero g X`. Establish `hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0` using `hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm`. Use `hcomp.congr_of_eventuallyEq ?_` and prove the remaining obligations. Establish `hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U` using `hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU)`.

Use `filter_upwards [hmem] with t ht`. Conclude with `he _ ht (curve_lev hg hX t)`.
-/
theorem hasDeriv_ext {f F : Mx k r → E} {U : Set (Mx k r)} (hU : IsOpen U) {g X : Mx k r}
    (hgU : g ∈ U) (hg : g ∈ Glev k r i) (hX : inLieLev k r i X) (hF : DifferentiableAt ℝ F g)
    (he : ∀ x ∈ U, x ∈ Glev k r i → f x = F x) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hγ0 := B5.curve_zero g X
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU)
  filter_upwards [hmem] with t ht
  exact he _ ht (curve_lev hg hX t)

/- English proof (translation)
Take `⟨U, F, hU, hgU, hF, he⟩` from `hf g hg`. Establish `hd : DifferentiableAt ℝ F g` using `(hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)`. Conclude with `(hasDeriv_ext hU hgU hg.1 hX hd he).differentiableAt.hasDerivAt`.
-/
theorem rd_hasDeriv {f : Mx k r → E} (hf : SmoothLev k r i D f) {g X : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hX : inLieLev k r i X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (RdV X f g) 0 := by
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g hg
  have hd : DifferentiableAt ℝ F g := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  exact (hasDeriv_ext hU hgU hg.1 hX hd he).differentiableAt.hasDerivAt

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, he⟩` from `hf g₀ hg₀`. Use `⟨U, fun x => fderiv ℝ F x (x * X), hU, hgU, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hF.fderiv_of_isOpen (m := ∞) hU (by simp)`. Conclude with `h1.clm_apply (mulRightRealCLM X).contDiff.contDiffOn`.

Introduce `x hx hxG`. Establish `hd : DifferentiableAt ℝ F x` using `(hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)`. Conclude with `(hasDeriv_ext hU hx hxG hX hd he).deriv`.
-/
theorem rd_smooth {f : Mx k r → E} (hf : SmoothLev k r i D f) {X : Mx k r} (hX : inLieLev k r i X) :
    SmoothLev k r i D (RdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  refine ⟨U, fun x => fderiv ℝ F x (x * X), hU, hgU, ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := ∞) hU (by simp)
    exact h1.clm_apply (mulRightRealCLM X).contDiff.contDiffOn
  · intro x hx hxG
    have hd : DifferentiableAt ℝ F x := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    exact (hasDeriv_ext hU hx hxG hX hd he).deriv

/- English proof (translation)
Establish `hγ` using `hasDerivAt_mul_exp_smul_zero g X`. Establish `hγ0` using `B5.curve_zero g X`. Establish `hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ D` using `hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hD.mem_nhds hg.2)`. Apply `Filter.EventuallyEq.deriv_eq` to reduce the goal to its premises. Use `filter_upwards [hmem] with t ht`.

Conclude with `h _ ⟨curve_lev hg.1 hX t, ht⟩`.
-/
theorem rd_loc (hD : IsOpen D) {f f₂ : Mx k r → E} (h : ∀ x ∈ Glev k r i ∩ D, f x = f₂ x) {g X : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) (hX : inLieLev k r i X) : RdV X f g = RdV X f₂ g := by
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hγ0 := B5.curve_zero g X
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ D :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hD.mem_nhds hg.2)
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hmem] with t ht
  exact h _ ⟨curve_lev hg.1 hX t, ht⟩

/- English proof (translation)
Establish `h1` using `rd_hasDeriv hf hg hX`. Establish `h2` using `rd_hasDeriv hf₂ hg hX`. Conclude with `(h1.add (h2.const_smul s)).deriv`.
-/
theorem rd_lin {f f₂ : Mx k r → E} (hf : SmoothLev k r i D f) (hf₂ : SmoothLev k r i D f₂) (s : ℂ)
    {g X : Mx k r} (hg : g ∈ Glev k r i ∩ D) (hX : inLieLev k r i X) :
    RdV X (fun x => f x + s • f₂ x) g = RdV X f g + s • RdV X f₂ g := by
  have h1 := rd_hasDeriv hf hg hX
  have h2 := rd_hasDeriv hf₂ hg hX
  exact (h1.add (h2.const_smul s)).deriv

/- English proof (translation)
Introduce `g₀ _` and use `⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩`.
-/
theorem smooth_zero : SmoothLev k r i D (fun _ => (0 : E)) := fun g₀ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, he⟩` from `hf g₀ hg₀`. Take `⟨U₂, F₂, hU₂, hgU₂, hF₂, he₂⟩` from `hf₂ g₀ hg₀`. Use `⟨U ∩ U₂, fun x => F x + F₂ x, hU.inter hU₂, ⟨hgU, hgU₂⟩, (hF.mono Set.inter_subset_left).add (hF₂.mono Set.inter_subset_right), fun g hg hgG => ?_⟩` and prove the remaining obligations. Simplify using `only [he g hg.1 hgG, he₂ g hg.2 hgG]`.
-/
theorem smooth_add {f f₂ : Mx k r → E} (hf : SmoothLev k r i D f) (hf₂ : SmoothLev k r i D f₂) :
    SmoothLev k r i D (fun x => f x + f₂ x) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  obtain ⟨U₂, F₂, hU₂, hgU₂, hF₂, he₂⟩ := hf₂ g₀ hg₀
  refine ⟨U ∩ U₂, fun x => F x + F₂ x, hU.inter hU₂, ⟨hgU, hgU₂⟩,
    (hF.mono Set.inter_subset_left).add (hF₂.mono Set.inter_subset_right), fun g hg hgG => ?_⟩
  simp only [he g hg.1 hgG, he₂ g hg.2 hgG]

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, he⟩` from `hf g₀ hg₀`. Use `⟨U, fun x => s • F x, hU, hgU, hF.const_smul s, fun g hg hgG => ?_⟩` and prove the remaining obligations. Simplify using `only [he g hg hgG]`.
-/
theorem smooth_smul {f : Mx k r → E} (hf : SmoothLev k r i D f) (s : ℂ) :
    SmoothLev k r i D (fun x => s • f x) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  refine ⟨U, fun x => s • F x, hU, hgU, hF.const_smul s, fun g hg hgG => ?_⟩
  simp only [he g hg hgG]

structure Good (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (T : (Mx k r → E) → Mx k r → E) : Prop where
  sm : ∀ f, SmoothLev k r i D f → SmoothLev k r i D (T f)
  loc : ∀ f f₂, (∀ x ∈ Glev k r i ∩ D, f x = f₂ x) → ∀ x ∈ Glev k r i ∩ D, T f x = T f₂ x
  lin : ∀ f f₂ (s : ℂ), SmoothLev k r i D f → SmoothLev k r i D f₂ → ∀ x ∈ Glev k r i ∩ D,
    T (fun y => f y + s • f₂ y) x = T f x + s • T f₂ x

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun f hf => hf, fun f f₂ h x hx => h x hx, fun f f₂ s _ _ x _ => rfl⟩`.
-/
theorem good_id : Good k r i D (fun f : Mx k r → E => f) := ⟨fun f hf => hf, fun f f₂ h x hx => h x hx, fun f f₂ s _ _ x _ => rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun f _ => smooth_zero, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => by simp⟩`.
-/
theorem good_zero : Good k r i D (fun _ : Mx k r → E => fun _ => (0 : E)) := ⟨fun f _ => smooth_zero, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => by simp⟩

/- English proof (translation)
Use `⟨fun f hf => hT.sm _ (hS.sm f hf), fun f f₂ h x hx => hT.loc _ _ (hS.loc f f₂ h) x hx, fun f f₂ s hf hf₂ x hx => ?_⟩` and prove the remaining obligations. Conclude with `(hT.loc _ _ (fun y hy => hS.lin f f₂ s hf hf₂ y hy) x hx).trans (hT.lin _ _ s (hS.sm f hf) (hS.sm f₂ hf₂) x hx)`.
-/
theorem Good.comp {T S : (Mx k r → E) → Mx k r → E} (hT : Good k r i D T) (hS : Good k r i D S) :
    Good k r i D (fun f => T (S f)) := by
  refine ⟨fun f hf => hT.sm _ (hS.sm f hf), fun f f₂ h x hx => hT.loc _ _ (hS.loc f f₂ h) x hx,
    fun f f₂ s hf hf₂ x hx => ?_⟩
  exact (hT.loc _ _ (fun y hy => hS.lin f f₂ s hf hf₂ y hy) x hx).trans
    (hT.lin _ _ s (hS.sm f hf) (hS.sm f₂ hf₂) x hx)

/- English proof (translation)
Use `⟨fun f hf => smooth_add (hT.sm f hf) (hS.sm f hf), fun f f₂ h x hx => ?_, fun f f₂ s hf hf₂ x hx => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Rewrite using `[hT.loc f f₂ h x hx, hS.loc f f₂ h x hx]`. Apply the tactic sequence `try dsimp only`. Rewrite using `[hT.lin f f₂ s hf hf₂ x hx, hS.lin f f₂ s hf hf₂ x hx, smul_add]`.

Normalize the expressions using the abelian group laws.
-/
theorem Good.add {T S : (Mx k r → E) → Mx k r → E} (hT : Good k r i D T) (hS : Good k r i D S) :
    Good k r i D (fun f x => T f x + S f x) := by
  refine ⟨fun f hf => smooth_add (hT.sm f hf) (hS.sm f hf), fun f f₂ h x hx => ?_,
    fun f f₂ s hf hf₂ x hx => ?_⟩
  · try dsimp only
    rw [hT.loc f f₂ h x hx, hS.loc f f₂ h x hx]
  · try dsimp only
    rw [hT.lin f f₂ s hf hf₂ x hx, hS.lin f f₂ s hf hf₂ x hx, smul_add]
    abel

/- English proof (translation)
Use `⟨fun f hf => smooth_smul (hT.sm f hf) c, fun f f₂ h x hx => ?_, fun f f₂ s hf hf₂ x hx => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Rewrite using `[hT.loc f f₂ h x hx]`. Apply the tactic sequence `try dsimp only`. Rewrite using `[hT.lin f f₂ s hf hf₂ x hx, smul_add, smul_comm c s]`.
-/
theorem Good.smul {T : (Mx k r → E) → Mx k r → E} (hT : Good k r i D T) (c : ℂ) :
    Good k r i D (fun f x => c • T f x) := by
  refine ⟨fun f hf => smooth_smul (hT.sm f hf) c, fun f f₂ h x hx => ?_,
    fun f f₂ s hf hf₂ x hx => ?_⟩
  · try dsimp only
    rw [hT.loc f f₂ h x hx]
  · try dsimp only
    rw [hT.lin f f₂ s hf hf₂ x hx, smul_add, smul_comm c s]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun f hf => rd_smooth hf hX, fun f f₂ h x hx => rd_loc hD h hx hX, fun f f₂ s hf hf₂ x hx => rd_lin hf hf₂ s hx hX⟩`.
-/
theorem good_rd (hD : IsOpen D) {X : Mx k r} (hX : inLieLev k r i X) :
    Good k r i D (fun f : Mx k r → E => RdV X f) := ⟨fun f hf => rd_smooth hf hX, fun f f₂ h x hx => rd_loc hD h hx hX,
    fun f f₂ s hf hf₂ x hx => rd_lin hf hf₂ s hx hX⟩

/- English proof (translation)
The claim follows from `Good.add (good_rd hD (hpart_lev i a b).1) (Good.smul (good_rd hD (hpart_lev i a b).2) Complex.I)`.
-/
theorem good_eh (hD : IsOpen D) (a b : Fin (mdim k r i)) :
    Good k r i D (fun f : Mx k r → E => EH k r (posL k r i a) (posL k r i b) f) := Good.add (good_rd hD (hpart_lev i a b).1) (Good.smul (good_rd hD (hpart_lev i a b).2) Complex.I)

/- English proof (translation)
Establish `hE` using `good_eh (E := E) hD a b`. Establish `hI : Good k r i D (fun (f : Mx k r → E) (g : Mx k r) => if posL k r i a = posL k r i b then u • f g else 0)`. Distinguish the cases in `hc : posL k r i a = posL k r i b`. Simplify using `only [if_pos hc]`. Conclude with `Good.smul good_id u`.

Simplify using `only [if_neg hc]`. Conclude with `good_zero`. Conclude with `Good.add hI hE`.
-/
theorem good_top (hD : IsOpen D) (u : ℂ) (a b : Fin (mdim k r i)) :
    Good k r i D (fun f : Mx k r → E => QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) f) := by
  have hE := good_eh (E := E) hD a b
  have hI : Good k r i D (fun (f : Mx k r → E) (g : Mx k r) =>
      if posL k r i a = posL k r i b then u • f g else 0) := by
    by_cases hc : posL k r i a = posL k r i b
    · simp only [if_pos hc]
      exact Good.smul good_id u
    · simp only [if_neg hc]
      exact good_zero
  exact Good.add hI hE

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact good_id`. Consider the case `cons T L ih`. Conclude with `Good.comp (hL T (by simp)) (ih fun T' h => hL T' (by simp [h]))`.
-/
theorem good_foldr (L : List ((Mx k r → E) → Mx k r → E)) (hL : ∀ T ∈ L, Good k r i D T) :
    Good k r i D (fun f => L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact good_id
  | cons T L ih =>
    exact Good.comp (hL T (by simp)) (ih fun T' h => hL T' (by simp [h]))

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `good_zero`. Consider the case `@insert a s ha ih`.

Simplify using `only [Finset.sum_insert ha]`. Conclude with `Good.add (Good.smul (hT a (Finset.mem_insert_self a s)) (c a)) (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))`.
-/
theorem good_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (T : ι → (Mx k r → E) → Mx k r → E)
    (hT : ∀ j ∈ s, Good k r i D (T j)) : Good k r i D (fun f x => ∑ j ∈ s, c j • T j f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact good_zero
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact Good.add (Good.smul (hT a (Finset.mem_insert_self a s)) (c a))
      (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Establish `key : ∀ σ : Equiv.Perm (Fin t), Good k r i D (fun f : Mx k r → E => (List.ofFn fun l : Fin t => QuantumDeterminants.Top (EH k r) (u - ((l : ℕ) : ℂ)) ((posL k r i ∘ a) (σ l)) ((posL k r i ∘ b) l)).foldr (fun T h => T h) f)` using `fun σ => good_foldr _ fun T hT => by`. Rewrite `hT` using `[List.mem_ofFn]`. Take `⟨l, rfl⟩` from `hT`. Conclude with `good_top hD _ _ _`. Establish `h` using `good_sum Finset.univ (fun σ : Equiv.Perm (Fin t) => ((Equiv.Perm.sign σ : ℤ) : ℂ)) _ (fun σ _ => key σ)`.

Use `h using 2 with f` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using `only [qminorOp, Finset.sum_apply, Pi.smul_apply]`.
-/
theorem good_qminor (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    Good k r i D (fun f : Mx k r → E => qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u f) := by
  have key : ∀ σ : Equiv.Perm (Fin t), Good k r i D (fun f : Mx k r → E =>
      (List.ofFn fun l : Fin t => QuantumDeterminants.Top (EH k r) (u - ((l : ℕ) : ℂ)) ((posL k r i ∘ a) (σ l))
        ((posL k r i ∘ b) l)).foldr (fun T h => T h) f) := fun σ =>
    good_foldr _ fun T hT => by
      rw [List.mem_ofFn] at hT
      obtain ⟨l, rfl⟩ := hT
      exact good_top hD _ _ _
  have h := good_sum Finset.univ (fun σ : Equiv.Perm (Fin t) => ((Equiv.Perm.sign σ : ℤ) : ℂ)) _
    (fun σ _ => key σ)
  convert h using 2 with f
  funext x
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]

end Analysis

section LinLoc

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

structure LL (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (T : (Mx k r → E) → Mx k r → E) : Prop where
  loc : ∀ f f₂, (∀ x ∈ Glev k r i ∩ D, f x = f₂ x) → ∀ x ∈ Glev k r i ∩ D, T f x = T f₂ x
  lin : ∀ f f₂ (s : ℂ), SmoothLev k r i D f → SmoothLev k r i D f₂ → ∀ x ∈ Glev k r i ∩ D,
    T (fun y => f y + s • f₂ y) x = T f x + s • T f₂ x

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.loc, h.lin⟩`.
-/
theorem Good.ll {T : (Mx k r → E) → Mx k r → E} (h : Good k r i D T) : LL k r i D T := ⟨h.loc, h.lin⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => by simp⟩`.
-/
theorem ll_zero : LL k r i D (fun _ : Mx k r → E => fun _ => (0 : E)) := ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => by simp⟩

/- English proof (translation)
Use `⟨fun f f₂ hh x hx => ?_, fun f f₂ s hf hf₂ x hx => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Rewrite using `[h.loc f f₂ hh x hx]`. Apply the tactic sequence `try dsimp only`. Rewrite using `[h.lin f f₂ s hf hf₂ x hx, smul_add, smul_comm (c x) s]`.
-/
theorem LL.coef {T : (Mx k r → E) → Mx k r → E} (h : LL k r i D T) (c : Mx k r → ℂ) :
    LL k r i D (fun f x => c x • T f x) := by
  refine ⟨fun f f₂ hh x hx => ?_, fun f f₂ s hf hf₂ x hx => ?_⟩
  · try dsimp only
    rw [h.loc f f₂ hh x hx]
  · try dsimp only
    rw [h.lin f f₂ s hf hf₂ x hx, smul_add, smul_comm (c x) s]

/- English proof (translation)
Use `⟨fun f f₂ h x hx => ?_, fun f f₂ s hf hf₂ x hx => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Rewrite using `[hT.loc f f₂ h x hx, hS.loc f f₂ h x hx]`. Apply the tactic sequence `try dsimp only`. Rewrite using `[hT.lin f f₂ s hf hf₂ x hx, hS.lin f f₂ s hf hf₂ x hx, smul_add]`.

Normalize the expressions using the abelian group laws.
-/
theorem LL.add {T S : (Mx k r → E) → Mx k r → E} (hT : LL k r i D T) (hS : LL k r i D S) :
    LL k r i D (fun f x => T f x + S f x) := by
  refine ⟨fun f f₂ h x hx => ?_, fun f f₂ s hf hf₂ x hx => ?_⟩
  · try dsimp only
    rw [hT.loc f f₂ h x hx, hS.loc f f₂ h x hx]
  · try dsimp only
    rw [hT.lin f f₂ s hf hf₂ x hx, hS.lin f f₂ s hf hf₂ x hx, smul_add]
    abel

/- English proof (translation)
Use `⟨fun f f₂ hh x hx => ?_, fun f f₂ s hf hf₂ x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.neg_apply, h.loc f f₂ hh x hx]`. Simplify using `only [Pi.neg_apply, h.lin f f₂ s hf hf₂ x hx, neg_add, smul_neg]`.
-/
theorem LL.neg {T : (Mx k r → E) → Mx k r → E} (h : LL k r i D T) : LL k r i D (fun f => -(T f)) := by
  refine ⟨fun f f₂ hh x hx => ?_, fun f f₂ s hf hf₂ x hx => ?_⟩
  · simp only [Pi.neg_apply, h.loc f f₂ hh x hx]
  · simp only [Pi.neg_apply, h.lin f f₂ s hf hf₂ x hx, neg_add, smul_neg]

/- English proof (translation)
Use `⟨fun f f₂ hh x hx => ?_, fun f f₂ s hf hf₂ x hx => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `by_cases hp : p <;> simp [hp, h.loc f f₂ hh x hx]`. Apply the tactic sequence `by_cases hp : p <;> simp [hp, h.lin f f₂ s hf hf₂ x hx]`.
-/
theorem LL.ite {T : (Mx k r → E) → Mx k r → E} (h : LL k r i D T) (p : Prop) [Decidable p] :
    LL k r i D (fun f x => if p then T f x else 0) := by
  refine ⟨fun f f₂ hh x hx => ?_, fun f f₂ s hf hf₂ x hx => ?_⟩
  · by_cases hp : p <;> simp [hp, h.loc f f₂ hh x hx]
  · by_cases hp : p <;> simp [hp, h.lin f f₂ s hf hf₂ x hx]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `ll_zero`. Consider the case `@insert a s ha ih`.

Simplify using `only [Finset.sum_insert ha]`. Conclude with `LL.add (hT a (Finset.mem_insert_self a s)) (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))`.
-/
theorem ll_sum {ι : Type*} (s : Finset ι) (T : ι → (Mx k r → E) → Mx k r → E)
    (hT : ∀ j ∈ s, LL k r i D (T j)) : LL k r i D (fun f x => ∑ j ∈ s, T j f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ll_zero
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact LL.add (hT a (Finset.mem_insert_self a s)) (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
The claim follows from `ll_sum Finset.univ _ (fun p _ => ll_sum Finset.univ _ (fun q _ => LL.coef (Good.ll (good_qminor hD (skip1 p) (skip1 q) u)) (fun g => (-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * β g p * a g q)))`.
-/
theorem ll_chat (hD : IsOpen D) (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ) :
    LL k r i D (fun f : Mx k r → E => chatL (EH k r) (posL k r i) u a β f) := ll_sum Finset.univ _ (fun p _ => ll_sum Finset.univ _ (fun q _ =>
    LL.coef (Good.ll (good_qminor hD (skip1 p) (skip1 q) u))
      (fun g => (-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * β g p * a g q)))

/- English proof (translation)
The claim follows from `ll_sum Finset.univ _ fun p _ => ll_sum Finset.univ _ fun p' _ => ll_sum Finset.univ _ fun q _ => ll_sum Finset.univ _ fun q' _ => LL.ite (LL.coef (Good.ll (good_qminor hD (skip2 p p') (skip2 q q') u)) (fun g => (-1 : ℂ) ^ ((p : ℕ) + (p' : ℕ) + (q : ℕ) + (q' : ℕ)) * (β g p * β' g …`.
-/
theorem ll_chat2 (hD : IsOpen D) (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ) :
    LL k r i D (fun f : Mx k r → E => chat2L (EH k r) (posL k r i) u a a' β β' f) := ll_sum Finset.univ _ fun p _ => ll_sum Finset.univ _ fun p' _ => ll_sum Finset.univ _ fun q _ =>
    ll_sum Finset.univ _ fun q' _ =>
      LL.ite (LL.coef (Good.ll (good_qminor hD (skip2 p p') (skip2 q q') u))
        (fun g => (-1 : ℂ) ^ ((p : ℕ) + (p' : ℕ) + (q : ℕ) + (q' : ℕ)) * (β g p * β' g p' - β g p' * β' g p) *
          (a g q * a' g q' - a g q' * a' g q))) (p < p' ∧ q < q')

/- English proof (translation)
Use `match p, q with`. Consider the case `0, 0 => exact Good.ll (good_qminor hD id id (uC k r i Y))`. Consider the case `0, 1 => exact LL.neg (ll_chat hD _ _ _)`. Consider the case `1, 0 => exact LL.neg (ll_chat hD _ _ _)`. Consider the case `1, 1 => exact LL.neg (ll_chat2 hD _ _ _ _ _)`.
-/
theorem ll_tL (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2) :
    LL k r i D (fun f : Mx k r → E => tL k r z z' i Y p q f) := by
  match p, q with
  | 0, 0 => exact Good.ll (good_qminor hD id id (uC k r i Y))
  | 0, 1 => exact LL.neg (ll_chat hD _ _ _)
  | 1, 0 => exact LL.neg (ll_chat hD _ _ _)
  | 1, 1 => exact LL.neg (ll_chat2 hD _ _ _ _ _)

end LinLoc

section Poly

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

def PolyFam (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (N : ℕ) (h : ℂ → Mx k r → E) : Prop :=
  ∃ c : ℕ → Mx k r → E, (∀ j, SmoothLev k r i D (c j)) ∧
    ∀ Y, ∀ x ∈ Glev k r i ∩ D, h Y x = ∑ j ∈ Finset.range N, Y ^ j • c j x

/- English proof (translation)
Take `⟨c, hc, he⟩` from `H`. Conclude with `⟨c, hc, fun Y x hx => (e Y x hx).trans (he Y x hx)⟩`.
-/
theorem PolyFam.congr {N : ℕ} {h h' : ℂ → Mx k r → E} (H : PolyFam k r i D N h)
    (e : ∀ Y, ∀ x ∈ Glev k r i ∩ D, h' Y x = h Y x) : PolyFam k r i D N h' := by
  obtain ⟨c, hc, he⟩ := H
  exact ⟨c, hc, fun Y x hx => (e Y x hx).trans (he Y x hx)⟩

/- English proof (translation)
Take `⟨c, hc, he⟩` from `H`. Use `⟨fun j x => if j < N then c j x else 0, fun j => ?_, fun Y x hx => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j < N`. Simplify using `only [if_pos hj]`. Conclude with `hc j`.

Simplify using `only [if_neg hj]`. Conclude with `smooth_zero`. Rewrite using `[he Y x hx, Finset.sum_range_succ]`. Simplify using `only [lt_self_iff_false, ↓reduceIte, smul_zero, add_zero]`. Conclude with `Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]`.
-/
theorem PolyFam.succ {N : ℕ} {h : ℂ → Mx k r → E} (H : PolyFam k r i D N h) : PolyFam k r i D (N + 1) h := by
  obtain ⟨c, hc, he⟩ := H
  refine ⟨fun j x => if j < N then c j x else 0, fun j => ?_, fun Y x hx => ?_⟩
  · by_cases hj : j < N
    · simp only [if_pos hj]
      exact hc j
    · simp only [if_neg hj]
      exact smooth_zero
  · rw [he Y x hx, Finset.sum_range_succ]
    simp only [lt_self_iff_false, ↓reduceIte, smul_zero, add_zero]
    exact Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]

/- English proof (translation)
Take `⟨c, hc, he⟩` from `H`. Take `⟨c', hc', he'⟩` from `H'`. Use `⟨fun j x => c j x + c' j x, fun j => smooth_add (hc j) (hc' j), fun Y x hx => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Rewrite using `[he Y x hx, he' Y x hx, ← Finset.sum_add_distrib]`.

Simplify using `only [smul_add]`.
-/
theorem PolyFam.add {N : ℕ} {h h' : ℂ → Mx k r → E} (H : PolyFam k r i D N h) (H' : PolyFam k r i D N h') :
    PolyFam k r i D N (fun Y x => h Y x + h' Y x) := by
  obtain ⟨c, hc, he⟩ := H
  obtain ⟨c', hc', he'⟩ := H'
  refine ⟨fun j x => c j x + c' j x, fun j => smooth_add (hc j) (hc' j), fun Y x hx => ?_⟩
  try dsimp only
  rw [he Y x hx, he' Y x hx, ← Finset.sum_add_distrib]
  simp only [smul_add]

/- English proof (translation)
Take `⟨c, hc, he⟩` from `H`. Use `⟨fun j x => s • c j x, fun j => smooth_smul (hc j) s, fun Y x hx => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Rewrite using `[he Y x hx, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => smul_comm _ _ _`.
-/
theorem PolyFam.smul {N : ℕ} {h : ℂ → Mx k r → E} (H : PolyFam k r i D N h) (s : ℂ) :
    PolyFam k r i D N (fun Y x => s • h Y x) := by
  obtain ⟨c, hc, he⟩ := H
  refine ⟨fun j x => s • c j x, fun j => smooth_smul (hc j) s, fun Y x hx => ?_⟩
  try dsimp only
  rw [he Y x hx, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

/- English proof (translation)
Take `⟨c, hc, he⟩` from `H`. Use `⟨fun j x => if j = 0 then 0 else c (j - 1) x, fun j => ?_, fun Y x hx => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j = 0`. Simplify using `only [if_pos hj]`. Conclude with `smooth_zero`.

Simplify using `only [if_neg hj]`. Conclude with `hc (j - 1)`. Apply the tactic sequence `try dsimp only`. Rewrite using `[he Y x hx, Finset.sum_range_succ', Finset.smul_sum]`. Simplify using `only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, eq_self_iff_true, if_true, smul_zero, add_zero, pow_succ', mul_smul]`.
-/
theorem PolyFam.mulY {N : ℕ} {h : ℂ → Mx k r → E} (H : PolyFam k r i D N h) :
    PolyFam k r i D (N + 1) (fun Y x => Y • h Y x) := by
  obtain ⟨c, hc, he⟩ := H
  refine ⟨fun j x => if j = 0 then 0 else c (j - 1) x, fun j => ?_, fun Y x hx => ?_⟩
  · by_cases hj : j = 0
    · simp only [if_pos hj]
      exact smooth_zero
    · simp only [if_neg hj]
      exact hc (j - 1)
  · try dsimp only
    rw [he Y x hx, Finset.sum_range_succ', Finset.smul_sum]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, eq_self_iff_true, if_true, smul_zero, add_zero, pow_succ',
      mul_smul]

/- English proof (translation)
Use `⟨fun j x => if j = N then f x else 0, fun j => ?_, fun Y x hx => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j = N`. Simplify using `only [if_pos hj]`. Conclude with `hf`. Simplify using `only [if_neg hj]`.

Conclude with `smooth_zero`. Simplify using `[smul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]`.
-/
theorem polyFam_monomial {f : Mx k r → E} (hf : SmoothLev k r i D f) (N : ℕ) :
    PolyFam k r i D (N + 1) (fun Y x => Y ^ N • f x) := by
  refine ⟨fun j x => if j = N then f x else 0, fun j => ?_, fun Y x hx => ?_⟩
  · by_cases hj : j = N
    · simp only [if_pos hj]
      exact hf
    · simp only [if_neg hj]
      exact smooth_zero
  · simp [smul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

/- English proof (translation)
Simplify using `using hT.lin (fun _ => 0) (fun _ => 0) 1 smooth_zero smooth_zero x hx`.
-/
theorem Good.map_zero {T : (Mx k r → E) → Mx k r → E} (hT : Good k r i D T) {x : Mx k r}
    (hx : x ∈ Glev k r i ∩ D) : T (fun _ => 0) x = 0 := by
  simpa using hT.lin (fun _ => 0) (fun _ => 0) 1 smooth_zero smooth_zero x hx

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Simplify using `only [Finset.sum_range_zero]`. Conclude with `smooth_zero`. Consider the case `succ N ih`.

Simplify using `only [Finset.sum_range_succ]`. Conclude with `smooth_add ih (smooth_smul (hc N) (a N))`.
-/
theorem smooth_lin_sum (a : ℕ → ℂ) {c : ℕ → Mx k r → E} (hc : ∀ j, SmoothLev k r i D (c j)) (N : ℕ) :
    SmoothLev k r i D (fun y => ∑ j ∈ Finset.range N, a j • c j y) := by
  induction N with
  | zero =>
    simp only [Finset.sum_range_zero]
    exact smooth_zero
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    exact smooth_add ih (smooth_smul (hc N) (a N))

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Simplify using `only [Finset.sum_range_zero]`. Conclude with `hT.map_zero hx`. Consider the case `succ N ih`.

Establish `h` using `hT.lin (fun y => ∑ j ∈ Finset.range N, a j • c j y) (c N) (a N) (smooth_lin_sum a hc N) (hc N) x hx`. Simplify using `only [Finset.sum_range_succ]`. Rewrite using `[h, ih]`.
-/
theorem Good.map_sum {T : (Mx k r → E) → Mx k r → E} (hT : Good k r i D T) (a : ℕ → ℂ)
    {c : ℕ → Mx k r → E} (hc : ∀ j, SmoothLev k r i D (c j)) {x : Mx k r} (hx : x ∈ Glev k r i ∩ D) (N : ℕ) :
    T (fun y => ∑ j ∈ Finset.range N, a j • c j y) x = ∑ j ∈ Finset.range N, a j • T (c j) x := by
  induction N with
  | zero =>
    simp only [Finset.sum_range_zero]
    exact hT.map_zero hx
  | succ N ih =>
    have h := hT.lin (fun y => ∑ j ∈ Finset.range N, a j • c j y) (c N) (a N)
      (smooth_lin_sum a hc N) (hc N) x hx
    simp only [Finset.sum_range_succ]
    rw [h, ih]

/- English proof (translation)
Take `⟨c, hc, he⟩` from `H`. Use `⟨fun j => T (c j), fun j => hT.sm _ (hc j), fun Y x hx => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Rewrite using `[hT.loc (h Y) (fun y => ∑ j ∈ Finset.range N, Y ^ j • c j y) (fun y hy => he Y y hy) x hx]`. Conclude with `hT.map_sum (fun j => Y ^ j) hc hx N`.
-/
theorem PolyFam.good {N : ℕ} {h : ℂ → Mx k r → E} (H : PolyFam k r i D N h)
    {T : (Mx k r → E) → Mx k r → E} (hT : Good k r i D T) : PolyFam k r i D N (fun Y => T (h Y)) := by
  obtain ⟨c, hc, he⟩ := H
  refine ⟨fun j => T (c j), fun j => hT.sm _ (hc j), fun Y x hx => ?_⟩
  try dsimp only
  rw [hT.loc (h Y) (fun y => ∑ j ∈ Finset.range N, Y ^ j • c j y) (fun y hy => he Y y hy) x hx]
  exact hT.map_sum (fun j => Y ^ j) hc hx N

def opF (k r : ℕ) (i : Fin (r + 1)) (Y : ℂ) (x : ℂ × Fin (mdim k r i) × Fin (mdim k r i)) :
    (Mx k r → E) → Mx k r → E :=
  QuantumDeterminants.Top (EH k r) (Y + x.1) (posL k r i x.2.1) (posL k r i x.2.2)

def dl (k r : ℕ) (i : Fin (r + 1)) (x : ℂ × Fin (mdim k r i) × Fin (mdim k r i)) : ℂ :=
  if posL k r i x.2.1 = posL k r i x.2.2 then 1 else 0

/- English proof (translation)
Simplify using `only [opF, dl, QuantumDeterminants.Top]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem opF_apply (Y : ℂ) (x : ℂ × Fin (mdim k r i) × Fin (mdim k r i)) (h : Mx k r → E) (g : Mx k r) :
    opF k r i Y x h g = dl k r i x • ((Y + x.1) • h g) + EH k r (posL k r i x.2.1) (posL k r i x.2.2) h g := by
  simp only [opF, dl, QuantumDeterminants.Top]
  split_ifs <;> simp

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil`. Use `⟨fun _ _ => 0, fun _ => smooth_zero, fun Y x _ => ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Consider the case `cons e L ih`.

Establish `hG : PolyFam k r i D (L.length + 1) (fun Y => (L.map (opF k r i Y)).foldr (fun T h => T h) f)` using `(ih.succ.add (polyFam_monomial (smooth_smul hf (L.map (dl k r i)).prod) L.length)).congr fun Y x _ => by simp`. Establish `hE` using `hG.good (good_eh hD e.2.1 e.2.2)`. Establish `hA` using `ih.mulY.smul (dl k r i e)`. Establish `hB` using `ih.succ.smul (dl k r i e * e.1)`. Establish `hC` using `polyFam_monomial (smooth_smul hf (dl k r i e * e.1 * (L.map (dl k r i)).prod)) L.length`.

Use `(((hA.add hB).add hC).add hE).congr fun Y x _ => ?_` and prove the remaining obligations. Simplify using `only [List.map_cons, List.foldr_cons, List.prod_cons, List.length_cons]`. Rewrite using `[opF_apply]`. Use `module`.
-/
theorem fold_poly (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f)
    (L : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i))) :
    PolyFam k r i D L.length (fun Y x => (L.map (opF k r i Y)).foldr (fun T h => T h) f x -
      Y ^ L.length • ((L.map (dl k r i)).prod • f x)) := by
  induction L with
  | nil =>
    refine ⟨fun _ _ => 0, fun _ => smooth_zero, fun Y x _ => ?_⟩
    simp
  | cons e L ih =>
    have hG : PolyFam k r i D (L.length + 1) (fun Y => (L.map (opF k r i Y)).foldr (fun T h => T h) f) :=
      (ih.succ.add (polyFam_monomial (smooth_smul hf (L.map (dl k r i)).prod) L.length)).congr
        fun Y x _ => by simp
    have hE := hG.good (good_eh hD e.2.1 e.2.2)
    have hA := ih.mulY.smul (dl k r i e)
    have hB := ih.succ.smul (dl k r i e * e.1)
    have hC := polyFam_monomial (smooth_smul hf (dl k r i e * e.1 * (L.map (dl k r i)).prod)) L.length
    refine (((hA.add hB).add hC).add hE).congr fun Y x _ => ?_
    simp only [List.map_cons, List.foldr_cons, List.prod_cons, List.length_cons]
    rw [opF_apply]
    module

def PolyAt (N : ℕ) (φ : ℂ → E) : Prop := ∃ c : ℕ → E, ∀ Y, φ Y = ∑ j ∈ Finset.range N, Y ^ j • c j

/- English proof (translation)
Take `⟨c, hc, he⟩` from `H`. Conclude with `⟨fun j => c j x, fun Y => he Y x hx⟩`.
-/
theorem PolyFam.at {N : ℕ} {h : ℂ → Mx k r → E} (H : PolyFam k r i D N h) {x : Mx k r}
    (hx : x ∈ Glev k r i ∩ D) : PolyAt N (fun Y => h Y x) := by
  obtain ⟨c, hc, he⟩ := H
  exact ⟨fun j => c j x, fun Y => he Y x hx⟩

/- English proof (translation)
Take `⟨c, hc⟩` from `H`. Conclude with `⟨c, fun Y => (e Y).trans (hc Y)⟩`.
-/
theorem PolyAt.congr {N : ℕ} {φ ψ : ℂ → E} (H : PolyAt N φ) (e : ∀ Y, ψ Y = φ Y) : PolyAt N ψ := by
  obtain ⟨c, hc⟩ := H
  exact ⟨c, fun Y => (e Y).trans (hc Y)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => 0, fun Y => by simp⟩`.
-/
theorem polyAt_zero (N : ℕ) : PolyAt N (fun _ => (0 : E)) := ⟨fun _ => 0, fun Y => by simp⟩

/- English proof (translation)
Take `⟨c, hc⟩` from `H`. Take `⟨c', hc'⟩` from `H'`. Use `⟨fun j => c j + c' j, fun Y => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Rewrite using `[hc Y, hc' Y, ← Finset.sum_add_distrib]`.

Simplify using `only [smul_add]`.
-/
theorem PolyAt.add {N : ℕ} {φ ψ : ℂ → E} (H : PolyAt N φ) (H' : PolyAt N ψ) : PolyAt N (fun Y => φ Y + ψ Y) := by
  obtain ⟨c, hc⟩ := H
  obtain ⟨c', hc'⟩ := H'
  refine ⟨fun j => c j + c' j, fun Y => ?_⟩
  try dsimp only
  rw [hc Y, hc' Y, ← Finset.sum_add_distrib]
  simp only [smul_add]

/- English proof (translation)
Take `⟨c, hc⟩` from `H`. Use `⟨fun j => s • c j, fun Y => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Rewrite using `[hc Y, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => smul_comm _ _ _`.
-/
theorem PolyAt.smul {N : ℕ} {φ : ℂ → E} (H : PolyAt N φ) (s : ℂ) : PolyAt N (fun Y => s • φ Y) := by
  obtain ⟨c, hc⟩ := H
  refine ⟨fun j => s • c j, fun Y => ?_⟩
  try dsimp only
  rw [hc Y, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

/- English proof (translation)
Take `⟨c, hc⟩` from `H`. Use `⟨fun j => -c j, fun Y => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Rewrite using `[hc Y]`. Simplify using `[smul_neg, Finset.sum_neg_distrib]`.
-/
theorem PolyAt.neg {N : ℕ} {φ : ℂ → E} (H : PolyAt N φ) : PolyAt N (fun Y => -φ Y) := by
  obtain ⟨c, hc⟩ := H
  refine ⟨fun j => -c j, fun Y => ?_⟩
  try dsimp only
  rw [hc Y]
  simp [smul_neg, Finset.sum_neg_distrib]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `polyAt_zero N`. Consider the case `@insert a s ha ih`.

Simplify using `only [Finset.sum_insert ha]`. Conclude with `PolyAt.add (H a (Finset.mem_insert_self a s)) (ih fun j hj => H j (Finset.mem_insert_of_mem hj))`.
-/
theorem polyAt_sum {ι : Type*} {N : ℕ} (s : Finset ι) (φ : ι → ℂ → E) (H : ∀ j ∈ s, PolyAt N (φ j)) :
    PolyAt N (fun Y => ∑ j ∈ s, φ j Y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact polyAt_zero N
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact PolyAt.add (H a (Finset.mem_insert_self a s)) (ih fun j hj => H j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Take `⟨c, hc⟩` from `H`. Use `⟨fun j => if j < N then c j else 0, fun Y => ?_⟩` and prove the remaining obligations. Rewrite using `[hc Y, Finset.sum_range_succ]`. Simplify using `only [lt_self_iff_false, ↓reduceIte, smul_zero, add_zero]`. Conclude with `Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]`.
-/
theorem PolyAt.succ {N : ℕ} {φ : ℂ → E} (H : PolyAt N φ) : PolyAt (N + 1) φ := by
  obtain ⟨c, hc⟩ := H
  refine ⟨fun j => if j < N then c j else 0, fun Y => ?_⟩
  rw [hc Y, Finset.sum_range_succ]
  simp only [lt_self_iff_false, ↓reduceIte, smul_zero, add_zero]
  exact Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]

/- English proof (translation)
Use `⟨fun j => if j = N then e else 0, fun Y => ?_⟩` and prove the remaining obligations. Simplify using `[smul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]`.
-/
theorem polyAt_monomial (N : ℕ) (e : E) : PolyAt (N + 1) (fun Y => Y ^ N • e) := by
  refine ⟨fun j => if j = N then e else 0, fun Y => ?_⟩
  simp [smul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

def lc (k r : ℕ) (i : Fin (r + 1)) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) : ℂ :=
  ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
    ∏ l : Fin t, if posL k r i (a (σ l)) = posL k r i (b l) then 1 else 0

/- English proof (translation)
Establish `key : ∀ σ : Equiv.Perm (Fin t), PolyAt t (fun Y => (List.ofFn fun l : Fin t => QuantumDeterminants.Top (EH k r) (Y + s - ((l : ℕ) : ℂ)) ((posL k r i ∘ a) (σ l)) ((posL k r i ∘ b) l)).foldr (fun T h => T h) f x - Y ^ t • ((∏ l : Fin t, if posL k r i (a (σ l)) = posL k r i (b l) th …`. Introduce `σ`. Establish `h` using `(fold_poly hD hf (List.ofFn fun l : Fin t => (s - ((l : ℕ) : ℂ), a (σ l), b l))).at hx`. Simplify using `only [List.length_ofFn, List.map_ofFn, List.prod_ofFn] at h`. Use `h.congr fun Y => ?_` and prove the remaining obligations.

Establish `e : (List.ofFn fun l : Fin t => QuantumDeterminants.Top (E` using `E) (EH k r) (Y + s - ((l : ℕ) : ℂ)) ((posL k r i ∘ a) (σ l)) ((posL k r i ∘ b) l)) = List.ofFn (opF k r i Y ∘ fun l : Fin t => (s - ((l : ℕ) : ℂ), a (σ l), b l)) := by`. Use `congr 1`. Use function extensionality and compare the values at `l`. Simplify using `only [Function.comp, opF, add_sub_assoc]`. Rewrite using `[e]`.

Both sides reduce to the same expression. Use `(polyAt_sum Finset.univ _ fun σ _ => (key σ).smul ((Equiv.Perm.sign σ : ℤ) : ℂ)).congr fun Y => ?_` and prove the remaining obligations. Simplify using `only [qminorOp, Finset.sum_apply, Pi.smul_apply, lc, Finset.sum_smul, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Use `module`.
-/
theorem qminor_poly (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f) {x : Mx k r}
    (hx : x ∈ Glev k r i ∩ D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (s : ℂ) :
    PolyAt t (fun Y => qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) (Y + s) f x -
      Y ^ t • (lc k r i a b • f x)) := by
  have key : ∀ σ : Equiv.Perm (Fin t), PolyAt t (fun Y =>
      (List.ofFn fun l : Fin t => QuantumDeterminants.Top (EH k r) (Y + s - ((l : ℕ) : ℂ)) ((posL k r i ∘ a) (σ l))
        ((posL k r i ∘ b) l)).foldr (fun T h => T h) f x -
      Y ^ t • ((∏ l : Fin t, if posL k r i (a (σ l)) = posL k r i (b l) then (1 : ℂ) else 0) • f x)) := by
    intro σ
    have h := (fold_poly hD hf (List.ofFn fun l : Fin t => (s - ((l : ℕ) : ℂ), a (σ l), b l))).at hx
    simp only [List.length_ofFn, List.map_ofFn, List.prod_ofFn] at h
    refine h.congr fun Y => ?_
    have e : (List.ofFn fun l : Fin t => QuantumDeterminants.Top (E := E) (EH k r) (Y + s - ((l : ℕ) : ℂ))
        ((posL k r i ∘ a) (σ l)) ((posL k r i ∘ b) l)) =
        List.ofFn (opF k r i Y ∘ fun l : Fin t => (s - ((l : ℕ) : ℂ), a (σ l), b l)) := by
      congr 1
      funext l
      simp only [Function.comp, opF, add_sub_assoc]
    rw [e]
    rfl
  refine (polyAt_sum Finset.univ _ fun σ _ => (key σ).smul ((Equiv.Perm.sign σ : ℤ) : ℂ)).congr fun Y => ?_
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply, lc, Finset.sum_smul, Finset.smul_sum, smul_sub,
    Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  module

/- English proof (translation)
The claim follows from `((qminor_poly hD hf hx a b s).succ.add (polyAt_monomial t (lc k r i a b • f x))).congr fun Y => by simp`.
-/
theorem qminor_poly' (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f) {x : Mx k r}
    (hx : x ∈ Glev k r i ∩ D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (s : ℂ) :
    PolyAt (t + 1) (fun Y => qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) (Y + s) f x) := ((qminor_poly hD hf hx a b s).succ.add (polyAt_monomial t (lc k r i a b • f x))).congr
    fun Y => by simp

end Poly

section Lead

variable {k r : ℕ} {i : Fin (r + 1)}

/- English proof (translation)
Unfold `lc`. Rewrite using `[Finset.sum_eq_single 1]`. Simplify using the standard rewrite rules. Introduce `σ _ hσ`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l, σ l ≠ l := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hσ (Equiv.ext hc)`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ l) (if_neg fun e => hl (ha (posL_inj i e))), mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem lc_self {t : ℕ} (a : Fin t → Fin (mdim k r i)) (ha : Function.Injective a) : lc k r i a a = 1 := by
  unfold lc
  rw [Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    obtain ⟨l, hl⟩ : ∃ l, σ l ≠ l := by
      by_contra hc
      push_neg at hc
      exact hσ (Equiv.ext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ l) (if_neg fun e => hl (ha (posL_inj i e))), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `lc`. Conclude with `Finset.sum_eq_zero fun σ _ => by`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ l₀) (if_neg fun e => h (σ l₀) (posL_inj i e)), mul_zero]`.
-/
theorem lc_miss {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (l₀ : Fin t) (h : ∀ l, a l ≠ b l₀) :
    lc k r i a b = 0 := by
  unfold lc
  exact Finset.sum_eq_zero fun σ _ => by
    rw [Finset.prod_eq_zero (Finset.mem_univ l₀) (if_neg fun e => h (σ l₀) (posL_inj i e)), mul_zero]

/- English proof (translation)
Introduce `x y e`. Apply `Fin.ext` to reduce the goal to its premises. Establish `h` using `congrArg Fin.val e`. Unfold `skip1 at h`. Apply the tactic sequence `split_ifs at h <;> simp only [Fin.val_mk] at h <;> omega`.
-/
theorem skip_one_injective {t : ℕ} (a : Fin t) : Function.Injective (skip1 a) := by
  intro x y e
  apply Fin.ext
  have h := congrArg Fin.val e
  unfold skip1 at h
  split_ifs at h <;> simp only [Fin.val_mk] at h <;> omega

/- English proof (translation)
Introduce `e`. Establish `h` using `congrArg Fin.val e`. Unfold `skip1 at h`. Apply the tactic sequence `split_ifs at h <;> simp only [Fin.val_mk] at h <;> omega`.
-/
theorem skip_one_ne {t : ℕ} (a : Fin t) (l : Fin (t - 1)) : skip1 a l ≠ a := by
  intro e
  have h := congrArg Fin.val e
  unfold skip1 at h
  split_ifs at h <;> simp only [Fin.val_mk] at h <;> omega

/- English proof (translation)
Break down `Nat.lt_or_gt_of_ne (fun e => h (Fin.ext e)) with hab | hab` into its components or cases. Use `⟨⟨a.val, by have := b.isLt; omega⟩, ?_⟩` and prove the remaining obligations. Apply `Fin.ext` to reduce the goal to its premises. Unfold `skip1`. Apply the tactic sequence `split_ifs with h' <;> simp only [Fin.val_mk] at * <;> omega`.

Use `⟨⟨a.val - 1, by have := a.isLt; omega⟩, ?_⟩` and prove the remaining obligations. Apply `Fin.ext` to reduce the goal to its premises. Unfold `skip1`. Apply the tactic sequence `split_ifs with h' <;> simp only [Fin.val_mk] at * <;> omega`.
-/
theorem exists_skip_one_eq {t : ℕ} {a b : Fin t} (h : a ≠ b) : ∃ l, skip1 b l = a := by
  rcases Nat.lt_or_gt_of_ne (fun e => h (Fin.ext e)) with hab | hab
  · refine ⟨⟨a.val, by have := b.isLt; omega⟩, ?_⟩
    apply Fin.ext
    unfold skip1
    split_ifs with h' <;> simp only [Fin.val_mk] at * <;> omega
  · refine ⟨⟨a.val - 1, by have := a.isLt; omega⟩, ?_⟩
    apply Fin.ext
    unfold skip1
    split_ifs with h' <;> simp only [Fin.val_mk] at * <;> omega

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `lc_self _ (skip_one_injective a)`. Take `⟨l₀, hl₀⟩` from `exists_skip_one_eq h`. Conclude with `lc_miss _ _ l₀ fun l e => skip_one_ne a l (e.trans hl₀)`.
-/
theorem lc_skip1 (a b : Fin (mdim k r i)) : lc k r i (skip1 a) (skip1 b) = if a = b then 1 else 0 := by
  split_ifs with h
  · subst h
    exact lc_self _ (skip_one_injective a)
  · obtain ⟨l₀, hl₀⟩ := exists_skip_one_eq h
    exact lc_miss _ _ l₀ fun l e => skip_one_ne a l (e.trans hl₀)

/- English proof (translation)
Unfold `fvec`. Use `split_ifs with h`. Simplify using `only [bvec]`. Rewrite using `[Pi.single_apply, if_neg]`. Introduce `e`.

Apply `hp` to reduce the goal to its premises. Rewrite using `[e]`. Use `show i.val ≤ i.val ∧ i.val + i.val ≤ 2 * r + k`. Use linear arithmetic over natural numbers and integers. Apply `hz` to reduce the goal to its premises.

Unfold `inV at hp`. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem fvec_out {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {p : Fin (2 * r + k + 1)}
    (hp : ¬ inV k r i p) : fvec k r z i p = 0 := by
  unfold fvec
  split_ifs with h
  · simp only [bvec]
    rw [Pi.single_apply, if_neg]
    intro e
    apply hp
    rw [e]
    show i.val ≤ i.val ∧ i.val + i.val ≤ 2 * r + k
    omega
  · apply hz
    unfold inV at hp
    have := i.isLt
    omega

/- English proof (translation)
Establish `key : ∑ p ∈ Finset.univ.image (posL k r i), F p = ∑ j, F (posL k r i j)` using `Finset.sum_image (by intro x _ y _ e; exact posL_inj i e)`. Rewrite using `[← key]`. Use `Finset.sum_subset (Finset.subset_univ _) fun p _ hp => h p fun hv => hp ?_` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_posL hv`. Conclude with `Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩`.
-/
theorem sum_posL (F : Fin (2 * r + k + 1) → ℂ) (h : ∀ p, ¬ inV k r i p → F p = 0) :
    ∑ j, F (posL k r i j) = ∑ p, F p := by
  have key : ∑ p ∈ Finset.univ.image (posL k r i), F p = ∑ j, F (posL k r i j) :=
    Finset.sum_image (by intro x _ y _ e; exact posL_inj i e)
  rw [← key]
  refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp => h p fun hv => hp ?_
  obtain ⟨j, hj⟩ := exists_posL hv
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩

/- English proof (translation)
Simplify using `only [herm, Matrix.dotProduct_mulVec, bvec, dotProduct_single, mul_one]`. Both sides reduce to the same expression.
-/
theorem herm_expand (M : Mx k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (M *ᵥ v) w = ∑ p, herm (Hpk k r) (M *ᵥ bvec p) w * v p := by
  simp only [herm, Matrix.dotProduct_mulVec, bvec, dotProduct_single, mul_one]
  rfl

/- English proof (translation)
Establish `hH : ∀ a b, star (Hpk k r a b) = Hpk k r b a` using `fun a b => by`. Establish `h` using `congrFun (congrFun (hpk_h (k := k) (r := r)) b) a`. Rewrite `h` using `[Matrix.conjTranspose_apply]`. Conclude with `h`. Simplify using `only [herm, dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum, hH]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_star (v w : Fin (2 * r + k + 1) → ℂ) : star (herm (Hpk k r) v w) = herm (Hpk k r) w v := by
  have hH : ∀ a b, star (Hpk k r a b) = Hpk k r b a := fun a b => by
    have h := congrFun (congrFun (hpk_h (k := k) (r := r)) b) a
    rw [Matrix.conjTranspose_apply] at h
    exact h
  simp only [herm, dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star,
    Finset.mul_sum, hH]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Establish `hg' : (g)ᴴ * Hpk k r * g = Hpk k r` using `hg`. Unfold `herm`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg', ← Matrix.dotProduct_mulVec]`.
-/
theorem herm_uh {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ x) (g *ᵥ y) = herm (Hpk k r) x y := by
  have hg' : (g)ᴴ * Hpk k r * g = Hpk k r := hg
  unfold herm
  rw [Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.mul_assoc, hg', ← Matrix.dotProduct_mulVec]

/- English proof (translation)
Unfold `herm dotProduct`. Use `Finset.sum_eq_zero fun q _ => ?_` and prove the remaining obligations. Distinguish the cases in `hq : inV k r i q`. Rewrite using `[show (Hpk k r *ᵥ bvec p) q = Hpk k r q p by`. Simplify using `[Matrix.mulVec, dotProduct, bvec, Pi.single_apply], hpk_out hq hp, mul_zero]`.

Rewrite using `[Pi.star_apply, fvec_out hz hq, star_zero, zero_mul]`.
-/
theorem herm_bvec_out {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {p : Fin (2 * r + k + 1)}
    (hp : ¬ inV k r i p) : herm (Hpk k r) (bvec p) (fvec k r z i) = 0 := by
  unfold herm dotProduct
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : inV k r i q
  · rw [show (Hpk k r *ᵥ bvec p) q = Hpk k r q p by
      simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply], hpk_out hq hp, mul_zero]
  · rw [Pi.star_apply, fvec_out hz hq, star_zero, zero_mul]

/- English proof (translation)
Unfold `zetaL`. Rewrite using `[herm_expand, ← sum_posL]`. Both sides reduce to the same expression. Introduce `p hp`. Rewrite using `[fvec_out hz' hp, mul_zero]`.
-/
theorem sum_dual_vector_eq_zeta (z : Fin (2 * r + k + 1) → ℂ) {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (g : Mx k r) :
    ∑ j, ybv k r z i g j * xv k r z' i j = zetaL k r z z' i g := by
  unfold zetaL
  rw [herm_expand, ← sum_posL]
  · rfl
  · intro p hp
    rw [fvec_out hz' hp, mul_zero]

/- English proof (translation)
Establish `hdet : IsUnit g.det`. Establish `h1 : (g)ᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `h2 : (Hpk k r).det * (Hpk k r).det = 1`. Rewrite using `[← Matrix.det_mul, hpk_sq', Matrix.det_one]`. Establish `h3` using `congrArg Matrix.det h1`.

Rewrite `h3` using `[Matrix.det_mul, Matrix.det_mul]`. Use `isUnit_iff_ne_zero.mpr fun h0 => ?_` and prove the remaining obligations. Rewrite `h3` using `[h0, mul_zero]`. Rewrite `h2` using `[← h3, zero_mul]`. Conclude with `zero_ne_one h2`.

Establish `hgi : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv g hdet`. Establish `e1 : ∑ j, xbv k r z' i j * yv k r z i g j = herm (Hpk k r) (g⁻¹ *ᵥ fvec k r z i) (fvec k r z' i)`. Establish `hx` using `herm_expand (k := k) (r := r) 1 (g⁻¹ *ᵥ fvec k r z i) (fvec k r z' i)`. Simplify using `only [Matrix.one_mulVec] at hx`. Rewrite using `[hx, ← sum_posL (i := i)]`.

Both sides reduce to the same expression. Introduce `p hp`. Rewrite using `[herm_bvec_out hz' hp, zero_mul]`. Rewrite using `[e1, zetaL, herm_star, ← herm_uh hg (g⁻¹ *ᵥ fvec k r z i) (fvec k r z' i), Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]`.
-/
theorem sum_xb_y (z : Fin (2 * r + k + 1) → ℂ) {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') {g : Mx k r}
    (hg : g ∈ UH (Hpk k r)) : ∑ j, xbv k r z' i j * yv k r z i g j = star (zetaL k r z z' i g) := by
  have hdet : IsUnit g.det := by
    have h1 : (g)ᴴ * Hpk k r * g = Hpk k r := hg
    have h2 : (Hpk k r).det * (Hpk k r).det = 1 := by
      rw [← Matrix.det_mul, hpk_sq', Matrix.det_one]
    have h3 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h3
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, mul_zero] at h3
    rw [← h3, zero_mul] at h2
    exact zero_ne_one h2
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
  have e1 : ∑ j, xbv k r z' i j * yv k r z i g j =
      herm (Hpk k r) (g⁻¹ *ᵥ fvec k r z i) (fvec k r z' i) := by
    have hx := herm_expand (k := k) (r := r) 1 (g⁻¹ *ᵥ fvec k r z i) (fvec k r z' i)
    simp only [Matrix.one_mulVec] at hx
    rw [hx, ← sum_posL (i := i)]
    · rfl
    · intro p hp
      rw [herm_bvec_out hz' hp, zero_mul]
  rw [e1, zetaL, herm_star, ← herm_uh hg (g⁻¹ *ᵥ fvec k r z i) (fvec k r z' i), Matrix.mulVec_mulVec, hgi,
    Matrix.one_mulVec]

end Lead

section Entries

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

/- English proof (translation)
Establish `H : PolyAt (mdim k r i - 1) (fun Y => ∑ p : Fin (mdim k r i), ∑ q : Fin (mdim k r i), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * β x p * a x q) • (qminorOp (EH k r) (posL k r i ∘ skip1 p) (posL k r i ∘ skip1 q) (Y + s) f x - Y ^ (mdim k r i - 1) • (lc k r i (skip1 p) (skip1 q) • f x)))` using `polyAt_sum _ _ fun p _ => polyAt_sum _ _ fun q _ => (qminor_poly hD hf hx (skip1 p) (skip1 q) s).smul _`. Establish `hc : ∀ p : Fin (mdim k r i), (-1 : ℂ) ^ ((p : ℕ) + (p : ℕ)) = 1` using `fun p => Even.neg_one_pow ⟨p, rfl⟩`. Establish `key : ∀ Y : ℂ, (∑ p : Fin (mdim k r i), ∑ q : Fin (mdim k r i), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * β x p * a x q) • (Y ^ (mdim k r i - 1) • (lc k r i (skip1 p) (skip1 q) • f x))) = Y ^ (mdim k r i - 1) • ((∑ j, β x j * a x j) • f x)` using `fun Y => by`. Simplify using `only [lc_skip1, ite_smul, one_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, hc, one_mul]`. Rewrite using `[Finset.sum_smul, Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun p _ => smul_comm _ _ _`. Use `H.congr fun Y => ?_` and prove the remaining obligations. Rewrite using `[← key Y]`. Simplify using `only [smul_sub, Finset.sum_sub_distrib]`. Both sides reduce to the same expression.
-/
theorem chat_poly (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f) {x : Mx k r}
    (hx : x ∈ Glev k r i ∩ D) (a β : Mx k r → Fin (mdim k r i) → ℂ) (s : ℂ) :
    PolyAt (mdim k r i - 1) (fun Y => chatL (EH k r) (posL k r i) (Y + s) a β f x -
      Y ^ (mdim k r i - 1) • ((∑ j, β x j * a x j) • f x)) := by
  have H : PolyAt (mdim k r i - 1) (fun Y => ∑ p : Fin (mdim k r i), ∑ q : Fin (mdim k r i),
      ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * β x p * a x q) •
        (qminorOp (EH k r) (posL k r i ∘ skip1 p) (posL k r i ∘ skip1 q) (Y + s) f x -
          Y ^ (mdim k r i - 1) • (lc k r i (skip1 p) (skip1 q) • f x))) :=
    polyAt_sum _ _ fun p _ => polyAt_sum _ _ fun q _ => (qminor_poly hD hf hx (skip1 p) (skip1 q) s).smul _
  have hc : ∀ p : Fin (mdim k r i), (-1 : ℂ) ^ ((p : ℕ) + (p : ℕ)) = 1 := fun p => Even.neg_one_pow ⟨p, rfl⟩
  have key : ∀ Y : ℂ, (∑ p : Fin (mdim k r i), ∑ q : Fin (mdim k r i),
      ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * β x p * a x q) •
        (Y ^ (mdim k r i - 1) • (lc k r i (skip1 p) (skip1 q) • f x))) =
      Y ^ (mdim k r i - 1) • ((∑ j, β x j * a x j) • f x) := fun Y => by
    simp only [lc_skip1, ite_smul, one_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, hc, one_mul]
    rw [Finset.sum_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun p _ => smul_comm _ _ _
  refine H.congr fun Y => ?_
  rw [← key Y]
  simp only [smul_sub, Finset.sum_sub_distrib]
  rfl

/- English proof (translation)
Simplify using `only [chat2L]`. Use `polyAt_sum _ _ fun p _ => polyAt_sum _ _ fun p' _ => polyAt_sum _ _ fun q _ => polyAt_sum _ _ fun q' _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : p < p' ∧ q < q'`. Simplify using `only [if_pos hc]`. Establish `h1 : p.val < p'.val` using `hc.1`.

Establish `h2` using `p'.isLt`. Establish `hm : mdim k r i - 2 + 1 = mdim k r i - 1` using `by omega`. Rewrite using `[← hm]`. Conclude with `(qminor_poly' hD hf hx (skip2 p p') (skip2 q q') s).smul _`. Simplify using `only [if_neg hc]`.

Conclude with `polyAt_zero _`.
-/
theorem capelli_two_polynomial (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f) {x : Mx k r}
    (hx : x ∈ Glev k r i ∩ D) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ) (s : ℂ) :
    PolyAt (mdim k r i - 1) (fun Y => chat2L (EH k r) (posL k r i) (Y + s) a a' β β' f x) := by
  simp only [chat2L]
  refine polyAt_sum _ _ fun p _ => polyAt_sum _ _ fun p' _ => polyAt_sum _ _ fun q _ =>
    polyAt_sum _ _ fun q' _ => ?_
  by_cases hc : p < p' ∧ q < q'
  · simp only [if_pos hc]
    have h1 : p.val < p'.val := hc.1
    have h2 := p'.isLt
    have hm : mdim k r i - 2 + 1 = mdim k r i - 1 := by omega
    rw [← hm]
    exact (qminor_poly' hD hf hx (skip2 p p') (skip2 q q') s).smul _
  · simp only [if_neg hc]
    exact polyAt_zero _

open Classical in

def coefOf (N : ℕ) (φ : ℂ → E) : ℕ → E := if h : PolyAt N φ then h.choose else 0

/- English proof (translation)
Rewrite using `[coefOf, dif_pos h]`. Conclude with `h.choose_spec Y`.
-/
theorem coefOf_spec {N : ℕ} {φ : ℂ → E} (h : PolyAt N φ) (Y : ℂ) :
    φ Y = ∑ j ∈ Finset.range N, Y ^ j • coefOf N φ j := by
  rw [coefOf, dif_pos h]
  exact h.choose_spec Y

def lowC (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) :
    Fin 2 → Fin 2 → ℕ → (Mx k r → E) → Mx k r → E :=
  fun p q j f g =>
    match p, q with
    | 0, 0 => coefOf (mdim k r i) (fun Y => tL k r z z' i Y 0 0 f g - Y ^ mdim k r i • f g) j
    | 0, 1 => coefOf (mdim k r i - 1) (fun Y => tL k r z z' i Y 0 1 f g +
        (zetaL k r z z' i g * Y ^ (mdim k r i - 1)) • f g) j
    | 1, 0 => coefOf (mdim k r i - 1) (fun Y => tL k r z z' i Y 1 0 f g +
        (star (zetaL k r z z' i g) * Y ^ (mdim k r i - 1)) • f g) j
    | 1, 1 => coefOf (mdim k r i - 1) (fun Y => tL k r z z' i Y 1 1 f g) j

end Entries

end Qx2

/- English proof (translation)
Introduce `E _ _ m l f hf`. Take `⟨h1, h2, h3, h4, h5, -⟩` from `weylFun m E l f hf`. Use `⟨⟨h1, h2, h3⟩, ⟨h5, h4, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Qx2.pbOp_neg, Qx2.cbiOp_neg, neg_neg, neg_neg, Qx2.pb_cbi l hf, sub_eq_add_neg]`. Introduce `i j hij`.

Conclude with `commFun m E l l i j f hf (Or.inr hij)`.
-/
theorem transfer_triples : Formalism.FourierDecayAlt.Q.TTriples := by
  intro E _ _ m l f hf
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := weylFun m E l f hf
  refine ⟨⟨h1, h2, h3⟩, ⟨h5, h4, ?_⟩, ?_⟩
  · rw [Qx2.pbOp_neg, Qx2.cbiOp_neg, neg_neg, neg_neg, Qx2.pb_cbi l hf, sub_eq_add_neg]
  · intro i j hij
    exact commFun m E l l i j f hf (Or.inr hij)

/- English proof (translation)
Introduce `E _ _ k r z z' i D Y p q f f₂ s hD hf hf₂ g hg`. Establish `h` using `Qx2.ll_tL (E := E) (k := k) (r := r) (i := i) (D := D) hD z z' Y p q`. Conclude with `⟨h.lin f f₂ s hf hf₂ g hg, fun he => h.loc f f₂ he g hg⟩`.
-/
theorem transfer_linear_local : Formalism.FourierDecayAlt.Q.TLinLoc := by
  intro E _ _ k r z z' i D Y p q f f₂ s hD hf hf₂ g hg
  have h := Qx2.ll_tL (E := E) (k := k) (r := r) (i := i) (D := D) hD z z' Y p q
  exact ⟨h.lin f f₂ s hf hf₂ g hg, fun he => h.loc f f₂ he g hg⟩

/- English proof (translation)
Introduce `E _ _ k r z z' i hz hz'`. Use `⟨Qx2.lowC k r z z' i, fun D f hD hf g hg Y => ?_⟩` and prove the remaining obligations. Establish `hUH : g ∈ UH (Hpk k r)` using `hg.1.1`. Establish `hu : ∀ Y : ℂ, uC k r i Y - 1 = Y + (((mdim k r i : ℂ) - 1) / 2 - 1)` using `fun Y => by`. Unfold `uC`.

Expand and normalize the polynomial expressions, which then agree. Establish `hu0 : ∀ Y : ℂ, uC k r i Y = Y + ((mdim k r i : ℂ) - 1) / 2` using `fun Y => rfl`. Establish `s00 : Qx2.PolyAt (mdim k r i) (fun Y => tL k r z z' i Y 0 0 f g - Y ^ mdim k r i • f g)` using `(Qx2.qminor_poly hD hf hg id id (((mdim k r i : ℂ) - 1) / 2)).congr fun Y => by`. Rewrite using `[Qx2.lc_self id Function.injective_id, one_smul]`. Both sides reduce to the same expression.

Establish `s01 : Qx2.PolyAt (mdim k r i - 1) (fun Y => tL k r z z' i Y 0 1 f g + (zetaL k r z z' i g * Y ^ (mdim k r i - 1)) • f g)` using `(Qx2.chat_poly hD hf hg (fun _ => xv k r z' i) (ybv k r z i) (((mdim k r i : ℂ) - 1) / 2 - 1)).neg.congr fun Y => by`. Rewrite using `[show tL k r z z' i Y 0 1 f g = -(chatL (EH k r) (posL k r i) (uC k r i Y - 1) (fun _ => xv k r z' i) (ybv k r z i) f g) from rfl, hu, Qx2.sum_dual_vector_eq_zeta z hz' g]`. Use `module`. Establish `s10 : Qx2.PolyAt (mdim k r i - 1) (fun Y => tL k r z z' i Y 1 0 f g + (star (zetaL k r z z' i g) * Y ^ (mdim k r i - 1)) • f g)` using `(Qx2.chat_poly hD hf hg (yv k r z i) (fun _ => xbv k r z' i) (((mdim k r i : ℂ) - 1) / 2)).neg.congr fun Y => by`. Rewrite using `[show tL k r z z' i Y 1 0 f g = -(chatL (EH k r) (posL k r i) (uC k r i Y) (yv k r z i) (fun _ => xbv k r z' i) f g) from rfl, hu0, Qx2.sum_xb_y z hz' hUH]`.

Use `module`. Establish `s11 : Qx2.PolyAt (mdim k r i - 1) (fun Y => tL k r z z' i Y 1 1 f g)` using `(Qx2.capelli_two_polynomial hD hf hg (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i) (fun _ => xbv k r z' i) (((mdim k r i : ℂ) - 1) / 2 - 1)).neg.congr fun Y => by`. Rewrite using `[show tL k r z z' i Y 1 1 f g = -(chat2L (EH k r) (posL k r i) (uC k r i Y - 1) (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i) (fun _ => xbv k r z' i) f g) from rfl, hu]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `sub_eq_iff_eq_add'.mp (Qx2.coefOf_spec s00 Y)`.

Conclude with `eq_neg_add_of_add_eq ((add_comm _ _).trans (Qx2.coefOf_spec s01 Y))`. Conclude with `eq_neg_add_of_add_eq ((add_comm _ _).trans (Qx2.coefOf_spec s10 Y))`. Conclude with `Qx2.coefOf_spec s11 Y`.
-/
theorem leading_term_alt : Formalism.FourierDecayAlt.Q.Leading := by
  intro E _ _ k r z z' i hz hz'
  refine ⟨Qx2.lowC k r z z' i, fun D f hD hf g hg Y => ?_⟩
  have hUH : g ∈ UH (Hpk k r) := hg.1.1
  have hu : ∀ Y : ℂ, uC k r i Y - 1 = Y + (((mdim k r i : ℂ) - 1) / 2 - 1) := fun Y => by
    unfold uC
    ring
  have hu0 : ∀ Y : ℂ, uC k r i Y = Y + ((mdim k r i : ℂ) - 1) / 2 := fun Y => rfl
  have s00 : Qx2.PolyAt (mdim k r i) (fun Y => tL k r z z' i Y 0 0 f g - Y ^ mdim k r i • f g) :=
    (Qx2.qminor_poly hD hf hg id id (((mdim k r i : ℂ) - 1) / 2)).congr fun Y => by
      rw [Qx2.lc_self id Function.injective_id, one_smul]
      rfl
  have s01 : Qx2.PolyAt (mdim k r i - 1) (fun Y => tL k r z z' i Y 0 1 f g +
      (zetaL k r z z' i g * Y ^ (mdim k r i - 1)) • f g) :=
    (Qx2.chat_poly hD hf hg (fun _ => xv k r z' i) (ybv k r z i)
      (((mdim k r i : ℂ) - 1) / 2 - 1)).neg.congr fun Y => by
      rw [show tL k r z z' i Y 0 1 f g = -(chatL (EH k r) (posL k r i) (uC k r i Y - 1)
        (fun _ => xv k r z' i) (ybv k r z i) f g) from rfl, hu, Qx2.sum_dual_vector_eq_zeta z hz' g]
      module
  have s10 : Qx2.PolyAt (mdim k r i - 1) (fun Y => tL k r z z' i Y 1 0 f g +
      (star (zetaL k r z z' i g) * Y ^ (mdim k r i - 1)) • f g) :=
    (Qx2.chat_poly hD hf hg (yv k r z i) (fun _ => xbv k r z' i)
      (((mdim k r i : ℂ) - 1) / 2)).neg.congr fun Y => by
      rw [show tL k r z z' i Y 1 0 f g = -(chatL (EH k r) (posL k r i) (uC k r i Y)
        (yv k r z i) (fun _ => xbv k r z' i) f g) from rfl, hu0, Qx2.sum_xb_y z hz' hUH]
      module
  have s11 : Qx2.PolyAt (mdim k r i - 1) (fun Y => tL k r z z' i Y 1 1 f g) :=
    (Qx2.capelli_two_polynomial hD hf hg (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i) (fun _ => xbv k r z' i)
      (((mdim k r i : ℂ) - 1) / 2 - 1)).neg.congr fun Y => by
      rw [show tL k r z z' i Y 1 1 f g = -(chat2L (EH k r) (posL k r i) (uC k r i Y - 1) (yv k r z i)
        (fun _ => xv k r z' i) (ybv k r z i) (fun _ => xbv k r z' i) f g) from rfl, hu]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sub_eq_iff_eq_add'.mp (Qx2.coefOf_spec s00 Y)
  · exact eq_neg_add_of_add_eq ((add_comm _ _).trans (Qx2.coefOf_spec s01 Y))
  · exact eq_neg_add_of_add_eq ((add_comm _ _).trans (Qx2.coefOf_spec s10 Y))
  · exact Qx2.coefOf_spec s11 Y

end Formalism.FourierDecayAlt.P
