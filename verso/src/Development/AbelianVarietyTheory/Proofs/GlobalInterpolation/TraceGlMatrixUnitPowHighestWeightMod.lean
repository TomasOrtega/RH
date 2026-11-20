import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GlMatrixUnitPowCommutatorAndTraceCentralStatement

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

def hwRowSum (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) (i : Fin N) : R :=
  ∑ l, (hcMat R μ ^ k) i l

/- English proof (translation)
Simplify using `[hwRowSum, Matrix.one_apply]`.
-/
theorem hwRowSum_zero (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (i : Fin N) :
    hwRowSum R μ 0 i = 1 := by
  simp [hwRowSum, Matrix.one_apply]

/- English proof (translation)
Simplify using `only [hwRowSum, pow_succ', Matrix.mul_apply, Finset.mul_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem hwRowSum_succ_eq_mul (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) (i : Fin N) :
    hwRowSum R μ (k + 1) i = ∑ m, hcMat R μ i m * hwRowSum R μ k m := by
  simp only [hwRowSum, pow_succ', Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Rewrite using `[hwRowSum_succ_eq_mul]`. Use `set r := hwRowSum R μ k with hr`. Establish `h1 : ∀ l, hcMat R μ i l * r l = (if l = i then μ i * r i else 0) + (if l = i then ((N - 1 - i.val : ℕ) : R) * r i else 0) - (if i < l then r l else 0)`. Introduce `l`. Distinguish the cases in `hl : l = i`.

Substitute `hl` using the available equality. Simplify using `[hcMat, shift, add_mul]`. Distinguish the cases in `hil : i < l`. Simplify using `[hcMat, hl, hil]`. Simplify using `[hcMat, hl, hil]`.

Establish `h2 : ∀ l, (if l < i then 0 else if l = i then μ i * r i else r i - r l) = (if l = i then μ i * r i else 0) + (if i < l then r i else 0) - (if i < l then r l else 0)`. Introduce `l`. Break down `lt_trichotomy l i with h | h | h` into its components or cases. Simplify using `[h, h.ne, h.not_gt]`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h, h.ne', h.not_gt]`. Simplify using `only [h1, h2, Finset.sum_sub_distrib, Finset.sum_add_distrib]`. Use `congr 2`. Establish `h3 : ∑ l : Fin N, (if i < l then r i else 0) = ((N - 1 - i.val : ℕ) : R) * r i`.

Rewrite using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`. Use `congr 2`. Establish `: Finset.univ.filter (fun l : Fin N => i < l) = Finset.Ioi i`. Use extensionality with `l`. Simplify using the standard rewrite rules.

Rewrite using `[this, Fin.card_Ioi]`. Rewrite using `[h3]`. Simplify using the standard rewrite rules.
-/
theorem hwRowSum_succ (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) (i : Fin N) :
    hwRowSum R μ (k + 1) i =
      ∑ l, (if l < i then 0 else if l = i then μ i * hwRowSum R μ k i
        else hwRowSum R μ k i - hwRowSum R μ k l) := by
  rw [hwRowSum_succ_eq_mul]
  set r := hwRowSum R μ k with hr
  have h1 : ∀ l, hcMat R μ i l * r l =
      (if l = i then μ i * r i else 0) + (if l = i then ((N - 1 - i.val : ℕ) : R) * r i else 0)
        - (if i < l then r l else 0) := by
    intro l
    by_cases hl : l = i
    · subst hl
      simp [hcMat, shift, add_mul]
    · by_cases hil : i < l
      · simp [hcMat, hl, hil]
      · simp [hcMat, hl, hil]
  have h2 : ∀ l, (if l < i then 0 else if l = i then μ i * r i else r i - r l) =
      (if l = i then μ i * r i else 0) + (if i < l then r i else 0)
        - (if i < l then r l else 0) := by
    intro l
    rcases lt_trichotomy l i with h | h | h
    · simp [h, h.ne, h.not_gt]
    · subst h
      simp
    · simp [h, h.ne', h.not_gt]
  simp only [h1, h2, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr 2
  have h3 : ∑ l : Fin N, (if i < l then r i else 0) = ((N - 1 - i.val : ℕ) : R) * r i := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 2
    have : Finset.univ.filter (fun l : Fin N => i < l) = Finset.Ioi i := by
      ext l
      simp
    rw [this, Fin.card_Ioi]
  rw [h3]
  simp

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `a b f hf`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Simplify `hf` using `[Matrix.one_apply]`. Simplify using `[Matrix.one_apply, h]`. Consider the case `succ k ih`. Introduce `a b f hf`. Rewrite using `[pow_succ', Matrix.mul_apply, LinearMap.sum_apply]`.

Conclude with `Submodule.sum_mem _ fun l _ => hM a l _ (ih l b f hf)`.
-/
theorem pow_entry_stable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {N : ℕ}
    (E : Matrix (Fin N) (Fin N) (Module.End R V)) (M : Submodule R V)
    (hM : ∀ a b, ∀ f ∈ M, E a b f ∈ M) (k : ℕ) :
    ∀ a b, ∀ f ∈ M, (E ^ k) a b f ∈ M := by
  induction k with
  | zero =>
    intro a b f hf
    by_cases h : a = b
    · subst h
      simpa [Matrix.one_apply] using hf
    · simp [Matrix.one_apply, h]
  | succ k ih =>
    intro a b f hf
    rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun l _ => hM a l _ (ih l b f hf)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Prove the components needed by the constructor for the conclusion. Introduce `i j hij`. Simplify using `[Matrix.one_apply, hij.ne]`.

Introduce `i`. Simplify using `[hwRowSum_zero, Matrix.one_apply]`. Consider the case `succ k ih`. Take `⟨ih1, ih2⟩` from `ih`. Establish `hcomm` using `(GlobalTheory.T.glMatrixUnit_pow_commutator_and_trace_central (Module.End R V) N E hE k).1`.

Establish `hst` using `pow_entry_stable E M hM k`. Establish `key : ∀ i j l, i < l → E i l ((E ^ k) l j v) - ((E ^ k) i j v - (if j = i then (E ^ k) l l v else 0)) ∈ M`. Introduce `i j l hil`. Establish `h` using `LinearMap.congr_fun (hcomm i l l j) v`. Establish `h' : E i l ((E ^ k) l j v) - (E ^ k) l j (E i l v) = (E ^ k) i j v - (if j = i then (E ^ k) l l v else 0)`.

Distinguish the cases in `hji : j = i`. Simplify `h` using `[hji, Module.End.mul_apply]`. Simplify `h` using `[hji, Module.End.mul_apply]`. Establish `h2 : (E ^ k) l j (E i l v) ∈ M` using `hst l j _ (hup i l hil)`. Rewrite using `[← h']`.

Simplify using `using h2`. Prove the components needed by the constructor for the conclusion. Introduce `i j hij`. Rewrite using `[pow_succ', Matrix.mul_apply, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[Module.End.mul_apply]`. Break down `lt_trichotomy l j with h | h | h` into its components or cases. Conclude with `hM i l _ (ih1 l j h)`. Substitute `h` using the available equality. Establish `h1` using `hM i l _ (ih2 l)`.

Rewrite `h1` using `[map_sub, map_smul]`. Establish `h2` using `M.smul_mem (hwRowSum R μ k l) (hup i l hij)`. Simplify using `using M.add_mem h1 h2`. Establish `h1` using `key i j l (hij.trans h)`. Rewrite `h1` using `[if_neg hij.ne']`.

Simplify using `using M.add_mem h1 (ih1 i j hij)`. Introduce `i`. Rewrite using `[pow_succ', Matrix.mul_apply, LinearMap.sum_apply, hwRowSum_succ, Finset.sum_smul, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply]`.

Break down `lt_trichotomy l i with h | h | h` into its components or cases. Simplify `hM i l _ (ih1 l i h)` using `[h]`. Substitute `h` using the available equality. Establish `h1` using `hM l l _ (ih2 l)`. Rewrite `h1` using `[map_sub, map_smul]`.

Establish `h2` using `M.smul_mem (hwRowSum R μ k l) (hd l)`. Establish `h3` using `M.add_mem h1 h2`. Establish `e : E l l ((E ^ k) l l v) - hwRowSum R μ k l • E l l v + hwRowSum R μ k l • (E l l v - μ l • v) = E l l ((E ^ k) l l v) - (μ l * hwRowSum R μ k l) • v`. Rewrite using `[smul_sub, smul_smul, mul_comm (hwRowSum R μ k l)]`. Normalize the expressions using the abelian group laws.

Rewrite `h3` using `[e]`. Simplify using `using h3`. Establish `h1` using `key i i l h`. Rewrite `h1` using `[if_pos rfl]`. Establish `h3` using `M.sub_mem (M.add_mem h1 (ih2 i)) (ih2 l)`.

Establish `e : E i l ((E ^ k) l i v) - ((E ^ k) i i v - (E ^ k) l l v) + ((E ^ k) i i v - hwRowSum R μ k i • v) - ((E ^ k) l l v - hwRowSum R μ k l • v) = E i l ((E ^ k) l i v) - (hwRowSum R μ k i - hwRowSum R μ k l) • v`. Rewrite using `[sub_smul]`. Normalize the expressions using the abelian group laws. Rewrite `h3` using `[e]`. Simplify `h3` using `[h.not_gt, h.ne']`.
-/
theorem hw_pow_entries {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {N : ℕ}
    (E : Matrix (Fin N) (Fin N) (Module.End R V)) (hE : GlRel E) (M : Submodule R V)
    (hM : ∀ a b, ∀ f ∈ M, E a b f ∈ M) (μ : Fin N → R) (v : V)
    (hup : ∀ a b, a < b → E a b v ∈ M) (hd : ∀ a, E a a v - μ a • v ∈ M) (k : ℕ) :
    (∀ i j, i < j → (E ^ k) i j v ∈ M) ∧ (∀ i, (E ^ k) i i v - hwRowSum R μ k i • v ∈ M) := by
  induction k with
  | zero =>
    constructor
    · intro i j hij
      simp [Matrix.one_apply, hij.ne]
    · intro i
      simp [hwRowSum_zero, Matrix.one_apply]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hcomm := (GlobalTheory.T.glMatrixUnit_pow_commutator_and_trace_central (Module.End R V) N E hE k).1
    have hst := pow_entry_stable E M hM k
    have key : ∀ i j l, i < l →
        E i l ((E ^ k) l j v) - ((E ^ k) i j v - (if j = i then (E ^ k) l l v else 0)) ∈ M := by
      intro i j l hil
      have h := LinearMap.congr_fun (hcomm i l l j) v
      have h' : E i l ((E ^ k) l j v) - (E ^ k) l j (E i l v) =
          (E ^ k) i j v - (if j = i then (E ^ k) l l v else 0) := by
        by_cases hji : j = i
        · simpa [hji, Module.End.mul_apply] using h
        · simpa [hji, Module.End.mul_apply] using h
      have h2 : (E ^ k) l j (E i l v) ∈ M := hst l j _ (hup i l hil)
      rw [← h']
      simpa using h2
    constructor
    · intro i j hij
      rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [Module.End.mul_apply]
      rcases lt_trichotomy l j with h | h | h
      · exact hM i l _ (ih1 l j h)
      · subst h
        have h1 := hM i l _ (ih2 l)
        rw [map_sub, map_smul] at h1
        have h2 := M.smul_mem (hwRowSum R μ k l) (hup i l hij)
        simpa using M.add_mem h1 h2
      · have h1 := key i j l (hij.trans h)
        rw [if_neg hij.ne'] at h1
        simpa using M.add_mem h1 (ih1 i j hij)
    · intro i
      rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply, hwRowSum_succ, Finset.sum_smul,
        ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [Module.End.mul_apply]
      rcases lt_trichotomy l i with h | h | h
      · simpa [h] using hM i l _ (ih1 l i h)
      · subst h
        have h1 := hM l l _ (ih2 l)
        rw [map_sub, map_smul] at h1
        have h2 := M.smul_mem (hwRowSum R μ k l) (hd l)
        have h3 := M.add_mem h1 h2
        have e : E l l ((E ^ k) l l v) - hwRowSum R μ k l • E l l v +
            hwRowSum R μ k l • (E l l v - μ l • v) =
            E l l ((E ^ k) l l v) - (μ l * hwRowSum R μ k l) • v := by
          rw [smul_sub, smul_smul, mul_comm (hwRowSum R μ k l)]
          abel
        rw [e] at h3
        simpa using h3
      · have h1 := key i i l h
        rw [if_pos rfl] at h1
        have h3 := M.sub_mem (M.add_mem h1 (ih2 i)) (ih2 l)
        have e : E i l ((E ^ k) l i v) - ((E ^ k) i i v - (E ^ k) l l v) +
            ((E ^ k) i i v - hwRowSum R μ k i • v) - ((E ^ k) l l v - hwRowSum R μ k l • v) =
            E i l ((E ^ k) l i v) - (hwRowSum R μ k i - hwRowSum R μ k l) • v := by
          rw [sub_smul]
          abel
        rw [e] at h3
        simpa [h.not_gt, h.ne'] using h3

/- English proof (translation)
Introduce `R V _ _ _ N E hE M hM μ v hup hd k`. Establish `h` using `(hw_pow_entries E hE M hM μ v hup hd k).2`. Establish `e : (E ^ k).trace v - hcVal R μ k • v = ∑ i, ((E ^ k) i i v - hwRowSum R μ k i • v)`. Simplify using `only [Matrix.trace, Matrix.diag, LinearMap.sum_apply, hcVal, Finset.sum_sub_distrib, Finset.sum_smul, hwRowSum]`. Rewrite using `[e]`.

Conclude with `Submodule.sum_mem _ fun i _ => h i`.
-/
theorem trace_pow_hw : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (N : ℕ)
    (E : Matrix (Fin N) (Fin N) (Module.End R V)), GlRel E → ∀ (M : Submodule R V),
    (∀ a b, ∀ f ∈ M, E a b f ∈ M) → ∀ (μ : Fin N → R) (v : V), (∀ a b, a < b → E a b v ∈ M) →
    (∀ a, E a a v - μ a • v ∈ M) → ∀ k : ℕ, (E ^ k).trace v - hcVal R μ k • v ∈ M := by
  intro R V _ _ _ N E hE M hM μ v hup hd k
  have h := (hw_pow_entries E hE M hM μ v hup hd k).2
  have e : (E ^ k).trace v - hcVal R μ k • v = ∑ i, ((E ^ k) i i v - hwRowSum R μ k i • v) := by
    simp only [Matrix.trace, Matrix.diag, LinearMap.sum_apply, hcVal, Finset.sum_sub_distrib,
      Finset.sum_smul, hwRowSum]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => h i

end GlobalTheory.Alc
