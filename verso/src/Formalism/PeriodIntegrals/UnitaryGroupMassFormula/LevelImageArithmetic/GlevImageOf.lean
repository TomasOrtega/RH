import Mathlib
import Formalism.HermitianCurvature.StatementQ

open Matrix Finset

noncomputable section

namespace QnGlevImageW

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

local macro "ifarith" : tactic =>
  `(tactic| (split_ifs <;> first | rfl | (exfalso; omega)))

/- English proof (translation)
Use extensionality with `p`. Simplify using `[bvec, Matrix.mulVec_single]`.
-/
lemma mulVec_bvec {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (q : Fin m) :
    g *ᵥ bvec q = fun p => g p q := by
  ext p
  simp [bvec, Matrix.mulVec_single]

/- English proof (translation)
Use `x.isLt` as an intermediate fact. Simplify using `only [levPos]`. Conclude with `⟨by omega, by omega⟩`.
-/
lemma levPos_mem (k i r' : ℕ) (x : Fin (2 * r' + k + 1)) :
    i ≤ (levPos k i r' x).val ∧ (levPos k i r' x).val < 2 * r' + k + 1 + i := by
  have := x.isLt
  simp only [levPos]
  exact ⟨by omega, by omega⟩

/- English proof (translation)
Use `symm`. Use `Finset.sum_bij_ne_zero (fun x' _ _ => levPos k i r' x') (fun _ _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ _ => rfl)` and prove the remaining obligations. Introduce `a _ _ b _ _ h`. Simplify using `only [levPos, Fin.mk.injEq] at h`. Conclude with `Fin.ext (by omega)`.

Introduce `y _ hy`. Establish `hin : i ≤ y.val ∧ y.val < 2 * r' + k + 1 + i`. Assume the negation of the conclusion as `h`. Conclude with `hy (hf y h)`. Establish `hy' : levPos k i r' ⟨y.val - i, by omega⟩ = y` using `Fin.ext (by simp only [levPos]; omega)`.

Conclude with `⟨⟨y.val - i, by omega⟩, Finset.mem_univ _, by rw [hy']; exact hy, hy'⟩`.
-/
lemma sum_block (k i r' : ℕ) (f : Fin (2 * (i + r') + k + 1) → ℂ)
    (hf : ∀ x : Fin (2 * (i + r') + k + 1), ¬(i ≤ x.val ∧ x.val < 2 * r' + k + 1 + i) → f x = 0) :
    ∑ x, f x = ∑ x' : Fin (2 * r' + k + 1), f (levPos k i r' x') := by
  symm
  refine Finset.sum_bij_ne_zero (fun x' _ _ => levPos k i r' x') (fun _ _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ _ => rfl)
  · intro a _ _ b _ _ h
    simp only [levPos, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  · intro y _ hy
    have hin : i ≤ y.val ∧ y.val < 2 * r' + k + 1 + i := by
      by_contra h
      exact hy (hf y h)
    have hy' : levPos k i r' ⟨y.val - i, by omega⟩ = y := Fin.ext (by simp only [levPos]; omega)
    exact ⟨⟨y.val - i, by omega⟩, Finset.mem_univ _, by rw [hy']; exact hy, hy'⟩

/- English proof (translation)
Use `s.isLt` as an intermediate fact. Use `t.isLt` as an intermediate fact. Use `show Hpk k (i + r') ⟨s.val + i, by omega⟩ ⟨t.val + i, by omega⟩ = _`. Simplify using `only [Hpk, Fin.ext_iff]`. Use `ifarith`.
-/
lemma hpk_shift (k i r' : ℕ) (s t : Fin (2 * r' + k + 1)) :
    Hpk k (i + r') (levPos k i r' s) (levPos k i r' t) = Hpk k r' s t := by
  have := s.isLt
  have := t.isLt
  show Hpk k (i + r') ⟨s.val + i, by omega⟩ ⟨t.val + i, by omega⟩ = _
  simp only [Hpk, Fin.ext_iff]
  ifarith

/- English proof (translation)
Establish `hX` using `X.isLt`. Establish `hy` using `y.isLt`. Establish `hp'` using `p.isLt`. Unfold `Hpk`. Simplify using `only [Fin.ext_iff]`.

Use `ifarith`.
-/
lemma hpk_partner (k i r' : ℕ) (X p : Fin (2 * (i + r') + k + 1)) (hXv : X.val = 2 * (i + r') + k - p.val)
    (hp : ¬(i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) (y : Fin (2 * (i + r') + k + 1)) :
    Hpk k (i + r') X y = if y = p then 1 else 0 := by
  have hX := X.isLt
  have hy := y.isLt
  have hp' := p.isLt
  unfold Hpk
  simp only [Fin.ext_iff]
  ifarith

/- English proof (translation)
Introduce `k i r'`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hg, hfix⟩`. Establish `hg' : gᴴ * Hpk k (i + r') * g = Hpk k (i + r')` using `hg`.

Establish `hcol : ∀ q : Fin (2 * (i + r') + k + 1), ¬(i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i) → ∀ p, g p q = if p = q then 1 else 0`. Introduce `q hq p`. Establish `hqlt` using `q.isLt`. Distinguish the cases in `hqi : q.val < i`. Establish `h` using `(hfix ⟨q.val, by omega⟩ (by simpa using hqi)).1`.

Establish `e : eI k (i + r') ⟨q.val, by omega⟩ = q` using `Fin.ext (by simp [eI])`. Rewrite `h` using `[e, mulVec_bvec]`. Use `congrFun h p` as an intermediate fact. Simplify `this` using `[bvec, Pi.single_apply]`. Establish `h` using `(hfix ⟨2 * (i + r') + k - q.val, by omega⟩ (by simp; omega)).2`.

Establish `e : esI k (i + r') ⟨2 * (i + r') + k - q.val, by omega⟩ = q` using `Fin.ext (by simp [esI]; omega)`. Rewrite `h` using `[e, mulVec_bvec]`. Use `congrFun h p` as an intermediate fact. Simplify `this` using `[bvec, Pi.single_apply]`. Establish `hrow : ∀ p : Fin (2 * (i + r') + k + 1), ¬(i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) → ∀ Q, g p Q = if Q = p then 1 else 0`.

Introduce `p hp Q`. Establish `hplt` using `p.isLt`. Take `⟨X, hXv⟩ : ∃ X : Fin (2 * (i + r') + k + 1), X.val = 2 * (i + r') + k - p.val` from `⟨⟨2 * (i + r') + k - p.val, by omega⟩, rfl⟩`. Establish `hX : ¬(i ≤ X.val ∧ X.val < 2 * r' + k + 1 + i)` using `by omega`. Establish `h1 : ∀ y, (gᴴ * Hpk k (i + r')) X y = Hpk k (i + r') X y`.

Introduce `y`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [conjTranspose_apply, hcol X hX]`. Rewrite using `[Finset.sum_eq_single X (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ X) h)]`. Simplify using the standard rewrite rules.

Establish `h2` using `congrFun (congrFun hg' X) Q`. Rewrite `h2` using `[Matrix.mul_apply]`. Simplify using `only [h1, hpk_partner k i r' X p hXv hp, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2`. Conclude with `h2`. Establish `hblk : ∀ p q : Fin (2 * (i + r') + k + 1), ¬(i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) → (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i) → g p q = 0`.

Introduce `p q hp hq`. Rewrite using `[hrow p hp q, if_neg]`. Introduce and unpack `rfl`. Conclude with `hp hq`. Use `⟨Matrix.of fun x y => g (levPos k i r' x) (levPos k i r' y), ?_, ?_⟩` and prove the remaining obligations.

Use `show _ = _`. Use extensionality with `s t`. Establish `h` using `congrFun (congrFun hg' (levPos k i r' s)) (levPos k i r' t)`. Rewrite `h` using `[hpk_shift]`. Rewrite using `[← h, Matrix.mul_apply, Matrix.mul_apply, sum_block k i r' (fun Y => (gᴴ * Hpk k (i + r')) (levPos k i r' s) Y * g Y (levPos k i r' t)) (fun Y hY => by simp only [hblk Y _ hY (levPos_mem k i r' t), mul_zero])]`.

Use `Finset.sum_congr rfl (fun y _ => ?_)` and prove the remaining obligations. Use `congr 1`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply, sum_block k i r' (fun x => (gᴴ) (levPos k i r' s) x * Hpk k (i + r') x (levPos k i r' y)) (fun x hx => by simp only [conjTranspose_apply, hblk x _ hx (levPos_mem k i r' s), star_zero, zero_mul])]`. Use `Finset.sum_congr rfl (fun x _ => ?_)` and prove the remaining obligations. Simplify using `only [conjTranspose_apply, hpk_shift, Matrix.of_apply]`.

Use extensionality with `p q`. Simplify using `only [ιLev, Matrix.of_apply]`. Distinguish the cases in `hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i`. Rewrite using `[dif_pos hp]`. Distinguish the cases in `hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i`.

Rewrite using `[dif_pos hq]`. Apply the tactic sequence `congr 1 <;> (apply Fin.ext; simp only [levPos]; omega)`. Rewrite using `[dif_neg hq, hcol q hq p, if_neg]`. Introduce and unpack `rfl`. Conclude with `hq hp`.

Rewrite using `[dif_neg hp, hrow p hp q]`. Break down `eq_or_ne p q with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, h.symm]`.

Introduce and unpack `⟨g₀, hg₀, rfl⟩`. Use `⟨hU k i r' g₀ hg₀, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Establish `ha' : a.val < i` using `ha`. Use `a.isLt` as an intermediate fact.

Prove the components needed by the constructor for the conclusion. Rewrite using `[mulVec_bvec]`. Use function extensionality and compare the values at `p`. Use `p.isLt` as an intermediate fact. Simplify using `only [ιLev, bvec, eI]`.

Simplify using `only [Pi.single_apply, Fin.ext_iff]`. Use `ifarith`. Rewrite using `[mulVec_bvec]`. Use function extensionality and compare the values at `p`. Use `p.isLt` as an intermediate fact.

Simplify using `only [ιLev, bvec, esI]`. Simplify using `only [Pi.single_apply, Fin.ext_iff]`. Use `ifarith`.
-/
theorem glevImage_of (_hH : LevHom) (hU : LevUH) : GlevImage := by
  intro k i r'
  ext g
  constructor
  · rintro ⟨hg, hfix⟩
    have hg' : gᴴ * Hpk k (i + r') * g = Hpk k (i + r') := hg
    have hcol : ∀ q : Fin (2 * (i + r') + k + 1), ¬(i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i) →
        ∀ p, g p q = if p = q then 1 else 0 := by
      intro q hq p
      have hqlt := q.isLt
      by_cases hqi : q.val < i
      · have h := (hfix ⟨q.val, by omega⟩ (by simpa using hqi)).1
        have e : eI k (i + r') ⟨q.val, by omega⟩ = q := Fin.ext (by simp [eI])
        rw [e, mulVec_bvec] at h
        have := congrFun h p
        simpa [bvec, Pi.single_apply] using this
      · have h := (hfix ⟨2 * (i + r') + k - q.val, by omega⟩ (by simp; omega)).2
        have e : esI k (i + r') ⟨2 * (i + r') + k - q.val, by omega⟩ = q := Fin.ext (by simp [esI]; omega)
        rw [e, mulVec_bvec] at h
        have := congrFun h p
        simpa [bvec, Pi.single_apply] using this
    have hrow : ∀ p : Fin (2 * (i + r') + k + 1), ¬(i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) →
        ∀ Q, g p Q = if Q = p then 1 else 0 := by
      intro p hp Q
      have hplt := p.isLt
      obtain ⟨X, hXv⟩ : ∃ X : Fin (2 * (i + r') + k + 1), X.val = 2 * (i + r') + k - p.val :=
        ⟨⟨2 * (i + r') + k - p.val, by omega⟩, rfl⟩
      have hX : ¬(i ≤ X.val ∧ X.val < 2 * r' + k + 1 + i) := by omega
      have h1 : ∀ y, (gᴴ * Hpk k (i + r')) X y = Hpk k (i + r') X y := by
        intro y
        rw [Matrix.mul_apply]
        simp only [conjTranspose_apply, hcol X hX]
        rw [Finset.sum_eq_single X (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ X) h)]
        simp
      have h2 := congrFun (congrFun hg' X) Q
      rw [Matrix.mul_apply] at h2
      simp only [h1, hpk_partner k i r' X p hXv hp, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
      exact h2
    have hblk : ∀ p q : Fin (2 * (i + r') + k + 1), ¬(i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) →
        (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i) → g p q = 0 := by
      intro p q hp hq
      rw [hrow p hp q, if_neg]
      rintro rfl
      exact hp hq
    refine ⟨Matrix.of fun x y => g (levPos k i r' x) (levPos k i r' y), ?_, ?_⟩
    · show _ = _
      ext s t
      have h := congrFun (congrFun hg' (levPos k i r' s)) (levPos k i r' t)
      rw [hpk_shift] at h
      rw [← h, Matrix.mul_apply, Matrix.mul_apply,
        sum_block k i r' (fun Y => (gᴴ * Hpk k (i + r')) (levPos k i r' s) Y * g Y (levPos k i r' t))
          (fun Y hY => by simp only [hblk Y _ hY (levPos_mem k i r' t), mul_zero])]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      congr 1
      rw [Matrix.mul_apply, Matrix.mul_apply,
        sum_block k i r' (fun x => (gᴴ) (levPos k i r' s) x * Hpk k (i + r') x (levPos k i r' y))
          (fun x hx => by simp only [conjTranspose_apply, hblk x _ hx (levPos_mem k i r' s), star_zero, zero_mul])]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [conjTranspose_apply, hpk_shift, Matrix.of_apply]
    · ext p q
      simp only [ιLev, Matrix.of_apply]
      by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
      · rw [dif_pos hp]
        by_cases hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i
        · rw [dif_pos hq]
          congr 1 <;> (apply Fin.ext; simp only [levPos]; omega)
        · rw [dif_neg hq, hcol q hq p, if_neg]
          rintro rfl
          exact hq hp
      · rw [dif_neg hp, hrow p hp q]
        rcases eq_or_ne p q with h | h
        · subst h; simp
        · simp [h, h.symm]
  · rintro ⟨g₀, hg₀, rfl⟩
    refine ⟨hU k i r' g₀ hg₀, ?_⟩
    intro a ha
    have ha' : a.val < i := ha
    have := a.isLt
    constructor
    · rw [mulVec_bvec]
      funext p
      have := p.isLt
      dsimp only [ιLev, bvec, eI]
      simp only [Pi.single_apply, Fin.ext_iff]
      ifarith
    · rw [mulVec_bvec]
      funext p
      have := p.isLt
      dsimp only [ιLev, bvec, esI]
      simp only [Pi.single_apply, Fin.ext_iff]
      ifarith

end QnGlevImageW
