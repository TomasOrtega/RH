import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
open Classical

namespace GlobalTheory.LevelVecNorm

/- English proof (translation)
Distinguish the cases in `hs : s.Finite`. Rewrite using `[← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card s hs]`. Simplify using the standard rewrite rules. Establish `hsupp : Function.support (s.indicator (fun _ => (1:ℝ))) = s`. Apply the tactic sequence `ext x; by_cases hx : x ∈ s <;> simp [hx]`.

Rewrite using `[finsum_of_infinite_support (by rw [hsupp]; exact hs), Set.Infinite.ncard hs]`. Simplify using the standard rewrite rules.
-/
theorem finsum_indicator_one_eq_ncard' {α : Type} (s : Set α) :
    (∑ᶠ x, s.indicator (fun _ => (1:ℝ)) x) = (s.ncard : ℝ) := by
  by_cases hs : s.Finite
  · rw [← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card s hs]
    simp
  · have hsupp : Function.support (s.indicator (fun _ => (1:ℝ))) = s := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [finsum_of_infinite_support (by rw [hsupp]; exact hs), Set.Infinite.ncard hs]
    simp

/- English proof (translation)
Introduce `k _ b a r t hb ha H`. Substitute `hb` using the available equality. Substitute `a` using the available equality. Set `f : GL (Fin r) k → Matrix (Fin (r + t)) (Fin r) k` to `fun g i j => if h : i.val < r then (g : Matrix (Fin r) (Fin r) k) ⟨i.val, h⟩ j else 0`. Establish `htop : ∀ g, Formalism.IndefR.Datum.topL r (f g) = (g : Matrix (Fin r) (Fin r) k)`.

Introduce `g`. Use extensionality with `i j`. Simplify using `[Formalism.IndefR.Datum.topL, f, i.isLt, j.isLt, show i.val < r + t by omega]`. Establish `hlow : ∀ g, Formalism.IndefR.Datum.LowZero r (f g)`. Introduce `g i j hi _`.

Simplify using `[f, show ¬ i.val < r by omega]`. Establish `hinj : Function.Injective f`. Introduce `g g' h`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[← htop g, ← htop g', h]`.

Set `S : Set (Matrix (Fin (r + t)) (Fin r) k)` to `{z | Formalism.IndefR.Datum.LowZero r z ∧ ∃ g ∈ H, ((g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = Formalism.IndefR.Datum.topL r z}`. Establish `hS : S = f '' (H : Set (GL (Fin r) k))`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz, g, hg, hgz⟩`.

Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Distinguish the cases in `hi : i.val < r`. Use `congrFun (congrFun hgz ⟨i.val, hi⟩) j` as an intermediate fact. Simplify using `only [Formalism.IndefR.Datum.topL, j.isLt, show i.val < r + t by omega] at this`.

Simplify `this` using `[f, hi]`. Simplify using `[f, hi, hz i j (by omega) j.isLt]`. Introduce and unpack `⟨g, hg, rfl⟩`. Conclude with `⟨hlow g, g, hg, (htop g).symm⟩`. Establish `hfun : ∀ z, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = S.indicator (fun _ => (1:ℝ)) z`.

Introduce `z`. Unfold `GlobalTheory.LevelVecNorm.suppInd`. Distinguish the cases in `hz : z ∈ S`. Establish `hz'` using `hz`. Simplify using `only [S, Set.mem_ofPred_eq] at hz'`.

Rewrite using `[if_pos hz', Set.indicator_of_mem hz]`. Evaluate the numerical expressions. Establish `hz'` using `hz`. Simplify using `only [S, Set.mem_ofPred_eq] at hz'`. Rewrite using `[if_neg hz', Set.indicator_of_notMem hz]`.

Evaluate the numerical expressions. Repeatedly rewrite using `[hfun]`. Rewrite using `[finsum_indicator_one_eq_ncard', hS, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]`. Both sides reduce to the same expression.
-/
theorem suppInd_sq_sum_eq_card : ∀ {k : Type} [CommRing k] {b a : ℕ} (r t : ℕ), b = r + t → a = r → ∀ H : Subgroup (GL (Fin r) k),
    ∑ᶠ z : Matrix (Fin b) (Fin a) k, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = (Nat.card H : ℝ) := by
  intro k _ b a r t hb ha H
  subst hb; subst a
  let f : GL (Fin r) k → Matrix (Fin (r + t)) (Fin r) k := fun g i j =>
    if h : i.val < r then (g : Matrix (Fin r) (Fin r) k) ⟨i.val, h⟩ j else 0
  have htop : ∀ g, Formalism.IndefR.Datum.topL r (f g) = (g : Matrix (Fin r) (Fin r) k) := by
    intro g; ext i j
    simp [Formalism.IndefR.Datum.topL, f, i.isLt, j.isLt, show i.val < r + t by omega]
  have hlow : ∀ g, Formalism.IndefR.Datum.LowZero r (f g) := by
    intro g i j hi _
    simp [f, show ¬ i.val < r by omega]
  have hinj : Function.Injective f := by
    intro g g' h
    apply Units.ext
    rw [← htop g, ← htop g', h]
  let S : Set (Matrix (Fin (r + t)) (Fin r) k) :=
    {z | Formalism.IndefR.Datum.LowZero r z ∧ ∃ g ∈ H, ((g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = Formalism.IndefR.Datum.topL r z}
  have hS : S = f '' (H : Set (GL (Fin r) k)) := by
    ext z
    constructor
    · rintro ⟨hz, g, hg, hgz⟩
      refine ⟨g, hg, ?_⟩
      ext i j
      by_cases hi : i.val < r
      · have := congrFun (congrFun hgz ⟨i.val, hi⟩) j
        simp only [Formalism.IndefR.Datum.topL, j.isLt, show i.val < r + t by omega] at this
        simpa [f, hi] using this
      · simp [f, hi, hz i j (by omega) j.isLt]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hlow g, g, hg, (htop g).symm⟩
  have hfun : ∀ z, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = S.indicator (fun _ => (1:ℝ)) z := by
    intro z
    unfold GlobalTheory.LevelVecNorm.suppInd
    by_cases hz : z ∈ S
    · have hz' := hz
      simp only [S, Set.mem_ofPred_eq] at hz'
      rw [if_pos hz', Set.indicator_of_mem hz]; norm_num
    · have hz' := hz
      simp only [S, Set.mem_ofPred_eq] at hz'
      rw [if_neg hz', Set.indicator_of_notMem hz]; norm_num
  simp_rw [hfun]
  rw [finsum_indicator_one_eq_ncard', hS, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
  rfl

end GlobalTheory.LevelVecNorm
