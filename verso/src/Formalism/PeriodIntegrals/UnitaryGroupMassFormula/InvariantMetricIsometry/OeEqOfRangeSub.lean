import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.ColChoiceFintype

noncomputable section

open Matrix Classical

namespace PI.IsoInvMetricW

open PI.IsoInvMetric

/- English proof (translation)
Establish `h1 : Finset.univ.image I ⊆ Finset.univ.image J`. Introduce `x hx`. Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢`. Take `⟨i, rfl⟩` from `hx`. Conclude with `hs i`.

Establish `h2 : Finset.univ.image I = Finset.univ.image J` using `Finset.eq_of_subset_of_card_le h1 (by`. Rewrite using `[Finset.card_image_of_injective _ J.injective, Finset.card_image_of_injective _ I.injective])`. Apply `OrderEmbedding.range_inj.mp` to reduce the goal to its premises. Use `congrArg (fun s : Finset (Fin N) => (s : Set (Fin N))) h2` as an intermediate fact. Simplify `this` using `only [Finset.coe_image, Finset.coe_univ, Set.image_univ]`.
-/
theorem oe_eq_of_range_sub {h N : ℕ} (I J : Fin h ↪o Fin N) (hs : ∀ i, ∃ k, J k = I i) :
    I = J := by
  classical
  have h1 : Finset.univ.image I ⊆ Finset.univ.image J := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨i, rfl⟩ := hx
    exact hs i
  have h2 : Finset.univ.image I = Finset.univ.image J :=
    Finset.eq_of_subset_of_card_le h1 (by
      rw [Finset.card_image_of_injective _ J.injective,
        Finset.card_image_of_injective _ I.injective])
  apply OrderEmbedding.range_inj.mp
  have := congrArg (fun s : Finset (Fin N) => (s : Set (Fin N))) h2
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using this

/- English proof (translation)
Introduce `Lt _ _ N nu d I J`. Unfold `E`. Use `split_ifs with hIJ`. Substitute `hIJ` using the available equality. Use `Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations.

Establish `: (Matrix.of fun i k : Fin ((nu s).colLen c) => Matrix.diagonal (d s) (I s c i) (I s c k)) = Matrix.diagonal (fun i => d s (I s c i))`. Use extensionality with `i k`. Simplify using `[Matrix.diagonal_apply, (I s c).injective.eq_iff]`. Rewrite using `[this, Matrix.det_diagonal]`. Establish `: ∃ s c, I s c ≠ J s c`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Conclude with `hIJ (funext fun s => funext fun c => hne s c)`. Take `⟨s, c, hsc⟩` from `this`. Establish `: ∃ i, ∀ k, J s c k ≠ I s c i`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Conclude with `hsc (oe_eq_of_range_sub _ _ hne)`. Take `⟨i, hi⟩` from `this`. Apply `Finset.prod_eq_zero (Finset.mem_univ s)` to reduce the goal to its premises.

Apply `Finset.prod_eq_zero (Finset.mem_univ c)` to reduce the goal to its premises. Apply `Matrix.det_eq_zero_of_row_eq_zero i` to reduce the goal to its premises. Introduce `k`. Simplify using `[Matrix.diagonal_apply_ne _ (hi k).symm]`.
-/
theorem metric_diagonal : EDiag := by
  intro Lt _ _ N nu d I J
  unfold E
  split_ifs with hIJ
  · subst hIJ
    refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
    have : (Matrix.of fun i k : Fin ((nu s).colLen c) =>
        Matrix.diagonal (d s) (I s c i) (I s c k)) = Matrix.diagonal (fun i => d s (I s c i)) := by
      ext i k
      simp [Matrix.diagonal_apply, (I s c).injective.eq_iff]
    rw [this, Matrix.det_diagonal]
  · have : ∃ s c, I s c ≠ J s c := by
      by_contra hne
      push_neg at hne
      exact hIJ (funext fun s => funext fun c => hne s c)
    obtain ⟨s, c, hsc⟩ := this
    have : ∃ i, ∀ k, J s c k ≠ I s c i := by
      by_contra hne
      push_neg at hne
      exact hsc (oe_eq_of_range_sub _ _ hne)
    obtain ⟨i, hi⟩ := this
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro k
    simp [Matrix.diagonal_apply_ne _ (hi k).symm]

def J0 {Lt : Type} {N : ℕ} (nu : Lt → YoungDiagram) (hle : ∀ z, (nu z).colLen 0 ≤ N) :
    ColChoice N nu :=
  fun s c => Fin.castLEOrderEmb (le_trans ((nu s).colLen_anti 0 c (Nat.zero_le _)) (hle s))

/- English proof (translation)
Establish `e : u0 N nu J = E nu (fun _ => Matrix.diagonal (fun _ => (1 : ℂ))) J (J0 nu hle)`. Unfold `u0 hvC minY E`. Use `Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `i k`.

Establish `hk : (k : ℕ) < N` using `lt_of_lt_of_le k.2 (le_trans ((nu s).colLen_anti 0 c (Nat.zero_le _)) (hle s))`. Simplify using `only [Matrix.of_apply, colsOf, hk, dite_true, Matrix.diagonal_one, J0]`. Both sides reduce to the same expression. Rewrite using `[e, metric_diagonal]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem unitVector_val_eq {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} (nu : Lt → YoungDiagram)
    (hle : ∀ z, (nu z).colLen 0 ≤ N) (J : ColChoice N nu) :
    u0 N nu J = if J = J0 nu hle then 1 else 0 := by
  have e : u0 N nu J = E nu (fun _ => Matrix.diagonal (fun _ => (1 : ℂ))) J (J0 nu hle) := by
    unfold u0 hvC minY E
    refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
    congr 1
    ext i k
    have hk : (k : ℕ) < N := lt_of_lt_of_le k.2
      (le_trans ((nu s).colLen_anti 0 c (Nat.zero_le _)) (hle s))
    simp only [Matrix.of_apply, colsOf, hk, dite_true, Matrix.diagonal_one, J0]
    rfl
  rw [e, metric_diagonal]
  split_ifs <;> simp

/- English proof (translation)
Introduce `Lt _ _ N nu hle`. Unfold `l2`. Rewrite using `[finsum_eq_sum_of_fintype]`. Simplify using `[unitVector_val_eq nu hle, apply_ite (fun x : ℂ => ‖x‖ ^ 2)]`.
-/
theorem norm1' : Norm1 := by
  intro Lt _ _ N nu hle
  unfold l2
  rw [finsum_eq_sum_of_fintype]
  simp [unitVector_val_eq nu hle, apply_ite (fun x : ℂ => ‖x‖ ^ 2)]

end PI.IsoInvMetricW
