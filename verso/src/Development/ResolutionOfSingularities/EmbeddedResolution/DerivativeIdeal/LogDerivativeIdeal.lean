import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal

namespace FunctorialResolution.EmbeddedResolution

variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

def tangentDerivations (P : Ideal S) : Submodule S (Derivation k S S) where
  carrier := {D : Derivation k S S | ∀ x ∈ P, D x ∈ P}
  add_mem' := by
    intro D D' hD hD' x hx
    have h := P.add_mem (hD x hx) (hD' x hx)
    simpa using h
  zero_mem' := by
    intro x _
    simp
  smul_mem' := by
    intro a D hD x hx
    have h := Ideal.mul_mem_left P a (hD x hx)
    simpa [smul_eq_mul] using h

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_tangentDerivations (P : Ideal S) (D : Derivation k S S) :
    D ∈ tangentDerivations k P ↔ ∀ x ∈ P, D x ∈ P := Iff.rfl

/- English proof (translation)
Rewrite using `[mem_tangentDerivations]`. Introduce `x _`. Establish `h` using `Ideal.mul_mem_right (D x) P hp`. Simplify `h` using `[smul_eq_mul]`.
-/
theorem smul_mem_tangentDerivations (P : Ideal S) {p : S} (hp : p ∈ P)
    (D : Derivation k S S) : p • D ∈ tangentDerivations k P := by
  rw [mem_tangentDerivations]
  intro x _
  have h := Ideal.mul_mem_right (D x) P hp
  simpa [smul_eq_mul] using h

/- English proof (translation)
Rewrite using `[mem_tangentDerivations]`. Prove the components needed by the constructor for the conclusion. Introduce `hD`. Conclude with `hD x (Ideal.subset_span (Set.mem_singleton x))`. Introduce `hD y hy`.

Use `derivation_apply_mem_of_mem_span D le_rfl ?_ hy` and prove the remaining obligations. Introduce `g hg`. Rewrite `hg` using `[Set.mem_singleton_iff]`. Substitute `hg` using the available equality. Conclude with `hD`.
-/
theorem mem_tangentDerivations_span_singleton (x : S) (D : Derivation k S S) :
    D ∈ tangentDerivations k (Ideal.span ({x} : Set S)) ↔
      D x ∈ Ideal.span ({x} : Set S) := by
  rw [mem_tangentDerivations]
  constructor
  · intro hD
    exact hD x (Ideal.subset_span (Set.mem_singleton x))
  · intro hD y hy
    refine derivation_apply_mem_of_mem_span D le_rfl ?_ hy
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hD

def logDerivIdeal (P J : Ideal S) : Ideal S :=
  J ⊔ Ideal.span {x : S | ∃ D ∈ tangentDerivations k P, ∃ y ∈ J, D y = x}

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem logDerivIdeal_eq_sup_span (P J : Ideal S) :
    logDerivIdeal k P J =
      J ⊔ Ideal.span {x : S | ∃ D ∈ tangentDerivations k P, ∃ y ∈ J, D y = x} := rfl

/- English proof (translation)
Rewrite using `[logDerivIdeal_eq_sup_span]`. Conclude with `le_sup_left`.
-/
theorem le_logDerivIdeal (P J : Ideal S) : J ≤ logDerivIdeal k P J := by
  rw [logDerivIdeal_eq_sup_span]
  exact le_sup_left

/- English proof (translation)
Rewrite using `[logDerivIdeal_eq_sup_span]`. Conclude with `Submodule.mem_sup_right (Ideal.subset_span ⟨D, hD, x, hx, rfl⟩)`.
-/
theorem derivation_apply_mem_logDerivIdeal (P J : Ideal S) (D : Derivation k S S)
    (hD : D ∈ tangentDerivations k P) {x : S} (hx : x ∈ J) :
    D x ∈ logDerivIdeal k P J := by
  rw [logDerivIdeal_eq_sup_span]
  exact Submodule.mem_sup_right (Ideal.subset_span ⟨D, hD, x, hx, rfl⟩)

/- English proof (translation)
Rewrite using `[logDerivIdeal_eq_sup_span, sup_le_iff, Ideal.span_le]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, fun D hD x hx => h2 ⟨D, hD, x, hx, rfl⟩⟩`. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨D, hD, y, hy, rfl⟩`. Conclude with `h2 D hD y hy`.
-/
theorem logDerivIdeal_le_iff (P J K : Ideal S) :
    logDerivIdeal k P J ≤ K ↔
      J ≤ K ∧ ∀ D ∈ tangentDerivations k P, ∀ x ∈ J, D x ∈ K := by
  rw [logDerivIdeal_eq_sup_span, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun D hD x hx => h2 ⟨D, hD, x, hx, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro x ⟨D, hD, y, hy, rfl⟩
    exact h2 D hD y hy

/- English proof (translation)
Introduce `I J h`. Rewrite using `[logDerivIdeal_le_iff]`. Use `⟨h.trans (le_logDerivIdeal k P J), fun D hD x hx => ?_⟩` and prove the remaining obligations. Conclude with `derivation_apply_mem_logDerivIdeal k P J D hD (h hx)`.
-/
theorem logDerivIdeal_mono (P : Ideal S) : Monotone (logDerivIdeal k P : Ideal S → Ideal S) := by
  intro I J h
  rw [logDerivIdeal_le_iff]
  refine ⟨h.trans (le_logDerivIdeal k P J), fun D hD x hx => ?_⟩
  exact derivation_apply_mem_logDerivIdeal k P J D hD (h hx)

/- English proof (translation)
The claim follows from `logDerivIdeal_mono k P h`.
-/
theorem logDerivIdeal_le_logDerivIdeal (P : Ideal S) {I J : Ideal S} (h : I ≤ J) :
    logDerivIdeal k P I ≤ logDerivIdeal k P J :=
  logDerivIdeal_mono k P h

/- English proof (translation)
Rewrite using `[logDerivIdeal_le_iff]`. Use `⟨le_derivIdeal k J, fun D _ x hx => ?_⟩` and prove the remaining obligations. Conclude with `derivation_apply_mem_derivIdeal k J D hx`.
-/
theorem logDerivIdeal_le_derivIdeal (P J : Ideal S) :
    logDerivIdeal k P J ≤ derivIdeal k J := by
  rw [logDerivIdeal_le_iff]
  refine ⟨le_derivIdeal k J, fun D _ x hx => ?_⟩
  exact derivation_apply_mem_derivIdeal k J D hx

/- English proof (translation)
Use `le_antisymm (logDerivIdeal_le_derivIdeal k ⊤ J) ?_` and prove the remaining obligations. Rewrite using `[derivIdeal_le_iff]`. Use `⟨le_logDerivIdeal k ⊤ J, fun D x hx => ?_⟩` and prove the remaining obligations. Use `derivation_apply_mem_logDerivIdeal k ⊤ J D ?_ hx` and prove the remaining obligations. Rewrite using `[mem_tangentDerivations]`.

Introduce `y _`. Conclude with `Submodule.mem_top`.
-/
theorem logDerivIdeal_top_eq_derivIdeal (J : Ideal S) :
    logDerivIdeal k (⊤ : Ideal S) J = derivIdeal k J := by
  refine le_antisymm (logDerivIdeal_le_derivIdeal k ⊤ J) ?_
  rw [derivIdeal_le_iff]
  refine ⟨le_logDerivIdeal k ⊤ J, fun D x hx => ?_⟩
  refine derivation_apply_mem_logDerivIdeal k ⊤ J D ?_ hx
  rw [mem_tangentDerivations]
  intro y _
  exact Submodule.mem_top

/- English proof (translation)
Rewrite using `[logDerivIdeal_le_iff]`. Use `⟨iSup_mono fun i => le_logDerivIdeal k P (J i), ?_⟩` and prove the remaining obligations. Introduce `D hD x hx`. Use `Submodule.iSup_induction (motive := fun z : S => D z ∈ ⨆ i, logDerivIdeal k P (J i)) J hx ?_ ?_ ?_` and prove the remaining obligations. Introduce `i y hy`.

Conclude with `le_iSup (fun i => logDerivIdeal k P (J i)) i (derivation_apply_mem_logDerivIdeal k P (J i) D hD hy)`. Simplify `Submodule.zero_mem (⨆ i, logDerivIdeal k P (J i))` using `only [map_zero]`. Introduce `a b ha hb`. Simplify `Submodule.add_mem (⨆ i, logDerivIdeal k P (J i)) ha hb` using `only [map_add]`.
-/
theorem logDerivIdeal_iSup_le {ι : Sort*} (P : Ideal S) (J : ι → Ideal S) :
    logDerivIdeal k P (⨆ i, J i) ≤ ⨆ i, logDerivIdeal k P (J i) := by
  rw [logDerivIdeal_le_iff]
  refine ⟨iSup_mono fun i => le_logDerivIdeal k P (J i), ?_⟩
  intro D hD x hx
  refine Submodule.iSup_induction
    (motive := fun z : S => D z ∈ ⨆ i, logDerivIdeal k P (J i)) J hx ?_ ?_ ?_
  · intro i y hy
    exact le_iSup (fun i => logDerivIdeal k P (J i)) i
      (derivation_apply_mem_logDerivIdeal k P (J i) D hD hy)
  · simpa only [map_zero] using Submodule.zero_mem (⨆ i, logDerivIdeal k P (J i))
  · intro a b ha hb
    simpa only [map_add] using Submodule.add_mem (⨆ i, logDerivIdeal k P (J i)) ha hb

def logDerivIdealIterate (P : Ideal S) : ℕ → Ideal S → Ideal S
  | 0, J => J
  | r + 1, J => logDerivIdeal k P (logDerivIdealIterate P r J)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem logDerivIdealIterate_zero (P J : Ideal S) : logDerivIdealIterate k P 0 J = J := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem logDerivIdealIterate_succ (P : Ideal S) (r : ℕ) (J : Ideal S) :
    logDerivIdealIterate k P (r + 1) J = logDerivIdeal k P (logDerivIdealIterate k P r J) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem logDerivIdealIterate_one (P J : Ideal S) :
    logDerivIdealIterate k P 1 J = logDerivIdeal k P J := rfl

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => rw [Nat.zero_add, logDerivIdealIterate_zero]`. Consider the case `succ r ih => rw [Nat.succ_add, logDerivIdealIterate_succ, logDerivIdealIterate_succ, ih]`.
-/
theorem logDerivIdealIterate_add (P : Ideal S) (r s : ℕ) (J : Ideal S) :
    logDerivIdealIterate k P (r + s) J =
      logDerivIdealIterate k P r (logDerivIdealIterate k P s J) := by
  induction r with
  | zero => rw [Nat.zero_add, logDerivIdealIterate_zero]
  | succ r ih => rw [Nat.succ_add, logDerivIdealIterate_succ, logDerivIdealIterate_succ, ih]

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => exact (logDerivIdealIterate_zero k P J).ge`. Consider the case `succ r ih`. Rewrite using `[logDerivIdealIterate_succ]`. Conclude with `ih.trans (le_logDerivIdeal k P _)`.
-/
theorem le_logDerivIdealIterate (P : Ideal S) (r : ℕ) (J : Ideal S) :
    J ≤ logDerivIdealIterate k P r J := by
  induction r with
  | zero => exact (logDerivIdealIterate_zero k P J).ge
  | succ r ih =>
      rw [logDerivIdealIterate_succ]
      exact ih.trans (le_logDerivIdeal k P _)

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero`. Introduce `I J h`. Rewrite using `[logDerivIdealIterate_zero, logDerivIdealIterate_zero]`. Conclude with `h`.

Consider the case `succ r ih`. Introduce `I J h`. Rewrite using `[logDerivIdealIterate_succ, logDerivIdealIterate_succ]`. Conclude with `logDerivIdeal_mono k P (ih h)`.
-/
theorem logDerivIdealIterate_mono (P : Ideal S) (r : ℕ) :
    Monotone (logDerivIdealIterate k P r : Ideal S → Ideal S) := by
  induction r with
  | zero =>
      intro I J h
      rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero]
      exact h
  | succ r ih =>
      intro I J h
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      exact logDerivIdeal_mono k P (ih h)

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le h`. Rewrite using `[Nat.add_comm r d, logDerivIdealIterate_add]`. Conclude with `le_logDerivIdealIterate k P d _`.
-/
theorem logDerivIdealIterate_le_of_le (P : Ideal S) {r r' : ℕ} (h : r ≤ r') (J : Ideal S) :
    logDerivIdealIterate k P r J ≤ logDerivIdealIterate k P r' J := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm r d, logDerivIdealIterate_add]
  exact le_logDerivIdealIterate k P d _

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => rw [logDerivIdealIterate_zero, derivIdealIterate_zero]`. Consider the case `succ r ih`. Rewrite using `[logDerivIdealIterate_succ, derivIdealIterate_succ, ih, logDerivIdeal_top_eq_derivIdeal]`.
-/
theorem logDerivIdealIterate_top_eq_derivIdealIterate (r : ℕ) (J : Ideal S) :
    logDerivIdealIterate k (⊤ : Ideal S) r J = derivIdealIterate k r J := by
  induction r with
  | zero => rw [logDerivIdealIterate_zero, derivIdealIterate_zero]
  | succ r ih =>
      rw [logDerivIdealIterate_succ, derivIdealIterate_succ, ih, logDerivIdeal_top_eq_derivIdeal]

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => exact le_rfl`. Consider the case `succ r ih`. Rewrite using `[logDerivIdealIterate_succ]`. Use `le_trans (logDerivIdeal_mono k P ih) ?_` and prove the remaining obligations.

Use `le_trans (logDerivIdeal_iSup_le k P fun i => logDerivIdealIterate k P r (J i)) ?_` and prove the remaining obligations. Conclude with `iSup_mono fun i => le_of_eq (logDerivIdealIterate_succ k P r (J i)).symm`.
-/
theorem logDerivIdealIterate_iSup_le {ι : Sort*} (P : Ideal S) (r : ℕ) (J : ι → Ideal S) :
    logDerivIdealIterate k P r (⨆ i, J i) ≤ ⨆ i, logDerivIdealIterate k P r (J i) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      rw [logDerivIdealIterate_succ]
      refine le_trans (logDerivIdeal_mono k P ih) ?_
      refine le_trans (logDerivIdeal_iSup_le k P fun i => logDerivIdealIterate k P r (J i)) ?_
      exact iSup_mono fun i => le_of_eq (logDerivIdealIterate_succ k P r (J i)).symm

end FunctorialResolution.EmbeddedResolution
