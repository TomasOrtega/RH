import Formalism.SharpRestriction.GrowthBounds.ColumnSystems

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

/- English proof (translation)
Unfold `coarseA`. Conclude with `(Nat.div_le_self _ _).trans (Nat.sub_le _ _)`.
-/
theorem kf_coarseA_le {s r p : ℕ} (S : SegData s) (b : SegBlock s r) (i : Fin s) : coarseA p S b i ≤ S.bTop i := by
  unfold coarseA
  exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

/- English proof (translation)
Unfold `coarseC`. Conclude with `(Nat.div_le_self _ _).trans (Nat.sub_le _ _)`.
-/
theorem kf_coarseC_le {s r p : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r) (i : Fin s) :
    coarseC p S aTop b i ≤ aTop i := by
  unfold coarseC
  exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

def kfTuple {s r : ℕ} (b : SegBlock s r) :
    (Fin s → Fin (r + 1) → ℕ) × (Fin s → Fin (r + 1) → ℕ) × (Fin s → ℕ) × (Fin s → ℕ) × (Fin s → ℕ) × ℕ :=
  (b.rz, b.ry, b.o, b.w, b.sg, b.oPlus)

/- English proof (translation)
Introduce and unpack `⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩ h`. Simplify using `only [kfTuple, Prod.mk.injEq] at h`. Take `⟨rfl, rfl, rfl, rfl, rfl, rfl⟩` from `h`. Both sides reduce to the same expression.
-/
theorem kfTuple_inj {s r : ℕ} : Function.Injective (@kfTuple s r) := by
  rintro ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩ h
  simp only [kfTuple, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

/- English proof (translation)
Unfold `cap`. Use `gcongr with i`. Use `split_ifs`. Establish `h1` using `kf_coarseA_le (p := p) S b i`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers.
-/
theorem kf_cap_le {s r p : ℕ} (S : SegData s) (b : SegBlock s r) (l : ℕ) :
    cap p S b l ≤ S.A0 p + ∑ i, (S.bTop i : ℤ) := by
  unfold cap
  gcongr with i
  split_ifs
  · have h1 := kf_coarseA_le (p := p) S b i
    omega
  · omega

/- English proof (translation)
Take `⟨R, hR⟩ : ∃ R : ℝ, R = ((S.A0 p + ∑ i, (S.bTop i : ℤ) : ℤ) : ℝ) + (S.La / (r + 1) + 4 / (p : ℝ) ^ 2) * ∑ i, 2 * (S.a : ℝ) / (S.P p i : ℝ) + S.La * (S.bPlus : ℝ) / (r + 1)` from `⟨_, rfl⟩`. Establish `hT` using `Set.Finite.prod (Set.Finite.pi fun i => Set.Finite.pi fun (_ : Fin (r + 1)) => Set.finite_Iic (S.P p i)) (Set.Finite.prod (Set.Finite.pi fun i => Set.Finite.pi fun (_ : Fin (r + 1)) => Set.finite_Iic (S.P p i)) (Set.Finite.prod (Set.Finite.pi fun i => Set.finite_Iic (S.bTop i)) ( …`. Use `(hT.preimage kfTuple_inj.injOn).subset ?_` and prove the remaining obligations. Introduce and unpack `b ⟨⟨hdig, -, -⟩, hge, hlt, hop⟩`. Simplify using `only [Set.mem_preimage, kfTuple, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic, forall_const]`.

Use `⟨fun i c => (hdig i c).1.le, fun i c => (hdig i c).2.le, fun i => ?_, fun i => ?_, fun i => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : S.sigma ≤ (i : ℕ)`. Conclude with `(hge i h).1.trans (kf_coarseA_le S b i)`. Rewrite using `[(hlt i (not_le.mp h)).1]`. Conclude with `Nat.zero_le _`.

Distinguish the cases in `h : (i : ℕ) < S.sigma`. Conclude with `(hlt i h).2.1.trans (kf_coarseA_le S b i)`. Rewrite using `[(hge i (not_lt.mp h)).2.2.1]`. Conclude with `Nat.zero_le _`. Distinguish the cases in `h : (i : ℕ) < S.sigma`.

Conclude with `(hlt i h).2.2.1.trans (kf_coarseC_le S aTop b i)`. Rewrite using `[(hge i (not_lt.mp h)).2.2.2]`. Conclude with `Nat.zero_le _`. Establish `hc : (cap p S b s : ℝ) ≤ ((S.A0 p + ∑ i, (S.bTop i : ℤ) : ℤ) : ℝ)`. Conclude with `kf_cap_le S b s` after adjusting the coercions.

Establish `h1 : (b.oPlus : ℝ) ≤ R`. Use `hop.trans ?_` and prove the remaining obligations. Rewrite using `[hR]`. Unfold `Oplus`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `h1.trans (Nat.le_ceil R)` after adjusting the coercions.
-/
theorem kf_kept_finite (p r : ℕ) {s : ℕ} (S : SegData s) (aTop : Fin s → ℕ) :
    {b : SegBlock s r | Kept p r S aTop b}.Finite := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ((S.A0 p + ∑ i, (S.bTop i : ℤ) : ℤ) : ℝ) +
      (S.La / (r + 1) + 4 / (p : ℝ) ^ 2) * ∑ i, 2 * (S.a : ℝ) / (S.P p i : ℝ) +
      S.La * (S.bPlus : ℝ) / (r + 1) := ⟨_, rfl⟩
  have hT := Set.Finite.prod (Set.Finite.pi fun i => Set.Finite.pi fun (_ : Fin (r + 1)) => Set.finite_Iic (S.P p i))
    (Set.Finite.prod (Set.Finite.pi fun i => Set.Finite.pi fun (_ : Fin (r + 1)) => Set.finite_Iic (S.P p i))
    (Set.Finite.prod (Set.Finite.pi fun i => Set.finite_Iic (S.bTop i))
    (Set.Finite.prod (Set.Finite.pi fun i => Set.finite_Iic (S.bTop i))
    (Set.Finite.prod (Set.Finite.pi fun i => Set.finite_Iic (aTop i)) (Set.finite_Iic ⌈R⌉₊)))))
  refine (hT.preimage kfTuple_inj.injOn).subset ?_
  rintro b ⟨⟨hdig, -, -⟩, hge, hlt, hop⟩
  simp only [Set.mem_preimage, kfTuple, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic,
    forall_const]
  refine ⟨fun i c => (hdig i c).1.le, fun i c => (hdig i c).2.le, fun i => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · by_cases h : S.sigma ≤ (i : ℕ)
    · exact (hge i h).1.trans (kf_coarseA_le S b i)
    · rw [(hlt i (not_le.mp h)).1]
      exact Nat.zero_le _
  · by_cases h : (i : ℕ) < S.sigma
    · exact (hlt i h).2.1.trans (kf_coarseA_le S b i)
    · rw [(hge i (not_lt.mp h)).2.2.1]
      exact Nat.zero_le _
  · by_cases h : (i : ℕ) < S.sigma
    · exact (hlt i h).2.2.1.trans (kf_coarseC_le S aTop b i)
    · rw [(hge i (not_lt.mp h)).2.2.2]
      exact Nat.zero_le _
  · have hc : (cap p S b s : ℝ) ≤ ((S.A0 p + ∑ i, (S.bTop i : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast kf_cap_le S b s
    have h1 : (b.oPlus : ℝ) ≤ R := by
      refine hop.trans ?_
      rw [hR]
      unfold Oplus
      linarith
    exact_mod_cast h1.trans (Nat.le_ceil R)

end Formalism.MainNotions.ColumnSystems.Pf
