import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesD

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

def LocalSymmStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (j : Fin A.n) (χ w : X → ℝ), A.Smooth χ → A.Smooth w →
    tsupport χ ⊆ (A.chart j).source → ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun w) Φ) χ = mInt A (Fin.cons (LocPot.ofFun χ) Φ) w

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem localSymm : LocalSymmStatement := by
  intro e X _ _ _ A _ χ w hχ hw _ Φ hΦ
  exact st_byPartsSymm_of ReciprocityTheory.AnForm.A.parts_thm A χ w hχ hw Φ hΦ

def MIntConstPotStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X) (c : ℝ)
    (Φ : Fin e → LocPot X) (g : X → ℝ), mInt A (Fin.cons (LocPot.ofFun fun _ => c) Φ) g = 0

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma sum_neg_one_pow_det_sum_eq_zero_of_eq_zero {ι m : Type} [Fintype ι] [DecidableEq ι] [Fintype m]
    [DecidableEq m] (M : ι → Matrix m m ℂ) (a : ι) (ha : M a = 0) (N : ℕ)
    (hN : Fintype.card ι ≤ N) :
    ∑ S : Finset ι, (-1 : ℂ) ^ (N - S.card) * (∑ k ∈ S, M k).det = 0 := by
  have hU : (Finset.univ : Finset (Finset ι)) = (Finset.univ : Finset ι).powerset :=
    Finset.powerset_univ.symm
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨a⟩
  rw [hU, ← Finset.insert_erase (Finset.mem_univ a),
    Finset.sum_powerset_insert (by simp : a ∉ (Finset.univ : Finset ι).erase a),
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro t ht
  rw [Finset.mem_powerset] at ht
  have hat : a ∉ t := fun h => by simpa using ht h
  have hc : t.card + 1 ≤ N := by
    have h1 := Finset.card_le_card ht
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ] at h1
    omega
  rw [Finset.sum_insert hat, ha, zero_add, Finset.card_insert_of_notMem hat]
  obtain ⟨d, hd⟩ : ∃ d, N - t.card = d + 1 := ⟨N - (t.card + 1), by omega⟩
  have hd' : N - (t.card + 1) = d := by omega
  rw [hd, hd', pow_succ]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private lemma mdisc_eq_zero_of_eq_zero' {n : ℕ} (M : Fin n → Matrix (Fin n) (Fin n) ℂ) (a : Fin n)
    (ha : M a = 0) : mdisc M = 0 := by
  unfold mdisc
  rw [sum_neg_one_pow_det_sum_eq_zero_of_eq_zero M a ha n (by simp)]
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument.

Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem mIntConstPot : MIntConstPotStatement := by
  intro e X _ A c Φ g
  unfold mInt
  split_ifs with h
  · simp only [integralWith, locDens]
    apply Finset.sum_eq_zero
    intro j _
    have h0 : ∀ y : Fin (e + 1) → ℂ, hessC (fun _ : Fin (e + 1) → ℂ => c) y = 0 := by
      intro y
      unfold hessC
      simp
      funext i k
      rfl
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun y _ => ?_)
    unfold maDens
    rw [mdisc_eq_zero_of_eq_zero' _ 0]
    · simp
    · simp only [Fin.cons_zero]
      exact h0 y
  · rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stokes : StokesStatement := st_stokes_of ReciprocityTheory.AnForm.A.parts_thm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem byPartsSymm : ByPartsSymmStatement := st_byPartsSymm_of ReciprocityTheory.AnForm.A.parts_thm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem byPartsNonpos : ByPartsNonposStatement :=
  st_byPartsNonpos_of ReciprocityTheory.AnForm.A.parts_thm ReciprocityTheory.AnForm.A.gradDensNonneg_thm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem massIndep : MassIndepStatement := st_massIndep_of ReciprocityTheory.AnForm.A.parts_thm

end

end ReciprocityTheory.AnForm.M
