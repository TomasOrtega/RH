import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.SignRenumber

def signKey {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ℕ := (if ε a = true then 0 else n) + a.val

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions.

Apply the first step, then apply the next step to every resulting obligation.
-/
lemma signKey_injective {n : ℕ} (ε : Fin n → Bool) : Function.Injective (signKey ε) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  unfold signKey at h
  split_ifs at h <;> omega

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma signKey_lt_iff_of_eq {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    signKey ε a < signKey ε b ↔ a < b := by
  unfold signKey
  rw [h, Fin.lt_iff_val_lt_val]
  split_ifs <;> omega

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma signKey_lt_n_iff {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : signKey ε a < n ↔ ε a = true := by
  have ha := a.isLt
  unfold signKey
  cases h : ε a <;> simp <;> omega

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma signKey_true_lt_false {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (ha : ε a = true)
    (hb : ε b = false) : signKey ε a < signKey ε b := by
  have h1 := (signKey_lt_n_iff ε a).mpr ha
  have h2 : ¬ signKey ε b < n := by rw [signKey_lt_n_iff, hb]; simp
  omega

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma val_eq_rank {n : ℕ} (κ : Fin n → ℕ) (hκ : Function.Injective κ) (f : Equiv.Perm (Fin n))
    (hf : ∀ a b, κ a < κ b → f a < f b) (a : Fin n) :
    (f a).val = (univ.filter (fun b => κ b < κ a)).card := by
  have hiff : ∀ b, f b < f a ↔ κ b < κ a := by
    intro b
    constructor
    · intro h
      rcases lt_trichotomy (κ b) (κ a) with h' | h' | h'
      · exact h'
      · exact absurd (congrArg f (hκ h')) (ne_of_lt h)
      · exact absurd (hf a b h') (not_lt.mpr h.le)
    · exact hf b a
  rw [← Fin.card_Iio (f a)]
  refine Finset.card_nbij' (fun i => f.symm i) (fun b => f b) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_Iio, Set.mem_Iio, Finset.mem_Iio] at hi
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    rw [← hiff]
    simpa using hi
  · intro b hb
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hb
    simp only [Finset.coe_Iio, Set.mem_Iio, Finset.mem_Iio]
    exact (hiff b).mpr hb
  · intro i _
    simp
  · intro b _
    simp

def signCount {n : ℕ} (ε : Fin n → Bool) : ℕ := (univ.filter (fun a => ε a = true)).card

def stdSign {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : Bool := decide (i.val < signCount ε)

def renumber {n : ℕ} (ε : Fin n → Bool) : Equiv.Perm (Fin n) := (Tuple.sort (signKey ε))⁻¹

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma renumber_compat {n : ℕ} (ε : Fin n → Bool) (a b : Fin n)
    (h : signKey ε a < signKey ε b) : renumber ε a < renumber ε b := by
  by_contra h'
  have hm := Tuple.monotone_sort (signKey ε) (not_lt.mp h')
  simp only [Function.comp_apply, renumber, Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hm
  exact absurd hm (not_le.mpr h)

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma renumber_val {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    (renumber ε a).val = (univ.filter (fun b => signKey ε b < signKey ε a)).card :=
  val_eq_rank (signKey ε) (signKey_injective ε) (renumber ε) (renumber_compat ε) a

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma renumber_lt_of_lt {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b)
    (he : ε a = ε b) : renumber ε a < renumber ε b :=
  renumber_compat ε a b ((signKey_lt_iff_of_eq ε he).mpr hab)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Split into cases according to the possible forms of the given data. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
lemma stdSign_renumber {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    stdSign ε (renumber ε a) = ε a := by
  unfold stdSign
  rw [renumber_val]
  cases h : ε a
  · have : signCount ε ≤ (univ.filter (fun b => signKey ε b < signKey ε a)).card := by
      apply Finset.card_le_card
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact signKey_true_lt_false ε hb h
    simpa using this
  · have : (univ.filter (fun b => signKey ε b < signKey ε a)).card < signCount ε := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨a, by simp [h], by simp⟩
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact (signKey_lt_n_iff ε b).mp (lt_trans hb ((signKey_lt_n_iff ε a).mpr h))
    simpa using this

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma signCount_comp {n : ℕ} (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) :
    signCount (ε ∘ s) = signCount ε := by
  unfold signCount
  refine Finset.card_nbij' (fun a => s a) (fun b => s.symm b) ?_ ?_ ?_ ?_ <;> intro x hx <;> simp_all

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
lemma stdSign_comp {n : ℕ} (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) :
    stdSign (ε ∘ s) = stdSign ε := by
  funext i
  unfold stdSign
  rw [signCount_comp]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Use linear arithmetic over natural numbers and integers.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
lemma renumber_comp {n : ℕ} (ε : Fin n → Bool) (s : Equiv.Perm (Fin n))
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (a : Fin n) :
    renumber (ε ∘ s) a = renumber ε (s a) := by
  have hc : ∀ x y, signKey (ε ∘ s) x < signKey (ε ∘ s) y →
      (s.trans (renumber ε)) x < (s.trans (renumber ε)) y := by
    intro x y hxy
    simp only [Equiv.trans_apply]
    apply renumber_compat
    by_cases he : ε (s x) = ε (s y)
    · have hxy' := (signKey_lt_iff_of_eq (ε ∘ s) (a := x) (b := y) he).mp hxy
      exact (signKey_lt_iff_of_eq ε he).mpr (hs x y hxy' he)
    · cases hx : ε (s x) <;> cases hy : ε (s y)
      · rw [hx, hy] at he; exact absurd rfl he
      · have h1 : ¬ signKey (ε ∘ s) x < n := by
          rw [signKey_lt_n_iff]; simpa using hx
        have h2 : signKey (ε ∘ s) y < n := by
          rw [signKey_lt_n_iff]; simpa using hy
        omega
      · exact signKey_true_lt_false ε hx hy
      · rw [hx, hy] at he; exact absurd rfl he
  exact Fin.ext ((val_eq_rank _ (signKey_injective _) (renumber (ε ∘ s)) (renumber_compat _) a).trans
    (val_eq_rank _ (signKey_injective _) (s.trans (renumber ε)) hc a).symm)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem block_renumbering :
    ∀ n : ℕ, ∃ (std : (Fin n → Bool) → (Fin n → Bool)) (t : (Fin n → Bool) → Equiv.Perm (Fin n)),
      (∀ ε, std ε ∘ t ε = ε ∧ ∀ a b, a < b → ε a = ε b → t ε a < t ε b) ∧
      (∀ (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)), std (ε ∘ s) = std ε ∧
        ((∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) → ∀ a, t (ε ∘ s) a = t ε (s a))) ∧
      ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ), Function.Injective lam →
        ∃ (w s : Equiv.Perm (Fin n)), (∀ a, ε (w a) = ε a) ∧ StrictAnti ((lam ∘ w) ∘ s) ∧
          ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b := by
  intro n
  refine ⟨stdSign, renumber, ?_, ?_, ?_⟩
  · intro ε
    exact ⟨funext fun a => stdSign_renumber ε a, fun a b hab he => renumber_lt_of_lt ε hab he⟩
  · intro ε s
    exact ⟨stdSign_comp ε s, fun hs a => renumber_comp ε s hs a⟩
  · intro ε lam hlam
    obtain ⟨u, hu⟩ : ∃ u : Equiv.Perm (Fin n), StrictAnti (lam ∘ u) := by
      refine ⟨Tuple.sort (fun a => -lam a), ?_⟩
      have hinj : Function.Injective ((fun a => -lam a) ∘ Tuple.sort (fun a => -lam a)) :=
        (neg_injective.comp hlam).comp (Tuple.sort (fun a => -lam a)).injective
      have hmono := (Tuple.monotone_sort (fun a => -lam a)).strictMono_of_injective hinj
      intro a b hab
      have := hmono hab
      simp only [Function.comp_apply, neg_lt_neg_iff] at this
      simpa using this
    let s : Equiv.Perm (Fin n) := (renumber (ε ∘ u)).trans (renumber ε).symm
    have hs_ren : ∀ x, renumber ε (s x) = renumber (ε ∘ u) x := by
      intro x; simp [s]
    have hsx : ∀ x, ε (s x) = ε (u x) := by
      intro x
      have h := stdSign_renumber (ε ∘ u) x
      rw [stdSign_comp] at h
      rw [← stdSign_renumber ε (s x), hs_ren]
      exact h
    refine ⟨s.symm.trans u, s, ?_, ?_, ?_⟩
    · intro a
      simp only [Equiv.trans_apply]
      rw [← hsx, Equiv.apply_symm_apply]
    · have : (lam ∘ ⇑(s.symm.trans u)) ∘ ⇑s = lam ∘ u := by
        funext a; simp
      rw [this]; exact hu
    · intro a b hab he
      rcases lt_trichotomy (s a) (s b) with h | h | h
      · exact h
      · exact absurd (s.injective h) (ne_of_lt hab)
      · have h1 := renumber_lt_of_lt ε h he.symm
        rw [hs_ren, hs_ren] at h1
        have he' : (ε ∘ u) a = (ε ∘ u) b := by
          show ε (u a) = ε (u b)
          rw [← hsx, ← hsx]; exact he
        have h2 := renumber_lt_of_lt (ε ∘ u) hab he'
        exact absurd h1 (not_lt.mpr h2.le)

end GlobalTheory.SignRenumber
