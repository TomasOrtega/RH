import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.BasisTrans

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

/- English proof (translation)
Introduce `_` and use `⟨0, trivial, by simp⟩`.
-/
theorem in_zero : In (⊤ : Ideal B) (0 : MvPowerSeries σ Q) :=
  fun _ => ⟨0, trivial, by simp⟩

/- English proof (translation)
Introduce `α` and use `by obtain ⟨a, -, ha⟩ := hg α obtain ⟨b, -, hb⟩ := hh α exact ⟨a + b, trivial, by rw [map_add, ha, hb, map_add]⟩`.
-/
theorem in_add {g h : MvPowerSeries σ Q} (hg : In (⊤ : Ideal B) g) (hh : In (⊤ : Ideal B) h) :
    In (⊤ : Ideal B) (g + h) := fun α => by
  obtain ⟨a, -, ha⟩ := hg α
  obtain ⟨b, -, hb⟩ := hh α
  exact ⟨a + b, trivial, by rw [map_add, ha, hb, map_add]⟩

/- English proof (translation)
Introduce `α` and use `by obtain ⟨a, -, ha⟩ := hg α exact ⟨c * a, trivial, by rw [coeff_smul, ha, map_mul]⟩`.
-/
theorem in_smul (c : B) {g : MvPowerSeries σ Q} (hg : In (⊤ : Ideal B) g) :
    In (⊤ : Ideal B) (algebraMap B Q c • g) := fun α => by
  obtain ⟨a, -, ha⟩ := hg α
  exact ⟨c * a, trivial, by rw [coeff_smul, ha, map_mul]⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using in_zero`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `in_add (hg a (Finset.mem_insert_self _ _)) (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))`.
-/
theorem in_sum {κ : Type} (s : Finset κ) (g : κ → MvPowerSeries σ Q)
    (hg : ∀ j ∈ s, In (⊤ : Ideal B) (g j)) : In (⊤ : Ideal B) (∑ j ∈ s, g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using in_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact in_add (hg a (Finset.mem_insert_self _ _)) (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Simplify using `[comb, Matrix.one_apply]`.
-/
theorem comb_one {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → MvPowerSeries σ Q) (i : ι) :
    comb ((1 : Matrix ι ι B) i) e = e i := by
  simp [comb, Matrix.one_apply]

/- English proof (translation)
Simplify using `only [comb, Matrix.mul_apply, Matrix.of_apply, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, ← map_mul, map_sum, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm (f := fun j k => algebraMap B Q (P i j * P' j k) • e k)]`. Normalize the expressions using the abelian group laws.
-/
theorem comb_mul {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι → MvPowerSeries σ Q)
    (f : κ → MvPowerSeries σ Q) (P : ι → κ → B) (P' : κ → ι → B) (i : ι) :
    e i - comb ((Matrix.of P * Matrix.of P') i) e =
      (e i - comb (P i) f) + ∑ j, algebraMap B Q (P i j) • (f j - comb (P' j) e) := by
  simp only [comb, Matrix.mul_apply, Matrix.of_apply, smul_sub, Finset.sum_sub_distrib,
    Finset.smul_sum, smul_smul, ← map_mul, map_sum, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun j k => algebraMap B Q (P i j * P' j k) • e k)]
  abel

/- English proof (translation)
Use function extensionality and compare the values at `i`. Take `⟨b, -, hb⟩` from `he.2 (e i) (he.1 i)`. Establish `hA : In (⊤ : Ideal B) (e i - comb ((Matrix.of P * Matrix.of P') i) e)`. Rewrite using `[comb_mul e f P P' i]`. Conclude with `in_add (h1 i) (in_sum _ _ fun j _ => in_smul _ (h2 j))`.

Establish `hB : In (⊤ : Ideal B) (e i - comb ((1 : Matrix ι ι B) i) e)`. Rewrite using `[comb_one, sub_self]`. Conclude with `in_zero`. Conclude with `(hb _ hA).trans (hb _ hB).symm`.
-/
theorem mul_eq_one {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι]
    [Fintype κ] [DecidableEq ι] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q)
    (he : IsBasis μ e) (P : ι → κ → B) (P' : κ → ι → B)
    (h1 : ∀ i, In (⊤ : Ideal B) (e i - comb (P i) f))
    (h2 : ∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) :
    Matrix.of P * Matrix.of P' = 1 := by
  funext i
  obtain ⟨b, -, hb⟩ := he.2 (e i) (he.1 i)
  have hA : In (⊤ : Ideal B) (e i - comb ((Matrix.of P * Matrix.of P') i) e) := by
    rw [comb_mul e f P P' i]
    exact in_add (h1 i) (in_sum _ _ fun j _ => in_smul _ (h2 j))
  have hB : In (⊤ : Ideal B) (e i - comb ((1 : Matrix ι ι B) i) e) := by
    rw [comb_one, sub_self]; exact in_zero
  exact (hb _ hA).trans (hb _ hB).symm

/- English proof (translation)
Introduce `B Q _ _ _ d μ ι κ _ _ _ _ e f he hf P P' h1 h2`. Conclude with `⟨mul_eq_one μ e f he P P' h1 h2, mul_eq_one μ f e hf P' P h2 h1⟩`.
-/
theorem trans_inverse : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q), IsBasis μ e → IsBasis μ f → ∀ (P : ι → κ → B) (P' : κ → ι → B), (∀ i, In (⊤ : Ideal B) (e i - comb (P i) f)) → (∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) → Matrix.of P * Matrix.of P' = 1 ∧ Matrix.of P' * Matrix.of P = 1 := by
  intro B Q _ _ _ d μ ι κ _ _ _ _ e f he hf P P' h1 h2
  exact ⟨mul_eq_one μ e f he P P' h1 h2, mul_eq_one μ f e hf P' P h2 h1⟩

end GlobalTheory.BasisTrans
