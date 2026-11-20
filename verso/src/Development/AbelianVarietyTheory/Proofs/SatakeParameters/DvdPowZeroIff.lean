import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat

noncomputable section

namespace GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def DvdPow (ϖ : L) (k : ℕ) (a : L) : Prop := ∃ b ∈ Formalism.UG.intL L, a = ϖ ^ k * b

def IndepMod (ϖ : L) {ι : Type} [Fintype ι] {m : ℕ} (z : ι → Fin m → L) : Prop :=
  ∀ d : ι → L, (∀ i, d i ∈ Formalism.UG.intL L) → (∀ r, DvdPow ϖ 1 (∑ i, d i * z i r)) → ∀ i, DvdPow ϖ 1 (d i)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, rfl⟩`. Simplify using `using hb`. Introduce `h; exact ⟨a, h, by simp⟩`.
-/
theorem dvdPow_zero_iff {ϖ a : L} : DvdPow ϖ 0 a ↔ a ∈ Formalism.UG.intL L := by
  constructor
  · rintro ⟨b, hb, rfl⟩; simpa using hb
  · intro h; exact ⟨a, h, by simp⟩

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `ha`. Take `⟨d, hd, rfl⟩` from `hb`. Conclude with `⟨c + d, (Formalism.UG.intL L).add_mem hc hd, by ring⟩`.
-/
theorem dvdPow_add {ϖ a b : L} {k : ℕ} (ha : DvdPow ϖ k a) (hb : DvdPow ϖ k b) : DvdPow ϖ k (a + b) := by
  obtain ⟨c, hc, rfl⟩ := ha; obtain ⟨d, hd, rfl⟩ := hb
  exact ⟨c + d, (Formalism.UG.intL L).add_mem hc hd, by ring⟩

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `ha`. Conclude with `⟨-c, (Formalism.UG.intL L).neg_mem hc, by ring⟩`.
-/
theorem dvdPow_neg {ϖ a : L} {k : ℕ} (ha : DvdPow ϖ k a) : DvdPow ϖ k (-a) := by
  obtain ⟨c, hc, rfl⟩ := ha
  exact ⟨-c, (Formalism.UG.intL L).neg_mem hc, by ring⟩

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `dvdPow_add ha (dvdPow_neg hb)`.
-/
theorem dvdPow_sub {ϖ a b : L} {k : ℕ} (ha : DvdPow ϖ k a) (hb : DvdPow ϖ k b) : DvdPow ϖ k (a - b) := by
  rw [sub_eq_add_neg]; exact dvdPow_add ha (dvdPow_neg hb)

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, (Formalism.UG.intL L).zero_mem, by simp⟩`.
-/
theorem dvdPow_zero (ϖ : L) (k : ℕ) : DvdPow ϖ k 0 := ⟨0, (Formalism.UG.intL L).zero_mem, by simp⟩

/- English proof (translation)
Take `⟨b, hb, rfl⟩` from `ha`. Conclude with `⟨c * b, (Formalism.UG.intL L).mul_mem hc hb, by ring⟩`.
-/
theorem dvdPow_mul_int {ϖ a c : L} {k : ℕ} (ha : DvdPow ϖ k a) (hc : c ∈ Formalism.UG.intL L) : DvdPow ϖ k (c * a) := by
  obtain ⟨b, hb, rfl⟩ := ha
  exact ⟨c * b, (Formalism.UG.intL L).mul_mem hc hb, by ring⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using dvdPow_zero ϖ k`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj]`. Conclude with `dvdPow_add (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem dvdPow_sum {ϖ : L} {k : ℕ} {ι : Type} (s : Finset ι) (f : ι → L) (h : ∀ i ∈ s, DvdPow ϖ k (f i)) :
    DvdPow ϖ k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dvdPow_zero ϖ k
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact dvdPow_add (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Take `⟨b, hb, rfl⟩` from `ha`. Use `⟨ϖ ^ (k - l) * b, (Formalism.UG.intL L).mul_mem ((Formalism.UG.intL L).pow_mem hϖ _) hb, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlk]`.
-/
theorem dvdPow_mono {ϖ a : L} {k l : ℕ} (hϖ : ϖ ∈ Formalism.UG.intL L) (hlk : l ≤ k) (ha : DvdPow ϖ k a) : DvdPow ϖ l a := by
  obtain ⟨b, hb, rfl⟩ := ha
  refine ⟨ϖ ^ (k - l) * b, (Formalism.UG.intL L).mul_mem ((Formalism.UG.intL L).pow_mem hϖ _) hb, ?_⟩
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlk]

end GlobalTheory.Hk3.IntWitt

end
