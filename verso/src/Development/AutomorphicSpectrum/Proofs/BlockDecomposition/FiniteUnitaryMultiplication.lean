import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VLtOneOfOrdLEqOne

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.FUMulPf

section Abstract

variable {H : Type} [Group H] {I B M : Subgroup H}

def Fac (I B M : Subgroup H) : Prop := M ≤ I ∧ ∀ x ∈ I, ∃ p ∈ I ⊓ B, ∃ m ∈ M, x = p * m

def Dom (I B M : Subgroup H) (t : H) : Prop :=
  t ∈ B ∧ (∀ p ∈ I ⊓ B, t * p * t⁻¹ ∈ I ⊓ B) ∧ ∀ m ∈ M, t⁻¹ * m * t ∈ M

/- English proof (translation)
Take `⟨p, hp, m, hm, rfl⟩` from `hF.2 a ha`. Conclude with `⟨p, hp, _, hF.1 (ht.2.2 m hm), by group⟩`.
-/
theorem absorb (hF : Fac I B M) {t : H} (ht : Dom I B M t) {a : H} (ha : a ∈ I) :
    ∃ p ∈ I ⊓ B, ∃ c ∈ I, a * t = p * t * c := by
  obtain ⟨p, hp, m, hm, rfl⟩ := hF.2 a ha
  exact ⟨p, hp, _, hF.1 (ht.2.2 m hm), by group⟩

/- English proof (translation)
Take `⟨a, ha, c, hc, rfl⟩` from `hz`. Take `⟨a', ha', c', hc', rfl⟩` from `hz'`. Take `⟨p, hp, m, hm, e⟩` from `hF.2 (c * a') (I.mul_mem hc ha')`. Use `⟨a * (t * p * t⁻¹), I.mul_mem ha (ht.2.1 p hp).1, (t'⁻¹ * m * t') * c', I.mul_mem (hF.1 (ht'.2.2 m hm)) hc', ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dc_mul (hF : Fac I B M) {t t' : H} (ht : Dom I B M t) (ht' : Dom I B M t') {z z' : H}
    (hz : ∃ x ∈ I, ∃ c ∈ I, z = x * t * c) (hz' : ∃ x ∈ I, ∃ c ∈ I, z' = x * t' * c) :
    ∃ x ∈ I, ∃ c ∈ I, z * z' = x * (t * t') * c := by
  obtain ⟨a, ha, c, hc, rfl⟩ := hz
  obtain ⟨a', ha', c', hc', rfl⟩ := hz'
  obtain ⟨p, hp, m, hm, e⟩ := hF.2 (c * a') (I.mul_mem hc ha')
  refine ⟨a * (t * p * t⁻¹), I.mul_mem ha (ht.2.1 p hp).1, (t'⁻¹ * m * t') * c',
    I.mul_mem (hF.1 (ht'.2.2 m hm)) hc', ?_⟩
  calc a * t * c * (a' * t' * c') = a * t * (c * a') * t' * c' := by group
    _ = _ := by rw [e]; group

/- English proof (translation)
Take `⟨a, ha, c, hc, rfl⟩` from `hz`. Take `⟨a₂, ha₂, c₂, hc₂, e⟩` from `hz'`. Take `⟨p, hp, c₁, hc₁, e₁⟩` from `absorb hF ht ha`. Take `⟨d, hd, hzd⟩ : ∃ d ∈ I, a * t * c = p * t * d` from `⟨c₁ * c, I.mul_mem hc₁ hc, by rw [e₁]; group⟩`. Rewrite `e`, the goal using `[hzd]`.

Take `⟨p₂, hp₂, c₃, hc₃, e₃⟩` from `absorb hF ht' (I.mul_mem hd ha₂)`. Establish `e₄ : t⁻¹ * p⁻¹ * t * t' = p₂ * t' * (c₃ * c₂)`. Establish `h1 : t⁻¹ * p⁻¹ * t * t' = d * ((p * t * d)⁻¹ * (t * t'))` using `by group`. Rewrite using `[h1, e]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hc₄ : c₃ * c₂ ∈ I` using `I.mul_mem hc₃ hc₂`. Establish `hpB : t⁻¹ * p⁻¹ * t ∈ B` using `B.mul_mem (B.mul_mem (B.inv_mem ht.1) (B.inv_mem hp.2)) ht.1`. Establish `hB : c₃ * c₂ ∈ B`. Establish `h2 : c₃ * c₂ = (p₂ * t')⁻¹ * (t⁻¹ * p⁻¹ * t * t')` using `by rw [e₄]; group`. Rewrite using `[h2]`.

Conclude with `B.mul_mem (B.inv_mem (B.mul_mem hp₂.2 ht'.1)) (B.mul_mem hpB ht'.1)`. Establish `h5` using `(ht'.2.1 _ ⟨hc₄, hB⟩).1`. Establish `h6 : t⁻¹ * p⁻¹ * t ∈ I`. Establish `h3 : t⁻¹ * p⁻¹ * t = p₂ * (t' * (c₃ * c₂) * t'⁻¹)`. Establish `h4 : t⁻¹ * p⁻¹ * t = (t⁻¹ * p⁻¹ * t * t') * t'⁻¹` using `by group`.

Rewrite using `[h4, e₄]`. Use `group`. Rewrite using `[h3]`. Conclude with `I.mul_mem hp₂.1 h5`. Establish `h7 : t⁻¹ * (p * t * d) = (t⁻¹ * p⁻¹ * t)⁻¹ * d` using `by group`.

Rewrite using `[h7]`. Conclude with `I.mul_mem (I.inv_mem h6) hd`.
-/
theorem dc_uniq (hF : Fac I B M) {t t' : H} (ht : Dom I B M t) (ht' : Dom I B M t') {z : H}
    (hz : ∃ x ∈ I, ∃ c ∈ I, z = x * t * c) (hz' : ∃ x ∈ I, ∃ c ∈ I, z⁻¹ * (t * t') = x * t' * c) :
    t⁻¹ * z ∈ I := by
  obtain ⟨a, ha, c, hc, rfl⟩ := hz
  obtain ⟨a₂, ha₂, c₂, hc₂, e⟩ := hz'
  obtain ⟨p, hp, c₁, hc₁, e₁⟩ := absorb hF ht ha
  obtain ⟨d, hd, hzd⟩ : ∃ d ∈ I, a * t * c = p * t * d := ⟨c₁ * c, I.mul_mem hc₁ hc, by rw [e₁]; group⟩
  rw [hzd] at e ⊢
  obtain ⟨p₂, hp₂, c₃, hc₃, e₃⟩ := absorb hF ht' (I.mul_mem hd ha₂)
  have e₄ : t⁻¹ * p⁻¹ * t * t' = p₂ * t' * (c₃ * c₂) := by
    have h1 : t⁻¹ * p⁻¹ * t * t' = d * ((p * t * d)⁻¹ * (t * t')) := by group
    rw [h1, e]
    calc d * (a₂ * t' * c₂) = (d * a₂) * t' * c₂ := by group
      _ = _ := by rw [e₃]; group
  have hc₄ : c₃ * c₂ ∈ I := I.mul_mem hc₃ hc₂
  have hpB : t⁻¹ * p⁻¹ * t ∈ B :=
    B.mul_mem (B.mul_mem (B.inv_mem ht.1) (B.inv_mem hp.2)) ht.1
  have hB : c₃ * c₂ ∈ B := by
    have h2 : c₃ * c₂ = (p₂ * t')⁻¹ * (t⁻¹ * p⁻¹ * t * t') := by rw [e₄]; group
    rw [h2]
    exact B.mul_mem (B.inv_mem (B.mul_mem hp₂.2 ht'.1)) (B.mul_mem hpB ht'.1)
  have h5 := (ht'.2.1 _ ⟨hc₄, hB⟩).1
  have h6 : t⁻¹ * p⁻¹ * t ∈ I := by
    have h3 : t⁻¹ * p⁻¹ * t = p₂ * (t' * (c₃ * c₂) * t'⁻¹) := by
      have h4 : t⁻¹ * p⁻¹ * t = (t⁻¹ * p⁻¹ * t * t') * t'⁻¹ := by group
      rw [h4, e₄]; group
    rw [h3]
    exact I.mul_mem hp₂.1 h5
  have h7 : t⁻¹ * (p * t * d) = (t⁻¹ * p⁻¹ * t)⁻¹ * d := by group
  rw [h7]
  exact I.mul_mem (I.inv_mem h6) hd

def dc (I : Subgroup H) (t y : H) : ℂ := if ∃ x ∈ I, ∃ z ∈ I, y = x * t * z then 1 else 0

/- English proof (translation)
Establish `hS : rStab u ⊓ K = I`. Use extensionality with `k`. Rewrite using `[Subgroup.mem_inf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, -⟩`.

Establish `h1 : u (g * k) = u g` using `h g`. Rewrite `h1` using `[hu, hu, inv_mul_cancel_left, inv_mul_cancel, if_pos I.one_mem]`. Assume the negation of the conclusion as `hk`. Rewrite `h1` using `[if_neg hk]`. Conclude with `zero_ne_one h1`.

Introduce `hk`. Use `⟨fun x => ?_, hIK hk⟩` and prove the remaining obligations. Establish `h2 : g⁻¹ * (x * k) ∈ I ↔ g⁻¹ * x ∈ I`. Rewrite using `[← mul_assoc]`. Conclude with `Subgroup.mul_mem_cancel_right I hk`.

Rewrite using `[hu, hu]`. Simplify using `only [h2]`. Unfold `hint`. Rewrite using `[hS]`. Establish `hsum : ∑ᶠ q : H ⧸ I, u q.out = 1`.

Rewrite using `[finsum_eq_single (fun q : H ⧸ I => u q.out) (QuotientGroup.mk g)]`. Rewrite using `[hu, if_pos]`. Conclude with `QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk g : H ⧸ I)).symm`. Introduce `q hq`. Rewrite using `[hu, if_neg]`.

Introduce `h`. Apply `hq` to reduce the goal to its premises. Rewrite using `[← QuotientGroup.out_eq' q]`. Conclude with `(QuotientGroup.eq.2 h).symm`. Rewrite using `[hsum, mul_one]`.
-/
theorem hint_ind (K : Subgroup H) (hIK : I ≤ K) (g : H) (u : H → ℂ)
    (hu : ∀ z, u z = if g⁻¹ * z ∈ I then 1 else 0) : hint K u = ((I.relIndex K : ℕ) : ℂ)⁻¹ := by
  have hS : rStab u ⊓ K = I := by
    ext k
    rw [Subgroup.mem_inf]
    constructor
    · rintro ⟨h, -⟩
      have h1 : u (g * k) = u g := h g
      rw [hu, hu, inv_mul_cancel_left, inv_mul_cancel, if_pos I.one_mem] at h1
      by_contra hk
      rw [if_neg hk] at h1
      exact zero_ne_one h1
    · intro hk
      refine ⟨fun x => ?_, hIK hk⟩
      have h2 : g⁻¹ * (x * k) ∈ I ↔ g⁻¹ * x ∈ I := by
        rw [← mul_assoc]; exact Subgroup.mul_mem_cancel_right I hk
      rw [hu, hu]
      simp only [h2]
  unfold hint
  rw [hS]
  have hsum : ∑ᶠ q : H ⧸ I, u q.out = 1 := by
    rw [finsum_eq_single (fun q : H ⧸ I => u q.out) (QuotientGroup.mk g)]
    · rw [hu, if_pos]
      exact QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk g : H ⧸ I)).symm
    · intro q hq
      rw [hu, if_neg]
      intro h
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact (QuotientGroup.eq.2 h).symm
  rw [hsum, mul_one]

/- English proof (translation)
Distinguish the cases in `hy : ∃ x ∈ I, ∃ c ∈ I, y = x * (t * t') * c`. Rewrite using `[dc, if_pos hy, mul_one]`. Take `⟨a, ha, c, hc, rfl⟩` from `hy`. Use `hint_ind K hIK (a * t) _ fun z => ?_` and prove the remaining obligations. Distinguish the cases in `hz : (a * t)⁻¹ * z ∈ I`.

Rewrite using `[if_pos hz, dc, dc, if_pos, if_pos, mul_one]`. Conclude with `⟨((a * t)⁻¹ * z)⁻¹, I.inv_mem hz, c, hc, by group⟩`. Conclude with `⟨a, ha, _, hz, by group⟩`. Rewrite using `[if_neg hz]`. Assume the negation of the conclusion as `hne`.

Establish `h1 : ∃ x ∈ I, ∃ c ∈ I, z = x * t * c`. Assume the negation of the conclusion as `h`. Conclude with `hne (by rw [dc, if_neg h, zero_mul])`. Establish `h2 : ∃ x ∈ I, ∃ c' ∈ I, z⁻¹ * (a * (t * t') * c) = x * t' * c'`. Assume the negation of the conclusion as `h`.

Conclude with `hne (by rw [dc, dc, if_neg h, mul_zero])`. Take `⟨x, hx, d, hd, e⟩` from `h1`. Take `⟨x₂, hx₂, d₂, hd₂, e₂⟩` from `h2`. Apply `hz` to reduce the goal to its premises. Establish `h3` using `dc_uniq hF ht ht' (z := a⁻¹ * z) ⟨a⁻¹ * x, I.mul_mem (I.inv_mem ha) hx, d, hd, by rw [e]; group⟩ ⟨x₂, hx₂, d₂ * c⁻¹, I.mul_mem hd₂ (I.inv_mem hc), by`.

Establish `h4 : (a⁻¹ * z)⁻¹ * (t * t') = (z⁻¹ * (a * (t * t') * c)) * c⁻¹` using `by group`. Rewrite using `[h4, e₂]`. Use the proof step `group⟩`. Establish `h5 : (a * t)⁻¹ * z = t⁻¹ * (a⁻¹ * z)` using `by group`. Rewrite using `[h5]`.

Conclude with `h3`. Rewrite using `[dc, if_neg hy, mul_zero]`. Establish `hu : (fun z => dc I t z * dc I t' (z⁻¹ * y)) = fun _ => 0`. Use function extensionality and compare the values at `z`. Assume the negation of the conclusion as `hne`.

Establish `h1 : ∃ x ∈ I, ∃ c ∈ I, z = x * t * c`. Assume the negation of the conclusion as `h`. Conclude with `hne (by rw [dc, if_neg h, zero_mul])`. Establish `h2 : ∃ x ∈ I, ∃ c ∈ I, z⁻¹ * y = x * t' * c`. Assume the negation of the conclusion as `h`.

Conclude with `hne (by rw [dc, dc, if_neg h, mul_zero])`. Apply `hy` to reduce the goal to its premises. Use `dc_mul hF ht ht' h1 h2` as an intermediate fact. Simplify using `using this`. Rewrite using `[hu]`.

Simplify using `[hint]`.
-/
theorem hint_dc (K : Subgroup H) (hIK : I ≤ K) (hF : Fac I B M) {t t' : H} (ht : Dom I B M t)
    (ht' : Dom I B M t') (y : H) :
    hint K (fun z => dc I t z * dc I t' (z⁻¹ * y)) = ((I.relIndex K : ℕ) : ℂ)⁻¹ * dc I (t * t') y := by
  by_cases hy : ∃ x ∈ I, ∃ c ∈ I, y = x * (t * t') * c
  · rw [dc, if_pos hy, mul_one]
    obtain ⟨a, ha, c, hc, rfl⟩ := hy
    refine hint_ind K hIK (a * t) _ fun z => ?_
    by_cases hz : (a * t)⁻¹ * z ∈ I
    · rw [if_pos hz, dc, dc, if_pos, if_pos, mul_one]
      · exact ⟨((a * t)⁻¹ * z)⁻¹, I.inv_mem hz, c, hc, by group⟩
      · exact ⟨a, ha, _, hz, by group⟩
    · rw [if_neg hz]
      by_contra hne
      have h1 : ∃ x ∈ I, ∃ c ∈ I, z = x * t * c := by
        by_contra h
        exact hne (by rw [dc, if_neg h, zero_mul])
      have h2 : ∃ x ∈ I, ∃ c' ∈ I, z⁻¹ * (a * (t * t') * c) = x * t' * c' := by
        by_contra h
        exact hne (by rw [dc, dc, if_neg h, mul_zero])
      obtain ⟨x, hx, d, hd, e⟩ := h1
      obtain ⟨x₂, hx₂, d₂, hd₂, e₂⟩ := h2
      apply hz
      have h3 := dc_uniq hF ht ht' (z := a⁻¹ * z) ⟨a⁻¹ * x, I.mul_mem (I.inv_mem ha) hx, d, hd, by rw [e]; group⟩
        ⟨x₂, hx₂, d₂ * c⁻¹, I.mul_mem hd₂ (I.inv_mem hc), by
          have h4 : (a⁻¹ * z)⁻¹ * (t * t') = (z⁻¹ * (a * (t * t') * c)) * c⁻¹ := by group
          rw [h4, e₂]; group⟩
      have h5 : (a * t)⁻¹ * z = t⁻¹ * (a⁻¹ * z) := by group
      rw [h5]
      exact h3
  · rw [dc, if_neg hy, mul_zero]
    have hu : (fun z => dc I t z * dc I t' (z⁻¹ * y)) = fun _ => 0 := by
      funext z
      by_contra hne
      have h1 : ∃ x ∈ I, ∃ c ∈ I, z = x * t * c := by
        by_contra h
        exact hne (by rw [dc, if_neg h, zero_mul])
      have h2 : ∃ x ∈ I, ∃ c ∈ I, z⁻¹ * y = x * t' * c := by
        by_contra h
        exact hne (by rw [dc, dc, if_neg h, mul_zero])
      apply hy
      have := dc_mul hF ht ht' h1 h2
      simpa using this
    rw [hu]
    simp [hint]

end Abstract

section Triangular

variable (L : Type) [Field L] (n : ℕ)

def upS : Subgroup (GL (Fin n) L) where
  carrier := {g | (∀ a b, b < a → g.val a b = 0) ∧ ∀ a b, b < a → (g⁻¹).val a b = 0}
  one_mem' := by
    refine ⟨fun a b h => ?_, fun a b h => ?_⟩
    · exact Matrix.one_apply_ne h.ne'
    · simpa using Matrix.one_apply_ne h.ne'
  mul_mem' := by
    rintro x y ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨fun a b h => ?_, fun a b h => ?_⟩
    · exact GlobalTheory.CompanionTheory.SatPow.IwFact.upper_mul h1 h3 a b h
    · rw [_root_.mul_inv_rev]
      exact GlobalTheory.CompanionTheory.SatPow.IwFact.upper_mul h4 h2 a b h
  inv_mem' := by
    rintro x ⟨h1, h2⟩
    exact ⟨h2, by simpa using h1⟩

variable {L n} in
/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge a k with h1 | h1` into its components or cases. Rewrite using `[hA a k h1, zero_mul]`. Rewrite using `[hB k b (lt_of_le_of_lt h1 h), mul_zero]`.
-/
theorem lower_mul {A B : Matrix (Fin n) (Fin n) L} (hA : ∀ a b, a < b → A a b = 0)
    (hB : ∀ a b, a < b → B a b = 0) (a b : Fin n) (h : a < b) : (A * B) a b = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge a k with h1 | h1
  · rw [hA a k h1, zero_mul]
  · rw [hB k b (lt_of_le_of_lt h1 h), mul_zero]

def loS : Subgroup (GL (Fin n) L) where
  carrier := {g | (∀ a b, a < b → g.val a b = 0) ∧ ∀ a b, a < b → (g⁻¹).val a b = 0}
  one_mem' := by
    refine ⟨fun a b h => ?_, fun a b h => ?_⟩
    · exact Matrix.one_apply_ne h.ne
    · simpa using Matrix.one_apply_ne h.ne
  mul_mem' := by
    rintro x y ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨fun a b h => ?_, fun a b h => ?_⟩
    · exact lower_mul h1 h3 a b h
    · rw [_root_.mul_inv_rev]
      exact lower_mul h4 h2 a b h
  inv_mem' := by
    rintro x ⟨h1, h2⟩
    exact ⟨h2, by simpa using h1⟩

end Triangular

section Torus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

/- English proof (translation)
Unfold `tdiag`. Rewrite using `[← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[_root_.zpow_add]`.
-/
theorem tdiag_add (ϖ : (w.adicCompletion E)ˣ) (a c : Fin n → ℤ) :
    tdiag ϖ (a + c) = tdiag ϖ a * tdiag ϖ c := by
  unfold tdiag
  rw [← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

/- English proof (translation)
Unfold `tdiag`. Rewrite using `[← map_inv]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem tdiag_inv (ϖ : (w.adicCompletion E)ˣ) (a : Fin n → ℤ) : (tdiag ϖ a)⁻¹ = tdiag ϖ (-a) := by
  unfold tdiag
  rw [← map_inv]
  congr 1
  funext i
  simp

/- English proof (translation)
Rewrite using `[tdiag, GlobalTheory.SmGL.val_diagT]`.
-/
theorem tdiag_val (ϖ : (w.adicCompletion E)ˣ) (a : Fin n → ℤ) :
    (tdiag ϖ a : GLw n w).val = Matrix.diagonal fun i => ((ϖ ^ a i : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
  rw [tdiag, GlobalTheory.SmGL.val_diagT]

/- English proof (translation)
Simplify using `only [Units.val_mul]`. Rewrite using `[tdiag_val, tdiag_val, Matrix.mul_diagonal, Matrix.diagonal_mul, _root_.zpow_add, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_apply (ϖ : (w.adicCompletion E)ˣ) (a c : Fin n → ℤ) (g : GLw n w) (i j : Fin n) :
    (tdiag ϖ a * g * tdiag ϖ c).val i j =
      ((ϖ ^ (a i + c j) : (w.adicCompletion E)ˣ) : w.adicCompletion E) * g.val i j := by
  simp only [Units.val_mul]
  rw [tdiag_val, tdiag_val, Matrix.mul_diagonal, Matrix.diagonal_mul, _root_.zpow_add, Units.val_mul]
  ring

/- English proof (translation)
Use `⟨fun i j h => ?_, fun i j h => ?_⟩` and prove the remaining obligations. Rewrite using `[tdiag_val, Matrix.diagonal_apply_ne _ h.ne']`. Rewrite using `[tdiag_inv, tdiag_val, Matrix.diagonal_apply_ne _ h.ne']`.
-/
theorem tdiag_mem_upS (ϖ : (w.adicCompletion E)ˣ) (a : Fin n → ℤ) :
    tdiag ϖ a ∈ upS (w.adicCompletion E) n := by
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · rw [tdiag_val, Matrix.diagonal_apply_ne _ h.ne']
  · rw [tdiag_inv, tdiag_val, Matrix.diagonal_apply_ne _ h.ne']

/- English proof (translation)
Use `⟨fun i j h => ?_, fun i j h => ?_⟩` and prove the remaining obligations. Rewrite using `[tdiag_val, Matrix.diagonal_apply_ne _ h.ne]`. Rewrite using `[tdiag_inv, tdiag_val, Matrix.diagonal_apply_ne _ h.ne]`.
-/
theorem tdiag_mem_loS (ϖ : (w.adicCompletion E)ˣ) (a : Fin n → ℤ) :
    tdiag ϖ a ∈ loS (w.adicCompletion E) n := by
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · rw [tdiag_val, Matrix.diagonal_apply_ne _ h.ne]
  · rw [tdiag_inv, tdiag_val, Matrix.diagonal_apply_ne _ h.ne]

/- English proof (translation)
Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le he`. Rewrite using `[map_mul, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]`. Conclude with `mul_le_of_le_one_left' (pow_le_one' hϖ.le k)`.
-/
theorem v_pow_le {ϖ : (w.adicCompletion E)ˣ} (hϖ : Valued.v (ϖ : w.adicCompletion E) < 1) {e : ℤ} (he : 0 ≤ e)
    (x : w.adicCompletion E) :
    Valued.v (((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E) * x) ≤ Valued.v x := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le he
  rw [map_mul, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  exact mul_le_of_le_one_left' (pow_le_one' hϖ.le k)

/- English proof (translation)
Establish `key : ∀ g' : GLw n w, g' ∈ iwGL n w → g' ∈ upS (w.adicCompletion E) n → ∀ i j, Valued.v ((tdiag ϖ a * g' * tdiag ϖ (-a)).val i j) ≤ 1`. Introduce `g' h1 h2 i j`. Rewrite using `[conj_apply]`. Distinguish the cases in `hij : j < i`. Rewrite using `[h2.1 i j hij, mul_zero, map_zero]`.

Conclude with `zero_le'`. Establish `hae : 0 ≤ a i + (-a) j`. Use `ha (not_lt.1 hij)` as an intermediate fact. Simplify using `only [Pi.neg_apply]`. Use linear arithmetic over natural numbers and integers.

Conclude with `(v_pow_le hϖ hae _).trans (((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g').1.1 h1).1 i j)`. Rewrite using `[tdiag_inv]`. Use `(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.2 ⟨key g hg hu, ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Establish `h3 : (tdiag ϖ a * g * tdiag ϖ (-a))⁻¹ = tdiag ϖ a * g⁻¹ * tdiag ϖ (-a)`. Rewrite using `[← tdiag_inv]`.

Use `group`. Rewrite using `[h3]`. Conclude with `key _ ((iwGL n w).inv_mem hg) ((upS _ n).inv_mem hu)`. Rewrite using `[conj_apply, hu.1 i j hij, mul_zero, map_zero]`. Conclude with `zero_lt_one`.
-/
theorem up_conj {ϖ : (w.adicCompletion E)ˣ} (hϖ : Valued.v (ϖ : w.adicCompletion E) < 1) {a : Fin n → ℤ}
    (ha : Antitone a) {g : GLw n w} (hg : g ∈ iwGL n w) (hu : g ∈ upS (w.adicCompletion E) n) :
    tdiag ϖ a * g * (tdiag ϖ a)⁻¹ ∈ iwGL n w := by
  have key : ∀ g' : GLw n w, g' ∈ iwGL n w → g' ∈ upS (w.adicCompletion E) n → ∀ i j,
      Valued.v ((tdiag ϖ a * g' * tdiag ϖ (-a)).val i j) ≤ 1 := by
    intro g' h1 h2 i j
    rw [conj_apply]
    by_cases hij : j < i
    · rw [h2.1 i j hij, mul_zero, map_zero]
      exact zero_le'
    · have hae : 0 ≤ a i + (-a) j := by
        have := ha (not_lt.1 hij)
        simp only [Pi.neg_apply]
        omega
      exact (v_pow_le hϖ hae _).trans (((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g').1.1 h1).1 i j)
  rw [tdiag_inv]
  refine (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.2 ⟨key g hg hu, ?_, fun i j hij => ?_⟩
  · have h3 : (tdiag ϖ a * g * tdiag ϖ (-a))⁻¹ = tdiag ϖ a * g⁻¹ * tdiag ϖ (-a) := by
      rw [← tdiag_inv]; group
    rw [h3]
    exact key _ ((iwGL n w).inv_mem hg) ((upS _ n).inv_mem hu)
  · rw [conj_apply, hu.1 i j hij, mul_zero, map_zero]
    exact zero_lt_one

/- English proof (translation)
Establish `key : ∀ g' : GLw n w, g' ∈ iwGL n w → g' ∈ loS (w.adicCompletion E) n → ∀ i j, Valued.v ((tdiag ϖ (-a) * g' * tdiag ϖ a).val i j) ≤ 1`. Introduce `g' h1 h2 i j`. Rewrite using `[conj_apply]`. Distinguish the cases in `hij : i < j`. Rewrite using `[h2.1 i j hij, mul_zero, map_zero]`.

Conclude with `zero_le'`. Establish `hae : 0 ≤ (-a) i + a j`. Use `ha (not_lt.1 hij)` as an intermediate fact. Simplify using `only [Pi.neg_apply]`. Use linear arithmetic over natural numbers and integers.

Conclude with `(v_pow_le hϖ hae _).trans (((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g').1.1 h1).1 i j)`. Rewrite using `[tdiag_inv]`. Use `(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.2 ⟨key g hg hu, ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Establish `h3 : (tdiag ϖ (-a) * g * tdiag ϖ a)⁻¹ = tdiag ϖ (-a) * g⁻¹ * tdiag ϖ a`. Establish `h4 : tdiag ϖ a = (tdiag ϖ (-a))⁻¹` using `by rw [tdiag_inv, neg_neg]`.

Rewrite using `[h4]`. Use `group`. Rewrite using `[h3]`. Conclude with `key _ ((iwGL n w).inv_mem hg) ((loS _ n).inv_mem hu)`. Rewrite using `[conj_apply]`.

Establish `hae : 0 ≤ (-a) i + a j`. Use `ha hij.le` as an intermediate fact. Simplify using `only [Pi.neg_apply]`. Use linear arithmetic over natural numbers and integers. Conclude with `(v_pow_le hϖ hae _).trans_lt (((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1.1 hg).2.2 i j hij)`.
-/
theorem lo_conj {ϖ : (w.adicCompletion E)ˣ} (hϖ : Valued.v (ϖ : w.adicCompletion E) < 1) {a : Fin n → ℤ}
    (ha : Antitone a) {g : GLw n w} (hg : g ∈ iwGL n w) (hu : g ∈ loS (w.adicCompletion E) n) :
    (tdiag ϖ a)⁻¹ * g * tdiag ϖ a ∈ iwGL n w := by
  have key : ∀ g' : GLw n w, g' ∈ iwGL n w → g' ∈ loS (w.adicCompletion E) n → ∀ i j,
      Valued.v ((tdiag ϖ (-a) * g' * tdiag ϖ a).val i j) ≤ 1 := by
    intro g' h1 h2 i j
    rw [conj_apply]
    by_cases hij : i < j
    · rw [h2.1 i j hij, mul_zero, map_zero]
      exact zero_le'
    · have hae : 0 ≤ (-a) i + a j := by
        have := ha (not_lt.1 hij)
        simp only [Pi.neg_apply]
        omega
      exact (v_pow_le hϖ hae _).trans (((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g').1.1 h1).1 i j)
  rw [tdiag_inv]
  refine (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.2 ⟨key g hg hu, ?_, fun i j hij => ?_⟩
  · have h3 : (tdiag ϖ (-a) * g * tdiag ϖ a)⁻¹ = tdiag ϖ (-a) * g⁻¹ * tdiag ϖ a := by
      have h4 : tdiag ϖ a = (tdiag ϖ (-a))⁻¹ := by rw [tdiag_inv, neg_neg]
      rw [h4]; group
    rw [h3]
    exact key _ ((iwGL n w).inv_mem hg) ((loS _ n).inv_mem hu)
  · rw [conj_apply]
    have hae : 0 ≤ (-a) i + a j := by
      have := ha hij.le
      simp only [Pi.neg_apply]
      omega
    exact (v_pow_le hϖ hae _).trans_lt (((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1.1 hg).2.2 i j hij)

end Torus

section Fact

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

open GlobalTheory.CompanionTheory.SatPow.IwFact

/- English proof (translation)
Establish `hEq : (ValuativeRel.valuation (w.adicCompletion E)).IsEquiv (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))`. Establish `: (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible` using `Valuation.Compatible.ofValuation _`. Conclude with `ValuativeRel.isEquiv _ _`. Conclude with `hEq.eq_one_iff_eq_one.1 (GlobalTheory.CompanionTheory.TwContraction.val_diag_of_mem_iwahori ((GlobalTheory.CompanionTheory.IwahoriContraction.mem_iwGL_iff w n g).1 hg) i)`.
-/
theorem diag_unit {g : GLw n w} (hg : g ∈ iwGL n w) (i : Fin n) : Valued.v (g.val i i) = 1 := by
  have hEq : (ValuativeRel.valuation (w.adicCompletion E)).IsEquiv
      (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) := by
    have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact ValuativeRel.isEquiv _ _
  exact hEq.eq_one_iff_eq_one.1 (GlobalTheory.CompanionTheory.TwContraction.val_diag_of_mem_iwahori
    ((GlobalTheory.CompanionTheory.IwahoriContraction.mem_iwGL_iff w n g).1 hg) i)

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1.1 hg`. Take `⟨W, Y, hW, hY, hMW, hz⟩` from `exists_fact (M := g.val) ⟨h1, h3, diag_unit hg⟩ n le_rfl`. Establish `hz' : ∀ a b : Fin n, a < b → Y a b = 0` using `fun a b h => hz a b h (by omega)`. Establish `hPW : tau (cj w) W * W = 1` using `tau_mul_self g hU hW hz' hMW`. Set `Wg : GLw n w` to `⟨W, tau (cj w) W, mul_eq_one_comm.1 hPW, hPW⟩`.

Establish `hWU : Wg ∈ GU (cj w) n` using `(GlobalTheory.LGrp.mem_GU_iff (cj w) n Wg).2 fun a b => rfl`. Establish `hWup : Wg ∈ upS (w.adicCompletion E) n`. Use `⟨hW.1, fun a b h => ?_⟩` and prove the remaining obligations. Use `show cj w (W b.rev a.rev) = 0`. Rewrite using `[hW.1 _ _ (Fin.rev_lt_rev.2 h), map_zero]`.

Establish `hWI : Wg ∈ iwGL n w`. Use `(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.2 ⟨hW.2.2, fun a b => ?_, fun a b h => ?_⟩` and prove the remaining obligations. Use `show Valued.v (cj w (W b.rev a.rev)) ≤ 1`. Rewrite using `[hcv]`. Conclude with `hW.2.2 _ _`.

Use `show Valued.v (W a b) < 1`. Rewrite using `[hW.1 a b h, map_zero]`. Conclude with `zero_lt_one`. Establish `hmI : Wg⁻¹ * g ∈ iwGL n w` using `(iwGL n w).mul_mem ((iwGL n w).inv_mem hWI) hg`. Establish `hmU : Wg⁻¹ * g ∈ GU (cj w) n` using `(GU (cj w) n).mul_mem ((GU (cj w) n).inv_mem hWU) hU`.

Establish `hval : (Wg⁻¹ * g).val = Y` using `by show tau (cj w) W * g.val = Y`. Rewrite using `[hMW, ← Matrix.mul_assoc, hPW, Matrix.one_mul]`. Use `⟨Wg, hWI, hWU, hWup, Wg⁻¹ * g, hmI, hmU, ⟨fun a b h => ?_, fun a b h => ?_⟩, by group⟩` and prove the remaining obligations. Rewrite using `[hval]`. Conclude with `hz' a b h`.

Rewrite using `[(GlobalTheory.LGrp.mem_GU_iff (cj w) n _).1 hmU a b, hval, hz' _ _ (Fin.rev_lt_rev.2 h), map_zero]`.
-/
theorem gl_fact (hcv : ∀ x, Valued.v (cj w x) = Valued.v x) {g : GLw n w} (hg : g ∈ iwGL n w)
    (hU : g ∈ GU (cj w) n) :
    ∃ p ∈ iwGL n w, p ∈ GU (cj w) n ∧ p ∈ upS (w.adicCompletion E) n ∧
      ∃ m ∈ iwGL n w, m ∈ GU (cj w) n ∧ m ∈ loS (w.adicCompletion E) n ∧ g = p * m := by
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1.1 hg
  obtain ⟨W, Y, hW, hY, hMW, hz⟩ := exists_fact (M := g.val) ⟨h1, h3, diag_unit hg⟩ n le_rfl
  have hz' : ∀ a b : Fin n, a < b → Y a b = 0 := fun a b h => hz a b h (by omega)
  have hPW : tau (cj w) W * W = 1 := tau_mul_self g hU hW hz' hMW
  let Wg : GLw n w := ⟨W, tau (cj w) W, mul_eq_one_comm.1 hPW, hPW⟩
  have hWU : Wg ∈ GU (cj w) n := (GlobalTheory.LGrp.mem_GU_iff (cj w) n Wg).2 fun a b => rfl
  have hWup : Wg ∈ upS (w.adicCompletion E) n := by
    refine ⟨hW.1, fun a b h => ?_⟩
    show cj w (W b.rev a.rev) = 0
    rw [hW.1 _ _ (Fin.rev_lt_rev.2 h), map_zero]
  have hWI : Wg ∈ iwGL n w := by
    refine (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.2 ⟨hW.2.2, fun a b => ?_, fun a b h => ?_⟩
    · show Valued.v (cj w (W b.rev a.rev)) ≤ 1
      rw [hcv]
      exact hW.2.2 _ _
    · show Valued.v (W a b) < 1
      rw [hW.1 a b h, map_zero]
      exact zero_lt_one
  have hmI : Wg⁻¹ * g ∈ iwGL n w := (iwGL n w).mul_mem ((iwGL n w).inv_mem hWI) hg
  have hmU : Wg⁻¹ * g ∈ GU (cj w) n := (GU (cj w) n).mul_mem ((GU (cj w) n).inv_mem hWU) hU
  have hval : (Wg⁻¹ * g).val = Y := by
    show tau (cj w) W * g.val = Y
    rw [hMW, ← Matrix.mul_assoc, hPW, Matrix.one_mul]
  refine ⟨Wg, hWI, hWU, hWup, Wg⁻¹ * g, hmI, hmU, ⟨fun a b h => ?_, fun a b h => ?_⟩, by group⟩
  · rw [hval]; exact hz' a b h
  · rw [(GlobalTheory.LGrp.mem_GU_iff (cj w) n _).1 hmU a b, hval, hz' _ _ (Fin.rev_lt_rev.2 h), map_zero]

end Fact

section Exponents

variable {n : ℕ}

/- English proof (translation)
Establish `key : ∀ d : ℕ, ∀ i j : Fin m, j.val = i.val + d → l j ≤ l i`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `i j h`.

Rewrite using `[show j = i from Fin.ext (by simpa using h)]`. Consider the case `succ d ih`. Introduce `i j h`. Establish `hlt : i.val + d < m`. Use `j.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h1` using `ih i ⟨i.val + d, hlt⟩ rfl`. Establish `h2` using `hl.1 ⟨i.val + d, hlt⟩ j (by simp only; omega)`. Use linear arithmetic over natural numbers and integers. Introduce `i j hij`.

Establish `h : i.val ≤ j.val` using `hij`. Conclude with `key (j.val - i.val) i j (by omega)`.
-/
theorem cone_anti {m : ℕ} {l : Fin m → ℤ} (hl : Cone l) : Antitone l := by
  have key : ∀ d : ℕ, ∀ i j : Fin m, j.val = i.val + d → l j ≤ l i := by
    intro d
    induction d with
    | zero =>
      intro i j h
      rw [show j = i from Fin.ext (by simpa using h)]
    | succ d ih =>
      intro i j h
      have hlt : i.val + d < m := by
        have := j.2
        omega
      have h1 := ih i ⟨i.val + d, hlt⟩ rfl
      have h2 := hl.1 ⟨i.val + d, hlt⟩ j (by simp only; omega)
      omega
  intro i j hij
  have h : i.val ≤ j.val := hij
  exact key (j.val - i.val) i j (by omega)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [wexp, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp <;> ring`.
-/
theorem wexp_add (l l' : Fin (n / 2) → ℤ) : wexp n (l + l') = wexp n l + wexp n l' := by
  funext i
  simp only [wexp, Pi.add_apply]
  split_ifs <;> simp <;> ring

/- English proof (translation)
Establish `hi` using `i.2`. Establish `hv : i.rev.val = n - 1 - i.val`. Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Establish `hv2 : n - 1 - i.rev.val = i.val` using `by omega`.

Unfold `wexp`. Distinguish the cases in `h1 : i.val < n / 2`. Rewrite using `[dif_pos h1, dif_neg (show ¬ i.rev.val < n / 2 by omega), dif_pos (show n - 1 - i.rev.val < n / 2 by omega)]`. Conclude with `congrArg (fun x => - l x) (Fin.ext hv2)`. Rewrite using `[dif_neg h1]`.

Distinguish the cases in `h2 : n - 1 - i.val < n / 2`. Rewrite using `[dif_pos h2, dif_pos (show i.rev.val < n / 2 by omega), neg_neg]`. Conclude with `congrArg l (Fin.ext hv)`. Rewrite using `[dif_neg h2, dif_neg (show ¬ i.rev.val < n / 2 by omega), dif_neg (show ¬ n - 1 - i.rev.val < n / 2 by omega), neg_zero]`.
-/
theorem wexp_rev (l : Fin (n / 2) → ℤ) (i : Fin n) : wexp n l i.rev = - wexp n l i := by
  have hi := i.2
  have hv : i.rev.val = n - 1 - i.val := by
    rw [Fin.val_rev]
    omega
  have hv2 : n - 1 - i.rev.val = i.val := by omega
  unfold wexp
  by_cases h1 : i.val < n / 2
  · rw [dif_pos h1, dif_neg (show ¬ i.rev.val < n / 2 by omega), dif_pos (show n - 1 - i.rev.val < n / 2 by omega)]
    exact congrArg (fun x => - l x) (Fin.ext hv2)
  · rw [dif_neg h1]
    by_cases h2 : n - 1 - i.val < n / 2
    · rw [dif_pos h2, dif_pos (show i.rev.val < n / 2 by omega), neg_neg]
      exact congrArg l (Fin.ext hv)
    · rw [dif_neg h2, dif_neg (show ¬ i.rev.val < n / 2 by omega),
        dif_neg (show ¬ n - 1 - i.rev.val < n / 2 by omega), neg_zero]

/- English proof (translation)
Establish `ha` using `cone_anti hl`. Establish `hp` using `hl.2`. Introduce `i j hij`. Establish `hij' : i.val ≤ j.val` using `hij`. Unfold `wexp`.

Distinguish the cases in `h1 : i.val < n / 2`. Rewrite using `[dif_pos h1]`. Distinguish the cases in `h2 : j.val < n / 2`. Rewrite using `[dif_pos h2]`. Conclude with `ha (show (⟨i.val, h1⟩ : Fin (n / 2)) ≤ ⟨j.val, h2⟩ from hij')`.

Rewrite using `[dif_neg h2]`. Establish `h5` using `hp ⟨i.val, h1⟩`. Use `split_ifs with h3`. Use `hp ⟨_, h3⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_neg h1, dif_neg (show ¬ j.val < n / 2 by omega)]`. Distinguish the cases in `h3 : n - 1 - i.val < n / 2`. Establish `h4 : n - 1 - j.val < n / 2` using `by omega`. Rewrite using `[dif_pos h3, dif_pos h4]`.

Use `ha (show (⟨n - 1 - j.val, h4⟩ : Fin (n / 2)) ≤ ⟨n - 1 - i.val, h3⟩ from show n - 1 - j.val ≤ n - 1 - i.val by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_neg h3] split_ifs with h4`. Use `hp ⟨_, h4⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Conclude with `le_rfl`.
-/
theorem wexp_anti {l : Fin (n / 2) → ℤ} (hl : Cone l) : Antitone (wexp n l) := by
  have ha := cone_anti hl
  have hp := hl.2
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  unfold wexp
  by_cases h1 : i.val < n / 2
  · rw [dif_pos h1]
    by_cases h2 : j.val < n / 2
    · rw [dif_pos h2]
      exact ha (show (⟨i.val, h1⟩ : Fin (n / 2)) ≤ ⟨j.val, h2⟩ from hij')
    · rw [dif_neg h2]
      have h5 := hp ⟨i.val, h1⟩
      split_ifs with h3
      · have := hp ⟨_, h3⟩
        omega
      · omega
  · rw [dif_neg h1, dif_neg (show ¬ j.val < n / 2 by omega)]
    by_cases h3 : n - 1 - i.val < n / 2
    · have h4 : n - 1 - j.val < n / 2 := by omega
      rw [dif_pos h3, dif_pos h4]
      have := ha (show (⟨n - 1 - j.val, h4⟩ : Fin (n / 2)) ≤ ⟨n - 1 - i.val, h3⟩ from
        show n - 1 - j.val ≤ n - 1 - i.val by omega)
      omega
    · rw [dif_neg h3]
      split_ifs with h4
      · have := hp ⟨_, h4⟩
        omega
      · exact le_rfl

end Exponents

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

/- English proof (translation)
Take `⟨h1, -, -, h4⟩` from `GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb`. Establish `ht : tdiag ϖ (wexp n l) ∈ UJ (cj w) (antiJ (w.adicCompletion E) n)`. Use `(h4 _).2 fun i => ?_` and prove the remaining obligations. Use `show cj w ((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ) : w.adicCompletion E) * ((ϖ ^ wexp n l i.rev : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1`. Rewrite using `[wexp_rev, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ.2, _root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ ϖ.ne_zero)]`.

Conclude with `⟨⟨_, (h1 _).2 ht⟩, rfl⟩`.
-/
theorem exists_intMod_levelPrimePow_eq_add_mul (hU : Unr E) (hw : ¬ IsSplitAt w) {b : GLw n w} (hb : IsWitt n w b)
    {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) (l : Fin (n / 2) → ℤ) :
    ∃ s : UL n w, s.1 = b * tdiag ϖ (wexp n l) * b⁻¹ := by
  obtain ⟨h1, -, -, h4⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  have ht : tdiag ϖ (wexp n l) ∈ UJ (cj w) (antiJ (w.adicCompletion E) n) := by
    refine (h4 _).2 fun i => ?_
    show cj w ((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ) : w.adicCompletion E) *
      ((ϖ ^ wexp n l i.rev : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    rw [wexp_rev, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ.2, _root_.zpow_neg,
      mul_inv_cancel₀ (zpow_ne_zero _ ϖ.ne_zero)]
  exact ⟨⟨_, (h1 _).2 ht⟩, rfl⟩

/- English proof (translation)
Introduce `E _ _ _ hU w hw n b hb ϖ hϖ l l' hl hl'`. Take `⟨hUL, hiw, -, -⟩` from `GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb`. Establish `hcv` using `(GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.1`. Establish `hv1 : Valued.v (ϖ : w.adicCompletion E) < 1` using `GlobalTheory.CompanionTheory.IwahoriContraction.v_lt_one_of_ordL_eq_one w ϖ.ne_zero hϖ.1`. Set `φ : UL n w →* GLw n w` to `(MulAut.conj b⁻¹).toMonoidHom.comp (UL n w).subtype`.

Establish `hφ : ∀ x, φ x = b⁻¹ * x.1 * b` using `fun x => by simp [φ, MulAut.conj_apply]`. Set `B : Subgroup (UL n w)` to `(upS (w.adicCompletion E) n).comap φ`. Set `M : Subgroup (UL n w)` to `((iwGL n w) ⊓ (loS (w.adicCompletion E) n)).comap φ`. Establish `hF : Fac (iwU n w b) B M`. Use `⟨fun x hx => (hiw x).2 ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hφ]`. Conclude with `hx.1`. Establish `hxI` using `(hiw x).1 hx`. Establish `hxU : b⁻¹ * x.1 * b ∈ GU (cj w) n`. Use `(hUL _).1 ?_` and prove the remaining obligations.

Establish `h1 : b * (b⁻¹ * x.1 * b) * b⁻¹ = x.1` using `by group`. Rewrite using `[h1]`. Conclude with `x.2`. Take `⟨p, hpI, hpU, hpu, m, hmI, hmU, hml, e⟩` from `gl_fact hcv hxI hxU`. Establish `hp1 : b⁻¹ * (b * p * b⁻¹) * b = p` using `by group`.

Establish `hm1 : b⁻¹ * (b * m * b⁻¹) * b = m` using `by group`. Use `⟨⟨b * p * b⁻¹, (hUL p).2 hpU⟩, ⟨(hiw _).2 ?_, ?_⟩, ⟨b * m * b⁻¹, (hUL m).2 hmU⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show b⁻¹ * (b * p * b⁻¹) * b ∈ iwGL n w`. Rewrite using `[hp1]`. Conclude with `hpI`.

Use `show φ _ ∈ upS (w.adicCompletion E) n`. Rewrite using `[hφ]`. Use `show b⁻¹ * (b * p * b⁻¹) * b ∈ upS (w.adicCompletion E) n`. Rewrite using `[hp1]`. Conclude with `hpu`.

Use `show φ _ ∈ (iwGL n w) ⊓ (loS (w.adicCompletion E) n)`. Rewrite using `[hφ]`. Use `show b⁻¹ * (b * m * b⁻¹) * b ∈ (iwGL n w) ⊓ (loS (w.adicCompletion E) n)`. Rewrite using `[hm1]`. Conclude with `⟨hmI, hml⟩`.

Apply `Subtype.ext show x.1 = b * p * b⁻¹ * (b * m * b⁻¹)` to reduce the goal to its premises. Establish `h2 : b * p * b⁻¹ * (b * m * b⁻¹) = b * (p * m) * b⁻¹` using `by group`. Rewrite using `[h2, ← e]`. Use `group`. Establish `hD : ∀ l : Fin (n / 2) → ℤ, Cone l → ∀ s : UL n w, s.1 = b * tdiag ϖ (wexp n l) * b⁻¹ → Dom (iwU n w b) B M s`.

Introduce `l hl s hs`. Establish `hφs : φ s = tdiag ϖ (wexp n l)`. Rewrite using `[hφ, hs]`. Use `group`. Establish `ha` using `wexp_anti hl`.

Use `⟨?_, fun p hp => ⟨?_, ?_⟩, fun m hm => ?_⟩` and prove the remaining obligations. Use `show φ s ∈ upS (w.adicCompletion E) n`. Rewrite using `[hφs]`. Conclude with `tdiag_mem_upS _ _`. Rewrite `*` using `[SetLike.mem_coe]`.

Use `(hiw _).2 ?_` and prove the remaining obligations. Rewrite using `[← hφ, map_mul, map_mul, map_inv, hφs]`. Establish `h1 : φ p ∈ iwGL n w`. Rewrite using `[hφ]`. Conclude with `(hiw p).1 hp.1`.

Conclude with `up_conj hv1 ha h1 hp.2`. Use `show φ (s * p * s⁻¹) ∈ upS (w.adicCompletion E) n`. Rewrite using `[map_mul, map_mul, map_inv, hφs]`. Conclude with `(upS _ n).mul_mem ((upS _ n).mul_mem (tdiag_mem_upS _ _) hp.2) ((upS _ n).inv_mem (tdiag_mem_upS _ _))`. Use `show φ (s⁻¹ * m * s) ∈ (iwGL n w) ⊓ (loS (w.adicCompletion E) n)`.

Rewrite using `[map_mul, map_mul, map_inv, hφs]`. Conclude with `⟨lo_conj hv1 ha hm.1 hm.2, (loS _ n).mul_mem ((loS _ n).mul_mem ((loS _ n).inv_mem (tdiag_mem_loS _ _)) hm.2) (tdiag_mem_loS _ _)⟩`. Establish `hIK : iwU n w b ≤ KL n w`. Introduce `x hx`. Use `Subgroup.mem_subgroupOf.2 ?_` and prove the remaining obligations.

Establish `h1` using `(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.1 ((hiw x).1 hx)`. Establish `h2 : b⁻¹ * x.1 * b ∈ GlobalTheory.LFun.KGL w n` using `(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).2.2 ⟨h1.1, h1.2.1⟩`. Establish `h3 : (x.1 : GLw n w) = b * (b⁻¹ * x.1 * b) * b⁻¹` using `by group`. Use `show (x.1 : GLw n w) ∈ GlobalTheory.LFun.KGL w n`. Rewrite using `[h3]`.

Conclude with `mul_mem (mul_mem hb.1 h2) (inv_mem hb.1)`. Establish `hf : ∀ (l : Fin (n / 2) → ℤ) (s : UL n w), s.1 = b * tdiag ϖ (wexp n l) * b⁻¹ → fU n w b ϖ l = dc (iwU n w b) s`. Introduce `l s hs`. Use function extensionality and compare the values at `γ`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations.

Rewrite using `[← hs]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, z, hz, e⟩`. Conclude with `⟨x, hx, z, hz, Subtype.ext e⟩`. Introduce and unpack `⟨x, hx, z, hz, rfl⟩`.

Conclude with `⟨x, hx, z, hz, rfl⟩`. Take `⟨s, hs⟩` from `exists_intMod_levelPrimePow_eq_add_mul hU hw hb hϖ l`. Take `⟨s', hs'⟩` from `exists_intMod_levelPrimePow_eq_add_mul hU hw hb hϖ l'`. Establish `hss : (s * s').1 = b * tdiag ϖ (wexp n (l + l')) * b⁻¹` using `by show s.1 * s'.1 = _`. Rewrite using `[hs, hs', wexp_add, tdiag_add]`.

Use `group`. Use function extensionality and compare the values at `γ`. Rewrite using `[hf l s hs, hf l' s' hs', hf (l + l') (s * s') hss]`. Conclude with `hint_dc (KL n w) hIK hF (hD l hl s hs) (hD l' hl' s' hs') γ`.
-/
theorem fuMul : FUMul := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l l' hl hl'
  obtain ⟨hUL, hiw, -, -⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  have hcv := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.1
  have hv1 : Valued.v (ϖ : w.adicCompletion E) < 1 :=
    GlobalTheory.CompanionTheory.IwahoriContraction.v_lt_one_of_ordL_eq_one w ϖ.ne_zero hϖ.1
  let φ : UL n w →* GLw n w := (MulAut.conj b⁻¹).toMonoidHom.comp (UL n w).subtype
  have hφ : ∀ x, φ x = b⁻¹ * x.1 * b := fun x => by simp [φ, MulAut.conj_apply]
  let B : Subgroup (UL n w) := (upS (w.adicCompletion E) n).comap φ
  let M : Subgroup (UL n w) := ((iwGL n w) ⊓ (loS (w.adicCompletion E) n)).comap φ
  have hF : Fac (iwU n w b) B M := by
    refine ⟨fun x hx => (hiw x).2 ?_, fun x hx => ?_⟩
    · rw [← hφ]
      exact hx.1
    have hxI := (hiw x).1 hx
    have hxU : b⁻¹ * x.1 * b ∈ GU (cj w) n := by
      refine (hUL _).1 ?_
      have h1 : b * (b⁻¹ * x.1 * b) * b⁻¹ = x.1 := by group
      rw [h1]
      exact x.2
    obtain ⟨p, hpI, hpU, hpu, m, hmI, hmU, hml, e⟩ := gl_fact hcv hxI hxU
    have hp1 : b⁻¹ * (b * p * b⁻¹) * b = p := by group
    have hm1 : b⁻¹ * (b * m * b⁻¹) * b = m := by group
    refine ⟨⟨b * p * b⁻¹, (hUL p).2 hpU⟩, ⟨(hiw _).2 ?_, ?_⟩, ⟨b * m * b⁻¹, (hUL m).2 hmU⟩, ?_, ?_⟩
    · show b⁻¹ * (b * p * b⁻¹) * b ∈ iwGL n w
      rw [hp1]
      exact hpI
    · show φ _ ∈ upS (w.adicCompletion E) n
      rw [hφ]
      show b⁻¹ * (b * p * b⁻¹) * b ∈ upS (w.adicCompletion E) n
      rw [hp1]
      exact hpu
    · show φ _ ∈ (iwGL n w) ⊓ (loS (w.adicCompletion E) n)
      rw [hφ]
      show b⁻¹ * (b * m * b⁻¹) * b ∈ (iwGL n w) ⊓ (loS (w.adicCompletion E) n)
      rw [hm1]
      exact ⟨hmI, hml⟩
    · apply Subtype.ext
      show x.1 = b * p * b⁻¹ * (b * m * b⁻¹)
      have h2 : b * p * b⁻¹ * (b * m * b⁻¹) = b * (p * m) * b⁻¹ := by group
      rw [h2, ← e]
      group
  have hD : ∀ l : Fin (n / 2) → ℤ, Cone l → ∀ s : UL n w, s.1 = b * tdiag ϖ (wexp n l) * b⁻¹ →
      Dom (iwU n w b) B M s := by
    intro l hl s hs
    have hφs : φ s = tdiag ϖ (wexp n l) := by
      rw [hφ, hs]
      group
    have ha := wexp_anti hl
    refine ⟨?_, fun p hp => ⟨?_, ?_⟩, fun m hm => ?_⟩
    · show φ s ∈ upS (w.adicCompletion E) n
      rw [hφs]
      exact tdiag_mem_upS _ _
    · rw [SetLike.mem_coe] at *
      refine (hiw _).2 ?_
      rw [← hφ, map_mul, map_mul, map_inv, hφs]
      have h1 : φ p ∈ iwGL n w := by
        rw [hφ]
        exact (hiw p).1 hp.1
      exact up_conj hv1 ha h1 hp.2
    · show φ (s * p * s⁻¹) ∈ upS (w.adicCompletion E) n
      rw [map_mul, map_mul, map_inv, hφs]
      exact (upS _ n).mul_mem ((upS _ n).mul_mem (tdiag_mem_upS _ _) hp.2) ((upS _ n).inv_mem (tdiag_mem_upS _ _))
    · show φ (s⁻¹ * m * s) ∈ (iwGL n w) ⊓ (loS (w.adicCompletion E) n)
      rw [map_mul, map_mul, map_inv, hφs]
      exact ⟨lo_conj hv1 ha hm.1 hm.2,
        (loS _ n).mul_mem ((loS _ n).mul_mem ((loS _ n).inv_mem (tdiag_mem_loS _ _)) hm.2) (tdiag_mem_loS _ _)⟩
  have hIK : iwU n w b ≤ KL n w := by
    intro x hx
    refine Subgroup.mem_subgroupOf.2 ?_
    have h1 := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.1 ((hiw x).1 hx)
    have h2 : b⁻¹ * x.1 * b ∈ GlobalTheory.LFun.KGL w n :=
      (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).2.2 ⟨h1.1, h1.2.1⟩
    have h3 : (x.1 : GLw n w) = b * (b⁻¹ * x.1 * b) * b⁻¹ := by group
    show (x.1 : GLw n w) ∈ GlobalTheory.LFun.KGL w n
    rw [h3]
    exact mul_mem (mul_mem hb.1 h2) (inv_mem hb.1)
  have hf : ∀ (l : Fin (n / 2) → ℤ) (s : UL n w), s.1 = b * tdiag ϖ (wexp n l) * b⁻¹ →
      fU n w b ϖ l = dc (iwU n w b) s := by
    intro l s hs
    funext γ
    refine if_congr ?_ rfl rfl
    rw [← hs]
    constructor
    · rintro ⟨x, hx, z, hz, e⟩
      exact ⟨x, hx, z, hz, Subtype.ext e⟩
    · rintro ⟨x, hx, z, hz, rfl⟩
      exact ⟨x, hx, z, hz, rfl⟩
  obtain ⟨s, hs⟩ := exists_intMod_levelPrimePow_eq_add_mul hU hw hb hϖ l
  obtain ⟨s', hs'⟩ := exists_intMod_levelPrimePow_eq_add_mul hU hw hb hϖ l'
  have hss : (s * s').1 = b * tdiag ϖ (wexp n (l + l')) * b⁻¹ := by
    show s.1 * s'.1 = _
    rw [hs, hs', wexp_add, tdiag_add]
    group
  funext γ
  rw [hf l s hs, hf l' s' hs', hf (l + l') (s * s') hss]
  exact hint_dc (KL n w) hIK hF (hD l hl s hs) (hD l' hl' s' hs') γ

end Main

end GlobalTheory.CompanionTheory.FUMulPf

end
