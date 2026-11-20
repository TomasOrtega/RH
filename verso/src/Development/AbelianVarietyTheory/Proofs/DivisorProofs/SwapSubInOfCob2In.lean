import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundarySymmCocycleModStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealSubstOfConstantCoeffZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSmulProdChooseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEdgesMemOfCoboundaryTwoCoeffsInIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryDegreePartCocycleModIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCob1HomogLiftBinomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstMapToFractionsMemSubmoduleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegreeLtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOneFractionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapVariableGroupsFormalGroupLawCoboundaryOneComStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundarySwapSubRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSumElimPowerSeriesSwapVariableGroupsStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SymCob

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

def V (p : ℕ) (J : Ideal B) : Submodule B Q where
  carrier := {q | ∃ k : ℕ, ∃ b ∈ J, (p : Q) ^ k * q = algebraMap B Q b}
  zero_mem' := ⟨0, 0, J.zero_mem, by simp⟩
  add_mem' := by
    rintro q₁ q₂ ⟨k₁, b₁, hb₁, h₁⟩ ⟨k₂, b₂, hb₂, h₂⟩
    refine ⟨k₁ + k₂, (p : B) ^ k₂ * b₁ + (p : B) ^ k₁ * b₂,
      J.add_mem (J.mul_mem_left _ hb₁) (J.mul_mem_left _ hb₂), ?_⟩
    simp only [map_add, map_mul, map_pow, map_natCast, ← h₁, ← h₂]
    ring
  smul_mem' := by
    rintro b q ⟨k, b₁, hb₁, h₁⟩
    refine ⟨k, b * b₁, J.mul_mem_left _ hb₁, ?_⟩
    simp only [Algebra.smul_def, map_mul, ← h₁]
    ring

def NS (N : Ideal B) : Submodule B Q := Submodule.map (Algebra.linearMap B Q) N

/- English proof (translation)
Simplify using `only [NS, Submodule.mem_map, Algebra.linearMap_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, rfl⟩`. Conclude with `⟨b, hb, rfl⟩`. Introduce and unpack `⟨b, hb, rfl⟩`.

Conclude with `⟨b, hb, rfl⟩`.
-/
theorem mem_NS {N : Ideal B} {q : Q} : q ∈ (NS N : Submodule B Q) ↔ ∃ b ∈ N, q = algebraMap B Q b := by
  simp only [NS, Submodule.mem_map, Algebra.linearMap_apply]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_V {p : ℕ} {J : Ideal B} {q : Q} :
    q ∈ (V p J : Submodule B Q) ↔ ∃ k : ℕ, ∃ b ∈ J, (p : Q) ^ k * q = algebraMap B Q b := Iff.rfl

/- English proof (translation)
Introduce `q hq`. Take `⟨b, hb, rfl⟩` from `mem_NS.1 hq`. Conclude with `⟨0, b, h hb, by simp⟩`.
-/
theorem NS_le_V (p : ℕ) {N J : Ideal B} (h : N ≤ J) : (NS N : Submodule B Q) ≤ V p J := by
  intro q hq
  obtain ⟨b, hb, rfl⟩ := mem_NS.1 hq
  exact ⟨0, b, h hb, by simp⟩

/- English proof (translation)
Simplify using `only [In, mem_NS, eq_comm]`.
-/
theorem in_iff {σ : Type} {N : Ideal B} {f : MvPowerSeries σ Q} :
    In N f ↔ ∀ α, coeff α f ∈ (NS N : Submodule B Q) := by
  simp only [In, mem_NS, eq_comm]

/- English proof (translation)
Simplify using `only [Finsupp.degree_eq_sum, Fintype.sum_sum_type, Finsupp.sumElim_inl, Finsupp.sumElim_inr, Finsupp.add_apply, Finset.sum_add_distrib]`.
-/
theorem degree_sumElim {d : ℕ} (a e : Fin d →₀ ℕ) :
    (Finsupp.sumElim a e).degree = (a + e).degree := by
  simp only [Finsupp.degree_eq_sum, Fintype.sum_sum_type, Finsupp.sumElim_inl, Finsupp.sumElim_inr,
    Finsupp.add_apply, Finset.sum_add_distrib]

/- English proof (translation)
Take `⟨⟨a, e⟩, h⟩` from `Finsupp.sumFinsuppEquivProdFinsupp.symm.surjective α`. Conclude with `⟨a, e, by rw [← h, Finsupp.sumFinsuppEquivProdFinsupp_symm_apply]⟩`.
-/
theorem exists_sumElim {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) : ∃ a e : Fin d →₀ ℕ, α = Finsupp.sumElim a e := by
  obtain ⟨⟨a, e⟩, h⟩ := Finsupp.sumFinsuppEquivProdFinsupp.symm.surjective α
  exact ⟨a, e, by rw [← h, Finsupp.sumFinsuppEquivProdFinsupp_symm_apply]⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[up, map_X]`.
-/
theorem up_inl {d : ℕ} : up Q (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) B)) =
    fun i => X (Sum.inl i) := by
  funext i; simp [up, map_X]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[up, map_X]`.
-/
theorem up_inr {d : ℕ} : up Q (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B)) =
    fun i => X (Sum.inr i) := by
  funext i; simp [up, map_X]

end GlobalTheory.SymCob

namespace GlobalTheory.SymCob

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

/- English proof (translation)
Simplify using `[up, hμ i]`.
-/
theorem up_const {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) : constantCoeff (up Q μ i) = 0 := by
  simp [up, hμ i]

/- English proof (translation)
Rewrite using `[up_inl]`. Both sides reduce to the same expression.
-/
theorem inL_eq {d : ℕ} (f : MvPowerSeries (Fin d) Q) :
    inL f = subst (up Q (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) B))) f := by
  rw [up_inl]; rfl

/- English proof (translation)
Rewrite using `[up_inr]`. Both sides reduce to the same expression.
-/
theorem inR_eq {d : ℕ} (f : MvPowerSeries (Fin d) Q) :
    inR f = subst (up Q (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B))) f := by
  rw [up_inr]; rfl

/- English proof (translation)
Establish `h1` using `GlobalTheory.T.coeff_subst_mapToFractions_mem_submodule B Q (Fin d) (Fin d ⊕ Fin d) S f μ hμ hf α`. Establish `h2` using `GlobalTheory.T.coeff_subst_mapToFractions_mem_submodule B Q (Fin d) (Fin d ⊕ Fin d) S f _ (fun i => constantCoeff_X (Sum.inl i)) hf α`. Establish `h3` using `GlobalTheory.T.coeff_subst_mapToFractions_mem_submodule B Q (Fin d) (Fin d ⊕ Fin d) S f _ (fun i => constantCoeff_X (Sum.inr i)) hf α`. Unfold `cob1`. Rewrite using `[inL_eq (B := B), inR_eq (B := B), map_sub, map_sub]`.

Conclude with `S.sub_mem (S.sub_mem h1 h2) h3`.
-/
theorem coeff_cob1_mem_submodule {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (S : Submodule B Q) (f : MvPowerSeries (Fin d) Q)
    (hf : ∀ α, coeff α f ∈ S) (α : Fin d ⊕ Fin d →₀ ℕ) : coeff α (cob1 (up Q μ) f) ∈ S := by
  have h1 := GlobalTheory.T.coeff_subst_mapToFractions_mem_submodule B Q (Fin d) (Fin d ⊕ Fin d) S f μ hμ hf α
  have h2 := GlobalTheory.T.coeff_subst_mapToFractions_mem_submodule B Q (Fin d) (Fin d ⊕ Fin d) S f _ (fun i => constantCoeff_X (Sum.inl i)) hf α
  have h3 := GlobalTheory.T.coeff_subst_mapToFractions_mem_submodule B Q (Fin d) (Fin d ⊕ Fin d) S f _ (fun i => constantCoeff_X (Sum.inr i)) hf α
  unfold cob1
  rw [inL_eq (B := B), inR_eq (B := B), map_sub, map_sub]
  exact S.sub_mem (S.sub_mem h1 h2) h3

/- English proof (translation)
Introduce `α i`. Take `⟨b, hb, e⟩` from `hf α i`. Take `⟨b', hb', e'⟩` from `hg α i`. Conclude with `⟨b - b', N.sub_mem hb hb', by rw [map_sub, mul_sub, e, e', map_sub]⟩`.
-/
theorem din_sub {σ : Type} {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : DIn N f) (hg : DIn N g) :
    DIn N (f - g) := by
  intro α i
  obtain ⟨b, hb, e⟩ := hf α i
  obtain ⟨b', hb', e'⟩ := hg α i
  exact ⟨b - b', N.sub_mem hb hb', by rw [map_sub, mul_sub, e, e', map_sub]⟩

/- English proof (translation)
Establish `h1` using `(GlobalTheory.T.diffCoeffsInIdeal_subst_of_constantCoeff_zero p B O Q θ hF (Fin d) (Fin d ⊕ Fin d) N f μ hf hμ).1`. Establish `h2` using `(GlobalTheory.T.diffCoeffsInIdeal_subst_of_constantCoeff_zero p B O Q θ hF (Fin d) (Fin d ⊕ Fin d) N f _ hf (fun i => constantCoeff_X (Sum.inl i))).1`. Establish `h3` using `(GlobalTheory.T.diffCoeffsInIdeal_subst_of_constantCoeff_zero p B O Q θ hF (Fin d) (Fin d ⊕ Fin d) N f _ hf (fun i => constantCoeff_X (Sum.inr i))).1`. Unfold `cob1`. Rewrite using `[inL_eq (B := B), inR_eq (B := B)]`.

Conclude with `din_sub (din_sub h1 h2) h3`.
-/
theorem dIn_cob1_of_isFrame_of_dIn {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {θ : B →+* O} (hF : IsFrame p Q θ)
    {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    (hμ : ∀ i, constantCoeff (μ i) = 0) {N : Ideal B} {f : MvPowerSeries (Fin d) Q}
    (hf : DIn N f) : DIn N (cob1 (up Q μ) f) := by
  have h1 := (GlobalTheory.T.diffCoeffsInIdeal_subst_of_constantCoeff_zero p B O Q θ hF (Fin d) (Fin d ⊕ Fin d) N f μ hf hμ).1
  have h2 := (GlobalTheory.T.diffCoeffsInIdeal_subst_of_constantCoeff_zero p B O Q θ hF (Fin d) (Fin d ⊕ Fin d) N f _ hf
    (fun i => constantCoeff_X (Sum.inl i))).1
  have h3 := (GlobalTheory.T.diffCoeffsInIdeal_subst_of_constantCoeff_zero p B O Q θ hF (Fin d) (Fin d ⊕ Fin d) N f _ hf
    (fun i => constantCoeff_X (Sum.inr i))).1
  unfold cob1
  rw [inL_eq (B := B), inR_eq (B := B)]
  exact din_sub (din_sub h1 h2) h3

/- English proof (translation)
Rewrite `*` using `[in_iff]`. Introduce `α`. Rewrite using `[map_sub]`. Conclude with `Submodule.sub_mem _ (hf α) (hg α)`.
-/
theorem in_sub {σ : Type} {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) :
    In N (f - g) := by
  rw [in_iff] at *
  intro α; rw [map_sub]; exact Submodule.sub_mem _ (hf α) (hg α)

end GlobalTheory.SymCob

namespace GlobalTheory.SymCob

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

/- English proof (translation)
Establish `hμQ` using `up_const (Q := Q) hμ.const`. Establish `hlin` using `GlobalTheory.T.formalGroupLawCoboundary_swap_sub_rules Q d (up Q μ) hμQ`. Establish `hsw` using `GlobalTheory.T.swapVariableGroups_formalGroupLawCoboundaryOne_comm B Q d μ hμ.const hμ.comm h`. Establish `hco` using `GlobalTheory.T.coeff_cob1_homog_lift_binomial B O Q θ d μ hμ m h hm hhom`. Establish `hedge` using `GlobalTheory.T.coeff_edges_mem_of_coboundaryTwo_coeffsInIdeal B O Q θ d μ hμ N c h0 h2`.

Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Break down `hor with hl | ⟨hc, hh⟩` into its components or cases. Conclude with `Or.inl hl`. Conclude with `Or.inr (din_sub hc (dIn_cob1_of_isFrame_of_dIn hF hμ.const hh))`. Use `hco 0 0 (by simp)` as an intermediate fact.

Apply the tactic sequence `have hz : Finsupp.sumElim (0 : Fin d →₀ ℕ) (0 : Fin d →₀ ℕ) = 0 := by ext x; cases x <;> simp`. Simplify using `only [hz, add_zero, ne_eq, not_true_eq_false, false_and, if_false] at this`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, map_sub, this, coeff_zero_eq_constantCoeff_apply, h0, sub_zero]`. Introduce `α`. Rewrite using `[map_sub]`.

Conclude with `Submodule.sub_mem _ (hV α) (coeff_cob1_mem_submodule hμ.const _ h hhV α)`. Rewrite using `[(hlin c (cob1 (up Q μ) h) 0 0).1]`. Break down `hor with hl | ⟨hc, hh⟩` into its components or cases. Rewrite using `[GlobalTheory.T.cob2_cob1_eq_zero_of_isLaw B Q d μ hl h, sub_zero]`. Conclude with `h2`.

Establish `h3` using `(GlobalTheory.T.formalGroupLawCoboundary_symmCocycle_mod p B O Q θ hF d μ hμ N h hh).1`. Use `in_sub h2 ?_` and prove the remaining obligations. Introduce `α`. Take `⟨b, hb, e⟩` from `h3 α`. Establish `hle : RingHom.ker θ * N ≤ N` using `Ideal.mul_le_inf.trans inf_le_right`.

Conclude with `⟨b, hle hb, e⟩`. Rewrite using `[(hlin c (cob1 (up Q μ) h) 0 0).2.1, hsw]`. Establish `: swap c - cob1 (up Q μ) h - (c - cob1 (up Q μ) h) = swap c - c` using `by abel`. Rewrite using `[this]`. Conclude with `hs`.

Introduce `α hα`. Take `⟨a, e, rfl⟩` from `exists_sumElim α`. Rewrite `hα` using `[degree_sumElim]`. Establish `hco'` using `hco a e (by omega)`. Rewrite using `[map_sub, hco']`.

Break down `Nat.lt_or_ge (a + e).degree m with hlt | hge` into its components or cases. Establish `: coeff (a + e) h = 0` using `hhom _ (by omega)`. Rewrite using `[this, mul_zero, ite_self, sub_zero]`. Conclude with `hlow _ (by rw [degree_sumElim]; exact hlt)`. Establish `heq : (a + e).degree = m` using `by omega`.

Distinguish the cases in `hae : a ≠ 0 ∧ e ≠ 0`. Rewrite using `[if_pos hae]`. Conclude with `hcong a e hae.1 hae.2 heq`. Rewrite using `[if_neg hae, sub_zero]`. Break down `not_and_or.1 hae with ha | he` into its components or cases.

Rewrite using `[not_not.1 ha]`. Take `⟨b, hb, eb⟩` from `(hedge e).2`. Conclude with `mem_NS.2 ⟨b, hb, eb⟩`. Rewrite using `[not_not.1 he]`. Take `⟨b, hb, eb⟩` from `(hedge a).1`.

Conclude with `mem_NS.2 ⟨b, hb, eb⟩`.
-/
theorem maint {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {θ : B →+* O} (hF : IsFrame p Q θ)
    {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : IsLift θ μ) {N J : Ideal B}
    {m : ℕ} (hm : m ≠ 0) {c : MvPowerSeries (Fin d ⊕ Fin d) Q} {h : MvPowerSeries (Fin d) Q}
    (hor : IsLaw μ ∨ (DIn N c ∧ DIn N h)) (h0 : constantCoeff c = 0)
    (hV : ∀ α, coeff α c ∈ (V p J : Submodule B Q)) (h2 : In N (cob2 (up Q μ) c))
    (hs : In N (swap c - c)) (hlow : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → coeff α c ∈ (NS N : Submodule B Q))
    (hhom : ∀ α : Fin d →₀ ℕ, α.degree ≠ m → coeff α h = 0) (hhV : ∀ α, coeff α h ∈ (V p J : Submodule B Q))
    (hcong : ∀ a e : Fin d →₀ ℕ, a ≠ 0 → e ≠ 0 → (a + e).degree = m →
      coeff (Finsupp.sumElim a e) c - (∏ i, Nat.choose ((a + e) i) (a i) : Q) * coeff (a + e) h ∈
        (NS N : Submodule B Q)) :
    (IsLaw μ ∨ DIn N (c - cob1 (up Q μ) h)) ∧ constantCoeff (c - cob1 (up Q μ) h) = 0 ∧
      (∀ α, coeff α (c - cob1 (up Q μ) h) ∈ (V p J : Submodule B Q)) ∧
      In N (cob2 (up Q μ) (c - cob1 (up Q μ) h)) ∧
      In N (swap (c - cob1 (up Q μ) h) - (c - cob1 (up Q μ) h)) ∧
      ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m + 1 → coeff α (c - cob1 (up Q μ) h) ∈ (NS N : Submodule B Q) := by
  have hμQ := up_const (Q := Q) hμ.const
  have hlin := GlobalTheory.T.formalGroupLawCoboundary_swap_sub_rules Q d (up Q μ) hμQ
  have hsw := GlobalTheory.T.swapVariableGroups_formalGroupLawCoboundaryOne_comm B Q d μ hμ.const hμ.comm h
  have hco := GlobalTheory.T.coeff_cob1_homog_lift_binomial B O Q θ d μ hμ m h hm hhom
  have hedge := GlobalTheory.T.coeff_edges_mem_of_coboundaryTwo_coeffsInIdeal B O Q θ d μ hμ N c h0 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hor with hl | ⟨hc, hh⟩
    · exact Or.inl hl
    · exact Or.inr (din_sub hc (dIn_cob1_of_isFrame_of_dIn hF hμ.const hh))
  · have := hco 0 0 (by simp)
    have hz : Finsupp.sumElim (0 : Fin d →₀ ℕ) (0 : Fin d →₀ ℕ) = 0 := by ext x; cases x <;> simp
    simp only [hz, add_zero, ne_eq, not_true_eq_false, false_and, if_false] at this
    rw [← coeff_zero_eq_constantCoeff_apply, map_sub, this, coeff_zero_eq_constantCoeff_apply, h0, sub_zero]
  · intro α; rw [map_sub]
    exact Submodule.sub_mem _ (hV α) (coeff_cob1_mem_submodule hμ.const _ h hhV α)
  · rw [(hlin c (cob1 (up Q μ) h) 0 0).1]
    rcases hor with hl | ⟨hc, hh⟩
    · rw [GlobalTheory.T.cob2_cob1_eq_zero_of_isLaw B Q d μ hl h, sub_zero]; exact h2
    · have h3 := (GlobalTheory.T.formalGroupLawCoboundary_symmCocycle_mod p B O Q θ hF d μ hμ N h hh).1
      refine in_sub h2 ?_
      intro α
      obtain ⟨b, hb, e⟩ := h3 α
      have hle : RingHom.ker θ * N ≤ N := Ideal.mul_le_inf.trans inf_le_right
      exact ⟨b, hle hb, e⟩
  · rw [(hlin c (cob1 (up Q μ) h) 0 0).2.1, hsw]
    have : swap c - cob1 (up Q μ) h - (c - cob1 (up Q μ) h) = swap c - c := by abel
    rw [this]; exact hs
  · intro α hα
    obtain ⟨a, e, rfl⟩ := exists_sumElim α
    rw [degree_sumElim] at hα
    have hco' := hco a e (by omega)
    rw [map_sub, hco']
    rcases Nat.lt_or_ge (a + e).degree m with hlt | hge
    · have : coeff (a + e) h = 0 := hhom _ (by omega)
      rw [this, mul_zero, ite_self, sub_zero]
      exact hlow _ (by rw [degree_sumElim]; exact hlt)
    · have heq : (a + e).degree = m := by omega
      by_cases hae : a ≠ 0 ∧ e ≠ 0
      · rw [if_pos hae]; exact hcong a e hae.1 hae.2 heq
      · rw [if_neg hae, sub_zero]
        rcases not_and_or.1 hae with ha | he
        · rw [not_not.1 ha]
          obtain ⟨b, hb, eb⟩ := (hedge e).2
          exact mem_NS.2 ⟨b, hb, eb⟩
        · rw [not_not.1 he]
          obtain ⟨b, hb, eb⟩ := (hedge a).1
          exact mem_NS.2 ⟨b, hb, eb⟩

end GlobalTheory.SymCob

namespace GlobalTheory.SymCob

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

/- English proof (translation)
Simplify using `only [Finsupp.degree_eq_sum]`. Conclude with `Finset.sum_le_sum fun i _ => h i`.
-/
theorem degree_mono {d : ℕ} {a b : Fin d →₀ ℕ} (h : a ≤ b) : a.degree ≤ b.degree := by
  simp only [Finsupp.degree_eq_sum]; exact Finset.sum_le_sum fun i _ => h i

/- English proof (translation)
Rewrite using `[Finset.prod_eq_single i]`. Rewrite using `[Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.choose_symm (by omega), Nat.choose_one_right]`. Introduce `j _ hj`. Rewrite using `[Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hj), Nat.sub_zero, Nat.choose_self]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem prod_choose_pred {d : ℕ} (α : Fin d →₀ ℕ) (i : Fin d) (hi : α i ≠ 0) :
    (∏ j, Nat.choose (α j) ((α - Finsupp.single i 1 : Fin d →₀ ℕ) j) : ℕ) = α i := by
  rw [Finset.prod_eq_single i]
  · rw [Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.choose_symm (by omega), Nat.choose_one_right]
  · intro j _ hj
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hj), Nat.sub_zero, Nat.choose_self]
  · intro h; exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Use `set VJ : Submodule B Q := V p J`. Use `set K : Submodule B VJ := (NS N : Submodule B Q).comap VJ.subtype`. Establish `hK : ∀ x y : VJ, (Submodule.Quotient.mk x : VJ ⧸ K) = Submodule.Quotient.mk y ↔ (x : Q) - y ∈ (NS N : Submodule B Q)`. Introduce `x y`. Rewrite using `[Submodule.Quotient.eq]`.

Both sides reduce to the same expression. Establish `hns : ∀ (k : ℕ) (x : VJ), k • (Submodule.Quotient.mk x : VJ ⧸ K) = Submodule.Quotient.mk (k • x)` using `fun k x => (map_nsmul K.mkQ k x).symm`. Establish `hcoe : ∀ (k : ℕ) (x : VJ), ((k • x : VJ) : Q) = (k : Q) * x`. Introduce `k x`. Rewrite using `[Submodule.coe_smul_of_tower, nsmul_eq_mul]`.

Establish `hdiv : ∀ x : VJ ⧸ K, ∃ x', p • x' = x`. Introduce `x`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective K x`. Take `⟨k, b, hb, e⟩` from `v.2`. Establish `hp` using `hF.unit_p`.

Use `⟨Submodule.Quotient.mk ⟨(hp.unit⁻¹ : Qˣ) * v, k + 1, b, hb, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← e, pow_succ]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hns]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hcoe] show (p : Q) * ((hp.unit⁻¹ : Qˣ) * v) = v`. Rewrite using `[← mul_assoc, hp.mul_val_inv, one_mul]`. Establish `hbij : ∀ n : ℕ, Nat.Coprime n p → Function.Bijective fun x : VJ ⧸ K => n • x`. Introduce `n hn`.

Establish `hu` using `hF.unit_coprime n hn`. Use `Function.bijective_iff_has_inverse.2 ⟨fun x => (hu.unit⁻¹ : Bˣ) • x, ?_, ?_⟩` and prove the remaining obligations. Introduce `x show (hu.unit⁻¹ : Bˣ) • (n • x) = x`. Rewrite using `[← Nat.cast_smul_eq_nsmul B, Units.smul_def, smul_smul]`. Rewrite using `[show ((hu.unit⁻¹ : Bˣ) : B) * (n : B) = 1 from hu.val_inv_mul, one_smul]`.

Introduce `x show n • ((hu.unit⁻¹ : Bˣ) • x) = x`. Rewrite using `[← Nat.cast_smul_eq_nsmul B, Units.smul_def, smul_smul]`. Rewrite using `[show (n : B) * ((hu.unit⁻¹ : Bˣ) : B) = 1 from hu.mul_val_inv, one_smul]`. Establish `hlow' : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b`. Introduce `α hα`.

Conclude with `mem_NS.1 (hlow α hα)`. Establish `hrel` using `GlobalTheory.T.coboundary_degree_part_cocycle_mod_ideal B O Q θ d μ hμ N m c hlow' h2`. Establish `key : ∀ n : Fin d →₀ ℕ, ∃ q : VJ, n.degree = m → ∀ a, a ≤ n → a ≠ 0 → a ≠ n → coeff (Finsupp.sumElim a (n - a)) c - (∏ i, Nat.choose (n i) (a i) : Q) * q ∈ (NS N : Submodule B Q)`. Introduce `n`. Distinguish the cases in `hn : n.degree = m`.

Use `swap`. Conclude with `⟨0, fun h => absurd h hn⟩`. Set `cn : (Fin d →₀ ℕ) → VJ ⧸ K` to `fun a => Submodule.Quotient.mk ⟨coeff (Finsupp.sumElim a (n - a)) c, hV _⟩`. Establish `hsym : ∀ a, a ≤ n → cn a = cn (n - a)`. Introduce `a ha`.

Use `show Submodule.Quotient.mk _ = Submodule.Quotient.mk _`. Rewrite using `[hK]`. Simplify using `only [tsub_tsub_cancel_of_le ha]`. Use `(in_iff.1 hs) (Finsupp.sumElim (n - a) a)` as an intermediate fact. Rewrite `this` using `[map_sub, GlobalTheory.T.coeff_sumElim_powerSeriesSwapVariableGroups]`. Then use the resulting hypothesis.

Establish `hr : ∀ a b, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n → (∏ i, Nat.choose ((a + b : Fin d →₀ ℕ) i) (a i)) • cn (a + b) = (∏ i, Nat.choose ((n - a : Fin d →₀ ℕ) i) (b i)) • cn a`. Introduce `a b ha hb hab hab'`. Simplify using `only [cn, hns]`. Rewrite using `[hK, hcoe, hcoe]`. Take `⟨r, hr, e⟩` from `hrel n hn a b ha hb hab hab'`.

Use `push_cast`. Conclude with `mem_NS.2 ⟨r, hr, e⟩`. Take `⟨g, hg⟩` from `GlobalTheory.T.exists_eq_prod_choose_smul_of_choose_relation p (VJ ⧸ K) hdiv hbij d n cn hsym hr`. Take `⟨q, rfl⟩` from `Submodule.Quotient.mk_surjective K g`. Use `⟨q, fun _ a ha ha0 han => ?_⟩` and prove the remaining obligations.

Establish `h1` using `hg a ha ha0 han`. Simplify using `only [cn, hns] at h1`. Rewrite `h1` using `[hK, hcoe]`. Move the coercions through the operations in `at h1`. Conclude with `h1`.

Use `choose qf hqf using key`. Set `h : MvPowerSeries (Fin d) Q` to `fun α => if α.degree = m then (qf α : Q) else 0`. Establish `hh : ∀ α, coeff α h = if α.degree = m then (qf α : Q) else 0` using `fun α => by`. Rewrite using `[coeff_apply]`. Use `⟨h, fun α hα => by rw [hh, if_neg hα], fun α => ?_, fun hc => ?_, fun a e ha he hae => ?_⟩` and prove the remaining obligations.

Rewrite using `[hh]`. Use `split_ifs`. Conclude with `(qf α).2`. Conclude with `VJ.zero_mem`. Introduce `α i`.

Distinguish the cases in `hα : α.degree = m`. Use `swap`. Conclude with `⟨0, N.zero_mem, by rw [hh, if_neg hα, mul_zero, map_zero]⟩`. Distinguish the cases in `hi : α i = 0`. Conclude with `⟨0, N.zero_mem, by rw [hi, Nat.cast_zero, zero_mul, map_zero]⟩`.

Establish `hle1 : Finsupp.single i 1 ≤ α` using `Finsupp.single_le_iff.2 (by omega)`. Use `set a := α - Finsupp.single i 1 with ha_def`. Establish `ha : a ≤ α` using `tsub_le_self`. Establish `ha0 : a ≠ 0`. Introduce `h0`.

Establish `h3` using `degree_mono (tsub_eq_zero_iff_le.1 h0)`. Establish `h4 : (Finsupp.single i 1 : Fin d →₀ ℕ).degree = 1`. Simplify using `[Finsupp.degree_eq_sum, Finsupp.single_apply]`. Use linear arithmetic over natural numbers and integers. Establish `han : a ≠ α`.

Introduce `h0`. Use `congrArg (fun f : Fin d →₀ ℕ => f i) h0` as an intermediate fact. Simplify using `only [ha_def, Finsupp.tsub_apply, Finsupp.single_eq_same] at this`. Use linear arithmetic over natural numbers and integers. Establish `hq` using `hqf α hα a ha ha0 han`.

Rewrite `hq` using `[tsub_tsub_cancel_of_le hle1]`. Establish `hprod : (∏ j, Nat.choose (α j) (a j) : Q) = (α i : Q)`. Rewrite using `[← Nat.cast_prod, prod_choose_pred α i hi]`. Rewrite `hq` using `[hprod]`. Take `⟨b, hb, eb⟩` from `hc (Finsupp.sumElim a (Finsupp.single i 1)) (Sum.inr i)`.

Simplify using `only [Finsupp.sumElim_inr, Finsupp.single_eq_same, Nat.cast_one, one_mul] at eb`. Establish `hmem : (α i : Q) * coeff α h ∈ (NS N : Submodule B Q)`. Establish `e2 : (α i : Q) * coeff α h = coeff (Finsupp.sumElim a (Finsupp.single i 1)) c - (coeff (Finsupp.sumElim a (Finsupp.single i 1)) c - (α i : Q) * (qf α : Q))`. Rewrite using `[hh, if_pos hα]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2]`. Conclude with `Submodule.sub_mem _ (mem_NS.2 ⟨b, hb, eb⟩) hq`. Take `⟨b', hb', e'⟩` from `mem_NS.1 hmem`. Conclude with `⟨b', hb', e'⟩`. Establish `hne : a ≠ a + e`.

Introduce `h0; exact he (by simpa using h0.symm)`. Establish `hq` using `hqf (a + e) hae a le_self_add ha hne`. Rewrite `hq` using `[add_tsub_cancel_left]`. Rewrite using `[hh, if_pos hae]`. Conclude with `hq`.
-/
theorem build {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {θ : B →+* O} (hF : IsFrame p Q θ)
    {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : IsLift θ μ) {N J : Ideal B}
    (hNJ : N ≤ J) {m : ℕ} (hm : 2 ≤ m) {c : MvPowerSeries (Fin d ⊕ Fin d) Q}
    (hV : ∀ α, coeff α c ∈ (V p J : Submodule B Q)) (h2 : In N (cob2 (up Q μ) c))
    (hs : In N (swap c - c)) (hlow : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → coeff α c ∈ (NS N : Submodule B Q)) :
    ∃ h : MvPowerSeries (Fin d) Q, (∀ α : Fin d →₀ ℕ, α.degree ≠ m → coeff α h = 0) ∧
      (∀ α, coeff α h ∈ (V p J : Submodule B Q)) ∧ (DIn N c → DIn N h) ∧
      ∀ a e : Fin d →₀ ℕ, a ≠ 0 → e ≠ 0 → (a + e).degree = m →
        coeff (Finsupp.sumElim a e) c - (∏ i, Nat.choose ((a + e) i) (a i) : Q) * coeff (a + e) h ∈
          (NS N : Submodule B Q) := by
  set VJ : Submodule B Q := V p J
  set K : Submodule B VJ := (NS N : Submodule B Q).comap VJ.subtype
  have hK : ∀ x y : VJ, (Submodule.Quotient.mk x : VJ ⧸ K) = Submodule.Quotient.mk y ↔
      (x : Q) - y ∈ (NS N : Submodule B Q) := by
    intro x y; rw [Submodule.Quotient.eq]; rfl
  have hns : ∀ (k : ℕ) (x : VJ), k • (Submodule.Quotient.mk x : VJ ⧸ K) = Submodule.Quotient.mk (k • x) :=
    fun k x => (map_nsmul K.mkQ k x).symm
  have hcoe : ∀ (k : ℕ) (x : VJ), ((k • x : VJ) : Q) = (k : Q) * x := by
    intro k x; rw [Submodule.coe_smul_of_tower, nsmul_eq_mul]
  have hdiv : ∀ x : VJ ⧸ K, ∃ x', p • x' = x := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective K x
    obtain ⟨k, b, hb, e⟩ := v.2
    have hp := hF.unit_p
    refine ⟨Submodule.Quotient.mk ⟨(hp.unit⁻¹ : Qˣ) * v, k + 1, b, hb, ?_⟩, ?_⟩
    · rw [← e, pow_succ]
      calc (p : Q) ^ k * (p : Q) * ((hp.unit⁻¹ : Qˣ) * v)
          = (p : Q) ^ k * (((p : Q) * (hp.unit⁻¹ : Qˣ)) * v) := by ring
        _ = (p : Q) ^ k * v := by rw [show (p : Q) * (hp.unit⁻¹ : Qˣ) = 1 from hp.mul_val_inv, one_mul]
    · rw [hns]; congr 1; apply Subtype.ext; rw [hcoe]
      show (p : Q) * ((hp.unit⁻¹ : Qˣ) * v) = v
      rw [← mul_assoc, hp.mul_val_inv, one_mul]
  have hbij : ∀ n : ℕ, Nat.Coprime n p → Function.Bijective fun x : VJ ⧸ K => n • x := by
    intro n hn
    have hu := hF.unit_coprime n hn
    refine Function.bijective_iff_has_inverse.2 ⟨fun x => (hu.unit⁻¹ : Bˣ) • x, ?_, ?_⟩
    · intro x
      show (hu.unit⁻¹ : Bˣ) • (n • x) = x
      rw [← Nat.cast_smul_eq_nsmul B, Units.smul_def, smul_smul]
      rw [show ((hu.unit⁻¹ : Bˣ) : B) * (n : B) = 1 from hu.val_inv_mul, one_smul]
    · intro x
      show n • ((hu.unit⁻¹ : Bˣ) • x) = x
      rw [← Nat.cast_smul_eq_nsmul B, Units.smul_def, smul_smul]
      rw [show (n : B) * ((hu.unit⁻¹ : Bˣ) : B) = 1 from hu.mul_val_inv, one_smul]
  have hlow' : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b := by
    intro α hα; exact mem_NS.1 (hlow α hα)
  have hrel := GlobalTheory.T.coboundary_degree_part_cocycle_mod_ideal B O Q θ d μ hμ N m c hlow' h2
  have key : ∀ n : Fin d →₀ ℕ, ∃ q : VJ, n.degree = m → ∀ a, a ≤ n → a ≠ 0 → a ≠ n →
      coeff (Finsupp.sumElim a (n - a)) c - (∏ i, Nat.choose (n i) (a i) : Q) * q ∈ (NS N : Submodule B Q) := by
    intro n
    by_cases hn : n.degree = m
    swap
    · exact ⟨0, fun h => absurd h hn⟩
    let cn : (Fin d →₀ ℕ) → VJ ⧸ K := fun a =>
      Submodule.Quotient.mk ⟨coeff (Finsupp.sumElim a (n - a)) c, hV _⟩
    have hsym : ∀ a, a ≤ n → cn a = cn (n - a) := by
      intro a ha
      show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      rw [hK]
      simp only [tsub_tsub_cancel_of_le ha]
      have := (in_iff.1 hs) (Finsupp.sumElim (n - a) a)
      rwa [map_sub, GlobalTheory.T.coeff_sumElim_powerSeriesSwapVariableGroups] at this
    have hr : ∀ a b, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n →
        (∏ i, Nat.choose ((a + b : Fin d →₀ ℕ) i) (a i)) • cn (a + b) =
          (∏ i, Nat.choose ((n - a : Fin d →₀ ℕ) i) (b i)) • cn a := by
      intro a b ha hb hab hab'
      simp only [cn, hns]
      rw [hK, hcoe, hcoe]
      obtain ⟨r, hr, e⟩ := hrel n hn a b ha hb hab hab'
      push_cast
      exact mem_NS.2 ⟨r, hr, e⟩
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_eq_prod_choose_smul_of_choose_relation p (VJ ⧸ K) hdiv hbij d n cn hsym hr
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective K g
    refine ⟨q, fun _ a ha ha0 han => ?_⟩
    have h1 := hg a ha ha0 han
    simp only [cn, hns] at h1
    rw [hK, hcoe] at h1
    push_cast at h1
    exact h1
  choose qf hqf using key
  let h : MvPowerSeries (Fin d) Q := fun α => if α.degree = m then (qf α : Q) else 0
  have hh : ∀ α, coeff α h = if α.degree = m then (qf α : Q) else 0 := fun α => by
    rw [coeff_apply]
  refine ⟨h, fun α hα => by rw [hh, if_neg hα], fun α => ?_, fun hc => ?_, fun a e ha he hae => ?_⟩
  · rw [hh]; split_ifs
    · exact (qf α).2
    · exact VJ.zero_mem
  · intro α i
    by_cases hα : α.degree = m
    swap
    · exact ⟨0, N.zero_mem, by rw [hh, if_neg hα, mul_zero, map_zero]⟩
    by_cases hi : α i = 0
    · exact ⟨0, N.zero_mem, by rw [hi, Nat.cast_zero, zero_mul, map_zero]⟩
    have hle1 : Finsupp.single i 1 ≤ α := Finsupp.single_le_iff.2 (by omega)
    set a := α - Finsupp.single i 1 with ha_def
    have ha : a ≤ α := tsub_le_self
    have ha0 : a ≠ 0 := by
      intro h0
      have h3 := degree_mono (tsub_eq_zero_iff_le.1 h0)
      have h4 : (Finsupp.single i 1 : Fin d →₀ ℕ).degree = 1 := by
        simp [Finsupp.degree_eq_sum, Finsupp.single_apply]
      omega
    have han : a ≠ α := by
      intro h0
      have := congrArg (fun f : Fin d →₀ ℕ => f i) h0
      simp only [ha_def, Finsupp.tsub_apply, Finsupp.single_eq_same] at this
      omega
    have hq := hqf α hα a ha ha0 han
    rw [tsub_tsub_cancel_of_le hle1] at hq
    have hprod : (∏ j, Nat.choose (α j) (a j) : Q) = (α i : Q) := by
      rw [← Nat.cast_prod, prod_choose_pred α i hi]
    rw [hprod] at hq
    obtain ⟨b, hb, eb⟩ := hc (Finsupp.sumElim a (Finsupp.single i 1)) (Sum.inr i)
    simp only [Finsupp.sumElim_inr, Finsupp.single_eq_same, Nat.cast_one, one_mul] at eb
    have hmem : (α i : Q) * coeff α h ∈ (NS N : Submodule B Q) := by
      have e2 : (α i : Q) * coeff α h = coeff (Finsupp.sumElim a (Finsupp.single i 1)) c -
          (coeff (Finsupp.sumElim a (Finsupp.single i 1)) c - (α i : Q) * (qf α : Q)) := by
        rw [hh, if_pos hα]; ring
      rw [e2]
      exact Submodule.sub_mem _ (mem_NS.2 ⟨b, hb, eb⟩) hq
    obtain ⟨b', hb', e'⟩ := mem_NS.1 hmem
    exact ⟨b', hb', e'⟩
  · have hne : a ≠ a + e := by
      intro h0; exact he (by simpa using h0.symm)
    have hq := hqf (a + e) hae a le_self_add ha hne
    rw [add_tsub_cancel_left] at hq
    rw [hh, if_pos hae]
    exact hq

end GlobalTheory.SymCob

namespace GlobalTheory.SymCob

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

/- English proof (translation)
Simplify using `only [Finsupp.degree_eq_sum, Finsupp.add_apply, Finset.sum_add_distrib]`.
-/
theorem degree_add' {d : ℕ} (a e : Fin d →₀ ℕ) : (a + e).degree = a.degree + e.degree := by
  simp only [Finsupp.degree_eq_sum, Finsupp.add_apply, Finset.sum_add_distrib]

def Inv (p : ℕ) {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (N J : Ideal B) (m : ℕ)
    (c : MvPowerSeries (Fin d ⊕ Fin d) Q) : Prop :=
  (IsLaw μ ∨ DIn N c) ∧ constantCoeff c = 0 ∧ (∀ α, coeff α c ∈ (V p J : Submodule B Q)) ∧
    In N (cob2 (up Q μ) c) ∧ In N (swap c - c) ∧
    ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → coeff α c ∈ (NS N : Submodule B Q)

/- English proof (translation)
Take `⟨hor, h0, hV, h2, hs, hlow⟩` from `hc`. Distinguish the cases in `hm2 : 2 ≤ m`. Take `⟨h, hhom, hhV, hdin, hcong⟩` from `build hF hμ hNJ hm2 hV h2 hs hlow`. Use `⟨h, fun α hα => hhom α (by omega), hhV, ?_⟩` and prove the remaining obligations. Establish `hor' : IsLaw μ ∨ (DIn N c ∧ DIn N h)`.

Break down `hor with hl | hd` into its components or cases. Conclude with `Or.inl hl`. Conclude with `Or.inr ⟨hd, hdin hd⟩`. Conclude with `maint hF hμ hm hor' h0 hV h2 hs hlow hhom hhV hcong`. Use `⟨0, fun α _ => by simp, fun α => by simp, ?_⟩` and prove the remaining obligations.

Establish `hor' : IsLaw μ ∨ (DIn N c ∧ DIn N (0 : MvPowerSeries (Fin d) Q))`. Break down `hor with hl | hd` into its components or cases. Conclude with `Or.inl hl`. Conclude with `Or.inr ⟨hd, fun α i => ⟨0, N.zero_mem, by simp⟩⟩`. Use `maint hF hμ hm hor' h0 hV h2 hs hlow (fun α _ => by simp) (fun α => by simp) ?_` and prove the remaining obligations.

Introduce `a e ha he hae`. Establish `h1 : a.degree ≠ 0` using `fun h => ha ((Finsupp.degree_eq_zero_iff a).1 h)`. Establish `h3 : e.degree ≠ 0` using `fun h => he ((Finsupp.degree_eq_zero_iff e).1 h)`. Rewrite `hae` using `[degree_add']`. Use linear arithmetic over natural numbers and integers.
-/
theorem step {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {θ : B →+* O} (hF : IsFrame p Q θ)
    {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : IsLift θ μ) {N J : Ideal B}
    (hNJ : N ≤ J) {m : ℕ} (hm : m ≠ 0) {c : MvPowerSeries (Fin d ⊕ Fin d) Q}
    (hc : Inv p μ N J m c) :
    ∃ h : MvPowerSeries (Fin d) Q, (∀ α : Fin d →₀ ℕ, (α.degree < 2 ∨ α.degree ≠ m) → coeff α h = 0) ∧
      (∀ α, coeff α h ∈ (V p J : Submodule B Q)) ∧ Inv p μ N J (m + 1) (c - cob1 (up Q μ) h) := by
  obtain ⟨hor, h0, hV, h2, hs, hlow⟩ := hc
  by_cases hm2 : 2 ≤ m
  · obtain ⟨h, hhom, hhV, hdin, hcong⟩ := build hF hμ hNJ hm2 hV h2 hs hlow
    refine ⟨h, fun α hα => hhom α (by omega), hhV, ?_⟩
    have hor' : IsLaw μ ∨ (DIn N c ∧ DIn N h) := by
      rcases hor with hl | hd
      · exact Or.inl hl
      · exact Or.inr ⟨hd, hdin hd⟩
    exact maint hF hμ hm hor' h0 hV h2 hs hlow hhom hhV hcong
  · refine ⟨0, fun α _ => by simp, fun α => by simp, ?_⟩
    have hor' : IsLaw μ ∨ (DIn N c ∧ DIn N (0 : MvPowerSeries (Fin d) Q)) := by
      rcases hor with hl | hd
      · exact Or.inl hl
      · exact Or.inr ⟨hd, fun α i => ⟨0, N.zero_mem, by simp⟩⟩
    refine maint hF hμ hm hor' h0 hV h2 hs hlow (fun α _ => by simp) (fun α => by simp) ?_
    intro a e ha he hae
    have h1 : a.degree ≠ 0 := fun h => ha ((Finsupp.degree_eq_zero_iff a).1 h)
    have h3 : e.degree ≠ 0 := fun h => he ((Finsupp.degree_eq_zero_iff e).1 h)
    rw [degree_add'] at hae
    omega

/- English proof (translation)
Establish `h1` using `GlobalTheory.T.coeff_subst_eq_zero_of_degree_lt' Q (Fin d) (Fin d ⊕ Fin d) (up Q μ) f M (up_const hμ) hf α hα`. Establish `h2` using `GlobalTheory.T.coeff_subst_eq_zero_of_degree_lt' Q (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inl i)) f M (fun i => constantCoeff_X _) hf α hα`. Establish `h3` using `GlobalTheory.T.coeff_subst_eq_zero_of_degree_lt' Q (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inr i)) f M (fun i => constantCoeff_X _) hf α hα`. Unfold `cob1 inL inR`. Rewrite using `[map_sub, map_sub, h1, h2, h3, sub_zero, sub_zero]`.
-/
theorem coeff_cob1_low_degree_vanish {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) Q) (M : ℕ)
    (hf : ∀ β : Fin d →₀ ℕ, β.degree < M → coeff β f = 0) (α : Fin d ⊕ Fin d →₀ ℕ)
    (hα : α.degree < M) : coeff α (cob1 (up Q μ) f) = 0 := by
  have h1 := GlobalTheory.T.coeff_subst_eq_zero_of_degree_lt' Q (Fin d) (Fin d ⊕ Fin d) (up Q μ) f M (up_const hμ) hf α hα
  have h2 := GlobalTheory.T.coeff_subst_eq_zero_of_degree_lt' Q (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inl i)) f M
    (fun i => constantCoeff_X _) hf α hα
  have h3 := GlobalTheory.T.coeff_subst_eq_zero_of_degree_lt' Q (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inr i)) f M
    (fun i => constantCoeff_X _) hf α hα
  unfold cob1 inL inR
  rw [map_sub, map_sub, h1, h2, h3, sub_zero, sub_zero]

end GlobalTheory.SymCob

open GlobalTheory.SymCob in
/- English proof (translation)
Introduce `p _ B O Q _ _ _ _ θ hF d μ hμ N J hNJ c hor h0 hVc h2 hs`. Establish `hV : ∀ α, coeff α c ∈ (V p J : Submodule B Q)` using `hVc`. Establish `step' : ∀ (k : ℕ) (c' : MvPowerSeries (Fin d ⊕ Fin d) Q), ∃ h : MvPowerSeries (Fin d) Q, Inv p μ N J (k + 1) c' → (∀ α : Fin d →₀ ℕ, (α.degree < 2 ∨ α.degree ≠ k + 1) → coeff α h = 0) ∧ (∀ α, coeff α h ∈ (V p J : Submodule B Q)) ∧ Inv p μ N J (k + 1 + 1) (c' - cob1 (up Q μ) h)`. Introduce `k c'`. Distinguish the cases in `hP : Inv p μ N J (k + 1) c'`.

Take `⟨h, h1, h2, h3⟩` from `step hF hμ hNJ (Nat.succ_ne_zero k) hP`. Conclude with `⟨h, fun _ => ⟨h1, h2, h3⟩⟩`. Conclude with `⟨0, fun h => absurd h hP⟩`. Use `choose H hH using step'`. Set `s : ℕ → MvPowerSeries (Fin d ⊕ Fin d) Q` to `fun k => Nat.rec c (fun k sk => sk - cob1 (up Q μ) (H k sk)) k`.

Establish `hsS : ∀ k, s (k + 1) = s k - cob1 (up Q μ) (H k (s k))` using `fun k => rfl`. Establish `hP : ∀ k, Inv p μ N J (k + 1) (s k)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Use `⟨hor, h0, hV, h2, hs, fun α hα => ?_⟩` and prove the remaining obligations. Establish `: α = 0` using `(Finsupp.degree_eq_zero_iff α).1 (by omega)`. Substitute `this` using the available equality. Use `show coeff 0 c ∈ _`. Rewrite using `[coeff_zero_eq_constantCoeff_apply, h0]`.

Conclude with `Submodule.zero_mem _`. Consider the case `succ k ih => rw [hsS]`. Conclude with `(hH k (s k) ih).2.2`. Set `piece : ℕ → MvPowerSeries (Fin d) Q` to `fun k => H k (s k)`. Establish `hpz : ∀ k, ∀ α : Fin d →₀ ℕ, (α.degree < 2 ∨ α.degree ≠ k + 1) → coeff α (piece k) = 0` using `fun k => (hH k (s k) (hP k)).1`.

Establish `hpV : ∀ k α, coeff α (piece k) ∈ (V p J : Submodule B Q)` using `fun k => (hH k (s k) (hP k)).2.1`. Establish `hμQ` using `up_const (Q := Q) hμ.const`. Establish `hc0 : cob1 (up Q μ) (0 : MvPowerSeries (Fin d) Q) = 0`. Use `formalCoboundary_smul hμQ (0 : Q) (0 : MvPowerSeries (Fin d) Q)` as an intermediate fact. Simplify using `using this`.

Set `G : ℕ → MvPowerSeries (Fin d) Q` to `fun k => ∑ j ∈ Finset.range k, piece j`. Establish `hsG : ∀ k, s k = c - cob1 (up Q μ) (G k)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => show c = c - cob1 (up Q μ) (∑ j ∈ Finset.range 0, piece j)`.

Rewrite using `[Finset.sum_range_zero, hc0, sub_zero]`. Consider the case `succ k ih`. Rewrite using `[hsS]`. Express the relevant statement in the definitionally equal form `s k - cob1 (up Q μ) (piece k) = c - cob1 (up Q μ) (∑ j ∈ Finset.range (k + 1), piece j)`. Rewrite using `[ih]`.

Rewrite using `[Finset.sum_range_succ, formalCoboundary_add hμQ]`. Normalize the expressions using the abelian group laws. Set `g : MvPowerSeries (Fin d) Q` to `fun α => ∑ j ∈ Finset.range α.degree, coeff α (piece j)`. Establish `hg : ∀ α, coeff α g = ∑ j ∈ Finset.range α.degree, coeff α (piece j)` using `fun α => by`. Rewrite using `[coeff_apply]`.

Establish `hgG : ∀ k (α : Fin d →₀ ℕ), α.degree ≤ k → coeff α g = coeff α (G k)`. Introduce `k α hk`. Rewrite using `[hg]`. Use `show _ = coeff α (∑ j ∈ Finset.range k, piece j)`. Rewrite using `[map_sum]`.

Use `Finset.sum_subset (Finset.range_mono hk) fun j _ hj => hpz j α (Or.inr ?_)` and prove the remaining obligations. Rewrite `hj` using `[Finset.mem_range, not_lt]`. Use linear arithmetic over natural numbers and integers. Use `⟨g, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, hg]`.

Simplify using the standard rewrite rules. Use function extensionality and compare the values at `i show coeff (Finsupp.single i 1) g = 0`. Rewrite using `[hg]`. Establish `hd : (Finsupp.single i 1 : Fin d →₀ ℕ).degree = 1`. Simplify using `[Finsupp.degree_eq_sum, Finsupp.single_apply]`.

Rewrite using `[hd, Finset.sum_range_one]`. Conclude with `hpz 0 _ (Or.inl (by omega))`. Introduce `α show coeff α g ∈ (V p J : Submodule B Q)`. Rewrite using `[hg]`. Conclude with `Submodule.sum_mem _ fun j _ => hpV j α`.

Rewrite using `[in_iff]`. Introduce `α`. Establish `hdiff : coeff α (cob1 (up Q μ) (g - G α.degree)) = 0`. Use `coeff_cob1_low_degree_vanish hμ.const _ (α.degree + 1) (fun β hβ => ?_) α (by omega)` and prove the remaining obligations. Rewrite using `[map_sub, hgG α.degree β (by omega), sub_self]`.

Rewrite `hdiff` using `[(GlobalTheory.T.formalGroupLawCoboundary_swap_sub_rules Q d (up Q μ) hμQ 0 0 g (G α.degree)).2.2, map_sub, sub_eq_zero]`. Rewrite using `[map_sub, hdiff, ← map_sub, ← hsG]`. Conclude with `(hP α.degree).2.2.2.2.2 α (by omega)`.
-/
theorem GlobalTheory.symmetric_cocycle_is_coboundary_mod : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N J : Ideal B), N ≤ J → ∀ c : MvPowerSeries (Fin d ⊕ Fin d) Q, (IsLaw μ ∨ DIn N c) → constantCoeff c = 0 → (∀ α, ∃ k : ℕ, ∃ b ∈ J, (p : Q) ^ k * coeff α c = algebraMap B Q b) → In N (cob2 (up Q μ) c) → In N (swap c - c) → ∃ g : MvPowerSeries (Fin d) Q, constantCoeff g = 0 ∧ lin g = 0 ∧ (∀ α, ∃ k : ℕ, ∃ b ∈ J, (p : Q) ^ k * coeff α g = algebraMap B Q b) ∧ In N (c - cob1 (up Q μ) g) := by
  intro p _ B O Q _ _ _ _ θ hF d μ hμ N J hNJ c hor h0 hVc h2 hs
  have hV : ∀ α, coeff α c ∈ (V p J : Submodule B Q) := hVc
  have step' : ∀ (k : ℕ) (c' : MvPowerSeries (Fin d ⊕ Fin d) Q), ∃ h : MvPowerSeries (Fin d) Q,
      Inv p μ N J (k + 1) c' → (∀ α : Fin d →₀ ℕ, (α.degree < 2 ∨ α.degree ≠ k + 1) → coeff α h = 0) ∧
        (∀ α, coeff α h ∈ (V p J : Submodule B Q)) ∧ Inv p μ N J (k + 1 + 1) (c' - cob1 (up Q μ) h) := by
    intro k c'
    by_cases hP : Inv p μ N J (k + 1) c'
    · obtain ⟨h, h1, h2, h3⟩ := step hF hμ hNJ (Nat.succ_ne_zero k) hP
      exact ⟨h, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose H hH using step'
  let s : ℕ → MvPowerSeries (Fin d ⊕ Fin d) Q := fun k =>
    Nat.rec c (fun k sk => sk - cob1 (up Q μ) (H k sk)) k
  have hsS : ∀ k, s (k + 1) = s k - cob1 (up Q μ) (H k (s k)) := fun k => rfl
  have hP : ∀ k, Inv p μ N J (k + 1) (s k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨hor, h0, hV, h2, hs, fun α hα => ?_⟩
      have : α = 0 := (Finsupp.degree_eq_zero_iff α).1 (by omega)
      subst this
      show coeff 0 c ∈ _
      rw [coeff_zero_eq_constantCoeff_apply, h0]; exact Submodule.zero_mem _
    | succ k ih => rw [hsS]; exact (hH k (s k) ih).2.2
  let piece : ℕ → MvPowerSeries (Fin d) Q := fun k => H k (s k)
  have hpz : ∀ k, ∀ α : Fin d →₀ ℕ, (α.degree < 2 ∨ α.degree ≠ k + 1) → coeff α (piece k) = 0 :=
    fun k => (hH k (s k) (hP k)).1
  have hpV : ∀ k α, coeff α (piece k) ∈ (V p J : Submodule B Q) := fun k => (hH k (s k) (hP k)).2.1
  have hμQ := up_const (Q := Q) hμ.const
  have hc0 : cob1 (up Q μ) (0 : MvPowerSeries (Fin d) Q) = 0 := by
    have := formalCoboundary_smul hμQ (0 : Q) (0 : MvPowerSeries (Fin d) Q)
    simpa using this
  let G : ℕ → MvPowerSeries (Fin d) Q := fun k => ∑ j ∈ Finset.range k, piece j
  have hsG : ∀ k, s k = c - cob1 (up Q μ) (G k) := by
    intro k
    induction k with
    | zero => show c = c - cob1 (up Q μ) (∑ j ∈ Finset.range 0, piece j); rw [Finset.sum_range_zero, hc0, sub_zero]
    | succ k ih =>
      rw [hsS]
      change s k - cob1 (up Q μ) (piece k) = c - cob1 (up Q μ) (∑ j ∈ Finset.range (k + 1), piece j)
      rw [ih]
      rw [Finset.sum_range_succ, formalCoboundary_add hμQ]
      abel
  let g : MvPowerSeries (Fin d) Q := fun α => ∑ j ∈ Finset.range α.degree, coeff α (piece j)
  have hg : ∀ α, coeff α g = ∑ j ∈ Finset.range α.degree, coeff α (piece j) := fun α => by
    rw [coeff_apply]
  have hgG : ∀ k (α : Fin d →₀ ℕ), α.degree ≤ k → coeff α g = coeff α (G k) := by
    intro k α hk
    rw [hg]
    show _ = coeff α (∑ j ∈ Finset.range k, piece j)
    rw [map_sum]
    refine Finset.sum_subset (Finset.range_mono hk) fun j _ hj => hpz j α (Or.inr ?_)
    rw [Finset.mem_range, not_lt] at hj
    omega
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, hg]; simp
  · funext i
    show coeff (Finsupp.single i 1) g = 0
    rw [hg]
    have hd : (Finsupp.single i 1 : Fin d →₀ ℕ).degree = 1 := by
      simp [Finsupp.degree_eq_sum, Finsupp.single_apply]
    rw [hd, Finset.sum_range_one]
    exact hpz 0 _ (Or.inl (by omega))
  · intro α
    show coeff α g ∈ (V p J : Submodule B Q)
    rw [hg]
    exact Submodule.sum_mem _ fun j _ => hpV j α
  · rw [in_iff]
    intro α
    have hdiff : coeff α (cob1 (up Q μ) (g - G α.degree)) = 0 := by
      refine coeff_cob1_low_degree_vanish hμ.const _ (α.degree + 1) (fun β hβ => ?_) α (by omega)
      rw [map_sub, hgG α.degree β (by omega), sub_self]
    rw [(GlobalTheory.T.formalGroupLawCoboundary_swap_sub_rules Q d (up Q μ) hμQ 0 0 g (G α.degree)).2.2, map_sub, sub_eq_zero] at hdiff
    rw [map_sub, hdiff, ← map_sub, ← hsG]
    exact (hP α.degree).2.2.2.2.2 α (by omega)
