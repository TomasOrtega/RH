import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeTateSurjectivePositiveDim

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

/- English proof (translation)
Introduce `l _ K _ P M n hS hV hI hJ`. Establish `hfd : ∀ a, FiniteDimensional K (Hdg M.q a n)` using `fun a => (P.fin M hS a n).1`. Set `m : ℕ → ℕ` to `fun a => Module.finrank K (Hdg M.q a n)`. Set `bH : ∀ a, Module.Basis (Fin (m a)) K (Hdg M.q a n)` to `fun a => Module.finBasis K _`. Set `bV` to `Module.finBasis ℚ_[l] (M.V n)`.

Set `ι` to `Σ a : Fin (n + 1), Fin (m a)`. Establish `hcard : Fintype.card ι = ∑ a ∈ Finset.range (n + 1), m a`. Simplify using `only [ι, Fintype.card_sigma, Fintype.card_fin]`. Conclude with `Fin.sum_univ_eq_sum_range (fun a => m a) (n + 1)`. Establish `hdual : ∀ a (v : M.V n) (φ : Module.Dual K (Hdg M.q a n)), P.h M a n v φ = ∑ s, kC K (φ (bH a s)) * P.h M a n v ((bH a).coord s)`.

Introduce `a v φ`. Use `conv_lhs => rw [← (bH a).sum_dual_apply_smul_coord φ]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun s _ => P.lin' M a n _ v _`. Establish `hexp : ∀ a (v : M.V n) (φ : Module.Dual K (Hdg M.q a n)), P.h M a n v φ = ∑ i, qC l (bV.repr v i) * P.h M a n (bV i) φ`.

Introduce `a v φ`. Use `conv_lhs => rw [← bV.sum_repr v]`. Rewrite using `[map_sum, AddMonoidHom.finsetSum_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => P.lin M a n _ _ φ`. Establish `h1 : Module.finrank ℚ_[l] (M.V n) ≤ Fintype.card ι`.

Set `r : Fin (Module.finrank ℚ_[l] (M.V n)) → (ι → ℂ_[l])` to `fun i p => P.h M p.1 n (bV i) ((bH p.1).coord p.2)`. Establish `hr : LinearIndependent ℂ_[l] r`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `hg' : ∀ (a : Fin (n + 1)) s, ∑ i, g i * P.h M a n (bV i) ((bH a).coord s) = 0`.

Introduce `a s`. Use `congrFun hg ⟨a, s⟩` as an intermediate fact. Simplify `this` using `[r, Finset.sum_apply]`. Establish `hz` using `hI bV g ?_`. Introduce `i`.

Conclude with `congrFun hz i`. Introduce `a φ`. Distinguish the cases in `ha : n < a`. Use `(P.fin M hS a n).2 ha` as an intermediate fact. Establish `h0 : φ = 0`.

Use extensionality with `x`. Simplify using `[Subsingleton.elim x 0]`. Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Establish `key : ∀ s, ∑ i, g i * P.h M a n (bV i) ((bH a).coord s) = 0` using `fun s => hg' ⟨a, Nat.lt_succ_of_le (not_lt.1 ha)⟩ s`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hdual, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Use `_ = ∑ s, kC K (φ (bH a s)) * ∑ i, g i * P.h M a n (bV i) ((bH a).coord s) := by`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[Finset.mul_sum]`. Use `_ = 0 := by simp [key]`. Use `hr.fintype_card_le_finrank` as an intermediate fact.

Simplify `this` using `[Module.finrank_fintype_fun_eq_card]`. Establish `h2 : Fintype.card ι ≤ Module.finrank ℚ_[l] (M.V n)`. Set `c : ι → (Fin (Module.finrank ℚ_[l] (M.V n)) → ℂ_[l])` to `fun p i => P.h M p.1 n (bV i) ((bH p.1).coord p.2)`. Establish `hc : LinearIndependent ℂ_[l] c`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `g hg`. Establish `hg' : ∀ i, ∑ p : ι, g p * P.h M p.1 n (bV i) ((bH p.1).coord p.2) = 0`. Introduce `i`. Use `congrFun hg i` as an intermediate fact. Simplify `this` using `[c, Finset.sum_apply]`.

Set `z : ∀ a, Fin (m a) → ℂ_[l]` to `fun a s => if h : a < n + 1 then g ⟨⟨a, h⟩, s⟩ else 0`. Establish `e : ∀ i, ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * P.h M a n (bV i) ((bH a).coord s) = 0`. Introduce `i`. Rewrite using `[Finset.sum_range, ← hg' i, Fintype.sum_sigma]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Simplify using `only [z]`. Rewrite using `[dif_pos a.isLt]`. Establish `hz` using `hJ bH z ?_`. Introduce and unpack `⟨⟨a, ha⟩, s⟩`. Use `congrFun (hz a (Nat.lt_succ_iff.1 ha)) s` as an intermediate fact.

Simplify using `only [z, dif_pos ha] at this`. Conclude with `this`. Introduce `v`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[hexp, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ a ∈ Finset.range (n + 1), ∑ i, ∑ s, qC l (bV.repr v i) * (z a s * P.h M a n (bV i) ((bH a).coord s)) := Finset.sum_congr rfl fun a _ => Finset.sum_comm`. Use `_ = ∑ i, ∑ a ∈ Finset.range (n + 1), ∑ s, qC l (bV.repr v i) * (z a s * P.h M a n (bV i) ((bH a).coord s)) := Finset.sum_comm`.

Use `_ = ∑ i, qC l (bV.repr v i) * ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * P.h M a n (bV i) ((bH a).coord s) := by`. Repeatedly rewrite using `[Finset.mul_sum]`. Use `_ = 0 := by simp [e]`. Use `hc.fintype_card_le_finrank` as an intermediate fact. Simplify `this` using `[Module.finrank_fintype_fun_eq_card]`.

Use `le_antisymm h1 h2` as an intermediate fact. Rewrite using `[this, hcard]`.
-/
theorem rank_equality : HodgeTateDimensionEquality := by
  intro l _ K _ P M n hS hV hI hJ
  classical
  have hfd : ∀ a, FiniteDimensional K (Hdg M.q a n) := fun a => (P.fin M hS a n).1
  let m : ℕ → ℕ := fun a => Module.finrank K (Hdg M.q a n)
  let bH : ∀ a, Module.Basis (Fin (m a)) K (Hdg M.q a n) := fun a => Module.finBasis K _
  let bV := Module.finBasis ℚ_[l] (M.V n)
  let ι := Σ a : Fin (n + 1), Fin (m a)
  have hcard : Fintype.card ι = ∑ a ∈ Finset.range (n + 1), m a := by
    simp only [ι, Fintype.card_sigma, Fintype.card_fin]
    exact Fin.sum_univ_eq_sum_range (fun a => m a) (n + 1)
  have hdual : ∀ a (v : M.V n) (φ : Module.Dual K (Hdg M.q a n)),
      P.h M a n v φ = ∑ s, kC K (φ (bH a s)) * P.h M a n v ((bH a).coord s) := by
    intro a v φ
    conv_lhs => rw [← (bH a).sum_dual_apply_smul_coord φ]
    rw [map_sum]
    exact Finset.sum_congr rfl fun s _ => P.lin' M a n _ v _
  have hexp : ∀ a (v : M.V n) (φ : Module.Dual K (Hdg M.q a n)),
      P.h M a n v φ = ∑ i, qC l (bV.repr v i) * P.h M a n (bV i) φ := by
    intro a v φ
    conv_lhs => rw [← bV.sum_repr v]
    rw [map_sum, AddMonoidHom.finsetSum_apply]
    exact Finset.sum_congr rfl fun i _ => P.lin M a n _ _ φ
  have h1 : Module.finrank ℚ_[l] (M.V n) ≤ Fintype.card ι := by
    let r : Fin (Module.finrank ℚ_[l] (M.V n)) → (ι → ℂ_[l]) :=
      fun i p => P.h M p.1 n (bV i) ((bH p.1).coord p.2)
    have hr : LinearIndependent ℂ_[l] r := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hg' : ∀ (a : Fin (n + 1)) s, ∑ i, g i * P.h M a n (bV i) ((bH a).coord s) = 0 := by
        intro a s
        have := congrFun hg ⟨a, s⟩
        simpa [r, Finset.sum_apply] using this
      have hz := hI bV g ?_
      · intro i; exact congrFun hz i
      intro a φ
      by_cases ha : n < a
      · have := (P.fin M hS a n).2 ha
        have h0 : φ = 0 := by
          ext x
          simp [Subsingleton.elim x 0]
        subst h0
        simp
      · have key : ∀ s, ∑ i, g i * P.h M a n (bV i) ((bH a).coord s) = 0 :=
          fun s => hg' ⟨a, Nat.lt_succ_of_le (not_lt.1 ha)⟩ s
        calc ∑ i, g i * P.h M a n (bV i) φ
            = ∑ i, ∑ s, kC K (φ (bH a s)) * (g i * P.h M a n (bV i) ((bH a).coord s)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hdual, Finset.mul_sum]
              refine Finset.sum_congr rfl fun s _ => ?_
              ring
          _ = ∑ s, kC K (φ (bH a s)) * ∑ i, g i * P.h M a n (bV i) ((bH a).coord s) := by
              rw [Finset.sum_comm]
              simp_rw [Finset.mul_sum]
          _ = 0 := by simp [key]
    have := hr.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using this
  have h2 : Fintype.card ι ≤ Module.finrank ℚ_[l] (M.V n) := by
    let c : ι → (Fin (Module.finrank ℚ_[l] (M.V n)) → ℂ_[l]) :=
      fun p i => P.h M p.1 n (bV i) ((bH p.1).coord p.2)
    have hc : LinearIndependent ℂ_[l] c := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hg' : ∀ i, ∑ p : ι, g p * P.h M p.1 n (bV i) ((bH p.1).coord p.2) = 0 := by
        intro i
        have := congrFun hg i
        simpa [c, Finset.sum_apply] using this
      let z : ∀ a, Fin (m a) → ℂ_[l] := fun a s => if h : a < n + 1 then g ⟨⟨a, h⟩, s⟩ else 0
      have e : ∀ i, ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * P.h M a n (bV i) ((bH a).coord s) = 0 := by
        intro i
        rw [Finset.sum_range, ← hg' i, Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
        simp only [z]
        rw [dif_pos a.isLt]
      have hz := hJ bH z ?_
      · rintro ⟨⟨a, ha⟩, s⟩
        have := congrFun (hz a (Nat.lt_succ_iff.1 ha)) s
        simp only [z, dif_pos ha] at this
        exact this
      intro v
      calc ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * P.h M a n v ((bH a).coord s)
          = ∑ a ∈ Finset.range (n + 1), ∑ s, ∑ i,
              qC l (bV.repr v i) * (z a s * P.h M a n (bV i) ((bH a).coord s)) := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
            rw [hexp, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ = ∑ a ∈ Finset.range (n + 1), ∑ i, ∑ s,
              qC l (bV.repr v i) * (z a s * P.h M a n (bV i) ((bH a).coord s)) :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ i, ∑ a ∈ Finset.range (n + 1), ∑ s,
              qC l (bV.repr v i) * (z a s * P.h M a n (bV i) ((bH a).coord s)) := Finset.sum_comm
        _ = ∑ i, qC l (bV.repr v i) * ∑ a ∈ Finset.range (n + 1), ∑ s,
              z a s * P.h M a n (bV i) ((bH a).coord s) := by
            simp_rw [Finset.mul_sum]
        _ = 0 := by simp [e]
    have := hc.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using this
  have := le_antisymm h1 h2
  rw [this, hcard]

end CrystallineSemistableComparison.Onto

end
