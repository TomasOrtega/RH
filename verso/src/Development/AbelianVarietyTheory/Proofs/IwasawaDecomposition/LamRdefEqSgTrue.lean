import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Formalism.LocalToGlobal.Columns.BaseLemmas

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowWeight

/- English proof (translation)
Substitute `h` using the available equality. Take `⟨hcard, c, hc, hm, hw⟩` from `hS`. Establish `key : ∀ d : Fin N → ℚ, StrictAnti d → (∀ i, (d i, true) ∈ S) → Set.range d = {x | (x, true) ∈ S}`. Introduce `d hd hdm`. Establish `h1 : Finset.univ.image (fun i => (d i, true)) = S`.

Use `Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `hdm i`. Rewrite using `[Finset.card_image_of_injective _ (fun x y h => hd.injective (Prod.ext_iff.mp h).1), hcard]`. Simplify using the standard rewrite rules.

Use extensionality with `x`. Rewrite using `[← h1]`. Simplify using the standard rewrite rules. Establish `hm2 : ∀ i, (c i, true) ∈ S` using `fun i => by`. Take `⟨s, hs'⟩` from `hm i`.

Establish `: s = true` using `hs _ hs'`. Rewrite `hs'` using `[this]`. Then use the resulting hypothesis. Establish `e : c = c'` using `(hc.range_inj hc').1 ((key c hc hm2).trans (key c' hc' hm').symm)`. Rewrite using `[hw, e]`. Both sides reduce to the same expression.
-/
lemma isWtOfPar_eq {N n : ℕ} (h : N = n) {lam : DomWeight N} {S : SPar} (hS : Bridge.IsWtOfPar lam S)
    (hs : ∀ x ∈ S, x.2 = true) (c' : Fin n → ℚ) (hc' : StrictAnti c') (hm' : ∀ i, (c' i, true) ∈ S) (i : Fin N) :
    (lam.w i : ℚ) = c' (Fin.cast h i) - rhoVec n (Fin.cast h i) := by
  subst h
  obtain ⟨hcard, c, hc, hm, hw⟩ := hS
  have key : ∀ d : Fin N → ℚ, StrictAnti d → (∀ i, (d i, true) ∈ S) → Set.range d = {x | (x, true) ∈ S} := by
    intro d hd hdm
    have h1 : Finset.univ.image (fun i => (d i, true)) = S := by
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
        exact hdm i
      · rw [Finset.card_image_of_injective _ (fun x y h => hd.injective (Prod.ext_iff.mp h).1), hcard]
        simp
    ext x
    rw [← h1]
    simp
  have hm2 : ∀ i, (c i, true) ∈ S := fun i => by
    obtain ⟨s, hs'⟩ := hm i
    have : s = true := hs _ hs'
    rwa [this] at hs'
  have e : c = c' := (hc.range_inj hc').1 ((key c hc hm2).trans (key c' hc' hm').symm)
  rw [hw, e]
  rfl

/- English proof (translation)
Establish `hk` using `R.m_add_three_le_k`. Unfold `Ranks.N at hn`. Distinguish the cases in `h1 : n < R.k - 1`. Use `⟨.inl ⟨n, h1⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.L2.Col.RowPar.sgHC_lo _ h1, Formalism.L2.Col.RowPar.vb_lo _ h1]`.

Simplify using `[GlobalTheory.ForcedWeights.entry]`. Choose the witnesses or unpack the hypotheses as in `⟨B, ρ, hρ, rfl⟩ : ∃ B ρ, ρ < R.t + 1 ∧ n = R.k - 1 + B * (R.t + 1) + ρ := by`. Use `⟨(n - (R.k - 1)) / (R.t + 1), (n - (R.k - 1)) % (R.t + 1), Nat.mod_lt _ (by omega), ?_⟩` and prove the remaining obligations. Use `Nat.div_add_mod (n - (R.k - 1)) (R.t + 1)` as an intermediate fact. Rewrite `this` using `[Nat.mul_comm]`.

Use linear arithmetic over natural numbers and integers. Establish `hBm : B < R.m`. Apply `Nat.lt_of_mul_lt_mul_right (a := R.t + 1)` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Break down `ρ with _ | ρ` into its components or cases.

Use `⟨.inr (.inl ⟨B, hBm⟩), ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.add_zero, Formalism.L2.Col.RowPar.sgHC_b, Formalism.L2.Col.RowPar.bAt_of _ hBm]`. Simplify using `[GlobalTheory.ForcedWeights.entry]`. Use `⟨.inr (.inr (⟨B, hBm⟩, ⟨ρ, by omega⟩)), ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.L2.Col.RowPar.sgHC_e _ B (ρ + 1) (by omega) (by omega), Formalism.L2.Col.RowPar.eAt_of _ hBm]`.

Simplify using `only [GlobalTheory.ForcedWeights.entry]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sgHC_mem {R : Ranks} (P : HCParam R) (n : ℕ) (hn : n < R.N R.m - 1) :
    ∃ x, GlobalTheory.ForcedWeights.entry P x = (Formalism.L2.Col.RowPar.of P).sgHC n - Formalism.L2.Col.RowPar.sh R := by
  have hk := R.m_add_three_le_k
  unfold Ranks.N at hn
  by_cases h1 : n < R.k - 1
  · refine ⟨.inl ⟨n, h1⟩, ?_⟩
    rw [Formalism.L2.Col.RowPar.sgHC_lo _ h1, Formalism.L2.Col.RowPar.vb_lo _ h1]
    simp [GlobalTheory.ForcedWeights.entry]
  · obtain ⟨B, ρ, hρ, rfl⟩ : ∃ B ρ, ρ < R.t + 1 ∧ n = R.k - 1 + B * (R.t + 1) + ρ := by
      refine ⟨(n - (R.k - 1)) / (R.t + 1), (n - (R.k - 1)) % (R.t + 1), Nat.mod_lt _ (by omega), ?_⟩
      have := Nat.div_add_mod (n - (R.k - 1)) (R.t + 1)
      rw [Nat.mul_comm] at this
      omega
    have hBm : B < R.m := by
      apply Nat.lt_of_mul_lt_mul_right (a := R.t + 1)
      omega
    rcases ρ with _ | ρ
    · refine ⟨.inr (.inl ⟨B, hBm⟩), ?_⟩
      rw [Nat.add_zero, Formalism.L2.Col.RowPar.sgHC_b, Formalism.L2.Col.RowPar.bAt_of _ hBm]
      simp [GlobalTheory.ForcedWeights.entry]
    · refine ⟨.inr (.inr (⟨B, hBm⟩, ⟨ρ, by omega⟩)), ?_⟩
      rw [Formalism.L2.Col.RowPar.sgHC_e _ B (ρ + 1) (by omega) (by omega), Formalism.L2.Col.RowPar.eAt_of _ hBm]
      simp only [GlobalTheory.ForcedWeights.entry]
      push_cast
      ring

/- English proof (translation)
Introduce `i j hij`. Establish `h` using `Formalism.L2.Col.anti_sub_rho (N := R.N R.m - 1) (Formalism.L2.Col.RowPar.of P).sgHC (fun _ hn => Formalism.L2.Col.RowPar.sgHC_step P hn) hij.le`. Establish `h2 : (i.1 : ℚ) < (j.1 : ℚ)` using `by exact_mod_cast (show i.1 < j.1 from hij)`. Simplify using `only [rhoVec] at h ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sgHC_strictAnti {R : Ranks} (P : HCParam R) :
    StrictAnti fun i : Fin (R.N R.m - 1) => (Formalism.L2.Col.RowPar.of P).sgHC i.1 - Formalism.L2.Col.RowPar.sh R := by
  intro i j hij
  have h := Formalism.L2.Col.anti_sub_rho (N := R.N R.m - 1) (Formalism.L2.Col.RowPar.of P).sgHC
    (fun _ hn => Formalism.L2.Col.RowPar.sgHC_step P hn) hij.le
  have h2 : (i.1 : ℚ) < (j.1 : ℚ) := by exact_mod_cast (show i.1 < j.1 from hij)
  simp only [rhoVec] at h ⊢
  linarith

/- English proof (translation)
Establish `hF` using `GlobalTheory.ForcedWeights.lamRForced D τ`. Rewrite `hF` using `[GlobalTheory.ForcedWeights.dpar_eq]`. Establish `h1` using `isWtOfPar_eq h hF (fun x hx => by`. Take `⟨y, -, rfl⟩` from `Finset.mem_image.1 hx`. Use the proof step `rfl) _ (sgHC_strictAnti (D.hc τ)) (fun a => by`.

Take `⟨x, hx⟩` from `sgHC_mem (D.hc τ) a.1 a.2`. Conclude with `Finset.mem_image.2 ⟨x, Finset.mem_univ _, by rw [hx]⟩) i`. Rewrite `h1` using `[← Formalism.L2.Col.RowPar.sgTrue_eq]`. Conclude with `h1` after adjusting the coercions.
-/
theorem lamRdef_eq (D : D7) (h : D.sp.X'.rank = D.R.N D.R.m - 1) (τ : D.what₂.Tau) (i : Fin D.sp.X'.rank) :
    (Bridge.lamRdef (Ptw D) τ).w i = (Formalism.L2.Col.RowPar.of (D.hc τ)).sgTrue.w (Fin.cast h i) := by
  have hF := GlobalTheory.ForcedWeights.lamRForced D τ
  rw [GlobalTheory.ForcedWeights.dpar_eq] at hF
  have h1 := isWtOfPar_eq h hF (fun x hx => by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
      rfl) _ (sgHC_strictAnti (D.hc τ)) (fun a => by
      obtain ⟨x, hx⟩ := sgHC_mem (D.hc τ) a.1 a.2
      exact Finset.mem_image.2 ⟨x, Finset.mem_univ _, by rw [hx]⟩) i
  rw [← Formalism.L2.Col.RowPar.sgTrue_eq] at h1
  exact_mod_cast h1

/- English proof (translation)
Introduce `X τ i` and use `lamRdef_eq X.toD7 (RowAd.rank_X' X) τ i`.
-/
theorem lamRdef_eq_sgTrue : ∀ (X : Stages) (τ : X.B.fields.Tau) (i : Fin X.toD7.sp.X'.rank), (Bridge.lamRdef (Ptw X.toD7) τ).w i = (X.B.wts.sgTrue τ).w (Fin.cast (RowAd.rank_X' X) i) :=
  fun X τ i => lamRdef_eq X.toD7 (RowAd.rank_X' X) τ i

end GlobalTheory.Mem.R3.RowWeight
