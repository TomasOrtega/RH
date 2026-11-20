import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColsRowsRestPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEmbeddingMemUnitGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InhabitedStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocStageInhabited
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInnerProductSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatBoundPre

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace StagesInhab

def HasLetters (P : Pre) : Prop :=
  ∃ (Del : ℚ) (letter : P.Word → Fin (P.R.k - 2) → Bool), 0 < Del ∧ Function.Injective letter ∧
    (∀ w τ (l : ℕ) (h : l + 1 < P.R.k - 1), (P.hcW w τ).v ⟨l, by omega⟩ - (P.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) ∧
    ∀ w τ (l : ℕ) (h : l < P.R.k - 2), (P.hcW w τ).u ⟨l + 1, by omega⟩ =
      (P.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)

/- English proof (translation)
Rewrite using `[RowsModel.ipC_cols, RowsModel.ipC_cols, map_sum]`. Conclude with `Finset.sum_congr rfl fun c _ => by simp [mul_comm]`.
-/
theorem ipC_conj (B : Base) (u : B.Word)
    (φ ψ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) :
    ((ColsModel.cols B).fm u).ipC 0 ψ φ = starRingEnd ℂ (((ColsModel.cols B).fm u).ipC 0 φ ψ) := by
  rw [RowsModel.ipC_cols, RowsModel.ipC_cols, map_sum]
  exact Finset.sum_congr rfl fun c _ => by simp [mul_comm]

/- English proof (translation)
Rewrite using `[RowsModel.ipC_cols, Complex.re_sum]`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, φ c () ≠ 0 := by`. Assume the negation of the conclusion as `h`. Conclude with `hφ (funext fun c => funext fun _ => not_not.mp fun hc => h ⟨c, hc⟩)`. Use `Finset.sum_pos' (fun c _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]`. Check the signs of the components of the expression. Rewrite using `[Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]`. Check the signs of the components of the expression.
-/
theorem ipC_pos (B : Base) (u : B.Word)
    (φ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) (hφ : φ ≠ 0) :
    0 < (((ColsModel.cols B).fm u).ipC 0 φ φ).re := by
  rw [RowsModel.ipC_cols, Complex.re_sum]
  obtain ⟨c, hc⟩ : ∃ c, φ c () ≠ 0 := by
    by_contra h
    exact hφ (funext fun c => funext fun _ => not_not.mp fun hc => h ⟨c, hc⟩)
  refine Finset.sum_pos' (fun c _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩
  · rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity
  · rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity

/- English proof (translation)
Establish `hf : ∀ u, ∃ e : RowsModel.Euc ((ColsModel.cols B).mem u).A.du ≃ₗ[ℂ] ((ColsModel.cols B).mem u).A.Mram, ∀ φ ψ, inner ℂ φ ψ = ((ColsModel.cols B).fm u).ipC 0 (e φ).1 (e ψ).1` using `fun u => haveI := RowsModel.mram_fd (ColsModel.cols B) u RowsModel.exists_frame (RowsModel.ramCore (ColsModel.cols B) u (fun φ _ ψ _ => ipC_conj B u φ ψ) (fun φ _ h => ipC_pos B u φ h))`. Use `choose eM heM using hf`. Set `e : ℂ ≃ₗ[ℂ] RowsModel.Euc 1` to `(LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm.trans (WithLp.linearEquiv 2 ℂ _).symm`. Use `⟨RowsModel.model (ColsModel.cols B) (fun _ => 1) D (fun _ => e) (fun _ _ => e) eM heM, rfl, rfl, fun u => ?_⟩` and prove the remaining obligations. Establish `: Fact (B.T u).Prime` using `⟨B.T_prime u⟩`.

Establish `hne : ((ColsModel.cols B).mem u).A.Mram ≠ ⊥` using `MemberTorsor.mram_ne_bot B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) (ColsModel.two_lt_alt B.toPre u)`. Use `Submodule.nontrivial_iff_ne_bot.mpr hne` as an intermediate fact. Conclude with `(eM u).toEquiv.nontrivial`.
-/
theorem exists_rows (B : Base) (D : ℕ) :
    ∃ W : RowsRest B (ColsModel.cols B), W.Drows = D ∧ W.Dall = D ∧ ∀ u, Nontrivial (W.Mu u) := by
  classical
  have hf : ∀ u, ∃ e : RowsModel.Euc ((ColsModel.cols B).mem u).A.du ≃ₗ[ℂ] ((ColsModel.cols B).mem u).A.Mram,
      ∀ φ ψ, inner ℂ φ ψ = ((ColsModel.cols B).fm u).ipC 0 (e φ).1 (e ψ).1 := fun u =>
    haveI := RowsModel.mram_fd (ColsModel.cols B) u
    RowsModel.exists_frame (RowsModel.ramCore (ColsModel.cols B) u (fun φ _ ψ _ => ipC_conj B u φ ψ)
      (fun φ _ h => ipC_pos B u φ h))
  choose eM heM using hf
  let e : ℂ ≃ₗ[ℂ] RowsModel.Euc 1 :=
    (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm.trans (WithLp.linearEquiv 2 ℂ _).symm
  refine ⟨RowsModel.model (ColsModel.cols B) (fun _ => 1) D (fun _ => e) (fun _ _ => e) eM heM, rfl, rfl,
    fun u => ?_⟩
  have : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  have hne : ((ColsModel.cols B).mem u).A.Mram ≠ ⊥ :=
    MemberTorsor.mram_ne_bot B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) (ColsModel.two_lt_alt B.toPre u)
  have := Submodule.nontrivial_iff_ne_bot.mpr hne
  exact (eM u).toEquiv.nontrivial

/- English proof (translation)
Take `⟨Del, letter, hD, hinj, gap, hu⟩` from `hB`. Take `⟨W, h1, h2, h3⟩` from `exists_rows B D`. Establish `hc : ∀ u i, Nonempty (((ColsModel.cols B).mem u).C.cls i)` using `fun u _ => ⟨(1 : Tau B.R → (ZMod (B.T u))ˣ)⟩`. Take `⟨L⟩` from `locStage_inhabited`. Take `⟨N, -⟩` from `GaloisStage.exists_nStage_adapt B _ W L`.

Take `⟨V, -⟩` from `DivInhab.exists_divStage B _ (GaloisStage.adapt W)`. Take `⟨S⟩` from `SStageInhab.nonempty_sStage B _ (GaloisStage.adapt W) Del hD gap letter hinj hu (fun u x _ y _ => (ipC_conj B u y x).symm) (fun u x _ h => ipC_pos B u x h) (show W.Drows ≤ W.Dall by omega)`. Take `⟨G, -, hG⟩` from `(GJInhab.inhabited_stage B (ColsModel.cols B)).2.2 (hc _ _) (hc _ _)`. Conclude with `⟨⟨B, _, GaloisStage.adapt W, V, S, N, G⟩, rfl, h1, h2, h3, hc, hG⟩`.
-/
theorem exists_stages_over (B : Base) (hB : HasLetters B.toPre) (D : ℕ) :
    ∃ X : Stages, X.B = B ∧ X.W.Drows = D ∧ X.W.Dall = D ∧ (∀ u, Nontrivial (X.W.Mu u)) ∧
      (∀ u i, Nonempty ((X.C.mem u).C.cls i)) ∧ Nonempty X.G.jet.Sit := by
  obtain ⟨Del, letter, hD, hinj, gap, hu⟩ := hB
  obtain ⟨W, h1, h2, h3⟩ := exists_rows B D
  have hc : ∀ u i, Nonempty (((ColsModel.cols B).mem u).C.cls i) :=
    fun u _ => ⟨(1 : Tau B.R → (ZMod (B.T u))ˣ)⟩
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_adapt B _ W L
  obtain ⟨V, -⟩ := DivInhab.exists_divStage B _ (GaloisStage.adapt W)
  obtain ⟨S⟩ := SStageInhab.nonempty_sStage B _ (GaloisStage.adapt W) Del hD gap letter hinj hu
    (fun u x _ y _ => (ipC_conj B u y x).symm) (fun u x _ h => ipC_pos B u x h)
    (show W.Drows ≤ W.Dall by omega)
  obtain ⟨G, -, hG⟩ := (GJInhab.inhabited_stage B (ColsModel.cols B)).2.2 (hc _ _) (hc _ _)
  exact ⟨⟨B, _, GaloisStage.adapt W, V, S, N, G⟩, rfl, h1, h2, h3, hc, hG⟩

/- English proof (translation)
Take `⟨P, h1, h2, -, -, h3⟩` from `exists_pre_two_words`. Conclude with `⟨P, h3, h1, h2⟩`.
-/
theorem exists_pre_hasLetters : ∃ P : Pre, HasLetters P ∧ Nonempty (PreX P) ∧ 2 ≤ Fintype.card P.Word := by
  obtain ⟨P, h1, h2, -, -, h3⟩ := exists_pre_two_words
  exact ⟨P, h3, h1, h2⟩

/- English proof (translation)
Take `⟨B, rfl, a, b, c⟩` from `BaseExt.exists_base P S₀ S₁ S₂ h₀ h₁ h₂`. Take `⟨X, rfl, h⟩` from `exists_stages_over B hP D`. Conclude with `⟨X, rfl, a, b, c, h⟩`.
-/
theorem exists_stages_large (P : Pre) (hP : HasLetters P) (D : ℕ) (S₀ S₁ S₂ : Finset ℂ)
    (h₀ : ∀ z ∈ S₀, IsAlgebraic ℚ z) (h₁ : ∀ z ∈ S₁, IsAlgebraic ℚ z) (h₂ : ∀ z ∈ S₂, IsAlgebraic ℚ z) :
    ∃ X : Stages, X.B.toPre = P ∧ (∀ z ∈ S₀, ∃ x ∈ X.B.Ks, X.B.embLL x = z) ∧
      (∀ z ∈ S₁, ∃ x ∈ X.B.LL0, X.B.embLL x = z) ∧ (∀ z ∈ S₂, ∃ x : X.B.LL, X.B.embLL x = z) ∧
      X.W.Drows = D ∧ X.W.Dall = D ∧ (∀ u, Nontrivial (X.W.Mu u)) ∧
      (∀ u i, Nonempty ((X.C.mem u).C.cls i)) ∧ Nonempty X.G.jet.Sit := by
  obtain ⟨B, rfl, a, b, c⟩ := BaseExt.exists_base P S₀ S₁ S₂ h₀ h₁ h₂
  obtain ⟨X, rfl, h⟩ := exists_stages_over B hP D
  exact ⟨X, rfl, a, b, c, h⟩

end StagesInhab

/- English proof (translation)
Take `⟨P, hP, -⟩` from `StagesInhab.exists_pre_hasLetters`. Take `⟨X, -, -, -, -, h1, -, h2, h3, -⟩` from `StagesInhab.exists_stages_large P hP 1 ∅ ∅ ∅ (by simp) (by simp) (by simp)`. Conclude with `⟨X, by omega, h2, h3⟩`.
-/
theorem exists_stages : ∃ X : GlobalTheory.Mem.Stages, 0 < X.W.Drows ∧ (∀ u, Nontrivial (X.W.Mu u)) ∧
    ∀ u i, Nonempty ((X.C.mem u).C.cls i) := by
  obtain ⟨P, hP, -⟩ := StagesInhab.exists_pre_hasLetters
  obtain ⟨X, -, -, -, -, h1, -, h2, h3, -⟩ :=
    StagesInhab.exists_stages_large P hP 1 ∅ ∅ ∅ (by simp) (by simp) (by simp)
  exact ⟨X, by omega, h2, h3⟩

/- English proof (translation)
The claim follows from `exists_stages.elim fun X _ => ⟨X⟩`.
-/
theorem nonempty_stages : Nonempty Stages := exists_stages.elim fun X _ => ⟨X⟩

/- English proof (translation)
The claim follows from `nonempty_stages.map Stages.toD7`.
-/
theorem nonempty_record : Nonempty Formalism.BasicNotions.D7 := nonempty_stages.map Stages.toD7

end GlobalTheory.Mem

end
