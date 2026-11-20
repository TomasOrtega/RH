import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepSpan

variable {R S : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Simplify using `[word]`.
-/
lemma word_zero (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (g : Fin 0 → NC R S) : word act g = 1 := by
  simp [word]

/- English proof (translation)
Simplify using `[word, List.ofFn_succ]`.
-/
lemma word_succ (act : Mat R S →ₗ[ℂ] Module.End ℂ V) {k : ℕ} (g : Fin (k + 1) → NC R S) :
    word act g = act (eNC (g 0)) * word act (fun i : Fin k => g i.succ) := by
  simp [word, List.ofFn_succ]

def wordSpan (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {y | ∃ (k : ℕ) (g : Fin k → NC R S) (n : V), n ∈ N ∧ y = word act g n}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨k, g, n, hn, rfl⟩`.
-/
lemma word_mem_wordSpan (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k : ℕ} (g : Fin k → NC R S)
    {n : V} (hn : n ∈ N) : word act g n ∈ wordSpan act N :=
  Submodule.subset_span ⟨k, g, n, hn, rfl⟩

/- English proof (translation)
Simplify `word_mem_wordSpan act N (k := 0) Fin.elim0 hn` using `[word_zero]`.
-/
lemma le_wordSpan (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {n : V} (hn : n ∈ N) :
    n ∈ wordSpan act N := by
  simpa [word_zero] using word_mem_wordSpan act N (k := 0) Fin.elim0 hn

/- English proof (translation)
Establish `: wordSpan act N ≤ (wordSpan act N).comap (act (eNC x))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, g, n, hn, rfl⟩`. Establish `h` using `word_mem_wordSpan act N (k := k + 1) (Fin.cons x g) hn`. Rewrite `h` using `[word_succ]`.

Simplify using `using h`. Conclude with `this hy`.
-/
lemma nc_mem_wordSpan (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (x : NC R S) {y : V}
    (hy : y ∈ wordSpan act N) : act (eNC x) y ∈ wordSpan act N := by
  have : wordSpan act N ≤ (wordSpan act N).comap (act (eNC x)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, g, n, hn, rfl⟩
    have h := word_mem_wordSpan act N (k := k + 1) (Fin.cons x g) hn
    rw [word_succ] at h
    simpa using h
  exact this hy

/- English proof (translation)
Establish `hZ : Z = ∑ a, ∑ b, Z a b • Eab a b` using `by conv_lhs => rw [Matrix.matrix_eq_sum_single Z]`. Simplify using `[Eab, Matrix.smul_single]`. Rewrite using `[hZ]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]`. Use `Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Distinguish the cases in `h : sameBlock a b`. Conclude with `le_wordSpan act N (hN _ (GlobalTheory.TensorHW.isKC_Eab h) _ hn)`. Conclude with `nc_mem_wordSpan act N ⟨(a, b), h⟩ (le_wordSpan act N hn)`.
-/
lemma act_base (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (hN : KStable act N) (Z : Mat R S)
    {n : V} (hn : n ∈ N) : act Z n ∈ wordSpan act N := by
  have hZ : Z = ∑ a, ∑ b, Z a b • Eab a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    simp [Eab, Matrix.smul_single]
  rw [hZ]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_
  by_cases h : sameBlock a b
  · exact le_wordSpan act N (hN _ (GlobalTheory.TensorHW.isKC_Eab h) _ hn)
  · exact nc_mem_wordSpan act N ⟨(a, b), h⟩ (le_wordSpan act N hn)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `g Z`. Rewrite using `[word_zero]`. Conclude with `act_base act N hN Z hn`.

Consider the case `succ k ih`. Introduce `g Z`. Rewrite using `[word_succ, Module.End.mul_apply]`. Establish `h` using `ih (fun i => g i.succ) (Z * eNC (g 0) - eNC (g 0) * Z)`. Rewrite `h` using `[hL, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]`.

Simplify using `using add_mem h (nc_mem_wordSpan act N (g 0) (ih (fun i => g i.succ) Z))`.
-/
lemma act_word (act : Mat R S →ₗ[ℂ] Module.End ℂ V)
    (hL : ∀ Y Z : Mat R S, act (Y * Z - Z * Y) = act Y * act Z - act Z * act Y)
    (N : Submodule ℂ V) (hN : KStable act N) {n : V} (hn : n ∈ N) (k : ℕ) :
    ∀ (g : Fin k → NC R S) (Z : Mat R S), act Z (word act g n) ∈ wordSpan act N := by
  induction k with
  | zero =>
    intro g Z
    rw [word_zero]
    exact act_base act N hN Z hn
  | succ k ih =>
    intro g Z
    rw [word_succ, Module.End.mul_apply]
    have h := ih (fun i => g i.succ) (Z * eNC (g 0) - eNC (g 0) * Z)
    rw [hL, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply] at h
    simpa using add_mem h (nc_mem_wordSpan act N (g 0) (ih (fun i => g i.succ) Z))

/- English proof (translation)
The claim follows from `iSup_le fun j => le_iSup (fun j : Fin (l + 1) => LinearMap.range (phiN act N j)) ⟨j, by omega⟩`.
-/
lemma filt_mono (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k l : ℕ} (h : k ≤ l) :
    filt act N k ≤ filt act N l :=
  iSup_le fun j => le_iSup (fun j : Fin (l + 1) => LinearMap.range (phiN act N j)) ⟨j, by omega⟩

/- English proof (translation)
Use `le_iSup (fun j : Fin (k + 1) => LinearMap.range (phiN act N j)) (Fin.last k) ?_` and prove the remaining obligations. Use `⟨(Pi.single g ⟨n, hn⟩ : (Fin k → NC R S) → N), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `phiN act N k _ = _`. Rewrite using `[phiN_apply, Finset.sum_eq_single g]`. Simplify using the standard rewrite rules.

Introduce `h _ hne`. Simplify using `[Pi.single_eq_of_ne hne]`. Simplify using the standard rewrite rules.
-/
lemma word_mem_filt (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k : ℕ} (g : Fin k → NC R S)
    {n : V} (hn : n ∈ N) : word act g n ∈ filt act N k := by
  classical
  refine le_iSup (fun j : Fin (k + 1) => LinearMap.range (phiN act N j)) (Fin.last k) ?_
  refine ⟨(Pi.single g ⟨n, hn⟩ : (Fin k → NC R S) → N), ?_⟩
  change phiN act N k _ = _
  rw [phiN_apply, Finset.sum_eq_single g]
  · simp
  · intro h _ hne
    simp [Pi.single_eq_of_ne hne]
  · simp

/- English proof (translation)
Introduce `R S M Λ v _ hgen w`. Establish `hle : genSub M.act {v} ≤ wordSpan M.act (GlobalTheory.BlockReps.gen M.act v)`. Use `sInf_le ⟨Set.singleton_subset_iff.2 (le_wordSpan _ _ (GlobalTheory.BlockReps.mem_gen v)), fun Z => ?_⟩` and prove the remaining obligations. Establish `: wordSpan M.act (GlobalTheory.BlockReps.gen M.act v) ≤ (wordSpan M.act (GlobalTheory.BlockReps.gen M.act v)).comap (M.act Z)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, g, n, hn, rfl⟩`. Conclude with `act_word M.act M.lie _ (GlobalTheory.BlockReps.stable_gen v) hn k g Z`. Conclude with `fun y hy => this hy`. Establish `hw : w ∈ wordSpan M.act (GlobalTheory.BlockReps.gen M.act v)` using `hle (hgen ▸ Submodule.mem_top)`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨k, g, n, hn, rfl⟩` from `hy`. Conclude with `⟨k, word_mem_filt _ _ g hn⟩`. Consider the case `zero => exact ⟨0, zero_mem _⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨k, hk⟩` from `hx`. Take `⟨l, hl⟩` from `hy`. Conclude with `⟨max k l, add_mem (filt_mono _ _ (le_max_left _ _) hk) (filt_mono _ _ (le_max_right _ _) hl)⟩`. Consider the case `smul c x _ hx`. Take `⟨k, hk⟩` from `hx`.

Conclude with `⟨k, Submodule.smul_mem _ _ hk⟩`.
-/
theorem filt_exhaustive : ∀ (R S : ℕ) (M : GKMod R S) (Λ : Ix R S → ℚ) (v : M.V), IsHW M.act Λ v →
    genSub M.act {v} = ⊤ → ∀ w, ∃ k, w ∈ filt M.act (GlobalTheory.BlockReps.gen M.act v) k := by
  intro R S M Λ v _ hgen w
  have hle : genSub M.act {v} ≤ wordSpan M.act (GlobalTheory.BlockReps.gen M.act v) := by
    refine sInf_le ⟨Set.singleton_subset_iff.2 (le_wordSpan _ _ (GlobalTheory.BlockReps.mem_gen v)), fun Z => ?_⟩
    have : wordSpan M.act (GlobalTheory.BlockReps.gen M.act v) ≤
        (wordSpan M.act (GlobalTheory.BlockReps.gen M.act v)).comap (M.act Z) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, g, n, hn, rfl⟩
      exact act_word M.act M.lie _ (GlobalTheory.BlockReps.stable_gen v) hn k g Z
    exact fun y hy => this hy
  have hw : w ∈ wordSpan M.act (GlobalTheory.BlockReps.gen M.act v) := hle (hgen ▸ Submodule.mem_top)
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, g, n, hn, rfl⟩ := hy
    exact ⟨k, word_mem_filt _ _ g hn⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    exact ⟨max k l, add_mem (filt_mono _ _ (le_max_left _ _) hk) (filt_mono _ _ (le_max_right _ _) hl)⟩
  | smul c x _ hx =>
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, Submodule.smul_mem _ _ hk⟩

end GlobalTheory.SteepSpan

end
