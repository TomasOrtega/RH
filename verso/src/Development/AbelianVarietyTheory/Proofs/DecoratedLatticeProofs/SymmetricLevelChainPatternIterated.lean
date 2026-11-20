import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPatternStatement

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain.IterPattern

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Simplify using `using h (e.symm i) (e.symm j)`. Introduce `h i j`. Conclude with `h (e i) (e j)`.
-/
theorem intM_submatrix_iff {a b : Type*} (e : a ≃ b) (M : Matrix b b k) :
    IntM (M.submatrix e e) ↔ IntM M := by
  constructor
  · intro h i j
    simpa using h (e.symm i) (e.symm j)
  · intro h i j
    exact h (e i) (e j)

/- English proof (translation)
Rewrite using `[mem_KO, mem_KO, ← map_inv (reGL e).symm g, reGL_symm_val, reGL_symm_val, intM_submatrix_iff, intM_submatrix_iff]`.
-/
theorem symm_mem_KO_iff {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    (g : GL b k) : (reGL e).symm g ∈ KO k a ↔ g ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv (reGL e).symm g, reGL_symm_val, reGL_symm_val,
    intM_submatrix_iff, intM_submatrix_iff]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_reindex_J {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (P : TypeDatum k a)
    (e : a ≃ b) (g : GL b k) : g ∈ (P.reindex e).J ↔ (reGL e).symm g ∈ P.J := Iff.rfl

variable {ρ κ l j : ℕ} {t : Type}

/- English proof (translation)
Apply the tactic sequence `rcases x with a | ⟨i, s⟩ <;> rcases y with b | ⟨i', s'⟩ <;> simp [ixSucc, FreeIx]`.
-/
theorem free_ll (x y : Ix (Fin κ ⊕ Fin l) t j) :
    FreeIx ρ (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) ↔ FreeIx ρ x y := by
  rcases x with a | ⟨i, s⟩ <;> rcases y with b | ⟨i', s'⟩ <;> simp [ixSucc, FreeIx]

/- English proof (translation)
Apply the tactic sequence `rcases x with a | ⟨i, s'⟩ <;> simp [ixSucc, FreeIx, (Fin.castSucc_lt_last _).le]`.
-/
theorem free_lr (x : Ix (Fin κ ⊕ Fin l) t j) (s : t) :
    FreeIx ρ (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inr s)) := by
  rcases x with a | ⟨i, s'⟩ <;> simp [ixSucc, FreeIx, (Fin.castSucc_lt_last _).le]

/- English proof (translation)
Break down `y with b | ⟨i, s'⟩` into its components or cases. Simplify using `[ixSucc, FreeIx]`. Simplify using `[ixSucc, FreeIx]`.
-/
theorem not_free_rl (s : t) (y : Ix (Fin κ ⊕ Fin l) t j) :
    ¬ FreeIx ρ (ixSucc _ t j (.inr s)) (ixSucc _ t j (.inl y)) := by
  rcases y with b | ⟨i, s'⟩
  · simp [ixSucc, FreeIx]
  · simp [ixSucc, FreeIx]

/- English proof (translation)
Simplify using `[ixSucc, FreeIx]`.
-/
theorem free_rr (s s' : t) : FreeIx ρ (ixSucc (Fin κ ⊕ Fin l) t j (.inr s)) (ixSucc _ t j (.inr s')) := by
  simp [ixSucc, FreeIx]

variable [Fintype t] [DecidableEq t]

/- English proof (translation)
Establish `hz : ∀ a b : Fin κ ⊕ Fin l, FreeIx ρ (ixZero _ t a) (ixZero _ t b) ↔ FreeTop ρ a b` using `fun _ _ => Iff.rfl`. Rewrite using `[mem_reindex_J, hP, symm_mem_KO_iff]`. Simplify using `only [reGL_symm_val]`. Use `and_congr_right fun _ => ⟨fun h a b hab => ?_, fun h a b hab => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `(ixZero _ t).surjective a`.

Take `⟨b, rfl⟩` from `(ixZero _ t).surjective b`. Use `h a b (fun hf => hab ((hz a b).2 hf))` as an intermediate fact. Simplify `this` using `[Matrix.one_apply]`. Use `h _ _ (fun hf => hab ((hz a b).1 hf))` as an intermediate fact. Simplify `this` using `[Matrix.one_apply]`.
-/
theorem base_iff (P : TypeDatum k (Fin κ ⊕ Fin l))
    (hP : ∀ g : GL (Fin κ ⊕ Fin l) k, g ∈ P.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (g : GL (Ix (Fin κ ⊕ Fin l) t 0) k) :
    g ∈ (P.reindex (ixZero _ t)).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  have hz : ∀ a b : Fin κ ⊕ Fin l, FreeIx ρ (ixZero _ t a) (ixZero _ t b) ↔ FreeTop ρ a b := fun _ _ => Iff.rfl
  rw [mem_reindex_J, hP, symm_mem_KO_iff]
  simp only [reGL_symm_val]
  refine and_congr_right fun _ => ⟨fun h a b hab => ?_, fun h a b hab => ?_⟩
  · obtain ⟨a, rfl⟩ := (ixZero _ t).surjective a
    obtain ⟨b, rfl⟩ := (ixZero _ t).surjective b
    have := h a b (fun hf => hab ((hz a b).2 hf))
    simpa [Matrix.one_apply] using this
  · have := h _ _ (fun hf => hab ((hz a b).1 hf))
    simpa [Matrix.one_apply] using this

/- English proof (translation)
Rewrite using `[mem_reindex_J, TypeDatum.step_J, TypeDatum.mem_stepJ_iff, symm_mem_KO_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hK, ⟨g', hg', hval⟩, hC⟩`. Use `⟨hK, fun a b hab => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `(ixSucc _ t j).surjective a`.

Take `⟨b, rfl⟩` from `(ixSucc _ t j).surjective b`. Apply the tactic sequence `rcases a with x | s <;> rcases b with y | s'`. Establish `hxy : ¬ FreeIx ρ x y` using `fun h => hab ((free_ll x y).2 h)`. Establish `hold` using `((hQ g').1 hg').2 x y hxy`. Apply the tactic sequence `have hentry : g'.val x y = g.val (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) := by`.

Rewrite using `[hval, reGL_symm_val]`. Both sides reduce to the same expression. Rewrite `hold` using `[hentry]`. Simplify `hold` using `[Matrix.one_apply]`. Conclude with `absurd (free_lr x s') hab`.

Establish `hlow` using `hC s y`. Simplify `hlow` using `[Matrix.one_apply, reGL_symm_val, Matrix.toBlocks₂₁]`. Conclude with `absurd (free_rr s s') hab`. Introduce and unpack `⟨hK, hfree⟩`. Establish `hK' : (reGL (ixSucc _ t j)).symm g ∈ KO k _` using `(symm_mem_KO_iff _ g).2 hK`.

Establish `hC : MaxM ((reGL (ixSucc _ t j)).symm g).val.toBlocks₂₁`. Introduce `s y`. Establish `hnf` using `hfree _ _ (not_free_rl s y)`. Simplify `hnf` using `[Matrix.one_apply, reGL_symm_val, Matrix.toBlocks₂₁]`. Use `⟨hK, ?_, hC⟩` and prove the remaining obligations.

Take `⟨⟨g', hg'K, hg'val⟩, -⟩` from `exists_diag_blocks hK' hC`. Use `⟨g', (hQ g').2 ⟨hg'K, fun x y hxy => ?_⟩, hg'val⟩` and prove the remaining obligations. Establish `hnf` using `hfree _ _ (fun h => hxy ((free_ll x y).1 h))`. Apply the tactic sequence `have hentry : g'.val x y = g.val (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) := by`. Rewrite using `[hg'val, reGL_symm_val]`.

Both sides reduce to the same expression. Rewrite using `[hentry]`. Simplify `hnf` using `[Matrix.one_apply]`.
-/
theorem step_iff (Q : TypeDatum k (Ix (Fin κ ⊕ Fin l) t j)) (μ : kˣ →* ℂˣ) (hμ : IsTame μ)
    (hQ : ∀ g : GL (Ix (Fin κ ⊕ Fin l) t j) k, g ∈ Q.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (g : GL (Ix (Fin κ ⊕ Fin l) t (j + 1)) k) :
    g ∈ ((Q.step t μ hμ).reindex (ixSucc _ t j)).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  rw [mem_reindex_J, TypeDatum.step_J, TypeDatum.mem_stepJ_iff, symm_mem_KO_iff]
  constructor
  · rintro ⟨hK, ⟨g', hg', hval⟩, hC⟩
    refine ⟨hK, fun a b hab => ?_⟩
    obtain ⟨a, rfl⟩ := (ixSucc _ t j).surjective a
    obtain ⟨b, rfl⟩ := (ixSucc _ t j).surjective b
    rcases a with x | s <;> rcases b with y | s'
    ·
      have hxy : ¬ FreeIx ρ x y := fun h => hab ((free_ll x y).2 h)
      have hold := ((hQ g').1 hg').2 x y hxy
      have hentry : g'.val x y = g.val (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) := by
        rw [hval, reGL_symm_val]; rfl
      rw [hentry] at hold
      simpa [Matrix.one_apply] using hold
    · exact absurd (free_lr x s') hab
    ·
      have hlow := hC s y
      simpa [Matrix.one_apply, reGL_symm_val, Matrix.toBlocks₂₁] using hlow
    · exact absurd (free_rr s s') hab
  · rintro ⟨hK, hfree⟩
    have hK' : (reGL (ixSucc _ t j)).symm g ∈ KO k _ := (symm_mem_KO_iff _ g).2 hK
    have hC : MaxM ((reGL (ixSucc _ t j)).symm g).val.toBlocks₂₁ := by
      intro s y
      have hnf := hfree _ _ (not_free_rl s y)
      simpa [Matrix.one_apply, reGL_symm_val, Matrix.toBlocks₂₁] using hnf
    refine ⟨hK, ?_, hC⟩
    obtain ⟨⟨g', hg'K, hg'val⟩, -⟩ := exists_diag_blocks hK' hC
    refine ⟨g', (hQ g').2 ⟨hg'K, fun x y hxy => ?_⟩, hg'val⟩
    have hnf := hfree _ _ (fun h => hxy ((free_ll x y).1 h))
    have hentry : g'.val x y = g.val (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) := by
      rw [hg'val, reGL_symm_val]; rfl
    rw [hentry]
    simpa [Matrix.one_apply] using hnf

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Rewrite using `[TypeDatum.iter_zero]`. Conclude with `base_iff P hP g`. Consider the case `succ j ih`.

Rewrite using `[TypeDatum.iter_succ]`. Conclude with `step_iff _ (μ (j + 1)) (hμ _) ih g`.
-/
theorem iter_iff (P : TypeDatum k (Fin κ ⊕ Fin l)) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hP : ∀ g : GL (Fin κ ⊕ Fin l) k, g ∈ P.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (j : ℕ) (g : GL (Ix (Fin κ ⊕ Fin l) t j) k) :
    g ∈ (P.iter t μ hμ j).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  induction j with
  | zero =>
    rw [TypeDatum.iter_zero]
    exact base_iff P hP g
  | succ j ih =>
    rw [TypeDatum.iter_succ]
    exact step_iff _ (μ (j + 1)) (hμ _) ih g

end GlobalTheory.SymChain.IterPattern

/- English proof (translation)
Introduce `j g`. Conclude with `IterPattern.iter_iff S.P S.μ S.tame (GlobalTheory.T.mem_level_iff_symmetricPosition_entry_pattern k s κ S) j g`.
-/
theorem GlobalTheory.SymChain.pattern_iter (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] :
    S.Pattern t := by
  intro j g
  exact IterPattern.iter_iff S.P S.μ S.tame (GlobalTheory.T.mem_level_iff_symmetricPosition_entry_pattern k s κ S) j g
