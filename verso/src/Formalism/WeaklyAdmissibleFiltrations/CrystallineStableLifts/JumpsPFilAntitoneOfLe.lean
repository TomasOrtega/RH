import Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

namespace FilPhi

variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]

/- English proof (translation)
Proceed by induction on `a, hba using Int.le_induction with`. Consider the case `base => exact le_rfl`. Consider the case `succ k _ ih => exact (F.Fil_anti τ k).trans ih`.
-/
theorem fil_le_fil_of_le (F : FilPhi LL D n Emb) (τ : Emb) {b a : ℤ} (hba : b ≤ a) :
    F.Fil τ a ≤ F.Fil τ b := by
  induction a, hba using Int.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact (F.Fil_anti τ k).trans ih

end FilPhi

open FilPhi

/- English proof (translation)
Introduce `LL _ D _ _ n Emb _ F τ l h`. Prove the components needed by the constructor for the conclusion. Introduce `hJ`. Establish `hno : ∀ a, a ∉ Set.Icc l h → F.Fil τ (a + 1) = F.Fil τ a`. Introduce `a ha`.

Assume the negation of the conclusion as `hne`. Conclude with `ha (hJ a hne)`. Prove the components needed by the constructor for the conclusion. Establish `key : ∀ k : ℕ, F.Fil τ (l - k) = F.Fil τ l`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `hk : (l - ((k + 1 : ℕ) : ℤ)) ∉ Set.Icc l h`. Introduce `hm`.

Use `hm.1` as an intermediate fact. Move the coercions through the operations in `at this`. Use linear arithmetic over natural numbers and integers. Establish `e` using `hno _ hk`. Establish `: l - ((k + 1 : ℕ) : ℤ) + 1 = l - (k : ℤ)` using `by push_cast; ring`.

Rewrite `e` using `[this]`. Rewrite using `[← e, ih]`. Establish `hlo` using `F.Fil_lo τ (l - ((l - min F.lo l).toNat : ℕ)) (by omega)`. Rewrite `hlo` using `[key]`. Conclude with `hlo`.

Establish `key : ∀ k : ℕ, F.Fil τ (h + 1 + k) = F.Fil τ (h + 1)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Establish `hk : (h + 1 + (k : ℤ)) ∉ Set.Icc l h`. Introduce `hm`. Use `hm.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `e` using `hno _ hk`.

Establish `: h + 1 + ((k + 1 : ℕ) : ℤ) = h + 1 + (k : ℤ) + 1` using `by push_cast; ring`. Rewrite using `[this, e, ih]`. Establish `hhi` using `F.Fil_hi τ (h + 1 + ((F.hi - (h + 1)).toNat : ℕ)) (by omega)`. Rewrite `hhi` using `[key]`. Conclude with `hhi`.

Introduce and unpack `⟨hl, hh⟩ a ha`. Assume the negation of the conclusion as `hm`. Apply `ha` to reduce the goal to its premises. Break down `(not_and_or.mp hm) with hal | hah` into its components or cases. Establish `hal : a + 1 ≤ l` using `by omega`.

Apply `le_antisymm (F.Fil_anti τ a)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hah : h + 1 ≤ a` using `by omega`. Establish `h1 : F.Fil τ a = ⊥` using `le_bot_iff.mp (hh ▸ F.fil_le_fil_of_le τ hah)`. Establish `h2 : F.Fil τ (a + 1) = ⊥` using `le_bot_iff.mp (hh ▸ F.fil_le_fil_of_le τ (by omega : h + 1 ≤ a + 1))`.

Rewrite using `[h1, h2]`.
-/
theorem jumpsIcc : JumpsIcc := by
  intro LL _ D _ _ n Emb _ F τ l h
  constructor
  · intro hJ
    have hno : ∀ a, a ∉ Set.Icc l h → F.Fil τ (a + 1) = F.Fil τ a := by
      intro a ha
      by_contra hne
      exact ha (hJ a hne)
    constructor
    ·
      have key : ∀ k : ℕ, F.Fil τ (l - k) = F.Fil τ l := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hk : (l - ((k + 1 : ℕ) : ℤ)) ∉ Set.Icc l h := by
            intro hm; have := hm.1; push_cast at this; omega
          have e := hno _ hk
          have : l - ((k + 1 : ℕ) : ℤ) + 1 = l - (k : ℤ) := by push_cast; ring
          rw [this] at e
          rw [← e, ih]
      have hlo := F.Fil_lo τ (l - ((l - min F.lo l).toNat : ℕ)) (by omega)
      rw [key] at hlo
      exact hlo
    ·
      have key : ∀ k : ℕ, F.Fil τ (h + 1 + k) = F.Fil τ (h + 1) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hk : (h + 1 + (k : ℤ)) ∉ Set.Icc l h := by
            intro hm; have := hm.2; omega
          have e := hno _ hk
          have : h + 1 + ((k + 1 : ℕ) : ℤ) = h + 1 + (k : ℤ) + 1 := by push_cast; ring
          rw [this, e, ih]
      have hhi := F.Fil_hi τ (h + 1 + ((F.hi - (h + 1)).toNat : ℕ)) (by omega)
      rw [key] at hhi
      exact hhi
  · rintro ⟨hl, hh⟩ a ha
    by_contra hm
    apply ha
    rcases (not_and_or.mp hm) with hal | hah
    · have hal : a + 1 ≤ l := by omega
      apply le_antisymm (F.Fil_anti τ a)
      calc F.Fil τ a ≤ F.Dl (F.letter τ) := F.Fil_le τ a
        _ = F.Fil τ l := hl.symm
        _ ≤ F.Fil τ (a + 1) := F.fil_le_fil_of_le τ hal
    · have hah : h + 1 ≤ a := by omega
      have h1 : F.Fil τ a = ⊥ := le_bot_iff.mp (hh ▸ F.fil_le_fil_of_le τ hah)
      have h2 : F.Fil τ (a + 1) = ⊥ :=
        le_bot_iff.mp (hh ▸ F.fil_le_fil_of_le τ (by omega : h + 1 ≤ a + 1))
      rw [h1, h2]

/- English proof (translation)
Introduce `LL _ D _ _ n Emb _ F`. Prove the components needed by the constructor for the conclusion. Use `⟨fun x _ => Submodule.mem_top, ?_⟩` and prove the remaining obligations. Simplify using `only [top_inf_eq]`. Conclude with `F.internal.submodule_iSup_eq_top.symm`.

Use `⟨fun x hx => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hx`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hx, map_zero]`. Simplify using the standard rewrite rules.
-/
theorem subTopBot : SubTopBot := by
  intro LL _ D _ _ n Emb _ F
  constructor
  · refine ⟨fun x _ => Submodule.mem_top, ?_⟩
    simp only [top_inf_eq]
    exact F.internal.submodule_iSup_eq_top.symm
  · refine ⟨fun x hx => ?_, ?_⟩
    · rw [Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]
    · simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨jumpsIcc, subTopBot⟩`.
-/
theorem jumpsIcc_and_subTopBot : JumpsIcc ∧ SubTopBot := ⟨jumpsIcc, subTopBot⟩

end Formalism.WeaklyAdmissibleFiltrations
