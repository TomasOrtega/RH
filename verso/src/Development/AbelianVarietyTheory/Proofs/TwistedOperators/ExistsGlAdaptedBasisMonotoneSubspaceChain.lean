import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic

open scoped Matrix

namespace GlobalTheory.Flag

/- English proof (translation)
Take `⟨q, hq⟩` from `Submodule.exists_isCompl A`. Establish `hsup : q ⊓ B ⊔ A = B`. Rewrite using `[inf_comm, inf_sup_assoc_of_le _ hAB, sup_comm, hq.sup_eq_top, inf_top_eq]`. Use `⟨q ⊓ B, hsup, ?_⟩` and prove the remaining obligations. Establish `h1` using `Submodule.finrank_sup_add_finrank_inf_eq (q ⊓ B) A`.

Establish `h2 : q ⊓ B ⊓ A = ⊥`. Use `eq_bot_iff.2 (le_trans ?_ hq.inf_eq_bot.le)` and prove the remaining obligations. Rewrite using `[inf_comm A q]`. Conclude with `inf_le_inf_right _ inf_le_left`. Rewrite `h1` using `[hsup, h2, finrank_bot]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_sup_eq_finrank_sub {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {A B : Submodule K V} (hAB : A ≤ B) :
    ∃ C : Submodule K V, C ⊔ A = B ∧
      Module.finrank K C = Module.finrank K B - Module.finrank K A := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl A
  have hsup : q ⊓ B ⊔ A = B := by
    rw [inf_comm, inf_sup_assoc_of_le _ hAB, sup_comm, hq.sup_eq_top, inf_top_eq]
  refine ⟨q ⊓ B, hsup, ?_⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (q ⊓ B) A
  have h2 : q ⊓ B ⊓ A = ⊥ := by
    refine eq_bot_iff.2 (le_trans ?_ hq.inf_eq_bot.le)
    rw [inf_comm A q]; exact inf_le_inf_right _ inf_le_left
  rw [hsup, h2, finrank_bot] at h1
  omega

/- English proof (translation)
Introduce `K _ n m Y hmono h0 htop`. Set `r : Fin (m + 1) → ℕ` to `fun j => Module.finrank K (Y j)`. Establish `hC : ∀ j : Fin m, ∃ C : Submodule K (Fin n → K), C ⊔ Y j.castSucc = Y j.succ ∧ Module.finrank K C = r j.succ - r j.castSucc` using `fun j => exists_sup_eq_finrank_sub (hmono (Fin.castSucc_le_succ j))`. Use `choose C hCsup hCrk using hC`. Set `d : Fin m → ℕ` to `fun j => r j.succ - r j.castSucc`.

Set `R : ℕ → ℕ` to `fun k => r ⟨min k m, by omega⟩`. Establish `hRmono : Monotone R`. Introduce `a b hab`. Conclude with `Submodule.finrank_mono (hmono (Fin.mk_le_mk.2 (min_le_min_right m hab)))`. Establish `hsum : ∑ j, d j = n`.

Establish `e1 : ∑ j, d j = ∑ k ∈ Finset.range m, (R (k + 1) - R k)`. Rewrite using `[← Fin.sum_univ_eq_sum_range]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `a1 : (⟨min ((j : ℕ) + 1) m, by omega⟩ : Fin (m + 1)) = j.succ` using `Fin.ext (by simp)`. Establish `a2 : (⟨min (j : ℕ) m, by omega⟩ : Fin (m + 1)) = j.castSucc` using `Fin.ext (by simp)`.

Simplify using `only [d, R, a1, a2]`. Rewrite using `[e1, Finset.sum_range_tsub hRmono]`. Establish `a3 : (⟨min m m, by omega⟩ : Fin (m + 1)) = Fin.last m` using `Fin.ext (by simp)`. Establish `a4 : (⟨min 0 m, by omega⟩ : Fin (m + 1)) = 0` using `Fin.ext (by simp)`. Establish `hRm : R m = n` using `by show Module.finrank K (Y ⟨min m m, _⟩) = n`.

Rewrite using `[a3, htop, finrank_top, Module.finrank_fin_fun]`. Establish `hR0 : R 0 = 0` using `by show Module.finrank K (Y ⟨min 0 m, _⟩) = 0`. Rewrite using `[a4, h0, finrank_bot]`. Rewrite using `[hRm, hR0, Nat.sub_zero]`. Set `B : ∀ j : Fin m, Module.Basis (Fin (d j)) K (C j)` to `fun j => Module.finBasisOfFinrankEq K (C j) (hCrk j)`.

Set `f : (Σ j : Fin m, Fin (d j)) → (Fin n → K)` to `fun p => (B p.1 p.2 : Fin n → K)`. Establish `hspanC : ∀ j : Fin m, Submodule.span K (Set.range fun i => f ⟨j, i⟩) = C j`. Introduce `j`. Establish `: (Set.range fun i => f ⟨j, i⟩) = (C j).subtype '' Set.range (B j)` using `Set.range_comp (C j).subtype (B j)`. Rewrite using `[this, Submodule.span_image, (B j).span_eq, Submodule.map_subtype_top]`.

Establish `hspan : ∀ k (hk : k ≤ m), Y ⟨k, by omega⟩ = Submodule.span K (f '' {p | (p.1 : ℕ) < k})`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`. Simplify using `[h0]`.

Consider the case `succ k ih`. Introduce `hk`. Establish `hset : f '' {p | (p.1 : ℕ) < k + 1} = (Set.range fun i => f ⟨⟨k, hk⟩, i⟩) ∪ f '' {p | (p.1 : ℕ) < k}`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨a, i⟩, hp, rfl⟩`. Simplify using `only [Set.mem_setOf_eq] at hp`. Distinguish the cases in `ha : (a : ℕ) < k`. Conclude with `Or.inr ⟨⟨a, i⟩, ha, rfl⟩`. Take `rfl : a = ⟨k, hk⟩` from `Fin.ext (by simp; omega)`.

Conclude with `Or.inl ⟨i, rfl⟩`. Introduce and unpack `(⟨i, rfl⟩ | ⟨p, hp, rfl⟩)`. Conclude with `⟨⟨⟨k, hk⟩, i⟩, by simp, rfl⟩`. Conclude with `⟨p, by simp only [Set.mem_setOf_eq] at hp ⊢; omega, rfl⟩`. Establish `e1 : (⟨k + 1, by omega⟩ : Fin (m + 1)) = (⟨k, hk⟩ : Fin m).succ` using `rfl`.

Establish `e2 : (⟨k, by omega⟩ : Fin (m + 1)) = (⟨k, hk⟩ : Fin m).castSucc` using `rfl`. Rewrite using `[hset, Submodule.span_union, hspanC, ← ih (by omega), e1, e2, hCsup]`. Set `b : Fin n → (Fin n → K)` to `fun i => f ((GlobalTheory.SmGL.stdBlocks d hsum).symm i)`. Establish `hsub : ∀ j : Fin (m + 1), f '' {p | (p.1 : ℕ) < j} = b '' {i | ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d hsum) i : Fin m) : ℕ) < j}`. Introduce `j`.

Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, rfl⟩`. Conclude with `⟨(GlobalTheory.SmGL.stdBlocks d hsum) p, by simpa [GlobalTheory.SmGL.blk] using hp, by simp [b]⟩`. Introduce and unpack `⟨i, hi, rfl⟩`.

Conclude with `⟨(GlobalTheory.SmGL.stdBlocks d hsum).symm i, hi, rfl⟩`. Establish `htopb : ⊤ ≤ Submodule.span K (Set.range b)`. Establish `h1` using `hspan m le_rfl`. Establish `h2 : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m` using `rfl`. Establish `h3` using `hsub (Fin.last m)`.

Rewrite `h3` using `[Fin.val_last]`. Rewrite `h1` using `[h2, htop, h3]`. Rewrite using `[h1]`. Conclude with `Submodule.span_mono (Set.image_subset_range _ _)`. Establish `hli : LinearIndependent K b`.

Rewrite using `[linearIndependent_iff_card_eq_finrank_span, Set.finrank, top_unique htopb, finrank_top]`. Simplify using the standard rewrite rules. Set `Bas : Module.Basis (Fin n) K (Fin n → K)` to `Module.Basis.mk hli htopb`. Establish `hBas : ⇑Bas = b` using `Module.Basis.coe_mk hli htopb`. Set `pf` to `Pi.basisFun K (Fin n)`.

Set `g : GL (Fin n) K` to `⟨pf.toMatrix Bas, Bas.toMatrix pf, Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩`. Establish `hg : ∀ y : Fin n → K, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y = ⇑(Bas.repr y)`. Introduce `y`. Use `Module.Basis.toMatrix_mulVec_repr pf Bas y` as an intermediate fact. Establish `hy : ⇑(pf.repr y) = y` using `funext fun i => by simp [pf]`.

Rewrite `this` using `[hy]`. Conclude with `this`. Use `⟨d, hsum, g, fun j y => ?_⟩` and prove the remaining obligations. Establish `hYj : Y j = Submodule.span K (Bas '' {i | ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d hsum) i : Fin m) : ℕ) < j})`. Rewrite using `[hBas, ← hsub, ← hspan j (by omega)]`.

Rewrite using `[hYj, Module.Basis.mem_span_image, hg]`. Prove the components needed by the constructor for the conclusion. Introduce `hs i hi`. Assume the negation of the conclusion as `hne`. Use `hs (Finsupp.mem_support_iff.2 hne)` as an intermediate fact.

Simplify using `only [Set.mem_setOf_eq] at this`. Use linear arithmetic over natural numbers and integers. Introduce `H i hi`. Rewrite `hi` using `[Finset.mem_coe, Finsupp.mem_support_iff]`. Assume the negation of the conclusion as `hlt`.

Simplify using `only [Set.mem_setOf_eq, not_lt] at hlt`. Conclude with `hi (H i hlt)`.
-/
theorem exists_gl_adapted_chain : ∀ {K : Type} [Field K] {n m : ℕ} (Y : Fin (m + 1) → Submodule K (Fin n → K)), Monotone Y → Y 0 = ⊥ → Y (Fin.last m) = ⊤ →
    ∃ (d : Fin m → ℕ) (h : ∑ j, d j = n) (g : GL (Fin n) K), ∀ (j : Fin (m + 1)) (y : Fin n → K),
      y ∈ Y j ↔ ∀ i : Fin n, (j : ℕ) ≤ ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) i : Fin m) : ℕ) →
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) i = 0 := by
  intro K _ n m Y hmono h0 htop
  let r : Fin (m + 1) → ℕ := fun j => Module.finrank K (Y j)
  have hC : ∀ j : Fin m, ∃ C : Submodule K (Fin n → K), C ⊔ Y j.castSucc = Y j.succ ∧
      Module.finrank K C = r j.succ - r j.castSucc :=
    fun j => exists_sup_eq_finrank_sub (hmono (Fin.castSucc_le_succ j))
  choose C hCsup hCrk using hC
  let d : Fin m → ℕ := fun j => r j.succ - r j.castSucc
  let R : ℕ → ℕ := fun k => r ⟨min k m, by omega⟩
  have hRmono : Monotone R := by
    intro a b hab
    exact Submodule.finrank_mono (hmono (Fin.mk_le_mk.2 (min_le_min_right m hab)))
  have hsum : ∑ j, d j = n := by
    have e1 : ∑ j, d j = ∑ k ∈ Finset.range m, (R (k + 1) - R k) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      have a1 : (⟨min ((j : ℕ) + 1) m, by omega⟩ : Fin (m + 1)) = j.succ := Fin.ext (by simp)
      have a2 : (⟨min (j : ℕ) m, by omega⟩ : Fin (m + 1)) = j.castSucc := Fin.ext (by simp)
      simp only [d, R, a1, a2]
    rw [e1, Finset.sum_range_tsub hRmono]
    have a3 : (⟨min m m, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
    have a4 : (⟨min 0 m, by omega⟩ : Fin (m + 1)) = 0 := Fin.ext (by simp)
    have hRm : R m = n := by
      show Module.finrank K (Y ⟨min m m, _⟩) = n
      rw [a3, htop, finrank_top, Module.finrank_fin_fun]
    have hR0 : R 0 = 0 := by
      show Module.finrank K (Y ⟨min 0 m, _⟩) = 0
      rw [a4, h0, finrank_bot]
    rw [hRm, hR0, Nat.sub_zero]
  let B : ∀ j : Fin m, Module.Basis (Fin (d j)) K (C j) := fun j => Module.finBasisOfFinrankEq K (C j) (hCrk j)
  let f : (Σ j : Fin m, Fin (d j)) → (Fin n → K) := fun p => (B p.1 p.2 : Fin n → K)
  have hspanC : ∀ j : Fin m, Submodule.span K (Set.range fun i => f ⟨j, i⟩) = C j := by
    intro j
    have : (Set.range fun i => f ⟨j, i⟩) = (C j).subtype '' Set.range (B j) :=
      Set.range_comp (C j).subtype (B j)
    rw [this, Submodule.span_image, (B j).span_eq, Submodule.map_subtype_top]
  have hspan : ∀ k (hk : k ≤ m), Y ⟨k, by omega⟩ = Submodule.span K (f '' {p | (p.1 : ℕ) < k}) := by
    intro k
    induction k with
    | zero => intro _; simp [h0]
    | succ k ih =>
      intro hk
      have hset : f '' {p | (p.1 : ℕ) < k + 1} =
          (Set.range fun i => f ⟨⟨k, hk⟩, i⟩) ∪ f '' {p | (p.1 : ℕ) < k} := by
        ext v
        constructor
        · rintro ⟨⟨a, i⟩, hp, rfl⟩
          simp only [Set.mem_setOf_eq] at hp
          by_cases ha : (a : ℕ) < k
          · exact Or.inr ⟨⟨a, i⟩, ha, rfl⟩
          · obtain rfl : a = ⟨k, hk⟩ := Fin.ext (by simp; omega)
            exact Or.inl ⟨i, rfl⟩
        · rintro (⟨i, rfl⟩ | ⟨p, hp, rfl⟩)
          · exact ⟨⟨⟨k, hk⟩, i⟩, by simp, rfl⟩
          · exact ⟨p, by simp only [Set.mem_setOf_eq] at hp ⊢; omega, rfl⟩
      have e1 : (⟨k + 1, by omega⟩ : Fin (m + 1)) = (⟨k, hk⟩ : Fin m).succ := rfl
      have e2 : (⟨k, by omega⟩ : Fin (m + 1)) = (⟨k, hk⟩ : Fin m).castSucc := rfl
      rw [hset, Submodule.span_union, hspanC, ← ih (by omega), e1, e2, hCsup]
  let b : Fin n → (Fin n → K) := fun i => f ((GlobalTheory.SmGL.stdBlocks d hsum).symm i)
  have hsub : ∀ j : Fin (m + 1), f '' {p | (p.1 : ℕ) < j} = b '' {i | ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d hsum) i : Fin m) : ℕ) < j} := by
    intro j
    ext v
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(GlobalTheory.SmGL.stdBlocks d hsum) p, by simpa [GlobalTheory.SmGL.blk] using hp, by simp [b]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(GlobalTheory.SmGL.stdBlocks d hsum).symm i, hi, rfl⟩
  have htopb : ⊤ ≤ Submodule.span K (Set.range b) := by
    have h1 := hspan m le_rfl
    have h2 : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
    have h3 := hsub (Fin.last m)
    rw [Fin.val_last] at h3
    rw [h2, htop, h3] at h1
    rw [h1]
    exact Submodule.span_mono (Set.image_subset_range _ _)
  have hli : LinearIndependent K b := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, top_unique htopb, finrank_top]
    simp
  let Bas : Module.Basis (Fin n) K (Fin n → K) := Module.Basis.mk hli htopb
  have hBas : ⇑Bas = b := Module.Basis.coe_mk hli htopb
  let pf := Pi.basisFun K (Fin n)
  let g : GL (Fin n) K := ⟨pf.toMatrix Bas, Bas.toMatrix pf, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  have hg : ∀ y : Fin n → K, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y = ⇑(Bas.repr y) := by
    intro y
    have := Module.Basis.toMatrix_mulVec_repr pf Bas y
    have hy : ⇑(pf.repr y) = y := funext fun i => by simp [pf]
    rw [hy] at this
    exact this
  refine ⟨d, hsum, g, fun j y => ?_⟩
  have hYj : Y j = Submodule.span K (Bas '' {i | ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d hsum) i : Fin m) : ℕ) < j}) := by
    rw [hBas, ← hsub, ← hspan j (by omega)]
  rw [hYj, Module.Basis.mem_span_image, hg]
  constructor
  · intro hs i hi
    by_contra hne
    have := hs (Finsupp.mem_support_iff.2 hne)
    simp only [Set.mem_setOf_eq] at this
    omega
  · intro H i hi
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hi
    by_contra hlt
    simp only [Set.mem_setOf_eq, not_lt] at hlt
    exact hi (H i hlt)

end GlobalTheory.Flag
