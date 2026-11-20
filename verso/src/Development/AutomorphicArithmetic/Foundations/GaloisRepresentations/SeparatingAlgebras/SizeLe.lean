import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound

private def sz {a : ℕ} (lam : DomWeight a) : ℕ := ∑ k, (lam.w k).natAbs

/- English proof (translation)
Unfold `sz DomWeight.dual`. Simplify using `only [Int.natAbs_neg]`. Conclude with `Fintype.sum_equiv Fin.revPerm _ _ (fun k => by simp)`.
-/
private theorem sz_dual {a : ℕ} (lam : DomWeight a) : sz lam.dual = sz lam := by
  unfold sz DomWeight.dual
  simp only [Int.natAbs_neg]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun k => by simp)

/- English proof (translation)
Establish `key : ∀ i : Fin a, lam.natW i + lam.detShift.natAbs ≤ 2 * sz lam`. Introduce `i`. Establish `ha : 0 < a` using `i.pos`. Establish `hd : lam.detShift = lam.w ⟨a - 1, by omega⟩`. Simplify using `only [DomWeight.detShift, dif_pos ha]`.

Establish `hnat : lam.natW i = (lam.w i - lam.w ⟨a - 1, by omega⟩).toNat`. Simplify using `only [DomWeight.natW, hd]`. Establish `hLle : (lam.w ⟨a - 1, by omega⟩).natAbs ≤ sz lam`. Unfold `sz`. Conclude with `Finset.single_le_sum (f := fun k => (lam.w k).natAbs) (fun k _ => Nat.zero_le _) (Finset.mem_univ _)`.

Rewrite using `[hnat, hd]`. Distinguish the cases in `hi : i = ⟨a - 1, by omega⟩`. Establish `h0 : (lam.w i - lam.w ⟨a - 1, by omega⟩).toNat = 0`. Rewrite using `[hi, sub_self]`. Both sides reduce to the same expression.

Use linear arithmetic over natural numbers and integers. Establish `hpair : (lam.w i).natAbs + (lam.w ⟨a - 1, by omega⟩).natAbs ≤ sz lam`. Unfold `sz`. Establish `h` using `Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => (lam.w k).natAbs) (Finset.subset_univ {i, ⟨a - 1, by omega⟩}) (fun _ _ _ => Nat.zero_le _)`. Rewrite `h` using `[Finset.sum_pair hi]`. Then use the resulting hypothesis.

Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Simplify using `[Finset.sum_add_distrib]`. Use `_ ≤ ∑ _i : Fin a, 2 * sz lam := Finset.sum_le_sum fun i _ => key i`. Use `_ = a * (2 * sz lam) := by simp`.
-/
private theorem one_le {a : ℕ} (lam : DomWeight a) :
    ∑ i, lam.natW i + a * lam.detShift.natAbs ≤ a * (2 * sz lam) := by
  have key : ∀ i : Fin a, lam.natW i + lam.detShift.natAbs ≤ 2 * sz lam := by
    intro i
    have ha : 0 < a := i.pos
    have hd : lam.detShift = lam.w ⟨a - 1, by omega⟩ := by
      simp only [DomWeight.detShift, dif_pos ha]
    have hnat : lam.natW i = (lam.w i - lam.w ⟨a - 1, by omega⟩).toNat := by
      simp only [DomWeight.natW, hd]
    have hLle : (lam.w ⟨a - 1, by omega⟩).natAbs ≤ sz lam := by
      unfold sz
      exact Finset.single_le_sum (f := fun k => (lam.w k).natAbs) (fun k _ => Nat.zero_le _)
        (Finset.mem_univ _)
    rw [hnat, hd]
    by_cases hi : i = ⟨a - 1, by omega⟩
    · have h0 : (lam.w i - lam.w ⟨a - 1, by omega⟩).toNat = 0 := by
        rw [hi, sub_self]; rfl
      omega
    · have hpair : (lam.w i).natAbs + (lam.w ⟨a - 1, by omega⟩).natAbs ≤ sz lam := by
        unfold sz
        have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => (lam.w k).natAbs)
          (Finset.subset_univ {i, ⟨a - 1, by omega⟩}) (fun _ _ _ => Nat.zero_le _)
        rwa [Finset.sum_pair hi] at h
      omega
  calc ∑ i, lam.natW i + a * lam.detShift.natAbs
      = ∑ i, (lam.natW i + lam.detShift.natAbs) := by
        simp [Finset.sum_add_distrib]
    _ ≤ ∑ _i : Fin a, 2 * sz lam := Finset.sum_le_sum fun i _ => key i
    _ = a * (2 * sz lam) := by simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

private noncomputable def emb : InfinitePlace E ⊕ InfinitePlace E → (E →+* ℂ)
  | .inl v => v.embedding
  | .inr v => ComplexEmbedding.conjugate v.embedding

/- English proof (translation)
The claim follows from `InfinitePlace.mk_embedding v`.
-/
private theorem mk_emb_inl (v : InfinitePlace E) : InfinitePlace.mk (emb (.inl v)) = v :=
  InfinitePlace.mk_embedding v

/- English proof (translation)
Simplify using `[emb]`.
-/
private theorem mk_emb_inr (v : InfinitePlace E) : InfinitePlace.mk (emb (.inr v)) = v := by
  simp [emb]

/- English proof (translation)
Introduce `x y h`. Establish `hm : InfinitePlace.mk (emb x) = InfinitePlace.mk (emb y)` using `by rw [h]`. Apply the tactic sequence `rcases x with v | v <;> rcases y with w | w <;>`. Apply the tactic sequence `simp only [mk_emb_inl, mk_emb_inr] at hm <;> subst hm`. Both sides reduce to the same expression.

Simplify using `only [emb] at h`. Conclude with `absurd h.symm (conjugate_ne _)`. Simplify using `only [emb] at h`. Conclude with `absurd h (conjugate_ne _)`. Both sides reduce to the same expression.
-/
private theorem emb_injective : Function.Injective (emb (E := E)) := by
  intro x y h
  have hm : InfinitePlace.mk (emb x) = InfinitePlace.mk (emb y) := by rw [h]
  rcases x with v | v <;> rcases y with w | w <;>
    simp only [mk_emb_inl, mk_emb_inr] at hm <;> subst hm
  · rfl
  · simp only [emb] at h
    exact absurd h.symm (conjugate_ne _)
  · simp only [emb] at h
    exact absurd h (conjugate_ne _)
  · rfl

/- English proof (translation)
Establish `h1 : ∑ v, 2 * sz (W v) = ∑ s : InfinitePlace E ⊕ InfinitePlace E, sz (W.at (emb s))`. Rewrite using `[Fintype.sum_sum_type]`. Simplify using `only [emb, Wt.at_embedding, Wt.at_conjugate, sz_dual, two_mul, Finset.sum_add_distrib]`. Establish `h2 : ∑ s : InfinitePlace E ⊕ InfinitePlace E, sz (W.at (emb s)) = ∑ τ ∈ Finset.univ.map ⟨emb, emb_injective⟩, sz (W.at τ)`. Rewrite using `[Finset.sum_map]`.

Both sides reduce to the same expression. Establish `h3 : GlobalTheory.CongW.wtSize W.at = ∑ τ, sz (W.at τ)` using `rfl`. Rewrite using `[h1, h2, h3]`. Conclude with `Finset.sum_le_sum_of_subset (Finset.subset_univ _)`.
-/
private theorem two_le (W : Wt E a) : ∑ v, 2 * sz (W v) ≤ GlobalTheory.CongW.wtSize W.at := by
  have h1 : ∑ v, 2 * sz (W v)
      = ∑ s : InfinitePlace E ⊕ InfinitePlace E, sz (W.at (emb s)) := by
    rw [Fintype.sum_sum_type]
    simp only [emb, Wt.at_embedding, Wt.at_conjugate, sz_dual, two_mul, Finset.sum_add_distrib]
  have h2 : ∑ s : InfinitePlace E ⊕ InfinitePlace E, sz (W.at (emb s))
      = ∑ τ ∈ Finset.univ.map ⟨emb, emb_injective⟩, sz (W.at τ) := by
    rw [Finset.sum_map]; rfl
  have h3 : GlobalTheory.CongW.wtSize W.at = ∑ τ, sz (W.at τ) := rfl
  rw [h1, h2, h3]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound

open UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound in
/- English proof (translation)
Introduce `E _ _ _ a W`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.Gal.Gen.sizeLe_pf :
    UpperTheory.Gal.Gen.SizeLe := by
  intro E _ _ _ a W
  calc (∑ v, ∑ i, (W v).natW i) + ∑ v, a * (W v).detShift.natAbs
      = ∑ v, (∑ i, (W v).natW i + a * (W v).detShift.natAbs) := Finset.sum_add_distrib.symm
    _ ≤ ∑ v, a * (2 * sz (W v)) := Finset.sum_le_sum fun v _ => one_le (W v)
    _ = a * ∑ v, 2 * sz (W v) := by rw [Finset.mul_sum]
    _ ≤ a * GlobalTheory.CongW.wtSize W.at := Nat.mul_le_mul_left a (two_le W)
