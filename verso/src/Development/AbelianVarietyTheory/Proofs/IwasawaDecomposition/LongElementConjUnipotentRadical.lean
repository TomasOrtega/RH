import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ThetaRad

/- English proof (translation)
Rewrite using `[mem_unipRad]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hp, hd⟩ i j hij`. Take `⟨⟨c, i⟩, rfl⟩` from `e.surjective i`. Take `⟨⟨d, j⟩, rfl⟩` from `e.surjective j`.

Simplify using `only [blk_apply] at hij`. Break down `hij.lt_or_eq with hlt | rfl` into its components or cases. Rewrite using `[mem_parab_iff.1 hp c d i j hlt, Matrix.one_apply_ne]`. Introduce `hh`. Use `congrArg Sigma.fst (e.injective hh)` as an intermediate fact.

Conclude with `hlt.ne' this`. Rewrite using `[hd]`. Simplify using `only [Matrix.one_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]`. Introduce `h`. Use `⟨mem_parab.2 fun i j hij => ?_, fun c i j => ?_⟩` and prove the remaining obligations.

Rewrite using `[h i j hij.le, Matrix.one_apply_ne]`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hij`. Rewrite using `[h _ _ (by simp)]`. Simplify using `only [Matrix.one_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]`.
-/
theorem mem_unipRad_iff_entries {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, blk e j ≤ blk e i → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  constructor
  · rintro ⟨hp, hd⟩ i j hij
    obtain ⟨⟨c, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨d, j⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at hij
    rcases hij.lt_or_eq with hlt | rfl
    · rw [mem_parab_iff.1 hp c d i j hlt, Matrix.one_apply_ne]
      intro hh
      have := congrArg Sigma.fst (e.injective hh)
      exact hlt.ne' this
    · rw [hd]
      simp only [Matrix.one_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  · intro h
    refine ⟨mem_parab.2 fun i j hij => ?_, fun c i j => ?_⟩
    · rw [h i j hij.le, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hij
    · rw [h _ _ (by simp)]
      simp only [Matrix.one_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]

/- English proof (translation)
Take `⟨⟨c, i⟩, rfl⟩` from `(stdBlocks ![a, b] h).surjective p`. Rewrite using `[blk_apply, stdBlocks_val]`. Use `fin_cases c`. Simplify using `using i.2`. Simplify using the standard rewrite rules.
-/
theorem blk_stdBlocks_two {a b n : ℕ} (h : ∑ i, ![a, b] i = n) (p : Fin n) :
    blk (stdBlocks ![a, b] h) p = if (p : ℕ) < a then 0 else 1 := by
  obtain ⟨⟨c, i⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective p
  rw [blk_apply, stdBlocks_val]
  fin_cases c
  · simpa using i.2
  · simp

/- English proof (translation)
Simplify using `only [longElt, Units.val_mul, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[Finset.sum_eq_single j.rev (fun x _ hx => by rw [if_neg (fun hh => hx (by rw [hh, Fin.rev_rev])), mul_zero]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem longElt_conj_apply {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) (i j : Fin n) :
    ((longElt n R * g * longElt n R : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      (g : Matrix (Fin n) (Fin n) R) i.rev j.rev := by
  simp only [longElt, Units.val_mul, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single j.rev (fun x _ hx => by rw [if_neg (fun hh => hx (by rw [hh, Fin.rev_rev])), mul_zero]) (by simp)]
  simp

end GlobalTheory.ThetaRad

/- English proof (translation)
Introduce `R _ n a b h h' u hu`. Establish `hn : a + b = n` using `by simpa [Fin.sum_univ_two] using h`. Establish `hv` using `GlobalTheory.ThetaRad.mem_unipRad_iff_entries.1 (inv_mem hu)`. Use `GlobalTheory.ThetaRad.mem_unipRad_iff_entries.2 fun i j hij => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.ThetaRad.longElt_conj_apply]`.

Express the relevant statement in the definitionally equal form `((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ i.rev j.rev = _`. Rewrite using `[Matrix.transpose_apply]`. Rewrite using `[hv j.rev i.rev ?_]`. Simplify using `[Matrix.one_apply, Fin.rev_inj, eq_comm]`. Rewrite `*` using `[GlobalTheory.ThetaRad.blk_stdBlocks_two, GlobalTheory.ThetaRad.blk_stdBlocks_two]`.

Establish `hi` using `i.2`. Establish `hj` using `j.2`. Simplify using `only [Fin.val_rev] at *`. Apply the tactic sequence `split_ifs at hij ⊢ <;> first | exact le_refl _ | decide | (exfalso; omega) | (exfalso; revert hij; decide)`.
-/
theorem GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad : ∀ (R : Type) [CommRing R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n) (h' : ∑ i, ![b, a] i = n) (u : GL (Fin n) R), u ∈ unipRad R (stdBlocks ![a, b] h) → longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipRad R (stdBlocks ![b, a] h') := by
  intro R _ n a b h h' u hu
  have hn : a + b = n := by simpa [Fin.sum_univ_two] using h
  have hv := GlobalTheory.ThetaRad.mem_unipRad_iff_entries.1 (inv_mem hu)
  refine GlobalTheory.ThetaRad.mem_unipRad_iff_entries.2 fun i j hij => ?_
  rw [GlobalTheory.ThetaRad.longElt_conj_apply]
  change ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ i.rev j.rev = _
  rw [Matrix.transpose_apply]
  rw [hv j.rev i.rev ?_]
  · simp [Matrix.one_apply, Fin.rev_inj, eq_comm]
  · rw [GlobalTheory.ThetaRad.blk_stdBlocks_two, GlobalTheory.ThetaRad.blk_stdBlocks_two] at *
    have hi := i.2; have hj := j.2
    simp only [Fin.val_rev] at *
    split_ifs at hij ⊢ <;> first | exact le_refl _ | decide | (exfalso; omega) | (exfalso; revert hij; decide)
