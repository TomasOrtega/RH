import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnveloping

noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.CasFamily

/- English proof (translation)
Establish `h1 : ∀ i j, (X i j + X j i) * (X i j + X j i) - (X i j - X j i) * (X i j - X j i) + ((Y i j - Y j i) * (Y i j - Y j i) - (Y i j + Y j i) * (Y i j + Y j i)) = (2 : ℂ) • (X i j * X j i) + (2 : ℂ) • (X j i * X i j) - ((2 : ℂ) • (Y i j * Y j i) + (2 : ℂ) • (Y j i * Y i j))`. Introduce `i j`. Simplify using `only [add_mul, mul_add, sub_mul, mul_sub]`. Apply the tactic sequence `match_scalars <;> ring`. Establish `h2 : ∀ i j, ((1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) * ((1 / 2 : ℂ) • (X j i - Complex.I • Y j i)) + ((1 / 2 : ℂ) • (X i j + Complex.I • Y i j)) * ((1 / 2 : ℂ) • (X j i + Complex.I • Y j i)) = (1 / 2 : ℂ) • (X i j * X j i) - (1 / 2 : ℂ) • (Y i j * Y j i)`.

Introduce `i j`. Simplify using `only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub, smul_add, smul_sub, smul_smul]`. Apply the tactic sequence `match_scalars <;> ring_nf <;> simp <;> norm_num`. Establish `hX : ∑ i, ∑ j, X j i * X i j = ∑ i, ∑ j, X i j * X j i` using `Finset.sum_comm`. Establish `hY : ∑ i, ∑ j, Y j i * Y i j = ∑ i, ∑ j, Y i j * Y j i` using `Finset.sum_comm`.

Establish `hc : Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) + Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j + Complex.I • Y i j)) = ∑ i, ∑ j, ((1 / 2 : ℂ) • (X i j * X j i) - (1 / 2 : ℂ) • (Y i j * Y j i))`. Simplify using `only [Formalism.REAL.Cas, ← Finset.sum_add_distrib, h2]`. Rewrite using `[hc]`. Simplify using `only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, hX, hY]`. Apply the tactic sequence `match_scalars <;> norm_num`.
-/
theorem sum_squares_eq {A : Type} [Ring A] [Algebra ℂ A] {a : ℕ} (X Y : Fin a → Fin a → A) :
    ∑ i, ∑ j, ((X i j + X j i) * (X i j + X j i) - (X i j - X j i) * (X i j - X j i) +
        ((Y i j - Y j i) * (Y i j - Y j i) - (Y i j + Y j i) * (Y i j + Y j i))) =
      (8 : ℂ) • (Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) +
        Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j + Complex.I • Y i j))) := by
  have h1 : ∀ i j, (X i j + X j i) * (X i j + X j i) - (X i j - X j i) * (X i j - X j i) +
      ((Y i j - Y j i) * (Y i j - Y j i) - (Y i j + Y j i) * (Y i j + Y j i)) =
      (2 : ℂ) • (X i j * X j i) + (2 : ℂ) • (X j i * X i j) -
        ((2 : ℂ) • (Y i j * Y j i) + (2 : ℂ) • (Y j i * Y i j)) := by
    intro i j
    simp only [add_mul, mul_add, sub_mul, mul_sub]
    match_scalars <;> ring
  have h2 : ∀ i j, ((1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) * ((1 / 2 : ℂ) • (X j i - Complex.I • Y j i)) +
      ((1 / 2 : ℂ) • (X i j + Complex.I • Y i j)) * ((1 / 2 : ℂ) • (X j i + Complex.I • Y j i)) =
      (1 / 2 : ℂ) • (X i j * X j i) - (1 / 2 : ℂ) • (Y i j * Y j i) := by
    intro i j
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub, smul_add, smul_sub, smul_smul]
    match_scalars <;> ring_nf <;> simp <;> norm_num
  have hX : ∑ i, ∑ j, X j i * X i j = ∑ i, ∑ j, X i j * X j i := Finset.sum_comm
  have hY : ∑ i, ∑ j, Y j i * Y i j = ∑ i, ∑ j, Y i j * Y j i := Finset.sum_comm
  have hc : Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) +
      Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j + Complex.I • Y i j)) =
      ∑ i, ∑ j, ((1 / 2 : ℂ) • (X i j * X j i) - (1 / 2 : ℂ) • (Y i j * Y j i)) := by
    simp only [Formalism.REAL.Cas, ← Finset.sum_add_distrib, h2]
  rw [hc]
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, hX, hY]
  match_scalars <;> norm_num

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def sgl (i j : Fin a) : Cinf E →ₗ[ℝ] Lie E a :=
  (Matrix.singleLinearMap ℝ i j : Cinf E →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))

def eW (w : InfinitePlace E) : Cinf E := atEmb w.embedding 1

def fW (w : InfinitePlace E) : Cinf E := atEmb w.embedding Complex.I

omit [NumberField E] [IsTotallyComplex E] in
open Classical in
/- English proof (translation)
Unfold `atEmb`. Rewrite using `[InfinitePlace.mk_embedding, if_pos rfl, Pi.single_apply]`.
-/
theorem atEmb_embedding_apply (w v : InfinitePlace E) (z : ℂ) :
    atEmb w.embedding z v = if v = w then z else 0 := by
  unfold atEmb
  rw [InfinitePlace.mk_embedding, if_pos rfl, Pi.single_apply]

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Use function extensionality and compare the values at `v`. Rewrite using `[Pi.star_apply, atEmb_embedding_apply, atEmb_embedding_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem star_atEmb (w : InfinitePlace E) (z : ℂ) :
    star (atEmb w.embedding z) = atEmb w.embedding (starRingEnd ℂ z) := by
  classical
  funext v
  rw [Pi.star_apply, atEmb_embedding_apply, atEmb_embedding_apply]
  split_ifs <;> simp

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Simplify using `[eW, star_atEmb]`.
-/
theorem star_eW (w : InfinitePlace E) : star (eW w) = eW w := by
  simp [eW, star_atEmb]

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Use function extensionality and compare the values at `v`. Simplify using `only [fW, star_atEmb, Pi.neg_apply, atEmb_embedding_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem star_fW (w : InfinitePlace E) : star (fW w) = -fW w := by
  classical
  funext v
  simp only [fW, star_atEmb, Pi.neg_apply, atEmb_embedding_apply]
  split_ifs <;> simp

omit [IsTotallyComplex E] in
/- English proof (translation)
Establish `e : ∀ w, (x w).re • eW w + (x w).im • fW w = atEmb w.embedding (x w)` using `fun w => (atEmb_eq _ _).symm`. Simplify using `only [e]`. Use function extensionality and compare the values at `v`. Simplify using `[Finset.sum_apply, atEmb_embedding_apply]`.
-/
theorem sum_atEmb (x : Cinf E) : x = ∑ w, ((x w).re • eW w + (x w).im • fW w) := by
  classical
  have e : ∀ w, (x w).re • eW w + (x w).im • fW w = atEmb w.embedding (x w) := fun w =>
    (atEmb_eq _ _).symm
  simp only [e]
  funext v
  simp [Finset.sum_apply, atEmb_embedding_apply]

def famZ : InfinitePlace E × Fin a × Fin a × Bool × Bool → Lie E a
  | (w, i, j, false, false) => sgl i j (eW w) + sgl j i (eW w)
  | (w, i, j, false, true) => sgl i j (eW w) - sgl j i (eW w)
  | (w, i, j, true, false) => sgl i j (fW w) - sgl j i (fW w)
  | (w, i, j, true, true) => sgl i j (fW w) + sgl j i (fW w)

/- English proof (translation)
Use `set S := Submodule.span ℝ (Set.range (famZ (E := E) (a := a))) with hS`. Establish `hz : ∀ k, famZ (E` using `E) (a := a) k ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩`. Establish `hE : ∀ w i j, sgl (E` using `E) (a := a) i j (eW w) ∈ S := fun w i j => by`. Establish `e : sgl (E` using `E) (a := a) i j (eW w) = (1 / 2 : ℝ) • (famZ (w, i, j, false, false) + famZ (w, i, j, false, true)) := by`. Express the relevant statement in the definitionally equal form `_ = (1 / 2 : ℝ) • ((sgl i j (eW w) + sgl j i (eW w)) + (sgl i j (eW w) - sgl j i (eW w)))`.

Use `module`. Rewrite using `[e]`. Conclude with `S.smul_mem _ (S.add_mem (hz _) (hz _))`. Establish `hF : ∀ w i j, sgl (E` using `E) (a := a) i j (fW w) ∈ S := fun w i j => by`. Establish `e : sgl (E` using `E) (a := a) i j (fW w) = (1 / 2 : ℝ) • (famZ (w, i, j, true, false) + famZ (w, i, j, true, true)) := by`.

Express the relevant statement in the definitionally equal form `_ = (1 / 2 : ℝ) • ((sgl i j (fW w) - sgl j i (fW w)) + (sgl i j (fW w) + sgl j i (fW w)))`. Use `module`. Rewrite using `[e]`. Conclude with `S.smul_mem _ (S.add_mem (hz _) (hz _))`. Establish `hx : ∀ i j (x : Cinf E), sgl (a` using `a) i j x ∈ S := fun i j x => by`.

Rewrite using `[sum_atEmb x, map_sum]`. Use `S.sum_mem fun w _ => ?_` and prove the remaining obligations. Rewrite using `[map_add, map_smul, map_smul]`. Conclude with `S.add_mem (S.smul_mem _ (hE w i j)) (S.smul_mem _ (hF w i j))`. Use `eq_top_iff.2 fun L _ => ?_` and prove the remaining obligations.

Establish `e : L = ∑ i, ∑ j, sgl i j (L i j)` using `Matrix.matrix_eq_sum_single (Matrix.of L)`. Rewrite using `[e]`. Conclude with `S.sum_mem fun i _ => S.sum_mem fun j _ => hx i j _`.
-/
theorem span_famZ : Submodule.span ℝ (Set.range (famZ (E := E) (a := a))) = ⊤ := by
  set S := Submodule.span ℝ (Set.range (famZ (E := E) (a := a))) with hS
  have hz : ∀ k, famZ (E := E) (a := a) k ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hE : ∀ w i j, sgl (E := E) (a := a) i j (eW w) ∈ S := fun w i j => by
    have e : sgl (E := E) (a := a) i j (eW w) =
        (1 / 2 : ℝ) • (famZ (w, i, j, false, false) + famZ (w, i, j, false, true)) := by
      change _ = (1 / 2 : ℝ) • ((sgl i j (eW w) + sgl j i (eW w)) + (sgl i j (eW w) - sgl j i (eW w)))
      module
    rw [e]
    exact S.smul_mem _ (S.add_mem (hz _) (hz _))
  have hF : ∀ w i j, sgl (E := E) (a := a) i j (fW w) ∈ S := fun w i j => by
    have e : sgl (E := E) (a := a) i j (fW w) =
        (1 / 2 : ℝ) • (famZ (w, i, j, true, false) + famZ (w, i, j, true, true)) := by
      change _ = (1 / 2 : ℝ) • ((sgl i j (fW w) - sgl j i (fW w)) + (sgl i j (fW w) + sgl j i (fW w)))
      module
    rw [e]
    exact S.smul_mem _ (S.add_mem (hz _) (hz _))
  have hx : ∀ i j (x : Cinf E), sgl (a := a) i j x ∈ S := fun i j x => by
    rw [sum_atEmb x, map_sum]
    refine S.sum_mem fun w _ => ?_
    rw [map_add, map_smul, map_smul]
    exact S.add_mem (S.smul_mem _ (hE w i j)) (S.smul_mem _ (hF w i j))
  refine eq_top_iff.2 fun L _ => ?_
  have e : L = ∑ i, ∑ j, sgl i j (L i j) := Matrix.matrix_eq_sum_single (Matrix.of L)
  rw [e]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => hx i j _

/- English proof (translation)
The claim follows from `Matrix.conjTranspose_single i j x`.
-/
theorem conjTranspose_sgl (i j : Fin a) (x : Cinf E) :
    (Matrix.of (sgl i j x))ᴴ = Matrix.of (sgl j i (star x)) :=
  Matrix.conjTranspose_single i j x

/- English proof (translation)
Take `⟨w, i, j, b, c⟩` from `k`. Take `rfl : c = true` from `hk`. Consider the cases of `b`. Express the relevant statement in the definitionally equal form `(Matrix.of (sgl i j (eW w)) - Matrix.of (sgl j i (eW w)))ᴴ = -(Matrix.of (sgl i j (eW w)) - Matrix.of (sgl j i (eW w)))`. Rewrite using `[Matrix.conjTranspose_sub, conjTranspose_sgl, conjTranspose_sgl, star_eW, neg_sub]`.

Express the relevant statement in the definitionally equal form `(Matrix.of (sgl i j (fW w)) + Matrix.of (sgl j i (fW w)))ᴴ = -(Matrix.of (sgl i j (fW w)) + Matrix.of (sgl j i (fW w)))`. Establish `hn : ∀ i j : Fin a, Matrix.of (sgl i j (-fW w)) = -Matrix.of (sgl i j (fW w))` using `fun i j => by`. Rewrite using `[map_neg]`. Both sides reduce to the same expression. Rewrite using `[Matrix.conjTranspose_add, conjTranspose_sgl, conjTranspose_sgl, star_fW, hn, hn, neg_add, add_comm]`.
-/
theorem skew_famZ (k : InfinitePlace E × Fin a × Fin a × Bool × Bool) (hk : k.2.2.2.2 = true) :
    (Matrix.of (famZ k))ᴴ = -(Matrix.of (famZ k)) := by
  obtain ⟨w, i, j, b, c⟩ := k
  obtain rfl : c = true := hk
  cases b
  · change (Matrix.of (sgl i j (eW w)) - Matrix.of (sgl j i (eW w)))ᴴ =
      -(Matrix.of (sgl i j (eW w)) - Matrix.of (sgl j i (eW w)))
    rw [Matrix.conjTranspose_sub, conjTranspose_sgl, conjTranspose_sgl, star_eW, neg_sub]
  · change (Matrix.of (sgl i j (fW w)) + Matrix.of (sgl j i (fW w)))ᴴ =
      -(Matrix.of (sgl i j (fW w)) + Matrix.of (sgl j i (fW w)))
    have hn : ∀ i j : Fin a, Matrix.of (sgl i j (-fW w)) = -Matrix.of (sgl i j (fW w)) := fun i j => by
      rw [map_neg]; rfl
    rw [Matrix.conjTranspose_add, conjTranspose_sgl, conjTranspose_sgl, star_fW, hn, hn, neg_add, add_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Eop_embedding (w : InfinitePlace E) (i j : Fin a) :
    Eop w.embedding i j = (1 / 2 : ℂ) • (lieS E a i j (eW w) - Complex.I • lieS E a i j (fW w)) := rfl

/- English proof (translation)
Establish `h : atEmb w.embedding (-Complex.I) = -fW w`. Rewrite using `[atEmb_eq]`. Simplify using `[fW]`. Rewrite using `[Eop, atEmb_conj, atEmb_conj, map_one, Complex.conj_I, h, map_neg, smul_neg, sub_neg_eq_add]`. Both sides reduce to the same expression.
-/
theorem Eop_conjugate (w : InfinitePlace E) (i j : Fin a) :
    Eop (ComplexEmbedding.conjugate w.embedding) i j =
      (1 / 2 : ℂ) • (lieS E a i j (eW w) + Complex.I • lieS E a i j (fW w)) := by
  have h : atEmb w.embedding (-Complex.I) = -fW w := by
    rw [atEmb_eq]; simp [fW]
  rw [Eop, atEmb_conj, atEmb_conj, map_one, Complex.conj_I, h, map_neg, smul_neg, sub_neg_eq_add]
  rfl

/- English proof (translation)
Establish `e : ∀ f : InfinitePlace E × Fin a × Fin a × Bool × Bool → Module.End ℂ (Sm E a), ∑ k ∈ (Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true)ᶜ, f k - ∑ k ∈ Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2. …` using `fun f => by`. Rewrite using `[Finset.compl_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : k.2.2.2.2 = true <;> simp [h]`. Rewrite using `[e]`.

Simplify using `only [Fintype.sum_prod_type, Fintype.sum_bool]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `h` using `sum_squares_eq (fun i j : Fin a => lieS E a i j (eW w)) (fun i j => lieS E a i j (fW w))`. Establish `c1 : Formalism.REAL.Cas (Eop (a` using `a) w.embedding) = Formalism.REAL.Cas (fun i j : Fin a => (1 / 2 : ℂ) • (lieS E a i j (eW w) - Complex.I • lieS E a i j (fW w))) := rfl`. Establish `c2 : Formalism.REAL.Cas (Eop (a` using `a) (ComplexEmbedding.conjugate w.embedding)) = Formalism.REAL.Cas (fun i j : Fin a => (1 / 2 : ℂ) • (lieS E a i j (eW w) + Complex.I • lieS E a i j (fW w))) := congrArg _ (funext fun i => funext fun j => Eop_conjugate w i j)`.

Rewrite using `[c1, c2, ← h]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `f1 : lie E a (famZ (w, i, j, false, false)) = lieS E a i j (eW w) + lieS E a j i (eW w)` using `map_add _ _ _`. Establish `f2 : lie E a (famZ (w, i, j, false, true)) = lieS E a i j (eW w) - lieS E a j i (eW w)` using `map_sub _ _ _`. Establish `f3 : lie E a (famZ (w, i, j, true, false)) = lieS E a i j (fW w) - lieS E a j i (fW w)` using `map_sub _ _ _`.

Establish `f4 : lie E a (famZ (w, i, j, true, true)) = lieS E a i j (fW w) + lieS E a j i (fW w)` using `map_add _ _ _`. Simplify using `only [if_true, Bool.false_eq_true, if_false, f1, f2, f3, f4]`. Normalize the expressions using the abelian group laws.
-/
theorem sum_famZ [DecidableEq (InfinitePlace E)] :
    ∑ k ∈ (Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true)ᶜ,
        lie E a (famZ k) * lie E a (famZ k) -
      ∑ k ∈ Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true,
        lie E a (famZ k) * lie E a (famZ k) =
    ∑ w : InfinitePlace E, (8 : ℂ) • (Formalism.REAL.Cas (Eop (a := a) w.embedding) +
      Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding))) := by
  have e : ∀ f : InfinitePlace E × Fin a × Fin a × Bool × Bool → Module.End ℂ (Sm E a),
      ∑ k ∈ (Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true)ᶜ, f k -
        ∑ k ∈ Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true, f k =
      ∑ k, if k.2.2.2.2 = true then -f k else f k := fun f => by
    rw [Finset.compl_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : k.2.2.2.2 = true <;> simp [h]
  rw [e]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h := sum_squares_eq (fun i j : Fin a => lieS E a i j (eW w)) (fun i j => lieS E a i j (fW w))
  have c1 : Formalism.REAL.Cas (Eop (a := a) w.embedding) = Formalism.REAL.Cas (fun i j : Fin a =>
      (1 / 2 : ℂ) • (lieS E a i j (eW w) - Complex.I • lieS E a i j (fW w))) := rfl
  have c2 : Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding)) = Formalism.REAL.Cas (fun i j : Fin a =>
      (1 / 2 : ℂ) • (lieS E a i j (eW w) + Complex.I • lieS E a i j (fW w))) :=
    congrArg _ (funext fun i => funext fun j => Eop_conjugate w i j)
  rw [c1, c2, ← h]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have f1 : lie E a (famZ (w, i, j, false, false)) = lieS E a i j (eW w) + lieS E a j i (eW w) := map_add _ _ _
  have f2 : lie E a (famZ (w, i, j, false, true)) = lieS E a i j (eW w) - lieS E a j i (eW w) := map_sub _ _ _
  have f3 : lie E a (famZ (w, i, j, true, false)) = lieS E a i j (fW w) - lieS E a j i (fW w) := map_sub _ _ _
  have f4 : lie E a (famZ (w, i, j, true, true)) = lieS E a i j (fW w) + lieS E a j i (fW w) := map_add _ _ _
  simp only [if_true, Bool.false_eq_true, if_false, f1, f2, f3, f4]
  abel

/- English proof (translation)
Introduce `E _ _ _ a`. Establish `: DecidableEq (InfinitePlace E)` using `Classical.decEq _`. Use `⟨InfinitePlace E × Fin a × Fin a × Bool × Bool, inferInstance, inferInstance, famZ, Finset.univ.filter fun k => k.2.2.2.2 = true, span_famZ, fun κ hκ => skew_famZ κ (Finset.mem_filter.1 hκ).2, ?_⟩` and prove the remaining obligations. Rewrite using `[sum_famZ]`. Conclude with `Subalgebra.sum_mem _ fun w _ => Subalgebra.smul_mem _ (Subalgebra.add_mem _ (GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg E a _) (GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg E a _)) _`.
-/
theorem exists_family : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Z : ι → GlobalTheory.CuspRep.Lie E a) (K : Finset ι), Submodule.span ℝ (Set.range Z) = ⊤ ∧ (∀ κ ∈ K, (Matrix.of (Z κ))ᴴ = -(Matrix.of (Z κ))) ∧ (∑ i ∈ Kᶜ, lie E a (Z i) * lie E a (Z i) - ∑ κ ∈ K, lie E a (Z κ) * lie E a (Z κ)) ∈ Zalg E a := by
  intro E _ _ _ a
  have : DecidableEq (InfinitePlace E) := Classical.decEq _
  refine ⟨InfinitePlace E × Fin a × Fin a × Bool × Bool, inferInstance, inferInstance, famZ,
    Finset.univ.filter fun k => k.2.2.2.2 = true, span_famZ, fun κ hκ => skew_famZ κ (Finset.mem_filter.1 hκ).2, ?_⟩
  rw [sum_famZ]
  exact Subalgebra.sum_mem _ fun w _ => Subalgebra.smul_mem _
    (Subalgebra.add_mem _ (GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg E a _) (GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg E a _)) _

end GlobalTheory.CompanionTheory.CasFamily
