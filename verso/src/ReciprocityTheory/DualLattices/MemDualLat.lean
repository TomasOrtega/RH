import ReciprocityTheory.DualLattices.SubgroupQuotientStatement
import ReciprocityTheory.DualLattices.ExistsSmulMemOfMemSpan
import ReciprocityTheory.DualLattices.MapTensorSpan

noncomputable section

namespace ReciprocityTheory.PGsh.L2

open SecondCohomologyLattice

section SlopeTestRemainingChoices

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_dualLat {X : Type} [Fintype X] (M : Submodule R (X → C)) (u : X → C) :
    u ∈ dualLat M ↔ ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a := Iff.rfl

/- English proof (translation)
Take `⟨G, hG⟩ : ∃ G : N → C, G = fun a => if h : a ∈ K then u ⟨a, h⟩ * f a else 0` from `⟨_, rfl⟩`. Establish `e1 : ∀ a, extK (R` using `R) K u a * f a = G a := by`. Introduce `a`. Use `show (if h : a ∈ K then u ⟨a, h⟩ else 0) * f a = G a`. Distinguish the cases in `h : a ∈ K`.

Simplify using `[hG, h]`. Simplify using `[hG, h]`. Establish `e2 : ∀ k : K, u k * f k = G k`. Introduce `k`. Simplify using `[hG, k.2]`.

Simplify using `only [e1, e2]`. Rewrite using `[← Finset.sum_subtype (p := (· ∈ K)) (Finset.univ.filter (· ∈ K)) (fun x => by simp) G, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : a ∈ K`. Simplify using `[h]`.

Simplify using `[hG, h]`.
-/
private theorem sum_extK {N : Type} [AddCommGroup N] [Fintype N] (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] (u : K → C) (f : N → C) :
    ∑ a, extK (R := R) K u a * f a = ∑ k : K, u k * f k := by
  obtain ⟨G, hG⟩ : ∃ G : N → C, G = fun a => if h : a ∈ K then u ⟨a, h⟩ * f a else 0 :=
    ⟨_, rfl⟩
  have e1 : ∀ a, extK (R := R) K u a * f a = G a := by
    intro a
    show (if h : a ∈ K then u ⟨a, h⟩ else 0) * f a = G a
    by_cases h : a ∈ K
    · simp [hG, h]
    · simp [hG, h]
  have e2 : ∀ k : K, u k * f k = G k := by
    intro k
    simp [hG, k.2]
  simp only [e1, e2]
  rw [← Finset.sum_subtype (p := (· ∈ K)) (Finset.univ.filter (· ∈ K)) (fun x => by simp) G,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a ∈ K
  · simp [h]
  · simp [hG, h]

/- English proof (translation)
Establish `e1 : ∀ c, pushQ (R` using `R) K u c * g c = ∑ a ∈ Finset.univ.filter (fun a : N => (a : N ⧸ K) = c), u a * g (a : N ⧸ K) := by`. Introduce `c`. Use `show (∑ a ∈ Finset.univ.filter (fun a : N => (a : N ⧸ K) = c), u a) * g c = _`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations.

Rewrite using `[(Finset.mem_filter.1 ha).2]`. Simplify using `only [e1]`. Conclude with `Finset.sum_fiberwise Finset.univ (fun a : N => (a : N ⧸ K)) (fun a => u a * g (a : N ⧸ K))`.
-/
private theorem sum_pushQ {N : Type} [AddCommGroup N] [Fintype N] (K : AddSubgroup N)
    [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)] (u : N → C) (g : N ⧸ K → C) :
    ∑ c, pushQ (R := R) K u c * g c = ∑ a, u a * g (a : N ⧸ K) := by
  have e1 : ∀ c, pushQ (R := R) K u c * g c =
      ∑ a ∈ Finset.univ.filter (fun a : N => (a : N ⧸ K) = c), u a * g (a : N ⧸ K) := by
    intro c
    show (∑ a ∈ Finset.univ.filter (fun a : N => (a : N ⧸ K) = c), u a) * g c = _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.1 ha).2]
  simp only [e1]
  exact Finset.sum_fiberwise Finset.univ (fun a : N => (a : N ⧸ K)) (fun a => u a * g (a : N ⧸ K))

end SlopeTestRemainingChoices

/- English proof (translation)
Set `A : (X → ι) → Matrix X X C` to `fun σ x y => w (σ y) x`. Take `⟨s, hs, hss, hli⟩` from `exists_linearIndependent C (Set.range w)`. Set `bs : Module.Basis s C (X → C)` to `Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hss, hw]))`. Set `e : s ≃ X` to `bs.indexEquiv (Pi.basisFun C X)`. Establish `hpre : ∀ x, ∃ i, w i = ((e.symm x : s) : X → C)` using `fun x => hs (e.symm x).2`.

Use `choose σ0 hσ0 using hpre`. Establish `h0 : (A σ0).det ≠ 0`. Establish `hli' : LinearIndependent C (fun y => (Matrix.transpose (A σ0)) y)`. Establish `hfun : (fun y => (Matrix.transpose (A σ0)) y) = (fun y => ((e.symm y : s) : X → C))`. Use function extensionality and compare the values at `y x`.

Use `show w (σ0 y) x = ((e.symm y : s) : X → C) x`. Rewrite using `[hσ0]`. Rewrite using `[hfun]`. Conclude with `hli.comp e.symm e.symm.injective`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli')).ne_zero`.

Use `haveI : Nonempty (X → ι) := ⟨σ0⟩`. Take `⟨σ, hσ⟩` from `Finite.exists_max (fun σ : X → ι => v (A σ).det)`. Establish `hne : (A σ).det ≠ 0`. Introduce `h`. Establish `h1` using `hσ σ0`.

Rewrite `h1` using `[h, map_zero]`. Conclude with `h0 ((Valuation.zero_iff v).1 (le_antisymm h1 zero_le))`. Establish `hvne : v (A σ).det ≠ 0` using `fun h => hne ((Valuation.zero_iff v).1 h)`. Use `⟨A σ, isUnit_iff_ne_zero.2 hne, ?_⟩` and prove the remaining obligations. Establish `hcols : Set.range (fun j x => A σ x j) = Set.range (w ∘ σ)` using `rfl`.

Rewrite using `[hcols]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `hup : ∀ y, Matrix.cramer (A σ) (w i) y = (A (Function.update σ y i)).det`.

Introduce `y`. Rewrite using `[Matrix.cramer_apply]`. Use `congr 1`. Use extensionality with `x y'`. Simplify using `only [Matrix.updateCol, Matrix.of_apply, Function.update_apply, A]`.

Apply the tactic sequence `split_ifs <;> rfl`. Establish `hc : ∀ y, ∃ r : R, algebraMap R C r = (A σ).det⁻¹ * Matrix.cramer (A σ) (w i) y`. Introduce `y`. Apply `hv.exists_of_le_one` to reduce the goal to its premises. Rewrite using `[hup, map_mul, map_inv₀]`.

Combine the equalities or inequalities in the displayed calculation. Use `choose r hr using hc`. Establish `hm` using `Matrix.mulVec_cramer (A σ) (w i)`. Establish `hsum : w i = ∑ y, r y • (w ∘ σ) y`. Use function extensionality and compare the values at `x`.

Establish `hx : ∑ y, w (σ y) x * Matrix.cramer (A σ) (w i) y = (A σ).det * w i x` using `congrFun hm x`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply]`. Simplify using `only [Algebra.smul_def, hr]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hne, one_mul]`.

Use `_ = (A σ).det⁻¹ * ∑ y, w (σ y) x * Matrix.cramer (A σ) (w i) y := by rw [hx]`. Use `_ = ∑ y, (A σ).det⁻¹ * Matrix.cramer (A σ) (w i) y * w (σ y) x := by`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun y _ => by ring`. Rewrite using `[hsum]`.

Conclude with `Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)`. Conclude with `Submodule.span_mono (Set.range_comp_subset_range σ w)`.
-/
private theorem isLat_span_lemma {C R : Type} [Field C] [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) (hv : v.Integers R) {X ι : Type} [Fintype X] [DecidableEq X]
    [Fintype ι] [DecidableEq ι] (w : ι → X → C)
    (hw : Submodule.span C (Set.range w) = ⊤) :
    IsLat R (Submodule.span R (Set.range w)) := by
  let A : (X → ι) → Matrix X X C := fun σ x y => w (σ y) x
  obtain ⟨s, hs, hss, hli⟩ := exists_linearIndependent C (Set.range w)
  let bs : Module.Basis s C (X → C) :=
    Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hss, hw]))
  let e : s ≃ X := bs.indexEquiv (Pi.basisFun C X)
  have hpre : ∀ x, ∃ i, w i = ((e.symm x : s) : X → C) := fun x => hs (e.symm x).2
  choose σ0 hσ0 using hpre
  have h0 : (A σ0).det ≠ 0 := by
    have hli' : LinearIndependent C (fun y => (Matrix.transpose (A σ0)) y) := by
      have hfun : (fun y => (Matrix.transpose (A σ0)) y) = (fun y => ((e.symm y : s) : X → C)) := by
        funext y x
        show w (σ0 y) x = ((e.symm y : s) : X → C) x
        rw [hσ0]
      rw [hfun]
      exact hli.comp e.symm e.symm.injective
    exact ((Matrix.isUnit_iff_isUnit_det _).1
      (Matrix.linearIndependent_cols_iff_isUnit.1 hli')).ne_zero
  haveI : Nonempty (X → ι) := ⟨σ0⟩
  obtain ⟨σ, hσ⟩ := Finite.exists_max (fun σ : X → ι => v (A σ).det)
  have hne : (A σ).det ≠ 0 := by
    intro h
    have h1 := hσ σ0
    rw [h, map_zero] at h1
    exact h0 ((Valuation.zero_iff v).1 (le_antisymm h1 zero_le))
  have hvne : v (A σ).det ≠ 0 := fun h => hne ((Valuation.zero_iff v).1 h)
  refine ⟨A σ, isUnit_iff_ne_zero.2 hne, ?_⟩
  have hcols : Set.range (fun j x => A σ x j) = Set.range (w ∘ σ) := rfl
  rw [hcols]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hup : ∀ y, Matrix.cramer (A σ) (w i) y = (A (Function.update σ y i)).det := by
      intro y
      rw [Matrix.cramer_apply]
      congr 1
      ext x y'
      simp only [Matrix.updateCol, Matrix.of_apply, Function.update_apply, A]
      split_ifs <;> rfl
    have hc : ∀ y, ∃ r : R, algebraMap R C r = (A σ).det⁻¹ * Matrix.cramer (A σ) (w i) y := by
      intro y
      apply hv.exists_of_le_one
      rw [hup, map_mul, map_inv₀]
      calc (v (A σ).det)⁻¹ * v (A (Function.update σ y i)).det
          ≤ (v (A σ).det)⁻¹ * v (A σ).det := mul_le_mul_of_nonneg_left (hσ _) zero_le
        _ = 1 := inv_mul_cancel₀ hvne
    choose r hr using hc
    have hm := Matrix.mulVec_cramer (A σ) (w i)
    have hsum : w i = ∑ y, r y • (w ∘ σ) y := by
      funext x
      have hx : ∑ y, w (σ y) x * Matrix.cramer (A σ) (w i) y = (A σ).det * w i x :=
        congrFun hm x
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply]
      simp only [Algebra.smul_def, hr]
      calc w i x = (A σ).det⁻¹ * ((A σ).det * w i x) := by
            rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
        _ = (A σ).det⁻¹ * ∑ y, w (σ y) x * Matrix.cramer (A σ) (w i) y := by rw [hx]
        _ = ∑ y, (A σ).det⁻¹ * Matrix.cramer (A σ) (w i) y * w (σ y) x := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun y _ => by ring
    rw [hsum]
    exact Submodule.sum_mem _ fun y _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  · exact Submodule.span_mono (Set.range_comp_subset_range σ w)

/- English proof (translation)
Set `Q : Submodule R (X → C)` to `{ carrier := {f | ∃ r : R, algebraMap R C r = ∑ a, u a * f a} add_mem' := by`. Introduce and unpack `f g ⟨r, hr⟩ ⟨s, hs⟩`. Use `⟨r + s, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hr, hs, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c f ⟨r, hr⟩`.

Use `⟨c * r, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hr, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, Algebra.smul_def]`. Use `ring }`.

Establish `hle : Submodule.span R S ≤ Q` using `Submodule.span_le.2 (fun f hf => h f hf)`. Use `(mem_dualLat _ _).2 fun f hf => ?_` and prove the remaining obligations. Conclude with `hle hf`.
-/
private theorem mem_dualLat_span_lemma_2 {C R : Type} [Field C] [CommRing R] [Algebra R C]
    {X : Type} [Fintype X] (S : Set (X → C)) (u : X → C)
    (h : ∀ f ∈ S, ∃ r : R, algebraMap R C r = ∑ a, u a * f a) :
    u ∈ dualLat (Submodule.span R S) := by
  let Q : Submodule R (X → C) :=
    { carrier := {f | ∃ r : R, algebraMap R C r = ∑ a, u a * f a}
      add_mem' := by
        rintro f g ⟨r, hr⟩ ⟨s, hs⟩
        refine ⟨r + s, ?_⟩
        rw [map_add, hr, hs, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [Pi.add_apply]
        ring
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c f ⟨r, hr⟩
        refine ⟨c * r, ?_⟩
        rw [map_mul, hr, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [Pi.smul_apply, Algebra.smul_def]
        ring }
  have hle : Submodule.span R S ≤ Q := Submodule.span_le.2 (fun f hf => h f hf)
  refine (mem_dualLat _ _).2 fun f hf => ?_
  exact hle hf

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `u hu`. Rewrite `hu` using `[mem_dualLat]`. Establish `hc : ∀ j, ∃ r : R, algebraMap R C r = ∑ a, u a * B a j` using `fun j => hu _ (Submodule.subset_span ⟨j, rfl⟩)`. Use `choose r hr using hc`.

Establish `hinv : ∀ a x, ∑ j, B a j * B⁻¹ j x = if a = x then 1 else 0`. Introduce `a x`. Establish `h` using `congrFun (congrFun (Matrix.mul_nonsing_inv B hB) a) x`. Rewrite `h` using `[Matrix.mul_apply, Matrix.one_apply]`. Conclude with `h`.

Establish `hu' : u = ∑ j, r j • (fun x => B⁻¹ j x)`. Use function extensionality and compare the values at `x`. Simplify using `only [Finset.sum_apply, Pi.smul_apply]`. Simplify using `only [Algebra.smul_def, hr]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by ring`. Rewrite using `[hu']`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `show (fun x => B⁻¹ i x) ∈ dualLat (Submodule.span R (Set.range fun j x => B x j))`. Use `mem_dualLat_span_lemma_2 _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `show ∃ r : R, algebraMap R C r = ∑ a, B⁻¹ i a * B a j`. Establish `h` using `congrFun (congrFun (Matrix.nonsing_inv_mul B hB) i) j`. Rewrite `h` using `[Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[h]`. Distinguish the cases in `hij : i = j`.

Conclude with `⟨1, by simp [hij]⟩`. Conclude with `⟨0, by simp [hij]⟩`.
-/
private theorem dualLat_cols_lemma_3 {C R : Type} [Field C] [CommRing R] [Algebra R C]
    {X : Type} [Fintype X] [DecidableEq X] (B : Matrix X X C) (hB : IsUnit B.det) :
    dualLat (Submodule.span R (Set.range fun j x => B x j)) =
      Submodule.span R (Set.range fun j x => B⁻¹ j x) := by
  apply le_antisymm
  · intro u hu
    rw [mem_dualLat] at hu
    have hc : ∀ j, ∃ r : R, algebraMap R C r = ∑ a, u a * B a j := fun j =>
      hu _ (Submodule.subset_span ⟨j, rfl⟩)
    choose r hr using hc
    have hinv : ∀ a x, ∑ j, B a j * B⁻¹ j x = if a = x then 1 else 0 := by
      intro a x
      have h := congrFun (congrFun (Matrix.mul_nonsing_inv B hB) a) x
      rw [Matrix.mul_apply, Matrix.one_apply] at h
      exact h
    have hu' : u = ∑ j, r j • (fun x => B⁻¹ j x) := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply]
      simp only [Algebra.smul_def, hr]
      calc u x = ∑ a, u a * (if a = x then 1 else 0) := by simp
        _ = ∑ a, u a * ∑ j, B a j * B⁻¹ j x := by simp only [hinv]
        _ = ∑ j, (∑ a, u a * B a j) * B⁻¹ j x := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by ring
    rw [hu']
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show (fun x => B⁻¹ i x) ∈ dualLat (Submodule.span R (Set.range fun j x => B x j))
    refine mem_dualLat_span_lemma_2 _ _ ?_
    rintro _ ⟨j, rfl⟩
    show ∃ r : R, algebraMap R C r = ∑ a, B⁻¹ i a * B a j
    have h := congrFun (congrFun (Matrix.nonsing_inv_mul B hB) i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [h]
    by_cases hij : i = j
    · exact ⟨1, by simp [hij]⟩
    · exact ⟨0, by simp [hij]⟩

/- English proof (translation)
Take `⟨B, hB, rfl⟩` from `hM`. Establish `hBt : IsUnit ((Matrix.transpose (B⁻¹))).det`. Rewrite using `[Matrix.det_transpose]`. Conclude with `Matrix.isUnit_nonsing_inv_det B hB`. Use `⟨⟨(Matrix.transpose (B⁻¹)), hBt, ?_⟩, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `rw [dualLat_cols_lemma_3 (R := R) B hB] all_goals rfl`. Rewrite using `[dualLat_cols_lemma_3 (R := R) B hB]`. Establish `e : (Set.range fun j x => B⁻¹ j x) = Set.range fun j x => ((Matrix.transpose (B⁻¹))) x j` using `rfl`. Rewrite using `[e, dualLat_cols_lemma_3 (R := R) ((Matrix.transpose (B⁻¹))) hBt, ← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv B hB]`. Apply the tactic sequence `all_goals rfl`.
-/
private theorem dual_isLat_lemma_4 {C R : Type} [Field C] [CommRing R] [Algebra R C]
    {X : Type} [Fintype X] [DecidableEq X] (M : Submodule R (X → C)) (hM : IsLat R M) :
    IsLat R (dualLat M) ∧ dualLat (dualLat M) = M := by
  obtain ⟨B, hB, rfl⟩ := hM
  have hBt : IsUnit ((Matrix.transpose (B⁻¹))).det := by
    rw [Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det B hB
  refine ⟨⟨(Matrix.transpose (B⁻¹)), hBt, ?_⟩, ?_⟩
  · rw [dualLat_cols_lemma_3 (R := R) B hB]
    all_goals rfl
  · rw [dualLat_cols_lemma_3 (R := R) B hB]
    have e : (Set.range fun j x => B⁻¹ j x) = Set.range fun j x => ((Matrix.transpose (B⁻¹))) x j := rfl
    rw [e, dualLat_cols_lemma_3 (R := R) ((Matrix.transpose (B⁻¹))) hBt, ← Matrix.transpose_nonsing_inv,
      Matrix.nonsing_inv_nonsing_inv B hB]
    all_goals rfl

/- English proof (translation)
Take `⟨B, hB, rfl⟩` from `hM`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Apply `isLat_span_lemma v hv` to reduce the goal to its premises. Rewrite using `[Submodule.eq_top_iff']`. Introduce `t`.

Take `⟨f, rfl⟩` from `hT t`. Establish `hinv : ∀ x k, ∑ j, B x j * B⁻¹ j k = if x = k then 1 else 0`. Introduce `x k`. Establish `h` using `congrFun (congrFun (Matrix.mul_nonsing_inv B hB) x) k`. Rewrite `h` using `[Matrix.mul_apply, Matrix.one_apply]`.

Conclude with `h`. Establish `hf : f = ∑ j, (∑ k, B⁻¹ j k * f k) • (fun x => B x j)`. Use function extensionality and compare the values at `x`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring`. Rewrite using `[hf, map_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_⟩)` and prove the remaining obligations. Use `show T' (fun x => B x j) = T (fun x => B x j)`. Conclude with `hTT _`.
-/
private theorem isLat_map_lemma_5 {C R : Type} [Field C] [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) (hv : v.Integers R)
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Submodule R (X → C)) (hM : IsLat R M) (T : (X → C) →ₗ[C] (Y → C))
    (hT : Function.Surjective T) (T' : (X → C) →ₗ[R] (Y → C)) (hTT : ∀ f, T' f = T f) :
    IsLat R (M.map T') := by
  obtain ⟨B, hB, rfl⟩ := hM
  rw [Submodule.map_span, ← Set.range_comp]
  apply isLat_span_lemma v hv
  rw [Submodule.eq_top_iff']
  intro t
  obtain ⟨f, rfl⟩ := hT t
  have hinv : ∀ x k, ∑ j, B x j * B⁻¹ j k = if x = k then 1 else 0 := by
    intro x k
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv B hB) x) k
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  have hf : f = ∑ j, (∑ k, B⁻¹ j k * f k) • (fun x => B x j) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc f x = ∑ k, (if x = k then 1 else 0) * f k := by simp
      _ = ∑ k, (∑ j, B x j * B⁻¹ j k) * f k := by simp only [hinv]
      _ = ∑ j, (∑ k, B⁻¹ j k * f k) * B x j := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hf, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_⟩)
  show T' (fun x => B x j) = T (fun x => B x j)
  exact hTT _

/- English proof (translation)
Rewrite `hx`, `hy` using `[mem_dualLat]`. Set `Q : Submodule R (X × X → C)` to `{ carrier := {F | ∃ r : R, algebraMap R C r = ∑ a, ∑ b, F (a, b) * x a * y b} add_mem' := by`. Introduce and unpack `F G ⟨r, hr⟩ ⟨s, hs⟩`. Use `⟨r + s, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hr, hs, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c F ⟨r, hr⟩`. Use `⟨c * r, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hr, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, Algebra.smul_def]`. Use `ring }`.

Establish `hle : tensorSpan R L ≤ Q` using `by show Submodule.span R {F : X × X → C | ∃ g ∈ L, ∃ h ∈ L, F = fun p => g p.1 * h p.2} ≤ Q`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, h, hh, rfl⟩`. Take `⟨r, hr⟩` from `hx g hg`. Take `⟨s, hs⟩` from `hy h hh`.

Use `show ∃ t : R, algebraMap R C t = ∑ a, ∑ b, g a * h b * x a * y b`. Use `⟨r * s, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hr, hs, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Conclude with `hle hF`.
-/
private theorem tensor_pair_lemma_6 {C R : Type} [Field C] [CommRing R] [Algebra R C]
    {X : Type} [Fintype X] (L : Submodule R (X → C)) (x y : X → C)
    (hx : x ∈ dualLat L) (hy : y ∈ dualLat L) (F : X × X → C) (hF : F ∈ tensorSpan R L) :
    ∃ r : R, algebraMap R C r = ∑ a, ∑ b, F (a, b) * x a * y b := by
  rw [mem_dualLat] at hx hy
  let Q : Submodule R (X × X → C) :=
    { carrier := {F | ∃ r : R, algebraMap R C r = ∑ a, ∑ b, F (a, b) * x a * y b}
      add_mem' := by
        rintro F G ⟨r, hr⟩ ⟨s, hs⟩
        refine ⟨r + s, ?_⟩
        rw [map_add, hr, hs, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [Pi.add_apply]
        ring
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c F ⟨r, hr⟩
        refine ⟨c * r, ?_⟩
        rw [map_mul, hr, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [Pi.smul_apply, Algebra.smul_def]
        ring }
  have hle : tensorSpan R L ≤ Q := by
    show Submodule.span R {F : X × X → C | ∃ g ∈ L, ∃ h ∈ L, F = fun p => g p.1 * h p.2} ≤ Q
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, h, hh, rfl⟩
    obtain ⟨r, hr⟩ := hx g hg
    obtain ⟨s, hs⟩ := hy h hh
    show ∃ t : R, algebraMap R C t = ∑ a, ∑ b, g a * h b * x a * y b
    refine ⟨r * s, ?_⟩
    rw [map_mul, hr, hs, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  exact hle hF

/- English proof (translation)
Take `⟨B, hB, rfl⟩` from `hL`. Establish `hD : ∀ i, (fun x => B⁻¹ i x) ∈ dualLat (Submodule.span R (Set.range fun j x => B x j))`. Introduce `i`. Rewrite using `[dualLat_cols_lemma_3 (R := R) B hB]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.

Establish `hc : ∀ i j, ∃ r : R, algebraMap R C r = ∑ a, ∑ b, F (a, b) * B⁻¹ i a * B⁻¹ j b` using `fun i j => hF _ (hD i) _ (hD j)`. Use `choose r hr using hc`. Set `Fm : Matrix X X C` to `Matrix.of fun a b => F (a, b)`. Set `c : Matrix X X C` to `B⁻¹ * Fm * (Matrix.transpose (B⁻¹))`. Establish `hcr : ∀ i j, c i j = ∑ a, ∑ b, F (a, b) * B⁻¹ i a * B⁻¹ j b`.

Introduce `i j`. Simplify using `only [c, Fm, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`. Establish `hrc : ∀ i j, algebraMap R C (r i j) = c i j` using `fun i j => (hr i j).trans (hcr i j).symm`.

Establish `hm : B * c * (Matrix.transpose B) = Fm`. Simplify using `only [c]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Fm := by`.

Rewrite using `[← Matrix.transpose_mul, Matrix.mul_nonsing_inv B hB, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]`. Establish `hFe : F = ∑ i, ∑ j, r i j • (fun p : X × X => B p.1 i * B p.2 j)`. Use function extensionality and compare the values at `p`. Take `⟨x, y⟩` from `p`. Establish `hxy : F (x, y) = (B * c * (Matrix.transpose B)) x y` using `(congrFun (congrFun hm x) y).symm`.

Rewrite using `[hxy]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply]`. Simplify using `only [Algebra.smul_def, hrc, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.

Rewrite using `[hFe]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Use `show _ ∈ Submodule.span R {G : X × X → C | ∃ g ∈ Submodule.span R (Set.range fun j x => B x j), ∃ h ∈ Submodule.span R (Set.range fun j x => B x j), G = fun p => g p.1 * h p.2}`. Conclude with `Submodule.subset_span ⟨fun x => B x i, Submodule.subset_span ⟨i, rfl⟩, fun x => B x j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩`.
-/
private theorem tensor_of_pair_lemma_7 {C R : Type} [Field C] [CommRing R] [Algebra R C]
    {X : Type} [Fintype X] [DecidableEq X] (L : Submodule R (X → C)) (hL : IsLat R L)
    (F : X × X → C)
    (hF : ∀ x ∈ dualLat L, ∀ y ∈ dualLat L,
      ∃ r : R, algebraMap R C r = ∑ a, ∑ b, F (a, b) * x a * y b) :
    F ∈ tensorSpan R L := by
  obtain ⟨B, hB, rfl⟩ := hL
  have hD : ∀ i, (fun x => B⁻¹ i x) ∈
      dualLat (Submodule.span R (Set.range fun j x => B x j)) := by
    intro i
    rw [dualLat_cols_lemma_3 (R := R) B hB]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hc : ∀ i j, ∃ r : R, algebraMap R C r = ∑ a, ∑ b, F (a, b) * B⁻¹ i a * B⁻¹ j b :=
    fun i j => hF _ (hD i) _ (hD j)
  choose r hr using hc
  let Fm : Matrix X X C := Matrix.of fun a b => F (a, b)
  let c : Matrix X X C := B⁻¹ * Fm * (Matrix.transpose (B⁻¹))
  have hcr : ∀ i j, c i j = ∑ a, ∑ b, F (a, b) * B⁻¹ i a * B⁻¹ j b := by
    intro i j
    simp only [c, Fm, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hrc : ∀ i j, algebraMap R C (r i j) = c i j := fun i j => (hr i j).trans (hcr i j).symm
  have hm : B * c * (Matrix.transpose B) = Fm := by
    simp only [c]
    calc B * (B⁻¹ * Fm * (Matrix.transpose (B⁻¹))) * (Matrix.transpose B) = (B * B⁻¹) * Fm * ((Matrix.transpose (B⁻¹)) * (Matrix.transpose B)) := by
          simp only [Matrix.mul_assoc]
      _ = Fm := by
          rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv B hB, Matrix.transpose_one,
            Matrix.one_mul, Matrix.mul_one]
  have hFe : F = ∑ i, ∑ j, r i j • (fun p : X × X => B p.1 i * B p.2 j) := by
    funext p
    obtain ⟨x, y⟩ := p
    have hxy : F (x, y) = (B * c * (Matrix.transpose B)) x y := (congrFun (congrFun hm x) y).symm
    rw [hxy]
    simp only [Finset.sum_apply, Pi.smul_apply]
    simp only [Algebra.smul_def, hrc, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hFe]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ ?_
  show _ ∈ Submodule.span R {G : X × X → C |
    ∃ g ∈ Submodule.span R (Set.range fun j x => B x j),
      ∃ h ∈ Submodule.span R (Set.range fun j x => B x j), G = fun p => g p.1 * h p.2}
  exact Submodule.subset_span ⟨fun x => B x i, Submodule.subset_span ⟨i, rfl⟩,
    fun x => B x j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩

/- English proof (translation)
Introduce `v hv N _ _ _ K _ _ _ AA`. Establish `hdual` using `dual_isLat_lemma_4 AA.carrier AA.lat`. Establish `e3 : dualLat (AA.carrier.map (resK (R` using `R) K)) = (dualLat AA.carrier).comap (extK K) := by`. Use extensionality with `u`. Rewrite using `[Submodule.mem_comap, mem_dualLat, mem_dualLat]`.

Prove the components needed by the constructor for the conclusion. Introduce `hu f hf`. Rewrite using `[sum_extK (R := R) K u f]`. Conclude with `hu _ (Submodule.mem_map_of_mem hf)`. Introduce and unpack `hu _ ⟨f, hf, rfl⟩`.

Establish `h` using `hu f hf`. Rewrite `h` using `[sum_extK (R := R) K u f]`. Conclude with `h`. Establish `hres_surj : Function.Surjective (resK (R` using `C) (C := C) K) := by`. Introduce `u`.

Use `⟨extK (R := C) (C := C) K u, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Use `show (if h : (k : N) ∈ K then u ⟨k, h⟩ else 0) = u k`. Rewrite using `[dif_pos k.2]`. Establish `hAK_lat : IsLat R (AA.carrier.map (resK (R` using `R) K)) := isLat_map_lemma_5 v hv AA.carrier AA.lat (resK (R := C) (C := C) K) hres_surj (resK (R := R) K) (fun _ => rfl)`.

Establish `hs : ∀ q : N ⧸ K, ∃ a : N, (a : N ⧸ K) = q` using `fun q => QuotientAddGroup.mk_surjective q`. Use `choose s hs using hs`. Establish `hpush_surj : Function.Surjective (pushQ (R` using `C) (C := C) K) := by`. Introduce `t`. Use `⟨fun a => if a = s (a : N ⧸ K) then t (a : N ⧸ K) else 0, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `c`. Use `show ∑ a ∈ Finset.univ.filter (fun a : N => (a : N ⧸ K) = c), (if a = s (a : N ⧸ K) then t (a : N ⧸ K) else 0) = t c`. Rewrite using `[Finset.sum_eq_single (s c)]`. Rewrite using `[hs c, if_pos rfl]`. Introduce `b hb hne`.

Rewrite using `[(Finset.mem_filter.1 hb).2, if_neg hne]`. Introduce `h`. Conclude with `(h (Finset.mem_filter.2 ⟨Finset.mem_univ _, hs c⟩)).elim`. Establish `hP_lat : IsLat R ((dualLat AA.carrier).map (pushQ (R` using `R) K)) := isLat_map_lemma_5 v hv (dualLat AA.carrier) hdual.1 (pushQ (R := C) (C := C) K) hpush_surj (pushQ (R := R) K) (fun _ => rfl)`. Establish `hPd` using `dual_isLat_lemma_4 _ hP_lat`.

Establish `eQ : AA.carrier.comap (pullQ (R` using `R) K) = dualLat ((dualLat AA.carrier).map (pushQ (R := R) K)) := by`. Use extensionality with `g`. Rewrite using `[Submodule.mem_comap]`. Prove the components needed by the constructor for the conclusion. Introduce `hg`.

Rewrite using `[mem_dualLat]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Take `⟨r, hr⟩` from `(mem_dualLat _ _).1 hw _ hg`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`.

Combine the equalities or inequalities in the displayed calculation. Introduce `hg`. Rewrite using `[← hdual.2, mem_dualLat]`. Introduce `w hw`. Rewrite `hg` using `[mem_dualLat]`.

Take `⟨r, hr⟩` from `hg _ (Submodule.mem_map_of_mem hw)`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`. Combine the equalities or inequalities in the displayed calculation. Establish `hAQ_lat : IsLat R (AA.carrier.comap (pullQ (R` using `R) K)) := by`.

Rewrite using `[eQ]`. Conclude with `hPd.1`. Use `⟨⟨⟨AA.carrier.map (resK (R := R) K), hAK_lat, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩, ⟨⟨AA.carrier.comap (pullQ (R := R) K), hAQ_lat, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩, e3, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Conclude with `fun k => AA.le_int hf k`.

Conclude with `⟨1, AA.one_mem, rfl⟩`. Introduce and unpack `_ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩`. Conclude with `⟨f * g, AA.mul_mem f g hf hg, rfl⟩`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Establish `hm` using `SecondCohomologyLattice.map_tensorSpan (C := C) (R := R) (fun k : K => (k : N)) AA.carrier`.

Establish `hmem` using `Submodule.mem_map_of_mem (f := LinearMap.funLeft R C (Prod.map (fun k : K => (k : N)) (fun k : K => (k : N)))) (AA.comul f hf)`. Rewrite `hmem` using `[hm]`. Conclude with `hmem`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Conclude with `⟨fun y => f (-y), AA.antipode f hf, rfl⟩`.

Introduce `g hg q`. Establish `hg' : pullQ (R` using `R) K g ∈ AA.carrier := hg`. Take `⟨r, hr⟩` from `AA.le_int hg' (s q)`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`.

Use `show g ((s q : N) : N ⧸ K) = g q`. Rewrite using `[hs q]`. Use `show pullQ (R := R) K 1 ∈ AA.carrier`. Conclude with `AA.one_mem`. Introduce `f g hf hg`.

Conclude with `AA.mul_mem (pullQ (R := R) K f) (pullQ (R := R) K g) hf hg`. Introduce `g hg`. Establish `hg' : pullQ (R` using `R) K g ∈ AA.carrier := hg`. Rewrite using `[eQ]`. Apply `tensor_of_pair_lemma_7 _ hPd.1` to reduce the goal to its premises.

Rewrite using `[hPd.2]`. Introduce and unpack `_ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩`. Take `⟨r, hr⟩` from `tensor_pair_lemma_6 AA.carrier x y hx hy _ (AA.comul _ hg')`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`.

Use `symm`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Use `show g (c + d) * _ * _ = _`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ c, pushQ (R := R) K x c * ∑ b, y b * g (c + (b : N ⧸ K)) := by`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[sum_pushQ (R := R) K y (fun d => g (c + d))]`.

Use `_ = ∑ a, x a * ∑ b, y b * g ((a : N ⧸ K) + (b : N ⧸ K)) := sum_pushQ (R := R) K x (fun c => ∑ b, y b * g (c + (b : N ⧸ K)))`. Use `_ = ∑ a, ∑ b, addPull R N (pullQ (R := R) K g) (a, b) * x a * y b := by`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Use `show _ = g (((a + b : N)) : N ⧸ K) * x a * y b`. Rewrite using `[QuotientAddGroup.mk_add]`. Expand and normalize the polynomial expressions, which then agree. Introduce `g hg`. Establish `h` using `AA.antipode (pullQ (R := R) K g) hg`.

Establish `e : (fun x : N => pullQ (R` using `R) K g (-x)) = pullQ (R := R) K (fun y : N ⧸ K => g (-y)) := by`. Use function extensionality and compare the values at `x`. Use `show g ((-x : N) : N ⧸ K) = g (-((x : N ⧸ K)))`. Rewrite using `[QuotientAddGroup.mk_neg]`. Rewrite `h` using `[e]`.

Conclude with `h`. Rewrite using `[eQ]`. Conclude with `hPd.2`.
-/
theorem h2 (C R : Type) [Field C] [CommRing R] [Algebra R C] :
    SubgroupQuotientStatement (C := C) (R := R) := by
  intro v hv N _ _ _ K _ _ _ AA
  have hdual := dual_isLat_lemma_4 AA.carrier AA.lat
  have e3 : dualLat (AA.carrier.map (resK (R := R) K)) =
      (dualLat AA.carrier).comap (extK K) := by
    ext u
    rw [Submodule.mem_comap, mem_dualLat, mem_dualLat]
    constructor
    · intro hu f hf
      rw [sum_extK (R := R) K u f]
      exact hu _ (Submodule.mem_map_of_mem hf)
    · rintro hu _ ⟨f, hf, rfl⟩
      have h := hu f hf
      rw [sum_extK (R := R) K u f] at h
      exact h
  have hres_surj : Function.Surjective (resK (R := C) (C := C) K) := by
    intro u
    refine ⟨extK (R := C) (C := C) K u, ?_⟩
    funext k
    show (if h : (k : N) ∈ K then u ⟨k, h⟩ else 0) = u k
    rw [dif_pos k.2]
  have hAK_lat : IsLat R (AA.carrier.map (resK (R := R) K)) :=
    isLat_map_lemma_5 v hv AA.carrier AA.lat (resK (R := C) (C := C) K) hres_surj
      (resK (R := R) K) (fun _ => rfl)
  have hs : ∀ q : N ⧸ K, ∃ a : N, (a : N ⧸ K) = q := fun q => QuotientAddGroup.mk_surjective q
  choose s hs using hs
  have hpush_surj : Function.Surjective (pushQ (R := C) (C := C) K) := by
    intro t
    refine ⟨fun a => if a = s (a : N ⧸ K) then t (a : N ⧸ K) else 0, ?_⟩
    funext c
    show ∑ a ∈ Finset.univ.filter (fun a : N => (a : N ⧸ K) = c),
      (if a = s (a : N ⧸ K) then t (a : N ⧸ K) else 0) = t c
    rw [Finset.sum_eq_single (s c)]
    · rw [hs c, if_pos rfl]
    · intro b hb hne
      rw [(Finset.mem_filter.1 hb).2, if_neg hne]
    · intro h
      exact (h (Finset.mem_filter.2 ⟨Finset.mem_univ _, hs c⟩)).elim
  have hP_lat : IsLat R ((dualLat AA.carrier).map (pushQ (R := R) K)) :=
    isLat_map_lemma_5 v hv (dualLat AA.carrier) hdual.1 (pushQ (R := C) (C := C) K) hpush_surj
      (pushQ (R := R) K) (fun _ => rfl)
  have hPd := dual_isLat_lemma_4 _ hP_lat
  have eQ : AA.carrier.comap (pullQ (R := R) K) =
      dualLat ((dualLat AA.carrier).map (pushQ (R := R) K)) := by
    ext g
    rw [Submodule.mem_comap]
    constructor
    · intro hg
      rw [mem_dualLat]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨r, hr⟩ := (mem_dualLat _ _).1 hw _ hg
      refine ⟨r, ?_⟩
      rw [hr]
      calc ∑ a, w a * pullQ (R := R) K g a = ∑ a, w a * g (a : N ⧸ K) := rfl
        _ = ∑ c, pushQ (R := R) K w c * g c := (sum_pushQ (R := R) K w g).symm
        _ = ∑ c, g c * pushQ (R := R) K w c := Finset.sum_congr rfl fun c _ => mul_comm _ _
    · intro hg
      rw [← hdual.2, mem_dualLat]
      intro w hw
      rw [mem_dualLat] at hg
      obtain ⟨r, hr⟩ := hg _ (Submodule.mem_map_of_mem hw)
      refine ⟨r, ?_⟩
      rw [hr]
      calc ∑ c, g c * pushQ (R := R) K w c = ∑ c, pushQ (R := R) K w c * g c :=
            Finset.sum_congr rfl fun c _ => mul_comm _ _
        _ = ∑ a, w a * g (a : N ⧸ K) := sum_pushQ (R := R) K w g
        _ = ∑ a, pullQ (R := R) K g a * w a := Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hAQ_lat : IsLat R (AA.carrier.comap (pullQ (R := R) K)) := by
    rw [eQ]
    exact hPd.1
  refine ⟨⟨⟨AA.carrier.map (resK (R := R) K), hAK_lat, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩,
    ⟨⟨AA.carrier.comap (pullQ (R := R) K), hAQ_lat, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩, e3, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact fun k => AA.le_int hf k
  · exact ⟨1, AA.one_mem, rfl⟩
  · rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, AA.mul_mem f g hf hg, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    have hm := SecondCohomologyLattice.map_tensorSpan (C := C) (R := R) (fun k : K => (k : N)) AA.carrier
    have hmem := Submodule.mem_map_of_mem
      (f := LinearMap.funLeft R C (Prod.map (fun k : K => (k : N)) (fun k : K => (k : N))))
      (AA.comul f hf)
    rw [hm] at hmem
    exact hmem
  · rintro _ ⟨f, hf, rfl⟩
    exact ⟨fun y => f (-y), AA.antipode f hf, rfl⟩
  · intro g hg q
    have hg' : pullQ (R := R) K g ∈ AA.carrier := hg
    obtain ⟨r, hr⟩ := AA.le_int hg' (s q)
    refine ⟨r, ?_⟩
    rw [hr]
    show g ((s q : N) : N ⧸ K) = g q
    rw [hs q]
  · show pullQ (R := R) K 1 ∈ AA.carrier
    exact AA.one_mem
  · intro f g hf hg
    exact AA.mul_mem (pullQ (R := R) K f) (pullQ (R := R) K g) hf hg
  · intro g hg
    have hg' : pullQ (R := R) K g ∈ AA.carrier := hg
    rw [eQ]
    apply tensor_of_pair_lemma_7 _ hPd.1
    rw [hPd.2]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨r, hr⟩ := tensor_pair_lemma_6 AA.carrier x y hx hy _ (AA.comul _ hg')
    refine ⟨r, ?_⟩
    rw [hr]
    symm
    calc ∑ c, ∑ d, addPull R (N ⧸ K) g (c, d) * pushQ (R := R) K x c * pushQ (R := R) K y d
        = ∑ c, pushQ (R := R) K x c * ∑ d, pushQ (R := R) K y d * g (c + d) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          show g (c + d) * _ * _ = _
          ring
      _ = ∑ c, pushQ (R := R) K x c * ∑ b, y b * g (c + (b : N ⧸ K)) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [sum_pushQ (R := R) K y (fun d => g (c + d))]
      _ = ∑ a, x a * ∑ b, y b * g ((a : N ⧸ K) + (b : N ⧸ K)) :=
          sum_pushQ (R := R) K x (fun c => ∑ b, y b * g (c + (b : N ⧸ K)))
      _ = ∑ a, ∑ b, addPull R N (pullQ (R := R) K g) (a, b) * x a * y b := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          show _ = g (((a + b : N)) : N ⧸ K) * x a * y b
          rw [QuotientAddGroup.mk_add]
          ring
  · intro g hg
    have h := AA.antipode (pullQ (R := R) K g) hg
    have e : (fun x : N => pullQ (R := R) K g (-x)) =
        pullQ (R := R) K (fun y : N ⧸ K => g (-y)) := by
      funext x
      show g ((-x : N) : N ⧸ K) = g (-((x : N ⧸ K)))
      rw [QuotientAddGroup.mk_neg]
    rw [e] at h
    exact h
  · rw [eQ]
    exact hPd.2

end ReciprocityTheory.PGsh.L2
