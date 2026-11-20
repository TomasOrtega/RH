import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftStratifiedSolutionSuccOfCoverStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top]`.
-/
theorem pow_smul_top_eq {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) :
    (I ^ n • (⊤ : Submodule A A)) = I ^ n := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv j)`.
-/
theorem mulVec_mem_of_mem {B : Type} [CommRing B] {d : ℕ} (E : Matrix (Fin d) (Fin d) B) (J : Ideal B)
    (v : Fin d → B) (hv : ∀ j, v j ∈ J) (i : Fin d) : E.mulVec v i ∈ J := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv j)

/- English proof (translation)
Set `res : (Fin d → A) → Fin d → B` to `fun w i => p (w i) - E.mulVec (fun j => q (w j)) i`. Establish `hres_sub : ∀ (w w' : Fin d → A) (i : Fin d), res w i - res w' i = p (w i - w' i) - E.mulVec (fun j => q (w j - w' j)) i`. Introduce `w w' i`. Establish `: (fun j => q (w j - w' j)) = (fun j => q (w j)) - (fun j => q (w' j))`. Use function extensionality and compare the values at `j`.

Simplify using the standard rewrite rules. Use `show p (w i) - E.mulVec (fun j => q (w j)) i - (p (w' i) - E.mulVec (fun j => q (w' j)) i) = _`. Rewrite using `[this, Matrix.mulVec_sub, Pi.sub_apply, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Establish `hseq : ∃ g : ℕ → (Fin d → A), g 0 = z ∧ (∀ k i, res (g k) i ∈ J ^ (k + 1)) ∧ ∀ k i, g (k + 1) i - g k i ∈ I ^ (k + 1)`.

Set `G : (k : ℕ) → {w : Fin d → A // ∀ i, res w i ∈ J ^ (k + 1)}` to `fun k => Nat.rec (motive := fun k => {w : Fin d → A // ∀ i, res w i ∈ J ^ (k + 1)}) ⟨z, hz⟩ (fun k w => ⟨Classical.choose (step (k + 1) w.1 w.2), (Classical.choose_spec (step (k + 1) w.1 w.2)).2⟩) k`. Use `⟨fun k => (G k).1, rfl, fun k => (G k).2, fun k i => ?_⟩` and prove the remaining obligations. Conclude with `(Classical.choose_spec (step (k + 1) (G k).1 (G k).2)).1 i`. Set `g` to `Classical.choose hseq`. Establish `hg0 : g 0 = z` using `(Classical.choose_spec hseq).1`.

Establish `hgres : ∀ k i, res (g k) i ∈ J ^ (k + 1)` using `(Classical.choose_spec hseq).2.1`. Establish `hgd : ∀ k i, g (k + 1) i - g k i ∈ I ^ (k + 1)` using `(Classical.choose_spec hseq).2.2`. Establish `hcau : ∀ i {m n : ℕ}, m ≤ n → g n i - g m i ∈ I ^ m`. Introduce `i m n hmn`. Proceed by induction on `n, hmn using Nat.le_induction with`.

Consider the case `base => simp`. Consider the case `succ n hmn ih`. Establish `h1 : g (n + 1) i - g n i ∈ I ^ m` using `Ideal.pow_le_pow_right (by omega) (hgd n i)`. Use `Ideal.add_mem _ h1 ih` as an intermediate fact. Simplify using `using this`.

Establish `hlim : ∀ i, ∃ L : A, ∀ n, g n i - L ∈ I ^ n`. Introduce `i`. Establish `h` using `@IsPrecomplete.prec' A _ I A _ _ hA (fun k => g k i) (fun {m n} hmn => by`. Rewrite using `[SModEq.sub_mem, pow_smul_top_eq]`. Use `hcau i hmn` as an intermediate fact.

Rewrite `this` using `[← neg_mem_iff, neg_sub]`. Conclude with `this)`. Use `⟨Classical.choose h, fun n => ?_⟩` and prove the remaining obligations. Use `Classical.choose_spec h n` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, pow_smul_top_eq]`.

Conclude with `this`. Set `z' : Fin d → A` to `fun i => Classical.choose (hlim i)`. Establish `hz' : ∀ i n, g n i - z' i ∈ I ^ n` using `fun i => Classical.choose_spec (hlim i)`. Use `⟨z', fun i => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : g 1 i - z' i ∈ I ^ 1` using `hz' i 1`.

Establish `h2 : g 1 i - g 0 i ∈ I ^ 1` using `hgd 0 i`. Rewrite `h2` using `[hg0]`. Use `Ideal.sub_mem _ h2 h1` as an intermediate fact. Simplify using `using this`. Use function extensionality and compare the values at `i`.

Rewrite using `[← sub_eq_zero]`. Use `hB.haus' _ fun k => ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero, pow_smul_top_eq]`. Establish `hd : res (g k) i - res z' i ∈ J ^ k`. Rewrite using `[hres_sub]`.

Use `Ideal.sub_mem _ (hp k (hz' i k)) ?_` and prove the remaining obligations. Conclude with `mulVec_mem_of_mem E _ _ (fun j => hq k (hz' j k)) i`. Establish `hr : res (g k) i ∈ J ^ k` using `Ideal.pow_le_pow_right (by omega) (hgres k i)`. Use `Ideal.sub_mem _ hr hd` as an intermediate fact. Simplify `this` using `[res]`.
-/
theorem lift_solution_of_step {A B : Type} [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    (hA : IsPrecomplete I A) (hB : IsHausdorff J B) {d : ℕ} (p q : A →+* B)
    (hp : ∀ m : ℕ, I ^ m ≤ (J ^ m).comap p) (hq : ∀ m : ℕ, I ^ m ≤ (J ^ m).comap q)
    (E : Matrix (Fin d) (Fin d) B)
    (step : ∀ (m : ℕ) (z : Fin d → A), (∀ i, p (z i) - E.mulVec (fun j => q (z j)) i ∈ J ^ m) →
      ∃ z' : Fin d → A, (∀ i, z' i - z i ∈ I ^ m) ∧
        ∀ i, p (z' i) - E.mulVec (fun j => q (z' j)) i ∈ J ^ (m + 1))
    (z : Fin d → A) (hz : ∀ i, p (z i) - E.mulVec (fun j => q (z j)) i ∈ J ^ 1) :
    ∃ z' : Fin d → A, (∀ i, z' i - z i ∈ I ^ 1) ∧
      (fun i => p (z' i)) = E.mulVec (fun j => q (z' j)) := by

  let res : (Fin d → A) → Fin d → B := fun w i => p (w i) - E.mulVec (fun j => q (w j)) i
  have hres_sub : ∀ (w w' : Fin d → A) (i : Fin d),
      res w i - res w' i = p (w i - w' i) - E.mulVec (fun j => q (w j - w' j)) i := by
    intro w w' i
    have : (fun j => q (w j - w' j)) = (fun j => q (w j)) - (fun j => q (w' j)) := by
      funext j; simp
    show p (w i) - E.mulVec (fun j => q (w j)) i - (p (w' i) - E.mulVec (fun j => q (w' j)) i) = _
    rw [this, Matrix.mulVec_sub, Pi.sub_apply, map_sub]
    ring

  have hseq : ∃ g : ℕ → (Fin d → A), g 0 = z ∧ (∀ k i, res (g k) i ∈ J ^ (k + 1)) ∧
      ∀ k i, g (k + 1) i - g k i ∈ I ^ (k + 1) := by
    let G : (k : ℕ) → {w : Fin d → A // ∀ i, res w i ∈ J ^ (k + 1)} := fun k =>
      Nat.rec (motive := fun k => {w : Fin d → A // ∀ i, res w i ∈ J ^ (k + 1)}) ⟨z, hz⟩
        (fun k w => ⟨Classical.choose (step (k + 1) w.1 w.2),
          (Classical.choose_spec (step (k + 1) w.1 w.2)).2⟩) k
    refine ⟨fun k => (G k).1, rfl, fun k => (G k).2, fun k i => ?_⟩
    exact (Classical.choose_spec (step (k + 1) (G k).1 (G k).2)).1 i
  let g := Classical.choose hseq
  have hg0 : g 0 = z := (Classical.choose_spec hseq).1
  have hgres : ∀ k i, res (g k) i ∈ J ^ (k + 1) := (Classical.choose_spec hseq).2.1
  have hgd : ∀ k i, g (k + 1) i - g k i ∈ I ^ (k + 1) := (Classical.choose_spec hseq).2.2

  have hcau : ∀ i {m n : ℕ}, m ≤ n → g n i - g m i ∈ I ^ m := by
    intro i m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : g (n + 1) i - g n i ∈ I ^ m :=
        Ideal.pow_le_pow_right (by omega) (hgd n i)
      have := Ideal.add_mem _ h1 ih
      simpa using this

  have hlim : ∀ i, ∃ L : A, ∀ n, g n i - L ∈ I ^ n := by
    intro i
    have h := @IsPrecomplete.prec' A _ I A _ _ hA (fun k => g k i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, pow_smul_top_eq]
      have := hcau i hmn
      rw [← neg_mem_iff, neg_sub] at this
      exact this)
    refine ⟨Classical.choose h, fun n => ?_⟩
    have := Classical.choose_spec h n
    rw [SModEq.sub_mem, pow_smul_top_eq] at this
    exact this
  let z' : Fin d → A := fun i => Classical.choose (hlim i)
  have hz' : ∀ i n, g n i - z' i ∈ I ^ n := fun i => Classical.choose_spec (hlim i)
  refine ⟨z', fun i => ?_, ?_⟩
  · have h1 : g 1 i - z' i ∈ I ^ 1 := hz' i 1
    have h2 : g 1 i - g 0 i ∈ I ^ 1 := hgd 0 i
    rw [hg0] at h2
    have := Ideal.sub_mem _ h2 h1
    simpa using this
  · funext i
    rw [← sub_eq_zero]
    refine hB.haus' _ fun k => ?_
    rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq]
    have hd : res (g k) i - res z' i ∈ J ^ k := by
      rw [hres_sub]
      refine Ideal.sub_mem _ (hp k (hz' i k)) ?_
      exact mulVec_mem_of_mem E _ _ (fun j => hq k (hz' j k)) i
    have hr : res (g k) i ∈ J ^ k := Ideal.pow_le_pow_right (by omega) (hgres k i)
    have := Ideal.sub_mem _ hr hd
    simpa [res] using this

/- English proof (translation)
The claim follows from `lift_solution_of_step (adI C) (adI D) C.complete.toIsPrecomplete D.complete.toIsHausdorff p.f q.f (adI_pow_le p) (adI_pow_le q) _ (GlobalTheory.T.lift_stratifiedSolution_succ_of_cover l K bk d S B C D h f p q hh hpo) z hz`.
-/
theorem lift_solution (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D) (hh : Cover h)
    (hpo : IsPO h h p q) (z : Fin d → C.A)
    (hz : ∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ 1) :
    ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ 1) ∧
      (fun i => p.f (z' i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) :=
  lift_solution_of_step (adI C) (adI D) C.complete.toIsPrecomplete D.complete.toIsHausdorff p.f q.f
    (adI_pow_le p) (adI_pow_le q) _ (GlobalTheory.T.lift_stratifiedSolution_succ_of_cover l K bk d S B C D h f p q hh hpo) z hz

end GlobalTheory.BSP
