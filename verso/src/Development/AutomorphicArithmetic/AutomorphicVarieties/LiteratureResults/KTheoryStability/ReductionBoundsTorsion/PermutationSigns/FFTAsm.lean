import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PStab

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.BlockInvariants

namespace FourierAssembly

variable {L : Type} [Field L] [NumberField L] {N q : ℕ}

/- English proof (translation)
Rewrite using `[← Finset.sum_filter]`. Use `symm`. Use `Finset.sum_nbij' (fun a i => (w i, a i)) (fun I i => (I i).2) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a _`. Simplify using `[hP]`.

Introduce `I _`. Simplify using the standard rewrite rules. Introduce `a _`. Both sides reduce to the same expression. Introduce `I hI`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, hP] at hI`. Use function extensionality and compare the values at `i`. Conclude with `Prod.ext (hI i).symm rfl`. Introduce `a _`. Both sides reduce to the same expression.
-/
theorem sum_place {W : Type} {N q : ℕ} (w : Fin q → W)
    (P : (Fin q → Ix W N) → Prop) [DecidablePred P] (hP : ∀ I, P I ↔ ∀ i, (I i).1 = w i)
    (g : (Fin q → Ix W N) → ℂ) [Fintype W] :
    ∑ I : Fin q → Ix W N, (if P I then g I else 0) = ∑ a : Fin q → Fin N, g (fun i => (w i, a i)) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun a i => (w i, a i)) (fun I i => (I i).2) ?_ ?_ ?_ ?_ ?_
  · intro a _
    simp [hP]
  · intro I _
    simp
  · intro a _
    rfl
  · intro I hI
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP] at hI
    funext i
    exact Prod.ext (hI i).symm rfl
  · intro a _
    rfl

open Classical in

def fTL (Y : Fin q → HS L N) :
    Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ →ₗ[ℂ] ℂ where
  toFun T := fT T Y
  map_add' T T' := by
    simp only [fT, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a T := by
    simp only [fT, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, RingHom.id_apply]

open Classical in
/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem fT_sum {ι : Type} [Fintype ι] (c : ι → ℂ)
    (M : ι → Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ)
    (Y : Fin q → HS L N) : fT (∑ p, c p • M p) Y = ∑ p, c p * fT (M p) Y := by
  calc fT (∑ p, c p • M p) Y = fTL Y (∑ p, c p • M p) := rfl
    _ = ∑ p, fTL Y (c p • M p) := map_sum _ _ _
    _ = ∑ p, c p * fT (M p) Y := by simp only [map_smul, smul_eq_mul]; rfl

open Classical in
/- English proof (translation)
Unfold `fT perm' tmC`. Simplify using `only [Matrix.of_apply, ite_mul, one_mul, zero_mul]`. Establish `hin : ∀ x : Fin q → Ix (InfinitePlace L) N, (∑ J : Fin q → Ix (InfinitePlace L) N, if (∀ i, (x i).1 = w i) ∧ J = x ∘ σ then ∏ i, blk (fun v => mat (Y i) v) (x i) (J i) else 0) = if (∀ i, (x i).1 = w i) then ∏ i, blk (fun v => mat (Y i) v) (x i) (x (σ i)) else 0`. Introduce `x`. Distinguish the cases in `h : ∀ i, (x i).1 = w i`.

Rewrite using `[if_pos h, Finset.sum_eq_single (x ∘ σ)]`. Rewrite using `[if_pos ⟨h, rfl⟩]`. Both sides reduce to the same expression. Introduce `J _ hJ`. Rewrite using `[if_neg (fun hh => hJ hh.2)]`.

Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`. Simplify using `[h]`. Rewrite using `[Finset.sum_congr rfl (fun x _ => hin x)]`. Rewrite using `[sum_place w _ (fun _ => Iff.rfl)]`.

Distinguish the cases in `hw : ∀ i, w (σ i) = w i`. Rewrite using `[if_pos hw]`. Simplify using `[ContinuousMultilinearMap.sum_apply, blk, ent, hw]`. Both sides reduce to the same expression. Rewrite `hw` using `[if_neg hw] push_neg`.

Take `⟨i, hi⟩` from `hw`. Simplify using `only [ContinuousMultilinearMap.zero_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`. Apply `Finset.prod_eq_zero (Finset.mem_univ i)` to reduce the goal to its premises.

Simplify using `[blk, Ne.symm hi]`.
-/
theorem fT_perm' (σ : Equiv.Perm (Fin q)) (w : Fin q → InfinitePlace L) (Y : Fin q → HS L N) :
    fT (perm' (m := N) σ w) Y = tmC σ w Y := by
  unfold fT perm' tmC
  simp only [Matrix.of_apply, ite_mul, one_mul, zero_mul]
  have hin : ∀ x : Fin q → Ix (InfinitePlace L) N,
      (∑ J : Fin q → Ix (InfinitePlace L) N,
        if (∀ i, (x i).1 = w i) ∧ J = x ∘ σ then
          ∏ i, blk (fun v => mat (Y i) v) (x i) (J i) else 0) =
      if (∀ i, (x i).1 = w i) then ∏ i, blk (fun v => mat (Y i) v) (x i) (x (σ i)) else 0 := by
    intro x
    by_cases h : ∀ i, (x i).1 = w i
    · rw [if_pos h, Finset.sum_eq_single (x ∘ σ)]
      · rw [if_pos ⟨h, rfl⟩]
        rfl
      · intro J _ hJ
        rw [if_neg (fun hh => hJ hh.2)]
      · intro hh
        exact absurd (Finset.mem_univ _) hh
    · simp [h]
  rw [Finset.sum_congr rfl (fun x _ => hin x)]
  rw [sum_place w _ (fun _ => Iff.rfl)]
  by_cases hw : ∀ i, w (σ i) = w i
  · rw [if_pos hw]
    simp [ContinuousMultilinearMap.sum_apply, blk, ent, hw]
    rfl
  · rw [if_neg hw]
    push_neg at hw
    obtain ⟨i, hi⟩ := hw
    simp only [ContinuousMultilinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [blk, Ne.symm hi]

/- English proof (translation)
Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]`.
-/
theorem sign_sq_one (π : Equiv.Perm (Fin q)) :
    ((Equiv.Perm.sign π : ℤ) : ℝ) * ((Equiv.Perm.sign π : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]

end FourierAssembly

open FourierAssembly in
open Classical in
/- English proof (translation)
Introduce `L _ _ N q β hβ`. Take `⟨T, hT, hTc⟩` from `hC L N q β.toContinuousMultilinearMap (by`. Introduce `u hu Y`. Use `congrArg (fun g => g Y) (hβ u hu)` as an intermediate fact. Simplify `this)` using `[Function.comp_def]`.

Establish `hTs : T ∈ Submodule.span ℂ (Set.range fun p : Equiv.Perm (Fin q) × (Fin q → InfinitePlace L) => perm' (m` using `N) p.1 p.2) := by`. Apply `h1 (InfinitePlace L) N q T` to reduce the goal to its premises. Introduce `Z hZ`. Establish `hZs` using `h2 (InfinitePlace L) N q Z hZ`. Use `clear hZ`.

Proceed by induction on `hZs using Submodule.span_induction with`. Consider the case `mem M hM`. Take `⟨d, hd, rfl⟩` from `hM`. Conclude with `(hTc d hd).symm`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [mul_add, add_mul, hx, hy]`. Consider the case `smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc, hx]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 hTs`. Establish `hf : ∀ Z, β Z = ∑ p : Equiv.Perm (Fin q) × (Fin q → InfinitePlace L), ((c p).re * tmR p.1 p.2 false Z - (c p).im * tmR p.1 p.2 true Z)`. Introduce `Z`.

Use `hT Z` as an intermediate fact. Rewrite `this` using `[← hc, fT_sum]`. Simplify using `only [fT_perm'] at this`. Rewrite using `[show β Z = β.toContinuousMultilinearMap Z from rfl, this, Complex.re_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `p _`. Simplify using `[tmR, Complex.mul_re]`. Establish `hperm : ∀ Z, β Z = ((q.factorial : ℕ) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin q), ((Equiv.Perm.sign σ : ℤ) : ℝ) * β (Z ∘ σ)`. Introduce `Z`. Establish `hp : ∀ σ : Equiv.Perm (Fin q), β (Z ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * β Z`.

Introduce `σ`. Use `β.toAlternatingMap.map_perm Z σ` as an intermediate fact. Rewrite `this` using `[Units.smul_def, zsmul_eq_mul]`. Conclude with `this`. Simplify using `only [hp, ← mul_assoc, sign_sq_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Use `⟨fun x => if x.2.2 then -(c (x.1, x.2.1)).im / (q.factorial : ℝ) else (c (x.1, x.2.1)).re / (q.factorial : ℝ), ?_⟩` and prove the remaining obligations. Use extensionality with `Y`. Rewrite using `[hperm Y]`. Simplify using `only [hf, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, AT, ContinuousMultilinearMap.alternatization_apply_apply, Fintype.sum_prod_type, Fintype.sum_bool, smul_eq_mul, Units.smul_def, zsmul_eq_mul, ContinuousAlternatingMap.sum_apply, ContinuousAlternati …`.

Rewrite using `[Finset.mul_sum]`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fft_of (hC : Cplx) (h1 : PlacePermOperatorBicommutantSpan) (h2 : PlacePermOperatorCommutantSpan) : FFT := by
  intro L _ _ N q β hβ
  obtain ⟨T, hT, hTc⟩ := hC L N q β.toContinuousMultilinearMap (by
    intro u hu Y
    have := congrArg (fun g => g Y) (hβ u hu)
    simpa [Function.comp_def] using this)
  have hTs : T ∈ Submodule.span ℂ (Set.range fun p : Equiv.Perm (Fin q) × (Fin q → InfinitePlace L) =>
      perm' (m := N) p.1 p.2) := by
    apply h1 (InfinitePlace L) N q T
    intro Z hZ
    have hZs := h2 (InfinitePlace L) N q Z hZ
    clear hZ
    induction hZs using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨d, hd, rfl⟩ := hM
      exact (hTc d hd).symm
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, add_mul, hx, hy]
    | smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc, hx]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hTs
  have hf : ∀ Z, β Z = ∑ p : Equiv.Perm (Fin q) × (Fin q → InfinitePlace L),
      ((c p).re * tmR p.1 p.2 false Z - (c p).im * tmR p.1 p.2 true Z) := by
    intro Z
    have := hT Z
    rw [← hc, fT_sum] at this
    simp only [fT_perm'] at this
    rw [show β Z = β.toContinuousMultilinearMap Z from rfl, this, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro p _
    simp [tmR, Complex.mul_re]
  have hperm : ∀ Z, β Z = ((q.factorial : ℕ) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin q), ((Equiv.Perm.sign σ : ℤ) : ℝ) * β (Z ∘ σ) := by
    intro Z
    have hp : ∀ σ : Equiv.Perm (Fin q), β (Z ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * β Z := by
      intro σ
      have := β.toAlternatingMap.map_perm Z σ
      rw [Units.smul_def, zsmul_eq_mul] at this
      exact this
    simp only [hp, ← mul_assoc, sign_sq_one, one_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨fun x => if x.2.2 then -(c (x.1, x.2.1)).im / (q.factorial : ℝ)
    else (c (x.1, x.2.1)).re / (q.factorial : ℝ), ?_⟩
  ext Y
  rw [hperm Y]
  simp only [hf, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, AT,
    ContinuousMultilinearMap.alternatization_apply_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    smul_eq_mul, Units.smul_def, zsmul_eq_mul, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, if_true, Bool.false_eq_true,
    if_false]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  ring

end PositivityTheory.KB.BlockInvariants

end
