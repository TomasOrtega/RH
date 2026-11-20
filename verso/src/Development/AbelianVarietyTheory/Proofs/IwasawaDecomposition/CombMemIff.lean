import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncreasingRowChoicePerColumn

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylCombInt

open Formalism.L2.DIV

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem weyl_eq (N : ℕ) (ν : Fin N → ℕ) :
    Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν = WeylLatticeDuality.weyl ℤ N N le_rfl ν := rfl

/- English proof (translation)
Unfold `ten`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [Formalism.GradedWeylDivisibility.blockEmb, eval_rename]`. Both sides reduce to the same expression.
-/
theorem eval_ten {K Lt : Type} [Field K] [Fintype Lt] {N : ℕ} (f : Lt → MvPolynomial (Fin N × Fin N) K)
    (z : Lt × Fin N × Fin N → K) : eval z (ten f) = ∏ s, eval (fun v => z (s, v)) (f s) := by
  unfold ten
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [Formalism.GradedWeylDivisibility.blockEmb, eval_rename]
  rfl

/- English proof (translation)
Rewrite using `[GlobalTheory.WeylMinorDual.fockB_ten]`. Simplify using `only [GlobalTheory.WeylMinorDual.fockB_map, hbg]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Take `⟨s, hs⟩` from `Function.ne_iff.mp h`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])`.
-/
theorem fockB_ten_dual {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {K : Type} [Field K] [CharZero K]
    (ι : Lt → Type) [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (Nc : Lt → ℚ)
    (hbg : ∀ s i k, Formalism.GradedWeylDivisibility.fockQ (b s i) (g s k) = if i = k then Nc s else 0) (κ' κ : ∀ s, ι s) :
    fockB (ten fun s => map (algebraMap ℚ K) (b s (κ' s))) (ten fun s => map (algebraMap ℚ K) (g s (κ s))) =
      if κ' = κ then ∏ s, (Nc s : K) else 0 := by
  rw [GlobalTheory.WeylMinorDual.fockB_ten]
  simp only [GlobalTheory.WeylMinorDual.fockB_map, hbg]
  split_ifs with h
  · subst h; simp
  · obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

/- English proof (translation)
Use `set E := Equiv.ofBijective e he with hE`. Use `set P : (∀ s, ι s) → MvPolynomial (Lt × Fin N × Fin N) ℂ_[p] := fun κ => ten fun s => map (algebraMap ℚ ℂ_[p]) (g s (κ s)) with hP`. Establish `h0 : ∑ κ, c κ • P κ = 0`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `z`.

Establish `hz` using `h (fun τ => Matrix.of fun i j => z (E.symm τ, i, j))`. Rewrite using `[map_zero, map_sum]`. Rewrite using `[← hz]`. Use `Finset.sum_congr rfl fun κ _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eval, hP]`.

Simplify using `only [eval_ten]`. Use `congr 1`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `hs : E.symm (e s) = s`. Rewrite using `[← Equiv.ofBijective_apply e he]`.

Conclude with `E.symm_apply_apply s`. Simplify using `only [Matrix.of_apply, hs]`. Use function extensionality and compare the values at `κ'`. Establish `h1` using `congrArg (fockB (ten fun s => map (algebraMap ℚ ℂ_[p]) (b s (κ' s)))) h0`. Rewrite `h1` using `[← fockBL_apply, ← fockBL_apply, map_sum, map_zero]`.

Simplify using `only [map_smul, fockBL_apply, hP, fockB_ten_dual ι b g Nc hbg, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1`. Establish `hne : ∏ s, (Nc s : ℂ_[p]) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun s _ => by exact_mod_cast hNc s`. Simplify `h1` using `[hne]`.
-/
theorem coeff_unique (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T]
    (e : Lt → T) (he : Function.Bijective e) (N : ℕ) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    [∀ s, DecidableEq (ι s)] (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (Nc : Lt → ℚ)
    (hNc : ∀ s, Nc s ≠ 0) (hbg : ∀ s i k, Formalism.GradedWeylDivisibility.fockQ (b s i) (g s k) = if i = k then Nc s else 0)
    (c : (∀ s, ι s) → ℂ_[p])
    (h : ∀ y : T → Matrix (Fin N) (Fin N) ℂ_[p], ∑ κ, c κ * ∏ s, MvPolynomial.eval
      (fun k : Fin N × Fin N => y (e s) k.1 k.2) (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) = 0) :
    c = 0 := by
  set E := Equiv.ofBijective e he with hE
  set P : (∀ s, ι s) → MvPolynomial (Lt × Fin N × Fin N) ℂ_[p] :=
    fun κ => ten fun s => map (algebraMap ℚ ℂ_[p]) (g s (κ s)) with hP
  have h0 : ∑ κ, c κ • P κ = 0 := by
    apply MvPolynomial.funext
    intro z
    have hz := h (fun τ => Matrix.of fun i j => z (E.symm τ, i, j))
    rw [map_zero, map_sum]
    rw [← hz]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [smul_eval, hP]
    simp only [eval_ten]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    have hs : E.symm (e s) = s := by
      rw [← Equiv.ofBijective_apply e he]; exact E.symm_apply_apply s
    simp only [Matrix.of_apply, hs]
  funext κ'
  have h1 := congrArg (fockB (ten fun s => map (algebraMap ℚ ℂ_[p]) (b s (κ' s)))) h0
  rw [← fockBL_apply, ← fockBL_apply, map_sum, map_zero] at h1
  simp only [map_smul, fockBL_apply, hP, fockB_ten_dual ι b g Nc hbg, smul_eq_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  have hne : ∏ s, (Nc s : ℂ_[p]) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s _ => by exact_mod_cast hNc s
  simpa [hne] using h1

/- English proof (translation)
Establish `: Formalism.GradedWeylDivisibility.intQ N N w = map (Int.castRingHom ℚ) w` using `rfl`. Rewrite using `[this, map_map, show (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ_[p] from RingHom.ext_int _ _]`.
-/
theorem map_intQ (p : ℕ) [Fact p.Prime] (N : ℕ) (w : MvPolynomial (Fin N × Fin N) ℤ) :
    map (algebraMap ℚ ℂ_[p]) (Formalism.GradedWeylDivisibility.intQ N N w) = map (Int.castRingHom ℂ_[p]) w := by
  have : Formalism.GradedWeylDivisibility.intQ N N w = map (Int.castRingHom ℚ) w := rfl
  rw [this, map_map, show (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ_[p] from
    RingHom.ext_int _ _]

/- English proof (translation)
Introduce `p _ Lt T _ _ _ e he N ν ι _ _ b g Nc hNc hbg hspan a`. Use `set E := Equiv.ofBijective e he with hE`. Establish `hs : ∀ s, E.symm (e s) = s` using `fun s => by`. Rewrite using `[← Equiv.ofBijective_apply e he]`. Conclude with `E.symm_apply_apply s`.

Use `set G : (∀ s, ι s) → (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p] := fun κ y => ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2) (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) with hG`. Prove the components needed by the constructor for the conclusion. Introduce `hmem`. Set `S : AddSubgroup ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p])` to `{ carrier := {F | ∃ a' : (∀ s, ι s) → ℂ_[p], (∀ κ, ‖a' κ‖ ≤ 1) ∧ F = fun y => ∑ κ, a' κ * G κ y} zero_mem' := ⟨0, fun _ => by simp, by funext y; simp⟩ add_mem' := by`. Introduce and unpack `F F' ⟨a1, h1, rfl⟩ ⟨a2, h2, rfl⟩`.

Use `⟨a1 + a2, fun κ => ?_, ?_⟩` and prove the remaining obligations. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 κ) (h2 κ))`. Use function extensionality and compare the values at `y`. Simplify using `[add_mul, Finset.sum_add_distrib]`. Use the proof step `neg_mem' := by`.

Introduce and unpack `F ⟨a1, h1, rfl⟩`. Use `⟨-a1, fun κ => by simpa using h1 κ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Simplify using `[neg_mul, Finset.sum_neg_distrib] }`. Establish `hle : WeylLatticeDuality.DelW p T N ν ≤ S`.

Unfold `WeylLatticeDuality.DelW`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `F ⟨r, f, hr, hf, rfl⟩`. Establish `hn : ∀ s, ∃ n : ι s → ℤ, ∑ k, n k • g s k = Formalism.GradedWeylDivisibility.intQ N N (f (e s))`. Introduce `s`.

Rewrite using `[← Submodule.mem_span_range_iff_exists_fun, hspan s, weyl_eq]`. Conclude with `Submodule.mem_map_of_mem (hf (e s))`. Use `choose n hn using hn`. Use `⟨fun κ => r * ∏ s, ((n s (κ s) : ℤ) : ℂ_[p]), fun κ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, norm_prod]`.

Conclude with `mul_le_one₀ hr (by positivity) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun s _ => IsUltrametricDist.norm_intCast_le_one _ _)`. Use function extensionality and compare the values at `y`. Rewrite using `[← he.prod_comp]`. Establish `hterm : ∀ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f (e s))) = ∑ k, ((n s k : ℤ) : ℂ_[p]) * MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2) (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s k))`. Introduce `s`.

Rewrite using `[← map_intQ, ← hn s, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, map_zsmul, zsmul_eq_mul]`. Simplify using `only [hterm, Fintype.prod_sum, Finset.mul_sum, hG]`. Use `Finset.sum_congr rfl fun κ _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨a', ha', heq⟩` from `hle hmem`. Establish `hc` using `coeff_unique p Lt T e he N ι b g Nc hNc hbg (a - a') (fun y => by`. Use `congrFun heq y` as an intermediate fact.

Simplify using `only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[sub_eq_zero]`. Conclude with `this)`. Establish `: a = a'` using `sub_eq_zero.mp hc`. Substitute `this` using the available equality.

Conclude with `ha'`. Introduce `ha`. Establish `hw : ∀ s k, ∃ w ∈ WeylLatticeDuality.weyl ℤ N N le_rfl (ν (e s)), Formalism.GradedWeylDivisibility.intQ N N w = g s k`. Introduce `s k`. Establish `: g s k ∈ Submodule.span ℤ (Set.range (g s))` using `Submodule.subset_span (Set.mem_range_self k)`.

Rewrite `this` using `[hspan s, weyl_eq]`. Conclude with `this`. Use `choose w hw hwg using hw`. Establish `hfun : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ * G κ y) = ∑ κ : (∀ s, ι s), fun y => a κ * G κ y`. Use function extensionality and compare the values at `y`.

Simplify using `[Finset.sum_apply]`. Use `show (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ * G κ y) ∈ _`. Rewrite using `[hfun]`. Use `AddSubgroup.sum_mem _ fun κ _ => AddSubgroup.subset_closure ?_` and prove the remaining obligations. Use `⟨a κ, fun τ => w (E.symm τ) (κ (E.symm τ)), ha κ, fun τ => ?_, ?_⟩` and prove the remaining obligations.

Use `hw (E.symm τ) (κ (E.symm τ))` as an intermediate fact. Rewrite `this` using `[show e (E.symm τ) = τ from E.apply_symm_apply τ]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `y`. Use `congr 1`. Rewrite using `[← he.prod_comp]`.

Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hs s, ← hwg s (κ s), map_intQ]`.
-/
theorem comb_mem_iff : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T), Function.Bijective e →
    ∀ (N : ℕ) (ν : T → Fin N → ℕ) (ι : Lt → Type) [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (Nc : Lt → ℚ), (∀ s, Nc s ≠ 0) →
    (∀ s i k, Formalism.GradedWeylDivisibility.fockQ (b s i) (g s k) = if i = k then Nc s else 0) →
    (∀ s, Submodule.span ℤ (Set.range (g s)) =
      (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (ν (e s))).map (Formalism.GradedWeylDivisibility.intQ N N)) →
    ∀ a : (∀ s, ι s) → ℂ_[p],
      ((fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s)))) ∈ WeylLatticeDuality.DelW p T N ν ↔
        ∀ κ, ‖a κ‖ ≤ 1) := by
  intro p _ Lt T _ _ _ e he N ν ι _ _ b g Nc hNc hbg hspan a
  set E := Equiv.ofBijective e he with hE
  have hs : ∀ s, E.symm (e s) = s := fun s => by
    rw [← Equiv.ofBijective_apply e he]; exact E.symm_apply_apply s
  set G : (∀ s, ι s) → (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p] := fun κ y =>
    ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
      (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) with hG
  constructor
  · intro hmem
    let S : AddSubgroup ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) :=
      { carrier := {F | ∃ a' : (∀ s, ι s) → ℂ_[p], (∀ κ, ‖a' κ‖ ≤ 1) ∧ F = fun y => ∑ κ, a' κ * G κ y}
        zero_mem' := ⟨0, fun _ => by simp, by funext y; simp⟩
        add_mem' := by
          rintro F F' ⟨a1, h1, rfl⟩ ⟨a2, h2, rfl⟩
          refine ⟨a1 + a2, fun κ => ?_, ?_⟩
          · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 κ) (h2 κ))
          · funext y; simp [add_mul, Finset.sum_add_distrib]
        neg_mem' := by
          rintro F ⟨a1, h1, rfl⟩
          refine ⟨-a1, fun κ => by simpa using h1 κ, ?_⟩
          funext y; simp [neg_mul, Finset.sum_neg_distrib] }
    have hle : WeylLatticeDuality.DelW p T N ν ≤ S := by
      unfold WeylLatticeDuality.DelW
      rw [AddSubgroup.closure_le]
      rintro F ⟨r, f, hr, hf, rfl⟩
      have hn : ∀ s, ∃ n : ι s → ℤ, ∑ k, n k • g s k = Formalism.GradedWeylDivisibility.intQ N N (f (e s)) := by
        intro s
        rw [← Submodule.mem_span_range_iff_exists_fun, hspan s, weyl_eq]
        exact Submodule.mem_map_of_mem (hf (e s))
      choose n hn using hn
      refine ⟨fun κ => r * ∏ s, ((n s (κ s) : ℤ) : ℂ_[p]), fun κ => ?_, ?_⟩
      · rw [norm_mul, norm_prod]
        exact mul_le_one₀ hr (by positivity)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun s _ => IsUltrametricDist.norm_intCast_le_one _ _)
      · funext y
        rw [← he.prod_comp]
        have hterm : ∀ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f (e s))) =
            ∑ k, ((n s k : ℤ) : ℂ_[p]) * MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
              (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s k)) := by
          intro s
          rw [← map_intQ, ← hn s, map_sum, map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_zsmul, map_zsmul, zsmul_eq_mul]
        simp only [hterm, Fintype.prod_sum, Finset.mul_sum, hG]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    obtain ⟨a', ha', heq⟩ := hle hmem
    have hc := coeff_unique p Lt T e he N ι b g Nc hNc hbg (a - a') (fun y => by
      have := congrFun heq y
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]; exact this)
    have : a = a' := sub_eq_zero.mp hc
    subst this; exact ha'
  · intro ha
    have hw : ∀ s k, ∃ w ∈ WeylLatticeDuality.weyl ℤ N N le_rfl (ν (e s)), Formalism.GradedWeylDivisibility.intQ N N w = g s k := by
      intro s k
      have : g s k ∈ Submodule.span ℤ (Set.range (g s)) := Submodule.subset_span (Set.mem_range_self k)
      rw [hspan s, weyl_eq] at this
      exact this
    choose w hw hwg using hw
    have hfun : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ * G κ y) =
        ∑ κ : (∀ s, ι s), fun y => a κ * G κ y := by
      funext y; simp [Finset.sum_apply]
    show (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ * G κ y) ∈ _
    rw [hfun]
    refine AddSubgroup.sum_mem _ fun κ _ => AddSubgroup.subset_closure ?_
    refine ⟨a κ, fun τ => w (E.symm τ) (κ (E.symm τ)), ha κ, fun τ => ?_, ?_⟩
    · have := hw (E.symm τ) (κ (E.symm τ))
      rwa [show e (E.symm τ) = τ from E.apply_symm_apply τ] at this
    · funext y
      congr 1
      rw [← he.prod_comp]
      refine Finset.prod_congr rfl fun s _ => ?_
      dsimp only
      rw [hs s, ← hwg s (κ s), map_intQ]

end GlobalTheory.WeylCombInt
