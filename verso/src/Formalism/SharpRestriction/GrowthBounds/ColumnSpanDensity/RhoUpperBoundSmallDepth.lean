import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MapMDetUnit

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

section Fam

variable {p n' : ℕ} (R : RS p n') {k : ℕ}

abbrev RS.res : R.W →+* (R.W ⧸ Ideal.span {(p : R.W)}) := Ideal.Quotient.mk _

/- English proof (translation)
Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)`.
-/
theorem RS.res_p : R.res (p : R.W) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Establish `hp : IsLocalRing.maximalIdeal R.W = Ideal.span {(p : R.W)}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 R.std.1.p_unif`. Assume the negation of the conclusion as `hu`. Apply `h` to reduce the goal to its premises. Rewrite using `[RS.res, Ideal.Quotient.eq_zero_iff_mem, ← hp]`. Conclude with `(IsLocalRing.mem_maximalIdeal x).2 hu`.
-/
theorem RS.unit_of_res_ne {x : R.W} (h : R.res x ≠ 0) : IsUnit x := by
  have hp : IsLocalRing.maximalIdeal R.W = Ideal.span {(p : R.W)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 R.std.1.p_unif
  by_contra hu
  apply h
  rw [RS.res, Ideal.Quotient.eq_zero_iff_mem, ← hp]
  exact (IsLocalRing.mem_maximalIdeal x).2 hu

/- English proof (translation)
Establish `h1` using `Matrix.det_updateCol_sum (1 : Matrix (Fin k) (Fin k) A) j v`. Establish `e : (fun k' => ∑ i, v i • (1 : Matrix (Fin k) (Fin k) A) k' i) = v`. Use function extensionality and compare the values at `k'`. Simplify using `[Matrix.one_apply]`. Rewrite `h1` using `[e, Matrix.det_one, smul_eq_mul, mul_one]`.

Conclude with `h1`.
-/
theorem det_updateCol_one {A : Type*} [CommRing A] (j : Fin k) (v : Fin k → A) :
    ((1 : Matrix (Fin k) (Fin k) A).updateCol j v).det = v j := by
  have h1 := Matrix.det_updateCol_sum (1 : Matrix (Fin k) (Fin k) A) j v
  have e : (fun k' => ∑ i, v i • (1 : Matrix (Fin k) (Fin k) A) k' i) = v := by
    funext k'
    simp [Matrix.one_apply]
  rw [e, Matrix.det_one, smul_eq_mul, mul_one] at h1
  exact h1

/- English proof (translation)
Establish `h1` using `Matrix.det_updateRow_sum (1 : Matrix (Fin k) (Fin k) A) j v`. Establish `e : (∑ k', v k' • (1 : Matrix (Fin k) (Fin k) A) k') = v`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.one_apply]`. Rewrite `h1` using `[e, Matrix.det_one, smul_eq_mul, mul_one]`.

Conclude with `h1`.
-/
theorem det_updateRow_one {A : Type*} [CommRing A] (j : Fin k) (v : Fin k → A) :
    ((1 : Matrix (Fin k) (Fin k) A).updateRow j v).det = v j := by
  have h1 := Matrix.det_updateRow_sum (1 : Matrix (Fin k) (Fin k) A) j v
  have e : (∑ k', v k' • (1 : Matrix (Fin k) (Fin k) A) k') = v := by
    funext i
    simp [Matrix.one_apply]
  rw [e, Matrix.det_one, smul_eq_mul, mul_one] at h1
  exact h1

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h1` using `congrFun h i`. Use `haveI := R.std.1.frac_alt`. Conclude with `IsFractionRing.injective R.W R.Qq h1`.
-/
theorem emb_inj {w w' : Fin k → R.W} (h : (emb w : Fin k → R.Qq) = emb w') : w = w' := by
  funext i
  have h1 := congrFun h i
  haveI := R.std.1.frac_alt
  exact IsFractionRing.injective R.W R.Qq h1

/- English proof (translation)
Take `⟨j, hj⟩` from `Function.ne_iff.mp hv`. Use `choose vt hvt using fun i => Ideal.Quotient.mk_surjective (v i)`. Establish `hres : ∀ i, R.res (vt i) = v i` using `hvt`. Establish `hu : IsUnit (vt j)` using `R.unit_of_res_ne (by rw [hres]; exact hj)`. Set `V : Matrix (Fin k) (Fin k) R.W` to `(1 : Matrix (Fin k) (Fin k) R.W).updateCol j vt`.

Establish `hV : IsUnit V.det` using `by show IsUnit ((1 : Matrix (Fin k) (Fin k) R.W).updateCol j vt).det`. Rewrite using `[det_updateCol_one]`. Conclude with `hu`. Use `⟨_, edgeS R V hV j, rfl, vt, hres, ?_, ?_⟩` and prove the remaining obligations. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨j, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[V, mapM, dj, Matrix.mul_diagonal, Matrix.updateCol_apply]`. Apply the tactic sequence `try ring`. Introduce `x hx`.

Unfold `colSpan at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c0, rfl⟩` from `hx`. Distinguish the cases in `hc : c0 = j`.

Substitute `hc` using the available equality. Use `⟨1, 0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[V, mapM, dj, Matrix.mul_diagonal, Matrix.updateCol_apply]`. Apply the tactic sequence `try ring`.

Use `⟨0, fun i => (1 : Matrix (Fin k) (Fin k) R.W) i c0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[V, mapM, dj, Matrix.mul_diagonal, Matrix.updateCol_apply, hc]`. Apply the tactic sequence `try ring`. Consider the case `zero`.

Conclude with `⟨0, 0, by funext i; simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨y1, s1, rfl⟩` from `hx`. Take `⟨y2, s2, rfl⟩` from `hy`. Conclude with `⟨y1 + y2, s1 + s2, by funext i; simp only [Pi.add_apply, map_add]; ring⟩`.

Consider the case `smul r x _ hx`. Take `⟨y1, s1, rfl⟩` from `hx`. Conclude with `⟨r * y1, r • s1, by`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]`.

Use the proof step `ring⟩`.
-/
theorem famS (v : Fin k → R.W ⧸ Ideal.span {(p : R.W)}) (hv : v ≠ 0) :
    ∃ e : Edge R.W R.Qq k, IsEdge p n' 1 e ∧ e.src = colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) ∧
      ∃ vt : Fin k → R.W, (∀ i, R.res (vt i) = v i) ∧
        ((fun i => (p : R.Qq)⁻¹ * algebraMap R.W R.Qq (vt i)) ∈ e.tgt) ∧
        ∀ x ∈ e.tgt, ∃ (y : R.W) (s : Fin k → R.W),
          x = fun i => algebraMap R.W R.Qq (vt i) * (p : R.Qq)⁻¹ * algebraMap R.W R.Qq y +
            algebraMap R.W R.Qq (s i) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  choose vt hvt using fun i => Ideal.Quotient.mk_surjective (v i)
  have hres : ∀ i, R.res (vt i) = v i := hvt
  have hu : IsUnit (vt j) := R.unit_of_res_ne (by rw [hres]; exact hj)
  let V : Matrix (Fin k) (Fin k) R.W := (1 : Matrix (Fin k) (Fin k) R.W).updateCol j vt
  have hV : IsUnit V.det := by
    show IsUnit ((1 : Matrix (Fin k) (Fin k) R.W).updateCol j vt).det
    rw [det_updateCol_one]
    exact hu
  refine ⟨_, edgeS R V hV j, rfl, vt, hres, ?_, ?_⟩
  · apply Submodule.subset_span
    refine ⟨j, ?_⟩
    funext i
    simp [V, mapM, dj, Matrix.mul_diagonal, Matrix.updateCol_apply]
    try ring
  · intro x hx
    unfold colSpan at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c0, rfl⟩ := hx
      by_cases hc : c0 = j
      · subst hc
        refine ⟨1, 0, ?_⟩
        funext i
        simp [V, mapM, dj, Matrix.mul_diagonal, Matrix.updateCol_apply]
        try ring
      · refine ⟨0, fun i => (1 : Matrix (Fin k) (Fin k) R.W) i c0, ?_⟩
        funext i
        simp [V, mapM, dj, Matrix.mul_diagonal, Matrix.updateCol_apply, hc]
        try ring
    | zero =>
      exact ⟨0, 0, by funext i; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨y1, s1, rfl⟩ := hx
      obtain ⟨y2, s2, rfl⟩ := hy
      exact ⟨y1 + y2, s1 + s2, by funext i; simp only [Pi.add_apply, map_add]; ring⟩
    | smul r x _ hx =>
      obtain ⟨y1, s1, rfl⟩ := hx
      exact ⟨r * y1, r • s1, by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]
        ring⟩

def phi (c : Fin k → R.W ⧸ Ideal.span {(p : R.W)}) (w : Fin k → R.W) : R.W ⧸ Ideal.span {(p : R.W)} :=
  ∑ l, c l * R.res (w l)

def VT (j : Fin k) (a : Fin k → R.W) : Matrix (Fin k) (Fin k) R.W :=
  (1 : Matrix (Fin k) (Fin k) R.W).updateRow j fun i => if i = j then 1 else -a i

/- English proof (translation)
Unfold `phi VT`. Rewrite using `[Fintype.sum_eq_add i j hij]`. Apply the tactic sequence `simp [Matrix.updateRow_ne hij, Matrix.one_apply, hij] <;> ring`. Introduce and unpack `l ⟨hli, hlj⟩`. Simplify using `[Matrix.updateRow_ne hlj, Matrix.one_apply, hli]`.
-/
theorem phi_col (c : Fin k → R.W ⧸ Ideal.span {(p : R.W)}) (j : Fin k) (a : Fin k → R.W) (i : Fin k)
    (hij : i ≠ j) : phi R c (fun l => VT R j a l i) = c i - R.res (a i) * c j := by
  unfold phi VT
  rw [Fintype.sum_eq_add i j hij]
  · simp [Matrix.updateRow_ne hij, Matrix.one_apply, hij] <;> ring
  · rintro l ⟨hli, hlj⟩
    simp [Matrix.updateRow_ne hlj, Matrix.one_apply, hli]

/- English proof (translation)
Establish `hdet : IsUnit (VT R j a).det`. Unfold `VT`. Rewrite using `[det_updateRow_one]`. Simplify using the standard rewrite rules. Use `⟨edgeT R (VT R j a) hdet j, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Unfold `colSpan at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c0, rfl⟩` from `hx`.

Use `⟨fun i => VT R j a i c0 * (if c0 = j then (p : R.W) else 1), ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases hc : c0 = j <;> simp [emb, mapM, dj, Matrix.mul_diagonal, hc]`. Distinguish the cases in `hc : c0 = j`. Substitute `hc` using the available equality.

Unfold `phi`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l _`. Simplify using `[map_mul, R.res_p]`. Simplify using `only [hc, if_false, mul_one]`.

Rewrite using `[phi_col R c j a c0 hc, ha c0, sub_self]`. Consider the case `zero`. Use `⟨0, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[emb]`.

Unfold `phi`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`. Take `⟨w1, rfl, h1⟩` from `hx`. Take `⟨w2, rfl, h2⟩` from `hy`.

Use `⟨w1 + w2, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[emb]`. Unfold `phi at h1 h2 ⊢`. Simplify using `only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]`.

Consider the case `smul r x _ hx`. Take `⟨w, rfl, hw⟩` from `hx`. Use `⟨r • w, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[emb, Algebra.smul_def]`.

Unfold `phi at hw ⊢`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `l _`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by rw [hw, mul_zero]`. Introduce `i hij`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨i, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `l`. Simplify using `[emb, mapM, dj, Matrix.mul_diagonal, hij]`.
-/
theorem famT (c : Fin k → R.W ⧸ Ideal.span {(p : R.W)}) (j : Fin k) (a : Fin k → R.W)
    (ha : ∀ i, R.res (a i) * c j = c i) :
    IsEdge p n' 1 (⟨colSpan R.W (mapM (VT R j a) * dj j (p : R.Qq)),
        colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)⟩ : Edge R.W R.Qq k) ∧
      (∀ x ∈ colSpan R.W (mapM (VT R j a) * dj j (p : R.Qq)), ∃ w : Fin k → R.W, x = emb w ∧ phi R c w = 0) ∧
      ∀ i, i ≠ j → (emb (fun l => VT R j a l i) : Fin k → R.Qq) ∈
        colSpan R.W (mapM (VT R j a) * dj j (p : R.Qq)) := by
  have hdet : IsUnit (VT R j a).det := by
    unfold VT
    rw [det_updateRow_one]
    simp
  refine ⟨edgeT R (VT R j a) hdet j, ?_, ?_⟩
  · intro x hx
    unfold colSpan at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c0, rfl⟩ := hx
      refine ⟨fun i => VT R j a i c0 * (if c0 = j then (p : R.W) else 1), ?_, ?_⟩
      · funext i
        by_cases hc : c0 = j <;> simp [emb, mapM, dj, Matrix.mul_diagonal, hc]
      · by_cases hc : c0 = j
        · subst hc
          unfold phi
          apply Finset.sum_eq_zero
          intro l _
          simp [map_mul, R.res_p]
        · simp only [hc, if_false, mul_one]
          rw [phi_col R c j a c0 hc, ha c0, sub_self]
    | zero =>
      refine ⟨0, ?_, ?_⟩
      · funext i
        simp [emb]
      · unfold phi
        simp
    | add x y _ _ hx hy =>
      obtain ⟨w1, rfl, h1⟩ := hx
      obtain ⟨w2, rfl, h2⟩ := hy
      refine ⟨w1 + w2, ?_, ?_⟩
      · funext i
        simp [emb]
      · unfold phi at h1 h2 ⊢
        simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]
    | smul r x _ hx =>
      obtain ⟨w, rfl, hw⟩ := hx
      refine ⟨r • w, ?_, ?_⟩
      · funext i
        simp [emb, Algebra.smul_def]
      · unfold phi at hw ⊢
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        calc ∑ l, c l * (R.res r * R.res (w l)) = R.res r * ∑ l, c l * R.res (w l) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro l _
              ring
          _ = 0 := by rw [hw, mul_zero]
  · intro i hij
    apply Submodule.subset_span
    refine ⟨i, ?_⟩
    funext l
    simp [emb, mapM, dj, Matrix.mul_diagonal, hij]

end Fam

/- English proof (translation)
Introduce `p n' R k hk L hL`. Use `haveI hmax : (Ideal.span {(p : R.W)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible R.std.1.p_unif`. Use `letI : Field (R.W ⧸ Ideal.span {(p : R.W)}) := Ideal.Quotient.field _`. Use `haveI := R.std.1.frac_alt`. Establish `hcard : Nat.card (R.W ⧸ Ideal.span {(p : R.W)}) = p ^ n'` using `R.std.1.res_card`.

Establish `hp5 : 5 ≤ p` using `R.std.1.five_le`. Establish `hq2 : 2 ≤ p ^ n'` using `le_trans (by omega) (Nat.le_self_pow (by have := R.std.1.two_le; omega) p)`. Use `haveI : Finite (R.W ⧸ Ideal.span {(p : R.W)}) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)`. Use `haveI : Finite (Projectivization (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)})) := by`. Unfold `Projectivization`.

Use `infer_instance`. Use `set Ne := Nat.card (Projectivization (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)}))`. Set `eqv` to `Finite.equivFin (Projectivization (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)}))`. Use `set v : Fin Ne → Fin k → R.W ⧸ Ideal.span {(p : R.W)} := fun i => (eqv.symm i).rep with hvdef`. Establish `hv0 : ∀ i, v i ≠ 0` using `fun i => Projectivization.rep_nonzero _`.

Use `choose es he using fun i => famS R (v i) (hv0 i)`. Establish `hp0 : (p : R.Qq) ≠ 0`. Establish `h1 : (p : R.W) ≠ 0` using `R.std.1.p_unif.ne_zero`. Introduce `h2`. Apply `h1` to reduce the goal to its premises.

Apply `IsFractionRing.injective R.W R.Qq` to reduce the goal to its premises. Rewrite using `[map_natCast, map_zero]`. Conclude with `h2`. Establish `hpp : (p : R.Qq) * (p : R.Qq)⁻¹ = 1` using `mul_inv_cancel₀ hp0`. Establish `hinj : Function.Injective es`.

Introduce `i i' hii`. Take `⟨-, -, vt, hvt, hmem, -⟩` from `he i'`. Take `⟨-, -, vt0, hvt0, -, hall⟩` from `he i`. Rewrite `hmem` using `[← hii]`. Take `⟨y, s, hys⟩` from `hall _ hmem`.

Establish `hW : ∀ l, vt l = vt0 l * y + (p : R.W) * s l`. Introduce `l`. Establish `e1` using `congrFun hys l`. Apply `IsFractionRing.injective R.W R.Qq` to reduce the goal to its premises. Rewrite using `[map_add, map_mul, map_mul, map_natCast]`.

Take the linear combination `(p : R.Qq) * e1 - (algebraMap R.W R.Qq (vt l) - algebraMap R.W R.Qq (vt0 l) * algebraMap R.W R.Qq y) * hpp`. Establish `hv : (R.res y) • v i = v i'`. Use function extensionality and compare the values at `l`. Rewrite using `[Pi.smul_apply, ← hvt l, ← hvt0 l, hW l, smul_eq_mul]`. Simplify using `[R.res_p, mul_comm]`.

Establish `key : Projectivization.mk (R.W ⧸ Ideal.span {(p : R.W)}) (v i') (hv0 i') = Projectivization.mk (R.W ⧸ Ideal.span {(p : R.W)}) (v i) (hv0 i)`. Establish `hy0 : R.res y ≠ 0` using `fun h0 => hv0 i' (by rw [← hv, h0, zero_smul])`. Conclude with `(Projectivization.mk_eq_mk_iff _ _ _ _ _).2 ⟨Units.mk0 (R.res y) hy0, by rw [Units.smul_def, Units.val_mk0]; exact hv⟩`. Apply `eqv.symm.injective` to reduce the goal to its premises. Rewrite using `[← Projectivization.mk_rep (eqv.symm i), ← Projectivization.mk_rep (eqv.symm i')]`.

Conclude with `key.symm`. Take `⟨es', hinj', hedge', -, hsrc'⟩` from `transport R L hL es hinj (fun i => (he i).1)`. Use `⟨Ne, es', hinj', fun i => ⟨hedge' i, hsrc' i (he i).2.1⟩, ?_⟩` and prove the remaining obligations. Establish `hV : Nat.card (Fin k → R.W ⧸ Ideal.span {(p : R.W)}) = (p ^ n') ^ k`. Rewrite using `[Nat.card_fun, hcard, Nat.card_fin]`.

Establish `h1 : (p ^ n') ^ k - 1 = Ne * (p ^ n' - 1)`. Establish `h2` using `Projectivization.card (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)})`. Rewrite `h2` using `[hV, hcard]`. Then use the resulting hypothesis. Establish `hqk : 1 ≤ (p ^ n') ^ k` using `Nat.one_le_pow _ _ (by omega)`. Establish `h1' : (((p ^ n' : ℕ) : ℝ)) ^ k - 1 = (Ne : ℝ) * (((p ^ n' : ℕ) : ℝ) - 1)`.

Establish `h3` using `congrArg (Nat.cast : ℕ → ℝ) h1`. Rewrite `h3` using `[Nat.cast_sub hqk, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p ^ n'), Nat.cast_pow, Nat.cast_one]`. Conclude with `h3`. Establish `hq2' : (2 : ℝ) ≤ ((p ^ n' : ℕ) : ℝ)` using `by exact_mod_cast hq2`. Unfold `gaussianNumber`.

Rewrite using `[div_le_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem restEdgeCountSrc : RestEdgeCountSrc := by
  intro p n' R k hk L hL
  haveI hmax : (Ideal.span {(p : R.W)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible R.std.1.p_unif
  letI : Field (R.W ⧸ Ideal.span {(p : R.W)}) := Ideal.Quotient.field _
  haveI := R.std.1.frac_alt
  have hcard : Nat.card (R.W ⧸ Ideal.span {(p : R.W)}) = p ^ n' := R.std.1.res_card
  have hp5 : 5 ≤ p := R.std.1.five_le
  have hq2 : 2 ≤ p ^ n' := le_trans (by omega) (Nat.le_self_pow (by have := R.std.1.two_le; omega) p)
  haveI : Finite (R.W ⧸ Ideal.span {(p : R.W)}) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  haveI : Finite (Projectivization (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)})) := by
    unfold Projectivization
    infer_instance
  set Ne := Nat.card (Projectivization (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)}))
  let eqv := Finite.equivFin (Projectivization (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)}))
  set v : Fin Ne → Fin k → R.W ⧸ Ideal.span {(p : R.W)} := fun i => (eqv.symm i).rep with hvdef
  have hv0 : ∀ i, v i ≠ 0 := fun i => Projectivization.rep_nonzero _
  choose es he using fun i => famS R (v i) (hv0 i)
  have hp0 : (p : R.Qq) ≠ 0 := by
    have h1 : (p : R.W) ≠ 0 := R.std.1.p_unif.ne_zero
    intro h2
    apply h1
    apply IsFractionRing.injective R.W R.Qq
    rw [map_natCast, map_zero]
    exact h2
  have hpp : (p : R.Qq) * (p : R.Qq)⁻¹ = 1 := mul_inv_cancel₀ hp0
  have hinj : Function.Injective es := by
    intro i i' hii
    obtain ⟨-, -, vt, hvt, hmem, -⟩ := he i'
    obtain ⟨-, -, vt0, hvt0, -, hall⟩ := he i
    rw [← hii] at hmem
    obtain ⟨y, s, hys⟩ := hall _ hmem
    have hW : ∀ l, vt l = vt0 l * y + (p : R.W) * s l := by
      intro l
      have e1 := congrFun hys l
      apply IsFractionRing.injective R.W R.Qq
      rw [map_add, map_mul, map_mul, map_natCast]
      linear_combination (p : R.Qq) * e1 -
        (algebraMap R.W R.Qq (vt l) - algebraMap R.W R.Qq (vt0 l) * algebraMap R.W R.Qq y) * hpp
    have hv : (R.res y) • v i = v i' := by
      funext l
      rw [Pi.smul_apply, ← hvt l, ← hvt0 l, hW l, smul_eq_mul]
      simp [R.res_p, mul_comm]
    have key : Projectivization.mk (R.W ⧸ Ideal.span {(p : R.W)}) (v i') (hv0 i') =
        Projectivization.mk (R.W ⧸ Ideal.span {(p : R.W)}) (v i) (hv0 i) := by
      have hy0 : R.res y ≠ 0 := fun h0 => hv0 i' (by rw [← hv, h0, zero_smul])
      exact (Projectivization.mk_eq_mk_iff _ _ _ _ _).2 ⟨Units.mk0 (R.res y) hy0, by rw [Units.smul_def, Units.val_mk0]; exact hv⟩
    apply eqv.symm.injective
    rw [← Projectivization.mk_rep (eqv.symm i), ← Projectivization.mk_rep (eqv.symm i')]
    exact key.symm
  obtain ⟨es', hinj', hedge', -, hsrc'⟩ := transport R L hL es hinj (fun i => (he i).1)
  refine ⟨Ne, es', hinj', fun i => ⟨hedge' i, hsrc' i (he i).2.1⟩, ?_⟩
  have hV : Nat.card (Fin k → R.W ⧸ Ideal.span {(p : R.W)}) = (p ^ n') ^ k := by
    rw [Nat.card_fun, hcard, Nat.card_fin]
  have h1 : (p ^ n') ^ k - 1 = Ne * (p ^ n' - 1) := by
    have h2 := Projectivization.card (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)})
    rwa [hV, hcard] at h2
  have hqk : 1 ≤ (p ^ n') ^ k := Nat.one_le_pow _ _ (by omega)
  have h1' : (((p ^ n' : ℕ) : ℝ)) ^ k - 1 = (Ne : ℝ) * (((p ^ n' : ℕ) : ℝ) - 1) := by
    have h3 := congrArg (Nat.cast : ℕ → ℝ) h1
    rw [Nat.cast_sub hqk, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p ^ n'), Nat.cast_pow, Nat.cast_one] at h3
    exact h3
  have hq2' : (2 : ℝ) ≤ ((p ^ n' : ℕ) : ℝ) := by exact_mod_cast hq2
  unfold gaussianNumber
  rw [div_le_iff₀ (by linarith)]
  linarith

/- English proof (translation)
Introduce `p n' R k hk L hL`. Use `haveI hmax : (Ideal.span {(p : R.W)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible R.std.1.p_unif`. Use `letI : Field (R.W ⧸ Ideal.span {(p : R.W)}) := Ideal.Quotient.field _`. Use `haveI := R.std.1.frac_alt`. Establish `hcard : Nat.card (R.W ⧸ Ideal.span {(p : R.W)}) = p ^ n'` using `R.std.1.res_card`.

Establish `hp5 : 5 ≤ p` using `R.std.1.five_le`. Establish `hq2 : 2 ≤ p ^ n'` using `le_trans (by omega) (Nat.le_self_pow (by have := R.std.1.two_le; omega) p)`. Use `haveI : Finite (R.W ⧸ Ideal.span {(p : R.W)}) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)`. Use `haveI : Finite (Projectivization (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)})) := by`. Unfold `Projectivization`.

Use `infer_instance`. Use `set Ne := Nat.card (Projectivization (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)}))`. Set `eqv` to `Finite.equivFin (Projectivization (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)}))`. Use `set cc : Fin Ne → Fin k → R.W ⧸ Ideal.span {(p : R.W)} := fun i => (eqv.symm i).rep with hccdef`. Establish `hc0 : ∀ i, cc i ≠ 0` using `fun i => Projectivization.rep_nonzero _`.

Use `choose jj hjj using fun i => Function.ne_iff.mp (hc0 i)`. Establish `hjj' : ∀ i, cc i (jj i) ≠ 0` using `fun i => by simpa using hjj i`. Use `choose aa haa using fun i l => Ideal.Quotient.mk_surjective (cc i l * (cc i (jj i))⁻¹)`. Establish `hres : ∀ i l, R.res (aa i l) = cc i l * (cc i (jj i))⁻¹` using `haa`. Establish `hA : ∀ i l, R.res (aa i l) * cc i (jj i) = cc i l`.

Introduce `i l`. Rewrite using `[hres, mul_assoc, inv_mul_cancel₀ (hjj' i), mul_one]`. Establish `hf` using `fun i => famT R (cc i) (jj i) (aa i) (hA i)`. Set `es : Fin Ne → Edge R.W R.Qq k` to `fun i => ⟨colSpan R.W (mapM (VT R (jj i) (aa i)) * dj (jj i) (p : R.Qq)), colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)⟩`. Establish `hinj : Function.Injective es`.

Introduce `i i' hii`. Establish `hsrc` using `congrArg Edge.src hii`. Establish `key : ∀ l, cc i l = cc i' l * (cc i' (jj i'))⁻¹ * cc i (jj i')`. Introduce `l`. Distinguish the cases in `hl : l = jj i'`.

Substitute `hl` using the available equality. Rewrite using `[mul_inv_cancel₀ (hjj' i'), one_mul]`. Establish `hmem` using `(hf i').2.2 l hl`. Establish `hmem' : (emb (fun l' => VT R (jj i') (aa i') l' l) : Fin k → R.Qq) ∈ (es i).src`. Rewrite using `[hsrc]`.

Conclude with `hmem`. Take `⟨w, hw, hphi⟩` from `(hf i).2.1 _ hmem'`. Establish `hw'` using `emb_inj R hw`. Rewrite `hphi` using `[← hw', phi_col R (cc i) (jj i') (aa i') l hl, hres]`. Take the linear combination `hphi`.

Establish `hv : (cc i (jj i') * (cc i' (jj i'))⁻¹) • cc i' = cc i`. Use function extensionality and compare the values at `l`. Rewrite using `[Pi.smul_apply, smul_eq_mul, key l]`. Expand and normalize the polynomial expressions, which then agree. Establish `hne : cc i (jj i') * (cc i' (jj i'))⁻¹ ≠ 0`.

Introduce `h0`. Apply `hc0 i` to reduce the goal to its premises. Rewrite using `[← hv, h0, zero_smul]`. Establish `key2 : Projectivization.mk (R.W ⧸ Ideal.span {(p : R.W)}) (cc i) (hc0 i) = Projectivization.mk (R.W ⧸ Ideal.span {(p : R.W)}) (cc i') (hc0 i')` using `(Projectivization.mk_eq_mk_iff _ _ _ _ _).2 ⟨Units.mk0 _ hne, by rw [Units.smul_def, Units.val_mk0]; exact hv⟩`. Apply `eqv.symm.injective` to reduce the goal to its premises.

Rewrite using `[← Projectivization.mk_rep (eqv.symm i), ← Projectivization.mk_rep (eqv.symm i')]`. Conclude with `key2`. Take `⟨es', hinj', hedge', htgt', -⟩` from `transport R L hL es hinj (fun i => (hf i).1)`. Use `⟨Ne, es', hinj', fun i => ⟨hedge' i, htgt' i rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hV : Nat.card (Fin k → R.W ⧸ Ideal.span {(p : R.W)}) = (p ^ n') ^ k`.

Rewrite using `[Nat.card_fun, hcard, Nat.card_fin]`. Establish `h1 : (p ^ n') ^ k - 1 = Ne * (p ^ n' - 1)`. Establish `h2` using `Projectivization.card (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)})`. Rewrite `h2` using `[hV, hcard]`. Then use the resulting hypothesis. Establish `hqk : 1 ≤ (p ^ n') ^ k` using `Nat.one_le_pow _ _ (by omega)`.

Establish `h1' : (((p ^ n' : ℕ) : ℝ)) ^ k - 1 = (Ne : ℝ) * (((p ^ n' : ℕ) : ℝ) - 1)`. Establish `h3` using `congrArg (Nat.cast : ℕ → ℝ) h1`. Rewrite `h3` using `[Nat.cast_sub hqk, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p ^ n'), Nat.cast_pow, Nat.cast_one]`. Conclude with `h3`. Establish `hq2' : (2 : ℝ) ≤ ((p ^ n' : ℕ) : ℝ)` using `by exact_mod_cast hq2`.

Unfold `gaussianNumber`. Rewrite using `[div_le_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem restEdgeCount : RestEdgeCount := by
  intro p n' R k hk L hL
  haveI hmax : (Ideal.span {(p : R.W)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible R.std.1.p_unif
  letI : Field (R.W ⧸ Ideal.span {(p : R.W)}) := Ideal.Quotient.field _
  haveI := R.std.1.frac_alt
  have hcard : Nat.card (R.W ⧸ Ideal.span {(p : R.W)}) = p ^ n' := R.std.1.res_card
  have hp5 : 5 ≤ p := R.std.1.five_le
  have hq2 : 2 ≤ p ^ n' := le_trans (by omega) (Nat.le_self_pow (by have := R.std.1.two_le; omega) p)
  haveI : Finite (R.W ⧸ Ideal.span {(p : R.W)}) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  haveI : Finite (Projectivization (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)})) := by
    unfold Projectivization
    infer_instance
  set Ne := Nat.card (Projectivization (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)}))
  let eqv := Finite.equivFin (Projectivization (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)}))
  set cc : Fin Ne → Fin k → R.W ⧸ Ideal.span {(p : R.W)} := fun i => (eqv.symm i).rep with hccdef
  have hc0 : ∀ i, cc i ≠ 0 := fun i => Projectivization.rep_nonzero _
  choose jj hjj using fun i => Function.ne_iff.mp (hc0 i)
  have hjj' : ∀ i, cc i (jj i) ≠ 0 := fun i => by simpa using hjj i
  choose aa haa using fun i l => Ideal.Quotient.mk_surjective (cc i l * (cc i (jj i))⁻¹)
  have hres : ∀ i l, R.res (aa i l) = cc i l * (cc i (jj i))⁻¹ := haa
  have hA : ∀ i l, R.res (aa i l) * cc i (jj i) = cc i l := by
    intro i l
    rw [hres, mul_assoc, inv_mul_cancel₀ (hjj' i), mul_one]
  have hf := fun i => famT R (cc i) (jj i) (aa i) (hA i)
  let es : Fin Ne → Edge R.W R.Qq k := fun i =>
    ⟨colSpan R.W (mapM (VT R (jj i) (aa i)) * dj (jj i) (p : R.Qq)), colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)⟩
  have hinj : Function.Injective es := by
    intro i i' hii
    have hsrc := congrArg Edge.src hii
    have key : ∀ l, cc i l = cc i' l * (cc i' (jj i'))⁻¹ * cc i (jj i') := by
      intro l
      by_cases hl : l = jj i'
      · subst hl
        rw [mul_inv_cancel₀ (hjj' i'), one_mul]
      · have hmem := (hf i').2.2 l hl
        have hmem' : (emb (fun l' => VT R (jj i') (aa i') l' l) : Fin k → R.Qq) ∈ (es i).src := by
          rw [hsrc]
          exact hmem
        obtain ⟨w, hw, hphi⟩ := (hf i).2.1 _ hmem'
        have hw' := emb_inj R hw
        rw [← hw', phi_col R (cc i) (jj i') (aa i') l hl, hres] at hphi
        linear_combination hphi
    have hv : (cc i (jj i') * (cc i' (jj i'))⁻¹) • cc i' = cc i := by
      funext l
      rw [Pi.smul_apply, smul_eq_mul, key l]
      ring
    have hne : cc i (jj i') * (cc i' (jj i'))⁻¹ ≠ 0 := by
      intro h0
      apply hc0 i
      rw [← hv, h0, zero_smul]
    have key2 : Projectivization.mk (R.W ⧸ Ideal.span {(p : R.W)}) (cc i) (hc0 i) =
        Projectivization.mk (R.W ⧸ Ideal.span {(p : R.W)}) (cc i') (hc0 i') :=
      (Projectivization.mk_eq_mk_iff _ _ _ _ _).2 ⟨Units.mk0 _ hne, by rw [Units.smul_def, Units.val_mk0]; exact hv⟩
    apply eqv.symm.injective
    rw [← Projectivization.mk_rep (eqv.symm i), ← Projectivization.mk_rep (eqv.symm i')]
    exact key2
  obtain ⟨es', hinj', hedge', htgt', -⟩ := transport R L hL es hinj (fun i => (hf i).1)
  refine ⟨Ne, es', hinj', fun i => ⟨hedge' i, htgt' i rfl⟩, ?_⟩
  have hV : Nat.card (Fin k → R.W ⧸ Ideal.span {(p : R.W)}) = (p ^ n') ^ k := by
    rw [Nat.card_fun, hcard, Nat.card_fin]
  have h1 : (p ^ n') ^ k - 1 = Ne * (p ^ n' - 1) := by
    have h2 := Projectivization.card (R.W ⧸ Ideal.span {(p : R.W)}) (Fin k → R.W ⧸ Ideal.span {(p : R.W)})
    rwa [hV, hcard] at h2
  have hqk : 1 ≤ (p ^ n') ^ k := Nat.one_le_pow _ _ (by omega)
  have h1' : (((p ^ n' : ℕ) : ℝ)) ^ k - 1 = (Ne : ℝ) * (((p ^ n' : ℕ) : ℝ) - 1) := by
    have h3 := congrArg (Nat.cast : ℕ → ℝ) h1
    rw [Nat.cast_sub hqk, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p ^ n'), Nat.cast_pow, Nat.cast_one] at h3
    exact h3
  have hq2' : (2 : ℝ) ≤ ((p ^ n' : ℕ) : ℝ) := by exact_mod_cast hq2
  unfold gaussianNumber
  rw [div_le_iff₀ (by linarith)]
  linarith

/- English proof (translation)
Conclude with `rho_lower_bound_of_edge_count restEdgeCount`.
-/
theorem rho_lower_bound_large_conductor : RhoLowerBoundLargeConductor := by
  exact rho_lower_bound_of_edge_count restEdgeCount

/- English proof (translation)
Conclude with `rho_upper_bound_of_edge_count restEdgeCountSrc`.
-/
theorem rho_upper_bound_small_depth : RhoUpperBoundSmallDepth := by
  exact rho_upper_bound_of_edge_count restEdgeCountSrc

end Formalism.MainNotions.flipOneThree.Pf

end
