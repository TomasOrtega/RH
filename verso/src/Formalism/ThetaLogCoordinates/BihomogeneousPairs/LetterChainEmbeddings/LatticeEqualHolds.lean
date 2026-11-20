import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PairStep

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality

section tieop
variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `hp1 : (1 : ℝ) ≤ p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt.le`. Use `set Mc : ℝ := (p : ℝ) ^ L with hMc`. Establish `hM1 : 1 ≤ Mc` using `one_le_pow₀ hp1`. Establish `hM : ∀ j ≤ m, ∀ k ≤ j, ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ Mc` using `fun j hj k hk => (norm_choose_inv_le j k hk).trans (pow_le_pow_right₀ hp1 ((Nat.log_mono_right hj).trans hmL))`. Set `Dc : Fin r → (MvPolynomial τ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial τ ℚ_[p])` to `fun c => (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial τ ℚ_[p]) (MvPolynomial τ ℚ_[p])).toLinearMap ∘ₗ (pderiv (e c)).toLinearMap`.

Establish `hcomm : ∀ a b, Commute (Dc a) (Dc b)`. Introduce `a b`. Simplify using `only [Dc, ← Module.End.mul_eq_comp]`. Apply the tactic sequence `refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>`. Conclude with `commute_pderiv _ _`.

Establish `hF` using `contr_Fsum Dc hcomm (fun a k => contr_D _ _ k) hM1 m hM Finset.univ`. Rewrite `hF` using `[Finset.card_univ, Fintype.card_fin]`. Establish `hFeq : tieF (k` using `ℚ_[p]) w e = ∑ c ∈ Finset.univ, Dc c := rfl`. Establish `hb : Bnd (p` using `p) 1 y := (intPol_iff_bnd y).mp hy`. Establish `h1` using `hF m le_rfl 1 zero_le_one y hb`.

Rewrite `h1` using `[← hFeq]`. Rewrite using `[intPol_iff_bnd, ← smul_smul]`. Establish `h2` using `bnd_smul ((p : ℚ_[p]) ^ (r * L)) h1`. Introduce `μ`. Use `(h2 μ).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[Padic.norm_p_pow, hMc, one_mul, ← pow_mul, zpow_neg, zpow_natCast, mul_comm L r]`. Conclude with `inv_mul_cancel₀ (pow_ne_zero _ (by positivity))`.
-/
theorem int_Fpow {τ : Type} {r : ℕ} (L m : ℕ) (hmL : Nat.log p m ≤ L) (w e : Fin r → τ)
    {y : MvPolynomial τ ℚ_[p]} (hy : y ∈ IntPol p τ) :
    (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF w e ^ m) y) ∈ IntPol p τ := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  set Mc : ℝ := (p : ℝ) ^ L with hMc
  have hM1 : 1 ≤ Mc := one_le_pow₀ hp1
  have hM : ∀ j ≤ m, ∀ k ≤ j, ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ Mc := fun j hj k hk =>
    (norm_choose_inv_le j k hk).trans (pow_le_pow_right₀ hp1 ((Nat.log_mono_right hj).trans hmL))
  let Dc : Fin r → (MvPolynomial τ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial τ ℚ_[p]) := fun c =>
    (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial τ ℚ_[p]) (MvPolynomial τ ℚ_[p])).toLinearMap ∘ₗ
      (pderiv (e c)).toLinearMap
  have hcomm : ∀ a b, Commute (Dc a) (Dc b) := by
    intro a b
    simp only [Dc, ← Module.End.mul_eq_comp]
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
      exact commute_pderiv _ _
  have hF := contr_Fsum Dc hcomm (fun a k => contr_D _ _ k) hM1 m hM Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hF
  have hFeq : tieF (k := ℚ_[p]) w e = ∑ c ∈ Finset.univ, Dc c := rfl
  have hb : Bnd (p := p) 1 y := (intPol_iff_bnd y).mp hy
  have h1 := hF m le_rfl 1 zero_le_one y hb
  rw [← hFeq] at h1
  rw [intPol_iff_bnd, ← smul_smul]
  have h2 := bnd_smul ((p : ℚ_[p]) ^ (r * L)) h1
  intro μ
  refine (h2 μ).trans (le_of_eq ?_)
  rw [Padic.norm_p_pow, hMc, one_mul, ← pow_mul, zpow_neg, zpow_natCast, mul_comm L r]
  exact inv_mul_cancel₀ (pow_ne_zero _ (by positivity))

variable {N r : ℕ} [NeZero r] {D : BlockData N}

/- English proof (translation)
The claim follows from `ProjS.pderiv_of_free v g (fun m hm => (xi_supp hg hm).1 v hv)`.
-/
theorem xi_free {b : ℕ} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]} (hg : g ∈ XiPolZ p N r D.T.t b)
    {v : BVar N r D.T.t} (hv : ∀ c, v ≠ xiVar N r D.T.t c) : pderiv v g = 0 :=
  ProjS.pderiv_of_free v g (fun m hm => (xi_supp hg hm).1 v hv)

/- English proof (translation)
Rewrite using `[tieF_apply', tieF_apply', map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[pderiv_mul, he c, mul_zero, add_zero, ev_chain hB, pderiv_rename chainEmb_inj, pderiv_mul, hw c, mul_zero, add_zero, wv_chain hB, pderiv_rename chainEmb_inj]`.
-/
theorem tieF_gen (hB : D.BlockOK) (i : Fin D.T.t) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (g : MvPolynomial (BVar N r D.T.t) ℚ_[p]) (hw : ∀ c, pderiv (wv D i c) g = 0)
    (he : ∀ c, pderiv (ev D i c) g = 0) :
    tieF (wv D i) (ev D i) (rename (chainEmb N r D.T.t) y * g) =
      rename (chainEmb N r D.T.t)
        (tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) y) * g := by
  rw [tieF_apply', tieF_apply', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [pderiv_mul, he c, mul_zero, add_zero, ev_chain hB, pderiv_rename chainEmb_inj, pderiv_mul, hw c,
    mul_zero, add_zero, wv_chain hB, pderiv_rename chainEmb_inj]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, tieF_gen hB i _ g hw he, ← Module.End.mul_apply, ← pow_succ']`.
-/
theorem tieF_pow_gen (hB : D.BlockOK) (i : Fin D.T.t) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (g : MvPolynomial (BVar N r D.T.t) ℚ_[p]) (hw : ∀ c, pderiv (wv D i c) g = 0)
    (he : ∀ c, pderiv (ev D i c) g = 0) (m : ℕ) :
    (tieF (wv D i) (ev D i) ^ m) (rename (chainEmb N r D.T.t) y * g) =
      rename (chainEmb N r D.T.t)
        ((tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) ^ m) y) * g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, tieF_gen hB i _ g hw he, ← Module.End.mul_apply, ← pow_succ']

omit [NeZero r] in
/- English proof (translation)
Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[hk]`.
-/
theorem update_single (j : Fin D.T.t → ℕ) (i : Fin D.T.t) (m : ℕ) :
    Function.update (j + Pi.single i m : Fin D.T.t → ℕ) i ((j + Pi.single i m : Fin D.T.t → ℕ) i + 1) =
      j + Pi.single i (m + 1) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp; ring
  · simp [hk]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `j jp y hy`. Establish `h0 : j + Pi.single i 0 = j` using `by simp`.

Rewrite using `[h0, pow_zero, Module.End.one_apply]`. Conclude with `hy`. Consider the case `succ m ih`. Introduce `j jp y hy`. Establish `h` using `hF _ jp i _ (ih j jp y hy)`.

Rewrite `h` using `[update_single]`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `h`.
-/
theorem Y_iter (hF : HypJoin p (r := r) D) (i : Fin D.T.t) :
    ∀ m (j : Fin D.T.t → ℕ) (jp : ℕ), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      (tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) ^ m) y ∈
        Y p (r := r) (D.lettersAt (j + Pi.single i m) jp) D.T.J D.T.thr := by
  intro m
  induction m with
  | zero =>
    intro j jp y hy
    have h0 : j + Pi.single i 0 = j := by simp
    rw [h0, pow_zero, Module.End.one_apply]
    exact hy
  | succ m ih =>
    intro j jp y hy
    have h := hF _ jp i _ (ih j jp y hy)
    rw [update_single] at h
    rw [pow_succ', Module.End.mul_apply]
    exact h

/- English proof (translation)
Introduce `x hx`. Use `span_map_mem ((((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹)) • (tieF (wv D i) (ev D i) ^ m)) _ (Lat p D (r := r) (j + Pi.single i m) jp) ?_ x hx` as an intermediate fact. Simplify using `using this`. Introduce and unpack `v ⟨y, hy, g, hg, rfl⟩`. Rewrite using `[LinearMap.smul_apply, tieF_pow_gen hB i y g (fun c => xi_free hg (fun d => wv_ne_xi hB i c d)) (fun c => xi_free hg (fun d => ev_ne_xi hB i c d)), ← smul_mul_assoc, ← map_smul]`.

Use `Submodule.subset_span ⟨_, yz_mk (Submodule.smul_mem _ _ (Y_iter hF i m j jp y (yz_y hy))) (int_Fpow L m hmL _ _ (yz_int hy)), g, hg, rfl⟩` and prove the remaining obligations.
-/
theorem lat_tie (hB : D.BlockOK) (hF : HypJoin p (r := r) D) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t)
    (m L : ℕ) (hmL : Nat.log p m ≤ L) :
    ∀ x ∈ Lat p D (r := r) j jp, (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) •
      (tieF (wv D i) (ev D i) ^ m) x) ∈ Lat p D (r := r) (j + Pi.single i m) jp := by
  intro x hx
  have := span_map_mem ((((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹)) •
    (tieF (wv D i) (ev D i) ^ m)) _ (Lat p D (r := r) (j + Pi.single i m) jp) ?_ x hx
  · simpa using this
  rintro v ⟨y, hy, g, hg, rfl⟩
  rw [LinearMap.smul_apply, tieF_pow_gen hB i y g
    (fun c => xi_free hg (fun d => wv_ne_xi hB i c d)) (fun c => xi_free hg (fun d => ev_ne_xi hB i c d)),
    ← smul_mul_assoc, ← map_smul]
  refine Submodule.subset_span ⟨_, yz_mk (Submodule.smul_mem _ _ (Y_iter hF i m j jp y (yz_y hy)))
    (int_Fpow L m hmL _ _ (yz_int hy)), g, hg, rfl⟩

end tieop

/- English proof (translation)
Introduce `p _ N r _ D hB hF j jp i m L hmL x hx`. Conclude with `lat_tie hB hF j jp i m L hmL x hx`.
-/
theorem lattice_equal_holds : LatTie := by
  intro p _ N r _ D hB hF j jp i m L hmL x hx
  exact lat_tie hB hF j jp i m L hmL x hx

end Formalism.InvariantFactorPaths.KP.LL
