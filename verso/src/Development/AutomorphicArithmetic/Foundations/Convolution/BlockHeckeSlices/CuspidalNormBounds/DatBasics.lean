import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CapPoly
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

open NumberField IsDedekindDomain GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.IdeleGroup
open UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

/- English proof (translation)
Establish `hw : ¬ w.IsReal` using `InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)`. Rewrite using `[← coe_infiniteProj, infiniteProj_posIdele]`. Express the relevant statement in the definitionally equal form `GroundTheory.Global.posRealElem w _ = _`. Unfold `GroundTheory.Global.posRealElem`. Rewrite using `[dif_neg hw]`.

Simplify using `[InfinitePlace.mult, hw, Real.sqrt_sq hs.le]`.
-/
private theorem posIdele_inf (s : ℝ) (hs : 0 < s) (w : InfinitePlace E) :
    ((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (s : ℂ) := by
  have hw : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  change GroundTheory.Global.posRealElem w _ = _
  unfold GroundTheory.Global.posRealElem
  rw [dif_neg hw]
  simp [InfinitePlace.mult, hw, Real.sqrt_sq hs.le]

private noncomputable def eU (E : Type) [Field E] (x : ℝ) : (Cinf E)ˣ where
  val := fun _ => (Real.exp x : ℂ)
  inv := fun _ => (Real.exp (-x) : ℂ)
  val_inv := funext fun _ => by simp [← Complex.exp_add]
  inv_val := funext fun _ => by simp [← Complex.exp_add]

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Use `set y : GL (Fin n) (Cinf E) := diagUnits n fun i => eU E (a i) with hy`. Establish `h2 : ((infGL E n y).val i j).2 = (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j` using `congrArg (fun g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) => g.val i j) (pFin_infGL y)`. Apply the tactic sequence `have h1 : ∀ w, ((infGL E n y).val i j).1 w = (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (y.val i j w) := fun w => congrFun (infGL_entry y i j) w`. Establish `hyv : y.val = Matrix.diagonal fun i => (fun _ : InfinitePlace E => (Real.exp (a i) : ℂ))` using `rfl`.

Rewrite using `[coe_diagUnits]`. Use `Prod.ext (funext fun w => ?_) ?_` and prove the remaining obligations. Rewrite using `[h1, hyv]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Rewrite using `[Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, posIdele_inf]`. Rewrite using `[Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]`. Conclude with `(map_zero _).symm`. Rewrite using `[h2]`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, Matrix.one_apply_eq]`. Conclude with `FiniteAdeleRing.ext E fun v => posIdele_finite _ _ v`. Rewrite using `[Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]`. Both sides reduce to the same expression.
-/
private theorem diag_eq (a : Fin n → ℝ) :
    (diagUnits n fun i => posIdele (K := E) (Real.exp (a i)) (Real.exp_pos _) : GA E n) =
      infGL E n (diagUnits n fun i => eU E (a i)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  set y : GL (Fin n) (Cinf E) := diagUnits n fun i => eU E (a i) with hy
  have h2 : ((infGL E n y).val i j).2 = (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j :=
    congrArg (fun g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) => g.val i j) (pFin_infGL y)
  have h1 : ∀ w, ((infGL E n y).val i j).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (y.val i j w) :=
    fun w => congrFun (infGL_entry y i j) w
  have hyv : y.val = Matrix.diagonal fun i => (fun _ : InfinitePlace E => (Real.exp (a i) : ℂ)) := rfl
  rw [coe_diagUnits]
  refine Prod.ext (funext fun w => ?_) ?_
  · rw [h1, hyv]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, posIdele_inf]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
      exact (map_zero _).symm
  · rw [h2]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact FiniteAdeleRing.ext E fun v => posIdele_finite _ _ v
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
      rfl

/- English proof (translation)
Rewrite using `[lie_eq_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `e : ∀ k l, coord τ (toL (Matrix.single i i (1 : Cinf E)) k l) = if i = k then if i = l then 1 else 0 else 0`. Introduce `k l`. Express the relevant statement in the definitionally equal form `coord τ (Matrix.single i i (1 : Cinf E) k l) = _`.

Rewrite using `[Matrix.single_apply]`. Apply the tactic sequence `by_cases h1 : i = k <;> by_cases h2 : i = l <;> simp [h1, h2]`. Simplify using `only [e]`. Simplify using the standard rewrite rules.
-/
private theorem sum_Eop (i : Fin n) : ∑ τ : E →+* ℂ, Eop τ i i = lie E n (toL (Matrix.single i i 1)) := by
  rw [lie_eq_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : ∀ k l, coord τ (toL (Matrix.single i i (1 : Cinf E)) k l) = if i = k then if i = l then 1 else 0 else 0 := by
    intro k l
    change coord τ (Matrix.single i i (1 : Cinf E) k l) = _
    rw [Matrix.single_apply]
    by_cases h1 : i = k <;> by_cases h2 : i = l <;> simp [h1, h2]
  simp only [e]
  simp

/- English proof (translation)
Rewrite using `[lie_eq_sum]`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `e : ∀ l, coord τ (oneL E n k l) = if k = l then 1 else 0`. Introduce `l`. Express the relevant statement in the definitionally equal form `coord τ ((1 : Matrix (Fin n) (Fin n) (Cinf E)) k l) = _`.

Rewrite using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [e]`. Simplify using the standard rewrite rules.
-/
private theorem lie_one : lie E n (oneL E n) = ∑ τ : E →+* ℂ, ∑ i, Eop τ i i := by
  rw [lie_eq_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ l, coord τ (oneL E n k l) = if k = l then 1 else 0 := by
    intro l
    change coord τ ((1 : Matrix (Fin n) (Fin n) (Cinf E)) k l) = _
    rw [Matrix.one_apply]
    split_ifs <;> simp
  simp only [e]
  simp

/- English proof (translation)
Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Establish `hd : HasDerivAt (fun t : ℝ => toL (diagUnits n fun _ => eU E t : GL (Fin n) (Cinf E)).val) (oneL E n) 0`. Establish `e : (fun t : ℝ => toL (diagUnits n fun _ => eU E t : GL (Fin n) (Cinf E)).val) = fun t : ℝ => Real.exp t • oneL E n`. Use function extensionality and compare the values at `t k l w`. Express the relevant statement in the definitionally equal form `(Matrix.diagonal fun _ => (fun _ : InfinitePlace E => (Real.exp t : ℂ))) k l w = Real.exp t • (1 : Matrix (Fin n) (Fin n) (Cinf E)) k l w`.

Distinguish the cases in `h : k = l`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Rewrite using `[e]`.

Simplify using `using (Real.hasDerivAt_exp 0).smul_const (oneL E n)`. Establish `h0 : (diagUnits n fun _ => eU E 0 : GL (Fin n) (Cinf E)) = 1`. Rewrite using `[← map_one (diagUnits n)]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `Units.ext (funext fun _ => by simp [eU])`. Establish `h1` using `hasDerivAt_curve f g (fun t => diagUnits n fun _ => eU E t) _ h0 hd`. Establish `e : (fun t : ℝ => f.1 (g * infGL E n (diagUnits n fun _ => eU E t))) = fun _ => f.1 g`. Use function extensionality and compare the values at `t`. Establish `ha : (n : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne'`.

Establish `hd : (Module.finrank ℚ E : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Establish `e : rpowHom ((n * Module.finrank ℚ E : ℝ))⁻¹ ⟨Real.exp (n * Module.finrank ℚ E * t), Real.exp_pos _⟩ = ⟨Real.exp t, Real.exp_pos t⟩`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Real.exp (n * Module.finrank ℚ E * t) ^ ((n * Module.finrank ℚ E : ℝ))⁻¹ = Real.exp t`. Rewrite using `[← Real.exp_mul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[← h (n * Module.finrank ℚ E * t) g, ← diag_eq, zt, centralSection_mul_comm, centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, e]`. Both sides reduce to the same expression. Rewrite `h1` using `[e]`.

Conclude with `h1.unique (hasDerivAt_const _ _)`.
-/
private theorem lie_one_eq_zero (hn : 0 < n) (f : Sm E n) (h : ∀ t g, f.1 (zt E n t * g) = f.1 g) :
    lie E n (oneL E n) f = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have hd : HasDerivAt (fun t : ℝ => toL (diagUnits n fun _ => eU E t : GL (Fin n) (Cinf E)).val) (oneL E n) 0 := by
    have e : (fun t : ℝ => toL (diagUnits n fun _ => eU E t : GL (Fin n) (Cinf E)).val) =
        fun t : ℝ => Real.exp t • oneL E n := by
      funext t k l w
      change (Matrix.diagonal fun _ => (fun _ : InfinitePlace E => (Real.exp t : ℂ))) k l w =
        Real.exp t • (1 : Matrix (Fin n) (Fin n) (Cinf E)) k l w
      by_cases h : k = l
      · subst h; simp
      · simp [h]
    rw [e]
    simpa using (Real.hasDerivAt_exp 0).smul_const (oneL E n)
  have h0 : (diagUnits n fun _ => eU E 0 : GL (Fin n) (Cinf E)) = 1 := by
    rw [← map_one (diagUnits n)]
    congr 1
    funext i
    exact Units.ext (funext fun _ => by simp [eU])
  have h1 := hasDerivAt_curve f g (fun t => diagUnits n fun _ => eU E t) _ h0 hd
  have e : (fun t : ℝ => f.1 (g * infGL E n (diagUnits n fun _ => eU E t))) = fun _ => f.1 g := by
    funext t
    have ha : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    have e : rpowHom ((n * Module.finrank ℚ E : ℝ))⁻¹ ⟨Real.exp (n * Module.finrank ℚ E * t), Real.exp_pos _⟩ =
        ⟨Real.exp t, Real.exp_pos t⟩ := by
      refine Subtype.ext ?_
      change Real.exp (n * Module.finrank ℚ E * t) ^ ((n * Module.finrank ℚ E : ℝ))⁻¹ = Real.exp t
      rw [← Real.exp_mul]
      congr 1
      field_simp
    rw [← h (n * Module.finrank ℚ E * t) g, ← diag_eq, zt, centralSection_mul_comm, centralSection, MonoidHom.comp_apply,
      MonoidHom.comp_apply, e]
    rfl
  rw [e] at h1
  exact h1.unique (hasDerivAt_const _ _)

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `(Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_` and prove the remaining obligations. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Take `⟨p, -, -, h3, h4⟩` from `exists_capPoly (Eop (a := m + 1) τ) (ℓ ∘ₗ LinearMap.applyₗ f)`. Establish `e : p = Polynomial.C (ℓ f) * ∏ i, (Polynomial.X - Polynomial.C (-Λ i))`.

Use `Polynomial.funext fun u => ?_` and prove the remaining obligations. Rewrite using `[h4]`. Express the relevant statement in the definitionally equal form `ℓ (cap τ u f) = _`. Rewrite using `[h, map_smul]`. Simplify using `[Polynomial.eval_prod, mul_comm]`.

Establish `h5` using `h3 m rfl`. Establish `h6` using `Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin (m + 1))) (fun i => -Λ i) (by simp)`. Rewrite `h6` using `[Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]`. Rewrite `h5` using `[e, Polynomial.coeff_C_mul, h6]`. Rewrite using `[map_sub, map_smul, sub_eq_zero]`.

Use `h5.symm.trans ?_` and prove the remaining obligations. Simplify using `[mul_comm]`.
-/
private theorem trace_eq {f : Sm E n} {τ : E →+* ℂ} {Λ : Fin n → ℂ} (hn : 0 < n)
    (h : ∀ u, cap τ u f = (∏ i, (u + Λ i)) • f) : (∑ i, Eop τ i i) f = (∑ i, Λ i) • f := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨p, -, -, h3, h4⟩ := exists_capPoly (Eop (a := m + 1) τ) (ℓ ∘ₗ LinearMap.applyₗ f)
  have e : p = Polynomial.C (ℓ f) * ∏ i, (Polynomial.X - Polynomial.C (-Λ i)) := by
    refine Polynomial.funext fun u => ?_
    rw [h4]
    change ℓ (cap τ u f) = _
    rw [h, map_smul]
    simp [Polynomial.eval_prod, mul_comm]
  have h5 := h3 m rfl
  have h6 := Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin (m + 1))) (fun i => -Λ i) (by simp)
  rw [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] at h6
  rw [e, Polynomial.coeff_C_mul, h6] at h5
  rw [map_sub, map_smul, sub_eq_zero]
  refine h5.symm.trans ?_
  simp [mul_comm]

/- English proof (translation)
Establish `h` using `lie_one_eq_zero b.pos b.f b.cen`. Rewrite `h` using `[lie_one, LinearMap.sum_apply, Finset.sum_congr rfl fun τ _ => trace_eq b.pos (b.inf τ), ← Finset.sum_smul]`. Conclude with `(smul_eq_zero.1 h).resolve_right b.ne`.
-/
private theorem blo_sum {S : Set (Pl E)} (b : Blo S n) : ∑ τ, ∑ i, b.Λ τ i = 0 := by
  have h := lie_one_eq_zero b.pos b.f b.cen
  rw [lie_one, LinearMap.sum_apply, Finset.sum_congr rfl fun τ _ => trace_eq b.pos (b.inf τ), ← Finset.sum_smul] at h
  exact (smul_eq_zero.1 h).resolve_right b.ne

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, by rw [Dat.J, Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop i]⟩`.
-/
private theorem J_eq {S : Set (Pl E)} (d : Dat S n) (j : Fin d.len) : ∃ c : ℂ,
    d.J j = c • ∑ i ∈ Finset.univ.filter fun i => d.idx i = j, lie E n (toL (Matrix.single i i 1)) :=
  ⟨_, by rw [Dat.J, Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop i]⟩

/- English proof (translation)
Establish `h` using `isLieHom_ιC (E := E) (a := n) (Matrix.single i i 1) (Matrix.single l l 1)`. Establish `e : Matrix.single i i (1 : Cinf E) * Matrix.single l l 1 - Matrix.single l l 1 * Matrix.single i i 1 = 0`. Distinguish the cases in `h : i = l`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.single_mul_single_of_ne _ _ _ _ h, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h), sub_zero]`. Rewrite `h` using `[e]`. Establish `h2` using `congrArg (uC E n) h`. Simplify using `only [map_sub, map_mul, uC_ιC] at h2`. Establish `z : lie E n (toL 0) = 0` using `map_zero (lie E n)`.

Rewrite `h2` using `[z]`. Apply the tactic sequence `first | exact sub_eq_zero.1 h2 | exact sub_eq_zero.1 h2.symm`.
-/
private theorem comm_lie (i l : Fin n) :
    Commute (lie E n (toL (Matrix.single i i 1))) (lie E n (toL (Matrix.single l l 1))) := by
  have h := isLieHom_ιC (E := E) (a := n) (Matrix.single i i 1) (Matrix.single l l 1)
  have e : Matrix.single i i (1 : Cinf E) * Matrix.single l l 1 - Matrix.single l l 1 * Matrix.single i i 1 = 0 := by
    by_cases h : i = l
    · subst h; simp
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h), sub_zero]
  rw [e] at h
  have h2 := congrArg (uC E n) h
  simp only [map_sub, map_mul, uC_ιC] at h2
  have z : lie E n (toL 0) = 0 := map_zero (lie E n)
  rw [z] at h2
  first | exact sub_eq_zero.1 h2 | exact sub_eq_zero.1 h2.symm

/- English proof (translation)
Establish `h` using `GlobalTheory.CapAdInv.rt_lie (E := E) (diagUnits n a) (Matrix.single i i 1)`. Establish `e : (diagUnits n a).val * Matrix.single i i (1 : Cinf E) * ((diagUnits n a)⁻¹).val = Matrix.single i i 1`. Rewrite using `[Units.mul_inv_eq_iff_eq_mul, coe_diagUnits]`. Use extensionality with `k l`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]`.

Use `split_ifs with h`. Take `⟨rfl, rfl⟩` from `h`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite `h` using `[e]`.

Conclude with `h.symm`.
-/
private theorem comm_rt (i : Fin n) (a : Fin n → (Cinf E)ˣ) :
    Commute (lie E n (toL (Matrix.single i i 1))) (rt E n (infGL E n (diagUnits n a))) := by
  have h := GlobalTheory.CapAdInv.rt_lie (E := E) (diagUnits n a) (Matrix.single i i 1)
  have e : (diagUnits n a).val * Matrix.single i i (1 : Cinf E) * ((diagUnits n a)⁻¹).val = Matrix.single i i 1 := by
    rw [Units.mul_inv_eq_iff_eq_mul, coe_diagUnits]
    ext k l
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · simp
  rw [e] at h
  exact h.symm

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `nil => exact ⟨fun j => j.elim0, le_rfl, fun j => j.elim0, fun j => j.elim0⟩`. Consider the case `@cons r s b d ih`. Take `⟨h1, h2, h3, h4⟩` from `ih`. Set `I : Fin (r + s) → Fin (d.len + 1)` to `Fin.addCases (fun _ => 0) fun i => (d.idx i).succ`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∀ j : Fin (d.len + 1), ∃ i, I i = j`. Use `Fin.cases ⟨Fin.castAdd s ⟨0, b.pos⟩, Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) _⟩ fun j => ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `h1 j`. Conclude with `⟨Fin.natAdd r i, by simp [I]⟩`.

Use `b.pos` as an intermediate fact. Express the relevant statement in the definitionally equal form `d.len + 1 ≤ _`. Use linear arithmetic over natural numbers and integers. Express the relevant statement in the definitionally equal form `∀ j : Fin (d.len + 1), ∑ τ, ∑ i, (if I i = j then Fin.addCases (motive := fun _ => ℂ) (b.Λ τ) (d.lam τ) i else 0) = 0`. Simplify using `only [Fin.sum_univ_add, I, Fin.addCases_left, Fin.addCases_right]`.

Use `Fin.cases ?_ fun j => ?_` and prove the remaining obligations. Simplify `blo_sum b` using `[Fin.succ_ne_zero]`. Simplify `h3 j` using `[(Fin.succ_ne_zero _).symm]`. Express the relevant statement in the definitionally equal form `∀ (j : Fin (d.len + 1)) w, w ∉ S → (Fin.cases (motive := fun _ => Pl E → Multiset ℂˣ) b.sat d.sat j w).card = ∑ i, if I i = j then 1 else 0`. Simplify using `only [Fin.sum_univ_add, I, Fin.addCases_left, Fin.addCases_right]`.

Use `Fin.cases (fun w hw => ?_) fun j w hw => ?_` and prove the remaining obligations. Simplify `(b.isSat w hw).2.2.1` using `[Fin.succ_ne_zero]`. Simplify `h4 j w hw` using `[(Fin.succ_ne_zero _).symm]`.
-/
private theorem comb {S : Set (Pl E)} (d : Dat S n) : Function.Surjective d.idx ∧ d.len ≤ n ∧
    (∀ j, ∑ τ, ∑ i, (if d.idx i = j then d.lam τ i else 0) = 0) ∧
    ∀ j w, w ∉ S → (d.sat j w).card = ∑ i, if d.idx i = j then 1 else 0 := by
  induction d with
  | nil => exact ⟨fun j => j.elim0, le_rfl, fun j => j.elim0, fun j => j.elim0⟩
  | @cons r s b d ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    let I : Fin (r + s) → Fin (d.len + 1) := Fin.addCases (fun _ => 0) fun i => (d.idx i).succ
    refine ⟨?_, ?_, ?_, ?_⟩
    · change ∀ j : Fin (d.len + 1), ∃ i, I i = j
      refine Fin.cases ⟨Fin.castAdd s ⟨0, b.pos⟩, Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) _⟩ fun j => ?_
      obtain ⟨i, rfl⟩ := h1 j
      exact ⟨Fin.natAdd r i, by simp [I]⟩
    · have := b.pos
      change d.len + 1 ≤ _
      omega
    · change ∀ j : Fin (d.len + 1), ∑ τ, ∑ i, (if I i = j then
        Fin.addCases (motive := fun _ => ℂ) (b.Λ τ) (d.lam τ) i else 0) = 0
      simp only [Fin.sum_univ_add, I, Fin.addCases_left, Fin.addCases_right]
      refine Fin.cases ?_ fun j => ?_
      · simpa [Fin.succ_ne_zero] using blo_sum b
      · simpa [(Fin.succ_ne_zero _).symm] using h3 j
    · change ∀ (j : Fin (d.len + 1)) w, w ∉ S →
        (Fin.cases (motive := fun _ => Pl E → Multiset ℂˣ) b.sat d.sat j w).card = ∑ i, if I i = j then 1 else 0
      simp only [Fin.sum_univ_add, I, Fin.addCases_left, Fin.addCases_right]
      refine Fin.cases (fun w hw => ?_) fun j w hw => ?_
      · simpa [Fin.succ_ne_zero] using (b.isSat w hw).2.2.1
      · simpa [(Fin.succ_ne_zero _).symm] using h4 j w hw

end UpperTheory.ConvolutionTheory.BW

/- English proof (translation)
Introduce `E _ _ _`. Use `⟨fun S r b => blo_sum b, fun S n d => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, h3, h4⟩` from `comb d`. Establish `hp : ∀ x : ℝ, posIdele (K` using `E) (Real.exp x) (Real.exp_pos x) = posIdeleHom E ⟨Real.exp x, Real.exp_pos x⟩ := fun _ => rfl`. Use `⟨h1, h2, fun j => ?_, fun j w hw => ?_, ?_, fun v v' => ?_, fun v => ⟨_, diag_eq _⟩, fun j l => ?_, fun j v => ?_, fun j => ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.sum_filter, Fintype.sum_prod_type]`. Conclude with `h3 j`. Rewrite using `[h4 j w hw, Dat.size, Finset.card_filter]`. Rewrite using `[Dat.tr, ← map_one (diagUnits n)]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Rewrite using `[hp, Pi.one_apply, ← map_one (posIdeleHom E)]`. Use `congr 1`. Conclude with `Subtype.ext (by simp)`. Rewrite using `[Dat.tr, Dat.tr, Dat.tr, ← map_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.mul_apply, hp, hp, hp, ← map_mul]`. Use `congr 1`. Conclude with `Subtype.ext (by simp [add_div, Real.exp_add])`.

Take `⟨c, hc⟩` from `J_eq d j`. Take `⟨c', hc'⟩` from `J_eq d l`. Rewrite using `[hc, hc']`. Conclude with `((Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun k _ => comm_lie i k).smul_left c).smul_right c'`. Take `⟨c, hc⟩` from `J_eq d j`.

Take `⟨a, ha⟩ : ∃ a : Fin n → (Cinf E)ˣ, d.tr v = infGL E n (diagUnits n a)` from `⟨_, diag_eq _⟩`. Rewrite using `[hc, ha]`. Conclude with `(Commute.sum_left _ _ _ fun i _ => comm_rt i a).smul_left c`. Take `⟨c, hc⟩` from `J_eq d j`. Conclude with `⟨c • ∑ i ∈ Finset.univ.filter fun i => d.idx i = j, ιC E n (toL (Matrix.single i i 1)), by`.

Rewrite using `[map_smul, map_sum, Finset.sum_congr rfl fun i _ => uC_ιC _]`. Conclude with `hc⟩`.
-/
theorem UpperTheory.ConvolutionTheory.BW.datBasics :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.DatBasics E := by
  intro E _ _ _
  refine ⟨fun S r b => blo_sum b, fun S n d => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := comb d
  have hp : ∀ x : ℝ, posIdele (K := E) (Real.exp x) (Real.exp_pos x) = posIdeleHom E ⟨Real.exp x, Real.exp_pos x⟩ :=
    fun _ => rfl
  refine ⟨h1, h2, fun j => ?_, fun j w hw => ?_, ?_, fun v v' => ?_, fun v => ⟨_, diag_eq _⟩, fun j l => ?_,
    fun j v => ?_, fun j => ?_⟩
  · rw [Finset.sum_filter, Fintype.sum_prod_type]
    exact h3 j
  · rw [h4 j w hw, Dat.size, Finset.card_filter]
  · rw [Dat.tr, ← map_one (diagUnits n)]
    congr 1
    funext i
    rw [hp, Pi.one_apply, ← map_one (posIdeleHom E)]
    congr 1
    exact Subtype.ext (by simp)
  · rw [Dat.tr, Dat.tr, Dat.tr, ← map_mul]
    congr 1
    funext i
    rw [Pi.mul_apply, hp, hp, hp, ← map_mul]
    congr 1
    exact Subtype.ext (by simp [add_div, Real.exp_add])
  · obtain ⟨c, hc⟩ := J_eq d j
    obtain ⟨c', hc'⟩ := J_eq d l
    rw [hc, hc']
    exact ((Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun k _ => comm_lie i k).smul_left c).smul_right c'
  · obtain ⟨c, hc⟩ := J_eq d j
    obtain ⟨a, ha⟩ : ∃ a : Fin n → (Cinf E)ˣ, d.tr v = infGL E n (diagUnits n a) := ⟨_, diag_eq _⟩
    rw [hc, ha]
    exact (Commute.sum_left _ _ _ fun i _ => comm_rt i a).smul_left c
  · obtain ⟨c, hc⟩ := J_eq d j
    exact ⟨c • ∑ i ∈ Finset.univ.filter fun i => d.idx i = j, ιC E n (toL (Matrix.single i i 1)), by
      rw [map_smul, map_sum, Finset.sum_congr rfl fun i _ => uC_ιC _]
      exact hc⟩
