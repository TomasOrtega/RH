import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddWeightCycles.WOneOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.Weights

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.BlockEvaluationBounds

open BlockInvariants BlockInvariants.AlternatingWeights

namespace AlternatingWeights

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Unfold `tmC`. Rewrite using `[if_pos (fun _ => rfl), if_pos (fun _ => rfl)]`. Simplify using `only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.mkPiAlgebra_apply, LinearMap.coe_toContinuousLinearMap', Function.comp_apply]`. Use `Fintype.sum_equiv (Equiv.arrowCongr c (Equiv.refl _)) _ _ (fun a => ?_)` and prove the remaining obligations. Use `Fintype.prod_equiv c _ _ (fun i => ?_)` and prove the remaining obligations.

Simplify using `[Equiv.arrowCongr_apply, Equiv.Perm.mul_apply]`.
-/
theorem tmC_relabel {N q : ℕ} (ρ c : Equiv.Perm (Fin q)) (w0 : InfinitePlace L) (Y : Fin q → HS L N) :
    tmC (c⁻¹ * ρ * c) (fun _ => w0) Y = tmC ρ (fun _ => w0) (Y ∘ ⇑c⁻¹) := by
  unfold tmC
  rw [if_pos (fun _ => rfl), if_pos (fun _ => rfl)]
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, LinearMap.coe_toContinuousLinearMap', Function.comp_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr c (Equiv.refl _)) _ _ (fun a => ?_)
  refine Fintype.prod_equiv c _ _ (fun i => ?_)
  simp [Equiv.arrowCongr_apply, Equiv.Perm.mul_apply]

/- English proof (translation)
Unfold `tmC`. Rewrite using `[if_pos (fun _ => rfl), if_pos (fun _ => rfl)]`. Simplify using `only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.mkPiAlgebra_apply, LinearMap.coe_toContinuousLinearMap', star_sum, star_prod]`. Use `Fintype.sum_equiv (Equiv.arrowCongr ρ (Equiv.refl _)) _ _ (fun b => ?_)` and prove the remaining obligations. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Simplify using `only [ent, mat, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_id, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]`. Establish `hh` using `((Y i).2 w0).apply (b i) (b (ρ⁻¹ i))`. Simplify using `only [Matrix.of_apply] at hh ⊢`. Simplify using `only [id, Equiv.symm_apply_apply, ← Equiv.Perm.inv_def]`. Establish `e : ρ⁻¹ (ρ i) = i` using `by simp`.

Rewrite using `[e]`. Conclude with `hh.symm`.
-/
theorem tmC_inv_star {N q : ℕ} (ρ : Equiv.Perm (Fin q)) (w0 : InfinitePlace L) (Y : Fin q → HS L N) :
    tmC ρ⁻¹ (fun _ => w0) Y = star (tmC ρ (fun _ => w0) Y) := by
  unfold tmC
  rw [if_pos (fun _ => rfl), if_pos (fun _ => rfl)]
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, LinearMap.coe_toContinuousLinearMap', star_sum, star_prod]
  refine Fintype.sum_equiv (Equiv.arrowCongr ρ (Equiv.refl _)) _ _ (fun b => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [ent, mat, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_id, Function.comp_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  have hh := ((Y i).2 w0).apply (b i) (b (ρ⁻¹ i))
  simp only [Matrix.of_apply] at hh ⊢
  simp only [id, Equiv.symm_apply_apply, ← Equiv.Perm.inv_def]
  have e : ρ⁻¹ (ρ i) = i := by simp
  rw [e]
  exact hh.symm

/- English proof (translation)
Break down `q with _ | n` into its components or cases. Conclude with `Subsingleton.elim _ _`. Rewrite using `[eq_inv_iff_mul_eq_one]`. Use extensionality with `i`. Simplify using `[Equiv.Perm.inv_def, finRotate_succ_apply, Fin.revPerm_apply, Fin.rev_add]`.
-/
theorem rot_rev (q : ℕ) :
    (Fin.revPerm : Equiv.Perm (Fin q))⁻¹ * finRotate q * Fin.revPerm = (finRotate q)⁻¹ := by
  rcases q with _ | n
  · exact Subsingleton.elim _ _
  · rw [eq_inv_iff_mul_eq_one]
    ext i
    simp [Equiv.Perm.inv_def, finRotate_succ_apply, Fin.revPerm_apply, Fin.rev_add]

/- English proof (translation)
Use extensionality with `v`. Rewrite using `[ContinuousAlternatingMap.smul_apply, ContinuousMultilinearMap.alternatization_apply_apply, ContinuousMultilinearMap.alternatization_apply_apply, Finset.smul_sum]`. Use `Fintype.sum_equiv (Equiv.mulRight τ) _ _ (fun σ => ?_)` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, h, Equiv.Perm.coe_mul, Function.comp_assoc]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hs | hs <;> simp [hs]`.
-/
theorem alt_relabel {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℕ}
    (f g : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) (τ : Equiv.Perm (Fin q))
    (h : ∀ v, f v = g (v ∘ τ)) :
    ContinuousMultilinearMap.alternatization f =
      ((Equiv.Perm.sign τ : ℤ) : ℝ) • ContinuousMultilinearMap.alternatization g := by
  ext v
  rw [ContinuousAlternatingMap.smul_apply, ContinuousMultilinearMap.alternatization_apply_apply,
    ContinuousMultilinearMap.alternatization_apply_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ (fun σ => ?_)
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, h, Equiv.Perm.coe_mul, Function.comp_assoc]
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hs | hs <;> simp [hs]

/- English proof (translation)
Establish `h2` using `alt_relabel f (-f) σ (fun v => by`. Rewrite using `[ContinuousMultilinearMap.neg_apply, hf, neg_neg])`. Rewrite `h2` using `[hs, map_neg]`. Use extensionality with `v`. Establish `h3` using `congrArg (fun F => F v) h2`.

Simplify using `at h3`. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem alt_zero' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) (σ : Equiv.Perm (Fin q))
    (hf : ∀ v, f (v ∘ σ) = -f v) (hs : Equiv.Perm.sign σ = 1) :
    ContinuousMultilinearMap.alternatization f = 0 := by
  have h2 := alt_relabel f (-f) σ (fun v => by
    rw [ContinuousMultilinearMap.neg_apply, hf, neg_neg])
  rw [hs, map_neg] at h2
  ext v
  have h3 := congrArg (fun F => F v) h2
  simp at h3
  simp
  linarith

/- English proof (translation)
Take `⟨k, rfl⟩` from `hab`. Establish `key : ∀ n : ℕ, ∀ x, w ((σ ^ n) x) = w x`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x`.

Both sides reduce to the same expression. Consider the case `succ n ih => intro x`. Rewrite using `[pow_succ', Equiv.Perm.mul_apply, hw, ih]`. Break down `k with n | n` into its components or cases. Simplify using `only [Int.ofNat_eq_coe, zpow_natCast]`.

Conclude with `(key n a).symm`. Establish `e : (σ ^ (n + 1)) ((σ ^ (n + 1))⁻¹ a) = a` using `by simp`. Rewrite using `[zpow_negSucc, ← key (n + 1) ((σ ^ (n + 1))⁻¹ a), e]`.
-/
theorem const_of_cycle {q : ℕ} {α : Type} (σ : Equiv.Perm (Fin q)) (w : Fin q → α)
    (hw : ∀ i, w (σ i) = w i) (a b : Fin q) (hab : σ.SameCycle a b) : w a = w b := by
  obtain ⟨k, rfl⟩ := hab
  have key : ∀ n : ℕ, ∀ x, w ((σ ^ n) x) = w x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ', Equiv.Perm.mul_apply, hw, ih]
  rcases k with n | n
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact (key n a).symm
  · have e : (σ ^ (n + 1)) ((σ ^ (n + 1))⁻¹ a) = a := by simp
    rw [zpow_negSucc, ← key (n + 1) ((σ ^ (n + 1))⁻¹ a), e]

/- English proof (translation)
Establish `h1` using `(Nat.card_eq_one_iff_unique.mp h).1`. Conclude with `Quotient.exact (Subsingleton.elim (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x) (Quotient.mk _ y))`.
-/
theorem sameCycle_of_ncyc {q : ℕ} (σ : Equiv.Perm (Fin q)) (h : ncyc σ = 1) (x y : Fin q) : σ.SameCycle x y := by
  have h1 := (Nat.card_eq_one_iff_unique.mp h).1
  exact Quotient.exact (Subsingleton.elim (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x) (Quotient.mk _ y))

/- English proof (translation)
Break down `q with _ | _ | n` into its components or cases. Conclude with `⟨1, Subsingleton.elim _ _⟩`. Use `⟨1, ?_⟩` and prove the remaining obligations. Apply `Equiv.ext` to reduce the goal to its premises. Introduce `i`.

Apply `Fin.ext` to reduce the goal to its premises. Establish `h1` using `(σ i).2`. Establish `h2` using `((1⁻¹ * finRotate (0 + 1) * 1 : Equiv.Perm (Fin (0 + 1))) i).2`. Use linear arithmetic over natural numbers and integers. Establish `hsc` using `sameCycle_of_ncyc σ h`.

Establish `hne : σ ≠ 1`. Introduce `h1`. Establish `h01` using `hsc 0 1`. Rewrite `h01` using `[h1]`. Simplify using `at h01`.

Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, σ x ≠ x := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hne (Equiv.ext hc)`. Establish `hall : ∀ y, σ y ≠ y` using `fun y hy => hx (((hsc x y).apply_eq_self_iff).mpr hy)`.

Establish `hcyc : σ.IsCycle` using `⟨x, hx, fun y _ => hsc x y⟩`. Establish `hsupp : σ.support = Finset.univ`. Use extensionality with `y`. Simplify using `[Equiv.Perm.mem_support, hall y]`. Establish `hct : σ.cycleType = (finRotate (n + 2)).cycleType`.

Rewrite using `[hcyc.cycleType, isCycle_finRotate.cycleType, hsupp, support_finRotate]`. Take `⟨c, hc⟩` from `isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr hct)`. Conclude with `⟨c, by rw [← hc]; group⟩`.
-/
theorem conj_rot {q : ℕ} (σ : Equiv.Perm (Fin q)) (h : ncyc σ = 1) :
    ∃ c : Equiv.Perm (Fin q), σ = c⁻¹ * finRotate q * c := by
  rcases q with _ | _ | n
  · exact ⟨1, Subsingleton.elim _ _⟩
  · refine ⟨1, ?_⟩
    apply Equiv.ext
    intro i
    apply Fin.ext
    have h1 := (σ i).2
    have h2 := ((1⁻¹ * finRotate (0 + 1) * 1 : Equiv.Perm (Fin (0 + 1))) i).2
    omega
  · have hsc := sameCycle_of_ncyc σ h
    have hne : σ ≠ 1 := by
      intro h1
      have h01 := hsc 0 1
      rw [h1] at h01
      simp at h01
    obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
      by_contra hc
      push_neg at hc
      exact hne (Equiv.ext hc)
    have hall : ∀ y, σ y ≠ y := fun y hy => hx (((hsc x y).apply_eq_self_iff).mpr hy)
    have hcyc : σ.IsCycle := ⟨x, hx, fun y _ => hsc x y⟩
    have hsupp : σ.support = Finset.univ := by
      ext y
      simp [Equiv.Perm.mem_support, hall y]
    have hct : σ.cycleType = (finRotate (n + 2)).cycleType := by
      rw [hcyc.cycleType, isCycle_finRotate.cycleType, hsupp, support_finRotate]
    obtain ⟨c, hc⟩ := isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr hct)
    exact ⟨c, by rw [← hc]; group⟩

end AlternatingWeights

open AlternatingWeights

/- English proof (translation)
Introduce `q hq`. Establish `hs : ∀ x y : Fin q, (finRotate q).SameCycle x y`. Introduce `x y`. Break down `q with _ | _ | n` into its components or cases. Conclude with `x.elim0`.

Take `rfl : x = y` from `Fin.ext (by have := x.2; have := y.2; omega)`. Conclude with `Equiv.Perm.SameCycle.refl _ _`. Conclude with `isCycle_finRotate.sameCycle (by rw [← Equiv.Perm.mem_support, support_finRotate]; exact Finset.mem_univ _) (by rw [← Equiv.Perm.mem_support, support_finRotate]; exact Finset.mem_univ _)`. Rewrite using `[ncyc, Nat.card_eq_one_iff_unique]`. Conclude with `⟨⟨fun a b => Quotient.inductionOn₂ a b (fun x y => Quotient.sound (hs x y))⟩, ⟨Quotient.mk _ ⟨0, hq⟩⟩⟩`.
-/
theorem wRot : WRot := by
  intro q hq
  have hs : ∀ x y : Fin q, (finRotate q).SameCycle x y := by
    intro x y
    rcases q with _ | _ | n
    · exact x.elim0
    · obtain rfl : x = y := Fin.ext (by have := x.2; have := y.2; omega)
      exact Equiv.Perm.SameCycle.refl _ _
    · exact isCycle_finRotate.sameCycle
        (by rw [← Equiv.Perm.mem_support, support_finRotate]; exact Finset.mem_univ _)
        (by rw [← Equiv.Perm.mem_support, support_finRotate]; exact Finset.mem_univ _)
  rw [ncyc, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Quotient.inductionOn₂ a b (fun x y => Quotient.sound (hs x y))⟩,
    ⟨Quotient.mk _ ⟨0, hq⟩⟩⟩

/- English proof (translation)
Introduce `L _ _ N q x hodd hx`. Take `⟨σ, w, ε⟩` from `x`. Establish `hq : 0 < q` using `hodd.pos`. Establish `hx' : ncyc σ = 1` using `hx`. Distinguish the cases in `hw : ∀ i, w (σ i) = w i`.

Take `⟨w0, rfl⟩ : ∃ w0, w = fun _ => w0` from `⟨w ⟨0, hq⟩, funext fun i => const_of_cycle σ w hw i ⟨0, hq⟩ (sameCycle_of_ncyc σ hx' i ⟨0, hq⟩)⟩`. Take `⟨c, rfl⟩` from `conj_rot σ hx'`. Establish `hrel : AT (N` using `N) ((c⁻¹ * finRotate q * c, fun _ => w0, ε) : Pat L q) = ((Equiv.Perm.sign c⁻¹ : ℤ) : ℝ) • AT (N := N) ((finRotate q, fun _ => w0, ε) : Pat L q) := by`. Simplify using `only [AT]`. Apply `alt_relabel` to reduce the goal to its premises.

Introduce `v`. Simplify using `only [tmR, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, tmC_relabel]`. Establish `hrev : ∀ Y : Fin q → HS L N, tmC (finRotate q) (fun _ => w0) (Y ∘ ⇑(Fin.revPerm : Equiv.Perm (Fin q))⁻¹) = star (tmC (finRotate q) (fun _ => w0) Y)`. Introduce `Y`. Rewrite using `[← tmC_relabel, rot_rev, tmC_inv_star]`.

Establish `hrev' : ∀ Y : Fin q → HS L N, tmC (finRotate q) (fun _ => w0) (Y ∘ ⇑(Fin.revPerm : Equiv.Perm (Fin q))) = star (tmC (finRotate q) (fun _ => w0) Y)`. Introduce `Y`. Simplify using `using hrev Y`. Establish `hvan : AT (N` using `N) ((finRotate q, fun _ => w0, true) : Pat L q) = 0 ∨ AT (N := N) ((finRotate q, fun _ => w0, false) : Pat L q) = 0 := by`. Break down `Int.units_eq_one_or (Equiv.Perm.sign ((Fin.revPerm : Equiv.Perm (Fin q))⁻¹)) with hs | hs` into its components or cases.

Use `left`. Simplify using `only [AT]`. Apply `alt_zero' _ ((Fin.revPerm : Equiv.Perm (Fin q))⁻¹) _ hs` to reduce the goal to its premises. Introduce `v`. Simplify using `[tmR, hrev']`.

Use `right`. Establish `h2` using `alt_relabel (tmR (N := N) (finRotate q) (fun _ => w0) false) (tmR (finRotate q) (fun _ => w0) false) ((Fin.revPerm : Equiv.Perm (Fin q))⁻¹) (fun v => by simp [tmR, hrev'])`. Rewrite `h2` using `[hs]`. Simplify using `only [AT]`. Use extensionality with `v`.

Establish `h3` using `congrArg (fun F => F v) h2`. Simplify using `at h3`. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Apply the tactic sequence `rcases hvan with h0 | h0 <;> cases ε`.

Conclude with `⟨((Equiv.Perm.sign c⁻¹ : ℤ) : ℝ), w0, by rw [hrel, h0, add_zero]⟩`. Conclude with `⟨0, w0, by rw [hrel, h0, smul_zero, zero_smul]⟩`. Conclude with `⟨0, w0, by rw [hrel, h0, smul_zero, zero_smul]⟩`. Conclude with `⟨((Equiv.Perm.sign c⁻¹ : ℤ) : ℝ), w0, by rw [hrel, h0, zero_add]⟩`. Use `⟨0, w ⟨0, hq⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[zero_smul]`. Establish `h0 : tmR (N` using `N) σ w ε = 0 := by`. Use extensionality with `v`. Simplify using `only [tmR, tmC, if_neg hw, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, ContinuousMultilinearMap.zero_apply, map_zero]`. Simplify using `only [AT]`.

Rewrite using `[h0, map_zero]`.
-/
theorem wOneOdd : WOneOdd := by
  intro L _ _ N q x hodd hx
  obtain ⟨σ, w, ε⟩ := x
  have hq : 0 < q := hodd.pos
  have hx' : ncyc σ = 1 := hx
  by_cases hw : ∀ i, w (σ i) = w i
  · obtain ⟨w0, rfl⟩ : ∃ w0, w = fun _ => w0 :=
      ⟨w ⟨0, hq⟩, funext fun i => const_of_cycle σ w hw i ⟨0, hq⟩ (sameCycle_of_ncyc σ hx' i ⟨0, hq⟩)⟩
    obtain ⟨c, rfl⟩ := conj_rot σ hx'
    have hrel : AT (N := N) ((c⁻¹ * finRotate q * c, fun _ => w0, ε) : Pat L q) =
        ((Equiv.Perm.sign c⁻¹ : ℤ) : ℝ) • AT (N := N) ((finRotate q, fun _ => w0, ε) : Pat L q) := by
      simp only [AT]
      apply alt_relabel
      intro v
      simp only [tmR, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, tmC_relabel]
    have hrev : ∀ Y : Fin q → HS L N, tmC (finRotate q) (fun _ => w0) (Y ∘ ⇑(Fin.revPerm : Equiv.Perm (Fin q))⁻¹)
        = star (tmC (finRotate q) (fun _ => w0) Y) := by
      intro Y
      rw [← tmC_relabel, rot_rev, tmC_inv_star]
    have hrev' : ∀ Y : Fin q → HS L N, tmC (finRotate q) (fun _ => w0) (Y ∘ ⇑(Fin.revPerm : Equiv.Perm (Fin q)))
        = star (tmC (finRotate q) (fun _ => w0) Y) := by
      intro Y
      simpa using hrev Y
    have hvan : AT (N := N) ((finRotate q, fun _ => w0, true) : Pat L q) = 0 ∨
        AT (N := N) ((finRotate q, fun _ => w0, false) : Pat L q) = 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign ((Fin.revPerm : Equiv.Perm (Fin q))⁻¹)) with hs | hs
      · left
        simp only [AT]
        apply alt_zero' _ ((Fin.revPerm : Equiv.Perm (Fin q))⁻¹) _ hs
        intro v
        simp [tmR, hrev']
      · right
        have h2 := alt_relabel (tmR (N := N) (finRotate q) (fun _ => w0) false)
          (tmR (finRotate q) (fun _ => w0) false) ((Fin.revPerm : Equiv.Perm (Fin q))⁻¹)
          (fun v => by simp [tmR, hrev'])
        rw [hs] at h2
        simp only [AT]
        ext v
        have h3 := congrArg (fun F => F v) h2
        simp at h3
        simp
        linarith
    rcases hvan with h0 | h0 <;> cases ε
    · exact ⟨((Equiv.Perm.sign c⁻¹ : ℤ) : ℝ), w0, by rw [hrel, h0, add_zero]⟩
    · exact ⟨0, w0, by rw [hrel, h0, smul_zero, zero_smul]⟩
    · exact ⟨0, w0, by rw [hrel, h0, smul_zero, zero_smul]⟩
    · exact ⟨((Equiv.Perm.sign c⁻¹ : ℤ) : ℝ), w0, by rw [hrel, h0, zero_add]⟩
  · refine ⟨0, w ⟨0, hq⟩, ?_⟩
    rw [zero_smul]
    have h0 : tmR (N := N) σ w ε = 0 := by
      ext v
      simp only [tmR, tmC, if_neg hw, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
        ContinuousMultilinearMap.zero_apply, map_zero]
    simp only [AT]
    rw [h0, map_zero]

end PositivityTheory.KB.BlockEvaluationBounds

end
