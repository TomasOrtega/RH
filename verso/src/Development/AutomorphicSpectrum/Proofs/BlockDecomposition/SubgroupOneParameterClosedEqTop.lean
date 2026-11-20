import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.GenOneParam

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : Type} [Fintype n] [DecidableEq n]

def packM (g : ι → Matrix n n ℂ) : Matrix n n (ι → ℂ) := Matrix.of fun i j w => g w i j

/- English proof (translation)
By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem packM_one : packM (1 : ι → Matrix n n ℂ) = 1 := by
  ext i j w
  by_cases h : i = j
  · subst h; simp [packM]
  · simp [packM, h]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem packM_mul (g h : ι → Matrix n n ℂ) : packM (g * h) = packM g * packM h := by
  ext i j w
  simp [packM, Matrix.mul_apply, Finset.sum_apply]

def packGL : (ι → GL n ℂ) →* GL n (ι → ℂ) where
  toFun g := ⟨packM fun w => (g w).val, packM fun w => (g w)⁻¹.val,
    by rw [← packM_mul, ← packM_one]; congr 1; ext1 w; simp,
    by rw [← packM_mul, ← packM_one]; congr 1; ext1 w; simp⟩
  map_one' := by
    apply Units.ext
    show packM (fun w => ((1 : ι → GL n ℂ) w).val) = 1
    rw [← packM_one]; congr 1
  map_mul' g h := by
    apply Units.ext
    show packM (fun w => ((g * h) w).val) = packM _ * packM _
    rw [← packM_mul]; congr 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem packGL_val (g : ι → GL n ℂ) : (packGL g).val = packM fun w => (g w).val := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem packGL_inv_val (g : ι → GL n ℂ) : (packGL g)⁻¹.val = packM fun w => (g w)⁻¹.val := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem packGL_surjective : Function.Surjective (packGL : (ι → GL n ℂ) → GL n (ι → ℂ)) := by
  intro y
  refine ⟨fun w => Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : ι => ℂ) w) y, ?_⟩
  apply Units.ext
  ext i j w
  simp [packGL_val, packM]

end GlobalTheory.CompanionTheory.GenOneParam

namespace GlobalTheory.CompanionTheory.GenOneParam

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem packGL_mulSingle_val (w w' : ι) (g : GL n ℂ) (i j : n) :
    (packGL (Pi.mulSingle w g)).val i j w' = if w' = w then g.val i j else (1 : Matrix n n ℂ) i j := by
  by_cases h : w' = w
  · subst h; simp [packGL_val, packM]
  · simp [packGL_val, packM, h, Pi.mulSingle_eq_of_ne h]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem packGL_mulSingle_inv_val (w w' : ι) (g : GL n ℂ) (i j : n) :
    (packGL (Pi.mulSingle w g))⁻¹.val i j w' =
      if w' = w then g⁻¹.val i j else (1 : Matrix n n ℂ) i j := by
  by_cases h : w' = w
  · subst h; rw [packGL_inv_val]; simp [packM]
  · rw [packGL_inv_val]; simp [packM, h, Pi.mulSingle_eq_of_ne h]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem mem_of_family {S : Subgroup (GL n (ι → ℂ))}
    (hS : ∀ (c : ℝ → GL n (ι → ℂ)) (X : n → n → ι → ℂ), Continuous c → c 0 = 1 →
      (∀ s t, c (s + t) = c s * c t) →
      HasDerivAt (fun t => Matrix.of.symm (c t).val) X 0 → ∀ t, c t ∈ S)
    (w : ι) (m : ℝ → Matrix n n ℂ) (hm : Continuous m) (h0 : m 0 = 1)
    (hadd : ∀ s t, m (s + t) = m s * m t) (X₀ : n → n → ℂ)
    (hd : ∀ i j, HasDerivAt (fun t => m t i j) (X₀ i j) 0)
    (t : ℝ) (g : GL n ℂ) (hg : g.val = m t) : packGL (Pi.mulSingle w g) ∈ S := by
  let c₀ : ℝ → GL n ℂ := fun s => ⟨m s, m (-s),
    by rw [← hadd]; simp [h0], by rw [← hadd]; simp [h0]⟩
  have hc₀ : ∀ s, (c₀ s).val = m s := fun s => rfl
  have hc₀i : ∀ s, (c₀ s)⁻¹.val = m (-s) := fun s => rfl
  have hg' : c₀ t = g := Units.ext (by rw [hc₀, hg])
  have h00 : c₀ 0 = 1 := Units.ext (by rw [hc₀, h0]; rfl)
  have hadd₀ : ∀ s u, c₀ (s + u) = c₀ s * c₀ u := fun s u => Units.ext (by
    rw [Units.val_mul, hc₀, hc₀, hc₀, hadd])
  rw [← hg']
  refine hS (fun s => packGL (Pi.mulSingle w (c₀ s)))
    (fun i j w' => if w' = w then X₀ i j else 0) ?_ ?_ ?_ ?_ t
  · rw [Units.continuous_iff]
    constructor
    · refine continuous_matrix fun i j => continuous_pi fun w' => ?_
      simp only [Function.comp, packGL_mulSingle_val, hc₀]
      split_ifs
      · exact (continuous_id.matrix_elem i j).comp hm
      · exact continuous_const
    · refine continuous_matrix fun i j => continuous_pi fun w' => ?_
      simp only [packGL_mulSingle_inv_val, hc₀i]
      split_ifs
      · exact (continuous_id.matrix_elem i j).comp (hm.comp continuous_neg)
      · exact continuous_const
  · simp [h00]
  · intro s u
    simp only [hadd₀]
    rw [Pi.mulSingle_mul, map_mul]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w' => ?_
    simp only [Matrix.of_symm_apply, packGL_mulSingle_val, hc₀]
    by_cases h : w' = w
    · simpa [h] using hd i j
    · simpa [h] using hasDerivAt_const (0 : ℝ) ((1 : Matrix n n ℂ) i j)

/- English proof (translation)
Reduce the argument to an intermediate assertion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Put the polynomial expressions in normal form. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem single_mem {S : Subgroup (GL n (ι → ℂ))}
    (hS : ∀ (c : ℝ → GL n (ι → ℂ)) (X : n → n → ι → ℂ), Continuous c → c 0 = 1 →
      (∀ s t, c (s + t) = c s * c t) →
      HasDerivAt (fun t => Matrix.of.symm (c t).val) X 0 → ∀ t, c t ∈ S)
    (w : ι) (g : GL n ℂ) : packGL (Pi.mulSingle w g) ∈ S := by
  suffices H : ∀ M : Matrix n n ℂ, M.det ≠ 0 →
      ∀ g : GL n ℂ, g.val = M → packGL (Pi.mulSingle w g) ∈ S from
    H g.val (Matrix.isUnits_det_units g).ne_zero g rfl
  intro M hM
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ g : GL n ℂ, g.val = M → packGL (Pi.mulSingle w g) ∈ S) M hM ?_ ?_ ?_
  · intro D hD g hg
    have hD' : ∀ k, D k ≠ 0 := fun k => by
      rw [Matrix.det_diagonal] at hD
      exact Finset.prod_ne_zero_iff.1 hD k (Finset.mem_univ k)
    refine mem_of_family hS w
      (fun t => Matrix.diagonal fun k => Complex.exp ((t : ℂ) * Complex.log (D k)))
      ?_ ?_ ?_ (fun i j => if i = j then Complex.log (D i) else 0) ?_ 1 g ?_
    · refine Continuous.matrix_diagonal (continuous_pi fun k => ?_)
      fun_prop
    · simp
    · intro s u
      rw [Matrix.diagonal_mul_diagonal']
      congr 1; ext k
      rw [← Complex.exp_add]; push_cast; ring_nf
    · intro i j
      by_cases h : i = j
      · subst h
        simp only [Matrix.diagonal_apply_eq, if_true]
        have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.log (D i)) (Complex.log (D i)) 0 := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (Complex.log (D i))
        simpa using h1.cexp
      · simpa [h, Matrix.diagonal_apply_ne _ h] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · rw [hg]; congr 1; ext k
      simp [Complex.exp_log (hD' k)]
  · intro τ g hg
    refine mem_of_family hS w (fun t => Matrix.transvection τ.i τ.j ((t : ℂ) * τ.c))
      ?_ ?_ ?_ (fun a b => (Matrix.single τ.i τ.j τ.c : Matrix n n ℂ) a b) ?_ 1 g ?_
    · unfold Matrix.transvection
      refine continuous_const.add ?_
      refine continuous_matrix fun a b => ?_
      simp only [Matrix.single_apply]
      split_ifs
      · fun_prop
      · exact continuous_const
    · simp
    · intro s u
      rw [Matrix.transvection_mul_transvection_same _ _ τ.hij]
      congr 1; push_cast; ring
    · intro a b
      unfold Matrix.transvection
      simp only [Matrix.add_apply, Matrix.single_apply]
      split_ifs
      · have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * τ.c) τ.c 0 := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const τ.c
        exact h1.const_add _
      · exact hasDerivAt_const (0 : ℝ) _ |>.add (hasDerivAt_const (0 : ℝ) (0 : ℂ)) |>.congr_deriv (by simp)
    · rw [hg]; simp [Matrix.TransvectionStruct.toMatrix]
  · intro A B hA hB PA PB g hg
    have : g = Matrix.GeneralLinearGroup.mkOfDetNeZero A hA *
        Matrix.GeneralLinearGroup.mkOfDetNeZero B hB := Units.ext (by rw [hg]; rfl)
    rw [this, Pi.mulSingle_mul, map_mul]
    exact S.mul_mem (PA _ rfl) (PB _ rfl)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
-/
theorem eq_top_of_oneParam {S : Subgroup (GL n (ι → ℂ))}
    (hS : ∀ (c : ℝ → GL n (ι → ℂ)) (X : n → n → ι → ℂ), Continuous c → c 0 = 1 →
      (∀ s t, c (s + t) = c s * c t) →
      HasDerivAt (fun t => Matrix.of.symm (c t).val) X 0 → ∀ t, c t ∈ S) : S = ⊤ := by
  have hle : Subgroup.pi Set.univ (fun _ : ι => (⊤ : Subgroup (GL n ℂ))) ≤ S.comap packGL := by
    rw [Subgroup.pi_le_iff]
    rintro w _ ⟨g, -, rfl⟩
    exact single_mem hS w g
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨g, rfl⟩ := packGL_surjective y
  exact hle (by simp [Subgroup.mem_pi])

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem eq_top_of_oneParam_Cinf : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Subgroup (GL (Fin a) (Cinf E))), (∀ (c : ℝ → GL (Fin a) (Cinf E)) (X : GlobalTheory.CuspRep.Lie E a), Continuous c → c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → HasDerivAt (fun t => toL (c t).val) X 0 → ∀ t, c t ∈ S) → S = ⊤ := by
  intro E _ _ a S hS
  classical
  exact eq_top_of_oneParam (ι := InfinitePlace E) (n := Fin a) hS

end GlobalTheory.CompanionTheory.GenOneParam
