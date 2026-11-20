import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpan
import Development.WeilBound.CoreStatements.BranchingTraces.ContinuousEmb

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

/- English proof (translation)
Introduce `m ε K _ _ σ hU hI u w hu hw`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hJ : PI.UpqRep.Jm ε * PI.UpqRep.Jm ε = 1`. Unfold `PI.UpqRep.Jm`.

Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hlift : ∀ g ∈ UJset ε, ∃ h : UJ ε, um h = g`.

Introduce `g hg`. Establish `hg' : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε` using `hg`. Establish `h2 : PI.UpqRep.Jm ε * gᴴ * PI.UpqRep.Jm ε * g = 1`. Rewrite using `[Matrix.mul_assoc (PI.UpqRep.Jm ε * gᴴ), Matrix.mul_assoc (PI.UpqRep.Jm ε), ← Matrix.mul_assoc gᴴ, hg', hJ]`. Establish `h1 : g * (PI.UpqRep.Jm ε * gᴴ * PI.UpqRep.Jm ε) = 1` using `mul_eq_one_comm.mp h2`.

Conclude with `⟨⟨⟨g, _, h1, h2⟩, hg⟩, rfl⟩`. Establish `hmul : ∀ g ∈ UJset ε, ∀ h ∈ UJset ε, g * h ∈ UJset ε`. Introduce `g hg h hh`. Establish `hg' : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε` using `hg`. Establish `hh' : hᴴ * PI.UpqRep.Jm ε * h = PI.UpqRep.Jm ε` using `hh`.

Use `show (g * h)ᴴ * PI.UpqRep.Jm ε * (g * h) = PI.UpqRep.Jm ε`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = PI.UpqRep.Jm ε := by rw [hg', hh']`.

Establish `hone : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ UJset ε` using `by show (1 : Matrix (Fin m) (Fin m) ℂ)ᴴ * PI.UpqRep.Jm ε * 1 = PI.UpqRep.Jm ε`. Simplify using the standard rewrite rules. Set `Sp : Submodule ℂ K` to `Submodule.span ℂ {x | ∃ g ∈ UJset ε, x = σ g u}`. Establish `hSpinv : ∀ g ∈ UJset ε, ∀ x ∈ Sp, σ g x ∈ Sp`. Introduce `g hg x hx`.

Use `Submodule.span_induction (p := fun x _ => σ g x ∈ Sp) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `y ⟨h, hh, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨g * h, hmul g hg h hh, ?_⟩` and prove the remaining obligations. Rewrite using `[hU.1.2 g hg h hh]`.

Both sides reduce to the same expression. Simplify using the standard rewrite rules. Introduce `a b _ _ ha hb`. Rewrite using `[map_add]`. Conclude with `Sp.add_mem ha hb`.

Introduce `c a _ ha`. Rewrite using `[map_smul]`. Conclude with `Sp.smul_mem c ha`. Establish `hMinv : ∀ g ∈ UJset ε, ∀ v ∈ Sp.topologicalClosure, σ g v ∈ Sp.topologicalClosure`. Introduce `g hg v hv`.

Rewrite `hv`, the goal using `[← SetLike.mem_coe, Submodule.topologicalClosure_coe]`. Conclude with `map_mem_closure (σ g).continuous hv (fun x hx => hSpinv g hg x hx)`. Establish `huM : u ∈ Sp.topologicalClosure`. Apply `Submodule.le_topologicalClosure` to reduce the goal to its premises. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨1, hone, ?_⟩` and prove the remaining obligations. Rewrite using `[hU.1.1]`. Both sides reduce to the same expression. Establish `hker : Sp.topologicalClosure ≤ LinearMap.ker (innerSL ℂ w : K →ₗ[ℂ] ℂ)`. Apply `Submodule.topologicalClosure_minimal` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `x ⟨g, hg, rfl⟩`. Take `⟨h, rfl⟩` from `hlift g hg`. Use `show innerSL ℂ w (σ (um h) u) = 0`. Rewrite using `[innerSL_apply_apply]`.

Conclude with `hcon h`. Conclude with `ContinuousLinearMap.isClosed_ker _`. Break down `hI _ (Submodule.isClosed_topologicalClosure _) hMinv with h0 | htop` into its components or cases. Rewrite `huM` using `[h0]`. Conclude with `hu ((Submodule.mem_bot ℂ).mp huM)`.

Establish `hwM : w ∈ Sp.topologicalClosure`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`. Establish `hw0` using `hker hwM`. Rewrite `hw0` using `[LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_self_eq_zero]`.

Conclude with `hw hw0`.
-/
theorem irr : Irr := by
  intro m ε K _ _ σ hU hI u w hu hw
  by_contra hcon
  push_neg at hcon
  have hJ : PI.UpqRep.Jm ε * PI.UpqRep.Jm ε = 1 := by
    unfold PI.UpqRep.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hlift : ∀ g ∈ UJset ε, ∃ h : UJ ε, um h = g := by
    intro g hg
    have hg' : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := hg
    have h2 : PI.UpqRep.Jm ε * gᴴ * PI.UpqRep.Jm ε * g = 1 := by
      rw [Matrix.mul_assoc (PI.UpqRep.Jm ε * gᴴ), Matrix.mul_assoc (PI.UpqRep.Jm ε),
        ← Matrix.mul_assoc gᴴ, hg', hJ]
    have h1 : g * (PI.UpqRep.Jm ε * gᴴ * PI.UpqRep.Jm ε) = 1 := mul_eq_one_comm.mp h2
    exact ⟨⟨⟨g, _, h1, h2⟩, hg⟩, rfl⟩
  have hmul : ∀ g ∈ UJset ε, ∀ h ∈ UJset ε, g * h ∈ UJset ε := by
    intro g hg h hh
    have hg' : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := hg
    have hh' : hᴴ * PI.UpqRep.Jm ε * h = PI.UpqRep.Jm ε := hh
    show (g * h)ᴴ * PI.UpqRep.Jm ε * (g * h) = PI.UpqRep.Jm ε
    rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * PI.UpqRep.Jm ε * (g * h) = hᴴ * (gᴴ * PI.UpqRep.Jm ε * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = PI.UpqRep.Jm ε := by rw [hg', hh']
  have hone : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin m) (Fin m) ℂ)ᴴ * PI.UpqRep.Jm ε * 1 = PI.UpqRep.Jm ε
    simp
  let Sp : Submodule ℂ K := Submodule.span ℂ {x | ∃ g ∈ UJset ε, x = σ g u}
  have hSpinv : ∀ g ∈ UJset ε, ∀ x ∈ Sp, σ g x ∈ Sp := by
    intro g hg x hx
    refine Submodule.span_induction (p := fun x _ => σ g x ∈ Sp) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨h, hh, rfl⟩
      apply Submodule.subset_span
      refine ⟨g * h, hmul g hg h hh, ?_⟩
      rw [hU.1.2 g hg h hh]
      rfl
    · simp
    · intro a b _ _ ha hb
      rw [map_add]
      exact Sp.add_mem ha hb
    · intro c a _ ha
      rw [map_smul]
      exact Sp.smul_mem c ha
  have hMinv : ∀ g ∈ UJset ε, ∀ v ∈ Sp.topologicalClosure, σ g v ∈ Sp.topologicalClosure := by
    intro g hg v hv
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hv ⊢
    exact map_mem_closure (σ g).continuous hv (fun x hx => hSpinv g hg x hx)
  have huM : u ∈ Sp.topologicalClosure := by
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨1, hone, ?_⟩
    rw [hU.1.1]
    rfl
  have hker : Sp.topologicalClosure ≤ LinearMap.ker (innerSL ℂ w : K →ₗ[ℂ] ℂ) := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro x ⟨g, hg, rfl⟩
      obtain ⟨h, rfl⟩ := hlift g hg
      show innerSL ℂ w (σ (um h) u) = 0
      rw [innerSL_apply_apply]
      exact hcon h
    · exact ContinuousLinearMap.isClosed_ker _
  rcases hI _ (Submodule.isClosed_topologicalClosure _) hMinv with h0 | htop
  · rw [h0] at huM
    exact hu ((Submodule.mem_bot ℂ).mp huM)
  · have hwM : w ∈ Sp.topologicalClosure := by
      rw [htop]
      exact Submodule.mem_top
    have hw0 := hker hwM
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_self_eq_zero] at hw0
    exact hw hw0

/- English proof (translation)
Unfold `emb zi`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]`. Break down `h : e.symm d with i | u` into its components or cases. Establish `hne : d ≠ e (Sum.inr ())`. Introduce `hd`.

Rewrite `h` using `[hd, Equiv.symm_apply_apply]`. Consider the cases of `h`. Simplify using `[hne]`. Consider the cases of `u`. Establish `heq : d = e (Sum.inr ())` using `by rw [← h, Equiv.apply_symm_apply]`.

Simplify using `[heq]`.
-/
theorem emb_row {n : ℕ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (a : Matrix (Fin n) (Fin n) ℂ) (d : Fin (n + 1)) :
    emb e a (zi e) d = if d = zi e then 1 else 0 := by
  unfold emb zi
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases h : e.symm d with i | u
  · have hne : d ≠ e (Sum.inr ()) := by
      intro hd
      rw [hd, Equiv.symm_apply_apply] at h
      cases h
    simp [hne]
  · cases u
    have heq : d = e (Sum.inr ()) := by rw [← h, Equiv.apply_symm_apply]
    simp [heq]

/- English proof (translation)
Simplify using `[emb]`.
-/
theorem emb_ll {n : ℕ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (a : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    emb e a (e (Sum.inl i)) (e (Sum.inl j)) = a i j := by
  simp [emb]

/- English proof (translation)
Simplify using `[emb]`.
-/
theorem emb_rl {n : ℕ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (a : Matrix (Fin n) (Fin n) ℂ) (u : Unit) (j : Fin n) :
    emb e a (e (Sum.inr u)) (e (Sum.inl j)) = 0 := by
  simp [emb]

/- English proof (translation)
Introduce `n ε ε' e H H' _ _ _ _ π σ S E P hF hS hU hP η hη`. Establish `hJJ : Jm ε' * Jm ε' = 1`. Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hlift : ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * Jm ε' * g = Jm ε' → ∃ h : UJ ε', um h = g`. Introduce `g hg`. Establish `h2 : Jm ε' * gᴴ * Jm ε' * g = 1`.

Rewrite using `[Matrix.mul_assoc (Jm ε' * gᴴ), Matrix.mul_assoc (Jm ε'), ← Matrix.mul_assoc gᴴ, hg, hJJ]`. Establish `h1 : g * (Jm ε' * gᴴ * Jm ε') = 1` using `mul_eq_one_comm.mp h2`. Conclude with `⟨⟨⟨g, _, h1, h2⟩, hg⟩, rfl⟩`. Establish `hembJ : ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * Jm ε' * g = Jm ε' → (emb e g)ᴴ * Jm ε * emb e g = Jm ε`. Introduce `g hg`.

Rewrite using `[jm_emb hF, emb_ct, ← emb_mul, ← emb_mul, hg]`. Establish `hsm : ∀ x ∈ S, P x ∈ PI.PhMeasCore.smoothVecs (Jm ε') σ`. Introduce `x hx`. Use `show PI.PhMeasCore.SmoothOnH _ _`. Introduce `g₀ hg₀`.

Establish `hx' : PI.PhMeasCore.SmoothOnH (Jm ε) (fun g => π g x)` using `(hS.mem x).mp hx`. Take `⟨U, F, hUo, hg₀U, hFc, hFeq⟩` from `hx' (emb e g₀) (hembJ g₀ hg₀)`. Use `letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup`. Use `letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace`. Use `letI : NormedAddCommGroup (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := Matrix.normedAddCommGroup`.

Use `letI : NormedSpace ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := Matrix.normedSpace`. Set `L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ` to `{ toFun := fun g => emb e g - emb e 0 map_add' := by`. Introduce `a b`. Use extensionality with `i j`. Simplify using `only [emb, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply]`.

Apply the tactic sequence `rcases e.symm i with i' | i' <;> rcases e.symm j with j' | j' <;> simp`. Use the proof step `map_smul' := by`. Introduce `c a`. Use extensionality with `i j`. Simplify using `only [emb, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, RingHom.id_apply]`.

Apply the tactic sequence `rcases e.symm i with i' | i' <;> rcases e.symm j with j' | j' <;> simp }`. Establish `hembd : ContDiff ℝ (⊤ : ℕ∞) (emb e)`. Establish `hfun : emb e = fun g => L g + emb e 0`. Use function extensionality and compare the values at `g`. Use `show emb e g = emb e g - emb e 0 + emb e 0`.

Normalize the expressions using the abelian group laws. Rewrite using `[hfun]`. Conclude with `(LinearMap.toContinuousLinearMap L).contDiff.add contDiff_const`. Use `⟨emb e ⁻¹' U, fun g => P (F (emb e g)), hUo.preimage hembd.continuous, hg₀U, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(P.restrictScalars ℝ).contDiff.comp_contDiffOn (hFc.comp hembd.contDiffOn (fun g hg => hg))`.

Introduce `g hgU hgH`. Establish `hgH' : gᴴ * Jm ε' * g = Jm ε'` using `hgH`. Establish `h1` using `hFeq (emb e g) hgU (hembJ g hgH')`. Take `⟨h, rfl⟩` from `hlift g hgH'`. Use `show σ (um h) (P x) = P (F (emb e (um h)))`.

Rewrite using `[← h1, ← hP.2 h x]`. Use `⟨fun l => ?_, fun h => ?_⟩` and prove the remaining obligations. Use `show P (ap (E (e (Sum.inl l)) (zi e)) η) ∈ _`. Unfold `ap`. Rewrite using `[dif_pos hη]`.

Conclude with `hsm _ (Subtype.coe_prop _)`. Establish `hgU : emb e (um h) ∈ UJset ε` using `(embU hF h).2`. Establish `hgiU : emb e (um h⁻¹) ∈ UJset ε` using `(embU hF h⁻¹).2`. Establish `hu1 : um h⁻¹ * um h = 1` using `by simp [PositivityTheory.UnitaryDecomposition.um]`. Establish `hu2 : um h * um h⁻¹ = 1` using `by simp [PositivityTheory.UnitaryDecomposition.um]`.

Establish `hgg : emb e (um h⁻¹) * emb e (um h) = 1` using `by rw [← emb_mul, hu1, emb_one]`. Establish `hgg' : emb e (um h) * emb e (um h⁻¹) = 1` using `by rw [← emb_mul, hu2, emb_one]`. Establish `hinv : (emb e (um h⁻¹))⁻¹ = emb e (um h)` using `Matrix.inv_eq_right_inv hgg`. Establish `hπη : π (emb e (um h)) η ∈ S` using `hS.stab _ hgU η hη`. Establish `hcomp1 : ∀ y, π (emb e (um h⁻¹)) (π (emb e (um h)) y) = y`.

Introduce `y`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← hU.1.2 _ hgiU _ hgU, hgg, hU.1.1]`. Both sides reduce to the same expression. Establish `hcomp2 : ∀ y, π (emb e (um h)) (π (emb e (um h⁻¹)) y) = y`. Introduce `y`.

Rewrite using `[← ContinuousLinearMap.comp_apply, ← hU.1.2 _ hgU _ hgiU, hgg', hU.1.1]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `c0`. Use `show P (ap (E (e (Sum.inl c0)) (zi e)) (π (emb e (um h)) η)) = ∑ d, (um h)⁻¹ d c0 • σ (um h) (P (ap (E (e (Sum.inl d)) (zi e)) η))`. Simplify using `only [ap, dif_pos hη, dif_pos hπη]`.

Establish `hc` using `hS.conj _ hgiU (e (Sum.inl c0)) (zi e) ⟨π (emb e (um h)) η, hπη⟩ ⟨η, hη⟩ (hcomp1 η).symm`. Rewrite `hc` using `[hinv]`. Simplify using `only [emb_row, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_true] at hc`. Establish `hc2` using `congrArg (fun y => P (π (emb e (um h)) y)) hc`. Simplify using `only [hcomp2, map_sum, map_smul] at hc2`.

Rewrite using `[hc2, ← e.sum_comp, Fintype.sum_sum_type]`. Simplify using `only [emb_rl, zero_smul, Finset.sum_const_zero, add_zero, emb_ll, um_inv]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[hP.2 h]`.
-/
theorem phiEq : PhiEq := by
  intro n ε ε' e H H' _ _ _ _ π σ S E P hF hS hU hP η hη
  have hJJ : Jm ε' * Jm ε' = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hlift : ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * Jm ε' * g = Jm ε' → ∃ h : UJ ε', um h = g := by
    intro g hg
    have h2 : Jm ε' * gᴴ * Jm ε' * g = 1 := by
      rw [Matrix.mul_assoc (Jm ε' * gᴴ), Matrix.mul_assoc (Jm ε'), ← Matrix.mul_assoc gᴴ, hg, hJJ]
    have h1 : g * (Jm ε' * gᴴ * Jm ε') = 1 := mul_eq_one_comm.mp h2
    exact ⟨⟨⟨g, _, h1, h2⟩, hg⟩, rfl⟩
  have hembJ : ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * Jm ε' * g = Jm ε' →
      (emb e g)ᴴ * Jm ε * emb e g = Jm ε := by
    intro g hg
    rw [jm_emb hF, emb_ct, ← emb_mul, ← emb_mul, hg]
  have hsm : ∀ x ∈ S, P x ∈ PI.PhMeasCore.smoothVecs (Jm ε') σ := by
    intro x hx
    show PI.PhMeasCore.SmoothOnH _ _
    intro g₀ hg₀
    have hx' : PI.PhMeasCore.SmoothOnH (Jm ε) (fun g => π g x) := (hS.mem x).mp hx
    obtain ⟨U, F, hUo, hg₀U, hFc, hFeq⟩ := hx' (emb e g₀) (hembJ g₀ hg₀)
    letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
    letI : NormedAddCommGroup (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := Matrix.normedSpace
    let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
      { toFun := fun g => emb e g - emb e 0
        map_add' := by
          intro a b
          ext i j
          simp only [emb, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply]
          rcases e.symm i with i' | i' <;> rcases e.symm j with j' | j' <;> simp
        map_smul' := by
          intro c a
          ext i j
          simp only [emb, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
            RingHom.id_apply]
          rcases e.symm i with i' | i' <;> rcases e.symm j with j' | j' <;> simp }
    have hembd : ContDiff ℝ (⊤ : ℕ∞) (emb e) := by
      have hfun : emb e = fun g => L g + emb e 0 := by
        funext g
        show emb e g = emb e g - emb e 0 + emb e 0
        abel
      rw [hfun]
      exact (LinearMap.toContinuousLinearMap L).contDiff.add contDiff_const
    refine ⟨emb e ⁻¹' U, fun g => P (F (emb e g)), hUo.preimage hembd.continuous, hg₀U, ?_, ?_⟩
    · exact (P.restrictScalars ℝ).contDiff.comp_contDiffOn (hFc.comp hembd.contDiffOn (fun g hg => hg))
    · intro g hgU hgH
      have hgH' : gᴴ * Jm ε' * g = Jm ε' := hgH
      have h1 := hFeq (emb e g) hgU (hembJ g hgH')
      obtain ⟨h, rfl⟩ := hlift g hgH'
      show σ (um h) (P x) = P (F (emb e (um h)))
      rw [← h1, ← hP.2 h x]
  refine ⟨fun l => ?_, fun h => ?_⟩
  · show P (ap (E (e (Sum.inl l)) (zi e)) η) ∈ _
    unfold ap
    rw [dif_pos hη]
    exact hsm _ (Subtype.coe_prop _)
  · have hgU : emb e (um h) ∈ UJset ε := (embU hF h).2
    have hgiU : emb e (um h⁻¹) ∈ UJset ε := (embU hF h⁻¹).2
    have hu1 : um h⁻¹ * um h = 1 := by simp [PositivityTheory.UnitaryDecomposition.um]
    have hu2 : um h * um h⁻¹ = 1 := by simp [PositivityTheory.UnitaryDecomposition.um]
    have hgg : emb e (um h⁻¹) * emb e (um h) = 1 := by rw [← emb_mul, hu1, emb_one]
    have hgg' : emb e (um h) * emb e (um h⁻¹) = 1 := by rw [← emb_mul, hu2, emb_one]
    have hinv : (emb e (um h⁻¹))⁻¹ = emb e (um h) := Matrix.inv_eq_right_inv hgg
    have hπη : π (emb e (um h)) η ∈ S := hS.stab _ hgU η hη
    have hcomp1 : ∀ y, π (emb e (um h⁻¹)) (π (emb e (um h)) y) = y := by
      intro y
      rw [← ContinuousLinearMap.comp_apply, ← hU.1.2 _ hgiU _ hgU, hgg, hU.1.1]
      rfl
    have hcomp2 : ∀ y, π (emb e (um h)) (π (emb e (um h⁻¹)) y) = y := by
      intro y
      rw [← ContinuousLinearMap.comp_apply, ← hU.1.2 _ hgU _ hgiU, hgg', hU.1.1]
      rfl
    funext c0
    show P (ap (E (e (Sum.inl c0)) (zi e)) (π (emb e (um h)) η)) =
      ∑ d, (um h)⁻¹ d c0 • σ (um h) (P (ap (E (e (Sum.inl d)) (zi e)) η))
    simp only [ap, dif_pos hη, dif_pos hπη]
    have hc := hS.conj _ hgiU (e (Sum.inl c0)) (zi e) ⟨π (emb e (um h)) η, hπη⟩ ⟨η, hη⟩ (hcomp1 η).symm
    rw [hinv] at hc
    simp only [emb_row, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, ite_true] at hc
    have hc2 := congrArg (fun y => P (π (emb e (um h)) y)) hc
    simp only [hcomp2, map_sum, map_smul] at hc2
    rw [hc2, ← e.sum_comp, Fintype.sum_sum_type]
    simp only [emb_rl, zero_smul, Finset.sum_const_zero, add_zero, emb_ll, um_inv]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [hP.2 h]

end PositivityTheory.RgHe.SM
