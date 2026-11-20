import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

open MeasureTheory Matrix

namespace UpperTheory.Esk.FormsStableLemmas

open UpperTheory.Esk

/- English proof (translation)
Use function extensionality and compare the values at `t`. Unfold `ext1`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem extendHalfPlane_finset_sum {ι : Type} (s : Finset ι) (g : ι → P → ℂ) :
    ext1 (fun t => ∑ i ∈ s, g i t) = fun t => ∑ i ∈ s, ext1 (g i) t := by
  funext t
  unfold ext1
  split_ifs <;> simp

/- English proof (translation)
Unfold `Hol1`. Rewrite using `[extendHalfPlane_finset_sum]`. Conclude with `(DifferentiableOn.sum h).congr fun t _ => by simp [Finset.sum_apply]`.
-/
theorem holomorphic_on_half_plane_finset_sum {ι : Type} (s : Finset ι) (g : ι → P → ℂ) (h : ∀ i ∈ s, Hol1 (g i)) :
    Hol1 (fun t => ∑ i ∈ s, g i t) := by
  unfold Hol1
  rw [extendHalfPlane_finset_sum]
  exact (DifferentiableOn.sum h).congr fun t _ => by simp [Finset.sum_apply]

/- English proof (translation)
Establish `: ext1 (fun t => f t + g t) = fun t => ext1 f t + ext1 g t`. Apply the tactic sequence `funext t; unfold ext1; split_ifs <;> simp`. Unfold `Hol1 at *`. Rewrite using `[this]`. Conclude with `hf.add hg`.
-/
theorem holomorphic_on_half_plane_add (f g : P → ℂ) (hf : Hol1 f) (hg : Hol1 g) : Hol1 (fun t => f t + g t) := by
  have : ext1 (fun t => f t + g t) = fun t => ext1 f t + ext1 g t := by
    funext t; unfold ext1; split_ifs <;> simp
  unfold Hol1 at *
  rw [this]
  exact hf.add hg

/- English proof (translation)
Establish `: ext1 (fun t => c * f t) = fun t => c * ext1 f t`. Apply the tactic sequence `funext t; unfold ext1; split_ifs <;> simp`. Unfold `Hol1 at *`. Rewrite using `[this]`. Conclude with `hf.const_mul c`.
-/
theorem holomorphic_on_half_plane_const_mul (c : ℂ) (f : P → ℂ) (hf : Hol1 f) : Hol1 (fun t => c * f t) := by
  have : ext1 (fun t => c * f t) = fun t => c * ext1 f t := by
    funext t; unfold ext1; split_ifs <;> simp
  unfold Hol1 at *
  rw [this]
  exact hf.const_mul c

/- English proof (translation)
Establish `: ext1 (fun _ : P => (0 : ℂ)) = fun _ => 0`. Apply the tactic sequence `funext t; unfold ext1; split_ifs <;> simp`. Unfold `Hol1`. Rewrite using `[this]`. Conclude with `differentiableOn_const 0`.
-/
theorem holomorphic_on_half_plane_zero : Hol1 (fun _ : P => (0 : ℂ)) := by
  have : ext1 (fun _ : P => (0 : ℂ)) = fun _ => 0 := by
    funext t; unfold ext1; split_ifs <;> simp
  unfold Hol1
  rw [this]
  exact differentiableOn_const 0

/- English proof (translation)
Unfold `nrm`. Conclude with `Finset.prod_nonneg fun v _ => Real.rpow_nonneg (abs_nonneg _) _`.
-/
theorem nrm_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z : X I) : 0 ≤ nrm k z := by
  unfold nrm
  exact Finset.prod_nonneg fun v _ => Real.rpow_nonneg (abs_nonneg _) _

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

omit [Fintype I] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem op_apply {ι : Type} [Fintype ι] (a : ι → Gf) (f : X I × Gf → ℂ) (p : X I × Gf) :
    Dat.Op a f p = ∑ i, f (p.1, p.2 * a i) := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨continuous_const, fun _ _ => holomorphic_on_half_plane_zero⟩ aut γ z x := by simp lev z x h := by simp bdd := ⟨0, fun z x => by simp⟩`.
-/
theorem isForm_zero (k : I → ℕ) : D.IsForm k 0 where
  hol x := ⟨continuous_const, fun _ _ => holomorphic_on_half_plane_zero⟩
  aut γ z x := by simp
  lev z x h := by simp
  bdd := ⟨0, fun z x => by simp⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨(hf.hol x).1.add (hg.hol x).1, fun z v => holomorphic_on_half_plane_add _ _ ((hf.hol x).2 z v) ((hg.hol x).2 z v)⟩ aut γ z x := by simp [Pi.add_apply, hf.aut, hg.aut, mul_add] lev z x h := by simp [Pi.add_apply, hf.lev, hg.lev, mul_add] bdd := by obtain ⟨C₁, h₁⟩ := hf.bdd obtain …`.
-/
theorem isForm_add (k : I → ℕ) (f g : X I × Gf → ℂ) (hf : D.IsForm k f) (hg : D.IsForm k g) :
    D.IsForm k (f + g) where
  hol x := ⟨(hf.hol x).1.add (hg.hol x).1, fun z v => holomorphic_on_half_plane_add _ _ ((hf.hol x).2 z v) ((hg.hol x).2 z v)⟩
  aut γ z x := by simp [Pi.add_apply, hf.aut, hg.aut, mul_add]
  lev z x h := by simp [Pi.add_apply, hf.lev, hg.lev, mul_add]
  bdd := by
    obtain ⟨C₁, h₁⟩ := hf.bdd
    obtain ⟨C₂, h₂⟩ := hg.bdd
    refine ⟨C₁ + C₂, fun z x => ?_⟩
    have hn := nrm_nonneg k z
    calc ‖(f + g) (z, x)‖ * nrm k z ≤ (‖f (z, x)‖ + ‖g (z, x)‖) * nrm k z :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) hn
      _ = ‖f (z, x)‖ * nrm k z + ‖g (z, x)‖ * nrm k z := add_mul _ _ _
      _ ≤ C₁ + C₂ := add_le_add (h₁ z x) (h₂ z x)

/- English proof (translation)
Assemble the required witnesses or components as `⟨continuous_const.mul (hf.hol x).1, fun z v => holomorphic_on_half_plane_const_mul c _ ((hf.hol x).2 z v)⟩ aut γ z x := by simp [Pi.smul_apply, hf.aut]; ring lev z x h := by simp [Pi.smul_apply, hf.lev]; ring bdd := by obtain ⟨C, h⟩ := hf.bdd refine ⟨‖c‖ * C, fun z x => ?_⟩ have …`.
-/
theorem isForm_smul (k : I → ℕ) (c : ℂ) (f : X I × Gf → ℂ) (hf : D.IsForm k f) :
    D.IsForm k (c • f) where
  hol x := ⟨continuous_const.mul (hf.hol x).1, fun z v => holomorphic_on_half_plane_const_mul c _ ((hf.hol x).2 z v)⟩
  aut γ z x := by simp [Pi.smul_apply, hf.aut]; ring
  lev z x h := by simp [Pi.smul_apply, hf.lev]; ring
  bdd := by
    obtain ⟨C, h⟩ := hf.bdd
    refine ⟨‖c‖ * C, fun z x => ?_⟩
    have := h z x
    have hc := norm_nonneg c
    calc ‖(c • f) (z, x)‖ * nrm k z = ‖c‖ * (‖f (z, x)‖ * nrm k z) := by
          rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      _ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left this hc

def S (k : I → ℕ) : Submodule ℂ (X I × Gf → ℂ) where
  carrier := {f | D.IsForm k f}
  add_mem' {f g} hf hg := isForm_add D k f g hf hg
  zero_mem' := isForm_zero D k
  smul_mem' c f hf := isForm_smul D k c f hf

/- English proof (translation)
The claim follows from `Submodule.span_eq (S D k)`.
-/
theorem M_eq (k : I → ℕ) : D.M k = S D k := Submodule.span_eq (S D k)

/- English proof (translation)
Rewrite using `[M_eq]`. Both sides reduce to the same expression.
-/
theorem mem_M (k : I → ℕ) (f : X I × Gf → ℂ) : f ∈ D.M k ↔ D.IsForm k f := by
  rw [M_eq]; rfl

open Classical in
/- English proof (translation)
Use `⟨?_, fun z v => ?_⟩` and prove the remaining obligations. Simplify using `only [op_apply]`. Conclude with `continuous_finsetSum _ fun i _ => (hf.hol (x * a i)).1`. Simplify using `only [op_apply]`. Conclude with `holomorphic_on_half_plane_finset_sum Finset.univ (fun i t => f (Function.update z v t, x * a i)) (fun i _ => (hf.hol (x * a i)).2 z v)`.

Use `aut γ z x := by`. Simplify using `only [op_apply]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, hf.aut]`.

Use `lev z x h := by`. Simplify using `only [op_apply]`. Conclude with `ha (fun y => f (z, y)) (fun y h' => hf.lev z y h') x h`. Use `bdd := by`. Take `⟨C, hC⟩` from `hf.bdd`.

Use `⟨Fintype.card ι * C, fun z x => ?_⟩` and prove the remaining obligations. Establish `hn` using `nrm_nonneg k z`. Simplify using `only [op_apply]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isForm_op (k : I → ℕ) {ι : Type} [Fintype ι] (a : ι → Gf) (ha : D.Good a)
    (f : X I × Gf → ℂ) (hf : D.IsForm k f) : D.IsForm k (Dat.Op a f) where
  hol x := by
    refine ⟨?_, fun z v => ?_⟩
    · simp only [op_apply]
      exact continuous_finsetSum _ fun i _ => (hf.hol (x * a i)).1
    · simp only [op_apply]
      exact holomorphic_on_half_plane_finset_sum Finset.univ (fun i t => f (Function.update z v t, x * a i))
        (fun i _ => (hf.hol (x * a i)).2 z v)
  aut γ z x := by
    simp only [op_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, hf.aut]
  lev z x h := by
    simp only [op_apply]
    exact ha (fun y => f (z, y)) (fun y h' => hf.lev z y h') x h
  bdd := by
    obtain ⟨C, hC⟩ := hf.bdd
    refine ⟨Fintype.card ι * C, fun z x => ?_⟩
    have hn := nrm_nonneg k z
    simp only [op_apply]
    calc ‖∑ i, f (z, x * a i)‖ * nrm k z ≤ (∑ i, ‖f (z, x * a i)‖) * nrm k z :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) hn
      _ = ∑ i, ‖f (z, x * a i)‖ * nrm k z := Finset.sum_mul _ _ _
      _ ≤ ∑ _i : ι, C := Finset.sum_le_sum fun i _ => hC z (x * a i)
      _ = Fintype.card ι * C := by simp

/- English proof (translation)
Use `⟨mem_M D k, fun ι _ a ha f hf => ?_⟩` and prove the remaining obligations. Rewrite `hf`, the goal using `[mem_M]`. Conclude with `isForm_op D k a ha f hf`.
-/
theorem main (k : I → ℕ) : (∀ f, f ∈ D.M k ↔ D.IsForm k f) ∧
    ∀ (ι : Type) [Fintype ι] (a : ι → Gf), D.Good a → ∀ f ∈ D.M k, Dat.Op a f ∈ D.M k := by
  refine ⟨mem_M D k, fun ι _ a ha f hf => ?_⟩
  rw [mem_M] at hf ⊢
  exact isForm_op D k a ha f hf

end UpperTheory.Esk.FormsStableLemmas

/- English proof (translation)
Introduce `_ _ _ _ _ _ D _ k` and use `UpperTheory.Esk.FormsStableLemmas.main D k`.
-/
theorem UpperTheory.Esk.forms_stable_under_operators_proof : UpperTheory.Esk.FormsStableUnderOperators :=
  fun _ _ _ _ _ _ D _ k => UpperTheory.Esk.FormsStableLemmas.main D k
