import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleSimpleCharZeroStatement
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Unfold `sqAct`. Establish `hm` using `congrArg (fun φ => φ f) (Formalism.GradedWeylDivisibility.rowActMul K n n ((g : Matrix (Fin n) (Fin n) K)ᵀ) ((h : Matrix (Fin n) (Fin n) K)ᵀ))`. Simplify using `only [AlgHom.comp_apply] at hm`. Rewrite using `[map_smul, hm, smul_smul, ← Matrix.transpose_mul]`. Use `congr 1`.

Unfold `detPow`. Rewrite using `[map_mul, mul_zpow, Units.val_mul]`.
-/
theorem sqAct_sqAct_nabla (K : Type) [Field K] (n : ℕ) (lam : DomWeight n) (g h : GL (Fin n) K)
    (f : MvPolynomial (Fin n × Fin n) K) :
    sqAct K n lam g (sqAct K n lam h f) = sqAct K n lam (g * h) f := by
  unfold sqAct
  have hm := congrArg (fun φ => φ f) (Formalism.GradedWeylDivisibility.rowActMul K n n
    ((g : Matrix (Fin n) (Fin n) K)ᵀ) ((h : Matrix (Fin n) (Fin n) K)ᵀ))
  simp only [AlgHom.comp_apply] at hm
  rw [map_smul, hm, smul_smul, ← Matrix.transpose_mul]
  congr 1
  unfold detPow
  rw [map_mul, mul_zpow, Units.val_mul]

/- English proof (translation)
Unfold `sqAct detPow`. Simplify using `only [Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one, map_one, one_zpow, Units.val_one, one_smul]`. Establish `h1 : Formalism.GradedWeylDivisibility.rowAct K (n` using `n) (1 : Matrix (Fin n) (Fin n) K) = AlgHom.id K _ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`.

Unfold `Formalism.GradedWeylDivisibility.rowAct`. Rewrite using `[aeval_X]`. Simplify using `[Matrix.one_apply, ite_mul]`. Rewrite using `[h1]`. Both sides reduce to the same expression.
-/
theorem sqAct_one_nabla (K : Type) [Field K] (n : ℕ) (lam : DomWeight n)
    (f : MvPolynomial (Fin n × Fin n) K) : sqAct K n lam 1 f = f := by
  unfold sqAct detPow
  simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one, map_one, one_zpow, Units.val_one, one_smul]
  have h1 : Formalism.GradedWeylDivisibility.rowAct K (n := n) (1 : Matrix (Fin n) (Fin n) K) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro v
    unfold Formalism.GradedWeylDivisibility.rowAct
    rw [aeval_X]
    simp [Matrix.one_apply, ite_mul]
  rw [h1]; rfl

/- English proof (translation)
Introduce `K _ _ n lam`. Use `set M := Submodule.span K (Set.range fun g : GL (Fin n) K => sqAct K n lam g (extremal K n lam)) with hM`. Establish `hanti : Antitone lam.natW`. Introduce `i j hij`. Use `lam.anti hij` as an intermediate fact.

Unfold `DomWeight.natW`. Use linear arithmetic over natural numbers and integers. Establish `hext : extremal K n lam ∈ nablaSq K n lam` using `Formalism.GradedWeylDivisibility.hwMem K n n le_rfl lam.natW hanti`. Establish `hstab : ∀ g : GL (Fin n) K, ∀ f ∈ nablaSq K n lam, sqAct K n lam g f ∈ nablaSq K n lam`. Introduce `g f hf`.

Unfold `sqAct`. Conclude with `Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable K n n lam.natW _ f hf)`. Establish `hle : M ≤ nablaSq K n lam`. Rewrite using `[hM, Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`.

Conclude with `hstab g _ hext`. Establish `hlin : ∀ g : GL (Fin n) K, ∀ (c : K) (f₁ f₂ : MvPolynomial (Fin n × Fin n) K), sqAct K n lam g (c • f₁ + f₂) = c • sqAct K n lam g f₁ + sqAct K n lam g f₂`. Introduce `g c f₁ f₂`. Unfold `sqAct`. Rewrite using `[map_add, map_smul, smul_add, smul_comm]`.

Establish `hMstab : ∀ g : GL (Fin n) K, ∀ f ∈ M, sqAct K n lam g f ∈ M`. Introduce `g f hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨h, rfl⟩` from `hx`.

Rewrite using `[sqAct_sqAct_nabla]`. Conclude with `Submodule.subset_span ⟨g * h, rfl⟩`. Consider the case `zero`. Establish `h0 : sqAct K n lam g 0 = 0` using `by unfold sqAct; simp`. Rewrite using `[h0]`.

Conclude with `M.zero_mem`. Consider the case `add x y _ _ hx hy`. Use `hlin g 1 x y` as an intermediate fact. Rewrite `this` using `[one_smul, one_smul]`. Rewrite using `[this]`.

Conclude with `M.add_mem hx hy`. Consider the case `smul c x _ hx`. Establish `hs : sqAct K n lam g (c • x) = c • sqAct K n lam g x`. Unfold `sqAct`. Rewrite using `[map_smul, smul_comm]`.

Rewrite using `[hs]`. Conclude with `M.smul_mem c hx`. Break down `GlobalTheory.T.dualWeylModule_simple_charZero K n lam M hle hMstab with h0 | h1` into its components or cases. It suffices to derive a contradiction. Establish `hmem : extremal K n lam ∈ M`.

Establish `: sqAct K n lam 1 (extremal K n lam) ∈ M` using `Submodule.subset_span ⟨1, rfl⟩`. Rewrite `this` using `[sqAct_one_nabla]`. Then use the resulting hypothesis. Rewrite `hmem` using `[h0, Submodule.mem_bot]`. Conclude with `Formalism.GradedWeylDivisibility.hwNe K n n le_rfl lam.natW hmem`. Rewrite using `[h1]`.
-/
theorem nablaSq_le_span_extremal : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight n),
    nablaSq K n lam ≤ Submodule.span K (Set.range fun g : GL (Fin n) K => sqAct K n lam g (extremal K n lam)) := by
  intro K _ _ n lam
  set M := Submodule.span K (Set.range fun g : GL (Fin n) K => sqAct K n lam g (extremal K n lam)) with hM
  have hanti : Antitone lam.natW := by
    intro i j hij
    have := lam.anti hij
    unfold DomWeight.natW
    omega
  have hext : extremal K n lam ∈ nablaSq K n lam :=
    Formalism.GradedWeylDivisibility.hwMem K n n le_rfl lam.natW hanti
  have hstab : ∀ g : GL (Fin n) K, ∀ f ∈ nablaSq K n lam, sqAct K n lam g f ∈ nablaSq K n lam := by
    intro g f hf
    unfold sqAct
    exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable K n n lam.natW _ f hf)
  have hle : M ≤ nablaSq K n lam := by
    rw [hM, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hstab g _ hext
  have hlin : ∀ g : GL (Fin n) K, ∀ (c : K) (f₁ f₂ : MvPolynomial (Fin n × Fin n) K),
      sqAct K n lam g (c • f₁ + f₂) = c • sqAct K n lam g f₁ + sqAct K n lam g f₂ := by
    intro g c f₁ f₂
    unfold sqAct
    rw [map_add, map_smul, smul_add, smul_comm]
  have hMstab : ∀ g : GL (Fin n) K, ∀ f ∈ M, sqAct K n lam g f ∈ M := by
    intro g f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [sqAct_sqAct_nabla]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero =>
      have h0 : sqAct K n lam g 0 = 0 := by unfold sqAct; simp
      rw [h0]; exact M.zero_mem
    | add x y _ _ hx hy =>
      have := hlin g 1 x y
      rw [one_smul, one_smul] at this
      rw [this]; exact M.add_mem hx hy
    | smul c x _ hx =>
      have hs : sqAct K n lam g (c • x) = c • sqAct K n lam g x := by
        unfold sqAct; rw [map_smul, smul_comm]
      rw [hs]; exact M.smul_mem c hx
  rcases GlobalTheory.T.dualWeylModule_simple_charZero K n lam M hle hMstab with h0 | h1
  · exfalso
    have hmem : extremal K n lam ∈ M := by
      have : sqAct K n lam 1 (extremal K n lam) ∈ M := Submodule.subset_span ⟨1, rfl⟩
      rwa [sqAct_one_nabla] at this
    rw [h0, Submodule.mem_bot] at hmem
    exact Formalism.GradedWeylDivisibility.hwNe K n n le_rfl lam.natW hmem
  · rw [h1]

end GlobalTheory
