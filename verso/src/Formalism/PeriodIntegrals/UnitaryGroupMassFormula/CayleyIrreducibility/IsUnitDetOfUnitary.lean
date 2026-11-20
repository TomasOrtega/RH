import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.DivClosedOf

noncomputable section

namespace Formalism.L2.SG.Pf.ColDictValCPf

open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder

section Transfer

variable {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Simplify using `[fnOfV]`.
-/
lemma fnOfV_one_apply (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : FramesV G) :
    fnOfV G s 1 P y = (∏ τ, (y.1 τ).det ^ s τ) * eval (fun x => y.1 x.1 x.2.1 x.2.2) P := by
  simp [fnOfV]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp [famAct]`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq, map_add]`. Consider the case `mul_X p v hp => rw [map_mul, map_mul, hp, map_mul]`. Simplify using `[famAct]`.
-/
lemma eval_famAct (g : ι → Matrix (Fin n) (Fin n) ℂ) (x : ι × Fin n × Fin n → ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    eval x (famAct g P) = eval (fun v => ∑ c : Fin n, g v.1 v.2.1 c * x (v.1, c, v.2.2)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [famAct]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul]; simp [famAct]

def detBlocks : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  ∏ τ, (Matrix.of fun a b : Fin n => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det

/- English proof (translation)
Rewrite using `[detBlocks, map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `a b`.

Simplify using the standard rewrite rules.
-/
lemma eval_detBlocks (x : ι × Fin n × Fin n → ℂ) :
    eval x (detBlocks (ι := ι) (n := n)) = ∏ τ, (Matrix.of fun a b : Fin n => x (τ, a, b)).det := by
  rw [detBlocks, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

/- English proof (translation)
Introduce `h`. Establish `hx` using `eval_detBlocks (ι := ι) (n := n) (fun v => (1 : Matrix (Fin n) (Fin n) ℂ) v.2.1 v.2.2)`. Rewrite `hx` using `[h, map_zero]`. Establish `h1 : ∀ τ : ι, (Matrix.of fun a b : Fin n => (fun v : ι × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) v.2.1 v.2.2) (τ, a, b)) = 1` using `fun τ => by`. Use extensionality with `a b`.

Simplify using the standard rewrite rules. Simplify using `[h1] at hx`.
-/
lemma detBlocks_ne_zero : (detBlocks (ι := ι) (n := n)) ≠ 0 := by
  intro h
  have hx := eval_detBlocks (ι := ι) (n := n) (fun v => (1 : Matrix (Fin n) (Fin n) ℂ) v.2.1 v.2.2)
  rw [h, map_zero] at hx
  have h1 : ∀ τ : ι, (Matrix.of fun a b : Fin n => (fun v : ι × Fin n × Fin n =>
      (1 : Matrix (Fin n) (Fin n) ℂ) v.2.1 v.2.2) (τ, a, b)) = 1 := fun τ => by
    ext a b
    simp
  simp [h1] at hx

/- English proof (translation)
Establish `hz : detBlocks (ι` using `ι) (n := n) * P = 0 := by`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[map_mul, map_zero, eval_detBlocks]`. Distinguish the cases in `hx : ∀ τ, (Matrix.of fun a b : Fin n => x (τ, a, b)).det ≠ 0`.

Take `⟨y0, hy0⟩ : ∃ y0 : FramesV G, ∀ τ, y0.1 τ = Matrix.of fun a b => x (τ, a, b)` from `⟨⟨fun τ => Matrix.of fun a b => x (τ, a, b), fun τ => (hx τ).isUnit⟩, fun _ => rfl⟩`. Establish `hy : fnOfV G s 1 P y0 = 0` using `by rw [h]; rfl`. Rewrite `hy` using `[fnOfV_one_apply]`. Simplify using `only [hy0, Matrix.of_apply] at hy`. Break down `mul_eq_zero.mp hy with h0 | h0` into its components or cases.

Conclude with `absurd h0 (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ))`. Conclude with `mul_eq_zero_of_right _ h0`. Use `push_neg at hx`. Take `⟨τ, hτ⟩` from `hx`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ τ) hτ, zero_mul]`.

Simplify `hz` using `[detBlocks_ne_zero]`.
-/
lemma fnOfV_injective (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (h : fnOfV G s 1 P = 0) : P = 0 := by
  have hz : detBlocks (ι := ι) (n := n) * P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero, eval_detBlocks]
    by_cases hx : ∀ τ, (Matrix.of fun a b : Fin n => x (τ, a, b)).det ≠ 0
    · obtain ⟨y0, hy0⟩ : ∃ y0 : FramesV G, ∀ τ, y0.1 τ = Matrix.of fun a b => x (τ, a, b) :=
        ⟨⟨fun τ => Matrix.of fun a b => x (τ, a, b), fun τ => (hx τ).isUnit⟩, fun _ => rfl⟩
      have hy : fnOfV G s 1 P y0 = 0 := by rw [h]; rfl
      rw [fnOfV_one_apply] at hy
      simp only [hy0, Matrix.of_apply] at hy
      rcases mul_eq_zero.mp hy with h0 | h0
      · exact absurd h0 (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ))
      · exact mul_eq_zero_of_right _ h0
    · push_neg at hx
      obtain ⟨τ, hτ⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, zero_mul]
  simpa [detBlocks_ne_zero] using hz

/- English proof (translation)
Establish `hGd : G.det ≠ 0`. Break down `hG with h | h` into its components or cases. Conclude with `h.det_pos.ne'`. Establish `h2` using `h.det_pos.ne'`. Rewrite `h2` using `[Matrix.det_neg]`.

Introduce `h0`. Apply `h2` to reduce the goal to its premises. Rewrite using `[h0, mul_zero]`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `hg0`.

Establish `h3` using `congrArg Matrix.det hg`. Rewrite `h3` using `[Matrix.det_mul, Matrix.det_mul, hg0, mul_zero]`. Conclude with `hGd h3.symm`.
-/
lemma isUnit_det_of_unitary {G g : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef ∨ (-G).PosDef)
    (hg : gᴴ * G * g = G) : IsUnit g.det := by
  have hGd : G.det ≠ 0 := by
    rcases hG with h | h
    · exact h.det_pos.ne'
    · have h2 := h.det_pos.ne'
      rw [Matrix.det_neg] at h2
      intro h0
      apply h2
      rw [h0, mul_zero]
  rw [isUnit_iff_ne_zero]
  intro hg0
  have h3 := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, hg0, mul_zero] at h3
  exact hGd h3.symm

/- English proof (translation)
Introduce `ι _ n G hG lam W hW hne hinv`. Use `set φ := fnOfV G (shiftOfV lam) 1 with hφ`. Establish `hinj : Function.Injective φ` using `fun P Q hPQ => by`. Establish `h0 : φ (P - Q) = 0` using `by rw [map_sub, hPQ, sub_self]`. Conclude with `sub_eq_zero.mp (fnOfV_injective G _ _ h0)`.

Use `⟨W.comap φ ⊓ CSpanV lam, inf_le_right, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨F, hFW, hF0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Take `⟨P, hP, rfl⟩` from `hW hFW`. Introduce `hbot`. Establish `hPM : P ∈ W.comap φ ⊓ CSpanV lam` using `Submodule.mem_inf.mpr ⟨hFW, hP⟩`.

Rewrite `hPM` using `[hbot, Submodule.mem_bot]`. Conclude with `hF0 (by rw [hPM, map_zero])`. Introduce `g hg P hPM`. Take `⟨hPW, hPC⟩` from `Submodule.mem_inf.mp hPM`. Establish `hPW' : φ P ∈ W` using `Submodule.mem_comap.mp hPW`.

Take `⟨F', hF'W, hF'⟩` from `hinv g hg (φ P) hPW'`. Establish `hdet : ∀ τ, IsUnit (g τ).det` using `fun τ => isUnit_det_of_unitary (hG τ) (hg τ)`. Use `set cst : ℂ := ∏ τ, (g τ).det ^ (shiftOfV lam τ) with hcst`. Establish `hcst0 : cst ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hdet τ).ne_zero`. Establish `key : φ (famAct g P) = cst⁻¹ • F'`.

Use function extensionality and compare the values at `y`. Take `⟨y', hy'0⟩ : ∃ y' : FramesV G, ∀ τ, y'.1 τ = g τ * y.1 τ` from `⟨⟨fun τ => g τ * y.1 τ, fun τ => by`. Rewrite using `[Matrix.det_mul]`. Conclude with `(hdet τ).mul (y.2 τ)⟩, fun _ => rfl⟩`. Establish `hy'` using `hF' y y' hy'0`.

Use `show _ = cst⁻¹ * F' y`. Rewrite using `[hy', hφ, fnOfV_one_apply, fnOfV_one_apply, eval_famAct]`. Simplify using `only [hy'0, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_apply]`. Rewrite using `[← hcst]`. Clear the denominators using the available nonvanishing facts.

Establish `hmemW : φ (famAct g P) ∈ W`. Rewrite using `[key]`. Conclude with `W.smul_mem _ hF'W`. Take `⟨P', hP'C, hP'⟩` from `hW hF'W`. Establish `hfam : famAct g P = cst⁻¹ • P'` using `hinj (by rw [key, map_smul, hP'])`.

Use `Submodule.mem_inf.mpr ⟨hmemW, ?_⟩` and prove the remaining obligations. Rewrite using `[hfam]`. Conclude with `(CSpanV lam).smul_mem _ hP'C`. Introduce `hle`. Apply `le_antisymm hW` to reduce the goal to its premises.

Introduce and unpack `F ⟨P, hP, rfl⟩`. Conclude with `(Submodule.mem_inf.mp (hle hP)).1`.
-/
theorem transfer_holds : Transfer := by
  intro ι _ n G hG lam W hW hne hinv
  set φ := fnOfV G (shiftOfV lam) 1 with hφ
  have hinj : Function.Injective φ := fun P Q hPQ => by
    have h0 : φ (P - Q) = 0 := by rw [map_sub, hPQ, sub_self]
    exact sub_eq_zero.mp (fnOfV_injective G _ _ h0)
  refine ⟨W.comap φ ⊓ CSpanV lam, inf_le_right, ?_, ?_, ?_⟩
  · obtain ⟨F, hFW, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨P, hP, rfl⟩ := hW hFW
    intro hbot
    have hPM : P ∈ W.comap φ ⊓ CSpanV lam := Submodule.mem_inf.mpr ⟨hFW, hP⟩
    rw [hbot, Submodule.mem_bot] at hPM
    exact hF0 (by rw [hPM, map_zero])
  · intro g hg P hPM
    obtain ⟨hPW, hPC⟩ := Submodule.mem_inf.mp hPM
    have hPW' : φ P ∈ W := Submodule.mem_comap.mp hPW
    obtain ⟨F', hF'W, hF'⟩ := hinv g hg (φ P) hPW'
    have hdet : ∀ τ, IsUnit (g τ).det := fun τ => isUnit_det_of_unitary (hG τ) (hg τ)
    set cst : ℂ := ∏ τ, (g τ).det ^ (shiftOfV lam τ) with hcst
    have hcst0 : cst ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hdet τ).ne_zero
    have key : φ (famAct g P) = cst⁻¹ • F' := by
      funext y
      obtain ⟨y', hy'0⟩ : ∃ y' : FramesV G, ∀ τ, y'.1 τ = g τ * y.1 τ :=
        ⟨⟨fun τ => g τ * y.1 τ, fun τ => by
          rw [Matrix.det_mul]
          exact (hdet τ).mul (y.2 τ)⟩, fun _ => rfl⟩
      have hy' := hF' y y' hy'0
      show _ = cst⁻¹ * F' y
      rw [hy', hφ, fnOfV_one_apply, fnOfV_one_apply, eval_famAct]
      simp only [hy'0, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_apply]
      rw [← hcst]
      field_simp
    have hmemW : φ (famAct g P) ∈ W := by
      rw [key]
      exact W.smul_mem _ hF'W
    obtain ⟨P', hP'C, hP'⟩ := hW hF'W
    have hfam : famAct g P = cst⁻¹ • P' := hinj (by rw [key, map_smul, hP'])
    refine Submodule.mem_inf.mpr ⟨hmemW, ?_⟩
    rw [hfam]
    exact (CSpanV lam).smul_mem _ hP'C
  · intro hle
    apply le_antisymm hW
    rintro F ⟨P, hP, rfl⟩
    exact (Submodule.mem_inf.mp (hle hP)).1

end Transfer

end Formalism.L2.SG.Pf.ColDictValCPf
