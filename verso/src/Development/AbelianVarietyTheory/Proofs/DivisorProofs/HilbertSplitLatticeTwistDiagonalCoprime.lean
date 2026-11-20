import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHilbertLatticeTwistIffLiftStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

/- English proof (translation)
Introduce `F _ _ _ N 𝔞 𝔟 x a hcop hlev`. Establish `hstd : ∀ w : Fin 2 → F, w ∈ stdLat F ↔ ∀ i, w i ∈ (1 : Submodule (𝓞 F) F)`. Introduce `w`. Simplify using `only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff]`. Establish `hsp : ∀ (z : F) (w : Fin 2 → F), w ∈ split 𝔞 𝔟 z ↔ w 0 ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : Submodule (𝓞 F) F) ∧ w 1 - w 0 * z ∈ (latM 𝔞 : Submodule (𝓞 F) F)` using `fun _ _ ↦ Iff.rfl`.

Establish `hA : (Matrix.diagonal ![1, (a : ZMod N)]) = (Matrix.diagonal ![(1 : ℤ), a]).map (Int.cast : ℤ → ZMod N)`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp`. Establish `hv0 : ∀ y : Fin 2 → F, Matrix.vecMul y ((Matrix.diagonal ![(1 : ℤ), a]).map (Int.cast : ℤ → F)) = ![y 0, a * y 1]`. Introduce `y`. Apply the tactic sequence `ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]`.

Establish `hN : ∀ w ∈ stdLat F, (N : F) • w ∈ split 𝔞 𝔟 x`. Introduce `w hw`. Establish `h` using `hlev.1 w hw`. Rewrite `h`, the goal using `[Nat.cast_smul_eq_nsmul]`. Conclude with `h`.

Establish `hz : ∀ (n : ℤ) (S : Submodule (𝓞 F) F) (m : F), m ∈ S → (n : F) * m ∈ S`. Introduce `n S m hm`. Rewrite using `[← zsmul_eq_mul]`. Conclude with `zsmul_mem hm n`. Use extensionality with `v`.

Rewrite using `[hA, GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N _ _ v hlev.2]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, w, hw, rfl⟩`. Rewrite using `[hv0]`. Establish `hw'` using `(hstd w).1 hw`.

Establish `h0` using `(hsp _ _).1 (hN ![w 0, 0] ((hstd _).2 (by`. Introduce `i`. Use `fin_cases i`. Conclude with `hw' 0`. Conclude with `Submodule.zero_mem _)))`.

Establish `h1` using `(hsp _ _).1 (hN ![0, w 1] ((hstd _).2 (by`. Introduce `i`. Use `fin_cases i`. Conclude with `Submodule.zero_mem _`. Conclude with `hw' 1)))`.

Establish `hy'` using `(hsp _ _).1 hy`. Rewrite using `[hsp]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `Submodule.add_mem _ hy'.1 h0.1` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using the standard rewrite rules. Use `Submodule.add_mem _ (Submodule.add_mem _ (hz a _ _ hy'.2) h1.2) (hz a _ _ h0.2)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Introduce `hv`. Establish `hv'` using `(hsp _ _).1 hv`. Take `⟨u, t, hut⟩` from `hcop`. Establish `hut' : (u : F) * a + t * N = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → F) hut`. Establish `hm : ![0, v 1 - v 0 * (a * x)] ∈ split 𝔞 𝔟 x`.

Rewrite using `[hsp]`. Use `⟨Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Use `hv'.2 using 1` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules. Establish `hm'` using `(hstd _).1 (hlev.2 hm) 1`.

Use `⟨![v 0, v 0 * x + u * (v 1 - v 0 * (a * x))], ?_, ![0, t * (v 1 - v 0 * (a * x))], ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hsp]`. Use `⟨hv'.1, ?_⟩` and prove the remaining obligations. Use `hz u _ _ hv'.2 using 1` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules.

Rewrite using `[hstd]`. Introduce `i`. Use `fin_cases i`. Conclude with `Submodule.zero_mem _`. Conclude with `hz t _ _ hm'`.

Rewrite using `[hv0]`. Use extensionality with `j`. Use `fin_cases j`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Take the linear combination `(-(v 1 - v 0 * (a * x))) * hut'`.
-/
theorem twist_split_diagonal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x : F) (a : ℤ), IsCoprime a (N : ℤ) → HasLevel N (split 𝔞 𝔟 x) → twist N (split 𝔞 𝔟 x) (Matrix.diagonal ![1, (a : ZMod N)]) = split 𝔞 𝔟 (a * x) := by
  intro F _ _ _ N 𝔞 𝔟 x a hcop hlev
  have hstd : ∀ w : Fin 2 → F, w ∈ stdLat F ↔ ∀ i, w i ∈ (1 : Submodule (𝓞 F) F) := by
    intro w; simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  have hsp : ∀ (z : F) (w : Fin 2 → F), w ∈ split 𝔞 𝔟 z ↔
      w 0 ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : Submodule (𝓞 F) F) ∧
      w 1 - w 0 * z ∈ (latM 𝔞 : Submodule (𝓞 F) F) := fun _ _ ↦ Iff.rfl
  have hA : (Matrix.diagonal ![1, (a : ZMod N)]) =
      (Matrix.diagonal ![(1 : ℤ), a]).map (Int.cast : ℤ → ZMod N) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hv0 : ∀ y : Fin 2 → F,
      Matrix.vecMul y ((Matrix.diagonal ![(1 : ℤ), a]).map (Int.cast : ℤ → F)) = ![y 0, a * y 1] := by
    intro y
    ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  have hN : ∀ w ∈ stdLat F, (N : F) • w ∈ split 𝔞 𝔟 x := by
    intro w hw
    have h := hlev.1 w hw
    rw [Nat.cast_smul_eq_nsmul] at h ⊢
    exact h
  have hz : ∀ (n : ℤ) (S : Submodule (𝓞 F) F) (m : F), m ∈ S → (n : F) * m ∈ S := by
    intro n S m hm
    rw [← zsmul_eq_mul]
    exact zsmul_mem hm n
  ext v
  rw [hA, GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N _ _ v hlev.2]
  constructor
  · rintro ⟨y, hy, w, hw, rfl⟩
    rw [hv0]
    have hw' := (hstd w).1 hw
    have h0 := (hsp _ _).1 (hN ![w 0, 0] ((hstd _).2 (by
      intro i; fin_cases i
      · exact hw' 0
      · exact Submodule.zero_mem _)))
    have h1 := (hsp _ _).1 (hN ![0, w 1] ((hstd _).2 (by
      intro i; fin_cases i
      · exact Submodule.zero_mem _
      · exact hw' 1)))
    have hy' := (hsp _ _).1 hy
    rw [hsp]
    refine ⟨?_, ?_⟩
    · have := Submodule.add_mem _ hy'.1 h0.1
      convert this using 1
      simp
    · have := Submodule.add_mem _ (Submodule.add_mem _ (hz a _ _ hy'.2) h1.2) (hz a _ _ h0.2)
      convert this using 1
      simp
      ring
  · intro hv
    have hv' := (hsp _ _).1 hv
    obtain ⟨u, t, hut⟩ := hcop
    have hut' : (u : F) * a + t * N = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → F) hut
    have hm : ![0, v 1 - v 0 * (a * x)] ∈ split 𝔞 𝔟 x := by
      rw [hsp]
      refine ⟨Submodule.zero_mem _, ?_⟩
      convert hv'.2 using 1
      simp
    have hm' := (hstd _).1 (hlev.2 hm) 1
    refine ⟨![v 0, v 0 * x + u * (v 1 - v 0 * (a * x))], ?_, ![0, t * (v 1 - v 0 * (a * x))], ?_, ?_⟩
    · rw [hsp]
      refine ⟨hv'.1, ?_⟩
      convert hz u _ _ hv'.2 using 1
      simp
    · rw [hstd]
      intro i; fin_cases i
      · exact Submodule.zero_mem _
      · exact hz t _ _ hm'
    · rw [hv0]
      ext j; fin_cases j
      · simp
      · simp
        linear_combination (-(v 1 - v 0 * (a * x))) * hut'

end GlobalTheory.HilbFam
