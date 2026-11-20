import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Introduce `N s _ hs`. Establish `hsum : Summable fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => ((n : ℕ) : ℂ) ^ (-(2 * s))`. Establish `h : Summable fun n : ℕ => 1 / (n : ℂ) ^ (2 * s)` using `Complex.summable_one_div_nat_cpow.2 (by simp; linarith)`. Use `(h.subtype _).congr fun n => ?_` and prove the remaining obligations. Simplify using `[Complex.cpow_neg]`.

Establish `hinj : Function.Injective fun m : {n : ℕ // 0 < n ∧ n.Coprime N} => (m : ℕ) * m` using `fun a b e => Subtype.ext (Nat.mul_self_inj.1 e)`. Establish `h2 : HasSum (LSeries.term (sqN N) s) (∑' n : {n : ℕ // 0 < n ∧ n.Coprime N}, ((n : ℕ) : ℂ) ^ (-(2 * s)))`. Use `(hinj.hasSum_iff fun x hx => ?_).1 ?_` and prove the remaining obligations. Break down `eq_or_ne x 0 with rfl | h0` into its components or cases. Simplify using the standard rewrite rules.

Rewrite using `[LSeries.term_of_ne_zero h0, sqN, if_neg, zero_div]`. Introduce and unpack `⟨m, rfl, hm⟩`. Conclude with `hx ⟨⟨m, Nat.pos_of_ne_zero fun e => h0 (by simp [e]), hm⟩, rfl⟩`. Use `hsum.hasSum using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `m`.

Establish `h0 : (m : ℕ) * m ≠ 0` using `mul_ne_zero m.2.1.ne' m.2.1.ne'`. Rewrite using `[Function.comp_apply, LSeries.term_of_ne_zero h0, sqN, if_pos ⟨m, rfl, m.2.2⟩, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Complex.cpow_neg, two_mul, Complex.cpow_add _ _ (Nat.cast_ne_zero.2 m.2.1.ne'), one_div]`. Rewrite using `[LSeries, h2.tsum_eq]`. Conclude with `hsum.hasSum`.
-/
theorem UpperTheory.hasSum_coprime_inv_pow_two_mul_eq_LSeries :
    ∀ (N : ℕ) (s : ℂ), 0 < N → 1 < s.re → HasSum (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => ((n : ℕ) : ℂ) ^ (-(2 * s))) (LSeries (sqN N) s) := by
  intro N s _ hs
  have hsum : Summable fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => ((n : ℕ) : ℂ) ^ (-(2 * s)) := by
    have h : Summable fun n : ℕ => 1 / (n : ℂ) ^ (2 * s) :=
      Complex.summable_one_div_nat_cpow.2 (by simp; linarith)
    refine (h.subtype _).congr fun n => ?_
    simp [Complex.cpow_neg]
  have hinj : Function.Injective fun m : {n : ℕ // 0 < n ∧ n.Coprime N} => (m : ℕ) * m := fun a b e =>
    Subtype.ext (Nat.mul_self_inj.1 e)
  have h2 : HasSum (LSeries.term (sqN N) s) (∑' n : {n : ℕ // 0 < n ∧ n.Coprime N}, ((n : ℕ) : ℂ) ^ (-(2 * s))) := by
    refine (hinj.hasSum_iff fun x hx => ?_).1 ?_
    · rcases eq_or_ne x 0 with rfl | h0
      · simp
      · rw [LSeries.term_of_ne_zero h0, sqN, if_neg, zero_div]
        rintro ⟨m, rfl, hm⟩
        exact hx ⟨⟨m, Nat.pos_of_ne_zero fun e => h0 (by simp [e]), hm⟩, rfl⟩
    · convert hsum.hasSum using 1
      funext m
      have h0 : (m : ℕ) * m ≠ 0 := mul_ne_zero m.2.1.ne' m.2.1.ne'
      rw [Function.comp_apply, LSeries.term_of_ne_zero h0, sqN, if_pos ⟨m, rfl, m.2.2⟩, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, Complex.cpow_neg, two_mul,
        Complex.cpow_add _ _ (Nat.cast_ne_zero.2 m.2.1.ne'), one_div]
  rw [LSeries, h2.tsum_eq]
  exact hsum.hasSum
