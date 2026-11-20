import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMEulerProducts.StepRegroup

open NumberField

noncomputable section

namespace CMEul

open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory

/- English proof (translation)
Establish `h1 : Ideal.absNorm v ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`. Conclude with `hv.ne_top`. Establish `h0 : Ideal.absNorm v ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `Ring.ne_bot_of_isMaximal_of_not_isField hv (RingOfIntegers.not_isField F)`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_le_absNorm {F : Type} [Field F] [NumberField F] (v : Ideal (𝓞 F)) (hv : v.IsMaximal) :
    2 ≤ Ideal.absNorm v := by
  have h1 : Ideal.absNorm v ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hv.ne_top
  have h0 : Ideal.absNorm v ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField hv (RingOfIntegers.not_isField F)
  omega

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ M hM v hv hS`. Establish `hN2 : (2 : ℝ) ≤ (Ideal.absNorm v : ℝ)` using `by exact_mod_cast two_le_absNorm v hv`. Establish `hNpos : (0 : ℝ) < (Ideal.absNorm v : ℝ)` using `by linarith`. Establish `hx1 : ((Ideal.absNorm v : ℕ) : ℝ) ^ (-(M : ℤ)) < 1`. Rewrite using `[zpow_neg, zpow_natCast]`.

Apply `inv_lt_one_of_one_lt₀` to reduce the goal to its premises. Conclude with `one_lt_pow₀ (by linarith) (by omega)`. Break down `hS with ⟨P, hPm, hPv, hPc, hPN, hPu⟩ | ⟨P, Q, hPm, hQm, hPv, hQv, hPQ, hPc, hQc, hPN, hQN, hu⟩` into its components or cases. Establish `heta : etaF F E v = -1`. Unfold `etaF`.

Rewrite using `[if_pos ⟨P, ⟨hPm, hPv⟩, fun R hR => hPu R hR.1 hR.2⟩]`. Set `p0 : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v}` to `⟨P, hPm, hPv⟩`. Establish `hval : eulerFac E M P = eulerF F E M v`. Unfold `eulerFac eulerF`. Rewrite using `[if_pos hPc, heta, hPN]`.

Use `push_cast`. Rewrite using `[Real.sqrt_sq hNpos.le]`. Use `hasProd_single (f := fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} => eulerFac E M c.1) p0 (fun b hb => by` as an intermediate fact. It suffices to derive a contradiction. Apply `hb` to reduce the goal to its premises.

Conclude with `Subtype.ext (hPu b.1 b.2.1 b.2.2))`. Simplify `this` using `[p0, hval]`. Establish `heta : etaF F E v = 1`. Unfold `etaF`. Rewrite using `[if_neg]`.

Introduce and unpack `⟨R, ⟨hRm, hRv⟩, hR⟩`. Conclude with `hPQ ((hR P ⟨hPm, hPv⟩).trans (hR Q ⟨hQm, hQv⟩).symm)`. Set `p0 : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v}` to `⟨P, hPm, hPv⟩`. Set `q0 : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v}` to `⟨Q, hQm, hQv⟩`. Establish `hne : p0 ≠ q0` using `fun h => hPQ (congrArg Subtype.val h)`.

Use `set y : ℝ := 1 - ((Ideal.absNorm v : ℕ) : ℝ) ^ (-(M : ℤ)) with hy`. Establish `hypos : 0 < y` using `by rw [hy]; linarith`. Establish `hP' : eulerFac E M P = y ^ (-(1 : ℝ) / 2)`. Unfold `eulerFac`. Rewrite using `[if_neg (by rw [hPc]; exact fun h => hPQ h.symm), hPN]`.

Establish `hQ' : eulerFac E M Q = y ^ (-(1 : ℝ) / 2)`. Unfold `eulerFac`. Rewrite using `[if_neg (by rw [hQc]; exact hPQ), hQN]`. Establish `hval : eulerFac E M P * eulerFac E M Q = eulerF F E M v`. Rewrite using `[hP', hQ', ← Real.rpow_add hypos]`.

Unfold `eulerF`. Rewrite using `[heta, one_pow, one_mul, ← hy]`. Evaluate the numerical expressions. Conclude with `Real.rpow_neg_one y`. Use `hasProd_prod_of_ne_finset_one (f := fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} => eulerFac E M c.1) (s := {p0, q0}) (L := SummationFilter.unconditional _) (fun b hb => by` as an intermediate fact.

It suffices to derive a contradiction. Apply `hb` to reduce the goal to its premises. Break down `hu b.1 b.2.1 b.2.2 with h | h` into its components or cases. Conclude with `Finset.mem_insert.mpr (Or.inl (Subtype.ext h))`. Conclude with `Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h))))`.

Rewrite `this` using `[Finset.prod_pair hne]`. Simplify `this` using `[p0, q0, hval]`.
-/
theorem euler_factor_local : StepLocal := by
  intro F E _ _ _ _ _ _ M hM v hv hS
  classical
  have hN2 : (2 : ℝ) ≤ (Ideal.absNorm v : ℝ) := by exact_mod_cast two_le_absNorm v hv
  have hNpos : (0 : ℝ) < (Ideal.absNorm v : ℝ) := by linarith
  have hx1 : ((Ideal.absNorm v : ℕ) : ℝ) ^ (-(M : ℤ)) < 1 := by
    rw [zpow_neg, zpow_natCast]
    apply inv_lt_one_of_one_lt₀
    exact one_lt_pow₀ (by linarith) (by omega)
  rcases hS with ⟨P, hPm, hPv, hPc, hPN, hPu⟩ | ⟨P, Q, hPm, hQm, hPv, hQv, hPQ, hPc, hQc, hPN, hQN, hu⟩
  ·
    have heta : etaF F E v = -1 := by
      unfold etaF
      rw [if_pos ⟨P, ⟨hPm, hPv⟩, fun R hR => hPu R hR.1 hR.2⟩]
    let p0 : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} :=
      ⟨P, hPm, hPv⟩
    have hval : eulerFac E M P = eulerF F E M v := by
      unfold eulerFac eulerF
      rw [if_pos hPc, heta, hPN]
      push_cast
      rw [Real.sqrt_sq hNpos.le]
    have := hasProd_single (f := fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧
        P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} => eulerFac E M c.1) p0 (fun b hb => by
      exfalso
      apply hb
      exact Subtype.ext (hPu b.1 b.2.1 b.2.2))
    simpa [p0, hval] using this
  ·
    have heta : etaF F E v = 1 := by
      unfold etaF
      rw [if_neg]
      rintro ⟨R, ⟨hRm, hRv⟩, hR⟩
      exact hPQ ((hR P ⟨hPm, hPv⟩).trans (hR Q ⟨hQm, hQv⟩).symm)
    let p0 : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} :=
      ⟨P, hPm, hPv⟩
    let q0 : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} :=
      ⟨Q, hQm, hQv⟩
    have hne : p0 ≠ q0 := fun h => hPQ (congrArg Subtype.val h)
    set y : ℝ := 1 - ((Ideal.absNorm v : ℕ) : ℝ) ^ (-(M : ℤ)) with hy
    have hypos : 0 < y := by rw [hy]; linarith
    have hP' : eulerFac E M P = y ^ (-(1 : ℝ) / 2) := by
      unfold eulerFac
      rw [if_neg (by rw [hPc]; exact fun h => hPQ h.symm), hPN]
    have hQ' : eulerFac E M Q = y ^ (-(1 : ℝ) / 2) := by
      unfold eulerFac
      rw [if_neg (by rw [hQc]; exact hPQ), hQN]
    have hval : eulerFac E M P * eulerFac E M Q = eulerF F E M v := by
      rw [hP', hQ', ← Real.rpow_add hypos]
      unfold eulerF
      rw [heta, one_pow, one_mul, ← hy]
      norm_num
      exact Real.rpow_neg_one y
    have := hasProd_prod_of_ne_finset_one (f := fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧
        P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} => eulerFac E M c.1) (s := {p0, q0})
      (L := SummationFilter.unconditional _) (fun b hb => by
      exfalso
      apply hb
      rcases hu b.1 b.2.1 b.2.2 with h | h
      · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext h))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h))))
    rw [Finset.prod_pair hne] at this
    simpa [p0, q0, hval] using this

end CMEul
