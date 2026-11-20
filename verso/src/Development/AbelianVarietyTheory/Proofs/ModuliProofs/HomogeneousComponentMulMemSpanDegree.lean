import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

open MvPolynomial in

/- English proof (translation)
Proceed by induction on `hF using Submodule.span_induction generalizing a with`. Consider the case `mem G hG`. Take `⟨hGI, hG⟩` from `hG`. Proceed by induction on `a using MvPolynomial.induction_on' with`. Consider the case `monomial m c`.

Establish `hm : (monomial m c * G).IsHomogeneous (m.degree + d₀)` using `(isHomogeneous_monomial c rfl).mul hG`. Rewrite using `[homogeneousComponent_of_mem hm]`. Use `split_ifs with h`. Take `⟨m₂, hle, hdeg⟩` from `Finsupp.exists_le_degree_eq m (d - d₀) (by omega)`. Take `⟨m₁, rfl⟩` from `exists_add_of_le hle`.

Establish `: (monomial (m₂ + m₁) c : MvPolynomial σ K) * G = monomial m₁ c * (monomial m₂ 1 * G)`. Rewrite using `[← _root_.mul_assoc, monomial_mul, _root_.mul_one, add_comm]`. Rewrite using `[this]`. Use `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨I.mul_mem_left _ hGI, ?_⟩)` and prove the remaining obligations. Establish `h2` using `(isHomogeneous_monomial (1 : K) hdeg).mul hG`.

Rewrite `h2` using `[Nat.sub_add_cancel h₀]`. Then use the resulting hypothesis. Conclude with `Ideal.zero_mem _`. Consider the case `add a b ha hb => rw [add_mul, map_add]`. Conclude with `Ideal.add_mem _ ha hb`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [mul_add, map_add]`. Conclude with `Ideal.add_mem _ (hx a) (hy a)`. Consider the case `smul r x _ hx => rw [smul_eq_mul, ← _root_.mul_assoc]`. Conclude with `hx _`.
-/
theorem homogeneousComponent_mul_mem_span_degree {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) {d₀ d e : ℕ}
    (h₀ : d₀ ≤ d) (he : d ≤ e) {F : MvPolynomial σ K} (hF : F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d₀})
    (a : MvPolynomial σ K) :
    homogeneousComponent e (a * F) ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
  induction hF using Submodule.span_induction generalizing a with
  | mem G hG =>
    obtain ⟨hGI, hG⟩ := hG
    induction a using MvPolynomial.induction_on' with
    | monomial m c =>
      have hm : (monomial m c * G).IsHomogeneous (m.degree + d₀) :=
        (isHomogeneous_monomial c rfl).mul hG
      rw [homogeneousComponent_of_mem hm]
      split_ifs with h
      · obtain ⟨m₂, hle, hdeg⟩ := Finsupp.exists_le_degree_eq m (d - d₀) (by omega)
        obtain ⟨m₁, rfl⟩ := exists_add_of_le hle
        have : (monomial (m₂ + m₁) c : MvPolynomial σ K) * G = monomial m₁ c * (monomial m₂ 1 * G) := by
          rw [← _root_.mul_assoc, monomial_mul, _root_.mul_one, add_comm]
        rw [this]
        refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨I.mul_mem_left _ hGI, ?_⟩)
        have h2 := (isHomogeneous_monomial (1 : K) hdeg).mul hG
        rwa [Nat.sub_add_cancel h₀] at h2
      · exact Ideal.zero_mem _
    | add a b ha hb => rw [add_mul, map_add]; exact Ideal.add_mem _ ha hb
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add]; exact Ideal.add_mem _ (hx a) (hy a)
  | smul r x _ hx => rw [smul_eq_mul, ← _root_.mul_assoc]; exact hx _

/- English proof (translation)
Introduce `K σ Hh _ I Q d₀ d p h₀ hreg hvan hzero e he`. Establish `hV : vanIdeal d p = Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d}`. Unfold `vanIdeal`. Use `congr 1`. Use extensionality with `F`.

Conclude with `⟨fun h => ⟨hzero F h.1 h.2, h.1⟩, fun h => ⟨h.2, hvan F h.1⟩⟩`. Use `⟨(hreg e (h₀.trans he)).1, fun F hF => ⟨fun hI => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `h` using `homogeneousComponent_mul_mem_span_degree I h₀ he ((hreg e (h₀.trans he)).2 F hI hF) 1`. Rewrite `h` using `[_root_.one_mul, MvPolynomial.homogeneousComponent_of_mem hF, if_pos rfl]`. Rewrite using `[hV]` and apply the resulting hypothesis.

Rewrite `h` using `[hV]`. Conclude with `(Ideal.span_le.2 fun G hG => hG.1) h`.
-/
theorem cutBy_of_regular_of_zeroEstimate : ∀ (K σ Hh : Type) [Field K] (I : Ideal (MvPolynomial σ K)) (Q : Polynomial ℚ) (d₀ d : ℕ) (p : Hh → σ → K), d₀ ≤ d → (∀ e ≥ d₀, (dimDeg I e : ℚ) = Q.eval (e : ℚ) ∧ ∀ F ∈ I, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d₀}) → (∀ F ∈ I, ∀ h, MvPolynomial.eval (p h) F = 0) → (∀ F : MvPolynomial σ K, F.IsHomogeneous d → (∀ h, MvPolynomial.eval (p h) F = 0) → F ∈ I) → CutBy I Q d p := by
  intro K σ Hh _ I Q d₀ d p h₀ hreg hvan hzero e he
  have hV : vanIdeal d p = Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
    unfold vanIdeal
    congr 1
    ext F
    exact ⟨fun h => ⟨hzero F h.1 h.2, h.1⟩, fun h => ⟨h.2, hvan F h.1⟩⟩
  refine ⟨(hreg e (h₀.trans he)).1, fun F hF => ⟨fun hI => ?_, fun h => ?_⟩⟩
  · have h := homogeneousComponent_mul_mem_span_degree I h₀ he ((hreg e (h₀.trans he)).2 F hI hF) 1
    rw [_root_.one_mul, MvPolynomial.homogeneousComponent_of_mem hF, if_pos rfl] at h
    rwa [hV]
  · rw [hV] at h
    exact (Ideal.span_le.2 fun G hG => hG.1) h

end GlobalTheory
