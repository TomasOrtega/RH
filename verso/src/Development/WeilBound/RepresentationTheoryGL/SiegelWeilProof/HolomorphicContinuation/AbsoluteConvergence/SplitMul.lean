import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HzBound0

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem split_mul (x₀ : G) (y k : GR n) : x₀ * ι y * ι k = x₀ * ι (y * k) := by
  rw [mul_assoc, ← map_mul]

/- English proof (translation)
Extract witnesses or component facts from the available result. Substitute using the available equality. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem cont_hz (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    (z : ℂ) (b : GR n) (x : G) : Continuous fun k : KR n => hz Ht sec s₀ z 1 (x * ι ((k : GR n) * b)) := by
  obtain ⟨x₀, y, S, r, hr, hx, h⟩ := hG.split x
  subst hx
  have hfun : (fun k : KR n => hz Ht sec s₀ z 1 (x₀ * ι y * ι ((k : GR n) * b))) =
      fun k : KR n => ((r * hLoc (y * ((k : GR n) * b)) : ℝ) : ℂ) ^ (z - s₀) *
        (S * sL 1 (y * ((k : GR n) * b))) := by
    funext k
    unfold hz
    rw [split_mul, (h _).1, (h _).2]
  rw [hfun]
  have hcy : Continuous fun k : KR n => y * ((k : GR n) * b) :=
    continuous_const.mul (continuous_subtype_val.mul continuous_const)
  refine Continuous.mul ?_ (continuous_const.mul ((hL.cont 1).comp hcy))
  refine Continuous.cpow ?_ continuous_const
    (fun k => Complex.ofReal_mem_slitPlane.2 (mul_pos hr (hLoc_pos hD _)))
  exact Complex.continuous_ofReal.comp (continuous_const.mul ((continuous_hLoc hD).comp hcy))

/- English proof (translation)
Extract witnesses or component facts from the available result. Substitute using the available equality. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pointId [MeasurableSpace (KR n)] (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {ν : Measure (KR n)} {κ : KR n → ℂ} {N : ℕ}
    {yy : Fin N → GR n} {QQ : Fin N → PX m n} {M : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hMid : ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
        F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y')
    (z : ℂ) (i : Fin N) (x : G) :
    ∫ k, κ k * hz Ht sec s₀ z 1 (x * ι ((k : GR n) * yy i)) ∂ν = ∑ j, M (z - s₀) i j * hz Ht sec s₀ z (QQ j) x := by
  obtain ⟨x₀, y, S, r, hr, hx, h⟩ := hG.split x
  subst hx
  have key : ∀ (P : PX m n) (g : GR n), hz Ht sec s₀ z P (x₀ * ι g) =
      (r : ℂ) ^ (z - s₀) * S * ((hLoc g : ℂ) ^ (z - s₀) * sL P g) := by
    intro P g
    unfold hz
    rw [(h g).1, (h g).2, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_pos hD g).le]
    ring
  have hx' : ∀ k : KR n, x₀ * ι y * ι ((k : GR n) * yy i) = x₀ * ι (y * (k : GR n) * yy i) := by
    intro k
    rw [split_mul, mul_assoc]
  simp_rw [hx', key, hL.vac]
  simp only [mul_left_comm (κ _) ((r : ℂ) ^ (z - s₀) * S)]
  rw [integral_const_mul, hMid (z - s₀) i y, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

end PositivityTheory.Rg.Sw.AbsSt.Far
