import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Factor

open CompanionTheory.D.gk.admitted.FinOfPIAux

variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Diag

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `haveI : CompleteSpace C := hcl.completeSpace_coe`. Establish `hPg` using `proj_comm (ι := ι) σ hσ C hC`. Set `Q : ι → ι → H →L[ℂ] H` to `fun k l => (PiLp.proj 2 (fun _ : ι => H) k).comp (C.starProjection.comp (incl l))`. Establish `hQ : ∀ k l, Q k l * T = T * Q k l`. Introduce `k l`.

Apply `hT` to reduce the goal to its premises. Introduce `g`. Use extensionality with `v`. Simplify using `only [Q, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply]`. Rewrite using `[← diag_incl, hPg, diag_apply]`.

Establish `hsum : ∀ w : PiLp 2 (fun _ : ι => H), ∀ k, (C.starProjection w).ofLp k = ∑ l, Q k l (w.ofLp l)`. Introduce `w k`. Use `conv_lhs => rw [← sum_incl w]`. Simplify using `[Q, map_sum]`. Establish `key : C.starProjection (diag T z) = diag T (C.starProjection z)`.

Use extensionality with `k`. Rewrite using `[hsum, diag_apply, hsum, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[diag_apply]`. Conclude with `congrArg (fun S : H →L[ℂ] H => S (z.ofLp l)) (hQ k l)`.

Establish `hz' : C.starProjection z = z` using `(Submodule.starProjection_eq_self_iff).2 hz`. Rewrite using `[← hz', ← key]`. Conclude with `C.starProjection_apply_mem _`.
-/
theorem diag_mem_of_bicomm (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (C : Submodule ℂ (PiLp 2 (fun _ : ι => H))) (hcl : IsClosed (C : Set (PiLp 2 (fun _ : ι => H))))
    (hC : ∀ g, ∀ z ∈ C, diag (σ g) z ∈ C) (T : H →L[ℂ] H)
    (hT : ∀ S : H →L[ℂ] H, (∀ g, S * σ g = σ g * S) → S * T = T * S)
    (z : PiLp 2 (fun _ : ι => H)) (hz : z ∈ C) :
    diag T z ∈ C := by
  haveI : CompleteSpace C := hcl.completeSpace_coe
  have hPg := proj_comm (ι := ι) σ hσ C hC
  let Q : ι → ι → H →L[ℂ] H := fun k l =>
    (PiLp.proj 2 (fun _ : ι => H) k).comp (C.starProjection.comp (incl l))
  have hQ : ∀ k l, Q k l * T = T * Q k l := by
    intro k l
    apply hT
    intro g
    ext v
    simp only [Q, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    rw [← diag_incl, hPg, diag_apply]
  have hsum : ∀ w : PiLp 2 (fun _ : ι => H), ∀ k,
      (C.starProjection w).ofLp k = ∑ l, Q k l (w.ofLp l) := by
    intro w k
    conv_lhs => rw [← sum_incl w]
    simp [Q, map_sum]
  have key : C.starProjection (diag T z) = diag T (C.starProjection z) := by
    ext k
    rw [hsum, diag_apply, hsum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [diag_apply]
    exact congrArg (fun S : H →L[ℂ] H => S (z.ofLp l)) (hQ k l)
  have hz' : C.starProjection z = z := (Submodule.starProjection_eq_self_iff).2 hz
  rw [← hz', ← key]
  exact C.starProjection_apply_mem _

/- English proof (translation)
Set `y' : PiLp 2 (fun _ : ι => H)` to `WithLp.toLp 2 y`. Set `V : Submodule ℂ (PiLp 2 (fun _ : ι => H))` to `Submodule.span ℂ (Set.range fun g : G => diag (σ g) y')`. Establish `hdiag_mul : ∀ a b : G, ∀ w : PiLp 2 (fun _ : ι => H), diag (σ a) (diag (σ b) w) = diag (σ (a * b)) w`. Introduce `a b w`. Use extensionality with `k`.

Simplify using `only [diag_apply, map_mul, ContinuousLinearMap.mul_apply]`. Establish `hCinv : ∀ g, ∀ z ∈ V.topologicalClosure, diag (σ g) z ∈ V.topologicalClosure`. Introduce `g`. Establish `hle : V ≤ V.topologicalClosure.comap ((diag (σ g) : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H))) : (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] (PiLp 2 (fun _ : ι => H)))`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨b, rfl⟩`. Use `show diag (σ g) (diag (σ b) y') ∈ V.topologicalClosure`. Rewrite using `[hdiag_mul]`. Conclude with `V.le_topologicalClosure (Submodule.subset_span ⟨g * b, rfl⟩)`. Establish `hcl' : IsClosed ((V.topologicalClosure.comap ((diag (σ g) : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H))) : (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] (PiLp 2 (fun _ : ι => H))) : Submodule ℂ (PiLp 2 (fun _ : ι => H))) : Set (PiLp 2 (fun _ : ι => H)))` using `V.isClosed_topologicalClosure.preimage (diag (σ g)).continuous`.

Introduce `z hz`. Conclude with `Submodule.topologicalClosure_minimal V hle hcl' hz`. Establish `hy' : y' ∈ V.topologicalClosure`. Apply `V.le_topologicalClosure` to reduce the goal to its premises. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨1, ?_⟩` and prove the remaining obligations. Use extensionality with `k`. Simplify using `[diag_apply]`. Establish `hT'` using `diag_mem_of_bicomm σ hσ V.topologicalClosure V.isClosed_topologicalClosure hCinv T hT y' hy'`. Set `Λ : (PiLp 2 (fun _ : ι => H)) →L[ℂ] H` to `∑ k, (L k).comp (PiLp.proj 2 (fun _ : ι => H) k)`.

Establish `hΛ : ∀ w : PiLp 2 (fun _ : ι => H), Λ w = ∑ k, L k (w.ofLp k)`. Introduce `w`. Simplify using `[Λ]`. Establish `hker : V.topologicalClosure ≤ LinearMap.ker (Λ : (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] H)`. Apply `Submodule.topologicalClosure_minimal` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΛ, diag_apply]`. Simplify `h g` using `[y']`. Conclude with `Λ.isClosed_ker`.

Establish `hfin` using `hker hT'`. Simplify using `only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΛ, diag_apply] at hfin`. Simplify `hfin` using `[y']`.
-/
theorem sum_eq_zero_of_bicomm (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (L : ι → H →L[ℂ] H) (y : ι → H) (h : ∀ g, ∑ k, L k (σ g (y k)) = 0) (T : H →L[ℂ] H)
    (hT : ∀ S : H →L[ℂ] H, (∀ g, S * σ g = σ g * S) → S * T = T * S) :
    ∑ k, L k (T (y k)) = 0 := by
  let y' : PiLp 2 (fun _ : ι => H) := WithLp.toLp 2 y
  let V : Submodule ℂ (PiLp 2 (fun _ : ι => H)) :=
    Submodule.span ℂ (Set.range fun g : G => diag (σ g) y')
  have hdiag_mul : ∀ a b : G, ∀ w : PiLp 2 (fun _ : ι => H),
      diag (σ a) (diag (σ b) w) = diag (σ (a * b)) w := by
    intro a b w
    ext k
    simp only [diag_apply, map_mul, ContinuousLinearMap.mul_apply]
  have hCinv : ∀ g, ∀ z ∈ V.topologicalClosure, diag (σ g) z ∈ V.topologicalClosure := by
    intro g
    have hle : V ≤ V.topologicalClosure.comap
        ((diag (σ g) : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H))) :
          (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] (PiLp 2 (fun _ : ι => H))) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      show diag (σ g) (diag (σ b) y') ∈ V.topologicalClosure
      rw [hdiag_mul]
      exact V.le_topologicalClosure (Submodule.subset_span ⟨g * b, rfl⟩)
    have hcl' : IsClosed ((V.topologicalClosure.comap
        ((diag (σ g) : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H))) :
          (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] (PiLp 2 (fun _ : ι => H))) :
          Submodule ℂ (PiLp 2 (fun _ : ι => H))) : Set (PiLp 2 (fun _ : ι => H))) :=
      V.isClosed_topologicalClosure.preimage (diag (σ g)).continuous
    intro z hz
    exact Submodule.topologicalClosure_minimal V hle hcl' hz
  have hy' : y' ∈ V.topologicalClosure := by
    apply V.le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨1, ?_⟩
    ext k
    simp [diag_apply]
  have hT' := diag_mem_of_bicomm σ hσ V.topologicalClosure V.isClosed_topologicalClosure
    hCinv T hT y' hy'
  let Λ : (PiLp 2 (fun _ : ι => H)) →L[ℂ] H := ∑ k, (L k).comp (PiLp.proj 2 (fun _ : ι => H) k)
  have hΛ : ∀ w : PiLp 2 (fun _ : ι => H), Λ w = ∑ k, L k (w.ofLp k) := by
    intro w
    simp [Λ]
  have hker : V.topologicalClosure ≤ LinearMap.ker (Λ : (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] H) := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΛ, diag_apply]
      simpa [y'] using h g
    · exact Λ.isClosed_ker
  have hfin := hker hT'
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΛ, diag_apply] at hfin
  simpa [y'] using hfin

end Diag

/- English proof (translation)
Establish `step : ∀ j : ℕ, ∀ g : Fin M → G, stdPoly E (fun i : Fin M => if (i : ℕ) < j then a i else σ (g i)) = 0`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro g`. Simplify using `using h g`.

Consider the case `succ j ih`. Introduce `g`. Distinguish the cases in `hj : j < M`. Set `k : Fin M` to `⟨j, hj⟩`. Set `b : Fin M → H →L[ℂ] H` to `fun i => if (i : ℕ) < j then a i else σ (g i)`.

Establish `hb : (fun i : Fin M => if (i : ℕ) < j + 1 then a i else σ (g i)) = Function.update b k (a k)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality. Simplify using `[b, k]`.

Rewrite using `[Function.update_of_ne hik]`. Establish `hne : (i : ℕ) ≠ j` using `fun e => hik (Fin.ext e)`. Distinguish the cases in `hlt : (i : ℕ) < j`. Establish `h2 : (i : ℕ) < j + 1` using `by omega`. Simplify using `[b, hlt, h2]`.

Establish `h2 : ¬ (i : ℕ) < j + 1` using `by omega`. Simplify using `[b, hlt, h2]`. Take `⟨A, B, hAB⟩` from `CompanionTheory.D.gk.admitted.FinOfPIAux.stdPoly_update E b k`. Establish `hσk : ∀ x : G, stdPoly E (Function.update b k (σ x)) = 0`. Introduce `x`.

Establish `hx` using `ih (Function.update g k x)`. Use `hx using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality.

Simplify using `[b, k]`. Rewrite using `[Function.update_of_ne hik]`. Simplify using `[b, Function.update_of_ne hik]`. Rewrite using `[hb, hAB]`. Use extensionality with `v`.

Simplify using `only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply]`. Use `sum_eq_zero_of_bicomm σ hσ A (fun π => B π v) ?_ (a k) (ha k)` and prove the remaining obligations. Introduce `x`. Establish `hv` using `congrArg (fun S : H →L[ℂ] H => S v) ((hAB (σ x)).symm.trans (hσk x))`. Simplify `hv` using `[ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply]`.

Establish `hiff : ∀ i : Fin M, ((i : ℕ) < j + 1 ↔ (i : ℕ) < j)` using `fun i => by`. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify `ih g` using `[hiff]`. Simplify using `using step M (fun _ => 1)`.
-/
theorem standard_polynomial_vanishes_on_bicommutant (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (E : H →L[ℂ] H) (M : ℕ) (h : ∀ g : Fin M → G, stdPoly E (fun i => σ (g i)) = 0)
    (a : Fin M → H →L[ℂ] H)
    (ha : ∀ i, ∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → T * a i = a i * T) :
    stdPoly E a = 0 := by
  classical
  have step : ∀ j : ℕ, ∀ g : Fin M → G,
      stdPoly E (fun i : Fin M => if (i : ℕ) < j then a i else σ (g i)) = 0 := by
    intro j
    induction j with
    | zero => intro g; simpa using h g
    | succ j ih =>
      intro g
      by_cases hj : j < M
      · let k : Fin M := ⟨j, hj⟩
        let b : Fin M → H →L[ℂ] H := fun i => if (i : ℕ) < j then a i else σ (g i)
        have hb : (fun i : Fin M => if (i : ℕ) < j + 1 then a i else σ (g i)) =
            Function.update b k (a k) := by
          funext i
          by_cases hik : i = k
          · subst hik
            simp [b, k]
          · rw [Function.update_of_ne hik]
            have hne : (i : ℕ) ≠ j := fun e => hik (Fin.ext e)
            by_cases hlt : (i : ℕ) < j
            · have h2 : (i : ℕ) < j + 1 := by omega
              simp [b, hlt, h2]
            · have h2 : ¬ (i : ℕ) < j + 1 := by omega
              simp [b, hlt, h2]
        obtain ⟨A, B, hAB⟩ := CompanionTheory.D.gk.admitted.FinOfPIAux.stdPoly_update E b k
        have hσk : ∀ x : G, stdPoly E (Function.update b k (σ x)) = 0 := by
          intro x
          have hx := ih (Function.update g k x)
          convert hx using 2
          funext i
          by_cases hik : i = k
          · subst hik
            simp [b, k]
          · rw [Function.update_of_ne hik]
            simp [b, Function.update_of_ne hik]
        rw [hb, hAB]
        ext v
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply,
          ContinuousLinearMap.zero_apply]
        refine sum_eq_zero_of_bicomm σ hσ A (fun π => B π v) ?_ (a k) (ha k)
        intro x
        have hv := congrArg (fun S : H →L[ℂ] H => S v) ((hAB (σ x)).symm.trans (hσk x))
        simpa [ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply] using hv
      · have hiff : ∀ i : Fin M, ((i : ℕ) < j + 1 ↔ (i : ℕ) < j) := fun i => by
          have := i.isLt
          omega
        simpa [hiff] using ih g
  simpa using step M (fun _ => 1)

/- English proof (translation)
Introduce `G H _ _ _ _ σ hσ E m h a ha`. Conclude with `standard_polynomial_vanishes_on_bicommutant σ hσ E m h a ha`.
-/
theorem stdPoly_bicomm : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (E : H →L[ℂ] H) (m : ℕ), (∀ g : Fin m → G, stdPoly E (fun i => σ (g i)) = 0) →
    ∀ a : Fin m → (H →L[ℂ] H), (∀ i, ∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → T * a i = a i * T) → stdPoly E a = 0 := by
  intro G H _ _ _ _ σ hσ E m h a ha
  exact standard_polynomial_vanishes_on_bicommutant σ hσ E m h a ha

end GlobalTheory.CompanionTheory.Factor
