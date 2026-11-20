import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

/- English proof (translation)
Use `letI := g.toAlgebra`. Establish `hfin : Module.Finite A B` using `hg`. Take `⟨S, hS⟩` from `hfin.fg_top`. Use `⟨S.card, fun K _ ψ φ hφ hinj => ?_⟩` and prove the remaining obligations. Set `L : (Fin (S.card + 1) → K) →ₗ[K] (S → K)` to `{ toFun := fun c s => ∑ j, c j * φ j (s : B) map_add' := by intro c d; funext s; simp [add_mul, Finset.sum_add_distrib] map_smul' := by intro a c; funext s; simp [Finset.mul_sum, mul_assoc] }`.

Establish `hker : LinearMap.ker L ≠ ⊥` using `LinearMap.ker_ne_bot_of_finrank_lt (by simp)`. Take `⟨c, hc, hc0⟩` from `(Submodule.ne_bot_iff _).1 hker`. Establish `hcS : ∀ s ∈ S, ∑ j, c j * φ j s = 0`. Introduce `s hs`. Use `congrFun (LinearMap.mem_ker.1 hc) ⟨s, hs⟩` as an intermediate fact.

Simplify `this` using `[L]`. Establish `hall : ∀ b : B, ∑ j, c j * φ j b = 0`. Introduce `b`. Establish `hb : b ∈ Submodule.span A (S : Set B)` using `hS ▸ Submodule.mem_top`. Proceed by induction on `hb using Submodule.span_induction with`.

Consider the case `mem x hx => exact hcS x hx`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [mul_add, Finset.sum_add_distrib, hx, hy]`. Consider the case `smul a x _ hx`. Establish `e : ∀ j, φ j (a • x) = ψ a * φ j x`.

Introduce `j`. Rewrite using `[Algebra.smul_def, map_mul, ← hφ j]`. Both sides reduce to the same expression. Simplify using `only [e]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring`. Use `_ = 0 := by rw [hx, mul_zero]`. Establish `hli` using `(linearIndependent_monoidHom B K).comp (fun j => (φ j : B →* K)) (fun i j h => hinj (RingHom.ext fun b => DFunLike.congr_fun h b))`. Use `(Fintype.linearIndependent_iff.1 hli) c (by` as an intermediate fact. Use function extensionality and compare the values at `b`.

Simplify `hall b)` using `[Finset.sum_apply, smul_eq_mul]`. Conclude with `hc0 (funext this)`.
-/
theorem ringHom_count_bound {A B : Type} [CommRing A] [CommRing B] (g : A →+* B)
    (hg : g.Finite) : ∃ n : ℕ, ∀ (K : Type) [Field K] (ψ : A →+* K) (φ : Fin (n + 1) → (B →+* K)),
      (∀ j, (φ j).comp g = ψ) → ¬ Function.Injective φ := by
  letI := g.toAlgebra
  have hfin : Module.Finite A B := hg
  obtain ⟨S, hS⟩ := hfin.fg_top
  refine ⟨S.card, fun K _ ψ φ hφ hinj => ?_⟩
  let L : (Fin (S.card + 1) → K) →ₗ[K] (S → K) :=
    { toFun := fun c s => ∑ j, c j * φ j (s : B)
      map_add' := by intro c d; funext s; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro a c; funext s; simp [Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hcS : ∀ s ∈ S, ∑ j, c j * φ j s = 0 := by
    intro s hs
    have := congrFun (LinearMap.mem_ker.1 hc) ⟨s, hs⟩
    simpa [L] using this
  have hall : ∀ b : B, ∑ j, c j * φ j b = 0 := by
    intro b
    have hb : b ∈ Submodule.span A (S : Set B) := hS ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact hcS x hx
    | zero => simp
    | add x y _ _ hx hy => simp [mul_add, Finset.sum_add_distrib, hx, hy]
    | smul a x _ hx =>
      have e : ∀ j, φ j (a • x) = ψ a * φ j x := by
        intro j
        rw [Algebra.smul_def, map_mul, ← hφ j]
        rfl
      simp only [e]
      calc ∑ j, c j * (ψ a * φ j x) = ψ a * ∑ j, c j * φ j x := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hx, mul_zero]
  have hli := (linearIndependent_monoidHom B K).comp (fun j => (φ j : B →* K))
    (fun i j h => hinj (RingHom.ext fun b => DFunLike.congr_fun h b))
  have := (Fintype.linearIndependent_iff.1 hli) c (by
    funext b
    simpa [Finset.sum_apply, smul_eq_mul] using hall b)
  exact hc0 (funext this)

/- English proof (translation)
Introduce `Z X f _ _`. Use `haveI := isAffine_of_isAffineHom f`. Take `⟨n, hn⟩` from `ringHom_count_bound f.appTop.hom f.finite_appTop`. Use `⟨n, fun K _ y s hs hinj => ?_⟩` and prove the remaining obligations. Use `hn K (y.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom (fun j => ((s j).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom) (fun j => ?_) ?_` and prove the remaining obligations.

Rewrite using `[← hs j, Scheme.Hom.comp_appTop, Category.assoc]`. Simplify using `only [CommRingCat.hom_comp]`. Introduce `i j h`. Apply `hinj` to reduce the goal to its premises. Apply `ext_of_isAffine` to reduce the goal to its premises.

Conclude with `(cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1 (CommRingCat.hom_ext h)`.
-/
theorem finite_fibrePointsLE_of_isAffine : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [IsAffine X],
    ∃ n, GlobalTheory.EtC.Tr.FibrePointsLE f n := by
  intro Z X f _ _
  haveI := isAffine_of_isAffineHom f
  obtain ⟨n, hn⟩ := ringHom_count_bound f.appTop.hom f.finite_appTop
  refine ⟨n, fun K _ y s hs hinj => ?_⟩
  refine hn K (y.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
    (fun j => ((s j).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom) (fun j => ?_) ?_
  · rw [← hs j, Scheme.Hom.comp_appTop, Category.assoc]
    simp only [CommRingCat.hom_comp]
  · intro i j h
    apply hinj
    apply ext_of_isAffine
    exact (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1 (CommRingCat.hom_ext h)

end GlobalTheory.EtC.Tr
