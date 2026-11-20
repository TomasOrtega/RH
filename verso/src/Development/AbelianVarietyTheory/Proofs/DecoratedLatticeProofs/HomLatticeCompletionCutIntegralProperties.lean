import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

/- English proof (translation)
Use `show (((0 : Ainf F), a) * ((0 : Ainf F), b) : Ainf F × Af F) = ((0 : Ainf F), a * b)`. Rewrite using `[Prod.mk_mul_mk, mul_zero]`.
-/
theorem pairA_zero_mul_pairA_zero (F : Type) [Field F] [NumberField F] (a b : Af F) :
    pairA F 0 a * pairA F 0 b = pairA F 0 (a * b) := by
  show (((0 : Ainf F), a) * ((0 : Ainf F), b) : Ainf F × Af F) = ((0 : Ainf F), a * b)
  rw [Prod.mk_mul_mk, mul_zero]

/- English proof (translation)
Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, pairA_zero_mul_pairA_zero]`.
-/
theorem pairA_zero_smul_tmul (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a b : Af F) (e : E) :
    pairA F 0 a • (pairA F 0 b ⊗ₜ[F] e : AF F ⊗[F] E) = pairA F 0 (a * b) ⊗ₜ[F] e := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, pairA_zero_mul_pairA_zero]

/- English proof (translation)
Use `show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 b ⊗ₜ[D.host.F] e) = 0`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Establish `: fstA D.host.F (pairA D.host.F 0 b) = 0` using `rfl`. Rewrite using `[this, TensorProduct.zero_tmul]`.
-/
theorem infPart_pairA_zero_tmul (D : D7) (b : Af D.host.F) (e : D.host.E) :
    infPart D (pairA D.host.F 0 b ⊗ₜ[D.host.F] e) = 0 := by
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    (pairA D.host.F 0 b ⊗ₜ[D.host.F] e) = 0
  rw [Algebra.TensorProduct.map_tmul]
  have : fstA D.host.F (pairA D.host.F 0 b) = 0 := rfl
  rw [this, TensorProduct.zero_tmul]

/- English proof (translation)
Introduce `D S T LS LT P u hu`. Unfold `latO at hu`. Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩` from `hw`.

Use `⟨fun γ hγ => ?_, ?_, ?_, fun h => ?_⟩` and prove the remaining obligations. Use `AddSubgroup.subset_closure ⟨γ * α, fun v => ?_, fun v hv => ?_, a, ha, s, hs, t, ht, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_mem (hγ v) (hα v)`. Rewrite using `[map_mul]`.

Distinguish the cases in `h : P v`. Establish `: evalV D.host.F v γ = 0`. Assume the negation of the conclusion as `h'`. Conclude with `hv ⟨h, h'⟩`. Rewrite using `[this, zero_mul]`.

Rewrite using `[hP v h, mul_zero]`. Use extensionality with `i j`. Conclude with `pairA_zero_smul_tmul _ _ _ _ _`. Use extensionality with `i j`. Use `pairA_zero_smul_tmul D.host.F D.host.E 1 α (a * t i * ∑ k, star (s k) * S.gram k j)` as an intermediate fact.

Rewrite `this` using `[one_mul]`. Conclude with `this`. Use extensionality with `i j`. Conclude with `infPart_pairA_zero_tmul D α _`. Establish `h0 : α = 0`.

Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `v`. Conclude with `hP v (h v)`. Substitute `h0` using the available equality. Use extensionality with `i j`.

Establish `: pairA D.host.F 0 0 = 0` using `rfl`. Use `show pairA D.host.F 0 0 ⊗ₜ[D.host.F] _ = (0 : AE D)`. Rewrite using `[this, TensorProduct.zero_tmul]`. Consider the case `zero`. Use `⟨fun γ _ => ?_, smul_zero _, ?_, fun _ => rfl⟩` and prove the remaining obligations.

Rewrite using `[smul_zero]`. Conclude with `zero_mem _`. Use extensionality with `i j`. Conclude with `map_zero (infPart D)`. Consider the case `add x y _ _ hx hy`.

Use `⟨fun γ hγ => ?_, ?_, ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Conclude with `add_mem (hx.1 γ hγ) (hy.1 γ hγ)`. Rewrite using `[smul_add, hx.2.1, hy.2.1]`. Use extensionality with `i j`.

Establish `h1 : infPart D (x i j) = 0` using `congrFun (congrFun hx.2.2.1 i) j`. Establish `h2 : infPart D (y i j) = 0` using `congrFun (congrFun hy.2.2.1 i) j`. Use `show infPart D (x i j + y i j) = 0`. Rewrite using `[(infPart D).map_add, h1, h2, add_zero]`. Rewrite using `[hx.2.2.2 h, hy.2.2.2 h, add_zero]`.

Consider the case `neg x _ hx`. Use `⟨fun γ hγ => ?_, ?_, ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[smul_neg]`. Conclude with `neg_mem (hx.1 γ hγ)`. Rewrite using `[smul_neg, hx.2.1]`.

Use extensionality with `i j`. Establish `h1 : infPart D (x i j) = 0` using `congrFun (congrFun hx.2.2.1 i) j`. Use `show infPart D (- x i j) = 0`. Rewrite using `[map_neg, h1, neg_zero]`. Rewrite using `[hx.2.2.2 h, neg_zero]`.
-/
theorem latO_algebra : ∀ (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop) (u : WO S T), u ∈ latO S T LS LT P → (∀ γ ∈ intAf D.host.F, pairA D.host.F 0 γ • u ∈ latO S T LS LT (fun v => P v ∧ evalV D.host.F v γ ≠ 0)) ∧ pairA D.host.F 0 1 • u = u ∧ u.map (infPart D) = 0 ∧ ((∀ v, ¬ P v) → u = 0) := by
  intro D S T LS LT P u hu
  unfold latO at hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine ⟨fun γ hγ => ?_, ?_, ?_, fun h => ?_⟩
    · refine AddSubgroup.subset_closure ⟨γ * α, fun v => ?_, fun v hv => ?_, a, ha, s, hs, t, ht, ?_⟩
      · rw [map_mul]
        exact mul_mem (hγ v) (hα v)
      · rw [map_mul]
        by_cases h : P v
        · have : evalV D.host.F v γ = 0 := by
            by_contra h'
            exact hv ⟨h, h'⟩
          rw [this, zero_mul]
        · rw [hP v h, mul_zero]
      · ext i j
        exact pairA_zero_smul_tmul _ _ _ _ _
    · ext i j
      have := pairA_zero_smul_tmul D.host.F D.host.E 1 α (a * t i * ∑ k, star (s k) * S.gram k j)
      rw [one_mul] at this
      exact this
    · ext i j
      exact infPart_pairA_zero_tmul D α _
    · have h0 : α = 0 := by
        apply RestrictedProduct.ext
        intro v
        exact hP v (h v)
      subst h0
      ext i j
      have : pairA D.host.F 0 0 = 0 := rfl
      show pairA D.host.F 0 0 ⊗ₜ[D.host.F] _ = (0 : AE D)
      rw [this, TensorProduct.zero_tmul]
  | zero =>
    refine ⟨fun γ _ => ?_, smul_zero _, ?_, fun _ => rfl⟩
    · rw [smul_zero]
      exact zero_mem _
    · ext i j
      exact map_zero (infPart D)
  | add x y _ _ hx hy =>
    refine ⟨fun γ hγ => ?_, ?_, ?_, fun h => ?_⟩
    · rw [smul_add]
      exact add_mem (hx.1 γ hγ) (hy.1 γ hγ)
    · rw [smul_add, hx.2.1, hy.2.1]
    · ext i j
      have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx.2.2.1 i) j
      have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy.2.2.1 i) j
      show infPart D (x i j + y i j) = 0
      rw [(infPart D).map_add, h1, h2, add_zero]
    · rw [hx.2.2.2 h, hy.2.2.2 h, add_zero]
  | neg x _ hx =>
    refine ⟨fun γ hγ => ?_, ?_, ?_, fun h => ?_⟩
    · rw [smul_neg]
      exact neg_mem (hx.1 γ hγ)
    · rw [smul_neg, hx.2.1]
    · ext i j
      have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx.2.2.1 i) j
      show infPart D (- x i j) = 0
      rw [map_neg, h1, neg_zero]
    · rw [hx.2.2.2 h, neg_zero]

end GlobalTheory.FinPl
