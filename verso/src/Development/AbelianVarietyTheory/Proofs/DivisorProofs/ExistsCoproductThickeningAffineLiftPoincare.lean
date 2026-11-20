import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourTermComplexQuasiIsoAtFormalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionsMonoReductionAffineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSpecPointsLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoproductThickeningQuotientFreeThickeningStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.CopPoincare

/- English proof (translation)
Take `⟨N, hN⟩` from `(isDPNilpotent_iff_exists_isLevel δ).1 h`. Establish `key : ∀ (m : ℕ), ∀ x ∈ J ^ m, ∀ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ J) → N ≤ m + (l.map Prod.fst).sum → x * (l.map fun p ↦ δ.dpow p.1 p.2).prod = 0`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`.

Introduce `x _ l hl hs`. Rewrite using `[(isLev_iff_prod δ N).1 hN l hl (by simpa using hs), mul_zero]`. Consider the case `succ m ih`. Introduce `x hx l hl hs`. Rewrite `hx` using `[pow_succ]`.

Use `Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ by rw [add_mul, ha, hb, add_zero])` and prove the remaining obligations. Use `ih a ha ((1, b) :: l) (by` as an intermediate fact. Introduce `p hp`. Break down `List.mem_cons.1 hp with rfl | hp` into its components or cases. Conclude with `hb`.

Conclude with `hl p hp) (by simp only [List.map_cons, List.sum_cons]; omega)`. Simplify `this` using `[δ.dpow_one hb, mul_assoc]`. Use `⟨N, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.zero_eq_bot, eq_bot_iff]`. Introduce `x hx`.

Simplify using `using key N x hx [] (by simp) (by simp)`.
-/
theorem isNilpotent_of_isNilDP {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J} (h : IsNilDP δ) :
    IsNilpotent J := by
  obtain ⟨N, hN⟩ := (isDPNilpotent_iff_exists_isLevel δ).1 h
  have key : ∀ (m : ℕ), ∀ x ∈ J ^ m, ∀ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ J) → N ≤ m + (l.map Prod.fst).sum →
      x * (l.map fun p ↦ δ.dpow p.1 p.2).prod = 0 := by
    intro m
    induction m with
    | zero =>
      intro x _ l hl hs
      rw [(isLev_iff_prod δ N).1 hN l hl (by simpa using hs), mul_zero]
    | succ m ih =>
      intro x hx l hl hs
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ by rw [add_mul, ha, hb, add_zero])
      have := ih a ha ((1, b) :: l) (by
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hb
        · exact hl p hp) (by simp only [List.map_cons, List.sum_cons]; omega)
      simpa [δ.dpow_one hb, mul_assoc] using this
  refine ⟨N, ?_⟩
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  intro x hx
  simpa using key N x hx [] (by simp) (by simp)

/- English proof (translation)
Introduce `D Λ n U T hT hU`. Take `⟨F, G, u, q, r, hu, hF, hq, hJ, hc⟩` from `GlobalTheory.T.exists_coproductThickening_quotient_freeThickening D Λ n U T hT hU`. Take `⟨h1, -, -, -⟩` from `GlobalTheory.T.hom_spec_points_levels D Λ`. Use `⟨G, u ≫ q, r, hc, ?_⟩` and prove the remaining obligations. Use `haveI := D.sec_smooth U.unop`.

Establish `hker : RingHom.ker (q.φ : F.B →+* G.B) ≤ F.J` using `fun b hb ↦ hJ b (by`. Rewrite using `[show q.φ b = 0 from hb]`. Conclude with `G.J.zero_mem)`. Establish `hnil : IsNilpotent (RingHom.ker (q.φ : F.B →+* G.B))`. Take `⟨N, hN⟩` from `isNilpotent_of_isNilDP F.nil`.

Use `⟨N, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hN]`. Conclude with `Ideal.pow_right_mono hker N`. Set `y : Sec D.s U.unop.1 →ₐ[D.R] G.B` to `r.φ.comp (Λ.e U : Sec D.s U.unop.1 →ₐ[D.R] (Λ.L.obj U).B)`. Set `y' : Sec D.s U.unop.1 →ₐ[D.R] F.B` to `Algebra.FormallySmooth.liftOfSurjective y q.φ hq hnil`.

Establish `hy' : ∀ a, q.φ (y' a) = y a` using `fun a ↦ Algebra.FormallySmooth.liftOfSurjective_apply y q.φ hq hnil a`. Establish `hbij : Function.Bijective q.φ₀`. Use `⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ ?_, fun c ↦ ?_⟩` and prove the remaining obligations. Take `⟨b, rfl⟩` from `F.surj b`. Rewrite `hb` using `[q.comm, G.ker]`.

Conclude with `(F.ker b).2 (hJ b hb)`. Take `⟨c, rfl⟩` from `G.surj c`. Take `⟨b, rfl⟩` from `hq c`. Conclude with `⟨F.π b, q.comm b⟩`. Use `haveI : IsIso (spMap q.φ₀) := (inferInstance : IsIso (Spec.map (RingEquiv.ofBijective q.φ₀ hbij).toCommRingCatIso.hom))`.

Establish `hy` using `(h1 U G y).2 ⟨r, fun _ ↦ rfl⟩`. Establish `hpt : spMap (F.π.comp (y' : Sec D.s U.unop.1 →+* F.B)) ≫ affPt D.s U.unop = F.x ≫ D.i`. Rewrite using `[← cancel_epi (spMap q.φ₀), ← Category.assoc, ← Cris.spMap_comp, ← Category.assoc, q.pt, ← hy]`. Use `congr 2`. Use extensionality with `a`.

Conclude with `(q.comm _).trans (congrArg G.π (hy' a))`. Take `⟨b', hb'⟩` from `(h1 U F y').1 hpt`. Take `⟨s, ⟨hs1, hs2⟩, -⟩` from `hc.2 F hF u b'`. Establish `hbq : b' ≫ q = r` using `Thick.hom_ext fun b ↦ by`. Take `⟨a, rfl⟩` from `(Λ.e U).surjective b`.

Rewrite using `[Thick.comp_φ, hb', hy']`. Both sides reduce to the same expression. Establish `hsq : s ≫ q = 𝟙 G`. Take `⟨c, -, huniq⟩` from `hc.2 G hc.1 (u ≫ q) r`. Use `(huniq _ ⟨?_, ?_⟩).trans (huniq _ ⟨Category.comp_id _, Category.comp_id _⟩).symm` and prove the remaining obligations.

Rewrite using `[← Category.assoc, hs1]`. Rewrite using `[← Category.assoc, hs2, hbq]`. Conclude with `(GlobalTheory.CxCoh.QAtFormal.qAt_formal _ (KK D.κ D.t)).2.2 T G F (u ≫ q) s q hsq (by rw [hs1]; exact hu)`.
-/
theorem exists_cop_qAt : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (U : AffOp D.X) (T : Thick D.κ D.t), IsLev T.δ (n + 1) → ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ (G : Thick D.κ D.t) (l : T ⟶ G) (r : Λ.L.obj U ⟶ G), IsCop (n + 1) l r ∧ (KK D.κ D.t).QAt l := by
  intro D Λ n U T hT hU
  obtain ⟨F, G, u, q, r, hu, hF, hq, hJ, hc⟩ := GlobalTheory.T.exists_coproductThickening_quotient_freeThickening D Λ n U T hT hU
  obtain ⟨h1, -, -, -⟩ := GlobalTheory.T.hom_spec_points_levels D Λ
  refine ⟨G, u ≫ q, r, hc, ?_⟩
  haveI := D.sec_smooth U.unop
  have hker : RingHom.ker (q.φ : F.B →+* G.B) ≤ F.J := fun b hb ↦ hJ b (by
    rw [show q.φ b = 0 from hb]; exact G.J.zero_mem)
  have hnil : IsNilpotent (RingHom.ker (q.φ : F.B →+* G.B)) := by
    obtain ⟨N, hN⟩ := isNilpotent_of_isNilDP F.nil
    refine ⟨N, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hN]
    exact Ideal.pow_right_mono hker N
  let y : Sec D.s U.unop.1 →ₐ[D.R] G.B := r.φ.comp (Λ.e U : Sec D.s U.unop.1 →ₐ[D.R] (Λ.L.obj U).B)
  let y' : Sec D.s U.unop.1 →ₐ[D.R] F.B := Algebra.FormallySmooth.liftOfSurjective y q.φ hq hnil
  have hy' : ∀ a, q.φ (y' a) = y a := fun a ↦ Algebra.FormallySmooth.liftOfSurjective_apply y q.φ hq hnil a
  have hbij : Function.Bijective q.φ₀ := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ ?_, fun c ↦ ?_⟩
    · obtain ⟨b, rfl⟩ := F.surj b
      rw [q.comm, G.ker] at hb
      exact (F.ker b).2 (hJ b hb)
    · obtain ⟨c, rfl⟩ := G.surj c
      obtain ⟨b, rfl⟩ := hq c
      exact ⟨F.π b, q.comm b⟩
  haveI : IsIso (spMap q.φ₀) :=
    (inferInstance : IsIso (Spec.map (RingEquiv.ofBijective q.φ₀ hbij).toCommRingCatIso.hom))
  have hy := (h1 U G y).2 ⟨r, fun _ ↦ rfl⟩
  have hpt : spMap (F.π.comp (y' : Sec D.s U.unop.1 →+* F.B)) ≫ affPt D.s U.unop = F.x ≫ D.i := by
    rw [← cancel_epi (spMap q.φ₀), ← Category.assoc, ← Cris.spMap_comp, ← Category.assoc, q.pt, ← hy]
    congr 2
    ext a
    exact (q.comm _).trans (congrArg G.π (hy' a))
  obtain ⟨b', hb'⟩ := (h1 U F y').1 hpt
  obtain ⟨s, ⟨hs1, hs2⟩, -⟩ := hc.2 F hF u b'
  have hbq : b' ≫ q = r := Thick.hom_ext fun b ↦ by
    obtain ⟨a, rfl⟩ := (Λ.e U).surjective b
    rw [Thick.comp_φ, hb', hy']; rfl
  have hsq : s ≫ q = 𝟙 G := by
    obtain ⟨c, -, huniq⟩ := hc.2 G hc.1 (u ≫ q) r
    refine (huniq _ ⟨?_, ?_⟩).trans (huniq _ ⟨Category.comp_id _, Category.comp_id _⟩).symm
    · rw [← Category.assoc, hs1]
    · rw [← Category.assoc, hs2, hbq]
  exact (GlobalTheory.CxCoh.QAtFormal.qAt_formal _ (KK D.κ D.t)).2.2 T G F (u ≫ q) s q hsq (by rw [hs1]; exact hu)

end GlobalTheory.PDForm.CopPoincare
