import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapUnit

/- English proof (translation)
Introduce `Λ A B K _ _ _ _ C hC P hP h hR φ`. Take `⟨hsem, e, z, hz, hb⟩` from `hR`. Establish `hw : C.b 0 z = ((C.ℓ : B) ^ e) • C.μ 0 P.oneV`. Establish `h0 : C.b 0 (z - ((C.ℓ : A) ^ e) • P.oneZ) = 0` using `hC.sep 0 _ (fun n => by`. Rewrite using `[map_sub, map_smul, hP.one_r, hz, sub_self])`.

Rewrite `h0` using `[map_sub, map_smulₛₗ, hP.one_b, sub_eq_zero]`. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Use `haveI := hC.fin 0`. Set `bs` to `Module.finBasis K (C.V 0)`.

Establish `h1` using `hb bs`. Rewrite `h1` using `[hw]`. Establish `h2 : ∑ s, h (bs.coord s) • C.μ 0 (bs s) = C.μ 0 P.oneV`. Take `⟨u, hu⟩` from `hC.unit.pow e`. Rewrite `h1` using `[← hu]`.

Establish `h1'` using `congrArg (fun w => ((u⁻¹ : Bˣ) : B) • w) h1`. Simplify `h1'` using `only [smul_smul, Units.inv_mul, one_smul]`. Establish `h3 : C.μ 0 P.oneV = ∑ s, C.o (bs.coord s P.oneV) • C.μ 0 (bs s)` using `by conv_lhs => rw [← bs.sum_repr P.oneV]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smulₛₗ]`. Both sides reduce to the same expression. Establish `h4 : (fun s => h (bs.coord s)) = fun s => C.o (bs.coord s P.oneV)` using `(hC.basis 0 bs (C.μ 0 P.oneV)).unique h2.symm h3`. Establish `h5 : φ = ∑ s, φ (bs s) • bs.coord s`. Use `bs.ext fun t => ?_` and prove the remaining obligations.

Simplify using `[Finset.sum_apply, Module.Basis.coord_apply, Finsupp.single_apply]`. Establish `h6 : φ P.oneV = ∑ s, bs.coord s P.oneV * φ (bs s)` using `by conv_lhs => rw [← bs.sum_repr P.oneV]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul]`.

Both sides reduce to the same expression. Rewrite using `[h6, map_sum]`. Use `conv_lhs => rw [h5]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[hsem, map_mul, mul_comm]`. Conclude with `congrArg (· * C.o (φ (bs s))) (congrFun h4 s)`.
-/
theorem rho_one_eval : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) (P : Cup C), P.Good → ∀ h : Module.Dual K (C.V 0) →+ B, C.Rho P.oneS h → ∀ φ : Module.Dual K (C.V 0), h φ = C.o (φ P.oneV) := by
  intro Λ A B K _ _ _ _ C hC P hP h hR φ
  obtain ⟨hsem, e, z, hz, hb⟩ := hR
  have hw : C.b 0 z = ((C.ℓ : B) ^ e) • C.μ 0 P.oneV := by
    have h0 : C.b 0 (z - ((C.ℓ : A) ^ e) • P.oneZ) = 0 := hC.sep 0 _ (fun n => by
      rw [map_sub, map_smul, hP.one_r, hz, sub_self])
    rw [map_sub, map_smulₛₗ, hP.one_b, sub_eq_zero] at h0
    rw [h0]
    simp
  haveI := hC.fin 0
  let bs := Module.finBasis K (C.V 0)
  have h1 := hb bs
  rw [hw] at h1
  have h2 : ∑ s, h (bs.coord s) • C.μ 0 (bs s) = C.μ 0 P.oneV := by
    obtain ⟨u, hu⟩ := hC.unit.pow e
    rw [← hu] at h1
    have h1' := congrArg (fun w => ((u⁻¹ : Bˣ) : B) • w) h1
    simpa only [smul_smul, Units.inv_mul, one_smul] using h1'
  have h3 : C.μ 0 P.oneV = ∑ s, C.o (bs.coord s P.oneV) • C.μ 0 (bs s) := by
    conv_lhs => rw [← bs.sum_repr P.oneV]
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smulₛₗ]
    rfl
  have h4 : (fun s => h (bs.coord s)) = fun s => C.o (bs.coord s P.oneV) :=
    (hC.basis 0 bs (C.μ 0 P.oneV)).unique h2.symm h3
  have h5 : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [Finset.sum_apply, Module.Basis.coord_apply, Finsupp.single_apply]
  have h6 : φ P.oneV = ∑ s, bs.coord s P.oneV * φ (bs s) := by
    conv_lhs => rw [← bs.sum_repr P.oneV]
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  rw [h6, map_sum]
  conv_lhs => rw [h5]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hsem, map_mul, mul_comm]
  exact congrArg (· * C.o (φ (bs s))) (congrFun h4 s)

end GlobalTheory.CompanionTheory.KapUnit
