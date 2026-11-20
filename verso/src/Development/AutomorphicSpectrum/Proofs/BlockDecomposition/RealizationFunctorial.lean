import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr

open CrystallineSemistableComparison.Pb.Kap

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.KapRhoHom

/- English proof (translation)
Establish `hφ : φ = ∑ s, φ (bs s) • bs.coord s`. Use `bs.ext fun t => ?_` and prove the remaining obligations. Simplify using `[LinearMap.sum_apply, Finsupp.single_apply]`. Use `conv_lhs => rw [hφ]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[hf, mul_comm]`.
-/
private theorem dual_expand {K B : Type} {V : Type*} [Field K] [CommRing B] [AddCommGroup V] [Module K V]
    (o : K →+* B) (f : Module.Dual K V →+ B) (hf : ∀ (k : K) φ, f (k • φ) = o k * f φ)
    {m : ℕ} (bs : Module.Basis (Fin m) K V) (φ : Module.Dual K V) :
    f φ = ∑ s, f (bs.coord s) * o (φ (bs s)) := by
  have hφ : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [LinearMap.sum_apply, Finsupp.single_apply]
  conv_lhs => rw [hφ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hf, mul_comm]

/- English proof (translation)
Introduce `Λ A B K Λ' A' B' _ _ _ _ _ _ _ C C' h hC hC' hh j x f hR`. Take `⟨hs, e, z, hz, hW⟩` from `hR`. Establish `htr : ∀ φ : Module.Dual K (C'.V j), h.tr j f φ = h.sB (f (Module.Dual.transpose (R` using `K) (h.fV j) φ)) := fun φ => rfl`. Use `⟨fun k φ => ?_, e, h.fZ j z, fun n => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[htr, htr, map_smul, hs, map_mul, hh.o]`.

Rewrite using `[← hh.red, hz, map_smulₛₗ, hh.r, map_pow, map_natCast, hh.ℓ]`. Introduce `m bs' haveI := hC.fin j`. Establish `bs` using `Module.finBasis K (C.V j)`. Establish `hE` using `congrArg (h.fW j) (hW bs)`. Rewrite `hE` using `[hh.b, map_smulₛₗ, map_sum, map_pow, map_natCast]`.

Rewrite using `[← hE, hh.ℓ]`. Use `congr 1`. Establish `hexp : ∀ t, h.tr j f (bs'.coord t) = ∑ s, h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s)))`. Introduce `t`. Rewrite using `[htr, dual_expand C.o f hs bs, map_sum]`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hh.o]`. Both sides reduce to the same expression. Establish `hμ : ∀ s, C'.μ j (h.fV j (bs s)) = ∑ t, C'.o (bs'.coord t (h.fV j (bs s))) • C'.μ j (bs' t)`. Introduce `s`.

Use `conv_lhs => rw [← bs'.sum_repr (h.fV j (bs s))]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ]`. Both sides reduce to the same expression.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[hexp, Finset.sum_smul]`. Use `_ = ∑ s, ∑ t, (h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s)))) • C'.μ j (bs' t) := Finset.sum_comm`. Use `_ = ∑ s, h.fW j (f (bs.coord s) • C.μ j (bs s)) := by`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, hh.μ, hμ, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul]`.
-/
theorem rho_hom :
    ∀ {Λ A B K Λ' A' B' : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] [CommRing Λ']
      [CommRing A'] [CommRing B'] (C : Chain.{1} Λ A B K) (C' : Chain.{1} Λ' A' B' K)
      (h : Hom C C'), C.Good → C'.Good → h.Good → ∀ {j : ℕ} (x : ∀ n, C.S n j)
      (f : Module.Dual K (C.V j) →+ B), C.Rho x f →
        C'.Rho (fun n => h.fS n j (x n)) (h.tr j f) := by
  intro Λ A B K Λ' A' B' _ _ _ _ _ _ _ C C' h hC hC' hh j x f hR
  obtain ⟨hs, e, z, hz, hW⟩ := hR
  have htr : ∀ φ : Module.Dual K (C'.V j),
      h.tr j f φ = h.sB (f (Module.Dual.transpose (R := K) (h.fV j) φ)) := fun φ => rfl
  refine ⟨fun k φ => ?_, e, h.fZ j z, fun n => ?_, ?_⟩
  · rw [htr, htr, map_smul, hs, map_mul, hh.o]
  · rw [← hh.red, hz, map_smulₛₗ, hh.r, map_pow, map_natCast, hh.ℓ]
  · intro m bs'
    haveI := hC.fin j
    have bs := Module.finBasis K (C.V j)
    have hE := congrArg (h.fW j) (hW bs)
    rw [hh.b, map_smulₛₗ, map_sum, map_pow, map_natCast] at hE
    rw [← hE, hh.ℓ]
    congr 1
    have hexp : ∀ t, h.tr j f (bs'.coord t) =
        ∑ s, h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s))) := by
      intro t
      rw [htr, dual_expand C.o f hs bs, map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_mul, hh.o]
      rfl
    have hμ : ∀ s, C'.μ j (h.fV j (bs s)) =
        ∑ t, C'.o (bs'.coord t (h.fV j (bs s))) • C'.μ j (bs' t) := by
      intro s
      conv_lhs => rw [← bs'.sum_repr (h.fV j (bs s))]
      rw [map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_smulₛₗ]
      rfl
    calc ∑ t, h.tr j f (bs'.coord t) • C'.μ j (bs' t)
        = ∑ t, ∑ s, (h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s)))) • C'.μ j (bs' t) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hexp, Finset.sum_smul]
      _ = ∑ s, ∑ t, (h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s)))) • C'.μ j (bs' t) :=
          Finset.sum_comm
      _ = ∑ s, h.fW j (f (bs.coord s) • C.μ j (bs s)) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [map_smulₛₗ, hh.μ, hμ, Finset.smul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [mul_smul]

end GlobalTheory.CompanionTheory.KapRhoHom
