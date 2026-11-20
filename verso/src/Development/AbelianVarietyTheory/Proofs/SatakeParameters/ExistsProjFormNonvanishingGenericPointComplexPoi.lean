import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

/- English proof (translation)
Set `V : T → Submodule ℂ (GlobalTheory.ProjSpace.grading ℂ N 1)` to `fun x => ((x.1.asHomogeneousIdeal.toIdeal).restrictScalars ℂ).comap (GlobalTheory.ProjSpace.grading ℂ N 1).subtype`. Establish `hV : ∀ x, V x ≠ ⊤`. Introduce `x h`. Take `⟨i, hi⟩` from `GlobalTheory.ProjSpace.exists_mem_chart ℂ N x.1`. Establish `hX : (⟨MvPolynomial.X i, GlobalTheory.ProjSpace.X_mem ℂ N i⟩ : GlobalTheory.ProjSpace.grading ℂ N 1) ∈ V x` using `h ▸ Submodule.mem_top`.

Conclude with `(Proj.mem_basicOpen _ _ _).1 hi hX`. Take `⟨ℓ, hℓ⟩` from `Submodule.exists_forall_notMem_of_forall_ne_top V hV`. Establish `hpow : ℓ.1 ^ n ∈ GlobalTheory.ProjSpace.grading ℂ N n`. Simplify using `using SetLike.pow_mem_graded n ℓ.2`. Use `⟨ℓ.1 ^ n, hpow, fun x hx hmem => hℓ ⟨x, hx⟩ ?_⟩` and prove the remaining obligations.

Conclude with `x.isPrime.mem_of_pow_mem n hmem`.
-/
theorem exists_form_forall_notMem (N n : ℕ) (T : Finset (PSpace ℂ N)) :
    ∃ f ∈ GlobalTheory.ProjSpace.grading ℂ N n, ∀ x ∈ T, f ∉ x.asHomogeneousIdeal := by
  classical
  let V : T → Submodule ℂ (GlobalTheory.ProjSpace.grading ℂ N 1) := fun x =>
    ((x.1.asHomogeneousIdeal.toIdeal).restrictScalars ℂ).comap (GlobalTheory.ProjSpace.grading ℂ N 1).subtype
  have hV : ∀ x, V x ≠ ⊤ := by
    intro x h
    obtain ⟨i, hi⟩ := GlobalTheory.ProjSpace.exists_mem_chart ℂ N x.1
    have hX : (⟨MvPolynomial.X i, GlobalTheory.ProjSpace.X_mem ℂ N i⟩ : GlobalTheory.ProjSpace.grading ℂ N 1) ∈ V x :=
      h ▸ Submodule.mem_top
    exact (Proj.mem_basicOpen _ _ _).1 hi hX
  obtain ⟨ℓ, hℓ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top V hV
  have hpow : ℓ.1 ^ n ∈ GlobalTheory.ProjSpace.grading ℂ N n := by
    simpa using SetLike.pow_mem_graded n ℓ.2
  refine ⟨ℓ.1 ^ n, hpow, fun x hx hmem => hℓ ⟨x, hx⟩ ?_⟩
  exact x.isPrime.mem_of_pow_mem n hmem

/- English proof (translation)
Introduce `X _ p N ι n F`. Take `⟨f, hf, hT⟩` from `exists_form_forall_notMem N n (insert (ι.base (genericPoint X)) (F.image fun z => ι.base (z.1 (IsLocalRing.closedPoint ℂ))))`. Use `⟨f, hf, hT _ (Finset.mem_insert_self _ _), fun z hz => ?_⟩` and prove the remaining obligations. Conclude with `CxPts.mem_ptsIn.2 (hT _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hz)))`.
-/
theorem exists_form_genericPoint_cxPts : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (N : ℕ)
    (ι : X ⟶ PSpace ℂ N) (n : ℕ) (F : Finset (CxPts p (RingHom.id ℂ))), ∃ f ∈ GlobalTheory.ProjSpace.grading ℂ N n,
      genericPoint X ∈ GlobalTheory.EtProj.fOpen ι f ∧ ∀ z ∈ F, z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι f) := by
  intro X _ p N ι n F
  classical
  obtain ⟨f, hf, hT⟩ := exists_form_forall_notMem N n
    (insert (ι.base (genericPoint X)) (F.image fun z => ι.base (z.1 (IsLocalRing.closedPoint ℂ))))
  refine ⟨f, hf, hT _ (Finset.mem_insert_self _ _), fun z hz => ?_⟩
  exact CxPts.mem_ptsIn.2 (hT _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hz)))

end GlobalTheory.EtProj
