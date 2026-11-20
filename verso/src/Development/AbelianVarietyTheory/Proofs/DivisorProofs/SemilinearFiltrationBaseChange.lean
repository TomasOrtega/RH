import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `R R' _ _ _ M _ _ _ _ M' _ _ f hf F hF F' hF' g hg`. Substitute `hF'` using the available equality. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨h, hh, rfl⟩`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_dualAnnihilator]`. Introduce `w hw`. Use `Submodule.span_induction (p := fun w _ => g h w = 0) ?_ ?_ ?_ ?_ hw` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Rewrite using `[hg, (Submodule.mem_dualAnnihilator h).1 hh c hc, map_zero]`.

Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`. Simplify using `[hx, hy]`. Introduce `a x _ hx`. Simplify using `[hx]`.

Introduce `φ hφ`. Rewrite `hφ` using `[Submodule.mem_dualAnnihilator]`. Take `⟨N, hN⟩` from `hF`. Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' R M`. Take `⟨s, hs⟩` from `Module.projective_lifting_property π LinearMap.id hπ`.

Set `q : M →ₗ[R] M` to `LinearMap.id - F.subtype ∘ₗ Submodule.linearProjOfIsCompl F N hN`. Establish `hqF : ∀ c ∈ F, q c = 0`. Introduce `c hc`. Establish `e : F.linearProjOfIsCompl N hN c = ⟨c, hc⟩` using `Submodule.linearProjOfIsCompl_apply_left hN ⟨c, hc⟩`. Simplify using `[q, e]`.

Establish `hqd : ∀ m, m - q m ∈ F` using `by intro m; simp [q]`. Set `k : Fin n → Module.Dual R M` to `fun i => LinearMap.proj i ∘ₗ s ∘ₗ q`. Establish `hk : ∀ i, k i ∈ F.dualAnnihilator`. Introduce `i`. Rewrite using `[Submodule.mem_dualAnnihilator]`.

Introduce `c hc`. Simplify using `[k, hqF c hc]`. Establish `hexp : ∀ m : M, m = ∑ i, s m i • π (Pi.single i 1)`. Introduce `m`. Establish `e1 : m = π (s m)` using `by rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]`.

Use `conv_lhs => rw [e1, pi_eq_sum_univ (s m)]`. Simplify using `only [map_sum, map_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 2`. Use extensionality with `j`.

Simplify using `[Pi.single_apply, eq_comm]`. Establish `key : φ = ∑ i, φ (f (π (Pi.single i 1))) • g (k i)`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `w`. Take `⟨z, rfl⟩` from `hf.2 w`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul x c`. Rewrite using `[liftSemi_tmul, map_smul, map_smul]`.

Use `congr 1`. Establish `h1 : φ (f c) = φ (f (q c))`. Use `hφ _ (Submodule.subset_span ⟨_, hqd c, rfl⟩)` as an intermediate fact. Rewrite `this` using `[map_sub, map_sub, sub_eq_zero]`. Conclude with `this`.

Rewrite using `[h1, hexp (q c)]`. Simplify using `[map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, hg, k, Algebra.smul_def, mul_comm]`. Rewrite using `[key]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k i, hk i, rfl⟩)`.
-/
theorem annihilator_baseChange : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] {M' : Type*} [AddCommGroup M'] [Module R' M']
    (f : M →ₛₗ[algebraMap R R'] M') (hf : Function.Bijective (liftSemi f)) (F : Submodule R M)
    (hF : ∃ N : Submodule R M, IsCompl F N) (F' : Submodule R' M') (hF' : F' = Submodule.span R' (f '' (F : Set M)))
    (g : Module.Dual R M →ₛₗ[algebraMap R R'] Module.Dual R' M') (hg : ∀ h c, g h (f c) = algebraMap R R' (h c)),
   Submodule.span R' (g '' (F.dualAnnihilator : Set (Module.Dual R M))) = F'.dualAnnihilator := by
  intro R R' _ _ _ M _ _ _ _ M' _ _ f hf F hF F' hF' g hg
  subst hF'
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨h, hh, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
    intro w hw
    refine Submodule.span_induction (p := fun w _ => g h w = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨c, hc, rfl⟩
      rw [hg, (Submodule.mem_dualAnnihilator h).1 hh c hc, map_zero]
    · simp
    · intro x y _ _ hx hy; simp [hx, hy]
    · intro a x _ hx; simp [hx]
  · intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    obtain ⟨N, hN⟩ := hF
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
    let q : M →ₗ[R] M := LinearMap.id - F.subtype ∘ₗ Submodule.linearProjOfIsCompl F N hN
    have hqF : ∀ c ∈ F, q c = 0 := by
      intro c hc
      have e : F.linearProjOfIsCompl N hN c = ⟨c, hc⟩ := Submodule.linearProjOfIsCompl_apply_left hN ⟨c, hc⟩
      simp [q, e]
    have hqd : ∀ m, m - q m ∈ F := by intro m; simp [q]
    let k : Fin n → Module.Dual R M := fun i => LinearMap.proj i ∘ₗ s ∘ₗ q
    have hk : ∀ i, k i ∈ F.dualAnnihilator := by
      intro i; rw [Submodule.mem_dualAnnihilator]; intro c hc; simp [k, hqF c hc]
    have hexp : ∀ m : M, m = ∑ i, s m i • π (Pi.single i 1) := by
      intro m
      have e1 : m = π (s m) := by rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
      conv_lhs => rw [e1, pi_eq_sum_univ (s m)]
      simp only [map_sum, map_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      ext j
      simp [Pi.single_apply, eq_comm]
    have key : φ = ∑ i, φ (f (π (Pi.single i 1))) • g (k i) := by
      apply LinearMap.ext; intro w
      obtain ⟨z, rfl⟩ := hf.2 w
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x c =>
        rw [liftSemi_tmul, map_smul, map_smul]
        congr 1
        have h1 : φ (f c) = φ (f (q c)) := by
          have := hφ _ (Submodule.subset_span ⟨_, hqd c, rfl⟩)
          rw [map_sub, map_sub, sub_eq_zero] at this; exact this
        rw [h1, hexp (q c)]
        simp [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, hg, k, Algebra.smul_def, mul_comm]
    rw [key]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k i, hk i, rfl⟩)

end GlobalTheory
