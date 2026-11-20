import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLevelBijectiveOfPowEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastOfIsNilpotent
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup

/- English proof (translation)
Introduce `p _ R _ N hN A _ G t x`. Establish `hb` using `omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl`. Set `e` to `LinearEquiv.ofBijective (G.omegaLevel N) hb`. Set `D : G.A N →ₗ[R] R` to `x ∘ₗ e.symm.toLinearMap ∘ₗ AugCot.d (Bialgebra.counitAlgHom R (G.A N))`. Establish `hD : ∀ a b : G.A N, D (a * b) = Coalgebra.counit (R` using `R) a * D b + Coalgebra.counit (R := R) b * D a := by`.

Introduce `a b`. Simplify using `only [D, LinearMap.comp_apply, AugCot.d_mul, map_add, map_smul, smul_eq_mul]`. Both sides reduce to the same expression. Establish `hD1 : D 1 = 0` using `by simp [D]`. Set `ψ₀ : G.A N →ₐ[R] DualNumber R` to `AlgHom.ofLinearMap (Algebra.linearMap R (DualNumber R) ∘ₗ Coalgebra.counit + TrivSqZeroExt.inrHom R R ∘ₗ D) (by simp [hD1]) (fun a b ↦ by`.

Use `ext`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl, hD, mul_comm])`. Establish `hfst : ∀ a, (ψ₀ a).fst = Coalgebra.counit (R` using `R) a := fun a ↦ by`. Simplify using `[ψ₀, TrivSqZeroExt.algebraMap_eq_inl]`.

Establish `hsnd : ∀ a, (ψ₀ a).snd = D a` using `fun a ↦ by`. Simplify using `[ψ₀, TrivSqZeroExt.algebraMap_eq_inl]`. Set `v : epsR R ⟶ A` to `spOver ψ₀ ≫ t.y N`. Establish `hv : IsTangent v`. Establish `h` using `(t.eq_one_iff N ((TrivSqZeroExt.fstHom R R R).comp ψ₀)).2 hfst`.

Rewrite `h` using `[← spOver_comp, Category.assoc]`. Use `(congrArg Over.Hom.left h).trans ?_` and prove the remaining obligations. Rewrite using `[Hom.one_def, Over.comp_left, Over.toUnit_left]`. Conclude with `(congrArg (· ≫ η[A].left) (Cris.spMap_id R)).trans (Category.id_comp _)`. Use `haveI : IsAdicComplete (Ideal.span {(p : R)}) R := isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩`.

Take `⟨x', hx', -⟩` from `t.existsUnique_lieCorr hv`. Use `⟨v, ?_⟩` and prove the remaining obligations. It suffices to establish `hx : x' = x by rw [← hx]; exact hx'`. Use `LinearMap.ext fun w ↦ ?_` and prove the remaining obligations. Establish `k` using `(t.lieCorr_iff hv x').1 hx' N w`.

Take `⟨a, ha⟩` from `AugCot.d_surjective _ (w.1 N)`. Establish `ep : t.tanPt hv N = (epsTo R (ModPow p R N)).comp ψ₀` using `t.inj N _ _ _ (by rw [t.tanPt_y hv N, ← spOver_comp, Category.assoc])`. Establish `ew : e.symm (w.1 N) = w` using `e.symm_apply_eq.2 rfl`. Rewrite `k` using `[← ha, TorsionTower.tanDer_d, ep, AlgHom.comp_apply, snd_epsTo, hsnd]`. Establish `k2 : D a = x w`.

Simplify using `only [D, LinearMap.comp_apply]`. Express the relevant statement in the definitionally equal form `x (e.symm (AugCot.d (Bialgebra.counitAlgHom R (G.A N)) a)) = x w`. Rewrite using `[ha, ew]`. Rewrite `k` using `[k2, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq, hN, Ideal.mem_span_singleton, zero_dvd_iff, sub_eq_zero]`. Conclude with `k`.
-/
theorem exists_lieCorr_of_pow_eq_zero : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A] (G : PDivGroup p R) (t : G.TorsionTower A) (x : G.Lie), ∃ v : epsR R ⟶ A, t.LieCorr x v := by
  intro p _ R _ N hN A _ G t x
  have hb := omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl
  let e := LinearEquiv.ofBijective (G.omegaLevel N) hb
  let D : G.A N →ₗ[R] R := x ∘ₗ e.symm.toLinearMap ∘ₗ AugCot.d (Bialgebra.counitAlgHom R (G.A N))
  have hD : ∀ a b : G.A N, D (a * b) = Coalgebra.counit (R := R) a * D b + Coalgebra.counit (R := R) b * D a := by
    intro a b
    simp only [D, LinearMap.comp_apply, AugCot.d_mul, map_add, map_smul, smul_eq_mul]
    rfl
  have hD1 : D 1 = 0 := by simp [D]
  let ψ₀ : G.A N →ₐ[R] DualNumber R :=
    AlgHom.ofLinearMap
      (Algebra.linearMap R (DualNumber R) ∘ₗ Coalgebra.counit + TrivSqZeroExt.inrHom R R ∘ₗ D)
      (by simp [hD1])
      (fun a b ↦ by
        ext
        · simp [TrivSqZeroExt.algebraMap_eq_inl]
        · simp [TrivSqZeroExt.algebraMap_eq_inl, hD, mul_comm])
  have hfst : ∀ a, (ψ₀ a).fst = Coalgebra.counit (R := R) a := fun a ↦ by
    simp [ψ₀, TrivSqZeroExt.algebraMap_eq_inl]
  have hsnd : ∀ a, (ψ₀ a).snd = D a := fun a ↦ by
    simp [ψ₀, TrivSqZeroExt.algebraMap_eq_inl]
  let v : epsR R ⟶ A := spOver ψ₀ ≫ t.y N
  have hv : IsTangent v := by
    have h := (t.eq_one_iff N ((TrivSqZeroExt.fstHom R R R).comp ψ₀)).2 hfst
    rw [← spOver_comp, Category.assoc] at h
    refine (congrArg Over.Hom.left h).trans ?_
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    exact (congrArg (· ≫ η[A].left) (Cris.spMap_id R)).trans (Category.id_comp _)
  haveI : IsAdicComplete (Ideal.span {(p : R)}) R :=
    isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩
  obtain ⟨x', hx', -⟩ := t.existsUnique_lieCorr hv
  refine ⟨v, ?_⟩
  suffices hx : x' = x by rw [← hx]; exact hx'
  refine LinearMap.ext fun w ↦ ?_
  have k := (t.lieCorr_iff hv x').1 hx' N w
  obtain ⟨a, ha⟩ := AugCot.d_surjective _ (w.1 N)
  have ep : t.tanPt hv N = (epsTo R (ModPow p R N)).comp ψ₀ :=
    t.inj N _ _ _ (by rw [t.tanPt_y hv N, ← spOver_comp, Category.assoc])
  have ew : e.symm (w.1 N) = w := e.symm_apply_eq.2 rfl
  rw [← ha, TorsionTower.tanDer_d, ep, AlgHom.comp_apply, snd_epsTo, hsnd] at k
  have k2 : D a = x w := by
    simp only [D, LinearMap.comp_apply]
    change x (e.symm (AugCot.d (Bialgebra.counitAlgHom R (G.A N)) a)) = x w
    rw [ha, ew]
  rw [k2, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq, hN, Ideal.mem_span_singleton,
    zero_dvd_iff, sub_eq_zero] at k
  exact k

end GlobalTheory.PDivGroup
