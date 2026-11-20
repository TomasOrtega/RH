import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

/- English proof (translation)
Simplify using `only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.transpose_apply, HSpace.gram]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hT_symm_equivFun {D : D7} (V : HSp D) (x y : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm y) =
      ∑ a, ∑ b, y a * V.gramᵀ a b * star (x b) := by
  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.transpose_apply, HSpace.gram]
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify using `using hx`. Introduce `h`. Conclude with `⟨_, h, V.frame.equivFun.apply_symm_apply v⟩`.
-/
theorem mem_latC {D : D7} (V : HSp D) (v : Fin V.rank → D.host.E) :
    v ∈ latC V ↔ V.frame.equivFun.symm v ∈ V.L0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, V.frame.equivFun.apply_symm_apply v⟩

/- English proof (translation)
Introduce `h`. Take `⟨v, hv, h0⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 h`. Apply `hv` to reduce the goal to its premises. Establish `h1 : V.frame.equivFun.symm v = 0`. Apply `V.nondeg.2` to reduce the goal to its premises.

Introduce `x`. Take `⟨x, rfl⟩` from `V.frame.equivFun.symm.surjective x`. Rewrite using `[hT_symm_equivFun, Finset.sum_comm]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul]`.

Establish `: ∑ a, v a * V.gramᵀ a b = 0` using `congrFun h0 b`. Rewrite using `[this, zero_mul]`. Conclude with `V.frame.equivFun.symm.map_eq_zero_iff.1 h1`.
-/
theorem gram_transpose_det_ne_zero {D : D7} (V : HSp D) : V.gramᵀ.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  apply hv
  have h1 : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    obtain ⟨x, rfl⟩ := V.frame.equivFun.symm.surjective x
    rw [hT_symm_equivFun, Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ a, v a * V.gramᵀ a b = 0 := congrFun h0 b
    rw [this, zero_mul]
  exact V.frame.equivFun.symm.map_eq_zero_iff.1 h1

/- English proof (translation)
Introduce `D V`. Use `⟨?_, fun v => rfl, ?_, ?_, fun x => star_star x, fun x => rfl, ?_, ?_, gram_transpose_det_ne_zero V, ?_, ?_⟩` and prove the remaining obligations. Unfold `latHat GlobalTheory.AdLat.hat`. Use `congr 1`. Use extensionality with `z`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, x, hx, rfl⟩`. Conclude with `⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩`. Introduce and unpack `⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨a, ha, x, hx, rfl⟩`.

Conclude with `V.standardTuple_isLattice.fg.map _`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Take `⟨x, rfl⟩` from `V.frame.equivFun.surjective v`. Establish `hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V)`.

Rewrite using `[V.standardTuple_isLattice.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Use `Submodule.mem_map_of_mem (f := V.frame.equivFun.toLinearMap) hx` as an intermediate fact. Rewrite `this` using `[Submodule.map_span]`. Conclude with `this`.

Introduce `h`. Apply `IsCMField.complexConj_ne_one D.host.E` to reduce the goal to its premises. Use `AlgEquiv.ext fun x => ?_` and prove the remaining obligations. Establish `hx : cF D x = x` using `by rw [h]; rfl`. Conclude with `hx`.

Introduce `a b`. Conclude with `V.herm.eq _ _`. Introduce `x y`. Rewrite using `[hT_symm_equivFun]`. Simplify using `only [herm, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]`.

Both sides reduce to the same expression. Introduce `v`. Rewrite using `[mem_latC]`. Use `conv_rhs => rw [← V.baseLattice_isUnimodular]`. Establish `key : V.frame.equivFun.symm v ∈ Formalism.HermitianLatticesTheory.dual V.hT V.L0 ↔ ∀ y ∈ V.L0, V.hT y (V.frame.equivFun.symm v) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)`.

Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]`. Both sides reduce to the same expression. Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`.

Take `⟨y, rfl⟩` from `V.frame.equivFun.symm.surjective y`. Rewrite using `[hT_symm_equivFun, Submodule.mem_one]`. Conclude with `(FractionalIdeal.mem_one_iff _).1 (h y ((mem_latC V y).2 hy))`. Introduce `h y hy`. Use `h _ ((mem_latC V y).1 hy)` as an intermediate fact.

Rewrite `this` using `[hT_symm_equivFun, Submodule.mem_one]`. Conclude with `(FractionalIdeal.mem_one_iff _).2 this`.
-/
theorem latHat_eq_hat_and_gram :
    ∀ (D : D7) (V : HSp D), latHat V = GlobalTheory.AdLat.hat D.host.F (latC V : Set (Fin V.rank → D.host.E)) ∧ (∀ v, finVec V v = GlobalTheory.AdLat.fv D.host.F v) ∧ (latC V).FG ∧ Submodule.span D.host.E (latC V : Set (Fin V.rank → D.host.E)) = ⊤ ∧ (∀ x, cF D (cF D x) = x) ∧ (∀ x, cF D x = cc x) ∧ cF D ≠ 1 ∧ (∀ a b, cF D (V.gramᵀ a b) = V.gramᵀ b a) ∧ V.gramᵀ.det ≠ 0 ∧ (∀ x y, V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm y) = -herm (-V.gramᵀ) y x) ∧ ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latC V, (∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ latC V := by
  intro D V
  refine ⟨?_, fun v => rfl, ?_, ?_, fun x => star_star x, fun x => rfl, ?_, ?_,
    gram_transpose_det_ne_zero V, ?_, ?_⟩
  · unfold latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  · exact V.standardTuple_isLattice.fg.map _
  · rw [eq_top_iff]
    intro v _
    obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective v
    have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [V.standardTuple_isLattice.span_eq_top]; trivial
    have := Submodule.mem_map_of_mem (f := V.frame.equivFun.toLinearMap) hx
    rw [Submodule.map_span] at this
    exact this
  · intro h
    apply IsCMField.complexConj_ne_one D.host.E
    refine AlgEquiv.ext fun x => ?_
    have hx : cF D x = x := by rw [h]; rfl
    exact hx
  · intro a b
    exact V.herm.eq _ _
  · intro x y
    rw [hT_symm_equivFun]
    simp only [herm, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rfl
  · intro v
    rw [mem_latC]
    conv_rhs => rw [← V.baseLattice_isUnimodular]
    have key : V.frame.equivFun.symm v ∈ Formalism.HermitianLatticesTheory.dual V.hT V.L0 ↔
        ∀ y ∈ V.L0, V.hT y (V.frame.equivFun.symm v) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
      rfl
    rw [key]
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := V.frame.equivFun.symm.surjective y
      rw [hT_symm_equivFun, Submodule.mem_one]
      exact (FractionalIdeal.mem_one_iff _).1 (h y ((mem_latC V y).2 hy))
    · intro h y hy
      have := h _ ((mem_latC V y).1 hy)
      rw [hT_symm_equivFun, Submodule.mem_one] at this
      exact (FractionalIdeal.mem_one_iff _).2 this

end GlobalTheory.Member
