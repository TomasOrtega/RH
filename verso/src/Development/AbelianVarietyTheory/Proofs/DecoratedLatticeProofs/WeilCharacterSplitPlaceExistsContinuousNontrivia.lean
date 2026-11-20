import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceAnnihilatorRelativelyCompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocChar

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

/- English proof (translation)
Establish `h` using `p.ι_π 1`. Rewrite `h` using `[map_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem ι_one : p.ι 1 = p.e := by
  have h := p.ι_π 1
  rwa [map_one, mul_one] at h

/- English proof (translation)
Establish `h` using `p.ι_π (p.ι x)`. Rewrite `h` using `[p.π_ι]`. Conclude with `h.symm`.
-/
theorem e_mul_ι (x : k) : p.e * p.ι x = p.ι x := by
  have h := p.ι_π (p.ι x)
  rw [p.π_ι] at h
  exact h.symm

/- English proof (translation)
Establish `h` using `p.ι_π (p.ι x * p.ι y)`. Rewrite `h` using `[map_mul, p.π_ι, p.π_ι]`. Rewrite using `[h, ← mul_assoc, e_mul_ι]`.
-/
theorem ι_mul (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have h := p.ι_π (p.ι x * p.ι y)
  rw [map_mul, p.π_ι, p.π_ι] at h
  rw [h, ← mul_assoc, e_mul_ι]

/- English proof (translation)
The claim follows from `(_root_.map_ne_zero (p.π.comp (incA D))).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)`.
-/
theorem xi_ne : p.xi ≠ 0 :=
  (_root_.map_ne_zero (p.π.comp (incA D))).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

/- English proof (translation)
Establish `h1` using `e_mul_ι p x`. Establish `h2` using `e_mul_ι p y`. Establish `h3 : p.e * p.e = p.e` using `p.split.1`. Rewrite using `[ι_mul]`. Take the linear combination `(-1 : AE D) * h1 + (-1 : AE D) * h2 + h3`.
-/
theorem mul_aux (x y : k) : (p.ι x + (1 - p.e)) * (p.ι y + (1 - p.e)) = p.ι (x * y) + (1 - p.e) := by
  have h1 := e_mul_ι p x
  have h2 := e_mul_ι p y
  have h3 : p.e * p.e = p.e := p.split.1
  rw [ι_mul]
  linear_combination (-1 : AE D) * h1 + (-1 : AE D) * h2 + h3

def unitsHom : kˣ →* (AE D)ˣ where
  toFun x := ⟨p.ι x + (1 - p.e), p.ι ↑x⁻¹ + (1 - p.e),
    by rw [mul_aux, Units.mul_inv, ι_one, add_sub_cancel],
    by rw [mul_aux, Units.inv_mul, ι_one, add_sub_cancel]⟩
  map_one' := by
    ext
    simp only [Units.val_one, ι_one, Units.val_mk, add_sub_cancel]
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk]
    rw [mul_aux]

def wchar (ψ : AddChar (AF D.host.F) ℂ) (h : ∀ x, ‖ψ x‖ = 1) : AddChar k Circle where
  toFun x := (⟨psiE ψ (incA D D.host.xi0 * p.ι x), mem_sphere_zero_iff_norm.2 (h _)⟩ : Submonoid.unitSphere ℂ)
  map_zero_eq_one' := by
    apply Circle.ext
    show psiE ψ (incA D D.host.xi0 * p.ι 0) = 1
    simp [psiE]
  map_add_eq_mul' x y := by
    apply Circle.ext
    show psiE ψ (incA D D.host.xi0 * p.ι (x + y)) = psiE ψ (incA D D.host.xi0 * p.ι x) * psiE ψ (incA D D.host.xi0 * p.ι y)
    simp only [psiE, map_add, mul_add, AddChar.map_add_eq_mul]

end GlobalTheory.LocChar

namespace GlobalTheory.LocChar

/- English proof (translation)
Introduce `D k _ _ _ _ p ψ hψ`. Use `⟨⟨wchar p ψ hψ.1.2.1, fun x => rfl⟩, fun ψk hk => ⟨?_, ?_⟩, xi_ne p, ι_mul p, fun χ => ⟨(Circle.toUnits.comp χ).comp (unitsHom p), fun x a ha => ?_⟩⟩` and prove the remaining obligations. Establish `: IsModuleTopology (AF D.host.F) (AE D)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)`. Establish `hT : Continuous (Algebra.trace (AF D.host.F) (AE D))` using `IsModuleTopology.continuous_of_linearMap _`.

Establish `hc : Continuous fun x => ((ψk x : Circle) : ℂ)`. Rewrite using `[funext hk]`. Conclude with `hψ.1.1.comp (hT.comp (continuous_const.mul p.cont_ι))`. Conclude with `continuous_induced_rng.2 hc`. Introduce `h1`.

Take `⟨v, he⟩` from `(GlobalTheory.IdemModTwo.isSplitIdem_iff p.e).1 p.split`. Take `⟨y, hy⟩` from `GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ v`. Establish `hta` using `GlobalTheory.SplitAnnihilator.trace_split he y 1`. Rewrite `hta` using `[mul_one]`. Establish `hea : p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e)) = GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e)`.

Take the linear combination `(GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e) * he.1`. Generalize the expression as in `GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e) = a at hea hta`. Establish `hu0 : IsUnit (incA D D.host.xi0)` using `(isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map (incA D)`. Take `⟨u, hu⟩` from `hu0`. Establish `hx : incA D D.host.xi0 * p.ι (p.π (↑u⁻¹ * a)) = a`.

Rewrite using `[p.ι_π, ← hu]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `hk (p.π (↑u⁻¹ * a))`. Rewrite `h2` using `[h1, AddChar.one_apply, Circle.coe_one, hx]`. Conclude with `hy (by rw [psiV, ← hta]; exact h2.symm)`.

Establish `: unitsHom p x = a` using `Units.ext ha.symm`. Simplify using `only [MonoidHom.comp_apply, this]`. Both sides reduce to the same expression.
-/
theorem weil_char_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∃ ψk : AddChar k Circle, p.IsChar ψ ψk) ∧ (∀ ψk : AddChar k Circle, p.IsChar ψ ψk → Continuous ψk ∧ ψk ≠ 1) ∧ p.xi ≠ 0 ∧ (∀ x y, p.ι (x * y) = p.ι x * p.ι y) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ := by
  intro D k _ _ _ _ p ψ hψ
  refine ⟨⟨wchar p ψ hψ.1.2.1, fun x => rfl⟩, fun ψk hk => ⟨?_, ?_⟩, xi_ne p, ι_mul p, fun χ =>
    ⟨(Circle.toUnits.comp χ).comp (unitsHom p), fun x a ha => ?_⟩⟩
  · have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
    have hT : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
      IsModuleTopology.continuous_of_linearMap _
    have hc : Continuous fun x => ((ψk x : Circle) : ℂ) := by
      rw [funext hk]
      exact hψ.1.1.comp (hT.comp (continuous_const.mul p.cont_ι))
    exact continuous_induced_rng.2 hc
  · intro h1
    obtain ⟨v, he⟩ := (GlobalTheory.IdemModTwo.isSplitIdem_iff p.e).1 p.split
    obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ v
    have hta := GlobalTheory.SplitAnnihilator.trace_split he y 1
    rw [mul_one] at hta
    have hea : p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e)) =
        GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e) := by
      linear_combination (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e) * he.1
    generalize GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e) = a at hea hta
    have hu0 : IsUnit (incA D D.host.xi0) := (isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map (incA D)
    obtain ⟨u, hu⟩ := hu0
    have hx : incA D D.host.xi0 * p.ι (p.π (↑u⁻¹ * a)) = a := by
      rw [p.ι_π, ← hu]
      calc (u : AE D) * (p.e * (↑u⁻¹ * a)) = ((u : AE D) * ↑u⁻¹) * (p.e * a) := by ring
        _ = a := by rw [Units.mul_inv, one_mul, hea]
    have h2 := hk (p.π (↑u⁻¹ * a))
    rw [h1, AddChar.one_apply, Circle.coe_one, hx] at h2
    exact hy (by rw [psiV, ← hta]; exact h2.symm)
  · have : unitsHom p x = a := Units.ext ha.symm
    simp only [MonoidHom.comp_apply, this]
    rfl

end GlobalTheory.LocChar

end
