import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowParseval
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InWLeft
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPS

noncomputable section

open NumberField Formalism.BasicNotions
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def Wb : Submodule D.host.E (VS D).V :=
  ⨅ c, LinearMap.ker ((VS D).hT (X.eX c)) ⊓ LinearMap.ker ((VS D).hT (X.fY c))

/- English proof (translation)
Simplify using `[Wb, Submodule.mem_iInf, LinearMap.mem_ker]`.
-/
theorem mem_Wb {y : (VS D).V} : y ∈ Wb X ↔ ∀ c, (VS D).hT (X.eX c) y = 0 ∧ (VS D).hT (X.fY c) y = 0 := by
  simp [Wb, Submodule.mem_iInf, LinearMap.mem_ker]

def phi : (VS D).V →ₗ[D.host.E] (Fin D.R.rS → D.host.E) × (Fin D.R.rS → D.host.E) :=
  LinearMap.prod (LinearMap.pi fun c => (VS D).hT (X.eX c)) (LinearMap.pi fun c => (VS D).hT (X.fY c))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phi_apply (y : (VS D).V) :
    phi X y = (fun c => (VS D).hT (X.eX c) y, fun c => (VS D).hT (X.fY c) y) := rfl

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[LinearMap.mem_ker, mem_Wb, phi_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h c`. Conclude with `⟨congrFun (congrArg Prod.fst h) c, congrFun (congrArg Prod.snd h) c⟩`.

Introduce `h`. Use `Prod.ext (funext fun c => (h c).1) (funext fun c => (h c).2)` and prove the remaining obligations.
-/
theorem ker_phi : LinearMap.ker (phi X) = Wb X := by
  ext y
  rw [LinearMap.mem_ker, mem_Wb, phi_apply]
  constructor
  · intro h c
    exact ⟨congrFun (congrArg Prod.fst h) c, congrFun (congrArg Prod.snd h) c⟩
  · intro h
    refine Prod.ext (funext fun c => (h c).1) (funext fun c => (h c).2)

/- English proof (translation)
Rewrite using `[LinearMap.range_eq_top]`. Introduce and unpack `⟨p, q⟩`. Use `⟨∑ a, p a • X.fY a + ∑ a, q a • X.eX a, ?_⟩` and prove the remaining obligations. Rewrite using `[phi_apply]`. Use `Prod.ext (funext fun c => ?_) (funext fun c => ?_)` and prove the remaining obligations.

Simplify using `[map_sum, map_smul, X.ef, X.ee, Finset.sum_ite_eq]`. Simplify using `[map_sum, map_smul, X.ff, Ex.h_fe, Finset.sum_ite_eq]`.
-/
theorem range_phi : LinearMap.range (phi X) = ⊤ := by
  rw [LinearMap.range_eq_top]
  rintro ⟨p, q⟩
  refine ⟨∑ a, p a • X.fY a + ∑ a, q a • X.eX a, ?_⟩
  rw [phi_apply]
  refine Prod.ext (funext fun c => ?_) (funext fun c => ?_)
  · simp [map_sum, map_smul, X.ef, X.ee, Finset.sum_ite_eq]
  · simp [map_sum, map_smul, X.ff, Ex.h_fe, Finset.sum_ite_eq]

/- English proof (translation)
Rewrite using `[Module.finrank_eq_card_basis X.bas, Fintype.card_fin, nX X]`.
-/
theorem finrank_V (X : HidaSetting D) : Module.finrank D.host.E (VS D).V = 2 * D.R.rS + D.R.k + 1 := by
  rw [Module.finrank_eq_card_basis X.bas, Fintype.card_fin, nX X]

/- English proof (translation)
Establish `h` using `LinearMap.finrank_range_add_finrank_ker (phi X)`. Rewrite `h` using `[range_phi, ker_phi, finrank_top, Module.finrank_prod, Module.finrank_fin_fun, finrank_V X]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_Wb : Module.finrank D.host.E (Wb X) = D.R.k + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (phi X)
  rw [range_phi, ker_phi, finrank_top, Module.finrank_prod, Module.finrank_fin_fun, finrank_V X] at h
  omega

/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Conclude with `(mem_Wb X).2 fun c => X.Lb_perp x hx c`.
-/
theorem span_Lb_le : Submodule.span D.host.E (X.Lb : Set (VS D).V) ≤ Wb X := by
  rw [Submodule.span_le]
  intro x hx
  exact (mem_Wb X).2 fun c => X.Lb_perp x hx c

/- English proof (translation)
Use `le_antisymm (span_Lb_le X) fun y hy => ?_` and prove the remaining obligations. Establish `hy'` using `(mem_Wb X).1 hy`. Establish `htop : Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) = ⊤` using `(VS D).standardTuple_isLattice.span_eq_top`. Establish `hyL : y ∈ Submodule.span D.host.E ((VS D).L0 : Set (VS D).V)` using `by rw [htop]; trivial`. Establish `hle : Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) ≤ Submodule.span D.host.E (Set.range X.eX) ⊔ Submodule.span D.host.E (X.Lb : Set (VS D).V) ⊔ Submodule.span D.host.E (Set.range X.fY)`.

Rewrite using `[Submodule.span_le]`. Introduce `z hz`. Use `set T := Submodule.span D.host.E (Set.range X.eX) ⊔ Submodule.span D.host.E (X.Lb : Set (VS D).V) ⊔ Submodule.span D.host.E (Set.range X.fY) with hT`. Establish `hL : (VS D).L0 ≤ T.restrictScalars (𝓞 D.host.E)`. Rewrite using `[X.Lam_split]`.

Use `sup_le (sup_le ?_ ?_) ?_` and prove the remaining obligations. Unfold `latSpanS`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, x, -, rfl⟩`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)))`.

Introduce `l hl`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span hl))`. Unfold `latSpanS`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, x, -, rfl⟩`.

Conclude with `Submodule.mem_sup_right (Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩))`. Conclude with `hL hz`. Take `⟨y12, hy12, y3, hy3, rfl⟩` from `Submodule.mem_sup.1 (hle hyL)`. Take `⟨y1, hy1, l, hl, rfl⟩` from `Submodule.mem_sup.1 hy12`. Take `⟨α, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy1`.

Take `⟨β, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy3`. Establish `hlW : ∀ c, (VS D).hT (X.eX c) l = 0 ∧ (VS D).hT (X.fY c) l = 0` using `(mem_Wb X).1 (span_Lb_le X hl)`. Establish `hα : ∀ c, α c = 0`. Introduce `c`. Use `(hy' c).2` as an intermediate fact.

Simplify using `[map_add, map_sum, map_smul, Ex.h_fe, X.ff, (hlW c).2, Finset.sum_ite_eq] at this`. Conclude with `this`. Establish `hβ : ∀ c, β c = 0`. Introduce `c`. Use `(hy' c).1` as an intermediate fact.

Simplify using `[map_add, map_sum, map_smul, X.ef, X.ee, (hlW c).1, Finset.sum_ite_eq] at this`. Conclude with `this`. Simplify using `only [hα, hβ, zero_smul, Finset.sum_const_zero, zero_add, add_zero]`. Conclude with `hl`.
-/
theorem span_Lb : Submodule.span D.host.E (X.Lb : Set (VS D).V) = Wb X := by
  refine le_antisymm (span_Lb_le X) fun y hy => ?_
  have hy' := (mem_Wb X).1 hy
  have htop : Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) = ⊤ := (VS D).standardTuple_isLattice.span_eq_top
  have hyL : y ∈ Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) := by rw [htop]; trivial
  have hle : Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) ≤
      Submodule.span D.host.E (Set.range X.eX) ⊔ Submodule.span D.host.E (X.Lb : Set (VS D).V) ⊔
        Submodule.span D.host.E (Set.range X.fY) := by
    rw [Submodule.span_le]
    intro z hz
    set T := Submodule.span D.host.E (Set.range X.eX) ⊔ Submodule.span D.host.E (X.Lb : Set (VS D).V) ⊔
        Submodule.span D.host.E (Set.range X.fY) with hT
    have hL : (VS D).L0 ≤ T.restrictScalars (𝓞 D.host.E) := by
      rw [X.Lam_split]
      refine sup_le (sup_le ?_ ?_) ?_
      · unfold latSpanS
        rw [Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        exact Submodule.mem_sup_left (Submodule.mem_sup_left
          (Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)))
      · intro l hl
        exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span hl))
      · unfold latSpanS
        rw [Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        exact Submodule.mem_sup_right (Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩))
    exact hL hz
  obtain ⟨y12, hy12, y3, hy3, rfl⟩ := Submodule.mem_sup.1 (hle hyL)
  obtain ⟨y1, hy1, l, hl, rfl⟩ := Submodule.mem_sup.1 hy12
  obtain ⟨α, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy1
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy3
  have hlW : ∀ c, (VS D).hT (X.eX c) l = 0 ∧ (VS D).hT (X.fY c) l = 0 := (mem_Wb X).1 (span_Lb_le X hl)
  have hα : ∀ c, α c = 0 := by
    intro c
    have := (hy' c).2
    simp [map_add, map_sum, map_smul, Ex.h_fe, X.ff, (hlW c).2, Finset.sum_ite_eq] at this
    exact this
  have hβ : ∀ c, β c = 0 := by
    intro c
    have := (hy' c).1
    simp [map_add, map_sum, map_smul, X.ef, X.ee, (hlW c).1, Finset.sum_ite_eq] at this
    exact this
  simp only [hα, hβ, zero_smul, Finset.sum_const_zero, zero_add, add_zero]
  exact hl

/- English proof (translation)
Rewrite using `[span_Lb, finrank_Wb]`.
-/
theorem finrank_span_Lb : Module.finrank D.host.E (Submodule.span D.host.E (X.Lb : Set (VS D).V)) = D.R.k + 1 := by
  rw [span_Lb, finrank_Wb]

end Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans
