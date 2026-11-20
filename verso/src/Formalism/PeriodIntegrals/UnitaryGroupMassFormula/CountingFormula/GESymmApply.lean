import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowLatticeMassHolds

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Form

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

/- English proof (translation)
Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Rewrite using `[hWb_mk, hWb_mk]`. Conclude with `PI.ScalarPairDr.W.hT_swap _ _ _`.
-/
theorem hWb_swap (x y : WbQ D F0) : hWb D F0 y x = star (hWb D F0 x y) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [hWb_mk, hWb_mk]
  exact PI.ScalarPairDr.W.hT_swap _ _ _

/- English proof (translation)
Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Use `show (b : (VS D).V) ∈ F0.X`. Establish `h2 : (b : (VS D).V) ∈ orth (VS D) (orth (VS D) F0.X)`. Rewrite using `[PI.ScalarPairDr.W.mem_orth]`.

Introduce `x hx`. Rewrite `hx` using `[← perpS_eq_orth]`. Establish `h3` using `hy (Submodule.Quotient.mk ⟨x, hx⟩)`. Rewrite `h3` using `[hWb_mk]`. Then use the resulting hypothesis. Rewrite `h2` using `[PI.ScalarPairDr.W.orth_orth]`.

Conclude with `h2`.
-/
theorem hWb_sepR (y : WbQ D F0) (hy : ∀ x, hWb D F0 x y = 0) : y = 0 := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  show (b : (VS D).V) ∈ F0.X
  have h2 : (b : (VS D).V) ∈ orth (VS D) (orth (VS D) F0.X) := by
    rw [PI.ScalarPairDr.W.mem_orth]
    intro x hx
    rw [← perpS_eq_orth] at hx
    have h3 := hy (Submodule.Quotient.mk ⟨x, hx⟩)
    rwa [hWb_mk] at h3
  rw [PI.ScalarPairDr.W.orth_orth] at h2
  exact h2

/- English proof (translation)
Use `sub_eq_zero.1 (hWb_sepR D F0 (x - y) (fun a => ?_))` and prove the remaining obligations. Rewrite using `[map_sub, h a, sub_self]`.
-/
theorem hWb_eq_of (x y : WbQ D F0) (h : ∀ a, hWb D F0 a x = hWb D F0 a y) : x = y := by
  refine sub_eq_zero.1 (hWb_sepR D F0 (x - y) (fun a => ?_))
  rw [map_sub, h a, sub_self]

/- English proof (translation)
Set `b` to `Module.finBasis D.host.E (WbQ D F0)`. Set `M : WbQ D F0 →ₗ[D.host.E] (Fin (Module.finrank D.host.E (WbQ D F0)) → D.host.E)` to `LinearMap.pi (fun i => hWb D F0 (b i))`. Establish `hMinj : Function.Injective M`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`.

Establish `hy' : ∀ i, hWb D F0 (b i) y = 0` using `fun i => congrFun hy i`. Apply `hWb_sepR D F0 y` to reduce the goal to its premises. Introduce `a`. Rewrite using `[← b.sum_repr a]`. Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy', smul_zero, Finset.sum_const_zero]`.

Establish `hMsurj : Function.Surjective M` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hMinj`. Take `⟨Me, hMe⟩ : ∃ Me : WbQ D F0 ≃ₗ[D.host.E] (Fin (Module.finrank D.host.E (WbQ D F0)) → D.host.E), ∀ x, Me x = M x` from `⟨LinearEquiv.ofBijective M ⟨hMinj, hMsurj⟩, fun x => rfl⟩`. Set `g : (VS D).V →ₗ[D.host.E] (Fin (Module.finrank D.host.E (WbQ D F0)) → D.host.E)` to `LinearMap.pi (fun i => (VS D).hT (sE (b i) : (VS D).V))`. Use `⟨Me.symm.toLinearMap ∘ₗ g, fun a v => ?_⟩` and prove the remaining obligations. Establish `key : ∀ i, hWb D F0 (b i) (Me.symm (g v)) = (VS D).hT (sE (b i) : (VS D).V) v`.

Introduce `i`. Establish `h` using `hMe (Me.symm (g v))`. Rewrite `h` using `[Me.apply_symm_apply]`. Conclude with `(congrFun h i).symm`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`.

Rewrite using `[← b.sum_repr a]`. Simplify using `only [map_sum, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, Submodule.coe_smul, key]`.
-/
theorem exists_u (sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X) :
    ∃ u : (VS D).V →ₗ[D.host.E] WbQ D F0,
      ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v := by
  classical
  let b := Module.finBasis D.host.E (WbQ D F0)
  let M : WbQ D F0 →ₗ[D.host.E] (Fin (Module.finrank D.host.E (WbQ D F0)) → D.host.E) :=
    LinearMap.pi (fun i => hWb D F0 (b i))
  have hMinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : ∀ i, hWb D F0 (b i) y = 0 := fun i => congrFun hy i
    apply hWb_sepR D F0 y
    intro a
    rw [← b.sum_repr a]
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy',
      smul_zero, Finset.sum_const_zero]
  have hMsurj : Function.Surjective M :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hMinj
  obtain ⟨Me, hMe⟩ : ∃ Me : WbQ D F0 ≃ₗ[D.host.E] (Fin (Module.finrank D.host.E (WbQ D F0)) → D.host.E),
      ∀ x, Me x = M x := ⟨LinearEquiv.ofBijective M ⟨hMinj, hMsurj⟩, fun x => rfl⟩
  let g : (VS D).V →ₗ[D.host.E] (Fin (Module.finrank D.host.E (WbQ D F0)) → D.host.E) :=
    LinearMap.pi (fun i => (VS D).hT (sE (b i) : (VS D).V))
  refine ⟨Me.symm.toLinearMap ∘ₗ g, fun a v => ?_⟩
  have key : ∀ i, hWb D F0 (b i) (Me.symm (g v)) = (VS D).hT (sE (b i) : (VS D).V) v := by
    intro i
    have h := hMe (Me.symm (g v))
    rw [Me.apply_symm_apply] at h
    exact (congrFun h i).symm
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← b.sum_repr a]
  simp only [map_sum, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, map_smul, Submodule.coe_smul, key]

end Form

section Gamma

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def gF (sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X) (u : (VS D).V →ₗ[D.host.E] WbQ D F0)
    (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id + (perpS (VS D) F0.X).subtype ∘ₗ sE ∘ₗ
    ((σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) - LinearMap.id) ∘ₗ u

variable {D F0}
variable {sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X} {u : (VS D).V →ₗ[D.host.E] WbQ D F0}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gF_apply (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) (v : (VS D).V) :
    gF D F0 sE u σ v = v + (sE (σ (u v) - u v) : (VS D).V) := by
  rfl

/- English proof (translation)
Apply `hWb_eq_of D F0` to reduce the goal to its premises. Introduce `a`. Rewrite using `[hu]`. Use `conv_rhs => rw [← hsE a]`. Rewrite using `[hWb_mk]`.
-/
theorem u_perp (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (y : perpS (VS D) F0.X) :
    u y = Submodule.Quotient.mk y := by
  apply hWb_eq_of D F0
  intro a
  rw [hu]
  conv_rhs => rw [← hsE a]
  rw [hWb_mk]

/- English proof (translation)
Rewrite using `[u_perp hsE hu (sE b), hsE b]`.
-/
theorem u_sE (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (b : WbQ D F0) :
    u (sE b : (VS D).V) = b := by
  rw [u_perp hsE hu (sE b), hsE b]

/- English proof (translation)
Apply `hWb_sepR D F0` to reduce the goal to its premises. Introduce `a`. Rewrite using `[hu]`. Conclude with `hT_perp_X D F0 (sE a).2 hx`.
-/
theorem u_X (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) {x : (VS D).V} (hx : x ∈ F0.X) :
    u x = 0 := by
  apply hWb_sepR D F0
  intro a
  rw [hu]
  exact hT_perp_X D F0 (sE a).2 hx

/- English proof (translation)
Rewrite using `[gF_apply, map_add, u_sE hsE hu]`. Normalize the expressions using the abelian group laws.
-/
theorem u_gF (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0)
    (v : (VS D).V) : u (gF D F0 sE u σ v) = σ (u v) := by
  rw [gF_apply, map_add, u_sE hsE hu]
  abel

/- English proof (translation)
Rewrite using `[gF_apply σ.symm (gF D F0 sE u σ v), u_gF hsE hu σ v, LinearEquiv.symm_apply_apply, gF_apply σ v, show u v - σ (u v) = -(σ (u v) - u v) by abel, map_neg, Submodule.coe_neg, add_neg_cancel_right]`.
-/
theorem gF_symm (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0)
    (v : (VS D).V) : gF D F0 sE u σ.symm (gF D F0 sE u σ v) = v := by
  rw [gF_apply σ.symm (gF D F0 sE u σ v), u_gF hsE hu σ v, LinearEquiv.symm_apply_apply, gF_apply σ v,
    show u v - σ (u v) = -(σ (u v) - u v) by abel, map_neg, Submodule.coe_neg, add_neg_cancel_right]

def gE (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) :
    (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (gF D F0 sE u σ) (gF D F0 sE u σ.symm)
    (by
      ext v
      have := gF_symm hsE hu σ.symm v
      rwa [LinearEquiv.symm_symm] at this)
    (by
      ext v
      exact gF_symm hsE hu σ v)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gE_symm_apply (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0)
    (v : (VS D).V) : (gE hsE hu σ).symm v = gF D F0 sE u σ.symm v := rfl

/- English proof (translation)
Rewrite using `[gF_apply, gF_apply]`. Establish `h1 : ∀ c x, (VS D).hT x (sE c : (VS D).V) = hWb D F0 (u x) c`. Introduce `c x`. Rewrite using `[PI.ScalarPairDr.W.hT_swap (VS D) (sE c : (VS D).V) x, ← hu, ← hWb_swap D F0 c (u x)]`. Establish `h2 : ∀ c x, (VS D).hT (sE c : (VS D).V) x = hWb D F0 c (u x)` using `fun c x => (hu c x).symm`.

Establish `h3 : ∀ c c', (VS D).hT (sE c : (VS D).V) (sE c' : (VS D).V) = hWb D F0 c c'`. Introduce `c c'`. Rewrite using `[h2, u_sE hsE hu]`. Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[h3, h1, h2]`.

Simplify using `only [map_sub, LinearMap.sub_apply, hσ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gF_isom (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0)
    (hσ : ∀ x y, hWb D F0 (σ x) (σ y) = hWb D F0 x y) (v w : (VS D).V) :
    (VS D).hT (gF D F0 sE u σ v) (gF D F0 sE u σ w) = (VS D).hT v w := by
  rw [gF_apply, gF_apply]
  have h1 : ∀ c x, (VS D).hT x (sE c : (VS D).V) = hWb D F0 (u x) c := by
    intro c x
    rw [PI.ScalarPairDr.W.hT_swap (VS D) (sE c : (VS D).V) x, ← hu, ← hWb_swap D F0 c (u x)]
  have h2 : ∀ c x, (VS D).hT (sE c : (VS D).V) x = hWb D F0 c (u x) := fun c x => (hu c x).symm
  have h3 : ∀ c c', (VS D).hT (sE c : (VS D).V) (sE c' : (VS D).V) = hWb D F0 c c' := by
    intro c c'
    rw [h2, u_sE hsE hu]
  simp only [map_add, LinearMap.add_apply]
  rw [h3, h1, h2]
  simp only [map_sub, LinearMap.sub_apply, hσ]
  ring

end Gamma

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf
