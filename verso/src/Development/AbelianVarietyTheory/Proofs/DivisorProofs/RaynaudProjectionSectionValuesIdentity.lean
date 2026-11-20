import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveQuasiCompactQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullUInjectiveOfFlatSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FourierDescent

/- English proof (translation)
Establish `h` using `gs_pull (𝟙 Z) p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom C)`. Rewrite `h` using `[Category.id_comp]`. Conclude with `h.symm`.
-/
theorem cst_eq_gs_scal {R : Type} [CommRing R] {Z : Scheme.{0}} (p : Z ⟶ Sp R) (z : Z) (C : R) :
    cst p z C = gs (𝟙 _) z ⊤ (scal p C) := by
  have h := gs_pull (𝟙 Z) p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom C)
  rw [Category.id_comp] at h
  exact h.symm

/- English proof (translation)
Introduce `R _ _ Q O _ _ _ oa Y k α σ σ' σ'' C hyp T x z J hJ`. Establish `hL` using `Q.P.isLB`. Establish `: Smooth Y.q.left` using `GlobalTheory.RayEv.Ray.smooth_q Y`. Establish `: Surjective Y.q.left` using `(GlobalTheory.RayEv.Ray.surjective_quasiCompact_q Y).1`. Establish `key : ∀ j : Fin 4 → Q.P.L.ι, σ'.f j = σ''.f j + constFn Q.P.A.hom ((LB.LinComb Q.P.L (DegPre.famφB Q α) (DegPre.famε k)).U j) C * σ.f j`.

Introduce `j`. Apply `GlobalTheory.EigenDescent.app_injective_of_flat_surjective Y.q.left` to reduce the goal to its premises. Apply `fn_ext` to reduce the goal to its premises. Introduce `y hy`. Rewrite using `[gs_pull (𝟙 _) Y.q.left y _ hy, gs_pull (𝟙 _) Y.q.left y _ hy, Category.id_comp]`.

Take `⟨J', hJ'⟩ : ∃ J', Good Q.P.L y J'` from `⟨fun ψ => (exists_chart hL (ψ y)).choose, fun ψ => (exists_chart hL (ψ y)).choose_spec⟩`. Establish `h` using `hyp y J' hJ'`. Establish `hm` using `hJ'.mem (DegPre.famφB Q α) Y.q.left`. Rewrite using `[gs_add _ _ _ hy, gs_mul _ _ _ hy, gs_constFn _ _ _ _ hy]`. Use `erw [sec_trans σ' _ y hy hm, sec_trans σ'' _ y hy hm, sec_trans σ _ y hy hm]`.

Rewrite using `[Over.w Y.q, cst_eq_gs_scal]`. Express the relevant statement in the definitionally equal form `_ * sval σ' Y.q.left y J' = _ * sval σ'' Y.q.left y J' + _ * (_ * sval σ Y.q.left y J')`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hm` using `hJ.mem (DegPre.famφB Q α) x.left`.

Express the relevant statement in the definitionally equal form `gs x.left z _ (σ'.f _) = gs x.left z _ (σ''.f _) + _ * gs x.left z _ (σ.f _)`. Rewrite using `[key]`. Use `erw [gs_add _ _ _ hm, gs_mul _ _ _ hm, gs_constFn _ _ _ _ hm]`. Rewrite using `[Over.w x, cst_eq_gs_scal]`. Both sides reduce to the same expression.
-/
theorem values_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α) (C : R), (∀ (y : Y.H.left) J, Good Q.P.L y J → sval σ' Y.q.left y J = sval σ'' Y.q.left y J + gs (𝟙 _) y ⊤ (scal Y.H.hom C) * sval σ Y.q.left y J) → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ' x.left z J = sval σ'' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom C) * sval σ x.left z J := by
  intro R _ _ Q O _ _ _ oa Y k α σ σ' σ'' C hyp T x z J hJ
  classical
  have hL := Q.P.isLB
  have : Smooth Y.q.left := GlobalTheory.RayEv.Ray.smooth_q Y
  have : Surjective Y.q.left := (GlobalTheory.RayEv.Ray.surjective_quasiCompact_q Y).1
  have key : ∀ j : Fin 4 → Q.P.L.ι, σ'.f j =
      σ''.f j + constFn Q.P.A.hom ((LB.LinComb Q.P.L (DegPre.famφB Q α) (DegPre.famε k)).U j) C * σ.f j := by
    intro j
    apply GlobalTheory.EigenDescent.app_injective_of_flat_surjective Y.q.left
    apply fn_ext
    intro y hy
    rw [gs_pull (𝟙 _) Y.q.left y _ hy, gs_pull (𝟙 _) Y.q.left y _ hy, Category.id_comp]
    obtain ⟨J', hJ'⟩ : ∃ J', Good Q.P.L y J' :=
      ⟨fun ψ => (exists_chart hL (ψ y)).choose, fun ψ => (exists_chart hL (ψ y)).choose_spec⟩
    have h := hyp y J' hJ'
    have hm := hJ'.mem (DegPre.famφB Q α) Y.q.left
    rw [gs_add _ _ _ hy, gs_mul _ _ _ hy, gs_constFn _ _ _ _ hy]
    erw [sec_trans σ' _ y hy hm, sec_trans σ'' _ y hy hm, sec_trans σ _ y hy hm]
    rw [Over.w Y.q, cst_eq_gs_scal]
    change _ * sval σ' Y.q.left y J' = _ * sval σ'' Y.q.left y J' + _ * (_ * sval σ Y.q.left y J')
    rw [h]
    ring
  have hm := hJ.mem (DegPre.famφB Q α) x.left
  change gs x.left z _ (σ'.f _) = gs x.left z _ (σ''.f _) + _ * gs x.left z _ (σ.f _)
  rw [key]
  erw [gs_add _ _ _ hm, gs_mul _ _ _ hm, gs_constFn _ _ _ _ hm]
  rw [Over.w x, cst_eq_gs_scal]
  rfl

end GlobalTheory.FourierDescent
