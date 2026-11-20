import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantTangentBasisRaynaudExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FstGenericAppInjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.RayFlatDesc

/- English proof (translation)
Simplify using `only [gs, dif_pos h, map_sub]`.
-/
theorem gs_sub_of {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  simp only [gs, dif_pos h, map_sub]

/- English proof (translation)
Apply the tactic sequence `unfold gs; split_ifs <;> simp`.
-/
theorem gs_zero_of {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

/- English proof (translation)
Introduce `R _ _ Q O _ _ _ oa Y k ρ τ a b H Z r z J hJ`. Use `GlobalTheory.RayTan.smooth_H R Q O oa Y` as an intermediate fact. Establish `hL : Q.P.L.IsLB` using `Q.P.isLB`. Establish `key : ∀ j : Fin 1 → Q.P.L.ι, (Y.H.left.presheaf.map (homOfLE le_top).op).hom (scal Y.H.hom a) * ρ.f j - (Y.H.left.presheaf.map (homOfLE le_top).op).hom (scal Y.H.hom b) * τ.f j = 0`. Introduce `j`.

Apply `GlobalTheory.Mum.fst_generic_app_injective Y.H.hom _` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply `fn_ext` to reduce the goal to its premises. Introduce `y hy`. Establish `hy' : pullback.fst Y.H.hom (jK R) y ∈ (LB.LinComb Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ))).U j` using `hy`.

Establish `hw : pullback.fst Y.H.hom (jK R) y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j` using `hy`. Take `⟨J', hJ', e⟩` from `exists_good Q.P.L hL y (fun _ : Unit => pullback.fst Y.H.hom (jK R) ≫ Y.q.left) (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hw 0)`. Establish `ej : ∀ i : Fin 1, J' (pullback.fst Y.H.hom (jK R) ≫ Y.q.left) = j i` using `fun i => by`. Rewrite using `[Subsingleton.elim i 0]`. Conclude with `e ()`.

Establish `h1` using `H _ (pullback.snd _ _) (pullback.fst _ _) pullback.condition y J' hJ'`. Rewrite `h1` using `[sval_of ρ _ y J' j ej, sval_of τ _ y J' j ej]`. Rewrite using `[gs_pull (𝟙 _) (pullback.fst Y.H.hom (jK R)) y _ hy', Category.id_comp, gs_zero_of _ _ _, gs_sub_of _ _ _ hy', gs_mul _ _ _ hy', gs_mul _ _ _ hy', gs_res _ _ _ hy', gs_res _ _ _ hy']`. Conclude with `sub_eq_zero.2 h1`. Establish `hm : r z ∈ (LB.LinComb Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ))).U (fun _ => J (r ≫ Y.q.left))` using `Set.mem_iInter.2 fun _ => hJ (r ≫ Y.q.left)`.

Establish `e` using `congrArg (gs r z _) (key fun _ => J (r ≫ Y.q.left))`. Rewrite `e` using `[gs_sub_of _ _ _ hm, gs_mul _ _ _ hm, gs_mul _ _ _ hm, gs_res _ _ _ hm, gs_res _ _ _ hm, gs_zero_of _ _ _, sub_eq_zero]`. Rewrite using `[sval_of ρ r z J _ (fun _ => rfl), sval_of τ r z J _ (fun _ => rfl)]`. Conclude with `e`.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (ρ τ : SecM Y.q.left Q.P.L k) (a b : R), (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (r : Z ⟶ Y.H.left), r ≫ Y.H.hom = g ≫ jK R → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J := by
  intro R _ _ Q O _ _ _ oa Y k ρ τ a b H Z r z J hJ
  have := GlobalTheory.RayTan.smooth_H R Q O oa Y
  have hL : Q.P.L.IsLB := Q.P.isLB
  have key : ∀ j : Fin 1 → Q.P.L.ι,
      (Y.H.left.presheaf.map (homOfLE le_top).op).hom (scal Y.H.hom a) * ρ.f j -
        (Y.H.left.presheaf.map (homOfLE le_top).op).hom (scal Y.H.hom b) * τ.f j = 0 := by
    intro j
    apply GlobalTheory.Mum.fst_generic_app_injective Y.H.hom _
    rw [map_zero]
    apply fn_ext
    intro y hy
    have hy' : pullback.fst Y.H.hom (jK R) y ∈
        (LB.LinComb Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ))).U j := hy
    have hw : pullback.fst Y.H.hom (jK R) y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j := hy
    obtain ⟨J', hJ', e⟩ := exists_good Q.P.L hL y (fun _ : Unit => pullback.fst Y.H.hom (jK R) ≫ Y.q.left)
      (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hw 0)
    have ej : ∀ i : Fin 1, J' (pullback.fst Y.H.hom (jK R) ≫ Y.q.left) = j i := fun i => by
      rw [Subsingleton.elim i 0]; exact e ()
    have h1 := H _ (pullback.snd _ _) (pullback.fst _ _) pullback.condition y J' hJ'
    rw [sval_of ρ _ y J' j ej, sval_of τ _ y J' j ej] at h1
    rw [gs_pull (𝟙 _) (pullback.fst Y.H.hom (jK R)) y _ hy', Category.id_comp, gs_zero_of _ _ _,
      gs_sub_of _ _ _ hy', gs_mul _ _ _ hy', gs_mul _ _ _ hy', gs_res _ _ _ hy', gs_res _ _ _ hy']
    exact sub_eq_zero.2 h1
  have hm : r z ∈ (LB.LinComb Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ))).U
      (fun _ => J (r ≫ Y.q.left)) :=
    Set.mem_iInter.2 fun _ => hJ (r ≫ Y.q.left)
  have e := congrArg (gs r z _) (key fun _ => J (r ≫ Y.q.left))
  rw [gs_sub_of _ _ _ hm, gs_mul _ _ _ hm, gs_mul _ _ _ hm, gs_res _ _ _ hm, gs_res _ _ _ hm, gs_zero_of _ _ _,
    sub_eq_zero] at e
  rw [sval_of ρ r z J _ (fun _ => rfl), sval_of τ r z J _ (fun _ => rfl)]
  exact e

end GlobalTheory.RayFlatDesc
