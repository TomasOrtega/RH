import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegOfValWOpen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCompTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

/- English proof (translation)
Establish `sc : spMap j ≫ spMap i = spMap (j.comp i)` using `(spMap_comp i j).symm`. Establish `gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p)` using `((pull_grp q).comp (pull_grp p)).congr sc rfl`. Establish `g₁` using `(isGen_iff _).1 p.w_gen`. Establish `g₂` using `(isGen_iff _).1 q.w_gen`. Take `⟨w, T⟩` from `Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB`.

Establish `hr` using `T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)`. Rewrite `hr` using `[sc]`. Establish `hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left` using `fun x => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))`. Take `⟨ψ', hv⟩` from `PullDegCancelTop.exists_psiOn_pull p`. Take `⟨g, hg'⟩ : ∃ g : (TK R'').left ⟶ (specOf i ⁻¹ᵁ p.W).toScheme, g ≫ (specOf i ⁻¹ᵁ p.W).ι = jK R'' ≫ specOf j` from `⟨IsOpenImmersion.lift _ _ (by`.

Introduce and unpack `y -`. Rewrite using `[Scheme.Opens.range_ι, hW]`. Use the proof step `trivial), IsOpenImmersion.lift_fac _ _ _⟩`. Establish `hg : (g ≫ (specOf i ∣_ p.W)) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i)`. Rewrite using `[Category.assoc, morphismRestrict_ι, ← Category.assoc, hg', Category.assoc]`.

Conclude with `congrArg (jK R'' ≫ ·) sc`. Take `⟨r, hr₁, hr₂, -⟩` from `PullDegCompData.exists_isPullDeg_of_valW D D'' p.psiW (g ≫ (specOf i ∣_ p.W)) hg gp w (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by`. Take `⟨J', hJ'⟩` from `DegPull.exists_good' D'.P.isLB z`. Establish `v₁` using `hv (q.xe x) _ g z J J' hJ hJ'`. Establish `v₂` using `PsiEvenPull.psi_pull q x (𝟙 _) z hJ' hJ''`.

Establish `ag : val (ψ'.psi (q.xe x)) g z J' = val (q.psiW.psi (q.xe x)) (𝟙 _ ≫ q.g) z J'` using `ArcSpecialise.psiOn_agree ψ' q.psiW _ _ _ (by rw [hg', Category.id_comp, q.g_comm]) hJ'`. Establish `hx : D''.xK x ≫ proj q = g ≫ (specOf i ⁻¹ᵁ p.W).ι ≫ (D'.c (q.xe x)).left` using `by show (jK R'' ≫ (D''.c x).left) ≫ proj q = _`. Rewrite using `[Category.assoc, q.c_pr, ← Category.assoc g, hg', Category.assoc]`. Establish `t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x)` using `(congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x))) (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))`. Express the relevant statement in the definitionally equal form `_ = (om q.w z J' J'' (𝟙 _ ≫ D''.xK x))⁻¹ * _ at v₂`.

Rewrite `v₁` using `[ag, v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t]`. Conclude with `v₁)`. Conclude with `⟨r, hr₁, hr₂⟩`.
-/
theorem exists_isPullDeg_comp_of_preimage {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'')
    (hW : specOf i ⁻¹ᵁ p.W = ⊤) :
    ∃ r : IsPullDeg (j.comp i) D D'', proj r = proj q ≫ proj p ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨ψ', hv⟩ := PullDegCancelTop.exists_psiOn_pull p
  obtain ⟨g, hg'⟩ : ∃ g : (TK R'').left ⟶ (specOf i ⁻¹ᵁ p.W).toScheme,
      g ≫ (specOf i ⁻¹ᵁ p.W).ι = jK R'' ≫ specOf j :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hg : (g ≫ (specOf i ∣_ p.W)) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg', Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, hr₁, hr₂, -⟩ := PullDegCompData.exists_isPullDeg_of_valW D D'' p.psiW (g ≫ (specOf i ∣_ p.W)) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := hv (q.xe x) _ g z J J' hJ hJ'
      have v₂ := PsiEvenPull.psi_pull q x (𝟙 _) z hJ' hJ''
      have ag : val (ψ'.psi (q.xe x)) g z J' = val (q.psiW.psi (q.xe x)) (𝟙 _ ≫ q.g) z J' :=
        ArcSpecialise.psiOn_agree ψ' q.psiW _ _ _ (by rw [hg', Category.id_comp, q.g_comm]) hJ'
      have hx : D''.xK x ≫ proj q = g ≫ (specOf i ⁻¹ᵁ p.W).ι ≫ (D'.c (q.xe x)).left := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = _
        rw [Category.assoc, q.c_pr, ← Category.assoc g, hg', Category.assoc]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om q.w z J' J'' (𝟙 _ ≫ D''.xK x))⁻¹ * _ at v₂
      rw [ag, v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, hr₁, hr₂⟩

/- English proof (translation)
Introduce `R R' R'' _ _ _ _ _ _ i j D D' D'' p q e`. Conclude with `exists_isPullDeg_comp_of_preimage p q (by rw [e]; rfl)`.
-/
theorem exists_isPullDeg_comp_top : ∀ {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D''), p.W = ⊤ → ∃ r : IsPullDeg (j.comp i) D D'', r.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (j.comp i)) = (q.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf j)) ≫ p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  intro R R' R'' _ _ _ _ _ _ i j D D' D'' p q e
  exact exists_isPullDeg_comp_of_preimage p q (by rw [e]; rfl)

end GlobalTheory.PullDegCompTop
