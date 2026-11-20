import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfTrivial

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

/- English proof (translation)
Establish `hc : (⊤ : X.Opens) ≤ iSup U` using `hU.ge`. Take `⟨s, hs, -⟩` from `X.sheaf.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hc (fun i => (r i).val) (fun i j => congrArg Units.val (hr i j))`. Take `⟨s', hs', -⟩` from `X.sheaf.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hc (fun i => ((r i)⁻¹).val) (fun i j => congrArg Units.val (show res (inf_le_left : U i ⊓ U j ≤ U i) (r i)⁻¹ = res (inf_le_right : U i ⊓ U j ≤ U j) (r j)⁻¹ by rw [map_inv, map_inv, hr i j]))`. Establish `hss : s * s' = 1`. Use `X.sheaf.eq_of_locally_eq' U ⊤ (fun _ => homOfLE le_top) hc _ _ fun i => ?_` and prove the remaining obligations.

Establish `h1` using `hs i`. Establish `h2` using `hs' i`. Rewrite using `[map_mul, map_one, h1, h2]`. Conclude with `(r i).mul_inv`. Conclude with `⟨Units.mkOfMulEqOne (s : Γ(X, ⊤)) s' hss, fun i => Units.ext (hs i)⟩`.
-/
private theorem exists_global_unit_of_compatible_of_iSup_eq {X : Scheme.{0}} {J : Type} (U : J → X.Opens) (hU : ⨆ i, U i = ⊤)
    (r : ∀ i, Γ(X, U i)ˣ)
    (hr : ∀ i j, res (inf_le_left : U i ⊓ U j ≤ U i) (r i) = res (inf_le_right : U i ⊓ U j ≤ U j) (r j)) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ i, res (le_top : U i ≤ ⊤) u = r i := by
  have hc : (⊤ : X.Opens) ≤ iSup U := hU.ge
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hc
    (fun i => (r i).val) (fun i j => congrArg Units.val (hr i j))
  obtain ⟨s', hs', -⟩ := X.sheaf.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hc
    (fun i => ((r i)⁻¹).val)
    (fun i j => congrArg Units.val (show res (inf_le_left : U i ⊓ U j ≤ U i) (r i)⁻¹ =
      res (inf_le_right : U i ⊓ U j ≤ U j) (r j)⁻¹ by rw [map_inv, map_inv, hr i j]))
  have hss : s * s' = 1 := by
    refine X.sheaf.eq_of_locally_eq' U ⊤ (fun _ => homOfLE le_top) hc _ _ fun i => ?_
    have h1 := hs i
    have h2 := hs' i
    rw [map_mul, map_one, h1, h2]
    exact (r i).mul_inv
  exact ⟨Units.mkOfMulEqOne (s : Γ(X, ⊤)) s' hss, fun i => Units.ext (hs i)⟩

/- English proof (translation)
The claim follows from `Units.ext (Y.sheaf.eq_of_locally_eq' V W (fun i => homOfLE (hVW i)) hW _ _ fun i => congrArg Units.val (h i))`.
-/
private theorem units_eq_of_res_eq_of_le_iSup {Y : Scheme.{0}} {J : Type} (V : J → Y.Opens) (W : Y.Opens) (hVW : ∀ i, V i ≤ W)
    (hW : W ≤ ⨆ i, V i) (s t : Γ(Y, W)ˣ) (h : ∀ i, res (hVW i) s = res (hVW i) t) : s = t :=
  Units.ext (Y.sheaf.eq_of_locally_eq' V W (fun i => homOfLE (hVW i)) hW _ _ fun i => congrArg Units.val (h i))

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(f.app U ≫ Y.presheaf.map (homOfLE h2).op).hom x.val = (X.presheaf.map (homOfLE hU).op ≫ f.app U' ≫ Y.presheaf.map (homOfLE h1).op).hom x.val`. Rewrite using `[Scheme.Hom.naturality_assoc, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
private theorem app_rs_eq_rs_app' {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} (U' : X.Opens) (hU : U' ≤ U) {V : Y.Opens}
    (h1 : V ≤ f ⁻¹ᵁ U') (h2 : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h2 (pullU f U x) = res h1 (pullU f U' (res hU x)) := by
  apply Units.ext
  change (f.app U ≫ Y.presheaf.map (homOfLE h2).op).hom x.val =
    (X.presheaf.map (homOfLE hU).op ≫ f.app U' ≫ Y.presheaf.map (homOfLE h1).op).hom x.val
  rw [Scheme.Hom.naturality_assoc, ← Functor.map_comp]
  rfl

/- English proof (translation)
Rewrite `h` using `[Fintype.prod_unique, Fintype.prod_unique]`. Then use the resulting hypothesis.
-/
private theorem apply_default_eq_of_prod_eq_of_unique {K G : Type*} [Fintype K] [Unique K] [CommMonoid G] (f g : K → G)
    (h : ∏ k, f k = ∏ k, g k) : f default = g default := by
  rwa [Fintype.prod_unique, Fintype.prod_unique] at h

/- English proof (translation)
Establish `hcov : ⨆ q, (LB.div (M₀.pull φ) M).U q = ⊤`. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Establish `hx₀ : φ.base x ∈ (⨆ i, M₀.U i)` using `by rw [hM₀.cover]; trivial`. Establish `hx : x ∈ (⨆ j, M.U j)` using `by rw [hM.cover]; trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx₀`.

Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Use `TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => i, j), ?_⟩` and prove the remaining obligations. Conclude with `⟨Set.mem_iInter.2 fun _ => hi, hj⟩`. Take `⟨u, hu⟩` from `exists_global_unit_of_compatible_of_iSup_eq (LB.div (M₀.pull φ) M).U hcov (fun q => w₁.s q / w₂.s q) fun q q' => by`. Rewrite using `[map_div, map_div, g₁ q q', g₂ q q']`.

Conclude with `mul_div_mul_left_eq_div _ _ _`. Establish `hcovY : (eSec A) ⁻¹ᵁ (⊤ : A.left.Opens) ≤ ⨆ p, (LB.div ((M₀.pull φ).pull (eSec A)) (M.pull (eSec A))).U p`. Introduce `y _`. Establish `hx : (eSec A).base y ∈ (⨆ q, (LB.div (M₀.pull φ) M).U q)` using `by rw [hcov]; trivial`. Take `⟨q, hq⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`.

Use `TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => q.1, fun _ => q.2), ?_⟩` and prove the remaining obligations. Conclude with `⟨Set.mem_iInter.2 fun _ => hq.1, Set.mem_iInter.2 fun _ => hq.2⟩`. Establish `hc : pullU (eSec A) ⊤ u = 1`. Use `units_eq_of_res_eq_of_le_iSup _ _ (fun _ _ _ => by trivial) hcovY _ _ fun p => ?_` and prove the remaining obligations. Rewrite using `[map_one]`.

Establish `E` using `mul_right_cancel ((m₁ p).symm.trans (m₂ p))`. Simplify using `only [id_eq, LB.linCombIso, Fintype.prod_unique, zpow_one] at E`. Use `(app_rs_eq_rs_app' (eSec A) ((LB.div (M₀.pull φ) M).U (p.1 default, p.2 default)) le_top ?_ _ u).trans ?_` and prove the remaining obligations. Conclude with `le_inf (inf_le_left.trans (LB.wchart_le _ _ p.1 default)) (inf_le_right.trans (LB.wchart_le _ _ p.2 default))`. Apply the tactic sequence `refine (congrArg (fun z => res _ (pullU (eSec A) _ z)) (hu (p.1 default, p.2 default))).trans ?_ try dsimp only`.

Rewrite using `[map_div, map_div, div_eq_one]`. Conclude with `apply_default_eq_of_prod_eq_of_unique _ _ E`. Establish `hc' : (eSec A).appTop.hom (u : Γ(A.left, ⊤)) = 1` using `congrArg Units.val hc`. Take `⟨v, hv⟩` from `(hG S A hA).2 (u : Γ(A.left, ⊤))`. Establish `hw : eSec A ≫ A.hom = (𝟙_ (Over S)).hom`.

Conclude with `Over.w _`. Establish `key : (eSec A).appTop.hom (A.hom.appTop.hom v) = v`. Establish `h3 : (eSec A).appTop.hom (A.hom.appTop.hom v) = (eSec A ≫ A.hom).appTop.hom v`. Both sides reduce to the same expression. Rewrite using `[h3, hw]`.

Both sides reduce to the same expression. Establish `hv1 : v = 1` using `by rw [← key, hv]; exact hc'`. Establish `hu1 : u = 1` using `Units.ext (by rw [← hv, hv1, map_one, Units.val_one])`. Establish `hq : ∀ q, w₁.s q = w₂.s q` using `fun q => by`. Establish `h` using `hu q`.

Rewrite `h` using `[hu1, map_one]`. Conclude with `div_eq_one.1 h.symm`. Consider the cases of `w₁`. Consider the cases of `w₂`. Use `congr 1`.

Use function extensionality and compare the values at `q`. Conclude with `hq q`.
-/
theorem iso_unique_of_rig (hG : Out.GlobalFnsSt) {S X₀ : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    {M : LB A.left} {M₀ : LB X₀} (hM : M.IsLB) (hM₀ : M₀.IsLB) {φ : A.left ⟶ X₀}
    {w₁ w₂ : LB.Iso M (M₀.pull φ)} (g₁ : w₁.IsGen) (g₂ : w₂.IsGen) {a : LB.Gen (M.pull (eSec A))}
    {b : LB.Gen ((M₀.pull φ).pull (eSec A))}
    (m₁ : LB.Gen.Maps (LB.linCombIso w₁ (K := PUnit) (fun _ => eSec A) (fun _ => 1)) a b)
    (m₂ : LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec A) (fun _ => 1)) a b) : w₁ = w₂ := by
  have hcov : ⨆ q, (LB.div (M₀.pull φ) M).U q = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx₀ : φ.base x ∈ (⨆ i, M₀.U i) := by rw [hM₀.cover]; trivial
    have hx : x ∈ (⨆ j, M.U j) := by rw [hM.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx₀
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => i, j), ?_⟩
    exact ⟨Set.mem_iInter.2 fun _ => hi, hj⟩
  obtain ⟨u, hu⟩ := exists_global_unit_of_compatible_of_iSup_eq (LB.div (M₀.pull φ) M).U hcov (fun q => w₁.s q / w₂.s q) fun q q' => by
    rw [map_div, map_div, g₁ q q', g₂ q q']
    exact mul_div_mul_left_eq_div _ _ _
  have hcovY : (eSec A) ⁻¹ᵁ (⊤ : A.left.Opens) ≤
      ⨆ p, (LB.div ((M₀.pull φ).pull (eSec A)) (M.pull (eSec A))).U p := by
    intro y _
    have hx : (eSec A).base y ∈ (⨆ q, (LB.div (M₀.pull φ) M).U q) := by rw [hcov]; trivial
    obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => q.1, fun _ => q.2), ?_⟩
    exact ⟨Set.mem_iInter.2 fun _ => hq.1, Set.mem_iInter.2 fun _ => hq.2⟩
  have hc : pullU (eSec A) ⊤ u = 1 := by
    refine units_eq_of_res_eq_of_le_iSup _ _ (fun _ _ _ => by trivial) hcovY _ _ fun p => ?_
    rw [map_one]
    have E := mul_right_cancel ((m₁ p).symm.trans (m₂ p))
    simp only [id_eq, LB.linCombIso, Fintype.prod_unique, zpow_one] at E
    refine (app_rs_eq_rs_app' (eSec A) ((LB.div (M₀.pull φ) M).U (p.1 default, p.2 default)) le_top ?_ _ u).trans ?_
    · exact le_inf (inf_le_left.trans (LB.wchart_le _ _ p.1 default))
        (inf_le_right.trans (LB.wchart_le _ _ p.2 default))
    · refine (congrArg (fun z => res _ (pullU (eSec A) _ z)) (hu (p.1 default, p.2 default))).trans ?_
      try dsimp only
      rw [map_div, map_div, div_eq_one]
      exact apply_default_eq_of_prod_eq_of_unique _ _ E
  have hc' : (eSec A).appTop.hom (u : Γ(A.left, ⊤)) = 1 := congrArg Units.val hc
  obtain ⟨v, hv⟩ := (hG S A hA).2 (u : Γ(A.left, ⊤))
  have hw : eSec A ≫ A.hom = (𝟙_ (Over S)).hom := by
    exact Over.w _
  have key : (eSec A).appTop.hom (A.hom.appTop.hom v) = v := by
    have h3 : (eSec A).appTop.hom (A.hom.appTop.hom v) = (eSec A ≫ A.hom).appTop.hom v := by
      rfl
    rw [h3, hw]
    rfl
  have hv1 : v = 1 := by rw [← key, hv]; exact hc'
  have hu1 : u = 1 := Units.ext (by rw [← hv, hv1, map_one, Units.val_one])
  have hq : ∀ q, w₁.s q = w₂.s q := fun q => by
    have h := hu q
    rw [hu1, map_one] at h
    exact div_eq_one.1 h.symm
  cases w₁
  cases w₂
  congr 1
  funext q
  exact hq q

/- English proof (translation)
Introduce `E _ _ _ H D l c k _ bF a P _ oP φ he w₁ w₂ e h₁ h₂`. Take `⟨-, g₁, m₁, -⟩` from `h₁`. Take `⟨-, g₂, m₂, -⟩` from `h₂`. Conclude with `iso_unique_of_rig hG P.toPre.P.A P.toPre.P.isAb P.toPre.P.isLB a.D₀.P.isLB g₁ g₂ m₁ m₂`.
-/
theorem wTriv (hG : Out.GlobalFnsSt) : WTrivSt := by
  intro E _ _ _ H D l c k _ bF a P _ oP φ he w₁ w₂ e h₁ h₂
  obtain ⟨-, g₁, m₁, -⟩ := h₁
  obtain ⟨-, g₂, m₂, -⟩ := h₂
  exact iso_unique_of_rig hG P.toPre.P.A P.toPre.P.isAb P.toPre.P.isLB a.D₀.P.isLB g₁ g₂ m₁ m₂

/- English proof (translation)
The claim follows from `dataRigid_torsion_of_trivial (gammaTriv hBe hMo hF hK) (thetaTriv h1 h2 h3) (wTriv hG)`.
-/
theorem dataRigid_torsion (hG : Out.GlobalFnsSt) (hF : LatFinOrdSt) (hK : LatMinkowskiSt) (hBe : GammaBetaSt)
    (hMo : GammaModMSt) (h1 : ThetaFixMbSt) (h2 : ThetaWeilSt) (h3 : SerreAllSt) : DataRigidTorsion :=
  dataRigid_torsion_of_trivial (gammaTriv hBe hMo hF hK) (thetaTriv h1 h2 h3) (wTriv hG)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
