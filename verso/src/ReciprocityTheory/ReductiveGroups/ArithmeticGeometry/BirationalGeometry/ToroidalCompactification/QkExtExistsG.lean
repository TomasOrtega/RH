import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsGenVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.QkExtExistsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped Pointwise

/- English proof (translation)
Use `choose I hI using fun χ : Sp F ⟶ X => exists_chart hM (χ y)`. Conclude with `⟨I, hI⟩`.
-/
theorem good_pt {F : Type} [Field F] {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) (y : Sp F) : ∃ J, Good M y J := by
  choose I hI using fun χ : Sp F ⟶ X => exists_chart hM (χ y)
  exact ⟨I, hI⟩

/- English proof (translation)
Introduce `R _ _ D F F' _ _ _ _ f hf k p`. Establish `hj : spMap f ≫ jFK (R` using `R) F = jFK (R := R) F' := (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext hf))`. Set `ρ : TF (R` to `R) F' ⟶ TF (R := R) F := Over.homMk (spMap f) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hj))`. Take `⟨J, hJ⟩` from `good_pt D.P.isLB (default : PrimeSpectrum F')`. Take `⟨q, hy, hb, hv⟩` from `exists_qk (F := F') hJ (n := k) p.y (ρ ≫ p.g.b) _ (mult_gx ρ hJ p.g) fun χ => (gx_qk ρ hJ p χ).trans (Ex.ext rfl (congrArg (fun q => val (D.tau p.y χ) q _ J) (hj.trans (Category.id_comp _).symm)))`.

Use `⟨q, hy, congrArg (fun q => q.left) hb, fun χ => corr_pt D.P.isLB (fun U _ h => ?_) (q.g.isGen χ) (pullGen_isGen _ _ _ _ (p.g.isGen χ) _) hJ ((hv χ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)).symm)⟩` and prove the remaining obligations. Use `(prod_gt _ χ h).trans (Eq.trans ?_ (prod_gt p.g.b χ fun q => h (ρ.left ≫ q)).symm)` and prove the remaining obligations. Simplify using `only [← Over.comp_left, MonObj.comp_mul, comp_cP, MonObj.comp_one, hb]`.
-/
theorem qkExtExists_g : QkExtExistsSt := by
  intro R _ _ D F F' _ _ _ _ f hf k p
  have hj : spMap f ≫ jFK (R := R) F = jFK (R := R) F' := (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext hf))
  let ρ : TF (R := R) F' ⟶ TF (R := R) F := Over.homMk (spMap f) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hj))
  obtain ⟨J, hJ⟩ := good_pt D.P.isLB (default : PrimeSpectrum F')
  obtain ⟨q, hy, hb, hv⟩ := exists_qk (F := F') hJ (n := k) p.y (ρ ≫ p.g.b) _ (mult_gx ρ hJ p.g) fun χ =>
    (gx_qk ρ hJ p χ).trans (Ex.ext rfl (congrArg (fun q => val (D.tau p.y χ) q _ J) (hj.trans (Category.id_comp _).symm)))
  refine ⟨q, hy, congrArg (fun q => q.left) hb, fun χ => corr_pt D.P.isLB (fun U _ h => ?_) (q.g.isGen χ)
    (pullGen_isGen _ _ _ _ (p.g.isGen χ) _) hJ ((hv χ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)).symm)⟩
  refine (prod_gt _ χ h).trans (Eq.trans ?_ (prod_gt p.g.b χ fun q => h (ρ.left ≫ q)).symm)
  simp only [← Over.comp_left, MonObj.comp_mul, comp_cP, MonObj.comp_one, hb]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {k : Type} [Field k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF) {F : Type} [Field F] [IsAlgClosed F]
  [Algebra (FractionRing k) F]

/- English proof (translation)
Use `letI := H.starRing`. Establish `hM0 : 0 < l.M` using `by have := l.three_le; omega`. Set `r : c.F` to `⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩`. Set `z : c.F` to `⟨zeta l.A, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩`. Take `⟨-, I, -, -, hI⟩` from `a.geom F r z rfl rfl ((algebraMap (FractionRing k) F).comp (algebraMap k _)) rfl`.

Take `⟨x, hx⟩` from `I.onto _ hM0 q`. Establish `hv : star m • x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)` using `Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hm) Submodule.mem_top`. Take `⟨q₀, h₀⟩` from `qkExtExists_g k a.D₀ _ F (algebraMap _ F) (fun _ => rfl) _ (a.eta (star m • x))`. Take `⟨q', y', ⟨b', s'⟩, e'⟩` from `I.lin _ hM0 (star m) x`. Take `⟨z₁, y₁, g₁⟩` from `gx_equiv (𝟙 _) hJ hx`.

Take `⟨z₂, y₂, g₂⟩` from `gx_equiv (𝟙 _) hJ e'`. Take `⟨z₃, y₃, g₃⟩` from `gx_equiv (𝟙 _) hJ (hI _ hv q₀ h₀)`. Use `a.oa.onB.hom m` as an intermediate fact. Use `a.oa.onB.hom (star m)` as an intermediate fact. Establish `hr` using `a.oa.onB.rosati (star (star m))`.

Establish `hbal` using `a.oa.tau_bal (star (star m))`. Rewrite `hr`, `hbal` using `[star_star (star m)]`. Use `a.oa.onB.hom (star (star m))` as an intermediate fact. Take `⟨u, hu, u₀⟩` from `exists_ros hG a.D₀.P.isAb a.D₀.P.isLB _ _ hr`. Establish `C` using `isCub_cubV a.D₀.cub (T := TF (R := k) F) hJ`.

Establish `cf : ∀ (x : 𝓞 E) χ, cP a.D₀ (TF (R` using `k) F) (x • χ) = cP a.D₀ _ χ ≫ a.oa.onB.act x := fun x χ => by`. Rewrite using `[cP, a.oa.c_lin, ← Category.assoc]`. Both sides reduce to the same expression. Establish `ra` using `ros_add a.D₀.cub hG a.D₀.P.isAb _ _ u hu u₀ (T := TF (R := k) F) hJ`. Set `Ac : ∀ χ, Ex C (cP a.D₀ _ (star (star m) • χ)) →* Ex C (cP a.D₀ _ χ)` to `fun χ => MonoidHom.mk' (fun p => ⟨p.b ≫ a.oa.onB.act (star m), p.u * val₂ u y J (cP a.D₀ _ χ) p.b⟩) fun p p' => Ex.ext (MonObj.mul_comp _ _ _) (by`.

Establish `e` using `congrArg Additive.ofMul (ra p.b p'.b (cP a.D₀ _ χ)).2`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [Ex.mul_u, Ex.mul_b, cf, ofMul_mul, ofMul_inv] at e ⊢`. Take the linear combination `(norm := abel) e)`. Establish `A₁ : ∀ χ, Ac χ (gx (𝟙 _) hJ (I.ev l.M x).g _) = gx (𝟙 _) hJ q'.g χ` using `fun χ => Ex.ext (by show (𝟙 _ ≫ _) ≫ _ = 𝟙 _ ≫ _; rw [b', Category.assoc]) (by`.

Establish `e` using `(val_mul hJ _ _ _).symm.trans (val_corr hJ (s' u hu u₀ χ) (𝟙 _))`. Rewrite `e` using `[val_pull hJ, Category.id_comp]`. Use `show _ * val₂ u y J _ (𝟙 _ ≫ _) = _`. Rewrite using `[Category.id_comp]`. Conclude with `e)`.

Establish `A₂ : ∀ χ w, Ac χ (ix (𝟙 _) hJ w _) = ix (𝟙 _) hJ (star m • w) χ` using `fun χ w => Ex.ext (cf _ _).symm (by`. Set `κ : TF (R` to `k) F ⟶ TK k := Over.homMk (𝟙 _ ≫ jFK (R := k) F) (by rw [Category.id_comp]; rfl)`. Establish `e` using `(val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal u hu u₀ χ w) κ.left)`. Establish `e' : val (LB.pullGen a.D₀.P.L _ _ u (a.D₀.pt2 χ w)) κ.left y J = val₂ u y J (cP a.D₀ _ χ) (cP a.D₀ _ w)`. Rewrite using `[val_pull hJ, val₂, ← comp_cP a.D₀ κ, ← comp_cP a.D₀ κ w, ← comp_lift]`.

Both sides reduce to the same expression. Conclude with `(congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := k) F)) hJ _ _) e'.symm).trans (e.trans (tau_symm (𝟙 (TF (R := k) F)) hJ _ _)))`. Establish `key : ∀ χ, gx (𝟙 _) hJ q₀.g χ * ix (𝟙 _) hJ (z₃ - z₂ + star m • z₁) χ = Ac χ (gx (𝟙 _) hJ q.g _)` using `fun χ => by`. Establish `i` using `ix_add (𝟙 _) hJ a.bimult (z₃ - z₂) z₂ χ`. Rewrite `i` using `[sub_add_cancel]`.

Use `(g₃ χ).symm.trans (g₂ χ)` as an intermediate fact. Rewrite `this` using `[i, ← _root_.mul_assoc, mul_left_inj]`. Rewrite using `[g₁, map_mul, A₁, A₂, ix_add _ _ a.bimult, ← _root_.mul_assoc, this]`. Use `⟨_, hv, q₀, z₃ - z₂ + star m • z₁, h₀, ?_, ?_, fun hb χ => (key χ).trans (Ex.ext ?_ ?_)⟩` and prove the remaining obligations. Rewrite using `[y₁, smul_add (star m), ← y', smul_add, smul_sub, smul_comm (star m) l.M]`.

Take the linear combination `(norm := abel) y₂ - y₃`. Use `congrArg Ex.b (key 0)` as an intermediate fact. Conclude with `(congrArg (· * _) (Category.id_comp _).symm).trans (this.trans (congrArg (· ≫ _) (Category.id_comp _)))`. Use `show (𝟙 _ ≫ q.g.b) ≫ _ = 1`. Rewrite using `[Category.id_comp, hb, MonObj.one_comp]`.

Establish `e` using `(ra 1 1 (cP a.D₀ _ χ)).2`. Rewrite `e` using `[_root_.mul_one, MonObj.one_comp (a.oa.onB.act (star m)), C.face₃, C.face₃, _root_.mul_one, _root_.one_mul]`. Use `show val (q.g.s (star (star m) • χ)) _ y J * val₂ u y J _ (𝟙 _ ≫ q.g.b) = _`. Establish `e₁ : val₂ u y J (cP a.D₀ _ χ) (𝟙 _ ≫ q.g.b) = 1` using `by rw [Category.id_comp, hb, mul_eq_left.1 e.symm]`. Rewrite using `[e₁, _root_.mul_one, star_star]`.

Both sides reduce to the same expression.
-/
theorem exists_level (hG : GlobalFnsSt) {y : (TF (R := k) F).left} {J} (hJ : Good a.D₀.P.L y J) (q : QkPt a.D₀ F l.M)
    (m : 𝓞 E) (hm : m ∈ l.Mb) : letI := H.starRing
    ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ (q₀ : QkPt a.D₀ F l.M) (z : a.D₀.X),
      QkExt (algebraMap _ F) (a.eta v) q₀ ∧ q₀.y + l.M • z = star m • q.y ∧
      q₀.g.b * cP a.D₀ _ z = q.g.b ≫ a.oa.onB.act (star m) ∧ (q.g.b = 1 → ∀ χ, gx (𝟙 _) hJ q₀.g χ * ix (𝟙 _) hJ z χ =
        ⟨1, val (q.g.s (m • χ)) (𝟙 _) y J⟩) := by
  letI := H.starRing
  have hM0 : 0 < l.M := by have := l.three_le; omega
  let r : c.F := ⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩
  let z : c.F := ⟨zeta l.A, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩
  obtain ⟨-, I, -, -, hI⟩ := a.geom F r z rfl rfl ((algebraMap (FractionRing k) F).comp (algebraMap k _)) rfl
  obtain ⟨x, hx⟩ := I.onto _ hM0 q
  have hv : star m • x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hm) Submodule.mem_top
  obtain ⟨q₀, h₀⟩ := qkExtExists_g k a.D₀ _ F (algebraMap _ F) (fun _ => rfl) _ (a.eta (star m • x))
  obtain ⟨q', y', ⟨b', s'⟩, e'⟩ := I.lin _ hM0 (star m) x
  obtain ⟨z₁, y₁, g₁⟩ := gx_equiv (𝟙 _) hJ hx
  obtain ⟨z₂, y₂, g₂⟩ := gx_equiv (𝟙 _) hJ e'
  obtain ⟨z₃, y₃, g₃⟩ := gx_equiv (𝟙 _) hJ (hI _ hv q₀ h₀)
  have := a.oa.onB.hom m
  have := a.oa.onB.hom (star m)
  have hr := a.oa.onB.rosati (star (star m))
  have hbal := a.oa.tau_bal (star (star m))
  rw [star_star (star m)] at hr hbal
  have := a.oa.onB.hom (star (star m))
  obtain ⟨u, hu, u₀⟩ := exists_ros hG a.D₀.P.isAb a.D₀.P.isLB _ _ hr
  have C := isCub_cubV a.D₀.cub (T := TF (R := k) F) hJ
  have cf : ∀ (x : 𝓞 E) χ, cP a.D₀ (TF (R := k) F) (x • χ) = cP a.D₀ _ χ ≫ a.oa.onB.act x := fun x χ => by
    rw [cP, a.oa.c_lin, ← Category.assoc]; rfl
  have ra := ros_add a.D₀.cub hG a.D₀.P.isAb _ _ u hu u₀ (T := TF (R := k) F) hJ
  let Ac : ∀ χ, Ex C (cP a.D₀ _ (star (star m) • χ)) →* Ex C (cP a.D₀ _ χ) := fun χ => MonoidHom.mk'
    (fun p => ⟨p.b ≫ a.oa.onB.act (star m), p.u * val₂ u y J (cP a.D₀ _ χ) p.b⟩) fun p p' =>
      Ex.ext (MonObj.mul_comp _ _ _) (by
        have e := congrArg Additive.ofMul (ra p.b p'.b (cP a.D₀ _ χ)).2
        apply Additive.ofMul.injective
        simp only [Ex.mul_u, Ex.mul_b, cf, ofMul_mul, ofMul_inv] at e ⊢
        linear_combination (norm := abel) e)
  have A₁ : ∀ χ, Ac χ (gx (𝟙 _) hJ (I.ev l.M x).g _) = gx (𝟙 _) hJ q'.g χ := fun χ =>
    Ex.ext (by show (𝟙 _ ≫ _) ≫ _ = 𝟙 _ ≫ _; rw [b', Category.assoc]) (by
      have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (s' u hu u₀ χ) (𝟙 _))
      rw [val_pull hJ, Category.id_comp] at e
      show _ * val₂ u y J _ (𝟙 _ ≫ _) = _
      rw [Category.id_comp]; exact e)
  have A₂ : ∀ χ w, Ac χ (ix (𝟙 _) hJ w _) = ix (𝟙 _) hJ (star m • w) χ := fun χ w => Ex.ext (cf _ _).symm (by
    let κ : TF (R := k) F ⟶ TK k := Over.homMk (𝟙 _ ≫ jFK (R := k) F) (by rw [Category.id_comp]; rfl)
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal u hu u₀ χ w) κ.left)
    have e' : val (LB.pullGen a.D₀.P.L _ _ u (a.D₀.pt2 χ w)) κ.left y J = val₂ u y J (cP a.D₀ _ χ) (cP a.D₀ _ w) := by
      rw [val_pull hJ, val₂, ← comp_cP a.D₀ κ, ← comp_cP a.D₀ κ w, ← comp_lift]; rfl
    exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := k) F)) hJ _ _) e'.symm).trans
      (e.trans (tau_symm (𝟙 (TF (R := k) F)) hJ _ _)))
  have key : ∀ χ, gx (𝟙 _) hJ q₀.g χ * ix (𝟙 _) hJ (z₃ - z₂ + star m • z₁) χ = Ac χ (gx (𝟙 _) hJ q.g _) := fun χ => by
    have i := ix_add (𝟙 _) hJ a.bimult (z₃ - z₂) z₂ χ
    rw [sub_add_cancel] at i
    have := (g₃ χ).symm.trans (g₂ χ)
    rw [i, ← _root_.mul_assoc, mul_left_inj] at this
    rw [g₁, map_mul, A₁, A₂, ix_add _ _ a.bimult, ← _root_.mul_assoc, this]
  refine ⟨_, hv, q₀, z₃ - z₂ + star m • z₁, h₀, ?_, ?_, fun hb χ => (key χ).trans (Ex.ext ?_ ?_)⟩
  · rw [y₁, smul_add (star m), ← y', smul_add, smul_sub, smul_comm (star m) l.M]
    linear_combination (norm := abel) y₂ - y₃
  · have := congrArg Ex.b (key 0)
    exact (congrArg (· * _) (Category.id_comp _).symm).trans (this.trans (congrArg (· ≫ _) (Category.id_comp _)))
  · show (𝟙 _ ≫ q.g.b) ≫ _ = 1
    rw [Category.id_comp, hb, MonObj.one_comp]
  · have e := (ra 1 1 (cP a.D₀ _ χ)).2
    rw [_root_.mul_one, MonObj.one_comp (a.oa.onB.act (star m)), C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    show val (q.g.s (star (star m) • χ)) _ y J * val₂ u y J _ (𝟙 _ ≫ q.g.b) = _
    have e₁ : val₂ u y J (cP a.D₀ _ χ) (𝟙 _ ≫ q.g.b) = 1 := by rw [Category.id_comp, hb, mul_eq_left.1 e.symm]
    rw [e₁, _root_.mul_one, star_star]; rfl

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
