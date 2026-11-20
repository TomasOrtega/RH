import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabMapCubical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqOfDominantGeometricPointsOfUnramified
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj

namespace ObjRigid

/- English proof (translation)
Use `unit_ext fun p _ => ?_` and prove the remaining obligations. Take `⟨V, hpV, ⟨θx₀, θy₀, hx₀, hy₀⟩, hall₀⟩` from `h₀ p`. Take `⟨V', hpV', -, hall⟩` from `h p`. Choose the witnesses or unpack the hypotheses as in `rfl : V = V' := by`. Use extensionality with `q`.

Rewrite using `[Subsingleton.elim q p]`. Conclude with `⟨fun _ => hpV', fun _ => hpV⟩`. Establish `hp` using `isGrpPullback_of_iso θ`. Establish `hτ : 𝟙 _ ≫ (Out.overRes (T` using `T) V).hom = (Out.overRes (T := T) V).hom ≫ 𝟙 S := by`. Rewrite using `[Category.id_comp, Category.comp_id]`.

Establish `mvx : 𝟙 _ ≫ θx₀.pt.left = (Out.overResι V ≫ x).left ≫ θ.hom.left`. Rewrite using `[hx₀, Category.id_comp, ← Over.comp_left, Category.assoc]`. Establish `mvy : 𝟙 _ ≫ θy₀.pt.left = (Out.overResι V ≫ y).left ≫ θ.hom.left`. Rewrite using `[hy₀, Category.id_comp, ← Over.comp_left, Category.assoc]`. Take `⟨θx, hθx, mx⟩` from `exists_theta_move hp (𝟙 _) hτ hL hL w hw k _ θx₀ mvx`.

Take `⟨θy, hθy, my⟩` from `exists_theta_move hp (𝟙 _) hτ hL hL w hw k _ θy₀ mvy`. Establish `hm` using `commIsOf_move hp (𝟙 _) hτ hL hL w k θx₀ θy₀ θx θy (by rw [hθx]; exact mvx) (by rw [hθy]; exact mvy) mx my (Out.unitRes V c₀) (Out.unitRes V c₀) (fun Z r z => by rw [Category.comp_id]) (hall₀ θx₀ θy₀ hx₀ hy₀)`. Conclude with `WeilCube.germ_eq_of_unitRes hpV (commIsOf_unique hL θx θy _ _ (hall θx θy hθx hθy) hm)`.
-/
theorem weil_eq_of_iso {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (θ : A ≅ A) [IsMonHom θ.hom] (w : LB.Iso L (L.pull θ.hom.left)) (hw : w.IsGen) {T : Over S}
    [Subsingleton T.left] (k : ℤ) (x y : T ⟶ A) (c c₀ : Γ(T.left, ⊤)ˣ) (h : Out.WeilIs A L k x y c)
    (h₀ : Out.WeilIs A L k (x ≫ θ.hom) (y ≫ θ.hom) c₀) : c = c₀ := by
  refine unit_ext fun p _ => ?_
  obtain ⟨V, hpV, ⟨θx₀, θy₀, hx₀, hy₀⟩, hall₀⟩ := h₀ p
  obtain ⟨V', hpV', -, hall⟩ := h p
  obtain rfl : V = V' := by
    ext q
    rw [Subsingleton.elim q p]
    exact ⟨fun _ => hpV', fun _ => hpV⟩
  have hp := isGrpPullback_of_iso θ
  have hτ : 𝟙 _ ≫ (Out.overRes (T := T) V).hom = (Out.overRes (T := T) V).hom ≫ 𝟙 S := by
    rw [Category.id_comp, Category.comp_id]
  have mvx : 𝟙 _ ≫ θx₀.pt.left = (Out.overResι V ≫ x).left ≫ θ.hom.left := by
    rw [hx₀, Category.id_comp, ← Over.comp_left, Category.assoc]
  have mvy : 𝟙 _ ≫ θy₀.pt.left = (Out.overResι V ≫ y).left ≫ θ.hom.left := by
    rw [hy₀, Category.id_comp, ← Over.comp_left, Category.assoc]
  obtain ⟨θx, hθx, mx⟩ := exists_theta_move hp (𝟙 _) hτ hL hL w hw k _ θx₀ mvx
  obtain ⟨θy, hθy, my⟩ := exists_theta_move hp (𝟙 _) hτ hL hL w hw k _ θy₀ mvy
  have hm := commIsOf_move hp (𝟙 _) hτ hL hL w k θx₀ θy₀ θx θy (by rw [hθx]; exact mvx) (by rw [hθy]; exact mvy)
    mx my (Out.unitRes V c₀) (Out.unitRes V c₀) (fun Z r z => by rw [Category.comp_id]) (hall₀ θx₀ θy₀ hx₀ hy₀)
  exact WeilCube.germ_eq_of_unitRes hpV (commIsOf_unique hL θx θy _ _ (hall θx θy hθx hθy) hm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Use `⟨0, D.unimod.1 (LinearMap.ext fun b => ?_)⟩` and prove the remaining obligations. Simplify using `using h b`. Establish `hn' : (n : ℤ) ≠ 0` using `by exact_mod_cast hn.ne'`. Set `f : D.La →+ ℤ` to `AddMonoidHom.mk' (fun b => D.EF v b / n) fun b b' => by`.

Rewrite using `[map_add, Int.add_ediv_of_dvd_left (h b)]`. Take `⟨z, hz⟩` from `D.unimod.2 f.toIntLinearMap`. Use `⟨z, D.unimod.1 (LinearMap.ext fun b => ?_)⟩` and prove the remaining obligations. Rewrite using `[map_nsmul, LinearMap.smul_apply, hz]`. Conclude with `(Int.mul_ediv_cancel' (h b)).symm`.
-/
theorem exists_eq_nsmul (D : Datum H) (n : ℕ) (v : D.La) (h : ∀ b, (n : ℤ) ∣ D.EF v b) : ∃ z, v = n • z := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, D.unimod.1 (LinearMap.ext fun b => ?_)⟩
    simpa using h b
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let f : D.La →+ ℤ := AddMonoidHom.mk' (fun b => D.EF v b / n) fun b b' => by
    rw [map_add, Int.add_ediv_of_dvd_left (h b)]
  obtain ⟨z, hz⟩ := D.unimod.2 f.toIntLinearMap
  refine ⟨z, D.unimod.1 (LinearMap.ext fun b => ?_)⟩
  rw [map_nsmul, LinearMap.smul_apply, hz]
  exact (Int.mul_ediv_cancel' (h b)).symm

/- English proof (translation)
Establish `hM : 0 < l.M` using `lt_of_lt_of_le (by norm_num) l.three_le`. Take `⟨a, rfl⟩` from `(I.onto _ hM x).1 hx`. Take `⟨a', ha'⟩` from `(I.onto _ hM (θ (I.ev l.M a))).1 (by rw [← map_pow, hx, map_one])`. Take `⟨i, hi, j, hj, hij⟩` from `Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp l.coprime)`. Establish `hj' : I.ev l.M (j • a') = I.ev l.M (j • a)`.

Rewrite using `[← θ_fix (j • a) (Submodule.smul_mem_smul hj trivial), I.lin, I.lin, θ_act, ha']`. Take `⟨z, hz⟩` from `exists_eq_nsmul D l.M (i • (a' - a)) fun b => by`. Establish `hb : H.bar i • b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)` using `Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hi) trivial`. Establish `h` using `θ_iso _ _ _ _ (I.isom _ hM a (H.bar i • b)) (by`. Rewrite using `[θ_fix _ hb, ← ha']`.

Conclude with `I.isom _ hM a' (H.bar i • b))`. Rewrite using `[D.adj, map_sub, LinearMap.sub_apply, ← (I.ζ_prim _ hM).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]`. Establish `hi' : I.ev l.M (i • a') = I.ev l.M (i • a)`. Establish `h : i • a' = i • (a' - a) + i • a` using `by rw [← smul_add, sub_add_cancel]`. Rewrite using `[h, I.add, (I.ker _ hM _).2 ⟨z, hz⟩, _root_.one_mul]`.

Establish `split : ∀ v, I.ev l.M v = I.ev l.M (i • v) * I.ev l.M (j • v)` using `fun v => by`. Rewrite using `[← I.add, ← add_smul, hij, one_smul]`. Rewrite using `[← ha', split a', split a, hi', hj']`.
-/
theorem fix_torsion {D : Datum H} (l : Level H) {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) (θ : Q →* Q)
    (θ_act : ∀ a x, θ (act a x) = act a (θ x))
    (θ_iso : ∀ x y c c', e l.M x y c → e l.M (θ x) (θ y) c' → c = c')
    (θ_fix : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), θ (I.ev l.M a) = I.ev l.M a)
    (x : Q) (hx : x ^ l.M = 1) : θ x = x := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨a, rfl⟩ := (I.onto _ hM x).1 hx
  obtain ⟨a', ha'⟩ := (I.onto _ hM (θ (I.ev l.M a))).1 (by rw [← map_pow, hx, map_one])
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp l.coprime)
  have hj' : I.ev l.M (j • a') = I.ev l.M (j • a) := by
    rw [← θ_fix (j • a) (Submodule.smul_mem_smul hj trivial), I.lin, I.lin, θ_act, ha']
  obtain ⟨z, hz⟩ := exists_eq_nsmul D l.M (i • (a' - a)) fun b => by
    have hb : H.bar i • b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
      Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hi) trivial
    have h := θ_iso _ _ _ _ (I.isom _ hM a (H.bar i • b)) (by
      rw [θ_fix _ hb, ← ha']; exact I.isom _ hM a' (H.bar i • b))
    rw [D.adj, map_sub, LinearMap.sub_apply, ← (I.ζ_prim _ hM).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]
  have hi' : I.ev l.M (i • a') = I.ev l.M (i • a) := by
    have h : i • a' = i • (a' - a) + i • a := by rw [← smul_add, sub_add_cancel]
    rw [h, I.add, (I.ker _ hM _).2 ⟨z, hz⟩, _root_.one_mul]
  have split : ∀ v, I.ev l.M v = I.ev l.M (i • v) * I.ev l.M (j • v) := fun v => by
    rw [← I.add, ← add_smul, hij, one_smul]
  rw [← ha', split a', split a, hi', hj']

variable {D : Datum H} {l : Level H}

/- English proof (translation)
Take `⟨w, hw⟩` from `hL`. Establish `hM : 0 < l.M` using `lt_of_lt_of_le (by norm_num) l.three_le`. Use `o.t.semi.smooth` as an intermediate fact. Use `o.t.semi.geomConnected` as an intermediate fact. Use `o.proper` as an intermediate fact.

Establish `hsub : Subsingleton (Sp k)` using `inferInstance`. Set `p : Sp k` to `IsLocalRing.closedPoint k`. Establish `: ConnectedSpace S`. Establish `: Nonempty S` using `⟨x p⟩`. Establish `: PreconnectedSpace S` using `x.denseRange.preconnectedSpace x.continuous`.

Conclude with `⟨inferInstance⟩`. Establish `: ConnectedSpace o.t.G.left` using `GeometricallyConnected.connectedSpace o.t.G.hom o.t.G.hom.isOpenMap`. Take `⟨d, hd⟩` from `exists_dim_of_preconnected o.t.G.hom (eSec o.t.G (x p))`. Take `⟨-, ws, gs', -⟩` from `o.t.sym`. Set `P : Out.PolAV S` to `{ A := o.t.G, g := d, smoothDim := hd, L := o.t.PP.L, isLB := o.t.PP.isLB, ample := o.ample, ktriv := o.ktriv isAb := ⟨inferInstance, inferInstance, inferInstance, ‹_›⟩ rigid := ⟨o.t.PP.rig, o.t.PP.rigGen⟩ sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }`.

Take `⟨-, I, -, -, hI⟩` from `o.geom k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage _).symm`. Establish `hMu : IsUnit (l.M : Γ(S, ⊤))`. Simplify using `using (b.unit _ hM).map ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ s.appTop).hom`. Establish `: Etale (Out.mulA o.t.G l.M).left` using `GrpTangent.etale_id_pow o.t.G hMu`. Establish `: IsSeparated (Out.mulA o.t.G l.M).left`.

Establish `: IsSeparated ((Out.mulA o.t.G l.M).left ≫ o.t.G.hom)` using `by rw [Over.w]; infer_instance`. Conclude with `IsSeparated.of_comp _ o.t.G.hom`. Use `hS S P l.M l.three_le θ ‹_› (fun _ => ⟨⊤, trivial, ?_⟩) (fix_torsion_of_fix_geometric_of_etale o.t.G l.M x θ.hom fun y hy => ?_)` and prove the remaining obligations. Take `⟨t, ht⟩` from `gen_of_iso ((isGen_iff w).1 hw) (o.t.G.hom ⁻¹ᵁ ⊤).ι`. Use `gen_chartPull (chartPullOut o.t.PP.L _ _ _ _ fun n => ?_) t ht` and prove the remaining obligations.

Use `fin_cases n`. Use `exacts [rfl, (Category.comp_id _).symm]`. Use `fix_torsion l I (IsMonHom.monoidHom θ.hom (Over.mk x)) (fun a z => ?_) (fun z z' c c' h h' => ?_) (fun a ha => ?_) y hy` and prove the remaining obligations. Use `show (z ≫ _) ≫ θ.hom = (z ≫ θ.hom) ≫ _`. Rewrite using `[Category.assoc, hact, Category.assoc]`.

Establish `: Subsingleton (Over.mk x).left` using `hsub`. Conclude with `unitOn_injective (weil_eq_of_iso (T := Over.mk x) o.t.PP.isLB θ w hw _ z z' _ _ h h')`. Use `show _ ≫ θ.hom = _`. Rewrite using `[← hI a ha, Category.assoc, heta]`.
-/
theorem aut_eq_id (hS : Out.SerreSt) {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} [IsLocallyNoetherian S]
    {s : S ⟶ Sp B} (o : Obj D l b s) {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) [IsDominant x]
    (θ : o.t.G ≅ o.t.G) [IsMonHom θ.hom] (hact : ∀ a, o.t.act.act a ≫ θ.hom = θ.hom ≫ o.t.act.act a)
    (hL : LBIso o.t.PP.L (o.t.PP.L.pull θ.hom.left)) (heta : ∀ a, o.eta a ≫ θ.hom = o.eta a) :
    θ.hom = 𝟙 _ := by
  obtain ⟨w, hw⟩ := hL
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have := o.t.semi.smooth
  have := o.t.semi.geomConnected
  have := o.proper
  have hsub : Subsingleton (Sp k) := inferInstance
  let p : Sp k := IsLocalRing.closedPoint k
  have : ConnectedSpace S := by
    have : Nonempty S := ⟨x p⟩
    have : PreconnectedSpace S := x.denseRange.preconnectedSpace x.continuous
    exact ⟨inferInstance⟩
  have : ConnectedSpace o.t.G.left := GeometricallyConnected.connectedSpace o.t.G.hom o.t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected o.t.G.hom (eSec o.t.G (x p))
  obtain ⟨-, ws, gs', -⟩ := o.t.sym
  let P : Out.PolAV S :=
    { A := o.t.G, g := d, smoothDim := hd, L := o.t.PP.L, isLB := o.t.PP.isLB, ample := o.ample, ktriv := o.ktriv
      isAb := ⟨inferInstance, inferInstance, inferInstance, ‹_›⟩
      rigid := ⟨o.t.PP.rig, o.t.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage _).symm
  have hMu : IsUnit (l.M : Γ(S, ⊤)) := by
    simpa using (b.unit _ hM).map ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ s.appTop).hom
  have : Etale (Out.mulA o.t.G l.M).left := GrpTangent.etale_id_pow o.t.G hMu
  have : IsSeparated (Out.mulA o.t.G l.M).left := by
    have : IsSeparated ((Out.mulA o.t.G l.M).left ≫ o.t.G.hom) := by rw [Over.w]; infer_instance
    exact IsSeparated.of_comp _ o.t.G.hom
  refine hS S P l.M l.three_le θ ‹_› (fun _ => ⟨⊤, trivial, ?_⟩)
    (fix_torsion_of_fix_geometric_of_etale o.t.G l.M x θ.hom fun y hy => ?_)
  · obtain ⟨t, ht⟩ := gen_of_iso ((isGen_iff w).1 hw) (o.t.G.hom ⁻¹ᵁ ⊤).ι
    refine gen_chartPull (chartPullOut o.t.PP.L _ _ _ _ fun n => ?_) t ht
    fin_cases n
    exacts [rfl, (Category.comp_id _).symm]
  · refine fix_torsion l I (IsMonHom.monoidHom θ.hom (Over.mk x)) (fun a z => ?_) (fun z z' c c' h h' => ?_)
      (fun a ha => ?_) y hy
    · show (z ≫ _) ≫ θ.hom = (z ≫ θ.hom) ≫ _
      rw [Category.assoc, hact, Category.assoc]
    · have : Subsingleton (Over.mk x).left := hsub
      exact unitOn_injective (weil_eq_of_iso (T := Over.mk x) o.t.PP.isLB θ w hw _ z z' _ _ h h')
    · show _ ≫ θ.hom = _
      rw [← hI a ha, Category.assoc, heta]

end ObjRigid

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

/- English proof (translation)
Take `⟨θ, hθ, hφ, hact, -, w, hw, -⟩` from `sabMap_iso m.toSABMap m'.toSABMap rfl rfl`. Establish `h` using `ObjRigid.aut_eq_id hS o₁ x θ hact ⟨w, hw⟩ fun a => by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `m'.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, Category.assoc]`.

Conclude with `(congrArg _ hφ).trans ((m.eta a).trans (m'.eta a).symm)`. Rewrite using `[Over.w, Over.w]`. Rewrite using `[← hφ, h, Over.id_left, Category.id_comp]`.
-/
theorem objMap_unique_of_isDominant (hS : Out.SerreSt) {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S S' : Scheme.{0}} [IsLocallyNoetherian S'] {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') [IsDominant x]
    {o : Obj D l b s} {o₁ : Obj D l b' s'} {y : S' ⟶ S} (m m' : ObjMap o₁ o y) :
    m.toSABMap.φ = m'.toSABMap.φ := by
  obtain ⟨θ, hθ, hφ, hact, -, w, hw, -⟩ := sabMap_iso m.toSABMap m'.toSABMap rfl rfl
  have h := ObjRigid.aut_eq_id hS o₁ x θ hact ⟨w, hw⟩ fun a => by
    apply Over.OverMorphism.ext
    apply m'.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc]
      exact (congrArg _ hφ).trans ((m.eta a).trans (m'.eta a).symm)
    · rw [Over.w, Over.w]
  rw [← hφ, h, Over.id_left, Category.id_comp]

/- English proof (translation)
Set `φ : R →+* AlgebraicClosure (FractionRing R)` to `(algebraMap (FractionRing R) _).comp (algebraMap R _)`. Establish `hφ : Function.Injective φ` using `(algebraMap (FractionRing R) _).injective.comp (IsFractionRing.injective R _)`. Establish `: IsDominant (spMap φ)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot φ).1 hφ]`. Conclude with `bot_le)⟩`.

Conclude with `objMap_unique_of_isDominant hS (spMap φ) m m'`.
-/
theorem objMap_unique_of_isDomain (hS : Out.SerreSt) {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S : Scheme.{0}} {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {s : S ⟶ Sp B}
    {s' : Sp R ⟶ Sp B'} {o : Obj D l b s} {o₁ : Obj D l b' s'} {y : Sp R ⟶ S} (m m' : ObjMap o₁ o y) :
    m.toSABMap.φ = m'.toSABMap.φ := by
  let φ : R →+* AlgebraicClosure (FractionRing R) := (algebraMap (FractionRing R) _).comp (algebraMap R _)
  have hφ : Function.Injective φ := (algebraMap (FractionRing R) _).injective.comp (IsFractionRing.injective R _)
  have : IsDominant (spMap φ) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)⟩
  exact objMap_unique_of_isDominant hS (spMap φ) m m'

/- English proof (translation)
The claim follows from `objMap_unique_of_isDomain hS m m'`.
-/
theorem objMap_unique_of_field (hS : Out.SerreSt) {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S : Scheme.{0}} {F : Type} [Field F] {s : S ⟶ Sp B} {s' : Sp F ⟶ Sp B'}
    {o : Obj D l b s} {o₁ : Obj D l b' s'} {y : Sp F ⟶ S} (m m' : ObjMap o₁ o y) :
    m.toSABMap.φ = m'.toSABMap.φ :=
  objMap_unique_of_isDomain hS m m'

end GlobalTheory
