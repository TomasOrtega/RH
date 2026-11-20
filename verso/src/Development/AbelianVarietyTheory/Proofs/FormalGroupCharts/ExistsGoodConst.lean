import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_val val val_of Good cubV val₂ IsCub isCub_cubV exists_chart psum_hom preHom)
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer.FBOf

/- English proof (translation)
Rewrite using `[gm_val r z U (h trivial), fnVal, dif_pos h]`. Establish `e : ∀ b, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom b) = b` using `fun b => congrArg (fun q => q.hom b) (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id`. Rewrite using `[e]`. Conclude with `(TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of A)).presheaf (homOfLE h) z trivial _).symm`.
-/
theorem gm_eq_germ_fnVal {A : Type} [CommRing A] {X : Scheme.{0}} (r : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ r ⁻¹ᵁ U) (a : Γ(X, U)ˣ) (z : Spec (CommRingCat.of A)) :
    (gm r z U a).val = ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (fnVal r U a.val)) := by
  rw [gm_val r z U (h trivial), fnVal, dif_pos h]
  have e : ∀ b, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom b) = b :=
    fun b => congrArg (fun q => q.hom b) (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id
  rw [e]
  exact (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of A)).presheaf (homOfLE h) z trivial _).symm

/- English proof (translation)
Apply `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1` to reduce the goal to its premises. Conclude with `TopCat.Presheaf.section_ext (Spec (CommRingCat.of A)).sheaf ⊤ _ _ fun z _ => h z`.
-/
theorem eq_of_germ {A : Type} [CommRing A] {a b : A} (h : ∀ z : Spec (CommRingCat.of A),
    ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
    ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)) :
    a = b := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1
  exact TopCat.Presheaf.section_ext (Spec (CommRingCat.of A)).sheaf ⊤ _ _ fun z _ => h z

/- English proof (translation)
Use `choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)`. Use `⟨fun ψ => if ψ z ∈ L.U j then j else I ψ, fun ψ => ?_, fun ψ h => if_pos h⟩` and prove the remaining obligations. Distinguish the cases in `h : ψ z ∈ L.U j`. Simplify `h` using `only [if_pos h]`. Simplify `hI ψ` using `only [if_neg h]`.
-/
theorem exists_good_const {X Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (j : L.ι) (z : Z) :
    ∃ J, Good L z J ∧ ∀ ψ : Z ⟶ X, ψ z ∈ L.U j → J ψ = j := by
  classical
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  refine ⟨fun ψ => if ψ z ∈ L.U j then j else I ψ, fun ψ => ?_, fun ψ h => if_pos h⟩
  by_cases h : ψ z ∈ L.U j
  · simpa only [if_pos h] using h
  · simpa only [if_neg h] using hI ψ

/- English proof (translation)
The claim follows from `val_of t r z J _ fun k => hJ _ (Set.mem_iInter.1 (h (trivial : z ∈ (⊤ : Z.Opens))) k)`.
-/
theorem val_const {X Y Z : Scheme.{0}} {L : LB X} {j : L.ι} {z : Z} {J : (Z ⟶ X) → L.ι}
    (hJ : ∀ ψ : Z ⟶ X, ψ z ∈ L.U j → J ψ = j) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (h : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun _ => j)) :
    val t r z J = gm r z (LB.wchart L φ (fun _ => j)) (t.s fun _ => j) :=
  val_of t r z J _ fun k => hJ _ (Set.mem_iInter.1 (h (trivial : z ∈ (⊤ : Z.Opens))) k)

section Key
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

/- English proof (translation)
Take `⟨j1, -, j3, -⟩` from `hJet R (Fin n × Fin d)`. Take `⟨r1, -, -, r4, -⟩` from `hRep R G d x hx (Fin n × Fin d)`. Establish `ex : ∀ a : Pt R n d, ∃ Y : Fam G (Fin n × Fin d), GP a → Rep x a Y ∧ ∀ Y', Rep x a Y' → Y' = Y` using `fun a => by`. Distinguish the cases in `h : GP a`. Take `⟨Y, h1, h2⟩` from `r1 a h`.

Conclude with `⟨Y, fun _ => ⟨h1, h2⟩⟩`. Conclude with `⟨fun _ => 1, fun h' => absurd h' h⟩`. Use `choose Y hY using ex`. Use `j3 g g' fun m => ?_` and prove the remaining obligations. Take `⟨τ, hτ, -⟩` from `j1 m`.

Use `eq_of_germ fun z => ?_` and prove the remaining obligations. Take `⟨J, hJ, hJ'⟩` from `exists_good_const Lr.L Lr.isLB j z`. Rewrite using `[← hτ, ← hτ]`. Use `H (sp (R₀ := R) (JetR R (Fin n × Fin d) m)) z J hJ ((((Spec (CommRingCat.of (JetR R (Fin n × Fin d) m))).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (JetR R (Fin n × Fin d) m))).inv.hom).comp τ.toRingHom) (fun a => Y a m) ?_ (fun a b ha hb => ?_) (fun o a …` and prove the remaining obligations. Conclude with `(congrFun ((hY 0 gp_zero₂).2 _ r4) m).symm`.

Conclude with `(congrFun ((hY _ (gp_addOf F hF.1 a b ha hb)).2 _ (hF.2 n a b _ _ (hY a ha).1 (hY b hb).1)) m).symm`. Conclude with `(congrFun ((hY _ (gp_comp1 _ a (hα o).1 ha)).2 _ ((hα o).2 n a _ (hY a ha).1)) m).symm`. Take `⟨h1, h2⟩` from `hph n a b e _ _ _ (hY a ha).1 (hY b hb).1 (hY e he).1 m`. Use `Eq.trans ?_ (congrArg Units.val (val_const (L := Lr.L) (φ := thφ G (x3 G)) (ε := thε) hJ' c.t _ h1)).symm` and prove the remaining obligations. Use `Eq.trans ?_ (gm_eq_germ_fnVal _ _ h1 _ z).symm` and prove the remaining obligations.

Conclude with `congrArg _ (congrArg _ ((hτ _).trans h2.symm))`. Take `⟨h1, h2⟩` from `had o n a b _ _ (hY a ha).1 (hY b hb).1 m`. Use `Eq.trans ?_ (congrArg (fun q => q⁻¹.val) (val_const hJ' (u o) _ h1)).symm` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg Units.val (map_inv _ _))` and prove the remaining obligations. Use `Eq.trans ?_ (gm_eq_germ_fnVal _ _ h1 _ z).symm` and prove the remaining obligations.

Conclude with `congrArg _ (congrArg _ ((hτ _).trans h2.symm))`.
-/
theorem series_ext (hJet : JetAlgSt) (hRep : RepSt) (Lr : RigLB G) (c : CubicalStr G Lr) {O : Type} [CommRing O]
    [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G)
    (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε))
    {d : ℕ} (x : Fam G (Fin d)) (hx : IsUnivChart G d x) (j : Lr.L.ι)
    (F : Fin d → PS R 2 d) (hF : IsLawOf x F) (α : O → Pt R 1 d) (hα : ∀ a, IsMapOf x x (act.act a) (α a))
    (ph : PS R 3 d) (hph : IsSer3 x _ (c.t.s (fun _ => j)).val ph)
    (ad : O → PS R 2 d) (had : ∀ a, IsSer2 x _ ((u a).s (fun _ => j))⁻¹.val (ad a))
    (n : ℕ) (g g' : PS R n d)
    (H : ∀ (T : Over (Spec (CommRingCat.of R))) (z : T.left) (J : (T.left ⟶ G.left) → Lr.L.ι), Good Lr.L z J →
      ∀ (Φ : PS R n d →+* T.left.presheaf.stalk z) (y : Pt R n d → (T ⟶ G)), y 0 = 1 →
      (∀ a b, GP a → GP b → y (addOf F a b) = y a * y b) →
      (∀ o a, GP a → y (comp1 (α o) a) = y a ≫ act.act o) →
      (∀ a b e, GP a → GP b → GP e → Φ (ev ![a, b, e] ph) = (cubV c z J (y a) (y b) (y e)).val) →
      (∀ o a b, GP a → GP b → Φ (ev ![a, b] (ad o)) = (val₂ (u o) z J (y a) (y b))⁻¹.val) → Φ g = Φ g') :
    g = g' := by
  classical
  obtain ⟨j1, -, j3, -⟩ := hJet R (Fin n × Fin d)
  obtain ⟨r1, -, -, r4, -⟩ := hRep R G d x hx (Fin n × Fin d)
  have ex : ∀ a : Pt R n d, ∃ Y : Fam G (Fin n × Fin d), GP a → Rep x a Y ∧ ∀ Y', Rep x a Y' → Y' = Y := fun a => by
    by_cases h : GP a
    · obtain ⟨Y, h1, h2⟩ := r1 a h
      exact ⟨Y, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 1, fun h' => absurd h' h⟩
  choose Y hY using ex
  refine j3 g g' fun m => ?_
  obtain ⟨τ, hτ, -⟩ := j1 m
  refine eq_of_germ fun z => ?_
  obtain ⟨J, hJ, hJ'⟩ := exists_good_const Lr.L Lr.isLB j z
  rw [← hτ, ← hτ]
  refine H (sp (R₀ := R) (JetR R (Fin n × Fin d) m)) z J hJ
    ((((Spec (CommRingCat.of (JetR R (Fin n × Fin d) m))).presheaf.germ ⊤ z trivial).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (JetR R (Fin n × Fin d) m))).inv.hom).comp τ.toRingHom)
    (fun a => Y a m) ?_ (fun a b ha hb => ?_) (fun o a ha => ?_) (fun a b e ha hb he => ?_) (fun o a b ha hb => ?_)
  · exact (congrFun ((hY 0 gp_zero₂).2 _ r4) m).symm
  · exact (congrFun ((hY _ (gp_addOf F hF.1 a b ha hb)).2 _ (hF.2 n a b _ _ (hY a ha).1 (hY b hb).1)) m).symm
  · exact (congrFun ((hY _ (gp_comp1 _ a (hα o).1 ha)).2 _ ((hα o).2 n a _ (hY a ha).1)) m).symm
  · obtain ⟨h1, h2⟩ := hph n a b e _ _ _ (hY a ha).1 (hY b hb).1 (hY e he).1 m
    refine Eq.trans ?_ (congrArg Units.val (val_const (L := Lr.L) (φ := thφ G (x3 G)) (ε := thε) hJ' c.t _ h1)).symm
    refine Eq.trans ?_ (gm_eq_germ_fnVal _ _ h1 _ z).symm
    exact congrArg _ (congrArg _ ((hτ _).trans h2.symm))
  · obtain ⟨h1, h2⟩ := had o n a b _ _ (hY a ha).1 (hY b hb).1 m
    refine Eq.trans ?_ (congrArg (fun q => q⁻¹.val) (val_const hJ' (u o) _ h1)).symm
    refine Eq.trans ?_ (congrArg Units.val (map_inv _ _))
    refine Eq.trans ?_ (gm_eq_germ_fnVal _ _ h1 _ z).symm
    exact congrArg _ (congrArg _ ((hτ _).trans h2.symm))

/- English proof (translation)
Introduce `s _`. Use `Set.mem_iInter.2 fun I => ?_` and prove the remaining obligations. Establish `h1 : (η[G] : 𝟙_ _ ⟶ G) = 1` using `by simp [Hom.one_def]`. Establish `e : lift η[G] (lift η[G] η[G]) ≫ psum G (x3 G) I.down = η[G]`. Use `(psum_hom (preHom (lift η[G] (lift η[G] η[G]))) (x3 G) I.down).trans ?_` and prove the remaining obligations.

Establish `: (fun i => preHom (lift η[G] (lift η[G] η[G])) (x3 G i)) = fun _ => 1`. Apply the tactic sequence `funext fun i => by fin_cases i <;> simp [preHom, x3, Hom.one_def]`. Use `(congrArg (fun q => psum G q I.down) this).trans ?_` and prove the remaining obligations. Rewrite using `[h1]`. Unfold `psum`.

Proceed by induction on `((List.finRange 3).filter (· ∈ I.down)) with`. Consider the case `nil => rfl`. Consider the case `cons k l ih => rw [List.foldr_cons, ih]`. Conclude with `_root_.mul_one (1 : 𝟙_ _ ⟶ G)`. Conclude with `(congrArg (fun q => q.left s ∈ L.U j) e).mpr (hj (trivial : s ∈ ⊤))`.
-/
theorem unit_mem_cube (L : LB G.left) (j : L.ι) (hj : ⊤ ≤ η[G].left ⁻¹ᵁ L.U j) :
    ⊤ ≤ (lift η[G] (lift η[G] η[G])).left ⁻¹ᵁ LB.wchart L (thφ G (x3 G)) (fun _ => j) := by
  intro s _
  refine Set.mem_iInter.2 fun I => ?_
  have h1 : (η[G] : 𝟙_ _ ⟶ G) = 1 := by simp [Hom.one_def]
  have e : lift η[G] (lift η[G] η[G]) ≫ psum G (x3 G) I.down = η[G] := by
    refine (psum_hom (preHom (lift η[G] (lift η[G] η[G]))) (x3 G) I.down).trans ?_
    have : (fun i => preHom (lift η[G] (lift η[G] η[G])) (x3 G i)) = fun _ => 1 :=
      funext fun i => by fin_cases i <;> simp [preHom, x3, Hom.one_def]
    refine (congrArg (fun q => psum G q I.down) this).trans ?_
    rw [h1]
    unfold psum
    induction ((List.finRange 3).filter (· ∈ I.down)) with
    | nil => rfl
    | cons k l ih => rw [List.foldr_cons, ih]; exact _root_.mul_one (1 : 𝟙_ _ ⟶ G)
  exact (congrArg (fun q => q.left s ∈ L.U j) e).mpr (hj (trivial : s ∈ ⊤))

/- English proof (translation)
Introduce `s _`. Use `Set.mem_iInter.2 fun a => ?_` and prove the remaining obligations. Establish `one : zero2 G ≫ rosatiφ G f g a = η[G].left`. Establish `e : ∀ q : G ⊗ G ⟶ G, lift η[G] η[G] ≫ q = η[G] → zero2 G ≫ q.left = η[G].left` using `fun q hq => congrArg (fun m => m.left) hq`. Establish `o : lift η[G] η[G] ≫ μ[G] = η[G]` using `by simpa [Hom.one_def, Hom.mul_def] using (_root_.mul_one (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G))`.

Apply the tactic sequence `fin_cases a <;> refine e _ ?_ <;> simp [padd, comp_lift_assoc, o]`. Conclude with `(congrArg (fun q => q s ∈ L.U j) one).mpr (hj (trivial : s ∈ ⊤))`.
-/
theorem unit_mem_ros (L : LB G.left) (j : L.ι) (hj : ⊤ ≤ η[G].left ⁻¹ᵁ L.U j) (f g : G ⟶ G) [IsMonHom f] [IsMonHom g] :
    ⊤ ≤ (lift η[G] η[G]).left ⁻¹ᵁ LB.wchart L (rosatiφ G f g) (fun _ => j) := by
  intro s _
  refine Set.mem_iInter.2 fun a => ?_
  have one : zero2 G ≫ rosatiφ G f g a = η[G].left := by
    have e : ∀ q : G ⊗ G ⟶ G, lift η[G] η[G] ≫ q = η[G] → zero2 G ≫ q.left = η[G].left := fun q hq =>
      congrArg (fun m => m.left) hq
    have o : lift η[G] η[G] ≫ μ[G] = η[G] := by simpa [Hom.one_def, Hom.mul_def] using
      (_root_.mul_one (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G))
    fin_cases a <;> refine e _ ?_ <;> simp [padd, comp_lift_assoc, o]
  exact (congrArg (fun q => q s ∈ L.U j) one).mpr (hj (trivial : s ∈ ⊤))

end Key

section Self
variable {R : Type} [CommRing R] {d : ℕ}

/- English proof (translation)
Unfold `ev`. Conclude with `congrFun MvPowerSeries.subst_self f`.
-/
theorem ev_self {n : ℕ} (f : PS R n d) : ev (fun j => pt R (n := n) d j) f = f := by
  unfold ev
  exact congrFun MvPowerSeries.subst_self f

/- English proof (translation)
Establish `: (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) = fun j => pt R d j`. Apply the tactic sequence `funext j; fin_cases j <;> rfl`. Rewrite using `[this, ev_self]`.
-/
theorem ev_self2 (f : PS R 2 d) : ev (n := 2) ![pt R d 0, pt R d 1] f = f := by
  have : (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) = fun j => pt R d j := by
    funext j; fin_cases j <;> rfl
  rw [this, ev_self]

/- English proof (translation)
Establish `: (![pt R d 0, pt R d 1, pt R d 2] : Fin 3 → Pt R 3 d) = fun j => pt R d j`. Apply the tactic sequence `funext j; fin_cases j <;> rfl`. Rewrite using `[this, ev_self]`.
-/
theorem ev_self3 (f : PS R 3 d) : ev (n := 3) ![pt R d 0, pt R d 1, pt R d 2] f = f := by
  have : (![pt R d 0, pt R d 1, pt R d 2] : Fin 3 → Pt R 3 d) = fun j => pt R d j := by
    funext j; fin_cases j <;> rfl
  rw [this, ev_self]

end Self

/- English proof (translation)
Introduce `hJet hRep hLaw _ hAct _ hSer _ hRos R _ G _ _ s2 s3 Lr c O _ _ act u hu d x hx j hj`. Take `⟨⟨Gl, hF⟩, -⟩` from `hLaw R G d x hx`. Take `⟨A, hA⟩` from `hAct R G d x hx O act Gl hF`. Take `⟨-, e2, e3⟩` from `hSer R G d x hx`. Take `⟨ph, hph, -⟩` from `e3 _ (unit_mem_cube Lr.L j hj) (c.t.s (fun _ => j)).val`.

Establish `exad` using `fun a : O => (e2 _ (@unit_mem_ros _ _ _ _ _ Lr.L j hj _ _ (act.hom a) (act.hom (star a))) ((u a).s (fun _ => j))⁻¹.val).exists`. Use `choose ad had using exad`. Establish `K` using `series_ext hJet hRep Lr c act u x hx j Gl.F hF A.act hA ph hph ad had`. Establish `Ro` using `hRos _ G s2 s3 Lr c O act u hu`. Establish `gA : ∀ {n} {a b : Pt R n d}, GP a → GP b → GP (addOf Gl.F a b)` using `fun ha hb => gp_addOf _ Gl.const _ _ ha hb`.

Establish `gC : ∀ {n} (o) {a : Pt R n d}, GP a → GP (comp1 (A.act o) a)` using `fun o _ ha => gp_comp1 _ _ (A.const o) ha`. Establish `g0 : ∀ {n}, GP (0 : Pt R n d)` using `gp_zero₂`. Establish `gp : ∀ {n} (i : Fin n), GP (pt R d i)` using `fun i => gp_pt i`. Establish `face : ∀ {n} (a b : Pt R n d), GP a → GP b → ev ![0, a, b] ph = 1` using `fun a b ha hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by`. Rewrite using `[p _ _ _ g0 ha hb, y0, (isCub_cubV c hJ).face, map_one, Units.val_one]`.

Establish `s01 : ∀ {n} (a b e : Pt R n d), GP a → GP b → GP e → ev ![a, b, e] ph = ev ![b, a, e] ph` using `fun a b e ha hb he => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by`. Rewrite using `[p _ _ _ ha hb he, p _ _ _ hb ha he, (isCub_cubV c hJ).s01]`. Establish `s12 : ∀ {n} (a b e : Pt R n d), GP a → GP b → GP e → ev ![a, b, e] ph = ev ![a, e, b] ph` using `fun a b e ha hb he => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by`. Rewrite using `[p _ _ _ ha hb he, p _ _ _ ha he hb, (isCub_cubV c hJ).s12]`. Establish `coc : ∀ {n} (a b e f : Pt R n d), GP a → GP b → GP e → GP f → ev ![a, b, f] ph * ev ![addOf Gl.F a b, e, f] ph = ev ![b, e, f] ph * ev ![a, addOf Gl.F b e, f] ph` using `fun a b e f ha hb he hf => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by`.

Rewrite using `[map_mul, map_mul, p _ _ _ ha hb hf, p _ _ _ (gA ha hb) he hf, p _ _ _ hb he hf, p _ _ _ ha (gA hb he) hf, ya _ _ ha hb, ya _ _ hb he, ← Units.val_mul, ← Units.val_mul, _root_.mul_comm, (isCub_cubV c hJ).coc, _root_.mul_comm]`. Establish `cpt : ∀ {n} (a b e f : Pt R n d), GP a → GP b → GP e → GP f → ev ![a, b, e] ph * ev ![a, b, f] ph * ev ![addOf Gl.F a b, e, f] ph = ev ![a, e, f] ph * ev ![b, e, f] ph * ev ![a, b, addOf Gl.F e f] ph` using `fun a b e f ha hb he hf => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by`. Rewrite using `[map_mul, map_mul, map_mul, map_mul, p _ _ _ ha hb he, p _ _ _ ha hb hf, p _ _ _ (gA ha hb) he hf, p _ _ _ ha he hf, p _ _ _ hb he hf, p _ _ _ ha hb (gA he hf), ya _ _ ha hb, ya _ _ he hf]`. Use `congrArg Units.val ((isCub_cubV c hJ).compat (y a) (y b) (y e) (y f))` as an intermediate fact. Simplify using `only [Units.val_mul] at this`.

Take the linear combination `this`. Establish `inv3 : ∀ {U : Type} [CommGroup U] {a b e s t : U}, a * s = t * (b * e) → t * a⁻¹ = b⁻¹ * e⁻¹ * s`. Introduce `U _ a b e s t h`. Establish `: s = a⁻¹ * (t * (b * e))` using `by rw [← h, inv_mul_cancel_left]`. Rewrite using `[this]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws. Establish `l1 : ∀ {n} (o) (a b e : Pt R n d), GP a → GP b → GP e → ev ![comp1 (A.act o) a, comp1 (A.act o) b, e] ph * ev ![addOf Gl.F a b, e] (ad o) = ev ![a, e] (ad o) * ev ![b, e] (ad o) * ev ![a, b, comp1 (A.act (star o)) e] ph` using `fun o a b e ha hb he => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by`. Rewrite using `[map_mul, map_mul, map_mul, p _ _ _ (gC o ha) (gC o hb) he, p _ _ _ ha hb (gC _ he), q _ _ _ (gA ha hb) he, q _ _ _ ha he, q _ _ _ hb he, ya _ _ ha hb, yc _ _ ha, yc _ _ hb, yc _ _ he, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]`.

Conclude with `congrArg Units.val (inv3 ((Ro T z J hJ).1 o _ _ _))`. Establish `l2 : ∀ {n} (o) (a b e : Pt R n d), GP a → GP b → GP e → ev ![comp1 (A.act o) a, b, e] ph * ev ![a, addOf Gl.F b e] (ad o) = ev ![a, b] (ad o) * ev ![a, e] (ad o) * ev ![a, comp1 (A.act (star o)) b, comp1 (A.act (star o)) e] ph` using `fun o a b e ha hb he => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by`. Rewrite using `[map_mul, map_mul, map_mul, p _ _ _ (gC o ha) hb he, p _ _ _ ha (gC _ hb) (gC _ he), q _ _ _ ha (gA hb he), q _ _ _ ha hb, q _ _ _ ha he, ya _ _ hb he, yc _ _ ha, yc _ _ hb, yc _ _ he, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]`. Conclude with `congrArg Units.val (inv3 ((Ro T z J hJ).2.1 o _ _ _))`. Establish `a1 : ∀ {n} (a b : Pt R n d), GP a → GP b → ev ![a, b] (ad 1) = 1` using `fun a b ha hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by`.

Rewrite using `[q _ _ _ ha hb, map_one]`. Conclude with `congrArg (fun t => t⁻¹.val) ((Ro T z J hJ).2.2.1 _ _)`. Establish `am : ∀ {n} (o o') (a b : Pt R n d), GP a → GP b → ev ![a, b] (ad (o * o')) = ev ![comp1 (A.act o') a, b] (ad o) * ev ![a, comp1 (A.act (star o)) b] (ad o')` using `fun o o' a b ha hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by`. Rewrite using `[map_mul, q _ _ _ ha hb, q _ _ _ (gC _ ha) hb, q _ _ _ ha (gC _ hb), yc _ _ ha, yc _ _ hb, ← Units.val_mul, ← mul_inv]`. Conclude with `congrArg (fun t => t⁻¹.val) ((Ro T z J hJ).2.2.2.1 _ _ _ _)`.

Establish `aa : ∀ {n} (o o') (a b : Pt R n d), GP a → GP b → ev ![comp1 (A.act o) a, comp1 (A.act o') a, b] ph * ev ![a, b] (ad (o + o')) = ev ![a, b] (ad o) * ev ![a, b] (ad o') * ev ![a, comp1 (A.act (star o)) b, comp1 (A.act (star o')) b] ph` using `fun o o' a b ha hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by`. Rewrite using `[map_mul, map_mul, map_mul, p _ _ _ (gC _ ha) (gC _ ha) hb, p _ _ _ ha (gC _ hb) (gC _ hb), q _ _ _ ha hb, q _ _ _ ha hb, q _ _ _ ha hb, yc _ _ ha, yc _ _ ha, yc _ _ hb, yc _ _ hb, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]`. Conclude with `congrArg Units.val (inv3 ((Ro T z J hJ).2.2.2.2.1 _ _ _ _))`. Establish `as : ∀ {n} (o) (a b : Pt R n d), GP a → GP b → ev ![a, b] (ad o) * ev ![b, a] (ad (star o)) = 1` using `fun o a b ha hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by`. Rewrite using `[map_mul, q _ _ _ ha hb, q _ _ _ hb ha, ← Units.val_mul, ← mul_inv, map_one]`.

Conclude with `congrArg (fun t => t⁻¹.val) ((Ro T z J hJ).2.2.2.2.2 _ _ _)`. Establish `x0 : ∀ {n} (o) (b : Pt R n d), GP b → ev ![0, b] (ad o) = 1` using `fun o b hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by`. Rewrite using `[q _ _ _ g0 hb, y0, map_one]`. Establish `h` using `(Ro T z J hJ).1 o 1 1 (y b)`. Use `act.hom o` as an intermediate fact.

Use `beta_reduce at h`. Rewrite `h` using `[_root_.mul_one, MonObj.one_comp, (isCub_cubV c hJ).face, (isCub_cubV c hJ).face, _root_.mul_one, _root_.one_mul]`. Conclude with `congrArg (fun t => t⁻¹.val) (left_eq_mul.1 h)`. Establish `x1 : ∀ {n} (o) (b : Pt R n d), GP b → ev ![b, 0] (ad o) = 1` using `fun o b hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by`. Rewrite using `[q _ _ _ hb g0, y0, map_one]`.

Establish `h` using `(Ro T z J hJ).2.1 o (y b) 1 1`. Use `act.hom (star o)` as an intermediate fact. Use `beta_reduce at h`. Rewrite `h` using `[_root_.mul_one, MonObj.one_comp, (isCub_cubV c hJ).face₂, (isCub_cubV c hJ).face₂, _root_.mul_one, _root_.one_mul]`. Conclude with `congrArg (fun t => t⁻¹.val) (left_eq_mul.1 h)`.

Establish `f0 : ev (n` using `2) ![0, pt R d 0, pt R d 1] ph = 1 := face _ _ (gp 0) (gp 1)`. Establish `f1 : ev (n` using `2) ![pt R d 0, 0, pt R d 1] ph = 1 := (s01 _ _ _ (gp 0) g0 (gp 1)).trans f0`. Establish `f2 : ev (n` using `2) ![pt R d 0, pt R d 1, 0] ph = 1 := (s12 _ _ _ (gp 0) (gp 1) g0).trans f1`. Use `⟨{ G := Gl, A := A, ph1 := ph, ph2 := ph, sy := 1, ad := ad cocycleLeft_zero_fst := f0, cocycleLeft_zero_snd := f1, cocycleLeft_zero_thd := f2, cocycleRight_zero_fst := f0, cocycleRight_zero_snd := f1, cocycleRight_zero_thd := f2 symmetry_zero_fst := ev_one _, symmetry_zero_snd : …` and prove the remaining obligations. Establish `rot : ∀ (a b e : Pt R 4 d), GP a → GP b → GP e → ev ![a, b, e] ph = ev ![b, e, a] ph` using `fun a b e ha hb he => (s01 _ _ _ ha hb he).trans (s12 _ _ _ hb ha he)`.

Rewrite using `[rot _ _ _ (gp 0) (gp 1) (gp 2), rot _ _ _ (gp 0) (gA (gp 1) (gp 2)) (gp 3), rot _ _ _ (gp 0) (gp 2) (gp 3), rot _ _ _ (gp 0) (gp 1) (gA (gp 2) (gp 3))]`. Conclude with `coc _ _ _ _ (gp 1) (gp 2) (gp 3) (gp 0)`. Rewrite using `[ev_one, ev_one, ev_one, _root_.mul_one, _root_.mul_one, _root_.one_mul]`. Conclude with `(ev_self3 _).symm.trans ((s01 _ _ _ (gp 0) (gp 1) (gp 2)).trans (s12 _ _ _ (gp 1) (gp 0) (gp 2)))`. Use `aa a b _ _ (gp (0 : Fin 2)) (gp 1)` as an intermediate fact.

Rewrite `this` using `[ev_self2, ev_self2, ev_self2]`. Then use the resulting hypothesis. Use `as a _ _ (gp (0 : Fin 2)) (gp 1)` as an intermediate fact. Rewrite `this` using `[ev_self2]`. Rewrite using `[ev_one, ev_one, _root_.mul_one, this]`.
-/
theorem fbOf : JetAlgSt → RepSt → LawSt → MapSt → ActSt → SerSt → SerExSt → ValSerSt → RosIdSt → FBOfSt := by
  intro hJet hRep hLaw _ hAct _ hSer _ hRos R _ G _ _ s2 s3 Lr c O _ _ act u hu d x hx j hj
  obtain ⟨⟨Gl, hF⟩, -⟩ := hLaw R G d x hx
  obtain ⟨A, hA⟩ := hAct R G d x hx O act Gl hF
  obtain ⟨-, e2, e3⟩ := hSer R G d x hx
  obtain ⟨ph, hph, -⟩ := e3 _ (unit_mem_cube Lr.L j hj) (c.t.s (fun _ => j)).val
  have exad := fun a : O => (e2 _ (@unit_mem_ros _ _ _ _ _ Lr.L j hj _ _ (act.hom a) (act.hom (star a)))
    ((u a).s (fun _ => j))⁻¹.val).exists
  choose ad had using exad
  have K := series_ext hJet hRep Lr c act u x hx j Gl.F hF A.act hA ph hph ad had
  have Ro := hRos _ G s2 s3 Lr c O act u hu
  have gA : ∀ {n} {a b : Pt R n d}, GP a → GP b → GP (addOf Gl.F a b) := fun ha hb => gp_addOf _ Gl.const _ _ ha hb
  have gC : ∀ {n} (o) {a : Pt R n d}, GP a → GP (comp1 (A.act o) a) := fun o _ ha => gp_comp1 _ _ (A.const o) ha
  have g0 : ∀ {n}, GP (0 : Pt R n d) := gp_zero₂
  have gp : ∀ {n} (i : Fin n), GP (pt R d i) := fun i => gp_pt i
  have face : ∀ {n} (a b : Pt R n d), GP a → GP b → ev ![0, a, b] ph = 1 := fun a b ha hb =>
    K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [p _ _ _ g0 ha hb, y0, (isCub_cubV c hJ).face, map_one, Units.val_one]
  have s01 : ∀ {n} (a b e : Pt R n d), GP a → GP b → GP e → ev ![a, b, e] ph = ev ![b, a, e] ph := fun a b e ha hb he =>
    K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [p _ _ _ ha hb he, p _ _ _ hb ha he, (isCub_cubV c hJ).s01]
  have s12 : ∀ {n} (a b e : Pt R n d), GP a → GP b → GP e → ev ![a, b, e] ph = ev ![a, e, b] ph := fun a b e ha hb he =>
    K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [p _ _ _ ha hb he, p _ _ _ ha he hb, (isCub_cubV c hJ).s12]
  have coc : ∀ {n} (a b e f : Pt R n d), GP a → GP b → GP e → GP f →
      ev ![a, b, f] ph * ev ![addOf Gl.F a b, e, f] ph = ev ![b, e, f] ph * ev ![a, addOf Gl.F b e, f] ph :=
    fun a b e f ha hb he hf => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [map_mul, map_mul, p _ _ _ ha hb hf, p _ _ _ (gA ha hb) he hf, p _ _ _ hb he hf, p _ _ _ ha (gA hb he) hf,
        ya _ _ ha hb, ya _ _ hb he, ← Units.val_mul, ← Units.val_mul, _root_.mul_comm, (isCub_cubV c hJ).coc,
        _root_.mul_comm]
  have cpt : ∀ {n} (a b e f : Pt R n d), GP a → GP b → GP e → GP f →
      ev ![a, b, e] ph * ev ![a, b, f] ph * ev ![addOf Gl.F a b, e, f] ph =
        ev ![a, e, f] ph * ev ![b, e, f] ph * ev ![a, b, addOf Gl.F e f] ph :=
    fun a b e f ha hb he hf => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [map_mul, map_mul, map_mul, map_mul, p _ _ _ ha hb he, p _ _ _ ha hb hf, p _ _ _ (gA ha hb) he hf,
        p _ _ _ ha he hf, p _ _ _ hb he hf, p _ _ _ ha hb (gA he hf), ya _ _ ha hb, ya _ _ he hf]
      have := congrArg Units.val ((isCub_cubV c hJ).compat (y a) (y b) (y e) (y f))
      simp only [Units.val_mul] at this
      linear_combination this
  have inv3 : ∀ {U : Type} [CommGroup U] {a b e s t : U}, a * s = t * (b * e) → t * a⁻¹ = b⁻¹ * e⁻¹ * s := by
    intro U _ a b e s t h
    have : s = a⁻¹ * (t * (b * e)) := by rw [← h, inv_mul_cancel_left]
    rw [this]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have l1 : ∀ {n} (o) (a b e : Pt R n d), GP a → GP b → GP e →
      ev ![comp1 (A.act o) a, comp1 (A.act o) b, e] ph * ev ![addOf Gl.F a b, e] (ad o) =
        ev ![a, e] (ad o) * ev ![b, e] (ad o) * ev ![a, b, comp1 (A.act (star o)) e] ph :=
    fun o a b e ha hb he => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [map_mul, map_mul, map_mul, p _ _ _ (gC o ha) (gC o hb) he, p _ _ _ ha hb (gC _ he), q _ _ _ (gA ha hb) he,
        q _ _ _ ha he, q _ _ _ hb he, ya _ _ ha hb, yc _ _ ha, yc _ _ hb, yc _ _ he, ← Units.val_mul, ← Units.val_mul,
        ← Units.val_mul]
      exact congrArg Units.val (inv3 ((Ro T z J hJ).1 o _ _ _))
  have l2 : ∀ {n} (o) (a b e : Pt R n d), GP a → GP b → GP e →
      ev ![comp1 (A.act o) a, b, e] ph * ev ![a, addOf Gl.F b e] (ad o) =
        ev ![a, b] (ad o) * ev ![a, e] (ad o) * ev ![a, comp1 (A.act (star o)) b, comp1 (A.act (star o)) e] ph :=
    fun o a b e ha hb he => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [map_mul, map_mul, map_mul, p _ _ _ (gC o ha) hb he, p _ _ _ ha (gC _ hb) (gC _ he), q _ _ _ ha (gA hb he),
        q _ _ _ ha hb, q _ _ _ ha he, ya _ _ hb he, yc _ _ ha, yc _ _ hb, yc _ _ he, ← Units.val_mul, ← Units.val_mul,
        ← Units.val_mul]
      exact congrArg Units.val (inv3 ((Ro T z J hJ).2.1 o _ _ _))
  have a1 : ∀ {n} (a b : Pt R n d), GP a → GP b → ev ![a, b] (ad 1) = 1 :=
    fun a b ha hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [q _ _ _ ha hb, map_one]
      exact congrArg (fun t => t⁻¹.val) ((Ro T z J hJ).2.2.1 _ _)
  have am : ∀ {n} (o o') (a b : Pt R n d), GP a → GP b → ev ![a, b] (ad (o * o')) =
      ev ![comp1 (A.act o') a, b] (ad o) * ev ![a, comp1 (A.act (star o)) b] (ad o') :=
    fun o o' a b ha hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [map_mul, q _ _ _ ha hb, q _ _ _ (gC _ ha) hb, q _ _ _ ha (gC _ hb), yc _ _ ha, yc _ _ hb, ← Units.val_mul,
        ← mul_inv]
      exact congrArg (fun t => t⁻¹.val) ((Ro T z J hJ).2.2.2.1 _ _ _ _)
  have aa : ∀ {n} (o o') (a b : Pt R n d), GP a → GP b →
      ev ![comp1 (A.act o) a, comp1 (A.act o') a, b] ph * ev ![a, b] (ad (o + o')) =
        ev ![a, b] (ad o) * ev ![a, b] (ad o') * ev ![a, comp1 (A.act (star o)) b, comp1 (A.act (star o')) b] ph :=
    fun o o' a b ha hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [map_mul, map_mul, map_mul, p _ _ _ (gC _ ha) (gC _ ha) hb, p _ _ _ ha (gC _ hb) (gC _ hb), q _ _ _ ha hb,
        q _ _ _ ha hb, q _ _ _ ha hb, yc _ _ ha, yc _ _ ha, yc _ _ hb, yc _ _ hb, ← Units.val_mul, ← Units.val_mul,
        ← Units.val_mul]
      exact congrArg Units.val (inv3 ((Ro T z J hJ).2.2.2.2.1 _ _ _ _))
  have as : ∀ {n} (o) (a b : Pt R n d), GP a → GP b → ev ![a, b] (ad o) * ev ![b, a] (ad (star o)) = 1 :=
    fun o a b ha hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [map_mul, q _ _ _ ha hb, q _ _ _ hb ha, ← Units.val_mul, ← mul_inv, map_one]
      exact congrArg (fun t => t⁻¹.val) ((Ro T z J hJ).2.2.2.2.2 _ _ _)
  have x0 : ∀ {n} (o) (b : Pt R n d), GP b → ev ![0, b] (ad o) = 1 :=
    fun o b hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [q _ _ _ g0 hb, y0, map_one]
      have h := (Ro T z J hJ).1 o 1 1 (y b)
      have := act.hom o
      beta_reduce at h
      rw [_root_.mul_one, MonObj.one_comp, (isCub_cubV c hJ).face, (isCub_cubV c hJ).face, _root_.mul_one,
        _root_.one_mul] at h
      exact congrArg (fun t => t⁻¹.val) (left_eq_mul.1 h)
  have x1 : ∀ {n} (o) (b : Pt R n d), GP b → ev ![b, 0] (ad o) = 1 :=
    fun o b hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [q _ _ _ hb g0, y0, map_one]
      have h := (Ro T z J hJ).2.1 o (y b) 1 1
      have := act.hom (star o)
      beta_reduce at h
      rw [_root_.mul_one, MonObj.one_comp, (isCub_cubV c hJ).face₂, (isCub_cubV c hJ).face₂, _root_.mul_one,
        _root_.one_mul] at h
      exact congrArg (fun t => t⁻¹.val) (left_eq_mul.1 h)
  have f0 : ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1 := face _ _ (gp 0) (gp 1)
  have f1 : ev (n := 2) ![pt R d 0, 0, pt R d 1] ph = 1 := (s01 _ _ _ (gp 0) g0 (gp 1)).trans f0
  have f2 : ev (n := 2) ![pt R d 0, pt R d 1, 0] ph = 1 := (s12 _ _ _ (gp 0) (gp 1) g0).trans f1
  refine ⟨{ G := Gl, A := A, ph1 := ph, ph2 := ph, sy := 1, ad := ad
            cocycleLeft_zero_fst := f0, cocycleLeft_zero_snd := f1, cocycleLeft_zero_thd := f2, cocycleRight_zero_fst := f0, cocycleRight_zero_snd := f1, cocycleRight_zero_thd := f2
            symmetry_zero_fst := ev_one _, symmetry_zero_snd := ev_one _
            adjoint_zero_fst := fun a => x0 a _ (gp 0), adjoint_zero_snd := fun a => x1 a _ (gp 0)
            cocycleLeft_assoc := coc _ _ _ _ (gp 0) (gp 1) (gp 2) (gp 3)
            cocycleLeft_comm := (s01 _ _ _ (gp 1) (gp 0) (gp 2)).trans (ev_self3 _)
            cocycleRight_assoc := ?_
            cocycleRight_comm := (s12 _ _ _ (gp 0) (gp 2) (gp 1)).trans (ev_self3 _)
            interchange := cpt _ _ _ _ (gp 0) (gp 1) (gp 2) (gp 3)
            sy_inv := by rw [ev_one, _root_.mul_one]
            sy_law := ?_
            adjoint_compat_left := fun a => l1 a _ _ _ (gp 0) (gp 1) (gp 2)
            adjoint_compat_right := fun a => l2 a _ _ _ (gp 0) (gp 1) (gp 2)
            ad_one := (ev_self2 _).symm.trans (a1 _ _ (gp 0) (gp 1))
            ad_mul := fun a b => (ev_self2 _).symm.trans (am a b _ _ (gp 0) (gp 1))
            ad_add := fun a b => ?_
            ad_sy := fun a => ?_ }, hF, hA, hph, rfl, rfl, had⟩
  · have rot : ∀ (a b e : Pt R 4 d), GP a → GP b → GP e → ev ![a, b, e] ph = ev ![b, e, a] ph := fun a b e ha hb he =>
      (s01 _ _ _ ha hb he).trans (s12 _ _ _ hb ha he)
    rw [rot _ _ _ (gp 0) (gp 1) (gp 2), rot _ _ _ (gp 0) (gA (gp 1) (gp 2)) (gp 3), rot _ _ _ (gp 0) (gp 2) (gp 3),
      rot _ _ _ (gp 0) (gp 1) (gA (gp 2) (gp 3))]
    exact coc _ _ _ _ (gp 1) (gp 2) (gp 3) (gp 0)
  · rw [ev_one, ev_one, ev_one, _root_.mul_one, _root_.mul_one, _root_.one_mul]
    exact (ev_self3 _).symm.trans ((s01 _ _ _ (gp 0) (gp 1) (gp 2)).trans (s12 _ _ _ (gp 1) (gp 0) (gp 2)))
  · have := aa a b _ _ (gp (0 : Fin 2)) (gp 1)
    rwa [ev_self2, ev_self2, ev_self2] at this
  · have := as a _ _ (gp (0 : Fin 2)) (gp 1)
    rw [ev_self2] at this
    rw [ev_one, ev_one, _root_.mul_one, this]

end GlobalTheory.JetSer.FBOf
