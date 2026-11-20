import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.GC

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing

section Points

variable {V : Type} [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F]

/- English proof (translation)
Simplify using `only [DegPre.jFR, jFK, jK, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
private theorem jFR_eq' : DegPre.jFR (R := V) F = Spec.map (CommRingCat.ofHom
    ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)))) := by
  simp only [DegPre.jFR, jFK, jK, ← Spec.map_comp]
  rfl

/- English proof (translation)
Rewrite using `[jFR_eq']`. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[Spec.map_base]`. Establish `hinj : Function.Injective ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)))` using `(algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))`. Use `(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (fun x hx => ?_)` and prove the remaining obligations.

Establish `hx' : ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))) x = 0` using `hx`. Rewrite using `[show x = 0 from hinj (hx'.trans (map_zero _).symm)]`. Conclude with `zero_mem _`.
-/
theorem isDominant_jFR : IsDominant (DegPre.jFR (R := V) F) := by
  rw [jFR_eq']
  refine ⟨?_⟩
  rw [Spec.map_base]
  have hinj : Function.Injective ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))) :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (fun x hx => ?_)
  have hx' : ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))) x = 0 := hx
  rw [show x = 0 from hinj (hx'.trans (map_zero _).symm)]
  exact zero_mem _

end Points

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, q.base (IsLocalRing.closedPoint V) ∈ L.U i := by`. Establish `: q.base (IsLocalRing.closedPoint V) ∈ (⨆ i, L.U i)` using `by rw [hL.cover]; trivial`. Simplify `this` using `[TopologicalSpace.Opens.mem_iSup]`. Use `⟨i, top_unique fun x _ => ?_⟩` and prove the remaining obligations. Establish `hs : x ⤳ IsLocalRing.closedPoint V` using `(PrimeSpectrum.le_iff_specializes x _).1 (IsLocalRing.le_maximalIdeal x.isPrime.ne_top)`.

Conclude with `hs.mem_open (q ⁻¹ᵁ L.U i).isOpen hi`.
-/
theorem exists_chart_top {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    (q : Spec (CommRingCat.of V) ⟶ X) : ∃ i, q ⁻¹ᵁ L.U i = ⊤ := by
  obtain ⟨i, hi⟩ : ∃ i, q.base (IsLocalRing.closedPoint V) ∈ L.U i := by
    have : q.base (IsLocalRing.closedPoint V) ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  refine ⟨i, top_unique fun x _ => ?_⟩
  have hs : x ⤳ IsLocalRing.closedPoint V :=
    (PrimeSpectrum.le_iff_specializes x _).1 (IsLocalRing.le_maximalIdeal x.isPrime.ne_top)
  exact hs.mem_open (q ⁻¹ᵁ L.U i).isOpen hi

section Sep

variable {V : Type} [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F]
  (P : PolAV (Spec (CommRingCat.of V)))

/- English proof (translation)
Use `haveI := isDominant_jFR (V := V) F`. Use `haveI : IsProper P.A.hom := P.isAb.proper`. Conclude with `ext_of_isDominant_of_isSeparated P.A.hom (h₁.trans h₂.symm) (DegPre.jFR (R := V) F) h`.
-/
theorem vpt_ext {q₁ q₂ : Spec (CommRingCat.of V) ⟶ P.A.left} (h₁ : q₁ ≫ P.A.hom = 𝟙 _)
    (h₂ : q₂ ≫ P.A.hom = 𝟙 _) (h : DegPre.jFR (R := V) F ≫ q₁ = DegPre.jFR (R := V) F ≫ q₂) : q₁ = q₂ := by
  haveI := isDominant_jFR (V := V) F
  haveI : IsProper P.A.hom := P.isAb.proper
  exact ext_of_isDominant_of_isSeparated P.A.hom (h₁.trans h₂.symm) (DegPre.jFR (R := V) F) h

end Sep

section Fam

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
  [Algebra (FractionRing R) F]

/- English proof (translation)
Use `fin_cases k`. Use `show (DegPre.prB D F).left = (DegPre.prB D F).left ≫ 𝟙 _`. Simplify using the standard rewrite rules. Use `show (padd D.P.A (DegPre.prB D F) (toUnit _ ≫ D.c α)).left = (DegPre.prB D F).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left`. Rewrite using `[← Over.comp_left]`.

Use `congr 1`. Simplify using `[padd, comp_lift_assoc]`. Use `show (toUnit _ ≫ D.c α).left = (DegPre.prB D F).left ≫ (toUnit D.P.A ≫ D.c α).left`. Rewrite using `[← Over.comp_left]`. Use `congr 1`.

Simplify using the standard rewrite rules. Use `show (toUnit _ ≫ η[D.P.A]).left = (DegPre.prB D F).left ≫ (toUnit D.P.A ≫ η[D.P.A]).left`. Rewrite using `[← Over.comp_left]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem famφ_eq (α : D.X) (k : Fin 4) :
    DegPre.famφ D F α k = (DegPre.prB D F).left ≫ D.famφB α k := by
  fin_cases k
  · show (DegPre.prB D F).left = (DegPre.prB D F).left ≫ 𝟙 _
    simp
  · show (padd D.P.A (DegPre.prB D F) (toUnit _ ≫ D.c α)).left =
      (DegPre.prB D F).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    rw [← Over.comp_left]; congr 1; simp [padd, comp_lift_assoc]
  · show (toUnit _ ≫ D.c α).left = (DegPre.prB D F).left ≫ (toUnit D.P.A ≫ D.c α).left
    rw [← Over.comp_left]; congr 1; simp
  · show (toUnit _ ≫ η[D.P.A]).left = (DegPre.prB D F).left ≫ (toUnit D.P.A ≫ η[D.P.A]).left
    rw [← Over.comp_left]; congr 1; simp

/- English proof (translation)
Establish `h` using `Over.w (toUnit T)`. Use `erw [Category.comp_id] at h`. Conclude with `h`.
-/
private theorem toUnit_left_lemma {S : Scheme.{0}} (T : Over S) : (toUnit T).left = T.hom := by
  have h := Over.w (toUnit T)
  erw [Category.comp_id] at h
  exact h

/- English proof (translation)
Rewrite using `[← Over.comp_left]`. Simplify using `only [DegPre.zF, DegPre.prB, lift_snd, Over.comp_left, toUnit_left_lemma]`. Both sides reduce to the same expression.
-/
theorem zF_prB : (DegPre.zF D F).left ≫ (DegPre.prB D F).left =
    DegPre.jFR (R := R) F ≫ (η[D.P.A]).left := by
  rw [← Over.comp_left]
  simp only [DegPre.zF, DegPre.prB, lift_snd, Over.comp_left, toUnit_left_lemma]
  rfl

end Fam

section Eval

def evalTop {A : Type} [CommRing A] (U : (Spec (CommRingCat.of A)).Opens) (hU : U = ⊤) :
    Γ(Spec (CommRingCat.of A), U) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
    ((Spec (CommRingCat.of A)).presheaf.map (homOfLE hU.ge).op).hom

/- English proof (translation)
Establish `: X.presheaf.map i.op ≫ X.presheaf.map j.op = X.presheaf.map k.op`. Rewrite using `[← Functor.map_comp]`. Both sides reduce to the same expression. Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
private theorem res_res_lemma (X : Scheme.{0}) {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) (k : W ⟶ U)
    (a : Γ(X, U)) : (X.presheaf.map j.op).hom ((X.presheaf.map i.op).hom a) = (X.presheaf.map k.op).hom a := by
  have : X.presheaf.map i.op ≫ X.presheaf.map j.op = X.presheaf.map k.op := by
    rw [← Functor.map_comp]; rfl
  rw [← this]; rfl

/- English proof (translation)
Rewrite using `[show i = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]`. Both sides reduce to the same expression.
-/
private theorem presheaf_map_endo_apply (X : Scheme.{0}) {U : X.Opens} (i : U ⟶ U) (a : Γ(X, U)) :
    (X.presheaf.map i.op).hom a = a := by
  rw [show i = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]; rfl

/- English proof (translation)
Simplify using `only [evalTop, RingHom.comp_apply]`. Rewrite using `[res_res_lemma _ _ _ (homOfLE hU.ge)]`.
-/
theorem evalTop_res {A : Type} [CommRing A] {U U' : (Spec (CommRingCat.of A)).Opens} (h : U' ≤ U)
    (hU : U = ⊤) (hU' : U' = ⊤) (a : Γ(Spec (CommRingCat.of A), U)) :
    evalTop U' hU' (((Spec (CommRingCat.of A)).presheaf.map (homOfLE h).op).hom a) = evalTop U hU a := by
  simp only [evalTop, RingHom.comp_apply]
  rw [res_res_lemma _ _ _ (homOfLE hU.ge)]

/- English proof (translation)
Substitute `hU` using the available equality. Simplify using `only [evalTop, RingHom.comp_apply]`. Rewrite using `[show (homOfLE hU'.ge).op = 𝟙 _ from rfl]`. Use `erw [CategoryTheory.Functor.map_id]`. Rewrite using `[presheaf_map_endo_apply]`.

Conclude with `congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))`.
-/
theorem evalTop_specMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (U : (Spec (CommRingCat.of A)).Opens) (hU : U = ⊤)
    (hU' : Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ U = ⊤) (a : Γ(Spec (CommRingCat.of A), U)) :
    evalTop _ hU' (((Spec.map (CommRingCat.ofHom f)).app U).hom a) = f (evalTop U hU a) := by
  subst hU
  simp only [evalTop, RingHom.comp_apply]
  rw [show (homOfLE hU'.ge).op = 𝟙 _ from rfl]
  erw [CategoryTheory.Functor.map_id]
  rw [presheaf_map_endo_apply]
  exact congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

/- English proof (translation)
Substitute `hg` using the available equality. Conclude with `evalTop_specMap f U hU hU' a`.
-/
theorem evalTop_of_eq {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom f))
    (U : (Spec (CommRingCat.of A)).Opens) (hU : U = ⊤) (hU' : g ⁻¹ᵁ U = ⊤)
    (a : Γ(Spec (CommRingCat.of A), U)) :
    evalTop _ hU' ((g.app U).hom a) = f (evalTop U hU a) := by
  subst hg
  exact evalTop_specMap f U hU hU' a

variable {V : Type} [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Substitute `hg` using the available equality. Establish `h1` using `evalTop_of_eq ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))) (DegPre.jFR (R := V) F) (jFR_eq' F) (e ⁻¹ᵁ U) hU hU' ((e.app U).hom a)`. Conclude with `h1`.
-/
theorem evalTop_comp {Y : Scheme.{0}} (g : Spec (CommRingCat.of F) ⟶ Y) (e : Spec (CommRingCat.of V) ⟶ Y)
    (hg : g = DegPre.jFR (R := V) F ≫ e) (U : Y.Opens) (hU : e ⁻¹ᵁ U = ⊤) (hU' : g ⁻¹ᵁ U = ⊤)
    (a : Γ(Y, U)) :
    evalTop _ hU' ((g.app U).hom a) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (evalTop _ hU ((e.app U).hom a))) := by
  subst hg
  have h1 := evalTop_of_eq ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)))
    (DegPre.jFR (R := V) F) (jFR_eq' F) (e ⁻¹ᵁ U) hU hU' ((e.app U).hom a)
  exact h1

end Eval

section EvalMore

/- English proof (translation)
Simplify using `only [evalTop, RingHom.comp_apply]`. Establish `h2` using `congrArg (fun φ => φ.hom a) (g.naturality (homOfLE h).op)`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at h2`. Rewrite using `[h2, res_res_lemma _ _ _ (homOfLE hU.ge)]`.
-/
theorem evalTop_app_res {A : Type} [CommRing A] {Y : Scheme.{0}} (g : Spec (CommRingCat.of A) ⟶ Y)
    {U U' : Y.Opens} (h : U' ≤ U) (hU : g ⁻¹ᵁ U = ⊤) (hU' : g ⁻¹ᵁ U' = ⊤) (a : Γ(Y, U)) :
    evalTop _ hU' ((g.app U').hom ((Y.presheaf.map (homOfLE h).op).hom a)) = evalTop _ hU ((g.app U).hom a) := by
  simp only [evalTop, RingHom.comp_apply]
  have h2 := congrArg (fun φ => φ.hom a) (g.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [h2, res_res_lemma _ _ _ (homOfLE hU.ge)]

/- English proof (translation)
Simplify using `only [evalTop, RingHom.comp_apply]`. Rewrite using `[res_res_lemma _ _ _ (𝟙 (⊤ : (Spec (CommRingCat.of A)).Opens)), op_id, CategoryTheory.Functor.map_id]`. Conclude with `congrArg (fun φ => φ.hom x) (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id`.
-/
theorem evalTop_const {A : Type} [CommRing A] (U : (Spec (CommRingCat.of A)).Opens) (hU : U = ⊤) (x : A) :
    evalTop U hU (((Spec (CommRingCat.of A)).presheaf.map (homOfLE le_top).op).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x)) = x := by
  simp only [evalTop, RingHom.comp_apply]
  rw [res_res_lemma _ _ _ (𝟙 (⊤ : (Spec (CommRingCat.of A)).Opens)), op_id, CategoryTheory.Functor.map_id]
  exact congrArg (fun φ => φ.hom x) (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id

/- English proof (translation)
Simplify using `only [evalTop, RingHom.comp_apply]`. Rewrite using `[show (g₁.app (g₂ ⁻¹ᵁ ⊤)).hom ((g₂.app ⊤).hom y) = ((g₁ ≫ g₂).app ⊤).hom y from rfl, Scheme.Hom.congr_app h, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.id_app]`. Use `erw [res_res_lemma _ _ _ (homOfLE (le_refl (⊤ : (Spec (CommRingCat.of A)).Opens)))]`.
-/
theorem evalTop_comp_id {A : Type} [CommRing A] {Y : Scheme.{0}} (g₁ : Spec (CommRingCat.of A) ⟶ Y)
    (g₂ : Y ⟶ Spec (CommRingCat.of A)) (h : g₁ ≫ g₂ = 𝟙 _) (hU : g₁ ⁻¹ᵁ (g₂ ⁻¹ᵁ ⊤) = ⊤)
    (y : Γ(Spec (CommRingCat.of A), ⊤)) :
    evalTop _ hU ((g₁.app _).hom ((g₂.app ⊤).hom y)) = evalTop ⊤ rfl y := by
  simp only [evalTop, RingHom.comp_apply]
  rw [show (g₁.app (g₂ ⁻¹ᵁ ⊤)).hom ((g₂.app ⊤).hom y) = ((g₁ ≫ g₂).app ⊤).hom y from rfl,
    Scheme.Hom.congr_app h, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.id_app]
  erw [res_res_lemma _ _ _ (homOfLE (le_refl (⊤ : (Spec (CommRingCat.of A)).Opens)))]

end EvalMore

section Val

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Simplify using `[hc]`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hc hϖ`. Establish `hval : HasVal ϖ (algebraMap V (FractionRing V) c) (n : ℤ)` using `⟨u⁻¹, by`. Rewrite using `[zpow_natCast, ← map_pow, ← map_mul]`.

Use `congr 1`. Rewrite using `[← hu, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩`. Rewrite using `[hv _ _ hval]`. Conclude with `WithTop.coe_nonneg.2 (by positivity)`.
-/
theorem v_alg_nonneg (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) (c : V) :
    (0 : WithTop ℚ) ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) := by
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc hϖ
  have hval : HasVal ϖ (algebraMap V (FractionRing V) c) (n : ℤ) := ⟨u⁻¹, by
    rw [zpow_natCast, ← map_pow, ← map_mul]; congr 1
    rw [← hu, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
  rw [hv _ _ hval]
  exact WithTop.coe_nonneg.2 (by positivity)

/- English proof (translation)
Use `hv (algebraMap V (FractionRing V) (u : V)) 0 ⟨u, by simp⟩` as an intermediate fact. Simplify using `using this`.
-/
theorem v_alg_unit (hv : ValOver ϖ F v) (u : Vˣ) :
    v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (u : V))) = 0 := by
  have := hv (algebraMap V (FractionRing V) (u : V)) 0 ⟨u, by simp⟩
  simpa using this

end Val

section PullGen

/- English proof (translation)
Simplify using `only [evalTop, RingHom.comp_apply]`. Rewrite using `[presheaf_map_endo_apply]`.
-/
theorem evalTop_top {A : Type} [CommRing A] (y : Γ(Spec (CommRingCat.of A), ⊤)) :
    evalTop ⊤ rfl y = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y := by
  simp only [evalTop, RingHom.comp_apply]
  rw [presheaf_map_endo_apply]

/- English proof (translation)
Use `top_unique fun x _ => ?_` and prove the remaining obligations. Establish `hx : g.base x ∈ LB.wchart L φ j` using `by rw [hU]; trivial`. Express the relevant statement in the definitionally equal form `x ∈ ⋂ k, (g ≫ φ k).base ⁻¹' (L.U (j k) : Set X)`. Express the relevant statement in the definitionally equal form `g.base x ∈ ⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X) at hx`. Rewrite `hx`, the goal using `[Set.mem_iInter]`.

Introduce `k`. Simplify using `using hx k`.
-/
theorem wchart_top_comp {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (g : Z ⟶ Y) (j : K → L.ι) (hU : LB.wchart L φ j = ⊤) : LB.wchart L (fun k => g ≫ φ k) j = ⊤ := by
  refine top_unique fun x _ => ?_
  have hx : g.base x ∈ LB.wchart L φ j := by rw [hU]; trivial
  change x ∈ ⋂ k, (g ≫ φ k).base ⁻¹' (L.U (j k) : Set X)
  change g.base x ∈ ⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X) at hx
  rw [Set.mem_iInter] at hx ⊢
  intro k
  simpa using hx k

/- English proof (translation)
Establish `hW : g ⁻¹ᵁ LB.wchart L φ j = ⊤` using `by rw [hU, Scheme.Hom.preimage_top]`. Establish `h1` using `evalTop_res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) : LB.wchart L (fun k => g ≫ φ k) j ≤ g ⁻¹ᵁ LB.wchart L φ j) hW hU' ((g.app _).hom (c.s j).val)`. Conclude with `h1.trans (evalTop_of_eq f g hg _ hU hW _)`.
-/
theorem evalTop_pullGen_val {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom f))
    {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of A) ⟶ X)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (j : K → L.ι) (hU : LB.wchart L φ j = ⊤)
    (hU' : LB.wchart L (fun k => g ≫ φ k) j = ⊤) :
    evalTop _ hU' ((LB.pullGen L φ ε c g).s j).val = f (evalTop _ hU (c.s j).val) := by
  have hW : g ⁻¹ᵁ LB.wchart L φ j = ⊤ := by rw [hU, Scheme.Hom.preimage_top]
  have h1 := evalTop_res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
    LB.wchart L (fun k => g ≫ φ k) j ≤ g ⁻¹ᵁ LB.wchart L φ j) hW hU' ((g.app _).hom (c.s j).val)
  exact h1.trans (evalTop_of_eq f g hg _ hU hW _)

end PullGen

section ValMain

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

/- English proof (translation)
Apply the tactic sequence `fin_cases k <;> simp [DegPre.famφB]`.
-/
theorem famφB_over (α : D.toPre.X) (k : Fin 4) :
    D.toPre.famφB α k ≫ D.toPre.P.A.hom = D.toPre.P.A.hom := by
  fin_cases k <;> simp [DegPre.famφB]

/- English proof (translation)
Conclude with `toUnit_left_lemma _`.
-/
theorem toUnit_TK_left : (toUnit (TK V)).left = jK V := by
  exact toUnit_left_lemma _

/- English proof (translation)
Rewrite using `[← Over.comp_left, DegPre.zF, lift_fst, Over.id_left]`.
-/
theorem zF_fst : (DegPre.zF D.toPre F).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = 𝟙 _ := by
  rw [← Over.comp_left, DegPre.zF, lift_fst, Over.id_left]

/- English proof (translation)
Rewrite using `[famφ_eq, ← Category.assoc, zF_prB, Category.assoc]`.
-/
private theorem zF_comp_famφ (α : D.toPre.X) (i : Fin 4) :
    (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i =
      DegPre.jFR (R := V) F ≫ ((η[D.toPre.P.A]).left ≫ D.toPre.famφB α i) := by
  rw [famφ_eq, ← Category.assoc, zF_prB, Category.assoc]

/- English proof (translation)
Use `top_unique fun x _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x ∈ ⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X)`. Rewrite using `[Set.mem_iInter]`. Introduce `k`. Establish `hx : x ∈ φ k ⁻¹ᵁ L.U (j k)` using `by rw [h k]; trivial`.

Conclude with `hx`.
-/
private theorem wchart_eq_whole_of_preimage_eq_whole {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : K → L.ι) (h : ∀ k, φ k ⁻¹ᵁ L.U (j k) = ⊤) : LB.wchart L φ j = ⊤ := by
  refine top_unique fun x _ => ?_
  change x ∈ ⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X)
  rw [Set.mem_iInter]
  intro k
  have hx : x ∈ φ k ⁻¹ᵁ L.U (j k) := by rw [h k]; trivial
  exact hx

/- English proof (translation)
Use `top_unique fun x _ => ?_` and prove the remaining obligations. Establish `hx : x ∈ LB.wchart L (fun k => g ≫ φ k) j` using `by rw [h]; trivial`. Express the relevant statement in the definitionally equal form `x ∈ ⋂ k, (g ≫ φ k).base ⁻¹' (L.U (j k) : Set X) at hx`. Express the relevant statement in the definitionally equal form `g.base x ∈ ⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X)`. Rewrite `hx`, the goal using `[Set.mem_iInter]`.

Introduce `k`. Simplify using `using hx k`.
-/
private theorem preimage_wchart_eq_whole_of_wchart_comp_eq_whole {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (g : Z ⟶ Y) (j : K → L.ι) (h : LB.wchart L (fun k => g ≫ φ k) j = ⊤) :
    g ⁻¹ᵁ LB.wchart L φ j = ⊤ := by
  refine top_unique fun x _ => ?_
  have hx : x ∈ LB.wchart L (fun k => g ≫ φ k) j := by rw [h]; trivial
  change x ∈ ⋂ k, (g ≫ φ k).base ⁻¹' (L.U (j k) : Set X) at hx
  change g.base x ∈ ⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X)
  rw [Set.mem_iInter] at hx ⊢
  intro k
  simpa using hx k

/- English proof (translation)
Rewrite using `[DegPre.constBF, evalTop_app_res _ le_top (Scheme.Hom.preimage_top _) hZ]`. Establish `h1` using `evalTop_comp_id (DegPre.zF D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left zF_fst (by rw [Scheme.Hom.preimage_top, Scheme.Hom.preimage_top]) ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ)`. Rewrite `h1` using `[evalTop_top]`. Conclude with `h1.trans (congrArg (fun φ => φ.hom ζ) (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id)`.
-/
private theorem eval_top_const_section_eq (ζ : F) (W0 : (DegPre.BF D.toPre F).left.Opens)
    (hZ : (DegPre.zF D.toPre F).left ⁻¹ᵁ W0 = ⊤) :
    evalTop _ hZ (((DegPre.zF D.toPre F).left.app W0).hom (DegPre.constBF D.toPre F ζ W0)) = ζ := by
  rw [DegPre.constBF, evalTop_app_res _ le_top (Scheme.Hom.preimage_top _) hZ]
  have h1 := evalTop_comp_id (DegPre.zF D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left zF_fst
    (by rw [Scheme.Hom.preimage_top, Scheme.Hom.preimage_top]) ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ)
  rw [evalTop_top] at h1
  exact h1.trans (congrArg (fun φ => φ.hom ζ) (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id)

/- English proof (translation)
Take `⟨n, a, σ, σF, hσ, ha, hsum⟩` from `hs`. Take `⟨τ, -, hτ, hxj⟩` from `hx`. Establish `hL` using `D.toPre.P.isLB`. Set `ch : (Spec (CommRingCat.of V) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι` to `fun q => Classical.choose (exists_chart_top D.toPre.P.L hL q)`. Establish `hch : ∀ q, q ⁻¹ᵁ D.toPre.P.L.U (ch q) = ⊤` using `fun q => Classical.choose_spec (exists_chart_top D.toPre.P.L hL q)`.

Establish `he : (η[D.toPre.P.A]).left ≫ D.toPre.P.A.hom = 𝟙 _` using `Over.w (η[D.toPre.P.A])`. Establish `heB : ∀ i, ((η[D.toPre.P.A]).left ≫ D.toPre.famφB α i) ≫ D.toPre.P.A.hom = 𝟙 _` using `fun i => by rw [Category.assoc, famφB_over, he]`. Set `j : Fin 4 → D.toPre.P.L.ι` to `fun i => ch ((η[D.toPre.P.A]).left ≫ D.toPre.famφB α i)`. Establish `hinjB : ∀ i i', DegPre.jFR (R` using `V) F ≫ ((η[D.toPre.P.A]).left ≫ D.toPre.famφB α i) = DegPre.jFR (R := V) F ≫ ((η[D.toPre.P.A]).left ≫ D.toPre.famφB α i') → j i = j i' := fun i i' h => congrArg ch (vpt_ext F D.toPre.P (heB i) (heB i') h)`. Establish `hφcoh : ∀ k₁ k₂, DegPre.famφ D.toPre F α k₁ = DegPre.famφ D.toPre F α k₂ → j k₁ = j k₂`.

Introduce `k₁ k₂ h`. Apply `hinjB` to reduce the goal to its premises. Rewrite using `[← zF_comp_famφ, ← zF_comp_famφ, h]`. Establish `hWB : LB.wchart D.toPre.P.L (fun i => (η[D.toPre.P.A]).left ≫ D.toPre.famφB α i) j = ⊤` using `wchart_eq_whole_of_preimage_eq_whole _ _ _ (fun i => hch _)`. Establish `hW : LB.wchart D.toPre.P.L (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) j = ⊤`.

Establish `h` using `wchart_top_comp D.toPre.P.L (fun i => (η[D.toPre.P.A]).left ≫ D.toPre.famφB α i) (DegPre.jFR (R := V) F) j hWB`. Simplify `h` using `only [zF_comp_famφ]`. Establish `hZ : (DegPre.zF D.toPre F).left ⁻¹ᵁ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F α) j = ⊤` using `preimage_wchart_eq_whole_of_wchart_comp_eq_whole _ _ _ _ hW`. Establish `hC` using `hτ j (fun _ => ch (η[D.toPre.P.A]).left) (fun k₁ k₂ h => by`. Simplify using `only [zF_comp_famφ] at h`.

Conclude with `hinjB k₁ k₂ h)`. Use the proof step `(fun _ _ _ => rfl)`. Use the proof step `(fun k u h => by`. Establish `key2 : jFK (R` using `V) F ≫ ((toUnit (TK V)).left ≫ eSec D.toPre.P.A) = DegPre.jFR (R := V) F ≫ (η[D.toPre.P.A]).left := by`. Rewrite using `[toUnit_TK_left]`.

Simplify using `only [eSec, DegPre.jFR, Category.assoc]`. Simplify using `only [zF_comp_famφ, key2] at h`. Conclude with `congrArg ch (vpt_ext F D.toPre.P (heB k) he h))`. Establish `hW' : LB.wchart D.toPre.P.L (fun _ : PUnit.{1} => jFK (R` using `V) F ≫ ((toUnit (TK V)).left ≫ eSec D.toPre.P.A)) (fun _ => ch (η[D.toPre.P.A]).left) = ⊤ := wchart_eq_whole_of_preimage_eq_whole _ _ _ (fun _ => by`. Simplify using `only [Scheme.Hom.comp_preimage]`.

Rewrite using `[show (eSec D.toPre.P.A) ⁻¹ᵁ D.toPre.P.L.U (ch (η[D.toPre.P.A]).left) = ⊤ from hch _, Scheme.Hom.preimage_top, Scheme.Hom.preimage_top])`. Establish `hUK : LB.wchart D.toPre.P.L (fun _ : PUnit.{1} => (toUnit (TK V)).left ≫ eSec D.toPre.P.A) (fun _ => ch (η[D.toPre.P.A]).left) = ⊤` using `wchart_eq_whole_of_preimage_eq_whole _ _ _ (fun _ => by`. Simplify using `only [Scheme.Hom.comp_preimage]`. Rewrite using `[show (eSec D.toPre.P.A) ⁻¹ᵁ D.toPre.P.L.U (ch (η[D.toPre.P.A]).left) = ⊤ from hch _, Scheme.Hom.preimage_top])`. Establish `hUV : LB.wchart D.toPre.P.L (fun _ : PUnit.{1} => eSec D.toPre.P.A) (fun _ => ch (η[D.toPre.P.A]).left) = ⊤` using `wchart_eq_whole_of_preimage_eq_whole _ _ _ (fun _ => hch _)`.

Establish `hIv : LB.wchart D.toPre.P.L (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) j ⊓ LB.wchart D.toPre.P.L (fun _ : PUnit.{1} => jFK (R` using `V) F ≫ ((toUnit (TK V)).left ≫ eSec D.toPre.P.A)) (fun _ => ch (η[D.toPre.P.A]).left) = ⊤ := by`. Rewrite using `[hW, hW', top_inf_eq]`. Establish `hT : evalTop _ hW (τ.s j).val = evalTop _ hW' ((LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK k) (jFK (R` using `V) F)).s (fun _ => ch (η[D.toPre.P.A]).left)).val := by erw [← evalTop_res inf_le_left hW hIv, ← evalTop_res inf_le_right hW' hIv]`. Conclude with `congrArg (fun u => evalTop _ hIv (Units.val u)) hC`. Take `⟨w, hw⟩ : ∃ w : Vˣ, evalTop _ hUV (D.toPre.rig.s (fun _ => ch (η[D.toPre.P.A]).left)).val = (w : V)` from `⟨Units.map (evalTop _ hUV).toMonoidHom (D.toPre.rig.s _), rfl⟩`.

Establish `hT2 : evalTop _ hW' ((LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK k) (jFK (R` using `V) F)).s (fun _ => ch (η[D.toPre.P.A]).left)).val = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w : V)) ^ k := by`. Establish `h2` using `evalTop_pullGen_val (algebraMap (FractionRing V) F) (jFK (R := V) F) rfl D.toPre.P.L (fun _ : PUnit.{1} => (toUnit (TK V)).left ≫ eSec D.toPre.P.A) (fun _ => (k : ℤ) * 1) (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK k) (fun _ => ch (η[D.toPre.P.A]).left) hUK hW'`. Establish `h3` using `evalTop_pullGen_val (algebraMap V (FractionRing V)) ((toUnit (TK V)).left) toUnit_TK_left D.toPre.P.L (fun _ : PUnit.{1} => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig (fun _ => ch (η[D.toPre.P.A]).left) hUV hUK`. Rewrite `h3` using `[hw]`. Establish `h4 : evalTop _ hUK ((GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK k).s (fun _ => ch (η[D.toPre.P.A]).left)).val = (evalTop _ hUK (D.toPre.rigK.s (fun _ => ch (η[D.toPre.P.A]).left)).val) ^ k` using `map_pow (evalTop _ hUK) _ k`.

Use `h2.trans ?_` and prove the remaining obligations. Rewrite using `[h4, map_pow]`. Use `congr 1`. Rewrite using `[DegPre.rigK]`. Conclude with `congrArg (algebraMap (FractionRing V) F) h3`.

Establish `hvT : v (evalTop _ hW (τ.s j).val) = 0`. Rewrite using `[hT, hT2, AddValuation.map_pow, v_alg_unit hv w, smul_zero]`. Establish `hE` using `congrArg (evalTop _ hW) (hxj j)`. Use `erw [map_mul, evalTop_const, evalTop_res _ hZ hW] at hE`. Rewrite `hE` using `[hsum j, map_sum]`.

Establish `hE2 : ∑ i, a i * evalTop _ hZ (((DegPre.zF D.toPre F).left.app _).hom ((σF i).f j)) = x * evalTop _ hW (τ.s j).val`. Use `Eq.trans ?_ hE` and prove the remaining obligations. Use `Eq.trans ?_ (map_sum (evalTop _ hZ) _ _).symm` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Use `erw [map_mul, eval_top_const_section_eq _ _ hZ]`. Both sides reduce to the same expression. Establish `hfam : (fun k => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α k) = DegPre.famφ D.toPre F α`. Use function extensionality and compare the values at `fun k => (famφ_eq D.toPre F α k).symm`. Establish `hZ' : (DegPre.zF D.toPre F).left ⁻¹ᵁ LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α k) j = ⊤`.

Rewrite using `[hfam]`. Conclude with `hZ`. Establish `hZ'' : (DegPre.zF D.toPre F).left ⁻¹ᵁ (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F α) j ⊓ LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α k) j) = ⊤`. Use `top_unique fun y _ => ?_` and prove the remaining obligations. Establish `h1 : y ∈ (DegPre.zF D.toPre F).left ⁻¹ᵁ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F α) j`.

Rewrite using `[hZ]`. Discharge the goal by the elementary cases of `trivial`. Establish `h2 : y ∈ (DegPre.zF D.toPre F).left ⁻¹ᵁ LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α k) j`. Rewrite using `[hZ']`. Discharge the goal by the elementary cases of `trivial`.

Use `show (DegPre.zF D.toPre F).left.base y ∈ (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F α) j ⊓ LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α k) j)`. Conclude with `TopologicalSpace.Opens.mem_inf.2 ⟨h1, h2⟩`. Establish `hηU : (η[D.toPre.P.A]).left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) j = ⊤` using `preimage_wchart_eq_whole_of_wchart_comp_eq_whole D.toPre.P.L (D.toPre.famφB α) (η[D.toPre.P.A]).left j hWB`. Establish `hP : ((DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left) ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) j = ⊤`. Rewrite using `[zF_prB, Scheme.Hom.comp_preimage, hηU, Scheme.Hom.preimage_top]`.

Establish `hbnn : ∀ i, (0 : WithTop ℚ) ≤ v (evalTop _ hZ (((DegPre.zF D.toPre F).left.app _).hom ((σF i).f j)))`. Introduce `i`. Establish `hs'` using `hσ i j j (by`. Introduce `k₁ k₂ h`. Apply the tactic sequence `rcases k₁ with k₁ | k₁ <;> rcases k₂ with k₂ | k₂ <;>`.

Apply the tactic sequence `simp only [Sum.elim_inl, Sum.elim_inr, ← famφ_eq] at h ⊢ <;> exact hφcoh _ _ h)`. Simplify using `only [resTop, map_one, _root_.one_mul] at hs'`. Use `erw [← evalTop_app_res _ inf_le_left hZ hZ'', ← hs', evalTop_app_res _ _ (by rw [← Scheme.Hom.comp_preimage]; exact hP) hZ'']`. Establish `hb` using `evalTop_comp F ((DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left) (η[D.toPre.P.A]).left (zF_prB D.toPre F) (LB.wchart D.toPre.P.L (D.toPre.famφB α) j) hηU hP ((σ i).f j)`. Conclude with `le_of_le_of_eq (v_alg_nonneg hϖ hv _) (congrArg v hb).symm`.

Establish `hterm : ∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (a i * evalTop _ hZ (((DegPre.zF D.toPre F).left.app _).hom ((σF i).f j)))` using `fun i => by`. Rewrite using `[AddValuation.map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hvx : v (x * evalTop _ hW (τ.s j).val) = v x` using `by rw [AddValuation.map_mul, hvT, add_zero]`. Rewrite using `[← hvx, ← hE2]`.

Conclude with `Finset.sum_induction _ (fun y => ((r : ℚ) : WithTop ℚ) ≤ v y) (fun y z hy hz => le_trans (le_min hy hz) (v.map_add y z)) (by simp) (fun i _ => hterm i)`.
-/
theorem valuation_ge_at_zero (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {r : ℚ} {x : F}
    (hs : VGe D F v k α s r) (hx : Val0 D F k α s x) : ((r : ℚ) : WithTop ℚ) ≤ v x := by
  classical
  obtain ⟨n, a, σ, σF, hσ, ha, hsum⟩ := hs
  obtain ⟨τ, -, hτ, hxj⟩ := hx
  have hL := D.toPre.P.isLB
  let ch : (Spec (CommRingCat.of V) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι :=
    fun q => Classical.choose (exists_chart_top D.toPre.P.L hL q)
  have hch : ∀ q, q ⁻¹ᵁ D.toPre.P.L.U (ch q) = ⊤ :=
    fun q => Classical.choose_spec (exists_chart_top D.toPre.P.L hL q)
  have he : (η[D.toPre.P.A]).left ≫ D.toPre.P.A.hom = 𝟙 _ := Over.w (η[D.toPre.P.A])
  have heB : ∀ i, ((η[D.toPre.P.A]).left ≫ D.toPre.famφB α i) ≫ D.toPre.P.A.hom = 𝟙 _ :=
    fun i => by rw [Category.assoc, famφB_over, he]
  let j : Fin 4 → D.toPre.P.L.ι := fun i => ch ((η[D.toPre.P.A]).left ≫ D.toPre.famφB α i)
  have hinjB : ∀ i i', DegPre.jFR (R := V) F ≫ ((η[D.toPre.P.A]).left ≫ D.toPre.famφB α i) =
      DegPre.jFR (R := V) F ≫ ((η[D.toPre.P.A]).left ≫ D.toPre.famφB α i') → j i = j i' :=
    fun i i' h => congrArg ch (vpt_ext F D.toPre.P (heB i) (heB i') h)
  have hφcoh : ∀ k₁ k₂, DegPre.famφ D.toPre F α k₁ = DegPre.famφ D.toPre F α k₂ → j k₁ = j k₂ := by
    intro k₁ k₂ h
    apply hinjB
    rw [← zF_comp_famφ, ← zF_comp_famφ, h]
  have hWB : LB.wchart D.toPre.P.L (fun i => (η[D.toPre.P.A]).left ≫ D.toPre.famφB α i) j = ⊤ :=
    wchart_eq_whole_of_preimage_eq_whole _ _ _ (fun i => hch _)
  have hW : LB.wchart D.toPre.P.L (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) j = ⊤ := by
    have h := wchart_top_comp D.toPre.P.L (fun i => (η[D.toPre.P.A]).left ≫ D.toPre.famφB α i)
      (DegPre.jFR (R := V) F) j hWB
    simpa only [zF_comp_famφ] using h
  have hZ : (DegPre.zF D.toPre F).left ⁻¹ᵁ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F α) j = ⊤ :=
    preimage_wchart_eq_whole_of_wchart_comp_eq_whole _ _ _ _ hW
  have hC := hτ j (fun _ => ch (η[D.toPre.P.A]).left)
    (fun k₁ k₂ h => by
      simp only [zF_comp_famφ] at h
      exact hinjB k₁ k₂ h)
    (fun _ _ _ => rfl)
    (fun k u h => by
      have key2 : jFK (R := V) F ≫ ((toUnit (TK V)).left ≫ eSec D.toPre.P.A) =
          DegPre.jFR (R := V) F ≫ (η[D.toPre.P.A]).left := by
        rw [toUnit_TK_left]; simp only [eSec, DegPre.jFR, Category.assoc]
      simp only [zF_comp_famφ, key2] at h
      exact congrArg ch (vpt_ext F D.toPre.P (heB k) he h))
  have hW' : LB.wchart D.toPre.P.L (fun _ : PUnit.{1} => jFK (R := V) F ≫ ((toUnit (TK V)).left ≫ eSec D.toPre.P.A))
      (fun _ => ch (η[D.toPre.P.A]).left) = ⊤ :=
    wchart_eq_whole_of_preimage_eq_whole _ _ _ (fun _ => by
      simp only [Scheme.Hom.comp_preimage]
      rw [show (eSec D.toPre.P.A) ⁻¹ᵁ D.toPre.P.L.U (ch (η[D.toPre.P.A]).left) = ⊤ from hch _,
        Scheme.Hom.preimage_top, Scheme.Hom.preimage_top])
  have hUK : LB.wchart D.toPre.P.L (fun _ : PUnit.{1} => (toUnit (TK V)).left ≫ eSec D.toPre.P.A)
      (fun _ => ch (η[D.toPre.P.A]).left) = ⊤ :=
    wchart_eq_whole_of_preimage_eq_whole _ _ _ (fun _ => by
      simp only [Scheme.Hom.comp_preimage]
      rw [show (eSec D.toPre.P.A) ⁻¹ᵁ D.toPre.P.L.U (ch (η[D.toPre.P.A]).left) = ⊤ from hch _,
        Scheme.Hom.preimage_top])
  have hUV : LB.wchart D.toPre.P.L (fun _ : PUnit.{1} => eSec D.toPre.P.A)
      (fun _ => ch (η[D.toPre.P.A]).left) = ⊤ :=
    wchart_eq_whole_of_preimage_eq_whole _ _ _ (fun _ => hch _)
  have hIv : LB.wchart D.toPre.P.L (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) j ⊓
      LB.wchart D.toPre.P.L (fun _ : PUnit.{1} => jFK (R := V) F ≫ ((toUnit (TK V)).left ≫ eSec D.toPre.P.A))
        (fun _ => ch (η[D.toPre.P.A]).left) = ⊤ := by
    rw [hW, hW', top_inf_eq]
  have hT : evalTop _ hW (τ.s j).val = evalTop _ hW' ((LB.pullGen D.toPre.P.L _ _
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK k) (jFK (R := V) F)).s (fun _ => ch (η[D.toPre.P.A]).left)).val := by
    erw [← evalTop_res inf_le_left hW hIv, ← evalTop_res inf_le_right hW' hIv]
    exact congrArg (fun u => evalTop _ hIv (Units.val u)) hC
  obtain ⟨w, hw⟩ : ∃ w : Vˣ, evalTop _ hUV (D.toPre.rig.s (fun _ => ch (η[D.toPre.P.A]).left)).val = (w : V) :=
    ⟨Units.map (evalTop _ hUV).toMonoidHom (D.toPre.rig.s _), rfl⟩
  have hT2 : evalTop _ hW' ((LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK k)
      (jFK (R := V) F)).s (fun _ => ch (η[D.toPre.P.A]).left)).val =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w : V)) ^ k := by
    have h2 := evalTop_pullGen_val (algebraMap (FractionRing V) F) (jFK (R := V) F) rfl D.toPre.P.L
      (fun _ : PUnit.{1} => (toUnit (TK V)).left ≫ eSec D.toPre.P.A) (fun _ => (k : ℤ) * 1)
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK k) (fun _ => ch (η[D.toPre.P.A]).left) hUK hW'
    have h3 := evalTop_pullGen_val (algebraMap V (FractionRing V)) ((toUnit (TK V)).left) toUnit_TK_left
      D.toPre.P.L (fun _ : PUnit.{1} => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig
      (fun _ => ch (η[D.toPre.P.A]).left) hUV hUK
    rw [hw] at h3
    have h4 : evalTop _ hUK ((GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK k).s
        (fun _ => ch (η[D.toPre.P.A]).left)).val =
        (evalTop _ hUK (D.toPre.rigK.s (fun _ => ch (η[D.toPre.P.A]).left)).val) ^ k :=
      map_pow (evalTop _ hUK) _ k
    refine h2.trans ?_
    rw [h4, map_pow]
    congr 1
    rw [DegPre.rigK]
    exact congrArg (algebraMap (FractionRing V) F) h3
  have hvT : v (evalTop _ hW (τ.s j).val) = 0 := by
    rw [hT, hT2, AddValuation.map_pow, v_alg_unit hv w, smul_zero]
  have hE := congrArg (evalTop _ hW) (hxj j)
  erw [map_mul, evalTop_const, evalTop_res _ hZ hW] at hE
  rw [hsum j, map_sum] at hE
  have hE2 : ∑ i, a i * evalTop _ hZ (((DegPre.zF D.toPre F).left.app _).hom ((σF i).f j)) =
      x * evalTop _ hW (τ.s j).val := by
    refine Eq.trans ?_ hE
    refine Eq.trans ?_ (map_sum (evalTop _ hZ) _ _).symm
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    erw [map_mul, eval_top_const_section_eq _ _ hZ]
    rfl
  have hfam : (fun k => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α k) = DegPre.famφ D.toPre F α :=
    funext fun k => (famφ_eq D.toPre F α k).symm
  have hZ' : (DegPre.zF D.toPre F).left ⁻¹ᵁ LB.wchart D.toPre.P.L
      (fun k => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α k) j = ⊤ := by
    rw [hfam]; exact hZ
  have hZ'' : (DegPre.zF D.toPre F).left ⁻¹ᵁ (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F α) j ⊓
      LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α k) j) = ⊤ := by
    refine top_unique fun y _ => ?_
    have h1 : y ∈ (DegPre.zF D.toPre F).left ⁻¹ᵁ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F α) j := by
      rw [hZ]; trivial
    have h2 : y ∈ (DegPre.zF D.toPre F).left ⁻¹ᵁ LB.wchart D.toPre.P.L
        (fun k => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α k) j := by
      rw [hZ']; trivial
    show (DegPre.zF D.toPre F).left.base y ∈ (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F α) j ⊓
      LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α k) j)
    exact TopologicalSpace.Opens.mem_inf.2 ⟨h1, h2⟩
  have hηU : (η[D.toPre.P.A]).left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) j = ⊤ :=
    preimage_wchart_eq_whole_of_wchart_comp_eq_whole D.toPre.P.L (D.toPre.famφB α) (η[D.toPre.P.A]).left j hWB
  have hP : ((DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left) ⁻¹ᵁ
      LB.wchart D.toPre.P.L (D.toPre.famφB α) j = ⊤ := by
    rw [zF_prB, Scheme.Hom.comp_preimage, hηU, Scheme.Hom.preimage_top]
  have hbnn : ∀ i, (0 : WithTop ℚ) ≤ v (evalTop _ hZ (((DegPre.zF D.toPre F).left.app _).hom ((σF i).f j))) := by
    intro i
    have hs' := hσ i j j (by
      intro k₁ k₂ h
      rcases k₁ with k₁ | k₁ <;> rcases k₂ with k₂ | k₂ <;>
        simp only [Sum.elim_inl, Sum.elim_inr, ← famφ_eq] at h ⊢ <;> exact hφcoh _ _ h)
    simp only [resTop, map_one, _root_.one_mul] at hs'
    erw [← evalTop_app_res _ inf_le_left hZ hZ'', ← hs',
      evalTop_app_res _ _ (by rw [← Scheme.Hom.comp_preimage]; exact hP) hZ'']
    have hb := evalTop_comp F ((DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left)
      (η[D.toPre.P.A]).left (zF_prB D.toPre F) (LB.wchart D.toPre.P.L (D.toPre.famφB α) j) hηU hP ((σ i).f j)
    exact le_of_le_of_eq (v_alg_nonneg hϖ hv _) (congrArg v hb).symm
  have hterm : ∀ i, ((r : ℚ) : WithTop ℚ) ≤
      v (a i * evalTop _ hZ (((DegPre.zF D.toPre F).left.app _).hom ((σF i).f j))) := fun i => by
    rw [AddValuation.map_mul]
    calc ((r : ℚ) : WithTop ℚ) = ((r : ℚ) : WithTop ℚ) + 0 := (add_zero _).symm
      _ ≤ _ := add_le_add (ha i) (hbnn i)
  have hvx : v (x * evalTop _ hW (τ.s j).val) = v x := by rw [AddValuation.map_mul, hvT, add_zero]
  rw [← hvx, ← hE2]
  exact Finset.sum_induction _ (fun y => ((r : ℚ) : WithTop ℚ) ≤ v y)
    (fun y z hy hz => le_trans (le_min hy hz) (v.map_add y z)) (by simp) (fun i _ => hterm i)

end ValMain

end ReciprocityTheory.ChartRestriction.G.DVR.GC
