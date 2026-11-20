import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialFibreTestGeometricTestStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricTestMapClassicalPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreTorsionEqReductions
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionExtendingTorsionPointsSupportStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TorsionValue

/- English proof (translation)
Establish `h` using `isGrpPullback_pullback H r`. Set `c' : baseOver B' ⟶ (Over.pullback r).obj H` to `Over.homMk (pullback.lift c.left (𝟙 B') ((Over.w c).trans (Category.id_comp r).symm)) (pullback.lift_snd _ _ _)`. Establish `e : c'.left ≫ pullback.fst H.hom r = c.left` using `pullback.lift_fst _ _ _`. Set `U : Over.mk ((baseOver B').hom ≫ r) ⟶ Over.mk r` to `Over.homMk (𝟙 B') rfl`. Establish `e₁ : pushHom h _ c' = preHom U c` using `Over.OverMorphism.ext (e.trans (Category.id_comp _).symm)`.

Establish `e₂ : pushHom h _ (c' ^ n) = pushHom h _ 1`. Rewrite using `[map_pow, e₁, ← map_pow, hc, map_one, map_one]`. Use `⟨c', ?_, e⟩` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `h.1.hom_ext` to reduce the goal to its premises.

Conclude with `congrArg (fun z => z.left) e₂`. Rewrite using `[Over.w, Over.w]`.
-/
theorem exists_torsion_pullback {B B' : Scheme.{0}} (H : Over B) [GrpObj H] (r : B' ⟶ B) (c : Over.mk r ⟶ H) (n : ℕ)
    (hc : c ^ n = 1) : ∃ c' : baseOver B' ⟶ (Over.pullback r).obj H, c' ^ n = 1 ∧
      c'.left ≫ pullback.fst H.hom r = c.left := by
  have h := isGrpPullback_pullback H r
  let c' : baseOver B' ⟶ (Over.pullback r).obj H :=
    Over.homMk (pullback.lift c.left (𝟙 B') ((Over.w c).trans (Category.id_comp r).symm)) (pullback.lift_snd _ _ _)
  have e : c'.left ≫ pullback.fst H.hom r = c.left := pullback.lift_fst _ _ _
  let U : Over.mk ((baseOver B').hom ≫ r) ⟶ Over.mk r := Over.homMk (𝟙 B') rfl
  have e₁ : pushHom h _ c' = preHom U c := Over.OverMorphism.ext (e.trans (Category.id_comp _).symm)
  have e₂ : pushHom h _ (c' ^ n) = pushHom h _ 1 := by
    rw [map_pow, e₁, ← map_pow, hc, map_one, map_one]
  refine ⟨c', ?_, e⟩
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · exact congrArg (fun z => z.left) e₂
  · rw [Over.w, Over.w]

/- English proof (translation)
Set `k : τ.V →+* PadicAlgCl p` to `(GlobalTheory.ZJ.OO p).subtype.comp τ.j`. Establish `hk : Function.Injective k` using `Subtype.val_injective.comp τ.j_inj`. Establish `e : GlobalTheory.ZJ.gPt p ≫ spMap τ.j = spMap (IsFractionRing.lift (K` using `FractionRing τ.V) hk) ≫ jK τ.V := by`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`.

Use extensionality with `x`. Conclude with `(IsFractionRing.lift_algebraMap (K := FractionRing τ.V) hk x).symm`. Establish `e2 : GlobalTheory.ZJ.gPt p ≫ y = (spMap (IsFractionRing.lift (K` using `FractionRing τ.V) hk) ≫ τ.yK) ≫ C.U.ι := by`. Rewrite using `[Category.assoc, τ.yK_fac, ← Category.assoc, ← e, Category.assoc, τ.fac]`. Unfold `GlobalTheory.ZJ.Core.Cl`.

Rewrite using `[e2]`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `((spMap (IsFractionRing.lift (K := FractionRing τ.V) hk) ≫ τ.yK) w).2`.
-/
theorem cl_of_test {C : GlobalTheory.ZJ.Core} {p : ℕ} [Fact p.Prime] {y : Sp (GlobalTheory.ZJ.OO p) ⟶ C.Z} (τ : C.Test y) : C.Cl y := by
  let k : τ.V →+* PadicAlgCl p := (GlobalTheory.ZJ.OO p).subtype.comp τ.j
  have hk : Function.Injective k := Subtype.val_injective.comp τ.j_inj
  have e : GlobalTheory.ZJ.gPt p ≫ spMap τ.j = spMap (IsFractionRing.lift (K := FractionRing τ.V) hk) ≫ jK τ.V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (IsFractionRing.lift_algebraMap (K := FractionRing τ.V) hk x).symm
  have e2 : GlobalTheory.ZJ.gPt p ≫ y = (spMap (IsFractionRing.lift (K := FractionRing τ.V) hk) ≫ τ.yK) ≫ C.U.ι := by
    rw [Category.assoc, τ.yK_fac, ← Category.assoc, ← e, Category.assoc, τ.fac]
  unfold GlobalTheory.ZJ.Core.Cl
  rw [e2]
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact ((spMap (IsFractionRing.lift (K := FractionRing τ.V) hk) ≫ τ.yK) w).2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Conclude with `(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (OO p).subtype).2 (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (OO p).subtype_injective]; exact bot_le)`.
-/
theorem isDominant_gPt (p : ℕ) [Fact p.Prime] : IsDominant (gPt p) := by
  constructor
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (OO p).subtype).2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (OO p).subtype_injective]; exact bot_le)

/- English proof (translation)
Establish `hr : Set.range y ⊆ Set.range W.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `((IsLocalRing.specializes_closedPoint w).map y.continuous).mem_open W.isOpen hy`. Establish `hy' : IsOpenImmersion.lift W.ι y hr ≫ W.ι = y` using `IsOpenImmersion.lift_fac _ _ _`.

Use `⟨_, hy', ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono W.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, hy', hx]`.
-/
theorem exists_lift {Z : Scheme.{0}} {N W : Z.Opens} (hN : N ≤ W) {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ Z)
    (hy : y (cPt p) ∈ W) (x : Sp (kb p) ⟶ N.toScheme) (hx : x ≫ N.ι = rPt p ≫ y) :
    ∃ y' : Sp (OO p) ⟶ W.toScheme, y' ≫ W.ι = y ∧ x ≫ Z.homOfLE hN = rPt p ≫ y' := by
  have hr : Set.range y ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint w).map y.continuous).mem_open W.isOpen hy
  have hy' : IsOpenImmersion.lift W.ι y hr ≫ W.ι = y := IsOpenImmersion.lift_fac _ _ _
  refine ⟨_, hy', ?_⟩
  rw [← cancel_mono W.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, hy', hx]

/- English proof (translation)
Rewrite using `[← cancel_mono j]`. Simplify using `only [Category.assoc] at h₃ ⊢`. Rewrite using `[reassoc_of% h₁, h₂, reassoc_of% h₃, h₄, reassoc_of% h₅]`.
-/
theorem chase {k O N W G P H H' Φ X V : Scheme.{0}} {x : k ⟶ N} {i : N ⟶ W} {h : W ⟶ G} {j : G ⟶ P} [Mono j]
    {r : k ⟶ O} {y' : O ⟶ W} {c₁ : O ⟶ X} {f : X ⟶ V} {κ : V ⟶ P} {c' : k ⟶ H'} {e : H' ⟶ Φ} {s : Φ ⟶ X}
    {q : H' ⟶ H} {g : H ⟶ G} {c : k ⟶ H} (h₁ : x ≫ i = r ≫ y') (h₂ : y' ≫ h ≫ j = c₁ ≫ f ≫ κ)
    (h₃ : r ≫ c₁ = (c' ≫ e) ≫ s) (h₄ : e ≫ s ≫ f ≫ κ = q ≫ g ≫ j) (h₅ : c' ≫ q = c) : x ≫ i ≫ h = c ≫ g := by
  rw [← cancel_mono j]
  simp only [Category.assoc] at h₃ ⊢
  rw [reassoc_of% h₁, h₂, reassoc_of% h₃, h₄, reassoc_of% h₅]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}

/- English proof (translation)
Take `⟨e, -, he⟩` from `t.mt`. Use `(he a 0).2 (by rw [map_zero]; exact ha)` as an intermediate fact. Conclude with `this`.
-/
theorem mem_ker (t : ρ.GeoTest p y₀) {a : S.Gam} (ha : a ∈ t.l.yy.ker) : a ∈ t.τ.yy.ker := by
  obtain ⟨e, -, he⟩ := t.mt
  have := (he a 0).2 (by rw [map_zero]; exact ha)
  exact this

/- English proof (translation)
Use `Q.proper` as an intermediate fact. Use `isDominant_gPt p` as an intermediate fact. Establish `e : gPt p ≫ spMap t.u.j = jFK (R` using `t.u.V) (PadicAlgCl p) ≫ jK t.u.V := by`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression.

Establish `e₀ : jFK (R` using `t.u.V) (PadicAlgCl p) ≫ spMap t.u.yK = spMap y₀ := by`. Use `Eq.trans ?_ (congrArg spMap t.u.fac)` and prove the remaining obligations. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Set `α : Sp (PadicAlgCl p) ⟶ pullback t.u.G.hom (jK t.u.V)` to `a'.left`.

Establish `ha : α ≫ pullback.snd _ _ = jFK (R` using `t.u.V) (PadicAlgCl p) := Over.w a'`. Establish `hs : (α ≫ tm.φ) ≫ pullback.snd _ _ = jFK (R` using `t.u.V) (PadicAlgCl p) ≫ c.yK := by`. Rewrite using `[Category.assoc, tm.φ_snd, ← Category.assoc, ha]`. Use `ext_of_isDominant_of_isSeparated Q.P.hom ?_ (gPt p) ?_` and prove the remaining obligations. Simplify using `only [Category.assoc]`.

Rewrite using `[hh, hy, tm.f_over, ← Category.assoc, h₁, c.fac]`. Establish `k` using `hgen (gPt p ≫ y') (α ≫ tm.φ) ?_ ?_`. Rewrite `k` using `[Category.assoc, Category.assoc, tm.φ_f]`. Rewrite using `[k, ← Category.assoc (gPt p), h₂]`. Conclude with `(Category.assoc _ _ _).symm`.

Rewrite using `[← Category.assoc (α ≫ tm.φ), hs, Category.assoc, Category.assoc, hy, c.yK_fac, ← Category.assoc, ← e, Category.assoc, c.fac]`. Rewrite using `[← Category.assoc (α ≫ tm.φ), hs, Category.assoc, Category.assoc, tm.φ_fst, ← Category.assoc c.yK, c.yK_u, ← Category.assoc (jFK _), e₀]`. Conclude with `h₃`.
-/
theorem integral_eq_section {Q : Clos ρ M U₀ EE} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u} (tm : Q.TMap t c)
    {a : S.Gam} {W : M.Z.Opens} {h : W.toScheme ⟶ Q.G.toScheme} (hh : h ≫ Q.G.ι ≫ Q.P.hom = W.ι)
    (hgen : ∀ (x : Sp (PadicAlgCl p) ⟶ W.toScheme) (x' : Sp (PadicAlgCl p) ⟶ pullback ρ.P.A.hom Q.u₀),
      x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι →
      x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left → x ≫ h ≫ Q.G.ι = x' ≫ Q.a₀)
    {y' : Sp (OO p) ⟶ W.toScheme} (hy : y' ≫ W.ι = y) {c₁ : Sp (OO p) ⟶ t.u.G.left} {a' : t.u.PtC}
    (h₁ : c₁ ≫ t.u.G.hom = spMap t.u.j) (h₂ : gPt p ≫ c₁ = t.u.toG a')
    (h₃ : t.u.toA a' = spMap y₀ ≫ (ρ.pt a).left) :
    y' ≫ h ≫ Q.G.ι = c₁ ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := by
  have := Q.proper
  have := isDominant_gPt p
  have e : gPt p ≫ spMap t.u.j = jFK (R := t.u.V) (PadicAlgCl p) ≫ jK t.u.V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have e₀ : jFK (R := t.u.V) (PadicAlgCl p) ≫ spMap t.u.yK = spMap y₀ := by
    refine Eq.trans ?_ (congrArg spMap t.u.fac)
    rw [← Spec.map_comp]
    rfl
  let α : Sp (PadicAlgCl p) ⟶ pullback t.u.G.hom (jK t.u.V) := a'.left
  have ha : α ≫ pullback.snd _ _ = jFK (R := t.u.V) (PadicAlgCl p) := Over.w a'
  have hs : (α ≫ tm.φ) ≫ pullback.snd _ _ = jFK (R := t.u.V) (PadicAlgCl p) ≫ c.yK := by
    rw [Category.assoc, tm.φ_snd, ← Category.assoc, ha]
  refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ (gPt p) ?_
  · simp only [Category.assoc]
    rw [hh, hy, tm.f_over, ← Category.assoc, h₁, c.fac]
  · have k := hgen (gPt p ≫ y') (α ≫ tm.φ) ?_ ?_
    · rw [Category.assoc, Category.assoc, tm.φ_f] at k
      rw [k, ← Category.assoc (gPt p), h₂]
      exact (Category.assoc _ _ _).symm
    · rw [← Category.assoc (α ≫ tm.φ), hs, Category.assoc, Category.assoc, hy, c.yK_fac, ← Category.assoc, ← e,
        Category.assoc, c.fac]
    · rw [← Category.assoc (α ≫ tm.φ), hs, Category.assoc, Category.assoc, tm.φ_fst, ← Category.assoc c.yK, c.yK_u,
        ← Category.assoc (jFK _), e₀]
      exact h₃

/- English proof (translation)
Introduce `hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hS hG hF z _`. Establish `: NeZero (S.r * S.N)` using `⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩`. Use `choose W h hz hh hgen using fun a : S.HH M z => GlobalTheory.T.exists_section_extending_torsionPoints_support hL o Ω S ρ M U₀ EE hB Q z a.1 a.2`. Set `N : M.Z.Opens` to `⟨⋂ a, (W a : Set M.Z), isOpen_iInter_of_finite fun a => (W a).isOpen⟩`. Establish `hN : ∀ a, N ≤ W a` using `fun a w hw => Set.mem_iInter.1 hw a`.

Use `⟨N, Set.mem_iInter.2 hz, ?_⟩` and prove the remaining obligations. Introduce `p _ y τ x c hy hx hc`. Establish `hcl` using `cl_of_test τ`. Take `⟨y₀, t, cf, ⟨tm⟩⟩` from `(GlobalTheory.T.exists_geometricTest_map_classicalPoint hL o Ω S ρ M U₀ EE hB Q hS hG).1 p y hcl`. Take `⟨e, he, hef⟩` from `GlobalTheory.T.exists_iso_special_fibre_test_geometric_test hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t cf tm τ hS hF`.

Take `⟨c', hc', hcl'⟩` from `exists_torsion_pullback τ.H _ c _ hc`. Establish `hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1` using `fun a => by`. Rewrite using `[cf.at_]`. Conclude with `RatModel.norm_val_le_one rfl ((M.O _).algebraMap_mem a)`. Establish `hX : (c' ≫ e.hom) ^ (S.r * S.N) = 1`.

Rewrite using `[← MonObj.pow_comp, hc', MonObj.one_comp]`. Take `⟨a, ha, c₁, a', h₁, h₂, h₃, h₄⟩` from `(special_torsion_eq_reduction hL o Ω S ρ p y₀ t.u t.l t.σ t.cls t.mod hint).2.1 (c' ≫ e.hom) hX`. Establish `haH : a ∈ S.HH M z`. Rewrite using `[hB.atTest z p y y₀ t.τ ⟨hy, hcl⟩ cf.at_]`. Conclude with `mem_ker t ha`.

Set `b : S.HH M z` to `⟨a, haH⟩`. Take `⟨y', hy', hxy⟩` from `exists_lift (Z := M.Z) (hN b) y ((congrArg (· ∈ W b) hy).mpr (hz b)) x hx`. Establish `key` using `integral_eq_section tm (hh b) (hgen b _) hy' h₁ h₂ h₃`. Use `⟨M.Z.homOfLE (hN b) ≫ h b, ?_, chase (j := Q.G.ι) hxy key h₄ hef hcl'⟩` and prove the remaining obligations. Use `show (M.Z.homOfLE (hN b) ≫ h b) ≫ Q.G.ι ≫ Q.P.hom = N.ι`.

Rewrite using `[Category.assoc, hh, Scheme.homOfLE_ι]`.
-/
theorem torsSec : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → ex.core.TorsSec (S.r * S.N) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hS hG hF z _
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  choose W h hz hh hgen using fun a : S.HH M z => GlobalTheory.T.exists_section_extending_torsionPoints_support hL o Ω S ρ M U₀ EE hB Q z a.1 a.2
  let N : M.Z.Opens := ⟨⋂ a, (W a : Set M.Z), isOpen_iInter_of_finite fun a => (W a).isOpen⟩
  have hN : ∀ a, N ≤ W a := fun a w hw => Set.mem_iInter.1 hw a
  refine ⟨N, Set.mem_iInter.2 hz, ?_⟩
  intro p _ y τ x c hy hx hc
  have hcl := cl_of_test τ
  obtain ⟨y₀, t, cf, ⟨tm⟩⟩ := (GlobalTheory.T.exists_geometricTest_map_classicalPoint hL o Ω S ρ M U₀ EE hB Q hS hG).1 p y hcl
  obtain ⟨e, he, hef⟩ := GlobalTheory.T.exists_iso_special_fibre_test_geometric_test hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t cf tm τ hS hF
  obtain ⟨c', hc', hcl'⟩ := exists_torsion_pullback τ.H _ c _ hc
  have hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a => by
    rw [cf.at_]
    exact RatModel.norm_val_le_one rfl ((M.O _).algebraMap_mem a)
  have hX : (c' ≫ e.hom) ^ (S.r * S.N) = 1 := by
    rw [← MonObj.pow_comp, hc', MonObj.one_comp]
  obtain ⟨a, ha, c₁, a', h₁, h₂, h₃, h₄⟩ :=
    (special_torsion_eq_reduction hL o Ω S ρ p y₀ t.u t.l t.σ t.cls t.mod hint).2.1 (c' ≫ e.hom) hX
  have haH : a ∈ S.HH M z := by
    rw [hB.atTest z p y y₀ t.τ ⟨hy, hcl⟩ cf.at_]
    exact mem_ker t ha
  let b : S.HH M z := ⟨a, haH⟩
  obtain ⟨y', hy', hxy⟩ := exists_lift (Z := M.Z) (hN b) y ((congrArg (· ∈ W b) hy).mpr (hz b)) x hx
  have key := integral_eq_section tm (hh b) (hgen b _) hy' h₁ h₂ h₃
  refine ⟨M.Z.homOfLE (hN b) ≫ h b, ?_, chase (j := Q.G.ι) hxy key h₄ hef hcl'⟩
  show (M.Z.homOfLE (hN b) ≫ h b) ≫ Q.G.ι ≫ Q.P.hom = N.ι
  rw [Category.assoc, hh, Scheme.homOfLE_ι]

end GlobalTheory.ZH.TorsionValue
end
