import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.UnitNorm

section Values
variable {C : Type} [NormedField C] {X Y : Scheme.{0}}

/- English proof (translation)
Establish `h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ W` using `fun q hq => e (h hq)`. Rewrite using `[valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE x f W U ⊤ e h]`. Both sides reduce to the same expression.
-/
theorem valF_appLE' {F : Type} [Field F] {x : Sp F ⟶ X} {U : X.Opens} (f : X ⟶ Y) (W : Y.Opens) (e : U ≤ f ⁻¹ᵁ W)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, W)) : valF x U ((f.appLE W U e).hom a) = valF (x ≫ f) W a := by
  have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ W := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE x f W U ⊤ e h]
  rfl

/- English proof (translation)
Establish `h' : ⊤ ≤ x ⁻¹ᵁ U` using `fun q hq => e (h hq)`. Rewrite using `[valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]`. Both sides reduce to the same expression.
-/
theorem valF_res' {F : Type} [Field F] {x : Sp F ⟶ X} {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

/- English proof (translation)
Use `⟨(Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp (t.appLE U ⊤ ht).hom, fun a => ?_⟩` and prove the remaining obligations. Establish `h' : ⊤ ≤ (spMap S.subtype ≫ t) ⁻¹ᵁ U` using `fun q _ => ht (Set.mem_univ (spMap S.subtype q))`. Rewrite using `[valF, dif_pos h']`. Establish `e : (spMap S.subtype ≫ t).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom = t.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫ CommRingCat.ofHom S.subtype`. Rewrite using `[← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap S.subtype) t U ⊤ ⊤ ht le_rfl, Category.assoc]`.

Both sides reduce to the same expression. Conclude with `congrArg (fun g => g.hom a) e`.
-/
theorem exists_valHom (S : ValuationSubring C) (t : Sp S ⟶ X) (U : X.Opens) (ht : ⊤ ≤ t ⁻¹ᵁ U) :
    ∃ g : Γ(X, U) →+* S, ∀ a, valF (spMap S.subtype ≫ t) U a = g a := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp (t.appLE U ⊤ ht).hom, fun a => ?_⟩
  have h' : ⊤ ≤ (spMap S.subtype ≫ t) ⁻¹ᵁ U := fun q _ => ht (Set.mem_univ (spMap S.subtype q))
  rw [valF, dif_pos h']
  have e : (spMap S.subtype ≫ t).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom =
      t.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫ CommRingCat.ofHom S.subtype := by
    rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap S.subtype) t U ⊤ ⊤ ht le_rfl,
      Category.assoc]
    rfl
  exact congrArg (fun g => g.hom a) e

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_valHom S t U ht`. Rewrite using `[hg]`. Conclude with `(hS _).1 (g a).2`.
-/
theorem norm_valF_le {S : ValuationSubring C} (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (t : Sp S ⟶ X) (U : X.Opens)
    (ht : ⊤ ≤ t ⁻¹ᵁ U) (a : Γ(X, U)) : ‖valF (spMap S.subtype ≫ t) U a‖ ≤ 1 := by
  obtain ⟨g, hg⟩ := exists_valHom S t U ht
  rw [hg]
  exact (hS _).1 (g a).2

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_valHom S t U ht`. Take `⟨b, hb⟩` from `(ha.map g).exists_right_inv`. Rewrite using `[hg]`. Establish `h1` using `(hS _).1 (g a).2`. Establish `h2` using `(hS _).1 b.2`.

Establish `h3 : ‖(g a : C)‖ * ‖(b : C)‖ = 1`. Rewrite using `[← norm_mul]`. Establish `: (g a : C) * b = 1` using `congrArg Subtype.val hb`. Rewrite using `[this, norm_one]`. Use polynomial arithmetic with `[norm_nonneg (g a : C), norm_nonneg (b : C)]`.
-/
theorem norm_valF_unit {S : ValuationSubring C} (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (t : Sp S ⟶ X) (U : X.Opens)
    (ht : ⊤ ≤ t ⁻¹ᵁ U) (a : Γ(X, U)) (ha : IsUnit a) : ‖valF (spMap S.subtype ≫ t) U a‖ = 1 := by
  obtain ⟨g, hg⟩ := exists_valHom S t U ht
  obtain ⟨b, hb⟩ := (ha.map g).exists_right_inv
  rw [hg]
  have h1 := (hS _).1 (g a).2
  have h2 := (hS _).1 b.2
  have h3 : ‖(g a : C)‖ * ‖(b : C)‖ = 1 := by
    rw [← norm_mul]
    have : (g a : C) * b = 1 := congrArg Subtype.val hb
    rw [this, norm_one]
  nlinarith [norm_nonneg (g a : C), norm_nonneg (b : C)]
end Values

section Geo
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [NormedField C] [Algebra (FractionRing R) C]
  {N : NumD C} {ν : NumOf D C N} {S : ValuationSubring C} {s : Sp S ⟶ Sp R}

/- English proof (translation)
Use `⟨spMap (((algebraMap (FractionRing R) C).comp (algebraMap R _)).codRestrict S.toSubring fun r => (hS _).2 (h r)), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = jFK (R := R) C ≫ jK R`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem exists_base (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (h : ∀ r : R, ‖algebraMap (FractionRing R) C (algebraMap R _ r)‖ ≤ 1) :
    ∃ s : Sp S ⟶ Sp R, spMap S.subtype ≫ s = (TF (R := R) C).hom := by
  refine ⟨spMap (((algebraMap (FractionRing R) C).comp (algebraMap R _)).codRestrict S.toSubring fun r => (hS _).2 (h r)), ?_⟩
  change _ = jFK (R := R) C ≫ jK R
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/- English proof (translation)
Take `⟨a, rfl⟩` from `Spec.map_surjective a`. Take `⟨b, rfl⟩` from `Spec.map_surjective b`. Rewrite `h` using `[← Spec.map_comp, ← Spec.map_comp]`. Use `Spec.map_injective h` as an intermediate fact. Use `congr 1`.

Use extensionality with `r`. Conclude with `congrArg (fun g => g.hom r) this`.
-/
theorem base_ext {a b : Sp S ⟶ Sp R} (h : spMap S.subtype ≫ a = spMap S.subtype ≫ b) : a = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have := Spec.map_injective h
  congr 1
  ext r
  exact congrArg (fun g => g.hom r) this

/- English proof (translation)
Assemble the required witnesses or components as `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.subtype).2 (by rw [(RingHom.injective_iff_ker_eq_bot _).1 S.subtype_injective]; exact bot_le)⟩`.
-/
theorem isDominant_sub : IsDominant (spMap S.subtype) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 S.subtype_injective]; exact bot_le)⟩

/- English proof (translation)
Take `⟨x₀, e, h⟩` from `hν (Over.homMk (spMap S.subtype ≫ y) (by rw [Category.assoc, hy, hs]))`. Use `D.P.isAb.proper` as an intermediate fact. Use `isDominant_sub (S := S)` as an intermediate fact. Establish `e' : spMap S.subtype ≫ x₀ = spMap S.subtype ≫ y` using `e`. Take `rfl : x₀ = y` from `ext_of_isDominant_of_isSeparated D.P.A.hom (base_ext (by rw [← Category.assoc, e', Category.assoc])) _ e'`.

Conclude with `h`.
-/
theorem chart_int (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) (y : Sp S ⟶ D.P.A.left)
    (hy : y ≫ D.P.A.hom = s) : ⊤ ≤ y ⁻¹ᵁ D.P.L.U (ν.J (spMap S.subtype ≫ y)) := by
  obtain ⟨x₀, e, h⟩ := hν (Over.homMk (spMap S.subtype ≫ y) (by rw [Category.assoc, hy, hs]))
  have := D.P.isAb.proper
  have := isDominant_sub (S := S)
  have e' : spMap S.subtype ≫ x₀ = spMap S.subtype ≫ y := e
  obtain rfl : x₀ = y := ext_of_isDominant_of_isSeparated D.P.A.hom
    (base_ext (by rw [← Category.assoc, e', Category.assoc])) _ e'
  exact h

/- English proof (translation)
Introduce `q hq` and use `Set.mem_iInter.2 fun k => by beta_reduce rw [Category.assoc] exact chart_int hν hs (r ≫ φ k) (by rw [Category.assoc, h]) hq`.
-/
theorem wchart_int (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) {Y : Scheme.{0}} {K : Type}
    [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) :
    ⊤ ≤ r ⁻¹ᵁ LB.wchart D.P.L φ fun k => ν.J ((spMap S.subtype ≫ r) ≫ φ k) := fun q hq =>
  Set.mem_iInter.2 fun k => by
    beta_reduce
    rw [Category.assoc]
    exact chart_int hν hs (r ≫ φ k) (by rw [Category.assoc, h]) hq

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `norm_valF_unit hS r _ (wchart_int hν hs φ r h) _ (Units.isUnit _)`.
-/
theorem norm_vF (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε))
    (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) {r' : Sp C ⟶ Y} (e : spMap S.subtype ≫ r = r') :
    ‖vF t r' ν.J‖ = 1 := by
  subst e
  exact norm_valF_unit hS r _ (wchart_int hν hs φ r h) _ (Units.isUnit _)

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `norm_valF_le hS r _ (wchart_int hν hs φ r h) _`.
-/
theorem norm_sF (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Sec (LB.LinComb D.P.L φ ε))
    (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) {r' : Sp C ⟶ Y} (e : spMap S.subtype ≫ r = r') :
    ‖sF t r' ν.J‖ ≤ 1 := by
  subst e
  exact norm_valF_le hS r _ (wchart_int hν hs φ r h) _

/- English proof (translation)
Take `⟨x₀, e, -⟩` from `hν x`. Use `⟨Over.homMk x₀ (base_ext ?_), Over.OverMorphism.ext e⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, e, Over.w x]`. Conclude with `hs.symm`.
-/
theorem exists_ext (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) (x : TF (R := R) C ⟶ D.P.A) :
    ∃ x₀ : Over.mk s ⟶ D.P.A, (Over.homMk (spMap S.subtype) hs : TF (R := R) C ⟶ Over.mk s) ≫ x₀ = x := by
  obtain ⟨x₀, e, -⟩ := hν x
  refine ⟨Over.homMk x₀ (base_ext ?_), Over.OverMorphism.ext e⟩
  rw [← Category.assoc, e, Over.w x]
  exact hs.symm

/- English proof (translation)
The claim follows from `norm_vF hS hν hs _ s (fun _ => by have : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A] exact (congrArg (s ≫ ·) this).trans (Category.comp_id _)) hs`.
-/
theorem norm_rig (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) :
    ‖vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) C).hom ν.J‖ = 1 :=
  norm_vF hS hν hs _ s (fun _ => by
    have : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
    exact (congrArg (s ≫ ·) this).trans (Category.comp_id _)) hs

/- English proof (translation)
Take `⟨x₀, hx⟩` from `exists_ext hν hs (ν.eA x)`. Take `⟨y₀, hy⟩` from `exists_ext hν hs (ν.eA y)`. Take `⟨u₀, hu⟩` from `exists_ext hν hs (ν.eA u)`. Rewrite using `[ν.θ_eq]`. Use `norm_vF hS hν hs _ (lift x₀ (lift y₀ u₀)).left (fun k => ?_) ?_` and prove the remaining obligations.

Conclude with `(congrArg (_ ≫ ·) (Over.w (psum D.P.A (x3 D.P.A) k.down))).trans (Over.w (lift x₀ (lift y₀ u₀)))`. Rewrite using `[← hx, ← hy, ← hu, ← comp_lift, ← comp_lift]`. Both sides reduce to the same expression.
-/
theorem norm_θ (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x y u : N.A) : ‖(N.θ x y u : C)‖ = 1 := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  obtain ⟨y₀, hy⟩ := exists_ext hν hs (ν.eA y)
  obtain ⟨u₀, hu⟩ := exists_ext hν hs (ν.eA u)
  rw [ν.θ_eq]
  refine norm_vF hS hν hs _ (lift x₀ (lift y₀ u₀)).left (fun k => ?_) ?_
  · exact (congrArg (_ ≫ ·) (Over.w (psum D.P.A (x3 D.P.A) k.down))).trans (Over.w (lift x₀ (lift y₀ u₀)))
  · rw [← hx, ← hy, ← hu, ← comp_lift, ← comp_lift]
    rfl

/- English proof (translation)
Take `⟨x₀, hx⟩` from `exists_ext hν hs (ν.eA x)`. Rewrite using `[ν.σ_eq]`. Use `norm_vF hS hν hs _ x₀.left (fun k => ?_) (congrArg (·.left) hx)` and prove the remaining obligations. Use `fin_cases k`. Conclude with `(congrArg (_ ≫ ·) (Over.w ι[D.P.A])).trans (Over.w x₀)`.

Conclude with `(congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w x₀)`.
-/
theorem norm_σ (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x : N.A) : ‖(N.σ x : C)‖ = 1 := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  rw [ν.σ_eq]
  refine norm_vF hS hν hs _ x₀.left (fun k => ?_) (congrArg (·.left) hx)
  fin_cases k
  · exact (congrArg (_ ≫ ·) (Over.w ι[D.P.A])).trans (Over.w x₀)
  · exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w x₀)

/- English proof (translation)
Take `⟨x₀, hx⟩` from `exists_ext hν hs (ν.eA x)`. Establish `h` using `congrArg norm (ν.th_eq x)`. Rewrite `h` using `[norm_mul, norm_rig hS hν hs, _root_.mul_one]`. Rewrite using `[h]`. Conclude with `norm_sF hS hν hs _ x₀.left (fun _ => (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w x₀)) (congrArg (·.left) hx)`.
-/
theorem norm_th (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x : N.A) : ‖N.th x‖ ≤ 1 := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  have h := congrArg norm (ν.th_eq x)
  rw [norm_mul, norm_rig hS hν hs, _root_.mul_one] at h
  rw [h]
  exact norm_sF hS hν hs _ x₀.left (fun _ => (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w x₀))
    (congrArg (·.left) hx)

/- English proof (translation)
Establish `e : jFK (R` using `R) C ≫ D.xK χ = spMap S.subtype ≫ s ≫ (D.c χ).left := by`. Rewrite using `[← Category.assoc, hs]`. Conclude with `(Category.assoc _ _ _).symm`. Establish `h1` using `chart_int hν hs (s ≫ (D.c χ).left) ((Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (Over.w (D.c χ))).trans (Category.comp_id _)))`. Rewrite `h1` using `[← e]`.

Establish `h2 : s (IsLocalRing.closedPoint S) ∈ ((D.c χ).left ⁻¹ᵁ D.P.L.U (ν.J (jFK (R` using `R) C ≫ D.xK χ)) : (Sp R).Opens) := h1 (Set.mem_univ _)`. Take `⟨_, ⟨V, hV, rfl⟩, hy, hle⟩` from `(Sp R).isBasis_affineOpens.exists_subset_of_mem_open h2 (TopologicalSpace.Opens.isOpen _)`. Establish `h3 : ⊤ ≤ s ⁻¹ᵁ V` using `((IsLocalRing.closedPoint_mem_iff (s ⁻¹ᵁ V)).1 hy).ge`. Establish `h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K` using `PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) := fun y hy => Set.mem_iInter.2 fun _ => hle hy`. Take `⟨r, hr, er⟩` from `hχ (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) V hV (Set.subset_univ _) hle h`.

Establish `hs' : jFK (R` using `R) C ≫ jK R = spMap S.subtype ≫ s := hs.symm`. Establish `h4 : ⊤ ≤ jFK (R` using `R) C ⁻¹ᵁ (jK R ⁻¹ᵁ V) := by`. Express the relevant statement in the definitionally equal form `⊤ ≤ (jFK (R := R) C ≫ jK R) ⁻¹ᵁ V`. Rewrite using `[hs']`. Conclude with `fun q _ => h3 (Set.mem_univ (spMap S.subtype q))`.

Establish `a` using `valF_res' h h4 ((D.psi χ).s _).val`. Rewrite `er` using `[Scheme.Hom.app_eq_appLE]`. Use `(congrArg norm (a.symm.trans ((congrArg (valF _ _) er.symm).trans (valF_appLE' (jK R) V le_rfl h4 r)))).trans ?_` and prove the remaining obligations. Conclude with `(congrArg (fun q => ‖valF q V r‖) hs').trans (norm_valF_unit hS s V h3 r hr)`.
-/
theorem norm_psi (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (χ : D.X) (hχ : PsiUnitOn D χ Set.univ) : ‖vF (D.psi χ) (jFK (R := R) C) ν.J‖ = 1 := by
  have e : jFK (R := R) C ≫ D.xK χ = spMap S.subtype ≫ s ≫ (D.c χ).left := by
    rw [← Category.assoc, hs]
    exact (Category.assoc _ _ _).symm
  have h1 := chart_int hν hs (s ≫ (D.c χ).left)
    ((Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (Over.w (D.c χ))).trans (Category.comp_id _)))
  rw [← e] at h1
  have h2 : s (IsLocalRing.closedPoint S) ∈ ((D.c χ).left ⁻¹ᵁ D.P.L.U (ν.J (jFK (R := R) C ≫ D.xK χ)) : (Sp R).Opens) :=
    h1 (Set.mem_univ _)
  obtain ⟨_, ⟨V, hV, rfl⟩, hy, hle⟩ := (Sp R).isBasis_affineOpens.exists_subset_of_mem_open h2 (TopologicalSpace.Opens.isOpen _)
  have h3 : ⊤ ≤ s ⁻¹ᵁ V := ((IsLocalRing.closedPoint_mem_iff (s ⁻¹ᵁ V)).1 hy).ge
  have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U
      (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) := fun y hy => Set.mem_iInter.2 fun _ => hle hy
  obtain ⟨r, hr, er⟩ := hχ (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) V hV (Set.subset_univ _) hle h
  have hs' : jFK (R := R) C ≫ jK R = spMap S.subtype ≫ s := hs.symm
  have h4 : ⊤ ≤ jFK (R := R) C ⁻¹ᵁ (jK R ⁻¹ᵁ V) := by
    change ⊤ ≤ (jFK (R := R) C ≫ jK R) ⁻¹ᵁ V
    rw [hs']
    exact fun q _ => h3 (Set.mem_univ (spMap S.subtype q))
  have a := valF_res' h h4 ((D.psi χ).s _).val
  rw [Scheme.Hom.app_eq_appLE] at er
  refine (congrArg norm (a.symm.trans ((congrArg (valF _ _) er.symm).trans
    (valF_appLE' (jK R) V le_rfl h4 r)))).trans ?_
  exact (congrArg (fun q => ‖valF q V r‖) hs').trans (norm_valF_unit hS s V h3 r hr)

/- English proof (translation)
Rewrite using `[ν.ψ_eq, norm_mul, norm_rig hS hν hs, norm_psi hS hν hs _ hχ, _root_.mul_one]`.
-/
theorem norm_ψ (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (χ : N.X) (hχ : PsiUnitOn D (ν.eX χ) Set.univ) : ‖(N.ψ χ : C)‖ = 1 := by
  rw [ν.ψ_eq, norm_mul, norm_rig hS hν hs, norm_psi hS hν hs _ hχ, _root_.mul_one]
end Geo

section Num
variable {C : Type} [NormedField C]

def oneU (C : Type) [NormedField C] : Subgroup Cˣ where
  carrier := {x | ‖(x : C)‖ = 1}
  mul_mem' {a b} ha hb := by
    change ‖((a * b : Cˣ) : C)‖ = 1
    rw [Units.val_mul, norm_mul, ha, hb, _root_.mul_one]
  one_mem' := norm_one
  inv_mem' {a} ha := by
    change ‖((a⁻¹ : Cˣ) : C)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, ha, inv_one]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `‖((x ^ k : Cˣ) : C)‖ = 1 at h`. Rewrite `h` using `[Units.val_pow_eq_pow_val, norm_pow]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hk).1 h`.
-/
theorem oneU_of_pow {x : Cˣ} {k : ℕ} (hk : k ≠ 0) (h : x ^ k ∈ oneU C) : x ∈ oneU C := by
  change ‖((x ^ k : Cˣ) : C)‖ = 1 at h
  rw [Units.val_pow_eq_pow_val, norm_pow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk).1 h

variable (N : NumD C) (hθ : ∀ x y u, N.θ x y u ∈ oneU C) (hσ : ∀ x, N.σ x ∈ oneU C) (hψ : ∀ χ, N.ψ χ ∈ oneU C)
include hθ

/- English proof (translation)
The claim follows from `prod_mem fun _ _ => hθ _ _ _`.
-/
theorem cubN_mem (k : ℕ) (a b x : N.A) : cubN N.θ k a b x ∈ oneU C := prod_mem fun _ _ => hθ _ _ _

/- English proof (translation)
Rewrite using `[eq_div_iff_mul_eq'.2 (g.pow_s k χ)]`. Conclude with `div_mem (pow_mem h k) (cubN_mem N hθ _ _ _ _)`.
-/
theorem pow_s_mem {g : N.Gt} {χ : N.X} (k : ℕ) (h : g.s χ ∈ oneU C) : (g ^ k).s χ ∈ oneU C := by
  rw [eq_div_iff_mul_eq'.2 (g.pow_s k χ)]
  exact div_mem (pow_mem h k) (cubN_mem N hθ _ _ _ _)

include hψ in
/- English proof (translation)
Use `oneU_of_pow hk ?_` and prove the remaining obligations. Rewrite using `[← p.1.2.pow_s k χ, N.mem_QT.1 p.2]`. Conclude with `mul_mem (div_mem (div_mem (hψ _) (hψ _)) (hψ _)) (cubN_mem N hθ _ _ _ _)`.
-/
theorem s_mem {k : ℕ} (hk : k ≠ 0) (p : N.QT k) (χ : N.X) : p.1.2.s χ ∈ oneU C := by
  refine oneU_of_pow hk ?_
  rw [← p.1.2.pow_s k χ, N.mem_QT.1 p.2]
  exact mul_mem (div_mem (div_mem (hψ _) (hψ _)) (hψ _)) (cubN_mem N hθ _ _ _ _)

include hσ

/- English proof (translation)
The claim follows from `div_mem (hθ _ _ _) (hσ _)`.
-/
theorem dbl_mem (x : N.A) : dbl N.θ N.σ x ∈ oneU C := div_mem (hθ _ _ _) (hσ _)

/- English proof (translation)
The claim follows from `prod_mem fun _ _ => div_mem (cubN_mem N hθ _ _ _ _) (pow_mem (dbl_mem N hθ hσ _) _)`.
-/
theorem mulq_mem (n : ℕ) (x : N.A) : mulq N.θ N.σ n x ∈ oneU C :=
  prod_mem fun _ _ => div_mem (cubN_mem N hθ _ _ _ _) (pow_mem (dbl_mem N hθ hσ _) _)

include hψ

/- English proof (translation)
Establish `hs` using `s_mem N hθ hψ (pow_ne_zero 2 hm) p`. Establish `a : N.wQ p / mulq N.θ N.σ m p.1.2.b ∈ oneU C` using `div_mem (div_mem (mul_mem (hψ _) (mulq_mem N hθ hσ _ _)) (pow_mem (div_mem (mul_mem (hs _) (cubN_mem N hθ _ _ _ _)) (pow_mem (dbl_mem N hθ hσ _) _)) _)) (mulq_mem N hθ hσ _ _)`. Establish `b : N.ψ χ * (p.1.2 ^ m).s χ ∈ oneU C` using `mul_mem (hψ _) (pow_s_mem N hθ m (hs χ))`. Rewrite using `[NumD.txT, NumD.vt, norm_mul, norm_mul, show ‖_‖ = 1 from a, show ‖_‖ = 1 from b, _root_.one_mul, _root_.one_mul]`. Conclude with `hth _`.
-/
theorem norm_txT (hth : ∀ x, ‖N.th x‖ ≤ 1) {m : ℕ} (hm : m ≠ 0) (p : N.QT (m ^ 2)) (χ : N.X) : ‖N.txT m p χ‖ ≤ 1 := by
  have hs := s_mem N hθ hψ (pow_ne_zero 2 hm) p
  have a : N.wQ p / mulq N.θ N.σ m p.1.2.b ∈ oneU C :=
    div_mem (div_mem (mul_mem (hψ _) (mulq_mem N hθ hσ _ _))
      (pow_mem (div_mem (mul_mem (hs _) (cubN_mem N hθ _ _ _ _)) (pow_mem (dbl_mem N hθ hσ _) _)) _))
      (mulq_mem N hθ hσ _ _)
  have b : N.ψ χ * (p.1.2 ^ m).s χ ∈ oneU C := mul_mem (hψ _) (pow_s_mem N hθ m (hs χ))
  rw [NumD.txT, NumD.vt, norm_mul, norm_mul, show ‖_‖ = 1 from a, show ‖_‖ = 1 from b, _root_.one_mul, _root_.one_mul]
  exact hth _

/- English proof (translation)
Establish `h0 : 0 < ‖(u : C)‖` using `norm_pos_iff.2 u.ne_zero`. Establish `hl : 0 < -Real.log ‖(u : C)‖` using `neg_pos.2 (Real.log_neg h0 hu)`. Set `q : QuadraticMap ℤ N.X ℝ` to `(LinearMap.toSpanSingleton ℤ ℝ (-Real.log ‖(u : C)‖ / 2)).compQuadraticMap β.be.toQuadraticMap`. Establish `hq : ∀ y, q y = -Real.log ‖(u : C)‖ * (β.be y y / 2)` using `fun y => by`. Simplify using `only [q, LinearMap.compQuadraticMap_apply, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.toSpanSingleton_apply, zsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨q, ⟨hθ, hσ, hth, fun (χ : N.X) => ?_, ?_⟩, hq⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `(Dvd.intro _ rfl : (2 : ℤ) ∣ 2 * k).trans (β.dvd χ χ)`. Express the relevant statement in the definitionally equal form `‖((N.ψ χ * u ^ (β.be χ χ / 2) : Cˣ) : C)‖ = Real.exp (-q χ)`. Rewrite using `[hq, Units.val_mul, norm_mul, show ‖_‖ = 1 from hψ χ, _root_.one_mul, ha, Int.mul_ediv_cancel_left _ two_ne_zero, Units.val_zpow_eq_zpow_val, norm_zpow, ← Real.rpow_intCast, Real.rpow_def_of_pos h0]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `t : Filter.Tendsto (fun y => β.be y y) Filter.cofinite Filter.atTop` using `Filter.tendsto_atTop.2 fun b => Filter.eventually_cofinite.2 ((ToricData.finite_form_le β.be β.symm β.pos b).subset fun y hy => (not_le.1 hy).le)`. Express the relevant statement in the definitionally equal form `Filter.Tendsto (q : N.X → ℝ) Filter.cofinite Filter.atTop`.

Rewrite using `[show (q : N.X → ℝ) = _ from funext hq]`. Conclude with `((tendsto_intCast_atTop_atTop.comp t).atTop_div_const two_pos).const_mul_atTop hl`.
-/
theorem twist_int (hth : ∀ x, ‖N.th x‖ ≤ 1) {k : ℕ} (β : N.Form k) (u : Cˣ) (hu : ‖(u : C)‖ < 1) :
    ∃ q : QuadraticMap ℤ N.X ℝ, (N.twist β u).Int q ∧ ∀ y, q y = -Real.log ‖(u : C)‖ * (β.be y y / 2) := by
  have h0 : 0 < ‖(u : C)‖ := norm_pos_iff.2 u.ne_zero
  have hl : 0 < -Real.log ‖(u : C)‖ := neg_pos.2 (Real.log_neg h0 hu)
  let q : QuadraticMap ℤ N.X ℝ :=
    (LinearMap.toSpanSingleton ℤ ℝ (-Real.log ‖(u : C)‖ / 2)).compQuadraticMap β.be.toQuadraticMap
  have hq : ∀ y, q y = -Real.log ‖(u : C)‖ * (β.be y y / 2) := fun y => by
    simp only [q, LinearMap.compQuadraticMap_apply, LinearMap.BilinMap.toQuadraticMap_apply,
      LinearMap.toSpanSingleton_apply, zsmul_eq_mul]
    ring
  refine ⟨q, ⟨hθ, hσ, hth, fun (χ : N.X) => ?_, ?_⟩, hq⟩
  · obtain ⟨a, ha⟩ := (Dvd.intro _ rfl : (2 : ℤ) ∣ 2 * k).trans (β.dvd χ χ)
    change ‖((N.ψ χ * u ^ (β.be χ χ / 2) : Cˣ) : C)‖ = Real.exp (-q χ)
    rw [hq, Units.val_mul, norm_mul, show ‖_‖ = 1 from hψ χ, _root_.one_mul, ha, Int.mul_ediv_cancel_left _ two_ne_zero,
      Units.val_zpow_eq_zpow_val, norm_zpow, ← Real.rpow_intCast, Real.rpow_def_of_pos h0]
    congr 1
    push_cast
    ring
  · have t : Filter.Tendsto (fun y => β.be y y) Filter.cofinite Filter.atTop :=
      Filter.tendsto_atTop.2 fun b => Filter.eventually_cofinite.2
        ((ToricData.finite_form_le β.be β.symm β.pos b).subset fun y hy => (not_le.1 hy).le)
    change Filter.Tendsto (q : N.X → ℝ) Filter.cofinite Filter.atTop
    rw [show (q : N.X → ℝ) = _ from funext hq]
    exact ((tendsto_intCast_atTop_atTop.comp t).atTop_div_const two_pos).const_mul_atTop hl
end Num

end GlobalTheory.Ex.UnitNorm
end
