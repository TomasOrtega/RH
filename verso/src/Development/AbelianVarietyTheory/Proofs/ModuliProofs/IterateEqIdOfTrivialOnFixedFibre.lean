import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LiftOfUniqueOfSimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtendedStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.StabTame

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `a.add 0 0`. Rewrite `h` using `[add_zero]`. Rewrite using `[Nat.cast_zero, pow_zero]`.

Conclude with `left_eq_mul.1 h`. Consider the case `succ n ih => rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]`.
-/
theorem act_natCast {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (a : OAct O G) (n : ℕ) :
    a.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h := a.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.1 h
  | succ n ih => rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]

/- English proof (translation)
Take `⟨z⟩ : Nonempty S` from `inferInstance`. Conclude with `⟨AlgebraicClosure (S.residueField z), inferInstance, inferInstance, ⟨Spec.map (CommRingCat.ofHom (algebraMap (S.residueField z) _)) ≫ S.fromSpecResidueField z⟩⟩`.
-/
theorem exists_geomPoint (S : Scheme.{0}) [Nonempty S] :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k), Nonempty (Sp k ⟶ S) := by
  obtain ⟨z⟩ : Nonempty S := inferInstance
  exact ⟨AlgebraicClosure (S.residueField z), inferInstance, inferInstance,
    ⟨Spec.map (CommRingCat.ofHom (algebraMap (S.residueField z) _)) ≫ S.fromSpecResidueField z⟩⟩

/- English proof (translation)
Establish `h1 : P (g v - v)`. Use `hco _ fun w hw => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `hP w hw`. Establish `e1 : e (g v - v) w = (e (g v) (g w) - e v w) - (N : ℤ) * e (g v) c`. Establish `: g w = w + N • c` using `by rw [← hc]; abel`.

Rewrite using `[this]`. Simplify using `only [map_sub, map_add, map_nsmul, LinearMap.sub_apply, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `dvd_sub (hg v w) (dvd_mul_right _ _)`.

Take `⟨d, hd⟩` from `hP _ h1`. Establish `key : ∀ n : ℕ, ∃ c, g^[n] v = v + n • (g v - v) + N • c`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `succ n ih`. Take `⟨c, hc⟩` from `ih`. Use `⟨g c + n • d, ?_⟩` and prove the remaining obligations. Establish `: g (g v - v) = (g v - v) + N • d` using `by rw [← hd]; abel`. Rewrite using `[Function.iterate_succ_apply', hc, map_add, map_add, map_nsmul, map_nsmul, this]`.

Simplify using `only [nsmul_add, succ_nsmul, smul_comm N n d]`. Normalize the expressions using the abelian group laws. Take `⟨c, hc⟩` from `key N`. Conclude with `⟨g v - v + c, by rw [hc, nsmul_add]; abel⟩`.
-/
theorem iterate_modN {V : Type} [AddCommGroup V] (N : ℕ) (e : LinearMap.BilinForm ℤ V) (P : V → Prop) (g : V →+ V)
    (hg : ∀ v w, (N : ℤ) ∣ e (g v) (g w) - e v w) (hP : ∀ v, P v → ∃ c, g v - v = N • c)
    (hco : ∀ v, (∀ w, P w → (N : ℤ) ∣ e v w) → P v) (v : V) : ∃ c, g^[N] v - v = N • c := by
  have h1 : P (g v - v) := by
    refine hco _ fun w hw => ?_
    obtain ⟨c, hc⟩ := hP w hw
    have e1 : e (g v - v) w = (e (g v) (g w) - e v w) - (N : ℤ) * e (g v) c := by
      have : g w = w + N • c := by rw [← hc]; abel
      rw [this]
      simp only [map_sub, map_add, map_nsmul, LinearMap.sub_apply, nsmul_eq_mul]
      ring
    rw [e1]
    exact dvd_sub (hg v w) (dvd_mul_right _ _)
  obtain ⟨d, hd⟩ := hP _ h1
  have key : ∀ n : ℕ, ∃ c, g^[n] v = v + n • (g v - v) + N • c := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨g c + n • d, ?_⟩
      have : g (g v - v) = (g v - v) + N • d := by rw [← hd]; abel
      rw [Function.iterate_succ_apply', hc, map_add, map_add, map_nsmul, map_nsmul, this]
      simp only [nsmul_add, succ_nsmul, smul_comm N n d]
      abel
  obtain ⟨c, hc⟩ := key N
  exact ⟨g v - v + c, by rw [hc, nsmul_add]; abel⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

section

variable {B : Type} [CommRing B] {b : Base l B} {U : Scheme.{0}} {s : U ⟶ Sp B}

/- English proof (translation)
Take `⟨β, hβ⟩` from `Spec.map_surjective (u ≫ s)`. Take `⟨-, I, -, hA, -⟩` from `o.geom k u β.hom hβ.symm`. Establish `h1 : I.ev l.A a' = I.ev l.A a`. Rewrite using `[← hA, ← hA]`. Conclude with `Over.OverMorphism.ext h`.

Establish `h2` using `I.add l.A (a' - a) a`. Rewrite `h2` using `[sub_add_cancel, h1]`. Conclude with `(I.ker l.A l.A_pos _).1 (right_eq_mul.1 h2)`.
-/
theorem modN_of_point_eq (o : Obj D l b s) {k : Type} [Field k] [IsAlgClosed k] (u : Sp k ⟶ U) {a a' : D.La}
    (h : u ≫ (o.etaA a').left = u ≫ (o.etaA a).left) : ∃ c, a' - a = l.A • c := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (u ≫ s)
  obtain ⟨-, I, -, hA, -⟩ := o.geom k u β.hom hβ.symm
  have h1 : I.ev l.A a' = I.ev l.A a := by
    rw [← hA, ← hA]
    exact Over.OverMorphism.ext h
  have h2 := I.add l.A (a' - a) a
  rw [sub_add_cancel, h1] at h2
  exact (I.ker l.A l.A_pos _).1 (right_eq_mul.1 h2)

/- English proof (translation)
Take `⟨k, _, _, ⟨u⟩⟩` from `exists_geomPoint U`. Take `⟨β, hβ⟩` from `Spec.map_surjective (u ≫ s)`. Take `⟨-, I, hζ, hA, -⟩` from `o.geom k u β.hom hβ.symm`. Take `⟨-, J, hζ', hA', -⟩` from `o.geom k (u ≫ r) β.hom (by rw [Category.assoc, hr]; exact hβ.symm)`. Establish `hz : I.ζ l.A = J.ζ l.A` using `Units.ext (hζ.trans hζ'.symm)`.

Establish `hL : LBIso o.t.PP.L (o.t.PP.L.pull ν.φ)` using `ν.lin.imp fun _ h => h.1`. Establish `mv : ∀ {x x' : D.La}, (o.etaA x').left ≫ ν.φ = r ≫ (o.etaA x).left → (J.ev l.A x).left = (I.ev l.A x').left ≫ ν.φ`. Introduce `x x' h`. Rewrite using `[← hA, ← hA']`. Use `show (u ≫ r) ≫ (o.etaA x).left = (u ≫ (o.etaA x').left) ≫ ν.φ`.

Rewrite using `[Category.assoc, Category.assoc, h]`. Establish `w` using `(weilIs_grpPullback_of_comm U U o.t.G o.t.G r ν.φ o.t.PP.L o.t.PP.L o.t.PP.isLB o.t.PP.isLB ν.cart hL (Over.mk u) l.A _ _ (J.ev l.A a) (J.ev l.A c) _ (mv ha) (mv hc)).1 (I.isom l.A l.A_pos a' c')`. Establish `e` using `weilIs_unique_fieldPoint U o.t.G o.t.PP.L o.t.PP.isLB k (u ≫ r) l.A _ _ _ _ w (J.isom l.A l.A_pos a c)`. Rewrite `e` using `[hz]`. Rewrite using `[← (J.ζ_prim l.A l.A_pos).zpow_eq_one_iff_dvd, zpow_sub, e, mul_inv_cancel]`.
-/
theorem isometry_modN (o : Obj D l b s) [Nonempty U] (r : U ⟶ U) (ν : SABMap o.t o.t r) (hr : r ≫ s = s)
    {a a' c c' : D.La} (ha : (o.etaA a').left ≫ ν.φ = r ≫ (o.etaA a).left)
    (hc : (o.etaA c').left ≫ ν.φ = r ≫ (o.etaA c).left) : (l.A : ℤ) ∣ D.EF a' c' - D.EF a c := by
  obtain ⟨k, _, _, ⟨u⟩⟩ := exists_geomPoint U
  obtain ⟨β, hβ⟩ := Spec.map_surjective (u ≫ s)
  obtain ⟨-, I, hζ, hA, -⟩ := o.geom k u β.hom hβ.symm
  obtain ⟨-, J, hζ', hA', -⟩ := o.geom k (u ≫ r) β.hom (by rw [Category.assoc, hr]; exact hβ.symm)
  have hz : I.ζ l.A = J.ζ l.A := Units.ext (hζ.trans hζ'.symm)
  have hL : LBIso o.t.PP.L (o.t.PP.L.pull ν.φ) := ν.lin.imp fun _ h => h.1
  have mv : ∀ {x x' : D.La}, (o.etaA x').left ≫ ν.φ = r ≫ (o.etaA x).left →
      (J.ev l.A x).left = (I.ev l.A x').left ≫ ν.φ := by
    intro x x' h
    rw [← hA, ← hA']
    show (u ≫ r) ≫ (o.etaA x).left = (u ≫ (o.etaA x').left) ≫ ν.φ
    rw [Category.assoc, Category.assoc, h]
  have w := (weilIs_grpPullback_of_comm U U o.t.G o.t.G r ν.φ o.t.PP.L o.t.PP.L o.t.PP.isLB o.t.PP.isLB ν.cart hL
    (Over.mk u) l.A _ _ (J.ev l.A a) (J.ev l.A c) _ (mv ha) (mv hc)).1 (I.isom l.A l.A_pos a' c')
  have e := weilIs_unique_fieldPoint U o.t.G o.t.PP.L o.t.PP.isLB k (u ≫ r) l.A _ _ _ _ w (J.isom l.A l.A_pos a c)
  rw [hz] at e
  rw [← (J.ζ_prim l.A l.A_pos).zpow_eq_one_iff_dvd, zpow_sub, e, mul_inv_cancel]

end

/- English proof (translation)
Establish `pn : IsPullback μ₀.φ o.t.G.hom t.G.hom j` using `μ₀.cart.1`. Establish `pm : IsPullback mu.φ t.G.hom t.G.hom ρ` using `mu.cart.1`. Establish `sec : ∀ y : 𝟙_ (Over U) ⟶ o.t.G, y.left ≫ o.t.G.hom = 𝟙 U` using `fun y => Over.w y`. Establish `ext : ∀ {Z : Scheme.{0}} (w : Z ⟶ W.toScheme) (u : Z ⟶ U), w ≫ W.ι = u ≫ j → w ≫ σ = u ≫ (o.etaA a).left ≫ μ₀.φ`. Introduce `Z w u h`.

Use `pullback.lift w u h ≫= hσj` as an intermediate fact. Rewrite `this` using `[pullback.lift_fst_assoc, pullback.lift_snd_assoc]`. Then use the resulting hypothesis. Set `T` to `pullback W.ι (W.ι ≫ ρ)`. Set `p₁ : T ⟶ W.toScheme` to `pullback.fst _ _`. Set `p₂ : T ⟶ W.toScheme` to `pullback.snd _ _`.

Establish `hp : p₁ ≫ W.ι = p₂ ≫ W.ι ≫ ρ` using `pullback.condition`. Establish `: IsOpenImmersion p₂` using `inferInstanceAs (IsOpenImmersion (pullback.snd W.ι (W.ι ≫ ρ)))`. Set `i : T ⟶ X` to `p₂ ≫ W.ι`. Establish `: IsReduced T` using `isReduced_of_isOpenImmersion i`. Establish `w₂ : (p₁ ≫ σ) ≫ t.G.hom = i ≫ ρ` using `by rw [Category.assoc, hσ, hp, Category.assoc]`.

Set `σ₁ : T ⟶ t.G.left` to `p₂ ≫ σ`. Set `σ₂ : T ⟶ t.G.left` to `pm.lift (p₁ ≫ σ) i w₂`. Establish `s₁ : σ₁ ≫ t.G.hom = i` using `by rw [Category.assoc, hσ]`. Establish `s₂ : σ₂ ≫ t.G.hom = i` using `pm.lift_snd _ _ _`. Establish `s₃ : σ₂ ≫ mu.φ = p₁ ≫ σ` using `pm.lift_fst _ _ _`.

Set `x₀ : Sp k ⟶ W.toScheme` to `IsOpenImmersion.lift W.ι x (by rwa [Scheme.Opens.range_ι])`. Establish `hx₀ : x₀ ≫ W.ι = x` using `IsOpenImmersion.lift_fac _ _ _`. Set `xT : Sp k ⟶ T` to `pullback.lift x₀ x₀ (by rw [← Category.assoc, hx₀, hx])`. Establish `x₁ : xT ≫ p₁ = x₀` using `pullback.lift_fst _ _ _`. Establish `x₂ : xT ≫ p₂ = x₀` using `pullback.lift_snd _ _ _`.

Establish `hxT : xT ≫ σ₁ = xT ≫ σ₂`. Establish `w : (xT ≫ σ₂) ≫ t.G.hom = 𝟙 _ ≫ x`. Rewrite using `[Category.assoc, s₂, ← Category.assoc, x₂, hx₀, Category.id_comp]`. Establish `h` using `pullback.lift (xT ≫ σ₂) (𝟙 _) w ≫= hfib`. Rewrite `h` using `[pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc, s₃, ← Category.assoc, x₁]`.

Rewrite using `[← h, ← Category.assoc, x₂]`. Set `q₁` to `pullback.fst i j`. Set `q₂` to `pullback.snd i j`. Establish `hq : q₁ ≫ i = q₂ ≫ j` using `pullback.condition`. Establish `: IsDominant q₁` using `isDominant_pullback_fst_of_isOpenMap j i i.isOpenEmbedding.isOpenMap`.

Establish `v₁ : q₁ ≫ σ₁ = q₂ ≫ (o.etaA a).left ≫ μ₀.φ`. Rewrite using `[← Category.assoc]`. Conclude with `ext _ _ (by rw [Category.assoc]; exact hq)`. Establish `v₂ : q₁ ≫ σ₂ = q₂ ≫ (o.etaA a').left ≫ μ₀.φ`. Use `pm.hom_ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, s₃, Category.assoc, Category.assoc, hφ, reassoc_of% ha, ← Category.assoc, ← Category.assoc q₂ r]`. Use `ext _ _ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hp, Category.assoc, ← hj, ← Category.assoc q₂, ← hq, Category.assoc, Category.assoc]`. Rewrite using `[Category.assoc, s₂, hq, Category.assoc, Category.assoc, pn.w, ← Category.assoc (o.etaA a').left, sec]`. Conclude with `congrArg (q₂ ≫ ·) (Category.id_comp j).symm`.

Establish `tor : ∀ y : D.La, (o.etaA y).left ≫ μ₀.φ ≫ (t.act.act (l.A : 𝓞 E)).left = (1 : 𝟙_ (Over U) ⟶ o.t.G).left ≫ μ₀.φ`. Introduce `y`. Establish `h : μ₀.φ ≫ (t.act.act (l.A : 𝓞 E)).left = (o.t.act.act (l.A : 𝓞 E)).left ≫ μ₀.φ` using `(μ₀.act _).symm`. Rewrite using `[h, ← Category.assoc, ← Over.comp_left, act_natCast, MonObj.comp_pow, Category.comp_id, ← LiftAut.etaA_nsmul, o.etaA_ker]`. Use `t.semi.separated` as an intermediate fact.

Use `t.semi.smooth` as an intermediate fact. Establish `: Etale (t.act.act (l.A : 𝓞 E)).left`. Rewrite using `[act_natCast]`. Conclude with `GrpTangent.etale_id_pow t.G hN`. Establish `hmul : σ₁ ≫ (t.act.act (l.A : 𝓞 E)).left = σ₂ ≫ (t.act.act (l.A : 𝓞 E)).left`.

Use `ext_of_isDominant_of_isSeparated t.G.hom ?_ q₁ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc σ₁, Category.assoc σ₂, Over.w, s₁, s₂]`. Rewrite using `[reassoc_of% v₁, reassoc_of% v₂, tor, tor]`. Use `isOpenImmersion_equalizer_ι_of_unramified _ hmul` as an intermediate fact. Set `e` to `equalizer.ι σ₁ σ₂`.

Establish `he : e ≫ σ₁ = e ≫ σ₂` using `equalizer.condition _ _`. Establish `: IsDominant (pullback.fst e q₁)` using `isDominant_pullback_fst_of_isOpenMap q₁ e e.isOpenEmbedding.isOpenMap`. Establish `: Nonempty ↑(equalizer σ₁ σ₂)` using `⟨equalizer.lift xT hxT (⊥ : PrimeSpectrum k)⟩`. Establish `: Nonempty ↑(pullback e q₁)` using `(pullback.fst e q₁).denseRange.nonempty`. Take `⟨K, _, _, ⟨y⟩⟩` from `exists_geomPoint (pullback e q₁)`.

Use `modN_of_point_eq o (y ≫ pullback.snd e q₁ ≫ q₂) (pn.hom_ext ?_ ?_)` and prove the remaining obligations. Simplify using `only [Category.assoc]`. Rewrite using `[← v₁, ← v₂, ← pullback.condition_assoc, ← pullback.condition_assoc, he]`. Simplify using `only [Category.assoc]`. Rewrite using `[sec, sec]`.
-/
theorem modN_of_extends {B : Type} [CommRing B] {b : Base l B} {X U : Scheme.{0}} [IsReduced X] {s : U ⟶ Sp B}
    (j : U ⟶ X) [IsDominant j] (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j) (hN : IsUnit (l.A : Γ(X, ⊤)))
    (r : U ⟶ U) (ν : SABMap o.t o.t r) (ρ : X ⟶ X) (mu : SABMap t t ρ) (hj : j ≫ ρ = r ≫ j)
    (hφ : μ₀.φ ≫ mu.φ = ν.φ ≫ μ₀.φ) {a a' : D.La} (ha : (o.etaA a').left ≫ ν.φ = r ≫ (o.etaA a).left)
    {k : Type} [Field k] (x : Sp k ⟶ X) (hx : x ≫ ρ = x)
    (hfib : pullback.fst t.G.hom x ≫ mu.φ = pullback.fst t.G.hom x)
    (W : X.Opens) (σ : W.toScheme ⟶ t.G.left) (hxW : Set.range x ⊆ W) (hσ : σ ≫ t.G.hom = W.ι)
    (hσj : pullback.fst W.ι j ≫ σ = pullback.snd W.ι j ≫ (o.etaA a).left ≫ μ₀.φ) : ∃ c, a' - a = l.A • c := by
  have pn : IsPullback μ₀.φ o.t.G.hom t.G.hom j := μ₀.cart.1
  have pm : IsPullback mu.φ t.G.hom t.G.hom ρ := mu.cart.1
  have sec : ∀ y : 𝟙_ (Over U) ⟶ o.t.G, y.left ≫ o.t.G.hom = 𝟙 U := fun y => Over.w y
  have ext : ∀ {Z : Scheme.{0}} (w : Z ⟶ W.toScheme) (u : Z ⟶ U), w ≫ W.ι = u ≫ j →
      w ≫ σ = u ≫ (o.etaA a).left ≫ μ₀.φ := by
    intro Z w u h
    have := pullback.lift w u h ≫= hσj
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  let T := pullback W.ι (W.ι ≫ ρ)
  let p₁ : T ⟶ W.toScheme := pullback.fst _ _
  let p₂ : T ⟶ W.toScheme := pullback.snd _ _
  have hp : p₁ ≫ W.ι = p₂ ≫ W.ι ≫ ρ := pullback.condition
  have : IsOpenImmersion p₂ := inferInstanceAs (IsOpenImmersion (pullback.snd W.ι (W.ι ≫ ρ)))
  let i : T ⟶ X := p₂ ≫ W.ι
  have : IsReduced T := isReduced_of_isOpenImmersion i
  have w₂ : (p₁ ≫ σ) ≫ t.G.hom = i ≫ ρ := by rw [Category.assoc, hσ, hp, Category.assoc]
  let σ₁ : T ⟶ t.G.left := p₂ ≫ σ
  let σ₂ : T ⟶ t.G.left := pm.lift (p₁ ≫ σ) i w₂
  have s₁ : σ₁ ≫ t.G.hom = i := by rw [Category.assoc, hσ]
  have s₂ : σ₂ ≫ t.G.hom = i := pm.lift_snd _ _ _
  have s₃ : σ₂ ≫ mu.φ = p₁ ≫ σ := pm.lift_fst _ _ _
  let x₀ : Sp k ⟶ W.toScheme := IsOpenImmersion.lift W.ι x (by rwa [Scheme.Opens.range_ι])
  have hx₀ : x₀ ≫ W.ι = x := IsOpenImmersion.lift_fac _ _ _
  let xT : Sp k ⟶ T := pullback.lift x₀ x₀ (by rw [← Category.assoc, hx₀, hx])
  have x₁ : xT ≫ p₁ = x₀ := pullback.lift_fst _ _ _
  have x₂ : xT ≫ p₂ = x₀ := pullback.lift_snd _ _ _
  have hxT : xT ≫ σ₁ = xT ≫ σ₂ := by
    have w : (xT ≫ σ₂) ≫ t.G.hom = 𝟙 _ ≫ x := by
      rw [Category.assoc, s₂, ← Category.assoc, x₂, hx₀, Category.id_comp]
    have h := pullback.lift (xT ≫ σ₂) (𝟙 _) w ≫= hfib
    rw [pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc, s₃, ← Category.assoc, x₁] at h
    rw [← h, ← Category.assoc, x₂]
  let q₁ := pullback.fst i j
  let q₂ := pullback.snd i j
  have hq : q₁ ≫ i = q₂ ≫ j := pullback.condition
  have : IsDominant q₁ := isDominant_pullback_fst_of_isOpenMap j i i.isOpenEmbedding.isOpenMap
  have v₁ : q₁ ≫ σ₁ = q₂ ≫ (o.etaA a).left ≫ μ₀.φ := by
    rw [← Category.assoc]
    exact ext _ _ (by rw [Category.assoc]; exact hq)
  have v₂ : q₁ ≫ σ₂ = q₂ ≫ (o.etaA a').left ≫ μ₀.φ := by
    refine pm.hom_ext ?_ ?_
    · rw [Category.assoc, s₃, Category.assoc, Category.assoc, hφ, reassoc_of% ha, ← Category.assoc,
        ← Category.assoc q₂ r]
      refine ext _ _ ?_
      rw [Category.assoc, hp, Category.assoc, ← hj, ← Category.assoc q₂, ← hq, Category.assoc, Category.assoc]
    · rw [Category.assoc, s₂, hq, Category.assoc, Category.assoc, pn.w, ← Category.assoc (o.etaA a').left, sec]
      exact congrArg (q₂ ≫ ·) (Category.id_comp j).symm
  have tor : ∀ y : D.La, (o.etaA y).left ≫ μ₀.φ ≫ (t.act.act (l.A : 𝓞 E)).left =
      (1 : 𝟙_ (Over U) ⟶ o.t.G).left ≫ μ₀.φ := by
    intro y
    have h : μ₀.φ ≫ (t.act.act (l.A : 𝓞 E)).left = (o.t.act.act (l.A : 𝓞 E)).left ≫ μ₀.φ := (μ₀.act _).symm
    rw [h, ← Category.assoc, ← Over.comp_left, act_natCast, MonObj.comp_pow, Category.comp_id,
      ← LiftAut.etaA_nsmul, o.etaA_ker]
  have := t.semi.separated
  have := t.semi.smooth
  have : Etale (t.act.act (l.A : 𝓞 E)).left := by
    rw [act_natCast]
    exact GrpTangent.etale_id_pow t.G hN
  have hmul : σ₁ ≫ (t.act.act (l.A : 𝓞 E)).left = σ₂ ≫ (t.act.act (l.A : 𝓞 E)).left := by
    refine ext_of_isDominant_of_isSeparated t.G.hom ?_ q₁ ?_
    · rw [Category.assoc σ₁, Category.assoc σ₂, Over.w, s₁, s₂]
    · rw [reassoc_of% v₁, reassoc_of% v₂, tor, tor]
  have := isOpenImmersion_equalizer_ι_of_unramified _ hmul
  let e := equalizer.ι σ₁ σ₂
  have he : e ≫ σ₁ = e ≫ σ₂ := equalizer.condition _ _
  have : IsDominant (pullback.fst e q₁) := isDominant_pullback_fst_of_isOpenMap q₁ e e.isOpenEmbedding.isOpenMap
  have : Nonempty ↑(equalizer σ₁ σ₂) := ⟨equalizer.lift xT hxT (⊥ : PrimeSpectrum k)⟩
  have : Nonempty ↑(pullback e q₁) := (pullback.fst e q₁).denseRange.nonempty
  obtain ⟨K, _, _, ⟨y⟩⟩ := exists_geomPoint (pullback e q₁)
  refine modN_of_point_eq o (y ≫ pullback.snd e q₁ ≫ q₂) (pn.hom_ext ?_ ?_)
  · simp only [Category.assoc]
    rw [← v₁, ← v₂, ← pullback.condition_assoc, ← pullback.condition_assoc, he]
  · simp only [Category.assoc]
    rw [sec, sec]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Take `⟨m, hm⟩` from `ObjMaps.exists_sab_id Xo.univ.t`. Conclude with `⟨𝟙 _, m, rfl, Category.id_comp _, fun _ => by rw [hm, Category.comp_id, Category.id_comp], fun _ => by rw [hm, Category.comp_id, Category.id_comp]; rfl⟩`. Consider the case `succ n ih`.

Take `⟨f, m, hf, hs, h₁, h₂⟩` from `ih`. Take `⟨m', hm⟩` from `ObjMaps.exists_sab_comp ν m`. Use `⟨f ≫ r, m', by rw [Function.iterate_succ_apply', ← hf], by rw [Category.assoc, hr, hs], fun x => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hm, reassoc_of% (h₁ x), h, Category.assoc]`. Rewrite using `[hm, Function.iterate_succ_apply, reassoc_of% (h₂ (g x)), hg, Category.assoc]`.
-/
theorem exists_sabMap_iterate (Xo : Moduli D l) (r : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r)
    (hr : r ≫ Xo.s = Xo.s) (h : ∀ x, (Xo.univ.eta x).left ≫ ν.φ = r ≫ (Xo.univ.eta x).left) (g : D.La → D.La)
    (hg : ∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r ≫ (Xo.univ.etaA x).left) (n : ℕ) :
    ∃ (f : Xo.X ⟶ Xo.X) (m : SABMap Xo.univ.t Xo.univ.t f), f = (fun f : Xo.X ⟶ Xo.X => f ≫ r)^[n] (𝟙 _) ∧
      f ≫ Xo.s = Xo.s ∧ (∀ x, (Xo.univ.eta x).left ≫ m.φ = f ≫ (Xo.univ.eta x).left) ∧
      ∀ x, (Xo.univ.etaA (g^[n] x)).left ≫ m.φ = f ≫ (Xo.univ.etaA x).left := by
  induction n with
  | zero =>
    obtain ⟨m, hm⟩ := ObjMaps.exists_sab_id Xo.univ.t
    exact ⟨𝟙 _, m, rfl, Category.id_comp _, fun _ => by rw [hm, Category.comp_id, Category.id_comp],
      fun _ => by rw [hm, Category.comp_id, Category.id_comp]; rfl⟩
  | succ n ih =>
    obtain ⟨f, m, hf, hs, h₁, h₂⟩ := ih
    obtain ⟨m', hm⟩ := ObjMaps.exists_sab_comp ν m
    refine ⟨f ≫ r, m', by rw [Function.iterate_succ_apply', ← hf], by rw [Category.assoc, hr, hs], fun x => ?_,
      fun x => ?_⟩
    · rw [hm, reassoc_of% (h₁ x), h, Category.assoc]
    · rw [hm, Function.iterate_succ_apply, reassoc_of% (h₂ (g x)), hg, Category.assoc]

/- English proof (translation)
Introduce `h₁ h₂ h₃ E _ _ _ H D l Xo S β C r ν ρ mu hinc hS ⟨e, he⟩ hj hφ hr hη g hg k _ _ x hx hfib`. Take `⟨⟨_, hded⟩, -, hfrac⟩` from `(BaseRing.isDedFrac_RZ E H l S e hS he).2.2 β hinc`. Use `letI := β.toAlgebra`. Take `⟨hnoeth, -, -, hpre, hflat, hdom, hqc⟩` from `genericPart_dense_proOpen (RZ H S l.A) (KA l) C.X Xo.X C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense`. Establish `hd : IsDominant C.j` using `hdom`.

Establish `hred : IsReduced C.X`. Use `fun y => (C.normal y).1` as an intermediate fact. Conclude with `isReduced_of_isReduced_stalk _`. Set `t : RZ H S l.A` to `⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩`. Establish `hSu : IsUnit (S : RZ H S l.A)` using `IsUnit.of_mul_eq_one t (Subtype.ext (by`.

Establish `: (S : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hS.ne'`. Simplify using `[t, this]))`. Establish `hAu : IsUnit (l.A : RZ H S l.A)`. Use `isUnit_of_dvd_unit (Nat.cast_dvd_cast he) ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_pow]`.

Conclude with `hSu.pow e`. Establish `hN : IsUnit (l.A : Γ(C.X, ⊤))`. Use `(hAu.map (Scheme.ΓSpecIso (CommRingCat.of (RZ H S l.A))).inv.hom).map C.s.appTop.hom` as an intermediate fact. Rewrite `this` using `[map_natCast, map_natCast]`. Then use the resulting hypothesis. Establish `: Nonempty C.X` using `⟨x (⊥ : PrimeSpectrum k)⟩`.

Establish `: Nonempty Xo.X` using `C.j.denseRange.nonempty`. Establish `hmod` using `iterate_modN l.A D.EF _ g.toAddMonoidHom (fun v w => isometry_modN Xo.univ r.hom ν hr (hg v) (hg w)) (fun v ⟨W, σ, hW, hσ, hσj⟩ => modN_of_extends C.j Xo.univ C.t C.m hN r.hom ν ρ.hom mu hj hφ (hg v) x hx hfib W σ hW hσ hσj) (GlobalTheory.T.levelLabel_extends_of_orthogonal_to_ext …`. Take `⟨f, m, hf, hs, e₁, e₂⟩` from `exists_sabMap_iterate Xo r.hom ν hr hη g.toAddMonoidHom hg l.A`. Rewrite using `[← hf]`. Use `LiftAut.eq_id Xo f m hs e₁ fun a => ?_` and prove the remaining obligations.

Rewrite using `[← e₂, LiftAut.etaA_congr Xo.univ (hmod a)]`.
-/
theorem iterate_eq_id_of_fixes_fibre : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (ρ : C.X ≅ C.X) (mu : SABMap C.t C.t ρ.hom), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ → r.hom ≫ Xo.s = Xo.s → (∀ x, (Xo.univ.eta x).left ≫ ν.φ = r.hom ≫ (Xo.univ.eta x).left) → ∀ g : D.La →ₗ[𝓞 E] D.La, (∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA x).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → pullback.fst C.t.G.hom x ≫ mu.φ = pullback.fst C.t.G.hom x → (fun f : Xo.X ⟶ Xo.X => f ≫ r.hom)^[l.A] (𝟙 _) = 𝟙 _ := by
  intro h₁ h₂ h₃ E _ _ _ H D l Xo S β C r ν ρ mu hinc hS ⟨e, he⟩ hj hφ hr hη g hg k _ _ x hx hfib
  obtain ⟨⟨_, hded⟩, -, hfrac⟩ := (BaseRing.isDedFrac_RZ E H l S e hS he).2.2 β hinc
  letI := β.toAlgebra
  obtain ⟨hnoeth, -, -, hpre, hflat, hdom, hqc⟩ := genericPart_dense_proOpen (RZ H S l.A) (KA l) C.X Xo.X C.s C.jQ
    C.flat C.proj C.jQ_open C.jQ_dense
  have hd : IsDominant C.j := hdom
  have hred : IsReduced C.X := by
    have := fun y => (C.normal y).1
    exact isReduced_of_isReduced_stalk _
  let t : RZ H S l.A := ⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩
  have hSu : IsUnit (S : RZ H S l.A) := IsUnit.of_mul_eq_one t (Subtype.ext (by
    have : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
    simp [t, this]))
  have hAu : IsUnit (l.A : RZ H S l.A) := by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast he) ?_
    rw [Nat.cast_pow]
    exact hSu.pow e
  have hN : IsUnit (l.A : Γ(C.X, ⊤)) := by
    have := (hAu.map (Scheme.ΓSpecIso (CommRingCat.of (RZ H S l.A))).inv.hom).map C.s.appTop.hom
    rwa [map_natCast, map_natCast] at this
  have : Nonempty C.X := ⟨x (⊥ : PrimeSpectrum k)⟩
  have : Nonempty Xo.X := C.j.denseRange.nonempty
  have hmod := iterate_modN l.A D.EF _ g.toAddMonoidHom
    (fun v w => isometry_modN Xo.univ r.hom ν hr (hg v) (hg w))
    (fun v ⟨W, σ, hW, hσ, hσj⟩ =>
      modN_of_extends C.j Xo.univ C.t C.m hN r.hom ν ρ.hom mu hj hφ (hg v) x hx hfib W σ hW hσ hσj)
    (GlobalTheory.T.levelLabel_extends_of_orthogonal_to_extended h₁ h₂ h₃ E H D l (KA l) (baseKA l) C.X Xo.X C.j Xo.s Xo.univ C.t C.m C.normal hpre hflat hdom hqc
      hN k x)
  obtain ⟨f, m, hf, hs, e₁, e₂⟩ := exists_sabMap_iterate Xo r.hom ν hr hη g.toAddMonoidHom hg l.A
  rw [← hf]
  refine LiftAut.eq_id Xo f m hs e₁ fun a => ?_
  rw [← e₂, LiftAut.etaA_congr Xo.univ (hmod a)]

end GlobalTheory.StabTame
