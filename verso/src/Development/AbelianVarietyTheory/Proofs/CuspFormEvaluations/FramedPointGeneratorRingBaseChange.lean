import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace GenBaseChange

open VVRank EmbPull TopologicalSpace

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

/- English proof (translation)
Introduce `s`. Set `I : Ideal Γ(T'.left, ⊤)` to `(Submodule.span Γ(T'.left, ⊤) {pullM P.A P.L 1 h (SecM.ofSec P.A th)}).comap (LinearMap.toSpanSingleton _ _ (SecM.ofSec P.A s))`. Establish `key : ∀ p : T'.left, ∃ f ∈ I, p ∈ T'.left.basicOpen f` using `fun p => by`. Take `⟨V, hV, b, hb⟩` from `hS S P 1 le_rfl (T.hom (h.left p))`. Establish `hq : Unique (Fin (1 ^ P.g))` using `by rw [one_pow]; infer_instance`.

Take `⟨f, hf, hp⟩` from `(isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨h.left p, hV⟩ trivial`. Set `f'` to `h.left.appTop.hom f`. Establish `hf' : h.left ⁻¹ᵁ T.left.basicOpen f = T'.left.basicOpen f'` using `Scheme.preimage_basicOpen_top _ _`. Set `W` to `T.left.basicOpen f`. Set `W'` to `T'.left.basicOpen f'`.

Set `l : overRes W ⟶ overRes (T` to `baseOver S) V := Over.homMk (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))`. Set `k₀ : W'.toScheme ⟶ W.toScheme` to `IsOpenImmersion.lift W.ι (W'.ι ≫ h.left) (by`.

Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `hf'.ge y.2)`. Establish `hk₀ : k₀ ≫ W.ι = W'.ι ≫ h.left` using `IsOpenImmersion.lift_fac _ _ _`. Set `k : overRes W' ⟶ overRes W` to `Over.homMk k₀ (by`.

Express the relevant statement in the definitionally equal form `k₀ ≫ W.ι ≫ T.hom = W'.ι ≫ T'.hom`. Rewrite using `[← Category.assoc, hk₀, Category.assoc, Over.w])`. Establish `hk : k ≫ overResι W = overResι W' ≫ h` using `Over.OverMorphism.ext hk₀`. Establish `hW' : IsAffineOpen W'` using `(isAffineOpen_top _).basicOpen f'`. Establish `: IsAffine (overRes W').left` using `hW'`.

Take `⟨c, hc⟩` from `exists_basis P 1 b hb (overRes W') (k ≫ l)`. Take `⟨n, u, hu⟩` from `exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))`. Take `⟨r, hr⟩` from `H (SecM.toSec P.A u)`. Establish `hr' : u = r • SecM.ofSec P.A th` using `Subtype.ext (funext hr)`. Establish `e₁` using `congrArg (pullM P.A P.L 1 k) hu`.

Rewrite `e₁` using `[LinearMap.map_smulₛₗ, pullM_comp _ P.isLB, pullM_comp _ P.isLB, hk, ← pullM_comp _ P.isLB, hr', LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]`. Establish `e₂ : k.left.appTop.hom ((overResι W).left.appTop.hom (f ^ n)) = (overResι W').left.appTop.hom (f' ^ n)` using `(congrArg (fun q => q.left.appTop.hom (f ^ n)) hk).trans (congrArg (overResι W').left.appTop.hom (map_pow h.left.appTop.hom f n))`. Rewrite `e₁` using `[e₂]`. Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d : Γ((overRes W').left, ⊤), pullM P.A P.L 1 (overResι W') (SecM.ofSec P.A s) = d • pullM P.A P.L 1 (k ≫ l) (SecM.ofSec P.A (b hq.default)) := by`. Use `c.sum_repr (pullM P.A P.L 1 (overResι W') (SecM.ofSec P.A s))` as an intermediate fact.

Rewrite `this` using `[Fintype.sum_unique, hc]`. Conclude with `⟨_, this.symm⟩`. Take `⟨m, d₀, hd₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T'.left, ⊤)), (overResι W').left.appTop.hom d₀ = (overResι W').left.appTop.hom (f' ^ m) * d` from `exists_pow_mul_extend f' d`. Take `⟨N, hN⟩` from `exists_pow_kill_secM P 1 f' ((f' ^ m * f' ^ n) • SecM.ofSec P.A s - (d₀ * h.left.appTop.hom r) • pullM P.A P.L 1 h (SecM.ofSec P.A th)) (map_sub_eq_zero _ _ _ _ _ _ _ _ _ d e₁ hd hd₀)`. Use `⟨f' ^ N * (f' ^ m * f' ^ n), Submodule.mem_span_singleton.2 ⟨f' ^ N * (d₀ * h.left.appTop.hom r), ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite `hN` using `[smul_sub, sub_eq_zero, ← mul_smul, ← mul_smul]`. Conclude with `hN.symm`. Establish `hp' : p ∈ T'.left.basicOpen f'` using `hf'.le hp`. Rewrite `hp'`, the goal using `[Scheme.mem_basicOpen_top]`. Simplify using `only [map_mul, map_pow]`.

Conclude with `(hp'.pow _).mul ((hp'.pow _).mul (hp'.pow _))`. Establish `hI : Ideal.span (I : Set Γ(T'.left, ⊤)) = ⊤` using `(isAffineOpen_top T'.left).self_le_iSup_basicOpen_iff.1 fun p _ => by`. Take `⟨f, hf, hp⟩` from `key p`. Conclude with `Opens.mem_iSup.2 ⟨⟨f, hf⟩, hp⟩`. Rewrite `hI` using `[Ideal.span_eq, Ideal.eq_top_iff_one]`.

Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.1 hI`. Rewrite `hr` using `[LinearMap.toSpanSingleton_apply, one_smul]`. Conclude with `⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩`.
-/
theorem isGenSec_pullS (hS : SecBaseChangeSt) [IsLocallyNoetherian S] [IsAffine T.left] [IsAffine T'.left] (h : T' ⟶ T)
    {th : LB.Sec (LPow P.A P.L 1 T)} (H : IsGenSec P.A P.L 1 th) : IsGenSec P.A P.L 1 (pullS P.A 1 h th) := by
  intro s
  let I : Ideal Γ(T'.left, ⊤) := (Submodule.span Γ(T'.left, ⊤)
    {pullM P.A P.L 1 h (SecM.ofSec P.A th)}).comap (LinearMap.toSpanSingleton _ _ (SecM.ofSec P.A s))
  have key : ∀ p : T'.left, ∃ f ∈ I, p ∈ T'.left.basicOpen f := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom (h.left p))
    have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
    obtain ⟨f, hf, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨h.left p, hV⟩ trivial
    let f' := h.left.appTop.hom f
    have hf' : h.left ⁻¹ᵁ T.left.basicOpen f = T'.left.basicOpen f' := Scheme.preimage_basicOpen_top _ _
    let W := T.left.basicOpen f
    let W' := T'.left.basicOpen f'
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
      (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
    let k₀ : W'.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (W'.ι ≫ h.left) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hf'.ge y.2)
    have hk₀ : k₀ ≫ W.ι = W'.ι ≫ h.left := IsOpenImmersion.lift_fac _ _ _
    let k : overRes W' ⟶ overRes W := Over.homMk k₀ (by
      change k₀ ≫ W.ι ≫ T.hom = W'.ι ≫ T'.hom
      rw [← Category.assoc, hk₀, Category.assoc, Over.w])
    have hk : k ≫ overResι W = overResι W' ≫ h := Over.OverMorphism.ext hk₀
    have hW' : IsAffineOpen W' := (isAffineOpen_top _).basicOpen f'
    have : IsAffine (overRes W').left := hW'
    obtain ⟨c, hc⟩ := exists_basis P 1 b hb (overRes W') (k ≫ l)
    obtain ⟨n, u, hu⟩ := exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))
    obtain ⟨r, hr⟩ := H (SecM.toSec P.A u)
    have hr' : u = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
    have e₁ := congrArg (pullM P.A P.L 1 k) hu
    rw [LinearMap.map_smulₛₗ, pullM_comp _ P.isLB, pullM_comp _ P.isLB, hk, ← pullM_comp _ P.isLB, hr',
      LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ] at e₁
    have e₂ : k.left.appTop.hom ((overResι W).left.appTop.hom (f ^ n)) = (overResι W').left.appTop.hom (f' ^ n) :=
      (congrArg (fun q => q.left.appTop.hom (f ^ n)) hk).trans
        (congrArg (overResι W').left.appTop.hom (map_pow h.left.appTop.hom f n))
    rw [e₂] at e₁
    obtain ⟨d, hd⟩ : ∃ d : Γ((overRes W').left, ⊤), pullM P.A P.L 1 (overResι W') (SecM.ofSec P.A s) =
        d • pullM P.A P.L 1 (k ≫ l) (SecM.ofSec P.A (b hq.default)) := by
      have := c.sum_repr (pullM P.A P.L 1 (overResι W') (SecM.ofSec P.A s))
      rw [Fintype.sum_unique, hc] at this
      exact ⟨_, this.symm⟩
    obtain ⟨m, d₀, hd₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T'.left, ⊤)), (overResι W').left.appTop.hom d₀ =
        (overResι W').left.appTop.hom (f' ^ m) * d := exists_pow_mul_extend f' d
    obtain ⟨N, hN⟩ := exists_pow_kill_secM P 1 f' ((f' ^ m * f' ^ n) • SecM.ofSec P.A s -
      (d₀ * h.left.appTop.hom r) • pullM P.A P.L 1 h (SecM.ofSec P.A th))
        (map_sub_eq_zero _ _ _ _ _ _ _ _ _ d e₁ hd hd₀)
    refine ⟨f' ^ N * (f' ^ m * f' ^ n), Submodule.mem_span_singleton.2 ⟨f' ^ N * (d₀ * h.left.appTop.hom r), ?_⟩, ?_⟩
    · rw [smul_sub, sub_eq_zero, ← mul_smul, ← mul_smul] at hN
      exact hN.symm
    · have hp' : p ∈ T'.left.basicOpen f' := hf'.le hp
      rw [Scheme.mem_basicOpen_top] at hp' ⊢
      simp only [map_mul, map_pow]
      exact (hp'.pow _).mul ((hp'.pow _).mul (hp'.pow _))
  have hI : Ideal.span (I : Set Γ(T'.left, ⊤)) = ⊤ :=
    (isAffineOpen_top T'.left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨f, hf, hp⟩ := key p
      exact Opens.mem_iSup.2 ⟨⟨f, hf⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hI
  rw [LinearMap.toSpanSingleton_apply, one_smul] at hr
  exact ⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩

/- English proof (translation)
Set `z : (Y.basicOpen f).toScheme` to `⟨p, hp⟩`. Establish `q` using `(gs_pull (𝟙 _) (Y.basicOpen f).ι z ⊤ trivial (a * f ^ n)).symm.trans ((congrArg (gs (𝟙 _) z _) h).trans (LBGerm.gs_zero _ z _ trivial))`. Rewrite `q` using `[Category.id_comp]`. Use `replace q := (gs_stalkMap (Y.basicOpen f).ι z ⊤ trivial _).symm.trans q`. Establish `q' : gs (𝟙 Y) p ⊤ (a * f ^ n) = 0` using `PushInv.stalk_inj (Y.basicOpen f).ι z (q.trans (map_zero _).symm)`.

Rewrite `q'` using `[gs_mul _ p ⊤ trivial, LBGerm.gs_pow _ p ⊤ trivial]`. Establish `hu : IsUnit (gs (𝟙 Y) p ⊤ f)`. Rewrite using `[gs_eq _ p ⊤ trivial]`. Conclude with `(Scheme.mem_basicOpen_top _ _ _).1 hp`. Conclude with `(hu.pow n).mul_left_eq_zero.1 q'`.
-/
theorem gs_eq_zero {Y : Scheme.{0}} (f a : Γ(Y, ⊤)) (n : ℕ) (h : (Y.basicOpen f).ι.appTop.hom (a * f ^ n) = 0)
    (p : Y) (hp : p ∈ Y.basicOpen f) : gs (𝟙 Y) p ⊤ a = 0 := by
  let z : (Y.basicOpen f).toScheme := ⟨p, hp⟩
  have q := (gs_pull (𝟙 _) (Y.basicOpen f).ι z ⊤ trivial (a * f ^ n)).symm.trans
    ((congrArg (gs (𝟙 _) z _) h).trans (LBGerm.gs_zero _ z _ trivial))
  rw [Category.id_comp] at q
  replace q := (gs_stalkMap (Y.basicOpen f).ι z ⊤ trivial _).symm.trans q
  have q' : gs (𝟙 Y) p ⊤ (a * f ^ n) = 0 := PushInv.stalk_inj (Y.basicOpen f).ι z (q.trans (map_zero _).symm)
  rw [gs_mul _ p ⊤ trivial, LBGerm.gs_pow _ p ⊤ trivial] at q'
  have hu : IsUnit (gs (𝟙 Y) p ⊤ f) := by
    rw [gs_eq _ p ⊤ trivial]
    exact (Scheme.mem_basicOpen_top _ _ _).1 hp
  exact (hu.pow n).mul_left_eq_zero.1 q'

/- English proof (translation)
Simplify using `using congrArg (fun q => c.repr q i) h`.
-/
theorem basis_smul_eq_zero {R M κ : Type} [CommRing R] [AddCommGroup M] [Module R M] (c : Module.Basis κ R M) (i : κ)
    (x : R) (h : x • c i = 0) : x = 0 := by
  simpa using congrArg (fun q => c.repr q i) h

/- English proof (translation)
Use `fn_ext fun p _ => Eq.trans ?_ (LBGerm.gs_zero _ p ⊤ trivial).symm` and prove the remaining obligations. Take `⟨V, hV, b, hb⟩` from `hS S P 1 le_rfl (T.hom p)`. Establish `hq : Unique (Fin (1 ^ P.g))` using `by rw [one_pow]; infer_instance`. Take `⟨f, hf, hp⟩` from `(isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨p, hV⟩ trivial`. Set `W` to `T.left.basicOpen f`.

Set `l : overRes W ⟶ overRes (T` to `baseOver S) V := Over.homMk (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))`. Establish `hW : IsAffineOpen W` using `(isAffineOpen_top _).basicOpen f`.

Establish `: IsAffine (overRes W).left` using `hW`. Take `⟨c, hc⟩` from `exists_basis P 1 b hb (overRes W) l`. Take `⟨n, u, hu⟩` from `exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))`. Take `⟨r, hr⟩` from `H (SecM.toSec P.A u)`. Establish `hr' : u = r • SecM.ofSec P.A th` using `Subtype.ext (funext hr)`.

Establish `h0 : a • u = 0` using `by rw [hr', smul_comm, ha, smul_zero]`. Establish `e` using `congrArg (pullM P.A P.L 1 (overResι W)) h0`. Rewrite `e` using `[LinearMap.map_smulₛₗ, map_zero, hu, ← mul_smul, ← map_mul]`. Establish `e' : (overResι W).left.appTop.hom (a * f ^ n) • c hq.default = 0`. Rewrite using `[hc]`.

Conclude with `e`. Establish `e₂` using `basis_smul_eq_zero c _ _ e'`. Conclude with `gs_eq_zero f a n e₂ p hp`.
-/
theorem eq_zero_of_smul (hS : SecBaseChangeSt) [IsLocallyNoetherian S] [IsAffine T.left]
    {th : LB.Sec (LPow P.A P.L 1 T)} (H : IsGenSec P.A P.L 1 th) (a : Γ(T.left, ⊤))
    (ha : a • (SecM.ofSec P.A th : SecM P.A P.L 1 T) = 0) : a = 0 := by
  refine fn_ext fun p _ => Eq.trans ?_ (LBGerm.gs_zero _ p ⊤ trivial).symm
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨f, hf, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨p, hV⟩ trivial
  let W := T.left.basicOpen f
  let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
    (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have : IsAffine (overRes W).left := hW
  obtain ⟨c, hc⟩ := exists_basis P 1 b hb (overRes W) l
  obtain ⟨n, u, hu⟩ := exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))
  obtain ⟨r, hr⟩ := H (SecM.toSec P.A u)
  have hr' : u = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
  have h0 : a • u = 0 := by rw [hr', smul_comm, ha, smul_zero]
  have e := congrArg (pullM P.A P.L 1 (overResι W)) h0
  rw [LinearMap.map_smulₛₗ, map_zero, hu, ← mul_smul, ← map_mul] at e
  have e' : (overResι W).left.appTop.hom (a * f ^ n) • c hq.default = 0 := by
    rw [hc]; exact e
  have e₂ := basis_smul_eq_zero c _ _ e'
  exact gs_eq_zero f a n e₂ p hp

/- English proof (translation)
Establish `H' : IsGenSec P.A P.L 1 th'` using `fun s => by`. Take `⟨r, hr⟩` from `isGenSec_pullS P hS h H s`. Conclude with `⟨r, fun j => (hr j).trans (congrArg (_ * ·) (hp j).symm)⟩`. Take `⟨r, hr⟩` from `H' s`. Use `⟨r, hr, fun r' hr' => sub_eq_zero.1 (eq_zero_of_smul P hS H' _ ?_)⟩` and prove the remaining obligations.

Rewrite using `[sub_smul, sub_eq_zero]`. Conclude with `Subtype.ext (funext fun j => (hr' j).symm.trans (hr j))`.
-/
theorem existsUnique_of_isPullSec (hS : SecBaseChangeSt) [IsLocallyNoetherian S] [IsAffine T.left] [IsAffine T'.left]
    (h : T' ⟶ T) {th : LB.Sec (LPow P.A P.L 1 T)} (H : IsGenSec P.A P.L 1 th) {th' : LB.Sec (LPow P.A P.L 1 T')}
    (hp : IsPullSec P.A P.L 1 (h ▷ P.A) (whiskerRight_snd _ _) th th') (s : LB.Sec (LPow P.A P.L 1 T')) :
    ∃! r : Γ(T'.left, ⊤), ∀ j, s.f j = liftFun P.A _ r * th'.f j := by
  have H' : IsGenSec P.A P.L 1 th' := fun s => by
    obtain ⟨r, hr⟩ := isGenSec_pullS P hS h H s
    exact ⟨r, fun j => (hr j).trans (congrArg (_ * ·) (hp j).symm)⟩
  obtain ⟨r, hr⟩ := H' s
  refine ⟨r, hr, fun r' hr' => sub_eq_zero.1 (eq_zero_of_smul P hS H' _ ?_)⟩
  rw [sub_smul, sub_eq_zero]
  exact Subtype.ext (funext fun j => (hr' j).symm.trans (hr j))

/- English proof (translation)
The claim follows from `ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv`.
-/
theorem toΓ_bijective (R : Type) [CommRing R] : Function.Bijective (toΓ R) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv

end GenBaseChange

/- English proof (translation)
Introduce `hL E _ _ _ H Dw l Xo c S T _ _ _ ψ y h _ s' hs' s''`. Use `UnivPol.isLocallyNoetherian Xo` as an intermediate fact. Establish `: IsAffine (ptO Xo y.x).left` using `inferInstanceAs (IsAffine (Spec _))`. Establish `: IsAffine (ptO Xo (spMap ψ ≫ y.x)).left` using `inferInstanceAs (IsAffine (Spec _))`. Take `⟨r, hr, hu⟩` from `GenBaseChange.existsUnique_of_isPullSec (UnivPol.pol Xo) hL.secBaseChange h (th := y.s) (fun s => by`.

Take `⟨a, ha, -⟩` from `y.gen s`. Conclude with `⟨toΓ S a, ha⟩) (th' := s') hs' s''`. Take `⟨a, rfl⟩` from `(GenBaseChange.toΓ_bijective T).2 r`. Conclude with `⟨a, hr, fun a' ha' => (GenBaseChange.toΓ_bijective T).1 (hu _ ha')⟩`.
-/
theorem framedPoint_generator_baseChange :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] (ψ : S →+* T) (y : FrPt Xo c S) (h : ptO Xo (spMap ψ ≫ y.x) ⟶ ptO Xo y.x), h.left = spMap ψ → ∀ s' : LB.Sec (PPx (spMap ψ ≫ y.x)), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s s' → ∀ s'' : LB.Sec (PPx (spMap ψ ≫ y.x)), ∃! a : T, ∀ i, s''.f i = scal (spMap ψ ≫ y.x) a i * s'.f i := by
  intro hL E _ _ _ H Dw l Xo c S T _ _ _ ψ y h _ s' hs' s''
  have := UnivPol.isLocallyNoetherian Xo
  have : IsAffine (ptO Xo y.x).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (ptO Xo (spMap ψ ≫ y.x)).left := inferInstanceAs (IsAffine (Spec _))
  obtain ⟨r, hr, hu⟩ := GenBaseChange.existsUnique_of_isPullSec (UnivPol.pol Xo) hL.secBaseChange h
    (th := y.s) (fun s => by
      obtain ⟨a, ha, -⟩ := y.gen s
      exact ⟨toΓ S a, ha⟩) (th' := s') hs' s''
  obtain ⟨a, rfl⟩ := (GenBaseChange.toΓ_bijective T).2 r
  exact ⟨a, hr, fun a' ha' => (GenBaseChange.toΓ_bijective T).1 (hu _ ha')⟩

end GlobalTheory
