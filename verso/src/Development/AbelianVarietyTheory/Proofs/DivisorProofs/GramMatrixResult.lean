import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HalfGeo

/- English proof (translation)
Use `letI : Algebra K Ω := io.toAlgebra`. Establish `h : (CommRingCat.ofHom io).hom.FaithfullyFlat`. Express the relevant statement in the definitionally equal form `(algebraMap K Ω).FaithfullyFlat`. Rewrite using `[RingHom.faithfullyFlat_algebraMap_iff]`. Use `infer_instance`.

Take `⟨h1, h2⟩` from `(flat_and_surjective_SpecMap_iff _).2 h`. Conclude with `Flat.epi_of_flat_of_surjective _`.
-/
theorem epi_spMap_field {K Ω : Type} [Field K] [Field Ω] (io : K →+* Ω) : Epi (spMap io) := by
  letI : Algebra K Ω := io.toAlgebra
  have h : (CommRingCat.ofHom io).hom.FaithfullyFlat := by
    change (algebraMap K Ω).FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  obtain ⟨h1, h2⟩ := (flat_and_surjective_SpecMap_iff _).2 h
  exact Flat.epi_of_flat_of_surjective _

/- English proof (translation)
Use `haveI := epi_spMap_field io`. Set `T : Over S'` to `Over.mk (spMap io ≫ ξ₀)`. Set `push : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G)` to `fun x => Over.homMk (x.left ≫ φ) (by`. Simplify using `only [Over.mk_hom, Category.assoc]`. Rewrite using `[h.1.w, ← Category.assoc, Over.w x])`.

Establish `hmul : ∀ x y : T ⟶ G', push (x * y) = push x * push y`. Introduce `x y`. Use `ext`. Conclude with `(h.2 T x y (push x) (push y) rfl rfl).symm`. Establish `hone : push 1 = 1`.

Establish `e : push 1 * push 1 = push 1` using `by rw [← hmul, _root_.mul_one]`. Simplify using `using e`. Establish `hpow : ∀ (x : T ⟶ G') (k : ℕ), push (x ^ k) = push x ^ k`. Introduce `x k`. Proceed by induction on `k with`.

Consider the case `zero => simpa using hone`. Consider the case `succ k ih => rw [pow_succ, pow_succ, hmul, ih]`. Establish `h1 : push a ^ q = 1` using `by rw [← hpow, ha, hone]`. Take `⟨w₀, hw₀⟩` from `hs (push a) h1`. Establish `hw₀' : spMap io ≫ w₀ = a.left ≫ φ` using `hw₀`.

Establish `haw : a.left ≫ G'.hom = spMap io ≫ ξ₀` using `Over.w a`. Establish `hb : w₀ ≫ G.hom = ξ₀ ≫ f`. Rewrite using `[← cancel_epi (spMap io), ← Category.assoc, hw₀', Category.assoc, h.1.w, ← Category.assoc, haw, Category.assoc]`. Use `⟨Over.homMk (h.1.lift w₀ ξ₀ hb) (h.1.lift_snd _ _ _), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `spMap io ≫ h.1.lift w₀ ξ₀ hb = a.left`.

Use `h.1.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, h.1.lift_fst, hw₀']`. Rewrite using `[Category.assoc, h.1.lift_snd, haw]`.
-/
theorem gram_descend {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S)
    (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G f φ) {K Ω : Type} [Field K] [Field Ω] (io : K →+* Ω)
    (ξ₀ : Sp K ⟶ S') (q : ℕ)
    (hs : ∀ w : Over.mk (spMap io ≫ ξ₀ ≫ f) ⟶ G, w ^ q = 1 → ∃ w₀ : Sp K ⟶ G.left, spMap io ≫ w₀ = w.left)
    (a : Over.mk (spMap io ≫ ξ₀) ⟶ G') (ha : a ^ q = 1) :
    ∃ s : Over.mk ξ₀ ⟶ G', spMap io ≫ s.left = a.left := by
  haveI := epi_spMap_field io
  let T : Over S' := Over.mk (spMap io ≫ ξ₀)
  let push : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.1.w, ← Category.assoc, Over.w x])
  have hmul : ∀ x y : T ⟶ G', push (x * y) = push x * push y := by
    intro x y
    ext
    exact (h.2 T x y (push x) (push y) rfl rfl).symm
  have hone : push 1 = 1 := by
    have e : push 1 * push 1 = push 1 := by rw [← hmul, _root_.mul_one]
    simpa using e
  have hpow : ∀ (x : T ⟶ G') (k : ℕ), push (x ^ k) = push x ^ k := by
    intro x k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, pow_succ, hmul, ih]
  have h1 : push a ^ q = 1 := by rw [← hpow, ha, hone]
  obtain ⟨w₀, hw₀⟩ := hs (push a) h1
  have hw₀' : spMap io ≫ w₀ = a.left ≫ φ := hw₀
  have haw : a.left ≫ G'.hom = spMap io ≫ ξ₀ := Over.w a
  have hb : w₀ ≫ G.hom = ξ₀ ≫ f := by
    rw [← cancel_epi (spMap io), ← Category.assoc, hw₀', Category.assoc, h.1.w, ← Category.assoc, haw, Category.assoc]
  refine ⟨Over.homMk (h.1.lift w₀ ξ₀ hb) (h.1.lift_snd _ _ _), ?_⟩
  change spMap io ≫ h.1.lift w₀ ξ₀ hb = a.left
  refine h.1.hom_ext ?_ ?_
  · rw [Category.assoc, h.1.lift_fst, hw₀']
  · rw [Category.assoc, h.1.lift_snd, haw]

/- English proof (translation)
Use `(LinearEquiv.ofBijective D.EF D.unimod).isUnit_det b b.dualBasis` as an intermediate fact. Rewrite `this` using `[← Matrix.det_transpose]`. Establish `e : (Matrix.of fun m m' => D.EF (b m) (b m')) = (LinearMap.toMatrix b b.dualBasis (LinearEquiv.ofBijective D.EF D.unimod : D.La →ₗ[ℤ] _)).transpose`. Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, LinearMap.toMatrix_apply, Matrix.of_apply, Module.Basis.dualBasis_repr]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `this`.
-/
theorem isUnit_det_gram {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (D : Datum H) {N : ℕ} (b : Module.Basis (Fin N) ℤ D.La) :
    IsUnit (Matrix.of fun m m' => D.EF (b m) (b m')).det := by
  have := (LinearEquiv.ofBijective D.EF D.unimod).isUnit_det b b.dualBasis
  rw [← Matrix.det_transpose] at this
  have e : (Matrix.of fun m m' => D.EF (b m) (b m')) =
      (LinearMap.toMatrix b b.dualBasis (LinearEquiv.ofBijective D.EF D.unimod : D.La →ₗ[ℤ] _)).transpose := by
    ext i j
    simp only [Matrix.transpose_apply, LinearMap.toMatrix_apply, Matrix.of_apply, Module.Basis.dualBasis_repr]
    rfl
  rw [e]
  exact this

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z K _ _ ξ₀ q hq hζ hsplit N hN`. Take `⟨ζ₀, hζ₀⟩` from `hζ`. Establish `hq0 : 0 < q` using `Nat.pos_of_ne_zero hq`. Use `haveI : NeZero q := ⟨hq⟩`. Set `Ω` to `AlgebraicClosure K`.

Set `io : K →+* Ω` to `algebraMap K Ω`. Use `haveI := epi_spMap_field io`. Set `x : Sp Ω ⟶ Xo.XF c` to `spMap io ≫ ξ₀`. Take `⟨-, I, -⟩` from `Z.oF.geom Ω x (Spec.preimage (x ≫ pullback.fst _ _ ≫ Xo.s)).hom (Spec.map_preimage _).symm`. Use `haveI := Dw.fin`.

Use `haveI := Dw.proj`. Use `haveI : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La`. Use `haveI : Module.Flat ℤ Dw.La := Module.Flat.trans ℤ (𝓞 E) Dw.La`. Use `haveI : Module.Free ℤ Dw.La := inferInstance`. Set `b : Module.Basis (Fin N) ℤ Dw.La` to `Module.finBasisOfFinrankEq ℤ Dw.La hN.symm`.

Establish `hev : ∀ a, I.ev q a ^ q = 1` using `fun a => (I.onto q hq0 _).2 ⟨a, rfl⟩`. Establish `hd : ∀ m, ∃ s : Over.mk ξ₀ ⟶ Z.oF.t.G, spMap io ≫ s.left = (I.ev q (b m)).left` using `fun m => gram_descend Z.oF.t.G Z.t.G Z.j Z.m.φ Z.m.cart io ξ₀ q (hsplit Ω io) _ (hev _)`. Use `choose s hs using hd`. Set `hKo : Over.mk x ⟶ Over.mk ξ₀` to `Over.homMk (spMap io) rfl`. Establish `hKl : hKo.left = spMap io` using `rfl`.

Establish `hinj : ∀ a a' : Over.mk ξ₀ ⟶ Z.oF.t.G, hKo ≫ a = hKo ≫ a' → a = a'`. Introduce `a a' e`. Use `ext1`. Use `congrArg (fun u => u.left) e` as an intermediate fact. Conclude with `(cancel_epi (spMap io)).1 this`.

Establish `hs' : ∀ m, hKo ≫ s m = I.ev q (b m)` using `fun m => by ext1; exact hs m`. Establish `hst : ∀ m, s m ^ q = 1` using `fun m => hinj _ _ (by rw [MonObj.comp_pow, hs', hev, MonObj.comp_one])`. Establish `hp1 : IsPrimitiveRoot (io ζ₀) q` using `hζ₀.map_of_injective io.injective`. Establish `hp2 : IsPrimitiveRoot (I.ζ q : Ω) q` using `(I.ζ_prim q hq0).map_of_injective (f := Units.coeHom Ω) Units.val_injective`. Take `⟨i, -, hi⟩` from `hp1.eq_pow_of_pow_eq_one hp2.pow_eq_one`.

Establish `hne : ζ₀ ^ i ≠ 0` using `pow_ne_zero _ (hζ₀.ne_zero hq)`. Set `ζ : Kˣ` to `Units.mk0 _ hne`. Establish `hmap : Units.map (io : K →* Ω) ζ = I.ζ q`. Use `ext`. Simplify using `[ζ, ← hi]`.

Establish `hminj : Function.Injective (Units.map (io : K →* Ω))` using `Units.map_injective io.injective`. Use `⟨s, ζ, Matrix.of fun m m' => Dw.EF (b m) (b m'), ?_, isUnit_det_gram Dw b, ⟨hst, fun m m' => ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `IsPrimitiveRoot.of_map_of_injective (f := Units.map (io : K →* Ω)) (by rw [hmap]; exact I.ζ_prim q hq0) hminj`. Set `P` to `GlobalTheory.Obj.toPolAV Z.oF`. Take `⟨cq, hcq, -⟩` from `GlobalTheory.LevelCompare.weil_existsUnique P q (s m) (s m') (hst m) (hst m')`.

Take `⟨u, rfl⟩` from `GlobalTheory.Ex.Specialise.unitOn_bijective.2 cq`. Establish `hN` using `(GlobalTheory.LevelCompare.weil_skew_natural P q (Over.mk ξ₀)).2 (Over.mk x) hKo (s m) (s m') (unitOn u) hcq`. Rewrite `hN` using `[hKl, GlobalTheory.Ex.Specialise.map_unitOn]`. Establish `hI` using `I.isom q hq0 (b m) (b m')`. Rewrite `hI` using `[← hs', ← hs']`.

Establish `t : ∀ m, (hKo ≫ s m) ^ q = 1` using `fun m => by rw [hs', hev]`. Establish `e1` using `(GlobalTheory.LevelCompare.weil_existsUnique P q (hKo ≫ s m) (hKo ≫ s m') (t m) (t m')).unique hN hI`. Establish `e2` using `GlobalTheory.Ex.Specialise.unitOn_bijective.1 e1`. Rewrite `e2` using `[← hmap, ← map_zpow]`. Establish `e3` using `hminj e2`.

Rewrite `hcq` using `[e3]`. Conclude with `hcq`. Introduce `a ha`. Take `⟨y, hy⟩` from `(I.onto q hq0 (hKo ≫ a)).1 (by rw [← MonObj.comp_pow, ha, MonObj.comp_one])`. Set `ev : Multiplicative Dw.La →* (Over.mk x ⟶ Z.oF.t.G)` to `MonoidHom.mk' (fun u => I.ev q u.toAdd) (fun u v => I.add q _ _)`.

Set `pb : (Over.mk ξ₀ ⟶ Z.oF.t.G) →* (Over.mk x ⟶ Z.oF.t.G)` to `MonoidHom.mk' (fun u => hKo ≫ u) (fun u v => MonObj.comp_mul _ _ _)`. Use `⟨fun m => (b.repr y m % q).toNat, hinj _ _ ?_⟩` and prove the remaining obligations. Establish `e1 : hKo ≫ a = ev (Multiplicative.ofAdd (∑ m, b.repr y m • b m))`. Rewrite using `[b.sum_repr, ← hy]`. Both sides reduce to the same expression.

Rewrite using `[e1, ofAdd_sum, map_prod]`. Express the relevant statement in the definitionally equal form `_ = pb _`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[ofAdd_zsmul, map_zpow, map_pow]`.

Express the relevant statement in the definitionally equal form `I.ev q (b m) ^ _ = (hKo ≫ s m) ^ _`. Rewrite using `[hs', ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hq))]`. Conclude with `zpow_eq_zpow_emod' _ (hev _)`.
-/
theorem gram : GramSt := by
  intro E _ _ _ H Dw l Xo c O _ β Z K _ _ ξ₀ q hq hζ hsplit N hN
  obtain ⟨ζ₀, hζ₀⟩ := hζ
  have hq0 : 0 < q := Nat.pos_of_ne_zero hq
  haveI : NeZero q := ⟨hq⟩
  let Ω := AlgebraicClosure K
  let io : K →+* Ω := algebraMap K Ω
  haveI := epi_spMap_field io
  let x : Sp Ω ⟶ Xo.XF c := spMap io ≫ ξ₀
  obtain ⟨-, I, -⟩ := Z.oF.geom Ω x (Spec.preimage (x ≫ pullback.fst _ _ ≫ Xo.s)).hom (Spec.map_preimage _).symm
  haveI := Dw.fin
  haveI := Dw.proj
  haveI : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
  haveI : Module.Flat ℤ Dw.La := Module.Flat.trans ℤ (𝓞 E) Dw.La
  haveI : Module.Free ℤ Dw.La := inferInstance
  let b : Module.Basis (Fin N) ℤ Dw.La := Module.finBasisOfFinrankEq ℤ Dw.La hN.symm
  have hev : ∀ a, I.ev q a ^ q = 1 := fun a => (I.onto q hq0 _).2 ⟨a, rfl⟩
  have hd : ∀ m, ∃ s : Over.mk ξ₀ ⟶ Z.oF.t.G, spMap io ≫ s.left = (I.ev q (b m)).left := fun m =>
    gram_descend Z.oF.t.G Z.t.G Z.j Z.m.φ Z.m.cart io ξ₀ q (hsplit Ω io) _ (hev _)
  choose s hs using hd
  let hKo : Over.mk x ⟶ Over.mk ξ₀ := Over.homMk (spMap io) rfl
  have hKl : hKo.left = spMap io := rfl
  have hinj : ∀ a a' : Over.mk ξ₀ ⟶ Z.oF.t.G, hKo ≫ a = hKo ≫ a' → a = a' := by
    intro a a' e
    ext1
    have := congrArg (fun u => u.left) e
    exact (cancel_epi (spMap io)).1 this
  have hs' : ∀ m, hKo ≫ s m = I.ev q (b m) := fun m => by ext1; exact hs m
  have hst : ∀ m, s m ^ q = 1 := fun m => hinj _ _ (by rw [MonObj.comp_pow, hs', hev, MonObj.comp_one])
  have hp1 : IsPrimitiveRoot (io ζ₀) q := hζ₀.map_of_injective io.injective
  have hp2 : IsPrimitiveRoot (I.ζ q : Ω) q := (I.ζ_prim q hq0).map_of_injective (f := Units.coeHom Ω) Units.val_injective
  obtain ⟨i, -, hi⟩ := hp1.eq_pow_of_pow_eq_one hp2.pow_eq_one
  have hne : ζ₀ ^ i ≠ 0 := pow_ne_zero _ (hζ₀.ne_zero hq)
  let ζ : Kˣ := Units.mk0 _ hne
  have hmap : Units.map (io : K →* Ω) ζ = I.ζ q := by
    ext
    simp [ζ, ← hi]
  have hminj : Function.Injective (Units.map (io : K →* Ω)) := Units.map_injective io.injective
  refine ⟨s, ζ, Matrix.of fun m m' => Dw.EF (b m) (b m'), ?_, isUnit_det_gram Dw b, ⟨hst, fun m m' => ?_⟩, ?_⟩
  · exact IsPrimitiveRoot.of_map_of_injective (f := Units.map (io : K →* Ω)) (by rw [hmap]; exact I.ζ_prim q hq0) hminj
  · let P := GlobalTheory.Obj.toPolAV Z.oF
    obtain ⟨cq, hcq, -⟩ := GlobalTheory.LevelCompare.weil_existsUnique P q (s m) (s m') (hst m) (hst m')
    obtain ⟨u, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 cq
    have hN := (GlobalTheory.LevelCompare.weil_skew_natural P q (Over.mk ξ₀)).2 (Over.mk x) hKo (s m) (s m') (unitOn u) hcq
    rw [hKl, GlobalTheory.Ex.Specialise.map_unitOn] at hN
    have hI := I.isom q hq0 (b m) (b m')
    rw [← hs', ← hs'] at hI
    have t : ∀ m, (hKo ≫ s m) ^ q = 1 := fun m => by rw [hs', hev]
    have e1 := (GlobalTheory.LevelCompare.weil_existsUnique P q (hKo ≫ s m) (hKo ≫ s m') (t m) (t m')).unique hN hI
    have e2 := GlobalTheory.Ex.Specialise.unitOn_bijective.1 e1
    rw [← hmap, ← map_zpow] at e2
    have e3 := hminj e2
    rw [e3] at hcq
    exact hcq
  · intro a ha
    obtain ⟨y, hy⟩ := (I.onto q hq0 (hKo ≫ a)).1 (by rw [← MonObj.comp_pow, ha, MonObj.comp_one])
    let ev : Multiplicative Dw.La →* (Over.mk x ⟶ Z.oF.t.G) :=
      MonoidHom.mk' (fun u => I.ev q u.toAdd) (fun u v => I.add q _ _)
    let pb : (Over.mk ξ₀ ⟶ Z.oF.t.G) →* (Over.mk x ⟶ Z.oF.t.G) :=
      MonoidHom.mk' (fun u => hKo ≫ u) (fun u v => MonObj.comp_mul _ _ _)
    refine ⟨fun m => (b.repr y m % q).toNat, hinj _ _ ?_⟩
    have e1 : hKo ≫ a = ev (Multiplicative.ofAdd (∑ m, b.repr y m • b m)) := by
      rw [b.sum_repr, ← hy]; rfl
    rw [e1, ofAdd_sum, map_prod]
    change _ = pb _
    rw [map_prod]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [ofAdd_zsmul, map_zpow, map_pow]
    change I.ev q (b m) ^ _ = (hKo ≫ s m) ^ _
    rw [hs', ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hq))]
    exact zpow_eq_zpow_emod' _ (hev _)

end GlobalTheory.HalfGeo
