import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieNormSquareOfFamilyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramLinearCombinationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramInvariantPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualBasisHermitianSumStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieNormSqBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fl.GInf

variable {S : Scheme.{0}} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

/- English proof (translation)
Apply the tactic sequence `refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dualMap_comp_alg (f : R →+* R') :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Apply the tactic sequence `refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]`.
-/
theorem dualMap_comp_epsMul (f : R →+* R') (c : R) :
    (dualMap f).comp (epsMul c) = (epsMul (f c)).comp (dualMap f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

/- English proof (translation)
Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Simplify using `[dualMap]`.
-/
theorem fst_comp_dualMap (f : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [dualMap]

/- English proof (translation)
Apply the tactic sequence `refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap]`.
-/
theorem dualMap_comp_dualMap (f : R →+* R') (g : R' →+* R'') :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap]

/- English proof (translation)
Apply the tactic sequence `refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem epsMul_zero_eq : epsMul (0 : R) =
    (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

def bar (f : R →+* R') (x : Sp R ⟶ S) : epsAt (spMap f ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap f)) (by
    show spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) ≫ x = spMap (algebraMap R' (DualNumber R')) ≫ spMap f ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg])

/- English proof (translation)
Substitute `hx` using the available equality. Conclude with `⟨bar f x ≫ u, rfl⟩`.
-/
theorem exists_bc {G : Over S} (f : R →+* R') (x : Sp R ⟶ S) {x' : Sp R' ⟶ S} (hx : x' = spMap f ≫ x)
    (u : epsAt x ⟶ G) : ∃ u' : epsAt x' ⟶ G, u'.left = spMap (dualMap f) ≫ u.left := by
  subst hx
  exact ⟨bar f x ≫ u, rfl⟩

/- English proof (translation)
Substitute `hx` using the available equality. Take `⟨u, hu, rfl⟩` from `h`. Set `φ : (epsAt x ⟶ G) →* (epsAt (spMap f ≫ x) ⟶ G)` to `{ toFun := fun y => bar f x ≫ y map_one' := comp_one _ map_mul' := fun a b => comp_mul _ _ _ }`. Use `⟨fun i => φ (u i), fun i => ?_, ?_⟩` and prove the remaining obligations. Use `show spMap (dualMap f) ≫ (u i).left = _`.

Rewrite using `[hu i, hv i, ← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_epsMul]`. Establish `e : w' = φ (List.ofFn u).prod` using `Over.OverMorphism.ext hw`. Rewrite using `[e, map_list_prod, List.map_ofFn]`. Both sides reduce to the same expression.
-/
theorem isComb_bc {G : Over S} [GrpObj G] (f : R →+* R') (x : Sp R ⟶ S) {x' : Sp R' ⟶ S} (hx : x' = spMap f ≫ x)
    {n : ℕ} (c : Fin n → R)
    (v : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) (v' : Fin n → (epsAt x' ⟶ G))
    (w' : epsAt x' ⟶ G) (hv : ∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left)
    (hw : w'.left = spMap (dualMap f) ≫ w.left) (h : Fl.IsComb c v w) :
    Fl.IsComb (fun i => f (c i)) v' w' := by
  subst hx
  obtain ⟨u, hu, rfl⟩ := h
  let φ : (epsAt x ⟶ G) →* (epsAt (spMap f ≫ x) ⟶ G) :=
    { toFun := fun y => bar f x ≫ y
      map_one' := comp_one _
      map_mul' := fun a b => comp_mul _ _ _ }
  refine ⟨fun i => φ (u i), fun i => ?_, ?_⟩
  · show spMap (dualMap f) ≫ (u i).left = _
    rw [hu i, hv i, ← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_epsMul]
  · have e : w' = φ (List.ofFn u).prod := Over.OverMorphism.ext hw
    rw [e, map_list_prod, List.map_ofFn]
    rfl

/- English proof (translation)
Rewrite using `[Hom.one_def, Over.comp_left]`. Both sides reduce to the same expression.
-/
theorem one_left {G : Over S} [GrpObj G] {T : Scheme.{0}} (x : T ⟶ S) : (1 : Over.mk x ⟶ G).left = x ≫ eSec G := by
  rw [Hom.one_def, Over.comp_left]
  rfl

/- English proof (translation)
Take `⟨u, hu, rfl⟩` from `h`. Set `U : Fin M → (epsAt x ⟶ G)` to `fun q => if hq : ∃ j, jj j = q then u hq.choose else 1`. Establish `hU : ∀ j, U (jj j) = u j` using `fun j => by`. Establish `hq : ∃ j', jj j' = jj j` using `⟨j, rfl⟩`. Simplify using `only [U, dif_pos hq]`.

Rewrite using `[hj hq.choose_spec]`. Establish `hU1 : ∀ q, q ∉ Set.range jj → U q = 1` using `fun q hq => by`. Simplify using `only [U]`. Conclude with `dif_neg hq`. Use `⟨U, fun q => ?_, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hq : q ∈ Set.range jj`. Take `⟨j, rfl⟩` from `hq`. Rewrite using `[hU, hu, hc, hv]`. Rewrite using `[hU1 q hq, h0 q hq, epsMul_zero_eq, ← spMap_comp_spMap, Category.assoc]`. Use `ht q` as an intermediate fact.

Unfold `IsTanAt at this`. Use `erw [this]`. Rewrite using `[one_left, one_left]`. Both sides reduce to the same expression. Rewrite using `[List.prod_ofFn, List.prod_ofFn]`.

Conclude with `Fintype.prod_of_injective jj hj _ _ (fun q hq => hU1 q hq) (fun j => (hU j).symm)`.
-/
theorem isComb_pad {G : Over S} [GrpObj G] [IsCommMonObj G] {x : Sp R ⟶ S} {m M : ℕ} {c : Fin m → R}
    {v : Fin m → (epsAt x ⟶ G)} {w : epsAt x ⟶ G} (C : Fin M → R) (V : Fin M → (epsAt x ⟶ G)) (jj : Fin m → Fin M)
    (hj : Function.Injective jj) (hc : ∀ j, C (jj j) = c j) (hv : ∀ j, V (jj j) = v j)
    (h0 : ∀ q, q ∉ Set.range jj → C q = 0) (ht : ∀ q, IsTanAt G x (V q)) (h : Fl.IsComb c v w) :
    Fl.IsComb C V w := by
  classical
  obtain ⟨u, hu, rfl⟩ := h
  let U : Fin M → (epsAt x ⟶ G) := fun q => if hq : ∃ j, jj j = q then u hq.choose else 1
  have hU : ∀ j, U (jj j) = u j := fun j => by
    have hq : ∃ j', jj j' = jj j := ⟨j, rfl⟩
    simp only [U, dif_pos hq]
    rw [hj hq.choose_spec]
  have hU1 : ∀ q, q ∉ Set.range jj → U q = 1 := fun q hq => by
    simp only [U]
    exact dif_neg hq
  refine ⟨U, fun q => ?_, ?_⟩
  · by_cases hq : q ∈ Set.range jj
    · obtain ⟨j, rfl⟩ := hq
      rw [hU, hu, hc, hv]
    · rw [hU1 q hq, h0 q hq, epsMul_zero_eq, ← spMap_comp_spMap, Category.assoc]
      have := ht q
      unfold IsTanAt at this
      erw [this]
      rw [one_left, one_left]
      rfl
  · rw [List.prod_ofFn, List.prod_ofFn]
    exact Fintype.prod_of_injective jj hj _ _ (fun q hq => hU1 q hq) (fun j => (hU j).symm)

end GlobalTheory.CompanionTheory.Ar.Fl.GInf

namespace GlobalTheory.CompanionTheory.Ar.Fl.GInf

variable {S : Scheme.{0}} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Substitute `hx` using the available equality. Establish `he : eSec t'.G ≫ m.φ = f ≫ eSec t.G` using `PolBaseChange.eSec_comm m.cart`. Unfold `IsTanAt`. Rewrite using `[one_left, one_left, h]`. Prove the components needed by the constructor for the conclusion.

Introduce `e`. Rewrite using `[← Category.assoc, e, Category.assoc, he, Category.assoc]`. Introduce `e`. Use `m.cart.1.hom_ext ?_ ?_` and prove the remaining obligations. Establish `he' : eSec t'.G ≫ m.cm.F = f ≫ eSec t.G` using `he`.

Rewrite using `[Category.assoc, e, Category.assoc, Category.assoc, he']`. Establish `h1 : v'.left ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x'` using `Over.w v'`. Establish `h2 : eSec t'.G ≫ t'.G.hom = 𝟙 _` using `Over.w η[t'.G]`. Rewrite using `[Category.assoc, Category.assoc, h1, h2]`. Use `Eq.trans ?_ (Category.comp_id x').symm` and prove the remaining obligations.

Use `erw [← Category.assoc, spMap_comp_spMap]`. Establish `: ((TrivSqZeroExt.fstHom R R R).toRingHom).comp (algebraMap R (DualNumber R)) = RingHom.id R`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`. Rewrite using `[this]`.

Use `show Spec.map (𝟙 _) ≫ x' = x'`. Rewrite using `[Spec.map_id, Category.id_comp]`.
-/
theorem tan_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {x' : Sp R ⟶ S'} {x : Sp R ⟶ S} (hx : x = x' ≫ f) (v' : epsAt x' ⟶ t'.G) (v : epsAt x ⟶ t.G)
    (h : v.left = v'.left ≫ m.φ) : IsTanAt t'.G x' v' ↔ IsTanAt t.G x v := by
  subst hx
  have he : eSec t'.G ≫ m.φ = f ≫ eSec t.G := PolBaseChange.eSec_comm m.cart
  unfold IsTanAt
  rw [one_left, one_left, h]
  constructor
  · intro e
    rw [← Category.assoc, e, Category.assoc, he, Category.assoc]
  · intro e
    refine m.cart.1.hom_ext ?_ ?_
    · have he' : eSec t'.G ≫ m.cm.F = f ≫ eSec t.G := he
      rw [Category.assoc, e, Category.assoc, Category.assoc, he']
    · have h1 : v'.left ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x' := Over.w v'
      have h2 : eSec t'.G ≫ t'.G.hom = 𝟙 _ := Over.w η[t'.G]
      rw [Category.assoc, Category.assoc, h1, h2]
      refine Eq.trans ?_ (Category.comp_id x').symm
      erw [← Category.assoc, spMap_comp_spMap]
      have : ((TrivSqZeroExt.fstHom R R R).toRingHom).comp (algebraMap R (DualNumber R)) = RingHom.id R := by
        refine RingHom.ext fun a => ?_
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      show Spec.map (𝟙 _) ≫ x' = x'
      rw [Spec.map_id, Category.id_comp]

/- English proof (translation)
Establish `h1 : w.left ≫ G.hom = spMap (algebraMap R (DualNumber R))` using `Over.w w`. Use `⟨Over.homMk (spMap (dualMap σ) ≫ w.left) (by show (spMap (dualMap σ) ≫ w.left) ≫ G.hom = spMap (algebraMap R' (DualNumber R')) ≫ spMap σ` and prove the remaining obligations. Rewrite using `[Category.assoc, h1, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]), rfl, fun ht => ?_⟩`. Unfold `IsTanAt`. Rewrite using `[one_left]`.

Unfold `IsTangent at ht`. Use `show spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (dualMap σ) ≫ w.left = _`. Rewrite using `[← Category.assoc, spMap_comp_spMap, fst_comp_dualMap, ← spMap_comp_spMap, Category.assoc, ht]`. Both sides reduce to the same expression.
-/
theorem exists_vec {G : Over (Sp R)} [GrpObj G] (σ : R →+* R') (w : epsR R ⟶ G) :
    ∃ U : epsAt (spMap σ) ⟶ G, U.left = spMap (dualMap σ) ≫ w.left ∧ (IsTangent w → IsTanAt G (spMap σ) U) := by
  have h1 : w.left ≫ G.hom = spMap (algebraMap R (DualNumber R)) := Over.w w
  refine ⟨Over.homMk (spMap (dualMap σ) ≫ w.left) (by
    show (spMap (dualMap σ) ≫ w.left) ≫ G.hom = spMap (algebraMap R' (DualNumber R')) ≫ spMap σ
    rw [Category.assoc, h1, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]), rfl, fun ht => ?_⟩
  unfold IsTanAt
  rw [one_left]
  unfold IsTangent at ht
  show spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (dualMap σ) ≫ w.left = _
  rw [← Category.assoc, spMap_comp_spMap, fst_comp_dualMap, ← spMap_comp_spMap, Category.assoc, ht]
  rfl

/- English proof (translation)
Establish `: Epi (CommRingCat.ofHom (algebraMap (𝓞 K) K))` using `IsLocalization.epi (nonZeroDivisors (𝓞 K)) K`. Conclude with `Scheme.Spec.map_mono (CommRingCat.ofHom _).op`.
-/
theorem mono_alg (K : Type) [Field K] [NumberField K] : Mono (spMap (algebraMap (𝓞 K) K)) := by
  have : Epi (CommRingCat.ofHom (algebraMap (𝓞 K) K)) := IsLocalization.epi (nonZeroDivisors (𝓞 K)) K
  exact Scheme.Spec.map_mono (CommRingCat.ofHom _).op

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Z : ∀ b : Bool, Curve0 H (sgnRt H b)} {c : Coeff l} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n}
  {P : (FU.Di i).La →+ (Fin g → ℂ)} {hP : IsPeriod (FU.Di i) ty P}

abbrev sg (X : CMPack Z c FU i hP) (s : X.K →+* ℂ) : 𝓞 X.K →+* ℂ := s.comp (algebraMap (𝓞 X.K) X.K)

/- English proof (translation)
Take `⟨ρ, h1, h2⟩` from `hu`. Establish `hm` using `mono_alg X.K`. Establish `hw : ρ ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K))`. Rewrite using `[← cancel_mono (spMap (algebraMap (𝓞 X.K) X.K)), Category.assoc, ← X.m'.cart.1.w, ← Category.assoc, h2, Category.assoc, Category.assoc, Over.w (X.ψ b a)]`. Establish `e1 : (X.C b).v.left ≫ (X.C b).P.A.hom = spMap (algebraMap (𝓞 X.K) (DualNumber (𝓞 X.K)))` using `Over.w (X.C b).v`.

Rewrite using `[e1, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]`. Use `⟨Over.homMk (spMap (dualMap s) ≫ ρ) (by show (spMap (dualMap s) ≫ ρ) ≫ X.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap s` and prove the remaining obligations. Rewrite using `[Category.assoc, hw, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]), ?_, ?_⟩`. Use `show (spMap (dualMap s) ≫ ρ) ≫ X.m.φ = _`. Rewrite using `[Category.assoc, h1]`.

Use `show (spMap (dualMap s) ≫ ρ) ≫ X.m'.φ = _`. Rewrite using `[Category.assoc, h2, hUx, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMap]`.
-/
theorem exists_lift (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b))
    (u : epsAt (under X.y) ⟶ Xo.univ.t.G) (hu : X.IsImage b a u) (s : X.K →+* ℂ)
    (Ux : epsAt (spMap (sg X s)) ⟶ X.B.t.G)
    (hUx : Ux.left = spMap (dualMap (sg X s)) ≫ (X.C b).v.left ≫ (X.ψ b a).left) :
    ∃ U' : epsAt (spMap s) ⟶ X.t.G, U'.left ≫ X.m.φ = spMap (dualMap s) ≫ u.left ∧ U'.left ≫ X.m'.φ = Ux.left := by
  obtain ⟨ρ, h1, h2⟩ := hu
  have hm := mono_alg X.K
  have hw : ρ ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) := by
    rw [← cancel_mono (spMap (algebraMap (𝓞 X.K) X.K)), Category.assoc, ← X.m'.cart.1.w, ← Category.assoc, h2,
      Category.assoc, Category.assoc, Over.w (X.ψ b a)]
    have e1 : (X.C b).v.left ≫ (X.C b).P.A.hom = spMap (algebraMap (𝓞 X.K) (DualNumber (𝓞 X.K))) := Over.w (X.C b).v
    rw [e1, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]
  refine ⟨Over.homMk (spMap (dualMap s) ≫ ρ) (by
    show (spMap (dualMap s) ≫ ρ) ≫ X.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap s
    rw [Category.assoc, hw, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]), ?_, ?_⟩
  · show (spMap (dualMap s) ≫ ρ) ≫ X.m.φ = _
    rw [Category.assoc, h1]
  · show (spMap (dualMap s) ≫ ρ) ≫ X.m'.φ = _
    rw [Category.assoc, h2, hUx, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMap]

/- English proof (translation)
Establish `h1 : IsTangent (X.C b).v` using `(X.C b).basis.1 0`. Establish `h2 : IsMonHom (X.ψ b a)` using `((X.fam b).1 a).isMonHom`. Unfold `IsTangent at h1 ⊢`. Rewrite using `[Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, IsMonHom.one_hom]`.
-/
theorem one_tangent (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b)) :
    IsTangent ((X.C b).v ≫ X.ψ b a) := by
  have h1 : IsTangent (X.C b).v := (X.C b).basis.1 0
  have h2 : IsMonHom (X.ψ b a) := ((X.fam b).1 a).isMonHom
  unfold IsTangent at h1 ⊢
  rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, IsMonHom.one_hom]

/- English proof (translation)
Use `show s _ = s _`. Use `congr 1`. Use `Subtype.ext ?_` and prove the remaining obligations. Establish `e1` using `(X.map b).1`. Establish `e2` using `(Z b).hω`.

Establish `e3 : 2 * τ (H.w0 : E) = 1 + τ (H.rt : E)`. Establish `h0 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E)`. Use `congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root` as an intermediate fact. Simplify using `only [map_mul, map_add, map_one, map_ofNat] at this`. Conclude with `this`.

Use `congrArg τ h0` as an intermediate fact. Rewrite `this` using `[map_mul, map_add, map_one, map_ofNat]`. Then use the resulting hypothesis. Establish `e4 : (((X.ω b : 𝓞 X.K) : X.K) : ℂ) = (((Z b).ω : (Z b).M) : ℂ)` using `by rw [← e1]; rfl`. Establish `e5 : ((X.β (tauE c τ (H.w0 : E)) : X.K) : ℂ) = τ (H.w0 : E)` using `rfl`. Rewrite using `[e4, e5]`.

Rewrite `e3` using `[hτ, ← e2]`. Take the linear combination `(1/2 : ℂ) * e3`.
-/
theorem w_eq (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = sgnRt H b) (s : X.K →+* ℂ) :
    s (X.β (tauE c τ (H.w0 : E))) = sg X s (X.ω b) := by
  show s _ = s _
  congr 1
  refine Subtype.ext ?_
  have e1 := (X.map b).1
  have e2 := (Z b).hω
  have e3 : 2 * τ (H.w0 : E) = 1 + τ (H.rt : E) := by
    have h0 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
      simp only [map_mul, map_add, map_one, map_ofNat] at this
      exact this
    have := congrArg τ h0
    rwa [map_mul, map_add, map_one, map_ofNat] at this
  have e4 : (((X.ω b : 𝓞 X.K) : X.K) : ℂ) = (((Z b).ω : (Z b).M) : ℂ) := by rw [← e1]; rfl
  have e5 : ((X.β (tauE c τ (H.w0 : E)) : X.K) : ℂ) = τ (H.w0 : E) := rfl
  rw [e4, e5]
  rw [hτ, ← e2] at e3
  linear_combination (1/2 : ℂ) * e3

def kap (X : CMPack Z c FU i hP) (τ : E →+* ℂ) (s : X.K →+* ℂ) : OK H →+* ℂ :=
  (s.comp (X.β.comp (tauE c τ))).comp ((algebraMap (𝓞 E) E).comp (OK H).val.toRingHom)

/- English proof (translation)
Establish `hU` using `fun q => exists_vec (sg X s) ((X.C b).v ≫ X.ψ b (aq q))`. Use `choose U hUl hUt using hU`. Establish `hU'` using `fun q => exists_lift X b (aq q) (Wq q) (hW q) s (U q) (hUl q)`. Use `choose U' h1 h2 using hU'`. Establish `hnorm : IsLieNormSq (X.C b).P (X.C b).v (sg X s) r` using `(T.lie_norm_sq_base_change E H _ _ _ _ (Z b).C (X.C b) _ (X.φ b) (sg X s) r (X.map b)).1 hr`.

Establish `hk : kap X τ s (wK H) = sg X s (X.ω b)` using `w_eq X b τ hτ s`. Establish `g0` using `T.lie_norm_square_of_family E H (FU.Di i) (𝓞 X.K) (X.ω b) (X.C b) X.B (fun x x' => X.h b x x') _ (X.ψ b) (sg X s) (kap X τ s) r M aq U (X.fam b) hk hnorm hUl`. Establish `hx1 : spMap (sg X s) = spMap s ≫ spMap (algebraMap (𝓞 X.K) X.K)` using `(spMap_comp_spMap _ _).symm`. Establish `hx2 : under (spMap s ≫ X.y) = spMap s ≫ under X.y` using `Category.assoc _ _ _`. Establish `hV2 : ∀ q, (V q).left = (U' q).left ≫ X.m.φ` using `fun q => (hV q).trans (h1 q).symm`.

Establish `hU2 : ∀ q, (U q).left = (U' q).left ≫ X.m'.φ` using `fun q => (h2 q).symm`. Establish `g1` using `(T.hodge_gram_invariant_pullback E H _ _ X.B.t X.t _ X.m' (spMap s) (spMap (sg X s)) M U' U _ hx1 hU2).2 g0`. Establish `g2` using `(T.hodge_gram_invariant_pullback E H _ _ Xo.univ.t X.t _ X.m (spMap s) (under (spMap s ≫ X.y)) M U' V _ hx2 hV2).1 g1`. Use `⟨fun q => ?_, g2⟩` and prove the remaining obligations. Conclude with `(tan_iff X.m hx2 (U' q) (V q) (hV2 q)).1 ((tan_iff X.m' hx1 (U' q) (U q) (hU2 q)).2 (hUt q (one_tangent X b (aq q))))`.
-/
theorem gram_family (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = sgnRt H b) (s : X.K →+* ℂ)
    (r : ℝ) (hr : IsLieNormSq (Z b).C.P (Z b).C.v
      ((s.comp (IntermediateField.inclusion (X.hM b)).toRingHom).comp (algebraMap (𝓞 (Z b).M) (Z b).M)) r)
    {M : ℕ} (aq : Fin M → PureType.lat hP (sgnRt H b)) (Wq : Fin M → (epsAt (under X.y) ⟶ Xo.univ.t.G))
    (hW : ∀ q, X.IsImage b (aq q) (Wq q)) (V : Fin M → (epsAt (under (spMap s ≫ X.y)) ⟶ Xo.univ.t.G))
    (hV : ∀ q, (V q).left = spMap (dualMap s) ≫ (Wq q).left) :
    (∀ q, IsTanAt Xo.univ.t.G (under (spMap s ≫ X.y)) (V q)) ∧
    IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under (spMap s ≫ X.y)) V
      (Matrix.of fun q q' => r * kap X τ s (X.h b (aq q) (aq q'))) := by
  have hU := fun q => exists_vec (sg X s) ((X.C b).v ≫ X.ψ b (aq q))
  choose U hUl hUt using hU
  have hU' := fun q => exists_lift X b (aq q) (Wq q) (hW q) s (U q) (hUl q)
  choose U' h1 h2 using hU'
  have hnorm : IsLieNormSq (X.C b).P (X.C b).v (sg X s) r :=
    (T.lie_norm_sq_base_change E H _ _ _ _ (Z b).C (X.C b) _ (X.φ b) (sg X s) r (X.map b)).1 hr
  have hk : kap X τ s (wK H) = sg X s (X.ω b) := w_eq X b τ hτ s
  have g0 := T.lie_norm_square_of_family E H (FU.Di i) (𝓞 X.K) (X.ω b) (X.C b) X.B (fun x x' => X.h b x x') _ (X.ψ b) (sg X s)
    (kap X τ s) r M aq U (X.fam b) hk hnorm hUl
  have hx1 : spMap (sg X s) = spMap s ≫ spMap (algebraMap (𝓞 X.K) X.K) := (spMap_comp_spMap _ _).symm
  have hx2 : under (spMap s ≫ X.y) = spMap s ≫ under X.y := Category.assoc _ _ _
  have hV2 : ∀ q, (V q).left = (U' q).left ≫ X.m.φ := fun q => (hV q).trans (h1 q).symm
  have hU2 : ∀ q, (U q).left = (U' q).left ≫ X.m'.φ := fun q => (h2 q).symm
  have g1 := (T.hodge_gram_invariant_pullback E H _ _ X.B.t X.t _ X.m' (spMap s) (spMap (sg X s)) M U' U _ hx1 hU2).2 g0
  have g2 := (T.hodge_gram_invariant_pullback E H _ _ Xo.univ.t X.t _ X.m (spMap s) (under (spMap s ≫ X.y)) M U' V _ hx2 hV2).1 g1
  refine ⟨fun q => ?_, g2⟩
  exact (tan_iff X.m hx2 (U' q) (V q) (hV2 q)).1
    ((tan_iff X.m' hx1 (U' q) (U q) (hU2 q)).2 (hUt q (one_tangent X b (aq q))))

/- English proof (translation)
Establish `hl : ∀ (k : Fin n) (F : Fin M → ℂ) (F' : Fin n × I → ℂ), (∀ q, F q = F' (e q)) → ∑ q, A k q * F q = ∑ m, x m * F' (k, m)` using `fun k F F' hF => by`. Rewrite using `[← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_eq_single k]`. Simplify using `[hA, hF]`. Introduce `b _ hb`. Simplify using `[hA, hb]`.

Simplify using the standard rewrite rules. Establish `hr : ∀ (k : Fin n) (F : Fin M → ℂ) (F' : Fin n × I → ℂ), (∀ q, F q = F' (e q)) → ∑ q, F q * star (A k q) = ∑ m, F' (k, m) * starRingEnd ℂ (x m)` using `fun k F F' hF => by`. Rewrite using `[← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_eq_single k]`. Simplify using `[hA, hF]`. Introduce `b _ hb`.

Simplify using `[hA, hb]`. Simplify using the standard rewrite rules. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]`. Rewrite using `[hr k' _ (fun p' => ∑ m, x m * G (k, m) p') (fun q' => hl k _ (fun p => G p (e q')) fun q => rfl)]`. Simplify using `only [Finset.sum_mul]`.

Conclude with `Finset.sum_comm`.
-/
theorem mat_id {n M : ℕ} {I : Type} [Fintype I] [DecidableEq I] (e : Fin M ≃ Fin n × I) (x : I → ℂ)
    (G : Fin n × I → Fin n × I → ℂ) (A : Matrix (Fin n) (Fin M) ℂ)
    (hA : ∀ k q, A k q = if (e q).1 = k then x (e q).2 else 0) (k k' : Fin n) :
    (A * Matrix.of (fun q q' => G (e q) (e q')) * Aᴴ) k k' =
      ∑ m, ∑ m', x m * G (k, m) (k', m') * starRingEnd ℂ (x m') := by
  have hl : ∀ (k : Fin n) (F : Fin M → ℂ) (F' : Fin n × I → ℂ), (∀ q, F q = F' (e q)) →
      ∑ q, A k q * F q = ∑ m, x m * F' (k, m) := fun k F F' hF => by
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_eq_single k]
    · simp [hA, hF]
    · intro b _ hb
      simp [hA, hb]
    · simp
  have hr : ∀ (k : Fin n) (F : Fin M → ℂ) (F' : Fin n × I → ℂ), (∀ q, F q = F' (e q)) →
      ∑ q, F q * star (A k q) = ∑ m, F' (k, m) * starRingEnd ℂ (x m) := fun k F F' hF => by
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_eq_single k]
    · simp [hA, hF]
    · intro b _ hb
      simp [hA, hb]
    · simp
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [hr k' _ (fun p' => ∑ m, x m * G (k, m) p') (fun q' => hl k _ (fun p => G p (e q')) fun q => rfl)]
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

end GlobalTheory.CompanionTheory.Ar.Fl.GInf

namespace GlobalTheory.CompanionTheory.Ar.Fl.GInf

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c g ty FU i Z P hP X b τ n a v s y' v' r hτ hv hy hv' hr`. Substitute `hy` using the available equality. Establish `hx2 : under (spMap s ≫ X.y) = spMap s ≫ under X.y` using `Category.assoc _ _ _`. Set `e0 : Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)` to `(Fintype.equivFin _).symm`. Set `e : Fin (n * Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))) ≃ Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 E)` to `finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) e0)`.

Use `choose nk ek uk h1 h2 using hv`. Set `W₂ : Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (epsAt (under X.y) ⟶ Xo.univ.t.G)` to `fun k m => uk k ((ek k).symm m)`. Establish `hW₂ : ∀ k m, X.IsImage b (RingOfIntegers.basis E m • a k) (W₂ k m)` using `fun k m => by`. Use `h1 k ((ek k).symm m)` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Then use the resulting hypothesis.

Establish `hVex` using `fun q => exists_bc (G := Xo.univ.t.G) s (under X.y) hx2 (W₂ (e q).1 (e q).2)`. Use `choose V hV using hVex`. Take `⟨ht, hg⟩` from `gram_family X b τ hτ s r hr (fun q => RingOfIntegers.basis E (e q).2 • a (e q).1) (fun q => W₂ (e q).1 (e q).2) (fun q => hW₂ _ _) V hV`. Set `x : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ` to `fun m => s (X.β (tauE c τ (HT.dualInt E m)))`. Set `A : Matrix (Fin n) (Fin (n * Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)))) ℂ` to `Matrix.of fun k q => if (e q).1 = k then x (e q).2 else 0`.

Establish `hcomb : ∀ k, Fl.IsComb (A k) V (v' k)` using `fun k => by`. Establish `b1` using `isComb_bc s (under X.y) hx2 _ (uk k) (v k) (fun j => V (e.symm (k, ek k j))) (v' k) (fun j => by`. Rewrite using `[hV]`. Simplify using `only [Equiv.apply_symm_apply, W₂, Equiv.symm_apply_apply]) (hv' k) (h2 k)`. Use `isComb_pad (A k) V (fun j => e.symm (k, ek k j)) (fun j j' hj => ?_) (fun j => ?_) (fun _ => rfl) (fun q hq => ?_) ht b1` and prove the remaining obligations.

Use `e.symm.injective hj` as an intermediate fact. Conclude with `(ek k).injective (Prod.ext_iff.1 this).2`. Simplify using `[A, x]`. Assume the negation of the conclusion as `hne`. Establish `hk : (e q).1 = k`.

Assume the negation of the conclusion as `hk`. Conclude with `hne (by simp [A, hk])`. Use `hq ⟨(ek k).symm (e q).2, ?_⟩` and prove the remaining obligations. Simplify using `only [Equiv.apply_symm_apply]`. Rewrite using `[← hk]`.

Conclude with `e.symm_apply_apply q`. Establish `g3` using `T.hodge_gram_linear_combination _ _ _ _ _ _ V v' _ A ht hg hcomb`. Use `g3 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k k'`. Establish `m1` using `mat_id e x (fun p p' => (r : ℂ) * kap X τ s (X.h b ((RingOfIntegers.basis E p.2 • a p.1 : PureType.lat hP (sgnRt H b)) : (FU.Di i).La) ((RingOfIntegers.basis E p'.2 • a p'.1 : PureType.lat hP (sgnRt H b)) : (FU.Di i).La))) A (fun _ _ => rfl) k k'`.

Establish `m2` using `T.dual_basis_hermitian_sum E H (FU.Di i) (X.ε b) (X.h b) (s.comp (X.β.comp (tauE c τ))) (kap X τ s) _ e0 (a k) (a k') (X.kform b) rfl`. Simplify using `only at m1`. Establish `m3 : ∑ m, ∑ m', x m * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La)) (RingOfIntegers.basis E m' • (a k' : (FU.Di i).La))) * starRingEnd ℂ (x m') = ((X.ε b : ℤ) : ℂ) * s (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (a k) (a k'))))`. Use `Eq.trans ?_ m2` and prove the remaining obligations. Rewrite using `[← Equiv.sum_comp e0]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Equiv.sum_comp e0]`. Both sides reduce to the same expression. Use `Eq.trans ?_ m1.symm` and prove the remaining obligations. Rewrite using `[Matrix.of_apply, _root_.mul_assoc, ← m3, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m' _ => ?_` and prove the remaining obligations. Use `show (r : ℂ) * (x m * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La)) (RingOfIntegers.basis E m' • (a k' : (FU.Di i).La))) * starRingEnd ℂ (x m')) = x m * ((r : ℂ) * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La)) (RingOfIntegers.basis E m' • …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hodgeGram_cmVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (n : ℕ) (a : Fin n → PureType.lat hP (sgnRt H b)) (v : Vecs X.y n) (s : X.K →+* ℂ) (y' : Sp ℂ ⟶ Xo.XF c) (v' : Vecs y' n) (r : ℝ), τ (H.rt : E) = sgnRt H b → (∀ k, X.IsCMVec b τ (a k) (v k)) → y' = spMap s ≫ X.y → (∀ k, (v' k).left = spMap (dualMap s) ≫ (v k).left) → IsLieNormSq (Z b).C.P (Z b).C.v ((s.comp (IntermediateField.inclusion (X.hM b)).toRingHom).comp (algebraMap (𝓞 (Z b).M) (Z b).M)) r → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y') v' (Matrix.of fun k k' => r * ((X.ε b : ℤ) : ℂ) * s (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (a k) (a k'))))) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X b τ n a v s y' v' r hτ hv hy hv' hr
  classical
  subst hy
  have hx2 : under (spMap s ≫ X.y) = spMap s ≫ under X.y := Category.assoc _ _ _
  let e0 : Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E) :=
    (Fintype.equivFin _).symm
  let e : Fin (n * Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))) ≃
      Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 E) :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) e0)
  choose nk ek uk h1 h2 using hv
  let W₂ : Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (epsAt (under X.y) ⟶ Xo.univ.t.G) :=
    fun k m => uk k ((ek k).symm m)
  have hW₂ : ∀ k m, X.IsImage b (RingOfIntegers.basis E m • a k) (W₂ k m) := fun k m => by
    have := h1 k ((ek k).symm m)
    rwa [Equiv.apply_symm_apply] at this
  have hVex := fun q => exists_bc (G := Xo.univ.t.G) s (under X.y) hx2 (W₂ (e q).1 (e q).2)
  choose V hV using hVex
  obtain ⟨ht, hg⟩ := gram_family X b τ hτ s r hr (fun q => RingOfIntegers.basis E (e q).2 • a (e q).1)
    (fun q => W₂ (e q).1 (e q).2) (fun q => hW₂ _ _) V hV
  let x : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ := fun m => s (X.β (tauE c τ (HT.dualInt E m)))
  let A : Matrix (Fin n) (Fin (n * Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)))) ℂ :=
    Matrix.of fun k q => if (e q).1 = k then x (e q).2 else 0
  have hcomb : ∀ k, Fl.IsComb (A k) V (v' k) := fun k => by
    have b1 := isComb_bc s (under X.y) hx2 _ (uk k) (v k) (fun j => V (e.symm (k, ek k j))) (v' k)
      (fun j => by
        rw [hV]
        simp only [Equiv.apply_symm_apply, W₂, Equiv.symm_apply_apply]) (hv' k) (h2 k)
    refine isComb_pad (A k) V (fun j => e.symm (k, ek k j)) (fun j j' hj => ?_) (fun j => ?_) (fun _ => rfl)
      (fun q hq => ?_) ht b1
    · have := e.symm.injective hj
      exact (ek k).injective (Prod.ext_iff.1 this).2
    · simp [A, x]
    · by_contra hne
      have hk : (e q).1 = k := by
        by_contra hk
        exact hne (by simp [A, hk])
      refine hq ⟨(ek k).symm (e q).2, ?_⟩
      simp only [Equiv.apply_symm_apply]
      rw [← hk]
      exact e.symm_apply_apply q
  have g3 := T.hodge_gram_linear_combination _ _ _ _ _ _ V v' _ A ht hg hcomb
  convert g3 using 1
  ext k k'
  have m1 := mat_id e x (fun p p' => (r : ℂ) * kap X τ s (X.h b
    ((RingOfIntegers.basis E p.2 • a p.1 : PureType.lat hP (sgnRt H b)) : (FU.Di i).La)
    ((RingOfIntegers.basis E p'.2 • a p'.1 : PureType.lat hP (sgnRt H b)) : (FU.Di i).La))) A (fun _ _ => rfl) k k'
  have m2 := T.dual_basis_hermitian_sum E H (FU.Di i) (X.ε b) (X.h b) (s.comp (X.β.comp (tauE c τ))) (kap X τ s) _ e0 (a k) (a k')
    (X.kform b) rfl
  dsimp only at m1
  have m3 : ∑ m, ∑ m', x m * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La))
      (RingOfIntegers.basis E m' • (a k' : (FU.Di i).La))) * starRingEnd ℂ (x m') =
      ((X.ε b : ℤ) : ℂ) * s (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (a k) (a k')))) := by
    refine Eq.trans ?_ m2
    rw [← Equiv.sum_comp e0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Equiv.sum_comp e0]
    rfl
  refine Eq.trans ?_ m1.symm
  rw [Matrix.of_apply, _root_.mul_assoc, ← m3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  show (r : ℂ) * (x m * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La))
      (RingOfIntegers.basis E m' • (a k' : (FU.Di i).La))) * starRingEnd ℂ (x m')) =
    x m * ((r : ℂ) * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La))
      (RingOfIntegers.basis E m' • (a k' : (FU.Di i).La)))) * starRingEnd ℂ (x m')
  ring

end GlobalTheory.CompanionTheory.Ar.Fl.GInf
