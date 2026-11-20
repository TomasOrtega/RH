import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointsDefinedGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPointsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NatCastSmulMemHtLat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing

noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {S : Scheme.{0}}
  (t : SAB H S) {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ S)

structure IsParam (n : ℕ) (ev : D.La → (Over.mk ξ ⟶ t.G)) (ζ₀ : Ωˣ) : Prop where
  prim : IsPrimitiveRoot ζ₀ n
  add : ∀ a b, ev (a + b) = ev a * ev b
  lin : ∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ t.act.act c
  ker : ∀ a, ev a = 1 ↔ ∃ b, a = n • b
  onto : ∀ g, g ^ n = 1 ↔ ∃ a, ev a = g
  weil : ∀ (a b : D.La) (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k)
    (xk gk : Over.mk (spMap i ≫ ξ) ⟶ t.G) (c : kˣ), xk.left = spMap i ≫ (ev a).left →
      gk.left = spMap i ≫ (ev b).left →
      (Out.WeilIs t.G t.PP.L n xk gk (unitOn c) ↔ (c : k) = i ((ζ₀ ^ D.EF a b : Ωˣ) : Ω))
  tate : ∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k),
    ∃ I : TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
      (I.ζ n : k) = f ζ₀ ∧ ∀ a, (I.ev n a).left = spMap f ≫ (ev a).left

def bcPt {K : Type} [Field K] (f : Ω →+* K) (ξ' : Sp K ⟶ S) (h : spMap f ≫ ξ = ξ') : Over.mk ξ' ⟶ Over.mk ξ :=
  Over.homMk (spMap f) h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bcPt_left {K : Type} [Field K] (f : Ω →+* K) (ξ' : Sp K ⟶ S) (h : spMap f ≫ ξ = ξ') {G : Over S}
    (g : Over.mk ξ ⟶ G) : (bcPt ξ f ξ' h ≫ g).left = spMap f ≫ g.left := rfl

/- English proof (translation)
Use `HTTie.epi_spMap f` as an intermediate fact. Establish `e' : spMap f ≫ g.left = spMap f ≫ g'.left` using `congrArg CommaMorphism.left e`. Conclude with `Over.OverMorphism.ext ((cancel_epi _).1 e')`.
-/
theorem bcPt_cancel {K : Type} [Field K] (f : Ω →+* K) (ξ' : Sp K ⟶ S) (h : spMap f ≫ ξ = ξ') {G : Over S}
    {g g' : Over.mk ξ ⟶ G} (e : bcPt ξ f ξ' h ≫ g = bcPt ξ f ξ' h ≫ g') : g = g' := by
  have := HTTie.epi_spMap f
  have e' : spMap f ≫ g.left = spMap f ≫ g'.left := congrArg CommaMorphism.left e
  exact Over.OverMorphism.ext ((cancel_epi _).1 e')

/- English proof (translation)
Take `⟨ev, ζ₀, hζ, hI⟩` from `h578 E H D S t Ω ξ n hn hpq hprop hfull hT`. Take `⟨I, -, hIe⟩` from `hI (AlgebraicClosure Ω) (algebraMap Ω _)`. Set `ψ` to `bcPt ξ (algebraMap Ω (AlgebraicClosure Ω)) _ rfl`. Establish `hψ : ∀ a, I.ev n a = ψ ≫ ev a` using `fun a => Over.OverMorphism.ext (hIe a)`. Establish `can : ∀ {g g' : Over.mk ξ ⟶ t.G}, ψ ≫ g = ψ ≫ g' → g = g'` using `fun e => bcPt_cancel ξ _ _ rfl e`.

Use `⟨ev, ζ₀, hζ, fun a b => can ?_, fun c a => can ?_, fun a => ?_, fun g => ?_, ?_, hI⟩` and prove the remaining obligations. Rewrite using `[comp_mul, ← hψ, ← hψ, ← hψ, I.add]`. Rewrite using `[← Category.assoc, ← hψ, ← hψ, I.lin]`. Rewrite using `[← I.ker n hn a, hψ]`. Conclude with `⟨fun h => by rw [h, MonObj.comp_one], fun h => can (by rw [h, MonObj.comp_one])⟩`.

Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨a, ha⟩` from `(I.onto n hn (ψ ≫ g)).1 (by rw [← HTTie.comp_pow', hg, MonObj.comp_one])`. Conclude with `⟨a, can (by rw [← hψ, ha])⟩`. Introduce and unpack `⟨a, rfl⟩`.

Use `can ?_` and prove the remaining obligations. Rewrite using `[HTTie.comp_pow', ← hψ, MonObj.comp_one]`. Conclude with `(I.onto n hn _).2 ⟨a, rfl⟩`. Introduce `a b k _ _ i xk gk c hx hg`. Take `⟨I', hz, hI'⟩` from `hI k i`.

Take `rfl : xk = I'.ev n a` from `Over.OverMorphism.ext (hx.trans (hI' a).symm)`. Take `rfl : gk = I'.ev n b` from `Over.OverMorphism.ext (hg.trans (hI' b).symm)`. Establish `h0` using `I'.isom n hn a b`. Establish `hv : ((I'.ζ n ^ D.EF a b : kˣ) : k) = i ((ζ₀ ^ D.EF a b : Ωˣ) : Ω)`. Rewrite using `[Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, hz]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[GlobalTheory.weilIs_unique_fieldPoint S t.G t.PP.L t.PP.isLB k _ n _ _ _ _ h h0, hv]`. Introduce `h`. Take `rfl : c = I'.ζ n ^ D.EF a b` from `Units.ext (h.trans hv.symm)`.

Conclude with `h0`.
-/
theorem exists_isParam (h578 : type_of% @GlobalTheory.T.torsion_points_defined_generic) [CharZero Ω] (n : ℕ) (hn : 1 ≤ n) (hpq : 0 < D.p + D.q)
    (hprop : IsProper (pullback.snd t.G.hom ξ)) (hfull : FullTorsion t.G ξ n)
    (hT : ∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k),
      Nonempty (TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)))) :
    ∃ ev ζ₀, IsParam D t ξ n ev ζ₀ := by
  obtain ⟨ev, ζ₀, hζ, hI⟩ := h578 E H D S t Ω ξ n hn hpq hprop hfull hT
  obtain ⟨I, -, hIe⟩ := hI (AlgebraicClosure Ω) (algebraMap Ω _)
  let ψ := bcPt ξ (algebraMap Ω (AlgebraicClosure Ω)) _ rfl
  have hψ : ∀ a, I.ev n a = ψ ≫ ev a := fun a => Over.OverMorphism.ext (hIe a)
  have can : ∀ {g g' : Over.mk ξ ⟶ t.G}, ψ ≫ g = ψ ≫ g' → g = g' := fun e => bcPt_cancel ξ _ _ rfl e
  refine ⟨ev, ζ₀, hζ, fun a b => can ?_, fun c a => can ?_, fun a => ?_, fun g => ?_, ?_, hI⟩
  · rw [comp_mul, ← hψ, ← hψ, ← hψ, I.add]
  · rw [← Category.assoc, ← hψ, ← hψ, I.lin]
  · rw [← I.ker n hn a, hψ]
    exact ⟨fun h => by rw [h, MonObj.comp_one], fun h => can (by rw [h, MonObj.comp_one])⟩
  · constructor
    · intro hg
      obtain ⟨a, ha⟩ := (I.onto n hn (ψ ≫ g)).1 (by rw [← HTTie.comp_pow', hg, MonObj.comp_one])
      exact ⟨a, can (by rw [← hψ, ha])⟩
    · rintro ⟨a, rfl⟩
      refine can ?_
      rw [HTTie.comp_pow', ← hψ, MonObj.comp_one]
      exact (I.onto n hn _).2 ⟨a, rfl⟩
  · intro a b k _ _ i xk gk c hx hg
    obtain ⟨I', hz, hI'⟩ := hI k i
    obtain rfl : xk = I'.ev n a := Over.OverMorphism.ext (hx.trans (hI' a).symm)
    obtain rfl : gk = I'.ev n b := Over.OverMorphism.ext (hg.trans (hI' b).symm)
    have h0 := I'.isom n hn a b
    have hv : ((I'.ζ n ^ D.EF a b : kˣ) : k) = i ((ζ₀ ^ D.EF a b : Ωˣ) : Ω) := by
      rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, hz]
    constructor
    · intro h
      rw [GlobalTheory.weilIs_unique_fieldPoint S t.G t.PP.L t.PP.isLB k _ n _ _ _ _ h h0, hv]
    · intro h
      obtain rfl : c = I'.ζ n ^ D.EF a b := Units.ext (h.trans hv.symm)
      exact h0

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hev.tate k f`.
-/
theorem IsParam.tate' {n : ℕ} {ev : D.La → (Over.mk ξ ⟶ t.G)} {ζ₀ : Ωˣ} (hev : IsParam D t ξ n ev ζ₀)
    (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k) (ξ' : Sp k ⟶ S) (h : spMap f ≫ ξ = ξ') :
    ∃ I : TateIso D k (Over.mk ξ' ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
      (I.ζ n : k) = f ζ₀ ∧ ∀ a, (I.ev n a).left = spMap f ≫ (ev a).left := by
  subst h
  exact hev.tate k f

/- English proof (translation)
Substitute `e` using the available equality. Establish `hp : IsPullback (pullback.lift (pullback.fst f (g ≫ h)) (pullback.snd f (g ≫ h) ≫ g) (by rw [pullback.condition, Category.assoc])) (pullback.snd f (g ≫ h)) (pullback.snd f h) g`. Use `IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f h)` and prove the remaining obligations. Rewrite using `[pullback.lift_fst]`. Conclude with `IsPullback.of_hasPullback f (g ≫ h)`.

Conclude with `MorphismProperty.of_isPullback (P := @IsProper) hp inferInstance`.
-/
theorem isProper_of_iso {G S Y Z : Scheme.{0}} (f : G ⟶ S) (h : Y ⟶ S) (g : Z ⟶ Y) (h' : Z ⟶ S) (e : g ≫ h = h')
    [IsProper (pullback.snd f h)] : IsProper (pullback.snd f h') := by
  subst e
  have hp : IsPullback (pullback.lift (pullback.fst f (g ≫ h)) (pullback.snd f (g ≫ h) ≫ g)
      (by rw [pullback.condition, Category.assoc])) (pullback.snd f (g ≫ h)) (pullback.snd f h) g := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f h)
    rw [pullback.lift_fst]
    exact IsPullback.of_hasPullback f (g ≫ h)
  exact MorphismProperty.of_isPullback (P := @IsProper) hp inferInstance

/- English proof (translation)
Establish `hpos : 0 < p ^ m` using `pow_pos (Fact.out : p.Prime).pos _`. Establish `hq : spMap κ.symm.toRingHom ≫ ξ = (BT.genPt A).hom ≫ x`. Rewrite using `[← hx, ← Category.assoc, ← HTTie.spec_comp]`. Use `congr 2`. Use extensionality with `a`.

Simplify using the standard rewrite rules. Establish `hκκ : spMap κ.toRingHom ≫ spMap κ.symm.toRingHom = 𝟙 _`. Rewrite using `[← HTTie.spec_comp]`. Establish `: κ.toRingHom.comp κ.symm.toRingHom = RingHom.id Ω` using `by ext a; simp`. Rewrite using `[this]`.

Conclude with `Spec.map_id _`. Set `ψ` to `bcPt ξ κ.symm.toRingHom _ hq`. Establish `ev0 : ev 0 = 1` using `(hev.ker 0).2 ⟨0, by simp⟩`. Set `φ : Multiplicative D.La →* (Over.mk ((BT.genPt A).hom ≫ x) ⟶ t.G)` to `{ toFun := fun a => ψ ≫ ev a.toAdd map_one' := by show ψ ≫ ev 0 = 1`. Rewrite using `[ev0, MonObj.comp_one]`.

Use the proof step `map_mul' := fun a b => by show ψ ≫ ev (a.toAdd + b.toAdd) = _`. Rewrite using `[hev.add, comp_mul] }`. Set `π₀ : Multiplicative D.La →* LevGrp D.La p m` to `(LinearMap.range ((p ^ m) • (LinearMap.id : D.La →ₗ[ℤ] D.La))).mkQ.toAddMonoidHom.toMultiplicative`. Establish `hπ₀ : ∀ a, π₀ (Multiplicative.ofAdd a) = lev p m a` using `fun a => rfl`. Establish `hsurj : ∀ s : LevGrp D.La p m, ∃ a, lev p m a = s` using `fun s => by`.

Take `⟨a, ha⟩` from `Submodule.Quotient.mk_surjective _ s.toAdd`. Conclude with `⟨a, congrArg Multiplicative.ofAdd ha⟩`. Establish `hlev : ∀ a : D.La, lev p m a = 1 ↔ ∃ b, a = p ^ m • b` using `fun a => by`. Establish `: lev p m a = 1 ↔ a ∈ LinearMap.range ((p ^ m) • (LinearMap.id : D.La →ₗ[ℤ] D.La))` using `Submodule.Quotient.mk_eq_zero _`. Rewrite using `[this]`.

Conclude with `⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩`. Establish `hs₀ : Function.Surjective π₀` using `fun s => by`. Take `⟨a, ha⟩` from `hsurj s`. Conclude with `⟨Multiplicative.ofAdd a, ha⟩`. Set `τ : LevGrp D.La p m →* (Over.mk ((BT.genPt A).hom ≫ x) ⟶ t.G)` to `π₀.liftOfRightInverse (Function.surjInv hs₀) (Function.rightInverse_surjInv hs₀) ⟨φ, fun z hz => by`.

Establish `h1 : lev p m z.toAdd = 1` using `hz`. Use `show ψ ≫ ev z.toAdd = 1`. Rewrite using `[(hev.ker _).2 ((hlev _).1 h1), MonObj.comp_one]⟩`. Establish `hτ : ∀ a, τ (lev p m a) = ψ ≫ ev a` using `fun a => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ (Multiplicative.ofAdd a)`. Establish `hinj : Function.Injective τ`.

Rewrite using `[injective_iff_map_eq_one]`. Introduce `s hs`. Take `⟨a, rfl⟩` from `hsurj s`. Rewrite `hs` using `[hτ]`. Conclude with `(hlev a).2 ((hev.ker a).1 (bcPt_cancel ξ _ _ hq (hs.trans (MonObj.comp_one _).symm)))`.

Establish `htor : ∀ s, τ s ^ (p ^ m) = 1` using `fun s => by`. Take `⟨a, rfl⟩` from `hsurj s`. Rewrite using `[hτ, ← HTTie.comp_pow', (hev.onto _).2 ⟨a, rfl⟩, MonObj.comp_one]`. Establish `hk : ∀ (k : Type) [Field k] (f : FractionRing A →+* k), spMap (f.comp κ.symm.toRingHom) ≫ ξ = spMap f ≫ (BT.genPt A).hom ≫ x` using `fun k _ f => by`. Rewrite using `[← hq, ← Category.assoc, ← HTTie.spec_comp]`.

Establish `hgeo : ∀ (k : Type) [Field k] [IsAlgClosed k] (f : FractionRing A →+* k) (g : Over.mk (spMap f ≫ (BT.genPt A).hom ≫ x) ⟶ t.G), g ^ (p ^ m) = 1 → ∃ s, g.left = spMap f ≫ (τ s).left`. Introduce `k _ _ f g hg`. Take `⟨I, -, hI⟩` from `hev.tate' D t ξ k _ _ (hk k f)`. Take `⟨a, rfl⟩` from `(I.onto _ hpos g).1 hg`. Use `⟨lev p m a, ?_⟩` and prove the remaining obligations.

Rewrite using `[hI, hτ, bcPt_left]`. Conclude with `(congrArg (· ≫ (ev a).left) (HTTie.spec_comp κ.symm.toRingHom f)).trans (Category.assoc _ _ _)`. Take `⟨Γ, i, hi, hpt⟩` from `h450 A (LevGrp D.La p m) S t.G t.semi x (p ^ m) hpos τ hinj htor hgeo`. Establish `hpt' : ∀ a, (Γ.pt (lev p m a)).left ≫ i = spMap κ.symm.toRingHom ≫ (ev a).left` using `fun a => by`. Rewrite using `[hpt, hτ, bcPt_left]`.

Use `⟨Γ, i, hi, fun a => ?_, fun c a => ?_, isProper_of_iso _ ξ _ _ hq, fun k _ _ f => ?_⟩` and prove the remaining obligations. Rewrite using `[hpt', ← Category.assoc, hκκ, Category.id_comp]`. Rewrite using `[← Category.assoc, hpt', hpt', hev.lin, Category.assoc]`. Both sides reduce to the same expression. Take `⟨I, hz, hI⟩` from `hev.tate' D t ξ k _ _ (hk k f)`.

Use `⟨I, hz, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hI, hpt']`. Conclude with `(congrArg (· ≫ (ev a).left) (HTTie.spec_comp κ.symm.toRingHom f)).trans (Category.assoc _ _ _)`.
-/
theorem exists_chartGroup (h450 : type_of% @GlobalTheory.T.torsion_embedding_geometric_points) (p m : ℕ) [Fact p.Prime]
    {ev : D.La → (Over.mk ξ ⟶ t.G)} {ζ₀ : Ωˣ} (hev : IsParam D t ξ (p ^ m) ev ζ₀)
    (hprop : IsProper (pullback.snd t.G.hom ξ)) (hfull : FullTorsion t.G ξ (p ^ m))
    (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CharZero A] (x : Sp A ⟶ S)
    (κ : FractionRing A ≃+* Ω) (hx : spMap (κ.toRingHom.comp (algebraMap A (FractionRing A))) ≫ x = ξ) :
    ∃ (Γ : BT.QFGroup A (LevGrp D.La p m)) (i : Γ.G.left ⟶ t.G.left), Γ.IsTorsionAlong t.G x (p ^ m) i ∧
      (∀ a, spMap κ.toRingHom ≫ (Γ.pt (lev p m a)).left ≫ i = (ev a).left) ∧
      (∀ (c : 𝓞 E) a, (Γ.pt (lev p m (c • a))).left ≫ i = (Γ.pt (lev p m a)).left ≫ i ≫ (t.act.act c).left) ∧
      IsProper (pullback.snd t.G.hom ((BT.genPt A).hom ≫ x)) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (f : FractionRing A →+* k),
        ∃ I : TateIso D k (Over.mk (spMap f ≫ (BT.genPt A).hom ≫ x) ⟶ t.G) (fun a g => g ≫ t.act.act a)
            (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
          (I.ζ (p ^ m) : k) = f (κ.symm (ζ₀ : Ω)) ∧
            ∀ a, (I.ev (p ^ m) a).left = spMap f ≫ (Γ.pt (lev p m a)).left ≫ i := by
  have hpos : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos _
  have hq : spMap κ.symm.toRingHom ≫ ξ = (BT.genPt A).hom ≫ x := by
    rw [← hx, ← Category.assoc, ← HTTie.spec_comp]
    congr 2
    ext a
    simp
  have hκκ : spMap κ.toRingHom ≫ spMap κ.symm.toRingHom = 𝟙 _ := by
    rw [← HTTie.spec_comp]
    have : κ.toRingHom.comp κ.symm.toRingHom = RingHom.id Ω := by ext a; simp
    rw [this]
    exact Spec.map_id _
  let ψ := bcPt ξ κ.symm.toRingHom _ hq
  have ev0 : ev 0 = 1 := (hev.ker 0).2 ⟨0, by simp⟩
  let φ : Multiplicative D.La →* (Over.mk ((BT.genPt A).hom ≫ x) ⟶ t.G) :=
    { toFun := fun a => ψ ≫ ev a.toAdd
      map_one' := by
        show ψ ≫ ev 0 = 1
        rw [ev0, MonObj.comp_one]
      map_mul' := fun a b => by
        show ψ ≫ ev (a.toAdd + b.toAdd) = _
        rw [hev.add, comp_mul] }
  let π₀ : Multiplicative D.La →* LevGrp D.La p m :=
    (LinearMap.range ((p ^ m) • (LinearMap.id : D.La →ₗ[ℤ] D.La))).mkQ.toAddMonoidHom.toMultiplicative
  have hπ₀ : ∀ a, π₀ (Multiplicative.ofAdd a) = lev p m a := fun a => rfl
  have hsurj : ∀ s : LevGrp D.La p m, ∃ a, lev p m a = s := fun s => by
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ s.toAdd
    exact ⟨a, congrArg Multiplicative.ofAdd ha⟩
  have hlev : ∀ a : D.La, lev p m a = 1 ↔ ∃ b, a = p ^ m • b := fun a => by
    have : lev p m a = 1 ↔ a ∈ LinearMap.range ((p ^ m) • (LinearMap.id : D.La →ₗ[ℤ] D.La)) :=
      Submodule.Quotient.mk_eq_zero _
    rw [this]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hs₀ : Function.Surjective π₀ := fun s => by
    obtain ⟨a, ha⟩ := hsurj s
    exact ⟨Multiplicative.ofAdd a, ha⟩
  let τ : LevGrp D.La p m →* (Over.mk ((BT.genPt A).hom ≫ x) ⟶ t.G) :=
    π₀.liftOfRightInverse (Function.surjInv hs₀) (Function.rightInverse_surjInv hs₀)
      ⟨φ, fun z hz => by
        have h1 : lev p m z.toAdd = 1 := hz
        show ψ ≫ ev z.toAdd = 1
        rw [(hev.ker _).2 ((hlev _).1 h1), MonObj.comp_one]⟩
  have hτ : ∀ a, τ (lev p m a) = ψ ≫ ev a := fun a =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ (Multiplicative.ofAdd a)
  have hinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    obtain ⟨a, rfl⟩ := hsurj s
    rw [hτ] at hs
    exact (hlev a).2 ((hev.ker a).1 (bcPt_cancel ξ _ _ hq (hs.trans (MonObj.comp_one _).symm)))
  have htor : ∀ s, τ s ^ (p ^ m) = 1 := fun s => by
    obtain ⟨a, rfl⟩ := hsurj s
    rw [hτ, ← HTTie.comp_pow', (hev.onto _).2 ⟨a, rfl⟩, MonObj.comp_one]
  have hk : ∀ (k : Type) [Field k] (f : FractionRing A →+* k),
      spMap (f.comp κ.symm.toRingHom) ≫ ξ = spMap f ≫ (BT.genPt A).hom ≫ x := fun k _ f => by
    rw [← hq, ← Category.assoc, ← HTTie.spec_comp]
  have hgeo : ∀ (k : Type) [Field k] [IsAlgClosed k] (f : FractionRing A →+* k)
      (g : Over.mk (spMap f ≫ (BT.genPt A).hom ≫ x) ⟶ t.G), g ^ (p ^ m) = 1 →
      ∃ s, g.left = spMap f ≫ (τ s).left := by
    intro k _ _ f g hg
    obtain ⟨I, -, hI⟩ := hev.tate' D t ξ k _ _ (hk k f)
    obtain ⟨a, rfl⟩ := (I.onto _ hpos g).1 hg
    refine ⟨lev p m a, ?_⟩
    rw [hI, hτ, bcPt_left]
    exact (congrArg (· ≫ (ev a).left) (HTTie.spec_comp κ.symm.toRingHom f)).trans (Category.assoc _ _ _)
  obtain ⟨Γ, i, hi, hpt⟩ := h450 A (LevGrp D.La p m) S t.G t.semi x (p ^ m) hpos τ hinj htor hgeo
  have hpt' : ∀ a, (Γ.pt (lev p m a)).left ≫ i = spMap κ.symm.toRingHom ≫ (ev a).left := fun a => by
    rw [hpt, hτ, bcPt_left]
  refine ⟨Γ, i, hi, fun a => ?_, fun c a => ?_, isProper_of_iso _ ξ _ _ hq, fun k _ _ f => ?_⟩
  · rw [hpt', ← Category.assoc, hκκ, Category.id_comp]
  · rw [← Category.assoc, hpt', hpt', hev.lin, Category.assoc]
    rfl
  · obtain ⟨I, hz, hI⟩ := hev.tate' D t ξ k _ _ (hk k f)
    refine ⟨I, hz, fun a => ?_⟩
    rw [hI, hpt']
    exact (congrArg (· ≫ (ev a).left) (HTTie.spec_comp κ.symm.toRingHom f)).trans (Category.assoc _ _ _)

end PositivityTheory.HtPt.Htat
