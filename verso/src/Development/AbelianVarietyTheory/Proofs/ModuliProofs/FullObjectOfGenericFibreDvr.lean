import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionIsometryPrimitiveRootBijectiveModNStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsometryOfFiniteLevelIsometries
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionSpreadsOfDensePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelIsometryOfDenseGeometricPointsStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FullSpread

section Pairing

variable {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rwa [zero_add, pow_one, pow_one]`. Consider the case `succ m ih`. Rewrite using `[pow_succ x, pow_succ c]`. Conclude with `(hW S P n T).2.1 _ _ _ _ _ ih h`.
-/
theorem weilIs_pow_left (hW : Out.WeilSt) {n : ℕ} {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs P.A P.L n x y c) (m : ℕ) : Out.WeilIs P.A P.L n (x ^ (m + 1)) y (c ^ (m + 1)) := by
  induction m with
  | zero => rwa [zero_add, pow_one, pow_one]
  | succ m ih =>
    rw [pow_succ x, pow_succ c]
    exact (hW S P n T).2.1 _ _ _ _ _ ih h

/- English proof (translation)
Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hm.ne'`. Establish `h₁` using `CommPairing.weilIs_symm P.isLB (weilIs_pow_left P hW (CommPairing.weilIs_symm P.isLB h) m)`. Rewrite `h₁` using `[inv_pow, inv_inv, Nat.cast_mul]`. Conclude with `((hW S P n T).2.2.2 _ x _ _ hu hx (by rw [← pow_mul, mul_comm, hy])).1 h₁`.
-/
theorem weilIs_lower (hW : Out.WeilSt) {n m : ℕ} (hm : 0 < m) (hu : IsUnit ((n * m : ℕ) : Γ(T.left, ⊤)))
    {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hx : x ^ (n * m) = 1) (hy : y ^ (n * m) = 1)
    (h : Out.WeilIs P.A P.L ((n * m : ℕ) : ℤ) x y c) : Out.WeilIs P.A P.L n (x ^ m) (y ^ m) (c ^ m) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have h₁ := CommPairing.weilIs_symm P.isLB (weilIs_pow_left P hW (CommPairing.weilIs_symm P.isLB h) m)
  rw [inv_pow, inv_inv, Nat.cast_mul] at h₁
  exact ((hW S P n T).2.2.2 _ x _ _ hu hx (by rw [← pow_mul, mul_comm, hy])).1 h₁

/- English proof (translation)
Establish `h₁` using `(hW S P n _).2.1 _ _ _ _ _ h h`. Rewrite `h₁` using `[_root_.mul_one]`. Establish `e : unitOn (c * c) = unitOn c * unitOn c` using `map_mul _ _ _`. Conclude with `mul_eq_left.1 (weilIs_unique_fieldPoint S P.A P.L P.isLB K x n 1 y _ _ (e ▸ h₁) h)`.
-/
theorem eq_one_of_weilIs_one {K : Type} [Field K] (hW : Out.WeilSt) {x : Sp K ⟶ S} {n : ℕ}
    {y : Over.mk x ⟶ P.A} {c : Kˣ} (h : Out.WeilIs P.A P.L n 1 y (unitOn c)) : c = 1 := by
  have h₁ := (hW S P n _).2.1 _ _ _ _ _ h h
  rw [_root_.mul_one] at h₁
  have e : unitOn (c * c) = unitOn c * unitOn c := map_mul _ _ _
  exact mul_eq_left.1 (weilIs_unique_fieldPoint S P.A P.L P.isLB K x n 1 y _ _ (e ▸ h₁) h)

end Pairing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Establish `e : ((RZ.rt H n N : RZ H n N) : ℂ) = H.rt0`. Express the relevant statement in the definitionally equal form `2 * ((1 + H.rt0) / 2) - 1 = H.rt0`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[e, H.sqrt_neg_disc_sq]`.
-/
theorem rt_sq (H : Host E) (n N : ℕ) : RZ.rt H n N ^ 2 = -(H.d : RZ H n N) := by
  apply Subtype.ext
  have e : ((RZ.rt H n N : RZ H n N) : ℂ) = H.rt0 := by
    change 2 * ((1 + H.rt0) / 2) - 1 = H.rt0
    ring
  simp [e, H.sqrt_neg_disc_sq]

def GeomAt (D : Datum H) {S : Scheme.{0}} (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) {k : Type} [Field k]
    (x : Sp k ⟶ S) (β : RZ H n N →+* k) : Prop :=
  DetCond D t.act x (β (RZ.rt H n N)) ∧
    ∃ I : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun m g g' c => Out.WeilIs t.G t.PP.L m g g' (unitOn c)),
      (I.ζ N : k) = β (RZ.ze H n N) ∧ ∀ a, toUnit _ ≫ lev a = I.ev N a

/- English proof (translation)
Take `⟨hdet, I, hI, hA⟩` from `h`. Establish `hL : LBIso t'.PP.L (t.PP.L.pull ν.cm.F)`. Take `⟨w, hw, -⟩` from `ν.lin`. Conclude with `⟨w, hw⟩`. Use `⟨(detCond_iff_of_sabMap E H D S S' t t' f ⟨ν⟩ k y _).1 hdet, ObjPull.tateMove (ObjPull.pushEquiv ν.cart (Over.mk y)).symm (fun c g => ?_) (fun m g g' c hc => ?_) I, hI, fun a => ?_⟩` and prove the remaining obligations.

Take `⟨g, rfl⟩` from `(ObjPull.pushEquiv ν.cart (Over.mk y)).surjective g`. Rewrite using `[MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _`. Rewrite using `[Category.assoc, ← ν.act, Category.assoc]`.

Conclude with `(weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f ν.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ν.cart hL (Over.mk y) m _ _ g g' _ (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g).symm (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g').symm).1 hc`. Apply `Over.OverMorphism.ext show _ = (I.ev N a).left ≫ ν.φ` to reduce the goal to its premises. Rewrite using `[← hA, Over.comp_left, Over.comp_left, ObjPull.toUnit_left', ObjPull.toUnit_left', Category.assoc, hl]`. Conclude with `Category.assoc _ _ _`.
-/
theorem GeomAt.push {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (ν : SABMap t' t f)
    {lev : D.La → (𝟙_ (Over S) ⟶ t.G)} {lev' : D.La → (𝟙_ (Over S') ⟶ t'.G)}
    (hl : ∀ a, (lev' a).left ≫ ν.φ = f ≫ (lev a).left) {k : Type} [Field k] {y : Sp k ⟶ S'} {β : RZ H n N →+* k}
    (h : GeomAt D t' lev' y β) : GeomAt D t lev (y ≫ f) β := by
  obtain ⟨hdet, I, hI, hA⟩ := h
  have hL : LBIso t'.PP.L (t.PP.L.pull ν.cm.F) := by
    obtain ⟨w, hw, -⟩ := ν.lin
    exact ⟨w, hw⟩
  refine ⟨(detCond_iff_of_sabMap E H D S S' t t' f ⟨ν⟩ k y _).1 hdet,
    ObjPull.tateMove (ObjPull.pushEquiv ν.cart (Over.mk y)).symm (fun c g => ?_) (fun m g g' c hc => ?_) I,
    hI, fun a => ?_⟩
  · obtain ⟨g, rfl⟩ := (ObjPull.pushEquiv ν.cart (Over.mk y)).surjective g
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]
    apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, ← ν.act, Category.assoc]
  · exact (weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f ν.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ν.cart hL
      (Over.mk y) m _ _ g g' _ (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g).symm
      (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g').symm).1 hc
  · apply Over.OverMorphism.ext
    show _ = (I.ev N a).left ≫ ν.φ
    rw [← hA, Over.comp_left, Over.comp_left, ObjPull.toUnit_left', ObjPull.toUnit_left', Category.assoc, hl]
    exact Category.assoc _ _ _

/- English proof (translation)
Use `t.semi.smooth` as an intermediate fact. Use `t.semi.geomConnected` as an intermediate fact. Establish `: ConnectedSpace t.G.left` using `GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap`. Take `⟨g, hg⟩` from `exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)`. Set `P : Out.PolAV S` to `{ A := t.G, g := g, smoothDim := hg, L := t.PP.L, isLB := t.PP.isLB, ample := ha, ktriv := hk isAb := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩ rigid := ObjDim.rigidified sym := ObjDim.sym }`.

Establish `hdet : DetCond D t.act x (β (RZ.rt H n N))` using `GlobalTheory.T.determinantCondition_spreads_of_dense_points E H D S t.G g t.act _ s _ hg (rt_sq H n N) (hd.mono fun p hp => by`. Take `⟨K, _, _, _, x, β, h₁, h₂, h₃, -⟩` from `hp`. Conclude with `⟨K, inferInstance, inferInstance, inferInstance, x, β, h₁, h₂, h₃⟩) K x β hx`. Use `⟨hdet, ?_⟩` and prove the remaining obligations. Establish `hdim : g = Module.finrank ℚ E / 2 * (D.p + D.q)` using `ObjDim.dim_eq_of_detCond D t.act x (by rw [← map_pow, rt_sq, map_neg, map_natCast]) hdet ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback t.G.hom x) hg)`.

Establish `e₀ : ∀ {K : Type} [Field K] (x : Sp K ⟶ S), (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) = toUnit (Over.mk x)` using `fun x => Over.OverMorphism.ext (ObjPull.toUnit_left' (Over.mk x)).symm`. Establish `hcard : ∀ m, 0 < m → Nat.card {z : Over.mk x ⟶ t.G // z ^ m = 1} = m ^ Module.finrank ℤ D.La` using `fun m hm => by`. Rewrite using `[finrank_int_lattice D, ← hdim]`. Conclude with `(hL.mulN S P m hm).2.2.2.2 K x (Nat.cast_ne_zero.2 hm.ne')`. Take `⟨I, hI, hA⟩` from `GlobalTheory.TateTower.tateIso_of_levels E H D K (Over.mk x ⟶ t.G) (fun c z => z ≫ t.act.act c) (fun n z z' c => Out.WeilIs t.G t.PP.L n z z' (unitOn c)) N (β (RZ.ze H n N)) _ id (fun i => toUnit _ ≫ lev i) hN (fun n hn => Nat.finite_of_card_ne_zero (by rw [hcard n hn]; positivit …`.

Establish `e : unitOn (c ^ m) = unitOn c ^ m` using `map_pow _ _ _`. Establish `u : IsUnit ((n * m : ℕ) : K)` using `(Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne').isUnit`. Establish `u'` using `u.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom`. Rewrite `u'` using `[map_natCast]`. Rewrite using `[e]`.

Conclude with `weilIs_lower P hL.weil hm u' hz hz' h)`. Use the proof step `(fun m hm => by`. Establish `hn` using `Nat.mul_pos hN hm`. Take `⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩` from `GlobalTheory.T.exists_level_isometry_of_dense_geometric_points hL E H D S P t.act.act _ s (RZ.ze H n N) _ id lev (N * m) m hn (hd.mono fun p hp => by`. Take `⟨K, _, _, _, x, β, h₁, h₂, -, I, h₃, h₄⟩` from `hp`.

Conclude with `⟨K, inferInstance, x, β, I.ζ (N * m), I.ev (N * m), Nat.cast_ne_zero.2 hn.ne', h₁, h₂, I.ζ_prim _ hn, I.add _, fun v => (I.onto _ hn _).2 ⟨v, rfl⟩, I.lin _, I.isom _ hn, by rw [← h₃, ← I.ζ_pow N m hN hm, Units.val_pow_eq_pow_val], fun i => (I.tower N m hN hm _).trans ((h₄ i).symm …`. Use `K x β (Nat.cast_ne_zero.2 hn.ne') hx`. Take `⟨h₈, h₉⟩` from `GlobalTheory.T.torsionIsometry_primitiveRoot_bijective_mod_n E H D K (Over.mk x ⟶ t.G) (fun z z' c => Out.WeilIs t.G t.PP.L (N * m : ℕ) z z' (unitOn c)) (N * m) ζ ev hn (hcard _ hn) (fun _ _ _ h => eq_one_of_weilIs_one P hL.weil h) h₁ h₂ h₃ h₅`. Conclude with `⟨ζ, ev, h₁, h₂, h₄, h₈, h₉, h₅, h₆, fun i => (h₇ i).trans (congrArg (· ≫ lev i) (e₀ x))⟩)`. Conclude with `⟨I, hI, fun a => (hA a).symm⟩`.
-/
theorem geomAt_of_dense (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] [IsReduced S] [ConnectedSpace S]
    (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (hN : 0 < N)
    (hp : IsProper t.G.hom) (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L)
    (hd : Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S)
      (β : RZ H n N →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ GeomAt D t lev x β})
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ S) (β : RZ H n N →+* K) (hx : x ≫ s = spMap β) :
    GeomAt D t lev x β := by
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  let P : Out.PolAV S :=
    { A := t.G, g := g, smoothDim := hg, L := t.PP.L, isLB := t.PP.isLB, ample := ha, ktriv := hk
      isAb := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
      rigid := ObjDim.rigidified
      sym := ObjDim.sym }
  have hdet : DetCond D t.act x (β (RZ.rt H n N)) :=
    GlobalTheory.T.determinantCondition_spreads_of_dense_points E H D S t.G g t.act _ s _ hg (rt_sq H n N) (hd.mono fun p hp => by
      obtain ⟨K, _, _, _, x, β, h₁, h₂, h₃, -⟩ := hp
      exact ⟨K, inferInstance, inferInstance, inferInstance, x, β, h₁, h₂, h₃⟩) K x β hx
  refine ⟨hdet, ?_⟩
  have hdim : g = Module.finrank ℚ E / 2 * (D.p + D.q) :=
    ObjDim.dim_eq_of_detCond D t.act x (by rw [← map_pow, rt_sq, map_neg, map_natCast]) hdet
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback t.G.hom x) hg)
  have e₀ : ∀ {K : Type} [Field K] (x : Sp K ⟶ S),
      (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) = toUnit (Over.mk x) := fun x =>
    Over.OverMorphism.ext (ObjPull.toUnit_left' (Over.mk x)).symm
  have hcard : ∀ m, 0 < m → Nat.card {z : Over.mk x ⟶ t.G // z ^ m = 1} = m ^ Module.finrank ℤ D.La := fun m hm => by
    rw [finrank_int_lattice D, ← hdim]
    exact (hL.mulN S P m hm).2.2.2.2 K x (Nat.cast_ne_zero.2 hm.ne')
  obtain ⟨I, hI, hA⟩ := GlobalTheory.TateTower.tateIso_of_levels E H D K (Over.mk x ⟶ t.G) (fun c z => z ≫ t.act.act c)
    (fun n z z' c => Out.WeilIs t.G t.PP.L n z z' (unitOn c)) N (β (RZ.ze H n N)) _ id
    (fun i => toUnit _ ≫ lev i) hN
    (fun n hn => Nat.finite_of_card_ne_zero (by rw [hcard n hn]; positivity))
    (fun n m z z' c hn hm hz hz' h => by
      have e : unitOn (c ^ m) = unitOn c ^ m := map_pow _ _ _
      have u : IsUnit ((n * m : ℕ) : K) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne').isUnit
      have u' := u.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast] at u'
      rw [e]
      exact weilIs_lower P hL.weil hm u' hz hz' h)
    (fun m hm => by
      have hn := Nat.mul_pos hN hm
      obtain ⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := GlobalTheory.T.exists_level_isometry_of_dense_geometric_points hL E H D S P t.act.act _ s (RZ.ze H n N) _
        id lev (N * m) m hn (hd.mono fun p hp => by
          obtain ⟨K, _, _, _, x, β, h₁, h₂, -, I, h₃, h₄⟩ := hp
          exact ⟨K, inferInstance, x, β, I.ζ (N * m), I.ev (N * m), Nat.cast_ne_zero.2 hn.ne', h₁, h₂, I.ζ_prim _ hn,
            I.add _, fun v => (I.onto _ hn _).2 ⟨v, rfl⟩, I.lin _, I.isom _ hn,
            by rw [← h₃, ← I.ζ_pow N m hN hm, Units.val_pow_eq_pow_val],
            fun i => (I.tower N m hN hm _).trans ((h₄ i).symm.trans (congrArg (· ≫ lev i) (e₀ x).symm))⟩)
          K x β (Nat.cast_ne_zero.2 hn.ne') hx
      obtain ⟨h₈, h₉⟩ := GlobalTheory.T.torsionIsometry_primitiveRoot_bijective_mod_n E H D K (Over.mk x ⟶ t.G)
        (fun z z' c => Out.WeilIs t.G t.PP.L (N * m : ℕ) z z' (unitOn c)) (N * m) ζ ev hn (hcard _ hn)
        (fun _ _ _ h => eq_one_of_weilIs_one P hL.weil h) h₁ h₂ h₃ h₅
      exact ⟨ζ, ev, h₁, h₂, h₄, h₈, h₉, h₅, h₆, fun i => (h₇ i).trans (congrArg (· ≫ lev i) (e₀ x))⟩)
  exact ⟨I, hI, fun a => (hA a).symm⟩

/- English proof (translation)
Introduce `hL _ E _ _ _ H D n N V K _ _ _ _ _ _ s t lv tK ν lvK hN hp ha hk hadd hker hl o`. Use `⟨hp, ha, hk, hadd, hker, fun k _ _ _ x β hx => ?_⟩` and prove the remaining obligations. Establish `: CharZero V` using `(Spec.preimage x).hom.charZero`. Establish `: CharZero K` using `charZero_of_injective_algebraMap (IsFractionRing.injective V K)`. Set `Ω` to `AlgebraicClosure K`.

Set `y : Sp Ω ⟶ Sp K` to `spMap (algebraMap K Ω)`. Take `⟨b, hb⟩ : ∃ b : RZ H n N →+* Ω, y ≫ spMap (algebraMap V K) ≫ s = spMap b` from `⟨(Spec.preimage (y ≫ spMap (algebraMap V K) ≫ s)).hom, (Spec.map_preimage _).symm⟩`. Establish `hΩ : GeomAt D t lv (y ≫ spMap (algebraMap V K)) b` using `GeomAt.push ν hl (o.geom Ω y b hb)`. Establish `hdense : Dense {(⊥ : PrimeSpectrum V)}`. Rewrite using `[dense_iff_closure_eq, PrimeSpectrum.closure_singleton]`.

Simplify using the standard rewrite rules. Use `geomAt_of_dense hL s t lv hN hp ha hk (Dense.mono ?_ hdense) k x β hx` and prove the remaining obligations. Introduce and unpack `_ rfl`. Use `⟨Ω, inferInstance, inferInstance, inferInstance, _, b, ⟨(⊥ : PrimeSpectrum Ω), ?_⟩, (Category.assoc _ _ _).trans hb, hΩ⟩` and prove the remaining obligations. Apply `PrimeSpectrum.ext` to reduce the goal to its premises.

Use `show Ideal.comap (algebraMap V K) (Ideal.comap (algebraMap K Ω) ⊥) = ⊥`. Rewrite using `[Ideal.comap_bot_of_injective _ (algebraMap K Ω).injective, Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)]`.
-/
theorem fullObj_of_genericFibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (s : Sp V ⟶ Sp (RZ H n N)) (t : SAB H (Sp V)) (lv : D.La → (𝟙_ (Over (Sp V)) ⟶ t.G)) (tK : SAB H (Sp K)) (ν : SABMap tK t (spMap (algebraMap V K))) (lvK : D.La → (𝟙_ (Over (Sp K)) ⟶ tK.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ a, (lvK a).left ≫ ν.φ = spMap (algebraMap V K) ≫ (lv a).left) → FullObj D (spMap (algebraMap V K) ≫ s) tK lvK → FullObj D s t lv := by
  intro hL _ E _ _ _ H D n N V K _ _ _ _ _ _ s t lv tK ν lvK hN hp ha hk hadd hker hl o
  refine ⟨hp, ha, hk, hadd, hker, fun k _ _ _ x β hx => ?_⟩
  have : CharZero V := (Spec.preimage x).hom.charZero
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
  let Ω := AlgebraicClosure K
  let y : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  obtain ⟨b, hb⟩ : ∃ b : RZ H n N →+* Ω, y ≫ spMap (algebraMap V K) ≫ s = spMap b :=
    ⟨(Spec.preimage (y ≫ spMap (algebraMap V K) ≫ s)).hom, (Spec.map_preimage _).symm⟩
  have hΩ : GeomAt D t lv (y ≫ spMap (algebraMap V K)) b := GeomAt.push ν hl (o.geom Ω y b hb)
  have hdense : Dense {(⊥ : PrimeSpectrum V)} := by
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    simp
  refine geomAt_of_dense hL s t lv hN hp ha hk (Dense.mono ?_ hdense) k x β hx
  rintro _ rfl
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, _, b, ⟨(⊥ : PrimeSpectrum Ω), ?_⟩,
    (Category.assoc _ _ _).trans hb, hΩ⟩
  apply PrimeSpectrum.ext
  show Ideal.comap (algebraMap V K) (Ideal.comap (algebraMap K Ω) ⊥) = ⊥
  rw [Ideal.comap_bot_of_injective _ (algebraMap K Ω).injective,
    Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)]

end GlobalTheory.FullSpread
