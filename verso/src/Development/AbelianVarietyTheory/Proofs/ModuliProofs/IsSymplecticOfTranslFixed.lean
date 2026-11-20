import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SiegelFamilyZetaUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.CechPic GlobalTheory.MatrixBundle GlobalTheory.SiegelPull GlobalTheory.SiegelPullComp GlobalTheory.EighthPower GlobalTheory.ZM
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelTypings

/- English proof (translation)
Use `le_antisymm (Subring.closure_le.2 ?_) (Subring.closure_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `x (hx | ⟨n, hn, rfl⟩)`. Conclude with `Subring.subset_closure (Or.inr hx)`. Use `Subring.subset_closure (Or.inl ⟨(n : ℚ)⁻¹, ?_, by simp⟩)` and prove the remaining obligations. Establish `h0 : n ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hp.one_lt.ne' (by simpa using hn)`. Rewrite using `[Rat.inv_natCast_den, if_neg h0]`. Conclude with `(hp.coprime_iff_not_dvd).1 hn.symm`. Introduce and unpack `x (⟨q, hq, rfl⟩ | hx)`.

Rewrite using `[Rat.cast_def, div_eq_mul_inv]`. Conclude with `Subring.mul_mem _ (intCast_mem _ _) (Subring.subset_closure (Or.inr ⟨q.den, ((hp.coprime_iff_not_dvd).2 hq).symm, rfl⟩))`. Conclude with `Subring.subset_closure (Or.inl hx)`.
-/
theorem zp_eq_cycloLocal {p : ℕ} (hp : p.Prime) (M : ℕ) : ZP p M = cycloLocal p M := by
  refine le_antisymm (Subring.closure_le.2 ?_) (Subring.closure_le.2 ?_)
  · rintro x (hx | ⟨n, hn, rfl⟩)
    · exact Subring.subset_closure (Or.inr hx)
    · refine Subring.subset_closure (Or.inl ⟨(n : ℚ)⁻¹, ?_, by simp⟩)
      have h0 : n ≠ 0 := by
        rintro rfl
        exact hp.one_lt.ne' (by simpa using hn)
      rw [Rat.inv_natCast_den, if_neg h0]
      exact (hp.coprime_iff_not_dvd).1 hn.symm
  · rintro x (⟨q, hq, rfl⟩ | hx)
    · rw [Rat.cast_def, div_eq_mul_inv]
      exact Subring.mul_mem _ (intCast_mem _ _)
        (Subring.subset_closure (Or.inr ⟨q.den, ((hp.coprime_iff_not_dvd).2 hq).symm, rfl⟩))
    · exact Subring.subset_closure (Or.inl hx)

/- English proof (translation)
Establish `h0 : M ≠ 0`. Introduce and unpack `rfl`. Conclude with `hp.one_lt.ne' (by simpa using hM)`. Establish `hm : ((M : ℂ))⁻¹ ∈ cycloLocal p M`. Rewrite using `[← zp_eq_cycloLocal hp]`.

Conclude with `Subring.subset_closure (Or.inr ⟨M, hM, rfl⟩)`. Use `IsUnit.of_mul_eq_one ⟨_, hm⟩ (Subtype.ext ?_)` and prove the remaining obligations. Simplify using `using mul_inv_cancel₀ (Nat.cast_ne_zero.2 h0 : (M : ℂ) ≠ 0)`.
-/
theorem isUnit_cycloLocal {p M : ℕ} (hp : p.Prime) (hM : M.Coprime p) : IsUnit (M : cycloLocal p M) := by
  have h0 : M ≠ 0 := by
    rintro rfl
    exact hp.one_lt.ne' (by simpa using hM)
  have hm : ((M : ℂ))⁻¹ ∈ cycloLocal p M := by
    rw [← zp_eq_cycloLocal hp]
    exact Subring.subset_closure (Or.inr ⟨M, hM, rfl⟩)
  refine IsUnit.of_mul_eq_one ⟨_, hm⟩ (Subtype.ext ?_)
  simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 h0 : (M : ℂ) ≠ 0)

section Labels

variable {h : ℕ} (M : ℕ)

def red (a : Fin h ⊕ Fin h → ℤ) : Std h M := (fun i => (a (.inl i) : ZMod M), fun i => (a (.inr i) : ZMod M))

variable {M}

def lft (a : Std h M) : Fin h ⊕ Fin h → ℤ := Sum.elim (fun i => (a.1 i).cast) fun i => (a.2 i).cast

/- English proof (translation)
Apply the tactic sequence `ext i <;> simp [red, lft]`.
-/
theorem red_lft (a : Std h M) : red M (lft a) = a := by
  ext i <;> simp [red, lft]

/- English proof (translation)
Apply the tactic sequence `ext i <;> simp [red]`.
-/
theorem red_add (a b : Fin h ⊕ Fin h → ℤ) : red M (a + b) = red M a + red M b := by
  ext i <;> simp [red]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `e`. Establish `d : ∀ j, (M : ℤ) ∣ a j - b j`. Introduce and unpack `(i | i)`. Conclude with `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (congrFun (congrArg Prod.fst e) i).symm`.

Conclude with `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (congrFun (congrArg Prod.snd e) i).symm`. Use `choose c hc using d`. Conclude with `⟨c, funext fun j => by simp [← hc j]⟩`. Introduce and unpack `⟨c, rfl⟩`. Apply the tactic sequence `ext i <;> simp [red]`.
-/
theorem red_eq_iff (a b : Fin h ⊕ Fin h → ℤ) : red M a = red M b ↔ ∃ c, a = b + M • c := by
  constructor
  · intro e
    have d : ∀ j, (M : ℤ) ∣ a j - b j := by
      rintro (i | i)
      · exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (congrFun (congrArg Prod.fst e) i).symm
      · exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (congrFun (congrArg Prod.snd e) i).symm
    choose c hc using d
    exact ⟨c, funext fun j => by simp [← hc j]⟩
  · rintro ⟨c, rfl⟩
    ext i <;> simp [red]

/- English proof (translation)
Apply the tactic sequence `ext i <;> simp [red]`.
-/
theorem red_zero : red M (0 : Fin h ⊕ Fin h → ℤ) = 0 := by
  ext i <;> simp [red]

/- English proof (translation)
Simplify using `[stdForm, red, omegaStd]`.
-/
theorem stdForm_red (a b : Fin h ⊕ Fin h → ℤ) : stdForm (red M a) (red M b) = (omegaStd a b : ZMod M) := by
  simp [stdForm, red, omegaStd]

/- English proof (translation)
Establish `: NeZero M` using `⟨hM⟩`. Rewrite using `[← zpow_natCast]`. Take `⟨c, hc⟩ : (M : ℤ) ∣ 2 * omegaStd a b - ((2 * stdForm (red M a) (red M b)).val : ℕ)` from `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (by simp [stdForm_red])`. Rewrite using `[sub_eq_iff_eq_add.1 hc, zpow_add, zpow_mul, zpow_natCast z M, hz, one_zpow, _root_.one_mul]`.
-/
theorem pow_form {U : Type} [CommGroup U] (hM : M ≠ 0) {z : U} (hz : z ^ M = 1) (a b : Fin h ⊕ Fin h → ℤ) :
    z ^ (2 * stdForm (red M a) (red M b)).val = z ^ (2 * omegaStd a b) := by
  have : NeZero M := ⟨hM⟩
  rw [← zpow_natCast]
  obtain ⟨c, hc⟩ : (M : ℤ) ∣ 2 * omegaStd a b - ((2 * stdForm (red M a) (red M b)).val : ℕ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (by simp [stdForm_red])
  rw [sub_eq_iff_eq_add.1 hc, zpow_add, zpow_mul, zpow_natCast z M, hz, one_zpow, _root_.one_mul]

/- English proof (translation)
Establish `: NeZero M` using `⟨hM⟩`. Simplify using `[Nat.card_prod, two_mul, pow_add]`.
-/
theorem card_std (hM : M ≠ 0) : Nat.card (Std h M) = M ^ (2 * h) := by
  have : NeZero M := ⟨hM⟩
  simp [Nat.card_prod, two_mul, pow_add]

end Labels

section Objects

variable {h M : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}

def lvOf {ζ : B} (o : SiegPre h M ζ s) (a : Std h M) : 𝟙_ (Over S) ⟶ o.A := o.lev (lft a)

/- English proof (translation)
Establish `e` using `o.lev_add 0 0`. Rewrite `e` using `[add_zero]`. Conclude with `left_eq_mul.1 e`.
-/
theorem lev_zero {ζ : B} (o : SiegPre h M ζ s) : o.lev 0 = 1 := by
  have e := o.lev_add 0 0
  rw [add_zero] at e
  exact left_eq_mul.1 e

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_smul, pow_zero, lev_zero]`. Consider the case `succ n ih => rw [succ_nsmul, o.lev_add, ih, pow_succ]`.
-/
theorem lev_nsmul {ζ : B} (o : SiegPre h M ζ s) (n : ℕ) (a) : o.lev (n • a) = o.lev a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, lev_zero]
  | succ n ih => rw [succ_nsmul, o.lev_add, ih, pow_succ]

/- English proof (translation)
Take `⟨c, hc⟩` from `(red_eq_iff _ _).1 (red_lft (red M a))`. Rewrite using `[lvOf, hc, o.lev_add, lev_nsmul, o.lev_tors, _root_.mul_one]`.
-/
theorem lvOf_red {ζ : B} (o : SiegPre h M ζ s) (a) : lvOf o (red M a) = o.lev a := by
  obtain ⟨c, hc⟩ := (red_eq_iff _ _).1 (red_lft (red M a))
  rw [lvOf, hc, o.lev_add, lev_nsmul, o.lev_tors, _root_.mul_one]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨φ, φ₂, pb, sq, iso, hl⟩`. Conclude with `⟨φ, φ₂, pb, sq.1, sq.2, iso, fun a => hl _⟩`. Introduce and unpack `⟨φ, φ₂, pb, s₁, s₂, iso, hl⟩`. Conclude with `⟨φ, φ₂, pb, ⟨s₁, s₂⟩, iso, fun a => by rw [← lvOf_red, ← lvOf_red]; exact hl _⟩`.
-/
theorem siegPB_iff {ζ : B} {ζ' : B'} (o' : SiegPre h M ζ' s') (o : SiegPre h M ζ s) (f : S' ⟶ S) :
    SiegPB o' o f ↔ IsPullbackTriple o'.A o'.P (lvOf o') o.A o.P (lvOf o) f := by
  constructor
  · rintro ⟨φ, φ₂, pb, sq, iso, hl⟩
    exact ⟨φ, φ₂, pb, sq.1, sq.2, iso, fun a => hl _⟩
  · rintro ⟨φ, φ₂, pb, s₁, s₂, iso, hl⟩
    exact ⟨φ, φ₂, pb, ⟨s₁, s₂⟩, iso, fun a => by rw [← lvOf_red, ← lvOf_red]; exact hl _⟩

/- English proof (translation)
The claim follows from `e ▸ H`.
-/
theorem siegPB_congr {ζ : B} {ζ' : B'} {o' : SiegPre h M ζ' s'} {o : SiegPre h M ζ s} {f g : S' ⟶ S}
    (H : SiegPB o' o f) (e : f = g) : SiegPB o' o g := e ▸ H

/- English proof (translation)
Use `(cls_eq_zero_iff (pull_isLB hP _)).symm.trans (Iff.trans ?_ (cls_eq_zero_iff (pull_isLB hP _)))` and prove the remaining obligations. Use `show pairCls (cls P hP) _ _ = 0 ↔ pairCls (cls P hP) _ _ = 0`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Use `congrArg (pull (lift (snd T A) (fst T A)).left) e` as an intermediate fact.

Rewrite `this` using `[pull_pairCls, map_zero, lift_snd_assoc, lift_fst]`. Then use the resulting hypothesis. Introduce `e`. Use `congrArg (pull (lift (snd A T) (fst A T)).left) e` as an intermediate fact. Rewrite `this` using `[pull_pairCls, map_zero, lift_fst_assoc, lift_snd]`. Then use the resulting hypothesis.
-/
theorem triv_swap {A : Over S} {P : LB (A ⊗ A).left} (hP : P.IsLB) {T : Over S} (x : T ⟶ A) :
    (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) ↔ IsTrivial (slice A P x) := by
  refine (cls_eq_zero_iff (pull_isLB hP _)).symm.trans (Iff.trans ?_ (cls_eq_zero_iff (pull_isLB hP _)))
  show pairCls (cls P hP) _ _ = 0 ↔ pairCls (cls P hP) _ _ = 0
  constructor
  · intro e
    have := congrArg (pull (lift (snd T A) (fst T A)).left) e
    rwa [pull_pairCls, map_zero, lift_snd_assoc, lift_fst] at this
  · intro e
    have := congrArg (pull (lift (snd A T) (fst A T)).left) e
    rwa [pull_pairCls, map_zero, lift_fst_assoc, lift_snd] at this

/- English proof (translation)
The claim follows from `and_congr Iff.rfl (forall₂_congr fun _ x => imp_congr_left (triv_swap o.isLB x))`.
-/
theorem principal_iff {ζ : B} (o : SiegPre h M ζ s) : o.Principal ↔ IsPrincipal o.A o.P :=
  and_congr Iff.rfl (forall₂_congr fun _ x => imp_congr_left (triv_swap o.isLB x))

/- English proof (translation)
Establish `add : ∀ a b, lvOf o (a + b) = lvOf o a * lvOf o b` using `fun a b => by`. Rewrite using `[← red_lft a, ← red_lft b, ← red_add, lvOf_red, lvOf_red, lvOf_red, o.lev_add]`. Use `⟨add, fun k _ _ x => ?_⟩` and prove the remaining obligations. Take `⟨β, hβ⟩` from `exists_spMap (x ≫ s)`. Take `⟨g₁, g₂, -⟩` from `o.geom k x β (Units.map β.toMonoidHom ζ) hβ rfl`.

Use `⟨fun a b e => ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩` and prove the remaining obligations. Establish `e₁ : o.lev (lft a) = o.lev (lft a - lft b) * o.lev (lft b)` using `by rw [← o.lev_add, sub_add_cancel]`. Establish `e₂ : toUnit (Over.mk x) ≫ o.lev (lft a) = toUnit (Over.mk x) ≫ o.lev (lft b)` using `e`. Rewrite `e₂` using `[e₁, MonObj.comp_mul, mul_eq_right]`. Take `⟨c, hc⟩` from `(g₁ _).1 e₂`.

Rewrite using `[← red_lft a, ← red_lft b]`. Conclude with `(red_eq_iff _ _).2 ⟨c, by rw [← hc, add_sub_cancel]⟩`. Take `⟨a, ha⟩` from `g₂ g hg`. Conclude with `⟨red M a, by rw [lvOf_red, ha]⟩`. Introduce and unpack `⟨a, rfl⟩`.

Rewrite using `[← MonObj.comp_pow, lvOf, o.lev_tors, MonObj.comp_one]`.
-/
theorem isLevel_lvOf {ζ : Bˣ} (o : SiegPre h M (ζ : B) s) : IsLevel o.A (lvOf o) := by
  have add : ∀ a b, lvOf o (a + b) = lvOf o a * lvOf o b := fun a b => by
    rw [← red_lft a, ← red_lft b, ← red_add, lvOf_red, lvOf_red, lvOf_red, o.lev_add]
  refine ⟨add, fun k _ _ x => ?_⟩
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
  obtain ⟨g₁, g₂, -⟩ := o.geom k x β (Units.map β.toMonoidHom ζ) hβ rfl
  refine ⟨fun a b e => ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · have e₁ : o.lev (lft a) = o.lev (lft a - lft b) * o.lev (lft b) := by rw [← o.lev_add, sub_add_cancel]
    have e₂ : toUnit (Over.mk x) ≫ o.lev (lft a) = toUnit (Over.mk x) ≫ o.lev (lft b) := e
    rw [e₁, MonObj.comp_mul, mul_eq_right] at e₂
    obtain ⟨c, hc⟩ := (g₁ _).1 e₂
    rw [← red_lft a, ← red_lft b]
    exact (red_eq_iff _ _).2 ⟨c, by rw [← hc, add_sub_cancel]⟩
  · obtain ⟨a, ha⟩ := g₂ g hg
    exact ⟨red M a, by rw [lvOf_red, ha]⟩
  · rintro ⟨a, rfl⟩
    rw [← MonObj.comp_pow, lvOf, o.lev_tors, MonObj.comp_one]

/- English proof (translation)
Assemble the required witnesses or components as `⟨AlgebraicClosure (S.residueField p), inferInstance, inferInstance, spMap (algebraMap (S.residueField p) _) ≫ S.fromSpecResidueField p, IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply p _⟩`.
-/
theorem exists_geomPt (p : S) : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (t : Sp K ⟶ S), p ∈ Set.range t :=
  ⟨AlgebraicClosure (S.residueField p), inferInstance, inferInstance,
    spMap (algebraMap (S.residueField p) _) ≫ S.fromSpecResidueField p,
    IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply p _⟩

/- English proof (translation)
Use `o.ab.smooth` as an intermediate fact. Use `choose n W hW hd using H1.exists_dim o.A.hom`. Establish `: IsZariskiLocalAtSource (@SmoothOfRelativeDimension h)` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension h) W (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_` and prove the remaining obligations. Take `⟨K, _, _, t, ht⟩` from `exists_geomPt (o.A.hom x)`.

Take `⟨c, φ, φ₂, pb, -⟩` from `(siegPre_pullback h M B ζ S _ s _ t o rfl).1`. Use `c.ab.smooth` as an intermediate fact. Use `c.ab.geomConnected` as an intermediate fact. Establish `: ConnectedSpace c.A.left` using `GeometricallyConnected.connectedSpace c.A.hom c.A.hom.isOpenMap`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : x ∈ Set.range (pullback.fst o.A.hom t) := by`.

Rewrite using `[Scheme.Pullback.range_fst]`. Conclude with `ht`. Take `⟨g, hg⟩` from `exists_dim_of_preconnected c.A.hom (pb.1.isoPullback.inv y)`. Establish `e₁ : n x = g` using `H1.dim_base pb.1 (hd x) hg (pb.1.isoPullback.inv y) (by`. Rewrite using `[← Scheme.Hom.comp_apply, pb.1.isoPullback_inv_fst, hy]`.

Conclude with `hW x)`. Take `⟨β, -⟩` from `exists_spMap (t ≫ s)`. Establish `hK : (M : K) ≠ 0` using `by simpa using (hu.map β).ne_zero`. Establish `e₂` using `card_torsion_abelianVariety K c.A g M c.ab hg hK`. Take `⟨i, j⟩` from `(isLevel_lvOf c).2 K (𝟙 _)`.

Establish `e₃ : Nat.card (Std h M) = Nat.card {x : 𝟙_ (Over (Sp K)) ⟶ c.A // x ^ M = 1}` using `Nat.card_congr (Equiv.ofBijective (fun a => ⟨_, (j _).2 ⟨a, rfl⟩⟩) ⟨fun a b e => i (congrArg Subtype.val e), fun y => ((j y.1).1 y.2).imp fun a e => Subtype.ext e⟩)`. Rewrite `e₃` using `[e₂, card_std (by omega)]`. Establish `e₄ : n x = h` using `by have := Nat.pow_right_injective hM e₃; omega`. Use `hd x` as an intermediate fact. Rewrite `this` using `[e₄]`. Then use the resulting hypothesis.
-/
theorem relDim {ζ : Bˣ} (hM : 2 ≤ M) (hu : IsUnit (M : B)) (o : SiegPre h M (ζ : B) s) :
    SmoothOfRelativeDimension h o.A.hom := by
  have := o.ab.smooth
  choose n W hW hd using H1.exists_dim o.A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension h) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension h) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  obtain ⟨K, _, _, t, ht⟩ := exists_geomPt (o.A.hom x)
  obtain ⟨c, φ, φ₂, pb, -⟩ := (siegPre_pullback h M B ζ S _ s _ t o rfl).1
  have := c.ab.smooth
  have := c.ab.geomConnected
  have : ConnectedSpace c.A.left := GeometricallyConnected.connectedSpace c.A.hom c.A.hom.isOpenMap
  obtain ⟨y, hy⟩ : x ∈ Set.range (pullback.fst o.A.hom t) := by
    rw [Scheme.Pullback.range_fst]
    exact ht
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected c.A.hom (pb.1.isoPullback.inv y)
  have e₁ : n x = g := H1.dim_base pb.1 (hd x) hg (pb.1.isoPullback.inv y) (by
    rw [← Scheme.Hom.comp_apply, pb.1.isoPullback_inv_fst, hy]; exact hW x)
  obtain ⟨β, -⟩ := exists_spMap (t ≫ s)
  have hK : (M : K) ≠ 0 := by simpa using (hu.map β).ne_zero
  have e₂ := card_torsion_abelianVariety K c.A g M c.ab hg hK
  obtain ⟨i, j⟩ := (isLevel_lvOf c).2 K (𝟙 _)
  have e₃ : Nat.card (Std h M) = Nat.card {x : 𝟙_ (Over (Sp K)) ⟶ c.A // x ^ M = 1} :=
    Nat.card_congr (Equiv.ofBijective (fun a => ⟨_, (j _).2 ⟨a, rfl⟩⟩) ⟨fun a b e => i (congrArg Subtype.val e),
      fun y => ((j y.1).1 y.2).imp fun a e => Subtype.ext e⟩)
  rw [e₂, card_std (by omega)] at e₃
  have e₄ : n x = h := by have := Nat.pow_right_injective hM e₃; omega
  have := hd x
  rwa [e₄] at this

/- English proof (translation)
Assemble the required witnesses or components as `⟨o.ab, relDim hM hu o, o.isLB, o.rig₁, o.rig₂, o.symm⟩`.
-/
theorem isSymmetricPair {ζ : Bˣ} (hM : 2 ≤ M) (hu : IsUnit (M : B)) (o : SiegPre h M (ζ : B) s) :
    IsSymmetricPair h o.A o.P :=
  ⟨o.ab, relDim hM hu o, o.isLB, o.rig₁, o.rig₂, o.symm⟩

/- English proof (translation)
The claim follows from `congrArg (fun q : S ⟶ Sp B => unitS q (ζ ^ n)) (Category.id_comp s)`.
-/
theorem unit_eq (ζ : Bˣ) (n : ℕ) :
    Units.map ((𝟙_ (Over S)).hom ≫ s).appTop.hom.toMonoidHom (unitOn (ζ ^ n)) = unitS s (ζ ^ n) :=
  congrArg (fun q : S ⟶ Sp B => unitS q (ζ ^ n)) (Category.id_comp s)

def ofTriple {ζ : Bˣ} (hM : M ≠ 0) (hζ : ζ ^ M = 1) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left)
    (lv : Std h M → (𝟙_ (Over S) ⟶ A)) (h₁ : IsSymmetricPair h A P) (h₂ : IsLevel A lv)
    (h₃ : IsSymplectic ζ s A P lv) : SiegPre h M (ζ : B) s :=
  haveI := h₁.1.comm
  have z₀ : lv 0 = 1 := by
    have e := h₂.1 0 0
    rw [add_zero] at e
    exact left_eq_mul.1 e
  { A := A
    ab := h₁.1
    P := P
    isLB := h₁.2.2.1
    rig₁ := h₁.2.2.2.1
    rig₂ := h₁.2.2.2.2.1
    symm := h₁.2.2.2.2.2
    lev := fun a => lv (red M a)
    lev_add := fun a b => by rw [red_add, h₂.1]
    lev_tors := fun a => by
      have e : ∀ n : ℕ, lv (n • red M a) = lv (red M a) ^ n := fun n => by
        induction n with
        | zero => rw [zero_smul, pow_zero, z₀]
        | succ n ih => rw [succ_nsmul, h₂.1, ih, pow_succ]
      rw [← e, show M • red M a = 0 by ext i <;> simp, z₀]
    geom := fun k _ _ x β z hx hz => by
      obtain ⟨i, j⟩ := h₂.2 k x
      refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
      · refine Iff.trans ?_ ((red_eq_iff (M := M) a 0).trans (by simp only [zero_add]))
        rw [red_zero, ← i.eq_iff]
        beta_reduce
        rw [z₀, MonObj.comp_one]
      · obtain ⟨a, ha⟩ := (j g).1 hg
        exact ⟨lft a, by rw [red_lft, ha]⟩
      · have w := CommPairing.weilIs_pull globalFns_holds h₁.1 (pull_isLB h₁.2.2.1 _) (toUnit (Over.mk x))
          (h₃ (red M a) (red M b))
        have e : Units.map (toUnit (Over.mk x)).left.appTop.hom.toMonoidHom
            (Units.map ((𝟙_ (Over S)).hom ≫ s).appTop.hom.toMonoidHom
              (unitOn (ζ ^ (2 * stdForm (red M a) (red M b)).val))) = unitOn (z ^ (2 * omegaStd a b)) := by
          rw [unit_eq, pow_form hM hζ, Over.toUnit_left]
          refine (map_unitS hx _).trans (congrArg unitOn ?_)
          rw [map_zpow]
          exact congrArg (· ^ (2 * omegaStd a b)) (Units.ext hz.symm)
        exact e ▸ w }

/- English proof (translation)
The claim follows from `funext fun a => congrArg lv (red_lft a)`.
-/
theorem lvOf_ofTriple {ζ : Bˣ} (hM : M ≠ 0) (hζ : ζ ^ M = 1) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left)
    (lv : Std h M → (𝟙_ (Over S) ⟶ A)) (h₁ : IsSymmetricPair h A P) (h₂ : IsLevel A lv)
    (h₃ : IsSymplectic ζ s A P lv) : lvOf (ofTriple hM hζ A P lv h₁ h₂ h₃) = lv :=
  funext fun a => congrArg lv (red_lft a)

end Objects

section Symplectic

variable {h M : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}

open WeilMul in
/- English proof (translation)
Introduce `p`. Use `hA.comm` as an intermediate fact. Establish `hG` using `globalFns_holds`. Take `⟨V, hV, a₁, a₂⟩` from `h p`. Take `⟨V', hV', b₁, b₂⟩` from `h' p`.

Take `⟨θx, θy, px, py, hc⟩` from `exists_commV_of_le hL (inf_le_left : V ⊓ V' ≤ V) a₁ a₂`. Take `⟨θx', θy', px', py', hc'⟩` from `exists_commV_of_le hL (inf_le_right : V ⊓ V' ≤ V') b₁ b₂`. Take `⟨θ, pθ, hθ⟩` from `hc.mul hL (hc'.congr hG hA hL rfl (py.trans py'.symm))`. Establish `q : θ.pt = Out.overResι (V ⊓ V') ≫ (x * x')` using `by rw [pθ, px, px', MonObj.comp_mul]`. Use `⟨V ⊓ V', ⟨hV, hV'⟩, ⟨θ, θy, q, py⟩, fun θ₁ θ₂ p₁ p₂ => ?_⟩` and prove the remaining obligations.

Conclude with `(commIs_iff hL _ _ _ _).2 (hθ.congr hG hA hL (p₁.trans q.symm) (p₂.trans py.symm))`.
-/
theorem weilIs_mul {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S}
    {x x' y : T ⟶ A} {c c' : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs A L k x y c) (h' : Out.WeilIs A L k x' y c') :
    Out.WeilIs A L k (x * x') y (c * c') := by
  intro p
  have := hA.comm
  have hG := globalFns_holds
  obtain ⟨V, hV, a₁, a₂⟩ := h p
  obtain ⟨V', hV', b₁, b₂⟩ := h' p
  obtain ⟨θx, θy, px, py, hc⟩ := exists_commV_of_le hL (inf_le_left : V ⊓ V' ≤ V) a₁ a₂
  obtain ⟨θx', θy', px', py', hc'⟩ := exists_commV_of_le hL (inf_le_right : V ⊓ V' ≤ V') b₁ b₂
  obtain ⟨θ, pθ, hθ⟩ := hc.mul hL (hc'.congr hG hA hL rfl (py.trans py'.symm))
  have q : θ.pt = Out.overResι (V ⊓ V') ≫ (x * x') := by rw [pθ, px, px', MonObj.comp_mul]
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ⟨θ, θy, q, py⟩, fun θ₁ θ₂ p₁ p₂ => ?_⟩
  exact (commIs_iff hL _ _ _ _).2 (hθ.congr hG hA hL (p₁.trans q.symm) (p₂.trans py.symm))

/- English proof (translation)
Establish `hpow : ∀ j : ℕ, Out.WeilIs A L k (x ^ (j + 1)) y (c ^ (j + 1))`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => rwa [zero_add, pow_one, pow_one]`. Consider the case `succ j ih => rw [pow_succ, pow_succ c]`.

Conclude with `weilIs_mul hA hL ih hc`. Establish `h` using `hpow n`. Rewrite `h` using `[pow_succ, hx, _root_.one_mul]`. Use `CommutatorPairing.weilIs_unique globalFns_holds hA hL h hc` as an intermediate fact. Rewrite `this` using `[pow_succ, mul_eq_right]`. Then use the resulting hypothesis.
-/
theorem weil_pow_eq_one {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {k : ℤ}
    {T : Over S} {x y : T ⟶ A} {n : ℕ} (hx : x ^ n = 1) {c : Γ(T.left, ⊤)ˣ} (hc : Out.WeilIs A L k x y c) :
    c ^ n = 1 := by
  have hpow : ∀ j : ℕ, Out.WeilIs A L k (x ^ (j + 1)) y (c ^ (j + 1)) := by
    intro j
    induction j with
    | zero => rwa [zero_add, pow_one, pow_one]
    | succ j ih => rw [pow_succ, pow_succ c]; exact weilIs_mul hA hL ih hc
  have h := hpow n
  rw [pow_succ, hx, _root_.one_mul] at h
  have := CommutatorPairing.weilIs_unique globalFns_holds hA hL h hc
  rwa [pow_succ, mul_eq_right] at this

def TranslFixed {ζ : B} (o : SiegPre h M ζ s) : Prop :=
  ∀ a, (M : ℤ) • cls o.diag (pull_isLB o.isLB _) =
    (M : ℤ) • pull ((toUnit o.A ≫ o.lev a) * 𝟙 o.A).left (cls o.diag (pull_isLB o.isLB _))

/- English proof (translation)
Introduce `a`. Establish `hb` using `isSymBilin globalFns_holds o ha`. Establish `d : ∀ f : o.A ⟶ o.A, pull f.left (cls o.diag (pull_isLB o.isLB _)) = pairCls (cls o.P o.isLB) f f` using `fun f => (pull_pairCls (cls o.P o.isLB) f (𝟙 _) (𝟙 _)).trans (by rw [Category.comp_id])`. Establish `z : ∀ y : o.A ⟶ o.A, (M : ℤ) • pairCls (cls o.P o.isLB) (toUnit o.A ≫ o.lev a) y = 0` using `fun y => by`. Establish `e` using `BilinCalc.map_prod_zpow (fun z => pairCls (cls o.P o.isLB) z y) (fun a b => hb.mul _ a b y) (fun _ : Fin 1 => toUnit o.A ≫ o.lev a) fun _ => (M : ℤ)`.

Simplify using `only [Finset.univ_unique, Finset.prod_const, Finset.card_singleton, pow_one, Finset.sum_const, one_smul, zpow_natCast] at e`. Rewrite using `[← e, ← MonObj.comp_pow, o.lev_tors, MonObj.comp_one]`. Conclude with `one_left (hb.mul _) y`. Rewrite using `[d, hb.mul, hb.symm _ (𝟙 o.A) (_ * _), hb.mul, smul_add, smul_add, z, z, zero_add, zero_add]`. Both sides reduce to the same expression.
-/
theorem translFixed_of_ample {ζ : B} (o : SiegPre h M ζ s) (ha : Out.RelAmple o.A o.diag) : TranslFixed o := by
  intro a
  have hb := isSymBilin globalFns_holds o ha
  have d : ∀ f : o.A ⟶ o.A, pull f.left (cls o.diag (pull_isLB o.isLB _)) = pairCls (cls o.P o.isLB) f f := fun f =>
    (pull_pairCls (cls o.P o.isLB) f (𝟙 _) (𝟙 _)).trans (by rw [Category.comp_id])
  have z : ∀ y : o.A ⟶ o.A, (M : ℤ) • pairCls (cls o.P o.isLB) (toUnit o.A ≫ o.lev a) y = 0 := fun y => by
    have e := BilinCalc.map_prod_zpow (fun z => pairCls (cls o.P o.isLB) z y) (fun a b => hb.mul _ a b y)
      (fun _ : Fin 1 => toUnit o.A ≫ o.lev a) fun _ => (M : ℤ)
    simp only [Finset.univ_unique, Finset.prod_const, Finset.card_singleton, pow_one, Finset.sum_const, one_smul,
      zpow_natCast] at e
    rw [← e, ← MonObj.comp_pow, o.lev_tors, MonObj.comp_one]
    exact one_left (hb.mul _) y
  rw [d, hb.mul, hb.symm _ (𝟙 o.A) (_ * _), hb.mul, smul_add, smul_add, z, z, zero_add, zero_add]
  rfl

/- English proof (translation)
Introduce `a`. Take `⟨φ, φ₂, hφ, sq, iso, hl⟩` from `pb`. Establish `hD : o.diag.IsLB` using `pull_isLB o.isLB _`. Establish `hD' : o'.diag.IsLB` using `pull_isLB o'.isLB _`. Establish `hd : cls o'.diag hD' = pull φ (cls o.diag hD)` using `(cls_eq_iff hD' (pull_isLB hD φ)).2 (diag_iso sq iso)`.

Set `N` to `LB.LinComb o.diag (K := Fin 2) ![𝟙 _, ((toUnit o.A ≫ o.lev a) * 𝟙 o.A).left] ![M, -M]`. Establish `hN : N.IsLB` using `LB.isLB_linComb hD _ _`. Establish `cN : cls N hN = (M : ℤ) • cls o.diag hD - (M : ℤ) • pull ((toUnit o.A ≫ o.lev a) * 𝟙 o.A).left (cls o.diag hD)`. Rewrite using `[cls_linComb hD, Fin.sum_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, pull_id, sub_eq_add_neg]`.

Establish `e : ((toUnit o'.A ≫ o'.lev a) * 𝟙 o'.A).left ≫ φ = φ ≫ ((toUnit o.A ≫ o.lev a) * 𝟙 o.A).left`. Set `U : Over.mk (o'.A.hom ≫ spMap (algebraMap O K)) ⟶ o.A` to `Over.homMk φ hφ.1.w`. Use `(hφ.2 o'.A _ _ (U ≫ toUnit o.A ≫ o.lev a) (U ≫ 𝟙 _) ?_ ?_).symm.trans ?_` and prove the remaining obligations. Simplify using `only [Over.comp_left, Over.toUnit_left, Category.assoc]`. Rewrite using `[hl a]`.

Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hφ.1.w).trans (Category.assoc _ _ _))`. Conclude with `(Category.comp_id _).trans (Category.id_comp _).symm`. Rewrite using `[← MonObj.comp_mul]`. Both sides reduce to the same expression. Use `o.ab.smooth` as an intermediate fact.

Use `o.ab.proper` as an intermediate fact. Establish `t` using `ValGenExtend.triv_of_triv_generic O K _ _ o.A.hom φ o'.A.hom hφ.1 o.ab.smooth inferInstance (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ o.ab.smooth o.ab.geomConnected) N hN ((cls_eq_zero_iff (pull_isLB hN φ)).1 (by`. Rewrite using `[cls_pull hN, cN, map_sub, map_zsmul, map_zsmul, ← pull_comp, ← e, pull_comp, ← hd]`. Conclude with `sub_eq_zero.2 (H a)))`. Conclude with `sub_eq_zero.1 (cN.symm.trans ((cls_eq_zero_iff hN).2 t))`.
-/
theorem translFixed_of_generic (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O]
    [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] {s : Sp O ⟶ Sp B} {s' : Sp K ⟶ Sp B'} {ζ : B} {ζ' : B'}
    (o : SiegPre h M ζ s) (o' : SiegPre h M ζ' s') (pb : SiegPB o' o (spMap (algebraMap O K)))
    (H : TranslFixed o') : TranslFixed o := by
  intro a
  obtain ⟨φ, φ₂, hφ, sq, iso, hl⟩ := pb
  have hD : o.diag.IsLB := pull_isLB o.isLB _
  have hD' : o'.diag.IsLB := pull_isLB o'.isLB _
  have hd : cls o'.diag hD' = pull φ (cls o.diag hD) := (cls_eq_iff hD' (pull_isLB hD φ)).2 (diag_iso sq iso)
  let N := LB.LinComb o.diag (K := Fin 2) ![𝟙 _, ((toUnit o.A ≫ o.lev a) * 𝟙 o.A).left] ![M, -M]
  have hN : N.IsLB := LB.isLB_linComb hD _ _
  have cN : cls N hN = (M : ℤ) • cls o.diag hD -
      (M : ℤ) • pull ((toUnit o.A ≫ o.lev a) * 𝟙 o.A).left (cls o.diag hD) := by
    rw [cls_linComb hD, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, pull_id, sub_eq_add_neg]
  have e : ((toUnit o'.A ≫ o'.lev a) * 𝟙 o'.A).left ≫ φ = φ ≫ ((toUnit o.A ≫ o.lev a) * 𝟙 o.A).left := by
    let U : Over.mk (o'.A.hom ≫ spMap (algebraMap O K)) ⟶ o.A := Over.homMk φ hφ.1.w
    refine (hφ.2 o'.A _ _ (U ≫ toUnit o.A ≫ o.lev a) (U ≫ 𝟙 _) ?_ ?_).symm.trans ?_
    · simp only [Over.comp_left, Over.toUnit_left, Category.assoc]
      rw [hl a]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hφ.1.w).trans (Category.assoc _ _ _))
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · rw [← MonObj.comp_mul]
      rfl
  have := o.ab.smooth
  have := o.ab.proper
  have t := ValGenExtend.triv_of_triv_generic O K _ _ o.A.hom φ o'.A.hom hφ.1 o.ab.smooth inferInstance
    (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ o.ab.smooth o.ab.geomConnected) N hN
    ((cls_eq_zero_iff (pull_isLB hN φ)).1 (by
      rw [cls_pull hN, cN, map_sub, map_zsmul, map_zsmul, ← pull_comp, ← e, pull_comp, ← hd]
      exact sub_eq_zero.2 (H a)))
  exact sub_eq_zero.1 (cN.symm.trans ((cls_eq_zero_iff hN).2 t))

/- English proof (translation)
Establish `hD : o.diag.IsLB` using `pull_isLB o.isLB _`. Establish `th : ∀ a (p : (𝟙_ (Over S)).left), ∃ V : (𝟙_ (Over S)).left.Opens, p ∈ V ∧ ∃ θ : Out.ThetaGrp o.A o.diag M (Out.overRes V), θ.pt = Out.overResι V ≫ o.lev a` using `fun a p => by`. Set `T` to `Out.overRes (T := 𝟙_ (Over S)) ⊤`. Establish `hT : (Out.thetaLB o.A o.diag M (Out.overResι ⊤ ≫ o.lev a)).IsLB` using `LB.isLB_linComb hD _ _`. Take `⟨t, ht⟩` from `(cls_eq_zero_iff hT).1 (by`.

Unfold `Out.thetaLB at hT ⊢`. Rewrite using `[cls_linComb hD, Fin.sum_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul]`. Establish `e : Out.translPt o.A (Out.overResι ⊤ ≫ o.lev a) = snd T o.A ≫ ((toUnit o.A ≫ o.lev a) * 𝟙 o.A)`. Rewrite using `[MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.translPt, ← Hom.mul_def, ← Category.assoc, toUnit_unique (fst _ _ ≫ _) (toUnit _)]`.

Rewrite using `[e, Over.comp_left, pull_comp, ← map_zsmul, ← map_zsmul, ← H a, add_neg_cancel])`. Conclude with `⟨⊤, trivial, ⟨_, t, ht⟩, rfl⟩`. Introduce `a b`. Take `⟨c, hc⟩` from `CommutatorPairing.exists_weilIs globalFns_holds o.ab hD (th (lft a)) (th (lft b))`. Establish `p₀ : c ^ M = 1` using `weil_pow_eq_one o.ab hD (o.lev_tors _) hc`.

Establish `hn : IsUnit (M : Γ(S, ⊤))`. Use `(hu.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom).map s.appTop.hom` as an intermediate fact. Rewrite `this` using `[map_natCast, map_natCast]`. Then use the resulting hypothesis. Establish `e : c = unitS s (ζ ^ (2 * stdForm a b).val)` using `eq_of_geometric (X := S) hn p₀ (by`. Rewrite using `[unitS, unitOn, ← map_pow, ← map_pow, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, map_one, map_one])`.

Use `fun K _ _ x => by`. Take `⟨β, hβ⟩` from `exists_spMap (x ≫ s)`. Take `⟨-, -, g₃⟩` from `o.geom K x β (Units.map β.toMonoidHom ζ) hβ rfl`. Establish `w` using `CommPairing.weilIs_pull globalFns_holds o.ab hD (toUnit (Over.mk x)) hc`. Establish `q` using `CommutatorPairing.weilIs_unique globalFns_holds o.ab hD w (g₃ _ _)`.

Rewrite `q` using `[Over.toUnit_left]`. Use `q.trans ?_` and prove the remaining obligations. Rewrite using `[map_unitS hβ, ← map_zpow, ← pow_form hM hζ, red_lft, red_lft]`. Rewrite using `[unit_eq, ← e]`. Conclude with `hc`.
-/
theorem isSymplectic_of_translFixed {ζ : Bˣ} (hM : M ≠ 0) (hζ : ζ ^ M = 1) (hu : IsUnit (M : B))
    (o : SiegPre h M (ζ : B) s) (H : TranslFixed o) : IsSymplectic ζ s o.A o.P (lvOf o) := by
  have hD : o.diag.IsLB := pull_isLB o.isLB _
  have th : ∀ a (p : (𝟙_ (Over S)).left), ∃ V : (𝟙_ (Over S)).left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp o.A o.diag M (Out.overRes V), θ.pt = Out.overResι V ≫ o.lev a := fun a p => by
    let T := Out.overRes (T := 𝟙_ (Over S)) ⊤
    have hT : (Out.thetaLB o.A o.diag M (Out.overResι ⊤ ≫ o.lev a)).IsLB := LB.isLB_linComb hD _ _
    obtain ⟨t, ht⟩ := (cls_eq_zero_iff hT).1 (by
      unfold Out.thetaLB at hT ⊢
      rw [cls_linComb hD, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul]
      have e : Out.translPt o.A (Out.overResι ⊤ ≫ o.lev a) = snd T o.A ≫ ((toUnit o.A ≫ o.lev a) * 𝟙 o.A) := by
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.translPt, ← Hom.mul_def, ← Category.assoc,
          toUnit_unique (fst _ _ ≫ _) (toUnit _)]
      rw [e, Over.comp_left, pull_comp, ← map_zsmul, ← map_zsmul, ← H a, add_neg_cancel])
    exact ⟨⊤, trivial, ⟨_, t, ht⟩, rfl⟩
  intro a b
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_weilIs globalFns_holds o.ab hD (th (lft a)) (th (lft b))
  have p₀ : c ^ M = 1 := weil_pow_eq_one o.ab hD (o.lev_tors _) hc
  have hn : IsUnit (M : Γ(S, ⊤)) := by
    have := (hu.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom).map s.appTop.hom
    rwa [map_natCast, map_natCast] at this
  have e : c = unitS s (ζ ^ (2 * stdForm a b).val) := eq_of_geometric (X := S) hn p₀ (by
    rw [unitS, unitOn, ← map_pow, ← map_pow, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, map_one, map_one])
    fun K _ _ x => by
      obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
      obtain ⟨-, -, g₃⟩ := o.geom K x β (Units.map β.toMonoidHom ζ) hβ rfl
      have w := CommPairing.weilIs_pull globalFns_holds o.ab hD (toUnit (Over.mk x)) hc
      have q := CommutatorPairing.weilIs_unique globalFns_holds o.ab hD w (g₃ _ _)
      rw [Over.toUnit_left] at q
      refine q.trans ?_
      rw [map_unitS hβ, ← map_zpow, ← pow_form hM hζ, red_lft, red_lft]
  rw [unit_eq, ← e]
  exact hc

end Symplectic

section Along

variable {h M : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
  {ζ : B} {ζ' : B'}

/- English proof (translation)
Use `⟨h₁.1.lift φ₂ A₂.hom h₂.1.w, h₁.1.lift_fst _ _ _, h₁.cancel ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[h₁.1.lift_fst, Category.id_comp]`. Conclude with `h₂`. Rewrite using `[h₁.1.lift_snd, Category.comp_id]`.
-/
theorem isGrpPullback_of_comp_eq {A : Over S} {A₁ A₂ : Over S'} [GrpObj A] [GrpObj A₁] [GrpObj A₂] {f : S' ⟶ S}
    {φ₁ : A₁.left ⟶ A.left} {φ₂ : A₂.left ⟶ A.left} (h₁ : IsGrpPullback A₁ A f φ₁) (h₂ : IsGrpPullback A₂ A f φ₂) :
    ∃ e : A₂.left ⟶ A₁.left, e ≫ φ₁ = φ₂ ∧ IsGrpPullback A₂ A₁ (𝟙 S') e := by
  refine ⟨h₁.1.lift φ₂ A₂.hom h₂.1.w, h₁.1.lift_fst _ _ _, h₁.cancel ?_ ?_⟩
  · rw [h₁.1.lift_fst, Category.id_comp]
    exact h₂
  · rw [h₁.1.lift_snd, Category.comp_id]

/- English proof (translation)
Take `⟨φ, φ₂, hφ, sq, iso, -⟩` from `pb`. Establish `hD : o.diag.IsLB` using `pull_isLB o.isLB _`. Establish `hD' : o'.diag.IsLB` using `pull_isLB o'.isLB _`. Establish `hd : cls o'.diag hD' = pull φ (cls o.diag hD)` using `(cls_eq_iff hD' (pull_isLB hD φ)).2 (diag_iso sq iso)`. Establish `hψ` using `isGrpPullback_pullback o.A t`.

Establish `hE` using `pull_isLB hD (pullback.fst o.A.hom t)`. Prove the components needed by the constructor for the conclusion. Take `⟨e, he, H⟩` from `isGrpPullback_of_comp_eq hφ hψ`. Conclude with `(pol_pull _ _ _ _ _ e _ _ hD' hE o'.ab H ((cls_eq_iff hE (pull_isLB hD' e)).1 (by`. Rewrite using `[cls_pull hD, cls_pull hD', hd, ← pull_comp, he]))).2.1`.

Take `⟨e, he, H⟩` from `isGrpPullback_of_comp_eq hψ hφ`. Conclude with `(pol_pull _ _ _ _ _ e _ _ hE hD' (pol_pull _ _ _ _ _ _ _ _ hD hE o.ab hψ (Pdiv.PullbackComparison.gen_refl _ hE)).1 H ((cls_eq_iff hD' (pull_isLB hE e)).1 (by rw [cls_pull hE, cls_pull hD, hd, ← pull_comp, he]))).2.1`.
-/
theorem ample_iff_along {o' : SiegPre h M ζ' s'} {o : SiegPre h M ζ s} {t : S' ⟶ S} (pb : SiegPB o' o t) :
    Out.RelAmple o'.A o'.diag ↔ DiagAmpleAlong o.A o.P t := by
  obtain ⟨φ, φ₂, hφ, sq, iso, -⟩ := pb
  have hD : o.diag.IsLB := pull_isLB o.isLB _
  have hD' : o'.diag.IsLB := pull_isLB o'.isLB _
  have hd : cls o'.diag hD' = pull φ (cls o.diag hD) := (cls_eq_iff hD' (pull_isLB hD φ)).2 (diag_iso sq iso)
  have hψ := isGrpPullback_pullback o.A t
  have hE := pull_isLB hD (pullback.fst o.A.hom t)
  constructor
  · obtain ⟨e, he, H⟩ := isGrpPullback_of_comp_eq hφ hψ
    exact (pol_pull _ _ _ _ _ e _ _ hD' hE o'.ab H ((cls_eq_iff hE (pull_isLB hD' e)).1 (by
      rw [cls_pull hD, cls_pull hD', hd, ← pull_comp, he]))).2.1
  · obtain ⟨e, he, H⟩ := isGrpPullback_of_comp_eq hψ hφ
    exact (pol_pull _ _ _ _ _ e _ _ hE hD'
      (pol_pull _ _ _ _ _ _ _ _ hD hE o.ab hψ (Pdiv.PullbackComparison.gen_refl _ hE)).1 H
      ((cls_eq_iff hD' (pull_isLB hE e)).1 (by rw [cls_pull hE, cls_pull hD, hd, ← pull_comp, he]))).2.1

/- English proof (translation)
Use `(principal_iff o').trans (and_congr (ample_iff_along pb) ?_)` and prove the remaining obligations. Take `⟨φ, φ₂, hφ, sq, iso, -⟩` from `pb`. Establish `hP : cls o'.P o'.isLB = pull φ₂ (cls o.P o.isLB)` using `(cls_eq_iff _ (pull_isLB o.isLB _)).2 iso`. Establish `key : ∀ (T : Over S') (x : T ⟶ o'.A), IsTrivial (slice o'.A o'.P x) ↔ IsTrivial (slice o.A o.P (pushHom hφ T x))` using `fun T x => by`. Use `(cls_eq_zero_iff (pull_isLB o'.isLB _)).symm.trans (Iff.trans ?_ (cls_eq_zero_iff (pull_isLB o.isLB _)))` and prove the remaining obligations.

Rewrite using `[cls_pull o'.isLB, cls_pull o.isLB, hP, ← pull_comp]`. Set `T₀ : Over S` to `Over.mk (T.hom ≫ t)`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Establish `w₁ : (snd T₀ o.A).left ≫ o.A.hom = ((fst T₀ o.A).left ≫ T.hom) ≫ t` using `pullback.condition.symm.trans (Category.assoc _ _ _).symm`.

Set `a : (T₀ ⊗ o.A).left ⟶ o'.A.left` to `hφ.1.lift _ _ w₁`. Establish `a₁ : a ≫ φ = (snd T₀ o.A).left` using `hφ.1.lift_fst _ _ _`. Establish `a₂ : a ≫ o'.A.hom = (fst T₀ o.A).left ≫ T.hom` using `hφ.1.lift_snd _ _ _`. Set `χ : (T₀ ⊗ o.A).left ⟶ (T ⊗ o'.A).left` to `pullback.lift (fst T₀ o.A).left a a₂.symm`. Establish `c₁ : χ ≫ (fst T o'.A).left = (fst T₀ o.A).left` using `pullback.lift_fst _ _ _`.

Establish `c₂ : χ ≫ (snd T o'.A).left = a` using `pullback.lift_snd _ _ _`. Use `congrArg (pull χ) e` as an intermediate fact. Rewrite `this` using `[map_zero, ← pull_comp, lift_sq sq (T := T₀ ⊗ o.A) χ _ _ (𝟙 _) (fst T₀ o.A ≫ pushHom hφ T x) (snd T₀ o.A) (by rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₁, Category.id_comp]; rfl) (by rw [← Category.assoc, c₂, a₁, Category.id_comp]), Category.id_comp]`. Conclude with `this`. Introduce `e`.

Set `χ : (T ⊗ o'.A).left ⟶ (T₀ ⊗ o.A).left` to `pullback.lift (fst T o'.A).left ((snd T o'.A).left ≫ φ) (by`. Rewrite using `[Category.assoc, hφ.1.w, ← Category.assoc, Over.w (snd T o'.A), ← Over.w (fst T o'.A), Category.assoc]`. Use the proof step `rfl)`. Establish `c₁ : χ ≫ (fst T₀ o.A).left = (fst T o'.A).left` using `pullback.lift_fst _ _ _`. Establish `c₂ : χ ≫ (snd T₀ o.A).left = (snd T o'.A).left ≫ φ` using `pullback.lift_snd _ _ _`.

Use `congrArg (pull χ) e` as an intermediate fact. Rewrite `this` using `[map_zero, ← pull_comp, ← lift_sq sq (T := Over.mk ((T ⊗ o'.A).hom ≫ t)) (𝟙 _) (fst T o'.A ≫ x) (snd T o'.A) χ _ _ (by rw [Over.comp_left, Over.comp_left, ← Category.assoc χ, c₁]; exact (Category.id_comp _).trans (Category.assoc _ _ _)) ((Category.id_comp _).trans c₂.symm)]`. Conclude with `(congrArg (fun q => pull q _) (Category.id_comp _)).symm.trans this`. Prove the components needed by the constructor for the conclusion. Introduce `H T τ x hx`.

Take `⟨x', rfl⟩` from `push_surjective hφ (Over.mk τ) x`. Rewrite using `[H _ x' ((key _ x').2 hx)]`. Conclude with `map_one _`. Introduce `H T x hx`. Conclude with `push_injective hφ T ((H T.left T.hom _ ((key T x).1 hx)).trans (map_one _).symm)`.
-/
theorem principal_iff_along {o' : SiegPre h M ζ' s'} {o : SiegPre h M ζ s} {t : S' ⟶ S} (pb : SiegPB o' o t) :
    o'.Principal ↔ IsPrincipalAlong o.A o.P t := by
  refine (principal_iff o').trans (and_congr (ample_iff_along pb) ?_)
  obtain ⟨φ, φ₂, hφ, sq, iso, -⟩ := pb
  have hP : cls o'.P o'.isLB = pull φ₂ (cls o.P o.isLB) := (cls_eq_iff _ (pull_isLB o.isLB _)).2 iso
  have key : ∀ (T : Over S') (x : T ⟶ o'.A),
      IsTrivial (slice o'.A o'.P x) ↔ IsTrivial (slice o.A o.P (pushHom hφ T x)) := fun T x => by
    refine (cls_eq_zero_iff (pull_isLB o'.isLB _)).symm.trans (Iff.trans ?_ (cls_eq_zero_iff (pull_isLB o.isLB _)))
    rw [cls_pull o'.isLB, cls_pull o.isLB, hP, ← pull_comp]
    let T₀ : Over S := Over.mk (T.hom ≫ t)
    constructor
    · intro e
      have w₁ : (snd T₀ o.A).left ≫ o.A.hom = ((fst T₀ o.A).left ≫ T.hom) ≫ t :=
        pullback.condition.symm.trans (Category.assoc _ _ _).symm
      let a : (T₀ ⊗ o.A).left ⟶ o'.A.left := hφ.1.lift _ _ w₁
      have a₁ : a ≫ φ = (snd T₀ o.A).left := hφ.1.lift_fst _ _ _
      have a₂ : a ≫ o'.A.hom = (fst T₀ o.A).left ≫ T.hom := hφ.1.lift_snd _ _ _
      let χ : (T₀ ⊗ o.A).left ⟶ (T ⊗ o'.A).left := pullback.lift (fst T₀ o.A).left a a₂.symm
      have c₁ : χ ≫ (fst T o'.A).left = (fst T₀ o.A).left := pullback.lift_fst _ _ _
      have c₂ : χ ≫ (snd T o'.A).left = a := pullback.lift_snd _ _ _
      have := congrArg (pull χ) e
      rw [map_zero, ← pull_comp, lift_sq sq (T := T₀ ⊗ o.A) χ _ _ (𝟙 _) (fst T₀ o.A ≫ pushHom hφ T x) (snd T₀ o.A)
        (by rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₁, Category.id_comp]; rfl)
        (by rw [← Category.assoc, c₂, a₁, Category.id_comp]), Category.id_comp] at this
      exact this
    · intro e
      let χ : (T ⊗ o'.A).left ⟶ (T₀ ⊗ o.A).left := pullback.lift (fst T o'.A).left ((snd T o'.A).left ≫ φ) (by
        rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w (snd T o'.A), ← Over.w (fst T o'.A), Category.assoc]
        rfl)
      have c₁ : χ ≫ (fst T₀ o.A).left = (fst T o'.A).left := pullback.lift_fst _ _ _
      have c₂ : χ ≫ (snd T₀ o.A).left = (snd T o'.A).left ≫ φ := pullback.lift_snd _ _ _
      have := congrArg (pull χ) e
      rw [map_zero, ← pull_comp, ← lift_sq sq (T := Over.mk ((T ⊗ o'.A).hom ≫ t)) (𝟙 _) (fst T o'.A ≫ x) (snd T o'.A) χ
        _ _ (by rw [Over.comp_left, Over.comp_left, ← Category.assoc χ, c₁]; exact (Category.id_comp _).trans (Category.assoc _ _ _))
        ((Category.id_comp _).trans c₂.symm)] at this
      exact (congrArg (fun q => pull q _) (Category.id_comp _)).symm.trans this
  constructor
  · intro H T τ x hx
    obtain ⟨x', rfl⟩ := push_surjective hφ (Over.mk τ) x
    rw [H _ x' ((key _ x').2 hx)]
    exact map_one _
  · intro H T x hx
    exact push_injective hφ T ((H T.left T.hom _ ((key T x).1 hx)).trans (map_one _).symm)

def ofPullback (o : SiegPre h M ζ s) (f : S' ⟶ S) (A : Over S') [GrpObj A] (P : LB (A ⊗ A).left)
    (lv : Std h M → (𝟙_ (Over S') ⟶ A)) (hP : P.IsLB) (H : IsPullbackTriple A P lv o.A o.P (lvOf o) f) :
    SiegPre h M ζ (f ≫ s) :=
  have main : IsAbelianScheme A ∧ IsTrivial (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) ∧
      IsTrivial (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧
      (∀ a b, lv (red M (a + b)) = lv (red M a) * lv (red M b)) ∧ (∀ a, lv (red M a) ^ M = 1) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') (β : B →+* k) (z : kˣ), x ≫ f ≫ s = spMap β →
        (z : k) = β ζ → (∀ a, (toUnit (Over.mk x) ≫ lv (red M a) = 1 ↔ ∃ b, a = M • b)) ∧
        (∀ g : Over.mk x ⟶ A, g ^ M = 1 → ∃ a, toUnit _ ≫ lv (red M a) = g) ∧
        ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) M (toUnit (Over.mk x) ≫ lv (red M a))
          (toUnit _ ≫ lv (red M b)) (unitOn (z ^ (2 * omegaStd a b))) := by
    obtain ⟨φ, φ₂, pb, s₁, s₂, iso, hl⟩ := H
    have sq : IsSquare φ φ₂ := ⟨s₁, s₂⟩
    have hD : o.diag.IsLB := pull_isLB o.isLB _
    have hc : cls P hP = pull φ₂ (cls o.P o.isLB) := (cls_eq_iff _ (pull_isLB o.isLB _)).2 iso
    have l : ∀ a, lv (red M a) = SiegelPull.secPull pb (o.lev a) := fun a => Over.OverMorphism.ext
      (pb.1.hom_ext (by rw [hl, lvOf_red, secPull_left]) (by rw [Over.w, Over.w]))
    let U : Over.mk (A.hom ≫ f) ⟶ o.A := Over.homMk φ pb.1.w
    have o₁ : (1 : A ⟶ A).left ≫ φ = φ ≫ (1 : o.A ⟶ o.A).left :=
      congrArg (fun q => q.left) ((map_one (pushHom pb A)).trans (MonObj.comp_one U).symm)
    have ax : ∀ (x y : A ⟶ A) (x₀ y₀ : o.A ⟶ o.A), x.left ≫ φ = φ ≫ x₀.left → y.left ≫ φ = φ ≫ y₀.left →
        IsTrivial (o.P.pull (lift x₀ y₀).left) → IsTrivial (P.pull (lift x y).left) := fun x y x₀ y₀ hx hy H => by
      refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
      have e : (lift x y).left ≫ φ₂ = φ ≫ (lift x₀ y₀).left := (Category.id_comp _).symm.trans
        (lift_sq sq (T := Over.mk (A.hom ≫ f)) (𝟙 A.left) x y φ x₀ y₀ ((Category.id_comp _).trans hx)
          ((Category.id_comp _).trans hy))
      rw [cls_pull hP, hc, ← pull_comp, e, pull_comp, ← cls_pull o.isLB _ (pull_isLB o.isLB _),
        (cls_eq_zero_iff _).2 H, map_zero]
    refine ⟨(pol_pull _ _ _ _ f φ _ _ hD (pull_isLB hP _) o.ab pb (diag_iso sq iso)).1,
      ax _ _ _ _ o₁ (by simp) o.rig₁, ax _ _ _ _ (by simp) o₁ o.rig₂, ?_, fun a b => ?_, fun a => ?_,
      fun k _ _ x β z hx hz => ?_⟩
    · refine (cls_eq_iff hP (pull_isLB hP _)).1 ?_
      have e : (lift (snd A A) (fst A A)).left ≫ φ₂ = φ₂ ≫ (lift (snd o.A o.A) (fst o.A o.A)).left :=
        (Category.id_comp _).symm.trans (lift_sq sq (T := Over.mk ((A ⊗ A).hom ≫ f)) (𝟙 (A ⊗ A).left) _ _ φ₂ _ _
          ((Category.id_comp _).trans s₂.symm) ((Category.id_comp _).trans s₁.symm))
      rw [cls_pull hP, hc, ← pull_comp, e, pull_comp]
      exact congrArg (pull φ₂) ((cls_eq_iff o.isLB (pull_isLB o.isLB _)).2 o.symm)
    · rw [l, l, l]
      exact push_injective pb _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', o.lev_add, MonObj.comp_mul])
    · rw [l]
      exact push_injective pb _ (by
        rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, o.lev_tors, MonObj.comp_one])
    · simp only [l]
      obtain ⟨g₁, g₂, g₃⟩ := o.geom k (x ≫ f) β z (by rw [Category.assoc, hx]) hz
      refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
      · rw [← (push_injective pb (Over.mk x)).eq_iff, push_secPull, map_one]
        rfl
      · obtain ⟨a, ha⟩ := g₂ (pushHom pb (Over.mk x) g) (by
          have := congrArg (pushHom pb (Over.mk x)) hg
          rw [map_pow, map_one] at this
          exact this)
        exact ⟨a, push_injective pb _ ((push_secPull pb _ _).trans ha)⟩
      · exact (weilIs_grpPullback_of_comm S S' o.A A f φ _ _ hD (pull_isLB hP _) pb
          (diag_iso sq iso) (Over.mk x) M _ _ _ _ _
          (congrArg (fun q => q.left) (push_secPull pb (o.lev a) (Over.mk x)).symm)
          (congrArg (fun q => q.left) (push_secPull pb (o.lev b) (Over.mk x)).symm)).2 (g₃ a b)
  haveI := main.1.comm
  { A := A
    ab := main.1
    P := P
    isLB := hP
    rig₁ := main.2.1
    rig₂ := main.2.2.1
    symm := main.2.2.2.1
    lev := fun a => lv (red M a)
    lev_add := main.2.2.2.2.1
    lev_tors := main.2.2.2.2.2.1
    geom := main.2.2.2.2.2.2 }

/- English proof (translation)
The claim follows from `funext fun a => congrArg lv (red_lft a)`.
-/
theorem lvOf_ofPullback (o : SiegPre h M ζ s) (f : S' ⟶ S) (A : Over S') [GrpObj A] (P : LB (A ⊗ A).left)
    (lv : Std h M → (𝟙_ (Over S') ⟶ A)) (hP : P.IsLB) (H : IsPullbackTriple A P lv o.A o.P (lvOf o) f) :
    lvOf (ofPullback o f A P lv hP H) = lv :=
  funext fun a => congrArg lv (red_lft a)

end Along

section Clauses

variable {h M : ℕ} (p : ℕ) {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B}

def PointsObj {ζ : B} (u : SiegPre h M ζ s) : Prop :=
  ∀ (C O : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
    [CommRing O] [IsLocalRing O] [Algebra O C], IsUnitBall O C → ‖(p : C)‖ < 1 →
    ∀ (β : B →+* O) (o : SiegPre h M ζ (spMap β)),
      (∃ o' : SiegPre h M ζ (spMap (algebraMap O C) ≫ spMap β), SiegPB o' o (spMap (algebraMap O C)) ∧ o'.Principal) →
      Out.RelAmple (Over.mk (pullback.snd o.A.hom (spMap (IsLocalRing.residue O))))
        (o.diag.pull (pullback.fst o.A.hom (spMap (IsLocalRing.residue O)))) →
      ∃ x : Sp O ⟶ X, x ≫ s = spMap β ∧ SiegPB o u x

def PointsTriple (ζ : Bˣ) (s : X ⟶ Sp B) (A : Over X) [GrpObj A] (P : LB (A ⊗ A).left)
    (lv : Std h M → (𝟙_ (Over X) ⟶ A)) : Prop :=
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(p : C)‖ < 1 →
    ∀ (β : B →+* intRing C) (G : Over (Sp (intRing C))) [GrpObj G] (P' : LB (G ⊗ G).left)
      (lv' : Std h M → (𝟙_ (Over (Sp (intRing C))) ⟶ G)),
      IsSymmetricPair h G P' → IsLevel G lv' → IsSymplectic ζ (spMap β) G P' lv' →
      IsPrincipalAlong G P' (spMap (intRing C).subtype) →
      DiagAmpleAlong G P' (spMap (IsLocalRing.residue (intRing C))) →
      ∃ y : Sp (intRing C) ⟶ X, y ≫ s = spMap β ∧ IsPullbackTriple G P' lv' A P lv y

def UnramObj {ζ : B} (u : SiegPre h M ζ s) : Prop :=
  ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ X) (o : SiegPre h M ζ (x ≫ s)),
    SiegPB o u x → SiegPB o u (constPt x) → x = constPt x

def UnramTriple (A : Over X) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over X) ⟶ A)) : Prop :=
  ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ X) (G : Over (Sp (DualNumber k))) [GrpObj G]
    (P' : LB (G ⊗ G).left) (lv' : Std h M → (𝟙_ (Over (Sp (DualNumber k))) ⟶ G)),
    P'.IsLB → IsPullbackTriple G P' lv' A P lv x → IsPullbackTriple G P' lv' A P lv (constPt x) → x = constPt x

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H k _ x G _ P' lv' hP h₁ h₂`. Use `H k x (ofPullback u x G P' lv' hP h₁) ((siegPB_iff _ _ _).2 ?_) ((siegPB_iff _ _ _).2 ?_)` and prove the remaining obligations. Rewrite using `[lvOf_ofPullback]`. Conclude with `h₁`.

Rewrite using `[lvOf_ofPullback]`. Conclude with `h₂`. Introduce `H k _ x o h₁ h₂`. Conclude with `H k x o.A o.P (lvOf o) o.isLB ((siegPB_iff _ _ _).1 h₁) ((siegPB_iff _ _ _).1 h₂)`.
-/
theorem unram_iff {ζ : B} (u : SiegPre h M ζ s) : UnramObj u ↔ UnramTriple u.A u.P (lvOf u) := by
  constructor
  · intro H k _ x G _ P' lv' hP h₁ h₂
    refine H k x (ofPullback u x G P' lv' hP h₁) ((siegPB_iff _ _ _).2 ?_) ((siegPB_iff _ _ _).2 ?_)
    · rw [lvOf_ofPullback]
      exact h₁
    · rw [lvOf_ofPullback]
      exact h₂
  · intro H k _ x o h₁ h₂
    exact H k x o.A o.P (lvOf o) o.isLB ((siegPB_iff _ _ _).1 h₁) ((siegPB_iff _ _ _).1 h₂)

/- English proof (translation)
Assemble the required witnesses or components as `⟨Subtype.val_injective, fun x => ⟨fun ⟨y, hy⟩ => hy ▸ (mem_intRing _).1 y.2, fun hx => ⟨⟨x, (mem_intRing x).2 hx⟩, rfl⟩⟩⟩`.
-/
theorem isUnitBall_intRing (C : Type) [NormedField C] [IsUltrametricDist C] : IsUnitBall (intRing C) C :=
  ⟨Subtype.val_injective, fun x => ⟨fun ⟨y, hy⟩ => hy ▸ (mem_intRing _).1 y.2,
    fun hx => ⟨⟨x, (mem_intRing x).2 hx⟩, rfl⟩⟩⟩

/- English proof (translation)
Establish `r : (algebraMap O C).range = (algebraMap O' C).range` using `Subring.ext fun x => (H.2 x).trans (H'.2 x).symm`. Set `a : O ≃+* (algebraMap O C).range` to `RingEquiv.ofBijective (algebraMap O C).rangeRestrict ⟨fun x y e => H.1 (congrArg Subtype.val e), RingHom.rangeRestrict_surjective _⟩`. Set `b : O' ≃+* (algebraMap O' C).range` to `RingEquiv.ofBijective (algebraMap O' C).rangeRestrict ⟨fun x y e => H'.1 (congrArg Subtype.val e), RingHom.rangeRestrict_surjective _⟩`. Use `⟨a.trans ((RingEquiv.subringCongr r).trans b.symm), RingHom.ext fun x => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Subtype.val (b.apply_symm_apply (RingEquiv.subringCongr r (a x)))`.
-/
theorem exists_ringEquiv {O O' C : Type} [CommRing O] [CommRing O'] [NormedField C] [Algebra O C] [Algebra O' C]
    (H : IsUnitBall O C) (H' : IsUnitBall O' C) :
    ∃ e : O ≃+* O', (algebraMap O' C).comp (e : O →+* O') = algebraMap O C := by
  have r : (algebraMap O C).range = (algebraMap O' C).range :=
    Subring.ext fun x => (H.2 x).trans (H'.2 x).symm
  let a : O ≃+* (algebraMap O C).range := RingEquiv.ofBijective (algebraMap O C).rangeRestrict
    ⟨fun x y e => H.1 (congrArg Subtype.val e), RingHom.rangeRestrict_surjective _⟩
  let b : O' ≃+* (algebraMap O' C).range := RingEquiv.ofBijective (algebraMap O' C).rangeRestrict
    ⟨fun x y e => H'.1 (congrArg Subtype.val e), RingHom.rangeRestrict_surjective _⟩
  refine ⟨a.trans ((RingEquiv.subringCongr r).trans b.symm), RingHom.ext fun x => ?_⟩
  exact congrArg Subtype.val (b.apply_symm_apply (RingEquiv.subringCongr r (a x)))

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem spMap_comp {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂) (g : R₂ →+* R₃) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/- English proof (translation)
Establish `h0 : M ≠ 0` using `by omega`. Prove the components needed by the constructor for the conclusion. Introduce `H C _ _ _ _ _ hC β G _ P' lv' h₁ h₂ h₃ h₄ h₅`. Set `_ : NontriviallyNormedField C` to `{ ‹NormedField C› with non_trivial := ⟨(p : C)⁻¹, by`. Rewrite using `[norm_inv]`.

Conclude with `(one_lt_inv₀ (norm_pos_iff.2 (Nat.cast_ne_zero.2 hp))).2 hC⟩ }`. Set `o` to `ofTriple h0 hζ G P' lv' h₁ h₂ h₃`. Take `⟨o', pb⟩` from `(siegPre_pullback h M B ζ _ _ _ _ (spMap (algebraMap (intRing C) C)) o rfl).1`. Take `⟨x, hx, m⟩` from `H C (intRing C) (isUnitBall_intRing C) hC β o ⟨o', pb, (principal_iff_along pb).2 h₄⟩ h₅`. Establish `m'` using `(siegPB_iff _ _ _).1 m`.

Rewrite `m'` using `[lvOf_ofTriple]`. Conclude with `⟨x, hx, m'⟩`. Introduce and unpack `H C O _ _ _ _ _ _ _ _ hO hC β o ⟨o', pb', pr'⟩ sp`. Take `⟨e, he⟩` from `exists_ringEquiv hO (isUnitBall_intRing C)`. Set `g` to `spMap (e : O →+* intRing C)`.

Set `g'` to `spMap (e.symm : intRing C →+* O)`. Establish `gg : g' ≫ g = 𝟙 _`. Rewrite using `[← spMap_comp, RingEquiv.symm_comp]`. Conclude with `Spec.map_id _`. Take `⟨o₁, pb₁⟩` from `(siegPre_pullback h M B ζ _ _ _ _ g o (spMap_comp β _).symm).1`.

Establish `pbC : SiegPB o' o₁ (spMap (algebraMap (intRing C) C))` using `pb_cancel pb₁ (siegPB_congr pb' ((congrArg spMap he.symm).trans (spMap_comp _ _)))`. Take `⟨_, v₁, v₂, v₃⟩` from `UnitBallVal.main C (intRing C) (isUnitBall_intRing C)`. Establish `tf` using `translFixed_of_generic (intRing C) C o₁ o' pbC (translFixed_of_ample o' pr'.1)`. Take `⟨k₀, pk₀⟩` from `(siegPre_pullback h M B ζ _ _ _ _ (spMap (IsLocalRing.residue O)) o rfl).1`. Take `⟨k₁, pk₁⟩` from `(siegPre_pullback h M B ζ _ _ _ _ (spMap (IsLocalRing.residue (intRing C))) o₁ rfl).1`.

Establish `: IsLocalHom (e : O →+* intRing C)` using `⟨fun a ha => (MulEquiv.isUnit_map e).1 ha⟩`. Establish `pk : SiegPB k₁ k₀ (spMap (IsLocalRing.ResidueField.map (e : O →+* intRing C)))` using `pb_cancel pk₀ (siegPB_congr (pb_comp pb₁ pk₁) ((spMap_comp _ _).symm.trans ((congrArg spMap (IsLocalRing.ResidueField.map_comp_residue _).symm).trans (spMap_comp _ _))))`. Establish `am : Out.RelAmple k₁.A k₁.diag`. Take `⟨φ, φ₂, hφ, sq, iso, -⟩` from `pk`. Conclude with `(pol_pull _ _ _ _ _ φ _ _ (pull_isLB k₀.isLB _) (pull_isLB k₁.isLB _) k₀.ab hφ (diag_iso sq iso)).2.1 ((ample_iff_along pk₀).2 sp)`.

Take `⟨y, hy, m⟩` from `H C hC _ o₁.A o₁.P (lvOf o₁) (isSymmetricPair hM hu o₁) (isLevel_lvOf o₁) (isSymplectic_of_translFixed h0 hζ hu o₁ tf) ((principal_iff_along pbC).1 pr') ((ample_iff_along pk₁).1 am)`. Use `⟨g' ≫ y, ?_, pb_comp ((siegPB_iff _ _ _).2 m) (pb_cancel pb₁ (by rw [gg]; exact pb_id o))⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hy, spMap_comp, ← Category.assoc, gg, Category.id_comp]`.
-/
theorem points_iff {ζ : Bˣ} (hp : p ≠ 0) (hM : 2 ≤ M) (hζ : ζ ^ M = 1) (hu : IsUnit (M : B))
    (u : SiegPre h M (ζ : B) s) : PointsObj p u ↔ PointsTriple p ζ s u.A u.P (lvOf u) := by
  have h0 : M ≠ 0 := by omega
  constructor
  · intro H C _ _ _ _ _ hC β G _ P' lv' h₁ h₂ h₃ h₄ h₅
    let _ : NontriviallyNormedField C :=
      { ‹NormedField C› with
        non_trivial := ⟨(p : C)⁻¹, by
          rw [norm_inv]
          exact (one_lt_inv₀ (norm_pos_iff.2 (Nat.cast_ne_zero.2 hp))).2 hC⟩ }
    let o := ofTriple h0 hζ G P' lv' h₁ h₂ h₃
    obtain ⟨o', pb⟩ := (siegPre_pullback h M B ζ _ _ _ _ (spMap (algebraMap (intRing C) C)) o rfl).1
    obtain ⟨x, hx, m⟩ := H C (intRing C) (isUnitBall_intRing C) hC β o ⟨o', pb, (principal_iff_along pb).2 h₄⟩ h₅
    have m' := (siegPB_iff _ _ _).1 m
    rw [lvOf_ofTriple] at m'
    exact ⟨x, hx, m'⟩
  · rintro H C O _ _ _ _ _ _ _ _ hO hC β o ⟨o', pb', pr'⟩ sp
    obtain ⟨e, he⟩ := exists_ringEquiv hO (isUnitBall_intRing C)
    let g := spMap (e : O →+* intRing C)
    let g' := spMap (e.symm : intRing C →+* O)
    have gg : g' ≫ g = 𝟙 _ := by
      rw [← spMap_comp, RingEquiv.symm_comp]
      exact Spec.map_id _
    obtain ⟨o₁, pb₁⟩ := (siegPre_pullback h M B ζ _ _ _ _ g o (spMap_comp β _).symm).1
    have pbC : SiegPB o' o₁ (spMap (algebraMap (intRing C) C)) :=
      pb_cancel pb₁ (siegPB_congr pb' ((congrArg spMap he.symm).trans (spMap_comp _ _)))
    obtain ⟨_, v₁, v₂, v₃⟩ := UnitBallVal.main C (intRing C) (isUnitBall_intRing C)
    have tf := translFixed_of_generic (intRing C) C o₁ o' pbC (translFixed_of_ample o' pr'.1)
    obtain ⟨k₀, pk₀⟩ := (siegPre_pullback h M B ζ _ _ _ _ (spMap (IsLocalRing.residue O)) o rfl).1
    obtain ⟨k₁, pk₁⟩ := (siegPre_pullback h M B ζ _ _ _ _ (spMap (IsLocalRing.residue (intRing C))) o₁ rfl).1
    have : IsLocalHom (e : O →+* intRing C) := ⟨fun a ha => (MulEquiv.isUnit_map e).1 ha⟩
    have pk : SiegPB k₁ k₀ (spMap (IsLocalRing.ResidueField.map (e : O →+* intRing C))) :=
      pb_cancel pk₀ (siegPB_congr (pb_comp pb₁ pk₁) ((spMap_comp _ _).symm.trans
        ((congrArg spMap (IsLocalRing.ResidueField.map_comp_residue _).symm).trans (spMap_comp _ _))))
    have am : Out.RelAmple k₁.A k₁.diag := by
      obtain ⟨φ, φ₂, hφ, sq, iso, -⟩ := pk
      exact (pol_pull _ _ _ _ _ φ _ _ (pull_isLB k₀.isLB _) (pull_isLB k₁.isLB _) k₀.ab hφ (diag_iso sq iso)).2.1
        ((ample_iff_along pk₀).2 sp)
    obtain ⟨y, hy, m⟩ := H C hC _ o₁.A o₁.P (lvOf o₁) (isSymmetricPair hM hu o₁) (isLevel_lvOf o₁)
      (isSymplectic_of_translFixed h0 hζ hu o₁ tf) ((principal_iff_along pbC).1 pr') ((ample_iff_along pk₁).1 am)
    refine ⟨g' ≫ y, ?_, pb_comp ((siegPB_iff _ _ _).2 m) (pb_cancel pb₁ (by rw [gg]; exact pb_id o))⟩
    rw [Category.assoc, hy, spMap_comp, ← Category.assoc, gg, Category.id_comp]

def FamilyObj {ζ : B} (u : SiegPre h M ζ s) : Prop :=
  SmoothOfRelativeDimension (h * (h + 1) / 2) s ∧ QuasiCompact s ∧ u.Principal ∧ PointsObj p u ∧ UnramObj u

def FamilyTriple (ζ : Bˣ) (s : X ⟶ Sp B) (A : Over X) [GrpObj A] (P : LB (A ⊗ A).left)
    (lv : Std h M → (𝟙_ (Over X) ⟶ A)) : Prop :=
  SmoothOfRelativeDimension (h * (h + 1) / 2) s ∧ LocallyOfFiniteType s ∧ QuasiCompact s ∧
    IsSymmetricPair h A P ∧ IsPrincipal A P ∧ IsLevel A lv ∧ IsSymplectic ζ s A P lv ∧
    PointsTriple p ζ s A P lv ∧ UnramTriple A P lv

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b, c, d, e⟩`. Establish `: Smooth s` using `SmoothOfRelativeDimension.smooth (h * (h + 1) / 2) s`. Conclude with `⟨a, inferInstance, b, isSymmetricPair hM hu u, (principal_iff u).1 c, isLevel_lvOf u, isSymplectic_of_translFixed (by omega) hζ hu u (translFixed_of_ample u c.1), (points_iff p hp hM hζ hu u).1 d, (unram_iff u).1 e⟩`. Introduce and unpack `⟨a, -, b, -, c, -, -, d, e⟩`.

Conclude with `⟨a, b, (principal_iff u).2 c, (points_iff p hp hM hζ hu u).2 d, (unram_iff u).2 e⟩`.
-/
theorem family_iff {ζ : Bˣ} (hp : p ≠ 0) (hM : 2 ≤ M) (hζ : ζ ^ M = 1) (hu : IsUnit (M : B))
    (u : SiegPre h M (ζ : B) s) : FamilyObj p u ↔ FamilyTriple p ζ s u.A u.P (lvOf u) := by
  constructor
  · rintro ⟨a, b, c, d, e⟩
    have : Smooth s := SmoothOfRelativeDimension.smooth (h * (h + 1) / 2) s
    exact ⟨a, inferInstance, b, isSymmetricPair hM hu u, (principal_iff u).1 c, isLevel_lvOf u,
      isSymplectic_of_translFixed (by omega) hζ hu u (translFixed_of_ample u c.1),
      (points_iff p hp hM hζ hu u).1 d, (unram_iff u).1 e⟩
  · rintro ⟨a, -, b, -, c, -, -, d, e⟩
    exact ⟨a, b, (principal_iff u).2 c, (points_iff p hp hM hζ hu u).2 d, (unram_iff u).2 e⟩

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `family_iff p hp hM hζ hu u`.
-/
theorem family_iff' {ζ : Bˣ} {ζ₀ : B} (e : (ζ : B) = ζ₀) (hp : p ≠ 0) (hM : 2 ≤ M) (hζ : ζ ^ M = 1)
    (hu : IsUnit (M : B)) (u : SiegPre h M ζ₀ s) : FamilyObj p u ↔ FamilyTriple p ζ s u.A u.P (lvOf u) := by
  subst e
  exact family_iff p hp hM hζ hu u

/- English proof (translation)
Substitute `e` using the available equality. Use `⟨ofTriple (by omega) hζ A P lv H.2.2.2.1 H.2.2.2.2.2.1 H.2.2.2.2.2.2.1, (family_iff p hp hM hζ hu _).2 ?_, congrArg (fun l => (⟨A, g, P, l⟩ : Σ (A : Over X) (_ : GrpObj A), LB (A ⊗ A).left × (Std h M → (𝟙_ (Over X) ⟶ A)))) (lvOf_ofTriple _ _ _ _ _ _ _ _)⟩` and prove the remaining obligations. Rewrite using `[lvOf_ofTriple]`. Conclude with `H`.
-/
theorem exists_familyObj {ζ : Bˣ} {ζ₀ : B} (e : (ζ : B) = ζ₀) (hp : p ≠ 0) (hM : 2 ≤ M) (hζ : ζ ^ M = 1)
    (hu : IsUnit (M : B)) {A : Over X} [g : GrpObj A] {P : LB (A ⊗ A).left} {lv : Std h M → (𝟙_ (Over X) ⟶ A)}
    (H : FamilyTriple p ζ s A P lv) : ∃ u : SiegPre h M ζ₀ s, FamilyObj p u ∧ (⟨u.A, u.grp, u.P, lvOf u⟩ :
      Σ (A : Over X) (_ : GrpObj A), LB (A ⊗ A).left × (Std h M → (𝟙_ (Over X) ⟶ A))) = ⟨A, g, P, lv⟩ := by
  subst e
  refine ⟨ofTriple (by omega) hζ A P lv H.2.2.2.1 H.2.2.2.2.2.1 H.2.2.2.2.2.2.1, (family_iff p hp hM hζ hu _).2 ?_,
    congrArg (fun l => (⟨A, g, P, l⟩ : Σ (A : Over X) (_ : GrpObj A),
      LB (A ⊗ A).left × (Std h M → (𝟙_ (Over X) ⟶ A)))) (lvOf_ofTriple _ _ _ _ _ _ _ _)⟩
  rw [lvOf_ofTriple]
  exact H

end Clauses

section Main

/- English proof (translation)
Substitute `e` using the available equality. Take `rfl : ζ = ζ'` from `Units.ext (Subtype.ext hζ)`. Establish `: spMap (Subring.inclusion (le_refl R)) = 𝟙 _` using `Spec.map_id _`. Rewrite using `[this, Category.comp_id]`.
-/
theorem familyTriple_congr {h M : ℕ} (p : ℕ) {R R' : Subring ℂ} (e : R = R') (ζ : Rˣ) (ζ' : R'ˣ)
    (hζ : ((ζ : R) : ℂ) = ((ζ' : R') : ℂ)) {X : Scheme.{0}} (s : X ⟶ Sp R) (A : Over X) [GrpObj A]
    (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over X) ⟶ A)) :
    FamilyTriple p ζ s A P lv ↔ FamilyTriple p ζ' (s ≫ spMap (Subring.inclusion e.ge)) A P lv := by
  subst e
  obtain rfl : ζ = ζ' := Units.ext (Subtype.ext hζ)
  have : spMap (Subring.inclusion (le_refl R)) = 𝟙 _ := Spec.map_id _
  rw [this, Category.comp_id]

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `⟨s, (congrArg (s ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)⟩`.
-/
theorem exists_comp_inclusion {R R' : Subring ℂ} (e : R = R') {X : Scheme.{0}} (s : X ⟶ Sp R') :
    ∃ s₀ : X ⟶ Sp R, s₀ ≫ spMap (Subring.inclusion e.ge) = s := by
  subst e
  exact ⟨s, (congrArg (s ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)⟩

/- English proof (translation)
The claim follows from `Subtype.ext (Complex.isPrimitiveRoot_exp M hM).pow_eq_one`.
-/
theorem zeta_pow_eq_one (p : ℕ) {M : ℕ} (hM : M ≠ 0) : zetaZP p M ^ M = 1 :=
  Subtype.ext (Complex.isPrimitiveRoot_exp M hM).pow_eq_one

def zetaZPUnit (p : ℕ) {M : ℕ} (hM : M ≠ 0) : (ZP p M)ˣ := Units.ofPowEqOne (zetaZP p M) M (zeta_pow_eq_one p hM) hM

/- English proof (translation)
The claim follows from `Units.val_ofPowEqOne _ _ _ _`.
-/
theorem zetaZPUnit_val (p : ℕ) {M : ℕ} (hM : M ≠ 0) : (zetaZPUnit p hM : ZP p M) = zetaZP p M :=
  Units.val_ofPowEqOne _ _ _ _

/- English proof (translation)
The claim follows from `Units.ext (by rw [Units.val_pow_eq_pow_val, zetaZPUnit_val, zeta_pow_eq_one p hM, Units.val_one])`.
-/
theorem zetaZPUnit_pow (p : ℕ) {M : ℕ} (hM : M ≠ 0) : zetaZPUnit p hM ^ M = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, zetaZPUnit_val, zeta_pow_eq_one p hM, Units.val_one])

/- English proof (translation)
Rewrite using `[zetaZPUnit_val, zetaUnit, Units.val_ofPowEqOne]`. Both sides reduce to the same expression.
-/
theorem zeta_units (p : ℕ) {M : ℕ} (hM : M ≠ 0) :
    ((zetaZPUnit p hM : ZP p M) : ℂ) = ((zetaUnit p hM : cycloLocal p M) : ℂ) := by
  rw [zetaZPUnit_val, zetaUnit, Units.val_ofPowEqOne]
  rfl

variable {h p M : ℕ}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem isSiegelFamily_def (hM : M ≠ 0) (X : Scheme.{0}) (s : X ⟶ Sp (cycloLocal p M)) (A : Over X) [GrpObj A]
    (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over X) ⟶ A)) :
    IsSiegelFamily h p hM X s A P lv ↔ FamilyTriple p (zetaUnit p hM) s A P lv := Iff.rfl

/- English proof (translation)
Rewrite using `[zp_eq_cycloLocal hp]`. Conclude with `isUnit_cycloLocal hp hc`.
-/
theorem isUnit_zp (hp : p.Prime) (hc : M.Coprime p) : IsUnit (M : ZP p M) := by
  rw [zp_eq_cycloLocal hp]
  exact isUnit_cycloLocal hp hc

/- English proof (translation)
Establish `h0 : M ≠ 0` using `by omega`. Establish `hu` using `isUnit_zp hp hc`. Conclude with `(family_iff' p (zetaZPUnit_val p h0) hp.ne_zero hM (zetaZPUnit_pow p h0) hu u).trans ((familyTriple_congr p (zp_eq_cycloLocal hp M) _ _ (zeta_units p h0) s u.A u.P (lvOf u)).trans (isSiegelFamily_def h0 _ _ _ _ _).symm)`.
-/
theorem familyObj_iff (hp : p.Prime) (hM : 2 ≤ M) (hc : M.Coprime p) {X : Scheme.{0}} {s : X ⟶ Sp (ZP p M)}
    (u : SiegPre h M (zetaZP p M) s) : FamilyObj p u ↔
      IsSiegelFamily h p (M := M) (by omega) X (s ≫ spMap (Subring.inclusion (zp_eq_cycloLocal hp M).ge))
        u.A u.P (lvOf u) := by
  have h0 : M ≠ 0 := by omega
  have hu := isUnit_zp hp hc
  exact (family_iff' p (zetaZPUnit_val p h0) hp.ne_zero hM (zetaZPUnit_pow p h0) hu u).trans
    ((familyTriple_congr p (zp_eq_cycloLocal hp M) _ _ (zeta_units p h0) s u.A u.P (lvOf u)).trans
      (isSiegelFamily_def h0 _ _ _ _ _).symm)

abbrev FamilyData (h p M : ℕ) : Type 1 :=
  Σ (X : Scheme.{0}) (_ : X ⟶ Sp (cycloLocal p M)) (A : Over X) (_ : GrpObj A),
    LB (A ⊗ A).left × (Std h M → (𝟙_ (Over X) ⟶ A))

def dataOf (hp : p.Prime) (F : SiegelFamily h p M) : FamilyData h p M :=
  ⟨F.X, F.s ≫ spMap (Subring.inclusion (zp_eq_cycloLocal hp M).ge), F.univ.A, F.univ.grp, F.univ.P, lvOf F.univ⟩

/- English proof (translation)
Establish `h0 : M ≠ 0` using `by omega`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Take `⟨s, rfl⟩` from `exists_comp_inclusion (zp_eq_cycloLocal hp M) s`. Establish `H₀` using `(familyTriple_congr p (zp_eq_cycloLocal hp M) _ _ (zeta_units p h0) s A P lv).2 ((isSiegelFamily_def h0 _ _ _ _ _).1 H)`.

Take `⟨u, ⟨a, b, c, d, e⟩, hd⟩` from `exists_familyObj p (zetaZPUnit_val p h0) hp.ne_zero hM (zetaZPUnit_pow p h0) (isUnit_zp hp hc) H₀`. Conclude with `⟨⟨X, s, a, b, u, c, d, e⟩, congrArg (fun d => (⟨X, _, d⟩ : FamilyData h p M)) hd⟩`. Introduce and unpack `⟨F, e⟩`. Establish `H` using `(familyObj_iff hp hM hc F.univ).1 ⟨F.smooth, F.qc, F.princ, F.points, F.unram⟩`. Unfold `dataOf at e`.

Consider the cases of `e`. Conclude with `H`.
-/
theorem isSiegelFamily_iff (hp : p.Prime) (hM : 2 ≤ M) (hc : M.Coprime p) (X : Scheme.{0})
    (s : X ⟶ Sp (cycloLocal p M)) (A : Over X) [g : GrpObj A] (P : LB (A ⊗ A).left)
    (lv : Std h M → (𝟙_ (Over X) ⟶ A)) :
    IsSiegelFamily h p (M := M) (by omega) X s A P lv ↔
      ∃ F : SiegelFamily h p M, dataOf hp F = ⟨X, s, A, g, P, lv⟩ := by
  have h0 : M ≠ 0 := by omega
  constructor
  · intro H
    obtain ⟨s, rfl⟩ := exists_comp_inclusion (zp_eq_cycloLocal hp M) s
    have H₀ := (familyTriple_congr p (zp_eq_cycloLocal hp M) _ _ (zeta_units p h0) s A P lv).2
      ((isSiegelFamily_def h0 _ _ _ _ _).1 H)
    obtain ⟨u, ⟨a, b, c, d, e⟩, hd⟩ := exists_familyObj p (zetaZPUnit_val p h0) hp.ne_zero hM
      (zetaZPUnit_pow p h0) (isUnit_zp hp hc) H₀
    exact ⟨⟨X, s, a, b, u, c, d, e⟩, congrArg (fun d => (⟨X, _, d⟩ : FamilyData h p M)) hd⟩
  · rintro ⟨F, e⟩
    have H := (familyObj_iff hp hM hc F.univ).1 ⟨F.smooth, F.qc, F.princ, F.points, F.unram⟩
    unfold dataOf at e
    cases e
    exact H

/- English proof (translation)
Use `forall_congr' fun h => forall_congr' fun p => forall_congr' fun n => forall_congr' fun _ => forall_congr' fun hp => forall_congr' fun hn => forall_congr' fun _ => forall_congr' fun hne => ?_` and prove the remaining obligations. Establish `co : ∀ j, (n ^ j).Coprime p` using `fun j => Nat.Coprime.pow_left j ((Nat.coprime_primes hn hp).2 hne)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, hj, ⟨F⟩⟩`. Conclude with `⟨n ^ j, hj, ⟨j, rfl⟩, _, _, _, _, _, _, (isSiegelFamily_iff hp (by omega) (co j) _ _ _ _ _).2 ⟨F, rfl⟩⟩`.

Introduce and unpack `⟨_, hj, ⟨j, rfl⟩, X, s, A, _, P, lv, H⟩`. Take `⟨F, -⟩` from `(isSiegelFamily_iff hp (by omega) (co j) X s A P lv).1 H`. Conclude with `⟨j, hj, ⟨F⟩⟩`.
-/
theorem existence_iff : N0 ↔ SiegelFamilyExists := by
  refine forall_congr' fun h => forall_congr' fun p => forall_congr' fun n => forall_congr' fun _ =>
    forall_congr' fun hp => forall_congr' fun hn => forall_congr' fun _ => forall_congr' fun hne => ?_
  have co : ∀ j, (n ^ j).Coprime p := fun j => Nat.Coprime.pow_left j ((Nat.coprime_primes hn hp).2 hne)
  constructor
  · rintro ⟨j, hj, ⟨F⟩⟩
    exact ⟨n ^ j, hj, ⟨j, rfl⟩, _, _, _, _, _, _, (isSiegelFamily_iff hp (by omega) (co j) _ _ _ _ _).2 ⟨F, rfl⟩⟩
  · rintro ⟨_, hj, ⟨j, rfl⟩, X, s, A, _, P, lv, H⟩
    obtain ⟨F, -⟩ := (isSiegelFamily_iff hp (by omega) (co j) X s A P lv).1 H
    exact ⟨j, hj, ⟨F⟩⟩

/- English proof (translation)
Use `⟨fun p M hp => zp_eq_cycloLocal hp M, fun C _ _ => ⟨isUnitBall_intRing C, fun O _ _ H => exists_ringEquiv H (isUnitBall_intRing C)⟩, fun h M a b => stdForm_red a b, fun h M B _ ζ S s hM hζ hu => ⟨fun o => ⟨lvOf_red o, isSymmetricPair hM hu o, isLevel_lvOf o, fun ha => isSymplecti …` and prove the remaining obligations. Conclude with `⟨ofTriple (by omega) hζ A P lv h₁ h₂ h₃, congrArg (fun l => (⟨A, g, P, l⟩ : Σ (A : Over S) (_ : GrpObj A), LB (A ⊗ A).left × (Std h M → (𝟙_ (Over S) ⟶ A)))) (lvOf_ofTriple _ _ _ _ _ _ _ _)⟩`.
-/
theorem typings_agree :
    (∀ p M : ℕ, p.Prime → ZP p M = cycloLocal p M) ∧
    (∀ (C : Type) [NormedField C] [IsUltrametricDist C], IsUnitBall (intRing C) C ∧
      ∀ (O : Type) [CommRing O] [Algebra O C], IsUnitBall O C →
        ∃ e : O ≃+* intRing C, (intRing C).subtype.comp (e : O →+* intRing C) = algebraMap O C) ∧
    (∀ (h M : ℕ) (a b : Fin h ⊕ Fin h → ℤ), stdForm (red M a) (red M b) = (omegaStd a b : ZMod M)) ∧
    (∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : Bˣ) (S : Scheme.{0}) (s : S ⟶ Sp B), 2 ≤ M → ζ ^ M = 1 →
      IsUnit (M : B) →
      (∀ o : SiegPre h M (ζ : B) s, (∀ a, lvOf o (red M a) = o.lev a) ∧ IsSymmetricPair h o.A o.P ∧
        IsLevel o.A (lvOf o) ∧ (Out.RelAmple o.A o.diag → IsSymplectic ζ s o.A o.P (lvOf o)) ∧
        (o.Principal ↔ IsPrincipal o.A o.P) ∧
        (∀ (B' : Type) [CommRing B'] (ζ' : B') (S' : Scheme.{0}) (s' : S' ⟶ Sp B') (o' : SiegPre h M ζ' s')
          (t : S' ⟶ S), (SiegPB o' o t ↔ IsPullbackTriple o'.A o'.P (lvOf o') o.A o.P (lvOf o) t) ∧
          (SiegPB o' o t → (o'.Principal ↔ IsPrincipalAlong o.A o.P t))) ∧
        (∀ p : ℕ, p ≠ 0 → (PointsObj p o ↔ PointsTriple p ζ s o.A o.P (lvOf o))) ∧
        (UnramObj o ↔ UnramTriple o.A o.P (lvOf o))) ∧
      ∀ (A : Over S) [g : GrpObj A] (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over S) ⟶ A)),
        IsSymmetricPair h A P → IsLevel A lv → IsSymplectic ζ s A P lv →
        ∃ o : SiegPre h M (ζ : B) s, (⟨o.A, o.grp, o.P, lvOf o⟩ :
          Σ (A : Over S) (_ : GrpObj A), LB (A ⊗ A).left × (Std h M → (𝟙_ (Over S) ⟶ A))) = ⟨A, g, P, lv⟩) ∧
    (∀ (h p M : ℕ) (hp : p.Prime) (hM : 2 ≤ M), M.Coprime p → ∀ (X : Scheme.{0}) (s : X ⟶ Sp (cycloLocal p M))
      (A : Over X) [g : GrpObj A] (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over X) ⟶ A)),
      IsSiegelFamily h p (M := M) (by omega) X s A P lv ↔
        ∃ F : SiegelFamily h p M, dataOf hp F = ⟨X, s, A, g, P, lv⟩) ∧
    (N0 ↔ SiegelFamilyExists) := by
  refine ⟨fun p M hp => zp_eq_cycloLocal hp M,
    fun C _ _ => ⟨isUnitBall_intRing C, fun O _ _ H => exists_ringEquiv H (isUnitBall_intRing C)⟩,
    fun h M a b => stdForm_red a b, fun h M B _ ζ S s hM hζ hu => ⟨fun o => ⟨lvOf_red o, isSymmetricPair hM hu o,
      isLevel_lvOf o, fun ha => isSymplectic_of_translFixed (by omega) hζ hu o (translFixed_of_ample o ha),
      principal_iff o, fun B' _ ζ' S' s' o' t => ⟨siegPB_iff o' o t, principal_iff_along⟩,
      fun p hp => points_iff p hp hM hζ hu o, unram_iff o⟩, fun A g P lv h₁ h₂ h₃ => ?_⟩,
    fun h p M hp hM hc X s A _ P lv => isSiegelFamily_iff hp hM hc X s A P lv, existence_iff⟩
  exact ⟨ofTriple (by omega) hζ A P lv h₁ h₂ h₃, congrArg (fun l => (⟨A, g, P, l⟩ :
    Σ (A : Over S) (_ : GrpObj A), LB (A ⊗ A).left × (Std h M → (𝟙_ (Over S) ⟶ A)))) (lvOf_ofTriple _ _ _ _ _ _ _ _)⟩

end Main

end GlobalTheory.SiegelTypings
