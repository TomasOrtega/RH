import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculusStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinearStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointEndomorphismImageEqMovedGtPointStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkPairingExistsUniqueTorusStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemOfNonempty
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilIsCompIffOfRosatiAdj

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.KeyIota
open GlobalTheory.TorusExt

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hd : a - b ≠ 0` using `sub_ne_zero.2 hne`. Take `⟨φ, hφ⟩` from `Module.Projective.exists_dual_ne_zero ℤ hd`. Set `k : ℕ` to `(φ (a - b)).natAbs + 1`. Use `haveI : NeZero k := ⟨Nat.succ_ne_zero _⟩`.

Use `haveI : NeZero (k : F) := ⟨Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot F k`. Set `u : Fˣ` to `(hζ.isUnit (NeZero.ne k)).unit`. Establish `hu : IsPrimitiveRoot u k` using `hζ.isUnit_unit (NeZero.ne k)`. Set `t : Multiplicative X →* Fˣ` to `(zpowersHom Fˣ u).comp (AddMonoidHom.toMultiplicative φ.toAddMonoidHom)`.

Establish `ht : ∀ x, t (Multiplicative.ofAdd x) = u ^ φ x` using `fun _ => rfl`. Establish `h1` using `h k (Nat.succ_le_succ (Nat.zero_le _)) t (MonoidHom.ext fun x => by show t (Multiplicative.ofAdd x.toAdd) ^ k = 1`. Rewrite using `[ht, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu.pow_eq_one, one_zpow])`. Rewrite `h1` using `[ht, ht]`. Establish `h2 : u ^ φ (a - b) = 1` using `by rw [map_sub, zpow_sub, h1, mul_inv_cancel]`.

Establish `h3` using `Int.natCast_dvd.1 ((hu.zpow_eq_one_iff_dvd _).1 h2)`. Establish `h4` using `Nat.le_of_dvd (Int.natAbs_pos.2 hφ) h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_of_torsion_chars {X F : Type} [AddCommGroup X] [Module.Free ℤ X] [Field F] [IsAlgClosed F] [CharZero F]
    {a b : X} (h : ∀ k : ℕ, 1 ≤ k → ∀ t : Multiplicative X →* Fˣ, t ^ k = 1 →
      t (Multiplicative.ofAdd a) = t (Multiplicative.ofAdd b)) : a = b := by
  by_contra hne
  have hd : a - b ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℤ hd
  let k : ℕ := (φ (a - b)).natAbs + 1
  haveI : NeZero k := ⟨Nat.succ_ne_zero _⟩
  haveI : NeZero (k : F) := ⟨Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F k
  let u : Fˣ := (hζ.isUnit (NeZero.ne k)).unit
  have hu : IsPrimitiveRoot u k := hζ.isUnit_unit (NeZero.ne k)
  let t : Multiplicative X →* Fˣ := (zpowersHom Fˣ u).comp (AddMonoidHom.toMultiplicative φ.toAddMonoidHom)
  have ht : ∀ x, t (Multiplicative.ofAdd x) = u ^ φ x := fun _ => rfl
  have h1 := h k (Nat.succ_le_succ (Nat.zero_le _)) t (MonoidHom.ext fun x => by
    show t (Multiplicative.ofAdd x.toAdd) ^ k = 1
    rw [ht, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu.pow_eq_one, one_zpow])
  rw [ht, ht] at h1
  have h2 : u ^ φ (a - b) = 1 := by rw [map_sub, zpow_sub, h1, mul_inv_cancel]
  have h3 := Int.natCast_dvd.1 ((hu.zpow_eq_one_iff_dvd _).1 h2)
  have h4 := Nat.le_of_dvd (Int.natAbs_pos.2 hφ) h3
  omega

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

/- English proof (translation)
Introduce `w' w hw' hw s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ α j`. Establish `e` using `h w w' hw hw' s s₃ s₄ s₁ s₂ h₃ h₄ h₁ h₂ α j`. Rewrite using `[e, ← _root_.mul_assoc]`. Establish `: ∀ W, DegPre.constBF D F ((z⁻¹ : Fˣ) : F) W * DegPre.constBF D F (z : F) W = 1` using `fun W => by`. Unfold `DegPre.constBF`.

Rewrite using `[← map_mul, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one, map_one]`. Rewrite using `[this, _root_.one_mul]`.
-/
theorem weilQkIs_swap {k : ℕ} {p p' : QkPt D F k} {z : Fˣ} (h : WeilQkIs D F k p p' z) :
    WeilQkIs D F k p' p (z⁻¹ : Fˣ) := by
  intro w' w hw' hw s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ α j
  have e := h w w' hw hw' s s₃ s₄ s₁ s₂ h₃ h₄ h₁ h₂ α j
  rw [e, ← _root_.mul_assoc]
  have : ∀ W, DegPre.constBF D F ((z⁻¹ : Fˣ) : F) W * DegPre.constBF D F (z : F) W = 1 := fun W => by
    unfold DegPre.constBF
    rw [← map_mul, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one, map_one]
  rw [this, _root_.one_mul]

/- English proof (translation)
Introduce `hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U E E' hE hE' hadj y g g' hg hgg'`. Establish `hA : AdmBase V (maximalIdeal V)` using `⟨inferInstance, inferInstance, inferInstance, hc⟩`. Use `haveI : CharZero (FractionRing V) := charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))`. Use `haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing V) F).injective`. Use `letI := gtGroup D.toPre F`.

Establish `hB` using `D.tau_bimult`. Establish `inj` using `GlobalTheory.IotaInj.main hL V _ hA D F`. Establish `dv` using `(gt_onto_divisible_kernel hL V _ hA D F).2.1`. Establish `ec` using `GlobalTheory.T.uniformizationEndomorphism_calculus hL V _ hA D A G hG U F`. Establish `key` using `GlobalTheory.T.torsionPoint_endomorphism_image_eq_moved_gtPoint hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U`.

Establish `ros` using `(GlobalTheory.T.rosatiAdjoint_abelianPart_and_classifying_map_linear hL V _ hA D A G hG U E E' hadj).1`. Establish `act : ∀ e : EndU U.toUnifPre, ∃ a : GtPtF D.toPre F →+ GtPtF D.toPre F, ∀ x x', e.Act x x' ↔ x' = a x`. Introduce `e`. Take `⟨ex, ad, -⟩` from `ec e e e`. Use `choose a ha hu using ex`.

Conclude with `⟨AddMonoidHom.mk' a fun x x' => (isAdd_iff_eq _ _ _).1 (ad x x' (x + x') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (ha x) (ha x') (ha _)), fun x x' => ⟨hu x x', fun h => h ▸ ha x⟩⟩`. Take `⟨a, ha⟩` from `act E`. Take `⟨a', ha'⟩` from `act E'`. Establish `hy : g = iota hB F y` using `(isIota_iff_eq hB _ _).1 hg`. Establish `hg' : g' = a g` using `(ha _ _).1 hgg'`.

Establish `div : ∀ k : ℕ, 1 ≤ k → ∀ f, Tors U.toUnifPre F k f → ∃ p p' : QkPt D.toPre F k, p.y = y ∧ f p' = f p ≫ E.aA ∧ GtPtF.IsIota p'.y g'`. Introduce `k hk f hf`. Take `⟨gk, hgk⟩` from `dv k hk g`. Set `p : QkPt D.toPre F k` to `⟨y, gk, g, hgk, hg⟩`. Take `⟨p', e₁, e₂⟩` from `key E hE k hk p (f p) ((hf.1 _ _).2 rfl) (a gk) ((ha _ _).2 rfl)`.

Use `⟨p, p', rfl, ((hf.1 _ _).1 e₂).symm, (isIota_iff_eq hB _ _).2 ?_⟩` and prove the remaining obligations. Rewrite using `[← qk_nsmul hB p', e₁, ← map_nsmul, hg', (isNsmul_iff_eq _ _ _).1 hgk]`. Take `⟨f₁, hf₁⟩` from `GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F 1 le_rfl`. Take `⟨-, p₁, -, -, hp₁⟩` from `div 1 le_rfl f₁ hf₁`. It suffices to establish `hs : p₁.y = E'.h y from hs ▸ hp₁`.

Use `eq_of_torsion_chars (F := F) fun k hk t ht => ?_` and prove the remaining obligations. Take `⟨f, hf⟩` from `GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F k hk`. Take `⟨p, p', hp, hpp', hp'⟩` from `div k hk f hf`. Establish `wp` using `GlobalTheory.T.weilQk_pairing_existsUnique_torus hL V _ hA D F k hk`. Rewrite using `[inj _ _ _ hp₁ hp', ← hp]`.

Establish `tor : ∀ p : QkPt D.toPre F k, f p ^ k = 1` using `fun p => by`. Take `⟨w, hw⟩` from `U.toUnifPre.ext`. Conclude with `((hf.1 p _).2 rfl w hw).1`. Establish `h0 : k • torusPt D.toPre F (Additive.ofMul t) = 0`. Rewrite using `[← map_nsmul, ← ofMul_pow, ht, ofMul_one, map_zero]`.

Set `q : QkPt D.toPre F k` to `qkMk hB 0 (torusPt D.toPre F (Additive.ofMul t)) (h0.trans (map_zero _).symm)`. Establish `hq : IsTor t q.g` using `(isTor_iff _ _).2 (isTorusPtF_torusPt t)`. Take `⟨q', e₁, e₂⟩` from `key E' hE' k hk q (f q) ((hf.1 _ _).2 rfl) (a' q.g) ((ha' _ _).2 rfl)`. Establish `hq' : IsTor (t.comp (AddMonoidHom.toMultiplicative E'.h)) q'.g` using `(ec E' E' E').2.2.1 t q.g q'.g hq ((ha' _ _).2 e₁)`. Establish `hq0 : q'.y = 0`.

Use `inj _ _ (0 : GtPtF D.toPre F) ((isIota_iff_eq hB _ _).2 ?_) ((isIota_iff_eq hB _ _).2 (map_zero _).symm)` and prove the remaining obligations. Rewrite using `[← qk_nsmul hB q', e₁, ← map_nsmul]`. Conclude with `((congrArg a' h0).trans (map_zero _)).symm`. Establish `w₁` using `(hf.2.2.2.2 _ _ _).1 (weilQkIs_swap ((wp q p').2 t rfl hq))`. Rewrite `w₁` using `[hpp', weilIs_comp_iff_of_rosatiAdj hL _ A E.aA E'.aA E.homA E'.homA ros F _ k _ _ (tor p) (tor q), (hf.1 _ _).1 e₂]`.

Establish `w₂` using `weilQkIs_swap ((hf.2.2.2.2 _ _ _).2 w₁)`. Rewrite `w₂` using `[inv_inv]`. Conclude with `(wp q' p).1.unique w₂ ((wp q' p).2 _ hq0 hq')`.
-/
theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ E E' : EndU U.toUnifPre, Function.Injective E.h → Function.Injective E'.h → LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → ∀ y (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (E'.h y) g' := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U E E' hE hE' hadj y g g' hg hgg'
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  haveI : CharZero (FractionRing V) := charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing V) F).injective
  letI := gtGroup D.toPre F
  have hB := D.tau_bimult
  have inj := GlobalTheory.IotaInj.main hL V _ hA D F
  have dv := (gt_onto_divisible_kernel hL V _ hA D F).2.1
  have ec := GlobalTheory.T.uniformizationEndomorphism_calculus hL V _ hA D A G hG U F
  have key := GlobalTheory.T.torsionPoint_endomorphism_image_eq_moved_gtPoint hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U
  have ros := (GlobalTheory.T.rosatiAdjoint_abelianPart_and_classifying_map_linear hL V _ hA D A G hG U E E' hadj).1

  have act : ∀ e : EndU U.toUnifPre, ∃ a : GtPtF D.toPre F →+ GtPtF D.toPre F, ∀ x x', e.Act x x' ↔ x' = a x := by
    intro e
    obtain ⟨ex, ad, -⟩ := ec e e e
    choose a ha hu using ex
    exact ⟨AddMonoidHom.mk' a fun x x' => (isAdd_iff_eq _ _ _).1
      (ad x x' (x + x') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (ha x) (ha x') (ha _)),
      fun x x' => ⟨hu x x', fun h => h ▸ ha x⟩⟩
  obtain ⟨a, ha⟩ := act E
  obtain ⟨a', ha'⟩ := act E'
  have hy : g = iota hB F y := (isIota_iff_eq hB _ _).1 hg
  have hg' : g' = a g := (ha _ _).1 hgg'

  have div : ∀ k : ℕ, 1 ≤ k → ∀ f, Tors U.toUnifPre F k f → ∃ p p' : QkPt D.toPre F k, p.y = y ∧
      f p' = f p ≫ E.aA ∧ GtPtF.IsIota p'.y g' := by
    intro k hk f hf
    obtain ⟨gk, hgk⟩ := dv k hk g
    let p : QkPt D.toPre F k := ⟨y, gk, g, hgk, hg⟩
    obtain ⟨p', e₁, e₂⟩ := key E hE k hk p (f p) ((hf.1 _ _).2 rfl) (a gk) ((ha _ _).2 rfl)
    refine ⟨p, p', rfl, ((hf.1 _ _).1 e₂).symm, (isIota_iff_eq hB _ _).2 ?_⟩
    rw [← qk_nsmul hB p', e₁, ← map_nsmul, hg', (isNsmul_iff_eq _ _ _).1 hgk]
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F 1 le_rfl
  obtain ⟨-, p₁, -, -, hp₁⟩ := div 1 le_rfl f₁ hf₁
  suffices hs : p₁.y = E'.h y from hs ▸ hp₁
  refine eq_of_torsion_chars (F := F) fun k hk t ht => ?_
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F k hk
  obtain ⟨p, p', hp, hpp', hp'⟩ := div k hk f hf
  have wp := GlobalTheory.T.weilQk_pairing_existsUnique_torus hL V _ hA D F k hk
  rw [inj _ _ _ hp₁ hp', ← hp]
  have tor : ∀ p : QkPt D.toPre F k, f p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U.toUnifPre.ext
    exact ((hf.1 p _).2 rfl w hw).1
  have h0 : k • torusPt D.toPre F (Additive.ofMul t) = 0 := by
    rw [← map_nsmul, ← ofMul_pow, ht, ofMul_one, map_zero]
  let q : QkPt D.toPre F k := qkMk hB 0 (torusPt D.toPre F (Additive.ofMul t)) (h0.trans (map_zero _).symm)
  have hq : IsTor t q.g := (isTor_iff _ _).2 (isTorusPtF_torusPt t)
  obtain ⟨q', e₁, e₂⟩ := key E' hE' k hk q (f q) ((hf.1 _ _).2 rfl) (a' q.g) ((ha' _ _).2 rfl)
  have hq' : IsTor (t.comp (AddMonoidHom.toMultiplicative E'.h)) q'.g :=
    (ec E' E' E').2.2.1 t q.g q'.g hq ((ha' _ _).2 e₁)
  have hq0 : q'.y = 0 := by
    refine inj _ _ (0 : GtPtF D.toPre F) ((isIota_iff_eq hB _ _).2 ?_) ((isIota_iff_eq hB _ _).2 (map_zero _).symm)
    rw [← qk_nsmul hB q', e₁, ← map_nsmul]
    exact ((congrArg a' h0).trans (map_zero _)).symm
  have w₁ := (hf.2.2.2.2 _ _ _).1 (weilQkIs_swap ((wp q p').2 t rfl hq))
  rw [hpp', weilIs_comp_iff_of_rosatiAdj hL _ A E.aA E'.aA E.homA E'.homA ros F _ k _ _ (tor p) (tor q),
    (hf.1 _ _).1 e₂] at w₁
  have w₂ := weilQkIs_swap ((hf.2.2.2.2 _ _ _).2 w₁)
  rw [inv_inv] at w₂
  exact (wp q' p).1.unique w₂ ((wp q' p).2 _ hq0 hq')

end GlobalTheory.KeyIota
end
