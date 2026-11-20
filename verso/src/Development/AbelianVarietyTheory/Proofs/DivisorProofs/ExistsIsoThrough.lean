import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniversalBasisMoveBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsTorsFrameOfSymLift
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedFibreThroughIso
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaExtend
open GlobalTheory.ThetaPtMove GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift

section Root
variable {X T Y : Scheme.{0}} [IsIntegral T] {f : Y ⟶ T} {y : Y}

/- English proof (translation)
Rewrite `h` using `[gs_eq f y W hW, gs_eq f y W hW, ← sub_eq_zero, ← map_sub, ← map_sub]`. Assume the negation of the conclusion as `h0`. Establish `hne : ((T.basicOpen (a - b) : T.Opens) : Set T).Nonempty`. Rewrite using `[Set.nonempty_iff_ne_empty]`. Conclude with `fun e => h0 (sub_eq_zero.1 ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective e)))`.

Establish `h1 : y ∈ f ⁻¹ᵁ T.basicOpen (a - b)` using `hg _ hne`. Rewrite `h1` using `[Scheme.preimage_basicOpen]`. Conclude with `((Y.mem_basicOpen _ y hW).1 h1).ne_zero h`.
-/
theorem eq_of_gs (hg : ∀ V : T.Opens, (V : Set T).Nonempty → f y ∈ V) {W : T.Opens} (hW : f y ∈ W) {a b : Γ(T, W)}
    (h : gs f y W a = gs f y W b) : a = b := by
  rw [gs_eq f y W hW, gs_eq f y W hW, ← sub_eq_zero, ← map_sub, ← map_sub] at h
  by_contra h0
  have hne : ((T.basicOpen (a - b) : T.Opens) : Set T).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => h0 (sub_eq_zero.1 ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective e)))
  have h1 : y ∈ f ⁻¹ᵁ T.basicOpen (a - b) := hg _ hne
  rw [Scheme.preimage_basicOpen] at h1
  exact ((Y.mem_basicOpen _ y hW).1 h1).ne_zero h

/- English proof (translation)
The claim follows from `unit_ext fun x hx => by have hW := hg W ⟨x, hx⟩ have e : a = b := Units.ext (eq_of_gs hg hW ((gs_unit f y W hW a).trans ((congrArg Units.val (h hW)).trans (gs_unit f y W hW b).symm))) rw [e]`.
-/
theorem eq_of_gm (hg : ∀ V : T.Opens, (V : Set T).Nonempty → f y ∈ V) {W : T.Opens} {a b : Γ(T, W)ˣ}
    (h : f y ∈ W → gm f y W a = gm f y W b) : a = b := unit_ext fun x hx => by
  have hW := hg W ⟨x, hx⟩
  have e : a = b := Units.ext (eq_of_gs hg hW
    ((gs_unit f y W hW a).trans ((congrArg Units.val (h hW)).trans (gs_unit f y W hW b).symm)))
  rw [e]

/- English proof (translation)
Distinguish the cases in `hW : f y ∈ W`. Use `swap`. Conclude with `⟨1, fun h => (hW h).elim⟩`. Use `haveI : Nonempty W := ⟨⟨_, hW⟩⟩`. Take `⟨a, b, hb, e⟩` from `hf t.val`.

Set `F : Γ(T, W) →+* Y.presheaf.stalk y` to `(Y.presheaf.germ (f ⁻¹ᵁ W) y hW).hom.comp (f.app W).hom`. Establish `hF : ∀ c, gs f y W c = F c` using `fun c => gs_eq f y W hW c`. Establish `inj : Function.Injective F` using `fun c d h => eq_of_gs hg hW (by rw [hF, hF, h])`. Rewrite `e` using `[← gs_res f y le_top hW a, ← gs_res f y le_top hW b, hF, hF]`. Establish `hb' : F ((T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom b) ≠ 0` using `fun h => hb (eq_of_gs (W := ⊤) hg trivial (by`.

Rewrite using `[← gs_res f y le_top hW b, hF, h, gs_eq f y ⊤ trivial, map_zero, map_zero]))`. Generalize the expression as in `(T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom a = a' at e`. Generalize the expression as in `(T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom b = b' at e hb'`. Establish `e₁ : t.val ^ q = F β.val`. Rewrite using `[← hF, gs_unit f y W hW, ← ht hW, Units.val_pow_eq_pow_val]`.

Establish `e₂ : a' ^ q = b' ^ q * β.val` using `inj (by rw [map_mul, map_pow, map_pow, ← e, ← e₁, mul_pow, mul_comm])`. Take `⟨s, rfl⟩` from `(IsIntegrallyClosed.pow_dvd_pow_iff hq).1 ⟨_, e₂⟩`. Establish `e₃ : F s = t.val`. Rewrite `e` using `[map_mul, mul_comm]`. Conclude with `(mul_left_cancel₀ hb' e).symm`.

Establish `e₄ : s ^ q = β.val` using `inj (by rw [map_pow, e₃, e₁])`. Establish `hs : IsUnit s` using `(isUnit_pow_iff hq).1 (e₄ ▸ β.isUnit)`. Conclude with `⟨hs.unit, fun _ => Units.ext ((gs_unit f y W hW _).symm.trans ((hF _).trans e₃))⟩`.
-/
theorem exists_unit_root [GlobalTheory.IsNormalScheme T] (hg : ∀ V : T.Opens, (V : Set T).Nonempty → f y ∈ V)
    (hf : ∀ t : Y.presheaf.stalk y, ∃ a b : Γ(T, ⊤), b ≠ 0 ∧ t * gs f y ⊤ b = gs f y ⊤ a) [IsDomain (Y.presheaf.stalk y)]
    {W : T.Opens} (β : Γ(T, W)ˣ) {q : ℕ} (hq : q ≠ 0) (t : (Y.presheaf.stalk y)ˣ)
    (ht : f y ∈ W → t ^ q = gm f y W β) : ∃ s : Γ(T, W)ˣ, f y ∈ W → gm f y W s = t := by
  by_cases hW : f y ∈ W
  swap
  · exact ⟨1, fun h => (hW h).elim⟩
  haveI : Nonempty W := ⟨⟨_, hW⟩⟩
  obtain ⟨a, b, hb, e⟩ := hf t.val
  let F : Γ(T, W) →+* Y.presheaf.stalk y := (Y.presheaf.germ (f ⁻¹ᵁ W) y hW).hom.comp (f.app W).hom
  have hF : ∀ c, gs f y W c = F c := fun c => gs_eq f y W hW c
  have inj : Function.Injective F := fun c d h => eq_of_gs hg hW (by rw [hF, hF, h])
  rw [← gs_res f y le_top hW a, ← gs_res f y le_top hW b, hF, hF] at e
  have hb' : F ((T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom b) ≠ 0 := fun h => hb (eq_of_gs (W := ⊤) hg trivial (by
    rw [← gs_res f y le_top hW b, hF, h, gs_eq f y ⊤ trivial, map_zero, map_zero]))
  generalize (T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom a = a' at e
  generalize (T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom b = b' at e hb'
  have e₁ : t.val ^ q = F β.val := by
    rw [← hF, gs_unit f y W hW, ← ht hW, Units.val_pow_eq_pow_val]
  have e₂ : a' ^ q = b' ^ q * β.val := inj (by rw [map_mul, map_pow, map_pow, ← e, ← e₁, mul_pow, mul_comm])
  obtain ⟨s, rfl⟩ := (IsIntegrallyClosed.pow_dvd_pow_iff hq).1 ⟨_, e₂⟩
  have e₃ : F s = t.val := by
    rw [map_mul, mul_comm] at e
    exact (mul_left_cancel₀ hb' e).symm
  have e₄ : s ^ q = β.val := inj (by rw [map_pow, e₃, e₁])
  have hs : IsUnit s := (isUnit_pow_iff hq).1 (e₄ ▸ β.isUnit)
  exact ⟨hs.unit, fun _ => Units.ext ((gs_unit f y W hW _).symm.trans ((hF _).trans e₃))⟩

/- English proof (translation)
Establish `m₀` using `hJ.mem (fun _ : Fin 1 => x) f`. Establish `tr : ∀ j j', trF (L` using `L) (fun _ : Fin 1 => x) (fun _ => 1) f y j j' ^ q = trF (fun _ : Fin 1 => x) (fun _ => (q : ℤ)) f y j j' := fun j j' => by`. Rewrite using `[trF, trF, Fin.prod_univ_one, Fin.prod_univ_one, zpow_one, zpow_natCast]`. Establish `h₁ : ∀ j, f y ∈ LB.wchart L (fun _ : Fin 1 => x) j → (trF (fun _ : Fin 1 => x) (fun _ => 1) f y j (fun _ => J (f ≫ x)) * t) ^ q = gm f y (LB.wchart L (fun _ : Fin 1 => x) j) (β.s j)` using `fun j hj => by`. Rewrite using `[mul_pow, tr, ht]`.

Conclude with `(gen_trans hβ f y hj m₀).symm`. Use `choose s hs using fun j => exists_unit_root hg hf (W := LB.wchart L (fun _ : Fin 1 => x) j) (β.s j) hq _ (h₁ j)`. Establish `e : ∀ j, s j ^ q = β.s j` using `fun j => eq_of_gm hg fun hj => by rw [map_pow, hs j hj, h₁ j hj]`. Use `⟨⟨s⟩, fun i j => eq_of_gm hg fun h => ?_, (hs _ m₀).trans ?_, fun Z r z J' => ?_⟩` and prove the remaining obligations. Use `(gm_res f y _ h _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linComb L _ _ f y i j h.1 h.2) (gm_res f y _ h _))).symm)` and prove the remaining obligations.

Use `(hs i h.1).trans (Eq.trans ?_ (congrArg _ (hs j h.2)).symm)` and prove the remaining obligations. Rewrite using `[← trF_trans hL _ _ f y h.1 h.2 m₀, _root_.mul_assoc]`. Both sides reduce to the same expression. Rewrite using `[mul_eq_left.1 (trF_trans hL _ _ f y m₀ m₀ m₀), _root_.one_mul]`. Conclude with `(map_pow _ _ _).symm.trans (congrArg _ (e _))`.
-/
theorem exists_gen_root [GlobalTheory.IsNormalScheme T] (hg : ∀ V : T.Opens, (V : Set T).Nonempty → f y ∈ V)
    (hf : ∀ t : Y.presheaf.stalk y, ∃ a b : Γ(T, ⊤), b ≠ 0 ∧ t * gs f y ⊤ b = gs f y ⊤ a) [IsDomain (Y.presheaf.stalk y)]
    {L : LB X} (hL : L.IsLB) (x : T ⟶ X) {q : ℕ} (hq : q ≠ 0)
    (β : LB.Gen (LB.LinComb L (fun _ : Fin 1 => x) (fun _ => (q : ℤ)))) (hβ : β.IsGen) {J} (hJ : Good L y J)
    (t : (Y.presheaf.stalk y)ˣ) (ht : t ^ q = val β f y J) :
    ∃ τ : LB.Gen (LB.LinComb L (fun _ : Fin 1 => x) (fun _ => 1)), τ.IsGen ∧ val τ f y J = t ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) J', val τ r z J' ^ q = val β r z J' := by
  have m₀ := hJ.mem (fun _ : Fin 1 => x) f
  have tr : ∀ j j', trF (L := L) (fun _ : Fin 1 => x) (fun _ => 1) f y j j' ^ q =
      trF (fun _ : Fin 1 => x) (fun _ => (q : ℤ)) f y j j' := fun j j' => by
    rw [trF, trF, Fin.prod_univ_one, Fin.prod_univ_one, zpow_one, zpow_natCast]
  have h₁ : ∀ j, f y ∈ LB.wchart L (fun _ : Fin 1 => x) j →
      (trF (fun _ : Fin 1 => x) (fun _ => 1) f y j (fun _ => J (f ≫ x)) * t) ^ q =
        gm f y (LB.wchart L (fun _ : Fin 1 => x) j) (β.s j) := fun j hj => by
    rw [mul_pow, tr, ht]
    exact (gen_trans hβ f y hj m₀).symm
  choose s hs using fun j => exists_unit_root hg hf (W := LB.wchart L (fun _ : Fin 1 => x) j) (β.s j) hq _ (h₁ j)
  have e : ∀ j, s j ^ q = β.s j := fun j => eq_of_gm hg fun hj => by rw [map_pow, hs j hj, h₁ j hj]
  refine ⟨⟨s⟩, fun i j => eq_of_gm hg fun h => ?_, (hs _ m₀).trans ?_, fun Z r z J' => ?_⟩
  · refine (gm_res f y _ h _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_linComb L _ _ f y i j h.1 h.2) (gm_res f y _ h _))).symm)
    refine (hs i h.1).trans (Eq.trans ?_ (congrArg _ (hs j h.2)).symm)
    rw [← trF_trans hL _ _ f y h.1 h.2 m₀, _root_.mul_assoc]
    rfl
  · rw [mul_eq_left.1 (trF_trans hL _ _ f y m₀ m₀ m₀), _root_.one_mul]
  · exact (map_pow _ _ _).symm.trans (congrArg _ (e _))

end Root

/- English proof (translation)
Establish `e : t.s = t'.s` using `funext fun j => unit_ext fun y hy => by`. Take `⟨J, hJ, e⟩` from `h y`. Conclude with `(gen_trans ht (𝟙 Y) y hy (hJ.mem φ _)).trans ((congrArg _ e).trans (gen_trans ht' (𝟙 Y) y hy (hJ.mem φ _)).symm)`. Consider the cases of `t`. Consider the cases of `t'`.

Consider the cases of `e`. Both sides reduce to the same expression.
-/
theorem gen_ext {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t t' : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (h : ∀ y, ∃ J, Good L y J ∧ val t (𝟙 Y) y J = val t' (𝟙 Y) y J) : t = t' := by
  have e : t.s = t'.s := funext fun j => unit_ext fun y hy => by
    obtain ⟨J, hJ, e⟩ := h y
    exact (gen_trans ht (𝟙 Y) y hy (hJ.mem φ _)).trans ((congrArg _ e).trans (gen_trans ht' (𝟙 Y) y hy (hJ.mem φ _)).symm)
  cases t; cases t'; cases e; rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `V ⟨p, hp⟩`. Use `Specializes.mem_open ?_ V.isOpen hp` and prove the remaining obligations. Use `(PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_` and prove the remaining obligations. Establish `h : φ a ∈ y.asIdeal` using `ha`.

Use `y.isPrime` as an intermediate fact. Rewrite `h` using `[Ideal.eq_bot_of_prime y.asIdeal, Ideal.mem_bot, map_eq_zero_iff φ hφ]`. Conclude with `h ▸ zero_mem _`. Introduce `t`. Take `⟨U, hU, c, rfl⟩` from `(Sp Ω).presheaf.germ_exist t`.

Take `rfl : U = ⊤` from `eq_top_iff.2 fun z _ => by rwa [Subsingleton.elim z y]`. Take `⟨c, rfl⟩` from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv).2 c`. Establish `key : ∃ a b : R, b ≠ 0 ∧ c * φ b = φ a`. Take `⟨a, b, e⟩` from `frac c`. Distinguish the cases in `hb : b = 0`.

Conclude with `⟨0, 1, fun h => one_ne_zero (((map_one φ).symm.trans (congrArg φ h)).trans (map_zero φ)), by rw [e, hb]; simp⟩`. Conclude with `⟨a, b, hb, by rw [e, div_mul_cancel₀ _ ((map_ne_zero_iff φ hφ).2 hb)]⟩`. Take `⟨a, b, hb, e⟩` from `key`. Use `⟨fn a, fn b, fun h => hb (ThetaReal.fn_injective (h.trans (map_zero _).symm)), ?_⟩` and prove the remaining obligations. Rewrite using `[FrameMove.gs_spMap, FrameMove.gs_spMap, ← e, map_mul, gs_mul (𝟙 _) y ⊤ trivial]`.

Conclude with `congrArg (· * _) (gs_eq (𝟙 _) y ⊤ trivial _).symm`.
-/
theorem generic_spMap {R Ω : Type} [CommRing R] [Field Ω] (φ : R →+* Ω) (hφ : Function.Injective φ)
    (frac : ∀ x : Ω, ∃ a b : R, x = φ a / φ b) (y : Sp Ω) :
    (∀ V : (Sp R).Opens, (V : Set (Sp R)).Nonempty → spMap φ y ∈ V) ∧
    (∀ t : (Sp Ω).presheaf.stalk y, ∃ a b : Γ(Sp R, ⊤), b ≠ 0 ∧ t * gs (spMap φ) y ⊤ b = gs (spMap φ) y ⊤ a) := by
  constructor
  · rintro V ⟨p, hp⟩
    refine Specializes.mem_open ?_ V.isOpen hp
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_
    have h : φ a ∈ y.asIdeal := ha
    have := y.isPrime
    rw [Ideal.eq_bot_of_prime y.asIdeal, Ideal.mem_bot, map_eq_zero_iff φ hφ] at h
    exact h ▸ zero_mem _
  · intro t
    obtain ⟨U, hU, c, rfl⟩ := (Sp Ω).presheaf.germ_exist t
    obtain rfl : U = ⊤ := eq_top_iff.2 fun z _ => by rwa [Subsingleton.elim z y]
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv).2 c
    have key : ∃ a b : R, b ≠ 0 ∧ c * φ b = φ a := by
      obtain ⟨a, b, e⟩ := frac c
      by_cases hb : b = 0
      · exact ⟨0, 1, fun h => one_ne_zero (((map_one φ).symm.trans (congrArg φ h)).trans (map_zero φ)),
          by rw [e, hb]; simp⟩
      · exact ⟨a, b, hb, by rw [e, div_mul_cancel₀ _ ((map_ne_zero_iff φ hφ).2 hb)]⟩
    obtain ⟨a, b, hb, e⟩ := key
    refine ⟨fn a, fn b, fun h => hb (ThetaReal.fn_injective (h.trans (map_zero _).symm)), ?_⟩
    rw [FrameMove.gs_spMap, FrameMove.gs_spMap, ← e, map_mul, gs_mul (𝟙 _) y ⊤ trivial]
    exact congrArg (· * _) (gs_eq (𝟙 _) y ⊤ trivial _).symm

/- English proof (translation)
Take `⟨σ, rfl⟩` from `Spec.map_surjective σ`. Establish `e : CommRingCat.ofHom φ ≫ σ = CommRingCat.ofHom φ` using `Spec.map_injective ((Spec.map_comp _ _).trans h)`. Establish `e' : ∀ a, σ.hom (φ a) = φ a` using `fun a => congrArg (fun q => q.hom a) e`. Establish `: σ = 𝟙 _`. Use extensionality with `x`.

Take `⟨a, b, rfl⟩` from `frac x`. Express the relevant statement in the definitionally equal form `σ.hom (φ a / φ b) = φ a / φ b`. Rewrite using `[map_div₀, e', e']`. Rewrite using `[this, Spec.map_id]`.
-/
theorem eq_id_of_comp {R Ω : Type} [CommRing R] [Field Ω] (φ : R →+* Ω)
    (frac : ∀ x : Ω, ∃ a b : R, x = φ a / φ b) (σ : Sp Ω ⟶ Sp Ω) (h : σ ≫ spMap φ = spMap φ) : σ = 𝟙 _ := by
  obtain ⟨σ, rfl⟩ := Spec.map_surjective σ
  have e : CommRingCat.ofHom φ ≫ σ = CommRingCat.ofHom φ := Spec.map_injective ((Spec.map_comp _ _).trans h)
  have e' : ∀ a, σ.hom (φ a) = φ a := fun a => congrArg (fun q => q.hom a) e
  have : σ = 𝟙 _ := by
    ext x
    obtain ⟨a, b, rfl⟩ := frac x
    change σ.hom (φ a / φ b) = φ a / φ b
    rw [map_div₀, e', e']
  rw [this, Spec.map_id]

/- English proof (translation)
Take `⟨w, hw⟩` from `lb`. Take `⟨r₁, h₁, H⟩` from `exists_gen_through (K := PUnit) (φ' := fun _ => eSec P'.A) (φ := fun _ => eSec P.A) (ε := fun _ => 1) (h := f) hw P.isLB P'.isLB (fun _ => PolBaseChange.eSec_comm gp) rig hr`. Take `⟨c, hc⟩` from `exists_ratio P'.isLB rfl r₁ rig' h₁ hr'`. Set `w' : LB.Iso P'.L (P.L.pull φ)` to `⟨fun p => w.s p * res le_top (pullU P'.A.hom ⊤ c)⟩`. Use `⟨w', fun i j => unit_ext fun y hy => ?_, fun Z r z J J' hJ hJ' => ?_⟩` and prove the remaining obligations.

Establish `e` using `congrArg (gm (𝟙 _) y _) (hw i j)`. Rewrite `e` using `[map_mul, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy]`. Rewrite using `[gm_res (𝟙 _) y _ hy, map_mul (gm (𝟙 _) y _) (LB.g _ i j), gm_res (𝟙 _) y _ hy]`. Use `(map_mul _ _ _).trans (Eq.trans ?_ (congrArg _ (map_mul _ _ _)).symm)` and prove the remaining obligations. Rewrite using `[e, _root_.mul_assoc]`.

Conclude with `congrArg (fun q => _ * (_ * q)) ((gm_res (𝟙 _) y _ hy.1 _).trans (gm_res (𝟙 _) y _ hy.2 _).symm)`. Establish `m : (r ≫ eSec P'.A) z ∈ (P.L.pull φ).U (fun _ => J ((r ≫ eSec P'.A) ≫ φ)) ⊓ P'.L.U (J' (r ≫ eSec P'.A))` using `⟨mem_pull.2 (hJ _), hJ' _⟩`. Establish `e : wVal w' z J J' (r ≫ eSec P'.A) = wVal w z J J' (r ≫ eSec P'.A) * gm r z ⊤ c`. Use `(map_mul _ _ _).trans (congrArg _ ((gm_res _ _ _ m _).trans ((gm_pull _ _ z ⊤ trivial c).trans ?_)))` and prove the remaining obligations. Rewrite using `[Category.assoc, TorsFrame.eSec_hom, Category.comp_id]`.

Rewrite using `[H Z r z J J' hJ hJ', hc Z r z J' hJ', Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, e, _root_.mul_assoc]`.
-/
theorem exists_iso_through {S S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P' : PolAV S'} {φ : P'.A.left ⟶ P.A.left}
    (gp : IsGrpPullback P'.A P.A f φ) (lb : LBIso P'.L (P.L.pull φ)) {rig : LB.Gen (P.L.pull (eSec P.A))}
    {rig' : LB.Gen (P'.L.pull (eSec P'.A))} (hr : rig.IsGen) (hr' : rig'.IsGen) :
    ∃ w : LB.Iso P'.L (P.L.pull φ), w.IsGen ∧
      GenThrough w (fun _ : PUnit => eSec P'.A) (fun _ : PUnit => eSec P.A) (fun _ => 1) rig' rig f := by
  obtain ⟨w, hw⟩ := lb
  obtain ⟨r₁, h₁, H⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec P'.A) (φ := fun _ => eSec P.A)
    (ε := fun _ => 1) (h := f) hw P.isLB P'.isLB (fun _ => PolBaseChange.eSec_comm gp) rig hr
  obtain ⟨c, hc⟩ := exists_ratio P'.isLB rfl r₁ rig' h₁ hr'
  let w' : LB.Iso P'.L (P.L.pull φ) := ⟨fun p => w.s p * res le_top (pullU P'.A.hom ⊤ c)⟩
  refine ⟨w', fun i j => unit_ext fun y hy => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · have e := congrArg (gm (𝟙 _) y _) (hw i j)
    rw [map_mul, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy] at e
    rw [gm_res (𝟙 _) y _ hy, map_mul (gm (𝟙 _) y _) (LB.g _ i j), gm_res (𝟙 _) y _ hy]
    refine (map_mul _ _ _).trans (Eq.trans ?_ (congrArg _ (map_mul _ _ _)).symm)
    rw [e, _root_.mul_assoc]
    exact congrArg (fun q => _ * (_ * q)) ((gm_res (𝟙 _) y _ hy.1 _).trans (gm_res (𝟙 _) y _ hy.2 _).symm)
  · have m : (r ≫ eSec P'.A) z ∈ (P.L.pull φ).U (fun _ => J ((r ≫ eSec P'.A) ≫ φ)) ⊓ P'.L.U (J' (r ≫ eSec P'.A)) :=
      ⟨mem_pull.2 (hJ _), hJ' _⟩
    have e : wVal w' z J J' (r ≫ eSec P'.A) = wVal w z J J' (r ≫ eSec P'.A) * gm r z ⊤ c := by
      refine (map_mul _ _ _).trans (congrArg _ ((gm_res _ _ _ m _).trans ((gm_pull _ _ z ⊤ trivial c).trans ?_)))
      rw [Category.assoc, TorsFrame.eSec_hom, Category.comp_id]
    rw [H Z r z J J' hJ hJ', hc Z r z J' hJ', Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, e,
      _root_.mul_assoc]

/- English proof (translation)
Take `⟨c, hc⟩` from `SymLiftOdd.exists_const hL p e he hp (fun U _ h => (Fintype.prod_sum_type _).trans (by`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]))`. Use the proof step `(DVR.mulGen_isGen L _ _ _ _ u (LB.invGen L _ _ u') hu (DVR.invGen_isGen _ _ _ _ hu'))`. Use `gen_ext hu hu' fun y => ?_` and prove the remaining obligations. Take `⟨J, hJ⟩` from `exists_good' hL y`.

Establish `e1` using `hc _ (𝟙 _) y J hJ`. Establish `e2` using `hc _ ((𝟙 _ ≫ p) ≫ e) y J hJ`. Rewrite `e1`, `e2` using `[val_mul hJ, val_inv]`. Rewrite `e2` using `[h _ _ _ _ hJ, mul_inv_cancel, Category.assoc _ e, he, Category.comp_id]`. Conclude with `⟨J, hJ, mul_inv_eq_one.1 (e1.trans e2.symm)⟩`.
-/
theorem gen_eq_of_section {X Y S₀ : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ S₀) (z : Z) J, Good L z J → val u (r ≫ e) z J = val u' (r ≫ e) z J) : u = u' := by
  obtain ⟨c, hc⟩ := SymLiftOdd.exists_const hL p e he hp
    (fun U _ h => (Fintype.prod_sum_type _).trans (by
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]))
    (DVR.mulGen_isGen L _ _ _ _ u (LB.invGen L _ _ u') hu (DVR.invGen_isGen _ _ _ _ hu'))
  refine gen_ext hu hu' fun y => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e1 := hc _ (𝟙 _) y J hJ
  have e2 := hc _ ((𝟙 _ ≫ p) ≫ e) y J hJ
  rw [val_mul hJ, val_inv] at e1 e2
  rw [h _ _ _ _ hJ, mul_inv_cancel, Category.assoc _ e, he, Category.comp_id] at e2
  exact ⟨J, hJ, mul_inv_eq_one.1 (e1.trans e2.symm)⟩

open FrameMove in

/- English proof (translation)
Establish `zp : ∀ {U : Type} [CommGroup U] (u : U), u ^ ((n : ℤ) ^ 2) = u ^ (n ^ 2)` using `fun u => by`. Rewrite using `[← Nat.cast_pow, zpow_natCast]`. Establish `hr' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S₀)).left) (z : Z) J J', Good P.L z J → Good P₀.L z J' → rval rig (r ≫ f) z J = wVal w z J J' (r ≫ eSec P₀.A) * rval rig₀ r z J'` using `fun Z r z J J' hJ hJ' => (hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))`. Take `⟨hn₀, hτ₀, α₀, hα₀, hN₀, hc₀⟩` from `H`. Take `⟨α₁, h₁⟩` from `hLaw.mulPull S P n`.

Take `⟨α, hα, vα⟩` from `TorsFrame.exists_norm P.isLB hrig h₁`. Take `⟨α', hα', Hα⟩` from `exists_gen_through (φ' := ![𝟙 P₀.A.left, (mulA P₀.A n).left]) (h := φ) hw P.isLB P₀.isLB (fun k => by fin_cases k`. Conclude with `(Category.id_comp _).trans (Category.comp_id _).symm`. Conclude with `pow_comm gp (x := 𝟙 P.A) (x' := 𝟙 P₀.A) (h := φ) ((Category.id_comp _).trans (Category.comp_id _).symm) n) α hα`. Establish `Hα' : ∀ (Z : Scheme.{0}) (r : Z ⟶ P₀.A.left) (z : Z) J J', Good P.L z J → Good P₀.L z J' → val α (r ≫ φ) z J = wVal w z J J' r ^ (n ^ 2) * (wVal w z J J' (r ≫ (mulA P₀.A n).left))⁻¹ * val α' r z J'` using `fun Z r z J J' hJ hJ' => by`.

Rewrite using `[Hα Z r z J J' hJ hJ', Fin.prod_univ_two, ← zpow_natCast]`. Simplify using the standard rewrite rules. Take `rfl : α' = α₀` from `gen_eq_of_section P₀.isLB P₀.A.hom (eSec P₀.A) TorsFrame.eSec_hom (hLaw.globalFns _ _ P₀.isAb).2 hα' hα₀ fun Z r z J' hJ' => by`. Take `⟨J, hJ⟩` from `exists_good' P.isLB z`. Establish `a : val α₀ (r ≫ eSec P₀.A) z J' = rval rig₀ r z J' ^ ((n : ℤ) ^ 2) * (rval rig₀ r z J')⁻¹` using `(val_pull hJ' α₀ (eSec P₀.A) r).symm.trans ((val_corr hJ' hN₀ r).trans ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) (map_zpow _ _ _) (val_inv _ _))))`.

Establish `b` using `Hα' _ (r ≫ eSec P₀.A) z J J' hJ hJ'`. Establish `c` using `hr' _ r z J J' hJ hJ'`. Establish `d : val α ((r ≫ f) ≫ eSec P.A) z J = rval rig (r ≫ f) z J ^ (n ^ 2) * (rval rig (r ≫ f) z J)⁻¹` using `vα _ _ z J hJ`. Establish `e : (r ≫ eSec P₀.A) ≫ φ = (r ≫ f) ≫ eSec P.A`. Rewrite using `[Category.assoc, Category.assoc]`.

Conclude with `congrArg _ (PolBaseChange.eSec_comm gp)`. Rewrite `b` using `[e, d, c, Category.assoc r _ (mulA P₀.A n).left, eSec_mulA]`. Rewrite using `[a, zp]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Use `replace b := congrArg Additive.ofMul b`.

Simplify using `only [ofMul_mul, ofMul_inv, ofMul_pow] at b ⊢`. Take the linear combination `(norm := module) -b`. Take `⟨β, hβ, vβ⟩` from `exists_gen P.isLB (φ' := fun _ : Fin 1 => x.left) (ε' := fun _ => ((n ^ 2 : ℕ) : ℤ)) (fun U _ h => by`. Simplify using `only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, comp_mulA, hxn, TorsFrame.one_left, Category.comp_id]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_zpow]`. Use the proof step `module)`. Use the proof step `(LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α x.left) (rigT P.A P.L rig T 1))`. Use the proof step `(DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) (ThetaReal.NormMul.rigT_isGen hrig 1))`. Take `⟨J, hJ⟩` from `exists_good' P.isLB y`.

Take `⟨J', hJ'⟩` from `exists_good' P₀.isLB y`. Take `⟨τ, hτ, v₁, v₂⟩` from `exists_gen_root hg hf P.isLB x.left (pow_ne_zero 2 hn) β hβ hJ (wVal w y J J' x₀.left * val τ₀ (𝟙 _) y J') (by`. Establish `a : val τ₀ (𝟙 _) y J' ^ ((n : ℤ) ^ 2) = val α' (𝟙 _ ≫ x₀.left) y J' * rval rig₀ (𝟙 _ ≫ T₀.hom) y J' ^ (1 : ℤ)` using `(map_zpow _ _ _).symm.trans ((val_corr hJ' hc₀ (𝟙 _)).trans ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ' _ _ _) (val_rigT _ _ _ hJ'))))`. Establish `b` using `Hα' _ x₀.left y J J' hJ hJ'`. Establish `c : rval rig (T₀.hom ≫ f) y J = wVal w y J J' (1 : T₀ ⟶ P₀.A).left * rval rig₀ T₀.hom y J'` using `hr' _ T₀.hom y J J' hJ hJ'`.

Rewrite `b` using `[comp_mulA, hn₀, hx]`. Rewrite `a` using `[zp, Category.id_comp, Category.id_comp]`. Use `Eq.trans ?_ ((vβ _ h y J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_rigT _ _ _ hJ)))).symm` and prove the remaining obligations. Rewrite using `[mul_pow, a, b, base_comm gp hx, c]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]`. Use the proof step `module)`. Take `⟨τ₁, hτ₁, H₁⟩` from `exists_gen_through (φ' := fun _ : Fin 1 => x₀.left) (h := h) hw P.isLB P₀.isLB (fun _ => hx) τ hτ`. Take `rfl : τ₁ = τ₀` from `gen_ext hτ₁ hτ₀ fun z => by`. Take `rfl : y = z` from `Subsingleton.elim _ _`.

Use `H₁ _ (𝟙 _) y J J' hJ hJ'` as an intermediate fact. Rewrite `this` using `[Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp]`. Conclude with `⟨J', hJ', mul_left_cancel (this.symm.trans v₁)⟩`. Use `⟨τ, ⟨hxn, hτ, α, hα, corr_of_val P.isLB fun z J hJ => ?_, corr_of_val P.isLB fun z J hJ => ?_⟩, H₁⟩` and prove the remaining obligations. Use `(val_pull hJ _ _ _).trans ((vα _ _ z J hJ).trans (Eq.symm ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (val_inv _ _)))))` and prove the remaining obligations.

Rewrite using `[← Nat.cast_pow, zpow_natCast]`. Both sides reduce to the same expression. Use `Eq.trans ?_ ((v₂ _ _ z J).trans (vβ _ _ z J hJ))` and prove the remaining obligations. Conclude with `(map_zpow _ _ _).trans (by rw [← Nat.cast_pow, zpow_natCast]; rfl)`.
-/
theorem exists_frame_up (hLaw : Laws) {S S₀ : Scheme.{0}} [IsLocallyNoetherian S] {T : Over S} {T₀ : Over S₀}
    [IsIntegral T.left] [GlobalTheory.IsNormalScheme T.left] [Subsingleton T₀.left] {f : S₀ ⟶ S} {h : T₀.left ⟶ T.left}
    (y : T₀.left) (hg : ∀ V : T.left.Opens, (V : Set T.left).Nonempty → h y ∈ V)
    (hf : ∀ t : T₀.left.presheaf.stalk y, ∃ a b : Γ(T.left, ⊤), b ≠ 0 ∧ t * gs h y ⊤ b = gs h y ⊤ a)
    [IsDomain (T₀.left.presheaf.stalk y)] {P : PolAV S} {P₀ : PolAV S₀} {φ : P₀.A.left ⟶ P.A.left}
    (gp : IsGrpPullback P₀.A P.A f φ) {w : LB.Iso P₀.L (P.L.pull φ)} (hw : w.IsGen)
    {rig : LB.Gen (P.L.pull (eSec P.A))} {rig₀ : LB.Gen (P₀.L.pull (eSec P₀.A))} (hrig : rig.IsGen)
    (hr : GenThrough w (fun _ : PUnit => eSec P₀.A) (fun _ : PUnit => eSec P.A) (fun _ => 1) rig₀ rig f)
    {x : T ⟶ P.A} {x₀ : T₀ ⟶ P₀.A} (hx : x₀.left ≫ φ = h ≫ x.left) {n : ℕ} (hn : n ≠ 0)
    (hxn : x ^ n = 1) {τ₀} (H : IsTorsFrame P₀ rig₀ n x₀ τ₀) :
    ∃ τ, IsTorsFrame P rig n x τ ∧
      GenThrough w (fun _ : Fin 1 => x₀.left) (fun _ : Fin 1 => x.left) (fun _ => 1) τ₀ τ h := by
  have zp : ∀ {U : Type} [CommGroup U] (u : U), u ^ ((n : ℤ) ^ 2) = u ^ (n ^ 2) := fun u => by
    rw [← Nat.cast_pow, zpow_natCast]
  have hr' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S₀)).left) (z : Z) J J', Good P.L z J → Good P₀.L z J' →
      rval rig (r ≫ f) z J = wVal w z J J' (r ≫ eSec P₀.A) * rval rig₀ r z J' := fun Z r z J J' hJ hJ' =>
    (hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))
  obtain ⟨hn₀, hτ₀, α₀, hα₀, hN₀, hc₀⟩ := H
  obtain ⟨α₁, h₁⟩ := hLaw.mulPull S P n
  obtain ⟨α, hα, vα⟩ := TorsFrame.exists_norm P.isLB hrig h₁
  obtain ⟨α', hα', Hα⟩ := exists_gen_through (φ' := ![𝟙 P₀.A.left, (mulA P₀.A n).left]) (h := φ) hw P.isLB P₀.isLB
    (fun k => by
      fin_cases k
      · exact (Category.id_comp _).trans (Category.comp_id _).symm
      · exact pow_comm gp (x := 𝟙 P.A) (x' := 𝟙 P₀.A) (h := φ)
          ((Category.id_comp _).trans (Category.comp_id _).symm) n) α hα
  have Hα' : ∀ (Z : Scheme.{0}) (r : Z ⟶ P₀.A.left) (z : Z) J J', Good P.L z J → Good P₀.L z J' →
      val α (r ≫ φ) z J = wVal w z J J' r ^ (n ^ 2) * (wVal w z J J' (r ≫ (mulA P₀.A n).left))⁻¹ *
        val α' r z J' := fun Z r z J J' hJ hJ' => by
    rw [Hα Z r z J J' hJ hJ', Fin.prod_univ_two, ← zpow_natCast]
    simp
  obtain rfl : α' = α₀ := gen_eq_of_section P₀.isLB P₀.A.hom (eSec P₀.A) TorsFrame.eSec_hom
    (hLaw.globalFns _ _ P₀.isAb).2 hα' hα₀ fun Z r z J' hJ' => by
      obtain ⟨J, hJ⟩ := exists_good' P.isLB z
      have a : val α₀ (r ≫ eSec P₀.A) z J' = rval rig₀ r z J' ^ ((n : ℤ) ^ 2) * (rval rig₀ r z J')⁻¹ :=
        (val_pull hJ' α₀ (eSec P₀.A) r).symm.trans ((val_corr hJ' hN₀ r).trans ((val_mul hJ' _ _ _).trans
          (congrArg₂ (· * ·) (map_zpow _ _ _) (val_inv _ _))))
      have b := Hα' _ (r ≫ eSec P₀.A) z J J' hJ hJ'
      have c := hr' _ r z J J' hJ hJ'
      have d : val α ((r ≫ f) ≫ eSec P.A) z J = rval rig (r ≫ f) z J ^ (n ^ 2) * (rval rig (r ≫ f) z J)⁻¹ :=
        vα _ _ z J hJ
      have e : (r ≫ eSec P₀.A) ≫ φ = (r ≫ f) ≫ eSec P.A := by
        rw [Category.assoc, Category.assoc]
        exact congrArg _ (PolBaseChange.eSec_comm gp)
      rw [e, d, c, Category.assoc r _ (mulA P₀.A n).left, eSec_mulA] at b
      rw [a, zp]
      apply Additive.ofMul.injective
      replace b := congrArg Additive.ofMul b
      simp only [ofMul_mul, ofMul_inv, ofMul_pow] at b ⊢
      linear_combination (norm := module) -b
  obtain ⟨β, hβ, vβ⟩ := exists_gen P.isLB (φ' := fun _ : Fin 1 => x.left) (ε' := fun _ => ((n ^ 2 : ℕ) : ℤ))
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, comp_mulA, hxn, TorsFrame.one_left, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α x.left) (rigT P.A P.L rig T 1))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) (ThetaReal.NormMul.rigT_isGen hrig 1))
  obtain ⟨J, hJ⟩ := exists_good' P.isLB y
  obtain ⟨J', hJ'⟩ := exists_good' P₀.isLB y
  obtain ⟨τ, hτ, v₁, v₂⟩ := exists_gen_root hg hf P.isLB x.left (pow_ne_zero 2 hn) β hβ hJ
    (wVal w y J J' x₀.left * val τ₀ (𝟙 _) y J') (by
      have a : val τ₀ (𝟙 _) y J' ^ ((n : ℤ) ^ 2) =
          val α' (𝟙 _ ≫ x₀.left) y J' * rval rig₀ (𝟙 _ ≫ T₀.hom) y J' ^ (1 : ℤ) :=
        (map_zpow _ _ _).symm.trans ((val_corr hJ' hc₀ (𝟙 _)).trans ((val_mul hJ' _ _ _).trans
          (congrArg₂ (· * ·) (val_pull hJ' _ _ _) (val_rigT _ _ _ hJ'))))
      have b := Hα' _ x₀.left y J J' hJ hJ'
      have c : rval rig (T₀.hom ≫ f) y J = wVal w y J J' (1 : T₀ ⟶ P₀.A).left * rval rig₀ T₀.hom y J' :=
        hr' _ T₀.hom y J J' hJ hJ'
      rw [comp_mulA, hn₀, hx] at b
      rw [zp, Category.id_comp, Category.id_comp] at a
      refine Eq.trans ?_ ((vβ _ h y J hJ).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_rigT _ _ _ hJ)))).symm
      rw [mul_pow, a, b, base_comm gp hx, c]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
      module)
  obtain ⟨τ₁, hτ₁, H₁⟩ := exists_gen_through (φ' := fun _ : Fin 1 => x₀.left) (h := h) hw P.isLB P₀.isLB
    (fun _ => hx) τ hτ
  obtain rfl : τ₁ = τ₀ := gen_ext hτ₁ hτ₀ fun z => by
    obtain rfl : y = z := Subsingleton.elim _ _
    have := H₁ _ (𝟙 _) y J J' hJ hJ'
    rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this
    exact ⟨J', hJ', mul_left_cancel (this.symm.trans v₁)⟩
  refine ⟨τ, ⟨hxn, hτ, α, hα, corr_of_val P.isLB fun z J hJ => ?_, corr_of_val P.isLB fun z J hJ => ?_⟩, H₁⟩
  · refine (val_pull hJ _ _ _).trans ((vα _ _ z J hJ).trans (Eq.symm ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (val_inv _ _)))))
    rw [← Nat.cast_pow, zpow_natCast]; rfl
  · refine Eq.trans ?_ ((v₂ _ _ z J).trans (vβ _ _ z J hJ))
    exact (map_zpow _ _ _).trans (by rw [← Nat.cast_pow, zpow_natCast]; rfl)

section Sections
open GlobalTheory.ThetaReal GlobalTheory.UnivBasisMove

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

/- English proof (translation)
Use `VVRank.isTwistPull_of_sv A hL θ'.isGen fun z J hJ => ?_` and prove the remaining obligations. Establish `e` using `val_corr hJ (SymLiftOdd.symLift_unique hG hA hL hq θ θ' H H') (𝟙 _)`. Use `(VVRank.sv_of_isTwistPull A h (𝟙 _) z hJ).trans (congrArg₂ (· * ·) (congrArg Units.val e) ?_)` and prove the remaining obligations. Rewrite using `[H.pt_eq, H'.pt_eq]`.
-/
theorem isActOf_congr (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {q : ℕ} (hq : Odd q) {x : T ⟶ A}
    {θ θ' : ThetaGrp A L k T} (H : SymLift A L k q x θ) (H' : SymLift A L k q x θ') {s s' : LB.Sec (LPow A L k T)}
    (h : IsActOf A L k θ s s') : IsActOf A L k θ' s s' := by
  refine VVRank.isTwistPull_of_sv A hL θ'.isGen fun z J hJ => ?_
  have e := val_corr hJ (SymLiftOdd.symLift_unique hG hA hL hq θ θ' H H') (𝟙 _)
  refine (VVRank.sv_of_isTwistPull A h (𝟙 _) z hJ).trans (congrArg₂ (· * ·) (congrArg Units.val e) ?_)
  rw [H.pt_eq, H'.pt_eq]

/- English proof (translation)
The claim follows from `fn_ext fun y _ => by obtain ⟨J, hJ⟩ := exists_good' hL y have a := (congrArg (fun q => ThetaAct.sv q (𝟙 _ ≫ (ptSecT A x).left) y J) e).trans (ThetaAct.sv_smul c _ _ y hJ) have b := (sv_of_isValueAt h' (𝟙 _) y hJ).symm.trans (a.trans (congrArg _ (sv_of_isValueAt h (𝟙 _) y hJ))) rw …`.
-/
theorem value_smul (hL : L.IsLB) {k : ℤ} {s s' : LB.Sec (LPow A L k T)} {x : T ⟶ A} {τ} {v v' c : Γ(T.left, ⊤)}
    (h : IsValueAt A L k s x τ v) (h' : IsValueAt A L k s' x τ v') (e : SecM.ofSec A s' = c • SecM.ofSec A s) :
    v' = c * v := fn_ext fun y _ => by
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have a := (congrArg (fun q => ThetaAct.sv q (𝟙 _ ≫ (ptSecT A x).left) y J) e).trans (ThetaAct.sv_smul c _ _ y hJ)
  have b := (sv_of_isValueAt h' (𝟙 _) y hJ).symm.trans (a.trans (congrArg _ (sv_of_isValueAt h (𝟙 _) y hJ)))
  rw [Category.assoc, ptSecT_fst, Category.comp_id, ← _root_.mul_assoc] at b
  exact ((Units.mul_left_inj _).1 b).trans (gs_mul (𝟙 _) y ⊤ trivial _ _).symm

/- English proof (translation)
The claim follows from `ThetaAct.sv_ext hL fun y J hJ => by have a := (congrArg (fun q => ThetaAct.sv q (𝟙 _ ≫ (lift (fst T A) m).left) y J) e).trans (ThetaAct.sv_smul c _ _ y hJ) rw [Category.assoc, ← Over.comp_left, lift_fst] at a refine (VVRank.sv_of_isTwistPull A h' (𝟙 _) y hJ).trans ((congrArg _ a) …`.
-/
theorem twistPull_smul (hL : L.IsLB) {m : T ⊗ A ⟶ A} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} {s t : LB.Sec (LPow A L b T)}
    {s' t' : LB.Sec (LPow A L a T)} (h : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α s s')
    (h' : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α t t') {c : Γ(T.left, ⊤)}
    (e : SecM.ofSec A t = c • SecM.ofSec A s) : SecM.ofSec A t' = c • SecM.ofSec A s' :=
  ThetaAct.sv_ext hL fun y J hJ => by
    have a := (congrArg (fun q => ThetaAct.sv q (𝟙 _ ≫ (lift (fst T A) m).left) y J) e).trans
      (ThetaAct.sv_smul c _ _ y hJ)
    rw [Category.assoc, ← Over.comp_left, lift_fst] at a
    refine (VVRank.sv_of_isTwistPull A h' (𝟙 _) y hJ).trans ((congrArg _ a).trans
      (Eq.trans ?_ (ThetaAct.sv_smul c _ _ y hJ).symm))
    exact (mul_left_comm _ _ _).trans (congrArg _ (VVRank.sv_of_isTwistPull A h (𝟙 _) y hJ).symm)

variable {S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P' : PolAV S'} {φ : P'.A.left ⟶ P.A.left}
  {hp : IsGrpPullback P'.A P.A f φ} {w : LB.Iso P'.L (P.L.pull φ)} {n : ℤ} {κ : Type}
  {τ : (baseOver S').left ⟶ T.left} {hτ : τ ≫ T.hom = (baseOver S').hom ≫ f}

/- English proof (translation)
Introduce `T' hT h`. Establish `hh : h.left = T'.hom` using `(Category.comp_id _).symm.trans (Over.w h)`. Set `h₀ : Over.mk (T'.hom ≫ f) ⟶ T` to `Over.homMk (h.left ≫ τ) (by`. Express the relevant statement in the definitionally equal form `(h.left ≫ τ) ≫ T.hom = T'.hom ≫ f`. Rewrite using `[Category.assoc, hτ, ← Category.assoc, Over.w h])`.

Establish `: IsAffine (Over.mk (T'.hom ≫ f)).left` using `hT`. Take `⟨c, hc⟩` from `hb₀ _ h₀`. Take `⟨E, hE⟩` from `exists_linearEquiv hp hw P.isLB P'.isLB n T'`. Use `⟨Module.Basis.map (R := Γ(T'.left, ⊤)) c E, fun i => ?_⟩` and prove the remaining obligations. Use `(hE (c i)).unique_down P.isLB P'.isLB ?_` and prove the remaining obligations.

Rewrite using `[hc]`. Conclude with `(hb i).pull _ _ h h₀ (Category.id_comp _)`.
-/
theorem univBasis_of_rel (hw : w.IsGen) {b₀ : κ → SecM P.A P.L n T} (hb₀ : UnivBasis P n b₀)
    {b : κ → SecM P'.A P'.L n (baseOver S')} (hb : ∀ i, Rel hp τ hτ w (b i) (b₀ i)) : UnivBasis P' n b := by
  intro T' hT h
  have hh : h.left = T'.hom := (Category.comp_id _).symm.trans (Over.w h)
  let h₀ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk (h.left ≫ τ) (by
    change (h.left ≫ τ) ≫ T.hom = T'.hom ≫ f
    rw [Category.assoc, hτ, ← Category.assoc, Over.w h])
  have : IsAffine (Over.mk (T'.hom ≫ f)).left := hT
  obtain ⟨c, hc⟩ := hb₀ _ h₀
  obtain ⟨E, hE⟩ := exists_linearEquiv hp hw P.isLB P'.isLB n T'
  refine ⟨Module.Basis.map (R := Γ(T'.left, ⊤)) c E, fun i => ?_⟩
  refine (hE (c i)).unique_down P.isLB P'.isLB ?_
  rw [hc]
  exact (hb i).pull _ _ h h₀ (Category.id_comp _)

/- English proof (translation)
The claim follows from `ThetaGeom.secRel_comb hp τ hτ (w := w) c (t := fun i => SecM.toSec _ (b i)) (t₀ := fun i => SecM.toSec _ (b₀ i)) hb (σ := SecM.toSec _ (∑ i, τ.appTop.hom (c i) • b i)) (σ₀ := SecM.toSec _ (∑ i, c i • b₀ i)) rfl rfl`.
-/
theorem rel_sum [Fintype κ] (c : κ → Γ(T.left, ⊤)) {b₀ : κ → SecM P.A P.L n T}
    {b : κ → SecM P'.A P'.L n (baseOver S')} (hb : ∀ i, Rel hp τ hτ w (b i) (b₀ i)) :
    Rel hp τ hτ w (∑ i, τ.appTop.hom (c i) • b i) (∑ i, c i • b₀ i) :=
  ThetaGeom.secRel_comb hp τ hτ (w := w) c (t := fun i => SecM.toSec _ (b i)) (t₀ := fun i => SecM.toSec _ (b₀ i)) hb
    (σ := SecM.toSec _ (∑ i, τ.appTop.hom (c i) • b i)) (σ₀ := SecM.toSec _ (∑ i, c i • b₀ i)) rfl rfl

/- English proof (translation)
Use `haveI : IsAffine (baseOver S').left := ‹IsAffine S'›`. Use `choose b hb using fun i => exists_rel hp τ hτ hw P.isLB P'.isLB (b₀ i)`. Take `⟨c, hc⟩` from `(univBasis_of_rel hw hb₀ hb).exists_basis`. Take `⟨c₀, hc₀⟩` from `hb₀.exists_basis`. Establish `key : ∀ x, Rel hp τ hτ w s x → c.equivFun s = fun i => τ.appTop.hom (c₀.equivFun x i)` using `fun x hx => by`.

Establish `h` using `rel_sum (c₀.equivFun x) hb`. Simplify using `only [← hc, ← hc₀] at h`. Rewrite `h` using `[c₀.sum_equivFun]`. Rewrite using `[hx.unique_down P.isLB P'.isLB h, ← c.equivFun_symm_apply, LinearEquiv.apply_symm_apply]`. Conclude with `c₀.equivFun.injective (funext fun i => hi (congrFun ((key x hx).symm.trans (key y hy)) i))`.
-/
theorem rel_inj [Fintype κ] [IsAffine S'] [IsAffine T.left] (hw : w.IsGen) {b₀ : κ → SecM P.A P.L n T}
    (hb₀ : UnivBasis P n b₀) (hi : Function.Injective τ.appTop.hom) {s : SecM P'.A P'.L n (baseOver S')}
    {x y : SecM P.A P.L n T} (hx : Rel hp τ hτ w s x) (hy : Rel hp τ hτ w s y) : x = y := by
  haveI : IsAffine (baseOver S').left := ‹IsAffine S'›
  choose b hb using fun i => exists_rel hp τ hτ hw P.isLB P'.isLB (b₀ i)
  obtain ⟨c, hc⟩ := (univBasis_of_rel hw hb₀ hb).exists_basis
  obtain ⟨c₀, hc₀⟩ := hb₀.exists_basis
  have key : ∀ x, Rel hp τ hτ w s x → c.equivFun s = fun i => τ.appTop.hom (c₀.equivFun x i) := fun x hx => by
    have h := rel_sum (c₀.equivFun x) hb
    simp only [← hc, ← hc₀] at h
    rw [c₀.sum_equivFun] at h
    rw [hx.unique_down P.isLB P'.isLB h, ← c.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  exact c₀.equivFun.injective (funext fun i => hi (congrFun ((key x hx).symm.trans (key y hy)) i))

end Sections

end GlobalTheory.ThetaExtend
