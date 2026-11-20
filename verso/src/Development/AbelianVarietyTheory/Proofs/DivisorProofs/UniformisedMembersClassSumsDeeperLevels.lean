import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupTowerLargeRatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupTowerBaseChangeMemberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingLabelAndShiftsPersistDeeperModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapStalkHomFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveRootMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeEquivTwoMembersSamePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulEighthPowerDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingThetaConstantsGenerateIntegralTorsionLabStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveLabelHomLatticeModLevelThetaMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGaloisFractionRingOfIsFractionRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeAutomorphismCongrOneModDetEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassSumOfAdicSumUnitSmulTermsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumMaximalIdealUniqueNoetherianLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeeperPointIntegralClosureGaloisStalkStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVector
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightZeroSectionUnitIntegralTorsionPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.Sep.DeepSums

/- English proof (translation)
Take `⟨w, hw⟩` from `h`. Use `⟨w, ?_⟩` and prove the remaining obligations. Establish `hd' : ((d : ℤ)) ≠ 0` using `by exact_mod_cast hd.ne'`. Apply `smul_right_injective X hd'` to reduce the goal to its premises. Simplify using `only [natCast_zsmul, smul_add]`.

Rewrite using `[hw, mul_comm, mul_nsmul]`. Use `congr 1`. Conclude with `smul_comm _ _ _`.
-/
theorem congMod_of_nsmul {X : Type} [AddCommGroup X] [Module.Free ℤ X] {L d : ℕ} (hd : 0 < d) {x y : X}
    (h : CongMod (L * d) (d • x) (d • y)) : CongMod L x y := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, ?_⟩
  have hd' : ((d : ℤ)) ≠ 0 := by exact_mod_cast hd.ne'
  apply smul_right_injective X hd'
  simp only [natCast_zsmul, smul_add]
  rw [hw, mul_comm, mul_nsmul]
  congr 1
  exact smul_comm _ _ _

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}

/- English proof (translation)
Take `⟨h1, -, h3, h4⟩` from `GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪`. Take `⟨mu, hmu⟩` from `h1 (a - a')`. Establish `hs` using `h4 _ _ _ _ hmu h'`. Rewrite `hs` using `[sub_add_cancel]`. Establish `hc2` using `(h3 a κ (mu + κ') h).1 hs`.

Use `(h3 _ mu 0 hmu).2 fun v => ?_` and prove the remaining obligations. Take `⟨w1, hw1⟩` from `hc2 v`. Take `⟨w2, hw2⟩` from `hc v`. Use `⟨-(w1 + w2), ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Pi.zero_apply] at hw1`.

Use `show (0 : X) = _`. Rewrite `hw1` using `[hw2]`. Establish `e : mu v = (X₁.S.r * X₁.S.N) • w1 + (X₁.S.r * X₁.S.N) • w2`. Establish `h5 : mu v + κ' v - κ' v = κ' v + (X₁.S.r * X₁.S.N) • w2 + (X₁.S.r * X₁.S.N) • w1 - κ' v` using `by rw [hw1]`. Rewrite `h5` using `[add_sub_cancel_right]`.

Rewrite using `[h5]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, smul_neg, smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem yy_sub_zero (𝔪 : UMem X₁ z₁ act V ev X t δ) {a a' : X₁.S.Gam} {κ κ' : Fin 8 → X} (h : 𝔪.YY a κ)
    (h' : 𝔪.YY a' κ') (hc : ∀ v, CongMod (X₁.S.r * X₁.S.N) (κ v) (κ' v)) : 𝔪.YY (a - a') 0 := by
  obtain ⟨h1, -, h3, h4⟩ := GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  obtain ⟨mu, hmu⟩ := h1 (a - a')
  have hs := h4 _ _ _ _ hmu h'
  rw [sub_add_cancel] at hs
  have hc2 := (h3 a κ (mu + κ') h).1 hs
  refine (h3 _ mu 0 hmu).2 fun v => ?_
  obtain ⟨w1, hw1⟩ := hc2 v
  obtain ⟨w2, hw2⟩ := hc v
  refine ⟨-(w1 + w2), ?_⟩
  simp only [Pi.add_apply, Pi.zero_apply] at hw1
  show (0 : X) = _
  rw [hw2] at hw1
  have e : mu v = (X₁.S.r * X₁.S.N) • w1 + (X₁.S.r * X₁.S.N) • w2 := by
    have h5 : mu v + κ' v - κ' v = κ' v + (X₁.S.r * X₁.S.N) • w2 + (X₁.S.r * X₁.S.N) • w1 - κ' v := by rw [hw1]
    rw [add_sub_cancel_right] at h5
    rw [h5]; abel
  rw [e, smul_neg, smul_add]; abel

/- English proof (translation)
Take `⟨-, -, -, h4⟩` from `GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪`. Proceed by induction on `d with`. Consider the case `zero`. Use `yy_sub_zero 𝔪 h h fun v => ⟨0, by simp⟩` as an intermediate fact. Rewrite `this` using `[sub_self]`.

Rewrite using `[zero_nsmul, zero_nsmul]` and apply the resulting hypothesis. Consider the case `succ d ih`. Rewrite using `[succ_nsmul, succ_nsmul]`. Conclude with `h4 _ _ _ _ ih h`.
-/
theorem yy_nsmul (𝔪 : UMem X₁ z₁ act V ev X t δ) {a : X₁.S.Gam} {κ : Fin 8 → X} (h : 𝔪.YY a κ) (d : ℕ) :
    𝔪.YY (d • a) (d • κ) := by
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  induction d with
  | zero =>
    have := yy_sub_zero 𝔪 h h fun v => ⟨0, by simp⟩
    rw [sub_self] at this
    rwa [zero_nsmul, zero_nsmul]
  | succ d ih =>
    rw [succ_nsmul, succ_nsmul]
    exact h4 _ _ _ _ ih h

end GlobalTheory.Poinc.Sep.DeepSums

namespace GlobalTheory.Poinc.Sep.DeepSums

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff f x]`.
-/
theorem comap_maximalIdeal_of_isLocalHom {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] : (maximalIdeal S).comap f = maximalIdeal R := by
  ext x
  simp only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff f x]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a ha => by have h1 : IsUnit (e a) := IsLocalHom.map_nonunit (f := f) _ ha simpa using h1.map e.symm.toRingHom⟩`.
-/
theorem isLocalHom_comp_equiv {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : S →+* T) [IsLocalHom f]
    (e : R ≃+* S) : IsLocalHom (f.comp e.toRingHom) :=
  ⟨fun a ha => by
    have h1 : IsUnit (e a) := IsLocalHom.map_nonunit (f := f) _ ha
    simpa using h1.map e.symm.toRingHom⟩

open Classical in

/- English proof (translation)
Introduce `g hg n hn hodd F Z z i _ hP hNZ hiz hD W hW hT X₁ z₁ act hact x₀ Φ lab _ hgeo`. Take `⟨hdiv, hrange, hmem⟩` from `hgeo`. Use `choose 𝔪 h𝔪 using hmem`. Introduce `y₀ N₀`. Take `⟨𝔗, hN₀⟩` from `GlobalTheory.T.exists_thetaSetup_tower_large_ratio g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT X₁ z₁ act hact N₀`.

Use `letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra`. Take `⟨-, hfr, -, -⟩` from `GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ z₁`. Use `haveI := hfr`. Use `letI algAL : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra`. Use `haveI := 𝔗.fd`.

Use `haveI := 𝔗.gal`. Take `⟨algFL, tower, hfd, hgal, hfix⟩` from `GlobalTheory.T.exists_finite_galois_fractionRing_fixing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ 𝔗.X₂.Ω₁ (fun _ => rfl)`. Take `⟨z₂, j₂, hz₂, hj₂, hmax, hint, hσ₂, hinj⟩` from `GlobalTheory.T.exists_deeperPoint_integralClosure_galois_stalk g n F W Z i X₁ act 𝔗 z₁`. Establish `hdiv₂ : ∀ w, 𝔗.p w = z₁ → 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) w` using `fun w hw => (GlobalTheory.T.dividing_label_and_shifts_persist_deeper_model g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT X₁ z₁ act hact 𝔗 w hw x₀ hdiv (Φ.V y₀) (Φ.ev y₀) (Φ.X y₀) (Φ.m y₀) (Φ.t y₀) (Φ.δ y₀) (𝔪 y₀)).1`. Establish `hlab : ∀ c, 𝔗.lam (lab c) ∈ 𝔗.X₂.S.HH 𝔗.X₂.M z₂` using `fun c => (GlobalTheory.T.dividing_label_and_shifts_persist_deeper_model g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hdiv (Φ.V y₀) (Φ.ev y₀) (Φ.X y₀) (Φ.m y₀) (Φ.t y₀) (Φ.δ y₀) (𝔪 y₀)).2 _ (by rw [← SetLike.mem_coe, ← hrange]; exact ⟨c, rfl⟩)`.

Take `⟨f₂, hf₂O, hf₂per, hf₂sum⟩` from `GlobalTheory.Poinc.Sep.ClassSumFun.exists_classSum_fun g n F W Z i 𝔗.X₂ z₂ 𝔗.act₂ (𝔗.lam x₀) (hdiv₂ z₂ hz₂)`. Take `⟨eps, hsbc⟩` from `GlobalTheory.T.exists_thetaSetupTower_baseChange_member g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hdiv`. Use `set L₂ := 𝔗.X₂.S.r * 𝔗.X₂.S.N with hL₂`. Establish `hL₂pos : 1 ≤ L₂` using `Nat.mul_pos 𝔗.X₂.S.r_pos (by have := 𝔗.X₂.S.N_ge; omega)`. Use `set ζ₂ : 𝔗.X₂.Ω₁ := algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ with hζ₂`.

Establish `hζO : ∀ w, ζ₂ ∈ 𝔗.X₂.M.O w` using `fun w => Subalgebra.algebraMap_mem _ _`. Establish `hsurj : ∀ x ∈ 𝔗.X₂.M.O z₂, ∃ h, 𝔗.X₂.M.stalkHom z₂ h = x` using `fun x hx =>`. Set `⟨h, hh⟩` to `(𝔗.X₂.M.stalkEquiv z₂).surjective ⟨x, hx⟩`. Use the proof step `⟨h, by rw [← RatModel.coe_stalkEquiv, hh]⟩`. Take `⟨zt, hzt⟩` from `hsurj ζ₂ (hζO z₂)`.

Establish `hztM : zt ^ (L₂ ^ 2) = 1` using `𝔗.X₂.M.stalkHom_injective z₂ (by`. Rewrite using `[map_pow, hzt, map_one, hζ₂, ← map_pow, 𝔗.X₂.S.prim.pow_eq_one, map_one])`. Use `set M := L₂ ^ 2 with hM`. Establish `hMpos : 1 ≤ M` using `Nat.one_le_pow _ _ hL₂pos`. Set `Fv : 𝔗.X₂.S.Gam → Φ.Q → 𝔗.X₂.Ω₁` to `fun a c => ζ₂ ^ ((M - 1) * eps (lab c)) * f₂ a (𝔗.lam (lab c))`.

Establish `hFB : ∀ a c, Fv a c ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁` using `fun a c => hint _ fun w hw => mul_mem (pow_mem (hζO w) _) (hf₂O _ _ w (hdiv₂ w hw))`. Establish `hext : ∀ y, ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : Φ.V y →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal (Φ.V y), (I.map io).comap io = I) ∧ 𝔗.Ext (Φ.ev y) io ev₂` using `fun y => GlobalTheory.T.exists_centred_pure_finite_extension_deeper_model g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT X₁ z₁ act hact 𝔗 z₂ hz₂ (Φ.V y) (Φ.ev y) (Φ.cn y) (Φ.ev_loc y) (𝔪 y).reg`. Use `choose V' iR iD iL io ev₂ hcn hioi hiof hiol hioI hExt using hext`. Establish `hmem₂` using `fun y => hsbc (Φ.V y) (Φ.ev y) (Φ.X y) (Φ.m y) (Φ.t y) (Φ.δ y) (𝔪 y) Φ.Q lab (Φ.term y) (h𝔪 y) (V' y) (io y) (hcn y) (hioi y) (hiof y)`. Use `choose 𝔪₂ h𝔪₂T h𝔪₂G using hmem₂`.

Set `M₂` to `fun y => 𝔪₂ y (ev₂ y) (hExt y)`. Establish `hyy` using `fun y => GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i 𝔗.X₂ z₂ 𝔗.act₂ (V' y) (ev₂ y) (Φ.X y) (Φ.m y) _ _ (M₂ y)`. Establish `hint₂` using `fun y => GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i 𝔗.X₂ z₂ 𝔗.act₂ (𝔗.lam x₀) (hdiv₂ z₂ hz₂) (V' y) (ev₂ y) (Φ.X y) (Φ.m y) _ _ (M₂ y)`. Establish `hK` using `fun y => GlobalTheory.T.exists_lattice_equiv_two_members_same_point g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT 𝔗.X₂ z₂ 𝔗.act₂ 𝔗.isAct (V' y₀) (ev₂ y₀) (Φ.X y₀) (Φ.m y₀) _ _ (M₂ y₀) (V' y) (ev₂ y) (Φ.X y) (Φ.m y) _ _ (M₂ y)`. Use `choose K hKlin hKyy using hK`.

Use `choose k₀ hk₀ using fun y => GlobalTheory.smul_eighth_power_diag _ _ (K y) (hKlin y)`. Set `kk : ∀ y, Φ.X y₀ ≃+ Φ.X y` to `fun y => if h : y₀ = y then h ▸ AddEquiv.refl (Φ.X y₀) else k₀ y`. Establish `hkk₀ : kk y₀ = AddEquiv.refl _` using `by simp [kk]`. Establish `hkk : ∀ y a κ, (M₂ y₀).YY a κ → (M₂ y).YY a (fun u => kk y (κ u))`. Introduce `y a κ h`.

Distinguish the cases in `hy : y₀ = y`. Substitute `hy` using the available equality. Rewrite using `[hkk₀]`. Conclude with `h`. Use `hKyy y a κ h` as an intermediate fact.

Rewrite `this` using `[hk₀ y]`. Simplify `this` using `[kk, hy]`. Use `choose aκ haκ using (hyy y₀).2.1`. Establish `hper : ∀ κ κ' c, (∀ v, CongMod L₂ (κ v) (κ' v)) → Fv (aκ κ) c = Fv (aκ κ') c`. Introduce `κ κ' c h`.

Establish `h0` using `yy_sub_zero (M₂ y₀) (haκ κ) (haκ κ') h`. Simplify using `only [Fv]`. Rewrite using `[hf₂per _ _ _ ((hint₂ y₀ _).2 h0)]`. Establish `hsmul : ∀ y (c : ℤ) (x : Φ.X y), (@HSMul.hSMul ℤ (Φ.X y) (Φ.X y) (@instHSMul ℤ (Φ.X y) (Φ.mod y).toSMul) c x) = c • x` using `fun y c x => int_smul_eq_zsmul (Φ.mod y) c x`. Use `⟨L₂, hN₀, hL₂pos, ⟨𝔗.d, 𝔗.lev⟩, fun y => (kk y).toIntLinearEquiv.toLinearMap, ?_, ?_, 𝔗.X₂.Ω₁, inferInstance, algFL, algAL, tower, hfd, hgal, (maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂, fun κ c => ⟨Fv (aκ κ) c, hFB _ _⟩, hmax, fun κ κ' c h => Subtype.ext (hper κ κ' c h) …` and prove the remaining obligations.

Use `show (kk y₀).toIntLinearEquiv.toLinearMap = LinearMap.id`. Rewrite using `[hkk₀]`. Both sides reduce to the same expression. Introduce `y`. Use `⟨fun c x => ⟨0, ?_⟩, (kk y).symm.toIntLinearEquiv, ?_⟩` and prove the remaining obligations.

Rewrite using `[hsmul, hsmul]`. Simplify using the standard rewrite rules. Establish `: ((kk y).symm.toIntLinearEquiv.toLinearMap ∘ₗ (kk y).toIntLinearEquiv.toLinearMap) = LinearMap.id`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite using `[this, LinearMap.det_id, sub_self]`. Conclude with `dvd_zero _`. Introduce `y`. Establish `hzu : IsUnit (ev₂ y zt)`. Conclude with `IsUnit.of_pow_eq_one (n := M) (by rw [← map_pow, hztM, map_one]) (by omega)`.

Use `⟨V' y, inferInstance, inferInstance, io y, (ev₂ y).comp j₂, hiof y, hiol y, hioI y, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Conclude with `(hExt y).2 x _ (by rw [hj₂]; rfl)`. Use `haveI := (hExt y).1`. Rewrite using `[← Ideal.comap_comap, comap_maximalIdeal_of_isLocalHom]`.

Introduce `κ c`. Take `⟨h, hh⟩` from `hsurj _ (hf₂O (aκ κ) (𝔗.lam (lab c)) z₂ (hdiv₂ z₂ hz₂))`. Establish `hs` using `hf₂sum (V' y) (ev₂ y) (Φ.X y) (Φ.m y) _ _ (M₂ y) Φ.Q (fun c => 𝔗.lam (lab c)) hlab (fun mu c => ev₂ y zt ^ eps (lab c) * io y (Φ.term y mu c)) (h𝔪₂T y (ev₂ y) (hExt y) zt hzt) c (aκ κ) _ (hkk y _ κ (haκ κ)) h hh`. Set `e : (V' y)ˣ` to `hzu.unit ^ eps (lab c)`. Establish `hcs` using `GlobalTheory.T.isClassSum_of_adicSum_unit_smul_terms ℤ id g 8 W _ Φ y L₂ hL₂pos (fun v => kk y (κ v)) c (V' y) (io y) e (ev₂ y h) (by convert hs using 3; simp [e])`.

Establish `hj : j₂ ⟨Fv (aκ κ) c, hFB _ _⟩ = zt ^ ((M - 1) * eps (lab c)) * h` using `𝔗.X₂.M.stalkHom_injective z₂ (by`. Rewrite using `[hj₂, map_mul, map_pow, hzt, hh])`. Establish `hval : ((ev₂ y).comp j₂) ⟨Fv (aκ κ) c, hFB _ _⟩ = ↑e⁻¹ * ev₂ y h`. Rewrite using `[RingHom.comp_apply, hj, map_mul, map_pow]`. Use `congr 1`.

Use `(Units.inv_eq_of_mul_eq_one_right ?_).symm` and prove the remaining obligations. Establish `hMe : eps (lab c) + (M - 1) * eps (lab c) = M * eps (lab c)`. Establish `h1 : M - 1 + 1 = M` using `by omega`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show (e : V' y) = ev₂ y zt ^ eps (lab c) by simp [e], ← pow_add, hMe, pow_mul, ← map_pow, hztM, map_one, one_pow]`.

Apply the tactic sequence `convert hcs using 1 <;> first | exact hval | rfl`. Introduce `σ hσ`. Set `σ' : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁` to `AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => hfix σ x)`. Take `⟨σ₂, hσ₂'⟩` from `hσ₂ σ' (fun b b' hb => by`. Use `hσ b b' hb` as an intermediate fact.

Simplify `this)` using `only [Ideal.mem_comap]`. Establish `hExtσ : ∀ {V V' : Type} [CommRing V] [CommRing V'] [IsLocalRing V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (e₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), 𝔗.Ext ev io e₂ → 𝔗.Ext ev io (e₂.comp σ₂.toRingHom)`. Introduce `V V' _ _ _ ev io e₂ he`. Use `haveI := he.1`. Use `⟨isLocalHom_comp_equiv e₂ σ₂, fun x x₂ hx => he.2 x (σ₂ x₂) ?_⟩` and prove the remaining obligations.

Rewrite using `[hσ₂', hx]`. Conclude with `σ'.commutes _`. Establish `hgl : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X} {V' : Type} [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (𝔫 : ∀ e₂ : 𝔗.X₂.M …`. Introduce `V _ _ _ ev X _ m t δ V' _ _ _ io 𝔫 hG e₂ h a mu`. Use `hG e₂ h _ _ σ' (fun x x' hx => ?_) (fun x => ⟨σ₂ x, hσ₂' x⟩) a mu` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply]`. Use `congr 1`. Conclude with `𝔗.X₂.M.stalkHom_injective z₂ (by show 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = _; rw [hσ₂', hx])`. Establish `hext₀` using `hExtσ (Φ.ev y₀) (io y₀) (ev₂ y₀) (hExt y₀)`. Take `⟨Kσ, hKσlin, hKσyy⟩` from `GlobalTheory.T.exists_lattice_equiv_two_members_same_point g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT 𝔗.X₂ z₂ 𝔗.act₂ 𝔗.isAct (V' y₀) (ev₂ y₀) (Φ.X y₀) (Φ.m y₀) _ _ (M₂ y₀) (V' y₀) ((ev₂ y₀).comp σ₂.toRingHom) (Φ.X y₀) (Φ.m y₀) _ _ (𝔪₂ y₀ ((ev₂ y₀).comp σ₂.toRingHom) hext₀)`.

Take `⟨gk, hgk⟩` from `GlobalTheory.smul_eighth_power_diag _ _ Kσ hKσlin`. Establish `hga : ∀ a κ, (M₂ y₀).YY a κ → (M₂ y₀).YY (𝔗.gl σ' a) (fun u => gk (κ u))` using `fun a κ h => by`. Use `hKσyy a κ h` as an intermediate fact. Rewrite `this` using `[hgk]`. Conclude with `(hgl (Φ.ev y₀) (io y₀) (𝔪₂ y₀) (h𝔪₂G y₀) (ev₂ y₀) (hExt y₀) a _).1 this`.

Establish `hL₁ : 3 ≤ X₁.S.r * X₁.S.N`. Take `⟨k, hk⟩` from `GlobalTheory.ZH.TestVal.odd_level X₁.ρ`. Use `Nat.mul_le_mul X₁.S.r_pos X₁.S.N_ge` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hd : 0 < 𝔗.d`.

Break down `Nat.eq_zero_or_pos 𝔗.d with h | h` into its components or cases. Establish `h' : L₂ = 0` using `by rw [hL₂, 𝔗.lev, h, mul_zero]`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hcong : ∀ x, CongMod (X₁.S.r * X₁.S.N) (gk x) x`.

Introduce `x`. Take `⟨a', ha'⟩` from `(hyy y₀).2.1 (fun _ => x)`. Establish `h1` using `yy_nsmul (M₂ y₀) ha' 𝔗.d`. Take `⟨a'', ha''⟩` from `𝔗.lam_range a'`. Rewrite `h1` using `[← ha'']`.

Establish `h2` using `hga _ _ h1`. Rewrite `h2` using `[𝔗.gl_lam]`. Establish `h3` using `((hyy y₀).2.2.1 _ _ _ h1).1 h2 0`. Simplify using `only [Pi.smul_apply, map_nsmul] at h3`. Conclude with `congMod_of_nsmul hd (by rw [← 𝔗.lev]; exact h3)`.

Establish `hdet : LinearMap.det (gk.toIntLinearEquiv : Φ.X y₀ →ₗ[ℤ] Φ.X y₀) = 1` using `GlobalTheory.T.lattice_automorphism_congr_one_mod_det_eq_one (Φ.X y₀) gk _ hL₁ hcong`. Establish `hFσ : ∀ a c, σ' (Fv a c) = Fv (𝔗.gl σ' a) c`. Take `⟨Vr, _, _, _, evr, Xr, _, mr, tr, δr, hevr, ⟨𝔪r⟩⟩` from `GlobalTheory.Poinc.Sep.exists_uMem_injective g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT X₁ z₁ act hact`. Take `⟨ur, hur, -, -⟩` from `GlobalTheory.T.exists_member_terms_integral_unit_shift g n F W Z i X₁ z₁ act x₀ hdiv Vr evr Xr mr tr δr 𝔪r Φ.Q lab hrange`. Take `⟨Vr', _, _, _, ior, evr₂, hcnr, hior, hiorf, -, -, hExtr⟩` from `GlobalTheory.T.exists_centred_pure_finite_extension_deeper_model g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT X₁ z₁ act hact 𝔗 z₂ hz₂ Vr evr 𝔪r.cn 𝔪r.loc 𝔪r.reg`.

Establish `hinjr : Function.Injective evr₂` using `hinj Vr evr Vr' ior evr₂ hevr hior hExtr`. Take `⟨𝔫, h𝔫T, h𝔫G⟩` from `hsbc Vr evr Xr mr tr δr 𝔪r Φ.Q lab _ hur Vr' ior hcnr hior hiorf`. Use `haveI : IsNoetherianRing Vr' := hcnr.1`. Introduce `a c`. Establish `hextr` using `hExtσ evr ior evr₂ hExtr`.

Take `⟨mu, hmu⟩` from `(GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i 𝔗.X₂ z₂ 𝔗.act₂ Vr' _ Xr mr _ _ (𝔫 _ hextr)).1 a`. Establish `hmu'` using `(hgl evr ior 𝔫 h𝔫G evr₂ hExtr a mu).1 hmu`. Take `⟨h, hh⟩` from `hsurj _ (hf₂O a (𝔗.lam (lab c)) z₂ (hdiv₂ z₂ hz₂))`. Take `⟨h', hh'⟩` from `hsurj _ (hf₂O (𝔗.gl σ' a) (𝔗.lam (lab c)) z₂ (hdiv₂ z₂ hz₂))`. Establish `s1` using `hf₂sum Vr' _ Xr mr _ _ (𝔫 _ hextr) Φ.Q (fun c => 𝔗.lam (lab c)) hlab _ (h𝔫T _ hextr zt hzt) c a mu hmu h hh`.

Establish `s2` using `hf₂sum Vr' _ Xr mr _ _ (𝔫 _ hExtr) Φ.Q (fun c => 𝔗.lam (lab c)) hlab _ (h𝔫T _ hExtr zt hzt) c (𝔗.gl σ' a) mu hmu' h' hh'`. Establish `key : ∀ (u : Vr'), u ^ M = 1 → ∀ (x : Vr'), u ^ ((M - 1) * eps (lab c)) • (u ^ eps (lab c) * x) = x`. Introduce `u hu x`. Establish `h1 : (M - 1) * eps (lab c) + eps (lab c) = M * eps (lab c)`. Establish `h2 : M - 1 + 1 = M` using `by omega`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_eq_mul, ← _root_.mul_assoc, ← pow_add, h1, pow_mul, hu, one_pow, _root_.one_mul]`. Establish `t1` using `GlobalTheory.Poinc.Sep.ClassSumFun.sumI_smul ((evr₂ (σ₂ zt)) ^ ((M - 1) * eps (lab c))) s1`. Establish `t2` using `GlobalTheory.Poinc.Sep.ClassSumFun.sumI_smul ((evr₂ zt) ^ ((M - 1) * eps (lab c))) s2`. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at t1`.

Establish `hu1 : (evr₂ (σ₂ zt)) ^ M = 1` using `by rw [← map_pow, ← map_pow, hztM, map_one, map_one]`. Establish `hu2 : (evr₂ zt) ^ M = 1` using `by rw [← map_pow, hztM, map_one]`. Simplify using `only [key _ hu1, key _ hu2] at t1 t2`. Establish `heq` using `GlobalTheory.T.adicSum_maximalIdeal_unique_noetherian_local Vr' _ _ _ _ t1 t2`. Establish `heq' : σ₂ (zt ^ ((M - 1) * eps (lab c)) * h) = zt ^ ((M - 1) * eps (lab c)) * h'` using `hinjr (by simpa only [map_mul, map_pow, smul_eq_mul] using heq)`.

Use `congrArg (𝔗.X₂.M.stalkHom z₂) heq'` as an intermediate fact. Rewrite `this` using `[hσ₂']`. Simplify using `only [map_mul, map_pow, hzt, hh, hh'] at this`. Simplify using `only [Fv, map_mul, map_pow]`. Conclude with `this`.

Use `⟨gk.toIntLinearEquiv.toLinearMap, fun b x => ⟨0, ?_⟩, ?_, hcong, fun κ c => ?_⟩` and prove the remaining obligations. Rewrite using `[hsmul, hsmul]`. Simplify using the standard rewrite rules. Rewrite using `[hdet, sub_self]`. Conclude with `dvd_zero _`.

Use `show σ (Fv (aκ κ) c) = Fv (aκ (fun v => gk (κ v))) c`. Establish `e1 : σ (Fv (aκ κ) c) = σ' (Fv (aκ κ) c)` using `rfl`. Rewrite using `[e1, hFσ]`. Simplify using `only [Fv]`. Rewrite using `[hf₂per _ _ _ ((hint₂ y₀ _).2 (yy_sub_zero (M₂ y₀) (hga _ _ (haκ κ)) (haκ _) fun v => ⟨0, (add_zero _).symm.trans (congrArg _ (smul_zero _).symm)⟩))]`.
-/
theorem classSums_deeper : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (x₀ : X₁.S.Gam) (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam) [IsDomain (X₁.M.Z.presheaf.stalk z₁)], IsGeo X₁ z₁ act x₀ Φ lab → Φ.ClassSums (X₁.S.r * X₁.S.N) := by
  intro g hg n hn hodd F Z z i _ hP hNZ hiz hD W hW hT X₁ z₁ act hact x₀ Φ lab _ hgeo
  obtain ⟨hdiv, hrange, hmem⟩ := hgeo
  choose 𝔪 h𝔪 using hmem
  intro y₀ N₀
  obtain ⟨𝔗, hN₀⟩ := GlobalTheory.T.exists_thetaSetup_tower_large_ratio g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT X₁ z₁ act hact N₀
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  obtain ⟨-, hfr, -, -⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ z₁
  haveI := hfr
  letI algAL : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ :=
    ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
  haveI := 𝔗.fd
  haveI := 𝔗.gal
  obtain ⟨algFL, tower, hfd, hgal, hfix⟩ :=
    GlobalTheory.T.exists_finite_galois_fractionRing_fixing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ 𝔗.X₂.Ω₁ (fun _ => rfl)
  obtain ⟨z₂, j₂, hz₂, hj₂, hmax, hint, hσ₂, hinj⟩ := GlobalTheory.T.exists_deeperPoint_integralClosure_galois_stalk g n F W Z i X₁ act 𝔗 z₁
  have hdiv₂ : ∀ w, 𝔗.p w = z₁ → 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) w := fun w hw =>
    (GlobalTheory.T.dividing_label_and_shifts_persist_deeper_model g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT X₁ z₁ act hact 𝔗 w hw x₀ hdiv (Φ.V y₀) (Φ.ev y₀)
      (Φ.X y₀) (Φ.m y₀) (Φ.t y₀) (Φ.δ y₀) (𝔪 y₀)).1
  have hlab : ∀ c, 𝔗.lam (lab c) ∈ 𝔗.X₂.S.HH 𝔗.X₂.M z₂ := fun c =>
    (GlobalTheory.T.dividing_label_and_shifts_persist_deeper_model g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hdiv (Φ.V y₀) (Φ.ev y₀)
      (Φ.X y₀) (Φ.m y₀) (Φ.t y₀) (Φ.δ y₀) (𝔪 y₀)).2 _ (by rw [← SetLike.mem_coe, ← hrange]; exact ⟨c, rfl⟩)
  obtain ⟨f₂, hf₂O, hf₂per, hf₂sum⟩ :=
    GlobalTheory.Poinc.Sep.ClassSumFun.exists_classSum_fun g n F W Z i 𝔗.X₂ z₂ 𝔗.act₂ (𝔗.lam x₀) (hdiv₂ z₂ hz₂)
  obtain ⟨eps, hsbc⟩ := GlobalTheory.T.exists_thetaSetupTower_baseChange_member g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hdiv

  set L₂ := 𝔗.X₂.S.r * 𝔗.X₂.S.N with hL₂
  have hL₂pos : 1 ≤ L₂ := Nat.mul_pos 𝔗.X₂.S.r_pos (by have := 𝔗.X₂.S.N_ge; omega)
  set ζ₂ : 𝔗.X₂.Ω₁ := algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ with hζ₂
  have hζO : ∀ w, ζ₂ ∈ 𝔗.X₂.M.O w := fun w => Subalgebra.algebraMap_mem _ _
  have hsurj : ∀ x ∈ 𝔗.X₂.M.O z₂, ∃ h, 𝔗.X₂.M.stalkHom z₂ h = x := fun x hx =>
    let ⟨h, hh⟩ := (𝔗.X₂.M.stalkEquiv z₂).surjective ⟨x, hx⟩
    ⟨h, by rw [← RatModel.coe_stalkEquiv, hh]⟩
  obtain ⟨zt, hzt⟩ := hsurj ζ₂ (hζO z₂)
  have hztM : zt ^ (L₂ ^ 2) = 1 := 𝔗.X₂.M.stalkHom_injective z₂ (by
    rw [map_pow, hzt, map_one, hζ₂, ← map_pow, 𝔗.X₂.S.prim.pow_eq_one, map_one])
  set M := L₂ ^ 2 with hM
  have hMpos : 1 ≤ M := Nat.one_le_pow _ _ hL₂pos
  let Fv : 𝔗.X₂.S.Gam → Φ.Q → 𝔗.X₂.Ω₁ := fun a c => ζ₂ ^ ((M - 1) * eps (lab c)) * f₂ a (𝔗.lam (lab c))
  have hFB : ∀ a c, Fv a c ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := fun a c =>
    hint _ fun w hw => mul_mem (pow_mem (hζO w) _) (hf₂O _ _ w (hdiv₂ w hw))

  have hext : ∀ y, ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : Φ.V y →+* V')
      (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧
        (∀ I : Ideal (Φ.V y), (I.map io).comap io = I) ∧ 𝔗.Ext (Φ.ev y) io ev₂ := fun y =>
    GlobalTheory.T.exists_centred_pure_finite_extension_deeper_model g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT X₁ z₁ act hact 𝔗 z₂ hz₂ (Φ.V y) (Φ.ev y) (Φ.cn y)
      (Φ.ev_loc y) (𝔪 y).reg
  choose V' iR iD iL io ev₂ hcn hioi hiof hiol hioI hExt using hext
  have hmem₂ := fun y => hsbc (Φ.V y) (Φ.ev y) (Φ.X y) (Φ.m y) (Φ.t y) (Φ.δ y) (𝔪 y) Φ.Q lab (Φ.term y) (h𝔪 y)
    (V' y) (io y) (hcn y) (hioi y) (hiof y)
  choose 𝔪₂ h𝔪₂T h𝔪₂G using hmem₂

  let M₂ := fun y => 𝔪₂ y (ev₂ y) (hExt y)
  have hyy := fun y => GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i 𝔗.X₂ z₂ 𝔗.act₂ (V' y) (ev₂ y) (Φ.X y) (Φ.m y) _ _ (M₂ y)
  have hint₂ := fun y => GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i 𝔗.X₂ z₂ 𝔗.act₂ (𝔗.lam x₀) (hdiv₂ z₂ hz₂) (V' y) (ev₂ y) (Φ.X y) (Φ.m y) _ _ (M₂ y)
  have hK := fun y => GlobalTheory.T.exists_lattice_equiv_two_members_same_point g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT 𝔗.X₂ z₂ 𝔗.act₂ 𝔗.isAct (V' y₀) (ev₂ y₀)
    (Φ.X y₀) (Φ.m y₀) _ _ (M₂ y₀) (V' y) (ev₂ y) (Φ.X y) (Φ.m y) _ _ (M₂ y)
  choose K hKlin hKyy using hK
  choose k₀ hk₀ using fun y => GlobalTheory.smul_eighth_power_diag _ _ (K y) (hKlin y)
  let kk : ∀ y, Φ.X y₀ ≃+ Φ.X y := fun y => if h : y₀ = y then h ▸ AddEquiv.refl (Φ.X y₀) else k₀ y
  have hkk₀ : kk y₀ = AddEquiv.refl _ := by simp [kk]
  have hkk : ∀ y a κ, (M₂ y₀).YY a κ → (M₂ y).YY a (fun u => kk y (κ u)) := by
    intro y a κ h
    by_cases hy : y₀ = y
    · subst hy
      rw [hkk₀]
      exact h
    · have := hKyy y a κ h
      rw [hk₀ y] at this
      simpa [kk, hy] using this
  choose aκ haκ using (hyy y₀).2.1
  have hper : ∀ κ κ' c, (∀ v, CongMod L₂ (κ v) (κ' v)) → Fv (aκ κ) c = Fv (aκ κ') c := by
    intro κ κ' c h
    have h0 := yy_sub_zero (M₂ y₀) (haκ κ) (haκ κ') h
    simp only [Fv]
    rw [hf₂per _ _ _ ((hint₂ y₀ _).2 h0)]

  have hsmul : ∀ y (c : ℤ) (x : Φ.X y), (@HSMul.hSMul ℤ (Φ.X y) (Φ.X y) (@instHSMul ℤ (Φ.X y) (Φ.mod y).toSMul) c x) = c • x :=
    fun y c x => int_smul_eq_zsmul (Φ.mod y) c x
  refine ⟨L₂, hN₀, hL₂pos, ⟨𝔗.d, 𝔗.lev⟩, fun y => (kk y).toIntLinearEquiv.toLinearMap, ?_, ?_,
    𝔗.X₂.Ω₁, inferInstance, algFL, algAL, tower, hfd, hgal, (maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂,
    fun κ c => ⟨Fv (aκ κ) c, hFB _ _⟩, hmax, fun κ κ' c h => Subtype.ext (hper κ κ' c h), ?_, ?_⟩
  · show (kk y₀).toIntLinearEquiv.toLinearMap = LinearMap.id
    rw [hkk₀]; rfl
  · intro y
    refine ⟨fun c x => ⟨0, ?_⟩, (kk y).symm.toIntLinearEquiv, ?_⟩
    · rw [hsmul, hsmul]
      simp
    · have : ((kk y).symm.toIntLinearEquiv.toLinearMap ∘ₗ (kk y).toIntLinearEquiv.toLinearMap) = LinearMap.id := by
        ext x; simp
      rw [this, LinearMap.det_id, sub_self]
      exact dvd_zero _
  · intro y
    have hzu : IsUnit (ev₂ y zt) := by
      exact IsUnit.of_pow_eq_one (n := M) (by rw [← map_pow, hztM, map_one]) (by omega)
    refine ⟨V' y, inferInstance, inferInstance, io y, (ev₂ y).comp j₂, hiof y, hiol y, hioI y, ?_, ?_, ?_⟩
    · ext x
      exact (hExt y).2 x _ (by rw [hj₂]; rfl)
    · haveI := (hExt y).1
      rw [← Ideal.comap_comap, comap_maximalIdeal_of_isLocalHom]
    · intro κ c
      obtain ⟨h, hh⟩ := hsurj _ (hf₂O (aκ κ) (𝔗.lam (lab c)) z₂ (hdiv₂ z₂ hz₂))
      have hs := hf₂sum (V' y) (ev₂ y) (Φ.X y) (Φ.m y) _ _ (M₂ y) Φ.Q (fun c => 𝔗.lam (lab c)) hlab
        (fun mu c => ev₂ y zt ^ eps (lab c) * io y (Φ.term y mu c)) (h𝔪₂T y (ev₂ y) (hExt y) zt hzt) c (aκ κ) _
        (hkk y _ κ (haκ κ)) h hh
      let e : (V' y)ˣ := hzu.unit ^ eps (lab c)
      have hcs := GlobalTheory.T.isClassSum_of_adicSum_unit_smul_terms ℤ id g 8 W _ Φ y L₂ hL₂pos (fun v => kk y (κ v)) c (V' y) (io y) e (ev₂ y h)
        (by convert hs using 3; simp [e])
      have hj : j₂ ⟨Fv (aκ κ) c, hFB _ _⟩ = zt ^ ((M - 1) * eps (lab c)) * h := 𝔗.X₂.M.stalkHom_injective z₂ (by
        rw [hj₂, map_mul, map_pow, hzt, hh])
      have hval : ((ev₂ y).comp j₂) ⟨Fv (aκ κ) c, hFB _ _⟩ = ↑e⁻¹ * ev₂ y h := by
        rw [RingHom.comp_apply, hj, map_mul, map_pow]
        congr 1
        refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
        have hMe : eps (lab c) + (M - 1) * eps (lab c) = M * eps (lab c) := by
          have h1 : M - 1 + 1 = M := by omega
          calc eps (lab c) + (M - 1) * eps (lab c) = (M - 1 + 1) * eps (lab c) := by ring
            _ = M * eps (lab c) := by rw [h1]
        rw [show (e : V' y) = ev₂ y zt ^ eps (lab c) by simp [e], ← pow_add, hMe, pow_mul, ← map_pow, hztM, map_one,
          one_pow]
      convert hcs using 1 <;> first | exact hval | rfl
  · intro σ hσ
    let σ' : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => hfix σ x)
    obtain ⟨σ₂, hσ₂'⟩ := hσ₂ σ' (fun b b' hb => by
      have := hσ b b' hb
      simpa only [Ideal.mem_comap] using this)
    have hExtσ : ∀ {V V' : Type} [CommRing V] [CommRing V'] [IsLocalRing V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V)
        (io : V →+* V') (e₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), 𝔗.Ext ev io e₂ →
        𝔗.Ext ev io (e₂.comp σ₂.toRingHom) := by
      intro V V' _ _ _ ev io e₂ he
      haveI := he.1
      refine ⟨isLocalHom_comp_equiv e₂ σ₂, fun x x₂ hx => he.2 x (σ₂ x₂) ?_⟩
      rw [hσ₂', hx]
      exact σ'.commutes _
    have hgl : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) {X : Type}
        [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
        {V' : Type} [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V')
        (𝔫 : ∀ e₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io e₂ →
          UMem 𝔗.X₂ z₂ 𝔗.act₂ V' e₂ X (fun k => io (t k)) δ),
        (∀ e₂ h e₂' h' (τ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁),
          (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = τ (𝔗.X₂.M.stalkHom z₂ x) → e₂' x = e₂ x') →
          (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = τ (𝔗.X₂.M.stalkHom z₂ x)) →
          ∀ a mu, (𝔫 e₂' h').YY a mu ↔ (𝔫 e₂ h).YY (𝔗.gl τ a) mu) →
        ∀ e₂ (h : 𝔗.Ext ev io e₂) a mu,
          (𝔫 (e₂.comp σ₂.toRingHom) (hExtσ ev io e₂ h)).YY a mu ↔ (𝔫 e₂ h).YY (𝔗.gl σ' a) mu := by
      intro V _ _ _ ev X _ m t δ V' _ _ _ io 𝔫 hG e₂ h a mu
      refine hG e₂ h _ _ σ' (fun x x' hx => ?_) (fun x => ⟨σ₂ x, hσ₂' x⟩) a mu
      simp only [RingHom.comp_apply]
      congr 1
      exact 𝔗.X₂.M.stalkHom_injective z₂ (by show 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = _; rw [hσ₂', hx])
    have hext₀ := hExtσ (Φ.ev y₀) (io y₀) (ev₂ y₀) (hExt y₀)
    obtain ⟨Kσ, hKσlin, hKσyy⟩ := GlobalTheory.T.exists_lattice_equiv_two_members_same_point g hg n hn hodd F Z z i hP hNZ hiz hD W hW hT 𝔗.X₂ z₂ 𝔗.act₂ 𝔗.isAct
      (V' y₀) (ev₂ y₀) (Φ.X y₀) (Φ.m y₀) _ _ (M₂ y₀) (V' y₀) ((ev₂ y₀).comp σ₂.toRingHom) (Φ.X y₀) (Φ.m y₀) _ _
      (𝔪₂ y₀ ((ev₂ y₀).comp σ₂.toRingHom) hext₀)
    obtain ⟨gk, hgk⟩ := GlobalTheory.smul_eighth_power_diag _ _ Kσ hKσlin
    have hga : ∀ a κ, (M₂ y₀).YY a κ → (M₂ y₀).YY (𝔗.gl σ' a) (fun u => gk (κ u)) := fun a κ h => by
      have := hKσyy a κ h
      rw [hgk] at this
      exact (hgl (Φ.ev y₀) (io y₀) (𝔪₂ y₀) (h𝔪₂G y₀) (ev₂ y₀) (hExt y₀) a _).1 this
    have hL₁ : 3 ≤ X₁.S.r * X₁.S.N := by
      obtain ⟨k, hk⟩ := GlobalTheory.ZH.TestVal.odd_level X₁.ρ
      have := Nat.mul_le_mul X₁.S.r_pos X₁.S.N_ge
      omega
    have hd : 0 < 𝔗.d := by
      rcases Nat.eq_zero_or_pos 𝔗.d with h | h
      · have h' : L₂ = 0 := by rw [hL₂, 𝔗.lev, h, mul_zero]
        omega
      · exact h
    have hcong : ∀ x, CongMod (X₁.S.r * X₁.S.N) (gk x) x := by
      intro x
      obtain ⟨a', ha'⟩ := (hyy y₀).2.1 (fun _ => x)
      have h1 := yy_nsmul (M₂ y₀) ha' 𝔗.d
      obtain ⟨a'', ha''⟩ := 𝔗.lam_range a'
      rw [← ha''] at h1
      have h2 := hga _ _ h1
      rw [𝔗.gl_lam] at h2
      have h3 := ((hyy y₀).2.2.1 _ _ _ h1).1 h2 0
      simp only [Pi.smul_apply, map_nsmul] at h3
      exact congMod_of_nsmul hd (by rw [← 𝔗.lev]; exact h3)
    have hdet : LinearMap.det (gk.toIntLinearEquiv : Φ.X y₀ →ₗ[ℤ] Φ.X y₀) = 1 := GlobalTheory.T.lattice_automorphism_congr_one_mod_det_eq_one (Φ.X y₀) gk _ hL₁ hcong
    have hFσ : ∀ a c, σ' (Fv a c) = Fv (𝔗.gl σ' a) c := by
      obtain ⟨Vr, _, _, _, evr, Xr, _, mr, tr, δr, hevr, ⟨𝔪r⟩⟩ := GlobalTheory.Poinc.Sep.exists_uMem_injective g hg n hn hodd F Z z i
        hP hNZ hiz hD W hW hT X₁ z₁ act hact
      obtain ⟨ur, hur, -, -⟩ := GlobalTheory.T.exists_member_terms_integral_unit_shift g n F W Z i X₁ z₁ act x₀ hdiv Vr evr Xr mr tr δr 𝔪r Φ.Q lab hrange
      obtain ⟨Vr', _, _, _, ior, evr₂, hcnr, hior, hiorf, -, -, hExtr⟩ := GlobalTheory.T.exists_centred_pure_finite_extension_deeper_model g hg n hn hodd F Z z i hP hNZ hiz
        hD W hW hT X₁ z₁ act hact 𝔗 z₂ hz₂ Vr evr 𝔪r.cn 𝔪r.loc 𝔪r.reg
      have hinjr : Function.Injective evr₂ := hinj Vr evr Vr' ior evr₂ hevr hior hExtr
      obtain ⟨𝔫, h𝔫T, h𝔫G⟩ := hsbc Vr evr Xr mr tr δr 𝔪r Φ.Q lab _ hur Vr' ior hcnr hior hiorf
      haveI : IsNoetherianRing Vr' := hcnr.1
      intro a c
      have hextr := hExtσ evr ior evr₂ hExtr
      obtain ⟨mu, hmu⟩ := (GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i 𝔗.X₂ z₂ 𝔗.act₂ Vr' _ Xr mr _ _ (𝔫 _ hextr)).1 a
      have hmu' := (hgl evr ior 𝔫 h𝔫G evr₂ hExtr a mu).1 hmu
      obtain ⟨h, hh⟩ := hsurj _ (hf₂O a (𝔗.lam (lab c)) z₂ (hdiv₂ z₂ hz₂))
      obtain ⟨h', hh'⟩ := hsurj _ (hf₂O (𝔗.gl σ' a) (𝔗.lam (lab c)) z₂ (hdiv₂ z₂ hz₂))
      have s1 := hf₂sum Vr' _ Xr mr _ _ (𝔫 _ hextr) Φ.Q (fun c => 𝔗.lam (lab c)) hlab _ (h𝔫T _ hextr zt hzt) c a mu
        hmu h hh
      have s2 := hf₂sum Vr' _ Xr mr _ _ (𝔫 _ hExtr) Φ.Q (fun c => 𝔗.lam (lab c)) hlab _ (h𝔫T _ hExtr zt hzt) c
        (𝔗.gl σ' a) mu hmu' h' hh'
      have key : ∀ (u : Vr'), u ^ M = 1 → ∀ (x : Vr'), u ^ ((M - 1) * eps (lab c)) • (u ^ eps (lab c) * x) = x := by
        intro u hu x
        have h1 : (M - 1) * eps (lab c) + eps (lab c) = M * eps (lab c) := by
          have h2 : M - 1 + 1 = M := by omega
          calc (M - 1) * eps (lab c) + eps (lab c) = (M - 1 + 1) * eps (lab c) := by ring
            _ = M * eps (lab c) := by rw [h2]
        rw [smul_eq_mul, ← _root_.mul_assoc, ← pow_add, h1, pow_mul, hu, one_pow, _root_.one_mul]
      have t1 := GlobalTheory.Poinc.Sep.ClassSumFun.sumI_smul ((evr₂ (σ₂ zt)) ^ ((M - 1) * eps (lab c))) s1
      have t2 := GlobalTheory.Poinc.Sep.ClassSumFun.sumI_smul ((evr₂ zt) ^ ((M - 1) * eps (lab c))) s2
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at t1
      have hu1 : (evr₂ (σ₂ zt)) ^ M = 1 := by rw [← map_pow, ← map_pow, hztM, map_one, map_one]
      have hu2 : (evr₂ zt) ^ M = 1 := by rw [← map_pow, hztM, map_one]
      simp only [key _ hu1, key _ hu2] at t1 t2
      have heq := GlobalTheory.T.adicSum_maximalIdeal_unique_noetherian_local Vr' _ _ _ _ t1 t2
      have heq' : σ₂ (zt ^ ((M - 1) * eps (lab c)) * h) = zt ^ ((M - 1) * eps (lab c)) * h' :=
        hinjr (by simpa only [map_mul, map_pow, smul_eq_mul] using heq)
      have := congrArg (𝔗.X₂.M.stalkHom z₂) heq'
      rw [hσ₂'] at this
      simp only [map_mul, map_pow, hzt, hh, hh'] at this
      simp only [Fv, map_mul, map_pow]
      exact this
    refine ⟨gk.toIntLinearEquiv.toLinearMap, fun b x => ⟨0, ?_⟩, ?_, hcong, fun κ c => ?_⟩
    · rw [hsmul, hsmul]
      simp
    · rw [hdet, sub_self]
      exact dvd_zero _
    · show σ (Fv (aκ κ) c) = Fv (aκ (fun v => gk (κ v))) c
      have e1 : σ (Fv (aκ κ) c) = σ' (Fv (aκ κ) c) := rfl
      rw [e1, hFσ]
      simp only [Fv]
      rw [hf₂per _ _ _ ((hint₂ y₀ _).2 (yy_sub_zero (M₂ y₀) (hga _ _ (haκ κ)) (haκ _) fun v => ⟨0, (add_zero _).symm.trans (congrArg _ (smul_zero _).symm)⟩))]

end GlobalTheory.Poinc.Sep.DeepSums
