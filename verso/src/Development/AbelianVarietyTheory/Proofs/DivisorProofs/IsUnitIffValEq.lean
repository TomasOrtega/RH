import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulOfValLe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRootStalk
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPrimGenerator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsValuationClosure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFrameOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.ScaleAtModel

open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.ZH.TestVal GlobalTheory.ThetaDvr.Scale

/- English proof (translation)
Establish `inj` using `IsFractionRing.injective V (FractionRing V)`. Prove the components needed by the constructor for the conclusion. Introduce `hu`. Assume the negation of the conclusion as `hne`. Establish `hlt` using `lt_of_le_of_ne hle (fun h => hne h.symm)`.

Take `⟨w'', hw'', hm⟩` from `GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hs hle`. Establish `e : w'' = w`. Apply `inj` to reduce the goal to its premises. Establish `: s * (algebraMap V (FractionRing V) w'' - algebraMap V (FractionRing V) w) = 0`. Take the linear combination `hw - hw''`.

Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hs)`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 (e ▸ hm hlt) hu`. Introduce `heq`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`.

Rewrite `heq` using `[map_zero, AddValuation.map_zero]`. Conclude with `hs ((map_eq_zero_iff _ (algebraMap (FractionRing V) F).injective).1 ((AddValuation.top_iff v).1 heq.symm))`. Take `⟨w', hw', -⟩` from `GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hy0 heq.le`. Establish `e : s * (algebraMap V (FractionRing V) (w * w') - 1) = 0`. Rewrite using `[map_mul]`.

Take the linear combination `-hw' - (algebraMap V (FractionRing V) w') * hw`. Establish `e' : w * w' = 1` using `inj (by rw [map_one]; exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_left hs))`. Conclude with `IsUnit.of_mul_eq_one w' e'`.
-/
theorem isUnit_iff_val_eq {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {s y : FractionRing V} (hs : s ≠ 0) {w : V}
    (hw : y = s * algebraMap V (FractionRing V) w)
    (hle : v (algebraMap (FractionRing V) F s) ≤ v (algebraMap (FractionRing V) F y)) :
    IsUnit w ↔ v (algebraMap (FractionRing V) F y) = v (algebraMap (FractionRing V) F s) := by
  have inj := IsFractionRing.injective V (FractionRing V)
  constructor
  · intro hu
    by_contra hne
    have hlt := lt_of_le_of_ne hle (fun h => hne h.symm)
    obtain ⟨w'', hw'', hm⟩ := GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hs hle
    have e : w'' = w := by
      apply inj
      have : s * (algebraMap V (FractionRing V) w'' - algebraMap V (FractionRing V) w) = 0 := by
        linear_combination hw - hw''
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hs)
    exact (IsLocalRing.mem_maximalIdeal _).1 (e ▸ hm hlt) hu
  · intro heq
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero, AddValuation.map_zero] at heq
      exact hs ((map_eq_zero_iff _ (algebraMap (FractionRing V) F).injective).1 ((AddValuation.top_iff v).1 heq.symm))
    obtain ⟨w', hw', -⟩ := GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hy0 heq.le
    have e : s * (algebraMap V (FractionRing V) (w * w') - 1) = 0 := by
      rw [map_mul]; linear_combination -hw' - (algebraMap V (FractionRing V) w') * hw
    have e' : w * w' = 1 := inj (by rw [map_one]; exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_left hs))
    exact IsUnit.of_mul_eq_one w' e'

open MonObj in
attribute [local instance] gtGroup in

/- English proof (translation)
Introduce `o' Ω _ _ _ S ρ V _ _ _ _ hc hu σ A φ cart lb G _ _ semi D U hne`. Take `⟨hL, hL₂, -⟩` from `GlobalTheory.allSixLaws`. Take `⟨H, h₁, h₂, h₃, h₄⟩` from `hyps hL hL₂`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Take `⟨v, hv, -⟩` from `GlobalTheory.ValClosure.exists_valuation_closure V ϖ hϖ`.

Establish `hm` using `odd_level' ρ`. Establish `hA : AdmBase V (IsLocalRing.maximalIdeal V)` using `⟨inferInstance, inferInstance, inferInstance, hc⟩`. Establish `hB` using `D.tau_bimult`. Use `choose Q hQ using QForm.exists_QVal hϖ D`. Take `⟨x, hx, xadd, xinj, xonto⟩` from `GlobalTheory.ThetaDvr.torsion_points σ cart`.

Take `⟨rig, e, hrig, he, hsec⟩` from `GlobalTheory.ThetaDvr.frames σ cart lb x hx`. Take `⟨t, ht⟩` from `hsec 1 ρ.th₁`. Take `⟨w₀, hw₀⟩` from `EvalZero.exists_normW U.toUnifPre rig hrig`. Take `⟨th, ϑ, hE, hP, hgen⟩` from `exists_prim_generator H h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A G semi U w₀ hw₀.1`. Establish `key` using `val_theta H h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A G semi U w₀ rig hw₀ th ϑ hE hP _ hm hu`.

Take `⟨f, f₁, f₂, f₃, -⟩` from `GlobalTheory.TorsionIso.torsion_eq H V _ hA D A G semi U (AlgebraicClosure (FractionRing V)) _ hm.pos`. Take `⟨r, hr⟩` from `hgen t`. Take `⟨sc, rfl⟩` from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing V)))).inv).2 r`. Use `set F := AlgebraicClosure (FractionRing V) with hF`. Use `set iK := algebraMap (FractionRing V) F with hiK`.

Use `set y₀ : S.R →+* F := iK.comp σ with hy₀`. Establish `tv : ∀ a z J, Good A.L z J → cst (R` using `V) F z sc * @id ((TF (R := V) F).left.presheaf.stalk z) (sA th (ptSecT A.A (x a)).left z J) = cst (R := V) F z (y₀ ⟨S.th a, S.th_mem a⟩) * @id ((TF (R := V) F).left.presheaf.stalk z) (val (powFrame A.A A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => (ThetaCompare …`. Establish `b` using `ρ.th_val a`. Rewrite `b` using `[← powFrame_one' (ρ.pt a) (ρ.fr a)]`. Conclude with `b) z J hJ)`.

Establish `uniq : ∀ a (x' : TFK (R` using `V) F ⟶ A.A), x'.left ≫ φ = spMap (iK.comp σ) ≫ (ρ.pt a).left → x' = x a := fun a x' h' => by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `cart.1.hom_ext (h'.trans (hx a).symm) ((Over.w x').trans (Over.w (x a)).symm)`. Establish `h0 : sc ≠ 0`. Introduce `h0`.

Take `⟨a, ha⟩` from `hne`. Apply `ha` to reduce the goal to its premises. Take `⟨z⟩` from `CoefBasic.exists_pt (R := V) (F := F)`. Take `⟨J, hJ⟩` from `CoefBasic.exists_good' (Z := (TFK (R := V) F).left) A.isLB z`. Use `tv a z J hJ` as an intermediate fact.

Rewrite `this` using `[h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul]`. Establish `z0 : y₀ ⟨S.th a, S.th_mem a⟩ = 0` using `CoefBasic.cstH_inj (R := V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)`. Conclude with `(map_eq_zero_iff _ iK.injective).1 z0`. Establish `tv' : ∀ a z J, Good A.L z J → sA th (ptSecT A.A (x a)).left z J = @id ((TFK (R` using `V) F).left.presheaf.stalk z) (cst (R := V) F z (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩)) * (val (powFrame A.A A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by`. Establish `b` using `congrArg (CoefBasic.cstH (R := V) z sc⁻¹ * ·) (tv a z J hJ)`.

Simplify using `only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b`. Rewrite using `[CoefBasic.cst_eq]`. Conclude with `b`. Establish `hvs : v sc ≠ ⊤` using `v.ne_top_iff.2 h0`. Establish `split : ∀ a, v (y₀ ⟨S.th a, S.th_mem a⟩) = v sc + v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩)` using `fun a => by`.

Rewrite using `[← v.map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]`. Establish `nz : ∀ a, v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) = 0 ↔ v (y₀ ⟨S.th a, S.th_mem a⟩) = v sc` using `fun a => by`. Rewrite using `[split a]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[h, add_zero]`. Introduce `h`. Take `⟨s, hs⟩` from `WithTop.ne_top_iff_exists.1 hvs`. Rewrite `h` using `[← hs]`. Establish `e1` using `congrArg (((-s : ℚ) : WithTop ℚ) + ·) h`.

Simplify using `only [← add_assoc, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero, zero_add] at e1`. Conclude with `e1`. Establish `low : ∀ b, v sc ≤ v (y₀ ⟨S.th b, S.th_mem b⟩)` using `fun b => by`. Take `⟨q, hq⟩` from `f₂ (x b) (he b).1`. Establish `hk` using `(key q _ ((f₁ _ _).2 hq.symm)).1 _ _ (he b) (tv' b)`.

Establish `lo : (0 : WithTop ℚ) ≤ v (sc⁻¹ * y₀ ⟨S.th b, S.th_mem b⟩)`. Use `hk.1 0 fun χ => by` as an intermediate fact. Distinguish the cases in `c : (S.r * S.N) • χ + q.y = 0`. Rewrite using `[c, QForm.Q_zero hϖ D hQ]`. Simplify using the standard rewrite rules.

Conclude with `div_nonneg (Int.cast_nonneg (zero_le_one.trans (QForm.Q_pos hϖ D hQ c))) (Nat.cast_nonneg _)`. Simplify using `using this`. Rewrite using `[split b]`. Conclude with `le_add_of_nonneg_right lo`. Establish `dvd : ∀ b (q : QkPt D.toPre F (S.r * S.N)), QkToAkU U.toUnifPre F (S.r * S.N) q (x b) → v (y₀ ⟨S.th b, S.th_mem b⟩) = v sc → ∃ z, q.y = (S.r * S.N) • z` using `fun b q hq h => ((key q _ hq).1 _ _ (he b) (tv' b)).2 ((nz b).2 h)`.

Take `⟨j, hj, hrj⟩` from `ρ.r_eq`. Establish `hnd : ρ.n ∣ S.r * S.N`. Rewrite using `[hrj, ρ.N_eq]`. Conclude with `Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _`. Establish `coset : ∀ a (q : QkPt D.toPre F (S.r * S.N)), QkToAkU U.toUnifPre F (S.r * S.N) q (x a) → (∃ z, q.y = (S.r * S.N) • z) → ∃ a', ρ.n • (a' - a) = 0 ∧ v (y₀ ⟨S.th a', S.th_mem a'⟩) = v sc`.

Introduce and unpack `a q hq₁ ⟨z, hz'⟩`. Set `q₀ : QkPt D.toPre F (S.r * S.N)` to `qkMk hB 0 (q.g + iota hB _ (-z)) (by`. Rewrite using `[smul_add, qk_nsmul hB, ← map_nsmul, ← map_add, smul_neg, ← hz', add_neg_cancel])`. Establish `e₀ : f q = f q₀` using `(f₃ _ _).2 ((equiv_iff hB _ _).2 ⟨-z, by`. Rewrite using `[smul_neg, ← hz', add_neg_cancel]`.

Use the proof step `rfl, rfl⟩)`. Take `⟨q', x', hy', hx', hpow, hval⟩` from `(key q₀ (x a) ((f₁ _ _).2 (((f₁ _ _).1 hq₁).trans e₀))).2 ρ.n ρ.n_prime.two_le hnd rfl`. Take `⟨a', rfl⟩` from `xonto x' (hx' w₀ hw₀.1).1`. Use `A.isAb.comm` as an intermediate fact. Set `X : Multiplicative S.Gam →* (TFK (R` to `V) F ⟶ A.A) := MonoidHom.mk' (fun a => x a.toAdd) fun a b => xadd _ _`.

Use `⟨a', xinj ?_, (nz a').1 (hval _ _ (he a') (tv' a'))⟩` and prove the remaining obligations. Establish `b : X ((Multiplicative.ofAdd a' * (Multiplicative.ofAdd a)⁻¹) ^ ρ.n) = X 1`. Rewrite using `[map_pow, map_mul, map_inv, map_one]`. Conclude with `hpow`. Rewrite using `[sub_eq_add_neg]`.

Conclude with `b`. Establish `q0 : QkToAkU U.toUnifPre F (S.r * S.N) (qkMk hB 0 0 (by rw [smul_zero, map_zero]) : QkPt D.toPre F (S.r * S.N)) (f (qkMk hB 0 0 (by rw [smul_zero, map_zero])))` using `(f₁ _ _).2 rfl`. Take `⟨a₁, ha₁⟩` from `xonto _ (q0 w₀ hw₀.1).1`. Take `⟨a₀, -, ha₀⟩` from `coset a₁ _ (ha₁ ▸ q0) ⟨0, by simp [qkMk]⟩`. Use `set s := σ ⟨S.th a₀, S.th_mem a₀⟩ with hs_def`.

Establish `hs0 : s ≠ 0`. Introduce `h`. Establish `: v (y₀ ⟨S.th a₀, S.th_mem a₀⟩) = ⊤` using `by show v (iK s) = ⊤`. Rewrite using `[h, map_zero, AddValuation.map_zero]`. Conclude with `hvs (ha₀.symm.trans this)`.

Establish `hle : ∀ b, v (iK s) ≤ v (iK (σ ⟨S.th b, S.th_mem b⟩))` using `fun b => by`. Establish `h1 : v (iK s) = v sc` using `ha₀`. Rewrite using `[h1]`. Conclude with `low b`. Use `choose w hw using fun b => (GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hs0 (hle b))`.

Establish `hw' : ∀ b, σ ⟨S.th b, S.th_mem b⟩ = s * algebraMap V (FractionRing V) (w b)` using `fun b => by`. Rewrite using `[(hw b).1, mul_comm]`. Establish `unit_iff : ∀ b, IsUnit (w b) ↔ v (y₀ ⟨S.th b, S.th_mem b⟩) = v sc` using `fun b => by`. Rewrite using `[← ha₀]`. Conclude with `isUnit_iff_val_eq hϖ hv hs0 (hw' b) (hle b)`.

Use `⟨s, w, hs0, hw', fun a => ?_, fun a pk x' hpk hx' => ?_⟩` and prove the remaining obligations. Take `⟨q, hq⟩` from `f₂ (x a) (he a).1`. Conclude with `⟨q, x a, (f₁ _ _).2 hq.symm, hx a⟩`. Take `rfl` from `uniq a x' hx'`. Use `⟨fun hu' => dvd a pk hpk ((unit_iff a).1 hu'), fun hd => ?_⟩` and prove the remaining obligations.

Take `⟨a', hn, hv'⟩` from `coset a pk hpk hd`. Use `⟨a' - a, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[add_sub_cancel]`. Conclude with `(unit_iff a').2 hv'`.
-/
theorem scale_at_model : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → IsUnit ((S.r * S.N : ℕ) : V) →
    ∀ (σ : S.R →+* FractionRing V) (A : PolAV (Sp (FractionRing V))) (φ : A.A.left ⟶ ρ.P.A.left),
    IsGrpPullback A.A ρ.P.A (spMap σ) φ → LBIso A.L (ρ.P.L.pull φ) →
    ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (D : DegData V (maximalIdeal V)) (U : Unif (maximalIdeal V) D A G), (∃ a, σ ⟨S.th a, S.th_mem a⟩ ≠ 0) →
    ∃ (s : FractionRing V) (v : S.Gam → V), s ≠ 0 ∧
      (∀ a, σ ⟨S.th a, S.th_mem a⟩ = s * algebraMap V (FractionRing V) (v a)) ∧
      (∀ a, ∃ (pk : QkPt D.toPre (AlgebraicClosure (FractionRing V)) (S.r * S.N)) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A),
        QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) (S.r * S.N) pk x ∧
        x.left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp σ) ≫ (ρ.pt a).left) ∧
      (∀ a (pk : QkPt D.toPre (AlgebraicClosure (FractionRing V)) (S.r * S.N)) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A),
        QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) (S.r * S.N) pk x →
        x.left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp σ) ≫ (ρ.pt a).left →
        (IsUnit (v a) → ∃ z, pk.y = (S.r * S.N) • z) ∧
        ((∃ z, pk.y = (S.r * S.N) • z) → ∃ b : S.Gam, ρ.n • b = 0 ∧ IsUnit (v (a + b)))) := by
  intro o' Ω _ _ _ S ρ V _ _ _ _ hc hu σ A φ cart lb G _ _ semi D U hne
  obtain ⟨hL, hL₂, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := hyps hL hL₂
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, hv, -⟩ := GlobalTheory.ValClosure.exists_valuation_closure V ϖ hϖ
  have hm := odd_level' ρ
  have hA : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  choose Q hQ using QForm.exists_QVal hϖ D
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points σ cart
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.ThetaDvr.frames σ cart lb x hx
  obtain ⟨t, ht⟩ := hsec 1 ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A G
    semi U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A G semi U w₀ rig hw₀ th ϑ hE hP
    _ hm hu
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H V _ hA D A G semi U
    (AlgebraicClosure (FractionRing V)) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing V)))).inv).2 r
  set F := AlgebraicClosure (FractionRing V) with hF
  set iK := algebraMap (FractionRing V) F with hiK
  set y₀ : S.R →+* F := iK.comp σ with hy₀
  have tv : ∀ a z J, Good A.L z J → cst (R := V) F z sc *
      @id ((TF (R := V) F).left.presheaf.stalk z) (sA th (ptSecT A.A (x a)).left z J) =
      cst (R := V) F z (y₀ ⟨S.th a, S.th_mem a⟩) * @id ((TF (R := V) F).left.presheaf.stalk z)
        (val (powFrame A.A A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := ρ.th_val a
      rw [← powFrame_one' (ρ.pt a) (ρ.fr a)] at b
      exact b) z J hJ)
  have uniq : ∀ a (x' : TFK (R := V) F ⟶ A.A), x'.left ≫ φ = spMap (iK.comp σ) ≫ (ρ.pt a).left → x' = x a :=
    fun a x' h' => by
      apply Over.OverMorphism.ext
      exact cart.1.hom_ext (h'.trans (hx a).symm) ((Over.w x').trans (Over.w (x a)).symm)
  have h0 : sc ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := hne
    apply ha
    obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := F)
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := V) F).left) A.isLB z
    have := tv a z J hJ
    rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
    have z0 : y₀ ⟨S.th a, S.th_mem a⟩ = 0 :=
      CoefBasic.cstH_inj (R := V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    exact (map_eq_zero_iff _ iK.injective).1 z0
  have tv' : ∀ a z J, Good A.L z J → sA th (ptSecT A.A (x a)).left z J =
      @id ((TFK (R := V) F).left.presheaf.stalk z)
        (cst (R := V) F z (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩)) *
        (val (powFrame A.A A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have hvs : v sc ≠ ⊤ := v.ne_top_iff.2 h0
  have split : ∀ a, v (y₀ ⟨S.th a, S.th_mem a⟩) = v sc + v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) := fun a => by
    rw [← v.map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) = 0 ↔ v (y₀ ⟨S.th a, S.th_mem a⟩) = v sc := fun a => by
    rw [split a]
    constructor
    · intro h; rw [h, add_zero]
    · intro h
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hvs
      rw [← hs] at h
      have e1 := congrArg (((-s : ℚ) : WithTop ℚ) + ·) h
      simp only [← add_assoc, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero, zero_add] at e1
      exact e1

  have low : ∀ b, v sc ≤ v (y₀ ⟨S.th b, S.th_mem b⟩) := fun b => by
    obtain ⟨q, hq⟩ := f₂ (x b) (he b).1
    have hk := (key q _ ((f₁ _ _).2 hq.symm)).1 _ _ (he b) (tv' b)
    have lo : (0 : WithTop ℚ) ≤ v (sc⁻¹ * y₀ ⟨S.th b, S.th_mem b⟩) := by
      have := hk.1 0 fun χ => by
        by_cases c : (S.r * S.N) • χ + q.y = 0
        · rw [c, QForm.Q_zero hϖ D hQ]; simp
        · exact div_nonneg (Int.cast_nonneg (zero_le_one.trans (QForm.Q_pos hϖ D hQ c))) (Nat.cast_nonneg _)
      simpa using this
    rw [split b]; exact le_add_of_nonneg_right lo
  have dvd : ∀ b (q : QkPt D.toPre F (S.r * S.N)), QkToAkU U.toUnifPre F (S.r * S.N) q (x b) →
      v (y₀ ⟨S.th b, S.th_mem b⟩) = v sc → ∃ z, q.y = (S.r * S.N) • z := fun b q hq h =>
    ((key q _ hq).1 _ _ (he b) (tv' b)).2 ((nz b).2 h)

  obtain ⟨j, hj, hrj⟩ := ρ.r_eq
  have hnd : ρ.n ∣ S.r * S.N := by
    rw [hrj, ρ.N_eq]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
  have coset : ∀ a (q : QkPt D.toPre F (S.r * S.N)), QkToAkU U.toUnifPre F (S.r * S.N) q (x a) →
      (∃ z, q.y = (S.r * S.N) • z) → ∃ a', ρ.n • (a' - a) = 0 ∧ v (y₀ ⟨S.th a', S.th_mem a'⟩) = v sc := by
    rintro a q hq₁ ⟨z, hz'⟩
    let q₀ : QkPt D.toPre F (S.r * S.N) := qkMk hB 0 (q.g + iota hB _ (-z)) (by
      rw [smul_add, qk_nsmul hB, ← map_nsmul, ← map_add, smul_neg, ← hz', add_neg_cancel])
    have e₀ : f q = f q₀ := (f₃ _ _).2 ((equiv_iff hB _ _).2 ⟨-z, by
      rw [smul_neg, ← hz', add_neg_cancel]; rfl, rfl⟩)
    obtain ⟨q', x', hy', hx', hpow, hval⟩ :=
      (key q₀ (x a) ((f₁ _ _).2 (((f₁ _ _).1 hq₁).trans e₀))).2 ρ.n ρ.n_prime.two_le hnd rfl
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    have := A.isAb.comm
    let X : Multiplicative S.Gam →* (TFK (R := V) F ⟶ A.A) :=
      MonoidHom.mk' (fun a => x a.toAdd) fun a b => xadd _ _
    refine ⟨a', xinj ?_, (nz a').1 (hval _ _ (he a') (tv' a'))⟩
    have b : X ((Multiplicative.ofAdd a' * (Multiplicative.ofAdd a)⁻¹) ^ ρ.n) = X 1 := by
      rw [map_pow, map_mul, map_inv, map_one]; exact hpow
    rw [sub_eq_add_neg]
    exact b

  have q0 : QkToAkU U.toUnifPre F (S.r * S.N)
      (qkMk hB 0 0 (by rw [smul_zero, map_zero]) : QkPt D.toPre F (S.r * S.N)) (f (qkMk hB 0 0 (by rw [smul_zero, map_zero]))) :=
    (f₁ _ _).2 rfl
  obtain ⟨a₁, ha₁⟩ := xonto _ (q0 w₀ hw₀.1).1
  obtain ⟨a₀, -, ha₀⟩ := coset a₁ _ (ha₁ ▸ q0) ⟨0, by simp [qkMk]⟩
  set s := σ ⟨S.th a₀, S.th_mem a₀⟩ with hs_def
  have hs0 : s ≠ 0 := by
    intro h
    have : v (y₀ ⟨S.th a₀, S.th_mem a₀⟩) = ⊤ := by
      show v (iK s) = ⊤
      rw [h, map_zero, AddValuation.map_zero]
    exact hvs (ha₀.symm.trans this)
  have hle : ∀ b, v (iK s) ≤ v (iK (σ ⟨S.th b, S.th_mem b⟩)) := fun b => by
    have h1 : v (iK s) = v sc := ha₀
    rw [h1]; exact low b
  choose w hw using fun b => (GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hs0 (hle b))
  have hw' : ∀ b, σ ⟨S.th b, S.th_mem b⟩ = s * algebraMap V (FractionRing V) (w b) := fun b => by
    rw [(hw b).1, mul_comm]
  have unit_iff : ∀ b, IsUnit (w b) ↔ v (y₀ ⟨S.th b, S.th_mem b⟩) = v sc := fun b => by
    rw [← ha₀]
    exact isUnit_iff_val_eq hϖ hv hs0 (hw' b) (hle b)
  refine ⟨s, w, hs0, hw', fun a => ?_, fun a pk x' hpk hx' => ?_⟩
  · obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
    exact ⟨q, x a, (f₁ _ _).2 hq.symm, hx a⟩
  · obtain rfl := uniq a x' hx'
    refine ⟨fun hu' => dvd a pk hpk ((unit_iff a).1 hu'), fun hd => ?_⟩
    obtain ⟨a', hn, hv'⟩ := coset a pk hpk hd
    refine ⟨a' - a, hn, ?_⟩
    rw [add_sub_cancel]
    exact (unit_iff a').2 hv'

end GlobalTheory.Poinc.ScaleAtModel
end
