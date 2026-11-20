import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrincipalCongruenceInDefiniteLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteLevelPreimageFinitelyManyCosetsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.VFormCls

open Formalism.IndefR.Bridge

/- English proof (translation)
Introduce `i i' h`. Conclude with `(hy (y i)).unique ⟨1, 1, by simp⟩ ⟨1, 1, by simp [h]⟩`.
-/
theorem reps_inj {G Γ' : Type} [Group G] [Group Γ'] {ι : Γ' →* G} {J : Subgroup G} {I : Type} {y : I → G}
    (hy : IsReps ι J y) : Function.Injective y := by
  intro i i' h
  exact (hy (y i)).unique ⟨1, 1, by simp⟩ ⟨1, 1, by simp [h]⟩

/- English proof (translation)
Set `e : G ≃* G'` to `MulEquiv.ofBijective φ hφ`. Establish `he : ∀ x, φ (e.symm x) = x` using `fun x => e.apply_symm_apply x`. Set `t : I → G` to `fun i => a * e.symm (y i)`. Establish `hty : ∀ i, φ (a⁻¹ * t i) = y i`. Introduce `i`.

Simplify using `only [t, ← mul_assoc, inv_mul_cancel, one_mul, he]`. Establish `tinj : Function.Injective t`. Introduce `i i' h`. Apply `reps_inj hy` to reduce the goal to its premises. Rewrite using `[← hty i, ← hty i', h]`.

Establish `hrat' : ∀ γ : Γ, ∃ γ', ι γ' = φ (a⁻¹ * γ * a)` using `fun γ => (hrat γ).1 γ.2`. Establish `key : ∀ (g : G) (i : I), (∃ (γ : Γ) (κ : G), κ ∈ J'.comap φ ∧ g = (γ : G) * t i * κ) ↔ ∃ (γ' : Γ') (k : J'), φ (a⁻¹ * g) = ι γ' * y i * k`. Introduce `g i`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, κ, hκ, rfl⟩`.

Take `⟨γ', hγ'⟩` from `hrat' γ`. Use `⟨γ', ⟨φ κ, hκ⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hγ', ← hty i]`. Simplify using `only [t, map_mul, map_inv, he]`. Use `group`.

Introduce and unpack `⟨γ', k, h⟩`. Establish `hγ : a * e.symm (ι γ') * a⁻¹ ∈ Γ`. Rewrite using `[hrat]; exact ⟨γ', by simp [he, mul_assoc]⟩`. Use `⟨⟨_, hγ⟩, e.symm k, by simp [he], ?_⟩` and prove the remaining obligations. Apply `hφ.1` to reduce the goal to its premises.

Establish `h2 : φ g = φ a * (ι γ' * y i * k)`. Rewrite using `[← h, map_mul, map_inv]`. Use `group`. Rewrite using `[h2]`. Simplify using `only [t, map_mul, map_inv, he]`.

Use `group`. Use `choose c hc using hrat'`. Use `⟨Finset.univ.image t, ?_, ?_⟩` and prove the remaining obligations. Introduce `g`. Take `⟨i, ⟨γ', k, hi⟩, huniq⟩` from `hy (φ (a⁻¹ * g))`.

Use `⟨t i, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key g i).2 ⟨γ', k, hi⟩⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `s ⟨hs, hd⟩`. Take `⟨i', -, rfl⟩` from `Finset.mem_image.1 hs`. Rewrite using `[huniq i' ((key g i').1 hd)]`. Introduce `W _ _ F F'`.

Rewrite using `[Finset.sum_image (fun i _ j _ h => tinj h)]`. Unfold `adInner`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hty i]`. Use `congr 2`.

Use `congrArg (fun n : ℕ => (n : ℂ)) (Nat.card_congr (Equiv.symm ?_))` and prove the remaining obligations. Use `{ toFun := fun γ => ⟨c γ.1, ?_⟩ invFun := fun γ' => ⟨⟨a * e.symm (ι γ'.1) * a⁻¹, (hrat _).2 ⟨γ'.1, by simp [he, mul_assoc]⟩⟩, ?_⟩ left_inv := ?_ right_inv := ?_ }` and prove the remaining obligations. Rewrite using `[mem_stab, hc γ.1, ← hty i]`. Use `γ.2` as an intermediate fact. Rewrite `this` using `[Subgroup.mem_comap]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_mul, map_inv]`. Use `group`. Use `γ'.2` as an intermediate fact. Rewrite `this` using `[mem_stab]`.

Rewrite using `[Subgroup.mem_comap]`. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [t, map_mul, map_inv, he]`. Use `group`. Introduce `γ`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hφ.1` to reduce the goal to its premises. Simplify using `only [map_mul, map_inv, he]`. Rewrite using `[hc]`.

Simplify using `only [map_mul, map_inv]`. Use `group`. Introduce `γ'`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hι` to reduce the goal to its premises.

Rewrite using `[hc]`. Simplify using `[he, mul_assoc]`.
-/
theorem transport {G G' Γ' : Type} [Group G] [Group G'] [Group Γ'] (Γ : Subgroup G) (ι : Γ' →* G')
    (hι : Function.Injective ι) (φ : G →* G') (hφ : Function.Bijective φ) (a : G)
    (hrat : ∀ h, h ∈ Γ ↔ ∃ γ, ι γ = φ (a⁻¹ * h * a)) (J' : Subgroup G') {I : Type} [Fintype I]
    (y : I → G') (hy : IsReps ι J' y) :
    ∃ T : Finset G, (∀ g : G, ∃! t, t ∈ T ∧ ∃ (γ : Γ) (κ : G), κ ∈ J'.comap φ ∧ g = (γ : G) * t * κ) ∧
      ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (F F' : G' → W),
        adInner ι J' y F F' = ∑ t ∈ T, ((Nat.card {γ : Γ // t⁻¹ * (γ : G) * t ∈ J'.comap φ} : ℕ) : ℂ)⁻¹ *
          inner ℂ (F (φ (a⁻¹ * t))) (F' (φ (a⁻¹ * t))) := by
  classical
  let e : G ≃* G' := MulEquiv.ofBijective φ hφ
  have he : ∀ x, φ (e.symm x) = x := fun x => e.apply_symm_apply x
  let t : I → G := fun i => a * e.symm (y i)
  have hty : ∀ i, φ (a⁻¹ * t i) = y i := by
    intro i; simp only [t, ← mul_assoc, inv_mul_cancel, one_mul, he]
  have tinj : Function.Injective t := by
    intro i i' h
    apply reps_inj hy
    rw [← hty i, ← hty i', h]

  have hrat' : ∀ γ : Γ, ∃ γ', ι γ' = φ (a⁻¹ * γ * a) := fun γ => (hrat γ).1 γ.2

  have key : ∀ (g : G) (i : I), (∃ (γ : Γ) (κ : G), κ ∈ J'.comap φ ∧ g = (γ : G) * t i * κ) ↔
      ∃ (γ' : Γ') (k : J'), φ (a⁻¹ * g) = ι γ' * y i * k := by
    intro g i
    constructor
    · rintro ⟨γ, κ, hκ, rfl⟩
      obtain ⟨γ', hγ'⟩ := hrat' γ
      refine ⟨γ', ⟨φ κ, hκ⟩, ?_⟩
      rw [hγ', ← hty i]
      simp only [t, map_mul, map_inv, he]
      group
    · rintro ⟨γ', k, h⟩
      have hγ : a * e.symm (ι γ') * a⁻¹ ∈ Γ := by
        rw [hrat]; exact ⟨γ', by simp [he, mul_assoc]⟩
      refine ⟨⟨_, hγ⟩, e.symm k, by simp [he], ?_⟩
      apply hφ.1
      have h2 : φ g = φ a * (ι γ' * y i * k) := by
        rw [← h, map_mul, map_inv]; group
      rw [h2]
      simp only [t, map_mul, map_inv, he]
      group
  choose c hc using hrat'
  refine ⟨Finset.univ.image t, ?_, ?_⟩
  · intro g
    obtain ⟨i, ⟨γ', k, hi⟩, huniq⟩ := hy (φ (a⁻¹ * g))
    refine ⟨t i, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key g i).2 ⟨γ', k, hi⟩⟩, ?_⟩
    rintro s ⟨hs, hd⟩
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 hs
    rw [huniq i' ((key g i').1 hd)]
  · intro W _ _ F F'
    rw [Finset.sum_image (fun i _ j _ h => tinj h)]
    unfold adInner
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hty i]
    congr 2
    refine congrArg (fun n : ℕ => (n : ℂ)) (Nat.card_congr (Equiv.symm ?_))
    refine
      { toFun := fun γ => ⟨c γ.1, ?_⟩
        invFun := fun γ' => ⟨⟨a * e.symm (ι γ'.1) * a⁻¹, (hrat _).2 ⟨γ'.1, by simp [he, mul_assoc]⟩⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rw [mem_stab, hc γ.1, ← hty i]
      have := γ.2
      rw [Subgroup.mem_comap] at this
      convert this using 1
      simp only [map_mul, map_inv]; group
    · have := γ'.2
      rw [mem_stab] at this
      rw [Subgroup.mem_comap]
      convert this using 1
      simp only [t, map_mul, map_inv, he]; group
    · intro γ
      apply Subtype.ext; apply Subtype.ext
      apply hφ.1
      simp only [map_mul, map_inv, he]
      rw [hc]
      simp only [map_mul, map_inv]
      group
    · intro γ'
      apply Subtype.ext
      apply hι
      rw [hc]
      simp [he, mul_assoc]

end GlobalTheory.VFormCls

namespace GlobalTheory.VFormCls

/- English proof (translation)
Establish `h0` using `hF 1 g k`. Simplify using `using h0`.
-/
theorem adForms_right {G Γ W : Type} [Group G] [Group Γ] {ι : Γ →* G} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {F : G → W}
    (hF : F ∈ Formalism.IndefR.Bridge.AdForms ι ρ J χ) (g : G) (k : J) : F (g * k) = (χ k : ℂ) • F g := by
  have h0 := hF 1 g k
  simpa using h0

end GlobalTheory.VFormCls

namespace GlobalTheory.VFormCls

open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame Formalism.L2.Theta

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ipA_eq {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hinj : ∀ i t, Function.Injective (R.extV i t)) (μ : D.what₂.Tup) (i : Fin D.R.m)
    (x y : GA D (Vc D i) → (R.cV i).W) :
    (toLiftReal R F tupT hm hTop hinj).ipA μ i x y = (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ipVia (R.extV i (tupT μ)) x y :=
  rfl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hC` using `X.given.core`. Establish `hHV` using `hC.models.HV j (X.tupT μ)`. Establish `hex : ∀ x : D.what₂.Mt μ (j.1 + 1), ∃ h, X.R.extV j (X.tupT μ) h = X.fn hμ j x` using `fun x => (X.IL.jMt μ hμ j x).2.1`. Use `choose hx hhx using hex`. Use `⟨fun x => (X.R.HV j (X.tupT μ)).e (hx x), fun x => ?_, fun x => hhx x, fun x y => ?_⟩` and prove the remaining obligations.

Establish `h` using `LinearMap.mem_range_self (X.R.HV j (X.tupT μ)).e (hx x)`. Rewrite `h` using `[hHV.2.1]`. Conclude with `h`. Establish `hmt` using `X.recR.tied.lift.mt μ hμ j x y`. Rewrite using `[hmt]`.

Use `Eq.trans (ipA_eq X.R X.F X.tupT X.hm X.hTop X.hinj μ j (X.fn hμ j x) (X.fn hμ j y)) ?_` and prove the remaining obligations. Use `congr 1`. Unfold `ipVia`. Establish `h1 : X.fn hμ j x ∈ LinearMap.range (X.R.extV j (X.tupT μ))` using `⟨hx x, hhx x⟩`. Establish `h2 : X.fn hμ j y ∈ LinearMap.range (X.R.extV j (X.tupT μ))` using `⟨hx y, hhx y⟩`.

Use `split_ifs with h`. Establish `e1 : h.1.choose = hx x` using `X.hinj j _ (h.1.choose_spec.trans (hhx x).symm)`. Establish `e2 : h.2.choose = hx y` using `X.hinj j _ (h.2.choose_spec.trans (hhx y).symm)`. Conclude with `(congrArg₂ (fun a b => inner ℂ a b) e1 e2).trans (hHV.2.2 (hx x) (hx y))`. Conclude with `absurd ⟨h1, h2⟩ h`.
-/
theorem inner_eq {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : Fin D.R.m) :
    ∃ Fx : D.what₂.Mt μ (j.1 + 1) → (Bridge.Gf (Vc D j) → (X.R.cV j).W),
      (∀ x, Fx x ∈ Bridge.AdForms (Bridge.ratF (Vc D j)) (X.R.cV j).coef.ρ
        (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ))).J (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ))).χ) ∧
      (∀ x, (X.R.cV j).ext (Fx x) = X.fn hμ j x) ∧
      ∀ x y, inner ℂ x y = (((RealDat.nP X.F false)⁻¹ : ℝ) : ℂ) *
        Bridge.adInner (Bridge.ratF (Vc D j)) (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ))).J
          (X.R.B.L j (X.tupT μ)).pres.y (Fx x) (Fx y) := by
  have hC := X.given.core
  have hHV := hC.models.HV j (X.tupT μ)
  have hex : ∀ x : D.what₂.Mt μ (j.1 + 1), ∃ h, X.R.extV j (X.tupT μ) h = X.fn hμ j x :=
    fun x => (X.IL.jMt μ hμ j x).2.1
  choose hx hhx using hex
  refine ⟨fun x => (X.R.HV j (X.tupT μ)).e (hx x), fun x => ?_, fun x => hhx x, fun x y => ?_⟩
  · have h := LinearMap.mem_range_self (X.R.HV j (X.tupT μ)).e (hx x)
    rw [hHV.2.1] at h
    exact h
  · have hmt := X.recR.tied.lift.mt μ hμ j x y
    rw [hmt]
    refine Eq.trans (ipA_eq X.R X.F X.tupT X.hm X.hTop X.hinj μ j (X.fn hμ j x) (X.fn hμ j y)) ?_
    congr 1
    unfold ipVia
    have h1 : X.fn hμ j x ∈ LinearMap.range (X.R.extV j (X.tupT μ)) := ⟨hx x, hhx x⟩
    have h2 : X.fn hμ j y ∈ LinearMap.range (X.R.extV j (X.tupT μ)) := ⟨hx y, hhx y⟩
    split_ifs with h
    · have e1 : h.1.choose = hx x := X.hinj j _ (h.1.choose_spec.trans (hhx x).symm)
      have e2 : h.2.choose = hx y := X.hinj j _ (h.2.choose_spec.trans (hhx y).symm)
      exact (congrArg₂ (fun a b => inner ℂ a b) e1 e2).trans (hHV.2.2 (hx x) (hx y))
    · exact absurd ⟨h1, h2⟩ h

end GlobalTheory.VFormCls

namespace GlobalTheory.VFormCls

open Formalism.IndefR Formalism.L2.Theta

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Take `⟨hsplit, -, hinter, -⟩` from `GlobalTheory.UnitarySplit.real_finite_split D V`. Prove the components needed by the constructor for the conclusion. Introduce `x y h`. Apply `P.inj` to reduce the goal to its premises. Establish `h1 : finHom V (P.ψ x) = finHom V (P.ψ y)` using `congrArg Subtype.val h`.

Establish `h2 : (P.ψ y)⁻¹ * P.ψ x = 1`. Apply `hinter` to reduce the goal to its premises. Use `show _ ∈ (finHom V).ker`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]`. Conclude with `(GfC V).mul_mem ((GfC V).inv_mem (P.into y)) (P.into x)`.

Conclude with `(inv_mul_eq_one.1 h2).symm`. Introduce `x`. Take `⟨g, hg⟩` from `x.2`. Take `⟨a, ha, k, hk, rfl⟩` from `hsplit g`. Take `⟨h, hh⟩` from `P.onto k hk`.

Establish `ha' : finHom V a = 1` using `ha`. Use `⟨h, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.comp_apply, MonoidHom.coe_rangeRestrict, ← hg, map_mul, ha', one_mul, hh]`.
-/
theorem frame_bij {D : D7} {V : TH.HSp D} {n : ℕ} (P : principalLevelFrame.RowPsi V n) :
    Function.Bijective ((finHom V).rangeRestrict.comp P.ψ) := by
  obtain ⟨hsplit, -, hinter, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  constructor
  · intro x y h
    apply P.inj
    have h1 : finHom V (P.ψ x) = finHom V (P.ψ y) := congrArg Subtype.val h
    have h2 : (P.ψ y)⁻¹ * P.ψ x = 1 := by
      apply hinter
      · show _ ∈ (finHom V).ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      · exact (GfC V).mul_mem ((GfC V).inv_mem (P.into y)) (P.into x)
    exact (inv_mul_eq_one.1 h2).symm
  · intro x
    obtain ⟨g, hg⟩ := x.2
    obtain ⟨a, ha, k, hk, rfl⟩ := hsplit g
    obtain ⟨h, hh⟩ := P.onto k hk
    have ha' : finHom V a = 1 := ha
    refine ⟨h, Subtype.ext ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.coe_rangeRestrict, ← hg, map_mul, ha', one_mul, hh]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_one]`. Introduce `γ h`. Establish `h1 : finHom V (γ : GA D V) = 1` using `congrArg Subtype.val h`. Conclude with `Subtype.ext (GlobalTheory.DefFree.AdelCls.rat_inj V γ γ.2 ((GlobalTheory.DefFree.AdelCls.finU_eq_one_iff V _).2 (MonoidHom.mem_ker.2 h1)))`.
-/
theorem ratF_inj {D : D7} (V : TH.HSp D) : Function.Injective (Bridge.ratF V) := by
  rw [injective_iff_map_eq_one]
  intro γ h
  have h1 : finHom V (γ : GA D V) = 1 := congrArg Subtype.val h
  exact Subtype.ext (GlobalTheory.DefFree.AdelCls.rat_inj V γ γ.2
    ((GlobalTheory.DefFree.AdelCls.finU_eq_one_iff V _).2 (MonoidHom.mem_ker.2 h1)))

end GlobalTheory.VFormCls

namespace GlobalTheory.VFormCls

open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.L2.Theta

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Substitute `hk` using the available equality. Take `⟨Fx, hmem, hext, hin⟩` from `inner_eq X μ hμ j`. Take `⟨N, hN, hopen⟩` from `GlobalTheory.T.exists_principalCongruence_in_definiteLevel D P.cf P.C P.tp X P.M P.rep hA j (X.tupT μ)`. Take `⟨Fb, hFb⟩` from `GlobalTheory.T.definiteLevel_preimage_finitely_many_cosets D P.cf P.C P.tp X P.M P.rep hA j (X.tupT μ)`. Establish `hcV` using `X.given.core.models.cV j`.

Establish `hφ` using `frame_bij (hA.PV j)`. Use `set φ := (finHom (Vc D j)).rangeRestrict.comp (hA.PV j).ψ with hφdef`. Use `set EV := levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ)) with hEV`. Use `set eW := hA.eW μ hμ j with heW`. Establish `hrat : ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔ ∃ γ, Bridge.ratF (Vc D j) γ = φ ((hA.a j)⁻¹ * h * hA.a j)`.

Introduce `h`. Rewrite using `[hA.rat j h]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, hγ, e⟩`. Conclude with `⟨⟨γ, hγ⟩, Subtype.ext e⟩`.

Introduce and unpack `⟨γ, e⟩`. Conclude with `⟨γ.1, γ.2, congrArg Subtype.val e⟩`. Take `⟨T, hT, hsum⟩` from `transport (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (Bridge.ratF (Vc D j)) (ratF_inj _) φ hφ (hA.a j) hrat EV.J (X.R.B.L j (X.tupT μ)).pres.y (X.R.B.L j (X.tupT μ)).pres.reps`. Establish `hreal : ∀ x h, (P.M μ (j.1 + 1) h1 h2).real x h = eW (Fx x (φ ((hA.a j)⁻¹ * h)))`. Introduce `x h`.

Rewrite using `[hA.real μ hμ j x h, ← hext x]`. Establish `hin' : ((hA.PV j).ψ ((hA.a j)⁻¹ * h))⁻¹ ∈ GfC (Vc D j)` using `(GfC _).inv_mem ((hA.PV j).into _)`. Use `show eW ((X.R.cV j).ρ ((hA.PV j).ψ ((hA.a j)⁻¹ * h))⁻¹ _) = _`. Rewrite using `[hcV.1 _ hin']`. Both sides reduce to the same expression.

Set `β : (P.M μ (j.1 + 1) h1 h2).wt.W →ₗ⋆[ℂ] (P.M μ (j.1 + 1) h1 h2).wt.W →ₗ[ℂ] ℂ` to `((innerₛₗ ℂ).comp eW.symm.toLinearMap).compl₂ eW.symm.toLinearMap`. Establish `hβ : ∀ u v, β u v = inner ℂ (eW.symm u) (eW.symm v)` using `fun u v => rfl`. Use `⟨EV.J.comap φ, EV.χ.comp (φ.subgroupComap EV.J), T, β, (RealDat.nP X.F false)⁻¹, ⟨?_, ?_, ?_⟩, ?_, ?_, hT, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `u v`. Rewrite using `[hβ, hβ, inner_conj_symm]`.

Introduce `u hu`. Rewrite using `[hβ]`. Conclude with `(re_inner_self_pos (𝕜 := ℂ)).2 ((LinearEquiv.map_ne_zero_iff eW.symm).2 hu)`. Introduce `γ u v`. Take `⟨γ', e⟩` from `(hrat γ).1 γ.2`.

Establish `hw` using `hA.wt μ hμ j γ γ'.1 γ'.2 (congrArg Subtype.val e)`. Establish `hs : ∀ w, eW.symm ((P.M μ (j.1 + 1) h1 h2).wt.ρ γ w) = (X.R.cV j).ρ γ'.1 (eW.symm w)`. Introduce `w`. Rewrite using `[LinearEquiv.symm_apply_eq, hw, LinearEquiv.apply_symm_apply]`. Rewrite using `[hβ, hβ, hs, hs, hcV.2.1]`.

Conclude with `⟨Fb, fun κ hκ => hFb κ hκ⟩`. Conclude with `⟨N, hN, fun κ hκ => hopen κ hκ⟩`. Unfold `RealDat.nP`. Conclude with `inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)`. Introduce `x`.

Establish `hr : (P.M μ (j.1 + 1) h1 h2).real x ∈ NG.TypeSp (P.M μ (j.1 + 1) h1 h2).wt.ρ (P.M μ (j.1 + 1) h1 h2).J (P.M μ (j.1 + 1) h1 h2).χ`. Rewrite using `[← (P.M μ (j.1 + 1) h1 h2).real_range]`. Conclude with `LinearMap.mem_range_self _ _`. Use `⟨hr.1, fun κ => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `h`.

Use `show (P.M μ (j.1 + 1) h1 h2).real x (h * κ) = _`. Rewrite using `[Pi.smul_apply, hreal, hreal, ← mul_assoc, map_mul]`. Establish `hm` using `adForms_right (hmem x) (φ ((hA.a j)⁻¹ * h)) ⟨φ κ, κ.2⟩`. Rewrite using `[hm]`. Conclude with `(eW.map_smul _ _).trans rfl`.

Introduce `x y`. Rewrite using `[hin x y, hsum (Fx x) (Fx y)]`. Unfold `GlobalTheory.CoefDuty.classSum`. Use `congr 1`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[hreal, hreal]`. Simplify using `only [hβ, LinearEquiv.symm_apply_apply]`.
-/
theorem core (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)
    (hA : GlobalTheory.NJoin.Agree X P.M P.rep) (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : Fin D.R.m) (k : ℕ) (hk : j.1 + 1 = k)
    (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) :
    ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ) (T : Finset (GAf D.host.E D.R.nV))
      (β : (P.M μ k h1 h2).wt.W →ₗ⋆[ℂ] (P.M μ k h1 h2).wt.W →ₗ[ℂ] ℂ) (c : ℝ),
      GlobalTheory.CoefDuty.IsInvForm (P.M μ k h1 h2).wt β ∧ GlobalTheory.CoefDuty.IsBounded J ∧
      (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧
      GlobalTheory.CoefDuty.IsClassReps J T ∧ 0 < c ∧
      (∀ x, (P.M μ k h1 h2).real x ∈ NG.TypeSp (P.M μ k h1 h2).wt.ρ J χ) ∧
      ∀ x y, inner ℂ x y = (c : ℂ) * GlobalTheory.CoefDuty.classSum (P.M μ k h1 h2).wt β J T
        ((P.M μ k h1 h2).real x) ((P.M μ k h1 h2).real y) := by
  subst hk
  obtain ⟨Fx, hmem, hext, hin⟩ := inner_eq X μ hμ j
  obtain ⟨N, hN, hopen⟩ := GlobalTheory.T.exists_principalCongruence_in_definiteLevel D P.cf P.C P.tp X P.M P.rep hA j (X.tupT μ)
  obtain ⟨Fb, hFb⟩ := GlobalTheory.T.definiteLevel_preimage_finitely_many_cosets D P.cf P.C P.tp X P.M P.rep hA j (X.tupT μ)
  have hcV := X.given.core.models.cV j
  have hφ := frame_bij (hA.PV j)
  set φ := (finHom (Vc D j)).rangeRestrict.comp (hA.PV j).ψ with hφdef
  set EV := levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ)) with hEV
  set eW := hA.eW μ hμ j with heW
  have hrat : ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔
      ∃ γ, Bridge.ratF (Vc D j) γ = φ ((hA.a j)⁻¹ * h * hA.a j) := by
    intro h
    rw [hA.rat j h]
    constructor
    · rintro ⟨γ, hγ, e⟩
      exact ⟨⟨γ, hγ⟩, Subtype.ext e⟩
    · rintro ⟨γ, e⟩
      exact ⟨γ.1, γ.2, congrArg Subtype.val e⟩
  obtain ⟨T, hT, hsum⟩ := transport (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (Bridge.ratF (Vc D j)) (ratF_inj _) φ hφ
    (hA.a j) hrat EV.J (X.R.B.L j (X.tupT μ)).pres.y (X.R.B.L j (X.tupT μ)).pres.reps
  have hreal : ∀ x h, (P.M μ (j.1 + 1) h1 h2).real x h = eW (Fx x (φ ((hA.a j)⁻¹ * h))) := by
    intro x h
    rw [hA.real μ hμ j x h, ← hext x]
    have hin' : ((hA.PV j).ψ ((hA.a j)⁻¹ * h))⁻¹ ∈ GfC (Vc D j) := (GfC _).inv_mem ((hA.PV j).into _)
    show eW ((X.R.cV j).ρ ((hA.PV j).ψ ((hA.a j)⁻¹ * h))⁻¹ _) = _
    rw [hcV.1 _ hin']
    rfl
  let β : (P.M μ (j.1 + 1) h1 h2).wt.W →ₗ⋆[ℂ] (P.M μ (j.1 + 1) h1 h2).wt.W →ₗ[ℂ] ℂ :=
    ((innerₛₗ ℂ).comp eW.symm.toLinearMap).compl₂ eW.symm.toLinearMap
  have hβ : ∀ u v, β u v = inner ℂ (eW.symm u) (eW.symm v) := fun u v => rfl
  refine ⟨EV.J.comap φ, EV.χ.comp (φ.subgroupComap EV.J), T, β, (RealDat.nP X.F false)⁻¹, ⟨?_, ?_, ?_⟩, ?_, ?_, hT, ?_, ?_, ?_⟩
  · intro u v
    rw [hβ, hβ, inner_conj_symm]
  · intro u hu
    rw [hβ]
    exact (re_inner_self_pos (𝕜 := ℂ)).2 ((LinearEquiv.map_ne_zero_iff eW.symm).2 hu)
  · intro γ u v
    obtain ⟨γ', e⟩ := (hrat γ).1 γ.2
    have hw := hA.wt μ hμ j γ γ'.1 γ'.2 (congrArg Subtype.val e)
    have hs : ∀ w, eW.symm ((P.M μ (j.1 + 1) h1 h2).wt.ρ γ w) = (X.R.cV j).ρ γ'.1 (eW.symm w) := by
      intro w
      rw [LinearEquiv.symm_apply_eq, hw, LinearEquiv.apply_symm_apply]
    rw [hβ, hβ, hs, hs, hcV.2.1]
  · exact ⟨Fb, fun κ hκ => hFb κ hκ⟩
  · exact ⟨N, hN, fun κ hκ => hopen κ hκ⟩
  · unfold RealDat.nP
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  · intro x
    have hr : (P.M μ (j.1 + 1) h1 h2).real x ∈ NG.TypeSp (P.M μ (j.1 + 1) h1 h2).wt.ρ
        (P.M μ (j.1 + 1) h1 h2).J (P.M μ (j.1 + 1) h1 h2).χ := by
      rw [← (P.M μ (j.1 + 1) h1 h2).real_range]; exact LinearMap.mem_range_self _ _
    refine ⟨hr.1, fun κ => ?_⟩
    funext h
    show (P.M μ (j.1 + 1) h1 h2).real x (h * κ) = _
    rw [Pi.smul_apply, hreal, hreal, ← mul_assoc, map_mul]
    have hm := adForms_right (hmem x) (φ ((hA.a j)⁻¹ * h)) ⟨φ κ, κ.2⟩
    rw [hm]
    exact (eW.map_smul _ _).trans rfl
  · intro x y
    rw [hin x y, hsum (Fx x) (Fx y)]
    unfold GlobalTheory.CoefDuty.classSum
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hreal, hreal]
    simp only [hβ, LinearEquiv.symm_apply_apply]

/- English proof (translation)
Introduce `hL D P X hA i`. Establish `hμ : Used0 D (D.nd.mu i)` using `Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩`. Establish `hr` using `D.nd.j_range i`. Take `⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i` from `⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩`. Conclude with `core hL D P X hA _ hμ j _ hj hr.1 hr.2`.
-/
theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp),
    GlobalTheory.NJoin.Agree X P.M P.rep → ∀ i, ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ)
      (T : Finset (GAf D.host.E D.R.nV)) (β : (P.M.loc i).wt.W →ₗ⋆[ℂ] (P.M.loc i).wt.W →ₗ[ℂ] ℂ) (c : ℝ),
      GlobalTheory.CoefDuty.IsInvForm (P.M.loc i).wt β ∧ GlobalTheory.CoefDuty.IsBounded J ∧
      (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧
      GlobalTheory.CoefDuty.IsClassReps J T ∧ 0 < c ∧ (∀ x, (P.M.loc i).real x ∈ NG.TypeSp (P.M.loc i).wt.ρ J χ) ∧
      ∀ x y, inner ℂ x y = (c : ℂ) * GlobalTheory.CoefDuty.classSum (P.M.loc i).wt β J T ((P.M.loc i).real x)
        ((P.M.loc i).real y) := by
  intro hL D P X hA i
  have hμ : Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hr := D.nd.j_range i
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i := ⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩
  exact core hL D P X hA _ hμ j _ hj hr.1 hr.2

end GlobalTheory.VFormCls

end
