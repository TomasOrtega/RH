import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RpExistsUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RestrictedProductBoxFibre
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutInvMulMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutOrbit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.FinsumShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.EUInvApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section Abs

/- English proof (translation)
Rewrite using `[propext h]`.
-/
private theorem one_congr {p q : Prop} (h : p ↔ q) : one p = one q := by rw [propext h]

/- English proof (translation)
The claim follows from `if_pos h`.
-/
private theorem one_pos {p : Prop} (h : p) : one p = 1 := if_pos h

/- English proof (translation)
The claim follows from `if_neg h`.
-/
private theorem one_neg {p : Prop} (h : ¬ p) : one p = 0 := if_neg h

variable {G : Type} [Group G]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, q, hq, h⟩`. Use `⟨u⁻¹ * p, U.mul_mem (U.inv_mem hu) hp, q, hq, ?_⟩` and prove the remaining obligations. Establish `: y = u⁻¹ * (u * y)` using `by group`. Rewrite using `[this, h]`.

Simplify using `only [mul_assoc]`. Introduce and unpack `⟨p, hp, q, hq, rfl⟩`. Conclude with `⟨u * p, U.mul_mem hu hp, q, hq, by simp only [mul_assoc]⟩`.
-/
private theorem dc_left {U : Subgroup G} {a u y : G} (hu : u ∈ U) : u * y ∈ DC U a ↔ y ∈ DC U a := by
  constructor
  · rintro ⟨p, hp, q, hq, h⟩
    refine ⟨u⁻¹ * p, U.mul_mem (U.inv_mem hu) hp, q, hq, ?_⟩
    have : y = u⁻¹ * (u * y) := by group
    rw [this, h]; simp only [mul_assoc]
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨u * p, U.mul_mem hu hp, q, hq, by simp only [mul_assoc]⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, q, hq, h⟩`. Use `⟨p, hp, q * u⁻¹, U.mul_mem hq (U.inv_mem hu), ?_⟩` and prove the remaining obligations. Establish `: y = y * u * u⁻¹` using `by group`. Rewrite using `[this, h]`.

Simplify using `only [mul_assoc]`. Introduce and unpack `⟨p, hp, q, hq, rfl⟩`. Conclude with `⟨p, hp, q * u, U.mul_mem hq hu, by simp only [mul_assoc]⟩`.
-/
private theorem dc_right {U : Subgroup G} {a u y : G} (hu : u ∈ U) : y * u ∈ DC U a ↔ y ∈ DC U a := by
  constructor
  · rintro ⟨p, hp, q, hq, h⟩
    refine ⟨p, hp, q * u⁻¹, U.mul_mem hq (U.inv_mem hu), ?_⟩
    have : y = y * u * u⁻¹ := by group
    rw [this, h]; simp only [mul_assoc]
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p, hp, q * u, U.mul_mem hq hu, by simp only [mul_assoc]⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, q, hq, rfl⟩`. Simplify using `using U.mul_mem hp hq`. Introduce `h`. Conclude with `⟨y, h, 1, U.one_mem, by simp⟩`.
-/
private theorem dc_one {U : Subgroup G} {y : G} : y ∈ DC U (1 : G) ↔ y ∈ U := by
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    simpa using U.mul_mem hp hq
  · intro h
    exact ⟨y, h, 1, U.one_mem, by simp⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, q, hq, e⟩`. Use `⟨σ p, h p hp, σ q, h q hq, ?_⟩` and prove the remaining obligations. Use `congrArg σ e` as an intermediate fact. Simplify `this` using `[hi]`.

Introduce and unpack `⟨p, hp, q, hq, rfl⟩`. Conclude with `⟨σ p, h p hp, σ q, h q hq, by simp⟩`.
-/
private theorem dc_sig {U : Subgroup G} (σ : G →* G) (h : ∀ u ∈ U, σ u ∈ U) (hi : ∀ g, σ (σ g) = g) (a y : G) :
    σ y ∈ DC U (σ a) ↔ y ∈ DC U a := by
  constructor
  · rintro ⟨p, hp, q, hq, e⟩
    refine ⟨σ p, h p hp, σ q, h q hq, ?_⟩
    have := congrArg σ e
    simpa [hi] using this
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨σ p, h p hp, σ q, h q hq, by simp⟩

variable {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {B : Base Γ G V}

private def fw (U : Subgroup G) (w a y : G) : ℂ := one (y * w⁻¹ ∈ DC U a)

private structure TwOk (s : B.Tw) (w : G) : Prop where
  om : B.ω = 1
  inv : ∀ g, s.θ (s.θ g) = g
  ww : s.θ w = w⁻¹
  pres : ∀ u ∈ B.U, w * s.θ u * w⁻¹ ∈ B.U

private def sgm (s : B.Tw) (w : G) : G →* G := (MulAut.conj w).toMonoidHom.comp s.θ.toMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem sgm_apply (s : B.Tw) (w g : G) : sgm s w g = w * s.θ g * w⁻¹ := rfl

variable {s : B.Tw} {w : G}

/- English proof (translation)
Simplify using `only [sgm_apply, map_mul, map_inv, h.inv, h.ww]`. Use `group`.
-/
private theorem sgm_sgm (h : TwOk s w) (g : G) : sgm s w (sgm s w g) = g := by
  simp only [sgm_apply, map_mul, map_inv, h.inv, h.ww]; group

/- English proof (translation)
Simplify using `only [sgm_apply, map_mul, map_inv, h.inv, h.ww]`. Use `group`.
-/
private theorem sgm_key (h : TwOk s w) (y : G) : sgm s w (s.θ y * w⁻¹) = w * y := by
  simp only [sgm_apply, map_mul, map_inv, h.inv, h.ww]; group

/- English proof (translation)
Simplify using `only [sgm_apply, map_mul, map_inv, h.inv, h.ww]`. Use `group`.
-/
private theorem twisted_sigma_identity (h : TwOk s w) (y : G) : sgm s w (w * s.θ y) = y * w⁻¹ := by
  simp only [sgm_apply, map_mul, map_inv, h.inv, h.ww]; group

/- English proof (translation)
The claim follows from `h.pres u hu`.
-/
private theorem sgm_mem (h : TwOk s w) {u : G} (hu : u ∈ B.U) : sgm s w u ∈ B.U := h.pres u hu

/- English proof (translation)
Establish `hom : ∀ u : B.U, (((B.ω u)⁻¹ : ℂˣ) : ℂ) = 1` using `fun u => by rw [h.om]; simp`. Use `⟨fun u y => ?_, fun u y => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hom, one_mul]`. Use `one_congr ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`.

Conclude with `dc_left u.2`. Rewrite using `[hom, one_mul]`. Use `one_congr ?_` and prove the remaining obligations. Establish `e : y * s.θ u * w⁻¹ = y * w⁻¹ * (w * s.θ u * w⁻¹)` using `by group`. Rewrite using `[e]`.

Conclude with `dc_right (h.pres u u.2)`. Use `(hf.image fun q => w⁻¹ • q).subset ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hx' : s.θ x.out * w⁻¹ ∈ DC B.U a`. Assume the negation of the conclusion as `hn`.

Conclude with `hx (one_neg hn)`. Establish `h2` using `(dc_sig (sgm s w) (fun u hu => sgm_mem h hu) (sgm_sgm h) a _).2 hx'`. Rewrite `h2` using `[sgm_key h]`. Take `⟨p, hp, q, hq, e⟩` from `h2`. Establish `e' : x.out = w⁻¹ * (p * sgm s w a * q)` using `eq_inv_mul_of_mul_eq e`.

Use `⟨_, ⟨⟨p, hp⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← QuotientGroup.out_eq' x]`. Use `show ((w⁻¹ * (p * sgm s w a) : G) : G ⧸ B.U) = ((x.out : G) : G ⧸ B.U)`. Rewrite using `[e']`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations.

Simplify `hq` using `[mul_assoc]`.
-/
private theorem isTest (h : TwOk s w) (a : G) (hf : AlgebraTools.FinOrb B.U B.U (sgm s w a)) : s.IsTest (fw B.U w a) := by
  have hom : ∀ u : B.U, (((B.ω u)⁻¹ : ℂˣ) : ℂ) = 1 := fun u => by rw [h.om]; simp
  refine ⟨fun u y => ?_, fun u y => ?_, ?_⟩
  · rw [hom, one_mul]
    refine one_congr ?_
    rw [mul_assoc]
    exact dc_left u.2
  · rw [hom, one_mul]
    refine one_congr ?_
    have e : y * s.θ u * w⁻¹ = y * w⁻¹ * (w * s.θ u * w⁻¹) := by group
    rw [e]
    exact dc_right (h.pres u u.2)
  · refine (hf.image fun q => w⁻¹ • q).subset ?_
    intro x hx
    have hx' : s.θ x.out * w⁻¹ ∈ DC B.U a := by
      by_contra hn
      exact hx (one_neg hn)
    have h2 := (dc_sig (sgm s w) (fun u hu => sgm_mem h hu) (sgm_sgm h) a _).2 hx'
    rw [sgm_key h] at h2
    obtain ⟨p, hp, q, hq, e⟩ := h2
    have e' : x.out = w⁻¹ * (p * sgm s w a * q) := eq_inv_mul_of_mul_eq e
    refine ⟨_, ⟨⟨p, hp⟩, rfl⟩, ?_⟩
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    show ((w⁻¹ * (p * sgm s w a) : G) : G ⧸ B.U) = ((x.out : G) : G ⧸ B.U)
    rw [e']
    refine QuotientGroup.eq.2 ?_
    simpa [mul_assoc] using hq

/- English proof (translation)
Use function extensionality and compare the values at `y`. Use `show ∑ᶠ x : G ⧸ B.U, one (x.out ∈ DC B.U a) * fw B.U w 1 (x.out⁻¹ * y) = fw B.U w a y`. Establish `hz : ∀ x : G ⧸ B.U, x ≠ ((y * w⁻¹ : G) : G ⧸ B.U) → one (x.out ∈ DC B.U a) * fw B.U w 1 (x.out⁻¹ * y) = 0`. Introduce `x hx`. Establish `: ¬ (x.out⁻¹ * y * w⁻¹ ∈ DC B.U (1 : G))`.

Introduce `hm`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← QuotientGroup.out_eq' x]`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Use `dc_one.1 hm` as an intermediate fact.

Simplify `this` using `[mul_assoc]`. Rewrite using `[fw, one_neg this, mul_zero]`. Rewrite using `[finsum_eq_single _ _ hz]`. Establish `hm : (((y * w⁻¹ : G) : G ⧸ B.U)).out⁻¹ * (y * w⁻¹) ∈ B.U` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' _)`. Establish `h1 : fw B.U w 1 ((((y * w⁻¹ : G) : G ⧸ B.U)).out⁻¹ * y) = 1` using `one_pos (dc_one.2 (by simpa [mul_assoc] using hm))`.

Rewrite using `[h1, mul_one]`. Use `one_congr ?_` and prove the remaining obligations. Establish `e : y * w⁻¹ = (((y * w⁻¹ : G) : G ⧸ B.U)).out * ((((y * w⁻¹ : G) : G ⧸ B.U)).out⁻¹ * (y * w⁻¹))` using `by group`. Use `conv_rhs => rw [e]`. Conclude with `(dc_right hm).symm`.
-/
private theorem conv_left (a : G) :
    (Base.Tw.one B).conv (fun y => one (y ∈ DC B.U a)) (fw B.U w 1) = fw B.U w a := by
  funext y
  show ∑ᶠ x : G ⧸ B.U, one (x.out ∈ DC B.U a) * fw B.U w 1 (x.out⁻¹ * y) = fw B.U w a y
  have hz : ∀ x : G ⧸ B.U, x ≠ ((y * w⁻¹ : G) : G ⧸ B.U) →
      one (x.out ∈ DC B.U a) * fw B.U w 1 (x.out⁻¹ * y) = 0 := by
    intro x hx
    have : ¬ (x.out⁻¹ * y * w⁻¹ ∈ DC B.U (1 : G)) := by
      intro hm
      apply hx
      rw [← QuotientGroup.out_eq' x]
      refine QuotientGroup.eq.2 ?_
      have := dc_one.1 hm
      simpa [mul_assoc] using this
    rw [fw, one_neg this, mul_zero]
  rw [finsum_eq_single _ _ hz]
  have hm : (((y * w⁻¹ : G) : G ⧸ B.U)).out⁻¹ * (y * w⁻¹) ∈ B.U :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  have h1 : fw B.U w 1 ((((y * w⁻¹ : G) : G ⧸ B.U)).out⁻¹ * y) = 1 :=
    one_pos (dc_one.2 (by simpa [mul_assoc] using hm))
  rw [h1, mul_one]
  refine one_congr ?_
  have e : y * w⁻¹ = (((y * w⁻¹ : G) : G ⧸ B.U)).out * ((((y * w⁻¹ : G) : G ⧸ B.U)).out⁻¹ * (y * w⁻¹)) := by group
  conv_rhs => rw [e]
  exact (dc_right hm).symm

/- English proof (translation)
Use function extensionality and compare the values at `y`. Establish `hs : s.θ.symm y = s.θ y` using `(MulEquiv.symm_apply_eq _).2 (h.inv y).symm`. Use `show ∑ᶠ x : G ⧸ B.U, fw B.U w 1 (s.θ x.out) * one (x.out⁻¹ * s.θ.symm y ∈ DC B.U a) = fw B.U w (sgm s w a) y`. Rewrite using `[hs]`. Establish `hiff : ∀ x : G, s.θ x * w⁻¹ ∈ DC B.U (1 : G) ↔ w * x ∈ B.U`.

Introduce `x`. Rewrite using `[dc_one]`. Prove the components needed by the constructor for the conclusion. Introduce `hm`. Use `sgm_mem h hm` as an intermediate fact.

Rewrite `this` using `[sgm_key h]`. Then use the resulting hypothesis. Introduce `hm`. Use `sgm_mem h hm` as an intermediate fact. Rewrite `this` using `[← sgm_key h, sgm_sgm h]`. Conclude with `this`.

Establish `hz : ∀ x : G ⧸ B.U, x ≠ ((w⁻¹ : G) : G ⧸ B.U) → fw B.U w 1 (s.θ x.out) * one (x.out⁻¹ * s.θ y ∈ DC B.U a) = 0`. Introduce `x hx`. Establish `: ¬ (s.θ x.out * w⁻¹ ∈ DC B.U (1 : G))`. Introduce `hm`. Apply `hx` to reduce the goal to its premises.

Rewrite using `[← QuotientGroup.out_eq' x]`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Use `(hiff _).1 hm` as an intermediate fact. Simplify `(B.U.inv_mem this)` using `[mul_assoc]`. Rewrite using `[fw, one_neg this, zero_mul]`.

Rewrite using `[finsum_eq_single _ _ hz]`. Establish `hm : w * (((w⁻¹ : G) : G ⧸ B.U)).out ∈ B.U`. Use `QuotientGroup.eq.1 (QuotientGroup.out_eq' ((w⁻¹ : G) : G ⧸ B.U))` as an intermediate fact. Simplify `(B.U.inv_mem this)` using `[mul_assoc]`. Rewrite using `[fw, one_pos ((hiff _).2 hm), one_mul]`.

Use `one_congr ?_` and prove the remaining obligations. Establish `e : (((w⁻¹ : G) : G ⧸ B.U)).out⁻¹ * s.θ y = (w * (((w⁻¹ : G) : G ⧸ B.U)).out)⁻¹ * (w * s.θ y)` using `by group`. Rewrite using `[e, dc_left (B.U.inv_mem hm), ← twisted_sigma_identity h, dc_sig (sgm s w) (fun u hu => sgm_mem h hu) (sgm_sgm h)]`.
-/
private theorem conv_right (h : TwOk s w) (a : G) :
    s.conv (fw B.U w 1) (fun y => one (y ∈ DC B.U a)) = fw B.U w (sgm s w a) := by
  funext y
  have hs : s.θ.symm y = s.θ y := (MulEquiv.symm_apply_eq _).2 (h.inv y).symm
  show ∑ᶠ x : G ⧸ B.U, fw B.U w 1 (s.θ x.out) * one (x.out⁻¹ * s.θ.symm y ∈ DC B.U a) = fw B.U w (sgm s w a) y
  rw [hs]
  have hiff : ∀ x : G, s.θ x * w⁻¹ ∈ DC B.U (1 : G) ↔ w * x ∈ B.U := by
    intro x
    rw [dc_one]
    constructor
    · intro hm
      have := sgm_mem h hm
      rwa [sgm_key h] at this
    · intro hm
      have := sgm_mem h hm
      rw [← sgm_key h, sgm_sgm h] at this
      exact this
  have hz : ∀ x : G ⧸ B.U, x ≠ ((w⁻¹ : G) : G ⧸ B.U) →
      fw B.U w 1 (s.θ x.out) * one (x.out⁻¹ * s.θ y ∈ DC B.U a) = 0 := by
    intro x hx
    have : ¬ (s.θ x.out * w⁻¹ ∈ DC B.U (1 : G)) := by
      intro hm
      apply hx
      rw [← QuotientGroup.out_eq' x]
      refine QuotientGroup.eq.2 ?_
      have := (hiff _).1 hm
      simpa [mul_assoc] using (B.U.inv_mem this)
    rw [fw, one_neg this, zero_mul]
  rw [finsum_eq_single _ _ hz]
  have hm : w * (((w⁻¹ : G) : G ⧸ B.U)).out ∈ B.U := by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((w⁻¹ : G) : G ⧸ B.U))
    simpa [mul_assoc] using (B.U.inv_mem this)
  rw [fw, one_pos ((hiff _).2 hm), one_mul]
  refine one_congr ?_
  have e : (((w⁻¹ : G) : G ⧸ B.U)).out⁻¹ * s.θ y = (w * (((w⁻¹ : G) : G ⧸ B.U)).out)⁻¹ * (w * s.θ y) := by group
  rw [e, dc_left (B.U.inv_mem hm), ← twisted_sigma_identity h, dc_sig (sgm s w) (fun u hu => sgm_mem h hu) (sgm_sgm h)]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem tw_one_mul (s : B.Tw) : (Base.Tw.one B).mul s = s := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem tw_mul_one (s : B.Tw) : s.mul (Base.Tw.one B) = s := rfl

/- English proof (translation)
Establish `t1 : s.IsTest (fw B.U w 1)` using `isTest h 1 (by rwa [map_one])`. Establish `ta` using `(opDc Γ G V B h.om a hfa).1`. Use `⟨isTest h a hfs, ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `(Tf.rMul Γ G V B (Base.Tw.one B) s _ _ ta t1).2`. Rewrite `e` using `[tw_one_mul, conv_left]`.

Conclude with `e.symm`. Establish `e` using `(Tf.rMul Γ G V B s (Base.Tw.one B) _ _ t1 ta).2`. Rewrite `e` using `[tw_mul_one, conv_right h]`. Conclude with `e.symm`.
-/
private theorem ops (h : TwOk s w) (a : G) (hfa : AlgebraTools.FinOrb B.U B.U a) (hfs : AlgebraTools.FinOrb B.U B.U (sgm s w a))
    (hf1 : AlgebraTools.FinOrb B.U B.U (1 : G)) :
    s.IsTest (fw B.U w a) ∧
      s.R (fw B.U w a) = (Base.Tw.one B).R (fun y => one (y ∈ DC B.U a)) * s.R (fw B.U w 1) ∧
      s.R (fw B.U w (sgm s w a)) = s.R (fw B.U w 1) * (Base.Tw.one B).R (fun y => one (y ∈ DC B.U a)) := by
  have t1 : s.IsTest (fw B.U w 1) := isTest h 1 (by rwa [map_one])
  have ta := (opDc Γ G V B h.om a hfa).1
  refine ⟨isTest h a hfs, ?_, ?_⟩
  · have e := (Tf.rMul Γ G V B (Base.Tw.one B) s _ _ ta t1).2
    rw [tw_one_mul, conv_left] at e
    exact e.symm
  · have e := (Tf.rMul Γ G V B s (Base.Tw.one B) _ _ t1 ta).2
    rw [tw_mul_one, conv_right h] at e
    exact e.symm

end Abs

end UpperTheory.V.Z.Sym.So

namespace UpperTheory.V.Z.Sym.So

section Conc

/- English proof (translation)
Establish `hfin : {v | ¬ p v}.Finite` using `Filter.eventually_cofinite.1 h`. Distinguish the cases in `hall : ∀ v, p v`. Rewrite using `[one_pos hall]`. Establish `: ∀ v, one (p v) = 1` using `fun v => one_pos (hall v)`. Simplify using `only [this]`.

Conclude with `finprod_one`. Rewrite using `[one_neg hall]`. Take `⟨v, hv⟩` from `not_forall.1 hall`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset) _ ?_]`. Conclude with `Finset.prod_eq_zero (hfin.mem_toFinset.2 hv) (one_neg hv)`.

Introduce `x hx`. Simplify using `only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]`. Introduce `hp`. Conclude with `hx (one_pos hp)`.
-/
private theorem fp_one {I : Type} (p : I → Prop) (h : ∀ᶠ v in Filter.cofinite, p v) :
    ∏ᶠ v, one (p v) = one (∀ v, p v) := by
  classical
  have hfin : {v | ¬ p v}.Finite := Filter.eventually_cofinite.1 h
  by_cases hall : ∀ v, p v
  · rw [one_pos hall]
    have : ∀ v, one (p v) = 1 := fun v => one_pos (hall v)
    simp only [this]
    exact finprod_one
  · rw [one_neg hall]
    obtain ⟨v, hv⟩ := not_forall.1 hall
    rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset) _ ?_]
    · exact Finset.prod_eq_zero (hfin.mem_toFinset.2 hv) (one_neg hv)
    · intro x hx
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      intro hp
      exact hx (one_pos hp)

open Classical in
/- English proof (translation)
Rewrite using `[finprod_eq_prod_of_mulSupport_subset (s := T) f ?_]`. Rewrite using `[← Finset.prod_sdiff hST, mul_comm]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun v hv => hf v (Finset.mem_sdiff.1 hv).2`. Introduce `v hv`.

Assume the negation of the conclusion as `hn`. Establish `hn' : v ∉ T` using `by simpa using hn`. Conclude with `hv (by rw [hf v (fun h => hn' (hST h)), hc v hn'])`.
-/
private theorem split_prod {I : Type} {f c : I → ℂ} (S T : Finset I) (hST : S ⊆ T) (hc : ∀ v ∉ T, c v = 1)
    (hf : ∀ v ∉ S, f v = c v) : ∏ᶠ v, f v = (∏ v ∈ S, f v) * ∏ v ∈ T \ S, c v := by
  rw [finprod_eq_prod_of_mulSupport_subset (s := T) f ?_]
  · rw [← Finset.prod_sdiff hST, mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun v hv => hf v (Finset.mem_sdiff.1 hv).2
  · intro v hv
    by_contra hn
    have hn' : v ∉ T := by simpa using hn
    exact hv (by rw [hf v (fun h => hn' (hST h)), hc v hn'])

/- English proof (translation)
The claim follows from `Subtype.ext (Matrix.ext fun _ _ => star_star _)`.
-/
private theorem theta_theta {K : Type} [Field K] {Δ : K} (g : U3 Δ) : theta Δ (theta Δ g) = g :=
  Subtype.ext (Matrix.ext fun _ _ => star_star _)

/- English proof (translation)
Introduce `i j` and use `⟨(h i j).2, by show IsInt O (star (star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j))) rw [star_star] exact (h i j).1⟩`.
-/
private theorem theta_KU {K O : Type} [Field K] [CommRing O] [Algebra O K] {Δ : K} {g : U3 Δ} (h : g ∈ KU O Δ) :
    theta Δ g ∈ KU O Δ := fun i j =>
  ⟨(h i j).2, by
    show IsInt O (star (star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)))
    rw [star_star]
    exact (h i j).1⟩

variable {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ)

/- English proof (translation)
Establish `e : A.dat.S v = (A.V v).data (A.hs v h) (A.Ry v) (A.χ v)` using `dif_pos h`. Unfold `Dat.Jv`. Rewrite using `[if_pos (show v ∈ A.dat.Sg from h), e]`. Both sides reduce to the same expression.
-/
private theorem jv_pos {v : Pl F} (h : v ∈ A.Sg) : A.dat.Jv v = ((A.V v).J 3).comap (eU (A.hs v h)) := by
  have e : A.dat.S v = (A.V v).data (A.hs v h) (A.Ry v) (A.χ v) := dif_pos h
  unfold Dat.Jv
  rw [if_pos (show v ∈ A.dat.Sg from h), e]
  rfl

/- English proof (translation)
The claim follows from `if_neg h`.
-/
private theorem jv_neg {v : Pl F} (h : v ∉ A.Sg) : A.dat.Jv v = KU (Ov v) _ := if_neg h

private structure LocOk : Prop where
  bij : ∀ v (h : v ∈ A.Sg), Function.Bijective (eU (A.hs v h))
  th : ∀ v (h : v ∈ A.Sg) g, eU (A.hs v h) (theta _ g) = th (Kv v) 3 (eU (A.hs v h) g)

/- English proof (translation)
Establish `key : ∀ v (h : v ∈ A.Sg), _` using `fun v (h : v ∈ A.Sg) =>`. Set `q` to `(datOk F Δ A hok).2.2.1 v h`. Use `eU_facts (Kv v) (Ov v) q.1 q.2.1 (cv v Δ) (A.s v) (A.hs v h) q.2.2.1`. Conclude with `⟨fun v h => (key v h).1, fun v h => (key v h).2.1⟩`.
-/
private theorem locOk (hok : A.Ok) : LocOk A := by
  have key : ∀ v (h : v ∈ A.Sg), _ := fun v (h : v ∈ A.Sg) =>
    let q := (datOk F Δ A hok).2.2.1 v h
    eU_facts (Kv v) (Ov v) q.1 q.2.1 (cv v Δ) (A.s v) (A.hs v h) q.2.2.1
  exact ⟨fun v h => (key v h).1, fun v h => (key v h).2.1⟩

variable {A}

/- English proof (translation)
Rewrite using `[jv_pos A h]`. Use `(dcMap _ _ ℂ (eU (A.hs v h)) (L.bij v h) ((A.V v).J 3) a a).1 x` as an intermediate fact. Rewrite `this` using `[ha]`. Conclude with `this`.
-/
private theorem dc_loc (L : LocOk A) {v : Pl F} (h : v ∈ A.Sg) (x a : U3 (cv v Δ)) {e : Fin 3 → (Kv v)ˣ}
    (ha : eU (A.hs v h) a = dg e) : x ∈ DC (A.dat.Jv v) a ↔ eU (A.hs v h) x ∈ (A.V v).DC e := by
  rw [jv_pos A h]
  have := (dcMap _ _ ℂ (eU (A.hs v h)) (L.bij v h) ((A.V v).J 3) a a).1 x
  rw [ha] at this
  exact this

/- English proof (translation)
Use `choose f hf using fun v (h : v ∈ A.Sg) => (L.bij v h).2 (Phi (Kv v))`. Establish `hm : (fun v => if h : v ∈ A.Sg then f v h else 1) ∈ RP (fun v : Pl F => U3 (cv v Δ)) fun v => KU (Ov v) (cv v Δ)` using `by show ∀ᶠ v in Filter.cofinite, (if h : v ∈ A.Sg then f v h else 1) ∈ KU (Ov v) (cv v Δ)`. Use `((Finset.finite_toSet A.Sg).eventually_cofinite_notMem).mono fun v h => ?_` and prove the remaining obligations. Establish `h' : v ∉ A.Sg` using `h`. Rewrite using `[dif_neg h']`.

Conclude with `one_mem _`. Use `⟨⟨_, hm⟩, fun v h => ?_, fun v h => ?_⟩` and prove the remaining obligations. Use `show eU (A.hs v h) (if h : v ∈ A.Sg then f v h else 1) = _`. Rewrite using `[dif_pos h, hf]`. Use `show (if h : v ∈ A.Sg then f v h else 1) = 1`.

Rewrite using `[dif_neg h]`.
-/
private theorem exW (L : LocOk A) : ∃ w : GA Δ, (∀ v (h : v ∈ A.Sg), eU (A.hs v h) (w.1 v) = Phi (Kv v)) ∧
    ∀ v ∉ A.Sg, w.1 v = 1 := by
  classical
  choose f hf using fun v (h : v ∈ A.Sg) => (L.bij v h).2 (Phi (Kv v))
  have hm : (fun v => if h : v ∈ A.Sg then f v h else 1) ∈ RP (fun v : Pl F => U3 (cv v Δ)) fun v => KU (Ov v) (cv v Δ) := by
    show ∀ᶠ v in Filter.cofinite, (if h : v ∈ A.Sg then f v h else 1) ∈ KU (Ov v) (cv v Δ)
    refine ((Finset.finite_toSet A.Sg).eventually_cofinite_notMem).mono fun v h => ?_
    have h' : v ∉ A.Sg := h
    rw [dif_neg h']
    exact one_mem _
  refine ⟨⟨_, hm⟩, fun v h => ?_, fun v h => ?_⟩
  · show eU (A.hs v h) (if h : v ∈ A.Sg then f v h else 1) = _
    rw [dif_pos h, hf]
  · show (if h : v ∈ A.Sg then f v h else 1) = 1
    rw [dif_neg h]

open Classical in
/- English proof (translation)
Establish `hbox` using `(uFBox (Pl F) (GA Δ) _ _ A.dat.Jv (rpg _ _) A.Sg (fun v h => jv_neg A h) a (fun v h => by show a.1 v ∈ _`. Rewrite using `[ha.2 v h]`. Conclude with `one_mem _)).1 (y * w⁻¹)`. Set `P : Pl F → Prop` to `fun v => (v ∈ A.Sg → (y * w⁻¹).1 v ∈ DC (A.dat.Jv v) (a.1 v)) ∧ (v ∉ A.Sg → (y * w⁻¹).1 v ∈ A.dat.Jv v)`. Establish `hfac : ∀ v, (if h : v ∈ A.Sg then (A.V v).unitaryDoubleCosetIndicator (d v) (eU (A.hs v h) (y.1 v)) else one (y.1 v ∈ KU (Ov v) _)) = one (P v)`.

Introduce `v`. Distinguish the cases in `h : v ∈ A.Sg`. Rewrite using `[dif_pos h] show one _ = _`. Use `one_congr ?_` and prove the remaining obligations. Establish `e1 : eU (A.hs v h) ((y * w⁻¹).1 v) = eU (A.hs v h) (y.1 v) * (Phi (Kv v))⁻¹` using `by show eU _ (y.1 v * (w.1 v)⁻¹) = _`.

Rewrite using `[map_mul, map_inv, hw v h]`. Rewrite using `[← e1, ← dc_loc L h _ _ (ha.1 v h)]`. Conclude with `⟨fun q => ⟨fun _ => q, fun hn => absurd h hn⟩, fun q => q.1 h⟩`. Rewrite using `[dif_neg h]`. Use `one_congr ?_` and prove the remaining obligations.

Establish `e1 : (y * w⁻¹).1 v = y.1 v` using `by show y.1 v * (w.1 v)⁻¹ = _`. Rewrite using `[hw' v h]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Introduce `q`.

Conclude with `⟨fun h' => absurd h' h, fun _ => by rw [e1, jv_neg A h]; exact q⟩`. Introduce `q`. Use `q.2 h` as an intermediate fact. Rewrite `this` using `[e1, jv_neg A h]`. Then use the resulting hypothesis. Establish `hae : ∀ᶠ v in Filter.cofinite, P v`.

Establish `h0 : ∀ᶠ v in Filter.cofinite, (y * w⁻¹).1 v ∈ KU (Ov v) (cv v Δ)` using `(y * w⁻¹).2`. Use `filter_upwards [h0, (Finset.finite_toSet A.Sg).eventually_cofinite_notMem] with v h1 h2`. Establish `h2' : v ∉ A.Sg` using `h2`. Conclude with `⟨fun h => absurd h h2', fun _ => by rw [jv_neg A h2']; exact h1⟩`. Unfold `SD.F0 fw`.

Rewrite using `[finprod_congr hfac, fp_one P hae]`. Use `one_congr ?_` and prove the remaining obligations. Use `Iff.trans ?_ hbox.symm` and prove the remaining obligations. Conclude with `⟨fun q => ⟨fun v h => (q v).1 h, fun v h => (q v).2 h⟩, fun q v => ⟨q.1 v, q.2 v⟩⟩`.
-/
private theorem orbital_function_eq_weighted (L : LocOk A) {a w : GA Δ} {d : ParN F 3}
    (hw : ∀ v (h : v ∈ A.Sg), eU (A.hs v h) (w.1 v) = Phi (Kv v)) (hw' : ∀ v ∉ A.Sg, w.1 v = 1)
    (ha : A.IsElG a d) (y : GA Δ) : A.F0 d y = fw A.dat.UG w a y := by
  have hbox := (uFBox (Pl F) (GA Δ) _ _ A.dat.Jv (rpg _ _) A.Sg (fun v h => jv_neg A h) a (fun v h => by
    show a.1 v ∈ _
    rw [ha.2 v h]
    exact one_mem _)).1 (y * w⁻¹)
  let P : Pl F → Prop := fun v => (v ∈ A.Sg → (y * w⁻¹).1 v ∈ DC (A.dat.Jv v) (a.1 v)) ∧
    (v ∉ A.Sg → (y * w⁻¹).1 v ∈ A.dat.Jv v)
  have hfac : ∀ v, (if h : v ∈ A.Sg then (A.V v).unitaryDoubleCosetIndicator (d v) (eU (A.hs v h) (y.1 v)) else one (y.1 v ∈ KU (Ov v) _)) =
      one (P v) := by
    intro v
    by_cases h : v ∈ A.Sg
    · rw [dif_pos h]
      show one _ = _
      refine one_congr ?_
      have e1 : eU (A.hs v h) ((y * w⁻¹).1 v) = eU (A.hs v h) (y.1 v) * (Phi (Kv v))⁻¹ := by
        show eU _ (y.1 v * (w.1 v)⁻¹) = _
        rw [map_mul, map_inv, hw v h]
      rw [← e1, ← dc_loc L h _ _ (ha.1 v h)]
      exact ⟨fun q => ⟨fun _ => q, fun hn => absurd h hn⟩, fun q => q.1 h⟩
    · rw [dif_neg h]
      refine one_congr ?_
      have e1 : (y * w⁻¹).1 v = y.1 v := by
        show y.1 v * (w.1 v)⁻¹ = _
        rw [hw' v h]
        simp
      constructor
      · intro q
        exact ⟨fun h' => absurd h' h, fun _ => by rw [e1, jv_neg A h]; exact q⟩
      · intro q
        have := q.2 h
        rwa [e1, jv_neg A h] at this
  have hae : ∀ᶠ v in Filter.cofinite, P v := by
    have h0 : ∀ᶠ v in Filter.cofinite, (y * w⁻¹).1 v ∈ KU (Ov v) (cv v Δ) := (y * w⁻¹).2
    filter_upwards [h0, (Finset.finite_toSet A.Sg).eventually_cofinite_notMem] with v h1 h2
    have h2' : v ∉ A.Sg := h2
    exact ⟨fun h => absurd h h2', fun _ => by rw [jv_neg A h2']; exact h1⟩
  unfold SD.F0 fw
  rw [finprod_congr hfac, fp_one P hae]
  refine one_congr ?_
  refine Iff.trans ?_ hbox.symm
  exact ⟨fun q => ⟨fun v h => (q v).1 h, fun v h => (q v).2 h⟩, fun q v => ⟨q.1 v, q.2 v⟩⟩

/- English proof (translation)
Use `(uFBox (Pl F) (GA Δ) _ _ A.dat.Jv (rpg _ _) A.Sg (fun v h => jv_neg A h) a (fun v h => by show a.1 v ∈ _` and prove the remaining obligations. Rewrite using `[ha.2 v h]`. Conclude with `one_mem _)).2.1 fun v h => ?_`. Rewrite using `[jv_pos A h]`. Conclude with `((dcMap _ _ ℂ (eU (A.hs v h)) (L.bij v h) ((A.V v).J 3) (a.1 v) (a.1 v)).2.1).2 (((finFacts (Kv v) (A.V v)).2.2.2.2.2 3).1 _)`.
-/
private theorem el_fin (L : LocOk A) {a : GA Δ} {d : ParN F 3} (ha : A.IsElG a d) :
    AlgebraTools.FinOrb A.dat.UG A.dat.UG a := by
  refine (uFBox (Pl F) (GA Δ) _ _ A.dat.Jv (rpg _ _) A.Sg (fun v h => jv_neg A h) a (fun v h => by
    show a.1 v ∈ _
    rw [ha.2 v h]
    exact one_mem _)).2.1 fun v h => ?_
  rw [jv_pos A h]
  exact ((dcMap _ _ ℂ (eU (A.hs v h)) (L.bij v h) ((A.V v).J 3) (a.1 v) (a.1 v)).2.1).2
    (((finFacts (Kv v) (A.V v)).2.2.2.2.2 3).1 _)

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ch : F → ℂ} {B : Base (U3 Δ) (GA Δ) V} {s : B.Tw}

/- English proof (translation)
Use `⟨hB.ω, fun g => ?_, ?_, fun u hu => ?_⟩` and prove the remaining obligations. Use `Subtype.ext (funext fun v => ?_)` and prove the remaining obligations. Rewrite using `[hB.θ, hB.θ, theta_theta]`. Use `Subtype.ext (funext fun v => ?_)` and prove the remaining obligations. Rewrite using `[hB.θ]`.

Use `show _ = (w.1 v)⁻¹`. Distinguish the cases in `h : v ∈ A.Sg`. Apply `(L.bij v h).1` to reduce the goal to its premises. Rewrite using `[L.th v h, map_inv, hw v h, (thFacts (Kv v) (A.V v)).2.2.2.2.1]`. Rewrite using `[hw' v h]`.

Simplify using the standard rewrite rules. Rewrite `hu`, the goal using `[hB.U]`. Establish `mem` using `(datOk F Δ A hok).2.2.2.1`. Rewrite `hu`, the goal using `[mem]`. Use `⟨fun v h => ?_, fun v h => ?_⟩` and prove the remaining obligations.

Use `(thFacts (Kv v) (A.V v)).2.1 _ (hu.1 v h) show eU _ (w.1 v * (s.θ u).1 v * (w.1 v)⁻¹) ∈ _` as an intermediate fact. Rewrite using `[hB.θ, map_mul, map_mul, map_inv, hw v h, L.th v h]`. Conclude with `this`. Use `show w.1 v * (s.θ u).1 v * (w.1 v)⁻¹ ∈ _`. Rewrite using `[hB.θ, hw' v h]`.

Simplify using `using theta_KU (hu.2 v h)`.
-/
private theorem twOk (hok : A.Ok) (L : LocOk A) (hB : A.dat.IsBG ch B s) {w : GA Δ}
    (hw : ∀ v (h : v ∈ A.Sg), eU (A.hs v h) (w.1 v) = Phi (Kv v)) (hw' : ∀ v ∉ A.Sg, w.1 v = 1) : TwOk s w := by
  refine ⟨hB.ω, fun g => ?_, ?_, fun u hu => ?_⟩
  · refine Subtype.ext (funext fun v => ?_)
    rw [hB.θ, hB.θ, theta_theta]
  · refine Subtype.ext (funext fun v => ?_)
    rw [hB.θ]
    show _ = (w.1 v)⁻¹
    by_cases h : v ∈ A.Sg
    · apply (L.bij v h).1
      rw [L.th v h, map_inv, hw v h, (thFacts (Kv v) (A.V v)).2.2.2.2.1]
    · rw [hw' v h]
      simp
  · rw [hB.U] at hu ⊢
    have mem := (datOk F Δ A hok).2.2.2.1
    rw [mem] at hu ⊢
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · have := (thFacts (Kv v) (A.V v)).2.1 _ (hu.1 v h)
      show eU _ (w.1 v * (s.θ u).1 v * (w.1 v)⁻¹) ∈ _
      rw [hB.θ, map_mul, map_mul, map_inv, hw v h, L.th v h]
      exact this
    · show w.1 v * (s.θ u).1 v * (w.1 v)⁻¹ ∈ _
      rw [hB.θ, hw' v h]
      simpa using theta_KU (hu.2 v h)

/- English proof (translation)
Use `⟨fun v h => ?_, fun v h => ?_⟩` and prove the remaining obligations. Use `show eU _ (w.1 v * (s.θ a).1 v * (w.1 v)⁻¹) = _`. Rewrite using `[hB.θ, map_mul, map_mul, map_inv, hw v h, L.th v h, ha.1 v h]`. Apply the tactic sequence `have e : d v = ![d v 0, d v 1, d v 2] := funext fun i => by fin_cases i <;> rfl`. Use `(thFacts (Kv v) (A.V v)).2.2.1 (d v 0) (d v 1) (d v 2)` as an intermediate fact.

Rewrite `this` using `[← e]`. Conclude with `this`. Use `show w.1 v * (s.θ a).1 v * (w.1 v)⁻¹ = 1`. Rewrite using `[hB.θ, hw' v h, ha.2 v h]`. Simplify using the standard rewrite rules.
-/
private theorem el_sg (L : LocOk A) (hB : A.dat.IsBG ch B s) {w : GA Δ}
    (hw : ∀ v (h : v ∈ A.Sg), eU (A.hs v h) (w.1 v) = Phi (Kv v)) (hw' : ∀ v ∉ A.Sg, w.1 v = 1)
    {a : GA Δ} {d : ParN F 3} (ha : A.IsElG a d) : A.IsElG (sgm s w a) (SD.sg d) := by
  refine ⟨fun v h => ?_, fun v h => ?_⟩
  · show eU _ (w.1 v * (s.θ a).1 v * (w.1 v)⁻¹) = _
    rw [hB.θ, map_mul, map_mul, map_inv, hw v h, L.th v h, ha.1 v h]
    have e : d v = ![d v 0, d v 1, d v 2] := funext fun i => by fin_cases i <;> rfl
    have := (thFacts (Kv v) (A.V v)).2.2.1 (d v 0) (d v 1) (d v 2)
    rw [← e] at this
    exact this
  · show w.1 v * (s.θ a).1 v * (w.1 v)⁻¹ = 1
    rw [hB.θ, hw' v h, ha.2 v h]
    simp

/- English proof (translation)
Use `⟨fun v h => ?_, fun v h => rfl⟩` and prove the remaining obligations. Use `show eU (A.hs v h) 1 = diagT _ _ 1`. Rewrite using `[map_one, map_one]`.
-/
private theorem el_one : A.IsElG (1 : GA Δ) (1 : ParN F 3) := by
  refine ⟨fun v h => ?_, fun v h => rfl⟩
  show eU (A.hs v h) 1 = diagT _ _ 1
  rw [map_one, map_one]

open Classical in
/- English proof (translation)
Establish `hfin : {v | g.1 v ∉ KU (Ov v) (cv v Δ)}.Finite` using `Filter.eventually_cofinite.1 g.2`. Set `T : Finset (Pl F)` to `A.Sg ∪ hfin.toFinset`. Set `c : Pl F → ℂ` to `fun v => one (g.1 v ∈ KU (Ov v) (cv v Δ))`. Establish `hc : ∀ v ∉ T, c v = 1` using `fun v hv => one_pos (by`. Assume the negation of the conclusion as `hn`.

Conclude with `hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hn)))`. Establish `hST : A.Sg ⊆ T` using `Finset.subset_union_left`. Establish `e1 : A.dat.FG t g = (∏ v ∈ A.Sg, A.dat.fGv t v (g.1 v)) * ∏ v ∈ T \ A.Sg, c v`. Conclude with `split_prod (f := fun v => A.dat.fGv t v (g.1 v)) (c := c) _ _ hST hc fun v h => if_neg h`. Establish `e2 : ∀ y, A.F0 (A.dG t y) g = (∏ v ∈ A.Sg, if h : v ∈ A.Sg then (A.V v).unitaryDoubleCosetIndicator (A.dG t y v) (eU (A.hs v h) (g.1 v)) else one (g.1 v ∈ KU (Ov v) _)) * ∏ v ∈ T \ A.Sg, c v` using `fun y => by`.

Conclude with `split_prod (f := fun v => if h : v ∈ A.Sg then (A.V v).unitaryDoubleCosetIndicator (A.dG t y v) (eU (A.hs v h) (g.1 v)) else one (g.1 v ∈ KU (Ov v) _)) (c := c) _ _ hST hc fun v h => dif_neg h`. Set `b : ∀ v : A.Sg, (Kv v.1)ˣ → ℂ` to `fun v r => (A.V v.1).unitaryDoubleCosetIndicator ![t v.1 * (unif (Kv v.1))⁻¹, r, (unif (Kv v.1))⁻¹] (eU (A.hs v.1 v.2) (g.1 v.1))`. Establish `l1 : ∏ v ∈ A.Sg, A.dat.fGv t v (g.1 v) = ∏ v : A.Sg, ∑ r ∈ A.Ry v.1, b v r`. Rewrite using `[← Finset.prod_coe_sort A.Sg]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations.

Establish `e : A.dat.S v.1 = (A.V v.1).data (A.hs v.1 v.2) (A.Ry v.1) (A.χ v.1)` using `dif_pos v.2`. Unfold `Dat.fGv`. Rewrite using `[if_pos (show v.1 ∈ A.dat.Sg from v.2), e]`. Both sides reduce to the same expression. Establish `l2 : ∀ y, (∏ v ∈ A.Sg, if h : v ∈ A.Sg then (A.V v).unitaryDoubleCosetIndicator (A.dG t y v) (eU (A.hs v h) (g.1 v)) else one (g.1 v ∈ KU (Ov v) _)) = ∏ v : A.Sg, b v (y v)` using `fun y => by`.

Rewrite using `[← Finset.prod_coe_sort A.Sg]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos v.2]`. Establish `e : A.dG t y v.1 = ![t v.1 * (unif (Kv v.1))⁻¹, y v, (unif (Kv v.1))⁻¹]`. Unfold `SD.dG`.

Rewrite using `[dif_pos v.2]`. Rewrite using `[e]`. Rewrite using `[e1, l1]`. Simplify using `only [e2, l2]`. Rewrite using `[← Finset.sum_mul]`.

Use `congr 1`. Rewrite using `[Finset.prod_univ_sum]`. Both sides reduce to the same expression.
-/
private theorem FG_eq (t : Dat.Par F) (g : GA Δ) : A.dat.FG t g = ∑ y ∈ A.Ys, A.F0 (A.dG t y) g := by
  have hfin : {v | g.1 v ∉ KU (Ov v) (cv v Δ)}.Finite := Filter.eventually_cofinite.1 g.2
  let T : Finset (Pl F) := A.Sg ∪ hfin.toFinset
  let c : Pl F → ℂ := fun v => one (g.1 v ∈ KU (Ov v) (cv v Δ))
  have hc : ∀ v ∉ T, c v = 1 := fun v hv => one_pos (by
    by_contra hn
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hn)))
  have hST : A.Sg ⊆ T := Finset.subset_union_left
  have e1 : A.dat.FG t g = (∏ v ∈ A.Sg, A.dat.fGv t v (g.1 v)) * ∏ v ∈ T \ A.Sg, c v := by
    exact split_prod (f := fun v => A.dat.fGv t v (g.1 v)) (c := c) _ _ hST hc fun v h => if_neg h
  have e2 : ∀ y, A.F0 (A.dG t y) g = (∏ v ∈ A.Sg, if h : v ∈ A.Sg then (A.V v).unitaryDoubleCosetIndicator (A.dG t y v) (eU (A.hs v h) (g.1 v))
      else one (g.1 v ∈ KU (Ov v) _)) * ∏ v ∈ T \ A.Sg, c v := fun y => by
    exact split_prod (f := fun v => if h : v ∈ A.Sg then (A.V v).unitaryDoubleCosetIndicator (A.dG t y v) (eU (A.hs v h) (g.1 v))
      else one (g.1 v ∈ KU (Ov v) _)) (c := c) _ _ hST hc fun v h => dif_neg h
  let b : ∀ v : A.Sg, (Kv v.1)ˣ → ℂ := fun v r =>
    (A.V v.1).unitaryDoubleCosetIndicator ![t v.1 * (unif (Kv v.1))⁻¹, r, (unif (Kv v.1))⁻¹] (eU (A.hs v.1 v.2) (g.1 v.1))
  have l1 : ∏ v ∈ A.Sg, A.dat.fGv t v (g.1 v) = ∏ v : A.Sg, ∑ r ∈ A.Ry v.1, b v r := by
    rw [← Finset.prod_coe_sort A.Sg]
    refine Finset.prod_congr rfl fun v _ => ?_
    have e : A.dat.S v.1 = (A.V v.1).data (A.hs v.1 v.2) (A.Ry v.1) (A.χ v.1) := dif_pos v.2
    unfold Dat.fGv
    rw [if_pos (show v.1 ∈ A.dat.Sg from v.2), e]
    rfl
  have l2 : ∀ y, (∏ v ∈ A.Sg, if h : v ∈ A.Sg then (A.V v).unitaryDoubleCosetIndicator (A.dG t y v) (eU (A.hs v h) (g.1 v))
      else one (g.1 v ∈ KU (Ov v) _)) = ∏ v : A.Sg, b v (y v) := fun y => by
    rw [← Finset.prod_coe_sort A.Sg]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [dif_pos v.2]
    have e : A.dG t y v.1 = ![t v.1 * (unif (Kv v.1))⁻¹, y v, (unif (Kv v.1))⁻¹] := by
      unfold SD.dG
      rw [dif_pos v.2]
    rw [e]
  rw [e1, l1]
  simp only [e2, l2]
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.prod_univ_sum]
  rfl

end Conc

end UpperTheory.V.Z.Sym.So

/- English proof (translation)
Introduce `F _ _ Δ A hok V _ _ ch B s hB`. Establish `L` using `locOk A hok`. Take `⟨w, hw, hw'⟩` from `exW L`. Establish `T` using `twOk hok L hB hw hw'`. Establish `hU` using `hB.U`.

Establish `hfin : ∀ a d, A.IsElG a d → AlgebraTools.FinOrb B.U B.U a` using `fun a d ha => hU ▸ el_fin L ha`. Establish `hF : ∀ a d, A.IsElG a d → A.F0 d = fw B.U w a` using `fun a d ha => funext fun y => by`. Rewrite using `[hU]`. Conclude with `orbital_function_eq_weighted L hw hw' ha y`. Use `⟨fun d g hg => ?_, fun t _ => funext fun g => FG_eq t g⟩` and prove the remaining obligations.

Establish `hs` using `el_sg L hB hw hw' hg`. Establish `h1 : A.IsElG (1 : GA Δ) (1 : ParN F 3)` using `el_one`. Take `⟨o1, o2, o3⟩` from `ops T g (hfin _ _ hg) (hfin _ _ hs) (hfin _ _ h1)`. Rewrite using `[hF _ _ hg, hF _ _ hs, hF _ _ h1]`. Conclude with `⟨o1, o2, o3⟩`.
-/
theorem UpperTheory.V.Z.Sym.So.hecke_operators_on_twisted_base_function :
    UpperTheory.V.Z.Sym.So.UnitaryThreeTestFunctionHeckeRelations := by
  intro F _ _ Δ A hok V _ _ ch B s hB
  have L := locOk A hok
  obtain ⟨w, hw, hw'⟩ := exW L
  have T := twOk hok L hB hw hw'
  have hU := hB.U
  have hfin : ∀ a d, A.IsElG a d → AlgebraTools.FinOrb B.U B.U a := fun a d ha => hU ▸ el_fin L ha
  have hF : ∀ a d, A.IsElG a d → A.F0 d = fw B.U w a := fun a d ha => funext fun y => by
    rw [hU]
    exact orbital_function_eq_weighted L hw hw' ha y
  refine ⟨fun d g hg => ?_, fun t _ => funext fun g => FG_eq t g⟩
  have hs := el_sg L hB hw hw' hg
  have h1 : A.IsElG (1 : GA Δ) (1 : ParN F 3) := el_one
  obtain ⟨o1, o2, o3⟩ := ops T g (hfin _ _ hg) (hfin _ _ hs) (hfin _ _ h1)
  rw [hF _ _ hg, hF _ _ hs, hF _ _ h1]
  exact ⟨o1, o2, o3⟩

end
