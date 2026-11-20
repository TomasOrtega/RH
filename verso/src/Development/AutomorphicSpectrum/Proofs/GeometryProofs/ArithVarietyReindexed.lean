import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGenFibreChartDeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartScalingIndep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PAdjoinIndepRelfinrank
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsPowOfMemCellSec

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.GenFib

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

section Top

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [CharZero Ω]

/- English proof (translation)
Establish `hy : ∀ f : MRing J, aeval (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.ratioPt y c) f ∈ blockFnField y`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => rw [map_add]`.

Conclude with `add_mem hp hq`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul, aeval_X]`. Conclude with `mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨i, ⟨i.1, c i.1⟩, rfl, rfl⟩)`. Use `eq_top_iff.2 fun s _ => ?_` and prove the remaining obligations.

Take `⟨d, g, h, hg, hh, hne, e⟩` from `hb s`. Establish `eg` using `GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.aeval_eq_ratioPt y c hc hg`. Establish `eh` using `GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.aeval_eq_ratioPt y c hc hh`. Establish `hU : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)`. Rewrite `hne` using `[eh]`.

Establish `hH` using `left_ne_zero_of_mul hne`. Rewrite `e` using `[eg, eh, ← _root_.mul_assoc]`. Establish `e2` using `mul_right_cancel₀ hU e`. Establish `: s = aeval (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.ratioPt y c) g / aeval (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.ratioPt y c) h`. Rewrite using `[e2]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `div_mem (hy g) (hy h)`.
-/
theorem blockFnField_eq_top (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hb : Birational y) : blockFnField y = ⊤ := by
  have hy : ∀ f : MRing J,
      aeval (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.ratioPt y c) f ∈ blockFnField y := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, aeval_X]
      exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨i, ⟨i.1, c i.1⟩, rfl, rfl⟩)
  refine eq_top_iff.2 fun s _ => ?_
  obtain ⟨d, g, h, hg, hh, hne, e⟩ := hb s
  have eg := GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.aeval_eq_ratioPt y c hc hg
  have eh := GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.aeval_eq_ratioPt y c hc hh
  have hU : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  rw [eh] at hne
  have hH := left_ne_zero_of_mul hne
  rw [eg, eh, ← _root_.mul_assoc] at e
  have e2 := mul_right_cancel₀ hU e
  have : s = aeval (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.ratioPt y c) g /
      aeval (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.ratioPt y c) h := by
    rw [e2]; field_simp
  rw [this]
  exact div_mem (hy g) (hy h)

end Top

section Gen

/- English proof (translation)
Proceed by induction on `hc using IntermediateField.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨p, rfl⟩` from `hx`. Conclude with `⟨X p, 1, by simp, by simp⟩`. Consider the case `algebraMap r`.

Use `⟨C r.num, C (r.den : ℤ), by simp, ?_⟩` and prove the remaining obligations. Simplify using `[Rat.cast_def]`. Consider the case `add x y _ _ hx hy`. Take `⟨f₁, g₁, h₁, rfl⟩` from `hx`. Take `⟨f₂, g₂, h₂, rfl⟩` from `hy`.

Use `⟨f₁ * g₂ + f₂ * g₁, g₁ * g₂, by simpa using ⟨h₁, h₂⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul]`. Clear the denominators using the available nonvanishing facts. Consider the case `inv x _ hx`. Take `⟨f, g, h, rfl⟩` from `hx`.

Distinguish the cases in `h0 : aeval z f = 0`. Conclude with `⟨0, 1, by simp, by simp [h0]⟩`. Conclude with `⟨g, f, h0, by simp⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨f₁, g₁, h₁, rfl⟩` from `hx`.

Take `⟨f₂, g₂, h₂, rfl⟩` from `hy`. Use `⟨f₁ * f₂, g₁ * g₂, by simpa using ⟨h₁, h₂⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_quot_of_mem_adjoin {L I : Type} [Field L] [CharZero L] (z : I → L) {c : L}
    (hc : c ∈ IntermediateField.adjoin ℚ (Set.range z)) :
    ∃ f g : MvPolynomial I ℤ, aeval z g ≠ 0 ∧ c = aeval z f / aeval z g := by
  induction hc using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨X p, 1, by simp, by simp⟩
  | algebraMap r =>
    refine ⟨C r.num, C (r.den : ℤ), by simp, ?_⟩
    simp [Rat.cast_def]
  | add x y _ _ hx hy =>
    obtain ⟨f₁, g₁, h₁, rfl⟩ := hx
    obtain ⟨f₂, g₂, h₂, rfl⟩ := hy
    refine ⟨f₁ * g₂ + f₂ * g₁, g₁ * g₂, by simpa using ⟨h₁, h₂⟩, ?_⟩
    simp only [map_add, map_mul]
    field_simp
  | inv x _ hx =>
    obtain ⟨f, g, h, rfl⟩ := hx
    by_cases h0 : aeval z f = 0
    · exact ⟨0, 1, by simp, by simp [h0]⟩
    · exact ⟨g, f, h0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨f₁, g₁, h₁, rfl⟩ := hx
    obtain ⟨f₂, g₂, h₂, rfl⟩ := hy
    refine ⟨f₁ * f₂, g₁ * g₂, by simpa using ⟨h₁, h₂⟩, ?_⟩
    simp only [map_mul]
    field_simp

end Gen

section Point

variable {K : Type} {J : K → Type} {Ω : Type} [Field Ω]

def Fn (K Ω : Type) [Field Ω] : Type := FractionRing (MvPolynomial K Ω)

instance : Field (Fn K Ω) := inferInstanceAs (Field (FractionRing (MvPolynomial K Ω)))

def emb (K Ω : Type) [Field Ω] : MvPolynomial K Ω →+* Fn K Ω :=
  algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω))

/- English proof (translation)
The claim follows from `IsFractionRing.injective (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω))`.
-/
theorem emb_injective : Function.Injective (emb K Ω) :=
  IsFractionRing.injective (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω))

def cst (K Ω : Type) [Field Ω] : Ω →+* Fn K Ω := (emb K Ω).comp C

def tv (Ω : Type) [Field Ω] (k : K) : Fn K Ω := emb K Ω (X k)

/- English proof (translation)
Rewrite using `[tv, Ne, map_eq_zero_iff _ emb_injective]`. Conclude with `X_ne_zero k`.
-/
theorem tv_ne_zero (k : K) : tv Ω k ≠ 0 := by
  rw [tv, Ne, map_eq_zero_iff _ emb_injective]
  exact X_ne_zero k

instance [CharZero Ω] : CharZero (Fn K Ω) := charZero_of_injective_ringHom (cst K Ω).injective

def xPt (y : (Σ k, J k) → Ω) : (Σ k, J k) → Fn K Ω := fun p => cst K Ω (y p) * tv Ω p.1

/- English proof (translation)
The claim follows from `mul_ne_zero ((map_ne_zero _).2 h) (tv_ne_zero _)`.
-/
theorem xPt_ne_zero {y : (Σ k, J k) → Ω} {p : Σ k, J k} (h : y p ≠ 0) : xPt y p ≠ 0 :=
  mul_ne_zero ((map_ne_zero _).2 h) (tv_ne_zero _)

/- English proof (translation)
Rewrite using `[xPt, xPt, h, mul_div_mul_right _ _ (tv_ne_zero _), map_div₀]`.
-/
theorem xPt_div_xPt (y : (Σ k, J k) → Ω) {p q : Σ k, J k} (h : p.1 = q.1) :
    xPt y p / xPt y q = cst K Ω (y p / y q) := by
  rw [xPt, xPt, h, mul_div_mul_right _ _ (tv_ne_zero _), map_div₀]

variable [∀ k, Fintype (J k)] [Fintype K]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [mConeMap]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p n hp => simp [map_mul, hp, mConeMap, xPt, cst, tv]`.
-/
theorem aeval_xPt (y : (Σ k, J k) → Ω) (f : MRing J) :
    aeval (xPt y) f = emb K Ω (mConeMap y f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp [map_mul, hp, mConeMap, xPt, cst, tv]

/- English proof (translation)
Rewrite using `[aeval_xPt, map_eq_zero_iff _ emb_injective]`. Both sides reduce to the same expression.
-/
theorem aeval_xPt_eq_zero_iff (y : (Σ k, J k) → Ω) (f : MRing J) :
    aeval (xPt y) f = 0 ↔ f ∈ mCoordIdeal y := by
  rw [aeval_xPt, map_eq_zero_iff _ emb_injective]
  rfl

end Point

section Model

variable {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [CharZero Ω]

abbrev imgField (y : (Σ k, J k) → Ω) (v : (Σ k, J₀ k) → Σ k, J k) : IntermediateField ℚ (Fn K Ω) :=
  IntermediateField.adjoin ℚ (Set.range fun p => xPt y (v p))

def imgPt (y : (Σ k, J k) → Ω) (v : (Σ k, J₀ k) → Σ k, J k) : (Σ k, J₀ k) → imgField y v :=
  fun p => ⟨xPt y (v p), IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩⟩

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp only [map_add, IntermediateField.coe_add, hp, hq]`. Consider the case `mul_X p n hp => simp only [map_mul, MulMemClass.coe_mul, hp, aeval_X, imgPt]`.
-/
theorem coe_aeval_imgPt (y : (Σ k, J k) → Ω) (v : (Σ k, J₀ k) → Σ k, J k) (f : MRing J₀) :
    ((aeval (imgPt y v) f : imgField y v) : Fn K Ω) = aeval (fun p => xPt y (v p)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, IntermediateField.coe_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, MulMemClass.coe_mul, hp, aeval_X, imgPt]

def genFib (y : (Σ k, J k) → Ω) (v : (Σ k, J₀ k) → Σ k, J k) : GenFibre v (mCoordIdeal y) where
  Φ := imgField y v
  Φ' := Fn K Ω
  x := imgPt y v
  x' := xPt y
  ker_x := by
    ext f
    rw [RingHom.mem_ker]
    show _ ↔ rename v f ∈ mCoordIdeal y
    rw [← aeval_xPt_eq_zero_iff, aeval_rename, ← Subtype.coe_inj]
    exact (coe_aeval_imgPt y v f).symm ▸ Iff.rfl
  gen := by
    intro c
    obtain ⟨f, g, hg, e⟩ := exists_quot_of_mem_adjoin (fun p => xPt y (v p)) c.2
    refine ⟨f, g, ?_, ?_⟩
    · intro h0
      apply hg
      rw [← coe_aeval_imgPt, h0]
      rfl
    · apply Subtype.ext
      rw [IntermediateField.coe_div, coe_aeval_imgPt, coe_aeval_imgPt]
      exact e
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker]
    exact aeval_xPt_eq_zero_iff y f
  compat := fun _ => rfl

end Model

section Degree

variable {K₀ : Type} {J₀ : K₀ → Type} {K : Type} {J : K → Type} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
  [CharZero Ω₀] [CharZero Ω]

/- English proof (translation)
Rewrite using `[blockFnField, blockFnField, IntermediateField.adjoin_map]`. Use `congr 1`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, q, h, rfl⟩`.

Conclude with `⟨_, ⟨p, q, h, rfl⟩, (xPt_div_xPt y h).symm⟩`. Introduce and unpack `⟨_, ⟨p, q, h, rfl⟩, rfl⟩`. Conclude with `⟨p, q, h, (xPt_div_xPt y h).symm⟩`.
-/
theorem blockFnField_xPt (y : (Σ k, J k) → Ω) :
    blockFnField (xPt y) = (blockFnField y).map (cst K Ω).toRatAlgHom := by
  rw [blockFnField, blockFnField, IntermediateField.adjoin_map]
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨p, q, h, rfl⟩, (xPt_div_xPt y h).symm⟩
  · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
    exact ⟨p, q, h, (xPt_div_xPt y h).symm⟩

/- English proof (translation)
Establish `key : ∀ p q : Σ k, J₀ k, p.1 = q.1 → (xPt y ∘ v) p / (xPt y ∘ v) q = cst K Ω (i (y₀ p / y₀ q))`. Introduce `p q h`. Rewrite using `[Function.comp, Function.comp, xPt_div_xPt y (by rw [hv, hv, h]), hy, hy, map_div₀ i]`. Rewrite using `[blockFnField, blockFnField, IntermediateField.adjoin_map, IntermediateField.adjoin_map]`. Use `congr 1`.

Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, q, h, rfl⟩`. Conclude with `⟨_, ⟨_, ⟨p, q, h, rfl⟩, rfl⟩, (key p q h).symm⟩`. Introduce and unpack `⟨_, ⟨_, ⟨p, q, h, rfl⟩, rfl⟩, rfl⟩`.

Conclude with `⟨p, q, h, (key p q h).symm⟩`.
-/
theorem blockFnField_xPt_comp (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K)
    (v : (Σ k, J₀ k) → Σ k, J k) (hv : ∀ p, (v p).1 = bk p.1) (i : Ω₀ →+* Ω)
    (hy : ∀ p, y (v p) = i (y₀ p)) :
    blockFnField (xPt y ∘ v) =
      ((blockFnField y₀).map i.toRatAlgHom).map (cst K Ω).toRatAlgHom := by
  have key : ∀ p q : Σ k, J₀ k, p.1 = q.1 →
      (xPt y ∘ v) p / (xPt y ∘ v) q = cst K Ω (i (y₀ p / y₀ q)) := by
    intro p q h
    rw [Function.comp, Function.comp, xPt_div_xPt y (by rw [hv, hv, h]), hy, hy, map_div₀ i]
  rw [blockFnField, blockFnField, IntermediateField.adjoin_map, IntermediateField.adjoin_map]
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨_, ⟨p, q, h, rfl⟩, rfl⟩, (key p q h).symm⟩
  · rintro ⟨_, ⟨_, ⟨p, q, h, rfl⟩, rfl⟩, rfl⟩
    exact ⟨p, q, h, (key p q h).symm⟩

/- English proof (translation)
Use `letI := i.toAlgebra`. Rewrite using `[← AlgHom.fieldRange_eq_map]`. Set `e` to `AlgEquiv.ofInjectiveField i.toRatAlgHom`. Use `symm`. Use `Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl Ω) ?_` and prove the remaining obligations.

Use extensionality with `a`. Both sides reduce to the same expression.
-/
theorem finrank_map_top (i : Ω₀ →+* Ω) :
    Module.finrank ((⊤ : IntermediateField ℚ Ω₀).map i.toRatAlgHom) Ω =
      (letI := i.toAlgebra; Module.finrank Ω₀ Ω) := by
  letI := i.toAlgebra
  rw [← AlgHom.fieldRange_eq_map]
  let e := AlgEquiv.ofInjectiveField i.toRatAlgHom
  symm
  refine Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl Ω) ?_
  ext a
  rfl

/- English proof (translation)
Rewrite using `[blockFnField_xPt_comp y₀ y bk v hv i hy, blockFnField_xPt, h₀, h, IntermediateField.relfinrank_map_map, IntermediateField.relfinrank_top_right, finrank_map_top]`.
-/
theorem relfinrank_block (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K)
    (v : (Σ k, J₀ k) → Σ k, J k) (hv : ∀ p, (v p).1 = bk p.1) (i : Ω₀ →+* Ω)
    (hy : ∀ p, y (v p) = i (y₀ p)) (h₀ : blockFnField y₀ = ⊤) (h : blockFnField y = ⊤) :
    IntermediateField.relfinrank (blockFnField (xPt y ∘ v)) (blockFnField (xPt y)) =
      (letI := i.toAlgebra; Module.finrank Ω₀ Ω) := by
  rw [blockFnField_xPt_comp y₀ y bk v hv i hy, blockFnField_xPt, h₀, h,
    IntermediateField.relfinrank_map_map, IntermediateField.relfinrank_top_right, finrank_map_top]

end Degree

/- English proof (translation)
Introduce `K₀ K _ _ J₀ J _ _ Ω₀ Ω _ _ _ y₀ y bk bx i D d hbk hy hA₀ hA hb₀ hb hd _`. Use `haveI : CharZero Ω₀ := i.charZero`. Establish `hrel : ∀ {L : Type} {I : L → Type} [∀ k, Fintype (I k)] {F : Type} [Field F] (w : (Σ k, I k) → F) (_ : (mCoordIdeal w).IsPrime ∧ IsRelevant (mCoordIdeal w)), ∀ k, ∃ a, w ⟨k, a⟩ ≠ 0`. Introduce `L I _ F _ w h k`. Take `⟨a, ha⟩` from `h.2 k`.

Use `⟨a, fun h0 => ha ?_⟩` and prove the remaining obligations. Use `show mConeMap w (X ⟨k, a⟩) = 0`. Simplify using `[mConeMap, h0]`. Use `choose c₀ hc₀ using hrel y₀ ⟨hA₀.2.1.1, hA₀.2.1.2.2⟩`. Use `choose c hc using hrel y ⟨hA.2.1.1, hA.2.1.2.2⟩`.

Establish `hv` using `GlobalTheory.CompanionTheory.Ar.Chg.isBlockMap_blkV bx hbk`. Set `v` to `GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx`. Establish `hyv : ∀ p, y (v p) = i (y₀ p)` using `fun p => hy p.1 p.2`. Set `G` to `genFib y v`. Use `haveI : CharZero G.Φ' := inferInstanceAs (CharZero (Fn K Ω))`.

Set `ch : ∀ k : FibreBlock bk, J k.1` to `fun k => c k.1`. Establish `hch : ∀ k : FibreBlock bk, G.x' ⟨k.1, ch k⟩ ≠ 0` using `fun k => xPt_ne_zero (hc k.1)`. Establish `hx : ∀ k, G.x ⟨k, c₀ k⟩ ≠ 0`. Introduce `k h0`. Establish `h1 : xPt y (v ⟨k, c₀ k⟩) = 0` using `congrArg Subtype.val h0`.

Use `xPt_ne_zero ?_ h1` and prove the remaining obligations. Rewrite using `[hyv]`. Conclude with `(map_ne_zero i).2 (hc₀ k)`. Use `⟨G, ch, hch, ?_⟩` and prove the remaining obligations. Establish `main` using `GroundTheory.Heights₂.Heights.Targets.GenFibreChartDeg.proof GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.proof GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.proof K₀ J₀ K J bk v (mCoordIdeal y) G c₀ ch hv hA.2.1.2.1 hx hch`.

Use `main.trans ?_` and prove the remaining obligations. Rewrite using `[← hd]`. Conclude with `relfinrank_block y₀ y bk v (fun _ => rfl) i hyv (blockFnField_eq_top y₀ c₀ hc₀ hb₀) (blockFnField_eq_top y c hc hb)`.
-/
theorem exists_genFibre_chart_degree : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (D d : ℕ), Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → IsArithVar (mCoordIdeal y₀) (D + 1) → IsArithVar (mCoordIdeal y) (D + 1) → Birational y₀ → Birational y → (letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) → 0 < d → ∃ (Gf : GenFibre (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (mCoordIdeal y)) (ch : ∀ k : FibreBlock bk, J k.1), (∀ k : FibreBlock bk, Gf.x' ⟨k.1, ch k⟩ ≠ 0) ∧ Module.finrank Gf.Φ (IntermediateField.adjoin Gf.Φ (Set.range fun q : Σ k : FibreBlock bk, J k.1 => Gf.x' ⟨q.1.1, q.2⟩ / Gf.x' ⟨q.1.1, ch q.1⟩)) = d := by
  intro K₀ K _ _ J₀ J _ _ Ω₀ Ω _ _ _ y₀ y bk bx i D d hbk hy hA₀ hA hb₀ hb hd _
  haveI : CharZero Ω₀ := i.charZero
  have hrel : ∀ {L : Type} {I : L → Type} [∀ k, Fintype (I k)] {F : Type} [Field F]
      (w : (Σ k, I k) → F) (_ : (mCoordIdeal w).IsPrime ∧ IsRelevant (mCoordIdeal w)),
      ∀ k, ∃ a, w ⟨k, a⟩ ≠ 0 := by
    intro L I _ F _ w h k
    obtain ⟨a, ha⟩ := h.2 k
    refine ⟨a, fun h0 => ha ?_⟩
    show mConeMap w (X ⟨k, a⟩) = 0
    simp [mConeMap, h0]
  choose c₀ hc₀ using hrel y₀ ⟨hA₀.2.1.1, hA₀.2.1.2.2⟩
  choose c hc using hrel y ⟨hA.2.1.1, hA.2.1.2.2⟩
  have hv := GlobalTheory.CompanionTheory.Ar.Chg.isBlockMap_blkV bx hbk
  let v := GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx
  have hyv : ∀ p, y (v p) = i (y₀ p) := fun p => hy p.1 p.2
  let G := genFib y v
  haveI : CharZero G.Φ' := inferInstanceAs (CharZero (Fn K Ω))
  let ch : ∀ k : FibreBlock bk, J k.1 := fun k => c k.1
  have hch : ∀ k : FibreBlock bk, G.x' ⟨k.1, ch k⟩ ≠ 0 := fun k => xPt_ne_zero (hc k.1)
  have hx : ∀ k, G.x ⟨k, c₀ k⟩ ≠ 0 := by
    intro k h0
    have h1 : xPt y (v ⟨k, c₀ k⟩) = 0 := congrArg Subtype.val h0
    refine xPt_ne_zero ?_ h1
    rw [hyv]
    exact (map_ne_zero i).2 (hc₀ k)
  refine ⟨G, ch, hch, ?_⟩
  have main := GroundTheory.Heights₂.Heights.Targets.GenFibreChartDeg.proof
    GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.proof
    GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.proof
    K₀ J₀ K J bk v (mCoordIdeal y) G c₀ ch hv hA.2.1.2.1 hx hch
  refine main.trans ?_
  rw [← hd]
  exact relfinrank_block y₀ y bk v (fun _ => rfl) i hyv
    (blockFnField_eq_top y₀ c₀ hc₀ hb₀) (blockFnField_eq_top y c hc hb)

end GlobalTheory.CompanionTheory.Ar.Chg.GenFib
