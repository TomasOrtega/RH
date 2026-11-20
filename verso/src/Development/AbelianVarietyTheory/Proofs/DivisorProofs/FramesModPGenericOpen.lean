import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowOfFramesTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicPointSpecializingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEquationsHeightSum
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameGlue.ModPTest

/- English proof (translation)
Take `⟨a, rfl⟩` from `hf`. Take `⟨b, rfl⟩` from `hg`. Rewrite using `[← map_sub, SmallSec.valAt_algebraMap, SmallSec.valAt_algebraMap, SmallSec.valAt_algebraMap, map_sub]`.
-/
theorem valAt_sub {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z} {f g : Z.functionField}
    (hf : RegAt (below y) f) (hg : RegAt (below y) g) : valAt y (f - g) = valAt y f - valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_sub, SmallSec.valAt_algebraMap, SmallSec.valAt_algebraMap, SmallSec.valAt_algebraMap, map_sub]

/- English proof (translation)
Establish `h1 : valAt y (1 : Z.functionField) = 1`. Use `SmallSec.valAt_algebraMap (y := y) 1` as an intermediate fact. Rewrite `this` using `[map_one, map_one]`. Then use the resulting hypothesis. Establish `h2` using `SmallSec.valAt_mul hg.regAt hg.inv.regAt`. Rewrite `h2` using `[mul_inv_cancel₀ hg.ne_zero, h1]`.

Rewrite using `[div_eq_mul_inv, SmallSec.valAt_mul hf hg.inv.regAt, div_eq_mul_inv, eq_inv_of_mul_eq_one_right h2.symm]`.
-/
theorem valAt_div {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z} {f g : Z.functionField}
    (hf : RegAt (below y) f) (hg : UnitAt (below y) g) : valAt y (f / g) = valAt y f / valAt y g := by
  have h1 : valAt y (1 : Z.functionField) = 1 := by
    have := SmallSec.valAt_algebraMap (y := y) 1
    rwa [map_one, map_one] at this
  have h2 := SmallSec.valAt_mul hg.regAt hg.inv.regAt
  rw [mul_inv_cancel₀ hg.ne_zero, h1] at h2
  rw [div_eq_mul_inv, SmallSec.valAt_mul hf hg.inv.regAt, div_eq_mul_inv, eq_inv_of_mul_eq_one_right h2.symm]

/- English proof (translation)
The claim follows from `have ⟨a, ha⟩ := hf; have ⟨b, hb⟩ := hg; ⟨a - b, by rw [map_sub, ha, hb]⟩`.
-/
theorem regAt_sub {X : Scheme.{0}} [IsIntegral X] {x : X} {f g : X.functionField} (hf : RegAt x f) (hg : RegAt x g) :
    RegAt x (f - g) :=
  have ⟨a, ha⟩ := hf; have ⟨b, hb⟩ := hg; ⟨a - b, by rw [map_sub, ha, hb]⟩

/- English proof (translation)
Use `choose Ps hPs using hP`. Use `choose Qs hQs using hQ`. Set `f` to `algebraMap (X.presheaf.stalk x) X.functionField`. Establish `eP : f.mapMatrix (Matrix.of Ps) = P` using `by ext i k; exact hPs i k`. Establish `eQ : f.mapMatrix (Matrix.of Qs) = Q` using `by ext i k; exact hQs i k`.

Take `⟨u, hu, hu'⟩` from `hd`. Establish `hdet : IsUnit (Matrix.of Ps).det`. Establish `e : f (Matrix.of Ps).det = f u` using `by rw [RingHom.map_det, eP, ← hu']`. Rewrite using `[IsFractionRing.injective (X.presheaf.stalk x) X.functionField e]`. Conclude with `hu`.

Establish `einv : P⁻¹ = f.mapMatrix (Matrix.of Ps)⁻¹`. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Rewrite using `[← eP, ← map_mul, Matrix.nonsing_inv_mul _ hdet, map_one]`. Use `⟨((Matrix.of Ps)⁻¹ * Matrix.of Qs) i k, ?_⟩` and prove the remaining obligations. Rewrite using `[einv, ← eQ, ← map_mul]`.

Both sides reduce to the same expression.
-/
theorem regAt_inv_mul {X : Scheme.{0}} [IsIntegral X] {x : X} {N : ℕ} {P Q : Matrix (Fin N) (Fin N) X.functionField}
    (hP : ∀ i k, RegAt x (P i k)) (hd : UnitAt x P.det) (hQ : ∀ i k, RegAt x (Q i k)) (i k : Fin N) :
    RegAt x ((P⁻¹ * Q) i k) := by
  choose Ps hPs using hP
  choose Qs hQs using hQ
  let f := algebraMap (X.presheaf.stalk x) X.functionField
  have eP : f.mapMatrix (Matrix.of Ps) = P := by ext i k; exact hPs i k
  have eQ : f.mapMatrix (Matrix.of Qs) = Q := by ext i k; exact hQs i k
  obtain ⟨u, hu, hu'⟩ := hd
  have hdet : IsUnit (Matrix.of Ps).det := by
    have e : f (Matrix.of Ps).det = f u := by rw [RingHom.map_det, eP, ← hu']
    rw [IsFractionRing.injective (X.presheaf.stalk x) X.functionField e]
    exact hu
  have einv : P⁻¹ = f.mapMatrix (Matrix.of Ps)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← eP, ← map_mul, Matrix.nonsing_inv_mul _ hdet, map_one]
  refine ⟨((Matrix.of Ps)⁻¹ * Matrix.of Qs) i k, ?_⟩
  rw [einv, ← eQ, ← map_mul]
  rfl

end GlobalTheory.FrameGlue.ModPTest

open GlobalTheory.FrameGlue.ModPTest in

/- English proof (translation)
Introduce `F _ _ Y C N A p hp V hη W ι U M c hW H1 H2 H3 H4`. Use `haveI : IsPreimmersion V.j :=`. Establish `h : IsPreimmersion (spMap (algebraMap (𝓞 F) F))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))`. Use the proof step `MorphismProperty.of_isPullback (P := @IsPreimmersion) V.pb.flip h`. Use `choose c₀ hc₀ using fun a i => SmallSec.fnMap_surjective V.j hη (c a i : V.G.functionField)`.

Establish `hne : ∀ a i, c₀ a i ≠ 0` using `fun a i h => (c a i).ne_zero (by rw [← hc₀, h, map_zero])`. Set `c' : ι → Fin N → V.X.functionFieldˣ` to `fun a i => Units.mk0 (c₀ a i) (hne a i)`. Establish `hc' : ∀ a i, SmallSec.fnMap V.j hη (c' a i : V.X.functionField) = c a i` using `hc₀`. Use `⟨c', hc', H1, H2, ?_⟩` and prove the remaining obligations. Establish `hmap : ∀ a b i, SmallSec.fnMap V.j hη ((c' a i / c' b i : V.X.functionFieldˣ) : V.X.functionField) = ((c a i / c b i : V.G.functionFieldˣ) : V.G.functionField)`.

Introduce `a b i`. Rewrite using `[Units.val_div_eq_div_val, map_div₀, hc', hc', Units.val_div_eq_div_val]`. Establish `hratio : ∀ a b i (g : V.G.functionField), g * (c b i : V.G.functionField) ≠ 0 → ((c a i / c b i : V.G.functionFieldˣ) : V.G.functionField) = g * (c a i : V.G.functionField) / (g * (c b i : V.G.functionField))`. Introduce `a b i g hg`. Establish `hg0 : g ≠ 0` using `left_ne_zero_of_mul hg`.

Rewrite using `[Units.val_div_eq_div_val, mul_div_mul_left _ _ hg0]`. Establish `hgen : ∀ a b i (z : V.G), V.j z ∈ U a → V.j z ∈ U b → UnitAt z ((c a i / c b i : V.G.functionFieldˣ) : V.G.functionField)`. Introduce `a b i z ha hb`. Establish `h1` using `H3 a i z ha`. Establish `h2` using `H3 b i z hb`.

Rewrite using `[hratio a b i _ h2.ne_zero, div_eq_mul_inv]`. Conclude with `h1.mul h2.inv`. Establish `hbelow : ∀ {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), spMap e.O.subtype ≫ yt = z ≫ V.j → ∀ {U' : V.X.Opens}, ⊤ ≤ yt ⁻¹ᵁ U' → V.j (below z) ∈ U'`. Introduce `v e z yt h U' hU`. Express the relevant statement in the definitionally equal form `(z ≫ V.j) _ ∈ U'`.

Rewrite using `[← h]`. Conclude with `hU (x := spMap e.O.subtype _) trivial`. Establish `hreg : ∀ a b i, ∀ x ∈ U a ⊓ U b, ¬ IsUnit (p : V.X.presheaf.stalk x) → RegAt x ((c' a i / c' b i : V.X.functionFieldˣ) : V.X.functionField)`. Introduce `a b i`. Use `GlobalTheory.T.good_reduction_extends_regular F Y V p hp W hW (U a ⊓ U b) _ (fun z hz => ?_) (fun v hv e y hy z yt hzy hyt hU => ?_)` and prove the remaining obligations.

Rewrite using `[← SmallSec.regAt_fnMap_iff V.j hη, hmap]`. Conclude with `(hgen a b i z hz.1 hz.2).regAt`. Establish `hUa : ⊤ ≤ yt ⁻¹ᵁ U a` using `fun q hq => (hU hq).1`. Establish `hUb : ⊤ ≤ yt ⁻¹ᵁ U b` using `fun q hq => (hU hq).2`. Establish `hza` using `hbelow e z yt hyt hUa`.

Establish `hzb` using `hbelow e z yt hyt hUb`. Establish `hπ : V.π (below z) = below y.1` using `by rw [← hzy]; rfl`. Establish `ua` using `H3 a i (below z) hza`. Establish `ub` using `H3 b i (below z) hzb`. Rewrite `ua`, `ub` using `[hπ]`.

Establish `la` using `(H4 v hv e y hy z yt hzy hyt a hUa).1 i`. Establish `lb` using `(H4 v hv e y hy z yt hzy hyt b hUb).1 i`. Establish `hwa` using `e.w.pos (SmallSec.valAt_ne_zero ua)`. Establish `hwb` using `e.w.pos (SmallSec.valAt_ne_zero ub)`. Establish `heq` using `Real.log_injOn_pos (Set.mem_Ioi.2 hwa) (Set.mem_Ioi.2 hwb) (la.symm.trans lb)`.

Establish `hu` using `hgen a b i (below z) hza hzb`. Establish `hu' : RegAt (V.j (below z)) ((c' a i / c' b i : V.X.functionFieldˣ) : V.X.functionField)`. Rewrite using `[← SmallSec.regAt_fnMap_iff V.j hη, hmap]`. Conclude with `hu.regAt`. Rewrite using `[← SmallSec.valAt_fnMap V.j hη z hu', hmap, hratio a b i _ ub.ne_zero, valAt_div ua.regAt ub, map_div₀, heq, div_self hwb.ne']`.

Establish `hunit : ∀ a b i, ∀ x ∈ U a, x ∈ U b → ¬ IsUnit (p : V.X.presheaf.stalk x) → UnitAt x ((c' a i / c' b i : V.X.functionFieldˣ) : V.X.functionField)`. Introduce `a b i x ha hb hx`. Use `(unitAt_iff (Units.ne_zero _)).2 ⟨hreg a b i x ⟨ha, hb⟩ hx, ?_⟩` and prove the remaining obligations. Use `hreg b a i x ⟨hb, ha⟩ hx` as an intermediate fact. Rewrite using `[← Units.val_inv_eq_inv_val, inv_div]` and apply the resulting hypothesis.

Establish `hnot : ∀ a b, ∀ x ∈ U a, x ∈ U b → ¬ IsUnit (p : V.X.presheaf.stalk x) → ∀ t : V.X.functionField, (∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : TrueGeo.Ext v) (y : AlgPt Y), below y.1 ∈ W → ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e …`. Introduce `a b x ha hb hx t hlt ht`. Take `⟨U', hxU', hU'⟩` from `ht.exists_nhds`. Take `⟨v, e, y, z, yt, hv, hy, hzy, hyt, hU, -⟩` from `GlobalTheory.T.exists_algebraic_point_specializing F Y V p hp W hW (U a ⊓ U b ⊓ U') x ⟨⟨ha, hb⟩, hxU'⟩ hx`. Establish `h1 : e.w (valAt (z ≫ V.j) t) = 1` using `FinSum.w_valAt e (z ≫ V.j) yt hyt (hU' _ (hU (x := IsLocalRing.closedPoint e.O) trivial).2)`.

Establish `hzU' : V.j (below z) ∈ U'` using `hbelow e z yt hyt (fun q hq => (hU hq).2)`. Use `hlt v hv e y hy z yt hzy hyt (fun q hq => (hU hq).1.1) (fun q hq => (hU hq).1.2) (hU' _ hzU').regAt` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `a b x ha hb hx i`. Take `⟨hMa, hda⟩` from `H2 a x ha hx`.

Take `⟨hMb, -⟩` from `H2 b x hb hx`. Establish `hQ` using `regAt_inv_mul hMa hda hMb`. Use `⟨hunit a b i x ha hb hx, fun k hk => ?_, ?_⟩` and prove the remaining obligations. Use `zeroAt_iff.2 ⟨hQ i k, hnot a b x ha hb hx _ fun v hv e y hy z yt hzy hyt hUa hUb _ => ?_⟩` and prove the remaining obligations. Conclude with `((H4 v hv e y hy z yt hzy hyt a hUa).2 b hUb i).1 k hk`.

Use `zeroAt_iff.2 ⟨regAt_sub (hQ i i) (hunit a b i x ha hb hx).regAt, hnot a b x ha hb hx _ fun v hv e y hy z yt hzy hyt hUa hUb ht => ?_⟩` and prove the remaining obligations. Establish `hza` using `hbelow e z yt hyt hUa`. Establish `hzb` using `hbelow e z yt hyt hUb`. Establish `hu' : RegAt (V.j (below z)) ((c' a i / c' b i : V.X.functionFieldˣ) : V.X.functionField)`. Rewrite using `[← SmallSec.regAt_fnMap_iff V.j hη, hmap]`.

Conclude with `(hgen a b i (below z) hza hzb).regAt`. Establish `hQ' : RegAt (V.j (below z)) (((M a)⁻¹ * M b) i i)`. Use `ht.add hu'` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Rewrite using `[valAt_sub (y := z ≫ V.j) hQ' hu', ← SmallSec.valAt_fnMap V.j hη z hu', hmap]`.

Conclude with `((H4 v hv e y hy z yt hzy hyt a hUa).2 b hUb i).2`.
-/
theorem GlobalTheory.FrameGlue.exists_modPFrames_of_bounds :
  ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (N : ℕ) (A : Fin N → Adl C Y) (p : ℕ), p.Prime →
  ∀ (V : Cover Y) (hη : V.j (genericPoint V.G) ⤳ genericPoint V.X) (W : Y.X.Opens) (ι : Type) (U : ι → V.X.Opens)
    (M : ι → Matrix (Fin N) (Fin N) V.X.functionField) (c : ι → Fin N → V.G.functionFieldˣ), genericPoint Y.X ∈ W →
    (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) →
    (∀ a, ∀ x ∈ U a, ¬ IsUnit (p : V.X.presheaf.stalk x) → (∀ i k, RegAt x (M a i k)) ∧ UnitAt x (M a).det) →
    (∀ a i (z : V.G), V.j z ∈ U a → UnitAt z (V.φ (genAt (A i).D (V.π z)) * c a i)) →
    (∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
        (∀ i, (A i).lg v e y =
          Real.log (e.w (valAt z (V.φ (genAt (A i).D (below y.1)) * (c a i : V.G.functionField))))) ∧
        ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ i, (∀ k, k < i → e.w (valAt (z ≫ V.j) (((M a)⁻¹ * M b) i k)) < 1) ∧
          e.w (valAt (z ≫ V.j) (((M a)⁻¹ * M b) i i) - valAt z ((c a i / c b i : V.G.functionFieldˣ) : V.G.functionField)) < 1) →
    ∃ c' : ι → Fin N → V.X.functionFieldˣ, (∀ a i, GlobalTheory.TrueGeo.SmallSec.fnMap V.j hη (c' a i) = c a i) ∧ GlobalTheory.FrameGlue.ModPFrames p U M c' := by
  intro F _ _ Y C N A p hp V hη W ι U M c hW H1 H2 H3 H4
  haveI : IsPreimmersion V.j :=
    have h : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
    MorphismProperty.of_isPullback (P := @IsPreimmersion) V.pb.flip h
  choose c₀ hc₀ using fun a i => SmallSec.fnMap_surjective V.j hη (c a i : V.G.functionField)
  have hne : ∀ a i, c₀ a i ≠ 0 := fun a i h => (c a i).ne_zero (by rw [← hc₀, h, map_zero])
  let c' : ι → Fin N → V.X.functionFieldˣ := fun a i => Units.mk0 (c₀ a i) (hne a i)
  have hc' : ∀ a i, SmallSec.fnMap V.j hη (c' a i : V.X.functionField) = c a i := hc₀
  refine ⟨c', hc', H1, H2, ?_⟩
  have hmap : ∀ a b i, SmallSec.fnMap V.j hη ((c' a i / c' b i : V.X.functionFieldˣ) : V.X.functionField) =
      ((c a i / c b i : V.G.functionFieldˣ) : V.G.functionField) := by
    intro a b i
    rw [Units.val_div_eq_div_val, map_div₀, hc', hc', Units.val_div_eq_div_val]
  have hratio : ∀ a b i (g : V.G.functionField), g * (c b i : V.G.functionField) ≠ 0 →
      ((c a i / c b i : V.G.functionFieldˣ) : V.G.functionField) =
        g * (c a i : V.G.functionField) / (g * (c b i : V.G.functionField)) := by
    intro a b i g hg
    have hg0 : g ≠ 0 := left_ne_zero_of_mul hg
    rw [Units.val_div_eq_div_val, mul_div_mul_left _ _ hg0]
  have hgen : ∀ a b i (z : V.G), V.j z ∈ U a → V.j z ∈ U b →
      UnitAt z ((c a i / c b i : V.G.functionFieldˣ) : V.G.functionField) := by
    intro a b i z ha hb
    have h1 := H3 a i z ha
    have h2 := H3 b i z hb
    rw [hratio a b i _ h2.ne_zero, div_eq_mul_inv]
    exact h1.mul h2.inv
  have hbelow : ∀ {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G)
      (yt : Sp e.O ⟶ V.X), spMap e.O.subtype ≫ yt = z ≫ V.j → ∀ {U' : V.X.Opens}, ⊤ ≤ yt ⁻¹ᵁ U' →
      V.j (below z) ∈ U' := by
    intro v e z yt h U' hU
    change (z ≫ V.j) _ ∈ U'
    rw [← h]
    exact hU (x := spMap e.O.subtype _) trivial
  have hreg : ∀ a b i, ∀ x ∈ U a ⊓ U b, ¬ IsUnit (p : V.X.presheaf.stalk x) →
      RegAt x ((c' a i / c' b i : V.X.functionFieldˣ) : V.X.functionField) := by
    intro a b i
    refine GlobalTheory.T.good_reduction_extends_regular F Y V p hp W hW (U a ⊓ U b) _ (fun z hz => ?_) (fun v hv e y hy z yt hzy hyt hU => ?_)
    · rw [← SmallSec.regAt_fnMap_iff V.j hη, hmap]
      exact (hgen a b i z hz.1 hz.2).regAt
    · have hUa : ⊤ ≤ yt ⁻¹ᵁ U a := fun q hq => (hU hq).1
      have hUb : ⊤ ≤ yt ⁻¹ᵁ U b := fun q hq => (hU hq).2
      have hza := hbelow e z yt hyt hUa
      have hzb := hbelow e z yt hyt hUb
      have hπ : V.π (below z) = below y.1 := by rw [← hzy]; rfl
      have ua := H3 a i (below z) hza
      have ub := H3 b i (below z) hzb
      rw [hπ] at ua ub
      have la := (H4 v hv e y hy z yt hzy hyt a hUa).1 i
      have lb := (H4 v hv e y hy z yt hzy hyt b hUb).1 i
      have hwa := e.w.pos (SmallSec.valAt_ne_zero ua)
      have hwb := e.w.pos (SmallSec.valAt_ne_zero ub)
      have heq := Real.log_injOn_pos (Set.mem_Ioi.2 hwa) (Set.mem_Ioi.2 hwb) (la.symm.trans lb)
      have hu := hgen a b i (below z) hza hzb
      have hu' : RegAt (V.j (below z)) ((c' a i / c' b i : V.X.functionFieldˣ) : V.X.functionField) := by
        rw [← SmallSec.regAt_fnMap_iff V.j hη, hmap]
        exact hu.regAt
      rw [← SmallSec.valAt_fnMap V.j hη z hu', hmap, hratio a b i _ ub.ne_zero, valAt_div ua.regAt ub, map_div₀, heq,
        div_self hwb.ne']
  have hunit : ∀ a b i, ∀ x ∈ U a, x ∈ U b → ¬ IsUnit (p : V.X.presheaf.stalk x) →
      UnitAt x ((c' a i / c' b i : V.X.functionFieldˣ) : V.X.functionField) := by
    intro a b i x ha hb hx
    refine (unitAt_iff (Units.ne_zero _)).2 ⟨hreg a b i x ⟨ha, hb⟩ hx, ?_⟩
    have := hreg b a i x ⟨hb, ha⟩ hx
    rwa [← Units.val_inv_eq_inv_val, inv_div]
  have hnot : ∀ a b, ∀ x ∈ U a, x ∈ U b → ¬ IsUnit (p : V.X.presheaf.stalk x) → ∀ t : V.X.functionField,
      (∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : TrueGeo.Ext v) (y : AlgPt Y), below y.1 ∈ W →
        ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 →
          spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U a → ⊤ ≤ yt ⁻¹ᵁ U b → RegAt (V.j (below z)) t →
            e.w (valAt (z ≫ V.j) t) < 1) → ¬ UnitAt x t := by
    intro a b x ha hb hx t hlt ht
    obtain ⟨U', hxU', hU'⟩ := ht.exists_nhds
    obtain ⟨v, e, y, z, yt, hv, hy, hzy, hyt, hU, -⟩ :=
      GlobalTheory.T.exists_algebraic_point_specializing F Y V p hp W hW (U a ⊓ U b ⊓ U') x ⟨⟨ha, hb⟩, hxU'⟩ hx
    have h1 : e.w (valAt (z ≫ V.j) t) = 1 :=
      FinSum.w_valAt e (z ≫ V.j) yt hyt (hU' _ (hU (x := IsLocalRing.closedPoint e.O) trivial).2)
    have hzU' : V.j (below z) ∈ U' := hbelow e z yt hyt (fun q hq => (hU hq).2)
    have := hlt v hv e y hy z yt hzy hyt (fun q hq => (hU hq).1.1) (fun q hq => (hU hq).1.2) (hU' _ hzU').regAt
    linarith
  intro a b x ha hb hx i
  obtain ⟨hMa, hda⟩ := H2 a x ha hx
  obtain ⟨hMb, -⟩ := H2 b x hb hx
  have hQ := regAt_inv_mul hMa hda hMb
  refine ⟨hunit a b i x ha hb hx, fun k hk => ?_, ?_⟩
  · refine zeroAt_iff.2 ⟨hQ i k, hnot a b x ha hb hx _ fun v hv e y hy z yt hzy hyt hUa hUb _ => ?_⟩
    exact ((H4 v hv e y hy z yt hzy hyt a hUa).2 b hUb i).1 k hk
  · refine zeroAt_iff.2 ⟨regAt_sub (hQ i i) (hunit a b i x ha hb hx).regAt,
      hnot a b x ha hb hx _ fun v hv e y hy z yt hzy hyt hUa hUb ht => ?_⟩
    have hza := hbelow e z yt hyt hUa
    have hzb := hbelow e z yt hyt hUb
    have hu' : RegAt (V.j (below z)) ((c' a i / c' b i : V.X.functionFieldˣ) : V.X.functionField) := by
      rw [← SmallSec.regAt_fnMap_iff V.j hη, hmap]
      exact (hgen a b i (below z) hza hzb).regAt
    have hQ' : RegAt (V.j (below z)) (((M a)⁻¹ * M b) i i) := by
      have := ht.add hu'
      rwa [sub_add_cancel] at this
    rw [valAt_sub (y := z ≫ V.j) hQ' hu', ← SmallSec.valAt_fnMap V.j hη z hu', hmap]
    exact ((H4 v hv e y hy z yt hzy hyt a hUa).2 b hUb i).2
