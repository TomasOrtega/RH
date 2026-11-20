import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.DivisorFrames.RegularAtPointExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

namespace UpperTheory.UnitAtPowers

/- English proof (translation)
Take `⟨U, hx, s, rfl⟩` from `h.regAt.exists_fnOf`. Establish `hy : z ∈ g ⁻¹ᵁ U` using `hx`. Rewrite using `[SmallSec.fnMap_fnOf g hη _ (gen_mem hy), unitAt_fnOf_iff hy, ← Scheme.preimage_basicOpen]`. Conclude with `(unitAt_fnOf_iff hx _ s).1 h`.
-/
private theorem unitAt_fnMap {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (g : Z ⟶ X)
    (hη : g (genericPoint Z) ⤳ genericPoint X) {z : Z} {t : X.functionField} (h : UnitAt (g z) t) :
    UnitAt z (SmallSec.fnMap g hη t) := by
  obtain ⟨U, hx, s, rfl⟩ := h.regAt.exists_fnOf
  have hy : z ∈ g ⁻¹ᵁ U := hx
  rw [SmallSec.fnMap_fnOf g hη _ (gen_mem hy), unitAt_fnOf_iff hy, ← Scheme.preimage_basicOpen]
  exact (unitAt_fnOf_iff hx _ s).1 h

/- English proof (translation)
The claim follows from `have ⟨a, ha, e⟩ := h; ⟨a ^ m, ha.pow m, by rw [map_pow, e]⟩`.
-/
private theorem unitAt_pow {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : UnitAt x f) (m : ℕ) :
    UnitAt x (f ^ m) :=
  have ⟨a, ha, e⟩ := h; ⟨a ^ m, ha.pow m, by rw [map_pow, e]⟩

/- English proof (translation)
Establish `hx : x ∈ L.U i ⊓ L.U j` using `⟨hi, hj⟩`. Rewrite using `[hs i j (gen_mem hx), mul_div_cancel_right₀ _ (s j).ne_zero]`. Conclude with `unitAt_fnOf hx _ _`.
-/
private theorem unitAt_div {X : Scheme.{0}} [IsIntegral X] {L : LB X} {s : L.ι → X.functionFieldˣ} (hs : IsRatSec L s)
    {x : X} {i j : L.ι} (hi : x ∈ L.U i) (hj : x ∈ L.U j) : UnitAt x ((s i : X.functionField) / s j) := by
  have hx : x ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  rw [hs i j (gen_mem hx), mul_div_cancel_right₀ _ (s j).ne_zero]
  exact unitAt_fnOf hx _ _

/- English proof (translation)
Establish `hc : IsClosed (T.str '' closure {x})` using `T.str.isClosedMap _ isClosed_closure`. Establish `h₁ : T.str x ∈ T.str '' closure {x}` using `⟨x, subset_closure rfl, rfl⟩`. Take `⟨x₀, h, e⟩` from `(IsLocalRing.specializes_closedPoint (T.str x)).mem_closed hc h₁`. Conclude with `⟨x₀, specializes_iff_mem_closure.2 h, e⟩`.
-/
private theorem exists_special {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (T : Vert.Model O)
    (x : T.X) : ∃ x₀ : T.X, x ⤳ x₀ ∧ T.str x₀ = closedPoint O := by
  have hc : IsClosed (T.str '' closure {x}) := T.str.isClosedMap _ isClosed_closure
  have h₁ : T.str x ∈ T.str '' closure {x} := ⟨x, subset_closure rfl, rfl⟩
  obtain ⟨x₀, h, e⟩ := (IsLocalRing.specializes_closedPoint (T.str x)).mem_closed hc h₁
  exact ⟨x₀, specializes_iff_mem_closure.2 h, e⟩

/- English proof (translation)
Simplify using `using (Base.valAt_zpow y h).2 (-1)`.
-/
private theorem valAt_inv {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z} {f : Z.functionField}
    (h : UnitAt (below y) f) : valAt y f⁻¹ = (valAt y f)⁻¹ := by
  simpa using (Base.valAt_zpow y h).2 (-1)

/- English proof (translation)
Establish `e` using `congrArg (fun k => k (closedPoint (T.X.presheaf.stalk (genericPoint T.X)))) μ.φ_spec`. Establish `e₁ : μ.U.fromSpecStalkOfMem _ μ.mem (closedPoint (T.X.presheaf.stalk (genericPoint T.X))) = (⟨genericPoint T.X, μ.mem⟩ : μ.U)`. Apply `μ.U.ι.isOpenEmbedding.injective` to reduce the goal to its premises. Conclude with `(congrArg (fun k => k (closedPoint (T.X.presheaf.stalk (genericPoint T.X)))) (Scheme.Opens.fromSpecStalkOfMem_ι μ.U _ μ.mem)).trans Scheme.fromSpecStalk_closedPoint`. Rewrite using `[← e₁]`.

Use `Eq.trans e ?_` and prove the remaining obligations. Use `Eq.trans (congrArg (Y.X.fromSpecStalk (genericPoint Y.X)) (Subsingleton.elim (α := PrimeSpectrum Y.Fn) _ (closedPoint _))) ?_` and prove the remaining obligations. Conclude with `Scheme.fromSpecStalk_closedPoint`.
-/
private theorem h_gen {F : Type} [Field F] [NumberField F] {Y : Var F} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {b : 𝓞 F →+* O} {T : Vert.Model O} (μ : Match Y b T) :
    μ.h (⟨genericPoint T.X, μ.mem⟩ : μ.U) = genericPoint Y.X := by
  have e := congrArg (fun k => k (closedPoint (T.X.presheaf.stalk (genericPoint T.X)))) μ.φ_spec
  have e₁ : μ.U.fromSpecStalkOfMem _ μ.mem (closedPoint (T.X.presheaf.stalk (genericPoint T.X))) =
      (⟨genericPoint T.X, μ.mem⟩ : μ.U) := by
    apply μ.U.ι.isOpenEmbedding.injective
    exact (congrArg (fun k => k (closedPoint (T.X.presheaf.stalk (genericPoint T.X))))
      (Scheme.Opens.fromSpecStalkOfMem_ι μ.U _ μ.mem)).trans Scheme.fromSpecStalk_closedPoint
  rw [← e₁]
  refine Eq.trans e ?_
  refine Eq.trans (congrArg (Y.X.fromSpecStalk (genericPoint Y.X))
    (Subsingleton.elim (α := PrimeSpectrum Y.Fn) _ (closedPoint _))) ?_
  exact Scheme.fromSpecStalk_closedPoint

end UpperTheory.UnitAtPowers

open UpperTheory.UnitAtPowers in
/- English proof (translation)
Introduce `F _ _ Y v p _ _ F' _ _ ε O _ _ b hup T hT μ Q _ g hg hext L hL s N hN s' l m ⟨hs, W, hW, hR⟩ ⟨hs', W', hW', hG⟩`. Establish `key : ∀ (x : T.X) (i : L.ι) (i' : N.ι), T.str x = closedPoint O → x ∈ L.U i → g x ∈ N.U i' → UnitAt x ((s i : T.X.functionField) ^ m / SmallSec.fnMap g hg (s' i' : Q.X.functionField))`. Introduce `x i i' hx hi hi'`. Use `set u := (s i : T.X.functionField) ^ m / SmallSec.fnMap g hg (s' i' : Q.X.functionField) with hu`. Establish `hu0 : u ≠ 0` using `div_ne_zero (pow_ne_zero _ (s i).ne_zero) ((map_ne_zero _).2 (s' i').ne_zero)`.

Establish `hD : genericPoint T.X ∈ μ.U.ι ''ᵁ (μ.h ⁻¹ᵁ (W ⊓ W'))`. Use `⟨⟨genericPoint T.X, μ.mem⟩, ?_, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `μ.h (⟨genericPoint T.X, μ.mem⟩ : μ.U) ∈ W ⊓ W'`. Rewrite using `[h_gen μ]`. Conclude with `⟨hW, hW'⟩`.

Establish `main : ∀ (e : TrueGeo.Ext v) (zt : Sp e.O ⟶ T.X), ⊤ ≤ zt ⁻¹ᵁ (L.U i ⊓ g ⁻¹ᵁ N.U i') → (spMap e.O.subtype ≫ zt) ≫ T.str ≫ spMap b = spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) → below (spMap e.O.subtype ≫ zt) ∈ μ.U.ι ''ᵁ (μ.h ⁻¹ᵁ (W ⊓ W')) → UnitAt (belo …`. Introduce `e zt hV hstr hb`. Take `⟨q, hq, hqe⟩` from `hb`. Establish `hr : Set.range (spMap e.O.subtype ≫ zt) ⊆ Set.range μ.U.ι`. Introduce and unpack `_ ⟨t, rfl⟩`.

Take `rfl : t = closedPoint (AlgebraicClosure F)` from `Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure F)) _ _`. Conclude with `⟨q, hqe⟩`. Take `⟨z, hz⟩ : ∃ z : Sp (AlgebraicClosure F) ⟶ μ.U.toScheme, z ≫ μ.U.ι = spMap e.O.subtype ≫ zt` from `⟨_, IsOpenImmersion.lift_fac μ.U.ι _ hr⟩`. Establish `hzq : below z = q`. Apply `μ.U.ι.isOpenEmbedding.injective` to reduce the goal to its premises.

Use `Eq.trans ?_ hqe.symm` and prove the remaining obligations. Rewrite using `[← hz]`. Both sides reduce to the same expression. Establish `hmono : Mono (spMap (algebraMap (𝓞 F) F))`. Establish `: Epi (CommRingCat.ofHom (algebraMap (𝓞 F) F))` using `IsLocalization.epi (nonZeroDivisors (𝓞 F)) F`.

Conclude with `inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (𝓞 F) F)).op))`. Establish `hy : (z ≫ μ.h) ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F))`. Rewrite using `[← cancel_mono (spMap (algebraMap (𝓞 F) F)), ← hstr, ← hz, Category.assoc, Category.assoc, μ.h_str, Category.assoc]`. Set `y : AlgPt Y` to `⟨z ≫ μ.h, hy⟩`. Establish `hyW : below y.1 ∈ W ⊓ W'`.

Express the relevant statement in the definitionally equal form `μ.h (below z) ∈ W ⊓ W'`. Rewrite using `[hzq]`. Conclude with `hq`. Establish `hj : (z ≫ μ.U.ι) ≫ g = y.1 ≫ Q.j`. Rewrite using `[Category.assoc, hext.1, ← Category.assoc]`.

Take `⟨a₁, a₂⟩` from `hR e y z zt i hyW.1 rfl hz.symm (fun t ht => (hV ht).1)`. Take `⟨b₁, b₂⟩` from `hG e y (zt ≫ g) i' hyW.2 (by rw [← Category.assoc, ← hz, hj]) (fun t ht => (hV ht).2)`. Rewrite `b₁`, `b₂` using `[← hj]`. Rewrite using `[← hz]`. Establish `b₃` using `unitAt_fnMap g hg (z := below (z ≫ μ.U.ι)) b₁`.

Establish `c₁` using `unitAt_pow a₁ m`. Use `⟨by rw [hu, div_eq_mul_inv]; exact c₁.mul b₃.inv, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, div_eq_mul_inv, SmallSec.valAt_mul c₁.regAt b₃.inv.regAt, valAt_inv b₃, SmallSec.valAt_pow a₁.regAt, SmallSec.valAt_fnMap g hg _ b₁.regAt, map_mul, map_pow, map_inv₀]`. Establish `p₁` using `e.w.pos (SmallSec.valAt_ne_zero a₁)`. Establish `p₂` using `e.w.pos (SmallSec.valAt_ne_zero b₁)`.

Rewrite using `[mul_inv_eq_one₀ p₂.ne']`. Use `Real.log_injOn_pos (pow_pos p₁ m) p₂ ?_` and prove the remaining obligations. Rewrite using `[Real.log_pow, a₂, b₂]`. Use `(GlobalTheory.Cartier.unitAt_iff hu0).2 ⟨by_contra fun h => ?_, by_contra fun h => ?_⟩` and prove the remaining obligations. Take `⟨e, zt, h₁, h₂, h₃, h₄⟩` from `UpperTheory.regular_at_point_extension F v F' ε O b hup T hT x hx _ _ (show x ∈ L.U i ⊓ g ⁻¹ᵁ N.U i' from ⟨hi, hi'⟩) hD u h`.

Take `⟨k₁, k₂⟩` from `main e zt h₁ h₂ h₃`. Use `h₄ k₁.inv.regAt` as an intermediate fact. Rewrite `this` using `[valAt_inv k₁, map_inv₀, k₂, inv_one]`. Conclude with `lt_irrefl _ this`. Take `⟨e, zt, h₁, h₂, h₃, h₄⟩` from `UpperTheory.regular_at_point_extension F v F' ε O b hup T hT x hx _ _ (show x ∈ L.U i ⊓ g ⁻¹ᵁ N.U i' from ⟨hi, hi'⟩) hD u⁻¹ h`.

Take `⟨k₁, k₂⟩` from `main e zt h₁ h₂ h₃`. Rewrite `h₄` using `[inv_inv]`. Conclude with `(h₄ k₁.regAt).ne k₂`. Introduce `x i i' hi hi'`. Take `⟨x₀, hx, hx₀⟩` from `exists_special T x`.

Take `⟨j, hj⟩` from `exists_chart hL x₀`. Take `⟨j', hj'⟩` from `exists_chart hN (g x₀)`. Take `⟨U, hU, hUu⟩` from `(key x₀ j j' hx₀ hj hj').exists_nhds`. Establish `h₁` using `hUu x (hx.mem_open U.isOpen hU)`. Establish `h₂` using `unitAt_pow (unitAt_div hs hi (hx.mem_open (L.U j).isOpen hj)) m`.

Establish `h₃` using `unitAt_fnMap g hg (unitAt_div hs' ((hx.map g.continuous).mem_open (N.U j').isOpen hj') hi')`. Establish `h₄` using `(h₁.mul h₂).mul h₃`. Establish `n₁` using `(s j).ne_zero`. Establish `n₂ : SmallSec.fnMap g hg (s' j' : Q.X.functionField) ≠ 0` using `(map_ne_zero _).2 (s' j').ne_zero`. Use `h₄ using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_div₀, div_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.unitAt_pow_div_fnMap_of_reads_of_gReads :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime], (p : 𝓞 F) ∈ v.asIdeal → ∀ (F' : Type) [Field F'] [NumberField F'] (ε : F →+* F') (O : ValuationSubring F') [IsDiscreteValuationRing O] [CharP (ResidueField O) p] (b : 𝓞 F →+* O), IsUp v ε O b → ∀ (T : Vert.Model O), GlobalTheory.IsNormalScheme T.X → ∀ (μ : Match Y b T) (Q : TrueGeo.Model Y) [IsIntegral Q.X] (g : T.X ⟶ Q.X) (hg : g (genericPoint T.X) ⤳ genericPoint Q.X), Extends μ Q g → ∀ (L : LB T.X), L.IsLB → ∀ (s : L.ι → T.X.functionFieldˣ) (N : LB Q.X), N.IsLB → ∀ (s' : N.ι → Q.X.functionFieldˣ) (l : Ext v → AlgPt Y → ℝ) (m : ℕ), Reads μ v L s l → GReads Q v N s' (fun e y => (m : ℝ) * l e y) → ∀ (x : T.X) (i : L.ι) (i' : N.ι), x ∈ L.U i → g x ∈ N.U i' → UnitAt x ((s i : T.X.functionField) ^ m / SmallSec.fnMap g hg (s' i' : Q.X.functionField)) := by
  intro F _ _ Y v p _ _ F' _ _ ε O _ _ b hup T hT μ Q _ g hg hext L hL s N hN s' l m ⟨hs, W, hW, hR⟩ ⟨hs', W', hW', hG⟩
  have key : ∀ (x : T.X) (i : L.ι) (i' : N.ι), T.str x = closedPoint O → x ∈ L.U i → g x ∈ N.U i' →
      UnitAt x ((s i : T.X.functionField) ^ m / SmallSec.fnMap g hg (s' i' : Q.X.functionField)) := by
    intro x i i' hx hi hi'
    set u := (s i : T.X.functionField) ^ m / SmallSec.fnMap g hg (s' i' : Q.X.functionField) with hu
    have hu0 : u ≠ 0 := div_ne_zero (pow_ne_zero _ (s i).ne_zero) ((map_ne_zero _).2 (s' i').ne_zero)
    have hD : genericPoint T.X ∈ μ.U.ι ''ᵁ (μ.h ⁻¹ᵁ (W ⊓ W')) := by
      refine ⟨⟨genericPoint T.X, μ.mem⟩, ?_, rfl⟩
      change μ.h (⟨genericPoint T.X, μ.mem⟩ : μ.U) ∈ W ⊓ W'
      rw [h_gen μ]
      exact ⟨hW, hW'⟩
    have main : ∀ (e : TrueGeo.Ext v) (zt : Sp e.O ⟶ T.X), ⊤ ≤ zt ⁻¹ᵁ (L.U i ⊓ g ⁻¹ᵁ N.U i') →
        (spMap e.O.subtype ≫ zt) ≫ T.str ≫ spMap b =
          spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) →
        below (spMap e.O.subtype ≫ zt) ∈ μ.U.ι ''ᵁ (μ.h ⁻¹ᵁ (W ⊓ W')) →
        UnitAt (below (spMap e.O.subtype ≫ zt)) u ∧ e.w (valAt (spMap e.O.subtype ≫ zt) u) = 1 := by
      intro e zt hV hstr hb
      obtain ⟨q, hq, hqe⟩ := hb
      have hr : Set.range (spMap e.O.subtype ≫ zt) ⊆ Set.range μ.U.ι := by
        rintro _ ⟨t, rfl⟩
        obtain rfl : t = closedPoint (AlgebraicClosure F) :=
          Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure F)) _ _
        exact ⟨q, hqe⟩
      obtain ⟨z, hz⟩ : ∃ z : Sp (AlgebraicClosure F) ⟶ μ.U.toScheme, z ≫ μ.U.ι = spMap e.O.subtype ≫ zt :=
        ⟨_, IsOpenImmersion.lift_fac μ.U.ι _ hr⟩
      have hzq : below z = q := by
        apply μ.U.ι.isOpenEmbedding.injective
        refine Eq.trans ?_ hqe.symm
        rw [← hz]
        rfl
      have hmono : Mono (spMap (algebraMap (𝓞 F) F)) := by
        have : Epi (CommRingCat.ofHom (algebraMap (𝓞 F) F)) := IsLocalization.epi (nonZeroDivisors (𝓞 F)) F
        exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (𝓞 F) F)).op))
      have hy : (z ≫ μ.h) ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) := by
        rw [← cancel_mono (spMap (algebraMap (𝓞 F) F)), ← hstr, ← hz, Category.assoc, Category.assoc, μ.h_str,
          Category.assoc]
      let y : AlgPt Y := ⟨z ≫ μ.h, hy⟩
      have hyW : below y.1 ∈ W ⊓ W' := by
        change μ.h (below z) ∈ W ⊓ W'
        rw [hzq]
        exact hq
      have hj : (z ≫ μ.U.ι) ≫ g = y.1 ≫ Q.j := by
        rw [Category.assoc, hext.1, ← Category.assoc]
      obtain ⟨a₁, a₂⟩ := hR e y z zt i hyW.1 rfl hz.symm (fun t ht => (hV ht).1)
      obtain ⟨b₁, b₂⟩ := hG e y (zt ≫ g) i' hyW.2 (by rw [← Category.assoc, ← hz, hj]) (fun t ht => (hV ht).2)
      rw [← hj] at b₁ b₂
      rw [← hz]
      have b₃ := unitAt_fnMap g hg (z := below (z ≫ μ.U.ι)) b₁
      have c₁ := unitAt_pow a₁ m
      refine ⟨by rw [hu, div_eq_mul_inv]; exact c₁.mul b₃.inv, ?_⟩
      rw [hu, div_eq_mul_inv, SmallSec.valAt_mul c₁.regAt b₃.inv.regAt, valAt_inv b₃, SmallSec.valAt_pow a₁.regAt,
        SmallSec.valAt_fnMap g hg _ b₁.regAt, map_mul, map_pow, map_inv₀]
      have p₁ := e.w.pos (SmallSec.valAt_ne_zero a₁)
      have p₂ := e.w.pos (SmallSec.valAt_ne_zero b₁)
      rw [mul_inv_eq_one₀ p₂.ne']
      refine Real.log_injOn_pos (pow_pos p₁ m) p₂ ?_
      rw [Real.log_pow, a₂, b₂]
    refine (GlobalTheory.Cartier.unitAt_iff hu0).2 ⟨by_contra fun h => ?_, by_contra fun h => ?_⟩
    · obtain ⟨e, zt, h₁, h₂, h₃, h₄⟩ := UpperTheory.regular_at_point_extension F v F' ε O b hup T hT x hx _ _
        (show x ∈ L.U i ⊓ g ⁻¹ᵁ N.U i' from ⟨hi, hi'⟩) hD u h
      obtain ⟨k₁, k₂⟩ := main e zt h₁ h₂ h₃
      have := h₄ k₁.inv.regAt
      rw [valAt_inv k₁, map_inv₀, k₂, inv_one] at this
      exact lt_irrefl _ this
    · obtain ⟨e, zt, h₁, h₂, h₃, h₄⟩ := UpperTheory.regular_at_point_extension F v F' ε O b hup T hT x hx _ _
        (show x ∈ L.U i ⊓ g ⁻¹ᵁ N.U i' from ⟨hi, hi'⟩) hD u⁻¹ h
      obtain ⟨k₁, k₂⟩ := main e zt h₁ h₂ h₃
      rw [inv_inv] at h₄
      exact (h₄ k₁.regAt).ne k₂
  intro x i i' hi hi'
  obtain ⟨x₀, hx, hx₀⟩ := exists_special T x
  obtain ⟨j, hj⟩ := exists_chart hL x₀
  obtain ⟨j', hj'⟩ := exists_chart hN (g x₀)
  obtain ⟨U, hU, hUu⟩ := (key x₀ j j' hx₀ hj hj').exists_nhds
  have h₁ := hUu x (hx.mem_open U.isOpen hU)
  have h₂ := unitAt_pow (unitAt_div hs hi (hx.mem_open (L.U j).isOpen hj)) m
  have h₃ := unitAt_fnMap g hg (unitAt_div hs' ((hx.map g.continuous).mem_open (N.U j').isOpen hj') hi')
  have h₄ := (h₁.mul h₂).mul h₃
  have n₁ := (s j).ne_zero
  have n₂ : SmallSec.fnMap g hg (s' j' : Q.X.functionField) ≠ 0 := (map_ne_zero _).2 (s' j').ne_zero
  convert h₄ using 1
  rw [map_div₀, div_pow]
  field_simp
