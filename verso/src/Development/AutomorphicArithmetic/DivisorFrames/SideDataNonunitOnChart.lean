import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AutomorphicArithmetic.DivisorFrames.ColMinorMulTriangular
import Development.AutomorphicArithmetic.DivisorFrames.ExistsRowsAttainingMinorValues
import Development.AutomorphicArithmetic.DivisorFrames.ValuationRegularFunctionAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesModPGenericOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtPointsOverPrimeBound
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

namespace UpperTheory.NonarchimedeanMinorValuations
open GlobalTheory.TrueGeo.SmallSec

section Gen
variable {Z : Scheme.{0}} [IsIntegral Z]

/- English proof (translation)
Unfold `colMinor`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.
-/
private theorem map_colMinor {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n r : ℕ}
    (X : Matrix (Fin n) (Fin r) R) (k : ℕ) (hk : k ≤ r) (σ : Fin k → Fin n) :
    φ (colMinor X k hk σ) = colMinor (X.map φ) k hk σ := by
  unfold colMinor
  rw [RingHom.map_det]
  rfl

/- English proof (translation)
Use `choose A hA using h`. Establish `e : X = (Matrix.of A).map (algebraMap (Z.presheaf.stalk x) Z.functionField)`. Use extensionality with `a b`. Conclude with `(hA a b).symm`. Conclude with `⟨colMinor (Matrix.of A) k hk σ, by rw [map_colMinor, e]⟩`.
-/
private theorem regAt_colMinor {x : Z} {n r : ℕ} {X : Matrix (Fin n) (Fin r) Z.functionField}
    (h : ∀ a b, RegAt x (X a b)) (k : ℕ) (hk : k ≤ r) (σ : Fin k → Fin n) : RegAt x (colMinor X k hk σ) := by
  choose A hA using h
  have e : X = (Matrix.of A).map (algebraMap (Z.presheaf.stalk x) Z.functionField) := by
    ext a b; exact (hA a b).symm
  exact ⟨colMinor (Matrix.of A) k hk σ, by rw [map_colMinor, e]⟩

/- English proof (translation)
Use `choose A hA using h`. Establish `e : X = (Matrix.of A).map (algebraMap (Z.presheaf.stalk (below y)) Z.functionField)`. Use extensionality with `a b`. Conclude with `(hA a b).symm`. Rewrite using `[e, ← map_colMinor, valAt_algebraMap, map_colMinor]`.

Use `congr 1`. Use extensionality with `a b`. Conclude with `(valAt_algebraMap _).symm`.
-/
private theorem valAt_colMinor {K : Type} [Field K] {y : Sp K ⟶ Z} {n r : ℕ}
    {X : Matrix (Fin n) (Fin r) Z.functionField}
    (h : ∀ a b, RegAt (below y) (X a b)) (k : ℕ) (hk : k ≤ r) (σ : Fin k → Fin n) :
    TrueGeo.valAt y (colMinor X k hk σ) = colMinor (X.map (TrueGeo.valAt y)) k hk σ := by
  choose A hA using h
  have e : X = (Matrix.of A).map (algebraMap (Z.presheaf.stalk (below y)) Z.functionField) := by
    ext a b; exact (hA a b).symm
  rw [e, ← map_colMinor, valAt_algebraMap, map_colMinor]
  congr 1
  ext a b
  exact (valAt_algebraMap _).symm

/- English proof (translation)
The claim follows from `have ⟨a, ha, e⟩ := h; ⟨a ^ m, ha.pow m, by rw [map_pow, e]⟩`.
-/
private theorem unitAt_pow {x : Z} {f : Z.functionField} (h : UnitAt x f) (m : ℕ) : UnitAt x (f ^ m) :=
  have ⟨a, ha, e⟩ := h; ⟨a ^ m, ha.pow m, by rw [map_pow, e]⟩

/- English proof (translation)
The claim follows from `Finset.prod_induction _ _ (fun _ _ => UnitAt.mul) (unitAt_one x) fun i _ => h i`.
-/
private theorem unitAt_prod {x : Z} {I : Type} [Fintype I] {q : I → Z.functionField} (h : ∀ i, UnitAt x (q i)) :
    UnitAt x (∏ i, q i) :=
  Finset.prod_induction _ _ (fun _ _ => UnitAt.mul) (unitAt_one x) fun i _ => h i

/- English proof (translation)
Use `choose a ha using h`. Establish `e : q = fun i => algebraMap (Z.presheaf.stalk (below y)) Z.functionField (a i)` using `funext fun i => (ha i).symm`. Substitute `e` using the available equality. Rewrite using `[← map_prod, valAt_algebraMap, map_prod]`. Conclude with `Finset.prod_congr rfl fun i _ => (valAt_algebraMap _).symm`.
-/
private theorem valAt_prod {K : Type} [Field K] {y : Sp K ⟶ Z} {I : Type} [Fintype I] {q : I → Z.functionField}
    (h : ∀ i, RegAt (below y) (q i)) : TrueGeo.valAt y (∏ i, q i) = ∏ i, TrueGeo.valAt y (q i) := by
  choose a ha using h
  have e : q = fun i => algebraMap (Z.presheaf.stalk (below y)) Z.functionField (a i) := funext fun i => (ha i).symm
  subst e
  rw [← map_prod, valAt_algebraMap, map_prod]
  exact Finset.prod_congr rfl fun i _ => (valAt_algebraMap _).symm

/- English proof (translation)
Establish `h1` using `h.mul hq.inv`. Rewrite `h1` using `[mul_inv_cancel_right₀ hq.ne_zero]`. Take `⟨a, rfl⟩` from `hf`. Take `⟨b, hb, e⟩` from `h1`. Rewrite `e` using `[← map_pow]`.

Use `IsFractionRing.injective (Z.presheaf.stalk x) Z.functionField e` as an intermediate fact. Rewrite `hb` using `[this]`. Conclude with `⟨a, (isUnit_pow_iff hm.ne').1 hb, rfl⟩`.
-/
private theorem unitAt_of_pow_mul {x : Z} {f q : Z.functionField} {m : ℕ} (hm : 0 < m) (hf : RegAt x f)
    (hq : UnitAt x q) (h : UnitAt x (f ^ m * q)) : UnitAt x f := by
  have h1 := h.mul hq.inv
  rw [mul_inv_cancel_right₀ hq.ne_zero] at h1
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, hb, e⟩ := h1
  rw [← map_pow] at e
  have := IsFractionRing.injective (Z.presheaf.stalk x) Z.functionField e
  rw [this] at hb
  exact ⟨a, (isUnit_pow_iff hm.ne').1 hb, rfl⟩

/- English proof (translation)
Establish `: (w ∈ ((Finset.univ.inf U : Z.Opens) : Set Z)) ↔ ∀ i, w ∈ U i`. Rewrite using `[TopologicalSpace.Opens.coe_finset_inf]`. Simplify using the standard rewrite rules. Conclude with `this`.
-/
private theorem mem_inf {I : Type} [Fintype I] (U : I → Z.Opens) (w : Z) : w ∈ Finset.univ.inf U ↔ ∀ i, w ∈ U i := by
  have : (w ∈ ((Finset.univ.inf U : Z.Opens) : Set Z)) ↔ ∀ i, w ∈ U i := by
    rw [TopologicalSpace.Opens.coe_finset_inf]
    simp
  exact this

end Gen

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `hk`. Rewrite using `[Fin.prod_univ_castSucc, _root_.mul_assoc, ← ih (Nat.le_of_succ_le hk)]`. Use `congr 1`. Conclude with `h (Fin.castLE hk (Fin.last k))`.
-/
private theorem telescope {r : ℕ} (a : Fin r → ℝ) (ν : ℕ → ℝ) (h : ∀ i : Fin r, a i * ν (i + 1) = ν i) :
    ∀ (k : ℕ) (hk : k ≤ r), (∏ i : Fin k, a (Fin.castLE hk i)) * ν k = ν 0 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [Fin.prod_univ_castSucc, _root_.mul_assoc, ← ih (Nat.le_of_succ_le hk)]
    congr 1
    exact h (Fin.castLE hk (Fin.last k))

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

/- English proof (translation)
Establish `key : ∀ a b : AlgebraicClosure F, e.w a ≤ e.w b → e.w (a + b) ≤ e.w b`. Introduce `a b hab`. Distinguish the cases in `h0 : b = 0`. Substitute `h0` using the available equality. Simplify using `using hab`.

Establish `hb0 : 0 < e.w b` using `e.w.pos h0`. Establish `h1 : a / b ∈ e.O` using `(e.mem_O _).2 (by rw [map_div₀]; exact (div_le_one hb0).2 hab)`. Establish `h2 : a / b + 1 ∈ e.O` using `add_mem h1 e.O.one_mem`. Establish `h3 : a + b = (a / b + 1) * b` using `by field_simp`. Rewrite using `[h3, map_mul]`.

Conclude with `(mul_le_mul_of_nonneg_right ((e.mem_O _).1 h2) (e.w.nonneg _)).trans_eq (_root_.one_mul _)`. Introduce `a b`. Break down `le_total (e.w a) (e.w b) with h | h` into its components or cases. Conclude with `(key a b h).trans (le_max_right _ _)`. Rewrite using `[add_comm]`.

Conclude with `(key b a h).trans (le_max_left _ _)`.
-/
private theorem nonarch {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) : IsNonarchimedean e.w := by
  have key : ∀ a b : AlgebraicClosure F, e.w a ≤ e.w b → e.w (a + b) ≤ e.w b := by
    intro a b hab
    by_cases h0 : b = 0
    · subst h0
      simpa using hab
    have hb0 : 0 < e.w b := e.w.pos h0
    have h1 : a / b ∈ e.O := (e.mem_O _).2 (by rw [map_div₀]; exact (div_le_one hb0).2 hab)
    have h2 : a / b + 1 ∈ e.O := add_mem h1 e.O.one_mem
    have h3 : a + b = (a / b + 1) * b := by field_simp
    rw [h3, map_mul]
    exact (mul_le_mul_of_nonneg_right ((e.mem_O _).1 h2) (e.w.nonneg _)).trans_eq (_root_.one_mul _)
  intro a b
  rcases le_total (e.w a) (e.w b) with h | h
  · exact (key a b h).trans (le_max_right _ _)
  · rw [add_comm]
    exact (key b a h).trans (le_max_left _ _)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(z ≫ V.j) _ ∈ U'`. Rewrite using `[← h]`. Conclude with `hU (x := spMap e.O.subtype _) trivial`.
-/
private theorem below_mem (V : Cover Y) {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) (h : spMap e.O.subtype ≫ yt = z ≫ V.j)
    {U' : V.X.Opens} (hU : ⊤ ≤ yt ⁻¹ᵁ U') : V.j (below z) ∈ U' := by
  change (z ≫ V.j) _ ∈ U'
  rw [← h]
  exact hU (x := spMap e.O.subtype _) trivial

/- English proof (translation)
Use `haveI := RootLine.isPreimmersion_j V`. Establish `hη` using `RootLine.j_gen_specializes V`. Take `⟨t, rfl⟩` from `fnMap_surjective V.j hη g`. Establish `hreg` using `GlobalTheory.T.good_reduction_extends_regular F Y V p hp W hW U t (fun z hz => (regAt_fnMap_iff V.j hη).1 (hg z hz)) (fun v hv e y hy z yt hzy hyt hU => by`. Rewrite using `[← valAt_fnMap V.j hη z ((regAt_fnMap_iff V.j hη).1 (hg _ (below_mem V e z yt hyt hU)))]`.

Conclude with `hle v e y z yt ⟨hv, hy, hzy, hyt⟩ hU)`. Establish `hc : ¬ IsUnit (p : V.X.presheaf.stalk (yt₀ (IsLocalRing.closedPoint e₀.O)))` using `fun h => hx (by`. Use `h.map (V.X.presheaf.stalkSpecializes hs).hom` as an intermediate fact. Rewrite using `[map_natCast] at this)` and apply the resulting hypothesis. Establish `hr` using `hreg _ (hU₀ (x := IsLocalRing.closedPoint e₀.O) trivial) hc`.

Take `⟨hb, -, hiff⟩` from `UpperTheory.valuation_regular_function_at_point F Y V v₀ e₀ z₀ yt₀ h₀ t hr`. Rewrite `h1` using `[valAt_fnMap V.j hη z₀ hb]`. Take `⟨U', hxU', hU'⟩` from `(NormExt.unitAt_of_specializes hs (hiff.1 h1)).exists_nhds`. Use `⟨U', hxU', fun z hz => RootLine.unitAt_fnMap V.j hη (hU' _ hz), fun v e y z yt ht hU => ?_⟩` and prove the remaining obligations. Establish `hu` using `hU' _ (hU (x := IsLocalRing.closedPoint e.O) trivial)`.

Take `⟨hb, -, hiff⟩` from `UpperTheory.valuation_regular_function_at_point F Y V v e z yt ht.2.2.2 t hu.regAt`. Rewrite using `[valAt_fnMap V.j hη z hb]`. Conclude with `hiff.2 hu`.
-/
private theorem unit_nhds (V : Cover Y) (W : Y.X.Opens) (p : ℕ) (hp : p.Prime) (hW : genericPoint Y.X ∈ W)
    (U : V.X.Opens) (g : V.G.functionField) (hg : ∀ z : V.G, V.j z ∈ U → RegAt z g)
    (hle : ∀ v e y z yt, Tst V W p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ U → e.w (TrueGeo.valAt z g) ≤ 1)
    (x : V.X) (hx : ¬ IsUnit (p : V.X.presheaf.stalk x)) {v₀ : HeightOneSpectrum (𝓞 F)} (e₀ : TrueGeo.Ext v₀)
    (z₀ : Sp (AlgebraicClosure F) ⟶ V.G) (yt₀ : Sp e₀.O ⟶ V.X) (h₀ : spMap e₀.O.subtype ≫ yt₀ = z₀ ≫ V.j)
    (hU₀ : ⊤ ≤ yt₀ ⁻¹ᵁ U) (hs : x ⤳ yt₀ (IsLocalRing.closedPoint e₀.O)) (h1 : e₀.w (TrueGeo.valAt z₀ g) = 1) :
    ∃ U' : V.X.Opens, x ∈ U' ∧ (∀ z : V.G, V.j z ∈ U' → UnitAt z g) ∧
      ∀ v e y z yt, Tst V W p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ U' → e.w (TrueGeo.valAt z g) = 1 := by
  haveI := RootLine.isPreimmersion_j V
  have hη := RootLine.j_gen_specializes V
  obtain ⟨t, rfl⟩ := fnMap_surjective V.j hη g
  have hreg := GlobalTheory.T.good_reduction_extends_regular F Y V p hp W hW U t (fun z hz => (regAt_fnMap_iff V.j hη).1 (hg z hz))
    (fun v hv e y hy z yt hzy hyt hU => by
      rw [← valAt_fnMap V.j hη z ((regAt_fnMap_iff V.j hη).1 (hg _ (below_mem V e z yt hyt hU)))]
      exact hle v e y z yt ⟨hv, hy, hzy, hyt⟩ hU)
  have hc : ¬ IsUnit (p : V.X.presheaf.stalk (yt₀ (IsLocalRing.closedPoint e₀.O))) := fun h => hx (by
    have := h.map (V.X.presheaf.stalkSpecializes hs).hom
    rwa [map_natCast] at this)
  have hr := hreg _ (hU₀ (x := IsLocalRing.closedPoint e₀.O) trivial) hc
  obtain ⟨hb, -, hiff⟩ := UpperTheory.valuation_regular_function_at_point F Y V v₀ e₀ z₀ yt₀ h₀ t hr
  rw [valAt_fnMap V.j hη z₀ hb] at h1
  obtain ⟨U', hxU', hU'⟩ := (NormExt.unitAt_of_specializes hs (hiff.1 h1)).exists_nhds
  refine ⟨U', hxU', fun z hz => RootLine.unitAt_fnMap V.j hη (hU' _ hz), fun v e y z yt ht hU => ?_⟩
  have hu := hU' _ (hU (x := IsLocalRing.closedPoint e.O) trivial)
  obtain ⟨hb, -, hiff⟩ := UpperTheory.valuation_regular_function_at_point F Y V v e z yt ht.2.2.2 t hu.regAt
  rw [valAt_fnMap V.j hη z hb]
  exact hiff.2 hu

/- English proof (translation)
Use `choose m hm H using h`. Use `choose U s hxU hu hl using fun i => H i x hx`. Establish `hd : ∀ i, ∃ c, ∏ j, m j = m i * c` using `fun i => Finset.dvd_prod_of_mem m (Finset.mem_univ i)`. Use `choose c hc using hd`. Establish `hmem` using `mem_inf U`.

Use `⟨∏ j, m j, Finset.univ.inf U, fun i => s i ^ c i, Finset.prod_pos fun i _ => hm i, (hmem x).2 hxU, fun i z hz => ?_, fun i v e y z yt ht hU => ?_⟩` and prove the remaining obligations. Rewrite using `[hc i, pow_mul, ← mul_pow]`. Conclude with `unitAt_pow (hu i z ((hmem _).1 hz i)) _`. Establish `hUi : ⊤ ≤ yt ⁻¹ᵁ U i` using `fun q hq => (hmem _).1 (hU hq) i`. Establish `hπ : V.π (below z) = below y.1` using `by rw [← ht.2.2.1]; rfl`.

Establish `h2` using `hu i _ (below_mem V e z yt ht.2.2.2 hUi)`. Rewrite `h2` using `[hπ]`. Rewrite using `[hc i, pow_mul, ← mul_pow, valAt_pow h2.regAt, AbsoluteValue.map_pow, Real.log_pow, ← hl i v e y z yt ht hUi]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem common (V : Cover Y) (p : ℕ) {r : ℕ} (f : Fin r → Y.X → Y.Fn) (l : Fin r → PtFn Y)
    (h : ∀ i, PowRead V p (f i) (l i)) (x : V.X) (hx : ¬ IsUnit (p : V.X.presheaf.stalk x)) :
    ∃ (m : ℕ) (U : V.X.Opens) (s : Fin r → V.G.functionField), 0 < m ∧ x ∈ U ∧
      (∀ i (z : V.G), V.j z ∈ U → UnitAt z (V.φ (f i (V.π z)) ^ m * s i)) ∧
      ∀ i v e y z yt, Tst V ⊤ p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ U →
        m * l i v e y = Real.log (e.w (TrueGeo.valAt z (V.φ (f i (below y.1)) ^ m * s i))) := by
  choose m hm H using h
  choose U s hxU hu hl using fun i => H i x hx
  have hd : ∀ i, ∃ c, ∏ j, m j = m i * c := fun i => Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  choose c hc using hd
  have hmem := mem_inf U
  refine ⟨∏ j, m j, Finset.univ.inf U, fun i => s i ^ c i, Finset.prod_pos fun i _ => hm i, (hmem x).2 hxU,
    fun i z hz => ?_, fun i v e y z yt ht hU => ?_⟩
  · rw [hc i, pow_mul, ← mul_pow]
    exact unitAt_pow (hu i z ((hmem _).1 hz i)) _
  · have hUi : ⊤ ≤ yt ⁻¹ᵁ U i := fun q hq => (hmem _).1 (hU hq) i
    have hπ : V.π (below z) = below y.1 := by rw [← ht.2.2.1]; rfl
    have h2 := hu i _ (below_mem V e z yt ht.2.2.2 hUi)
    rw [hπ] at h2
    rw [hc i, pow_mul, ← mul_pow, valAt_pow h2.regAt, AbsoluteValue.map_pow, Real.log_pow, ← hl i v e y z yt ht hUi]
    push_cast
    ring

private noncomputable def fac (V : Cover Y) {r : ℕ} (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn) (f : Fin r → Y.X → Y.Fn) (m : ℕ)
    (s : Fin r → V.G.functionField) (x : Y.X) (i : Fin r) : V.G.functionField :=
  V.φ (f i x * T x i i) ^ m * (V.φ (f i x) ^ m * s i)⁻¹

/- English proof (translation)
Establish `hT' : ((T x).map V.φ).BlockTriangular id` using `fun a b h => by`. Rewrite using `[Matrix.map_apply, hT h, map_zero]`. Establish `hd : IsUnit ((T x).map V.φ).det`. Rewrite using `[Matrix.det_of_upperTriangular hT', isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]`. Introduce `i _`.

Conclude with `(map_ne_zero V.φ).2 (right_ne_zero_of_mul (hu i).ne_zero)`. Establish `e : X = locM V X T x * (T x).map V.φ`. Rewrite using `[RootFrame.locM, Matrix.nonsing_inv_mul_cancel_right _ _ hd]`. Use `conv_lhs => rw [e]`. Rewrite using `[UpperTheory.colMinor_mul_triangular _ _ _ _ _ hT', mul_pow, _root_.mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h0 : V.φ (f (Fin.castLE hk i) x) ≠ 0` using `(map_ne_zero V.φ).2 (left_ne_zero_of_mul (hu _).ne_zero)`. Rewrite using `[fac, Matrix.map_apply, map_mul, mul_pow, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel₀ (pow_ne_zero _ h0), _root_.one_mul]`.
-/
private theorem minor_eq (V : Cover Y) {n r : ℕ} (X : Matrix (Fin n) (Fin r) V.G.functionField)
    (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn) (f : Fin r → Y.X → Y.Fn) (m : ℕ) (s : Fin r → V.G.functionField) (x : Y.X)
    (hT : (T x).BlockTriangular id) (hu : ∀ i, UnitAt x (f i x * T x i i)) (k : ℕ) (hk : k ≤ r) (σ : Fin k → Fin n) :
    colMinor X k hk σ ^ m * ∏ i : Fin k, (s (Fin.castLE hk i))⁻¹ =
      colMinor (locM V X T x) k hk σ ^ m * ∏ i : Fin k, fac V T f m s x (Fin.castLE hk i) := by
  have hT' : ((T x).map V.φ).BlockTriangular id := fun a b h => by
    rw [Matrix.map_apply, hT h, map_zero]
  have hd : IsUnit ((T x).map V.φ).det := by
    rw [Matrix.det_of_upperTriangular hT', isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    exact (map_ne_zero V.φ).2 (right_ne_zero_of_mul (hu i).ne_zero)
  have e : X = locM V X T x * (T x).map V.φ := by
    rw [RootFrame.locM, Matrix.nonsing_inv_mul_cancel_right _ _ hd]
  conv_lhs => rw [e]
  rw [UpperTheory.colMinor_mul_triangular _ _ _ _ _ hT', mul_pow, _root_.mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : V.φ (f (Fin.castLE hk i) x) ≠ 0 := (map_ne_zero V.φ).2 (left_ne_zero_of_mul (hu _).ne_zero)
  rw [fac, Matrix.map_apply, map_mul, mul_pow, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel₀ (pow_ne_zero _ h0),
    _root_.one_mul]

/- English proof (translation)
Take `⟨hη, e⟩` from `V.φ_eq_fnMap`. Use `(unitAt_pow ?_ m).mul hs.inv` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `RootLine.unitAt_fnMap V.π hη hu`.
-/
private theorem unitAt_fac (V : Cover Y) {r : ℕ} (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn) (f : Fin r → Y.X → Y.Fn)
    (m : ℕ) (s : Fin r → V.G.functionField) (z : V.G) (i : Fin r)
    (hu : UnitAt (V.π z) (f i (V.π z) * T (V.π z) i i)) (hs : UnitAt z (V.φ (f i (V.π z)) ^ m * s i)) :
    UnitAt z (fac V T f m s (V.π z) i) := by
  obtain ⟨hη, e⟩ := V.φ_eq_fnMap
  refine (unitAt_pow ?_ m).mul hs.inv
  rw [e]
  exact RootLine.unitAt_fnMap V.π hη hu

/- English proof (translation)
Take `⟨hη, E⟩` from `V.φ_eq_fnMap`. Establish `hπ : V.π (below z) = below y.1` using `by rw [← hz]; rfl`. Establish `hu' : UnitAt (V.π (below z)) (f i (below y.1) * T (below y.1) i i)` using `hπ ▸ hu`. Establish `hφ : UnitAt (below z) (V.φ (f i (below y.1) * T (below y.1) i i))`. Rewrite using `[E]`.

Conclude with `RootLine.unitAt_fnMap V.π hη hu'`. Establish `hv : TrueGeo.valAt z (V.φ (f i (below y.1) * T (below y.1) i i)) = TrueGeo.valAt y.1 (f i (below y.1) * T (below y.1) i i)`. Rewrite using `[E, valAt_fnMap V.π hη z hu'.regAt, hz]`. Rewrite using `[fac, valAt_mul (unitAt_pow hφ m).regAt hs.inv.regAt, valAt_pow hφ.regAt, LineNorm.Neg.valAt_inv hs, hv, map_mul, map_inv₀, AbsoluteValue.map_pow]`. Establish `p1` using `e.w.pos (valAt_ne_zero hu)`.

Establish `p2` using `e.w.pos (valAt_ne_zero hs)`. Use `Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity)) ?_` and prove the remaining obligations. Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_pow, Real.log_pow, Real.log_pow, ← h2, h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem w_fac (V : Cover Y) {r : ℕ} (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn) (f : Fin r → Y.X → Y.Fn)
    (m : ℕ) (s : Fin r → V.G.functionField) {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) (y : AlgPt Y)
    (z : Sp (AlgebraicClosure F) ⟶ V.G) (hz : z ≫ V.π = y.1) (i : Fin r)
    (hu : UnitAt (below y.1) (f i (below y.1) * T (below y.1) i i))
    (hs : UnitAt (below z) (V.φ (f i (below y.1)) ^ m * s i)) (L a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : L = Real.log (e.w (TrueGeo.valAt y.1 (f i (below y.1) * T (below y.1) i i))) + Real.log a - Real.log b)
    (h2 : m * L = Real.log (e.w (TrueGeo.valAt z (V.φ (f i (below y.1)) ^ m * s i)))) :
    e.w (TrueGeo.valAt z (fac V T f m s (below y.1) i)) * a ^ m = b ^ m := by
  obtain ⟨hη, E⟩ := V.φ_eq_fnMap
  have hπ : V.π (below z) = below y.1 := by rw [← hz]; rfl
  have hu' : UnitAt (V.π (below z)) (f i (below y.1) * T (below y.1) i i) := hπ ▸ hu
  have hφ : UnitAt (below z) (V.φ (f i (below y.1) * T (below y.1) i i)) := by
    rw [E]; exact RootLine.unitAt_fnMap V.π hη hu'
  have hv : TrueGeo.valAt z (V.φ (f i (below y.1) * T (below y.1) i i)) =
      TrueGeo.valAt y.1 (f i (below y.1) * T (below y.1) i i) := by
    rw [E, valAt_fnMap V.π hη z hu'.regAt, hz]
  rw [fac, valAt_mul (unitAt_pow hφ m).regAt hs.inv.regAt, valAt_pow hφ.regAt, LineNorm.Neg.valAt_inv hs, hv,
    map_mul, map_inv₀, AbsoluteValue.map_pow]
  have p1 := e.w.pos (valAt_ne_zero hu)
  have p2 := e.w.pos (valAt_ne_zero hs)
  refine Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity)) ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_inv,
    Real.log_pow, Real.log_pow, Real.log_pow, ← h2, h1]
  ring

end UpperTheory.NonarchimedeanMinorValuations

open UpperTheory.NonarchimedeanMinorValuations GlobalTheory.TrueGeo.SmallSec in
/- English proof (translation)
Introduce `F _ _ Y V W p J U n r X T f l hp hW hS hP a x hxa hx`. Take `⟨hT, hR, hN⟩` from `hS`. Take `⟨m, U₀, s, hm, hx₀, hs, hl⟩` from `common V p f l hP x hx`. Set `g : ∀ k, k ≤ r → (Fin k → Fin n) → V.G.functionField` to `fun k hk σ => colMinor (X a) k hk σ ^ m * ∏ i : Fin k, (s (Fin.castLE hk i))⁻¹`. Establish `hg : ∀ (w : Y.X) k hk σ, g k hk σ = colMinor (locM V (X a) T w) k hk σ ^ m * ∏ i : Fin k, fac V T f m s w (Fin.castLE hk i)` using `fun w k hk σ => minor_eq V (X a) T f m s w (hT w).1 (hT w).2 k hk σ`.

Establish `hq : ∀ z : V.G, V.j z ∈ U a ⊓ U₀ → ∀ i, UnitAt z (fac V T f m s (V.π z) i)` using `fun z hz i => unitAt_fac V T f m s z i ((hT _).2 i) (hs i z hz.2)`. Establish `hreg : ∀ k hk σ (z : V.G), V.j z ∈ U a ⊓ U₀ → RegAt z (g k hk σ)` using `fun k hk σ z hz => by`. Rewrite using `[hg (V.π z)]`. Conclude with `(regAt_pow (regAt_colMinor (hR a z hz.1) k hk σ) m).mul (unitAt_prod fun i => hq z hz _).regAt`. Establish `hval : ∀ v e y z yt, Tst V W p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ (U a ⊓ U₀) → ∃ ν : ℕ → ℝ, (∀ k, k ≤ r → 0 < ν k) ∧ (∀ k (hk : k ≤ r) σ, e.w (colMinor (vals V (X a) T z (below y.1)) k hk σ) ≤ ν k) ∧ (∀ k (hk : k ≤ r), ∃ σ, e.w (colMinor (vals V (X a) T z (below y.1)) k hk σ) = ν k) ∧ ∀ k h …`.

Introduce `v e y z yt ht hU`. Take `⟨⟨ν, h0, h1, h2, h3⟩, -⟩` from `hN v e y z yt ht a (fun q hq => (hU hq).1)`. Use `⟨ν, h0, h2, h3, fun k hk σ => ?_⟩` and prove the remaining obligations. Establish `hπ : V.π (below z) = below y.1` using `by rw [← ht.2.2.1]; rfl`. Establish `hz` using `below_mem V e z yt ht.2.2.2 hU`.

Establish `hq'` using `hq _ hz`. Establish `hR'` using `hR a _ hz.1`. Establish `hs'` using `fun i => hs i _ hz.2`. Rewrite `hq'`, `hR'`, `hs'` using `[hπ]`. Establish `hν : ν 0 = 1`.

Take `⟨τ, hτ⟩` from `h3 0 (Nat.zero_le _)`. Rewrite using `[← hτ, colMinor, Matrix.det_isEmpty, map_one]`. Establish `tel` using `telescope (fun i => e.w (TrueGeo.valAt z (fac V T f m s (below y.1) i))) (fun k => ν k ^ m) (fun i => w_fac V T f m s e y z ht.2.2.1 i ((hT _).2 i) (hs' i) _ _ _ (h0 _ i.2) (h0 _ i.2.le) (h1 i) (hl i v e y z yt ⟨ht.1, trivial, ht.2.2⟩ fun q hq => (hU hq).2)) k hk`. Simplify using `only [hν, one_pow] at tel`. Rewrite using `[hg (below y.1), valAt_mul (regAt_pow (regAt_colMinor hR' k hk σ) m) (unitAt_prod fun i => hq' _).regAt, valAt_pow (regAt_colMinor hR' k hk σ), valAt_colMinor hR', valAt_prod fun i => (hq' _).regAt, map_mul, map_prod, AbsoluteValue.map_pow, _root_.mul_assoc, tel, _root_.mul_one]`.

Both sides reduce to the same expression. Establish `hle : ∀ k hk σ v e y z yt, Tst V W p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ (U a ⊓ U₀) → e.w (TrueGeo.valAt z (g k hk σ)) ≤ 1`. Introduce `k hk σ v e y z yt ht hU`. Take `⟨ν, h0, h2, -, h4⟩` from `hval v e y z yt ht hU`. Use `le_of_mul_le_mul_right ?_ (pow_pos (h0 k hk) m)` and prove the remaining obligations.

Rewrite using `[h4, _root_.one_mul]`. Conclude with `pow_le_pow_left₀ (e.w.nonneg _) (h2 k hk σ) m`. Take `⟨v₀, e₀, y₀, z₀, yt₀, t1, t2, t3, t4, hU₀, hsp⟩` from `GlobalTheory.T.exists_algebraic_point_specializing F Y V p hp W hW (U a ⊓ U₀) x ⟨hxa, hx₀⟩ hx`. Take `⟨ν, h0, h2, h3, h4⟩` from `hval v₀ e₀ y₀ z₀ yt₀ ⟨t1, t2, t3, t4⟩ hU₀`. Take `⟨σ, hσ⟩` from `UpperTheory.exists_rows_attaining_minor_values _ e₀.w (nonarch e₀) n r _ ν h0 h2 h3`.

Establish `key` using `fun k : Fin (r + 1) => unit_nhds V W p hp hW (U a ⊓ U₀) (g k (Nat.le_of_lt_succ k.2) fun i => σ (Fin.castLE (Nat.le_of_lt_succ k.2) i)) (hreg _ _ _) (hle _ _ _) x hx e₀ z₀ yt₀ t4 hU₀ hsp (by`. Use `mul_right_cancel₀ (pow_pos (h0 k (Nat.le_of_lt_succ k.2)) m).ne' ?_` and prove the remaining obligations. Rewrite using `[h4, _root_.one_mul, ← hσ k (Nat.le_of_lt_succ k.2)]`. Use the proof step `rfl)`. Use `choose U' hxU' hu h1 using key`.

Use `⟨(U a ⊓ U₀) ⊓ Finset.univ.inf U', σ, ⟨⟨hxa, hx₀⟩, (mem_inf U' x).2 hxU'⟩, inf_le_left.trans inf_le_left, fun z hz k hk => ?_, fun v e y z yt ht hU k hk σ' => ?_⟩` and prove the remaining obligations. Establish `h5` using `hu ⟨k, Nat.lt_succ_of_le hk⟩ z ((mem_inf U' _).1 hz.2 _)`. Rewrite `h5` using `[hg (V.π z)]`. Conclude with `unitAt_of_pow_mul hm (regAt_colMinor (hR a z hz.1.1) k hk _) (unitAt_prod fun i => hq z hz.1 _) h5`. Take `⟨ν', k0, k2, -, k4⟩` from `hval v e y z yt ht fun q hq => (hU hq).1`.

Establish `h5` using `h1 ⟨k, Nat.lt_succ_of_le hk⟩ v e y z yt ht fun q hq => (mem_inf U' _).1 (hU hq).2 _`. Establish `h6` using `k4 k hk fun i => σ (Fin.castLE hk i)`. Rewrite `h6` using `[h5, _root_.one_mul]`. Conclude with `(k2 k hk σ').trans_eq ((pow_left_inj₀ (k0 k hk).le (e.w.nonneg _) hm.ne').1 h6)`.
-/
theorem UpperTheory.side_data_nonunit_on_chart :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (W : Y.X.Opens) (p : ℕ) (J : Type) (U : J → V.X.Opens) (n r : ℕ) (X : J → Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn) (f : Fin r → Y.X → Y.Fn) (l : Fin r → PtFn Y), p.Prime → genericPoint Y.X ∈ W → SideData V W p U X T f l → (∀ i, PowRead V p (f i) (l i)) → ∀ (a : J) (x : V.X), x ∈ U a → ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ (U' : V.X.Opens) (σ : Fin r → Fin n), x ∈ U' ∧ U' ≤ U a ∧ GoodOn V W p U' (X a) T σ := by
  intro F _ _ Y V W p J U n r X T f l hp hW hS hP a x hxa hx
  obtain ⟨hT, hR, hN⟩ := hS
  obtain ⟨m, U₀, s, hm, hx₀, hs, hl⟩ := common V p f l hP x hx
  let g : ∀ k, k ≤ r → (Fin k → Fin n) → V.G.functionField := fun k hk σ =>
    colMinor (X a) k hk σ ^ m * ∏ i : Fin k, (s (Fin.castLE hk i))⁻¹
  have hg : ∀ (w : Y.X) k hk σ, g k hk σ =
      colMinor (locM V (X a) T w) k hk σ ^ m * ∏ i : Fin k, fac V T f m s w (Fin.castLE hk i) :=
    fun w k hk σ => minor_eq V (X a) T f m s w (hT w).1 (hT w).2 k hk σ
  have hq : ∀ z : V.G, V.j z ∈ U a ⊓ U₀ → ∀ i, UnitAt z (fac V T f m s (V.π z) i) :=
    fun z hz i => unitAt_fac V T f m s z i ((hT _).2 i) (hs i z hz.2)
  have hreg : ∀ k hk σ (z : V.G), V.j z ∈ U a ⊓ U₀ → RegAt z (g k hk σ) := fun k hk σ z hz => by
    rw [hg (V.π z)]
    exact (regAt_pow (regAt_colMinor (hR a z hz.1) k hk σ) m).mul (unitAt_prod fun i => hq z hz _).regAt
  have hval : ∀ v e y z yt, Tst V W p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ (U a ⊓ U₀) → ∃ ν : ℕ → ℝ, (∀ k, k ≤ r → 0 < ν k) ∧
      (∀ k (hk : k ≤ r) σ, e.w (colMinor (vals V (X a) T z (below y.1)) k hk σ) ≤ ν k) ∧
      (∀ k (hk : k ≤ r), ∃ σ, e.w (colMinor (vals V (X a) T z (below y.1)) k hk σ) = ν k) ∧
      ∀ k hk σ, e.w (TrueGeo.valAt z (g k hk σ)) * ν k ^ m =
        e.w (colMinor (vals V (X a) T z (below y.1)) k hk σ) ^ m := by
    intro v e y z yt ht hU
    obtain ⟨⟨ν, h0, h1, h2, h3⟩, -⟩ := hN v e y z yt ht a (fun q hq => (hU hq).1)
    refine ⟨ν, h0, h2, h3, fun k hk σ => ?_⟩
    have hπ : V.π (below z) = below y.1 := by rw [← ht.2.2.1]; rfl
    have hz := below_mem V e z yt ht.2.2.2 hU
    have hq' := hq _ hz
    have hR' := hR a _ hz.1
    have hs' := fun i => hs i _ hz.2
    rw [hπ] at hq' hR' hs'
    have hν : ν 0 = 1 := by
      obtain ⟨τ, hτ⟩ := h3 0 (Nat.zero_le _)
      rw [← hτ, colMinor, Matrix.det_isEmpty, map_one]
    have tel := telescope (fun i => e.w (TrueGeo.valAt z (fac V T f m s (below y.1) i))) (fun k => ν k ^ m)
      (fun i => w_fac V T f m s e y z ht.2.2.1 i ((hT _).2 i) (hs' i) _ _ _ (h0 _ i.2) (h0 _ i.2.le) (h1 i)
        (hl i v e y z yt ⟨ht.1, trivial, ht.2.2⟩ fun q hq => (hU hq).2)) k hk
    simp only [hν, one_pow] at tel
    rw [hg (below y.1), valAt_mul (regAt_pow (regAt_colMinor hR' k hk σ) m) (unitAt_prod fun i => hq' _).regAt,
      valAt_pow (regAt_colMinor hR' k hk σ), valAt_colMinor hR', valAt_prod fun i => (hq' _).regAt, map_mul,
      map_prod, AbsoluteValue.map_pow, _root_.mul_assoc, tel, _root_.mul_one]
    rfl
  have hle : ∀ k hk σ v e y z yt, Tst V W p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ (U a ⊓ U₀) →
      e.w (TrueGeo.valAt z (g k hk σ)) ≤ 1 := by
    intro k hk σ v e y z yt ht hU
    obtain ⟨ν, h0, h2, -, h4⟩ := hval v e y z yt ht hU
    refine le_of_mul_le_mul_right ?_ (pow_pos (h0 k hk) m)
    rw [h4, _root_.one_mul]
    exact pow_le_pow_left₀ (e.w.nonneg _) (h2 k hk σ) m
  obtain ⟨v₀, e₀, y₀, z₀, yt₀, t1, t2, t3, t4, hU₀, hsp⟩ := GlobalTheory.T.exists_algebraic_point_specializing F Y V p hp W hW (U a ⊓ U₀) x ⟨hxa, hx₀⟩ hx
  obtain ⟨ν, h0, h2, h3, h4⟩ := hval v₀ e₀ y₀ z₀ yt₀ ⟨t1, t2, t3, t4⟩ hU₀
  obtain ⟨σ, hσ⟩ := UpperTheory.exists_rows_attaining_minor_values _ e₀.w (nonarch e₀) n r _ ν h0 h2 h3
  have key := fun k : Fin (r + 1) => unit_nhds V W p hp hW (U a ⊓ U₀)
    (g k (Nat.le_of_lt_succ k.2) fun i => σ (Fin.castLE (Nat.le_of_lt_succ k.2) i)) (hreg _ _ _) (hle _ _ _) x hx
    e₀ z₀ yt₀ t4 hU₀ hsp (by
      refine mul_right_cancel₀ (pow_pos (h0 k (Nat.le_of_lt_succ k.2)) m).ne' ?_
      rw [h4, _root_.one_mul, ← hσ k (Nat.le_of_lt_succ k.2)]
      rfl)
  choose U' hxU' hu h1 using key
  refine ⟨(U a ⊓ U₀) ⊓ Finset.univ.inf U', σ, ⟨⟨hxa, hx₀⟩, (mem_inf U' x).2 hxU'⟩, inf_le_left.trans inf_le_left,
    fun z hz k hk => ?_, fun v e y z yt ht hU k hk σ' => ?_⟩
  · have h5 := hu ⟨k, Nat.lt_succ_of_le hk⟩ z ((mem_inf U' _).1 hz.2 _)
    rw [hg (V.π z)] at h5
    exact unitAt_of_pow_mul hm (regAt_colMinor (hR a z hz.1.1) k hk _) (unitAt_prod fun i => hq z hz.1 _) h5
  · obtain ⟨ν', k0, k2, -, k4⟩ := hval v e y z yt ht fun q hq => (hU hq).1
    have h5 := h1 ⟨k, Nat.lt_succ_of_le hk⟩ v e y z yt ht fun q hq => (mem_inf U' _).1 (hU hq).2 _
    have h6 := k4 k hk fun i => σ (Fin.castLE hk i)
    rw [h5, _root_.one_mul] at h6
    exact (k2 k hk σ').trans_eq ((pow_left_inj₀ (k0 k hk).le (e.w.nonneg _) hm.ne').1 h6)
