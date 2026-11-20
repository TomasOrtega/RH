import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ValuesEqOfCommonPointStatement

noncomputable section

namespace GlobalTheory.Reg.SecGlue

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def liftF {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by
    rw [y.x_over, spMap_comp_ring]; rfl)

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
theorem liftF_fst {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    liftF y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) = y.x :=
  pullback.lift_fst _ _ _

/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
theorem liftF_snd {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    liftF y ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) = spMap (algebraMap c.F S) :=
  pullback.lift_snd _ _ _

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, liftF_fst, liftF_fst, h]`. Rewrite using `[Category.assoc, liftF_snd, liftF_snd, spMap_comp_ring]`. Use `congr 1`. Conclude with `RingHom.ext fun r => (φ.commutes r).symm`.
-/
theorem liftF_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (z : FrPt Xo c T) (h : z.x = spMap φ.toRingHom ≫ y.x) :
    liftF z = spMap φ.toRingHom ≫ liftF y := by
  apply pullback.hom_ext
  · rw [Category.assoc, liftF_fst, liftF_fst, h]
  · rw [Category.assoc, liftF_snd, liftF_snd, spMap_comp_ring]
    congr 1
    exact RingHom.ext fun r => (φ.commutes r).symm

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[liftF_fst, liftF_fst, h]`. Rewrite using `[liftF_snd, liftF_snd]`.
-/
theorem liftF_congr {S : Type} [CommRing S] [Algebra c.F S] (y z : FrPt Xo c S) (h : z.x = y.x) :
    liftF z = liftF y := by
  apply pullback.hom_ext
  · rw [liftF_fst, liftF_fst, h]
  · rw [liftF_snd, liftF_snd]

/- English proof (translation)
Establish `e : spMap (algebraMap c.F (kap Z)) = genSp Z ≫ strK` using `Spec.map_preimage _`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[liftF_fst, (isGenFr_genFr h Z).1, Category.assoc]`. Both sides reduce to the same expression. Rewrite using `[liftF_snd, Category.assoc] erw [← e]`.

Rewrite using `[spMap_comp_ring]`.
-/
theorem liftF_gen (h : GenFrEx Xo c) (Z : Comp Xo c) :
    liftF (genFr h Z) = spMap (algebraMap (kap Z) (Om Z)) ≫ genSp Z := by
  have e : spMap (algebraMap c.F (kap Z)) = genSp Z ≫ strK := Spec.map_preimage _
  apply pullback.hom_ext
  · rw [liftF_fst, (isGenFr_genFr h Z).1, Category.assoc]; rfl
  · rw [liftF_snd, Category.assoc]
    erw [← e]
    rw [spMap_comp_ring]

/- English proof (translation)
Rewrite using `[liftF_gen, Scheme.Hom.comp_apply]`. Conclude with `Scheme.fromSpecResidueField_apply _ _`.
-/
theorem liftF_gen_apply (h : GenFrEx Xo c) (Z : Comp Xo c) (p : Sp (Om Z)) :
    liftF (genFr h Z) p = genPt Z := by
  rw [liftF_gen, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

/- English proof (translation)
The claim follows from `((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)).def`.
-/
theorem closure_gen (Z : Comp Xo c) : closure {genPt Z} = (Z : Set (Xo.XF c)) :=
  ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents _ Z.2)).def

/- English proof (translation)
Establish `e1 : liftF (genFr h Z) = spMap ψ.toRingHom ≫ liftF C.y`. Rewrite using `[liftF_congr _ _ h2.1, liftF_map ψ _ _ h1.1]`. Establish `e2 : liftF (genFr h C.Z) = spMap C.R.val.toRingHom ≫ liftF C.y`. Rewrite using `[← liftF_congr _ _ C.bor.1, liftF_map _ _ _ C.gen.1]`. Set `p : Sp (Om Z)` to `IsLocalRing.closedPoint (Om Z)`.

Set `p' : Sp (Om C.Z)` to `IsLocalRing.closedPoint (Om C.Z)`. Establish `f1` using `liftF_gen_apply h Z p`. Establish `f2` using `liftF_gen_apply h C.Z p'`. Rewrite `f1` using `[e1, Scheme.Hom.comp_apply]`. Rewrite `f2` using `[e2, Scheme.Hom.comp_apply]`.

Establish `hs : (spMap C.R.val.toRingHom p' : Sp C.R) ⤳ spMap ψ.toRingHom p`. Use `(PrimeSpectrum.le_iff_specializes _ _).1 ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hx' : (x : Om C.Z) ∈ IsLocalRing.maximalIdeal (Om C.Z)` using `hx`. Rewrite `hx'` using `[IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]`.

Establish `: x = 0` using `Subtype.ext hx'`. Rewrite using `[this]`. Conclude with `Ideal.zero_mem _`. Establish `hs'` using `hs.map (liftF C.y).continuous`. Rewrite `hs'` using `[f1, f2]`.

Establish `hm : genPt Z ∈ (C.Z : Set (Xo.XF c))`. Rewrite using `[← closure_gen]`. Conclude with `hs'.mem_closure`. Establish `hsub : (Z : Set (Xo.XF c)) ⊆ C.Z`. Rewrite using `[← closure_gen Z]`.

Conclude with `closure_minimal (Set.singleton_subset_iff.2 hm) (isClosed_of_mem_irreducibleComponents _ C.Z.2)`. Conclude with `Subtype.ext (Set.Subset.antisymm (Z.2.2 C.Z.2.1 hsub) hsub)`.
-/
theorem chart_comp {h : GenFrEx Xo c} (Z : Comp Xo c) (C : FChart h) (ψ : C.R →ₐ[c.F] Om Z)
    (z : FrPt Xo c (Om Z)) (t : Ix Dw → (Om Z)ˣ) (h1 : FrMap ψ C.y z) (h2 : FrBor t z (genFr h Z)) : C.Z = Z := by
  have e1 : liftF (genFr h Z) = spMap ψ.toRingHom ≫ liftF C.y := by
    rw [liftF_congr _ _ h2.1, liftF_map ψ _ _ h1.1]
  have e2 : liftF (genFr h C.Z) = spMap C.R.val.toRingHom ≫ liftF C.y := by
    rw [← liftF_congr _ _ C.bor.1, liftF_map _ _ _ C.gen.1]
  let p : Sp (Om Z) := IsLocalRing.closedPoint (Om Z)
  let p' : Sp (Om C.Z) := IsLocalRing.closedPoint (Om C.Z)
  have f1 := liftF_gen_apply h Z p
  have f2 := liftF_gen_apply h C.Z p'
  rw [e1, Scheme.Hom.comp_apply] at f1
  rw [e2, Scheme.Hom.comp_apply] at f2
  have hs : (spMap C.R.val.toRingHom p' : Sp C.R) ⤳ spMap ψ.toRingHom p := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro x hx
    have hx' : (x : Om C.Z) ∈ IsLocalRing.maximalIdeal (Om C.Z) := hx
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hx'
    have : x = 0 := Subtype.ext hx'
    rw [this]
    exact Ideal.zero_mem _
  have hs' := hs.map (liftF C.y).continuous
  rw [f1, f2] at hs'
  have hm : genPt Z ∈ (C.Z : Set (Xo.XF c)) := by
    rw [← closure_gen]; exact hs'.mem_closure
  have hsub : (Z : Set (Xo.XF c)) ⊆ C.Z := by
    rw [← closure_gen Z]
    exact closure_minimal (Set.singleton_subset_iff.2 hm) (isClosed_of_mem_irreducibleComponents _ C.Z.2)
  exact Subtype.ext (Set.Subset.antisymm (Z.2.2 C.Z.2.1 hsub) hsub)

/- English proof (translation)
Simplify using `only [wchar, Pi.mul_apply, Units.val_mul, mul_pow, Finset.prod_mul_distrib]`.
-/
theorem wchar_mul {S : Type} [CommRing S] (e : Ix Dw → ℕ) (t t' : Ix Dw → Sˣ) :
    wchar e (t * t') = wchar e t * wchar e t' := by
  simp only [wchar, Pi.mul_apply, Units.val_mul, mul_pow, Finset.prod_mul_distrib]

/- English proof (translation)
Simplify using `[wchar]`.
-/
theorem wchar_one {S : Type} [CommRing S] (e : Ix Dw → ℕ) : wchar e (1 : Ix Dw → Sˣ) = 1 := by
  simp [wchar]

/- English proof (translation)
Simplify using `[wchar]`.
-/
theorem wchar_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (e : Ix Dw → ℕ) (t : Ix Dw → Sˣ) :
    wchar e (fun i => Units.map (φ : S →* T) (t i)) = φ (wchar e t) := by
  simp [wchar]

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Apply `IsNilpotent.eq_zero` to reduce the goal to its premises. Rewrite using `[nilpotent_iff_mem_prime]`. Introduce `P hP`. Use `hs (FractionRing (S ⧸ P)) ((IsScalarTower.toAlgHom K (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mkₐ K P))` as an intermediate fact.

Conclude with `Ideal.Quotient.eq.1 (IsFractionRing.injective (S ⧸ P) (FractionRing (S ⧸ P)) this)`.
-/
theorem eq_of_fields {K S : Type} [Field K] [CommRing S] [IsReduced S] [Algebra K S] (s s' : S)
    (hs : ∀ (L : Type) [Field L] [Algebra K L] (χ : S →ₐ[K] L), χ s = χ s') : s = s' := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro P hP
  have := hs (FractionRing (S ⧸ P))
    ((IsScalarTower.toAlgHom K (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mkₐ K P))
  exact Ideal.Quotient.eq.1 (IsFractionRing.injective (S ⧸ P) (FractionRing (S ⧸ P)) this)

section Val

variable {h : GenFrEx Xo c} {e : Ix Dw → ℕ} {b : ∀ Z : Comp Xo c, Om Z}
  (hb : ∀ C : FChart h, wchar e C.t * b C.Z ∈ C.R)

def Val {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ (C : FChart h) (ψ : C.R →ₐ[c.F] S) (z : FrPt Xo c S) (t : Ix Dw → Sˣ),
    FrMap ψ C.y z ∧ FrBor t z y ∧ v = wchar e t * ψ ⟨_, hb C⟩

/- English proof (translation)
Take `⟨C, ψ, z, t, hz, ht, rfl⟩` from `h1`. Take `⟨C', ψ', z', t', hz', ht', rfl⟩` from `h2`. Take `⟨-, hmul, hinv, -⟩` from `GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L`. Use `(GlobalTheory.T.values_eq_of_common_point E H Dw l Xo c hl h C C' L ψ ψ' z z' _ hz hz' (hmul _ _ _ _ _ ht (hinv _ _ _ ht'))).2 e b (hb C) (hb C')` as an intermediate fact. Rewrite using `[this, ← mul_assoc, ← wchar_mul, mul_comm t, mul_inv_cancel_left]`.
-/
theorem val_unique (hl : EvLaws Xo c) {L : Type} [Field L] [Algebra c.F L] {y : FrPt Xo c L} {v v' : L}
    (h1 : Val hb y v) (h2 : Val hb y v') : v = v' := by
  obtain ⟨C, ψ, z, t, hz, ht, rfl⟩ := h1
  obtain ⟨C', ψ', z', t', hz', ht', rfl⟩ := h2
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L
  have := (GlobalTheory.T.values_eq_of_common_point E H Dw l Xo c hl h C C' L ψ ψ' z z' _ hz hz'
    (hmul _ _ _ _ _ ht (hinv _ _ _ ht'))).2 e b (hb C) (hb C')
  rw [this, ← mul_assoc, ← wchar_mul, mul_comm t, mul_inv_cancel_left]

/- English proof (translation)
Take `⟨C, ψ, z, t, hz, ht, rfl⟩` from `h1`. Take `⟨z', hz'⟩` from `hl.bc S T φ z`. Use `⟨C, φ.comp ψ, z', _, frMap_trans _ _ _ ψ φ _ _ _ hz hz', frBorBC _ _ φ t z y z' y' ht hz' hy, ?_⟩` and prove the remaining obligations. Rewrite using `[wchar_map, map_mul]`. Both sides reduce to the same expression.
-/
theorem val_map (hl : EvLaws Xo c) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {y' : FrPt Xo c T} (hy : FrMap φ y y') {v : S} (h1 : Val hb y v) :
    Val hb y' (φ v) := by
  obtain ⟨C, ψ, z, t, hz, ht, rfl⟩ := h1
  obtain ⟨z', hz'⟩ := hl.bc S T φ z
  refine ⟨C, φ.comp ψ, z', _, frMap_trans _ _ _ ψ φ _ _ _ hz hz', frBorBC _ _ φ t z y z' y' ht hz' hy, ?_⟩
  rw [wchar_map, map_mul]; rfl

/- English proof (translation)
Take `⟨C, ψ, z, t₀, hz, ht, rfl⟩` from `h1`. Use `⟨C, ψ, z, t₀ * t, hz, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c S).2.1 _ _ _ _ _ ht hy, ?_⟩` and prove the remaining obligations. Rewrite using `[wchar_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem val_bor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S}
    (hy : FrBor t y y') {v : S} (h1 : Val hb y v) : Val hb y' (wchar e t * v) := by
  obtain ⟨C, ψ, z, t₀, hz, ht, rfl⟩ := h1
  refine ⟨C, ψ, z, t₀ * t, hz, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c S).2.1 _ _ _ _ _ ht hy, ?_⟩
  rw [wchar_mul]; ring

/- English proof (translation)
Take `⟨C, ψ, z, t, h1, h2⟩` from `hA L y`. Conclude with `⟨_, C, ψ, z, t, h1, h2, rfl⟩`.
-/
theorem val_ex (hA : Atlas h) {L : Type} [Field L] [Algebra c.F L] (y : FrPt Xo c L) : ∃ v, Val hb y v := by
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA L y
  exact ⟨_, C, ψ, z, t, h1, h2, rfl⟩

/- English proof (translation)
Take `⟨C, ψ, z, t, h1, h2⟩` from `hA _ (genFr h Z)`. Take `rfl` from `chart_comp Z C ψ z t h1 h2`. Use `⟨C, C.R.val, C.yg, C.t⁻¹, C.gen, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c _).2.2.1 _ _ _ C.bor, ?_⟩` and prove the remaining obligations. Use `show b C.Z = wchar e C.t⁻¹ * (wchar e C.t * b C.Z)`. Rewrite using `[← mul_assoc, ← wchar_mul, inv_mul_cancel, wchar_one, one_mul]`.
-/
theorem val_gen (hA : Atlas h) (Z : Comp Xo c) : Val hb (genFr h Z) (b Z) := by
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA _ (genFr h Z)
  obtain rfl := chart_comp Z C ψ z t h1 h2
  refine ⟨C, C.R.val, C.yg, C.t⁻¹, C.gen, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c _).2.2.1 _ _ _ C.bor, ?_⟩
  show b C.Z = wchar e C.t⁻¹ * (wchar e C.t * b C.Z)
  rw [← mul_assoc, ← wchar_mul, inv_mul_cancel, wchar_one, one_mul]

def Rep {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (g s : S) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (χ : S →ₐ[c.F] L) (w : FrPt Xo c L) (v : L),
    FrMap χ y w → Val hb w v → χ g * v = χ s

/- English proof (translation)
Set `I : Ideal S` to `{ carrier := {g | ∃ s, Rep hb y g s} zero_mem' := ⟨0, fun L _ _ χ w v _ _ => by simp⟩ add_mem' := by`. Introduce and unpack `g g' ⟨s, hs⟩ ⟨s', hs'⟩`. Conclude with `⟨s + s', fun L _ _ χ w v h1 h2 => by`. Rewrite using `[map_add, map_add, add_mul, hs L χ w v h1 h2, hs' L χ w v h1 h2]⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `r g ⟨s, hs⟩`. Conclude with `⟨r * s, fun L _ _ χ w v h1 h2 => by`. Rewrite using `[smul_eq_mul, map_mul, map_mul, mul_assoc, hs L χ w v h1 h2]⟩ }`. Assume the negation of the conclusion as `hne`. Establish `hI : I ≠ ⊤` using `fun hI => hne ((Ideal.eq_top_iff_one I).1 hI)`.

Take `⟨P, hP, hIP⟩` from `Ideal.exists_le_maximal I hI`. Use `hP.isPrime` as an intermediate fact. Set `χ₀ : S →ₐ[c.F] FractionRing (S ⧸ P)` to `(IsScalarTower.toAlgHom c.F (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mkₐ c.F P)`. Take `⟨w₀, hw₀⟩` from `hl.bc _ _ χ₀ y`. Take `⟨C, ψ₀, z₀, t₀, h1, h2⟩` from `hA _ w₀`.

Take `⟨g, hg, hloc⟩` from `C.opn S _ χ₀ y w₀ hw₀ ⟨ψ₀, z₀, t₀, h1, h2⟩`. Set `lam : S →ₐ[c.F] Localization.Away g` to `IsScalarTower.toAlgHom c.F S _`. Establish `hu : IsUnit (lam g)` using `IsLocalization.Away.algebraMap_isUnit g`. Take `⟨w', hw'⟩` from `hl.bc _ _ lam y`. Take `⟨ψ, z, t, h3, h4⟩` from `hloc _ lam hu w' hw'`.

Establish `hv : Val hb w' (wchar e t * ψ ⟨_, hb C⟩)` using `⟨C, ψ, z, t, h3, h4, rfl⟩`. Generalize the expression as in `wchar e t * ψ ⟨_, hb C⟩ = u at hv`. Take `⟨n, a, ha⟩` from `IsLocalization.Away.surj g u`. Establish `hmem : g ^ (n + 1) ∈ I`. Use `⟨g * a, fun L _ _ χ w v h5 h6 => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hχ : χ g = 0`. Simplify using `[hχ]`. Set `mu : Localization.Away g →ₐ[c.F] L` to `IsLocalization.liftAlgHom (M := Submonoid.powers g) (f := χ) (by`. Introduce and unpack `⟨_, k, rfl⟩`. Simplify using `using (IsUnit.mk0 _ hχ).pow k)`.

Establish `hmu' : ∀ x, mu (algebraMap S _ x) = χ x` using `fun x => by`. Simplify using `[mu]`. Establish `hmu : mu.comp lam = χ` using `AlgHom.ext hmu'`. Establish `h7 : FrMap mu w' w` using `frMap_cancel _ _ _ lam mu y w' w hw' (by rw [hmu]; exact h5)`. Establish `h8` using `val_unique hb hl h6 (val_map hb hl mu h7 hv)`.

Establish `h9` using `congrArg mu ha`. Rewrite `h9` using `[map_mul, map_pow, hmu', hmu']`. Rewrite using `[h8, map_mul, map_pow, ← h9]`. Expand and normalize the polynomial expressions, which then agree. Establish `hgP : g ∈ P` using `this.mem_of_pow_mem _ (hIP hmem)`.

Apply `hg` to reduce the goal to its premises. Use `show algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P g) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 hgP, map_zero]`.
-/
theorem exists_rep (hl : EvLaws Xo c) (hA : Atlas h) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ s, Rep hb y 1 s := by
  let I : Ideal S :=
    { carrier := {g | ∃ s, Rep hb y g s}
      zero_mem' := ⟨0, fun L _ _ χ w v _ _ => by simp⟩
      add_mem' := by
        rintro g g' ⟨s, hs⟩ ⟨s', hs'⟩
        exact ⟨s + s', fun L _ _ χ w v h1 h2 => by
          rw [map_add, map_add, add_mul, hs L χ w v h1 h2, hs' L χ w v h1 h2]⟩
      smul_mem' := by
        rintro r g ⟨s, hs⟩
        exact ⟨r * s, fun L _ _ χ w v h1 h2 => by
          rw [smul_eq_mul, map_mul, map_mul, mul_assoc, hs L χ w v h1 h2]⟩ }
  by_contra hne
  have hI : I ≠ ⊤ := fun hI => hne ((Ideal.eq_top_iff_one I).1 hI)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  have := hP.isPrime
  let χ₀ : S →ₐ[c.F] FractionRing (S ⧸ P) :=
    (IsScalarTower.toAlgHom c.F (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mkₐ c.F P)
  obtain ⟨w₀, hw₀⟩ := hl.bc _ _ χ₀ y
  obtain ⟨C, ψ₀, z₀, t₀, h1, h2⟩ := hA _ w₀
  obtain ⟨g, hg, hloc⟩ := C.opn S _ χ₀ y w₀ hw₀ ⟨ψ₀, z₀, t₀, h1, h2⟩
  let lam : S →ₐ[c.F] Localization.Away g := IsScalarTower.toAlgHom c.F S _
  have hu : IsUnit (lam g) := IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨w', hw'⟩ := hl.bc _ _ lam y
  obtain ⟨ψ, z, t, h3, h4⟩ := hloc _ lam hu w' hw'
  have hv : Val hb w' (wchar e t * ψ ⟨_, hb C⟩) := ⟨C, ψ, z, t, h3, h4, rfl⟩
  generalize wchar e t * ψ ⟨_, hb C⟩ = u at hv
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g u
  have hmem : g ^ (n + 1) ∈ I := by
    refine ⟨g * a, fun L _ _ χ w v h5 h6 => ?_⟩
    by_cases hχ : χ g = 0
    · simp [hχ]
    · let mu : Localization.Away g →ₐ[c.F] L :=
        IsLocalization.liftAlgHom (M := Submonoid.powers g) (f := χ) (by
          rintro ⟨_, k, rfl⟩
          simpa using (IsUnit.mk0 _ hχ).pow k)
      have hmu' : ∀ x, mu (algebraMap S _ x) = χ x := fun x => by
        simp [mu]
      have hmu : mu.comp lam = χ := AlgHom.ext hmu'
      have h7 : FrMap mu w' w := frMap_cancel _ _ _ lam mu y w' w hw' (by rw [hmu]; exact h5)
      have h8 := val_unique hb hl h6 (val_map hb hl mu h7 hv)
      have h9 := congrArg mu ha
      rw [map_mul, map_pow, hmu', hmu'] at h9
      rw [h8, map_mul, map_pow, ← h9]
      ring
  have hgP : g ∈ P := this.mem_of_pow_mem _ (hIP hmem)
  apply hg
  show algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P g) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hgP, map_zero]

end Val

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c hl h hA a n b hb`. Establish `hred : ∀ p : TRing c.F, IsReduced p.R` using `fun p => (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad`. Use `choose g hg using fun (p : TRing c.F) (y : FrPt Xo c p.R) => exists_rep hb hl hA y`. Establish `hg' : ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (L : Type) [Field L] [Algebra c.F L] (χ : p.R →ₐ[c.F] L) (w : FrPt Xo c L) (v : L), FrMap χ y w → Val hb w v → χ (g p y) = v`. Introduce `p y L _ _ χ w v h1 h2`.

Rewrite using `[← hg p y L χ w v h1 h2, map_one, one_mul]`. Use `⟨g, ⟨fun p q φ y z hz => ?_, fun p t y y' hy => ?_⟩, fun Z => ?_⟩` and prove the remaining obligations. Use `hred q` as an intermediate fact. Use `eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_` and prove the remaining obligations. Take `⟨w, hw⟩` from `hl.bc _ _ χ z`.

Take `⟨v, hv⟩` from `val_ex hb hA w`. Rewrite using `[hg' q z L χ w v hw hv]`. Conclude with `(hg' p y L (χ.comp φ) w v (frMap_trans _ _ _ φ χ y z w hz hw) hv).symm`. Use `hred p` as an intermediate fact. Use `eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_` and prove the remaining obligations.

Take `⟨w, hw⟩` from `hl.bc _ _ χ y`. Take `⟨w', hw'⟩` from `hl.bc _ _ χ y'`. Take `⟨v, hv⟩` from `val_ex hb hA w`. Establish `hv'` using `val_bor hb (frBorBC _ _ χ t y y' w w' hy hw hw') hv`. Rewrite using `[hg' p y' L χ w' _ hw' hv', map_mul, hg' p y L χ w v hw hv, wchar_map]`.

Establish `hh` using `hl.test _ (genFr h Z)`. Unfold `evC evR evalAt`. Rewrite using `[dif_pos hh]`. Conclude with `hg' _ _ _ _ _ _ hh.choose_spec.choose_spec.choose_spec (val_gen hb hA Z)`.
-/
theorem exists_sec_of_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, wchar (ex Dw a n) C.t * b C.Z ∈ C.R) → ∃ g ∈ sec Xo c a n, ∀ Z, evC h Z g = b Z := by
  intro E _ _ _ H Dw l Xo c hl h hA a n b hb
  have hred : ∀ p : TRing c.F, IsReduced p.R := fun p => (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  choose g hg using fun (p : TRing c.F) (y : FrPt Xo c p.R) => exists_rep hb hl hA y
  have hg' : ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (L : Type) [Field L] [Algebra c.F L] (χ : p.R →ₐ[c.F] L)
      (w : FrPt Xo c L) (v : L), FrMap χ y w → Val hb w v → χ (g p y) = v := by
    intro p y L _ _ χ w v h1 h2
    rw [← hg p y L χ w v h1 h2, map_one, one_mul]
  refine ⟨g, ⟨fun p q φ y z hz => ?_, fun p t y y' hy => ?_⟩, fun Z => ?_⟩
  · have := hred q
    refine eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_
    obtain ⟨w, hw⟩ := hl.bc _ _ χ z
    obtain ⟨v, hv⟩ := val_ex hb hA w
    rw [hg' q z L χ w v hw hv]
    exact (hg' p y L (χ.comp φ) w v (frMap_trans _ _ _ φ χ y z w hz hw) hv).symm
  · have := hred p
    refine eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_
    obtain ⟨w, hw⟩ := hl.bc _ _ χ y
    obtain ⟨w', hw'⟩ := hl.bc _ _ χ y'
    obtain ⟨v, hv⟩ := val_ex hb hA w
    have hv' := val_bor hb (frBorBC _ _ χ t y y' w w' hy hw hw') hv
    rw [hg' p y' L χ w' _ hw' hv', map_mul, hg' p y L χ w v hw hv, wchar_map]
  · have hh := hl.test _ (genFr h Z)
    unfold evC evR evalAt
    rw [dif_pos hh]
    exact hg' _ _ _ _ _ _ hh.choose_spec.choose_spec.choose_spec (val_gen hb hA Z)

end GlobalTheory.Reg.SecGlue
