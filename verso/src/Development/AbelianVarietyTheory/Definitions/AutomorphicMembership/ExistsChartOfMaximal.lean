import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedImmersionBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsLogGrNormSubLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitSectionOfLocalValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsScfEmbeddingDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointOfIntegralPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DividesOfNormBoundedPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open Formalism.MainNotions.DIV.Cons (intO SCF)
open GlobalTheory.FieldPtGlue GlobalTheory.ShFam.Pad.Pull

namespace GlobalTheory.ShFam.Pad

namespace GenId

/- English proof (translation)
Establish `hc` using `irreducibleComponent_mem_irreducibleComponents z`. Establish `hg` using `hc.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hc)`. Use `⟨_, hg.specializes mem_irreducibleComponent, fun y hy => (hy.antisymm (hg.specializes ?_)).eq⟩` and prove the remaining obligations. Use `hc.2 isIrreducible_singleton.closure ?_ (subset_closure rfl)` and prove the remaining obligations. Conclude with `hg.def.ge.trans (closure_minimal (Set.singleton_subset_iff.2 hy.mem_closure) isClosed_closure)`.
-/
theorem exists_maximal {X : Scheme.{0}} (z : X) : ∃ η : X, η ⤳ z ∧ ∀ y : X, y ⤳ η → y = η := by
  have hc := irreducibleComponent_mem_irreducibleComponents z
  have hg := hc.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hc)
  refine ⟨_, hg.specializes mem_irreducibleComponent, fun y hy => (hy.antisymm (hg.specializes ?_)).eq⟩
  refine hc.2 isIrreducible_singleton.closure ?_ (subset_closure rfl)
  exact hg.def.ge.trans (closure_minimal (Set.singleton_subset_iff.2 hy.mem_closure) isClosed_closure)

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun z hz => ?_)` and prove the remaining obligations. Take `⟨η, hη, hm⟩` from `exists_maximal z`. Establish `hb : η ∈ X.basicOpen (a - b)` using `hη.mem_open (X.basicOpen _).isOpen hz`. Take `⟨k, _, w, rfl, e⟩` from `h η (X.basicOpen_le _ hb) hm`.

Establish `hU : ⊤ ≤ w ⁻¹ᵁ U` using `(le_preimage_iff U).2 (X.basicOpen_le _ hb)`. Conclude with `absurd (by rw [valF_sub hU, e, sub_self]) ((valF_ne_zero_iff hU (a - b)).2 ((le_preimage_iff _).2 hb))`.
-/
theorem ext_maximal {X : Scheme.{0}} [IsReduced X] {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ η ∈ U, (∀ y : X, y ⤳ η → y = η) → ∃ (k : Type) (_ : Field k) (w : Sp k ⟶ X),
      w (closedPoint k) = η ∧ valF w U a = valF w U b) : a = b := by
  rw [← sub_eq_zero]
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun z hz => ?_)
  obtain ⟨η, hη, hm⟩ := exists_maximal z
  have hb : η ∈ X.basicOpen (a - b) := hη.mem_open (X.basicOpen _).isOpen hz
  obtain ⟨k, _, w, rfl, e⟩ := h η (X.basicOpen_le _ hb) hm
  have hU : ⊤ ≤ w ⁻¹ᵁ U := (le_preimage_iff U).2 (X.basicOpen_le _ hb)
  exact absurd (by rw [valF_sub hU, e, sub_self]) ((valF_ne_zero_iff hU (a - b)).2 ((le_preimage_iff _).2 hb))

/- English proof (translation)
Take `⟨V, hV, hz, hle⟩` from `exists_isAffineOpen_mem_and_subset (X := X) ((le_preimage_iff U).1 h)`. Take `⟨χ, rfl⟩` from `exists_fromSpec hV w ((le_preimage_iff V).2 hz)`. Rewrite using `[← Category.assoc, ModelRelProbe.spMap_comp, ← valF_restrict hle (le_of_fromSpec hV rfl), ← valF_restrict hle (le_of_fromSpec hV rfl), valF_fromSpec, valF_fromSpec]`. Both sides reduce to the same expression.
-/
theorem valF_map {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X : Scheme.{0}} {w : Sp F ⟶ X} {U : X.Opens}
    (h : ⊤ ≤ w ⁻¹ᵁ U) (a : Γ(X, U)) : valF (spMap f ≫ w) U a = f (valF w U a) := by
  obtain ⟨V, hV, hz, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) ((le_preimage_iff U).1 h)
  obtain ⟨χ, rfl⟩ := exists_fromSpec hV w ((le_preimage_iff V).2 hz)
  rw [← Category.assoc, ModelRelProbe.spMap_comp, ← valF_restrict hle (le_of_fromSpec hV rfl),
    ← valF_restrict hle (le_of_fromSpec hV rfl), valF_fromSpec, valF_fromSpec]
  rfl

/- English proof (translation)
Rewrite using `[valF, dif_pos h, map_natCast, map_natCast]`.
-/
theorem valF_natCast {F : Type} [Field F] {X : Scheme.{0}} {w : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ w ⁻¹ᵁ U) (n : ℕ) :
    valF w U (n : Γ(X, U)) = n := by
  rw [valF, dif_pos h, map_natCast, map_natCast]

/- English proof (translation)
Rewrite using `[valF, dif_pos h, map_one, map_one]`.
-/
theorem valF_one {F : Type} [Field F] {X : Scheme.{0}} {w : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ w ⁻¹ᵁ U) :
    valF w U 1 = 1 := by
  rw [valF, dif_pos h, map_one, map_one]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `y ⤳ X.fromSpecStalk x (spMap f (closedPoint K)) at hy`. Express the relevant statement in the definitionally equal form `y = X.fromSpecStalk x (spMap f (closedPoint K))`. Take `⟨q, rfl⟩` from `(X.range_fromSpecStalk (x := x)).ge (hy.trans ((X.range_fromSpecStalk (x := x)).le ⟨_, rfl⟩))`. Establish `h : spMap f (closedPoint K) ⤳ q` using `(PrimeSpectrum.le_iff_specializes _ q).1 fun r hr => by`. Establish `: f r ∈ maximalIdeal K` using `hr`.

Rewrite `this` using `[maximalIdeal_eq_bot, Ideal.mem_bot, map_eq_zero_iff _ hf]`. Conclude with `this ▸ q.asIdeal.zero_mem`. Conclude with `(hy.antisymm (h.map (X.fromSpecStalk x).continuous)).eq`.
-/
theorem maximal_of_stalk {X : Scheme.{0}} {x : X} {K : Type} [Field K] {f : X.presheaf.stalk x →+* K}
    (hf : Function.Injective f) (y : X) (hy : y ⤳ (spMap f ≫ X.fromSpecStalk x) (closedPoint K)) :
    y = (spMap f ≫ X.fromSpecStalk x) (closedPoint K) := by
  change y ⤳ X.fromSpecStalk x (spMap f (closedPoint K)) at hy
  change y = X.fromSpecStalk x (spMap f (closedPoint K))
  obtain ⟨q, rfl⟩ := (X.range_fromSpecStalk (x := x)).ge (hy.trans ((X.range_fromSpecStalk (x := x)).le ⟨_, rfl⟩))
  have h : spMap f (closedPoint K) ⤳ q := (PrimeSpectrum.le_iff_specializes _ q).1 fun r hr => by
    have : f r ∈ maximalIdeal K := hr
    rw [maximalIdeal_eq_bot, Ideal.mem_bot, map_eq_zero_iff _ hf] at this
    exact this ▸ q.asIdeal.zero_mem
  exact (hy.antisymm (h.map (X.fromSpecStalk x).continuous)).eq

/- English proof (translation)
Use `IsIntegrallyClosed.algebraMap_eq_of_integral (by_contra fun hn => ?_)` and prove the remaining obligations. Establish `: Algebra.EssFiniteType R K` using `.of_isLocalization K (nonZeroDivisors R)`. Take `⟨V, hV, hd, hκ⟩` from `exists_discreteValuationSubring_dominating_notMem hn`. Take `⟨h₁, h₂⟩` from `(localSubring_range_le_valuationSubring_iff _ V).1 hd`. Establish `hpV : (p : V) ∈ maximalIdeal V`.

Rewrite using `[← ValuationSubring.coe_mem_nonunits_iff]`. Simplify using `using h₂ _ hR`. Take `⟨C, φ, φi, hφ⟩` from `exists_scf_embedding_dvd p V hp hpV ((Cardinal.mk_subtype_le _).trans ((IsLocalization.cardinalMk_le (nonZeroDivisors R)).trans hc))`. Set `θ : K →+* ↥C.S` to `IsFractionRing.lift (A := V) (g := (intO ↥C.S).subtype.comp φ) ((intO ↥C.S).subtype_injective.comp φi)`. Establish `hθ (v : V) : θ v = φ v` using `IsFractionRing.lift_algebraMap _ v`.

Establish `h₃` using `h C (φ.comp ((algebraMap R K).codRestrict V h₁)) θ (RingHom.ext fun r => hθ ⟨_, h₁ r⟩)`. Establish `h0 : κ ≠ 0` using `fun e => hκ (e ▸ V.zero_mem)`. Establish `hi : κ⁻¹ ∈ V` using `(V.mem_or_inv_mem κ).resolve_left hκ`. Take `⟨c, hc⟩` from `hφ 1 ⟨_, hi⟩ (by`. Rewrite using `[← hθ, ← hθ]`.

Simplify using `only [OneMemClass.coe_one, map_one, norm_one, map_inv₀, norm_inv]`. Conclude with `(one_le_inv₀ (norm_pos_iff.2 ((map_ne_zero θ).2 h0))).2 h₃)`. Establish `: κ⁻¹ * c = 1` using `(congrArg Subtype.val hc).symm`. Conclude with `hκ ((inv_mul_eq_one₀ h0).1 this ▸ c.2)`.
-/
theorem mem_range_of_norm_le {p : ℕ} (hp : p.Prime) {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (hR : (p : R) ∈ maximalIdeal R) (hc : Cardinal.mk R ≤ Cardinal.continuum) {κ : K}
    (h : ∀ (C : SCF p) (ψ : R →+* ↥(intO ↥C.S)) (θ : K →+* ↥C.S),
      θ.comp (algebraMap R K) = (intO ↥C.S).subtype.comp ψ → ‖θ κ‖ ≤ 1) : ∃ r, algebraMap R K r = κ := by
  refine IsIntegrallyClosed.algebraMap_eq_of_integral (by_contra fun hn => ?_)
  have : Algebra.EssFiniteType R K := .of_isLocalization K (nonZeroDivisors R)
  obtain ⟨V, hV, hd, hκ⟩ := exists_discreteValuationSubring_dominating_notMem hn
  obtain ⟨h₁, h₂⟩ := (localSubring_range_le_valuationSubring_iff _ V).1 hd
  have hpV : (p : V) ∈ maximalIdeal V := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    simpa using h₂ _ hR
  obtain ⟨C, φ, φi, hφ⟩ := exists_scf_embedding_dvd p V hp hpV
    ((Cardinal.mk_subtype_le _).trans ((IsLocalization.cardinalMk_le (nonZeroDivisors R)).trans hc))
  let θ : K →+* ↥C.S := IsFractionRing.lift (A := V) (g := (intO ↥C.S).subtype.comp φ)
    ((intO ↥C.S).subtype_injective.comp φi)
  have hθ (v : V) : θ v = φ v := IsFractionRing.lift_algebraMap _ v
  have h₃ := h C (φ.comp ((algebraMap R K).codRestrict V h₁)) θ (RingHom.ext fun r => hθ ⟨_, h₁ r⟩)
  have h0 : κ ≠ 0 := fun e => hκ (e ▸ V.zero_mem)
  have hi : κ⁻¹ ∈ V := (V.mem_or_inv_mem κ).resolve_left hκ
  obtain ⟨c, hc⟩ := hφ 1 ⟨_, hi⟩ (by
    rw [← hθ, ← hθ]
    simp only [OneMemClass.coe_one, map_one, norm_one, map_inv₀, norm_inv]
    exact (one_le_inv₀ (norm_pos_iff.2 ((map_ne_zero θ).2 h0))).2 h₃)
  have : κ⁻¹ * c = 1 := (congrArg Subtype.val hc).symm
  exact hκ ((inv_mul_eq_one₀ h0).1 this ▸ c.2)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) {Z : LocM.Mdl Y i₀}

include hp hW

/- English proof (translation)
The claim follows from `Set.mem_iUnion.1 (Z.cover.ge (HTLine.Dvd.mem_opn hp hW Z h))`.
-/
theorem exists_chart_of_maximal {η : Z.X} (h : ∀ y : Z.X, y ⤳ η → y = η) : ∃ a, η ∈ (Z.U a).1 :=
  Set.mem_iUnion.1 (Z.cover.ge (HTLine.Dvd.mem_opn hp hW Z h))

/- English proof (translation)
Use `isReduced_model Z` as an intermediate fact. Use `ext_maximal fun η hη hm => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_chart_of_maximal hp hW hm`. Conclude with `⟨_, _, resPt Z.X η, Scheme.fromSpecResidueField_apply η _, h _ _ a ((resPt_le_iff _ _ _).2 ha) ((resPt_le_iff _ _ _).2 hη)⟩`.
-/
theorem ext_chart {U : Z.X.Opens} {s t : Γ(Z.X, U)} (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X) a,
    ⊤ ≤ w ⁻¹ᵁ (Z.U a).1 → ⊤ ≤ w ⁻¹ᵁ U → valF w U s = valF w U t) : s = t := by
  have := isReduced_model Z
  refine ext_maximal fun η hη hm => ?_
  obtain ⟨a, ha⟩ := exists_chart_of_maximal hp hW hm
  exact ⟨_, _, resPt Z.X η, Scheme.fromSpecResidueField_apply η _,
    h _ _ a ((resPt_le_iff _ _ _).2 ha) ((resPt_le_iff _ _ _).2 hη)⟩

/- English proof (translation)
Use `isProper_str (Z.i.c.V W) Z.n` as an intermediate fact. Establish `: IsProper Z.s` using `inferInstanceAs (IsProper (_ ≫ _))`. Establish `hc : IsClosed (Z.s '' closure {z})` using `Z.s.isClosedMap _ isClosed_closure`. Take `⟨x, hx, e⟩ : closedPoint (Z.i.c.V W) ∈ Z.s '' closure {z}` from `(IsLocalRing.specializes_closedPoint (Z.s z)).mem_closed hc ⟨z, subset_closure rfl, rfl⟩`. Use `⟨x, specializes_iff_mem_closure.2 hx, (natCast_eq_zero_iff hp hW Z x).2 fun hq => ?_⟩` and prove the remaining obligations.

Conclude with `(mem_gen_iff_inQ hp hW (Z := Z)).2 hq e`.
-/
theorem exists_special (z : Z.X) : ∃ x : Z.X, z ⤳ x ∧ (p : Z.X.residueField x) = 0 := by
  have := isProper_str (Z.i.c.V W) Z.n
  have : IsProper Z.s := inferInstanceAs (IsProper (_ ≫ _))
  have hc : IsClosed (Z.s '' closure {z}) := Z.s.isClosedMap _ isClosed_closure
  obtain ⟨x, hx, e⟩ : closedPoint (Z.i.c.V W) ∈ Z.s '' closure {z} :=
    (IsLocalRing.specializes_closedPoint (Z.s z)).mem_closed hc ⟨z, subset_closure rfl, rfl⟩
  refine ⟨x, specializes_iff_mem_closure.2 hx, (natCast_eq_zero_iff hp hW Z x).2 fun hq => ?_⟩
  exact (mem_gen_iff_inQ hp hW (Z := Z)).2 hq e

/- English proof (translation)
Use `isDiscreteValuationRing_V Z.i.c hp hW` as an intermediate fact. Establish `hN : GlobalTheory.IsNormalScheme Z.X` using `Z.normal`. Use `isProper_str (Z.i.c.V W) Z.n` as an intermediate fact. Establish `: IsProper Z.s` using `inferInstanceAs (IsProper (_ ≫ _))`. Establish `: IsLocallyNoetherian Z.X` using `LocallyOfFiniteType.isLocallyNoetherian Z.s`.

Set `R : Type` to `Z.X.presheaf.stalk x`. Take `⟨_, _⟩ : IsDomain R ∧ IsIntegrallyClosed R` from `(GlobalTheory.isNormalScheme_iff _).1 hN x`. Set `K` to `FractionRing R`. Set `ι : Sp R ⟶ Z.X` to `Z.X.fromSpecStalk x`. Establish `hι (q : Sp R) : ι q ⤳ x` using `(Z.X.range_fromSpecStalk (x := x)).le ⟨q, rfl⟩`.

Set `w₀ : Sp K ⟶ Z.X` to `spMap (algebraMap R K) ≫ ι`. Establish `hη : w₀ (closedPoint K) ⤳ x` using `hι _`. Establish `hm : ∀ y : Z.X, y ⤳ w₀ (closedPoint K) → y = w₀ (closedPoint K)` using `maximal_of_stalk (IsFractionRing.injective R K)`. Take `⟨a₀, ha₀⟩` from `exists_chart_of_maximal hp hW hm`. Establish `w₀a` using `(le_preimage_iff _).2 ha₀`.

Establish `w₀U : ⊤ ≤ w₀ ⁻¹ᵁ U` using `(le_preimage_iff _).2 (hη.mem_open U.isOpen hx)`. Take `⟨φ₀, -⟩` from `exists_fromSpec (Z.U a₀).2 w₀ w₀a`. Establish `: CharZero K` using `(φ₀.comp (Z.alg a₀)).charZero_iff (RingHom.injective _) |>.1 inferInstance`. Establish `hc : Cardinal.mk R ≤ Cardinal.continuum`. Take `⟨V, hV, hxV, -⟩` from `exists_isAffineOpen_mem_and_subset (X := Z.X) hx`.

Take `⟨σ, -, hσ⟩` from `HTLine.Dvd.exists_base hp hW Z hV`. Use `letI := Z.X.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V)`. Use `hV.isLocalization_stalk ⟨x, hxV⟩` as an intermediate fact. Conclude with `(IsLocalization.cardinalMk_le (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl).trans (HTLine.Dvd.mk_le_of_finiteType σ hσ ((Cardinal.mk_subtype_le _).trans ((Cardinal.mk_subtype_le _).trans Cardinal.mk_complex.le)))`. Take `⟨ρ, hρ⟩` from `mem_range_of_norm_le (R := R) (K := K) hp ((residue_eq_zero_iff _).1 ((map_natCast _ p).trans hpx)) hc (κ := valF w₀ _ (f a₀)) fun C ψ θ e => by`.

Establish `g : spMap (intO ↥C.S).subtype ≫ spMap ψ ≫ ι = spMap θ ≫ w₀`. Rewrite using `[← Category.assoc, ← Category.assoc, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp, e]`. Take `⟨Q, hQ⟩` from `ModelPt.exists_ptC E H Dw Xo p W Y i₀ hp hW Z C (spMap ψ ≫ ι) (by`. Introduce and unpack `_ ⟨q, rfl⟩`. Rewrite using `[g, ← Z.cover]`.

Conclude with `Set.mem_iUnion.2 ⟨a₀, w₀a (Set.mem_univ (spMap θ q))⟩)`. Set `y : Z.Pt` to `⟨C, Q, spMap ψ ≫ ι, hQ⟩`. Establish `hy : y.gen = spMap θ ≫ w₀` using `g`. Use `hb y a₀ (hy ▸ fun q _ => w₀a (Set.mem_univ (spMap θ q))) fun q _ => (hι (spMap ψ q)).mem_open U.isOpen hx` as an intermediate fact. Rewrite `this` using `[hy, valF_map θ (U := (Z.U a₀).1 ⊓ U) fun q hq => ⟨w₀a hq, w₀U hq⟩]`. Then use the resulting hypothesis.

Take `⟨V₁, hx₁, t₁, rfl⟩` from `Z.X.presheaf.germ_exist ρ`. Establish `hC` using `irreducibleComponent_mem_irreducibleComponents x`. Establish `hg` using `hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)`. Take `⟨V, hV, hxV, hle⟩` from `exists_isAffineOpen_mem_and_subset (X := Z.X) (x := x) (U := V₁ ⊓ (U ⊓ IsNormalScheme.component ⟨_, hC⟩)) ⟨hx₁, hx, mem_irreducibleComponent⟩`. Establish `l₁ : V ≤ V₁` using `fun q hq => (hle hq).1`.

Establish `l₂ : V ≤ U` using `fun q hq => (hle hq).2.1`. Establish `hηV : w₀ (closedPoint K) ∈ V` using `hη.mem_open V.isOpen hxV`. Establish `v : valF w₀ V (resG Z.X l₁ t₁) = valF w₀ _ (f a₀)`. Establish `e : w₀ = spMap ((algebraMap R K).comp (Z.X.presheaf.germ V x hxV).hom) ≫ hV.fromSpec`. Rewrite using `[← ModelRelProbe.spMap_comp, Category.assoc]`.

Conclude with `congrArg (spMap (algebraMap R K) ≫ ·) (hV.fromSpecStalk_eq_fromSpecStalk hxV).symm`. Rewrite using `[← hρ, e, valF_fromSpec]`. Conclude with `congrArg (algebraMap R K) (Z.X.presheaf.germ_res_apply (homOfLE l₁) x hxV t₁)`. Use `⟨V, resG Z.X l₁ t₁, hxV, l₂, fun k _ w a ha hw => ?_⟩` and prove the remaining obligations. Establish `e : resG Z.X (inf_le_right : (Z.U a).1 ⊓ V ≤ V) (resG Z.X l₁ t₁) = resG Z.X (inf_le_inf_left _ l₂) (f a)`.

Use `ext_maximal fun η hη' hm' => ?_` and prove the remaining obligations. Take `rfl : η = w₀ (closedPoint K)` from `(hm' _ (hg.specializes (hle hη'.2).2.2)).symm.trans (hm _ (hg.specializes (hle hηV).2.2))`. Establish `h'` using `(le_preimage_iff (x := w₀) _).2 hη'`. Use `⟨K, inferInstance, w₀, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[valF_restrict _ h', valF_restrict _ h', v]`.

Conclude with `hf K w₀ a₀ a w₀a (fun q hq => (h' hq).1) w₀U`. Establish `h' : ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ V)` using `fun q hq => ⟨ha hq, hw hq⟩`. Rewrite using `[← valF_restrict inf_le_right h', ← valF_restrict (inf_le_inf_left _ l₂) h']`. Conclude with `congrArg _ e`.
-/
theorem exists_extension {U : Z.X.Opens} (f : ∀ a, Γ(Z.X, (Z.U a).1 ⊓ U))
    (hf : ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X) a a', ⊤ ≤ w ⁻¹ᵁ (Z.U a).1 → ⊤ ≤ w ⁻¹ᵁ (Z.U a').1 → ⊤ ≤ w ⁻¹ᵁ U →
      valF w _ (f a) = valF w _ (f a'))
    (hb : ∀ (y : Z.Pt) a, ⊤ ≤ y.gen ⁻¹ᵁ (Z.U a).1 → ⊤ ≤ y.z ⁻¹ᵁ U → ‖valF y.gen _ (f a)‖ ≤ 1)
    {x : Z.X} (hx : x ∈ U) (hpx : (p : Z.X.residueField x) = 0) :
    ∃ (V : Z.X.Opens) (t : Γ(Z.X, V)), x ∈ V ∧ V ≤ U ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X) a,
      ⊤ ≤ w ⁻¹ᵁ (Z.U a).1 → ⊤ ≤ w ⁻¹ᵁ V → valF w V t = valF w _ (f a) := by
  have := isDiscreteValuationRing_V Z.i.c hp hW
  have hN : GlobalTheory.IsNormalScheme Z.X := Z.normal
  have := isProper_str (Z.i.c.V W) Z.n
  have : IsProper Z.s := inferInstanceAs (IsProper (_ ≫ _))
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  let R : Type := Z.X.presheaf.stalk x
  obtain ⟨_, _⟩ : IsDomain R ∧ IsIntegrallyClosed R := (GlobalTheory.isNormalScheme_iff _).1 hN x
  let K := FractionRing R
  let ι : Sp R ⟶ Z.X := Z.X.fromSpecStalk x
  have hι (q : Sp R) : ι q ⤳ x := (Z.X.range_fromSpecStalk (x := x)).le ⟨q, rfl⟩
  let w₀ : Sp K ⟶ Z.X := spMap (algebraMap R K) ≫ ι
  have hη : w₀ (closedPoint K) ⤳ x := hι _
  have hm : ∀ y : Z.X, y ⤳ w₀ (closedPoint K) → y = w₀ (closedPoint K) :=
    maximal_of_stalk (IsFractionRing.injective R K)
  obtain ⟨a₀, ha₀⟩ := exists_chart_of_maximal hp hW hm
  have w₀a := (le_preimage_iff _).2 ha₀
  have w₀U : ⊤ ≤ w₀ ⁻¹ᵁ U := (le_preimage_iff _).2 (hη.mem_open U.isOpen hx)
  obtain ⟨φ₀, -⟩ := exists_fromSpec (Z.U a₀).2 w₀ w₀a
  have : CharZero K := (φ₀.comp (Z.alg a₀)).charZero_iff (RingHom.injective _) |>.1 inferInstance
  have hc : Cardinal.mk R ≤ Cardinal.continuum := by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z.X) hx
    obtain ⟨σ, -, hσ⟩ := HTLine.Dvd.exists_base hp hW Z hV
    letI := Z.X.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V)
    have := hV.isLocalization_stalk ⟨x, hxV⟩
    exact (IsLocalization.cardinalMk_le (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl).trans
      (HTLine.Dvd.mk_le_of_finiteType σ hσ
        ((Cardinal.mk_subtype_le _).trans ((Cardinal.mk_subtype_le _).trans Cardinal.mk_complex.le)))
  obtain ⟨ρ, hρ⟩ := mem_range_of_norm_le (R := R) (K := K) hp
    ((residue_eq_zero_iff _).1 ((map_natCast _ p).trans hpx)) hc (κ := valF w₀ _ (f a₀)) fun C ψ θ e => by
      have g : spMap (intO ↥C.S).subtype ≫ spMap ψ ≫ ι = spMap θ ≫ w₀ := by
        rw [← Category.assoc, ← Category.assoc, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp, e]
      obtain ⟨Q, hQ⟩ := ModelPt.exists_ptC E H Dw Xo p W Y i₀ hp hW Z C (spMap ψ ≫ ι) (by
        rintro _ ⟨q, rfl⟩
        rw [g, ← Z.cover]
        exact Set.mem_iUnion.2 ⟨a₀, w₀a (Set.mem_univ (spMap θ q))⟩)
      let y : Z.Pt := ⟨C, Q, spMap ψ ≫ ι, hQ⟩
      have hy : y.gen = spMap θ ≫ w₀ := g
      have := hb y a₀ (hy ▸ fun q _ => w₀a (Set.mem_univ (spMap θ q))) fun q _ => (hι (spMap ψ q)).mem_open U.isOpen hx
      rwa [hy, valF_map θ (U := (Z.U a₀).1 ⊓ U) fun q hq => ⟨w₀a hq, w₀U hq⟩] at this
  obtain ⟨V₁, hx₁, t₁, rfl⟩ := Z.X.presheaf.germ_exist ρ
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Z.X) (x := x)
    (U := V₁ ⊓ (U ⊓ IsNormalScheme.component ⟨_, hC⟩)) ⟨hx₁, hx, mem_irreducibleComponent⟩
  have l₁ : V ≤ V₁ := fun q hq => (hle hq).1
  have l₂ : V ≤ U := fun q hq => (hle hq).2.1
  have hηV : w₀ (closedPoint K) ∈ V := hη.mem_open V.isOpen hxV
  have v : valF w₀ V (resG Z.X l₁ t₁) = valF w₀ _ (f a₀) := by
    have e : w₀ = spMap ((algebraMap R K).comp (Z.X.presheaf.germ V x hxV).hom) ≫ hV.fromSpec := by
      rw [← ModelRelProbe.spMap_comp, Category.assoc]
      exact congrArg (spMap (algebraMap R K) ≫ ·) (hV.fromSpecStalk_eq_fromSpecStalk hxV).symm
    rw [← hρ, e, valF_fromSpec]
    exact congrArg (algebraMap R K) (Z.X.presheaf.germ_res_apply (homOfLE l₁) x hxV t₁)
  refine ⟨V, resG Z.X l₁ t₁, hxV, l₂, fun k _ w a ha hw => ?_⟩
  have e : resG Z.X (inf_le_right : (Z.U a).1 ⊓ V ≤ V) (resG Z.X l₁ t₁) = resG Z.X (inf_le_inf_left _ l₂) (f a) := by
    refine ext_maximal fun η hη' hm' => ?_
    obtain rfl : η = w₀ (closedPoint K) :=
      (hm' _ (hg.specializes (hle hη'.2).2.2)).symm.trans (hm _ (hg.specializes (hle hηV).2.2))
    have h' := (le_preimage_iff (x := w₀) _).2 hη'
    refine ⟨K, inferInstance, w₀, rfl, ?_⟩
    rw [valF_restrict _ h', valF_restrict _ h', v]
    exact hf K w₀ a₀ a w₀a (fun q hq => (h' hq).1) w₀U
  have h' : ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ V) := fun q hq => ⟨ha hq, hw hq⟩
  rw [← valF_restrict inf_le_right h', ← valF_restrict (inf_le_inf_left _ l₂) h']
  exact congrArg _ e

variable {b b' : Bool} {st st' : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw}

omit hp hW in

/- English proof (translation)
The claim follows from `left_ne_zero_of_mul_eq_one (valF_mul_inv (U := (Z.U a).1 ⊓ M.L.U i) (fun _ hq => ⟨ha hq, hi hq⟩) _)`.
-/
theorem val_ne_zero (M : LineModel Z b st x) {k : Type} [Field k] {w : Sp k ⟶ Z.X} {a : Fin Z.m} {i : Fin M.L.n}
    (ha : ⊤ ≤ w ⁻¹ᵁ (Z.U a).1) (hi : ⊤ ≤ w ⁻¹ᵁ M.L.U i) : valF w _ (M.r a i).val ≠ 0 :=
  left_ne_zero_of_mul_eq_one (valF_mul_inv (U := (Z.U a).1 ⊓ M.L.U i) (fun _ hq => ⟨ha hq, hi hq⟩) _)

omit hp hW in

/- English proof (translation)
Take `⟨φ, h⟩` from `exists_fromSpec (Z.U a).2 w ha`. Take `⟨φ', h'⟩` from `exists_fromSpec (Z.U a').2 w ha'`. Use `replace h : spMap φ ≫ Z.chart a = w := h`. Use `replace h' : spMap φ' ≫ Z.chart a' = w := h'`. Take `⟨d, d1, d2⟩` from `chart_tri Z hty h h' x.1 x.2`.

Establish `e` using `M.chart k a a' i φ φ' d (h.trans h'.symm) (h ▸ hi) d1 (by rwa [← Category.assoc, h])`. Establish `e'` using `M'.chart k a a' j φ φ' d (h.trans h'.symm) (h ▸ hj) d1 (by rwa [← Category.assoc, h])`. Rewrite `e`, `e'` using `[h]`. Rewrite using `[e, e']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cross_eq (hty : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) (M : LineModel Z b st x) (M' : LineModel Z b' st' x)
    {k : Type} [Field k] {w : Sp k ⟶ Z.X} {a a' : Fin Z.m} {i : Fin M.L.n} {j : Fin M'.L.n}
    (ha : ⊤ ≤ w ⁻¹ᵁ (Z.U a).1) (ha' : ⊤ ≤ w ⁻¹ᵁ (Z.U a').1) (hi : ⊤ ≤ w ⁻¹ᵁ M.L.U i) (hj : ⊤ ≤ w ⁻¹ᵁ M'.L.U j) :
    valF w _ (M'.r a j).val * valF w _ (M.r a' i).val = valF w _ (M'.r a' j).val * valF w _ (M.r a i).val := by
  obtain ⟨φ, h⟩ := exists_fromSpec (Z.U a).2 w ha
  obtain ⟨φ', h'⟩ := exists_fromSpec (Z.U a').2 w ha'
  replace h : spMap φ ≫ Z.chart a = w := h
  replace h' : spMap φ' ≫ Z.chart a' = w := h'
  obtain ⟨d, d1, d2⟩ := chart_tri Z hty h h' x.1 x.2
  have e := M.chart k a a' i φ φ' d (h.trans h'.symm) (h ▸ hi) d1 (by rwa [← Category.assoc, h])
  have e' := M'.chart k a a' j φ φ' d (h.trans h'.symm) (h ▸ hj) d1 (by rwa [← Category.assoc, h])
  rw [h] at e e'
  rw [e, e']
  ring

def IsQuot (M : LineModel Z b st x) (M' : LineModel Z b' st' x) (i : Fin M.L.n) (j : Fin M'.L.n) (c : ℕ)
    {V : Z.X.Opens} (s : Γ(Z.X, V)) : Prop :=
  ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X) a, ⊤ ≤ w ⁻¹ᵁ (Z.U a).1 → ⊤ ≤ w ⁻¹ᵁ V →
    valF w V s * valF w _ (M.r a i).val = c * valF w _ (M'.r a j).val

variable (Z b st b' st') in

def Bdd : Prop := ∃ m : ℕ, ∀ (y : Z.Pt) a (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S), spMap φ ≫ Z.chart a = y.gen →
  |lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p b st - lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p b' st'| ≤
    m * Real.log p

omit hp hW in

/- English proof (translation)
The claim follows from `h.imp fun _ h y a φ e => (abs_sub_comm _ _).trans_le (h y a φ e)`.
-/
theorem Bdd.symm (h : Bdd Z b b' st st') : Bdd Z b' b st' st :=
  h.imp fun _ h y a φ e => (abs_sub_comm _ _).trans_le (h y a φ e)

omit hW in

/- English proof (translation)
Use `Fact.mk hp` as an intermediate fact. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `hl : 0 ≤ Real.log p` using `Real.log_natCast_nonneg p`. Establish `hv : 0 ≤ vDiff E p` using `by unfold vDiff; positivity`. Use `⟨1 + ⌈vDiff E p⌉₊, fun y a φ _ => ?_⟩` and prove the remaining obligations.

Establish `hv'` using `mul_le_mul_of_nonneg_right (Nat.le_ceil (vDiff E p)) hl`. Establish `hv''` using `mul_nonneg hv hl`. Establish `g : y.gen ≫ Z.π = spMap (intO ↥y.C.S).subtype ≫ y.z ≫ Z.π` using `Category.assoc _ _ _`. Establish `key {m : ℕ} (u : Fin m → _) (i : Fin m) : |Real.log (grNorm (Y Z.i).t (y.gen ≫ Z.π) (latDR _ (y.gen ≫ Z.π)) u i) - Real.log (grNorm (Y Z.i).t (y.gen ≫ Z.π) (latHT _ p (y.gen ≫ Z.π)) u i)| ≤ Real.log p`. Use `(HTFrame.abs_log_grNorm_sub_le _ _ (a := (p : ↥y.C.S)) (Nat.cast_ne_zero.2 hp.ne_zero) ?_ (latDR_subset_latHT E H _ _ _ p _) (fun v hv => ?_) u i).trans_eq (by rw [y.C.norm_p, inv_inv])` and prove the remaining obligations.

Rewrite using `[y.C.norm_p]`. Conclude with `inv_le_one_of_one_le₀ (by linarith)`. Rewrite `hv`, the goal using `[g]`. Use `HTBound.htBound E H _ _ p _ y.C.norm_p _ (ext_unique _ _) v hv _ ?_` and prove the remaining obligations. Rewrite using `[y.C.norm_p, ← Real.rpow_neg_one]`.

Use `Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg ?_)` and prove the remaining obligations. Rewrite using `[div_le_one (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Nat.cast_add, Nat.cast_one, add_mul, one_mul]`. Break down `st with ⟨τ, k⟩ | k` into its components or cases.

Simplify using `only [lnStep, lat, Bool.false_eq_true, false_and, if_false, true_and, sub_zero] split_ifs with h h'`. Use `abs_le.1 (key ((Z.fr a).bc φ τ) ⟨k, h⟩)` as an intermediate fact. Conclude with `abs_le.2 ⟨by linarith, by linarith⟩`. Use `abs_le.1 (key ((Z.fr a).bc φ τ) ⟨k, h⟩)` as an intermediate fact. Conclude with `abs_le.2 ⟨by linarith, by linarith⟩`.

Rewrite using `[sub_self, abs_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [lnStep, lat] split_ifs with h`. Conclude with `(key _ _).trans (by linarith)`. Rewrite using `[sub_self, abs_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bdd_step (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : Bdd Z false true st st := by
  have := Fact.mk hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hv : 0 ≤ vDiff E p := by unfold vDiff; positivity
  refine ⟨1 + ⌈vDiff E p⌉₊, fun y a φ _ => ?_⟩
  have hv' := mul_le_mul_of_nonneg_right (Nat.le_ceil (vDiff E p)) hl
  have hv'' := mul_nonneg hv hl
  have g : y.gen ≫ Z.π = spMap (intO ↥y.C.S).subtype ≫ y.z ≫ Z.π := Category.assoc _ _ _
  have key {m : ℕ} (u : Fin m → _) (i : Fin m) : |Real.log (grNorm (Y Z.i).t (y.gen ≫ Z.π) (latDR _ (y.gen ≫ Z.π)) u i) -
      Real.log (grNorm (Y Z.i).t (y.gen ≫ Z.π) (latHT _ p (y.gen ≫ Z.π)) u i)| ≤ Real.log p := by
    refine (HTFrame.abs_log_grNorm_sub_le _ _ (a := (p : ↥y.C.S)) (Nat.cast_ne_zero.2 hp.ne_zero) ?_
      (latDR_subset_latHT E H _ _ _ p _) (fun v hv => ?_) u i).trans_eq (by rw [y.C.norm_p, inv_inv])
    · rw [y.C.norm_p]
      exact inv_le_one_of_one_le₀ (by linarith)
    · rw [g] at hv ⊢
      refine HTBound.htBound E H _ _ p _ y.C.norm_p _ (ext_unique _ _) v hv _ ?_
      rw [y.C.norm_p, ← Real.rpow_neg_one]
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg ?_)
      rw [div_le_one (by linarith)]
      linarith
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  rcases st with ⟨τ, k⟩ | k
  · simp only [lnStep, lat, Bool.false_eq_true, false_and, if_false, true_and, sub_zero]
    split_ifs with h h'
    · have := abs_le.1 (key ((Z.fr a).bc φ τ) ⟨k, h⟩)
      exact abs_le.2 ⟨by linarith, by linarith⟩
    · have := abs_le.1 (key ((Z.fr a).bc φ τ) ⟨k, h⟩)
      exact abs_le.2 ⟨by linarith, by linarith⟩
    · rw [sub_self, abs_zero]
      linarith
  · simp only [lnStep, lat]
    split_ifs with h
    · exact (key _ _).trans (by linarith)
    · rw [sub_self, abs_zero]
      linarith

variable (hty : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) {M : LineModel Z b st x} {M' : LineModel Z b' st' x}

/- English proof (translation)
Establish `e : resG Z.X (inf_le_left : V ⊓ V' ≤ V) s * resG Z.X (inf_le_right : V ⊓ V' ≤ V') s' = 1`. Use `ext_chart hp hW fun k _ w a ha hw => ?_` and prove the remaining obligations. Establish `e₁` using `h k w a ha fun q hq => (hw hq).1`. Establish `e₂` using `h' k w a ha fun q hq => (hw hq).2`. Rewrite using `[valF_mul hw, valF_restrict _ hw, valF_restrict _ hw, valF_one hw]`.

Use `mul_right_cancel₀ (val_ne_zero M ha fun q hq => hi (hw hq).1) ?_` and prove the remaining obligations. Rewrite `e₁`, `e₂` using `[Nat.cast_one, one_mul]`. Rewrite using `[mul_right_comm, e₁, mul_comm, e₂, one_mul]`. Establish `hw₂ : ⊤ ≤ w ⁻¹ᵁ (V ⊓ V')` using `fun q hq => ⟨hw hq, hw' hq⟩`. Use `congrArg (valF w _) e` as an intermediate fact.

Rewrite `this` using `[valF_mul hw₂, valF_restrict _ hw₂, valF_restrict _ hw₂, valF_one hw₂]`. Then use the resulting hypothesis.
-/
theorem IsQuot.mul_eq_one {i : Fin M.L.n} {j : Fin M'.L.n} {V V' : Z.X.Opens} {s : Γ(Z.X, V)} {s' : Γ(Z.X, V')}
    (h : IsQuot M M' i j 1 s) (h' : IsQuot M' M j i 1 s') (hi : V ≤ M.L.U i) {k : Type} [Field k] {w : Sp k ⟶ Z.X}
    (hw : ⊤ ≤ w ⁻¹ᵁ V) (hw' : ⊤ ≤ w ⁻¹ᵁ V') : valF w V s * valF w V' s' = 1 := by
  have e : resG Z.X (inf_le_left : V ⊓ V' ≤ V) s * resG Z.X (inf_le_right : V ⊓ V' ≤ V') s' = 1 := by
    refine ext_chart hp hW fun k _ w a ha hw => ?_
    have e₁ := h k w a ha fun q hq => (hw hq).1
    have e₂ := h' k w a ha fun q hq => (hw hq).2
    rw [valF_mul hw, valF_restrict _ hw, valF_restrict _ hw, valF_one hw]
    refine mul_right_cancel₀ (val_ne_zero M ha fun q hq => hi (hw hq).1) ?_
    rw [Nat.cast_one, one_mul] at e₁ e₂
    rw [mul_right_comm, e₁, mul_comm, e₂, one_mul]
  have hw₂ : ⊤ ≤ w ⁻¹ᵁ (V ⊓ V') := fun q hq => ⟨hw hq, hw' hq⟩
  have := congrArg (valF w _) e
  rwa [valF_mul hw₂, valF_restrict _ hw₂, valF_restrict _ hw₂, valF_one hw₂] at this

include hty

/- English proof (translation)
Take `⟨m, hm⟩` from `hB`. Set `f (a) : Γ(Z.X, (Z.U a).1 ⊓ (M.L.U i ⊓ M'.L.U j))` to `Nat.cast (p ^ m) * (resG Z.X (inf_le_inf_left _ inf_le_right) (M'.r a j).val * resG Z.X (inf_le_inf_left _ inf_le_left) (M.r a i)⁻¹.val)`. Establish `hf (k : Type) [Field k] (w : Sp k ⟶ Z.X) (a) (ha : ⊤ ≤ w ⁻¹ᵁ (Z.U a).1) (hw : ⊤ ≤ w ⁻¹ᵁ (M.L.U i ⊓ M'.L.U j)) : valF w _ (f a) * valF w _ (M.r a i).val = (p ^ m : ℕ) * valF w _ (M'.r a j).val`. Establish `h' : ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ (M.L.U i ⊓ M'.L.U j))` using `fun q hq => ⟨ha hq, hw hq⟩`. Establish `v` using `valF_mul_inv (x := w) (U := (Z.U a).1 ⊓ M.L.U i) (fun q hq => ⟨ha hq, (hw hq).1⟩) (M.r a i)`.

Rewrite using `[valF_mul h', valF_mul h', valF_restrict _ h', valF_restrict _ h', valF_natCast h']`. Take the linear combination `((p ^ m : ℕ) : k) * valF w _ (M'.r a j).val * v`. Use `⟨m, (exists_extension hp hW f (fun k _ w a a' ha ha' hw => ?_) (fun y a ha hy => ?_) hz hpz).imp fun V => Exists.imp fun t ⟨hzV, hle, ht⟩ => ⟨hzV, hle, fun k _ w a ha hw => by` and prove the remaining obligations. Rewrite using `[ht k w a ha hw, hf k w a ha fun q hq => hle (hw hq)]⟩⟩`. Establish `hi : ⊤ ≤ w ⁻¹ᵁ M.L.U i` using `fun q hq => (hw hq).1`.

Use `mul_right_cancel₀ (mul_ne_zero (val_ne_zero M ha hi) (val_ne_zero M ha' hi)) ?_` and prove the remaining obligations. Take the linear combination `valF w _ (M.r a' i).val * hf k w a ha hw - valF w _ (M.r a i).val * hf k w a' ha' hw + ((p ^ m : ℕ) : k) * cross_eq hty M M' ha ha' hi fun q hq => (hw hq).2`. Establish `hw : ⊤ ≤ y.gen ⁻¹ᵁ (M.L.U i ⊓ M'.L.U j)` using `fun q _ => hy (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))`. Take `⟨φ, hφ⟩` from `exists_fromSpec (Z.U a).2 y.gen ha`. Establish `n` using `M.norm y a i φ hφ fun q hq => (hy hq).1`.

Establish `n'` using `M'.norm y a j φ hφ fun q hq => (hy hq).2`. Establish `r` using `norm_pos_iff.2 (val_ne_zero M ha fun q hq => (hw hq).1)`. Establish `r'` using `norm_pos_iff.2 (val_ne_zero M' ha fun q hq => (hw hq).2)`. Establish `hp0 : (0 : ℝ) < p` using `Nat.cast_pos.2 hp.pos`. Establish `e` using `congrArg norm (hf _ y.gen a ha hw)`.

Rewrite `e` using `[norm_mul, norm_mul, Nat.cast_pow, norm_pow, y.C.norm_p]`. Use `le_of_mul_le_mul_right ?_ r` and prove the remaining obligations. Rewrite using `[e, one_mul, ← Real.log_le_log_iff (by positivity) r, Real.log_mul (by positivity) r'.ne', Real.log_pow, Real.log_inv]`. Combine the linear relations using `[(abs_le.1 (hm y a φ hφ)).2]`.
-/
theorem exists_isQuot_special (hB : Bdd Z b b' st st') (i : Fin M.L.n) (j : Fin M'.L.n) {z : Z.X}
    (hz : z ∈ M.L.U i ⊓ M'.L.U j) (hpz : (p : Z.X.residueField z) = 0) :
    ∃ (m : ℕ) (V : Z.X.Opens) (t : Γ(Z.X, V)), z ∈ V ∧ V ≤ M.L.U i ⊓ M'.L.U j ∧ IsQuot M M' i j (p ^ m) t := by
  obtain ⟨m, hm⟩ := hB
  let f (a) : Γ(Z.X, (Z.U a).1 ⊓ (M.L.U i ⊓ M'.L.U j)) := Nat.cast (p ^ m) *
    (resG Z.X (inf_le_inf_left _ inf_le_right) (M'.r a j).val * resG Z.X (inf_le_inf_left _ inf_le_left) (M.r a i)⁻¹.val)
  have hf (k : Type) [Field k] (w : Sp k ⟶ Z.X) (a) (ha : ⊤ ≤ w ⁻¹ᵁ (Z.U a).1) (hw : ⊤ ≤ w ⁻¹ᵁ (M.L.U i ⊓ M'.L.U j)) :
      valF w _ (f a) * valF w _ (M.r a i).val = (p ^ m : ℕ) * valF w _ (M'.r a j).val := by
    have h' : ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ (M.L.U i ⊓ M'.L.U j)) := fun q hq => ⟨ha hq, hw hq⟩
    have v := valF_mul_inv (x := w) (U := (Z.U a).1 ⊓ M.L.U i) (fun q hq => ⟨ha hq, (hw hq).1⟩) (M.r a i)
    rw [valF_mul h', valF_mul h', valF_restrict _ h', valF_restrict _ h', valF_natCast h']
    linear_combination ((p ^ m : ℕ) : k) * valF w _ (M'.r a j).val * v
  refine ⟨m, (exists_extension hp hW f (fun k _ w a a' ha ha' hw => ?_) (fun y a ha hy => ?_) hz hpz).imp
    fun V => Exists.imp fun t ⟨hzV, hle, ht⟩ => ⟨hzV, hle, fun k _ w a ha hw => by
      rw [ht k w a ha hw, hf k w a ha fun q hq => hle (hw hq)]⟩⟩
  · have hi : ⊤ ≤ w ⁻¹ᵁ M.L.U i := fun q hq => (hw hq).1
    refine mul_right_cancel₀ (mul_ne_zero (val_ne_zero M ha hi) (val_ne_zero M ha' hi)) ?_
    linear_combination valF w _ (M.r a' i).val * hf k w a ha hw - valF w _ (M.r a i).val * hf k w a' ha' hw +
      ((p ^ m : ℕ) : k) * cross_eq hty M M' ha ha' hi fun q hq => (hw hq).2
  · have hw : ⊤ ≤ y.gen ⁻¹ᵁ (M.L.U i ⊓ M'.L.U j) := fun q _ => hy (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
    obtain ⟨φ, hφ⟩ := exists_fromSpec (Z.U a).2 y.gen ha
    have n := M.norm y a i φ hφ fun q hq => (hy hq).1
    have n' := M'.norm y a j φ hφ fun q hq => (hy hq).2
    have r := norm_pos_iff.2 (val_ne_zero M ha fun q hq => (hw hq).1)
    have r' := norm_pos_iff.2 (val_ne_zero M' ha fun q hq => (hw hq).2)
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.2 hp.pos
    have e := congrArg norm (hf _ y.gen a ha hw)
    rw [norm_mul, norm_mul, Nat.cast_pow, norm_pow, y.C.norm_p] at e
    refine le_of_mul_le_mul_right ?_ r
    rw [e, one_mul, ← Real.log_le_log_iff (by positivity) r, Real.log_mul (by positivity) r'.ne', Real.log_pow,
      Real.log_inv]
    linarith [(abs_le.1 (hm y a φ hφ)).2]

/- English proof (translation)
Take `⟨z₀, hz₀, hpz⟩` from `exists_special hp hW z`. Take `⟨i₁, hi₁⟩` from `LB.mem_of_cover M.L.isLB z₀`. Take `⟨j₁, hj₁⟩` from `LB.mem_of_cover M'.L.isLB z₀`. Take `⟨m, V, t, hV, hle, ht⟩` from `exists_isQuot_special hp hW hty hB i₁ j₁ ⟨hi₁, hj₁⟩ hpz`. Set `T` to `V ⊓ ((nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j))`.

Establish `l : T ≤ M.L.U i ⊓ M.L.U i₁` using `fun q hq => ⟨hq.2.2.1, (hle hq.1).1⟩`. Establish `l' : T ≤ M'.L.U j ⊓ M'.L.U j₁` using `fun q hq => ⟨hq.2.2.2, (hle hq.1).2⟩`. Establish `hu : IsUnit ((p ^ m : ℕ) : Γ(Z.X, T))`. Establish `h : IsUnit (resG Z.X (Z.X.basicOpen_le (p : Γ(Z.X, ⊤))) p)` using `Z.X.toRingedSpace.isUnit_res_basicOpen _`. Use `h.map (resG Z.X (U := Z.X.basicOpen (p : Γ(Z.X, ⊤))) (V := T) fun q hq => (gen_eq_basicOpen hp hW (Z := Z)).le hq.2.1)` as an intermediate fact.

Rewrite `this` using `[map_natCast, map_natCast]`. Simplify using `using this.pow m`. Use `⟨T, resG Z.X inf_le_left t * resG Z.X l (M.L.g i i₁).val * resG Z.X l' (M'.L.g j j₁)⁻¹.val * hu.unit⁻¹.val, ⟨hz₀.mem_open V.isOpen hV, hz⟩, inf_le_right, fun k _ w a ha hw => ?_⟩` and prove the remaining obligations. Establish `e₁` using `ht k w a ha fun q hq => (hw hq).1`. Establish `e₂` using `M.trans k w a i i₁ fun q hq => ⟨ha hq, l (hw hq)⟩`.

Establish `e₃` using `M'.trans k w a j j₁ fun q hq => ⟨ha hq, l' (hw hq)⟩`. Establish `e₄` using `valF_mul_inv (x := w) (U := M'.L.U j ⊓ M'.L.U j₁) (fun q hq => l' (hw hq)) (M'.L.g j j₁)`. Establish `e₅` using `valF_mul_inv hw hu.unit`. Rewrite `e₅` using `[IsUnit.unit_spec, valF_natCast hw]`. Rewrite `e₁` using `[e₂, e₃]`.

Rewrite using `[valF_mul hw, valF_mul hw, valF_mul hw, valF_restrict _ hw, valF_restrict _ hw, valF_restrict _ hw, Nat.cast_one]`. Take the linear combination `valF w _ (M'.L.g j j₁)⁻¹.val * valF w _ hu.unit⁻¹.val * e₁ + ((p ^ m : ℕ) : k) * valF w _ hu.unit⁻¹.val * valF w _ (M'.r a j).val * e₄ + valF w _ (M'.r a j).val * e₅`.
-/
theorem exists_isQuot (hB : Bdd Z b b' st st') (i : Fin M.L.n) (j : Fin M'.L.n) {z : Z.X}
    (hz : z ∈ (nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j)) : ∃ (V : Z.X.Opens) (s : Γ(Z.X, V)), z ∈ V ∧
      V ≤ (nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j) ∧ IsQuot M M' i j 1 s := by
  obtain ⟨z₀, hz₀, hpz⟩ := exists_special hp hW z
  obtain ⟨i₁, hi₁⟩ := LB.mem_of_cover M.L.isLB z₀
  obtain ⟨j₁, hj₁⟩ := LB.mem_of_cover M'.L.isLB z₀
  obtain ⟨m, V, t, hV, hle, ht⟩ := exists_isQuot_special hp hW hty hB i₁ j₁ ⟨hi₁, hj₁⟩ hpz
  let T := V ⊓ ((nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j))
  have l : T ≤ M.L.U i ⊓ M.L.U i₁ := fun q hq => ⟨hq.2.2.1, (hle hq.1).1⟩
  have l' : T ≤ M'.L.U j ⊓ M'.L.U j₁ := fun q hq => ⟨hq.2.2.2, (hle hq.1).2⟩
  have hu : IsUnit ((p ^ m : ℕ) : Γ(Z.X, T)) := by
    have h : IsUnit (resG Z.X (Z.X.basicOpen_le (p : Γ(Z.X, ⊤))) p) := Z.X.toRingedSpace.isUnit_res_basicOpen _
    have := h.map
      (resG Z.X (U := Z.X.basicOpen (p : Γ(Z.X, ⊤))) (V := T) fun q hq => (gen_eq_basicOpen hp hW (Z := Z)).le hq.2.1)
    rw [map_natCast, map_natCast] at this
    simpa using this.pow m
  refine ⟨T, resG Z.X inf_le_left t * resG Z.X l (M.L.g i i₁).val * resG Z.X l' (M'.L.g j j₁)⁻¹.val * hu.unit⁻¹.val,
    ⟨hz₀.mem_open V.isOpen hV, hz⟩, inf_le_right, fun k _ w a ha hw => ?_⟩
  have e₁ := ht k w a ha fun q hq => (hw hq).1
  have e₂ := M.trans k w a i i₁ fun q hq => ⟨ha hq, l (hw hq)⟩
  have e₃ := M'.trans k w a j j₁ fun q hq => ⟨ha hq, l' (hw hq)⟩
  have e₄ := valF_mul_inv (x := w) (U := M'.L.U j ⊓ M'.L.U j₁) (fun q hq => l' (hw hq)) (M'.L.g j j₁)
  have e₅ := valF_mul_inv hw hu.unit
  rw [IsUnit.unit_spec, valF_natCast hw] at e₅
  rw [e₂, e₃] at e₁
  rw [valF_mul hw, valF_mul hw, valF_mul hw, valF_restrict _ hw, valF_restrict _ hw, valF_restrict _ hw, Nat.cast_one]
  linear_combination valF w _ (M'.L.g j j₁)⁻¹.val * valF w _ hu.unit⁻¹.val * e₁ +
    ((p ^ m : ℕ) : k) * valF w _ hu.unit⁻¹.val * valF w _ (M'.r a j).val * e₄ + valF w _ (M'.r a j).val * e₅

/- English proof (translation)
Use `isReduced_model Z` as an intermediate fact. Set `P (k : Type) [Field k] (w : Sp k ⟶ Z.X) (c : k) : Prop` to `∃ (V : Z.X.Opens) (s : Γ(Z.X, V)), V ≤ M.L.U i ∧ IsQuot M M' i j 1 s ∧ ⊤ ≤ w ⁻¹ᵁ V ∧ valF w V s = c`. Establish `key (k : Type) [Field k] (w : Sp k ⟶ Z.X) (hw : ⊤ ≤ w ⁻¹ᵁ ((nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j))) : ∃ d : k, ∀ c, P k w c → c * d = 1`. Establish `hz` using `(le_preimage_iff _).1 hw`. Take `⟨V', s', h₁, -, h₂⟩` from `exists_isQuot hp hW hty (M := M') (M' := M) hB.symm j i ⟨hz.1, hz.2.2, hz.2.1⟩`.

Conclude with `⟨_, fun c ⟨V, s, a₁, a₂, a₃, a₄⟩ => a₄ ▸ a₂.mul_eq_one hp hW h₂ a₁ a₃ ((le_preimage_iff _).2 h₁)⟩`. Take `⟨u, hu⟩` from `exists_unit_of_locally Z.X ((nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j)) P (fun k _ w c c' hw h h' => by`. Take `⟨d, hd⟩` from `key k w hw`. Conclude with `(eq_inv_of_mul_eq_one_left (hd c h)).trans (eq_inv_of_mul_eq_one_left (hd c' h')).symm)`. Use the proof step `(fun k _ w hw h => by`.

Take `⟨d, hd⟩` from `key k w hw`. Simplify using `using hd 0 h)`. Use `fun z hz => by`. Take `⟨V, s, h₁, h₂, h₃⟩` from `exists_isQuot hp hW hty hB i j hz`. Conclude with `⟨V, s, h₁, h₂, fun k _ w hw => ⟨V, s, fun q hq => (h₂ hq).2.1, h₃, hw, rfl⟩⟩`.

Use `⟨u, fun k _ w a ha hw => ?_⟩` and prove the remaining obligations. Take `⟨V, s, -, h₁, h₂, h₃⟩` from `hu k w hw`. Conclude with `h₃ ▸ h₁ k w a ha h₂`.
-/
theorem exists_unit (hB : Bdd Z b b' st st') (i : Fin M.L.n) (j : Fin M'.L.n) :
    ∃ u : Γ(Z.X, (nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j))ˣ, IsQuot M M' i j 1 u.val := by
  have := isReduced_model Z
  let P (k : Type) [Field k] (w : Sp k ⟶ Z.X) (c : k) : Prop := ∃ (V : Z.X.Opens) (s : Γ(Z.X, V)),
    V ≤ M.L.U i ∧ IsQuot M M' i j 1 s ∧ ⊤ ≤ w ⁻¹ᵁ V ∧ valF w V s = c
  have key (k : Type) [Field k] (w : Sp k ⟶ Z.X) (hw : ⊤ ≤ w ⁻¹ᵁ ((nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j))) :
      ∃ d : k, ∀ c, P k w c → c * d = 1 := by
    have hz := (le_preimage_iff _).1 hw
    obtain ⟨V', s', h₁, -, h₂⟩ := exists_isQuot hp hW hty (M := M') (M' := M) hB.symm j i ⟨hz.1, hz.2.2, hz.2.1⟩
    exact ⟨_, fun c ⟨V, s, a₁, a₂, a₃, a₄⟩ => a₄ ▸ a₂.mul_eq_one hp hW h₂ a₁ a₃ ((le_preimage_iff _).2 h₁)⟩
  obtain ⟨u, hu⟩ := exists_unit_of_locally Z.X ((nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j)) P
    (fun k _ w c c' hw h h' => by
      obtain ⟨d, hd⟩ := key k w hw
      exact (eq_inv_of_mul_eq_one_left (hd c h)).trans (eq_inv_of_mul_eq_one_left (hd c' h')).symm)
    (fun k _ w hw h => by
      obtain ⟨d, hd⟩ := key k w hw
      simpa using hd 0 h)
    fun z hz => by
      obtain ⟨V, s, h₁, h₂, h₃⟩ := exists_isQuot hp hW hty hB i j hz
      exact ⟨V, s, h₁, h₂, fun k _ w hw => ⟨V, s, fun q hq => (h₂ hq).2.1, h₃, hw, rfl⟩⟩
  refine ⟨u, fun k _ w a ha hw => ?_⟩
  obtain ⟨V, s, -, h₁, h₂, h₃⟩ := hu k w hw
  exact h₃ ▸ h₁ k w a ha h₂

end GenId

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : LocM.Mdl Y i₀} {b b' : Bool} {st st' : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw}

def IsGenId (M : LineModel Z b st x) (M' : LineModel Z b' st' x) (u : GenIso Z M.L M'.L) : Prop :=
  ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X) a i j, ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ (M.L.U i ⊓ M'.L.U j)) →
    valF w _ (u.u i j).val * valF w _ (M.r a i).val = valF w _ (M'.r a j).val

variable (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) {M : LineModel Z b st x} {M' : LineModel Z b' st' x}

include hp hW

/- English proof (translation)
Use `NModel.GenIso.ext (funext₂ fun i j => Units.ext (GenId.ext_chart hp hW fun k _ w a ha hw => ?_))` and prove the remaining obligations. Conclude with `mul_right_cancel₀ (GenId.val_ne_zero M ha fun q hq => (hw hq).2.1) ((h k w a i j fun q hq => ⟨ha hq, (hw hq).2⟩).trans (h' k w a i j fun q hq => ⟨ha hq, (hw hq).2⟩).symm)`.
-/
theorem IsGenId.unique {u u' : GenIso Z M.L M'.L} (h : IsGenId M M' u) (h' : IsGenId M M' u') : u = u' := by
  refine NModel.GenIso.ext (funext₂ fun i j => Units.ext (GenId.ext_chart hp hW fun k _ w a ha hw => ?_))
  exact mul_right_cancel₀ (GenId.val_ne_zero M ha fun q hq => (hw hq).2.1)
    ((h k w a i j fun q hq => ⟨ha hq, (hw hq).2⟩).trans (h' k w a i j fun q hq => ⟨ha hq, (hw hq).2⟩).symm)

/- English proof (translation)
Use `choose u hu using GenId.exists_unit hp hW hty (M := M) (M' := M') hB`. Establish `hu' (k : Type) [Field k] (w : Sp k ⟶ Z.X) (a i j) (h : ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ (M.L.U i ⊓ M'.L.U j))) : valF w _ (u i j).val * valF w _ (M.r a i).val = valF w _ (M'.r a j).val`. Simplify using `using hu i j k w a (fun q hq => (h hq).1) fun q hq => ⟨chart_le_gen hp hW a (h hq).1, (h hq).2⟩`. Use `⟨⟨u, fun i i₁ j j₁ => Units.ext (GenId.ext_chart hp hW fun k _ w a ha hw => ?_)⟩, hu'⟩` and prove the remaining obligations. Establish `e₁` using `hu' k w a i j fun q hq => ⟨ha hq, (hw hq).1.2⟩`.

Establish `e₂` using `hu' k w a i₁ j₁ fun q hq => ⟨ha hq, (hw hq).2⟩`. Establish `e₃` using `M.trans k w a i i₁ fun q hq => ⟨ha hq, (hw hq).1.2.1, (hw hq).2.1⟩`. Establish `e₄` using `M'.trans k w a j j₁ fun q hq => ⟨ha hq, (hw hq).1.2.2, (hw hq).2.2⟩`. Rewrite `e₂` using `[e₃, e₄]`. Use `((valF_mul hw _ _).trans (congrArg₂ (· * ·) (valF_restrict _ hw _) (valF_restrict _ hw _))).trans (Eq.trans ?_ ((valF_mul hw _ _).trans (congrArg₂ (· * ·) (valF_restrict _ hw _) (valF_restrict _ hw _))).symm)` and prove the remaining obligations.

Use `mul_right_cancel₀ (GenId.val_ne_zero M ha fun q hq => (hw hq).1.2.1) ?_` and prove the remaining obligations. Take the linear combination `valF w _ (M'.L.g j j₁).val * e₁ - e₂`.
-/
theorem exists_isGenId (hty : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) (hB : GenId.Bdd Z b b' st st')
    (M : LineModel Z b st x) (M' : LineModel Z b' st' x) : ∃ u, IsGenId M M' u := by
  choose u hu using GenId.exists_unit hp hW hty (M := M) (M' := M') hB
  have hu' (k : Type) [Field k] (w : Sp k ⟶ Z.X) (a i j) (h : ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ (M.L.U i ⊓ M'.L.U j))) :
      valF w _ (u i j).val * valF w _ (M.r a i).val = valF w _ (M'.r a j).val := by
    simpa using hu i j k w a (fun q hq => (h hq).1) fun q hq => ⟨chart_le_gen hp hW a (h hq).1, (h hq).2⟩
  refine ⟨⟨u, fun i i₁ j j₁ => Units.ext (GenId.ext_chart hp hW fun k _ w a ha hw => ?_)⟩, hu'⟩
  have e₁ := hu' k w a i j fun q hq => ⟨ha hq, (hw hq).1.2⟩
  have e₂ := hu' k w a i₁ j₁ fun q hq => ⟨ha hq, (hw hq).2⟩
  have e₃ := M.trans k w a i i₁ fun q hq => ⟨ha hq, (hw hq).1.2.1, (hw hq).2.1⟩
  have e₄ := M'.trans k w a j j₁ fun q hq => ⟨ha hq, (hw hq).1.2.2, (hw hq).2.2⟩
  rw [e₃, e₄] at e₂
  refine ((valF_mul hw _ _).trans (congrArg₂ (· * ·) (valF_restrict _ hw _) (valF_restrict _ hw _))).trans
    (Eq.trans ?_ ((valF_mul hw _ _).trans (congrArg₂ (· * ·) (valF_restrict _ hw _) (valF_restrict _ hw _))).symm)
  refine mul_right_cancel₀ (GenId.val_ne_zero M ha fun q hq => (hw hq).1.2.1) ?_
  linear_combination valF w _ (M'.L.g j j₁).val * e₁ - e₂

end GlobalTheory.ShFam.Pad
