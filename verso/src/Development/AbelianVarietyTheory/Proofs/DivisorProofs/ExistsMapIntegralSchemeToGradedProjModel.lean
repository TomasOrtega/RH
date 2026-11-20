import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueMorphismsIntegralAgreeAtGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAndUnitPreservedByFunctionFieldCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointCompStructureEqSpecMapConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomToAffineOpenOfFunctionFieldMapRegularStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ToModel

/- English proof (translation)
Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[terminal.hom_ext (terminal.from P) (p ≫ terminal.from _)]`. Use `infer_instance`.
-/
theorem sep (R : Type) [CommRing R] (P : Scheme.{0}) (p : P ⟶ Sp R) [IsSeparated p] : P.IsSeparated := by
  refine ⟨?_⟩
  rw [terminal.hom_ext (terminal.from P) (p ≫ terminal.from _)]
  infer_instance

/- English proof (translation)
Use `⟨?_⟩` and prove the remaining obligations. Establish `h : genericPoint Y ∈ Set.range (gp Y)` using `⟨closedPoint _, Scheme.fromSpecStalk_closedPoint⟩`. Use `Dense.mono (Set.singleton_subset_iff.2 h) ?_` and prove the remaining obligations. Rewrite using `[dense_iff_closure_eq, (genericPoint_spec Y).def]`.
-/
theorem gp_dom (Y : Scheme.{0}) [IsIntegral Y] : IsDominant (gp Y) := by
  refine ⟨?_⟩
  have h : genericPoint Y ∈ Set.range (gp Y) := ⟨closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  refine Dense.mono (Set.singleton_subset_iff.2 h) ?_
  rw [dense_iff_closure_eq, (genericPoint_spec Y).def]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero]`. Conclude with `(unitAt_one y).regAt`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ih.mul h`.
-/
theorem regAt_pow {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {x : Y.functionField} (h : RegAt y x) (m : ℕ) :
    RegAt y (x ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact (unitAt_one y).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

/- English proof (translation)
Take `⟨g, hg⟩` from `D.exists_isEqn y`. Establish `h1` using `((hg.nsmul (k * m)).regularAt_iff).1 (ha y)`. Establish `h2` using `((hg.nsmul k).generatesAt_iff).1 hu`. Establish `e : a / u ^ m = (a * ((g ^ (k * m) : Y.functionFieldˣ) : Y.functionField)) * ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ m`. Establish `hg0 : ((g : Y.functionFieldˣ) : Y.functionField) ≠ 0` using `Units.ne_zero _`.

Use `push_cast`. Rewrite using `[inv_pow, mul_pow, ← pow_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `h1.mul (regAt_pow h2.inv.regAt m)`.
-/
theorem reg_div (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (k m : ℕ) (u a : Y.functionField) (y : Y)
    (ha : a ∈ Sec D (k * m)) (hu : y ∈ locus D k u) : RegAt y (a / u ^ m) := by
  obtain ⟨g, hg⟩ := D.exists_isEqn y
  have h1 := ((hg.nsmul (k * m)).regularAt_iff).1 (ha y)
  have h2 := ((hg.nsmul k).generatesAt_iff).1 hu
  have e : a / u ^ m = (a * ((g ^ (k * m) : Y.functionFieldˣ) : Y.functionField)) *
      ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ m := by
    have hg0 : ((g : Y.functionFieldˣ) : Y.functionField) ≠ 0 := Units.ne_zero _
    push_cast
    rw [inv_pow, mul_pow, ← pow_mul]
    field_simp
  rw [e]
  exact h1.mul (regAt_pow h2.inv.regAt m)

/- English proof (translation)
Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `y hy`. Take `⟨g, hg, hu⟩` from `hy`. Take `⟨U, hyU, hU⟩` from `hg.exists_nhds`. Take `⟨V, hyV, hV⟩` from `hu.exists_nhds`.

Conclude with `⟨(U ⊓ V : Y.Opens), fun z hz => ⟨g, hU z hz.1, hV z hz.2⟩, (U ⊓ V).2, ⟨hyU, hyV⟩⟩`.
-/
theorem locus_open (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (k : ℕ) (u : Y.functionField) :
    IsOpen (locus D k u) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨g, hg, hu⟩ := hy
  obtain ⟨U, hyU, hU⟩ := hg.exists_nhds
  obtain ⟨V, hyV, hV⟩ := hu.exists_nhds
  exact ⟨(U ⊓ V : Y.Opens), fun z hz => ⟨g, hU z hz.1, hV z hz.2⟩, (U ⊓ V).2, ⟨hyU, hyV⟩⟩

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero]`. Conclude with `unitAt_one y`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ih.mul h`.
-/
theorem unitAt_pow {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {x : Y.functionField} (h : UnitAt y x) (m : ℕ) :
    UnitAt y (x ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact unitAt_one y
  | succ n ih => rw [pow_succ]; exact ih.mul h

/- English proof (translation)
Establish `hx : x ≠ 0` using `fun h0 => hu.ne_zero (by rw [h0, zero_pow (by omega)])`. Use `(unitAt_iff hx).2 ⟨h, ?_⟩` and prove the remaining obligations. Establish `e : x⁻¹ = x ^ (n - 1) * (x ^ n)⁻¹`. Take `⟨j, rfl⟩ : ∃ j, n = j + 1` from `⟨n - 1, by omega⟩`. Rewrite using `[Nat.add_sub_cancel, pow_succ]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `(regAt_pow h _).mul hu.inv.regAt`.
-/
theorem unitAt_of_pow {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {x : Y.functionField} (h : RegAt y x) {n : ℕ}
    (hn : 1 ≤ n) (hu : UnitAt y (x ^ n)) : UnitAt y x := by
  have hx : x ≠ 0 := fun h0 => hu.ne_zero (by rw [h0, zero_pow (by omega)])
  refine (unitAt_iff hx).2 ⟨h, ?_⟩
  have e : x⁻¹ = x ^ (n - 1) * (x ^ n)⁻¹ := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp
  rw [e]
  exact (regAt_pow h _).mul hu.inv.regAt

/- English proof (translation)
Take `⟨g, hg⟩` from `D.exists_isEqn y`. Establish `h2` using `((hg.nsmul k).generatesAt_iff).1 hu`. Establish `h1` using `((hg.nsmul k').regularAt_iff).1 (hu' y)`. Establish `e : u' ^ k / u ^ k' = (u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k * ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ k'`. Establish `hg0 : ((g : Y.functionFieldˣ) : Y.functionField) ≠ 0` using `Units.ne_zero _`.

Use `push_cast`. Rewrite using `[inv_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k' k]`. Clear the denominators using the available nonvanishing facts. Use `show (k' • D).GeneratesAt y u' ↔ _`. Rewrite using `[(hg.nsmul k').generatesAt_iff, e]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(unitAt_pow h k).mul (unitAt_pow h2.inv k')`. Introduce `h`. Use `unitAt_of_pow h1 hk ?_` and prove the remaining obligations.

Establish `e2 : (u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k = ((u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k * ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ k') * (u * ((g ^ k : Y.functionFieldˣ) : Y.functionField)) ^ k'`. Establish `h0 : (u * ((g ^ k : Y.functionFieldˣ) : Y.functionField)) ≠ 0` using `h2.ne_zero`. Rewrite using `[inv_pow, _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h0), _root_.mul_one]`. Rewrite using `[e2]`. Conclude with `h.mul (unitAt_pow h2 k')`.
-/
theorem locus_iff {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) {k k' : ℕ} (hk : 1 ≤ k)
    {u u' : Y.functionField} {y : Y} (hu : y ∈ locus D k u) (hu' : u' ∈ Sec D k') :
    y ∈ locus D k' u' ↔ UnitAt y (u' ^ k / u ^ k') := by
  obtain ⟨g, hg⟩ := D.exists_isEqn y
  have h2 := ((hg.nsmul k).generatesAt_iff).1 hu
  have h1 := ((hg.nsmul k').regularAt_iff).1 (hu' y)
  have e : u' ^ k / u ^ k' = (u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k *
      ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ k' := by
    have hg0 : ((g : Y.functionFieldˣ) : Y.functionField) ≠ 0 := Units.ne_zero _
    push_cast
    rw [inv_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k' k]
    field_simp
  show (k' • D).GeneratesAt y u' ↔ _
  rw [(hg.nsmul k').generatesAt_iff, e]
  constructor
  · intro h
    exact (unitAt_pow h k).mul (unitAt_pow h2.inv k')
  · intro h
    refine unitAt_of_pow h1 hk ?_
    have e2 : (u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k =
        ((u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k *
          ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ k') *
        (u * ((g ^ k : Y.functionFieldˣ) : Y.functionField)) ^ k' := by
      have h0 : (u * ((g ^ k : Y.functionFieldˣ) : Y.functionField)) ≠ 0 := h2.ne_zero
      rw [inv_pow, _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h0), _root_.mul_one]
    rw [e2]
    exact h.mul (unitAt_pow h2 k')

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using hN.one`. Consider the case `succ n ih => rw [pow_succ, Nat.mul_succ]`. Conclude with `hN.mul _ _ _ ih _ hb`.
-/
theorem pow_mem {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F} (hN : GradedFam c₀ N)
    {k : ℕ} {b : F} (hb : b ∈ N k) (n : ℕ) : b ^ n ∈ N (k * n) := by
  induction n with
  | zero => simpa using hN.one
  | succ n ih => rw [pow_succ, Nat.mul_succ]; exact hN.mul _ _ _ ih _ hb

/- English proof (translation)
Introduce `R F _ _ _ c₀ N hN P _ p ψ Dp hM R₁ _ ρ Y _ q θ D₁ hc hsec hcov`. Use `haveI : IsSeparated p := hM.sep`. Use `haveI : P.IsSeparated := sep R P p`. Use `choose k hk b hb hy using hcov`. Establish `hb0 : ∀ y, b y ≠ 0` using `fun y h => (hy y).ne_zero (by rw [h, map_zero])`.

Set `U : Y → Y.Opens` to `fun y => ⟨locus D₁ (k y) (θ (b y)), locus_open Y D₁ _ _⟩`. Establish `hyU : ∀ y, y ∈ U y` using `hy`. Establish `hgen : ∀ y, genericPoint Y ∈ U y` using `fun y => gen_mem (hyU y)`. Establish `hPη : ∀ y, genericPoint P ∈ Dp (k y) (b y)` using `fun y => (hM.gen _ (hk y) _ (hb y)).2 (hb0 y)`. Establish `hreg : ∀ y (s : Γ(P, Dp (k y) (b y))), ∀ z ∈ U y, RegAt z ((θ.comp ψ) (fnOf _ (hPη y) s))`.

Introduce `y s z hz`. Take `⟨m, a, ha, he⟩` from `(hM.ring _ (hk y) _ (hb y) (hb0 y) (ψ (fnOf _ (hPη y) s))).1 ⟨_, fun z' hz' => regAt_fnOf hz' _ s, rfl⟩`. Use `show RegAt z (θ (ψ _))`. Rewrite using `[he, map_div₀, map_pow]`. Conclude with `reg_div Y D₁ (k y) m (θ (b y)) (θ a) z (hsec _ a ha) hz`.

Use `choose f hfV hf using fun y => GlobalTheory.T.exists_hom_to_affineOpen_of_functionField_map_regular Y P (U y) (hgen y) (Dp (k y) (b y)) (hM.affine _ (hk y) _ (hb y)) (hPη y) (θ.comp ψ) (hreg y)`. Take `⟨m, hmU, hmg⟩` from `GlobalTheory.T.exists_glue_morphisms_integral_agree_at_genericPoint Y P U hyU f (spMap (θ.comp ψ) ≫ gp P) hf`. Use `⟨m, ?_, ⟨gp Y, Category.comp_id _, hmg⟩, ?_⟩` and prove the remaining obligations. Use `haveI := gp_dom Y`. Use `ext_of_isDominant (gp Y) ?_` and prove the remaining obligations.

Rewrite using `[reassoc_of% hmg, GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants P R p, ← Category.assoc, GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants Y R₁ q, ← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `θ (ψ (cst p x)) = cst q (ρ x)`. Establish `h1` using `congrArg (fun g => g x) hc`.

Establish `h2` using `congrArg (fun g => g x) hM.const`. Simplify using `only [RingHom.comp_apply] at h1 h2`. Rewrite using `[h2, h1]`. Introduce `k' hk' b' hb' y`. Establish `hmy : m y ∈ Dp (k y) (b y)`.

Establish `h1` using `hfV y ⟨y, hyU y⟩`. Rewrite `h1` using `[← hmU y]`. Conclude with `h1`. Rewrite using `[hM.mem _ (hk y) _ (hb y) _ hmy k' hk' b' hb']`. Take `⟨v₀, hv₀, hψ⟩` from `(hM.ring _ (hk y) _ (hb y) (hb0 y) (b' ^ (k y) / b y ^ k')).2 ⟨k', b' ^ (k y), by rw [mul_comm]; exact pow_mem hN hb' _, rfl⟩`.

Establish `hst` using `GlobalTheory.T.regular_and_unit_preserved_by_functionField_compatible Y P m (θ.comp ψ) hmg y v₀ (hv₀ _ hmy)`. Establish `hl` using `locus_iff D₁ (hk y) (hy y) (hsec _ _ hb')`. Establish `e : (θ.comp ψ) v₀ = θ b' ^ (k y) / θ (b y) ^ k'`. Rewrite using `[RingHom.comp_apply, hψ, map_div₀, map_pow, map_pow]`. Rewrite using `[hl, ← e]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, hvw⟩`. Take `rfl : v = v₀` from `ψ.injective (hvw.trans hψ.symm)`. Conclude with `hst.2.2 hv`. Introduce `h`.

Conclude with `⟨v₀, hst.2.1 h, hψ⟩`.
-/
theorem exists_map_to_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] (ρ : R →+* R₁) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → (∀ k, ∀ a ∈ N k, θ a ∈ Sec D₁ k) → (∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b)) → ∃ m : Y ⟶ P, m ≫ p = q ≫ spMap ρ ∧ PFF (𝟙 _) m (θ.comp ψ) ∧ ∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b) := by
  intro R F _ _ _ c₀ N hN P _ p ψ Dp hM R₁ _ ρ Y _ q θ D₁ hc hsec hcov
  haveI : IsSeparated p := hM.sep
  haveI : P.IsSeparated := sep R P p
  choose k hk b hb hy using hcov
  have hb0 : ∀ y, b y ≠ 0 := fun y h => (hy y).ne_zero (by rw [h, map_zero])
  let U : Y → Y.Opens := fun y => ⟨locus D₁ (k y) (θ (b y)), locus_open Y D₁ _ _⟩
  have hyU : ∀ y, y ∈ U y := hy
  have hgen : ∀ y, genericPoint Y ∈ U y := fun y => gen_mem (hyU y)
  have hPη : ∀ y, genericPoint P ∈ Dp (k y) (b y) := fun y => (hM.gen _ (hk y) _ (hb y)).2 (hb0 y)
  have hreg : ∀ y (s : Γ(P, Dp (k y) (b y))), ∀ z ∈ U y, RegAt z ((θ.comp ψ) (fnOf _ (hPη y) s)) := by
    intro y s z hz
    obtain ⟨m, a, ha, he⟩ := (hM.ring _ (hk y) _ (hb y) (hb0 y) (ψ (fnOf _ (hPη y) s))).1
      ⟨_, fun z' hz' => regAt_fnOf hz' _ s, rfl⟩
    show RegAt z (θ (ψ _))
    rw [he, map_div₀, map_pow]
    exact reg_div Y D₁ (k y) m (θ (b y)) (θ a) z (hsec _ a ha) hz
  choose f hfV hf using fun y => GlobalTheory.T.exists_hom_to_affineOpen_of_functionField_map_regular Y P (U y) (hgen y) (Dp (k y) (b y)) (hM.affine _ (hk y) _ (hb y)) (hPη y)
    (θ.comp ψ) (hreg y)
  obtain ⟨m, hmU, hmg⟩ := GlobalTheory.T.exists_glue_morphisms_integral_agree_at_genericPoint Y P U hyU f (spMap (θ.comp ψ) ≫ gp P) hf
  refine ⟨m, ?_, ⟨gp Y, Category.comp_id _, hmg⟩, ?_⟩
  · haveI := gp_dom Y
    refine ext_of_isDominant (gp Y) ?_
    rw [reassoc_of% hmg, GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants P R p, ← Category.assoc, GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants Y R₁ q, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    change θ (ψ (cst p x)) = cst q (ρ x)
    have h1 := congrArg (fun g => g x) hc
    have h2 := congrArg (fun g => g x) hM.const
    simp only [RingHom.comp_apply] at h1 h2
    rw [h2, h1]
  · intro k' hk' b' hb' y
    have hmy : m y ∈ Dp (k y) (b y) := by
      have h1 := hfV y ⟨y, hyU y⟩
      rw [← hmU y] at h1
      exact h1
    rw [hM.mem _ (hk y) _ (hb y) _ hmy k' hk' b' hb']
    obtain ⟨v₀, hv₀, hψ⟩ := (hM.ring _ (hk y) _ (hb y) (hb0 y) (b' ^ (k y) / b y ^ k')).2
      ⟨k', b' ^ (k y), by rw [mul_comm]; exact pow_mem hN hb' _, rfl⟩
    have hst := GlobalTheory.T.regular_and_unit_preserved_by_functionField_compatible Y P m (θ.comp ψ) hmg y v₀ (hv₀ _ hmy)
    have hl := locus_iff D₁ (hk y) (hy y) (hsec _ _ hb')
    have e : (θ.comp ψ) v₀ = θ b' ^ (k y) / θ (b y) ^ k' := by
      rw [RingHom.comp_apply, hψ, map_div₀, map_pow, map_pow]
    rw [hl, ← e]
    constructor
    · rintro ⟨v, hv, hvw⟩
      obtain rfl : v = v₀ := ψ.injective (hvw.trans hψ.symm)
      exact hst.2.2 hv
    · intro h
      exact ⟨v₀, hst.2.1 h, hψ⟩

end GlobalTheory.Desc.ToModel
