import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightLeOneOfFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussAtCompAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnOfPreimageMemSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentDataChartsCommonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussAtHeightOneVerticalPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndepDenom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierSectionsFlatBaseChangeLinearlyDisjointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.GaussPt

/- English proof (translation)
Introduce and unpack `v ⟨d, hd, hv⟩`. Prove the components needed by the constructor for the conclusion. Introduce `hW`. Establish `h₁ : ∃ d' : D, d' ≠ 0 ∧ c d' * (c d * v) ∈ spanBy c (θ '' W)`. Use `spanBy_induction (P := fun v => ∃ d' : D, d' ≠ 0 ∧ c d' * v ∈ spanBy c (θ '' W)) ⟨1, one_ne_zero, by simpa using spanBy_zero _⟩ ?_ ?_ ?_ hv` and prove the remaining obligations.

Introduce and unpack `_ ⟨u, rfl⟩`. Take `⟨d, hd, h⟩` from `den u`. Conclude with `⟨d, hd, subset_spanBy _ _ h⟩`. Introduce and unpack `u v ⟨d, hd, h⟩ ⟨e, he, h'⟩`. Use `⟨d * e, mul_ne_zero hd he, ?_⟩` and prove the remaining obligations.

Use `spanBy_add (spanBy_smul e h) (spanBy_smul d h')` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `r u ⟨d, hd, h⟩`.

Use `⟨d, hd, ?_⟩` and prove the remaining obligations. Use `spanBy_smul r h` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨d', hd', h₂⟩` from `h₁`.

Take `⟨n, e, he⟩` from `IsDiscreteValuationRing.associated_pow_irreducible (mul_ne_zero hd' hd) hϖ`. Establish `h₃ : c (ϖ ^ n) * v ∈ spanBy c (θ '' W)`. Use `spanBy_smul (e : D) h₂` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← he, map_mul, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h₄ : ∀ n : ℕ, c (ϖ ^ n) * v ∈ spanBy c (θ '' W) → v ∈ spanBy c (θ '' W)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`.

Consider the case `succ n ih`. Introduce `h`. Use `ih (key _ (hsm _ _ hW) ?_)` and prove the remaining obligations. Rewrite `h` using `[pow_succ', map_mul, _root_.mul_assoc]`. Then use the resulting hypothesis. Conclude with `⟨1, fun h => (mem_maximalIdeal _).1 h isUnit_one, by simpa using h₄ n h₃⟩`.

Introduce and unpack `⟨s, hs, h⟩`. Establish `h₁ : c s * v ∈ W'` using `spanBy_induction (P := (· ∈ W')) h0 (by rintro _ ⟨u, hu, rfl⟩; exact hθ u hu) (fun u v hu hv => hadd u hu v hv) (fun r u hu => hsm r u hu) h`. Take `⟨s, rfl⟩` from `IsLocalRing.notMem_maximalIdeal.1 hs`. Use `hsm (s⁻¹ : Dˣ) _ h₁` as an intermediate fact. Rewrite `this` using `[← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]`. Then use the resulting hypothesis.
-/
theorem gaussAt_of_dvd {D F F' : Type} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [Field F]
    [Field F'] {c : D →+* F'} {θ : F →+* F'} {ϖ : D} (hϖ : Irreducible ϖ) {W : Set F}
    {W' : Set F'} (h0 : (0 : F') ∈ W') (hadd : ∀ u ∈ W', ∀ v ∈ W', u + v ∈ W')
    (hsm : ∀ r, ∀ u ∈ W', c r * u ∈ W') (hθ : ∀ u ∈ W, θ u ∈ W')
    (den : ∀ u : F, ∃ d : D, d ≠ 0 ∧ c d * θ u ∈ θ '' W)
    (key : ∀ w ∈ W', c ϖ * w ∈ spanBy c (θ '' W) → w ∈ spanBy c (θ '' W)) :
    GaussAt c (maximalIdeal D) θ W W' := by
  rintro v ⟨d, hd, hv⟩
  constructor
  · intro hW
    have h₁ : ∃ d' : D, d' ≠ 0 ∧ c d' * (c d * v) ∈ spanBy c (θ '' W) := by
      refine spanBy_induction (P := fun v => ∃ d' : D, d' ≠ 0 ∧ c d' * v ∈ spanBy c (θ '' W))
        ⟨1, one_ne_zero, by simpa using spanBy_zero _⟩ ?_ ?_ ?_ hv
      · rintro _ ⟨u, rfl⟩
        obtain ⟨d, hd, h⟩ := den u
        exact ⟨d, hd, subset_spanBy _ _ h⟩
      · rintro u v ⟨d, hd, h⟩ ⟨e, he, h'⟩
        refine ⟨d * e, mul_ne_zero hd he, ?_⟩
        have := spanBy_add (spanBy_smul e h) (spanBy_smul d h')
        convert this using 1
        rw [map_mul]; ring
      · rintro r u ⟨d, hd, h⟩
        refine ⟨d, hd, ?_⟩
        have := spanBy_smul r h
        convert this using 1
        ring
    obtain ⟨d', hd', h₂⟩ := h₁
    obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible (mul_ne_zero hd' hd) hϖ
    have h₃ : c (ϖ ^ n) * v ∈ spanBy c (θ '' W) := by
      have := spanBy_smul (e : D) h₂
      convert this using 1
      rw [← he, map_mul, map_mul]; ring
    have h₄ : ∀ n : ℕ, c (ϖ ^ n) * v ∈ spanBy c (θ '' W) → v ∈ spanBy c (θ '' W) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro h
        refine ih (key _ (hsm _ _ hW) ?_)
        rwa [pow_succ', map_mul, _root_.mul_assoc] at h
    exact ⟨1, fun h => (mem_maximalIdeal _).1 h isUnit_one, by simpa using h₄ n h₃⟩
  · rintro ⟨s, hs, h⟩
    have h₁ : c s * v ∈ W' :=
      spanBy_induction (P := (· ∈ W')) h0 (by rintro _ ⟨u, hu, rfl⟩; exact hθ u hu)
        (fun u v hu hv => hadd u hu v hv) (fun r u hu => hsm r u hu) h
    obtain ⟨s, rfl⟩ := IsLocalRing.notMem_maximalIdeal.1 hs
    have := hsm (s⁻¹ : Dˣ) _ h₁
    rwa [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul] at this

/- English proof (translation)
Take `⟨a, rfl⟩` from `hu`. Use `letI : Algebra Γ(X, U) (X.presheaf.stalk y) := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : U)`. Establish `hl : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal` using `hU.isLocalization_stalk ⟨y, hy⟩`. Take `⟨⟨s, g⟩, h⟩` from `IsLocalization.surj (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl a`. Use `⟨g, s, ⟨_, IsLocalization.map_units (X.presheaf.stalk y) g, algebraMap_germ hy _⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← algebraMap_germ hy, ← algebraMap_germ hy, ← map_mul, mul_comm]`. Conclude with `congrArg _ h`.
-/
theorem exists_den {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) {y : X} (hy : y ∈ U)
    {u : X.functionField} (hu : RegAt y u) :
    ∃ g s : Γ(X, U), UnitAt y (fnOf U (gen_mem hy) g) ∧ fnOf U (gen_mem hy) g * u = fnOf U (gen_mem hy) s := by
  obtain ⟨a, rfl⟩ := hu
  letI : Algebra Γ(X, U) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : U)
  have hl : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨⟨s, g⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl a
  refine ⟨g, s, ⟨_, IsLocalization.map_units (X.presheaf.stalk y) g, algebraMap_germ hy _⟩, ?_⟩
  rw [← algebraMap_germ hy, ← algebraMap_germ hy, ← map_mul, mul_comm]
  exact congrArg _ h

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible D`. Use `set y' := i (genericPoint Z) with hy'`. Establish `hc : p' y' = closedPoint D` using `(DvrModel.mem_range_special hs y').1 ⟨_, rfl⟩`. Establish `hcst : θ.comp (GlobalTheory.Desc.cst p) = (GlobalTheory.Desc.cst p').comp a` using `comp_cst hθ (by rw [Category.id_comp]; exact hp.w)`. Establish `hcst' : ∀ r, θ (GlobalTheory.Desc.cst p r) = GlobalTheory.Desc.cst p' (a r)` using `fun r => RingHom.congr_fun hcst r`.

Establish `hϖ0 : GlobalTheory.Desc.cst p' ϖ ≠ 0` using `(map_ne_zero_iff _ (cst_injective p')).2 hϖ.ne_zero`. Use `gaussAt_of_dvd hϖ (regAt_zero _) (fun u hu v hv => RegAt.add hu hv) (fun r u hu => (regAt_cst p' y' r).mul hu) (fun u hu => regAt_theta hθ y' hu) ?_ ?_` and prove the remaining obligations. Introduce `u`. Take `⟨n, g, hg, rfl⟩` from `IsFractionRing.div_surjective (A := X.presheaf.stalk (π y')) u`. Take `⟨τ, hτ⟩` from `regAt_cst p (π y') t`.

Establish `hτu : ¬ IsUnit τ` using `fun h => by`. Use `unitAt_theta hθ y' ⟨τ, h, hτ⟩` as an intermediate fact. Rewrite `this` using `[hcst', unitAt_cst_iff, hc]`. Conclude with `this ht'`. Take `⟨m, k, hk⟩` from `dvd_pow_of_dim hd (nonZeroDivisors.ne_zero hg) hτu`.

Establish `hg0 : algebraMap _ X.functionField g ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hg`. Use `⟨a t ^ m, pow_ne_zero _ ht, algebraMap _ _ (k * n), ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, ← hcst', ← map_pow, ← map_mul, ← hτ, ← map_pow, hk]`. Use `congr 1`. Rewrite using `[map_mul, map_mul]`.

Clear the denominators using the available nonvanishing facts. Introduce `w hw hb`. Take `⟨U, hU, hyU, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (x := π y') trivial`. Establish `: IsAffineHom π` using `MorphismProperty.of_isPullback hp.flip inferInstance`. Establish `hU' : IsAffineOpen (π ⁻¹ᵁ U)` using `hU.preimage π`.

Establish `hyU' : y' ∈ π ⁻¹ᵁ U` using `hyU`. Establish `hres : ∀ r, fnOf (π ⁻¹ᵁ U) (gen_mem hyU') (resG X' le_top (p'.appTop ((Scheme.ΓSpecIso (CommRingCat.of D)).inv r))) = GlobalTheory.Desc.cst p' r` using `fun r => fnOf_resG _ _ _`. Establish `h₁ : ∃ g, UnitAt (π y') g ∧ θ g * (GlobalTheory.Desc.cst p' ϖ * w) ∈ (fnOf (π ⁻¹ᵁ U) (gen_mem hyU')).range`. Use `spanBy_induction (P := fun v => ∃ g, UnitAt (π y') g ∧ θ g * v ∈ (fnOf (π ⁻¹ᵁ U) (gen_mem hyU')).range) ⟨1, unitAt_one _, by simp⟩ ?_ ?_ ?_ hb` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`.

Take `⟨g, s, h₁, h₂⟩` from `exists_den hU hyU hu`. Use `⟨_, h₁, π.app U s, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, h₂, theta_fnOf hθ]`. Introduce and unpack `u v ⟨g, hg, h⟩ ⟨g', hg', h'⟩`. Take `⟨k, s, h₁, h₂⟩` from `exists_den hU hyU hg.regAt`.

Take `⟨k', s', h₁', h₂'⟩` from `exists_den hU hyU hg'.regAt`. Use `⟨_, (h₁.mul hg).mul (h₁'.mul hg'), ?_⟩` and prove the remaining obligations. Establish `m : ∀ s, θ (fnOf U (gen_mem hyU) s) ∈ (fnOf (π ⁻¹ᵁ U) (gen_mem hyU')).range` using `fun s => ⟨π.app U s, (theta_fnOf hθ _ _ _ _).symm⟩`. Use `add_mem (mul_mem (mul_mem (m k) h) (m s')) (mul_mem (mul_mem (m k') h') (m s))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[← h₂, ← h₂']`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `r u ⟨g, hg, h⟩`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations.

Use `mul_mem (⟨_, hres r⟩ : GlobalTheory.Desc.cst p' r ∈ (fnOf (π ⁻¹ᵁ U) (gen_mem hyU')).range) h` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨g, hg, σ, hσ⟩` from `h₁`. Establish `hz : y' ∉ X'.basicOpen σ`.

Rewrite using `[← unitAt_fnOf_iff hyU' (gen_mem hyU'), hσ]`. Establish `h₂ : ZeroAt y' (GlobalTheory.Desc.cst p' ϖ)` using `zeroAt_iff.2 ⟨regAt_cst _ _ _, by`. Rewrite using `[unitAt_cst_iff, hc, not_not]`. Conclude with `hϖ.not_isUnit⟩`. Establish `h₃` using `h₂.mul ((regAt_theta hθ y' hg.regAt).mul hw)`.

Rewrite using `[mul_left_comm]`. Conclude with `(zeroAt_iff.1 h₃).2`. Take `⟨σ', hσ'⟩` from `(PrimeSection.dvd_iff_notMem_basicOpen (DvrModel.notMem_basicOpen_iff_specializes hϖ hs) (DvrModel.prime_res_generic hϖ hs) hU' hyU' σ).2 hz`. Establish `h₄ : θ g * w = fnOf (π ⁻¹ᵁ U) (gen_mem hyU') σ'`. Apply `mul_left_cancel₀ hϖ0` to reduce the goal to its premises.

Rewrite using `[mul_left_comm, ← hσ, hσ', map_mul, ← hres]`. Establish `h₅` using `GlobalTheory.Desc.fnOf_preimage_mem_spanBy T D a X X' p p' π θ hp hθ U (gen_mem hyU) (gen_mem hyU') hU σ'`. Establish `h₆ : w = θ g⁻¹ * fnOf (π ⁻¹ᵁ U) (gen_mem hyU') σ'`. Rewrite using `[← h₄, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ hg.ne_zero, map_one, _root_.one_mul]`. Rewrite using `[h₆]`.

Use `spanBy_induction (P := fun v => θ g⁻¹ * v ∈ spanBy (GlobalTheory.Desc.cst p') (θ '' regSet (π y'))) (by simpa using spanBy_zero _) ?_ ?_ ?_ h₅` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨s, rfl⟩, rfl⟩`. Conclude with `subset_spanBy _ _ ⟨_, hg.inv.regAt.mul (regAt_fnOf hyU _ s), map_mul _ _ _⟩`. Introduce `u v hu hv`. Rewrite using `[mul_add]`.

Conclude with `spanBy_add hu hv`. Introduce `r u hu`. Rewrite using `[mul_left_comm]`. Conclude with `spanBy_smul r hu`.
-/
theorem gaussAt_pullback {T D : Type} [CommRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    {a : T →+* D} {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] {p : X ⟶ Sp T} {p' : X' ⟶ Sp D}
    [Flat p'] {π : X' ⟶ X} {θ : X.functionField →+* X'.functionField} (hp : IsPullback π p' p (spMap a))
    (hθ : PFF (𝟙 _) π θ) {Z : Scheme.{0}} [IsIntegral Z] {i : Z ⟶ X'} {s : Z ⟶ Sp (ResidueField D)}
    (hs : IsPullback i s p' (spMap (residue D))) (t : T) (ht : a t ≠ 0) (ht' : a t ∈ maximalIdeal D)
    (hd : ringKrullDim (X.presheaf.stalk (π (i (genericPoint Z)))) ≤ 1) :
    GaussAt (GlobalTheory.Desc.cst p') (maximalIdeal D) θ (regSet (π (i (genericPoint Z))))
      (regSet (i (genericPoint Z))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D
  set y' := i (genericPoint Z) with hy'
  have hc : p' y' = closedPoint D := (DvrModel.mem_range_special hs y').1 ⟨_, rfl⟩
  have hcst : θ.comp (GlobalTheory.Desc.cst p) = (GlobalTheory.Desc.cst p').comp a :=
    comp_cst hθ (by rw [Category.id_comp]; exact hp.w)
  have hcst' : ∀ r, θ (GlobalTheory.Desc.cst p r) = GlobalTheory.Desc.cst p' (a r) := fun r => RingHom.congr_fun hcst r
  have hϖ0 : GlobalTheory.Desc.cst p' ϖ ≠ 0 := (map_ne_zero_iff _ (cst_injective p')).2 hϖ.ne_zero
  refine gaussAt_of_dvd hϖ (regAt_zero _) (fun u hu v hv => RegAt.add hu hv)
    (fun r u hu => (regAt_cst p' y' r).mul hu) (fun u hu => regAt_theta hθ y' hu) ?_ ?_
  · intro u
    obtain ⟨n, g, hg, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (π y')) u
    obtain ⟨τ, hτ⟩ := regAt_cst p (π y') t
    have hτu : ¬ IsUnit τ := fun h => by
      have := unitAt_theta hθ y' ⟨τ, h, hτ⟩
      rw [hcst', unitAt_cst_iff, hc] at this
      exact this ht'
    obtain ⟨m, k, hk⟩ := dvd_pow_of_dim hd (nonZeroDivisors.ne_zero hg) hτu
    have hg0 : algebraMap _ X.functionField g ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hg
    refine ⟨a t ^ m, pow_ne_zero _ ht, algebraMap _ _ (k * n), ⟨_, rfl⟩, ?_⟩
    rw [map_pow, ← hcst', ← map_pow, ← map_mul, ← hτ, ← map_pow, hk]
    congr 1
    rw [map_mul, map_mul]
    field_simp
  · intro w hw hb
    obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := π y') trivial
    have : IsAffineHom π := MorphismProperty.of_isPullback hp.flip inferInstance
    have hU' : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
    have hyU' : y' ∈ π ⁻¹ᵁ U := hyU
    have hres : ∀ r, fnOf (π ⁻¹ᵁ U) (gen_mem hyU') (resG X' le_top
        (p'.appTop ((Scheme.ΓSpecIso (CommRingCat.of D)).inv r))) = GlobalTheory.Desc.cst p' r :=
      fun r => fnOf_resG _ _ _
    have h₁ : ∃ g, UnitAt (π y') g ∧ θ g * (GlobalTheory.Desc.cst p' ϖ * w) ∈ (fnOf (π ⁻¹ᵁ U) (gen_mem hyU')).range := by
      refine spanBy_induction
        (P := fun v => ∃ g, UnitAt (π y') g ∧ θ g * v ∈ (fnOf (π ⁻¹ᵁ U) (gen_mem hyU')).range)
        ⟨1, unitAt_one _, by simp⟩ ?_ ?_ ?_ hb
      · rintro _ ⟨u, hu, rfl⟩
        obtain ⟨g, s, h₁, h₂⟩ := exists_den hU hyU hu
        refine ⟨_, h₁, π.app U s, ?_⟩
        rw [← map_mul, h₂, theta_fnOf hθ]
      · rintro u v ⟨g, hg, h⟩ ⟨g', hg', h'⟩
        obtain ⟨k, s, h₁, h₂⟩ := exists_den hU hyU hg.regAt
        obtain ⟨k', s', h₁', h₂'⟩ := exists_den hU hyU hg'.regAt
        refine ⟨_, (h₁.mul hg).mul (h₁'.mul hg'), ?_⟩
        have m : ∀ s, θ (fnOf U (gen_mem hyU) s) ∈ (fnOf (π ⁻¹ᵁ U) (gen_mem hyU')).range :=
          fun s => ⟨π.app U s, (theta_fnOf hθ _ _ _ _).symm⟩
        have := add_mem (mul_mem (mul_mem (m k) h) (m s')) (mul_mem (mul_mem (m k') h') (m s))
        convert this using 1
        rw [← h₂, ← h₂']
        simp only [map_mul]
        ring
      · rintro r u ⟨g, hg, h⟩
        refine ⟨g, hg, ?_⟩
        have := mul_mem (⟨_, hres r⟩ : GlobalTheory.Desc.cst p' r ∈ (fnOf (π ⁻¹ᵁ U) (gen_mem hyU')).range) h
        convert this using 1
        ring
    obtain ⟨g, hg, σ, hσ⟩ := h₁
    have hz : y' ∉ X'.basicOpen σ := by
      rw [← unitAt_fnOf_iff hyU' (gen_mem hyU'), hσ]
      have h₂ : ZeroAt y' (GlobalTheory.Desc.cst p' ϖ) := zeroAt_iff.2 ⟨regAt_cst _ _ _, by
        rw [unitAt_cst_iff, hc, not_not]
        exact hϖ.not_isUnit⟩
      have h₃ := h₂.mul ((regAt_theta hθ y' hg.regAt).mul hw)
      rw [mul_left_comm]
      exact (zeroAt_iff.1 h₃).2
    obtain ⟨σ', hσ'⟩ := (PrimeSection.dvd_iff_notMem_basicOpen
      (DvrModel.notMem_basicOpen_iff_specializes hϖ hs) (DvrModel.prime_res_generic hϖ hs) hU' hyU' σ).2 hz
    have h₄ : θ g * w = fnOf (π ⁻¹ᵁ U) (gen_mem hyU') σ' := by
      apply mul_left_cancel₀ hϖ0
      rw [mul_left_comm, ← hσ, hσ', map_mul, ← hres]
    have h₅ := GlobalTheory.Desc.fnOf_preimage_mem_spanBy T D a X X' p p' π θ hp hθ U (gen_mem hyU) (gen_mem hyU') hU σ'
    have h₆ : w = θ g⁻¹ * fnOf (π ⁻¹ᵁ U) (gen_mem hyU') σ' := by
      rw [← h₄, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ hg.ne_zero, map_one, _root_.one_mul]
    rw [h₆]
    refine spanBy_induction
      (P := fun v => θ g⁻¹ * v ∈ spanBy (GlobalTheory.Desc.cst p') (θ '' regSet (π y')))
      (by simpa using spanBy_zero _) ?_ ?_ ?_ h₅
    · rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      exact subset_spanBy _ _ ⟨_, hg.inv.regAt.mul (regAt_fnOf hyU _ s), map_mul _ _ _⟩
    · intro u v hu hv
      rw [mul_add]
      exact spanBy_add hu hv
    · intro r u hu
      rw [mul_left_comm]
      exact spanBy_smul r hu

/- English proof (translation)
Use `hG.separated` as an intermediate fact. Use `(GlobalTheory.T.cartierSections_flat_baseChange_linearlyDisjoint T D a ha G.left X' X' G.hom p' (𝟙 _) π θ hG.quasiCompact inferInstance (by rwa [Category.id_comp]) hθ 0 0 fun v g hg => ?_).1` and prove the remaining obligations. Establish `h₁ : UnitAt (π v) ((g : G.left.functionField) / (1 : G.left.functionFieldˣ))` using `germOf_eq_iff.1 (show germOf (π v) 1 = germOf (π v) g from hg)`. Establish `h₂` using `unitAt_theta hθ v h₁`. Use `show germOf v 1 = germOf v _ from germOf_eq_iff.2 ?_` and prove the remaining obligations.

Simplify using `using h₂`.
-/
theorem linDisj_pullback {T D : Type} [CommRing T] [CommRing D] {a : T →+* D} (ha : a.Flat)
    {G : Over (Sp T)} [GrpObj G] [IsIntegral G.left] (hG : IsSemiAbelian G) {X' : Scheme.{0}}
    [IsIntegral X'] {p' : X' ⟶ Sp D} {π : X' ⟶ G.left} {θ : G.left.functionField →+* X'.functionField}
    (hp : IsPullback π p' G.hom (spMap a)) (hθ : PFF (𝟙 _) π θ) :
    LinDisj (GlobalTheory.Desc.cst G.hom) (GlobalTheory.Desc.cst p') θ := by
  have := hG.separated
  refine (GlobalTheory.T.cartierSections_flat_baseChange_linearlyDisjoint T D a ha G.left X' X' G.hom p' (𝟙 _) π θ hG.quasiCompact inferInstance
    (by rwa [Category.id_comp]) hθ 0 0 fun v g hg => ?_).1
  have h₁ : UnitAt (π v) ((g : G.left.functionField) / (1 : G.left.functionFieldˣ)) :=
    germOf_eq_iff.1 (show germOf (π v) 1 = germOf (π v) g from hg)
  have h₂ := unitAt_theta hθ v h₁
  refine show germOf v 1 = germOf v _ from germOf_eq_iff.2 ?_
  simpa using h₂

/- English proof (translation)
Introduce and unpack `σ x z ⟨hdim, hf⟩`. Use `set q := (σ.C x).G.hom z with hq`. Use `set p := spMap (σ.ρ x) q with hp`. Establish `: q.asIdeal.IsPrime` using `q.2`. Use `(σ.C x).semi.smooth` as an intermediate fact.

Use `(σ.C x).semi.geomConnected` as an intermediate fact. Use `(σ.C p).semi.smooth` as an intermediate fact. Establish `hcen : spMap (σ.ρ p) (closedPoint (σ.C p).R) = p`. Rewrite using `[← σ.hρ]`. Conclude with `(σ.C p).centre`.

Take `⟨Ω, _, u, u', hu, hu', huu⟩` from `exists_common_field (σ.ρ x) (σ.ρ p) q (closedPoint (σ.C p).R) hcen.symm`. Take `⟨E, _, _, _, a, b, v, H, _, _, πa, πb, θa, θb, ha, hb, hab, hv, hva, hvb, hm, hH, ⟨hπa, -⟩, ⟨hπb, -⟩, hθa, hθb, hθ⟩` from `GlobalTheory.T.abelianSchemeDescentData_charts_common σ x p Ω u u' hu' huu`. Use `hH.smooth` as an intermediate fact. Use `hH.geomConnected` as an intermediate fact. Establish `hca : (maximalIdeal E).comap a = q.asIdeal`.

Rewrite using `[← hv, RingHom.comap_ker, hva, hu]`. Establish `hcb : (maximalIdeal E).comap b = maximalIdeal _`. Rewrite using `[← hv, RingHom.comap_ker, hvb]`. Conclude with `hu'`. Establish `hf0 : σ.ρ x σ.f ≠ 0` using `(map_ne_zero_iff _ (injective_of_flat (σ.flat x))).2 σ.hf`.

Establish `hf0' : σ.ρ p σ.f ≠ 0` using `(map_ne_zero_iff _ (injective_of_flat (σ.flat p))).2 σ.hf`. Establish `hq0 : q.asIdeal ≠ ⊥` using `fun e => hf0 (by rwa [e] at hf)`. Establish `hfE : a (σ.ρ x σ.f) ∈ maximalIdeal E` using `by rwa [← hca] at hf`. Establish `hfE' : b (σ.ρ p σ.f) ∈ maximalIdeal E`. Rewrite using `[show b (σ.ρ p σ.f) = a (σ.ρ x σ.f) from (RingHom.congr_fun hab _).symm]` and apply the resulting hypothesis.

Establish `hfp : σ.ρ p σ.f ∈ maximalIdeal (σ.C p).R` using `by rw [← hcb]; exact hfE'`. Establish `hz1 : Order.coheight z ≤ 1` using `(coheight_le_one_iff z).2 hdim.le`. Establish `: IsDiscreteValuationRing E` using `dvr_of_height (height_le_of_map a q.asIdeal (height_le_one q (coheight_le_one_of_flat _ z hz1)) hca (hu ▸ hm)) fun e => (map_ne_zero_iff _ (injective_of_flat ha)).2 hf0 (by rwa [e] at hfE)`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible E`. Establish `hs` using `IsPullback.of_hasPullback H.hom (spMap (residue E))`.

Establish `: IsIntegral (pullback H.hom (spMap (residue E)))` using `isIntegral_pullback_of_smooth _ _`. Use `set y := pullback.fst H.hom (spMap (residue E)) (genericPoint _) with hy`. Establish `hyc : H.hom y = closedPoint E` using `(DvrModel.mem_range_special hs y).1 ⟨_, rfl⟩`. Establish `hy1 : Order.coheight y ≤ 1`. Use `(DvrModel.isDiscreteValuationRing_stalk_generic hϖ hs).1` as an intermediate fact.

Conclude with `(coheight_le_one_iff y).2 (IsDiscreteValuationRing.ringKrullDim_eq_one _).le`. Establish `: Flat (spMap a)` using `(HasRingHomProperty.Spec_iff (P := @Flat)).2 ha`. Establish `: Flat (spMap b)` using `(HasRingHomProperty.Spec_iff (P := @Flat)).2 hb`. Establish `: Flat πa` using `MorphismProperty.of_isPullback hπa.flip inferInstance`. Establish `: Flat πb` using `MorphismProperty.of_isPullback hπb.flip inferInstance`.

Establish `hya : (σ.C x).G.hom (πa y) = q`. Rewrite using `[← Scheme.Hom.comp_apply, hπa.w, Scheme.Hom.comp_apply, hyc]`. Conclude with `PrimeSpectrum.ext hca`. Establish `hyb : (σ.C p).G.hom (πb y) = closedPoint _`. Rewrite using `[← Scheme.Hom.comp_apply, hπb.w, Scheme.Hom.comp_apply, hyc]`.

Conclude with `PrimeSpectrum.ext hcb`. Establish `hyz : πa y = z` using `eq_of_coheight_le_one (σ.C x).G.hom hya (by rwa [hya]) (coheight_le_one_of_flat _ y hy1) hz1`. Establish `hz'` using `coheight_le_one_of_flat πb y hy1`. Establish `hm0 : maximalIdeal (σ.C p).R ≠ ⊥` using `fun e => hf0' (by rwa [e] at hfp)`. Establish `hV : Vert (σ.C p).G.hom (σ.ρ p σ.f) (πb y)` using `⟨ringKrullDim_eq_one (σ.C p).G.hom (by rw [hyb]; exact hm0) hz', by rw [hyb]; exact hfp⟩`.

Establish `: IsDiscreteValuationRing (σ.C p).R` using `dvr_of_height (height_le_one (closedPoint (σ.C p).R : Sp (σ.C p).R) (hyb ▸ coheight_le_one_of_flat (σ.C p).G.hom _ hz')) hm0`. Establish `hp1 : p.asIdeal.height = 1`. Establish `: Flat (spMap (σ.ρ x))` using `(HasRingHomProperty.Spec_iff (P := @Flat)).2 (σ.flat x)`. Establish `: p.asIdeal.IsPrime` using `p.2`. Use `le_antisymm (height_le_one p (coheight_le_one_of_flat _ q (coheight_le_one_of_flat _ z hz1))) (Order.one_le_iff_ne_zero.2 fun e => σ.hf ?_)` and prove the remaining obligations.

Establish `h₁ : σ.f ∈ p.asIdeal` using `hf`. Rewrite `h₁` using `[Ideal.height_eq_zero_iff_eq_bot.1 e]`. Then use the resulting hypothesis. Establish `g₁` using `GlobalTheory.T.gauss_at_height_one_vertical_point σ p (πb y) hp1 hV`. Establish `g₂` using `gaussAt_pullback hπb hθb hs (σ.ρ p σ.f) ((map_ne_zero_iff _ (injective_of_flat hb)).2 hf0') hfE' hV.1.le`. Establish `g₃` using `GlobalTheory.Desc.GaussComp.gaussAt_comp _ E _ _ _ b _ _ (σ.θ p) θb (maximalIdeal _) (maximalIdeal E) (σ.W p) (regSet (πb y)) (regSet y) (injective_of_flat hb) (cst_injective (σ.C p).G.hom) (fun s hs h => hs (by rw [← hcb]; exact h)) (comp_cst hθb (by rw [Category.id_comp]; exact …`.

Rewrite `g₃` using `[← hθ]`. Establish `ra : θa ⁻¹' regSet y = regSet z` using `by rw [preimage_regSet hθa, hyz]`. Establish `rb` using `preimage_regSet hθb y`. Prove the components needed by the constructor for the conclusion. Use `σ.ab.proper` as an intermediate fact.

Conclude with `GlobalTheory.Desc.GaussDown.gaussAt_descent σ.R _ E _ _ _ (σ.ρ x) a σ.c₀ _ _ (σ.θ x) θa q.asIdeal _ _ _ ha (cst_injective (σ.C x).G.hom) (fun s hs => notMem_maximalIdeal.1 fun h => hs (by rw [← hca]; exact h)) (fun t ht => by rwa [← hca] at ht) (comp_cst (σ.hθ x) (σ.cart x).w) (c …`. Rewrite using `[← ra, ← Set.preimage_comp, ← RingHom.coe_comp, hθ, RingHom.coe_comp, Set.preimage_comp, rb]`. Use extensionality with `w`. Use `⟨fun hw z' hz' => ?_, fun hw => hw _ hV⟩` and prove the remaining obligations. Establish `hd : ∃ d : (σ.C p).R, d ≠ 0 ∧ GlobalTheory.Desc.cst (σ.C p).G.hom d * σ.θ p w ∈ spanBy (GlobalTheory.Desc.cst (σ.C p).G.hom) (Set.range (σ.θ p))` using `⟨1, one_ne_zero, spanBy_smul _ (subset_spanBy _ _ ⟨w, rfl⟩)⟩`.

Conclude with `(GlobalTheory.T.gauss_at_height_one_vertical_point σ p z' hp1 hz' _ hd).2 ((g₁ _ hd).1 hw)`.
-/
theorem gaussAt_vert : ∀ (σ : Setup) (x : Sp σ.R) (z : (σ.C x).G.left), Vert (σ.C x).G.hom (σ.ρ x σ.f) z → GaussAt (GlobalTheory.Desc.cst (σ.C x).G.hom) ((σ.C x).G.hom z).asIdeal (σ.θ x) (σ.W (spMap (σ.ρ x) ((σ.C x).G.hom z))) (regSet z) ∧ (σ.θ x) ⁻¹' (regSet z) = σ.W (spMap (σ.ρ x) ((σ.C x).G.hom z)) := by
  rintro σ x z ⟨hdim, hf⟩
  set q := (σ.C x).G.hom z with hq
  set p := spMap (σ.ρ x) q with hp
  have : q.asIdeal.IsPrime := q.2
  have := (σ.C x).semi.smooth
  have := (σ.C x).semi.geomConnected
  have := (σ.C p).semi.smooth
  have hcen : spMap (σ.ρ p) (closedPoint (σ.C p).R) = p := by
    rw [← σ.hρ]; exact (σ.C p).centre
  obtain ⟨Ω, _, u, u', hu, hu', huu⟩ :=
    exists_common_field (σ.ρ x) (σ.ρ p) q (closedPoint (σ.C p).R) hcen.symm
  obtain ⟨E, _, _, _, a, b, v, H, _, _, πa, πb, θa, θb, ha, hb, hab, hv, hva, hvb, hm, hH, ⟨hπa, -⟩,
    ⟨hπb, -⟩, hθa, hθb, hθ⟩ := GlobalTheory.T.abelianSchemeDescentData_charts_common σ x p Ω u u' hu' huu
  have := hH.smooth
  have := hH.geomConnected
  have hca : (maximalIdeal E).comap a = q.asIdeal := by
    rw [← hv, RingHom.comap_ker, hva, hu]
  have hcb : (maximalIdeal E).comap b = maximalIdeal _ := by
    rw [← hv, RingHom.comap_ker, hvb]; exact hu'
  have hf0 : σ.ρ x σ.f ≠ 0 := (map_ne_zero_iff _ (injective_of_flat (σ.flat x))).2 σ.hf
  have hf0' : σ.ρ p σ.f ≠ 0 := (map_ne_zero_iff _ (injective_of_flat (σ.flat p))).2 σ.hf
  have hq0 : q.asIdeal ≠ ⊥ := fun e => hf0 (by rwa [e] at hf)
  have hfE : a (σ.ρ x σ.f) ∈ maximalIdeal E := by rwa [← hca] at hf
  have hfE' : b (σ.ρ p σ.f) ∈ maximalIdeal E := by
    rwa [show b (σ.ρ p σ.f) = a (σ.ρ x σ.f) from (RingHom.congr_fun hab _).symm]
  have hfp : σ.ρ p σ.f ∈ maximalIdeal (σ.C p).R := by rw [← hcb]; exact hfE'
  have hz1 : Order.coheight z ≤ 1 := (coheight_le_one_iff z).2 hdim.le
  have : IsDiscreteValuationRing E := dvr_of_height
    (height_le_of_map a q.asIdeal (height_le_one q (coheight_le_one_of_flat _ z hz1)) hca (hu ▸ hm))
    fun e => (map_ne_zero_iff _ (injective_of_flat ha)).2 hf0 (by rwa [e] at hfE)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E
  have hs := IsPullback.of_hasPullback H.hom (spMap (residue E))
  have : IsIntegral (pullback H.hom (spMap (residue E))) := isIntegral_pullback_of_smooth _ _
  set y := pullback.fst H.hom (spMap (residue E)) (genericPoint _) with hy
  have hyc : H.hom y = closedPoint E := (DvrModel.mem_range_special hs y).1 ⟨_, rfl⟩
  have hy1 : Order.coheight y ≤ 1 := by
    have := (DvrModel.isDiscreteValuationRing_stalk_generic hϖ hs).1
    exact (coheight_le_one_iff y).2 (IsDiscreteValuationRing.ringKrullDim_eq_one _).le
  have : Flat (spMap a) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 ha
  have : Flat (spMap b) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 hb
  have : Flat πa := MorphismProperty.of_isPullback hπa.flip inferInstance
  have : Flat πb := MorphismProperty.of_isPullback hπb.flip inferInstance
  have hya : (σ.C x).G.hom (πa y) = q := by
    rw [← Scheme.Hom.comp_apply, hπa.w, Scheme.Hom.comp_apply, hyc]
    exact PrimeSpectrum.ext hca
  have hyb : (σ.C p).G.hom (πb y) = closedPoint _ := by
    rw [← Scheme.Hom.comp_apply, hπb.w, Scheme.Hom.comp_apply, hyc]
    exact PrimeSpectrum.ext hcb
  have hyz : πa y = z := eq_of_coheight_le_one (σ.C x).G.hom hya (by rwa [hya])
    (coheight_le_one_of_flat _ y hy1) hz1
  have hz' := coheight_le_one_of_flat πb y hy1
  have hm0 : maximalIdeal (σ.C p).R ≠ ⊥ := fun e => hf0' (by rwa [e] at hfp)
  have hV : Vert (σ.C p).G.hom (σ.ρ p σ.f) (πb y) :=
    ⟨ringKrullDim_eq_one (σ.C p).G.hom (by rw [hyb]; exact hm0) hz', by rw [hyb]; exact hfp⟩
  have : IsDiscreteValuationRing (σ.C p).R := dvr_of_height
    (height_le_one (closedPoint (σ.C p).R : Sp (σ.C p).R)
      (hyb ▸ coheight_le_one_of_flat (σ.C p).G.hom _ hz')) hm0
  have hp1 : p.asIdeal.height = 1 := by
    have : Flat (spMap (σ.ρ x)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 (σ.flat x)
    have : p.asIdeal.IsPrime := p.2
    refine le_antisymm (height_le_one p (coheight_le_one_of_flat _ q (coheight_le_one_of_flat _ z hz1)))
      (Order.one_le_iff_ne_zero.2 fun e => σ.hf ?_)
    have h₁ : σ.f ∈ p.asIdeal := hf
    rwa [Ideal.height_eq_zero_iff_eq_bot.1 e] at h₁
  have g₁ := GlobalTheory.T.gauss_at_height_one_vertical_point σ p (πb y) hp1 hV
  have g₂ := gaussAt_pullback hπb hθb hs (σ.ρ p σ.f)
    ((map_ne_zero_iff _ (injective_of_flat hb)).2 hf0') hfE' hV.1.le
  have g₃ := GlobalTheory.Desc.GaussComp.gaussAt_comp _ E _ _ _ b _ _ (σ.θ p) θb (maximalIdeal _) (maximalIdeal E) (σ.W p)
    (regSet (πb y)) (regSet y) (injective_of_flat hb)
    (cst_injective (σ.C p).G.hom) (fun s hs h => hs (by rw [← hcb]; exact h))
    (comp_cst hθb (by rw [Category.id_comp]; exact hπb.w)) (linDisj_pullback hb (σ.C p).semi hπb hθb)
    (regAt_zero _) (fun u hu v hv => RegAt.add hu hv) (fun r u hu => (regAt_cst _ _ r).mul hu) g₁ g₂
  rw [← hθ] at g₃
  have ra : θa ⁻¹' regSet y = regSet z := by rw [preimage_regSet hθa, hyz]
  have rb := preimage_regSet hθb y
  constructor
  · have := σ.ab.proper
    exact GlobalTheory.Desc.GaussDown.gaussAt_descent σ.R _ E _ _ _ (σ.ρ x) a σ.c₀ _ _ (σ.θ x) θa q.asIdeal _ _ _ ha
      (cst_injective (σ.C x).G.hom)
      (fun s hs => notMem_maximalIdeal.1 fun h => hs (by rw [← hca]; exact h))
      (fun t ht => by rwa [← hca] at ht) (comp_cst (σ.hθ x) (σ.cart x).w)
      (comp_cst hθa (by rw [Category.id_comp]; exact hπa.w))
      (GlobalTheory.T.cartierSections_flat_baseChange_linearlyDisjoint σ.R _ (σ.ρ x) (σ.flat x) _ _ _ (σ.A.hom ≫ awayMap σ.f) (σ.C x).G.hom (σ.V x).ι (σ.φ x)
        (σ.θ x) inferInstance inferInstance (σ.cart x) (σ.hθ x) σ.D (σ.D₁ x) (σ.pull x)).1
      (linDisj_pullback ha (σ.C x).semi hπa hθa) ra g₃
  · rw [← ra, ← Set.preimage_comp, ← RingHom.coe_comp, hθ, RingHom.coe_comp, Set.preimage_comp, rb]
    ext w
    refine ⟨fun hw z' hz' => ?_, fun hw => hw _ hV⟩
    have hd : ∃ d : (σ.C p).R, d ≠ 0 ∧ GlobalTheory.Desc.cst (σ.C p).G.hom d * σ.θ p w ∈
        spanBy (GlobalTheory.Desc.cst (σ.C p).G.hom) (Set.range (σ.θ p)) :=
      ⟨1, one_ne_zero, spanBy_smul _ (subset_spanBy _ _ ⟨w, rfl⟩)⟩
    exact (GlobalTheory.T.gauss_at_height_one_vertical_point σ p z' hp1 hz' _ hd).2 ((g₁ _ hd).1 hw)

end GlobalTheory.Desc.GaussPt
