import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreGenericPointDvrOfPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeEqSpanOfCoheightLeOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpenGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VerticalUnit

/- English proof (translation)
Take `⟨u, rfl⟩` from `hs`. Use `⟨u ^ n, ?_⟩` and prove the remaining obligations. Use `congrArg Units.val (map_zpow (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom) u n)` as an intermediate fact. Rewrite `this` using `[Units.val_zpow_eq_zpow_val, Units.coe_map]`. Conclude with `this`.
-/
theorem UnitAt.zpow {X : Scheme.{0}} [IsIntegral X] {x : X} {s : X.functionField} (hs : UnitAt x s) (n : ℤ) :
    UnitAt x (s ^ n) := by
  obtain ⟨u, rfl⟩ := hs
  refine ⟨u ^ n, ?_⟩
  have := congrArg Units.val (map_zpow (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom) u n)
  rw [Units.val_zpow_eq_zpow_val, Units.coe_map] at this
  exact this

/- English proof (translation)
The claim follows from `Finset.prod_induction f (UnitAt x) (fun _ _ => UnitAt.mul) ⟨1, by simp⟩ h`.
-/
theorem UnitAt.prod {X : Scheme.{0}} [IsIntegral X] {x : X} {ι : Type} (s : Finset ι) (f : ι → X.functionField)
    (h : ∀ b ∈ s, UnitAt x (f b)) : UnitAt x (∏ b ∈ s, f b) :=
  Finset.prod_induction f (UnitAt x) (fun _ _ => UnitAt.mul) ⟨1, by simp⟩ h

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hlt : x < y` using `lt_of_le_not_ge (show x ≤ y from h) fun h' => hne (h.antisymm (show x ⤳ y from h')).eq.symm`. Use `Order.coheight_add_one_le hlt` as an intermediate fact. Rewrite `this` using `[hx, hy]`. Conclude with `absurd this (by decide)`.
-/
theorem eq_of_specializes_of_coheight {X : Scheme.{0}} {x y : X} (h : y ⤳ x) (hx : Order.coheight x = 1)
    (hy : Order.coheight y = 1) : x = y := by
  by_contra hne
  have hlt : x < y := lt_of_le_not_ge (show x ≤ y from h) fun h' => hne (h.antisymm (show x ⤳ y from h')).eq.symm
  have := Order.coheight_add_one_le hlt
  rw [hx, hy] at this
  exact absurd this (by decide)

/- English proof (translation)
Rewrite using `[← Scheme.mem_basicOpen_top, constFn_top, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]`. Conclude with `hb`.
-/
theorem unitAt_constFn {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (q : X ⟶ Sp R) (x : X) (b : R)
    (hb : b ∉ (q x).asIdeal) : IsUnit (X.presheaf.germ ⊤ x trivial (constFn q ⊤ b)) := by
  rw [← Scheme.mem_basicOpen_top, constFn_top, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact hb

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ _ X _ _ q _ _ κ hκ I U t hcov ht0 htr hgen`. Establish `hgz : GeneralizingMap q` using `Flat.generalizingMap q`. Establish `hinj` using `IsFractionRing.injective R K`. Establish `hunit : ∀ (x : X) (b : R), b ∉ (q x).asIdeal → UnitAt x (κ (algebraMap R K b))` using `fun x b hb => ⟨(unitAt_constFn q x b hb).unit, by`. Rewrite using `[IsUnit.unit_spec, hκ]`.

Conclude with `X.presheaf.germ_stalkSpecializes_apply _ _ _⟩`. Set `S : Set X` to `{x | ∃ i, x ∈ U i ∧ UnitAt x (t i)}`. Establish `hS : IsOpen S`. Express the relevant statement in the definitionally equal form `IsOpen {x | ∃ i, x ∈ U i ∧ UnitAt x (t i)}`. Rewrite using `[Set.setOf_exists]`.

Conclude with `isOpen_iUnion fun i => (U i).isOpen.inter (isOpen_unitAt _)`. Establish `hg : genericPoint X ∈ S`. Set `p₀ : PrimeSpectrum R` to `⟨⊥, Ideal.bot_prime⟩`. Take `⟨y, -, hy⟩` from `hgz ((PrimeSpectrum.le_iff_specializes p₀ (q (genericPoint X))).1 bot_le)`. Conclude with `(genericPoint_specializes y).mem_open hS (hgen y (by rw [hy]))`.

Establish `hB` using `GlobalTheory.T.finite_coheight_one_notMem_open_genericPoint X S hS hg`. Use `set B : Set X := {x : X | Order.coheight x = 1 ∧ x ∉ S} with hBdef`. Establish `key : ∀ b ∈ B, ∃ π : R, Prime π ∧ (q b).asIdeal = Ideal.span {π} ∧ (∀ x : X, (q x).asIdeal = Ideal.span {π} → b ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk b) ∧ Irreducible (X.presheaf.germ ⊤ b trivial (constFn q ⊤ π))`. Introduce and unpack `b ⟨h1, hbS⟩`. Establish `hb0 : (q b).asIdeal ≠ ⊥` using `fun h => hbS (hgen b h)`.

Take `⟨π, hπ, hqb⟩` from `GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' R X q hgz b h1.le hb0`. Take `⟨ξ, -, hξ, hd, hirr⟩` from `GlobalTheory.T.exists_fibre_genericPoint_dvr_of_prime R X q π hπ`. Establish `hξ1 : Order.coheight ξ = 1`. Establish `e` using `IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk ξ)`. Rewrite `e` using `[ringKrullDim_stalk_eq_coheight]`.

Conclude with `e` after adjusting the coercions. Take `rfl : b = ξ` from `eq_of_specializes_of_coheight (hξ b hqb) h1 hξ1`. Conclude with `⟨π, hπ, hqb, hξ, hd, hirr⟩`. Use `choose! π hπ hqπ hsp hdvr hirr using key`. Establish `hstar : ∀ b ∈ B, ∀ x : X, Order.coheight x = 1 → π b ∈ (q x).asIdeal → x = b`.

Introduce `b hb x hx hmem`. Establish `hx0 : (q x).asIdeal ≠ ⊥` using `fun h => (hπ b hb).ne_zero (by rw [h, Ideal.mem_bot] at hmem; exact hmem)`. Take `⟨π', hπ', hqx⟩` from `GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' R X q hgz x hx.le hx0`. Establish `hdvd : π' ∣ π b` using `Ideal.mem_span_singleton.1 (hqx ▸ hmem)`. Establish `hq : (q x).asIdeal = Ideal.span {π b}` using `hqx.trans (Ideal.span_singleton_eq_span_singleton.2 (hπ'.associated_of_dvd (hπ b hb) hdvd))`.

Conclude with `eq_of_specializes_of_coheight (hsp b hb x hq) hx hb.1`. Establish `hne : ∀ b ∈ B, algebraMap R K (π b) ≠ 0` using `fun b hb => (map_ne_zero_iff _ hinj).2 (hπ b hb).ne_zero`. Establish `key2 : ∀ b ∈ B, ∃ (i : I) (n : ℤ), b ∈ U i ∧ UnitAt b (κ (algebraMap R K (π b)) ^ (-n) * t i)`. Introduce `b hb`. Take `⟨i, hi⟩` from `hcov b`.

Use `hdvr b hb` as an intermediate fact. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (hirr b hb) (ht0 i b hi)`. Establish `e : algebraMap _ X.functionField (X.presheaf.germ ⊤ b trivial (constFn q ⊤ (π b))) = κ (algebraMap R K (π b))`. Rewrite using `[hκ]`. Conclude with `X.presheaf.germ_stalkSpecializes_apply _ _ _`.

Establish `hπ' : κ (algebraMap R K (π b)) ≠ 0` using `(map_ne_zero κ).2 (hne b hb)`. Use `⟨i, n, hi, u, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, e, Units.smul_def, Algebra.smul_def, mul_left_comm, ← zpow_add₀ hπ', neg_add_cancel, zpow_zero, _root_.mul_one]`. Establish `: Nonempty I` using `⟨(hcov (genericPoint X)).choose⟩`. Use `choose! ib n hUi hunitb using key2`.

Set `F` to `hB.toFinset`. Set `a : Kˣ` to `∏ b ∈ F.attach, (Units.mk0 _ (hne b.1 (hB.mem_toFinset.1 b.2))) ^ (-n b.1)`. Establish `hκa : κ (a : K) = ∏ b ∈ F, κ (algebraMap R K (π b)) ^ (-n b)`. Simplify using `only [a, Units.coe_prod, map_prod, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0]`. Conclude with `Finset.prod_attach F (fun b => κ (algebraMap R K (π b)) ^ (-n b))`.

Use `⟨a, fun i x hx h1 => ?_⟩` and prove the remaining obligations. Rewrite using `[hκa]`. Establish `hother : ∀ b ∈ F, b ≠ x → UnitAt x (κ (algebraMap R K (π b)) ^ (-n b))` using `fun b hb hbx => (hunit x (π b) fun hm => hbx (hstar b (hB.mem_toFinset.1 hb) x h1 hm).symm).zpow _`. Distinguish the cases in `hxS : x ∈ S`. Take `⟨j, hj, hu⟩` from `hxS`.

Use `htr i j x _ hx hj ((UnitAt.prod F _ fun b hb => hother b hb ?_).mul hu)` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `(hB.mem_toFinset.1 hb).2 ⟨j, hj, hu⟩`. Establish `hxB : x ∈ B` using `⟨h1, hxS⟩`. Establish `hxF : x ∈ F` using `hB.mem_toFinset.2 hxB`.

Rewrite using `[← Finset.mul_prod_erase F (fun b => κ (algebraMap R K (π b)) ^ (-n b)) hxF]`. Use `htr i (ib x) x _ hx (hUi x hxB) ?_` and prove the remaining obligations. Rewrite using `[mul_comm (κ (algebraMap R K (π x)) ^ (-n x)), mul_assoc]`. Conclude with `(UnitAt.prod _ _ fun b hb => hother b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)).mul (hunitb x hxB)`.
-/
theorem exists_const_mul_unitAt_coheight_one : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (κ : K →+* X.functionField), (∀ b : R, κ (algebraMap R K b) = X.presheaf.germ ⊤ (genericPoint X) trivial (constFn q ⊤ b)) → ∀ (I : Type) (U : I → X.Opens) (t : I → X.functionField), (∀ x, ∃ i, x ∈ U i) → (∀ i x, x ∈ U i → t i ≠ 0) → (∀ i j x (s : X.functionField), x ∈ U i → x ∈ U j → GlobalTheory.VerticalUnit.UnitAt x (s * t j) → GlobalTheory.VerticalUnit.UnitAt x (s * t i)) → (∀ x, (q x).asIdeal = ⊥ → ∃ i, x ∈ U i ∧ GlobalTheory.VerticalUnit.UnitAt x (t i)) → ∃ a : Kˣ, ∀ i x, x ∈ U i → Order.coheight x = 1 → GlobalTheory.VerticalUnit.UnitAt x (κ a * t i) := by
  intro R K _ _ _ _ _ _ _ X _ _ q _ _ κ hκ I U t hcov ht0 htr hgen
  classical
  have hgz : GeneralizingMap q := Flat.generalizingMap q
  have hinj := IsFractionRing.injective R K
  have hunit : ∀ (x : X) (b : R), b ∉ (q x).asIdeal → UnitAt x (κ (algebraMap R K b)) := fun x b hb =>
    ⟨(unitAt_constFn q x b hb).unit, by
      rw [IsUnit.unit_spec, hκ]
      exact X.presheaf.germ_stalkSpecializes_apply _ _ _⟩
  let S : Set X := {x | ∃ i, x ∈ U i ∧ UnitAt x (t i)}
  have hS : IsOpen S := by
    change IsOpen {x | ∃ i, x ∈ U i ∧ UnitAt x (t i)}
    rw [Set.setOf_exists]
    exact isOpen_iUnion fun i => (U i).isOpen.inter (isOpen_unitAt _)
  have hg : genericPoint X ∈ S := by
    let p₀ : PrimeSpectrum R := ⟨⊥, Ideal.bot_prime⟩
    obtain ⟨y, -, hy⟩ := hgz ((PrimeSpectrum.le_iff_specializes p₀ (q (genericPoint X))).1 bot_le)
    exact (genericPoint_specializes y).mem_open hS (hgen y (by rw [hy]))
  have hB := GlobalTheory.T.finite_coheight_one_notMem_open_genericPoint X S hS hg
  set B : Set X := {x : X | Order.coheight x = 1 ∧ x ∉ S} with hBdef
  have key : ∀ b ∈ B, ∃ π : R, Prime π ∧ (q b).asIdeal = Ideal.span {π} ∧
      (∀ x : X, (q x).asIdeal = Ideal.span {π} → b ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk b) ∧
      Irreducible (X.presheaf.germ ⊤ b trivial (constFn q ⊤ π)) := by
    rintro b ⟨h1, hbS⟩
    have hb0 : (q b).asIdeal ≠ ⊥ := fun h => hbS (hgen b h)
    obtain ⟨π, hπ, hqb⟩ := GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' R X q hgz b h1.le hb0
    obtain ⟨ξ, -, hξ, hd, hirr⟩ := GlobalTheory.T.exists_fibre_genericPoint_dvr_of_prime R X q π hπ
    have hξ1 : Order.coheight ξ = 1 := by
      have e := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk ξ)
      rw [ringKrullDim_stalk_eq_coheight] at e
      exact_mod_cast e
    obtain rfl : b = ξ := eq_of_specializes_of_coheight (hξ b hqb) h1 hξ1
    exact ⟨π, hπ, hqb, hξ, hd, hirr⟩
  choose! π hπ hqπ hsp hdvr hirr using key
  have hstar : ∀ b ∈ B, ∀ x : X, Order.coheight x = 1 → π b ∈ (q x).asIdeal → x = b := by
    intro b hb x hx hmem
    have hx0 : (q x).asIdeal ≠ ⊥ := fun h => (hπ b hb).ne_zero (by rw [h, Ideal.mem_bot] at hmem; exact hmem)
    obtain ⟨π', hπ', hqx⟩ := GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' R X q hgz x hx.le hx0
    have hdvd : π' ∣ π b := Ideal.mem_span_singleton.1 (hqx ▸ hmem)
    have hq : (q x).asIdeal = Ideal.span {π b} :=
      hqx.trans (Ideal.span_singleton_eq_span_singleton.2 (hπ'.associated_of_dvd (hπ b hb) hdvd))
    exact eq_of_specializes_of_coheight (hsp b hb x hq) hx hb.1
  have hne : ∀ b ∈ B, algebraMap R K (π b) ≠ 0 := fun b hb => (map_ne_zero_iff _ hinj).2 (hπ b hb).ne_zero
  have key2 : ∀ b ∈ B, ∃ (i : I) (n : ℤ), b ∈ U i ∧ UnitAt b (κ (algebraMap R K (π b)) ^ (-n) * t i) := by
    intro b hb
    obtain ⟨i, hi⟩ := hcov b
    have := hdvr b hb
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (hirr b hb) (ht0 i b hi)
    have e : algebraMap _ X.functionField (X.presheaf.germ ⊤ b trivial (constFn q ⊤ (π b))) =
        κ (algebraMap R K (π b)) := by
      rw [hκ]; exact X.presheaf.germ_stalkSpecializes_apply _ _ _
    have hπ' : κ (algebraMap R K (π b)) ≠ 0 := (map_ne_zero κ).2 (hne b hb)
    refine ⟨i, n, hi, u, ?_⟩
    rw [hu, e, Units.smul_def, Algebra.smul_def, mul_left_comm, ← zpow_add₀ hπ', neg_add_cancel, zpow_zero,
      _root_.mul_one]
  have : Nonempty I := ⟨(hcov (genericPoint X)).choose⟩
  choose! ib n hUi hunitb using key2
  let F := hB.toFinset
  let a : Kˣ := ∏ b ∈ F.attach, (Units.mk0 _ (hne b.1 (hB.mem_toFinset.1 b.2))) ^ (-n b.1)
  have hκa : κ (a : K) = ∏ b ∈ F, κ (algebraMap R K (π b)) ^ (-n b) := by
    simp only [a, Units.coe_prod, map_prod, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0]
    exact Finset.prod_attach F (fun b => κ (algebraMap R K (π b)) ^ (-n b))
  refine ⟨a, fun i x hx h1 => ?_⟩
  rw [hκa]
  have hother : ∀ b ∈ F, b ≠ x → UnitAt x (κ (algebraMap R K (π b)) ^ (-n b)) := fun b hb hbx =>
    (hunit x (π b) fun hm => hbx (hstar b (hB.mem_toFinset.1 hb) x h1 hm).symm).zpow _
  by_cases hxS : x ∈ S
  · obtain ⟨j, hj, hu⟩ := hxS
    refine htr i j x _ hx hj ((UnitAt.prod F _ fun b hb => hother b hb ?_).mul hu)
    rintro rfl
    exact (hB.mem_toFinset.1 hb).2 ⟨j, hj, hu⟩
  · have hxB : x ∈ B := ⟨h1, hxS⟩
    have hxF : x ∈ F := hB.mem_toFinset.2 hxB
    rw [← Finset.mul_prod_erase F (fun b => κ (algebraMap R K (π b)) ^ (-n b)) hxF]
    refine htr i (ib x) x _ hx (hUi x hxB) ?_
    rw [mul_comm (κ (algebraMap R K (π x)) ^ (-n x)), mul_assoc]
    exact (UnitAt.prod _ _ fun b hb => hother b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)).mul
      (hunitb x hxB)

end GlobalTheory.VerticalUnit
