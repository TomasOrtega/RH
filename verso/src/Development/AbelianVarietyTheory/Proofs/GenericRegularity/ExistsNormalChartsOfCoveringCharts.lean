import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReduced
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsMulEqOfSubfieldClosureEqTop
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsExtendOfPowDenom
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.InjectiveAlgebraMapOfDvrOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringLeDominatingOfFractionFiel

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.PlaceCompletion

namespace GlobalTheory.Reg.NormalCharts

section Val

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Conclude with `⟨fun _ => by simp [vV], fun _ => ⟨0, map_zero _⟩⟩`. Establish `h1 : valV V x ≠ 0` using `valV_ne_zero hx`. Establish `h2 : valV V x ≤ 1 ↔ 0 ≤ vV V x`.

Rewrite using `[vV, ← WithZero.log_le_log h1 one_ne_zero, WithZero.log_one]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← h2]`. Conclude with `⟨fun ⟨v, hv⟩ => hv ▸ valV_algebraMap_le_one v, exists_algebraMap_eq_of_valV_le_one⟩`.
-/
theorem mem_range_iff_vV_nonneg (x : K') : x ∈ Set.range (algebraMap V K') ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    exact ⟨fun _ => by simp [vV], fun _ => ⟨0, map_zero _⟩⟩
  have h1 : valV V x ≠ 0 := valV_ne_zero hx
  have h2 : valV V x ≤ 1 ↔ 0 ≤ vV V x := by
    rw [vV, ← WithZero.log_le_log h1 one_ne_zero, WithZero.log_one]
    omega
  rw [← h2]
  exact ⟨fun ⟨v, hv⟩ => hv ▸ valV_algebraMap_le_one v, exists_algebraMap_eq_of_valV_le_one⟩

/- English proof (translation)
Rewrite using `[vV, valV_algebraMap_of_irreducible hv, WithZero.log_exp]`. Simplify using the standard rewrite rules.
-/
theorem vV_of_irreducible {v : V} (hv : Irreducible v) : vV V (algebraMap V K' v) = 1 := by
  rw [vV, valV_algebraMap_of_irreducible hv, WithZero.log_exp]; simp

variable (V K') in

def imageVal : ValuationSubring K' := (valV V (K' := K')).valuationSubring

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => exists_algebraMap_eq_of_valV_le_one h, fun ⟨v, hv⟩ => hv ▸ valV_algebraMap_le_one v⟩`.
-/
theorem mem_imageVal (x : K') : x ∈ imageVal V K' ↔ x ∈ Set.range (algebraMap V K') :=
  ⟨fun h => exists_algebraMap_eq_of_valV_le_one h, fun ⟨v, hv⟩ => hv ▸ valV_algebraMap_le_one v⟩

/- English proof (translation)
Use `choose f hf using h`. Establish `hinj` using `IsFractionRing.injective V K'`. Conclude with `⟨{ toFun := f map_one' := hinj (by simp [hf]) map_mul' := fun x y => hinj (by simp [hf]) map_zero' := hinj (by simp [hf]) map_add' := fun x y => hinj (by simp [hf]) }, hf⟩`.
-/
theorem exists_corestrict {A : Type} [CommRing A] (φ : A →+* K')
    (h : ∀ x, φ x ∈ Set.range (algebraMap V K')) :
    ∃ φ' : A →+* V, ∀ x, algebraMap V K' (φ' x) = φ x := by
  choose f hf using h
  have hinj := IsFractionRing.injective V K'
  exact ⟨{ toFun := f
           map_one' := hinj (by simp [hf])
           map_mul' := fun x y => hinj (by simp [hf])
           map_zero' := hinj (by simp [hf])
           map_add' := fun x y => hinj (by simp [hf]) }, hf⟩

/- English proof (translation)
Establish `hinj : Function.Injective ((algebraMap V K').comp g)` using `(IsFractionRing.injective V K').comp hg`. Set `χ : F →+* K'` to `IsFractionRing.lift (K := F) hinj`. Establish `hχ : ∀ a, χ (algebraMap O F a) = algebraMap V K' (g a)` using `fun a => IsFractionRing.lift_algebraMap hinj a`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨ρ, hρ⟩` from `IsDiscreteValuationRing.exists_irreducible V`.

Establish `h0 : g π ≠ 0` using `fun h => hπ.ne_zero (hg (h.trans (map_zero g).symm))`. Take `⟨r, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hρ`. Establish `hr : 0 < r`. Use `Nat.pos_of_ne_zero fun h => hπ.not_isUnit (hl.map_nonunit π ?_)` and prove the remaining obligations. Rewrite using `[hu, h, pow_zero, mul_one]`.

Conclude with `u.isUnit`. Establish `key : ∀ a : O, valV V (χ (algebraMap O F a)) = valV O (algebraMap O F a) ^ r`. Introduce `a`. Distinguish the cases in `ha : a = 0`. Simplify using `[ha, hr.ne']`.

Take `⟨n, w, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ`. Rewrite using `[hχ]`. Simplify using `only [map_mul, map_pow, hu]`. Rewrite using `[valV_algebraMap_of_isUnit (w.isUnit.map g), valV_algebraMap_of_isUnit u.isUnit, valV_algebraMap_of_isUnit w.isUnit, valV_algebraMap_of_irreducible hρ, valV_algebraMap_of_irreducible hπ, one_mul, one_mul, one_mul, ← pow_mul, ← pow_mul, mul_comm]`. Use `⟨χ, r, hr, hχ, fun x => ?_⟩` and prove the remaining obligations.

Establish `: valV V (χ x) = valV O x ^ r`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := O) x`. Rewrite using `[map_div₀, map_div₀, map_div₀, key, key, div_pow]`. Rewrite using `[vV, vV, this, WithZero.log_pow]`. Simplify using the standard rewrite rules.
-/
theorem exists_ramification {O F : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field F] [Algebra O F] [IsFractionRing O F] (g : O →+* V) (hg : Function.Injective g)
    (hl : IsLocalHom g) :
    ∃ (χ : F →+* K') (r : ℕ), 0 < r ∧ (∀ a, χ (algebraMap O F a) = algebraMap V K' (g a)) ∧
      ∀ x, vV V (χ x) = (r : ℤ) * vV O x := by
  have hinj : Function.Injective ((algebraMap V K').comp g) :=
    (IsFractionRing.injective V K').comp hg
  let χ : F →+* K' := IsFractionRing.lift (K := F) hinj
  have hχ : ∀ a, χ (algebraMap O F a) = algebraMap V K' (g a) := fun a =>
    IsFractionRing.lift_algebraMap hinj a
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have h0 : g π ≠ 0 := fun h => hπ.ne_zero (hg (h.trans (map_zero g).symm))
  obtain ⟨r, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hρ
  have hr : 0 < r := by
    refine Nat.pos_of_ne_zero fun h => hπ.not_isUnit (hl.map_nonunit π ?_)
    rw [hu, h, pow_zero, mul_one]; exact u.isUnit
  have key : ∀ a : O, valV V (χ (algebraMap O F a)) = valV O (algebraMap O F a) ^ r := by
    intro a
    by_cases ha : a = 0
    · simp [ha, hr.ne']
    obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    rw [hχ]
    simp only [map_mul, map_pow, hu]
    rw [valV_algebraMap_of_isUnit (w.isUnit.map g), valV_algebraMap_of_isUnit u.isUnit,
      valV_algebraMap_of_isUnit w.isUnit, valV_algebraMap_of_irreducible hρ,
      valV_algebraMap_of_irreducible hπ, one_mul, one_mul, one_mul, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨χ, r, hr, hχ, fun x => ?_⟩
  have : valV V (χ x) = valV O x ^ r := by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    rw [map_div₀, map_div₀, map_div₀, key, key, div_pow]
  rw [vV, vV, this, WithZero.log_pow]
  simp

end Val

section Alg

variable {A : Type} [CommRing A] [IsDomain A]

/- English proof (translation)
Set `D : Ideal A` to `{ carrier := {s | ∃ x : A, q * algebraMap A _ s = algebraMap A _ x} add_mem' := by`. Introduce and unpack `a b ⟨x, hx⟩ ⟨y, hy⟩`. Conclude with `⟨x + y, by rw [map_add, map_add, mul_add, hx, hy]⟩`. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `r a ⟨x, hx⟩`. Conclude with `⟨r * x, by rw [smul_eq_mul, map_mul, map_mul, ← hx]; ring⟩ }`. Establish `: ∀ e ∈ Ideal.span s, ϖ * e ∈ D.radical`. Introduce `e he`. Proceed by induction on `he using Submodule.span_induction with`.

Consider the case `mem e he`. Take `⟨x, t, hx⟩` from `h e he`. Conclude with `⟨t, x, hx⟩`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [mul_add]`.

Conclude with `add_mem ha hb`. Consider the case `smul r a _ ha => rw [smul_eq_mul, mul_left_comm]`. Conclude with `Ideal.mul_mem_left _ _ ha`. Introduce `e he`. Take `⟨t, x, hx⟩` from `this e he`.

Conclude with `⟨x, t, hx⟩`.
-/
theorem regular_span (q : FractionRing A) (ϖ : A) (s : Set A)
    (h : ∀ e ∈ s, ∃ (x : A) (t : ℕ), q * algebraMap A _ ((ϖ * e) ^ t) = algebraMap A _ x) :
    ∀ e ∈ Ideal.span s, ∃ (x : A) (t : ℕ),
      q * algebraMap A _ ((ϖ * e) ^ t) = algebraMap A _ x := by
  let D : Ideal A :=
    { carrier := {s | ∃ x : A, q * algebraMap A _ s = algebraMap A _ x}
      add_mem' := by
        rintro a b ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x + y, by rw [map_add, map_add, mul_add, hx, hy]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r a ⟨x, hx⟩
        exact ⟨r * x, by rw [smul_eq_mul, map_mul, map_mul, ← hx]; ring⟩ }
  have : ∀ e ∈ Ideal.span s, ϖ * e ∈ D.radical := by
    intro e he
    induction he using Submodule.span_induction with
    | mem e he =>
      obtain ⟨x, t, hx⟩ := h e he
      exact ⟨t, x, hx⟩
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul r a _ ha => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ ha
  intro e he
  obtain ⟨t, x, hx⟩ := this e he
  exact ⟨x, t, hx⟩

/- English proof (translation)
Use `⟨x, s, hs, hq, ?_⟩` and prove the remaining obligations. Establish `h0 : algebraMap V (FractionRing V) (φ s) ≠ 0` using `by simpa using hs`. Rewrite using `[← hw, nval_mul, nval_of_ne h0, EReal.add_sub_cancel_right]`.
-/
theorem chV_of {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (φ : A →+* V)
    (n : ℕ) (q : FractionRing A) (w : FractionRing V) (x s : A) (hs : φ s ≠ 0)
    (hq : q * algebraMap A _ s = algebraMap A _ x)
    (hw : w * algebraMap V _ (φ s) = algebraMap V _ (φ x)) : ChV φ n q (nval V n w) := by
  refine ⟨x, s, hs, hq, ?_⟩
  have h0 : algebraMap V (FractionRing V) (φ s) ≠ 0 := by simpa using hs
  rw [← hw, nval_mul, nval_of_ne h0, EReal.add_sub_cancel_right]

end Alg

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} (P : PChart Xo c β)
  {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [IsDomain A]
  [Algebra O A] (io : c.F →+* FractionRing O) (α : P.Ω →+* FractionRing A)

/- English proof (translation)
Use `(Subring.closure_le (t := (P.R e).toSubring)).2 ?_ hb` and prove the remaining obligations. Introduce and unpack `x (⟨a, rfl⟩ | hx)`. Conclude with `(P.R e).algebraMap_mem _`. Conclude with `Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)`.
-/
theorem mem_R_of_mem_B (e : P.Ω) {b : P.Ω} (hb : b ∈ P.B) : b ∈ P.R e := by
  refine (Subring.closure_le (t := (P.R e).toSubring)).2 ?_ hb
  rintro x (⟨a, rfl⟩ | hx)
  · exact (P.R e).algebraMap_mem _
  · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)

def bdry : Ideal A := Ideal.span {x | ∃ e ∈ P.es, algebraMap A (FractionRing A) x = α e}

/- English proof (translation)
The claim follows from `evR_baseChange_of_isReduced E H Dw l Xo c hE a n f hf _ _ _ _ _ (P.gen e he)`.
-/
theorem evR_generic (hE : EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) (e : P.Ω) (he : e ∈ P.es) :
    evR Xo c f P.yg = (evR Xo c f (P.y e he) : P.R e) :=
  evR_baseChange_of_isReduced E H Dw l Xo c hE a n f hf _ _ _ _ _ (P.gen e he)

variable (hβ : ∀ a, io (β a) ∈ Set.range (algebraMap O (FractionRing O)))
  (hK : ∀ (k : c.F) (a b : O), io k * algebraMap O _ b = algebraMap O _ a →
    α (algebraMap c.F P.Ω k) * algebraMap A _ (algebraMap O A b) = algebraMap A _ (algebraMap O A a))
  (hg : ∀ g ∈ P.gens, α g ∈ Set.range (algebraMap A (FractionRing A)))

include hβ hK hg in
/- English proof (translation)
Use `(Subring.closure_le (t := (algebraMap A (FractionRing A)).range.comap α)).2 ?_ hb` and prove the remaining obligations. Introduce and unpack `x (⟨a, rfl⟩ | hx)`. Take `⟨x, hx⟩` from `hβ a`. Use `hK (β a) x 1 (by rw [map_one, mul_one, hx])` as an intermediate fact. Rewrite `this` using `[map_one, map_one, mul_one]`.

Conclude with `⟨_, this.symm⟩`. Conclude with `hg x hx`.
-/
theorem mem_range_of_mem_B {b : P.Ω} (hb : b ∈ P.B) :
    α b ∈ Set.range (algebraMap A (FractionRing A)) := by
  refine (Subring.closure_le (t := (algebraMap A (FractionRing A)).range.comap α)).2 ?_ hb
  rintro x (⟨a, rfl⟩ | hx)
  · obtain ⟨x, hx⟩ := hβ a
    have := hK (β a) x 1 (by rw [map_one, mul_one, hx])
    rw [map_one, map_one, mul_one] at this
    exact ⟨_, this.symm⟩
  · exact hg x hx

include hβ hK hg in
/- English proof (translation)
Take `⟨e, he⟩` from `P.es_ne`. Take `⟨x, hx⟩` from `mem_range_of_mem_B P io α hβ hK hg (P.es_mem e he).2`. Introduce `h`. Establish `: x ∈ bdry P α` using `Ideal.subset_span ⟨e, he, hx⟩`. Rewrite `this` using `[h, Ideal.mem_bot]`.

Rewrite `hx` using `[this, map_zero, eq_comm, map_eq_zero]`. Conclude with `(P.es_mem e he).1 hx`.
-/
theorem bdry_ne_bot : bdry P α ≠ ⊥ := by
  obtain ⟨e, he⟩ := P.es_ne
  obtain ⟨x, hx⟩ := mem_range_of_mem_B P io α hβ hK hg (P.es_mem e he).2
  intro h
  have : x ∈ bdry P α := Ideal.subset_span ⟨e, he, hx⟩
  rw [h, Ideal.mem_bot] at this
  rw [this, map_zero, eq_comm, map_eq_zero] at hx
  exact (P.es_mem e he).1 hx

include hK hg in
/- English proof (translation)
Introduce `e he ϖ hϖ`. Use `regular_span _ _ _ ?_ e he` and prove the remaining obligations. Introduce and unpack `eb ⟨e, he, heb⟩`. Conclude with `(GlobalTheory.Reg.openChart_regular_away c.F P.Ω O A io P.gens e α eb ϖ hϖ (P.es_mem e he).1 heb hK hg).1 q (hq e he)`.
-/
theorem regular_bdry {q : P.Ω} (hq : ∀ e ∈ P.es, q ∈ P.R e) :
    ∀ e ∈ bdry P α, ∀ ϖ : O, Irreducible ϖ → ∃ (x : A) (t : ℕ),
      α q * algebraMap A _ ((algebraMap O A ϖ * e) ^ t) = algebraMap A _ x := by
  intro e he ϖ hϖ
  refine regular_span _ _ _ ?_ e he
  rintro eb ⟨e, he, heb⟩
  exact (GlobalTheory.Reg.openChart_regular_away c.F P.Ω O A io P.gens e α eb ϖ hϖ (P.es_mem e he).1 heb hK hg).1 q (hq e he)

include hβ hK hg in
/- English proof (translation)
Take `⟨eb, heb⟩` from `mem_range_of_mem_B P io α hβ hK hg (P.es_mem e he).2`. Establish `h0 : φ eb ≠ 0`. Introduce `h`. Set `r : P.R e` to `⟨e, mem_R_of_mem_B P e (P.es_mem e he).2⟩`. Set `r' : P.R e` to `⟨e⁻¹, Algebra.subset_adjoin (Set.mem_insert _ _)⟩`.

Establish `h1` using `hψ r eb 1 (by rw [map_one, mul_one, heb])`. Rewrite `h1` using `[h, map_one, map_one, mul_one, map_zero]`. Establish `h2 : r * r' = 1` using `Subtype.ext (mul_inv_cancel₀ (P.es_mem e he).1)`. Establish `h3` using `congrArg ψ h2`. Rewrite `h3` using `[map_mul, h1, zero_mul, map_one]`.

Conclude with `zero_ne_one h3`. Use `⟨⟨eb, Ideal.subset_span ⟨e, he, heb⟩, h0⟩, fun n r => ?_⟩` and prove the remaining obligations. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨x, t, hx⟩` from `(GlobalTheory.Reg.openChart_regular_away c.F P.Ω O A io P.gens e α eb ϖ hϖ (P.es_mem e he).1 heb hK hg).1 r r.2`. Use `chV_of φ n _ _ x _ ?_ hx (hψ r x _ hx)` and prove the remaining obligations.

Rewrite using `[map_pow, map_mul]`. Conclude with `pow_ne_zero _ (mul_ne_zero (hφ ϖ hϖ.ne_zero) h0)`.
-/
theorem chV_point {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (φ : A →+* V)
    (e : P.Ω) (he : e ∈ P.es) (ψ : P.R e →+* FractionRing V)
    (hψ : ∀ (r : P.R e) (x s : A), α r * algebraMap A _ s = algebraMap A _ x →
      ψ r * algebraMap V _ (φ s) = algebraMap V _ (φ x))
    (hφ : ∀ a : O, a ≠ 0 → φ (algebraMap O A a) ≠ 0) :
    (∃ x ∈ bdry P α, φ x ≠ 0) ∧ ∀ (n : ℕ) (r : P.R e), ChV φ n (α r) (nval V n (ψ r)) := by
  obtain ⟨eb, heb⟩ := mem_range_of_mem_B P io α hβ hK hg (P.es_mem e he).2
  have h0 : φ eb ≠ 0 := by
    intro h
    let r : P.R e := ⟨e, mem_R_of_mem_B P e (P.es_mem e he).2⟩
    let r' : P.R e := ⟨e⁻¹, Algebra.subset_adjoin (Set.mem_insert _ _)⟩
    have h1 := hψ r eb 1 (by rw [map_one, mul_one, heb])
    rw [h, map_one, map_one, mul_one, map_zero] at h1
    have h2 : r * r' = 1 := Subtype.ext (mul_inv_cancel₀ (P.es_mem e he).1)
    have h3 := congrArg ψ h2
    rw [map_mul, h1, zero_mul, map_one] at h3
    exact zero_ne_one h3
  refine ⟨⟨eb, Ideal.subset_span ⟨e, he, heb⟩, h0⟩, fun n r => ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨x, t, hx⟩ := (GlobalTheory.Reg.openChart_regular_away c.F P.Ω O A io P.gens e α eb ϖ hϖ (P.es_mem e he).1 heb hK
    hg).1 r r.2
  refine chV_of φ n _ _ x _ ?_ hx (hψ r x _ hx)
  rw [map_pow, map_mul]
  exact pow_ne_zero _ (mul_ne_zero (hφ ϖ hϖ.ne_zero) h0)

include hK hg in
/- English proof (translation)
Take `⟨k, h0, h1, h2⟩` from `h`. Use `⟨k, (map_ne_zero α).2 h0, fun i => ?_, ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `mem_range_of_mem_B P io α hβ hK hg (h1 i)`. Conclude with `⟨x, by rw [hx, ← map_mul, div_mul_cancel₀ _ h0]⟩`. Rewrite using `[← map_inv₀]`.

Conclude with `regular_bdry P io α hK hg h2`.
-/
theorem family_chart {m : ℕ} {ws : Fin m → Rul Xo c}
    (hβ : ∀ a, io (β a) ∈ Set.range (algebraMap O (FractionRing O))) (h : P.Fam ws) :
    ∃ k, α (evR Xo c (ws k) P.yg) ≠ 0 ∧
      (∀ i, ∃ x : A, α (evR Xo c (ws i) P.yg) = algebraMap A _ x * α (evR Xo c (ws k) P.yg)) ∧
      ∀ e ∈ bdry P α, ∀ ϖ : O, Irreducible ϖ → ∃ (x : A) (t : ℕ),
        (α (evR Xo c (ws k) P.yg))⁻¹ * algebraMap A _ ((algebraMap O A ϖ * e) ^ t) =
          algebraMap A _ x := by
  obtain ⟨k, h0, h1, h2⟩ := h
  refine ⟨k, (map_ne_zero α).2 h0, fun i => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := mem_range_of_mem_B P io α hβ hK hg (h1 i)
    exact ⟨x, by rw [hx, ← map_mul, div_mul_cancel₀ _ h0]⟩
  · rw [← map_inv₀]
    exact regular_bdry P io α hK hg h2

include hβ hK hg in
/- English proof (translation)
Take `⟨hinj, hloc, hcpl, hch, hfin'⟩` from `GlobalTheory.dvr_finite_over_complete_dvr O V`. Take `⟨χ, r, hr, hχ, hv⟩` from `exists_ramification (K' := FractionRing V) (F := FractionRing O) (algebraMap O V) hinj hloc`. Establish `hgen : ∃ eb : A, (∃ e ∈ P.es, algebraMap A (FractionRing A) eb = α e) ∧ φ eb ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Take `⟨x, hx, hx0⟩` from `hφ`. Conclude with `hx0 ((Ideal.span_le (I := RingHom.ker φ.toRingHom)).2 (fun y hy => hcon y hy) hx)`. Take `⟨eb, ⟨e, he, heb⟩, h0⟩` from `hgen`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hφO : ∀ a : O, a ≠ 0 → φ (algebraMap O A a) ≠ 0` using `fun a ha => by`.

Rewrite using `[φ.commutes]`. Conclude with `(map_ne_zero_iff _ hinj).2 ha`. Take `⟨ψ, hψ⟩` from `(GlobalTheory.Reg.openChart_regular_away c.F P.Ω O A io P.gens e α eb ϖ hϖ (P.es_mem e he).1 heb hK hg).2 (FractionRing V) ((algebraMap V (FractionRing V)).comp φ.toRingHom) (by`. Express the relevant statement in the definitionally equal form `algebraMap V (FractionRing V) (φ _) ≠ 0`. Rewrite using `[map_mul]`.

Simplify using `using mul_ne_zero (hφO ϖ hϖ.ne_zero) h0)`. Use `replace hψ : ∀ (r : P.R e) (x s : A), α r * algebraMap A _ s = algebraMap A _ x → ψ r * algebraMap V _ (φ s) = algebraMap V _ (φ x) := hψ`. Set `T : CDVR` to `{ V := V }`. Set `ioV : c.F →+* T.Fr` to `χ.comp io`. Use `letI := ioV.toAlgebra`.

Establish `hψK : ∀ k : c.F, ψ (algebraMap c.F _ k) = ioV k`. Introduce `k`. Take `⟨a, b, hb, hab⟩` from `IsFractionRing.div_surjective (A := O) (io k)`. Establish `hb0 : algebraMap O (FractionRing O) b ≠ 0` using `by simpa using nonZeroDivisors.ne_zero hb`. Establish `h1 : io k * algebraMap O _ b = algebraMap O _ a`.

Rewrite using `[← hab, div_mul_cancel₀ _ hb0]`. Establish `h2` using `hψ (algebraMap c.F _ k) _ _ (hK k a b h1)`. Rewrite `h2` using `[φ.commutes, φ.commutes, ← hχ, ← hχ, ← h1, map_mul]`. Conclude with `mul_right_cancel₀ ((map_ne_zero χ).2 hb0) h2`. Set `ψ' : P.R e →ₐ[c.F] T.Fr` to `{ ψ with commutes' := hψK }`.

Take `⟨z, hz⟩` from `hE.bc _ _ ψ' (P.y e he)`. Establish `hint : Integral T ioV z`. Use `P.int e he T ioV ψ' (fun a => ?_) (fun g hg' => ?_) z hz` and prove the remaining obligations. Take `⟨x, hx⟩` from `hβ a`. Conclude with `⟨algebraMap O V x, by rw [← hχ, hx]; rfl⟩`.

Take `⟨x, hx⟩` from `hg g hg'`. Use `hψ g x 1 (by rw [map_one, mul_one, hx])` as an intermediate fact. Rewrite `this` using `[map_one, map_one, mul_one]`. Conclude with `⟨φ x, this.symm⟩`. Set `y : IntFr Xo c T ioV` to `⟨z, hE.test _ z, hint⟩`.

Establish `hov : OverLa la V ioV (r * 1)` using `hio.bc χ hr hv`. Use `⟨ioV, r * 1, hov, fun π hπ => ?_, _, ⟨PtV.mk (T := T) la hov y (hfin' hfin) () trivial, rfl⟩, fun a n f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[← hχ, hv, vV_of_irreducible hπ]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `ChV _ _ _ (nval T.V (r * 1) (evI y f))`.

Rewrite using `[evR_generic P hE hf e he]`. Establish `: evI y f = ψ (evR Xo c f (P.y e he))` using `evR_baseChange_of_isReduced E H Dw l Xo c hE a n f hf _ _ ψ' _ _ hz`. Rewrite using `[this]`. Conclude with `(chV_point P io α hβ hK hg φ.toRingHom e he ψ hψ hφO).2 _ _`.
-/
theorem points_chart (hE : EvLaws Xo c) [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O]
    (hfin : Finite (IsLocalRing.ResidueField O)) {la : HeightOneSpectrum (𝓞 c.F)}
    (hio : OverLa la O io 1)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
    [Module.Finite O V] (φ : A →ₐ[O] V) (hφ : ∃ e ∈ bdry P α, φ e ≠ 0) :
    ∃ (ioV : c.F →+* FractionRing V) (e : ℕ), OverLa la V ioV e ∧
      (∀ ϖ : O, Irreducible ϖ → vV (K' := FractionRing V) V
        (algebraMap V (FractionRing V) (algebraMap O V ϖ)) * ((1 : ℕ) : ℤ) = e) ∧
      ∃ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
        ∀ f ∈ sec Xo c a n, ChV φ.toRingHom e (α (evR Xo c f P.yg)) (v f) := by
  obtain ⟨hinj, hloc, hcpl, hch, hfin'⟩ := GlobalTheory.dvr_finite_over_complete_dvr O V
  obtain ⟨χ, r, hr, hχ, hv⟩ := exists_ramification (K' := FractionRing V) (F := FractionRing O)
    (algebraMap O V) hinj hloc
  have hgen : ∃ eb : A, (∃ e ∈ P.es, algebraMap A (FractionRing A) eb = α e) ∧ φ eb ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx, hx0⟩ := hφ
    exact hx0 ((Ideal.span_le (I := RingHom.ker φ.toRingHom)).2 (fun y hy => hcon y hy) hx)
  obtain ⟨eb, ⟨e, he, heb⟩, h0⟩ := hgen
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hφO : ∀ a : O, a ≠ 0 → φ (algebraMap O A a) ≠ 0 := fun a ha => by
    rw [φ.commutes]; exact (map_ne_zero_iff _ hinj).2 ha
  obtain ⟨ψ, hψ⟩ := (GlobalTheory.Reg.openChart_regular_away c.F P.Ω O A io P.gens e α eb ϖ hϖ (P.es_mem e he).1 heb hK
    hg).2 (FractionRing V) ((algebraMap V (FractionRing V)).comp φ.toRingHom) (by
      change algebraMap V (FractionRing V) (φ _) ≠ 0
      rw [map_mul]
      simpa using mul_ne_zero (hφO ϖ hϖ.ne_zero) h0)
  replace hψ : ∀ (r : P.R e) (x s : A), α r * algebraMap A _ s = algebraMap A _ x →
      ψ r * algebraMap V _ (φ s) = algebraMap V _ (φ x) := hψ
  let T : CDVR := { V := V }
  let ioV : c.F →+* T.Fr := χ.comp io
  letI := ioV.toAlgebra
  have hψK : ∀ k : c.F, ψ (algebraMap c.F _ k) = ioV k := by
    intro k
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := O) (io k)
    have hb0 : algebraMap O (FractionRing O) b ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
    have h1 : io k * algebraMap O _ b = algebraMap O _ a := by
      rw [← hab, div_mul_cancel₀ _ hb0]
    have h2 := hψ (algebraMap c.F _ k) _ _ (hK k a b h1)
    rw [φ.commutes, φ.commutes, ← hχ, ← hχ, ← h1, map_mul] at h2
    exact mul_right_cancel₀ ((map_ne_zero χ).2 hb0) h2
  let ψ' : P.R e →ₐ[c.F] T.Fr := { ψ with commutes' := hψK }
  obtain ⟨z, hz⟩ := hE.bc _ _ ψ' (P.y e he)
  have hint : Integral T ioV z := by
    refine P.int e he T ioV ψ' (fun a => ?_) (fun g hg' => ?_) z hz
    · obtain ⟨x, hx⟩ := hβ a
      exact ⟨algebraMap O V x, by rw [← hχ, hx]; rfl⟩
    · obtain ⟨x, hx⟩ := hg g hg'
      have := hψ g x 1 (by rw [map_one, mul_one, hx])
      rw [map_one, map_one, mul_one] at this
      exact ⟨φ x, this.symm⟩
  let y : IntFr Xo c T ioV := ⟨z, hE.test _ z, hint⟩
  have hov : OverLa la V ioV (r * 1) := hio.bc χ hr hv
  refine ⟨ioV, r * 1, hov, fun π hπ => ?_, _, ⟨PtV.mk (T := T) la hov y (hfin' hfin) () trivial, rfl⟩,
    fun a n f hf => ?_⟩
  · rw [← hχ, hv, vV_of_irreducible hπ]; simp
  · change ChV _ _ _ (nval T.V (r * 1) (evI y f))
    rw [evR_generic P hE hf e he]
    have : evI y f = ψ (evR Xo c f (P.y e he)) :=
      evR_baseChange_of_isReduced E H Dw l Xo c hE a n f hf _ _ ψ' _ _ hz
    rw [this]
    exact (chV_point P io α hβ hK hg φ.toRingHom e he ψ hψ hφO).2 _ _

end Chart

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Use `letI := io.toAlgebra`. Take `⟨e, he, ψ, z, t, hg, hz, ht⟩` from `h`. Establish `hint : Integral T io z` using `P.int e he T io ψ (fun a => hW _ (hβ a)) (fun g hg' => hW _ (hg g hg')) z hz`. Set `z' : IntFr Xo c T io` to `⟨z, hE.test _ z, hint⟩`. Use `⟨e, he, ψ.toRingHom, ψ.commutes, hg, fun a n f hf => ⟨evR Xo c f (P.y e he), evR_generic P hE hf e he, fun d => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[unitIndep_of hE.wt hU a n f hf T io y z' t ht d]`. Establish `: evI z' f = ψ (evR Xo c f (P.y e he))` using `evR_baseChange_of_isReduced E H Dw l Xo c hE a n f hf _ _ ψ _ _ hz`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem values_of_catches {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} (P : PChart Xo c β)
    (hE : EvLaws Xo c) (hU : IntDiagUnit Xo c) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io)
    (W : ValuationSubring T.Fr) (hW : ∀ x ∈ W, x ∈ Set.range (algebraMap T.V T.Fr))
    (hβ : ∀ a, io (β a) ∈ W) (h : letI := io.toAlgebra; P.Catches W y.1) :
    ∃ (e : P.Ω) (_ : e ∈ P.es) (ψ : P.R e →+* T.Fr), (∀ k, ψ (algebraMap c.F _ k) = io k) ∧
      (∀ g : P.R e, (g : P.Ω) ∈ P.gens → ψ g ∈ W) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∃ r : P.R e,
        evR Xo c f P.yg = r ∧ ∀ d : ℕ, nval T.V d (evI y f) = nval T.V d (ψ r) := by
  letI := io.toAlgebra
  obtain ⟨e, he, ψ, z, t, hg, hz, ht⟩ := h
  have hint : Integral T io z :=
    P.int e he T io ψ (fun a => hW _ (hβ a)) (fun g hg' => hW _ (hg g hg')) z hz
  let z' : IntFr Xo c T io := ⟨z, hE.test _ z, hint⟩
  refine ⟨e, he, ψ.toRingHom, ψ.commutes, hg, fun a n f hf =>
    ⟨evR Xo c f (P.y e he), evR_generic P hE hf e he, fun d => ?_⟩⟩
  rw [unitIndep_of hE.wt hU a n f hf T io y z' t ht d]
  have : evI z' f = ψ (evR Xo c f (P.y e he)) :=
    evR_baseChange_of_isReduced E H Dw l Xo c hE a n f hf _ _ ψ _ _ hz
  rw [this]; rfl

/- English proof (translation)
The claim follows from `exists_algebraMap_eq_of_valV_le_one (by rw [valV_eq_pow_of_overLa h] exact pow_le_one₀ zero_le a.2)`.
-/
theorem mem_range_of_overLa {la : HeightOneSpectrum (𝓞 c.F)} {V K' : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K'] [Algebra V K'] [IsFractionRing V K'] {io : c.F →+* K'}
    {e : ℕ} (h : OverLa la V io e) (a : (la.valuation c.F).valuationSubring) :
    io ((la.valuation c.F).valuationSubring.subtype a) ∈ Set.range (algebraMap V K') :=
  exists_algebraMap_eq_of_valV_le_one (by
    rw [valV_eq_pow_of_overLa h]
    exact pow_le_one₀ zero_le a.2)

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[Ideal.eq_top_iff_one, Submodule.mem_sup]`. Take `⟨u, hu, m, hm, hum⟩` from `h`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hu`. Establish `h1 : W.valuation (algebraMap V (FractionRing V) (φ (a * p))) < 1`.

Rewrite using `[map_mul, map_mul, map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right ((W.valuation_le_one_iff _).2 (hφ a)) zero_le (W.mem_nonunits_iff.1 hp)`. Establish `h2 : W.valuation (algebraMap V (FractionRing V) (φ m)) < 1`. Rewrite using `[← W.mem_nonunits_iff, W.mem_nonunits_iff_or]`. Distinguish the cases in `h0 : algebraMap V (FractionRing V) (φ m) = 0`.

Conclude with `Or.inl h0`. Use `Or.inr fun hinv => ?_` and prove the remaining obligations. Take `⟨v, hv⟩` from `(mem_imageVal _).1 (hW hinv)`. Use `(hm : ¬ IsUnit (φ m)) (IsUnit.of_mul_eq_one v (IsFractionRing.injective V (FractionRing V) ?_))` and prove the remaining obligations. Rewrite using `[map_mul, hv, map_one, mul_inv_cancel₀ h0]`.

Establish `h3` using `W.valuation.map_add_lt h1 h2`. Rewrite `h3` using `[← map_add, ← map_add, hum, map_one, map_one, map_one]`. Conclude with `lt_irrefl _ h3`.
-/
theorem sup_ne_top_of_nonunits {A V : Type} [CommRing A] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (φ : A →+* V) (W : ValuationSubring (FractionRing V))
    (hW : W ≤ imageVal V (FractionRing V)) (hφ : ∀ x, algebraMap V (FractionRing V) (φ x) ∈ W)
    (p : A) (hp : algebraMap V (FractionRing V) (φ p) ∈ W.nonunits) :
    Ideal.span {p} ⊔ (IsLocalRing.maximalIdeal V).comap φ ≠ ⊤ := by
  intro h
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at h
  obtain ⟨u, hu, m, hm, hum⟩ := h
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have h1 : W.valuation (algebraMap V (FractionRing V) (φ (a * p))) < 1 := by
    rw [map_mul, map_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right ((W.valuation_le_one_iff _).2 (hφ a)) zero_le
      (W.mem_nonunits_iff.1 hp)
  have h2 : W.valuation (algebraMap V (FractionRing V) (φ m)) < 1 := by
    rw [← W.mem_nonunits_iff, W.mem_nonunits_iff_or]
    by_cases h0 : algebraMap V (FractionRing V) (φ m) = 0
    · exact Or.inl h0
    refine Or.inr fun hinv => ?_
    obtain ⟨v, hv⟩ := (mem_imageVal _).1 (hW hinv)
    refine (hm : ¬ IsUnit (φ m)) (IsUnit.of_mul_eq_one v (IsFractionRing.injective V (FractionRing V) ?_))
    rw [map_mul, hv, map_one, mul_inv_cancel₀ h0]
  have h3 := W.valuation.map_add_lt h1 h2
  rw [← map_add, ← map_add, hum, map_one, map_one, map_one] at h3
  exact lt_irrefl _ h3

/- English proof (translation)
Take `⟨κ, hκ⟩` from `exists_corestrict (V := T) io fun a => (mem_range_iff_vV_nonneg _).2 (by`. Distinguish the cases in `ha : a = 0`. Simplify using `[ha, vV]`. Conclude with `(htriv a ha).ge)`. Take `⟨V, _, _, _, i, χ, hinj, hirr, hloc, hiχ⟩` from `@GlobalTheory.DVRBaseChange.exists_unramified_extension K F T _ _ _ io₀.toAlgebra _ _ _ κ.toAlgebra`.

Use `replace hiχ : ∀ a, i (κ a) = χ (io₀ a) := hiχ`. Take `⟨i', r, hr, hi', hv⟩` from `exists_ramification (K' := FractionRing V) (F := Fr) i hinj hloc`. Establish `hr1 : r = 1`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible T`. Use `hv (algebraMap T Fr π)` as an intermediate fact.

Rewrite `this` using `[hi', vV_of_irreducible hπ, vV_of_irreducible (hirr π hπ), mul_one]`. Conclude with `this.symm` after adjusting the coercions. Substitute `hr1` using the available equality. Conclude with `⟨V, inferInstance, inferInstance, inferInstance, i', χ, hv, fun k => by rw [← hκ, hi', hiχ]⟩`.
-/
theorem exists_unramified_of_trivial {K F T Fr : Type} [Field K] [CharZero K] [Field F] [CommRing T]
    [IsDomain T] [IsDiscreteValuationRing T] [Field Fr] [Algebra T Fr] [IsFractionRing T Fr]
    (io₀ : K →+* F) (io : K →+* Fr) (htriv : ∀ a : K, a ≠ 0 → vV T (io a) = 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (i : Fr →+* FractionRing V) (χ : F →+* V), (∀ x, vV V (i x) = ((1 : ℕ) : ℤ) * vV T x) ∧
      ∀ k, i (io k) = algebraMap V (FractionRing V) (χ (io₀ k)) := by
  obtain ⟨κ, hκ⟩ := exists_corestrict (V := T) io fun a => (mem_range_iff_vV_nonneg _).2 (by
    by_cases ha : a = 0
    · simp [ha, vV]
    · exact (htriv a ha).ge)
  obtain ⟨V, _, _, _, i, χ, hinj, hirr, hloc, hiχ⟩ :=
    @GlobalTheory.DVRBaseChange.exists_unramified_extension K F T _ _ _ io₀.toAlgebra _ _ _ κ.toAlgebra
  replace hiχ : ∀ a, i (κ a) = χ (io₀ a) := hiχ
  obtain ⟨i', r, hr, hi', hv⟩ := exists_ramification (K' := FractionRing V) (F := Fr) i hinj hloc
  have hr1 : r = 1 := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
    have := hv (algebraMap T Fr π)
    rw [hi', vV_of_irreducible hπ, vV_of_irreducible (hirr π hπ), mul_one] at this
    exact_mod_cast this.symm
  subst hr1
  exact ⟨V, inferInstance, inferInstance, inferInstance, i', χ, hv,
    fun k => by rw [← hκ, hi', hiχ]⟩

end Main

end GlobalTheory.Reg.NormalCharts

namespace GlobalTheory.Reg

open NormalCharts

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c hE hU la J _ P hP`. Take `⟨T₀, io₀, hov, hfin, hinit⟩` from `exists_initial_completion c.F la`. Establish `hβ` using `mem_range_of_overLa hov`. Establish `hN` using `fun j => GlobalTheory.exists_normal_charts_over_dvr c.F (P j).Ω T₀.V io₀ (P j).gens (P j).es (P j).frac (fun e he => ⟨((P j).es_mem e he).1, Subring.closure_mono (by`. Use `Set.union_subset_union_left _ ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨_, hβ a, rfl⟩) ((P j).es_mem e he).2⟩) (P j).sm`. Use `choose J' finJ A acr adom alg α hA hK hg hcov using hN`. Use `⟨{ O := T₀.V ioO := io₀ eO := 1 overO := hov J := Σ j, J' j A := fun j => A j.1 j.2 ft := fun j => (hA j.1 j.2).1 flat := fun j => (hA j.1 j.2).2.1 ic := fun j => (hA j.1 j.2).2.2 ch := fun j f => α j.1 j.2 (evR Xo c f (P j.1).yg) Eb := fun j => bdry (P j.1) (α j.1 j.2) Eb_ne := …` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨_, T, io, d, ho, y, -, η, -, rfl⟩, rfl⟩`.

Use `letI := io.toAlgebra`. Establish `hβT : ∀ a, io ((la.valuation c.F).valuationSubring.subtype a) ∈ imageVal T.V T.Fr` using `fun a => (mem_imageVal _).2 (mem_range_of_overLa ho a)`. Take `⟨j, hj⟩` from `hP T.Fr (imageVal T.V T.Fr) hβT y.1`. Take `⟨e, he, ψ, hψK, hψg, hval⟩` from `values_of_catches (P j) hE hU T io y _ (fun x hx => (mem_imageVal _).1 hx) hβT hj`. Take `⟨g, χ, hloc, hχio, hχg, hϖ⟩` from `hinit T io d ho`.

Establish `hχg' : ∀ a, χ (algebraMap T₀.V T₀.Fr a) = algebraMap T.V T.Fr (g a)` using `fun a => RingHom.congr_fun hχg a`. Take `⟨j', φ, hφW, hφO, hφψ⟩` from `hcov j e he T.Fr (imageVal T.V T.Fr) χ ψ (fun k => (hψK k).trans (RingHom.congr_fun hχio k).symm) (fun a => (mem_imageVal _).2 ⟨g a, (hχg' a).symm⟩) hψg`. Take `⟨φ', hφ'⟩` from `exists_corestrict (V := T.V) φ fun x => (mem_imageVal _).1 (hφW x)`. Use `letI : Algebra T₀.V T.V := g.toAlgebra`. Establish `hc : ∀ a, φ' (algebraMap T₀.V (A j j') a) = g a` using `fun a => IsFractionRing.injective T.V T.Fr (by rw [hφ', hφO, hχg'])`.

Take `⟨hx, hch⟩` from `chV_point (P j) io₀ (α j j') hβ (hK j j') (hg j j') φ' e he ψ (fun r x s h => by rw [hφ', hφ']; exact hφψ r x s h) (fun a ha h => by`. Use `hφ' (algebraMap T₀.V (A j j') a)` as an intermediate fact. Rewrite `this` using `[h, map_zero, hφO, eq_comm, map_eq_zero]`. Conclude with `ha (by simpa using this))`. Use `⟨⟨j, j'⟩, T.V, inferInstance, inferInstance, inferInstance, inferInstance, { φ' with commutes' := hc }, io, d, ho, hx, fun ϖ h => ?_, ?_, fun a n f hf => ?_⟩` and prove the remaining obligations.

Rewrite using `[Nat.cast_one, mul_one]`. Conclude with `hϖ ϖ h`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha hu`. Conclude with `ha (hloc.map_nonunit a (by rw [← hc]; exact hu))`.

Take `⟨r, hr, hv⟩` from `hval a n f hf`. Express the relevant statement in the definitionally equal form `ChV φ' d (α j j' (evR Xo c f (P j).yg)) (nval T.V d (evI y f))`. Rewrite using `[hr, hv]`. Conclude with `hch d r`. Introduce and unpack `_ ⟨T, io, y, htriv, rfl⟩`.

It suffices to establish `h : ∃ (j : Σ j, J' j) (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra T₀.V V) (φ : A j.1 j.2 →ₐ[T₀.V] V), (∀ ϖ : T₀.V, Irreducible ϖ → Ideal.span {algebraMap T₀.V (A j.1 j.2) ϖ} ⊔ (IsLocalRing.maximalIdeal V).comap φ.toRingHom ≠ ⊤) ∧ (∀ ϖ …`. Take `⟨V, _, _, _, i', χ, hv, hι⟩` from `exists_unramified_of_trivial io₀ io htriv`. Set `ι : T₀.Fr →+* FractionRing V` to `(algebraMap V (FractionRing V)).comp χ`. Use `replace hι : ∀ k, i' (io k) = ι (io₀ k) := hι`. Take `⟨W, hWle, hWO, hWm⟩` from `GlobalTheory.exists_valuationSubring_le_dominating_of_fractionField T₀.V T₀.Fr (FractionRing V) ι (imageVal V (FractionRing V)) (fun x => (mem_imageVal _).2 ⟨χ x, rfl⟩)`.

Use `letI := io.toAlgebra`. Establish `hβT : ∀ a, io ((la.valuation c.F).valuationSubring.subtype a) ∈ W.comap i'` using `fun a => by`. Take `⟨x, hx⟩` from `hβ a`. Rewrite using `[ValuationSubring.mem_comap, hι, ← hx]`. Conclude with `hWO x`.

Take `⟨j, hj⟩` from `hP T.Fr (W.comap i') hβT y.1`. Take `⟨e, he, ψ, hψK, hψg, hval⟩` from `values_of_catches (P j) hE hU T io y _ (fun x hx => by`. Use `(mem_range_iff_vV_nonneg _).1 ((mem_imageVal _).1 (hWle hx))` as an intermediate fact. Rewrite `this` using `[hv, Nat.cast_one, one_mul]`. Conclude with `(mem_range_iff_vV_nonneg _).2 this) hβT hj`.

Take `⟨j', φ, hφW, hφO, hφψ⟩` from `hcov j e he (FractionRing V) W ι (i'.comp ψ) (fun k => by rw [RingHom.comp_apply, hψK, hι]) hWO hψg`. Take `⟨φ', hφ'⟩` from `exists_corestrict (V := V) φ fun x => (mem_imageVal _).1 (hWle (hφW x))`. Use `letI : Algebra T₀.V V := (χ.comp (algebraMap T₀.V T₀.Fr)).toAlgebra`. Establish `hc : ∀ a, φ' (algebraMap T₀.V (A j j') a) = χ (algebraMap T₀.V T₀.Fr a)` using `fun a => IsFractionRing.injective V (FractionRing V) (by rw [hφ', hφO]; rfl)`. Take `⟨hx, hch⟩` from `chV_point (P j) io₀ (α j j') hβ (hK j j') (hg j j') φ' e he (i'.comp ψ) (fun r x s h => by rw [hφ', hφ']; exact hφψ r x s h) (fun a ha h => by`.

Use `hφ' (algebraMap T₀.V (A j j') a)` as an intermediate fact. Rewrite `this` using `[h, map_zero, hφO, eq_comm, map_eq_zero]`. Conclude with `ha (by simpa using this))`. Use `⟨⟨j, j'⟩, V, inferInstance, inferInstance, inferInstance, inferInstance, { φ' with commutes' := hc }, fun ϖ h => ?_, fun ϖ h => ?_, hx, fun a n f hf => ?_⟩` and prove the remaining obligations. Use `sup_ne_top_of_nonunits φ' W hWle (fun x => by rw [hφ']; exact hφW x) _ ?_` and prove the remaining obligations.

Rewrite using `[hφ']`. Use `hWm ϖ h.not_isUnit` as an intermediate fact. Rewrite `this` using `[← hφO]`. Conclude with `this`. Use `IsUnit.map χ (IsUnit.mk0 (algebraMap T₀.V T₀.Fr ϖ) ?_)` and prove the remaining obligations.

Simplify using `using h.ne_zero`. Take `⟨r, hr', hv'⟩` from `hval a n f hf`. Express the relevant statement in the definitionally equal form `ChV φ' 1 (α j j' (evR Xo c f (P j).yg)) (nval T.V 1 (evI y f))`. Rewrite using `[hr', hv', ← nval_bc i' one_pos hv]`. Conclude with `hch 1 r`.

Introduce `m ws hws choose k hk using fun j : Σ j, J' j => family_chart (P j.1) io₀ (α j.1 j.2) (hK j.1 j.2) (hg j.1 j.2) hβ (hws j.1)`. Conclude with `⟨k, hk⟩`.
-/
theorem exists_scharts_of_covers :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → IntDiagUnit Xo c → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (J : Type) [Finite J] (P : J → PChart Xo c (la.valuation c.F).valuationSubring.subtype), Covers P → ∃ S : SCharts Xo c la, S.CovQ ∧ ∀ (m : ℕ) (ws : Fin m → Rul Xo c), (∀ j, (P j).Fam ws) → S.FamW ws := by
  intro E _ _ _ H Dw l Xo c hE hU la J _ P hP
  obtain ⟨T₀, io₀, hov, hfin, hinit⟩ := exists_initial_completion c.F la
  have hβ := mem_range_of_overLa hov
  have hN := fun j => GlobalTheory.exists_normal_charts_over_dvr c.F (P j).Ω T₀.V io₀ (P j).gens (P j).es
    (P j).frac (fun e he => ⟨((P j).es_mem e he).1, Subring.closure_mono (by
      refine Set.union_subset_union_left _ ?_
      rintro _ ⟨a, rfl⟩
      exact ⟨_, hβ a, rfl⟩) ((P j).es_mem e he).2⟩) (P j).sm
  choose J' finJ A acr adom alg α hA hK hg hcov using hN
  refine ⟨{ O := T₀.V
            ioO := io₀
            eO := 1
            overO := hov
            J := Σ j, J' j
            A := fun j => A j.1 j.2
            ft := fun j => (hA j.1 j.2).1
            flat := fun j => (hA j.1 j.2).2.1
            ic := fun j => (hA j.1 j.2).2.2
            ch := fun j f => α j.1 j.2 (evR Xo c f (P j.1).yg)
            Eb := fun j => bdry (P j.1) (α j.1 j.2)
            Eb_ne := fun j => bdry_ne_bot (P j.1) io₀ _ hβ (hK j.1 j.2) (hg j.1 j.2)
            reg := fun j a n f hf => regular_bdry (P j.1) io₀ _ (hK j.1 j.2) (hg j.1 j.2)
              (fun e he => by rw [evR_generic (P j.1) hE hf e he]; exact Subtype.property _)
            pts := fun j V _ _ _ _ _ φ hφ => points_chart (P j.1) io₀ _ hβ (hK j.1 j.2)
              (hg j.1 j.2) hE hfin hov V φ hφ
            cover := ?_ }, ?_, ?_⟩
  · rintro _ ⟨⟨_, T, io, d, ho, y, -, η, -, rfl⟩, rfl⟩
    letI := io.toAlgebra
    have hβT : ∀ a, io ((la.valuation c.F).valuationSubring.subtype a) ∈ imageVal T.V T.Fr :=
      fun a => (mem_imageVal _).2 (mem_range_of_overLa ho a)
    obtain ⟨j, hj⟩ := hP T.Fr (imageVal T.V T.Fr) hβT y.1
    obtain ⟨e, he, ψ, hψK, hψg, hval⟩ := values_of_catches (P j) hE hU T io y _
      (fun x hx => (mem_imageVal _).1 hx) hβT hj
    obtain ⟨g, χ, hloc, hχio, hχg, hϖ⟩ := hinit T io d ho
    have hχg' : ∀ a, χ (algebraMap T₀.V T₀.Fr a) = algebraMap T.V T.Fr (g a) :=
      fun a => RingHom.congr_fun hχg a
    obtain ⟨j', φ, hφW, hφO, hφψ⟩ := hcov j e he T.Fr (imageVal T.V T.Fr) χ ψ
      (fun k => (hψK k).trans (RingHom.congr_fun hχio k).symm)
      (fun a => (mem_imageVal _).2 ⟨g a, (hχg' a).symm⟩) hψg
    obtain ⟨φ', hφ'⟩ := exists_corestrict (V := T.V) φ fun x => (mem_imageVal _).1 (hφW x)
    letI : Algebra T₀.V T.V := g.toAlgebra
    have hc : ∀ a, φ' (algebraMap T₀.V (A j j') a) = g a := fun a =>
      IsFractionRing.injective T.V T.Fr (by rw [hφ', hφO, hχg'])
    obtain ⟨hx, hch⟩ := chV_point (P j) io₀ (α j j') hβ (hK j j') (hg j j') φ' e he ψ
      (fun r x s h => by rw [hφ', hφ']; exact hφψ r x s h)
      (fun a ha h => by
        have := hφ' (algebraMap T₀.V (A j j') a)
        rw [h, map_zero, hφO, eq_comm, map_eq_zero] at this
        exact ha (by simpa using this))
    refine ⟨⟨j, j'⟩, T.V, inferInstance, inferInstance, inferInstance, inferInstance,
      { φ' with commutes' := hc }, io, d, ho, hx, fun ϖ h => ?_, ?_, fun a n f hf => ?_⟩
    · rw [Nat.cast_one, mul_one]; exact hϖ ϖ h
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha hu
      exact ha (hloc.map_nonunit a (by rw [← hc]; exact hu))
    · obtain ⟨r, hr, hv⟩ := hval a n f hf
      change ChV φ' d (α j j' (evR Xo c f (P j).yg)) (nval T.V d (evI y f))
      rw [hr, hv]
      exact hch d r
  · rintro _ ⟨T, io, y, htriv, rfl⟩
    suffices h : ∃ (j : Σ j, J' j) (V : Type) (_ : CommRing V) (_ : IsDomain V)
        (_ : IsDiscreteValuationRing V) (_ : Algebra T₀.V V) (φ : A j.1 j.2 →ₐ[T₀.V] V),
        (∀ ϖ : T₀.V, Irreducible ϖ → Ideal.span {algebraMap T₀.V (A j.1 j.2) ϖ} ⊔
          (IsLocalRing.maximalIdeal V).comap φ.toRingHom ≠ ⊤) ∧
        (∀ ϖ : T₀.V, Irreducible ϖ → IsUnit (algebraMap T₀.V V ϖ)) ∧
        (∃ x ∈ bdry (P j.1) (α j.1 j.2), φ x ≠ 0) ∧
        ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n,
          ChV φ.toRingHom 1 (α j.1 j.2 (evR Xo c f (P j.1).yg)) (nval T.V 1 (evI y f)) from h
    obtain ⟨V, _, _, _, i', χ, hv, hι⟩ := exists_unramified_of_trivial io₀ io htriv
    let ι : T₀.Fr →+* FractionRing V := (algebraMap V (FractionRing V)).comp χ
    replace hι : ∀ k, i' (io k) = ι (io₀ k) := hι
    obtain ⟨W, hWle, hWO, hWm⟩ := GlobalTheory.exists_valuationSubring_le_dominating_of_fractionField T₀.V
      T₀.Fr (FractionRing V) ι (imageVal V (FractionRing V))
      (fun x => (mem_imageVal _).2 ⟨χ x, rfl⟩)
    letI := io.toAlgebra
    have hβT : ∀ a, io ((la.valuation c.F).valuationSubring.subtype a) ∈ W.comap i' := fun a => by
      obtain ⟨x, hx⟩ := hβ a
      rw [ValuationSubring.mem_comap, hι, ← hx]
      exact hWO x
    obtain ⟨j, hj⟩ := hP T.Fr (W.comap i') hβT y.1
    obtain ⟨e, he, ψ, hψK, hψg, hval⟩ := values_of_catches (P j) hE hU T io y _
      (fun x hx => by
        have := (mem_range_iff_vV_nonneg _).1 ((mem_imageVal _).1 (hWle hx))
        rw [hv, Nat.cast_one, one_mul] at this
        exact (mem_range_iff_vV_nonneg _).2 this) hβT hj
    obtain ⟨j', φ, hφW, hφO, hφψ⟩ := hcov j e he (FractionRing V) W ι (i'.comp ψ)
      (fun k => by rw [RingHom.comp_apply, hψK, hι]) hWO hψg
    obtain ⟨φ', hφ'⟩ := exists_corestrict (V := V) φ fun x => (mem_imageVal _).1 (hWle (hφW x))
    letI : Algebra T₀.V V := (χ.comp (algebraMap T₀.V T₀.Fr)).toAlgebra
    have hc : ∀ a, φ' (algebraMap T₀.V (A j j') a) = χ (algebraMap T₀.V T₀.Fr a) := fun a =>
      IsFractionRing.injective V (FractionRing V) (by rw [hφ', hφO]; rfl)
    obtain ⟨hx, hch⟩ := chV_point (P j) io₀ (α j j') hβ (hK j j') (hg j j') φ' e he (i'.comp ψ)
      (fun r x s h => by rw [hφ', hφ']; exact hφψ r x s h)
      (fun a ha h => by
        have := hφ' (algebraMap T₀.V (A j j') a)
        rw [h, map_zero, hφO, eq_comm, map_eq_zero] at this
        exact ha (by simpa using this))
    refine ⟨⟨j, j'⟩, V, inferInstance, inferInstance, inferInstance, inferInstance,
      { φ' with commutes' := hc }, fun ϖ h => ?_, fun ϖ h => ?_, hx, fun a n f hf => ?_⟩
    · refine sup_ne_top_of_nonunits φ' W hWle (fun x => by rw [hφ']; exact hφW x) _ ?_
      rw [hφ']
      have := hWm ϖ h.not_isUnit
      rw [← hφO] at this
      exact this
    · refine IsUnit.map χ (IsUnit.mk0 (algebraMap T₀.V T₀.Fr ϖ) ?_)
      simpa using h.ne_zero
    · obtain ⟨r, hr', hv'⟩ := hval a n f hf
      change ChV φ' 1 (α j j' (evR Xo c f (P j).yg)) (nval T.V 1 (evI y f))
      rw [hr', hv', ← nval_bc i' one_pos hv]
      exact hch 1 r
  · intro m ws hws
    choose k hk using fun j : Σ j, J' j =>
      family_chart (P j.1) io₀ (α j.1 j.2) (hK j.1 j.2) (hg j.1 j.2) hβ (hws j.1)
    exact ⟨k, hk⟩

end GlobalTheory.Reg
