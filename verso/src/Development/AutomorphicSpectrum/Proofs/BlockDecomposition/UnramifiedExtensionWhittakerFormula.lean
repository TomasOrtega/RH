import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.AutomorphicForms.MacdonaldWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdEqZeroOfModulusEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantSeparatingSubalgebraStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.InertAsm.Decomp

section Gen

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/- English proof (translation)
Use `set π : K := (unifUnit K : K) with hπ`. Establish `hm : modulus π < 1`. Rewrite using `[hπ, modulus_of_ne_zero (unifUnit K).ne_zero, ord_unifUnit, _root_.zpow_neg, zpow_one]`. Conclude with `inv_lt_one_of_one_lt₀ (one_lt_residueCard_nnreal (K := K))`. Establish `hπO : π ∈ 𝒪[K]` using `modulus_le_one_iff.1 hm.le`.

Establish `hpow : ∀ n : ℕ, modulus (π ^ n) = modulus π ^ n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [modulus_one]`. Consider the case `succ n ih => rw [pow_succ, modulus_mul, ih, pow_succ]`.

Set `U : ℕ → Set K` to `fun n => {x | x * π ^ n ∈ 𝒪[K]}`. Establish `ho : IsOpen (𝒪[K] : Set K)` using `Valuation.isOpen_integer`. Establish `hUo : ∀ n, IsOpen (U n)` using `fun n => ho.preimage (continuous_mul_right _)`. Establish `hcov : S ⊆ ⋃ n, U n`. Introduce `x _`.

Use `Set.mem_iUnion.2 ?_` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Conclude with `⟨0, by simp [U, hx, zero_mem]⟩`. Establish `hmx : 0 < modulus x` using `pos_iff_ne_zero.2 (modulus_ne_zero hx)`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (inv_pos.2 hmx) hm`.

Use `⟨n, modulus_le_one_iff.1 ?_⟩` and prove the remaining obligations. Rewrite using `[modulus_mul, hpow]`. Combine the equalities or inequalities in the displayed calculation. Establish `hmono : Monotone U` using `monotone_nat_of_le_succ fun n x hx => by`. Establish `h : x * π ^ (n + 1) = (x * π ^ n) * π` using `by rw [pow_succ, mul_assoc]`.

Use `show x * π ^ (n + 1) ∈ 𝒪[K]`. Rewrite using `[h]`. Conclude with `mul_mem hx hπO`. Take `⟨n, hn⟩` from `hS.elim_directed_cover U hUo hcov hmono.directed_le`. Use `⟨unifUnit K ^ n, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_pow_eq_pow_val]`. Conclude with `hn hx`.
-/
theorem exists_scale {S : Set K} (hS : IsCompact S) : ∃ s : Kˣ, ∀ x ∈ S, x * (s : K) ∈ 𝒪[K] := by
  set π : K := (unifUnit K : K) with hπ
  have hm : modulus π < 1 := by
    rw [hπ, modulus_of_ne_zero (unifUnit K).ne_zero, ord_unifUnit, _root_.zpow_neg, zpow_one]
    exact inv_lt_one_of_one_lt₀ (one_lt_residueCard_nnreal (K := K))
  have hπO : π ∈ 𝒪[K] := modulus_le_one_iff.1 hm.le
  have hpow : ∀ n : ℕ, modulus (π ^ n) = modulus π ^ n := by
    intro n
    induction n with
    | zero => simp [modulus_one]
    | succ n ih => rw [pow_succ, modulus_mul, ih, pow_succ]
  let U : ℕ → Set K := fun n => {x | x * π ^ n ∈ 𝒪[K]}
  have ho : IsOpen (𝒪[K] : Set K) := Valuation.isOpen_integer
  have hUo : ∀ n, IsOpen (U n) := fun n => ho.preimage (continuous_mul_right _)
  have hcov : S ⊆ ⋃ n, U n := by
    intro x _
    refine Set.mem_iUnion.2 ?_
    by_cases hx : x = 0
    · exact ⟨0, by simp [U, hx, zero_mem]⟩
    have hmx : 0 < modulus x := pos_iff_ne_zero.2 (modulus_ne_zero hx)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hmx) hm
    refine ⟨n, modulus_le_one_iff.1 ?_⟩
    rw [modulus_mul, hpow]
    calc modulus x * modulus π ^ n ≤ modulus x * (modulus x)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hmx.ne'
  have hmono : Monotone U := monotone_nat_of_le_succ fun n x hx => by
    have h : x * π ^ (n + 1) = (x * π ^ n) * π := by rw [pow_succ, mul_assoc]
    show x * π ^ (n + 1) ∈ 𝒪[K]
    rw [h]
    exact mul_mem hx hπO
  obtain ⟨n, hn⟩ := hS.elim_directed_cover U hUo hcov hmono.directed_le
  refine ⟨unifUnit K ^ n, fun x hx => ?_⟩
  rw [Units.val_pow_eq_pow_val]
  exact hn hx

/- English proof (translation)
Use `(IsLocallyConstant.iff_eventually_eq _).mpr fun a => ?_` and prove the remaining obligations. Establish `h` using `isTrivialOn_addCharConductor hχ.1 hχ.2.1`. Establish `ho : IsOpen {y : K | y - a ∈ valBall K (addCharConductor χ)}` using `(isOpen_valBall (addCharConductor χ)).preimage (continuous_id.sub continuous_const)`. Use `filter_upwards [ho.mem_nhds (show a - a ∈ valBall K (addCharConductor χ) by`. Rewrite using `[sub_self]`.

Conclude with `zero_mem _)] with y hy`. Establish `h1 : χ (y - a) = 1` using `h _ hy`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isLocallyConstant_char {χ : AddChar K Circle} (hχ : IsStd χ) :
    IsLocallyConstant (χ : K → Circle) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun a => ?_
  have h := isTrivialOn_addCharConductor hχ.1 hχ.2.1
  have ho : IsOpen {y : K | y - a ∈ valBall K (addCharConductor χ)} :=
    (isOpen_valBall (addCharConductor χ)).preimage (continuous_id.sub continuous_const)
  filter_upwards [ho.mem_nhds (show a - a ∈ valBall K (addCharConductor χ) by
    rw [sub_self]; exact zero_mem _)] with y hy
  have h1 : χ (y - a) = 1 := h _ hy
  calc χ y = χ ((y - a) + a) := by rw [sub_add_cancel]
    _ = χ a := by rw [AddChar.map_add_eq_mul, h1, one_mul]

end Gen

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)]

open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep (modulus_norm)

/- English proof (translation)
Establish `hz : ∀ {x : E}, Algebra.norm F x = 0 → x = 0` using `fun hx => Algebra.norm_eq_zero_iff.1 hx`. Establish `hz0 : Algebra.norm F (0 : E) = 0` using `Algebra.norm_eq_zero_iff.2 rfl`. Distinguish the cases in `hp : p = 0`. Substitute `hp` using the available equality. Rewrite using `[hz (h.symm.trans hz0)]`.

Establish `hq : q ≠ 0` using `fun hq => hp (hz (by rw [h, hq, hz0]))`. Establish `hNp : Algebra.norm F p ≠ 0` using `Algebra.norm_ne_zero_iff.2 hp`. Set `u : Eˣ` to `Units.mk0 (q / p) (div_ne_zero hq hp)`. Establish `hu : Algebra.norm F (u : E) = 1`. Use `mul_right_cancel₀ hNp ?_` and prove the remaining obligations.

Rewrite using `[one_mul, ← map_mul, h]`. Simplify using `only [u, Units.val_mk0, div_mul_cancel₀ q hp]`. Establish `hm : modulus (u : E) = 1`. Rewrite using `[← modulus_norm (K := F), hu, modulus_one]`. Establish `h1 : c u = 1`.

Use `char_congr c hc (u := u) (v := 1) (by simpa using hm)` as an intermediate fact. Simplify using `using this`. Establish `h2` using `hΦ.2.2 u hu p`. Rewrite `h2` using `[h1, inv_one, Units.val_one, one_mul]`. Rewrite using `[← h2]`.

Simplify using `only [u, Units.val_mk0, mul_div_cancel₀ q hp]`.
-/
theorem eq_of_norm_eq {c : Eˣ →* ℂˣ} (hc : IsUnramifiedChar c) {Φ : E → ℂ}
    (hΦ : Φ ∈ GL2LocalData.SBc F E c) {p q : E} (h : Algebra.norm F p = Algebra.norm F q) : Φ p = Φ q := by
  have hz : ∀ {x : E}, Algebra.norm F x = 0 → x = 0 := fun hx => Algebra.norm_eq_zero_iff.1 hx
  have hz0 : Algebra.norm F (0 : E) = 0 := Algebra.norm_eq_zero_iff.2 rfl
  by_cases hp : p = 0
  · subst hp
    rw [hz (h.symm.trans hz0)]
  have hq : q ≠ 0 := fun hq => hp (hz (by rw [h, hq, hz0]))
  have hNp : Algebra.norm F p ≠ 0 := Algebra.norm_ne_zero_iff.2 hp
  let u : Eˣ := Units.mk0 (q / p) (div_ne_zero hq hp)
  have hu : Algebra.norm F (u : E) = 1 := by
    refine mul_right_cancel₀ hNp ?_
    rw [one_mul, ← map_mul, h]
    simp only [u, Units.val_mk0, div_mul_cancel₀ q hp]
  have hm : modulus (u : E) = 1 := by
    rw [← modulus_norm (K := F), hu, modulus_one]
  have h1 : c u = 1 := by
    have := char_congr c hc (u := u) (v := 1) (by simpa using hm)
    simpa using this
  have h2 := hΦ.2.2 u hu p
  rw [h1, inv_one, Units.val_one, one_mul] at h2
  rw [← h2]
  simp only [u, Units.val_mk0, mul_div_cancel₀ q hp]

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_scale (K := E) hΦ.2.1`. Set `Bs : Set E` to `{x | x * (s : E) ∈ 𝒪[E]}`. Establish `hO : IsCompact (𝒪[E] : Set E)` using `IsNonarchimedeanLocalField.isCompact_closedBall E 1`. Establish `hBc : IsCompact Bs` using `(Homeomorph.mulRight₀ (s : E) s.ne_zero).isCompact_preimage.2 hO`. Use `haveI : CompactSpace Bs := isCompact_iff_compactSpace.1 hBc`.

Set `e : F → Bs → ℂ` to `fun y x => (χ (y * Algebra.norm F (x : E)) : ℂ)`. Set `V : Submodule ℂ (Bs → ℂ)` to `Submodule.span ℂ (Set.range e)`. Establish `hone : (1 : Bs → ℂ) ∈ V` using `Submodule.subset_span ⟨0, by funext x; simp [e]⟩`. Establish `hemul : ∀ y y', e y * e y' = e (y + y')` using `fun y y' => by`. Use function extensionality and compare the values at `x`.

Simplify using `[e, add_mul, AddChar.map_add_eq_mul]`. Establish `hmul : ∀ f ∈ V, ∀ g ∈ V, f * g ∈ V`. Introduce `f hf g hg`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`.

Take `⟨y, rfl⟩` from `hf`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g hg`. Take `⟨y', rfl⟩` from `hg`. Rewrite using `[hemul]`.

Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [mul_add]`. Conclude with `V.add_mem ha hb`. Consider the case `smul t a _ ha => rw [mul_smul_comm]`.

Conclude with `V.smul_mem _ ha`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [add_mul]`. Conclude with `V.add_mem ha hb`. Consider the case `smul t a _ ha => rw [smul_mul_assoc]`.

Conclude with `V.smul_mem _ ha`. Establish `hNc : Continuous (Algebra.norm F : E → F)` using `GroundTheory.LocalField.continuous_algebraNorm F E`. Establish `hlc : ∀ f ∈ V, IsLocallyConstant f`. Introduce `f hf`. Proceed by induction on `hf using Submodule.span_induction with`.

Consider the case `mem f hf`. Take `⟨y, rfl⟩` from `hf`. Establish `hcont : Continuous fun x : Bs => y * Algebra.norm F (x : E)` using `continuous_const.mul (hNc.comp continuous_subtype_val)`. Conclude with `((isLocallyConstant_char hχ).comp_continuous hcont).comp (fun z : Circle => (z : ℂ))`. Consider the case `zero => exact IsLocallyConstant.const 0`.

Consider the case `add a b _ _ ha hb => exact ha.add hb`. Consider the case `smul t a _ ha => exact (IsLocallyConstant.const t).mul ha`. Establish `hsep : ∀ p q : Bs, Φ p ≠ Φ q → ∃ f ∈ V, f p ≠ f q`. Introduce `p q hpq`. Establish `hd : Algebra.norm F (p : E) - Algebra.norm F (q : E) ≠ 0` using `fun h => hpq (eq_of_norm_eq hc hΦ (sub_eq_zero.1 h))`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, χ t ≠ 1 := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Conclude with `hχ.2.1 (by ext x; simp [hall x])`. Use `set d := Algebra.norm F (p : E) - Algebra.norm F (q : E) with hdd`.

Use `⟨e (t / d), Submodule.subset_span ⟨_, rfl⟩, fun h => ht ?_⟩` and prove the remaining obligations. Establish `h1 : χ (t / d * Algebra.norm F (p : E)) = χ (t / d * Algebra.norm F (q : E))` using `Circle.coe_injective h`. Establish `h2 : t / d * Algebra.norm F (p : E) = t + t / d * Algebra.norm F (q : E)`. Establish `: t = t / d * d` using `(div_mul_cancel₀ t hd).symm`. Rewrite `this`, the goal using `[hdd]`.

Take the linear combination `(-1 : F) * this`. Rewrite `h1` using `[h2, AddChar.map_add_eq_mul]`. Conclude with `mul_right_cancel (h1.trans (one_mul _).symm)`. Establish `hmem : (fun x : Bs => Φ x) ∈ V` using `GlobalTheory.T.locally_constant_separating_subalgebra Bs V hone hmul hlc (fun x : Bs => Φ x) (hΦ.1.comp_continuous continuous_subtype_val) hsep`. Take `⟨w, hw⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 hmem`.

Set `eq` to `w.support.equivFin`. Use `⟨s, w.support.card, fun j => w (eq.symm j), fun j => (eq.symm j : F), fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x * (s : E) ∈ 𝒪[E]`. Establish `h1 : Φ x = (w.sum fun i a => a • e i) ⟨x, hx⟩` using `by rw [hw]`. Establish `h2 : (intInd (x * (s : E)) : ℂ) = 1` using `by simp [intInd, hx]`.

Rewrite using `[h1, Finsupp.sum, Finset.sum_apply, ← Finset.sum_coe_sort w.support, ← Equiv.sum_comp eq.symm]`. Simplify using `[e, h2]`. Establish `h0 : Φ x = 0`. Assume the negation of the conclusion as `h`. Conclude with `hx (hs x (subset_tsupport _ h))`.

Establish `h2 : (intInd (x * (s : E)) : ℂ) = 0` using `by simp [intInd, hx]`. Simplify using `[h0, h2]`.
-/
theorem sub_eq_neg_smul_add_of_sub_smul_eq (χ : AddChar F Circle) (hχ : IsStd χ) (c : Eˣ →* ℂˣ) (hc : IsUnramifiedChar c)
    (Φ : E → ℂ) (hΦ : Φ ∈ GL2LocalData.SBc F E c) :
    ∃ (s : Eˣ) (n : ℕ) (a : Fin n → ℂ) (y : Fin n → F), ∀ x, Φ x =
      ∑ j, a j * ((χ (y j * Algebra.norm F x) : ℂ) * intInd (x * (s : E))) := by
  obtain ⟨s, hs⟩ := exists_scale (K := E) hΦ.2.1
  let Bs : Set E := {x | x * (s : E) ∈ 𝒪[E]}
  have hO : IsCompact (𝒪[E] : Set E) := IsNonarchimedeanLocalField.isCompact_closedBall E 1
  have hBc : IsCompact Bs :=
    (Homeomorph.mulRight₀ (s : E) s.ne_zero).isCompact_preimage.2 hO
  haveI : CompactSpace Bs := isCompact_iff_compactSpace.1 hBc
  let e : F → Bs → ℂ := fun y x => (χ (y * Algebra.norm F (x : E)) : ℂ)
  let V : Submodule ℂ (Bs → ℂ) := Submodule.span ℂ (Set.range e)
  have hone : (1 : Bs → ℂ) ∈ V := Submodule.subset_span ⟨0, by funext x; simp [e]⟩
  have hemul : ∀ y y', e y * e y' = e (y + y') := fun y y' => by
    funext x
    simp [e, add_mul, AddChar.map_add_eq_mul]
  have hmul : ∀ f ∈ V, ∀ g ∈ V, f * g ∈ V := by
    intro f hf g hg
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨y, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨y', rfl⟩ := hg
        rw [hemul]
        exact Submodule.subset_span ⟨_, rfl⟩
      | zero => simp
      | add a b _ _ ha hb => rw [mul_add]; exact V.add_mem ha hb
      | smul t a _ ha => rw [mul_smul_comm]; exact V.smul_mem _ ha
    | zero => simp
    | add a b _ _ ha hb => rw [add_mul]; exact V.add_mem ha hb
    | smul t a _ ha => rw [smul_mul_assoc]; exact V.smul_mem _ ha
  have hNc : Continuous (Algebra.norm F : E → F) := GroundTheory.LocalField.continuous_algebraNorm F E
  have hlc : ∀ f ∈ V, IsLocallyConstant f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨y, rfl⟩ := hf
      have hcont : Continuous fun x : Bs => y * Algebra.norm F (x : E) :=
        continuous_const.mul (hNc.comp continuous_subtype_val)
      exact ((isLocallyConstant_char hχ).comp_continuous hcont).comp (fun z : Circle => (z : ℂ))
    | zero => exact IsLocallyConstant.const 0
    | add a b _ _ ha hb => exact ha.add hb
    | smul t a _ ha => exact (IsLocallyConstant.const t).mul ha
  have hsep : ∀ p q : Bs, Φ p ≠ Φ q → ∃ f ∈ V, f p ≠ f q := by
    intro p q hpq
    have hd : Algebra.norm F (p : E) - Algebra.norm F (q : E) ≠ 0 := fun h =>
      hpq (eq_of_norm_eq hc hΦ (sub_eq_zero.1 h))
    obtain ⟨t, ht⟩ : ∃ t, χ t ≠ 1 := by
      by_contra hall
      push_neg at hall
      exact hχ.2.1 (by ext x; simp [hall x])
    set d := Algebra.norm F (p : E) - Algebra.norm F (q : E) with hdd
    refine ⟨e (t / d), Submodule.subset_span ⟨_, rfl⟩, fun h => ht ?_⟩
    have h1 : χ (t / d * Algebra.norm F (p : E)) = χ (t / d * Algebra.norm F (q : E)) :=
      Circle.coe_injective h
    have h2 : t / d * Algebra.norm F (p : E) = t + t / d * Algebra.norm F (q : E) := by
      have : t = t / d * d := (div_mul_cancel₀ t hd).symm
      rw [hdd] at this ⊢
      linear_combination (-1 : F) * this
    rw [h2, AddChar.map_add_eq_mul] at h1
    exact mul_right_cancel (h1.trans (one_mul _).symm)
  have hmem : (fun x : Bs => Φ x) ∈ V :=
    GlobalTheory.T.locally_constant_separating_subalgebra Bs V hone hmul hlc (fun x : Bs => Φ x)
      (hΦ.1.comp_continuous continuous_subtype_val) hsep
  obtain ⟨w, hw⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  let eq := w.support.equivFin
  refine ⟨s, w.support.card, fun j => w (eq.symm j), fun j => (eq.symm j : F), fun x => ?_⟩
  by_cases hx : x * (s : E) ∈ 𝒪[E]
  · have h1 : Φ x = (w.sum fun i a => a • e i) ⟨x, hx⟩ := by rw [hw]
    have h2 : (intInd (x * (s : E)) : ℂ) = 1 := by simp [intInd, hx]
    rw [h1, Finsupp.sum, Finset.sum_apply, ← Finset.sum_coe_sort w.support,
      ← Equiv.sum_comp eq.symm]
    simp [e, h2]
  · have h0 : Φ x = 0 := by
      by_contra h
      exact hx (hs x (subset_tsupport _ h))
    have h2 : (intInd (x * (s : E)) : ℂ) = 0 := by simp [intInd, hx]
    simp [h0, h2]

end Main

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ h2 _ _ χ hχ c hc Φ hΦ`. Use `haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)`. Use `haveI : Algebra.IsSeparable F E := Algebra.IsAlgebraic.isSeparable_of_perfectField`. Conclude with `sub_eq_neg_smul_add_of_sub_smul_eq χ hχ c hc Φ hΦ`.
-/
theorem sbc_decomp : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ χ : AddChar F Circle, Ad3.IsStd χ → ∀ c : Eˣ →* ℂˣ, IsUnramifiedChar c → ∀ Φ ∈ GL2LocalData.SBc F E c, ∃ (s : Eˣ) (n : ℕ) (a : Fin n → ℂ) (y : Fin n → F), ∀ x, Φ x = ∑ j, a j * ((χ (y j * Algebra.norm F x) : ℂ) * intInd (x * (s : E))) := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ h2 _ _ χ hχ c hc Φ hΦ
  haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact sub_eq_neg_smul_add_of_sub_smul_eq χ hχ c hc Φ hΦ

end GlobalTheory.CompanionTheory.SphTheta.InertAsm.Decomp
