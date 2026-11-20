import Mathlib

namespace GlobalTheory.ClosedResidueExt

open Polynomial IsLocalRing

variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]

def Unram (π : W) (R : Subalgebra W Ω) : Prop :=
  (∀ x ∈ R, IsIntegral W x) ∧ (algebraMap W Ω π)⁻¹ ∉ R ∧
    ∀ x ∈ R, x ≠ 0 → ∃ (n : ℕ) (u : Ω), u ∈ R ∧ u⁻¹ ∈ R ∧ x = algebraMap W Ω π ^ n * u

/- English proof (translation)
The claim follows from `IsUnit.of_mul_eq_one ⟨u⁻¹, hu'⟩ (Subtype.ext (mul_inv_cancel₀ h0))`.
-/
theorem Unram.isUnit {R : Subalgebra W Ω} {u : Ω} (hu : u ∈ R) (hu' : u⁻¹ ∈ R) (h0 : u ≠ 0) :
    IsUnit (⟨u, hu⟩ : R) :=
  IsUnit.of_mul_eq_one ⟨u⁻¹, hu'⟩ (Subtype.ext (mul_inv_cancel₀ h0))

/- English proof (translation)
Establish `hx' : (x : Ω) ≠ 0` using `fun e => hx (Subtype.ext e)`. Take `⟨n, u, hu, hu', e⟩` from `h.2.2 x x.2 hx'`. Establish `h0 : u ≠ 0`. Introduce and unpack `rfl`. Conclude with `hx' (by simpa using e)`.

Use `⟨n, (Unram.isUnit hu hu' h0).unit, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `[e]`.
-/
theorem Unram.factor {π : W} {R : Subalgebra W Ω} (h : Unram π R) (x : R) (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : Rˣ), algebraMap W R π ^ n * u = x := by
  have hx' : (x : Ω) ≠ 0 := fun e => hx (Subtype.ext e)
  obtain ⟨n, u, hu, hu', e⟩ := h.2.2 x x.2 hx'
  have h0 : u ≠ 0 := by
    rintro rfl
    exact hx' (by simpa using e)
  refine ⟨n, (Unram.isUnit hu hu' h0).unit, Subtype.ext ?_⟩
  simp [e]

/- English proof (translation)
Establish `h0' : algebraMap W R π ≠ 0` using `fun e => h0 (congrArg Subtype.val e)`. Establish `hnu : ¬ IsUnit (algebraMap W R π)`. Introduce `hu`. Take `⟨v, hv⟩` from `hu.exists_right_inv`. Establish `hv' : algebraMap W Ω π * (v : Ω) = 1` using `congrArg Subtype.val hv`.

Conclude with `h.2.1 (eq_inv_of_mul_eq_one_right hv' ▸ v.2)`. Use `⟨hnu, fun a b hab => ?_⟩` and prove the remaining obligations. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `h0' (by simpa using hab)`.

Establish `hb : b ≠ 0`. Introduce and unpack `rfl`. Conclude with `h0' (by simpa using hab)`. Take `⟨n, u, rfl⟩` from `h.factor a ha`. Take `⟨m, v, rfl⟩` from `h.factor b hb`.

Break down `n with _ | n` into its components or cases. Use `left`. Simplify using the standard rewrite rules. Break down `m with _ | m` into its components or cases. Use `right`.

Simplify using the standard rewrite rules. It suffices to derive a contradiction. Use `hnu (IsUnit.of_mul_eq_one (algebraMap W R π ^ (n + m) * u * v) ?_)` and prove the remaining obligations. Use `mul_left_cancel₀ h0' ?_` and prove the remaining obligations. Rewrite using `[mul_one]`.

Use `conv_rhs => rw [hab]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Unram.irreducible {π : W} {R : Subalgebra W Ω} (h : Unram π R)
    (h0 : algebraMap W Ω π ≠ 0) : Irreducible (algebraMap W R π) := by
  have h0' : algebraMap W R π ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  have hnu : ¬ IsUnit (algebraMap W R π) := by
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv' : algebraMap W Ω π * (v : Ω) = 1 := congrArg Subtype.val hv
    exact h.2.1 (eq_inv_of_mul_eq_one_right hv' ▸ v.2)
  refine ⟨hnu, fun a b hab => ?_⟩
  have ha : a ≠ 0 := by
    rintro rfl
    exact h0' (by simpa using hab)
  have hb : b ≠ 0 := by
    rintro rfl
    exact h0' (by simpa using hab)
  obtain ⟨n, u, rfl⟩ := h.factor a ha
  obtain ⟨m, v, rfl⟩ := h.factor b hb
  rcases n with _ | n
  · left; simp
  rcases m with _ | m
  · right; simp
  exfalso
  refine hnu (IsUnit.of_mul_eq_one (algebraMap W R π ^ (n + m) * u * v) ?_)
  refine mul_left_cancel₀ h0' ?_
  rw [mul_one]
  conv_rhs => rw [hab]
  ring

/- English proof (translation)
The claim follows from `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, h.irreducible h0, fun {x} hx => h.factor x hx⟩`.
-/
theorem Unram.dvr {π : W} {R : Subalgebra W Ω} (h : Unram π R)
    (h0 : algebraMap W Ω π ≠ 0) : IsDiscreteValuationRing R :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, h.irreducible h0, fun {x} hx => h.factor x hx⟩

open Polynomial IsLocalRing in
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω] in
/- English proof (translation)
Take `⟨M, -, hM⟩` from `zorn_le_nonempty₀ {R : Subalgebra W Ω | _root_.GlobalTheory.ClosedResidueExt.Unram π R} (fun c hc hchain y hy => by`. Establish `hne : Nonempty c` using `⟨⟨y, hy⟩⟩`. Establish `hd : Directed (· ≤ ·) (fun R : c => (R : Subalgebra W Ω))` using `hchain.directed`. Establish `hmem : ∀ x ∈ ⨆ R : c, (R : Subalgebra W Ω), ∃ R : c, x ∈ (R : Subalgebra W Ω)` using `fun x hx => by`. Establish `: x ∈ (↑(⨆ R : c, (R : Subalgebra W Ω)) : Set Ω)` using `hx`.

Rewrite `this` using `[Subalgebra.coe_iSup_of_directed hd, Set.mem_iUnion]`. Conclude with `this`. Use `⟨⨆ R : c, (R : Subalgebra W Ω), ⟨fun x hx => ?_, fun hx => ?_, fun x hx hx0 => ?_⟩, fun R hR => le_iSup (fun R : c => (R : Subalgebra W Ω)) ⟨R, hR⟩⟩` and prove the remaining obligations. Take `⟨R, hR⟩` from `hmem x hx`. Conclude with `(hc R.2).1 x hR`.

Take `⟨R, hR⟩` from `hmem _ hx`. Conclude with `(hc R.2).2.1 hR`. Take `⟨R, hR⟩` from `hmem x hx`. Take `⟨n, u, hu, hu', e⟩` from `(hc R.2).2.2 x hR hx0`. Conclude with `⟨n, u, le_iSup (fun R : c => (R : Subalgebra W Ω)) R hu, le_iSup (fun R : c => (R : Subalgebra W Ω)) R hu', e⟩) ⊥ h0`.

Conclude with `⟨M, hM.prop, fun N hN hle => (hM.eq_of_le hN hle).symm⟩`.
-/
private lemma exists_maximal_unram_subalgebra (π : W) (h0 : _root_.GlobalTheory.ClosedResidueExt.Unram π (⊥ : Subalgebra W Ω)) :
    ∃ M : Subalgebra W Ω, _root_.GlobalTheory.ClosedResidueExt.Unram π M ∧
      ∀ N, _root_.GlobalTheory.ClosedResidueExt.Unram π N → M ≤ N → N = M := by
  obtain ⟨M, -, hM⟩ := zorn_le_nonempty₀ {R : Subalgebra W Ω | _root_.GlobalTheory.ClosedResidueExt.Unram π R}
    (fun c hc hchain y hy => by
    have hne : Nonempty c := ⟨⟨y, hy⟩⟩
    have hd : Directed (· ≤ ·) (fun R : c => (R : Subalgebra W Ω)) := hchain.directed
    have hmem : ∀ x ∈ ⨆ R : c, (R : Subalgebra W Ω), ∃ R : c, x ∈ (R : Subalgebra W Ω) := fun x hx => by
      have : x ∈ (↑(⨆ R : c, (R : Subalgebra W Ω)) : Set Ω) := hx
      rw [Subalgebra.coe_iSup_of_directed hd, Set.mem_iUnion] at this
      exact this
    refine ⟨⨆ R : c, (R : Subalgebra W Ω), ⟨fun x hx => ?_, fun hx => ?_, fun x hx hx0 => ?_⟩,
      fun R hR => le_iSup (fun R : c => (R : Subalgebra W Ω)) ⟨R, hR⟩⟩
    · obtain ⟨R, hR⟩ := hmem x hx
      exact (hc R.2).1 x hR
    · obtain ⟨R, hR⟩ := hmem _ hx
      exact (hc R.2).2.1 hR
    · obtain ⟨R, hR⟩ := hmem x hx
      obtain ⟨n, u, hu, hu', e⟩ := (hc R.2).2.2 x hR hx0
      exact ⟨n, u, le_iSup (fun R : c => (R : Subalgebra W Ω)) R hu,
        le_iSup (fun R : c => (R : Subalgebra W Ω)) R hu', e⟩) ⊥ h0
  exact ⟨M, hM.prop, fun N hN hle => (hM.eq_of_le hN hle).symm⟩

open Polynomial IsLocalRing in
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω] in
/- English proof (translation)
The claim follows from `have h : a * ⟨_, ha⟩ = 1 := Subtype.ext (by simp [mul_inv_cancel₀ ha0]) ⟨⟨a, ⟨_, ha⟩, h, by rw [mul_comm]; exact h⟩, rfl⟩`.
-/
private lemma isUnit_of_inv_mem_of_ne_zero {M : Subalgebra W Ω}
    (a : M) (ha : (a : Ω)⁻¹ ∈ M) (ha0 : (a : Ω) ≠ 0) : IsUnit a :=
  have h : a * ⟨_, ha⟩ = 1 := Subtype.ext (by simp [mul_inv_cancel₀ ha0])
  ⟨⟨a, ⟨_, ha⟩, h, by rw [mul_comm]; exact h⟩, rfl⟩

open Polynomial IsLocalRing in
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω] in
/- English proof (translation)
Take `⟨-, hinv, hfac⟩` from `hM`. Establish `hp0 : algebraMap W Ω π ≠ 0`. Introduce `h`. Rewrite `hinv` using `[h, inv_zero]`. Conclude with `hinv M.zero_mem`.

Establish `hcoe : ((algebraMap W M π : M) : Ω) = algebraMap W Ω π` using `rfl`. Establish `unit_of : ∀ (a : M) (u : Ω), u⁻¹ ∈ M → (a : Ω) = u → u ≠ 0 → IsUnit a` using `fun a u hu' e hu0 => isUnit_of_inv_mem_of_ne_zero a (e ▸ hu') (e ▸ hu0)`. Use `⟨⟨fun hu => ?_, fun a b hab => ?_⟩, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hu.exists_right_inv`. Establish `hy' : (y : Ω) = (algebraMap W Ω π)⁻¹`.

Use `congrArg Subtype.val hy` as an intermediate fact. Simplify using `only [MulMemClass.coe_mul, hcoe, OneMemClass.coe_one] at this`. Conclude with `eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact this)`. Conclude with `hinv (hy' ▸ y.2)`. Establish `hab' : algebraMap W Ω π = (a : Ω) * b`.

Use `congrArg Subtype.val hab` as an intermediate fact. Simplify using `using this`. Establish `ha0 : (a : Ω) ≠ 0` using `fun h => hp0 (by rw [hab', h, zero_mul])`. Establish `hb0 : (b : Ω) ≠ 0` using `fun h => hp0 (by rw [hab', h, mul_zero])`. Take `⟨i, u, hu, hu', ea⟩` from `hfac a a.2 ha0`.

Take `⟨j, v, hv, hv', eb⟩` from `hfac b b.2 hb0`. Establish `hu0 : u ≠ 0` using `fun h => ha0 (by rw [ea, h, mul_zero])`. Establish `hv0 : v ≠ 0` using `fun h => hb0 (by rw [eb, h, mul_zero])`. Break down `i with _ | i` into its components or cases. Conclude with `Or.inl (unit_of a u hu' (by rw [ea, pow_zero, one_mul]) hu0)`.

Break down `j with _ | j` into its components or cases. Conclude with `Or.inr (unit_of b v hv' (by rw [eb, pow_zero, one_mul]) hv0)`. It suffices to derive a contradiction. Apply `hinv` to reduce the goal to its premises. Establish `key : (algebraMap W Ω π)⁻¹ = algebraMap W Ω π ^ (i + j) * u * v`.

Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Apply `mul_left_cancel₀ hp0` to reduce the goal to its premises. Rewrite using `[mul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[key]`.

Conclude with `M.mul_mem (M.mul_mem (M.pow_mem (M.algebraMap_mem π) _) hu) hv`. Establish `hx0 : (x : Ω) ≠ 0` using `fun h => hx (Subtype.ext h)`. Take `⟨n, u, hu, hu', e⟩` from `hfac x x.2 hx0`. Establish `hu0 : u ≠ 0` using `fun h => hx0 (by rw [e, h, mul_zero])`. Take `⟨U, hU⟩` from `unit_of ⟨u, hu⟩ u hu' rfl hu0`.

Use `⟨n, ⟨U, Subtype.ext ?_⟩⟩` and prove the remaining obligations. Simplify using `[hU, e]`.
-/
private lemma irreducible_and_associated_pow_of_unram {π : W}
    (M : Subalgebra W Ω) (hM : _root_.GlobalTheory.ClosedResidueExt.Unram π M) :
    Irreducible (algebraMap W M π) ∧ ∀ x : M, x ≠ 0 → ∃ n : ℕ, Associated (algebraMap W M π ^ n) x := by
  obtain ⟨-, hinv, hfac⟩ := hM
  have hp0 : algebraMap W Ω π ≠ 0 := by
    intro h
    rw [h, inv_zero] at hinv
    exact hinv M.zero_mem
  have hcoe : ((algebraMap W M π : M) : Ω) = algebraMap W Ω π := rfl
  have unit_of : ∀ (a : M) (u : Ω), u⁻¹ ∈ M → (a : Ω) = u → u ≠ 0 → IsUnit a := fun a u hu' e hu0 =>
    isUnit_of_inv_mem_of_ne_zero a (e ▸ hu') (e ▸ hu0)
  refine ⟨⟨fun hu => ?_, fun a b hab => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := hu.exists_right_inv
    have hy' : (y : Ω) = (algebraMap W Ω π)⁻¹ := by
      have := congrArg Subtype.val hy
      simp only [MulMemClass.coe_mul, hcoe, OneMemClass.coe_one] at this
      exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact this)
    exact hinv (hy' ▸ y.2)
  · have hab' : algebraMap W Ω π = (a : Ω) * b := by
      have := congrArg Subtype.val hab
      simpa using this
    have ha0 : (a : Ω) ≠ 0 := fun h => hp0 (by rw [hab', h, zero_mul])
    have hb0 : (b : Ω) ≠ 0 := fun h => hp0 (by rw [hab', h, mul_zero])
    obtain ⟨i, u, hu, hu', ea⟩ := hfac a a.2 ha0
    obtain ⟨j, v, hv, hv', eb⟩ := hfac b b.2 hb0
    have hu0 : u ≠ 0 := fun h => ha0 (by rw [ea, h, mul_zero])
    have hv0 : v ≠ 0 := fun h => hb0 (by rw [eb, h, mul_zero])
    rcases i with _ | i
    · exact Or.inl (unit_of a u hu' (by rw [ea, pow_zero, one_mul]) hu0)
    rcases j with _ | j
    · exact Or.inr (unit_of b v hv' (by rw [eb, pow_zero, one_mul]) hv0)
    exfalso
    apply hinv
    have key : (algebraMap W Ω π)⁻¹ = algebraMap W Ω π ^ (i + j) * u * v := by
      apply inv_eq_of_mul_eq_one_right
      apply mul_left_cancel₀ hp0
      rw [mul_one]
      calc algebraMap W Ω π * (algebraMap W Ω π * (algebraMap W Ω π ^ (i + j) * u * v))
          = algebraMap W Ω π ^ (i + 1) * u * (algebraMap W Ω π ^ (j + 1) * v) := by ring
        _ = algebraMap W Ω π := by rw [← ea, ← eb, hab']
    rw [key]
    exact M.mul_mem (M.mul_mem (M.pow_mem (M.algebraMap_mem π) _) hu) hv
  · have hx0 : (x : Ω) ≠ 0 := fun h => hx (Subtype.ext h)
    obtain ⟨n, u, hu, hu', e⟩ := hfac x x.2 hx0
    have hu0 : u ≠ 0 := fun h => hx0 (by rw [e, h, mul_zero])
    obtain ⟨U, hU⟩ := unit_of ⟨u, hu⟩ u hu' rfl hu0
    refine ⟨n, ⟨U, Subtype.ext ?_⟩⟩
    simp [hU, e]

open Polynomial IsLocalRing in
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω] in
/- English proof (translation)
Assume the negation of the conclusion as `hu`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal (Ideal.span {1 + algebraMap W N π * h}) (by rwa [Ne, Ideal.span_singleton_eq_top])`. Use `haveI : Algebra.IsIntegral W N := ⟨fun x => (isIntegral_algHom_iff N.val Subtype.val_injective).1 (hN x x.2)⟩`. Establish `hmax : (m.comap (algebraMap W N)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m`. Establish `hc : m.comap (algebraMap W N) = IsLocalRing.maximalIdeal W` using `IsLocalRing.eq_maximalIdeal hmax`.

Establish `hπm : algebraMap W N π ∈ m`. Rewrite using `[← Ideal.mem_comap, hc]`. Conclude with `hπ`. Establish `h1 : 1 + algebraMap W N π * h ∈ m` using `hle (Ideal.subset_span rfl)`. Conclude with `hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using m.sub_mem h1 (m.mul_mem_right h hπm)))`.
-/
private lemma isUnit_one_add_algebraMap_mul_of_not_isUnit [IsLocalRing W] {π : W} (hπ : ¬ IsUnit π)
    (N : Subalgebra W Ω) (hN : ∀ x ∈ N, IsIntegral W x) (h : N) : IsUnit (1 + algebraMap W N π * h) := by
  by_contra hu
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {1 + algebraMap W N π * h})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  haveI : Algebra.IsIntegral W N :=
    ⟨fun x => (isIntegral_algHom_iff N.val Subtype.val_injective).1 (hN x x.2)⟩
  have hmax : (m.comap (algebraMap W N)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  have hc : m.comap (algebraMap W N) = IsLocalRing.maximalIdeal W := IsLocalRing.eq_maximalIdeal hmax
  have hπm : algebraMap W N π ∈ m := by
    rw [← Ideal.mem_comap, hc]; exact hπ
  have h1 : 1 + algebraMap W N π * h ∈ m := hle (Ideal.subset_span rfl)
  exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using m.sub_mem h1 (m.mul_mem_right h hπm)))

open Polynomial IsLocalRing in
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω] in
/- English proof (translation)
Use `set N := (Algebra.adjoin M {α}).restrictScalars W with hNdef`. Establish `memN : ∀ g : M[X], aeval α g ∈ N` using `fun g => by show aeval α g ∈ Algebra.adjoin M {α}`. Rewrite using `[Algebra.adjoin_singleton_eq_range_aeval]`. Conclude with `⟨g, rfl⟩`. Introduce `x hx hx0`.

Establish `hx' : x ∈ Algebra.adjoin M {α}` using `hx`. Rewrite `hx'` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨g0, rfl⟩` from `hx'`. Express the relevant statement in the definitionally equal form `aeval α g0 ≠ 0 at hx0`. Use `show ∃ (n : ℕ) (u : Ω), u ∈ N ∧ u⁻¹ ∈ N ∧ aeval α g0 = algebraMap W Ω π ^ n * u`.

Establish `hf1 : f ≠ 1`. Introduce and unpack `rfl`. Conclude with `hirr.not_isUnit (by simp)`. Use `set g := g0 %ₘ f with hgdef`. Establish `hg : aeval α g = aeval α g0` using `by conv_rhs => rw [← modByMonic_add_div g0 f]`.

Simplify using `[hgdef, hα]`. Establish `hgdeg : g.natDegree < f.natDegree` using `natDegree_modByMonic_lt g0 hf hf1`. Establish `hg0 : g ≠ 0`. Introduce `h`. Apply `hx0` to reduce the goal to its premises.

Rewrite using `[← hg, h, map_zero]`. Establish `hπM : algebraMap W M π ∈ RingHom.ker φ` using `hker ▸ Ideal.subset_span rfl`. Establish `hπC : ¬ IsUnit (C (algebraMap W M π))`. Rewrite using `[Polynomial.isUnit_C]`. Introduce `hu`.

Conclude with `(RingHom.ker_ne_top φ) (Ideal.eq_top_of_isUnit_mem _ hπM hu)`. Take `⟨n, g1, hndvd, hgeq⟩` from `WfDvdMonoid.max_power_factor' hg0 hπC`. Establish `hmap1 : g1.map φ ≠ 0`. Introduce `h0`. Apply `hndvd` to reduce the goal to its premises.

Establish `: g1 ∈ RingHom.ker (mapRingHom φ)` using `h0`. Rewrite `this` using `[Polynomial.ker_mapRingHom, hker, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]`. Conclude with `this`. Establish `hg1ne : g1 ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hg0 (by rw [hgeq, mul_zero])`. Establish `hpne : (C (algebraMap W M π)) ^ n ≠ 0`. Introduce `h`. Conclude with `hg0 (by rw [hgeq, h, zero_mul])`. Establish `hdeg1 : g1.natDegree ≤ g.natDegree`.

Rewrite using `[hgeq, natDegree_mul hpne hg1ne]`. Use linear arithmetic over natural numbers and integers. Establish `hndvdp : ¬ f.map φ ∣ g1.map φ`. Introduce `hd`. Establish `h1` using `natDegree_le_of_dvd hd hmap1`.

Rewrite `h1` using `[hf.natDegree_map]`. Establish `h2` using `natDegree_map_le (f := φ) (p := g1)`. Use linear arithmetic over natural numbers and integers. Take `⟨a, b, hab⟩` from `(hirr.coprime_iff_not_dvd).2 hndvdp`. Take `⟨A, rfl⟩` from `Polynomial.map_surjective φ hφ a`.

Take `⟨B, rfl⟩` from `Polynomial.map_surjective φ hφ b`. Establish `hker2 : A * f + B * g1 - 1 ∈ RingHom.ker (mapRingHom φ)`. Rewrite using `[RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_one, hab, sub_self]`. Rewrite `hker2` using `[Polynomial.ker_mapRingHom, hker, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]`. Take `⟨H, hH⟩` from `hker2`.

Establish `hev : aeval α B * aeval α g1 = 1 + algebraMap W Ω π * aeval α H`. Establish `h` using `congrArg (aeval α) hH`. Simplify using `only [map_sub, map_add, map_mul, map_one, hα, mul_zero, zero_add, aeval_C] at h`. Rewrite using `[IsScalarTower.algebraMap_apply W M Ω]`. Take the linear combination `h`.

Choose the witnesses or unpack the hypotheses as in `⟨v, hvN, hv⟩ : ∃ v ∈ N, v * (1 + algebraMap W Ω π * aeval α H) = 1 := by`. Take `⟨w, hw⟩` from `(isUnit_one_add_algebraMap_mul_of_not_isUnit hπ N hN ⟨aeval α H, memN H⟩).exists_left_inv`. Use `⟨w, w.2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hw` as an intermediate fact. Simplify using `using this`.

Use `⟨n, aeval α g1, memN g1, ?_, ?_⟩` and prove the remaining obligations. Establish `hinv : (aeval α g1)⁻¹ = v * aeval α B`. Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Take the linear combination `v * hev + hv`. Rewrite using `[hinv]`.

Conclude with `N.mul_mem hvN (memN B)`. Rewrite using `[← hg, hgeq, map_mul, map_pow, aeval_C, IsScalarTower.algebraMap_apply W M Ω]`.
-/
private lemma eq_pow_mul_unit_of_mem_adjoin [IsLocalRing W] {π : W}
    (hπ : ¬ IsUnit π) (M : Subalgebra W Ω) [WfDvdMonoid M] {k : Type} [Field k] (φ : M →+* k)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = Ideal.span {algebraMap W M π}) (f : M[X])
    (hf : f.Monic) (hirr : Irreducible (f.map φ)) (α : Ω) (hα : aeval α f = 0)
    (hN : ∀ x ∈ (Algebra.adjoin M {α}).restrictScalars W, IsIntegral W x) :
    ∀ x ∈ (Algebra.adjoin M {α}).restrictScalars W, x ≠ 0 → ∃ (n : ℕ) (u : Ω),
      u ∈ (Algebra.adjoin M {α}).restrictScalars W ∧ u⁻¹ ∈ (Algebra.adjoin M {α}).restrictScalars W ∧
      x = algebraMap W Ω π ^ n * u := by
  set N := (Algebra.adjoin M {α}).restrictScalars W with hNdef
  have memN : ∀ g : M[X], aeval α g ∈ N := fun g => by
    show aeval α g ∈ Algebra.adjoin M {α}
    rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨g, rfl⟩
  intro x hx hx0
  have hx' : x ∈ Algebra.adjoin M {α} := hx
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨g0, rfl⟩ := hx'
  change aeval α g0 ≠ 0 at hx0
  show ∃ (n : ℕ) (u : Ω), u ∈ N ∧ u⁻¹ ∈ N ∧ aeval α g0 = algebraMap W Ω π ^ n * u
  have hf1 : f ≠ 1 := by
    rintro rfl
    exact hirr.not_isUnit (by simp)
  set g := g0 %ₘ f with hgdef
  have hg : aeval α g = aeval α g0 := by
    conv_rhs => rw [← modByMonic_add_div g0 f]
    simp [hgdef, hα]
  have hgdeg : g.natDegree < f.natDegree := natDegree_modByMonic_lt g0 hf hf1
  have hg0 : g ≠ 0 := by
    intro h
    apply hx0
    rw [← hg, h, map_zero]
  have hπM : algebraMap W M π ∈ RingHom.ker φ := hker ▸ Ideal.subset_span rfl
  have hπC : ¬ IsUnit (C (algebraMap W M π)) := by
    rw [Polynomial.isUnit_C]
    intro hu
    exact (RingHom.ker_ne_top φ) (Ideal.eq_top_of_isUnit_mem _ hπM hu)
  obtain ⟨n, g1, hndvd, hgeq⟩ := WfDvdMonoid.max_power_factor' hg0 hπC
  have hmap1 : g1.map φ ≠ 0 := by
    intro h0
    apply hndvd
    have : g1 ∈ RingHom.ker (mapRingHom φ) := h0
    rw [Polynomial.ker_mapRingHom, hker, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton] at this
    exact this
  have hg1ne : g1 ≠ 0 := by
    rintro rfl
    exact hg0 (by rw [hgeq, mul_zero])
  have hpne : (C (algebraMap W M π)) ^ n ≠ 0 := by
    intro h
    exact hg0 (by rw [hgeq, h, zero_mul])
  have hdeg1 : g1.natDegree ≤ g.natDegree := by
    rw [hgeq, natDegree_mul hpne hg1ne]; omega
  have hndvdp : ¬ f.map φ ∣ g1.map φ := by
    intro hd
    have h1 := natDegree_le_of_dvd hd hmap1
    rw [hf.natDegree_map] at h1
    have h2 := natDegree_map_le (f := φ) (p := g1)
    omega
  obtain ⟨a, b, hab⟩ := (hirr.coprime_iff_not_dvd).2 hndvdp
  obtain ⟨A, rfl⟩ := Polynomial.map_surjective φ hφ a
  obtain ⟨B, rfl⟩ := Polynomial.map_surjective φ hφ b
  have hker2 : A * f + B * g1 - 1 ∈ RingHom.ker (mapRingHom φ) := by
    rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_one, hab, sub_self]
  rw [Polynomial.ker_mapRingHom, hker, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hker2
  obtain ⟨H, hH⟩ := hker2
  have hev : aeval α B * aeval α g1 = 1 + algebraMap W Ω π * aeval α H := by
    have h := congrArg (aeval α) hH
    simp only [map_sub, map_add, map_mul, map_one, hα, mul_zero, zero_add, aeval_C] at h
    rw [IsScalarTower.algebraMap_apply W M Ω]
    linear_combination h
  obtain ⟨v, hvN, hv⟩ : ∃ v ∈ N, v * (1 + algebraMap W Ω π * aeval α H) = 1 := by
    obtain ⟨w, hw⟩ := (isUnit_one_add_algebraMap_mul_of_not_isUnit hπ N hN ⟨aeval α H, memN H⟩).exists_left_inv
    refine ⟨w, w.2, ?_⟩
    have := congrArg Subtype.val hw
    simpa using this
  refine ⟨n, aeval α g1, memN g1, ?_, ?_⟩
  · have hinv : (aeval α g1)⁻¹ = v * aeval α B := by
      apply inv_eq_of_mul_eq_one_right
      linear_combination v * hev + hv
    rw [hinv]
    exact N.mul_mem hvN (memN B)
  · rw [← hg, hgeq, map_mul, map_pow, aeval_C, IsScalarTower.algebraMap_apply W M Ω]

open Polynomial IsLocalRing in
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω] in

/- English proof (translation)
Set `Ω` to `AlgebraicClosure (FractionRing W)`. Establish `hinj : Function.Injective (algebraMap W Ω)`. Rewrite using `[IsScalarTower.algebraMap_eq W (FractionRing W) Ω]`. Conclude with `(algebraMap (FractionRing W) Ω).injective.comp (IsFractionRing.injective W (FractionRing W))`. Establish `hπu : ¬ IsUnit π` using `hπ.not_isUnit`.

Establish `h0 : _root_.GlobalTheory.ClosedResidueExt.Unram π (⊥ : Subalgebra W Ω)`. Use `⟨fun x hx => ?_, fun hx => ?_, fun x hx hx0 => ?_⟩` and prove the remaining obligations. Take `⟨w, rfl⟩` from `Algebra.mem_bot.1 hx`. Conclude with `isIntegral_algebraMap`. Take `⟨w, hw⟩` from `Algebra.mem_bot.1 hx`.

Apply `hπu` to reduce the goal to its premises. Establish `hp0 : algebraMap W Ω π ≠ 0` using `fun h => hπ.ne_zero (hinj (by rw [h, map_zero]))`. Establish `h1 : π * w = 1` using `hinj (by rw [map_mul, hw, map_one, mul_inv_cancel₀ hp0])`. Conclude with `⟨⟨π, w, h1, by rw [mul_comm]; exact h1⟩, rfl⟩`. Take `⟨w, rfl⟩` from `Algebra.mem_bot.1 hx`.

Establish `hw0 : w ≠ 0` using `fun h => hx0 (by rw [h, map_zero])`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hπ`. Establish `hinv : (algebraMap W Ω (u : W))⁻¹ = algebraMap W Ω ((u⁻¹ : Wˣ) : W)`. Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[← map_mul, Units.mul_inv, map_one]`.

Use `⟨n, algebraMap W Ω u, Subalgebra.algebraMap_mem _ _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hinv]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Rewrite using `[hu, map_mul, map_pow, mul_comm]`. Take `⟨M, hM, hmax⟩` from `exists_maximal_unram_subalgebra π h0`.

Take `⟨hirrM, hfacM⟩` from `irreducible_and_associated_pow_of_unram M hM`. Use `haveI : IsDiscreteValuationRing M := IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirrM, fun {x} hx => hfacM x hx⟩`. Use `haveI hint : Algebra.IsIntegral W M := ⟨fun x => (isIntegral_algHom_iff M.val Subtype.val_injective).1 (hM.1 x x.2)⟩`. Use `⟨M, inferInstance, inferInstance, inferInstance, inferInstance, ?_, hint, hirrM, ?_⟩` and prove the remaining obligations. Introduce `a b hab`.

Conclude with `hinj (congrArg Subtype.val hab)`. Use `IsAlgClosed.of_exists_root _ fun p hpm hpirr => ?_` and prove the remaining obligations. Take `⟨q, hq⟩` from `Polynomial.map_surjective (IsLocalRing.residue M) IsLocalRing.residue_surjective p`. Take `⟨f, hfp, hfnat, hfm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic ((Polynomial.mem_lifts p).2 ⟨q, hq⟩) hpm`. Establish `hfdeg : f.degree ≠ 0`.

Rewrite using `[Polynomial.degree_eq_natDegree hfm.ne_zero, hfnat]`. Conclude with `(Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hpirr)).ne'` after adjusting the coercions. Take `⟨α, hα⟩` from `IsAlgClosed.exists_aeval_eq_zero Ω f hfdeg`. Establish `hαi : IsIntegral M α` using `⟨f, hfm, hα⟩`. Establish `hNint : ∀ x ∈ (Algebra.adjoin M {α}).restrictScalars W, IsIntegral W x` using `fun x hx => isIntegral_trans x (by`.

Use `adjoin_le_integralClosure hαi hx` as an intermediate fact. Conclude with `this)`. Establish `hker : RingHom.ker (IsLocalRing.residue M) = Ideal.span {algebraMap W M π}`. Rewrite using `[IsLocalRing.ker_residue]`. Conclude with `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirrM`.

Establish `hirr' : Irreducible (f.map (IsLocalRing.residue M))` using `hfp ▸ hpirr`. Establish `hp0 : algebraMap W Ω π ≠ 0`. Introduce `h`. Apply `hM.2.1` to reduce the goal to its premises. Rewrite using `[h, inv_zero]`.

Conclude with `M.zero_mem`. Establish `hNU : _root_.GlobalTheory.ClosedResidueExt.Unram π ((Algebra.adjoin M {α}).restrictScalars W)`. Use `⟨hNint, fun hx => ?_, eq_pow_mul_unit_of_mem_adjoin hπu M (IsLocalRing.residue M) IsLocalRing.residue_surjective hker f hfm hirr' α hα hNint⟩` and prove the remaining obligations. Establish `hu` using `isUnit_one_add_algebraMap_mul_of_not_isUnit hπu _ hNint ⟨-(algebraMap W Ω π)⁻¹, Subalgebra.neg_mem _ hx⟩`. Establish `hz : (1 + algebraMap W ((Algebra.adjoin M {α}).restrictScalars W) π * ⟨-(algebraMap W Ω π)⁻¹, Subalgebra.neg_mem _ hx⟩ : (Algebra.adjoin M {α}).restrictScalars W) = 0` using `Subtype.ext (by show (1 : Ω) + algebraMap W Ω π * -(algebraMap W Ω π)⁻¹ = 0`.

Rewrite using `[mul_neg, mul_inv_cancel₀ hp0, add_neg_cancel])`. Rewrite `hu` using `[hz]`. Conclude with `not_isUnit_zero hu`. Establish `hle : M ≤ (Algebra.adjoin M {α}).restrictScalars W` using `fun x hx => Subalgebra.algebraMap_mem (Algebra.adjoin M {α}) (⟨x, hx⟩ : M)`. Establish `hNM` using `hmax _ hNU hle`.

Establish `hαM : α ∈ M` using `hNM ▸ (Algebra.self_mem_adjoin_singleton M α : α ∈ Algebra.adjoin M {α})`. Use `⟨IsLocalRing.residue M ⟨α, hαM⟩, ?_⟩` and prove the remaining obligations. Establish `hev : Polynomial.eval (⟨α, hαM⟩ : M) f = 0`. Establish `h` using `hα`. Rewrite `h` using `[show α = algebraMap M Ω ⟨α, hαM⟩ from rfl, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]`.

Conclude with `Subtype.ext h`. Rewrite using `[← hfp, Polynomial.eval_map, Polynomial.eval₂_hom, hev, map_zero]`.
-/
theorem _root_.GlobalTheory.ClosedResidueExt.exists_unramified_ext (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : Algebra W R), Function.Injective (algebraMap W R) ∧ Algebra.IsIntegral W R ∧
        Irreducible (algebraMap W R π) ∧ IsAlgClosed (ResidueField R) := by
  let Ω := AlgebraicClosure (FractionRing W)
  have hinj : Function.Injective (algebraMap W Ω) := by
    rw [IsScalarTower.algebraMap_eq W (FractionRing W) Ω]
    exact (algebraMap (FractionRing W) Ω).injective.comp (IsFractionRing.injective W (FractionRing W))
  have hπu : ¬ IsUnit π := hπ.not_isUnit
  have h0 : _root_.GlobalTheory.ClosedResidueExt.Unram π (⊥ : Subalgebra W Ω) := by
    refine ⟨fun x hx => ?_, fun hx => ?_, fun x hx hx0 => ?_⟩
    · obtain ⟨w, rfl⟩ := Algebra.mem_bot.1 hx
      exact isIntegral_algebraMap
    · obtain ⟨w, hw⟩ := Algebra.mem_bot.1 hx
      apply hπu
      have hp0 : algebraMap W Ω π ≠ 0 := fun h => hπ.ne_zero (hinj (by rw [h, map_zero]))
      have h1 : π * w = 1 := hinj (by rw [map_mul, hw, map_one, mul_inv_cancel₀ hp0])
      exact ⟨⟨π, w, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
    · obtain ⟨w, rfl⟩ := Algebra.mem_bot.1 hx
      have hw0 : w ≠ 0 := fun h => hx0 (by rw [h, map_zero])
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hπ
      have hinv : (algebraMap W Ω (u : W))⁻¹ = algebraMap W Ω ((u⁻¹ : Wˣ) : W) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← map_mul, Units.mul_inv, map_one]
      refine ⟨n, algebraMap W Ω u, Subalgebra.algebraMap_mem _ _, ?_, ?_⟩
      · rw [hinv]; exact Subalgebra.algebraMap_mem _ _
      · rw [hu, map_mul, map_pow, mul_comm]
  obtain ⟨M, hM, hmax⟩ := exists_maximal_unram_subalgebra π h0
  obtain ⟨hirrM, hfacM⟩ := irreducible_and_associated_pow_of_unram M hM
  haveI : IsDiscreteValuationRing M :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirrM, fun {x} hx => hfacM x hx⟩
  haveI hint : Algebra.IsIntegral W M :=
    ⟨fun x => (isIntegral_algHom_iff M.val Subtype.val_injective).1 (hM.1 x x.2)⟩
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, ?_, hint, hirrM, ?_⟩
  · intro a b hab
    exact hinj (congrArg Subtype.val hab)
  refine IsAlgClosed.of_exists_root _ fun p hpm hpirr => ?_
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (IsLocalRing.residue M) IsLocalRing.residue_surjective p
  obtain ⟨f, hfp, hfnat, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts p).2 ⟨q, hq⟩) hpm
  have hfdeg : f.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hfm.ne_zero, hfnat]
    exact_mod_cast (Polynomial.natDegree_pos_iff_degree_pos.2
      (Polynomial.degree_pos_of_irreducible hpirr)).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero Ω f hfdeg
  have hαi : IsIntegral M α := ⟨f, hfm, hα⟩
  have hNint : ∀ x ∈ (Algebra.adjoin M {α}).restrictScalars W, IsIntegral W x := fun x hx =>
    isIntegral_trans x (by
      have := adjoin_le_integralClosure hαi hx
      exact this)
  have hker : RingHom.ker (IsLocalRing.residue M) = Ideal.span {algebraMap W M π} := by
    rw [IsLocalRing.ker_residue]
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirrM
  have hirr' : Irreducible (f.map (IsLocalRing.residue M)) := hfp ▸ hpirr
  have hp0 : algebraMap W Ω π ≠ 0 := by
    intro h
    apply hM.2.1
    rw [h, inv_zero]
    exact M.zero_mem
  have hNU : _root_.GlobalTheory.ClosedResidueExt.Unram π ((Algebra.adjoin M {α}).restrictScalars W) := by
    refine ⟨hNint, fun hx => ?_, eq_pow_mul_unit_of_mem_adjoin hπu M (IsLocalRing.residue M)
      IsLocalRing.residue_surjective hker f hfm hirr' α hα hNint⟩
    have hu := isUnit_one_add_algebraMap_mul_of_not_isUnit hπu _ hNint ⟨-(algebraMap W Ω π)⁻¹, Subalgebra.neg_mem _ hx⟩
    have hz : (1 + algebraMap W ((Algebra.adjoin M {α}).restrictScalars W) π *
        ⟨-(algebraMap W Ω π)⁻¹, Subalgebra.neg_mem _ hx⟩ : (Algebra.adjoin M {α}).restrictScalars W) = 0 :=
      Subtype.ext (by
        show (1 : Ω) + algebraMap W Ω π * -(algebraMap W Ω π)⁻¹ = 0
        rw [mul_neg, mul_inv_cancel₀ hp0, add_neg_cancel])
    rw [hz] at hu
    exact not_isUnit_zero hu
  have hle : M ≤ (Algebra.adjoin M {α}).restrictScalars W := fun x hx =>
    Subalgebra.algebraMap_mem (Algebra.adjoin M {α}) (⟨x, hx⟩ : M)
  have hNM := hmax _ hNU hle
  have hαM : α ∈ M := hNM ▸ (Algebra.self_mem_adjoin_singleton M α : α ∈ Algebra.adjoin M {α})
  refine ⟨IsLocalRing.residue M ⟨α, hαM⟩, ?_⟩
  have hev : Polynomial.eval (⟨α, hαM⟩ : M) f = 0 := by
    have h := hα
    rw [show α = algebraMap M Ω ⟨α, hαM⟩ from rfl, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at h
    exact Subtype.ext h
  rw [← hfp, Polynomial.eval_map, Polynomial.eval₂_hom, hev, map_zero]

open Polynomial IsLocalRing in
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω] in

/- English proof (translation)
Introduce `W _ _ _ _ _`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible W`. Take `⟨R, i1, i2, i3, i4, h1, h2, _, h4⟩` from `_root_.GlobalTheory.ClosedResidueExt.exists_unramified_ext W hπ`. Conclude with `⟨R, i1, i2, i3, i4, h1, h2, h4⟩`.
-/
theorem _root_.GlobalTheory.ClosedResidueExt.exists_integral_ext_isAlgClosed_residueField : ∀ (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W],
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : Algebra W R), Function.Injective (algebraMap W R) ∧ Algebra.IsIntegral W R ∧
        IsAlgClosed (IsLocalRing.ResidueField R) := by
  intro W _ _ _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨R, i1, i2, i3, i4, h1, h2, _, h4⟩ := _root_.GlobalTheory.ClosedResidueExt.exists_unramified_ext W hπ
  exact ⟨R, i1, i2, i3, i4, h1, h2, h4⟩

end GlobalTheory.ClosedResidueExt
