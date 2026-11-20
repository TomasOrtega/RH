import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.UnifVSpec

noncomputable section

namespace PI.VolStabW

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Res

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

abbrev iO (a : 𝓞 F) : Fv F v := algebraMap F (Fv F v) (algebraMap (𝓞 F) F a)

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation']`.
-/
theorem vcoe (x : F) : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, v.valuedAdicCompletion_eq_valuation']

/- English proof (translation)
Break down `eq_or_ne g 0 with rfl | hg` into its components or cases. Simplify using the standard rewrite rules. Take `⟨n, rfl⟩ : ∃ n : ℤ, g = WithZero.exp n` from `⟨WithZero.log g, (WithZero.exp_log hg).symm⟩`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lt_one_iff_le_expm1 (g : WithZero (Multiplicative ℤ)) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · obtain ⟨n, rfl⟩ : ∃ n : ℤ, g = WithZero.exp n := ⟨WithZero.log g, (WithZero.exp_log hg).symm⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

/- English proof (translation)
Rewrite using `[vcoe]`. Conclude with `v.valuation_le_one a`.
-/
theorem v_iO_le (a : 𝓞 F) : Valued.v (iO v a) ≤ 1 := by
  rw [vcoe]; exact v.valuation_le_one a

/- English proof (translation)
Rewrite using `[vcoe]`. Conclude with `v.valuation_lt_one_iff_mem a`.
-/
theorem v_iO_lt_iff (a : 𝓞 F) : Valued.v (iO v a) < 1 ↔ a ∈ v.asIdeal := by
  rw [vcoe]; exact v.valuation_lt_one_iff_mem a

/- English proof (translation)
Establish `hU : IsOpen {y : Fv F v | Valued.v (x - y) < 1}`. Establish `e : {y : Fv F v | Valued.v (x - y) < 1} = {y : Fv F v | ‖x - y‖ < 1}`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq]`. Conclude with `Valued.toNormedField.norm_lt_one_iff.symm`.

Rewrite using `[e]`. Conclude with `isOpen_lt (continuous_const.sub continuous_id).norm continuous_const`. Take `⟨y, hy⟩` from `(v.denseRange_algebraMap (K := F)).exists_mem_open hU ⟨x, by simp⟩`. Simplify using `only [Set.mem_setOf_eq] at hy`. Establish `hx1 : Valued.v x ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).1 hx`.

Establish `hy1 : v.valuation F y ≤ 1`. Rewrite using `[← vcoe]`. Establish `: algebraMap F (Fv F v) y = x - (x - algebraMap F (Fv F v) y)` using `by ring`. Rewrite using `[this]`. Conclude with `(Valuation.map_sub _ _ _).trans (max_le hx1 hy.le)`.

Take `⟨a, ha⟩` from `v.exists_valuation_sub_lt_of_integer hy1 (1 : (WithZero (Multiplicative ℤ))ˣ)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `ha' : Valued.v (iO v a - algebraMap F (Fv F v) y) < 1`. Rewrite using `[iO, ← map_sub, vcoe]`. Simplify using `using ha`.

Establish `: x - iO v a = (x - algebraMap F (Fv F v) y) - (iO v a - algebraMap F (Fv F v) y)` using `by ring`. Rewrite using `[this]`. Conclude with `Valuation.map_sub_lt _ hy ha'`.
-/
theorem exists_appr {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ a : 𝓞 F, Valued.v (x - iO v a) < 1 := by
  have hU : IsOpen {y : Fv F v | Valued.v (x - y) < 1} := by
    have e : {y : Fv F v | Valued.v (x - y) < 1} = {y : Fv F v | ‖x - y‖ < 1} := by
      ext y; simp only [Set.mem_setOf_eq]; exact Valued.toNormedField.norm_lt_one_iff.symm
    rw [e]
    exact isOpen_lt (continuous_const.sub continuous_id).norm continuous_const
  obtain ⟨y, hy⟩ := (v.denseRange_algebraMap (K := F)).exists_mem_open hU
    ⟨x, by simp⟩
  simp only [Set.mem_setOf_eq] at hy
  have hx1 : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).1 hx
  have hy1 : v.valuation F y ≤ 1 := by
    rw [← vcoe]
    have : algebraMap F (Fv F v) y = x - (x - algebraMap F (Fv F v) y) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le hx1 hy.le)
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hy1 (1 : (WithZero (Multiplicative ℤ))ˣ)
  refine ⟨a, ?_⟩
  have ha' : Valued.v (iO v a - algebraMap F (Fv F v) y) < 1 := by
    rw [iO, ← map_sub, vcoe]; simpa using ha
  have : x - iO v a = (x - algebraMap F (Fv F v) y) - (iO v a - algebraMap F (Fv F v) y) := by ring
  rw [this]
  exact Valuation.map_sub_lt _ hy ha'

open Classical in

def appr (x : Fv F v) : 𝓞 F :=
  if h : ∃ a : 𝓞 F, Valued.v (x - iO v a) < 1 then h.choose else 0

/- English proof (translation)
Establish `h` using `exists_appr v hx`. Rewrite using `[appr, dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem appr_spec {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    Valued.v (x - iO v (appr v x)) < 1 := by
  have h := exists_appr v hx
  rw [appr, dif_pos h]
  exact h.choose_spec

def red (x : Fv F v) : 𝓞 F ⧸ v.asIdeal := Ideal.Quotient.mk _ (appr v x)

/- English proof (translation)
Rewrite using `[red, Ideal.Quotient.eq, ← v_iO_lt_iff, iO, iO, map_sub, map_sub]`. Establish `h0` using `appr_spec v hx`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: x - iO v a = (x - iO v (appr v x)) + (iO v (appr v x) - iO v a)` using `by ring`.

Rewrite using `[this]`. Conclude with `Valuation.map_add_lt _ h0 h`. Introduce `h`. Establish `: iO v (appr v x) - iO v a = (x - iO v a) - (x - iO v (appr v x))` using `by ring`. Use `show Valued.v (iO v (appr v x) - iO v a) < 1`.

Rewrite using `[this]`. Conclude with `Valuation.map_sub_lt _ h h0`.
-/
theorem red_eq_mk_iff {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (a : 𝓞 F) :
    red v x = Ideal.Quotient.mk _ a ↔ Valued.v (x - iO v a) < 1 := by
  rw [red, Ideal.Quotient.eq, ← v_iO_lt_iff, iO, iO, map_sub, map_sub]
  have h0 := appr_spec v hx
  constructor
  · intro h
    have : x - iO v a = (x - iO v (appr v x)) + (iO v (appr v x) - iO v a) := by ring
    rw [this]; exact Valuation.map_add_lt _ h0 h
  · intro h
    have : iO v (appr v x) - iO v a = (x - iO v a) - (x - iO v (appr v x)) := by ring
    show Valued.v (iO v (appr v x) - iO v a) < 1
    rw [this]; exact Valuation.map_sub_lt _ h h0

/- English proof (translation)
The claim follows from `(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).2 (v_iO_le v a)`.
-/
theorem mem_O_iO (a : 𝓞 F) : iO v a ∈ v.adicCompletionIntegers F :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).2 (v_iO_le v a)

/- English proof (translation)
Rewrite using `[red_eq_mk_iff v (mem_O_iO v a) a]`. Simplify using the standard rewrite rules.
-/
theorem red_iO (a : 𝓞 F) : red v (iO v a) = Ideal.Quotient.mk _ a := by
  rw [red_eq_mk_iff v (mem_O_iO v a) a]
  simp

/- English proof (translation)
Establish `e : red v x + red v y = Ideal.Quotient.mk _ (appr v x + appr v y)`. Rewrite using `[map_add]`. Both sides reduce to the same expression. Rewrite using `[e, red_eq_mk_iff v (add_mem hx hy)]`. Establish `: x + y - iO v (appr v x + appr v y) = (x - iO v (appr v x)) + (y - iO v (appr v y))`.

Simplify using `only [iO, map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Valuation.map_add_lt _ (appr_spec v hx) (appr_spec v hy)`.
-/
theorem red_add {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F)
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x + y) = red v x + red v y := by
  have e : red v x + red v y = Ideal.Quotient.mk _ (appr v x + appr v y) := by
    rw [map_add]; rfl
  rw [e, red_eq_mk_iff v (add_mem hx hy)]
  have : x + y - iO v (appr v x + appr v y) = (x - iO v (appr v x)) + (y - iO v (appr v y)) := by
    simp only [iO, map_add]; ring
  rw [this]
  exact Valuation.map_add_lt _ (appr_spec v hx) (appr_spec v hy)

/- English proof (translation)
Establish `e : red v x * red v y = Ideal.Quotient.mk _ (appr v x * appr v y)`. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Rewrite using `[e, red_eq_mk_iff v (mul_mem hx hy)]`. Establish `: x * y - iO v (appr v x * appr v y) = x * (y - iO v (appr v y)) + iO v (appr v y) * (x - iO v (appr v x))`.

Simplify using `only [iO, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Establish `hx1 : Valued.v x ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).1 hx`. Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem red_mul {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F)
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x * y) = red v x * red v y := by
  have e : red v x * red v y = Ideal.Quotient.mk _ (appr v x * appr v y) := by
    rw [map_mul]; rfl
  rw [e, red_eq_mk_iff v (mul_mem hx hy)]
  have : x * y - iO v (appr v x * appr v y) =
      x * (y - iO v (appr v y)) + iO v (appr v y) * (x - iO v (appr v x)) := by
    simp only [iO, map_mul]; ring
  rw [this]
  have hx1 : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).1 hx
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul]
    calc Valued.v x * Valued.v (y - iO v (appr v y)) ≤ 1 * Valued.v (y - iO v (appr v y)) :=
          mul_le_mul_left hx1 _
      _ < 1 := by rw [one_mul]; exact appr_spec v hy
  · rw [map_mul]
    calc Valued.v (iO v (appr v y)) * Valued.v (x - iO v (appr v x)) ≤
          1 * Valued.v (x - iO v (appr v x)) := mul_le_mul_left (v_iO_le v _) _
      _ < 1 := by rw [one_mul]; exact appr_spec v hx

/- English proof (translation)
Use `red_iO v 1` as an intermediate fact. Simplify `this` using `[iO]`.
-/
theorem red_one : red v 1 = 1 := by
  have := red_iO v 1
  simpa [iO] using this

/- English proof (translation)
Use `red_eq_mk_iff v hx 0` as an intermediate fact. Simplify `this` using `[iO]`.
-/
theorem red_eq_zero_iff {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    red v x = 0 ↔ Valued.v x < 1 := by
  have := red_eq_mk_iff v hx 0
  simpa [iO] using this

/- English proof (translation)
The claim follows from `(red_eq_zero_iff v (zero_mem _)).2 (by simp)`.
-/
theorem red_zero : red v 0 = 0 := (red_eq_zero_iff v (zero_mem _)).2 (by simp)

/- English proof (translation)
Establish `h` using `red_add v hx (neg_mem hx)`. Rewrite `h` using `[add_neg_cancel, red_zero]`. Conclude with `(neg_eq_of_add_eq_zero_right h.symm).symm`.
-/
theorem red_neg {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) : red v (-x) = -red v x := by
  have h := red_add v hx (neg_mem hx)
  rw [add_neg_cancel, red_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/- English proof (translation)
Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective t`. Conclude with `⟨iO v a, mem_O_iO v a, red_iO v a⟩`.
-/
theorem red_surj (t : 𝓞 F ⧸ v.asIdeal) : ∃ x ∈ v.adicCompletionIntegers F, red v x = t := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  exact ⟨iO v a, mem_O_iO v a, red_iO v a⟩

/- English proof (translation)
Establish `hπ` using `unifV_val v`. Rewrite using `[map_mul, map_inv₀, hπ, lt_one_iff_le_expm1]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Combine the equalities or inequalities in the displayed calculation.

Introduce `h`. Establish `h2` using `mul_le_mul' h (le_refl (WithZero.exp (-1 : ℤ)))`. Rewrite `h2` using `[mul_comm, ← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul, one_mul]`. Then use the resulting hypothesis.
-/
theorem lt_one_iff_unif (x : Fv F v) :
    Valued.v x < 1 ↔ Valued.v ((unifV v)⁻¹ * x) ≤ 1 := by
  have hπ := unifV_val v
  rw [map_mul, map_inv₀, hπ, lt_one_iff_le_expm1]
  constructor
  · intro h
    calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v x ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1) :=
          mul_le_mul' le_rfl h
      _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
  · intro h
    have h2 := mul_le_mul' h (le_refl (WithZero.exp (-1 : ℤ)))
    rwa [mul_comm, ← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul, one_mul] at h2

/- English proof (translation)
Use `HeightOneSpectrum.Support.finite (𝓞 F) x` as an intermediate fact. Rewrite using `[Filter.eventually_cofinite]`. Use `this.subset fun w hw => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, HeightOneSpectrum.mem_adicCompletionIntegers, not_le, vcoe] at hw`. Conclude with `hw`.
-/
theorem ev_int (x : F) : ∀ᶠ v in cofinite,
    algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  have := HeightOneSpectrum.Support.finite (𝓞 F) x
  rw [Filter.eventually_cofinite]
  refine this.subset fun w hw => ?_
  simp only [Set.mem_setOf_eq, HeightOneSpectrum.mem_adicCompletionIntegers, not_le, vcoe] at hw
  exact hw

/- English proof (translation)
Use `filter_upwards [ev_int x, ev_int x⁻¹] with w h1 h2`. Rewrite `h1`, `h2` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Rewrite `h2` using `[map_inv₀, map_inv₀]`. Establish `h0 : Valued.v (algebraMap F (Fv F w) x) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`.

Simplify using `using hx`. Assume the negation of the conclusion as `hne`. Establish `hlt : Valued.v (algebraMap F (Fv F w) x) < 1` using `lt_of_le_of_ne h1 hne`. Conclude with `absurd h2 (not_le.2 ((one_lt_inv₀ (zero_lt_iff.2 h0)).2 hlt))`.
-/
theorem ev_unit {x : F} (hx : x ≠ 0) : ∀ᶠ v in cofinite,
    Valued.v (algebraMap F (Fv F v) x) = 1 := by
  filter_upwards [ev_int x, ev_int x⁻¹] with w h1 h2
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  rw [map_inv₀, map_inv₀] at h2
  have h0 : Valued.v (algebraMap F (Fv F w) x) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; simpa using hx
  by_contra hne
  have hlt : Valued.v (algebraMap F (Fv F w) x) < 1 := lt_of_le_of_ne h1 hne
  exact absurd h2 (not_le.2 ((one_lt_inv₀ (zero_lt_iff.2 h0)).2 hlt))

end Res

section Count

/- English proof (translation)
Use `choose l hlL hl using hsurj`. Establish `key : ∀ s x, -l s + x ∈ N ↔ x ∈ L ∧ φ x = s`. Introduce `s x`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `hx : x = l s + (-l s + x)` using `by abel`. Establish `hL : x ∈ L` using `by rw [hx]; exact L.add_mem (hlL s) (hNL h)`. Use `⟨hL, ?_⟩` and prove the remaining obligations. Rewrite using `[hx, hadd _ (hlL s) _ (hNL h), hl, (hker _ (hNL h)).2 h, add_zero]`. Introduce and unpack `⟨hL, rfl⟩`.

Establish `hm : -l (φ x) + x ∈ L` using `L.add_mem (L.neg_mem (hlL _)) hL`. Use `(hker _ hm).1 ?_` and prove the remaining obligations. Establish `e` using `hadd _ (hlL (φ x)) _ hm`. Rewrite `e` using `[show l (φ x) + (-l (φ x) + x) = x by abel, hl]`. Establish `e2` using `e.symm`.

Rewrite `e2` using `[add_eq_left]`. Then use the resulting hypothesis. Establish `hfin : S.Finite` using `S.toFinite`. Establish `hset : {x | x ∈ L ∧ φ x ∈ S} = ⋃ s ∈ hfin.toFinset, (fun x => -l s + x) ⁻¹' (N : Set G)`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, Set.Finite.mem_toFinset, exists_prop, key]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨_, h2, h1, rfl⟩`. Introduce and unpack `⟨s, hs, h1, rfl⟩`. Conclude with `⟨h1, hs⟩`.

Rewrite using `[hset, measure_biUnion_finset]`. Simplify using `only [measure_preimage_add]`. Rewrite using `[Finset.sum_const, nsmul_eq_mul, Nat.card_eq_card_finite_toFinset hfin]`. Introduce `s _ t _ hst`. Use `Set.disjoint_left.2 fun x h1 h2 => hst ?_` and prove the remaining obligations.

Simplify using `only [Set.mem_preimage, SetLike.mem_coe, key] at h1 h2`. Rewrite using `[← h1.2, ← h2.2]`. Introduce `s _`. Conclude with `hN.preimage (measurable_const_add _)`.
-/
theorem measure_count {G V : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    [AddCommGroup V] [Finite V] (μ : Measure G) [μ.IsAddLeftInvariant] (L N : AddSubgroup G)
    (hNL : N ≤ L) (hN : MeasurableSet (N : Set G)) (φ : G → V)
    (hadd : ∀ x ∈ L, ∀ y ∈ L, φ (x + y) = φ x + φ y) (hker : ∀ x ∈ L, φ x = 0 ↔ x ∈ N)
    (hsurj : ∀ w, ∃ x ∈ L, φ x = w) (S : Set V) :
    μ {x | x ∈ L ∧ φ x ∈ S} = (Nat.card S : ENNReal) * μ N := by
  choose l hlL hl using hsurj
  have key : ∀ s x, -l s + x ∈ N ↔ x ∈ L ∧ φ x = s := by
    intro s x
    constructor
    · intro h
      have hx : x = l s + (-l s + x) := by abel
      have hL : x ∈ L := by rw [hx]; exact L.add_mem (hlL s) (hNL h)
      refine ⟨hL, ?_⟩
      rw [hx, hadd _ (hlL s) _ (hNL h), hl, (hker _ (hNL h)).2 h, add_zero]
    · rintro ⟨hL, rfl⟩
      have hm : -l (φ x) + x ∈ L := L.add_mem (L.neg_mem (hlL _)) hL
      refine (hker _ hm).1 ?_
      have e := hadd _ (hlL (φ x)) _ hm
      rw [show l (φ x) + (-l (φ x) + x) = x by abel, hl] at e
      have e2 := e.symm
      rwa [add_eq_left] at e2
  have hfin : S.Finite := S.toFinite
  have hset : {x | x ∈ L ∧ φ x ∈ S} =
      ⋃ s ∈ hfin.toFinset, (fun x => -l s + x) ⁻¹' (N : Set G) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe,
      Set.Finite.mem_toFinset, exists_prop, key]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨_, h2, h1, rfl⟩
    · rintro ⟨s, hs, h1, rfl⟩; exact ⟨h1, hs⟩
  rw [hset, measure_biUnion_finset]
  · simp only [measure_preimage_add]
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_card_finite_toFinset hfin]
  · intro s _ t _ hst
    refine Set.disjoint_left.2 fun x h1 h2 => hst ?_
    simp only [Set.mem_preimage, SetLike.mem_coe, key] at h1 h2
    rw [← h1.2, ← h2.2]
  · intro s _
    exact hN.preimage (measurable_const_add _)

end Count

end PI.VolStabW
