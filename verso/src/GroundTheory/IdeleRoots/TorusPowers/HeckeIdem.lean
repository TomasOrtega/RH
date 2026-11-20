import Mathlib
import GroundTheory.IdeleRoots.TorusPowers.HeckeTensor
set_option maxSynthPendingDepth 1

noncomputable section

open scoped TensorProduct NumberField.AdeleRing
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  GroundTheory.Global.SemiLocal

namespace GroundTheory.BlockD

namespace ThmBHecke

section Single

variable {K : Type} [Field K] [NumberField K]

open Classical in

def finSingleOne (w : HeightOneSpectrum (𝓞 K)) : FiniteAdeleRing (𝓞 K) K :=
  ⟨Pi.single (M := fun u : HeightOneSpectrum (𝓞 K) ↦ u.adicCompletion K) w 1, by
    refine Filter.eventually_cofinite.2 ((Set.finite_singleton w).subset fun u hu ↦ ?_)
    by_contra h
    exact hu (by rw [Pi.single_eq_of_ne h]; exact zero_mem _)⟩

/- English proof (translation)
Conclude with `Pi.single_eq_same (M := fun u : HeightOneSpectrum (𝓞 K) ↦ u.adicCompletion K) w 1`.
-/
theorem finSingleOne_self (w : HeightOneSpectrum (𝓞 K)) : finSingleOne w w = 1 := by
  classical
  exact Pi.single_eq_same (M := fun u : HeightOneSpectrum (𝓞 K) ↦ u.adicCompletion K) w 1

/- English proof (translation)
Conclude with `Pi.single_eq_of_ne (M := fun u : HeightOneSpectrum (𝓞 K) ↦ u.adicCompletion K) h 1`.
-/
theorem finSingleOne_of_ne {w u : HeightOneSpectrum (𝓞 K)} (h : u ≠ w) : finSingleOne w u = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun u : HeightOneSpectrum (𝓞 K) ↦ u.adicCompletion K) h 1

/- English proof (translation)
Establish `h1 : x * (x - 1) = 0` using `by rw [mul_sub, h, mul_one, sub_self]`. Break down `mul_eq_zero.1 h1 with h2 | h2` into its components or cases. Conclude with `Or.inl h2`. Conclude with `Or.inr (sub_eq_zero.1 h2)`.
-/
theorem eq_zero_or_one_of_mul_self {L : Type*} [Field L] {x : L} (h : x * x = x) : x = 0 ∨ x = 1 := by
  have h1 : x * (x - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact Or.inl h2
  · exact Or.inr (sub_eq_zero.1 h2)

end Single

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def idemAt (P : HeightOneSpectrum (𝓞 E)) : 𝔸[E] := (0, finSingleOne P)

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem idemAt_fst (P : HeightOneSpectrum (𝓞 E)) : (idemAt P).1 = 0 := rfl

@[simp]
/- English proof (translation)
The claim follows from `finSingleOne_self P`.
-/
theorem idemAt_snd_self (P : HeightOneSpectrum (𝓞 E)) : (idemAt P).2 P = 1 := finSingleOne_self P

/- English proof (translation)
The claim follows from `finSingleOne_of_ne h`.
-/
theorem idemAt_snd_of_ne {P w : HeightOneSpectrum (𝓞 E)} (h : w ≠ P) : (idemAt P).2 w = 0 :=
  finSingleOne_of_ne h

/- English proof (translation)
Use `Prod.ext (by change (idemAt P).1 * (idemAt P).1 = (idemAt P).1; rw [idemAt_fst, mul_zero]) (FiniteAdeleRing.ext (K := E) fun w ↦ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(idemAt P).2 w * (idemAt P).2 w = (idemAt P).2 w`. Distinguish the cases in `h : w = P`. Substitute `h` using the available equality. Rewrite using `[idemAt_snd_self, mul_one]`.

Rewrite using `[idemAt_snd_of_ne h, mul_zero]`.
-/
theorem idemAt_mul_self (P : HeightOneSpectrum (𝓞 E)) : idemAt P * idemAt P = idemAt P := by
  refine Prod.ext (by change (idemAt P).1 * (idemAt P).1 = (idemAt P).1; rw [idemAt_fst, mul_zero])
    (FiniteAdeleRing.ext (K := E) fun w ↦ ?_)
  change (idemAt P).2 w * (idemAt P).2 w = (idemAt P).2 w
  by_cases h : w = P
  · subst h; rw [idemAt_snd_self, mul_one]
  · rw [idemAt_snd_of_ne h, mul_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adele_fst_mul (a b : 𝔸[E]) : (a * b).1 = a.1 * b.1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adele_snd_mul (a b : 𝔸[E]) (w : HeightOneSpectrum (𝓞 E)) : (a * b).2 w = a.2 w * b.2 w := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adele_fst_add (a b : 𝔸[E]) : (a + b).1 = a.1 + b.1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adele_snd_add (a b : 𝔸[E]) (w : HeightOneSpectrum (𝓞 E)) : (a + b).2 w = a.2 w + b.2 w := rfl

def placeIdem (v : HeightOneSpectrum (𝓞 F)) : AF F := pairA F 0 (finSingleOne v)

/- English proof (translation)
Assemble the required witnesses or components as `⟨finSingleOne v, rfl, finSingleOne_self v, fun _ h ↦ finSingleOne_of_ne h⟩`.
-/
theorem isPlaceIdem_placeIdem (v : HeightOneSpectrum (𝓞 F)) : IsPlaceIdem F v (placeIdem v) :=
  ⟨finSingleOne v, rfl, finSingleOne_self v, fun _ h ↦ finSingleOne_of_ne h⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adeleMap_snd_apply (a : AF F) (w : HeightOneSpectrum (𝓞 E)) :
    (adeleMap F E a).2 w = completionMap (below F w) w (a.2 (below F w)) :=
  rfl

/- English proof (translation)
Take `⟨α, rfl, -, -⟩` from `h`. Conclude with `map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))`.
-/
theorem adeleMap_fst_of_isPlaceIdem {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (h : IsPlaceIdem F v ε) :
    (adeleMap F E ε).1 = 0 := by
  obtain ⟨α, rfl, -, -⟩ := h
  exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))

open Classical in
/- English proof (translation)
Take `⟨α, rfl, h1, h0⟩` from `h`. Rewrite using `[adeleMap_snd_apply]`. Use `split_ifs with hw`. Establish `: (pairA F 0 α).2 (below F w) = 1` using `by rw [hw]; exact h1`. Rewrite using `[this, map_one]`.

Establish `: (pairA F 0 α).2 (below F w) = 0` using `h0 _ hw`. Rewrite using `[this, map_zero]`.
-/
theorem adeleMap_snd_of_isPlaceIdem {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (h : IsPlaceIdem F v ε)
    (w : HeightOneSpectrum (𝓞 E)) :
    (adeleMap F E ε).2 w = if below F w = v then 1 else 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  rw [adeleMap_snd_apply]
  split_ifs with hw
  · have : (pairA F 0 α).2 (below F w) = 1 := by rw [hw]; exact h1
    rw [this, map_one]
  · have : (pairA F 0 α).2 (below F w) = 0 := h0 _ hw
    rw [this, map_zero]

/- English proof (translation)
Take `⟨α, rfl, h1, h0⟩` from `h`. Use `Prod.ext (by change (0 : Ainf F) * 0 = 0; rw [mul_zero]) (FiniteAdeleRing.ext (K := F) fun u ↦ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `α u * α u = α u`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality.

Establish `h1' : α u = 1` using `h1`. Rewrite using `[h1', mul_one]`. Establish `h0' : α u = 0` using `h0 u hu`. Rewrite using `[h0', mul_zero]`.
-/
theorem isPlaceIdem_mul_self {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (h : IsPlaceIdem F v ε) :
    ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  refine Prod.ext (by change (0 : Ainf F) * 0 = 0; rw [mul_zero]) (FiniteAdeleRing.ext (K := F) fun u ↦ ?_)
  change α u * α u = α u
  by_cases hu : u = v
  · subst hu
    have h1' : α u = 1 := h1
    rw [h1', mul_one]
  · have h0' : α u = 0 := h0 u hu
    rw [h0', mul_zero]

/- English proof (translation)
Rewrite using `[mem_intAE_iff, ← adeleEquiv_snd]`. Both sides reduce to the same expression.
-/
theorem finPart_mem_intAE_iff (z : AE F E) :
    finPart F E z ∈ intAE F E ↔ ∀ w, (adeleEquiv F E z).2 w ∈ w.adicCompletionIntegers E := by
  rw [mem_intAE_iff, ← adeleEquiv_snd]
  rfl

/- English proof (translation)
Rewrite using `[finPart_mem_intAE_iff, map_mul, adeleEquiv_incA]`. Both sides reduce to the same expression.
-/
theorem finPart_mul_incA_mem_iff (e : AE F E) (x : E) :
    finPart F E (e * incA F E x) ∈ intAE F E ↔
      ∀ w, (adeleEquiv F E e).2 w * algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E := by
  rw [finPart_mem_intAE_iff, map_mul, adeleEquiv_incA]
  rfl

/- English proof (translation)
Establish `hc : algebraMap E (w.adicCompletion E) ((x : E)⁻¹) = (((x : E)⁻¹ : E) : w.adicCompletion E)` using `rfl`. Rewrite using `[hc, coe_mem_adicCompletionIntegers_iff, map_inv₀]`. Establish `hx0 : w.valuation E (x : E) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`. Conclude with `hx` after adjusting the coercions.

Rewrite using `[inv_le_one₀ (zero_lt_iff.2 hx0), ← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E)]`. Conclude with `⟨fun h ↦ le_antisymm (w.valuation_le_one x) h, fun h ↦ h.ge⟩`.
-/
theorem inv_mem_adicCompletionIntegers_iff (w : HeightOneSpectrum (𝓞 E)) {x : 𝓞 E} (hx : x ≠ 0) :
    algebraMap E (w.adicCompletion E) ((x : E)⁻¹) ∈ w.adicCompletionIntegers E ↔ x ∉ w.asIdeal := by
  have hc : algebraMap E (w.adicCompletion E) ((x : E)⁻¹) = (((x : E)⁻¹ : E) : w.adicCompletion E) := rfl
  rw [hc, coe_mem_adicCompletionIntegers_iff, map_inv₀]
  have hx0 : w.valuation E (x : E) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact_mod_cast hx
  rw [inv_le_one₀ (zero_lt_iff.2 hx0), ← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E)]
  exact ⟨fun h ↦ le_antisymm (w.valuation_le_one x) h, fun h ↦ h.ge⟩

/- English proof (translation)
Rewrite using `[finPart_mul_incA_mem_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h push_neg at h`. Take `⟨w, hw⟩` from `h`. Break down `h01 w with h0 | h1` into its components or cases.

Rewrite `hw` using `[h0, zero_mul]`. Conclude with `absurd (zero_mem _) hw`. Rewrite `hw` using `[h1, one_mul, inv_mem_adicCompletionIntegers_iff w hx, not_not]`. Conclude with `⟨w, h1, hw⟩`. Introduce and unpack `⟨w, h1, hxw⟩ hall`.

Use `hall w` as an intermediate fact. Rewrite `this` using `[h1, one_mul, inv_mem_adicCompletionIntegers_iff w hx]`. Conclude with `this hxw`.
-/
theorem char_iff_exists {e : AE F E} (h01 : ∀ w, (adeleEquiv F E e).2 w = 0 ∨ (adeleEquiv F E e).2 w = 1)
    {x : 𝓞 E} (hx : x ≠ 0) :
    finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E ↔
      ∃ w, (adeleEquiv F E e).2 w = 1 ∧ x ∈ w.asIdeal := by
  rw [finPart_mul_incA_mem_iff]
  constructor
  · intro h
    push_neg at h
    obtain ⟨w, hw⟩ := h
    rcases h01 w with h0 | h1
    · rw [h0, zero_mul] at hw
      exact absurd (zero_mem _) hw
    · rw [h1, one_mul, inv_mem_adicCompletionIntegers_iff w hx, not_not] at hw
      exact ⟨w, h1, hw⟩
  · rintro ⟨w, h1, hxw⟩ hall
    have := hall w
    rw [h1, one_mul, inv_mem_adicCompletionIntegers_iff w hx] at this
    exact this hxw

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h (HeightOneSpectrum.ext (w.isMaximal.eq_of_le P.isPrime.ne_top hc))`.
-/
theorem exists_mem_not_mem {P w : HeightOneSpectrum (𝓞 E)} (h : w ≠ P) :
    ∃ x : 𝓞 E, x ∈ w.asIdeal ∧ x ∉ P.asIdeal := by
  by_contra hc
  push_neg at hc
  exact h (HeightOneSpectrum.ext (w.isMaximal.eq_of_le P.isPrime.ne_top hc))

/- English proof (translation)
Use `set a := adeleEquiv F E e with ha`. Establish `ha2 : a * a = a` using `by rw [ha, ← map_mul, he]`. Establish `haε : a * adeleMap F E ε = a` using `by rw [ha, ← adeleEquiv_algebraMap, ← map_mul, hee]`. Establish `hfst : a.1 = 0`. Establish `h` using `congrArg Prod.fst haε`.

Express the relevant statement in the definitionally equal form `a.1 * (adeleMap F E ε).1 = a.1 at h`. Rewrite `h` using `[adeleMap_fst_of_isPlaceIdem hε, mul_zero]`. Conclude with `h.symm`. Establish `h01 : ∀ w, a.2 w = 0 ∨ a.2 w = 1` using `fun w ↦ by`. Establish `h` using `congrArg (fun b : 𝔸[E] ↦ b.2 w) ha2`.

Conclude with `eq_zero_or_one_of_mul_self h`. Establish `hchar : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ ∃ w, a.2 w = 1 ∧ x ∈ w.asIdeal)` using `fun x hx ↦ (hP x hx).trans (char_iff_exists h01 hx)`. Establish `hsupp : ∀ w, a.2 w = 1 → w = P`. Introduce `w hw`. Assume the negation of the conclusion as `hne`.

Take `⟨x, hxw, hxP⟩` from `exists_mem_not_mem hne`. Establish `hx0 : x ≠ 0` using `fun h0 ↦ hxP (h0 ▸ zero_mem _)`. Conclude with `hxP ((hchar x hx0).2 ⟨w, hw, hxw⟩)`. Establish `hP1 : a.2 P = 1`. Take `⟨x, hxP, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot`.

Take `⟨w, hw, -⟩` from `(hchar x hx0).1 hxP`. Rewrite using `[← hsupp w hw]` and apply the resulting hypothesis. Use `Prod.ext hfst (FiniteAdeleRing.ext (K := E) fun w ↦ ?_)` and prove the remaining obligations. Distinguish the cases in `hw : w = P`. Substitute `hw` using the available equality.

Rewrite using `[hP1, idemAt_snd_self]`. Rewrite using `[idemAt_snd_of_ne hw]`. Break down `h01 w with h0 | h1` into its components or cases. Conclude with `h0`. Conclude with `absurd (hsupp w h1) hw`.
-/
theorem adeleEquiv_eq_idemAt {e : AE F E} {P : HeightOneSpectrum (𝓞 E)} (he : e * e = e)
    {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (hε : IsPlaceIdem F v ε)
    (hee : e * algebraMap (AF F) (AE F E) ε = e)
    (hP : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E)) :
    adeleEquiv F E e = idemAt P := by
  set a := adeleEquiv F E e with ha
  have ha2 : a * a = a := by rw [ha, ← map_mul, he]
  have haε : a * adeleMap F E ε = a := by rw [ha, ← adeleEquiv_algebraMap, ← map_mul, hee]
  have hfst : a.1 = 0 := by
    have h := congrArg Prod.fst haε
    change a.1 * (adeleMap F E ε).1 = a.1 at h
    rw [adeleMap_fst_of_isPlaceIdem hε, mul_zero] at h
    exact h.symm
  have h01 : ∀ w, a.2 w = 0 ∨ a.2 w = 1 := fun w ↦ by
    have h := congrArg (fun b : 𝔸[E] ↦ b.2 w) ha2
    exact eq_zero_or_one_of_mul_self h
  have hchar : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ ∃ w, a.2 w = 1 ∧ x ∈ w.asIdeal) :=
    fun x hx ↦ (hP x hx).trans (char_iff_exists h01 hx)
  have hsupp : ∀ w, a.2 w = 1 → w = P := by
    intro w hw
    by_contra hne
    obtain ⟨x, hxw, hxP⟩ := exists_mem_not_mem hne
    have hx0 : x ≠ 0 := fun h0 ↦ hxP (h0 ▸ zero_mem _)
    exact hxP ((hchar x hx0).2 ⟨w, hw, hxw⟩)
  have hP1 : a.2 P = 1 := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    obtain ⟨w, hw, -⟩ := (hchar x hx0).1 hxP
    rwa [← hsupp w hw]
  refine Prod.ext hfst (FiniteAdeleRing.ext (K := E) fun w ↦ ?_)
  by_cases hw : w = P
  · subst hw; rw [hP1, idemAt_snd_self]
  · rw [idemAt_snd_of_ne hw]
    rcases h01 w with h0 | h1
    · exact h0
    · exact absurd (hsupp w h1) hw

/- English proof (translation)
Break down `h with ⟨⟨⟨he2, hes, v, ε, hε, hsum⟩, hchar⟩, -⟩ | ⟨-, ⟨v, ε, hε, rfl⟩, hchar⟩` into its components or cases. Use `adeleEquiv_eq_idemAt he2 hε ?_ hchar` and prove the remaining obligations. Rewrite using `[← hsum, mul_add, he2, hes, add_zero]`. Use `adeleEquiv_eq_idemAt ?_ hε ?_ hchar` and prove the remaining obligations. Rewrite using `[← map_mul, isPlaceIdem_mul_self hε]`.

Rewrite using `[← map_mul, isPlaceIdem_mul_self hε]`.
-/
theorem adeleEquiv_eq_idemAt_of_isPrimeIdem {σ : E →ₐ[F] E} {P : HeightOneSpectrum (𝓞 E)}
    {e f : AE F E} (h : IsPrimeIdem σ P e f) : adeleEquiv F E e = idemAt P := by
  rcases h with ⟨⟨⟨he2, hes, v, ε, hε, hsum⟩, hchar⟩, -⟩ | ⟨-, ⟨v, ε, hε, rfl⟩, hchar⟩
  · refine adeleEquiv_eq_idemAt he2 hε ?_ hchar
    rw [← hsum, mul_add, he2, hes, add_zero]
  · refine adeleEquiv_eq_idemAt ?_ hε ?_ hchar
    · rw [← map_mul, isPlaceIdem_mul_self hε]
    · rw [← map_mul, isPlaceIdem_mul_self hε]

/- English proof (translation)
Introduce `x hx`. Establish `h01 : ∀ w, (adeleEquiv F E e).2 w = 0 ∨ (adeleEquiv F E e).2 w = 1` using `fun w ↦ by`. Rewrite using `[h]`. Distinguish the cases in `hw : w = P`. Substitute `hw` using the available equality.

Conclude with `Or.inr (idemAt_snd_self w)`. Conclude with `Or.inl (idemAt_snd_of_ne hw)`. Rewrite using `[char_iff_exists h01 hx, h]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun hxP ↦ ⟨P, idemAt_snd_self P, hxP⟩`.

Introduce and unpack `⟨w, hw, hxw⟩`. Distinguish the cases in `hwP : w = P`. Conclude with `hwP ▸ hxw`. Rewrite `hw` using `[idemAt_snd_of_ne hwP]`. Conclude with `absurd hw zero_ne_one`.
-/
theorem char_of_adeleEquiv_eq_idemAt {e : AE F E} {P : HeightOneSpectrum (𝓞 E)}
    (h : adeleEquiv F E e = idemAt P) :
    ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E) := by
  intro x hx
  have h01 : ∀ w, (adeleEquiv F E e).2 w = 0 ∨ (adeleEquiv F E e).2 w = 1 := fun w ↦ by
    rw [h]
    by_cases hw : w = P
    · subst hw; exact Or.inr (idemAt_snd_self w)
    · exact Or.inl (idemAt_snd_of_ne hw)
  rw [char_iff_exists h01 hx, h]
  constructor
  · exact fun hxP ↦ ⟨P, idemAt_snd_self P, hxP⟩
  · rintro ⟨w, hw, hxw⟩
    by_cases hwP : w = P
    · exact hwP ▸ hxw
    · rw [idemAt_snd_of_ne hwP] at hw
      exact absurd hw zero_ne_one

section Conj

variable {σ : E →ₐ[F] E}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_AE_eq (a : AF F) : algebraMap (AF F) (AE F E) a = a ⊗ₜ 1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cA_tmul (a : AF F) (x : E) : cA σ (a ⊗ₜ x) = a ⊗ₜ σ x := rfl

/- English proof (translation)
Rewrite using `[algebraMap_AE_eq, cA_tmul, map_one]`.
-/
theorem cA_algebraMap (a : AF F) :
    cA σ (algebraMap (AF F) (AE F E) a) = algebraMap (AF F) (AE F E) a := by
  rw [algebraMap_AE_eq, cA_tmul, map_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cA_incA (x : E) : cA σ (incA F E x) = incA F E (σ x) := rfl

/- English proof (translation)
Take `⟨τ⟩` from `(inferInstance : Nonempty (E →+* ℂ))`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.
-/
theorem IsCMExt.sigma_sigma (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `tmul a x => rw [cA_tmul, cA_tmul, IsCMExt.sigma_sigma h]`. Consider the case `add y z hy hz => rw [map_add, map_add, hy, hz]`.
-/
theorem cA_cA (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x => rw [cA_tmul, cA_tmul, IsCMExt.sigma_sigma h]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨w⟩` from `(inferInstance : Nonempty (NumberField.InfinitePlace E))`. Establish `hreal : w.IsReal`. Rewrite using `[← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff, NumberField.ComplexEmbedding.isReal_iff]`.

Use `RingHom.ext fun x ↦ ?_` and prove the remaining obligations. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`. Express the relevant statement in the definitionally equal form `star (w.embedding x) = w.embedding x`. Rewrite using `[← h.2.2.2, hc]`. Conclude with `NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal`.
-/
theorem IsCMExt.exists_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
  have hreal : w.IsReal := by
    rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff,
      NumberField.ComplexEmbedding.isReal_iff]
    refine RingHom.ext fun x ↦ ?_
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    change star (w.embedding x) = w.embedding x
    rw [← h.2.2.2, hc]
  exact NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal

/- English proof (translation)
Take `⟨y, hy⟩` from `IsCMExt.exists_ne h`. Use `⟨y - σ y, sub_ne_zero.2 (Ne.symm hy), by rw [map_sub, IsCMExt.sigma_sigma h, neg_sub], ?_⟩` and prove the remaining obligations. Use `set θ := y - σ y with hθ`. Establish `hθ0 : θ ≠ 0` using `sub_ne_zero.2 (Ne.symm hy)`. Establish `hσθ : σ θ = -θ` using `by rw [hθ, map_sub, IsCMExt.sigma_sigma h, neg_sub]`.

Establish `hli : LinearIndependent F ![(1 : E), θ]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Rewrite `hst` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`. Establish `h2` using `congrArg σ hst`.

Rewrite `h2` using `[map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσθ, map_zero]`. Establish `hs2 : algebraMap F E (2 * s) = 0`. Rewrite using `[map_mul, map_ofNat]`. Take the linear combination `hst + h2`. Establish `hs : s = 0` using `(mul_eq_zero.1 ((map_eq_zero_iff _ (algebraMap F E).injective).1 hs2)).resolve_left two_ne_zero`.

Use `⟨hs, ?_⟩` and prove the remaining obligations. Rewrite `hst` using `[hs, map_zero, zero_add]`. Conclude with `(map_eq_zero_iff _ (algebraMap F E).injective).1 ((mul_eq_zero.1 hst).resolve_right hθ0)`. Establish `hcard : Fintype.card (Fin 2) = Module.finrank F E` using `by rw [Fintype.card_fin, h.2.2.1]`. Use `set B := basisOfLinearIndependentOfCardEqFinrank hli hcard`.

Introduce `x`. Use `⟨B.repr x 0, B.repr x 1, ?_⟩` and prove the remaining obligations. Establish `hx` using `B.sum_repr x`. Rewrite `hx` using `[Fin.sum_univ_two, coe_basisOfLinearIndependentOfCardEqFinrank]`. Simplify using `using hx.symm`.
-/
theorem IsCMExt.exists_decomp (h : IsCMExt F E σ) :
    ∃ θ : E, θ ≠ 0 ∧ σ θ = -θ ∧ ∀ x : E, ∃ s t : F, x = s • (1 : E) + t • θ := by
  obtain ⟨y, hy⟩ := IsCMExt.exists_ne h
  refine ⟨y - σ y, sub_ne_zero.2 (Ne.symm hy), by rw [map_sub, IsCMExt.sigma_sigma h, neg_sub], ?_⟩
  set θ := y - σ y with hθ
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hσθ : σ θ = -θ := by rw [hθ, map_sub, IsCMExt.sigma_sigma h, neg_sub]
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have h2 := congrArg σ hst
    rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσθ, map_zero] at h2
    have hs2 : algebraMap F E (2 * s) = 0 := by
      rw [map_mul, map_ofNat]
      linear_combination hst + h2
    have hs : s = 0 :=
      (mul_eq_zero.1 ((map_eq_zero_iff _ (algebraMap F E).injective).1 hs2)).resolve_left two_ne_zero
    refine ⟨hs, ?_⟩
    rw [hs, map_zero, zero_add] at hst
    exact (map_eq_zero_iff _ (algebraMap F E).injective).1 ((mul_eq_zero.1 hst).resolve_right hθ0)
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [Fintype.card_fin, h.2.2.1]
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  intro x
  refine ⟨B.repr x 0, B.repr x 1, ?_⟩
  have hx := B.sum_repr x
  rw [Fin.sum_univ_two, coe_basisOfLinearIndependentOfCardEqFinrank] at hx
  simpa using hx.symm

/- English proof (translation)
Take `⟨θ, -, hσθ, hdec⟩` from `IsCMExt.exists_decomp h`. Establish `hrep : ∀ z : AE F E, ∃ a b : AF F, z = algebraMap (AF F) (AE F E) a + algebraMap (AF F) (AE F E) b * incA F E θ`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`.

Consider the case `tmul c x`. Take `⟨s, t, rfl⟩` from `hdec x`. Use `⟨s • c, t • c, ?_⟩` and prove the remaining obligations. Rewrite using `[TensorProduct.tmul_add, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, algebraMap_AE_eq, algebraMap_AE_eq]`. Express the relevant statement in the definitionally equal form `_ = _ + ((t • c) ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] θ)`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Consider the case `add y z hy hz`. Take `⟨a, b, rfl⟩` from `hy`. Take `⟨a', b', rfl⟩` from `hz`. Conclude with `⟨a + a', b + b', by rw [map_add, map_add]; ring⟩`.

Take `⟨a, b, rfl⟩` from `hrep z`. Use `⟨a, ?_⟩` and prove the remaining obligations. Use `set X := algebraMap (AF F) (AE F E) b * incA F E θ with hX`. Establish `hcX : cA σ X = -X`. Rewrite using `[hX, map_mul, cA_algebraMap, cA_incA, hσθ, map_neg, mul_neg]`.

Rewrite `hz` using `[map_add, cA_algebraMap, hcX]`. Establish `h2 : (2 : F) • X = 0`. Rewrite using `[two_smul]`. Take the linear combination `-hz`. Establish `hX0 : X = 0` using `(smul_eq_zero.1 h2).resolve_left two_ne_zero`.

Rewrite using `[hX0, add_zero]`.
-/
theorem exists_eq_algebraMap_of_cA_eq (h : IsCMExt F E σ) {z : AE F E} (hz : cA σ z = z) :
    ∃ a : AF F, z = algebraMap (AF F) (AE F E) a := by
  obtain ⟨θ, -, hσθ, hdec⟩ := IsCMExt.exists_decomp h
  have hrep : ∀ z : AE F E, ∃ a b : AF F,
      z = algebraMap (AF F) (AE F E) a + algebraMap (AF F) (AE F E) b * incA F E θ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul c x =>
      obtain ⟨s, t, rfl⟩ := hdec x
      refine ⟨s • c, t • c, ?_⟩
      rw [TensorProduct.tmul_add, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
        algebraMap_AE_eq, algebraMap_AE_eq]
      change _ = _ + ((t • c) ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] θ)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add y z hy hz =>
      obtain ⟨a, b, rfl⟩ := hy
      obtain ⟨a', b', rfl⟩ := hz
      exact ⟨a + a', b + b', by rw [map_add, map_add]; ring⟩
  obtain ⟨a, b, rfl⟩ := hrep z
  refine ⟨a, ?_⟩
  set X := algebraMap (AF F) (AE F E) b * incA F E θ with hX
  have hcX : cA σ X = -X := by
    rw [hX, map_mul, cA_algebraMap, cA_incA, hσθ, map_neg, mul_neg]
  rw [map_add, cA_algebraMap, hcX] at hz
  have h2 : (2 : F) • X = 0 := by
    rw [two_smul]
    linear_combination -hz
  have hX0 : X = 0 := (smul_eq_zero.1 h2).resolve_left two_ne_zero
  rw [hX0, add_zero]

end Conj

/- English proof (translation)
The claim follows from `(adeleEquiv F E).injective`.
-/
theorem adeleEquiv_injective : Function.Injective (adeleEquiv F E) := (adeleEquiv F E).injective

/- English proof (translation)
Use `set e := (adeleEquiv F E).symm (idemAt P) with he`. Establish `heP : adeleEquiv F E e = idemAt P` using `by rw [he, AlgEquiv.apply_symm_apply]`. Use `set v := below F P with hv`. Use `set ε := placeIdem v with hεdef`. Establish `hε : IsPlaceIdem F v ε` using `isPlaceIdem_placeIdem v`.

Establish `hchar` using `char_of_adeleEquiv_eq_idemAt heP`. Establish `he2 : e * e = e` using `adeleEquiv_injective (by rw [map_mul, heP, idemAt_mul_self])`. Establish `hPε : idemAt P * adeleMap F E ε = idemAt P`. Use `Prod.ext (by change (idemAt P).1 * (adeleMap F E ε).1 = (idemAt P).1; rw [idemAt_fst, zero_mul]) (FiniteAdeleRing.ext (K := E) fun w ↦ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(idemAt P).2 w * (adeleMap F E ε).2 w = (idemAt P).2 w`.

Distinguish the cases in `hw : w = P`. Substitute `hw` using the available equality. Rewrite using `[adeleMap_snd_of_isPlaceIdem hε, if_pos hv.symm, mul_one]`. Rewrite using `[idemAt_snd_of_ne hw, zero_mul]`. Establish `heε : e * algebraMap (AF F) (AE F E) ε = e` using `adeleEquiv_injective (by rw [map_mul, adeleEquiv_algebraMap, heP, hPε])`.

Distinguish the cases in `hB : ∃ Q : HeightOneSpectrum (𝓞 E), Q ≠ P ∧ below F Q = v`. Take `⟨Q, hQP, hQv⟩` from `hB`. Use `set g := cA σ e with hg`. Establish `hgε : g * algebraMap (AF F) (AE F E) ε = g`. Rewrite using `[hg, ← cA_algebraMap (σ := σ), ← map_mul, heε]`.

Establish `hgfst : (adeleEquiv F E g).1 = 0`. Establish `h` using `congrArg (fun b : 𝔸[E] ↦ b.1) (congrArg (adeleEquiv F E) hgε)`. Simplify using `only [map_mul, adeleEquiv_algebraMap] at h`. Express the relevant statement in the definitionally equal form `(adeleEquiv F E g).1 * (adeleMap F E ε).1 = _ at h`. Rewrite `h` using `[adeleMap_fst_of_isPlaceIdem hε, mul_zero]`.

Conclude with `h.symm`. Establish `hgsnd : ∀ w, below F w ≠ v → (adeleEquiv F E g).2 w = 0`. Introduce `w hw`. Establish `h` using `congrArg (fun b : 𝔸[E] ↦ b.2 w) (congrArg (adeleEquiv F E) hgε)`. Simplify using `only [map_mul, adeleEquiv_algebraMap] at h`.

Express the relevant statement in the definitionally equal form `(adeleEquiv F E g).2 w * (adeleMap F E ε).2 w = _ at h`. Rewrite `h` using `[adeleMap_snd_of_isPlaceIdem hε, if_neg hw, mul_zero]`. Conclude with `h.symm`. Establish `hprod : e * g = 0`. Take `⟨b, hb⟩` from `exists_eq_algebraMap_of_cA_eq hσ (z := e * g) (by rw [map_mul, hg, cA_cA hσ, mul_comm])`.

Establish `himg : adeleEquiv F E (e * g) = adeleMap F E b` using `by rw [hb, adeleEquiv_algebraMap]`. Establish `hbv : b.2 v = 0`. Establish `h` using `congrArg (fun c : 𝔸[E] ↦ c.2 Q) himg`. Rewrite `h` using `[map_mul, adele_snd_mul, heP, idemAt_snd_of_ne hQP, zero_mul, adeleMap_snd_apply]`. Establish `h' : b.2 (below F Q) = 0` using `(map_eq_zero_iff _ (completionMap _ _).injective).1 h.symm`.

Rewrite `h'` using `[hQv]`. Then use the resulting hypothesis. Use `(map_eq_zero_iff _ adeleEquiv_injective).1 ?_` and prove the remaining obligations. Use `Prod.ext ?_ (FiniteAdeleRing.ext (K := E) fun w ↦ ?_)` and prove the remaining obligations. Rewrite using `[map_mul, adele_fst_mul, heP, idemAt_fst, zero_mul]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `(adeleEquiv F E (e * g)).2 w = 0`. Distinguish the cases in `hw : w = P`. Substitute `hw` using the available equality. Rewrite using `[himg, adeleMap_snd_apply]`. Establish `: b.2 (below F w) = 0` using `hbv`.

Rewrite using `[this, map_zero]`. Rewrite using `[map_mul, adele_snd_mul, heP, idemAt_snd_of_ne hw, zero_mul]`. Establish `hsum : e + g = algebraMap (AF F) (AE F E) ε`. Take `⟨a, ha⟩` from `exists_eq_algebraMap_of_cA_eq hσ (z := e + g) (by rw [map_add, hg, cA_cA hσ, add_comm])`. Establish `himg : adeleEquiv F E (e + g) = adeleMap F E a` using `by rw [ha, adeleEquiv_algebraMap]`.

Establish `hgP : (adeleEquiv F E g).2 P = 0`. Establish `h` using `congrArg (fun c : 𝔸[E] ↦ c.2 P) (congrArg (adeleEquiv F E) hprod)`. Rewrite `h` using `[map_mul, adele_snd_mul, heP, idemAt_snd_self, one_mul, map_zero]`. Conclude with `h`. Establish `hav : a.2 v = 1`.

Establish `h` using `congrArg (fun c : 𝔸[E] ↦ c.2 P) himg`. Rewrite `h` using `[map_add, adele_snd_add, heP, idemAt_snd_self, hgP, add_zero, adeleMap_snd_apply]`. Establish `h' : completionMap (below F P) P (a.2 (below F P)) = completionMap (below F P) P 1`. Rewrite using `[← h, map_one]`. Conclude with `(completionMap _ _).injective h'`.

Rewrite using `[ha]`. Use `congr 1`. Apply `adeleMap_injective (K := F) (L := E)` to reduce the goal to its premises. Use `Prod.ext ?_ (FiniteAdeleRing.ext (K := E) fun w ↦ ?_)` and prove the remaining obligations. Rewrite using `[← himg, adeleMap_fst_of_isPlaceIdem hε]`.

Rewrite using `[map_add, adele_fst_add, heP, hgfst, idemAt_fst, add_zero]`. Express the relevant statement in the definitionally equal form `(adeleMap F E a).2 w = (adeleMap F E ε).2 w`. Rewrite using `[adeleMap_snd_of_isPlaceIdem hε]`. Use `split_ifs with hw`. Rewrite using `[adeleMap_snd_apply]`.

Establish `: a.2 (below F w) = 1` using `by rw [hw]; exact hav`. Rewrite using `[this, map_one]`. Rewrite using `[← himg]`. Rewrite using `[map_add, adele_snd_add]`. Establish `hwP : w ≠ P` using `fun h ↦ hw (h ▸ hv.symm)`.

Rewrite using `[heP, idemAt_snd_of_ne hwP, hgsnd w hw, add_zero]`. Conclude with `⟨e + g, Or.inl ⟨⟨⟨he2, hprod, v, ε, hε, hsum⟩, hchar⟩, rfl⟩⟩`. Use `push_neg at hB`. Use `⟨e, Or.inr ⟨rfl, ⟨v, ε, hε, ?_⟩, hchar⟩⟩` and prove the remaining obligations. Apply `adeleEquiv_injective` to reduce the goal to its premises.

Rewrite using `[heP, adeleEquiv_algebraMap]`. Use `Prod.ext (by rw [idemAt_fst, adeleMap_fst_of_isPlaceIdem hε]) (FiniteAdeleRing.ext (K := E) fun w ↦ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(idemAt P).2 w = (adeleMap F E ε).2 w`. Rewrite using `[adeleMap_snd_of_isPlaceIdem hε]`. Distinguish the cases in `hw : w = P`.

Substitute `hw` using the available equality. Rewrite using `[idemAt_snd_self, if_pos hv.symm]`. Rewrite using `[idemAt_snd_of_ne hw, if_neg (hB w hw)]`.
-/
theorem exists_isPrimeIdem {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) :
    ∃ f, IsPrimeIdem σ P ((adeleEquiv F E).symm (idemAt P)) f := by
  set e := (adeleEquiv F E).symm (idemAt P) with he
  have heP : adeleEquiv F E e = idemAt P := by rw [he, AlgEquiv.apply_symm_apply]
  set v := below F P with hv
  set ε := placeIdem v with hεdef
  have hε : IsPlaceIdem F v ε := isPlaceIdem_placeIdem v
  have hchar := char_of_adeleEquiv_eq_idemAt heP
  have he2 : e * e = e := adeleEquiv_injective (by rw [map_mul, heP, idemAt_mul_self])
  have hPε : idemAt P * adeleMap F E ε = idemAt P := by
    refine Prod.ext (by change (idemAt P).1 * (adeleMap F E ε).1 = (idemAt P).1; rw [idemAt_fst, zero_mul])
      (FiniteAdeleRing.ext (K := E) fun w ↦ ?_)
    change (idemAt P).2 w * (adeleMap F E ε).2 w = (idemAt P).2 w
    by_cases hw : w = P
    · subst hw
      rw [adeleMap_snd_of_isPlaceIdem hε, if_pos hv.symm, mul_one]
    · rw [idemAt_snd_of_ne hw, zero_mul]
  have heε : e * algebraMap (AF F) (AE F E) ε = e :=
    adeleEquiv_injective (by rw [map_mul, adeleEquiv_algebraMap, heP, hPε])
  by_cases hB : ∃ Q : HeightOneSpectrum (𝓞 E), Q ≠ P ∧ below F Q = v
  ·
    obtain ⟨Q, hQP, hQv⟩ := hB
    set g := cA σ e with hg
    have hgε : g * algebraMap (AF F) (AE F E) ε = g := by
      rw [hg, ← cA_algebraMap (σ := σ), ← map_mul, heε]
    have hgfst : (adeleEquiv F E g).1 = 0 := by
      have h := congrArg (fun b : 𝔸[E] ↦ b.1) (congrArg (adeleEquiv F E) hgε)
      simp only [map_mul, adeleEquiv_algebraMap] at h
      change (adeleEquiv F E g).1 * (adeleMap F E ε).1 = _ at h
      rw [adeleMap_fst_of_isPlaceIdem hε, mul_zero] at h
      exact h.symm
    have hgsnd : ∀ w, below F w ≠ v → (adeleEquiv F E g).2 w = 0 := by
      intro w hw
      have h := congrArg (fun b : 𝔸[E] ↦ b.2 w) (congrArg (adeleEquiv F E) hgε)
      simp only [map_mul, adeleEquiv_algebraMap] at h
      change (adeleEquiv F E g).2 w * (adeleMap F E ε).2 w = _ at h
      rw [adeleMap_snd_of_isPlaceIdem hε, if_neg hw, mul_zero] at h
      exact h.symm

    have hprod : e * g = 0 := by
      obtain ⟨b, hb⟩ := exists_eq_algebraMap_of_cA_eq hσ (z := e * g)
        (by rw [map_mul, hg, cA_cA hσ, mul_comm])
      have himg : adeleEquiv F E (e * g) = adeleMap F E b := by rw [hb, adeleEquiv_algebraMap]
      have hbv : b.2 v = 0 := by
        have h := congrArg (fun c : 𝔸[E] ↦ c.2 Q) himg
        rw [map_mul, adele_snd_mul, heP, idemAt_snd_of_ne hQP, zero_mul, adeleMap_snd_apply] at h
        have h' : b.2 (below F Q) = 0 := (map_eq_zero_iff _ (completionMap _ _).injective).1 h.symm
        rwa [hQv] at h'
      refine (map_eq_zero_iff _ adeleEquiv_injective).1 ?_
      refine Prod.ext ?_ (FiniteAdeleRing.ext (K := E) fun w ↦ ?_)
      · rw [map_mul, adele_fst_mul, heP, idemAt_fst, zero_mul]
        rfl
      · change (adeleEquiv F E (e * g)).2 w = 0
        by_cases hw : w = P
        · subst hw
          rw [himg, adeleMap_snd_apply]
          have : b.2 (below F w) = 0 := hbv
          rw [this, map_zero]
        · rw [map_mul, adele_snd_mul, heP, idemAt_snd_of_ne hw, zero_mul]

    have hsum : e + g = algebraMap (AF F) (AE F E) ε := by
      obtain ⟨a, ha⟩ := exists_eq_algebraMap_of_cA_eq hσ (z := e + g)
        (by rw [map_add, hg, cA_cA hσ, add_comm])
      have himg : adeleEquiv F E (e + g) = adeleMap F E a := by rw [ha, adeleEquiv_algebraMap]
      have hgP : (adeleEquiv F E g).2 P = 0 := by
        have h := congrArg (fun c : 𝔸[E] ↦ c.2 P) (congrArg (adeleEquiv F E) hprod)
        rw [map_mul, adele_snd_mul, heP, idemAt_snd_self, one_mul, map_zero] at h
        exact h
      have hav : a.2 v = 1 := by
        have h := congrArg (fun c : 𝔸[E] ↦ c.2 P) himg
        rw [map_add, adele_snd_add, heP, idemAt_snd_self, hgP, add_zero, adeleMap_snd_apply] at h
        have h' : completionMap (below F P) P (a.2 (below F P)) = completionMap (below F P) P 1 := by
          rw [← h, map_one]
        exact (completionMap _ _).injective h'
      rw [ha]
      congr 1
      apply adeleMap_injective (K := F) (L := E)
      refine Prod.ext ?_ (FiniteAdeleRing.ext (K := E) fun w ↦ ?_)
      · rw [← himg, adeleMap_fst_of_isPlaceIdem hε]
        rw [map_add, adele_fst_add, heP, hgfst, idemAt_fst, add_zero]
      · change (adeleMap F E a).2 w = (adeleMap F E ε).2 w
        rw [adeleMap_snd_of_isPlaceIdem hε]
        split_ifs with hw
        · rw [adeleMap_snd_apply]
          have : a.2 (below F w) = 1 := by rw [hw]; exact hav
          rw [this, map_one]
        · rw [← himg]
          rw [map_add, adele_snd_add]
          have hwP : w ≠ P := fun h ↦ hw (h ▸ hv.symm)
          rw [heP, idemAt_snd_of_ne hwP, hgsnd w hw, add_zero]
    exact ⟨e + g, Or.inl ⟨⟨⟨he2, hprod, v, ε, hε, hsum⟩, hchar⟩, rfl⟩⟩
  ·
    push_neg at hB
    refine ⟨e, Or.inr ⟨rfl, ⟨v, ε, hε, ?_⟩, hchar⟩⟩
    apply adeleEquiv_injective
    rw [heP, adeleEquiv_algebraMap]
    refine Prod.ext (by rw [idemAt_fst, adeleMap_fst_of_isPlaceIdem hε]) (FiniteAdeleRing.ext (K := E) fun w ↦ ?_)
    change (idemAt P).2 w = (adeleMap F E ε).2 w
    rw [adeleMap_snd_of_isPlaceIdem hε]
    by_cases hw : w = P
    · subst hw; rw [idemAt_snd_self, if_pos hv.symm]
    · rw [idemAt_snd_of_ne hw, if_neg (hB w hw)]

end ThmBHecke

end GroundTheory.BlockD
