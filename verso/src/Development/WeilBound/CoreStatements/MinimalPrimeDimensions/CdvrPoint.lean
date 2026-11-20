import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.NvalLeOfMul
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmallFin

namespace ChowFormHeightComparison₂.SmallGenerators

/- English proof (translation)
Establish `: IsNoetherianRing A` using `Algebra.FiniteType.isNoetherianRing (𝓞 K) A`. Establish `hcoe : ∀ a : 𝓞 K, ((algebraMap (𝓞 K) A a : A) : Ω) = algebraMap K Ω (a : K)` using `fun a => rfl`. Establish `hinj : Function.Injective (algebraMap (𝓞 K) A)` using `fun a b hab => by`. Establish `: algebraMap K Ω (a : K) = algebraMap K Ω (b : K)`. Rewrite using `[← hcoe, ← hcoe, hab]`.

Conclude with `RingOfIntegers.ext ((algebraMap K Ω).injective this)`. Set `P : Ideal A` to `{ carrier := {a | ν (a : Ω) < 1} add_mem' := fun {a b} ha hb => ν.map_add_lt ha hb zero_mem' := by simp smul_mem' := fun c x hx => by show ν ((c : Ω) * (x : Ω)) < 1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hA _ c.2)) hx }`. Establish `hP : P ≠ ⊤` using `fun h => by`.

Establish `: (1 : A) ∈ P` using `h ▸ Submodule.mem_top`. Establish `h1 : ν ((1 : A) : Ω) < 1` using `this`. Simplify using `at h1`. Take `⟨m, hm, hPm⟩` from `Ideal.exists_le_maximal P hP`. Take `⟨π, hπla, hπ⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot`.

Establish `hπm : algebraMap (𝓞 K) A π ∈ m` using `hPm (h2 π hπla)`. Establish `hπ' : algebraMap (𝓞 K) A π ≠ 0` using `fun h => hπ (hinj (h.trans (map_zero _).symm))`. Take `⟨q, hqU, hqm, hht⟩` from `exists_mem_height_map_le_one m (PrimeSpectrum.basicOpen (algebraMap (𝓞 K) A π * t)).isOpen ⟨⊥, mul_ne_zero hπ' ht, bot_le⟩`. Establish `hqπ : algebraMap (𝓞 K) A π ∉ q.asIdeal` using `fun h => hqU (Ideal.mul_mem_right _ _ h)`. Establish `hqt : t ∉ q.asIdeal` using `fun h => hqU (Ideal.mul_mem_left _ _ h)`.

Establish `hsurj` using `Ideal.Quotient.mk_surjective (I := q.asIdeal)`. Establish `hcomap : (m.map (Ideal.Quotient.mk q.asIdeal)).comap (Ideal.Quotient.mk q.asIdeal) = m`. Rewrite using `[Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]`. Conclude with `sup_eq_left.mpr hqm`. Establish `: (m.map (Ideal.Quotient.mk q.asIdeal)).IsMaximal` using `(Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm).resolve_left fun e => by`.

Rewrite `hcomap` using `[e, Ideal.comap_top]`. Conclude with `hm.ne_top hcomap.symm`. Establish `hlaM : la.asIdeal ≤ m.comap (algebraMap (𝓞 K) A)` using `fun a ha => hPm (h2 a ha)`. Establish `hmax : (m.comap (algebraMap (𝓞 K) A)) = la.asIdeal` using `(la.isMaximal.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hlaM).symm`. Establish `hinj' : Function.Injective (algebraMap (𝓞 K) (A ⧸ q.asIdeal))`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `ha0`. Establish `h1 : a ∈ q.asIdeal.comap (algebraMap (𝓞 K) A)` using `(Ideal.Quotient.eq_zero_iff_mem (I := q.asIdeal) (a := algebraMap (𝓞 K) A a)).mp ha`. Establish `h2' : (q.asIdeal.comap (algebraMap (𝓞 K) A)).IsMaximal` using `Ideal.IsPrime.isMaximal inferInstance fun h => ha0 (by simpa [h] using h1)`.

Establish `h3` using `h2'.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (Ideal.comap_mono hqm)`. Conclude with `hqπ (by`. Establish `: π ∈ q.asIdeal.comap (algebraMap (𝓞 K) A)`. Rewrite using `[h3]`. Conclude with `hπm`.

Conclude with `this)`. Take `⟨L, _, _, _, O, φ, hφ, hφi, hφm⟩` from `exists_valuationSubring_of_height_le_one (K := K) hinj' (m.map (Ideal.Quotient.mk q.asIdeal)) hht π hπ (Ideal.mem_map_of_mem _ hπm)`. Establish `nL : NumberField L` using `NumberField.of_module_finite K L`. Use `⟨L, _, nL, _, O, φ.comp (Ideal.Quotient.mk _), fun a => hφ a, fun s hs => ?_, fun h => hqt ?_⟩` and prove the remaining obligations. Establish `h1 : Ideal.Quotient.mk q.asIdeal s ∈ m.map (Ideal.Quotient.mk q.asIdeal)` using `Ideal.mem_map_of_mem _ (hPm hs)`.

Rewrite `h1` using `[← hφm, Ideal.mem_comap]`. Conclude with `ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.2 ⟨(φ _).2, h1⟩`. Establish `: φ (Ideal.Quotient.mk _ t) = 0` using `h`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff φ hφi).1 this)`.
-/
theorem point_of_val {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (la : HeightOneSpectrum (𝓞 K)) (ν : Valuation Ω Γ)
    (h2 : ∀ a ∈ la.asIdeal, ν (algebraMap K Ω (a : K)) < 1)
    (A : Subalgebra (𝓞 K) Ω) [Algebra.FiniteType (𝓞 K) A] (hA : ∀ a ∈ A, ν a ≤ 1) {t : A} (ht : t ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (O : ValuationSubring L) (φ : A →+* O),
      (∀ a : 𝓞 K, ((φ (algebraMap (𝓞 K) A a) : O) : L) = algebraMap K L (a : K)) ∧
      (∀ s : A, ν (s : Ω) < 1 → ((φ s : O) : L) ∈ O.nonunits) ∧ φ t ≠ 0 := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing (𝓞 K) A
  have hcoe : ∀ a : 𝓞 K, ((algebraMap (𝓞 K) A a : A) : Ω) = algebraMap K Ω (a : K) := fun a => rfl
  have hinj : Function.Injective (algebraMap (𝓞 K) A) := fun a b hab => by
    have : algebraMap K Ω (a : K) = algebraMap K Ω (b : K) := by
      rw [← hcoe, ← hcoe, hab]
    exact RingOfIntegers.ext ((algebraMap K Ω).injective this)
  let P : Ideal A :=
    { carrier := {a | ν (a : Ω) < 1}
      add_mem' := fun {a b} ha hb => ν.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        show ν ((c : Ω) * (x : Ω)) < 1
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hA _ c.2)) hx }
  have hP : P ≠ ⊤ := fun h => by
    have : (1 : A) ∈ P := h ▸ Submodule.mem_top
    have h1 : ν ((1 : A) : Ω) < 1 := this
    simp at h1
  obtain ⟨m, hm, hPm⟩ := Ideal.exists_le_maximal P hP
  obtain ⟨π, hπla, hπ⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
  have hπm : algebraMap (𝓞 K) A π ∈ m := hPm (h2 π hπla)
  have hπ' : algebraMap (𝓞 K) A π ≠ 0 := fun h => hπ (hinj (h.trans (map_zero _).symm))
  obtain ⟨q, hqU, hqm, hht⟩ := exists_mem_height_map_le_one m
    (PrimeSpectrum.basicOpen (algebraMap (𝓞 K) A π * t)).isOpen ⟨⊥, mul_ne_zero hπ' ht, bot_le⟩
  have hqπ : algebraMap (𝓞 K) A π ∉ q.asIdeal := fun h => hqU (Ideal.mul_mem_right _ _ h)
  have hqt : t ∉ q.asIdeal := fun h => hqU (Ideal.mul_mem_left _ _ h)
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hcomap : (m.map (Ideal.Quotient.mk q.asIdeal)).comap (Ideal.Quotient.mk q.asIdeal) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm).resolve_left fun e => by
      rw [e, Ideal.comap_top] at hcomap
      exact hm.ne_top hcomap.symm
  have hlaM : la.asIdeal ≤ m.comap (algebraMap (𝓞 K) A) := fun a ha => hPm (h2 a ha)
  have hmax : (m.comap (algebraMap (𝓞 K) A)) = la.asIdeal :=
    (la.isMaximal.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hlaM).symm
  have hinj' : Function.Injective (algebraMap (𝓞 K) (A ⧸ q.asIdeal)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    have h1 : a ∈ q.asIdeal.comap (algebraMap (𝓞 K) A) :=
      (Ideal.Quotient.eq_zero_iff_mem (I := q.asIdeal) (a := algebraMap (𝓞 K) A a)).mp ha
    have h2' : (q.asIdeal.comap (algebraMap (𝓞 K) A)).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance fun h => ha0 (by simpa [h] using h1)
    have h3 := h2'.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (Ideal.comap_mono hqm)
    exact hqπ (by
      have : π ∈ q.asIdeal.comap (algebraMap (𝓞 K) A) := by
        rw [h3]
        exact hπm
      exact this)
  obtain ⟨L, _, _, _, O, φ, hφ, hφi, hφm⟩ := exists_valuationSubring_of_height_le_one (K := K)
    hinj' (m.map (Ideal.Quotient.mk q.asIdeal)) hht π hπ (Ideal.mem_map_of_mem _ hπm)
  have nL : NumberField L := NumberField.of_module_finite K L
  refine ⟨L, _, nL, _, O, φ.comp (Ideal.Quotient.mk _), fun a => hφ a, fun s hs => ?_, fun h => hqt ?_⟩
  · have h1 : Ideal.Quotient.mk q.asIdeal s ∈ m.map (Ideal.Quotient.mk q.asIdeal) := Ideal.mem_map_of_mem _ (hPm hs)
    rw [← hφm, Ideal.mem_comap] at h1
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.2 ⟨(φ _).2, h1⟩
  · have : φ (Ideal.Quotient.mk _ t) = 0 := h
    exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff φ hφi).1 this)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Set `A : Subalgebra (𝓞 K) Ω` to `Algebra.adjoin (𝓞 K) (Gn : Set Ω)`. Establish `: Algebra.FiniteType (𝓞 K) A` using `(Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_adjoin_finset Gn)`. Establish `hA : ∀ a ∈ A, ν a ≤ 1` using `fun a ha => by`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact hG x hx`.

Consider the case `algebraMap r => exact h1 r`. Consider the case `add x y _ _ hx hy => exact (ν.map_add x y).trans (max_le hx hy)`. Consider the case `mul x y _ _ hx hy`. Rewrite using `[map_mul]`. Conclude with `mul_le_one' hx hy`.

Establish `hKA : ∀ a : 𝓞 K, algebraMap K Ω (a : K) ∈ A` using `fun a => A.algebraMap_mem a`. Establish `hfrac : ∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a` using `fun x => by`. Establish `hx : x ∈ IntermediateField.adjoin K (Gn : Set Ω)` using `hgen ▸ IntermediateField.mem_top`. Proceed by induction on `hx using IntermediateField.adjoin_induction with`. Consider the case `mem x hx => exact ⟨x, Algebra.subset_adjoin hx, 1, A.one_mem, one_ne_zero, mul_one x⟩`.

Consider the case `algebraMap a`. Take `⟨p, q, hq, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) a`. Establish `hq0 : algebraMap K Ω (algebraMap (𝓞 K) K q) ≠ 0` using `(map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.ne_zero hq))`. Use `⟨_, hKA p, _, hKA q, hq0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀]`.

Conclude with `div_mul_cancel₀ _ hq0`. Consider the case `add x y _ _ ihx ihy`. Take `⟨a, ha, b, hb, hb0, e⟩` from `ihx`. Take `⟨a', ha', b', hb', hb0', e'⟩` from `ihy`. Use `⟨a * b' + a' * b, A.add_mem (A.mul_mem ha hb') (A.mul_mem ha' hb), b * b', A.mul_mem hb hb', mul_ne_zero hb0 hb0', ?_⟩` and prove the remaining obligations.

Rewrite using `[← e, ← e']`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul x y _ _ ihx ihy`. Take `⟨a, ha, b, hb, hb0, e⟩` from `ihx`. Take `⟨a', ha', b', hb', hb0', e'⟩` from `ihy`.

Use `⟨a * a', A.mul_mem ha ha', b * b', A.mul_mem hb hb', mul_ne_zero hb0 hb0', ?_⟩` and prove the remaining obligations. Rewrite using `[← e, ← e']`. Expand and normalize the polynomial expressions, which then agree. Consider the case `inv x _ ih`. Take `⟨a, ha, b, hb, hb0, e⟩` from `ih`.

Distinguish the cases in `hx0 : x = 0`. Conclude with `⟨0, A.zero_mem, 1, A.one_mem, one_ne_zero, by simp [hx0]⟩`. Use `⟨b, hb, a, ha, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← e]`. Conclude with `mul_ne_zero hx0 hb0`.

Rewrite using `[← e]`. Clear the denominators using the available nonvanishing facts. Use `choose fa hfa fb hfb hb0 hxb using hfrac`. Set `t : A` to `(∏ x ∈ W ∪ N, (⟨fb x, hfb x⟩ : A)) * ∏ x ∈ N, (⟨fa x, hfa x⟩ : A)`. Establish `hfa0 : ∀ x ∈ N, (⟨fa x, hfa x⟩ : A) ≠ 0` using `fun x hx h => by`.

Establish `h0 : fa x = 0` using `congrArg Subtype.val h`. Rewrite `h0` using `[← hxb x]`. Conclude with `mul_ne_zero (hN x hx) (hb0 x) h0`. Establish `ht : t ≠ 0` using `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun x _ h => hb0 x (congrArg Subtype.val h)) (Finset.prod_ne_zero_iff.2 hfa0)`. Take `⟨L, _, nL, _, O, φ, hφ, hφm, hφt⟩` from `point_of_val la ν h2 A hA ht`.

Establish `hcoeL : ∀ a : 𝓞 K, ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) = algebraMap K L (a : K)` using `fun a => rfl`. Take `⟨π, hπla, hπ⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot`. Establish `hOnon : ∀ a ∈ la.asIdeal, algebraMap K L (a : K) ∈ O.nonunits` using `fun a ha => by`. Rewrite using `[← hφ a]`. Conclude with `hφm _ (h2 a ha)`.

Establish `hx0 : algebraMap (𝓞 K) (𝓞 L) π ≠ 0` using `fun h => by`. Establish `h3 : algebraMap K L (π : K) = 0` using `by rw [← hcoeL, h]; rfl`. Conclude with `hπ (RingOfIntegers.ext ((map_eq_zero _).1 h3))`. Take `⟨w, hw⟩` from `exists_prime_eq O (algebraMap (𝓞 K) (𝓞 L) π) hx0 (hOnon π hπla)`. Establish `memO : ∀ x : L, x ∈ O ↔ w.valuation L x ≤ 1` using `fun x => by`.

Rewrite using `[← hw]`. Conclude with `GlobalTheory.PlaceCompletion.mem_atPrime_iff w x`. Establish `nonU : ∀ x : L, x ∈ O.nonunits → w.valuation L x < 1` using `fun x hx => by`. Break down `(ValuationSubring.mem_nonunits_iff_or O).1 hx with h0 | h0` into its components or cases. Simplify using `[h0]`.

Rewrite `h0` using `[memO, map_inv₀, not_le]`. Establish `hne : x ≠ 0` using `fun h => by simp [h] at h0`. Conclude with `(one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hne))).1 h0`. Establish `hlies : w.asIdeal.LiesOver la.asIdeal` using `⟨by`. Establish `hle : la.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L))` using `fun a ha => by`.

Rewrite using `[Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]`. Conclude with `nonU _ (hOnon a ha)`. Conclude with `la.isMaximal.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle⟩`. Establish `: Finite (𝓞 L ⧸ w.asIdeal)` using `w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot`. Establish `: CharZero (HeightOneSpectrum.adicCompletionIntegers L w)` using `charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective (𝓞 L) (HeightOneSpectrum.adicCompletionIntegers L w))`.

Take `⟨e1, he1, h1e⟩` from `GlobalTheory.AdicCompl.exists_e (L := L) w`. Set `T : CDVR` to `{ V := HeightOneSpectrum.adicCompletionIntegers L w, cpl := GlobalTheory.AdicCompl.isAdicComplete w }`. Set `k : L →+* T.Fr` to `GlobalTheory.AdicCompl.kMap w`. Establish `hvk : ∀ x : L, vV T.V (k x) = (e1 : ℤ) * vLa w x` using `fun x => by show vV (HeightOneSpectrum.adicCompletionIntegers L w) (GlobalTheory.AdicCompl.kMap w x) = _`. Simplify using `only [vV, vLa]`.

Rewrite using `[h1e, WithZero.log_pow]`. Simplify using the standard rewrite rules. Establish `he2 : la.asIdeal.ramificationIdx' w.asIdeal ≠ 0` using `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal la.ne_bot`. Establish `ho : OverLa la T.V (k.comp (algebraMap K L)) (la.asIdeal.ramificationIdx' w.asIdeal * e1)`. Use `⟨Nat.mul_pos (Nat.pos_of_ne_zero he2) he1, fun a => ?_⟩` and prove the remaining obligations.

Use `show vV (HeightOneSpectrum.adicCompletionIntegers L w) (GlobalTheory.AdicCompl.kMap w (algebraMap K L a)) = _`. Simplify using `only [vV, vLa]`. Rewrite using `[h1e, ← HeightOneSpectrum.valuation_liesOver L la w a, ← pow_mul, WithZero.log_pow]`. Use `push_cast`. Simplify using the standard rewrite rules.

Establish `hfin : T.FinRes` using `GlobalTheory.AdicCompl.finite_res w`. Set `g : A →+* T.Fr` to `(k.comp O.subtype).comp φ`. Establish `hg : ∀ a : A, g a = k (φ a : O)` using `fun _ => rfl`. Establish `hfg : IsFractionRing A Ω` using `IsFractionRing.of_field A Ω fun z => ⟨⟨fa z, hfa z⟩, ⟨fb z, hfb z⟩, by show z = fa z / fb z`. Rewrite using `[← hxb z, mul_div_cancel_right₀ _ (hb0 z)]⟩`.

Set `P₀ : Ideal A` to `RingHom.ker g`. Establish `hP₀ : P₀.IsPrime` using `RingHom.ker_isPrime g`. Establish `hM : P₀.primeCompl ≤ nonZeroDivisors A` using `P₀.primeCompl_le_nonZeroDivisors`. Set `S₀ : Subalgebra A Ω` to `Localization.subalgebra.ofField Ω P₀.primeCompl hM`. Use `haveI : IsLocalization P₀.primeCompl S₀ := Localization.subalgebra.isLocalization_ofField Ω P₀.primeCompl hM`.

Set `ρ₀ : S₀ →+* T.Fr` to `IsLocalization.lift (M := P₀.primeCompl) (g := g) fun y => isUnit_iff_ne_zero.2 fun h => y.2 h`. Establish `hρ₀ : ∀ a : A, ρ₀ (algebraMap A S₀ a) = g a` using `fun a => IsLocalization.lift_eq _ a`. Establish `memS₀ : ∀ (x : Ω) (a b : A), g b ≠ 0 → x * b = a → x ∈ S₀` using `fun x a b hb e => by`. Establish `hb0' : (b : Ω) ≠ 0` using `fun h => hb (by`. Establish `: b = 0` using `Subtype.ext h`.

Rewrite using `[this, map_zero])`. Establish `hx : x = algebraMap A Ω a * (algebraMap A Ω b)⁻¹` using `by show x = (a : Ω) * (b : Ω)⁻¹`. Rewrite using `[← e, mul_inv_cancel_right₀ hb0']`. Conclude with `⟨a, b, fun h => hb h, hx⟩`. Establish `hAS : ∀ a : A, (a : Ω) ∈ S₀` using `fun a => memS₀ _ a 1 (by rw [map_one]; exact one_ne_zero) (by simp)`.

Establish `hKS : ∀ a : K, algebraMap K Ω a ∈ S₀` using `fun a => by`. Take `⟨p, q, hq, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) a`. Establish `hq0 : (algebraMap (𝓞 K) K q) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.ne_zero hq)`. Use `memS₀ _ (algebraMap (𝓞 K) A p) (algebraMap (𝓞 K) A q) ?_ ?_` and prove the remaining obligations. Rewrite using `[hg, hφ q]`.

Conclude with `(map_ne_zero k).2 ((map_ne_zero _).2 hq0)`. Express the relevant statement in the definitionally equal form `algebraMap K Ω (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q) * algebraMap K Ω (algebraMap (𝓞 K) K q) = algebraMap K Ω (algebraMap (𝓞 K) K p)`. Rewrite using `[← map_mul, div_mul_cancel₀ _ hq0]`. Set `S : Subalgebra K Ω` to `{ S₀.toSubsemiring with algebraMap_mem' := hKS }`. Set `ι : S →+* S₀` to `{ toFun := fun x => ⟨x.1, x.2⟩ map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`.

Set `ρ : S →+* T.Fr` to `ρ₀.comp ι`. Establish `hρA : ∀ (x : S) (a : A), (x : Ω) = a → ρ x = g a` using `fun x a e => by`. Establish `h3 : ι x = algebraMap A S₀ a` using `Subtype.ext e`. Use `show ρ₀ (ι x) = _`. Rewrite using `[h3, hρ₀]`.

Establish `hρM : ∀ (x : S) (a b : A), (x : Ω) * b = a → ρ x * g b = g a` using `fun x a b e => by`. Establish `h3 : ι x * algebraMap A S₀ b = algebraMap A S₀ a` using `Subtype.ext e`. Establish `h4` using `congrArg ρ₀ h3`. Rewrite `h4` using `[map_mul, hρ₀, hρ₀]`. Then use the resulting hypothesis. Establish `hgt : g t ≠ 0`.

Rewrite using `[hg]`. Conclude with `(map_ne_zero k).2 fun h => hφt (Subtype.ext h)`. Establish `hgt'` using `hgt`. Rewrite `hgt'` using `[map_mul, map_prod, map_prod]`. Establish `hWN : ∀ x ∈ W ∪ N, g ⟨fb x, hfb x⟩ ≠ 0` using `fun x hx => Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hgt') x hx`.

Establish `hgfa : ∀ x ∈ N, g ⟨fa x, hfa x⟩ ≠ 0` using `fun x hx => Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hgt') x hx`. Establish `hvL : ∀ y : L, y ∈ O → 0 ≤ vLa w y` using `fun y hy => by`. Distinguish the cases in `hy0 : y = 0`. Simplify using `[vLa, hy0]`. Establish `h3` using `(WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hy0) one_ne_zero).2 ((memO y).1 hy)`.

Rewrite `h3` using `[WithZero.log_one]`. Simplify using `only [vLa]`. Use linear arithmetic over natural numbers and integers. Establish `hvL' : ∀ y : L, y ∈ O.nonunits → y ≠ 0 → 0 < vLa w y` using `fun y hy hy0 => by`. Establish `h3` using `(WithZero.log_lt_log ((Valuation.ne_zero_iff _).2 hy0) one_ne_zero).2 (nonU y hy)`.

Rewrite `h3` using `[WithZero.log_one]`. Simplify using `only [vLa]`. Use linear arithmetic over natural numbers and integers. Establish `hGS : ∀ x ∈ Gn, x ∈ A` using `fun x hx => Algebra.subset_adjoin hx`. Use `⟨T, k.comp (algebraMap K L), _, ho, hfin, S, ρ, fun a => ?_, fun x hx => hAS ⟨x, hGS x hx⟩, fun x hx => memS₀ x ⟨fa x, hfa x⟩ ⟨fb x, hfb x⟩ (hWN x (Finset.mem_union_left _ hx)) (hxb x), fun x hx => memS₀ x ⟨fa x, hfa x⟩ ⟨fb x, hfb x⟩ (hWN x (Finset.mem_union_right _ hx)) (hxb x), …` and prove the remaining obligations.

Take `⟨p, q, hq, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) a`. Establish `hq0 : (algebraMap (𝓞 K) K q) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.ne_zero hq)`. Establish `h3` using `hρM (algebraMap K S (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q)) (algebraMap (𝓞 K) A p) (algebraMap (𝓞 K) A q) (by`. Express the relevant statement in the definitionally equal form `algebraMap K Ω (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q) * algebraMap K Ω (algebraMap (𝓞 K) K q) = algebraMap K Ω (algebraMap (𝓞 K) K p)`. Rewrite using `[← map_mul, div_mul_cancel₀ _ hq0])`.

Rewrite `h3` using `[hg, hg, hφ q, hφ p]`. Establish `hk0 : k (algebraMap K L (algebraMap (𝓞 K) K q)) ≠ 0` using `(map_ne_zero k).2 ((map_ne_zero _).2 hq0)`. Use `show _ = k (algebraMap K L (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q))`. Rewrite using `[map_div₀ (algebraMap K L), map_div₀ k]`. Conclude with `eq_div_of_mul_eq hk0 h3`.

Establish `h3` using `hρM x ⟨fa x, hfa x⟩ ⟨fb x, hfb x⟩ (hxb x)`. Rewrite `h3` using `[h0, zero_mul]`. Conclude with `h3.symm`. Rewrite using `[hρA x ⟨x, hGS x hx⟩ rfl, hg, hvk]`. Conclude with `mul_nonneg (Int.natCast_nonneg _) (hvL _ (φ _).2)`.

Establish `hρ` using `hρA x ⟨x, hGS x hx⟩ rfl`. Rewrite `h0`, the goal using `[hρ, hg]`. Rewrite using `[hvk]`. Establish `hy0 : ((φ ⟨x, hGS x hx⟩ : O) : L) ≠ 0` using `fun h => h0 (by rw [h, map_zero])`. Conclude with `mul_pos (by exact_mod_cast he1) (hvL' _ (hφm ⟨x, hGS x hx⟩ hν) hy0)`.
-/
theorem cdvr_point {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (la : HeightOneSpectrum (𝓞 K)) (ν : Valuation Ω Γ)
    (h1 : ∀ a : 𝓞 K, ν (algebraMap K Ω (a : K)) ≤ 1)
    (h2 : ∀ a ∈ la.asIdeal, ν (algebraMap K Ω (a : K)) < 1)
    (Gn W N : Finset Ω) (hG : ∀ g ∈ Gn, ν g ≤ 1)
    (hgen : IntermediateField.adjoin K (Gn : Set Ω) = ⊤) (hN : ∀ x ∈ N, x ≠ 0) :
    ∃ (T : CDVR) (io : K →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e) (_ : T.FinRes)
      (S : Subalgebra K Ω) (ρ : S →+* T.Fr),
      (∀ a : K, ρ (algebraMap K S a) = io a) ∧ (∀ x ∈ Gn, x ∈ S) ∧ (∀ x ∈ W, x ∈ S) ∧ (∀ x ∈ N, x ∈ S) ∧
      (∀ x : S, (x : Ω) ∈ N → ρ x ≠ 0) ∧ (∀ x : S, (x : Ω) ∈ Gn → 0 ≤ vV T.V (ρ x)) ∧
      (∀ x : S, (x : Ω) ∈ Gn → ν x < 1 → ρ x ≠ 0 → 0 < vV T.V (ρ x)) := by
  classical
  let A : Subalgebra (𝓞 K) Ω := Algebra.adjoin (𝓞 K) (Gn : Set Ω)
  have : Algebra.FiniteType (𝓞 K) A := (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_adjoin_finset Gn)
  have hA : ∀ a ∈ A, ν a ≤ 1 := fun a ha => by
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hG x hx
    | algebraMap r => exact h1 r
    | add x y _ _ hx hy => exact (ν.map_add x y).trans (max_le hx hy)
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_le_one' hx hy
  have hKA : ∀ a : 𝓞 K, algebraMap K Ω (a : K) ∈ A := fun a => A.algebraMap_mem a
  have hfrac : ∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a := fun x => by
    have hx : x ∈ IntermediateField.adjoin K (Gn : Set Ω) := hgen ▸ IntermediateField.mem_top
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact ⟨x, Algebra.subset_adjoin hx, 1, A.one_mem, one_ne_zero, mul_one x⟩
    | algebraMap a =>
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
      have hq0 : algebraMap K Ω (algebraMap (𝓞 K) K q) ≠ 0 :=
        (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.ne_zero hq))
      refine ⟨_, hKA p, _, hKA q, hq0, ?_⟩
      rw [map_div₀]
      exact div_mul_cancel₀ _ hq0
    | add x y _ _ ihx ihy =>
      obtain ⟨a, ha, b, hb, hb0, e⟩ := ihx
      obtain ⟨a', ha', b', hb', hb0', e'⟩ := ihy
      refine ⟨a * b' + a' * b, A.add_mem (A.mul_mem ha hb') (A.mul_mem ha' hb), b * b', A.mul_mem hb hb',
        mul_ne_zero hb0 hb0', ?_⟩
      rw [← e, ← e']
      ring
    | mul x y _ _ ihx ihy =>
      obtain ⟨a, ha, b, hb, hb0, e⟩ := ihx
      obtain ⟨a', ha', b', hb', hb0', e'⟩ := ihy
      refine ⟨a * a', A.mul_mem ha ha', b * b', A.mul_mem hb hb', mul_ne_zero hb0 hb0', ?_⟩
      rw [← e, ← e']
      ring
    | inv x _ ih =>
      obtain ⟨a, ha, b, hb, hb0, e⟩ := ih
      by_cases hx0 : x = 0
      · exact ⟨0, A.zero_mem, 1, A.one_mem, one_ne_zero, by simp [hx0]⟩
      · refine ⟨b, hb, a, ha, ?_, ?_⟩
        · rw [← e]
          exact mul_ne_zero hx0 hb0
        · rw [← e]
          field_simp
  choose fa hfa fb hfb hb0 hxb using hfrac
  let t : A := (∏ x ∈ W ∪ N, (⟨fb x, hfb x⟩ : A)) * ∏ x ∈ N, (⟨fa x, hfa x⟩ : A)
  have hfa0 : ∀ x ∈ N, (⟨fa x, hfa x⟩ : A) ≠ 0 := fun x hx h => by
    have h0 : fa x = 0 := congrArg Subtype.val h
    rw [← hxb x] at h0
    exact mul_ne_zero (hN x hx) (hb0 x) h0
  have ht : t ≠ 0 := mul_ne_zero
    (Finset.prod_ne_zero_iff.2 fun x _ h => hb0 x (congrArg Subtype.val h))
    (Finset.prod_ne_zero_iff.2 hfa0)
  obtain ⟨L, _, nL, _, O, φ, hφ, hφm, hφt⟩ := point_of_val la ν h2 A hA ht
  have hcoeL : ∀ a : 𝓞 K, ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) = algebraMap K L (a : K) := fun a => rfl
  obtain ⟨π, hπla, hπ⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
  have hOnon : ∀ a ∈ la.asIdeal, algebraMap K L (a : K) ∈ O.nonunits := fun a ha => by
    rw [← hφ a]
    exact hφm _ (h2 a ha)
  have hx0 : algebraMap (𝓞 K) (𝓞 L) π ≠ 0 := fun h => by
    have h3 : algebraMap K L (π : K) = 0 := by rw [← hcoeL, h]; rfl
    exact hπ (RingOfIntegers.ext ((map_eq_zero _).1 h3))
  obtain ⟨w, hw⟩ := exists_prime_eq O (algebraMap (𝓞 K) (𝓞 L) π) hx0 (hOnon π hπla)
  have memO : ∀ x : L, x ∈ O ↔ w.valuation L x ≤ 1 := fun x => by
    rw [← hw]
    exact GlobalTheory.PlaceCompletion.mem_atPrime_iff w x
  have nonU : ∀ x : L, x ∈ O.nonunits → w.valuation L x < 1 := fun x hx => by
    rcases (ValuationSubring.mem_nonunits_iff_or O).1 hx with h0 | h0
    · simp [h0]
    · rw [memO, map_inv₀, not_le] at h0
      have hne : x ≠ 0 := fun h => by simp [h] at h0
      exact (one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hne))).1 h0
  have hlies : w.asIdeal.LiesOver la.asIdeal := ⟨by
    have hle : la.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) := fun a ha => by
      rw [Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]
      exact nonU _ (hOnon a ha)
    exact la.isMaximal.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle⟩
  have : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  have : CharZero (HeightOneSpectrum.adicCompletionIntegers L w) :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective (𝓞 L) (HeightOneSpectrum.adicCompletionIntegers L w))
  obtain ⟨e1, he1, h1e⟩ := GlobalTheory.AdicCompl.exists_e (L := L) w
  let T : CDVR := { V := HeightOneSpectrum.adicCompletionIntegers L w, cpl := GlobalTheory.AdicCompl.isAdicComplete w }
  let k : L →+* T.Fr := GlobalTheory.AdicCompl.kMap w
  have hvk : ∀ x : L, vV T.V (k x) = (e1 : ℤ) * vLa w x := fun x => by
    show vV (HeightOneSpectrum.adicCompletionIntegers L w) (GlobalTheory.AdicCompl.kMap w x) = _
    simp only [vV, vLa]
    rw [h1e, WithZero.log_pow]
    simp
  have he2 : la.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal la.ne_bot
  have ho : OverLa la T.V (k.comp (algebraMap K L)) (la.asIdeal.ramificationIdx' w.asIdeal * e1) := by
    refine ⟨Nat.mul_pos (Nat.pos_of_ne_zero he2) he1, fun a => ?_⟩
    show vV (HeightOneSpectrum.adicCompletionIntegers L w) (GlobalTheory.AdicCompl.kMap w (algebraMap K L a)) = _
    simp only [vV, vLa]
    rw [h1e, ← HeightOneSpectrum.valuation_liesOver L la w a, ← pow_mul, WithZero.log_pow]
    push_cast
    simp
  have hfin : T.FinRes := GlobalTheory.AdicCompl.finite_res w
  let g : A →+* T.Fr := (k.comp O.subtype).comp φ
  have hg : ∀ a : A, g a = k (φ a : O) := fun _ => rfl
  have hfg : IsFractionRing A Ω := IsFractionRing.of_field A Ω fun z =>
    ⟨⟨fa z, hfa z⟩, ⟨fb z, hfb z⟩, by
      show z = fa z / fb z
      rw [← hxb z, mul_div_cancel_right₀ _ (hb0 z)]⟩
  let P₀ : Ideal A := RingHom.ker g
  have hP₀ : P₀.IsPrime := RingHom.ker_isPrime g
  have hM : P₀.primeCompl ≤ nonZeroDivisors A := P₀.primeCompl_le_nonZeroDivisors
  let S₀ : Subalgebra A Ω := Localization.subalgebra.ofField Ω P₀.primeCompl hM
  haveI : IsLocalization P₀.primeCompl S₀ := Localization.subalgebra.isLocalization_ofField Ω P₀.primeCompl hM
  let ρ₀ : S₀ →+* T.Fr := IsLocalization.lift (M := P₀.primeCompl) (g := g) fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 h
  have hρ₀ : ∀ a : A, ρ₀ (algebraMap A S₀ a) = g a := fun a => IsLocalization.lift_eq _ a
  have memS₀ : ∀ (x : Ω) (a b : A), g b ≠ 0 → x * b = a → x ∈ S₀ := fun x a b hb e => by
    have hb0' : (b : Ω) ≠ 0 := fun h => hb (by
      have : b = 0 := Subtype.ext h
      rw [this, map_zero])
    have hx : x = algebraMap A Ω a * (algebraMap A Ω b)⁻¹ := by
      show x = (a : Ω) * (b : Ω)⁻¹
      rw [← e, mul_inv_cancel_right₀ hb0']
    exact ⟨a, b, fun h => hb h, hx⟩
  have hAS : ∀ a : A, (a : Ω) ∈ S₀ := fun a => memS₀ _ a 1 (by rw [map_one]; exact one_ne_zero) (by simp)
  have hKS : ∀ a : K, algebraMap K Ω a ∈ S₀ := fun a => by
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    have hq0 : (algebraMap (𝓞 K) K q) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.ne_zero hq)
    refine memS₀ _ (algebraMap (𝓞 K) A p) (algebraMap (𝓞 K) A q) ?_ ?_
    · rw [hg, hφ q]
      exact (map_ne_zero k).2 ((map_ne_zero _).2 hq0)
    · change algebraMap K Ω (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q) * algebraMap K Ω (algebraMap (𝓞 K) K q) =
        algebraMap K Ω (algebraMap (𝓞 K) K p)
      rw [← map_mul, div_mul_cancel₀ _ hq0]
  let S : Subalgebra K Ω := { S₀.toSubsemiring with algebraMap_mem' := hKS }
  let ι : S →+* S₀ :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ρ : S →+* T.Fr := ρ₀.comp ι
  have hρA : ∀ (x : S) (a : A), (x : Ω) = a → ρ x = g a := fun x a e => by
    have h3 : ι x = algebraMap A S₀ a := Subtype.ext e
    show ρ₀ (ι x) = _
    rw [h3, hρ₀]
  have hρM : ∀ (x : S) (a b : A), (x : Ω) * b = a → ρ x * g b = g a := fun x a b e => by
    have h3 : ι x * algebraMap A S₀ b = algebraMap A S₀ a := Subtype.ext e
    have h4 := congrArg ρ₀ h3
    rwa [map_mul, hρ₀, hρ₀] at h4
  have hgt : g t ≠ 0 := by
    rw [hg]
    exact (map_ne_zero k).2 fun h => hφt (Subtype.ext h)
  have hgt' := hgt
  rw [map_mul, map_prod, map_prod] at hgt'
  have hWN : ∀ x ∈ W ∪ N, g ⟨fb x, hfb x⟩ ≠ 0 := fun x hx =>
    Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hgt') x hx
  have hgfa : ∀ x ∈ N, g ⟨fa x, hfa x⟩ ≠ 0 := fun x hx =>
    Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hgt') x hx
  have hvL : ∀ y : L, y ∈ O → 0 ≤ vLa w y := fun y hy => by
    by_cases hy0 : y = 0
    · simp [vLa, hy0]
    · have h3 := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hy0) one_ne_zero).2 ((memO y).1 hy)
      rw [WithZero.log_one] at h3
      simp only [vLa]
      omega
  have hvL' : ∀ y : L, y ∈ O.nonunits → y ≠ 0 → 0 < vLa w y := fun y hy hy0 => by
    have h3 := (WithZero.log_lt_log ((Valuation.ne_zero_iff _).2 hy0) one_ne_zero).2 (nonU y hy)
    rw [WithZero.log_one] at h3
    simp only [vLa]
    omega
  have hGS : ∀ x ∈ Gn, x ∈ A := fun x hx => Algebra.subset_adjoin hx
  refine ⟨T, k.comp (algebraMap K L), _, ho, hfin, S, ρ, fun a => ?_, fun x hx => hAS ⟨x, hGS x hx⟩,
    fun x hx => memS₀ x ⟨fa x, hfa x⟩ ⟨fb x, hfb x⟩ (hWN x (Finset.mem_union_left _ hx)) (hxb x),
    fun x hx => memS₀ x ⟨fa x, hfa x⟩ ⟨fb x, hfb x⟩ (hWN x (Finset.mem_union_right _ hx)) (hxb x),
    fun x hx h0 => hgfa x hx ?_, fun x hx => ?_, fun x hx hν h0 => ?_⟩
  · obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    have hq0 : (algebraMap (𝓞 K) K q) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.ne_zero hq)
    have h3 := hρM (algebraMap K S (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q)) (algebraMap (𝓞 K) A p)
      (algebraMap (𝓞 K) A q) (by
        change algebraMap K Ω (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q) * algebraMap K Ω (algebraMap (𝓞 K) K q) =
          algebraMap K Ω (algebraMap (𝓞 K) K p)
        rw [← map_mul, div_mul_cancel₀ _ hq0])
    rw [hg, hg, hφ q, hφ p] at h3
    have hk0 : k (algebraMap K L (algebraMap (𝓞 K) K q)) ≠ 0 := (map_ne_zero k).2 ((map_ne_zero _).2 hq0)
    show _ = k (algebraMap K L (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q))
    rw [map_div₀ (algebraMap K L), map_div₀ k]
    exact eq_div_of_mul_eq hk0 h3
  · have h3 := hρM x ⟨fa x, hfa x⟩ ⟨fb x, hfb x⟩ (hxb x)
    rw [h0, zero_mul] at h3
    exact h3.symm
  · rw [hρA x ⟨x, hGS x hx⟩ rfl, hg, hvk]
    exact mul_nonneg (Int.natCast_nonneg _) (hvL _ (φ _).2)
  · have hρ := hρA x ⟨x, hGS x hx⟩ rfl
    rw [hρ, hg] at h0 ⊢
    rw [hvk]
    have hy0 : ((φ ⟨x, hGS x hx⟩ : O) : L) ≠ 0 := fun h => h0 (by rw [h, map_zero])
    exact mul_pos (by exact_mod_cast he1) (hvL' _ (hφm ⟨x, hGS x hx⟩ hν) hy0)

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨hGF, hGT⟩` from `GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c`. Take `⟨n, w, hw⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hFG`. Establish `hspan : Submodule.span c.F (Set.range w) = ⊤`.

Rewrite using `[← hsp, ← hw, Submodule.span_span_of_tower]`. Set `a : Fin n → Om Z` to `fun i => genVal Z (w i : Rul Xo c)`. Establish `hex : ∃ i, a i ≠ 0`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`.

Conclude with `hB.1 (LinearMap.ext_on_range hspan fun i => hall i)`. Take `⟨i₁, hi₁⟩` from `hex`. Establish `: Nonempty (Fin n)` using `⟨i₁⟩`. Take `⟨i₀, hi₀⟩` from `Finite.exists_max fun i => ν (a i)`. Establish `ha0 : a i₀ ≠ 0` using `fun h => by`.

Establish `h3` using `hi₀ i₁`. Simplify using `only [h, map_zero] at h3`. Conclude with `hi₁ ((Valuation.zero_iff ν).1 (le_antisymm h3 zero_le'))`. Establish `hwlat : ∀ i, w i ∈ latOn U Z G` using `fun i => hw ▸ Submodule.subset_span ⟨i, rfl⟩`. Establish `hlt : ν (a i₀) ^ τ < ν (genVal Z (f : Rul Xo c))` using `hcon (w i₀) (hwlat i₀)`.

Use `set b := genVal Z (f : Rul Xo c) with hbdef`. Establish `hb0 : b ≠ 0` using `fun h => by`. Rewrite `hlt` using `[h, map_zero]`. Conclude with `not_lt_zero' hlt`. Establish `hνa : 0 < ν (a i₀)` using `zero_lt_iff.2 ((Valuation.ne_zero_iff ν).2 ha0)`.

Establish `hνb : 0 < ν b` using `zero_lt_iff.2 ((Valuation.ne_zero_iff ν).2 hb0)`. Set `y : Fin n → Om Z` to `fun i => a i / a i₀`. Set `q : Om Z` to `a i₀ ^ τ / b`. Establish `hy : ∀ i, ν (y i) ≤ 1` using `fun i => by`. Simplify using `only [y, map_div₀]`.

Conclude with `div_le_one_of_le₀ (hi₀ i) hνa.le`. Establish `hq : ν q < 1`. Simplify using `only [q, map_div₀, map_pow]`. Conclude with `(div_lt_one₀ hνb).2 hlt`. Set `Gn : Finset (Om Z)` to `Finset.univ.image y ∪ {q}`.

Establish `hGn : ∀ g ∈ Gn, ν g ≤ 1` using `fun g hg => by`. Break down `Finset.mem_union.1 hg with h | h` into its components or cases. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 h`. Conclude with `hy i`. Rewrite using `[Finset.mem_singleton.1 h]`.

Conclude with `hq.le`. Establish `hgen : IntermediateField.adjoin c.F (Gn : Set (Om Z)) = ⊤`. Rewrite using `[eq_top_iff, ← adjoin_ratios (genPoint Z (cuspOn U Z G)) hB.2 w hspan i₀ ha0]`. Use `IntermediateField.adjoin.mono _ _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem y (Finset.mem_univ i)))`. Take `⟨p, χ, u₀, hu⟩` from `hGT hGF Z`. Set `Wf : Finset (Om Z)` to `Finset.univ.image fun i : Fin p.n => χ (Ideal.Quotient.mk p.I (MvPolynomial.X i))`. Set `N : Finset (Om Z)` to `{a i₀, b}`. Establish `hN : ∀ x ∈ N, x ≠ 0` using `fun x hx => by`.

Break down `Finset.mem_insert.1 hx with h | h` into its components or cases. Conclude with `h ▸ ha0`. Rewrite using `[Finset.mem_singleton.1 h]`. Conclude with `hb0`. Take `⟨T, io, e, ho, hfin, S, ρ, hρK, hSG, hSW, hSN, hρN, hρG, hρL⟩` from `cdvr_point la ν h1 h2 Gn Wf N hGn hgen hN`.

Establish `hχS : ∀ x : p.R, χ x ∈ S` using `fun x => by`. Take `⟨P, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `: χ (Ideal.Quotient.mk p.I (MvPolynomial.C a)) = algebraMap c.F (Om Z) a` using `χ.commutes a`.

Rewrite using `[this]`. Conclude with `S.algebraMap_mem a`. Consider the case `add P Q hP hQ`. Rewrite using `[map_add, map_add]`. Conclude with `S.add_mem hP hQ`.

Consider the case `mul_X P i hP`. Rewrite using `[map_mul, map_mul]`. Conclude with `S.mul_mem hP (hSW _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))`. Use `letI := io.toAlgebra`. Set `ψ : p.R →ₐ[c.F] T.Fr` to `{ (ρ.comp (χ.codRestrict S hχS).toRingHom) with commutes' := fun x => by`.

Establish `h3 : (χ.codRestrict S hχS) (algebraMap c.F p.R x) = algebraMap c.F S x` using `Subtype.ext (χ.commutes x)`. Use `show ρ ((χ.codRestrict S hχS) (algebraMap c.F p.R x)) = io x`. Rewrite using `[h3, hρK] }`. Establish `hψ : ∀ x, ψ x = ρ ⟨χ x, hχS x⟩` using `fun _ => rfl`. Take `⟨z, hz⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c p.R T.Fr ψ u₀`.

Take `⟨T', io', r', y', hr, ho', hf', φ, z', t', h1', h2', hz', hb'⟩` from `GlobalTheory.IntegralFrameCheck.intAll_ramified (intAll_all Xo c) la T io e ho hfin z`. Use `letI := io'.toAlgebra`. Establish `hz2 : FrMap (φ.comp ψ) u₀ z'` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ψ φ hz hz'`. Establish `hform : ∀ {G' : WTZ E} {g : Rul Xo c}, g ∈ secZ Xo c (exZ Dw G') → evI y' g = ((∏ i, t' i ^ exZ Dw G' i : T'.Frˣ) : T'.Fr) * φ (ψ (g p u₀))` using `fun hg => evR_bor hg p (φ.comp ψ) u₀ z' y'.1 hz2 t' hb'`. Establish `hgv : ∀ {e' : Ix Dw → ℤ} {g : Rul Xo c}, g ∈ secZ Xo c e' → genVal Z g = χ (g p u₀)` using `fun hg => (genVal_apply hGF Z _).trans (evR_test hg.1 p χ u₀ (genFr hGF Z) hu)`.

Establish `hmemG : ∀ i, (w i : Rul Xo c) ∈ secZ Xo c (exZ Dw G)` using `fun i => cuspW_le_secZ G (cuspOn_le U Z G (w i).2)`. Establish `hmemF : (f : Rul Xo c) ∈ secZ Xo c (exZ Dw (τ • G))` using `cuspW_le_secZ _ (cuspOn_le U Z _ f.2)`. Establish `ea : ∀ i, a i = χ ((w i : Rul Xo c) p u₀)` using `fun i => hgv (hmemG i)`. Establish `eb : b = χ ((f : Rul Xo c) p u₀)` using `hgv hmemF`. Set `Cu : T'.Frˣ` to `∏ i, t' i ^ exZ Dw G i`.

Set `A₀ : S` to `⟨χ ((w i₀ : Rul Xo c) p u₀), hχS _⟩`. Set `Bf : S` to `⟨χ ((f : Rul Xo c) p u₀), hχS _⟩`. Establish `hA₀ : ρ A₀ ≠ 0` using `hρN A₀ (by show χ _ ∈ N`. Rewrite using `[← ea]`. Conclude with `Finset.mem_insert_self _ _)`.

Establish `hBf : ρ Bf ≠ 0` using `hρN Bf (by show χ _ ∈ N`. Rewrite using `[← eb]`. Conclude with `Finset.mem_insert_of_mem (Finset.mem_singleton_self _))`. Establish `hyG : ∀ i, y i ∈ Gn` using `fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem y (Finset.mem_univ i))`. Establish `hqG : q ∈ Gn` using `Finset.mem_union_right _ (Finset.mem_singleton_self _)`.

Set `Q : S` to `⟨q, hSG q hqG⟩`. Establish `hYi : ∀ i, (⟨y i, hSG _ (hyG i)⟩ : S) * A₀ = ⟨χ ((w i : Rul Xo c) p u₀), hχS _⟩` using `fun i => Subtype.ext (by show y i * χ _ = χ _`. Rewrite using `[← ea, ← ea]`. Conclude with `div_mul_cancel₀ _ ha0)`. Establish `hQ : Q * Bf = A₀ ^ τ` using `Subtype.ext (by show q * χ _ = (χ _) ^ τ`.

Rewrite using `[← ea, ← eb]`. Conclude with `div_mul_cancel₀ _ hb0)`. Establish `hb0' : φ (ρ A₀) ≠ 0` using `(map_ne_zero φ).2 hA₀`. Establish `hbf' : φ (ρ Bf) ≠ 0` using `(map_ne_zero φ).2 hBf`. Establish `hCu : (Cu : T'.Fr) ≠ 0` using `Cu.ne_zero`.

Set `v : Rul Xo c → EReal` to `fun g => nval T'.V (r' * e) (evI y' g)`. Establish `hvmem : v ∈ (recVals Xo c).1 la` using `⟨PtV.mk la ho' y' hf' () trivial, rfl⟩`. Establish `hval : IsVal la v` using `(recVals Xo c).2 la v hvmem`. Establish `hgens : ∀ i, nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤ v (w i : Rul Xo c)` using `fun i => by show _ ≤ nval T'.V (r' * e) (evI y' (w i : Rul Xo c))`. Rewrite using `[hform (hmemG i)]`.

Establish `h3 : (Cu : T'.Fr) * φ (ψ ((w i : Rul Xo c) p u₀)) = φ (ρ ⟨y i, hSG _ (hyG i)⟩) * ((Cu : T'.Fr) * φ (ρ A₀))`. Rewrite using `[hψ, ← hYi i, map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `show nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤ nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ψ ((w i : Rul Xo c) p u₀)))`. Rewrite using `[h3]`.

Conclude with `nval_le_of_mul _ (mul_ne_zero hCu hb0') (by`. Rewrite using `[h1']`. Conclude with `mul_nonneg (Int.natCast_nonneg _) (hρG _ (hyG i)))`. Establish `hdep : nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤ depthOn U Z G v` using `le_iInf₂ fun l hl => le_of_mem_span hval w hgens (hw ▸ hl)`. Establish `hτ0 : (0 : EReal) ≤ (τ : EReal)` using `by exact_mod_cast Nat.zero_le τ`.

Establish `h4 : (τ : EReal) * nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤ v (f : Rul Xo c)` using `(mul_le_mul_of_nonneg_left hdep hτ0).trans (hf v hvmem)`. Establish `hvf : v (f : Rul Xo c) = nval T'.V (r' * e) ((Cu : T'.Fr) ^ τ * φ (ρ Bf))` using `by show nval T'.V (r' * e) (evI y' (f : Rul Xo c)) = _`. Rewrite using `[hform hmemF, prod_exZ_nsmul, Units.val_pow_eq_pow_val]`. Both sides reduce to the same expression. Establish `hX : (Cu : T'.Fr) * φ (ρ A₀) ≠ 0` using `mul_ne_zero hCu hb0'`.

Establish `hY : (Cu : T'.Fr) ^ τ * φ (ρ Bf) ≠ 0` using `mul_ne_zero (pow_ne_zero _ hCu) hbf'`. Establish `hkey : ((Cu : T'.Fr) * φ (ρ A₀)) ^ τ = φ (ρ Q) * ((Cu : T'.Fr) ^ τ * φ (ρ Bf))`. Rewrite using `[mul_pow, ← map_pow, ← map_pow, ← hQ, map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hD0 : φ (ρ Q) ≠ 0` using `fun h => pow_ne_zero τ hX (by rw [hkey, h, zero_mul])`.

Establish `hρQ : ρ Q ≠ 0` using `fun h => hD0 (by rw [h, map_zero])`. Establish `hD : 0 < vV T'.V (φ (ρ Q))`. Rewrite using `[h1']`. Conclude with `mul_pos (by exact_mod_cast hr) (hρL Q hqG hq hρQ)`. Establish `hvv : (τ : ℤ) * vV T'.V ((Cu : T'.Fr) * φ (ρ A₀)) = vV T'.V (φ (ρ Q)) + vV T'.V ((Cu : T'.Fr) ^ τ * φ (ρ Bf))`.

Rewrite using `[← vV_pow hX, hkey, vV_mul hD0 hY]`. Rewrite `h4` using `[hvf, nval_of_ne hX, nval_of_ne hY, show (τ : EReal) = ((τ : ℝ) : EReal) from by simp, ← EReal.coe_mul, EReal.coe_le_coe_iff, ← mul_div_assoc]`. Establish `hE : (0 : ℝ) < ((r' * e : ℕ) : ℝ)` using `by exact_mod_cast ho'.1`. Establish `h5` using `(div_le_div_iff_of_pos_right hE).1 h4`. Establish `h6 : (τ : ℤ) * vV T'.V ((Cu : T'.Fr) * φ (ρ A₀)) ≤ vV T'.V ((Cu : T'.Fr) ^ τ * φ (ρ Bf))`.

Conclude with `h5` after adjusting the coercions. Use linear arithmetic over natural numbers and integers.
-/
theorem fin_small_gen {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (Z : Comp Xo c) (G : WTZ E)
    (hFG : (latOn U Z G).FG) (hsp : Submodule.span c.F (latOn U Z G : Set (cuspOn U Z G)) = ⊤)
    (hB : GlobalTheory.DegVal.BirOn U Z G) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (la : HeightOneSpectrum (𝓞 c.F)) (ν : Valuation (Om Z) Γ)
    (h1 : ∀ a : 𝓞 c.F, ν (algebraMap c.F (Om Z) (a : c.F)) ≤ 1)
    (h2 : ∀ a ∈ la.asIdeal, ν (algebraMap c.F (Om Z) (a : c.F)) < 1) (τ : ℕ) (f : cuspOn U Z (τ • G))
    (hf : ∀ v ∈ (recVals Xo c).1 la, (τ : EReal) * depthOn U Z G v ≤ v (f : Rul Xo c)) :
    ∃ l ∈ latOn U Z G, ν (genVal Z (f : Rul Xo c)) ≤ ν (genVal Z (l : Rul Xo c)) ^ τ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hGF, hGT⟩ := GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c
  obtain ⟨n, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hFG
  have hspan : Submodule.span c.F (Set.range w) = ⊤ := by
    rw [← hsp, ← hw, Submodule.span_span_of_tower]
  let a : Fin n → Om Z := fun i => genVal Z (w i : Rul Xo c)
  have hex : ∃ i, a i ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hB.1 (LinearMap.ext_on_range hspan fun i => hall i)
  obtain ⟨i₁, hi₁⟩ := hex
  have : Nonempty (Fin n) := ⟨i₁⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => ν (a i)
  have ha0 : a i₀ ≠ 0 := fun h => by
    have h3 := hi₀ i₁
    simp only [h, map_zero] at h3
    exact hi₁ ((Valuation.zero_iff ν).1 (le_antisymm h3 zero_le'))
  have hwlat : ∀ i, w i ∈ latOn U Z G := fun i => hw ▸ Submodule.subset_span ⟨i, rfl⟩
  have hlt : ν (a i₀) ^ τ < ν (genVal Z (f : Rul Xo c)) := hcon (w i₀) (hwlat i₀)
  set b := genVal Z (f : Rul Xo c) with hbdef
  have hb0 : b ≠ 0 := fun h => by
    rw [h, map_zero] at hlt
    exact not_lt_zero' hlt
  have hνa : 0 < ν (a i₀) := zero_lt_iff.2 ((Valuation.ne_zero_iff ν).2 ha0)
  have hνb : 0 < ν b := zero_lt_iff.2 ((Valuation.ne_zero_iff ν).2 hb0)
  let y : Fin n → Om Z := fun i => a i / a i₀
  let q : Om Z := a i₀ ^ τ / b
  have hy : ∀ i, ν (y i) ≤ 1 := fun i => by
    simp only [y, map_div₀]
    exact div_le_one_of_le₀ (hi₀ i) hνa.le
  have hq : ν q < 1 := by
    simp only [q, map_div₀, map_pow]
    exact (div_lt_one₀ hνb).2 hlt
  classical
  let Gn : Finset (Om Z) := Finset.univ.image y ∪ {q}
  have hGn : ∀ g ∈ Gn, ν g ≤ 1 := fun g hg => by
    rcases Finset.mem_union.1 hg with h | h
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact hy i
    · rw [Finset.mem_singleton.1 h]
      exact hq.le
  have hgen : IntermediateField.adjoin c.F (Gn : Set (Om Z)) = ⊤ := by
    rw [eq_top_iff, ← adjoin_ratios (genPoint Z (cuspOn U Z G)) hB.2 w hspan i₀ ha0]
    refine IntermediateField.adjoin.mono _ _ _ ?_
    rintro _ ⟨i, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem y (Finset.mem_univ i)))
  obtain ⟨p, χ, u₀, hu⟩ := hGT hGF Z
  let Wf : Finset (Om Z) := Finset.univ.image fun i : Fin p.n => χ (Ideal.Quotient.mk p.I (MvPolynomial.X i))
  let N : Finset (Om Z) := {a i₀, b}
  have hN : ∀ x ∈ N, x ≠ 0 := fun x hx => by
    rcases Finset.mem_insert.1 hx with h | h
    · exact h ▸ ha0
    · rw [Finset.mem_singleton.1 h]
      exact hb0
  obtain ⟨T, io, e, ho, hfin, S, ρ, hρK, hSG, hSW, hSN, hρN, hρG, hρL⟩ :=
    cdvr_point la ν h1 h2 Gn Wf N hGn hgen hN
  have hχS : ∀ x : p.R, χ x ∈ S := fun x => by
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction P using MvPolynomial.induction_on with
    | C a =>
      have : χ (Ideal.Quotient.mk p.I (MvPolynomial.C a)) = algebraMap c.F (Om Z) a := χ.commutes a
      rw [this]
      exact S.algebraMap_mem a
    | add P Q hP hQ =>
      rw [map_add, map_add]
      exact S.add_mem hP hQ
    | mul_X P i hP =>
      rw [map_mul, map_mul]
      exact S.mul_mem hP (hSW _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  letI := io.toAlgebra
  let ψ : p.R →ₐ[c.F] T.Fr :=
    { (ρ.comp (χ.codRestrict S hχS).toRingHom) with
      commutes' := fun x => by
        have h3 : (χ.codRestrict S hχS) (algebraMap c.F p.R x) = algebraMap c.F S x := Subtype.ext (χ.commutes x)
        show ρ ((χ.codRestrict S hχS) (algebraMap c.F p.R x)) = io x
        rw [h3, hρK] }
  have hψ : ∀ x, ψ x = ρ ⟨χ x, hχS x⟩ := fun _ => rfl
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c p.R T.Fr ψ u₀
  obtain ⟨T', io', r', y', hr, ho', hf', φ, z', t', h1', h2', hz', hb'⟩ :=
    GlobalTheory.IntegralFrameCheck.intAll_ramified (intAll_all Xo c) la T io e ho hfin z
  letI := io'.toAlgebra
  have hz2 : FrMap (φ.comp ψ) u₀ z' := ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ψ φ hz hz'
  have hform : ∀ {G' : WTZ E} {g : Rul Xo c}, g ∈ secZ Xo c (exZ Dw G') →
      evI y' g = ((∏ i, t' i ^ exZ Dw G' i : T'.Frˣ) : T'.Fr) * φ (ψ (g p u₀)) := fun hg =>
    evR_bor hg p (φ.comp ψ) u₀ z' y'.1 hz2 t' hb'
  have hgv : ∀ {e' : Ix Dw → ℤ} {g : Rul Xo c}, g ∈ secZ Xo c e' → genVal Z g = χ (g p u₀) := fun hg =>
    (genVal_apply hGF Z _).trans (evR_test hg.1 p χ u₀ (genFr hGF Z) hu)
  have hmemG : ∀ i, (w i : Rul Xo c) ∈ secZ Xo c (exZ Dw G) := fun i => cuspW_le_secZ G (cuspOn_le U Z G (w i).2)
  have hmemF : (f : Rul Xo c) ∈ secZ Xo c (exZ Dw (τ • G)) := cuspW_le_secZ _ (cuspOn_le U Z _ f.2)
  have ea : ∀ i, a i = χ ((w i : Rul Xo c) p u₀) := fun i => hgv (hmemG i)
  have eb : b = χ ((f : Rul Xo c) p u₀) := hgv hmemF
  let Cu : T'.Frˣ := ∏ i, t' i ^ exZ Dw G i
  let A₀ : S := ⟨χ ((w i₀ : Rul Xo c) p u₀), hχS _⟩
  let Bf : S := ⟨χ ((f : Rul Xo c) p u₀), hχS _⟩
  have hA₀ : ρ A₀ ≠ 0 := hρN A₀ (by
    show χ _ ∈ N
    rw [← ea]
    exact Finset.mem_insert_self _ _)
  have hBf : ρ Bf ≠ 0 := hρN Bf (by
    show χ _ ∈ N
    rw [← eb]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hyG : ∀ i, y i ∈ Gn := fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem y (Finset.mem_univ i))
  have hqG : q ∈ Gn := Finset.mem_union_right _ (Finset.mem_singleton_self _)
  let Q : S := ⟨q, hSG q hqG⟩
  have hYi : ∀ i, (⟨y i, hSG _ (hyG i)⟩ : S) * A₀ = ⟨χ ((w i : Rul Xo c) p u₀), hχS _⟩ := fun i => Subtype.ext (by
    show y i * χ _ = χ _
    rw [← ea, ← ea]
    exact div_mul_cancel₀ _ ha0)
  have hQ : Q * Bf = A₀ ^ τ := Subtype.ext (by
    show q * χ _ = (χ _) ^ τ
    rw [← ea, ← eb]
    exact div_mul_cancel₀ _ hb0)
  have hb0' : φ (ρ A₀) ≠ 0 := (map_ne_zero φ).2 hA₀
  have hbf' : φ (ρ Bf) ≠ 0 := (map_ne_zero φ).2 hBf
  have hCu : (Cu : T'.Fr) ≠ 0 := Cu.ne_zero
  let v : Rul Xo c → EReal := fun g => nval T'.V (r' * e) (evI y' g)
  have hvmem : v ∈ (recVals Xo c).1 la := ⟨PtV.mk la ho' y' hf' () trivial, rfl⟩
  have hval : IsVal la v := (recVals Xo c).2 la v hvmem
  have hgens : ∀ i, nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤ v (w i : Rul Xo c) := fun i => by
    show _ ≤ nval T'.V (r' * e) (evI y' (w i : Rul Xo c))
    rw [hform (hmemG i)]
    have h3 : (Cu : T'.Fr) * φ (ψ ((w i : Rul Xo c) p u₀)) =
        φ (ρ ⟨y i, hSG _ (hyG i)⟩) * ((Cu : T'.Fr) * φ (ρ A₀)) := by
      rw [hψ, ← hYi i, map_mul, map_mul]
      ring
    show nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤
      nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ψ ((w i : Rul Xo c) p u₀)))
    rw [h3]
    exact nval_le_of_mul _ (mul_ne_zero hCu hb0') (by
      rw [h1']
      exact mul_nonneg (Int.natCast_nonneg _) (hρG _ (hyG i)))
  have hdep : nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤ depthOn U Z G v :=
    le_iInf₂ fun l hl => le_of_mem_span hval w hgens (hw ▸ hl)
  have hτ0 : (0 : EReal) ≤ (τ : EReal) := by exact_mod_cast Nat.zero_le τ
  have h4 : (τ : EReal) * nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤ v (f : Rul Xo c) :=
    (mul_le_mul_of_nonneg_left hdep hτ0).trans (hf v hvmem)
  have hvf : v (f : Rul Xo c) = nval T'.V (r' * e) ((Cu : T'.Fr) ^ τ * φ (ρ Bf)) := by
    show nval T'.V (r' * e) (evI y' (f : Rul Xo c)) = _
    rw [hform hmemF, prod_exZ_nsmul, Units.val_pow_eq_pow_val]
    rfl
  have hX : (Cu : T'.Fr) * φ (ρ A₀) ≠ 0 := mul_ne_zero hCu hb0'
  have hY : (Cu : T'.Fr) ^ τ * φ (ρ Bf) ≠ 0 := mul_ne_zero (pow_ne_zero _ hCu) hbf'
  have hkey : ((Cu : T'.Fr) * φ (ρ A₀)) ^ τ = φ (ρ Q) * ((Cu : T'.Fr) ^ τ * φ (ρ Bf)) := by
    rw [mul_pow, ← map_pow, ← map_pow, ← hQ, map_mul, map_mul]
    ring
  have hD0 : φ (ρ Q) ≠ 0 := fun h => pow_ne_zero τ hX (by rw [hkey, h, zero_mul])
  have hρQ : ρ Q ≠ 0 := fun h => hD0 (by rw [h, map_zero])
  have hD : 0 < vV T'.V (φ (ρ Q)) := by
    rw [h1']
    exact mul_pos (by exact_mod_cast hr) (hρL Q hqG hq hρQ)
  have hvv : (τ : ℤ) * vV T'.V ((Cu : T'.Fr) * φ (ρ A₀)) =
      vV T'.V (φ (ρ Q)) + vV T'.V ((Cu : T'.Fr) ^ τ * φ (ρ Bf)) := by
    rw [← vV_pow hX, hkey, vV_mul hD0 hY]
  rw [hvf, nval_of_ne hX, nval_of_ne hY, show (τ : EReal) = ((τ : ℝ) : EReal) from by simp, ← EReal.coe_mul,
    EReal.coe_le_coe_iff, ← mul_div_assoc] at h4
  have hE : (0 : ℝ) < ((r' * e : ℕ) : ℝ) := by exact_mod_cast ho'.1
  have h5 := (div_le_div_iff_of_pos_right hE).1 h4
  have h6 : (τ : ℤ) * vV T'.V ((Cu : T'.Fr) * φ (ρ A₀)) ≤ vV T'.V ((Cu : T'.Fr) ^ τ * φ (ρ Bf)) := by
    exact_mod_cast h5
  omega

end Main

end ChowFormHeightComparison₂.SmallGenerators
