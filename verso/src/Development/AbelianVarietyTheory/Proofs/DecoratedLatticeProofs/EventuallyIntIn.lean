import Mathlib
import ReciprocityTheory.Chebotarev.CyclotomicIrreducibleOfForallIsUnramifiedAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.InfiniteQAtOfIs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompIncAAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointComponentMemSpanOfLatticeGenerators
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatEqMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsComplIsUnif
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAtTypeAndOrd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDegreeOneAvoiding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel Filter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw.GeoInhab
open GlobalTheory.FinPl (SplitPt latV idAt intAt Lat Pl)
open Formalism.L2.NTheta (IsIdemAt)
open Formalism.L2.Col (IntAt qOf)
open GlobalTheory.SymBridge (IsOrd zPos xPos IsCompl)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsUnif)

/- English proof (translation)
Take `⟨N, hN⟩` from `ReciprocityTheory.Cheb.exists_forall_isUnramifiedAt D.host.E`. Take `⟨a, b, hb, hab⟩` from `IsFractionRing.div_surjective (A := 𝓞 D.host.E) D.host.xi0`. Establish `hb0 : (b : D.host.E) ≠ 0` using `RingOfIntegers.coe_ne_zero_iff.2 (nonZeroDivisors.ne_zero hb)`. Set `cO : 𝓞 D.host.E →+* 𝓞 D.host.E` to `RingOfIntegers.mapRingHom (starRingEnd D.host.E)`. Establish `hc : ∀ x, ((cO x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E)` using `fun _ => rfl`.

Establish `ha : (a : D.host.E) = D.host.xi0 * b` using `by rw [← hab]; exact (div_mul_cancel₀ _ hb0).symm`. Set `θ` to `a * cO b`. Establish `hθ : cO θ = -θ`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `star ((a : D.host.E) * star (b : D.host.E)) = -((a : D.host.E) * star (b : D.host.E))`.

Rewrite using `[ha, star_mul', star_mul', star_star, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D]`. Expand and normalize the polynomial expressions, which then agree. Establish `hθ0 : 2 * θ ≠ 0`. Use `mul_ne_zero two_ne_zero (RingOfIntegers.coe_ne_zero_iff.1 ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(a : D.host.E) * star (b : D.host.E) ≠ 0`.

Rewrite using `[ha]`. Conclude with `mul_ne_zero (mul_ne_zero (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D) hb0) (star_ne_zero.2 hb0)`. Set `n₁` to `Ideal.absNorm (Ideal.span {2 * θ})`. Set `n₂` to `∏ v ∈ hS.toFinset, Ideal.absNorm v.asIdeal`. Establish `h1 : n₁ ≠ 0` using `by simpa [n₁, Ideal.absNorm_eq_zero_iff] using hθ0`.

Establish `h2 : n₂ ≠ 0` using `Finset.prod_ne_zero_iff.2 fun v _ => by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot`. Take `⟨P, hP, hm, hs⟩` from `GlobalTheory.LargeSplitPrime.exists_degree_one_avoiding D.host.E ((n₁ * n₂ * N.factorial : ℕ) : ℤ) (by exact_mod_cast mul_ne_zero (mul_ne_zero h1 h2) N.factorial_ne_zero)`. Establish `key : ∀ n : ℕ, n ∣ n₁ * n₂ * N.factorial → (n : 𝓞 D.host.E) ∉ P`. Introduce and unpack `n ⟨t, ht⟩ hn`. Apply `hm` to reduce the goal to its premises.

Rewrite using `[ht]`. Use `push_cast`. Conclude with `Ideal.mul_mem_right _ _ hn`. Establish `hne : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.E)`. Set `PP : Formalism.L2.DIV.Pl D.host.E` to `⟨P, hP.isPrime, hne⟩`.

Use `letI := Ideal.Quotient.field P`. Use `haveI : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne`. Establish `hp : (qOf PP).Prime`. Set `p` to `ringChar (𝓞 D.host.E ⧸ P)`. Use `haveI : Fact p.Prime := ⟨CharP.char_is_prime (𝓞 D.host.E ⧸ P) p⟩`.

Establish `hbij : Function.Bijective (ZMod.castHom (dvd_refl p) (𝓞 D.host.E ⧸ P))`. Use `⟨RingHom.injective _, fun y => ?_⟩` and prove the remaining obligations. Take `⟨n, rfl⟩` from `hs y`. Conclude with `⟨n, by simp⟩`. Establish `: qOf PP = p`.

Express the relevant statement in the definitionally equal form `Ideal.absNorm P = p`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, ← Nat.card_eq_of_bijective _ hbij, Nat.card_zmod]`. Rewrite using `[this]`. Conclude with `Fact.out`. Establish `hmem : ((qOf PP : ℕ) : 𝓞 D.host.E) ∈ P` using `Ideal.absNorm_mem P`.

Use `haveI := hP.isPrime`. Use `⟨PP, hp, ?_, fun hv => ?_, GlobalTheory.MovedIdem.exists_isIdemAt PP fun he => ?_⟩` and prove the remaining obligations. Use `hN _ hp (not_le.1 fun h => key _ (Dvd.dvd.mul_left (Nat.dvd_factorial hp.pos h) _) hmem) P hmem` as an intermediate fact. Conclude with `ReciprocityTheory.Cheb.natCast_notMem_sq_of_isUnramifiedAt hp P`. Use `key (Ideal.absNorm (PP.under (𝓞 D.host.F)).asIdeal) (Dvd.dvd.mul_right (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (hS.mem_toFinset.2 hv)) _) _) ?_` and prove the remaining obligations.

Use `Ideal.absNorm_mem (PP.under (𝓞 D.host.F)).asIdeal` as an intermediate fact. Establish `h3 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P` using `this`. Simplify using `using h3`. Take `⟨n, hn⟩` from `hs (Ideal.Quotient.mk P θ)`. Establish `h3 : θ - n ∈ P`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, ← hn]`. Simplify using the standard rewrite rules. Establish `h4 : cO (θ - n) ∈ P`. Establish `: cO (θ - n) ∈ Formalism.HermitianLatticesTheory.conjIdeal (K` using `D.host.E) PP.asIdeal := Ideal.subset_span ⟨_, h3, rfl⟩`. Rewrite `this` using `[he]`. Then use the resulting hypothesis.

Rewrite `h4` using `[map_sub, hθ, map_intCast]`. Establish `h5 : 2 * θ ∈ P` using `by convert sub_mem h3 h4 using 1; ring`. Conclude with `key n₁ (Dvd.dvd.mul_right (dvd_mul_right _ _) _) ((Ideal.span_singleton_le_iff_mem _).2 h5 (Ideal.absNorm_mem _))`.
-/
theorem exists_place (D : D7) {S : Set (Pl D)} (hS : S.Finite) : ∃ PP : Formalism.L2.DIV.Pl D.host.E, (qOf PP).Prime ∧
    ((qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 ∧ PP.under (𝓞 D.host.F) ∉ S ∧ ∃ e, IsIdemAt e PP := by
  classical
  obtain ⟨N, hN⟩ := ReciprocityTheory.Cheb.exists_forall_isUnramifiedAt D.host.E
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) D.host.xi0
  have hb0 : (b : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 (nonZeroDivisors.ne_zero hb)
  let cO : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (starRingEnd D.host.E)
  have hc : ∀ x, ((cO x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) := fun _ => rfl
  have ha : (a : D.host.E) = D.host.xi0 * b := by rw [← hab]; exact (div_mul_cancel₀ _ hb0).symm
  let θ := a * cO b
  have hθ : cO θ = -θ := by
    apply RingOfIntegers.coe_injective
    change star ((a : D.host.E) * star (b : D.host.E)) = -((a : D.host.E) * star (b : D.host.E))
    rw [ha, star_mul', star_mul', star_star, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D]
    ring
  have hθ0 : 2 * θ ≠ 0 := by
    refine mul_ne_zero two_ne_zero (RingOfIntegers.coe_ne_zero_iff.1 ?_)
    change (a : D.host.E) * star (b : D.host.E) ≠ 0
    rw [ha]
    exact mul_ne_zero (mul_ne_zero (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D) hb0) (star_ne_zero.2 hb0)
  let n₁ := Ideal.absNorm (Ideal.span {2 * θ})
  let n₂ := ∏ v ∈ hS.toFinset, Ideal.absNorm v.asIdeal
  have h1 : n₁ ≠ 0 := by simpa [n₁, Ideal.absNorm_eq_zero_iff] using hθ0
  have h2 : n₂ ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
  obtain ⟨P, hP, hm, hs⟩ := GlobalTheory.LargeSplitPrime.exists_degree_one_avoiding D.host.E ((n₁ * n₂ * N.factorial : ℕ) : ℤ)
    (by exact_mod_cast mul_ne_zero (mul_ne_zero h1 h2) N.factorial_ne_zero)
  have key : ∀ n : ℕ, n ∣ n₁ * n₂ * N.factorial → (n : 𝓞 D.host.E) ∉ P := by
    rintro n ⟨t, ht⟩ hn
    apply hm
    rw [ht]; push_cast
    exact Ideal.mul_mem_right _ _ hn
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.E)
  let PP : Formalism.L2.DIV.Pl D.host.E := ⟨P, hP.isPrime, hne⟩
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  have hp : (qOf PP).Prime := by
    let p := ringChar (𝓞 D.host.E ⧸ P)
    haveI : Fact p.Prime := ⟨CharP.char_is_prime (𝓞 D.host.E ⧸ P) p⟩
    have hbij : Function.Bijective (ZMod.castHom (dvd_refl p) (𝓞 D.host.E ⧸ P)) := by
      refine ⟨RingHom.injective _, fun y => ?_⟩
      obtain ⟨n, rfl⟩ := hs y
      exact ⟨n, by simp⟩
    have : qOf PP = p := by
      change Ideal.absNorm P = p
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← Nat.card_eq_of_bijective _ hbij, Nat.card_zmod]
    rw [this]; exact Fact.out
  have hmem : ((qOf PP : ℕ) : 𝓞 D.host.E) ∈ P := Ideal.absNorm_mem P
  haveI := hP.isPrime
  refine ⟨PP, hp, ?_, fun hv => ?_, GlobalTheory.MovedIdem.exists_isIdemAt PP fun he => ?_⟩
  · have := hN _ hp (not_le.1 fun h => key _ (Dvd.dvd.mul_left (Nat.dvd_factorial hp.pos h) _) hmem) P hmem
    exact ReciprocityTheory.Cheb.natCast_notMem_sq_of_isUnramifiedAt hp P
  · refine key (Ideal.absNorm (PP.under (𝓞 D.host.F)).asIdeal)
      (Dvd.dvd.mul_right (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (hS.mem_toFinset.2 hv)) _) _) ?_
    have := Ideal.absNorm_mem (PP.under (𝓞 D.host.F)).asIdeal
    have h3 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P := this
    simpa using h3
  · obtain ⟨n, hn⟩ := hs (Ideal.Quotient.mk P θ)
    have h3 : θ - n ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, ← hn]; simp
    have h4 : cO (θ - n) ∈ P := by
      have : cO (θ - n) ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) PP.asIdeal := Ideal.subset_span ⟨_, h3, rfl⟩
      rwa [he] at this
    rw [map_sub, hθ, map_intCast] at h4
    have h5 : 2 * θ ∈ P := by convert sub_mem h3 h4 using 1; ring
    exact key n₁ (Dvd.dvd.mul_right (dvd_mul_right _ _) _)
      ((Ideal.span_singleton_le_iff_mem _).2 h5 (Ideal.absNorm_mem _))

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

/- English proof (translation)
Take `⟨k₀, _, _, _, _, q₀, he, -, hi, hd⟩` from `GlobalTheory.LocMod.SplitCompl.exists_place D PP q.e h`. Establish `pe : ∀ x, q.pr (q.e * x) = q.pr x` using `fun x => by rw [← q.sec_pr, q.pr_sec]`. Use `⟨fun a => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hi, q.int_iff, q₀.int_iff]`. Express the relevant statement in the definitionally equal form `finPart D (q.sec (q.pr _)) ∈ _ ↔ finPart D (q₀.sec (q₀.pr _)) ∈ _`.

Rewrite using `[q.sec_pr, q₀.sec_pr, he]`. Establish `hs : Function.Surjective (fun x => q.pr (q₀.sec x))` using `fun y => ⟨q₀.pr (q.sec y), by simp only [q₀.sec_pr, he, pe, q.pr_sec]⟩`. Use `hs.denseRange.comp hd (q.cont_pr.comp q₀.cont_sec)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`.

Express the relevant statement in the definitionally equal form `q.pr _ = q.pr (q₀.sec (q₀.pr _))`. Rewrite using `[q₀.sec_pr, he, pe]`.
-/
theorem int_dense {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) :
    (∀ a, (ofSplit q).pr a ∈ 𝒪[k] ↔ IntAt PP a) ∧ DenseRange (ofSplit q).pr := by
  obtain ⟨k₀, _, _, _, _, q₀, he, -, hi, hd⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP q.e h
  have pe : ∀ x, q.pr (q.e * x) = q.pr x := fun x => by rw [← q.sec_pr, q.pr_sec]
  refine ⟨fun a => ?_, ?_⟩
  · rw [← hi, q.int_iff, q₀.int_iff]
    change finPart D (q.sec (q.pr _)) ∈ _ ↔ finPart D (q₀.sec (q₀.pr _)) ∈ _
    rw [q.sec_pr, q₀.sec_pr, he]
  · have hs : Function.Surjective (fun x => q.pr (q₀.sec x)) := fun y =>
      ⟨q₀.pr (q.sec y), by simp only [q₀.sec_pr, he, pe, q.pr_sec]⟩
    have := hs.denseRange.comp hd (q.cont_pr.comp q₀.cont_sec)
    convert this using 1
    funext a
    change q.pr _ = q.pr (q₀.sec (q₀.pr _))
    rw [q₀.sec_pr, he, pe]

/- English proof (translation)
Take `⟨hi, hd⟩` from `int_dense q h`. Set `φ` to `q.pr.comp (incA D)`. Establish `hi' : ∀ a, valuation k (φ a) ≤ 1 ↔ PP.valuation D.host.E a ≤ 1` using `fun a => (hi a).trans (GlobalTheory.AdicComplMatch.intAt_iff PP a)`. Establish `hq : PP.valuation D.host.E (qOf PP : D.host.E) = WithZero.exp (-1 : ℤ)` using `GlobalTheory.AdicComplMatch.valuation_absNorm PP h2`. Establish `hq0 : (qOf PP : D.host.E) ≠ 0` using `fun e => by`.

Rewrite `hq` using `[e, map_zero]`. Conclude with `WithZero.exp_ne_zero hq.symm`. Establish `h0 : φ (qOf PP : D.host.E) ≠ 0` using `(map_ne_zero φ).2 hq0`. Establish `hE : ((valuation k).comap φ).IsEquiv (PP.valuation D.host.E)`. Rewrite using `[Valuation.isEquiv_iff_val_le_one]`.

Conclude with `fun {a} => hi' a`. Use `⟨Units.mk0 _ h0, fun x => ⟨fun hx => ?_, fun hx => hx.trans_lt ?_⟩, hi, hd, rfl, rfl⟩` and prove the remaining obligations. Distinguish the cases in `hx0 : x = 0`. Simplify using `[hx0]`. Establish `hv : valuation k x ≠ 0` using `(map_ne_zero _).2 hx0`.

Establish `h3 : {y : k | valuation k (y - x) < valuation k x} ∈ nhds x`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`. Conclude with `⟨Units.mk0 _ hv, by simp⟩`. Take `⟨a, ha⟩` from `hd.mem_nhds h3`. Establish `h4 : valuation k (φ a) = valuation k x` using `Valuation.map_eq_of_sub_lt _ ha`.

Rewrite `hx`, the goal using `[← h4]`. Establish `h5 : PP.valuation D.host.E a < 1` using `hE.lt_one_iff_lt_one.1 hx`. Use `(hE a _).2 ?_` and prove the remaining obligations. Rewrite using `[hq]`. Distinguish the cases in `h6 : PP.valuation D.host.E a = 0`.

Simplify using `[h6]`. Rewrite `h5`, the goal using `[← WithZero.exp_log h6]`. Rewrite `h5` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.

Use `(hE.lt_one_iff_lt_one (x := (qOf PP : D.host.E))).2 ?_` and prove the remaining obligations. Rewrite using `[hq, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_compl {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) (h2 : ((qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2) :
    ∃ ϖ : kˣ, IsUnif ϖ ∧ IsCompl PP (qOf PP) (q.pr.comp (incA D)) ϖ := by
  obtain ⟨hi, hd⟩ := int_dense q h
  let φ := q.pr.comp (incA D)
  have hi' : ∀ a, valuation k (φ a) ≤ 1 ↔ PP.valuation D.host.E a ≤ 1 := fun a =>
    (hi a).trans (GlobalTheory.AdicComplMatch.intAt_iff PP a)
  have hq : PP.valuation D.host.E (qOf PP : D.host.E) = WithZero.exp (-1 : ℤ) := GlobalTheory.AdicComplMatch.valuation_absNorm PP h2
  have hq0 : (qOf PP : D.host.E) ≠ 0 := fun e => by
    rw [e, map_zero] at hq; exact WithZero.exp_ne_zero hq.symm
  have h0 : φ (qOf PP : D.host.E) ≠ 0 := (map_ne_zero φ).2 hq0
  have hE : ((valuation k).comap φ).IsEquiv (PP.valuation D.host.E) := by
    rw [Valuation.isEquiv_iff_val_le_one]; exact fun {a} => hi' a
  refine ⟨Units.mk0 _ h0, fun x => ⟨fun hx => ?_, fun hx => hx.trans_lt ?_⟩, hi, hd, rfl, rfl⟩
  · by_cases hx0 : x = 0
    · simp [hx0]
    have hv : valuation k x ≠ 0 := (map_ne_zero _).2 hx0
    have h3 : {y : k | valuation k (y - x) < valuation k x} ∈ nhds x := by
      rw [IsValuativeTopology.mem_nhds_iff']
      exact ⟨Units.mk0 _ hv, by simp⟩
    obtain ⟨a, ha⟩ := hd.mem_nhds h3
    have h4 : valuation k (φ a) = valuation k x := Valuation.map_eq_of_sub_lt _ ha
    rw [← h4] at hx ⊢
    have h5 : PP.valuation D.host.E a < 1 := hE.lt_one_iff_lt_one.1 hx
    refine (hE a _).2 ?_
    rw [hq]
    by_cases h6 : PP.valuation D.host.E a = 0
    · simp [h6]
    · rw [← WithZero.exp_log h6] at h5 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h5
      rw [WithZero.exp_le_exp]; omega
  · refine (hE.lt_one_iff_lt_one (x := (qOf PP : D.host.E))).2 ?_
    rw [hq, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

/- English proof (translation)
Establish `he` using `(DblInhab.sec_mem_intAt q 1).2 (map_one _).le`. Take `⟨h1, h2⟩` from `hu.1 _ he`. Establish `h3` using `DblInhab.pr_le_one q h1`. Establish `h4` using `DblInhab.pr_le_one q h2`. Rewrite `h3`, `h4` using `[map_mul, q.pr_sec, mul_one]`.

Express the relevant statement in the definitionally equal form `valuation k ((q.pr.comp (incA D)) _) ≤ 1 at h4`. Rewrite `h4` using `[map_inv₀, map_inv₀]`. Conclude with `le_antisymm h3 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (Witness.xi_ne (ofSplit q))))).1 h4)`.
-/
theorem xi_unit (hu : q.UnitAA) : valuation k (ofSplit q).xi = 1 := by
  have he := (DblInhab.sec_mem_intAt q 1).2 (map_one _).le
  obtain ⟨h1, h2⟩ := hu.1 _ he
  have h3 := DblInhab.pr_le_one q h1
  have h4 := DblInhab.pr_le_one q h2
  rw [map_mul, q.pr_sec, mul_one] at h3 h4
  change valuation k ((q.pr.comp (incA D)) _) ≤ 1 at h4
  rw [map_inv₀, map_inv₀] at h4
  exact le_antisymm h3 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (Witness.xi_ne (ofSplit q))))).1 h4)

/- English proof (translation)
Take `⟨⟨ψk, hk⟩, -⟩` from `GlobalTheory.LocChar.weil_char_split D k (ofSplit q) ψ hψ`. Establish `hx` using `Witness.xi_ne (ofSplit q)`. Establish `hv` using `xi_unit q hu`. Establish `h1 : q.IsChar ψ (ψk.mulShift (ofSplit q).xi⁻¹)` using `fun a => by`. Rewrite using `[AddChar.mulShift_apply, hk]`.

Express the relevant statement in the definitionally equal form `psiE ψ (incA D D.host.xi0 * q.sec _) = _`. Rewrite using `[mul_comm (incA D _), ← DblInhab.sec_mul_pr]`. Express the relevant statement in the definitionally equal form `psiE ψ (q.sec (_ * (ofSplit q).xi)) = _`. Rewrite using `[mul_comm, mul_inv_cancel_left₀ hx]`. Establish `h2` using `GlobalTheory.SplitCharCond.hasConductor_one D k q ψ _ hψ h1 hu`.

Use `⟨ψk, hk, fun x => (Iff.trans ⟨fun h y hy => ?_, fun h y hy => ?_⟩ (h2 x))⟩` and prove the remaining obligations. Conclude with `h _ (by simpa [hv] using hy)`. Use `h ((ofSplit q).xi * y) (by simpa [hv] using hy)` as an intermediate fact. Rewrite `this` using `[AddChar.mulShift_apply, inv_mul_cancel_left₀ hx]`. Then use the resulting hypothesis.
-/
theorem exists_char (hu : q.UnitAA) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ ψk, (ofSplit q).IsChar ψ ψk ∧ HasConductor ψk 1 := by
  obtain ⟨⟨ψk, hk⟩, -⟩ := GlobalTheory.LocChar.weil_char_split D k (ofSplit q) ψ hψ
  have hx := Witness.xi_ne (ofSplit q)
  have hv := xi_unit q hu
  have h1 : q.IsChar ψ (ψk.mulShift (ofSplit q).xi⁻¹) := fun a => by
    rw [AddChar.mulShift_apply, hk]
    change psiE ψ (incA D D.host.xi0 * q.sec _) = _
    rw [mul_comm (incA D _), ← DblInhab.sec_mul_pr]
    change psiE ψ (q.sec (_ * (ofSplit q).xi)) = _
    rw [mul_comm, mul_inv_cancel_left₀ hx]
  have h2 := GlobalTheory.SplitCharCond.hasConductor_one D k q ψ _ hψ h1 hu
  refine ⟨ψk, hk, fun x => (Iff.trans ⟨fun h y hy => ?_, fun h y hy => ?_⟩ (h2 x))⟩
  · exact h _ (by simpa [hv] using hy)
  · have := h ((ofSplit q).xi * y) (by simpa [hv] using hy)
    rwa [AddChar.mulShift_apply, inv_mul_cancel_left₀ hx] at this

end Place

section Rat
variable {D : D7}

def IsRat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) {N : ℕ}
    {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) (M : Matrix (Fin N) Y D.host.E) : Prop := F.β = M.map (ofSplit q).pr

variable {n : Type} [Fintype n] [DecidableEq n]

def stdFr (k : Type) [Field k] {N : ℕ} (e : n ≃ Fin N) : Frame k N n :=
  ⟨(1 : Matrix (Fin N) (Fin N) k).submatrix id e, (1 : Matrix (Fin N) (Fin N) k).submatrix e id,
    by rw [submatrix_mul_equiv]; simp, by rw [← submatrix_mul (he₂ := Function.bijective_id)]; simp⟩

end Rat

variable {D : D7}

def Ranked (c : Comm D) : Prop := (∀ j, j ≤ D.R.m → (c.X j).rank = D.R.N j) ∧ c.T.rank = D.R.r + D.R.m * D.R.t

/- English proof (translation)
Establish `h1` using `(c.oT _ rfl).rank_add`. Establish `h2` using `D.R.two_le_m`. Rewrite `h1` using `[h.1 _ le_rfl, h.2, Ranks.N, Ranks.r, mul_add]`. Use linear arithmetic over natural numbers and integers.
-/
theorem Ranked.line {c : Comm D} (h : Ranked c) : c.Lz.rank = 1 := by
  have h1 := (c.oT _ rfl).rank_add
  have h2 := D.R.two_le_m
  rw [h.1 _ le_rfl, h.2, Ranks.N, Ranks.r, mul_add] at h1
  omega

section Loc
open GlobalTheory.Fam Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.MainNotions

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Links.RealDat D A Ks) (P : Formalism.L2.DIV.LevelP R.Pg D.R.r ℂ) (u : D.what₂.Word)
  {a : XGeo D} {y : YRat a} (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf R u (mkGeo m b)))
  {PP : Formalism.L2.DIV.Pl D.host.E} (l : LocX a R.βX PP)

set_option maxHeartbeats 2000000 in

def ofLoc (n : LocY l y v.N R.βY b fun _ _ _ => 1) (hψ : IsStdChar D R.ψ (-1)) (hτ : v.τ = y.τ) (hT : v.NT = a.LT)
    (h2 : ((qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2) : QGeo v (baseOf R P u (mkGeo m b)) PP where
  k := l.k
  ν := (GlobalTheory.SplitWeil.exists_isUnitVol l.k).choose
  unitVol := (GlobalTheory.SplitWeil.exists_isUnitVol l.k).choose_spec
  q := l.q
  idem := l.idem
  unit := l.unit
  ψk := (exists_char l.q l.unit hψ).choose
  char := (exists_char l.q l.unit hψ).choose_spec.1
  cond := (exists_char l.q l.unit hψ).choose_spec.2
  ϖ := (exists_compl l.q l.idem h2).choose
  unif := (exists_compl l.q l.idem h2).choose_spec.1
  compl := (exists_compl l.q l.idem h2).choose_spec.2
  s := l.s
  hs := l.hs
  FX := l.FX
  FT := l.FT
  FM := l.FM
  FY := n.FY
  sc := n.sc
  sc_ne := fun j e => by simpa [e] using n.sc_unit j
  sc_step := n.sc_step
  bes := n.bes
  jac := n.jac
  z₀ := fun i => (ofSplit l.q).pr (a.ζ₀ i)
  last := l.last
  tau := fun h => by rw [hτ]; exact n.tau h
  latX := l.latX
  latM := l.latM
  latY := n.latY
  latT := by rw [hT]; exact l.latT
  gl := fun j d hd => (GlobalTheory.QPl.Model.exists_gl l.q _ (n.FY j d hd)).choose
  gl_loc := fun j d hd => (GlobalTheory.QPl.Model.exists_gl l.q _ (n.FY j d hd)).choose_spec
  frame := fun j d hd => by simpa only [Units.val_one, Matrix.mul_one] using n.frame j d hd
  frameTop := l.frameTop

end Loc

end GlobalTheory.QTw.GeoInhab
end
