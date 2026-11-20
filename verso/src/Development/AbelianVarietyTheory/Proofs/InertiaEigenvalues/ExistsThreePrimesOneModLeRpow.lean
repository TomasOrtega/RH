import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationComapLtOne
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.NotGoodOfNoData

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (TwDatum Twisted SameBelow SamePair LiesUnder TwistedPlaceSettings namedPrimes expDat GoodDatum GoodSystem
  recorded ExistsChoice WithToricIntegralityConstant FamTwGood TwGoodClosed)

namespace GlobalTheory.TwistGoodCompare

variable {D : D7}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem twisted_iff (w : D.what₂.places.Pl) : Twisted D w ↔ TwistedAt D w := Iff.rfl

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | h0` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[D.val_eq w x h0]`. Establish `h1 : (D.plEq w).valuation D.what₂.LL x ≤ 1` using `(D.plEq w).valuation_le_one (⟨x, hx⟩ : 𝓞 D.what₂.LL)`. Establish `h2 : (D.plEq w).valuation D.what₂.LL x ≠ 0` using `by simpa using h0`.

Establish `h3 : WithZero.log ((D.plEq w).valuation D.what₂.LL x) ≤ 0`. Rewrite using `[← WithZero.log_one, WithZero.log_le_log h2 one_ne_zero]`. Conclude with `h1`. Establish `: 0 ≤ vAdd (D.plEq w) x` using `by unfold vAdd; omega`. Conclude with `this` after adjusting the coercions.
-/
theorem val_int_nonneg (w : D.what₂.places.Pl) {x : D.what₂.LL} (hx : IsIntegral ℤ x) :
    0 ≤ D.what₂.places.val w x := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  rw [D.val_eq w x h0]
  have h1 : (D.plEq w).valuation D.what₂.LL x ≤ 1 := (D.plEq w).valuation_le_one (⟨x, hx⟩ : 𝓞 D.what₂.LL)
  have h2 : (D.plEq w).valuation D.what₂.LL x ≠ 0 := by simpa using h0
  have h3 : WithZero.log ((D.plEq w).valuation D.what₂.LL x) ≤ 0 := by
    rw [← WithZero.log_one, WithZero.log_le_log h2 one_ne_zero]; exact h1
  have : 0 ≤ vAdd (D.plEq w) x := by unfold vAdd; omega
  exact_mod_cast this

/- English proof (translation)
The claim follows from `(RingOfIntegers.isIntegral_coe x).map (D.LL0.val.toRingHom.toIntAlgHom)`.
-/
theorem isIntegral_coe (x : 𝓞 ↥D.LL0) : IsIntegral ℤ ((x : ↥D.LL0) : D.what₂.LL) :=
  (RingOfIntegers.isIntegral_coe x).map (D.LL0.val.toRingHom.toIntAlgHom)

def below (w : D.what₂.places.Pl) : HeightOneSpectrum (𝓞 ↥D.LL0) where
  asIdeal :=
    { carrier := {x | 0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL)}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        have := (D.what₂.places.val w).map_add ((a : ↥D.LL0) : D.what₂.LL) ((b : ↥D.LL0) : D.what₂.LL)
        exact lt_of_lt_of_le (lt_min ha hb) this
      smul_mem' := fun a b hb => by
        have := (D.what₂.places.val w).map_mul ((a : ↥D.LL0) : D.what₂.LL) ((b : ↥D.LL0) : D.what₂.LL)
        have h2 := lt_of_lt_of_le hb (le_add_of_nonneg_left (val_int_nonneg w (isIntegral_coe a)))
        rw [← this] at h2
        exact h2 }
  isPrime := by
    refine ⟨fun h => ?_, fun {a b} h => ?_⟩
    · rw [Ideal.eq_top_iff_one] at h
      have : 0 < D.what₂.places.val w (((1 : 𝓞 ↥D.LL0) : ↥D.LL0) : D.what₂.LL) := h
      simp at this
    · by_contra hn
      rw [not_or] at hn
      have ha : D.what₂.places.val w ((a : ↥D.LL0) : D.what₂.LL) = 0 :=
        le_antisymm (not_lt.1 hn.1) (val_int_nonneg w (isIntegral_coe a))
      have hb : D.what₂.places.val w ((b : ↥D.LL0) : D.what₂.LL) = 0 :=
        le_antisymm (not_lt.1 hn.2) (val_int_nonneg w (isIntegral_coe b))
      have h' : 0 < D.what₂.places.val w (((a * b : 𝓞 ↥D.LL0) : ↥D.LL0) : D.what₂.LL) := h
      have := (D.what₂.places.val w).map_mul ((a : ↥D.LL0) : D.what₂.LL) ((b : ↥D.LL0) : D.what₂.LL)
      rw [ha, hb] at this
      simp [this] at h'
  ne_bot := by
    intro h
    have h1 : ((D.what₂.places.resChar w : ℕ) : 𝓞 ↥D.LL0) ∈ (⊥ : Ideal (𝓞 ↥D.LL0)) := by
      rw [← h]
      show 0 < D.what₂.places.val w ((((D.what₂.places.resChar w : ℕ) : 𝓞 ↥D.LL0) : ↥D.LL0) : D.what₂.LL)
      have := D.what₂.places.val_resChar w
      simp only [map_natCast, RingOfIntegers.coe_eq_algebraMap, SubringClass.coe_natCast]
      rw [this]
      exact_mod_cast D.what₂.places.ramIdx_pos w
    rw [Ideal.mem_bot] at h1
    exact (D.what₂.places.resChar_prime w).ne_zero (by exact_mod_cast h1)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_below (w : D.what₂.places.Pl) (x : 𝓞 ↥D.LL0) :
    x ∈ (below w).asIdeal ↔ 0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) := Iff.rfl

/- English proof (translation)
The claim follows from `le_antisymm (not_lt.1 hx) (val_int_nonneg w (isIntegral_coe x))`.
-/
theorem val_eq_zero_of_not_mem (w : D.what₂.places.Pl) {x : 𝓞 ↥D.LL0} (hx : x ∉ (below w).asIdeal) :
    D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) = 0 :=
  le_antisymm (not_lt.1 hx) (val_int_nonneg w (isIntegral_coe x))

/- English proof (translation)
Take `⟨n, ⟨d, hd⟩, e | e⟩` from `(below w).exists_primeCompl_mul_eq_or_mul_eq (K := ↥D.LL0) x`. Establish `e' : (x : D.what₂.LL) * ((d : ↥D.LL0) : D.what₂.LL) = ((n : ↥D.LL0) : D.what₂.LL)`. Conclude with `congrArg Subtype.val e` after adjusting the coercions. Establish `h1` using `(D.what₂.places.val w').map_mul (x : D.what₂.LL) ((d : ↥D.LL0) : D.what₂.LL)`. Rewrite `h1` using `[e', val_eq_zero_of_not_mem w' (x := d) (h ▸ hd), add_zero]`.

Rewrite using `[← h1]`. Conclude with `val_int_nonneg w' (isIntegral_coe n)`. Establish `e' : (x : D.what₂.LL) * ((n : ↥D.LL0) : D.what₂.LL) = ((d : ↥D.LL0) : D.what₂.LL)`. Conclude with `congrArg Subtype.val e` after adjusting the coercions. Establish `h1` using `(D.what₂.places.val w).map_mul (x : D.what₂.LL) ((n : ↥D.LL0) : D.what₂.LL)`.

Rewrite `h1` using `[e', val_eq_zero_of_not_mem w hd]`. Establish `hn : n ∉ (below w).asIdeal` using `fun hn => by`. Use `lt_of_lt_of_le ((mem_below w n).1 hn) (le_add_of_nonneg_left hx)` as an intermediate fact. Rewrite `this` using `[← h1]`. Conclude with `lt_irrefl _ this`.

Establish `h2` using `(D.what₂.places.val w').map_mul (x : D.what₂.LL) ((n : ↥D.LL0) : D.what₂.LL)`. Rewrite `h2` using `[e', val_eq_zero_of_not_mem w' (x := d) (h ▸ hd), val_eq_zero_of_not_mem w' (x := n) (h ▸ hn), add_zero]`. Conclude with `h2.le`.
-/
theorem nonneg_of_below {w w' : D.what₂.places.Pl} (h : below w = below w') (x : ↥D.LL0)
    (hx : 0 ≤ D.what₂.places.val w (x : D.what₂.LL)) : 0 ≤ D.what₂.places.val w' (x : D.what₂.LL) := by
  obtain ⟨n, ⟨d, hd⟩, e | e⟩ := (below w).exists_primeCompl_mul_eq_or_mul_eq (K := ↥D.LL0) x
  · have e' : (x : D.what₂.LL) * ((d : ↥D.LL0) : D.what₂.LL) = ((n : ↥D.LL0) : D.what₂.LL) := by
      exact_mod_cast congrArg Subtype.val e
    have h1 := (D.what₂.places.val w').map_mul (x : D.what₂.LL) ((d : ↥D.LL0) : D.what₂.LL)
    rw [e', val_eq_zero_of_not_mem w' (x := d) (h ▸ hd), add_zero] at h1
    rw [← h1]
    exact val_int_nonneg w' (isIntegral_coe n)
  · have e' : (x : D.what₂.LL) * ((n : ↥D.LL0) : D.what₂.LL) = ((d : ↥D.LL0) : D.what₂.LL) := by
      exact_mod_cast congrArg Subtype.val e
    have h1 := (D.what₂.places.val w).map_mul (x : D.what₂.LL) ((n : ↥D.LL0) : D.what₂.LL)
    rw [e', val_eq_zero_of_not_mem w hd] at h1
    have hn : n ∉ (below w).asIdeal := fun hn => by
      have := lt_of_lt_of_le ((mem_below w n).1 hn) (le_add_of_nonneg_left hx)
      rw [← h1] at this
      exact lt_irrefl _ this
    have h2 := (D.what₂.places.val w').map_mul (x : D.what₂.LL) ((n : ↥D.LL0) : D.what₂.LL)
    rw [e', val_eq_zero_of_not_mem w' (x := d) (h ▸ hd), val_eq_zero_of_not_mem w' (x := n) (h ▸ hn), add_zero] at h2
    exact h2.le

/- English proof (translation)
Establish `e : below w = below w'`. Use extensionality with `x`. Rewrite using `[mem_below, mem_below, ← h x, ← h' x]`. Conclude with `fun x => ⟨nonneg_of_below e x, nonneg_of_below e.symm x⟩`.
-/
theorem sameBelow_of_liesUnder {i : D.ntw.Tw} {w w' : D.what₂.places.Pl} (h : LiesUnder D i w)
    (h' : LiesUnder D i w') : SameBelow D w w' := by
  have e : below w = below w' := by
    ext x
    rw [mem_below, mem_below, ← h x, ← h' x]
  exact fun x => ⟨nonneg_of_below e x, nonneg_of_below e.symm x⟩

def exists_three_primes_one_mod_le_rpow (D : D7) : Set ℕ := {p | p.Prime ∧ (p = q0Av D ∨ p ∣ Ideal.absNorm D.host.ccK)}

def AvoidsFurtherPrimes (Q : Finset (PlE D.host)) : Prop := ∀ P ∈ Q, ∀ p ∈ exists_three_primes_one_mod_le_rpow D, P ∉ placesOver D.host.E p

def GoodPowers (I : TwIn D) (t : TwDatum D) : Prop :=
  I.Ok t.1 ∧ ∀ a : ℤ, IsCoprime a (D.ntw.l t.1 : ℤ) → TwGoodOne D I t.1 true t.2.1 t.2.2.1 (t.2.2.2 ^ a)

def ConstantTermsFinite (i : D.ntw.Tw) : Prop := ∀ lam : D.ntw.abelian₂ i, (∑ δ, D.ntw.th i ∅ lam δ) ≠ 0

/- English proof (translation)
Unfold `GoodPowers TwIn.Ok TwGoodOne at *`. Simplify using `only at hg ⊢`. Rewrite using `[← h]`. Conclude with `hg`.
-/
theorem goodPowers_congr {E : IntegralHeckeForms.XD D} {N0 S S'} {t : TwDatum D} (h : S t.1 = S' t.1)
    (hg : GoodPowers ⟨E, N0, S⟩ t) : GoodPowers ⟨E, N0, S'⟩ t := by
  unfold GoodPowers TwIn.Ok TwGoodOne at *
  simp only at hg ⊢
  rw [← h]
  exact hg

def AtPlace (t : D.what₂.places.Pl → TwDatum D) : Prop :=
  ∀ w, Twisted D w → LiesUnder D (t w).1 w ∨ LiesUnder D (t w).1 (D.what₂.places.conj w)

def OnePerPair (t : D.what₂.places.Pl → TwDatum D) : Prop :=
  ∀ w w', Twisted D w → Twisted D w' → SamePair D w w' → t w = t w'

def DisjointPairs (t : D.what₂.places.Pl → TwDatum D) : Prop :=
  ∀ w w', Twisted D w → Twisted D w' → ¬ SamePair D w w' →
    ∀ P ∈ (t w).2.1, ∀ P' ∈ (t w').2.1, ∀ p : ℕ, p.Prime →
      ¬ (P ∈ placesOver D.host.E p ∧ P' ∈ placesOver D.host.E p)

/- English proof (translation)
Establish `cw` using `(GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj w).2 hw`. Establish `cw'` using `(GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj w').2 hw'`. Establish `ew` using `h2 _ _ hw cw (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.samePair_conj w)`. Establish `ew'` using `h2 _ _ hw' cw' (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.samePair_conj w')`. Apply the tactic sequence `rcases h1 w hw with a | a <;> rcases h1 w' hw' with b | b <;> rw [← e] at b <;>`.

Establish `s` using `sameBelow_of_liesUnder a b`. Conclude with `h2 _ _ hw hw' (Or.inl s)`. Rewrite using `[ew']`. Conclude with `h2 _ _ hw cw' (Or.inl s)`. Rewrite using `[ew]`.

Conclude with `h2 _ _ cw hw' (Or.inl s)`. Rewrite using `[ew, ew']`. Conclude with `h2 _ _ cw cw' (Or.inl s)`.
-/
theorem eq_of_setting_eq {t : D.what₂.places.Pl → TwDatum D} (h1 : AtPlace t) (h2 : OnePerPair t)
    {w w' : D.what₂.places.Pl} (hw : Twisted D w) (hw' : Twisted D w') (e : (t w).1 = (t w').1) : t w = t w' := by
  have cw := (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj w).2 hw
  have cw' := (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj w').2 hw'
  have ew := h2 _ _ hw cw (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.samePair_conj w)
  have ew' := h2 _ _ hw' cw' (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.samePair_conj w')
  rcases h1 w hw with a | a <;> rcases h1 w' hw' with b | b <;> rw [← e] at b <;>
    have s := sameBelow_of_liesUnder a b
  · exact h2 _ _ hw hw' (Or.inl s)
  · rw [ew']; exact h2 _ _ hw cw' (Or.inl s)
  · rw [ew]; exact h2 _ _ cw hw' (Or.inl s)
  · rw [ew, ew']; exact h2 _ _ cw cw' (Or.inl s)

/- English proof (translation)
Establish `key : ∀ i : D.ntw.Tw, ∃ S, ∀ w, Twisted D w → (t w).1 = i → GoodPowers ⟨E, N0, S⟩ (t w)`. Introduce `i`. Distinguish the cases in `hi : ∃ w, Twisted D w ∧ (t w).1 = i`. Take `⟨w0, hw0, e0⟩` from `hi`. Take `⟨S, hS⟩` from `h w0 hw0`.

Conclude with `⟨S, fun w hw e => eq_of_setting_eq h1 h2 hw0 hw (e0.trans e.symm) ▸ hS⟩`. Conclude with `⟨fun _ _ _ => ∅, fun w hw e => absurd ⟨w, hw, e⟩ hi⟩`. Use `choose S hS using key`. Conclude with `⟨fun i => S i i, fun w hw => goodPowers_congr rfl (hS _ w hw rfl)⟩`.
-/
theorem exists_series {E : IntegralHeckeForms.XD D} {N0} {t : D.what₂.places.Pl → TwDatum D} (h1 : AtPlace t) (h2 : OnePerPair t)
    (h : ∀ w, Twisted D w → ∃ S, GoodPowers ⟨E, N0, S⟩ (t w)) :
    ∃ S, ∀ w, Twisted D w → GoodPowers ⟨E, N0, S⟩ (t w) := by
  have key : ∀ i : D.ntw.Tw, ∃ S, ∀ w, Twisted D w → (t w).1 = i → GoodPowers ⟨E, N0, S⟩ (t w) := by
    intro i
    by_cases hi : ∃ w, Twisted D w ∧ (t w).1 = i
    · obtain ⟨w0, hw0, e0⟩ := hi
      obtain ⟨S, hS⟩ := h w0 hw0
      exact ⟨S, fun w hw e => eq_of_setting_eq h1 h2 hw0 hw (e0.trans e.symm) ▸ hS⟩
    · exact ⟨fun _ _ _ => ∅, fun w hw e => absurd ⟨w, hw, e⟩ hi⟩
  choose S hS using key
  exact ⟨fun i => S i i, fun w hw => goodPowers_congr rfl (hS _ w hw rfl)⟩

def TwGoodAllAt (c : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, TwistedAt D w → I.Ok (c.twI w) ∧ ∀ a : ℤ, IsCoprime a (D.ntw.l (c.twI w) : ℤ) →
    TwGoodOne D I (c.twI w) (c.sd w) (c.Q w) (c.k' w) (c.psi' w ^ a)

/- English proof (translation)
Introduce `w hw` and use `by have := (h w hw).2 1 isCoprime_one_left rw [zpow_one] at this exact ⟨(h w hw).1, this⟩`.
-/
theorem TwGoodAllAt.twGoodAt {c : NChoice D} {I : TwIn D} (h : TwGoodAllAt c I) : TwGoodAt D c I := fun w hw => by
  have := (h w hw).2 1 isCoprime_one_left
  rw [zpow_one] at this
  exact ⟨(h w hw).1, this⟩

def AvoidsFurtherPrimesAt (c : NChoice D) : Prop := ∀ w, TwistedAt D w → AvoidsFurtherPrimes (c.Q w)

def Surplus (c : NChoice D) : Prop :=
  (∀ w, TwistedAt D w → ConstantTermsFinite (c.twI w)) ∧ AtPlace (recorded c) ∧ OnePerPair (recorded c) ∧
    DisjointPairs (recorded c)

/- English proof (translation)
Use `haveI := c.Oe_loc w`. Establish `h1` using `(isUnit_map_iff _ _).1 h`. Use `clear h`. Generalize the expression as in `c.k' w = k at h1`. Generalize the expression as in `c.twI w = i at y k h1`.

Use `haveI := D.ntw.Ok_fin i k`. Use `haveI : FaithfulSMul (D.ntw.O i) (D.ntw.Ok i k) := (faithfulSMul_iff_algebraMap_injective _ _).2 (D.ntw.Ok_inj i _)`. Establish `h2` using `(isUnit_map_iff (algebraMap (D.ntw.O i) (D.ntw.Ok i k)) _).1 h1`. Assume the negation of the conclusion as `hy`. Establish `hl : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ≠ 0` using `fun h0 => by`.

Use `congrArg (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) h0` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero, ← map_natCast (D.ntw.emb0 i), map_eq_zero]`. Conclude with `(D.ntw.lPrime i).out.ne_zero (by exact_mod_cast this)`. Establish `hP : ((IsLocalRing.maximalIdeal (D.ntw.O i)).comap (algebraMap (D.ntw.O0 i) (D.ntw.O i))).IsMaximal`. Use `Ideal.IsPrime.isMaximal inferInstance fun h0 => hl ?_` and prove the remaining obligations.

Rewrite using `[← Ideal.mem_bot, ← h0, Ideal.mem_comap, map_natCast]`. Conclude with `D.ntw.O_l i`. Establish `hm : y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i)` using `hy`. Rewrite `hm` using `[← IsLocalRing.eq_maximalIdeal hP, Ideal.mem_comap]`. Conclude with `hm h2`.
-/
theorem isUnit_of_toOe (c : NChoice D) (w : D.what₂.places.Pl) (y : D.ntw.O0 (c.twI w))
    (h : IsUnit (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
      (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w))
        (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y)))) : IsUnit y := by
  haveI := c.Oe_loc w
  have h1 := (isUnit_map_iff _ _).1 h
  clear h
  generalize c.k' w = k at h1
  generalize c.twI w = i at y k h1
  haveI := D.ntw.Ok_fin i k
  haveI : FaithfulSMul (D.ntw.O i) (D.ntw.Ok i k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (D.ntw.Ok_inj i _)
  have h2 := (isUnit_map_iff (algebraMap (D.ntw.O i) (D.ntw.Ok i k)) _).1 h1
  by_contra hy
  have hl : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ≠ 0 := fun h0 => by
    have := congrArg (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) h0
    rw [map_natCast, map_zero, ← map_natCast (D.ntw.emb0 i), map_eq_zero] at this
    exact (D.ntw.lPrime i).out.ne_zero (by exact_mod_cast this)
  have hP : ((IsLocalRing.maximalIdeal (D.ntw.O i)).comap (algebraMap (D.ntw.O0 i) (D.ntw.O i))).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => hl ?_
    rw [← Ideal.mem_bot, ← h0, Ideal.mem_comap, map_natCast]
    exact D.ntw.O_l i
  have hm : y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i) := hy
  rw [← IsLocalRing.eq_maximalIdeal hP, Ideal.mem_comap] at hm
  exact hm h2

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | h0` into its components or cases. Establish `: z = 0` using `IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) (by rw [← h, map_zero, map_zero])`. Simplify using `[this]`. Establish `hx : 0 ≤ D.what₂.places.val w x` using `(c.embW_w w x).2 ⟨z, h.symm⟩`. Establish `hmul` using `(D.what₂.places.val w).map_mul x x⁻¹`.

Rewrite `hmul` using `[mul_inv_cancel₀ h0, AddValuation.map_one]`. Establish `e1 : 0 < D.what₂.places.val w x ↔ ¬ 0 ≤ D.what₂.places.val w x⁻¹`. Rewrite `*` using `[D.val_eq w x h0, D.val_eq w _ (inv_ne_zero h0)]`. Normalize the coercions in `at *`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e1, c.embW_w, not_iff_not]`. Establish `hz : c.embW w x ≠ 0` using `by simpa using h0`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu⟩`. Use `IsUnit.of_mul_eq_one u (IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) ?_)` and prove the remaining obligations.

Rewrite using `[map_mul, hu, ← h, map_one, ← map_mul, mul_inv_cancel₀ h0, map_one]`. Introduce and unpack `⟨u, rfl⟩`. Use `⟨((u⁻¹ : (c.Oe w)ˣ) : c.Oe w), ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv₀, h]`. Conclude with `eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])`.
-/
theorem pos_iff_not_isUnit (c : NChoice D) (w : D.what₂.places.Pl) (x : D.what₂.LL) (z : c.Oe w)
    (h : c.embW w x = algebraMap (c.Oe w) (FractionRing (c.Oe w)) z) :
    0 < D.what₂.places.val w x ↔ ¬ IsUnit z := by
  rcases eq_or_ne x 0 with rfl | h0
  · have : z = 0 := IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) (by rw [← h, map_zero, map_zero])
    simp [this]
  have hx : 0 ≤ D.what₂.places.val w x := (c.embW_w w x).2 ⟨z, h.symm⟩
  have hmul := (D.what₂.places.val w).map_mul x x⁻¹
  rw [mul_inv_cancel₀ h0, AddValuation.map_one] at hmul
  have e1 : 0 < D.what₂.places.val w x ↔ ¬ 0 ≤ D.what₂.places.val w x⁻¹ := by
    rw [D.val_eq w x h0, D.val_eq w _ (inv_ne_zero h0)] at *
    norm_cast at *
    omega
  rw [e1, c.embW_w, not_iff_not]
  have hz : c.embW w x ≠ 0 := by simpa using h0
  constructor
  · rintro ⟨u, hu⟩
    refine IsUnit.of_mul_eq_one u (IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) ?_)
    rw [map_mul, hu, ← h, map_one, ← map_mul, mul_inv_cancel₀ h0, map_one]
  · rintro ⟨u, rfl⟩
    refine ⟨((u⁻¹ : (c.Oe w)ˣ) : c.Oe w), ?_⟩
    rw [map_inv₀, h]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

/- English proof (translation)
Set `σ : D.what₂.LL →ₐ[ℚ] D.what₂.LL` to `(starRingEnd D.what₂.LL).toRatAlgHom`. Conclude with `⟨σ.restrictNormal ↥D.LL0 x, σ.restrictNormal_commutes ↥D.LL0 x⟩`.
-/
theorem exists_star (hG : IsGalois ℚ ↥D.LL0) (x : ↥D.LL0) : ∃ x' : ↥D.LL0, (x' : D.what₂.LL) = star (x : D.what₂.LL) := by
  let σ : D.what₂.LL →ₐ[ℚ] D.what₂.LL := (starRingEnd D.what₂.LL).toRatAlgHom
  exact ⟨σ.restrictNormal ↥D.LL0 x, σ.restrictNormal_commutes ↥D.LL0 x⟩

/- English proof (translation)
Introduce `x`. Establish `hint : IsIntegral (D.ntw.O0 (c.twI w)) (D.ntw.emb0 (c.twI w) (x : ↥D.LL0))` using `(RingOfIntegers.isIntegral_coe x).map_of_comp_eq (Int.castRingHom _) (D.ntw.emb0 (c.twI w)) (RingHom.ext_int _ _)`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral hint`. Establish `hleft : (∃ y' ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)), algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y' = D.ntw.emb0 (c.twI w) (x : ↥D.LL0)) ↔ ¬ IsUnit y`. Use `⟨fun ⟨y', h1, h2⟩ => ?_, fun h1 => ⟨y, h1, hy⟩⟩` and prove the remaining obligations.

Rewrite using `[← IsFractionRing.injective _ _ (h2.trans hy.symm)]`. Conclude with `h1`. Establish `key : ∀ x' : ↥D.LL0, (if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x' = D.ntw.emb0 (c.twI w) (x : ↥D.LL0) → (0 < D.what₂.places.val w (x' : D.what₂.LL) ↔ ¬ IsUnit y)`. Introduce `x' hx'`. Establish `e` using `h.embedding_baseField_condition w x' y 1 one_ne_zero (by rw [hx', map_one, mul_one, hy])`.

Simplify using `only [map_one, mul_one] at e`. Rewrite using `[pos_iff_not_isUnit c w _ _ e, not_iff_not]`. Conclude with `⟨isUnit_of_toOe c w y, fun hu => ((hu.map _).map _).map _⟩`. Rewrite using `[hleft]`. Consider the cases of `hs : c.sd w`.

Take `⟨x', hx'⟩` from `exists_star hG (x : ↥D.LL0)`. Rewrite using `[if_neg (by simp), D.conj_val, ← hx']`. Use `(key x' ?_).symm` and prove the remaining obligations. Rewrite using `[hs, if_neg (by simp)]`. Conclude with `D.ntw.restX_coefficientEmbedding_conj _ _ _ (by rw [hx', star_star])`.

Rewrite using `[if_pos rfl]`. Conclude with `(key x (by rw [hs, if_pos rfl])).symm`.
-/
theorem liesUnder_of_tie (hG : IsGalois ℚ ↥D.LL0) {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) :
    LiesUnder D (c.twI w) (if c.sd w then w else D.what₂.places.conj w) := by
  intro x
  have hint : IsIntegral (D.ntw.O0 (c.twI w)) (D.ntw.emb0 (c.twI w) (x : ↥D.LL0)) :=
    (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (Int.castRingHom _) (D.ntw.emb0 (c.twI w))
      (RingHom.ext_int _ _)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hleft : (∃ y' ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y' = D.ntw.emb0 (c.twI w) (x : ↥D.LL0)) ↔ ¬ IsUnit y := by
    refine ⟨fun ⟨y', h1, h2⟩ => ?_, fun h1 => ⟨y, h1, hy⟩⟩
    rw [← IsFractionRing.injective _ _ (h2.trans hy.symm)]
    exact h1
  have key : ∀ x' : ↥D.LL0, (if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x' =
      D.ntw.emb0 (c.twI w) (x : ↥D.LL0) → (0 < D.what₂.places.val w (x' : D.what₂.LL) ↔ ¬ IsUnit y) := by
    intro x' hx'
    have e := h.embedding_baseField_condition w x' y 1 one_ne_zero (by rw [hx', map_one, mul_one, hy])
    simp only [map_one, mul_one] at e
    rw [pos_iff_not_isUnit c w _ _ e, not_iff_not]
    exact ⟨isUnit_of_toOe c w y, fun hu => ((hu.map _).map _).map _⟩
  rw [hleft]
  cases hs : c.sd w
  · obtain ⟨x', hx'⟩ := exists_star hG (x : ↥D.LL0)
    rw [if_neg (by simp), D.conj_val, ← hx']
    refine (key x' ?_).symm
    rw [hs, if_neg (by simp)]
    exact D.ntw.restX_coefficientEmbedding_conj _ _ _ (by rw [hx', star_star])
  · rw [if_pos rfl]
    exact (key x (by rw [hs, if_pos rfl])).symm

/- English proof (translation)
Introduce `w _`. Use `liesUnder_of_tie hG h w` as an intermediate fact. Use `split_ifs at this`. Use `exacts [Or.inl this, Or.inr this]`.
-/
theorem atPlace_of_tie (hG : IsGalois ℚ ↥D.LL0) {c : NChoice D} (h : NChTie D c) : AtPlace (recorded c) := by
  intro w _
  have := liesUnder_of_tie hG h w
  split_ifs at this
  exacts [Or.inl this, Or.inr this]

/- English proof (translation)
Break down `h w hw with h1 | h1` into its components or cases. Use `exacts [⟨w, hw, h1⟩, ⟨_, (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj w).2 hw, h1⟩]`.
-/
theorem AtPlace.inW1 {t : D.what₂.places.Pl → TwDatum D} (h : AtPlace t) {w : D.what₂.places.Pl} (hw : Twisted D w) :
    D.ntw.NonzeroIndexPlace (t w).1 := by
  rcases h w hw with h1 | h1
  exacts [⟨w, hw, h1⟩, ⟨_, (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj w).2 hw, h1⟩]

def ExpRange (c : NChoice D) : Prop :=
  ∀ w, TwistedAt D w → ∀ lam : D.ntw.abelian₂ (c.twI w), ∃ s : ℤ, BlochKatoReduction.Gen.SOk D.ntw (c.twI w) lam s

def Eventually {eps : ℝ} (Fm : FamP eps) (P : ∀ x, Fm.x1 < x → Fm.Ix x → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), P x hx i

def TwGoodAll {eps : ℝ} (Fm : FamP eps) : Prop :=
  Eventually Fm fun x hx i => TwConjAt (Fm.D x i) (Fm.ex x hx i).nch ∧
    ∃ N0 S, TwGoodAllAt (Fm.ex x hx i).nch ⟨twE Fm x hx i, N0, S⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `h`. Use `⟨a, fun x e hx i => ?_⟩` and prove the remaining obligations. Take `⟨h1, N0, S, h2⟩` from `ha x e hx i`. Conclude with `⟨h1, N0, S, h2.twGoodAt⟩`.
-/
theorem TwGoodAll.twGood {eps : ℝ} {Fm : FamP eps} (h : TwGoodAll Fm) : TwGood Fm := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun x e hx i => ?_⟩
  obtain ⟨h1, N0, S, h2⟩ := ha x e hx i
  exact ⟨h1, N0, S, h2.twGoodAt⟩

def FamilyAvoidsFurtherPrimes {eps : ℝ} (Fm : FamP eps) : Prop := Eventually Fm fun x hx i => AvoidsFurtherPrimesAt (Fm.ex x hx i).nch

def FamSurplus {eps : ℝ} (Fm : FamP eps) : Prop :=
  Eventually Fm fun x hx i => (∃ N0, BlochKatoReduction.adm9 (Fm.D x i) N0) ∧
    (∀ w, TwistedAt (Fm.D x i) w → ConstantTermsFinite ((Fm.ex x hx i).nch.twI w)) ∧
    OnePerPair (recorded (Fm.ex x hx i).nch) ∧ DisjointPairs (recorded (Fm.ex x hx i).nch)

end GlobalTheory.TwistGoodCompare

end
