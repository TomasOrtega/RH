import Mathlib
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisedKeyInvariantRuleCharZeroStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyHouse

open Cardinal in

/- English proof (translation)
Set `F` to `FractionRing (MvPolynomial ℝ K)`. Set `L` to `AlgebraicClosure F`. Establish `hF : #F = 𝔠`. Establish `hK : #K ≤ 𝔠` using `Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum`. Rewrite using `[Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK, max_eq_left Cardinal.aleph0_le_continuum]`.

Establish `hL : #L = 𝔠`. Use `le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)` and prove the remaining obligations. Use `Algebra.IsAlgebraic.cardinalMk_le_max F L` as an intermediate fact. Rewrite `this` using `[hF, max_eq_left Cardinal.aleph0_le_continuum]`. Then use the resulting hypothesis. Set `j : K →+* L` to `(algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)`.

Establish `: CharZero L` using `(RingHom.charZero_iff j.injective).1 inferInstance`. Take `⟨e⟩` from `IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ) (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))`. Conclude with `⟨e.toRingHom.comp j⟩`.
-/
theorem nonempty_ringHom_complex (K : Type) [Field K] [CharZero K] [Countable K] : Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  have hF : #F = 𝔠 := by
    have hK : #K ≤ 𝔠 := Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK,
      max_eq_left Cardinal.aleph0_le_continuum]
  have hL : #L = 𝔠 := by
    refine le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)
    have := Algebra.IsAlgebraic.cardinalMk_le_max F L
    rwa [hF, max_eq_left Cardinal.aleph0_le_continuum] at this
  let j : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  have : CharZero L := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))
  exact ⟨e.toRingHom.comp j⟩

/- English proof (translation)
Take `⟨_, _, _, hg, _⟩` from `h`. Conclude with `hg`.
-/
theorem g_eq_of_keyPB {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (h : KeyPB x' x f) : x'.P.g = x.P.g := by
  obtain ⟨_, _, _, hg, _⟩ := h
  exact hg

def NormalValue (g n : ℕ) (κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ) : Prop :=
  ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c₀ : ℂ), x.P.g = g →
    charHalf x.P.g a b → c₀ ≠ 0 → Mx.det ≠ 0 → NormalAt x τ Mx a b c₀ → (κ ℂ x : ℂ) = (Mx.det ^ 4 / c₀ ^ 8) ^ n

/- English proof (translation)
Take `⟨K₀, x₀, hK₀, hx₀⟩` from `hD K x`. Establish `hg₀ : x₀.P.g = g` using `(g_eq_of_keyPB hx₀).symm.trans hx`. Take `⟨σ⟩` from `nonempty_ringHom_complex K₀`. Take `⟨y, hy⟩` from `exists_keyPB_ring x₀ σ`. Establish `hgy : y.P.g = g` using `(g_eq_of_keyPB hy).trans hg₀`.

Take `⟨⟨τ, Mx, a, b, c, hab, hc, hM, hN⟩, -⟩` from `KeyNormalExists.exists_normalAt hU y`. Establish `e : (κ ℂ y : ℂ) ^ n' = (κ' ℂ y : ℂ) ^ n`. Rewrite using `[hn y τ Mx a b c hgy hab hc hM hN, hn' y τ Mx a b c hgy hab hc hM hN, ← pow_mul, ← pow_mul, Nat.mul_comm]`. Rewrite `e` using `[h.2.1 K₀ ℂ σ x₀ y hg₀ hy, h'.2.1 K₀ ℂ σ x₀ y hg₀ hy, ← map_pow, ← map_pow]`. Rewrite using `[h.2.1 K₀ K _ x₀ x hg₀ hx₀, h'.2.1 K₀ K _ x₀ x hg₀ hx₀, ← map_pow, ← map_pow, σ.injective e]`.
-/
theorem pow_eq_pow (hU : ThetaUnifAV) (hD : KeyDesc) {g n n' M M' : ℕ}
    {κ κ' : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (h : KaRuleK g n M κ) (h' : KaRuleK g n' M' κ')
    (hn : NormalValue g n κ) (hn' : NormalValue g n' κ') (K : Type) [Field K] [CharZero K] (x : KeyIn K)
    (hx : x.P.g = g) : (κ K x : K) ^ n' = (κ' K x : K) ^ n := by
  obtain ⟨K₀, x₀, hK₀, hx₀⟩ := hD K x
  have hg₀ : x₀.P.g = g := (g_eq_of_keyPB hx₀).symm.trans hx
  obtain ⟨σ⟩ := nonempty_ringHom_complex K₀
  obtain ⟨y, hy⟩ := exists_keyPB_ring x₀ σ
  have hgy : y.P.g = g := (g_eq_of_keyPB hy).trans hg₀
  obtain ⟨⟨τ, Mx, a, b, c, hab, hc, hM, hN⟩, -⟩ := KeyNormalExists.exists_normalAt hU y
  have e : (κ ℂ y : ℂ) ^ n' = (κ' ℂ y : ℂ) ^ n := by
    rw [hn y τ Mx a b c hgy hab hc hM hN, hn' y τ Mx a b c hgy hab hc hM hN, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h.2.1 K₀ ℂ σ x₀ y hg₀ hy, h'.2.1 K₀ ℂ σ x₀ y hg₀ hy, ← map_pow, ← map_pow] at e
  rw [h.2.1 K₀ K _ x₀ x hg₀ hx₀, h'.2.1 K₀ K _ x₀ x hg₀ hx₀, ← map_pow, ← map_pow, σ.injective e]

/- English proof (translation)
Take `⟨r, rfl⟩` from `IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (K := K) (x := z) hn (h ▸ isIntegral_algebraMap)`. Rewrite `h` using `[← map_pow]`. Establish `hr : IsUnit (r ^ n)` using `(IsFractionRing.injective R K h) ▸ u.isUnit`. Take `⟨w, rfl⟩` from `(isUnit_pow_iff (Nat.one_le_iff_ne_zero.1 hn)).1 hr`. Conclude with `⟨w, rfl⟩`.
-/
theorem exists_unit_of_pow {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {z : K} {n : ℕ} (hn : 1 ≤ n) {u : Rˣ} (h : z ^ n = algebraMap R K u) :
    ∃ w : Rˣ, z = algebraMap R K w := by
  obtain ⟨r, rfl⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (K := K) (x := z) hn
    (h ▸ isIntegral_algebraMap)
  rw [← map_pow] at h
  have hr : IsUnit (r ^ n) := (IsFractionRing.injective R K h) ▸ u.isUnit
  obtain ⟨w, rfl⟩ := (isUnit_pow_iff (Nat.one_le_iff_ne_zero.1 hn)).1 hr
  exact ⟨w, rfl⟩

/- English proof (translation)
Set `k` to `IsLocalRing.ResidueField R`. Establish `key : ∀ m : ℕ, IsUnit (m : R) ↔ ¬ ringChar k ∣ m` using `fun m => by`. Rewrite using `[← ringChar.spec, ← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_natCast]`. Use `⟨ringChar k, (CharP.char_is_prime_or_zero k _).resolve_right fun h0 => ?_, fun m hm => (key m).2 hm⟩` and prove the remaining obligations. Rewrite `h` using `[key, not_not, h0, zero_dvd_iff]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_prime_of_not_isUnit {R : Type} [CommRing R] [IsLocalRing R] {M : ℕ} (hM : 1 ≤ M)
    (h : ¬ IsUnit (M : R)) : ∃ p : ℕ, p.Prime ∧ ∀ m : ℕ, ¬ p ∣ m → IsUnit (m : R) := by
  let k := IsLocalRing.ResidueField R
  have key : ∀ m : ℕ, IsUnit (m : R) ↔ ¬ ringChar k ∣ m := fun m => by
    rw [← ringChar.spec, ← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_natCast]
  refine ⟨ringChar k, (CharP.char_is_prime_or_zero k _).resolve_right fun h0 => ?_, fun m hm => (key m).2 hm⟩
  rw [key, not_not, h0, zero_dvd_iff] at h
  omega

/- English proof (translation)
Rewrite using `[← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective r hr), RingHom.mem_ker, map_natCast, Nat.cast_eq_zero]`. Use linear arithmetic over natural numbers and integers.
-/
theorem isUnit_of_surjective {R k : Type} [CommRing R] [IsLocalRing R] [Field k] [CharZero k] {r : R →+* k}
    (hr : Function.Surjective r) {M : ℕ} (hM : 1 ≤ M) : IsUnit (M : R) := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective r hr),
    RingHom.mem_ker, map_natCast, Nat.cast_eq_zero]
  omega

/- English proof (translation)
Introduce `hL hU hI hP hT hK hD`. Establish `hall : ∀ g p : ℕ, p.Prime → ∃ (n M : ℕ) (κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ), 1 ≤ n ∧ 1 ≤ M ∧ (1 ≤ g → ¬ p ∣ M ∧ KaRuleK g n M κ ∧ NormalValue g n κ)`. Introduce `g p hp`. Distinguish the cases in `hg : 1 ≤ g`. Take `⟨c, M, hc, hM, hpM, hr⟩` from `hK (2 * g) p (by omega) hp`.

Take `⟨κ, h₁, h₂⟩` from `GlobalTheory.T.exists_normalised_key_invariant_rule_char_zero hL hU hI hP hT g c M hg hr`. Conclude with `⟨2 * c, M, κ, by omega, hM, fun _ => ⟨hpM, h₁, h₂⟩⟩`. Conclude with `⟨1, 1, fun _ _ _ _ => 1, le_rfl, le_rfl, fun h => absurd h hg⟩`. Use `choose N M κ hN hM hκ using fun g => hall g 2 Nat.prime_two`. Use `⟨N, hN, fun K _ _ x => κ x.P.g K x, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `K _ _ P hg rig hr th hth v hv th' hth' v' hv' a Mx h₁`. Conclude with `(hκ P.g h₁).2.1.1 K P hg rig hr th hth v hv th' hth' v' hv' a Mx rfl`. Introduce `K K' _ _ _ _ f x x' hg h dsimp only`. Rewrite using `[show κ x'.P.g K' x' = κ x.P.g K' x' by rw [g_eq_of_keyPB h]]`. Conclude with `(hκ _ hg).2.1.2.1 K K' f x x' rfl h`.

Introduce `R K _ _ _ _ _ _ _ x xK hg h dsimp only`. Rewrite using `[show κ xK.P.g K xK = κ x.P.g K xK by rw [g_eq_of_keyPB h]]`. Take `⟨-, h₁, h₂⟩` from `hκ _ hg`. Distinguish the cases in `hu : IsUnit (M x.P.g : R)`. Take `⟨u, hu₁, hu₂⟩` from `h₁.2.2.1 R K x xK rfl hu h`.

Use `⟨u, hu₁, fun k _ _ r xk hr hk => ?_⟩` and prove the remaining obligations. Rewrite using `[show κ xk.P.g k xk = κ x.P.g k xk by rw [g_eq_of_keyPB hk]]`. Conclude with `hu₂ k r xk hr hk`. Take `⟨p, hp, hpu⟩` from `exists_prime_of_not_isUnit (hM _) hu`. Take `⟨n', M', κ', hn', -, h'⟩` from `hall x.P.g p hp`.

Take `⟨hpM, h₁', h₂'⟩` from `h' hg`. Take `⟨u, hu₁, -⟩` from `h₁'.2.2.1 R K x xK rfl (hpu _ hpM) h`. Establish `e` using `pow_eq_pow hU hD h₁ h₁' h₂ h₂' K xK (g_eq_of_keyPB h)`. Rewrite `e` using `[hu₁, ← map_pow, ← Units.val_pow_eq_pow_val u]`. Take `⟨w, hw⟩` from `exists_unit_of_pow hn' e`.

Conclude with `⟨w, hw, fun k _ _ r xk hr _ => absurd (isUnit_of_surjective hr (hM _)) hu⟩`. Introduce `x τ a b hg hab hx`. Use `(hκ _ hg).2.2 x τ 1 a b 1 rfl hab one_ne_zero (by simp) hx` as an intermediate fact. Apply `Units.ext` to reduce the goal to its premises. Simplify using `using this`.
-/
theorem keyRule_of_kaSt : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → Key.PhHoloStatement → GlobalTheory.TorusAlgebraic → KaSt → KeyDesc → ∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧ KeyRule N 1 charHalf := by
  intro hL hU hI hP hT hK hD
  have hall : ∀ g p : ℕ, p.Prime → ∃ (n M : ℕ) (κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ),
      1 ≤ n ∧ 1 ≤ M ∧ (1 ≤ g → ¬ p ∣ M ∧ KaRuleK g n M κ ∧ NormalValue g n κ) := by
    intro g p hp
    by_cases hg : 1 ≤ g
    · obtain ⟨c, M, hc, hM, hpM, hr⟩ := hK (2 * g) p (by omega) hp
      obtain ⟨κ, h₁, h₂⟩ := GlobalTheory.T.exists_normalised_key_invariant_rule_char_zero hL hU hI hP hT g c M hg hr
      exact ⟨2 * c, M, κ, by omega, hM, fun _ => ⟨hpM, h₁, h₂⟩⟩
    · exact ⟨1, 1, fun _ _ _ _ => 1, le_rfl, le_rfl, fun h => absurd h hg⟩
  choose N M κ hN hM hκ using fun g => hall g 2 Nat.prime_two
  refine ⟨N, hN, fun K _ _ x => κ x.P.g K x, ?_, ?_, ?_, ?_⟩
  · intro K _ _ P hg rig hr th hth v hv th' hth' v' hv' a Mx h₁
    exact (hκ P.g h₁).2.1.1 K P hg rig hr th hth v hv th' hth' v' hv' a Mx rfl
  · intro K K' _ _ _ _ f x x' hg h
    dsimp only
    rw [show κ x'.P.g K' x' = κ x.P.g K' x' by rw [g_eq_of_keyPB h]]
    exact (hκ _ hg).2.1.2.1 K K' f x x' rfl h
  · intro R K _ _ _ _ _ _ _ x xK hg h
    dsimp only
    rw [show κ xK.P.g K xK = κ x.P.g K xK by rw [g_eq_of_keyPB h]]
    obtain ⟨-, h₁, h₂⟩ := hκ _ hg
    by_cases hu : IsUnit (M x.P.g : R)
    · obtain ⟨u, hu₁, hu₂⟩ := h₁.2.2.1 R K x xK rfl hu h
      refine ⟨u, hu₁, fun k _ _ r xk hr hk => ?_⟩
      rw [show κ xk.P.g k xk = κ x.P.g k xk by rw [g_eq_of_keyPB hk]]
      exact hu₂ k r xk hr hk
    · obtain ⟨p, hp, hpu⟩ := exists_prime_of_not_isUnit (hM _) hu
      obtain ⟨n', M', κ', hn', -, h'⟩ := hall x.P.g p hp
      obtain ⟨hpM, h₁', h₂'⟩ := h' hg
      obtain ⟨u, hu₁, -⟩ := h₁'.2.2.1 R K x xK rfl (hpu _ hpM) h
      have e := pow_eq_pow hU hD h₁ h₁' h₂ h₂' K xK (g_eq_of_keyPB h)
      rw [hu₁, ← map_pow, ← Units.val_pow_eq_pow_val u] at e
      obtain ⟨w, hw⟩ := exists_unit_of_pow hn' e
      exact ⟨w, hw, fun k _ _ r xk hr _ => absurd (isUnit_of_surjective hr (hM _)) hu⟩
  · intro x τ a b hg hab hx
    have := (hκ _ hg).2.2 x τ 1 a b 1 rfl hab one_ne_zero (by simp) hx
    apply Units.ext
    simpa using this

end GlobalTheory.KeyHouse
