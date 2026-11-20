import Mathlib
import Formalism.GL3MeanSquares.CongruenceTorsion
import Formalism.GL3MeanSquares.HookFormulaTorsion.DifferenceStableUnderAction
import Formalism.GL3MeanSquares.HookFormulaTorsion.DifferentIdealConditions
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.TameInertiaTowers.TowerFieldFoundations

namespace Formalism.HermitianLattices.StabilizerLevels
namespace PfB

section S1
open NumberField IsDedekindDomain
open scoped TensorProduct

/- English proof (translation)
Introduce `F E _ _ _ _ _ k σ J h1 h2 h3 h4 U hU w g hg hgw hk hx`. Use `h F E k σ J h1 h2 h3 h4 U hU w g hg hgw hk ?_` and prove the remaining obligations. Introduce `x hxU`. Use `⟨0, fun i j => ?_⟩` and prove the remaining obligations. Simplify using `using hx x hxU i j`.
-/
theorem stabG_of_proG (h : StabLevelProG) : StabLevelG := by
  intro F E _ _ _ _ _ k σ J h1 h2 h3 h4 U hU w g hg hgw hk hx
  refine h F E k σ J h1 h2 h3 h4 U hU w g hg hgw hk ?_
  intro x hxU
  refine ⟨0, fun i j => ?_⟩
  simpa using hx x hxU i j

/- English proof (translation)
Introduce `R _ I g k hg hgI A hA s hs i j`. Set `π` to `Ideal.Quotient.mk I`. Set `φ` to `π.mapMatrix (m := Fin k)`. Set `N : Matrix (Fin k) (Fin k) (R ⧸ I)` to `φ (A - 1)`. Establish `hN0 : ∀ i j : Fin k, j ≤ i → N i j = 0` using `fun i j h => Ideal.Quotient.eq_zero_iff_mem.2 (hA i j h)`.

Establish `hpow : ∀ m : ℕ, ∀ i j : Fin k, (j : ℕ) < i + m → (N ^ m) i j = 0`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `i j h`.

Rewrite using `[pow_zero, Matrix.one_apply, if_neg]`. Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Consider the case `succ m ih`. Introduce `i j h`.

Rewrite using `[pow_succ, Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l _`. Distinguish the cases in `hl : (l : ℕ) < i + m`. Rewrite using `[ih i l hl, zero_mul]`.

Rewrite using `[hN0 l j (by rw [Fin.le_def]; omega), mul_zero]`. Establish `hAm : φ A = N + 1` using `by simp [N]`. Establish `hg0 : ((g : ℕ) : R ⧸ I) = 0`. Use `Ideal.Quotient.eq_zero_iff_mem.2 hgI` as an intermediate fact. Simplify using `using this`.

Establish `key : (φ A) ^ (g ^ s) = 1`. Rewrite using `[hAm, (Commute.one_right N).add_pow, Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `m hm hm0`. Rewrite `hm` using `[Finset.mem_range]`.

Distinguish the cases in `hmm : m = g ^ s`. Establish `: N ^ m = 0`. Use extensionality with `a b`. Conclude with `hpow m a b (by have := b.2; omega)`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Establish `hd : g ∣ (g ^ s).choose m` using `hg.dvd_choose_pow hm0 hmm`. Take `⟨c, hc⟩` from `hd`. Establish `: (((g ^ s).choose m : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I)) = 0`. Rewrite using `[hc, Nat.cast_mul]`.

Establish `: ((g : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I)) = 0`. Use extensionality with `a b`. Simplify using `[Matrix.natCast_apply, hg0]`. Rewrite using `[this, zero_mul]`. Rewrite using `[this, mul_zero]`.

Introduce `h`. Simplify using `at h`. Establish `: φ (A ^ (g ^ s) - 1) = 0` using `by rw [map_sub, map_pow, key, map_one, sub_self]`. Establish `h2` using `congrFun (congrFun this i) j`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h2`.
-/
theorem unipotentPowers : UnipotentPowers := by
  intro R _ I g k hg hgI A hA s hs i j
  let π := Ideal.Quotient.mk I
  let φ := π.mapMatrix (m := Fin k)
  let N : Matrix (Fin k) (Fin k) (R ⧸ I) := φ (A - 1)
  have hN0 : ∀ i j : Fin k, j ≤ i → N i j = 0 := fun i j h =>
    Ideal.Quotient.eq_zero_iff_mem.2 (hA i j h)
  have hpow : ∀ m : ℕ, ∀ i j : Fin k, (j : ℕ) < i + m → (N ^ m) i j = 0 := by
    intro m
    induction m with
    | zero =>
      intro i j h
      rw [pow_zero, Matrix.one_apply, if_neg]
      rintro rfl
      omega
    | succ m ih =>
      intro i j h
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : (l : ℕ) < i + m
      · rw [ih i l hl, zero_mul]
      · rw [hN0 l j (by rw [Fin.le_def]; omega), mul_zero]
  have hAm : φ A = N + 1 := by simp [N]
  have hg0 : ((g : ℕ) : R ⧸ I) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 hgI
    simpa using this
  have key : (φ A) ^ (g ^ s) = 1 := by
    rw [hAm, (Commute.one_right N).add_pow, Finset.sum_eq_single 0]
    · simp
    · intro m hm hm0
      rw [Finset.mem_range] at hm
      by_cases hmm : m = g ^ s
      · have : N ^ m = 0 := by
          ext a b
          exact hpow m a b (by have := b.2; omega)
        rw [this]; simp
      · have hd : g ∣ (g ^ s).choose m := hg.dvd_choose_pow hm0 hmm
        obtain ⟨c, hc⟩ := hd
        have : (((g ^ s).choose m : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I)) = 0 := by
          rw [hc, Nat.cast_mul]
          have : ((g : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I)) = 0 := by
            ext a b
            simp [Matrix.natCast_apply, hg0]
          rw [this, zero_mul]
        rw [this, mul_zero]
    · intro h; simp at h
  have : φ (A ^ (g ^ s) - 1) = 0 := by rw [map_sub, map_pow, key, map_one, sub_self]
  have h2 := congrFun (congrFun this i) j
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2

/- English proof (translation)
Introduce `R _ I g k hg hgI hinf A hA N hN hAN`. Take `⟨s, N', hN', hNe⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hN.ne' g hg.ne_one`. Use `⟨s, ?_⟩` and prove the remaining obligations. Use `set Bm := A ^ (g ^ s) with hB`. Establish `hBN : Bm ^ N' = 1` using `by rw [hB, ← pow_mul, ← hNe, hAN]`.

Establish `hB1 : ∀ i j, (Bm - 1) i j ∈ I` using `fun i j => Ideal.pow_le_self (Nat.succ_ne_zero s) (Formalism.HermitianLattices.FiltrationBoundaryCriterion.congruence_powers R I g k hgI A hA s i j)`. Establish `hcop : Nat.Coprime g N'` using `(Nat.Prime.coprime_iff_not_dvd hg).2 hN'`. Establish `hN'0 : 0 < N'` using `Nat.pos_of_ne_zero (by rintro rfl; exact hN' (dvd_zero _))`. Establish `hfix : ∀ m : ℕ, Bm ^ (g ^ (N'.totient * m)) = Bm`. Introduce `m`.

Establish `h1 : g ^ (N'.totient * m) ≡ 1 [MOD N']`. Rewrite using `[pow_mul]`. Simplify using `using (Nat.ModEq.pow_totient hcop).pow m`. Rewrite using `[pow_eq_pow_mod _ hBN, h1, ← pow_eq_pow_mod _ hBN, pow_one]`. Establish `hz : ∀ i j, (Bm - 1) i j = 0`.

Introduce `i j`. Establish `: (Bm - 1) i j ∈ (⨅ m : ℕ, I ^ m)`. Rewrite using `[Ideal.mem_iInf]`. Introduce `m`. Establish `h` using `Formalism.HermitianLattices.FiltrationBoundaryCriterion.congruence_powers R I g k hgI Bm hB1 (N'.totient * m) i j`.

Rewrite `h` using `[hfix m]`. Use `Ideal.pow_le_pow_right ?_ h` and prove the remaining obligations. Use `Nat.totient_pos.2 hN'0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite `this` using `[hinf]`.

Simplify using `using this`. Establish `: Bm - 1 = 0` using `by ext i j; exact hz i j`. Conclude with `sub_eq_zero.1 this`.
-/
theorem congruenceTorsion : CongruenceTorsion := by
  intro R _ I g k hg hgI hinf A hA N hN hAN
  obtain ⟨s, N', hN', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' g hg.ne_one
  refine ⟨s, ?_⟩
  set Bm := A ^ (g ^ s) with hB
  have hBN : Bm ^ N' = 1 := by rw [hB, ← pow_mul, ← hNe, hAN]
  have hB1 : ∀ i j, (Bm - 1) i j ∈ I := fun i j =>
    Ideal.pow_le_self (Nat.succ_ne_zero s) (Formalism.HermitianLattices.FiltrationBoundaryCriterion.congruence_powers R I g k hgI A hA s i j)
  have hcop : Nat.Coprime g N' := (Nat.Prime.coprime_iff_not_dvd hg).2 hN'
  have hN'0 : 0 < N' := Nat.pos_of_ne_zero (by rintro rfl; exact hN' (dvd_zero _))
  have hfix : ∀ m : ℕ, Bm ^ (g ^ (N'.totient * m)) = Bm := by
    intro m
    have h1 : g ^ (N'.totient * m) ≡ 1 [MOD N'] := by
      rw [pow_mul]
      simpa using (Nat.ModEq.pow_totient hcop).pow m
    rw [pow_eq_pow_mod _ hBN, h1, ← pow_eq_pow_mod _ hBN, pow_one]
  have hz : ∀ i j, (Bm - 1) i j = 0 := by
    intro i j
    have : (Bm - 1) i j ∈ (⨅ m : ℕ, I ^ m) := by
      rw [Ideal.mem_iInf]
      intro m
      have h := Formalism.HermitianLattices.FiltrationBoundaryCriterion.congruence_powers R I g k hgI Bm hB1 (N'.totient * m) i j
      rw [hfix m] at h
      refine Ideal.pow_le_pow_right ?_ h
      have := Nat.totient_pos.2 hN'0
      nlinarith
    rw [hinf] at this
    simpa using this
  have : Bm - 1 = 0 := by ext i j; exact hz i j
  exact sub_eq_zero.1 this

section sep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (w : HeightOneSpectrum (𝓞 F))

noncomputable def owHom :
    (w.adicCompletionIntegers F) →+* E ⊗[F] w.adicCompletion F :=
  (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := w.adicCompletion F)).toRingHom.comp
    (w.adicCompletionIntegers F).subtype

local notation "O" => (HeightOneSpectrum.adicCompletionIntegers F w)

/- English proof (translation)
Set `_ : Algebra (w.adicCompletionIntegers F) (E ⊗[F] w.adicCompletion F)` to `(owHom (E := E) w).toAlgebra`. Set `ι : 𝓞 E →+* E ⊗[F] w.adicCompletion F` to `(Formalism.UG.inclE (F := F) (E := E) (w.adicCompletion F)).comp (algebraMap (𝓞 E) E)`. Set `bs` to `NumberField.RingOfIntegers.basis E`. Set `s : Set (E ⊗[F] w.adicCompletion F)` to `Set.range (fun i => ι (bs i))`. Establish `hsfin : s.Finite` using `Set.finite_range _`.

Establish `hint : ∀ x ∈ s, IsIntegral O x`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `h1 : IsIntegral ℤ (bs i)` using `Algebra.IsIntegral.isIntegral _`. Conclude with `h1.map_of_comp_eq (Int.castRingHom O) ι (RingHom.ext_int _ _)`. Establish `hfg` using `fg_adjoin_of_finite hsfin hint`.

Set `A` to `Algebra.adjoin O s`. Establish `: Module.Finite O A` using `Module.Finite.iff_fg.2 hfg`. Establish `hιA : ∀ x : 𝓞 E, ι x ∈ A`. Introduce `x`. Rewrite using `[← bs.sum_repr x, map_sum]`.

Use `Subalgebra.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[zsmul_eq_mul, map_mul, map_intCast]`. Conclude with `A.mul_mem (intCast_mem A _) (Algebra.subset_adjoin ⟨i, rfl⟩)`. Use `⟨A.toSubring, ?_, ?_⟩` and prove the remaining obligations. Unfold `Formalism.UG.tensInt`.

Rewrite using `[Subring.closure_le]`. Introduce and unpack `_ (⟨⟨_, ⟨x, rfl⟩⟩, rfl⟩ | ⟨y, rfl⟩)`. Conclude with `hιA x`. Conclude with `A.algebraMap_mem (⟨y.1, y.2⟩ : O)`. Establish `hg : (g : O) ∈ IsLocalRing.maximalIdeal O`.

Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Take `⟨u, hu⟩` from `hu.exists_right_inv`. Establish `h1 : Valued.v ((g : w.adicCompletion F)) * Valued.v (u : w.adicCompletion F) = 1`. Rewrite using `[← map_mul]`.

Use `congrArg (fun z : O => (z : w.adicCompletion F)) hu` as an intermediate fact. Simplify using `only [MulMemClass.coe_mul, OneMemClass.coe_one] at this`. Establish `e : (((g : O)) : w.adicCompletion F) = (g : w.adicCompletion F)` using `by simp`. Rewrite `this` using `[e]`. Rewrite using `[this, map_one]`.

Establish `h2 : Valued.v ((g : w.adicCompletion F)) < 1`. Establish `e : (g : w.adicCompletion F) = ((algebraMap (𝓞 F) F (g : 𝓞 F) : F) : w.adicCompletion F)`. Rewrite using `[map_natCast]`. Conclude with `(map_natCast (algebraMap F (w.adicCompletion F)) g).symm`. Rewrite using `[e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_lt_one_iff_mem]`.

Conclude with `hgw`. Establish `h3 : Valued.v (u : w.adicCompletion F) ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 u.2`. Establish `h4 : Valued.v ((g : w.adicCompletion F)) * Valued.v (u : w.adicCompletion F) < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right' h3) h2`. Rewrite `h4` using `[h1]`. Conclude with `lt_irrefl _ h4`.

Establish `hne : Ideal.span {(g : O)} ≠ ⊤`. Introduce `h`. Establish `: Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hg`.

Rewrite `this` using `[h]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal O).ne_top (top_le_iff.1 this)`. Establish `hK` using `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A) (Ideal.span {(g : O)}) hne`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`.

Rewrite `hx` using `[Ideal.mem_iInf]`. Establish `: (⟨x.1, x.2⟩ : A) ∈ (⨅ i : ℕ, (Ideal.span {(g : O)}) ^ i • (⊤ : Submodule O A))`. Rewrite using `[Submodule.mem_iInf]`. Introduce `m`. Establish `h1` using `hx m`.

Rewrite `h1` using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Take `⟨a, ha⟩` from `h1`. Establish `: (⟨x.1, x.2⟩ : A) = ((g : O) ^ m) • (⟨a.1, a.2⟩ : A)`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `e` using `congrArg Subtype.val ha`.

Use `show x.1 = ((g : O) ^ m) • a.1`. Rewrite using `[Algebra.smul_def]`. Use `show x.1 = owHom (E := E) w ((g : O) ^ m) * a.1`. Rewrite using `[map_pow, map_natCast, ← e]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) m) trivial`. Rewrite `this` using `[hK]`. Simplify using `using this`.
-/
theorem sepLemma (g : ℕ) (hgw : (g : 𝓞 F) ∈ w.asIdeal) :
    ∃ (A : Subring (E ⊗[F] w.adicCompletion F)),
      Formalism.UG.tensInt (F := F) (w.adicCompletion F) (Formalism.UG.intOE E)
        (w.adicCompletionIntegers F).toSubring ≤ A ∧
      (⨅ m : ℕ, (Ideal.span {(g : A)}) ^ m) = ⊥ := by
  classical
  let _ : Algebra (w.adicCompletionIntegers F) (E ⊗[F] w.adicCompletion F) := (owHom (E := E) w).toAlgebra
  let ι : 𝓞 E →+* E ⊗[F] w.adicCompletion F := (Formalism.UG.inclE (F := F) (E := E) (w.adicCompletion F)).comp (algebraMap (𝓞 E) E)
  let bs := NumberField.RingOfIntegers.basis E
  let s : Set (E ⊗[F] w.adicCompletion F) := Set.range (fun i => ι (bs i))
  have hsfin : s.Finite := Set.finite_range _
  have hint : ∀ x ∈ s, IsIntegral O x := by
    rintro _ ⟨i, rfl⟩
    have h1 : IsIntegral ℤ (bs i) := Algebra.IsIntegral.isIntegral _
    exact h1.map_of_comp_eq (Int.castRingHom O) ι (RingHom.ext_int _ _)
  have hfg := fg_adjoin_of_finite hsfin hint
  let A := Algebra.adjoin O s
  have : Module.Finite O A := Module.Finite.iff_fg.2 hfg
  have hιA : ∀ x : 𝓞 E, ι x ∈ A := by
    intro x
    rw [← bs.sum_repr x, map_sum]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    rw [zsmul_eq_mul, map_mul, map_intCast]
    exact A.mul_mem (intCast_mem A _) (Algebra.subset_adjoin ⟨i, rfl⟩)
  refine ⟨A.toSubring, ?_, ?_⟩
  · unfold Formalism.UG.tensInt
    rw [Subring.closure_le]
    rintro _ (⟨⟨_, ⟨x, rfl⟩⟩, rfl⟩ | ⟨y, rfl⟩)
    · exact hιA x
    · exact A.algebraMap_mem (⟨y.1, y.2⟩ : O)
  · have hg : (g : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu⟩ := hu.exists_right_inv
      have h1 : Valued.v ((g : w.adicCompletion F)) * Valued.v (u : w.adicCompletion F) = 1 := by
        rw [← map_mul]
        have := congrArg (fun z : O => (z : w.adicCompletion F)) hu
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
        have e : (((g : O)) : w.adicCompletion F) = (g : w.adicCompletion F) := by simp
        rw [e] at this
        rw [this, map_one]
      have h2 : Valued.v ((g : w.adicCompletion F)) < 1 := by
        have e : (g : w.adicCompletion F) = ((algebraMap (𝓞 F) F (g : 𝓞 F) : F) : w.adicCompletion F) := by
          rw [map_natCast]
          exact (map_natCast (algebraMap F (w.adicCompletion F)) g).symm
        rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_lt_one_iff_mem]
        exact hgw
      have h3 : Valued.v (u : w.adicCompletion F) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 u.2
      have h4 : Valued.v ((g : w.adicCompletion F)) * Valued.v (u : w.adicCompletion F) < 1 :=
        lt_of_le_of_lt (mul_le_of_le_one_right' h3) h2
      rw [h1] at h4
      exact lt_irrefl _ h4
    have hne : Ideal.span {(g : O)} ≠ ⊤ := by
      intro h
      have : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O := by
        rw [Ideal.span_le, Set.singleton_subset_iff]; exact hg
      rw [h] at this
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top (top_le_iff.1 this)
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A) (Ideal.span {(g : O)}) hne
    rw [eq_bot_iff]
    intro x hx
    rw [Ideal.mem_iInf] at hx
    have : (⟨x.1, x.2⟩ : A) ∈ (⨅ i : ℕ, (Ideal.span {(g : O)}) ^ i • (⊤ : Submodule O A)) := by
      rw [Submodule.mem_iInf]
      intro m
      have h1 := hx m
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h1
      obtain ⟨a, ha⟩ := h1
      have : (⟨x.1, x.2⟩ : A) = ((g : O) ^ m) • (⟨a.1, a.2⟩ : A) := by
        apply Subtype.ext
        have e := congrArg Subtype.val ha
        show x.1 = ((g : O) ^ m) • a.1
        rw [Algebra.smul_def]
        show x.1 = owHom (E := E) w ((g : O) ^ m) * a.1
        rw [map_pow, map_natCast, ← e]
        push_cast
        ring
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) m) trivial
    rw [hK] at this
    simpa using this

end sep

section main
open Formalism.HermitianLattices.FiltrationBoundaryCriterion

/- English proof (translation)
Introduce `F E _ _ _ _ _ k σ J hσ hH hdet hdef U hU w g hg hgw hk hUw y`. Establish `hfinS` using `Formalism.UG.Final.AdelicStabFinite F E (Fin k) σ J hσ hH hdet hdef y`. Apply `Set.eq_singleton_iff_unique_mem.2` to reduce the goal to its premises. Use `⟨by simp [Formalism.UG.stabAt], ?_⟩` and prove the remaining obligations. Introduce `γ hγ`.

Establish `hγ' : y⁻¹ * (γ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y ∈ U.subgroupOf (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F))` using `hγ`. Establish `hfo : IsOfFinOrder γ`. Rewrite using `[← finite_powers]`. Use `Set.Finite.subset (Set.finite_coe_iff.1 hfinS) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, rfl⟩`.

Use `show y⁻¹ * ((γ ^ n : _) : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y ∈ (Formalism.UG.levelAf σ J).subgroupOf (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F))`. Establish `e1 : y⁻¹ * ((γ ^ n : _) : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y = (y⁻¹ * (γ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y) ^ n`. Use `conj_pow (a := y⁻¹) (b := (γ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F))) (i := n)` as an intermediate fact. Simplify using `using this.symm`. Rewrite using `[e1]`.

Use `Subgroup.pow_mem _ hγ' n` as an intermediate fact. Conclude with `Subgroup.mem_subgroupOf.2 (hU (Subgroup.mem_subgroupOf.1 this))`. Take `⟨γ₀, hγ₀, hγ₀eq⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)`. Establish `hinj` using `Formalism.UG.Final.InclInj F E (Fin k) (w.adicCompletion F) inferInstance`. Take `⟨n, hn, hγn⟩` from `isOfFinOrder_iff_pow_eq_one.1 hfo`.

Establish `h0n : γ₀ ^ n = 1`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_one, map_pow, ← PfM.bc_pr_incl, hγ₀eq]`. Use `congrArg (fun z => Formalism.UG.bc (Formalism.UG.prV (E := E) w) ((z : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) : Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (congrArg Subtype.val hγn)` as an intermediate fact. Simplify using `using this`.

Establish `hfo0 : IsOfFinOrder γ₀` using `isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, h0n⟩`. Take `⟨s, hx⟩` from `hUw _ (Subgroup.mem_subgroupOf.1 hγ')`. Use `set yw := Formalism.UG.bc (Formalism.UG.prV (E := E) w) (y : Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) with hyw`. Establish `hxw : Formalism.UG.bc (Formalism.UG.prV (E` using `E) w) ((y⁻¹ * (γ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) : Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = yw⁻¹ * Formalism.UG.bc (Formalism.UG.inclE (F := F) (w.adicCompletion F)) γ₀ * yw := …`. Rewrite using `[← PfM.bc_pr_incl, hγ₀eq]`.

Simplify using `[hyw]`. Rewrite `hx` using `[hxw]`. Use `set X := yw⁻¹ * Formalism.UG.bc (Formalism.UG.inclE (F := F) (w.adicCompletion F)) γ₀ * yw with hX`. Establish `hord : orderOf X = orderOf γ₀`. Establish `h1` using `orderOf_injective ((MulAut.conj yw⁻¹).toMonoidHom.comp (Formalism.UG.bc (Formalism.UG.inclE (F := F) (w.adicCompletion F)))) ((MulAut.conj yw⁻¹).injective.comp hinj) γ₀`.

Simplify `h1` using `[MulAut.conj_apply]`. Establish `hXn : X ^ n = 1`. Rewrite using `[← orderOf_dvd_iff_pow_eq_one, hord, orderOf_dvd_iff_pow_eq_one]`. Conclude with `h0n`. Take `⟨A, hRA, hsep⟩` from `sepLemma (E := E) w g hgw`.

Use `choose r hr hr' using hx`. Set `B : Matrix (Fin k) (Fin k) A` to `fun i j => (1 : Matrix (Fin k) (Fin k) A) i j + (g : A) * ⟨r i j, hRA (hr i j)⟩`. Establish `hB : B.map A.subtype = (X : Matrix (Fin k) (Fin k) (E ⊗[F] w.adicCompletion F)) ^ (g ^ s)`. Use extensionality with `i j`. Use `hr' i j` as an intermediate fact.

Rewrite `this` using `[sub_eq_iff_eq_add]`. Rewrite using `[this]`. Use `show (((1 : Matrix (Fin k) (Fin k) A) i j + (g : A) * ⟨r i j, hRA (hr i j)⟩ : A) : E ⊗[F] w.adicCompletion F) = _`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `[add_comm]`. Simplify using `[hij]`. Establish `hinjA : Function.Injective (A.subtype.mapMatrix (m` using `Fin k)) := by`. Introduce `M N hMN`. Use extensionality with `i j`.

Conclude with `congrFun (congrFun hMN i) j`. Establish `hBn : B ^ n = 1`. Apply `hinjA` to reduce the goal to its premises. Rewrite using `[map_pow, map_one]`. Use `show (B.map A.subtype) ^ n = 1`.

Rewrite using `[hB, ← pow_mul, mul_comm, pow_mul]`. Use `congrArg (fun z : Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] w.adicCompletion F) => (z : Matrix (Fin k) (Fin k) (E ⊗[F] w.adicCompletion F))) hXn` as an intermediate fact. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_one] at this`. Rewrite using `[this, one_pow]`. Take `⟨m, hm⟩` from `congruenceTorsion A (Ideal.span {(g : A)}) g k hg (Ideal.mem_span_singleton_self _) hsep B (fun i j => by`.

Establish `e : (B - 1) i j = (g : A) * ⟨r i j, hRA (hr i j)⟩` using `by show ((1 : Matrix (Fin k) (Fin k) A) i j + (g : A) * ⟨r i j, hRA (hr i j)⟩) - (1 : Matrix (Fin k) (Fin k) A) i j = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ (Ideal.span {(g : A)}) (Ideal.mem_span_singleton_self (g : A))) n hn hBn`. Establish `hXg : X ^ (g ^ (s + m)) = 1`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, pow_add, pow_mul, ← hB]`. Use `congrArg (A.subtype.mapMatrix (m := Fin k)) hm` as an intermediate fact. Rewrite `this` using `[map_pow, map_one]`. Conclude with `this`.

Take `⟨t, -, ht⟩` from `(Nat.dvd_prime_pow hg).1 (orderOf_dvd_of_pow_eq_one hXg)`. Rewrite `ht` using `[hord]`. Establish `hbot` using `Formalism.BehrendSets.FinalE.trivStab E k g hg hk (Subgroup.zpowers γ₀) (Set.finite_coe_iff.2 (finite_zpowers.2 hfo0)) (IsPGroup.of_card (n := t) (by rw [Nat.card_zpowers, ht]))`. Establish `h1 : γ₀ = 1` using `Subgroup.zpowers_eq_bot.1 hbot`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hγ₀eq, h1]`. Simplify using the standard rewrite rules.
-/
theorem stabLevelProG : StabLevelProG := by
  intro F E _ _ _ _ _ k σ J hσ hH hdet hdef U hU w g hg hgw hk hUw y
  classical
  have hfinS := Formalism.UG.Final.AdelicStabFinite F E (Fin k) σ J hσ hH hdet hdef y
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨by simp [Formalism.UG.stabAt], ?_⟩
  intro γ hγ
  have hγ' : y⁻¹ * (γ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y ∈
      U.subgroupOf (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) := hγ
  have hfo : IsOfFinOrder γ := by
    rw [← finite_powers]
    refine Set.Finite.subset (Set.finite_coe_iff.1 hfinS) ?_
    rintro _ ⟨n, rfl⟩
    show y⁻¹ * ((γ ^ n : _) : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y ∈
      (Formalism.UG.levelAf σ J).subgroupOf (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F))
    have e1 : y⁻¹ * ((γ ^ n : _) : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y =
        (y⁻¹ * (γ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y) ^ n := by
      have := conj_pow (a := y⁻¹) (b := (γ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F))) (i := n)
      simpa using this.symm
    rw [e1]
    have := Subgroup.pow_mem _ hγ' n
    exact Subgroup.mem_subgroupOf.2 (hU (Subgroup.mem_subgroupOf.1 this))
  obtain ⟨γ₀, hγ₀, hγ₀eq⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  have hinj := Formalism.UG.Final.InclInj F E (Fin k) (w.adicCompletion F) inferInstance
  obtain ⟨n, hn, hγn⟩ := isOfFinOrder_iff_pow_eq_one.1 hfo
  have h0n : γ₀ ^ n = 1 := by
    apply hinj
    rw [map_one, map_pow, ← PfM.bc_pr_incl, hγ₀eq]
    have := congrArg (fun z => Formalism.UG.bc (Formalism.UG.prV (E := E) w)
      ((z : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
        Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (congrArg Subtype.val hγn)
    simpa using this
  have hfo0 : IsOfFinOrder γ₀ := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, h0n⟩
  obtain ⟨s, hx⟩ := hUw _ (Subgroup.mem_subgroupOf.1 hγ')
  set yw := Formalism.UG.bc (Formalism.UG.prV (E := E) w)
    (y : Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) with hyw
  have hxw : Formalism.UG.bc (Formalism.UG.prV (E := E) w)
      ((y⁻¹ * (γ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y :
        Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
        Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      yw⁻¹ * Formalism.UG.bc (Formalism.UG.inclE (F := F) (w.adicCompletion F)) γ₀ * yw := by
    rw [← PfM.bc_pr_incl, hγ₀eq]
    simp [hyw]
  rw [hxw] at hx
  set X := yw⁻¹ * Formalism.UG.bc (Formalism.UG.inclE (F := F) (w.adicCompletion F)) γ₀ * yw with hX
  have hord : orderOf X = orderOf γ₀ := by
    have h1 := orderOf_injective
      ((MulAut.conj yw⁻¹).toMonoidHom.comp (Formalism.UG.bc (Formalism.UG.inclE (F := F) (w.adicCompletion F))))
      ((MulAut.conj yw⁻¹).injective.comp hinj) γ₀
    simpa [MulAut.conj_apply] using h1
  have hXn : X ^ n = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hord, orderOf_dvd_iff_pow_eq_one]; exact h0n

  obtain ⟨A, hRA, hsep⟩ := sepLemma (E := E) w g hgw
  choose r hr hr' using hx
  let B : Matrix (Fin k) (Fin k) A := fun i j => (1 : Matrix (Fin k) (Fin k) A) i j + (g : A) * ⟨r i j, hRA (hr i j)⟩
  have hB : B.map A.subtype = (X : Matrix (Fin k) (Fin k) (E ⊗[F] w.adicCompletion F)) ^ (g ^ s) := by
    ext i j
    have := hr' i j
    rw [sub_eq_iff_eq_add] at this
    rw [this]
    show (((1 : Matrix (Fin k) (Fin k) A) i j + (g : A) * ⟨r i j, hRA (hr i j)⟩ : A) :
      E ⊗[F] w.adicCompletion F) = _
    by_cases hij : i = j
    · subst hij; simp [add_comm]
    · simp [hij]
  have hinjA : Function.Injective (A.subtype.mapMatrix (m := Fin k)) := by
    intro M N hMN
    ext i j
    exact congrFun (congrFun hMN i) j
  have hBn : B ^ n = 1 := by
    apply hinjA
    rw [map_pow, map_one]
    show (B.map A.subtype) ^ n = 1
    rw [hB, ← pow_mul, mul_comm, pow_mul]
    have := congrArg (fun z : Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] w.adicCompletion F) =>
      (z : Matrix (Fin k) (Fin k) (E ⊗[F] w.adicCompletion F))) hXn
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [this, one_pow]
  obtain ⟨m, hm⟩ := congruenceTorsion A (Ideal.span {(g : A)}) g k hg (Ideal.mem_span_singleton_self _) hsep B
    (fun i j => by
      have e : (B - 1) i j = (g : A) * ⟨r i j, hRA (hr i j)⟩ := by
        show ((1 : Matrix (Fin k) (Fin k) A) i j + (g : A) * ⟨r i j, hRA (hr i j)⟩) -
          (1 : Matrix (Fin k) (Fin k) A) i j = _
        ring
      rw [e]
      exact Ideal.mul_mem_right _ (Ideal.span {(g : A)}) (Ideal.mem_span_singleton_self (g : A))) n hn hBn
  have hXg : X ^ (g ^ (s + m)) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_add, pow_mul, ← hB]
    have := congrArg (A.subtype.mapMatrix (m := Fin k)) hm
    rw [map_pow, map_one] at this
    exact this
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow hg).1 (orderOf_dvd_of_pow_eq_one hXg)
  rw [hord] at ht
  have hbot := Formalism.BehrendSets.FinalE.trivStab E k g hg hk (Subgroup.zpowers γ₀)
    (Set.finite_coe_iff.2 (finite_zpowers.2 hfo0))
    (IsPGroup.of_card (n := t) (by rw [Nat.card_zpowers, ht]))
  have h1 : γ₀ = 1 := Subgroup.zpowers_eq_bot.1 hbot
  apply Subtype.ext
  apply Subtype.ext
  rw [← hγ₀eq, h1]
  simp

end main

/- English proof (translation)
Introduce `R _ I g k hg hgI A M hA s hs i j`. Set `π` to `Ideal.Quotient.mk I`. Set `φ` to `π.mapMatrix (m := Fin k)`. Set `N : Matrix (Fin k) (Fin k) (R ⧸ I)` to `φ (A - 1)`. Establish `hNM : N ^ M = 0`.

Use extensionality with `a b`. Establish `: N ^ M = φ ((A - 1) ^ M)` using `by simp [N]`. Rewrite using `[this]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hA a b)`. Establish `hAm : φ A = N + 1` using `by simp [N]`.

Establish `hg0 : ((g : ℕ) : R ⧸ I) = 0`. Use `Ideal.Quotient.eq_zero_iff_mem.2 hgI` as an intermediate fact. Simplify using `using this`. Establish `key : (φ A) ^ (g ^ s) = 1`. Rewrite using `[hAm, (Commute.one_right N).add_pow, Finset.sum_eq_single 0]`.

Simplify using the standard rewrite rules. Introduce `m hm hm0`. Rewrite `hm` using `[Finset.mem_range]`. Distinguish the cases in `hmm : m = g ^ s`. Establish `: N ^ m = 0`.

Rewrite using `[hmm]`. Conclude with `pow_eq_zero_of_le hs hNM`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `hd : g ∣ (g ^ s).choose m` using `hg.dvd_choose_pow hm0 hmm`.

Take `⟨c, hc⟩` from `hd`. Establish `: (((g ^ s).choose m : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I)) = 0`. Rewrite using `[hc, Nat.cast_mul]`. Establish `: ((g : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I)) = 0`. Use extensionality with `a b`.

Simplify using `[Matrix.natCast_apply, hg0]`. Rewrite using `[this, zero_mul]`. Rewrite using `[this, mul_zero]`. Introduce `h`. Simplify using `at h`.

Establish `: φ (A ^ (g ^ s) - 1) = 0` using `by rw [map_sub, map_pow, key, map_one, sub_self]`. Establish `h2` using `congrFun (congrFun this i) j`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h2`.
-/
theorem nilpotentPowers : NilpotentPowers := by
  intro R _ I g k hg hgI A M hA s hs i j
  let π := Ideal.Quotient.mk I
  let φ := π.mapMatrix (m := Fin k)
  let N : Matrix (Fin k) (Fin k) (R ⧸ I) := φ (A - 1)
  have hNM : N ^ M = 0 := by
    ext a b
    have : N ^ M = φ ((A - 1) ^ M) := by simp [N]
    rw [this]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hA a b)
  have hAm : φ A = N + 1 := by simp [N]
  have hg0 : ((g : ℕ) : R ⧸ I) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 hgI
    simpa using this
  have key : (φ A) ^ (g ^ s) = 1 := by
    rw [hAm, (Commute.one_right N).add_pow, Finset.sum_eq_single 0]
    · simp
    · intro m hm hm0
      rw [Finset.mem_range] at hm
      by_cases hmm : m = g ^ s
      · have : N ^ m = 0 := by
          rw [hmm]; exact pow_eq_zero_of_le hs hNM
        rw [this]; simp
      · have hd : g ∣ (g ^ s).choose m := hg.dvd_choose_pow hm0 hmm
        obtain ⟨c, hc⟩ := hd
        have : (((g ^ s).choose m : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I)) = 0 := by
          rw [hc, Nat.cast_mul]
          have : ((g : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I)) = 0 := by
            ext a b
            simp [Matrix.natCast_apply, hg0]
          rw [this, zero_mul]
        rw [this, mul_zero]
    · intro h; simp at h
  have : φ (A ^ (g ^ s) - 1) = 0 := by rw [map_sub, map_pow, key, map_one, sub_self]
  have h2 := congrFun (congrFun this i) j
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2

/- English proof (translation)
Set `S : G → Set G` to `fun g => {g' | ∃ γ ∈ Γ, ∃ u : U, g' = γ * g * (u : G)}`. Establish `hSself : ∀ g, g ∈ S g` using `fun g => ⟨1, Γ.one_mem, 1, by simp⟩`. Establish `hSeq : ∀ g, ∀ γ ∈ Γ, ∀ u : U, S (γ * g * (u : G)) = S g`. Introduce `g γ hγ u`. Use extensionality with `g'`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ', hγ', u', rfl⟩`. Conclude with `⟨γ' * γ, Γ.mul_mem hγ' hγ, u * u', by simp [mul_assoc]⟩`. Introduce and unpack `⟨γ', hγ', u', rfl⟩`. Conclude with `⟨γ' * γ⁻¹, Γ.mul_mem hγ' (Γ.inv_mem hγ), u⁻¹ * u', by simp [mul_assoc]⟩`.

Use `haveI : Nonempty G := ⟨1⟩`. Set `rep : G → G` to `fun g => Classical.epsilon (fun g' => g' ∈ S g)`. Establish `hrep : ∀ g, rep g ∈ S g` using `fun g => Classical.epsilon_spec (p := fun g' => g' ∈ S g) ⟨g, hSself g⟩`. Establish `hrepeq : ∀ g, ∀ γ ∈ Γ, ∀ u : U, rep (γ * g * (u : G)) = rep g`. Introduce `g γ hγ u`.

Use `show Classical.epsilon (fun g' => g' ∈ S (γ * g * (u : G))) = Classical.epsilon (fun g' => g' ∈ S g)`. Rewrite using `[hSeq g γ hγ u]`. Establish `hdec : ∀ g, ∃ γ : G, ∃ u : U, γ ∈ Γ ∧ g = γ * rep g * (u : G)`. Introduce `g`. Take `⟨γ, hγ, u, h⟩` from `hrep g`.

Conclude with `⟨γ⁻¹, u⁻¹, Γ.inv_mem hγ, by rw [h]; simp [mul_assoc]⟩`. Use `choose γf uf hγf hg using hdec`. Use `choose x hx using hs`. Use `⟨fun g => (uf g)⁻¹ • x (rep g), ?_, ?_⟩` and prove the remaining obligations. Introduce `γ hγ u g`.

Establish `hr` using `hrepeq g γ hγ u`. Establish `e1` using `hg (γ * g * (u : G))`. Rewrite `e1` using `[hr]`. Establish `e0` using `hg g`. Use `set r := rep g`.

Use `set γ1 := γf (γ * g * (u : G))`. Use `set u1 := uf (γ * g * (u : G))`. Use `set γ0 := γf g`. Use `set u0 := uf g`. Establish `e2 : γ * (γ0 * r * (u0 : G)) * (u : G) = γ1 * r * (u1 : G)` using `by rw [← e0]; exact e1`.

Establish `e3 : r⁻¹ * (γ1⁻¹ * (γ * γ0)) * r = (u1 : G) * ((u0 : G) * (u : G))⁻¹`. Establish `: γ * γ0 * r = γ1 * r * (u1 : G) * ((u0 : G) * (u : G))⁻¹`. Rewrite using `[← e2]`. Simplify using `[mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.

Establish `e4 : γ1⁻¹ * (γ * γ0) = 1`. Apply `hst r _ (Γ.mul_mem (Γ.inv_mem (hγf _)) (Γ.mul_mem hγ (hγf _)))` to reduce the goal to its premises. Rewrite using `[e3]`. Conclude with `U.mul_mem u1.2 (U.inv_mem (U.mul_mem u0.2 u.2))`. Establish `e5 : (u1 : G) = (u0 : G) * (u : G)`.

Rewrite `e3` using `[e4]`. Simplify using `only [mul_one, inv_mul_cancel] at e3`. Conclude with `(mul_inv_eq_one.1 e3.symm)`. Establish `e6 : u1 = u0 * u` using `Subtype.ext e5`. Use `show u1⁻¹ • x (rep (γ * g * (u : G))) = u⁻¹ • u0⁻¹ • x r`.

Rewrite using `[hr, e6, mul_inv_rev, mul_smul]`. Introduce `g show p ((uf g)⁻¹ • x (rep g)) = f g`. Rewrite using `[hp, hx]`. Use `conv_rhs => rw [hg g]`. Conclude with `(hf _ (hγf g) _ _).symm`.
-/
theorem liftForm {G : Type} [Group G] (Γ U : Subgroup G)
    (hst : ∀ y : G, ∀ γ ∈ Γ, y⁻¹ * γ * y ∈ U → γ = 1)
    {W V : Type} [MulAction U W] [MulAction U V] (p : W → V)
    (hp : ∀ (u : U) (x : W), p (u • x) = u • p x) (f : G → V) (hf : IsForm Γ U f)
    (hs : ∀ g, ∃ x, p x = f g) : ∃ f' : G → W, IsForm Γ U f' ∧ ∀ g, p (f' g) = f g := by
  classical
  let S : G → Set G := fun g => {g' | ∃ γ ∈ Γ, ∃ u : U, g' = γ * g * (u : G)}
  have hSself : ∀ g, g ∈ S g := fun g => ⟨1, Γ.one_mem, 1, by simp⟩
  have hSeq : ∀ g, ∀ γ ∈ Γ, ∀ u : U, S (γ * g * (u : G)) = S g := by
    intro g γ hγ u
    ext g'
    constructor
    · rintro ⟨γ', hγ', u', rfl⟩
      exact ⟨γ' * γ, Γ.mul_mem hγ' hγ, u * u', by simp [mul_assoc]⟩
    · rintro ⟨γ', hγ', u', rfl⟩
      exact ⟨γ' * γ⁻¹, Γ.mul_mem hγ' (Γ.inv_mem hγ), u⁻¹ * u', by simp [mul_assoc]⟩
  haveI : Nonempty G := ⟨1⟩
  let rep : G → G := fun g => Classical.epsilon (fun g' => g' ∈ S g)
  have hrep : ∀ g, rep g ∈ S g := fun g => Classical.epsilon_spec (p := fun g' => g' ∈ S g) ⟨g, hSself g⟩
  have hrepeq : ∀ g, ∀ γ ∈ Γ, ∀ u : U, rep (γ * g * (u : G)) = rep g := by
    intro g γ hγ u
    show Classical.epsilon (fun g' => g' ∈ S (γ * g * (u : G))) = Classical.epsilon (fun g' => g' ∈ S g)
    rw [hSeq g γ hγ u]
  have hdec : ∀ g, ∃ γ : G, ∃ u : U, γ ∈ Γ ∧ g = γ * rep g * (u : G) := by
    intro g
    obtain ⟨γ, hγ, u, h⟩ := hrep g
    exact ⟨γ⁻¹, u⁻¹, Γ.inv_mem hγ, by rw [h]; simp [mul_assoc]⟩
  choose γf uf hγf hg using hdec
  choose x hx using hs
  refine ⟨fun g => (uf g)⁻¹ • x (rep g), ?_, ?_⟩
  · intro γ hγ u g
    have hr := hrepeq g γ hγ u
    have e1 := hg (γ * g * (u : G))
    rw [hr] at e1
    have e0 := hg g
    set r := rep g
    set γ1 := γf (γ * g * (u : G))
    set u1 := uf (γ * g * (u : G))
    set γ0 := γf g
    set u0 := uf g
    have e2 : γ * (γ0 * r * (u0 : G)) * (u : G) = γ1 * r * (u1 : G) := by rw [← e0]; exact e1
    have e3 : r⁻¹ * (γ1⁻¹ * (γ * γ0)) * r = (u1 : G) * ((u0 : G) * (u : G))⁻¹ := by
      have : γ * γ0 * r = γ1 * r * (u1 : G) * ((u0 : G) * (u : G))⁻¹ := by
        rw [← e2]; simp [mul_assoc]
      calc r⁻¹ * (γ1⁻¹ * (γ * γ0)) * r = r⁻¹ * γ1⁻¹ * (γ * γ0 * r) := by simp [mul_assoc]
        _ = _ := by rw [this]; simp [mul_assoc]
    have e4 : γ1⁻¹ * (γ * γ0) = 1 := by
      apply hst r _ (Γ.mul_mem (Γ.inv_mem (hγf _)) (Γ.mul_mem hγ (hγf _)))
      rw [e3]
      exact U.mul_mem u1.2 (U.inv_mem (U.mul_mem u0.2 u.2))
    have e5 : (u1 : G) = (u0 : G) * (u : G) := by
      rw [e4] at e3
      simp only [mul_one, inv_mul_cancel] at e3
      exact (mul_inv_eq_one.1 e3.symm)
    have e6 : u1 = u0 * u := Subtype.ext e5
    show u1⁻¹ • x (rep (γ * g * (u : G))) = u⁻¹ • u0⁻¹ • x r
    rw [hr, e6, mul_inv_rev, mul_smul]
  · intro g
    show p ((uf g)⁻¹ • x (rep g)) = f g
    rw [hp, hx]
    conv_rhs => rw [hg g]
    exact (hf _ (hγf g) _ _).symm

/- English proof (translation)
Introduce `G _ Γ U hst W₁ W₂ W₃ _ _ _ _ _ _ a b ha hb hex`. Use `⟨fun f hf h0 => ?_, fun hsur f'' hf'' => ?_⟩` and prove the remaining obligations. Conclude with `liftForm Γ U hst a ha f hf (fun g => (hex _).1 (h0 g))`. Conclude with `liftForm Γ U hst b hb f'' hf'' (fun g => hsur _)`.
-/
theorem formsExact : FormsExact := by
  intro G _ Γ U hst W₁ W₂ W₃ _ _ _ _ _ _ a b ha hb hex
  refine ⟨fun f hf h0 => ?_, fun hsur f'' hf'' => ?_⟩
  · exact liftForm Γ U hst a ha f hf (fun g => (hex _).1 (h0 g))
  · exact liftForm Γ U hst b hb f'' hf'' (fun g => hsur _)

end S1

section S2
open NumberField IntermediateField

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

/- English proof (translation)
Establish `e : c * c.den = c.num` using `Rat.mul_den_eq_num c`. Establish `h1 : (m : ℚ) * (c.den : ℚ) ^ 2 = (c.num : ℚ) ^ 2 * m'`. Take the linear combination `(c.den : ℚ) ^ 2 * h + (m' : ℚ) * (c * c.den + c.num) * e`. Establish `h2 : m * (c.den : ℤ) ^ 2 = c.num ^ 2 * m'` using `by exact_mod_cast h1`. Establish `hcop : IsCoprime c.num (c.den : ℤ)`.

Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`. Simplify `c.reduced` using `[Int.gcd]`. Establish `hD : IsUnit (c.den : ℤ)`. Apply `hm'` to reduce the goal to its premises. Establish `: (c.den : ℤ) * c.den ∣ c.num ^ 2 * m'` using `⟨m, by rw [← h2]; ring⟩`.

Establish `hc2 : IsCoprime ((c.den : ℤ) * c.den) (c.num ^ 2)`. Rewrite using `[← pow_two]`. Conclude with `(hcop.symm.pow)`. Conclude with `hc2.dvd_of_dvd_mul_left this`. Establish `hN : IsUnit c.num`.

Apply `hm` to reduce the goal to its premises. Establish `: c.num * c.num ∣ m * (c.den : ℤ) ^ 2` using `⟨m', by rw [h2]; ring⟩`. Establish `hc2 : IsCoprime (c.num * c.num) ((c.den : ℤ) ^ 2)`. Rewrite using `[← pow_two]`. Conclude with `hcop.pow`.

Conclude with `hc2.dvd_of_dvd_mul_right this`. Establish `hD2 : (c.den : ℤ) ^ 2 = 1`. Apply the tactic sequence `rcases Int.isUnit_iff.1 hD with h | h <;> rw [h] <;> norm_num`. Establish `hN2 : c.num ^ 2 = 1`. Apply the tactic sequence `rcases Int.isUnit_iff.1 hN with h | h <;> rw [h] <;> norm_num`.

Rewrite `h2` using `[hD2, hN2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sqf_eq (m m' : ℤ) (hm : Squarefree m) (hm' : Squarefree m') (c : ℚ)
    (h : (m : ℚ) = c ^ 2 * m') : m = m' := by
  have e : c * c.den = c.num := Rat.mul_den_eq_num c
  have h1 : (m : ℚ) * (c.den : ℚ) ^ 2 = (c.num : ℚ) ^ 2 * m' := by
    linear_combination (c.den : ℚ) ^ 2 * h + (m' : ℚ) * (c * c.den + c.num) * e
  have h2 : m * (c.den : ℤ) ^ 2 = c.num ^ 2 * m' := by exact_mod_cast h1
  have hcop : IsCoprime c.num (c.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using c.reduced
  have hD : IsUnit (c.den : ℤ) := by
    apply hm'
    have : (c.den : ℤ) * c.den ∣ c.num ^ 2 * m' := ⟨m, by rw [← h2]; ring⟩
    have hc2 : IsCoprime ((c.den : ℤ) * c.den) (c.num ^ 2) := by
      rw [← pow_two]; exact (hcop.symm.pow)
    exact hc2.dvd_of_dvd_mul_left this
  have hN : IsUnit c.num := by
    apply hm
    have : c.num * c.num ∣ m * (c.den : ℤ) ^ 2 := ⟨m', by rw [h2]; ring⟩
    have hc2 : IsCoprime (c.num * c.num) ((c.den : ℤ) ^ 2) := by
      rw [← pow_two]; exact hcop.pow
    exact hc2.dvd_of_dvd_mul_right this
  have hD2 : (c.den : ℤ) ^ 2 = 1 := by
    rcases Int.isUnit_iff.1 hD with h | h <;> rw [h] <;> norm_num
  have hN2 : c.num ^ 2 = 1 := by
    rcases Int.isUnit_iff.1 hN with h | h <;> rw [h] <;> norm_num
  rw [hD2, hN2] at h2
  linarith

/- English proof (translation)
Take `⟨hq, hd, hqd, hq2, hd2⟩` from `h`. Rewrite using `[← Int.squarefree_natAbs]`. Establish `e : ((2 : ℤ) ^ i3 * (-(q : ℤ)) ^ i1 * (-(d : ℤ)) ^ i2).natAbs = 2 ^ i3 * q ^ i1 * d ^ i2`. Simplify using `[Int.natAbs_mul, Int.natAbs_pow]`. Rewrite using `[e]`.

Establish `hp : ∀ p : ℕ, p.Prime → ∀ i : ℕ, i ≤ 1 → Squarefree (p ^ i)`. Introduce `p hp i hi`. Use `interval_cases i`. Simplify using the standard rewrite rules. Simplify using `using hp.prime.squarefree`.

Establish `c1 : Nat.Coprime (2 ^ i3) (q ^ i1)` using `Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))`. Establish `c2 : Nat.Coprime (2 ^ i3 * q ^ i1) (d ^ i2)` using `Nat.Coprime.mul_left (Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hd).2 (Ne.symm hd2))) (Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hd).2 hqd))`. Rewrite using `[Nat.squarefree_mul c2, Nat.squarefree_mul c1]`. Conclude with `⟨⟨hp 2 Nat.prime_two i3 h3, hp q hq i1 h1⟩, hp d hd i2 h2⟩`.
-/
theorem sqf3 (q d : ℕ) (h : HypOdd q d) (i1 i2 i3 : ℕ) (h1 : i1 ≤ 1) (h2 : i2 ≤ 1) (h3 : i3 ≤ 1) :
    Squarefree ((2 : ℤ) ^ i3 * (-(q : ℤ)) ^ i1 * (-(d : ℤ)) ^ i2) := by
  obtain ⟨hq, hd, hqd, hq2, hd2⟩ := h
  rw [← Int.squarefree_natAbs]
  have e : ((2 : ℤ) ^ i3 * (-(q : ℤ)) ^ i1 * (-(d : ℤ)) ^ i2).natAbs = 2 ^ i3 * q ^ i1 * d ^ i2 := by
    simp [Int.natAbs_mul, Int.natAbs_pow]
  rw [e]
  have hp : ∀ p : ℕ, p.Prime → ∀ i : ℕ, i ≤ 1 → Squarefree (p ^ i) := by
    intro p hp i hi
    interval_cases i
    · simp
    · simpa using hp.prime.squarefree
  have c1 : Nat.Coprime (2 ^ i3) (q ^ i1) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
  have c2 : Nat.Coprime (2 ^ i3 * q ^ i1) (d ^ i2) :=
    Nat.Coprime.mul_left (Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hd).2 (Ne.symm hd2)))
      (Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hd).2 hqd))
  rw [Nat.squarefree_mul c2, Nat.squarefree_mul c1]
  exact ⟨⟨hp 2 Nat.prime_two i3 h3, hp q hq i1 h1⟩, hp d hd i2 h2⟩

/- English proof (translation)
Unfold `sgn at h`. Assume the negation of the conclusion as `hne`. Rewrite `h` using `[if_neg hne]`. Conclude with `absurd h (by decide)`.
-/
theorem sgn_one' {L : Type*} [Field L] [Algebra ℚ L] {τ : Gal(L/ℚ)} {x : L} (h : sgn τ x = 1) :
    τ x = x := by
  unfold sgn at h
  by_contra hne
  rw [if_neg hne] at h
  exact absurd h (by decide)

/- English proof (translation)
Unfold `sgn at h`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 hx with h1 | h1` into its components or cases. Rewrite `h` using `[if_pos h1]`. Conclude with `absurd h (by decide)`. Conclude with `h1`.
-/
theorem sgn_neg' {L : Type*} [Field L] [Algebra ℚ L] {τ : Gal(L/ℚ)} {x : L} (h : sgn τ x = -1)
    (hx : (τ x) ^ 2 = x ^ 2) : τ x = -x := by
  unfold sgn at h
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hx with h1 | h1
  · rw [if_pos h1] at h
    exact absurd h (by decide)
  · exact h1

section
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

/- English proof (translation)
Use `h.1.autToPow_spec ℚ τ` as an intermediate fact. Rewrite using `[← this]`. Establish `e1 : ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = (k : ZMod (2 ^ (e + 2)))` using `hk.symm`. Rewrite using `[e1, ZMod.val_natCast]`. Conclude with `(pow_eq_pow_mod k h.1.pow_eq_one).symm`.
-/
theorem act_zeta (h : IsLayer (e + 2) q d ζ a b) (τ : Gal(L/ℚ)) (k : ℕ)
    (hk : (k : ZMod (2 ^ (e + 2))) = ((galMap h.1 a b τ).1 : ZMod (2 ^ (e + 2)))) : τ ζ = ζ ^ k := by
  have := h.1.autToPow_spec ℚ τ
  rw [← this]
  have e1 : ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = (k : ZMod (2 ^ (e + 2))) :=
    hk.symm
  rw [e1, ZMod.val_natCast]
  exact (pow_eq_pow_mod k h.1.pow_eq_one).symm

/- English proof (translation)
Establish `hθ : ζ + ζ⁻¹ ∈ F1 ζ` using `mem_adjoin_simple_self ℚ _`. Proceed by induction on `j with`. Consider the case `zero`. Use `⟨?_, by simpa using hθ⟩` and prove the remaining obligations. Establish `: ζ ^ 0 + ζ⁻¹ ^ 0 = ((2 : ℕ) : L)` using `by norm_num`.

Rewrite using `[this]`. Conclude with `_root_.natCast_mem _ _`. Consider the case `succ j ih`. Use `⟨ih.2, ?_⟩` and prove the remaining obligations. Establish `: ζ ^ (j + 1 + 1) + ζ⁻¹ ^ (j + 1 + 1) = (ζ + ζ⁻¹) * (ζ ^ (j + 1) + ζ⁻¹ ^ (j + 1)) - (ζ ^ j + ζ⁻¹ ^ j)`.

Establish `h1 : ζ * ζ⁻¹ = 1` using `mul_inv_cancel₀ hζ0`. Take the linear combination `(-(ζ ^ j) - ζ⁻¹ ^ j) * h1`. Rewrite using `[this]`. Conclude with `sub_mem (mul_mem hθ ih.2) ih.1`.
-/
theorem cheb_mem (hζ0 : ζ ≠ 0) (j : ℕ) : ζ ^ j + ζ⁻¹ ^ j ∈ F1 ζ ∧ ζ ^ (j + 1) + ζ⁻¹ ^ (j + 1) ∈ F1 ζ := by
  have hθ : ζ + ζ⁻¹ ∈ F1 ζ := mem_adjoin_simple_self ℚ _
  induction j with
  | zero =>
    refine ⟨?_, by simpa using hθ⟩
    have : ζ ^ 0 + ζ⁻¹ ^ 0 = ((2 : ℕ) : L) := by norm_num
    rw [this]; exact _root_.natCast_mem _ _
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    have : ζ ^ (j + 1 + 1) + ζ⁻¹ ^ (j + 1 + 1) =
        (ζ + ζ⁻¹) * (ζ ^ (j + 1) + ζ⁻¹ ^ (j + 1)) - (ζ ^ j + ζ⁻¹ ^ j) := by
      have h1 : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
      linear_combination (-(ζ ^ j) - ζ⁻¹ ^ j) * h1
    rw [this]
    exact sub_mem (mul_mem hθ ih.2) ih.1

/- English proof (translation)
Take `⟨hGal, -, hmul, hbij⟩` from `layerGalois (e + 2) q d (by omega) hqd L ζ a b h`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Establish `: (m' : L) = 0` using `by rw [← hym]; ring`. Establish `: m' = 0` using `by exact_mod_cast this`.

Rewrite `hm'` using `[this]`. Conclude with `not_squarefree_zero hm'`. Take `⟨τ₀, h0⟩` from `hbij.2 ((-1, 1, 1) : GalL (e + 2))`. Establish `hfix0 : ∀ x ∈ hostE ζ a b, τ₀ x = x` using `fun x hx => ((hostFixed e q d hqd L ζ a b h).2 x).1 hx τ₀ h0`. Establish `hrel : ∀ τ : Gal(L/ℚ), τ X * y = X * τ y → τ (X / y) = X / y`.

Introduce `τ hτ`. Establish `: τ y ≠ 0` using `by simpa using hy0`. Rewrite using `[map_div₀, div_eq_div_iff this hy0, hτ]`. Set `φ : Gal(L/ℚ) →* GalL (e + 2)` to `MonoidHom.mk' (galMap h.1 a b) hmul`. Set `S : Subgroup Gal(L/ℚ)` to `MulAction.stabilizer Gal(L/ℚ) (X / y)`.

Establish `hS : ∀ τ : Gal(L/ℚ), τ (X / y) = X / y → τ ∈ S` using `fun τ hτ => hτ`. Establish `htop : S.map φ = ⊤`. Rewrite using `[eq_top_iff, ← (gensModel (e + 2) (by omega)).2.2.2.2, Subgroup.closure_le]`. Introduce and unpack `g (rfl | rfl | rfl | rfl)`. Conclude with `⟨τ₀, hS _ (hrel _ (by rw [hfix0 X hX, hfix0 y hy])), h0⟩`.

Conclude with `⟨τ₃, hS _ (hrel _ r3), h3⟩`. Conclude with `⟨τ₁, hS _ (hrel _ r1), h1⟩`. Conclude with `⟨τ₂, hS _ (hrel _ r2), h2⟩`. Establish `hall : ∀ τ : Gal(L/ℚ), τ (X / y) = X / y`. Introduce `τ`.

Establish `: φ τ ∈ S.map φ` using `by rw [htop]; trivial`. Take `⟨τ', hτ', he⟩` from `this`. Establish `: τ' = τ` using `hbij.1 he`. Rewrite using `[← this]`. Conclude with `hτ'`.

Establish `hbot` using `(IsGalois.mem_bot_iff_fixed (F := ℚ) (E := L) (X / y)).2 hall`. Take `⟨c, hc⟩` from `IntermediateField.mem_bot.1 hbot`. Apply `sqf_eq m m' hm hm' c` to reduce the goal to its premises. Establish `hXc : X = algebraMap ℚ L c * y` using `by rw [hc]; field_simp`. Establish `: ((m : ℚ) : L) = ((c ^ 2 * m' : ℚ) : L)`.

Use `push_cast`. Rewrite using `[← hXm, ← hym, hXc]`. Simplify using `only [eq_ratCast]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions.
-/
theorem coreQ (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (τ₁ τ₂ τ₃ : Gal(L/ℚ)) (h1 : galMap h.1 a b τ₁ = ((1, -1, 1) : GalL (e + 2)))
    (h2 : galMap h.1 a b τ₂ = ((1, 1, -1) : GalL (e + 2)))
    (h3 : galMap h.1 a b τ₃ = ((u5 (e + 2), 1, 1) : GalL (e + 2)))
    (X y : L) (hX : X ∈ hostE ζ a b) (hy : y ∈ hostE ζ a b) (m m' : ℤ) (hm : Squarefree m)
    (hm' : Squarefree m') (hXm : X ^ 2 = (m : L)) (hym : y ^ 2 = (m' : L))
    (r1 : τ₁ X * y = X * τ₁ y) (r2 : τ₂ X * y = X * τ₂ y) (r3 : τ₃ X * y = X * τ₃ y) : m = m' := by
  obtain ⟨hGal, -, hmul, hbij⟩ := layerGalois (e + 2) q d (by omega) hqd L ζ a b h
  have hy0 : y ≠ 0 := by
    rintro rfl
    have : (m' : L) = 0 := by rw [← hym]; ring
    have : m' = 0 := by exact_mod_cast this
    rw [this] at hm'
    exact not_squarefree_zero hm'
  obtain ⟨τ₀, h0⟩ := hbij.2 ((-1, 1, 1) : GalL (e + 2))
  have hfix0 : ∀ x ∈ hostE ζ a b, τ₀ x = x := fun x hx =>
    ((hostFixed e q d hqd L ζ a b h).2 x).1 hx τ₀ h0
  have hrel : ∀ τ : Gal(L/ℚ), τ X * y = X * τ y → τ (X / y) = X / y := by
    intro τ hτ
    have : τ y ≠ 0 := by simpa using hy0
    rw [map_div₀, div_eq_div_iff this hy0, hτ]
  let φ : Gal(L/ℚ) →* GalL (e + 2) := MonoidHom.mk' (galMap h.1 a b) hmul
  let S : Subgroup Gal(L/ℚ) := MulAction.stabilizer Gal(L/ℚ) (X / y)
  have hS : ∀ τ : Gal(L/ℚ), τ (X / y) = X / y → τ ∈ S := fun τ hτ => hτ
  have htop : S.map φ = ⊤ := by
    rw [eq_top_iff, ← (gensModel (e + 2) (by omega)).2.2.2.2, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl | rfl)
    · exact ⟨τ₀, hS _ (hrel _ (by rw [hfix0 X hX, hfix0 y hy])), h0⟩
    · exact ⟨τ₃, hS _ (hrel _ r3), h3⟩
    · exact ⟨τ₁, hS _ (hrel _ r1), h1⟩
    · exact ⟨τ₂, hS _ (hrel _ r2), h2⟩
  have hall : ∀ τ : Gal(L/ℚ), τ (X / y) = X / y := by
    intro τ
    have : φ τ ∈ S.map φ := by rw [htop]; trivial
    obtain ⟨τ', hτ', he⟩ := this
    have : τ' = τ := hbij.1 he
    rw [← this]; exact hτ'
  have hbot := (IsGalois.mem_bot_iff_fixed (F := ℚ) (E := L) (X / y)).2 hall
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hbot
  apply sqf_eq m m' hm hm' c
  have hXc : X = algebraMap ℚ L c * y := by rw [hc]; field_simp
  have : ((m : ℚ) : L) = ((c ^ 2 * m' : ℚ) : L) := by
    push_cast
    rw [← hXm, ← hym, hXc]
    simp only [eq_ratCast]
    ring
  exact_mod_cast this

end

/- English proof (translation)
Introduce `e q d he hqd L _ _ ζ a b h m hm`. Take `⟨hGal, -, hmul, hbij⟩` from `layerGalois (e + 2) q d (by omega) hqd L ζ a b h`. Establish `hζ0 : ζ ≠ 0` using `h.1.ne_zero (by positivity)`. Take `⟨r, hr⟩ : ∃ r, r = ζ ^ (2 ^ (e - 1))` from `⟨_, rfl⟩`. Establish `hr4 : r ^ 4 = -1`.

Establish `hp : IsPrimitiveRoot (ζ ^ (2 ^ (e + 1))) 2` using `h.1.pow (by positivity) (by rw [← pow_succ])`. Establish `: r ^ 4 = ζ ^ (2 ^ (e + 1))`. Rewrite using `[hr, ← pow_mul]`. Use `congr 1`. Take `⟨e', rfl⟩ : ∃ e', e = e' + 1` from `⟨e - 1, by omega⟩`.

Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `hp.eq_neg_one_of_two_right`. Take `⟨s, hs⟩ : ∃ s, s = r - r ^ 3` from `⟨_, rfl⟩`.

Establish `hs2 : s ^ 2 = 2`. Rewrite using `[hs]`. Take the linear combination `(r ^ 2 - 2) * hr4`. Establish `hsE : s ∈ hostE ζ a b`. Establish `h1` using `(cheb_mem hζ0 (2 ^ (e - 1))).1`.

Establish `: ζ⁻¹ ^ (2 ^ (e - 1)) = - r ^ 3`. Rewrite using `[inv_pow, ← hr]`. Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Take the linear combination `(-1 : L) * hr4`. Rewrite `h1` using `[this, ← hr, ← sub_eq_add_neg, ← hs]`.

Conclude with `(le_sup_right : F1 ζ ≤ hostE ζ a b) h1`. Establish `ha2 : a ^ 2 = -(q : L)` using `h.2.1`. Establish `hb2 : b ^ 2 = -(d : L)` using `h.2.2.1`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx⟩`.

Establish `hXm : (x : L) ^ 2 = (m : L)`. Use `congrArg (fun z : hostE ζ a b => (z : L)) hx` as an intermediate fact. Simplify using `using this`. Take `⟨τ₁, h1⟩` from `hbij.2 ((1, -1, 1) : GalL (e + 2))`. Take `⟨τ₂, h2⟩` from `hbij.2 ((1, 1, -1) : GalL (e + 2))`.

Take `⟨τ₃, h3⟩` from `hbij.2 ((u5 (e + 2), 1, 1) : GalL (e + 2))`. Establish `sq : ∀ (τ : Gal(L/ℚ)) (z : L) (n : ℤ), z ^ 2 = (n : L) → (τ z) ^ 2 = z ^ 2`. Introduce `τ z n hz`. Rewrite using `[← map_pow, hz, map_intCast]`. Establish `sgnX : ∀ τ : Gal(L/ℚ), ∃ i : ℕ, i ≤ 1 ∧ τ (x : L) = (-1) ^ i * x`.

Introduce `τ`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 (sq τ x m hXm) with h | h` into its components or cases. Conclude with `⟨0, by omega, by simp [h]⟩`. Conclude with `⟨1, le_refl _, by simp [h]⟩`. Establish `ha2' : a ^ 2 = ((-(q : ℤ) : ℤ) : L)` using `by push_cast; exact ha2`.

Establish `hb2' : b ^ 2 = ((-(d : ℤ) : ℤ) : L)` using `by push_cast; exact hb2`. Establish `t1ζ : τ₁ ζ = ζ` using `by simpa using act_zeta h τ₁ 1 (by rw [h1]; simp)`. Establish `t2ζ : τ₂ ζ = ζ` using `by simpa using act_zeta h τ₂ 1 (by rw [h2]; simp)`. Establish `t3ζ : τ₃ ζ = ζ ^ 5` using `act_zeta h τ₃ 5 (by rw [h3]; simp [u5])`. Establish `t1a : τ₁ a = -a` using `sgn_neg' (congrArg (fun g : GalL (e + 2) => g.2.1) h1) (sq _ _ _ ha2')`.

Establish `t1b : τ₁ b = b` using `sgn_one' (congrArg (fun g : GalL (e + 2) => g.2.2) h1)`. Establish `t2a : τ₂ a = a` using `sgn_one' (congrArg (fun g : GalL (e + 2) => g.2.1) h2)`. Establish `t2b : τ₂ b = -b` using `sgn_neg' (congrArg (fun g : GalL (e + 2) => g.2.2) h2) (sq _ _ _ hb2')`. Establish `t3a : τ₃ a = a` using `sgn_one' (congrArg (fun g : GalL (e + 2) => g.2.1) h3)`. Establish `t3b : τ₃ b = b` using `sgn_one' (congrArg (fun g : GalL (e + 2) => g.2.2) h3)`.

Establish `t1s : τ₁ s = s` using `by rw [hs, hr]; simp [t1ζ]`. Establish `t2s : τ₂ s = s` using `by rw [hs, hr]; simp [t2ζ]`. Establish `t3s : τ₃ s = -s`. Establish `: τ₃ r = r ^ 5` using `by rw [hr, map_pow, t3ζ, ← pow_mul, ← pow_mul, mul_comm]`. Rewrite using `[hs, map_sub, map_pow, this]`.

Take the linear combination `(r - r ^ 11 + r ^ 7 - r ^ 3) * hr4`. Take `⟨i1, hi1, e1⟩` from `sgnX τ₁`. Take `⟨i2, hi2, e2⟩` from `sgnX τ₂`. Take `⟨i3, hi3, e3⟩` from `sgnX τ₃`. Establish `key` using `coreQ hqd h τ₁ τ₂ τ₃ h1 h2 h3 (x : L) (s ^ i3 * a ^ i1 * b ^ i2) x.2 (mul_mem (mul_mem (pow_mem hsE _) (pow_mem (a_mem ζ a b) _)) (pow_mem (b_mem ζ a b) _)) m ((2 : ℤ) ^ i3 * (-(q : ℤ)) ^ i1 * (-(d : ℤ)) ^ i2) hm (sqf3 q d hqd i1 i2 i3 hi1 hi2 hi3) hXm (by`.

Use `push_cast`. Rewrite using `[← ha2, ← hb2, ← hs2]`. Use the proof step `ring)`. Use the proof step `(by rw [e1]; simp only [map_mul, map_pow, t1s, t1a, t1b]; rw [neg_pow a]; ring)`. Use the proof step `(by rw [e2]; simp only [map_mul, map_pow, t2s, t2a, t2b]; rw [neg_pow b]; ring)`.

Use the proof step `(by rw [e3]; simp only [map_mul, map_pow, t3s, t3a, t3b]; rw [neg_pow s]; ring)`. Rewrite using `[key]`. Apply the tactic sequence `interval_cases i1 <;> interval_cases i2 <;> interval_cases i3 <;> simp <;> ring_nf <;> simp`. Establish `hA : (aE ζ a b) ^ 2 = -(q : hostE ζ a b)` using `Subtype.ext (by simpa [aE] using ha2)`. Establish `hB : (bE ζ a b) ^ 2 = -(d : hostE ζ a b)` using `Subtype.ext (by simpa [bE] using hb2)`.

Set `sE : hostE ζ a b` to `⟨s, hsE⟩`. Establish `hS : sE ^ 2 = 2`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show s ^ 2 = ((2 : hostE ζ a b) : L)`. Rewrite using `[hs2]`.

Conclude with `(map_ofNat (hostE ζ a b).val 2).symm`. Introduce and unpack `(rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)`. Conclude with `⟨1, by simp⟩`. Conclude with `⟨sE, by rw [hS]; simp⟩`. Conclude with `⟨aE ζ a b, by rw [hA]; simp⟩`.

Conclude with `⟨bE ζ a b, by rw [hB]; simp⟩`. Conclude with `⟨aE ζ a b * bE ζ a b, by rw [mul_pow, hA, hB]; push_cast; ring⟩`. Conclude with `⟨sE * aE ζ a b, by rw [mul_pow, hA, hS]; push_cast; ring⟩`. Conclude with `⟨sE * bE ζ a b, by rw [mul_pow, hB, hS]; push_cast; ring⟩`. Conclude with `⟨sE * aE ζ a b * bE ζ a b, by rw [mul_pow, mul_pow, hA, hB, hS]; push_cast; ring⟩`.
-/
theorem hostQuadSub : HostQuadSub := by
  intro e q d he hqd L _ _ ζ a b h m hm
  obtain ⟨hGal, -, hmul, hbij⟩ := layerGalois (e + 2) q d (by omega) hqd L ζ a b h
  have hζ0 : ζ ≠ 0 := h.1.ne_zero (by positivity)
  obtain ⟨r, hr⟩ : ∃ r, r = ζ ^ (2 ^ (e - 1)) := ⟨_, rfl⟩
  have hr4 : r ^ 4 = -1 := by
    have hp : IsPrimitiveRoot (ζ ^ (2 ^ (e + 1))) 2 :=
      h.1.pow (by positivity) (by rw [← pow_succ])
    have : r ^ 4 = ζ ^ (2 ^ (e + 1)) := by
      rw [hr, ← pow_mul]
      congr 1
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [this]
    exact hp.eq_neg_one_of_two_right
  obtain ⟨s, hs⟩ : ∃ s, s = r - r ^ 3 := ⟨_, rfl⟩
  have hs2 : s ^ 2 = 2 := by
    rw [hs]; linear_combination (r ^ 2 - 2) * hr4
  have hsE : s ∈ hostE ζ a b := by
    have h1 := (cheb_mem hζ0 (2 ^ (e - 1))).1
    have : ζ⁻¹ ^ (2 ^ (e - 1)) = - r ^ 3 := by
      rw [inv_pow, ← hr]
      apply inv_eq_of_mul_eq_one_right
      linear_combination (-1 : L) * hr4
    rw [this, ← hr, ← sub_eq_add_neg, ← hs] at h1
    exact (le_sup_right : F1 ζ ≤ hostE ζ a b) h1
  have ha2 : a ^ 2 = -(q : L) := h.2.1
  have hb2 : b ^ 2 = -(d : L) := h.2.2.1
  constructor
  · rintro ⟨x, hx⟩
    have hXm : (x : L) ^ 2 = (m : L) := by
      have := congrArg (fun z : hostE ζ a b => (z : L)) hx
      simpa using this
    obtain ⟨τ₁, h1⟩ := hbij.2 ((1, -1, 1) : GalL (e + 2))
    obtain ⟨τ₂, h2⟩ := hbij.2 ((1, 1, -1) : GalL (e + 2))
    obtain ⟨τ₃, h3⟩ := hbij.2 ((u5 (e + 2), 1, 1) : GalL (e + 2))
    have sq : ∀ (τ : Gal(L/ℚ)) (z : L) (n : ℤ), z ^ 2 = (n : L) → (τ z) ^ 2 = z ^ 2 := by
      intro τ z n hz
      rw [← map_pow, hz, map_intCast]
    have sgnX : ∀ τ : Gal(L/ℚ), ∃ i : ℕ, i ≤ 1 ∧ τ (x : L) = (-1) ^ i * x := by
      intro τ
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 (sq τ x m hXm) with h | h
      · exact ⟨0, by omega, by simp [h]⟩
      · exact ⟨1, le_refl _, by simp [h]⟩
    have ha2' : a ^ 2 = ((-(q : ℤ) : ℤ) : L) := by push_cast; exact ha2
    have hb2' : b ^ 2 = ((-(d : ℤ) : ℤ) : L) := by push_cast; exact hb2
    have t1ζ : τ₁ ζ = ζ := by simpa using act_zeta h τ₁ 1 (by rw [h1]; simp)
    have t2ζ : τ₂ ζ = ζ := by simpa using act_zeta h τ₂ 1 (by rw [h2]; simp)
    have t3ζ : τ₃ ζ = ζ ^ 5 := act_zeta h τ₃ 5 (by rw [h3]; simp [u5])
    have t1a : τ₁ a = -a := sgn_neg' (congrArg (fun g : GalL (e + 2) => g.2.1) h1) (sq _ _ _ ha2')
    have t1b : τ₁ b = b := sgn_one' (congrArg (fun g : GalL (e + 2) => g.2.2) h1)
    have t2a : τ₂ a = a := sgn_one' (congrArg (fun g : GalL (e + 2) => g.2.1) h2)
    have t2b : τ₂ b = -b := sgn_neg' (congrArg (fun g : GalL (e + 2) => g.2.2) h2) (sq _ _ _ hb2')
    have t3a : τ₃ a = a := sgn_one' (congrArg (fun g : GalL (e + 2) => g.2.1) h3)
    have t3b : τ₃ b = b := sgn_one' (congrArg (fun g : GalL (e + 2) => g.2.2) h3)
    have t1s : τ₁ s = s := by rw [hs, hr]; simp [t1ζ]
    have t2s : τ₂ s = s := by rw [hs, hr]; simp [t2ζ]
    have t3s : τ₃ s = -s := by
      have : τ₃ r = r ^ 5 := by rw [hr, map_pow, t3ζ, ← pow_mul, ← pow_mul, mul_comm]
      rw [hs, map_sub, map_pow, this]
      linear_combination (r - r ^ 11 + r ^ 7 - r ^ 3) * hr4
    obtain ⟨i1, hi1, e1⟩ := sgnX τ₁
    obtain ⟨i2, hi2, e2⟩ := sgnX τ₂
    obtain ⟨i3, hi3, e3⟩ := sgnX τ₃
    have key := coreQ hqd h τ₁ τ₂ τ₃ h1 h2 h3 (x : L) (s ^ i3 * a ^ i1 * b ^ i2) x.2
      (mul_mem (mul_mem (pow_mem hsE _) (pow_mem (a_mem ζ a b) _)) (pow_mem (b_mem ζ a b) _))
      m ((2 : ℤ) ^ i3 * (-(q : ℤ)) ^ i1 * (-(d : ℤ)) ^ i2) hm (sqf3 q d hqd i1 i2 i3 hi1 hi2 hi3) hXm
      (by
        push_cast
        rw [← ha2, ← hb2, ← hs2]; ring)
      (by rw [e1]; simp only [map_mul, map_pow, t1s, t1a, t1b]; rw [neg_pow a]; ring)
      (by rw [e2]; simp only [map_mul, map_pow, t2s, t2a, t2b]; rw [neg_pow b]; ring)
      (by rw [e3]; simp only [map_mul, map_pow, t3s, t3a, t3b]; rw [neg_pow s]; ring)
    rw [key]
    interval_cases i1 <;> interval_cases i2 <;> interval_cases i3 <;> simp <;> ring_nf <;> simp
  · have hA : (aE ζ a b) ^ 2 = -(q : hostE ζ a b) := Subtype.ext (by simpa [aE] using ha2)
    have hB : (bE ζ a b) ^ 2 = -(d : hostE ζ a b) := Subtype.ext (by simpa [bE] using hb2)
    let sE : hostE ζ a b := ⟨s, hsE⟩
    have hS : sE ^ 2 = 2 := by
      apply Subtype.ext
      show s ^ 2 = ((2 : hostE ζ a b) : L)
      rw [hs2]
      exact (map_ofNat (hostE ζ a b).val 2).symm
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨1, by simp⟩
    · exact ⟨sE, by rw [hS]; simp⟩
    · exact ⟨aE ζ a b, by rw [hA]; simp⟩
    · exact ⟨bE ζ a b, by rw [hB]; simp⟩
    · exact ⟨aE ζ a b * bE ζ a b, by rw [mul_pow, hA, hB]; push_cast; ring⟩
    · exact ⟨sE * aE ζ a b, by rw [mul_pow, hA, hS]; push_cast; ring⟩
    · exact ⟨sE * bE ζ a b, by rw [mul_pow, hB, hS]; push_cast; ring⟩
    · exact ⟨sE * aE ζ a b * bE ζ a b, by rw [mul_pow, mul_pow, hA, hB, hS]; push_cast; ring⟩

open Formalism.HermitianLattices.FiltrationBoundaryCriterion in
/- English proof (translation)
Introduce `e q d h L _ _ ζ a b hl x`. Take `⟨_, _, hmul, hbij⟩` from `hostGalois e q d h L ζ a b hl`. Take `⟨c, hc⟩` from `hbij.2 (cc e)`. Establish `hreal` using `(Final.real e q d h L ζ a b hl).2`. Establish `hone : galE e ζ a b 1 = 1`.

Use `hmul 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `(mul_eq_left.1 this.symm)`. Establish `hcc : c * c = 1` using `hbij.1 (by`. Rewrite using `[hmul, hc, hone]`.

Simplify using `[cc, c0, Prod.ext_iff])`. Establish `hcc' : ∀ y, c (c y) = y` using `fun y => by`. Use `congrArg (fun s : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b => s y) hcc` as an intermediate fact. Simplify using `using this`. Establish `hmem : ∀ y : hostE ζ a b, c y = y → y ∈ hostF ζ a b` using `fun y hy => ((hreal y).1).2 (fun σ hσ => by rw [hbij.1 (hσ.trans hc.symm)]; exact hy)`.

Establish `hspec` using `hostGalSpec e q d h L ζ a b hl c`. Establish `hca : c (aE ζ a b) = - aE ζ a b`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hspec.1, hc]`. Simplify using `[cc, c0, aE]`.

Establish `hcb : c (bE ζ a b) = - bE ζ a b`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hspec.2.1, hc]`. Simplify using `[cc, c0, bE]`. Establish `ha0 : aE ζ a b ≠ 0`.

Introduce `h0`. Establish `: a = 0` using `congrArg Subtype.val h0`. Establish `h2` using `hl.2.1`. Rewrite `h2` using `[this]`. Establish `: (q : L) = 0` using `by simpa using h2.symm`.

Conclude with `h.1.ne_zero (by exact_mod_cast this)`. Establish `hb0 : bE ζ a b ≠ 0`. Introduce `h0`. Establish `: b = 0` using `congrArg Subtype.val h0`. Establish `h2` using `hl.2.2.1`.

Rewrite `h2` using `[this]`. Establish `: (d : L) = 0` using `by simpa using h2.symm`. Conclude with `h.2.1.ne_zero (by exact_mod_cast this)`. Establish `gen : ∀ t : hostE ζ a b, c t = -t → t ≠ 0 → ∃ u ∈ hostF ζ a b, ∃ v ∈ hostF ζ a b, x = u + v * t`. Introduce `t ht ht0`.

Use `⟨(x + c x) / 2, hmem _ ?_, (x - c x) / (2 * t), hmem _ ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [map_div₀, map_add, hcc', map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_div₀, map_sub, map_mul, hcc', map_ofNat, ht]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨gen _ hcb hb0, gen _ hca ha0⟩`.
-/
theorem hostEOverF : HostEOverF := by
  intro e q d h L _ _ ζ a b hl x
  obtain ⟨_, _, hmul, hbij⟩ := hostGalois e q d h L ζ a b hl
  obtain ⟨c, hc⟩ := hbij.2 (cc e)
  have hreal := (Final.real e q d h L ζ a b hl).2
  have hone : galE e ζ a b 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  have hcc : c * c = 1 := hbij.1 (by
    rw [hmul, hc, hone]
    simp [cc, c0, Prod.ext_iff])
  have hcc' : ∀ y, c (c y) = y := fun y => by
    have := congrArg (fun s : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b => s y) hcc
    simpa using this
  have hmem : ∀ y : hostE ζ a b, c y = y → y ∈ hostF ζ a b := fun y hy =>
    ((hreal y).1).2 (fun σ hσ => by rw [hbij.1 (hσ.trans hc.symm)]; exact hy)
  have hspec := hostGalSpec e q d h L ζ a b hl c
  have hca : c (aE ζ a b) = - aE ζ a b := by
    apply Subtype.ext
    rw [hspec.1, hc]
    simp [cc, c0, aE]
  have hcb : c (bE ζ a b) = - bE ζ a b := by
    apply Subtype.ext
    rw [hspec.2.1, hc]
    simp [cc, c0, bE]
  have ha0 : aE ζ a b ≠ 0 := by
    intro h0
    have : a = 0 := congrArg Subtype.val h0
    have h2 := hl.2.1
    rw [this] at h2
    have : (q : L) = 0 := by simpa using h2.symm
    exact h.1.ne_zero (by exact_mod_cast this)
  have hb0 : bE ζ a b ≠ 0 := by
    intro h0
    have : b = 0 := congrArg Subtype.val h0
    have h2 := hl.2.2.1
    rw [this] at h2
    have : (d : L) = 0 := by simpa using h2.symm
    exact h.2.1.ne_zero (by exact_mod_cast this)
  have gen : ∀ t : hostE ζ a b, c t = -t → t ≠ 0 →
      ∃ u ∈ hostF ζ a b, ∃ v ∈ hostF ζ a b, x = u + v * t := by
    intro t ht ht0
    refine ⟨(x + c x) / 2, hmem _ ?_, (x - c x) / (2 * t), hmem _ ?_, ?_⟩
    · simp only [map_div₀, map_add, hcc', map_ofNat]; ring
    · simp only [map_div₀, map_sub, map_mul, hcc', map_ofNat, ht]
      field_simp
      ring
    · field_simp
      ring
  exact ⟨gen _ hcb hb0, gen _ hca ha0⟩

end S2

section S3
open NumberField IntermediateField Ideal IsDedekindDomain nonZeroDivisors
open scoped Pointwise

section gen
variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Rewrite `h`, the goal using `[← FractionalIdeal.mem_coe]`. Conclude with `neg_mem h`.
-/
theorem fi_neg_mem {I : FractionalIdeal (𝓞 E)⁰ E} {x : E} (h : x ∈ I) : -x ∈ I := by
  rw [← FractionalIdeal.mem_coe] at h ⊢
  exact neg_mem h

/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_coeIdeal]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `⟨σ • w, Ideal.smul_mem_pointwise_smul σ w I hw, rfl⟩`. Introduce and unpack `⟨w, hw, he⟩`.

Rewrite `hw` using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Use `⟨σ⁻¹ • w, hw, ?_⟩` and prove the remaining obligations. Use `show σ⁻¹ (w : E) = z`. Establish `he' : (w : E) = σ z` using `he`. Rewrite using `[he']`.

Conclude with `σ.symm_apply_apply z`.
-/
theorem mem_coe_smul (σ : E ≃ₐ[ℚ] E) (I : Ideal (𝓞 E)) (z : E) :
    z ∈ (I : FractionalIdeal (𝓞 E)⁰ E) ↔
      σ z ∈ ((σ • I : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨σ • w, Ideal.smul_mem_pointwise_smul σ w I hw, rfl⟩
  · rintro ⟨w, hw, he⟩
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hw
    refine ⟨σ⁻¹ • w, hw, ?_⟩
    show σ⁻¹ (w : E) = z
    have he' : (w : E) = σ z := he
    rw [he']
    exact σ.symm_apply_apply z

/- English proof (translation)
Rewrite using `[← div_eq_mul_inv, ← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hJ), FractionalIdeal.mem_div_iff_of_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hJ')]`. Prove the components needed by the constructor for the conclusion. Introduce `h β' hβ'`. Establish `e : σ (σ.symm β') = β'` using `σ.apply_symm_apply β'`. Rewrite `hβ'`, the goal using `[← e]`.

Rewrite `hβ'` using `[← mem_coe_smul]`. Rewrite using `[← map_mul, ← mem_coe_smul]`. Conclude with `h _ hβ'`. Introduce `h β hβ`. Rewrite using `[mem_coe_smul σ, map_mul]`.

Conclude with `h _ ((mem_coe_smul σ J β).1 hβ)`.
-/
theorem mem_div_smul (σ : E ≃ₐ[ℚ] E) (I J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (hJ' : σ • J ≠ ⊥) (y : E) :
    y ∈ (I : FractionalIdeal (𝓞 E)⁰ E) * (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ↔
      σ y ∈ ((σ • I : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
        ((σ • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv,
    FractionalIdeal.mem_div_iff_of_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hJ),
    FractionalIdeal.mem_div_iff_of_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hJ')]
  constructor
  · intro h β' hβ'
    have e : σ (σ.symm β') = β' := σ.apply_symm_apply β'
    rw [← e] at hβ' ⊢
    rw [← mem_coe_smul] at hβ'
    rw [← map_mul, ← mem_coe_smul]
    exact h _ hβ'
  · intro h β hβ
    rw [mem_coe_smul σ, map_mul]
    exact h _ ((mem_coe_smul σ J β).1 hβ)

/- English proof (translation)
Set `φ0 : E →+* ℂ` to `Classical.arbitrary _`. Set `φ : E →ₐ[ℚ] ℂ` to `φ0.toRatAlgHom`. Set `τ1 : K →ₐ[ℚ] ℂ` to `φ.comp K.val`. Set `τ2 : K →ₐ[ℚ] ℂ` to `φ.comp ((σ : E →ₐ[ℚ] E).comp K.val)`. Establish `hne : τ1 ≠ τ2`.

Introduce `h`. Use `DFunLike.congr_fun h β` as an intermediate fact. Conclude with `hβ (φ.injective this).symm`. Establish `huniv : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) = {τ1, τ2}` using `(Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, AlgHom.card, hK])).symm`. Establish `h1` using `Algebra.norm_eq_prod_embeddings ℚ ℂ k`.

Rewrite `h1` using `[huniv, Finset.prod_pair hne]`. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_ratCast]`. Rewrite `h1` using `[eq_ratCast]`. Conclude with `h1`.
-/
theorem quadNorm (K : IntermediateField ℚ E) (hK : Module.finrank ℚ K = 2) (σ : E ≃ₐ[ℚ] E) (β : K)
    (hβ : σ (β : E) ≠ β) (k : K) : ((Algebra.norm ℚ k : ℚ) : E) = (k : E) * σ (k : E) := by
  classical
  let φ0 : E →+* ℂ := Classical.arbitrary _
  let φ : E →ₐ[ℚ] ℂ := φ0.toRatAlgHom
  let τ1 : K →ₐ[ℚ] ℂ := φ.comp K.val
  let τ2 : K →ₐ[ℚ] ℂ := φ.comp ((σ : E →ₐ[ℚ] E).comp K.val)
  have hne : τ1 ≠ τ2 := by
    intro h
    have := DFunLike.congr_fun h β
    exact hβ (φ.injective this).symm
  have huniv : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) = {τ1, τ2} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, AlgHom.card, hK])).symm
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ k
  rw [huniv, Finset.prod_pair hne] at h1
  apply φ.injective
  rw [map_mul, map_ratCast]
  rw [eq_ratCast] at h1
  exact h1

/- English proof (translation)
Establish `hnormE : ∀ z : 𝓞 K, (((Algebra.norm ℤ z : ℤ)) : E) = ((z : K) : E) * σ ((z : K) : E)`. Introduce `z`. Rewrite using `[← quadNorm K hK σ β hβ (z : K), ← Algebra.coe_norm_int z]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hnorm : ∀ z : 𝓞 K, (((Algebra.norm ℤ z : ℤ)) : 𝓞 E) = algebraMap (𝓞 K) (𝓞 E) z * σ • algebraMap (𝓞 K) (𝓞 E) z`. Introduce `z`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `hnormE z` as an intermediate fact. Use `show algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _`.

Rewrite using `[map_intCast, map_mul]`. Conclude with `this`. Establish `hN0 : ((Ideal.absNorm 𝔠 : ℕ) : E) ≠ 0`. Establish `: Ideal.absNorm 𝔠 ≠ 0` using `by rwa [ne_eq, Ideal.absNorm_eq_zero_iff]`. Conclude with `this` after adjusting the coercions.

Apply `le_antisymm` to reduce the goal to its premises. Establish `key : ∀ x ∈ 𝔠, ∀ y ∈ 𝔠, algebraMap (𝓞 K) (𝓞 E) x * σ • algebraMap (𝓞 K) (𝓞 E) y ∈ Ideal.span {((Ideal.absNorm 𝔠 : ℕ) : 𝓞 E)}`. Introduce `x hx y hy`. Take `⟨kx, hkx⟩` from `Ideal.absNorm_dvd_norm_of_mem hx`. Take `⟨ky, hky⟩` from `Ideal.absNorm_dvd_norm_of_mem hy`.

Take `⟨kxy, hkxy⟩` from `Ideal.absNorm_dvd_norm_of_mem (𝔠.add_mem hx hy)`. Establish `ex` using `hnormE x`. Establish `ey` using `hnormE y`. Establish `exy` using `hnormE (x + y)`. Rewrite `ex` using `[hkx]`.

Rewrite `ey` using `[hky]`. Rewrite `exy` using `[hkxy]`. Move the coercions through the operations in `at ex ey exy`. Rewrite `exy` using `[map_add]`. Take `⟨X, hX⟩ : ∃ X : E, X = ((x : K) : E)` from `⟨_, rfl⟩`.

Take `⟨Y, hY⟩ : ∃ Y : E, Y = ((y : K) : E)` from `⟨_, rfl⟩`. Take `⟨X', hX'⟩ : ∃ X' : E, X' = σ ((x : K) : E)` from `⟨_, rfl⟩`. Take `⟨Y', hY'⟩ : ∃ Y' : E, Y' = σ ((y : K) : E)` from `⟨_, rfl⟩`. Take `⟨N, hN⟩ : ∃ N : E, N = ((Ideal.absNorm 𝔠 : ℕ) : E)` from `⟨_, rfl⟩`. Rewrite `ex` using `[← hX', ← hX, ← hN]`.

Rewrite `ey` using `[← hY', ← hY, ← hN]`. Rewrite `exy` using `[← hX', ← hY', ← hX, ← hY, ← hN]`. Rewrite `hN0` using `[← hN]`. Establish `hkx' : (kx : E) = X * X' / N` using `by field_simp; linear_combination ex`. Establish `hky' : (ky : E) = Y * Y' / N` using `by field_simp; linear_combination ey`.

Establish `hkxy' : (kxy : E) = (X + Y) * (X' + Y') / N` using `by field_simp; linear_combination exy`. Establish `hint : IsIntegral ℤ (X * Y' / N)`. Take `⟨T, hT⟩ : ∃ T : ℤ, T = kxy - kx - ky` from `⟨_, rfl⟩`. Take `⟨M, hM⟩ : ∃ M : ℤ, M = kx * ky` from `⟨_, rfl⟩`. Use `⟨Polynomial.X ^ 2 - Polynomial.C T * Polynomial.X + Polynomial.C M, by monicity!, ?_⟩` and prove the remaining obligations.

Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]`. Simplify using `only [eq_intCast]`. Rewrite using `[hT, hM]`. Use `push_cast`. Rewrite using `[hkx', hky', hkxy']`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Ideal.mem_span_singleton']`. Take `⟨w, hw⟩ : ∃ w : 𝓞 E, algebraMap (𝓞 E) E w = X * Y' / N` from `⟨⟨_, hint⟩, rfl⟩`. Use `⟨w, ?_⟩` and prove the remaining obligations.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _`. Rewrite using `[map_mul, map_mul, map_natCast, hw]`. Use `show X * Y' / N * ((Ideal.absNorm 𝔠 : ℕ) : E) = ((x : K) : E) * σ ((y : K) : E)`. Rewrite using `[← hN, ← hX, ← hY']`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[Ideal.pointwise_smul_def, Ideal.map_map, Ideal.map, Ideal.map, Ideal.span_mul_span', Ideal.span_le]`. Introduce and unpack `_ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩`. Conclude with `key x hx y hy`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`.

Set `J : Ideal ℤ` to `Ideal.comap (algebraMap ℤ (𝓞 E)) (𝔠.map (algebraMap (𝓞 K) (𝓞 E)) * σ • (𝔠.map (algebraMap (𝓞 K) (𝓞 E))))`. Establish `hJ : Ideal.relNorm ℤ 𝔠 ≤ J`. Rewrite using `[Ideal.relNorm_apply, Ideal.span_le]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Use `Ideal.mem_comap.2 ?_` and prove the remaining obligations.

Rewrite using `[Algebra.intNorm_eq_norm, eq_intCast, hnorm]`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hz) (Ideal.smul_mem_pointwise_smul _ _ _ (Ideal.mem_map_of_mem _ hz))`. Rewrite `hJ` using `[Ideal.relNorm_int]`. Use `hJ (Ideal.mem_span_singleton_self _)` as an intermediate fact. Establish `h2 : algebraMap ℤ (𝓞 E) ((Ideal.absNorm 𝔠 : ℕ) : ℤ) ∈ (𝔠.map (algebraMap (𝓞 K) (𝓞 E)) * σ • (𝔠.map (algebraMap (𝓞 K) (𝓞 E))))` using `this`.

Simplify using `using h2`.
-/
theorem conjNorm (K : IntermediateField ℚ E) (hK : Module.finrank ℚ K = 2) (σ : E ≃ₐ[ℚ] E) (β : K)
    (hβ : σ (β : E) ≠ β) (𝔠 : Ideal (𝓞 K)) (h𝔠 : 𝔠 ≠ ⊥) :
    𝔠.map (algebraMap (𝓞 K) (𝓞 E)) * σ • (𝔠.map (algebraMap (𝓞 K) (𝓞 E))) =
      Ideal.span {((Ideal.absNorm 𝔠 : ℕ) : 𝓞 E)} := by
  have hnormE : ∀ z : 𝓞 K, (((Algebra.norm ℤ z : ℤ)) : E) = ((z : K) : E) * σ ((z : K) : E) := by
    intro z
    rw [← quadNorm K hK σ β hβ (z : K), ← Algebra.coe_norm_int z]
    push_cast; rfl
  have hnorm : ∀ z : 𝓞 K, (((Algebra.norm ℤ z : ℤ)) : 𝓞 E) =
      algebraMap (𝓞 K) (𝓞 E) z * σ • algebraMap (𝓞 K) (𝓞 E) z := by
    intro z
    apply RingOfIntegers.ext
    have := hnormE z
    show algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
    rw [map_intCast, map_mul]
    exact this
  have hN0 : ((Ideal.absNorm 𝔠 : ℕ) : E) ≠ 0 := by
    have : Ideal.absNorm 𝔠 ≠ 0 := by rwa [ne_eq, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast this
  apply le_antisymm
  · have key : ∀ x ∈ 𝔠, ∀ y ∈ 𝔠, algebraMap (𝓞 K) (𝓞 E) x * σ • algebraMap (𝓞 K) (𝓞 E) y ∈
        Ideal.span {((Ideal.absNorm 𝔠 : ℕ) : 𝓞 E)} := by
      intro x hx y hy
      obtain ⟨kx, hkx⟩ := Ideal.absNorm_dvd_norm_of_mem hx
      obtain ⟨ky, hky⟩ := Ideal.absNorm_dvd_norm_of_mem hy
      obtain ⟨kxy, hkxy⟩ := Ideal.absNorm_dvd_norm_of_mem (𝔠.add_mem hx hy)
      have ex := hnormE x
      have ey := hnormE y
      have exy := hnormE (x + y)
      rw [hkx] at ex
      rw [hky] at ey
      rw [hkxy] at exy
      push_cast at ex ey exy
      rw [map_add] at exy
      obtain ⟨X, hX⟩ : ∃ X : E, X = ((x : K) : E) := ⟨_, rfl⟩
      obtain ⟨Y, hY⟩ : ∃ Y : E, Y = ((y : K) : E) := ⟨_, rfl⟩
      obtain ⟨X', hX'⟩ : ∃ X' : E, X' = σ ((x : K) : E) := ⟨_, rfl⟩
      obtain ⟨Y', hY'⟩ : ∃ Y' : E, Y' = σ ((y : K) : E) := ⟨_, rfl⟩
      obtain ⟨N, hN⟩ : ∃ N : E, N = ((Ideal.absNorm 𝔠 : ℕ) : E) := ⟨_, rfl⟩
      rw [← hX', ← hX, ← hN] at ex
      rw [← hY', ← hY, ← hN] at ey
      rw [← hX', ← hY', ← hX, ← hY, ← hN] at exy
      rw [← hN] at hN0
      have hkx' : (kx : E) = X * X' / N := by field_simp; linear_combination ex
      have hky' : (ky : E) = Y * Y' / N := by field_simp; linear_combination ey
      have hkxy' : (kxy : E) = (X + Y) * (X' + Y') / N := by field_simp; linear_combination exy
      have hint : IsIntegral ℤ (X * Y' / N) := by
        obtain ⟨T, hT⟩ : ∃ T : ℤ, T = kxy - kx - ky := ⟨_, rfl⟩
        obtain ⟨M, hM⟩ : ∃ M : ℤ, M = kx * ky := ⟨_, rfl⟩
        refine ⟨Polynomial.X ^ 2 - Polynomial.C T * Polynomial.X + Polynomial.C M, by monicity!, ?_⟩
        simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C]
        simp only [eq_intCast]
        rw [hT, hM]
        push_cast
        rw [hkx', hky', hkxy']
        field_simp
        ring
      rw [Ideal.mem_span_singleton']
      obtain ⟨w, hw⟩ : ∃ w : 𝓞 E, algebraMap (𝓞 E) E w = X * Y' / N := ⟨⟨_, hint⟩, rfl⟩
      refine ⟨w, ?_⟩
      apply RingOfIntegers.ext
      show algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
      rw [map_mul, map_mul, map_natCast, hw]
      show X * Y' / N * ((Ideal.absNorm 𝔠 : ℕ) : E) = ((x : K) : E) * σ ((y : K) : E)
      rw [← hN, ← hX, ← hY']
      field_simp
    rw [Ideal.pointwise_smul_def, Ideal.map_map, Ideal.map, Ideal.map, Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact key x hx y hy
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    let J : Ideal ℤ := Ideal.comap (algebraMap ℤ (𝓞 E))
      (𝔠.map (algebraMap (𝓞 K) (𝓞 E)) * σ • (𝔠.map (algebraMap (𝓞 K) (𝓞 E))))
    have hJ : Ideal.relNorm ℤ 𝔠 ≤ J := by
      rw [Ideal.relNorm_apply, Ideal.span_le]
      rintro _ ⟨z, hz, rfl⟩
      refine Ideal.mem_comap.2 ?_
      rw [Algebra.intNorm_eq_norm, eq_intCast, hnorm]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hz)
        (Ideal.smul_mem_pointwise_smul _ _ _ (Ideal.mem_map_of_mem _ hz))
    rw [Ideal.relNorm_int] at hJ
    have := hJ (Ideal.mem_span_singleton_self _)
    have h2 : algebraMap ℤ (𝓞 E) ((Ideal.absNorm 𝔠 : ℕ) : ℤ) ∈
      (𝔠.map (algebraMap (𝓞 K) (𝓞 E)) * σ • (𝔠.map (algebraMap (𝓞 K) (𝓞 E)))) := this
    simpa using h2

end gen

section main
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HermitianLattices.FiltrationBoundaryCriterion

/- English proof (translation)
Simplify using `only [mul_inv, inv_inv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem algG {G : Type*} [CommGroupWithZero G] (cB cB' s cC cC' : G) (h1 : cB' ≠ 0) (h2 : cC ≠ 0) :
    (cB * cB' * s)⁻¹ * (cC' * cB'⁻¹)⁻¹ = (cC * cC' * s)⁻¹ * (cC * cB⁻¹) := by
  simp only [mul_inv, inv_inv]
  calc cB⁻¹ * cB'⁻¹ * s⁻¹ * (cC'⁻¹ * cB') = (cB'⁻¹ * cB') * (cB⁻¹ * s⁻¹ * cC'⁻¹) := by ac_rfl
    _ = (cC⁻¹ * cC) * (cB⁻¹ * s⁻¹ * cC'⁻¹) := by rw [inv_mul_cancel₀ h1, inv_mul_cancel₀ h2]
    _ = _ := by ac_rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `hb : σ (bE ζ a b) = - bE ζ a b`. Use `(hostGalSpec e q d hH.toHypOdd L ζ a b h σ).2.1` as an intermediate fact. Rewrite `this` using `[hσ]`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[this]`. Simplify using `[cc, c0, bE]`. Establish `h1` using `congrArg σ hξ`. Simplify using `only [map_mul, map_natCast, hb, map_neg, map_one] at h1`. Establish `hne : ((N : hostE ζ a b) * bE ζ a b) ≠ 0`.

Introduce `h0`. Rewrite `hξ` using `[h0]`. Simplify using `at hξ`. Establish `: (σ ξ + ξ) * ((N : hostE ζ a b) * bE ζ a b) = 0` using `by linear_combination hξ - h1`. Break down `mul_eq_zero.1 this with h2 | h2` into its components or cases.

Take the linear combination `h2`. Conclude with `absurd h2 hne`. Introduce `φ hφ`. Establish `hb : φ (bE ζ a b) = Complex.I * (Real.sqrt d : ℂ)` using `hφ`. Establish `h1` using `congrArg φ hξ`.

Simplify using `only [map_mul, map_natCast, hb, map_neg, map_one] at h1`. Establish `h2` using `congrArg Complex.re h1`. Simplify using `at h2`. Establish `hr : 0 ≤ (N : ℝ) * Real.sqrt d` using `by positivity`. Assume the negation of the conclusion as `hneg`.

Establish `hneg' : (φ ξ).im ≤ 0` using `not_lt.1 hneg`. Use `mul_nonpos_of_nonpos_of_nonneg hneg' hr` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem signs (e q d : ℕ) (hH : HostHyp q d)
    (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : galE e ζ a b σ = cc e) (N : ℕ)
    (ξ : hostE ζ a b) (hξ : ξ * ((N : hostE ζ a b) * bE ζ a b) = -1) :
    σ ξ = -ξ ∧ (∀ φ ∈ cmType ζ a b d, 0 < (φ ξ).im) := by
  constructor
  · have hb : σ (bE ζ a b) = - bE ζ a b := by
      have := (hostGalSpec e q d hH.toHypOdd L ζ a b h σ).2.1
      rw [hσ] at this
      apply Subtype.ext
      rw [this]
      simp [cc, c0, bE]
    have h1 := congrArg σ hξ
    simp only [map_mul, map_natCast, hb, map_neg, map_one] at h1
    have hne : ((N : hostE ζ a b) * bE ζ a b) ≠ 0 := by
      intro h0; rw [h0] at hξ; simp at hξ
    have : (σ ξ + ξ) * ((N : hostE ζ a b) * bE ζ a b) = 0 := by linear_combination hξ - h1
    rcases mul_eq_zero.1 this with h2 | h2
    · linear_combination h2
    · exact absurd h2 hne
  · intro φ hφ
    have hb : φ (bE ζ a b) = Complex.I * (Real.sqrt d : ℂ) := hφ
    have h1 := congrArg φ hξ
    simp only [map_mul, map_natCast, hb, map_neg, map_one] at h1
    have h2 := congrArg Complex.re h1
    simp at h2
    have hr : 0 ≤ (N : ℝ) * Real.sqrt d := by positivity
    by_contra hneg
    have hneg' : (φ ξ).im ≤ 0 := not_lt.1 hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg' hr
    linarith

/- English proof (translation)
Introduce `e q d hH L _ _ ζ a b h σ hσ 𝔟 h𝔟 𝔠 h𝔠 ξ hξ`. Take `⟨s1, s2⟩` from `signs e q d hH L ζ a b h σ hσ (Ideal.absNorm 𝔠) ξ hξ`. Use `⟨s1, s2, ?_⟩` and prove the remaining obligations. Introduce `x`. Establish `hsq : bE ζ a b ^ 2 = -(d : hostE ζ a b)` using `DiscrB.bE_sq h`.

Establish `hNb0 : ((Ideal.absNorm 𝔠 : ℕ) : hostE ζ a b) * bE ζ a b ≠ 0`. Introduce `h0`. Rewrite `hξ` using `[h0]`. Simplify using `at hξ`. Establish `hb0 : bE ζ a b ≠ 0` using `right_ne_zero_of_mul hNb0`.

Establish `hN0 : ((Ideal.absNorm 𝔠 : ℕ) : hostE ζ a b) ≠ 0` using `left_ne_zero_of_mul hNb0`. Establish `hσb : σ (bE ζ a b) = - bE ζ a b`. Use `(hostGalSpec e q d hH.toHypOdd L ζ a b h σ).2.1` as an intermediate fact. Rewrite `this` using `[hσ]`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[this]`. Simplify using `[cc, c0, bE]`. Establish `hK : Module.finrank ℚ (KinE ζ a b) = 2` using `Formalism.FrobeniusOrbits.SplitK.finrank_K (L := hostE ζ a b) (b := bE ζ a b) hH.2.1.pos hsq`. Establish `hCC` using `conjNorm (KinE ζ a b) hK σ ⟨bE ζ a b, Principal.bE_mem_KinE ζ a b⟩ (by show σ (bE ζ a b) ≠ bE ζ a b`. Rewrite using `[hσb]`.

Introduce `h1`. Apply `hb0` to reduce the goal to its premises. Take the linear combination `(-1 / 2 : hostE ζ a b) * h1) 𝔠 h𝔠`. Take `⟨β, hβ, hdiff⟩` from `difference_absolute_bound e q d hH L ζ a b h`. Take `⟨C, hC⟩ : ∃ C : Ideal (𝓞 (hostE ζ a b)), C = 𝔠.map (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)))` from `⟨_, rfl⟩`.

Rewrite `hCC`, the goal using `[← hC]`. Establish `hdne : differentIdeal ℤ (𝓞 (hostE ζ a b)) ≠ ⊥`. Introduce `h0`. Establish `h1 : (differentIdeal ℤ (𝓞 (hostE ζ a b))).absNorm = (discr (hostE ζ a b)).natAbs` using `absNorm_differentIdeal (hostE ζ a b) (𝓞 (hostE ζ a b))`. Rewrite `h1` using `[h0, Ideal.absNorm_bot]`.

Conclude with `NumberField.discr_ne_zero (hostE ζ a b) (Int.natAbs_eq_zero.1 h1.symm)`. Establish `hBB : 𝔟 * (σ • 𝔟) ≠ ⊥`. Introduce `h0`. Rewrite `hdne` using `[hdiff, h𝔟, h0]`. Simplify using `at hdne`.

Establish `hB : 𝔟 ≠ ⊥`. Introduce and unpack `rfl`. Simplify using `at hBB`. Establish `hB' : σ • 𝔟 ≠ ⊥`. Introduce `h0`.

Rewrite `hBB` using `[h0]`. Simplify using `at hBB`. Establish `hCCne : C * (σ • C) ≠ ⊥`. Rewrite using `[hCC, ne_eq, Ideal.span_singleton_eq_bot]`. Conclude with `hN0` after adjusting the coercions.

Establish `hC0 : C ≠ ⊥`. Introduce and unpack `rfl`. Simplify using `at hCCne`. Establish `hC' : σ • C ≠ ⊥`. Introduce `h0`.

Rewrite `hCCne` using `[h0]`. Simplify using `at hCCne`. Take `⟨cC, hcC⟩ : ∃ I : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b), I = (C : FractionalIdeal _ _)` from `⟨_, rfl⟩`. Take `⟨cB, hcB⟩ : ∃ I : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b), I = (𝔟 : FractionalIdeal _ _)` from `⟨_, rfl⟩`. Take `⟨cC', hcC'⟩ : ∃ I : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b), I = ((σ • C : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal _ _)` from `⟨_, rfl⟩`.

Take `⟨cB', hcB'⟩ : ∃ I : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b), I = ((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal _ _)` from `⟨_, rfl⟩`. Establish `ncC : cC ≠ 0` using `by rw [hcC]; exact FractionalIdeal.coeIdeal_ne_zero.2 hC0`. Establish `ncB : cB ≠ 0` using `by rw [hcB]; exact FractionalIdeal.coeIdeal_ne_zero.2 hB`. Establish `ncC' : cC' ≠ 0` using `by rw [hcC']; exact FractionalIdeal.coeIdeal_ne_zero.2 hC'`. Establish `ncB' : cB' ≠ 0` using `by rw [hcB']; exact FractionalIdeal.coeIdeal_ne_zero.2 hB'`.

Establish `hd : ((differentIdeal ℤ (𝓞 (hostE ζ a b)) : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) = cB * cB' * FractionalIdeal.spanSingleton _ (bE ζ a b)`. Rewrite using `[hdiff, h𝔟, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton, ← hcB, ← hcB']`. Use `congr 2`. Establish `hN : cC * cC' = FractionalIdeal.spanSingleton _ ((Ideal.absNorm 𝔠 : ℕ) : hostE ζ a b)`. Rewrite using `[hcC, hcC', ← FractionalIdeal.coeIdeal_mul, hCC, FractionalIdeal.coeIdeal_span_singleton]`.

Use `congr 1`. Establish `hdual1 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) = (cB * cB' * FractionalIdeal.spanSingleton _ (bE ζ a b))⁻¹`. Rewrite using `[← hd, coeIdeal_differentIdeal ℤ ℚ (hostE ζ a b) (𝓞 (hostE ζ a b)), inv_inv]`. Establish `hne' : cC' * cB'⁻¹ ≠ 0` using `mul_ne_zero ncC' (inv_ne_zero ncB')`. Establish `hdual : FractionalIdeal.dual ℤ ℚ (cC' * cB'⁻¹) = FractionalIdeal.spanSingleton _ ((((Ideal.absNorm 𝔠 : ℕ) : hostE ζ a b) * bE ζ a b)⁻¹) * (cC * cB⁻¹)`.

Rewrite using `[FractionalIdeal.dual_eq_mul_inv, hdual1, ← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← hN]`. Conclude with `algG _ _ _ _ _ ncB' ncC`. Rewrite using `[← hcC, ← hcB]`. Establish `step1 : (∀ y ∈ cC * cB⁻¹, Algebra.trace ℚ (hostE ζ a b) (ξ * x * σ y) ∈ (algebraMap ℤ ℚ).range) ↔ ξ * x ∈ FractionalIdeal.dual ℤ ℚ (cC' * cB'⁻¹)`. Rewrite using `[FractionalIdeal.mem_dual hne']`.

Prove the components needed by the constructor for the conclusion. Introduce `hy y' hy'`. Establish `e : σ (σ.symm y') = y'` using `σ.apply_symm_apply y'`. Rewrite using `[Algebra.traceForm_apply, ← e]`. Apply `hy` to reduce the goal to its premises.

Rewrite using `[hcC, hcB, mem_div_smul σ C 𝔟 hB hB', e, ← hcC', ← hcB']`. Conclude with `hy'`. Introduce `hy y hy'`. Use `hy (σ y) (by` as an intermediate fact. Rewrite using `[hcC', hcB', ← mem_div_smul σ C 𝔟 hB hB', ← hcC, ← hcB]`.

Conclude with `hy')`. Rewrite `this` using `[Algebra.traceForm_apply]`. Then use the resulting hypothesis. Rewrite using `[step1, hdual, FractionalIdeal.mem_singleton_mul]`. Establish `hξ' : ξ = -(((Ideal.absNorm 𝔠 : ℕ) : hostE ζ a b) * bE ζ a b)⁻¹`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `hξ`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨-x, fi_neg_mem hx, by rw [hξ']; ring⟩`. Introduce and unpack `⟨y', hy', he⟩`.

Establish `: x = -y'`. Rewrite `he` using `[hξ']`. Establish `h2` using `inv_ne_zero hNb0`. Apply `mul_left_cancel₀ h2` to reduce the goal to its premises. Take the linear combination `-he`.

Rewrite using `[this]`. Conclude with `fi_neg_mem hy'`.
-/
theorem principalRiemann : PrincipalRiemann := by
  intro e q d hH L _ _ ζ a b h σ hσ 𝔟 h𝔟 𝔠 h𝔠 ξ hξ
  obtain ⟨s1, s2⟩ := signs e q d hH L ζ a b h σ hσ (Ideal.absNorm 𝔠) ξ hξ
  refine ⟨s1, s2, ?_⟩
  intro x
  have hsq : bE ζ a b ^ 2 = -(d : hostE ζ a b) := DiscrB.bE_sq h
  have hNb0 : ((Ideal.absNorm 𝔠 : ℕ) : hostE ζ a b) * bE ζ a b ≠ 0 := by
    intro h0; rw [h0] at hξ; simp at hξ
  have hb0 : bE ζ a b ≠ 0 := right_ne_zero_of_mul hNb0
  have hN0 : ((Ideal.absNorm 𝔠 : ℕ) : hostE ζ a b) ≠ 0 := left_ne_zero_of_mul hNb0
  have hσb : σ (bE ζ a b) = - bE ζ a b := by
    have := (hostGalSpec e q d hH.toHypOdd L ζ a b h σ).2.1
    rw [hσ] at this
    apply Subtype.ext
    rw [this]
    simp [cc, c0, bE]
  have hK : Module.finrank ℚ (KinE ζ a b) = 2 :=
    Formalism.FrobeniusOrbits.SplitK.finrank_K (L := hostE ζ a b) (b := bE ζ a b) hH.2.1.pos hsq
  have hCC := conjNorm (KinE ζ a b) hK σ ⟨bE ζ a b, Principal.bE_mem_KinE ζ a b⟩
    (by
      show σ (bE ζ a b) ≠ bE ζ a b
      rw [hσb]
      intro h1
      apply hb0
      linear_combination (-1 / 2 : hostE ζ a b) * h1) 𝔠 h𝔠
  obtain ⟨β, hβ, hdiff⟩ := difference_absolute_bound e q d hH L ζ a b h
  obtain ⟨C, hC⟩ : ∃ C : Ideal (𝓞 (hostE ζ a b)),
    C = 𝔠.map (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) := ⟨_, rfl⟩
  rw [← hC] at hCC ⊢
  have hdne : differentIdeal ℤ (𝓞 (hostE ζ a b)) ≠ ⊥ := by
    intro h0
    have h1 : (differentIdeal ℤ (𝓞 (hostE ζ a b))).absNorm = (discr (hostE ζ a b)).natAbs :=
      absNorm_differentIdeal (hostE ζ a b) (𝓞 (hostE ζ a b))
    rw [h0, Ideal.absNorm_bot] at h1
    exact NumberField.discr_ne_zero (hostE ζ a b) (Int.natAbs_eq_zero.1 h1.symm)
  have hBB : 𝔟 * (σ • 𝔟) ≠ ⊥ := by
    intro h0
    rw [hdiff, h𝔟, h0] at hdne
    simp at hdne
  have hB : 𝔟 ≠ ⊥ := by
    rintro rfl; simp at hBB
  have hB' : σ • 𝔟 ≠ ⊥ := by
    intro h0; rw [h0] at hBB; simp at hBB
  have hCCne : C * (σ • C) ≠ ⊥ := by
    rw [hCC, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN0
  have hC0 : C ≠ ⊥ := by
    rintro rfl; simp at hCCne
  have hC' : σ • C ≠ ⊥ := by
    intro h0; rw [h0] at hCCne; simp at hCCne

  obtain ⟨cC, hcC⟩ : ∃ I : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b), I = (C : FractionalIdeal _ _) := ⟨_, rfl⟩
  obtain ⟨cB, hcB⟩ : ∃ I : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b), I = (𝔟 : FractionalIdeal _ _) := ⟨_, rfl⟩
  obtain ⟨cC', hcC'⟩ : ∃ I : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b),
    I = ((σ • C : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal _ _) := ⟨_, rfl⟩
  obtain ⟨cB', hcB'⟩ : ∃ I : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b),
    I = ((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal _ _) := ⟨_, rfl⟩
  have ncC : cC ≠ 0 := by rw [hcC]; exact FractionalIdeal.coeIdeal_ne_zero.2 hC0
  have ncB : cB ≠ 0 := by rw [hcB]; exact FractionalIdeal.coeIdeal_ne_zero.2 hB
  have ncC' : cC' ≠ 0 := by rw [hcC']; exact FractionalIdeal.coeIdeal_ne_zero.2 hC'
  have ncB' : cB' ≠ 0 := by rw [hcB']; exact FractionalIdeal.coeIdeal_ne_zero.2 hB'
  have hd : ((differentIdeal ℤ (𝓞 (hostE ζ a b)) : Ideal (𝓞 (hostE ζ a b))) :
      FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) =
      cB * cB' * FractionalIdeal.spanSingleton _ (bE ζ a b) := by
    rw [hdiff, h𝔟, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_span_singleton, ← hcB, ← hcB']
    congr 2
  have hN : cC * cC' = FractionalIdeal.spanSingleton _ ((Ideal.absNorm 𝔠 : ℕ) : hostE ζ a b) := by
    rw [hcC, hcC', ← FractionalIdeal.coeIdeal_mul, hCC, FractionalIdeal.coeIdeal_span_singleton]
    congr 1
  have hdual1 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) =
      (cB * cB' * FractionalIdeal.spanSingleton _ (bE ζ a b))⁻¹ := by
    rw [← hd, coeIdeal_differentIdeal ℤ ℚ (hostE ζ a b) (𝓞 (hostE ζ a b)), inv_inv]
  have hne' : cC' * cB'⁻¹ ≠ 0 := mul_ne_zero ncC' (inv_ne_zero ncB')
  have hdual : FractionalIdeal.dual ℤ ℚ (cC' * cB'⁻¹) =
      FractionalIdeal.spanSingleton _ ((((Ideal.absNorm 𝔠 : ℕ) : hostE ζ a b) * bE ζ a b)⁻¹) * (cC * cB⁻¹) := by
    rw [FractionalIdeal.dual_eq_mul_inv, hdual1, ← FractionalIdeal.spanSingleton_inv,
      ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← hN]
    exact algG _ _ _ _ _ ncB' ncC
  rw [← hcC, ← hcB]
  have step1 : (∀ y ∈ cC * cB⁻¹, Algebra.trace ℚ (hostE ζ a b) (ξ * x * σ y) ∈ (algebraMap ℤ ℚ).range) ↔
      ξ * x ∈ FractionalIdeal.dual ℤ ℚ (cC' * cB'⁻¹) := by
    rw [FractionalIdeal.mem_dual hne']
    constructor
    · intro hy y' hy'
      have e : σ (σ.symm y') = y' := σ.apply_symm_apply y'
      rw [Algebra.traceForm_apply, ← e]
      apply hy
      rw [hcC, hcB, mem_div_smul σ C 𝔟 hB hB', e, ← hcC', ← hcB']
      exact hy'
    · intro hy y hy'
      have := hy (σ y) (by
        rw [hcC', hcB', ← mem_div_smul σ C 𝔟 hB hB', ← hcC, ← hcB]; exact hy')
      rwa [Algebra.traceForm_apply] at this
  rw [step1, hdual, FractionalIdeal.mem_singleton_mul]
  have hξ' : ξ = -(((Ideal.absNorm 𝔠 : ℕ) : hostE ζ a b) * bE ζ a b)⁻¹ := by
    field_simp
    linear_combination hξ
  constructor
  · intro hx
    exact ⟨-x, fi_neg_mem hx, by rw [hξ']; ring⟩
  · rintro ⟨y', hy', he⟩
    have : x = -y' := by
      rw [hξ'] at he
      have h2 := inv_ne_zero hNb0
      apply mul_left_cancel₀ h2
      linear_combination -he
    rw [this]
    exact fi_neg_mem hy'

end main

end S3

end PfB

/- English proof (translation)
The claim follows from `PfB.hostEOverF`.
-/
theorem extension_over_base_field : HostEOverF := PfB.hostEOverF
/- English proof (translation)
The claim follows from `PfB.hostQuadSub`.
-/
theorem quadratic_subfield_exists : HostQuadSub := PfB.hostQuadSub
/- English proof (translation)
The claim follows from `PfB.congruenceTorsion`.
-/
theorem congruence_subgroup_torsion_free : CongruenceTorsion := PfB.congruenceTorsion
/- English proof (translation)
The claim follows from `PfB.unipotentPowers`.
-/
theorem unipotent_powers_bound : UnipotentPowers := PfB.unipotentPowers
/- English proof (translation)
The claim follows from `PfB.nilpotentPowers`.
-/
theorem nilpotent_powers_bound : NilpotentPowers := PfB.nilpotentPowers
/- English proof (translation)
The claim follows from `PfB.stabLevelProG`.
-/
theorem stabilizer_level_profinite : StabLevelProG := PfB.stabLevelProG
/- English proof (translation)
The claim follows from `PfB.stabG_of_proG PfB.stabLevelProG`.
-/
theorem stabilizer_level_of_group : StabLevelG := PfB.stabG_of_proG PfB.stabLevelProG
/- English proof (translation)
The claim follows from `PfB.formsExact`.
-/
theorem exact_sequence_of_forms : FormsExact := PfB.formsExact
/- English proof (translation)
The claim follows from `PfB.principalRiemann`.
-/
theorem principal_riemann_relation : PrincipalRiemann := PfB.principalRiemann

end Formalism.HermitianLattices.StabilizerLevels
