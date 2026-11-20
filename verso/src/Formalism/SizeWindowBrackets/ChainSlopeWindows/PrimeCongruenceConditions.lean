import Formalism.SizeWindowBrackets.SmoothedRemainderRealIntegralFormula
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

open Finset Filter Topology ArithmeticFunction DirichletCharacter

noncomputable section

namespace Formalism.LFunctionChainParameters.LBr2

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2

/- English proof (translation)
Introduce `e q d _ _ ψ`. Both sides reduce to the same expression.
-/
theorem ell_is_log_derivative : EllIsLD1 := by
  intro e q d _ _ ψ
  rfl

/- English proof (translation)
Introduce `y`. Unfold `Gz Sz G1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem g_zeta_eq_g_one : GrowthFunctionEqTrivial := by
  intro y
  unfold Gz Sz G1
  ring

/- English proof (translation)
Introduce `e q d _ _ ell ψ hψ hell y`. Unfold `GPsi Gchi`. Rewrite using `[if_neg hψ, hell]`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `n hn`. Establish `hn0 : n ≠ 0`. Use `(Finset.mem_Icc.1 hn).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h` using `primitive_value_primitive (H := HA e) (hostN e q d) q d (recMap e q d) ψ n (NeZero.ne _) hn0`.

Rewrite using `[show primVal (hostData e q d) ψ n = _ from h]`. Both sides reduce to the same expression.
-/
theorem g_psi_eq_g_chi : GPsiIsGchi := by
  intro e q d _ _ ell ψ hψ hell y
  unfold GPsi Gchi
  rw [if_neg hψ, hell]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    have := (Finset.mem_Icc.1 hn).1
    omega
  have h := primitive_value_primitive (H := HA e) (hostN e q d) q d (recMap e q d) ψ n (NeZero.ne _) hn0
  rw [show primVal (hostData e q d) ψ n = _ from h]
  rfl

/- English proof (translation)
Introduce `e q d _ _`. Use `⟨fun ψ hψ y => g_psi_eq_g_chi e q d _ ψ hψ (ell_is_log_derivative e q d ψ) y, fun y => ?_⟩` and prove the remaining obligations. Unfold `GPsi`. Rewrite using `[if_pos rfl, g_zeta_eq_g_one y]`.
-/
theorem g_psi_at_modulus : GPsiHost := by
  intro e q d _ _
  refine ⟨fun ψ hψ y => g_psi_eq_g_chi e q d _ ψ hψ (ell_is_log_derivative e q d ψ) y, fun y => ?_⟩
  unfold GPsi
  rw [if_pos rfl, g_zeta_eq_g_one y]

/- English proof (translation)
Apply `MulChar.ext` to reduce the goal to its premises. Introduce `u`. Rewrite using `[dirChar_unit, MulChar.one_apply_coe]`. Both sides reduce to the same expression.
-/
lemma dirChar_zero (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    dirChar (recMap e q d) (0 : AddChar (E0 × HA e) ℂ) = 1 := by
  apply MulChar.ext
  intro u
  rw [dirChar_unit, MulChar.one_apply_coe]
  rfl

/- English proof (translation)
Introduce `e q d _ _ h ψ`. Use `⟨primitiveCharacter_isPrimitive _, ⟨conductor_dvd_level _, changeLevel_primitiveCharacter _⟩, fun hψ => ?_⟩` and prove the remaining obligations. Establish `hne : dirChar (recMap e q d) ψ ≠ 1`. Introduce `h1`. Rewrite `h1` using `[← dirChar_zero e q d]`.

Conclude with `hψ (dirichlet_character_injective e q d h h1)`. Establish `hc : condOf e q d ψ ≠ 1` using `fun h1 => hne (eq_one_iff_conductor_eq_one.2 h1)`. Use `⟨fun h1 => hne ?_, hc⟩` and prove the remaining obligations. Establish `h2` using `changeLevel_primitiveCharacter (dirChar (recMap e q d) ψ)`. Rewrite `h2` using `[show (dirChar (recMap e q d) ψ).primitiveCharacter = 1 from h1, changeLevel_one]`.

Conclude with `h2.symm`.
-/
theorem character_of_facts : ChiOfFacts := by
  intro e q d _ _ h ψ
  refine ⟨primitiveCharacter_isPrimitive _, ⟨conductor_dvd_level _, changeLevel_primitiveCharacter _⟩, fun hψ => ?_⟩
  have hne : dirChar (recMap e q d) ψ ≠ 1 := by
    intro h1
    rw [← dirChar_zero e q d] at h1
    exact hψ (dirichlet_character_injective e q d h h1)
  have hc : condOf e q d ψ ≠ 1 := fun h1 => hne (eq_one_iff_conductor_eq_one.2 h1)
  refine ⟨fun h1 => hne ?_, hc⟩
  have h2 := changeLevel_primitiveCharacter (dirChar (recMap e q d) ψ)
  rw [show (dirChar (recMap e q d) ψ).primitiveCharacter = 1 from h1, changeLevel_one] at h2
  exact h2.symm

/- English proof (translation)
Introduce `e q d _ _ X' θ`. Take `⟨h1, h0⟩` from `g_psi_at_modulus e q d`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun ψ hψ y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations.

Rewrite using `[← h1 ψ hψ y]`. Conclude with `h ψ y hy`. Use `h 0 y hy` as an intermediate fact. Rewrite `this` using `[h0 y, Complex.norm_real, Real.norm_eq_abs]`. Then use the resulting hypothesis. Introduce and unpack `⟨hA, hB⟩ ψ y hy`.

Distinguish the cases in `hψ : ψ = 0`. Substitute `hψ` using the available equality. Rewrite using `[h0 y, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `hB y hy`. Rewrite using `[h1 ψ hψ y]`.

Conclude with `hA ψ hψ y hy`.
-/
theorem thin_iff : ThinIff := by
  intro e q d _ _ X' θ
  obtain ⟨h1, h0⟩ := g_psi_at_modulus e q d
  constructor
  · intro h
    refine ⟨fun ψ hψ y hy => ?_, fun y hy => ?_⟩
    · rw [← h1 ψ hψ y]
      exact h ψ y hy
    · have := h 0 y hy
      rwa [h0 y, Complex.norm_real, Real.norm_eq_abs] at this
  · rintro ⟨hA, hB⟩ ψ y hy
    by_cases hψ : ψ = 0
    · subst hψ
      rw [h0 y, Complex.norm_real, Real.norm_eq_abs]
      exact hB y hy
    · rw [h1 ψ hψ y]
      exact hA ψ hψ y hy

/- English proof (translation)
Apply `DFunLike.ext` to reduce the goal to its premises. Introduce `a`. Use `h.2 a.val` as an intermediate fact. Rewrite `this` using `[ZMod.natCast_zmod_val]`. Then use the resulting hypothesis.
-/
lemma sameChar_eq {N : ℕ} [NeZero N] {χ χ' : DirichletCharacter ℂ N} (h : SameChar χ χ') : χ = χ' := by
  apply DFunLike.ext
  intro a
  have := h.2 a.val
  rwa [ZMod.natCast_zmod_val] at this

/- English proof (translation)
Introduce `N M _ _ χ χ' h`. Take `⟨rfl, -⟩` from `id h`. Take `rfl` from `sameChar_eq h`. Conclude with `⟨rfl, fun _ => rfl, fun _ => rfl, rfl, Iff.rfl⟩`.
-/
theorem same_character_g : SameCharG := by
  intro N M _ _ χ χ' h
  obtain ⟨rfl, -⟩ := id h
  obtain rfl := sameChar_eq h
  exact ⟨rfl, fun _ => rfl, fun _ => rfl, rfl, Iff.rfl⟩

/- English proof (translation)
Establish `hc : χ.conductor = M`. Rewrite using `[hχ, conductor_changeLevel]`. Conclude with `hp`. Establish `key : ∀ (c : ℕ) (χ₀ : DirichletCharacter ℂ c) (hcN : c ∣ N), changeLevel hcN χ₀ = χ → c = M → SameChar χ₀ χ'`. Introduce `c χ₀ hcN h1 h2`.

Substitute `h2` using the available equality. Establish `h3 : χ₀ = χ'` using `changeLevel_injective hcN (h1.trans hχ)`. Substitute `h3` using the available equality. Conclude with `⟨rfl, fun _ => rfl⟩`. Conclude with `key _ _ (conductor_dvd_level χ) (changeLevel_primitiveCharacter χ) hc`.
-/
lemma sameChar_prim {N M : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hM : M ∣ N) (χ' : DirichletCharacter ℂ M)
    (hp : χ'.IsPrimitive) (hχ : χ = changeLevel hM χ') : SameChar χ.primitiveCharacter χ' := by
  have hc : χ.conductor = M := by
    rw [hχ, conductor_changeLevel]
    exact hp
  have key : ∀ (c : ℕ) (χ₀ : DirichletCharacter ℂ c) (hcN : c ∣ N), changeLevel hcN χ₀ = χ → c = M →
      SameChar χ₀ χ' := by
    intro c χ₀ hcN h1 h2
    subst h2
    have h3 : χ₀ = χ' := changeLevel_injective hcN (h1.trans hχ)
    subst h3
    exact ⟨rfl, fun _ => rfl⟩
  exact key _ _ (conductor_dvd_level χ) (changeLevel_primitiveCharacter χ) hc

/- English proof (translation)
Introduce `h`. Take `⟨a, ha⟩` from `quadraticChar_exists_neg_one' (F := ZMod q) (by rw [ZMod.ringChar_zmod_n]; exact h2)`. Establish `h1` using `DFunLike.congr_fun h (a : ZMod q)`. Rewrite `h1` using `[qc, MulChar.ringHomComp_apply, ha, MulChar.one_apply_coe]`. Evaluate the numerical expressions using `at h1`.
-/
lemma qc_ne_one (q : ℕ) [Fact q.Prime] (h2 : q ≠ 2) : qc q ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod q) (by rw [ZMod.ringChar_zmod_n]; exact h2)
  have h1 := DFunLike.congr_fun h (a : ZMod q)
  rw [qc, MulChar.ringHomComp_apply, ha, MulChar.one_apply_coe] at h1
  norm_num at h1

/- English proof (translation)
Rewrite using `[isPrimitive_def]`. Establish `hd` using `conductor_dvd_level (qc q)`. Break down `(Nat.dvd_prime Fact.out).1 hd with h | h` into its components or cases. Conclude with `absurd (eq_one_iff_conductor_eq_one.2 h) (qc_ne_one q h2)`. Conclude with `h`.
-/
lemma qc_prim (q : ℕ) [Fact q.Prime] (h2 : q ≠ 2) : (qc q).IsPrimitive := by
  rw [isPrimitive_def]
  have hd := conductor_dvd_level (qc q)
  rcases (Nat.dvd_prime Fact.out).1 hd with h | h
  · exact absurd (eq_one_iff_conductor_eq_one.2 h) (qc_ne_one q h2)
  · exact h

/- English proof (translation)
The claim follows from `((quadraticChar_isQuadratic (ZMod q)).comp (Int.castRingHom ℂ)).sq_eq_one`.
-/
lemma qc_sq (q : ℕ) [Fact q.Prime] : qc q ^ 2 = 1 :=
  ((quadraticChar_isQuadratic (ZMod q)).comp (Int.castRingHom ℂ)).sq_eq_one

/- English proof (translation)
Establish `cA : (changeLevel hm χ₁).conductor = m` using `by rw [conductor_changeLevel]; exact h1`. Establish `cB : (changeLevel hn χ₂).conductor = n` using `by rw [conductor_changeLevel]; exact h2`. Generalize the expression as in `changeLevel hm χ₁ = A at *`. Generalize the expression as in `changeLevel hn χ₂ = B at *`. Establish `d1 : m ∣ (A * B).conductor.lcm n`.

Establish `h` using `conductor_mul_dvd_lcm_conductor (A * B) B⁻¹`. Rewrite `h` using `[mul_inv_cancel_right, conductor_inv, cA, cB]`. Then use the resulting hypothesis. Establish `d2 : n ∣ (A * B).conductor.lcm m`. Establish `h` using `conductor_mul_dvd_lcm_conductor (B * A) A⁻¹`. Rewrite `h` using `[mul_inv_cancel_right, conductor_inv, cA, cB, mul_comm B A]`. Then use the resulting hypothesis.

Establish `e1 : m ∣ (A * B).conductor` using `hco.dvd_of_dvd_mul_right (d1.trans (Nat.lcm_dvd_mul _ _))`. Establish `e2 : n ∣ (A * B).conductor` using `hco.symm.dvd_of_dvd_mul_right (d2.trans (Nat.lcm_dvd_mul _ _))`. Rewrite using `[isPrimitive_def]`. Establish `e3 : N ∣ (A * B).conductor`. Establish `h` using `hco.mul_dvd_of_dvd_of_dvd e1 e2`.

Rewrite `h` using `[← hN]`. Then use the resulting hypothesis. Conclude with `Nat.dvd_antisymm (conductor_dvd_level _) e3`.
-/
lemma prim_mul {N m n : ℕ} [NeZero N] (hm : m ∣ N) (hn : n ∣ N) (hco : m.Coprime n) (hN : N = m * n)
    (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n) (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (changeLevel hm χ₁ * changeLevel hn χ₂).IsPrimitive := by
  have cA : (changeLevel hm χ₁).conductor = m := by rw [conductor_changeLevel]; exact h1
  have cB : (changeLevel hn χ₂).conductor = n := by rw [conductor_changeLevel]; exact h2
  generalize changeLevel hm χ₁ = A at *
  generalize changeLevel hn χ₂ = B at *
  have d1 : m ∣ (A * B).conductor.lcm n := by
    have h := conductor_mul_dvd_lcm_conductor (A * B) B⁻¹
    rwa [mul_inv_cancel_right, conductor_inv, cA, cB] at h
  have d2 : n ∣ (A * B).conductor.lcm m := by
    have h := conductor_mul_dvd_lcm_conductor (B * A) A⁻¹
    rwa [mul_inv_cancel_right, conductor_inv, cA, cB, mul_comm B A] at h
  have e1 : m ∣ (A * B).conductor :=
    hco.dvd_of_dvd_mul_right (d1.trans (Nat.lcm_dvd_mul _ _))
  have e2 : n ∣ (A * B).conductor :=
    hco.symm.dvd_of_dvd_mul_right (d2.trans (Nat.lcm_dvd_mul _ _))
  rw [isPrimitive_def]
  have e3 : N ∣ (A * B).conductor := by
    have h := hco.mul_dvd_of_dvd_of_dvd e1 e2
    rwa [← hN] at h
  exact Nat.dvd_antisymm (conductor_dvd_level _) e3

/- English proof (translation)
The claim follows from `(ZMod.isQuadratic_χ₈.comp (Int.castRingHom ℂ)).sq_eq_one`.
-/
lemma chi_eight_sq : chi8 ^ 2 = 1 :=
  (ZMod.isQuadratic_χ₈.comp (Int.castRingHom ℂ)).sq_eq_one

/- English proof (translation)
Rewrite using `[isPrimitive_def]`. Assume the negation of the conclusion as `hne`. Establish `hd` using `conductor_dvd_level chi8`. Establish `h4 : chi8.conductor ∣ 4`. Establish `hle : chi8.conductor ≤ 8` using `Nat.le_of_dvd (by norm_num) hd`.

Generalize the expression as in `chi8.conductor = k at *`. Apply the tactic sequence `interval_cases k <;> omega`. Take `⟨hd4, χ₀, h0⟩ : chi8.FactorsThrough 4` from `(mem_conductorSet_iff_conductor_dvd _ (by norm_num)).2 h4`. Establish `h5 : changeLevel hd4 χ₀ ((5 : ℤ) : ZMod 8) = χ₀ ((5 : ℤ) : ZMod 4)` using `changeLevel_eq_cast_of_dvd' χ₀ hd4 (by`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`.

Use the proof step `decide)`. Rewrite `h5` using `[← h0]`. Establish `h6 : ((5 : ℤ) : ZMod 4) = 1` using `by decide`. Establish `h7 : ZMod.χ₈ ((5 : ℤ) : ZMod 8) = -1` using `by decide`. Rewrite `h5` using `[h6, map_one, chi8, MulChar.ringHomComp_apply, h7]`.

Evaluate the numerical expressions using `at h5`.
-/
lemma chi_eight_primitive : chi8.IsPrimitive := by
  rw [isPrimitive_def]
  by_contra hne
  have hd := conductor_dvd_level chi8
  have h4 : chi8.conductor ∣ 4 := by
    have hle : chi8.conductor ≤ 8 := Nat.le_of_dvd (by norm_num) hd
    generalize chi8.conductor = k at *
    interval_cases k <;> omega
  obtain ⟨hd4, χ₀, h0⟩ : chi8.FactorsThrough 4 :=
    (mem_conductorSet_iff_conductor_dvd _ (by norm_num)).2 h4
  have h5 : changeLevel hd4 χ₀ ((5 : ℤ) : ZMod 8) = χ₀ ((5 : ℤ) : ZMod 4) :=
    changeLevel_eq_cast_of_dvd' χ₀ hd4 (by
      rw [Int.isCoprime_iff_gcd_eq_one]; decide)
  rw [← h0] at h5
  have h6 : ((5 : ℤ) : ZMod 4) = 1 := by decide
  have h7 : ZMod.χ₈ ((5 : ℤ) : ZMod 8) = -1 := by decide
  rw [h6, map_one, chi8, MulChar.ringHomComp_apply, h7] at h5
  norm_num at h5

/- English proof (translation)
Use `⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩` and prove the remaining obligations. Introduce `t θ q _ hθ h2 hco`. Establish `hq : q.Prime` using `Fact.out`. Establish `ht : t ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hco` using `[Nat.coprime_zero_right]`. Conclude with `hq.one_lt.ne' hco`. Establish `: NeZero t` using `⟨ht⟩`. Establish `hp : (tw θ q).IsPrimitive` using `prim_mul _ _ hco.symm rfl θ (qc q) hθ (qc_prim q h2)`. Use `⟨hp, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h1`. Rewrite `hp` using `[isPrimitive_def, h1, conductor_one]`. Establish `h3 : 2 ≤ q` using `hq.two_le`. Establish `h4 : 1 ≤ t` using `Nat.pos_of_ne_zero ht`. Use the polynomial consequences of the given equalities and inequalities.

Introduce `hs`. Rewrite using `[tw, mul_pow, ← map_pow, ← map_pow, hs, qc_sq, map_one, map_one, one_mul]`.
-/
theorem twist_primitive : TwPrimitive := by
  refine ⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩
  intro t θ q _ hθ h2 hco
  have hq : q.Prime := Fact.out
  have ht : t ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_right] at hco
    exact hq.one_lt.ne' hco
  have : NeZero t := ⟨ht⟩
  have hp : (tw θ q).IsPrimitive :=
    prim_mul _ _ hco.symm rfl θ (qc q) hθ (qc_prim q h2)
  refine ⟨hp, ?_, ?_⟩
  · intro h1
    rw [isPrimitive_def, h1, conductor_one] at hp
    have h3 : 2 ≤ q := hq.two_le
    have h4 : 1 ≤ t := Nat.pos_of_ne_zero ht
    nlinarith
  · intro hs
    rw [tw, mul_pow, ← map_pow, ← map_pow, hs, qc_sq, map_one, map_one, one_mul]

section Host
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

/- English proof (translation)
Rewrite using `[changeLevel_eq_cast_of_dvd]`. Unfold `qc`. Rewrite using `[MulChar.ringHomComp_apply]`. Simplify using `[ZMod.unitsMap_val]`.
-/
lemma qcLift_apply {N l : ℕ} [Fact l.Prime] (h : l ∣ N) (u : (ZMod N)ˣ) :
    changeLevel h (qc l) (u : ZMod N)
      = ((((quadraticChar (ZMod l)).toUnitHom (ZMod.unitsMap h u) : ℤˣ) : ℤ) : ℂ) := by
  rw [changeLevel_eq_cast_of_dvd]
  unfold qc
  rw [MulChar.ringHomComp_apply]
  simp [ZMod.unitsMap_val]

/- English proof (translation)
Unfold `tw`. Rewrite using `[map_mul, ← changeLevel_trans, ← changeLevel_trans]`.
-/
lemma tw_lift {N t l : ℕ} [Fact l.Prime] (θ : DirichletCharacter ℂ t) (h : t * l ∣ N) :
    changeLevel h (tw θ l) = changeLevel ((Dvd.intro l rfl).trans h) θ
      * changeLevel ((Dvd.intro_left t rfl).trans h) (qc l) := by
  unfold tw
  rw [map_mul, ← changeLevel_trans, ← changeLevel_trans]

/- English proof (translation)
Rewrite using `[← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
lemma psi_split (ψ : AddChar (E0 × HA e) ℂ) (a b : ZMod 2) (t : HA e) :
    ψ ((a, b), t) = ψ ((0, 0), t) * ψ ((0, b), 0) * ψ ((a, 0), 0) := by
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  simp

/- English proof (translation)
Establish `: ψ g * ψ g = 1` using `by rw [← AddChar.map_add_eq_mul, hg, AddChar.map_zero_eq_one]`. Conclude with `mul_self_eq_one_iff.1 this`.
-/
lemma psi_pm (ψ : AddChar (E0 × HA e) ℂ) (g : E0 × HA e) (hg : g + g = 0) : ψ g = 1 ∨ ψ g = -1 := by
  have : ψ g * ψ g = 1 := by rw [← AddChar.map_add_eq_mul, hg, AddChar.map_zero_eq_one]
  exact mul_self_eq_one_iff.1 this

/- English proof (translation)
Break down `zmod_two_eq_zero_or_eq_one a with rfl | rfl` into its components or cases. Rewrite using `[f0, AddChar.map_zero_eq_one]`. Conclude with `h1`.
-/
lemma comp_one (ψ : AddChar (E0 × HA e) ℂ) (f : ZMod 2 → E0 × HA e) (f0 : f 0 = 0) (h1 : ψ (f 1) = 1) (a : ZMod 2) :
    ψ (f a) = 1 := by
  rcases zmod_two_eq_zero_or_eq_one a with rfl | rfl
  · rw [f0, AddChar.map_zero_eq_one]
  · exact h1

/- English proof (translation)
Break down `Int.units_eq_one_or s with rfl | rfl` into its components or cases. Rewrite using `[map_one, toAdd_one, f0, AddChar.map_zero_eq_one]`. Simplify using the standard rewrite rules. Establish `: Multiplicative.toAdd (LHost.sgn2 (-1)) = 1` using `by decide`. Rewrite using `[this, h1]`.

Simplify using the standard rewrite rules.
-/
lemma comp_neg (ψ : AddChar (E0 × HA e) ℂ) (f : ZMod 2 → E0 × HA e) (f0 : f 0 = 0) (h1 : ψ (f 1) = -1) (s : ℤˣ) :
    ψ (f (Multiplicative.toAdd (LHost.sgn2 s))) = ((s : ℤ) : ℂ) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [map_one, toAdd_one, f0, AddChar.map_zero_eq_one]
    simp
  · have : Multiplicative.toAdd (LHost.sgn2 (-1)) = 1 := by decide
    rw [this, h1]
    simp

/- English proof (translation)
Apply `MulChar.ext` to reduce the goal to its premises. Introduce `u`. Rewrite using `[dirChar_unit, recMap_apply, psi_split, MulChar.mul_apply, MulChar.mul_apply, h2, hq, hd]`.
-/
lemma dirChar_prod (ψ : AddChar (E0 × HA e) ℂ) (D2 Dq Dd : DirichletCharacter ℂ (hostN e q d))
    (h2 : ∀ u : (ZMod (hostN e q d))ˣ, D2 (u : ZMod _)
      = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))))
    (hq : ∀ u : (ZMod (hostN e q d))ˣ, Dq (u : ZMod _) = ψ ((0, sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)), 0))
    (hd : ∀ u : (ZMod (hostN e q d))ˣ, Dd (u : ZMod _) = ψ ((sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u), 0), 0)) :
    dirChar (recMap e q d) ψ = D2 * Dq * Dd := by
  apply MulChar.ext
  intro u
  rw [dirChar_unit, recMap_apply, psi_split, MulChar.mul_apply, MulChar.mul_apply, h2, hq, hd]

/- English proof (translation)
Rewrite using `[MulChar.one_apply_coe, comp_one ψ (fun a => ((0, a), 0)) rfl h1]`.
-/
lemma compQ_one (ψ : AddChar (E0 × HA e) ℂ) (h1 : ψ ((0, 1), 0) = 1) (u : (ZMod (hostN e q d))ˣ) :
    (1 : DirichletCharacter ℂ (hostN e q d)) (u : ZMod _)
      = ψ ((0, sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)), 0) := by
  rw [MulChar.one_apply_coe, comp_one ψ (fun a => ((0, a), 0)) rfl h1]

/- English proof (translation)
Rewrite using `[MulChar.one_apply_coe, comp_one ψ (fun a => ((a, 0), 0)) rfl h1]`.
-/
lemma compD_one (ψ : AddChar (E0 × HA e) ℂ) (h1 : ψ ((1, 0), 0) = 1) (u : (ZMod (hostN e q d))ˣ) :
    (1 : DirichletCharacter ℂ (hostN e q d)) (u : ZMod _)
      = ψ ((sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u), 0), 0) := by
  rw [MulChar.one_apply_coe, comp_one ψ (fun a => ((a, 0), 0)) rfl h1]

/- English proof (translation)
Rewrite using `[qcLift_apply]`. Conclude with `(comp_neg ψ (fun a => ((0, a), 0)) rfl h1 _).symm`.
-/
lemma compQ_neg (ψ : AddChar (E0 × HA e) ℂ) (h1 : ψ ((0, 1), 0) = -1) (u : (ZMod (hostN e q d))ˣ) :
    changeLevel (q_dvd_hostN e q d) (qc q) (u : ZMod _)
      = ψ ((0, sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)), 0) := by
  rw [qcLift_apply]
  exact (comp_neg ψ (fun a => ((0, a), 0)) rfl h1 _).symm

/- English proof (translation)
Rewrite using `[qcLift_apply]`. Conclude with `(comp_neg ψ (fun a => ((a, 0), 0)) rfl h1 _).symm`.
-/
lemma compD_neg (ψ : AddChar (E0 × HA e) ℂ) (h1 : ψ ((1, 0), 0) = -1) (u : (ZMod (hostN e q d))ˣ) :
    changeLevel (d_dvd_hostN e q d) (qc d) (u : ZMod _)
      = ψ ((sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u), 0), 0) := by
  rw [qcLift_apply]
  exact (comp_neg ψ (fun a => ((a, 0), 0)) rfl h1 _).symm

/- English proof (translation)
Rewrite using `[MulChar.one_apply_coe, h1]`.
-/
lemma component_two_one (ψ : AddChar (E0 × HA e) ℂ) (h1 : ∀ t : HA e, ψ ((0, 0), t) = 1) (u : (ZMod (hostN e q d))ˣ) :
    (1 : DirichletCharacter ℂ (hostN e q d)) (u : ZMod _)
      = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) := by
  rw [MulChar.one_apply_coe, h1]

end Host

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma psC_apply {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (g : E0 × H) :
    (psC : AddChar (E0 × H) ℂ) g = if g.1.2 = 0 then 1 else -1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma chC_apply {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (g : E0 × H) :
    (chC : AddChar (E0 × H) ℂ) g = if g.1.1 = 0 then 1 else -1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma chpsC_apply {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (g : E0 × H) :
    (chpsC : AddChar (E0 × H) ℂ) g = (if g.1.1 = 0 then 1 else -1) * (if g.1.2 = 0 then 1 else -1) := rfl

/- English proof (translation)
Evaluate the decidable proposition.
-/
lemma one_ne_zero2 : (1 : ZMod 2) ≠ 0 := by decide

/- English proof (translation)
The claim follows from `changeLevel_one h`.
-/
lemma change_level_one {N : ℕ} (h : 1 ∣ N) : changeLevel h one1 = 1 := changeLevel_one h

/- English proof (translation)
Introduce `e q d _ _ h`. Take `⟨hq2, hd2, hqd⟩` from `HostHyp_ne h`. Establish `p1 : one1.IsPrimitive` using `isPrimitive_one_level_one`. Establish `pq` using `(twist_primitive.2 1 one1 q p1 hq2 (Nat.coprime_one_right q)).1`. Establish `pd` using `(twist_primitive.2 1 one1 d p1 hd2 (Nat.coprime_one_right d)).1`.

Establish `pqd` using `(twist_primitive.2 (1 * q) (tw one1 q) d pq hd2 (by rw [one_mul]; exact (Nat.coprime_primes h.2.1 h.1).2 hqd.symm)).1`. Establish `dq : 1 * q ∣ hostN e q d` using `by rw [one_mul]; exact q_dvd_hostN e q d`. Establish `dd : 1 * d ∣ hostN e q d` using `by rw [one_mul]; exact d_dvd_hostN e q d`. Establish `dqd : 1 * q * d ∣ hostN e q d` using `⟨2 ^ (e + 2), by unfold hostN; ring⟩`. Use `⟨sameChar_prim _ dq _ pq ?_, sameChar_prim _ dd _ pd ?_, sameChar_prim _ dqd _ pqd ?_⟩` and prove the remaining obligations.

Rewrite using `[tw_lift, change_level_one, dirChar_prod psC 1 (changeLevel (q_dvd_hostN e q d) (qc q)) 1 (component_two_one _ (fun t => by simp [psC_apply])) (compQ_neg _ (by simp [psC_apply])) (compD_one _ (by simp [psC_apply])), mul_one]`. Rewrite using `[tw_lift, change_level_one, dirChar_prod chC 1 1 (changeLevel (d_dvd_hostN e q d) (qc d)) (component_two_one _ (fun t => by simp [chC_apply])) (compQ_one _ (by simp [chC_apply])) (compD_neg _ (by simp [chC_apply])), mul_one]`. Rewrite using `[tw_lift, tw_lift, change_level_one, dirChar_prod chpsC 1 (changeLevel (q_dvd_hostN e q d) (qc q)) (changeLevel (d_dvd_hostN e q d) (qc d)) (component_two_one _ (fun t => by simp [chpsC_apply])) (compQ_neg _ (by simp [chpsC_apply])) (compD_neg _ (by simp [chpsC_apply]))]`.
-/
theorem quadratic_characters_input : HostQuadChars := by
  intro e q d _ _ h
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have p1 : one1.IsPrimitive := isPrimitive_one_level_one
  have pq := (twist_primitive.2 1 one1 q p1 hq2 (Nat.coprime_one_right q)).1
  have pd := (twist_primitive.2 1 one1 d p1 hd2 (Nat.coprime_one_right d)).1
  have pqd := (twist_primitive.2 (1 * q) (tw one1 q) d pq hd2
    (by rw [one_mul]; exact (Nat.coprime_primes h.2.1 h.1).2 hqd.symm)).1
  have dq : 1 * q ∣ hostN e q d := by rw [one_mul]; exact q_dvd_hostN e q d
  have dd : 1 * d ∣ hostN e q d := by rw [one_mul]; exact d_dvd_hostN e q d
  have dqd : 1 * q * d ∣ hostN e q d := ⟨2 ^ (e + 2), by unfold hostN; ring⟩
  refine ⟨sameChar_prim _ dq _ pq ?_, sameChar_prim _ dd _ pd ?_, sameChar_prim _ dqd _ pqd ?_⟩
  · rw [tw_lift, change_level_one, dirChar_prod psC 1 (changeLevel (q_dvd_hostN e q d) (qc q)) 1
      (component_two_one _ (fun t => by simp [psC_apply])) (compQ_neg _ (by simp [psC_apply]))
      (compD_one _ (by simp [psC_apply])), mul_one]
  · rw [tw_lift, change_level_one, dirChar_prod chC 1 1 (changeLevel (d_dvd_hostN e q d) (qc d))
      (component_two_one _ (fun t => by simp [chC_apply])) (compQ_one _ (by simp [chC_apply]))
      (compD_neg _ (by simp [chC_apply])), mul_one]
  · rw [tw_lift, tw_lift, change_level_one, dirChar_prod chpsC 1 (changeLevel (q_dvd_hostN e q d) (qc q))
      (changeLevel (d_dvd_hostN e q d) (qc d))
      (component_two_one _ (fun t => by simp [chpsC_apply])) (compQ_neg _ (by simp [chpsC_apply]))
      (compD_neg _ (by simp [chpsC_apply]))]

/- English proof (translation)
Use `⟨fun h => ?_, fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Use `DFunLike.congr_fun h (((0, 1), 0) : E0 × HA e)` as an intermediate fact. Rewrite `this` using `[psC_apply, AddChar.zero_apply]`. Evaluate the numerical expressions using `[one_ne_zero2] at this`. Use `DFunLike.congr_fun h (((1, 0), 0) : E0 × HA e)` as an intermediate fact.

Rewrite `this` using `[chC_apply, AddChar.zero_apply]`. Evaluate the numerical expressions using `[one_ne_zero2] at this`. Use `DFunLike.congr_fun h (((1, 0), 0) : E0 × HA e)` as an intermediate fact. Rewrite `this` using `[chpsC_apply, AddChar.zero_apply]`. Evaluate the numerical expressions using `[one_ne_zero2] at this`.
-/
lemma quad_ne_zero (e : ℕ) : (psC : AddChar (E0 × HA e) ℂ) ≠ 0 ∧ (chC : AddChar (E0 × HA e) ℂ) ≠ 0 ∧
    (chpsC : AddChar (E0 × HA e) ℂ) ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := DFunLike.congr_fun h (((0, 1), 0) : E0 × HA e)
    rw [psC_apply, AddChar.zero_apply] at this
    norm_num [one_ne_zero2] at this
  · have := DFunLike.congr_fun h (((1, 0), 0) : E0 × HA e)
    rw [chC_apply, AddChar.zero_apply] at this
    norm_num [one_ne_zero2] at this
  · have := DFunLike.congr_fun h (((1, 0), 0) : E0 × HA e)
    rw [chpsC_apply, AddChar.zero_apply] at this
    norm_num [one_ne_zero2] at this

/- English proof (translation)
Introduce `e q d _ _ h x ε C`. Take `⟨s1, s2, s3⟩` from `quadratic_characters_input e q d h`. Take `⟨n1, n2, n3⟩` from `quad_ne_zero e`. Take `⟨l1, g1, -⟩` from `same_character_g _ _ _ _ s1`. Take `⟨l2, g2, -⟩` from `same_character_g _ _ _ _ s2`.

Take `⟨l3, g3, -⟩` from `same_character_g _ _ _ _ s3`. Establish `hG` using `(g_psi_at_modulus e q d).1`. Establish `hL` using `ell_is_log_derivative e q d`. Prove the components needed by the constructor for the conclusion. Introduce `hv`.

Establish `v1` using `hv psC (Or.inl rfl)`. Establish `v2` using `hv chC (Or.inr (Or.inl rfl))`. Establish `v3` using `hv chpsC (Or.inr (Or.inr rfl))`. Rewrite `v1` using `[hG _ n1, hL, g1, l1]`. Rewrite `v2` using `[hG _ n2, hL, g2, l2]`.

Rewrite `v3` using `[hG _ n3, hL, g3, l3]`. Conclude with `⟨v1, v2, v3⟩`. Introduce and unpack `⟨v1, v2, v3⟩ ψ (rfl | rfl | rfl)`. Rewrite using `[hG _ n1, hL, g1, l1]`. Conclude with `v1`.

Rewrite using `[hG _ n2, hL, g2, l2]`. Conclude with `v2`. Rewrite using `[hG _ n3, hL, g3, l3]`. Conclude with `v3`.
-/
theorem valuesIff_valid : ValuesIff := by
  intro e q d _ _ h x ε C
  obtain ⟨s1, s2, s3⟩ := quadratic_characters_input e q d h
  obtain ⟨n1, n2, n3⟩ := quad_ne_zero e
  obtain ⟨l1, g1, -⟩ := same_character_g _ _ _ _ s1
  obtain ⟨l2, g2, -⟩ := same_character_g _ _ _ _ s2
  obtain ⟨l3, g3, -⟩ := same_character_g _ _ _ _ s3
  have hG := (g_psi_at_modulus e q d).1
  have hL := ell_is_log_derivative e q d
  constructor
  · intro hv
    have v1 := hv psC (Or.inl rfl)
    have v2 := hv chC (Or.inr (Or.inl rfl))
    have v3 := hv chpsC (Or.inr (Or.inr rfl))
    rw [hG _ n1, hL, g1, l1] at v1
    rw [hG _ n2, hL, g2, l2] at v2
    rw [hG _ n3, hL, g3, l3] at v3
    exact ⟨v1, v2, v3⟩
  · rintro ⟨v1, v2, v3⟩ ψ (rfl | rfl | rfl)
    · rw [hG _ n1, hL, g1, l1]; exact v1
    · rw [hG _ n2, hL, g2, l2]; exact v2
    · rw [hG _ n3, hL, g3, l3]; exact v3

/- English proof (translation)
Introduce `q d hq hd h8 h16 hs`. Take `⟨r, s, hrs, hr, hs⟩` from `hs`. Use `⟨hq, hd, h8, h16, ?_⟩` and prove the remaining obligations. Use `Fact.mk hq` as an intermediate fact. Establish `h4 : 4 * ((d + 1) / 4) = d + 1` using `by omega`.

Establish `h4' : (4 : ZMod q) * (((d + 1) / 4 : ℕ) : ZMod q) = (d : ZMod q) + 1`. Conclude with `congrArg (Nat.cast : ℕ → ZMod q) h4` after adjusting the coercions. Establish `two : (2 : ZMod q) ≠ 0`. Introduce `h`. Establish `h' : ((2 : ℕ) : ZMod q) = 0` using `by exact_mod_cast h`.

Rewrite `h'` using `[ZMod.natCast_eq_zero_iff]`. Use `Nat.le_of_dvd (by norm_num) h'` as an intermediate fact. Use `hq.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `sqr : ∀ t : ZMod q, t ^ 2 - t + (((d + 1) / 4 : ℕ) : ZMod q) = 0 → (2 * t - 1) ^ 2 = -(d : ZMod q)`.

Introduce `t ht`. Take the linear combination `4 * ht - h4'`. Establish `hne : ((-(d : ℤ) : ℤ) : ZMod q) ≠ 0`. Introduce `h0`. Establish `h0' : -(d : ZMod q) = 0` using `by exact_mod_cast h0`.

Establish `e1 : 2 * r - 1 = 0`. Use `sqr r hr` as an intermediate fact. Rewrite `this` using `[h0']`. Conclude with `pow_eq_zero_iff (two_ne_zero) |>.1 this`. Establish `e2 : 2 * s - 1 = 0`.

Use `sqr s hs` as an intermediate fact. Rewrite `this` using `[h0']`. Conclude with `pow_eq_zero_iff (two_ne_zero) |>.1 this`. Apply `hrs` to reduce the goal to its premises. Establish `: (2 : ZMod q) * (r - s) = 0` using `by linear_combination e1 - e2`.

Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `absurd h two`. Conclude with `sub_eq_zero.1 h`. Rewrite using `[← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff q hne]`. Use `⟨2 * r - 1, ?_⟩` and prove the remaining obligations.

Use `sqr r hr` as an intermediate fact. Use `push_cast`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prime_congruence_conditions : PrimeCongruenceHypotheses := by
  intro q d hq hd h8 h16 hs
  obtain ⟨r, s, hrs, hr, hs⟩ := hs
  refine ⟨hq, hd, h8, h16, ?_⟩
  have := Fact.mk hq
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have h4' : (4 : ZMod q) * (((d + 1) / 4 : ℕ) : ZMod q) = (d : ZMod q) + 1 := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod q) h4
  have two : (2 : ZMod q) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    have := hq.two_le
    omega
  have sqr : ∀ t : ZMod q, t ^ 2 - t + (((d + 1) / 4 : ℕ) : ZMod q) = 0 → (2 * t - 1) ^ 2 = -(d : ZMod q) := by
    intro t ht
    linear_combination 4 * ht - h4'
  have hne : ((-(d : ℤ) : ℤ) : ZMod q) ≠ 0 := by
    intro h0
    have h0' : -(d : ZMod q) = 0 := by exact_mod_cast h0
    have e1 : 2 * r - 1 = 0 := by
      have := sqr r hr
      rw [h0'] at this
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have e2 : 2 * s - 1 = 0 := by
      have := sqr s hs
      rw [h0'] at this
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    apply hrs
    have : (2 : ZMod q) * (r - s) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h two
    · exact sub_eq_zero.1 h
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff q hne]
  refine ⟨2 * r - 1, ?_⟩
  have := sqr r hr
  push_cast
  rw [← this]
  ring

section Real
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, ι, hι⟩` from `FrobeniusOrbits.hostGroup e`. Use `⟨(Multiplicative.toAdd (ι.symm t)).val, ?_⟩` and prove the remaining obligations. Rewrite using `[← hι, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd, MulEquiv.apply_symm_apply]`.
-/
lemma H_gen (e : ℕ) (t : FrobeniusOrbits.HGrp e) : ∃ k : ℕ, t = (FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2))) ^ k := by
  obtain ⟨-, -, -, -, -, -, -, -, ι, hι⟩ := FrobeniusOrbits.hostGroup e
  refine ⟨(Multiplicative.toAdd (ι.symm t)).val, ?_⟩
  rw [← hι, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd,
    MulEquiv.apply_symm_apply]

/- English proof (translation)
Rewrite using `[← AddChar.map_nsmul_eq_pow]`. Use `congr 1`. Simplify using `[Prod.smul_mk, ofMul_pow]`.
-/
lemma psi_H_pow (ψ : AddChar (E0 × HA e) ℂ) (g : FrobeniusOrbits.HGrp e) (k : ℕ) :
    ψ ((0, 0), Additive.ofMul (g ^ k)) = ψ ((0, 0), Additive.ofMul g) ^ k := by
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  simp [Prod.smul_mk, ofMul_pow]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `h` using `changeLevel_eq_cast_of_dvd' chi8 h8 (a := -1) (by`. Conclude with `(isCoprime_one_left).neg_left)`. Establish `e1 : (((-1 : ℤ)) : ZMod (2 ^ (e + 2))) = ((-1 : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2)))`. Simplify using the standard rewrite rules.

Rewrite `h` using `[e1]`. Rewrite using `[h, chi8, MulChar.ringHomComp_apply]`. Establish `: ZMod.χ₈ ((-1 : ℤ) : ZMod 8) = 1` using `by decide`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Establish `h` using `changeLevel_eq_cast_of_dvd' chi8 h8 (a := 5) (by`. Use `push_cast`. Apply `IsCoprime.pow_right` to reduce the goal to its premises. Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`. Use the proof step `decide)`.

Establish `e1 : (((5 : ℤ)) : ZMod (2 ^ (e + 2))) = ((TwoAdicCyclotomicDecomposition.u5 (e + 2) : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2)))`. Unfold `TwoAdicCyclotomicDecomposition.u5`. Rewrite using `[ZMod.coe_unitOfCoprime]`. Simplify using the standard rewrite rules. Rewrite `h` using `[e1]`.

Rewrite using `[h, chi8, MulChar.ringHomComp_apply]`. Establish `: ZMod.χ₈ ((5 : ℤ) : ZMod 8) = -1` using `by decide`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
lemma chi_eight_lift_values (e : ℕ) (h8 : 8 ∣ 2 ^ (e + 2)) :
    changeLevel h8 chi8 ((-1 : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = 1 ∧
    changeLevel h8 chi8 ((TwoAdicCyclotomicDecomposition.u5 (e + 2) : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = -1 := by
  constructor
  · have h := changeLevel_eq_cast_of_dvd' chi8 h8 (a := -1) (by
      exact (isCoprime_one_left).neg_left)
    have e1 : (((-1 : ℤ)) : ZMod (2 ^ (e + 2))) = ((-1 : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) := by
      simp
    rw [e1] at h
    rw [h, chi8, MulChar.ringHomComp_apply]
    have : ZMod.χ₈ ((-1 : ℤ) : ZMod 8) = 1 := by decide
    rw [this]
    simp
  · have h := changeLevel_eq_cast_of_dvd' chi8 h8 (a := 5) (by
      push_cast
      apply IsCoprime.pow_right
      rw [Int.isCoprime_iff_gcd_eq_one]
      decide)
    have e1 : (((5 : ℤ)) : ZMod (2 ^ (e + 2))) = ((TwoAdicCyclotomicDecomposition.u5 (e + 2) : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) := by
      unfold TwoAdicCyclotomicDecomposition.u5
      rw [ZMod.coe_unitOfCoprime]
      simp
    rw [e1] at h
    rw [h, chi8, MulChar.ringHomComp_apply]
    have : ZMod.χ₈ ((5 : ℤ) : ZMod 8) = -1 := by decide
    rw [this]
    simp

/- English proof (translation)
Take `⟨hm, h5⟩` from `chi_eight_lift_values e h8`. Use `set F := (changeLevel h8 chi8).toUnitHom with hF`. Establish `hFm : F (-1) = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hF, MulChar.coe_toUnitHom, hm]`.

Both sides reduce to the same expression. Establish `hF5 : ((F (TwoAdicCyclotomicDecomposition.u5 (e + 2)) : ℂˣ) : ℂ) = -1`. Rewrite using `[hF, MulChar.coe_toUnitHom, h5]`. Establish `hmem : v⁻¹ * (TwoAdicCyclotomicDecomposition.u5 (e + 2)) ^ k ∈ Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ)`. Apply `QuotientGroup.eq.1` to reduce the goal to its premises.

Conclude with `hk`. Take `⟨j, hj⟩` from `Subgroup.mem_zpowers_iff.1 hmem`. Establish `h1 : F (v⁻¹ * (TwoAdicCyclotomicDecomposition.u5 (e + 2)) ^ k) = 1`. Rewrite using `[← hj, map_zpow, hFm, one_zpow]`. Rewrite `h1` using `[map_mul, map_inv, map_pow, inv_mul_eq_one]`.

Rewrite using `[← MulChar.coe_toUnitHom, ← hF, h1, Units.val_pow_eq_pow_val, hF5]`.
-/
lemma chi_eight_lift_class (e : ℕ) (h8 : 8 ∣ 2 ^ (e + 2)) (v : (ZMod (2 ^ (e + 2)))ˣ) (k : ℕ)
    (hk : FrobeniusOrbits.hcl e v = (FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2))) ^ k) :
    changeLevel h8 chi8 (v : ZMod (2 ^ (e + 2))) = (-1) ^ k := by
  obtain ⟨hm, h5⟩ := chi_eight_lift_values e h8
  set F := (changeLevel h8 chi8).toUnitHom with hF
  have hFm : F (-1) = 1 := by
    apply Units.ext
    rw [hF, MulChar.coe_toUnitHom, hm]
    rfl
  have hF5 : ((F (TwoAdicCyclotomicDecomposition.u5 (e + 2)) : ℂˣ) : ℂ) = -1 := by
    rw [hF, MulChar.coe_toUnitHom, h5]
  have hmem : v⁻¹ * (TwoAdicCyclotomicDecomposition.u5 (e + 2)) ^ k ∈ Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ) := by
    apply QuotientGroup.eq.1
    exact hk
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have h1 : F (v⁻¹ * (TwoAdicCyclotomicDecomposition.u5 (e + 2)) ^ k) = 1 := by
    rw [← hj, map_zpow, hFm, one_zpow]
  rw [map_mul, map_inv, map_pow, inv_mul_eq_one] at h1
  rw [← MulChar.coe_toUnitHom, ← hF, h1, Units.val_pow_eq_pow_val, hF5]

/- English proof (translation)
Take `⟨k, hk⟩` from `H_gen e (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))`. Rewrite using `[hk, psi_H_pow, h1, changeLevel_trans chi8 h8 (two_dvd_hostN e q d), changeLevel_eq_cast_of_dvd, ← chi_eight_lift_class e h8 _ k hk, ZMod.unitsMap_val]`.
-/
lemma component_two_neg (ψ : AddChar (E0 × HA e) ℂ) (h8 : 8 ∣ 2 ^ (e + 2))
    (h1 : ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2)))) = -1) (u : (ZMod (hostN e q d))ˣ) :
    changeLevel (h8.trans (two_dvd_hostN e q d)) chi8 (u : ZMod _)
      = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) := by
  obtain ⟨k, hk⟩ := H_gen e (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))
  rw [hk, psi_H_pow, h1, changeLevel_trans chi8 h8 (two_dvd_hostN e q d), changeLevel_eq_cast_of_dvd,
    ← chi_eight_lift_class e h8 _ k hk, ZMod.unitsMap_val]

end Real
section Real2
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

/- English proof (translation)
Take `⟨hq2, hd2, hqd⟩` from `HostHyp_ne h`. Establish `cq : q.Coprime t` using `Nat.Coprime.coprime_dvd_right ht (Nat.Coprime.pow_right _ ((Nat.coprime_primes h.1 Nat.prime_two).2 hq2))`. Establish `cd : d.Coprime t` using `Nat.Coprime.coprime_dvd_right ht (Nat.Coprime.pow_right _ ((Nat.coprime_primes h.2.1 Nat.prime_two).2 hd2))`. Establish `pq` using `(twist_primitive.2 t θ q hθ hq2 cq).1`. Establish `pd` using `(twist_primitive.2 t θ d hθ hd2 cd).1`.

Establish `pqd` using `(twist_primitive.2 (t * q) (tw θ q) d pq hd2 (Nat.Coprime.mul_right cd ((Nat.coprime_primes h.2.1 h.1).2 hqd.symm))).1`. Take `⟨c, hc⟩` from `ht`. Establish `dq : t * q ∣ hostN e q d` using `⟨c * d, by unfold hostN; rw [hc]; ring⟩`. Establish `dd : t * d ∣ hostN e q d` using `⟨c * q, by unfold hostN; rw [hc]; ring⟩`. Establish `dqd : t * q * d ∣ hostN e q d` using `⟨c, by unfold hostN; rw [hc]; ring⟩`.

Establish `z1 : (((0, 1), 0) : E0 × HA e) + ((0, 1), 0) = 0` using `Prod.ext (Prod.ext (by simp) (show (1 : ZMod 2) + 1 = 0 by decide)) (by simp)`. Establish `z2 : (((1, 0), 0) : E0 × HA e) + ((1, 0), 0) = 0` using `Prod.ext (Prod.ext (show (1 : ZMod 2) + 1 = 0 by decide) (by simp)) (by simp)`. Apply the tactic sequence `rcases psi_pm ψ _ z1 with eq1 | eq1 <;> rcases psi_pm ψ _ z2 with ed1 | ed1`. Use `left`. Rewrite using `[dirChar_prod ψ _ 1 1 h2 (compQ_one ψ eq1) (compD_one ψ ed1), mul_one, mul_one]`.

Use `right`. Use `right`. Use `left`. Use `sameChar_prim _ dd _ pd ?_` and prove the remaining obligations. Rewrite using `[tw_lift, dirChar_prod ψ _ 1 _ h2 (compQ_one ψ eq1) (compD_neg ψ ed1), mul_one]`.

Use `right`. Use `left`. Use `sameChar_prim _ dq _ pq ?_` and prove the remaining obligations. Rewrite using `[tw_lift, dirChar_prod ψ _ _ 1 h2 (compQ_neg ψ eq1) (compD_one ψ ed1), mul_one]`. Use `right`.

Use `right`. Use `right`. Use `sameChar_prim _ dqd _ pqd ?_` and prove the remaining obligations. Rewrite using `[tw_lift, tw_lift, dirChar_prod ψ _ _ _ h2 (compQ_neg ψ eq1) (compD_neg ψ ed1)]`.
-/
lemma real_cases (h : FrobeniusOrbits.HostHyp q d) (ψ : AddChar (E0 × HA e) ℂ) {t : ℕ} (θ : DirichletCharacter ℂ t)
    (ht : t ∣ 2 ^ (e + 2)) (hθ : θ.IsPrimitive)
    (h2 : ∀ u : (ZMod (hostN e q d))ˣ, changeLevel (ht.trans (two_dvd_hostN e q d)) θ (u : ZMod _)
      = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u)))) :
    dirChar (recMap e q d) ψ = changeLevel (ht.trans (two_dvd_hostN e q d)) θ ∨
    SameChar (chiOf e q d ψ) (tw θ q) ∨ SameChar (chiOf e q d ψ) (tw θ d) ∨
    SameChar (chiOf e q d ψ) (tw (tw θ q) d) := by
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have cq : q.Coprime t := Nat.Coprime.coprime_dvd_right ht
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes h.1 Nat.prime_two).2 hq2))
  have cd : d.Coprime t := Nat.Coprime.coprime_dvd_right ht
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes h.2.1 Nat.prime_two).2 hd2))
  have pq := (twist_primitive.2 t θ q hθ hq2 cq).1
  have pd := (twist_primitive.2 t θ d hθ hd2 cd).1
  have pqd := (twist_primitive.2 (t * q) (tw θ q) d pq hd2
    (Nat.Coprime.mul_right cd ((Nat.coprime_primes h.2.1 h.1).2 hqd.symm))).1
  obtain ⟨c, hc⟩ := ht
  have dq : t * q ∣ hostN e q d := ⟨c * d, by unfold hostN; rw [hc]; ring⟩
  have dd : t * d ∣ hostN e q d := ⟨c * q, by unfold hostN; rw [hc]; ring⟩
  have dqd : t * q * d ∣ hostN e q d := ⟨c, by unfold hostN; rw [hc]; ring⟩
  have z1 : (((0, 1), 0) : E0 × HA e) + ((0, 1), 0) = 0 :=
    Prod.ext (Prod.ext (by simp) (show (1 : ZMod 2) + 1 = 0 by decide)) (by simp)
  have z2 : (((1, 0), 0) : E0 × HA e) + ((1, 0), 0) = 0 :=
    Prod.ext (Prod.ext (show (1 : ZMod 2) + 1 = 0 by decide) (by simp)) (by simp)
  rcases psi_pm ψ _ z1 with eq1 | eq1 <;> rcases psi_pm ψ _ z2 with ed1 | ed1
  · left
    rw [dirChar_prod ψ _ 1 1 h2 (compQ_one ψ eq1) (compD_one ψ ed1), mul_one, mul_one]
  · right; right; left
    refine sameChar_prim _ dd _ pd ?_
    rw [tw_lift, dirChar_prod ψ _ 1 _ h2 (compQ_one ψ eq1) (compD_neg ψ ed1), mul_one]
  · right; left
    refine sameChar_prim _ dq _ pq ?_
    rw [tw_lift, dirChar_prod ψ _ _ 1 h2 (compQ_neg ψ eq1) (compD_one ψ ed1), mul_one]
  · right; right; right
    refine sameChar_prim _ dqd _ pqd ?_
    rw [tw_lift, tw_lift, dirChar_prod ψ _ _ _ h2 (compQ_neg ψ eq1) (compD_neg ψ ed1)]

end Real2

/- English proof (translation)
Introduce `e q d _ _ h ψ hsq`. Establish `hD : dirChar (recMap e q d) ψ ^ 2 = 1`. Rewrite using `[← changeLevel_primitiveCharacter (dirChar (recMap e q d) ψ), ← map_pow, show (dirChar (recMap e q d) ψ).primitiveCharacter ^ 2 = 1 from hsq, map_one]`. Establish `hreal : ∀ g : E0 × HA e, ψ g = 1 ∨ ψ g = -1`. Introduce `g`.

Take `⟨u, hu⟩` from `recSurjective_valid e q d h (Multiplicative.ofAdd g)`. Establish `h1` using `DFunLike.congr_fun hD (u : ZMod (hostN e q d))`. Rewrite `h1` using `[MulChar.pow_apply_coe, MulChar.one_apply_coe, dirChar_unit, hu, toAdd_ofAdd]`. Conclude with `mul_self_eq_one_iff.1 (by rw [← sq]; exact h1)`. Break down `hreal ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2)))) with h5 | h5` into its components or cases.

Establish `hall : ∀ t : HA e, ψ ((0, 0), t) = 1`. Introduce `t`. Take `⟨k, hk⟩` from `H_gen e (Additive.toMul t)`. Establish `: t = Additive.ofMul ((FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2))) ^ k)` using `by rw [← hk]; rfl`. Rewrite using `[this, psi_H_pow, h5, one_pow]`.

Establish `h2 : ∀ u : (ZMod (hostN e q d))ˣ, changeLevel ((one_dvd (2 ^ (e + 2))).trans (two_dvd_hostN e q d)) one1 (u : ZMod _) = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u)))`. Introduce `u`. Rewrite using `[change_level_one]`. Conclude with `component_two_one ψ hall u`. Break down `real_cases h ψ one1 (one_dvd _) isPrimitive_one_level_one h2 with c | c | c | c` into its components or cases.

Use `left`. Rewrite `c` using `[change_level_one, ← dirChar_zero e q d]`. Conclude with `dirichlet_character_injective e q d h c`. Conclude with `Or.inr (Or.inr (Or.inl c))`. Conclude with `Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))`.

Conclude with `Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))))`. Establish `he : e ≠ 0`. Introduce and unpack `rfl`. Take `⟨-, -, -, -, -, -, -, ho, -⟩` from `FrobeniusOrbits.hostGroup 0`. Rewrite `ho` using `[pow_zero, orderOf_eq_one_iff]`.

Rewrite `h5` using `[ho]`. Establish `h0 : ψ ((0, 0), Additive.ofMul (1 : FrobeniusOrbits.HGrp 0)) = 1` using `AddChar.map_zero_eq_one ψ`. Rewrite `h5` using `[h0]`. Evaluate the numerical expressions using `at h5`. Establish `h8 : 8 ∣ 2 ^ (e + 2)`.

Take `⟨e', rfl⟩` from `Nat.exists_eq_succ_of_ne_zero he`. Conclude with `⟨2 ^ e', by rw [Nat.succ_eq_add_one]; ring⟩`. Break down `real_cases h ψ chi8 h8 chi_eight_primitive (component_two_neg ψ h8 h5) with c | c | c | c` into its components or cases. Conclude with `Or.inr (Or.inl (sameChar_prim _ _ _ chi_eight_primitive c))`. Conclude with `Or.inr (Or.inr (Or.inr (Or.inl c)))`.

Conclude with `Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c)))))`. Conclude with `Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c))))))`.
-/
theorem real_characters_input : HostRealChars := by
  intro e q d _ _ h ψ hsq
  have hD : dirChar (recMap e q d) ψ ^ 2 = 1 := by
    rw [← changeLevel_primitiveCharacter (dirChar (recMap e q d) ψ), ← map_pow,
      show (dirChar (recMap e q d) ψ).primitiveCharacter ^ 2 = 1 from hsq, map_one]
  have hreal : ∀ g : E0 × HA e, ψ g = 1 ∨ ψ g = -1 := by
    intro g
    obtain ⟨u, hu⟩ := recSurjective_valid e q d h (Multiplicative.ofAdd g)
    have h1 := DFunLike.congr_fun hD (u : ZMod (hostN e q d))
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, dirChar_unit, hu, toAdd_ofAdd] at h1
    exact mul_self_eq_one_iff.1 (by rw [← sq]; exact h1)
  rcases hreal ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2)))) with h5 | h5
  · have hall : ∀ t : HA e, ψ ((0, 0), t) = 1 := by
      intro t
      obtain ⟨k, hk⟩ := H_gen e (Additive.toMul t)
      have : t = Additive.ofMul ((FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2))) ^ k) := by rw [← hk]; rfl
      rw [this, psi_H_pow, h5, one_pow]
    have h2 : ∀ u : (ZMod (hostN e q d))ˣ,
        changeLevel ((one_dvd (2 ^ (e + 2))).trans (two_dvd_hostN e q d)) one1 (u : ZMod _)
          = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) := by
      intro u
      rw [change_level_one]
      exact component_two_one ψ hall u
    rcases real_cases h ψ one1 (one_dvd _) isPrimitive_one_level_one h2 with c | c | c | c
    · left
      rw [change_level_one, ← dirChar_zero e q d] at c
      exact dirichlet_character_injective e q d h c
    · exact Or.inr (Or.inr (Or.inl c))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))))
  · have he : e ≠ 0 := by
      rintro rfl
      obtain ⟨-, -, -, -, -, -, -, ho, -⟩ := FrobeniusOrbits.hostGroup 0
      rw [pow_zero, orderOf_eq_one_iff] at ho
      rw [ho] at h5
      have h0 : ψ ((0, 0), Additive.ofMul (1 : FrobeniusOrbits.HGrp 0)) = 1 := AddChar.map_zero_eq_one ψ
      rw [h0] at h5
      norm_num at h5
    have h8 : 8 ∣ 2 ^ (e + 2) := by
      obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
      exact ⟨2 ^ e', by rw [Nat.succ_eq_add_one]; ring⟩
    rcases real_cases h ψ chi8 h8 chi_eight_primitive (component_two_neg ψ h8 h5) with c | c | c | c
    · exact Or.inr (Or.inl (sameChar_prim _ _ _ chi_eight_primitive c))
    · exact Or.inr (Or.inr (Or.inr (Or.inl c)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c))))))

/- English proof (translation)
Introduce `e q d`. Unfold `hostN`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem modulus_formula : HostNIs := by
  intro e q d
  unfold hostN
  ring

/- English proof (translation)
Introduce `s h1 h2`. Rewrite using `[(same_character_g _ _ _ _ hs).2.2.2.1]`. Conclude with `h s h1 h2`.
-/
lemma zeroFreeBox_same {N M : ℕ} [NeZero N] [NeZero M] {χ : DirichletCharacter ℂ N} {χ' : DirichletCharacter ℂ M}
    (hs : SameChar χ χ') {Q : ℝ} (h : ZeroFreeBox Q χ') : ZeroFreeBox Q χ := by
  intro s h1 h2
  rw [(same_character_g _ _ _ _ hs).2.2.2.1]
  exact h s h1 h2

/- English proof (translation)
Introduce and unpack `⟨c, K, hc, hK⟩ ε c' hε`. Establish `T1 : Tendsto (fun x : ℝ => x ^ (ε / 8)) atTop atTop` using `tendsto_rpow_atTop (by positivity)`. Establish `T2 : Tendsto (fun x : ℝ => c / 2 * x ^ (ε / 24) - c') atTop atTop` using `tendsto_atTop_add_const_right _ _ ((tendsto_rpow_atTop (by positivity : 0 < ε / 24)).const_mul_atTop (by positivity))`. Establish `T3 : Tendsto (fun x : ℝ => Real.exp (x ^ (ε / 8) * (c / 2 * x ^ (ε / 24) - c'))) atTop atTop` using `Real.tendsto_exp_atTop.comp (T1.atTop_mul_atTop₀ T2)`. Establish `E1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x` using `eventually_ge_atTop 1`.

Establish `E2 : ∀ᶠ x : ℝ in atTop, 5 ≤ x ^ (ε / 3)` using `(tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop 5`. Establish `E3` using `T3.eventually_ge_atTop (max K 0)`. Take `⟨x₀, hx₀⟩` from `eventually_atTop.1 (E1.and (E2.and E3))`. Use `⟨x₀, fun x hx y hy => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `hx₀ x hx`.

Establish `hx0 : 0 < x` using `by linarith`. Use `set X := x ^ (ε / 3) with hX`. Establish `hexp : X + 1 ≤ Real.exp X` using `Real.add_one_le_exp X`. Establish `hy2 : 2 ≤ y` using `by linarith`. Establish `hy0 : 0 < y` using `by linarith`.

Establish `hlog3 : Real.log 3 ≤ 2`. Use `Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogy : X / 4 ≤ Real.log y`. Establish `h4 : Real.log (Real.exp X / 3) ≤ Real.log y` using `Real.log_le_log (by positivity) hy`.

Rewrite `h4` using `[Real.log_div (Real.exp_pos X).ne' (by norm_num), Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs : x ^ (ε / 6) / 2 ≤ Real.sqrt (Real.log y)`. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Establish `: (x ^ (ε / 6)) ^ 2 = X`.

Rewrite using `[hX, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[div_pow, this]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsplit : x ^ (ε / 6) = x ^ (ε / 8) * x ^ (ε / 24)`. Rewrite using `[← Real.rpow_add hx0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← g_zeta_eq_g_one y]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_max_left _ _`. Use `_ ≤ max K 0 * y * Real.exp (-c * (x ^ (ε / 6) / 2)) := by`. Establish `h0 : 0 ≤ max K 0` using `le_max_right _ _`.

Establish `h5 : Real.exp (-c * Real.sqrt (Real.log y)) ≤ Real.exp (-c * (x ^ (ε / 6) / 2))` using `Real.exp_le_exp.2 (by nlinarith)`. Conclude with `mul_le_mul_of_nonneg_left h5 (by positivity)`. Use `_ ≤ Real.exp (x ^ (ε / 8) * (c / 2 * x ^ (ε / 24) - c')) * y * Real.exp (-c * (x ^ (ε / 6) / 2)) := by gcongr`. Use `_ = y * Real.exp (-c' * x ^ (ε / 8)) := by`. Rewrite using `[mul_right_comm, ← Real.exp_add, mul_comm]`.

Use `congr 2`. Rewrite using `[hsplit]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thin_one_of : ThinOneOf := by
  rintro ⟨c, K, hc, hK⟩ ε c' hε
  have T1 : Tendsto (fun x : ℝ => x ^ (ε / 8)) atTop atTop := tendsto_rpow_atTop (by positivity)
  have T2 : Tendsto (fun x : ℝ => c / 2 * x ^ (ε / 24) - c') atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_rpow_atTop (by positivity : 0 < ε / 24)).const_mul_atTop (by positivity))
  have T3 : Tendsto (fun x : ℝ => Real.exp (x ^ (ε / 8) * (c / 2 * x ^ (ε / 24) - c'))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (T1.atTop_mul_atTop₀ T2)
  have E1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have E2 : ∀ᶠ x : ℝ in atTop, 5 ≤ x ^ (ε / 3) := (tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop 5
  have E3 := T3.eventually_ge_atTop (max K 0)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (E1.and (E2.and E3))
  refine ⟨x₀, fun x hx y hy => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  set X := x ^ (ε / 3) with hX
  have hexp : X + 1 ≤ Real.exp X := Real.add_one_le_exp X
  have hy2 : 2 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlogy : X / 4 ≤ Real.log y := by
    have h4 : Real.log (Real.exp X / 3) ≤ Real.log y := Real.log_le_log (by positivity) hy
    rw [Real.log_div (Real.exp_pos X).ne' (by norm_num), Real.log_exp] at h4
    linarith
  have hs : x ^ (ε / 6) / 2 ≤ Real.sqrt (Real.log y) := by
    apply Real.le_sqrt_of_sq_le
    have : (x ^ (ε / 6)) ^ 2 = X := by
      rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      congr 1
      push_cast
      ring
    rw [div_pow, this]
    linarith
  have hsplit : x ^ (ε / 6) = x ^ (ε / 8) * x ^ (ε / 24) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [← g_zeta_eq_g_one y]
  calc |Gz y| ≤ K * y * Real.exp (-c * Real.sqrt (Real.log y)) := hK y hy2
    _ ≤ max K 0 * y * Real.exp (-c * Real.sqrt (Real.log y)) := by
        gcongr
        exact le_max_left _ _
    _ ≤ max K 0 * y * Real.exp (-c * (x ^ (ε / 6) / 2)) := by
        have h0 : 0 ≤ max K 0 := le_max_right _ _
        have h5 : Real.exp (-c * Real.sqrt (Real.log y)) ≤ Real.exp (-c * (x ^ (ε / 6) / 2)) :=
          Real.exp_le_exp.2 (by nlinarith)
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
    _ ≤ Real.exp (x ^ (ε / 8) * (c / 2 * x ^ (ε / 24) - c')) * y * Real.exp (-c * (x ^ (ε / 6) / 2)) := by
        gcongr
    _ = y * Real.exp (-c' * x ^ (ε / 8)) := by
        rw [mul_right_comm, ← Real.exp_add, mul_comm]
        congr 2
        rw [hsplit]
        ring

/- English proof (translation)
Establish `h` using `Real.pow_div_factorial_le_exp (b * t) (by positivity) n`. Establish `h2 : (b * t) ^ n ≤ (n.factorial : ℝ) * Real.exp (b * t)`. Rewrite `h` using `[div_le_iff₀' (by positivity)]`. Then use the resulting hypothesis. Rewrite using `[Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma pow_mul_exp_neg_le (n : ℕ) (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) :
    t ^ n * Real.exp (-(b * t)) ≤ (n.factorial : ℝ) / b ^ n := by
  have h := Real.pow_div_factorial_le_exp (b * t) (by positivity) n
  have h2 : (b * t) ^ n ≤ (n.factorial : ℝ) * Real.exp (b * t) := by
    rwa [div_le_iff₀' (by positivity)] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  calc t ^ n * b ^ n = (b * t) ^ n := by rw [mul_pow]; ring
    _ ≤ _ := h2

/- English proof (translation)
Establish `hs2 : 2 ≤ s` using `by linarith`. Establish `hM0 : 0 < μ + s` using `by linarith`. Establish `hexpo : -a * s ^ 2 / (μ + s) ≤ -(a / 4 * s) + -(a / 8 * R)`. Establish `h8 : s / 2 ≤ s ^ 2 / (μ + s)`. Rewrite using `[div_le_div_iff₀ (by norm_num) hM0]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `e : -a * s ^ 2 / (μ + s) = -(a * (s ^ 2 / (μ + s)))` using `by ring`. Establish `m1` using `mul_le_mul_of_nonneg_left h8 ha.le`. Establish `m2` using `mul_le_mul_of_nonneg_left hsR ha.le`. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcube : (μ + s + s ^ 2) ^ 3 ≤ 8 * s ^ 6`. Establish `h9 : μ + s + s ^ 2 ≤ 2 * s ^ 2` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hK` using `pow_mul_exp_neg_le 6 (a / 4) s (by positivity) (by linarith)`.

Establish `hE` using `Real.exp_le_exp.2 hexpo`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.exp_add]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 8 * A * (((6 : ℕ).factorial : ℝ) / (a / 4) ^ 6) * Real.exp (-(a / 8 * R)) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by positivity)) (Real.exp_pos _).le`.
-/
lemma thin_caseA (a A μ s R : ℝ) (ha : 0 < a) (hA : 0 ≤ A) (hμ2 : 2 ≤ μ) (hμs : μ ≤ s) (hsR : R / 2 ≤ s) :
    A * (μ + s + s ^ 2) ^ 3 * Real.exp (-a * s ^ 2 / (μ + s))
      ≤ 8 * A * (((6 : ℕ).factorial : ℝ) / (a / 4) ^ 6) * Real.exp (-(a / 8 * R)) := by
  have hs2 : 2 ≤ s := by linarith
  have hM0 : 0 < μ + s := by linarith
  have hexpo : -a * s ^ 2 / (μ + s) ≤ -(a / 4 * s) + -(a / 8 * R) := by
    have h8 : s / 2 ≤ s ^ 2 / (μ + s) := by
      rw [div_le_div_iff₀ (by norm_num) hM0]
      nlinarith
    have e : -a * s ^ 2 / (μ + s) = -(a * (s ^ 2 / (μ + s))) := by ring
    have m1 := mul_le_mul_of_nonneg_left h8 ha.le
    have m2 := mul_le_mul_of_nonneg_left hsR ha.le
    rw [e]
    linarith
  have hcube : (μ + s + s ^ 2) ^ 3 ≤ 8 * s ^ 6 := by
    have h9 : μ + s + s ^ 2 ≤ 2 * s ^ 2 := by nlinarith
    calc (μ + s + s ^ 2) ^ 3 ≤ (2 * s ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) h9 3
      _ = 8 * s ^ 6 := by ring
  have hK := pow_mul_exp_neg_le 6 (a / 4) s (by positivity) (by linarith)
  have hE := Real.exp_le_exp.2 hexpo
  calc A * (μ + s + s ^ 2) ^ 3 * Real.exp (-a * s ^ 2 / (μ + s))
      ≤ A * (8 * s ^ 6) * Real.exp (-(a / 4 * s) + -(a / 8 * R)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcube hA) hE (Real.exp_pos _).le (by positivity)
    _ = 8 * A * (s ^ 6 * Real.exp (-(a / 4 * s))) * Real.exp (-(a / 8 * R)) := by
        rw [Real.exp_add]; ring
    _ ≤ 8 * A * (((6 : ℕ).factorial : ℝ) / (a / 4) ^ 6) * Real.exp (-(a / 8 * R)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by positivity)) (Real.exp_pos _).le

/- English proof (translation)
Establish `hM0 : 0 < μ + s` using `by linarith`. Establish `hexpo : -a * s ^ 2 / (μ + s) ≤ -(a / 8 * R) + -(a / 8 * R)`. Establish `h8 : R / 4 ≤ s ^ 2 / (μ + s)`. Rewrite using `[div_le_div_iff₀ (by norm_num) hM0]`. Establish `h10 : μ + s ≤ 2 * Lb` using `by linarith`.

Establish `h12 : R * (μ + s) ≤ R * (2 * Lb)` using `mul_le_mul_of_nonneg_left h10 hR0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : -a * s ^ 2 / (μ + s) = -(a * (s ^ 2 / (μ + s)))` using `by ring`. Establish `m1` using `mul_le_mul_of_nonneg_left h8 ha.le`. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcube : (μ + s + s ^ 2) ^ 3 ≤ 8 * R ^ 10`. Establish `h9 : μ + s + s ^ 2 ≤ 2 * Lb ^ 2`. Establish `k1 : s ^ 2 ≤ μ ^ 2` using `pow_le_pow_left₀ hs0 hsμ.le 2`. Establish `k2 : μ ^ 2 ≤ Lb ^ 2` using `pow_le_pow_left₀ (by linarith) hμL 2`.

Establish `k3 : 2 * μ ≤ μ ^ 2` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `hK` using `pow_mul_exp_neg_le 10 (a / 8) R (by positivity) hR0`. Establish `hE` using `Real.exp_le_exp.2 hexpo`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.exp_add]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 8 * A * (((10 : ℕ).factorial : ℝ) / (a / 8) ^ 10) * Real.exp (-(a / 8 * R)) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by positivity)) (Real.exp_pos _).le`.
-/
lemma thin_caseB (a A μ s R Lb : ℝ) (ha : 0 < a) (hA : 0 ≤ A) (hμ2 : 2 ≤ μ) (hs0 : 0 ≤ s) (hsμ : s < μ)
    (hμL : μ ≤ Lb) (hv : Lb * R / 2 ≤ s ^ 2) (hL6 : Lb ^ 6 = R ^ 10) (hR0 : 0 ≤ R) :
    A * (μ + s + s ^ 2) ^ 3 * Real.exp (-a * s ^ 2 / (μ + s))
      ≤ 8 * A * (((10 : ℕ).factorial : ℝ) / (a / 8) ^ 10) * Real.exp (-(a / 8 * R)) := by
  have hM0 : 0 < μ + s := by linarith
  have hexpo : -a * s ^ 2 / (μ + s) ≤ -(a / 8 * R) + -(a / 8 * R) := by
    have h8 : R / 4 ≤ s ^ 2 / (μ + s) := by
      rw [div_le_div_iff₀ (by norm_num) hM0]
      have h10 : μ + s ≤ 2 * Lb := by linarith
      have h12 : R * (μ + s) ≤ R * (2 * Lb) := mul_le_mul_of_nonneg_left h10 hR0
      linarith
    have e : -a * s ^ 2 / (μ + s) = -(a * (s ^ 2 / (μ + s))) := by ring
    have m1 := mul_le_mul_of_nonneg_left h8 ha.le
    rw [e]
    linarith
  have hcube : (μ + s + s ^ 2) ^ 3 ≤ 8 * R ^ 10 := by
    have h9 : μ + s + s ^ 2 ≤ 2 * Lb ^ 2 := by
      have k1 : s ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ hs0 hsμ.le 2
      have k2 : μ ^ 2 ≤ Lb ^ 2 := pow_le_pow_left₀ (by linarith) hμL 2
      have k3 : 2 * μ ≤ μ ^ 2 := by nlinarith
      linarith
    calc (μ + s + s ^ 2) ^ 3 ≤ (2 * Lb ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) h9 3
      _ = 8 * Lb ^ 6 := by ring
      _ = 8 * R ^ 10 := by rw [hL6]
  have hK := pow_mul_exp_neg_le 10 (a / 8) R (by positivity) hR0
  have hE := Real.exp_le_exp.2 hexpo
  calc A * (μ + s + s ^ 2) ^ 3 * Real.exp (-a * s ^ 2 / (μ + s))
      ≤ A * (8 * R ^ 10) * Real.exp (-(a / 8 * R) + -(a / 8 * R)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcube hA) hE (Real.exp_pos _).le (by positivity)
    _ = 8 * A * (R ^ 10 * Real.exp (-(a / 8 * R))) * Real.exp (-(a / 8 * R)) := by
        rw [Real.exp_add]; ring
    _ ≤ 8 * A * (((10 : ℕ).factorial : ℝ) / (a / 8) ^ 10) * Real.exp (-(a / 8 * R)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by positivity)) (Real.exp_pos _).le

/- English proof (translation)
Use `set K6 : ℝ := ((6 : ℕ).factorial : ℝ) / (a / 4) ^ 6 with hK6`. Use `set K10 : ℝ := ((10 : ℕ).factorial : ℝ) / (a / 8) ^ 10 with hK10`. Establish `TR : Tendsto (fun x : ℝ => x ^ (ε / 8)) atTop atTop` using `tendsto_rpow_atTop (by positivity)`. Establish `E1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x` using `eventually_ge_atTop 1`. Establish `E2 : ∀ᶠ x : ℝ in atTop, 8 ≤ x ^ (ε / 3)` using `(tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop 8`.

Establish `E3 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ 1 / 2 * ‖x ^ (ε / 480)‖` using `(isLittleO_log_rpow_atTop (by positivity : 0 < ε / 480)).bound (by norm_num)`. Establish `E4 : ∀ᶠ x : ℝ in atTop, 4 ≤ x ^ (5 * ε / 24)` using `(tendsto_rpow_atTop (by positivity : 0 < 5 * ε / 24)).eventually_ge_atTop 4`. Establish `E5 : ∀ᶠ x : ℝ in atTop, max (8 * A * K6) (8 * A * K10) ≤ Real.exp (a / 16 * x ^ (ε / 8))` using `(Real.tendsto_exp_atTop.comp (TR.const_mul_atTop (by positivity : 0 < a / 16))).eventually_ge_atTop _`. Take `⟨x₀, hx₀⟩` from `eventually_atTop.1 (E1.and (E2.and (E3.and (E4.and E5))))`. Use `⟨x₀, fun x hx μ v hμ2 hμ hv => ?_⟩` and prove the remaining obligations.

Take `⟨h1, h2, h3, h4, h5⟩` from `hx₀ x hx`. Establish `hx0 : 0 < x` using `by linarith`. Take `⟨R, hR⟩ : ∃ R : ℝ, R = x ^ (ε / 8)` from `⟨_, rfl⟩`. Take `⟨Lb, hLb⟩ : ∃ Lb : ℝ, Lb = x ^ (5 * ε / 24)` from `⟨_, rfl⟩`. Rewrite `h5`, the goal using `[← hR]`.

Rewrite `h4` using `[← hLb]`. Establish `hR1 : 1 ≤ R` using `hR ▸ Real.one_le_rpow h1 (by positivity)`. Establish `hRL : R ≤ Lb`. Rewrite using `[hR, hLb]`. Conclude with `Real.rpow_le_rpow_of_exponent_le h1 (by linarith)`.

Establish `hP3 : x ^ (ε / 3) = Lb * R`. Rewrite using `[hLb, hR, ← Real.rpow_add hx0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hL6 : Lb ^ 6 = R ^ 10`.

Rewrite using `[hLb, hR, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hμL : μ ≤ Lb`.

Establish `hp : 0 ≤ x ^ (ε / 480)` using `by positivity`. Rewrite `h3` using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp]`. Establish `hlog2 : Real.log x ^ 2 ≤ 1 / 4 * x ^ (ε / 240)`. Establish `e : x ^ (ε / 240) = x ^ (ε / 480) * x ^ (ε / 480)`. Rewrite using `[← Real.rpow_add hx0]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← sq_abs]`. Use polynomial arithmetic with `[abs_nonneg (Real.log x)]`. Establish `h6 : x ^ (ε / 5) * x ^ (ε / 240) ≤ Lb`.

Rewrite using `[← Real.rpow_add hx0, hLb]`. Apply `Real.rpow_le_rpow_of_exponent_le h1` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp5 : 0 ≤ x ^ (ε / 5)` using `by positivity`. Establish `h7 : 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 1 / 2 * Lb`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv4 : 4 ≤ v` using `by linarith`. Establish `hv0 : 0 ≤ v` using `by linarith`. Take `⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt v` from `⟨_, rfl⟩`.

Establish `hsv : v = s ^ 2` using `by rw [hs]; exact (Real.sq_sqrt hv0).symm`. Establish `hs2 : 2 ≤ s`. Rewrite using `[hs]`. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[← hs, hsv]`. Establish `hvL : Lb * R / 2 ≤ s ^ 2` using `by rw [← hsv, ← hP3]; exact hv`. Establish `hfin : ∀ Kc : ℝ, 8 * A * Kc ≤ Real.exp (a / 16 * R) → 8 * A * Kc * Real.exp (-(a / 8 * R)) ≤ Real.exp (-(a / 16) * R)`. Introduce `Kc hKc`. Combine the equalities or inequalities in the displayed calculation.

Distinguish the cases in `hcase : μ ≤ s`. Establish `hsR : R / 2 ≤ s`. Establish `h13 : (R / 2) ^ 2 ≤ s ^ 2`. Establish `h14 : R * R ≤ Lb * R` using `mul_le_mul_of_nonneg_right hRL (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `(abs_le_of_sq_le_sq' h13 (by linarith)).2`. Conclude with `(thin_caseA a A μ s R ha hA hμ2 hcase hsR).trans (hfin K6 (le_trans (le_max_left _ _) h5))`. Rewrite `hcase` using `[not_le]`. Conclude with `(thin_caseB a A μ s R Lb ha hA hμ2 (by linarith) hcase hμL hvL hL6 (by linarith)).trans (hfin K10 (le_trans (le_max_right _ _) h5))`.
-/
lemma thin_num (ε a A : ℝ) (hε : 0 < ε) (ha : 0 < a) (hA : 0 ≤ A) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ μ v : ℝ, 2 ≤ μ → μ ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 + 2 → x ^ (ε / 3) / 2 ≤ v →
      A * (μ + Real.sqrt v + v) ^ 3 * Real.exp (-a * v / (μ + Real.sqrt v)) ≤ Real.exp (-(a / 16) * x ^ (ε / 8)) := by
  set K6 : ℝ := ((6 : ℕ).factorial : ℝ) / (a / 4) ^ 6 with hK6
  set K10 : ℝ := ((10 : ℕ).factorial : ℝ) / (a / 8) ^ 10 with hK10
  have TR : Tendsto (fun x : ℝ => x ^ (ε / 8)) atTop atTop := tendsto_rpow_atTop (by positivity)
  have E1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have E2 : ∀ᶠ x : ℝ in atTop, 8 ≤ x ^ (ε / 3) := (tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop 8
  have E3 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ 1 / 2 * ‖x ^ (ε / 480)‖ :=
    (isLittleO_log_rpow_atTop (by positivity : 0 < ε / 480)).bound (by norm_num)
  have E4 : ∀ᶠ x : ℝ in atTop, 4 ≤ x ^ (5 * ε / 24) :=
    (tendsto_rpow_atTop (by positivity : 0 < 5 * ε / 24)).eventually_ge_atTop 4
  have E5 : ∀ᶠ x : ℝ in atTop, max (8 * A * K6) (8 * A * K10) ≤ Real.exp (a / 16 * x ^ (ε / 8)) :=
    (Real.tendsto_exp_atTop.comp (TR.const_mul_atTop (by positivity : 0 < a / 16))).eventually_ge_atTop _
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (E1.and (E2.and (E3.and (E4.and E5))))
  refine ⟨x₀, fun x hx μ v hμ2 hμ hv => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = x ^ (ε / 8) := ⟨_, rfl⟩
  obtain ⟨Lb, hLb⟩ : ∃ Lb : ℝ, Lb = x ^ (5 * ε / 24) := ⟨_, rfl⟩
  rw [← hR] at h5 ⊢
  rw [← hLb] at h4
  have hR1 : 1 ≤ R := hR ▸ Real.one_le_rpow h1 (by positivity)
  have hRL : R ≤ Lb := by
    rw [hR, hLb]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have hP3 : x ^ (ε / 3) = Lb * R := by
    rw [hLb, hR, ← Real.rpow_add hx0]
    congr 1
    ring
  have hL6 : Lb ^ 6 = R ^ 10 := by
    rw [hLb, hR, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  have hμL : μ ≤ Lb := by
    have hp : 0 ≤ x ^ (ε / 480) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp] at h3
    have hlog2 : Real.log x ^ 2 ≤ 1 / 4 * x ^ (ε / 240) := by
      have e : x ^ (ε / 240) = x ^ (ε / 480) * x ^ (ε / 480) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      rw [e, ← sq_abs]
      nlinarith [abs_nonneg (Real.log x)]
    have h6 : x ^ (ε / 5) * x ^ (ε / 240) ≤ Lb := by
      rw [← Real.rpow_add hx0, hLb]
      apply Real.rpow_le_rpow_of_exponent_le h1
      linarith
    have hp5 : 0 ≤ x ^ (ε / 5) := by positivity
    have h7 : 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 1 / 2 * Lb := by
      calc 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 2 * x ^ (ε / 5) * (1 / 4 * x ^ (ε / 240)) := by gcongr
        _ = 1 / 2 * (x ^ (ε / 5) * x ^ (ε / 240)) := by ring
        _ ≤ 1 / 2 * Lb := by gcongr
    linarith
  have hv4 : 4 ≤ v := by linarith
  have hv0 : 0 ≤ v := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt v := ⟨_, rfl⟩
  have hsv : v = s ^ 2 := by rw [hs]; exact (Real.sq_sqrt hv0).symm
  have hs2 : 2 ≤ s := by
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    linarith
  rw [← hs, hsv]
  have hvL : Lb * R / 2 ≤ s ^ 2 := by rw [← hsv, ← hP3]; exact hv
  have hfin : ∀ Kc : ℝ, 8 * A * Kc ≤ Real.exp (a / 16 * R) →
      8 * A * Kc * Real.exp (-(a / 8 * R)) ≤ Real.exp (-(a / 16) * R) := by
    intro Kc hKc
    calc 8 * A * Kc * Real.exp (-(a / 8 * R)) ≤ Real.exp (a / 16 * R) * Real.exp (-(a / 8 * R)) :=
          mul_le_mul_of_nonneg_right hKc (Real.exp_pos _).le
      _ = Real.exp (-(a / 16) * R) := by rw [← Real.exp_add]; congr 1; ring
  by_cases hcase : μ ≤ s
  · have hsR : R / 2 ≤ s := by
      have h13 : (R / 2) ^ 2 ≤ s ^ 2 := by
        have h14 : R * R ≤ Lb * R := mul_le_mul_of_nonneg_right hRL (by linarith)
        nlinarith
      exact (abs_le_of_sq_le_sq' h13 (by linarith)).2
    exact (thin_caseA a A μ s R ha hA hμ2 hcase hsR).trans (hfin K6 (le_trans (le_max_left _ _) h5))
  · rw [not_le] at hcase
    exact (thin_caseB a A μ s R Lb ha hA hμ2 (by linarith) hcase hμL hvL hL6 (by linarith)).trans
      (hfin K10 (le_trans (le_max_right _ _) h5))

/- English proof (translation)
Unfold `Gchi Formalism.ZeroFreeDirichlet.Schi Formalism.ZeroFreeDirichlet.negLD logDerivLAtOne`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma gchi_eq_schi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) :
    Gchi χ y = Formalism.ZeroFreeDirichlet.Schi χ y - Formalism.ZeroFreeDirichlet.negLD χ 1 * y := by
  unfold Gchi Formalism.ZeroFreeDirichlet.Schi Formalism.ZeroFreeDirichlet.negLD logDerivLAtOne
  ring

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `hP hRS hD hRight c₁ hc₁ hc₁'`. Take `⟨CD, hCD⟩` from `hD c₁ hc₁ hc₁'`. Take `⟨C₀, hC₀, hR⟩` from `hRight`. Take `⟨C, hCdef⟩ : ∃ C : ℝ, C = max CD 0` from `⟨_, rfl⟩`. Establish `hC : 0 ≤ C` using `hCdef ▸ le_max_right _ _`.

Take `⟨A, hAdef⟩ : ∃ A : ℝ, A = 2 * Real.pi * Real.exp 1 * (1 + C₀) + 6 * Real.exp 1 * (C + 1) + 16 * (C / c₁ + 24 / c₁ ^ 2) + 8 / c₁` from `⟨_, rfl⟩`. Establish `hA0 : 0 ≤ A`. Establish `ha1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀)` using `mul_nonneg (by positivity) (by linarith)`. Establish `ha2 : 0 ≤ 6 * Real.exp 1 * (C + 1)` using `mul_nonneg (by positivity) (by linarith)`. Establish `ha3 : 0 ≤ 16 * (C / c₁ + 24 / c₁ ^ 2)` using `mul_nonneg (by norm_num) (add_nonneg (div_nonneg hC hc₁.le) (by positivity))`.

Establish `ha4 : 0 ≤ 8 / c₁` using `by positivity`. Rewrite using `[hAdef]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨2 * A, by positivity, ?_⟩` and prove the remaining obligations. Introduce `q _ χ hχ hE y hy`.

Establish `hD' : ∀ s : ℂ, Formalism.ZeroFreeDirichlet.InRegion (c₁ / 2) q s → (∀ β ∈ (∅ : Finset ℝ), s ≠ (β : ℂ)) → ‖Formalism.ZeroFreeDirichlet.negLD χ s + ∑ β ∈ (∅ : Finset ℝ), 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2` using `fun s h1 h2 => (hCD q χ ∅ hχ hE s h1 h2).trans (mul_le_mul_of_nonneg_right (hCdef ▸ le_max_left _ _) (sq_nonneg _))`. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`. Establish `hy0 : 0 < y` using `by linarith`. Take `⟨v, hv⟩ : ∃ v : ℝ, v = Real.log y` from `⟨_, rfl⟩`. Establish `hv0 : 0 < v` using `hv ▸ Real.log_pos (by linarith)`.

Take `⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt v` from `⟨_, rfl⟩`. Establish `hvs : v = s ^ 2` using `by rw [hsdef]; exact (Real.sq_sqrt hv0.le).symm`. Establish `hs0 : 0 < s` using `by rw [hsdef]; exact Real.sqrt_pos.mpr hv0`. Establish `hlq : 0 ≤ Real.log q` using `Real.log_nonneg hq1`. Take `⟨M, hM⟩ : ∃ M : ℝ, M = Real.log q + 2 + s` from `⟨_, rfl⟩`.

Establish `hM2 : 2 ≤ M` using `by rw [hM]; linarith`. Establish `hMs : s ≤ M` using `by rw [hM]; linarith`. Establish `hM0 : 0 < M` using `by linarith`. Take `⟨τ, hτ⟩ : ∃ τ : ℝ, τ = c₁ / 16 * v / M` from `⟨_, rfl⟩`. Establish `hτ0 : 0 ≤ τ` using `by rw [hτ]; positivity`.

Establish `hτM : τ * M = c₁ / 16 * v` using `by rw [hτ]; field_simp`. Establish `hτs : τ ≤ s`. Establish `h1 : τ * M ≤ s * M`. Rewrite using `[hτM, hvs]`. Establish `: c₁ / 16 * s ^ 2 ≤ 1 * s ^ 2` using `mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg s)`.

Establish `: s * s ≤ s * M` using `mul_le_mul_of_nonneg_left hMs hs0.le`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `le_of_mul_le_mul_right h1 hM0`. Take `⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.exp τ` from `⟨_, rfl⟩`. Take `⟨X, hXdef⟩ : ∃ X : ℝ, X = Real.exp (-τ)` from `⟨_, rfl⟩`.

Establish `hT1 : 1 ≤ T` using `by rw [hTdef]; exact Real.one_le_exp hτ0`. Establish `hT0 : 0 < T` using `by linarith`. Establish `hTX : T * X = 1` using `by rw [hTdef, hXdef, ← Real.exp_add]; simp`. Establish `hX0 : 0 < X` using `by rw [hXdef]; exact Real.exp_pos _`. Take `⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log ((q : ℝ) * (T + 2))` from `⟨_, rfl⟩`.

Take `⟨σ₁, hσ₁, hmain⟩` from `Formalism.ZeroFreeDirichlet.chebyshev_character_explicit_general hP hRS c₁ C C₀ hc₁ hc₁' hC hC₀ χ ∅ hχ hE hD' (hR q χ) y T L hy hT1 hLdef.symm`. Rewrite `hmain` using `[Finset.sum_empty, add_zero, ← gchi_eq_schi, ← hv]`. Establish `hlogT : Real.log (T + 2) ≤ 2 + τ`. Rewrite using `[Real.log_le_iff_le_exp (by linarith), Real.exp_add, ← hTdef]`. Establish `h3 : (3 : ℝ) ≤ Real.exp 2` using `by have := Real.add_one_le_exp (2 : ℝ); linarith`.

Use `mul_le_mul_of_nonneg_right h3 hT0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLM : L ≤ M`. Rewrite using `[hLdef, Real.log_mul (by linarith) (by linarith), hM]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hL1 : 1 ≤ L`. Rewrite using `[hLdef, Real.le_log_iff_exp_le (by nlinarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hL0 : 0 ≤ L` using `by linarith`.

Establish `hW1 : 1 ≤ M + v` using `by linarith`. Establish `hP1 : 1 ≤ (M + v) ^ 3` using `one_le_pow₀ hW1`. Establish `hW3 : M + v ≤ (M + v) ^ 3` using `le_self_pow₀ hW1 (by norm_num)`. Establish `h23 : (M + v) ^ 2 ≤ (M + v) ^ 3` using `pow_le_pow_right₀ hW1 (by norm_num)`. Establish `hLW : L ≤ M + v` using `by linarith`.

Establish `hℓP : v ≤ (M + v) ^ 3` using `by linarith`. Establish `hL2P : L ^ 2 ≤ (M + v) ^ 3` using `(pow_le_pow_left₀ hL0 hLW 2).trans h23`. Establish `hL3P : L ^ 3 ≤ (M + v) ^ 3` using `pow_le_pow_left₀ hL0 hLW 3`. Establish `hLP : L ≤ (M + v) ^ 3` using `by linarith`. Establish `hyσ0 : 0 ≤ y ^ σ₁` using `Real.rpow_nonneg hy0.le _`.

Establish `hterms` using `Formalism.ZeroFreeDirichlet.perron_error_terms_sum_bound C C₀ c₁ y T X L ((M + v) ^ 3) (y ^ σ₁) v hc₁ hC hC₀ hy0 hT1 hTX hL0 hyσ0 hℓP hP1 hL2P hL3P hLP`. Rewrite `hterms` using `[← hAdef]`. Establish `htot` using `hmain.trans hterms`. Establish `hWX : T * y ^ σ₁ ≤ y * X`. Establish `hgap : 4 * τ ≤ v * (1 - σ₁)`.

Establish `h1 : c₁ / (4 * M) ≤ c₁ / (4 * L)` using `div_le_div_of_nonneg_left hc₁.le (by linarith) (by linarith)`. Establish `h2 : c₁ / (4 * M) ≤ 1 - σ₁` using `by linarith`. Establish `h3` using `mul_le_mul_of_nonneg_left h2 hv0.le`. Establish `e : v * (c₁ / (4 * M)) = 4 * τ` using `by rw [hτ]; field_simp; ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hyexp : y = Real.exp v` using `by rw [hv, Real.exp_log hy0]`. Rewrite using `[Real.rpow_def_of_pos hy0, ← hv, hTdef, hXdef, hyexp, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hfinal : ‖Gchi χ y‖ ≤ 2 * A * y * (M + v) ^ 3 * X`. Combine the equalities or inequalities in the displayed calculation.

Establish `eX : X = Real.exp (-(c₁ / 16) * v / M)`. Rewrite using `[hXdef, hτ]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hv, ← hsdef, ← hM, ← eX]`.

Conclude with `hfinal`.
-/
theorem smooth_weight_general : SmoothGen := by
  intro hP hRS hD hRight c₁ hc₁ hc₁'
  obtain ⟨CD, hCD⟩ := hD c₁ hc₁ hc₁'
  obtain ⟨C₀, hC₀, hR⟩ := hRight
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max CD 0 := ⟨_, rfl⟩
  have hC : 0 ≤ C := hCdef ▸ le_max_right _ _
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 2 * Real.pi * Real.exp 1 * (1 + C₀) + 6 * Real.exp 1 * (C + 1) +
      16 * (C / c₁ + 24 / c₁ ^ 2) + 8 / c₁ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    have ha1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀) := mul_nonneg (by positivity) (by linarith)
    have ha2 : 0 ≤ 6 * Real.exp 1 * (C + 1) := mul_nonneg (by positivity) (by linarith)
    have ha3 : 0 ≤ 16 * (C / c₁ + 24 / c₁ ^ 2) :=
      mul_nonneg (by norm_num) (add_nonneg (div_nonneg hC hc₁.le) (by positivity))
    have ha4 : 0 ≤ 8 / c₁ := by positivity
    rw [hAdef]; linarith
  refine ⟨2 * A, by positivity, ?_⟩
  intro q _ χ hχ hE y hy
  have hD' : ∀ s : ℂ, Formalism.ZeroFreeDirichlet.InRegion (c₁ / 2) q s → (∀ β ∈ (∅ : Finset ℝ), s ≠ (β : ℂ)) →
      ‖Formalism.ZeroFreeDirichlet.negLD χ s + ∑ β ∈ (∅ : Finset ℝ), 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 :=
    fun s h1 h2 => (hCD q χ ∅ hχ hE s h1 h2).trans
      (mul_le_mul_of_nonneg_right (hCdef ▸ le_max_left _ _) (sq_nonneg _))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hy0 : 0 < y := by linarith
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = Real.log y := ⟨_, rfl⟩
  have hv0 : 0 < v := hv ▸ Real.log_pos (by linarith)
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt v := ⟨_, rfl⟩
  have hvs : v = s ^ 2 := by rw [hsdef]; exact (Real.sq_sqrt hv0.le).symm
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hv0
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Real.log q + 2 + s := ⟨_, rfl⟩
  have hM2 : 2 ≤ M := by rw [hM]; linarith
  have hMs : s ≤ M := by rw [hM]; linarith
  have hM0 : 0 < M := by linarith
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = c₁ / 16 * v / M := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hτM : τ * M = c₁ / 16 * v := by rw [hτ]; field_simp
  have hτs : τ ≤ s := by
    have h1 : τ * M ≤ s * M := by
      rw [hτM, hvs]
      have : c₁ / 16 * s ^ 2 ≤ 1 * s ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg s)
      have : s * s ≤ s * M := mul_le_mul_of_nonneg_left hMs hs0.le
      nlinarith
    exact le_of_mul_le_mul_right h1 hM0
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.exp τ := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = Real.exp (-τ) := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by rw [hTdef]; exact Real.one_le_exp hτ0
  have hT0 : 0 < T := by linarith
  have hTX : T * X = 1 := by rw [hTdef, hXdef, ← Real.exp_add]; simp
  have hX0 : 0 < X := by rw [hXdef]; exact Real.exp_pos _
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log ((q : ℝ) * (T + 2)) := ⟨_, rfl⟩
  obtain ⟨σ₁, hσ₁, hmain⟩ :=
    Formalism.ZeroFreeDirichlet.chebyshev_character_explicit_general hP hRS c₁ C C₀ hc₁ hc₁' hC hC₀ χ ∅ hχ hE hD' (hR q χ) y T L hy hT1 hLdef.symm
  rw [Finset.sum_empty, add_zero, ← gchi_eq_schi, ← hv] at hmain
  have hlogT : Real.log (T + 2) ≤ 2 + τ := by
    rw [Real.log_le_iff_le_exp (by linarith), Real.exp_add, ← hTdef]
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
    have := mul_le_mul_of_nonneg_right h3 hT0.le
    linarith
  have hLM : L ≤ M := by
    rw [hLdef, Real.log_mul (by linarith) (by linarith), hM]
    linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by nlinarith)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hW1 : 1 ≤ M + v := by linarith
  have hP1 : 1 ≤ (M + v) ^ 3 := one_le_pow₀ hW1
  have hW3 : M + v ≤ (M + v) ^ 3 := le_self_pow₀ hW1 (by norm_num)
  have h23 : (M + v) ^ 2 ≤ (M + v) ^ 3 := pow_le_pow_right₀ hW1 (by norm_num)
  have hLW : L ≤ M + v := by linarith
  have hℓP : v ≤ (M + v) ^ 3 := by linarith
  have hL2P : L ^ 2 ≤ (M + v) ^ 3 := (pow_le_pow_left₀ hL0 hLW 2).trans h23
  have hL3P : L ^ 3 ≤ (M + v) ^ 3 := pow_le_pow_left₀ hL0 hLW 3
  have hLP : L ≤ (M + v) ^ 3 := by linarith
  have hyσ0 : 0 ≤ y ^ σ₁ := Real.rpow_nonneg hy0.le _
  have hterms := Formalism.ZeroFreeDirichlet.perron_error_terms_sum_bound C C₀ c₁ y T X L ((M + v) ^ 3) (y ^ σ₁) v hc₁ hC hC₀ hy0
    hT1 hTX hL0 hyσ0 hℓP hP1 hL2P hL3P hLP
  rw [← hAdef] at hterms
  have htot := hmain.trans hterms
  have hWX : T * y ^ σ₁ ≤ y * X := by
    have hgap : 4 * τ ≤ v * (1 - σ₁) := by
      have h1 : c₁ / (4 * M) ≤ c₁ / (4 * L) := div_le_div_of_nonneg_left hc₁.le (by linarith) (by linarith)
      have h2 : c₁ / (4 * M) ≤ 1 - σ₁ := by linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hv0.le
      have e : v * (c₁ / (4 * M)) = 4 * τ := by rw [hτ]; field_simp; ring
      linarith
    have hyexp : y = Real.exp v := by rw [hv, Real.exp_log hy0]
    rw [Real.rpow_def_of_pos hy0, ← hv, hTdef, hXdef, hyexp, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    nlinarith
  have hfinal : ‖Gchi χ y‖ ≤ 2 * A * y * (M + v) ^ 3 * X := by
    calc ‖Gchi χ y‖ ≤ A * (M + v) ^ 3 * (y * X + T * y ^ σ₁) := htot
      _ ≤ A * (M + v) ^ 3 * (y * X + y * X) := by gcongr
      _ = 2 * A * y * (M + v) ^ 3 * X := by ring
  have eX : X = Real.exp (-(c₁ / 16) * v / M) := by
    rw [hXdef, hτ]; congr 1; ring
  rw [← hv, ← hsdef, ← hM, ← eX]
  exact hfinal

/- English proof (translation)
Introduce `hP hRS hD hR ε c₁ hε hc₁ hc₁'`. Take `⟨A, hA, hS⟩` from `smooth_weight_general hP hRS hD hR c₁ hc₁ hc₁'`. Take `⟨x1, hN⟩` from `thin_num ε (c₁ / 16) A hε (by positivity) hA`. Take `⟨x2, hx2⟩` from `eventually_atTop.1 ((tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop (5 : ℝ))`. Use `⟨max x1 x2, fun x hx q _ χ hχ hE hq y hy => ?_⟩` and prove the remaining obligations.

Establish `h5 : 5 ≤ x ^ (ε / 3)` using `hx2 x (le_trans (le_max_right _ _) hx)`. Take `⟨X, hX⟩ : ∃ X : ℝ, X = x ^ (ε / 3)` from `⟨_, rfl⟩`. Rewrite `h5`, `hy` using `[← hX]`. Establish `hexp : X + 1 ≤ Real.exp X` using `Real.add_one_le_exp X`. Establish `hy2 : 2 ≤ y` using `by linarith`.

Establish `hy0 : 0 < y` using `by linarith`. Establish `hlog3 : Real.log 3 ≤ 2`. Use `Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogy : X / 2 ≤ Real.log y`.

Establish `h4 : Real.log (Real.exp X / 3) ≤ Real.log y` using `Real.log_le_log (by positivity) hy`. Rewrite `h4` using `[Real.log_div (Real.exp_pos X).ne' (by norm_num), Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`. Establish `hlq : 0 ≤ Real.log q` using `Real.log_nonneg hq1`.

Establish `hnum` using `hN x (le_trans (le_max_left _ _) hx) (Real.log q + 2) (Real.log y) (by linarith) (by linarith) (by rw [← hX]; exact hlogy)`. Combine the equalities or inequalities in the displayed calculation. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thin_of_no_exceptional_zero : ThinOfNoExc := by
  intro hP hRS hD hR ε c₁ hε hc₁ hc₁'
  obtain ⟨A, hA, hS⟩ := smooth_weight_general hP hRS hD hR c₁ hc₁ hc₁'
  obtain ⟨x1, hN⟩ := thin_num ε (c₁ / 16) A hε (by positivity) hA
  obtain ⟨x2, hx2⟩ := eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop (5 : ℝ))
  refine ⟨max x1 x2, fun x hx q _ χ hχ hE hq y hy => ?_⟩
  have h5 : 5 ≤ x ^ (ε / 3) := hx2 x (le_trans (le_max_right _ _) hx)
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = x ^ (ε / 3) := ⟨_, rfl⟩
  rw [← hX] at h5 hy
  have hexp : X + 1 ≤ Real.exp X := Real.add_one_le_exp X
  have hy2 : 2 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlogy : X / 2 ≤ Real.log y := by
    have h4 : Real.log (Real.exp X / 3) ≤ Real.log y := Real.log_le_log (by positivity) hy
    rw [Real.log_div (Real.exp_pos X).ne' (by norm_num), Real.log_exp] at h4
    linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hnum := hN x (le_trans (le_max_left _ _) hx) (Real.log q + 2) (Real.log y) (by linarith) (by linarith)
    (by rw [← hX]; exact hlogy)
  calc ‖Gchi χ y‖ ≤ A * y * (Real.log q + 2 + Real.sqrt (Real.log y) + Real.log y) ^ 3 *
        Real.exp (-(c₁ / 16) * Real.log y / (Real.log q + 2 + Real.sqrt (Real.log y))) := hS q χ hχ hE y hy2
    _ = y * (A * (Real.log q + 2 + Real.sqrt (Real.log y) + Real.log y) ^ 3 *
        Real.exp (-(c₁ / 16) * Real.log y / (Real.log q + 2 + Real.sqrt (Real.log y)))) := by ring
    _ ≤ y * Real.exp (-(c₁ / 16 / 16) * x ^ (ε / 8)) := mul_le_mul_of_nonneg_left hnum hy0.le
    _ = y * Real.exp (-(c₁ / 256) * x ^ (ε / 8)) := by
        congr 2
        ring

/- English proof (translation)
Introduce and unpack `⟨c, hc, hZ⟩`. Use `⟨min c (1 / 1000), lt_min hc (by norm_num), (min_le_right _ _).trans (by norm_num), ?_⟩` and prove the remaining obligations. Introduce `q _ χ hreal`. Use `⟨by simp, by simp, ?_⟩` and prove the remaining obligations. Introduce `s hs hz`.

It suffices to derive a contradiction. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`. Establish `h2le : (2 : ℝ) ≤ (q : ℝ) * (|s.im| + 2)`. Use `abs_nonneg s.im` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hlog2 : Real.log 2 ≤ Real.log ((q : ℝ) * (|s.im| + 2))` using `Real.log_le_log (by norm_num) h2le`. Establish `hl2` using `Real.log_two_gt_d9`. Establish `hLpos : 0 < Real.log ((q : ℝ) * (|s.im| + 2))` using `by linarith`. Unfold `Formalism.ZeroFreeDirichlet.InRegion at hs`. Establish `hs' : Formalism.ZeroFreeDirichlet.InRegion c q s`.

Unfold `Formalism.ZeroFreeDirichlet.InRegion`. Establish `: min c (1 / 1000) / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c / Real.log ((q : ℝ) * (|s.im| + 2))` using `div_le_div_of_nonneg_right (min_le_left _ _) hLpos.le`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨h2, -, him, -, -⟩` from `hZ q χ s hs' hz`. Establish `hsre : s = ((s.re : ℝ) : ℂ)` using `Complex.ext (by simp) (by simp [him])`.

Establish `hσ : 1 - 1 / 400 < s.re`. Establish `h3 : min c (1 / 1000) / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ (1 / 1000) / (1 / 2)` using `div_le_div₀ (by norm_num) (min_le_right _ _) (by norm_num) (by linarith)`. Evaluate the numerical expressions using `at h3`. Combine the linear equalities and inequalities to obtain the conclusion. Use `hreal h2 s.re hσ` as an intermediate fact.

Rewrite `this` using `[← hsre]`. Conclude with `this hz.2`.
-/
theorem no_exceptional_zero_of_real : NoExcOfReal := by
  rintro ⟨c, hc, hZ⟩
  refine ⟨min c (1 / 1000), lt_min hc (by norm_num), (min_le_right _ _).trans (by norm_num), ?_⟩
  intro q _ χ hreal
  refine ⟨by simp, by simp, ?_⟩
  intro s hs hz
  exfalso
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h2le : (2 : ℝ) ≤ (q : ℝ) * (|s.im| + 2) := by
    have := abs_nonneg s.im
    nlinarith
  have hlog2 : Real.log 2 ≤ Real.log ((q : ℝ) * (|s.im| + 2)) := Real.log_le_log (by norm_num) h2le
  have hl2 := Real.log_two_gt_d9
  have hLpos : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) := by linarith
  unfold Formalism.ZeroFreeDirichlet.InRegion at hs
  have hs' : Formalism.ZeroFreeDirichlet.InRegion c q s := by
    unfold Formalism.ZeroFreeDirichlet.InRegion
    have : min c (1 / 1000) / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c / Real.log ((q : ℝ) * (|s.im| + 2)) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hLpos.le
    linarith
  obtain ⟨h2, -, him, -, -⟩ := hZ q χ s hs' hz
  have hsre : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hσ : 1 - 1 / 400 < s.re := by
    have h3 : min c (1 / 1000) / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ (1 / 1000) / (1 / 2) :=
      div_le_div₀ (by norm_num) (min_le_right _ _) (by norm_num) (by linarith)
    norm_num at h3
    linarith
  have := hreal h2 s.re hσ
  rw [← hsre] at this
  exact this hz.2

/- English proof (translation)
Introduce `_ _ _` and use `Iff.rfl`.
-/
theorem proposition_at_iff : PrimePairExistsIffConditions := fun _ _ _ => Iff.rfl

/- English proof (translation)
Introduce `h`. Establish `hp` using `chi_eight_primitive`. Rewrite `hp` using `[isPrimitive_def, h, conductor_one]`. Evaluate the numerical expressions using `at hp`.
-/
lemma chi_eight_ne_one : chi8 ≠ 1 := by
  intro h
  have hp := chi_eight_primitive
  rw [isPrimitive_def, h, conductor_one] at hp
  norm_num at hp

/- English proof (translation)
The claim follows from `h σ (by simpa using hσ) (by simpa using hQ)`.
-/
lemma box_real {N : ℕ} [NeZero N] {Q : ℝ} (hQ : 0 ≤ Q) {χ : DirichletCharacter ℂ N} (h : ZeroFreeBox Q χ) (σ : ℝ)
    (hσ : 1 - 1 / 400 < σ) : LFunction χ (σ : ℂ) ≠ 0 :=
  h σ (by simpa using hσ) (by simpa using hQ)

/- English proof (translation)
Introduce `hG hZ hP hRS hD hR hNR hNE`. Take `⟨c₁, hc₁, hc₁', hNo⟩` from `no_exceptional_zero_of_real hZ`. Use `⟨c₁ / 256, by positivity, fun ε A hε hA => ?_⟩` and prove the remaining obligations. Take `⟨x1, hT⟩` from `thin_of_no_exceptional_zero hP hRS hD hR ε c₁ hε hc₁ hc₁'`. Take `⟨x2, hL⟩` from `hNE ε A hε hA`.

Take `⟨x3, hO⟩` from `thin_one_of hG ε (c₁ / 256) hε`. Use `⟨max (max x1 x2) x3, fun x hx C q d _ _ h25 => ?_⟩` and prove the remaining obligations. Establish `hx1 : x1 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `hx2 : x2 ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `hx3 : x3 ≤ x` using `le_trans (le_max_right _ _) hx`.

Take `⟨h8, h16, w1, w2, w3, w4, hs, hsp, g1, g2, g3, g4, g5, g6, v1, v2, v3⟩` from `h25`. Establish `hH` using `prime_congruence_conditions q d Fact.out Fact.out h8 h16 hs`. Use `⟨hH, fun e he => ⟨?_, (valuesIff_valid e q d hH x ε C).2 ⟨v1, v2, v3⟩⟩⟩` and prove the remaining obligations. Use `(thin_iff e q d _ _).2 ⟨fun ψ hψ y hy => ?_, fun y hy => hO x hx3 y hy⟩` and prove the remaining obligations. Establish `hX1 : 0 < X1 ε x` using `Real.exp_pos _`.

Establish `hX2 : 0 < X2 ε x` using `Real.exp_pos _`. Establish `hQ1 : 0 ≤ 8 * X1 ε x` using `by positivity`. Establish `hQ2 : 0 ≤ 8 * X1 ε x * X2 ε x` using `by positivity`. Take `⟨-, ⟨hdvd, -⟩, hne⟩` from `character_of_facts e q d hH ψ`. Establish `hlq : Real.log (condOf e q d ψ) ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2`.

Establish `hup` using `(hL x hx2 (2 ^ e) q d Nat.one_le_two_pow he w1 w2 w3 w4).2.2.2.2`. Rewrite `hup` using `[← modulus_formula e q d]`. Use `le_trans (Real.log_le_log ?_ ?_) hup` and prove the remaining obligations. Conclude with `Nat.pos_of_ne_zero (NeZero.ne (condOf e q d ψ))` after adjusting the coercions. Conclude with `Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne (hostN e q d))) hdvd` after adjusting the coercions.

Use `hT x hx1 _ (chiOf e q d ψ) (hne hψ).1 (hNo _ _ ?_) hlq y hy` and prove the remaining obligations. Introduce `hsq σ hσ`. Break down `real_characters_input e q d hH ψ hsq with c | c | c | c | c | c | c | c` into its components or cases. Conclude with `absurd c hψ`. Rewrite using `[(same_character_g _ _ _ _ c).2.2.2.1]`.

Distinguish the cases in `h1 : σ < 1`. Conclude with `hNR.2 σ (by linarith) h1`. Conclude with `LFunction_ne_zero_of_one_le_re chi8 (Or.inl chi_eight_ne_one) (by simpa using not_lt.1 h1)`. Conclude with `box_real hQ1 (zeroFreeBox_same c g1.2.2.2) σ hσ`. Conclude with `box_real hQ1 (zeroFreeBox_same c g2.2.2.2) σ hσ`.

Conclude with `box_real hQ2 (zeroFreeBox_same c g3.2.2.2) σ hσ`. Conclude with `box_real hQ2 (zeroFreeBox_same c g4.2.2.2) σ hσ`. Conclude with `box_real hQ2 (zeroFreeBox_same c g5.2.2.2) σ hσ`. Conclude with `box_real hQ2 (zeroFreeBox_same c g6.2.2.2) σ hσ`.
-/
theorem analytic_input_of_proposition : AnalyticInputsFromPNT := by
  intro hG hZ hP hRS hD hR hNR hNE
  obtain ⟨c₁, hc₁, hc₁', hNo⟩ := no_exceptional_zero_of_real hZ
  refine ⟨c₁ / 256, by positivity, fun ε A hε hA => ?_⟩
  obtain ⟨x1, hT⟩ := thin_of_no_exceptional_zero hP hRS hD hR ε c₁ hε hc₁ hc₁'
  obtain ⟨x2, hL⟩ := hNE ε A hε hA
  obtain ⟨x3, hO⟩ := thin_one_of hG ε (c₁ / 256) hε
  refine ⟨max (max x1 x2) x3, fun x hx C q d _ _ h25 => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : x3 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨h8, h16, w1, w2, w3, w4, hs, hsp, g1, g2, g3, g4, g5, g6, v1, v2, v3⟩ := h25
  have hH := prime_congruence_conditions q d Fact.out Fact.out h8 h16 hs
  refine ⟨hH, fun e he => ⟨?_, (valuesIff_valid e q d hH x ε C).2 ⟨v1, v2, v3⟩⟩⟩
  refine (thin_iff e q d _ _).2 ⟨fun ψ hψ y hy => ?_, fun y hy => hO x hx3 y hy⟩
  have hX1 : 0 < X1 ε x := Real.exp_pos _
  have hX2 : 0 < X2 ε x := Real.exp_pos _
  have hQ1 : 0 ≤ 8 * X1 ε x := by positivity
  have hQ2 : 0 ≤ 8 * X1 ε x * X2 ε x := by positivity
  obtain ⟨-, ⟨hdvd, -⟩, hne⟩ := character_of_facts e q d hH ψ
  have hlq : Real.log (condOf e q d ψ) ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 := by
    have hup := (hL x hx2 (2 ^ e) q d Nat.one_le_two_pow he w1 w2 w3 w4).2.2.2.2
    rw [← modulus_formula e q d] at hup
    refine le_trans (Real.log_le_log ?_ ?_) hup
    · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (condOf e q d ψ))
    · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne (hostN e q d))) hdvd
  refine hT x hx1 _ (chiOf e q d ψ) (hne hψ).1 (hNo _ _ ?_) hlq y hy
  intro hsq σ hσ
  rcases real_characters_input e q d hH ψ hsq with c | c | c | c | c | c | c | c
  · exact absurd c hψ
  · rw [(same_character_g _ _ _ _ c).2.2.2.1]
    by_cases h1 : σ < 1
    · exact hNR.2 σ (by linarith) h1
    · exact LFunction_ne_zero_of_one_le_re chi8 (Or.inl chi_eight_ne_one) (by simpa using not_lt.1 h1)
  · exact box_real hQ1 (zeroFreeBox_same c g1.2.2.2) σ hσ
  · exact box_real hQ1 (zeroFreeBox_same c g2.2.2.2) σ hσ
  · exact box_real hQ2 (zeroFreeBox_same c g3.2.2.2) σ hσ
  · exact box_real hQ2 (zeroFreeBox_same c g4.2.2.2) σ hσ
  · exact box_real hQ2 (zeroFreeBox_same c g5.2.2.2) σ hσ
  · exact box_real hQ2 (zeroFreeBox_same c g6.2.2.2) σ hσ

/- English proof (translation)
The claim follows from `analytic_input_of_proposition Formalism.ZF.gzPNT Formalism.ZeroFreeDirichlet.zFRDirichlet Formalism.ZeroFreeDirichlet.perron_formula_character Formalism.ZeroFreeDirichlet.rectangle_contour_shift_character Formalism.ZeroFreeDirichlet.logDerivRegionChi Formalism.ZeroFreeDirichlet.l …`.
-/
theorem analytic_input_conditional : AnalyticInputsOfNoSmallRealZero :=
  analytic_input_of_proposition Formalism.ZF.gzPNT Formalism.ZeroFreeDirichlet.zFRDirichlet Formalism.ZeroFreeDirichlet.perron_formula_character Formalism.ZeroFreeDirichlet.rectangle_contour_shift_character
    Formalism.ZeroFreeDirichlet.logDerivRegionChi Formalism.ZeroFreeDirichlet.l_log_deriv_right

end Formalism.LFunctionChainParameters.LBr2
