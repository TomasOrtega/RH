import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCoset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UniformizerPowerTorusMemNormalUnitarySubgroupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormalHyp

/- English proof (translation)
Introduce `L _ _ ϖ σ q n hU N hN hK u hu`. Take `⟨hσσ, hσv, hσϖ, hϖ, -, -, -⟩` from `hU`. Establish `hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ)` using `hϖ`. Establish `h0 : ϖ ≠ 0`. Introduce `h`.

Rewrite `hϖ'` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hϖ'.symm`. Establish `hϖ1 : Valued.v ϖ ≤ 1`. Rewrite using `[hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]`. Evaluate the numerical expressions.

Use `set U := (((u : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hUdef`. Take `⟨M, hM⟩` from `GlobalTheory.UnitarySwap.exists_pow_mem hϖ' U`. Set `b : Fin n → ℤ` to `fun i => (M : ℤ) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))`. Establish `hb : ∀ i : Fin n, b i.rev = -b i`. Introduce `i`.

Use `i.isLt` as an intermediate fact. Simplify using `only [b, Fin.val_rev]`. Rewrite using `[Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨s, hs, hs'⟩` from `Formalism.UG.P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ b i) (fun i => by`. Rewrite using `[map_zpow₀, hσϖ, hb, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])`. Establish `hpow : ∀ k : ℤ, 0 ≤ k → Valued.v (ϖ ^ k) ≤ 1`. Introduce `k hk`. Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le hk`.

Rewrite using `[zpow_natCast, map_pow]`. Conclude with `pow_le_one₀ zero_le hϖ1`. Use `set k := s * u * s⁻¹ with hkdef`. Establish `hkm : (((k : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => ϖ ^ b i) * U * Matrix.diagonal (fun i => (ϖ ^ b i)⁻¹)`. Rewrite using `[hkdef, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hs, hs']`.

Establish `hI : Formalism.UG.P.fIwasawaInt (((k : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)`. Introduce `i j`. Rewrite using `[hkm, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases. Establish `hle : (M : ℤ) ≤ b i - b j`.

Establish `: (i.val : ℤ) + 1 ≤ j.val` using `by exact_mod_cast hij`. Simplify using `only [b]`. Use the polynomial consequences of the given equalities and inequalities. Establish `e : ϖ ^ b i * U i j * (ϖ ^ b j)⁻¹ = ϖ ^ (b i - b j - M) * (ϖ ^ M * U i j)`. Rewrite using `[zpow_sub₀ h0, zpow_sub₀ h0, zpow_natCast]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e, map_mul]`. Conclude with `mul_le_one' (hpow _ (by omega)) (hM i j)`. Establish `e1 : U i i = 1` using `hu.2 i`. Rewrite using `[e1, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ h0), map_one]`.

Establish `e1 : U i j = 0` using `hu.1 i j hij`. Rewrite using `[e1, mul_zero, zero_mul, map_zero]`. Conclude with `zero_le`. Establish `hkK : k ∈ Formalism.UG.KU σ n`. Use `Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ k) hI` as an intermediate fact.

Establish `e : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ k) = k` using `Subtype.ext (Units.ext rfl)`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Use `hN.conj_mem k (hK hkK) s⁻¹` as an intermediate fact. Establish `e : s⁻¹ * k * s⁻¹⁻¹ = u` using `by rw [hkdef]; group`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem unip_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ N : Subgroup (Formalism.UG.GU σ n), N.Normal → Formalism.UG.KU σ n ≤ N → ∀ u : Formalism.UG.GU σ n, Formalism.UG.IsUnipU u → u ∈ N := by
  intro L _ _ ϖ σ q n hU N hN hK u hu
  obtain ⟨hσσ, hσv, hσϖ, hϖ, -, -, -⟩ := hU
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  set U := (((u : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hUdef
  obtain ⟨M, hM⟩ := GlobalTheory.UnitarySwap.exists_pow_mem hϖ' U
  let b : Fin n → ℤ := fun i => (M : ℤ) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))
  have hb : ∀ i : Fin n, b i.rev = -b i := by
    intro i
    have := i.isLt
    simp only [b, Fin.val_rev]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  obtain ⟨s, hs, hs'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ b i) (fun i => by
    rw [map_zpow₀, hσϖ, hb, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  have hpow : ∀ k : ℤ, 0 ≤ k → Valued.v (ϖ ^ k) ≤ 1 := by
    intro k hk
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, map_pow]
    exact pow_le_one₀ zero_le hϖ1
  set k := s * u * s⁻¹ with hkdef
  have hkm : (((k : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ϖ ^ b i) * U * Matrix.diagonal (fun i => (ϖ ^ b i)⁻¹) := by
    rw [hkdef, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hs, hs']
  have hI : Formalism.UG.P.fIwasawaInt (((k : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    intro i j
    rw [hkm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hle : (M : ℤ) ≤ b i - b j := by
        have : (i.val : ℤ) + 1 ≤ j.val := by exact_mod_cast hij
        simp only [b]
        nlinarith
      have e : ϖ ^ b i * U i j * (ϖ ^ b j)⁻¹ = ϖ ^ (b i - b j - M) * (ϖ ^ M * U i j) := by
        rw [zpow_sub₀ h0, zpow_sub₀ h0, zpow_natCast]
        field_simp
      rw [e, map_mul]
      exact mul_le_one' (hpow _ (by omega)) (hM i j)
    · have e1 : U i i = 1 := hu.2 i
      rw [e1, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ h0), map_one]
    · have e1 : U i j = 0 := hu.1 i j hij
      rw [e1, mul_zero, zero_mul, map_zero]; exact zero_le
  have hkK : k ∈ Formalism.UG.KU σ n := by
    have := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ k) hI
    have e : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ k) = k := Subtype.ext (Units.ext rfl)
    rwa [e] at this
  have := hN.conj_mem k (hK hkK) s⁻¹
  have e : s⁻¹ * k * s⁻¹⁻¹ = u := by rw [hkdef]; group
  rwa [e] at this

/- English proof (translation)
Introduce `L _ _ ϖ σ q n hU N hN hK hu t ht`. Establish `hU'` using `hU`. Take `⟨hσσ, hσv, hσϖ, hϖ, -, -, -⟩` from `hU'`. Establish `hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ)` using `hϖ`. Establish `h0 : ϖ ≠ 0`.

Introduce `h`. Rewrite `hϖ'` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hϖ'.symm`. Use `set T := (((t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTdef`. Establish `hTd : T = Matrix.diagonal (fun i => T i i)`.

Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.diagonal_apply_ne _ h]`.

Conclude with `ht i j h`. Establish `hunit : ∀ i : Fin n, σ (T i i) * T i.rev i.rev = 1`. Introduce `i`. Use `congrFun (congrFun (Formalism.UG.P.fIwasawa_mem_un σ t) i) i.rev` as an intermediate fact. Rewrite `this` using `[Formalism.UG.P.fIwasawa_gram, Formalism.UG.P.fIwasawa_antiJ, if_pos rfl]`.

Unfold `Formalism.UG.P.fIwasawaH at this`. Rewrite `this` using `[Finset.sum_eq_single i.rev]`. Rewrite `this` using `[Fin.rev_rev]`. Conclude with `this`. Introduce `j _ hj show σ (T j.rev i) * T j i.rev = 0`.

Rewrite using `[ht j i.rev (fun h => hj h), mul_zero]`. Simplify using the standard rewrite rules. Establish `hne : ∀ i, T i i ≠ 0`. Introduce `i h`. Use `hunit i` as an intermediate fact.

Rewrite `this` using `[h, map_zero, zero_mul]`. Conclude with `zero_ne_one this`. Establish `hv0 : ∀ i, Valued.v (T i i) ≠ 0` using `fun i => by simpa using hne i`. Set `c : Fin n → ℤ` to `fun i => - WithZero.log (Valued.v (T i i))`. Establish `hvrev : ∀ i, Valued.v (T i.rev i.rev) = (Valued.v (T i i))⁻¹`.

Introduce `i`. Use `congrArg Valued.v (hunit i)` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, hσv]`. Conclude with `(eq_inv_of_mul_eq_one_right this)`. Establish `hc : ∀ i : Fin n, c i.rev = -c i`.

Introduce `i`. Simplify using `only [c]`. Rewrite using `[hvrev, WithZero.log_inv]`. Take `⟨s, hs, hs'⟩` from `Formalism.UG.P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ c i) (fun i => by`. Rewrite using `[map_zpow₀, hσϖ, hc, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])`.

Establish `hsN : s ∈ N` using `GlobalTheory.T.uniformizerPowerTorus_mem_normal_unitarySubgroup L ϖ σ q n hU N hN hK hu c hc s hs`. Establish `hvpow : ∀ i, Valued.v (ϖ ^ c i) = Valued.v (T i i)`. Introduce `i`. Rewrite using `[map_zpow₀, hϖ', ← WithZero.exp_zsmul, ← WithZero.exp_log (hv0 i)]`. Simplify using `[c]`.

Establish `hε : (((s⁻¹ * t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => (ϖ ^ c i)⁻¹ * T i i)`. Rewrite using `[Subgroup.coe_mul, Units.val_mul, hs', ← hTdef, hTd, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Establish `hI : Formalism.UG.P.fIwasawaInt (((s⁻¹ * t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)`. Introduce `i j`. Rewrite using `[hε]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Rewrite using `[Matrix.diagonal_apply_eq, map_mul, map_inv₀, hvpow, inv_mul_cancel₀ (hv0 i)]`. Rewrite using `[Matrix.diagonal_apply_ne _ h, map_zero]`. Conclude with `zero_le`. Establish `hkK : s⁻¹ * t ∈ Formalism.UG.KU σ n`. Use `Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ (s⁻¹ * t)) hI` as an intermediate fact.

Establish `e : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ (s⁻¹ * t)) = s⁻¹ * t` using `Subtype.ext (Units.ext rfl)`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `e : t = s * (s⁻¹ * t)` using `by group`. Rewrite using `[e]`. Conclude with `N.mul_mem hsN (hK hkK)`.
-/
theorem diag_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ N : Subgroup (Formalism.UG.GU σ n), N.Normal → Formalism.UG.KU σ n ≤ N → (∀ u : Formalism.UG.GU σ n, Formalism.UG.IsUnipU u → u ∈ N) → ∀ t : Formalism.UG.GU σ n, (∀ i j : Fin n, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) → t ∈ N := by
  intro L _ _ ϖ σ q n hU N hN hK hu t ht
  have hU' := hU
  obtain ⟨hσσ, hσv, hσϖ, hϖ, -, -, -⟩ := hU'
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  set T := (((t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTdef
  have hTd : T = Matrix.diagonal (fun i => T i i) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · rw [Matrix.diagonal_apply_ne _ h]; exact ht i j h
  have hunit : ∀ i : Fin n, σ (T i i) * T i.rev i.rev = 1 := by
    intro i
    have := congrFun (congrFun (Formalism.UG.P.fIwasawa_mem_un σ t) i) i.rev
    rw [Formalism.UG.P.fIwasawa_gram, Formalism.UG.P.fIwasawa_antiJ, if_pos rfl] at this
    unfold Formalism.UG.P.fIwasawaH at this
    rw [Finset.sum_eq_single i.rev] at this
    · rw [Fin.rev_rev] at this; exact this
    · intro j _ hj
      show σ (T j.rev i) * T j i.rev = 0
      rw [ht j i.rev (fun h => hj h), mul_zero]
    · simp
  have hne : ∀ i, T i i ≠ 0 := by
    intro i h; have := hunit i; rw [h, map_zero, zero_mul] at this; exact zero_ne_one this
  have hv0 : ∀ i, Valued.v (T i i) ≠ 0 := fun i => by simpa using hne i
  let c : Fin n → ℤ := fun i => - WithZero.log (Valued.v (T i i))
  have hvrev : ∀ i, Valued.v (T i.rev i.rev) = (Valued.v (T i i))⁻¹ := by
    intro i
    have := congrArg Valued.v (hunit i)
    rw [map_mul, map_one, hσv] at this
    exact (eq_inv_of_mul_eq_one_right this)
  have hc : ∀ i : Fin n, c i.rev = -c i := by
    intro i
    simp only [c]
    rw [hvrev, WithZero.log_inv]
  obtain ⟨s, hs, hs'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ c i) (fun i => by
    rw [map_zpow₀, hσϖ, hc, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  have hsN : s ∈ N := GlobalTheory.T.uniformizerPowerTorus_mem_normal_unitarySubgroup L ϖ σ q n hU N hN hK hu c hc s hs
  have hvpow : ∀ i, Valued.v (ϖ ^ c i) = Valued.v (T i i) := by
    intro i
    rw [map_zpow₀, hϖ', ← WithZero.exp_zsmul, ← WithZero.exp_log (hv0 i)]
    simp [c]
  have hε : (((s⁻¹ * t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => (ϖ ^ c i)⁻¹ * T i i) := by
    rw [Subgroup.coe_mul, Units.val_mul, hs', ← hTdef, hTd, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; simp
  have hI : Formalism.UG.P.fIwasawaInt (((s⁻¹ * t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    intro i j
    rw [hε]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, map_mul, map_inv₀, hvpow, inv_mul_cancel₀ (hv0 i)]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero]; exact zero_le
  have hkK : s⁻¹ * t ∈ Formalism.UG.KU σ n := by
    have := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ (s⁻¹ * t)) hI
    have e : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ (s⁻¹ * t)) = s⁻¹ * t := Subtype.ext (Units.ext rfl)
    rwa [e] at this
  have e : t = s * (s⁻¹ * t) := by group
  rw [e]
  exact N.mul_mem hsN (hK hkK)

/- English proof (translation)
Introduce `L _ _ σ n b hb`. Take `⟨d, hd, hd'⟩` from `Formalism.UG.P.fSatake_diag_exists (σ := σ) (fun i => (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) (Formalism.UG.P.fSatake_unit_diag hb)`. Establish `hne : ∀ i, (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i ≠ 0`. Introduce `i h0`. Use `Formalism.UG.P.fSatake_unit_diag hb i` as an intermediate fact.

Rewrite `this` using `[h0, map_zero, zero_mul]`. Conclude with `zero_ne_one this`. Establish `hu : (((d⁻¹ * b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => ((((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)⁻¹) * (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)`. Rewrite using `[Subgroup.coe_mul, Units.val_mul, hd']`. Use `⟨d, d⁻¹ * b, fun i j hij => by rw [hd, Matrix.diagonal_apply_ne _ hij], ⟨fun i j hji => ?_, fun i => ?_⟩, by group⟩` and prove the remaining obligations.

Rewrite using `[hu, Matrix.diagonal_mul, hb i j hji, mul_zero]`. Rewrite using `[hu, Matrix.diagonal_mul, inv_mul_cancel₀ (hne i)]`.
-/
theorem borel_eq_diag_mul_unip : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (b : Formalism.UG.GU σ n), Formalism.UG.IsBorelU b → ∃ d u : Formalism.UG.GU σ n, (∀ i j : Fin n, i ≠ j → ((d : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) ∧ Formalism.UG.IsUnipU u ∧ b = d * u := by
  intro L _ _ σ n b hb
  obtain ⟨d, hd, hd'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ)
    (fun i => (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)
    (Formalism.UG.P.fSatake_unit_diag hb)
  have hne : ∀ i, (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
    intro i h0; have := Formalism.UG.P.fSatake_unit_diag hb i; rw [h0, map_zero, zero_mul] at this; exact zero_ne_one this
  have hu : (((d⁻¹ * b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ((((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)⁻¹) *
        (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [Subgroup.coe_mul, Units.val_mul, hd']
  refine ⟨d, d⁻¹ * b, fun i j hij => by rw [hd, Matrix.diagonal_apply_ne _ hij], ⟨fun i j hji => ?_, fun i => ?_⟩, by group⟩
  · rw [hu, Matrix.diagonal_mul, hb i j hji, mul_zero]
  · rw [hu, Matrix.diagonal_mul, inv_mul_cancel₀ (hne i)]

open Formalism.UG in
/- English proof (translation)
Take `⟨U, rfl⟩` from `hJ`. Set `c` to `GlobalTheory.UnramDoubleCoset.intConj hU.2.1`. Establish `hc : ∀ x, c (c x) = x` using `fun x => Subtype.ext (hU.1 x)`. Set `ι` to `(intL L).subtype`. Set `B : Matrix (Fin n) (Fin n) (intL L)` to `U`.

Establish `hB : cT c B = B`. Use extensionality with `i j`. Use `show σ ((B j i : intL L) : L) = (B i j : L)`. Conclude with `hh j i`. Take `⟨p, hp⟩` from `GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hc (GlobalTheory.UnramDoubleCoset.exists_dvd_norm_sub_X hU) hB U.isUnit`.

Establish `hu : IsUnit B` using `U.isUnit`. Establish `h2 : IsUnit (Polynomial.aeval B p)` using `isUnit_of_mul_isUnit_right (by rw [hp]; exact hu)`. Take `⟨h, hh', eh⟩` from `GlobalTheory.UnramDoubleCoset.exists_antiJ_frame hU n`. Use `set K : GL (Fin n) L := bc ι h2.unit with hKdef`. Establish `hK : (K : Matrix (Fin n) (Fin n) L) = (Polynomial.aeval B p).map ι` using `rfl`.

Establish `hJ : ((bc ι U : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = cT σ (K : Matrix (Fin n) (Fin n) L) * K`. Rewrite using `[hK, GlobalTheory.UnitaryDoubleCoset.cT_map ι (c := c) (fun _ => rfl), ← Matrix.map_mul, hp]`. Both sides reduce to the same expression. Use `⟨K⁻¹ * h, mul_mem (inv_mem ⟨_, rfl⟩) hh', ?_⟩` and prove the remaining obligations. Rewrite using `[hJ, Units.val_mul, cT_mul, ← eh, Matrix.mul_one]`.

Establish `e1 : cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * cT σ (K : Matrix (Fin n) (Fin n) L) = 1`. Rewrite using `[← cT_mul, Units.mul_inv, cT_one]`. Establish `e2 : (K : Matrix (Fin n) (Fin n) L) * ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1` using `Units.mul_inv K`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = cT σ (h : Matrix (Fin n) (Fin n) L) * h := by rw [e1, e2, Matrix.mul_one, Matrix.mul_one]`.
-/
theorem frame {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q n : ℕ}
    (hU : IsUnramInv ϖ σ q) {J : GL (Fin n) L} (hJ : J ∈ GLint (Fin n) (intL L))
    (hh : ∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) :
    ∃ P ∈ GLint (Fin n) (intL L), cT σ (P : Matrix (Fin n) (Fin n) L) * (J : Matrix (Fin n) (Fin n) L) * P = antiJ L n := by
  obtain ⟨U, rfl⟩ := hJ
  let c := GlobalTheory.UnramDoubleCoset.intConj hU.2.1
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hU.1 x)
  let ι := (intL L).subtype
  let B : Matrix (Fin n) (Fin n) (intL L) := U
  have hB : cT c B = B := by
    ext i j
    show σ ((B j i : intL L) : L) = (B i j : L)
    exact hh j i
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hc (GlobalTheory.UnramDoubleCoset.exists_dvd_norm_sub_X hU) hB U.isUnit
  have hu : IsUnit B := U.isUnit
  have h2 : IsUnit (Polynomial.aeval B p) := isUnit_of_mul_isUnit_right (by rw [hp]; exact hu)
  obtain ⟨h, hh', eh⟩ := GlobalTheory.UnramDoubleCoset.exists_antiJ_frame hU n
  set K : GL (Fin n) L := bc ι h2.unit with hKdef
  have hK : (K : Matrix (Fin n) (Fin n) L) = (Polynomial.aeval B p).map ι := rfl
  have hJ : ((bc ι U : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = cT σ (K : Matrix (Fin n) (Fin n) L) * K := by
    rw [hK, GlobalTheory.UnitaryDoubleCoset.cT_map ι (c := c) (fun _ => rfl), ← Matrix.map_mul, hp]; rfl
  refine ⟨K⁻¹ * h, mul_mem (inv_mem ⟨_, rfl⟩) hh', ?_⟩
  rw [hJ, Units.val_mul, cT_mul, ← eh, Matrix.mul_one]
  have e1 : cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * cT σ (K : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  have e2 : (K : Matrix (Fin n) (Fin n) L) * ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv K
  calc cT σ (h : Matrix (Fin n) (Fin n) L) * cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (cT σ (K : Matrix (Fin n) (Fin n) L) * K) * (((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * h)
      = cT σ (h : Matrix (Fin n) (Fin n) L) * (cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * cT σ (K : Matrix (Fin n) (Fin n) L)) * ((K : Matrix (Fin n) (Fin n) L) * ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) * h := by
        simp only [Matrix.mul_assoc]
    _ = cT σ (h : Matrix (Fin n) (Fin n) L) * h := by rw [e1, e2, Matrix.mul_one, Matrix.mul_one]

open Formalism.UG in
/- English proof (translation)
Establish `h2` using `unip_mem L ϖ σ q n hU N hN hK`. Establish `h3` using `diag_mem L ϖ σ q n hU N hN hK h2`. Rewrite using `[eq_top_iff]`. Introduce `g _`. Take `⟨b, k, hb, hk, rfl⟩` from `Formalism.UG.P.fIwasawa_iwasawa σ hU.1 hU.2.1 g`.

Take `⟨d, u, hd, hu, rfl⟩` from `borel_eq_diag_mul_unip L σ n b hb`. Conclude with `N.mul_mem (N.mul_mem (h3 d hd) (h2 u hu)) (hK hk)`.
-/
theorem antiJ_case {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q n : ℕ}
    (hU : IsUnramInv ϖ σ q) (N : Subgroup (GU σ n)) (hN : N.Normal) (hK : KU σ n ≤ N) : N = ⊤ := by
  have h2 := unip_mem L ϖ σ q n hU N hN hK
  have h3 := diag_mem L ϖ σ q n hU N hN hK h2
  rw [eq_top_iff]
  intro g _
  obtain ⟨b, k, hb, hk, rfl⟩ := Formalism.UG.P.fIwasawa_iwasawa σ hU.1 hU.2.1 g
  obtain ⟨d, u, hd, hu, rfl⟩ := borel_eq_diag_mul_unip L σ n b hb
  exact N.mul_mem (N.mul_mem (h3 d hd) (h2 u hu)) (hK hk)

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q n J hU hq hJ hh N hN hK`. Take `⟨P, hP, eP⟩` from `frame hU hJ hh`. Establish `memφ : ∀ g : Formalism.UG.GU σ n, P * (g : GL (Fin n) L) * P⁻¹ ∈ Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L)`. Introduce `g`. Simplify using `using GlobalTheory.InertDoubleCoset.conj_mem_UJ σ (GlobalTheory.InertDoubleCoset.inv_frame σ eP) g.2`.

Establish `memψ : ∀ g : Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L), P⁻¹ * (g : GL (Fin n) L) * P ∈ Formalism.UG.GU σ n` using `fun g => GlobalTheory.InertDoubleCoset.conj_mem_UJ σ eP g.2`. Set `φ : Formalism.UG.GU σ n →* Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L)` to `{ toFun := fun g => ⟨P * (g : GL (Fin n) L) * P⁻¹, memφ g⟩ map_one' := Subtype.ext (by simp) map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }`. Establish `hK' : Formalism.UG.KU σ n ≤ N.comap φ`. Introduce `k hk`. Use `show φ k ∈ N`.

Apply `hK` to reduce the goal to its premises. Use `show P * (k : GL (Fin n) L) * P⁻¹ ∈ _`. Conclude with `mul_mem (mul_mem hP (Subgroup.mem_subgroupOf.1 hk).2) (inv_mem hP)`. Establish `htop` using `antiJ_case hU (N.comap φ) (hN.comap φ) hK'`. Rewrite using `[eq_top_iff]`.

Introduce `g _`. Establish `hm : (⟨P⁻¹ * (g : GL (Fin n) L) * P, memψ g⟩ : Formalism.UG.GU σ n) ∈ N.comap φ` using `by rw [htop]; trivial`. Establish `e : φ ⟨P⁻¹ * (g : GL (Fin n) L) * P, memψ g⟩ = g` using `Subtype.ext (by show P * (P⁻¹ * (g : GL (Fin n) L) * P) * P⁻¹ = g group)`. Rewrite using `[← e]`. Conclude with `hm`.
-/
theorem normal_closure_hyp : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (J : GL (Fin n) L), Formalism.UG.IsUnramInv ϖ σ q → Odd q → J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) → ∀ N : Subgroup (Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L)), N.Normal → (∀ g : Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L), (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → g ∈ N) → N = ⊤ := by
  intro L _ _ _ ϖ σ q n J hU hq hJ hh N hN hK
  obtain ⟨P, hP, eP⟩ := frame hU hJ hh
  have memφ : ∀ g : Formalism.UG.GU σ n, P * (g : GL (Fin n) L) * P⁻¹ ∈ Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L) := by
    intro g
    simpa using GlobalTheory.InertDoubleCoset.conj_mem_UJ σ (GlobalTheory.InertDoubleCoset.inv_frame σ eP) g.2
  have memψ : ∀ g : Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L), P⁻¹ * (g : GL (Fin n) L) * P ∈ Formalism.UG.GU σ n :=
    fun g => GlobalTheory.InertDoubleCoset.conj_mem_UJ σ eP g.2
  let φ : Formalism.UG.GU σ n →* Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L) :=
    { toFun := fun g => ⟨P * (g : GL (Fin n) L) * P⁻¹, memφ g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hK' : Formalism.UG.KU σ n ≤ N.comap φ := by
    intro k hk
    show φ k ∈ N
    apply hK
    show P * (k : GL (Fin n) L) * P⁻¹ ∈ _
    exact mul_mem (mul_mem hP (Subgroup.mem_subgroupOf.1 hk).2) (inv_mem hP)
  have htop := antiJ_case hU (N.comap φ) (hN.comap φ) hK'
  rw [eq_top_iff]
  intro g _
  have hm : (⟨P⁻¹ * (g : GL (Fin n) L) * P, memψ g⟩ : Formalism.UG.GU σ n) ∈ N.comap φ := by rw [htop]; trivial
  have e : φ ⟨P⁻¹ * (g : GL (Fin n) L) * P, memψ g⟩ = g := Subtype.ext (by
    show P * (P⁻¹ * (g : GL (Fin n) L) * P) * P⁻¹ = g
    group)
  rw [← e]
  exact hm

end GlobalTheory.NormalHyp
