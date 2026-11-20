import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaB
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm

noncomputable section

namespace GlobalTheory.BorelChar

open Matrix Formalism.UG

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext e)`.
-/
theorem ext_mat {g h : GU σ n} (e : ⟪g⟫ = ⟪h⟫) : g = h := Subtype.ext (Units.ext e)

/- English proof (translation)
Take `⟨hσσ, hσv, hσϖ, hϖ, -, -, -⟩` from `hU`. Establish `hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ)` using `hϖ`. Establish `h0 : ϖ ≠ 0`. Introduce `h`. Rewrite `hϖ'` using `[h, map_zero]`.

Conclude with `WithZero.exp_ne_zero hϖ'.symm`. Establish `hϖ1 : Valued.v ϖ ≤ 1`. Rewrite using `[hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]`. Evaluate the numerical expressions. Use `set U := ⟪u⟫ with hUdef`.

Take `⟨M, hM⟩` from `GlobalTheory.UnitarySwap.exists_pow_mem hϖ' U`. Set `b : Fin n → ℤ` to `fun i => (M : ℤ) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))`. Establish `hb : ∀ i : Fin n, b i.rev = -b i`. Introduce `i`. Use `i.isLt` as an intermediate fact.

Simplify using `only [b, Fin.val_rev]`. Rewrite using `[Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨s, hs, hs'⟩` from `Formalism.UG.P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ b i) (fun i => by`.

Rewrite using `[map_zpow₀, hσϖ, hb, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])`. Establish `hpow : ∀ k : ℤ, 0 ≤ k → Valued.v (ϖ ^ k) ≤ 1`. Introduce `k hk`. Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le hk`. Rewrite using `[zpow_natCast, map_pow]`.

Conclude with `pow_le_one₀ zero_le hϖ1`. Use `set k := s * u * s⁻¹ with hkdef`. Establish `hkm : ⟪k⟫ = Matrix.diagonal (fun i => ϖ ^ b i) * U * Matrix.diagonal (fun i => (ϖ ^ b i)⁻¹)`. Rewrite using `[hkdef, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hs, hs']`. Establish `hI : Formalism.UG.P.fIwasawaInt ⟪k⟫`.

Introduce `i j`. Rewrite using `[hkm, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases. Establish `hle : (M : ℤ) ≤ b i - b j`. Establish `: (i.val : ℤ) + 1 ≤ j.val` using `by exact_mod_cast hij`.

Simplify using `only [b]`. Use the polynomial consequences of the given equalities and inequalities. Establish `e : ϖ ^ b i * U i j * (ϖ ^ b j)⁻¹ = ϖ ^ (b i - b j - M) * (ϖ ^ M * U i j)`. Rewrite using `[zpow_sub₀ h0, zpow_sub₀ h0, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e, map_mul]`. Conclude with `mul_le_one' (hpow _ (by omega)) (hM i j)`. Establish `e1 : U i i = 1` using `hu.2 i`. Rewrite using `[e1, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ h0), map_one]`. Establish `e1 : U i j = 0` using `hu.1 i j hij`.

Rewrite using `[e1, mul_zero, zero_mul, map_zero]`. Conclude with `zero_le`. Establish `hkK : k ∈ Formalism.UG.KU σ n`. Use `Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ k) hI` as an intermediate fact. Establish `e : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ k) = k` using `Subtype.ext (Units.ext rfl)`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Conclude with `⟨s, Formalism.UG.P.fSatake_borel_of_diag hs, hkK⟩`.
-/
theorem exists_conj_mem_K {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {u : GU σ n} (hu : IsUnipU u) :
    ∃ s : GU σ n, IsBorelU s ∧ s * u * s⁻¹ ∈ KU σ n := by
  obtain ⟨hσσ, hσv, hσϖ, hϖ, -, -, -⟩ := hU
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  set U := ⟪u⟫ with hUdef
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
  have hkm : ⟪k⟫ = Matrix.diagonal (fun i => ϖ ^ b i) * U * Matrix.diagonal (fun i => (ϖ ^ b i)⁻¹) := by
    rw [hkdef, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hs, hs']
  have hI : Formalism.UG.P.fIwasawaInt ⟪k⟫ := by
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
  exact ⟨s, Formalism.UG.P.fSatake_borel_of_diag hs, hkK⟩

/- English proof (translation)
Unfold `tMat`. Rewrite using `[diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `split_ifs <;> simp [zpow_add₀ h0, neg_add] <;> ring`.
-/
theorem tMat_add (ϖ : L) (h0 : ϖ ≠ 0) (m : ℕ) (a c : Fin m → ℤ) :
    tMat ϖ n m (a + c) = tMat ϖ n m a * tMat ϖ n m c := by
  unfold tMat
  rw [diagonal_mul_diagonal]
  congr 1; funext i
  split_ifs <;> simp [zpow_add₀ h0, neg_add] <;> ring

/- English proof (translation)
Unfold `tMat`. Rewrite using `[← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem tMat_zero (ϖ : L) (m : ℕ) : tMat ϖ n m 0 = 1 := by
  unfold tMat
  rw [← diagonal_one]
  congr 1; funext i
  split_ifs <;> simp

/- English proof (translation)
Introduce `L _ _ ϖ σ q hU n f hmul hK y hy b hb`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h`. Use `hU.2.2.2.1` as an intermediate fact. Rewrite `this` using `[h, Valuation.map_zero]`.

Conclude with `absurd this WithZero.zero_ne_coe`. Establish `h1 : f 1 = 1` using `hK 1 (one_mem _) Formalism.UG.P.fSatake_borel_one`. Establish `hinv : ∀ b, IsBorelU b → f b * f b⁻¹ = 1` using `fun b hb => by`. Rewrite using `[← hmul _ _ hb (Formalism.UG.P.fSatake_borel_inv hb), mul_inv_cancel, h1]`. Establish `hunip : ∀ u, IsUnipU u → f u = 1`.

Introduce `u hu`. Take `⟨s, hs, hsK⟩` from `exists_conj_mem_K hU hu`. Establish `hsu` using `Formalism.UG.P.fSatake_borel_mul hs hu.1`. Use `hK _ hsK (Formalism.UG.P.fSatake_borel_mul hsu (Formalism.UG.P.fSatake_borel_inv hs))` as an intermediate fact. Rewrite `this` using `[hmul _ _ hsu (Formalism.UG.P.fSatake_borel_inv hs), hmul _ _ hs hu.1]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hm : 2 * (n / 2) ≤ n` using `by omega`. Establish `hT : ∀ a : Fin (n / 2) → ℤ, ∃ t : GU σ n, (t).1.1 = tMat ϖ n (n / 2) a` using `fun a => Formalism.UG.P.fSatake_tMat_exists hU hm a`. Use `choose T hTm using hT`. Establish `hTb : ∀ a, IsBorelU (T a)` using `fun a => Formalism.UG.P.fSatake_borel_tMat (hTm a)`.

Establish `hTadd : ∀ a c, T (a + c) = T a * T c` using `fun a c => ext_mat (by`. Rewrite using `[Subgroup.coe_mul, Units.val_mul, hTm, hTm, hTm, tMat_add ϖ hϖ0])`. Establish `hT0 : T 0 = 1` using `ext_mat (by rw [hTm, tMat_zero]; rfl)`. Establish `hg : ∀ a c, f (T (a + c)) = f (T a) * f (T c)` using `fun a c => by`. Rewrite using `[hTadd, hmul _ _ (hTb a) (hTb c)]`.

Establish `hgu : ∀ a, f (T a) * f (T (-a)) = 1` using `fun a => by`. Rewrite using `[← hg, add_neg_cancel, hT0, h1]`. Set `G : Multiplicative (Fin (n / 2) → ℤ) →* ℂˣ` to `MonoidHom.mk' (fun a => ⟨f (T a.toAdd), f (T (-a.toAdd)), hgu _, by rw [mul_comm]; exact hgu _⟩) (fun a c => Units.ext (by simp only [toAdd_mul, Units.val_mul]; exact hg _ _))`. Establish `hGs : ∀ k, (G (Multiplicative.ofAdd (Pi.single k 1)) : ℂ) = y k` using `fun k => hy k _ (hTm _)`. Establish `hTval : ∀ a, f (T a) = ∏ k, y k ^ a k`.

Introduce `a`. Establish `ea : Multiplicative.ofAdd a = ∏ k, (Multiplicative.ofAdd (Pi.single k (1 : ℤ))) ^ a k`. Repeatedly rewrite using `[← ofAdd_zsmul, ← ofAdd_sum]`. Use `congr 1`. Use `conv_lhs => rw [← Finset.univ_sum_single a]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Simplify using `[Pi.single_apply]`. Use `congrArg (fun z => (G z : ℂ)) ea` as an intermediate fact. Simplify using `only [map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, hGs] at this`.

Conclude with `this`. Take `⟨a, u, hu, k', hk', he⟩` from `Formalism.UG.P.fSatake_cell_exists hU hm (by omega) hb (one_mem (KU σ n))`. Establish `hbe : b = T a * u * k'` using `ext_mat (by`. Rewrite using `[Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, hTm, ← he, mul_one])`. Establish `htu` using `Formalism.UG.P.fSatake_borel_mul (hTb a) hu.1`.

Establish `hkb : IsBorelU k'`. Establish `e : k' = (T a * u)⁻¹ * b` using `by rw [hbe]; group`. Rewrite using `[e]`. Conclude with `Formalism.UG.P.fSatake_borel_mul (Formalism.UG.P.fSatake_borel_inv htu) hb`. Establish `hfb : f b = f (T a)`.

Rewrite using `[hbe, hmul _ _ htu hkb, hmul _ _ (hTb a) hu.1, hunip u hu, hK k' hk' hkb, mul_one, mul_one]`. Rewrite using `[hfb, hTval]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `hj : (j : ℕ) < n` using `by omega`.

Establish `hd : (b).1.1 ⟨j, hj⟩ ⟨j, hj⟩ = ϖ ^ (a j) * (k').1.1 ⟨j, hj⟩ ⟨j, hj⟩`. Rewrite using `[hbe, Formalism.UG.P.fSatake_borel_diag_mul htu hkb, Formalism.UG.P.fSatake_borel_diag_mul (hTb a) hu.1, hu.2, mul_one, hTm, Formalism.UG.P.fSatake_tMat_apply_lt ϖ a j hj]`. Establish `hw0` using `Formalism.UG.P.fSatake_ne_zero_of_borel hkb ⟨j, hj⟩`. Establish `hwr0` using `Formalism.UG.P.fSatake_ne_zero_of_borel hkb (⟨j, hj⟩ : Fin n).rev`. Establish `hpair` using `congrArg ordL (Formalism.UG.P.fSatake_unit_diag hkb ⟨j, hj⟩)`.

Rewrite `hpair` using `[Formalism.UG.P.fSatake_ord_mul ((map_ne_zero σ).2 hw0) hwr0, Formalism.UG.P.fSatake_ord_of_v (hU.2.1 _), Formalism.UG.P.fSatake_ord_one]`. Establish `hn1` using `Formalism.UG.P.fSatake_ord_nonneg hw0 (Formalism.UG.P.fSatake_K_int hk' _ _)`. Establish `hn2` using `Formalism.UG.P.fSatake_ord_nonneg hwr0 (Formalism.UG.P.fSatake_K_int hk' _ _)`. Establish `h3` using `congrArg ordL hd`. Rewrite `h3` using `[Formalism.UG.P.fSatake_ord_mul (zpow_ne_zero _ hϖ0) hw0, Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1]`.

Use `show a j = ordL ((b).1.1 ⟨j, hj⟩ ⟨j, hj⟩)`. Use linear arithmetic over natural numbers and integers.
-/
theorem borel_char : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (f : GU σ n → ℂ), (∀ b b', IsBorelU b → IsBorelU b' → f (b * b') = f b * f b') →
    (∀ k ∈ KU σ n, IsBorelU k → f k = 1) → ∀ y : Fin (n / 2) → ℂ,
    (∀ (k : Fin (n / 2)) (t : GU σ n), t.1.1 = tMat ϖ n (n / 2) (Pi.single k 1) → f t = y k) →
    ∀ b, IsBorelU b → f b = ∏ k, y k ^ ordL (b.1.1 (GlobalTheory.SphTheta.lo n k) (GlobalTheory.SphTheta.lo n k)) := by
  intro L _ _ ϖ σ q hU n f hmul hK y hy b hb
  have hϖ0 : ϖ ≠ 0 := by
    intro h; have := hU.2.2.2.1; rw [h, Valuation.map_zero] at this; exact absurd this WithZero.zero_ne_coe
  have h1 : f 1 = 1 := hK 1 (one_mem _) Formalism.UG.P.fSatake_borel_one
  have hinv : ∀ b, IsBorelU b → f b * f b⁻¹ = 1 := fun b hb => by
    rw [← hmul _ _ hb (Formalism.UG.P.fSatake_borel_inv hb), mul_inv_cancel, h1]

  have hunip : ∀ u, IsUnipU u → f u = 1 := by
    intro u hu
    obtain ⟨s, hs, hsK⟩ := exists_conj_mem_K hU hu
    have hsu := Formalism.UG.P.fSatake_borel_mul hs hu.1
    have := hK _ hsK (Formalism.UG.P.fSatake_borel_mul hsu (Formalism.UG.P.fSatake_borel_inv hs))
    rw [hmul _ _ hsu (Formalism.UG.P.fSatake_borel_inv hs), hmul _ _ hs hu.1] at this
    calc f u = f u * (f s * f s⁻¹) := by rw [hinv s hs, mul_one]
      _ = f s * f u * f s⁻¹ := by ring
      _ = 1 := this

  have hm : 2 * (n / 2) ≤ n := by omega
  have hT : ∀ a : Fin (n / 2) → ℤ, ∃ t : GU σ n, (t).1.1 = tMat ϖ n (n / 2) a :=
    fun a => Formalism.UG.P.fSatake_tMat_exists hU hm a
  choose T hTm using hT
  have hTb : ∀ a, IsBorelU (T a) := fun a => Formalism.UG.P.fSatake_borel_tMat (hTm a)
  have hTadd : ∀ a c, T (a + c) = T a * T c := fun a c => ext_mat (by
    rw [Subgroup.coe_mul, Units.val_mul, hTm, hTm, hTm, tMat_add ϖ hϖ0])
  have hT0 : T 0 = 1 := ext_mat (by rw [hTm, tMat_zero]; rfl)
  have hg : ∀ a c, f (T (a + c)) = f (T a) * f (T c) := fun a c => by
    rw [hTadd, hmul _ _ (hTb a) (hTb c)]
  have hgu : ∀ a, f (T a) * f (T (-a)) = 1 := fun a => by
    rw [← hg, add_neg_cancel, hT0, h1]
  let G : Multiplicative (Fin (n / 2) → ℤ) →* ℂˣ := MonoidHom.mk'
    (fun a => ⟨f (T a.toAdd), f (T (-a.toAdd)), hgu _, by rw [mul_comm]; exact hgu _⟩)
    (fun a c => Units.ext (by simp only [toAdd_mul, Units.val_mul]; exact hg _ _))
  have hGs : ∀ k, (G (Multiplicative.ofAdd (Pi.single k 1)) : ℂ) = y k := fun k => hy k _ (hTm _)
  have hTval : ∀ a, f (T a) = ∏ k, y k ^ a k := by
    intro a
    have ea : Multiplicative.ofAdd a = ∏ k, (Multiplicative.ofAdd (Pi.single k (1 : ℤ))) ^ a k := by
      simp_rw [← ofAdd_zsmul, ← ofAdd_sum]
      congr 1
      conv_lhs => rw [← Finset.univ_sum_single a]
      refine Finset.sum_congr rfl fun k _ => ?_
      funext j
      simp [Pi.single_apply]
    have := congrArg (fun z => (G z : ℂ)) ea
    simp only [map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, hGs] at this
    exact this

  obtain ⟨a, u, hu, k', hk', he⟩ := Formalism.UG.P.fSatake_cell_exists hU hm (by omega) hb (one_mem (KU σ n))
  have hbe : b = T a * u * k' := ext_mat (by
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, hTm, ← he, mul_one])
  have htu := Formalism.UG.P.fSatake_borel_mul (hTb a) hu.1
  have hkb : IsBorelU k' := by
    have e : k' = (T a * u)⁻¹ * b := by rw [hbe]; group
    rw [e]; exact Formalism.UG.P.fSatake_borel_mul (Formalism.UG.P.fSatake_borel_inv htu) hb
  have hfb : f b = f (T a) := by
    rw [hbe, hmul _ _ htu hkb, hmul _ _ (hTb a) hu.1, hunip u hu, hK k' hk' hkb, mul_one, mul_one]
  rw [hfb, hTval]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1

  have hj : (j : ℕ) < n := by omega
  have hd : (b).1.1 ⟨j, hj⟩ ⟨j, hj⟩ = ϖ ^ (a j) * (k').1.1 ⟨j, hj⟩ ⟨j, hj⟩ := by
    rw [hbe, Formalism.UG.P.fSatake_borel_diag_mul htu hkb, Formalism.UG.P.fSatake_borel_diag_mul (hTb a) hu.1, hu.2, mul_one,
      hTm, Formalism.UG.P.fSatake_tMat_apply_lt ϖ a j hj]
  have hw0 := Formalism.UG.P.fSatake_ne_zero_of_borel hkb ⟨j, hj⟩
  have hwr0 := Formalism.UG.P.fSatake_ne_zero_of_borel hkb (⟨j, hj⟩ : Fin n).rev
  have hpair := congrArg ordL (Formalism.UG.P.fSatake_unit_diag hkb ⟨j, hj⟩)
  rw [Formalism.UG.P.fSatake_ord_mul ((map_ne_zero σ).2 hw0) hwr0, Formalism.UG.P.fSatake_ord_of_v (hU.2.1 _),
    Formalism.UG.P.fSatake_ord_one] at hpair
  have hn1 := Formalism.UG.P.fSatake_ord_nonneg hw0 (Formalism.UG.P.fSatake_K_int hk' _ _)
  have hn2 := Formalism.UG.P.fSatake_ord_nonneg hwr0 (Formalism.UG.P.fSatake_K_int hk' _ _)
  have h3 := congrArg ordL hd
  rw [Formalism.UG.P.fSatake_ord_mul (zpow_ne_zero _ hϖ0) hw0, Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1] at h3
  show a j = ordL ((b).1.1 ⟨j, hj⟩ ⟨j, hj⟩)
  omega

end GlobalTheory.BorelChar
