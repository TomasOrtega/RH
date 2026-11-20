import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.AdjKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.DetVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.BdxLog

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

/- English proof (translation)
Establish `hdvd : l ^ padicValNat l X ∣ X` using `pow_padicValNat_dvd`. Use `⟨padicValNat l X, Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd, ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `hdvd`. Establish `hm0 : ¬ l ∣ m`. Introduce and unpack `⟨k, rfl⟩`.

Apply `pow_succ_padicValNat_not_dvd (p := l) h0` to reduce the goal to its premises. Conclude with `⟨k, by rw [pow_succ, mul_assoc]; exact hm⟩`. Establish `hu : IsUnit (m : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff]`. Conclude with `le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hm0 (by simpa using h))`.

Establish `hX : (X : ℤ_[l]) = (l : ℤ_[l]) ^ padicValNat l X * m` using `by conv_lhs => rw [hm]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hX]`. Simplify using `using mul_dvd_mul_left ((l : ℤ_[l]) ^ padicValNat l X) (hu.dvd (a := 1))`.
-/
private theorem nat_dvd_pow (l : ℕ) [hl : Fact l.Prime] (X : ℕ) (h0 : X ≠ 0) :
    ∃ r : ℕ, l ^ r ≤ X ∧ (X : ℤ_[l]) ∣ (l : ℤ_[l]) ^ r := by
  have hdvd : l ^ padicValNat l X ∣ X := pow_padicValNat_dvd
  refine ⟨padicValNat l X, Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd, ?_⟩
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : ¬ l ∣ m := by
    rintro ⟨k, rfl⟩
    apply pow_succ_padicValNat_not_dvd (p := l) h0
    exact ⟨k, by rw [pow_succ, mul_assoc]; exact hm⟩
  have hu : IsUnit (m : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hm0 (by simpa using h))
  have hX : (X : ℤ_[l]) = (l : ℤ_[l]) ^ padicValNat l X * m := by
    conv_lhs => rw [hm]
    push_cast
    rfl
  rw [hX]
  simpa using mul_dvd_mul_left ((l : ℤ_[l]) ^ padicValNat l X) (hu.dvd (a := 1))

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `bdxLog`. Use `⟨C, hC0, ?_⟩` and prove the remaining obligations. Introduce `E Ω _ _ _ _ _ _ N hN hcyc l _ D hproc e he`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Establish `hl2 : 2 ≤ l` using `(Fact.out : l.Prime).two_le`.

Establish `hM0 : N * l ≠ 0` using `Nat.mul_ne_zero hN.ne' (by omega)`. Use `haveI : NeZero (N * l) := ⟨hM0⟩`. Take `⟨ρ0, hρ0⟩` from `actEx E Ω N hcyc`. Establish `hNM : N ∣ N * l` using `dvd_mul_right N l`. Establish `hρ` using `(actFacts E Ω N ρ0 hρ0).2.2.2.2 (N * l) hNM`.

Use `set ρ := ρ0.comp (ZMod.unitsMap hNM) with hρdef`. Take `⟨_, _, hcard, _, _⟩` from `actFacts E Ω (N * l) ρ hρ`. Take `⟨hconj, hne⟩` from `actConj E Ω (N * l) ρ hρ`. Establish `hlM : l ∣ N * l` using `dvd_mul_left l N`. Establish `hcop : (2 * (N * l) + 1).Coprime (N * l)`.

Simplify using `[Nat.coprime_mul_left_add_left]`. Establish `hodd : Odd (2 * (N * l) + 1)` using `odd_two_mul_add_one _`. Take `⟨z, hzI, hzK⟩` from `zKill E Ω l D e (N * l) ρ hρ he hproc hlM _ hcop hodd`. Establish `hφs : Function.Surjective ⇑((piQ ρ)⁻¹)`. Introduce `y`.

Take `⟨b, hb⟩` from `piQ_surjective ρ y⁻¹`. Conclude with `⟨b, by simp [hb]⟩`. Establish `hφ1 : ((piQ ρ)⁻¹) (-1) ≠ 1`. Simplify using `using hne`. Take `⟨r0, hr0, hdet⟩` from `detVal l _ (N * l) _ e _ hcop hφs hφ1 he (by omega) z hzI`.

Establish `hT : Nat.totient (N * l) ≠ 0` using `(Nat.totient_pos.mpr (NeZero.pos _)).ne'`. Take `⟨r1, hr1le, hr1dvd⟩` from `nat_dvd_pow l (Nat.totient (N * l)) hT`. Use `⟨r0 + r1, ?_, ?_⟩` and prove the remaining obligations. Establish `hb` using `hC N l e hN hl2 he`. Establish `hr1 : (r1 : ℝ) * Real.log l ≤ Real.log ((N : ℝ) * l)`.

Rewrite using `[← Real.log_pow]`. Apply `Real.log_le_log (by positivity)` to reduce the goal to its premises. Conclude with `hr1le.trans (Nat.totient_le _)` after adjusting the coercions. Rewrite `hr0` using `[hcard]`. Establish `hd : (1 : ℝ) ≤ Module.finrank ℚ E` using `by exact_mod_cast Module.finrank_pos`.

Establish `hB` using `Real.log_natCast_nonneg (bdX (N * l) (2 * (N * l) + 1) (e + 1))`. Establish `hL : 0 ≤ Real.log ((N : ℝ) * l)` using `Real.log_nonneg (by`. Establish `: (1 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `: (2 : ℝ) ≤ l` using `by exact_mod_cast hl2`. Use the proof step `nlinarith)`.

Establish `h1` using `mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℝ) ≤ Module.finrank ℚ E)`. Establish `h2` using `mul_nonneg (sub_nonneg.2 hd) hL`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Introduce `x hx`.

Take `⟨hxS, hxE⟩` from `Submodule.mem_inf.mp hx`. Rewrite `hxE` using `[Module.End.mem_eigenspace_iff]`. Establish `hK` using `hzK x hxS`. Establish `hcm : ((piQ ρ)⁻¹) (-1) = piQ ρ (-1)`. Rewrite using `[MonoidHom.inv_apply, ← map_inv, inv_neg_one]`.

Establish `hc : (actRep D (e : ℤ) ρ (((piQ ρ)⁻¹) (-1))) (Nat.totient (N * l) • x) = (((-1) ^ (e + 1) : ℤ) : ℤ_[l]) • (Nat.totient (N * l) • x)`. Rewrite using `[hcm, actRep_piQ, hconj, map_nsmul]`. Express the relevant statement in the definitionally equal form `Nat.totient (N * l) • (cAct D (e : ℤ)) x = _`. Rewrite using `[hxE, smul_comm]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hcc : ((piQ ρ)⁻¹) (-1) * ((piQ ρ)⁻¹) (-1) = 1`. Rewrite using `[← map_mul]`. Simplify using the standard rewrite rules. Establish `hεε : ((-1) ^ (e + 1) : ℤ) * (-1) ^ (e + 1) = 1`.

Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules. Establish `hkill` using `adjKill ℤ_[l] _ _ (actRep D (e : ℤ) ρ) _ _ hcc hφ1 hεε z _ hc hK`. Take `⟨u, hu⟩` from `hdet`. Take `⟨v, hv⟩` from `hr1dvd`.

Rewrite using `[pow_add, hu, hv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Nat.cast_smul_eq_nsmul ℤ_[l], smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = 0 := by rw [hkill, smul_zero]`.
-/
theorem UpperTheory.V.Odd.killPow :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l), Procyc E Ω l → ∀ e : ℕ, 1 ≤ e → ∃ r : ℕ, (r : ℝ) * Real.log l ≤ C * Module.finrank ℚ E * (e + 1) * Real.log ((e : ℝ) * l * N) ∧ ∀ x ∈ ShaMinus D e, (l : ℤ_[l]) ^ r • x = 0 := by
  obtain ⟨C, hC0, hC⟩ := bdxLog
  refine ⟨C, hC0, ?_⟩
  intro E Ω _ _ _ _ _ _ N hN hcyc l _ D hproc e he
  haveI : NeZero N := ⟨hN.ne'⟩
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hM0 : N * l ≠ 0 := Nat.mul_ne_zero hN.ne' (by omega)
  haveI : NeZero (N * l) := ⟨hM0⟩
  obtain ⟨ρ0, hρ0⟩ := actEx E Ω N hcyc
  have hNM : N ∣ N * l := dvd_mul_right N l
  have hρ := (actFacts E Ω N ρ0 hρ0).2.2.2.2 (N * l) hNM
  set ρ := ρ0.comp (ZMod.unitsMap hNM) with hρdef
  obtain ⟨_, _, hcard, _, _⟩ := actFacts E Ω (N * l) ρ hρ
  obtain ⟨hconj, hne⟩ := actConj E Ω (N * l) ρ hρ
  have hlM : l ∣ N * l := dvd_mul_left l N
  have hcop : (2 * (N * l) + 1).Coprime (N * l) := by
    simp [Nat.coprime_mul_left_add_left]
  have hodd : Odd (2 * (N * l) + 1) := odd_two_mul_add_one _
  obtain ⟨z, hzI, hzK⟩ := zKill E Ω l D e (N * l) ρ hρ he hproc hlM _ hcop hodd
  have hφs : Function.Surjective ⇑((piQ ρ)⁻¹) := by
    intro y
    obtain ⟨b, hb⟩ := piQ_surjective ρ y⁻¹
    exact ⟨b, by simp [hb]⟩
  have hφ1 : ((piQ ρ)⁻¹) (-1) ≠ 1 := by
    simpa using hne
  obtain ⟨r0, hr0, hdet⟩ := detVal l _ (N * l) _ e _ hcop hφs hφ1 he (by omega) z hzI
  have hT : Nat.totient (N * l) ≠ 0 := (Nat.totient_pos.mpr (NeZero.pos _)).ne'
  obtain ⟨r1, hr1le, hr1dvd⟩ := nat_dvd_pow l (Nat.totient (N * l)) hT
  refine ⟨r0 + r1, ?_, ?_⟩
  · have hb := hC N l e hN hl2 he
    have hr1 : (r1 : ℝ) * Real.log l ≤ Real.log ((N : ℝ) * l) := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by positivity)
      exact_mod_cast hr1le.trans (Nat.totient_le _)
    rw [hcard] at hr0
    have hd : (1 : ℝ) ≤ Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
    have hB := Real.log_natCast_nonneg (bdX (N * l) (2 * (N * l) + 1) (e + 1))
    have hL : 0 ≤ Real.log ((N : ℝ) * l) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have : (2 : ℝ) ≤ l := by exact_mod_cast hl2
      nlinarith)
    have h1 := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℝ) ≤ Module.finrank ℚ E)
    have h2 := mul_nonneg (sub_nonneg.2 hd) hL
    push_cast
    nlinarith
  · intro x hx
    obtain ⟨hxS, hxE⟩ := Submodule.mem_inf.mp hx
    rw [Module.End.mem_eigenspace_iff] at hxE
    have hK := hzK x hxS
    have hcm : ((piQ ρ)⁻¹) (-1) = piQ ρ (-1) := by
      rw [MonoidHom.inv_apply, ← map_inv, inv_neg_one]
    have hc : (actRep D (e : ℤ) ρ (((piQ ρ)⁻¹) (-1))) (Nat.totient (N * l) • x)
        = (((-1) ^ (e + 1) : ℤ) : ℤ_[l]) • (Nat.totient (N * l) • x) := by
      rw [hcm, actRep_piQ, hconj, map_nsmul]
      change Nat.totient (N * l) • (cAct D (e : ℤ)) x = _
      rw [hxE, smul_comm]
      push_cast
      rfl
    have hcc : ((piQ ρ)⁻¹) (-1) * ((piQ ρ)⁻¹) (-1) = 1 := by
      rw [← map_mul]
      simp
    have hεε : ((-1) ^ (e + 1) : ℤ) * (-1) ^ (e + 1) = 1 := by
      rw [← mul_pow]
      simp
    have hkill := adjKill ℤ_[l] _ _ (actRep D (e : ℤ) ρ) _ _ hcc hφ1 hεε z _ hc hK
    obtain ⟨u, hu⟩ := hdet
    obtain ⟨v, hv⟩ := hr1dvd
    rw [pow_add, hu, hv]
    calc _ = (u * v) • (detR (((piQ ρ)⁻¹) (-1)) ((-1) ^ (e + 1)) z • (Nat.totient (N * l) • x)) := by
          rw [← Nat.cast_smul_eq_nsmul ℤ_[l], smul_smul, smul_smul]
          congr 1
          ring
      _ = 0 := by rw [hkill, smul_zero]
