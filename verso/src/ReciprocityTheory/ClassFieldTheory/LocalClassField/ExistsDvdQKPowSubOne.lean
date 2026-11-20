import Mathlib
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtD
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtE

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K}

/- English proof (translation)
Take `⟨k, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hn.ne'`. Conclude with `le_iSup (fun n : ℕ => Kn p K (n + 1)) k`.
-/
theorem Kn_le_Kur {n : ℕ} (hn : 0 < n) : Kn p K n ≤ MaximalUnramifiedExtension p K := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact le_iSup (fun n : ℕ => Kn p K (n + 1)) k

/- English proof (translation)
The claim follows from `(le_Kn p K 1).trans (Kn_le_Kur one_pos)`.
-/
theorem le_Kur : K ≤ MaximalUnramifiedExtension p K := (le_Kn p K 1).trans (Kn_le_Kur one_pos)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hdir : Directed (· ≤ ·) (fun n : ℕ => Kn p K (n + 1))`. Introduce `i j`. Use `⟨(i + 1) * (j + 1) - 1, ?_, ?_⟩` and prove the remaining obligations.

Establish `: (i + 1) * (j + 1) - 1 + 1 = (i + 1) * (j + 1)` using `Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))`. Express the relevant statement in the definitionally equal form `Kn p K (i + 1) ≤ Kn p K ((i + 1) * (j + 1) - 1 + 1)`. Rewrite using `[this]`. Conclude with `Kn_mono p K hK (Dvd.intro _ rfl)`. Establish `: (i + 1) * (j + 1) - 1 + 1 = (i + 1) * (j + 1)` using `Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))`.

Express the relevant statement in the definitionally equal form `Kn p K (j + 1) ≤ Kn p K ((i + 1) * (j + 1) - 1 + 1)`. Rewrite using `[this]`. Conclude with `Kn_mono p K hK (Dvd.intro_left _ rfl)`. Establish `h` using `IntermediateField.coe_iSup_of_directed hdir`. Establish `hx' : x ∈ ((⨆ n : ℕ, Kn p K (n + 1) : IntermediateField ℚ_[p] (PadicAlgCl p)) : Set (PadicAlgCl p))` using `hx`.

Rewrite `hx'` using `[h]`. Take `⟨k, hk⟩` from `Set.mem_iUnion.1 hx'`. Conclude with `⟨k + 1, Nat.succ_pos k, hk⟩`. Introduce and unpack `⟨n, hn, hx⟩`. Conclude with `Kn_le_Kur hn hx`.
-/
theorem mem_Kur_iff (hK : FiniteDimensional ℚ_[p] K) (x : PadicAlgCl p) :
    x ∈ MaximalUnramifiedExtension p K ↔ ∃ n, 0 < n ∧ x ∈ Kn p K n := by
  constructor
  · intro hx
    have hdir : Directed (· ≤ ·) (fun n : ℕ => Kn p K (n + 1)) := by
      intro i j
      refine ⟨(i + 1) * (j + 1) - 1, ?_, ?_⟩
      · have : (i + 1) * (j + 1) - 1 + 1 = (i + 1) * (j + 1) := Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))
        change Kn p K (i + 1) ≤ Kn p K ((i + 1) * (j + 1) - 1 + 1)
        rw [this]; exact Kn_mono p K hK (Dvd.intro _ rfl)
      · have : (i + 1) * (j + 1) - 1 + 1 = (i + 1) * (j + 1) := Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))
        change Kn p K (j + 1) ≤ Kn p K ((i + 1) * (j + 1) - 1 + 1)
        rw [this]; exact Kn_mono p K hK (Dvd.intro_left _ rfl)
    have h := IntermediateField.coe_iSup_of_directed hdir
    have hx' : x ∈ ((⨆ n : ℕ, Kn p K (n + 1) : IntermediateField ℚ_[p] (PadicAlgCl p)) : Set (PadicAlgCl p)) := hx
    rw [h] at hx'
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx'
    exact ⟨k + 1, Nat.succ_pos k, hk⟩
  · rintro ⟨n, hn, hx⟩
    exact Kn_le_Kur hn hx

/- English proof (translation)
Establish `hm0 : 0 < m` using `Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero p))`. Take `⟨f, hf, hq⟩` from `qK_eq_pow p K hK`. Establish `hcop : Nat.Coprime (qK p K) m`. Rewrite using `[hq]`. Conclude with `Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)`.

Use `⟨Nat.totient m, Nat.totient_pos.2 hm0, ?_⟩` and prove the remaining obligations. Establish `h1 : 1 ≤ qK p K ^ Nat.totient m` using `Nat.one_le_pow _ _ (by have := one_lt_qK p K hK; omega)`. Conclude with `(Nat.modEq_iff_dvd' h1).1 (Nat.ModEq.pow_totient hcop).symm`.
-/
theorem exists_dvd_qK_pow_sub_one (hK : FiniteDimensional ℚ_[p] K) {m : ℕ} (hm : ¬ p ∣ m) :
    ∃ n, 0 < n ∧ m ∣ qK p K ^ n - 1 := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero p))
  obtain ⟨f, hf, hq⟩ := qK_eq_pow p K hK
  have hcop : Nat.Coprime (qK p K) m := by
    rw [hq]
    exact Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
  refine ⟨Nat.totient m, Nat.totient_pos.2 hm0, ?_⟩
  have h1 : 1 ≤ qK p K ^ Nat.totient m := Nat.one_le_pow _ _ (by have := one_lt_qK p K hK; omega)
  exact (Nat.modEq_iff_dvd' h1).1 (Nat.ModEq.pow_totient hcop).symm

/- English proof (translation)
Take `⟨n, hn, d, hd⟩` from `exists_dvd_qK_pow_sub_one hK hm`. Conclude with `Kn_le_Kur hn (mem_Kn_of_pow p K (by rw [hd, pow_mul, hζ, one_pow]))`.
-/
theorem mem_Kur_of_pow (hK : FiniteDimensional ℚ_[p] K) {m : ℕ} (hm : ¬ p ∣ m) {ζ : PadicAlgCl p}
    (hζ : ζ ^ m = 1) : ζ ∈ MaximalUnramifiedExtension p K := by
  obtain ⟨n, hn, d, hd⟩ := exists_dvd_qK_pow_sub_one hK hm
  exact Kn_le_Kur hn (mem_Kn_of_pow p K (by rw [hd, pow_mul, hζ, one_pow]))

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `iSup_le fun n => UnramifiedExtensions.Kn_le K le_sup_left fun ζ hζ => ?_` and prove the remaining obligations. Conclude with `(le_sup_right : _ ≤ K ⊔ _) (IntermediateField.subset_adjoin _ _ ⟨_, UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK (Nat.succ_pos n), hζ⟩)`. Use `sup_le le_Kur (IntermediateField.adjoin_le_iff.2 ?_)` and prove the remaining obligations. Introduce and unpack `ζ ⟨m, hm, hζ⟩`.

Conclude with `mem_Kur_of_pow hK hm hζ`.
-/
theorem Kur_eq (hK : FiniteDimensional ℚ_[p] K) :
    MaximalUnramifiedExtension p K = K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ∃ m : ℕ, ¬ p ∣ m ∧ ζ ^ m = 1} := by
  apply le_antisymm
  · refine iSup_le fun n => UnramifiedExtensions.Kn_le K le_sup_left fun ζ hζ => ?_
    exact (le_sup_right : _ ≤ K ⊔ _) (IntermediateField.subset_adjoin _ _
      ⟨_, UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK (Nat.succ_pos n), hζ⟩)
  · refine sup_le le_Kur (IntermediateField.adjoin_le_iff.2 ?_)
    rintro ζ ⟨m, hm, hζ⟩
    exact mem_Kur_of_pow hK hm hζ

/- English proof (translation)
Rewrite using `[Kur_eq hK, Kur_eq hL, ← sup_assoc, sup_eq_left.2 h]`.
-/
theorem Kur_eq_sup (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    MaximalUnramifiedExtension p L = L ⊔ MaximalUnramifiedExtension p K := by
  rw [Kur_eq hK, Kur_eq hL, ← sup_assoc, sup_eq_left.2 h]

/- English proof (translation)
Rewrite using `[Kur_eq_sup L hK hL h]`. Conclude with `le_sup_right`.
-/
theorem Kur_le_Kur (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    MaximalUnramifiedExtension p K ≤ MaximalUnramifiedExtension p L := by
  rw [Kur_eq_sup L hK hL h]; exact le_sup_right

/- English proof (translation)
Establish `hfd : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {x})` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)`. Take `⟨ζ, -, hζ, h⟩` from `exists_teichmuller p _ hfd (IntermediateField.mem_adjoin_simple_self ℚ_[p] x) hx`. Use `⟨ζ, _, ?_, hζ, h⟩` and prove the remaining obligations. Simplify using `using UnramifiedExtensions.not_dvd_qK_pow_sub_one _ hfd (n := 1) one_pos`.
-/
theorem exists_teichmuller_bar (x : PadicAlgCl p) (hx : ‖x‖ = 1) :
    ∃ (ζ : PadicAlgCl p) (m : ℕ), ¬ p ∣ m ∧ ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 := by
  have hfd : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  obtain ⟨ζ, -, hζ, h⟩ := exists_teichmuller p _ hfd (IntermediateField.mem_adjoin_simple_self ℚ_[p] x) hx
  refine ⟨ζ, _, ?_, hζ, h⟩
  simpa using UnramifiedExtensions.not_dvd_qK_pow_sub_one _ hfd (n := 1) one_pos

/- English proof (translation)
Take `⟨n, hn, hxn⟩` from `(mem_Kur_iff hK x).1 hx`. Conclude with `UnramifiedExtensions.eqOn_Kn K (fun ζ hζ => h ζ _ (UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn) hζ) hxn`.
-/
theorem eqOn_Kur {σ τ : GK p K} (h : ∀ (ζ : PadicAlgCl p) (m : ℕ), ¬ p ∣ m → ζ ^ m = 1 → σ ζ = τ ζ)
    (hK : FiniteDimensional ℚ_[p] K) {x : PadicAlgCl p} (hx : x ∈ MaximalUnramifiedExtension p K) : σ x = τ x := by
  obtain ⟨n, hn, hxn⟩ := (mem_Kur_iff hK x).1 hx
  exact UnramifiedExtensions.eqOn_Kn K (fun ζ hζ => h ζ _ (UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn) hζ) hxn

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h ζ m hm hζ`. Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hm (dvd_zero p)`. Assume the negation of the conclusion as `hne`. Establish `h1 : (σ ζ) ^ m = 1` using `by rw [← map_pow, hζ, map_one]`.

Establish `h2 : (ζ ^ qK p K) ^ m = 1` using `by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]`. Establish `h3` using `norm_sub_eq_one_of_pow_eq_one p hm h1 h2 hne`. Conclude with `absurd h3 (ne_of_lt (h ζ (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le))`. Introduce `h x hx`. Establish `hq : qK p K ≠ 0` using `by have := one_lt_qK p K hK; omega`.

Establish `hσx : ‖σ x‖ ≤ 1` using `by rw [norm_GK]; exact hx`. Establish `hxq : ‖x ^ qK p K‖ ≤ 1` using `by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx`. Rewrite using `[← UnramifiedExtensions.red_eq_iff hσx hxq, ← UnramifiedExtensions.sigBar_red σ hx, UnramifiedExtensions.red_pow hx]`. Break down `lt_or_eq_of_le hx with hlt | heq` into its components or cases. Establish `h0 : UnramifiedExtensions.red x = 0`.

Rewrite using `[UnramifiedExtensions.red_of_le hx, UnramifiedExtensions.res_eq_zero_iff]`. Conclude with `hlt`. Rewrite using `[h0, map_zero, zero_pow hq]`. Take `⟨ζ, m, hm, hζ, hxζ⟩` from `exists_teichmuller_bar x heq`. Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hm (dvd_zero p)`.

Establish `hζ1` using `(UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le`. Rewrite using `[(UnramifiedExtensions.red_eq_iff hx hζ1).2 hxζ, UnramifiedExtensions.sigBar_red σ hζ1, h ζ m hm hζ, UnramifiedExtensions.red_pow hζ1]`.
-/
theorem isFrob_iff (hK : FiniteDimensional ℚ_[p] K) (σ : GK p K) :
    IsFrob p K σ ↔ ∀ (ζ : PadicAlgCl p) (m : ℕ), ¬ p ∣ m → ζ ^ m = 1 → σ ζ = ζ ^ qK p K := by
  constructor
  · intro h ζ m hm hζ
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
    by_contra hne
    have h1 : (σ ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
    have h2 : (ζ ^ qK p K) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    have h3 := norm_sub_eq_one_of_pow_eq_one p hm h1 h2 hne
    exact absurd h3 (ne_of_lt (h ζ (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le))
  · intro h x hx
    have hq : qK p K ≠ 0 := by have := one_lt_qK p K hK; omega
    have hσx : ‖σ x‖ ≤ 1 := by rw [norm_GK]; exact hx
    have hxq : ‖x ^ qK p K‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    rw [← UnramifiedExtensions.red_eq_iff hσx hxq, ← UnramifiedExtensions.sigBar_red σ hx, UnramifiedExtensions.red_pow hx]
    rcases lt_or_eq_of_le hx with hlt | heq
    · have h0 : UnramifiedExtensions.red x = 0 := by
        rw [UnramifiedExtensions.red_of_le hx, UnramifiedExtensions.res_eq_zero_iff]; exact hlt
      rw [h0, map_zero, zero_pow hq]
    · obtain ⟨ζ, m, hm, hζ, hxζ⟩ := exists_teichmuller_bar x heq
      have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
      have hζ1 := (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le
      rw [(UnramifiedExtensions.red_eq_iff hx hζ1).2 hxζ, UnramifiedExtensions.sigBar_red σ hζ1, h ζ m hm hζ, UnramifiedExtensions.red_pow hζ1]

/- English proof (translation)
Set `S : ℕ → Set (GK p K)` to `fun k => {σ | IsFrobOn p K (k + 1).factorial σ}`. Establish `hS : ∀ k, S k = ⋂ ζ : PadicAlgCl p, ⋂ _ : ζ ^ (qK p K ^ (k + 1).factorial - 1) = 1, {σ : GK p K | σ ζ = ζ ^ qK p K}`. Introduce `k`. Use extensionality with `σ`. Simplify using `only [S, Set.mem_ofPred_eq, Set.mem_iInter]`.

Conclude with `isFrobOn_iff p K hK (Nat.factorial_pos _) σ`. Establish `hcl : ∀ k, IsClosed (S k)`. Introduce `k`. Rewrite using `[hS]`. Conclude with `isClosed_iInter fun ζ => isClosed_iInter fun _ => ReciprocityTheory.Gal.isClosed_setOf_apply ζ (fun y => y = ζ ^ qK p K)`.

Establish `hne : ∀ k, (S k).Nonempty` using `fun k => exists_isFrobOn p K hK (Nat.factorial_pos _)`. Establish `hmono : ∀ k, S (k + 1) ⊆ S k` using `fun k σ hσ => IsFrobOn.of_dvd p K hK (Nat.factorial_dvd_factorial (Nat.le_succ _)) hσ`. Take `⟨σ, hσ⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono hne (hcl 0).isCompact hcl`. Use `⟨σ, (isFrob_iff hK σ).2 fun ζ m hm hζ => ?_⟩` and prove the remaining obligations. Take `⟨n, hn, d, hd⟩` from `exists_dvd_qK_pow_sub_one hK hm`.

Establish `h1 : IsFrobOn p K n σ`. Establish `h2 : IsFrobOn p K ((n - 1) + 1).factorial σ` using `Set.mem_iInter.1 hσ (n - 1)`. Use `IsFrobOn.of_dvd p K hK ?_ h2` and prove the remaining obligations. Rewrite using `[Nat.sub_add_cancel hn]`. Conclude with `Nat.dvd_factorial hn le_rfl`.

Conclude with `(isFrobOn_iff p K hK hn σ).1 h1 ζ (by rw [hd, pow_mul, hζ, one_pow])`.
-/
theorem exists_isFrob (hK : FiniteDimensional ℚ_[p] K) : ∃ σ : GK p K, IsFrob p K σ := by
  let S : ℕ → Set (GK p K) := fun k => {σ | IsFrobOn p K (k + 1).factorial σ}
  have hS : ∀ k, S k = ⋂ ζ : PadicAlgCl p, ⋂ _ : ζ ^ (qK p K ^ (k + 1).factorial - 1) = 1,
      {σ : GK p K | σ ζ = ζ ^ qK p K} := by
    intro k
    ext σ
    simp only [S, Set.mem_ofPred_eq, Set.mem_iInter]
    exact isFrobOn_iff p K hK (Nat.factorial_pos _) σ
  have hcl : ∀ k, IsClosed (S k) := by
    intro k
    rw [hS]
    exact isClosed_iInter fun ζ => isClosed_iInter fun _ =>
      ReciprocityTheory.Gal.isClosed_setOf_apply ζ (fun y => y = ζ ^ qK p K)
  have hne : ∀ k, (S k).Nonempty := fun k => exists_isFrobOn p K hK (Nat.factorial_pos _)
  have hmono : ∀ k, S (k + 1) ⊆ S k := fun k σ hσ =>
    IsFrobOn.of_dvd p K hK (Nat.factorial_dvd_factorial (Nat.le_succ _)) hσ
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono hne
    (hcl 0).isCompact hcl
  refine ⟨σ, (isFrob_iff hK σ).2 fun ζ m hm hζ => ?_⟩
  obtain ⟨n, hn, d, hd⟩ := exists_dvd_qK_pow_sub_one hK hm
  have h1 : IsFrobOn p K n σ := by
    have h2 : IsFrobOn p K ((n - 1) + 1).factorial σ := Set.mem_iInter.1 hσ (n - 1)
    refine IsFrobOn.of_dvd p K hK ?_ h2
    rw [Nat.sub_add_cancel hn]
    exact Nat.dvd_factorial hn le_rfl
  exact (isFrobOn_iff p K hK hn σ).1 h1 ζ (by rw [hd, pow_mul, hζ, one_pow])

/- English proof (translation)
The claim follows from `Classical.epsilon_spec (exists_isFrob hK)`.
-/
theorem isFrob_frobK (hK : FiniteDimensional ℚ_[p] K) : IsFrob p K (frobK p K) :=
  Classical.epsilon_spec (exists_isFrob hK)

/- English proof (translation)
Introduce `x _ hx` and use `h x hx`.
-/
theorem IsFrob.isFrobOn {σ : GK p K} (h : IsFrob p K σ) (n : ℕ) : IsFrobOn p K n σ :=
  fun x _ hx => h x hx

/- English proof (translation)
The claim follows from `eqOn_Kur (fun ζ m hm hζ => by rw [(isFrob_iff hK σ).1 hσ ζ m hm hζ, (isFrob_iff hK τ).1 hτ ζ m hm hζ]) hK hx`.
-/
theorem IsFrob.eqOn (hK : FiniteDimensional ℚ_[p] K) {σ τ : GK p K} (hσ : IsFrob p K σ) (hτ : IsFrob p K τ)
    {x : PadicAlgCl p} (hx : x ∈ MaximalUnramifiedExtension p K) : σ x = τ x :=
  eqOn_Kur (fun ζ m hm hζ => by rw [(isFrob_iff hK σ).1 hσ ζ m hm hζ, (isFrob_iff hK τ).1 hτ ζ m hm hζ]) hK hx

/- English proof (translation)
Rewrite using `[QuotientGroup.eq, mem_subG_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Use `congrArg σ (h x hx)` as an intermediate fact. Rewrite `this` using `[AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, mul_inv_cancel]`.

Conclude with `this.symm`. Introduce `h x hx`. Rewrite using `[AlgEquiv.mul_apply, ← h x hx, ← AlgEquiv.mul_apply, inv_mul_cancel]`. Both sides reduce to the same expression.
-/
theorem mk_eq_mk_iff {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ τ : GK p K) :
    (QuotientGroup.mk σ : GalLK p K M) = QuotientGroup.mk τ ↔ ∀ x ∈ M, σ x = τ x := by
  rw [QuotientGroup.eq, mem_subG_iff]
  constructor
  · intro h x hx
    have := congrArg σ (h x hx)
    rw [AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, mul_inv_cancel] at this
    exact this.symm
  · intro h x hx
    rw [AlgEquiv.mul_apply, ← h x hx, ← AlgEquiv.mul_apply, inv_mul_cancel]
    rfl

/- English proof (translation)
The claim follows from `(mk_eq_mk_iff σ (frobK p K)).2 fun _ hx => IsFrob.eqOn hK h (isFrob_frobK hK) hx`.
-/
theorem IsFrob.mk_eq (hK : FiniteDimensional ℚ_[p] K) {σ : GK p K} (h : IsFrob p K σ) :
    (QuotientGroup.mk σ : GalLK p K (MaximalUnramifiedExtension p K)) = frobLK p K (MaximalUnramifiedExtension p K) :=
  (mk_eq_mk_iff σ (frobK p K)).2 fun _ hx => IsFrob.eqOn hK h (isFrob_frobK hK) hx

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Break down `lt_or_eq_of_le hx with hlt | heq` into its components or cases. Conclude with `lt_of_le_of_lt (UnramifiedExtensions.norm_sub_le_max' _ _) (max_lt (by rw [norm_GK]; exact hlt) hlt)`. Take `⟨ζ, m, hm, hζ, hxζ⟩` from `exists_teichmuller_bar x heq`.

Establish `h1 : σ ζ = ζ` using `h ζ (mem_Kur_of_pow hK hm hζ)`. Establish `h2 : σ x - x = σ (x - ζ) - (x - ζ)` using `by rw [map_sub, h1]; ring`. Rewrite using `[h2]`. Conclude with `lt_of_le_of_lt (UnramifiedExtensions.norm_sub_le_max' _ _) (max_lt (by rw [norm_GK]; exact hxζ) hxζ)`. Introduce `h x hx`.

Use `eqOn_Kur (σ := σ) (τ := 1) (fun ζ m hm hζ => ?_) hK hx` and prove the remaining obligations. Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hm (dvd_zero p)`. Assume the negation of the conclusion as `hne`. Establish `h1 : (σ ζ) ^ m = 1` using `by rw [← map_pow, hζ, map_one]`. Establish `h3` using `norm_sub_eq_one_of_pow_eq_one p hm h1 hζ hne`.

Conclude with `absurd h3 (ne_of_lt (h ζ (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le))`.
-/
theorem mem_subG_Kur_iff (hK : FiniteDimensional ℚ_[p] K) (σ : GK p K) :
    σ ∈ subG p K (MaximalUnramifiedExtension p K) ↔ ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by
  constructor
  · intro h x hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact lt_of_le_of_lt (UnramifiedExtensions.norm_sub_le_max' _ _) (max_lt (by rw [norm_GK]; exact hlt) hlt)
    · obtain ⟨ζ, m, hm, hζ, hxζ⟩ := exists_teichmuller_bar x heq
      have h1 : σ ζ = ζ := h ζ (mem_Kur_of_pow hK hm hζ)
      have h2 : σ x - x = σ (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
      rw [h2]
      exact lt_of_le_of_lt (UnramifiedExtensions.norm_sub_le_max' _ _) (max_lt (by rw [norm_GK]; exact hxζ) hxζ)
  · intro h x hx
    refine eqOn_Kur (σ := σ) (τ := 1) (fun ζ m hm hζ => ?_) hK hx
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
    by_contra hne
    have h1 : (σ ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
    have h3 := norm_sub_eq_one_of_pow_eq_one p hm h1 hζ hne
    exact absurd h3 (ne_of_lt (h ζ (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le))

/- English proof (translation)
Establish `h : inertiaSet p K = (subG p K (MaximalUnramifiedExtension p K) : Set (GK p K))`. Use extensionality with `σ`. Conclude with `(mem_subG_Kur_iff hK σ).symm`. Rewrite using `[inertiaK, h, Subgroup.closure_eq]`.
-/
theorem subG_Kur_eq_inertiaK (hK : FiniteDimensional ℚ_[p] K) : subG p K (MaximalUnramifiedExtension p K) = inertiaK p K := by
  have h : inertiaSet p K = (subG p K (MaximalUnramifiedExtension p K) : Set (GK p K)) := by
    ext σ
    exact (mem_subG_Kur_iff hK σ).symm
  rw [inertiaK, h, Subgroup.closure_eq]

/- English proof (translation)
Establish `h1` using `finrank_eq_degLK_mul (le_Kn p K n) (finiteDimensional_Kn p K hK hn)`. Rewrite `h1` using `[finrank_Kn p K hK hn]`. Establish `hd : 0 < Module.finrank ℚ_[p] K` using `Module.finrank_pos`. Conclude with `(Nat.eq_of_mul_eq_mul_right hd h1).symm`.
-/
theorem degLK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : degLK p K (Kn p K n) = n := by
  have h1 := finrank_eq_degLK_mul (le_Kn p K n) (finiteDimensional_Kn p K hK hn)
  rw [finrank_Kn p K hK hn] at h1
  have hd : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  exact (Nat.eq_of_mul_eq_mul_right hd h1).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frobLK_pow (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [(subG p K M).Normal] (i : ℕ) :
    frobLK p K M ^ i = QuotientGroup.mk (frobK p K ^ i) := rfl

/- English proof (translation)
Take `⟨σ, rfl⟩` from `QuotientGroup.mk_surjective g`. Take `⟨i, -, hi⟩` from `IsFrobOn.exists_pow p K hK hn ((isFrob_frobK hK).isFrobOn n) σ`. Use `⟨i, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `frobLK p K (Kn p K n) ^ (i : ℤ) = _`. Rewrite using `[zpow_natCast, frobLK_pow]`.

Conclude with `((mk_eq_mk_iff _ _).2 hi).symm`.
-/
theorem mem_zpowers_frobLK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n)
    (g : GalLK p K (Kn p K n)) : g ∈ Subgroup.zpowers (frobLK p K (Kn p K n)) := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨i, -, hi⟩ := IsFrobOn.exists_pow p K hK hn ((isFrob_frobK hK).isFrobOn n) σ
  refine ⟨i, ?_⟩
  change frobLK p K (Kn p K n) ^ (i : ℤ) = _
  rw [zpow_natCast, frobLK_pow]
  exact ((mk_eq_mk_iff _ _).2 hi).symm

/- English proof (translation)
Rewrite using `[frobLK_pow, ← IsFrobOn.pow_fixes_iff p K hK hn ((isFrob_frobK hK).isFrobOn n) i, ← QuotientGroup.mk_one, mk_eq_mk_iff]`. Both sides reduce to the same expression.
-/
theorem frobLK_Kn_pow_eq_one_iff (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    frobLK p K (Kn p K n) ^ i = 1 ↔ n ∣ i := by
  rw [frobLK_pow, ← IsFrobOn.pow_fixes_iff p K hK hn ((isFrob_frobK hK).isFrobOn n) i,
    ← QuotientGroup.mk_one, mk_eq_mk_iff]
  rfl

/- English proof (translation)
Apply `Nat.dvd_antisymm` to reduce the goal to its premises. Conclude with `orderOf_dvd_of_pow_eq_one ((frobLK_Kn_pow_eq_one_iff hK hn n).2 dvd_rfl)`. Conclude with `(frobLK_Kn_pow_eq_one_iff hK hn _).1 (pow_orderOf_eq_one _)`.
-/
theorem orderOf_frobLK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    orderOf (frobLK p K (Kn p K n)) = n := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((frobLK_Kn_pow_eq_one_iff hK hn n).2 dvd_rfl)
  · exact (frobLK_Kn_pow_eq_one_iff hK hn _).1 (pow_orderOf_eq_one _)

/- English proof (translation)
Take `⟨n, hn, hxn⟩` from `(mem_Kur_iff hK x).1 hx`. Apply `UnramifiedExtensions.mem_of_fixed K` to reduce the goal to its premises. Introduce `σ`. Take `⟨i, -, hi⟩` from `IsFrobOn.exists_pow p K hK hn ((isFrob_frobK hK).isFrobOn n) σ`. Rewrite using `[hi x hxn]`.

Use `clear hi`. Proceed by induction on `i with`. Consider the case `zero => rfl`. Consider the case `succ k ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]`.
-/
theorem mem_of_frobK_fixed (hK : FiniteDimensional ℚ_[p] K) {x : PadicAlgCl p} (hx : x ∈ MaximalUnramifiedExtension p K)
    (h : frobK p K x = x) : x ∈ K := by
  obtain ⟨n, hn, hxn⟩ := (mem_Kur_iff hK x).1 hx
  apply UnramifiedExtensions.mem_of_fixed K
  intro σ
  obtain ⟨i, -, hi⟩ := IsFrobOn.exists_pow p K hK hn ((isFrob_frobK hK).isFrobOn n) σ
  rw [hi x hxn]
  clear hi
  induction i with
  | zero => rfl
  | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `set C : Subgroup (GalLK p K (MaximalUnramifiedExtension p K)) := (Subgroup.zpowers (frobLK p K (MaximalUnramifiedExtension p K))).topologicalClosure with hC`. Establish `hCcl : IsClosed (C : Set (GalLK p K (MaximalUnramifiedExtension p K)))` using `Subgroup.isClosed_topologicalClosure _`. Use `set H : Subgroup (GK p K) := C.comap (QuotientGroup.mk' (subG p K (MaximalUnramifiedExtension p K))) with hH`. Establish `hHcl : IsClosed (H : Set (GK p K))` using `hCcl.preimage continuous_quot_mk`.

Take `⟨M, hKM, hM⟩` from `exists_subG_eq H hHcl`. Establish `hNH : subG p K (MaximalUnramifiedExtension p K) ≤ subG p K M`. Rewrite using `[hM]`. Introduce `σ hσ`. Express the relevant statement in the definitionally equal form `(QuotientGroup.mk σ : GalLK p K (MaximalUnramifiedExtension p K)) ∈ C`.

Rewrite using `[(QuotientGroup.eq_one_iff σ).2 hσ]`. Conclude with `C.one_mem`. Establish `hMur : M ≤ MaximalUnramifiedExtension p K`. Use `(subG_le_iff hKM).1 hNH` as an intermediate fact. Rewrite `this` using `[sup_eq_right.2 le_Kur]`. Then use the resulting hypothesis.

Establish `hfr : frobK p K ∈ subG p K M`. Rewrite using `[hM]`. Express the relevant statement in the definitionally equal form `frobLK p K (MaximalUnramifiedExtension p K) ∈ C`. Conclude with `Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)`. Establish `hMK : M ≤ K` using `fun x hx => mem_of_frobK_fixed hK (hMur hx) (hfr x hx)`.

Establish `htop : H = ⊤`. Rewrite using `[← hM, eq_top_iff]`. Introduce `σ _ x hx`. Conclude with `σ.commutes ⟨x, hMK hx⟩`. Establish `hCtop : C = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `g _`. Take `⟨σ, rfl⟩` from `QuotientGroup.mk_surjective g`. Establish `: σ ∈ H` using `by rw [htop]; trivial`. Conclude with `this`.

Rewrite using `[dense_iff_closure_eq]`. Establish `h1 : closure (Subgroup.zpowers (frobLK p K (MaximalUnramifiedExtension p K)) : Set (GalLK p K (MaximalUnramifiedExtension p K))) = (C : Set (GalLK p K (MaximalUnramifiedExtension p K)))` using `rfl`. Rewrite using `[h1, hCtop]`. Both sides reduce to the same expression. Introduce `k hk`.

Use `⟨(subG p K (Kn p K k)).map (QuotientGroup.mk' (subG p K (MaximalUnramifiedExtension p K))), ?_, ?_⟩` and prove the remaining obligations. Conclude with `QuotientGroup.isOpenMap_coe _ (isOpen_subG (finiteDimensional_Kn p K hK hk))`. Rewrite using `[Subgroup.index_map, QuotientGroup.ker_mk', sup_eq_left.2 (subG_anti (Kn_le_Kur hk)), MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), Subgroup.index_top, mul_one]`. Conclude with `degLK_Kn hK hk`.
-/
theorem isZHat_GalKur (hK : FiniteDimensional ℚ_[p] K) :
    IsZHat (GalLK p K (MaximalUnramifiedExtension p K)) (frobLK p K (MaximalUnramifiedExtension p K)) := by
  constructor
  · set C : Subgroup (GalLK p K (MaximalUnramifiedExtension p K)) :=
      (Subgroup.zpowers (frobLK p K (MaximalUnramifiedExtension p K))).topologicalClosure with hC
    have hCcl : IsClosed (C : Set (GalLK p K (MaximalUnramifiedExtension p K))) := Subgroup.isClosed_topologicalClosure _
    set H : Subgroup (GK p K) := C.comap (QuotientGroup.mk' (subG p K (MaximalUnramifiedExtension p K))) with hH
    have hHcl : IsClosed (H : Set (GK p K)) := hCcl.preimage continuous_quot_mk
    obtain ⟨M, hKM, hM⟩ := exists_subG_eq H hHcl
    have hNH : subG p K (MaximalUnramifiedExtension p K) ≤ subG p K M := by
      rw [hM]
      intro σ hσ
      change (QuotientGroup.mk σ : GalLK p K (MaximalUnramifiedExtension p K)) ∈ C
      rw [(QuotientGroup.eq_one_iff σ).2 hσ]
      exact C.one_mem
    have hMur : M ≤ MaximalUnramifiedExtension p K := by
      have := (subG_le_iff hKM).1 hNH
      rwa [sup_eq_right.2 le_Kur] at this
    have hfr : frobK p K ∈ subG p K M := by
      rw [hM]
      change frobLK p K (MaximalUnramifiedExtension p K) ∈ C
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)
    have hMK : M ≤ K := fun x hx => mem_of_frobK_fixed hK (hMur hx) (hfr x hx)
    have htop : H = ⊤ := by
      rw [← hM, eq_top_iff]
      intro σ _ x hx
      exact σ.commutes ⟨x, hMK hx⟩
    have hCtop : C = ⊤ := by
      rw [eq_top_iff]
      intro g _
      obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
      have : σ ∈ H := by rw [htop]; trivial
      exact this
    rw [dense_iff_closure_eq]
    have h1 : closure (Subgroup.zpowers (frobLK p K (MaximalUnramifiedExtension p K)) : Set (GalLK p K (MaximalUnramifiedExtension p K))) =
        (C : Set (GalLK p K (MaximalUnramifiedExtension p K))) := rfl
    rw [h1, hCtop]
    rfl
  · intro k hk
    refine ⟨(subG p K (Kn p K k)).map (QuotientGroup.mk' (subG p K (MaximalUnramifiedExtension p K))), ?_, ?_⟩
    · exact QuotientGroup.isOpenMap_coe _ (isOpen_subG (finiteDimensional_Kn p K hK hk))
    · rw [Subgroup.index_map, QuotientGroup.ker_mk', sup_eq_left.2 (subG_anti (Kn_le_Kur hk)),
        MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), Subgroup.index_top, mul_one]
      exact degLK_Kn hK hk

/- English proof (translation)
Set `b` to `Module.finBasis ℚ_[p] M`. Establish `h1 : ∀ i, ∃ n, 0 < n ∧ (b i : PadicAlgCl p) ∈ Kn p K n` using `fun i => (mem_Kur_iff hK _).1 (h (b i).2)`. Use `choose N hN hb using h1`. Use `⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : PadicAlgCl p)`.

Use `congrArg M.val (b.sum_repr ⟨x, hx⟩)` as an intermediate fact. Rewrite `this` using `[map_sum]`. Conclude with `this.symm`. Rewrite using `[hx']`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations.

Conclude with `(Kn p K (∏ i, N i)).smul_mem (Kn_mono p K hK (Finset.dvd_prod_of_mem N (Finset.mem_univ i)) (hb i))`.
-/
theorem exists_le_Kn_of_le_Kur (hK : FiniteDimensional ℚ_[p] K) {M : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hM : FiniteDimensional ℚ_[p] M) (h : M ≤ MaximalUnramifiedExtension p K) : ∃ n, 0 < n ∧ M ≤ Kn p K n := by
  let b := Module.finBasis ℚ_[p] M
  have h1 : ∀ i, ∃ n, 0 < n ∧ (b i : PadicAlgCl p) ∈ Kn p K n := fun i => (mem_Kur_iff hK _).1 (h (b i).2)
  choose N hN hb using h1
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun x hx => ?_⟩
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : PadicAlgCl p) := by
    have := congrArg M.val (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at this
    exact this.symm
  rw [hx']
  refine sum_mem fun i _ => ?_
  exact (Kn p K (∏ i, N i)).smul_mem (Kn_mono p K hK (Finset.dvd_prod_of_mem N (Finset.mem_univ i)) (hb i))

/- English proof (translation)
Take `⟨M, hKM, hM, rfl⟩` from `exists_subG_eq_of_isOpen hK U hU`. Establish `hMur : M ≤ MaximalUnramifiedExtension p K`. Use `(subG_le_iff hKM).1 h` as an intermediate fact. Rewrite `this` using `[sup_eq_right.2 le_Kur]`. Then use the resulting hypothesis. Take `⟨N, hN, hMN⟩` from `exists_le_Kn_of_le_Kur hK hM hMur`.

Use `⟨degLK p K M, degLK_pos hM, ?_⟩` and prove the remaining obligations. Rewrite using `[← eq_Kn_of_norm p K hK hKM (degLK_pos hM) (finrank_eq_degLK_mul hKM hM) (fun x hx => norm_Kn p K hK hN (hMN hx))]`.
-/
theorem exists_Kn_of_isOpen (hK : FiniteDimensional ℚ_[p] K) (U : Subgroup (GK p K))
    (hU : IsOpen (U : Set (GK p K))) (h : subG p K (MaximalUnramifiedExtension p K) ≤ U) :
    ∃ n, 0 < n ∧ U = subG p K (Kn p K n) := by
  obtain ⟨M, hKM, hM, rfl⟩ := exists_subG_eq_of_isOpen hK U hU
  have hMur : M ≤ MaximalUnramifiedExtension p K := by
    have := (subG_le_iff hKM).1 h
    rwa [sup_eq_right.2 le_Kur] at this
  obtain ⟨N, hN, hMN⟩ := exists_le_Kn_of_le_Kur hK hM hMur
  refine ⟨degLK p K M, degLK_pos hM, ?_⟩
  rw [← eq_Kn_of_norm p K hK hKM (degLK_pos hM) (finrank_eq_degLK_mul hKM hM)
    (fun x hx => norm_Kn p K hK hN (hMN hx))]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ', AlgEquiv.mul_apply, ih, map_pow, (isFrob_iff hK σ).1 h ζ m hm hζ, ← pow_mul, ← pow_succ']`.
-/
theorem IsFrob.pow_apply (hK : FiniteDimensional ℚ_[p] K) {σ : GK p K} (h : IsFrob p K σ) {m : ℕ}
    (hm : ¬ p ∣ m) (i : ℕ) {ζ : PadicAlgCl p} (hζ : ζ ^ m = 1) : (σ ^ i) ζ = ζ ^ (qK p K ^ i) := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, (isFrob_iff hK σ).1 h ζ m hm hζ, ← pow_mul, ← pow_succ']

/- English proof (translation)
Rewrite using `[frobLK_pow, mk_eq_mk_iff]`. Introduce `x hx`. Use `eqOn_Kur (fun ζ m hm hζ => ?_) hK hx` and prove the remaining obligations. Rewrite using `[resGK_apply, (isFrob_iff hL _).1 (isFrob_frobK hL) ζ m hm hζ, hf, IsFrob.pow_apply hK (isFrob_frobK hK) hm f hζ]`.
-/
theorem resGK_frobK (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) {f : ℕ}
    (hf : qK p L = qK p K ^ f) :
    (QuotientGroup.mk (resGK h (frobK p L)) : GalLK p K (MaximalUnramifiedExtension p K)) = frobLK p K (MaximalUnramifiedExtension p K) ^ f := by
  rw [frobLK_pow, mk_eq_mk_iff]
  intro x hx
  refine eqOn_Kur (fun ζ m hm hζ => ?_) hK hx
  rw [resGK_apply, (isFrob_iff hL _).1 (isFrob_frobK hL) ζ m hm hζ, hf,
    IsFrob.pow_apply hK (isFrob_frobK hK) hm f hζ]

end ReciprocityTheory.DiscreteGroups.LocalClassField
