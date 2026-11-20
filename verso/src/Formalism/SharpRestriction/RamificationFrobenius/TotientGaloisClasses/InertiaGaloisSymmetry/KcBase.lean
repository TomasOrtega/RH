import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.DecompTypeI
import Formalism.FrobeniusOrbits.HostCorollaries

open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

variable {φ : Frame} (H : HostRaw φ)

/- English proof (translation)
Introduce `h`. Establish `h1` using `H.sqd_sq`. Rewrite `h1` using `[h]`. Establish `hd : (H.d : H.E) = 0` using `by linear_combination h1`. Establish `hd0 : H.d = 0` using `by exact_mod_cast hd`.

Establish `hc` using `H.QS_coprime`. Rewrite `hc` using `[hd0, mul_zero, Nat.coprime_zero_right]`. Establish `ht` using `H.tower_dvd`. Rewrite `ht` using `[hc]`. Establish `h2 : 2 ^ (φ.e + 2) ≤ 1` using `Nat.le_of_dvd one_pos ht`.

Establish `h3 : 2 ^ 1 ≤ 2 ^ (φ.e + 2)` using `Nat.pow_le_pow_right (by norm_num) (by omega)`. Use linear arithmetic over natural numbers and integers.
-/
theorem kc_sqd_ne_zero : H.sqd ≠ 0 := by
  intro h
  have h1 := H.sqd_sq
  rw [h] at h1
  have hd : (H.d : H.E) = 0 := by linear_combination h1
  have hd0 : H.d = 0 := by exact_mod_cast hd
  have hc := H.QS_coprime
  rw [hd0, mul_zero, Nat.coprime_zero_right] at hc
  have ht := H.tower_dvd
  rw [hc] at ht
  have h2 : 2 ^ (φ.e + 2) ≤ 1 := Nat.le_of_dvd one_pos ht
  have h3 : 2 ^ 1 ≤ 2 ^ (φ.e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/- English proof (translation)
Rewrite using `[Frame.Psi, MonoidHom.mem_ker, H.gal_sqd]`. Simplify using `only [Frame.chD, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd]`. Apply the tactic sequence `rcases Int.units_eq_one_or ((H.gal σ).1.2) with h | h <;> rw [h]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Introduce `h1`. Conclude with `absurd h1 (by decide)`. Introduce `h1`. It suffices to derive a contradiction. Establish `h2 : (2 : H.E) * H.sqd = 0`.

Move the coercions through the operations in `at h1`. Take the linear combination `-h1`. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases. Evaluate the numerical expressions using `at h3`. Conclude with `kc_sqd_ne_zero H h3`.
-/
theorem kc_mem_Psi_iff (σ : H.E ≃ₐ[ℚ] H.E) : H.gal σ ∈ φ.Psi ↔ σ H.sqd = H.sqd := by
  rw [Frame.Psi, MonoidHom.mem_ker, H.gal_sqd]
  simp only [Frame.chD, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd]
  rcases Int.units_eq_one_or ((H.gal σ).1.2) with h | h <;> rw [h]
  · simp
  · constructor
    · intro h1
      exact absurd h1 (by decide)
    · intro h1
      exfalso
      have h2 : (2 : H.E) * H.sqd = 0 := by
        push_cast at h1
        linear_combination -h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · norm_num at h3
      · exact kc_sqd_ne_zero H h3

/- English proof (translation)
Unfold `HostRaw.conj`. Conclude with `H.gal.apply_symm_apply _`.
-/
theorem kc_gal_conj : H.gal H.conj = φ.cc := by
  unfold HostRaw.conj
  exact H.gal.apply_symm_apply _

/- English proof (translation)
Unfold `HostRaw.K`. Conclude with `IntermediateField.mem_adjoin_simple_self ℚ H.sqd`.
-/
theorem kc_sqd_mem : H.sqd ∈ H.K := by
  unfold HostRaw.K
  exact IntermediateField.mem_adjoin_simple_self ℚ H.sqd

/- English proof (translation)
Rewrite using `[kc_mem_Psi_iff]`. Conclude with `σ.commutes ⟨H.sqd, kc_sqd_mem H⟩`.
-/
theorem kc_restrict_mem_Psi (σ : H.E ≃ₐ[H.K] H.E) : H.gal (σ.restrictScalars ℚ) ∈ φ.Psi := by
  rw [kc_mem_Psi_iff]
  exact σ.commutes ⟨H.sqd, kc_sqd_mem H⟩

/- English proof (translation)
Establish `hs : H.sqd ∈ IntermediateField.fixedField (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd)` using `(IntermediateField.mem_fixedField_iff _ _).mpr fun f hf => hf`. Establish `hle : H.K ≤ IntermediateField.fixedField (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd)`. Unfold `HostRaw.K`. Conclude with `IntermediateField.adjoin_simple_le_iff.mpr hs`. Establish `hx` using `hle x.2`.

Rewrite `hx` using `[IntermediateField.mem_fixedField_iff]`. Conclude with `hx σ ((kc_mem_Psi_iff H σ).mp hσ)`.
-/
theorem kc_fixK (σ : H.E ≃ₐ[ℚ] H.E) (hσ : H.gal σ ∈ φ.Psi) (x : H.K) : σ (x : H.E) = x := by
  have hs : H.sqd ∈ IntermediateField.fixedField (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd) :=
    (IntermediateField.mem_fixedField_iff _ _).mpr fun f hf => hf
  have hle : H.K ≤ IntermediateField.fixedField (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd) := by
    unfold HostRaw.K
    exact IntermediateField.adjoin_simple_le_iff.mpr hs
  have hx := hle x.2
  rw [IntermediateField.mem_fixedField_iff] at hx
  exact hx σ ((kc_mem_Psi_iff H σ).mp hσ)

/- English proof (translation)
Simplify using `only [Frame.Psi, MonoidHom.mem_ker, Frame.chD, Frame.cc, c0, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd]`. Evaluate the decidable proposition.
-/
theorem kc_cc_not_mem : φ.cc ∉ φ.Psi := by
  simp only [Frame.Psi, MonoidHom.mem_ker, Frame.chD, Frame.cc, c0, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst, MonoidHom.coe_snd]
  decide

/- English proof (translation)
Simplify using `only [Frame.Psi, MonoidHom.mem_ker, Frame.chD, Frame.iod, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd]`. Evaluate the decidable proposition.
-/
theorem kc_iod_not_mem : φ.iod ∉ φ.Psi := by
  simp only [Frame.Psi, MonoidHom.mem_ker, Frame.chD, Frame.iod, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst, MonoidHom.coe_snd]
  decide

/- English proof (translation)
Establish `hne : span {(p : ℤ)} ≠ ⊥` using `by simp [hp.ne_zero]`. Conclude with `Ideal.ne_bot_of_liesOver_of_ne_bot hne P`.
-/
theorem kc_ne_bot {M : Type} [Field M] [NumberField M] (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 M))
    [P.LiesOver (span {(p : ℤ)})] : P ≠ ⊥ := by
  have hne : span {(p : ℤ)} ≠ ⊥ := by simp [hp.ne_zero]
  exact Ideal.ne_bot_of_liesOver_of_ne_bot hne P

/- English proof (translation)
The claim follows from `(dvd_pow_self 2 (by omega)).trans H.tower_dvd`.
-/
theorem kc_two_dvd : 2 ∣ H.QS := (dvd_pow_self 2 (by omega)).trans H.tower_dvd

/- English proof (translation)
Rewrite using `[MulAction.mem_stabilizer_iff]`. Use extensionality with `x`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Establish `h1` using `h (g⁻¹ • x)`. Rewrite `h1` using `[smul_inv_smul]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Simplify using `using P.add_mem h1 hx`. Introduce `hx`. Simplify using `using P.sub_mem hx h1`.
-/
theorem kc_stab_of_inertia {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] (g : G) (P : Ideal S)
    (h : ∀ x : S, g • x - x ∈ P) : g ∈ MulAction.stabilizer G P := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have h1 := h (g⁻¹ • x)
  rw [smul_inv_smul] at h1
  constructor
  · intro hx
    simpa using P.add_mem h1 hx
  · intro hx
    simpa using P.sub_mem hx h1

/- English proof (translation)
Introduce `p hp` and use `SplitK.clause (L := H.E) (b := H.sqd) H.hyp.2.1 (by have := H.hyp.2.2.2.1; omega) H.sqd_sq p hp`.
-/
theorem splitK : ∀ p : ℕ, p.Prime →
    ((primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2 ↔ (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1))) :=
  fun p hp => SplitK.clause (L := H.E) (b := H.sqd) H.hyp.2.1 (by have := H.hyp.2.2.2.1; omega) H.sqd_sq p hp

variable (C : HostCore H)
include C

/- English proof (translation)
Introduce `p hpf P _ _`. Establish `hp : p.Prime` using `hpf.out`. Establish `hred : (∀ σ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P → (H.gal (σ * τ) ∈ φ.Psi ↔ H.gal σ ∈ φ.Psi)) ↔ ∀ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P → H.gal τ ∈ φ.Psi`. Prove the components needed by the constructor for the conclusion. Introduce `h τ hτ`.

Use `h 1 τ hτ` as an intermediate fact. Rewrite `this` using `[one_mul, map_one]`. Conclude with `this.mpr (one_mem _)`. Introduce `h σ τ hτ`. Rewrite using `[map_mul]`.

Conclude with `Subgroup.mul_mem_cancel_right _ (h τ hτ)`. Rewrite using `[hred, splitK H p hp]`. Distinguish the cases in `h1 : p ∣ H.QS * H.q`. Use `iff_of_true (fun τ hτ => C.decomp_typeI p hp h1 P τ hτ) ?_` and prove the remaining obligations. Distinguish the cases in `h2 : p = 2`.

Conclude with `Or.inl h2`. Use `Or.inr ⟨h2, ?_⟩` and prove the remaining obligations. Break down `hp.dvd_mul.mp h1 with h3 | h3` into its components or cases. Conclude with `H.QS_split p hp h2 h3`. Rewrite using `[(Nat.prime_dvd_prime_iff_eq hp H.hyp.1).mp h3]`.

Conclude with `H.hyp.2.2.2.2`. Establish `hp2 : p ≠ 2`. Introduce and unpack `rfl`. Conclude with `h1 ((kc_two_dvd H).mul_right _)`. Distinguish the cases in `hpd : p = H.d`.

Substitute `hpd` using the available equality. Use `iff_of_false (fun h => ?_) ?_` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `H.gal.surjective φ.iod`. Establish `h3` using `h σ (kc_stab_of_inertia σ P ((C.inertia_d P σ).mpr (Or.inr hσ)))`. Rewrite `h3` using `[hσ]`.

Conclude with `kc_iod_not_mem h3`. Introduce and unpack `(h | ⟨-, h⟩)`. Conclude with `hp2 h`. Establish `: NeZero H.d` using `⟨hp.ne_zero⟩`. Establish `h0 : jacobiSym (-(H.d : ℤ)) H.d = 0` using `jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa using hp.ne_one)`.

Use linear arithmetic over natural numbers and integers. Establish `hN : ¬ p ∣ H.condN` using `fun h => by`. Break down `hp.dvd_mul.mp h with h3 | h3` into its components or cases. Conclude with `h1 h3`. Conclude with `hpd ((Nat.prime_dvd_prime_iff_eq hp H.hyp.2.1).mp h3)`.

Take `⟨⟨F, hF⟩, -, f3, f4⟩` from `C.frob p hN P`. Establish `hj` using `(f3 F hF).2.1`. Establish `hFP : H.gal F ∈ φ.Psi ↔ (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1))`. Rewrite using `[Frame.mem_Psi_iff, ← hj, or_iff_right hp2, and_iff_right hp2]`. Conclude with `(Units.val_eq_one).symm`.

Rewrite using `[← hFP]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `h F hF.mem_stabilizer`. Introduce `hFm τ hτ`.

Take `⟨k, ρ, hρ, rfl⟩` from `Decomp.stab_eq_inertia_mul p P F τ hF hτ`. Rewrite using `[(f4 ρ).mp hρ, one_mul, map_pow]`. Conclude with `Subgroup.pow_mem _ hFm k`.
-/
theorem ordinary : ∀ (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
    (∀ σ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P → (H.gal (σ * τ) ∈ φ.Psi ↔ H.gal σ ∈ φ.Psi)) ↔
      (primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2 := by
  intro p hpf P _ _
  have hp : p.Prime := hpf.out
  have hred : (∀ σ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P →
      (H.gal (σ * τ) ∈ φ.Psi ↔ H.gal σ ∈ φ.Psi)) ↔
      ∀ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P → H.gal τ ∈ φ.Psi := by
    constructor
    · intro h τ hτ
      have := h 1 τ hτ
      rw [one_mul, map_one] at this
      exact this.mpr (one_mem _)
    · intro h σ τ hτ
      rw [map_mul]
      exact Subgroup.mul_mem_cancel_right _ (h τ hτ)
  rw [hred, splitK H p hp]
  by_cases h1 : p ∣ H.QS * H.q
  · refine iff_of_true (fun τ hτ => C.decomp_typeI p hp h1 P τ hτ) ?_
    by_cases h2 : p = 2
    · exact Or.inl h2
    · refine Or.inr ⟨h2, ?_⟩
      rcases hp.dvd_mul.mp h1 with h3 | h3
      · exact H.QS_split p hp h2 h3
      · rw [(Nat.prime_dvd_prime_iff_eq hp H.hyp.1).mp h3]
        exact H.hyp.2.2.2.2
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h1 ((kc_two_dvd H).mul_right _)
  by_cases hpd : p = H.d
  · subst hpd
    refine iff_of_false (fun h => ?_) ?_
    · obtain ⟨σ, hσ⟩ := H.gal.surjective φ.iod
      have h3 := h σ (kc_stab_of_inertia σ P ((C.inertia_d P σ).mpr (Or.inr hσ)))
      rw [hσ] at h3
      exact kc_iod_not_mem h3
    · rintro (h | ⟨-, h⟩)
      · exact hp2 h
      · have : NeZero H.d := ⟨hp.ne_zero⟩
        have h0 : jacobiSym (-(H.d : ℤ)) H.d = 0 :=
          jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa using hp.ne_one)
        omega
  · have hN : ¬ p ∣ H.condN := fun h => by
      rcases hp.dvd_mul.mp h with h3 | h3
      · exact h1 h3
      · exact hpd ((Nat.prime_dvd_prime_iff_eq hp H.hyp.2.1).mp h3)
    obtain ⟨⟨F, hF⟩, -, f3, f4⟩ := C.frob p hN P
    have hj := (f3 F hF).2.1
    have hFP : H.gal F ∈ φ.Psi ↔ (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1)) := by
      rw [Frame.mem_Psi_iff, ← hj, or_iff_right hp2, and_iff_right hp2]
      exact (Units.val_eq_one).symm
    rw [← hFP]
    constructor
    · intro h
      exact h F hF.mem_stabilizer
    · intro hFm τ hτ
      obtain ⟨k, ρ, hρ, rfl⟩ := Decomp.stab_eq_inertia_mul p P F τ hF hτ
      rw [(f4 ρ).mp hρ, one_mul, map_pow]
      exact Subgroup.pow_mem _ hFm k

/- English proof (translation)
The claim follows from `C.cm; (IsCMField.complexConj H.E).restrictScalars ℚ = H.conj := by haveI := C.cm apply H.gal.injective rw [kc_gal_conj] let ψ : H.E →+* ℂ := (IsAlgClosed.lift : H.E →ₐ[ℚ] ℂ).toRingHom exact (C.conj_iff ψ _).mp (fun x => IsCMField.complexEmbedding_complexConj H.E ψ x)`.
-/
theorem kc_conj_eq : haveI := C.cm; (IsCMField.complexConj H.E).restrictScalars ℚ = H.conj := by
  haveI := C.cm
  apply H.gal.injective
  rw [kc_gal_conj]
  let ψ : H.E →+* ℂ := (IsAlgClosed.lift : H.E →ₐ[ℚ] ℂ).toRingHom
  exact (C.conj_iff ψ _).mp (fun x => IsCMField.complexEmbedding_complexConj H.E ψ x)

/- English proof (translation)
The claim follows from `C.cm; ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ≠ ⊥ → ¬ ∀ x : 𝓞 H.E, IsCMField.complexConj H.E • x - x ∈ P := by haveI := C.cm intro P hP hne h apply C.unramEF P hP hne intro x have e : H.conj • x = IsCMField.complexConj H.E • x := by rw [← kc_conj_eq H C] rfl rw [e] exact h x`.
-/
theorem kc_unr : haveI := C.cm; ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ≠ ⊥ →
    ¬ ∀ x : 𝓞 H.E, IsCMField.complexConj H.E • x - x ∈ P := by
  haveI := C.cm
  intro P hP hne h
  apply C.unramEF P hP hne
  intro x
  have e : H.conj • x = IsCMField.complexConj H.E • x := by
    rw [← kc_conj_eq H C]
    rfl
  rw [e]
  exact h x

/- English proof (translation)
Use `C.cm` as an intermediate fact. Establish `hunr` using `kc_unr H C`. Establish `hsm : ∀ P : Ideal (𝓞 H.E), IsCMField.complexConj H.E • P = H.conj • P` using `fun P => by`. Rewrite using `[← kc_conj_eq H C]`. Both sides reduce to the same expression.

Establish `hetaiff : ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime], P ≠ ⊥ → (H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1 ↔ H.conj • P ≠ P)`. Introduce `P _ hP0`. Establish `hk` using `Eta.ncard_eq_two_iff H.E hunr P hP0`. Rewrite `hk` using `[hsm]`. Unfold `HostRaw.etaF`.

Express the relevant statement in the definitionally equal form `(if (primesOver (P.under (𝓞 H.F)) (𝓞 H.E)).ncard = 2 then (1 : ℤ) else -1) = 1 ↔ _`. Rewrite using `[← hk]`. Use `split_ifs with h2`. Conclude with `iff_of_true rfl h2`. Conclude with `iff_of_false (by decide) h2`.

Use `⟨fun 𝔭 hp h0 => ?_, ?_, ?_⟩` and prove the remaining obligations. Use `hp` as an intermediate fact. Conclude with `Eta.split_or_inert H.E hunr 𝔭 h0`. Introduce `p hpf hN P _ _ σ hσ`. Establish `hP0` using `kc_ne_bot p hpf.out P`.

Establish `hm1 : H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 ↔ H.conj • P = P`. Establish `h1` using `hetaiff P hP0`. Establish `hval : H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1 ∨ H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1`. Apply the tactic sequence `unfold HostRaw.etaF; split_ifs <;> simp`. Prove the components needed by the constructor for the conclusion.

Introduce `hm`. Assume the negation of the conclusion as `hc`. Rewrite `hm` using `[h1.mpr hc]`. Conclude with `absurd hm (by decide)`. Introduce `hfix`.

Break down `hval with hv | hv` into its components or cases. Conclude with `absurd hfix (h1.mp hv)`. Conclude with `hv`. Rewrite using `[hm1]`. Prove the components needed by the constructor for the conclusion.

Introduce `hfix`. Establish `hst : H.conj ∈ MulAction.stabilizer _ P` using `hfix`. Take `⟨k, ρ, hρ, hρeq⟩` from `Decomp.stab_eq_inertia_mul p P σ H.conj hσ hst`. Rewrite `hρeq` using `[((C.frob p hN P).2.2.2 ρ).mp hρ, one_mul]`. Conclude with `Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [zpow_natCast, ← map_pow, ← hρeq, kc_gal_conj]⟩`.

Introduce `hg`. Take `⟨k, hk⟩` from `Subgroup.mem_zpowers_iff.mp hg`. Establish `hσc : σ ^ k = H.conj` using `H.gal.injective (by rw [map_zpow, hk, kc_gal_conj])`. Rewrite using `[← hσc]`. Conclude with `Subgroup.zpow_mem _ hσ.mem_stabilizer k`.

Introduce `p hpf hN P _ _`. Conclude with `(hetaiff P (kc_ne_bot p hpf.out P)).mpr (C.decompConj p hpf.out hN P)`.
-/
theorem eta : (∀ 𝔭 : Ideal (𝓞 H.F), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      (primesOver 𝔭 (𝓞 H.E)).ncard = 2 ∨ ((primesOver 𝔭 (𝓞 H.E)).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 H.E) = 2)) ∧
    (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P →
        (H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 ↔ φ.cc ∈ Subgroup.zpowers (H.gal σ))) ∧
    (∀ (p : ℕ) [Fact p.Prime], p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
        H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1) := by
  have := C.cm
  have hunr := kc_unr H C
  have hsm : ∀ P : Ideal (𝓞 H.E), IsCMField.complexConj H.E • P = H.conj • P := fun P => by
    rw [← kc_conj_eq H C]
    rfl
  have hetaiff : ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime], P ≠ ⊥ →
      (H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1 ↔ H.conj • P ≠ P) := by
    intro P _ hP0
    have hk := Eta.ncard_eq_two_iff H.E hunr P hP0
    rw [hsm] at hk
    unfold HostRaw.etaF
    change (if (primesOver (P.under (𝓞 H.F)) (𝓞 H.E)).ncard = 2 then (1 : ℤ) else -1) = 1 ↔ _
    rw [← hk]
    split_ifs with h2
    · exact iff_of_true rfl h2
    · exact iff_of_false (by decide) h2
  refine ⟨fun 𝔭 hp h0 => ?_, ?_, ?_⟩
  · have := hp
    exact Eta.split_or_inert H.E hunr 𝔭 h0
  · intro p hpf hN P _ _ σ hσ
    have hP0 := kc_ne_bot p hpf.out P
    have hm1 : H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 ↔ H.conj • P = P := by
      have h1 := hetaiff P hP0
      have hval : H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1 ∨
          H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 := by
        unfold HostRaw.etaF; split_ifs <;> simp
      constructor
      · intro hm
        by_contra hc
        rw [h1.mpr hc] at hm
        exact absurd hm (by decide)
      · intro hfix
        rcases hval with hv | hv
        · exact absurd hfix (h1.mp hv)
        · exact hv
    rw [hm1]
    constructor
    · intro hfix
      have hst : H.conj ∈ MulAction.stabilizer _ P := hfix
      obtain ⟨k, ρ, hρ, hρeq⟩ := Decomp.stab_eq_inertia_mul p P σ H.conj hσ hst
      rw [((C.frob p hN P).2.2.2 ρ).mp hρ, one_mul] at hρeq
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [zpow_natCast, ← map_pow, ← hρeq, kc_gal_conj]⟩
    · intro hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hσc : σ ^ k = H.conj := H.gal.injective (by rw [map_zpow, hk, kc_gal_conj])
      rw [← hσc]
      exact Subgroup.zpow_mem _ hσ.mem_stabilizer k
  · intro p hpf hN P _ _
    exact (hetaiff P (kc_ne_bot p hpf.out P)).mpr (C.decompConj p hpf.out hN P)

end Formalism.HC.Der

end
