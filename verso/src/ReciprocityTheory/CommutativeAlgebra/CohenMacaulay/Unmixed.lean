import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.AssDim

namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence

variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]

/- English proof (translation)
Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot`. It suffices to derive a contradiction. Use `first`. Consider the case `(simp at h; done)`.

Consider the case `(rw [WithBot.bot_add] at h; exact WithBot.bot_ne_coe (a := (n : ℕ∞)) (by exact_mod_cast h))`. Consider the case `coe b`. Proceed by induction on `b using ENat.recTopCoe with`. Consider the case `top`. It suffices to derive a contradiction.

Establish `h' : (⊤ : ℕ∞) + 1 = (n : ℕ∞)` using `by exact_mod_cast h`. Simplify using `at h'`. Consider the case `coe k`. Establish `h' : k + 1 = n` using `by exact_mod_cast h`. Apply the tactic sequence `exact ⟨k, h'.symm, by first | rfl | norm_cast | simp⟩`.
-/
private theorem unm_add_one_eq {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 = n) :
    ∃ m : ℕ, n = m + 1 ∧ a = m := by
  induction a using WithBot.recBotCoe with
  | bot =>
    exfalso
    first
    | (simp at h; done)
    | (rw [WithBot.bot_add] at h; exact WithBot.bot_ne_coe (a := (n : ℕ∞)) (by exact_mod_cast h))
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (⊤ : ℕ∞) + 1 = (n : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe k =>
      have h' : k + 1 = n := by exact_mod_cast h
      exact ⟨k, h'.symm, by first | rfl | norm_cast | simp⟩

/- English proof (translation)
Use `ringKrullDim_le_of_surjective (Ideal.Quotient.lift I (Ideal.Quotient.mk J) (fun y hy => Ideal.Quotient.eq_zero_iff_mem.mpr (h hy))) ?_` and prove the remaining obligations. Introduce `z`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Conclude with `⟨Ideal.Quotient.mk I y, rfl⟩`.
-/
private theorem unm_dim_le_of_le {I J : Ideal R} (h : I ≤ J) :
    ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ I) := by
  refine ringKrullDim_le_of_surjective
    (Ideal.Quotient.lift I (Ideal.Quotient.mk J)
      (fun y hy => Ideal.Quotient.eq_zero_iff_mem.mpr (h hy))) ?_
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨Ideal.Quotient.mk I y, rfl⟩

/- English proof (translation)
Take `⟨a, haP, haQ⟩` from `SetLike.exists_of_lt h`. Establish `hx0 : (Ideal.Quotient.mk Q a : R ⧸ Q) ≠ 0` using `fun hx => haQ (Ideal.Quotient.eq_zero_iff_mem.mp hx)`. Establish `hxreg : (Ideal.Quotient.mk Q a : R ⧸ Q) ∈ nonZeroDivisors (R ⧸ Q)` using `mem_nonZeroDivisors_of_ne_zero hx0`. Set `g : R ⧸ Q →+* R ⧸ P` to `Ideal.Quotient.lift Q (Ideal.Quotient.mk P) (fun y hy => Ideal.Quotient.eq_zero_iff_mem.mpr (h.le hy))`. Establish `hgx : g (Ideal.Quotient.mk Q a) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr haP`.

Set `f : (R ⧸ Q) ⧸ Ideal.span {(Ideal.Quotient.mk Q a : R ⧸ Q)} →+* R ⧸ P` to `Ideal.Quotient.lift (Ideal.span {(Ideal.Quotient.mk Q a : R ⧸ Q)}) g (fun y hy => by`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Rewrite using `[map_mul, hgx, mul_zero])`. Establish `hf : Function.Surjective f`. Introduce `z`.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Conclude with `⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk Q y), rfl⟩`. Establish `hle : ringKrullDim (R ⧸ P) ≤ ringKrullDim ((R ⧸ Q) ⧸ Ideal.span {(Ideal.Quotient.mk Q a : R ⧸ Q)})` using `ringKrullDim_le_of_surjective f hf`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem unm_dim_succ_le_of_lt {Q P : Ideal R} [Q.IsPrime] (h : Q < P) :
    ringKrullDim (R ⧸ P) + 1 ≤ ringKrullDim (R ⧸ Q) := by
  obtain ⟨a, haP, haQ⟩ := SetLike.exists_of_lt h
  have hx0 : (Ideal.Quotient.mk Q a : R ⧸ Q) ≠ 0 :=
    fun hx => haQ (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  have hxreg : (Ideal.Quotient.mk Q a : R ⧸ Q) ∈ nonZeroDivisors (R ⧸ Q) :=
    mem_nonZeroDivisors_of_ne_zero hx0
  let g : R ⧸ Q →+* R ⧸ P := Ideal.Quotient.lift Q (Ideal.Quotient.mk P)
    (fun y hy => Ideal.Quotient.eq_zero_iff_mem.mpr (h.le hy))
  have hgx : g (Ideal.Quotient.mk Q a) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr haP
  let f : (R ⧸ Q) ⧸ Ideal.span {(Ideal.Quotient.mk Q a : R ⧸ Q)} →+* R ⧸ P :=
    Ideal.Quotient.lift (Ideal.span {(Ideal.Quotient.mk Q a : R ⧸ Q)}) g
      (fun y hy => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
        rw [map_mul, hgx, mul_zero])
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk Q y), rfl⟩
  have hle : ringKrullDim (R ⧸ P) ≤
      ringKrullDim ((R ⧸ Q) ⧸ Ideal.span {(Ideal.Quotient.mk Q a : R ⧸ Q)}) :=
    ringKrullDim_le_of_surjective f hf
  calc ringKrullDim (R ⧸ P) + 1
      ≤ ringKrullDim ((R ⧸ Q) ⧸ Ideal.span {(Ideal.Quotient.mk Q a : R ⧸ Q)}) + 1 := by
        first | gcongr | exact add_le_add_right hle 1
    _ ≤ ringKrullDim (R ⧸ Q) := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hxreg

/- English proof (translation)
Take `⟨rs, hlen, hmem, hreg⟩` from `id h`. Unfold `ModDepthGE`. Use `⟨rs, hlen, hmem, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `exact (LinearEquiv.isRegular_congr e rs).mp hreg`.

Consider the case `exact (e.isRegular_congr rs).mp hreg`. Consider the case `exact (LinearEquiv.isRegular_congr' e rs).mp hreg`.
-/
private theorem unm_modDepthGE_congr {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {n : ℕ} (h : ModDepthGE R M n) : ModDepthGE R N n := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := id h
  unfold ModDepthGE
  refine ⟨rs, hlen, hmem, ?_⟩
  first
  | exact (LinearEquiv.isRegular_congr e rs).mp hreg
  | exact (e.isRegular_congr rs).mp hreg
  | exact (LinearEquiv.isRegular_congr' e rs).mp hreg

/- English proof (translation)
Take `⟨hR, hfin, n, hdim, hdep⟩` from `id h`. Use `haveI := hfin`. Establish `hs : Module.support R N = Module.support R M` using `(Module.support_subset_of_surjective e.toLinearMap e.surjective).antisymm (Module.support_subset_of_surjective e.symm.toLinearMap e.symm.surjective)`. Unfold `IsCMMod`. Use `⟨hR, Module.Finite.equiv e, n, ?_, unm_modDepthGE_congr e hdep⟩` and prove the remaining obligations.

Rewrite using `[← hdim]`. Use `first`. Consider the case `(unfold Module.supportDim; rw [hs])`. Consider the case `(simp only [Module.supportDim, hs])`. Consider the case `exact (Module.supportDim_eq_of_equiv e).symm`.
-/
private theorem unm_isCMMod_congr {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (h : IsCMMod R M) : IsCMMod R N := by
  obtain ⟨hR, hfin, n, hdim, hdep⟩ := id h
  haveI := hfin
  have hs : Module.support R N = Module.support R M :=
    (Module.support_subset_of_surjective e.toLinearMap e.surjective).antisymm
      (Module.support_subset_of_surjective e.symm.toLinearMap e.symm.surjective)
  unfold IsCMMod
  refine ⟨hR, Module.Finite.equiv e, n, ?_, unm_modDepthGE_congr e hdep⟩
  rw [← hdim]
  first
  | (unfold Module.supportDim; rw [hs])
  | (simp only [Module.supportDim, hs])
  | exact (Module.supportDim_eq_of_equiv e).symm

/- English proof (translation)
Take `⟨hR, hfin, n, hdim, hdep⟩` from `id h`. Use `haveI := hR`. Use `haveI := hfin`. Establish `hann : Module.annihilator R M ≤ p` using `by first`. Consider the case `(have h0 := IsAssociatedPrime.annihilator_le hp`.

Rewrite using `[Submodule.annihilator_top] at h0)` and apply the resulting hypothesis. Consider the case `exact Submodule.annihilator_top (R := R) (M := M) ▸ IsAssociatedPrime.annihilator_le hp`. Establish `hsupp : Module.supportDim R M = ringKrullDim (R ⧸ Module.annihilator R M)` using `by first`. Consider the case `exact Module.supportDim_eq_ringKrullDim_quotient_annihilator R M`. Consider the case `exact Module.supportDim_eq_ringKrullDim_quotient_annihilator`.

Consider the case `(rw [ringKrullDim_quotient]; unfold Module.supportDim; rw [Module.support_eq_zeroLocus])`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[hsupp]`. Conclude with `unm_dim_le_of_le hann`. Rewrite using `[hdim]`.

Conclude with `hdep.le_ringKrullDim_quotient_of_mem_associatedPrimes hp`.
-/
theorem IsCMMod.ringKrullDim_quotient_eq_supportDim (h : IsCMMod R M) {p : Ideal R}
    (hp : p ∈ associatedPrimes R M) : ringKrullDim (R ⧸ p) = Module.supportDim R M := by
  obtain ⟨hR, hfin, n, hdim, hdep⟩ := id h
  haveI := hR
  haveI := hfin
  have hann : Module.annihilator R M ≤ p := by
    first
    | (have h0 := IsAssociatedPrime.annihilator_le hp
       rwa [Submodule.annihilator_top] at h0)
    | exact Submodule.annihilator_top (R := R) (M := M) ▸ IsAssociatedPrime.annihilator_le hp
  have hsupp : Module.supportDim R M = ringKrullDim (R ⧸ Module.annihilator R M) := by
    first
    | exact Module.supportDim_eq_ringKrullDim_quotient_annihilator R M
    | exact Module.supportDim_eq_ringKrullDim_quotient_annihilator
    | (rw [ringKrullDim_quotient]; unfold Module.supportDim; rw [Module.support_eq_zeroLocus])
  apply le_antisymm
  · rw [hsupp]
    exact unm_dim_le_of_le hann
  · rw [hdim]
    exact hdep.le_ringKrullDim_quotient_of_mem_associatedPrimes hp

/- English proof (translation)
Take `⟨hR, hfin, n, hdim, -⟩` from `id h`. Use `haveI := hR`. Use `haveI := hfin`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `p hp`.

Establish `hpp : p.IsPrime` using `IsAssociatedPrime.isPrime hp`. Establish `hann : Module.annihilator R M ≤ p` using `by first`. Consider the case `(have h0 := IsAssociatedPrime.annihilator_le hp`. Rewrite using `[Submodule.annihilator_top] at h0)` and apply the resulting hypothesis. Consider the case `exact Submodule.annihilator_top (R := R) (M := M) ▸ IsAssociatedPrime.annihilator_le hp`.

Establish `hsupp : Module.supportDim R M = ringKrullDim (R ⧸ Module.annihilator R M)` using `by first`. Consider the case `exact Module.supportDim_eq_ringKrullDim_quotient_annihilator R M`. Consider the case `exact Module.supportDim_eq_ringKrullDim_quotient_annihilator`. Consider the case `(rw [ringKrullDim_quotient]; unfold Module.supportDim; rw [Module.support_eq_zeroLocus])`. Establish `hp' : ringKrullDim (R ⧸ p) = (n : WithBot ℕ∞)` using `(h.ringKrullDim_quotient_eq_supportDim hp).trans hdim`.

Use `⟨⟨hpp, hann⟩, fun q hq hqp => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hlt : q < p` using `lt_of_le_of_ne hqp (fun e => hne (le_of_eq e.symm))`. Use `haveI := hq.1`. Establish `h1` using `unm_dim_succ_le_of_lt hlt`.

Establish `h2 : ringKrullDim (R ⧸ q) ≤ (n : WithBot ℕ∞)`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h1` using `[hp']`. Establish `h3` using `h1.trans h2`. Establish `h4 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞)` using `by exact_mod_cast h3`.

Establish `h5 : n + 1 ≤ n` using `by exact_mod_cast h4`. Use linear arithmetic over natural numbers and integers. Use `first`. Consider the case `exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M`. Consider the case `exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes`.

Consider the case `exact minimalPrimes_annihilator_subset_associatedPrimes R M`. Consider the case `exact minimalPrimes_annihilator_subset_associatedPrimes`. Consider the case `exact associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M`. Consider the case `exact Module.minimalPrimes_annihilator_subset_associatedPrimes`.
-/
theorem IsCMMod.associatedPrimes_eq_minimalPrimes (h : IsCMMod R M) :
    associatedPrimes R M = (Module.annihilator R M).minimalPrimes := by
  obtain ⟨hR, hfin, n, hdim, -⟩ := id h
  haveI := hR
  haveI := hfin
  apply Set.Subset.antisymm
  · intro p hp
    have hpp : p.IsPrime := IsAssociatedPrime.isPrime hp
    have hann : Module.annihilator R M ≤ p := by
      first
      | (have h0 := IsAssociatedPrime.annihilator_le hp
         rwa [Submodule.annihilator_top] at h0)
      | exact Submodule.annihilator_top (R := R) (M := M) ▸ IsAssociatedPrime.annihilator_le hp
    have hsupp : Module.supportDim R M = ringKrullDim (R ⧸ Module.annihilator R M) := by
      first
      | exact Module.supportDim_eq_ringKrullDim_quotient_annihilator R M
      | exact Module.supportDim_eq_ringKrullDim_quotient_annihilator
      | (rw [ringKrullDim_quotient]; unfold Module.supportDim; rw [Module.support_eq_zeroLocus])
    have hp' : ringKrullDim (R ⧸ p) = (n : WithBot ℕ∞) :=
      (h.ringKrullDim_quotient_eq_supportDim hp).trans hdim
    refine ⟨⟨hpp, hann⟩, fun q hq hqp => ?_⟩
    by_contra hne
    have hlt : q < p := lt_of_le_of_ne hqp (fun e => hne (le_of_eq e.symm))
    haveI := hq.1
    have h1 := unm_dim_succ_le_of_lt hlt
    have h2 : ringKrullDim (R ⧸ q) ≤ (n : WithBot ℕ∞) := by
      calc ringKrullDim (R ⧸ q) ≤ ringKrullDim (R ⧸ Module.annihilator R M) :=
            unm_dim_le_of_le hq.2
        _ = (n : WithBot ℕ∞) := hsupp.symm.trans hdim
    rw [hp'] at h1
    have h3 := h1.trans h2
    have h4 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by exact_mod_cast h3
    have h5 : n + 1 ≤ n := by exact_mod_cast h4
    omega
  · first
    | exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M
    | exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    | exact minimalPrimes_annihilator_subset_associatedPrimes R M
    | exact minimalPrimes_annihilator_subset_associatedPrimes
    | exact associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M
    | exact Module.minimalPrimes_annihilator_subset_associatedPrimes

/- English proof (translation)
Take `⟨hR, hfin, n, hdim, hdep⟩` from `id h`. Use `haveI := hR`. Use `haveI := hfin`. Establish `hsd : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M` using `by first`. Consider the case `exact Module.supportDim_quotSMulTop_succ_eq_supportDim reg hx`.

Consider the case `exact Module.supportDim_quotSMulTop_succ_eq_supportDim hx reg`. Consider the case `exact supportDim_quotSMulTop_succ_eq_supportDim reg hx`. Rewrite `hsd` using `[hdim]`. Take `⟨m, rfl, hm⟩` from `unm_add_one_eq hsd`. Unfold `IsCMMod`.

Apply the tactic sequence `exact ⟨hR, by first | infer_instance | exact Module.Finite.quotient R _, m, hm, hdep.quotSMulTop hx reg⟩`.
-/
theorem IsCMMod.quotSMulTop (h : IsCMMod R M) {x : R} (hx : x ∈ maximalIdeal R)
    (reg : IsSMulRegular M x) : IsCMMod R (QuotSMulTop x M) := by
  obtain ⟨hR, hfin, n, hdim, hdep⟩ := id h
  haveI := hR
  haveI := hfin
  have hsd : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M := by
    first
    | exact Module.supportDim_quotSMulTop_succ_eq_supportDim reg hx
    | exact Module.supportDim_quotSMulTop_succ_eq_supportDim hx reg
    | exact supportDim_quotSMulTop_succ_eq_supportDim reg hx
  rw [hdim] at hsd
  obtain ⟨m, rfl, hm⟩ := unm_add_one_eq hsd
  unfold IsCMMod
  exact ⟨hR, by first | infer_instance | exact Module.Finite.quotient R _, m, hm,
    hdep.quotSMulTop hx reg⟩

/- English proof (translation)
Take `⟨-, -, n, hdim, hdep⟩` from `id h`. Establish `hsd : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M` using `by first`. Consider the case `exact Module.supportDim_quotSMulTop_succ_eq_supportDim reg hx`. Consider the case `exact Module.supportDim_quotSMulTop_succ_eq_supportDim hx reg`. Consider the case `exact supportDim_quotSMulTop_succ_eq_supportDim reg hx`.

Unfold `IsCMMod`. Use `⟨inferInstance, inferInstance, n + 1, ?_, hdep.of_quotSMulTop hx reg⟩` and prove the remaining obligations. Use `first`. Consider the case `(rw [← hsd, hdim]; done)`. Consider the case `(rw [← hsd, hdim]; norm_cast)`.

Consider the case `(rw [← hsd, hdim]; simp)`.
-/
theorem IsCMMod.of_quotSMulTop [IsNoetherianRing R] [Module.Finite R M] {x : R}
    (hx : x ∈ maximalIdeal R) (reg : IsSMulRegular M x) (h : IsCMMod R (QuotSMulTop x M)) :
    IsCMMod R M := by
  obtain ⟨-, -, n, hdim, hdep⟩ := id h
  have hsd : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M := by
    first
    | exact Module.supportDim_quotSMulTop_succ_eq_supportDim reg hx
    | exact Module.supportDim_quotSMulTop_succ_eq_supportDim hx reg
    | exact supportDim_quotSMulTop_succ_eq_supportDim reg hx
  unfold IsCMMod
  refine ⟨inferInstance, inferInstance, n + 1, ?_, hdep.of_quotSMulTop hx reg⟩
  first
  | (rw [← hsd, hdim]; done)
  | (rw [← hsd, hdim]; norm_cast)
  | (rw [← hsd, hdim]; simp)

/- English proof (translation)
Take `⟨hR, hfin, n, hdim, hdep⟩` from `id h`. Use `haveI := hR`. Use `haveI := hfin`. Assume the negation of the conclusion as `hx`. Establish `hmem : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R)`.

Rewrite using `[biUnion_associatedPrimes_eq_compl_regular]`. Conclude with `hx`. Simplify using `only [Set.mem_iUnion, SetLike.mem_coe] at hmem`. Take `⟨p, hp, hxp⟩` from `hmem`. Establish `hpp : p.IsPrime` using `IsAssociatedPrime.isPrime hp`.

Establish `hann : Module.annihilator R M ≤ p` using `by first`. Consider the case `(have h0 := IsAssociatedPrime.annihilator_le hp`. Rewrite using `[Submodule.annihilator_top] at h0)` and apply the resulting hypothesis. Consider the case `exact Submodule.annihilator_top (R := R) (M := M) ▸ IsAssociatedPrime.annihilator_le hp`. Establish `hsuppQ : (⟨p, hpp⟩ : PrimeSpectrum R) ∈ Module.support R (QuotSMulTop x M)`.

Rewrite using `[Module.support_quotSMulTop]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.mem_support_iff_of_finite]`. Conclude with `hann`. Simplify using `[PrimeSpectrum.mem_zeroLocus, hxp]`.

Establish `hannQ : Module.annihilator R (QuotSMulTop x M) ≤ p` using `Module.mem_support_iff_of_finite.mp hsuppQ`. Establish `hsQ : Module.supportDim R (QuotSMulTop x M) = ringKrullDim (R ⧸ Module.annihilator R (QuotSMulTop x M))` using `by first`. Consider the case `exact Module.supportDim_eq_ringKrullDim_quotient_annihilator R (QuotSMulTop x M)`. Consider the case `exact Module.supportDim_eq_ringKrullDim_quotient_annihilator`. Consider the case `(rw [ringKrullDim_quotient]; unfold Module.supportDim; rw [Module.support_eq_zeroLocus])`.

Establish `hle` using `unm_dim_le_of_le hannQ`. Rewrite `hle` using `[h.ringKrullDim_quotient_eq_supportDim hp, ← hsQ]`. Conclude with `absurd hd (not_lt.mpr hle)`.
-/
theorem IsCMMod.isSMulRegular_of_supportDim_quotSMulTop_lt (h : IsCMMod R M) {x : R}
    (hd : Module.supportDim R (QuotSMulTop x M) < Module.supportDim R M) :
    IsSMulRegular M x := by
  obtain ⟨hR, hfin, n, hdim, hdep⟩ := id h
  haveI := hR
  haveI := hfin
  by_contra hx
  have hmem : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact hx
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hmem
  obtain ⟨p, hp, hxp⟩ := hmem
  have hpp : p.IsPrime := IsAssociatedPrime.isPrime hp
  have hann : Module.annihilator R M ≤ p := by
    first
    | (have h0 := IsAssociatedPrime.annihilator_le hp
       rwa [Submodule.annihilator_top] at h0)
    | exact Submodule.annihilator_top (R := R) (M := M) ▸ IsAssociatedPrime.annihilator_le hp
  have hsuppQ : (⟨p, hpp⟩ : PrimeSpectrum R) ∈ Module.support R (QuotSMulTop x M) := by
    rw [Module.support_quotSMulTop]
    refine ⟨?_, ?_⟩
    · rw [Module.mem_support_iff_of_finite]
      exact hann
    · simp [PrimeSpectrum.mem_zeroLocus, hxp]
  have hannQ : Module.annihilator R (QuotSMulTop x M) ≤ p :=
    Module.mem_support_iff_of_finite.mp hsuppQ
  have hsQ : Module.supportDim R (QuotSMulTop x M) =
      ringKrullDim (R ⧸ Module.annihilator R (QuotSMulTop x M)) := by
    first
    | exact Module.supportDim_eq_ringKrullDim_quotient_annihilator R (QuotSMulTop x M)
    | exact Module.supportDim_eq_ringKrullDim_quotient_annihilator
    | (rw [ringKrullDim_quotient]; unfold Module.supportDim; rw [Module.support_eq_zeroLocus])
  have hle := unm_dim_le_of_le hannQ
  rw [h.ringKrullDim_quotient_eq_supportDim hp, ← hsQ] at hle
  exact absurd hd (not_lt.mpr hle)

/- English proof (translation)
Proceed by induction on `rs generalizing M with`. Consider the case `nil`. Use `unm_isCMMod_congr (Submodule.quotEquivOfEqBot _ ?_).symm h` and prove the remaining obligations. Apply the tactic sequence `first | simp | simp [Ideal.ofList]`. Consider the case `cons r rs ih`.

Rewrite `reg` using `[RingTheory.Sequence.isRegular_cons_iff]`. Establish `hr : r ∈ maximalIdeal R` using `hrs r (by simp)`. Establish `h1` using `h.quotSMulTop hr reg.1`. Establish `h2` using `ih h1 (fun s hs => hrs s (by simp [hs])) reg.2`. Conclude with `unm_isCMMod_congr (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r rs).symm h2`.
-/
theorem IsCMMod.quotient_ofList (h : IsCMMod R M) {rs : List R}
    (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R) (reg : IsRegular M rs) :
    IsCMMod R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) := by
  induction rs generalizing M with
  | nil =>
    refine unm_isCMMod_congr (Submodule.quotEquivOfEqBot _ ?_).symm h
    first | simp | simp [Ideal.ofList]
  | cons r rs ih =>
    rw [RingTheory.Sequence.isRegular_cons_iff] at reg
    have hr : r ∈ maximalIdeal R := hrs r (by simp)
    have h1 := h.quotSMulTop hr reg.1
    have h2 := ih h1 (fun s hs => hrs s (by simp [hs])) reg.2
    exact unm_isCMMod_congr
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r rs).symm h2

/- English proof (translation)
The claim follows from `| [], N, _, _, _, _ => by rw [Ideal.ofList_nil, Submodule.bot_smul, Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot ⊥ rfl)] simp | y :: ys, N, _, _, _, hys => by have h1 := Module.supportDim_le_supportDim_quotSMulTop_succ (M := N) (hys y List.mem_cons_self) have h2 := u …`.
-/
private theorem unm_supportDim_le_quotient_add [IsNoetherianRing R] :
    ∀ (ys : List R) (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N],
      (∀ r ∈ ys, r ∈ maximalIdeal R) →
      Module.supportDim R N ≤
        Module.supportDim R (N ⧸ Ideal.ofList ys • (⊤ : Submodule R N)) + ys.length
  | [], N, _, _, _, _ => by
    rw [Ideal.ofList_nil, Submodule.bot_smul,
      Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot ⊥ rfl)]
    simp
  | y :: ys, N, _, _, _, hys => by
    have h1 := Module.supportDim_le_supportDim_quotSMulTop_succ (M := N) (hys y List.mem_cons_self)
    have h2 := unm_supportDim_le_quotient_add ys (QuotSMulTop y N)
      (fun s hs => hys s (List.mem_cons_of_mem y hs))
    rw [Module.supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner N y ys)]
    calc Module.supportDim R N ≤ Module.supportDim R (QuotSMulTop y N) + 1 := h1
      _ ≤ (Module.supportDim R (QuotSMulTop y N ⧸ Ideal.ofList ys • (⊤ : Submodule R (QuotSMulTop y N)))
            + ys.length) + 1 := by gcongr
      _ = _ := by
        rw [List.length_cons, add_assoc]
        push_cast
        rfl

/- English proof (translation)
Proceed by induction on `xs generalizing M with`. Consider the case `nil`. Take `⟨-, -, n, hdim, hdep⟩` from `id h`. Establish `hn : ((0 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞)`. Apply the tactic sequence `rw [← hdim, ← hlen] <;> rfl`.

Establish `hn' : n = 0` using `by exact_mod_cast hn.symm`. Substitute `hn'` using the available equality. Take `⟨rs, hrs, -, hreg⟩` from `id hdep`. Consider the cases of `rs with`. Consider the case `nil => exact hreg`.

Consider the case `cons _ _ => simp at hrs`. Consider the case `cons x xs ih`. Take `⟨hR, hfin, n, hdim, hdep⟩` from `id h`. Use `haveI := hR`. Use `haveI := hfin`.

Establish `hx : x ∈ maximalIdeal R` using `hxs x (by simp)`. Establish `hxs' : ∀ r ∈ xs, r ∈ maximalIdeal R` using `fun r hr => hxs r (by simp [hr])`. Establish `e` using `Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x xs`. Establish `hs : Module.support R (M ⧸ Ideal.ofList (x :: xs) • (⊤ : Submodule R M)) = Module.support R (QuotSMulTop x M ⧸ Ideal.ofList xs • (⊤ : Submodule R (QuotSMulTop x M)))` using `(Module.support_subset_of_surjective e.symm.toLinearMap e.symm.surjective).antisymm (Module.support_subset_of_surjective e.toLinearMap e.surjective)`. Establish `hdd : Module.supportDim R (M ⧸ Ideal.ofList (x :: xs) • (⊤ : Submodule R M)) = Module.supportDim R (QuotSMulTop x M ⧸ Ideal.ofList xs • (⊤ : Submodule R (QuotSMulTop x M)))`.

Unfold `Module.supportDim`. Rewrite using `[hs]`. Establish `hdQ : Module.supportDim R (QuotSMulTop x M ⧸ Ideal.ofList xs • (⊤ : Submodule R (QuotSMulTop x M))) ≤ 0`. Rewrite using `[← hdd]`. Conclude with `h0`.

Establish `hQle : Module.supportDim R (QuotSMulTop x M) ≤ (xs.length : WithBot ℕ∞)`. Establish `h3` using `unm_supportDim_le_quotient_add xs (QuotSMulTop x M) hxs'`. Combine the equalities or inequalities in the displayed calculation. Establish `hlen' : Module.supportDim R M = (xs.length : WithBot ℕ∞) + 1` using `by first`. Consider the case `(rw [← hlen]; simp)`.

Consider the case `(rw [← hlen, List.length_cons, Nat.cast_succ])`. Consider the case `(rw [← hlen]; push_cast; rfl)`. Establish `hlt : Module.supportDim R (QuotSMulTop x M) < Module.supportDim R M`. Establish `hl : ((xs.length : ℕ) : WithBot ℕ∞) < ((xs.length + 1 : ℕ) : WithBot ℕ∞)`. Conclude with `Nat.lt_succ_self _` after adjusting the coercions.

Rewrite using `[hlen']`. Move the coercions through the operations in `at hl`. Conclude with `lt_of_le_of_lt hQle hl`. Establish `reg : IsSMulRegular M x` using `h.isSMulRegular_of_supportDim_quotSMulTop_lt hlt`. Establish `hQ : IsCMMod R (QuotSMulTop x M)` using `h.quotSMulTop hx reg`.

Establish `hsd : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M` using `by first`. Consider the case `exact Module.supportDim_quotSMulTop_succ_eq_supportDim reg hx`. Consider the case `exact Module.supportDim_quotSMulTop_succ_eq_supportDim hx reg`. Consider the case `exact supportDim_quotSMulTop_succ_eq_supportDim reg hx`. Establish `hlenQ : (xs.length : WithBot ℕ∞) = Module.supportDim R (QuotSMulTop x M)`.

Rewrite `hsd` using `[hlen']`. Establish `hsd' : Module.supportDim R (QuotSMulTop x M) + 1 = ((xs.length + 1 : ℕ) : WithBot ℕ∞)`. Apply the tactic sequence `rw [hsd] <;> norm_cast`. Take `⟨m, hm1, hm2⟩` from `unm_add_one_eq hsd'`. Establish `hm : xs.length = m` using `by omega`.

Rewrite using `[hm2, hm]`. Rewrite using `[RingTheory.Sequence.isRegular_cons_iff]`. Conclude with `⟨reg, ih hQ hxs' hlenQ hdQ⟩`.
-/
theorem IsCMMod.isRegular_of_supportDim_quotient_le_zero (h : IsCMMod R M) (xs : List R)
    (hxs : ∀ r ∈ xs, r ∈ maximalIdeal R) (hlen : (xs.length : WithBot ℕ∞) = Module.supportDim R M)
    (h0 : Module.supportDim R (M ⧸ Ideal.ofList xs • (⊤ : Submodule R M)) ≤ 0) :
    IsRegular M xs := by
  induction xs generalizing M with
  | nil =>
    obtain ⟨-, -, n, hdim, hdep⟩ := id h
    have hn : ((0 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
      rw [← hdim, ← hlen] <;> rfl
    have hn' : n = 0 := by exact_mod_cast hn.symm
    subst hn'
    obtain ⟨rs, hrs, -, hreg⟩ := id hdep
    cases rs with
    | nil => exact hreg
    | cons _ _ => simp at hrs
  | cons x xs ih =>
    obtain ⟨hR, hfin, n, hdim, hdep⟩ := id h
    haveI := hR
    haveI := hfin
    have hx : x ∈ maximalIdeal R := hxs x (by simp)
    have hxs' : ∀ r ∈ xs, r ∈ maximalIdeal R := fun r hr => hxs r (by simp [hr])
    have e := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x xs
    have hs : Module.support R (M ⧸ Ideal.ofList (x :: xs) • (⊤ : Submodule R M)) =
        Module.support R
          (QuotSMulTop x M ⧸ Ideal.ofList xs • (⊤ : Submodule R (QuotSMulTop x M))) :=
      (Module.support_subset_of_surjective e.symm.toLinearMap e.symm.surjective).antisymm
        (Module.support_subset_of_surjective e.toLinearMap e.surjective)
    have hdd : Module.supportDim R (M ⧸ Ideal.ofList (x :: xs) • (⊤ : Submodule R M)) =
        Module.supportDim R
          (QuotSMulTop x M ⧸ Ideal.ofList xs • (⊤ : Submodule R (QuotSMulTop x M))) := by
      unfold Module.supportDim
      rw [hs]
    have hdQ : Module.supportDim R
        (QuotSMulTop x M ⧸ Ideal.ofList xs • (⊤ : Submodule R (QuotSMulTop x M))) ≤ 0 := by
      rw [← hdd]
      exact h0
    have hQle : Module.supportDim R (QuotSMulTop x M) ≤ (xs.length : WithBot ℕ∞) := by
      have h3 := unm_supportDim_le_quotient_add xs (QuotSMulTop x M) hxs'
      calc Module.supportDim R (QuotSMulTop x M) ≤ _ := h3
        _ ≤ 0 + (xs.length : WithBot ℕ∞) := by
          first | gcongr | exact add_le_add_right hdQ _
        _ = (xs.length : WithBot ℕ∞) := zero_add _
    have hlen' : Module.supportDim R M = (xs.length : WithBot ℕ∞) + 1 := by
      first
      | (rw [← hlen]; simp)
      | (rw [← hlen, List.length_cons, Nat.cast_succ])
      | (rw [← hlen]; push_cast; rfl)
    have hlt : Module.supportDim R (QuotSMulTop x M) < Module.supportDim R M := by
      have hl : ((xs.length : ℕ) : WithBot ℕ∞) < ((xs.length + 1 : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast Nat.lt_succ_self _
      rw [hlen']
      push_cast at hl
      exact lt_of_le_of_lt hQle hl
    have reg : IsSMulRegular M x := h.isSMulRegular_of_supportDim_quotSMulTop_lt hlt
    have hQ : IsCMMod R (QuotSMulTop x M) := h.quotSMulTop hx reg
    have hsd : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M := by
      first
      | exact Module.supportDim_quotSMulTop_succ_eq_supportDim reg hx
      | exact Module.supportDim_quotSMulTop_succ_eq_supportDim hx reg
      | exact supportDim_quotSMulTop_succ_eq_supportDim reg hx
    have hlenQ : (xs.length : WithBot ℕ∞) = Module.supportDim R (QuotSMulTop x M) := by
      rw [hlen'] at hsd
      have hsd' : Module.supportDim R (QuotSMulTop x M) + 1 = ((xs.length + 1 : ℕ) : WithBot ℕ∞) := by
        rw [hsd] <;> norm_cast
      obtain ⟨m, hm1, hm2⟩ := unm_add_one_eq hsd'
      have hm : xs.length = m := by omega
      rw [hm2, hm]
    rw [RingTheory.Sequence.isRegular_cons_iff]
    exact ⟨reg, ih hQ hxs' hlenQ hdQ⟩

end ReciprocityTheory.CA
