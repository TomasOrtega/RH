import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.ElevenLe
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SplitColumnClasses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible

noncomputable section

namespace GlobalTheory.ColClassCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

section Descent

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {p : ℕ}

/- English proof (translation)
Take `⟨P, hP, hPl⟩` from `(inferInstance : Nonempty (v.primesOver (𝓞 E)))`. Establish `hgP : (p : 𝓞 E) ∈ P`. Simplify using `using (Ideal.mem_of_liesOver P v (p : 𝓞 F)).1 hpv`. Take `⟨hP2, hP3⟩` from `GlobalTheory.LocSplit.split_prime hp h P hgP`. Use `⟨fun h2 => hP2 ?_, ?_⟩` and prove the remaining obligations.

Use `Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h2` as an intermediate fact. Rewrite `this` using `[Ideal.map_pow, map_natCast]`. Conclude with `Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hPl.over.le) 2 this`. Use `haveI : Fact p.Prime := ⟨hp⟩ haveI : Nontrivial (𝓞 F ⧸ v) := Ideal.Quotient.nontrivial_iff.2 hv.ne_top`. Establish `h0 : ((p : ℕ) : 𝓞 F ⧸ v) = 0`.

Rewrite using `[← map_natCast (Ideal.Quotient.mk v), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hpv`. Use `haveI : CharP (𝓞 F ⧸ v) p := (CharP.charP_iff_prime_eq_zero hp).2 h0`. Establish `hb : Function.Bijective (ZMod.castHom (dvd_refl p) (𝓞 F ⧸ v))`. Use `⟨RingHom.injective _, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨m, hm⟩` from `hP3 (algebraMap (𝓞 F) (𝓞 E) x)`. Use `⟨(m : ZMod p), ?_⟩` and prove the remaining obligations. Rewrite using `[map_intCast, ← map_intCast (Ideal.Quotient.mk v), eq_comm, Ideal.Quotient.eq, Ideal.mem_of_liesOver P v]`. Simplify using `using hm`.

Rewrite using `[← Nat.card_eq_of_bijective _ hb, Nat.card_zmod]`.
-/
theorem unram_card_of_split (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E)
    (v : Ideal (𝓞 F)) [hv : v.IsPrime] (hpv : (p : 𝓞 F) ∈ v) :
    (p : 𝓞 F) ∉ v ^ 2 ∧ Nat.card (𝓞 F ⧸ v) = p := by
  obtain ⟨P, hP, hPl⟩ := (inferInstance : Nonempty (v.primesOver (𝓞 E)))
  have hgP : (p : 𝓞 E) ∈ P := by
    simpa using (Ideal.mem_of_liesOver P v (p : 𝓞 F)).1 hpv
  obtain ⟨hP2, hP3⟩ := GlobalTheory.LocSplit.split_prime hp h P hgP
  refine ⟨fun h2 => hP2 ?_, ?_⟩
  · have := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h2
    rw [Ideal.map_pow, map_natCast] at this
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hPl.over.le) 2 this
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : Nontrivial (𝓞 F ⧸ v) := Ideal.Quotient.nontrivial_iff.2 hv.ne_top
    have h0 : ((p : ℕ) : 𝓞 F ⧸ v) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v), Ideal.Quotient.eq_zero_iff_mem]
      exact hpv
    haveI : CharP (𝓞 F ⧸ v) p := (CharP.charP_iff_prime_eq_zero hp).2 h0
    have hb : Function.Bijective (ZMod.castHom (dvd_refl p) (𝓞 F ⧸ v)) := by
      refine ⟨RingHom.injective _, fun x => ?_⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨m, hm⟩ := hP3 (algebraMap (𝓞 F) (𝓞 E) x)
      refine ⟨(m : ZMod p), ?_⟩
      rw [map_intCast, ← map_intCast (Ideal.Quotient.mk v), eq_comm, Ideal.Quotient.eq,
        Ideal.mem_of_liesOver P v]
      simpa using hm
    rw [← Nat.card_eq_of_bijective _ hb, Nat.card_zmod]

/- English proof (translation)
Establish `hp' : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Use `haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp'.ne_zero).mpr hp'`. Establish `hne : (Ideal.span {(p : ℤ)}) ≠ ⊥` using `by simpa using hp.ne_zero`. Use `haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne`. Establish `hs` using `Ideal.sum_ramification_inertia (𝓞 F) ℚ F (p := Ideal.span {(p : ℤ)}) hne`.

Rewrite using `[← hs, ← IsDedekindDomain.coe_primesOverFinset hne, Set.ncard_coe_finset, Finset.card_eq_sum_ones]`. Use `Finset.sum_congr rfl fun q hq => ?_` and prove the remaining obligations. Rewrite `hq` using `[IsDedekindDomain.mem_primesOverFinset_iff hne]`. Use `haveI := hq.1`. Use `haveI := hq.2`.

Establish `hpq : (p : 𝓞 F) ∈ q`. Simplify using `using (Ideal.mem_of_liesOver q (Ideal.span {(p : ℤ)}) (p : ℤ)).1 (Ideal.mem_span_singleton_self _)`. Take `⟨h2, hc⟩` from `unram_card_of_split (E := E) hp h q hpq`. Establish `he : (Ideal.span {(p : ℤ)}).ramificationIdx' q = 1`. Assume the negation of the conclusion as `hne1`.

Use `h2 ?_` and prove the remaining obligations. Use `(Ideal.ramificationIdx'_ne_one_iff (by` as an intermediate fact. Rewrite using `[Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]`. Simplify using `using hpq)).1 hne1`. Rewrite `this` using `[Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]`.

Simplify using `using this`. Establish `hf : (Ideal.span {(p : ℤ)}).inertiaDeg' q = 1`. Establish `h1` using `Ideal.absNorm_eq_pow_inertiaDeg' q hp`. Rewrite `h1` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, hc]`. Conclude with `(Nat.pow_right_injective hp.two_le (by simpa using h1)).symm`.

Rewrite using `[he, hf]`.
-/
theorem ncard_primesOver_of_split (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F)).ncard = Module.finrank ℚ F := by
  classical
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp'.ne_zero).mpr hp'
  have hne : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simpa using hp.ne_zero
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  have hs := Ideal.sum_ramification_inertia (𝓞 F) ℚ F (p := Ideal.span {(p : ℤ)}) hne
  rw [← hs, ← IsDedekindDomain.coe_primesOverFinset hne, Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hne] at hq
  haveI := hq.1
  haveI := hq.2
  have hpq : (p : 𝓞 F) ∈ q := by
    simpa using (Ideal.mem_of_liesOver q (Ideal.span {(p : ℤ)}) (p : ℤ)).1 (Ideal.mem_span_singleton_self _)
  obtain ⟨h2, hc⟩ := unram_card_of_split (E := E) hp h q hpq
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' q = 1 := by
    by_contra hne1
    refine h2 ?_
    have := (Ideal.ramificationIdx'_ne_one_iff (by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; simpa using hpq)).1 hne1
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem] at this
    simpa using this
  have hf : (Ideal.span {(p : ℤ)}).inertiaDeg' q = 1 := by
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' q hp
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hc] at h1
    exact (Nat.pow_right_injective hp.two_le (by simpa using h1)).symm
  rw [he, hf]

end Descent

/- English proof (translation)
Use `letI := D.host.cmStar`. Establish `h1` using `Module.finrank_mul_finrank ℚ D.host.F D.host.E`. Rewrite `h1` using `[D.sp.cm.deg2, finrank_host D]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_F (D : D7) : Module.finrank ℚ D.host.F = D.R.f := by
  letI := D.host.cmStar
  have h1 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [D.sp.cm.deg2, finrank_host D] at h1
  omega

/- English proof (translation)
Take `⟨hp, h⟩` from `h`. Rewrite `h` using `[GlobalTheory.HostSplit.ncard_placesOver _ hp]`. Use `⟨?_, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h1` using `ncard_primesOver_of_split (F := D.host.F) hp h`. Rewrite `h1` using `[← GlobalTheory.HostSplit.ncard_placesOver _ hp, finrank_F]`.

Rewrite using `[← h1, ← Nat.card_coe_set_eq]`. Both sides reduce to the same expression. Use `haveI := v.isPrime`. Conclude with `(unram_card_of_split hp h v.asIdeal hv).2`.
-/
theorem splitsF_of_splitsCompletely (D : D7) {p : ℕ} (h : SplitsCompletely D.host.E p) : SplitsF D p := by
  obtain ⟨hp, h⟩ := h
  rw [GlobalTheory.HostSplit.ncard_placesOver _ hp] at h
  refine ⟨?_, fun v hv => ?_⟩
  · have h1 := ncard_primesOver_of_split (F := D.host.F) hp h
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp, finrank_F] at h1
    rw [← h1, ← Nat.card_coe_set_eq]
    rfl
  · haveI := v.isPrime
    exact (unram_card_of_split hp h v.asIdeal hv).2

/- English proof (translation)
Take `⟨π, -, hn, hm⟩` from `D.T_norm u`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 hm`. Establish `hq8 : D.host.q % 8 = 3` using `D.host.hyp.2.2.1`. Establish `hd16 : D.host.d % 16 = 7` using `D.host.hyp.2.2.2.1`. Establish `hn0 : 1 ≤ D.host.QS` using `D.host.QS_pos`.

Take `⟨M, hM⟩ : ∃ M : ℕ, M = D.host.QS * D.host.q * D.host.d` from `⟨_, rfl⟩`. Establish `hM1 : 1 < M`. Establish `h1 : 1 * 3 * 7 ≤ D.host.QS * D.host.q * D.host.d` using `Nat.mul_le_mul (Nat.mul_le_mul hn0 (by omega)) (by omega)`. Use linear arithmetic over natural numbers and integers. Rewrite `ha`, the goal using `[← hM]`.

Take `⟨G, hG⟩ : ∃ G : ℕ, G = (D.host.g 0 * D.host.g 1) ^ 2` from `⟨_, rfl⟩`. Rewrite `ha` using `[← hG]`. Use `set y : D.host.E := (a : D.host.E) * G with hy`. Establish `hyi : IsIntegral ℤ y` using `(RingOfIntegers.isIntegral_coe a).mul (isIntegral_natCast G)`. Establish `hπ : (π : D.host.E) = 1 + M * y`.

Use `congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) ha` as an intermediate fact. Simplify using `only [map_mul, map_sub, map_one, map_natCast] at this`. Rewrite using `[hy]`. Move the coercions through the operations in `at this ⊢`. Take the linear combination `-this`.

Establish `hci : IsIntegral ℤ (D.conjF y)` using `hyi.map (D.conjF.toRingHom.toIntAlgHom)`. Rewrite `hn` using `[← D.conjF_eq, hπ, map_add, map_mul, map_one, map_natCast]`. Use `set z : D.host.E := y + D.conjF y + M * (y * D.conjF y) with hz`. Establish `hzi : IsIntegral ℤ z` using `(hyi.add hci).add ((isIntegral_natCast (R := ℤ) (B := D.host.E) M).mul (hyi.mul hci))`. Establish `hM0 : (M : ℚ) ≠ 0` using `by exact_mod_cast (by omega : M ≠ 0)`.

Establish `h4 : z = algebraMap ℚ D.host.E ((((D.mem u).A.T : ℚ) - 1) / M)`. Establish `hM0' : (M : D.host.E) ≠ 0` using `by exact_mod_cast (by omega : M ≠ 0)`. Rewrite using `[map_div₀, map_sub, map_one, map_natCast, map_natCast, eq_div_iff hM0', hz]`. Take the linear combination `hn`. Rewrite `hzi` using `[h4, isIntegral_algebraMap_iff (algebraMap ℚ D.host.E).injective]`.

Take `⟨n, hn'⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hzi`. Establish `h5 : (((D.mem u).A.T : ℤ) : ℚ) = ((1 + M * n : ℤ) : ℚ)`. Establish `: (n : ℚ) = (((D.mem u).A.T : ℚ) - 1) / M` using `by simpa using hn'`. Use `push_cast`. Rewrite using `[this]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h6 : ((D.mem u).A.T : ℤ) = 1 + M * n` using `by exact_mod_cast h5`. Establish `h7 : (((D.mem u).A.T % M : ℕ) : ℤ) = 1`. Rewrite using `[Int.natCast_mod, h6, Int.add_mul_emod_self_left]`.

Conclude with `Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hM1)`. Conclude with `h7` after adjusting the coercions.
-/
theorem levelPrime_mod (D : D7) (u : D.what₂.Word) :
    (D.mem u).A.T % (D.host.QS * D.host.q * D.host.d) = 1 := by
  obtain ⟨π, -, hn, hm⟩ := D.T_norm u
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hm
  have hq8 : D.host.q % 8 = 3 := D.host.hyp.2.2.1
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hn0 : 1 ≤ D.host.QS := D.host.QS_pos
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = D.host.QS * D.host.q * D.host.d := ⟨_, rfl⟩
  have hM1 : 1 < M := by
    have h1 : 1 * 3 * 7 ≤ D.host.QS * D.host.q * D.host.d :=
      Nat.mul_le_mul (Nat.mul_le_mul hn0 (by omega)) (by omega)
    omega
  rw [← hM] at ha ⊢
  obtain ⟨G, hG⟩ : ∃ G : ℕ, G = (D.host.g 0 * D.host.g 1) ^ 2 := ⟨_, rfl⟩
  rw [← hG] at ha
  set y : D.host.E := (a : D.host.E) * G with hy
  have hyi : IsIntegral ℤ y := (RingOfIntegers.isIntegral_coe a).mul (isIntegral_natCast G)
  have hπ : (π : D.host.E) = 1 + M * y := by
    have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) ha
    simp only [map_mul, map_sub, map_one, map_natCast] at this
    rw [hy]
    push_cast at this ⊢
    linear_combination -this
  have hci : IsIntegral ℤ (D.conjF y) := hyi.map (D.conjF.toRingHom.toIntAlgHom)
  rw [← D.conjF_eq, hπ, map_add, map_mul, map_one, map_natCast] at hn
  set z : D.host.E := y + D.conjF y + M * (y * D.conjF y) with hz
  have hzi : IsIntegral ℤ z :=
    (hyi.add hci).add ((isIntegral_natCast (R := ℤ) (B := D.host.E) M).mul (hyi.mul hci))
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have h4 : z = algebraMap ℚ D.host.E ((((D.mem u).A.T : ℚ) - 1) / M) := by
    have hM0' : (M : D.host.E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
    rw [map_div₀, map_sub, map_one, map_natCast, map_natCast, eq_div_iff hM0', hz]
    linear_combination hn
  rw [h4, isIntegral_algebraMap_iff (algebraMap ℚ D.host.E).injective] at hzi
  obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi
  have h5 : (((D.mem u).A.T : ℤ) : ℚ) = ((1 + M * n : ℤ) : ℚ) := by
    have : (n : ℚ) = (((D.mem u).A.T : ℚ) - 1) / M := by simpa using hn'
    push_cast
    rw [this]
    field_simp
    ring
  have h6 : ((D.mem u).A.T : ℤ) = 1 + M * n := by exact_mod_cast h5
  have h7 : (((D.mem u).A.T % M : ℕ) : ℤ) = 1 := by
    rw [Int.natCast_mod, h6, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hM1)
  exact_mod_cast h7

/- English proof (translation)
Assemble the required witnesses or components as `⟨(D.mem u).A.T_prime, (GlobalTheory.HostSplit.split_of_one_mod D.R D.host _ (D.mem u).A.T_prime (levelPrime_mod D u)).1⟩`.
-/
theorem levelPrime_splitsCompletely_in_cmField (D : D7) (u : D.what₂.Word) : SplitsCompletely D.host.E (D.mem u).A.T :=
  ⟨(D.mem u).A.T_prime,
    (GlobalTheory.HostSplit.split_of_one_mod D.R D.host _ (D.mem u).A.T_prime (levelPrime_mod D u)).1⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => splitsCompletely_g D i, splitsF_of_splitsCompletely D⟩`.
-/
theorem split_g_iff (D : D7) (i : Fin 2) :
    SplitsF D (D.host.g i) ↔ SplitsCompletely D.host.E (D.host.g i) :=
  ⟨fun _ => splitsCompletely_g D i, splitsF_of_splitsCompletely D⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => levelPrime_splitsCompletely_in_cmField D u, splitsF_of_splitsCompletely D⟩`.
-/
theorem split_T_iff (D : D7) (u : D.what₂.Word) :
    SplitsF D (D.mem u).A.T ↔ SplitsCompletely D.host.E (D.mem u).A.T :=
  ⟨fun _ => levelPrime_splitsCompletely_in_cmField D u, splitsF_of_splitsCompletely D⟩

def BothBig (D : D7) : Prop := ∀ i : Fin 2, 2 * D.R.f * D.R.k + 1 < D.host.g i

/- English proof (translation)
The claim follows from `exists_congr fun _ => by omega`.
-/
theorem gBig_iff (D : D7) : GBig D ↔ ∃ i : Fin 2, 2 * D.R.f * D.R.k + 1 < D.host.g i :=
  exists_congr fun _ => by omega

/- English proof (translation)
The claim follows from `(gBig_iff D).2 ⟨0, h 0⟩`.
-/
theorem gBig_of_bothBig {D : D7} (h : BothBig D) : GBig D := (gBig_iff D).2 ⟨0, h 0⟩

/- English proof (translation)
Introduce `i`. Establish `hc` using `D.ntypes.g_cond i`. Establish `hg` using `(D.host.g_prime i).two_le`. Establish `h3 : D.host.QS * D.host.q * D.host.d ≤ D.host.g i`. Assume the negation of the conclusion as `h`.

Rewrite `hc` using `[Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers. Take `⟨hq, hd⟩` from `D.host.qd_big`. Establish `hn : 1 ≤ D.host.QS` using `D.host.QS_pos`. Establish `hf : D.R.f ≤ D.R.k` using `D.R.f_le_k`.

Establish `hm` using `D.R.two_le_m`. Establish `ht` using `D.R.rank_add_five_le`. Establish `hr : D.R.k ≤ D.R.r` using `by unfold Ranks.r; omega`. Establish `h4 : D.R.f * D.R.k ≤ D.R.t * D.R.r` using `Nat.mul_le_mul (by omega) hr`. Establish `h5 : D.host.q ≤ D.host.QS * D.host.q * D.host.d`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `hq`, the goal using `[mul_assoc]`. Use linear arithmetic over natural numbers and integers.
-/
theorem bothBig_all (D : D7) : BothBig D := by
  intro i
  have hc := D.ntypes.g_cond i
  have hg := (D.host.g_prime i).two_le
  have h3 : D.host.QS * D.host.q * D.host.d ≤ D.host.g i := by
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega)] at hc
    omega
  obtain ⟨hq, hd⟩ := D.host.qd_big
  have hn : 1 ≤ D.host.QS := D.host.QS_pos
  have hf : D.R.f ≤ D.R.k := D.R.f_le_k
  have hm := D.R.two_le_m
  have ht := D.R.rank_add_five_le
  have hr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
  have h4 : D.R.f * D.R.k ≤ D.R.t * D.R.r := Nat.mul_le_mul (by omega) hr
  have h5 : D.host.q ≤ D.host.QS * D.host.q * D.host.d :=
    calc D.host.q = 1 * D.host.q * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ hn) (by omega)
  rw [mul_assoc] at hq ⊢
  omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => bothBig_all D, gBig_of_bothBig⟩`.
-/
theorem gBig_iff_bothBig (D : D7) : GBig D ↔ BothBig D :=
  ⟨fun _ => bothBig_all D, gBig_of_bothBig⟩

/- English proof (translation)
Unfold `ClassCount`. Rewrite using `[card_colClassSet]`.
-/
theorem classCount_iff (D : D7) (L : LevelData D) (u : D.what₂.Word) :
    ClassCount D L u ↔
      (Nat.card ((D.mem u).C.cls 0) : ℝ) =
        massI D D.R.k * idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f := by
  unfold ClassCount
  rw [card_colClassSet]

def ColumnClassNumberAt (D : D7) (L : LevelData D) : Prop :=
  ∀ u : D.what₂.Word, (∀ i : Fin 2, 2 * D.R.f * D.R.k + 1 < D.host.g i) →
    (∀ i : Fin 2, SplitsCompletely D.host.E (D.host.g i)) →
    SplitsCompletely D.host.E (D.mem u).A.T → ClassCount D L u

/- English proof (translation)
Unfold `ClassNumberFormula₂`. Simplify using `only [gBig_iff, split_g_iff, split_T_iff, classCount_iff]`. Conclude with `⟨fun h u h1 h2 h3 => h h1 h2 u h3, fun h h1 h2 u h3 => h u h1 h2 h3⟩`.
-/
theorem first_iff (D : D7) (L : LevelData D) :
    ClassNumberFormula₂ D L ↔ ∀ u : D.what₂.Word, (∃ i : Fin 2, 2 * D.R.f * D.R.k + 1 < D.host.g i) →
      (∀ i : Fin 2, SplitsCompletely D.host.E (D.host.g i)) →
      SplitsCompletely D.host.E (D.mem u).A.T → ClassCount D L u := by
  unfold ClassNumberFormula₂
  simp only [gBig_iff, split_g_iff, split_T_iff, classCount_iff]
  exact ⟨fun h u h1 h2 h3 => h h1 h2 u h3, fun h h1 h2 u h3 => h u h1 h2 h3⟩

/- English proof (translation)
Rewrite using `[first_iff]`. Conclude with `⟨fun h hb u _ h2 h3 => h u hb h2 h3, fun h u hb h2 h3 => h hb u ⟨0, hb 0⟩ h2 h3⟩`.
-/
theorem at_iff (D : D7) (L : LevelData D) : ColumnClassNumberAt D L ↔ (BothBig D → ClassNumberFormula₂ D L) := by
  rw [first_iff]
  exact ⟨fun h hb u _ h2 h3 => h u hb h2 h3, fun h u hb h2 h3 => h hb u ⟨0, hb 0⟩ h2 h3⟩

/- English proof (translation)
Rewrite using `[at_iff]`. Conclude with `⟨fun h _ => h, fun h hg => h (hs hg) hg⟩`.
-/
theorem iff_of_size {D : D7} (hs : GBig D → BothBig D) (L : LevelData D) :
    ClassNumberFormula₂ D L ↔ ColumnClassNumberAt D L := by
  rw [at_iff]
  exact ⟨fun h _ => h, fun h hg => h (hs hg) hg⟩

/- English proof (translation)
The claim follows from `iff_of_size (gBig_iff_bothBig D).1 L`.
-/
theorem full_at (D : D7) (L : LevelData D) : ClassNumberFormula₂ D L ↔ ColumnClassNumberAt D L :=
  iff_of_size (gBig_iff_bothBig D).1 L

/- English proof (translation)
The claim follows from `forall_congr' fun D => forall_congr' fun L => (full_at D L).symm`.
-/
theorem full : ColumnClassNumber ↔ ∀ (D : D7) (L : LevelData D), ClassNumberFormula₂ D L :=
  forall_congr' fun D => forall_congr' fun L => (full_at D L).symm

end GlobalTheory.ColClassCompare

end
