import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum

noncomputable section

namespace GlobalTheory.LevelUnram

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨I, hI⟩ : P ∣ Ideal.span {t} := by`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `ht`. Establish `hIP : ¬ I ≤ P`. Introduce `h`.

Apply `ht2` to reduce the goal to its premises. Rewrite using `[← Ideal.span_singleton_le_iff_mem, hI, sq]`. Conclude with `Ideal.mul_mono_right h`. Take `⟨s, hs, hsP⟩` from `SetLike.not_le_iff_exists.1 hIP`. Establish `h1 : a * s ∈ Ideal.span {t}` using `by rw [hI]; exact Ideal.mul_mem_mul ha hs`.

Take `⟨b, hb⟩` from `Ideal.mem_span_singleton.1 h1`. Conclude with `⟨s, b, hsP, by rw [mul_comm, hb]⟩`.
-/
theorem exists_mul_eq {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R) (hP : P.IsPrime) (t : R)
    (ht : t ∈ P) (ht2 : t ∉ P ^ 2) (a : R) (ha : a ∈ P) : ∃ s b, s ∉ P ∧ s * a = t * b := by
  obtain ⟨I, hI⟩ : P ∣ Ideal.span {t} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact ht
  have hIP : ¬ I ≤ P := by
    intro h
    apply ht2
    rw [← Ideal.span_singleton_le_iff_mem, hI, sq]
    exact Ideal.mul_mono_right h
  obtain ⟨s, hs, hsP⟩ := SetLike.not_le_iff_exists.1 hIP
  have h1 : a * s ∈ Ideal.span {t} := by rw [hI]; exact Ideal.mul_mem_mul ha hs
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 h1
  exact ⟨s, b, hsP, by rw [mul_comm, hb]⟩

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Set `e : 𝓞 E ≃+* 𝓞 E` to `RingEquiv.ofRingHom s s (RingHom.ext hs) (RingHom.ext hs)`. Set `e' : 𝓞 E ≃ₐ[ℤ] 𝓞 E` to `AlgEquiv.ofRingEquiv (f := e) (fun n => by simp)`. Rewrite using `[Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]`. Conclude with `congrArg Int.natAbs (Algebra.norm_eq_of_algEquiv e' a)`.
-/
theorem absNorm_span_invol (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) (a : 𝓞 E) :
    Ideal.absNorm (Ideal.span {s a}) = Ideal.absNorm (Ideal.span {a}) := by
  let e : 𝓞 E ≃+* 𝓞 E := RingEquiv.ofRingHom s s (RingHom.ext hs) (RingHom.ext hs)
  let e' : 𝓞 E ≃ₐ[ℤ] 𝓞 E := AlgEquiv.ofRingEquiv (f := e) (fun n => by simp)
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
  exact congrArg Int.natAbs (Algebra.norm_eq_of_algEquiv e' a)

/- English proof (translation)
Introduce `hmem`. Establish `hnorm : Ideal.absNorm (Ideal.span {a}) = p ^ Fintype.card ι`. Establish `h1 : Ideal.absNorm (Ideal.span {a}) ^ 2 = (p ^ Fintype.card ι) ^ 2`. Rewrite using `[← pow_mul, mul_comm, hcard, ← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast, ← ha, ← Ideal.span_singleton_mul_span_singleton, map_mul, absNorm_span_invol s hs, sq]`. Conclude with `Nat.pow_left_injective two_ne_zero h1`.

Establish `ha2 : a ∈ P i ^ 2`. Take `⟨y, m, hm, h⟩` from `(hmax i).exists_inv hsa`. Establish `h1 : a = y * (p : 𝓞 E) + m * a`. Rewrite using `[← ha]`. Take the linear combination `(-a) * h`.

Rewrite using `[h1]`. Use `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) ?_` and prove the remaining obligations. Rewrite using `[sq]`. Conclude with `Ideal.mul_mem_mul hm (haP i)`. Establish `hcop : ∀ j k, j ≠ k → IsCoprime (P j) (P k)` using `fun j k hjk => Ideal.isCoprime_iff_sup_eq.2 ((hmax j).coprime_of_ne (hmax k) (fun h => hjk (hinj h)))`.

Establish `hd1 : P i ^ 2 ∣ Ideal.span {a}`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `ha2`. Establish `hd2 : ∏ j ∈ Finset.univ.erase i, P j ∣ Ideal.span {a}`. Use `Finset.prod_dvd_of_coprime (fun j _ k _ hjk => hcop j k hjk) ?_` and prove the remaining obligations.

Introduce `j _`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `haP j`. Establish `hc : IsCoprime (P i ^ 2) (∏ j ∈ Finset.univ.erase i, P j)` using `IsCoprime.pow_left (IsCoprime.prod_right fun j hj => hcop i j (Finset.ne_of_mem_erase hj).symm)`. Establish `hd` using `map_dvd Ideal.absNorm (hc.mul_dvd hd1 hd2)`.

Rewrite `hd` using `[hnorm, map_mul, map_pow, map_prod, hN i, Finset.prod_congr rfl (fun j _ => hN j), Finset.prod_const, ← pow_add, Nat.pow_dvd_pow_iff_le_right hp.one_lt]`. Establish `h3` using `Finset.card_erase_add_one (Finset.mem_univ i)`. Rewrite `h3` using `[Finset.card_univ]`. Use linear arithmetic over natural numbers and integers.
-/
theorem notMem_sq {ι : Type} [Fintype ι] (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) (a : 𝓞 E) (p : ℕ) (hp : p.Prime)
    (ha : a * s a = (p : 𝓞 E)) (hcard : 2 * Fintype.card ι = Module.finrank ℚ E) (P : ι → Ideal (𝓞 E))
    (hmax : ∀ i, (P i).IsMaximal) (hinj : Function.Injective P) (haP : ∀ i, a ∈ P i)
    (hN : ∀ i, Ideal.absNorm (P i) = p) (i : ι) (hsa : s a ∉ P i) : (p : 𝓞 E) ∉ P i ^ 2 := by
  classical
  intro hmem
  have hnorm : Ideal.absNorm (Ideal.span {a}) = p ^ Fintype.card ι := by
    have h1 : Ideal.absNorm (Ideal.span {a}) ^ 2 = (p ^ Fintype.card ι) ^ 2 := by
      rw [← pow_mul, mul_comm, hcard, ← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast, ← ha,
        ← Ideal.span_singleton_mul_span_singleton, map_mul, absNorm_span_invol s hs, sq]
    exact Nat.pow_left_injective two_ne_zero h1
  have ha2 : a ∈ P i ^ 2 := by
    obtain ⟨y, m, hm, h⟩ := (hmax i).exists_inv hsa
    have h1 : a = y * (p : 𝓞 E) + m * a := by
      rw [← ha]
      linear_combination (-a) * h
    rw [h1]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) ?_
    rw [sq]
    exact Ideal.mul_mem_mul hm (haP i)
  have hcop : ∀ j k, j ≠ k → IsCoprime (P j) (P k) := fun j k hjk =>
    Ideal.isCoprime_iff_sup_eq.2 ((hmax j).coprime_of_ne (hmax k) (fun h => hjk (hinj h)))
  have hd1 : P i ^ 2 ∣ Ideal.span {a} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact ha2
  have hd2 : ∏ j ∈ Finset.univ.erase i, P j ∣ Ideal.span {a} := by
    refine Finset.prod_dvd_of_coprime (fun j _ k _ hjk => hcop j k hjk) ?_
    intro j _
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact haP j
  have hc : IsCoprime (P i ^ 2) (∏ j ∈ Finset.univ.erase i, P j) :=
    IsCoprime.pow_left (IsCoprime.prod_right fun j hj => hcop i j (Finset.ne_of_mem_erase hj).symm)
  have hd := map_dvd Ideal.absNorm (hc.mul_dvd hd1 hd2)
  rw [hnorm, map_mul, map_pow, map_prod, hN i,
    Finset.prod_congr rfl (fun j _ => hN j), Finset.prod_const, ← pow_add,
    Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
  have h3 := Finset.card_erase_add_one (Finset.mem_univ i)
  rw [Finset.card_univ] at h3
  omega

/- English proof (translation)
Use `letI := D.host.cmStar`. Establish `h1` using `Module.finrank_mul_finrank ℚ D.host.F D.host.E`. Establish `h2 : Module.finrank ℚ D.host.F = D.R.f`. Rewrite using `[D.host.finrank_hostF, Ranks.f, Ranks.n]`. Rewrite `h1` using `[D.sp.cm.deg2, h2]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_E (D : D7) : 2 * D.R.f = Module.finrank ℚ D.host.E := by
  letI := D.host.cmStar
  have h1 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  have h2 : Module.finrank ℚ D.host.F = D.R.f := by
    rw [D.host.finrank_hostF, Ranks.f, Ranks.n]
  rw [D.sp.cm.deg2, h2] at h1
  omega

/- English proof (translation)
Set `s : 𝓞 D.host.E →+* 𝓞 D.host.E` to `RingOfIntegers.mapRingHom (sigD D : D.host.E →+* D.host.E)`. Establish `hsc : ∀ x, (s x : D.host.E) = D.host.conj (x : D.host.E)` using `fun x => forms_involution_eq_host_conj _`. Establish `hs : ∀ x, s (s x) = x` using `fun x => RingOfIntegers.ext (by rw [hsc, hsc, host_conj_involutive])`. Establish `ha : A.piU * s A.piU = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E)`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Use `A.piU_norm` as an intermediate fact. Rewrite `this` using `[← hsc]`. Simplify using `using this`. Establish `hT0 : A.res v (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) = 0`. Rewrite using `[← ha, map_mul, A.res_pi, zero_mul]`.

Establish `h2` using `notMem_sq s hs A.piU _ (D.mem u).A.T_prime ha (by rw [(D.mem u).A.card_vT]; exact finrank_E D) (fun w => RingHom.ker (A.res w)) (fun w => RingHom.ker_isMaximal_of_surjective _ (A.res_surj w)) (fun w w' h => by`. Apply `A.eV.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`.

Establish `h' : RingHom.ker (A.res w) = RingHom.ker (A.res w')` using `h`. Rewrite using `[A.res_v, A.res_v, ← RingHom.mem_ker, ← RingHom.mem_ker, h'])`. Use the proof step `(fun w => A.res_pi w)`. Use the proof step `(fun w => by`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr (RingHom.quotientKerEquivOfSurjective (A.res_surj w)).toEquiv, Nat.card_eq_fintype_card, (D.mem u).A.card_Fv w])`.

Use `v (A.res_conj v _ (hsc _))`. Conclude with `⟨hT0, fun a h => exists_mul_eq _ (RingHom.ker_isPrime _) _ hT0 h2 a h⟩`.
-/
theorem unram (D : D7) (u : D.what₂.Word) (A : AtTTied u) (v : (D.mem u).A.vT) :
    Unram (A.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  let s : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (sigD D : D.host.E →+* D.host.E)
  have hsc : ∀ x, (s x : D.host.E) = D.host.conj (x : D.host.E) := fun x => forms_involution_eq_host_conj _
  have hs : ∀ x, s (s x) = x := fun x => RingOfIntegers.ext (by rw [hsc, hsc, host_conj_involutive])
  have ha : A.piU * s A.piU = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    have := A.piU_norm
    rw [← hsc] at this
    simpa using this
  have hT0 : A.res v (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) = 0 := by
    rw [← ha, map_mul, A.res_pi, zero_mul]
  have h2 := notMem_sq s hs A.piU _ (D.mem u).A.T_prime ha (by rw [(D.mem u).A.card_vT]; exact finrank_E D)
    (fun w => RingHom.ker (A.res w)) (fun w => RingHom.ker_isMaximal_of_surjective _ (A.res_surj w))
    (fun w w' h => by
      apply A.eV.injective
      apply Subtype.ext
      apply HeightOneSpectrum.ext
      ext x
      have h' : RingHom.ker (A.res w) = RingHom.ker (A.res w') := h
      rw [A.res_v, A.res_v, ← RingHom.mem_ker, ← RingHom.mem_ker, h'])
    (fun w => A.res_pi w)
    (fun w => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_congr (RingHom.quotientKerEquivOfSurjective (A.res_surj w)).toEquiv, Nat.card_eq_fintype_card,
        (D.mem u).A.card_Fv w])
    v (A.res_conj v _ (hsc _))
  exact ⟨hT0, fun a h => exists_mul_eq _ (RingHom.ker_isPrime _) _ hT0 h2 a h⟩

end GlobalTheory.LevelUnram

end
