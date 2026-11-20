import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.PrimeDiscriminants.CycImage
import Development.AutomorphicArithmetic.PrimeDiscriminants.RamDiscr

open NumberField

namespace UpperTheory.Ram

open Formalism.L2.Host Formalism.HC Formalism.HC.Der Formalism.FrobeniusOrbits

/- English proof (translation)
Use `haveI : NeZero N := ⟨hN.ne'⟩`. Take `⟨w, hw⟩ : ∃ w : Qb, IsPrimitiveRoot w N` from `HasEnoughRootsOfUnity.exists_primitiveRoot Qb N`. Establish `hw' : IsPrimitiveRoot (w ^ u) N` using `hw.pow_of_coprime u hu`. Establish `hc : IsConjRoot ℚ (w ^ u) w`. Unfold `IsConjRoot`.

Rewrite using `[← Polynomial.cyclotomic_eq_minpoly_rat hw hN, ← Polynomial.cyclotomic_eq_minpoly_rat hw' hN]`. Use `haveI : IsAlgClosure ℚ Qb := AlgebraicClosure.instIsAlgClosure ℚ`. Use `haveI : Normal ℚ Qb := IsAlgClosure.normal ℚ Qb`. Take `⟨s, hs⟩` from `hc.exists_algEquiv`. Use `⟨s, fun z hz => ?_⟩` and prove the remaining obligations.

Take `⟨i, -, rfl⟩` from `hw.eq_pow_of_pow_eq_one hz`. Rewrite using `[map_pow, hs, ← pow_mul, ← pow_mul, mul_comm]`.
-/
private theorem exists_aut_pow (N : ℕ) (hN : 0 < N) (u : ℕ) (hu : u.Coprime N) :
    ∃ s : Qb ≃ₐ[ℚ] Qb, ∀ z ∈ mus N, s z = z ^ u := by
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨w, hw⟩ : ∃ w : Qb, IsPrimitiveRoot w N := HasEnoughRootsOfUnity.exists_primitiveRoot Qb N
  have hw' : IsPrimitiveRoot (w ^ u) N := hw.pow_of_coprime u hu
  have hc : IsConjRoot ℚ (w ^ u) w := by
    unfold IsConjRoot
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hw hN, ← Polynomial.cyclotomic_eq_minpoly_rat hw' hN]
  haveI : IsAlgClosure ℚ Qb := AlgebraicClosure.instIsAlgClosure ℚ
  haveI : Normal ℚ Qb := IsAlgClosure.normal ℚ Qb
  obtain ⟨s, hs⟩ := hc.exists_algEquiv
  refine ⟨s, fun z hz => ?_⟩
  obtain ⟨i, -, rfl⟩ := hw.eq_pow_of_pow_eq_one hz
  rw [map_pow, hs, ← pow_mul, ← pow_mul, mul_comm]

/- English proof (translation)
Establish `huM : u.Coprime M`. Unfold `Nat.Coprime`. Rewrite using `[hu1.gcd_eq, Nat.gcd_one_left]`. Take `⟨s, hs⟩` from `exists_aut_pow (N * M) (Nat.mul_pos hN hM) u (Nat.Coprime.mul_right hu huM)`. Use `⟨s, fun z hz => hs z ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Use `show z ^ (N * M) = 1`. Rewrite using `[pow_mul, show z ^ N = 1 from hz, one_pow]`. Unfold `cycQ at hx`. Proceed by induction on `hx using IntermediateField.adjoin_induction with`. Consider the case `mem z hz`.

Establish `hz' : z ^ M = 1` using `hz`. Rewrite using `[hs z (by show z ^ (N * M) = 1; rw [mul_comm, pow_mul, hz', one_pow]), pow_eq_pow_of_modEq hu1 hz', pow_one]`. Consider the case `algebraMap r => exact s.commutes r`. Consider the case `add a b _ _ ha hb => rw [map_add, ha, hb]`. Consider the case `inv a _ ha => rw [map_inv₀, ha]`.

Consider the case `mul a b _ _ ha hb => rw [map_mul, ha, hb]`.
-/
private theorem exists_aut_fix (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (u : ℕ) (hu : u.Coprime N)
    (hu1 : u ≡ 1 [MOD M]) :
    ∃ s : Qb ≃ₐ[ℚ] Qb, (∀ z ∈ mus N, s z = z ^ u) ∧ ∀ x ∈ cycQ M, s x = x := by
  have huM : u.Coprime M := by
    unfold Nat.Coprime
    rw [hu1.gcd_eq, Nat.gcd_one_left]
  obtain ⟨s, hs⟩ := exists_aut_pow (N * M) (Nat.mul_pos hN hM) u (Nat.Coprime.mul_right hu huM)
  refine ⟨s, fun z hz => hs z ?_, fun x hx => ?_⟩
  · show z ^ (N * M) = 1
    rw [pow_mul, show z ^ N = 1 from hz, one_pow]
  · unfold cycQ at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem z hz =>
      have hz' : z ^ M = 1 := hz
      rw [hs z (by show z ^ (N * M) = 1; rw [mul_comm, pow_mul, hz', one_pow]),
        pow_eq_pow_of_modEq hu1 hz', pow_one]
    | algebraMap r => exact s.commutes r
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | inv a _ ha => rw [map_inv₀, ha]
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]

/- English proof (translation)
Set `_ : Algebra H.E (Cond.Cyc H.condN)` to `(emb H).toRingHom.toAlgebra`. Establish `: IsScalarTower ℚ H.E (Cond.Cyc H.condN)` using `IsScalarTower.of_algebraMap_eq fun x => ((emb H).commutes x).symm`. Establish `: Algebra.IsAlgebraic H.E (Cond.Cyc H.condN)` using `Algebra.IsAlgebraic.tower_top (K := ℚ) H.E`. Set `_ : Algebra H.E Qb` to `j.toRingHom.toAlgebra`. Set `Ψ0 : Cond.Cyc H.condN →ₐ[H.E] Qb` to `IsAlgClosed.lift`.

Set `Ψ : Cond.Cyc H.condN →+* Qb` to `Ψ0.toRingHom`. Establish `h1 : ∀ y, Ψ (emb H y) = j y` using `fun y => Ψ0.commutes y`. Establish `key : (Ψ.comp (tauN H.condN u : Cond.Cyc H.condN →+* Cond.Cyc H.condN)).toRatAlgHom = ((s : Qb →+* Qb).comp Ψ).toRatAlgHom`. Use `AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top (Cond.z_spec H.condN)) ?_` and prove the remaining obligations. Introduce `y hy`.

Rewrite `hy` using `[Set.mem_singleton_iff]`. Substitute `hy` using the available equality. Use `show Ψ (tauN H.condN u (Cond.z H.condN)) = s (Ψ (Cond.z H.condN))`. Establish `hz` using `(Cond.z_spec H.condN).pow_eq_one`. Rewrite using `[tauN_root H.condN _ _ hz, map_pow, hs _ (show _ ^ H.condN = 1 by rw [← map_pow, hz, map_one])]`.

Rewrite using `[← h1, ← h1, emb_art]`. Conclude with `(DFunLike.congr_fun key (emb H x)).symm`.
-/
private theorem aut_art {φ : Frame} (H : HostRaw φ) (j : H.E →ₐ[ℚ] Qb) (u : (ZMod H.condN)ˣ) (s : Qb ≃ₐ[ℚ] Qb)
    (hs : ∀ z ∈ mus H.condN, s z = z ^ (u : ZMod H.condN).val) (x : H.E) :
    s (j x) = j (H.gal.symm (H.art u) x) := by
  let _ : Algebra H.E (Cond.Cyc H.condN) := (emb H).toRingHom.toAlgebra
  have : IsScalarTower ℚ H.E (Cond.Cyc H.condN) := IsScalarTower.of_algebraMap_eq fun x => ((emb H).commutes x).symm
  have : Algebra.IsAlgebraic H.E (Cond.Cyc H.condN) := Algebra.IsAlgebraic.tower_top (K := ℚ) H.E
  let _ : Algebra H.E Qb := j.toRingHom.toAlgebra
  let Ψ0 : Cond.Cyc H.condN →ₐ[H.E] Qb := IsAlgClosed.lift
  let Ψ : Cond.Cyc H.condN →+* Qb := Ψ0.toRingHom
  have h1 : ∀ y, Ψ (emb H y) = j y := fun y => Ψ0.commutes y
  have key : (Ψ.comp (tauN H.condN u : Cond.Cyc H.condN →+* Cond.Cyc H.condN)).toRatAlgHom =
      ((s : Qb →+* Qb).comp Ψ).toRatAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top (Cond.z_spec H.condN)) ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show Ψ (tauN H.condN u (Cond.z H.condN)) = s (Ψ (Cond.z H.condN))
    have hz := (Cond.z_spec H.condN).pow_eq_one
    rw [tauN_root H.condN _ _ hz, map_pow, hs _ (show _ ^ H.condN = 1 by rw [← map_pow, hz, map_one])]
  rw [← h1, ← h1, emb_art]
  exact (DFunLike.congr_fun key (emb H x)).symm

/- English proof (translation)
Break down `(H.toHostRaw.dvd_condN_iff hl).1 hd with h | rfl | rfl` into its components or cases. Conclude with `H.QS_exact l hl h`. Establish `hN : H.condN = H.QS * H.d * H.q` using `mul_right_comm _ _ _`. Take `⟨b, hb, hj⟩` from `D7.exists_sign H.q_prime H.q_mod_four (-1)`. Take `⟨n, hn1, hn2⟩` from `Nat.chineseRemainder H.toHostRaw.coprime_QSd_q 1 b`.

Take `⟨u, hu⟩` from `exists_unit_modEq (dvd_refl H.condN) n (hN ▸ Nat.Coprime.mul_right (hn1.gcd_eq.trans (Nat.coprime_one_left _)) (hn2.gcd_eq.trans hb))`. Use `⟨u, ?_, fun h3 => ?_⟩` and prove the remaining obligations. Rewrite using `[show H.condN / H.q = H.QS * H.d by rw [hN, Nat.mul_div_cancel _ hl.pos]]`. Conclude with `(hu.of_dvd ⟨H.q, hN⟩).trans hn1`. Establish `h4` using `H.flPS u`.

Rewrite `h4` using `[h3, D7.jac_congr ((hu.of_dvd H.toHostRaw.q_dvd_condN).trans hn2), hj]`. Conclude with `absurd h4 (show ¬ ((1 : ℤˣ) : ℤ) = ((-1 : ℤˣ) : ℤ) by decide)`. Take `⟨u, h1, h2⟩` from `exists_art_iod H.toHostRaw`. Use `⟨u, ?_, fun h3 => R.toFrame.iod_ne_one (h2.symm.trans h3)⟩` and prove the remaining obligations. Rewrite using `[show H.condN / H.d = H.QS * H.q from Nat.mul_div_cancel _ hl.pos]` and apply the resulting hypothesis.
-/
private theorem exists_exact {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) {l : ℕ} (hl : l.Prime) (hd : l ∣ H.condN) :
    ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.condN / l] ∧ H.art u ≠ 1 := by
  rcases (H.toHostRaw.dvd_condN_iff hl).1 hd with h | rfl | rfl
  · exact H.QS_exact l hl h
  · have hN : H.condN = H.QS * H.d * H.q := mul_right_comm _ _ _
    obtain ⟨b, hb, hj⟩ := D7.exists_sign H.q_prime H.q_mod_four (-1)
    obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder H.toHostRaw.coprime_QSd_q 1 b
    obtain ⟨u, hu⟩ := exists_unit_modEq (dvd_refl H.condN) n
      (hN ▸ Nat.Coprime.mul_right (hn1.gcd_eq.trans (Nat.coprime_one_left _)) (hn2.gcd_eq.trans hb))
    refine ⟨u, ?_, fun h3 => ?_⟩
    · rw [show H.condN / H.q = H.QS * H.d by rw [hN, Nat.mul_div_cancel _ hl.pos]]
      exact (hu.of_dvd ⟨H.q, hN⟩).trans hn1
    · have h4 := H.flPS u
      rw [h3, D7.jac_congr ((hu.of_dvd H.toHostRaw.q_dvd_condN).trans hn2), hj] at h4
      exact absurd h4 (show ¬ ((1 : ℤˣ) : ℤ) = ((-1 : ℤˣ) : ℤ) by decide)
  · obtain ⟨u, h1, h2⟩ := exists_art_iod H.toHostRaw
    refine ⟨u, ?_, fun h3 => R.toFrame.iod_ne_one (h2.symm.trans h3)⟩
    rwa [show H.condN / H.d = H.QS * H.q from Nat.mul_div_cancel _ hl.pos]

end UpperTheory.Ram

/- English proof (translation)
Introduce `R H j`. Establish `hN : 0 < H.condN` using `Nat.pos_of_ne_zero H.toHostRaw.condN_ne_zero`. Use `⟨?_, fun M hM hle => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `H.toHostRaw.image_mem_of_roots j.toRingHom (Formalism.L2.Host.cycQ H.condN).toSubfield (fun y hy => IntermediateField.subset_adjoin ℚ _ hy) x`.

Assume the negation of the conclusion as `hn`. Take `⟨k, hk⟩` from `Nat.gcd_dvd_left H.condN M`. Establish `hk1 : k ≠ 1`. Introduce and unpack `rfl`. Rewrite `hk` using `[mul_one]`.

Conclude with `hn (hk ▸ Nat.gcd_dvd_right _ _)`. Take `⟨l, hl, m, rfl⟩` from `Nat.exists_prime_and_dvd hk1`. Establish `hld : l ∣ H.condN` using `⟨Nat.gcd H.condN M * m, hk.trans (by ring)⟩`. Establish `hg : Nat.gcd H.condN M ∣ H.condN / l` using `⟨m, Nat.div_eq_of_eq_mul_right hl.pos (hk.trans (by ring))⟩`. Take `⟨u, hu1, hu2⟩` from `exists_exact H hl hld`.

Take `⟨n, hn1, hn2⟩` from `Nat.chineseRemainder' (hu1.of_dvd hg)`. Take `⟨s, hs1, hs2⟩` from `exists_aut_fix H.condN M hN hM n (hn1.gcd_eq.trans (ZMod.val_coe_unit_coprime u)) hn2`. Apply `hu2` to reduce the goal to its premises. Rewrite using `[← H.gal.symm.map_eq_one_iff]`. Use `AlgEquiv.ext fun x => j.injective ?_` and prove the remaining obligations.

Establish `h` using `aut_art H.toHostRaw j u s (fun z hz => by rw [hs1 z hz, pow_eq_pow_of_modEq hn1 hz]) x`. Conclude with `h.symm.trans (hs2 _ (hle ⟨x, rfl⟩))`.
-/
theorem UpperTheory.Ram.isCond_condN :
    ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (j : H.E →ₐ[ℚ] Formalism.L2.Host.Qb),
      Formalism.L2.Host.IsCond j.fieldRange H.condN := by
  intro R H j
  have hN : 0 < H.condN := Nat.pos_of_ne_zero H.toHostRaw.condN_ne_zero
  refine ⟨?_, fun M hM hle => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact H.toHostRaw.image_mem_of_roots j.toRingHom (Formalism.L2.Host.cycQ H.condN).toSubfield
      (fun y hy => IntermediateField.subset_adjoin ℚ _ hy) x
  · by_contra hn
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left H.condN M
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [mul_one] at hk
      exact hn (hk ▸ Nat.gcd_dvd_right _ _)
    obtain ⟨l, hl, m, rfl⟩ := Nat.exists_prime_and_dvd hk1
    have hld : l ∣ H.condN := ⟨Nat.gcd H.condN M * m, hk.trans (by ring)⟩
    have hg : Nat.gcd H.condN M ∣ H.condN / l :=
      ⟨m, Nat.div_eq_of_eq_mul_right hl.pos (hk.trans (by ring))⟩
    obtain ⟨u, hu1, hu2⟩ := exists_exact H hl hld
    obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder' (hu1.of_dvd hg)
    obtain ⟨s, hs1, hs2⟩ := exists_aut_fix H.condN M hN hM n
      (hn1.gcd_eq.trans (ZMod.val_coe_unit_coprime u)) hn2
    apply hu2
    rw [← H.gal.symm.map_eq_one_iff]
    refine AlgEquiv.ext fun x => j.injective ?_
    have h := aut_art H.toHostRaw j u s (fun z hz => by rw [hs1 z hz, pow_eq_pow_of_modEq hn1 hz]) x
    exact h.symm.trans (hs2 _ (hle ⟨x, rfl⟩))
