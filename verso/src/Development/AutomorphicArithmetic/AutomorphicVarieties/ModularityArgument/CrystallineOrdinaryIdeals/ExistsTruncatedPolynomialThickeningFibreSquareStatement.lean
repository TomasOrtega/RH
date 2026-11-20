import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `E B _ _ _ _ π hπ J`. Use `haveI : IsArtinianRing B := IsArtinianRing.of_finite E B`. Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : IsNilpotent (RingHom.ker (π : B →+* E)) := by`. Rewrite using `[Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]`. Introduce `c hc`.

Conclude with `mem_nilradical.mpr (hπ c (by simpa using hc))`. Use `set I := RingHom.ker (π : B →+* E) with hIdef`. Use `set N := J * e + 1 with hN`. Establish `hN0 : N ≠ 0` using `by omega`. Use `haveI : Module.Finite E (AdjoinRoot ((X : E[X]) ^ N)) := (AdjoinRoot.powerBasis' (monic_X_pow N)).finite`.

Use `haveI : Module.Finite B (AdjoinRoot ((X : B[X]) ^ N)) := (AdjoinRoot.powerBasis' (monic_X_pow N)).finite`. Use `haveI : Module.Finite E (AdjoinRoot ((X : B[X]) ^ N)) := Module.Finite.trans B _`. Establish `hrootE : (AdjoinRoot.root ((X : E[X]) ^ N)) ^ N = 0`. Rewrite using `[← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]`. Establish `hrootB : (AdjoinRoot.root ((X : B[X]) ^ N)) ^ N = 0`.

Rewrite using `[← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]`. Set `πC : AdjoinRoot ((X : E[X]) ^ N) →ₐ[E] E` to `AdjoinRoot.liftAlgHom _ (AlgHom.id E E) 0 (by simp [hN0])`. Set `p1 : AdjoinRoot ((X : B[X]) ^ N) →ₐ[E] B` to `AdjoinRoot.liftAlgHom _ (AlgHom.id E B) 0 (by simp [hN0])`. Set `p2 : AdjoinRoot ((X : B[X]) ^ N) →ₐ[E] AdjoinRoot ((X : E[X]) ^ N)` to `AdjoinRoot.liftAlgHom _ ((Algebra.ofId E _).comp π) (AdjoinRoot.root _) (by rw [eval₂_X_pow]; exact hrootE)`. Establish `hp1 : ∀ q : B[X], p1 (AdjoinRoot.mk _ q) = q.coeff 0`.

Introduce `q`. Simplify using `[p1, AdjoinRoot.liftAlgHom_mk, eval₂_at_zero]`. Establish `hp1of : ∀ b : B, p1 (AdjoinRoot.of _ b) = b` using `fun b => AdjoinRoot.liftAlgHom_of _ _ _ _ _`. Establish `hπC : ∀ q : E[X], πC (AdjoinRoot.mk _ q) = q.coeff 0`. Introduce `q`.

Simplify using `[πC, AdjoinRoot.liftAlgHom_mk, eval₂_at_zero]`. Establish `hp2 : ∀ q : B[X], p2 (AdjoinRoot.mk _ q) = AdjoinRoot.mk _ (q.map (π : B →+* E))`. Introduce `q`. Rewrite using `[AdjoinRoot.liftAlgHom_mk, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map]`. Both sides reduce to the same expression.

Establish `hp2root : p2 (AdjoinRoot.root _) = AdjoinRoot.root _` using `AdjoinRoot.liftAlgHom_root _ _ _ _`. Establish `hp2map : ∀ q : E[X], p2 (AdjoinRoot.mk _ (q.map (algebraMap E B))) = AdjoinRoot.mk _ q`. Introduce `q`. Rewrite using `[hp2, Polynomial.map_map]`. Use `congr 1`.

Use `conv_rhs => rw [← Polynomial.map_id (p := q)]`. Use `congr 1`. Use extensionality with `r`. Simplify using the standard rewrite rules. Establish `hnilT : ∀ a, π (p1 a) = 0 → IsNilpotent a`.

Introduce `a ha`. Take `⟨q, rfl⟩` from `AdjoinRoot.mk_surjective a`. Rewrite `ha` using `[hp1]`. Take `⟨r, hr⟩ : X ∣ q - C (q.coeff 0)` from `X_dvd_iff.mpr (by simp)`. Establish `hq : q = C (q.coeff 0) + X * r` using `by rw [← hr]; ring`.

Rewrite using `[hq, map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C]`. Conclude with `Commute.isNilpotent_add (Commute.all _ _) ((hπ _ ha).map _) ⟨N, by rw [mul_pow, hrootB, zero_mul]⟩`. Establish `hnilC : ∀ a, πC a = 0 → IsNilpotent a`. Introduce `a ha`. Take `⟨q, rfl⟩` from `AdjoinRoot.mk_surjective a`.

Rewrite `ha` using `[hπC]`. Take `⟨r, rfl⟩` from `X_dvd_iff.mpr ha`. Conclude with `⟨N, by rw [map_mul, AdjoinRoot.mk_X, mul_pow, hrootE, zero_mul]⟩`. Establish `hcomm : π.comp p1 = πC.comp p2`. Use `AlgHom.ext fun a => ?_` and prove the remaining obligations.

Take `⟨q, rfl⟩` from `AdjoinRoot.mk_surjective a`. Simplify using `only [AlgHom.comp_apply, hp1, hp2, hπC, coeff_map]`. Both sides reduce to the same expression. Establish `hsurj : ∀ b c, π b = πC c → ∃ s, p1 s = b ∧ p2 s = c`. Introduce `b c hbc`.

Take `⟨q, rfl⟩` from `AdjoinRoot.mk_surjective c`. Rewrite `hbc` using `[hπC]`. Use `⟨AdjoinRoot.of _ b + AdjoinRoot.mk _ (q.map (algebraMap E B)) - AdjoinRoot.of _ (algebraMap E B (q.coeff 0)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_add, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C, hp1, hp1, hp1]`. Simplify using the standard rewrite rules.

Rewrite using `[map_sub, map_add, hp2map, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C, hp2, hp2]`. Simplify using `[hbc]`. Establish `hker : ∀ Q, p2 Q = 0 → Q ∈ I.map (AdjoinRoot.of ((X : B[X]) ^ N))`. Introduce `Q hQ`. Take `⟨q, rfl⟩` from `AdjoinRoot.mk_surjective Q`.

Rewrite `hQ` using `[hp2, AdjoinRoot.mk_eq_zero]`. Establish `hmod : (q %ₘ (X ^ N)).map (π : B →+* E) = 0`. Rewrite using `[map_modByMonic _ (monic_X_pow N), Polynomial.map_pow, map_X]`. Conclude with `(modByMonic_eq_zero_iff_dvd (monic_X_pow N)).mpr hQ`. Establish `hmk : AdjoinRoot.mk ((X : B[X]) ^ N) q = AdjoinRoot.mk _ (q %ₘ (X ^ N))` using `by conv_lhs => rw [← modByMonic_add_div q (X ^ N)]`.

Rewrite using `[map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]`. Rewrite using `[hmk]`. Establish `hin : q %ₘ (X ^ N) ∈ I.map (C : B →+* B[X])`. Rewrite using `[Ideal.mem_map_C_iff]`. Introduce `n`.

Rewrite using `[hIdef, RingHom.mem_ker]`. Use `congrArg (fun p => p.coeff n) hmod` as an intermediate fact. Simplify using `using this`. Use `Ideal.mem_map_of_mem (AdjoinRoot.mk ((X : B[X]) ^ N)) hin` as an intermediate fact. Rewrite `this` using `[Ideal.map_map]`.

Conclude with `this`. Use `⟨AdjoinRoot ((X : E[X]) ^ N), inferInstance, inferInstance, inferInstance, AdjoinRoot ((X : B[X]) ^ N), inferInstance, inferInstance, inferInstance, πC, p1, p2, AdjoinRoot.root _, ⟨N, hrootE⟩, hnilC, hnilT, hcomm, hsurj, ?_⟩` and prove the remaining obligations. Introduce `P y j v hj hP hPy`. Take `⟨qv, hqv⟩` from `AdjoinRoot.mk_surjective (v : AdjoinRoot ((X : E[X]) ^ N))`. Use `set V := AdjoinRoot.mk ((X : B[X]) ^ N) (qv.map (algebraMap E B)) with hVdef`.

Establish `hV : p2 V = v` using `by rw [hVdef, hp2map, hqv]`. Establish `hVu : IsUnit V`. Establish `hw : π (p1 V) ≠ 0`. Rewrite using `[← AlgHom.comp_apply, hcomm, AlgHom.comp_apply, hV]`. Conclude with `(v.isUnit.map πC).ne_zero`.

Establish `h1 : IsNilpotent (V - AdjoinRoot.of _ (algebraMap E B (π (p1 V))))`. Apply `hnilT` to reduce the goal to its premises. Rewrite using `[map_sub, map_sub, hp1of, AlgHom.commutes]`. Simplify using the standard rewrite rules. Establish `h2 : IsUnit (AdjoinRoot.of ((X : B[X]) ^ N) (algebraMap E B (π (p1 V))))` using `((Ne.isUnit hw).map (algebraMap E B)).map _`.

Use `h1.isUnit_add_left_of_commute h2 (Commute.all _ _)` as an intermediate fact. Simplify using `using this`. Take `⟨Vi, hVi⟩ : ∃ Vi, V * Vi = 1` from `hVu.exists_right_inv`. Use `set Q := P - AdjoinRoot.root ((X : B[X]) ^ N) ^ j * V with hQdef`. Establish `hQ2 : p2 Q = 0`.

Rewrite using `[hQdef, map_sub, map_mul, map_pow, hV, hP, hp2root, sub_self]`. Use `set K := I.map (AdjoinRoot.of ((X : B[X]) ^ N)) with hK`. Establish `hQK : Q ∈ K` using `hker Q hQ2`. Use `set R := -(Q * Vi) with hR`. Establish `hRK : R ∈ K` using `K.neg_mem (K.mul_mem_right _ hQK)`.

Establish `hxR : AdjoinRoot.root ((X : B[X]) ^ N) ^ j * y = R * y`. Rewrite using `[hR]`. Take the linear combination `(-(AdjoinRoot.root ((X : B[X]) ^ N) ^ j * y)) * hVi + Vi * hPy + (Vi * y) * hQdef`. Establish `hpow : ∀ k : ℕ, AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * y = R ^ k * y`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `hsplit : AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * (k + 1)) = AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * AdjoinRoot.root ((X : B[X]) ^ N) ^ j`. Rewrite using `[← pow_add]`.

Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsplit, mul_assoc]`. Use `_ = R * (AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * y) := by rw [hxR]; ring`. Use `_ = R ^ (k + 1) * y := by rw [ih]; ring`.

Establish `hRe : R ^ e = 0`. Establish `h3 : R ^ e ∈ K ^ e` using `Ideal.pow_mem_pow hRK e`. Rewrite `h3` using `[hK, ← Ideal.map_pow, he, Ideal.zero_eq_bot, Ideal.map_bot]`. Conclude with `(Ideal.mem_bot).1 h3`. Establish `hy0 : AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * e) * y = 0`.

Rewrite using `[hpow, hRe, zero_mul]`. Establish `hlt : j * e < N`. Use `Nat.mul_le_mul_right e hj` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨qy, rfl⟩` from `AdjoinRoot.mk_surjective y`.

Rewrite using `[hp1]`. Rewrite `hy0` using `[← AdjoinRoot.mk_X, ← map_pow, ← map_mul, AdjoinRoot.mk_eq_zero]`. Take `⟨s, hs⟩` from `hy0`. Establish `h4` using `congrArg (fun p => p.coeff (j * e)) hs`. Simplify using `only [coeff_X_pow_mul'] at h4`.

Simplify `h4` using `[Nat.not_le.mpr hlt]`.
-/
theorem _root_.GlobalTheory.T.exists_truncated_polynomial_thickening_fibre_square : ∀ {E B : Type} [Field E] [CommRing B] [Algebra E B] [Module.Finite E B] (π : B →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ J : ℕ, ∃ (C : Type) (_ : CommRing C) (_ : Algebra E C) (_ : Module.Finite E C) (T : Type) (_ : CommRing T) (_ : Algebra E T) (_ : Module.Finite E T) (πC : C →ₐ[E] E) (p₁ : T →ₐ[E] B) (p₂ : T →ₐ[E] C) (t : C), IsNilpotent t ∧ (∀ a, πC a = 0 → IsNilpotent a) ∧ (∀ a, π (p₁ a) = 0 → IsNilpotent a) ∧ π.comp p₁ = πC.comp p₂ ∧ (∀ b c, π b = πC c → ∃ s, p₁ s = b ∧ p₂ s = c) ∧ ∀ (P y : T) (j : ℕ) (v : Cˣ), j ≤ J → p₂ P = t ^ j * v → P * y = 0 → p₁ y = 0 := by
  intro E B _ _ _ _ π hπ J
  classical
  haveI : IsArtinianRing B := IsArtinianRing.of_finite E B
  obtain ⟨e, he⟩ : IsNilpotent (RingHom.ker (π : B →+* E)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro c hc
    exact mem_nilradical.mpr (hπ c (by simpa using hc))
  set I := RingHom.ker (π : B →+* E) with hIdef
  set N := J * e + 1 with hN
  have hN0 : N ≠ 0 := by omega
  haveI : Module.Finite E (AdjoinRoot ((X : E[X]) ^ N)) :=
    (AdjoinRoot.powerBasis' (monic_X_pow N)).finite
  haveI : Module.Finite B (AdjoinRoot ((X : B[X]) ^ N)) :=
    (AdjoinRoot.powerBasis' (monic_X_pow N)).finite
  haveI : Module.Finite E (AdjoinRoot ((X : B[X]) ^ N)) := Module.Finite.trans B _
  have hrootE : (AdjoinRoot.root ((X : E[X]) ^ N)) ^ N = 0 := by
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  have hrootB : (AdjoinRoot.root ((X : B[X]) ^ N)) ^ N = 0 := by
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  let πC : AdjoinRoot ((X : E[X]) ^ N) →ₐ[E] E :=
    AdjoinRoot.liftAlgHom _ (AlgHom.id E E) 0 (by simp [hN0])
  let p1 : AdjoinRoot ((X : B[X]) ^ N) →ₐ[E] B :=
    AdjoinRoot.liftAlgHom _ (AlgHom.id E B) 0 (by simp [hN0])
  let p2 : AdjoinRoot ((X : B[X]) ^ N) →ₐ[E] AdjoinRoot ((X : E[X]) ^ N) :=
    AdjoinRoot.liftAlgHom _ ((Algebra.ofId E _).comp π) (AdjoinRoot.root _)
      (by rw [eval₂_X_pow]; exact hrootE)
  have hp1 : ∀ q : B[X], p1 (AdjoinRoot.mk _ q) = q.coeff 0 := by
    intro q
    simp [p1, AdjoinRoot.liftAlgHom_mk, eval₂_at_zero]
  have hp1of : ∀ b : B, p1 (AdjoinRoot.of _ b) = b := fun b =>
    AdjoinRoot.liftAlgHom_of _ _ _ _ _
  have hπC : ∀ q : E[X], πC (AdjoinRoot.mk _ q) = q.coeff 0 := by
    intro q
    simp [πC, AdjoinRoot.liftAlgHom_mk, eval₂_at_zero]
  have hp2 : ∀ q : B[X], p2 (AdjoinRoot.mk _ q) = AdjoinRoot.mk _ (q.map (π : B →+* E)) := by
    intro q
    rw [AdjoinRoot.liftAlgHom_mk, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map]
    rfl
  have hp2root : p2 (AdjoinRoot.root _) = AdjoinRoot.root _ := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hp2map : ∀ q : E[X], p2 (AdjoinRoot.mk _ (q.map (algebraMap E B))) = AdjoinRoot.mk _ q := by
    intro q
    rw [hp2, Polynomial.map_map]
    congr 1
    conv_rhs => rw [← Polynomial.map_id (p := q)]
    congr 1
    ext r
    simp
  have hnilT : ∀ a, π (p1 a) = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hp1] at ha
    obtain ⟨r, hr⟩ : X ∣ q - C (q.coeff 0) := X_dvd_iff.mpr (by simp)
    have hq : q = C (q.coeff 0) + X * r := by rw [← hr]; ring
    rw [hq, map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    exact Commute.isNilpotent_add (Commute.all _ _) ((hπ _ ha).map _)
      ⟨N, by rw [mul_pow, hrootB, zero_mul]⟩
  have hnilC : ∀ a, πC a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hπC] at ha
    obtain ⟨r, rfl⟩ := X_dvd_iff.mpr ha
    exact ⟨N, by rw [map_mul, AdjoinRoot.mk_X, mul_pow, hrootE, zero_mul]⟩
  have hcomm : π.comp p1 = πC.comp p2 := by
    refine AlgHom.ext fun a => ?_
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    simp only [AlgHom.comp_apply, hp1, hp2, hπC, coeff_map]
    rfl
  have hsurj : ∀ b c, π b = πC c → ∃ s, p1 s = b ∧ p2 s = c := by
    intro b c hbc
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective c
    rw [hπC] at hbc
    refine ⟨AdjoinRoot.of _ b + AdjoinRoot.mk _ (q.map (algebraMap E B)) -
      AdjoinRoot.of _ (algebraMap E B (q.coeff 0)), ?_, ?_⟩
    · rw [map_sub, map_add, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C, hp1, hp1, hp1]
      simp
    · rw [map_sub, map_add, hp2map, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C, hp2, hp2]
      simp [hbc]
  have hker : ∀ Q, p2 Q = 0 → Q ∈ I.map (AdjoinRoot.of ((X : B[X]) ^ N)) := by
    intro Q hQ
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective Q
    rw [hp2, AdjoinRoot.mk_eq_zero] at hQ
    have hmod : (q %ₘ (X ^ N)).map (π : B →+* E) = 0 := by
      rw [map_modByMonic _ (monic_X_pow N), Polynomial.map_pow, map_X]
      exact (modByMonic_eq_zero_iff_dvd (monic_X_pow N)).mpr hQ
    have hmk : AdjoinRoot.mk ((X : B[X]) ^ N) q = AdjoinRoot.mk _ (q %ₘ (X ^ N)) := by
      conv_lhs => rw [← modByMonic_add_div q (X ^ N)]
      rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
    rw [hmk]
    have hin : q %ₘ (X ^ N) ∈ I.map (C : B →+* B[X]) := by
      rw [Ideal.mem_map_C_iff]
      intro n
      rw [hIdef, RingHom.mem_ker]
      have := congrArg (fun p => p.coeff n) hmod
      simpa using this
    have := Ideal.mem_map_of_mem (AdjoinRoot.mk ((X : B[X]) ^ N)) hin
    rw [Ideal.map_map] at this
    exact this
  refine ⟨AdjoinRoot ((X : E[X]) ^ N), inferInstance, inferInstance, inferInstance,
    AdjoinRoot ((X : B[X]) ^ N), inferInstance, inferInstance, inferInstance, πC, p1, p2,
    AdjoinRoot.root _, ⟨N, hrootE⟩, hnilC, hnilT, hcomm, hsurj, ?_⟩
  intro P y j v hj hP hPy
  obtain ⟨qv, hqv⟩ := AdjoinRoot.mk_surjective (v : AdjoinRoot ((X : E[X]) ^ N))
  set V := AdjoinRoot.mk ((X : B[X]) ^ N) (qv.map (algebraMap E B)) with hVdef
  have hV : p2 V = v := by rw [hVdef, hp2map, hqv]
  have hVu : IsUnit V := by
    have hw : π (p1 V) ≠ 0 := by
      rw [← AlgHom.comp_apply, hcomm, AlgHom.comp_apply, hV]
      exact (v.isUnit.map πC).ne_zero
    have h1 : IsNilpotent (V - AdjoinRoot.of _ (algebraMap E B (π (p1 V)))) := by
      apply hnilT
      rw [map_sub, map_sub, hp1of, AlgHom.commutes]
      simp
    have h2 : IsUnit (AdjoinRoot.of ((X : B[X]) ^ N) (algebraMap E B (π (p1 V)))) :=
      ((Ne.isUnit hw).map (algebraMap E B)).map _
    have := h1.isUnit_add_left_of_commute h2 (Commute.all _ _)
    simpa using this
  obtain ⟨Vi, hVi⟩ : ∃ Vi, V * Vi = 1 := hVu.exists_right_inv
  set Q := P - AdjoinRoot.root ((X : B[X]) ^ N) ^ j * V with hQdef
  have hQ2 : p2 Q = 0 := by
    rw [hQdef, map_sub, map_mul, map_pow, hV, hP, hp2root, sub_self]
  set K := I.map (AdjoinRoot.of ((X : B[X]) ^ N)) with hK
  have hQK : Q ∈ K := hker Q hQ2
  set R := -(Q * Vi) with hR
  have hRK : R ∈ K := K.neg_mem (K.mul_mem_right _ hQK)
  have hxR : AdjoinRoot.root ((X : B[X]) ^ N) ^ j * y = R * y := by
    rw [hR]
    linear_combination (-(AdjoinRoot.root ((X : B[X]) ^ N) ^ j * y)) * hVi + Vi * hPy +
      (Vi * y) * hQdef
  have hpow : ∀ k : ℕ, AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * y = R ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hsplit : AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * (k + 1)) =
          AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * AdjoinRoot.root ((X : B[X]) ^ N) ^ j := by
        rw [← pow_add]
        congr 1
      calc AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * (k + 1)) * y
          = AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) *
              (AdjoinRoot.root ((X : B[X]) ^ N) ^ j * y) := by
            rw [hsplit, mul_assoc]
        _ = R * (AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * y) := by rw [hxR]; ring
        _ = R ^ (k + 1) * y := by rw [ih]; ring
  have hRe : R ^ e = 0 := by
    have h3 : R ^ e ∈ K ^ e := Ideal.pow_mem_pow hRK e
    rw [hK, ← Ideal.map_pow, he, Ideal.zero_eq_bot, Ideal.map_bot] at h3
    exact (Ideal.mem_bot).1 h3
  have hy0 : AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * e) * y = 0 := by
    rw [hpow, hRe, zero_mul]
  have hlt : j * e < N := by
    have := Nat.mul_le_mul_right e hj
    omega
  obtain ⟨qy, rfl⟩ := AdjoinRoot.mk_surjective y
  rw [hp1]
  rw [← AdjoinRoot.mk_X, ← map_pow, ← map_mul, AdjoinRoot.mk_eq_zero] at hy0
  obtain ⟨s, hs⟩ := hy0
  have h4 := congrArg (fun p => p.coeff (j * e)) hs
  simp only [coeff_X_pow_mul'] at h4
  simpa [Nat.not_le.mpr hlt] using h4
