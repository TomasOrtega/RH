import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjectiveStatement

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L

private abbrev rd (a : ℕ) : SL(2, ℤ) →* SL(2, ZMod a) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod a))

private def red {a b : ℕ} (h : b ∣ a) : SL(2, ZMod a) →* SL(2, ZMod b) :=
  Matrix.SpecialLinearGroup.map (ZMod.castHom h (ZMod b))

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma rd_apply (a : ℕ) (g : SL(2, ℤ)) (i j : Fin 2) : (rd a g) i j = ((g i j : ℤ) : ZMod a) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma red_apply {a b : ℕ} (h : b ∣ a) (γ : SL(2, ZMod a)) (i j : Fin 2) :
    (red h γ) i j = ZMod.castHom h (ZMod b) (γ i j) := rfl

private def cj {R : Type} [CommRing R] (u : Rˣ) (h : SL(2, R)) : SL(2, R) :=
  ⟨!![h 0 0, (u : R) * h 0 1; ((u⁻¹ : Rˣ) : R) * h 1 0, h 1 1], by
    have hd := h.det_coe
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
    linear_combination hd - h 0 1 * h 1 0 * hu⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma cj00 {R : Type} [CommRing R] (u : Rˣ) (h : SL(2, R)) : (cj u h) 0 0 = h 0 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma cj01 {R : Type} [CommRing R] (u : Rˣ) (h : SL(2, R)) : (cj u h) 0 1 = u * h 0 1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma cj10 {R : Type} [CommRing R] (u : Rˣ) (h : SL(2, R)) : (cj u h) 1 0 = ((u⁻¹ : Rˣ) : R) * h 1 0 := rfl

open Classical in
private noncomputable def H2 (N : ℕ) [NeZero N] : Finset SL(2, ZMod (N * N)) :=
  Finset.univ.filter fun η => η ∈ (CongruenceSubgroup.Gamma1 N).map (rd (N * N))

/- English proof (translation)
The claim follows from `Subgroup.mem_inf`.
-/
private lemma gam_iff {N l : ℕ} {g : SL(2, ℤ)} :
    g ∈ Gam N l ↔ g ∈ CongruenceSubgroup.Gamma1 N ∧ g ∈ CongruenceSubgroup.Gamma0 l :=
  Subgroup.mem_inf

end UpperTheory.Kd.L

/- English proof (translation)
Use `⟨((∏ p ∈ c.natAbs.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ d), (p : ℕ) : ℕ) : ℤ), ?_⟩` and prove the remaining obligations. Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`. Assume the negation of the conclusion as `hne`. Take `⟨p, hp, hpg⟩` from `Nat.exists_prime_and_dvd hne`. Rewrite `hpg` using `[Int.gcd_eq_natAbs]`.

Establish `hpc : (p : ℤ) ∣ c` using `Int.ofNat_dvd_left.2 (hpg.trans (Nat.gcd_dvd_left _ _))`. Establish `hpe` using `Int.ofNat_dvd_left.2 (hpg.trans (Nat.gcd_dvd_right _ _))`. Establish `hpz : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Distinguish the cases in `hpd : (p : ℤ) ∣ d`. Establish `htM` using `(dvd_add_right hpd).1 hpe`.

Break down `hpz.dvd_or_dvd htM with hpt | hpM` into its components or cases. Take `⟨q, hq, hpq⟩` from `(Prime.dvd_finset_prod_iff hp.prime _).1 (Int.natCast_dvd_natCast.1 hpt)`. Rewrite `hq` using `[Finset.mem_filter, Nat.mem_primeFactors]`. Establish `hpq' : p = q` using `(Nat.prime_dvd_prime_iff_eq hp hq.1.1).1 hpq`. Substitute `hpq'` using the available equality.

Conclude with `hq.2 hpd`. Conclude with `h p hp hpc hpd hpM`. Establish `hpt : (p : ℤ) ∣ ((∏ p ∈ c.natAbs.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ d), (p : ℕ) : ℕ) : ℤ)`. Apply `Int.natCast_dvd_natCast.2` to reduce the goal to its premises. Apply `Finset.dvd_prod_of_mem` to reduce the goal to its premises.

Rewrite using `[Finset.mem_filter, Nat.mem_primeFactors]`. Conclude with `⟨⟨hp, Int.ofNat_dvd_left.1 hpc, Int.natAbs_ne_zero.2 hc⟩, hpd⟩`. Conclude with `hpd ((dvd_add_left (dvd_mul_of_dvd_left hpt M)).1 hpe)`.
-/
private theorem coe_uel_eq_umat (c d M : ℤ) (hc : c ≠ 0)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c → (p : ℤ) ∣ d → (p : ℤ) ∣ M → False) :
    ∃ t : ℤ, IsCoprime c (d + t * M) := by
  classical
  refine ⟨((∏ p ∈ c.natAbs.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ d), (p : ℕ) : ℕ) : ℤ), ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  rw [Int.gcd_eq_natAbs] at hpg
  have hpc : (p : ℤ) ∣ c := Int.ofNat_dvd_left.2 (hpg.trans (Nat.gcd_dvd_left _ _))
  have hpe := Int.ofNat_dvd_left.2 (hpg.trans (Nat.gcd_dvd_right _ _))
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hpd : (p : ℤ) ∣ d
  · have htM := (dvd_add_right hpd).1 hpe
    rcases hpz.dvd_or_dvd htM with hpt | hpM
    · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 (Int.natCast_dvd_natCast.1 hpt)
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hq
      have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq.1.1).1 hpq
      subst hpq'
      exact hq.2 hpd
    · exact h p hp hpc hpd hpM
  · have hpt : (p : ℤ) ∣ ((∏ p ∈ c.natAbs.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ d), (p : ℕ) : ℕ) : ℤ) := by
      apply Int.natCast_dvd_natCast.2
      apply Finset.dvd_prod_of_mem
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hp, Int.ofNat_dvd_left.1 hpc, Int.natAbs_ne_zero.2 hc⟩, hpd⟩
    exact hpd ((dvd_add_left (dvd_mul_of_dvd_left hpt M)).1 hpe)

/- English proof (translation)
Take `⟨a, ha⟩` from `ZMod.intCast_surjective (γ 0 0)`. Take `⟨b, hb⟩` from `ZMod.intCast_surjective (γ 0 1)`. Take `⟨c0, hc0⟩` from `ZMod.intCast_surjective (γ 1 0)`. Take `⟨d0, hd0⟩` from `ZMod.intCast_surjective (γ 1 1)`. Establish `h1 : (a : ZMod M) * d0 - b * c0 = 1`.

Use `γ.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Rewrite using `[ha, hb, hc0, hd0]`. Conclude with `this`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : (M : ℤ) ∣ a * d0 - b * c0 - 1 := by`.

Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree. Choose the witnesses or unpack the hypotheses as in `⟨c, d, hc, hd, hcd⟩ : ∃ c d : ℤ, (c : ZMod M) = γ 1 0 ∧ (d : ZMod M) = γ 1 1 ∧ IsCoprime c d := by`.

Distinguish the cases in `hc00 : c0 + (if c0 = 0 then (M : ℤ) else 0) = 0`. Establish `hc0z : c0 = 0`. Assume the negation of the conclusion as `hne`. Simplify using `[hne] at hc00`. Establish `hM : (M : ℤ) = 0` using `by simpa [hc0z] using hc00`.

Use `⟨c0, d0, hc0, hd0, ⟨0, a, ?_⟩⟩` and prove the remaining obligations. Rewrite `hs` using `[hM, hc0z]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨t, ht⟩` from `coe_uel_eq_umat _ d0 (M : ℤ) hc00 (by`. Introduce `p hp h1 h2 h3`.

Establish `h1' : (p : ℤ) ∣ c0` using `by split_ifs at h1 with hz`. Rewrite using `[hz]`. Conclude with `dvd_zero _`. Simplify using `using h1`. Establish `h4 : (p : ℤ) ∣ 1`.

Establish `e : (1 : ℤ) = a * d0 - b * c0 - M * s` using `by linarith`. Rewrite using `[e]`. Conclude with `dvd_sub (dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1' _)) (dvd_mul_of_dvd_left h3 _)`. Establish `h5` using `Int.eq_one_of_dvd_one (by positivity) h4`. Conclude with `hp.one_lt.ne' (by exact_mod_cast h5))`.

Use `⟨_, _, ?_, ?_, ht⟩` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> push_cast <;> simp [hc0]`. Use `push_cast`. Simplify using `[hd0]`. Take `⟨u, v, huv⟩` from `hcd`.

Establish `h1' : (a : ZMod M) * d - b * c = 1`. Use `γ.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Rewrite using `[ha, hb, hc, hd]`. Conclude with `this`.

Establish `h2 : (v : ZMod M) * d + u * c = 1`. Use `congrArg (fun x : ℤ => (x : ZMod M)) huv` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this`. Take `⟨g, hg⟩ : ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) = !![v + ((b + u) * v + (a - v) * u) * c, -u + ((b + u) * v + (a - v) * u) * d; c, d]` from `⟨⟨_, by`.

Rewrite using `[Matrix.det_fin_two_of]`. Take the linear combination `huv⟩, rfl⟩`. Use `⟨g, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[rd_apply, hg]`.

Apply the tactic sequence `fin_cases i <;> fin_cases j`. Simplify using the standard rewrite rules. Rewrite using `[← ha]`. Take the linear combination `(-(v : ZMod M)) * h1' + (a : ZMod M) * h2`. Simplify using the standard rewrite rules.

Rewrite using `[← hb]`. Take the linear combination `(u : ZMod M) * h1' + (b : ZMod M) * h2`. Simplify using `[hc]`. Simplify using `[hd]`.
-/
private theorem exists_rd_eq (M : ℕ) (γ : SL(2, ZMod M)) : ∃ g : SL(2, ℤ), rd M g = γ := by
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective (γ 0 0)
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective (γ 0 1)
  obtain ⟨c0, hc0⟩ := ZMod.intCast_surjective (γ 1 0)
  obtain ⟨d0, hd0⟩ := ZMod.intCast_surjective (γ 1 1)
  have h1 : (a : ZMod M) * d0 - b * c0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    rw [ha, hb, hc0, hd0]
    exact this
  obtain ⟨s, hs⟩ : (M : ℤ) ∣ a * d0 - b * c0 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h1]
    ring
  obtain ⟨c, d, hc, hd, hcd⟩ : ∃ c d : ℤ, (c : ZMod M) = γ 1 0 ∧ (d : ZMod M) = γ 1 1 ∧ IsCoprime c d := by
    by_cases hc00 : c0 + (if c0 = 0 then (M : ℤ) else 0) = 0
    · have hc0z : c0 = 0 := by
        by_contra hne
        simp [hne] at hc00
      have hM : (M : ℤ) = 0 := by simpa [hc0z] using hc00
      refine ⟨c0, d0, hc0, hd0, ⟨0, a, ?_⟩⟩
      rw [hM, hc0z] at hs
      linarith
    · obtain ⟨t, ht⟩ := coe_uel_eq_umat _ d0 (M : ℤ) hc00 (by
        intro p hp h1 h2 h3
        have h1' : (p : ℤ) ∣ c0 := by
          split_ifs at h1 with hz
          · rw [hz]
            exact dvd_zero _
          · simpa using h1
        have h4 : (p : ℤ) ∣ 1 := by
          have e : (1 : ℤ) = a * d0 - b * c0 - M * s := by linarith
          rw [e]
          exact dvd_sub (dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1' _))
            (dvd_mul_of_dvd_left h3 _)
        have h5 := Int.eq_one_of_dvd_one (by positivity) h4
        exact hp.one_lt.ne' (by exact_mod_cast h5))
      refine ⟨_, _, ?_, ?_, ht⟩
      · split_ifs <;> push_cast <;> simp [hc0]
      · push_cast
        simp [hd0]
  obtain ⟨u, v, huv⟩ := hcd
  have h1' : (a : ZMod M) * d - b * c = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    rw [ha, hb, hc, hd]
    exact this
  have h2 : (v : ZMod M) * d + u * c = 1 := by
    have := congrArg (fun x : ℤ => (x : ZMod M)) huv
    push_cast at this
    linear_combination this
  obtain ⟨g, hg⟩ : ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) =
      !![v + ((b + u) * v + (a - v) * u) * c, -u + ((b + u) * v + (a - v) * u) * d; c, d] :=
    ⟨⟨_, by
      rw [Matrix.det_fin_two_of]
      linear_combination huv⟩, rfl⟩
  refine ⟨g, ?_⟩
  ext i j
  rw [rd_apply, hg]
  fin_cases i <;> fin_cases j
  · simp
    rw [← ha]
    linear_combination (-(v : ZMod M)) * h1' + (a : ZMod M) * h2
  · simp
    rw [← hb]
    linear_combination (u : ZMod M) * h1' + (b : ZMod M) * h2
  · simp [hc]
  · simp [hd]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[red_apply, rd_apply]`.
-/
private theorem red_rd_eq_rd_of_dvd {a b : ℕ} (h : b ∣ a) (g : SL(2, ℤ)) : red h (rd a g) = rd b g := by
  ext i j
  simp [red_apply, rd_apply]
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `show ((ZMod.cast x : ZMod L × ZMod Q)).1 = _`. Rewrite using `[Prod.fst_zmod_cast]`. Both sides reduce to the same expression. Use `show ((ZMod.cast x : ZMod L × ZMod Q)).2 = _`.

Rewrite using `[Prod.snd_zmod_cast]`. Both sides reduce to the same expression.
-/
private theorem chineseRemainder_fst_snd_eq_castHom {L Q : ℕ} (hLQ : L.Coprime Q) (x : ZMod (L * Q)) :
    (ZMod.chineseRemainder hLQ x).1 = ZMod.castHom (dvd_mul_right L Q) (ZMod L) x ∧
    (ZMod.chineseRemainder hLQ x).2 = ZMod.castHom (dvd_mul_left Q L) (ZMod Q) x := by
  constructor
  · show ((ZMod.cast x : ZMod L × ZMod Q)).1 = _
    rw [Prod.fst_zmod_cast]
    rfl
  · show ((ZMod.cast x : ZMod L × ZMod Q)).2 = _
    rw [Prod.snd_zmod_cast]
    rfl

/- English proof (translation)
Use extensionality with `i j`. Apply `(ZMod.chineseRemainder hLQ).injective` to reduce the goal to its premises. Establish `e1` using `congrArg (fun z : SL(2, ZMod L) => z i j) h1`. Establish `e2` using `congrArg (fun z : SL(2, ZMod Q) => z i j) h2`. Simplify using `only [red_apply] at e1 e2`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[(chineseRemainder_fst_snd_eq_castHom hLQ _).1, (chineseRemainder_fst_snd_eq_castHom hLQ _).1]`. Conclude with `e1`. Rewrite using `[(chineseRemainder_fst_snd_eq_castHom hLQ _).2, (chineseRemainder_fst_snd_eq_castHom hLQ _).2]`. Conclude with `e2`.
-/
private theorem eq_of_red_eq_of_coprime {L Q : ℕ} (hLQ : L.Coprime Q) (x y : SL(2, ZMod (L * Q)))
    (h1 : red (dvd_mul_right L Q) x = red (dvd_mul_right L Q) y)
    (h2 : red (dvd_mul_left Q L) x = red (dvd_mul_left Q L) y) : x = y := by
  ext i j
  apply (ZMod.chineseRemainder hLQ).injective
  have e1 := congrArg (fun z : SL(2, ZMod L) => z i j) h1
  have e2 := congrArg (fun z : SL(2, ZMod Q) => z i j) h2
  simp only [red_apply] at e1 e2
  refine Prod.ext ?_ ?_
  · rw [(chineseRemainder_fst_snd_eq_castHom hLQ _).1, (chineseRemainder_fst_snd_eq_castHom hLQ _).1]
    exact e1
  · rw [(chineseRemainder_fst_snd_eq_castHom hLQ _).2, (chineseRemainder_fst_snd_eq_castHom hLQ _).2]
    exact e2

/- English proof (translation)
Establish `hA : ∀ z : ZMod L × ZMod Q, ZMod.castHom (dvd_mul_right L Q) (ZMod L) ((ZMod.chineseRemainder hLQ).symm z) = z.1` using `fun z => by`. Rewrite using `[← (chineseRemainder_fst_snd_eq_castHom hLQ _).1]`. Conclude with `congrArg Prod.fst ((ZMod.chineseRemainder hLQ).apply_symm_apply z)`. Establish `hB : ∀ z : ZMod L × ZMod Q, ZMod.castHom (dvd_mul_left Q L) (ZMod Q) ((ZMod.chineseRemainder hLQ).symm z) = z.2` using `fun z => by`. Rewrite using `[← (chineseRemainder_fst_snd_eq_castHom hLQ _).2]`.

Conclude with `congrArg Prod.snd ((ZMod.chineseRemainder hLQ).apply_symm_apply z)`. Take `⟨X, hX⟩ : ∃ X : Matrix (Fin 2) (Fin 2) (ZMod (L * Q)), X = fun i j => (ZMod.chineseRemainder hLQ).symm (δ i j, η i j)` from `⟨_, rfl⟩`. Establish `hXA : (ZMod.castHom (dvd_mul_right L Q) (ZMod L)).mapMatrix X = (δ : Matrix (Fin 2) (Fin 2) (ZMod L))`. Use extensionality with `i j`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, hX]`.

Conclude with `hA _`. Establish `hXB : (ZMod.castHom (dvd_mul_left Q L) (ZMod Q)).mapMatrix X = (η : Matrix (Fin 2) (Fin 2) (ZMod Q))`. Use extensionality with `i j`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, hX]`. Conclude with `hB _`.

Establish `hdet : X.det = 1`. Apply `(ZMod.chineseRemainder hLQ).injective` to reduce the goal to its premises. Rewrite using `[map_one]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[(chineseRemainder_fst_snd_eq_castHom hLQ _).1] show ZMod.castHom (dvd_mul_right L Q) (ZMod L) X.det = 1`.

Rewrite using `[RingHom.map_det, hXA, δ.det_coe]`. Rewrite using `[(chineseRemainder_fst_snd_eq_castHom hLQ _).2] show ZMod.castHom (dvd_mul_left Q L) (ZMod Q) X.det = 1`. Rewrite using `[RingHom.map_det, hXB, η.det_coe]`. Take `⟨x, hx⟩ : ∃ x : SL(2, ZMod (L * Q)), (x : Matrix (Fin 2) (Fin 2) (ZMod (L * Q))) = X` from `⟨⟨X, hdet⟩, rfl⟩`. Use `⟨x, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Rewrite using `[red_apply, hx]`. Conclude with `congrFun (congrFun hXA i) j`. Use extensionality with `i j`. Rewrite using `[red_apply, hx]`.

Conclude with `congrFun (congrFun hXB i) j`.
-/
private theorem exists_red_eq_pair_of_coprime {L Q : ℕ} (hLQ : L.Coprime Q) (δ : SL(2, ZMod L)) (η : SL(2, ZMod Q)) :
    ∃ x : SL(2, ZMod (L * Q)), red (dvd_mul_right L Q) x = δ ∧ red (dvd_mul_left Q L) x = η := by
  have hA : ∀ z : ZMod L × ZMod Q,
      ZMod.castHom (dvd_mul_right L Q) (ZMod L) ((ZMod.chineseRemainder hLQ).symm z) = z.1 :=
    fun z => by
      rw [← (chineseRemainder_fst_snd_eq_castHom hLQ _).1]
      exact congrArg Prod.fst ((ZMod.chineseRemainder hLQ).apply_symm_apply z)
  have hB : ∀ z : ZMod L × ZMod Q,
      ZMod.castHom (dvd_mul_left Q L) (ZMod Q) ((ZMod.chineseRemainder hLQ).symm z) = z.2 :=
    fun z => by
      rw [← (chineseRemainder_fst_snd_eq_castHom hLQ _).2]
      exact congrArg Prod.snd ((ZMod.chineseRemainder hLQ).apply_symm_apply z)
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin 2) (Fin 2) (ZMod (L * Q)),
      X = fun i j => (ZMod.chineseRemainder hLQ).symm (δ i j, η i j) := ⟨_, rfl⟩
  have hXA : (ZMod.castHom (dvd_mul_right L Q) (ZMod L)).mapMatrix X = (δ : Matrix (Fin 2) (Fin 2) (ZMod L)) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hX]
    exact hA _
  have hXB : (ZMod.castHom (dvd_mul_left Q L) (ZMod Q)).mapMatrix X = (η : Matrix (Fin 2) (Fin 2) (ZMod Q)) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hX]
    exact hB _
  have hdet : X.det = 1 := by
    apply (ZMod.chineseRemainder hLQ).injective
    rw [map_one]
    refine Prod.ext ?_ ?_
    · rw [(chineseRemainder_fst_snd_eq_castHom hLQ _).1]
      show ZMod.castHom (dvd_mul_right L Q) (ZMod L) X.det = 1
      rw [RingHom.map_det, hXA, δ.det_coe]
    · rw [(chineseRemainder_fst_snd_eq_castHom hLQ _).2]
      show ZMod.castHom (dvd_mul_left Q L) (ZMod Q) X.det = 1
      rw [RingHom.map_det, hXB, η.det_coe]
  obtain ⟨x, hx⟩ : ∃ x : SL(2, ZMod (L * Q)), (x : Matrix (Fin 2) (Fin 2) (ZMod (L * Q))) = X :=
    ⟨⟨X, hdet⟩, rfl⟩
  refine ⟨x, ?_, ?_⟩
  · ext i j
    rw [red_apply, hx]
    exact congrFun (congrFun hXA i) j
  · ext i j
    rw [red_apply, hx]
    exact congrFun (congrFun hXB i) j

/- English proof (translation)
Unfold `Gs`. Simplify using `[Subgroup.mem_map]`.
-/
private theorem mem_gs_iff_exists_rd_eq (N l M : ℕ) [NeZero M] (γ : SL(2, ZMod M)) :
    γ ∈ Gs N l M ↔ ∃ g ∈ Gam N l, rd M g = γ := by
  unfold Gs
  simp [Subgroup.mem_map]

/- English proof (translation)
Rewrite using `[ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]`.
-/
private theorem castHom_eq_zero_iff_dvd_val (l k : ℕ) [NeZero (l ^ k)] (hd : l ∣ l ^ k) (x : ZMod (l ^ k)) :
    ZMod.castHom hd (ZMod l) x = 0 ↔ l ∣ x.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `hLQ : (l ^ k).Coprime (N * N)`. Establish `h : l.Coprime N` using `(Nat.Prime.coprime_iff_not_dvd hl).2 hlN`. Conclude with `Nat.Coprime.pow_left _ (Nat.Coprime.mul_right h h)`. Use `set B := Finset.univ.filter (fun δ : SL(2, ZMod (l ^ k)) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0) with hB`.

Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_nbij (fun γ => (red (dvd_mul_right (l ^ k) (N * N)) γ, red (dvd_mul_left (N * N) (l ^ k)) γ))` to reduce the goal to its premises. Introduce `γ hγ`. Take `⟨g, hg, rfl⟩` from `(mem_gs_iff_exists_rd_eq _ _ _ γ).1 hγ`. Rewrite `hg` using `[gam_iff]`.

Rewrite using `[red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd, Finset.mem_product, hB, Finset.mem_filter]`. Use `⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[rd_apply, map_intCast]`. Conclude with `CongruenceSubgroup.Gamma0_mem.1 hg.2`. Unfold `H2`.

Rewrite using `[Finset.mem_filter]`. Conclude with `⟨Finset.mem_univ _, Subgroup.mem_map_of_mem _ hg.1⟩`. Introduce `x _ y _ hxy`. Simplify using `only [Prod.mk.injEq] at hxy`. Conclude with `eq_of_red_eq_of_coprime hLQ x y hxy.1 hxy.2`.

Introduce and unpack `⟨δ, η⟩ hp`. Rewrite `hp` using `[Finset.mem_coe, Finset.mem_product, hB, Finset.mem_filter]`. Take `⟨⟨_, hδ⟩, hη⟩` from `hp`. Unfold `H2 at hη`. Rewrite `hη` using `[Finset.mem_filter]`.

Take `⟨g0, hg0, hg0e⟩` from `Subgroup.mem_map.1 hη.2`. Take `⟨x, hx1, hx2⟩` from `exists_red_eq_pair_of_coprime hLQ δ η`. Take `⟨g, rfl⟩` from `exists_rd_eq _ x`. Rewrite `hx1`, `hx2` using `[red_rd_eq_rd_of_dvd]`. Use `⟨rd _ g, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.mem_coe, mem_gs_iff_exists_rd_eq]`. Use `⟨g, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[gam_iff]`. Prove the components needed by the constructor for the conclusion. Establish `E` using `congrArg (red (dvd_mul_right N N)) (hx2.trans hg0e.symm)`.

Rewrite `E` using `[red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd]`. Establish `e : ∀ i j, ((g i j : ℤ) : ZMod N) = ((g0 i j : ℤ) : ZMod N)` using `fun i j => by`. Use `congrArg (fun z : SL(2, ZMod N) => z i j) E` as an intermediate fact. Simplify `this` using `only [rd_apply]`. Rewrite `hg0`, the goal using `[CongruenceSubgroup.Gamma1_mem]`.

Rewrite using `[e, e, e]`. Conclude with `hg0`. Rewrite using `[CongruenceSubgroup.Gamma0_mem]`. Use `congrArg (fun z : SL(2, ZMod (l ^ k)) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (z 1 0)) hx1` as an intermediate fact. Simplify using `only [rd_apply, map_intCast] at this`.

Rewrite using `[this]`. Conclude with `hδ`. Simplify using `only`. Rewrite using `[red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd, hx1, hx2]`. Introduce `_ _`.

Both sides reduce to the same expression. Use `_ = ∑ δ ∈ B, ∑ _η ∈ H2 N, F δ := Finset.sum_product _ _ _`. Use `_ = (H2 N).card • ∑ δ ∈ B, F δ := by`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl (fun δ _ => Finset.sum_const _)`.
-/
private theorem sum_gs_red_eq_card_smul_sum_lower_zero (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (k : ℕ) (hk : k ≠ 0)
    (hlN : ¬ l ∣ N) [NeZero (l ^ k * (N * N))] {V : Type} [AddCommMonoid V]
    (F : SL(2, ZMod (l ^ k)) → V) :
    ∑ γ ∈ Gs N l (l ^ k * (N * N)), F (red (dvd_mul_right (l ^ k) (N * N)) γ) =
      (H2 N).card • ∑ δ ∈ Finset.univ.filter
        (fun δ : SL(2, ZMod (l ^ k)) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0), F δ := by
  classical
  have hl : l.Prime := Fact.out
  have hLQ : (l ^ k).Coprime (N * N) := by
    have h : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
    exact Nat.Coprime.pow_left _ (Nat.Coprime.mul_right h h)
  set B := Finset.univ.filter
    (fun δ : SL(2, ZMod (l ^ k)) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0) with hB
  calc ∑ γ ∈ Gs N l (l ^ k * (N * N)), F (red (dvd_mul_right (l ^ k) (N * N)) γ)
        = ∑ p ∈ B ×ˢ H2 N, F p.1 := by
        apply Finset.sum_nbij (fun γ => (red (dvd_mul_right (l ^ k) (N * N)) γ,
          red (dvd_mul_left (N * N) (l ^ k)) γ))
        · intro γ hγ
          obtain ⟨g, hg, rfl⟩ := (mem_gs_iff_exists_rd_eq _ _ _ γ).1 hγ
          rw [gam_iff] at hg
          rw [red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd, Finset.mem_product, hB, Finset.mem_filter]
          refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rw [rd_apply, map_intCast]
            exact CongruenceSubgroup.Gamma0_mem.1 hg.2
          · unfold H2
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, Subgroup.mem_map_of_mem _ hg.1⟩
        · intro x _ y _ hxy
          simp only [Prod.mk.injEq] at hxy
          exact eq_of_red_eq_of_coprime hLQ x y hxy.1 hxy.2
        · rintro ⟨δ, η⟩ hp
          rw [Finset.mem_coe, Finset.mem_product, hB, Finset.mem_filter] at hp
          obtain ⟨⟨_, hδ⟩, hη⟩ := hp
          unfold H2 at hη
          rw [Finset.mem_filter] at hη
          obtain ⟨g0, hg0, hg0e⟩ := Subgroup.mem_map.1 hη.2
          obtain ⟨x, hx1, hx2⟩ := exists_red_eq_pair_of_coprime hLQ δ η
          obtain ⟨g, rfl⟩ := exists_rd_eq _ x
          rw [red_rd_eq_rd_of_dvd] at hx1 hx2
          refine ⟨rd _ g, ?_, ?_⟩
          · rw [Finset.mem_coe, mem_gs_iff_exists_rd_eq]
            refine ⟨g, ?_, rfl⟩
            rw [gam_iff]
            constructor
            · have E := congrArg (red (dvd_mul_right N N)) (hx2.trans hg0e.symm)
              rw [red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd] at E
              have e : ∀ i j, ((g i j : ℤ) : ZMod N) = ((g0 i j : ℤ) : ZMod N) := fun i j => by
                have := congrArg (fun z : SL(2, ZMod N) => z i j) E
                simpa only [rd_apply] using this
              rw [CongruenceSubgroup.Gamma1_mem] at hg0 ⊢
              rw [e, e, e]
              exact hg0
            · rw [CongruenceSubgroup.Gamma0_mem]
              have := congrArg
                (fun z : SL(2, ZMod (l ^ k)) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (z 1 0)) hx1
              simp only [rd_apply, map_intCast] at this
              rw [this]
              exact hδ
          · dsimp only
            rw [red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd, hx1, hx2]
        · intro _ _
          rfl
    _ = ∑ δ ∈ B, ∑ _η ∈ H2 N, F δ := Finset.sum_product _ _ _
    _ = (H2 N).card • ∑ δ ∈ B, F δ := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun δ _ => Finset.sum_const _)
/- English proof (translation)
Establish `e11 : ∀ (v : Rˣ) (Y : SL(2, R)), (cj v Y) 1 1 = Y 1 1` using `fun _ _ => rfl`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [cj00, cj01, cj10, e11]`.
-/
private theorem cj_inv_cj_eq_self {R : Type} [CommRing R] (u : Rˣ) (X : SL(2, R)) : cj u⁻¹ (cj u X) = X := by
  have e11 : ∀ (v : Rˣ) (Y : SL(2, R)), (cj v Y) 1 1 = Y 1 1 := fun _ _ => rfl
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cj00, cj01, cj10, e11]

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Use `haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Use `set π := ZMod.castHom (dvd_pow_self l hk) (ZMod l) with hπ`. Use `set B := Finset.univ.filter (fun δ : SL(2, ZMod (l ^ k)) => π (δ 1 0) = 0) with hB`. Use `set S := Finset.univ.filter (fun h : SL(2, ZMod (l ^ k)) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val) with hS`.

Establish `hS' : ∀ h, h ∈ S ↔ π (h 0 0) ≠ 0 ∧ π (h 1 0) ≠ 0`. Introduce `h`. Rewrite using `[hS, Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, a, b⟩`.

Conclude with `⟨fun h0 => a ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).1 h0), fun h0 => b ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).1 h0)⟩`. Introduce and unpack `⟨a, b⟩`. Conclude with `⟨Finset.mem_univ _, fun h0 => a ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).2 h0), fun h0 => b ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).2 h0)⟩`. Establish `hu : π (u : ZMod (l ^ k)) * π ((u⁻¹ : (ZMod (l ^ k))ˣ) : ZMod (l ^ k)) = 1`. Rewrite using `[← map_mul, u.mul_inv, map_one]`.

Establish `hu1 : π ((u⁻¹ : (ZMod (l ^ k))ˣ) : ZMod (l ^ k)) ≠ 0`. Introduce `h0`. Rewrite `hu` using `[h0, mul_zero]`. Conclude with `zero_ne_one hu`. Establish `hu2 : π (u : ZMod (l ^ k)) ≠ 0`.

Introduce `h0`. Rewrite `hu` using `[h0, zero_mul]`. Conclude with `zero_ne_one hu`. Establish `hA : ∀ r, π (rd (l ^ k) (gm r) 1 0) = -(r : ZMod l) * π (rd (l ^ k) (gm r) 0 0)`. Introduce `r`.

Rewrite using `[rd_apply, rd_apply, map_intCast, map_intCast]`. Conclude with `col r`. Establish `hA00 : ∀ r, π (rd (l ^ k) (gm r) 0 0) ≠ 0`. Introduce `r h0`. Establish `hd` using `(gm r).det_coe`.

Rewrite `hd` using `[Matrix.det_fin_two]`. Establish `h1` using `congrArg (fun x : ℤ => (x : ZMod l)) hd`. Move the coercions through the operations in `at h1`. Rewrite `h1` using `[col r]`. Rewrite `h0` using `[rd_apply, map_intCast]`.

Rewrite `h1` using `[h0]`. Simplify using `at h1`. Establish `pm : ∀ (X Y : SL(2, ZMod (l ^ k))) (i j : Fin 2), π ((X * Y) i j) = π (X i 0) * π (Y 0 j) + π (X i 1) * π (Y 1 j)`. Introduce `X Y i j`. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, map_mul]`.

Establish `pinv : ∀ X : SL(2, ZMod (l ^ k)), (X⁻¹) 1 0 = - X 1 0 ∧ (X⁻¹) 1 1 = X 0 0`. Introduce `X`. Rewrite using `[Matrix.SpecialLinearGroup.SL2_inv_expl]`. Simplify using the standard rewrite rules. Establish `hB00 : ∀ δ ∈ B, π (δ 0 0) ≠ 0`.

Introduce `δ hδ h0`. Rewrite `hδ` using `[hB, Finset.mem_filter]`. Establish `hd` using `δ.det_coe`. Rewrite `hd` using `[Matrix.det_fin_two]`. Establish `h1` using `congrArg π hd`.

Rewrite `h1` using `[map_sub, map_mul, map_mul, h0, hδ.2, map_one]`. Simplify using `at h1`. Establish `e11 : ∀ (v : (ZMod (l ^ k))ˣ) (Y : SL(2, ZMod (l ^ k))), (cj v Y) 1 1 = Y 1 1` using `fun _ _ => rfl`. Take `⟨w, hw⟩ : ∃ w : ZMod l → (ZMod l)ˣ, ∀ x, x ≠ 0 → (w x : ZMod l) = x` from `⟨fun x => if hx : x = 0 then 1 else Units.mk0 x hx, fun x hx => by simp [hx]⟩`. Take `⟨R, hR⟩ : ∃ R : SL(2, ZMod (l ^ k)) → (ZMod l)ˣ, ∀ h, R h = w (-(π ((cj u⁻¹ h) 1 0)) / π ((cj u⁻¹ h) 0 0))` from `⟨_, fun _ => rfl⟩`.

Establish `hcc : ∀ X, cj u (cj u⁻¹ X) = X`. Introduce `X`. Use `cj_inv_cj_eq_self u⁻¹ X` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Rewrite using `[(Finset.sum_product' Finset.univ B (fun r δ => Φ (cj u (rd (l ^ k) (gm r) * δ)))).symm]`.

Apply `Finset.sum_nbij' (fun p => cj u (rd (l ^ k) (gm p.1) * p.2)) (fun h => (R h, (rd (l ^ k) (gm (R h)))⁻¹ * cj u⁻¹ h))` to reduce the goal to its premises. Introduce and unpack `⟨r, δ⟩ hp`. Rewrite `hp` using `[Finset.mem_product]`. Establish `hδ` using `hp.2`. Establish `hδ' : π (δ 1 0) = 0`.

Rewrite `hδ` using `[hB, Finset.mem_filter]`. Conclude with `hδ.2`. Rewrite using `[hS']`. Simplify using `only`. Rewrite using `[cj00, cj10, map_mul, pm, pm, hδ', hA]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_zero, add_zero]`. Conclude with `mul_ne_zero (hA00 r) (hB00 δ hδ)`. Rewrite using `[mul_zero, add_zero]`. Conclude with `mul_ne_zero hu1 (mul_ne_zero (mul_ne_zero (neg_ne_zero.2 r.ne_zero) (hA00 r)) (hB00 δ hδ))`.

Introduce `h hh`. Rewrite `hh` using `[hS']`. Rewrite using `[Finset.mem_product, hB, Finset.mem_filter]`. Use `⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Establish `h00 : π ((cj u⁻¹ h) 0 0) = π (h 0 0)` using `by rw [cj00]`.

Establish `h10 : π ((cj u⁻¹ h) 1 0) = π (u : ZMod (l ^ k)) * π (h 1 0)`. Rewrite using `[cj10, inv_inv, map_mul]`. Establish `hx : ((R h : (ZMod l)ˣ) : ZMod l) = -(π ((cj u⁻¹ h) 1 0)) / π ((cj u⁻¹ h) 0 0)`. Rewrite using `[hR]`. Apply `hw` to reduce the goal to its premises.

Rewrite using `[h00, h10]`. Simplify using `[hh.1, hh.2, hu2]`. Establish `hh1` using `hh.1`. Rewrite using `[pm, (pinv _).1, (pinv _).2, map_neg, hA, hx, h00, h10]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨r, δ⟩ hp`. Rewrite `hp` using `[Finset.mem_product]`. Establish `hδ` using `hp.2`. Establish `hδ' : π (δ 1 0) = 0`.

Rewrite `hδ` using `[hB, Finset.mem_filter]`. Conclude with `hδ.2`. Establish `hA0` using `hA00 r`. Establish `hδ0` using `hB00 δ hδ`. Establish `hRr : R (cj u (rd (l ^ k) (gm r) * δ)) = r`.

Rewrite using `[hR, cj_inv_cj_eq_self]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hw]`. Rewrite using `[pm, pm, hδ', hA]`. Simplify using `only [mul_zero, add_zero]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[pm, pm, hδ', hA]`. Simplify using `only [mul_zero, add_zero]`. Conclude with `div_ne_zero (neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (neg_ne_zero.2 r.ne_zero) hA0) hδ0)) (mul_ne_zero hA0 hδ0)`. Simplify using `only`.

Rewrite using `[cj_inv_cj_eq_self, hRr, inv_mul_cancel_left]`. Introduce `h _ dsimp only`. Rewrite using `[mul_inv_cancel_left, hcc]`. Introduce `p _`. Both sides reduce to the same expression.
-/
private theorem sum_cj_eq_sum_entries_not_dvd (l : ℕ) [Fact l.Prime] (k : ℕ) (hk : k ≠ 0)
    (gm : (ZMod l)ˣ → SL(2, ℤ))
    (col : ∀ r : (ZMod l)ˣ, ((gm r 1 0 : ℤ) : ZMod l) = -(r : ZMod l) * ((gm r 0 0 : ℤ) : ZMod l))
    (u : (ZMod (l ^ k))ˣ) {V : Type} [AddCommMonoid V] (Φ : SL(2, ZMod (l ^ k)) → V) :
    ∑ r : (ZMod l)ˣ, ∑ δ ∈ Finset.univ.filter
        (fun δ : SL(2, ZMod (l ^ k)) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0),
        Φ (cj u (rd (l ^ k) (gm r) * δ)) =
      ∑ h ∈ Finset.univ.filter
        (fun h : SL(2, ZMod (l ^ k)) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), Φ h := by
  classical
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hl.ne_zero⟩
  set π := ZMod.castHom (dvd_pow_self l hk) (ZMod l) with hπ
  set B := Finset.univ.filter (fun δ : SL(2, ZMod (l ^ k)) => π (δ 1 0) = 0) with hB
  set S := Finset.univ.filter
    (fun h : SL(2, ZMod (l ^ k)) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val) with hS
  have hS' : ∀ h, h ∈ S ↔ π (h 0 0) ≠ 0 ∧ π (h 1 0) ≠ 0 := by
    intro h
    rw [hS, Finset.mem_filter]
    constructor
    · rintro ⟨_, a, b⟩
      exact ⟨fun h0 => a ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).1 h0),
        fun h0 => b ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).1 h0)⟩
    · rintro ⟨a, b⟩
      exact ⟨Finset.mem_univ _, fun h0 => a ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).2 h0),
        fun h0 => b ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).2 h0)⟩
  have hu : π (u : ZMod (l ^ k)) * π ((u⁻¹ : (ZMod (l ^ k))ˣ) : ZMod (l ^ k)) = 1 := by
    rw [← map_mul, u.mul_inv, map_one]
  have hu1 : π ((u⁻¹ : (ZMod (l ^ k))ˣ) : ZMod (l ^ k)) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hu
    exact zero_ne_one hu
  have hu2 : π (u : ZMod (l ^ k)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hu
    exact zero_ne_one hu
  have hA : ∀ r, π (rd (l ^ k) (gm r) 1 0) = -(r : ZMod l) * π (rd (l ^ k) (gm r) 0 0) := by
    intro r
    rw [rd_apply, rd_apply, map_intCast, map_intCast]
    exact col r
  have hA00 : ∀ r, π (rd (l ^ k) (gm r) 0 0) ≠ 0 := by
    intro r h0
    have hd := (gm r).det_coe
    rw [Matrix.det_fin_two] at hd
    have h1 := congrArg (fun x : ℤ => (x : ZMod l)) hd
    push_cast at h1
    rw [col r] at h1
    rw [rd_apply, map_intCast] at h0
    rw [h0] at h1
    simp at h1
  have pm : ∀ (X Y : SL(2, ZMod (l ^ k))) (i j : Fin 2),
      π ((X * Y) i j) = π (X i 0) * π (Y 0 j) + π (X i 1) * π (Y 1 j) := by
    intro X Y i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, map_mul]
  have pinv : ∀ X : SL(2, ZMod (l ^ k)), (X⁻¹) 1 0 = - X 1 0 ∧ (X⁻¹) 1 1 = X 0 0 := by
    intro X
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp
  have hB00 : ∀ δ ∈ B, π (δ 0 0) ≠ 0 := by
    intro δ hδ h0
    rw [hB, Finset.mem_filter] at hδ
    have hd := δ.det_coe
    rw [Matrix.det_fin_two] at hd
    have h1 := congrArg π hd
    rw [map_sub, map_mul, map_mul, h0, hδ.2, map_one] at h1
    simp at h1
  have e11 : ∀ (v : (ZMod (l ^ k))ˣ) (Y : SL(2, ZMod (l ^ k))), (cj v Y) 1 1 = Y 1 1 := fun _ _ => rfl
  obtain ⟨w, hw⟩ : ∃ w : ZMod l → (ZMod l)ˣ, ∀ x, x ≠ 0 → (w x : ZMod l) = x :=
    ⟨fun x => if hx : x = 0 then 1 else Units.mk0 x hx, fun x hx => by simp [hx]⟩
  obtain ⟨R, hR⟩ : ∃ R : SL(2, ZMod (l ^ k)) → (ZMod l)ˣ, ∀ h,
      R h = w (-(π ((cj u⁻¹ h) 1 0)) / π ((cj u⁻¹ h) 0 0)) := ⟨_, fun _ => rfl⟩
  have hcc : ∀ X, cj u (cj u⁻¹ X) = X := by
    intro X
    have := cj_inv_cj_eq_self u⁻¹ X
    rwa [inv_inv] at this
  rw [(Finset.sum_product' Finset.univ B (fun r δ => Φ (cj u (rd (l ^ k) (gm r) * δ)))).symm]
  apply Finset.sum_nbij' (fun p => cj u (rd (l ^ k) (gm p.1) * p.2))
    (fun h => (R h, (rd (l ^ k) (gm (R h)))⁻¹ * cj u⁻¹ h))
  · rintro ⟨r, δ⟩ hp
    rw [Finset.mem_product] at hp
    have hδ := hp.2
    have hδ' : π (δ 1 0) = 0 := by
      rw [hB, Finset.mem_filter] at hδ
      exact hδ.2
    rw [hS']
    dsimp only
    rw [cj00, cj10, map_mul, pm, pm, hδ', hA]
    refine ⟨?_, ?_⟩
    · rw [mul_zero, add_zero]
      exact mul_ne_zero (hA00 r) (hB00 δ hδ)
    · rw [mul_zero, add_zero]
      exact mul_ne_zero hu1 (mul_ne_zero (mul_ne_zero (neg_ne_zero.2 r.ne_zero) (hA00 r)) (hB00 δ hδ))
  · intro h hh
    rw [hS'] at hh
    rw [Finset.mem_product, hB, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
    have h00 : π ((cj u⁻¹ h) 0 0) = π (h 0 0) := by rw [cj00]
    have h10 : π ((cj u⁻¹ h) 1 0) = π (u : ZMod (l ^ k)) * π (h 1 0) := by
      rw [cj10, inv_inv, map_mul]
    have hx : ((R h : (ZMod l)ˣ) : ZMod l) = -(π ((cj u⁻¹ h) 1 0)) / π ((cj u⁻¹ h) 0 0) := by
      rw [hR]
      apply hw
      rw [h00, h10]
      simp [hh.1, hh.2, hu2]
    have hh1 := hh.1
    rw [pm, (pinv _).1, (pinv _).2, map_neg, hA, hx, h00, h10]
    field_simp
    ring
  · rintro ⟨r, δ⟩ hp
    rw [Finset.mem_product] at hp
    have hδ := hp.2
    have hδ' : π (δ 1 0) = 0 := by
      rw [hB, Finset.mem_filter] at hδ
      exact hδ.2
    have hA0 := hA00 r
    have hδ0 := hB00 δ hδ
    have hRr : R (cj u (rd (l ^ k) (gm r) * δ)) = r := by
      rw [hR, cj_inv_cj_eq_self]
      apply Units.ext
      rw [hw]
      · rw [pm, pm, hδ', hA]
        simp only [mul_zero, add_zero]
        field_simp
      · rw [pm, pm, hδ', hA]
        simp only [mul_zero, add_zero]
        exact div_ne_zero (neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (neg_ne_zero.2 r.ne_zero) hA0) hδ0))
          (mul_ne_zero hA0 hδ0)
    dsimp only
    rw [cj_inv_cj_eq_self, hRr, inv_mul_cancel_left]
  · intro h _
    dsimp only
    rw [mul_inv_cancel_left, hcc]
  · intro p _
    rfl
/- English proof (translation)
Unfold `liftSL`. Conclude with `Classical.epsilon_spec (exists_rd_eq M γ)`.
-/
private theorem rd_liftSL (M : ℕ) (γ : SL(2, ZMod M)) : rd M (liftSL M γ) = γ := by
  unfold liftSL
  exact Classical.epsilon_spec (exists_rd_eq M γ)

/- English proof (translation)
Introduce `l _ N _`. Establish `hl : l.Prime` using `Fact.out`. Use `⟨(H2 N).card, ?_, ?_⟩` and prove the remaining obligations. Apply `Finset.card_pos.2` to reduce the goal to its premises. Use `⟨1, ?_⟩` and prove the remaining obligations.

Unfold `H2`. Rewrite using `[Finset.mem_filter]`. Conclude with `⟨Finset.mem_univ _, ⟨1, Subgroup.one_mem _, map_one _⟩⟩`. Introduce `c d gm hP n m hm V _ Φ Ψ hΨ`. Take `⟨_, _, cop, _, _, _, _, g0, ga, col⟩` from `hP`.

Unfold `topMu`. Establish `hk : m + n ≠ 0` using `by omega`. Use `haveI : NeZero (l ^ (m + n) * (N * N)) := ⟨mul_ne_zero (pow_ne_zero _ hl.ne_zero) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩`. Establish `hcop : N.Coprime (l ^ (m + n))` using `Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hl).2 cop).symm`. Take `⟨u, hu⟩ : ∃ u : (ZMod (l ^ (m + n)))ˣ, (u : ZMod (l ^ (m + n))) = N` from `⟨ZMod.unitOfCoprime N hcop, ZMod.coe_unitOfCoprime _ _⟩`.

Establish `hNM : N ∣ l ^ (m + n) * (N * N)` using `(dvd_mul_right N N).trans (dvd_mul_left (N * N) _)`. Establish `key : ∀ r₀ : (ZMod l)ˣ, ∀ γ ∈ Gs N l (l ^ (m + n) * (N * N)), Ψ (gm r₀ * liftSL _ γ) = Φ (cj u (rd (l ^ (m + n)) (gm r₀) * red (dvd_mul_right (l ^ (m + n)) (N * N)) γ))`. Introduce `r₀ γ hγ`. Take `⟨g1, hg1, rfl⟩` from `(mem_gs_iff_exists_rd_eq _ _ _ γ).1 hγ`. Rewrite `hg1` using `[gam_iff]`.

Establish `hL` using `rd_liftSL _ (rd (l ^ (m + n) * (N * N)) g1)`. Use `set L1 := liftSL _ (rd (l ^ (m + n) * (N * N)) g1)`. Rewrite using `[← hL, red_rd_eq_rd_of_dvd, ← map_mul]`. Establish `E` using `congrArg (red hNM) hL`. Rewrite `E` using `[red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd]`.

Establish `e : ∀ i j, ((L1 i j : ℤ) : ZMod N) = ((g1 i j : ℤ) : ZMod N)` using `fun i j => by`. Use `congrArg (fun z : SL(2, ZMod N) => z i j) E` as an intermediate fact. Simplify `this` using `only [rd_apply]`. Establish `hg1'` using `(CongruenceSubgroup.Gamma1_mem _ _).1 hg1.1`. Establish `hL00 : ((L1 0 0 : ℤ) : ZMod N) = 1` using `by rw [e]; exact hg1'.1`.

Establish `hL10 : ((L1 1 0 : ℤ) : ZMod N) = 0` using `by rw [e]; exact hg1'.2.2`. Establish `hgΓ : gm r₀ * L1 ∈ CongruenceSubgroup.Gamma0 N` using `Subgroup.mul_mem _ (g0 r₀) (CongruenceSubgroup.Gamma0_mem.2 hL10)`. Establish `hg00 : ((en (gm r₀ * L1) 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N)`. Rewrite using `[← ga r₀]`. Unfold `en`.

Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]`. Use `push_cast`. Rewrite using `[hL00, hL10]`. Expand and normalize the polynomial expressions, which then agree. Apply `hΨ _ hgΓ hg00` to reduce the goal to its premises.

Rewrite using `[cj00, rd_apply]`. Both sides reduce to the same expression. Rewrite using `[cj01, rd_apply, hu]`. Unfold `en`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[cj10, ← hu, ← mul_assoc, Units.mul_inv, one_mul, rd_apply]`. Both sides reduce to the same expression. Rewrite using `[show (cj u (rd (l ^ (m + n)) (gm r₀ * L1))) 1 1 = (rd (l ^ (m + n)) (gm r₀ * L1)) 1 1 from rfl, rd_apply]`. Both sides reduce to the same expression.

Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `r₀ _`. Rewrite using `[Finset.sum_congr rfl (key r₀)]`. Conclude with `sum_gs_red_eq_card_smul_sum_lower_zero l N (m + n) hk cop (fun δ => Φ (cj u (rd (l ^ (m + n)) (gm r₀) * δ)))`.

Use `_ = (H2 N).card • ∑ r₀ : (ZMod l)ˣ, ∑ δ ∈ Finset.univ.filter (fun δ : SL(2, ZMod (l ^ (m + n))) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0), Φ (cj u (rd (l ^ (m + n)) (gm r₀) * δ)) := by`. Rewrite using `[Finset.smul_sum]`. Use `_ = _ := by`. Rewrite using `[sum_cj_eq_sum_entries_not_dvd l (m + n) hk gm col u Φ]`.
-/
theorem UpperTheory.Kd.L.count :
    ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N], ∃ μ : ℕ, 0 < μ ∧ ∀ (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (n m : ℕ), 1 ≤ m → ∀ (V : Type) [AddCommMonoid V] (Φ : SL(2, ZMod (l ^ (m + n))) → V) (Ψ : SL(2, ℤ) → V), (∀ g ∈ CongruenceSubgroup.Gamma0 N, ((en g 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) → ∀ h : SL(2, ZMod (l ^ (m + n))), h 0 0 = (en g 0 0 : ℤ) → h 0 1 = ((N : ℤ) * en g 0 1 : ℤ) → (N : ZMod (l ^ (m + n))) * h 1 0 = (en g 1 0 : ℤ) → h 1 1 = (en g 1 1 : ℤ) → Ψ g = Φ h) → ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Gs N l (topMu l n m N), Ψ (gm r₀ * liftSL _ γ) = μ • ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ (m + n))) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), Φ h := by
  classical
  intro l _ N _
  have hl : l.Prime := Fact.out
  refine ⟨(H2 N).card, ?_, ?_⟩
  · apply Finset.card_pos.2
    refine ⟨1, ?_⟩
    unfold H2
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨1, Subgroup.one_mem _, map_one _⟩⟩
  intro c d gm hP n m hm V _ Φ Ψ hΨ
  obtain ⟨_, _, cop, _, _, _, _, g0, ga, col⟩ := hP
  unfold topMu
  have hk : m + n ≠ 0 := by omega
  haveI : NeZero (l ^ (m + n) * (N * N)) :=
    ⟨mul_ne_zero (pow_ne_zero _ hl.ne_zero) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
  have hcop : N.Coprime (l ^ (m + n)) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hl).2 cop).symm
  obtain ⟨u, hu⟩ : ∃ u : (ZMod (l ^ (m + n)))ˣ, (u : ZMod (l ^ (m + n))) = N :=
    ⟨ZMod.unitOfCoprime N hcop, ZMod.coe_unitOfCoprime _ _⟩
  have hNM : N ∣ l ^ (m + n) * (N * N) := (dvd_mul_right N N).trans (dvd_mul_left (N * N) _)
  have key : ∀ r₀ : (ZMod l)ˣ, ∀ γ ∈ Gs N l (l ^ (m + n) * (N * N)),
      Ψ (gm r₀ * liftSL _ γ) =
        Φ (cj u (rd (l ^ (m + n)) (gm r₀) * red (dvd_mul_right (l ^ (m + n)) (N * N)) γ)) := by
    intro r₀ γ hγ
    obtain ⟨g1, hg1, rfl⟩ := (mem_gs_iff_exists_rd_eq _ _ _ γ).1 hγ
    rw [gam_iff] at hg1
    have hL := rd_liftSL _ (rd (l ^ (m + n) * (N * N)) g1)
    set L1 := liftSL _ (rd (l ^ (m + n) * (N * N)) g1)
    rw [← hL, red_rd_eq_rd_of_dvd, ← map_mul]
    have E := congrArg (red hNM) hL
    rw [red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd] at E
    have e : ∀ i j, ((L1 i j : ℤ) : ZMod N) = ((g1 i j : ℤ) : ZMod N) := fun i j => by
      have := congrArg (fun z : SL(2, ZMod N) => z i j) E
      simpa only [rd_apply] using this
    have hg1' := (CongruenceSubgroup.Gamma1_mem _ _).1 hg1.1
    have hL00 : ((L1 0 0 : ℤ) : ZMod N) = 1 := by rw [e]; exact hg1'.1
    have hL10 : ((L1 1 0 : ℤ) : ZMod N) = 0 := by rw [e]; exact hg1'.2.2
    have hgΓ : gm r₀ * L1 ∈ CongruenceSubgroup.Gamma0 N :=
      Subgroup.mul_mem _ (g0 r₀) (CongruenceSubgroup.Gamma0_mem.2 hL10)
    have hg00 : ((en (gm r₀ * L1) 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) := by
      rw [← ga r₀]
      unfold en
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      rw [hL00, hL10]
      ring
    apply hΨ _ hgΓ hg00
    · rw [cj00, rd_apply]
      rfl
    · rw [cj01, rd_apply, hu]
      unfold en
      push_cast
      ring
    · rw [cj10, ← hu, ← mul_assoc, Units.mul_inv, one_mul, rd_apply]
      rfl
    · rw [show (cj u (rd (l ^ (m + n)) (gm r₀ * L1))) 1 1 = (rd (l ^ (m + n)) (gm r₀ * L1)) 1 1 from rfl,
        rd_apply]
      rfl
  calc ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Gs N l (l ^ (m + n) * (N * N)), Ψ (gm r₀ * liftSL _ γ)
      = ∑ r₀ : (ZMod l)ˣ, (H2 N).card • ∑ δ ∈ Finset.univ.filter
          (fun δ : SL(2, ZMod (l ^ (m + n))) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0),
          Φ (cj u (rd (l ^ (m + n)) (gm r₀) * δ)) := by
        apply Finset.sum_congr rfl
        intro r₀ _
        rw [Finset.sum_congr rfl (key r₀)]
        exact sum_gs_red_eq_card_smul_sum_lower_zero l N (m + n) hk cop (fun δ => Φ (cj u (rd (l ^ (m + n)) (gm r₀) * δ)))
    _ = (H2 N).card • ∑ r₀ : (ZMod l)ˣ, ∑ δ ∈ Finset.univ.filter
          (fun δ : SL(2, ZMod (l ^ (m + n))) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0),
          Φ (cj u (rd (l ^ (m + n)) (gm r₀) * δ)) := by
        rw [Finset.smul_sum]
    _ = _ := by
        rw [sum_cj_eq_sum_entries_not_dvd l (m + n) hk gm col u Φ]
