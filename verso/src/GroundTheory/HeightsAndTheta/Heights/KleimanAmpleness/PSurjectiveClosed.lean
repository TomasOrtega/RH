import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTildeVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsIdealTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SurjectiveClosed

section Signs

variable {n : ℕ}

/- English proof (translation)
Use `wlog h : j < k generalizing j k with H`. Establish `h' : k < j` using `lt_of_le_of_ne (not_lt.mp h) (Ne.symm hjk)`. Rewrite using `[H hk hj (Ne.symm hjk) h', neg_neg]`. Establish `h1 : (L.erase j).filter (· < k) = (L.filter (· < k)).erase j`. Use extensionality with `z`.

Simplify using `only [Finset.mem_filter, Finset.mem_erase]`. The claim follows by propositional logic. Establish `h2 : (L.erase k).filter (· < j) = L.filter (· < j)`. Use extensionality with `z`. Simplify using `only [Finset.mem_filter, Finset.mem_erase]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨_, hz⟩, hzj⟩`. Conclude with `⟨hz, hzj⟩`. Introduce and unpack `⟨hz, hzj⟩`. Conclude with `⟨⟨fun hzk => by subst hzk; exact lt_irrefl _ (hzj.trans h), hz⟩, hzj⟩`.

Establish `hmem : j ∈ L.filter (· < k)` using `Finset.mem_filter.mpr ⟨hj, h⟩`. Establish `hc` using `Finset.card_erase_add_one hmem`. Simplify using `only [Cech.sgn, h1, h2]`. Rewrite using `[← hc, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sgn_mul_sgn_erase_swap {L : Finset (Fin n)} {j k : Fin n} (hj : j ∈ L) (hk : k ∈ L)
    (hjk : j ≠ k) :
    Cech.sgn L j * Cech.sgn (L.erase j) k = -(Cech.sgn L k * Cech.sgn (L.erase k) j) := by
  wlog h : j < k generalizing j k with H
  · have h' : k < j := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hjk)
    rw [H hk hj (Ne.symm hjk) h', neg_neg]
  have h1 : (L.erase j).filter (· < k) = (L.filter (· < k)).erase j := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  have h2 : (L.erase k).filter (· < j) = L.filter (· < j) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hz⟩, hzj⟩
      exact ⟨hz, hzj⟩
    · rintro ⟨hz, hzj⟩
      exact ⟨⟨fun hzk => by subst hzk; exact lt_irrefl _ (hzj.trans h), hz⟩, hzj⟩
  have hmem : j ∈ L.filter (· < k) := Finset.mem_filter.mpr ⟨hj, h⟩
  have hc := Finset.card_erase_add_one hmem
  simp only [Cech.sgn, h1, h2]
  rw [← hc, pow_succ]
  ring

variable {U : Finset (Fin n)} {A : Type*} [AddCommGroup A]

/- English proof (translation)
Simplify using `only [smul_sub, Finset.sum_sub_distrib]`. Rewrite using `[← Finset.sum_smul, Finset.sum_coe_sort J.1.1 (fun j => Cech.sgn J.1.1 j), Cech.sum_sgn_of_card_two J.2, zero_smul, sub_zero]`.
-/
theorem sum_sgn_smul_sub (φ : Cell U → A) (J : Cech.Idx U 1) :
    ∑ j : J.1.1, Cech.sgn J.1.1 j • (φ (Cech.face J j).1 - φ J.1) =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • φ (Cech.face J j).1 := by
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, Finset.sum_coe_sort J.1.1 (fun j => Cech.sgn J.1.1 j),
    Cech.sum_sgn_of_card_two J.2, zero_smul, sub_zero]

/- English proof (translation)
Set `ψ : Finset (Fin n) → A` to `fun T => if h : T.Nonempty ∧ T ⊆ U then φ ⟨T, h⟩ else 0`. Establish `hψ : ∀ c : Cell U, φ c = ψ c.1` using `fun c => by simp only [ψ, dif_pos c.2]`. Establish `hin : ∀ j : L.1.1, (∑ k : (Cech.face L j).1.1, Cech.sgn (Cech.face L j).1.1 k • φ (Cech.face (Cech.face L j) k).1) = ∑ k ∈ L.1.1.erase j, Cech.sgn (L.1.1.erase j) k • ψ ((L.1.1.erase j).erase k)`. Introduce `j`. Rewrite using `[← Finset.sum_coe_sort (L.1.1.erase j)]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hψ]`. Both sides reduce to the same expression. Simplify using `only [hin]`. Rewrite using `[Finset.sum_coe_sort L.1.1 (fun j => Cech.sgn L.1.1 j • ∑ k ∈ L.1.1.erase j, Cech.sgn (L.1.1.erase j) k • ψ ((L.1.1.erase j).erase k))]`.

Simplify using `only [Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_sigma' L.1.1 (fun j => L.1.1.erase j)]`. Use `Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨j, k⟩ hp`. Take `⟨hj, hk⟩` from `Finset.mem_sigma.mp hp`.

Take `⟨hkj, hk⟩` from `Finset.mem_erase.mp hk`. Simplify using `only`. Rewrite using `[Finset.erase_right_comm, sgn_mul_sgn_erase_swap hj hk (Ne.symm hkj), neg_smul]`. Conclude with `neg_add_cancel _`. Introduce and unpack `⟨j, k⟩ hp _ heq`.

Take `⟨-, hk⟩` from `Finset.mem_sigma.mp hp`. Conclude with `(Finset.mem_erase.mp hk).1 (Sigma.mk.inj_iff.mp heq).1`. Introduce and unpack `⟨j, k⟩ hp`. Take `⟨hj, hk⟩` from `Finset.mem_sigma.mp hp`. Take `⟨hkj, hk⟩` from `Finset.mem_erase.mp hk`.

Conclude with `Finset.mem_sigma.mpr ⟨hk, Finset.mem_erase.mpr ⟨Ne.symm hkj, hj⟩⟩`. Introduce and unpack `⟨j, k⟩ _`. Both sides reduce to the same expression.
-/
theorem sum_sgn_sum_sgn (φ : Cell U → A) (L : Cech.Idx U 2) :
    ∑ j : L.1.1, Cech.sgn L.1.1 j • ∑ k : (Cech.face L j).1.1,
      Cech.sgn (Cech.face L j).1.1 k • φ (Cech.face (Cech.face L j) k).1 = 0 := by
  classical
  let ψ : Finset (Fin n) → A := fun T => if h : T.Nonempty ∧ T ⊆ U then φ ⟨T, h⟩ else 0
  have hψ : ∀ c : Cell U, φ c = ψ c.1 := fun c => by simp only [ψ, dif_pos c.2]
  have hin : ∀ j : L.1.1, (∑ k : (Cech.face L j).1.1,
      Cech.sgn (Cech.face L j).1.1 k • φ (Cech.face (Cech.face L j) k).1) =
        ∑ k ∈ L.1.1.erase j, Cech.sgn (L.1.1.erase j) k • ψ ((L.1.1.erase j).erase k) := by
    intro j
    rw [← Finset.sum_coe_sort (L.1.1.erase j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hψ]
    rfl
  simp only [hin]
  rw [Finset.sum_coe_sort L.1.1 (fun j => Cech.sgn L.1.1 j •
    ∑ k ∈ L.1.1.erase j, Cech.sgn (L.1.1.erase j) k • ψ ((L.1.1.erase j).erase k))]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_sigma' L.1.1 (fun j => L.1.1.erase j)]
  refine Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨j, k⟩ hp
    obtain ⟨hj, hk⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hkj, hk⟩ := Finset.mem_erase.mp hk
    simp only
    rw [Finset.erase_right_comm, sgn_mul_sgn_erase_swap hj hk (Ne.symm hkj), neg_smul]
    exact neg_add_cancel _
  · rintro ⟨j, k⟩ hp _ heq
    obtain ⟨-, hk⟩ := Finset.mem_sigma.mp hp
    exact (Finset.mem_erase.mp hk).1 (Sigma.mk.inj_iff.mp heq).1
  · rintro ⟨j, k⟩ hp
    obtain ⟨hj, hk⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hkj, hk⟩ := Finset.mem_erase.mp hk
    exact Finset.mem_sigma.mpr ⟨hk, Finset.mem_erase.mpr ⟨Ne.symm hkj, hj⟩⟩
  · rintro ⟨j, k⟩ _
    rfl

end Signs

section Twists

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

/- English proof (translation)
Rewrite using `[Submodule.mul_eq_span_mul_set]`. Use `show Submodule.span (chartRing S x I) {z | ∃ q ∈ Q.sub I, ∃ y ∈ F.sub I, z = q • y} = _`. Use `congr 1`. Use extensionality with `z`. Simplify using `only [Set.mem_mul, SetLike.mem_coe, smul_eq_mul]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, hq, y, hy, rfl⟩`. Conclude with `⟨q, hq, y, hy, rfl⟩`. Introduce and unpack `⟨q, hq, y, hy, rfl⟩`. Conclude with `⟨q, hq, y, hy, rfl⟩`.
-/
theorem twist_sub_eq_mul (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  show Submodule.span (chartRing S x I) {z | ∃ q ∈ Q.sub I, ∃ y ∈ F.sub I, z = q • y} = _
  congr 1
  ext z
  simp only [Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨q, hq, y, hy, rfl⟩
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨q, hq, y, hy, rfl⟩

/- English proof (translation)
Use `SubSystem.ext_sub fun I => ?_` and prove the remaining obligations. Rewrite using `[twist_sub_eq_mul, twist_sub_eq_mul, twist_sub_eq_mul, twist_sub_eq_mul, mul_left_comm]`.
-/
theorem twist_twist_comm (F Q R : SubSystem S x Ω) : (F.twist Q).twist R = (F.twist R).twist Q := by
  refine SubSystem.ext_sub fun I => ?_
  rw [twist_sub_eq_mul, twist_sub_eq_mul, twist_sub_eq_mul, twist_sub_eq_mul, mul_left_comm]

/- English proof (translation)
Rewrite using `[twist_sub_eq_mul]`. Use `Submodule.mul_le.mpr fun a ha y hy => ?_` and prove the remaining obligations. Establish `ha' : a ∈ idealMod (x` using `x) J I := ha`. Establish `: ∃ b : chartRing S x I, (b : Ω) = a`. Use `Submodule.span_induction (p := fun a _ => ∃ b : chartRing S x I, (b : Ω) = a) ?_ ?_ ?_ ?_ ha'` and prove the remaining obligations.

Introduce and unpack `_ ⟨f, s, e, _, hs, hfe, hse, rfl⟩`. Conclude with `⟨⟨_, f, s, e, hs, hfe, hse, rfl⟩, rfl⟩`. Conclude with `⟨0, rfl⟩`. Introduce and unpack `_ _ _ _ ⟨b, rfl⟩ ⟨b', rfl⟩`. Conclude with `⟨b + b', rfl⟩`.

Introduce and unpack `r _ _ ⟨b, rfl⟩`. Conclude with `⟨r * b, rfl⟩`. Take `⟨b, rfl⟩` from `this`. Conclude with `(F.sub I).smul_mem b hy`.
-/
theorem twist_idealSys_le (F : SubSystem S x Ω) (J : Ideal (Poly S N)) (I : Chart x) :
    (F.twist (idealSys x J)).sub I ≤ F.sub I := by
  rw [twist_sub_eq_mul]
  refine Submodule.mul_le.mpr fun a ha y hy => ?_
  have ha' : a ∈ idealMod (x := x) J I := ha
  have : ∃ b : chartRing S x I, (b : Ω) = a := by
    refine Submodule.span_induction (p := fun a _ => ∃ b : chartRing S x I, (b : Ω) = a) ?_ ?_ ?_ ?_
      ha'
    · rintro _ ⟨f, s, e, _, hs, hfe, hse, rfl⟩
      exact ⟨⟨_, f, s, e, hs, hfe, hse, rfl⟩, rfl⟩
    · exact ⟨0, rfl⟩
    · rintro _ _ _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
      exact ⟨b + b', rfl⟩
    · rintro r _ _ ⟨b, rfl⟩
      exact ⟨r * b, rfl⟩
  obtain ⟨b, rfl⟩ := this
  exact (F.sub I).smul_mem b hy

/- English proof (translation)
Use `SubSystem.ext_sub fun I => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Rewrite using `[twist_sub_eq_mul]`. Express the relevant statement in the definitionally equal form `M.tilde c I = twistMod S x c I * M.tilde 0 I`.

Rewrite using `[twistMod_eq_span c I hi]`. Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩`. Establish `hs0` using `eval_ne_zero_of_mem_monos I hs`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_span_singleton_mul]`. Use `⟨(x i ^ c)⁻¹ * ((aeval x s)⁻¹ • m), ?_, mul_inv_cancel_left₀ (zpow_ne_zero c hxi) _⟩` and prove the remaining obligations. Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg c`. Use `Submodule.subset_span ⟨m, s * X i ^ n, a, e + n, mul_mem hs (pow_mem (X_mem_monos hi) n), hse.mul (isHomogeneous_X_pow i n), hm, by push_cast; omega, ?_⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul, map_mul, map_pow, aeval_X, zpow_natCast, mul_inv]`.

Expand and normalize the polynomial expressions, which then agree. Use `Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse, M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul, map_pow, aeval_X, zpow_neg, zpow_natCast, inv_inv]`. Expand and normalize the polynomial expressions, which then agree. Use `Submodule.mul_le.mpr fun g hg y hy => ?_` and prove the remaining obligations.

Take `⟨b, rfl⟩` from `Submodule.mem_span_singleton.mp hg`. Establish `hy' : y ∈ Submodule.span (chartRing S x I) {y | ∃ (m : Ω) (s : Poly S N) (a : ℤ) (e : ℕ), s ∈ monos I.1 ∧ s.IsHomogeneous e ∧ m ∈ M.piece a ∧ a - e = 0 ∧ y = (aeval x s)⁻¹ • m}` using `hy`. Establish `key : x i ^ c * y ∈ M.tilde c I`. Use `Submodule.span_induction (p := fun y _ => x i ^ c * y ∈ M.tilde c I) ?_ ?_ ?_ ?_ hy'` and prove the remaining obligations. Introduce and unpack `_ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩`.

Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg c`. Use `Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse, M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul, map_pow, aeval_X, zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree. Use `Submodule.subset_span ⟨m, s * X i ^ n, a, e + n, mul_mem hs (pow_mem (X_mem_monos hi) n), hse.mul (isHomogeneous_X_pow i n), hm, by push_cast; omega, ?_⟩` and prove the remaining obligations.

Simplify using `only [smul_eq_mul, map_mul, map_pow, aeval_X, zpow_neg, zpow_natCast, mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `y y' _ _ h h'`.

Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ h h'`. Introduce `r y _ h`. Rewrite using `[chartRing_smul_def, mul_left_comm]`. Conclude with `(M.tilde c I).smul_mem r h`.

Rewrite using `[chartRing_smul_def, mul_assoc]`. Conclude with `(M.tilde c I).smul_mem b key`.
-/
theorem tildeSys_eq_twist (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ) :
    M.tildeSys c = (M.tildeSys 0).twist (twistSys S x c) := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [twist_sub_eq_mul]
  change M.tilde c I = twistMod S x c I * M.tilde 0 I
  rw [twistMod_eq_span c I hi]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    rw [SetLike.mem_coe, Submodule.mem_span_singleton_mul]
    refine ⟨(x i ^ c)⁻¹ * ((aeval x s)⁻¹ • m), ?_, mul_inv_cancel_left₀ (zpow_ne_zero c hxi) _⟩
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · refine Submodule.subset_span ⟨m, s * X i ^ n, a, e + n, mul_mem hs (pow_mem (X_mem_monos hi) n),
        hse.mul (isHomogeneous_X_pow i n), hm, by push_cast; omega, ?_⟩
      simp only [smul_eq_mul, map_mul, map_pow, aeval_X, zpow_natCast, mul_inv]
      ring
    · refine Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse,
        M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩
      simp only [smul_eq_mul, map_pow, aeval_X, zpow_neg, zpow_natCast, inv_inv]
      ring
  · refine Submodule.mul_le.mpr fun g hg y hy => ?_
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hg
    have hy' : y ∈ Submodule.span (chartRing S x I) {y | ∃ (m : Ω) (s : Poly S N) (a : ℤ) (e : ℕ),
        s ∈ monos I.1 ∧ s.IsHomogeneous e ∧ m ∈ M.piece a ∧ a - e = 0 ∧ y = (aeval x s)⁻¹ • m} := hy
    have key : x i ^ c * y ∈ M.tilde c I := by
      refine Submodule.span_induction (p := fun y _ => x i ^ c * y ∈ M.tilde c I) ?_ ?_ ?_ ?_ hy'
      · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
        obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
        · refine Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse,
            M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩
          simp only [smul_eq_mul, map_pow, aeval_X, zpow_natCast]
          ring
        · refine Submodule.subset_span ⟨m, s * X i ^ n, a, e + n,
            mul_mem hs (pow_mem (X_mem_monos hi) n), hse.mul (isHomogeneous_X_pow i n), hm,
            by push_cast; omega, ?_⟩
          simp only [smul_eq_mul, map_mul, map_pow, aeval_X, zpow_neg, zpow_natCast, mul_inv]
          ring
      · rw [mul_zero]
        exact Submodule.zero_mem _
      · intro y y' _ _ h h'
        rw [mul_add]
        exact Submodule.add_mem _ h h'
      · intro r y _ h
        rw [chartRing_smul_def, mul_left_comm]
        exact (M.tilde c I).smul_mem r h
    rw [chartRing_smul_def, mul_assoc]
    exact (M.tilde c I).smul_mem b key

end Twists

/- English proof (translation)
The claim follows from `Submodule.mem_comap.mp <| (Submodule.Quotient.mk_eq_zero ((Cech.bdry G ρ i).comap (LinearMap.ker (Cech.d G ρ i)).subtype)).mp (@Subsingleton.elim _ h (Submodule.Quotient.mk ⟨z, hz⟩ : Cech.H G ρ i) 0)`.
-/
theorem mem_bdry_of_subsingleton {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
    {G : Cell U → Type w} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
    {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J} {i : ℕ} (h : Subsingleton (Cech.H G ρ i))
    (z : Cech.Cochain G i) (hz : z ∈ LinearMap.ker (Cech.d G ρ i)) : z ∈ Cech.bdry G ρ i :=
  Submodule.mem_comap.mp <| (Submodule.Quotient.mk_eq_zero
    ((Cech.bdry G ρ i).comap (LinearMap.ker (Cech.d G ρ i)).subtype)).mp
    (@Subsingleton.elim _ h (Submodule.Quotient.mk ⟨z, hz⟩ : Cech.H G ρ i) 0)

/- English proof (translation)
Rewrite using `[Cech.sgn, ← mul_pow]`. Evaluate the numerical expressions.
-/
theorem sgn_mul_self {n : ℕ} (L : Finset (Fin n)) (j : Fin n) : Cech.sgn L j * Cech.sgn L j = 1 := by
  rw [Cech.sgn, ← mul_pow]
  norm_num

/- English proof (translation)
Introduce `S _ _ Ω _ _ N x Q J' hJ'`. Take `⟨F, hF, hfg⟩` from `hFam S Ω N x Q J' hJ'`. Take `⟨M, -, hM⟩` from `hExt S Ω N x Ω F hfg`. Take `⟨c₀, hc₀⟩` from `hVan S Ω N x Ω M`. Use `⟨c₀, fun c hc s hs hcompat => ?_⟩` and prove the remaining obligations.

Establish `h0 : M.tildeSys 0 = Q.twist (idealSys x J')`. Rewrite using `[← hF]`. Conclude with `SubSystem.ext_sub fun I => hM I`. Establish `hK : M.tildeSys c = (Q.twist (twistSys S x c)).twist (idealSys x J')`. Rewrite using `[tildeSys_eq_twist, h0, twist_twist_comm]`.

Establish `hsub : Subsingleton (((Q.twist (twistSys S x c)).twist (idealSys x J')).H 1)` using `hK ▸ hc₀ 1 le_rfl c hc`. Use `set Qc := Q.twist (twistSys S x c) with hQc`. Use `set K := Qc.twist (idealSys x J') with hKdef`. Establish `hKQ : ∀ I, K.sub I ≤ Qc.sub I` using `twist_idealSys_le Qc J'`. Use `clear_value K Qc`.

Establish `hmem : ∀ J : Cech.Idx (support x) 1, (∑ j : J.1.1, Cech.sgn J.1.1 j • (s (Cech.face J j).1 - s J.1)) ∈ K.sub J.1` using `fun J => Submodule.sum_mem _ fun j _ => zsmul_mem (hcompat _ _ (Cech.face_subset J j)) _`. Set `w : Cech.Cochain (fun I => K.sub I) 1` to `fun J => ⟨_, hmem J⟩`. Establish `hres : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (y : K.sub I), ((K.res I J h y : K.sub J) : Ω) = y` using `fun _ _ _ _ => rfl`. Establish `hw : w ∈ LinearMap.ker (Cech.d (fun I => K.sub I) K.res 1)`. Rewrite using `[LinearMap.mem_ker]`.

Use function extensionality and compare the values at `L`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Cech.d_apply]`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hres, w, sum_sgn_smul_sub s, Pi.zero_apply, ZeroMemClass.coe_zero]`. Conclude with `sum_sgn_sum_sgn s L`.

Establish `hb : w ∈ Cech.bdry (fun I => K.sub I) K.res 1` using `mem_bdry_of_subsingleton hsub w hw`. Take `⟨v, hv⟩` from `LinearMap.mem_range.mp (show w ∈ LinearMap.range (Cech.d (fun I => K.sub I) K.res 0) from hb)`. Set `ψ : Finset (Fin (N + 1)) → Ω` to `fun T => if h : (T.Nonempty ∧ T ⊆ support x) ∧ T.card = 0 + 1 then s ⟨T, h.1⟩ - (v ⟨⟨T, h.1⟩, h.2⟩ : Ω) else 0`. Establish `hψ : ∀ I : Cech.Idx (support x) 0, ψ I.1.1 = s I.1 - (v I : Ω)` using `fun I => by`. Simplify using `only [ψ]`.

Rewrite using `[dif_pos ⟨I.1.2, I.2⟩]`. Establish `hpair : ∀ J : Cech.Idx (support x) 1, ∑ j : J.1.1, Cech.sgn J.1.1 j • ψ (J.1.1.erase j) = 0`. Introduce `J`. Establish `e` using `congrArg (fun z : Cech.Cochain (fun I => K.sub I) 1 => ((z J : K.sub J.1) : Ω)) hv`. Rewrite `e` using `[Cech.d_apply]`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hres, w, sum_sgn_smul_sub s] at e`. Establish `hj : ∀ j : J.1.1, ψ (J.1.1.erase j) = s (Cech.face J j).1 - (v (Cech.face J j) : Ω)` using `fun j => hψ (Cech.face J j)`. Simplify using `only [hj, smul_sub, Finset.sum_sub_distrib]`. Rewrite using `[e, sub_self]`. Establish `hconst : ∀ a b : Fin (N + 1), x a ≠ 0 → x b ≠ 0 → ψ {a} = ψ {b}`.

Introduce `a b ha hb`. Distinguish the cases in `hab : a = b`. Rewrite using `[hab]`. Establish `hsupp : ({a, b} : Finset (Fin (N + 1))) ⊆ support x`. Rewrite using `[Finset.insert_subset_iff, Finset.singleton_subset_iff]`.

Conclude with `⟨(mem_support x).mpr ha, (mem_support x).mpr hb⟩`. Set `J : Cech.Idx (support x) 1` to `⟨⟨{a, b}, Finset.insert_nonempty _ _, hsupp⟩, Finset.card_pair hab⟩`. Establish `e` using `hpair J`. Establish `e2` using `Cech.sum_sgn_of_card_two (J := ({a, b} : Finset (Fin (N + 1)))) (Finset.card_pair hab)`. Rewrite `e` using `[Finset.sum_coe_sort ({a, b} : Finset (Fin (N + 1))) (fun j => Cech.sgn {a, b} j • ψ (({a, b} : Finset (Fin (N + 1))).erase j))]`.

Rewrite `e`, `e2` using `[Finset.sum_pair hab]`. Establish `ea : ({a, b} : Finset (Fin (N + 1))).erase a = {b}` using `Finset.erase_insert (by simpa using hab)`. Establish `eb : ({a, b} : Finset (Fin (N + 1))).erase b = {a}`. Rewrite using `[Finset.pair_comm]`. Conclude with `Finset.erase_insert (by simpa using Ne.symm hab)`.

Rewrite `e` using `[ea, eb, eq_neg_of_add_eq_zero_right e2, neg_smul, ← sub_eq_add_neg, ← smul_sub]`. Use `congrArg (fun z => Cech.sgn {a, b} a • z) e` as an intermediate fact. Simplify using `only [smul_smul, sgn_mul_self, one_smul, smul_zero, sub_eq_zero] at this`. Conclude with `this.symm`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t : Ω, ∀ a, x a ≠ 0 → t = ψ {a} := by`.

Distinguish the cases in `hne : ∃ i, x i ≠ 0`. Take `⟨i₀, hi₀⟩` from `hne`. Conclude with `⟨ψ {i₀}, fun a ha => hconst i₀ a hi₀ ha⟩`. Simplify using `only [not_exists, not_not] at hne`. Conclude with `⟨0, fun a ha => absurd (hne a) ha⟩`.

Establish `hdiff : ∀ I : Chart x, t - s I ∈ K.sub I`. Introduce `I`. Take `⟨a, haI⟩` from `I.2.1`. Establish `ha : x a ≠ 0` using `(mem_support x).mp (I.2.2 haI)`. Set `c1 : Cech.Idx (support x) 0` to `⟨⟨{a}, Finset.singleton_nonempty a, Finset.singleton_subset_iff.mpr (I.2.2 haI)⟩, Finset.card_singleton a⟩`.

Establish `hsub1 : c1.1.1 ⊆ I.1` using `Finset.singleton_subset_iff.mpr haI`. Rewrite using `[ht a ha, show ψ {a} = s c1.1 - (v c1 : Ω) from hψ c1, show s c1.1 - (v c1 : Ω) - s I = (s c1.1 - s I) - (v c1 : Ω) by ring]`. Conclude with `Submodule.sub_mem _ (hcompat c1.1 I hsub1) (K.mono c1.1 I hsub1 _ (v c1).2)`. Use `⟨t, ?_, hdiff⟩` and prove the remaining obligations. Rewrite using `[SubSystem.secs, Submodule.mem_iInf]`.

Introduce `I`. Establish `: t = s I + (t - s I)` using `by ring`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ (hs I) (hKQ I (hdiff I))`.
-/
theorem proof (hExt : Extension.Statement.{u, w, w})
    (hFam : IdealTwistFamily.Statement.{u, w}) (hVan : TildeVanish.Statement.{u, w, w}) :
    SurjectiveClosed.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x Q J' hJ'
  obtain ⟨F, hF, hfg⟩ := hFam S Ω N x Q J' hJ'
  obtain ⟨M, -, hM⟩ := hExt S Ω N x Ω F hfg
  obtain ⟨c₀, hc₀⟩ := hVan S Ω N x Ω M
  refine ⟨c₀, fun c hc s hs hcompat => ?_⟩
  have h0 : M.tildeSys 0 = Q.twist (idealSys x J') := by
    rw [← hF]
    exact SubSystem.ext_sub fun I => hM I
  have hK : M.tildeSys c = (Q.twist (twistSys S x c)).twist (idealSys x J') := by
    rw [tildeSys_eq_twist, h0, twist_twist_comm]
  have hsub : Subsingleton (((Q.twist (twistSys S x c)).twist (idealSys x J')).H 1) :=
    hK ▸ hc₀ 1 le_rfl c hc
  set Qc := Q.twist (twistSys S x c) with hQc
  set K := Qc.twist (idealSys x J') with hKdef
  have hKQ : ∀ I, K.sub I ≤ Qc.sub I := twist_idealSys_le Qc J'
  clear_value K Qc

  have hmem : ∀ J : Cech.Idx (support x) 1,
      (∑ j : J.1.1, Cech.sgn J.1.1 j • (s (Cech.face J j).1 - s J.1)) ∈ K.sub J.1 :=
    fun J => Submodule.sum_mem _ fun j _ => zsmul_mem (hcompat _ _ (Cech.face_subset J j)) _
  let w : Cech.Cochain (fun I => K.sub I) 1 := fun J => ⟨_, hmem J⟩
  have hres : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (y : K.sub I), ((K.res I J h y : K.sub J) : Ω) = y :=
    fun _ _ _ _ => rfl
  have hw : w ∈ LinearMap.ker (Cech.d (fun I => K.sub I) K.res 1) := by
    rw [LinearMap.mem_ker]
    funext L
    apply Subtype.ext
    rw [Cech.d_apply]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hres, w, sum_sgn_smul_sub s,
      Pi.zero_apply, ZeroMemClass.coe_zero]
    exact sum_sgn_sum_sgn s L

  have hb : w ∈ Cech.bdry (fun I => K.sub I) K.res 1 := mem_bdry_of_subsingleton hsub w hw
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp
    (show w ∈ LinearMap.range (Cech.d (fun I => K.sub I) K.res 0) from hb)

  classical
  let ψ : Finset (Fin (N + 1)) → Ω := fun T =>
    if h : (T.Nonempty ∧ T ⊆ support x) ∧ T.card = 0 + 1 then s ⟨T, h.1⟩ - (v ⟨⟨T, h.1⟩, h.2⟩ : Ω)
    else 0
  have hψ : ∀ I : Cech.Idx (support x) 0, ψ I.1.1 = s I.1 - (v I : Ω) := fun I => by
    simp only [ψ]
    rw [dif_pos ⟨I.1.2, I.2⟩]
  have hpair : ∀ J : Cech.Idx (support x) 1,
      ∑ j : J.1.1, Cech.sgn J.1.1 j • ψ (J.1.1.erase j) = 0 := by
    intro J
    have e := congrArg (fun z : Cech.Cochain (fun I => K.sub I) 1 => ((z J : K.sub J.1) : Ω)) hv
    rw [Cech.d_apply] at e
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hres, w, sum_sgn_smul_sub s] at e
    have hj : ∀ j : J.1.1, ψ (J.1.1.erase j) = s (Cech.face J j).1 - (v (Cech.face J j) : Ω) :=
      fun j => hψ (Cech.face J j)
    simp only [hj, smul_sub, Finset.sum_sub_distrib]
    rw [e, sub_self]

  have hconst : ∀ a b : Fin (N + 1), x a ≠ 0 → x b ≠ 0 → ψ {a} = ψ {b} := by
    intro a b ha hb
    by_cases hab : a = b
    · rw [hab]
    have hsupp : ({a, b} : Finset (Fin (N + 1))) ⊆ support x := by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨(mem_support x).mpr ha, (mem_support x).mpr hb⟩
    let J : Cech.Idx (support x) 1 := ⟨⟨{a, b}, Finset.insert_nonempty _ _, hsupp⟩, Finset.card_pair hab⟩
    have e := hpair J
    have e2 := Cech.sum_sgn_of_card_two (J := ({a, b} : Finset (Fin (N + 1)))) (Finset.card_pair hab)
    rw [Finset.sum_coe_sort ({a, b} : Finset (Fin (N + 1)))
      (fun j => Cech.sgn {a, b} j • ψ (({a, b} : Finset (Fin (N + 1))).erase j))] at e
    rw [Finset.sum_pair hab] at e e2
    have ea : ({a, b} : Finset (Fin (N + 1))).erase a = {b} :=
      Finset.erase_insert (by simpa using hab)
    have eb : ({a, b} : Finset (Fin (N + 1))).erase b = {a} := by
      rw [Finset.pair_comm]
      exact Finset.erase_insert (by simpa using Ne.symm hab)
    rw [ea, eb, eq_neg_of_add_eq_zero_right e2, neg_smul, ← sub_eq_add_neg, ← smul_sub] at e
    have := congrArg (fun z => Cech.sgn {a, b} a • z) e
    simp only [smul_smul, sgn_mul_self, one_smul, smul_zero, sub_eq_zero] at this
    exact this.symm
  obtain ⟨t, ht⟩ : ∃ t : Ω, ∀ a, x a ≠ 0 → t = ψ {a} := by
    by_cases hne : ∃ i, x i ≠ 0
    · obtain ⟨i₀, hi₀⟩ := hne
      exact ⟨ψ {i₀}, fun a ha => hconst i₀ a hi₀ ha⟩
    · simp only [not_exists, not_not] at hne
      exact ⟨0, fun a ha => absurd (hne a) ha⟩

  have hdiff : ∀ I : Chart x, t - s I ∈ K.sub I := by
    intro I
    obtain ⟨a, haI⟩ := I.2.1
    have ha : x a ≠ 0 := (mem_support x).mp (I.2.2 haI)
    let c1 : Cech.Idx (support x) 0 :=
      ⟨⟨{a}, Finset.singleton_nonempty a, Finset.singleton_subset_iff.mpr (I.2.2 haI)⟩,
        Finset.card_singleton a⟩
    have hsub1 : c1.1.1 ⊆ I.1 := Finset.singleton_subset_iff.mpr haI
    rw [ht a ha, show ψ {a} = s c1.1 - (v c1 : Ω) from hψ c1,
      show s c1.1 - (v c1 : Ω) - s I = (s c1.1 - s I) - (v c1 : Ω) by ring]
    exact Submodule.sub_mem _ (hcompat c1.1 I hsub1) (K.mono c1.1 I hsub1 _ (v c1).2)
  refine ⟨t, ?_, hdiff⟩
  rw [SubSystem.secs, Submodule.mem_iInf]
  intro I
  have : t = s I + (t - s I) := by ring
  rw [this]
  exact Submodule.add_mem _ (hs I) (hKQ I (hdiff I))

end SurjectiveClosed

end

end GroundTheory.Heights₂.Heights.Kleiman
