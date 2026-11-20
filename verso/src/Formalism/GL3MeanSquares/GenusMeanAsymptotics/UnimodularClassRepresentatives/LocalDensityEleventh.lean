import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNotMemOfSol

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.vectorCountBounds

open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms hermitianFormColumns

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

/- English proof (translation)
Use `haveI := finite_quot (K := K) h𝔭 k`. Use `infer_instance`.
-/
theorem finite_vec {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Finite (m → 𝓞 K ⧸ extP K 𝔭 ^ k) := by
  haveI := finite_quot (K := K) h𝔭 k
  infer_instance

/- English proof (translation)
Use `haveI := finite_quot (K := K) h𝔭 k`. Establish `h1 : Nat.card (m → 𝓞 K ⧸ extP K 𝔭 ^ k) = Nat.card (𝓞 K ⧸ extP K 𝔭 ^ k) ^ Fintype.card m`. Rewrite using `[Nat.card_fun, ← Nat.card_eq_fintype_card]`. Rewrite using `[h1, absNorm_extP_pow hK Fact.out h𝔭 k, ← pow_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_vec (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (m → 𝓞 K ⧸ extP K 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m)) := by
  haveI := finite_quot (K := K) h𝔭 k
  have h1 : Nat.card (m → 𝓞 K ⧸ extP K 𝔭 ^ k) =
      Nat.card (𝓞 K ⧸ extP K 𝔭 ^ k) ^ Fintype.card m := by
    rw [Nat.card_fun, ← Nat.card_eq_fintype_card]
  rw [h1, absNorm_extP_pow hK Fact.out h𝔭 k, ← pow_mul]
  congr 1
  ring

/- English proof (translation)
Use `haveI := finite_vec (m := m) (K := K) h𝔭 k`. Rewrite using `[← card_vec hK h𝔭 k]`. Conclude with `Finite.card_subtype_le p`.
-/
theorem card_sub_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (p : (m → 𝓞 K ⧸ extP K 𝔭 ^ k) → Prop) :
    Nat.card {x // p x} ≤ Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m)) := by
  haveI := finite_vec (m := m) (K := K) h𝔭 k
  rw [← card_vec hK h𝔭 k]
  exact Finite.card_subtype_le p

/- English proof (translation)
Establish `h5 : Ideal.absNorm 𝔭 ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `idealPowerSpanBounds.ne_bot h𝔭`. Establish `h6 : Ideal.absNorm 𝔭 ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`.

Conclude with `h𝔭.ne_top`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_le_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 2 ≤ Ideal.absNorm 𝔭 := by
  have h5 : Ideal.absNorm 𝔭 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact idealPowerSpanBounds.ne_bot h𝔭
  have h6 : Ideal.absNorm 𝔭 ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact h𝔭.ne_top
  omega

/- English proof (translation)
Establish `hq` using `absNorm_pos h𝔭`. Establish `small : ∀ k, k ≤ 2 * c + 1 → nkQ 𝔭 k c H n ≤ Ideal.absNorm 𝔭 ^ (2 * c + 1) * Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m - 1))`. Introduce `k hk`. Use `(card_sub_le hK h𝔭 k _).trans ?_` and prove the remaining obligations. Rewrite using `[← pow_add]`.

Apply `Nat.pow_le_pow_right hq` to reduce the goal to its premises. Establish `: k * (2 * Fintype.card m) = k + k * (2 * Fintype.card m - 1)`. Take `⟨M, hM⟩ : ∃ M, Fintype.card m = M + 1` from `⟨Fintype.card m - 1, by omega⟩`. Rewrite using `[hM]`. Establish `: 2 * (M + 1) - 1 = 2 * M + 1` using `by omega`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Use linear arithmetic over natural numbers and integers. Break down `le_total k (2 * c + 1) with hk | hk` into its components or cases. Conclude with `small k hk`.

Proceed by induction on `k, hk using Nat.le_induction with`. Consider the case `base => exact small _ le_rfl`. Consider the case `succ k hk ih`. Establish `h1` using `nkQ_succ hK h𝔭 hH n hk`. Apply `Nat.le_of_mul_le_mul_right _ hq` to reduce the goal to its premises.

Rewrite using `[h1]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨M, hM⟩ : ∃ M, Fintype.card m = M + 1` from `⟨Fintype.card m - 1, by omega⟩`. Rewrite using `[hM]`. Establish `: 2 * (M + 1) - 1 = 2 * M + 1` using `by omega`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nkQ_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) (n : 𝓞 F) (c : ℕ) (hm : 1 ≤ Fintype.card m) (k : ℕ) :
    nkQ 𝔭 k c H n ≤ Ideal.absNorm 𝔭 ^ (2 * c + 1) * Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m - 1)) := by
  have hq := absNorm_pos h𝔭
  have small : ∀ k, k ≤ 2 * c + 1 → nkQ 𝔭 k c H n ≤
      Ideal.absNorm 𝔭 ^ (2 * c + 1) * Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m - 1)) := by
    intro k hk
    refine (card_sub_le hK h𝔭 k _).trans ?_
    rw [← pow_add]
    apply Nat.pow_le_pow_right hq
    have : k * (2 * Fintype.card m) = k + k * (2 * Fintype.card m - 1) := by
      obtain ⟨M, hM⟩ : ∃ M, Fintype.card m = M + 1 := ⟨Fintype.card m - 1, by omega⟩
      rw [hM]
      have : 2 * (M + 1) - 1 = 2 * M + 1 := by omega
      rw [this]; ring
    omega
  rcases le_total k (2 * c + 1) with hk | hk
  · exact small k hk
  · induction k, hk using Nat.le_induction with
    | base => exact small _ le_rfl
    | succ k hk ih =>
      have h1 := nkQ_succ hK h𝔭 hH n hk
      apply Nat.le_of_mul_le_mul_right _ hq
      rw [h1]
      calc Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * nkQ 𝔭 k c H n
          ≤ Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * (Ideal.absNorm 𝔭 ^ (2 * c + 1) *
            Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m - 1))) := Nat.mul_le_mul_left _ ih
        _ = _ := by
          obtain ⟨M, hM⟩ : ∃ M, Fintype.card m = M + 1 := ⟨Fintype.card m - 1, by omega⟩
          rw [hM]
          have : 2 * (M + 1) - 1 = 2 * M + 1 := by omega
          rw [this]
          ring

def nkB (𝔭 : Ideal (𝓞 F)) (k c : ℕ) (H : Matrix m m (𝓞 K)) (n : 𝓞 F) : ℕ :=
  Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // ¬ Qc 𝔭 k c H x ∧
    fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)}

/- English proof (translation)
Use `haveI := finite_vec (m := m) (K := K) h𝔭 k`. Unfold `nkM nkQ nkB`. Establish `e1 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // Qc 𝔭 k c H x ∧ fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} = Nat.card {y : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} // Qc 𝔭 k c H y.1}` using `Nat.card_congr ((Equiv.subtypeEquivRight (fun x => and_comm)).trans (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)`. Establish `e2 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // ¬ Qc 𝔭 k c H x ∧ fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} = Nat.card {y : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} // ¬ Qc 𝔭 k c H y.1}` using `Nat.card_congr ((Equiv.subtypeEquivRight (fun x => and_comm)).trans (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)`. Rewrite using `[e1, e2, ← Nat.card_sum]`.

Conclude with `Nat.card_congr (Equiv.sumCompl _).symm`.
-/
theorem nkM_eq_add {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k c : ℕ) (H : Matrix m m (𝓞 K)) (n : 𝓞 F) :
    nkM 𝔭 k H n = nkQ 𝔭 k c H n + nkB 𝔭 k c H n := by
  classical
  haveI := finite_vec (m := m) (K := K) h𝔭 k
  unfold nkM nkQ nkB
  have e1 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // Qc 𝔭 k c H x ∧
      fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} =
      Nat.card {y : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k //
        fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} // Qc 𝔭 k c H y.1} :=
    Nat.card_congr ((Equiv.subtypeEquivRight (fun x => and_comm)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)
  have e2 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // ¬ Qc 𝔭 k c H x ∧
      fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} =
      Nat.card {y : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k //
        fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} // ¬ Qc 𝔭 k c H y.1} :=
    Nat.card_congr ((Equiv.subtypeEquivRight (fun x => and_comm)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)
  rw [e1, e2, ← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl _).symm

/- English proof (translation)
Use `haveI := finite_quot (K := K) h𝔭 k`. Use `haveI := finite_quot (K := K) h𝔭 (k + 1)`. Use `haveI : Fintype (𝓞 K ⧸ extP K 𝔭 ^ k) := Fintype.ofFinite _`. Use `haveI : Fintype (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) := Fintype.ofFinite _`. Establish `hF : IsFixF K F` using `Fact.out`.

Establish `hz : ∀ w : 𝓞 K ⧸ extP K 𝔭 ^ k, Nat.card {z // piQ K 𝔭 k z = w} = Ideal.absNorm 𝔭 ^ 2`. Introduce `w`. Take `⟨z0, hz0⟩` from `piQ_surjective (K := K) 𝔭 k w`. Rewrite using `[← card_ker_piQ hK hF h𝔭 k]`. Conclude with `Nat.card_congr { toFun := fun z => ⟨z.1 - z0, by rw [RingHom.mem_ker, map_sub, z.2, hz0, sub_self]⟩ invFun := fun q => ⟨q.1 + z0, by rw [map_add, RingHom.mem_ker.mp q.2, hz0, zero_add]⟩ left_inv := fun z => Subtype.ext (sub_add_cancel _ _) right_inv := fun q => Subtype.ext (add_s …`.

Establish `hfib : ∀ y : m → 𝓞 K ⧸ extP K 𝔭 ^ k, Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // (fun i => piQ K 𝔭 k (x i)) = y} = Ideal.absNorm 𝔭 ^ (2 * Fintype.card m)`. Introduce `y`. Establish `e : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // (fun i => piQ K 𝔭 k (x i)) = y} ≃ ((i : m) → {z // piQ K 𝔭 k z = y i})` using `(Equiv.subtypeEquivRight (fun x => funext_iff)).trans (Equiv.subtypePiEquivPi (p := fun i z => piQ K 𝔭 k z = y i))`. Rewrite using `[Nat.card_congr e, Nat.card_pi]`. Simplify using `only [hz, Finset.prod_const, Finset.card_univ]`.

Rewrite using `[← pow_mul]`. Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]`. Rewrite using `[Finset.card_eq_sum_card_fiberwise (f := fun x => fun i => piQ K 𝔭 k (x i)) (t := Finset.univ.filter T) ?_]`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => Ideal.absNorm 𝔭 ^ (2 * Fintype.card m)) ?_, Finset.sum_const, smul_eq_mul, mul_comm]`. Introduce `b hb`.

Rewrite `hb` using `[Finset.mem_filter]`. Rewrite using `[← hfib b, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Apply `congrArg Finset.card` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.

Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.2`. Introduce `h`. Conclude with `⟨h ▸ hb.2, h⟩`. Introduce `x hx`.

Simplify using `using hx`.
-/
theorem card_preimage_piQ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (T : (m → 𝓞 K ⧸ extP K 𝔭 ^ k) → Prop) :
    Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // T (fun i => piQ K 𝔭 k (x i))} =
      Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * Nat.card {x // T x} := by
  classical
  haveI := finite_quot (K := K) h𝔭 k
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  haveI : Fintype (𝓞 K ⧸ extP K 𝔭 ^ k) := Fintype.ofFinite _
  haveI : Fintype (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) := Fintype.ofFinite _
  have hF : IsFixF K F := Fact.out
  have hz : ∀ w : 𝓞 K ⧸ extP K 𝔭 ^ k, Nat.card {z // piQ K 𝔭 k z = w} = Ideal.absNorm 𝔭 ^ 2 := by
    intro w
    obtain ⟨z0, hz0⟩ := piQ_surjective (K := K) 𝔭 k w
    rw [← card_ker_piQ hK hF h𝔭 k]
    exact Nat.card_congr
      { toFun := fun z => ⟨z.1 - z0, by rw [RingHom.mem_ker, map_sub, z.2, hz0, sub_self]⟩
        invFun := fun q => ⟨q.1 + z0, by rw [map_add, RingHom.mem_ker.mp q.2, hz0, zero_add]⟩
        left_inv := fun z => Subtype.ext (sub_add_cancel _ _)
        right_inv := fun q => Subtype.ext (add_sub_cancel_right _ _) }
  have hfib : ∀ y : m → 𝓞 K ⧸ extP K 𝔭 ^ k,
      Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // (fun i => piQ K 𝔭 k (x i)) = y} =
        Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) := by
    intro y
    have e : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // (fun i => piQ K 𝔭 k (x i)) = y} ≃
        ((i : m) → {z // piQ K 𝔭 k z = y i}) :=
      (Equiv.subtypeEquivRight (fun x => funext_iff)).trans
        (Equiv.subtypePiEquivPi (p := fun i z => piQ K 𝔭 k z = y i))
    rw [Nat.card_congr e, Nat.card_pi]
    simp only [hz, Finset.prod_const, Finset.card_univ]
    rw [← pow_mul]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => fun i => piQ K 𝔭 k (x i))
    (t := Finset.univ.filter T) ?_]
  · rw [Finset.sum_congr rfl (g := fun _ => Ideal.absNorm 𝔭 ^ (2 * Fintype.card m)) ?_,
      Finset.sum_const, smul_eq_mul, mul_comm]
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [← hfib b, Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hb.2, h⟩
  · intro x hx
    simpa using hx

/- English proof (translation)
Establish `hs : ∀ i, star (ι a * y i) = ι a * star (y i)` using `fun i => by`. Rewrite using `[star_mul', idealPowerSpanBounds.star_def (ι a), conjO_map hF]`. Simplify using `only [fm, dotProduct, Matrix.mulVec, Pi.star_apply, hs, map_mul, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fm_smul (hF : IsFixF K F) (H : Matrix m m (𝓞 K)) (a : 𝓞 F) (y : m → 𝓞 K) :
    fm H (fun i => ι a * y i) (fun i => ι a * y i) = ι (a * a) * fm H y y := by
  have hs : ∀ i, star (ι a * y i) = ι a * star (y i) := fun i => by
    rw [star_mul', idealPowerSpanBounds.star_def (ι a), conjO_map hF]
  simp only [fm, dotProduct, Matrix.mulVec, Pi.star_apply, hs, map_mul, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/- English proof (translation)
Establish `hF : IsFixF K F` using `Fact.out`. Use `h𝔭.isPrime` as an intermediate fact. Choose the witnesses or unpack the hypotheses as in `⟨π0, hπ1, hπ2⟩ : ∃ π0 ∈ 𝔭, π0 ∉ 𝔭 ^ (1 + 1) := by`. Take `⟨x, hx, hx'⟩` from `SetLike.exists_of_lt (Ideal.pow_succ_lt_pow (ne_bot h𝔭) 1)`. Conclude with `⟨x, by simpa using hx, hx'⟩`.

Establish `hbad : ∀ x : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 2) // ¬ Qc 𝔭 (k + 2) d H x ∧ fm (H.map (mkk K 𝔭 (k + 2))) x x = mkk K 𝔭 (k + 2) (ι n)}, ∃ y : m → 𝓞 K, (fun i => mkk K 𝔭 (k + 2) (ι π0 * y i)) = x.1`. Introduce `x`. Take `⟨x0, hx0⟩` from `exists_liftv 𝔭 _ x.1`. Establish `h1` using `x.2.1`. Rewrite `h1` using `[← hx0, Qc_mk hdk]`.

Use `push Not at h1`. Establish `h2 : ∀ i, x0 i ∈ extP K 𝔭 ^ 1`. Introduce `i`. Establish `h3` using `vecMul_mem h1 H.adjugate i`. Rewrite `h3` using `[vecMul_adjugate, hD]`.

Establish `h4 : star (x0 i) ∈ extP K 𝔭 ^ 1` using `mem_of_mul_mem h𝔭 hDd h3`. Establish `h5` using `conjO_mem_pow hF 𝔭 1 _ h4`. Rewrite `h5` using `[← star_def, star_star]`. Then use the resulting hypothesis. Establish `h3 : ∀ i, ∃ y, x0 i - ι π0 * y ∈ extP K 𝔭 ^ (k + 2)`. Introduce `i`.

Take `⟨a, ha, b, hb, e⟩` from `Submodule.mem_sup.1 (map_pow_le_span_sup h𝔭 hπ2 (k + 2) (h2 i))`. Take `⟨y, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `: x0 i - ι π0 * y = b` using `by rw [← e]; ring`. Rewrite using `[this]`.

Conclude with `hb`. Use `choose y hy using h3`. Conclude with `⟨y, by rw [← hx0]; funext i; exact (Ideal.Quotient.eq.2 (hy i)).symm⟩`. Use `choose Y hY using hbad`. Establish `hval : ∀ y : m → 𝓞 K, ∃ a : 𝓞 F, ι a = fm H y y` using `fun y => (conjO_eq_iff_mem_range hF _).1 (by rw [← star_def, ← fm_star hH])`.

Establish `hsol : ∀ x, ι (π0 * π0) * fm H (Y x) (Y x) - ι n ∈ extP K 𝔭 ^ (k + 2)`. Introduce `x`. Establish `h1` using `x.2.2`. Rewrite `h1` using `[← hY x, mk_fm, fm_smul hF]`. Conclude with `Ideal.Quotient.eq.1 h1`.

Distinguish the cases in `hne : Nonempty {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 2) // ¬ Qc 𝔭 (k + 2) d H x ∧ fm (H.map (mkk K 𝔭 (k + 2))) x x = mkk K 𝔭 (k + 2) (ι n)}`. Take `⟨x₀⟩` from `hne`. Take `⟨n', hn'⟩` from `hval (Y x₀)`. Use `⟨n', ?_⟩` and prove the remaining obligations. Unfold `nkM nkB`.

Rewrite using `[← card_preimage_piQ hK h𝔭 k (fun z => fm (H.map (mkk K 𝔭 k)) z z = mkk K 𝔭 k (ι n'))]`. Use `finite_vec (K := K) (m := m) h𝔭 (k + 1)` as an intermediate fact. Use `Nat.card_le_card_of_injective (fun x => ⟨fun i => mkk K 𝔭 (k + 1) (Y x i), ?_⟩) ?_` and prove the remaining obligations. Use `show fm (H.map (mkk K 𝔭 k)) (fun i => mkk K 𝔭 k (Y x i)) (fun i => mkk K 𝔭 k (Y x i)) = _`. Rewrite using `[mk_fm]`.

Apply `Ideal.Quotient.eq.2` to reduce the goal to its premises. Establish `hπ : π0 * π0 ∉ 𝔭 ^ (1 + 1 + 1)` using `mul_notMem h𝔭.isPrime (ne_bot h𝔭) hπ2 hπ2`. Apply `mem_of_mul_mem h𝔭 hπ` to reduce the goal to its premises. Establish `: ι (π0 * π0) * (fm H (Y x) (Y x) - ι n') = (ι (π0 * π0) * fm H (Y x) (Y x) - ι n) - (ι (π0 * π0) * fm H (Y x₀) (Y x₀) - ι n)` using `by rw [hn']; ring`. Rewrite using `[this, show 1 + 1 + k = k + 2 by ring]`.

Conclude with `sub_mem (hsol x) (hsol x₀)`. Introduce `x x' hxx`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hY x, ← hY x']`. Use function extensionality and compare the values at `i`.

Apply `Ideal.Quotient.eq.2` to reduce the goal to its premises. Establish `h1 : Y x i - Y x' i ∈ extP K 𝔭 ^ (k + 1)` using `Ideal.Quotient.eq.1 (congrFun (congrArg Subtype.val hxx) i)`. Establish `h2 : ι π0 ∈ extP K 𝔭` using `Ideal.mem_map_of_mem _ hπ1`. Rewrite using `[← mul_sub, pow_succ', ]`. Conclude with `Ideal.mul_mem_mul h2 h1`.

Use `⟨0, ?_⟩` and prove the remaining obligations. Unfold `nkB`. Rewrite `hne` using `[not_nonempty_iff]`. Rewrite using `[Nat.card_of_isEmpty]`. Conclude with `Nat.zero_le _`.
-/
theorem nkB_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) {D : 𝓞 F} (hD : H.det = ι D) {d : ℕ}
    (hDd : D ∉ 𝔭 ^ (d + 1)) (n : 𝓞 F) (k : ℕ) (hdk : d + 1 ≤ k + 2) :
    ∃ n' : 𝓞 F, nkB 𝔭 (k + 2) d H n ≤ Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * nkM 𝔭 k H n' := by
  have hF : IsFixF K F := Fact.out
  have := h𝔭.isPrime
  obtain ⟨π0, hπ1, hπ2⟩ : ∃ π0 ∈ 𝔭, π0 ∉ 𝔭 ^ (1 + 1) := by
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow (ne_bot h𝔭) 1)
    exact ⟨x, by simpa using hx, hx'⟩
  have hbad : ∀ x : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 2) // ¬ Qc 𝔭 (k + 2) d H x ∧
      fm (H.map (mkk K 𝔭 (k + 2))) x x = mkk K 𝔭 (k + 2) (ι n)},
      ∃ y : m → 𝓞 K, (fun i => mkk K 𝔭 (k + 2) (ι π0 * y i)) = x.1 := by
    intro x
    obtain ⟨x0, hx0⟩ := exists_liftv 𝔭 _ x.1
    have h1 := x.2.1
    rw [← hx0, Qc_mk hdk] at h1
    push Not at h1
    have h2 : ∀ i, x0 i ∈ extP K 𝔭 ^ 1 := by
      intro i
      have h3 := vecMul_mem h1 H.adjugate i
      rw [vecMul_adjugate, hD] at h3
      have h4 : star (x0 i) ∈ extP K 𝔭 ^ 1 := mem_of_mul_mem h𝔭 hDd h3
      have h5 := conjO_mem_pow hF 𝔭 1 _ h4
      rwa [← star_def, star_star] at h5
    have h3 : ∀ i, ∃ y, x0 i - ι π0 * y ∈ extP K 𝔭 ^ (k + 2) := by
      intro i
      obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (map_pow_le_span_sup h𝔭 hπ2 (k + 2) (h2 i))
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      refine ⟨y, ?_⟩
      have : x0 i - ι π0 * y = b := by rw [← e]; ring
      rw [this]; exact hb
    choose y hy using h3
    exact ⟨y, by rw [← hx0]; funext i; exact (Ideal.Quotient.eq.2 (hy i)).symm⟩
  choose Y hY using hbad
  have hval : ∀ y : m → 𝓞 K, ∃ a : 𝓞 F, ι a = fm H y y := fun y =>
    (conjO_eq_iff_mem_range hF _).1 (by rw [← star_def, ← fm_star hH])
  have hsol : ∀ x, ι (π0 * π0) * fm H (Y x) (Y x) - ι n ∈ extP K 𝔭 ^ (k + 2) := by
    intro x
    have h1 := x.2.2
    rw [← hY x, mk_fm, fm_smul hF] at h1
    exact Ideal.Quotient.eq.1 h1
  by_cases hne : Nonempty {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 2) // ¬ Qc 𝔭 (k + 2) d H x ∧
      fm (H.map (mkk K 𝔭 (k + 2))) x x = mkk K 𝔭 (k + 2) (ι n)}
  · obtain ⟨x₀⟩ := hne
    obtain ⟨n', hn'⟩ := hval (Y x₀)
    refine ⟨n', ?_⟩
    unfold nkM nkB
    rw [← card_preimage_piQ hK h𝔭 k (fun z => fm (H.map (mkk K 𝔭 k)) z z = mkk K 𝔭 k (ι n'))]
    have := finite_vec (K := K) (m := m) h𝔭 (k + 1)
    refine Nat.card_le_card_of_injective (fun x => ⟨fun i => mkk K 𝔭 (k + 1) (Y x i), ?_⟩) ?_
    · show fm (H.map (mkk K 𝔭 k)) (fun i => mkk K 𝔭 k (Y x i)) (fun i => mkk K 𝔭 k (Y x i)) = _
      rw [mk_fm]
      apply Ideal.Quotient.eq.2
      have hπ : π0 * π0 ∉ 𝔭 ^ (1 + 1 + 1) := mul_notMem h𝔭.isPrime (ne_bot h𝔭) hπ2 hπ2
      apply mem_of_mul_mem h𝔭 hπ
      have : ι (π0 * π0) * (fm H (Y x) (Y x) - ι n') = (ι (π0 * π0) * fm H (Y x) (Y x) - ι n) -
          (ι (π0 * π0) * fm H (Y x₀) (Y x₀) - ι n) := by rw [hn']; ring
      rw [this, show 1 + 1 + k = k + 2 by ring]
      exact sub_mem (hsol x) (hsol x₀)
    · intro x x' hxx
      apply Subtype.ext
      rw [← hY x, ← hY x']
      funext i
      apply Ideal.Quotient.eq.2
      have h1 : Y x i - Y x' i ∈ extP K 𝔭 ^ (k + 1) :=
        Ideal.Quotient.eq.1 (congrFun (congrArg Subtype.val hxx) i)
      have h2 : ι π0 ∈ extP K 𝔭 := Ideal.mem_map_of_mem _ hπ1
      rw [← mul_sub, pow_succ', ]
      exact Ideal.mul_mem_mul h2 h1
  · refine ⟨0, ?_⟩
    unfold nkB
    rw [not_nonempty_iff] at hne
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/- English proof (translation)
Establish `hq` using `absNorm_pos h𝔭`. Establish `hq2` using `two_le_absNorm h𝔭`. Take `⟨M, hM⟩ : ∃ M, Fintype.card m = M + 2` from `⟨Fintype.card m - 2, by omega⟩`. Establish `hM' : 2 * (M + 2) - 1 = 2 * M + 3` using `by omega`. Proceed by induction on `k using Nat.strong_induction_on with`.

Consider the case `_ k ih`. Introduce `n`. Break down `le_or_gt k (2 * d + 1) with hk | hk` into its components or cases. Use `(card_sub_le hK h𝔭 k _).trans ?_` and prove the remaining obligations. Rewrite using `[hM, hM', mul_assoc, ← pow_add]`.

Use `le_trans ?_ (Nat.le_mul_of_pos_left _ (by norm_num))` and prove the remaining obligations. Apply `Nat.pow_le_pow_right hq` to reduce the goal to its premises. Establish `: k * (2 * (M + 2)) = k + k * (2 * M + 3)` using `by ring`. Use linear arithmetic over natural numbers and integers. Take `⟨k', rfl⟩ : ∃ k', k = k' + 2` from `⟨k - 2, by omega⟩`.

Take `⟨n', hn'⟩` from `nkB_le hK h𝔭 hH hD hDd n k' (by omega)`. Establish `h1` using `nkQ_le hK h𝔭 hH n d (by omega) (k' + 2)`. Establish `h2` using `ih k' (by omega) n'`. Rewrite using `[nkM_eq_add h𝔭 (k' + 2) d H n]`. Rewrite `*` using `[hM, hM']`.

Establish `h3 : nkB 𝔭 (k' + 2) d H n ≤ Ideal.absNorm 𝔭 ^ (2 * d + 1) * Ideal.absNorm 𝔭 ^ ((k' + 2) * (2 * M + 3))`. Use `hn'.trans ((Nat.mul_le_mul_left _ h2).trans ?_)` and prove the remaining obligations. Establish `e1 : Ideal.absNorm 𝔭 ^ ((k' + 2) * (2 * M + 3)) = Ideal.absNorm 𝔭 ^ (2 * (M + 2)) * Ideal.absNorm 𝔭 * Ideal.absNorm 𝔭 ^ (2 * M + 1) * Ideal.absNorm 𝔭 ^ (k' * (2 * M + 3))`. Rewrite using `[← pow_succ, ← pow_add, ← pow_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Establish `h4 : 1 ≤ Ideal.absNorm 𝔭 ^ (2 * M + 1)` using `Nat.one_le_pow _ _ hq`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nkM_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) {D : 𝓞 F} (hD : H.det = ι D) {d : ℕ}
    (hDd : D ∉ 𝔭 ^ (d + 1)) (hm : 2 ≤ Fintype.card m) (k : ℕ) : ∀ n : 𝓞 F,
    nkM 𝔭 k H n ≤ 2 * Ideal.absNorm 𝔭 ^ (2 * d + 1) *
      Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m - 1)) := by
  have hq := absNorm_pos h𝔭
  have hq2 := two_le_absNorm h𝔭
  obtain ⟨M, hM⟩ : ∃ M, Fintype.card m = M + 2 := ⟨Fintype.card m - 2, by omega⟩
  have hM' : 2 * (M + 2) - 1 = 2 * M + 3 := by omega
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n
    rcases le_or_gt k (2 * d + 1) with hk | hk
    · refine (card_sub_le hK h𝔭 k _).trans ?_
      rw [hM, hM', mul_assoc, ← pow_add]
      refine le_trans ?_ (Nat.le_mul_of_pos_left _ (by norm_num))
      apply Nat.pow_le_pow_right hq
      have : k * (2 * (M + 2)) = k + k * (2 * M + 3) := by ring
      omega
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      obtain ⟨n', hn'⟩ := nkB_le hK h𝔭 hH hD hDd n k' (by omega)
      have h1 := nkQ_le hK h𝔭 hH n d (by omega) (k' + 2)
      have h2 := ih k' (by omega) n'
      rw [nkM_eq_add h𝔭 (k' + 2) d H n]
      rw [hM, hM'] at *
      have h3 : nkB 𝔭 (k' + 2) d H n ≤ Ideal.absNorm 𝔭 ^ (2 * d + 1) *
          Ideal.absNorm 𝔭 ^ ((k' + 2) * (2 * M + 3)) := by
        refine hn'.trans ((Nat.mul_le_mul_left _ h2).trans ?_)
        have e1 : Ideal.absNorm 𝔭 ^ ((k' + 2) * (2 * M + 3)) = Ideal.absNorm 𝔭 ^ (2 * (M + 2)) *
            Ideal.absNorm 𝔭 * Ideal.absNorm 𝔭 ^ (2 * M + 1) * Ideal.absNorm 𝔭 ^ (k' * (2 * M + 3)) := by
          rw [← pow_succ, ← pow_add, ← pow_add]
          congr 1
          ring
        rw [e1]
        have h4 : 1 ≤ Ideal.absNorm 𝔭 ^ (2 * M + 1) := Nat.one_le_pow _ _ hq
        calc Ideal.absNorm 𝔭 ^ (2 * (M + 2)) * (2 * Ideal.absNorm 𝔭 ^ (2 * d + 1) *
              Ideal.absNorm 𝔭 ^ (k' * (2 * M + 3)))
            = Ideal.absNorm 𝔭 ^ (2 * d + 1) * (Ideal.absNorm 𝔭 ^ (2 * (M + 2)) * 2 * 1 *
              Ideal.absNorm 𝔭 ^ (k' * (2 * M + 3))) := by ring
          _ ≤ _ := by gcongr
      calc nkQ 𝔭 (k' + 2) d H n + nkB 𝔭 (k' + 2) d H n ≤ _ := Nat.add_le_add h1 h3
        _ = _ := by ring

end Formalism.HermitianLattices.Ext.L3.vectorCountBounds
