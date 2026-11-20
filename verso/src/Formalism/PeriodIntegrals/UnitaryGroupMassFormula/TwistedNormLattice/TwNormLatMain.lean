import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.IdealForm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.PrXLeOfNf

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwNormLat.W

/- English proof (translation)
Introduce `E _ _ _ P N c kj j hp hq h hB`. Establish `Madd : ∀ u v : Fin (N + c) → E, h⁻¹ u ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 → h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 → h⁻¹ (u + v) ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0` using `fun u v hu hv => by rw [map_add]; exact add_mem hu hv`. Establish `Msmul : ∀ (t : E) (v : Fin (N + c) → E), IntAt P t → h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 → h⁻¹ (t • v) ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0` using `fun t v ht hv => by`. Rewrite using `[map_smul, mem_lam]`. Rewrite `hv` using `[mem_lam]`.

Introduce `l`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Conclude with `intAt_mul P ht (hv l)`. Establish `Mlam : ∀ v : Fin (N + c) → E, (∀ l, IntAt P (v l)) → h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0` using `fun v hv => (hB v ((mem_lam P N c v).2 hv)).1`. Establish `Mbd : ∀ v : Fin (N + c) → E, h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 → ∀ l, IntAt P (qE P ^ j * v l)` using `fun v hv l => by`.

Use `(hB _ hv).2` as an intermediate fact. Rewrite `this` using `[LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, mem_lam]`. Simplify `this l` using `[smul_eq_mul]`. Take `⟨K, b, hKj, hbM, hbl, hUT, hrep⟩` from `herm P (fun v => h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0) Madd Msmul Mlam hp hq j Mbd`. Establish `hq0` using `qE_ne_zero P hp`.

Establish `hbd : ∀ l, b l l ≠ 0` using `fun l => by rw [hbl]; exact inv_ne_zero (pow_ne_zero _ hq0)`. Set `d : Fin (N + c) → E` to `fun l => if l.1 < N then 1 else qE P ^ K l`. Set `x1 : Fin (N + c) → E` to `if hN : N < N + c then d ⟨N, hN⟩ • b ⟨N, hN⟩ - Pi.single ⟨N, hN⟩ 1 else 0`. Establish `hx1M : h⁻¹ x1 ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0`. Distinguish the cases in `hN : N < N + c`.

Simplify using `only [x1, dif_pos hN]`. Rewrite using `[sub_eq_add_neg, ← neg_one_smul E (Pi.single _ _)]`. Use `Madd _ _ (Msmul _ _ ?_ (hbM _)) (Msmul _ _ (intAt_neg P (intAt_one P)) (Mlam _ fun k => ?_))` and prove the remaining obligations. Simplify using `only [d, lt_irrefl, if_false]`. Conclude with `intAt_pow P (intAt_natCast P _) _`.

Distinguish the cases in `hk : k = ⟨N, hN⟩`. Rewrite using `[hk]`. Simplify using `using intAt_one P`. Simplify `intAt_zero P` using `[Pi.single_apply, hk]`. Simplify using `only [x1, dif_neg hN, map_zero]`.

Conclude with `zero_mem _`. Establish `hx1Z : Zab N x1`. Introduce `l hl`. Distinguish the cases in `hN : N < N + c`. Simplify using `only [x1, dif_pos hN, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`.

Break down `Nat.lt_or_eq_of_le hl with hlt | heq` into its components or cases. Rewrite using `[hUT _ l (by rw [Fin.lt_def]; exact hlt)]`. Establish `: l ≠ ⟨N, hN⟩` using `fun e => by rw [e] at hlt; exact lt_irrefl _ hlt`. Simplify using `[Pi.single_apply, this]`. Establish `: l = ⟨N, hN⟩` using `Fin.ext heq.symm`.

Rewrite using `[this, hbl]`. Simplify using `only [d, lt_irrefl, if_false, Pi.single_eq_same]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `[x1, dif_neg hN]`.

Take `⟨ζ, hζ, hx1ζ⟩` from `hrep x1 hx1M`. Establish `hζZ : Zab N ζ` using `comb_reflect hUT hbd ζ N (by rw [← hx1ζ]; exact hx1Z)`. Set `c' : Fin (N + c) → Fin (N + c) → E` to `fun l => d l • b l - (if l.1 = N then x1 else 0)`. Establish `hcUT : UT c'`. Introduce `l k hlk`.

Simplify using `only [c', Pi.sub_apply, Pi.smul_apply, hUT l k hlk, smul_zero, zero_sub, neg_eq_zero]`. Use `split_ifs with h1`. Conclude with `hx1Z k (by rw [Fin.lt_def] at hlk; omega)`. Both sides reduce to the same expression. Establish `hc1 : ∀ l : Fin (N + c), N ≤ l.1 → c' l l = 1`.

Introduce `l hl`. Distinguish the cases in `h1 : l.1 = N`. Simplify using `only [c', if_pos h1, d, if_neg (not_lt.2 hl), Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hbl, hx1Z l hl]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try simp`.

Simplify using `only [c', if_neg h1, d, if_neg (not_lt.2 hl), Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hbl, Pi.zero_apply, sub_zero]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try simp`. Establish `hcd : ∀ l, c' l l ≠ 0`. Introduce `l`.

Distinguish the cases in `hl : N ≤ l.1`. Rewrite using `[hc1 l hl]`. Conclude with `one_ne_zero`. Establish `h1 : l.1 ≠ N` using `by omega`. Simplify using `only [c', if_neg h1, d, if_pos (not_le.1 hl), Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hbl, Pi.zero_apply, sub_zero, one_mul]`.

Conclude with `inv_ne_zero (pow_ne_zero _ hq0)`. Establish `hca : ∀ hN : N < N + c, c' ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1`. Introduce `hN`. Use `show d _ • b _ - (if N = N then x1 else 0) = _`. Rewrite using `[if_pos rfl]`.

Simplify using `only [x1, dif_pos hN]`. Conclude with `sub_sub_cancel _ _`. Establish `hr : (combE hcUT hcd)⁻¹ ∈ Loc.R1 E N c` using `combinationEquiv_inv_mem_unipotentFlagGroup hcUT hcd hc1 hca`. Use `⟨(combE hcUT hcd)⁻¹, hr, 1, Subgroup.one_mem _, ?_⟩` and prove the remaining obligations. Establish `hinv : ∀ v, ((combE hcUT hcd)⁻¹ * h * 1)⁻¹ v = h⁻¹ (combE hcUT hcd v)` using `fun v => by`.

Rewrite using `[mul_one, mul_inv_rev, inv_inv]`. Both sides reduce to the same expression. Set `u : (Fin (N + c) → E) → Fin (N + c) → E` to `fun v l => v l * d l - Loc.atN v N * ζ l`. Establish `hsv : ∀ v, combE hcUT hcd v = ∑ l, u v l • b l`. Introduce `v`.

Rewrite using `[combE_apply]`. Establish `e1 : ∀ l, v l • c' l = (v l * d l) • b l - v l • (if l.1 = N then x1 else 0)` using `fun l => by`. Simplify using `only [c', smul_sub, smul_smul]`. Establish `e2 : ∑ l, v l • (if l.1 = N then x1 else 0) = Loc.atN v N • x1`. Distinguish the cases in `hN : N < N + c`.

Rewrite using `[Finset.sum_eq_single ⟨N, hN⟩]`. Simplify using `[Loc.atN, hN]`. Introduce `l _ hl`. Establish `: l.1 ≠ N` using `fun e => hl (Fin.ext e)`. Simplify using `[this]`.

Simplify using the standard rewrite rules. Establish `hz : Loc.atN v N = 0` using `by simp [Loc.atN, hN]`. Rewrite using `[hz, zero_smul]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Establish `: l.1 ≠ N` using `by have := l.2; omega`.

Simplify using `[this]`. Rewrite using `[Finset.sum_congr rfl (fun l _ => e1 l), Finset.sum_sub_distrib, e2, hx1ζ, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← sub_smul]`. Set `n : ℕ → ℤ` to `fun i => if hi : i < c then -(K (Fin.natAdd N ⟨i, hi⟩) : ℤ) else 0`.

Set `z : Sp E N` to `fun l => ζ (Fin.castAdd c l)`. Establish `hu1 : ∀ v (l : Fin N), u v (Fin.castAdd c l) = v (Fin.castAdd c l) - Loc.atN v N * z l`. Introduce `v l`. Simplify using `only [u, d, z]`. Rewrite using `[if_pos (show (Fin.castAdd c l).1 < N from l.2), mul_one]`.

Establish `hu2 : ∀ v (i : Fin c), u v (Fin.natAdd N i) = (qE P ^ (n i.1))⁻¹ * v (Fin.natAdd N i)`. Introduce `v i`. Simplify using `only [u, d, n]`. Rewrite using `[if_neg (show ¬ (Fin.natAdd N i).1 < N by simp), hζZ _ (by simp), dif_pos i.2, zpow_neg, inv_inv, zpow_natCast, mul_zero, sub_zero, mul_comm]`. Establish `hU : ∀ v, (∀ l, IntAt P (u v l)) ↔ Crit P N c n z v`.

Introduce `v`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Use `⟨fun l => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `H (Fin.castAdd c l)` as an intermediate fact.

Rewrite `this` using `[hu1]`. Then use the resulting hypothesis. Use `H (Fin.natAdd N i)` as an intermediate fact. Rewrite `this` using `[hu2]`. Then use the resulting hypothesis. Introduce `H l`. Break down `fin_split l with ⟨l', rfl⟩ | ⟨i, rfl⟩` into its components or cases.

Rewrite using `[hu1]`. Conclude with `H.1 l'`. Rewrite using `[hu2]`. Conclude with `H.2 i`. Establish `hcrit : ∀ v, ((combE hcUT hcd)⁻¹ * h * 1)⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ Crit P N c n z v`.

Introduce `v`. Rewrite using `[hinv, hsv, ← hU]`. Prove the components needed by the constructor for the conclusion. Introduce `hm`. Take `⟨w, hw, hwe⟩` from `hrep _ hm`.

Establish `hz0 : Zab 0 (u v - w)`. Apply `comb_reflect hUT hbd _ 0` to reduce the goal to its premises. Establish `: ∑ l, (u v - w) l • b l = 0`. Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[hwe, sub_self]`.

Rewrite using `[this]`. Introduce `_ _`. Both sides reduce to the same expression. Introduce `l`. Use `hz0 l (Nat.zero_le _)` as an intermediate fact.

Rewrite `this` using `[Pi.sub_apply, sub_eq_zero]`. Rewrite using `[this]`. Conclude with `hw l`. Introduce `H`. Conclude with `comb_mem P _ Madd Msmul Mlam b hbM _ H`.

Establish `hn : ∀ i, -(j : ℤ) ≤ n i ∧ n i ≤ 0`. Introduce `i`. Simplify using `only [n]`. Use `split_ifs with hi`. Apply the tactic sequence `have := hKj (Fin.natAdd N ⟨i, hi⟩); constructor <;> omega`.

Apply the tactic sequence `constructor <;> omega`. Establish `hz : z ∈ stdAt E N P` using `(mem_stdAt P z).2 fun l => hζ _`. Conclude with `⟨bdd_of_nf P hp _ n z hn hz hcrit, ⟨n, z, hn, hz, hcrit⟩, prX_le_of_nf P kj _ n z hcrit⟩`.
-/
theorem twNormLat_main : PI.TwNormLat.TwNormLat := by
  intro E _ _ _ P N c kj j hp hq h hB
  have Madd : ∀ u v : Fin (N + c) → E, h⁻¹ u ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 →
      h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 → h⁻¹ (u + v) ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 :=
    fun u v hu hv => by rw [map_add]; exact add_mem hu hv
  have Msmul : ∀ (t : E) (v : Fin (N + c) → E), IntAt P t → h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 →
      h⁻¹ (t • v) ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 := fun t v ht hv => by
    rw [map_smul, mem_lam]; rw [mem_lam] at hv
    intro l; rw [Pi.smul_apply, smul_eq_mul]; exact intAt_mul P ht (hv l)
  have Mlam : ∀ v : Fin (N + c) → E, (∀ l, IntAt P (v l)) → h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 :=
    fun v hv => (hB v ((mem_lam P N c v).2 hv)).1
  have Mbd : ∀ v : Fin (N + c) → E, h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 →
      ∀ l, IntAt P (qE P ^ j * v l) := fun v hv l => by
    have := (hB _ hv).2
    rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, mem_lam] at this
    simpa [smul_eq_mul] using this l
  obtain ⟨K, b, hKj, hbM, hbl, hUT, hrep⟩ :=
    herm P (fun v => h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0) Madd Msmul Mlam hp hq j Mbd
  have hq0 := qE_ne_zero P hp
  have hbd : ∀ l, b l l ≠ 0 := fun l => by rw [hbl]; exact inv_ne_zero (pow_ne_zero _ hq0)
  let d : Fin (N + c) → E := fun l => if l.1 < N then 1 else qE P ^ K l
  let x1 : Fin (N + c) → E := if hN : N < N + c then d ⟨N, hN⟩ • b ⟨N, hN⟩ - Pi.single ⟨N, hN⟩ 1 else 0
  have hx1M : h⁻¹ x1 ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 := by
    by_cases hN : N < N + c
    · simp only [x1, dif_pos hN]
      rw [sub_eq_add_neg, ← neg_one_smul E (Pi.single _ _)]
      refine Madd _ _ (Msmul _ _ ?_ (hbM _)) (Msmul _ _ (intAt_neg P (intAt_one P)) (Mlam _ fun k => ?_))
      · simp only [d, lt_irrefl, if_false]; exact intAt_pow P (intAt_natCast P _) _
      · by_cases hk : k = ⟨N, hN⟩
        · rw [hk]; simpa using intAt_one P
        · simpa [Pi.single_apply, hk] using intAt_zero P
    · simp only [x1, dif_neg hN, map_zero]; exact zero_mem _
  have hx1Z : Zab N x1 := by
    intro l hl
    by_cases hN : N < N + c
    · simp only [x1, dif_pos hN, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rcases Nat.lt_or_eq_of_le hl with hlt | heq
      · rw [hUT _ l (by rw [Fin.lt_def]; exact hlt)]
        have : l ≠ ⟨N, hN⟩ := fun e => by rw [e] at hlt; exact lt_irrefl _ hlt
        simp [Pi.single_apply, this]
      · have : l = ⟨N, hN⟩ := Fin.ext heq.symm
        rw [this, hbl]
        simp only [d, lt_irrefl, if_false, Pi.single_eq_same]
        field_simp; ring
    · simp [x1, dif_neg hN]
  obtain ⟨ζ, hζ, hx1ζ⟩ := hrep x1 hx1M
  have hζZ : Zab N ζ := comb_reflect hUT hbd ζ N (by rw [← hx1ζ]; exact hx1Z)
  let c' : Fin (N + c) → Fin (N + c) → E := fun l => d l • b l - (if l.1 = N then x1 else 0)
  have hcUT : UT c' := by
    intro l k hlk
    simp only [c', Pi.sub_apply, Pi.smul_apply, hUT l k hlk, smul_zero, zero_sub, neg_eq_zero]
    split_ifs with h1
    · exact hx1Z k (by rw [Fin.lt_def] at hlk; omega)
    · rfl
  have hc1 : ∀ l : Fin (N + c), N ≤ l.1 → c' l l = 1 := by
    intro l hl
    by_cases h1 : l.1 = N
    · simp only [c', if_pos h1, d, if_neg (not_lt.2 hl), Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hbl, hx1Z l hl]
      field_simp
      try simp
    · simp only [c', if_neg h1, d, if_neg (not_lt.2 hl), Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hbl,
        Pi.zero_apply, sub_zero]
      field_simp
      try simp
  have hcd : ∀ l, c' l l ≠ 0 := by
    intro l
    by_cases hl : N ≤ l.1
    · rw [hc1 l hl]; exact one_ne_zero
    · have h1 : l.1 ≠ N := by omega
      simp only [c', if_neg h1, d, if_pos (not_le.1 hl), Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hbl,
        Pi.zero_apply, sub_zero, one_mul]
      exact inv_ne_zero (pow_ne_zero _ hq0)
  have hca : ∀ hN : N < N + c, c' ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1 := by
    intro hN
    show d _ • b _ - (if N = N then x1 else 0) = _
    rw [if_pos rfl]
    simp only [x1, dif_pos hN]
    exact sub_sub_cancel _ _
  have hr : (combE hcUT hcd)⁻¹ ∈ Loc.R1 E N c := combinationEquiv_inv_mem_unipotentFlagGroup hcUT hcd hc1 hca
  refine ⟨(combE hcUT hcd)⁻¹, hr, 1, Subgroup.one_mem _, ?_⟩
  have hinv : ∀ v, ((combE hcUT hcd)⁻¹ * h * 1)⁻¹ v = h⁻¹ (combE hcUT hcd v) := fun v => by
    rw [mul_one, mul_inv_rev, inv_inv]; rfl
  let u : (Fin (N + c) → E) → Fin (N + c) → E := fun v l => v l * d l - Loc.atN v N * ζ l
  have hsv : ∀ v, combE hcUT hcd v = ∑ l, u v l • b l := by
    intro v
    rw [combE_apply]
    have e1 : ∀ l, v l • c' l = (v l * d l) • b l - v l • (if l.1 = N then x1 else 0) := fun l => by
      simp only [c', smul_sub, smul_smul]
    have e2 : ∑ l, v l • (if l.1 = N then x1 else 0) = Loc.atN v N • x1 := by
      by_cases hN : N < N + c
      · rw [Finset.sum_eq_single ⟨N, hN⟩]
        · simp [Loc.atN, hN]
        · intro l _ hl
          have : l.1 ≠ N := fun e => hl (Fin.ext e)
          simp [this]
        · simp
      · have hz : Loc.atN v N = 0 := by simp [Loc.atN, hN]
        rw [hz, zero_smul]
        refine Finset.sum_eq_zero fun l _ => ?_
        have : l.1 ≠ N := by have := l.2; omega
        simp [this]
    rw [Finset.sum_congr rfl (fun l _ => e1 l), Finset.sum_sub_distrib, e2, hx1ζ, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul, ← sub_smul]
  let n : ℕ → ℤ := fun i => if hi : i < c then -(K (Fin.natAdd N ⟨i, hi⟩) : ℤ) else 0
  let z : Sp E N := fun l => ζ (Fin.castAdd c l)
  have hu1 : ∀ v (l : Fin N), u v (Fin.castAdd c l) = v (Fin.castAdd c l) - Loc.atN v N * z l := by
    intro v l
    simp only [u, d, z]
    rw [if_pos (show (Fin.castAdd c l).1 < N from l.2), mul_one]
  have hu2 : ∀ v (i : Fin c), u v (Fin.natAdd N i) = (qE P ^ (n i.1))⁻¹ * v (Fin.natAdd N i) := by
    intro v i
    simp only [u, d, n]
    rw [if_neg (show ¬ (Fin.natAdd N i).1 < N by simp), hζZ _ (by simp), dif_pos i.2, zpow_neg, inv_inv,
      zpow_natCast, mul_zero, sub_zero, mul_comm]
  have hU : ∀ v, (∀ l, IntAt P (u v l)) ↔ Crit P N c n z v := by
    intro v
    constructor
    · intro H
      refine ⟨fun l => ?_, fun i => ?_⟩
      · have := H (Fin.castAdd c l); rwa [hu1] at this
      · have := H (Fin.natAdd N i); rwa [hu2] at this
    · intro H l
      rcases fin_split l with ⟨l', rfl⟩ | ⟨i, rfl⟩
      · rw [hu1]; exact H.1 l'
      · rw [hu2]; exact H.2 i
  have hcrit : ∀ v, ((combE hcUT hcd)⁻¹ * h * 1)⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔
      Crit P N c n z v := by
    intro v
    rw [hinv, hsv, ← hU]
    constructor
    · intro hm
      obtain ⟨w, hw, hwe⟩ := hrep _ hm
      have hz0 : Zab 0 (u v - w) := by
        apply comb_reflect hUT hbd _ 0
        have : ∑ l, (u v - w) l • b l = 0 := by
          simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]; rw [hwe, sub_self]
        rw [this]; intro _ _; rfl
      intro l
      have := hz0 l (Nat.zero_le _)
      rw [Pi.sub_apply, sub_eq_zero] at this
      rw [this]; exact hw l
    · intro H
      exact comb_mem P _ Madd Msmul Mlam b hbM _ H
  have hn : ∀ i, -(j : ℤ) ≤ n i ∧ n i ≤ 0 := by
    intro i
    simp only [n]
    split_ifs with hi
    · have := hKj (Fin.natAdd N ⟨i, hi⟩); constructor <;> omega
    · constructor <;> omega
  have hz : z ∈ stdAt E N P := (mem_stdAt P z).2 fun l => hζ _
  exact ⟨bdd_of_nf P hp _ n z hn hz hcrit, ⟨n, z, hn, hz, hcrit⟩, prX_le_of_nf P kj _ n z hcrit⟩

end PI.TwNormLat.W
