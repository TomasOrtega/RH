import Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations

open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf.WaPf

def swap {N : ℕ} (z : Pr N) : Pr N := ⟨z.2.1, z.1, z.2.2.2, z.2.2.1⟩

noncomputable def tau (N : ℕ) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun z => Finsupp.single (swap z) ((-1 : ℤ) ^ (z.1 * z.2.1))

/- English proof (translation)
Simplify using `[tau, Finsupp.linearCombination_single, Finsupp.smul_single]`.
-/
lemma tau_single {N : ℕ} (z : Pr N) (n : ℤ) :
    tau N (Finsupp.single z n) = Finsupp.single (swap z) (n * (-1 : ℤ) ^ (z.1 * z.2.1)) := by
  simp [tau, Finsupp.linearCombination_single, Finsupp.smul_single]

/- English proof (translation)
Simplify using `[Pr.d, Finsupp.linearCombination_single]`.
-/
lemma d_single {N : ℕ} (z : Pr N) (n : ℤ) :
    Pr.d N (Finsupp.single z n) = n • (z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂) := by
  simp [Pr.d, Finsupp.linearCombination_single]

/- English proof (translation)
Take `⟨p, r, a, b⟩` from `z`. Rewrite using `[tau_single, d_single, d_single]`. Consider the cases of `p with`. Consider the case `zero`. Consider the cases of `r with`.

Consider the case `zero => simp [swap, Pr.d₁, Pr.d₂]`. Consider the case `succ r`. Simplify using `only [swap, Pr.d₁, Pr.d₂, map_add, map_smul, map_sum, tau_single, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]`. Simplify using the standard rewrite rules. Consider the case `succ p`.

Consider the cases of `r with`. Consider the case `zero`. Simplify using `only [swap, Pr.d₁, Pr.d₂, map_add, map_smul, map_sum, tau_single, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]`. Simplify using the standard rewrite rules. Consider the case `succ r`.

Simplify using `only [swap, Pr.d₁, Pr.d₂, map_add, map_sum, tau_single, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, smul_add]`. Rewrite using `[add_comm]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`.

Put the polynomial expressions in normal form. Apply the tactic sequence `(try simp [pow_mul, mul_comm, mul_left_comm, mul_assoc])`. Apply the tactic sequence `(try exact neg_one_pow_eq_or ℤ _)`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`.

Put the polynomial expressions in normal form. Apply the tactic sequence `(try simp [pow_mul, mul_comm, mul_left_comm, mul_assoc])`. Apply the tactic sequence `(try exact neg_one_pow_eq_or ℤ _)`.
-/
lemma d_tau_single {N : ℕ} (z : Pr N) :
    Pr.d N (tau N (Finsupp.single z 1)) = tau N (Pr.d N (Finsupp.single z 1)) := by
  obtain ⟨p, r, a, b⟩ := z
  rw [tau_single, d_single, d_single]
  cases p with
  | zero =>
    cases r with
    | zero => simp [swap, Pr.d₁, Pr.d₂]
    | succ r =>
      simp only [swap, Pr.d₁, Pr.d₂, map_add, map_smul, map_sum, tau_single, Finset.smul_sum,
        Finsupp.smul_single, smul_eq_mul]
      simp
  | succ p =>
    cases r with
    | zero =>
      simp only [swap, Pr.d₁, Pr.d₂, map_add, map_smul, map_sum, tau_single, Finset.smul_sum,
        Finsupp.smul_single, smul_eq_mul]
      simp
    | succ r =>
      simp only [swap, Pr.d₁, Pr.d₂, map_add, map_sum, tau_single, Finset.smul_sum,
        Finsupp.smul_single, smul_eq_mul, smul_add]
      rw [add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        congr 1; ring_nf
        (try simp [pow_mul, mul_comm, mul_left_comm, mul_assoc])
        (try exact neg_one_pow_eq_or ℤ _)
      · refine Finset.sum_congr rfl fun i _ => ?_
        congr 1; ring_nf
        (try simp [pow_mul, mul_comm, mul_left_comm, mul_assoc])
        (try exact neg_one_pow_eq_or ℤ _)

/- English proof (translation)
Establish `: (Pr.d N).comp (tau N) = (tau N).comp (Pr.d N)`. Use `Finsupp.lhom_ext' fun z => LinearMap.ext_ring ?_` and prove the remaining obligations. Conclude with `d_tau_single z`. Conclude with `LinearMap.congr_fun this c`.
-/
lemma d_tau {N : ℕ} (c : Pr N →₀ ℤ) : Pr.d N (tau N c) = tau N (Pr.d N c) := by
  have : (Pr.d N).comp (tau N) = (tau N).comp (Pr.d N) := by
    refine Finsupp.lhom_ext' fun z => LinearMap.ext_ring ?_
    exact d_tau_single z
  exact LinearMap.congr_fun this c

/- English proof (translation)
Establish `: (tau M).comp (Pr.push θ) = (Pr.push θ).comp (tau N)`. Use `Finsupp.lhom_ext fun z n => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, tau_single]`. Both sides reduce to the same expression. Conclude with `LinearMap.congr_fun this c`.
-/
lemma tau_push {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (c : Pr N →₀ ℤ) :
    tau M (Pr.push θ c) = Pr.push θ (tau N c) := by
  have : (tau M).comp (Pr.push θ) = (Pr.push θ).comp (tau N) := by
    refine Finsupp.lhom_ext fun z n => ?_
    simp only [LinearMap.comp_apply, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, tau_single]
    rfl
  exact LinearMap.congr_fun this c

/- English proof (translation)
Unfold `Pr.bd`. Simplify using `only [map_sum, map_zsmul, tau_push]`.
-/
lemma tau_bd {N : ℕ} (c : Pr N →₀ ℤ) : tau (N + 1) (Pr.bd c) = Pr.bd (tau N c) := by
  unfold Pr.bd
  simp only [map_sum, map_zsmul, tau_push]

/- English proof (translation)
Unfold `Pr.wa Pr.aw`. Simplify using `only [map_sum, tau_single, swap, one_mul]`.
-/
lemma wa_eq (N : ℕ) : Pr.wa N = tau N (Pr.aw N) := by
  unfold Pr.wa Pr.aw
  simp only [map_sum, tau_single, swap, one_mul]

end LateralTheory.EtaleFoundations.SteenPf.WaPf

open LateralTheory.EtaleFoundations.SteenPf LateralTheory.EtaleFoundations.SteenPf.WaPf in

/- English proof (translation)
Introduce `N`. Rewrite using `[wa_eq, wa_eq, d_tau, hAW, tau_bd]`.
-/
theorem LateralTheory.EtaleFoundations.SteenPf.leaf_wa_of_aw (hAW : leaf_aw) : leaf_wa := by
  intro N
  rw [wa_eq, wa_eq, d_tau, hAW, tau_bd]

open LateralTheory.EtaleFoundations.SteenPf in

/- English proof (translation)
The claim follows from `leaf_wa_of_aw hAW`.
-/
theorem LateralTheory.EtaleFoundations.SteenPf.leaf_wa_of (hAW : leaf_aw) : leaf_wa := leaf_wa_of_aw hAW
