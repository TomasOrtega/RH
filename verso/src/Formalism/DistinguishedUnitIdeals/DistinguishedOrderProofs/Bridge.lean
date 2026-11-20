import Mathlib
import Formalism.DistinguishedUnitIdeals.BridgeLevelOf
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Graded
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Partners
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.UnivPart

noncomputable section

namespace Formalism.ExponentWindows.G

open TensorProduct SlopeTestRemainingChoices PT

namespace BR

section den
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
  {LL : Type} [Field LL] [Algebra O LL] [IsFractionRing O LL]

/- English proof (translation)
Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective O LL)]`. Conclude with `pow_ne_zero _ hϖ.ne_zero`.
-/
lemma alg_ne (hϖ : Irreducible ϖ) (N : ℕ) : algebraMap O LL (ϖ ^ N) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O LL)]
  exact pow_ne_zero _ hϖ.ne_zero

/- English proof (translation)
Take `⟨a, s, hs, rfl⟩` from `IsFractionRing.div_surjective (A := O) x`. Establish `hs0 : s ≠ 0` using `nonZeroDivisors.ne_zero hs`. Take `⟨N, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ`. Use `⟨N, ((u⁻¹ : Oˣ) : O) * a, ?_⟩` and prove the remaining obligations. Establish `h1 : algebraMap O LL ((u : O) * ϖ ^ N) ≠ 0`.

Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective O LL)]`. Conclude with `hs0`. Rewrite using `[mul_div_assoc', div_eq_iff h1, ← map_mul, ← map_mul]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma den_one (hϖ : Irreducible ϖ) (x : LL) :
    ∃ (N : ℕ) (a : O), algebraMap O LL (ϖ ^ N) * x = algebraMap O LL a := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨N, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
  refine ⟨N, ((u⁻¹ : Oˣ) : O) * a, ?_⟩
  have h1 : algebraMap O LL ((u : O) * ϖ ^ N) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O LL)]
    exact hs0
  rw [mul_div_assoc', div_eq_iff h1, ← map_mul, ← map_mul]
  congr 1
  calc ϖ ^ N * a = ((u⁻¹ : Oˣ) : O) * (u : O) * (ϖ ^ N * a) := by rw [Units.inv_mul, one_mul]
    _ = _ := by ring

/- English proof (translation)
Use `choose N a h using fun k => den_one (LL := LL) hϖ (x k)`. Use `⟨Finset.univ.sup N, fun k => ϖ ^ (Finset.univ.sup N - N k) * a k, fun k => ?_⟩` and prove the remaining obligations. Establish `hle : N k ≤ Finset.univ.sup N` using `Finset.le_sup (Finset.mem_univ k)`. Establish `: ϖ ^ Finset.univ.sup N = ϖ ^ (Finset.univ.sup N - N k) * ϖ ^ N k`. Rewrite using `[← pow_add, Nat.sub_add_cancel hle]`.

Rewrite using `[this, map_mul, mul_assoc, h k, map_mul]`.
-/
lemma den_fam (hϖ : Irreducible ϖ) {r : ℕ} (x : Fin r → LL) :
    ∃ (N : ℕ) (a : Fin r → O), ∀ k, algebraMap O LL (ϖ ^ N) * x k = algebraMap O LL (a k) := by
  choose N a h using fun k => den_one (LL := LL) hϖ (x k)
  refine ⟨Finset.univ.sup N, fun k => ϖ ^ (Finset.univ.sup N - N k) * a k, fun k => ?_⟩
  have hle : N k ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ k)
  have : ϖ ^ Finset.univ.sup N = ϖ ^ (Finset.univ.sup N - N k) * ϖ ^ N k := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [this, map_mul, mul_assoc, h k, map_mul]

end den

section retr
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} {r : ℕ}

/- English proof (translation)
Take `⟨Q, hQ⟩` from `exists_isCompl_of_saturated hϖ U hU`. Use `⟨U.subtype ∘ₗ Submodule.projectionOnto U Q hQ, fun v => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Conclude with `(Submodule.projectionOnto U Q hQ v).2`. Use `Submodule.projectionOnto_apply_left hQ ⟨v, hv⟩` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply]`.

Rewrite using `[this]`.
-/
lemma exists_retr (hϖ : Irreducible ϖ) (U : Submodule O (Fin r → O)) (hU : Saturated ϖ U) :
    ∃ π : (Fin r → O) →ₗ[O] (Fin r → O), (∀ v, π v ∈ U) ∧ ∀ v ∈ U, π v = v := by
  obtain ⟨Q, hQ⟩ := exists_isCompl_of_saturated hϖ U hU
  refine ⟨U.subtype ∘ₗ Submodule.projectionOnto U Q hQ, fun v => ?_, fun v hv => ?_⟩
  · exact (Submodule.projectionOnto U Q hQ v).2
  · have := Submodule.projectionOnto_apply_left hQ ⟨v, hv⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [this]

end retr

section lin
variable {LL Ks D : Type} [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]

def St (m m' : ℤ) (W : Submodule LL D) (i : ℤ) : Submodule LL D :=
  if i < m then ⊥ else if i < m' then W else ⊤

def Wp (W : Submodule LL D) (i : ℤ) : Submodule LL D := if i < 0 then ⊥ else W

/- English proof (translation)
Introduce `i j hij`. Simplify using `only [St]`. Apply the tactic sequence `split_ifs <;> first | exact le_rfl | exact bot_le | exact le_top | omega`.
-/
lemma st_mono (m m' : ℤ) (W : Submodule LL D) : Monotone (St m m' W) := by
  intro i j hij
  simp only [St]
  split_ifs <;> first | exact le_rfl | exact bot_le | exact le_top | omega

/- English proof (translation)
Introduce `i j hij`. Simplify using `only [Wp]`. Apply the tactic sequence `split_ifs <;> first | exact le_rfl | exact bot_le | omega`.
-/
lemma wp_mono (W : Submodule LL D) : Monotone (Wp W) := by
  intro i j hij
  simp only [Wp]
  split_ifs <;> first | exact le_rfl | exact bot_le | omega

/- English proof (translation)
Establish `hX' : Monotone fun i : ℤ => X (i - a)` using `fun i j hij => hX (by omega)`. Rewrite using `[ofPS_unit_X, mul_smul]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `unit_smul_mem hX' ε.isUnit h`.

Rewrite `h1` using `[xi_shift_holds LL Ks D]`. Conclude with `xi_mono (fun i => le_of_eq (by simp)) h1`. Introduce `h`. Use `xi_module_structure LL Ks D _ hX' _ _ ?_` and prove the remaining obligations. Rewrite using `[xi_shift_holds LL Ks D]`.

Conclude with `xi_mono (fun i => le_of_eq (by simp)) h`.
-/
lemma shift_iff {X : ℤ → Submodule LL D} (hX : Monotone X) (ε : (PowerSeries Ks)ˣ) (a : ℕ)
    (f : Amb LL Ks D) :
    HahnSeries.ofPowerSeries ℤ Ks ((ε : PowerSeries Ks) * PowerSeries.X ^ a) • f ∈
      Xi Ks (fun i => X (i - a)) ↔ f ∈ Xi Ks X := by
  have hX' : Monotone fun i : ℤ => X (i - a) := fun i j hij => hX (by omega)
  rw [ofPS_unit_X, mul_smul]
  constructor
  · intro h
    have h1 := unit_smul_mem hX' ε.isUnit h
    rw [xi_shift_holds LL Ks D] at h1
    exact xi_mono (fun i => le_of_eq (by simp)) h1
  · intro h
    refine xi_module_structure LL Ks D _ hX' _ _ ?_
    rw [xi_shift_holds LL Ks D]
    exact xi_mono (fun i => le_of_eq (by simp)) h

/- English proof (translation)
The claim follows from `((IsUnit.mk0 x hx).map (algebraMap LL Ks)).map PowerSeries.C`.
-/
lemma isUnit_C_alg {x : LL} (hx : x ≠ 0) :
    IsUnit (PowerSeries.C (algebraMap LL Ks x) : PowerSeries Ks) :=
  ((IsUnit.mk0 x hx).map (algebraMap LL Ks)).map PowerSeries.C

variable {r : ℕ} (lam : Fin r → D)

def Fy (LL : Type) {Ks D : Type} [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D]
    [Module LL D] {r : ℕ} (lam : Fin r → D) (x : Fin r → PowerSeries Ks) : Amb LL Ks D :=
  ∑ k, HahnSeries.ofPowerSeries ℤ Ks (x k) • cstD Ks (lam k)

/- English proof (translation)
Unfold `Fy`. Rewrite using `[cf_sum]`. Simplify using `only [cf_smul_cst]`.
-/
lemma cf_Fy (x : Fin r → PowerSeries Ks) (i : ℤ) :
    cf (Fy LL lam x) i =
      ∑ k, (HahnSeries.ofPowerSeries ℤ Ks (x k)).coeff i • ((1 : Ks) ⊗ₜ[LL] lam k) := by
  unfold Fy
  rw [cf_sum]
  simp only [cf_smul_cst]

/- English proof (translation)
Rewrite using `[cf_Fy]`. Simplify using `only [HahnSeries.ofPowerSeries_apply_coeff]`.
-/
lemma cf_Fy_nat (x : Fin r → PowerSeries Ks) (i : ℕ) :
    cf (Fy LL lam x) (i : ℤ) = ∑ k, PowerSeries.coeff i (x k) • ((1 : Ks) ⊗ₜ[LL] lam k) := by
  rw [cf_Fy]
  simp only [HahnSeries.ofPowerSeries_apply_coeff]

/- English proof (translation)
Rewrite using `[HahnSeries.ofPowerSeries_apply]`. Apply `HahnSeries.embDomain_of_notMem_range` to reduce the goal to its premises. Introduce and unpack `⟨n, hn⟩`. Establish `: (n : ℤ) = i` using `hn`. Use linear arithmetic over natural numbers and integers.
-/
lemma ofPS_coeff_neg (x : PowerSeries Ks) {i : ℤ} (hi : i < 0) :
    (HahnSeries.ofPowerSeries ℤ Ks x).coeff i = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_of_notMem_range
  rintro ⟨n, hn⟩
  have : (n : ℤ) = i := hn
  omega

/- English proof (translation)
Rewrite using `[cf_Fy]`. Conclude with `Finset.sum_eq_zero fun k _ => by rw [ofPS_coeff_neg _ hi, zero_smul]`.
-/
lemma cf_Fy_neg (x : Fin r → PowerSeries Ks) {i : ℤ} (hi : i < 0) : cf (Fy LL lam x) i = 0 := by
  rw [cf_Fy]
  exact Finset.sum_eq_zero fun k _ => by rw [ofPS_coeff_neg _ hi, zero_smul]

/- English proof (translation)
Unfold `Fy`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [Pi.add_apply, map_add, add_smul]`.
-/
lemma Fy_add (x x' : Fin r → PowerSeries Ks) : Fy LL lam (x + x') = Fy LL lam x + Fy LL lam x' := by
  unfold Fy
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [Pi.add_apply, map_add, add_smul]

/- English proof (translation)
Unfold `Fy`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul]`.
-/
lemma Fy_smul (a : PowerSeries Ks) (x : Fin r → PowerSeries Ks) :
    Fy LL lam (a • x) = HahnSeries.ofPowerSeries ℤ Ks a • Fy LL lam x := by
  unfold Fy
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul]

/- English proof (translation)
Apply `amb_ext` to reduce the goal to its premises. Introduce `i`. Rewrite using `[cf_cst]`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality.

Use `cf_Fy_nat (LL := LL) (Ks := Ks) lam (fun k => PowerSeries.C (algebraMap LL Ks (v k))) 0` as an intermediate fact. Rewrite `this` using `[Nat.cast_zero]`. Rewrite using `[this, if_pos rfl, TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_zero_C, TensorProduct.tmul_smul, algebraMap_smul]`.

Rewrite using `[if_neg hi]`. Break down `lt_or_gt_of_ne hi with h | h` into its components or cases. Conclude with `cf_Fy_neg lam _ h`. Take `⟨n, rfl⟩` from `Int.eq_ofNat_of_zero_le h.le`. Rewrite using `[cf_Fy_nat]`.

Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_C, if_neg (by omega), zero_smul]`.
-/
lemma Fy_const (v : Fin r → LL) :
    Fy LL lam (fun k => PowerSeries.C (algebraMap LL Ks (v k))) = cstD Ks (∑ k, v k • lam k) := by
  apply amb_ext
  intro i
  rw [cf_cst]
  by_cases hi : i = 0
  · subst hi
    have := cf_Fy_nat (LL := LL) (Ks := Ks) lam (fun k => PowerSeries.C (algebraMap LL Ks (v k))) 0
    rw [Nat.cast_zero] at this
    rw [this, if_pos rfl, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_zero_C, TensorProduct.tmul_smul, algebraMap_smul]
  · rw [if_neg hi]
    rcases lt_or_gt_of_ne hi with h | h
    · exact cf_Fy_neg lam _ h
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h.le
      rw [cf_Fy_nat]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [PowerSeries.coeff_C, if_neg (by omega), zero_smul]

/- English proof (translation)
Introduce `i`. Rewrite using `[cf_cst]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `only [Wp, lt_irrefl, if_false]`.

Conclude with `Submodule.tmul_mem_baseChange_of_mem 1 hd`. Conclude with `Submodule.zero_mem _`.
-/
lemma cst_mem_wp {W : Submodule LL D} {d : D} (hd : d ∈ W) : cstD Ks d ∈ Xi Ks (Wp W) := by
  intro i
  rw [cf_cst]
  split_ifs with h
  · subst h
    simp only [Wp, lt_irrefl, if_false]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hd
  · exact Submodule.zero_mem _

/- English proof (translation)
Introduce `i`. Simplify using `only [Tw]`. Use `split_ifs with h`. Rewrite using `[Submodule.baseChange_top]`. Conclude with `Submodule.mem_top`.

Rewrite using `[cf_Fy_neg lam x (by omega)]`. Conclude with `Submodule.zero_mem _`.
-/
lemma Fy_mem_tw (x : Fin r → PowerSeries Ks) : Fy LL lam x ∈ Xi Ks (Tw (LL := LL) (D := D) 0) := by
  intro i
  simp only [Tw]
  split_ifs with h
  · rw [Submodule.baseChange_top]
    exact Submodule.mem_top
  · rw [cf_Fy_neg lam x (by omega)]
    exact Submodule.zero_mem _

end lin

end BR

namespace BR

section kill
variable {LL Ks D : Type} [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]

def ev (Ks : Type) [CommRing Ks] [Algebra LL Ks] (f : D →ₗ[LL] LL) : (Ks ⊗[LL] D) →ₗ[LL] Ks :=
  (TensorProduct.rid LL Ks).toLinearMap ∘ₗ LinearMap.lTensor Ks f

/- English proof (translation)
Simplify using `[ev, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]`.
-/
lemma ev_smul_tmul (f : D →ₗ[LL] LL) (x : Ks) (d : D) :
    ev Ks f (x • ((1 : Ks) ⊗ₜ[LL] d)) = x * algebraMap LL Ks (f d) := by
  simp [ev, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]

/- English proof (translation)
Rewrite `hv` using `[mem_bc_iff]`. Establish `h1 : f = (W.liftQ f (fun w hw => LinearMap.mem_ker.2 (hf w hw))) ∘ₗ W.mkQ` using `(Submodule.liftQ_mkQ W f _).symm`. Unfold `ev`. Rewrite using `[h1, LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply, hv, map_zero, map_zero]`.
-/
lemma ev_kill (f : D →ₗ[LL] LL) (W : Submodule LL D) (hf : ∀ w ∈ W, f w = 0) {v : Ks ⊗[LL] D}
    (hv : v ∈ W.baseChange Ks) : ev Ks f v = 0 := by
  rw [mem_bc_iff] at hv
  have h1 : f = (W.liftQ f (fun w hw => LinearMap.mem_ker.2 (hf w hw))) ∘ₗ W.mkQ :=
    (Submodule.liftQ_mkQ W f _).symm
  unfold ev
  rw [h1, LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply, hv, map_zero,
    map_zero]

end kill

section split
variable {O : Type} [CommRing O] {r : ℕ}

def sv (O : Type) [CommRing O] {r : ℕ} (k : Fin r) : Fin r → O := fun j => if k = j then 1 else 0

def ex (g : (Fin r → O) →ₗ[O] (Fin r → O)) (z : Fin r → PowerSeries O) : Fin r → PowerSeries O :=
  ∑ k, z k • cst (g (sv O k))

/- English proof (translation)
Unfold `ex`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul]`.
-/
lemma ex_smul (g : (Fin r → O) →ₗ[O] (Fin r → O)) (a : PowerSeries O) (z : Fin r → PowerSeries O) :
    ex g (a • z) = a • ex g z := by
  unfold ex
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul]

/- English proof (translation)
The claim follows from `Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h _, rfl⟩)`.
-/
lemma ex_mem (g : (Fin r → O) →ₗ[O] (Fin r → O)) (U : Submodule O (Fin r → O)) (h : ∀ v, g v ∈ U)
    (z : Fin r → PowerSeries O) : ex g z ∈ ext U :=
  Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h _, rfl⟩)

/- English proof (translation)
Unfold `ex`. Rewrite using `[Finset.sum_apply]`. Both sides reduce to the same expression.
-/
lemma ex_apply (g : (Fin r → O) →ₗ[O] (Fin r → O)) (z : Fin r → PowerSeries O) (l : Fin r) :
    ex g z l = ∑ k, z k * PowerSeries.C (g (sv O k) l) := by
  unfold ex
  rw [Finset.sum_apply]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `l`. Rewrite using `[Pi.add_apply, ex_apply, ex_apply, ← Finset.sum_add_distrib]`. Establish `: ∀ k, z k * PowerSeries.C (π (sv O k) l) + z k * PowerSeries.C (((LinearMap.id : (Fin r → O) →ₗ[O] (Fin r → O)) - π) (sv O k) l) = z k * PowerSeries.C (sv O k l)`. Introduce `k`. Rewrite using `[← mul_add, ← map_add, LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply, add_sub_cancel]`.

Simplify using `only [this, sv]`. Simplify using the standard rewrite rules.
-/
lemma ex_split (π : (Fin r → O) →ₗ[O] (Fin r → O)) (z : Fin r → PowerSeries O) :
    z = ex π z + ex (LinearMap.id - π) z := by
  funext l
  rw [Pi.add_apply, ex_apply, ex_apply, ← Finset.sum_add_distrib]
  have : ∀ k, z k * PowerSeries.C (π (sv O k) l) +
      z k * PowerSeries.C (((LinearMap.id : (Fin r → O) →ₗ[O] (Fin r → O)) - π) (sv O k) l) =
        z k * PowerSeries.C (sv O k l) := by
    intro k
    rw [← mul_add, ← map_add, LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply,
      add_sub_cancel]
  simp only [this, sv]
  simp

end split

section theta
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
  {LL : Type} [Field LL] [Algebra O LL] [IsFractionRing O LL] {D : Type} [AddCommGroup D]
  [Module LL D] {r : ℕ}

/- English proof (translation)
Introduce `v hv`. Rewrite `hv`, the goal using `[hU]`. Establish `h1 : ∑ k, algebraMap O LL ((ϖ • v) k) • lam k = algebraMap O LL (ϖ ^ 1) • ∑ k, algebraMap O LL (v k) • lam k`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, pow_one]`. Rewrite `hv` using `[h1]`. Conclude with `(W.smul_mem_iff (alg_ne (LL := LL) hϖ 1)).1 hv`.
-/
lemma sat_of_uIs (hϖ : Irreducible ϖ) (lam : Fin r → D) (W : Submodule LL D)
    (U : Submodule O (Fin r → O))
    (hU : ∀ v : Fin r → O, v ∈ U ↔ ∑ k, algebraMap O LL (v k) • lam k ∈ W) : Saturated ϖ U := by
  intro v hv
  rw [hU] at hv ⊢
  have h1 : ∑ k, algebraMap O LL ((ϖ • v) k) • lam k =
      algebraMap O LL (ϖ ^ 1) • ∑ k, algebraMap O LL (v k) • lam k := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, pow_one]
  rw [h1] at hv
  exact (W.smul_mem_iff (alg_ne (LL := LL) hϖ 1)).1 hv

/- English proof (translation)
Establish `hd : d ∈ Submodule.span LL (Set.range lam)` using `hS ▸ Submodule.mem_top`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun LL).1 hd`. Take `⟨N, o, ho⟩` from `den_fam (LL := LL) hϖ c`. Use `⟨N, o, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun k _ => by rw [← mul_smul, ho k]`.
-/
lemma den_D (hϖ : Irreducible ϖ) (lam : Fin r → D)
    (hS : Submodule.span LL (Set.range lam) = ⊤) (d : D) :
    ∃ (N : ℕ) (o : Fin r → O), algebraMap O LL (ϖ ^ N) • d = ∑ k, algebraMap O LL (o k) • lam k := by
  have hd : d ∈ Submodule.span LL (Set.range lam) := hS ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun LL).1 hd
  obtain ⟨N, o, ho⟩ := den_fam (LL := LL) hϖ c
  refine ⟨N, o, ?_⟩
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [← mul_smul, ho k]

/- English proof (translation)
Set `bD : Module.Basis (Fin r) LL D` to `Module.Basis.mk hI hS.ge`. Set `f : D →ₗ[LL] LL` to `bD.constr LL fun k => algebraMap O LL (g (sv O k) l)`. Establish `hf : ∀ k, f (lam k) = algebraMap O LL (g (sv O k) l)`. Introduce `k`. Establish `h1 : bD k = lam k` using `Module.Basis.mk_apply hI hS.ge k`.

Rewrite using `[← h1]`. Conclude with `bD.constr_basis LL _ k`. Use `⟨f, hf, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨N, o, ho⟩` from `den_D (LL := LL) hϖ lam hS w`. Establish `h1 : o ∈ U`.

Rewrite using `[hU, ← ho]`. Conclude with `W.smul_mem _ hw`. Establish `h2 : f (algebraMap O LL (ϖ ^ N) • w) = algebraMap O LL (g o l)`. Rewrite using `[ho, map_sum, LinearMap.pi_apply_eq_sum_univ g o, Finset.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, hf, smul_eq_mul, Pi.smul_apply, smul_eq_mul, map_mul]`. Both sides reduce to the same expression. Rewrite `h2` using `[hg o h1, Pi.zero_apply, map_zero, map_smul, smul_eq_mul]`. Conclude with `(mul_eq_zero.1 h2).resolve_left (alg_ne (LL := LL) hϖ N)`.
-/
lemma exists_theta (hϖ : Irreducible ϖ) (lam : Fin r → D) (hI : LinearIndependent LL lam)
    (hS : Submodule.span LL (Set.range lam) = ⊤) (W : Submodule LL D)
    (U : Submodule O (Fin r → O))
    (hU : ∀ v : Fin r → O, v ∈ U ↔ ∑ k, algebraMap O LL (v k) • lam k ∈ W)
    (g : (Fin r → O) →ₗ[O] (Fin r → O)) (hg : ∀ v ∈ U, g v = 0) (l : Fin r) :
    ∃ f : D →ₗ[LL] LL, (∀ k, f (lam k) = algebraMap O LL (g (sv O k) l)) ∧ ∀ w ∈ W, f w = 0 := by
  let bD : Module.Basis (Fin r) LL D := Module.Basis.mk hI hS.ge
  let f : D →ₗ[LL] LL := bD.constr LL fun k => algebraMap O LL (g (sv O k) l)
  have hf : ∀ k, f (lam k) = algebraMap O LL (g (sv O k) l) := by
    intro k
    have h1 : bD k = lam k := Module.Basis.mk_apply hI hS.ge k
    rw [← h1]
    exact bD.constr_basis LL _ k
  refine ⟨f, hf, fun w hw => ?_⟩
  obtain ⟨N, o, ho⟩ := den_D (LL := LL) hϖ lam hS w
  have h1 : o ∈ U := by
    rw [hU, ← ho]
    exact W.smul_mem _ hw
  have h2 : f (algebraMap O LL (ϖ ^ N) • w) = algebraMap O LL (g o l) := by
    rw [ho, map_sum, LinearMap.pi_apply_eq_sum_univ g o, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hf, smul_eq_mul, Pi.smul_apply, smul_eq_mul, map_mul]
    rfl
  rw [hg o h1, Pi.zero_apply, map_zero, map_smul, smul_eq_mul] at h2
  exact (mul_eq_zero.1 h2).resolve_left (alg_ne (LL := LL) hϖ N)

end theta

end BR

namespace BR

section core
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
  {LL : Type} [Field LL] [Algebra O LL] [IsFractionRing O LL] {Ks : Type} [CommRing Ks]
  [Algebra LL Ks] {D : Type} [AddCommGroup D] [Module LL D] {r : ℕ}

def FA (LL : Type) [Field LL] {Ks : Type} [CommRing Ks] [Algebra LL Ks] {D : Type} [AddCommGroup D]
    [Module LL D] (lam : Fin r → D) (ρ : PowerSeries O →+* PowerSeries Ks)
    (y : Fin r → PowerSeries O) : Amb LL Ks D :=
  Fy LL lam fun k => ρ (y k)

variable (lam : Fin r → D) (ρ : PowerSeries O →+* PowerSeries Ks)

omit [IsDomain O] [IsDiscreteValuationRing O] in
/- English proof (translation)
Simplify using `[FA, Fy]`.
-/
lemma FA_zero : FA LL lam ρ 0 = 0 := by
  simp [FA, Fy]

omit [IsDomain O] [IsDiscreteValuationRing O] in
/- English proof (translation)
Unfold `FA`. Rewrite using `[← Fy_add]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.
-/
lemma FA_add (y y' : Fin r → PowerSeries O) : FA LL lam ρ (y + y') = FA LL lam ρ y + FA LL lam ρ y' := by
  unfold FA
  rw [← Fy_add]
  congr 1
  funext k
  simp

omit [IsDomain O] [IsDiscreteValuationRing O] in
/- English proof (translation)
Unfold `FA`. Rewrite using `[← Fy_smul]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.
-/
lemma FA_smul (a : PowerSeries O) (y : Fin r → PowerSeries O) :
    FA LL lam ρ (a • y) = HahnSeries.ofPowerSeries ℤ Ks (ρ a) • FA LL lam ρ y := by
  unfold FA
  rw [← Fy_smul]
  congr 1
  funext k
  simp

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] in
/- English proof (translation)
Unfold `FA cst`. Simplify using `only [hρ]`. Conclude with `Fy_const lam _`.
-/
lemma FA_cst (hρ : ∀ a : O, ρ (PowerSeries.C a) =
      PowerSeries.C (algebraMap LL Ks (algebraMap O LL a))) (v : Fin r → O) :
    FA LL lam ρ (cst v) = cstD Ks (∑ k, algebraMap O LL (v k) • lam k) := by
  unfold FA cst
  simp only [hρ]
  exact Fy_const lam _

omit [IsDomain O] [IsDiscreteValuationRing O] in
/- English proof (translation)
Use `choose N z hz using fun k => hC m (y k) (h k)`. Use `⟨Finset.univ.sup N, fun k => PowerSeries.C (ϖ ^ (Finset.univ.sup N - N k)) * z k, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Establish `hle : N k ≤ Finset.univ.sup N` using `Finset.le_sup (Finset.mem_univ k)`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Establish `: ϖ ^ Finset.univ.sup N = ϖ ^ (Finset.univ.sup N - N k) * ϖ ^ N k`. Rewrite using `[← pow_add, Nat.sub_add_cancel hle]`. Rewrite using `[this, map_mul, mul_assoc, hz k]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma compl_vec {ρ : PowerSeries O →+* PowerSeries Ks} {p : PowerSeries O}
    (hC : ∀ (k : ℕ) (a : PowerSeries O), PowerSeries.X ^ k ∣ ρ a →
      ∃ (N : ℕ) (z : PowerSeries O), PowerSeries.C (ϖ ^ N) * a = p ^ k * z)
    (m : ℕ) (y : Fin r → PowerSeries O) (h : ∀ k, PowerSeries.X ^ m ∣ ρ (y k)) :
    ∃ (N : ℕ) (z : Fin r → PowerSeries O), PowerSeries.C (ϖ ^ N) • y = p ^ m • z := by
  choose N z hz using fun k => hC m (y k) (h k)
  refine ⟨Finset.univ.sup N, fun k => PowerSeries.C (ϖ ^ (Finset.univ.sup N - N k)) * z k, ?_⟩
  funext k
  have hle : N k ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ k)
  simp only [Pi.smul_apply, smul_eq_mul]
  have : ϖ ^ Finset.univ.sup N = ϖ ^ (Finset.univ.sup N - N k) * ϖ ^ N k := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [this, map_mul, mul_assoc, hz k]
  ring

variable {lam} {ρ}

/- English proof (translation)
Take `⟨π, hπ1, hπ2⟩` from `exists_retr hϖ U (sat_of_uIs (LL := LL) hϖ lam W U hU)`. Establish `h1 : ∀ k, PowerSeries.X ^ m ∣ ρ (y k)`. Introduce `k`. Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `i hi`.

Establish `h4` using `h (i : ℤ)`. Rewrite `h4` using `[FA, cf_Fy_nat]`. Simplify using `only [St] at h4`. Rewrite `h4` using `[if_pos (by exact_mod_cast hi), Submodule.baseChange_bot, Submodule.mem_bot]`. Conclude with `coeffs_zero lam hI _ h4 k`.

Establish `h2 : ∀ l, PowerSeries.X ^ m' ∣ ρ (ex (LinearMap.id - π) y l)`. Introduce `l`. Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `i hi`. Take `⟨f, hf1, hf2⟩` from `exists_theta (LL := LL) hϖ lam hI hS W U hU (LinearMap.id - π) (fun v hv => by rw [LinearMap.sub_apply, LinearMap.id_apply, hπ2 v hv, sub_self]) l`.

Establish `h4 : cf (FA LL lam ρ y) (i : ℤ) ∈ W.baseChange Ks`. Establish `h5` using `h (i : ℤ)`. Simplify using `only [St] at h5`. Rewrite `h5` using `[if_pos (show (i : ℤ) < (m' : ℤ) by exact_mod_cast hi)]`. Use `split_ifs at h5`.

Rewrite `h5` using `[Submodule.baseChange_bot, Submodule.mem_bot]`. Rewrite using `[h5]`. Conclude with `Submodule.zero_mem _`. Conclude with `h5`. Establish `h5` using `ev_kill f W hf2 h4`.

Rewrite `h5` using `[FA, cf_Fy_nat, map_sum]`. Simplify using `only [ev_smul_tmul, hf1] at h5`. Rewrite using `[ex_apply, map_sum, map_sum]`. Simplify using `only [map_mul, hρ, PowerSeries.coeff_mul_C]`. Conclude with `h5`.

Take `⟨N1, z1, hz1⟩` from `compl_vec hC m y h1`. Take `⟨N2, z2, hz2⟩` from `compl_vec hC m' _ h2`. Use `⟨N1 + N2, PowerSeries.C (ϖ ^ N2) • ex π z1, PowerSeries.C (ϖ ^ N1) • z2, Submodule.smul_mem _ _ (ex_mem π U hπ1 z1), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ex_split π y]`.

Use `_ = PowerSeries.C (ϖ ^ N2) • ex π (PowerSeries.C (ϖ ^ N1) • y) + PowerSeries.C (ϖ ^ N1) • (PowerSeries.C (ϖ ^ N2) • ex (LinearMap.id - π) y) := by`. Rewrite using `[ex_smul, smul_add, pow_add, map_mul, mul_smul, mul_smul, smul_comm (PowerSeries.C (ϖ ^ N1)) (PowerSeries.C (ϖ ^ N2)) (ex π y)]`. Use `_ = _ := by`. Rewrite using `[hz1, hz2, ex_smul, smul_comm (PowerSeries.C (ϖ ^ N2)) (p ^ m), smul_comm (PowerSeries.C (ϖ ^ N1)) (p ^ m')]`.
-/
theorem core_mp (hϖ : Irreducible ϖ) (hI : LinearIndependent LL lam)
    (hS : Submodule.span LL (Set.range lam) = ⊤) {W : Submodule LL D}
    {U : Submodule O (Fin r → O)}
    (hU : ∀ v : Fin r → O, v ∈ U ↔ ∑ k, algebraMap O LL (v k) • lam k ∈ W)
    (hρ : ∀ a : O, ρ (PowerSeries.C a) = PowerSeries.C (algebraMap LL Ks (algebraMap O LL a)))
    {p : PowerSeries O}
    (hC : ∀ (k : ℕ) (a : PowerSeries O), PowerSeries.X ^ k ∣ ρ a →
      ∃ (N : ℕ) (z : PowerSeries O), PowerSeries.C (ϖ ^ N) * a = p ^ k * z)
    (m m' : ℕ) (y : Fin r → PowerSeries O) (h : FA LL lam ρ y ∈ Xi Ks (St m m' W)) :
    ∃ (N : ℕ) (c z : Fin r → PowerSeries O), c ∈ ext U ∧
      PowerSeries.C (ϖ ^ N) • y = p ^ m • c + p ^ m' • z := by
  obtain ⟨π, hπ1, hπ2⟩ := exists_retr hϖ U (sat_of_uIs (LL := LL) hϖ lam W U hU)
  have h1 : ∀ k, PowerSeries.X ^ m ∣ ρ (y k) := by
    intro k
    rw [PowerSeries.X_pow_dvd_iff]
    intro i hi
    have h4 := h (i : ℤ)
    rw [FA, cf_Fy_nat] at h4
    simp only [St] at h4
    rw [if_pos (by exact_mod_cast hi), Submodule.baseChange_bot, Submodule.mem_bot] at h4
    exact coeffs_zero lam hI _ h4 k
  have h2 : ∀ l, PowerSeries.X ^ m' ∣ ρ (ex (LinearMap.id - π) y l) := by
    intro l
    rw [PowerSeries.X_pow_dvd_iff]
    intro i hi
    obtain ⟨f, hf1, hf2⟩ := exists_theta (LL := LL) hϖ lam hI hS W U hU (LinearMap.id - π)
      (fun v hv => by rw [LinearMap.sub_apply, LinearMap.id_apply, hπ2 v hv, sub_self]) l
    have h4 : cf (FA LL lam ρ y) (i : ℤ) ∈ W.baseChange Ks := by
      have h5 := h (i : ℤ)
      simp only [St] at h5
      rw [if_pos (show (i : ℤ) < (m' : ℤ) by exact_mod_cast hi)] at h5
      split_ifs at h5
      · rw [Submodule.baseChange_bot, Submodule.mem_bot] at h5
        rw [h5]
        exact Submodule.zero_mem _
      · exact h5
    have h5 := ev_kill f W hf2 h4
    rw [FA, cf_Fy_nat, map_sum] at h5
    simp only [ev_smul_tmul, hf1] at h5
    rw [ex_apply, map_sum, map_sum]
    simp only [map_mul, hρ, PowerSeries.coeff_mul_C]
    exact h5
  obtain ⟨N1, z1, hz1⟩ := compl_vec hC m y h1
  obtain ⟨N2, z2, hz2⟩ := compl_vec hC m' _ h2
  refine ⟨N1 + N2, PowerSeries.C (ϖ ^ N2) • ex π z1, PowerSeries.C (ϖ ^ N1) • z2,
    Submodule.smul_mem _ _ (ex_mem π U hπ1 z1), ?_⟩
  calc PowerSeries.C (ϖ ^ (N1 + N2)) • y
      = PowerSeries.C (ϖ ^ (N1 + N2)) • (ex π y + ex (LinearMap.id - π) y) := by
        rw [← ex_split π y]
    _ = PowerSeries.C (ϖ ^ N2) • ex π (PowerSeries.C (ϖ ^ N1) • y) +
          PowerSeries.C (ϖ ^ N1) • (PowerSeries.C (ϖ ^ N2) • ex (LinearMap.id - π) y) := by
        rw [ex_smul, smul_add, pow_add, map_mul, mul_smul, mul_smul,
          smul_comm (PowerSeries.C (ϖ ^ N1)) (PowerSeries.C (ϖ ^ N2)) (ex π y)]
    _ = _ := by
        rw [hz1, hz2, ex_smul, smul_comm (PowerSeries.C (ϖ ^ N2)) (p ^ m),
          smul_comm (PowerSeries.C (ϖ ^ N1)) (p ^ m')]

/- English proof (translation)
Take `⟨N, c, z, hc, he⟩` from `h`. Establish `hcW : FA LL lam ρ c ∈ Xi Ks (Wp W)` using `by clear he`. Unfold `ext at hc`. Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨v, hv, rfl⟩` from `hx`. Rewrite using `[FA_cst lam ρ hρ]`. Conclude with `cst_mem_wp ((hU v).1 hv)`. Consider the case `zero`. Rewrite using `[FA_zero]`.

Conclude with `AddSubgroup.zero_mem _`. Consider the case `add x y _ _ hx hy`. Rewrite using `[FA_add]`. Conclude with `AddSubgroup.add_mem _ hx hy`. Consider the case `smul a x _ hx`.

Rewrite using `[FA_smul]`. Conclude with `xi_module_structure LL Ks D _ (wp_mono W) _ _ hx`. Establish `hρp : ∀ a : ℕ, ρ (p ^ a) = ((ε ^ a : (PowerSeries Ks)ˣ) : PowerSeries Ks) * PowerSeries.X ^ a`. Introduce `a`. Rewrite using `[map_pow, hp, mul_pow, Units.val_pow_eq_pow_val]`.

Establish `h1 : HahnSeries.ofPowerSeries ℤ Ks (ρ (p ^ m)) • FA LL lam ρ c ∈ Xi Ks (St m m' W)`. Rewrite using `[hρp]`. Use `xi_mono (fun i => ?_) ((shift_iff (wp_mono W) (ε ^ m) m _).2 hcW)` and prove the remaining obligations. Simplify using `only [Wp, St]`. Apply the tactic sequence `split_ifs <;> first | exact le_rfl | exact bot_le | exact le_top | omega`.

Establish `h2 : HahnSeries.ofPowerSeries ℤ Ks (ρ (p ^ m')) • FA LL lam ρ z ∈ Xi Ks (St m m' W)`. Rewrite using `[hρp]`. Use `xi_mono (fun i => ?_) ((shift_iff (tw_mono 0) (ε ^ m') m' _).2 (Fy_mem_tw lam _))` and prove the remaining obligations. Simplify using `only [Tw, St]`. Apply the tactic sequence `split_ifs <;> first | exact le_rfl | exact bot_le | exact le_top | omega`.

Establish `h3 : HahnSeries.ofPowerSeries ℤ Ks (ρ (PowerSeries.C (ϖ ^ N))) • FA LL lam ρ y ∈ Xi Ks (St m m' W)`. Rewrite using `[← FA_smul, he, FA_add, FA_smul, FA_smul]`. Conclude with `AddSubgroup.add_mem _ h1 h2`. Use `unit_smul_mem (st_mono _ _ W) ?_ h3` and prove the remaining obligations. Rewrite using `[hρ]`.

Conclude with `isUnit_C_alg (alg_ne (LL := LL) hϖ N)`.
-/
theorem core_mpr (hϖ : Irreducible ϖ) {W : Submodule LL D} {U : Submodule O (Fin r → O)}
    (hU : ∀ v : Fin r → O, v ∈ U ↔ ∑ k, algebraMap O LL (v k) • lam k ∈ W)
    (hρ : ∀ a : O, ρ (PowerSeries.C a) = PowerSeries.C (algebraMap LL Ks (algebraMap O LL a)))
    {p : PowerSeries O} (ε : (PowerSeries Ks)ˣ) (hp : ρ p = (ε : PowerSeries Ks) * PowerSeries.X)
    (m m' : ℕ) (hm : m ≤ m') (y : Fin r → PowerSeries O)
    (h : ∃ (N : ℕ) (c z : Fin r → PowerSeries O), c ∈ ext U ∧
      PowerSeries.C (ϖ ^ N) • y = p ^ m • c + p ^ m' • z) :
    FA LL lam ρ y ∈ Xi Ks (St m m' W) := by
  obtain ⟨N, c, z, hc, he⟩ := h
  have hcW : FA LL lam ρ c ∈ Xi Ks (Wp W) := by
    clear he
    unfold ext at hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      rw [FA_cst lam ρ hρ]
      exact cst_mem_wp ((hU v).1 hv)
    | zero =>
      rw [FA_zero]
      exact AddSubgroup.zero_mem _
    | add x y _ _ hx hy =>
      rw [FA_add]
      exact AddSubgroup.add_mem _ hx hy
    | smul a x _ hx =>
      rw [FA_smul]
      exact xi_module_structure LL Ks D _ (wp_mono W) _ _ hx
  have hρp : ∀ a : ℕ, ρ (p ^ a) =
      ((ε ^ a : (PowerSeries Ks)ˣ) : PowerSeries Ks) * PowerSeries.X ^ a := by
    intro a
    rw [map_pow, hp, mul_pow, Units.val_pow_eq_pow_val]
  have h1 : HahnSeries.ofPowerSeries ℤ Ks (ρ (p ^ m)) • FA LL lam ρ c ∈ Xi Ks (St m m' W) := by
    rw [hρp]
    refine xi_mono (fun i => ?_) ((shift_iff (wp_mono W) (ε ^ m) m _).2 hcW)
    simp only [Wp, St]
    split_ifs <;> first | exact le_rfl | exact bot_le | exact le_top | omega
  have h2 : HahnSeries.ofPowerSeries ℤ Ks (ρ (p ^ m')) • FA LL lam ρ z ∈ Xi Ks (St m m' W) := by
    rw [hρp]
    refine xi_mono (fun i => ?_) ((shift_iff (tw_mono 0) (ε ^ m') m' _).2 (Fy_mem_tw lam _))
    simp only [Tw, St]
    split_ifs <;> first | exact le_rfl | exact bot_le | exact le_top | omega
  have h3 : HahnSeries.ofPowerSeries ℤ Ks (ρ (PowerSeries.C (ϖ ^ N))) • FA LL lam ρ y ∈
      Xi Ks (St m m' W) := by
    rw [← FA_smul, he, FA_add, FA_smul, FA_smul]
    exact AddSubgroup.add_mem _ h1 h2
  refine unit_smul_mem (st_mono _ _ W) ?_ h3
  rw [hρ]
  exact isUnit_C_alg (alg_ne (LL := LL) hϖ N)

end core

end BR

namespace BR

section model
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} {B : E.Base O}
  {n : ℕ} {V : Type} [AddCommGroup V] [Module (PowerSeries O) V] {L : E.Lat B n V} {c : ZMod n}
  {ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {S : E.LevelData L c ell (abelian₂ B.p H ell) r} {LL : Type} [Field LL]
  [Algebra O LL] {Ks : ℕ → Type} [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] {Δ D : Type}
  [AddCommGroup D] [Module LL D] {R : LevelModel S LL Ks Δ D} {η : ℕ} {kind : ℕ → Kind}
  {b : ℕ → ℕ} {lam : Fin r → D} {U : ℕ → Submodule O (Fin r → O)}

omit [IsDomain O] [IsDiscreteValuationRing O] in

/- English proof (translation)
Take `⟨εΛ, hΛ⟩` from `rho_prod R h.k1b h.unitsAt s hs H`. Establish `hF : HahnSeries.ofPowerSeries ℤ (Ks s) ((εΛ : PowerSeries (Ks s)) * PowerSeries.X ^ H s) • R.pr s (S.locL s y) = FA LL lam (R.ρ s) y`. Rewrite using `[← hΛ, ← R.pr_smul]`. Conclude with `h.locLIs s hs y`. Rewrite using `[R.mem_Nb s hs, h.kind_eq s hs, h.b_eq s hs, h.η_eq, ← shift_iff (nbK_mono (kind s) (b s) (Int.natCast_nonneg _) _) εΛ (H s), hF]`.

Prove the components needed by the constructor for the conclusion. Introduce `h1 i`. Distinguish the cases in `hi : 0 ≤ i`. Rewrite using `[← hX i hi]`. Conclude with `h1 i`.

Rewrite using `[FA, cf_Fy_neg lam _ (by omega)]`. Conclude with `Submodule.zero_mem _`. Introduce `h1 i`. Distinguish the cases in `hi : 0 ≤ i`. Express the relevant statement in the definitionally equal form `_ ∈ (NbK (kind s) (b s) (UOf (kind s) (b s) η (R.Fil s)) (i - H s)).baseChange (Ks s)`.

Rewrite using `[hX i hi]`. Conclude with `h1 i`. Rewrite using `[FA, cf_Fy_neg lam _ (by omega)]`. Conclude with `Submodule.zero_mem _`.
-/
lemma nb_iff (h : BridgeItems R ϖ η kind b lam U) {s : ℕ} (hs : s < ell)
    (y : Fin r → PowerSeries O) (m m' : ℕ)
    (hX : ∀ i : ℤ, 0 ≤ i → NbK (kind s) (b s) (UOf (kind s) (b s) η (R.Fil s)) (i - H s) =
      St m m' (UOf (kind s) (b s) η (R.Fil s)) i) :
    S.locL s y ∈ S.Nb s ↔
      FA LL lam (R.ρ s) y ∈ Xi (Ks s) (St m m' (UOf (kind s) (b s) η (R.Fil s))) := by
  obtain ⟨εΛ, hΛ⟩ := rho_prod R h.k1b h.unitsAt s hs H
  have hF : HahnSeries.ofPowerSeries ℤ (Ks s) ((εΛ : PowerSeries (Ks s)) * PowerSeries.X ^ H s) •
      R.pr s (S.locL s y) = FA LL lam (R.ρ s) y := by
    rw [← hΛ, ← R.pr_smul]
    exact h.locLIs s hs y
  rw [R.mem_Nb s hs, h.kind_eq s hs, h.b_eq s hs, h.η_eq,
    ← shift_iff (nbK_mono (kind s) (b s) (Int.natCast_nonneg _) _) εΛ (H s), hF]
  constructor
  · intro h1 i
    by_cases hi : 0 ≤ i
    · rw [← hX i hi]
      exact h1 i
    · rw [FA, cf_Fy_neg lam _ (by omega)]
      exact Submodule.zero_mem _
  · intro h1 i
    by_cases hi : 0 ≤ i
    · change _ ∈ (NbK (kind s) (b s) (UOf (kind s) (b s) η (R.Fil s)) (i - H s)).baseChange (Ks s)
      rw [hX i hi]
      exact h1 i
    · rw [FA, cf_Fy_neg lam _ (by omega)]
      exact Submodule.zero_mem _

/- English proof (translation)
Use `h.frac` as an intermediate fact. Take `⟨ε, hε⟩` from `h.k1b s hs`. Establish `core : ∀ m m' : ℕ, m ≤ m' → (FA LL lam (R.ρ s) y ∈ Xi (Ks s) (St m m' (UOf (kind s) (b s) η (R.Fil s))) ↔ ∃ (N : ℕ) (c z : Fin r → PowerSeries O), c ∈ ext (U s) ∧ PowerSeries.C (ϖ ^ N) • y = B.p s ^ m • c + B.p s ^ m' • z)` using `fun m m' hm => ⟨core_mp hϖ h.lamInd h.lamSpan (h.uIs s hs) (R.ρ_C s) (h.compl s hs) m m' y, core_mpr hϖ (h.uIs s hs) (R.ρ_C s) ε hε m m' hm y⟩`. Consider the cases of `hk : kind s with`. Consider the case `thin`.

Rewrite using `[nb_iff h hs y (H s) (H s) (fun i hi => by`. Simplify using `only [hk, NbK, NbThin, St]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega), core _ _ le_rfl]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨N, c, z, -, he⟩`.

Conclude with `⟨N, c + z, by rw [he, smul_add]⟩`. Introduce and unpack `⟨N, z, he⟩`. Conclude with `⟨N, 0, z, Submodule.zero_mem _, by rw [he, smul_zero, zero_add]⟩`. Consider the case `up`. Rewrite using `[nb_iff h hs y (H s - b s) (H s) (fun i hi => by`.

Simplify using `only [hk, NbK, NbUp, St]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega), core _ _ (Nat.sub_le _ _)]`. Both sides reduce to the same expression. Consider the case `down`. Rewrite using `[nb_iff h hs y (H s) (H s + b s) (fun i hi => by`.

Simplify using `only [hk, NbK, NbDown, St]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega), core _ _ (Nat.le_add_right _ _)]`. Both sides reduce to the same expression.
-/
theorem level_iff (hϖ : Irreducible ϖ) (h : BridgeItems R ϖ η kind b lam U) {s : ℕ} (hs : s < ell)
    (y : Fin r → PowerSeries O) :
    S.locL s y ∈ S.Nb s ↔ LevelCond ϖ (B.p s) (H s) (b s) (kind s) (U s) y := by
  have := h.frac
  obtain ⟨ε, hε⟩ := h.k1b s hs
  have core : ∀ m m' : ℕ, m ≤ m' →
      (FA LL lam (R.ρ s) y ∈ Xi (Ks s) (St m m' (UOf (kind s) (b s) η (R.Fil s))) ↔
        ∃ (N : ℕ) (c z : Fin r → PowerSeries O), c ∈ ext (U s) ∧
          PowerSeries.C (ϖ ^ N) • y = B.p s ^ m • c + B.p s ^ m' • z) := fun m m' hm =>
    ⟨core_mp hϖ h.lamInd h.lamSpan (h.uIs s hs) (R.ρ_C s) (h.compl s hs) m m' y,
      core_mpr hϖ (h.uIs s hs) (R.ρ_C s) ε hε m m' hm y⟩
  cases hk : kind s with
  | thin =>
    rw [nb_iff h hs y (H s) (H s) (fun i hi => by
      simp only [hk, NbK, NbThin, St]
      split_ifs <;> first | rfl | omega), core _ _ le_rfl]
    constructor
    · rintro ⟨N, c, z, -, he⟩
      exact ⟨N, c + z, by rw [he, smul_add]⟩
    · rintro ⟨N, z, he⟩
      exact ⟨N, 0, z, Submodule.zero_mem _, by rw [he, smul_zero, zero_add]⟩
  | up =>
    rw [nb_iff h hs y (H s - b s) (H s) (fun i hi => by
      simp only [hk, NbK, NbUp, St]
      split_ifs <;> first | rfl | omega), core _ _ (Nat.sub_le _ _)]
    rfl
  | down =>
    rw [nb_iff h hs y (H s) (H s + b s) (fun i hi => by
      simp only [hk, NbK, NbDown, St]
      split_ifs <;> first | rfl | omega), core _ _ (Nat.le_add_right _ _)]
    rfl

omit [IsDomain O] [IsDiscreteValuationRing O] in

/- English proof (translation)
Establish `h1 : R.pr s (abelian₂ B.p H ell • S.locL s (cst o)) = R.pr s (PowerSeries.C (ϖ ^ N) • e)`. Establish `h2 : R.pr s (abelian₂ B.p H ell • S.locL s (cst o)) = FA LL lam (R.ρ s) (cst o)` using `h.locLIs s hs (cst o)`. Rewrite using `[h2, FA_cst lam (R.ρ s) (R.ρ_C s), ← hd, R.pr_smul, he, R.ρ_C]`. Establish `h3` using `Fy_const (Ks := Ks s) (fun _ : Fin 1 => d) (fun _ => algebraMap O LL (ϖ ^ N))`. Simplify using `only [Fy, Finset.univ_unique, Finset.sum_singleton] at h3`.

Conclude with `h3.symm`. Rewrite using `[map_sub, map_smul, map_smul, map_sub, smul_sub, map_sub, h1]`.
-/
lemma pr_key (h : BridgeItems R ϖ η kind b lam U) {s : ℕ} (hs : s < ell)
    (y : Fin r → PowerSeries O) (N : ℕ) (o : Fin r → O) (d : D) (e : S.Lv)
    (hd : algebraMap O LL (ϖ ^ N) • d = ∑ k, algebraMap O LL (o k) • lam k)
    (he : R.pr s e = cstD (Ks s) d) :
    R.pr s (S.locL s (PowerSeries.C (ϖ ^ N) • y - abelian₂ B.p H ell • cst o)) =
      R.pr s (PowerSeries.C (ϖ ^ N) • (S.locL s y - e)) := by
  have h1 : R.pr s (abelian₂ B.p H ell • S.locL s (cst o)) = R.pr s (PowerSeries.C (ϖ ^ N) • e) := by
    have h2 : R.pr s (abelian₂ B.p H ell • S.locL s (cst o)) = FA LL lam (R.ρ s) (cst o) :=
      h.locLIs s hs (cst o)
    rw [h2, FA_cst lam (R.ρ s) (R.ρ_C s), ← hd, R.pr_smul, he, R.ρ_C]
    have h3 := Fy_const (Ks := Ks s) (fun _ : Fin 1 => d) (fun _ => algebraMap O LL (ϖ ^ N))
    simp only [Fy, Finset.univ_unique, Finset.sum_singleton] at h3
    exact h3.symm
  rw [map_sub, map_smul, map_smul, map_sub, smul_sub, map_sub, h1]

/- English proof (translation)
Use `h.frac` as an intermediate fact. Use `⟨fun y => forall₂_congr fun s hs => level_iff hϖ h hs y, fun y => forall₂_congr fun s hs => ?_⟩` and prove the remaining obligations. Establish `hmono` using `nbK_mono (kind s) (b s) (Int.natCast_nonneg _) (UOf (kind s) (b s) η (R.Fil s))`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨e, he, hy⟩`.

Take `⟨d, hd⟩` from `(R.mem_Dc s hs e).1 he`. Take `⟨N, o, ho⟩` from `den_D (LL := LL) hϖ lam h.lamSpan d`. Use `⟨o, N, (level_iff hϖ h hs _).1 ?_⟩` and prove the remaining obligations. Rewrite using `[R.mem_Nb s hs, pr_key h hs y N o d e ho (hd s hs), ← R.mem_Nb s hs]`. Conclude with `Submodule.smul_mem _ _ hy`.

Introduce and unpack `⟨o, N, hc⟩`. Establish `h1` using `(level_iff hϖ h hs _).2 hc`. Establish `hne` using `alg_ne (LL := LL) hϖ N`. Take `⟨e, he, hpe⟩` from `exists_Dc R s hs ((algebraMap O LL (ϖ ^ N))⁻¹ • ∑ k, algebraMap O LL (o k) • lam k)`. Use `⟨e, he, ?_⟩` and prove the remaining obligations.

Rewrite `h1` using `[R.mem_Nb s hs, pr_key h hs y N o _ e (by rw [smul_smul, mul_inv_cancel₀ hne, one_smul]) hpe, R.pr_smul, R.ρ_C, h.kind_eq s hs, h.b_eq s hs, h.η_eq]`. Rewrite using `[R.mem_Nb s hs, h.kind_eq s hs, h.b_eq s hs, h.η_eq]`. Conclude with `unit_smul_mem hmono (isUnit_C_alg hne) h1`.
-/
theorem bridge (hϖ : Irreducible ϖ) (h : BridgeItems R ϖ η kind b lam U) :
    S.Bridge ϖ H b kind U := by
  have := h.frac
  refine ⟨fun y => forall₂_congr fun s hs => level_iff hϖ h hs y,
    fun y => forall₂_congr fun s hs => ?_⟩
  have hmono := nbK_mono (kind s) (b s) (Int.natCast_nonneg _) (UOf (kind s) (b s) η (R.Fil s))
  constructor
  · rintro ⟨e, he, hy⟩
    obtain ⟨d, hd⟩ := (R.mem_Dc s hs e).1 he
    obtain ⟨N, o, ho⟩ := den_D (LL := LL) hϖ lam h.lamSpan d
    refine ⟨o, N, (level_iff hϖ h hs _).1 ?_⟩
    rw [R.mem_Nb s hs, pr_key h hs y N o d e ho (hd s hs), ← R.mem_Nb s hs]
    exact Submodule.smul_mem _ _ hy
  · rintro ⟨o, N, hc⟩
    have h1 := (level_iff hϖ h hs _).2 hc
    have hne := alg_ne (LL := LL) hϖ N
    obtain ⟨e, he, hpe⟩ := exists_Dc R s hs
      ((algebraMap O LL (ϖ ^ N))⁻¹ • ∑ k, algebraMap O LL (o k) • lam k)
    refine ⟨e, he, ?_⟩
    rw [R.mem_Nb s hs, pr_key h hs y N o _ e (by rw [smul_smul, mul_inv_cancel₀ hne, one_smul]) hpe,
      R.pr_smul, R.ρ_C, h.kind_eq s hs, h.b_eq s hs, h.η_eq] at h1
    rw [R.mem_Nb s hs, h.kind_eq s hs, h.b_eq s hs, h.η_eq]
    exact unit_smul_mem hmono (isUnit_C_alg hne) h1

end model

end BR

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ B n V _ _ L c ell H r S LL _ _ Ks _ _ Δ D _ _ R η kind b lam U h`. Conclude with `BR.bridge hϖ h`.
-/
theorem lattice_transfer_holds : BridgeOf := by
  intro O _ _ _ ϖ hϖ B n V _ _ L c ell H r S LL _ _ Ks _ _ Δ D _ _ R η kind b lam U h
  exact BR.bridge hϖ h

end Formalism.ExponentWindows.G
