import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PHeckeFormal

noncomputable section

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

/- English proof (translation)
Introduce `a b h`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Establish `h2` using `congrArg (fun g : GL (Fin N) L => (g : Matrix (Fin N) (Fin N) L) i j) h`. Simplify using `[toK] at h2`.

Conclude with `h2` after adjusting the coercions.
-/
theorem toK_injective (L : Type) [Field L] [NumberField L] (N : ℕ) : Function.Injective (toK L N) := by
  intro a b h
  apply Units.ext
  ext i j
  have h2 := congrArg (fun g : GL (Fin N) L => (g : Matrix (Fin N) (Fin N) L) i j) h
  simp [toK] at h2
  exact_mod_cast h2

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [dC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem dC_addS {Y : Type} {m : ℕ} (F F' : (Fin (m + 1) → Y) → ℝ) (c : ℝ) :
    dC (F + c • F') = dC F + c • dC F' := by
  funext y
  simp only [dC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `[dC]`.
-/
theorem dC_zeroS {Y : Type} {m : ℕ} : dC (0 : (Fin (m + 1) → Y) → ℝ) = 0 := by
  funext y
  simp [dC]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `[hecke]`.
-/
theorem hecke_zero {G H K Y : Type} [Group G] [Group H] [Group K] [MulAction H Y] (ρ : G →* K) (τ : K →* H)
    (q : K) : hecke ρ τ q (0 : Y → ℝ) = 0 := by
  funext y
  simp [hecke]

section
variable {G H Y : Type} [Group G] [Group H] [MulAction H Y]

/- English proof (translation)
Unfold `ev`. Simplify using `only [Pi.add_apply, mul_add]`. Conclude with `Finsupp.sum_add`.
-/
theorem ev_fadd1 (ρ : G →* H) {m : ℕ} (F F' : (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn G m) :
    ev ρ (F + F') y z = ev ρ F y z + ev ρ F' y z := by
  unfold ev
  simp only [Pi.add_apply, mul_add]
  exact Finsupp.sum_add

/- English proof (translation)
Unfold `ev`. Rewrite using `[Finsupp.mul_sum]`. Conclude with `Finsupp.sum_congr fun g _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring`.
-/
theorem ev_fsmul (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (c : ℝ) (y : Y) (z : Chn G m) :
    ev ρ (c • F) y z = c * ev ρ F y z := by
  unfold ev
  rw [Finsupp.mul_sum]
  exact Finsupp.sum_congr fun g _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

end

def invCoc (L : Type) [Field L] [NumberField L] (n k : ℕ) : Submodule ℝ ((Fin (k + 2) → GK L n) → ℝ) where
  carrier := {G | Inv (toK L n) G ∧ dC G = 0}
  add_mem' := fun {F F'} hF hF' => ⟨fun g y => by
      simp only [Pi.add_apply]
      rw [hF.1, hF'.1], by
      have h := dC_addS F F' 1
      rw [one_smul, one_smul] at h
      rw [h, hF.2, hF'.2, add_zero]⟩
  zero_mem' := ⟨fun _ _ => rfl, dC_zeroS⟩
  smul_mem' := fun c F hF => ⟨fun g y => by
      simp only [Pi.smul_apply]
      rw [hF.1], by
      have h := dC_addS 0 F c
      rw [zero_add, dC_zeroS, zero_add] at h
      rw [h, hF.2, smul_zero]⟩

def resF (L : Type) [Field L] [NumberField L] (n r k : ℕ) (G : (Fin (k + 2) → GK L (n + r)) → ℝ) :
    (Fin (k + 2) → GK L n) → ℝ :=
  fun y => G fun j => stab L n (n + r) (Nat.le_add_right n r) (y j)

/- English proof (translation)
Establish `hk : LinearMap.ker P ≤ LinearMap.ker Q` using `fun v hv => h v hv`. Take `⟨M, hM⟩` from `LinearMap.exists_extend (((LinearMap.ker P).liftQ Q hk).comp (P.quotKerEquivRange.symm : LinearMap.range P →ₗ[ℝ] V ⧸ LinearMap.ker P))`. Use `⟨‖LinearMap.toContinuousLinearMap M‖, norm_nonneg _, fun v => ?_⟩` and prove the remaining obligations. Establish `hv : Q v = M (P v)`. Use `LinearMap.congr_fun hM ⟨P v, LinearMap.mem_range_self P v⟩` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply] at this`. Rewrite using `[this, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image]`. Both sides reduce to the same expression. Rewrite using `[hv]`. Conclude with `(LinearMap.toContinuousLinearMap M).le_opNorm (P v)`.
-/
private theorem lift_map_comp {V ι : Type} [AddCommGroup V] [Module ℝ V] [Fintype ι]
    (P Q : V →ₗ[ℝ] (ι → ℝ)) (h : ∀ v, P v = 0 → Q v = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v, ‖Q v‖ ≤ K * ‖P v‖ := by
  have hk : LinearMap.ker P ≤ LinearMap.ker Q := fun v hv => h v hv
  obtain ⟨M, hM⟩ := LinearMap.exists_extend (((LinearMap.ker P).liftQ Q hk).comp
    (P.quotKerEquivRange.symm : LinearMap.range P →ₗ[ℝ] V ⧸ LinearMap.ker P))
  refine ⟨‖LinearMap.toContinuousLinearMap M‖, norm_nonneg _, fun v => ?_⟩
  have hv : Q v = M (P v) := by
    have := LinearMap.congr_fun hM ⟨P v, LinearMap.mem_range_self P v⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  rw [hv]
  exact (LinearMap.toContinuousLinearMap M).le_opNorm (P v)

/- English proof (translation)
Introduce `z hz`. Take `⟨z', hz', hb⟩` from `hs z hz`. Establish `h1 : z' ∈ LinearMap.ker E` using `(Submodule.span_le (p := LinearMap.ker E)).2 (fun w hw => h0 w hw) hz'`. Establish `h2` using `hbd _ hb`. Rewrite `h2` using `[map_sub, LinearMap.mem_ker.1 h1, sub_zero]`.

Conclude with `h2`.
-/
private theorem eq_zero_of_mem_all_maximalIdeal_pow {G : Type} [Group G] {k : ℕ} (E : Chn G (k + 1) →ₗ[ℝ] ℝ)
    (s : Finset (Chn G (k + 1)))
    (hs : ∀ z, IsCyc z → ∃ z' ∈ Submodule.span ℝ (s : Set (Chn G (k + 1))), IsBd (z - z'))
    (hbd : ∀ z, IsBd z → E z = 0) (h0 : ∀ z ∈ s, E z = 0) : ∀ z, IsCyc z → E z = 0 := by
  intro z hz
  obtain ⟨z', hz', hb⟩ := hs z hz
  have h1 : z' ∈ LinearMap.ker E :=
    (Submodule.span_le (p := LinearMap.ker E)).2 (fun w hw => h0 w hw) hz'
  have h2 := hbd _ hb
  rw [map_sub, LinearMap.mem_ker.1 h1, sub_zero] at h2
  exact h2

/- English proof (translation)
Unfold `ev cmap`. Rewrite using `[Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]`. Use `Finsupp.sum_congr fun g _ => ?_` and prove the remaining obligations. Simplify using `only [resF, smul_eq_mul, mul_one, ← map_partialProd, hc]`.
-/
private theorem ev_resF_eq_ev_cmap_stab (L : Type) [Field L] [NumberField L] (n r k : ℕ)
    (hc : ∀ c : Gm L n, toK L (n + r) (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) c) =
      stab L n (n + r) (Nat.le_add_right n r) (toK L n c))
    (G : (Fin (k + 2) → GK L (n + r)) → ℝ) (z : Chn (Gm L n) (k + 1)) :
    ev (toK L n) (resF L n r k G) 1 z =
      ev (toK L (n + r)) G 1 (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1) z) := by
  unfold ev cmap
  rw [Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
  refine Finsupp.sum_congr fun g _ => ?_
  simp only [resF, smul_eq_mul, mul_one, ← map_partialProd, hc]

/- English proof (translation)
Use `⟨Finsupp.lsum ℝ fun g => LinearMap.id.smulRight (F fun j => ρ (Fin.partialProd g j) • y), fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.lsum_apply]`. Unfold `ev`. Use `Finsupp.sum_congr fun g _ => ?_` and prove the remaining obligations. Simplify using `[smul_eq_mul]`.
-/
private theorem exists_linearMap_eq_ev {G : Type} [Group G] {H Y : Type} [Group H] [MulAction H Y] (ρ : G →* H)
    {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) :
    ∃ E : Chn G m →ₗ[ℝ] ℝ, ∀ z, E z = ev ρ F y z := by
  refine ⟨Finsupp.lsum ℝ fun g => LinearMap.id.smulRight (F fun j => ρ (Fin.partialProd g j) • y),
    fun z => ?_⟩
  rw [Finsupp.lsum_apply]
  unfold ev
  refine Finsupp.sum_congr fun g _ => ?_
  simp [smul_eq_mul]

/- English proof (translation)
Unfold `SHecke`. Introduce `L _ _ hL k hk π hπ`. Establish `hπ0 : π ≠ 0` using `hπ.ne_zero`. Establish `hCh'` using `hCh`. Take `⟨_, hcm, _, _⟩` from `hCh`.

Establish `hbdmap : ∀ {G H : Type} [Group G] [Group H] (f : G →* H) (w : Chn G (k + 1)), IsBd w → IsBd (cmap f (k + 1) w)`. Introduce `G H _ _ f w hw`. Take `⟨v, rfl⟩` from `hw`. Conclude with `⟨cmap f (k + 2) v, hcm G H f (k + 1) v⟩`. Establish `hcycmap : ∀ {G H : Type} [Group G] [Group H] (f : G →* H) (w : Chn G (k + 1)), IsCyc w → IsCyc (cmap f (k + 1) w)`.

Introduce `G H _ _ f w hw`. Unfold `IsCyc at *`. Rewrite using `[hcm, hw, map_zero]`. Use `set n := 2 * (k + 1) + 4 with hn_def`. Establish `hn1 : 1 ≤ n` using `by omega`.

Take `⟨s, hs1, hs2⟩` from `hFin L hL n k`. Establish `hfinn` using `(hI L n π hπ).1`. Set `P : invCoc L n k →ₗ[ℝ] (↥s → ℝ)` to `{ toFun := fun H z₀ => ev (toK L n) (H : (Fin (k + 2) → GK L n) → ℝ) 1 z₀.1 map_add' := fun H H' => by`. Use function extensionality and compare the values at `z₀`. Simplify using `only [Submodule.coe_add, ev_fadd1, Pi.add_apply]`.

Use the proof step `map_smul' := fun c H => by`. Use function extensionality and compare the values at `z₀`. Simplify using `only [Submodule.coe_smul, ev_fsmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }`. Set `Q : invCoc L n k →ₗ[ℝ] (↥s → ℝ)` to `{ toFun := fun H z₀ => ev (toK L n) (hecke (toK L n) (MonoidHom.id (GK L n)) (qel L n π hπ0) (H : (Fin (k + 2) → GK L n) → ℝ)) 1 z₀.1 map_add' := fun H H' => by`. Use function extensionality and compare the values at `z₀`.

Establish `h1` using `(hF _ _ (toK L n) _ hfinn (k + 1) H H' 1 H.2.1).2.2`. Rewrite `h1` using `[one_smul, one_smul]`. Simplify using `only [Submodule.coe_add, h1, ev_fadd1, Pi.add_apply]`. Use the proof step `map_smul' := fun c H => by`. Use function extensionality and compare the values at `z₀`.

Establish `h1` using `(hF _ _ (toK L n) _ hfinn (k + 1) 0 H c (fun _ _ => rfl)).2.2`. Rewrite `h1` using `[zero_add, hecke_zero, zero_add]`. Simplify using `only [Submodule.coe_smul, h1, ev_fsmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }`. Establish `hPQ : ∀ H, P H = 0 → Q H = 0`. Introduce `H hH`.

Establish `hvan : ∀ z : Chn (Gm L n) (k + 1), IsCyc z → ev (toK L n) (H : (Fin (k + 2) → GK L n) → ℝ) 1 z = 0`. Take `⟨E, hE⟩` from `exists_linearMap_eq_ev (toK L n) (H : (Fin (k + 2) → GK L n) → ℝ) (1 : GK L n)`. Introduce `z hz`. Rewrite using `[← hE]`. Use `eq_zero_of_mem_all_maximalIdeal_pow E s hs2 (fun w hw => ?_) (fun w hw => ?_) z hz` and prove the remaining obligations.

Rewrite using `[hE]`. Conclude with `(hEv _ _ _ (toK L n) k _ H.2.1 H.2.2).1 1 w hw`. Rewrite using `[hE]`. Conclude with `congrFun hH ⟨w, hw⟩`. Use function extensionality and compare the values at `z₀`.

Conclude with `hK hEv _ _ (toK L n) (toK_injective L n) _ hfinn k _ H.2.1 H.2.2 hvan z₀.1 (hs1 _ z₀.2)`. Take `⟨K, hK0, hKb⟩` from `lift_map_comp P Q hPQ`. Use `set i0 : ℝ := ((Gq (toK L n) (qel L n π hπ0)).index : ℝ) with hi0_def`. Use `⟨n + 1 + ⌈5 * (1 + K) * i0⌉₊, fun N hN F hFi hFc hdec z hz => ?_⟩` and prove the remaining obligations. Take `⟨r, rfl⟩ : ∃ r, N = n + r` from `⟨N - n, by omega⟩`.

Establish `hr : 1 ≤ r` using `by omega`. Establish `hfinN` using `hI L (n + r) π hπ`. Use `set iN : ℝ := ((Gq (toK L (n + r)) (qel L (n + r) π hπ0)).index : ℝ) with hiN_def`. Establish `hiN : ((n + r : ℕ) : ℝ) ≤ iN` using `Nat.cast_le.2 hfinN.2`. Establish `hi0 : 0 ≤ i0` using `Nat.cast_nonneg _`.

Establish `hceil : 5 * (1 + K) * i0 ≤ iN`. Establish `h1` using `Nat.le_ceil (5 * (1 + K) * i0)`. Establish `h2 : ((n + 1 + ⌈5 * (1 + K) * i0⌉₊ : ℕ) : ℝ) ≤ ((n + r : ℕ) : ℝ)` using `by exact_mod_cast hN`. Move the coercions through the operations in `at h2 hiN`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hiNpos : 0 < iN`. Establish `h1 : (1 : ℝ) ≤ ((n + r : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ n + r)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set a : ℝ := i0 / iN with ha`. Establish `ha0 : 0 ≤ a` using `div_nonneg hi0 hiNpos.le`.

Establish `haK : a * (1 + K) ≤ 1 / 5`. Rewrite using `[ha, div_mul_eq_mul_div, div_le_iff₀ hiNpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha15 : a ≤ 1 / 5` using `by nlinarith [mul_nonneg ha0 hK0]`. Use `set TN : ((Fin (k + 2) → GK L (n + r)) → ℝ) → ((Fin (k + 2) → GK L (n + r)) → ℝ) := hecke (toK L (n + r)) (MonoidHom.id (GK L (n + r))) (qel L (n + r) π hπ0) with hTN`.

Establish `hit : ∀ j, Inv (toK L (n + r)) (TN^[j] F) ∧ dC (TN^[j] F) = 0`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => exact ⟨hFi, hFc⟩`. Consider the case `succ j ih`.

Rewrite using `[Function.iterate_succ_apply']`. Take `⟨h1, h2, _⟩` from `hF _ _ (toK L (n + r)) _ hfinN.1 (k + 1) (TN^[j] F) 0 0 ih.1`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, ih.2, hecke_zero]`. Establish `hc` using `(hSK L π hπ0 n r hn1).1`.

Establish `hres : ∀ G : (Fin (k + 2) → GK L (n + r)) → ℝ, Inv (toK L (n + r)) G → dC G = 0 → resF L n r k G ∈ invCoc L n k`. Introduce `G hGi hGc`. Use `⟨fun g y => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hGi (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) g) (fun j => stab L n (n + r) (Nat.le_add_right n r) (y j))`. Rewrite `h1` using `[hc]`.

Simplify using `only [resF, smul_eq_mul, map_mul] at h1 ⊢`. Conclude with `h1`. Use function extensionality and compare the values at `y`. Establish `h1` using `congrFun hGc (fun j => stab L n (n + r) (Nat.le_add_right n r) (y j))`. Simplify `h1` using `[dC, resF]`.

Set `x : ℕ → (↥s → ℝ)` to `fun j z₀ => ev (toK L (n + r)) (TN^[j] F) 1 (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1) z₀.1)`. Establish `hstep : ∀ j, (4 / 5 : ℝ) * ‖x j‖ ≤ ‖x (j + 1)‖`. Introduce `j`. Establish `hy : ‖Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩‖ ≤ K * ‖x j‖`. Establish `hP : P ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩ = x j`.

Use function extensionality and compare the values at `fun z₀ => ev_resF_eq_ev_cmap_stab L n r k hc _ z₀.1`. Rewrite using `[← hP]`. Conclude with `hKb _`. Establish `hxy : (1 - a) • x j = x (j + 1) - a • Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩`. Use function extensionality and compare the values at `z₀`.

Establish `h1' : x (j + 1) z₀ = (1 - a) * x j z₀ + a * Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩ z₀`. Establish `h1` using `hKey hCh' hEv hAff L hL k hk π hπ n r hn1 hr (TN^[j] F) (hit j).1 (hit j).2 z₀.1 (hs1 _ z₀.2)`. Simplify using `only [x, Function.iterate_succ_apply']`. Conclude with `h1`. Simplify using `only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`.

Rewrite using `[h1']`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `norm_sub_le (x (j + 1)) (a • Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩)`. Rewrite `h1` using `[← hxy, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha0, abs_of_nonneg (by linarith)]`. Establish `h2` using `mul_le_mul_of_nonneg_left hy ha0`.

Establish `h3` using `mul_le_mul_of_nonneg_right haK (norm_nonneg (x j))`. Use polynomial arithmetic with `[norm_nonneg (x j)]`. Establish `hlow : ∀ j, (4 / 5 : ℝ) ^ j * ‖x 0‖ ≤ ‖x j‖`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[pow_succ]`. Use polynomial arithmetic with `[hstep j, ih]`. Establish `hdec' : ∀ z₀ : ↥s, ∃ C : ℝ, ∀ j, |x j z₀| ≤ C * (3 / 5) ^ j` using `fun z₀ => hdec _ (hcycmap _ _ (hs1 _ z₀.2))`.

Use `choose C hC using hdec'`. Establish `hup : ∀ j, ‖x j‖ ≤ (∑ z₀, |C z₀|) * (3 / 5) ^ j`. Introduce `j`. Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun z₀ => ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `Finset.single_le_sum (f := fun z => |C z|) (fun _ _ => abs_nonneg _) (Finset.mem_univ z₀)`. Establish `hx0 : ‖x 0‖ = 0` using `by set D := ∑ z₀, |C z₀|`. Establish `hb : ∀ j, ‖x 0‖ ≤ D * (3 / 4) ^ j`. Introduce `j`.

Establish `h1` using `(hlow j).trans (hup j)`. Establish `hp : (0 : ℝ) < (4 / 5) ^ j` using `by positivity`. Establish `h2 : (3 / 5 : ℝ) ^ j = (3 / 4) ^ j * (4 / 5) ^ j` using `by rw [← mul_pow]; norm_num`. Rewrite `h1` using `[h2]`. Establish `h3 : (4 / 5 : ℝ) ^ j * ‖x 0‖ ≤ (4 / 5) ^ j * (D * (3 / 4) ^ j)` using `by linarith`.

Conclude with `le_of_mul_le_mul_left h3 hp`. Establish `ht : Filter.Tendsto (fun j : ℕ => D * (3 / 4 : ℝ) ^ j) Filter.atTop (nhds 0)`. Simplify using `using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num)).const_mul D`. Conclude with `le_antisymm (ge_of_tendsto' ht hb) (norm_nonneg _)`. Establish `hx0' : ∀ z₀ ∈ s, ev (toK L (n + r)) F 1 (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1) z₀) = 0`.

Introduce `z₀ hz₀`. Conclude with `congrFun (norm_eq_zero.1 hx0) ⟨z₀, hz₀⟩`. Take `⟨E, hE⟩` from `exists_linearMap_eq_ev (toK L (n + r)) F (1 : GK L (n + r))`. Establish `hall` using `eq_zero_of_mem_all_maximalIdeal_pow (E.comp (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1))) s hs2 (fun w hw => by`. Rewrite using `[LinearMap.comp_apply, hE]`.

Conclude with `(hEv _ _ _ _ k F hFi hFc).1 1 _ (hbdmap _ w hw))`. Use the proof step `(fun w hw => by`. Rewrite using `[LinearMap.comp_apply, hE]`. Conclude with `hx0' w hw)`. Take `⟨z₀, hz₀, hb⟩` from `(hSt (𝓞 L) k n (n + r) (Nat.le_add_right n r) (le_refl _)).2 z hz`.

Establish `h1` using `(hEv _ _ _ _ k F hFi hFc).1 1 _ hb`. Establish `h2` using `hall z₀ hz₀`. Rewrite `h1` using `[← hE, map_sub]`. Rewrite `h2` using `[LinearMap.comp_apply]`. Rewrite using `[← hE]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem assemble (hCh : SChain) (hEv : SEv) (hSt : SStab) (hFin : SFin) (hAff : SAff) (hKey : PKey)
    (hF : PHeckeFormal) (hK : PHeckeKer) (hI : PIndex) (hSK : PStabK) : SHecke := by
  unfold SHecke
  intro L _ _ hL k hk π hπ
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hCh' := hCh
  obtain ⟨_, hcm, _, _⟩ := hCh
  have hbdmap : ∀ {G H : Type} [Group G] [Group H] (f : G →* H) (w : Chn G (k + 1)), IsBd w →
      IsBd (cmap f (k + 1) w) := by
    intro G H _ _ f w hw
    obtain ⟨v, rfl⟩ := hw
    exact ⟨cmap f (k + 2) v, hcm G H f (k + 1) v⟩
  have hcycmap : ∀ {G H : Type} [Group G] [Group H] (f : G →* H) (w : Chn G (k + 1)), IsCyc w →
      IsCyc (cmap f (k + 1) w) := by
    intro G H _ _ f w hw
    unfold IsCyc at *
    rw [hcm, hw, map_zero]
  set n := 2 * (k + 1) + 4 with hn_def
  have hn1 : 1 ≤ n := by omega
  obtain ⟨s, hs1, hs2⟩ := hFin L hL n k
  have hfinn := (hI L n π hπ).1
  let P : invCoc L n k →ₗ[ℝ] (↥s → ℝ) :=
    { toFun := fun H z₀ => ev (toK L n) (H : (Fin (k + 2) → GK L n) → ℝ) 1 z₀.1
      map_add' := fun H H' => by
        funext z₀
        simp only [Submodule.coe_add, ev_fadd1, Pi.add_apply]
      map_smul' := fun c H => by
        funext z₀
        simp only [Submodule.coe_smul, ev_fsmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  let Q : invCoc L n k →ₗ[ℝ] (↥s → ℝ) :=
    { toFun := fun H z₀ => ev (toK L n) (hecke (toK L n) (MonoidHom.id (GK L n)) (qel L n π hπ0)
        (H : (Fin (k + 2) → GK L n) → ℝ)) 1 z₀.1
      map_add' := fun H H' => by
        funext z₀
        have h1 := (hF _ _ (toK L n) _ hfinn (k + 1) H H' 1 H.2.1).2.2
        rw [one_smul, one_smul] at h1
        simp only [Submodule.coe_add, h1, ev_fadd1, Pi.add_apply]
      map_smul' := fun c H => by
        funext z₀
        have h1 := (hF _ _ (toK L n) _ hfinn (k + 1) 0 H c (fun _ _ => rfl)).2.2
        rw [zero_add, hecke_zero, zero_add] at h1
        simp only [Submodule.coe_smul, h1, ev_fsmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hPQ : ∀ H, P H = 0 → Q H = 0 := by
    intro H hH
    have hvan : ∀ z : Chn (Gm L n) (k + 1), IsCyc z → ev (toK L n) (H : (Fin (k + 2) → GK L n) → ℝ) 1 z = 0 := by
      obtain ⟨E, hE⟩ := exists_linearMap_eq_ev (toK L n) (H : (Fin (k + 2) → GK L n) → ℝ) (1 : GK L n)
      intro z hz
      rw [← hE]
      refine eq_zero_of_mem_all_maximalIdeal_pow E s hs2 (fun w hw => ?_) (fun w hw => ?_) z hz
      · rw [hE]
        exact (hEv _ _ _ (toK L n) k _ H.2.1 H.2.2).1 1 w hw
      · rw [hE]
        exact congrFun hH ⟨w, hw⟩
    funext z₀
    exact hK hEv _ _ (toK L n) (toK_injective L n) _ hfinn k _ H.2.1 H.2.2 hvan z₀.1 (hs1 _ z₀.2)
  obtain ⟨K, hK0, hKb⟩ := lift_map_comp P Q hPQ
  set i0 : ℝ := ((Gq (toK L n) (qel L n π hπ0)).index : ℝ) with hi0_def
  refine ⟨n + 1 + ⌈5 * (1 + K) * i0⌉₊, fun N hN F hFi hFc hdec z hz => ?_⟩
  obtain ⟨r, rfl⟩ : ∃ r, N = n + r := ⟨N - n, by omega⟩
  have hr : 1 ≤ r := by omega
  have hfinN := hI L (n + r) π hπ
  set iN : ℝ := ((Gq (toK L (n + r)) (qel L (n + r) π hπ0)).index : ℝ) with hiN_def
  have hiN : ((n + r : ℕ) : ℝ) ≤ iN := Nat.cast_le.2 hfinN.2
  have hi0 : 0 ≤ i0 := Nat.cast_nonneg _
  have hceil : 5 * (1 + K) * i0 ≤ iN := by
    have h1 := Nat.le_ceil (5 * (1 + K) * i0)
    have h2 : ((n + 1 + ⌈5 * (1 + K) * i0⌉₊ : ℕ) : ℝ) ≤ ((n + r : ℕ) : ℝ) := by exact_mod_cast hN
    push_cast at h2 hiN
    linarith
  have hiNpos : 0 < iN := by
    have h1 : (1 : ℝ) ≤ ((n + r : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + r)
    linarith
  set a : ℝ := i0 / iN with ha
  have ha0 : 0 ≤ a := div_nonneg hi0 hiNpos.le
  have haK : a * (1 + K) ≤ 1 / 5 := by
    rw [ha, div_mul_eq_mul_div, div_le_iff₀ hiNpos]
    linarith
  have ha15 : a ≤ 1 / 5 := by nlinarith [mul_nonneg ha0 hK0]
  set TN : ((Fin (k + 2) → GK L (n + r)) → ℝ) → ((Fin (k + 2) → GK L (n + r)) → ℝ) := hecke (toK L (n + r)) (MonoidHom.id (GK L (n + r))) (qel L (n + r) π hπ0) with hTN
  have hit : ∀ j, Inv (toK L (n + r)) (TN^[j] F) ∧ dC (TN^[j] F) = 0 := by
    intro j
    induction j with
    | zero => exact ⟨hFi, hFc⟩
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨h1, h2, _⟩ := hF _ _ (toK L (n + r)) _ hfinN.1 (k + 1) (TN^[j] F) 0 0 ih.1
      refine ⟨h1, ?_⟩
      rw [h2, ih.2, hecke_zero]
  have hc := (hSK L π hπ0 n r hn1).1
  have hres : ∀ G : (Fin (k + 2) → GK L (n + r)) → ℝ, Inv (toK L (n + r)) G → dC G = 0 →
      resF L n r k G ∈ invCoc L n k := by
    intro G hGi hGc
    refine ⟨fun g y => ?_, ?_⟩
    · have h1 := hGi (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) g)
        (fun j => stab L n (n + r) (Nat.le_add_right n r) (y j))
      rw [hc] at h1
      simp only [resF, smul_eq_mul, map_mul] at h1 ⊢
      exact h1
    · funext y
      have h1 := congrFun hGc (fun j => stab L n (n + r) (Nat.le_add_right n r) (y j))
      simpa [dC, resF] using h1
  let x : ℕ → (↥s → ℝ) := fun j z₀ => ev (toK L (n + r)) (TN^[j] F) 1
    (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1) z₀.1)
  have hstep : ∀ j, (4 / 5 : ℝ) * ‖x j‖ ≤ ‖x (j + 1)‖ := by
    intro j
    have hy : ‖Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩‖ ≤ K * ‖x j‖ := by
      have hP : P ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩ = x j :=
        funext fun z₀ => ev_resF_eq_ev_cmap_stab L n r k hc _ z₀.1
      rw [← hP]
      exact hKb _
    have hxy : (1 - a) • x j = x (j + 1) - a • Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩ := by
      funext z₀
      have h1' : x (j + 1) z₀ = (1 - a) * x j z₀ +
          a * Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩ z₀ := by
        have h1 := hKey hCh' hEv hAff L hL k hk π hπ n r hn1 hr (TN^[j] F) (hit j).1 (hit j).2 z₀.1
          (hs1 _ z₀.2)
        simp only [x, Function.iterate_succ_apply']
        exact h1
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [h1']
      ring
    have h1 := norm_sub_le (x (j + 1)) (a • Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩)
    rw [← hxy, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha0,
      abs_of_nonneg (by linarith)] at h1
    have h2 := mul_le_mul_of_nonneg_left hy ha0
    have h3 := mul_le_mul_of_nonneg_right haK (norm_nonneg (x j))
    nlinarith [norm_nonneg (x j)]
  have hlow : ∀ j, (4 / 5 : ℝ) ^ j * ‖x 0‖ ≤ ‖x j‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ]
      nlinarith [hstep j, ih]
  have hdec' : ∀ z₀ : ↥s, ∃ C : ℝ, ∀ j, |x j z₀| ≤ C * (3 / 5) ^ j :=
    fun z₀ => hdec _ (hcycmap _ _ (hs1 _ z₀.2))
  choose C hC using hdec'
  have hup : ∀ j, ‖x j‖ ≤ (∑ z₀, |C z₀|) * (3 / 5) ^ j := by
    intro j
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun z₀ => ?_
    rw [Real.norm_eq_abs]
    calc |x j z₀| ≤ C z₀ * (3 / 5) ^ j := hC z₀ j
      _ ≤ |C z₀| * (3 / 5) ^ j := by gcongr; exact le_abs_self _
      _ ≤ (∑ z₀, |C z₀|) * (3 / 5) ^ j := by
        gcongr
        exact Finset.single_le_sum (f := fun z => |C z|) (fun _ _ => abs_nonneg _) (Finset.mem_univ z₀)
  have hx0 : ‖x 0‖ = 0 := by
    set D := ∑ z₀, |C z₀|
    have hb : ∀ j, ‖x 0‖ ≤ D * (3 / 4) ^ j := by
      intro j
      have h1 := (hlow j).trans (hup j)
      have hp : (0 : ℝ) < (4 / 5) ^ j := by positivity
      have h2 : (3 / 5 : ℝ) ^ j = (3 / 4) ^ j * (4 / 5) ^ j := by rw [← mul_pow]; norm_num
      rw [h2] at h1
      have h3 : (4 / 5 : ℝ) ^ j * ‖x 0‖ ≤ (4 / 5) ^ j * (D * (3 / 4) ^ j) := by linarith
      exact le_of_mul_le_mul_left h3 hp
    have ht : Filter.Tendsto (fun j : ℕ => D * (3 / 4 : ℝ) ^ j) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by norm_num)).const_mul D
    exact le_antisymm (ge_of_tendsto' ht hb) (norm_nonneg _)
  have hx0' : ∀ z₀ ∈ s, ev (toK L (n + r)) F 1
      (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1) z₀) = 0 := by
    intro z₀ hz₀
    exact congrFun (norm_eq_zero.1 hx0) ⟨z₀, hz₀⟩
  obtain ⟨E, hE⟩ := exists_linearMap_eq_ev (toK L (n + r)) F (1 : GK L (n + r))
  have hall := eq_zero_of_mem_all_maximalIdeal_pow (E.comp (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1))) s hs2
    (fun w hw => by
      rw [LinearMap.comp_apply, hE]
      exact (hEv _ _ _ _ k F hFi hFc).1 1 _ (hbdmap _ w hw))
    (fun w hw => by
      rw [LinearMap.comp_apply, hE]
      exact hx0' w hw)
  obtain ⟨z₀, hz₀, hb⟩ := (hSt (𝓞 L) k n (n + r) (Nat.le_add_right n r) (le_refl _)).2 z hz
  have h1 := (hEv _ _ _ _ k F hFi hFc).1 1 _ hb
  have h2 := hall z₀ hz₀
  rw [← hE, map_sub] at h1
  rw [LinearMap.comp_apply] at h2
  rw [← hE]
  linarith

end PositivityTheory.KB.AffineStabilizerVanishing

end
