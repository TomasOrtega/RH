import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir

noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier.FiniteInversion

open GlobalTheory.CompanionTheory.TwistedAverage

section Abstract

variable {G V : Type} [CommGroup G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Use `choose M hMfin hMsum using hM`. Use `haveI : ∀ i, (M i).FiniteIndex := hMfin`. Use `haveI : (⨅ i, M i).FiniteIndex := Subgroup.finiteIndex_iInf hMfin`. Use `set N : Subgroup L := K ⊓ ⨅ i, M i with hNdef`. Use `haveI : N.Normal := Subgroup.normal_of_isMulCommutative N`.

Use `letI : Fintype (L ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex`. Establish `hNK : N ≤ K` using `inf_le_left`. Establish `hNM : ∀ i, N ≤ M i` using `fun i => inf_le_right.trans (iInf_le _ i)`. Establish `htot : ∑ q : L ⧸ N, (∑ i, (((θ i q.out)⁻¹ : ℂˣ) : ℂ)) • ρ (q.out : G) v = 0`. Repeatedly rewrite using `[Finset.sum_smul]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_eq_zero fun i _ => hMsum i N (hNM i)`. Establish `hterm : ∀ q : L ⧸ N, (∑ i, (((θ i q.out)⁻¹ : ℂˣ) : ℂ)) • ρ (q.out : G) v = if q.out ∈ K then (Fintype.card I : ℂ) • v else 0`. Introduce `q`. Use `split_ifs with h`.

Rewrite using `[h1 _ h, hK _ h]`. Rewrite using `[h0 _ h, zero_smul]`. Rewrite `htot` using `[Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]`. Use `(smul_eq_zero.mp htot).resolve_left (mul_ne_zero (Nat.cast_ne_zero.mpr ?_) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))` and prove the remaining obligations. Apply `Finset.card_ne_zero_of_mem (a := (QuotientGroup.mk 1 : L ⧸ N))` to reduce the goal to its premises.

Use `Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul N (1 : L)`. Rewrite using `[hh, one_mul]`. Conclude with `hNK h.2`.
-/
theorem eq_zero_of_orthogonal (ρ : Representation ℂ G V) (L : Subgroup G) {I : Type} [Fintype I]
    [Nonempty I] (θ : I → (L →* ℂˣ)) (K : Subgroup L) [K.FiniteIndex] {v : V}
    (hK : ∀ x ∈ K, ρ (x : G) v = v)
    (hM : ∀ i, ∃ M : Subgroup L, M.FiniteIndex ∧ ∀ (N : Subgroup L) [N.Normal] [Fintype (L ⧸ N)],
      N ≤ M → ∑ q : L ⧸ N, twOrbit ρ L (θ i) v q.out = 0)
    (h1 : ∀ x ∈ K, ∑ i, (((θ i x)⁻¹ : ℂˣ) : ℂ) = Fintype.card I)
    (h0 : ∀ x, x ∉ K → ∑ i, (((θ i x)⁻¹ : ℂˣ) : ℂ) = 0) : v = 0 := by
  classical
  choose M hMfin hMsum using hM
  haveI : ∀ i, (M i).FiniteIndex := hMfin
  haveI : (⨅ i, M i).FiniteIndex := Subgroup.finiteIndex_iInf hMfin
  set N : Subgroup L := K ⊓ ⨅ i, M i with hNdef
  haveI : N.Normal := Subgroup.normal_of_isMulCommutative N
  letI : Fintype (L ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
  have hNK : N ≤ K := inf_le_left
  have hNM : ∀ i, N ≤ M i := fun i => inf_le_right.trans (iInf_le _ i)
  have htot : ∑ q : L ⧸ N, (∑ i, (((θ i q.out)⁻¹ : ℂˣ) : ℂ)) • ρ (q.out : G) v = 0 := by
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ => hMsum i N (hNM i)
  have hterm : ∀ q : L ⧸ N, (∑ i, (((θ i q.out)⁻¹ : ℂˣ) : ℂ)) • ρ (q.out : G) v =
      if q.out ∈ K then (Fintype.card I : ℂ) • v else 0 := by
    intro q
    split_ifs with h
    · rw [h1 _ h, hK _ h]
    · rw [h0 _ h, zero_smul]
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul] at htot
  refine (smul_eq_zero.mp htot).resolve_left
    (mul_ne_zero (Nat.cast_ne_zero.mpr ?_) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  apply Finset.card_ne_zero_of_mem (a := (QuotientGroup.mk 1 : L ⧸ N))
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N (1 : L)
  rw [hh, one_mul]
  exact hNK h.2

end Abstract

section Box

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, Set.mem_preimage, Set.mem_univ_pi]`. Conclude with `Iff.rfl`.
-/
theorem coe_box_eq (n : ℕ) (N : ℤ) : (box k n N : Set (Multiplicative (Fin n → k))) =
    Multiplicative.toAdd ⁻¹' (Set.univ.pi fun _ : Fin n => (valBall k N : Set k)) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_univ_pi]
  exact Iff.rfl

/- English proof (translation)
Rewrite using `[coe_box_eq]`. Conclude with `isCompact_univ_pi fun _ => isCompact_valBall N`.
-/
theorem isCompact_box (n : ℕ) (N : ℤ) :
    IsCompact (box k n N : Set (Multiplicative (Fin n → k))) := by
  rw [coe_box_eq]
  exact isCompact_univ_pi fun _ => isCompact_valBall N

/- English proof (translation)
Rewrite using `[coe_box_eq]`. Conclude with `(isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valBall N).preimage continuous_toAdd`.
-/
theorem isOpen_box (n : ℕ) (N : ℤ) :
    IsOpen (box k n N : Set (Multiplicative (Fin n → k))) := by
  rw [coe_box_eq]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valBall N).preimage continuous_toAdd

/- English proof (translation)
Use `show ∑ i, a i * x i ∈ valBall k (m + p)`. Conclude with `AddSubgroup.sum_mem _ fun i _ => mul_mem_valBall (ha i) (hx i)`.
-/
theorem dotProduct_mem_valBall {n : ℕ} {m p : ℤ} {a x : Fin n → k} (ha : ∀ i, a i ∈ valBall k m)
    (hx : ∀ i, x i ∈ valBall k p) : a ⬝ᵥ x ∈ valBall k (m + p) := by
  show ∑ i, a i * x i ∈ valBall k (m + p)
  exact AddSubgroup.sum_mem _ fun i _ => mul_mem_valBall (ha i) (hx i)

variable {ψ : AddChar k Circle}

/- English proof (translation)
Establish `h1 : ψ (a ⬝ᵥ x.toAdd) = 1` using `isTrivialOn_addCharConductor hψ hψ1 _ h`. Simplify using `[chi, h1]`.
-/
theorem chi_eq_one (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {n : ℕ} {a : Fin n → k}
    {x : Multiplicative (Fin n → k)} (h : a ⬝ᵥ x.toAdd ∈ valBall k (addCharConductor ψ)) :
    chi k ψ a x = 1 := by
  have h1 : ψ (a ⬝ᵥ x.toAdd) = 1 := isTrivialOn_addCharConductor hψ hψ1 _ h
  simp [chi, h1]

/- English proof (translation)
Establish `hU : IsOpen {x : Multiplicative (Fin n → k) | a ⬝ᵥ x.toAdd ∈ valBall k (addCharConductor ψ)}` using `(isOpen_valBall _).preimage (continuous_const.dotProduct continuous_toAdd)`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_` and prove the remaining obligations. Establish `hmem : (Subtype.val ⁻¹' {x : Multiplicative (Fin n → k) | a ⬝ᵥ x.toAdd ∈ valBall k (addCharConductor ψ)} : Set L) ∈ nhds (1 : L)` using `(hU.preimage continuous_subtype_val).mem_nhds (by simp [zero_mem])`. Use `Filter.mem_of_superset hmem fun y hy => ?_` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, MonoidHom.mem_ker]`.

Conclude with `chi_eq_one hψ hψ1 hy`.
-/
theorem isOpen_ker_chiOn (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {n : ℕ} (a : Fin n → k)
    (L : Subgroup (Multiplicative (Fin n → k))) : IsOpen ((chiOn k ψ a L).ker : Set L) := by
  have hU : IsOpen {x : Multiplicative (Fin n → k) | a ⬝ᵥ x.toAdd ∈ valBall k (addCharConductor ψ)} :=
    (isOpen_valBall _).preimage (continuous_const.dotProduct continuous_toAdd)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hmem : (Subtype.val ⁻¹' {x : Multiplicative (Fin n → k) |
      a ⬝ᵥ x.toAdd ∈ valBall k (addCharConductor ψ)} : Set L) ∈ nhds (1 : L) :=
    (hU.preimage continuous_subtype_val).mem_nhds (by simp [zero_mem])
  refine Filter.mem_of_superset hmem fun y hy => ?_
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  exact chi_eq_one hψ hψ1 hy

variable (ψ)

def ev {n : ℕ} (x : Multiplicative (Fin n → k)) (a : Multiplicative (Fin n → k)) : ℂ :=
  (((chi k ψ a.toAdd x)⁻¹ : ℂˣ) : ℂ)

/- English proof (translation)
Simplify using `[ev, chi, add_dotProduct, AddChar.map_add_eq_mul, mul_inv]`. Conclude with `mul_comm _ _`.
-/
theorem ev_mul {n : ℕ} (x a b : Multiplicative (Fin n → k)) :
    ev ψ x (a * b) = ev ψ x a * ev ψ x b := by
  simp [ev, chi, add_dotProduct, AddChar.map_add_eq_mul, mul_inv]
  exact mul_comm _ _

/- English proof (translation)
Unfold `ev`. Rewrite using `[h, inv_one, Units.val_one]`.
-/
theorem ev_eq_one {n : ℕ} {x a : Multiplicative (Fin n → k)} (h : chi k ψ a.toAdd x = 1) :
    ev ψ x a = 1 := by
  unfold ev
  rw [h, inv_one, Units.val_one]

/- English proof (translation)
Establish `hf : ∀ s : S, ∀ t ∈ T.subgroupOf S, ev ψ x ((s * t : S) : Multiplicative (Fin n → k)) = ev ψ x (s : Multiplicative (Fin n → k))`. Introduce `s t ht`. Rewrite using `[Subgroup.coe_mul, ev_mul, ev_eq_one ψ (hT _ (Subgroup.mem_subgroupOf.mp ht)), mul_one]`. Use `haveI : (T.subgroupOf S).Normal := Subgroup.normal_of_isMulCommutative _`. Establish `key` using `sum_out_mul_right (T.subgroupOf S) (fun s : S => ev ψ x (s : Multiplicative (Fin n → k))) hf ⟨l, hl⟩`.

Simplify using `only [Subgroup.coe_mul, ev_mul] at key`. Rewrite `key` using `[← Finset.sum_mul]`. Establish `hl1 : ev ψ x l ≠ 1`. Introduce `h`. Apply `hne` to reduce the goal to its premises.

Unfold `ev at h`. Conclude with `inv_eq_one.mp (Units.val_eq_one.mp h)`. Establish `hz : (∑ q : S ⧸ T.subgroupOf S, ev ψ x (q.out : Multiplicative (Fin n → k))) * (ev ψ x l - 1) = 0`. Rewrite using `[mul_sub, mul_one, key, sub_self]`. Break down `mul_eq_zero.mp hz with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd (sub_eq_zero.mp h) hl1`.
-/
theorem sum_ev_eq_zero {n : ℕ} (S T : Subgroup (Multiplicative (Fin n → k)))
    [Fintype (S ⧸ T.subgroupOf S)] (x : Multiplicative (Fin n → k))
    (hT : ∀ t ∈ T, chi k ψ (Multiplicative.toAdd t) x = 1)
    {l : Multiplicative (Fin n → k)} (hl : l ∈ S) (hne : chi k ψ l.toAdd x ≠ 1) :
    ∑ q : S ⧸ T.subgroupOf S, ev ψ x (q.out : Multiplicative (Fin n → k)) = 0 := by
  classical
  have hf : ∀ s : S, ∀ t ∈ T.subgroupOf S,
      ev ψ x ((s * t : S) : Multiplicative (Fin n → k)) = ev ψ x (s : Multiplicative (Fin n → k)) := by
    intro s t ht
    rw [Subgroup.coe_mul, ev_mul, ev_eq_one ψ (hT _ (Subgroup.mem_subgroupOf.mp ht)), mul_one]
  haveI : (T.subgroupOf S).Normal := Subgroup.normal_of_isMulCommutative _
  have key := sum_out_mul_right (T.subgroupOf S)
    (fun s : S => ev ψ x (s : Multiplicative (Fin n → k))) hf ⟨l, hl⟩
  simp only [Subgroup.coe_mul, ev_mul] at key
  rw [← Finset.sum_mul] at key
  have hl1 : ev ψ x l ≠ 1 := by
    intro h
    apply hne
    unfold ev at h
    exact inv_eq_one.mp (Units.val_eq_one.mp h)
  have hz : (∑ q : S ⧸ T.subgroupOf S, ev ψ x (q.out : Multiplicative (Fin n → k))) *
      (ev ψ x l - 1) = 0 := by
    rw [mul_sub, mul_one, key, sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hl1

variable {ψ}

/- English proof (translation)
Establish `hx' : ∃ i, x.toAdd i ∉ valBall k N`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hx hcon`. Take `⟨i, hi⟩` from `hx'`.

Establish `hnt : ¬ IsTrivialOn (ψ.mulShift (x.toAdd i)) (addCharConductor ψ - N)`. Rewrite using `[isTrivialOn_mulShift_iff_mem hψ hψ1, sub_sub_cancel]`. Conclude with `hi`. Unfold `IsTrivialOn at hnt`. Use `push_neg at hnt`.

Take `⟨y, hy, hψy⟩` from `hnt`. Use `⟨Multiplicative.ofAdd (Pi.single i y : Fin n → k), ?_, ?_⟩` and prove the remaining obligations. Use `show ∀ j, (Multiplicative.toAdd (Multiplicative.ofAdd (Pi.single i y : Fin n → k))) j ∈ valBall k (addCharConductor ψ - N)`. Introduce `j`. Rewrite using `[toAdd_ofAdd]`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `hy`. Rewrite using `[Pi.single_eq_of_ne hj]`.

Conclude with `zero_mem _`. Introduce `hc`. Apply `hψy` to reduce the goal to its premises. Rewrite using `[AddChar.mulShift_apply, mul_comm]`. Establish `h2 : Circle.toUnits (ψ ((Pi.single i y : Fin n → k) ⬝ᵥ x.toAdd)) = 1`.

Simplify `hc` using `[chi]`. Rewrite `h2` using `[single_dotProduct]`. Establish `h3` using `congrArg (fun u : ℂˣ => (u : ℂ)) h2`. Simplify using `only [Circle.toUnits_apply, Units.val_mk0, Units.val_one] at h3`. Conclude with `Circle.ext h3`.
-/
theorem exists_chi_ne_one (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {n : ℕ} {N : ℤ}
    {x : Multiplicative (Fin n → k)} (hx : x ∉ box k n N) :
    ∃ l ∈ box k n (addCharConductor ψ - N), chi k ψ (Multiplicative.toAdd l) x ≠ 1 := by
  classical
  have hx' : ∃ i, x.toAdd i ∉ valBall k N := by
    by_contra hcon
    push_neg at hcon
    exact hx hcon
  obtain ⟨i, hi⟩ := hx'
  have hnt : ¬ IsTrivialOn (ψ.mulShift (x.toAdd i)) (addCharConductor ψ - N) := by
    rw [isTrivialOn_mulShift_iff_mem hψ hψ1, sub_sub_cancel]
    exact hi
  unfold IsTrivialOn at hnt
  push_neg at hnt
  obtain ⟨y, hy, hψy⟩ := hnt
  refine ⟨Multiplicative.ofAdd (Pi.single i y : Fin n → k), ?_, ?_⟩
  · show ∀ j, (Multiplicative.toAdd (Multiplicative.ofAdd (Pi.single i y : Fin n → k))) j ∈
      valBall k (addCharConductor ψ - N)
    intro j
    rw [toAdd_ofAdd]
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same]
      exact hy
    · rw [Pi.single_eq_of_ne hj]
      exact zero_mem _
  · intro hc
    apply hψy
    rw [AddChar.mulShift_apply, mul_comm]
    have h2 : Circle.toUnits (ψ ((Pi.single i y : Fin n → k) ⬝ᵥ x.toAdd)) = 1 := by
      simpa [chi] using hc
    rw [single_dotProduct] at h2
    have h3 := congrArg (fun u : ℂˣ => (u : ℂ)) h2
    simp only [Circle.toUnits_apply, Units.val_mk0, Units.val_one] at h3
    exact Circle.ext h3

end Box

/- English proof (translation)
Introduce `k _ _ _ _ ψ hψ hψ1 n V _ _ ρ hρ v N J hJN hfix htw`. Establish `hfin : ∀ (A B : Subgroup (Multiplicative (Fin n → k))), IsCompact (A : Set (Multiplicative (Fin n → k))) → IsOpen (B : Set (Multiplicative (Fin n → k))) → (B.subgroupOf A).FiniteIndex`. Introduce `A B hA hB`. Use `haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA`. Use `haveI : Finite (A ⧸ B.subgroupOf A) := Subgroup.quotient_finite_of_isOpen _ (by`.

Rewrite using `[Subgroup.coe_subgroupOf]`. Conclude with `hB.preimage continuous_subtype_val)`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`. Use `haveI : ((box k n N).subgroupOf (box k n J)).FiniteIndex := hfin _ _ (isCompact_box n J) (isOpen_box n N)`. Use `haveI : ((box k n (addCharConductor ψ - J)).subgroupOf (box k n (addCharConductor ψ - N))).FiniteIndex := hfin _ _ (isCompact_box n (addCharConductor ψ - N)) (isOpen_box n (addCharConductor ψ - J))`.

Use `letI : Fintype (box k n (addCharConductor ψ - N) ⧸ (box k n (addCharConductor ψ - J)).subgroupOf (box k n (addCharConductor ψ - N))) := Subgroup.fintypeQuotientOfFiniteIndex`. Use `eq_zero_of_orthogonal ρ (box k n J) (I := box k n (addCharConductor ψ - N) ⧸ (box k n (addCharConductor ψ - J)).subgroupOf (box k n (addCharConductor ψ - N))) (fun q => chiOn k ψ (q.out : Multiplicative (Fin n → k)).toAdd (box k n J)) ((box k n N).subgroupOf (box k n J)) ?_ ?_ ?_ …` and prove the remaining obligations. Introduce `x hx`. Conclude with `hfix x (Subgroup.mem_subgroupOf.mp hx)`. Introduce `q`.

Conclude with `exists_sum_eq_zero hρ (isCompact_box n J) _ (isOpen_ker_chiOn hψ hψ1 _ _) (htw _ (fun i => q.out.2 i))`. Introduce `x hx`. Establish `hxN : (x : Multiplicative (Fin n → k)) ∈ box k n N` using `Subgroup.mem_subgroupOf.mp hx`. Establish `hone : ∀ q : box k n (addCharConductor ψ - N) ⧸ (box k n (addCharConductor ψ - J)).subgroupOf (box k n (addCharConductor ψ - N)), (((chiOn k ψ (q.out : Multiplicative (Fin n → k)).toAdd (box k n J) x)⁻¹ : ℂˣ) : ℂ) = 1`. Introduce `q`.

Establish `hmem` using `dotProduct_mem_valBall (fun i => q.out.2 i) (fun i => hxN i)`. Rewrite `hmem` using `[sub_add_cancel]`. Establish `h` using `chi_eq_one hψ hψ1 hmem`. Use `show (((chi k ψ (q.out : Multiplicative (Fin n → k)).toAdd (x : Multiplicative (Fin n → k)))⁻¹ : ℂˣ) : ℂ) = 1`. Rewrite using `[h, inv_one, Units.val_one]`.

Rewrite using `[Finset.sum_congr rfl (fun q _ => hone q), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]`. Introduce `x hx`. Establish `hxN : (x : Multiplicative (Fin n → k)) ∉ box k n N` using `fun h => hx (Subgroup.mem_subgroupOf.mpr h)`. Take `⟨l, hl, hne⟩` from `exists_chi_ne_one hψ hψ1 hxN`. Establish `hT : ∀ t ∈ box k n (addCharConductor ψ - J), chi k ψ (Multiplicative.toAdd t) (x : Multiplicative (Fin n → k)) = 1`.

Introduce `t ht`. Establish `hmem` using `dotProduct_mem_valBall (fun i => ht i) (fun i => x.2 i)`. Rewrite `hmem` using `[sub_add_cancel]`. Conclude with `chi_eq_one hψ hψ1 hmem`. Conclude with `sum_ev_eq_zero ψ (box k n (addCharConductor ψ - N)) (box k n (addCharConductor ψ - J)) (x : Multiplicative (Fin n → k)) hT hl hne`.
-/
theorem fourier_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V), IsSmooth ρ → ∀ (v : V) (N J : ℤ), J ≤ N → (∀ x ∈ box k n N, ρ x v = v) → (∀ a : Fin n → k, (∀ i, a i ∈ valBall k (addCharConductor ψ - N)) → v ∈ twKer ρ (box k n J) (chiOn k ψ a (box k n J))) → v = 0 := by
  intro k _ _ _ _ ψ hψ hψ1 n V _ _ ρ hρ v N J hJN hfix htw
  classical
  have hfin : ∀ (A B : Subgroup (Multiplicative (Fin n → k))), IsCompact (A : Set (Multiplicative (Fin n → k))) →
      IsOpen (B : Set (Multiplicative (Fin n → k))) → (B.subgroupOf A).FiniteIndex := by
    intro A B hA hB
    haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
    haveI : Finite (A ⧸ B.subgroupOf A) := Subgroup.quotient_finite_of_isOpen _ (by
      rw [Subgroup.coe_subgroupOf]
      exact hB.preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  haveI : ((box k n N).subgroupOf (box k n J)).FiniteIndex :=
    hfin _ _ (isCompact_box n J) (isOpen_box n N)
  haveI : ((box k n (addCharConductor ψ - J)).subgroupOf
      (box k n (addCharConductor ψ - N))).FiniteIndex :=
    hfin _ _ (isCompact_box n (addCharConductor ψ - N)) (isOpen_box n (addCharConductor ψ - J))
  letI : Fintype (box k n (addCharConductor ψ - N) ⧸
      (box k n (addCharConductor ψ - J)).subgroupOf (box k n (addCharConductor ψ - N))) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  refine eq_zero_of_orthogonal ρ (box k n J)
    (I := box k n (addCharConductor ψ - N) ⧸
      (box k n (addCharConductor ψ - J)).subgroupOf (box k n (addCharConductor ψ - N)))
    (fun q => chiOn k ψ (q.out : Multiplicative (Fin n → k)).toAdd (box k n J))
    ((box k n N).subgroupOf (box k n J)) ?_ ?_ ?_ ?_
  · intro x hx
    exact hfix x (Subgroup.mem_subgroupOf.mp hx)
  · intro q
    exact exists_sum_eq_zero hρ (isCompact_box n J) _ (isOpen_ker_chiOn hψ hψ1 _ _)
      (htw _ (fun i => q.out.2 i))
  · intro x hx
    have hxN : (x : Multiplicative (Fin n → k)) ∈ box k n N := Subgroup.mem_subgroupOf.mp hx
    have hone : ∀ q : box k n (addCharConductor ψ - N) ⧸
        (box k n (addCharConductor ψ - J)).subgroupOf (box k n (addCharConductor ψ - N)),
        (((chiOn k ψ (q.out : Multiplicative (Fin n → k)).toAdd (box k n J) x)⁻¹ : ℂˣ) : ℂ) = 1 := by
      intro q
      have hmem := dotProduct_mem_valBall (fun i => q.out.2 i) (fun i => hxN i)
      rw [sub_add_cancel] at hmem
      have h := chi_eq_one hψ hψ1 hmem
      show (((chi k ψ (q.out : Multiplicative (Fin n → k)).toAdd (x : Multiplicative (Fin n → k)))⁻¹ :
        ℂˣ) : ℂ) = 1
      rw [h, inv_one, Units.val_one]
    rw [Finset.sum_congr rfl (fun q _ => hone q), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
  · intro x hx
    have hxN : (x : Multiplicative (Fin n → k)) ∉ box k n N :=
      fun h => hx (Subgroup.mem_subgroupOf.mpr h)
    obtain ⟨l, hl, hne⟩ := exists_chi_ne_one hψ hψ1 hxN
    have hT : ∀ t ∈ box k n (addCharConductor ψ - J),
        chi k ψ (Multiplicative.toAdd t) (x : Multiplicative (Fin n → k)) = 1 := by
      intro t ht
      have hmem := dotProduct_mem_valBall (fun i => ht i) (fun i => x.2 i)
      rw [sub_add_cancel] at hmem
      exact chi_eq_one hψ hψ1 hmem
    exact sum_ev_eq_zero ψ (box k n (addCharConductor ψ - N)) (box k n (addCharConductor ψ - J))
      (x : Multiplicative (Fin n → k)) hT hl hne

end GlobalTheory.CompanionTheory.MirFourier.FiniteInversion

end
