import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestrictedWeightFirstTwoEq
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Imports

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model (Nv)

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis`. Set `_ : Algebra (WF p n') O` to `algOfIdent j φ`. Introduce `FsB hFsB Θ hΘ`. Establish `hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r` using `H.2.2.2.2.2.2.2.1`. Establish `hr2 : 2 ≤ r` using `H.2.1`.

Establish `hm2 : 2 ≤ m` using `by omega`. Establish `hdom : IsDominant lam0` using `H.2.2.2.2.1.2.1`. Establish `hwirr : Irreducible w` using `hSet.2.1`. Use `set ν : Fin n' → Fin (m + 1) → ℕ := fun s => nuOf (lamAt (restW TT lam0) s) with hν`. Use `set top : Fin n' → Bool := fun s => decide (s ∈ TT) with htop`.

Set `I` to `∀ s : Fin n', Xs m (top s) (vecE n' s) (ν s)`. Establish `: Finite I` using `Pi.finite`. Set `_ : Fintype I` to `Fintype.ofFinite I`. Set `eI : I ≃ Fin (Nat.card I)` to `Finite.equivFin I`. Establish `hbas` using `fun s => sSBasis O (m + 1) (m + 1) (ν s)`.

Use `choose b hb1 hb2 using hbas`. Set `bX : ∀ s, Xs m (top s) (vecE n' s) (ν s) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) O` to `fun s y => b s ⟨y.1, y.2.1⟩`. Set `sO : I → MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) O` to `fun i => ∏ s, blockEmb O s (bX s (i s))`. Establish `hsO : ∀ i, sO i ∈ tensorLat O O (fun s => dualWeyl O (m + 1) (m + 1) (nuOf (lamAt (restW TT lam0) s)))`. Introduce `i`.

Use `Submodule.subset_span ⟨fun s => bX s (i s), fun s => ?_, rfl⟩` and prove the remaining obligations. Use `show bX s (i s) ∈ dualWeyl O (m + 1) (m + 1) (ν s)`. Rewrite using `[← (hb1 s).2.1]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Take `⟨sh', hsh, hmain⟩` from `hTr p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r hm2 (by omega) (by omega) (dT TT lam0) (restW TT lam0) lam0 (lambda_zero_eq_product TT lam0) (restW_dom (by omega) TT lam0 hdom) e he hm g hhm hg hbasis Θ hΘ I sO hsO`.

Use `⟨Nat.card I, fun i => sh' (eI.symm i), fun i => hsh _, card_all hm2 TT lam0 hdom, ?_⟩` and prove the remaining obligations. Introduce `S hS c hcu hmem`. Take `⟨x0, hx0⟩` from `hcu`. Take `⟨SPO, hSPO1, hSPO2⟩` from `hSP p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ hrk F hF g hg (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x)`. Set `P : I → ↥((Pol (KK O) (ι` to `Fin n') (m + 1) (dT TT lam0)).restrictScalars O) := fun i => ∑ bb, c (bb, eI i) • FsB bb`.

Set `T0 : I → RRing O n' (r + K)` to `fun i => ∑ bb, c (bb, eI i) • B bb`. Set `Q : I → MvPolynomial (Fin n' × Fin (m + 1)) O` to `fun i => rename (castV hk) (T0 i) * SPO`. Establish `hPQ : ∀ i, subst p n' O w n' r g (P i : MvPolynomial (TV n' (m + 1)) (KK O)) = map (algebraMap O (KK O)) (Q i)`. Introduce `i`. Establish `e1 : ((P i : ↥((Pol (KK O) (ι` using `Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) : MvPolynomial (TV n' (m + 1)) (KK O)) = ∑ bb, algebraMap O (KK O) (c (bb, eI i)) • (FsB bb : MvPolynomial (TV n' (m + 1)) (KK O)) := by`.

Simplify using `only [P, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]`. Rewrite using `[e1, map_sum]`. Simplify using `only [map_smul, hFsB, symB, toK, Q, T0, map_mul, map_sum, ← hSPO1, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun bb _ => ?_` and prove the remaining obligations. Simplify using `only [MvPolynomial.smul_eq_C_mul, map_mul, map_C, mul_assoc]`.

Establish `hv : (((∑ y, c y • S y : Vsp Kf lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = ∑ i, ((Θ (P i) : Vsp Kf (flW (m` using `m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * ((sh' i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by`. Establish `e2 : ∀ i, ((Θ (P i) : Vsp Kf (flW (m` using `m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = ∑ bb, c (bb, eI i) • ((Θ (FsB bb) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by`. Introduce `i`. Simplify using `only [P, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul_of_tower]`. Simplify using `only [e2, Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_mul]`.

Rewrite using `[Fintype.sum_prod_type, Finset.sum_comm, ← Equiv.sum_comp eI]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun bb _ => ?_` and prove the remaining obligations. Rewrite using `[hS bb (eI i)]`. Simplify using `only [Equiv.symm_apply_apply, smul_mul_assoc]`. Take `⟨R, hR⟩` from `hmain P Q hPQ _ hv hmem`.

Set `Fr` to `IsLocalRing.ResidueField O`. Set `res : O →+* Fr` to `IsLocalRing.residue O`. Establish `hresw : res w = 0`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hwirr.not_isUnit`.

Establish `h0 : ∑ i ∈ (Finset.univ : Finset I), thAll Fr n' m (vecE n') (map res (Q i)) * ∏ s, blockEmb Fr s (map res (bX s (i s))) = 0`. Establish `h1` using `congrArg (map res) hR`. Simplify using `only [map_sum, map_mul, map_thAll, map_C, hresw, C_0, zero_mul, sO, map_prod, blockEmb, map_rename] at h1`. Simplify `h1` using `only [blockEmb]`. Establish `hQhom : ∀ i, IsMultiHom (dT TT lam0) (map res (Q i))`.

Introduce `i ee hee s`. Establish `h1 : ee ∈ (Q i).support` using `support_map_subset res (Q i) hee`. Establish `h2 : ee ∈ (map (algebraMap O (KK O)) (Q i)).support`. Rewrite using `[support_map_of_injective _ (IsFractionRing.injective O (KK O))]`. Conclude with `h1`.

Rewrite `h2` using `[← hPQ i]`. Establish `h3` using `hSub p n' W Qq O Kf ι σ j w hSet.1 φ hφ (m + 1) r (dT TT lam0) g hg _ (P i).2`. Conclude with `(Formalism.L2.G.Model.mem_Pol.1 h3) ee h2 s`. Establish `hQ0` using `bigInd Fr n' m hm2 top (vecE n') (dT TT lam0) ν (fun s hs => by`. Establish `: s ∉ TT` using `by simpa [htop] using hs`.

Simplify using `[dT, this])`. Use the proof step `(fun s hs hv t ht => nu_odd (by omega) TT lam0 hdom s (by simpa [htop] using hs) hv t ht)`. Use the proof step `(fun s y => map res (bX s y))`. Use the proof step `(fun s y => by`. Take `⟨d1, d2, -⟩` from `hb2 s ⟨y.1, y.2.1⟩`.

Use `deg_map (colLex (m + 1) (m + 1)) res (bX s y) d2` as an intermediate fact. Conclude with `⟨this.1.trans d1, this.2⟩)`. Use the proof step `Finset.univ (fun i => map res (Q i)) hQhom h0`. Establish `hq` using `hQ0 (eI.symm x0.2) (Finset.mem_univ _)`. Simplify using `only [Q, map_mul] at hq`.

Establish `hT : map res (rename (castV hk) (T0 (eI.symm x0.2))) = 0`. Break down `mul_eq_zero.1 hq with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd h1 hSPO2`. Rewrite `hT` using `[map_rename]`.

Establish `hinj : Function.Injective (castV (n'` using `n') hk) := by`. Introduce `u v huv`. Simplify using `only [castV, Prod.mk.injEq] at huv`. Conclude with `Prod.ext huv.1 (Fin.cast_injective _ huv.2)`. Establish `hT' : map res (T0 (eI.symm x0.2)) = 0`.

Apply `rename_injective _ hinj` to reduce the goal to its premises. Rewrite using `[hT, map_zero]`. Establish `hdvd : MvPolynomial.C w ∣ T0 (eI.symm x0.2)`. Rewrite using `[C_dvd_iff_dvd_coeff]`. Introduce `ee`.

Establish `h1 : res (coeff ee (T0 (eI.symm x0.2))) = 0`. Rewrite using `[← coeff_map, hT', coeff_zero]`. Rewrite `h1` using `[IsLocalRing.residue_eq_zero_iff, hwirr.maximalIdeal_eq, Ideal.mem_span_singleton]`. Conclude with `h1`. Take `⟨y, hy⟩` from `hdvd`.

Take `⟨T, hTc⟩` from `hc`. Establish `hfin` using `dvd_of_compl B hli T hTc w (fun bb => c (bb, x0.2)) y (by`. Establish `: T0 (eI.symm x0.2) = ∑ bb, c (bb, x0.2) • B bb`. Simplify using `only [T0, Equiv.apply_symm_apply]`. Rewrite using `[← this, hy, MvPolynomial.smul_eq_C_mul]) x0.1`.

Conclude with `hwirr.not_isUnit (isUnit_of_dvd_unit hfin hx0)`.
-/
theorem primStep_of (hTr : TransStep) (hSub : SubstPol) (C CLa : ℝ) (hSP : SPStep C) : PrimStep C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  have hm2 : 2 ≤ m := by omega
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  have hwirr : Irreducible w := hSet.2.1
  set ν : Fin n' → Fin (m + 1) → ℕ := fun s => nuOf (lamAt (restW TT lam0) s) with hν
  set top : Fin n' → Bool := fun s => decide (s ∈ TT) with htop
  let I := ∀ s : Fin n', Xs m (top s) (vecE n' s) (ν s)
  have : Finite I := Pi.finite
  let _ : Fintype I := Fintype.ofFinite I
  let eI : I ≃ Fin (Nat.card I) := Finite.equivFin I
  have hbas := fun s => sSBasis O (m + 1) (m + 1) (ν s)
  choose b hb1 hb2 using hbas
  let bX : ∀ s, Xs m (top s) (vecE n' s) (ν s) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) O :=
    fun s y => b s ⟨y.1, y.2.1⟩
  let sO : I → MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) O := fun i => ∏ s, blockEmb O s (bX s (i s))
  have hsO : ∀ i, sO i ∈ tensorLat O O (fun s => dualWeyl O (m + 1) (m + 1) (nuOf (lamAt (restW TT lam0) s))) := by
    intro i
    refine Submodule.subset_span ⟨fun s => bX s (i s), fun s => ?_, rfl⟩
    show bX s (i s) ∈ dualWeyl O (m + 1) (m + 1) (ν s)
    rw [← (hb1 s).2.1]
    exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨sh', hsh, hmain⟩ := hTr p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r hm2 (by omega) (by omega) (dT TT lam0)
    (restW TT lam0) lam0 (lambda_zero_eq_product TT lam0) (restW_dom (by omega) TT lam0 hdom) e he hm g hhm hg hbasis Θ hΘ I sO hsO
  refine ⟨Nat.card I, fun i => sh' (eI.symm i), fun i => hsh _, card_all hm2 TT lam0 hdom, ?_⟩
  intro S hS c hcu hmem
  obtain ⟨x0, hx0⟩ := hcu
  obtain ⟨SPO, hSPO1, hSPO2⟩ := hSP p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    hrk F hF g hg (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x)
  let P : I → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) :=
    fun i => ∑ bb, c (bb, eI i) • FsB bb
  let T0 : I → RRing O n' (r + K) := fun i => ∑ bb, c (bb, eI i) • B bb
  let Q : I → MvPolynomial (Fin n' × Fin (m + 1)) O := fun i => rename (castV hk) (T0 i) * SPO
  have hPQ : ∀ i, subst p n' O w n' r g (P i : MvPolynomial (TV n' (m + 1)) (KK O)) =
      map (algebraMap O (KK O)) (Q i) := by
    intro i
    have e1 : ((P i : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) :
        MvPolynomial (TV n' (m + 1)) (KK O)) =
        ∑ bb, algebraMap O (KK O) (c (bb, eI i)) • (FsB bb : MvPolynomial (TV n' (m + 1)) (KK O)) := by
      simp only [P, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
    rw [e1, map_sum]
    simp only [map_smul, hFsB, symB, toK, Q, T0, map_mul, map_sum, ← hSPO1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun bb _ => ?_
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_C, mul_assoc]
  have hv : (((∑ y, c y • S y : Vsp Kf lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      ∑ i, ((Θ (P i) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
        ((sh' i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
    have e2 : ∀ i, ((Θ (P i) : Vsp Kf (flW (m := m) (dT TT lam0))) :
        MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        ∑ bb, c (bb, eI i) • ((Θ (FsB bb) : Vsp Kf (flW (m := m) (dT TT lam0))) :
          MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
      intro i
      simp only [P, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul_of_tower]
    simp only [e2, Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_mul]
    rw [Fintype.sum_prod_type, Finset.sum_comm, ← Equiv.sum_comp eI]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun bb _ => ?_
    rw [hS bb (eI i)]
    simp only [Equiv.symm_apply_apply, smul_mul_assoc]
  obtain ⟨R, hR⟩ := hmain P Q hPQ _ hv hmem

  let Fr := IsLocalRing.ResidueField O
  let res : O →+* Fr := IsLocalRing.residue O
  have hresw : res w = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hwirr.not_isUnit
  have h0 : ∑ i ∈ (Finset.univ : Finset I), thAll Fr n' m (vecE n') (map res (Q i)) *
      ∏ s, blockEmb Fr s (map res (bX s (i s))) = 0 := by
    have h1 := congrArg (map res) hR
    simp only [map_sum, map_mul, map_thAll, map_C, hresw, C_0, zero_mul, sO, map_prod, blockEmb, map_rename] at h1
    simpa only [blockEmb] using h1
  have hQhom : ∀ i, IsMultiHom (dT TT lam0) (map res (Q i)) := by
    intro i ee hee s
    have h1 : ee ∈ (Q i).support := support_map_subset res (Q i) hee
    have h2 : ee ∈ (map (algebraMap O (KK O)) (Q i)).support := by
      rw [support_map_of_injective _ (IsFractionRing.injective O (KK O))]
      exact h1
    rw [← hPQ i] at h2
    have h3 := hSub p n' W Qq O Kf ι σ j w hSet.1 φ hφ (m + 1) r (dT TT lam0) g hg _ (P i).2
    exact (Formalism.L2.G.Model.mem_Pol.1 h3) ee h2 s
  have hQ0 := bigInd Fr n' m hm2 top (vecE n') (dT TT lam0) ν
    (fun s hs => by
      have : s ∉ TT := by simpa [htop] using hs
      simp [dT, this])
    (fun s hs hv t ht => nu_odd (by omega) TT lam0 hdom s (by simpa [htop] using hs) hv t ht)
    (fun s y => map res (bX s y))
    (fun s y => by
      obtain ⟨d1, d2, -⟩ := hb2 s ⟨y.1, y.2.1⟩
      have := deg_map (colLex (m + 1) (m + 1)) res (bX s y) d2
      exact ⟨this.1.trans d1, this.2⟩)
    Finset.univ (fun i => map res (Q i)) hQhom h0
  have hq := hQ0 (eI.symm x0.2) (Finset.mem_univ _)
  simp only [Q, map_mul] at hq
  have hT : map res (rename (castV hk) (T0 (eI.symm x0.2))) = 0 := by
    rcases mul_eq_zero.1 hq with h1 | h1
    · exact h1
    · exact absurd h1 hSPO2
  rw [map_rename] at hT
  have hinj : Function.Injective (castV (n' := n') hk) := by
    intro u v huv
    simp only [castV, Prod.mk.injEq] at huv
    exact Prod.ext huv.1 (Fin.cast_injective _ huv.2)
  have hT' : map res (T0 (eI.symm x0.2)) = 0 := by
    apply rename_injective _ hinj
    rw [hT, map_zero]
  have hdvd : MvPolynomial.C w ∣ T0 (eI.symm x0.2) := by
    rw [C_dvd_iff_dvd_coeff]
    intro ee
    have h1 : res (coeff ee (T0 (eI.symm x0.2))) = 0 := by
      rw [← coeff_map, hT', coeff_zero]
    rw [IsLocalRing.residue_eq_zero_iff, hwirr.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
    exact h1
  obtain ⟨y, hy⟩ := hdvd
  obtain ⟨T, hTc⟩ := hc
  have hfin := dvd_of_compl B hli T hTc w (fun bb => c (bb, x0.2)) y (by
    have : T0 (eI.symm x0.2) = ∑ bb, c (bb, x0.2) • B bb := by
      simp only [T0, Equiv.apply_symm_apply]
    rw [← this, hy, MvPolynomial.smul_eq_C_mul]) x0.1
  exact hwirr.not_isUnit (isUnit_of_dvd_unit hfin hx0)

/- English proof (translation)
Introduce `_` and use `⟨C₀, hC0, fun C hC => primStep_of hTr hSub C CLa (hSP C hC)⟩`.
-/
theorem source_integrality_of_substitution (hTr : TransStep) (hSub : SubstPol) (C₀ : ℝ) (hC0 : 0 < C₀) (hSP : ∀ C, C₀ ≤ C → SPStep C)
    (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : SourcePrimitiveIntegrality D CLa Ck Crk Cdeg :=
  fun _ => ⟨C₀, hC0, fun C hC => primStep_of hTr hSub C CLa (hSP C hC)⟩

end Formalism.MainNotions.TestSideCounting
