import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarEquivalenceGeneral.ScalarFactorEqOneOfLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.XLeOrthXplus

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.RowForm.ClassFramePositivePartDecomposition

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

section Basic

variable {r : ℕ} {T : E}

/- English proof (translation)
The claim follows from `PI.ScalarPairDr.W.hT_swap (S := S) x y`.
-/
theorem hswap (x y : S.V) : S.hT y x = star (S.hT x y) := PI.ScalarPairDr.W.hT_swap (S := S) x y

/- English proof (translation)
The claim follows from `((PI.ScalarPairDr.W.mem_orth_Xplus (S := S) F).1 (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F hx)).1 a`.
-/
theorem e_X (F : FlagG S r T) (a : Fin r) {x : S.V} (hx : x ∈ F.X) : S.hT (F.e a) x = 0 :=
  ((PI.ScalarPairDr.W.mem_orth_Xplus (S := S) F).1 (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F hx)).1 a

/- English proof (translation)
The claim follows from `((PI.ScalarPairDr.W.mem_orth_Xplus (S := S) F).1 (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F hx)).2`.
-/
theorem z_X (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : S.hT F.z x = 0 :=
  ((PI.ScalarPairDr.W.mem_orth_Xplus (S := S) F).1 (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F hx)).2

/- English proof (translation)
Express the relevant statement in the definitionally equal form `v ∈ F.X ⊔ Submodule.span E {F.z} at hv`. Take `⟨x, hx, w, hw, rfl⟩` from `Submodule.mem_sup.mp hv`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.mp hw`. Conclude with `⟨a, x, hx, by abel⟩`.
-/
theorem xplus_dec (F : FlagG S r T) {v : S.V} (hv : v ∈ F.Xplus) : ∃ a : E, ∃ x ∈ F.X, v = a • F.z + x := by
  change v ∈ F.X ⊔ Submodule.span E {F.z} at hv
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  exact ⟨a, x, hx, by abel⟩

/- English proof (translation)
The claim follows from `Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))) (Submodule.mem_sup_left hx)`.
-/
theorem xplus_mem (F : FlagG S r T) (a : E) {x : S.V} (hx : x ∈ F.X) : a • F.z + x ∈ F.Xplus :=
  Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
    (Submodule.mem_sup_left hx)

/- English proof (translation)
Rewrite using `[F.z_norm]`. Conclude with `neg_ne_zero.mpr hT`.
-/
theorem zz_ne (F : FlagG S r T) (hT : T ≠ 0) : S.hT F.z F.z ≠ 0 := by
  rw [F.z_norm]; exact neg_ne_zero.mpr hT

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.BetaLUniq.GN.coeffs_zero F F' C C' 0 h.symm (fun _ => by simp) (fun _ => by simp) hG`.
-/
theorem indep {T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) (C C' : Fin (r + 1) → E)
    (h : ∑ a, C a • F.fvec a + ∑ b, C' b • F'.fvec b = 0) : C = 0 ∧ C' = 0 :=
  PI.UnitaryGroupMassFormula.BetaLUniq.GN.coeffs_zero F F' C C' 0 h.symm (fun _ => by simp) (fun _ => by simp) hG

/- English proof (translation)
Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last]`. Normalize the expressions using the abelian group laws.
-/
theorem sum_fvec (F : FlagG S r T) (c : Fin r → E) (a : E) :
    ∑ i, (Fin.snoc (α := fun _ => E) c a : Fin (r + 1) → E) i • F.fvec i = a • F.z + ∑ i, c i • F.e i := by
  rw [Fin.sum_univ_castSucc]
  simp only [FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last]
  abel

/- English proof (translation)
The claim follows from `(Submodule.mem_span_range_iff_exists_fun E).1 hx`.
-/
theorem x_sum (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : ∃ c : Fin r → E, ∑ i, c i • F.e i = x :=
  (Submodule.mem_span_range_iff_exists_fun E).1 hx

/- English proof (translation)
Take `⟨c, hc⟩` from `x_sum F hv`. Take `⟨a', x', hx', e'⟩` from `xplus_dec F' hv'`. Take `⟨c', hc'⟩` from `x_sum F' hx'`. Establish `h` using `indep F F' hG (Fin.snoc (α := fun _ => E) c 0) (Fin.snoc (α := fun _ => E) (-c') (-a')) (by`. Rewrite using `[sum_fvec, sum_fvec]`.

Simplify using `only [zero_smul, zero_add, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]`. Rewrite using `[hc, hc', e']`. Use the proof step `abel)`. Establish `ha : a' = 0`. Use `congrFun h.2 (Fin.last r)` as an intermediate fact.

Simplify using `using this`. Establish `hc0 : c' = 0`. Use function extensionality and compare the values at `i`. Use `congrFun h.2 (Fin.castSucc i)` as an intermediate fact. Simplify using `using this`.

Rewrite using `[e', ← hc', ha, hc0]`. Simplify using the standard rewrite rules.
-/
theorem disj {T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) {v : S.V} (hv : v ∈ F.X)
    (hv' : v ∈ F'.Xplus) : v = 0 := by
  obtain ⟨c, hc⟩ := x_sum F hv
  obtain ⟨a', x', hx', e'⟩ := xplus_dec F' hv'
  obtain ⟨c', hc'⟩ := x_sum F' hx'
  have h := indep F F' hG (Fin.snoc (α := fun _ => E) c 0) (Fin.snoc (α := fun _ => E) (-c') (-a')) (by
    rw [sum_fvec, sum_fvec]
    simp only [zero_smul, zero_add, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    rw [hc, hc', e']; abel)
  have ha : a' = 0 := by
    have := congrFun h.2 (Fin.last r)
    simpa using this
  have hc0 : c' = 0 := by
    funext i
    have := congrFun h.2 (Fin.castSucc i)
    simpa using this
  rw [e', ← hc', ha, hc0]
  simp

/- English proof (translation)
The claim follows from `(indep F F' hG 0 C' (by simp [h])).2`.
-/
theorem indep' {T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) (C' : Fin (r + 1) → E)
    (h : ∑ b, C' b • F'.fvec b = 0) : C' = 0 :=
  (indep F F' hG 0 C' (by simp [h])).2

end Basic

section Pair

variable {Λ : Submodule (𝓞 E) S.V} {r : ℕ} {T T' : E} {F : LFlag S r T} {F' F'' : LFlag S r T'}
  {β : S.V ≃ₗ[E] S.V}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Apply `Submodule.subset_span show F.zt ∈ UU Λ F F'` to reduce the goal to its premises. Unfold `UU`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))`. Apply `Submodule.subset_span show F'.zt ∈ UU Λ F F'` to reduce the goal to its premises.

Unfold `UU`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`.
-/
theorem zt_mem (F : LFlag S r T) (F' : LFlag S r T') : F.zt ∈ UUE Λ F F' ∧ F'.zt ∈ UUE Λ F F' := by
  constructor
  · apply Submodule.subset_span
    show F.zt ∈ UU Λ F F'
    unfold UU
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  · apply Submodule.subset_span
    show F'.zt ∈ UU Λ F F'
    unfold UU
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `F.fl.X ⊔ Submodule.span E {F.fl.z} ≤ _`. Use `sup_le (PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE S Λ hΛ F F') ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff, ← hz]`. Conclude with `(zt_mem (Λ := Λ) F F').1`.
-/
theorem xplus_le (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T') (hz : F.zt = F.fl.z) :
    Xplus F ≤ UUE Λ F F' := by
  change F.fl.X ⊔ Submodule.span E {F.fl.z} ≤ _
  refine sup_le (PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE S Λ hΛ F F') ?_
  rw [Submodule.span_le, Set.singleton_subset_iff, ← hz]
  exact (zt_mem (Λ := Λ) F F').1

/- English proof (translation)
Express the relevant statement in the definitionally equal form `F'.fl.X ⊔ Submodule.span E {F'.fl.z} ≤ _`. Use `sup_le (PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE' S Λ hΛ F F') ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff, ← hz']`. Conclude with `(zt_mem (Λ := Λ) F F').2`.
-/
theorem xplus_le' (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T') (hz' : F'.zt = F'.fl.z) :
    Xplus F' ≤ UUE Λ F F' := by
  change F'.fl.X ⊔ Submodule.span E {F'.fl.z} ≤ _
  refine sup_le (PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE' S Λ hΛ F F') ?_
  rw [Submodule.span_le, Set.singleton_subset_iff, ← hz']
  exact (zt_mem (Λ := Λ) F F').2

/- English proof (translation)
The claim follows from `PI.ScalarPairDr.W.mem_orth_Xplus (S := S) G.fl`.
-/
theorem orth_xplus_iff {T₀ : E} (G : LFlag S r T₀) {v : S.V} :
    v ∈ orth S (Xplus G) ↔ (∀ a, S.hT (G.fl.e a) v = 0) ∧ S.hT G.fl.z v = 0 :=
  PI.ScalarPairDr.W.mem_orth_Xplus (S := S) G.fl

/- English proof (translation)
Rewrite using `[← PI.UnitaryGroupMassFormula.ScalEquivGen.orthOrthQ (UUE Λ F F'), PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ]`. Introduce `h hh`. Express the relevant statement in the definitionally equal form `h ∈ Hp Λ F F' at hh`. Rewrite `hh` using `[← hTh]`. Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.mp hh`.

Rewrite `hp` using `[PI.UnitaryGroupMassFormula.ScalEquivGen.memThPairsQ]`. Establish `hp2 : p.2 ∈ orth S (UUE Λ F F'')` using `hp.1.1.2`. Establish `hy1 : y ∈ UUE Λ F F''` using `hy.1`. Establish `hy2 : y ∈ orth S (Xplus F)` using `hy.2`. Establish `e1 : S.hT p.2 y = 0` using `PI.UnitaryGroupMassFormula.ScalEquivGen.hTCommQ.mp ((PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ.mp hp2) y hy1)`.

Establish `e2 : S.hT (p.1 - p.2) y = 0` using `PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ.mp (PI.UnitaryGroupMassFormula.ScalEquivGen.orthAntiQ (PI.UnitaryGroupMassFormula.ScalEquivGen.XspLeXplusQ F) hy2) _ hp.1.2`. Use `show S.hT p.1 y = 0`. Establish `e : p.1 = (p.1 - p.2) + p.2` using `by abel`. Rewrite using `[e, map_add, LinearMap.add_apply, e1, e2, add_zero]`.
-/
theorem ylift_rev (hTh : Th Λ F F' F'' β = Hp Λ F F') {y : S.V} (hy : y ∈ Ylift Λ F F'') : y ∈ UUE Λ F F' := by
  rw [← PI.UnitaryGroupMassFormula.ScalEquivGen.orthOrthQ (UUE Λ F F'), PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ]
  intro h hh
  change h ∈ Hp Λ F F' at hh
  rw [← hTh] at hh
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hh
  rw [PI.UnitaryGroupMassFormula.ScalEquivGen.memThPairsQ] at hp
  have hp2 : p.2 ∈ orth S (UUE Λ F F'') := hp.1.1.2
  have hy1 : y ∈ UUE Λ F F'' := hy.1
  have hy2 : y ∈ orth S (Xplus F) := hy.2
  have e1 : S.hT p.2 y = 0 :=
    PI.UnitaryGroupMassFormula.ScalEquivGen.hTCommQ.mp ((PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ.mp hp2) y hy1)
  have e2 : S.hT (p.1 - p.2) y = 0 :=
    PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ.mp (PI.UnitaryGroupMassFormula.ScalEquivGen.orthAntiQ (PI.UnitaryGroupMassFormula.ScalEquivGen.XspLeXplusQ F) hy2) _ hp.1.2
  show S.hT p.1 y = 0
  have e : p.1 = (p.1 - p.2) + p.2 := by abel
  rw [e, map_add, LinearMap.add_apply, e1, e2, add_zero]

variable (hΛ : Submodule.IsLattice E Λ) (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hz'' : F''.zt = F''.fl.z)
include hΛ hz hz' hz''

/- English proof (translation)
Establish `hzz` using `zz_ne F.fl hT`. Use `set c : E := (S.hT F.fl.z F.fl.z)⁻¹ with hc`. Use `set y : S.V := ν - c • F.fl.z with hy`. Establish `hyU : y ∈ UUE Λ F F'` using `Submodule.sub_mem _ (xplus_le' hΛ F F' hz' hν) (Submodule.smul_mem _ _ (hz ▸ (zt_mem (Λ := Λ) F F').1))`. Establish `hyO : y ∈ orth S (Xplus F)`.

Rewrite using `[orth_xplus_iff]`. Use `⟨fun a => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hy, map_sub, map_smul, he a, F.fl.z_orth a, smul_zero, sub_zero]`. Rewrite using `[hy, map_sub, map_smul, hzν, smul_eq_mul, hc, inv_mul_cancel₀ hzz, sub_self]`. Establish `hy' : y ∈ Ylift Λ F F'` using `⟨hyU, hyO⟩`.

Establish `hy'' : y ∈ Ylift Λ F F''` using `⟨PI.UnitaryGroupMassFormula.ScalEquivGen.yliftMemQ hTh hy', hyO⟩`. Take `⟨α', x', hx', hνe⟩` from `xplus_dec F'.fl hν`. Establish `hsg : SgRel F F' y 0 (-c) α'`. Use `⟨0, Submodule.zero_mem _, x', hx', ?_⟩` and prove the remaining obligations. Rewrite using `[hz, hz', hy, hνe, neg_smul]`.

Normalize the expressions using the abelian group laws. Establish `h0 : y - y ∈ Xsp F` using `by rw [sub_self]; exact Submodule.zero_mem _`. Establish `h0' : (0 : S.V) - β 0 ∈ Xsp F''` using `by simp`. Take `⟨x₂, hx₂, x'', hx'', h3⟩` from `(hSc y hy' y hy'' 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) h0 h0' (-c) α').1 hsg`. Rewrite `h3` using `[hz, hz'']`.

Use `⟨α' • F''.fl.z + x'', xplus_mem F''.fl α' hx'', ?_⟩` and prove the remaining obligations. Establish `hd : ν - (α' • F''.fl.z + x'') = x₂`. Establish `h4 : ν = (-c) • F.fl.z + x₂ + (α' • F''.fl.z + x'') + c • F.fl.z`. Rewrite using `[← h3, hy]`. Normalize the expressions using the abelian group laws.

Rewrite using `[h4, neg_smul]`. Normalize the expressions using the abelian group laws. Establish `hν₂ : α' • F''.fl.z + x'' = ν - x₂` using `by rw [← hd]; abel`. Use `⟨fun a => ?_, ?_, hd ▸ hx₂⟩` and prove the remaining obligations. Rewrite using `[hν₂, map_sub, he a, e_X F.fl a hx₂, sub_zero]`.

Rewrite using `[hν₂, map_sub, hzν, z_X F.fl hx₂, sub_zero]`.
-/
theorem firstNormal_transport (hT : T ≠ 0) (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') (hSc : IsScalar Λ F F' F'' β)
    {ν : S.V} (hν : ν ∈ Xplus F') (he : ∀ a, S.hT (F.fl.e a) ν = 0) (hzν : S.hT F.fl.z ν = 1) :
    ∃ ν₂ ∈ Xplus F'', (∀ a, S.hT (F.fl.e a) ν₂ = 0) ∧ S.hT F.fl.z ν₂ = 1 ∧ ν - ν₂ ∈ Xsp F := by
  have hzz := zz_ne F.fl hT
  set c : E := (S.hT F.fl.z F.fl.z)⁻¹ with hc
  set y : S.V := ν - c • F.fl.z with hy
  have hyU : y ∈ UUE Λ F F' :=
    Submodule.sub_mem _ (xplus_le' hΛ F F' hz' hν)
      (Submodule.smul_mem _ _ (hz ▸ (zt_mem (Λ := Λ) F F').1))
  have hyO : y ∈ orth S (Xplus F) := by
    rw [orth_xplus_iff]
    refine ⟨fun a => ?_, ?_⟩
    · rw [hy, map_sub, map_smul, he a, F.fl.z_orth a, smul_zero, sub_zero]
    · rw [hy, map_sub, map_smul, hzν, smul_eq_mul, hc, inv_mul_cancel₀ hzz, sub_self]
  have hy' : y ∈ Ylift Λ F F' := ⟨hyU, hyO⟩
  have hy'' : y ∈ Ylift Λ F F'' := ⟨PI.UnitaryGroupMassFormula.ScalEquivGen.yliftMemQ hTh hy', hyO⟩
  obtain ⟨α', x', hx', hνe⟩ := xplus_dec F'.fl hν
  have hsg : SgRel F F' y 0 (-c) α' := by
    refine ⟨0, Submodule.zero_mem _, x', hx', ?_⟩
    rw [hz, hz', hy, hνe, neg_smul]
    abel
  have h0 : y - y ∈ Xsp F := by rw [sub_self]; exact Submodule.zero_mem _
  have h0' : (0 : S.V) - β 0 ∈ Xsp F'' := by simp
  obtain ⟨x₂, hx₂, x'', hx'', h3⟩ :=
    (hSc y hy' y hy'' 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) h0 h0' (-c) α').1 hsg
  rw [hz, hz''] at h3
  refine ⟨α' • F''.fl.z + x'', xplus_mem F''.fl α' hx'', ?_⟩
  have hd : ν - (α' • F''.fl.z + x'') = x₂ := by
    have h4 : ν = (-c) • F.fl.z + x₂ + (α' • F''.fl.z + x'') + c • F.fl.z := by
      rw [← h3, hy]; abel
    rw [h4, neg_smul]; abel
  have hν₂ : α' • F''.fl.z + x'' = ν - x₂ := by rw [← hd]; abel
  refine ⟨fun a => ?_, ?_, hd ▸ hx₂⟩
  · rw [hν₂, map_sub, he a, e_X F.fl a hx₂, sub_zero]
  · rw [hν₂, map_sub, hzν, z_X F.fl hx₂, sub_zero]

/- English proof (translation)
Establish `hy' : d ∈ Ylift Λ F F'` using `⟨xplus_le' hΛ F F' hz' hd, hdO⟩`. Establish `hy'' : d ∈ Ylift Λ F F''` using `⟨PI.UnitaryGroupMassFormula.ScalEquivGen.yliftMemQ hTh hy', hdO⟩`. Take `⟨α', x', hx', hde⟩` from `xplus_dec F'.fl hd`. Establish `hsg : SgRel F F' d 0 0 α'`. Use `⟨0, Submodule.zero_mem _, x', hx', ?_⟩` and prove the remaining obligations.

Rewrite using `[hz', hde, zero_smul]`. Normalize the expressions using the abelian group laws. Establish `h0 : d - d ∈ Xsp F` using `by rw [sub_self]; exact Submodule.zero_mem _`. Establish `h0' : (0 : S.V) - β 0 ∈ Xsp F''` using `by simp`. Take `⟨x₂, hx₂, x'', hx'', h3⟩` from `(hSc d hy' d hy'' 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) h0 h0' 0 α').1 hsg`.

Rewrite `h3` using `[hz'']`. Establish `hd2 : α' • F''.fl.z + x'' = d - x₂`. Rewrite `h3` using `[sub_zero]`. Rewrite using `[h3, zero_smul]`. Normalize the expressions using the abelian group laws.

Use `⟨α' • F''.fl.z + x'', xplus_mem F''.fl α' hx'', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hd2]`. Conclude with `Submodule.sub_mem _ hdO (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F.fl hx₂)`. Introduce `h`. Rewrite `h` using `[hd2, sub_eq_zero]`.

Conclude with `hd0 (disj F.fl F'.fl hG' (h ▸ hx₂) hd)`.
-/
theorem ker_transport (hG' : Gflag F.fl F'.fl ≠ 0) (hTh : Th'' Λ F F' F'' β = Hp Λ F F'')
    (hSc : IsScalar Λ F F' F'' β) {d : S.V} (hd : d ∈ Xplus F') (hdO : d ∈ orth S (Xplus F)) (hd0 : d ≠ 0) :
    ∃ d₂ ∈ Xplus F'', d₂ ∈ orth S (Xplus F) ∧ d₂ ≠ 0 := by
  have hy' : d ∈ Ylift Λ F F' := ⟨xplus_le' hΛ F F' hz' hd, hdO⟩
  have hy'' : d ∈ Ylift Λ F F'' := ⟨PI.UnitaryGroupMassFormula.ScalEquivGen.yliftMemQ hTh hy', hdO⟩
  obtain ⟨α', x', hx', hde⟩ := xplus_dec F'.fl hd
  have hsg : SgRel F F' d 0 0 α' := by
    refine ⟨0, Submodule.zero_mem _, x', hx', ?_⟩
    rw [hz', hde, zero_smul]
    abel
  have h0 : d - d ∈ Xsp F := by rw [sub_self]; exact Submodule.zero_mem _
  have h0' : (0 : S.V) - β 0 ∈ Xsp F'' := by simp
  obtain ⟨x₂, hx₂, x'', hx'', h3⟩ :=
    (hSc d hy' d hy'' 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) h0 h0' 0 α').1 hsg
  rw [hz''] at h3
  have hd2 : α' • F''.fl.z + x'' = d - x₂ := by
    rw [sub_zero] at h3; rw [h3, zero_smul]; abel
  refine ⟨α' • F''.fl.z + x'', xplus_mem F''.fl α' hx'', ?_, ?_⟩
  · rw [hd2]
    exact Submodule.sub_mem _ hdO (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F.fl hx₂)
  · intro h
    rw [hd2, sub_eq_zero] at h
    exact hd0 (disj F.fl F'.fl hG' (h ▸ hx₂) hd)

/- English proof (translation)
Establish `hy'' : d ∈ Ylift Λ F F''` using `⟨xplus_le' hΛ F F'' hz'' hd, hdO⟩`. Establish `hy' : d ∈ Ylift Λ F F'` using `⟨ylift_rev hTh hy'', hdO⟩`. Take `⟨α', x', hx', hde⟩` from `xplus_dec F''.fl hd`. Establish `hsg : SgRel F F'' d 0 0 α'`. Use `⟨0, Submodule.zero_mem _, x', hx', ?_⟩` and prove the remaining obligations.

Rewrite using `[hz'', hde, zero_smul]`. Normalize the expressions using the abelian group laws. Establish `h0 : d - d ∈ Xsp F` using `by rw [sub_self]; exact Submodule.zero_mem _`. Establish `h0' : (0 : S.V) - β 0 ∈ Xsp F''` using `by simp`. Take `⟨x₂, hx₂, x'', hx'', h3⟩` from `(hSc d hy' d hy'' 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) h0 h0' 0 α').2 hsg`.

Rewrite `h3` using `[hz']`. Establish `hd2 : α' • F'.fl.z + x'' = d - x₂`. Rewrite `h3` using `[sub_zero]`. Rewrite using `[h3, zero_smul]`. Normalize the expressions using the abelian group laws.

Use `⟨α' • F'.fl.z + x'', xplus_mem F'.fl α' hx'', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hd2]`. Conclude with `Submodule.sub_mem _ hdO (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F.fl hx₂)`. Introduce `h`. Rewrite `h` using `[hd2, sub_eq_zero]`.

Conclude with `hd0 (disj F.fl F''.fl hG'' (h ▸ hx₂) hd)`.
-/
theorem ker_transport_rev (hG'' : Gflag F.fl F''.fl ≠ 0) (hTh : Th Λ F F' F'' β = Hp Λ F F')
    (hSc : IsScalar Λ F F' F'' β) {d : S.V} (hd : d ∈ Xplus F'') (hdO : d ∈ orth S (Xplus F)) (hd0 : d ≠ 0) :
    ∃ d₁ ∈ Xplus F', d₁ ∈ orth S (Xplus F) ∧ d₁ ≠ 0 := by
  have hy'' : d ∈ Ylift Λ F F'' := ⟨xplus_le' hΛ F F'' hz'' hd, hdO⟩
  have hy' : d ∈ Ylift Λ F F' := ⟨ylift_rev hTh hy'', hdO⟩
  obtain ⟨α', x', hx', hde⟩ := xplus_dec F''.fl hd
  have hsg : SgRel F F'' d 0 0 α' := by
    refine ⟨0, Submodule.zero_mem _, x', hx', ?_⟩
    rw [hz'', hde, zero_smul]
    abel
  have h0 : d - d ∈ Xsp F := by rw [sub_self]; exact Submodule.zero_mem _
  have h0' : (0 : S.V) - β 0 ∈ Xsp F'' := by simp
  obtain ⟨x₂, hx₂, x'', hx'', h3⟩ :=
    (hSc d hy' d hy'' 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) h0 h0' 0 α').2 hsg
  rw [hz'] at h3
  have hd2 : α' • F'.fl.z + x'' = d - x₂ := by
    rw [sub_zero] at h3; rw [h3, zero_smul]; abel
  refine ⟨α' • F'.fl.z + x'', xplus_mem F'.fl α' hx'', ?_, ?_⟩
  · rw [hd2]
    exact Submodule.sub_mem _ hdO (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F.fl hx₂)
  · intro h
    rw [hd2, sub_eq_zero] at h
    exact hd0 (disj F.fl F''.fl hG'' (h ▸ hx₂) hd)

omit hz hz' hz'' hΛ in
/- English proof (translation)
Use `show (Submodule.span E (F'.fl.e '' {i | i.1 < j})).map (β : S.V →ₗ[E] S.V) = Submodule.span E (F''.fl.e '' {i | i.1 < j})`. Rewrite using `[Submodule.map_span, Set.image_image]`. Use `congr 1`. Conclude with `Set.image_congr fun b _ => by simp [hβe]`.
-/
theorem xflag_map (hβe : ∀ b, β (F'.fl.e b) = F''.fl.e b) (j : ℕ) :
    (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j := by
  show (Submodule.span E (F'.fl.e '' {i | i.1 < j})).map (β : S.V →ₗ[E] S.V) =
    Submodule.span E (F''.fl.e '' {i | i.1 < j})
  rw [Submodule.map_span, Set.image_image]
  congr 1
  exact Set.image_congr fun b _ => by simp [hβe]

omit hz hz' hz'' hΛ in
/- English proof (translation)
Establish `h` using `xflag_map hβe r`. Rewrite `h` using `[PI.UnitaryGroupMassFormula.ScalEquivGen.XflagTopQ, PI.UnitaryGroupMassFormula.ScalEquivGen.XflagTopQ]`. Rewrite `hx` using `[← h]`. Take `⟨x', hx', rfl⟩` from `Submodule.mem_map.mp hx`. Simplify using `using hx'`.
-/
theorem symm_X (hβe : ∀ b, β (F'.fl.e b) = F''.fl.e b) {x : S.V} (hx : x ∈ Xsp F'') : β.symm x ∈ Xsp F' := by
  have h := xflag_map hβe r
  rw [PI.UnitaryGroupMassFormula.ScalEquivGen.XflagTopQ, PI.UnitaryGroupMassFormula.ScalEquivGen.XflagTopQ] at h
  rw [← h] at hx
  obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
  simpa using hx'

/- English proof (translation)
Establish `hzz` using `zz_ne F'.fl hT'`. Use `set c : E := (S.hT F'.fl.z F'.fl.z)⁻¹ with hc`. Use `set y : S.V := x₁ - c • F'.fl.z with hy`. Establish `hyU : y ∈ UUE Λ F F'` using `Submodule.sub_mem _ (xplus_le hΛ F F' hz hx) (Submodule.smul_mem _ _ (hz' ▸ (zt_mem (Λ := Λ) F F').2))`. Establish `hyO : y ∈ orth S (Xplus F')`.

Rewrite using `[orth_xplus_iff]`. Use `⟨fun b => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hy, map_sub, map_smul, hswap, he b, F'.fl.z_orth b, star_zero, smul_zero, sub_zero]`. Rewrite using `[hy, map_sub, map_smul, hswap, hzx, star_one, smul_eq_mul, hc, inv_mul_cancel₀ hzz, sub_self]`. Establish `hy' : y ∈ Ylift' Λ F F'` using `⟨hyU, hyO⟩`.

Establish `hby : β y ∈ UUE Λ F F''` using `PI.UnitaryGroupMassFormula.ScalEquivGen.ylift'MemQ hi (xflag_map hβe) hTh hy'`. Establish `hyO'` using `(orth_xplus_iff F').1 hyO`. Establish `hbyO : β y ∈ orth S (Xplus F'')`. Rewrite using `[orth_xplus_iff]`. Use `⟨fun b => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hβe b, hi]`. Conclude with `hyO'.1 b`. Rewrite using `[← hβz, hi]`. Conclude with `hyO'.2`. Establish `hby' : β y ∈ Ylift' Λ F F''` using `⟨hby, hbyO⟩`.

Take `⟨a, ξ, hξ, hxe⟩` from `xplus_dec F.fl hx`. Establish `hsg : SgRel F F' 0 y (-a) c`. Use `⟨-ξ, Submodule.neg_mem _ hξ, 0, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, hz', hy, hxe, neg_smul]`. Normalize the expressions using the abelian group laws.

Establish `h0 : (0 : S.V) - 0 ∈ Xsp F` using `by simp`. Establish `h0' : β y - β y ∈ Xsp F''` using `by rw [sub_self]; exact Submodule.zero_mem _`. Take `⟨x₃, hx₃, x'', hx'', h3⟩` from `(hSc 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) y hy' (β y) hby' h0 h0' (-a) c).1 hsg`. Rewrite `h3` using `[hz, hz'']`. Establish `hx2 : a • F.fl.z + -x₃ = β y + c • F''.fl.z + x''`.

Establish `h4 : β y = -((-a) • F.fl.z + x₃ + (c • F''.fl.z + x''))` using `by rw [← h3]; abel`. Rewrite using `[h4, neg_smul]`. Normalize the expressions using the abelian group laws. Use `⟨a • F.fl.z + -x₃, xplus_mem F.fl a (Submodule.neg_mem _ hx₃), ?_⟩` and prove the remaining obligations. Establish `hzz'' : S.hT F''.fl.z F''.fl.z = S.hT F'.fl.z F'.fl.z` using `by rw [← hβz, hi]`.

Establish `k1 : ∀ b, S.hT (F''.fl.e b) (a • F.fl.z + -x₃) = 0`. Introduce `b`. Rewrite using `[hx2, map_add, map_add, map_smul, (orth_xplus_iff F'').1 hbyO |>.1 b, F''.fl.z_orth b, e_X F''.fl b hx'', smul_zero, zero_add, add_zero]`. Establish `k2 : S.hT F''.fl.z (a • F.fl.z + -x₃) = 1`. Rewrite using `[hx2, map_add, map_add, map_smul, (orth_xplus_iff F'').1 hbyO |>.2, z_X F''.fl hx'', hzz'', smul_eq_mul, hc, inv_mul_cancel₀ hzz, zero_add, add_zero]`.

Use `⟨fun b => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hswap, k1 b, star_zero]`. Rewrite using `[hswap, k2, star_one]`. Establish `hs : β.symm F''.fl.z = F'.fl.z` using `by rw [← hβz]; simp`. Rewrite using `[hx2, map_add, map_add, map_smul, LinearEquiv.symm_apply_apply, hs, hy]`.

Establish `: x₁ - c • F'.fl.z + c • F'.fl.z + β.symm x'' - x₁ = β.symm x''` using `by abel`. Rewrite using `[this]`. Conclude with `symm_X hβe hx''`.
-/
theorem secondNormal_transport (hT' : T' ≠ 0) (hi : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hβe : ∀ b, β (F'.fl.e b) = F''.fl.e b)
    (hβz : β F'.fl.z = F''.fl.z) (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') (hSc : IsScalar Λ F F' F'' β)
    {x₁ : S.V} (hx : x₁ ∈ Xplus F) (he : ∀ b, S.hT x₁ (F'.fl.e b) = 0) (hzx : S.hT x₁ F'.fl.z = 1) :
    ∃ x₂ ∈ Xplus F, (∀ b, S.hT x₂ (F''.fl.e b) = 0) ∧ S.hT x₂ F''.fl.z = 1 ∧ β.symm x₂ - x₁ ∈ Xsp F' := by
  have hzz := zz_ne F'.fl hT'
  set c : E := (S.hT F'.fl.z F'.fl.z)⁻¹ with hc
  set y : S.V := x₁ - c • F'.fl.z with hy
  have hyU : y ∈ UUE Λ F F' :=
    Submodule.sub_mem _ (xplus_le hΛ F F' hz hx)
      (Submodule.smul_mem _ _ (hz' ▸ (zt_mem (Λ := Λ) F F').2))
  have hyO : y ∈ orth S (Xplus F') := by
    rw [orth_xplus_iff]
    refine ⟨fun b => ?_, ?_⟩
    · rw [hy, map_sub, map_smul, hswap, he b, F'.fl.z_orth b, star_zero, smul_zero, sub_zero]
    · rw [hy, map_sub, map_smul, hswap, hzx, star_one, smul_eq_mul, hc, inv_mul_cancel₀ hzz, sub_self]
  have hy' : y ∈ Ylift' Λ F F' := ⟨hyU, hyO⟩
  have hby : β y ∈ UUE Λ F F'' := PI.UnitaryGroupMassFormula.ScalEquivGen.ylift'MemQ hi (xflag_map hβe) hTh hy'
  have hyO' := (orth_xplus_iff F').1 hyO
  have hbyO : β y ∈ orth S (Xplus F'') := by
    rw [orth_xplus_iff]
    refine ⟨fun b => ?_, ?_⟩
    · rw [← hβe b, hi]; exact hyO'.1 b
    · rw [← hβz, hi]; exact hyO'.2
  have hby' : β y ∈ Ylift' Λ F F'' := ⟨hby, hbyO⟩
  obtain ⟨a, ξ, hξ, hxe⟩ := xplus_dec F.fl hx
  have hsg : SgRel F F' 0 y (-a) c := by
    refine ⟨-ξ, Submodule.neg_mem _ hξ, 0, Submodule.zero_mem _, ?_⟩
    rw [hz, hz', hy, hxe, neg_smul]
    abel
  have h0 : (0 : S.V) - 0 ∈ Xsp F := by simp
  have h0' : β y - β y ∈ Xsp F'' := by rw [sub_self]; exact Submodule.zero_mem _
  obtain ⟨x₃, hx₃, x'', hx'', h3⟩ :=
    (hSc 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) y hy' (β y) hby' h0 h0' (-a) c).1 hsg
  rw [hz, hz''] at h3
  have hx2 : a • F.fl.z + -x₃ = β y + c • F''.fl.z + x'' := by
    have h4 : β y = -((-a) • F.fl.z + x₃ + (c • F''.fl.z + x'')) := by rw [← h3]; abel
    rw [h4, neg_smul]; abel
  refine ⟨a • F.fl.z + -x₃, xplus_mem F.fl a (Submodule.neg_mem _ hx₃), ?_⟩
  have hzz'' : S.hT F''.fl.z F''.fl.z = S.hT F'.fl.z F'.fl.z := by rw [← hβz, hi]
  have k1 : ∀ b, S.hT (F''.fl.e b) (a • F.fl.z + -x₃) = 0 := by
    intro b
    rw [hx2, map_add, map_add, map_smul, (orth_xplus_iff F'').1 hbyO |>.1 b, F''.fl.z_orth b,
      e_X F''.fl b hx'', smul_zero, zero_add, add_zero]
  have k2 : S.hT F''.fl.z (a • F.fl.z + -x₃) = 1 := by
    rw [hx2, map_add, map_add, map_smul, (orth_xplus_iff F'').1 hbyO |>.2, z_X F''.fl hx'', hzz'', smul_eq_mul,
      hc, inv_mul_cancel₀ hzz, zero_add, add_zero]
  refine ⟨fun b => ?_, ?_, ?_⟩
  · rw [hswap, k1 b, star_zero]
  · rw [hswap, k2, star_one]
  · have hs : β.symm F''.fl.z = F'.fl.z := by rw [← hβz]; simp
    rw [hx2, map_add, map_add, map_smul, LinearEquiv.symm_apply_apply, hs, hy]
    have : x₁ - c • F'.fl.z + c • F'.fl.z + β.symm x'' - x₁ = β.symm x'' := by abel
    rw [this]
    exact symm_X hβe hx''

omit hz hz' hz'' hΛ in

/- English proof (translation)
Rewrite `hy` using `[← hTh]`. Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.mp hy`. Rewrite `hp` using `[PI.UnitaryGroupMassFormula.ScalEquivGen.memThPairsQ]`. Conclude with `⟨p.1, hp.1.1.1, hp.1.2, hp.2⟩`.
-/
theorem orthogonal_transport (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') {y₂ : S.V} (hy : y₂ ∈ Hp Λ F F'') :
    ∃ y₁ ∈ Hp Λ F F', y₁ - y₂ ∈ Xsp F ∧ β y₁ - y₂ ∈ Xsp F'' := by
  rw [← hTh] at hy
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
  rw [PI.UnitaryGroupMassFormula.ScalEquivGen.memThPairsQ] at hp
  exact ⟨p.1, hp.1.1.1, hp.1.2, hp.2⟩

end Pair

end Formalism.L2.SG.Pf.RowForm.ClassFramePositivePartDecomposition
