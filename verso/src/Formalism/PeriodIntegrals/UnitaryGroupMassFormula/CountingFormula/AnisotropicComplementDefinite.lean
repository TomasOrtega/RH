import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ZMemPerp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CardLeOfNonpos

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Unfold `Tn`. Conclude with `Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero`.
-/
theorem tn_ne_zero (D : D7) (u : D.what₂.Word) : (Tn u : D.host.E) ≠ 0 := by
  unfold Tn
  exact Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero

/- English proof (translation)
Establish `hT` using `(D.mem u).A.T_prime.pos`. Use `first`. Consider the case `simp [Tn, hT]`. Consider the case `(unfold Tn; simp; exact hT)`.
-/
theorem tau_negT (D : D7) (u : D.what₂.Word) (φ : D.host.E →+* ℂ) : (φ (-(Tn u))).re < 0 := by
  have hT := (D.mem u).A.T_prime.pos
  first
    | simp [Tn, hT]
    | (unfold Tn; simp; exact hT)

/- English proof (translation)
Unfold `VS`. Rewrite using `[D.sp.Y_rank 0 (Nat.zero_le _)]`. Take `⟨j, hj⟩` from `D.R.m_even`. Establish `h2` using `D.R.two_le_m`. Simplify using `only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS, zero_mul, add_zero]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem rank_VS (D : D7) : (VS D).rank = D.R.k + D.R.rS + (D.R.rS + 1) := by
  unfold VS
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]
  obtain ⟨j, hj⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS, zero_mul, add_zero]
  omega

/- English proof (translation)
Introduce and unpack `⟨y, hy⟩ hne φ`. Proceed by induction on `y using Submodule.Quotient.induction_on with`. Consider the case `H a => ?_`. Establish `hya : (VS D).hT F0.z a.1 = 0`. Establish `h` using `hy`.

Rewrite `h` using `[wPerp, LinearMap.mem_ker, zbar, hWb_mk]`. Conclude with `h`. Establish `hna : a.1 ∉ F0.X`. Introduce `hmem`. Apply `hne` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show Submodule.Quotient.mk a = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `hmem`. Establish `hval : hPerp (hWb D F0) (zbar D F0) ⟨Submodule.Quotient.mk a, hy⟩ ⟨Submodule.Quotient.mk a, hy⟩ = (VS D).hT a.1 a.1` using `hWb_mk D F0 a a`.

Rewrite using `[hval]`. Assume the negation of the conclusion as `hle`. Use `push Not at hle`. Establish `hT0` using `tn_ne_zero D u`. Establish `hzX : ∀ x ∈ F0.X, (VS D).hT F0.z x = 0` using `fun x hx => hT_perp_X D F0 (z_mem_perp D F0) hx`.

Set `v : Option (Option (Fin D.R.rS)) → (VS D).V` to `fun o => Option.casesOn' o a.1 (fun o' => Option.casesOn' o' F0.z F0.e)`. Establish `hv : LinearIndependent D.host.E v` using `by show LinearIndependent D.host.E (fun o => Option.casesOn' o a.1 (fun o' => Option.casesOn' o' F0.z F0.e) : Option (Option (Fin D.R.rS)) → (VS D).V)`. Rewrite using `[linearIndependent_option', linearIndependent_option']`. Use `⟨⟨F0.e_indep, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `hz`.

Establish `h` using `hzX F0.z hz`. Rewrite `h` using `[F0.z_norm]`. Conclude with `hT0 (neg_eq_zero.1 h)`. Introduce `ha`. Establish `hle' : Submodule.span D.host.E (Set.range (fun o' : Option (Fin D.R.rS) => Option.casesOn' o' F0.z F0.e)) ≤ F0.X ⊔ Submodule.span D.host.E {F0.z}`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨o, rfl⟩`. Consider the cases of `o with`. Consider the case `none => exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Consider the case `some i => exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)`.

Take `⟨x, hx, w, hw, hxw⟩` from `Submodule.mem_sup.1 (hle' ha)`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hw`. Establish `h1 : (VS D).hT F0.z a.1 = c * (-(Tn u))`. Rewrite using `[← hxw, map_add, map_smul, hzX x hx, F0.z_norm, smul_eq_mul, zero_add]`. Rewrite `h1` using `[hya]`.

Establish `hc : c = 0`. Break down `mul_eq_zero.1 h1.symm with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (neg_eq_zero.1 h) hT0`. Apply `hna` to reduce the goal to its premises.

Rewrite using `[← hxw, hc, zero_smul, add_zero]`. Conclude with `hx`. Establish `horth : ∀ o o', o ≠ o' → (VS D).hT (v o) (v o') = 0`. Introduce `o o' hne'`. Use `match o, o', hne' with`.

Consider the case `none, none, h => exact absurd rfl h`. Consider the case `none, some none, _ => show (VS D).hT a.1 F0.z = 0`. Rewrite using `[← (VS D).herm.eq F0.z a.1, hya, map_zero]`. Consider the case `none, some (some j), _ => exact hT_perp_X D F0 a.2 (Submodule.subset_span ⟨j, rfl⟩)`. Consider the case `some none, none, _ => exact hya`.

Consider the case `some none, some none, h => exact absurd rfl h`. Consider the case `some none, some (some j), _ => exact hzX _ (Submodule.subset_span ⟨j, rfl⟩)`. Consider the case `some (some i), none, _ => exact hT_X_perp D F0 (Submodule.subset_span ⟨i, rfl⟩) a.2`. Consider the case `some (some i), some none, _ => exact F0.z_orth i`. Consider the case `some (some i), some (some j), _ => exact F0.e_iso i j`.

Establish `hnp : ∀ o, (φ ((VS D).hT (v o) (v o))).re ≤ 0`. Introduce `o`. Use `match o with`. Consider the case `none => exact hle`. Consider the case `some none => show (φ ((VS D).hT F0.z F0.z)).re ≤ 0`.

Rewrite using `[F0.z_norm]`. Conclude with `le_of_lt (tau_negT D u φ)`. Consider the case `some (some i) => show (φ ((VS D).hT (F0.e i) (F0.e i))).re ≤ 0`. Rewrite using `[F0.e_iso i i]`. Simplify using the standard rewrite rules.

Establish `hcard` using `WbDefH.card_le_of_nonpos (VS D) φ (D.sp.cm.cmUnram.2.1 φ) (D.sp.Y_sig 0 φ) v hv horth hnp`. Establish `hs : (VS D).sig φ = D.R.sigY0` using `D.sp.baseSpace_signature_eq φ`. Rewrite `hcard` using `[hs]`. Simplify using `[Ranks.sigY0] at hcard`.
-/
theorem wbDef_pos (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) :
    Formalism.HermitianLattices.Ext.L3.IsTotPosDef (hPerp (hWb D F0) (zbar D F0)) := by
  rintro ⟨y, hy⟩ hne φ
  induction y using Submodule.Quotient.induction_on with
  | H a => ?_
  have hya : (VS D).hT F0.z a.1 = 0 := by
    have h := hy
    rw [wPerp, LinearMap.mem_ker, zbar, hWb_mk] at h
    exact h
  have hna : a.1 ∉ F0.X := by
    intro hmem
    apply hne
    apply Subtype.ext
    show Submodule.Quotient.mk a = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hmem
  have hval : hPerp (hWb D F0) (zbar D F0) ⟨Submodule.Quotient.mk a, hy⟩ ⟨Submodule.Quotient.mk a, hy⟩ =
      (VS D).hT a.1 a.1 := hWb_mk D F0 a a
  rw [hval]
  by_contra hle
  push Not at hle
  have hT0 := tn_ne_zero D u
  have hzX : ∀ x ∈ F0.X, (VS D).hT F0.z x = 0 := fun x hx => hT_perp_X D F0 (z_mem_perp D F0) hx
  let v : Option (Option (Fin D.R.rS)) → (VS D).V :=
    fun o => Option.casesOn' o a.1 (fun o' => Option.casesOn' o' F0.z F0.e)
  have hv : LinearIndependent D.host.E v := by
    show LinearIndependent D.host.E
      (fun o => Option.casesOn' o a.1 (fun o' => Option.casesOn' o' F0.z F0.e) : Option (Option (Fin D.R.rS)) → (VS D).V)
    rw [linearIndependent_option', linearIndependent_option']
    refine ⟨⟨F0.e_indep, ?_⟩, ?_⟩
    · intro hz
      have h := hzX F0.z hz
      rw [F0.z_norm] at h
      exact hT0 (neg_eq_zero.1 h)
    · intro ha
      have hle' : Submodule.span D.host.E
          (Set.range (fun o' : Option (Fin D.R.rS) => Option.casesOn' o' F0.z F0.e)) ≤
          F0.X ⊔ Submodule.span D.host.E {F0.z} := by
        rw [Submodule.span_le]
        rintro _ ⟨o, rfl⟩
        cases o with
        | none => exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
        | some i => exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      obtain ⟨x, hx, w, hw, hxw⟩ := Submodule.mem_sup.1 (hle' ha)
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have h1 : (VS D).hT F0.z a.1 = c * (-(Tn u)) := by
        rw [← hxw, map_add, map_smul, hzX x hx, F0.z_norm, smul_eq_mul, zero_add]
      rw [hya] at h1
      have hc : c = 0 := by
        rcases mul_eq_zero.1 h1.symm with h | h
        · exact h
        · exact absurd (neg_eq_zero.1 h) hT0
      apply hna
      rw [← hxw, hc, zero_smul, add_zero]
      exact hx
  have horth : ∀ o o', o ≠ o' → (VS D).hT (v o) (v o') = 0 := by
    intro o o' hne'
    match o, o', hne' with
    | none, none, h => exact absurd rfl h
    | none, some none, _ =>
      show (VS D).hT a.1 F0.z = 0
      rw [← (VS D).herm.eq F0.z a.1, hya, map_zero]
    | none, some (some j), _ => exact hT_perp_X D F0 a.2 (Submodule.subset_span ⟨j, rfl⟩)
    | some none, none, _ => exact hya
    | some none, some none, h => exact absurd rfl h
    | some none, some (some j), _ => exact hzX _ (Submodule.subset_span ⟨j, rfl⟩)
    | some (some i), none, _ => exact hT_X_perp D F0 (Submodule.subset_span ⟨i, rfl⟩) a.2
    | some (some i), some none, _ => exact F0.z_orth i
    | some (some i), some (some j), _ => exact F0.e_iso i j
  have hnp : ∀ o, (φ ((VS D).hT (v o) (v o))).re ≤ 0 := by
    intro o
    match o with
    | none => exact hle
    | some none =>
      show (φ ((VS D).hT F0.z F0.z)).re ≤ 0
      rw [F0.z_norm]
      exact le_of_lt (tau_negT D u φ)
    | some (some i) =>
      show (φ ((VS D).hT (F0.e i) (F0.e i))).re ≤ 0
      rw [F0.e_iso i i]
      simp
  have hcard := WbDefH.card_le_of_nonpos (VS D) φ (D.sp.cm.cmUnram.2.1 φ) (D.sp.Y_sig 0 φ) v hv horth hnp
  have hs : (VS D).sig φ = D.R.sigY0 := D.sp.baseSpace_signature_eq φ
  rw [hs] at hcard
  simp [Ranks.sigY0] at hcard

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `hy2 : ∀ x ∈ F0.X, (VS D).hT x y = 0` using `hy`.

Use function extensionality and compare the values at `a`. Conclude with `hy2 _ (Submodule.subset_span ⟨a, rfl⟩)`. Introduce `hy`. Establish `hy' : ∀ a, (VS D).hT (F0.e a) y = 0` using `fun a => congrFun hy a`. Use `show ∀ x ∈ F0.X, (VS D).hT x y = 0`.

Introduce `x hx`. Unfold `Formalism.MainNotions.S.FlagG.X at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨a, rfl⟩` from `h`.

Conclude with `hy' a`. Consider the case `zero => simp`. Consider the case `add x z _ _ h1 h2 => simp [h1, h2]`. Consider the case `smul c x _ h1 => simp [h1]`.
-/
private theorem perpS_eq_ker_pi_hT (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) :
    perpS (VS D) F0.X = LinearMap.ker (LinearMap.pi fun a => (VS D).hT (F0.e a)) := by
  ext y
  rw [LinearMap.mem_ker]
  constructor
  · intro hy
    have hy2 : ∀ x ∈ F0.X, (VS D).hT x y = 0 := hy
    funext a
    exact hy2 _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro hy
    have hy' : ∀ a, (VS D).hT (F0.e a) y = 0 := fun a => congrFun hy a
    show ∀ x ∈ F0.X, (VS D).hT x y = 0
    intro x hx
    unfold Formalism.MainNotions.S.FlagG.X at hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hy' a
    | zero => simp
    | add x z _ _ h1 h2 => simp [h1, h2]
    | smul c x _ h1 => simp [h1]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hf⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)`. Establish `key : ∀ a, f (fun j => if a = j then 1 else 0) = 0`. Establish `hw : ∀ y, (VS D).hT (∑ a, star (f (fun j => if a = j then 1 else 0)) • F0.e a) y = 0`. Introduce `y`.

Establish `h1 : f ((LinearMap.pi fun a => (VS D).hT (F0.e a)) y) = 0` using `LinearMap.mem_ker.mp (hf (LinearMap.mem_range_self _ y))`. Rewrite `h1` using `[LinearMap.pi_apply_eq_sum_univ]`. Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]`. Simplify `h1` using `[LinearMap.pi_apply, smul_eq_mul, mul_comm]`. Establish `h0` using `(VS D).nondeg.1 _ hw`.

Introduce `a`. Use `Fintype.linearIndependent_iff.mp F0.e_indep (fun a => star (f (fun j => if a = j then 1 else 0))) h0 a` as an intermediate fact. Simplify using `using this`. Apply `hf0` to reduce the goal to its premises. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.pi_apply_eq_sum_univ]`. Simplify using `[key]`.
-/
private theorem range_pi_hT_eq_top (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) :
    LinearMap.range (LinearMap.pi fun a => (VS D).hT (F0.e a)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have key : ∀ a, f (fun j => if a = j then 1 else 0) = 0 := by
    have hw : ∀ y, (VS D).hT (∑ a, star (f (fun j => if a = j then 1 else 0)) • F0.e a) y = 0 := by
      intro y
      have h1 : f ((LinearMap.pi fun a => (VS D).hT (F0.e a)) y) = 0 :=
        LinearMap.mem_ker.mp (hf (LinearMap.mem_range_self _ y))
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
        LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
      simpa [LinearMap.pi_apply, smul_eq_mul, mul_comm] using h1
    have h0 := (VS D).nondeg.1 _ hw
    intro a
    have := Fintype.linearIndependent_iff.mp F0.e_indep
      (fun a => star (f (fun j => if a = j then 1 else 0))) h0 a
    simpa using this
  apply hf0
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp [key]

/- English proof (translation)
Unfold `wPerp`. Establish `hle : F0.X ≤ perpS (VS D) F0.X`. Rewrite using `[perpS_eq_ker_pi_hT D u F0]`. Unfold `Formalism.MainNotions.S.FlagG.X`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker]`. Use function extensionality and compare the values at `b`. Conclude with `F0.e_iso b a`. Establish `hX : finrank D.host.E F0.X = D.R.rS`.

Unfold `Formalism.MainNotions.S.FlagG.X`. Rewrite using `[finrank_span_eq_card F0.e_indep, Fintype.card_fin]`. Establish `hnX : finrank D.host.E (nX D F0) = D.R.rS` using `(Submodule.comapSubtypeEquivOfLe hle).finrank_eq.trans hX`. Establish `hP : finrank D.host.E (perpS (VS D) F0.X) + D.R.rS = D.R.k + D.R.rS + (D.R.rS + 1)`. Rewrite using `[perpS_eq_ker_pi_hT D u F0]`.

Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun a => (VS D).hT (F0.e a))`. Rewrite `h1` using `[range_pi_hT_eq_top D u F0, finrank_top, Module.finrank_fin_fun]`. Establish `h2` using `(VS D).rank_eq`. Rewrite `h2` using `[rank_VS D]`. Use linear arithmetic over natural numbers and integers.

Establish `hq : finrank D.host.E (WbQ D F0) + finrank D.host.E (nX D F0) = finrank D.host.E (perpS (VS D) F0.X)` using `Submodule.finrank_quotient_add_finrank (nX D F0)`. Establish `hsurj : Function.Surjective (hWb D F0 (zbar D F0))`. Introduce `c`. Use `⟨(c / -(Tn u)) • zbar D F0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hWb_zbar, smul_eq_mul]`.

Establish `hT0` using `tn_ne_zero D u`. Clear the denominators using the available nonvanishing facts. Establish `hk` using `LinearMap.finrank_range_add_finrank_ker (hWb D F0 (zbar D F0))`. Rewrite `hk` using `[LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]`. Use linear arithmetic over natural numbers and integers.
-/
theorem wbDef_dim (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) :
    finrank D.host.E (wPerp (hWb D F0) (zbar D F0)) = D.R.k := by
  unfold wPerp
  have hle : F0.X ≤ perpS (VS D) F0.X := by
    rw [perpS_eq_ker_pi_hT D u F0]
    unfold Formalism.MainNotions.S.FlagG.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext b
    exact F0.e_iso b a
  have hX : finrank D.host.E F0.X = D.R.rS := by
    unfold Formalism.MainNotions.S.FlagG.X
    rw [finrank_span_eq_card F0.e_indep, Fintype.card_fin]
  have hnX : finrank D.host.E (nX D F0) = D.R.rS :=
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq.trans hX
  have hP : finrank D.host.E (perpS (VS D) F0.X) + D.R.rS = D.R.k + D.R.rS + (D.R.rS + 1) := by
    rw [perpS_eq_ker_pi_hT D u F0]
    have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun a => (VS D).hT (F0.e a))
    rw [range_pi_hT_eq_top D u F0, finrank_top, Module.finrank_fin_fun] at h1
    have h2 := (VS D).rank_eq
    rw [rank_VS D] at h2
    omega
  have hq : finrank D.host.E (WbQ D F0) + finrank D.host.E (nX D F0) =
      finrank D.host.E (perpS (VS D) F0.X) :=
    Submodule.finrank_quotient_add_finrank (nX D F0)
  have hsurj : Function.Surjective (hWb D F0 (zbar D F0)) := by
    intro c
    refine ⟨(c / -(Tn u)) • zbar D F0, ?_⟩
    rw [map_smul, hWb_zbar, smul_eq_mul]
    have hT0 := tn_ne_zero D u
    field_simp
  have hk := LinearMap.finrank_range_add_finrank_ker (hWb D F0 (zbar D F0))
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at hk
  omega

/- English proof (translation)
Unfold `WbDef`. Introduce `D u F0`. Conclude with `⟨wbDef_pos D u F0, wbDef_dim D u F0⟩`.
-/
theorem anisotropic_complement_definite : WbDef := by
  unfold WbDef
  intro D u F0
  exact ⟨wbDef_pos D u F0, wbDef_dim D u F0⟩

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
