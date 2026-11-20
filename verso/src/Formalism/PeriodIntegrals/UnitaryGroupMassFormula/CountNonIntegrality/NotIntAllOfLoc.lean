import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseMulEquiv

noncomputable section

namespace PI.CntNotIntW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def NormAt {L : Loc.LocE F E} (g : Loc.SplitG L) {r : ℕ} (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) : Prop :=
  (∃ s : 𝒪[F], (g.e (Zh a b)).1 + (if a = Fin.last r ∧ b = Fin.last r then T else 0) = (g.q : F) * s) ∧
  (∃ s : 𝒪[F], (g.e (Zh a b)).2 + (if a = Fin.last r ∧ b = Fin.last r then T else 0) = (g.q : F) * s) ∧
  (∃ s : 𝒪[F], (g.e (Zh a b)).1 + (g.e (Zh b a)).2 + (if a = Fin.last r ∧ b = Fin.last r then T + T' else 0) =
    (g.q : F) ^ 2 * s)

/- English proof (translation)
Unfold `Loc.Model.R`. Rewrite using `[hs]`. Simplify using `only [Subring.mem_comap, Subring.mem_map]`. Use `⟨(s1, s2), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.mem_eqLocus]`.

Simplify using `only [RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_snd]`. Conclude with `Ideal.Quotient.eq.2 hc`. Simplify using `[he]`.
-/
theorem mem_R_split (M : Loc.Model F E) (g : Loc.SplitG M.L) (hs : M.split = some g) (x : E) (s1 s2 : 𝒪[F])
    (he : g.e x = ((s1 : F), (s2 : F))) (hc : s1 - s2 ∈ Ideal.span {g.q}) : x ∈ M.R := by
  unfold Loc.Model.R
  rw [hs]
  simp only [Subring.mem_comap, Subring.mem_map]
  refine ⟨(s1, s2), ?_, ?_⟩
  · rw [RingHom.mem_eqLocus]
    simp only [RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_snd]
    exact Ideal.Quotient.eq.2 hc
  · simp [he]

/- English proof (translation)
Establish `hq : (g.q : F) ≠ 0`. Introduce `h0`. Establish `: g.q = 0` using `Subtype.ext h0`. Conclude with `g.q_irr.ne_zero this`. Take `⟨k, hk⟩` from `hTT`.

Take `⟨⟨s1, hs1⟩, -, ⟨s3, hs3⟩⟩` from `h a b`. Take `⟨-, ⟨s2, hs2⟩, -⟩` from `h b a`. Use `set c : Prop := a = Fin.last r ∧ b = Fin.last r with hc_def`. Establish `hcs : (b = Fin.last r ∧ a = Fin.last r) ↔ c` using `and_comm`. Unfold `Loc.HermSp.ZZplusOf`.

Rewrite using `[hs]`. Simplify using `only [Matrix.of_apply]`. Distinguish the cases in `hcc : c`. Establish `hcc' : b = Fin.last r ∧ a = Fin.last r` using `hcs.2 hcc`. Rewrite using `[if_pos hcc]`.

Rewrite `hs1`, `hs3` using `[if_pos hcc]`. Rewrite `hs2` using `[if_pos hcc']`. Use `mem_R_split M g hs _ s1 (k - s2) ?_ ?_` and prove the remaining obligations. Rewrite using `[map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]`. Use `ext`.

Simplify using `only [Prod.fst_sub]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `hs1`. Simplify using `only [Prod.snd_sub]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-hs2 + hk`. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨s3, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Use `push_cast`. Apply `mul_left_cancel₀ hq` to reduce the goal to its premises. Take the linear combination `hs1 + hs2 - hs3 - hk`. Rewrite using `[if_neg hcc, sub_zero]`. Establish `hcc' : ¬ (b = Fin.last r ∧ a = Fin.last r)` using `fun h' => hcc (hcs.1 h')`.

Rewrite `hs1` using `[if_neg hcc, add_zero]`. Rewrite `hs3` using `[if_neg hcc, add_zero]`. Rewrite `hs2` using `[if_neg hcc', add_zero]`. Use `mem_R_split M g hs _ s1 (-s2) ?_ ?_` and prove the remaining obligations. Rewrite using `[AlgEquiv.apply_symm_apply]`.

Use `ext`. Simplify using `only`. Clear the denominators using the available nonvanishing facts. Take the linear combination `hs1`. Simplify using `only`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-hs2`. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨s3, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `push_cast`. Apply `mul_left_cancel₀ hq` to reduce the goal to its premises. Take the linear combination `hs1 + hs2 - hs3`.
-/
theorem zzplus_mem (M : Loc.Model F E) (g : Loc.SplitG M.L) (hs : M.split = some g) {r : ℕ}
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (hTT : ∃ k : 𝒪[F], T - T' = (g.q : F) * k)
    (h : ∀ a b, NormAt g Zh T T' a b) (a b : Fin (r + 1)) : Loc.HermSp.ZZplusOf M Zh T T' a b ∈ M.R := by
  have hq : (g.q : F) ≠ 0 := by
    intro h0
    have : g.q = 0 := Subtype.ext h0
    exact g.q_irr.ne_zero this
  obtain ⟨k, hk⟩ := hTT
  obtain ⟨⟨s1, hs1⟩, -, ⟨s3, hs3⟩⟩ := h a b
  obtain ⟨-, ⟨s2, hs2⟩, -⟩ := h b a
  set c : Prop := a = Fin.last r ∧ b = Fin.last r with hc_def
  have hcs : (b = Fin.last r ∧ a = Fin.last r) ↔ c := and_comm
  unfold Loc.HermSp.ZZplusOf
  rw [hs]
  simp only [Matrix.of_apply]
  by_cases hcc : c
  · have hcc' : b = Fin.last r ∧ a = Fin.last r := hcs.2 hcc
    rw [if_pos hcc]
    rw [if_pos hcc] at hs1 hs3
    rw [if_pos hcc'] at hs2
    refine mem_R_split M g hs _ s1 (k - s2) ?_ ?_
    · rw [map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      ext
      · simp only [Prod.fst_sub]
        field_simp
        linear_combination hs1
      · simp only [Prod.snd_sub]
        push_cast
        field_simp
        linear_combination -hs2 + hk
    · rw [Ideal.mem_span_singleton']
      refine ⟨s3, ?_⟩
      apply Subtype.ext
      push_cast
      apply mul_left_cancel₀ hq
      linear_combination hs1 + hs2 - hs3 - hk
  · rw [if_neg hcc, sub_zero]
    have hcc' : ¬ (b = Fin.last r ∧ a = Fin.last r) := fun h' => hcc (hcs.1 h')
    rw [if_neg hcc, add_zero] at hs1
    rw [if_neg hcc, add_zero] at hs3
    rw [if_neg hcc', add_zero] at hs2
    refine mem_R_split M g hs _ s1 (-s2) ?_ ?_
    · rw [AlgEquiv.apply_symm_apply]
      ext
      · simp only
        field_simp
        linear_combination hs1
      · simp only
        push_cast
        field_simp
        linear_combination -hs2
    · rw [Ideal.mem_span_singleton']
      refine ⟨s3, ?_⟩
      apply Subtype.ext
      push_cast
      apply mul_left_cancel₀ hq
      linear_combination hs1 + hs2 - hs3

end Generic

def NormG : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ → ∀ Λ ∈ what₂, ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')),
        F' ∈ EZ (Tn u') F0 Λ Z → ∀ p (g : Loc.SplitG (M p).L), (M p).split = some g →
          ∀ a b, NormAt g (ZhatLoc M δ p Z) (((D.mem u).A.T : ℕ) : (D.s.atP p).Fp)
            (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) a b

/- English proof (translation)
Establish `hm` using `(hA p).2.2.2.2.2`. Rewrite `hm` using `[hs]`. Break down `hsp : (D.s.atP p).split with _ | sg` into its components or cases. Rewrite `hm` using `[hsp]`. Conclude with `hm.elim`.

Rewrite `hm` using `[hsp]`. Establish `hqq : g.q = sg.q` using `hm.2`. Establish `hell : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)` using `(D.s_split p).1 (by rw [hsp]; rfl)`. Establish `hdvd : Loc.resChar p ∣ Lat.gS D ^ 2`. Apply `Dvd.dvd.pow _ two_ne_zero` to reduce the goal to its premises.

Unfold `Lat.gS`. Break down `Finset.mem_insert.1 hell with h0 | h1` into its components or cases. Rewrite using `[h0]`. Conclude with `dvd_mul_right _ _`. Rewrite using `[Finset.mem_singleton.1 h1]`.

Conclude with `dvd_mul_left _ _`. Establish `hmod : (D.mem u).A.T ≡ (D.mem u').A.T [MOD Loc.resChar p]` using `Nat.ModEq.of_dvd hdvd hT`. Establish `hz : ((Loc.resChar p : ℕ) : ℤ) ∣ ((D.mem u').A.T : ℤ) - ((D.mem u).A.T : ℤ)` using `(Nat.modEq_iff_dvd).1 hmod`. Take `⟨k, hk⟩` from `hz`. Use `⟨⟨((-k : ℤ) : (D.s.atP p).Fp), intCast_mem _ (-k)⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hqq, sg.q_eq]`. Establish `hk' : (((D.mem u').A.T : ℤ) : (D.s.atP p).Fp) - (((D.mem u).A.T : ℤ) : (D.s.atP p).Fp) = (((Loc.resChar p : ℕ) : ℤ) : (D.s.atP p).Fp) * ((k : ℤ) : (D.s.atP p).Fp)`. Rewrite using `[← Int.cast_sub, hk, Int.cast_mul]`. Simplify using `only [Int.cast_natCast] at hk'`. Use `push_cast`.

Take the linear combination `-hk'`.
-/
theorem tt_mod_q (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word)
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (p : PlF D) (g : Loc.SplitG (M p).L)
    (hs : (M p).split = some g) :
    ∃ k : 𝒪[(D.s.atP p).Fp], (((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) - (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) =
      (g.q : (D.s.atP p).Fp) * k := by
  have hm := (hA p).2.2.2.2.2
  rw [hs] at hm
  rcases hsp : (D.s.atP p).split with _ | sg
  · rw [hsp] at hm
    exact hm.elim
  · rw [hsp] at hm
    have hqq : g.q = sg.q := hm.2
    have hell : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := (D.s_split p).1 (by rw [hsp]; rfl)
    have hdvd : Loc.resChar p ∣ Lat.gS D ^ 2 := by
      apply Dvd.dvd.pow _ two_ne_zero
      unfold Lat.gS
      rcases Finset.mem_insert.1 hell with h0 | h1
      · rw [h0]; exact dvd_mul_right _ _
      · rw [Finset.mem_singleton.1 h1]; exact dvd_mul_left _ _
    have hmod : (D.mem u).A.T ≡ (D.mem u').A.T [MOD Loc.resChar p] := Nat.ModEq.of_dvd hdvd hT
    have hz : ((Loc.resChar p : ℕ) : ℤ) ∣ ((D.mem u').A.T : ℤ) - ((D.mem u).A.T : ℤ) :=
      (Nat.modEq_iff_dvd).1 hmod
    obtain ⟨k, hk⟩ := hz
    refine ⟨⟨((-k : ℤ) : (D.s.atP p).Fp), intCast_mem _ (-k)⟩, ?_⟩
    rw [hqq, sg.q_eq]
    have hk' : (((D.mem u').A.T : ℤ) : (D.s.atP p).Fp) - (((D.mem u).A.T : ℤ) : (D.s.atP p).Fp) =
        (((Loc.resChar p : ℕ) : ℤ) : (D.s.atP p).Fp) * ((k : ℤ) : (D.s.atP p).Fp) := by
      rw [← Int.cast_sub, hk, Int.cast_mul]
    simp only [Int.cast_natCast] at hk'
    push_cast
    linear_combination -hk'

/- English proof (translation)
Introduce `D δ M hA u u' hT F0 what₂ hrows Λ hΛ Z F' hF' p g hs a b`. Conclude with `zzplus_mem (M p) g hs _ _ _ (tt_mod_q D δ M hA u u' hT p g hs) (hN D δ M hA u u' hT F0 what₂ hrows Λ hΛ Z F' hF' p g hs) a b`.
-/
theorem intG_of (hN : NormG) : IntG := by
  intro D δ M hA u u' hT F0 what₂ hrows Λ hΛ Z F' hF' p g hs a b
  exact zzplus_mem (M p) g hs _ _ _ (tt_mod_q D δ M hA u u' hT p g hs)
    (hN D δ M hA u u' hT F0 what₂ hrows Λ hΛ Z F' hF' p g hs) a b

/- English proof (translation)
The claim follows from `notIntAll_of_gen hL (intG_of hN)`.
-/
theorem notIntAll_of_loc (hL : LocGen) (hN : NormG) : PI.CntLocalParts.NotIntAll :=
  notIntAll_of_gen hL (intG_of hN)

end PI.CntNotIntW
