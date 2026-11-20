import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.BCAllPlaces

open Formalism.MainNotions.SumRepresentations.At GlobalTheory.TwistLG GlobalTheory.BCGal

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

def AllRep (m : ℕ) (L : ∀ w, A.LP w) : Prop :=
  ∃ r : Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin m) (Qbar (N.l i)), ContQ N i r ∧ IsSSRep r ∧
    ∀ w, WDok N A i r w ∧ A.wdOf i r w = L w

/- English proof (translation)
Substitute `hm` using the available equality. Take `⟨r, c, s, f⟩` from `h`. Conclude with `⟨r, c, s, fun w => ⟨(f w).1, (f w).2.trans (hL w)⟩⟩`.
-/
theorem AllRep.congr {m m' : ℕ} {L L' : ∀ w, A.LP w} (h : AllRep N A i m L) (hm : m = m')
    (hL : ∀ w, L w = L' w) : AllRep N A i m' L' := by
  subst hm
  obtain ⟨r, c, s, f⟩ := h
  exact ⟨r, c, s, fun w => ⟨(f w).1, (f w).2.trans (hL w)⟩⟩

/- English proof (translation)
Take `⟨r, c, s, f⟩` from `h`. Take `⟨r', c', s', f'⟩` from `h'`. Take `⟨-, -, hsum, -⟩` from `hGal.2.2.2 i`. Use `⟨sumRep r r', cont_sumRep r r' c c', ss_sumRep r r' s s', fun w => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Distinguish the cases in `hw : w ∈ placesOver H.E (N.l i)`.

Conclude with `Or.inr (((hsum m m' r r' c c').1 w hw).2 ⟨(f w).1.resolve_left (not_not.2 hw), (f' w).1.resolve_left (not_not.2 hw)⟩)`. Conclude with `Or.inl hw`. Rewrite using `[(hsum m m' r r' c c').2.1 w (f w).1 (f' w).1, (f w).2, (f' w).2]`.
-/
theorem AllRep.sum (hGal : TieGal N A) {m m' : ℕ} {L L' : ∀ w, A.LP w} (h : AllRep N A i m L)
    (h' : AllRep N A i m' L') : AllRep N A i (m + m') fun w => A.lpSum (L w) (L' w) := by
  obtain ⟨r, c, s, f⟩ := h
  obtain ⟨r', c', s', f'⟩ := h'
  obtain ⟨-, -, hsum, -⟩ := hGal.2.2.2 i
  refine ⟨sumRep r r', cont_sumRep r r' c c', ss_sumRep r r' s s', fun w => ⟨?_, ?_⟩⟩
  · by_cases hw : w ∈ placesOver H.E (N.l i)
    · exact Or.inr (((hsum m m' r r' c c').1 w hw).2
        ⟨(f w).1.resolve_left (not_not.2 hw), (f' w).1.resolve_left (not_not.2 hw)⟩)
    · exact Or.inl hw
  · rw [(hsum m m' r r' c c').2.1 w (f w).1 (f' w).1, (f w).2, (f' w).2]

/- English proof (translation)
Introduce `w`. Distinguish the cases in `hw : w ∈ placesOver H.E (N.l i)`. Conclude with `⟨Or.inr (h2 w hw).1, (h2 w hw).2⟩`. Conclude with `⟨Or.inl hw, h1 w hw⟩`.
-/
theorem allw {a : ℕ} (ρ : Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (L : ∀ w, A.LP w)
    (h1 : ∀ w, w ∉ placesOver H.E (N.l i) → A.wdOf i ρ w = L w)
    (h2 : ∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ w ∧ A.wdOf i ρ w = L w) :
    ∀ w, WDok N A i ρ w ∧ A.wdOf i ρ w = L w := by
  intro w
  by_cases hw : w ∈ placesOver H.E (N.l i)
  · exact ⟨Or.inr (h2 w hw).1, (h2 w hw).2⟩
  · exact ⟨Or.inl hw, h1 w hw⟩

/- English proof (translation)
Take `⟨-, -, -, htw⟩` from `hGal.2.2.2 i`. Establish `ht` using `htw a ρ χ cρ cχ`. Introduce `w`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hw : w ∈ placesOver H.E (N.l i)`.

Conclude with `Or.inr ((ht.1 w hw ((hχ w).1.resolve_left (not_not.2 hw))).2 ((hρ w).1.resolve_left (not_not.2 hw)))`. Conclude with `Or.inl hw`. Rewrite using `[ht.2.1 w (hρ w).1 (hχ w).1, (hρ w).2, (hχ w).2]`.
-/
theorem allTw (hGal : TieGal N A) {a : ℕ} (ρ : Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin a) (Qbar (N.l i)))
    (χ : Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin 1) (Qbar (N.l i))) (cρ : ContQ N i ρ) (cχ : ContQ N i χ)
    {L M : ∀ w, A.LP w} (hρ : ∀ w, WDok N A i ρ w ∧ A.wdOf i ρ w = L w)
    (hχ : ∀ w, WDok N A i χ w ∧ A.wdOf i χ w = M w) :
    ∀ w, WDok N A i (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w ∧
      A.wdOf i (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w = A.lpChar (L w) (M w) := by
  obtain ⟨-, -, -, htw⟩ := hGal.2.2.2 i
  have ht := htw a ρ χ cρ cχ
  intro w
  refine ⟨?_, ?_⟩
  · by_cases hw : w ∈ placesOver H.E (N.l i)
    · exact Or.inr ((ht.1 w hw ((hχ w).1.resolve_left (not_not.2 hw))).2
        ((hρ w).1.resolve_left (not_not.2 hw)))
    · exact Or.inl hw
  · rw [ht.2.1 w (hρ w).1 (hχ w).1, (hρ w).2, (hχ w).2]

/- English proof (translation)
The claim follows from `| [], h, _ => absurd rfl h | [x], _, h => (h x (by simp)).congr N A i (by simp) fun w => by simp [A.lpSum_zero] | x :: y :: ys, _, h => ((h x (by simp)).sum N A i hGal (allRep_foldr hGal m L (y :: ys) (by simp) fun z hz => h z (List.mem_cons_of_mem _ hz))).congr N A i (by simp) f …`.
-/
theorem allRep_foldr (hGal : TieGal N A) {α : Type} (m : α → ℕ) (L : α → ∀ w, A.LP w) :
    ∀ xs : List α, xs ≠ [] → (∀ x ∈ xs, AllRep N A i (m x) (L x)) →
      AllRep N A i (xs.map m).sum fun w => xs.foldr (fun x acc => A.lpSum (L x w) acc) (A.lpZero w)
  | [], h, _ => absurd rfl h
  | [x], _, h => (h x (by simp)).congr N A i (by simp) fun w => by simp [A.lpSum_zero]
  | x :: y :: ys, _, h =>
      ((h x (by simp)).sum N A i hGal (allRep_foldr hGal m L (y :: ys) (by simp)
        fun z hz => h z (List.mem_cons_of_mem _ hz))).congr N A i (by simp) fun w => rfl

/- English proof (translation)
Proceed by induction on `xs with`. Consider the case `nil => exact lpTw_lpZero N A w c`. Consider the case `cons x xs ih => rw [List.foldr_cons, List.foldr_cons, A.lpTw_sum, ih]`.
-/
theorem lpTw_foldr {α : Type} (L : α → ∀ w, A.LP w) (w : PlE H) (c : ℝ) (xs : List α) :
    A.lpTw (xs.foldr (fun x acc => A.lpSum (L x w) acc) (A.lpZero w)) c =
      xs.foldr (fun x acc => A.lpSum (A.lpTw (L x w) c) acc) (A.lpZero w) := by
  induction xs with
  | nil => exact lpTw_lpZero N A w c
  | cons x xs ih => rw [List.foldr_cons, List.foldr_cons, A.lpTw_sum, ih]

/- English proof (translation)
Establish `hp : ∀ p ∈ Pa, AllRep N A i (p.a * p.d) fun w => A.lpTw (spehLoc N A p w) c`. Introduce `p hpm`. Establish `hmem : ∀ k ∈ ((List.range p.d : List ℕ) : List ℝ), ∃ n : ℕ, n < p.d ∧ (n : ℝ) = k`. Introduce `k hk`. Simplify using `[Lean.Internal.coeM] at hk`.

Take `⟨n, hn, rfl⟩` from `hk`. Conclude with `⟨n, hn, rfl⟩`. Establish `hr : ((List.range p.d : List ℕ) : List ℝ) ≠ []`. Establish `h1 : 0 < p.d` using `hd p hpm`. Introduce `h0`.

Establish `: ((0 : ℕ) : ℝ) ∈ ((List.range p.d : List ℕ) : List ℝ)`. Simplify using `[Lean.Internal.coeM]`. Conclude with `⟨0, h1, by simp⟩`. Rewrite `this` using `[h0]`. Simplify using `at this`.

Use `(allRep_foldr N A i hGal (fun _ => p.a) (fun (k : ℝ) w => A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + c)) _ hr fun k hk => ?_).congr N A i ?_ fun w => ?_` and prove the remaining obligations. Take `⟨n, hn, rfl⟩` from `hmem k hk`. Conclude with `h p hpm n hn`. Simplify using `[Lean.Internal.coeM, mul_comm]`. Rewrite using `[spehLoc, lpTw_foldr N A (fun (k : ℝ) w => A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) w c]`.

Simplify using `only [A.lpTw_add]`. Conclude with `(allRep_foldr N A i hGal (fun p => p.a * p.d) (fun p w => A.lpTw (spehLoc N A p w) c) Pa hne hp).congr N A i rfl fun w => (lpTw_foldr N A (fun p w => spehLoc N A p w) w c Pa).symm`.
-/
theorem allRep_isoLoc (hGal : TieGal N A) (c : ℝ) (Pa : List (Part A.CG)) (hne : Pa ≠ [])
    (hd : ∀ p ∈ Pa, 1 ≤ p.d)
    (h : ∀ p ∈ Pa, ∀ k < p.d, AllRep N A i p.a fun w =>
      A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + c)) :
    AllRep N A i (rankIso N A Pa) fun w => A.lpTw (isoLoc N A Pa w) c := by
  have hp : ∀ p ∈ Pa, AllRep N A i (p.a * p.d) fun w => A.lpTw (spehLoc N A p w) c := by
    intro p hpm
    have hmem : ∀ k ∈ ((List.range p.d : List ℕ) : List ℝ), ∃ n : ℕ, n < p.d ∧ (n : ℝ) = k := by
      intro k hk
      simp [Lean.Internal.coeM] at hk
      obtain ⟨n, hn, rfl⟩ := hk
      exact ⟨n, hn, rfl⟩
    have hr : ((List.range p.d : List ℕ) : List ℝ) ≠ [] := by
      have h1 : 0 < p.d := hd p hpm
      intro h0
      have : ((0 : ℕ) : ℝ) ∈ ((List.range p.d : List ℕ) : List ℝ) := by
        simp [Lean.Internal.coeM]
        exact ⟨0, h1, by simp⟩
      rw [h0] at this
      simp at this
    refine (allRep_foldr N A i hGal (fun _ => p.a)
      (fun (k : ℝ) w => A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + c)) _ hr
      fun k hk => ?_).congr N A i ?_ fun w => ?_
    · obtain ⟨n, hn, rfl⟩ := hmem k hk
      exact h p hpm n hn
    · simp [Lean.Internal.coeM, mul_comm]
    · rw [spehLoc, lpTw_foldr N A (fun (k : ℝ) w => A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) w c]
      simp only [A.lpTw_add]
  exact (allRep_foldr N A i hGal (fun p => p.a * p.d) (fun p w => A.lpTw (spehLoc N A p w) c) Pa hne hp).congr
    N A i rfl fun w => (lpTw_foldr N A (fun p w => spehLoc N A p w) w c Pa).symm

end Glob

section Piece

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

/- English proof (translation)
Apply the tactic sequence `rcases Int.even_or_odd' m with ⟨k, hk | hk⟩ <;> subst hk`. Establish `hralg : A.ralg π` using `(A.ralg_def π).2 fun τ => ⟨(hinf τ).1, fun z hz => by`. Take `⟨n, hn⟩` from `(hinf τ).2 z hz`. Conclude with `⟨n - k, by push_cast at hn ⊢; linear_combination hn⟩⟩`. Take `⟨ρ1, c1, ss1, away1, over1⟩` from `(hG i).1 a ha π hc hralg`.

Take `⟨χA, cA, awayA, overA⟩` from `(hG i).2.2 A.etaT (1 / 2) fun τ z hz => by`. Take `⟨n, hn⟩` from `(eta_alg N A hAut 0 τ).1 z hz`. Conclude with `⟨n, by push_cast at hn ⊢; linear_combination hn⟩`. Take `⟨χB, cB, awayB, overB⟩` from `(hG i).2.2 A.etaTinv ((k : ℝ) - 1 / 2) fun τ z hz => by`. Take `⟨n, hn⟩` from `(eta_alg N A hAut (k - 1) τ).2 z hz`.

Conclude with `⟨n, by push_cast at hn ⊢; linear_combination hn⟩`. Establish `f1` using `allw N A i ρ1 _ (fun w hw => (away1 w hw).1) fun w hw => ⟨(over1 w hw).1, (over1 w hw).2.2⟩`. Establish `fA` using `allw N A i χA _ awayA fun w hw => ⟨(overA w hw).1, (overA w hw).2.1⟩`. Establish `fB` using `allw N A i χB _ awayB fun w hw => ⟨(overB w hw).1, (overB w hw).2.1⟩`. Set `ρ2` to `twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χA)`.

Establish `c2 : ContQ N i ρ2` using `cont_twGL ρ1 χA c1 cA`. Establish `f2` using `allTw N A i hGal ρ1 χA c1 cA f1 fA`. Establish `f3` using `allTw N A i hGal ρ2 χB c2 cB f2 fB`. Use `⟨twGL ρ2 (Matrix.GeneralLinearGroup.det.comp χB), cont_twGL ρ2 χB c2 cB, isSSRep_twGL _ _ (isSSRep_twGL _ _ ss1), fun w => ⟨(f3 w).1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[(f3 w).2, param_int N A hLP]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hcsd : A.csd (A.tw π A.etaT)` using `A.csd_tw π A.etaT hAut.1.1 hc`. Establish `hralg : A.ralg (A.tw π A.etaT)` using `(A.ralg_def _).2 fun τ => by`.

Take `⟨e, he⟩` from `Multiset.card_eq_one.mp (A.infG_card A.etaT τ)`. Rewrite using `[A.infG_tw π A.etaT τ e he]`. Use `⟨(hinf τ).1.map (add_left_injective e), fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, rfl⟩` from `Multiset.mem_map.1 hy`. Take `⟨n, hn⟩` from `(hinf τ).2 z hz`.

Take `⟨j, hj⟩` from `(eta_alg N A hAut 0 τ).1 e (by rw [he]; exact Multiset.mem_singleton_self e)`. Conclude with `⟨n + j - k - 1, by push_cast at hn hj ⊢; linear_combination hn + hj⟩`. Take `⟨ρ1, c1, ss1, away1, over1⟩` from `(hG i).1 a ha _ hcsd hralg`. Take `⟨χ1, cχ, awayχ, overχ⟩` from `(hG i).2.2 A.etaTinv ((k : ℝ) + 1 / 2) (eta_alg N A hAut k · |>.2)`. Establish `f1` using `allw N A i ρ1 _ (fun w hw => (away1 w hw).1) fun w hw => ⟨(over1 w hw).1, (over1 w hw).2.2⟩`.

Establish `fχ` using `allw N A i χ1 _ awayχ fun w hw => ⟨(overχ w hw).1, (overχ w hw).2.1⟩`. Establish `f2` using `allTw N A i hGal ρ1 χ1 c1 cχ f1 fχ`. Use `⟨twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χ1), cont_twGL ρ1 χ1 c1 cχ, isSSRep_twGL _ _ ss1, fun w => ⟨(f2 w).1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[(f2 w).2, param_twist N A hLP]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem allRep_piece (hLP : TieLP N A) (hAut : TieAut N A) (hGal : TieGal N A) (hG : exists_galois_rep_local_global_compatible N A)
    {a : ℕ} (ha : 1 ≤ a) (π : A.CG a) (hc : A.csd π) (m : ℤ)
    (hinf : ∀ τ, (A.infG π τ).Nodup ∧
      ∀ z ∈ A.infG π τ, ∃ n : ℤ, z + (((m : ℝ) / 2 : ℝ) : ℂ) = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    AllRep N A i a fun w => A.lpTw (A.locG π w) ((m : ℝ) / 2 + (1 - (a : ℝ)) / 2) := by
  rcases Int.even_or_odd' m with ⟨k, hk | hk⟩ <;> subst hk
  ·
    have hralg : A.ralg π := (A.ralg_def π).2 fun τ => ⟨(hinf τ).1, fun z hz => by
      obtain ⟨n, hn⟩ := (hinf τ).2 z hz
      exact ⟨n - k, by push_cast at hn ⊢; linear_combination hn⟩⟩
    obtain ⟨ρ1, c1, ss1, away1, over1⟩ := (hG i).1 a ha π hc hralg
    obtain ⟨χA, cA, awayA, overA⟩ := (hG i).2.2 A.etaT (1 / 2) fun τ z hz => by
      obtain ⟨n, hn⟩ := (eta_alg N A hAut 0 τ).1 z hz
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    obtain ⟨χB, cB, awayB, overB⟩ := (hG i).2.2 A.etaTinv ((k : ℝ) - 1 / 2) fun τ z hz => by
      obtain ⟨n, hn⟩ := (eta_alg N A hAut (k - 1) τ).2 z hz
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    have f1 := allw N A i ρ1 _ (fun w hw => (away1 w hw).1) fun w hw => ⟨(over1 w hw).1, (over1 w hw).2.2⟩
    have fA := allw N A i χA _ awayA fun w hw => ⟨(overA w hw).1, (overA w hw).2.1⟩
    have fB := allw N A i χB _ awayB fun w hw => ⟨(overB w hw).1, (overB w hw).2.1⟩
    let ρ2 := twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χA)
    have c2 : ContQ N i ρ2 := cont_twGL ρ1 χA c1 cA
    have f2 := allTw N A i hGal ρ1 χA c1 cA f1 fA
    have f3 := allTw N A i hGal ρ2 χB c2 cB f2 fB
    refine ⟨twGL ρ2 (Matrix.GeneralLinearGroup.det.comp χB), cont_twGL ρ2 χB c2 cB,
      isSSRep_twGL _ _ (isSSRep_twGL _ _ ss1), fun w => ⟨(f3 w).1, ?_⟩⟩
    rw [(f3 w).2, param_int N A hLP]
    congr 1
    push_cast
    ring
  ·
    have hcsd : A.csd (A.tw π A.etaT) := A.csd_tw π A.etaT hAut.1.1 hc
    have hralg : A.ralg (A.tw π A.etaT) := (A.ralg_def _).2 fun τ => by
      obtain ⟨e, he⟩ := Multiset.card_eq_one.mp (A.infG_card A.etaT τ)
      rw [A.infG_tw π A.etaT τ e he]
      refine ⟨(hinf τ).1.map (add_left_injective e), fun y hy => ?_⟩
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      obtain ⟨n, hn⟩ := (hinf τ).2 z hz
      obtain ⟨j, hj⟩ := (eta_alg N A hAut 0 τ).1 e (by rw [he]; exact Multiset.mem_singleton_self e)
      exact ⟨n + j - k - 1, by push_cast at hn hj ⊢; linear_combination hn + hj⟩
    obtain ⟨ρ1, c1, ss1, away1, over1⟩ := (hG i).1 a ha _ hcsd hralg
    obtain ⟨χ1, cχ, awayχ, overχ⟩ := (hG i).2.2 A.etaTinv ((k : ℝ) + 1 / 2) (eta_alg N A hAut k · |>.2)
    have f1 := allw N A i ρ1 _ (fun w hw => (away1 w hw).1) fun w hw => ⟨(over1 w hw).1, (over1 w hw).2.2⟩
    have fχ := allw N A i χ1 _ awayχ fun w hw => ⟨(overχ w hw).1, (overχ w hw).2.1⟩
    have f2 := allTw N A i hGal ρ1 χ1 c1 cχ f1 fχ
    refine ⟨twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χ1), cont_twGL ρ1 χ1 c1 cχ, isSSRep_twGL _ _ ss1,
      fun w => ⟨(f2 w).1, ?_⟩⟩
    rw [(f2 w).2, param_twist N A hLP]
    congr 1
    push_cast
    ring

end Piece

/- English proof (translation)
Introduce `D hT hG i P Pa hB`. Take `⟨hLP, hAut, hGal⟩` from `hT`. Establish `hne : Pa ≠ []`. Introduce and unpack `rfl`. Establish `h0` using `hB.2.2.1`.

Simplify using `only [rankIso, List.map_nil, List.sum_nil] at h0`. Establish `: 1 ≤ D.R.nV`. Use `D.R.t_odd.pos` as an intermediate fact. Unfold `Ranks.nV`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Establish `hreal` using `allRep_isoLoc D.nd D.naut i hGal ((1 - (D.R.nV : ℝ)) / 2) Pa hne (fun p hp => (hB.1 p hp).2.1) fun p hp k hk => by`. Take `⟨ha, -, hc⟩` from `hB.1 p hp`. Use `(allRep_piece D.nd D.naut i hLP hAut hGal hG ha p.π hc ((p.d : ℤ) - 1 - 2 * k + p.a - D.R.nV) fun τ => ?_).congr D.nd D.naut i rfl fun w => ?_` and prove the remaining obligations. Establish `hW : (D.naut.infWt i τ).Nodup ∧ ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2`.

Rewrite using `[D.nbc.embAV_inf i P]`. Conclude with `D.nbc.infW_alg _ _ τ`. Establish `hle : (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k)) ≤ D.naut.infWt i τ`. Rewrite using `[← hB.2.2.2.2.2 τ]`. Use `le_trans (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ ?_) (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))` and prove the remaining obligations.

Conclude with `List.mem_map.2 ⟨k, by simpa using hk, rfl⟩`. Use `⟨(Multiset.nodup_of_le hle hW.1).of_map _, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `hW.2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz))`. Conclude with `⟨n, by push_cast at hn ⊢; linear_combination hn⟩`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨r, c, s, f⟩` from `hreal.congr D.nd D.naut i hB.2.2.1 fun _ => rfl`. Conclude with `⟨r, c, s, f⟩`.
-/
theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → ∀ (i : D.nd.Loc) (PI : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), IsBCV D.nd D.naut i PI Pa →
    ∃ ρ : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧
      ∀ w, SumRepresentations.At.WDok D.nd D.naut i ρ w ∧
        D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) := by
  intro D hT hG i P Pa hB
  obtain ⟨hLP, hAut, hGal⟩ := hT
  have hne : Pa ≠ [] := by
    rintro rfl
    have h0 := hB.2.2.1
    simp only [rankIso, List.map_nil, List.sum_nil] at h0
    have : 1 ≤ D.R.nV := by
      have := D.R.t_odd.pos
      unfold Ranks.nV
      omega
    omega
  have hreal := allRep_isoLoc D.nd D.naut i hGal ((1 - (D.R.nV : ℝ)) / 2) Pa hne
    (fun p hp => (hB.1 p hp).2.1) fun p hp k hk => by
    obtain ⟨ha, -, hc⟩ := hB.1 p hp
    refine (allRep_piece D.nd D.naut i hLP hAut hGal hG ha p.π hc
      ((p.d : ℤ) - 1 - 2 * k + p.a - D.R.nV) fun τ => ?_).congr D.nd D.naut i rfl fun w => ?_
    · have hW : (D.naut.infWt i τ).Nodup ∧
          ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
        rw [D.nbc.embAV_inf i P]
        exact D.nbc.infW_alg _ _ τ
      have hle : (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k)) ≤ D.naut.infWt i τ := by
        rw [← hB.2.2.2.2.2 τ]
        refine le_trans (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ ?_)
          (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
        exact List.mem_map.2 ⟨k, by simpa using hk, rfl⟩
      refine ⟨(Multiset.nodup_of_le hle hW.1).of_map _, fun z hz => ?_⟩
      obtain ⟨n, hn⟩ := hW.2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz))
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    · congr 1
      push_cast
      ring
  obtain ⟨r, c, s, f⟩ := hreal.congr D.nd D.naut i hB.2.2.1 fun _ => rfl
  exact ⟨r, c, s, f⟩

end GlobalTheory.BCAllPlaces

end
