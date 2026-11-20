import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FourTermExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace TVCoefPf

variable {k r : ℕ}

/- English proof (translation)
The claim follows from `Fin.ext rfl`.
-/
theorem castLE_self (h : r ≤ r) (a : Fin r) : Fin.castLE h a = a := Fin.ext rfl

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `Fin.ext` to reduce the goal to its premises.

Establish `h'` using `congrArg Fin.val h`. Simplify using `only [esI] at h'`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Rewrite using `[h]`.
-/
theorem esI_inj (a b : Fin r) : esI k r a = esI k r b ↔ a = b := by
  have := a.isLt
  have := b.isLt
  constructor
  · intro h
    apply Fin.ext
    have h' := congrArg Fin.val h
    simp only [esI] at h'
    omega
  · intro h; rw [h]

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Unfold `C3.keyS esI`. Simplify using `only`. Apply the tactic sequence `split_ifs with h <;> omega`.
-/
theorem keyS_esI (a : Fin r) : C3.keyS k r (esI k r a) = a.val := by
  have := a.isLt
  unfold C3.keyS esI
  simp only
  split_ifs with h <;> omega

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Formalism.FourierDecayAlt.P.Qx3.w1_apply, Formalism.FourierDecayAlt.P.Qx3.sw_es, Formalism.FourierDecayAlt.P.Qx3.dd_es]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem w1_mulVec_bvec_esI (l : Fin r) (s : ℂ) : Q.w1 k r l s *ᵥ bvec (esI k r l) = (star s)⁻¹ • bvec (eI k r l) := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, Formalism.FourierDecayAlt.P.Qx3.sw_es, Formalism.FourierDecayAlt.P.Qx3.dd_es]
  split_ifs <;> simp

/- English proof (translation)
Establish `h1 : a.val ≠ b.val` using `fun h => hab (Fin.ext h)`. Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Break down `hq with rfl | rfl` into its components or cases. Apply the tactic sequence `constructor <;> intro h <;> have h' := congrArg Fin.val h <;> simp only [eI, esI] at h' <;> omega`.

Apply the tactic sequence `constructor <;> intro h <;> have h' := congrArg Fin.val h <;> simp only [eI, esI] at h' <;> omega`.
-/
theorem ne_of_ne {a b : Fin r} (hab : ¬ a = b) {q : Fin (2 * r + k + 1)} (hq : q = eI k r a ∨ q = esI k r a) :
    q ≠ eI k r b ∧ q ≠ esI k r b := by
  have h1 : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have := a.isLt
  have := b.isLt
  rcases hq with rfl | rfl
  · constructor <;> intro h <;> have h' := congrArg Fin.val h <;> simp only [eI, esI] at h' <;> omega
  · constructor <;> intro h <;> have h' := congrArg Fin.val h <;> simp only [eI, esI] at h' <;> omega

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => intro _`. Simplify using the standard rewrite rules. Consider the case `cons b L ih`.

Introduce `ha`. Rewrite `ha` using `[List.mem_cons, not_or]`. Rewrite using `[List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih ha.2]`. Take `⟨h1, h2⟩` from `ne_of_ne ha.1 hq`. Conclude with `Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b (c b) h1 h2`.
-/
theorem wlist_fix (c : Fin r → ℂ) (a : Fin r) {q : Fin (2 * r + k + 1)} (hq : q = eI k r a ∨ q = esI k r a) :
    ∀ L : List (Fin r), a ∉ L → (L.map fun b => Q.w1 k r b (c b)).prod *ᵥ bvec q = bvec q := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons b L ih =>
    intro ha
    rw [List.mem_cons, not_or] at ha
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih ha.2]
    obtain ⟨h1, h2⟩ := ne_of_ne ha.1 hq
    exact Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b (c b) h1 h2

/- English proof (translation)
Establish `hc' : ∀ l, c l ≠ 0` using `hc`. Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => intro _ h`. Simplify using `at h`.

Consider the case `cons b L ih`. Introduce `hnd ha`. Rewrite `hnd` using `[List.nodup_cons]`. Rewrite using `[List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]`. Distinguish the cases in `hab : b = a`.

Substitute `hab` using the available equality. Rewrite using `[Matrix.mulVec_smul, wlist_fix c b (Or.inr rfl) L hnd.1, Matrix.mulVec_smul, w1_mulVec_bvec_esI, smul_smul, mul_inv_cancel₀ (star_ne_zero.2 (hc' b)), one_smul]`. Establish `haL : a ∈ L`. Break down `List.mem_cons.1 ha with h | h` into its components or cases. Conclude with `absurd h.symm hab`.

Conclude with `h`. Rewrite using `[ih hnd.2 haL]`. Take `⟨h1, h2⟩` from `ne_of_ne (fun h => hab h.symm) (Or.inl rfl)`. Conclude with `Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b (c b) h1 h2`.
-/
theorem wlist_main {c : Fin r → ℂ} (hc : c ∈ OmX r) (a : Fin r) :
    ∀ L : List (Fin r), L.Nodup → a ∈ L →
      (L.map fun b => Q.w1 k r b (c b)).prod *ᵥ (star (c a) • bvec (esI k r a)) = bvec (eI k r a) := by
  have hc' : ∀ l, c l ≠ 0 := hc
  intro L
  induction L with
  | nil => intro _ h; simp at h
  | cons b L ih =>
    intro hnd ha
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
    by_cases hab : b = a
    · subst hab
      rw [Matrix.mulVec_smul, wlist_fix c b (Or.inr rfl) L hnd.1, Matrix.mulVec_smul, w1_mulVec_bvec_esI, smul_smul,
        mul_inv_cancel₀ (star_ne_zero.2 (hc' b)), one_smul]
    · have haL : a ∈ L := by
        rcases List.mem_cons.1 ha with h | h
        · exact absurd h.symm hab
        · exact h
      rw [ih hnd.2 haL]
      obtain ⟨h1, h2⟩ := ne_of_ne (fun h => hab h.symm) (Or.inl rfl)
      exact Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b (c b) h1 h2

/- English proof (translation)
Unfold `Q.wCell`. Use `wlist_main hc a _ ((List.nodup_finRange r).filter _) ?_` and prove the remaining obligations. Rewrite using `[List.mem_filter]`. Conclude with `⟨List.mem_finRange a, by simp⟩`.
-/
theorem wcell_es {c : Fin r → ℂ} (hc : c ∈ OmX r) (a : Fin r) :
    Q.wCell k r (Fin.last r) c *ᵥ (star (c a) • bvec (esI k r a)) = bvec (eI k r a) := by
  unfold Q.wCell
  refine wlist_main hc a _ ((List.nodup_finRange r).filter _) ?_
  rw [List.mem_filter]
  exact ⟨List.mem_finRange a, by simp⟩

/- English proof (translation)
Establish `hW : Q.wCell k r (Fin.last r) c ∈ Q.Glev k r 0` using `Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _`. Establish `hu : IsUnit (Q.wCell k r (Fin.last r) c * g).det`. Rewrite using `[Matrix.det_mul]`. Conclude with `(Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hW.1).mul (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg.1)`. Establish `ha : a.val < (Fin.last r).val` using `by rw [Fin.val_last]; exact a.isLt`.

Establish `hv : (Q.wCell k r (Fin.last r) c * g) *ᵥ (star (c a) • bvec (esI k r a)) = bvec (eI k r a)`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.mulVec_smul, (hg.2 a ha).2]`. Conclude with `wcell_es hc a`. Rewrite using `[← hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`.
-/
theorem inv_e {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) (a : Fin r) :
    (Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r a) = star (c a) • bvec (esI k r a) := by
  have hW : Q.wCell k r (Fin.last r) c ∈ Q.Glev k r 0 := Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _
  have hu : IsUnit (Q.wCell k r (Fin.last r) c * g).det := by
    rw [Matrix.det_mul]
    exact (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hW.1).mul (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg.1)
  have ha : a.val < (Fin.last r).val := by rw [Fin.val_last]; exact a.isLt
  have hv : (Q.wCell k r (Fin.last r) c * g) *ᵥ (star (c a) • bvec (esI k r a)) = bvec (eI k r a) := by
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_smul, (hg.2 a ha).2]
    exact wcell_es hc a
  rw [← hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/- English proof (translation)
Use extensionality with `a l`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[castLE_self, inv_e hc hg a]`. Simplify using `[bvec, Pi.single_apply]`.
-/
theorem det_entry {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r))
    (B : Fin r → Fin (2 * r + k + 1)) :
    (Matrix.of fun a l : Fin r =>
        ((Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)) =
      Matrix.of fun a l : Fin r => star (c a) * (if B l = esI k r a then (1 : ℂ) else 0) := by
  ext a l
  simp only [Matrix.of_apply]
  rw [castLE_self, inv_e hc hg a]
  simp [bvec, Pi.single_apply]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro j _`. Use linear arithmetic over natural numbers and integers. Consider the case `succ m ih`.

Introduce `j hj`. Establish `hm : m < n` using `by have := j.isLt; omega`. Establish `h1` using `ih ⟨m, hm⟩ rfl`. Establish `h2 : τ ⟨m, hm⟩ < τ j` using `h (by rw [Fin.lt_def]; simp only; omega)`. Rewrite `h2` using `[Fin.lt_def]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem sm_ge {n : ℕ} {τ : Fin n → Fin n} (h : StrictMono τ) : ∀ m (j : Fin n), j.val = m → m ≤ (τ j).val := by
  intro m
  induction m with
  | zero => intro j _; omega
  | succ m ih =>
    intro j hj
    have hm : m < n := by have := j.isLt; omega
    have h1 := ih ⟨m, hm⟩ rfl
    have h2 : τ ⟨m, hm⟩ < τ j := h (by rw [Fin.lt_def]; simp only; omega)
    rw [Fin.lt_def] at h2
    omega

/- English proof (translation)
Establish `hρ : StrictMono fun j : Fin n => Fin.rev (τ (Fin.rev j))`. Introduce `a b hab`. Rewrite using `[Fin.rev_lt_rev]`. Conclude with `h (Fin.rev_lt_rev.2 hab)`. Use function extensionality and compare the values at `j`.

Apply `Fin.ext` to reduce the goal to its premises. Establish `e1` using `sm_ge h j.val j rfl`. Establish `e2` using `sm_ge hρ (Fin.rev j).val (Fin.rev j) rfl`. Simplify using `only [Fin.rev_rev, Fin.val_rev] at e2`. Use `j.isLt` as an intermediate fact.

Use `(τ j).isLt` as an intermediate fact. Simplify using `only [id]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sm_eq_id {n : ℕ} {τ : Fin n → Fin n} (h : StrictMono τ) : τ = id := by
  have hρ : StrictMono fun j : Fin n => Fin.rev (τ (Fin.rev j)) := by
    intro a b hab
    rw [Fin.rev_lt_rev]
    exact h (Fin.rev_lt_rev.2 hab)
  funext j
  apply Fin.ext
  have e1 := sm_ge h j.val j rfl
  have e2 := sm_ge hρ (Fin.rev j).val (Fin.rev j) rfl
  simp only [Fin.rev_rev, Fin.val_rev] at e2
  have := j.isLt
  have := (τ j).isLt
  simp only [id]
  omega

/- English proof (translation)
Apply the tactic sequence `rw [det_entry hc hg B]`. Distinguish the cases in `hcol : ∃ l, ∀ a, B l ≠ esI k r a`. Take `⟨l, hl⟩` from `hcol`. Conclude with `Matrix.det_eq_zero_of_column_eq_zero l (fun a => by simp [hl a])`. Use `push Not at hcol choose τ hτ using hcol`.

Establish `hτm : StrictMono τ`. Introduce `a b hab`. Use `hm hab` as an intermediate fact. Simplify using `only [hτ, keyS_esI] at this`. Conclude with `Fin.lt_def.2 this`.

Establish `hid` using `sm_eq_id hτm`. Conclude with `absurd (funext fun l => by rw [hτ l, hid]; rfl) hB`.
-/
theorem det_zero {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r))
    (B : Fin r → Fin (2 * r + k + 1)) (hm : StrictMono fun l => C3.keyS k r (B l)) (hB : B ≠ C3.sR k r r le_rfl) :
    (Matrix.of fun a l : Fin r =>
        ((Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)).det = 0 := by
  rw [det_entry hc hg B]
  by_cases hcol : ∃ l, ∀ a, B l ≠ esI k r a
  · obtain ⟨l, hl⟩ := hcol
    exact Matrix.det_eq_zero_of_column_eq_zero l (fun a => by simp [hl a])
  · push Not at hcol
    choose τ hτ using hcol
    have hτm : StrictMono τ := by
      intro a b hab
      have := hm hab
      simp only [hτ, keyS_esI] at this
      exact Fin.lt_def.2 this
    have hid := sm_eq_id hτm
    exact absurd (funext fun l => by rw [hτ l, hid]; rfl) hB

/- English proof (translation)
Apply the tactic sequence `rw [det_entry hc hg]`. Establish `e : (Matrix.of fun a l : Fin r => star (c a) * (if C3.sR k r r le_rfl l = esI k r a then (1 : ℂ) else 0)) = Matrix.diagonal fun a => star (c a)`. Use extensionality with `a l`. Simplify using `only [Matrix.of_apply, Matrix.diagonal_apply, C3.sR, castLE_self, esI_inj]`. Distinguish the cases in `h : a = l`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Rewrite using `[e, Matrix.det_diagonal]`. Simplify using `[drbF, map_prod]`.
-/
theorem det_sR {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) :
    (Matrix.of fun a l : Fin r =>
        ((Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (C3.sR k r r le_rfl l)).det =
      drbF r c := by
  rw [det_entry hc hg]
  have e : (Matrix.of fun a l : Fin r => star (c a) * (if C3.sR k r r le_rfl l = esI k r a then (1 : ℂ) else 0)) =
      Matrix.diagonal fun a => star (c a) := by
    ext a l
    simp only [Matrix.of_apply, Matrix.diagonal_apply, C3.sR, castLE_self, esI_inj]
    by_cases h : a = l
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [e, Matrix.det_diagonal]
  simp [drbF, map_prod]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Apply `Fin.ext` to reduce the goal to its premises. Use `j.isLt` as an intermediate fact. Simplify using `[colsVm, C3.sR, esI, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.
-/
theorem colsVm_eq : colsVm k r r = C3.sR k r r le_rfl ∘ Fin.revPerm := by
  funext j
  apply Fin.ext
  have := j.isLt
  simp [colsVm, C3.sR, esI, Fin.val_rev]
  omega

/- English proof (translation)
Unfold `kvM`. Rewrite using `[colsVm_eq, Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.skewRow, Formalism.FourierDecayAlt.P.FourTermExpansion.skewCol (C3.sR k r r le_rfl) w J x hx hloc, smul_smul, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_smul]`.
-/
theorem kv_rev {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : Q.Mx k r} (hx : x ∈ B.GV k r)
    {J : Q.Mx k r → E} (hloc : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ((r : ℕ) : ℕ∞) J x) (w : ℂ) :
    kvM k r r w J x = qminorOp (Q.EH k r) (C3.sR k r r le_rfl) (C3.sR k r r le_rfl) w J x := by
  unfold kvM
  rw [colsVm_eq, Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.skewRow, Formalism.FourierDecayAlt.P.FourTermExpansion.skewCol (C3.sR k r r le_rfl) w J x hx hloc, smul_smul,
    ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_smul]

/- English proof (translation)
Rewrite using `[kv_rev hx hloc, ← det_sR hc hg]`. Simplify using `only [capAv, C3.AAvop]`. Rewrite using `[Fintype.sum_eq_single (C3.sR k r r le_rfl)]`. Establish `hmono : StrictMono fun l => C3.keyS k r (C3.sR k r r le_rfl l)`. Introduce `a b hab`.

Simplify using `only [C3.sR, castLE_self, keyS_esI]`. Conclude with `hab`. Rewrite using `[if_pos hmono]`. Both sides reduce to the same expression. Introduce `B hB split_ifs with hm`.

Rewrite using `[det_zero hc hg B hm hB, zero_smul]`. Both sides reduce to the same expression.
-/
theorem coef_gen {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) (hx : Q.wCell k r (Fin.last r) c * g ∈ B.GV k r)
    {J : Q.Mx k r → E} (hloc : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ((r : ℕ) : ℕ∞) J (Q.wCell k r (Fin.last r) c * g)) (y : ℂ) :
    capAv k r y J (Q.wCell k r (Fin.last r) c * g) =
      drbF r c • kvM k r r (kvTop k r y) J (Q.wCell k r (Fin.last r) c * g) := by
  rw [kv_rev hx hloc, ← det_sR hc hg]
  simp only [capAv, C3.AAvop]
  rw [Fintype.sum_eq_single (C3.sR k r r le_rfl)]
  · have hmono : StrictMono fun l => C3.keyS k r (C3.sR k r r le_rfl l) := by
      intro a b hab
      simp only [C3.sR, castLE_self, keyS_esI]
      exact hab
    rw [if_pos hmono]
    rfl
  · intro B hB
    split_ifs with hm
    · rw [det_zero hc hg B hm hB, zero_smul]
    · rfl

end TVCoefPf

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg`. Take `⟨hGV, hCk⟩` from `capa_J_ck P Bs hJ hc hg hcg ((P.r : ℕ) : ℕ∞)`. Conclude with `TVCoefPf.coef_gen hc hg hGV (hCk _ (Set.mem_singleton _)) y`.
-/
theorem toda_coefficient_holds : TVCoef := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg
  obtain ⟨hGV, hCk⟩ := capa_J_ck P Bs hJ hc hg hcg ((P.r : ℕ) : ℕ∞)
  exact TVCoefPf.coef_gen hc hg hGV (hCk _ (Set.mem_singleton _)) y

end

end Formalism.FourierDecayAlt.P.CutMP
