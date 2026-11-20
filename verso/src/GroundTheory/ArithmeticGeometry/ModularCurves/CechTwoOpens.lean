import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor

open CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

namespace GroundTheory.Arith.Modular

section TwoOpens

variable {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : Fin 2 → Opens X)

abbrev i01 : Fin 2 → Fin 2 := ![0, 1]

noncomputable def twoDiff : Cochain P U 0 →+ P.obj (op (inter U i01)) :=
  (Pi.evalAddMonoidHom (fun i => P.obj (op (inter U i))) i01).comp (d P U 0)

abbrev TwoQuot : Type u := P.obj (op (inter U i01)) ⧸ (twoDiff P U).range

noncomputable def cocycleToQuot : cocycles P U 1 →+ TwoQuot P U :=
  (QuotientAddGroup.mk' _).comp
    ((Pi.evalAddMonoidHom (fun i => P.obj (op (inter U i))) i01).comp (cocycles P U 1).subtype)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma cocycleToQuot_apply (σ : cocycles P U 1) :
    cocycleToQuot P U σ = QuotientAddGroup.mk ((σ : Cochain P U 1) i01) := rfl

noncomputable def cechOneToQuot : cechH P U 1 →+ TwoQuot P U :=
  QuotientAddGroup.lift _ (cocycleToQuot P U) (by
    rintro ⟨σ, hσ⟩ hb
    rw [AddSubgroup.mem_addSubgroupOf, coboundaries_succ] at hb
    obtain ⟨τ, rfl⟩ := hb
    rw [AddMonoidHom.mem_ker, cocycleToQuot_apply, QuotientAddGroup.eq_zero_iff]
    exact ⟨τ, rfl⟩)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma cechOneToQuot_cls (σ : Cochain P U 1) (hσ : d P U 1 σ = 0) :
    cechOneToQuot P U (cls σ hσ) = QuotientAddGroup.mk (σ i01) := rfl

end TwoOpens

section TwoOpens2

variable {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : Fin 2 → Opens X)

/- English proof (translation)
Introduce `x y hxy`. Use `congrArg (res P h') hxy` as an intermediate fact. Rewrite `this` using `[res_res, res_res, res_refl, res_refl]`. Then use the resulting hypothesis.
-/
lemma res_injective_of_le {V W : Opens X} (h : V ≤ W) (h' : W ≤ V) :
    Function.Injective (res P h) := by
  intro x y hxy
  have := congrArg (res P h') hxy
  rwa [res_res, res_res, res_refl, res_refl] at this

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
lemma res_cochain_congr {n : ℕ} (σ : Cochain P U n) {V : Opens X} {i i' : Fin (n + 1) → Fin 2}
    (e : i = i') (h : V ≤ inter U i) (h' : V ≤ inter U i') : res P h (σ i) = res P h' (σ i') := by
  subst e
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Apply the tactic sequence `fin_cases x <;> rfl`.
-/
lemma vec2_eq (i : Fin 2 → Fin 2) : i = ![i 0, i 1] := by
  funext x
  fin_cases x <;> rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Apply the tactic sequence `fin_cases x <;> rfl`.
-/
lemma vec3_eq (j : Fin 3 → Fin 2) : j = ![j 0, j 1, j 2] := by
  funext x
  fin_cases x <;> rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Apply the tactic sequence `fin_cases x <;> rfl`.
-/
lemma comp_succAbove_zero (a b c : Fin 2) : ![a, b, c] ∘ Fin.succAbove 0 = ![b, c] := by
  funext x
  fin_cases x <;> rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Apply the tactic sequence `fin_cases x <;> rfl`.
-/
lemma comp_succAbove_one (a b c : Fin 2) : ![a, b, c] ∘ Fin.succAbove 1 = ![a, c] := by
  funext x
  fin_cases x <;> rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Apply the tactic sequence `fin_cases x <;> rfl`.
-/
lemma comp_succAbove_two (a b c : Fin 2) : ![a, b, c] ∘ Fin.succAbove 2 = ![a, b] := by
  funext x
  fin_cases x <;> rfl

/- English proof (translation)
Rewrite using `[d_apply, Fin.sum_univ_three]`. Rewrite using `[res_cochain_congr P U σ (comp_succAbove_zero a b c) _ (by rw [← comp_succAbove_zero a b c]; exact inter_le_comp U _ _), res_cochain_congr P U σ (comp_succAbove_one a b c) _ (by rw [← comp_succAbove_one a b c]; exact inter_le_comp U _ _), res_cochain_congr P U σ (comp_succAbove_t …`. Simplify using `only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, Fin.val_two]`. Normalize the expressions using the abelian group laws.
-/
lemma d_one_apply (σ : Cochain P U 1) (a b c : Fin 2) :
    d P U 1 σ ![a, b, c] =
      res P (by rw [← comp_succAbove_zero a b c]; exact inter_le_comp U _ _) (σ ![b, c]) -
        res P (by rw [← comp_succAbove_one a b c]; exact inter_le_comp U _ _) (σ ![a, c]) +
        res P (by rw [← comp_succAbove_two a b c]; exact inter_le_comp U _ _) (σ ![a, b]) := by
  rw [d_apply, Fin.sum_univ_three]
  rw [res_cochain_congr P U σ (comp_succAbove_zero a b c) _
      (by rw [← comp_succAbove_zero a b c]; exact inter_le_comp U _ _),
    res_cochain_congr P U σ (comp_succAbove_one a b c) _
      (by rw [← comp_succAbove_one a b c]; exact inter_le_comp U _ _),
    res_cochain_congr P U σ (comp_succAbove_two a b c) _
      (by rw [← comp_succAbove_two a b c]; exact inter_le_comp U _ _)]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, Fin.val_two]
  abel

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[mem_inter_iff]`. Introduce `a`. Take `⟨b, hb⟩` from `h a`. Rewrite using `[← hb]`.

Conclude with `hx b`.
-/
lemma inter_le_inter_of_forall {m n : ℕ} (i : Fin m → Fin 2) (i' : Fin n → Fin 2)
    (h : ∀ a, ∃ b, i b = i' a) : inter U i ≤ inter U i' := by
  intro x hx
  rw [mem_inter_iff] at hx ⊢
  intro a
  obtain ⟨b, hb⟩ := h a
  rw [← hb]
  exact hx b

variable {P U}

/- English proof (translation)
Establish `h` using `congrFun hσ ![c, c, c]`. Rewrite `h` using `[d_one_apply, sub_self, zero_add]`. Apply the tactic sequence `exact res_injective_of_le P _ (inter_le_inter_of_forall U _ _ (fun a => ⟨0, by fin_cases a <;> rfl⟩)) (h.trans (map_zero _).symm)`.
-/
lemma cocycle_diag {σ : Cochain P U 1} (hσ : d P U 1 σ = 0) (c : Fin 2) : σ ![c, c] = 0 := by
  have h := congrFun hσ ![c, c, c]
  rw [d_one_apply, sub_self, zero_add] at h
  exact res_injective_of_le P _ (inter_le_inter_of_forall U _ _ (fun a => ⟨0, by fin_cases a <;> rfl⟩))
    (h.trans (map_zero _).symm)

/- English proof (translation)
Establish `h` using `congrFun hσ ![0, 1, 0]`. Rewrite `h` using `[d_one_apply, cocycle_diag hσ 0, map_zero, sub_zero]`. Express the relevant statement in the definitionally equal form `_ + res P _ (σ i01) = 0 at h`. Rewrite `h` using `[h01, map_zero, add_zero]`. Conclude with `res_injective_of_le P _ (inter_le_inter_of_forall U _ _ (fun a => by fin_cases a`.

Conclude with `⟨1, rfl⟩`. Conclude with `⟨0, rfl⟩`. Conclude with `⟨1, rfl⟩)) (h.trans (map_zero _).symm)`.
-/
lemma cocycle_swap {σ : Cochain P U 1} (hσ : d P U 1 σ = 0) (h01 : σ i01 = 0) : σ ![1, 0] = 0 := by
  have h := congrFun hσ ![0, 1, 0]
  rw [d_one_apply, cocycle_diag hσ 0, map_zero, sub_zero] at h
  change _ + res P _ (σ i01) = 0 at h
  rw [h01, map_zero, add_zero] at h
  exact res_injective_of_le P _ (inter_le_inter_of_forall U _ _ (fun a => by
    fin_cases a
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩)) (h.trans (map_zero _).symm)

variable (P U)

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Proceed by induction on `x using QuotientAddGroup.induction_on with`. Consider the case `H σ`. Take `⟨σ, hσ⟩` from `σ`.

Take `⟨τ, hτ⟩` from `(QuotientAddGroup.eq_zero_iff _).1 hx`. Apply `(QuotientAddGroup.eq_zero_iff _).2` to reduce the goal to its premises. Rewrite using `[AddSubgroup.mem_addSubgroupOf, coboundaries_succ]`. Use `⟨τ, ?_⟩` and prove the remaining obligations. Establish `hσ' : d P U 1 (σ - d P U 0 τ) = 0`.

Rewrite using `[map_sub, (mem_cocycles _).1 hσ, d_d, sub_zero]`. Establish `h01 : (σ - d P U 0 τ) i01 = 0`. Express the relevant statement in the definitionally equal form `σ i01 - twoDiff P U τ = 0`. Rewrite using `[hτ]`. Conclude with `sub_self _`.

It suffices to establish `h : σ - d P U 0 τ = 0 from (sub_eq_zero.1 h).symm`. Use function extensionality and compare the values at `i`. Take `⟨a, b, rfl⟩ : ∃ a b, i = ![a, b]` from `⟨_, _, vec2_eq i⟩`. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Conclude with `cocycle_diag hσ' 0`.

Conclude with `h01`. Conclude with `cocycle_swap hσ' h01`. Conclude with `cocycle_diag hσ' 1`.
-/
theorem cechOneToQuot_injective : Function.Injective (cechOneToQuot P U) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H σ =>
  obtain ⟨σ, hσ⟩ := σ
  obtain ⟨τ, hτ⟩ := (QuotientAddGroup.eq_zero_iff _).1 hx
  apply (QuotientAddGroup.eq_zero_iff _).2
  rw [AddSubgroup.mem_addSubgroupOf, coboundaries_succ]
  refine ⟨τ, ?_⟩
  have hσ' : d P U 1 (σ - d P U 0 τ) = 0 := by
    rw [map_sub, (mem_cocycles _).1 hσ, d_d, sub_zero]
  have h01 : (σ - d P U 0 τ) i01 = 0 := by
    change σ i01 - twoDiff P U τ = 0
    rw [hτ]
    exact sub_self _
  suffices h : σ - d P U 0 τ = 0 from (sub_eq_zero.1 h).symm
  funext i
  obtain ⟨a, b, rfl⟩ : ∃ a b, i = ![a, b] := ⟨_, _, vec2_eq i⟩
  fin_cases a <;> fin_cases b
  · exact cocycle_diag hσ' 0
  · exact h01
  · exact cocycle_swap hσ' h01
  · exact cocycle_diag hσ' 1

end TwoOpens2

section TwoOpens3

variable {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : Fin 2 → Opens X)

/- English proof (translation)
Establish `hi : ∀ a : Fin 2, a = i 0 ∨ a = i 1`. Introduce `a`. Use `revert h`. Generalize the expression as in `i 0 = p`. Generalize the expression as in `i 1 = q`.

Apply the tactic sequence `fin_cases a <;> fin_cases p <;> fin_cases q <;> simp`. Conclude with `inter_le_inter_of_forall U _ _ (fun a => (hi (i01 a)).elim (fun e => ⟨0, e.symm⟩) (fun e => ⟨1, e.symm⟩))`.
-/
lemma inter_le_inter_zero_one {i : Fin 2 → Fin 2} (h : i 0 ≠ i 1) : inter U i ≤ inter U i01 := by
  have hi : ∀ a : Fin 2, a = i 0 ∨ a = i 1 := by
    intro a
    revert h
    generalize i 0 = p
    generalize i 1 = q
    fin_cases a <;> fin_cases p <;> fin_cases q <;> simp
  exact inter_le_inter_of_forall U _ _ (fun a =>
    (hi (i01 a)).elim (fun e => ⟨0, e.symm⟩) (fun e => ⟨1, e.symm⟩))

open Classical in

noncomputable def twoCochain (s : P.obj (op (inter U i01))) : Cochain P U 1 := fun i =>
  if h : i 0 = i 1 then 0 else
    if i 0 = 0 then res P (inter_le_inter_zero_one U h) s else -res P (inter_le_inter_zero_one U h) s

/- English proof (translation)
Use function extensionality and compare the values at `j`. Take `⟨a, b, c, rfl⟩ : ∃ a b c, j = ![a, b, c]` from `⟨_, _, _, vec3_eq j⟩`. Rewrite using `[d_one_apply]`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> fin_cases c <;>`. Simplify using `[twoCochain, res_res]`.
-/
theorem d_twoCochain (s : P.obj (op (inter U i01))) : d P U 1 (twoCochain P U s) = 0 := by
  funext j
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, j = ![a, b, c] := ⟨_, _, _, vec3_eq j⟩
  rw [d_one_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [twoCochain, res_res]

/- English proof (translation)
Simplify using `[twoCochain]`.
-/
theorem twoCochain_zero_one (s : P.obj (op (inter U i01))) : twoCochain P U s i01 = s := by
  simp [twoCochain]

/- English proof (translation)
Introduce `q`. Proceed by induction on `q using QuotientAddGroup.induction_on with`. Consider the case `H s`. Conclude with `⟨cls (twoCochain P U s) (d_twoCochain P U s), by`. Rewrite using `[cechOneToQuot_cls, twoCochain_zero_one]⟩`.
-/
theorem cechOneToQuot_surjective : Function.Surjective (cechOneToQuot P U) := by
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H s =>
  exact ⟨cls (twoCochain P U s) (d_twoCochain P U s), by
    rw [cechOneToQuot_cls, twoCochain_zero_one]⟩

noncomputable def cechOneEquiv : cechH P U 1 ≃+ TwoQuot P U :=
  AddEquiv.ofBijective (cechOneToQuot P U)
    ⟨cechOneToQuot_injective P U, cechOneToQuot_surjective P U⟩

variable {P} in

noncomputable def twoQuotMap {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') :
    TwoQuot P U →+ TwoQuot P' U :=
  QuotientAddGroup.map _ _ (φ.app (op (inter U i01))).hom (by
    rintro _ ⟨τ, rfl⟩
    refine ⟨push U φ 0 τ, ?_⟩
    change (d P' U 0 (push U φ 0 τ)) i01 = φ.app _ ((d P U 0 τ) i01)
    rw [← push_d]
    rfl)

end TwoOpens3

end GroundTheory.Arith.Modular
