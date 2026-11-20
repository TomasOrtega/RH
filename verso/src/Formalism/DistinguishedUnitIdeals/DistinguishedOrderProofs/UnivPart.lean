import Mathlib
import Formalism.DistinguishedUnitIdeals.UnivPart

noncomputable section

namespace Formalism.ExponentWindows

open Module

section Lattice

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} {r : ℕ}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using h`. Consider the case `succ n ih`. Apply `ih` to reduce the goal to its premises. Apply `hS` to reduce the goal to its premises.

Rewrite using `[smul_smul, ← pow_succ']`. Conclude with `h`.
-/
lemma mem_of_pow_smul_mem (S : Submodule O (Fin r → O)) (hS : ∀ v : Fin r → O, ϖ • v ∈ S → v ∈ S)
    (n : ℕ) (v : Fin r → O) (h : ϖ ^ n • v ∈ S) : v ∈ S := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply hS
    rw [smul_smul, ← pow_succ']
    exact h

/- English proof (translation)
Establish `hnz : ∀ (c : O) (v : Fin r → O), c ≠ 0 → c • v ∈ S → v ∈ S`. Introduce `c v hc hcv`. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hc hϖ`. Take `⟨u, hu⟩` from `hn`. Apply `mem_of_pow_smul_mem S hS n v` to reduce the goal to its premises.

Rewrite using `[← hu, mul_comm, mul_smul]`. Conclude with `S.smul_mem _ hcv`. Prove the components needed by the constructor for the conclusion. Introduce `c hc x y hxy`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Simplify using `only [← Submodule.Quotient.mk_smul] at hxy`. Rewrite `hxy`, the goal using `[Submodule.Quotient.eq]`. Rewrite `hxy` using `[← smul_sub]`. Conclude with `hnz c _ hc.ne_zero hxy`.
-/
lemma quotient_isTorsionFree (hϖ : Irreducible ϖ) (S : Submodule O (Fin r → O))
    (hS : ∀ v : Fin r → O, ϖ • v ∈ S → v ∈ S) : IsTorsionFree O ((Fin r → O) ⧸ S) := by
  have hnz : ∀ (c : O) (v : Fin r → O), c ≠ 0 → c • v ∈ S → v ∈ S := by
    intro c v hc hcv
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc hϖ
    obtain ⟨u, hu⟩ := hn
    apply mem_of_pow_smul_mem S hS n v
    rw [← hu, mul_comm, mul_smul]
    exact S.smul_mem _ hcv
  constructor
  intro c hc x y hxy
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [← Submodule.Quotient.mk_smul] at hxy
  rw [Submodule.Quotient.eq] at hxy ⊢
  rw [← smul_sub] at hxy
  exact hnz c _ hc.ne_zero hxy

/- English proof (translation)
Use `quotient_isTorsionFree hϖ S hS` as an intermediate fact. Establish `: Module.Free O ((Fin r → O) ⧸ S)` using `Module.free_of_finite_type_torsion_free'`. Take `⟨h, hh⟩` from `Module.projective_lifting_property S.mkQ (LinearMap.id) S.mkQ_surjective`. Use `⟨LinearMap.range h, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`.

Introduce and unpack `x hxS ⟨q, rfl⟩`. Establish `hq : q = 0`. Use `LinearMap.congr_fun hh q` as an intermediate fact. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this`. Rewrite using `[← this, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Conclude with `hxS`. Simplify using `[hq]`. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `x _`. Establish `hx : x - h (S.mkQ x) ∈ S`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply]`. Use `LinearMap.congr_fun hh (S.mkQ x)` as an intermediate fact. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this`. Rewrite using `[this, sub_self]`. Establish `: x = (x - h (S.mkQ x)) + h (S.mkQ x)` using `by abel`.

Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup hx (LinearMap.mem_range_self h _)`.
-/
lemma exists_isCompl_of_saturated (hϖ : Irreducible ϖ) (S : Submodule O (Fin r → O))
    (hS : ∀ v : Fin r → O, ϖ • v ∈ S → v ∈ S) : ∃ Q : Submodule O (Fin r → O), IsCompl S Q := by
  have := quotient_isTorsionFree hϖ S hS
  have : Module.Free O ((Fin r → O) ⧸ S) := Module.free_of_finite_type_torsion_free'
  obtain ⟨h, hh⟩ := Module.projective_lifting_property S.mkQ (LinearMap.id) S.mkQ_surjective
  refine ⟨LinearMap.range h, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hxS ⟨q, rfl⟩
    have hq : q = 0 := by
      have := LinearMap.congr_fun hh q
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
      rw [← this, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hxS
    simp [hq]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x - h (S.mkQ x) ∈ S := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← Submodule.mkQ_apply,
        ← Submodule.mkQ_apply]
      have := LinearMap.congr_fun hh (S.mkQ x)
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
      rw [this, sub_self]
    have : x = (x - h (S.mkQ x)) + h (S.mkQ x) := by abel
    rw [this]
    exact Submodule.add_mem_sup hx (LinearMap.mem_range_self h _)

def saturation (ϖ : O) (T : Submodule O (Fin r → O)) : Submodule O (Fin r → O) where
  carrier := {v | ∃ n : ℕ, ϖ ^ n • v ∈ T}
  add_mem' := by
    rintro v w ⟨n, hn⟩ ⟨k, hk⟩
    refine ⟨n + k, ?_⟩
    rw [smul_add, pow_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, ← smul_smul]; exact T.smul_mem _ hn
    · rw [← smul_smul]; exact T.smul_mem _ hk
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c v ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [smul_comm]
    exact T.smul_mem c hn

/- English proof (translation)
Introduce `v hv` and use `show ∃ n : ℕ, ϖ ^ n • v ∈ T from ⟨0, by rwa [pow_zero, one_smul]⟩`.
-/
lemma le_saturation (T : Submodule O (Fin r → O)) : T ≤ saturation ϖ T := fun v hv => show ∃ n : ℕ, ϖ ^ n • v ∈ T from ⟨0, by rwa [pow_zero, one_smul]⟩

/- English proof (translation)
Take `⟨n, hn⟩ : ∃ n : ℕ, ϖ ^ n • ϖ • v ∈ T` from `h`. Conclude with `show ∃ n : ℕ, ϖ ^ n • v ∈ T from ⟨n + 1, by rwa [pow_succ, mul_smul]⟩`.
-/
lemma saturation_saturated (T : Submodule O (Fin r → O)) (v : Fin r → O)
    (h : ϖ • v ∈ saturation ϖ T) : v ∈ saturation ϖ T := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ϖ ^ n • ϖ • v ∈ T := h
  exact show ∃ n : ℕ, ϖ ^ n • v ∈ T from ⟨n + 1, by rwa [pow_succ, mul_smul]⟩

/- English proof (translation)
Establish `hle : T ≤ saturation ϖ T` using `le_saturation T`. Establish `htor : Module.rank O ((saturation ϖ T) ⧸ T.comap (saturation ϖ T).subtype) = 0`. Rewrite using `[rank_eq_zero_iff]`. Introduce `x`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Take `⟨n, hn⟩ : ∃ n : ℕ, ϖ ^ n • (v : Fin r → O) ∈ T` from `v.2`. Use `⟨ϖ ^ n, pow_ne_zero n hϖ.ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `hn`. Establish `h : Module.rank O ((saturation ϖ T) ⧸ T.comap (saturation ϖ T).subtype) + Module.rank O (T.comap (saturation ϖ T).subtype) = Module.rank O (saturation ϖ T)` using `by first`.

Consider the case `exact HasRankNullity.rank_quotient_add_rank _`. Consider the case `exact Submodule.rank_quotient_add_rank _`. Consider the case `exact rank_quotient_add_rank_of_divisionRing _`. Rewrite `h` using `[htor, zero_add, (Submodule.comapSubtypeEquivOfLe hle).rank_eq]`. Conclude with `le_of_eq (congrArg Cardinal.toNat h.symm)`.
-/
lemma finrank_saturation_le (hϖ : Irreducible ϖ) (T : Submodule O (Fin r → O)) :
    finrank O (saturation ϖ T) ≤ finrank O T := by
  have hle : T ≤ saturation ϖ T := le_saturation T
  have htor : Module.rank O ((saturation ϖ T) ⧸ T.comap (saturation ϖ T).subtype) = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ϖ ^ n • (v : Fin r → O) ∈ T := v.2
    refine ⟨ϖ ^ n, pow_ne_zero n hϖ.ne_zero, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hn
  have h : Module.rank O ((saturation ϖ T) ⧸ T.comap (saturation ϖ T).subtype) +
      Module.rank O (T.comap (saturation ϖ T).subtype) = Module.rank O (saturation ϖ T) := by
    first
      | exact HasRankNullity.rank_quotient_add_rank _
      | exact Submodule.rank_quotient_add_rank _
      | exact rank_quotient_add_rank_of_divisionRing _
  rw [htor, zero_add, (Submodule.comapSubtypeEquivOfLe hle).rank_eq] at h
  exact le_of_eq (congrArg Cardinal.toNat h.symm)

/- English proof (translation)
Establish `h` using `congrArg Cardinal.toNat (Submodule.rank_sup_add_rank_inf_eq s t)`. Rewrite `h` using `[Cardinal.toNat_add (Module.rank_lt_aleph0 _ _) (Module.rank_lt_aleph0 _ _), Cardinal.toNat_add (Module.rank_lt_aleph0 _ _) (Module.rank_lt_aleph0 _ _)]`. Then use the resulting hypothesis.
-/
lemma finrank_sup_add_finrank_inf (s t : Submodule O (Fin r → O)) :
    finrank O ↥(s ⊔ t) + finrank O ↥(s ⊓ t) = finrank O s + finrank O t := by
  have h := congrArg Cardinal.toNat (Submodule.rank_sup_add_rank_inf_eq s t)
  rwa [Cardinal.toNat_add (Module.rank_lt_aleph0 _ _) (Module.rank_lt_aleph0 _ _),
    Cardinal.toNat_add (Module.rank_lt_aleph0 _ _) (Module.rank_lt_aleph0 _ _)] at h

/- English proof (translation)
Conclude with `(Submodule.finrank_le s).trans (Module.finrank_fin_fun O).le`.
-/
lemma finrank_submodule_le (s : Submodule O (Fin r → O)) : finrank O s ≤ r := by
  exact (Submodule.finrank_le s).trans (Module.finrank_fin_fun O).le

/- English proof (translation)
Use `revert hC`. Use `Finset.induction_on Up ?_ ?_` and prove the remaining obligations. Introduce `_`. Establish `h : (⨅ s ∈ (∅ : Finset ℕ), C s) = ⊤` using `eq_top_iff.2 (le_iInf₂ fun s hs => absurd hs (by simp))`. Simplify using `only [Finset.card_empty, mul_zero, add_zero]`.

Apply the tactic sequence `(rw [h, finrank_top, Module.finrank_fin_fun]) <;> exact le_rfl`. Introduce `a s ha ih hC`. Establish `ih'` using `ih (fun t ht => hC t (Finset.mem_insert_of_mem ht))`. Establish `hCa` using `hC a (Finset.mem_insert_self a s)`. Rewrite using `[Finset.iInf_insert]`.

Establish `key` using `finrank_sup_add_finrank_inf (C a) (⨅ t ∈ s, C t)`. Establish `hle` using `finrank_submodule_le (C a ⊔ ⨅ t ∈ s, C t)`. Establish `e : (insert a s).card = s.card + 1` using `by first`. Consider the case `exact Finset.card_insert_of_not_mem ha`. Consider the case `exact Finset.card_insert_of_notMem ha`.

Rewrite using `[e, Nat.mul_succ]`. Apply the tactic sequence `first | omega | linarith`.
-/
lemma finrank_iInf_ge (m : ℕ) (C : ℕ → Submodule O (Fin r → O)) (Up : Finset ℕ)
    (hC : ∀ s ∈ Up, r ≤ finrank O (C s) + m) :
    r ≤ finrank O ↥(⨅ s ∈ Up, C s) + m * Up.card := by
  revert hC
  refine Finset.induction_on Up ?_ ?_
  · intro _
    have h : (⨅ s ∈ (∅ : Finset ℕ), C s) = ⊤ :=
      eq_top_iff.2 (le_iInf₂ fun s hs => absurd hs (by simp))
    simp only [Finset.card_empty, mul_zero, add_zero]
    (rw [h, finrank_top, Module.finrank_fin_fun]) <;> exact le_rfl
  · intro a s ha ih hC
    have ih' := ih (fun t ht => hC t (Finset.mem_insert_of_mem ht))
    have hCa := hC a (Finset.mem_insert_self a s)
    rw [Finset.iInf_insert]
    have key := finrank_sup_add_finrank_inf (C a) (⨅ t ∈ s, C t)
    have hle := finrank_submodule_le (C a ⊔ ⨅ t ∈ s, C t)
    have e : (insert a s).card = s.card + 1 := by
      first
        | exact Finset.card_insert_of_not_mem ha
        | exact Finset.card_insert_of_notMem ha
    rw [e, Nat.mul_succ]
    first | omega | linarith

/- English proof (translation)
Use `revert hF`. Use `Finset.induction_on Dn ?_ ?_` and prove the remaining obligations. Introduce `_`. Establish `h : (⨆ s ∈ (∅ : Finset ℕ), F s) = ⊥` using `eq_bot_iff.2 (iSup₂_le fun s hs => absurd hs (by simp))`. Simplify using `only [Finset.card_empty, mul_zero, add_zero]`.

Apply the tactic sequence `(rw [h, sup_bot_eq]) <;> exact le_rfl`. Introduce `a s ha ih hF`. Establish `ih'` using `ih (fun t ht => hF t (Finset.mem_insert_of_mem ht))`. Establish `hFa` using `hF a (Finset.mem_insert_self a s)`. Rewrite using `[Finset.iSup_insert, sup_comm (F a), ← sup_assoc]`.

Establish `key` using `finrank_sup_add_finrank_inf (L ⊔ ⨆ t ∈ s, F t) (F a)`. Establish `e : (insert a s).card = s.card + 1` using `by first`. Consider the case `exact Finset.card_insert_of_not_mem ha`. Consider the case `exact Finset.card_insert_of_notMem ha`. Rewrite using `[e, Nat.mul_succ]`.

Apply the tactic sequence `first | omega | linarith`.
-/
lemma finrank_sup_iSup_le (m : ℕ) (L : Submodule O (Fin r → O)) (F : ℕ → Submodule O (Fin r → O))
    (Dn : Finset ℕ) (hF : ∀ s ∈ Dn, finrank O (F s) ≤ m) :
    finrank O ↥(L ⊔ ⨆ s ∈ Dn, F s) ≤ finrank O L + m * Dn.card := by
  revert hF
  refine Finset.induction_on Dn ?_ ?_
  · intro _
    have h : (⨆ s ∈ (∅ : Finset ℕ), F s) = ⊥ :=
      eq_bot_iff.2 (iSup₂_le fun s hs => absurd hs (by simp))
    simp only [Finset.card_empty, mul_zero, add_zero]
    (rw [h, sup_bot_eq]) <;> exact le_rfl
  · intro a s ha ih hF
    have ih' := ih (fun t ht => hF t (Finset.mem_insert_of_mem ht))
    have hFa := hF a (Finset.mem_insert_self a s)
    rw [Finset.iSup_insert, sup_comm (F a), ← sup_assoc]
    have key := finrank_sup_add_finrank_inf (L ⊔ ⨆ t ∈ s, F t) (F a)
    have e : (insert a s).card = s.card + 1 := by
      first
        | exact Finset.card_insert_of_not_mem ha
        | exact Finset.card_insert_of_notMem ha
    rw [e, Nat.mul_succ]
    first | omega | linarith

end Lattice

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ r m Up Dn C F hCs hFs hCr hFr`. Use `set W : Submodule O (Fin r → O) := ⨅ s ∈ Up, C s with hWdef`. Establish `hWmem : ∀ v, v ∈ W ↔ ∀ s ∈ Up, v ∈ C s`. Introduce `v`. Simplify using `[W, Submodule.mem_iInf]`.

Establish `hWsat : ∀ v : Fin r → O, ϖ • v ∈ W → v ∈ W`. Introduce `v hv`. Rewrite `hv`, the goal using `[hWmem]`. Conclude with `fun s hs => hCs s hs v (hv s hs)`. Take `⟨L₂, hL₂⟩` from `exists_isCompl_of_saturated hϖ W hWsat`.

Use `set T : Submodule O (Fin r → O) := L₂ ⊔ ⨆ s ∈ Dn, F s`. Use `set Lrest := saturation ϖ T`. Use `set X := W ⊓ Lrest`. Establish `hXsat : ∀ v : Fin r → O, ϖ • v ∈ X → v ∈ X`. Introduce `v hv`.

Conclude with `⟨hWsat v hv.1, saturation_saturated T v hv.2⟩`. Take `⟨Q, hQ⟩` from `exists_isCompl_of_saturated hϖ X hXsat`. Use `⟨W ⊓ Q, Lrest, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`.

Introduce `v hv1 hv2`. Conclude with `(Submodule.disjoint_def.mp hQ.disjoint) v ⟨hv1.1, hv2⟩ hv1.2`. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `v _`. Establish `hv : v ∈ W ⊔ L₂` using `by rw [hL₂.sup_eq_top]; trivial`.

Take `⟨w, hw, l, hl, rfl⟩` from `Submodule.mem_sup.mp hv`. Establish `hw' : w ∈ X ⊔ Q` using `by rw [hQ.sup_eq_top]; trivial`. Take `⟨x, hx, q, hq, hxq⟩` from `Submodule.mem_sup.mp hw'`. Establish `hqW : q ∈ W`. Establish `: q = w - x` using `by rw [← hxq]; abel`.

Rewrite using `[this]`. Conclude with `W.sub_mem hw hx.1`. Establish `hlL : l ∈ Lrest` using `le_saturation T (Submodule.mem_sup_left hl)`. Rewrite using `[← hxq]`. Conclude with `Submodule.mem_sup.mpr ⟨q, Submodule.mem_inf.mpr ⟨hqW, hq⟩, x + l, Lrest.add_mem hx.2 hlL, by abel⟩`.

Introduce `s hs v hv`. Conclude with `(hWmem v).mp hv.1 s hs`. Introduce `s hs`. Use `le_trans ?_ (le_saturation T)` and prove the remaining obligations. Use `le_trans ?_ le_sup_right` and prove the remaining obligations.

Conclude with `le_trans (le_iSup₂_of_le s hs le_rfl) le_rfl`. Establish `h1 : finrank O Lrest ≤ finrank O T` using `finrank_saturation_le hϖ T`. Establish `h2 : finrank O T ≤ finrank O L₂ + m * Dn.card` using `finrank_sup_iSup_le m L₂ F Dn hFr`. Establish `h3 : r ≤ finrank O W + m * Up.card` using `finrank_iInf_ge m C Up hCr`. Establish `h4` using `finrank_sup_add_finrank_inf W L₂`.

Rewrite `h4` using `[hL₂.sup_eq_top, hL₂.inf_eq_bot, finrank_top, finrank_bot, Module.finrank_fin_fun]`. Rewrite using `[Nat.mul_add]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_complement_adapted : UnivPart := by
  intro O _ _ _ ϖ hϖ r m Up Dn C F hCs hFs hCr hFr
  set W : Submodule O (Fin r → O) := ⨅ s ∈ Up, C s with hWdef
  have hWmem : ∀ v, v ∈ W ↔ ∀ s ∈ Up, v ∈ C s := by
    intro v; simp [W, Submodule.mem_iInf]
  have hWsat : ∀ v : Fin r → O, ϖ • v ∈ W → v ∈ W := by
    intro v hv
    rw [hWmem] at hv ⊢
    exact fun s hs => hCs s hs v (hv s hs)
  obtain ⟨L₂, hL₂⟩ := exists_isCompl_of_saturated hϖ W hWsat
  set T : Submodule O (Fin r → O) := L₂ ⊔ ⨆ s ∈ Dn, F s
  set Lrest := saturation ϖ T
  set X := W ⊓ Lrest
  have hXsat : ∀ v : Fin r → O, ϖ • v ∈ X → v ∈ X := by
    intro v hv
    exact ⟨hWsat v hv.1, saturation_saturated T v hv.2⟩
  obtain ⟨Q, hQ⟩ := exists_isCompl_of_saturated hϖ X hXsat
  refine ⟨W ⊓ Q, Lrest, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [Submodule.disjoint_def]
      intro v hv1 hv2
      exact (Submodule.disjoint_def.mp hQ.disjoint) v ⟨hv1.1, hv2⟩ hv1.2
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have hv : v ∈ W ⊔ L₂ := by rw [hL₂.sup_eq_top]; trivial
      obtain ⟨w, hw, l, hl, rfl⟩ := Submodule.mem_sup.mp hv
      have hw' : w ∈ X ⊔ Q := by rw [hQ.sup_eq_top]; trivial
      obtain ⟨x, hx, q, hq, hxq⟩ := Submodule.mem_sup.mp hw'
      have hqW : q ∈ W := by
        have : q = w - x := by rw [← hxq]; abel
        rw [this]; exact W.sub_mem hw hx.1
      have hlL : l ∈ Lrest := le_saturation T (Submodule.mem_sup_left hl)
      rw [← hxq]
      exact Submodule.mem_sup.mpr ⟨q, Submodule.mem_inf.mpr ⟨hqW, hq⟩, x + l,
        Lrest.add_mem hx.2 hlL, by abel⟩
  · intro s hs v hv
    exact (hWmem v).mp hv.1 s hs
  · intro s hs
    refine le_trans ?_ (le_saturation T)
    refine le_trans ?_ le_sup_right
    exact le_trans (le_iSup₂_of_le s hs le_rfl) le_rfl
  · have h1 : finrank O Lrest ≤ finrank O T := finrank_saturation_le hϖ T
    have h2 : finrank O T ≤ finrank O L₂ + m * Dn.card := finrank_sup_iSup_le m L₂ F Dn hFr
    have h3 : r ≤ finrank O W + m * Up.card := finrank_iInf_ge m C Up hCr
    have h4 := finrank_sup_add_finrank_inf W L₂
    rw [hL₂.sup_eq_top, hL₂.inf_eq_bot, finrank_top, finrank_bot, Module.finrank_fin_fun] at h4
    rw [Nat.mul_add]
    omega

end Formalism.ExponentWindows
