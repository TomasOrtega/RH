import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.MoveTyped

open Formalism.L2.NG

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Assemble the required witnesses or components as `⟨bot_le, fun h f hf => by rw [Submodule.mem_bot] at hf ⊢ subst hf exact map_zero _⟩`.
-/
theorem isSubrep_bot (ρ : Representation ℂ (GQ L n) W) :
    IsSubrep ρ (⊥ : Submodule ℂ (GAf L n → W)) :=
  ⟨bot_le, fun h f hf => by
    rw [Submodule.mem_bot] at hf ⊢
    subst hf
    exact map_zero _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨sup_le hX.le hY.le, fun h f hf => by obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf rw [map_add] exact Submodule.add_mem_sup (hX.stable h a ha) (hY.stable h b hb)⟩`.
-/
theorem isSubrep_sup {ρ : Representation ℂ (GQ L n) W} {X Y : Submodule ℂ (GAf L n → W)}
    (hX : IsSubrep ρ X) (hY : IsSubrep ρ Y) : IsSubrep ρ (X ⊔ Y) :=
  ⟨sup_le hX.le hY.le, fun h f hf => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
    rw [map_add]
    exact Submodule.add_mem_sup (hX.stable h a ha) (hY.stable h b hb)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨inf_le_right.trans hY.le, fun h f hf => ⟨hX.stable h f hf.1, hY.stable h f hf.2⟩⟩`.
-/
theorem isSubrep_inf {ρ : Representation ℂ (GQ L n) W} {X Y : Submodule ℂ (GAf L n → W)}
    (hX : IsSubrep ρ X) (hY : IsSubrep ρ Y) : IsSubrep ρ (X ⊓ Y) :=
  ⟨inf_le_right.trans hY.le, fun h f hf => ⟨hX.stable h f hf.1, hY.stable h f hf.2⟩⟩

/- English proof (translation)
Distinguish the cases in `hXY : X ⊓ Y = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `v ⟨hv, hvT⟩`. Establish `hvT' : v ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) v = ((χ κ : ℂˣ) : ℂ) • v` using `hvT`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hv`.

Establish `key : ∀ κ : J, rt L n (κ : GAf L n) a = ((χ κ : ℂˣ) : ℂ) • a ∧ rt L n (κ : GAf L n) b = ((χ κ : ℂˣ) : ℂ) • b`. Introduce `κ`. Establish `e` using `hvT'.2 κ`. Rewrite `e` using `[map_add, smul_add]`. Establish `hmem : rt L n (κ : GAf L n) a - ((χ κ : ℂˣ) : ℂ) • a ∈ X ⊓ Y`.

Use `⟨Submodule.sub_mem _ (hX.stable _ a ha) (Submodule.smul_mem _ _ ha), ?_⟩` and prove the remaining obligations. Establish `hab : rt L n (κ : GAf L n) a - ((χ κ : ℂˣ) : ℂ) • a = ((χ κ : ℂˣ) : ℂ) • b - rt L n (κ : GAf L n) b`. Rewrite using `[sub_eq_sub_iff_add_eq_add, e, add_comm]`. Rewrite using `[hab]`. Conclude with `Submodule.sub_mem _ (Submodule.smul_mem _ _ hb) (hY.1.stable _ b hb)`.

Rewrite `hmem` using `[hXY, Submodule.mem_bot, sub_eq_zero]`. Use `⟨hmem, ?_⟩` and prove the remaining obligations. Rewrite `e` using `[hmem]`. Conclude with `add_left_cancel e`. Establish `ha0 : a ∈ X ⊓ TypeSp ρ J χ` using `⟨ha, hX.le ha, fun κ => (key κ).1⟩`.

Establish `hb0 : b ∈ Y ⊓ TypeSp ρ J χ` using `⟨hb, hY.1.le hb, fun κ => (key κ).2⟩`. Rewrite `ha0` using `[hXT, Submodule.mem_bot]`. Rewrite `hb0` using `[hYT, Submodule.mem_bot]`. Simplify using `[ha0, hb0]`. Establish `hle : X ⊓ Y = Y` using `(hY.2.2 _ (isSubrep_inf hX hY.1) inf_le_right).resolve_left hXY`.

Establish `hYX : Y ≤ X` using `hle ▸ inf_le_left`. Rewrite using `[sup_eq_left.2 hYX, hXT]`.
-/
theorem sup_typed_eq_bot {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {X Y : Submodule ℂ (GAf L n → W)} (hX : IsSubrep ρ X) (hXT : X ⊓ TypeSp ρ J χ = ⊥)
    (hY : IsIrrRep ρ Y) (hYT : Y ⊓ TypeSp ρ J χ = ⊥) : (X ⊔ Y) ⊓ TypeSp ρ J χ = ⊥ := by
  by_cases hXY : X ⊓ Y = ⊥
  · rw [eq_bot_iff]
    rintro v ⟨hv, hvT⟩
    have hvT' : v ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) v = ((χ κ : ℂˣ) : ℂ) • v := hvT
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    have key : ∀ κ : J, rt L n (κ : GAf L n) a = ((χ κ : ℂˣ) : ℂ) • a ∧
        rt L n (κ : GAf L n) b = ((χ κ : ℂˣ) : ℂ) • b := by
      intro κ
      have e := hvT'.2 κ
      rw [map_add, smul_add] at e
      have hmem : rt L n (κ : GAf L n) a - ((χ κ : ℂˣ) : ℂ) • a ∈ X ⊓ Y := by
        refine ⟨Submodule.sub_mem _ (hX.stable _ a ha) (Submodule.smul_mem _ _ ha), ?_⟩
        have hab : rt L n (κ : GAf L n) a - ((χ κ : ℂˣ) : ℂ) • a =
            ((χ κ : ℂˣ) : ℂ) • b - rt L n (κ : GAf L n) b := by
          rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
        rw [hab]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hb) (hY.1.stable _ b hb)
      rw [hXY, Submodule.mem_bot, sub_eq_zero] at hmem
      refine ⟨hmem, ?_⟩
      rw [hmem] at e
      exact add_left_cancel e
    have ha0 : a ∈ X ⊓ TypeSp ρ J χ := ⟨ha, hX.le ha, fun κ => (key κ).1⟩
    have hb0 : b ∈ Y ⊓ TypeSp ρ J χ := ⟨hb, hY.1.le hb, fun κ => (key κ).2⟩
    rw [hXT, Submodule.mem_bot] at ha0
    rw [hYT, Submodule.mem_bot] at hb0
    simp [ha0, hb0]
  · have hle : X ⊓ Y = Y := (hY.2.2 _ (isSubrep_inf hX hY.1) inf_le_right).resolve_left hXY
    have hYX : Y ≤ X := hle ▸ inf_le_left
    rw [sup_eq_left.2 hYX, hXT]

/- English proof (translation)
Take `⟨T, hT⟩` from `hiso`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `u ⟨hu, huT⟩`. Establish `huT' : u ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) u = ((χ κ : ℂˣ) : ℂ) • u` using `huT`. Take `⟨f, hfu⟩ : ∃ f : S, T f = ⟨u, hu⟩` from `⟨T.symm _, T.apply_symm_apply _⟩`.

Establish `hf : ∀ κ : J, rt L n (κ : GAf L n) (f : GAf L n → W) = ((χ κ : ℂˣ) : ℂ) • (f : GAf L n → W)`. Introduce `κ`. Set `f' : S` to `⟨rt L n (κ : GAf L n) f, hS.stable _ _ f.2⟩`. Establish `e` using `hT κ f f' rfl`. Establish `hTT : T f' = T (((χ κ : ℂˣ) : ℂ) • f)`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[e, map_smul, Submodule.coe_smul, hfu]`. Conclude with `huT'.2 κ`. Use `congrArg Subtype.val (T.injective hTT)` as an intermediate fact. Simplify `this` using `[f']`.

Establish `hfm : (f : GAf L n → W) ∈ S ⊓ TypeSp ρ J χ` using `⟨f.2, hS.le f.2, hf⟩`. Rewrite `hfm` using `[h, Submodule.mem_bot]`. Establish `hf0 : f = 0` using `Subtype.ext hfm`. Rewrite `hfu` using `[hf0, map_zero]`. Use `congrArg Subtype.val hfu` as an intermediate fact.

Simplify using `using this.symm`.
-/
theorem typed_eq_bot_of_iso {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {S S' : Submodule ℂ (GAf L n → W)} (hS : IsSubrep ρ S) (hiso : IsoRep S S')
    (h : S ⊓ TypeSp ρ J χ = ⊥) : S' ⊓ TypeSp ρ J χ = ⊥ := by
  obtain ⟨T, hT⟩ := hiso
  rw [eq_bot_iff]
  rintro u ⟨hu, huT⟩
  have huT' : u ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) u = ((χ κ : ℂˣ) : ℂ) • u := huT
  obtain ⟨f, hfu⟩ : ∃ f : S, T f = ⟨u, hu⟩ := ⟨T.symm _, T.apply_symm_apply _⟩
  have hf : ∀ κ : J, rt L n (κ : GAf L n) (f : GAf L n → W) = ((χ κ : ℂˣ) : ℂ) • (f : GAf L n → W) := by
    intro κ
    let f' : S := ⟨rt L n (κ : GAf L n) f, hS.stable _ _ f.2⟩
    have e := hT κ f f' rfl
    have hTT : T f' = T (((χ κ : ℂˣ) : ℂ) • f) := by
      apply Subtype.ext
      rw [e, map_smul, Submodule.coe_smul, hfu]
      exact huT'.2 κ
    have := congrArg Subtype.val (T.injective hTT)
    simpa [f'] using this
  have hfm : (f : GAf L n → W) ∈ S ⊓ TypeSp ρ J χ := ⟨f.2, hS.le f.2, hf⟩
  rw [h, Submodule.mem_bot] at hfm
  have hf0 : f = 0 := Subtype.ext hfm
  rw [hf0, map_zero] at hfu
  have := congrArg Subtype.val hfu
  simpa using this.symm

/- English proof (translation)
Introduce `L _ _ _ n W _ _ ρ J χ S hS hne h0`. Apply `hne` to reduce the goal to its premises. Establish `hfam : ∀ S' ∈ {S' | IsIrrRep ρ S' ∧ IsoRep S S'}, S' ⊓ TypeSp ρ J χ = ⊥` using `fun S' hS' => typed_eq_bot_of_iso hS hS'.2 h0`. Establish `fin : ∀ s : Finset (Submodule ℂ (GAf L n → W)), (↑s : Set _) ⊆ {S' | IsIrrRep ρ S' ∧ IsoRep S S'} → IsSubrep ρ (⨆ i ∈ s, i) ∧ (⨆ i ∈ s, i) ⊓ TypeSp ρ J χ = ⊥`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _`. Simplify using `[isSubrep_bot]`. Consider the case `insert a s ha ih`. Introduce `hs`.

Rewrite `hs` using `[Finset.coe_insert, Set.insert_subset_iff]`. Take `⟨h1, h2⟩` from `ih hs.2`. Rewrite using `[Finset.iSup_insert, sup_comm]`. Conclude with `⟨isSubrep_sup h1 hs.1.1.1, sup_typed_eq_bot h1 h2 hs.1.1 (hfam a hs.1)⟩`. Rewrite using `[eq_bot_iff]`.

Introduce and unpack `v ⟨hv, hvT⟩`. Unfold `isoTyp at hv`. Take `⟨s, hs, hvs⟩` from `Submodule.mem_sSup_iff_exists_finset.1 hv`. Establish `hb` using `(fin s hs).2`. Rewrite `hb` using `[eq_bot_iff]`.

Conclude with `hb ⟨hvs, hvT⟩`.
-/
theorem typed_of_isoTyp : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
    (S : Submodule ℂ (GAf L n → W)), Formalism.L2.NG.IsSubrep ρ S →
    Formalism.L2.NG.isoTyp ρ S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ → S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ := by
  intro L _ _ _ n W _ _ ρ J χ S hS hne h0
  apply hne
  have hfam : ∀ S' ∈ {S' | IsIrrRep ρ S' ∧ IsoRep S S'}, S' ⊓ TypeSp ρ J χ = ⊥ :=
    fun S' hS' => typed_eq_bot_of_iso hS hS'.2 h0
  have fin : ∀ s : Finset (Submodule ℂ (GAf L n → W)), (↑s : Set _) ⊆ {S' | IsIrrRep ρ S' ∧ IsoRep S S'} →
      IsSubrep ρ (⨆ i ∈ s, i) ∧ (⨆ i ∈ s, i) ⊓ TypeSp ρ J χ = ⊥ := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp [isSubrep_bot]
    | insert a s ha ih =>
      intro hs
      rw [Finset.coe_insert, Set.insert_subset_iff] at hs
      obtain ⟨h1, h2⟩ := ih hs.2
      rw [Finset.iSup_insert, sup_comm]
      exact ⟨isSubrep_sup h1 hs.1.1.1, sup_typed_eq_bot h1 h2 hs.1.1 (hfam a hs.1)⟩
  rw [eq_bot_iff]
  rintro v ⟨hv, hvT⟩
  unfold isoTyp at hv
  obtain ⟨s, hs, hvs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hv
  have hb := (fin s hs).2
  rw [eq_bot_iff] at hb
  exact hb ⟨hvs, hvT⟩

end GlobalTheory.MoveTyped
