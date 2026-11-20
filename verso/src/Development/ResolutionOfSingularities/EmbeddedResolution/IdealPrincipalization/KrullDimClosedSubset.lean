import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
universe u v

open TopologicalSpace AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

open Order in
/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem topologicalKrullDim_eq_iSup_length {Z : Type*} [TopologicalSpace Z] :
    topologicalKrullDim Z =
      ⨆ p : LTSeries (IrreducibleCloseds Z), (p.length : WithBot ℕ∞) := rfl

private def irreducibleClosedsImageSubtypeVal {X : Type u} [TopologicalSpace X] {Y : Set X} (hY : IsClosed Y)
    (a : IrreducibleCloseds ↥Y) : IrreducibleCloseds X :=
  ⟨Subtype.val '' a.1, a.2.image _ continuous_subtype_val.continuousOn,
    hY.isClosedMap_subtype_val _ a.3⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem coe_irreducibleClosedsImageVal {X : Type u} [TopologicalSpace X] {Y : Set X} (hY : IsClosed Y)
    (a : IrreducibleCloseds ↥Y) :
    ((irreducibleClosedsImageSubtypeVal hY a : IrreducibleCloseds X) : Set X) = Subtype.val '' (a : Set ↥Y) := rfl

/- English proof (translation)
Rewrite using `[coe_irreducibleClosedsImageVal]`. Introduce and unpack `x ⟨y, -, rfl⟩`. Conclude with `y.2`.
-/
private theorem irreducibleClosedsImageVal_subset {X : Type u} [TopologicalSpace X] {Y : Set X} (hY : IsClosed Y)
    (a : IrreducibleCloseds ↥Y) :
    ((irreducibleClosedsImageSubtypeVal hY a : IrreducibleCloseds X) : Set X) ⊆ Y := by
  rw [coe_irreducibleClosedsImageVal]
  rintro x ⟨y, -, rfl⟩
  exact y.2

/- English proof (translation)
Introduce `a b hab`. Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations. Rewrite using `[← SetLike.coe_subset_coe, coe_irreducibleClosedsImageVal, coe_irreducibleClosedsImageVal]`. Conclude with `Set.image_mono (SetLike.coe_subset_coe.mpr hab.le)`. Introduce `h`.

Establish `h1 : Subtype.val '' (a : Set ↥Y) = Subtype.val '' (b : Set ↥Y)`. Rewrite using `[← coe_irreducibleClosedsImageVal hY a, ← coe_irreducibleClosedsImageVal hY b, h]`. Conclude with `hab.ne (SetLike.coe_injective (Set.image_injective.mpr Subtype.val_injective h1))`.
-/
private theorem strictMono_irreducibleClosedsImageVal {X : Type u} [TopologicalSpace X] {Y : Set X}
    (hY : IsClosed Y) : StrictMono (irreducibleClosedsImageSubtypeVal hY) := by
  intro a b hab
  refine lt_of_le_of_ne ?_ ?_
  · rw [← SetLike.coe_subset_coe, coe_irreducibleClosedsImageVal, coe_irreducibleClosedsImageVal]
    exact Set.image_mono (SetLike.coe_subset_coe.mpr hab.le)
  · intro h
    have h1 : Subtype.val '' (a : Set ↥Y) = Subtype.val '' (b : Set ↥Y) := by
      rw [← coe_irreducibleClosedsImageVal hY a, ← coe_irreducibleClosedsImageVal hY b, h]
    exact hab.ne (SetLike.coe_injective (Set.image_injective.mpr Subtype.val_injective h1))

/- English proof (translation)
Take `⟨t, ht, hst, hmax⟩` from `exists_preirreducible s hs.2`. Establish `htirr : IsIrreducible t` using `⟨hs.1.mono hst, ht⟩`. Establish `htc : closure t = t` using `hmax (closure t) ht.closure subset_closure`. Conclude with `⟨t, ⟨htirr, fun u hu htu => le_of_eq (hmax u hu.2 htu)⟩, htirr, closure_eq_iff_isClosed.mp htc, hst⟩`.
-/
private theorem exists_mem_irreducibleComponents_superset_of_isIrreducible {X : Type u} [TopologicalSpace X] {s : Set X}
    (hs : IsIrreducible s) :
    ∃ C : Set X, C ∈ irreducibleComponents X ∧ IsIrreducible C ∧ IsClosed C ∧ s ⊆ C := by
  obtain ⟨t, ht, hst, hmax⟩ := exists_preirreducible s hs.2
  have htirr : IsIrreducible t := ⟨hs.1.mono hst, ht⟩
  have htc : closure t = t := hmax (closure t) ht.closure subset_closure
  exact ⟨t, ⟨htirr, fun u hu htu => le_of_eq (hmax u hu.2 htu)⟩, htirr,
    closure_eq_iff_isClosed.mp htc, hst⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨closure {z}, ⟨⟨z, subset_closure rfl⟩, isPreirreducible_singleton.closure⟩, isClosed_closure⟩⟩`.
-/
private theorem nonempty_irreducibleCloseds {Z : Type u} [TopologicalSpace Z] (z : Z) :
    Nonempty (IrreducibleCloseds Z) :=
  ⟨⟨closure {z}, ⟨⟨z, subset_closure rfl⟩, isPreirreducible_singleton.closure⟩,
    isClosed_closure⟩⟩

open Order in
/- English proof (translation)
Establish `key : ∀ p : LTSeries (IrreducibleCloseds ↥Y), (((p.length + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim X`. Introduce `p`. Take `⟨q, hqlen, hqlast⟩ : ∃ q : LTSeries (IrreducibleCloseds X), q.length = p.length ∧ q.last = irreducibleClosedsImageSubtypeVal hY p.last` from `⟨p.map (irreducibleClosedsImageSubtypeVal hY) (strictMono_irreducibleClosedsImageVal hY), rfl, rfl⟩`. Take `⟨C, hCmem, hCirr, hCcl, hsub⟩` from `exists_mem_irreducibleComponents_superset_of_isIrreducible q.last.2`. Establish `hsub' : ((q.last : IrreducibleCloseds X) : Set X) ⊆ ((⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) : Set X)` using `hsub`.

Establish `hlt : q.last < (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X)`. Use `lt_of_le_of_ne (SetLike.coe_subset_coe.mp hsub') ?_` and prove the remaining obligations. Introduce `h`. Use `hcomp C hCmem ?_` and prove the remaining obligations. Establish `hc : ((⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) : Set X) ⊆ Y`.

Rewrite using `[← h, hqlast]`. Conclude with `irreducibleClosedsImageVal_subset hY p.last`. Conclude with `hc`. Establish `hs1 : (q.snoc (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) hlt).length = q.length + 1` using `rfl`. Establish `hs2 : (q.snoc (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) hlt).length = p.length + 1`.

Use linear arithmetic over natural numbers and integers. Establish `h1 : ((q.snoc (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) hlt).length : WithBot ℕ∞) ≤ ⨆ r : LTSeries (IrreducibleCloseds X), (r.length : WithBot ℕ∞)` using `le_iSup (fun r : LTSeries (IrreducibleCloseds X) => (r.length : WithBot ℕ∞)) _`. Rewrite `h1` using `[hs2]`. Rewrite using `[topologicalKrullDim_eq_iSup_length, WithBot.coe_natCast]`. Conclude with `h1`.

Take `⟨y0, hy0⟩` from `hne`. Take `⟨a0⟩` from `nonempty_irreducibleCloseds (⟨y0, hy0⟩ : ↥Y)`. Establish `hp0 : (((1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim X` using `key ⟨0, fun _ => a0, fun i => i.elim0⟩`. Establish `hbot : topologicalKrullDim X ≠ ⊥`. Introduce `hb`.

Rewrite `hp0` using `[hb]`. Conclude with `WithBot.coe_ne_bot (le_bot_iff.mp hp0)`. Take `⟨e, he⟩` from `WithBot.ne_bot_iff_exists.mp hbot`. Establish `hetop : e ≠ ⊤`. Introduce and unpack `rfl`.

Rewrite `hfin` using `[← he]`. Conclude with `lt_irrefl _ hfin`. Take `⟨N, hN⟩` from `ENat.ne_top_iff_exists.mp hetop`. Establish `hD : topologicalKrullDim X = (((N : ℕ) : ℕ∞) : WithBot ℕ∞)`. Rewrite using `[← he, ← hN]`.

Rewrite `hp0` using `[hD]`. Establish `hN1 : 1 ≤ N`. Establish `h2` using `WithBot.coe_le_coe.mp hp0`. Conclude with `h2` after adjusting the coercions. Establish `hbound : (⨆ p : LTSeries (IrreducibleCloseds ↥Y), (p.length : WithBot ℕ∞)) ≤ ((((N - 1 : ℕ)) : ℕ∞) : WithBot ℕ∞)`.

Use `iSup_le fun p => ?_` and prove the remaining obligations. Use `show ((p.length : ℕ) : WithBot ℕ∞) ≤ ((((N - 1 : ℕ)) : ℕ∞) : WithBot ℕ∞)`. Establish `hk` using `key p`. Rewrite `hk` using `[hD]`. Establish `h3 : p.length + 1 ≤ N`.

Establish `h2` using `WithBot.coe_le_coe.mp hk`. Conclude with `h2` after adjusting the coercions. Establish `h4 : p.length ≤ N - 1` using `by omega`. Rewrite using `[← WithBot.coe_natCast]`. Conclude with `WithBot.coe_le_coe.mpr (by exact_mod_cast h4)`.

Establish `h5 : N - 1 < N` using `by omega`. Establish `h6 : (((N - 1 : ℕ)) : ℕ∞) < ((N : ℕ) : ℕ∞)` using `by exact_mod_cast h5`. Rewrite using `[topologicalKrullDim_eq_iSup_length (Z := ↥Y), hD]`. Conclude with `lt_of_le_of_lt hbound (WithBot.coe_lt_coe.mpr h6)`.
-/
theorem topologicalKrullDim_lt_of_isClosed_of_not_subset_irreducibleComponents
    {X : Type u} [TopologicalSpace X] (Y : Set X) (hY : IsClosed Y) (hne : Y.Nonempty)
    (hcomp : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ Y)
    (hfin : topologicalKrullDim X < ⊤) :
    topologicalKrullDim ↥Y < topologicalKrullDim X := by
  have key : ∀ p : LTSeries (IrreducibleCloseds ↥Y),
      (((p.length + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    intro p
    obtain ⟨q, hqlen, hqlast⟩ :
        ∃ q : LTSeries (IrreducibleCloseds X),
          q.length = p.length ∧ q.last = irreducibleClosedsImageSubtypeVal hY p.last :=
      ⟨p.map (irreducibleClosedsImageSubtypeVal hY) (strictMono_irreducibleClosedsImageVal hY), rfl, rfl⟩
    obtain ⟨C, hCmem, hCirr, hCcl, hsub⟩ := exists_mem_irreducibleComponents_superset_of_isIrreducible q.last.2
    have hsub' : ((q.last : IrreducibleCloseds X) : Set X)
        ⊆ ((⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) : Set X) := hsub
    have hlt : q.last < (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) := by
      refine lt_of_le_of_ne (SetLike.coe_subset_coe.mp hsub') ?_
      intro h
      refine hcomp C hCmem ?_
      have hc : ((⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) : Set X) ⊆ Y := by
        rw [← h, hqlast]
        exact irreducibleClosedsImageVal_subset hY p.last
      exact hc
    have hs1 : (q.snoc (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) hlt).length = q.length + 1 := rfl
    have hs2 : (q.snoc (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) hlt).length = p.length + 1 := by
      omega
    have h1 : ((q.snoc (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) hlt).length : WithBot ℕ∞)
        ≤ ⨆ r : LTSeries (IrreducibleCloseds X), (r.length : WithBot ℕ∞) :=
      le_iSup (fun r : LTSeries (IrreducibleCloseds X) => (r.length : WithBot ℕ∞)) _
    rw [hs2] at h1
    rw [topologicalKrullDim_eq_iSup_length, WithBot.coe_natCast]
    exact h1
  obtain ⟨y0, hy0⟩ := hne
  obtain ⟨a0⟩ := nonempty_irreducibleCloseds (⟨y0, hy0⟩ : ↥Y)
  have hp0 : (((1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim X :=
    key ⟨0, fun _ => a0, fun i => i.elim0⟩
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    intro hb
    rw [hb] at hp0
    exact WithBot.coe_ne_bot (le_bot_iff.mp hp0)
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hetop : e ≠ ⊤ := by
    rintro rfl
    rw [← he] at hfin
    exact lt_irrefl _ hfin
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hetop
  have hD : topologicalKrullDim X = (((N : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [← he, ← hN]
  rw [hD] at hp0
  have hN1 : 1 ≤ N := by
    have h2 := WithBot.coe_le_coe.mp hp0
    exact_mod_cast h2
  have hbound : (⨆ p : LTSeries (IrreducibleCloseds ↥Y), (p.length : WithBot ℕ∞))
      ≤ ((((N - 1 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
    refine iSup_le fun p => ?_
    show ((p.length : ℕ) : WithBot ℕ∞) ≤ ((((N - 1 : ℕ)) : ℕ∞) : WithBot ℕ∞)
    have hk := key p
    rw [hD] at hk
    have h3 : p.length + 1 ≤ N := by
      have h2 := WithBot.coe_le_coe.mp hk
      exact_mod_cast h2
    have h4 : p.length ≤ N - 1 := by omega
    rw [← WithBot.coe_natCast]
    exact WithBot.coe_le_coe.mpr (by exact_mod_cast h4)
  have h5 : N - 1 < N := by omega
  have h6 : (((N - 1 : ℕ)) : ℕ∞) < ((N : ℕ) : ℕ∞) := by exact_mod_cast h5
  rw [topologicalKrullDim_eq_iSup_length (Z := ↥Y), hD]
  exact lt_of_le_of_lt hbound (WithBot.coe_lt_coe.mpr h6)

private def irreducibleClosedsMapHomeomorph {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (a : IrreducibleCloseds X) : IrreducibleCloseds Y :=
  ⟨e '' a.1, a.2.image e e.continuous.continuousOn, e.isClosedMap _ a.3⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem coe_irreducibleClosedsMapOfHomeomorph {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (a : IrreducibleCloseds X) :
    ((irreducibleClosedsMapHomeomorph e a : IrreducibleCloseds Y) : Set Y) = e '' (a : Set X) := rfl

/- English proof (translation)
Introduce `a b hab`. Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations. Rewrite using `[← SetLike.coe_subset_coe, coe_irreducibleClosedsMapOfHomeomorph, coe_irreducibleClosedsMapOfHomeomorph]`. Conclude with `Set.image_mono (SetLike.coe_subset_coe.mpr hab.le)`. Introduce `h`.

Establish `h1 : e '' (a : Set X) = e '' (b : Set X)`. Rewrite using `[← coe_irreducibleClosedsMapOfHomeomorph e a, ← coe_irreducibleClosedsMapOfHomeomorph e b, h]`. Conclude with `hab.ne (SetLike.coe_injective (Set.image_injective.mpr e.injective h1))`.
-/
private theorem strictMono_irreducibleClosedsMapOfHomeomorph {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : StrictMono (irreducibleClosedsMapHomeomorph e) := by
  intro a b hab
  refine lt_of_le_of_ne ?_ ?_
  · rw [← SetLike.coe_subset_coe, coe_irreducibleClosedsMapOfHomeomorph, coe_irreducibleClosedsMapOfHomeomorph]
    exact Set.image_mono (SetLike.coe_subset_coe.mpr hab.le)
  · intro h
    have h1 : e '' (a : Set X) = e '' (b : Set X) := by
      rw [← coe_irreducibleClosedsMapOfHomeomorph e a, ← coe_irreducibleClosedsMapOfHomeomorph e b, h]
    exact hab.ne (SetLike.coe_injective (Set.image_injective.mpr e.injective h1))

open Order in
/- English proof (translation)
Rewrite using `[topologicalKrullDim_eq_iSup_length (Z := X), topologicalKrullDim_eq_iSup_length (Z := Y)]`. Use `iSup_le fun p => ?_` and prove the remaining obligations. Establish `h` using `le_iSup (fun r : LTSeries (IrreducibleCloseds Y) => (r.length : WithBot ℕ∞)) (p.map (irreducibleClosedsMapHomeomorph e) (strictMono_irreducibleClosedsMapOfHomeomorph e))`. Conclude with `h`.
-/
private theorem topologicalKrullDim_le_of_homeomorph {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_iSup_length (Z := X), topologicalKrullDim_eq_iSup_length (Z := Y)]
  refine iSup_le fun p => ?_
  have h := le_iSup (fun r : LTSeries (IrreducibleCloseds Y) => (r.length : WithBot ℕ∞))
    (p.map (irreducibleClosedsMapHomeomorph e) (strictMono_irreducibleClosedsMapOfHomeomorph e))
  exact h

/- English proof (translation)
The claim follows from `le_antisymm (topologicalKrullDim_le_of_homeomorph e) (topologicalKrullDim_le_of_homeomorph e.symm)`.
-/
theorem topologicalKrullDim_eq_of_homeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  le_antisymm (topologicalKrullDim_le_of_homeomorph e) (topologicalKrullDim_le_of_homeomorph e.symm)

/- English proof (translation)
Proceed by induction on `b using WithBot.recBotCoe with`. Consider the case `bot => exact absurd h not_lt_bot`. Consider the case `coe n`. Establish `hn : n ≠ ⊤`. Introduce and unpack `rfl`.

Conclude with `lt_irrefl _ hb`. Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot`. Rewrite using `[withBotSuccToNat_bot, withBotSuccToNat_coe]`. Use linear arithmetic over natural numbers and integers.

Consider the case `coe m`. Establish `hmn : m < n` using `WithBot.coe_lt_coe.mp h`. Establish `hm : m ≠ ⊤` using `ne_top_of_lt hmn`. Take `⟨M, hM⟩` from `ENat.ne_top_iff_exists.mp hm`. Take `⟨N, hN⟩` from `ENat.ne_top_iff_exists.mp hn`.

Substitute `hM` using the available equality. Substitute `hN` using the available equality. Rewrite using `[withBotSuccToNat_coe, withBotSuccToNat_coe]`. Establish `hMN : M < N` using `by exact_mod_cast hmn`. Establish `e1 : ((M : ℕ∞)).toNat = M` using `by simp`.

Establish `e2 : ((N : ℕ∞)).toNat = N` using `by simp`. Use linear arithmetic over natural numbers and integers.
-/
private theorem withBotSuccToNat_lt_withBotSuccToNat {a b : WithBot ℕ∞} (h : a < b) (hb : b < ⊤) :
    withBotSuccToNat a < withBotSuccToNat b := by
  induction b using WithBot.recBotCoe with
  | bot => exact absurd h not_lt_bot
  | coe n =>
    have hn : n ≠ ⊤ := by
      rintro rfl
      exact lt_irrefl _ hb
    induction a using WithBot.recBotCoe with
    | bot =>
      rw [withBotSuccToNat_bot, withBotSuccToNat_coe]
      omega
    | coe m =>
      have hmn : m < n := WithBot.coe_lt_coe.mp h
      have hm : m ≠ ⊤ := ne_top_of_lt hmn
      obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp hm
      obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hn
      subst hM
      subst hN
      rw [withBotSuccToNat_coe, withBotSuccToNat_coe]
      have hMN : M < N := by exact_mod_cast hmn
      have e1 : ((M : ℕ∞)).toNat = M := by simp
      have e2 : ((N : ℕ∞)).toNat = N := by simp
      omega

/- English proof (translation)
The claim follows from `withBotSuccToNat_lt_withBotSuccToNat h hfin`.
-/
theorem krullDimSucc_lt_of_topologicalKrullDim_lt (Z X : Scheme.{u})
    (h : topologicalKrullDim ↥Z < topologicalKrullDim ↥X)
    (hfin : topologicalKrullDim ↥X < ⊤) :
    krullDimSucc Z < krullDimSucc X := withBotSuccToNat_lt_withBotSuccToNat h hfin

/- English proof (translation)
Establish `h` using `topologicalKrullDim_lt_of_isClosed_of_not_subset_irreducibleComponents Y hY hne hcomp hfin`. Use `krullDimSucc_lt_of_topologicalKrullDim_lt Z X ?_ hfin` and prove the remaining obligations. Rewrite using `[topologicalKrullDim_eq_of_homeomorph e]`. Conclude with `h`.
-/
theorem krullDimSucc_lt_of_homeomorph_isClosed (X Z : Scheme.{u}) (Y : Set ↥X)
    (hY : IsClosed Y) (hne : Y.Nonempty)
    (hcomp : ∀ C ∈ irreducibleComponents ↥X, ¬ C ⊆ Y)
    (hfin : topologicalKrullDim ↥X < ⊤)
    (e : ↥Z ≃ₜ ↥Y) :
    krullDimSucc Z < krullDimSucc X := by
  have h := topologicalKrullDim_lt_of_isClosed_of_not_subset_irreducibleComponents Y hY hne hcomp
    hfin
  refine krullDimSucc_lt_of_topologicalKrullDim_lt Z X ?_ hfin
  rw [topologicalKrullDim_eq_of_homeomorph e]
  exact h

end FunctorialResolution.EmbeddedResolution
