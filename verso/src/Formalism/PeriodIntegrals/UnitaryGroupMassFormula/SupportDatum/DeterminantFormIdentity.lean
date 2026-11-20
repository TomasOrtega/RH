import Mathlib
import Formalism.PeriodIntegrals.SupportParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.Blocks
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.PowModTwoOfSq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.ModKUnitMul

noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Proceed by induction on `bs generalizing a l with`. Consider the case `nil`. Simplify using `only [modBlocks, Option.some.injEq] at h`. Substitute `h` using the available equality. Simplify using `[mapBlocks]`.

Consider the case `cons b rest ih`. Take `⟨t, s⟩` from `b`. Simplify using `only [modBlocks] at h`. Use `split_ifs at h with hu`. Take `⟨l', hl', rfl⟩` from `Option.map_eq_some_iff.mp h`.

Simplify using `[mapBlocks, ih (a + s) l' hl']`.
-/
theorem modBlocks_some {A B : Type} [Monoid B] (f : ℕ → ℕ → A → B) (bs : List (A × ℕ)) (a : ℕ)
    (l : List (Bˣ × ℕ+)) (h : modBlocks f a bs = some l) :
    l.map (fun x => ((x.1 : B), (x.2 : ℕ))) = mapBlocks f a bs := by
  induction bs generalizing a l with
  | nil =>
    simp only [modBlocks, Option.some.injEq] at h
    subst h
    simp [mapBlocks]
  | cons b rest ih =>
    obtain ⟨t, s⟩ := b
    simp only [modBlocks] at h
    split_ifs at h with hu
    obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp h
    simp [mapBlocks, ih (a + s) l' hl']

/- English proof (translation)
Proceed by induction on `bs generalizing a with`. Consider the case `nil => simp [mapBlocks]`. Consider the case `cons b rest ih`. Take `⟨t, s⟩` from `b`. Simplify using `[mapBlocks, ih]`.
-/
theorem mapBlocks_snd {A B : Type} (f : ℕ → ℕ → A → B) (bs : List (A × ℕ)) (a : ℕ) :
    (mapBlocks f a bs).map Prod.snd = bs.map Prod.snd := by
  induction bs generalizing a with
  | nil => simp [mapBlocks]
  | cons b rest ih =>
    obtain ⟨t, s⟩ := b
    simp [mapBlocks, ih]

/- English proof (translation)
Proceed by induction on `l1 with`. Consider the case `nil => simp [blkDet]`. Consider the case `cons b rest ih`. Take `⟨t, s⟩` from `b`. Simplify using `only [List.cons_append, blkDet, ih]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem blkDet_append {K : Type} [CommRing K] (l1 l2 : List (K × ℕ)) :
    blkDet (l1 ++ l2) = blkDet l1 * blkDet l2 := by
  induction l1 with
  | nil => simp [blkDet]
  | cons b rest ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.cons_append, blkDet, ih]
    ring

/- English proof (translation)
Proceed by induction on `bs generalizing a with`. Consider the case `nil => simp [mapBlocks, blkDet, prodFac]`. Consider the case `cons b rest ih`. Take `⟨t, s⟩` from `b`. Establish `ht : t ≠ 0` using `h (t, s) (by simp)`.

Establish `hr : ∀ b ∈ rest, b.1 ≠ 0` using `fun b hb => h b (by simp [hb])`. Simplify using `only [mapBlocks, blkDet, prodFac, ih (a + s) hr, blkTop_eq D δ T T' p a s t ht, map_mul, map_pow, map_neg, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem blkDet_map (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D)
    (bs : List (D.host.E × ℕ)) (a : ℕ) (h : ∀ b ∈ bs, b.1 ≠ 0) :
    blkDet (mapBlocks (blkTop δ T T' p) a bs) =
      (D.s.atP p).ιE (blkDet bs) * prodFac (gF D δ T T' p) a bs := by
  induction bs generalizing a with
  | nil => simp [mapBlocks, blkDet, prodFac]
  | cons b rest ih =>
    obtain ⟨t, s⟩ := b
    have ht : t ≠ 0 := h (t, s) (by simp)
    have hr : ∀ b ∈ rest, b.1 ≠ 0 := fun b hb => h b (by simp [hb])
    simp only [mapBlocks, blkDet, prodFac, ih (a + s) hr, blkTop_eq D δ T T' p a s t ht, map_mul,
      map_pow, map_neg, map_one]
    ring

def cKind (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) :
    Option D.host.E → (D.s.atP p).Ep
  | none => Hm D δ p 1 (D.R.rS + 1)
  | some ζ => Hm D δ p 1 D.R.rS * gF D δ T T' p (D.R.rS + 1) 1 ζ

/- English proof (translation)
Unfold `modPt at ha`. Use `split at ha`. Simplify using `at ha`. Name the introduced variables `l hl split_ifs at ha with hsum`. Consider the cases of `ha`.

Establish `hmap` using `modBlocks_some _ _ _ l hl`. Apply the tactic sequence `have hmat : (⟨l, hsum⟩ : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)).mat = Matrix.of fun i j : Fin (D.R.rS + 1) => ptEntry (mapBlocks (blkTop δ T T' p) 1 w.1) i.val j.val := by`. Use extensionality with `i j`. Simplify using `only [Loc.Pt.mat, Matrix.of_apply]`. Rewrite using `[ptEntryL_eq, hmap]`.

Rewrite using `[hmat]`. Apply `ptEntry_det` to reduce the goal to its premises. Rewrite using `[mapBlocks_snd]`. Conclude with `w.2.2`.
-/
theorem modPt_det (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D)
    (w : Point D.host.E (D.R.rS + 1)) (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))
    (ha : modPt δ T T' p w = some a) :
    a.mat.det = blkDet (mapBlocks (blkTop δ T T' p) 1 w.1) := by
  unfold modPt at ha
  split at ha
  · simp at ha
  · rename_i l hl
    split_ifs at ha with hsum
    · cases ha
      have hmap := modBlocks_some _ _ _ l hl
      have hmat : (⟨l, hsum⟩ : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)).mat =
          Matrix.of fun i j : Fin (D.R.rS + 1) =>
            ptEntry (mapBlocks (blkTop δ T T' p) 1 w.1) i.val j.val := by
        ext i j
        simp only [Loc.Pt.mat, Matrix.of_apply]
        rw [ptEntryL_eq, hmap]
      rw [hmat]
      apply ptEntry_det
      rw [mapBlocks_snd]
      exact w.2.2

/- English proof (translation)
Introduce `D δ p T T'`. Use `⟨cKind D δ T T' p, fun w a ha => ?_⟩` and prove the remaining obligations. Establish `hne : ∀ b ∈ w.1, b.1 ≠ 0` using `fun b hb => (w.2.1 b hb).1`. Rewrite using `[modPt_det D δ T T' p w a ha, blkDet_map D δ T T' p w.1 1 hne, dmin_top]`. Use `congr 1`.

Choose the witnesses or unpack the hypotheses as in `⟨head, ⟨t, s⟩, hw⟩ : ∃ head b, w.1 = head ++ [b] := by`. Establish `hnil : w.1 ≠ []`. Introduce `h0`. Establish `h1` using `w.2.2`. Rewrite `h1` using `[h0, List.map_nil, List.sum_nil]`.

Use linear arithmetic over natural numbers and integers. Conclude with `⟨w.1.dropLast, w.1.getLast hnil, (List.dropLast_append_getLast hnil).symm⟩`. Establish `hsum` using `w.2.2`. Rewrite `hsum` using `[hw]`. Simplify using `only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsum`.

Establish `hts` using `w.2.1 (t, s) (by rw [hw]; simp)`. Establish `hhead : ∀ b ∈ head, 1 ≤ b.2` using `fun b hb => (w.2.1 b (by rw [hw]; simp [hb])).2`. Establish `hs1 : 1 ≤ s` using `hts.2`. Rewrite using `[hw, prodFac_append, prodFac_noTop D δ T T' p head 1 le_rfl hhead (by omega)]`. Simplify using `only [prodFac, mul_one]`.

Break down `Nat.lt_or_ge s 2 with hs | hs` into its components or cases. Establish `hs' : s = 1` using `by omega`. Substitute `hs'` using the available equality. Establish `hk : Dmin w D.R.rS = blkDet head` using `dmin_last_one D w head t hw`. Establish `hkne : blkDet head ≠ 0` using `blkDet_ne_zero head (fun b hb => hne b (by rw [hw]; simp [hb]))`.

Establish `hz : zetaOf w = t`. Unfold `zetaOf`. Rewrite using `[hk, dmin_top, hw, blkDet_append]`. Establish `h1 : blkDet [(t, 1)] = t` using `by simp [blkDet]`. Rewrite using `[h1, mul_div_cancel_left₀ t hkne]`.

Establish `hkind : kind w = some t`. Unfold `kind`. Rewrite using `[if_neg (by rw [hk]; exact hkne), hz]`. Rewrite using `[hkind]`. Simplify using `only [cKind, pow_one]`.

Establish `h2 : (head.map Prod.snd).sum = D.R.rS` using `by omega`. Rewrite using `[h2, Nat.add_comm 1 D.R.rS]`. Establish `hk : Dmin w D.R.rS = 0` using `dmin_last_big D w head t s hw hs`. Establish `hkind : kind w = none`. Unfold `kind`.

Rewrite using `[if_pos hk]`. Rewrite using `[hkind]`. Simplify using `only [cKind]`. Establish `hg : gF D δ T T' p (1 + (head.map Prod.snd).sum) s t = hF D δ p (1 + (head.map Prod.snd).sum) s`. Unfold `gF`.

Rewrite using `[if_neg (by omega)]`. Rewrite using `[hg, hF_pow D δ p _ s (by omega) (by omega), ← Hm_add]`. Use `congr 1`.
-/
theorem determinant_form_identity : DetForm := by
  intro D δ p T T'
  refine ⟨cKind D δ T T' p, fun w a ha => ?_⟩
  have hne : ∀ b ∈ w.1, b.1 ≠ 0 := fun b hb => (w.2.1 b hb).1
  rw [modPt_det D δ T T' p w a ha, blkDet_map D δ T T' p w.1 1 hne, dmin_top]
  congr 1
  obtain ⟨head, ⟨t, s⟩, hw⟩ : ∃ head b, w.1 = head ++ [b] := by
    have hnil : w.1 ≠ [] := by
      intro h0
      have h1 := w.2.2
      rw [h0, List.map_nil, List.sum_nil] at h1
      omega
    exact ⟨w.1.dropLast, w.1.getLast hnil, (List.dropLast_append_getLast hnil).symm⟩
  have hsum := w.2.2
  rw [hw] at hsum
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] at hsum
  have hts := w.2.1 (t, s) (by rw [hw]; simp)
  have hhead : ∀ b ∈ head, 1 ≤ b.2 := fun b hb => (w.2.1 b (by rw [hw]; simp [hb])).2
  have hs1 : 1 ≤ s := hts.2
  rw [hw, prodFac_append, prodFac_noTop D δ T T' p head 1 le_rfl hhead (by omega)]
  simp only [prodFac, mul_one]
  rcases Nat.lt_or_ge s 2 with hs | hs
  · have hs' : s = 1 := by omega
    subst hs'
    have hk : Dmin w D.R.rS = blkDet head := dmin_last_one D w head t hw
    have hkne : blkDet head ≠ 0 :=
      blkDet_ne_zero head (fun b hb => hne b (by rw [hw]; simp [hb]))
    have hz : zetaOf w = t := by
      unfold zetaOf
      rw [hk, dmin_top, hw, blkDet_append]
      have h1 : blkDet [(t, 1)] = t := by simp [blkDet]
      rw [h1, mul_div_cancel_left₀ t hkne]
    have hkind : kind w = some t := by
      unfold kind
      rw [if_neg (by rw [hk]; exact hkne), hz]
    rw [hkind]
    simp only [cKind, pow_one]
    have h2 : (head.map Prod.snd).sum = D.R.rS := by omega
    rw [h2, Nat.add_comm 1 D.R.rS]
  · have hk : Dmin w D.R.rS = 0 := dmin_last_big D w head t s hw hs
    have hkind : kind w = none := by
      unfold kind
      rw [if_pos hk]
    rw [hkind]
    simp only [cKind]
    have hg : gF D δ T T' p (1 + (head.map Prod.snd).sum) s t =
        hF D δ p (1 + (head.map Prod.snd).sum) s := by
      unfold gF
      rw [if_neg (by omega)]
    rw [hg, hF_pow D δ p _ s (by omega) (by omega), ← Hm_add]
    congr 1

end PI.SupportDatumW
