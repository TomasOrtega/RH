import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.UnipotentCharacter

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace UpperBlockProducts

/- English proof (translation)
Introduce `i c hic`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) S) i c - s ((1 : Matrix (Fin a) (Fin a) R) i c) + s (g.val i c) = _`. Rewrite using `[hg i c hic, sub_add_cancel]`.
-/
theorem blk_corner {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S) {j : ℕ} {g : GL (Fin a) R}
    (hg : GlobalTheory j g) : GlobalTheory j (cornerGL a s g) := by
  intro i c hic
  change (1 : Matrix (Fin a) (Fin a) S) i c - s ((1 : Matrix (Fin a) (Fin a) R) i c) + s (g.val i c) = _
  rw [hg i c hic, sub_add_cancel]

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

/- English proof (translation)
The claim follows from `blk_corner (sFin E) (blk_corner (sLoc E v) hc)`.
-/
theorem blk_fl (v : Pl E) {j : ℕ} {c : GL (Fin k) (v.adicCompletion E)} (hc : GlobalTheory j c) : GlobalTheory j (fl k v c) :=
  blk_corner (sFin E) (blk_corner (sLoc E v) hc)

/- English proof (translation)
Simplify using `only [posM, Matrix.sum_apply, Matrix.single_apply]`. Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Take `⟨t1, t2, t3⟩` from `t.2`.

Rewrite `*` using `[h1, h2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem posM_blk_zero {j : ℕ} (Y : UnipotentBlockColumnIndex k j j → Ad E) (i c : Fin k) (h : (c : ℕ) ≤ i) :
    posM Subtype.val Y i c = 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [if_neg]
  rintro ⟨h1, h2⟩
  obtain ⟨t1, t2, t3⟩ := t.2
  rw [h1, h2] at *
  omega

/- English proof (translation)
Use `⟨fun i c hci => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 + posM Subtype.val Y) i c = 0`. Rewrite using `[Matrix.add_apply, posM_blk_zero Y i c (le_of_lt hci), Matrix.one_apply_ne hci.ne', add_zero]`. Express the relevant statement in the definitionally equal form `(1 + posM Subtype.val Y) i i = 1`. Rewrite using `[Matrix.add_apply, posM_blk_zero Y i i le_rfl, Matrix.one_apply_eq, add_zero]`.
-/
theorem uu_blkU {j : ℕ} (Y : UnipotentBlockColumnIndex k j j → Ad E) : UU 0 (blkU Y : GA E k) := by
  refine ⟨fun i c hci => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · change (1 + posM Subtype.val Y) i c = 0
    rw [Matrix.add_apply, posM_blk_zero Y i c (le_of_lt hci), Matrix.one_apply_ne hci.ne', add_zero]
  · change (1 + posM Subtype.val Y) i i = 1
    rw [Matrix.add_apply, posM_blk_zero Y i i le_rfl, Matrix.one_apply_eq, add_zero]

/- English proof (translation)
Use `⟨fun i c hci => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Break down `lt_or_ge l i with h | h` into its components or cases. Rewrite using `[hu.1 i l h, zero_mul]`.

Rewrite using `[hu'.1 l c (lt_of_lt_of_le hci h), mul_zero]`. Rewrite using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, hu.2.1, hu'.2.1, one_mul]`. Introduce `l _ hl`. Break down `lt_or_gt_of_ne hl with h | h` into its components or cases. Rewrite using `[hu.1 i l h, zero_mul]`.

Rewrite using `[hu'.1 l i h, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem uu_mul {u u' : GA E k} (hu : UU 0 u) (hu' : UU 0 u') : UU 0 (u * u') := by
  refine ⟨fun i c hci => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hu.1 i l h, zero_mul]
    · rw [hu'.1 l c (lt_of_lt_of_le hci h), mul_zero]
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, hu.2.1, hu'.2.1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hu.1 i l h, zero_mul]
      · rw [hu'.1 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

end UpperBlockProducts

open UpperBlockProducts UnipotentCharacter in
/- English proof (translation)
Introduce `hS2 hS9 hS10 hG0 hG5 hG5b hP2 E _ _ _ k wt ρ J hW ψ hψ S Y hY n m v hv hmv hm0 U hU x C hxY hsm hlev hB`. Take `⟨-, -, i3, i4, i5, -, i7, i8, -, i10, -, -, -, i14, -⟩` from `hG0 E k`. Take `⟨g5a, g5r, -, g5c⟩` from `hG5 E k ψ hψ`. Take `⟨-, b2, b3, b4, b5⟩` from `hG5b E k S`. Take `⟨s10dec, -, -, s10blk1, -⟩` from `hS10 (v.adicCompletion E) k (m v + 1)`.

Take `⟨p2law, p2norm, p2uu, p2whit, -, p2good, -⟩` from `hP2 E k ψ hψ`. Take `⟨s0, sadd, ssmul, -, sT, -⟩` from `hS2 (InfinitePlace E) k (XB E k) (ρ.comp (infGL E k)) hW.poly`. Set `U' : Set (GL (Fin k) (v.adicCompletion E))` to `{u | repW k v u (J x) = J x} ∩ (fl k v) ⁻¹' U`. Establish `hU' : U' ∈ 𝓝 (1 : GL (Fin k) (v.adicCompletion E))` using `Filter.inter_mem (hlev v hv) ((i14 v).continuousAt.preimage_mem_nhds (by rw [map_one]; exact hU))`. Establish `hne : ∃ y, chi ψ v y ≠ 1`.

Take `⟨y, hy⟩` from `hψ.loc v`. Conclude with `⟨y, hy⟩`. Take `⟨T, c, η, r, hη1, hr1, hrMir, hηr, ⟨Cl, hClc, hClU, hClB, hCl⟩, hmain⟩` from `hS9 (v.adicCompletion E) k (m v) hmv (chi ψ v) (chi_cont hψ v) hne (XB E k) (repW k v) U' hU'`. Establish `hClU' : ∀ c ∈ Cl, fl k v c ∈ U` using `fun c hc => (hClU hc).2`. Establish `inS : ∀ u, InS S (fl k v u : GA E k)` using `fun u w hw => i5 v w u (fun e => hw (e ▸ hv))`.

Establish `stab : ∀ u, ∀ z ∈ Y, repW k v u z ∈ Y` using `fun u z hz => hY.stable _ (inS u) z hz`. Establish `hJx' : J (∑ t ∈ T, c t • ρ (fl k v t) x) = ∑ t ∈ T, c t • repW k v t (J x)`. Simplify using `only [map_sum, map_smul, hW.inter, repW_apply]`. Establish `hJY : J (∑ t ∈ T, c t • ρ (fl k v t) x) ∈ Y`. Rewrite using `[hJx']`.

Conclude with `Y.sum_mem fun t _ => Y.smul_mem _ (stab t _ hxY)`. Establish `hgood' : Good ψ (k - 1) (J (∑ t ∈ T, c t • ρ (fl k v t) x))` using `hY.good _ hJY`. Establish `key : ∀ g' : GA E k, cLoc v g' = 1 → ∀ h, GlobalTheory (m v + 1) h → Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (g' * fl k v h) = η h * Wh ψ (J x) (g' * fl k v (r h))`. Introduce `g' hg' h hh`. Take `⟨Λ, hΛ⟩` from `g5a g'`.

Establish `hcond : ∀ z ∈ Y, ∀ y : UnipotentBlockColumnIndex k (m v + 1) (m v + 1) → v.adicCompletion E, (Λ : XB E k →ₗ[ℂ] ℂ) (repW k v (blkU y) z) = chi ψ v (lastE (m v + 1) y) * (Λ : XB E k →ₗ[ℂ] ℂ) z`. Introduce `z hz y`. Use `show Λ _ = _ * Λ _`. Rewrite using `[hΛ _ (hY.good _ (stab _ z hz)), hΛ _ (hY.good _ hz), repW_apply, g5r, i8 v g' hg', i10, (g5c z (hY.good _ hz)).2.2 (m v + 1) (Nat.succ_pos _), lastE_loc, chi_apply]`. Use `hmain (J x) (fun u hu => hu.1) Y stab hxY (Λ : XB E k →ₗ[ℂ] ℂ) hcond h hh` as an intermediate fact.

Express the relevant statement in the definitionally equal form `Λ _ = η h * Λ _ at this`. Establish `hsum : ∑ t ∈ T, c t • repW k v t (J x) ∈ Y` using `by rw [← hJx']; exact hJY`. Rewrite `this` using `[hΛ _ (hY.good _ (stab _ _ hsum)), hΛ _ (hY.good _ (stab _ _ hxY)), repW_apply, repW_apply, g5r, g5r]`. Rewrite using `[hJx']`. Conclude with `this`.

Establish `hpre : Pre ψ 0 (Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)))` using `p2whit (k - 1) (by omega) _ (p2good _ _ hgood')`. Establish `hlawW : ∀ u, UU 0 u → ∀ z, Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (u * z) = psN ψ u * Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) z` using `fun u hu z => p2law 0 _ hpre u (p2uu u hu) z`. Establish `hpsN : ∀ u : GA E k, psN ψ u ≠ 0` using `fun u e0 => by`. Establish `h1` using `p2norm u`. Rewrite `h1` using `[e0, norm_zero]`.

Conclude with `zero_ne_one h1`. Use `⟨∑ t ∈ T, c t • ρ (fl k v t) x, fl k v '' Cl, ?_, hJY, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨c₂, hc₂, rfl⟩`. Conclude with `hClU' c₂ hc₂`. Use `sum_of _ s0 sadd ssmul T c _ fun t => sT (ρ (fl k v t)) (fun g z => ?_) x hsm` and prove the remaining obligations.

Simplify using `only [MonoidHom.comp_apply]`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, i7 _ (i3 v t) g, map_mul, ContinuousLinearMap.mul_apply]`. Rewrite using `[hJx']`. Conclude with `sum_of _ b5 b4 b3 T c _ fun t => by rw [repW_apply]; exact b2 _ _ hlev`. Introduce and unpack `_ ⟨c₂, hc₂, rfl⟩`.

Conclude with `blk_fl v (hClB c₂ hc₂)`. Take `⟨hCc, hCS, ⟨t₀, ht₀, hW1⟩, hCb⟩` from `hB`. Use `⟨hCc.mul (hClc.image (i14 v)), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨c₁, hc₁, _, ⟨c₂, hc₂, rfl⟩, rfl⟩ w hw`. Rewrite using `[map_mul, hCS c₁ hc₁ w hw, inS c₂ w hw, one_mul]`.

Establish `h1` using `key 1 (map_one _) 1 s10blk1`. Rewrite `h1` using `[hr1]`. Simplify using `only [map_one, mul_one] at h1`. Take `⟨s₁, hs₁, hηs₁⟩` from `hηr 1`. Establish `hs₁' : 0 < s₁` using `lt_of_le_of_ne hs₁ fun e0 => hη1 (by rw [hηs₁, ← e0, Complex.ofReal_zero])`.

Use `⟨s₁ * t₀, mul_pos hs₁' ht₀, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, hηs₁, hW1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `g hg hg0`.

Take `⟨hgI, hgL⟩` from `hg`. Establish `hgv : Mir (m v + 1) (cLoc v g)` using `by simpa using hgL v`. Take `⟨y, h, hh, hdec⟩` from `s10dec _ hgv`. Use `set g' : GA E k := g * (fl k v (cLoc v g))⁻¹ with hg'def`. Establish `hg' : cLoc v g' = 1` using `by rw [hg'def, map_mul, map_inv, i4, mul_inv_cancel]`.

Establish `e : g = blkU (fun t => sFin E (sLoc E v (y t))) * (g' * fl k v h)`. Rewrite using `[← i10, ← mul_assoc, ← i8 v g' hg', mul_assoc, ← map_mul, ← hdec, hg'def, inv_mul_cancel_right]`. Establish `hWg : Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) g = ψ (lastE (m v + 1) fun t => sFin E (sLoc E v (y t))) * (η h * Wh ψ (J x) (g' * fl k v (r h)))`. Rewrite using `[e, (g5c _ hgood').2.2 (m v + 1) (Nat.succ_pos _), key g' hg' h hh]`. Establish `hηh : η h ≠ 0` using `fun e0 => hg0 (by rw [hWg, e0]; simp)`.

Establish `hW'' : Wh ψ (J x) (g' * fl k v (r h)) ≠ 0` using `fun e0 => hg0 (by rw [hWg, e0]; simp)`. Take `⟨c₂, hc₂, hhc⟩` from `hCl h hh hηh`. Establish `hOm : Om n m (g' * fl k v (r h))`. Use `⟨?_, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hg'def, map_mul, map_inv, i3, i3, inv_one, mul_one, mul_one]`.

Conclude with `hgI`. Break down `eq_or_ne w v with rfl | hwv` into its components or cases. Rewrite using `[map_mul, hg', i4, one_mul]`. Conclude with `hrMir h hh hηh`. Rewrite using `[map_mul, hg'def, map_mul, map_inv, i5 v w _ hwv, i5 v w _ hwv, inv_one, mul_one, mul_one]`.

Simplify `hgL w` using `[hwv]`. Take `⟨nn₀, c₁, hc₁, t₁, hnn₀, hnnS, hgeq₀, ht₁, hWv⟩` from `hCb _ hOm hW''`. Take `⟨sh, hsh, hηsh⟩` from `hηr h`. Establish `hYg : (blkU fun t => sFin E (sLoc E v (y t)) : GA E k) = fl k v (blkU y)` using `(i10 v _ y).symm`. Establish `h2 : nn₀ * (c₁ * fl k v c₂) = g' * fl k v h`.

Rewrite using `[hhc, map_mul, ← mul_assoc g', hgeq₀, mul_assoc]`. Establish `hcc : Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (c₁ * fl k v c₂) = ((sh * t₁ : ℝ) : ℂ)`. Establish `h1` using `hlawW nn₀ hnn₀ (c₁ * fl k v c₂)`. Rewrite `h1` using `[h2, key g' hg' h hh, hWv, hηsh]`. Apply `mul_left_cancel₀ (hpsN nn₀)` to reduce the goal to its premises.

Rewrite using `[← h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `huu : UU 0 ((blkU fun t => sFin E (sLoc E v (y t))) * nn₀ : GA E k)` using `uu_mul (uu_blkU _) hnn₀`. Use `⟨(blkU fun t => sFin E (sLoc E v (y t))) * nn₀, c₁ * fl k v c₂, Set.mem_image2_of_mem hc₁ ⟨c₂, hc₂, rfl⟩, sh * t₁, huu, ?_, ?_, mul_nonneg hsh ht₁, ?_⟩` and prove the remaining obligations.

Introduce `w hw`. Rewrite using `[map_mul, hYg, i5 v w _ (fun e0 => hw (e0 ▸ hv)), hnnS w hw, one_mul]`. Rewrite using `[mul_assoc, h2]`. Conclude with `e`. Establish `hg2 : g = ((blkU fun t => sFin E (sLoc E v (y t))) * nn₀) * (c₁ * fl k v c₂)`.

Rewrite using `[mul_assoc, h2]`. Conclude with `e`. Rewrite using `[hg2, hlawW _ huu, hcc]`.
-/
theorem finite_place_of_jump_windows : jumpWindows.S2 → jumpWindows.S9 → jumpWindows.MirabolicColumnBlock → jumpWindows.G0 → jumpWindows.G5 → jumpWindows.G5b → P2 → FinitePlaceStep := by
  intro hS2 hS9 hS10 hG0 hG5 hG5b hP2 E _ _ _ k wt ρ J hW ψ hψ S Y hY n m v hv hmv hm0 U hU x C hxY hsm hlev hB
  obtain ⟨-, -, i3, i4, i5, -, i7, i8, -, i10, -, -, -, i14, -⟩ := hG0 E k
  obtain ⟨g5a, g5r, -, g5c⟩ := hG5 E k ψ hψ
  obtain ⟨-, b2, b3, b4, b5⟩ := hG5b E k S
  obtain ⟨s10dec, -, -, s10blk1, -⟩ := hS10 (v.adicCompletion E) k (m v + 1)
  obtain ⟨p2law, p2norm, p2uu, p2whit, -, p2good, -⟩ := hP2 E k ψ hψ
  obtain ⟨s0, sadd, ssmul, -, sT, -⟩ := hS2 (InfinitePlace E) k (XB E k) (ρ.comp (infGL E k)) hW.poly
  let U' : Set (GL (Fin k) (v.adicCompletion E)) := {u | repW k v u (J x) = J x} ∩ (fl k v) ⁻¹' U
  have hU' : U' ∈ 𝓝 (1 : GL (Fin k) (v.adicCompletion E)) :=
    Filter.inter_mem (hlev v hv) ((i14 v).continuousAt.preimage_mem_nhds (by rw [map_one]; exact hU))
  have hne : ∃ y, chi ψ v y ≠ 1 := by
    obtain ⟨y, hy⟩ := hψ.loc v
    exact ⟨y, hy⟩
  obtain ⟨T, c, η, r, hη1, hr1, hrMir, hηr, ⟨Cl, hClc, hClU, hClB, hCl⟩, hmain⟩ :=
    hS9 (v.adicCompletion E) k (m v) hmv (chi ψ v) (chi_cont hψ v) hne (XB E k) (repW k v) U' hU'
  have hClU' : ∀ c ∈ Cl, fl k v c ∈ U := fun c hc => (hClU hc).2
  have inS : ∀ u, InS S (fl k v u : GA E k) := fun u w hw => i5 v w u (fun e => hw (e ▸ hv))
  have stab : ∀ u, ∀ z ∈ Y, repW k v u z ∈ Y := fun u z hz => hY.stable _ (inS u) z hz
  have hJx' : J (∑ t ∈ T, c t • ρ (fl k v t) x) = ∑ t ∈ T, c t • repW k v t (J x) := by
    simp only [map_sum, map_smul, hW.inter, repW_apply]
  have hJY : J (∑ t ∈ T, c t • ρ (fl k v t) x) ∈ Y := by
    rw [hJx']
    exact Y.sum_mem fun t _ => Y.smul_mem _ (stab t _ hxY)
  have hgood' : Good ψ (k - 1) (J (∑ t ∈ T, c t • ρ (fl k v t) x)) := hY.good _ hJY
  have key : ∀ g' : GA E k, cLoc v g' = 1 → ∀ h, GlobalTheory (m v + 1) h →
      Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (g' * fl k v h) = η h * Wh ψ (J x) (g' * fl k v (r h)) := by
    intro g' hg' h hh
    obtain ⟨Λ, hΛ⟩ := g5a g'
    have hcond : ∀ z ∈ Y, ∀ y : UnipotentBlockColumnIndex k (m v + 1) (m v + 1) → v.adicCompletion E,
        (Λ : XB E k →ₗ[ℂ] ℂ) (repW k v (blkU y) z) = chi ψ v (lastE (m v + 1) y) * (Λ : XB E k →ₗ[ℂ] ℂ) z := by
      intro z hz y
      show Λ _ = _ * Λ _
      rw [hΛ _ (hY.good _ (stab _ z hz)),
        hΛ _ (hY.good _ hz), repW_apply, g5r, i8 v g' hg', i10,
        (g5c z (hY.good _ hz)).2.2 (m v + 1) (Nat.succ_pos _), lastE_loc, chi_apply]
    have := hmain (J x) (fun u hu => hu.1) Y stab hxY (Λ : XB E k →ₗ[ℂ] ℂ) hcond h hh
    change Λ _ = η h * Λ _ at this
    have hsum : ∑ t ∈ T, c t • repW k v t (J x) ∈ Y := by rw [← hJx']; exact hJY
    rw [hΛ _ (hY.good _ (stab _ _ hsum)), hΛ _ (hY.good _ (stab _ _ hxY)),
      repW_apply, repW_apply, g5r, g5r] at this
    rw [hJx']
    exact this
  have hpre : Pre ψ 0 (Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x))) :=
    p2whit (k - 1) (by omega) _ (p2good _ _ hgood')
  have hlawW : ∀ u, UU 0 u → ∀ z, Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (u * z) =
      psN ψ u * Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) z :=
    fun u hu z => p2law 0 _ hpre u (p2uu u hu) z
  have hpsN : ∀ u : GA E k, psN ψ u ≠ 0 := fun u e0 => by
    have h1 := p2norm u
    rw [e0, norm_zero] at h1
    exact zero_ne_one h1
  refine ⟨∑ t ∈ T, c t • ρ (fl k v t) x, fl k v '' Cl, ?_, hJY, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c₂, hc₂, rfl⟩
    exact hClU' c₂ hc₂
  · refine sum_of _ s0 sadd ssmul T c _ fun t => sT (ρ (fl k v t)) (fun g z => ?_) x hsm
    simp only [MonoidHom.comp_apply]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, i7 _ (i3 v t) g, map_mul, ContinuousLinearMap.mul_apply]
  · rw [hJx']
    exact sum_of _ b5 b4 b3 T c _ fun t => by rw [repW_apply]; exact b2 _ _ hlev
  · rintro _ ⟨c₂, hc₂, rfl⟩
    exact blk_fl v (hClB c₂ hc₂)
  obtain ⟨hCc, hCS, ⟨t₀, ht₀, hW1⟩, hCb⟩ := hB
  refine ⟨hCc.mul (hClc.image (i14 v)), ?_, ?_, ?_⟩
  · rintro _ ⟨c₁, hc₁, _, ⟨c₂, hc₂, rfl⟩, rfl⟩ w hw
    rw [map_mul, hCS c₁ hc₁ w hw, inS c₂ w hw, one_mul]
  · have h1 := key 1 (map_one _) 1 s10blk1
    rw [hr1] at h1
    simp only [map_one, mul_one] at h1
    obtain ⟨s₁, hs₁, hηs₁⟩ := hηr 1
    have hs₁' : 0 < s₁ := lt_of_le_of_ne hs₁ fun e0 => hη1 (by rw [hηs₁, ← e0, Complex.ofReal_zero])
    refine ⟨s₁ * t₀, mul_pos hs₁' ht₀, ?_⟩
    rw [h1, hηs₁, hW1]
    push_cast
    ring
  · intro g hg hg0
    obtain ⟨hgI, hgL⟩ := hg
    have hgv : Mir (m v + 1) (cLoc v g) := by simpa using hgL v
    obtain ⟨y, h, hh, hdec⟩ := s10dec _ hgv
    set g' : GA E k := g * (fl k v (cLoc v g))⁻¹ with hg'def
    have hg' : cLoc v g' = 1 := by rw [hg'def, map_mul, map_inv, i4, mul_inv_cancel]
    have e : g = blkU (fun t => sFin E (sLoc E v (y t))) * (g' * fl k v h) := by
      rw [← i10, ← mul_assoc, ← i8 v g' hg', mul_assoc, ← map_mul, ← hdec, hg'def, inv_mul_cancel_right]
    have hWg : Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) g =
        ψ (lastE (m v + 1) fun t => sFin E (sLoc E v (y t))) * (η h * Wh ψ (J x) (g' * fl k v (r h))) := by
      rw [e, (g5c _ hgood').2.2 (m v + 1) (Nat.succ_pos _), key g' hg' h hh]
    have hηh : η h ≠ 0 := fun e0 => hg0 (by rw [hWg, e0]; simp)
    have hW'' : Wh ψ (J x) (g' * fl k v (r h)) ≠ 0 := fun e0 => hg0 (by rw [hWg, e0]; simp)
    obtain ⟨c₂, hc₂, hhc⟩ := hCl h hh hηh
    have hOm : Om n m (g' * fl k v (r h)) := by
      refine ⟨?_, fun w => ?_⟩
      · rw [map_mul, hg'def, map_mul, map_inv, i3, i3, inv_one, mul_one, mul_one]
        exact hgI
      · rcases eq_or_ne w v with rfl | hwv
        · rw [map_mul, hg', i4, one_mul]
          exact hrMir h hh hηh
        · rw [map_mul, hg'def, map_mul, map_inv, i5 v w _ hwv, i5 v w _ hwv, inv_one, mul_one, mul_one]
          simpa [hwv] using hgL w
    obtain ⟨nn₀, c₁, hc₁, t₁, hnn₀, hnnS, hgeq₀, ht₁, hWv⟩ := hCb _ hOm hW''
    obtain ⟨sh, hsh, hηsh⟩ := hηr h
    have hYg : (blkU fun t => sFin E (sLoc E v (y t)) : GA E k) = fl k v (blkU y) := (i10 v _ y).symm
    have h2 : nn₀ * (c₁ * fl k v c₂) = g' * fl k v h := by
      rw [hhc, map_mul, ← mul_assoc g', hgeq₀, mul_assoc]
    have hcc : Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (c₁ * fl k v c₂) = ((sh * t₁ : ℝ) : ℂ) := by
      have h1 := hlawW nn₀ hnn₀ (c₁ * fl k v c₂)
      rw [h2, key g' hg' h hh, hWv, hηsh] at h1
      apply mul_left_cancel₀ (hpsN nn₀)
      rw [← h1]
      push_cast
      ring
    have huu : UU 0 ((blkU fun t => sFin E (sLoc E v (y t))) * nn₀ : GA E k) := uu_mul (uu_blkU _) hnn₀
    refine ⟨(blkU fun t => sFin E (sLoc E v (y t))) * nn₀, c₁ * fl k v c₂,
      Set.mem_image2_of_mem hc₁ ⟨c₂, hc₂, rfl⟩, sh * t₁, huu, ?_, ?_, mul_nonneg hsh ht₁, ?_⟩
    · intro w hw
      rw [map_mul, hYg, i5 v w _ (fun e0 => hw (e0 ▸ hv)), hnnS w hw, one_mul]
    · rw [mul_assoc, h2]
      exact e
    · have hg2 : g = ((blkU fun t => sFin E (sLoc E v (y t))) * nn₀) * (c₁ * fl k v c₂) := by
        rw [mul_assoc, h2]
        exact e
      rw [hg2, hlawW _ huu, hcc]

end PositivityTheory.AdelicQuotientData

end
