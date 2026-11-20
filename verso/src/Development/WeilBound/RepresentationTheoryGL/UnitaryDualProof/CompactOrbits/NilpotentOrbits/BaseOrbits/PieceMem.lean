import Mathlib
import GroundTheory.AutomorphicForms.WhittakerLSpace

noncomputable section

open Set GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Nil.BasePf

variable {Y W G : Type*} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace W] [T2Space W]
  [Group G] [MulAction G W]

def rel (K : Subgroup G) : Setoid W where
  r a b := ∃ g ∈ K, g • b = a
  iseqv :=
    { refl := fun a => ⟨1, K.one_mem, one_smul _ _⟩
      symm := fun {a b} ⟨g, hg, h⟩ => ⟨g⁻¹, K.inv_mem hg, by rw [← h, inv_smul_smul]⟩
      trans := fun {a b c} ⟨g, hg, h⟩ ⟨g', hg', h'⟩ => ⟨g * g', K.mul_mem hg hg', by rw [mul_smul, h', h]⟩ }

/- English proof (translation)
The claim follows from `Quotient.eq (r := rel K)`.
-/
theorem rel_iff (K : Subgroup G) (a b : W) :
    Quotient.mk (rel K) a = Quotient.mk (rel K) b ↔ ∃ g ∈ K, g • b = a :=
  Quotient.eq (r := rel K)

abbrev TF (X : Type*) [TopologicalSpace X] : Submodule ℂ (X → ℂ) :=
  GroundTheory.Automorphic.locallyConstantCompactSupport X ℂ ℂ

/- English proof (translation)
Use `⟨hF.1.comp_continuous (continuous_fst.prodMk (hg.comp continuous_snd)), ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro ((hF.2.isCompact).image (continuous_fst.prodMk (hg'.comp continuous_snd))) fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `hx ⟨(x.1, g • x.2), subset_tsupport _ h, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `all_goals simp`.
-/
theorem comp_mem {F : Y × W → ℂ} (hF : F ∈ TF (Y × W)) (g : G) (hg : Continuous fun w : W => g • w)
    (hg' : Continuous fun w : W => g⁻¹ • w) : (fun p : Y × W => F (p.1, g • p.2)) ∈ TF (Y × W) := by
  refine ⟨hF.1.comp_continuous (continuous_fst.prodMk (hg.comp continuous_snd)), ?_⟩
  refine HasCompactSupport.intro ((hF.2.isCompact).image
    (continuous_fst.prodMk (hg'.comp continuous_snd))) fun x hx => ?_
  by_contra h
  refine hx ⟨(x.1, g • x.2), subset_tsupport _ h, ?_⟩
  all_goals simp

/- English proof (translation)
Establish `h1 : IsLocallyConstant (U.indicator (1 : W → ℂ))` using `(LocallyConstant.indicator (LocallyConstant.const W (1 : ℂ)) ⟨hUc.isClosed, hUo⟩).isLocallyConstant`. Use `⟨(ha.1.comp_continuous continuous_fst).comp₂ (h1.comp_continuous continuous_snd) (· * ·), ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro (ha.2.isCompact.prod hUc) fun p hp => ?_` and prove the remaining obligations. Simplify using `only [mem_prod, not_and_or] at hp`. Break down `hp with h | h` into its components or cases.

Simplify using `[image_eq_zero_of_notMem_tsupport h]`. Simplify using `[Set.indicator_of_notMem h]`.
-/
theorem tens_mem {a : Y → ℂ} (ha : a ∈ TF Y) {U : Set W} (hUc : IsCompact U) (hUo : IsOpen U) :
    (fun p : Y × W => a p.1 * U.indicator 1 p.2) ∈ TF (Y × W) := by
  have h1 : IsLocallyConstant (U.indicator (1 : W → ℂ)) :=
    (LocallyConstant.indicator (LocallyConstant.const W (1 : ℂ)) ⟨hUc.isClosed, hUo⟩).isLocallyConstant
  refine ⟨(ha.1.comp_continuous continuous_fst).comp₂ (h1.comp_continuous continuous_snd) (· * ·), ?_⟩
  refine HasCompactSupport.intro (ha.2.isCompact.prod hUc) fun p hp => ?_
  simp only [mem_prod, not_and_or] at hp
  rcases hp with h | h
  · simp [image_eq_zero_of_notMem_tsupport h]
  · simp [Set.indicator_of_notMem h]

/- English proof (translation)
Use `⟨hF.1.comp_continuous (continuous_id.prodMk continuous_const), ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro (hF.2.isCompact.image continuous_fst) fun y hy => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hy ⟨(y, w), subset_tsupport _ h, rfl⟩`.
-/
theorem slice_mem {F : Y × W → ℂ} (hF : F ∈ TF (Y × W)) (w : W) : (fun y => F (y, w)) ∈ TF Y := by
  refine ⟨hF.1.comp_continuous (continuous_id.prodMk continuous_const), ?_⟩
  refine HasCompactSupport.intro (hF.2.isCompact.image continuous_fst) fun y hy => ?_
  by_contra h
  exact hy ⟨(y, w), subset_tsupport _ h, rfl⟩

open Classical in

/- English proof (translation)
Use `⟨?_, hF.2.mul_right⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `p`. Distinguish the cases in `hp : p.2 ∈ S`. Establish `hO : {w' | ∃ g ∈ K, g • p.2 = w'} ∈ nhds p.2` using `(hKo p.2 hp).mem_nhds ⟨1, K.one_mem, one_smul _ _⟩`.

Establish `h1` using `((IsLocallyConstant.iff_eventually_eq _).1 hF.1) p`. Establish `h2 : ∀ᶠ x : Y × W in nhds p, x.2 ∈ {w' | ∃ g ∈ K, g • p.2 = w'}` using `continuous_snd.continuousAt.preimage_mem_nhds hO`. Use `filter_upwards [h1, h2] with x hx1 hx2`. Take `⟨g, hg, hgx⟩` from `hx2`. Establish `: Quotient.mk (rel K) x.2 = Quotient.mk (rel K) p.2` using `(rel_iff K _ _).2 ⟨g, hg, hgx⟩`.

Rewrite using `[hx1, this]`. Establish `h0 : F p = 0` using `hFS p hp`. Establish `h1` using `((IsLocallyConstant.iff_eventually_eq _).1 hF.1) p`. Use `filter_upwards [h1] with x hx1`. Rewrite using `[hx1, h0, zero_mul, zero_mul]`.
-/
theorem piece_mem (K : Subgroup G) (S : Set W) (hKo : ∀ w ∈ S, IsOpen {w' | ∃ g ∈ K, g • w = w'})
    {F : Y × W → ℂ} (hF : F ∈ TF (Y × W)) (hFS : ∀ p : Y × W, p.2 ∉ S → F p = 0)
    (q : Quotient (rel K)) :
    (fun p : Y × W => F p * if Quotient.mk (rel K) p.2 = q then 1 else 0) ∈ TF (Y × W) := by
  refine ⟨?_, hF.2.mul_right⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p
  by_cases hp : p.2 ∈ S
  · have hO : {w' | ∃ g ∈ K, g • p.2 = w'} ∈ nhds p.2 := (hKo p.2 hp).mem_nhds ⟨1, K.one_mem, one_smul _ _⟩
    have h1 := ((IsLocallyConstant.iff_eventually_eq _).1 hF.1) p
    have h2 : ∀ᶠ x : Y × W in nhds p, x.2 ∈ {w' | ∃ g ∈ K, g • p.2 = w'} :=
      continuous_snd.continuousAt.preimage_mem_nhds hO
    filter_upwards [h1, h2] with x hx1 hx2
    obtain ⟨g, hg, hgx⟩ := hx2
    have : Quotient.mk (rel K) x.2 = Quotient.mk (rel K) p.2 := (rel_iff K _ _).2 ⟨g, hg, hgx⟩
    rw [hx1, this]
  · have h0 : F p = 0 := hFS p hp
    have h1 := ((IsLocallyConstant.iff_eventually_eq _).1 hF.1) p
    filter_upwards [h1] with x hx1
    rw [hx1, h0, zero_mul, zero_mul]

variable {ι : Type*}

open Classical in
/- English proof (translation)
Use `set tL : Set W := {w | t⁻¹ • w ∈ L} with htLdef`. Establish `htLc : IsClopen tL` using `⟨hLc.isClosed.preimage (hcont t⁻¹), hLo.preimage (hcont t⁻¹)⟩`. Use `set B : Set W := L ∩ tLᶜ with hBdef`. Establish `hBc : IsCompact B` using `hLc.inter_right htLc.compl.isClosed`. Establish `hBo : IsOpen B` using `hLo.inter htLc.isClosed.isOpen_compl`.

Establish `hBS : B ⊆ S` using `fun w hw => hLS w hw.1 hw.2`. Establish `hBK : ∀ i, ∀ g ∈ K i, ∀ w ∈ B, g • w ∈ B`. Introduce `i g hg w hw`. Use `⟨hLK i g hg w hw.1, fun h => hw.2 ?_⟩` and prove the remaining obligations. Establish `h' : g⁻¹ • (t⁻¹ • (g • w)) ∈ L` using `hLK i g⁻¹ ((K i).inv_mem hg) _ h`.

Establish `e : g⁻¹ • (t⁻¹ • (g • w)) = t⁻¹ • w`. Rewrite using `[← mul_smul, ← mul_smul, hcomm g⁻¹ t⁻¹, mul_assoc, inv_mul_cancel, mul_one]`. Use `show t⁻¹ • w ∈ L`. Rewrite `h'` using `[e]`. Then use the resulting hypothesis. Establish `claimA : ∀ i, ∀ F ∈ TF (Y × W), (∀ g ∈ K i, ∀ p : Y × W, F (p.1, g • p.2) = F p) → (∀ p : Y × W, F p ≠ 0 → ∃ g ∈ K i, g • w0 = p.2) → D F = 0`.

Introduce `i F hF hFK hFO`. Use `set a : Y → ℂ := fun y => F (y, w0) with ha`. Establish `haT : a ∈ TF Y` using `slice_mem hF w0`. Use `set Φ : Y × W → ℂ := fun p => a p.1 * B.indicator 1 p.2 with hΦ`. Establish `hΦT : Φ ∈ TF (Y × W)` using `tens_mem haT hBc hBo`.

Establish `hΦ0 : D Φ = 0` using `by set ΦL : Y × W → ℂ := fun p => a p.1 * L.indicator 1 p.2`. Establish `hLT : ΦL ∈ TF (Y × W)` using `tens_mem haT hLc hLo`. Establish `e1 : (fun p : Y × W => ΦL (p.1, t⁻¹ • p.2)) = fun p => a p.1 * tL.indicator 1 p.2`. Use function extensionality and compare the values at `p`. Distinguish the cases in `h : t⁻¹ • p.2 ∈ L`.

Simplify using `[ΦL, Set.indicator_of_mem h, Set.indicator_of_mem (show p.2 ∈ tL from h)]`. Simplify using `[ΦL, Set.indicator_of_notMem h, Set.indicator_of_notMem (show p.2 ∉ tL from h)]`. Establish `e2 : Φ = ΦL - fun p => a p.1 * tL.indicator 1 p.2`. Use function extensionality and compare the values at `p`. Simplify using `only [Φ, ΦL, Pi.sub_apply, B]`.

Distinguish the cases in `h1 : p.2 ∈ tL`. Establish `h2 : p.2 ∈ L` using `htL _ h1`. Simplify using `[Set.indicator_of_mem h1, Set.indicator_of_mem h2, Set.indicator_of_notMem (show p.2 ∉ L ∩ tLᶜ from fun h => h.2 h1)]`. Distinguish the cases in `h2 : p.2 ∈ L`. Simplify using `[Set.indicator_of_notMem h1, Set.indicator_of_mem h2, Set.indicator_of_mem (show p.2 ∈ L ∩ tLᶜ from ⟨h2, h1⟩)]`.

Simplify using `[Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, Set.indicator_of_notMem (show p.2 ∉ L ∩ tLᶜ from fun h => h2 h.1)]`. Rewrite using `[e2, map_sub, ← e1, hD t⁻¹ ΦL hLT, sub_self]`. Take `⟨b, hbB, hbfin, hbcov⟩` from `hBc.elim_finite_subcover_image (b := B) (c := fun r => {w' | ∃ g ∈ K i, g • r = w'}) (fun r hr => hKo i r (hBS hr)) (fun w hw => mem_iUnion₂.2 ⟨w, hw, 1, (K i).one_mem, one_smul _ _⟩)`. Use `set Q : Finset (Quotient (rel (K i))) := hbfin.toFinset.image (Quotient.mk (rel (K i))) with hQ`. Establish `hΦsum : Φ = ∑ q ∈ Q, fun p : Y × W => Φ p * if Quotient.mk (rel (K i)) p.2 = q then 1 else 0`.

Use function extensionality and compare the values at `p`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_const_zero]`. Distinguish the cases in `hp : p.2 ∈ B`. Take `⟨r, hr, g, hg, hgr⟩` from `mem_iUnion₂.1 (hbcov hp)`.

Establish `: Quotient.mk (rel (K i)) p.2 ∈ Q` using `Finset.mem_image.2 ⟨r, hbfin.mem_toFinset.2 hr, ((rel_iff _ _ _).2 ⟨g, hg, hgr⟩).symm⟩`. Simplify using `[this]`. Simplify using `[Φ, Set.indicator_of_notMem hp]`. Establish `hpiece : ∀ q ∈ Q, D (fun p : Y × W => Φ p * if Quotient.mk (rel (K i)) p.2 = q then 1 else 0) = D F`. Introduce `q hq`.

Take `⟨r, hr, rfl⟩` from `Finset.mem_image.1 hq`. Establish `hrB : r ∈ B` using `hbB (hbfin.mem_toFinset.1 hr)`. Take `⟨h, hh⟩` from `htr r (hBS hrB)`. Establish `hPT` using `piece_mem (K i) S (hKo i) hΦT (fun p hp => by simp [Φ, Set.indicator_of_notMem (fun h' => hp (hBS h'))]) (Quotient.mk (rel (K i)) r)`. Rewrite using `[← hD h _ hPT]`.

Use `congr 1`. Use function extensionality and compare the values at `p`. Establish `key : Quotient.mk (rel (K i)) (h • p.2) = Quotient.mk (rel (K i)) r ↔ ∃ g ∈ K i, g • w0 = p.2`. Rewrite using `[rel_iff, ← hh]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨g, hg, hgx⟩`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Establish `: h • (g • w0) = h • p.2` using `by rw [← hgx, ← mul_smul, ← mul_smul, hcomm]`. Conclude with `smul_left_cancel h this`. Introduce and unpack `⟨g, hg, hgx⟩`.

Conclude with `⟨g, hg, by rw [← hgx, ← mul_smul, ← mul_smul, hcomm]⟩`. Distinguish the cases in `hp : ∃ g ∈ K i, g • w0 = p.2`. Establish `hk` using `key.2 hp`. Take `⟨g, hg, hgx⟩` from `hp`. Establish `hhB : h • p.2 ∈ B`.

Rewrite using `[← hgx, ← mul_smul, hcomm, mul_smul, hh]`. Conclude with `hBK i g hg r hrB`. Simplify using `only [Φ, Set.indicator_of_mem hhB, hk, if_true, Pi.one_apply, mul_one, a]`. Establish `e3` using `hFK g hg (p.1, w0)`. Simplify using `only [hgx] at e3`.

Rewrite using `[← e3]`. Establish `hk : ¬ Quotient.mk (rel (K i)) (h • p.2) = Quotient.mk (rel (K i)) r` using `fun h' => hp (key.1 h')`. Simplify using `only [hk, if_false, mul_zero]`. Assume the negation of the conclusion as `h0`. Conclude with `hp (hFO p (Ne.symm h0))`.

Establish `hQne : Q.Nonempty`. Take `⟨w, hwL, hwt⟩` from `hne`. Establish `hwB : w ∈ B` using `⟨hwL, hwt⟩`. Take `⟨r, hr, -⟩` from `mem_iUnion₂.1 (hbcov hwB)`. Conclude with `⟨_, Finset.mem_image.2 ⟨r, hbfin.mem_toFinset.2 hr, rfl⟩⟩`.

Establish `hsum : D Φ = (Q.card : ℂ) * D F` using `by conv_lhs => rw [hΦsum]`. Rewrite using `[map_sum, Finset.sum_congr rfl hpiece, Finset.sum_const, nsmul_eq_mul]`. Rewrite `hsum` using `[hΦ0]`. Establish `hc : (Q.card : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hQne)`. Conclude with `(mul_eq_zero.1 hsum.symm).resolve_left hc`.

Introduce `f hf`. Take `⟨i, hfK⟩` from `hKf f hf`. Establish `hfT : f ∈ TF (Y × W)` using `hf.1`. Establish `hfS : ∀ p : Y × W, p.2 ∉ S → f p = 0` using `fun p hp => by`. Assume the negation of the conclusion as `h`.

Conclude with `hp (hf.2 h).2`. Use `set C : Set W := Prod.snd '' Function.support f`. Establish `hCc : IsCompact C` using `(isCompact_support hf.1).image continuous_snd`. Establish `hCS : C ⊆ S`. Introduce and unpack `_ ⟨p, hp, rfl⟩`.

Conclude with `(hf.2 hp).2`. Take `⟨b, hbC, hbfin, hbcov⟩` from `hCc.elim_finite_subcover_image (b := C) (c := fun r => {w' | ∃ g ∈ K i, g • r = w'}) (fun r hr => hKo i r (hCS hr)) (fun w hw => mem_iUnion₂.2 ⟨w, hw, 1, (K i).one_mem, one_smul _ _⟩)`. Use `set Q : Finset (Quotient (rel (K i))) := hbfin.toFinset.image (Quotient.mk (rel (K i))) with hQ`. Establish `hfsum : f = ∑ q ∈ Q, fun p : Y × W => f p * if Quotient.mk (rel (K i)) p.2 = q then 1 else 0`. Use function extensionality and compare the values at `p`.

Rewrite using `[Finset.sum_apply]`. Simplify using `only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_const_zero]`. Distinguish the cases in `hp : f p = 0`. Simplify using `[hp]`. Take `⟨r, hr, g, hg, hgr⟩` from `mem_iUnion₂.1 (hbcov ⟨p, hp, rfl⟩)`.

Establish `: Quotient.mk (rel (K i)) p.2 ∈ Q` using `Finset.mem_image.2 ⟨r, hbfin.mem_toFinset.2 hr, ((rel_iff _ _ _).2 ⟨g, hg, hgr⟩).symm⟩`. Simplify using `[this]`. Rewrite using `[hfsum, map_sum]`. Use `Finset.sum_eq_zero fun q hq => ?_` and prove the remaining obligations. Take `⟨r, hr, rfl⟩` from `Finset.mem_image.1 hq`.

Establish `hrS : r ∈ S` using `hCS (hbC (hbfin.mem_toFinset.1 hr))`. Take `⟨h, hh⟩` from `htr r hrS`. Establish `hPT` using `piece_mem (K i) S (hKo i) hfT hfS (Quotient.mk (rel (K i)) r)`. Rewrite using `[← hD h _ hPT]`. Use `claimA i _ (comp_mem hPT h (hcont h) (hcont h⁻¹)) ?_ ?_` and prove the remaining obligations.

Introduce `g hg p`. Establish `e : Quotient.mk (rel (K i)) (g • h • p.2) = Quotient.mk (rel (K i)) (h • p.2)` using `(rel_iff _ _ _).2 ⟨g, hg, rfl⟩`. Establish `e2 : h • g • p.2 = g • h • p.2` using `by rw [← mul_smul, ← mul_smul, hcomm]`. Establish `e3` using `hfK g hg (p.1, h • p.2)`. Simplify using `only at e3`.

Simplify using `only [e2]`. Rewrite using `[e, e3]`. Introduce `p hp`. Establish `hk : Quotient.mk (rel (K i)) (h • p.2) = Quotient.mk (rel (K i)) r`. Assume the negation of the conclusion as `hk`.

Conclude with `hp (by simp [hk])`. Take `⟨g, hg, hgx⟩` from `(rel_iff _ _ _).1 hk`. Use `⟨g, hg, smul_left_cancel h ?_⟩` and prove the remaining obligations. Rewrite using `[← hgx, ← hh, ← mul_smul, ← mul_smul, hcomm]`.
-/
theorem core (hcomm : ∀ a b : G, a * b = b * a) (hcont : ∀ g : G, Continuous fun w : W => g • w)
    (D : (Y × W → ℂ) →ₗ[ℂ] ℂ)
    (hD : ∀ g : G, ∀ f ∈ TF (Y × W), D (fun p => f (p.1, g • p.2)) = D f)
    (S : Set W) (w0 : W) (htr : ∀ w ∈ S, ∃ g : G, g • w0 = w)
    (K : ι → Subgroup G) (hKo : ∀ i, ∀ w ∈ S, IsOpen {w' | ∃ g ∈ K i, g • w = w'})
    (hKf : ∀ f ∈ supportedIn (univ ×ˢ S : Set (Y × W)), ∃ i, ∀ g ∈ K i, ∀ p : Y × W, f (p.1, g • p.2) = f p)
    (t : G) (L : Set W) (hLc : IsCompact L) (hLo : IsOpen L) (hLK : ∀ i, ∀ g ∈ K i, ∀ w ∈ L, g • w ∈ L)
    (htL : ∀ w, t⁻¹ • w ∈ L → w ∈ L) (hLS : ∀ w ∈ L, t⁻¹ • w ∉ L → w ∈ S)
    (hne : ∃ w ∈ L, t⁻¹ • w ∉ L) :
    ∀ f ∈ supportedIn (univ ×ˢ S : Set (Y × W)), D f = 0 := by

  set tL : Set W := {w | t⁻¹ • w ∈ L} with htLdef
  have htLc : IsClopen tL := ⟨hLc.isClosed.preimage (hcont t⁻¹), hLo.preimage (hcont t⁻¹)⟩
  set B : Set W := L ∩ tLᶜ with hBdef
  have hBc : IsCompact B := hLc.inter_right htLc.compl.isClosed
  have hBo : IsOpen B := hLo.inter htLc.isClosed.isOpen_compl
  have hBS : B ⊆ S := fun w hw => hLS w hw.1 hw.2
  have hBK : ∀ i, ∀ g ∈ K i, ∀ w ∈ B, g • w ∈ B := by
    intro i g hg w hw
    refine ⟨hLK i g hg w hw.1, fun h => hw.2 ?_⟩
    have h' : g⁻¹ • (t⁻¹ • (g • w)) ∈ L := hLK i g⁻¹ ((K i).inv_mem hg) _ h
    have e : g⁻¹ • (t⁻¹ • (g • w)) = t⁻¹ • w := by
      rw [← mul_smul, ← mul_smul, hcomm g⁻¹ t⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    show t⁻¹ • w ∈ L
    rwa [e] at h'

  have claimA : ∀ i, ∀ F ∈ TF (Y × W), (∀ g ∈ K i, ∀ p : Y × W, F (p.1, g • p.2) = F p) →
      (∀ p : Y × W, F p ≠ 0 → ∃ g ∈ K i, g • w0 = p.2) → D F = 0 := by
    intro i F hF hFK hFO
    set a : Y → ℂ := fun y => F (y, w0) with ha
    have haT : a ∈ TF Y := slice_mem hF w0
    set Φ : Y × W → ℂ := fun p => a p.1 * B.indicator 1 p.2 with hΦ
    have hΦT : Φ ∈ TF (Y × W) := tens_mem haT hBc hBo

    have hΦ0 : D Φ = 0 := by
      set ΦL : Y × W → ℂ := fun p => a p.1 * L.indicator 1 p.2
      have hLT : ΦL ∈ TF (Y × W) := tens_mem haT hLc hLo
      have e1 : (fun p : Y × W => ΦL (p.1, t⁻¹ • p.2)) = fun p => a p.1 * tL.indicator 1 p.2 := by
        funext p
        by_cases h : t⁻¹ • p.2 ∈ L
        · simp [ΦL, Set.indicator_of_mem h, Set.indicator_of_mem (show p.2 ∈ tL from h)]
        · simp [ΦL, Set.indicator_of_notMem h, Set.indicator_of_notMem (show p.2 ∉ tL from h)]
      have e2 : Φ = ΦL - fun p => a p.1 * tL.indicator 1 p.2 := by
        funext p
        simp only [Φ, ΦL, Pi.sub_apply, B]
        by_cases h1 : p.2 ∈ tL
        · have h2 : p.2 ∈ L := htL _ h1
          simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
            Set.indicator_of_notMem (show p.2 ∉ L ∩ tLᶜ from fun h => h.2 h1)]
        · by_cases h2 : p.2 ∈ L
          · simp [Set.indicator_of_notMem h1, Set.indicator_of_mem h2,
              Set.indicator_of_mem (show p.2 ∈ L ∩ tLᶜ from ⟨h2, h1⟩)]
          · simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
              Set.indicator_of_notMem (show p.2 ∉ L ∩ tLᶜ from fun h => h2 h.1)]
      rw [e2, map_sub, ← e1, hD t⁻¹ ΦL hLT, sub_self]

    obtain ⟨b, hbB, hbfin, hbcov⟩ := hBc.elim_finite_subcover_image (b := B)
      (c := fun r => {w' | ∃ g ∈ K i, g • r = w'}) (fun r hr => hKo i r (hBS hr))
      (fun w hw => mem_iUnion₂.2 ⟨w, hw, 1, (K i).one_mem, one_smul _ _⟩)
    set Q : Finset (Quotient (rel (K i))) := hbfin.toFinset.image (Quotient.mk (rel (K i))) with hQ
    have hΦsum : Φ = ∑ q ∈ Q, fun p : Y × W => Φ p * if Quotient.mk (rel (K i)) p.2 = q then 1 else 0 := by
      funext p
      rw [Finset.sum_apply]
      simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_const_zero]
      by_cases hp : p.2 ∈ B
      · obtain ⟨r, hr, g, hg, hgr⟩ := mem_iUnion₂.1 (hbcov hp)
        have : Quotient.mk (rel (K i)) p.2 ∈ Q :=
          Finset.mem_image.2 ⟨r, hbfin.mem_toFinset.2 hr, ((rel_iff _ _ _).2 ⟨g, hg, hgr⟩).symm⟩
        simp [this]
      · simp [Φ, Set.indicator_of_notMem hp]
    have hpiece : ∀ q ∈ Q, D (fun p : Y × W => Φ p * if Quotient.mk (rel (K i)) p.2 = q then 1 else 0) = D F := by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
      have hrB : r ∈ B := hbB (hbfin.mem_toFinset.1 hr)
      obtain ⟨h, hh⟩ := htr r (hBS hrB)
      have hPT := piece_mem (K i) S (hKo i) hΦT
        (fun p hp => by simp [Φ, Set.indicator_of_notMem (fun h' => hp (hBS h'))])
        (Quotient.mk (rel (K i)) r)
      rw [← hD h _ hPT]
      congr 1
      funext p
      have key : Quotient.mk (rel (K i)) (h • p.2) = Quotient.mk (rel (K i)) r ↔ ∃ g ∈ K i, g • w0 = p.2 := by
        rw [rel_iff, ← hh]
        constructor
        · rintro ⟨g, hg, hgx⟩
          refine ⟨g, hg, ?_⟩
          have : h • (g • w0) = h • p.2 := by rw [← hgx, ← mul_smul, ← mul_smul, hcomm]
          exact smul_left_cancel h this
        · rintro ⟨g, hg, hgx⟩
          exact ⟨g, hg, by rw [← hgx, ← mul_smul, ← mul_smul, hcomm]⟩
      by_cases hp : ∃ g ∈ K i, g • w0 = p.2
      · have hk := key.2 hp
        obtain ⟨g, hg, hgx⟩ := hp
        have hhB : h • p.2 ∈ B := by
          rw [← hgx, ← mul_smul, hcomm, mul_smul, hh]
          exact hBK i g hg r hrB
        simp only [Φ, Set.indicator_of_mem hhB, hk, if_true, Pi.one_apply, mul_one, a]
        have e3 := hFK g hg (p.1, w0)
        simp only [hgx] at e3
        rw [← e3]
      · have hk : ¬ Quotient.mk (rel (K i)) (h • p.2) = Quotient.mk (rel (K i)) r := fun h' => hp (key.1 h')
        simp only [hk, if_false, mul_zero]
        by_contra h0
        exact hp (hFO p (Ne.symm h0))
    have hQne : Q.Nonempty := by
      obtain ⟨w, hwL, hwt⟩ := hne
      have hwB : w ∈ B := ⟨hwL, hwt⟩
      obtain ⟨r, hr, -⟩ := mem_iUnion₂.1 (hbcov hwB)
      exact ⟨_, Finset.mem_image.2 ⟨r, hbfin.mem_toFinset.2 hr, rfl⟩⟩
    have hsum : D Φ = (Q.card : ℂ) * D F := by
      conv_lhs => rw [hΦsum]
      rw [map_sum, Finset.sum_congr rfl hpiece, Finset.sum_const, nsmul_eq_mul]
    rw [hΦ0] at hsum
    have hc : (Q.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hQne)
    exact (mul_eq_zero.1 hsum.symm).resolve_left hc

  intro f hf
  obtain ⟨i, hfK⟩ := hKf f hf
  have hfT : f ∈ TF (Y × W) := hf.1
  have hfS : ∀ p : Y × W, p.2 ∉ S → f p = 0 := fun p hp => by
    by_contra h
    exact hp (hf.2 h).2
  set C : Set W := Prod.snd '' Function.support f
  have hCc : IsCompact C := (isCompact_support hf.1).image continuous_snd
  have hCS : C ⊆ S := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hf.2 hp).2
  obtain ⟨b, hbC, hbfin, hbcov⟩ := hCc.elim_finite_subcover_image (b := C)
    (c := fun r => {w' | ∃ g ∈ K i, g • r = w'}) (fun r hr => hKo i r (hCS hr))
    (fun w hw => mem_iUnion₂.2 ⟨w, hw, 1, (K i).one_mem, one_smul _ _⟩)
  set Q : Finset (Quotient (rel (K i))) := hbfin.toFinset.image (Quotient.mk (rel (K i))) with hQ
  have hfsum : f = ∑ q ∈ Q, fun p : Y × W => f p * if Quotient.mk (rel (K i)) p.2 = q then 1 else 0 := by
    funext p
    rw [Finset.sum_apply]
    simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_const_zero]
    by_cases hp : f p = 0
    · simp [hp]
    · obtain ⟨r, hr, g, hg, hgr⟩ := mem_iUnion₂.1 (hbcov ⟨p, hp, rfl⟩)
      have : Quotient.mk (rel (K i)) p.2 ∈ Q :=
        Finset.mem_image.2 ⟨r, hbfin.mem_toFinset.2 hr, ((rel_iff _ _ _).2 ⟨g, hg, hgr⟩).symm⟩
      simp [this]
  rw [hfsum, map_sum]
  refine Finset.sum_eq_zero fun q hq => ?_
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
  have hrS : r ∈ S := hCS (hbC (hbfin.mem_toFinset.1 hr))
  obtain ⟨h, hh⟩ := htr r hrS
  have hPT := piece_mem (K i) S (hKo i) hfT hfS (Quotient.mk (rel (K i)) r)
  rw [← hD h _ hPT]
  refine claimA i _ (comp_mem hPT h (hcont h) (hcont h⁻¹)) ?_ ?_
  · intro g hg p
    have e : Quotient.mk (rel (K i)) (g • h • p.2) = Quotient.mk (rel (K i)) (h • p.2) :=
      (rel_iff _ _ _).2 ⟨g, hg, rfl⟩
    have e2 : h • g • p.2 = g • h • p.2 := by rw [← mul_smul, ← mul_smul, hcomm]
    have e3 := hfK g hg (p.1, h • p.2)
    simp only at e3
    simp only [e2]
    rw [e, e3]
  · intro p hp
    have hk : Quotient.mk (rel (K i)) (h • p.2) = Quotient.mk (rel (K i)) r := by
      by_contra hk
      exact hp (by simp [hk])
    obtain ⟨g, hg, hgx⟩ := (rel_iff _ _ _).1 hk
    refine ⟨g, hg, smul_left_cancel h ?_⟩
    rw [← hgx, ← hh, ← mul_smul, ← mul_smul, hcomm]

end PositivityTheory.RgUd.T.Nil.BasePf
