import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Establish `hfi : ∀ i, (Function.support (fun k : κ i => f ⟨i, k⟩)).Finite` using `fun i => hf.preimage (fun a _ b _ h => sigma_mk_injective h)`. Rewrite using `[finsum_eq_sum_of_support_subset f (s := hf.toFinset) (by simp)]`. Establish `hg : Function.support (fun i => ∑ᶠ k, f ⟨i, k⟩) ⊆ ↑(hf.toFinset.image Sigma.fst)`. Introduce `i hi`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, f ⟨i, k⟩ ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hi (finsum_eq_zero_of_forall_eq_zero h)`. Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe]`. Conclude with `⟨⟨i, k⟩, by simpa using hk, rfl⟩`.

Rewrite using `[finsum_eq_sum_of_support_subset _ hg]`. Establish `hk : ∀ i, ∑ᶠ k, f ⟨i, k⟩ = ∑ k ∈ (hfi i).toFinset, f ⟨i, k⟩` using `fun i => finsum_eq_sum_of_support_subset _ (by simp)`. Repeatedly rewrite using `[hk]`. Rewrite using `[← Finset.sum_sigma]`. Apply `Finset.sum_congr ?_ (fun _ _ => rfl)` to reduce the goal to its premises.

Use extensionality with `⟨i, k⟩`. Simplify using `only [Set.Finite.mem_toFinset, Function.mem_support, Finset.mem_sigma, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨⟨⟨i, k⟩, h, rfl⟩, h⟩`.

Introduce and unpack `⟨-, h⟩`. Conclude with `h`.
-/
private theorem finsum_sigma {I : Type} {κ : I → Type} (f : (Σ i, κ i) → ℂ)
    (hf : (Function.support f).Finite) : ∑ᶠ s, f s = ∑ᶠ i, ∑ᶠ k, f ⟨i, k⟩ := by
  classical
  have hfi : ∀ i, (Function.support (fun k : κ i => f ⟨i, k⟩)).Finite := fun i =>
    hf.preimage (fun a _ b _ h => sigma_mk_injective h)
  rw [finsum_eq_sum_of_support_subset f (s := hf.toFinset) (by simp)]
  have hg : Function.support (fun i => ∑ᶠ k, f ⟨i, k⟩) ⊆ ↑(hf.toFinset.image Sigma.fst) := by
    intro i hi
    obtain ⟨k, hk⟩ : ∃ k, f ⟨i, k⟩ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hi (finsum_eq_zero_of_forall_eq_zero h)
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨⟨i, k⟩, by simpa using hk, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hg]
  have hk : ∀ i, ∑ᶠ k, f ⟨i, k⟩ = ∑ k ∈ (hfi i).toFinset, f ⟨i, k⟩ := fun i =>
    finsum_eq_sum_of_support_subset _ (by simp)
  simp_rw [hk]
  rw [← Finset.sum_sigma]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ⟨i, k⟩
  simp only [Set.Finite.mem_toFinset, Function.mem_support, Finset.mem_sigma, Finset.mem_image]
  constructor
  · intro h
    exact ⟨⟨⟨i, k⟩, h, rfl⟩, h⟩
  · rintro ⟨-, h⟩
    exact h

private noncomputable def tm {p : ℕ} [Fact p.Prime] {G : HTGroup p} (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ)
    (K : Subgroup G.GAf) (S : Set G.GAf) (B : GlobalTheory.LKCx.Form G) (b : GlobalTheory.LKCx.Dat G v B.β) : ℂ :=
  ((Nat.card (GlobalTheory.LKCx.Form.Stab v B K (KHT p G.m G.n 1 G.Fw) b) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ y : GlobalTheory.LKCx.grp G B.β, if GlobalTheory.LKCx.FixL G v B.β y b.2.1 then
      (S.indicator (1 : G.GAf → ℂ)) (b.1.1⁻¹ * B.toAf y * b.1.1) *
        (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator (1 : Gr G 1 → ℂ))
          (b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * b.1.2) *
        c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v B.β y b.2.1) else 0

/- English proof (translation)
Establish `hcard : Nat.card (GlobalTheory.LKCx.Form.Stab v B K (KHT p G.m G.n 1 G.Fw) b) = 1`. Rewrite using `[Nat.card_eq_one_iff_unique]`. Use `⟨⟨fun s t => ?_⟩, ⟨LKCx.Stab.one G v B.β _ _ _ K _ b⟩⟩` and prove the remaining obligations. Take `⟨y, hy1, hy2, hy3⟩` from `s`. Take `⟨y', hy1', hy2', hy3'⟩` from `t`.

Establish `e1 : y = 1` using `hK y ⟨hy3, hy1, hy2⟩`. Establish `e2 : y' = 1` using `hK y' ⟨hy3', hy1', hy2'⟩`. Substitute `e1` using the available equality. Substitute `e2` using the available equality. Both sides reduce to the same expression.

Unfold `tm`. Rewrite using `[hcard, Nat.cast_one, inv_one, _root_.one_mul]`. Apply `finsum_congr` to reduce the goal to its premises. Introduce `y`. Unfold `Sees`.

Distinguish the cases in `hF : GlobalTheory.LKCx.FixL G v B.β y b.2.1`. Distinguish the cases in `h1 : b.1.1⁻¹ * B.toAf y * b.1.1 ∈ S`. Distinguish the cases in `h2 : b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * b.1.2 ∈ KHT p G.m G.n 1 G.Fw`. Simplify using `[hF, h1, h2]`. Simplify using `[hF, h1, h2]`.

Simplify using `[hF, h1]`. Simplify using `[hF]`.
-/
private theorem tm_eq {p : ℕ} [Fact p.Prime] {G : HTGroup p} (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ)
    (K : Subgroup G.GAf) (S : Set G.GAf) (B : GlobalTheory.LKCx.Form G) (b : GlobalTheory.LKCx.Dat G v B.β)
    (hK : ∀ y, Sees B (K : Set G.GAf) b y → y = 1) :
    tm v c K S B b = ∑ᶠ y : GlobalTheory.LKCx.grp G B.β, if Sees B S b y then
      c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v B.β y b.2.1) else 0 := by
  have hcard : Nat.card (GlobalTheory.LKCx.Form.Stab v B K (KHT p G.m G.n 1 G.Fw) b) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun s t => ?_⟩, ⟨LKCx.Stab.one G v B.β _ _ _ K _ b⟩⟩
    obtain ⟨y, hy1, hy2, hy3⟩ := s
    obtain ⟨y', hy1', hy2', hy3'⟩ := t
    have e1 : y = 1 := hK y ⟨hy3, hy1, hy2⟩
    have e2 : y' = 1 := hK y' ⟨hy3', hy1', hy2'⟩
    subst e1
    subst e2
    rfl
  unfold tm
  rw [hcard, Nat.cast_one, inv_one, _root_.one_mul]
  apply finsum_congr
  intro y
  unfold Sees
  by_cases hF : GlobalTheory.LKCx.FixL G v B.β y b.2.1
  · by_cases h1 : b.1.1⁻¹ * B.toAf y * b.1.1 ∈ S
    · by_cases h2 : b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * b.1.2 ∈ KHT p G.m G.n 1 G.Fw
      · simp [hF, h1, h2]
      · simp [hF, h1, h2]
    · simp [hF, h1]
  · simp [hF]

/- English proof (translation)
Introduce `hE p _ G v c K S hconj hK hS T Φ Fb w hx`. Set `g : LKCx.AllPts G v K (KHT p G.m G.n 1 G.Fw) → ℂ` to `fun s => tm v c K S (Quot.out s.1) (Quot.out s.2)`. Establish `key : ∀ x : T, g (Φ x) = if x ∈ Fb then w x else 0`. Introduce `x`. Take `⟨q, a, hΦ, hFb, hw⟩` from `hx x`.

Take `⟨pt, hpt⟩ : ∃ pt : LKCx.Form.Pts v (Quot.out q) K (KHT p G.m G.n 1 G.Fw), Quot.mk _ a = pt` from `⟨_, rfl⟩`. Rewrite `hΦ` using `[hpt]`. Establish `hmk : Quot.mk _ a = Quot.mk _ (Quot.out pt)` using `hpt.trans (Quot.out_eq pt).symm`. Take `⟨E, -, hE1⟩` from `hE p G v c (Quot.out q) K S hconj a (Quot.out pt) hmk`. Take `⟨E', -, hE2⟩` from `hE p G v c (Quot.out q) K S hconj (Quot.out pt) a hmk.symm`.

Establish `hg : g (Φ x) = g ⟨q, pt⟩` using `by rw [hΦ]`. Rewrite using `[hg]`. Use `show tm v c K S (Quot.out q) (Quot.out pt) = _`. Rewrite using `[tm_eq v c K S _ _ (hK _ _)]`. Distinguish the cases in `hxF : x ∈ Fb`.

Rewrite using `[if_pos hxF]`. Take `⟨y, hy⟩` from `hFb.1 hxF`. Establish `hy'` using `((hE1 y).1).1 hy`. Rewrite using `[finsum_eq_single _ (E y)]`. Rewrite using `[if_pos hy', ((hE1 y).2 hy).1, ((hE1 y).2 hy).2, hw y hy]`.

Introduce `y' hne`. Rewrite using `[if_neg]`. Introduce `hs`. Conclude with `hne (hS _ _ _ _ hs hy')`. Rewrite using `[if_neg hxF]`.

Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `y'`. Rewrite using `[if_neg]`. Introduce `hs`. Conclude with `hxF (hFb.2 ⟨E' y', ((hE2 y').1).1 hs⟩)`.

Establish `hsupp : Function.support (fun x => g (Φ x)) ⊆ ↑Fb`. Introduce `x hx0`. Assume the negation of the conclusion as `hn`. Conclude with `hx0 (by show g (Φ x) = 0; rw [key x, if_neg (show x ∉ Fb from hn)])`. Establish `hfin : (Function.support g).Finite`.

Apply `((Fb.finite_toSet).image Φ).subset` to reduce the goal to its premises. Introduce `s hs`. Use `⟨Φ.symm s, hsupp ?_, Φ.apply_symm_apply s⟩` and prove the remaining obligations. Use `show g (Φ (Φ.symm s)) ≠ 0`. Rewrite using `[Φ.apply_symm_apply]`.

Conclude with `hs`. Establish `h1 : RootSumWeights.cxTotalM G v c K (S.indicator 1) (KHT p G.m G.n 1 G.Fw) ((↑(KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1) = ∑ᶠ s, g s`. Rewrite using `[finsum_sigma g hfin]`. Both sides reduce to the same expression. Rewrite using `[h1, ← finsum_comp_equiv Φ, finsum_eq_sum_of_support_subset (fun x => g (Φ x)) hsupp]`.

Conclude with `Finset.sum_congr rfl (fun x hx => by rw [key, if_pos hx])`.
-/
theorem UpperTheory.Gal.W2.sumPts_of :
    UpperTheory.Gal.W2.EigSame → UpperTheory.Gal.W2.SumPts := by
  intro hE p _ G v c K S hconj hK hS T Φ Fb w hx
  classical
  let g : LKCx.AllPts G v K (KHT p G.m G.n 1 G.Fw) → ℂ := fun s => tm v c K S (Quot.out s.1) (Quot.out s.2)
  have key : ∀ x : T, g (Φ x) = if x ∈ Fb then w x else 0 := by
    intro x
    obtain ⟨q, a, hΦ, hFb, hw⟩ := hx x
    obtain ⟨pt, hpt⟩ : ∃ pt : LKCx.Form.Pts v (Quot.out q) K (KHT p G.m G.n 1 G.Fw), Quot.mk _ a = pt := ⟨_, rfl⟩
    rw [hpt] at hΦ
    have hmk : Quot.mk _ a = Quot.mk _ (Quot.out pt) := hpt.trans (Quot.out_eq pt).symm
    obtain ⟨E, -, hE1⟩ := hE p G v c (Quot.out q) K S hconj a (Quot.out pt) hmk
    obtain ⟨E', -, hE2⟩ := hE p G v c (Quot.out q) K S hconj (Quot.out pt) a hmk.symm
    have hg : g (Φ x) = g ⟨q, pt⟩ := by rw [hΦ]
    rw [hg]
    show tm v c K S (Quot.out q) (Quot.out pt) = _
    rw [tm_eq v c K S _ _ (hK _ _)]
    by_cases hxF : x ∈ Fb
    · rw [if_pos hxF]
      obtain ⟨y, hy⟩ := hFb.1 hxF
      have hy' := ((hE1 y).1).1 hy
      rw [finsum_eq_single _ (E y)]
      · rw [if_pos hy', ((hE1 y).2 hy).1, ((hE1 y).2 hy).2, hw y hy]
      · intro y' hne
        rw [if_neg]
        intro hs
        exact hne (hS _ _ _ _ hs hy')
    · rw [if_neg hxF]
      apply finsum_eq_zero_of_forall_eq_zero
      intro y'
      rw [if_neg]
      intro hs
      exact hxF (hFb.2 ⟨E' y', ((hE2 y').1).1 hs⟩)
  have hsupp : Function.support (fun x => g (Φ x)) ⊆ ↑Fb := by
    intro x hx0
    by_contra hn
    exact hx0 (by show g (Φ x) = 0; rw [key x, if_neg (show x ∉ Fb from hn)])
  have hfin : (Function.support g).Finite := by
    apply ((Fb.finite_toSet).image Φ).subset
    intro s hs
    refine ⟨Φ.symm s, hsupp ?_, Φ.apply_symm_apply s⟩
    show g (Φ (Φ.symm s)) ≠ 0
    rw [Φ.apply_symm_apply]
    exact hs
  have h1 : RootSumWeights.cxTotalM G v c K (S.indicator 1) (KHT p G.m G.n 1 G.Fw)
      ((↑(KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1) = ∑ᶠ s, g s := by
    rw [finsum_sigma g hfin]
    rfl
  rw [h1, ← finsum_comp_equiv Φ, finsum_eq_sum_of_support_subset (fun x => g (Φ x)) hsupp]
  exact Finset.sum_congr rfl (fun x hx => by rw [key, if_pos hx])
