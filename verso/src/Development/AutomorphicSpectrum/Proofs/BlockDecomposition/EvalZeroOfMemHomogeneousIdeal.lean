import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoVanish

open HomogeneousLocalization MvPolynomial

variable {K : Type} [Field K] {N : ℕ}

/- English proof (translation)
Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Simplify using `only [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_zero]`.
-/
theorem away_mk_zero {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) (n : ℕ)
    (h0 : (0 : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n 0 h0 = 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_zero]

/- English proof (translation)
Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Simplify using `only [Away.val_mk, HomogeneousLocalization.val_add, Localization.add_mk_self]`.
-/
theorem away_mk_add {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) (n : ℕ)
    {a b : MvPolynomial (Fin (N + 1)) K} (ha : a ∈ grK K N (n • 1)) (hb : b ∈ grK K N (n • 1))
    (hab : a + b ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n (a + b) hab = Away.mk (grK K N) hx n a ha + Away.mk (grK K N) hx n b hb := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_add, Localization.add_mk_self]

/- English proof (translation)
Substitute `hn` using the available equality. Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Simplify using `only [Away.val_mk, HomogeneousLocalization.val_mul, Localization.mk_mul]`. Use `congr 1`. Conclude with `Subtype.ext (pow_add x k m)`.
-/
theorem away_mk_mul {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) {k m n : ℕ} (hn : k + m = n)
    {a b : MvPolynomial (Fin (N + 1)) K} (ha : a ∈ grK K N (k • 1)) (hb : b ∈ grK K N (m • 1))
    (hab : a * b ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n (a * b) hab = Away.mk (grK K N) hx k a ha * Away.mk (grK K N) hx m b hb := by
  subst hn
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_mul, Localization.mk_mul]
  congr 1
  exact Subtype.ext (pow_add x k m)

/- English proof (translation)
Establish `hmem : ∀ (q : MvPolynomial (Fin (N + 1)) K) (n : ℕ), (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (n • 1)`. Introduce `q n`. Simplify using `using (DirectSum.decompose (grK K N) q n).2`. Establish `hzero : ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)), f = (DirectSum.decompose (grK K N) (0 : MvPolynomial (Fin (N + 1)) K) n : MvPolynomial (Fin (N + 1)) K) → φ (Away.mk (grK K N) hx n f hf) = 0`. Introduce `n f hf h`.

Establish `h0 : f = 0` using `by simpa using h`. Substitute `h0` using the available equality. Rewrite using `[away_mk_zero, map_zero]`. Establish `hadd : ∀ (p q : MvPolynomial (Fin (N + 1)) K), (∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)), f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) → φ (Away.mk (grK K N) hx n f hf) = 0) → (∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) ( …`. Introduce `p q ihp ihq n f hf h`.

Establish `h' : f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) + (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K)`. Rewrite using `[h, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]`. Substitute `h'` using the available equality. Rewrite using `[away_mk_add hx n (hmem p n) (hmem q n), map_add, ihp n _ _ rfl, ihq n _ _ rfl, add_zero]`. Proceed by induction on `hp using Submodule.span_induction with`.

Consider the case `mem p hp`. Take `⟨d, hd, h0⟩` from `hS p hp`. Introduce `n f hf h`. Establish `hd' : p ∈ grK K N d` using `by simpa using hd`. Distinguish the cases in `hnd : n = d`.

Substitute `hnd` using the available equality. Establish `: f = p` using `h.trans (DirectSum.decompose_of_mem_same _ hd')`. Substitute `this` using the available equality. Conclude with `h0`. Establish `h1 : f = 0` using `h.trans (DirectSum.decompose_of_mem_ne _ hd' (Ne.symm hnd))`.

Substitute `h1` using the available equality. Rewrite using `[away_mk_zero, map_zero]`. Consider the case `zero => exact hzero`. Consider the case `add p q _ _ ihp ihq => exact hadd p q ihp ihq`. Consider the case `smul a p _ ih`.

Proceed by induction on `a using DirectSum.Decomposition.inductionOn (grK K N) with`. Consider the case `zero => simpa using hzero`. Consider the case `@homogeneous k m`. Introduce `n f hf h`. Rewrite `h` using `[smul_eq_mul]`.

Distinguish the cases in `hk : k ≤ n`. Rewrite `h` using `[DirectSum.coe_decompose_mul_of_left_mem_of_le _ m.2 hk]`. Substitute `h` using the available equality. Establish `hm1 : (m : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (k • 1)` using `by simpa using m.2`. Rewrite using `[away_mk_mul hx (by omega : k + (n - k) = n) hm1 (hmem p (n - k)), map_mul, ih (n - k) _ _ rfl, mul_zero]`.

Rewrite `h` using `[DirectSum.coe_decompose_mul_of_left_mem_of_not_le _ m.2 hk]`. Substitute `h` using the available equality. Rewrite using `[away_mk_zero, map_zero]`. Consider the case `add a b iha ihb`. Rewrite using `[add_smul]`.

Conclude with `hadd _ _ iha ihb`.
-/
theorem chart_zero {R : Type} [CommRing R] {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1)
    (φ : Away (grK K N) x →+* R) (S : Set (MvPolynomial (Fin (N + 1)) K))
    (hS : ∀ f ∈ S, ∃ (d : ℕ) (hf : f ∈ grK K N (d • 1)), φ (Away.mk (grK K N) hx d f hf) = 0)
    {p : MvPolynomial (Fin (N + 1)) K} (hp : p ∈ Ideal.span S) :
    ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
      f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) →
        φ (Away.mk (grK K N) hx n f hf) = 0 := by
  have hmem : ∀ (q : MvPolynomial (Fin (N + 1)) K) (n : ℕ),
      (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (n • 1) := by
    intro q n
    simpa using (DirectSum.decompose (grK K N) q n).2
  have hzero : ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
      f = (DirectSum.decompose (grK K N) (0 : MvPolynomial (Fin (N + 1)) K) n : MvPolynomial (Fin (N + 1)) K) →
        φ (Away.mk (grK K N) hx n f hf) = 0 := by
    intro n f hf h
    have h0 : f = 0 := by simpa using h
    subst h0
    rw [away_mk_zero, map_zero]
  have hadd : ∀ (p q : MvPolynomial (Fin (N + 1)) K),
      (∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0) →
      (∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0) →
      ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) (p + q) n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0 := by
    intro p q ihp ihq n f hf h
    have h' : f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) +
        (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) := by
      rw [h, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
    subst h'
    rw [away_mk_add hx n (hmem p n) (hmem q n), map_add, ihp n _ _ rfl, ihq n _ _ rfl, add_zero]
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨d, hd, h0⟩ := hS p hp
    intro n f hf h
    have hd' : p ∈ grK K N d := by simpa using hd
    by_cases hnd : n = d
    · subst hnd
      have : f = p := h.trans (DirectSum.decompose_of_mem_same _ hd')
      subst this
      exact h0
    · have h1 : f = 0 := h.trans (DirectSum.decompose_of_mem_ne _ hd' (Ne.symm hnd))
      subst h1
      rw [away_mk_zero, map_zero]
  | zero => exact hzero
  | add p q _ _ ihp ihq => exact hadd p q ihp ihq
  | smul a p _ ih =>
    induction a using DirectSum.Decomposition.inductionOn (grK K N) with
    | zero => simpa using hzero
    | @homogeneous k m =>
      intro n f hf h
      rw [smul_eq_mul] at h
      by_cases hk : k ≤ n
      · rw [DirectSum.coe_decompose_mul_of_left_mem_of_le _ m.2 hk] at h
        subst h
        have hm1 : (m : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (k • 1) := by simpa using m.2
        rw [away_mk_mul hx (by omega : k + (n - k) = n) hm1 (hmem p (n - k)), map_mul,
          ih (n - k) _ _ rfl, mul_zero]
      · rw [DirectSum.coe_decompose_mul_of_left_mem_of_not_le _ m.2 hk] at h
        subst h
        rw [away_mk_zero, map_zero]
    | add a b iha ihb =>
      rw [add_smul]
      exact hadd _ _ iha ihb

/- English proof (translation)
Use `Scheme.Hom.appLE_map i hV (homOfLE h).op` as an intermediate fact. Simplify using `only [evV]`. Conclude with `congr($(this).hom ((Proj.awayToSection (grK K N) g).hom y))`.
-/
theorem evV_res {X : Scheme.{0}} (i : X ⟶ PSpace K N) (g : MvPolynomial (Fin (N + 1)) K) {V W : X.Opens}
    (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (h : W ≤ V) (y : Away (grK K N) g) :
    resO h (evV i g V hV y) = evV i g W (h.trans hV) y := by
  have := Scheme.Hom.appLE_map i hV (homOfLE h).op
  simp only [evV]
  exact congr($(this).hom ((Proj.awayToSection (grK K N) g).hom y))

/- English proof (translation)
Establish `h1` using `Proj.awayMap_awayToSection (grK K N) hb hc`. Establish `h2` using `Scheme.Hom.map_appLE i hW (homOfLE (Proj.basicOpen_mono (grK K N) a c ⟨_, hc⟩)).op`. Establish `h3 : (Proj.awayToSection (grK K N) c).hom (awayMap (grK K N) hb hc y) = ((PSpace K N).presheaf.map (homOfLE (Proj.basicOpen_mono (grK K N) a c ⟨_, hc⟩)).op).hom ((Proj.awayToSection (grK K N) a).hom y)` using `congr($(h1).hom y)`. Simplify using `only [evV, RingHom.comp_apply]`. Rewrite using `[h3]`.

Conclude with `congr($(h2).hom ((Proj.awayToSection (grK K N) a).hom y))`.
-/
theorem evV_awayMap {X : Scheme.{0}} (i : X ⟶ PSpace K N) {a b c : MvPolynomial (Fin (N + 1)) K} {m : ℕ}
    (hb : b ∈ grK K N m) (hc : c = a * b) {W : X.Opens} (hW : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) c)
    (hW' : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) a) (y : Away (grK K N) a) :
    evV i c W hW (awayMap (grK K N) hb hc y) = evV i a W hW' y := by
  have h1 := Proj.awayMap_awayToSection (grK K N) hb hc
  have h2 := Scheme.Hom.map_appLE i hW (homOfLE (Proj.basicOpen_mono (grK K N) a c ⟨_, hc⟩)).op
  have h3 : (Proj.awayToSection (grK K N) c).hom (awayMap (grK K N) hb hc y) =
      ((PSpace K N).presheaf.map (homOfLE (Proj.basicOpen_mono (grK K N) a c ⟨_, hc⟩)).op).hom
        ((Proj.awayToSection (grK K N) a).hom y) := congr($(h1).hom y)
  simp only [evV, RingHom.comp_apply]
  rw [h3]
  exact congr($(h2).hom ((Proj.awayToSection (grK K N) a).hom y))

/- English proof (translation)
Establish `h : ⨆ j, Proj.basicOpen (grK K N) (X j : MvPolynomial (Fin (N + 1)) K) = ⊤`. Use `Proj.iSup_basicOpen_eq_top _ _ ((HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun n hn f hf => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f ∈ Ideal.span _`. Rewrite using `[← Set.image_univ, mem_ideal_span_X_image]`. Introduce `m hm`.

Use `by_contra! H`. Take `rfl : m = 0` from `Finsupp.ext fun i => H i (Set.mem_univ i)`. Establish `hf' : f ∈ grK K N n` using `hf`. Use `((mem_homogeneousSubmodule _ _).1 hf') (mem_support_iff.1 hm)` as an intermediate fact. Simplify using `only [map_zero] at this`.

Use linear arithmetic over natural numbers and integers. Conclude with `TopologicalSpace.Opens.mem_iSup.1 (h.ge (Set.mem_univ p))`.
-/
theorem exists_chart (p : PSpace K N) : ∃ j, p ∈ Proj.basicOpen (grK K N) (X j : MvPolynomial (Fin (N + 1)) K) := by
  have h : ⨆ j, Proj.basicOpen (grK K N) (X j : MvPolynomial (Fin (N + 1)) K) = ⊤ := by
    refine Proj.iSup_basicOpen_eq_top _ _ ((HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun n hn f hf => ?_)
    change f ∈ Ideal.span _
    rw [← Set.image_univ, mem_ideal_span_X_image]
    intro m hm
    by_contra! H
    obtain rfl : m = 0 := Finsupp.ext fun i => H i (Set.mem_univ i)
    have hf' : f ∈ grK K N n := hf
    have := ((mem_homogeneousSubmodule _ _).1 hf') (mem_support_iff.1 hm)
    simp only [map_zero] at this
    omega
  exact TopologicalSpace.Opens.mem_iSup.1 (h.ge (Set.mem_univ p))

/- English proof (translation)
Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Simplify using `only [awayMap_mk, Away.val_mk, HomogeneousLocalization.val_mul, Localization.mk_mul]`. Rewrite using `[Localization.mk_eq_mk_iff, Localization.r_iff_exists]`. Use `⟨1, ?_⟩` and prove the remaining obligations. Simplify using `only [Submonoid.coe_mul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ratio_eq {g x f : MvPolynomial (Fin (N + 1)) K} {e s : ℕ} (hg : g ∈ grK K N e) (hx : x ∈ grK K N 1)
    (hf : f ∈ grK K N (s • e)) (hf1 : f ∈ grK K N ((s • e) • 1)) (hxs : x ^ (s • e) ∈ grK K N (s • e)) :
    awayMap (grK K N) hx (rfl : g * x = g * x) (Away.mk (grK K N) hg s f hf) =
      awayMap (grK K N) hx (rfl : g * x = g * x) (Away.mk (grK K N) hg s (x ^ (s • e)) hxs) *
        awayMap (grK K N) hg (mul_comm g x) (Away.mk (grK K N) hx (s • e) f hf1) := by
  apply HomogeneousLocalization.val_injective
  simp only [awayMap_mk, Away.val_mk, HomogeneousLocalization.val_mul, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, smul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.GeoVanish

open GlobalTheory.CompanionTheory.GeoVanish in

/- English proof (translation)
Introduce `K _ X N i g e he hg s f hf hfI V hV`. Establish `hf1 : f ∈ grK K N ((s • e) • 1)` using `by simpa using hf`. Establish `key : ∀ j : Fin (N + 1), evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) (s • e) f hf1) = 0`. Introduce `j`. Use `chart_zero (xv_mem K N j) (evV i (MvPolynomial.X j) _ le_rfl) _ ?_ hfI (s • e) f hf1 (DirectSum.decompose_of_mem_same _ hf).symm` and prove the remaining obligations.

Introduce and unpack `p ⟨d, hp, h⟩`. Conclude with `⟨d, hp, h j⟩`. Use `TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun j : Fin (N + 1) => V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) V (fun j => homOfLE inf_le_left) ?_ _ _ ?_` and prove the remaining obligations. Introduce `p hp`. Take `⟨j, hj⟩` from `exists_chart (i p)`.

Use `TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩` and prove the remaining obligations. Conclude with `And.intro hp hj`. Introduce `j set x : MvPolynomial (Fin (N + 1)) K := MvPolynomial.X j with hxdef`. Establish `hx : x ∈ grK K N 1` using `xv_mem K N j`. Use `set W := V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) x with hWdef`.

Establish `hWg : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g` using `inf_le_left.trans hV`. Establish `hWx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x` using `inf_le_right`. Establish `hWgx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (g * x)`. Rewrite using `[Proj.basicOpen_mul]`. Conclude with `fun p hp => And.intro (hWg hp) (hWx hp)`.

Establish `hxs : x ^ (s • e) ∈ grK K N (s • e)`. Simplify using `using SetLike.pow_mem_graded (s • e) hx`. Establish `h0 : evV i x W hWx (HomogeneousLocalization.Away.mk (grK K N) hx (s • e) f hf1) = 0`. Rewrite using `[← evV_res i x le_rfl hWx, key j, map_zero]`. Establish `h1 : evV i g W hWg (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0`.

Rewrite using `[← evV_awayMap i hx rfl hWgx hWg, ratio_eq hg hx hf hf1 hxs, map_mul, evV_awayMap i hg (mul_comm g x) hWgx hWx, h0, mul_zero]`. Express the relevant statement in the definitionally equal form `resO (inf_le_left : W ≤ V) (evV i g V hV _) = resO (inf_le_left : W ≤ V) 0`. Rewrite using `[map_zero, evV_res i g hV inf_le_left]`. Conclude with `h1`.
-/
theorem GlobalTheory.CompanionTheory.GeoVanish.homIdeal_vanish : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e) (hg : g ∈ grK K N e) {s : ℕ} {f : MvPolynomial (Fin (N + 1)) K} (hf : f ∈ grK K N (s • e)), f ∈ homIdeal i → ∀ (V : X.Opens) (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g), evV i g V hV (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0 := by
  intro K _ X N i g e he hg s f hf hfI V hV
  have hf1 : f ∈ grK K N ((s • e) • 1) := by simpa using hf
  have key : ∀ j : Fin (N + 1), evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) (s • e) f hf1) = 0 := by
    intro j
    refine chart_zero (xv_mem K N j) (evV i (MvPolynomial.X j) _ le_rfl) _ ?_ hfI (s • e) f hf1
      (DirectSum.decompose_of_mem_same _ hf).symm
    rintro p ⟨d, hp, h⟩
    exact ⟨d, hp, h j⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun j : Fin (N + 1) => V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) V
    (fun j => homOfLE inf_le_left) ?_ _ _ ?_
  · intro p hp
    obtain ⟨j, hj⟩ := exists_chart (i p)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩
    exact And.intro hp hj
  · intro j
    set x : MvPolynomial (Fin (N + 1)) K := MvPolynomial.X j with hxdef
    have hx : x ∈ grK K N 1 := xv_mem K N j
    set W := V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) x with hWdef
    have hWg : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g := inf_le_left.trans hV
    have hWx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x := inf_le_right
    have hWgx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (g * x) := by
      rw [Proj.basicOpen_mul]
      exact fun p hp => And.intro (hWg hp) (hWx hp)
    have hxs : x ^ (s • e) ∈ grK K N (s • e) := by
      simpa using SetLike.pow_mem_graded (s • e) hx
    have h0 : evV i x W hWx (HomogeneousLocalization.Away.mk (grK K N) hx (s • e) f hf1) = 0 := by
      rw [← evV_res i x le_rfl hWx, key j, map_zero]
    have h1 : evV i g W hWg (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0 := by
      rw [← evV_awayMap i hx rfl hWgx hWg, ratio_eq hg hx hf hf1 hxs, map_mul,
        evV_awayMap i hg (mul_comm g x) hWgx hWx, h0, mul_zero]
    change resO (inf_le_left : W ≤ V) (evV i g V hV _) = resO (inf_le_left : W ≤ V) 0
    rw [map_zero, evV_res i g hV inf_le_left]
    exact h1
