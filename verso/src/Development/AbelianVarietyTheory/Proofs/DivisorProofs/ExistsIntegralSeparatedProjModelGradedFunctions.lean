import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAlgebraMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.GrSpec

open Polynomial HomogeneousLocalization

variable {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F} (hN : GradedFam c₀ N)

/- English proof (translation)
Rewrite using `[SubmonoidClass.coe_pow, coe_hel, monomial_pow]`.
-/
theorem coe_hel_pow {k : ℕ} {b : F} (hb : b ∈ N k) (n : ℕ) :
    ((hel hN k b hb ^ n : ring hN) : F[X]) = monomial (k * n) (b ^ n) := by
  rw [SubmonoidClass.coe_pow, coe_hel, monomial_pow]

/- English proof (translation)
Use `SetLike.pow_mem_graded n (hel_mem hN k b hb)` as an intermediate fact. Rewrite `this` using `[smul_eq_mul, mul_comm]`. Then use the resulting hypothesis.
-/
theorem hel_pow_mem {k : ℕ} {b : F} (hb : b ∈ N k) (n : ℕ) : hel hN k b hb ^ n ∈ piece hN (k * n) := by
  have := SetLike.pow_mem_graded n (hel_mem hN k b hb)
  rwa [smul_eq_mul, mul_comm] at this

/- English proof (translation)
Rewrite using `[← isUnit_iff_isUnit_val, val_mk, Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]`. Both sides reduce to the same expression.
-/
theorem isUnit_mk_iff (P : Ideal (ring hN)) [P.IsPrime] (g : NumDenSameDeg (piece hN) P.primeCompl) :
    IsUnit (mk g : AtPrime (piece hN) P) ↔ (g.num : ring hN) ∉ P := by
  rw [← isUnit_iff_isUnit_val, val_mk, Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

/- English proof (translation)
Rewrite using `[Dp_of_mem hN hb]`. Conclude with `Proj.isAffineOpen_basicOpen _ _ (hel_mem hN k b hb) (by omega)`.
-/
theorem affine {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) : IsAffineOpen (Dp hN k b) := by
  rw [Dp_of_mem hN hb]
  exact Proj.isAffineOpen_basicOpen _ _ (hel_mem hN k b hb) (by omega)

/- English proof (translation)
Take `⟨y, hy, hyz⟩` from `Set.not_subset.1 z.not_irrelevant_le`. Establish `: ∃ j, (DirectSum.decompose (piece hN) y j : ring hN) ∉ z.asHomogeneousIdeal`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `hyz` to reduce the goal to its premises.

Rewrite using `[← DirectSum.sum_support_decompose (piece hN) y]`. Conclude with `Ideal.sum_mem _ fun j _ => hc j`. Take `⟨j, hj⟩` from `this`. Establish `hj0 : j ≠ 0`. Introduce and unpack `rfl`.

Apply `hj` to reduce the goal to its premises. Establish `: (DirectSum.decompose (piece hN) y 0 : ring hN) = 0`. Rewrite using `[← GradedRing.proj_apply]`. Conclude with `(HomogeneousIdeal.mem_irrelevant_iff _ _).1 hy`. Rewrite using `[this]`.

Conclude with `zero_mem _`. Use `set c := DirectSum.decompose (piece hN) y j`. Establish `hb : ((c : ring hN) : F[X]).coeff j ∈ N j` using `(c : ring hN).2 j`. Use `⟨j, by omega, _, hb, ?_⟩` and prove the remaining obligations. Rewrite using `[Dp_of_mem hN hb, Proj.mem_basicOpen]`.

Establish `: hel hN j _ hb = (c : ring hN)` using `Subtype.ext ((mem_piece_iff hN).1 c.2).symm`. Rewrite using `[this]`. Conclude with `hj`.
-/
theorem cover (z : Proj (piece hN)) : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, z ∈ Dp hN k b := by
  classical
  obtain ⟨y, hy, hyz⟩ := Set.not_subset.1 z.not_irrelevant_le
  have : ∃ j, (DirectSum.decompose (piece hN) y j : ring hN) ∉ z.asHomogeneousIdeal := by
    by_contra hc
    push_neg at hc
    apply hyz
    rw [← DirectSum.sum_support_decompose (piece hN) y]
    exact Ideal.sum_mem _ fun j _ => hc j
  obtain ⟨j, hj⟩ := this
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hj
    have : (DirectSum.decompose (piece hN) y 0 : ring hN) = 0 := by
      rw [← GradedRing.proj_apply]; exact (HomogeneousIdeal.mem_irrelevant_iff _ _).1 hy
    rw [this]; exact zero_mem _
  set c := DirectSum.decompose (piece hN) y j
  have hb : ((c : ring hN) : F[X]).coeff j ∈ N j := (c : ring hN).2 j
  refine ⟨j, by omega, _, hb, ?_⟩
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen]
  have : hel hN j _ hb = (c : ring hN) := Subtype.ext ((mem_piece_iff hN).1 c.2).symm
  rw [this]; exact hj

/- English proof (translation)
The claim follows from `le_bot_iff.1 ((ProjectiveSpectrum.le_iff_mem_closure (piece hN) _ (gen hN hk hb h0)).2 (specializes_iff_mem_closure.1 (genericPoint_specializes (show Proj (piece hN) from gen hN hk hb h0))))`.
-/
theorem ideal_gen [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (h0 : b ≠ 0) :
    (genericPoint (Proj (piece hN))).asHomogeneousIdeal = ⊥ :=
  le_bot_iff.1 ((ProjectiveSpectrum.le_iff_mem_closure (piece hN) _ (gen hN hk hb h0)).2
    (specializes_iff_mem_closure.1 (genericPoint_specializes (show Proj (piece hN) from gen hN hk hb h0))))

/- English proof (translation)
Take `⟨k', hk', b', hb', h0'⟩` from `h`. Rewrite using `[Dp_of_mem hN hb, Proj.mem_basicOpen, ideal_gen hN hk' hb' h0']`. Express the relevant statement in the definitionally equal form `¬ (hel hN k b hb = 0) ↔ _`. Rewrite using `[not_iff_not, Subtype.ext_iff]`. Simplify using the standard rewrite rules.
-/
theorem genMem [IsIntegral (Proj (piece hN))] (h : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0) {k : ℕ} {b : F} (hb : b ∈ N k) :
    genericPoint (Proj (piece hN)) ∈ Dp hN k b ↔ b ≠ 0 := by
  obtain ⟨k', hk', b', hb', h0'⟩ := h
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen, ideal_gen hN hk' hb' h0']
  change ¬ (hel hN k b hb = 0) ↔ _
  rw [not_iff_not, Subtype.ext_iff]
  simp

/- English proof (translation)
Introduce `h` and use `hz (Ideal.IsPrime.mem_of_pow_mem inferInstance n h)`.
-/
theorem hel_notMem {z : Proj (piece hN)} {k : ℕ} {b : F} {hb : b ∈ N k} (n : ℕ)
    (hz : hel hN k b hb ∉ z.asHomogeneousIdeal) : hel hN k b hb ^ n ∉ z.asHomogeneousIdeal.toIdeal :=
  fun h => hz (Ideal.IsPrime.mem_of_pow_mem inferInstance n h)

/- English proof (translation)
Introduce and unpack `rfl`. Apply `hz` to reduce the goal to its premises. Establish `: hel hN k 0 hb = 0` using `Subtype.ext (by simp)`. Rewrite using `[this]`. Conclude with `zero_mem _`.
-/
theorem ne_zero_of_notMem {z : Proj (piece hN)} {k : ℕ} {b : F} {hb : b ∈ N k}
    (hz : hel hN k b hb ∉ z.asHomogeneousIdeal) : b ≠ 0 := by
  rintro rfl
  apply hz
  have : hel hN k 0 hb = 0 := Subtype.ext (by simp)
  rw [this]; exact zero_mem _

/- English proof (translation)
Rewrite `hz` using `[Dp_of_mem hN hb, Proj.mem_basicOpen]`. Rewrite using `[Dp_of_mem hN ha, Proj.mem_basicOpen]`. Establish `hfz` using `hel_notMem hN l hz`. Establish `hb0` using `ne_zero_of_notMem hN hz`. Prove the components needed by the constructor for the conclusion.

Introduce `hg`. Set `nd : NumDenSameDeg (piece hN) z.asHomogeneousIdeal.toIdeal.primeCompl` to `⟨l * k, ⟨_, hel_pow_mem hN ha k⟩, ⟨_, by rw [mul_comm]; exact hel_pow_mem hN hb l⟩, hfz⟩`. Use `⟨algebraMap ((Proj (piece hN)).presheaf.stalk z) _ ((Proj.stalkIso' (piece hN) z).symm (mk nd)), ⟨_, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Conclude with `((isUnit_mk_iff hN _ nd).2 (hel_notMem hN k hg)).map (Proj.stalkIso' (piece hN) z).symm`. Use `(psi_algebraMap hN z _).trans ?_ erw [RingEquiv.apply_symm_apply]` and prove the remaining obligations.

Rewrite using `[psiAt_mk]`. Simplify using `only [nd, coe_hel_pow, coeff_monomial, if_pos (mul_comm k l), if_pos rfl, ↓reduceIte]`. Introduce and unpack `⟨v, ⟨w, hwu, rfl⟩, hv⟩ hg`. Rewrite `hv` using `[psi_algebraMap]`. Take `⟨g, hg'⟩` from `mk_surjective (Proj.stalkIso' (piece hN) z w)`.

Rewrite `hv` using `[← hg', psiAt_mk]`. Establish `hu : IsUnit (mk g : AtPrime (piece hN) z.asHomogeneousIdeal.toIdeal)`. Rewrite using `[hg']`. Conclude with `hwu.map (Proj.stalkIso' (piece hN) z)`. Rewrite `hu` using `[isUnit_mk_iff]`.

Establish `hnum` using `(mem_piece_iff hN).1 g.num.2`. Establish `hden` using `(mem_piece_iff hN).1 g.den.2`. Establish `hs : ((g.den : ring hN) : F[X]).coeff g.deg ≠ 0`. Introduce `h0`. Apply `g.den_mem` to reduce the goal to its premises.

Establish `: (g.den : ring hN) = 0` using `Subtype.ext (by rw [hden, h0, map_zero]; rfl)`. Rewrite using `[this]`. Conclude with `zero_mem _`. Establish `key : (g.num : ring hN) * hel hN k b hb ^ l = hel hN l a ha ^ k * (g.den : ring hN)`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[Subring.coe_mul, Subring.coe_mul, coe_hel_pow, coe_hel_pow, hnum, hden, monomial_mul_monomial, monomial_mul_monomial, show l * k + g.deg = g.deg + k * l by ring]`. Use `congr 1`. Rewrite `hv` using `[div_eq_div_iff hs (pow_ne_zero _ hb0)]`. Conclude with `hv`. Establish `: (g.num : ring hN) * hel hN k b hb ^ l ∈ z.asHomogeneousIdeal.toIdeal`.

Rewrite using `[key]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hg _ (by omega))`. Break down `Ideal.IsPrime.mem_or_mem inferInstance this with h | h` into its components or cases. Conclude with `hu h`. Conclude with `hfz h`.
-/
theorem mem [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (z : Proj (piece hN))
    (hz : z ∈ Dp hN k b) {l : ℕ} {a : F} (ha : a ∈ N l) :
    z ∈ Dp hN l a ↔ ∃ v, UnitAt z v ∧ psi hN v = a ^ k / b ^ l := by
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen] at hz
  rw [Dp_of_mem hN ha, Proj.mem_basicOpen]
  have hfz := hel_notMem hN l hz
  have hb0 := ne_zero_of_notMem hN hz
  constructor
  · intro hg
    let nd : NumDenSameDeg (piece hN) z.asHomogeneousIdeal.toIdeal.primeCompl :=
      ⟨l * k, ⟨_, hel_pow_mem hN ha k⟩, ⟨_, by rw [mul_comm]; exact hel_pow_mem hN hb l⟩, hfz⟩
    refine ⟨algebraMap ((Proj (piece hN)).presheaf.stalk z) _ ((Proj.stalkIso' (piece hN) z).symm (mk nd)), ⟨_, ?_, rfl⟩, ?_⟩
    · exact ((isUnit_mk_iff hN _ nd).2 (hel_notMem hN k hg)).map (Proj.stalkIso' (piece hN) z).symm
    · refine (psi_algebraMap hN z _).trans ?_
      erw [RingEquiv.apply_symm_apply]
      rw [psiAt_mk]
      simp only [nd, coe_hel_pow, coeff_monomial, if_pos (mul_comm k l), if_pos rfl, ↓reduceIte]
  · rintro ⟨v, ⟨w, hwu, rfl⟩, hv⟩ hg
    rw [psi_algebraMap] at hv
    obtain ⟨g, hg'⟩ := mk_surjective (Proj.stalkIso' (piece hN) z w)
    rw [← hg', psiAt_mk] at hv
    have hu : IsUnit (mk g : AtPrime (piece hN) z.asHomogeneousIdeal.toIdeal) := by
      rw [hg']; exact hwu.map (Proj.stalkIso' (piece hN) z)
    rw [isUnit_mk_iff] at hu
    have hnum := (mem_piece_iff hN).1 g.num.2
    have hden := (mem_piece_iff hN).1 g.den.2
    have hs : ((g.den : ring hN) : F[X]).coeff g.deg ≠ 0 := by
      intro h0
      apply g.den_mem
      have : (g.den : ring hN) = 0 := Subtype.ext (by rw [hden, h0, map_zero]; rfl)
      rw [this]; exact zero_mem _
    have key : (g.num : ring hN) * hel hN k b hb ^ l = hel hN l a ha ^ k * (g.den : ring hN) := by
      apply Subtype.ext
      rw [Subring.coe_mul, Subring.coe_mul, coe_hel_pow, coe_hel_pow, hnum, hden, monomial_mul_monomial,
        monomial_mul_monomial, show l * k + g.deg = g.deg + k * l by ring]
      congr 1
      rw [div_eq_div_iff hs (pow_ne_zero _ hb0)] at hv
      exact hv
    have : (g.num : ring hN) * hel hN k b hb ^ l ∈ z.asHomogeneousIdeal.toIdeal := by
      rw [key]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hg _ (by omega))
    rcases Ideal.IsPrime.mem_or_mem inferInstance this with h | h
    · exact hu h
    · exact hfz h

def fracAt {k : ℕ} {b : F} (hb : b ∈ N k) (m : ℕ) {a : F} (ha : a ∈ N (k * m)) (x : Proj (piece hN))
    (hx : hel hN k b hb ∉ x.asHomogeneousIdeal) : NumDenSameDeg (piece hN) x.asHomogeneousIdeal.toIdeal.primeCompl :=
  ⟨k * m, ⟨hel hN (k * m) a ha, hel_mem hN _ _ ha⟩, ⟨_, hel_pow_mem hN hb m⟩, hel_notMem hN m hx⟩

/- English proof (translation)
Use `(psi_algebraMap hN x _).trans ?_` and prove the remaining obligations. Use `erw [RingEquiv.apply_symm_apply]`. Rewrite using `[psiAt_mk]`. Simplify using `only [fracAt, coe_hel, coe_hel_pow, coeff_monomial, ↓reduceIte]`.
-/
theorem psi_fracAt [IsIntegral (Proj (piece hN))] {k : ℕ} {b : F} (hb : b ∈ N k) (m : ℕ) {a : F}
    (ha : a ∈ N (k * m)) (x : Proj (piece hN)) (hx : hel hN k b hb ∉ x.asHomogeneousIdeal) :
    psi hN (algebraMap ((Proj (piece hN)).presheaf.stalk x) _
      ((Proj.stalkIso' (piece hN) x).symm (mk (fracAt hN hb m ha x hx)))) = a / b ^ m := by
  refine (psi_algebraMap hN x _).trans ?_
  erw [RingEquiv.apply_symm_apply]
  rw [psiAt_mk]
  simp only [fracAt, coe_hel, coe_hel_pow, coeff_monomial, ↓reduceIte]

/- English proof (translation)
Establish `h1 : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0` using `⟨k, hk, b, hb, hb0⟩`. Establish `hgen : genericPoint (Proj (piece hN)) ∈ Dp hN k b` using `(genMem hN h1 hb).2 hb0`. Rewrite `hgen`, the goal using `[Dp_of_mem hN hb]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`.

Take `⟨s, rfl⟩` from `exists_fnOf_eq hgen hv`. Choose the witnesses or unpack the hypotheses as in `⟨y, rfl⟩ : ∃ y, Proj.awayToSection (piece hN) (hel hN k b hb) y = s := by`. Use `⟨(Proj.basicOpenIsoAway (piece hN) _ (hel_mem hN k b hb) (by omega)).inv s, ?_⟩` and prove the remaining obligations. Rewrite using `[← Proj.basicOpenIsoAway_hom (piece hN) _ (hel_mem hN k b hb) (by omega)]`. Conclude with `(Proj.basicOpenIsoAway (piece hN) _ (hel_mem hN k b hb) (by omega)).inv_hom_id_apply s`.

Take `⟨nd, rfl⟩` from `mk_surjective y`. Take `⟨m, hm⟩` from `nd.den_mem`. Establish `hdeg : nd.deg = k * m`. Establish `hne : (nd.den : ring hN) ≠ 0`. Rewrite using `[← hm]`.

Conclude with `pow_ne_zero _ (hel_ne_zero hN hb hb0)`. Conclude with `DirectSum.degree_eq_of_mem_mem (piece hN) nd.den.2 (hm ▸ hel_pow_mem hN hb m) hne`. Use `⟨m, ((nd.num : ring hN) : F[X]).coeff nd.deg, hdeg ▸ (nd.num : ring hN).2 nd.deg, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.germ _ _ hgen (Proj.awayToSection (piece hN) (hel hN k b hb) (mk nd)))) = _`. Use `erw [Proj.stalkIso'_germ]`.

Establish `key : ∀ (h : Submonoid.powers (hel hN k b hb) ≤ (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal.primeCompl), psiAt hN _ (HomogeneousLocalization.mapId (piece hN) h (mk nd)) = ((nd.num : ring hN) : F[X]).coeff nd.deg / ((nd.den : ring hN) : F[X]).coeff nd.deg`. Introduce `h`. Conclude with `psiAt_mk hN _ ⟨nd.deg, nd.num, nd.den, h nd.den_mem⟩`. Use `(key _).trans ?_` and prove the remaining obligations. Rewrite using `[← hm, coe_hel_pow, coeff_monomial, if_pos hdeg.symm]`.

Introduce and unpack `⟨m, a, ha, rfl⟩`. Use `⟨_, fun z hz => ⟨_, (psi hN).injective ((psi_fracAt hN hb m ha z hz).trans (psi_fracAt hN hb m ha _ hgen).symm)⟩, psi_fracAt hN hb m ha _ hgen⟩` and prove the remaining obligations.
-/
theorem ringChar [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (hb0 : b ≠ 0) (u : F) :
    (∃ v, (∀ z ∈ Dp hN k b, RegAt z v) ∧ psi hN v = u) ↔ ∃ m, ∃ a ∈ N (k * m), u = a / b ^ m := by
  have h1 : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0 := ⟨k, hk, b, hb, hb0⟩
  have hgen : genericPoint (Proj (piece hN)) ∈ Dp hN k b := (genMem hN h1 hb).2 hb0
  rw [Dp_of_mem hN hb] at hgen ⊢
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨s, rfl⟩ := exists_fnOf_eq hgen hv
    obtain ⟨y, rfl⟩ : ∃ y, Proj.awayToSection (piece hN) (hel hN k b hb) y = s := by
      refine ⟨(Proj.basicOpenIsoAway (piece hN) _ (hel_mem hN k b hb) (by omega)).inv s, ?_⟩
      rw [← Proj.basicOpenIsoAway_hom (piece hN) _ (hel_mem hN k b hb) (by omega)]
      exact (Proj.basicOpenIsoAway (piece hN) _ (hel_mem hN k b hb) (by omega)).inv_hom_id_apply s
    obtain ⟨nd, rfl⟩ := mk_surjective y
    obtain ⟨m, hm⟩ := nd.den_mem
    have hdeg : nd.deg = k * m := by
      have hne : (nd.den : ring hN) ≠ 0 := by
        rw [← hm]; exact pow_ne_zero _ (hel_ne_zero hN hb hb0)
      exact DirectSum.degree_eq_of_mem_mem (piece hN) nd.den.2 (hm ▸ hel_pow_mem hN hb m) hne
    refine ⟨m, ((nd.num : ring hN) : F[X]).coeff nd.deg, hdeg ▸ (nd.num : ring hN).2 nd.deg, ?_⟩
    change psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.germ _ _ hgen
      (Proj.awayToSection (piece hN) (hel hN k b hb) (mk nd)))) = _
    erw [Proj.stalkIso'_germ]
    have key : ∀ (h : Submonoid.powers (hel hN k b hb) ≤
        (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal.primeCompl),
        psiAt hN _ (HomogeneousLocalization.mapId (piece hN) h (mk nd)) =
          ((nd.num : ring hN) : F[X]).coeff nd.deg / ((nd.den : ring hN) : F[X]).coeff nd.deg := by
      intro h
      exact psiAt_mk hN _ ⟨nd.deg, nd.num, nd.den, h nd.den_mem⟩
    refine (key _).trans ?_
    rw [← hm, coe_hel_pow, coeff_monomial, if_pos hdeg.symm]
  · rintro ⟨m, a, ha, rfl⟩
    refine ⟨_, fun z hz => ⟨_, (psi hN).injective ((psi_fracAt hN hb m ha z hz).trans
      (psi_fracAt hN hb m ha _ hgen).symm)⟩, psi_fracAt hN hb m ha _ hgen⟩

def gR : CommRingCat.of R ⟶ Γ(Proj (piece hN), ⊤) :=
  CommRingCat.ofHom ((fromZeroRingHom (piece hN) _).comp (toZero hN)) ≫ Proj.awayToSection (piece hN) 1 ≫
    (Proj (piece hN)).presheaf.map (homOfLE (Proj.basicOpen_one (piece hN)).ge).op

def pstr : Proj (piece hN) ⟶ Sp R := (Proj (piece hN)).toSpecΓ ≫ Spec.map (gR hN)

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem sep : IsSeparated (pstr hN) := inferInstance

/- English proof (translation)
Use extensionality with `r`. Establish `hg : genericPoint (Proj (piece hN)) ∈ Proj.basicOpen (piece hN) 1`. Rewrite using `[Proj.basicOpen_one]`. Discharge the goal by the elementary cases of `trivial`. Establish `e0 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pstr hN).appTop = gR hN`.

Rewrite using `[pstr, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]`. Express the relevant statement in the definitionally equal form `psi hN (fnOf ⊤ trivial (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pstr hN).appTop) r)) = c₀ r`. Rewrite using `[e0]`. Express the relevant statement in the definitionally equal form `psi hN (fnOf ⊤ trivial (resG (Proj (piece hN)) (Proj.basicOpen_one (piece hN)).ge (Proj.awayToSection (piece hN) 1 (fromZeroRingHom (piece hN) _ (toZero hN r))))) = c₀ r`. Rewrite using `[fnOf_resG (Proj.basicOpen_one (piece hN)).ge trivial]`.

Express the relevant statement in the definitionally equal form `psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.germ _ _ hg (Proj.awayToSection (piece hN) 1 (fromZeroRingHom (piece hN) _ (toZero hN r))))) = _`. Use `erw [Proj.stalkIso'_germ]`. Use `(psiAt_mk hN _ ⟨0, toZero hN r, 1, fun h => ?_⟩).trans ?_` and prove the remaining obligations. Conclude with `(Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h)`. Simplify using `[toZero]`.
-/
theorem const [IsIntegral (Proj (piece hN))] : (psi hN).comp (cst (pstr hN)) = c₀ := by
  ext r
  have hg : genericPoint (Proj (piece hN)) ∈ Proj.basicOpen (piece hN) 1 := by
    rw [Proj.basicOpen_one]; trivial
  have e0 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pstr hN).appTop = gR hN := by
    rw [pstr, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  change psi hN (fnOf ⊤ trivial (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pstr hN).appTop) r)) = c₀ r
  rw [e0]
  change psi hN (fnOf ⊤ trivial (resG (Proj (piece hN)) (Proj.basicOpen_one (piece hN)).ge
    (Proj.awayToSection (piece hN) 1 (fromZeroRingHom (piece hN) _ (toZero hN r))))) = c₀ r
  rw [fnOf_resG (Proj.basicOpen_one (piece hN)).ge trivial]
  change psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.germ _ _ hg
      (Proj.awayToSection (piece hN) 1 (fromZeroRingHom (piece hN) _ (toZero hN r))))) = _
  erw [Proj.stalkIso'_germ]
  refine (psiAt_mk hN _ ⟨0, toZero hN r, 1, fun h => ?_⟩).trans ?_
  · exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h)
  · simp [toZero]

end GlobalTheory.Desc.GrSpec

namespace GlobalTheory.Desc

/- English proof (translation)
Introduce `R F _ _ _ c₀ N hN h`. Take `⟨k₀, hk₀, b₀, hb₀, h₀⟩` from `h`. Use `haveI := GrSpec.isIntegral hN hk₀ hb₀ h₀`. Use `⟨Proj (GrSpec.piece hN), inferInstance, GrSpec.pstr hN, GrSpec.psi hN, GrSpec.Dp hN, ?_⟩` and prove the remaining obligations. Conclude with `{ sep := GrSpec.sep hN const := GrSpec.const hN affine := fun k hk b hb => GrSpec.affine hN hk hb cover := GrSpec.cover hN gen := fun k _ b hb => GrSpec.genMem hN ⟨k₀, hk₀, b₀, hb₀, h₀⟩ hb`.

Use `ring := fun k hk b hb hb0 u => GrSpec.ringChar hN hk hb hb0 u`. Use `mem := fun k hk b hb z hz l _ a ha => GrSpec.mem hN hk hb z hz ha }`.
-/
theorem exists_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F),
    GradedFam c₀ N → (∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0) → ∃ (P : Scheme.{0}) (_ : IsIntegral P) (p : P ⟶ Sp R)
      (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp := by
  intro R F _ _ _ c₀ N hN h
  obtain ⟨k₀, hk₀, b₀, hb₀, h₀⟩ := h
  haveI := GrSpec.isIntegral hN hk₀ hb₀ h₀
  refine ⟨Proj (GrSpec.piece hN), inferInstance, GrSpec.pstr hN, GrSpec.psi hN, GrSpec.Dp hN, ?_⟩
  exact
    { sep := GrSpec.sep hN
      const := GrSpec.const hN
      affine := fun k hk b hb => GrSpec.affine hN hk hb
      cover := GrSpec.cover hN
      gen := fun k _ b hb => GrSpec.genMem hN ⟨k₀, hk₀, b₀, hb₀, h₀⟩ hb
      ring := fun k hk b hb hb0 u => GrSpec.ringChar hN hk hb hb0 u
      mem := fun k hk b hb z hz l _ a ha => GrSpec.mem hN hk hb z hz ha }

end GlobalTheory.Desc
