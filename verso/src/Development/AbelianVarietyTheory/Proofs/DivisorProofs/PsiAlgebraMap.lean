import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial HomogeneousLocalization
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Desc.GrSpec

variable {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F}

def ring (hN : GradedFam c₀ N) : Subring F[X] where
  carrier := {p | ∀ k, p.coeff k ∈ N k}
  mul_mem' {p q} hp hq k := by
    rw [coeff_mul]
    refine Finset.sum_induction _ (· ∈ N k) (fun a b ha hb => hN.add k a ha b hb) (hN.zero k) ?_
    rintro ⟨i, j⟩ hij
    have hij' : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hij
    subst hij'
    exact hN.mul i j _ (hp i) _ (hq j)
  one_mem' k := by
    rw [coeff_one]
    split_ifs with h
    · subst h; exact hN.one
    · exact hN.zero k
  add_mem' {p q} hp hq k := by rw [coeff_add]; exact hN.add k _ (hp k) _ (hq k)
  zero_mem' k := by rw [coeff_zero]; exact hN.zero k
  neg_mem' {p} hp k := by
    rw [coeff_neg]
    have := hN.smul k (-1) _ (hp k)
    simpa using this

/- English proof (translation)
Introduce `j`. Rewrite using `[coeff_monomial]`. Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `hb`.

Conclude with `hN.zero j`.
-/
theorem monomial_mem (hN : GradedFam c₀ N) {k : ℕ} {b : F} (hb : b ∈ N k) : monomial k b ∈ ring hN := by
  intro j
  rw [coeff_monomial]
  split_ifs with h
  · subst h; exact hb
  · exact hN.zero j

def piece (hN : GradedFam c₀ N) (k : ℕ) : AddSubgroup (ring hN) where
  carrier := {p | ∀ j, j ≠ k → (p : F[X]).coeff j = 0}
  add_mem' {p q} hp hq j hj := by
    rw [Subring.coe_add, coeff_add, hp j hj, hq j hj, add_zero]
  zero_mem' j _ := by rw [Subring.coe_zero, coeff_zero]
  neg_mem' {p} hp j hj := by rw [Subring.coe_neg, coeff_neg, hp j hj, neg_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hp`. Use extensionality with `j`. Rewrite using `[coeff_monomial]`. Use `split_ifs with h`.

Rewrite using `[h]`. Conclude with `hp j (Ne.symm h)`. Introduce `hp j hj`. Rewrite using `[hp, coeff_monomial, if_neg (Ne.symm hj)]`.
-/
theorem mem_piece_iff (hN : GradedFam c₀ N) {k : ℕ} {p : ring hN} :
    p ∈ piece hN k ↔ (p : F[X]) = monomial k ((p : F[X]).coeff k) := by
  constructor
  · intro hp
    ext j
    rw [coeff_monomial]
    split_ifs with h
    · rw [h]
    · exact hp j (Ne.symm h)
  · intro hp j hj
    rw [hp, coeff_monomial, if_neg (Ne.symm hj)]

def hel (hN : GradedFam c₀ N) (k : ℕ) (b : F) (hb : b ∈ N k) : ring hN := ⟨monomial k b, monomial_mem hN hb⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_hel (hN : GradedFam c₀ N) (k : ℕ) (b : F) (hb : b ∈ N k) :
    (hel hN k b hb : F[X]) = monomial k b := rfl

/- English proof (translation)
Rewrite using `[mem_piece_iff, coe_hel, coeff_monomial, if_pos rfl]`.
-/
theorem hel_mem (hN : GradedFam c₀ N) (k : ℕ) (b : F) (hb : b ∈ N k) : hel hN k b hb ∈ piece hN k := by
  rw [mem_piece_iff, coe_hel, coeff_monomial, if_pos rfl]

/- English proof (translation)
Introduce `e`. Use `congrArg (fun p : ring hN => (p : F[X]).coeff k) e` as an intermediate fact. Simplify using `[coeff_monomial] at this`. Conclude with `h this`.
-/
theorem hel_ne_zero (hN : GradedFam c₀ N) {k : ℕ} {b : F} (hb : b ∈ N k) (h : b ≠ 0) : hel hN k b hb ≠ 0 := by
  intro e
  have := congrArg (fun p : ring hN => (p : F[X]).coeff k) e
  simp [coeff_monomial] at this
  exact h this

def comp (hN : GradedFam c₀ N) (k : ℕ) : ring hN →+ piece hN k where
  toFun p := ⟨⟨monomial k ((p : F[X]).coeff k), monomial_mem hN (p.2 k)⟩, by
    intro j hj; simp [coeff_monomial, Ne.symm hj]⟩
  map_zero' := by ext; simp
  map_add' p q := by ext; simp

/- English proof (translation)
Use `ext`. Simplify using `[comp, h]`.
-/
theorem comp_eq_zero (hN : GradedFam c₀ N) {k : ℕ} {p : ring hN} (h : (p : F[X]).coeff k = 0) : comp hN k p = 0 := by
  ext; simp [comp, h]

/- English proof (translation)
Use `ext1`. Conclude with `((mem_piece_iff hN).1 h).symm`.
-/
theorem comp_of_mem (hN : GradedFam c₀ N) {k : ℕ} {p : ring hN} (h : p ∈ piece hN k) : (comp hN k p : ring hN) = p := by
  ext1; exact ((mem_piece_iff hN).1 h).symm

def dec (hN : GradedFam c₀ N) (p : ring hN) : DirectSum ℕ (fun k => piece hN k) :=
  ∑ k ∈ (p : F[X]).support, DirectSum.of (fun k => piece hN k) k (comp hN k p)

/- English proof (translation)
Use `Finset.sum_subset hS fun k _ hk => ?_` and prove the remaining obligations. Rewrite using `[comp_eq_zero hN (notMem_support_iff.1 hk), map_zero]`.
-/
theorem dec_eq (hN : GradedFam c₀ N) (p : ring hN) (S : Finset ℕ) (hS : (p : F[X]).support ⊆ S) :
    dec hN p = ∑ k ∈ S, DirectSum.of (fun k => piece hN k) k (comp hN k p) := by
  refine Finset.sum_subset hS fun k _ hk => ?_
  rw [comp_eq_zero hN (notMem_support_iff.1 hk), map_zero]

def decHom (hN : GradedFam c₀ N) : ring hN →+ DirectSum ℕ (fun k => piece hN k) where
  toFun := dec hN
  map_zero' := by simp [dec]
  map_add' p q := by
    classical
    set S := (p : F[X]).support ∪ (q : F[X]).support ∪ ((p + q : ring hN) : F[X]).support
    rw [dec_eq hN _ S (fun x hx => Finset.mem_union_right _ hx),
      dec_eq hN p S (fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)),
      dec_eq hN q S (fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, map_add]

instance gradedMonoid (hN : GradedFam c₀ N) : SetLike.GradedMonoid (piece hN) where
  one_mem j hj := by
    change (1 : F[X]).coeff j = 0
    rw [coeff_one, if_neg hj]
  mul_mem i j a b ha hb := by
    rw [mem_piece_iff] at ha hb
    intro l hl
    rw [Subring.coe_mul, ha, hb, monomial_mul_monomial, coeff_monomial, if_neg (Ne.symm hl)]

instance gradedRing (hN : GradedFam c₀ N) : GradedRing (piece hN) :=
  { gradedMonoid hN with
    toDecomposition := DirectSum.Decomposition.ofAddHom (piece hN) (decHom hN)
      (by
        refine AddMonoidHom.ext fun p => Subtype.ext ?_
        change (((DirectSum.coeAddMonoidHom (piece hN)) (dec hN p) : ring hN) : F[X]) = p
        rw [dec, map_sum]
        simp only [DirectSum.coeAddMonoidHom_of]
        rw [AddSubmonoidClass.coe_finset_sum]
        exact (as_sum_support _).symm)
      (by
        refine DirectSum.addHom_ext fun k y => ?_
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, DirectSum.coeAddMonoidHom_of]
        change dec hN (y : ring hN) = DirectSum.of _ k y
        rw [dec_eq hN _ {k} (fun j hj => by
          by_contra h'
          exact (mem_support_iff.1 hj) (y.2 j (by simpa using h')))]
        rw [Finset.sum_singleton]
        congr 1
        exact Subtype.ext (comp_of_mem hN y.2)) }

section Frac

variable (F) in

def cL : F →+* FractionRing F[X] := (algebraMap F[X] (FractionRing F[X])).comp C

/- English proof (translation)
The claim follows from `(IsFractionRing.injective F[X] (FractionRing F[X])).comp C_injective`.
-/
theorem cL_injective : Function.Injective (cL F) :=
  (IsFractionRing.injective F[X] (FractionRing F[X])).comp C_injective

def toL (hN : GradedFam c₀ N) : ring hN →+* FractionRing F[X] :=
  (algebraMap F[X] (FractionRing F[X])).comp (ring hN).subtype

/- English proof (translation)
The claim follows from `(IsFractionRing.injective F[X] (FractionRing F[X])).comp Subtype.val_injective`.
-/
theorem toL_injective (hN : GradedFam c₀ N) : Function.Injective (toL hN) :=
  (IsFractionRing.injective F[X] (FractionRing F[X])).comp Subtype.val_injective

variable (hN : GradedFam c₀ N) (P : Ideal (ring hN)) [P.IsPrime]

def liftAt : Localization.AtPrime P →+* FractionRing F[X] :=
  IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) (g := toL hN) fun s =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (toL_injective hN)).2 fun h => s.2 (h ▸ P.zero_mem))

def valL : AtPrime (piece hN) P →+* FractionRing F[X] :=
  (liftAt hN P).comp (algebraMap (AtPrime (piece hN) P) (Localization.AtPrime P))

/- English proof (translation)
Establish `hnum` using `(mem_piece_iff hN).1 g.num.2`. Establish `hden` using `(mem_piece_iff hN).1 g.den.2`. Establish `hs : ((g.den : ring hN) : F[X]).coeff g.deg ≠ 0`. Introduce `h0`. Apply `g.den_mem` to reduce the goal to its premises.

Establish `: (g.den : ring hN) = 0` using `Subtype.ext (by rw [hden, h0, map_zero]; rfl)`. Rewrite using `[this]`. Conclude with `P.zero_mem`. Express the relevant statement in the definitionally equal form `liftAt hN P (mk g).val = _`. Rewrite using `[val_mk, Localization.mk_eq_mk', liftAt, IsLocalization.lift_mk'_spec]`.

Express the relevant statement in the definitionally equal form `algebraMap F[X] _ ((g.num : ring hN) : F[X]) = algebraMap F[X] _ ((g.den : ring hN) : F[X]) * algebraMap F[X] _ (C _)`. Rewrite using `[← map_mul]`. Use `congr 1`. Rewrite using `[hnum, hden, coeff_monomial, if_pos rfl, coeff_monomial, if_pos rfl, monomial_mul_C, mul_div_cancel₀ _ hs]`.
-/
theorem valL_mk (g : NumDenSameDeg (piece hN) P.primeCompl) :
    valL hN P (mk g) = cL F (((g.num : ring hN) : F[X]).coeff g.deg / ((g.den : ring hN) : F[X]).coeff g.deg) := by
  have hnum := (mem_piece_iff hN).1 g.num.2
  have hden := (mem_piece_iff hN).1 g.den.2
  have hs : ((g.den : ring hN) : F[X]).coeff g.deg ≠ 0 := by
    intro h0
    apply g.den_mem
    have : (g.den : ring hN) = 0 := Subtype.ext (by rw [hden, h0, map_zero]; rfl)
    rw [this]; exact P.zero_mem
  change liftAt hN P (mk g).val = _
  rw [val_mk, Localization.mk_eq_mk', liftAt, IsLocalization.lift_mk'_spec]
  change algebraMap F[X] _ ((g.num : ring hN) : F[X]) =
    algebraMap F[X] _ ((g.den : ring hN) : F[X]) * algebraMap F[X] _ (C _)
  rw [← map_mul]
  congr 1
  rw [hnum, hden, coeff_monomial, if_pos rfl, coeff_monomial, if_pos rfl, monomial_mul_C, mul_div_cancel₀ _ hs]

variable (F) in

def eqR : F ≃+* (cL F).range :=
  RingEquiv.ofBijective (cL F).rangeRestrict
    ⟨fun a b h => cL_injective (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩

def valR : AtPrime (piece hN) P →+* (cL F).range :=
  (valL hN P).codRestrict (cL F).range fun y => by
    obtain ⟨g, rfl⟩ := mk_surjective y
    exact ⟨_, (valL_mk hN P g).symm⟩

def psiAt : AtPrime (piece hN) P →+* F := (eqR F).symm.toRingHom.comp (valR hN P)

/- English proof (translation)
The claim follows from `congrArg Subtype.val ((eqR F).apply_symm_apply (valR hN P y))`.
-/
theorem cL_psiAt (y : AtPrime (piece hN) P) : cL F (psiAt hN P y) = valL hN P y :=
  congrArg Subtype.val ((eqR F).apply_symm_apply (valR hN P y))

/- English proof (translation)
The claim follows from `cL_injective (by rw [cL_psiAt, valL_mk])`.
-/
theorem psiAt_mk (g : NumDenSameDeg (piece hN) P.primeCompl) :
    psiAt hN P (mk g) = ((g.num : ring hN) : F[X]).coeff g.deg / ((g.den : ring hN) : F[X]).coeff g.deg :=
  cL_injective (by rw [cL_psiAt, valL_mk])

end Frac

section Scheme

variable (hN : GradedFam c₀ N)

instance isPrime_point (x : Proj (piece hN)) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  ProjectiveSpectrum.isPrime x

def gen {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (h0 : b ≠ 0) : Proj (piece hN) :=
  ⟨⊥, Ideal.isPrime_bot, fun h => hel_ne_zero hN hb h0 (by
    have : hel hN k b hb ∈ HomogeneousIdeal.irrelevant (piece hN) := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne (piece hN) (hel_mem hN k b hb) (by omega)]
    exact h this)⟩

/- English proof (translation)
Establish `hred : IsReduced (Proj (piece hN))`. Establish `(x : Proj (piece hN)) : _root_.IsReduced ((Proj (piece hN)).presheaf.stalk x)`. Set `x' : ProjectiveSpectrum (piece hN)` to `x`. Establish `h1 : _root_.IsReduced (HomogeneousLocalization.AtPrime (piece hN) x'.asHomogeneousIdeal.toIdeal)` using `isReduced_of_injective (algebraMap _ (Localization.AtPrime x'.asHomogeneousIdeal.toIdeal)) (HomogeneousLocalization.val_injective _)`. Conclude with `isReduced_of_injective (Proj.stalkIso' (piece hN) x') (Proj.stalkIso' (piece hN) x').injective`.

Conclude with `isReduced_of_isReduced_stalk _`. Establish `hcl : closure ({gen hN hk hb h0} : Set (ProjectiveSpectrum (piece hN))) = Set.univ`. Use `Set.eq_univ_of_forall fun y => ?_` and prove the remaining obligations. Conclude with `(ProjectiveSpectrum.le_iff_mem_closure (piece hN) (gen hN hk hb h0) y).1 (by show (⊥ : HomogeneousIdeal (piece hN)) ≤ y.asHomogeneousIdeal`. Conclude with `bot_le)`.

Establish `hirr : IrreducibleSpace (ProjectiveSpectrum (piece hN))`. Use `(irreducibleSpace_def _).2 ?_` and prove the remaining obligations. Rewrite using `[Set.top_eq_univ, ← hcl]`. Conclude with `(isIrreducible_singleton (x := gen hN hk hb h0)).closure`. Establish `: IrreducibleSpace (Proj (piece hN))` using `hirr`.

Conclude with `isIntegral_of_irreducibleSpace_of_isReduced _`.
-/
theorem isIntegral {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (h0 : b ≠ 0) : IsIntegral (Proj (piece hN)) := by
  have hred : IsReduced (Proj (piece hN)) := by
    have (x : Proj (piece hN)) : _root_.IsReduced ((Proj (piece hN)).presheaf.stalk x) := by
      let x' : ProjectiveSpectrum (piece hN) := x
      have h1 : _root_.IsReduced (HomogeneousLocalization.AtPrime (piece hN) x'.asHomogeneousIdeal.toIdeal) :=
        isReduced_of_injective (algebraMap _ (Localization.AtPrime x'.asHomogeneousIdeal.toIdeal))
          (HomogeneousLocalization.val_injective _)
      exact isReduced_of_injective (Proj.stalkIso' (piece hN) x') (Proj.stalkIso' (piece hN) x').injective
    exact isReduced_of_isReduced_stalk _
  have hcl : closure ({gen hN hk hb h0} : Set (ProjectiveSpectrum (piece hN))) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    exact (ProjectiveSpectrum.le_iff_mem_closure (piece hN) (gen hN hk hb h0) y).1 (by
      show (⊥ : HomogeneousIdeal (piece hN)) ≤ y.asHomogeneousIdeal
      exact bot_le)
  have hirr : IrreducibleSpace (ProjectiveSpectrum (piece hN)) := by
    refine (irreducibleSpace_def _).2 ?_
    rw [Set.top_eq_univ, ← hcl]
    exact (isIrreducible_singleton (x := gen hN hk hb h0)).closure
  have : IrreducibleSpace (Proj (piece hN)) := hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

def toZero : R →+* piece hN 0 where
  toFun r := ⟨⟨C (c₀ r), by
      have : c₀ r * 1 ∈ N 0 := hN.smul 0 r 1 hN.one
      rw [mul_one] at this
      exact monomial_mem hN (k := 0) this⟩, by
    intro j hj; simp [coeff_C, hj]⟩
  map_one' := by ext1; ext1; simp
  map_mul' a b := by ext1; ext1; simp
  map_zero' := by ext1; ext1; simp
  map_add' a b := by ext1; ext1; simp

def pmap : Proj (piece hN) ⟶ Sp R := Proj.toSpecZero (piece hN) ≫ Spec.map (CommRingCat.ofHom (toZero hN))

def Dp (k : ℕ) (b : F) : (Proj (piece hN)).Opens := by
  classical exact if hb : b ∈ N k then Proj.basicOpen (piece hN) (hel hN k b hb) else ⊥

/- English proof (translation)
Rewrite using `[Dp, dif_pos hb]`.
-/
theorem Dp_of_mem {k : ℕ} {b : F} (hb : b ∈ N k) : Dp hN k b = Proj.basicOpen (piece hN) (hel hN k b hb) := by
  rw [Dp, dif_pos hb]

def psi [IsIntegral (Proj (piece hN))] : (Proj (piece hN)).functionField →+* F :=
  (psiAt hN _).comp (Proj.stalkIso' (piece hN) (genericPoint (Proj (piece hN)))).toRingHom

/- English proof (translation)
Take `⟨g, hg⟩` from `mk_surjective (Proj.stalkIso' (piece hN) x w)`. Establish `hw : w = (Proj.stalkIso' (piece hN) x).symm (mk g)` using `((Proj.stalkIso' (piece hN) x).symm_apply_apply w).symm.trans (congrArg _ hg.symm)`. Substitute `hw` using the available equality. Establish `hsp : genericPoint (Proj (piece hN)) ⤳ x` using `genericPoint_specializes x`. Establish `hle : (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal ≤ x.asHomogeneousIdeal.toIdeal` using `(ProjectiveSpectrum.le_iff_mem_closure (piece hN) _ _).2 (specializes_iff_mem_closure.1 hsp)`.

Establish `key : Proj.stalkIso' (piece hN) (genericPoint (Proj (piece hN))) ((Proj (piece hN)).presheaf.stalkSpecializes hsp ((Proj.stalkIso' (piece hN) x).symm (mk g))) = mk (⟨g.deg, g.num, g.den, fun hy => g.den_mem (hle hy)⟩ : NumDenSameDeg (piece hN) (genericPoint (Proj (piece hN))).asH …` using `by erw [Proj.stalkIso'_symm_mk, TopCat.Presheaf.germ_stalkSpecializes_apply, Proj.stalkIso'_germ]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.stalkSpecializes hsp _)) = _`. Rewrite using `[key, RingEquiv.apply_symm_apply, psiAt_mk, psiAt_mk]`.
-/
theorem psi_algebraMap [IsIntegral (Proj (piece hN))] (x : Proj (piece hN)) (w : (Proj (piece hN)).presheaf.stalk x) :
    psi hN (algebraMap _ _ w) = psiAt hN _ (Proj.stalkIso' (piece hN) x w) := by
  obtain ⟨g, hg⟩ := mk_surjective (Proj.stalkIso' (piece hN) x w)
  have hw : w = (Proj.stalkIso' (piece hN) x).symm (mk g) :=
    ((Proj.stalkIso' (piece hN) x).symm_apply_apply w).symm.trans (congrArg _ hg.symm)
  subst hw
  have hsp : genericPoint (Proj (piece hN)) ⤳ x := genericPoint_specializes x
  have hle : (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal ≤ x.asHomogeneousIdeal.toIdeal :=
    (ProjectiveSpectrum.le_iff_mem_closure (piece hN) _ _).2 (specializes_iff_mem_closure.1 hsp)
  have key : Proj.stalkIso' (piece hN) (genericPoint (Proj (piece hN)))
      ((Proj (piece hN)).presheaf.stalkSpecializes hsp ((Proj.stalkIso' (piece hN) x).symm (mk g))) =
      mk (⟨g.deg, g.num, g.den, fun hy => g.den_mem (hle hy)⟩ :
        NumDenSameDeg (piece hN) (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal.primeCompl) := by
    erw [Proj.stalkIso'_symm_mk, TopCat.Presheaf.germ_stalkSpecializes_apply, Proj.stalkIso'_germ]
    rfl
  change psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.stalkSpecializes hsp _)) = _
  rw [key, RingEquiv.apply_symm_apply, psiAt_mk, psiAt_mk]

end Scheme

end GlobalTheory.Desc.GrSpec
