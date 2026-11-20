import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.DiscreteGroups.GlobalIrreducibility.DzGalTR
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameRecAll

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Polynomial

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Res

variable {Ω : Type} [Field Ω]

private def toRes (A : ValuationSubring Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω] :
    𝓞 F →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp
    { toFun := fun x => ⟨algebraMap F Ω (x : F), ReciprocityTheory.Gal.mem_of_isIntegral_int A (x.2.map (algebraMap F Ω).toIntAlgHom)⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }

/- English proof (translation)
Unfold `toRes`. Rewrite using `[RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]`. Conclude with `A.valuation_lt_one_iff _`.
-/
private theorem toRes_eq_zero_iff (A : ValuationSubring Ω) {F : Type} [Field F] [NumberField F] [Algebra F Ω] (x : 𝓞 F) :
    toRes A F x = 0 ↔ A.valuation (algebraMap F Ω (x : F)) < 1 := by
  unfold toRes
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
  exact A.valuation_lt_one_iff _

/- English proof (translation)
Unfold `toRes`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Conclude with `(A.valuation_lt_one_iff _).2 hxy`.
-/
private theorem toRes_eq_of_val {A : ValuationSubring Ω} {F F' : Type} [Field F] [NumberField F] [Algebra F Ω]
    [Field F'] [NumberField F'] [Algebra F' Ω] (x : 𝓞 F) (y : 𝓞 F')
    (hxy : A.valuation (algebraMap F Ω (x : F) - algebraMap F' Ω (y : F')) < 1) : toRes A F x = toRes A F' y := by
  unfold toRes
  rw [RingHom.comp_apply, RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact (A.valuation_lt_one_iff _).2 hxy

/- English proof (translation)
Use `⟨RingHom.liftOfSurjective red hs ⟨toRes A F, fun x hx => ?_⟩, fun x => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[hk]`. Rewrite using `[RingHom.mem_ker, toRes_eq_zero_iff]`. Conclude with `(hv x).2 hx`. Conclude with `RingHom.liftOfRightInverse_comp_apply _ _ _ _ _`.
-/
private theorem exists_emb {A : ValuationSubring Ω} {F : Type} [Field F] [NumberField F] [Algebra F Ω]
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsPlaceOver A v) {K : Type} [Field K] (red : 𝓞 F →+* K)
    (hs : Function.Surjective red) (hk : RingHom.ker red = v.asIdeal) :
    ∃ ι : K →+* IsLocalRing.ResidueField A, ∀ x, ι (red x) = toRes A F x := by
  refine ⟨RingHom.liftOfSurjective red hs ⟨toRes A F, fun x hx => ?_⟩, fun x => ?_⟩
  · rw [hk] at hx
    rw [RingHom.mem_ker, toRes_eq_zero_iff]
    exact (hv x).2 hx
  · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

/- English proof (translation)
Establish `e` using `(Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hs)`. Conclude with `(Nat.card_congr e.toEquiv).symm`.
-/
private theorem card_K {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {K : Type} [Field K]
    (red : 𝓞 F →+* K) (hs : Function.Surjective red) (hk : RingHom.ker red = v.asIdeal) :
    Nat.card K = normV v := by
  have e := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hs)
  exact (Nat.card_congr e.toEquiv).symm

open Classical in
/- English proof (translation)
Establish `: Finite K` using `Nat.finite_of_card_ne_zero (by omega)`. Use `Fintype.ofFinite K` as an intermediate fact. Establish `hne : (X ^ q - X : κ[X]) ≠ 0` using `FiniteField.X_pow_card_sub_X_ne_zero κ hq`. Establish `hsub : (ι.range : Set κ) ⊆ ((X ^ q - X : κ[X]).roots.toFinset : Set κ)`. Introduce and unpack `_ ⟨y, rfl⟩`.

Simplify using `only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hne, IsRoot.def, eval_sub, eval_pow, eval_X]`. Rewrite using `[← map_pow, ← hc, Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]`. Use `Set.eq_of_subset_of_ncard_le hsub ?_ (Finset.finite_toSet _)` and prove the remaining obligations. Establish `h1 : (ι.range : Set κ).ncard = q`. Rewrite using `[RingHom.coe_range, ← Set.image_univ, Set.ncard_image_of_injective _ ι.injective, Set.ncard_univ, hc]`.

Rewrite using `[h1, Set.ncard_coe_finset]`. Use `(Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)` and prove the remaining obligations. Rewrite using `[FiniteField.X_pow_card_sub_X_natDegree_eq κ hq]`.
-/
private theorem range_sub {κ K : Type} [Field κ] [Field K] (ι : K →+* κ) (q : ℕ) (hq : 1 < q) (hc : Nat.card K = q) :
    (ι.range : Set κ) = ((X ^ q - X : κ[X]).roots.toFinset : Set κ) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite K
  have hne : (X ^ q - X : κ[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero κ hq
  have hsub : (ι.range : Set κ) ⊆ ((X ^ q - X : κ[X]).roots.toFinset : Set κ) := by
    rintro _ ⟨y, rfl⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hne, IsRoot.def, eval_sub, eval_pow, eval_X]
    rw [← map_pow, ← hc, Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Finset.finite_toSet _)
  have h1 : (ι.range : Set κ).ncard = q := by
    rw [RingHom.coe_range, ← Set.image_univ, Set.ncard_image_of_injective _ ι.injective, Set.ncard_univ, hc]
  rw [h1, Set.ncard_coe_finset]
  refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq κ hq]

/- English proof (translation)
Establish `hr : ι.range = ι'.range`. Apply `SetLike.coe_injective` to reduce the goal to its premises. Rewrite using `[range_sub ι q hq hc, range_sub ι' q hq hc']`. Set `e1 : K ≃+* ι.range` to `RingEquiv.ofBijective ι.rangeRestrict ⟨ι.rangeRestrict.injective, ι.rangeRestrict_surjective⟩`. Set `e2 : K' ≃+* ι'.range` to `RingEquiv.ofBijective ι'.rangeRestrict ⟨ι'.rangeRestrict.injective, ι'.rangeRestrict_surjective⟩`.

Use `⟨(e1.trans (RingEquiv.subringCongr hr)).trans e2.symm, fun y => ?_⟩` and prove the remaining obligations. Establish `h2 : ∀ z : ι'.range, ι' (e2.symm z) = z` using `fun z => by`. Establish `: (e2 (e2.symm z) : κ) = z` using `by rw [RingEquiv.apply_symm_apply]`. Conclude with `this`. Conclude with `h2 (RingEquiv.subringCongr hr (e1 y))`.
-/
private theorem exists_equiv {κ K K' : Type} [Field κ] [Field K] [Field K'] (ι : K →+* κ) (ι' : K' →+* κ) (q : ℕ) (hq : 1 < q)
    (hc : Nat.card K = q) (hc' : Nat.card K' = q) : ∃ e : K ≃+* K', ∀ y, ι' (e y) = ι y := by
  have hr : ι.range = ι'.range := by
    apply SetLike.coe_injective
    rw [range_sub ι q hq hc, range_sub ι' q hq hc']
  let e1 : K ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict ⟨ι.rangeRestrict.injective, ι.rangeRestrict_surjective⟩
  let e2 : K' ≃+* ι'.range := RingEquiv.ofBijective ι'.rangeRestrict ⟨ι'.rangeRestrict.injective, ι'.rangeRestrict_surjective⟩
  refine ⟨(e1.trans (RingEquiv.subringCongr hr)).trans e2.symm, fun y => ?_⟩
  have h2 : ∀ z : ι'.range, ι' (e2.symm z) = z := fun z => by
    have : (e2 (e2.symm z) : κ) = z := by rw [RingEquiv.apply_symm_apply]
    exact this
  exact h2 (RingEquiv.subringCongr hr (e1 y))

end Res

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Take `⟨t', ht', e⟩` from `DiscreteGroups.sglob.DzType.ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2`. Take `⟨x, hx⟩` from `DiscreteGroups.sglob.DzType.exists_int_approx_compl D.w' _ (DiscreteGroups.sglob.DzType.val_artin_ine D.ha' ⟨t', ht'⟩).le`. Establish `hne` using `DiscreteGroups.sglob.DzType.red_ne_zero_of_approx D.ha' D.ker hx`. Use `⟨⟨t', ht'⟩, x, fun z => by rw [← e]; rfl, hx, ?_⟩` and prove the remaining obligations. Use `hR t ⟨t', ht'⟩ x (Units.mk0 _ hne) e.symm rfl hx` as an intermediate fact.

Rewrite using `[this]`. Both sides reduce to the same expression.
-/
private theorem res_read {g n : ℕ} [Fact g.Prime] (hn : 0 < n) (D : Ext h g n) (R : Ine (F := E) A →* D.Kˣ) (hR : D.Res R)
    (t : Ine (F := E) A) : ∃ (t' : Ine (F := D.E') A) (x : 𝓞 D.E'),
      (∀ z : Ω, (t : G E Ω) z = (t' : G D.E' Ω) z) ∧
      Valued.v ((D.a' (ineIncl D.h' t') : D.w'.adicCompletion D.E') - algebraMap D.E' (D.w'.adicCompletion D.E') (x : D.E')) < 1 ∧
      ((R t : D.Kˣ) : D.K) = D.red x := by
  obtain ⟨t', ht', e⟩ := DiscreteGroups.sglob.DzType.ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
  obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl D.w' _ (DiscreteGroups.sglob.DzType.val_artin_ine D.ha' ⟨t', ht'⟩).le
  have hne := DiscreteGroups.sglob.DzType.red_ne_zero_of_approx D.ha' D.ker hx
  refine ⟨⟨t', ht'⟩, x, fun z => by rw [← e]; rfl, hx, ?_⟩
  have := hR t ⟨t', ht'⟩ x (Units.mk0 _ hne) e.symm rfl hx
  rw [this]; rfl

/- English proof (translation)
Take `⟨ι, hι⟩` from `exists_emb D.h' D.red D.surj D.ker`. Take `⟨ι', hι'⟩` from `exists_emb D'.h' D'.red D'.surj D'.ker`. Establish `hq : 1 < g ^ n` using `Nat.one_lt_pow hn.ne' (Fact.out : g.Prime).one_lt`. Take `⟨e, he⟩` from `exists_equiv ι ι' (g ^ n) hq ((card_K D.red D.surj D.ker).trans D.card) ((card_K D'.red D'.surj D'.ker).trans D'.card)`. Use `⟨e, fun t => ι'.injective ?_⟩` and prove the remaining obligations.

Take `⟨t1, x, h1, a1, r1⟩` from `res_read hn D R hR t`. Take `⟨t2, y, h2, a2, r2⟩` from `res_read hn D' R' hR' t`. Rewrite using `[he, r1, r2, hι, hι']`. Conclude with `(toRes_eq_of_val x y (hm t1 t2 (fun z => by rw [← h1, h2]) x y a1 a2)).symm`.
-/
private theorem core {g n : ℕ} [Fact g.Prime] (hn : 0 < n) (D D' : Ext h g n)
    (R : Ine (F := E) A →* D.Kˣ) (R' : Ine (F := E) A →* D'.Kˣ) (hR : D.Res R) (hR' : D'.Res R')
    (hm : ∀ (t : Ine (F := D.E') A) (t' : Ine (F := D'.E') A), (∀ z : Ω, (t : G D.E' Ω) z = (t' : G D'.E' Ω) z) →
      ∀ (x : 𝓞 D.E') (y : 𝓞 D'.E'),
      Valued.v ((D.a' (ineIncl D.h' t) : D.w'.adicCompletion D.E') - algebraMap D.E' (D.w'.adicCompletion D.E') (x : D.E')) < 1 →
      Valued.v ((D'.a' (ineIncl D'.h' t') : D'.w'.adicCompletion D'.E') - algebraMap D'.E' (D'.w'.adicCompletion D'.E') (y : D'.E')) < 1 →
      A.valuation (algebraMap D.E' Ω (x : D.E') - algebraMap D'.E' Ω (y : D'.E')) < 1) :
    ∃ e : D.K ≃+* D'.K, ∀ t, ((R' t : D'.Kˣ) : D'.K) = e (R t : D.Kˣ) := by
  obtain ⟨ι, hι⟩ := exists_emb D.h' D.red D.surj D.ker
  obtain ⟨ι', hι'⟩ := exists_emb D'.h' D'.red D'.surj D'.ker
  have hq : 1 < g ^ n := Nat.one_lt_pow hn.ne' (Fact.out : g.Prime).one_lt
  obtain ⟨e, he⟩ := exists_equiv ι ι' (g ^ n) hq ((card_K D.red D.surj D.ker).trans D.card)
    ((card_K D'.red D'.surj D'.ker).trans D'.card)
  refine ⟨e, fun t => ι'.injective ?_⟩
  obtain ⟨t1, x, h1, a1, r1⟩ := res_read hn D R hR t
  obtain ⟨t2, y, h2, a2, r2⟩ := res_read hn D' R' hR' t
  rw [he, r1, r2, hι, hι']
  exact (toRes_eq_of_val x y (hm t1 t2 (fun z => by rw [← h1, h2]) x y a1 a2)).symm

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h g _ i hi n hn D D' R R' hR hR'`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed E`. Establish `hq : 1 < g ^ n` using `Nat.one_lt_pow hn.ne' (Fact.out : g.Prime).one_lt`. Take `⟨π, hπ⟩` from `IsAlgClosed.exists_pow_nat_eq (g : Ω) (show 0 < g ^ n - 1 by omega)`. Use `core hn D D' R R' hR hR' fun t t' htt x y hx hy => ?_` and prove the remaining obligations.

Establish `hg` using `DiscreteGroups.sglob.DzType.natCast_mem_of_normV D.w' g n hn D.card`. Establish `hg'` using `DiscreteGroups.sglob.DzType.natCast_mem_of_normV D'.w' g n hn D'.card`. Establish `h1` using `tameRecAll D.E' Ω g A D.w' D.h' hg D.unr D.a' D.ha' π (by rw [D.card]; exact hπ) t x hx`. Establish `h2` using `tameRecAll D'.E' Ω g A D'.w' D'.h' hg' D'.unr D'.a' D'.ha' π (by rw [D'.card]; exact hπ) t' y hy`. Rewrite `h2` using `[← htt]`.

Establish `e : algebraMap D.E' Ω (x : D.E') - algebraMap D'.E' Ω (y : D'.E') = ((t : G D.E' Ω) π / π - algebraMap D'.E' Ω (y : D'.E')) - ((t : G D.E' Ω) π / π - algebraMap D.E' Ω (x : D.E'))` using `by ring`. Rewrite using `[e]`. Conclude with `lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h2 h1)`.
-/
theorem resIndep : ResIndep := by
  intro E Ω _ _ _ _ _ A w h g _ i hi n hn D D' R R' hR hR'
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hq : 1 < g ^ n := Nat.one_lt_pow hn.ne' (Fact.out : g.Prime).one_lt
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (g : Ω) (show 0 < g ^ n - 1 by omega)
  refine core hn D D' R R' hR hR' fun t t' htt x y hx hy => ?_
  have hg := DiscreteGroups.sglob.DzType.natCast_mem_of_normV D.w' g n hn D.card
  have hg' := DiscreteGroups.sglob.DzType.natCast_mem_of_normV D'.w' g n hn D'.card
  have h1 := tameRecAll D.E' Ω g A D.w' D.h' hg D.unr D.a' D.ha' π (by rw [D.card]; exact hπ) t x hx
  have h2 := tameRecAll D'.E' Ω g A D'.w' D'.h' hg' D'.unr D'.a' D'.ha' π (by rw [D'.card]; exact hπ) t' y hy
  rw [← htt] at h2
  have e : algebraMap D.E' Ω (x : D.E') - algebraMap D'.E' Ω (y : D'.E') =
      ((t : G D.E' Ω) π / π - algebraMap D'.E' Ω (y : D'.E')) - ((t : G D.E' Ω) π / π - algebraMap D.E' Ω (x : D.E')) := by ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h2 h1)

end UpperTheory.Zero.LLC

end
