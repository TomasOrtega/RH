import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveEtaleCohomologyMultiplicativeGroupProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianEtaleStalkOverPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCofilteredLimitAffineEtaleOfIsStalkStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorIsFinitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistRingFunctorPreservesFilteredColimitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousCofilteredAffineLimitStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.KunRed

/- English proof (translation)
The claim follows from `GlobalTheory.T.cup_hypercohomologyPullback _ (twPair q i j) f rfl a b`.
-/
private theorem pull_cup' {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n m i j : ℤ} (a : Ht q E' n i) (b : Ht q E' m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b) :=
  GlobalTheory.T.cup_hypercohomologyPullback _ (twPair q i j) f rfl a b

private noncomputable def Phi (q : ℕ) (m j : ℤ) (V : Scheme.{0})
    (p : Ht q (sch.obj V) (m + 1) (j + 1) × Ht q (sch.obj V) m j) : Ht q (sch.obj (Gq q ⨯ V)) (m + 1) (j + 1) :=
  pull _ (sch.map (prod.snd : Gq q ⨯ V ⟶ V)) _ _ p.1 +
    cup q (pull _ (sch.map (prod.snd : Gq q ⨯ V ⟶ V)) _ _ p.2) (pull _ (sch.map (prod.fst : Gq q ⨯ V ⟶ Gq q)) _ _ (kappa q))

/- English proof (translation)
Establish `h1 : ∀ {n i : ℤ} (a : Ht q (sch.obj V) n i), pull _ (sch.map (prod.map (𝟙 (Gq q)) g)) _ _ (pull _ (sch.map (prod.snd : Gq q ⨯ V ⟶ V)) _ _ a) = pull _ (sch.map (prod.snd : Gq q ⨯ V' ⟶ V')) _ _ (pull _ (sch.map g) _ _ a)`. Introduce `n i a`. Rewrite using `[← pull_comp, ← pull_comp, ← sch.map_comp, ← sch.map_comp, prod.map_snd]`. Establish `h2 : pull _ (sch.map (prod.map (𝟙 (Gq q)) g)) _ _ (pull _ (sch.map (prod.fst : Gq q ⨯ V ⟶ Gq q)) _ _ (kappa q)) = pull _ (sch.map (prod.fst : Gq q ⨯ V' ⟶ Gq q)) _ _ (kappa q)`. Rewrite using `[← pull_comp, ← sch.map_comp, prod.map_fst, Category.comp_id]`.

Simplify using `only [Phi]`. Rewrite using `[map_add, pull_cup', h1, h1, h2]`.
-/
private theorem Phi_nat (q : ℕ) (m j : ℤ) {V' V : Scheme.{0}} (g : V' ⟶ V)
    (p : Ht q (sch.obj V) (m + 1) (j + 1) × Ht q (sch.obj V) m j) :
    pull _ (sch.map (prod.map (𝟙 (Gq q)) g)) _ _ (Phi q m j V p) =
      Phi q m j V' (pull _ (sch.map g) _ _ p.1, pull _ (sch.map g) _ _ p.2) := by
  have h1 : ∀ {n i : ℤ} (a : Ht q (sch.obj V) n i),
      pull _ (sch.map (prod.map (𝟙 (Gq q)) g)) _ _ (pull _ (sch.map (prod.snd : Gq q ⨯ V ⟶ V)) _ _ a) =
        pull _ (sch.map (prod.snd : Gq q ⨯ V' ⟶ V')) _ _ (pull _ (sch.map g) _ _ a) := by
    intro n i a
    rw [← pull_comp, ← pull_comp, ← sch.map_comp, ← sch.map_comp, prod.map_snd]
  have h2 : pull _ (sch.map (prod.map (𝟙 (Gq q)) g)) _ _ (pull _ (sch.map (prod.fst : Gq q ⨯ V ⟶ Gq q)) _ _ (kappa q)) =
      pull _ (sch.map (prod.fst : Gq q ⨯ V' ⟶ Gq q)) _ _ (kappa q) := by
    rw [← pull_comp, ← sch.map_comp, prod.map_fst, Category.comp_id]
  simp only [Phi]
  rw [map_add, pull_cup', h1, h1, h2]

/- English proof (translation)
Rewrite using `[← pull_comp, ← sch.map_comp, prod.map_map, Category.comp_id]`.
-/
private theorem pull_prod (q : ℕ) {n i : ℤ} {V'' V' V : Scheme.{0}} (h : V'' ⟶ V') (g : V' ⟶ V)
    (y : Ht q (sch.obj (Gq q ⨯ V)) n i) :
    pull _ (sch.map (prod.map (𝟙 (Gq q)) h)) _ _ (pull _ (sch.map (prod.map (𝟙 (Gq q)) g)) _ _ y) =
      pull _ (sch.map (prod.map (𝟙 (Gq q)) (h ≫ g))) _ _ y := by
  rw [← pull_comp, ← sch.map_comp, prod.map_map, Category.comp_id]

/- English proof (translation)
The claim follows from `GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary (ZMod q) (twF q i) (GlobalTheory.T.tateTwistRingFunctor_preservesFilteredColimits q i)`.
-/
private theorem tw_finitary (q : ℕ) (i : ℤ) : Finitary (tw q i) :=
  GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary (ZMod q) (twF q i) (GlobalTheory.T.tateTwistRingFunctor_preservesFilteredColimits q i)

/- English proof (translation)
Use `haveI : IsAffine (⊤_ Scheme.{0}) := IsAffine.of_isIso (terminalIsoIsTerminal specZIsTerminal).hom`. Use `haveI : IsAffine (pullback (terminal.from W) (terminal.from X)) := isAffine_of_isAffineHom (pullback.snd (terminal.from W) (terminal.from X))`. Conclude with `IsAffine.of_isIso (prodIsoPullback W X).hom`.
-/
private theorem affine_prod (W X : Scheme.{0}) [IsAffine W] [IsAffine X] : IsAffine (W ⨯ X) := by
  haveI : IsAffine (⊤_ Scheme.{0}) := IsAffine.of_isIso (terminalIsoIsTerminal specZIsTerminal).hom
  haveI : IsAffine (pullback (terminal.from W) (terminal.from X)) :=
    isAffine_of_isAffineHom (pullback.snd (terminal.from W) (terminal.from X))
  exact IsAffine.of_isIso (prodIsoPullback W X).hom

/- English proof (translation)
Take `⟨O, _, s, g, hs, v, hv⟩` from `GlobalTheory.T.exists_strictlyHenselianEtaleStalk_over_point T (Over.mk (𝟙 T)) (by dsimp; infer_instance) u`. Take `⟨I, _, _, G, π, ⟨hl⟩, hG⟩` from `GlobalTheory.T.exists_cofiltered_limit_affine_etale_of_isStalk' T O s hs`. Use `haveI : IsConnected I := IsCofiltered.isConnected I`. Establish `hgs : g.left = s` using `by simpa using Over.w g`. Establish `hc : IsLimit ((Over.forget T).mapCone (Cone.mk _ π))` using `isLimitOfPreserves (Over.forget T) hl`.

Use `haveI := prod_preservesConnectedLimits (J := I) (Gq q)`. Establish `hc2` using `isLimitOfPreserves (prod.functor.obj (Gq q)) hc`. Establish `hπ : ∀ {i k : I} (f : k ⟶ i), π.app k ≫ G.map f = π.app i` using `fun f => by`. Simplify using `using (π.naturality f).symm`. Use `⟨O, inferInstance, s, I, inferInstance, inferInstance, G ⋙ Over.forget T, fun i => (G.obj i).hom, fun i => (π.app i).left, hs.1, ?_, ⟨v, ?_⟩, fun i => hG i, fun i => Over.w (π.app i), fun f => Over.w (G.map f), fun f => by` and prove the remaining obligations.

Use `congrArg (fun a => a.left) (hπ f)` as an intermediate fact. Simplify using `using this, ?_, ?_⟩`. Use `(hq.map s.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom` as an intermediate fact. Simplify using `using this`. Rewrite using `[← hgs]`.

Conclude with `hv`. Introduce `n i'`. Conclude with `GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit (ZMod q) (tw q i') (tw_finitary q i') I (G ⋙ Over.forget T) _ hc (fun i => (hG i).1) n`. Introduce `n i' k y hy`. Establish `hA : ∀ i, IsAffine (((G ⋙ Over.forget T) ⋙ prod.functor.obj (Gq q)).obj i)` using `fun i => by haveI := (hG i).1`.

Conclude with `affine_prod (Gq q) (G.obj i).left`. Conclude with `(GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit (ZMod q) (tw q i') (tw_finitary q i') I ((G ⋙ Over.forget T) ⋙ prod.functor.obj (Gq q)) _ hc2 hA n).2 k y hy`.
-/
private theorem exists_nbhd (q : ℕ) [NeZero q] (T : Scheme.{0}) (hq : IsUnit (q : Γ(T, ⊤))) (u : T) :
    ∃ (O : Type) (_ : CommRing O) (s : Spec (CommRingCat.of O) ⟶ T) (I : Type) (_ : SmallCategory I) (_ : IsCofiltered I)
      (D : I ⥤ Scheme.{0}) (t : ∀ i, D.obj i ⟶ T) (e : ∀ i, Spec (CommRingCat.of O) ⟶ D.obj i),
      SH O ∧ IsUnit (q : O) ∧ (∃ v, s v = u) ∧ (∀ i, IsAffine (D.obj i) ∧ Etale (t i)) ∧ (∀ i, e i ≫ t i = s) ∧
      (∀ {i k : I} (f : k ⟶ i), D.map f ≫ t i = t k) ∧ (∀ {i k : I} (f : k ⟶ i), e k ≫ D.map f = e i) ∧
      (∀ n i' : ℤ, (∀ x : Ht q (sch.obj (Spec (CommRingCat.of O))) n i', ∃ (k : I) (y : Ht q (sch.obj (D.obj k)) n i'),
          pull _ (sch.map (e k)) _ _ y = x) ∧
        ∀ (k : I) (y : Ht q (sch.obj (D.obj k)) n i'), pull _ (sch.map (e k)) _ _ y = 0 →
          ∃ (k' : I) (f : k' ⟶ k), pull _ (sch.map (D.map f)) _ _ y = 0) ∧
      (∀ n i' : ℤ, ∀ (k : I) (y : Ht q (sch.obj (Gq q ⨯ D.obj k)) n i'),
        pull _ (sch.map (prod.map (𝟙 (Gq q)) (e k))) _ _ y = 0 →
          ∃ (k' : I) (f : k' ⟶ k), pull _ (sch.map (prod.map (𝟙 (Gq q)) (D.map f))) _ _ y = 0) := by
  obtain ⟨O, _, s, g, hs, v, hv⟩ := GlobalTheory.T.exists_strictlyHenselianEtaleStalk_over_point T (Over.mk (𝟙 T)) (by dsimp; infer_instance) u
  obtain ⟨I, _, _, G, π, ⟨hl⟩, hG⟩ := GlobalTheory.T.exists_cofiltered_limit_affine_etale_of_isStalk' T O s hs
  haveI : IsConnected I := IsCofiltered.isConnected I
  have hgs : g.left = s := by simpa using Over.w g
  have hc : IsLimit ((Over.forget T).mapCone (Cone.mk _ π)) := isLimitOfPreserves (Over.forget T) hl
  haveI := prod_preservesConnectedLimits (J := I) (Gq q)
  have hc2 := isLimitOfPreserves (prod.functor.obj (Gq q)) hc
  have hπ : ∀ {i k : I} (f : k ⟶ i), π.app k ≫ G.map f = π.app i := fun f => by
    simpa using (π.naturality f).symm
  refine ⟨O, inferInstance, s, I, inferInstance, inferInstance, G ⋙ Over.forget T, fun i => (G.obj i).hom,
    fun i => (π.app i).left, hs.1, ?_, ⟨v, ?_⟩, fun i => hG i, fun i => Over.w (π.app i), fun f => Over.w (G.map f),
    fun f => by
      have := congrArg (fun a => a.left) (hπ f)
      simpa using this, ?_, ?_⟩
  · have := (hq.map s.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom
    simpa using this
  · rw [← hgs]; exact hv
  · intro n i'
    exact GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit (ZMod q) (tw q i') (tw_finitary q i') I (G ⋙ Over.forget T) _ hc (fun i => (hG i).1) n
  · intro n i' k y hy
    have hA : ∀ i, IsAffine (((G ⋙ Over.forget T) ⋙ prod.functor.obj (Gq q)).obj i) := fun i => by
      haveI := (hG i).1
      exact affine_prod (Gq q) (G.obj i).left
    exact (GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit (ZMod q) (tw q i') (tw_finitary q i') I ((G ⋙ Over.forget T) ⋙ prod.functor.obj (Gq q)) _ hc2
      hA n).2 k y hy

/- English proof (translation)
Use `(GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover T _ ?_).2 ?_` and prove the remaining obligations. Introduce and unpack `V W g k ⟨p, hp⟩`. Use `⟨(pull _ (sch.map k) _ _ p.1, pull _ (sch.map k) _ _ p.2), ?_⟩` and prove the remaining obligations. Rewrite using `[← Phi_nat, hp, pull_prod]`. Introduce `u`.

Take `⟨O, _, s, I, _, _, D, t, e, hO, hqO, ⟨v, hv⟩, hD, het, hDt, hDe, c1, c2⟩` from `exists_nbhd q T hq u`. Take `⟨p, hp⟩` from `(UpperTheory.bijective_etaleCohomology_multiplicativeGroup_prod q O hO hqO m j).2 (pull _ (sch.map (prod.map (𝟙 (Gq q)) s)) _ _ y)`. Express the relevant statement in the definitionally equal form `Phi q m j _ p = _ at hp`. Take `⟨i1, a, ha⟩` from `(c1 (m + 1) (j + 1)).1 p.1`. Take `⟨i2, b, hb⟩` from `(c1 m j).1 p.2`.

Set `k` to `IsCofiltered.min i1 i2`. Set `f1 : k ⟶ i1` to `IsCofiltered.minToLeft i1 i2`. Set `f2 : k ⟶ i2` to `IsCofiltered.minToRight i1 i2`. Set `a1` to `pull _ (sch.map (D.map f1)) _ _ a`. Set `b1` to `pull _ (sch.map (D.map f2)) _ _ b`.

Establish `ea : pull _ (sch.map (e k)) _ _ a1 = p.1`. Rewrite using `[← ha, ← pull_comp, ← sch.map_comp, hDe]`. Establish `eb : pull _ (sch.map (e k)) _ _ b1 = p.2`. Rewrite using `[← hb, ← pull_comp, ← sch.map_comp, hDe]`. Establish `hd : pull _ (sch.map (prod.map (𝟙 (Gq q)) (e k))) _ _ (Phi q m j (D.obj k) (a1, b1) - pull _ (sch.map (prod.map (𝟙 (Gq q)) (t k))) _ _ y) = 0`.

Rewrite using `[map_sub, Phi_nat, pull_prod, het, sub_eq_zero]`. Simplify using `only [ea, eb]`. Conclude with `hp`. Take `⟨k', f', hf'⟩` from `c2 _ _ k _ hd`. Use `⟨D.obj k', t k', (hD k').1, (hD k').2, ⟨e k' v, ?_⟩, (pull _ (sch.map (D.map f')) _ _ a1, pull _ (sch.map (D.map f')) _ _ b1), ?_⟩` and prove the remaining obligations.

Rewrite using `[← Scheme.Hom.comp_apply, het, hv]`. Rewrite `hf'` using `[map_sub, sub_eq_zero, Phi_nat, pull_prod, hDt]`. Conclude with `hf'`.
-/
private theorem surj_part (q : ℕ) [NeZero q] (T : Scheme.{0}) (hq : IsUnit (q : Γ(T, ⊤))) (m j : ℤ)
    (y : Ht q (sch.obj (Gq q ⨯ T)) (m + 1) (j + 1)) :
    Loc T fun V g => ∃ p, Phi q m j V p = pull _ (sch.map (prod.map (𝟙 (Gq q)) g)) _ _ y := by
  refine (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover T _ ?_).2 ?_
  · rintro V W g k ⟨p, hp⟩
    refine ⟨(pull _ (sch.map k) _ _ p.1, pull _ (sch.map k) _ _ p.2), ?_⟩
    rw [← Phi_nat, hp, pull_prod]
  intro u
  obtain ⟨O, _, s, I, _, _, D, t, e, hO, hqO, ⟨v, hv⟩, hD, het, hDt, hDe, c1, c2⟩ := exists_nbhd q T hq u
  obtain ⟨p, hp⟩ := (UpperTheory.bijective_etaleCohomology_multiplicativeGroup_prod q O hO hqO m j).2 (pull _ (sch.map (prod.map (𝟙 (Gq q)) s)) _ _ y)
  change Phi q m j _ p = _ at hp
  obtain ⟨i1, a, ha⟩ := (c1 (m + 1) (j + 1)).1 p.1
  obtain ⟨i2, b, hb⟩ := (c1 m j).1 p.2
  let k := IsCofiltered.min i1 i2
  let f1 : k ⟶ i1 := IsCofiltered.minToLeft i1 i2
  let f2 : k ⟶ i2 := IsCofiltered.minToRight i1 i2
  let a1 := pull _ (sch.map (D.map f1)) _ _ a
  let b1 := pull _ (sch.map (D.map f2)) _ _ b
  have ea : pull _ (sch.map (e k)) _ _ a1 = p.1 := by
    rw [← ha, ← pull_comp, ← sch.map_comp, hDe]
  have eb : pull _ (sch.map (e k)) _ _ b1 = p.2 := by
    rw [← hb, ← pull_comp, ← sch.map_comp, hDe]
  have hd : pull _ (sch.map (prod.map (𝟙 (Gq q)) (e k))) _ _
      (Phi q m j (D.obj k) (a1, b1) - pull _ (sch.map (prod.map (𝟙 (Gq q)) (t k))) _ _ y) = 0 := by
    rw [map_sub, Phi_nat, pull_prod, het, sub_eq_zero]
    simp only [ea, eb]
    exact hp
  obtain ⟨k', f', hf'⟩ := c2 _ _ k _ hd
  refine ⟨D.obj k', t k', (hD k').1, (hD k').2, ⟨e k' v, ?_⟩,
    (pull _ (sch.map (D.map f')) _ _ a1, pull _ (sch.map (D.map f')) _ _ b1), ?_⟩
  · rw [← Scheme.Hom.comp_apply, het, hv]
  · rw [map_sub, sub_eq_zero, Phi_nat, pull_prod, hDt] at hf'
    exact hf'

/- English proof (translation)
Use `(GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover T _ ?_).2 ?_` and prove the remaining obligations. Introduce and unpack `V W g k ⟨h1, h2⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[sch.map_comp, pull_comp, h1, map_zero]`. Rewrite using `[sch.map_comp, pull_comp, h2, map_zero]`.

Introduce `u`. Take `⟨O, _, s, I, _, _, D, t, e, hO, hqO, ⟨v, hv⟩, hD, het, hDt, hDe, c1, c2⟩` from `exists_nbhd q T hq u`. Establish `h0 : Phi q m j _ (pull _ (sch.map s) _ _ p.1, pull _ (sch.map s) _ _ p.2) = 0`. Rewrite using `[← Phi_nat, hp, map_zero]`. Establish `hz : Phi q m j (Spec (CommRingCat.of O)) 0 = 0`.

Simplify using `[Phi]`. Establish `hinj : (pull _ (sch.map s) _ _ p.1, pull _ (sch.map s) _ _ p.2) = (0 : Ht q (sp O) (m + 1) (j + 1) × Ht q (sp O) m j)` using `(UpperTheory.bijective_etaleCohomology_multiplicativeGroup_prod q O hO hqO m j).1 (h0.trans hz.symm)`. Establish `s1 : pull _ (sch.map s) _ _ p.1 = 0` using `congrArg Prod.fst hinj`. Establish `s2 : pull _ (sch.map s) _ _ p.2 = 0` using `congrArg Prod.snd hinj`. Take `⟨i0⟩ : Nonempty I` from `IsCofiltered.nonempty`.

Establish `d1 : pull _ (sch.map (e i0)) _ _ (pull _ (sch.map (t i0)) _ _ p.1) = 0`. Rewrite using `[← pull_comp, ← sch.map_comp, het, s1]`. Establish `d2 : pull _ (sch.map (e i0)) _ _ (pull _ (sch.map (t i0)) _ _ p.2) = 0`. Rewrite using `[← pull_comp, ← sch.map_comp, het, s2]`. Take `⟨k1, f1, h1⟩` from `(c1 _ _).2 i0 _ d1`.

Take `⟨k2, f2, h2⟩` from `(c1 _ _).2 i0 _ d2`. Set `k` to `IsCofiltered.min k1 k2`. Set `g1 : k ⟶ k1` to `IsCofiltered.minToLeft k1 k2`. Set `g2 : k ⟶ k2` to `IsCofiltered.minToRight k1 k2`. Use `⟨D.obj k, t k, (hD k).1, (hD k).2, ⟨e k v, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Scheme.Hom.comp_apply, het, hv]`. Establish `e1 : t k = D.map g1 ≫ D.map f1 ≫ t i0` using `by rw [hDt, hDt]`. Rewrite using `[e1, sch.map_comp, sch.map_comp, pull_comp, pull_comp, h1, map_zero]`. Establish `e2 : t k = D.map g2 ≫ D.map f2 ≫ t i0` using `by rw [hDt, hDt]`. Rewrite using `[e2, sch.map_comp, sch.map_comp, pull_comp, pull_comp, h2, map_zero]`.
-/
private theorem inj_part (q : ℕ) [NeZero q] (T : Scheme.{0}) (hq : IsUnit (q : Γ(T, ⊤))) (m j : ℤ)
    (p : Ht q (sch.obj T) (m + 1) (j + 1) × Ht q (sch.obj T) m j) (hp : Phi q m j T p = 0) :
    Loc T fun V g => pull _ (sch.map g) _ _ p.1 = 0 ∧ pull _ (sch.map g) _ _ p.2 = 0 := by
  refine (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover T _ ?_).2 ?_
  · rintro V W g k ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [sch.map_comp, pull_comp, h1, map_zero]
    · rw [sch.map_comp, pull_comp, h2, map_zero]
  intro u
  obtain ⟨O, _, s, I, _, _, D, t, e, hO, hqO, ⟨v, hv⟩, hD, het, hDt, hDe, c1, c2⟩ := exists_nbhd q T hq u
  have h0 : Phi q m j _ (pull _ (sch.map s) _ _ p.1, pull _ (sch.map s) _ _ p.2) = 0 := by
    rw [← Phi_nat, hp, map_zero]
  have hz : Phi q m j (Spec (CommRingCat.of O)) 0 = 0 := by
    simp [Phi]
  have hinj : (pull _ (sch.map s) _ _ p.1, pull _ (sch.map s) _ _ p.2) =
      (0 : Ht q (sp O) (m + 1) (j + 1) × Ht q (sp O) m j) :=
    (UpperTheory.bijective_etaleCohomology_multiplicativeGroup_prod q O hO hqO m j).1 (h0.trans hz.symm)
  have s1 : pull _ (sch.map s) _ _ p.1 = 0 := congrArg Prod.fst hinj
  have s2 : pull _ (sch.map s) _ _ p.2 = 0 := congrArg Prod.snd hinj
  obtain ⟨i0⟩ : Nonempty I := IsCofiltered.nonempty
  have d1 : pull _ (sch.map (e i0)) _ _ (pull _ (sch.map (t i0)) _ _ p.1) = 0 := by
    rw [← pull_comp, ← sch.map_comp, het, s1]
  have d2 : pull _ (sch.map (e i0)) _ _ (pull _ (sch.map (t i0)) _ _ p.2) = 0 := by
    rw [← pull_comp, ← sch.map_comp, het, s2]
  obtain ⟨k1, f1, h1⟩ := (c1 _ _).2 i0 _ d1
  obtain ⟨k2, f2, h2⟩ := (c1 _ _).2 i0 _ d2
  let k := IsCofiltered.min k1 k2
  let g1 : k ⟶ k1 := IsCofiltered.minToLeft k1 k2
  let g2 : k ⟶ k2 := IsCofiltered.minToRight k1 k2
  refine ⟨D.obj k, t k, (hD k).1, (hD k).2, ⟨e k v, ?_⟩, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, het, hv]
  · have e1 : t k = D.map g1 ≫ D.map f1 ≫ t i0 := by rw [hDt, hDt]
    rw [e1, sch.map_comp, sch.map_comp, pull_comp, pull_comp, h1, map_zero]
  · have e2 : t k = D.map g2 ≫ D.map f2 ≫ t i0 := by rw [hDt, hDt]
    rw [e2, sch.map_comp, sch.map_comp, pull_comp, pull_comp, h2, map_zero]

end UpperTheory.KunRed

/- English proof (translation)
Introduce `q _ T hq m j` and use `⟨fun y => UpperTheory.KunRed.surj_part q T hq m j y, fun p hp => UpperTheory.KunRed.inj_part q T hq m j p hp⟩`.
-/
theorem UpperTheory.locally_surjective_multiplicativeGroupKunnethMap :
    ∀ (q : ℕ) [NeZero q] (T : Scheme.{0}), IsUnit (q : Γ(T, ⊤)) → ∀ m j : ℤ,
        (∀ y : Ht q (sch.obj (Gq q ⨯ T)) (m + 1) (j + 1), Loc T fun V g =>
          ∃ p : Ht q (sch.obj V) (m + 1) (j + 1) × Ht q (sch.obj V) m j,
            pull _ (sch.map (prod.snd : Gq q ⨯ V ⟶ V)) _ _ p.1 +
              cup q (pull _ (sch.map (prod.snd : Gq q ⨯ V ⟶ V)) _ _ p.2) (pull _ (sch.map (prod.fst : Gq q ⨯ V ⟶ Gq q)) _ _ (kappa q)) =
            pull _ (sch.map (prod.map (𝟙 (Gq q)) g)) _ _ y) ∧
        (∀ p : Ht q (sch.obj T) (m + 1) (j + 1) × Ht q (sch.obj T) m j,
          pull _ (sch.map (prod.snd : Gq q ⨯ T ⟶ T)) _ _ p.1 +
              cup q (pull _ (sch.map (prod.snd : Gq q ⨯ T ⟶ T)) _ _ p.2) (pull _ (sch.map (prod.fst : Gq q ⨯ T ⟶ Gq q)) _ _ (kappa q)) = 0 →
          Loc T fun V g => pull _ (sch.map g) _ _ p.1 = 0 ∧ pull _ (sch.map g) _ _ p.2 = 0) :=
  fun q _ T hq m j => ⟨fun y => UpperTheory.KunRed.surj_part q T hq m j y, fun p hp => UpperTheory.KunRed.inj_part q T hq m j p hp⟩
