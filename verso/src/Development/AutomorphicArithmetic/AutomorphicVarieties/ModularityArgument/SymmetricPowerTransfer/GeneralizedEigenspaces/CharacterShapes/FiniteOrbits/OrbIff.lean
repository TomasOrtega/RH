import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul U g`. Conclude with `⟨h, h.2, hh⟩`.
-/
private theorem out_mul {G : Type} [Group G] (U : Subgroup G) (g : G) :
    ∃ i ∈ U, ((g : G ⧸ U)).out = g * i := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U g
  exact ⟨h, h.2, hh⟩

/- English proof (translation)
Establish `key : ∀ u : U, u • (a : G ⧸ U) = (((u : G) * a : G) : G ⧸ U)` using `fun u => rfl`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Take `⟨i, hi, h⟩` from `out_mul U ((u : G) * a)`. Use `⟨u, u.2, i, hi, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[key, h]`. Introduce and unpack `⟨u, hu, u', hu', h⟩`. Use `⟨⟨u, hu⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[key, ← QuotientGroup.out_eq' p, h]`. Use `QuotientGroup.eq.mpr ?_` and prove the remaining obligations. Rewrite using `[inv_mul_cancel_left]`. Conclude with `hu'`.
-/
private theorem orb_iff {G : Type} [Group G] (U : Subgroup G) (a : G) (p : G ⧸ U) :
    p ∈ MulAction.orbit U (a : G ⧸ U) ↔ p.out ∈ DC U a := by
  have key : ∀ u : U, u • (a : G ⧸ U) = (((u : G) * a : G) : G ⧸ U) := fun u => rfl
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨i, hi, h⟩ := out_mul U ((u : G) * a)
    refine ⟨u, u.2, i, hi, ?_⟩
    dsimp only
    rw [key, h]
  · rintro ⟨u, hu, u', hu', h⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    dsimp only
    rw [key, ← QuotientGroup.out_eq' p, h]
    refine QuotientGroup.eq.mpr ?_
    rw [inv_mul_cancel_left]
    exact hu'

/- English proof (translation)
Simplify using `only [dcF, dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, Finset.sum_apply]`. Both sides reduce to the same expression.
-/
private theorem dcF_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (U : Subgroup G) (a : G)
    [Fintype (MulAction.orbit U (a : G ⧸ U))] (φ : G → V) (g : G) :
    dcF U a φ g = ∑ q : MulAction.orbit U (a : G ⧸ U), φ (g * (q : G ⧸ U).out) := by
  simp only [dcF, dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, Finset.sum_apply]
  rfl

/- English proof (translation)
Take `⟨u, hu, u', hu', rfl⟩` from `hx`. Conclude with `⟨u, hu, u' * i, U.mul_mem hu' hi, mul_assoc _ _ _⟩`.
-/
private theorem mul_mem_dc_of_mem_subgroup {G : Type} [Group G] (U : Subgroup G) (c x i : G) (hx : x ∈ DC U c) (hi : i ∈ U) :
    x * i ∈ DC U c := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hx
  exact ⟨u, hu, u' * i, U.mul_mem hu' hi, mul_assoc _ _ _⟩

/- English proof (translation)
Take `⟨i, hi, h⟩` from `out_mul U x`. Rewrite using `[h]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Simplify using `using mul_mem_dc_of_mem_subgroup U c _ i⁻¹ hx (U.inv_mem hi)`.

Introduce `hx`. Conclude with `mul_mem_dc_of_mem_subgroup U c x i hx hi`.
-/
private theorem quotient_out_mem_dc_iff {G : Type} [Group G] (U : Subgroup G) (c x : G) :
    ((x : G ⧸ U)).out ∈ DC U c ↔ x ∈ DC U c := by
  obtain ⟨i, hi, h⟩ := out_mul U x
  rw [h]
  constructor
  · intro hx
    simpa using mul_mem_dc_of_mem_subgroup U c _ i⁻¹ hx (U.inv_mem hi)
  · intro hx
    exact mul_mem_dc_of_mem_subgroup U c x i hx hi

/- English proof (translation)
Introduce `G V _ _ _ U a b ha hb hab huf φ hφ`. Use `haveI : Fintype (MulAction.orbit U (a : G ⧸ U)) := Set.Finite.fintype ha`. Use `haveI : Fintype (MulAction.orbit U (b : G ⧸ U)) := Set.Finite.fintype hb`. Use `haveI : Fintype (MulAction.orbit U ((a * b : G) : G ⧸ U)) := Set.Finite.fintype hab`. Use function extensionality and compare the values at `g`.

Rewrite using `[dcF_sum U a _ g, dcF_sum U (a * b) φ g]`. Simplify using `only [dcF_sum U b φ]`. Rewrite using `[← Fintype.sum_prod_type']`. Establish `hmem : ∀ x : MulAction.orbit U (a : G ⧸ U) × MulAction.orbit U (b : G ⧸ U), (((x.1 : G ⧸ U).out * (x.2 : G ⧸ U).out : G) : G ⧸ U) ∈ MulAction.orbit U ((a * b : G) : G ⧸ U)`. Introduce `x`.

Use `(orb_iff U (a * b) _).mpr ((quotient_out_mem_dc_iff U _ _).mpr ((huf _).2 _ ((orb_iff U a _).mp x.1.2) ?_))` and prove the remaining obligations. Rewrite using `[inv_mul_cancel_left]`. Conclude with `(orb_iff U b _).mp x.2.2`. Use `Fintype.sum_bijective (fun x => ⟨_, hmem x⟩) ⟨?_, ?_⟩ _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨q, r⟩ ⟨q', r'⟩ hx`.

Establish `hx' : (((q : G ⧸ U).out * (r : G ⧸ U).out : G) : G ⧸ U) = (((q' : G ⧸ U).out * (r' : G ⧸ U).out : G) : G ⧸ U)` using `congrArg Subtype.val hx`. Take `⟨i, hi, hs⟩` from `out_mul U ((q : G ⧸ U).out * (r : G ⧸ U).out)`. Take `⟨i', hi', hs'⟩` from `out_mul U ((q' : G ⧸ U).out * (r' : G ⧸ U).out)`. Establish `hsab : (q : G ⧸ U).out * (r : G ⧸ U).out * i ∈ DC U (a * b)`. Use `(orb_iff U (a * b) _).mp (hmem (q, r))` as an intermediate fact.

Rewrite `this` using `[hs]`. Then use the resulting hypothesis. Rewrite `hs` using `[hx']`. Establish `he : (q : G ⧸ U).out * (r : G ⧸ U).out * i = (q' : G ⧸ U).out * (r' : G ⧸ U).out * i'` using `hs.symm.trans hs'`. Take `⟨y, -, huniq⟩` from `(huf _).1 hsab`. Establish `h1 : (q : G ⧸ U) = y` using `huniq _ ⟨(orb_iff U a _).mp q.2, by`.

Simplify using `only [mul_assoc, inv_mul_cancel_left]`. Conclude with `mul_mem_dc_of_mem_subgroup U b _ i ((orb_iff U b _).mp r.2) hi⟩`. Establish `h2 : (q' : G ⧸ U) = y` using `huniq _ ⟨(orb_iff U a _).mp q'.2, by`. Rewrite using `[he]`. Simplify using `only [mul_assoc, inv_mul_cancel_left]`.

Conclude with `mul_mem_dc_of_mem_subgroup U b _ i' ((orb_iff U b _).mp r'.2) hi'⟩`. Establish `hq : q = q'` using `Subtype.ext (h1.trans h2.symm)`. Substitute `hq` using the available equality. Establish `hr : (r : G ⧸ U).out * i = (r' : G ⧸ U).out * i'`. Rewrite `he` using `[mul_assoc, mul_assoc]`.

Conclude with `mul_left_cancel he`. Establish `hr' : (r : G ⧸ U) = r'`. Rewrite using `[← QuotientGroup.out_eq' (r : G ⧸ U), ← QuotientGroup.out_eq' (r' : G ⧸ U), ← QuotientGroup.mk_mul_of_mem (r : G ⧸ U).out hi, hr, QuotientGroup.mk_mul_of_mem _ hi']`. Conclude with `Prod.ext rfl (Subtype.ext hr')`. Introduce and unpack `⟨s, hs⟩`.

Establish `hsd : (s : G ⧸ U).out ∈ DC U (a * b)` using `(orb_iff U (a * b) s).mp hs`. Take `⟨y, ⟨hy1, hy2⟩, -⟩` from `(huf _).1 hsd`. Use `⟨(⟨y, (orb_iff U a y).mpr hy1⟩, ⟨((y.out⁻¹ * s.out : G) : G ⧸ U), (orb_iff U b _).mpr ((quotient_out_mem_dc_iff U _ _).mpr hy2)⟩), ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Take `⟨i, hi, h⟩` from `out_mul U (y.out⁻¹ * s.out)`.

Simplify using `only`. Rewrite using `[h, ← mul_assoc, mul_inv_cancel_left, QuotientGroup.mk_mul_of_mem _ hi, QuotientGroup.out_eq']`. Introduce and unpack `⟨q, r⟩`. Take `⟨i, hi, h⟩` from `out_mul U ((q : G ⧸ U).out * (r : G ⧸ U).out)`. Simplify using `only`.

Rewrite using `[h, ← mul_assoc, ← mul_assoc, hφ i hi]`.
-/
theorem UpperTheory.V.Z.Sym.So.uFMul :
    UpperTheory.V.Z.Sym.So.UFMul := by
  intro G V _ _ _ U a b ha hb hab huf φ hφ
  haveI : Fintype (MulAction.orbit U (a : G ⧸ U)) := Set.Finite.fintype ha
  haveI : Fintype (MulAction.orbit U (b : G ⧸ U)) := Set.Finite.fintype hb
  haveI : Fintype (MulAction.orbit U ((a * b : G) : G ⧸ U)) := Set.Finite.fintype hab
  funext g
  rw [dcF_sum U a _ g, dcF_sum U (a * b) φ g]
  simp only [dcF_sum U b φ]
  rw [← Fintype.sum_prod_type']
  have hmem : ∀ x : MulAction.orbit U (a : G ⧸ U) × MulAction.orbit U (b : G ⧸ U),
      (((x.1 : G ⧸ U).out * (x.2 : G ⧸ U).out : G) : G ⧸ U) ∈ MulAction.orbit U ((a * b : G) : G ⧸ U) := by
    intro x
    refine (orb_iff U (a * b) _).mpr ((quotient_out_mem_dc_iff U _ _).mpr ((huf _).2 _ ((orb_iff U a _).mp x.1.2) ?_))
    rw [inv_mul_cancel_left]
    exact (orb_iff U b _).mp x.2.2
  refine Fintype.sum_bijective (fun x => ⟨_, hmem x⟩) ⟨?_, ?_⟩ _ _ ?_
  · rintro ⟨q, r⟩ ⟨q', r'⟩ hx
    have hx' : (((q : G ⧸ U).out * (r : G ⧸ U).out : G) : G ⧸ U) =
        (((q' : G ⧸ U).out * (r' : G ⧸ U).out : G) : G ⧸ U) := congrArg Subtype.val hx
    obtain ⟨i, hi, hs⟩ := out_mul U ((q : G ⧸ U).out * (r : G ⧸ U).out)
    obtain ⟨i', hi', hs'⟩ := out_mul U ((q' : G ⧸ U).out * (r' : G ⧸ U).out)
    have hsab : (q : G ⧸ U).out * (r : G ⧸ U).out * i ∈ DC U (a * b) := by
      have := (orb_iff U (a * b) _).mp (hmem (q, r))
      rwa [hs] at this
    rw [hx'] at hs
    have he : (q : G ⧸ U).out * (r : G ⧸ U).out * i = (q' : G ⧸ U).out * (r' : G ⧸ U).out * i' :=
      hs.symm.trans hs'
    obtain ⟨y, -, huniq⟩ := (huf _).1 hsab
    have h1 : (q : G ⧸ U) = y := huniq _ ⟨(orb_iff U a _).mp q.2, by
      simp only [mul_assoc, inv_mul_cancel_left]
      exact mul_mem_dc_of_mem_subgroup U b _ i ((orb_iff U b _).mp r.2) hi⟩
    have h2 : (q' : G ⧸ U) = y := huniq _ ⟨(orb_iff U a _).mp q'.2, by
      rw [he]
      simp only [mul_assoc, inv_mul_cancel_left]
      exact mul_mem_dc_of_mem_subgroup U b _ i' ((orb_iff U b _).mp r'.2) hi'⟩
    have hq : q = q' := Subtype.ext (h1.trans h2.symm)
    subst hq
    have hr : (r : G ⧸ U).out * i = (r' : G ⧸ U).out * i' := by
      rw [mul_assoc, mul_assoc] at he
      exact mul_left_cancel he
    have hr' : (r : G ⧸ U) = r' := by
      rw [← QuotientGroup.out_eq' (r : G ⧸ U), ← QuotientGroup.out_eq' (r' : G ⧸ U),
        ← QuotientGroup.mk_mul_of_mem (r : G ⧸ U).out hi, hr, QuotientGroup.mk_mul_of_mem _ hi']
    exact Prod.ext rfl (Subtype.ext hr')
  · rintro ⟨s, hs⟩
    have hsd : (s : G ⧸ U).out ∈ DC U (a * b) := (orb_iff U (a * b) s).mp hs
    obtain ⟨y, ⟨hy1, hy2⟩, -⟩ := (huf _).1 hsd
    refine ⟨(⟨y, (orb_iff U a y).mpr hy1⟩,
      ⟨((y.out⁻¹ * s.out : G) : G ⧸ U), (orb_iff U b _).mpr ((quotient_out_mem_dc_iff U _ _).mpr hy2)⟩), ?_⟩
    apply Subtype.ext
    obtain ⟨i, hi, h⟩ := out_mul U (y.out⁻¹ * s.out)
    dsimp only
    rw [h, ← mul_assoc, mul_inv_cancel_left, QuotientGroup.mk_mul_of_mem _ hi, QuotientGroup.out_eq']
  · rintro ⟨q, r⟩
    obtain ⟨i, hi, h⟩ := out_mul U ((q : G ⧸ U).out * (r : G ⧸ U).out)
    dsimp only
    rw [h, ← mul_assoc, ← mul_assoc, hφ i hi]

end
