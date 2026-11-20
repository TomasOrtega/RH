import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Consider the cases of `nonempty_fintype α`. Simplify using `only [finsum_eq_sum_of_fintype, LinearMap.sum_apply]`.
-/
private theorem finsum_end_apply {α M : Type} [AddCommGroup M] [Module ℂ M] [Finite α]
    (f : α → Module.End ℂ M) (x : M) : (∑ᶠ a, f a) x = ∑ᶠ a, f a x := by
  cases nonempty_fintype α
  simp only [finsum_eq_sum_of_fintype, LinearMap.sum_apply]

/- English proof (translation)
Introduce `H G V _ _ _ _ j p J U hpj hU hJ d hd`. Establish `hin : ∀ h : H, (h : H ⧸ J) ∈ MulAction.orbit J (d : H ⧸ J) → ((j h : G) : G ⧸ U) ∈ MulAction.orbit U ((j d : G) : G ⧸ U)`. Introduce and unpack `h ⟨a, ha⟩`. Establish `h1 : (((a : H) * d : H) : H ⧸ J) = (h : H ⧸ J)` using `ha`. Establish `h2 : ((a : H) * d)⁻¹ * h ∈ J` using `QuotientGroup.eq.1 h1`.

Establish `h3 : (j ((a : H) * d))⁻¹ * j h ∈ U`. Use `hJ _ h2` as an intermediate fact. Simplify `this` using `[map_mul]`. Use `⟨⟨j a, hJ _ a.2⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((j a * j d : G) : G ⧸ U) = ((j h : G) : G ⧸ U)`.

Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Simplify `h3` using `[map_mul]`. Establish `hsurj : ∀ y ∈ MulAction.orbit U ((j d : G) : G ⧸ U), ∃ h : H, (h : H ⧸ J) ∈ MulAction.orbit J (d : H ⧸ J) ∧ ((j h : G) : G ⧸ U) = y`. Introduce and unpack `y ⟨u, rfl⟩`. Take `⟨hpu, hc⟩` from `hU u u.2`.

Use `set c : G := (u : G) * (j (p u))⁻¹ with hcdef`. Establish `hcU : c ∈ U` using `U.mul_mem u.2 (U.inv_mem (hJ _ hpu))`. Use `⟨p u * d, ⟨⟨p u, hpu⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((j (p u * d) : G) : G ⧸ U) = (((u : G) * j d : G) : G ⧸ U)`. Establish `hfac : (u : G) * j d = j (p u * d) * c`.

Establish `h1 : (u : G) = c * j (p u)` using `by simp [hcdef]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hfac]`. Conclude with `(QuotientGroup.mk_mul_of_mem _ hcU).symm`. Establish `hfin : AlgebraTools.FinOrb U U (j d)`.

Use `(hd.image fun q : H ⧸ J => ((j q.out : G) : G ⧸ U)).subset ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨h, hh, rfl⟩` from `hsurj y hy`. Use `⟨(h : H ⧸ J), hh, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((j (h : H ⧸ J).out : G) : G ⧸ U) = ((j h : G) : G ⧸ U)`.

Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Establish `h1 : ((h : H ⧸ J).out)⁻¹ * h ∈ J` using `QuotientGroup.eq.1 (by simp)`. Use `hJ _ h1` as an intermediate fact. Simplify `this` using `[map_mul]`. Use `⟨hfin, fun φ hφ => ?_⟩` and prove the remaining obligations.

Use `haveI : Finite (MulAction.orbit J (d : H ⧸ J)) := Set.Finite.to_subtype hd`. Use `haveI : Finite (MulAction.orbit U ((j d : G) : G ⧸ U)) := Set.Finite.to_subtype hfin`. Set `e : MulAction.orbit J (d : H ⧸ J) → MulAction.orbit U ((j d : G) : G ⧸ U)` to `fun q => ⟨((j (q : H ⧸ J).out : G) : G ⧸ U), hin _ (by simpa using q.2)⟩`. Establish `he : Function.Bijective e`. Prove the components needed by the constructor for the conclusion.

Introduce `q q' hqq`. Establish `h1 : ((j (q : H ⧸ J).out : G) : G ⧸ U) = ((j (q' : H ⧸ J).out : G) : G ⧸ U)` using `congrArg Subtype.val hqq`. Establish `h2 : (j (q : H ⧸ J).out)⁻¹ * j (q' : H ⧸ J).out ∈ U` using `QuotientGroup.eq.1 h1`. Establish `h3` using `(hU _ h2).1`. Establish `h4 : ((q : H ⧸ J).out)⁻¹ * (q' : H ⧸ J).out ∈ J`.

Simplify `h3` using `[map_mul, map_inv, hpj]`. Establish `h5 : (((q : H ⧸ J).out : H) : H ⧸ J) = (((q' : H ⧸ J).out : H) : H ⧸ J)` using `QuotientGroup.eq.2 h4`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using h5`. Introduce and unpack `⟨y, hy⟩`.

Take `⟨h, hh, rfl⟩` from `hsurj y hy`. Use `⟨⟨(h : H ⧸ J), hh⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((j (h : H ⧸ J).out : G) : G ⧸ U) = ((j h : G) : G ⧸ U)`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Establish `h1 : ((h : H ⧸ J).out)⁻¹ * h ∈ J` using `QuotientGroup.eq.1 (by simp)`.

Use `hJ _ h1` as an intermediate fact. Simplify `this` using `[map_mul]`. Unfold `dcF dc`. Rewrite using `[finsum_end_apply, finsum_end_apply, ← finsum_comp e he]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `g`. Establish `h1 : (((e q : G ⧸ U)).out)⁻¹ * j (q : H ⧸ J).out ∈ U` using `QuotientGroup.eq.1 (by simp [e])`. Establish `h2` using `hφ _ h1 (g * ((e q : G ⧸ U)).out)`. Express the relevant statement in the definitionally equal form `φ (g * ((e q : G ⧸ U)).out) = φ (g * j (q : H ⧸ J).out)`. Rewrite using `[← h2]`.

Use `congr 1`. Use `group`.
-/
theorem UpperTheory.V.Z.Sym.So.dcLocal :
    UpperTheory.V.Z.Sym.So.DcLocal := by
  intro H G V _ _ _ _ j p J U hpj hU hJ d hd

  have hin : ∀ h : H, (h : H ⧸ J) ∈ MulAction.orbit J (d : H ⧸ J) →
      ((j h : G) : G ⧸ U) ∈ MulAction.orbit U ((j d : G) : G ⧸ U) := by
    rintro h ⟨a, ha⟩
    have h1 : (((a : H) * d : H) : H ⧸ J) = (h : H ⧸ J) := ha
    have h2 : ((a : H) * d)⁻¹ * h ∈ J := QuotientGroup.eq.1 h1
    have h3 : (j ((a : H) * d))⁻¹ * j h ∈ U := by
      have := hJ _ h2
      simpa [map_mul] using this
    refine ⟨⟨j a, hJ _ a.2⟩, ?_⟩
    change ((j a * j d : G) : G ⧸ U) = ((j h : G) : G ⧸ U)
    refine QuotientGroup.eq.2 ?_
    simpa [map_mul] using h3

  have hsurj : ∀ y ∈ MulAction.orbit U ((j d : G) : G ⧸ U),
      ∃ h : H, (h : H ⧸ J) ∈ MulAction.orbit J (d : H ⧸ J) ∧ ((j h : G) : G ⧸ U) = y := by
    rintro y ⟨u, rfl⟩
    obtain ⟨hpu, hc⟩ := hU u u.2
    set c : G := (u : G) * (j (p u))⁻¹ with hcdef
    have hcU : c ∈ U := U.mul_mem u.2 (U.inv_mem (hJ _ hpu))
    refine ⟨p u * d, ⟨⟨p u, hpu⟩, rfl⟩, ?_⟩
    change ((j (p u * d) : G) : G ⧸ U) = (((u : G) * j d : G) : G ⧸ U)
    have hfac : (u : G) * j d = j (p u * d) * c := by
      have h1 : (u : G) = c * j (p u) := by simp [hcdef]
      calc (u : G) * j d = c * j (p u * d) := by rw [map_mul, ← mul_assoc, ← h1]
        _ = j (p u * d) * c := hc _
    rw [hfac]
    exact (QuotientGroup.mk_mul_of_mem _ hcU).symm
  have hfin : AlgebraTools.FinOrb U U (j d) := by
    refine (hd.image fun q : H ⧸ J => ((j q.out : G) : G ⧸ U)).subset ?_
    intro y hy
    obtain ⟨h, hh, rfl⟩ := hsurj y hy
    refine ⟨(h : H ⧸ J), hh, ?_⟩
    change ((j (h : H ⧸ J).out : G) : G ⧸ U) = ((j h : G) : G ⧸ U)
    refine QuotientGroup.eq.2 ?_
    have h1 : ((h : H ⧸ J).out)⁻¹ * h ∈ J := QuotientGroup.eq.1 (by simp)
    have := hJ _ h1
    simpa [map_mul] using this
  refine ⟨hfin, fun φ hφ => ?_⟩
  haveI : Finite (MulAction.orbit J (d : H ⧸ J)) := Set.Finite.to_subtype hd
  haveI : Finite (MulAction.orbit U ((j d : G) : G ⧸ U)) := Set.Finite.to_subtype hfin

  let e : MulAction.orbit J (d : H ⧸ J) → MulAction.orbit U ((j d : G) : G ⧸ U) := fun q =>
    ⟨((j (q : H ⧸ J).out : G) : G ⧸ U), hin _ (by simpa using q.2)⟩
  have he : Function.Bijective e := by
    constructor
    · intro q q' hqq
      have h1 : ((j (q : H ⧸ J).out : G) : G ⧸ U) = ((j (q' : H ⧸ J).out : G) : G ⧸ U) :=
        congrArg Subtype.val hqq
      have h2 : (j (q : H ⧸ J).out)⁻¹ * j (q' : H ⧸ J).out ∈ U := QuotientGroup.eq.1 h1
      have h3 := (hU _ h2).1
      have h4 : ((q : H ⧸ J).out)⁻¹ * (q' : H ⧸ J).out ∈ J := by
        simpa [map_mul, map_inv, hpj] using h3
      have h5 : (((q : H ⧸ J).out : H) : H ⧸ J) = (((q' : H ⧸ J).out : H) : H ⧸ J) :=
        QuotientGroup.eq.2 h4
      apply Subtype.ext
      simpa using h5
    · rintro ⟨y, hy⟩
      obtain ⟨h, hh, rfl⟩ := hsurj y hy
      refine ⟨⟨(h : H ⧸ J), hh⟩, Subtype.ext ?_⟩
      change ((j (h : H ⧸ J).out : G) : G ⧸ U) = ((j h : G) : G ⧸ U)
      refine QuotientGroup.eq.2 ?_
      have h1 : ((h : H ⧸ J).out)⁻¹ * h ∈ J := QuotientGroup.eq.1 (by simp)
      have := hJ _ h1
      simpa [map_mul] using this
  unfold dcF dc
  rw [finsum_end_apply, finsum_end_apply, ← finsum_comp e he]
  refine finsum_congr fun q => ?_
  funext g
  have h1 : (((e q : G ⧸ U)).out)⁻¹ * j (q : H ⧸ J).out ∈ U := QuotientGroup.eq.1 (by simp [e])
  have h2 := hφ _ h1 (g * ((e q : G ⧸ U)).out)
  change φ (g * ((e q : G ⧸ U)).out) = φ (g * j (q : H ⧸ J).out)
  rw [← h2]
  congr 1
  group

end
