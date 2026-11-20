import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsDualLatticesStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ActQIsLocallyConstant
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GrowthGaloisInvariantsModPrimePowerLattice

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

/- English proof (translation)
Use `set I : Ideal O := Ideal.span {a}`. Set `F` to `M ⧸ Submodule.torsion O M`. Set `b` to `Module.finBasis O F`. Establish `e : finrank O F = finrank O M` using `finrank_quotient_eq_of_le_torsion le_rfl`. Set `ψL : M →ₗ[O] (Fin (finrank O F) → O)` to `b.equivFun.toLinearMap ∘ₗ (Submodule.torsion O M).mkQ`.

Set `ψ : M → (Fin (finrank O F) → O ⧸ I)` to `fun m i => Ideal.Quotient.mk I (ψL m i)`. Establish `hψ : ∀ x y, (∃ w, x - y = a • w) → ψ x = ψ y`. Introduce and unpack `x y ⟨w, hw⟩`. Use function extensionality and compare the values at `i`. Use `Ideal.Quotient.eq.mpr ?_` and prove the remaining obligations.

Establish `h1 : ψL x i - ψL y i = a * ψL w i`. Rewrite using `[← Pi.sub_apply, ← map_sub, hw, map_smul]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `Ideal.mem_span_singleton'.mpr ⟨ψL w i, mul_comm _ _⟩`.

Establish `hsurj : Function.Surjective (fun z => ψ (p z))`. Introduce `t`. Use `choose c hc using fun i => Ideal.Quotient.mk_surjective (I := I) (t i)`. Take `⟨m, hm⟩` from `(Submodule.torsion O M).mkQ_surjective (b.equivFun.symm c)`. Take `⟨z, rfl⟩` from `hp m`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [ψ, ψL, LinearMap.coe_comp, Function.comp_apply, hm, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hc]`. Set `g : Set.range f → (Fin (finrank O F) → O ⧸ I)` to `fun n => ψ (p (Classical.choose n.2))`. Establish `hg : Function.Surjective g`.

Introduce `t`. Take `⟨z, hz⟩` from `hsurj t`. Use `⟨⟨f z, z, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hz' : f (Classical.choose (⟨z, rfl⟩ : ∃ y, f y = f z)) = f z` using `Classical.choose_spec (⟨z, rfl⟩ : ∃ y, f y = f z)`. Simplify using `only [g]`.

Rewrite using `[hψ _ _ (hf _ _ hz')]`. Conclude with `hz`. Establish `h1` using `Nat.card_le_card_of_surjective g hg`. Establish `h2 : Nat.card (Set.range f) ≤ Nat.card N` using `Nat.card_le_card_of_injective Subtype.val Subtype.val_injective`. Rewrite `h1` using `[Nat.card_fun, Nat.card_fin, e]`.

Conclude with `h1.trans h2`.
-/
theorem card_pow_le {O M Z N : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] [Finite N] (a : O) (p : Z → M) (hp : Function.Surjective p)
    (f : Z → N) (hf : ∀ x y, f x = f y → ∃ w, p x - p y = a • w) :
    Nat.card (O ⧸ Ideal.span {a}) ^ finrank O M ≤ Nat.card N := by
  classical
  set I : Ideal O := Ideal.span {a}
  let F := M ⧸ Submodule.torsion O M
  let b := Module.finBasis O F
  have e : finrank O F = finrank O M := finrank_quotient_eq_of_le_torsion le_rfl
  let ψL : M →ₗ[O] (Fin (finrank O F) → O) := b.equivFun.toLinearMap ∘ₗ (Submodule.torsion O M).mkQ
  let ψ : M → (Fin (finrank O F) → O ⧸ I) := fun m i => Ideal.Quotient.mk I (ψL m i)
  have hψ : ∀ x y, (∃ w, x - y = a • w) → ψ x = ψ y := by
    rintro x y ⟨w, hw⟩
    funext i
    refine Ideal.Quotient.eq.mpr ?_
    have h1 : ψL x i - ψL y i = a * ψL w i := by
      rw [← Pi.sub_apply, ← map_sub, hw, map_smul]
      rfl
    rw [h1]
    exact Ideal.mem_span_singleton'.mpr ⟨ψL w i, mul_comm _ _⟩
  have hsurj : Function.Surjective (fun z => ψ (p z)) := by
    intro t
    choose c hc using fun i => Ideal.Quotient.mk_surjective (I := I) (t i)
    obtain ⟨m, hm⟩ := (Submodule.torsion O M).mkQ_surjective (b.equivFun.symm c)
    obtain ⟨z, rfl⟩ := hp m
    refine ⟨z, ?_⟩
    funext i
    simp only [ψ, ψL, LinearMap.coe_comp, Function.comp_apply, hm, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, hc]
  let g : Set.range f → (Fin (finrank O F) → O ⧸ I) := fun n => ψ (p (Classical.choose n.2))
  have hg : Function.Surjective g := by
    intro t
    obtain ⟨z, hz⟩ := hsurj t
    refine ⟨⟨f z, z, rfl⟩, ?_⟩
    have hz' : f (Classical.choose (⟨z, rfl⟩ : ∃ y, f y = f z)) = f z := Classical.choose_spec (⟨z, rfl⟩ : ∃ y, f y = f z)
    simp only [g]
    rw [hψ _ _ (hf _ _ hz')]
    exact hz
  have h1 := Nat.card_le_card_of_surjective g hg
  have h2 : Nat.card (Set.range f) ≤ Nat.card N := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  rw [Nat.card_fun, Nat.card_fin, e] at h1
  exact h1.trans h2

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
  (A : GRep G Qp LL O) (L : Lattice (O := O) A.ρ)

open GlobalTheory.CompanionTheory.GrowthOfInvariants in

/- English proof (translation)
Take `⟨⟨hcont, hcoc⟩, _⟩` from `c.2`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `g0`. Establish `hW' : (fun x => ϖ ^ r • x) '' (L.T : Set A.V) ∈ nhds ((c : _ → A.V) g0 + -(c : _ → A.V) g0)`.

Rewrite using `[add_neg_cancel]`. Conclude with `hW`. Use `filter_upwards [(hcont.tendsto g0).add_const (-(c : _ → A.V) g0) hW'] with g hg`. Take `⟨x, hx, hxe⟩` from `hg`. Use `(Submodule.Quotient.eq _).mpr ?_` and prove the remaining obligations.

Establish `: (evT L g c - evT L g0 c : ↥L.T) = ϖ ^ r • (⟨x, hx⟩ : ↥L.T)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_sub, SetLike.val_smul]`. Establish `hxe' : ϖ ^ r • x = (c : _ → A.V) g + -(c : _ → A.V) g0` using `hxe`. Rewrite using `[hxe', sub_eq_add_neg]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top`. Introduce `g h show Submodule.Quotient.mk (evT L (g * h) c) = Submodule.Quotient.mk (evT L g c) + actQ L _ hI g (Submodule.Quotient.mk (evT L h c))`. Rewrite using `[actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_add]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hcoc g h`.
-/
theorem redT_mem {ϖ : O} {r : ℕ} (hW : (fun x => ϖ ^ r • x) '' (L.T : Set A.V) ∈ nhds (0 : A.V))
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (c : ↥(latticeCocycles L)) :
    redT L _ c ∈ quotientCocycles L _ hI := by
  obtain ⟨⟨hcont, hcoc⟩, _⟩ := c.2
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have hW' : (fun x => ϖ ^ r • x) '' (L.T : Set A.V) ∈ nhds ((c : _ → A.V) g0 + -(c : _ → A.V) g0) := by
      rw [add_neg_cancel]
      exact hW
    filter_upwards [(hcont.tendsto g0).add_const (-(c : _ → A.V) g0) hW'] with g hg
    obtain ⟨x, hx, hxe⟩ := hg
    refine (Submodule.Quotient.eq _).mpr ?_
    have : (evT L g c - evT L g0 c : ↥L.T) = ϖ ^ r • (⟨x, hx⟩ : ↥L.T) := by
      apply Subtype.ext
      simp only [Submodule.coe_sub, SetLike.val_smul]
      have hxe' : ϖ ^ r • x = (c : _ → A.V) g + -(c : _ → A.V) g0 := hxe
      rw [hxe', sub_eq_add_neg]
      rfl
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  · intro g h
    show Submodule.Quotient.mk (evT L (g * h) c) = Submodule.Quotient.mk (evT L g c) + actQ L _ hI g (Submodule.Quotient.mk (evT L h c))
    rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact hcoc g h

open GlobalTheory.CompanionTheory.GrowthOfInvariants in

/- English proof (translation)
Take `⟨t, ht⟩` from `hc`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ t`. Establish `hd : ∀ g, ∃ y : ↥L.T, a • y = evT L g c - (actT L g x - x)`. Introduce `g`. Establish `h1` using `congrFun ht g`.

Simplify using `only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at h1`. Express the relevant statement in the definitionally equal form `actQ L _ hI g (Submodule.Quotient.mk x) - Submodule.Quotient.mk x = Submodule.Quotient.mk (evT L g c) at h1`. Rewrite `h1` using `[actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, eq_comm, Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨y, _, hy⟩` from `h1`. Conclude with `⟨y, hy⟩`.

Use `choose y hy using hd`. Take `⟨⟨hcont, hcoc⟩, _⟩` from `c.2`. Use `set α : LL := algebraMap O LL a with hαdef`. Establish `hα : α ≠ 0` using `fun h => ha ((IsFractionRing.injective O LL) (h.trans (map_zero _).symm))`. Establish `hyV : ∀ g, a • ((y g : ↥L.T) : A.V) = (c : G → A.V) g - (A.ρ g (x : A.V) - (x : A.V))`.

Introduce `g`. Use `congrArg Subtype.val (hy g)` as an intermediate fact. Conclude with `this`. Establish `hyL : ∀ g, α • ((y g : ↥L.T) : A.V) = (c : G → A.V) g - (A.ρ g (x : A.V) - (x : A.V))`. Introduce `g`.

Rewrite using `[hαdef, algebraMap_smul]`. Conclude with `hyV g`. Set `e : G → A.V` to `fun g => (y g : A.V)`. Establish `he_form : e = fun g => α⁻¹ • ((c : G → A.V) g + (-1 : LL) • A.ρ g (x : A.V) + (x : A.V))`. Use function extensionality and compare the values at `g`.

Establish `h2 : (c : G → A.V) g + (-1 : LL) • A.ρ g (x : A.V) + (x : A.V) = α • e g`. Rewrite using `[hyL g, neg_one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[h2, inv_smul_smul₀ hα]`. Establish `he : e ∈ latticeCocycles L`.

Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[he_form]`. Conclude with `((hcont.add ((A.cont (x : A.V)).const_smul (-1 : LL))).add continuous_const).const_smul α⁻¹`. Introduce `g h`. Apply `smul_right_injective A.V hα` to reduce the goal to its premises.

Simplify using `only [smul_add, e, hyL, ← map_smul, hcoc, map_mul, Module.End.mul_apply, map_sub]`. Normalize the expressions using the abelian group laws. Introduce `g _`. Conclude with `(y g).2`. Use `⟨Submodule.Quotient.mk ⟨e, he⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]`. Use `⟨x, x.2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `A.ρ g (x : A.V) - (x : A.V) = (c : G → A.V) g - a • e g`. Rewrite using `[show a • e g = a • ((y g : ↥L.T) : A.V) from rfl, hyV g, sub_sub_cancel]`.
-/
theorem exists_div_class [IsDomain O] [IsFractionRing O LL] {a : O} (ha : a ≠ 0)
    (hI : StableSub L (Ideal.span {a} • ⊤ : Submodule O ↥L.T)) (c : ↥(latticeCocycles L))
    (hc : redT L (Ideal.span {a} • ⊤ : Submodule O ↥L.T) c ∈ BQ L _ hI) :
    ∃ w : LatticeCohomology L, (Submodule.Quotient.mk c : LatticeCohomology L) = a • w := by
  obtain ⟨t, ht⟩ := hc
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  have hd : ∀ g, ∃ y : ↥L.T, a • y = evT L g c - (actT L g x - x) := by
    intro g
    have h1 := congrFun ht g
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at h1
    change actQ L _ hI g (Submodule.Quotient.mk x) - Submodule.Quotient.mk x = Submodule.Quotient.mk (evT L g c) at h1
    rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, eq_comm, Submodule.Quotient.eq,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨y, _, hy⟩ := h1
    exact ⟨y, hy⟩
  choose y hy using hd
  obtain ⟨⟨hcont, hcoc⟩, _⟩ := c.2
  set α : LL := algebraMap O LL a with hαdef
  have hα : α ≠ 0 := fun h => ha ((IsFractionRing.injective O LL) (h.trans (map_zero _).symm))
  have hyV : ∀ g, a • ((y g : ↥L.T) : A.V) = (c : G → A.V) g - (A.ρ g (x : A.V) - (x : A.V)) := by
    intro g
    have := congrArg Subtype.val (hy g)
    exact this
  have hyL : ∀ g, α • ((y g : ↥L.T) : A.V) = (c : G → A.V) g - (A.ρ g (x : A.V) - (x : A.V)) := by
    intro g
    rw [hαdef, algebraMap_smul]
    exact hyV g
  let e : G → A.V := fun g => (y g : A.V)
  have he_form : e = fun g => α⁻¹ • ((c : G → A.V) g + (-1 : LL) • A.ρ g (x : A.V) + (x : A.V)) := by
    funext g
    have h2 : (c : G → A.V) g + (-1 : LL) • A.ρ g (x : A.V) + (x : A.V) = α • e g := by
      rw [hyL g, neg_one_smul]
      abel
    rw [h2, inv_smul_smul₀ hα]
  have he : e ∈ latticeCocycles L := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [he_form]
      exact ((hcont.add ((A.cont (x : A.V)).const_smul (-1 : LL))).add continuous_const).const_smul α⁻¹
    · intro g h
      apply smul_right_injective A.V hα
      simp only [smul_add, e, hyL, ← map_smul, hcoc, map_mul, Module.End.mul_apply, map_sub]
      abel
    · intro g _
      exact (y g).2
  refine ⟨Submodule.Quotient.mk ⟨e, he⟩, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
  refine ⟨x, x.2, ?_⟩
  funext g
  change A.ρ g (x : A.V) - (x : A.V) = (c : G → A.V) g - a • e g
  rw [show a • e g = a • ((y g : ↥L.T) : A.V) from rfl, hyV g, sub_sub_cancel]

end Gen

/- English proof (translation)
Introduce `D l _ K hfin hZ LL _ _ _ O _ _ hO A LA ϖ hϖ r hI`. Take `⟨⟨hD, hV, hF⟩, -⟩` from `id hO`. Take `⟨-, hB, -⟩` from `GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hO A LA ϖ hϖ`. Establish `hW : (fun x => ϖ ^ r • x) '' (LA.T : Set A.V) ∈ nhds (0 : A.V)` using `hB.mem_of_mem trivial`. Use `hfin LL O hO A LA` as an intermediate fact.

Use `hZ LL O hO A LA ϖ hϖ r hI` as an intermediate fact. Establish `: Finite (QuotientCohomology LA _ hI)` using `Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)`. Rewrite using `[pow_mul, ← GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_pow ϖ hϖ.ne_zero r]`. Use `card_pow_le (ϖ ^ r) (fun c : ↥(latticeCocycles LA) => (Submodule.Quotient.mk c : LatticeCohomology LA)) (Submodule.Quotient.mk_surjective _) (fun c => (Submodule.Quotient.mk ⟨redT LA _ c, redT_mem A LA hW hI c⟩ : QuotientCohomology LA _ hI)) ?_` and prove the remaining obligations. Introduce `x y h`.

Rewrite using `[← Submodule.Quotient.mk_sub]`. Use `exists_div_class A LA (pow_ne_zero r hϖ.ne_zero) hI _ ?_` and prove the remaining obligations. Rewrite using `[map_sub]`. Establish `h'` using `(Submodule.Quotient.eq _).1 h`. Conclude with `h'`.
-/
theorem card_lower_bound : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), TateFiniteness ((D.loc l).PD K) → FinZQ ((D.loc l).PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ ϖ : O, Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank O (LatticeCohomology LA)) ≤ Nat.card (QuotientCohomology LA _ hI) := by
  intro D l _ K hfin hZ LL _ _ _ O _ _ hO A LA ϖ hϖ r hI
  obtain ⟨⟨hD, hV, hF⟩, -⟩ := id hO
  obtain ⟨-, hB, -⟩ := GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hO A LA ϖ hϖ
  have hW : (fun x => ϖ ^ r • x) '' (LA.T : Set A.V) ∈ nhds (0 : A.V) := hB.mem_of_mem trivial
  have := hfin LL O hO A LA
  have := hZ LL O hO A LA ϖ hϖ r hI
  have : Finite (QuotientCohomology LA _ hI) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  rw [pow_mul, ← GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_pow ϖ hϖ.ne_zero r]
  refine card_pow_le (ϖ ^ r) (fun c : ↥(latticeCocycles LA) => (Submodule.Quotient.mk c : LatticeCohomology LA))
    (Submodule.Quotient.mk_surjective _)
    (fun c => (Submodule.Quotient.mk ⟨redT LA _ c, redT_mem A LA hW hI c⟩ : QuotientCohomology LA _ hI)) ?_
  intro x y h
  rw [← Submodule.Quotient.mk_sub]
  refine exists_div_class A LA (pow_ne_zero r hϖ.ne_zero) hI _ ?_
  rw [map_sub]
  have h' := (Submodule.Quotient.eq _).1 h
  exact h'

end PositivityTheory.LocalTateOrthogonality.Bk
