import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ExtGraded
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.XrMonomial
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.AmbScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallExt

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply]`. Conclude with `SetLike.prod_pow_mem_graded W.gr W.wt W.zA n fun s _ => W.z_mem s`.
-/
private theorem mono_mem {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
    (n : W.σ →₀ ℕ) : (n.prod fun s k => W.zA s ^ k) ∈ W.gr (Finsupp.weight W.wt n) := by
  rw [Finsupp.weight_apply]
  exact SetLike.prod_pow_mem_graded W.gr W.wt W.zA n fun s _ => W.z_mem s

/- English proof (translation)
Take `⟨s, hs⟩` from `Finsupp.support_nonempty_iff.2 hn`. Use `show W.A.val _ ∈ I`. Rewrite using `[Finsupp.prod, map_prod]`. Use `Ideal.prod_mem _ hs ?_` and prove the remaining obligations. Rewrite using `[map_pow]`.

Conclude with `Ideal.pow_mem_of_mem _ (h s) _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hs))`.
-/
private theorem mono_max {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
    (I : Ideal R) (h : ∀ s, W.z s ∈ I) (n : W.σ →₀ ℕ) (hn : n ≠ 0) :
    ((n.prod fun s k => W.zA s ^ k : W.A) : R) ∈ I := by
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.2 hn
  show W.A.val _ ∈ I
  rw [Finsupp.prod, map_prod]
  refine Ideal.prod_mem _ hs ?_
  rw [map_pow]
  exact Ideal.pow_mem_of_mem _ (h s) _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hs))

/- English proof (translation)
Use `choose g hg using h`. Conclude with `⟨{ toFun := g map_one' := hF (by rw [hg, map_one, map_one]) map_mul' := fun a b => hF (by rw [map_mul, hg, hg, hg, map_mul]) map_zero' := hF (by rw [hg, map_zero, map_zero]) map_add' := fun a b => hF (by rw [map_add, hg, hg, hg, map_add]) }, hg⟩`.
-/
private theorem factor {B C K : Type} [CommRing B] [CommRing C] [CommRing K] (F : C →+* K) (hF : Function.Injective F)
    (ξ : B →+* K) (h : ∀ x, ξ x ∈ F.range) : ∃ η : B →+* C, ∀ x, F (η x) = ξ x := by
  choose g hg using h
  exact ⟨{ toFun := g
           map_one' := hF (by rw [hg, map_one, map_one])
           map_mul' := fun a b => hF (by rw [map_mul, hg, hg, hg, map_mul])
           map_zero' := hF (by rw [hg, map_zero, map_zero])
           map_add' := fun a b => hF (by rw [map_add, hg, hg, hg, map_add]) }, hg⟩

/- English proof (translation)
Introduce `l _ 𝔞 A _ _ _ f hf s O _ _ _ _ X _ _ _ _ R _ _ _ W hz y hy hcl`. Use `letI : Algebra O 𝔞.K := ((𝔞.toK.comp y).comp (algebraMap O (W.gr 0))).toAlgebra`. Set `y' : W.gr 0 →ₐ[O] 𝔞.K` to `{ 𝔞.toK.comp y with commutes' := fun _ => rfl }`. Take `⟨ξ, hξ⟩` from `Po.extA O X R W hz 𝔞.K y'`. Establish `hξ' : ∀ b : W.gr 0, ξ b = (y b : 𝔞.K)` using `hξ`.

Take `⟨t, ht⟩` from `Po.ambScale 𝔞 A f hf W.σ X W.wt (fun i => ξ (W.zA i)) fun n hn hw => by`. Establish `h0 : (n.prod fun s k => W.zA s ^ k) ∈ W.gr 0` using `hw ▸ mono_mem W n`. Establish `h1` using `(𝔞.V.valuation_lt_one_iff _).1 (hy ⟨_, h0⟩ (mono_max W _ hz n hn))`. Rewrite `h1` using `[← hξ']`. Simplify `h1` using `only [Finsupp.prod, map_prod ξ, map_pow ξ]`.

Set `ζ : W.A →ₐ[O] 𝔞.K` to `act W.gr t ξ`. Establish `hζ0 : ∀ b : W.gr 0, ζ b = (y b : 𝔞.K)` using `fun b => by`. Rewrite using `[act_of_mem W.gr t ξ b.2, ofAdd_zero, map_one, Units.val_one, one_mul, hξ']`. Establish `hζz : ∀ i, 𝔞.V.valuation (ζ (W.zA i)) < 1` using `fun i => by`. Rewrite using `[act_of_mem W.gr t ξ (j := W.wt i) (W.z_mem i)]`.

Conclude with `ht i`. Take `⟨A', _, _, _, f', g, hf', -, hr⟩` from `smallExt 𝔞 A f hf (s ∪ Finset.univ.image fun i => ζ (W.zA i))`. Establish `hmem : ∀ x : 𝔞.V, x ∈ f'.range → (x : 𝔞.K) ∈ (𝔞.toK.comp f').range`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨a, rfl⟩`.

Establish `h0 : ∀ b : W.gr 0, ζ b ∈ (𝔞.toK.comp f').range` using `fun b => by`. Rewrite using `[hζ0]`. Use `hmem _ (hr _ (Subfield.closure_mono (Set.union_subset_union_right _ ?_) (hcl b)))` and prove the remaining obligations. Conclude with `Finset.coe_subset.2 Finset.subset_union_left`. Establish `hall : ∀ x, (ζ : W.A →+* 𝔞.K) x ∈ (𝔞.toK.comp f').range` using `fun x => by`.

Establish `hx : x ∈ Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA)`. Rewrite using `[gr_gen O R X W]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Take `hx | ⟨i, rfl⟩` from `hx`. Conclude with `h0 ⟨x, hx⟩`. Use `hmem ⟨_, 𝔞.V.mem_of_valuation_le_one _ (hζz i).le⟩ (hr _ (Subfield.subset_closure (.inr ?_)))` and prove the remaining obligations. Conclude with `Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))`. Consider the case `algebraMap a => exact h0 (algebraMap O (W.gr 0) a)`.

Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_mem ha hb`. Take `⟨η, hη⟩` from `factor (𝔞.toK.comp f') (Subtype.val_injective.comp hf'.inj) _ hall`.

Establish `hη' : ∀ x, (f' (η x) : 𝔞.K) = ζ x` using `hη`. Establish `hmax : ∀ x, 𝔞.V.valuation (ζ x) < 1 → η x ∈ maximalIdeal A'` using `fun x hx hu => by`. Rewrite `hx` using `[← hη', ← 𝔞.V.valuation_lt_one_iff]`. Conclude with `hx (hu.map f')`. Use `letI : Algebra O A' := (η.comp (algebraMap O W.A)).toAlgebra`.

Use `haveI := hf'.complete`. Take `⟨Ξ, hΞ, hΞm⟩` from `Po.extR O X R W hz A' { η with commutes' := fun _ => rfl } (fun i => hmax _ (hζz i)) fun b hb hm => hmax b (by`. Rewrite using `[hζ0 ⟨b, hb⟩]`. Conclude with `(𝔞.V.valuation_lt_one_iff _).1 (hy ⟨b, hb⟩ hm))`. Use `⟨A', inferInstance, inferInstance, inferInstance, f', Ξ, hf', hΞm, fun b => Subtype.ext ?_⟩` and prove the remaining obligations.

Establish `e : Ξ ((b : W.A) : R) = η b` using `AlgHom.congr_fun hΞ b`. Use `show (f' (Ξ _) : 𝔞.K) = _`. Rewrite using `[e, hη', hζ0]`.
-/
theorem UpperTheory.V.Ws.Po.ptA :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (f : A →+* 𝔞.V), 𝔞.IsDvr f → ∀ (s : Finset 𝔞.K)
      (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) →
      ∀ y : W.gr 0 →+* 𝔞.V, (∀ b : W.gr 0, ((b : W.A) : R) ∈ maximalIdeal R → y b ∈ maximalIdeal 𝔞.V) →
      (∀ b, (y b : 𝔞.K) ∈ Subfield.closure (Set.range (𝔞.toK.comp f) ∪ s)) →
      ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (f' : A' →+* 𝔞.V) (Ξ : R →+* A'),
        𝔞.IsDvr f' ∧ (∀ x ∈ maximalIdeal R, Ξ x ∈ maximalIdeal A') ∧ ∀ b : W.gr 0, f' (Ξ ((b : W.A) : R)) = y b := by
  intro l _ 𝔞 A _ _ _ f hf s O _ _ _ _ X _ _ _ _ R _ _ _ W hz y hy hcl
  classical
  letI : Algebra O 𝔞.K := ((𝔞.toK.comp y).comp (algebraMap O (W.gr 0))).toAlgebra
  let y' : W.gr 0 →ₐ[O] 𝔞.K := { 𝔞.toK.comp y with commutes' := fun _ => rfl }
  obtain ⟨ξ, hξ⟩ := Po.extA O X R W hz 𝔞.K y'
  have hξ' : ∀ b : W.gr 0, ξ b = (y b : 𝔞.K) := hξ
  obtain ⟨t, ht⟩ := Po.ambScale 𝔞 A f hf W.σ X W.wt (fun i => ξ (W.zA i)) fun n hn hw => by
    have h0 : (n.prod fun s k => W.zA s ^ k) ∈ W.gr 0 := hw ▸ mono_mem W n
    have h1 := (𝔞.V.valuation_lt_one_iff _).1 (hy ⟨_, h0⟩ (mono_max W _ hz n hn))
    rw [← hξ'] at h1
    simpa only [Finsupp.prod, map_prod ξ, map_pow ξ] using h1
  let ζ : W.A →ₐ[O] 𝔞.K := act W.gr t ξ
  have hζ0 : ∀ b : W.gr 0, ζ b = (y b : 𝔞.K) := fun b => by
    rw [act_of_mem W.gr t ξ b.2, ofAdd_zero, map_one, Units.val_one, one_mul, hξ']
  have hζz : ∀ i, 𝔞.V.valuation (ζ (W.zA i)) < 1 := fun i => by
    rw [act_of_mem W.gr t ξ (j := W.wt i) (W.z_mem i)]
    exact ht i
  obtain ⟨A', _, _, _, f', g, hf', -, hr⟩ := smallExt 𝔞 A f hf (s ∪ Finset.univ.image fun i => ζ (W.zA i))
  have hmem : ∀ x : 𝔞.V, x ∈ f'.range → (x : 𝔞.K) ∈ (𝔞.toK.comp f').range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  have h0 : ∀ b : W.gr 0, ζ b ∈ (𝔞.toK.comp f').range := fun b => by
    rw [hζ0]
    refine hmem _ (hr _ (Subfield.closure_mono (Set.union_subset_union_right _ ?_) (hcl b)))
    exact Finset.coe_subset.2 Finset.subset_union_left
  have hall : ∀ x, (ζ : W.A →+* 𝔞.K) x ∈ (𝔞.toK.comp f').range := fun x => by
    have hx : x ∈ Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) := by
      rw [gr_gen O R X W]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain hx | ⟨i, rfl⟩ := hx
      · exact h0 ⟨x, hx⟩
      · refine hmem ⟨_, 𝔞.V.mem_of_valuation_le_one _ (hζz i).le⟩ (hr _ (Subfield.subset_closure (.inr ?_)))
        exact Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
    | algebraMap a => exact h0 (algebraMap O (W.gr 0) a)
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  obtain ⟨η, hη⟩ := factor (𝔞.toK.comp f') (Subtype.val_injective.comp hf'.inj) _ hall
  have hη' : ∀ x, (f' (η x) : 𝔞.K) = ζ x := hη
  have hmax : ∀ x, 𝔞.V.valuation (ζ x) < 1 → η x ∈ maximalIdeal A' := fun x hx hu => by
    rw [← hη', ← 𝔞.V.valuation_lt_one_iff] at hx
    exact hx (hu.map f')
  letI : Algebra O A' := (η.comp (algebraMap O W.A)).toAlgebra
  haveI := hf'.complete
  obtain ⟨Ξ, hΞ, hΞm⟩ := Po.extR O X R W hz A' { η with commutes' := fun _ => rfl } (fun i => hmax _ (hζz i))
    fun b hb hm => hmax b (by
      rw [hζ0 ⟨b, hb⟩]
      exact (𝔞.V.valuation_lt_one_iff _).1 (hy ⟨b, hb⟩ hm))
  refine ⟨A', inferInstance, inferInstance, inferInstance, f', Ξ, hf', hΞm, fun b => Subtype.ext ?_⟩
  have e : Ξ ((b : W.A) : R) = η b := AlgHom.congr_fun hΞ b
  show (f' (Ξ _) : 𝔞.K) = _
  rw [e, hη', hζ0]
