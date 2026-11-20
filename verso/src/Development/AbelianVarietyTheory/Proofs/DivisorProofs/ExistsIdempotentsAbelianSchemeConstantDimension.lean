import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothOfRelDimOfIsUnitProperFlat
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DimSplit

/- English proof (translation)
Use `(PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (by` as an intermediate fact. Use extensionality with `q`. Use `show q ∈ PrimeSpectrum.basicOpen a ↔ q ∈ PrimeSpectrum.basicOpen b`. Simplify using `only [PrimeSpectrum.mem_basicOpen]`. Conclude with `hab q)`.

Conclude with `congrArg Subtype.val this`.
-/
theorem idem_eq_of {S : Type} [CommRing S] {a b : S} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : ∀ q : PrimeSpectrum S, a ∉ q.asIdeal ↔ b ∉ q.asIdeal) : a = b := by
  have := (PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).injective
    (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (by
      ext q
      show q ∈ PrimeSpectrum.basicOpen a ↔ q ∈ PrimeSpectrum.basicOpen b
      simp only [PrimeSpectrum.mem_basicOpen]
      exact hab q)
  exact congrArg Subtype.val this

/- English proof (translation)
Establish `hfin : (Set.range d).Finite` using `hd.range_finite`. Set `s` to `hfin.toFinset`. Set `g : Fin s.card → α` to `fun k => (s.equivFin.symm k).1`. Establish `hg : Function.Injective g` using `fun i j h => s.equivFin.symm.injective (Subtype.val_injective h)`. Set `C : Fin s.card → TopologicalSpace.Clopens (PrimeSpectrum R)` to `fun k => ⟨d ⁻¹' {g k}, hd.isClopen_fiber _⟩`.

Set `e : Fin s.card → R` to `fun k => ((PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm (C k)).1`. Establish `he : ∀ k, IsIdempotentElem (e k)` using `fun k => ((PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm (C k)).2`. Establish `hmem : ∀ k (p : PrimeSpectrum R), e k ∉ p.asIdeal ↔ d p = g k`. Introduce `k p`. Establish `h` using `PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm (R := R) (C k)`.

Rewrite using `[← PrimeSpectrum.mem_basicOpen]`. Use `show p ∈ PrimeSpectrum.basicOpen (e k) ↔ _`. Rewrite using `[h]`. Both sides reduce to the same expression. Establish `horth : OrthogonalIdempotents e`.

Use `⟨he, fun i j hij => idem_eq_of ((he i).mul (he j)) IsIdempotentElem.zero fun q => ?_⟩` and prove the remaining obligations. Use `⟨fun h => ?_, fun h => absurd q.asIdeal.zero_mem h⟩` and prove the remaining obligations. Establish `hi : e i ∉ q.asIdeal` using `fun hi => h (q.asIdeal.mul_mem_right _ hi)`. Establish `hj : e j ∉ q.asIdeal` using `fun hj => h (q.asIdeal.mul_mem_left _ hj)`. Conclude with `absurd (hg (((hmem i q).1 hi).symm.trans ((hmem j q).1 hj))) hij`.

Use `⟨s.card, e, ⟨horth, ?_⟩, fun k => ⟨g k, fun p hp => (hmem k p).1 fun hk => ?_⟩⟩` and prove the remaining obligations. Use `idem_eq_of horth.isIdempotentElem_sum IsIdempotentElem.one fun q => ?_` and prove the remaining obligations. Use `⟨fun _ => q.isPrime.ne_top ∘ (Ideal.eq_top_iff_one _).2, fun _ hsum => ?_⟩` and prove the remaining obligations. Establish `hq : d q ∈ s` using `hfin.mem_toFinset.2 ⟨q, rfl⟩`. Set `k` to `s.equivFin ⟨d q, hq⟩`.

Establish `hk : g k = d q` using `by simp [g, k]`. Establish `hrest : ∑ j ∈ Finset.univ.erase k, e j ∈ q.asIdeal`. Use `Ideal.sum_mem _ fun j hj => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hj'`. Conclude with `(Finset.ne_of_mem_erase hj) (hg (((hmem j q).1 hj').symm.trans hk.symm))`.

Establish `: e k ∈ q.asIdeal`. Establish `h2` using `q.asIdeal.sub_mem hsum hrest`. Rewrite `h2` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ k), add_sub_cancel_right]`. Then use the resulting hypothesis. Conclude with `(hmem k q).2 hk.symm this`. Conclude with `p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using p.asIdeal.add_mem hp hk))`.
-/
theorem exists_idempotents_of_isLocallyConstant {R α : Type} [CommRing R] (d : PrimeSpectrum R → α)
    (hd : IsLocallyConstant d) :
    ∃ (n : ℕ) (e : Fin n → R), CompleteOrthogonalIdempotents e ∧
      ∀ k, ∃ a : α, ∀ p : PrimeSpectrum R, 1 - e k ∈ p.asIdeal → d p = a := by
  classical
  have hfin : (Set.range d).Finite := hd.range_finite
  let s := hfin.toFinset
  let g : Fin s.card → α := fun k => (s.equivFin.symm k).1
  have hg : Function.Injective g := fun i j h => s.equivFin.symm.injective (Subtype.val_injective h)
  let C : Fin s.card → TopologicalSpace.Clopens (PrimeSpectrum R) := fun k =>
    ⟨d ⁻¹' {g k}, hd.isClopen_fiber _⟩
  let e : Fin s.card → R := fun k => ((PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm (C k)).1
  have he : ∀ k, IsIdempotentElem (e k) := fun k =>
    ((PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm (C k)).2
  have hmem : ∀ k (p : PrimeSpectrum R), e k ∉ p.asIdeal ↔ d p = g k := by
    intro k p
    have h := PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm (R := R) (C k)
    rw [← PrimeSpectrum.mem_basicOpen]
    show p ∈ PrimeSpectrum.basicOpen (e k) ↔ _
    rw [h]
    rfl
  have horth : OrthogonalIdempotents e := by
    refine ⟨he, fun i j hij => idem_eq_of ((he i).mul (he j)) IsIdempotentElem.zero fun q => ?_⟩
    refine ⟨fun h => ?_, fun h => absurd q.asIdeal.zero_mem h⟩
    have hi : e i ∉ q.asIdeal := fun hi => h (q.asIdeal.mul_mem_right _ hi)
    have hj : e j ∉ q.asIdeal := fun hj => h (q.asIdeal.mul_mem_left _ hj)
    exact absurd (hg (((hmem i q).1 hi).symm.trans ((hmem j q).1 hj))) hij
  refine ⟨s.card, e, ⟨horth, ?_⟩, fun k => ⟨g k, fun p hp => (hmem k p).1 fun hk => ?_⟩⟩
  · refine idem_eq_of horth.isIdempotentElem_sum IsIdempotentElem.one fun q => ?_
    refine ⟨fun _ => q.isPrime.ne_top ∘ (Ideal.eq_top_iff_one _).2, fun _ hsum => ?_⟩
    have hq : d q ∈ s := hfin.mem_toFinset.2 ⟨q, rfl⟩
    let k := s.equivFin ⟨d q, hq⟩
    have hk : g k = d q := by simp [g, k]
    have hrest : ∑ j ∈ Finset.univ.erase k, e j ∈ q.asIdeal := by
      refine Ideal.sum_mem _ fun j hj => ?_
      by_contra hj'
      exact (Finset.ne_of_mem_erase hj) (hg (((hmem j q).1 hj').symm.trans hk.symm))
    have : e k ∈ q.asIdeal := by
      have h2 := q.asIdeal.sub_mem hsum hrest
      rwa [← Finset.add_sum_erase _ _ (Finset.mem_univ k), add_sub_cancel_right] at h2
    exact (hmem k q).2 hk.symm this
  · exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using p.asIdeal.add_mem hp hk))

end GlobalTheory.DimSplit

namespace GlobalTheory.DimSplit

/- English proof (translation)
Introduce `R₀ _ A _ hA`. Use `hA.smooth` as an intermediate fact. Use `hA.proper` as an intermediate fact. Use `hA.geomConnected` as an intermediate fact. Use `choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim A.hom`.

Establish `loc : ∀ x y, y ∈ W x → n y = n x` using `fun x y hy => by`. Use `hd x` as an intermediate fact. Use `hd y` as an intermediate fact. Establish `e₁ : SmoothOfRelativeDimension (0 + n y) ((W y ⊓ W x).ι ≫ A.hom)`. Rewrite using `[← Scheme.homOfLE_ι _ (inf_le_left : W y ⊓ W x ≤ W y), Category.assoc]`.

Use `infer_instance`. Establish `e₂ : SmoothOfRelativeDimension (0 + n x) ((W y ⊓ W x).ι ≫ A.hom)`. Rewrite using `[← Scheme.homOfLE_ι _ (inf_le_right : W y ⊓ W x ≤ W x), Category.assoc]`. Use `infer_instance`. Simplify using `using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hW y, hy⟩`.

Establish `hc : IsLocallyConstant n` using `(IsLocallyConstant.iff_exists_open n).2 fun x => ⟨W x, (W x).isOpen, hW x, loc x⟩`. Establish `fib : ∀ x y, A.hom x = A.hom y → n x = n y` using `fun x y h => hc.apply_eq_of_isPreconnected (A.hom.isConnected_preimage_singleton (A.hom x)).isPreconnected`. Use `rfl h.symm`. Establish `hsurj : Function.Surjective A.hom` using `(inferInstance : Surjective A.hom).surj`. Set `d : PrimeSpectrum R₀ → ℕ` to `fun p => n (Classical.choose (hsurj p))`.

Establish `hdn : ∀ x, d (A.hom x) = n x` using `fun x => fib _ _ (Classical.choose_spec (hsurj (A.hom x)))`. Establish `hdl : IsLocallyConstant d`. Use `(IsLocallyConstant.iff_isOpen_fiber).2 fun g => ?_` and prove the remaining obligations. Establish `hcl : IsClosed (A.hom '' (n ⁻¹' {g})ᶜ)` using `A.hom.isClosedMap _ (hc.isOpen_fiber g).isClosed_compl`. Establish `heq : (d ⁻¹' {g})ᶜ = A.hom '' (n ⁻¹' {g})ᶜ`.

Use extensionality with `p`. Use `⟨fun hp => ⟨_, hp, Classical.choose_spec (hsurj p)⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `fun h => hx (show n x = g from (hdn x).symm.trans h)`. Rewrite using `[← isClosed_compl_iff, heq]`.

Conclude with `hcl`. Take `⟨m, e, he, hk⟩` from `exists_idempotents_of_isLocallyConstant d hdl`. Use `⟨m, e, he, fun k => ?_⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `hk k`. Use `⟨g, GlobalTheory.SmoothNearFibre.smoothOfRelativeDimension_pullback_snd A.hom _ g fun z w hzw => ⟨W z, hW z, ?_⟩⟩` and prove the remaining obligations.

Establish `hn : n z = g`. Rewrite using `[← hdn z, hzw]`. Apply `hg` to reduce the goal to its premises. Use `show Ideal.Quotient.mk _ (1 - e k) ∈ w.asIdeal`. Establish `h0 : Ideal.Quotient.mk (Ideal.span {1 - e k}) (1 - e k) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))`.

Rewrite using `[h0]`. Conclude with `w.asIdeal.zero_mem`. Rewrite using `[← hn]`. Conclude with `hd z`.
-/
theorem exists_idempotents_smoothOfRelativeDimension : ∀ (R₀ : Type) [CommRing R₀] (A : Over (Sp R₀)) [GrpObj A],
    IsAbelianScheme A → ∃ (n : ℕ) (e : Fin n → R₀), CompleteOrthogonalIdempotents e ∧ ∀ k, ∃ g : ℕ,
      SmoothOfRelativeDimension g (Limits.pullback.snd A.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - e k})))) := by
  intro R₀ _ A _ hA
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim A.hom
  have loc : ∀ x y, y ∈ W x → n y = n x := fun x y hy => by
    have := hd x
    have := hd y
    have e₁ : SmoothOfRelativeDimension (0 + n y) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W y ⊓ W x ≤ W y), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + n x) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W y ⊓ W x ≤ W x), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hW y, hy⟩
  have hc : IsLocallyConstant n :=
    (IsLocallyConstant.iff_exists_open n).2 fun x => ⟨W x, (W x).isOpen, hW x, loc x⟩
  have fib : ∀ x y, A.hom x = A.hom y → n x = n y := fun x y h =>
    hc.apply_eq_of_isPreconnected (A.hom.isConnected_preimage_singleton (A.hom x)).isPreconnected
      rfl h.symm
  have hsurj : Function.Surjective A.hom := (inferInstance : Surjective A.hom).surj
  let d : PrimeSpectrum R₀ → ℕ := fun p => n (Classical.choose (hsurj p))
  have hdn : ∀ x, d (A.hom x) = n x := fun x => fib _ _ (Classical.choose_spec (hsurj (A.hom x)))
  have hdl : IsLocallyConstant d := by
    refine (IsLocallyConstant.iff_isOpen_fiber).2 fun g => ?_
    have hcl : IsClosed (A.hom '' (n ⁻¹' {g})ᶜ) :=
      A.hom.isClosedMap _ (hc.isOpen_fiber g).isClosed_compl
    have heq : (d ⁻¹' {g})ᶜ = A.hom '' (n ⁻¹' {g})ᶜ := by
      ext p
      refine ⟨fun hp => ⟨_, hp, Classical.choose_spec (hsurj p)⟩, ?_⟩
      rintro ⟨x, hx, rfl⟩
      exact fun h => hx (show n x = g from (hdn x).symm.trans h)
    rw [← isClosed_compl_iff, heq]
    exact hcl
  obtain ⟨m, e, he, hk⟩ := exists_idempotents_of_isLocallyConstant d hdl
  refine ⟨m, e, he, fun k => ?_⟩
  obtain ⟨g, hg⟩ := hk k
  refine ⟨g, GlobalTheory.SmoothNearFibre.smoothOfRelativeDimension_pullback_snd A.hom _ g fun z w hzw => ⟨W z, hW z, ?_⟩⟩
  have hn : n z = g := by
    rw [← hdn z, hzw]
    apply hg
    show Ideal.Quotient.mk _ (1 - e k) ∈ w.asIdeal
    have h0 : Ideal.Quotient.mk (Ideal.span {1 - e k}) (1 - e k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))
    rw [h0]
    exact w.asIdeal.zero_mem
  rw [← hn]
  exact hd z

end GlobalTheory.DimSplit
