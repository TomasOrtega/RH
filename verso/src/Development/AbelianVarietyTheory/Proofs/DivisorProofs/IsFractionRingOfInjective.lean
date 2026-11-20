import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleBaseChangeEvalHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFractionRingTensorOfFractionFieldsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.TensorTower

/- English proof (translation)
Use `haveI : IsDomain A := hi.isDomain (algebraMap A F)`. Use `⟨fun y => ?_, fun z => ?_, fun {x y} e => ⟨1, by simp [hi e]⟩⟩` and prove the remaining obligations. Conclude with `(map_ne_zero_iff _ hi).2 (nonZeroDivisors.ne_zero y.2) |>.isUnit`. Take `⟨x, y, hy, e⟩` from `hs z`. Conclude with `⟨⟨x, y, mem_nonZeroDivisors_of_ne_zero fun h => hy (by simp [h])⟩, e⟩`.
-/
theorem isFractionRing_of_injective {A F : Type} [CommRing A] [Field F] [Algebra A F]
    (hi : Function.Injective (algebraMap A F))
    (hs : ∀ z : F, ∃ x y : A, algebraMap A F y ≠ 0 ∧ z * algebraMap A F y = algebraMap A F x) :
    IsFractionRing A F := by
  haveI : IsDomain A := hi.isDomain (algebraMap A F)
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} e => ⟨1, by simp [hi e]⟩⟩
  · exact (map_ne_zero_iff _ hi).2 (nonZeroDivisors.ne_zero y.2) |>.isUnit
  · obtain ⟨x, y, hy, e⟩ := hs z
    exact ⟨⟨x, y, mem_nonZeroDivisors_of_ne_zero fun h => hy (by simp [h])⟩, e⟩

/- English proof (translation)
The claim follows from `isFractionRing_of_injective Subtype.val_injective fun z => by obtain ⟨a, ha, b, hb, hb0, e⟩ := h z exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hb0, e⟩`.
-/
theorem isFractionRing_subring {K : Type} [Field K] (R : Subring K)
    (h : ∀ f : K, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ f * b = a) : IsFractionRing R K :=
  isFractionRing_of_injective Subtype.val_injective fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hb0, e⟩

/- English proof (translation)
Use `haveI := hB.isLocalRing`. Set `c0 : ℂ →+* B` to `(algebraMap ℂ κ).codRestrict B hB.const_mem`. Set `g : ℂ →+* IsLocalRing.ResidueField B` to `(IsLocalRing.residue B).comp c0`. Establish `key : ∀ (b : B) (a : ℂ), NonUnit B ((b : κ) - algebraMap ℂ κ a) ↔ IsLocalRing.residue B b = g a` using `fun b a => by`. Rewrite using `[show (b : κ) - algebraMap ℂ κ a = ((b - c0 a : B) : κ) from rfl, nonUnit_iff, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]`.

Use `show _ ↔ Ideal.Quotient.mk _ b = Ideal.Quotient.mk _ (c0 a)`. Rewrite using `[Ideal.Quotient.eq]`. Establish `hbij : Function.Bijective g` using `⟨g.injective, fun y => by`. Take `⟨b, rfl⟩` from `IsLocalRing.residue_surjective y`. Take `⟨a, ha⟩` from `hr b b.2`.

Conclude with `⟨a, ((key b a).1 ha).symm⟩⟩`. Set `e` to `RingEquiv.ofBijective g hbij`. Use `⟨e.symm.toRingHom.comp (IsLocalRing.residue B), fun b a => ?_⟩` and prove the remaining obligations. Rewrite using `[key]`. Use `show _ ↔ e.symm _ = a`.

Rewrite using `[e.symm_apply_eq]`. Both sides reduce to the same expression.
-/
theorem exists_residue {κ : Type} [Field κ] [Algebra ℂ κ] (B : Subring κ)
    (hB : IsLocModel (algebraMap ℂ κ) B) (hr : RatRes (algebraMap ℂ κ) B) :
    ∃ ev : B →+* ℂ, ∀ (b : B) (a : ℂ), NonUnit B ((b : κ) - algebraMap ℂ κ a) ↔ ev b = a := by
  haveI := hB.isLocalRing
  let c0 : ℂ →+* B := (algebraMap ℂ κ).codRestrict B hB.const_mem
  let g : ℂ →+* IsLocalRing.ResidueField B := (IsLocalRing.residue B).comp c0
  have key : ∀ (b : B) (a : ℂ), NonUnit B ((b : κ) - algebraMap ℂ κ a) ↔
      IsLocalRing.residue B b = g a := fun b a => by
    rw [show (b : κ) - algebraMap ℂ κ a = ((b - c0 a : B) : κ) from rfl, nonUnit_iff,
      ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    show _ ↔ Ideal.Quotient.mk _ b = Ideal.Quotient.mk _ (c0 a)
    rw [Ideal.Quotient.eq]
  have hbij : Function.Bijective g := ⟨g.injective, fun y => by
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := hr b b.2
    exact ⟨a, ((key b a).1 ha).symm⟩⟩
  let e := RingEquiv.ofBijective g hbij
  refine ⟨e.symm.toRingHom.comp (IsLocalRing.residue B), fun b a => ?_⟩
  rw [key]
  show _ ↔ e.symm _ = a
  rw [e.symm_apply_eq]
  rfl

/- English proof (translation)
Introduce `K κ L _ _ _ _ _ _ _ _ _ R B hB r τ hR hRn hRr hBr hm he`. Use `haveI := hR.isLocalRing`. Use `haveI := hB.isLocalRing`. Use `letI iR : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R hR.const_mem).toAlgebra`. Use `letI iB : Algebra ℂ B := ((algebraMap ℂ κ).codRestrict B hB.const_mem).toAlgebra`.

Use `haveI : IsScalarTower ℂ R K := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : IsScalarTower ℂ B κ := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : IsFractionRing R K := isFractionRing_subring R hR.frac`. Use `haveI : IsFractionRing B κ := isFractionRing_subring B hB.frac`. Take `⟨hinj, hsurj⟩` from `GlobalTheory.T.isFractionRing_tensor_of_fraction_fields (k := ℂ) (R := R) (B := B) (K := K) (κ := κ) (L := L)`.

Use `set f := (algebraMap (K ⊗[ℂ] κ) L).comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℂ R K) (IsScalarTower.toAlgHom ℂ B κ)).toRingHom with hf`. Use `letI iA : Algebra (R ⊗[ℂ] B) L := f.toAlgebra`. Use `haveI : IsFractionRing (R ⊗[ℂ] B) L := isFractionRing_of_injective hinj hsurj`. Use `haveI : IsDomain (R ⊗[ℂ] B) := hinj.isDomain f`. Use `haveI : Nontrivial (R ⊗[ℂ] B) := IsDomain.toNontrivial`.

Establish `hft : ∀ (a : R) (b : B), algebraMap (R ⊗[ℂ] B) L (a ⊗ₜ b) = algebraMap (K ⊗[ℂ] κ) L ((a : K) ⊗ₜ (b : κ))` using `fun a b => rfl`. Take `⟨ev, hev⟩` from `exists_residue B hB hBr`. Establish `hevc : ∀ a : ℂ, ev (algebraMap ℂ B a) = a` using `fun a => (hev _ a).1 (by`. Rewrite using `[show ((algebraMap ℂ B a : B) : κ) = algebraMap ℂ κ a from rfl, sub_self]`. Conclude with `nonUnit_zero B)`.

Set `ev' : B →ₐ[ℂ] ℂ` to `{ ev with commutes' := hevc }`. Set `φ : R ⊗[ℂ] B →ₐ[ℂ] R` to `Algebra.TensorProduct.lift (AlgHom.id ℂ R) ((Algebra.ofId ℂ R).comp ev') (fun _ _ => Commute.all _ _)`. Establish `hφ : ∀ (a : R) (b : B), φ (a ⊗ₜ b) = a * algebraMap ℂ R (ev b)` using `fun a b => by`. Simplify using `[φ, ev']`. Set `q : Ideal (R ⊗[ℂ] B)` to `(IsLocalRing.maximalIdeal R).comap φ`.

Use `haveI : q.IsPrime := Ideal.comap_isPrime _ _`. Establish `hq : q.primeCompl ≤ nonZeroDivisors (R ⊗[ℂ] B)` using `q.primeCompl_le_nonZeroDivisors`. Set `A : Subalgebra (R ⊗[ℂ] B) L` to `Localization.subalgebra.ofField L q.primeCompl hq`. Use `haveI hA : IsLocalization q.primeCompl A := Localization.subalgebra.isLocalization_ofField L _ hq`. Establish `hu : ∀ y : q.primeCompl, IsUnit (φ.toRingHom y)` using `fun y => by`.

Assume the negation of the conclusion as `hy`. Conclude with `y.2 (show (y : R ⊗[ℂ] B) ∈ q from (IsLocalRing.mem_maximalIdeal _).2 hy)`. Set `ψ : A →+* R` to `IsLocalization.lift hu`. Establish `hψ : ∀ x, ψ (algebraMap _ A x) = φ x` using `IsLocalization.lift_eq hu`. Set `a : R ⊗[ℂ] B →+* A` to `algebraMap _ A`.

Establish `ha : ∀ x, (a x : L) = algebraMap (R ⊗[ℂ] B) L x` using `fun x => rfl`. Set `ι : R →+* A` to `a.comp Algebra.TensorProduct.includeLeftRingHom`. Set `j : B →+* A` to `a.comp Algebra.TensorProduct.includeRight.toRingHom`. Establish `hcL : ∀ z : ℂ, algebraMap (R ⊗[ℂ] B) L (algebraMap ℂ _ z) = algebraMap ℂ L z` using `fun z => by`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, hft, IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ) L, Algebra.TensorProduct.algebraMap_apply]`.

Both sides reduce to the same expression. Establish `hcl : ∀ x, a x ∈ Subring.closure (Set.range ι ∪ Set.range j)` using `fun x => by`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y`.

Establish `e : a (x ⊗ₜ y) = ι x * j y`. Simplify using `[ι, j, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[e]`. Conclude with `Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨x, rfl⟩)) (Subring.subset_closure (Or.inr ⟨y, rfl⟩))`. Consider the case `add x y hx hy => rw [map_add]`.

Conclude with `Subring.add_mem _ hx hy`. Establish `hmem : ∀ z : ℂ, algebraMap ℂ L z ∈ A.toSubring` using `fun z => by`. Rewrite using `[← hcL]`. Conclude with `A.algebraMap_mem _`. Establish `hevτ : ∀ i, ev (τ i) = 0` using `fun i => by`.

Use `(hev _ 0).1 ?_` and prove the remaining obligations. Rewrite using `[map_zero, sub_zero]`. Use `(nonUnit_iff (τ i)).2 fun hu => ?_` and prove the remaining obligations. Establish `: τ i ∈ IsLocalRing.maximalIdeal B`. Rewrite using `[hm]`.

Conclude with `Ideal.subset_span ⟨i, rfl⟩`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 this hu`. Use `⟨A.toSubring, ι, ψ, j, ⟨hR, hRn, ⟨hmem, IsLocalization.AtPrime.isLocalRing A q, ?_, ?_⟩, fun z => ?_, fun x => ?_, fun i => ?_, ?_⟩, fun x => rfl, fun y => rfl, fun b z hbz => ?_, fun t => ?_⟩` and prove the remaining obligations. Establish `e : (algebraMap ℂ L).codRestrict A.toSubring hmem = a.comp (algebraMap ℂ (R ⊗[ℂ] B))` using `RingHom.ext fun z => Subtype.ext (hcL z).symm`. Rewrite using `[e]`.

Use `haveI : Algebra.EssFiniteType ℂ R := RingHom.essFiniteType_algebraMap.1 hR.essFiniteType`. Use `haveI : Algebra.EssFiniteType ℂ B := RingHom.essFiniteType_algebraMap.1 hB.essFiniteType`. Use `haveI : Algebra.EssFiniteType ℂ (R ⊗[ℂ] B) := Algebra.EssFiniteType.comp ℂ R _`. Establish `h1 : (algebraMap (R ⊗[ℂ] B) A).EssFiniteType` using `RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization A q.primeCompl)`. Establish `h2 : (algebraMap ℂ (R ⊗[ℂ] B)).EssFiniteType` using `RingHom.essFiniteType_algebraMap.2 inferInstance`.

Conclude with `h2.comp h1`. Introduce `z`. Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (A := R ⊗[ℂ] B) z`. Establish `hy' : algebraMap (R ⊗[ℂ] B) L y ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy`. Conclude with `⟨_, A.algebraMap_mem x, _, A.algebraMap_mem y, hy', div_mul_cancel₀ _ hy'⟩`.

Conclude with `(ha _).trans (hcL z)`. Use `show ψ (a (x ⊗ₜ 1)) = x`. Rewrite using `[hψ, hφ, map_one, map_one, mul_one]`. Use `show ψ (a (1 ⊗ₜ τ i)) = 0`. Rewrite using `[hψ, hφ, hevτ, map_zero, mul_zero]`.

Establish `e : MvPolynomial.eval₂Hom ι (fun i => j (τ i)) = a.comp (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[ℂ] B) (fun i => (1 : R) ⊗ₜ[ℂ] τ i))`. Apply the tactic sequence `ext x <;> simp [ι, j]`. Rewrite using `[e]`. Establish `h1 : (algebraMap (R ⊗[ℂ] B) A).FormallyEtale` using `RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isLocalization q.primeCompl)`. Conclude with `(GlobalTheory.T.formallyEtale_baseChange_eval_hom τ he).comp h1`.

Use `show ((ψ (a (1 ⊗ₜ b)) : R) : K) = _`. Rewrite using `[hψ, hφ, one_mul, (hev b z).1 hbz]`. Both sides reduce to the same expression. Take `⟨⟨x, y⟩, e⟩` from `IsLocalization.surj q.primeCompl (S := A) t`. Use `⟨a x, a y, hcl x, hcl y, ?_, congrArg Subtype.val e⟩` and prove the remaining obligations.

Rewrite using `[hψ]`. Conclude with `hu y`.
-/
theorem exists_isEtTower_tensor : ∀ {K κ L : Type} [Field K] [Field κ] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ) L] [IsScalarTower ℂ (K ⊗[ℂ] κ) L] [IsFractionRing (K ⊗[ℂ] κ) L]
    (R : Subring K) (B : Subring κ) (hB : IsLocModel (algebraMap ℂ κ) B) (r : ℕ) (τ : Fin r → B),
  IsLocModel (algebraMap ℂ K) R → IsIntegrallyClosed R → RatRes (algebraMap ℂ K) R →
  RatRes (algebraMap ℂ κ) B → (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) →
  (MvPolynomial.eval₂Hom ((algebraMap ℂ κ).codRestrict B hB.const_mem) τ).FormallyEtale →
  ∃ (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (j : B →+* T),
    IsEtTower (algebraMap ℂ K) R (algebraMap ℂ L) T ι ψ (fun i => j (τ i)) ∧
    (∀ a : R, (ι a : L) = algebraMap (K ⊗[ℂ] κ) L ((a : K) ⊗ₜ 1)) ∧
    (∀ b : B, (j b : L) = algebraMap (K ⊗[ℂ] κ) L (1 ⊗ₜ (b : κ))) ∧
    (∀ (b : B) (a : ℂ), NonUnit B ((b : κ) - algebraMap ℂ κ a) → ((ψ (j b) : R) : K) = algebraMap ℂ K a) ∧
    (∀ t : T, ∃ s s' : T, s ∈ Subring.closure (Set.range ι ∪ Set.range j) ∧
      s' ∈ Subring.closure (Set.range ι ∪ Set.range j) ∧ IsUnit (ψ s') ∧ (t : L) * s' = s) := by
  intro K κ L _ _ _ _ _ _ _ _ _ R B hB r τ hR hRn hRr hBr hm he
  haveI := hR.isLocalRing
  haveI := hB.isLocalRing
  letI iR : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R hR.const_mem).toAlgebra
  letI iB : Algebra ℂ B := ((algebraMap ℂ κ).codRestrict B hB.const_mem).toAlgebra
  haveI : IsScalarTower ℂ R K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ B κ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsFractionRing R K := isFractionRing_subring R hR.frac
  haveI : IsFractionRing B κ := isFractionRing_subring B hB.frac
  obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.isFractionRing_tensor_of_fraction_fields (k := ℂ) (R := R) (B := B) (K := K) (κ := κ) (L := L)
  set f := (algebraMap (K ⊗[ℂ] κ) L).comp (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom ℂ R K) (IsScalarTower.toAlgHom ℂ B κ)).toRingHom with hf
  letI iA : Algebra (R ⊗[ℂ] B) L := f.toAlgebra
  haveI : IsFractionRing (R ⊗[ℂ] B) L := isFractionRing_of_injective hinj hsurj
  haveI : IsDomain (R ⊗[ℂ] B) := hinj.isDomain f
  haveI : Nontrivial (R ⊗[ℂ] B) := IsDomain.toNontrivial
  have hft : ∀ (a : R) (b : B), algebraMap (R ⊗[ℂ] B) L (a ⊗ₜ b) =
      algebraMap (K ⊗[ℂ] κ) L ((a : K) ⊗ₜ (b : κ)) := fun a b => rfl

  obtain ⟨ev, hev⟩ := exists_residue B hB hBr
  have hevc : ∀ a : ℂ, ev (algebraMap ℂ B a) = a := fun a =>
    (hev _ a).1 (by
      rw [show ((algebraMap ℂ B a : B) : κ) = algebraMap ℂ κ a from rfl, sub_self]
      exact nonUnit_zero B)
  let ev' : B →ₐ[ℂ] ℂ := { ev with commutes' := hevc }
  let φ : R ⊗[ℂ] B →ₐ[ℂ] R := Algebra.TensorProduct.lift (AlgHom.id ℂ R)
    ((Algebra.ofId ℂ R).comp ev') (fun _ _ => Commute.all _ _)
  have hφ : ∀ (a : R) (b : B), φ (a ⊗ₜ b) = a * algebraMap ℂ R (ev b) := fun a b => by
    simp [φ, ev']
  let q : Ideal (R ⊗[ℂ] B) := (IsLocalRing.maximalIdeal R).comap φ
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  have hq : q.primeCompl ≤ nonZeroDivisors (R ⊗[ℂ] B) := q.primeCompl_le_nonZeroDivisors
  let A : Subalgebra (R ⊗[ℂ] B) L := Localization.subalgebra.ofField L q.primeCompl hq
  haveI hA : IsLocalization q.primeCompl A := Localization.subalgebra.isLocalization_ofField L _ hq
  have hu : ∀ y : q.primeCompl, IsUnit (φ.toRingHom y) := fun y => by
    by_contra hy
    exact y.2 (show (y : R ⊗[ℂ] B) ∈ q from (IsLocalRing.mem_maximalIdeal _).2 hy)
  let ψ : A →+* R := IsLocalization.lift hu
  have hψ : ∀ x, ψ (algebraMap _ A x) = φ x := IsLocalization.lift_eq hu
  let a : R ⊗[ℂ] B →+* A := algebraMap _ A
  have ha : ∀ x, (a x : L) = algebraMap (R ⊗[ℂ] B) L x := fun x => rfl
  let ι : R →+* A := a.comp Algebra.TensorProduct.includeLeftRingHom
  let j : B →+* A := a.comp Algebra.TensorProduct.includeRight.toRingHom
  have hcL : ∀ z : ℂ, algebraMap (R ⊗[ℂ] B) L (algebraMap ℂ _ z) = algebraMap ℂ L z := fun z => by
    rw [Algebra.TensorProduct.algebraMap_apply, hft, IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ) L,
      Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hcl : ∀ x, a x ∈ Subring.closure (Set.range ι ∪ Set.range j) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have e : a (x ⊗ₜ y) = ι x * j y := by
        simp [ι, j, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]
      rw [e]
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨x, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨y, rfl⟩))
    | add x y hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
  have hmem : ∀ z : ℂ, algebraMap ℂ L z ∈ A.toSubring := fun z => by
    rw [← hcL]; exact A.algebraMap_mem _
  have hevτ : ∀ i, ev (τ i) = 0 := fun i => by
    refine (hev _ 0).1 ?_
    rw [map_zero, sub_zero]
    refine (nonUnit_iff (τ i)).2 fun hu => ?_
    have : τ i ∈ IsLocalRing.maximalIdeal B := by
      rw [hm]; exact Ideal.subset_span ⟨i, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).1 this hu
  refine ⟨A.toSubring, ι, ψ, j, ⟨hR, hRn, ⟨hmem, IsLocalization.AtPrime.isLocalRing A q, ?_, ?_⟩,
    fun z => ?_, fun x => ?_, fun i => ?_, ?_⟩, fun x => rfl, fun y => rfl, fun b z hbz => ?_,
    fun t => ?_⟩
  · have e : (algebraMap ℂ L).codRestrict A.toSubring hmem = a.comp (algebraMap ℂ (R ⊗[ℂ] B)) :=
      RingHom.ext fun z => Subtype.ext (hcL z).symm
    rw [e]
    haveI : Algebra.EssFiniteType ℂ R := RingHom.essFiniteType_algebraMap.1 hR.essFiniteType
    haveI : Algebra.EssFiniteType ℂ B := RingHom.essFiniteType_algebraMap.1 hB.essFiniteType
    haveI : Algebra.EssFiniteType ℂ (R ⊗[ℂ] B) := Algebra.EssFiniteType.comp ℂ R _
    have h1 : (algebraMap (R ⊗[ℂ] B) A).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization A q.primeCompl)
    have h2 : (algebraMap ℂ (R ⊗[ℂ] B)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
    exact h2.comp h1
  · intro z
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R ⊗[ℂ] B) z
    have hy' : algebraMap (R ⊗[ℂ] B) L y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    exact ⟨_, A.algebraMap_mem x, _, A.algebraMap_mem y, hy', div_mul_cancel₀ _ hy'⟩
  · exact (ha _).trans (hcL z)
  · show ψ (a (x ⊗ₜ 1)) = x
    rw [hψ, hφ, map_one, map_one, mul_one]
  · show ψ (a (1 ⊗ₜ τ i)) = 0
    rw [hψ, hφ, hevτ, map_zero, mul_zero]
  · have e : MvPolynomial.eval₂Hom ι (fun i => j (τ i)) =
        a.comp (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[ℂ] B)
          (fun i => (1 : R) ⊗ₜ[ℂ] τ i)) := by
      ext x <;> simp [ι, j]
    rw [e]
    have h1 : (algebraMap (R ⊗[ℂ] B) A).FormallyEtale :=
      RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isLocalization q.primeCompl)
    exact (GlobalTheory.T.formallyEtale_baseChange_eval_hom τ he).comp h1
  · show ((ψ (a (1 ⊗ₜ b)) : R) : K) = _
    rw [hψ, hφ, one_mul, (hev b z).1 hbz]
    rfl
  · obtain ⟨⟨x, y⟩, e⟩ := IsLocalization.surj q.primeCompl (S := A) t
    refine ⟨a x, a y, hcl x, hcl y, ?_, congrArg Subtype.val e⟩
    rw [hψ]; exact hu y

end GlobalTheory.FieldPair.TensorTower
