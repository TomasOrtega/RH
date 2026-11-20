import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFinrankLeCardAlgHomAlgebraicClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdPowOfZeros
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NullstellensatzPointOfSystem

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.HSChoice.EtaleSection

/- English proof (translation)
Use `⟨(Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom, ← Scheme.toSpecΓ_naturality, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]`.
-/
theorem exists_eq_isoSpec_comp {k : Type} [CommRing k] {X : Scheme.{0}} [IsAffine X] (g : X ⟶ Spec (.of k)) :
    letI := algebraΓOfHom g
    ∃ a : CommRingCat.of k ⟶ Γ(X, ⊤), a.hom = algebraMap k Γ(X, ⊤) ∧ g = X.isoSpec.hom ≫ Spec.map a := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop, rfl, ?_⟩
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/- English proof (translation)
Use `letI := algebraΓOfHom (I.subschemeι ≫ S.str)`. Use `haveI : IsFinite (I.subschemeι ≫ S.str) := hI`. Use `haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ S.str)`. Take `⟨a, ha, he⟩` from `exists_eq_isoSpec_comp (I.subschemeι ≫ S.str)`. Establish `e1 : Nat.card (S.subPts I Ω) = Nat.card {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)}`.

Use `(Nat.card_congr (Equiv.ofBijective (fun z => (⟨⟨z.1 ≫ I.subschemeι, by rw [Category.assoc]; exact z.2⟩, z.1, rfl⟩ : S.subPts I Ω)) ⟨?_, ?_⟩)).symm` and prove the remaining obligations. Introduce `z z' h`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h0 : z.1 ≫ I.subschemeι = z'.1 ≫ I.subschemeι` using `congrArg (fun x : S.subPts I Ω => x.1.1) h`. Conclude with `(cancel_mono I.subschemeι).1 h0`.

Introduce and unpack `⟨x, z, hz⟩`. Use `⟨⟨z, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, hz]`. Conclude with `x.2`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hz`. Establish `hmk : ∀ φ : Γ(I.subscheme, ⊤) →ₐ[k] Ω, (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ I.subscheme.isoSpec.inv) ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)`. Introduce `φ`. Rewrite using `[he, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]`.

Use `congr 1`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Use extensionality with `r`. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]`. Rewrite using `[ha]`.

Conclude with `φ.commutes r`. Establish `e2 : Nat.card {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)} = Nat.card (Γ(I.subscheme, ⊤) →ₐ[k] Ω)`. Use `(Nat.card_congr (Equiv.ofBijective (fun φ : Γ(I.subscheme, ⊤) →ₐ[k] Ω => (⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ I.subscheme.isoSpec.inv, hmk φ⟩ : {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)})) ⟨?_, ?_⟩)).symm` and prove the remaining obligations. Introduce `φ ψ h`. Simplify using `only [Subtype.mk.injEq, cancel_mono] at h`.

Establish `h2` using `Spec.map_injective h`. Use extensionality with `r`. Conclude with `congrArg (fun f => f.hom r) h2`. Introduce and unpack `⟨z, hz⟩`. Establish `hψ : Spec.map (Spec.preimage (z ≫ I.subscheme.isoSpec.hom)) = z ≫ I.subscheme.isoSpec.hom` using `Spec.map_preimage _`.

Establish `hc : a ≫ Spec.preimage (z ≫ I.subscheme.isoSpec.hom) = CommRingCat.ofHom (algebraMap k Ω)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hψ, Category.assoc, ← he]`. Conclude with `hz`. Use `⟨AlgHom.mk (Spec.preimage (z ≫ I.subscheme.isoSpec.hom)).hom (fun r => ?_), ?_⟩` and prove the remaining obligations.

Establish `h3` using `congrArg (fun f => f.hom r) hc`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, ha] at h3`. Conclude with `h3`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Iso.comp_inv_eq]`.

Conclude with `hψ`. Rewrite using `[e1, e2]`.
-/
theorem natCard_subPts {k : Type} [Field k] (S : LinSys k) (I : S.Y.IdealSheafData) (hI : S.IsFiniteSub I)
    (Ω : Type) [Field Ω] [Algebra k Ω] :
    letI := algebraΓOfHom (I.subschemeι ≫ S.str)
    Nat.card (S.subPts I Ω) = Nat.card (Γ(I.subscheme, ⊤) →ₐ[k] Ω) := by
  letI := algebraΓOfHom (I.subschemeι ≫ S.str)
  haveI : IsFinite (I.subschemeι ≫ S.str) := hI
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ S.str)
  obtain ⟨a, ha, he⟩ := exists_eq_isoSpec_comp (I.subschemeι ≫ S.str)
  have e1 : Nat.card (S.subPts I Ω) =
      Nat.card {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)} := by
    refine (Nat.card_congr (Equiv.ofBijective (fun z => (⟨⟨z.1 ≫ I.subschemeι, by rw [Category.assoc]; exact z.2⟩,
      z.1, rfl⟩ : S.subPts I Ω)) ⟨?_, ?_⟩)).symm
    · intro z z' h
      apply Subtype.ext
      have h0 : z.1 ≫ I.subschemeι = z'.1 ≫ I.subschemeι := congrArg (fun x : S.subPts I Ω => x.1.1) h
      exact (cancel_mono I.subschemeι).1 h0
    · rintro ⟨x, z, hz⟩
      refine ⟨⟨z, ?_⟩, ?_⟩
      · rw [← Category.assoc, hz]
        exact x.2
      · apply Subtype.ext
        apply Subtype.ext
        exact hz
  have hmk : ∀ φ : Γ(I.subscheme, ⊤) →ₐ[k] Ω,
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ I.subscheme.isoSpec.inv) ≫ I.subschemeι ≫ S.str =
        spMap (algebraMap k Ω) := by
    intro φ
    rw [he, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [ha]
    exact φ.commutes r
  have e2 : Nat.card {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)} =
      Nat.card (Γ(I.subscheme, ⊤) →ₐ[k] Ω) := by
    refine (Nat.card_congr (Equiv.ofBijective (fun φ : Γ(I.subscheme, ⊤) →ₐ[k] Ω =>
      (⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ I.subscheme.isoSpec.inv, hmk φ⟩ :
        {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)})) ⟨?_, ?_⟩)).symm
    · intro φ ψ h
      simp only [Subtype.mk.injEq, cancel_mono] at h
      have h2 := Spec.map_injective h
      ext r
      exact congrArg (fun f => f.hom r) h2
    · rintro ⟨z, hz⟩
      have hψ : Spec.map (Spec.preimage (z ≫ I.subscheme.isoSpec.hom)) = z ≫ I.subscheme.isoSpec.hom :=
        Spec.map_preimage _
      have hc : a ≫ Spec.preimage (z ≫ I.subscheme.isoSpec.hom) = CommRingCat.ofHom (algebraMap k Ω) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hψ, Category.assoc, ← he]
        exact hz
      refine ⟨AlgHom.mk (Spec.preimage (z ≫ I.subscheme.isoSpec.hom)).hom (fun r => ?_), ?_⟩
      · have h3 := congrArg (fun f => f.hom r) hc
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, ha] at h3
        exact h3
      · apply Subtype.ext
        rw [Iso.comp_inv_eq]
        exact hψ
  rw [e1, e2]

/- English proof (translation)
Use `letI := algebraΓOfHom (I.subschemeι ≫ S.str)`. Introduce `h`. Use `haveI : IsFinite (I.subschemeι ≫ S.str) := hI`. Use `haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ S.str)`. Take `⟨a, ha, he⟩` from `exists_eq_isoSpec_comp (I.subschemeι ≫ S.str)`.

Establish `h2 : Etale (Spec.map a)`. Use `HasRingHomProperty.Spec_iff.mpr ?_` and prove the remaining obligations. Rewrite using `[ha]`. Conclude with `(RingHom.etale_algebraMap (R := k) (S := Γ(I.subscheme, ⊤))).mpr h`. Rewrite using `[he]`.

Use `infer_instance`.
-/
theorem etale_of_algebraEtale {k : Type} [Field k] (S : LinSys k) (I : S.Y.IdealSheafData) (hI : S.IsFiniteSub I) :
    letI := algebraΓOfHom (I.subschemeι ≫ S.str)
    Algebra.Etale k Γ(I.subscheme, ⊤) → Etale (I.subschemeι ≫ S.str) := by
  letI := algebraΓOfHom (I.subschemeι ≫ S.str)
  intro h
  haveI : IsFinite (I.subschemeι ≫ S.str) := hI
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ S.str)
  obtain ⟨a, ha, he⟩ := exists_eq_isoSpec_comp (I.subschemeι ≫ S.str)
  have h2 : Etale (Spec.map a) := by
    refine HasRingHomProperty.Spec_iff.mpr ?_
    rw [ha]
    exact (RingHom.etale_algebraMap (R := k) (S := Γ(I.subscheme, ⊤))).mpr h
  rw [he]
  infer_instance

/- English proof (translation)
Establish `hv : (T.toLinSys.baseChange E).IsVariety` using `hT.alg.variety.baseChange E`. Establish `H` using `GlobalTheory.ProperCut.topSelf_eq_length_of_smooth (T.toLinSys.baseChange E).str hv.smooth hv.proj (T.toLinSys.baseChange E).isLB (fun i => (T.toLinSys.baseChange E).comb (s i)) hfin`. Establish `hdel : (T.toLinSys.baseChange E).del = T.del` using `GlobalTheory.FieldChangeInter.del_baseChange F E T.toLinSys hT.alg.variety.proj`. Use `⟨H.1, ?_⟩` and prove the remaining obligations. Use `⟨H.2.2.2.2.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hdel]`. Conclude with `H.2.2.2.2.2.symm`.
-/
theorem finite_finrank {F : Type} [Field F] [NumberField F] (T : Tuple F) (hT : T.IsGeometric) (E : Type) [Field E]
    [Algebra F E] (s : Fin T.D → Fin T.N → E)
    (hfin : ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite) :
    (T.toLinSys.baseChange E).IsFiniteSub (T.linSection E s) ∧
    (letI := algebraΓOfHom ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)
    Module.Finite E Γ((T.linSection E s).subscheme, ⊤) ∧
      (Module.finrank E Γ((T.linSection E s).subscheme, ⊤) : ℤ) = T.del) := by
  have hv : (T.toLinSys.baseChange E).IsVariety := hT.alg.variety.baseChange E
  have H := GlobalTheory.ProperCut.topSelf_eq_length_of_smooth (T.toLinSys.baseChange E).str hv.smooth hv.proj
    (T.toLinSys.baseChange E).isLB (fun i => (T.toLinSys.baseChange E).comb (s i)) hfin
  have hdel : (T.toLinSys.baseChange E).del = T.del :=
    GlobalTheory.FieldChangeInter.del_baseChange F E T.toLinSys hT.alg.variety.proj
  refine ⟨H.1, ?_⟩
  refine ⟨H.2.2.2.2.1, ?_⟩
  rw [← hdel]
  exact H.2.2.2.2.2.symm

/- English proof (translation)
Take `⟨i, j⟩` from `v`. Break down `Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl` into its components or cases. Simplify `isHomogeneous_C (Fin 1 × Fin N) (s i j)` using `[join, Fin.castSucc_ne_last]`. Simplify `isHomogeneous_X K ((0 : Fin 1), j)` using `[join]`.
-/
private lemma isHomogeneous_join_C_X {K : Type} [CommRing K] {D N : ℕ} (s : Fin D → Fin N → K) (v : Fin (D + 1) × Fin N) :
    (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v).IsHomogeneous
      (if v.1 = Fin.last D then 1 else 0) := by
  obtain ⟨i, j⟩ := v
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · simpa [join, Fin.castSucc_ne_last] using isHomogeneous_C (Fin 1 × Fin N) (s i j)
  · simpa [join] using isHomogeneous_X K ((0 : Fin 1), j)

/- English proof (translation)
Unfold `spec`. Rewrite using `[f.as_sum, map_sum]`. Apply `IsHomogeneous.sum` to reduce the goal to its premises. Introduce `m hm`. Establish `hprod : (m.prod fun v e => (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v) ^ e).IsHomogeneous (∑ v ∈ m.support, (if v.1 = Fin.last D then 1 else 0) * m v)` using `IsHomogeneous.prod _ _ _ fun v _ => (isHomogeneous_join_C_X s v).pow (m v)`.

Establish `hdeg : ∑ v ∈ m.support, (if v.1 = Fin.last D then 1 else 0) * m v = δ`. Rewrite using `[Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by simp [Finsupp.notMem_support_iff.1 hv])]`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single (Fin.last D)]`. Simplify using `using hf m hm (Fin.last D)`. Introduce `i _ hi`.

Simplify using `[hi]`. Simplify using the standard rewrite rules. Establish `h2` using `(isHomogeneous_C (Fin 1 × Fin N) (algebraMap F K (coeff m f))).mul hprod`. Rewrite `h2` using `[zero_add, hdeg]`. Rewrite using `[aeval_monomial, MvPolynomial.algebraMap_apply]`.

Conclude with `h2`.
-/
theorem isHomogeneous_spec {F K : Type} [Field F] [Field K] [Algebra F K] {D N δ : ℕ} (s : Fin D → Fin N → K)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (hf : IsMultiHomogeneous (fun _ => δ) f) :
    (spec s f).IsHomogeneous δ := by
  classical
  unfold spec
  rw [f.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro m hm
  have hprod : (m.prod fun v e =>
      (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v) ^ e).IsHomogeneous
      (∑ v ∈ m.support, (if v.1 = Fin.last D then 1 else 0) * m v) :=
    IsHomogeneous.prod _ _ _ fun v _ => (isHomogeneous_join_C_X s v).pow (m v)
  have hdeg : ∑ v ∈ m.support, (if v.1 = Fin.last D then 1 else 0) * m v = δ := by
    rw [Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by simp [Finsupp.notMem_support_iff.1 hv])]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (Fin.last D)]
    · simpa using hf m hm (Fin.last D)
    · intro i _ hi
      simp [hi]
    · simp
  have h2 := (isHomogeneous_C (Fin 1 × Fin N) (algebraMap F K (coeff m f))).mul hprod
  rw [zero_add, hdeg] at h2
  rw [aeval_monomial, MvPolynomial.algebraMap_apply]
  exact h2

/- English proof (translation)
Take `⟨i, j⟩` from `v`. Break down `Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl` into its components or cases. Simplify using `[join]`. Simplify using `[join]`.
-/
private lemma eval_join_C_X_eq_join {K : Type} [CommRing K] {D N : ℕ} (s : Fin D → Fin N → K) (ξ : Fin N → K)
    (v : Fin (D + 1) × Fin N) :
    eval (fun p : Fin 1 × Fin N => ξ p.2)
      (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v) = join s ξ v := by
  obtain ⟨i, j⟩ := v
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · simp [join]
  · simp [join]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [spec, MvPolynomial.algebraMap_apply]`. Consider the case `add p q hp hq`. Simplify using `only [spec, map_add] at hp hq ⊢`. Rewrite using `[hp, hq]`.

Consider the case `mul_X p v hp`. Simplify using `only [spec, map_mul, aeval_X] at hp ⊢`. Rewrite using `[hp, eval_join_C_X_eq_join]`.
-/
theorem eval_spec {F K : Type} [CommRing F] [CommRing K] [Algebra F K] {D N : ℕ} (s : Fin D → Fin N → K)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (ξ : Fin N → K) :
    eval (fun p => ξ p.2) (spec s f) = aeval (join s ξ) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [spec, MvPolynomial.algebraMap_apply]
  | add p q hp hq =>
    simp only [spec, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    simp only [spec, map_mul, aeval_X] at hp ⊢
    rw [hp, eval_join_C_X_eq_join]

end GlobalTheory.HSChoice.EtaleSection
