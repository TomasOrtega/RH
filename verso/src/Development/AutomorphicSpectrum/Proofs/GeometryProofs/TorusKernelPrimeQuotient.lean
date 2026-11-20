import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharValMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompactCentralizerTranslate
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsSurjectiveZmodOfNeZero

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TsField

/- English proof (translation)
Use `haveI hcl : IsClosedImmersion (equalizer.ι f g).left := isClosedImmersion_equalizer_ι_left _ _`. Take `⟨I, e, he⟩` from `IsClosedImmersion.Spec_iff.1 hcl`. Establish `hcond : (equalizer.ι f g).left ≫ f.left = (equalizer.ι f g).left ≫ g.left`. Rewrite using `[← Over.comp_left, ← Over.comp_left, equalizer.condition]`. Use `⟨I, fun A _ ρ => ⟨fun h => ?_, fun h => ?_⟩⟩` and prove the remaining obligations.

Set `i : Over.mk (spMap ρ ≫ c) ⟶ Over.mk c` to `Over.homMk (spMap ρ)`. Establish `hi : i ≫ f = i ≫ g` using `by ext1`. Conclude with `h`. Set `l` to `equalizer.lift i hi`. Establish `h1 : spMap ρ = l.left ≫ (equalizer.ι f g).left`.

Rewrite using `[← Over.comp_left, equalizer.lift_ι]`. Both sides reduce to the same expression. Rewrite `h1` using `[he]`. Set `σ` to `Spec.preimage (l.left ≫ e.hom)`. Establish `h2 : spMap ρ = Spec.map σ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`.

Rewrite using `[Spec.map_preimage, Category.assoc]`. Conclude with `h1`. Rewrite `h2` using `[← Spec.map_comp]`. Establish `h3` using `Spec.map_injective h2`. Introduce `x hx`.

Establish `h4 : ρ x = σ.hom (Ideal.Quotient.mk I x)`. Use `congrArg (fun q => q.hom x) h3` as an intermediate fact. Simplify using `using this`. Rewrite using `[RingHom.mem_ker, h4, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]`. Set `q : (R ⧸ I) →+* A` to `Ideal.Quotient.lift I ρ (fun a ha => h ha)`.

Establish `hq : CommRingCat.ofHom ρ = CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ CommRingCat.ofHom q`. Use extensionality with `x`. Conclude with `(Ideal.Quotient.lift_mk I ρ (fun a ha => h ha)).symm`. Establish `h1 : spMap ρ = (spMap q ≫ e.inv) ≫ (equalizer.ι f g).left`. Rewrite using `[he, Category.assoc, Iso.inv_hom_id_assoc, spMap, hq, Spec.map_comp]`.

Rewrite using `[h1]`. Simplify using `only [Category.assoc, hcond]`.
-/
theorem exists_ideal_eq_iff {S : Scheme.{0}} {Y : Over S} [IsSeparated Y.hom] {R : Type} [CommRing R]
    {c : Sp R ⟶ S} (f g : Over.mk c ⟶ Y) :
    ∃ J : Ideal R, ∀ (A : Type) [CommRing A] (ρ : R →+* A),
      spMap ρ ≫ f.left = spMap ρ ≫ g.left ↔ J ≤ RingHom.ker ρ := by
  haveI hcl : IsClosedImmersion (equalizer.ι f g).left := isClosedImmersion_equalizer_ι_left _ _
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.1 hcl
  have hcond : (equalizer.ι f g).left ≫ f.left = (equalizer.ι f g).left ≫ g.left := by
    rw [← Over.comp_left, ← Over.comp_left, equalizer.condition]
  refine ⟨I, fun A _ ρ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · let i : Over.mk (spMap ρ ≫ c) ⟶ Over.mk c := Over.homMk (spMap ρ)
    have hi : i ≫ f = i ≫ g := by
      ext1
      exact h
    let l := equalizer.lift i hi
    have h1 : spMap ρ = l.left ≫ (equalizer.ι f g).left := by
      rw [← Over.comp_left, equalizer.lift_ι]; rfl
    rw [he] at h1
    let σ := Spec.preimage (l.left ≫ e.hom)
    have h2 : spMap ρ = Spec.map σ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
      rw [Spec.map_preimage, Category.assoc]
      exact h1
    rw [← Spec.map_comp] at h2
    have h3 := Spec.map_injective h2
    intro x hx
    have h4 : ρ x = σ.hom (Ideal.Quotient.mk I x) := by
      have := congrArg (fun q => q.hom x) h3
      simpa using this
    rw [RingHom.mem_ker, h4, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  · let q : (R ⧸ I) →+* A := Ideal.Quotient.lift I ρ (fun a ha => h ha)
    have hq : CommRingCat.ofHom ρ =
        CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ CommRingCat.ofHom q := by
      ext x
      exact (Ideal.Quotient.lift_mk I ρ (fun a ha => h ha)).symm
    have h1 : spMap ρ = (spMap q ≫ e.inv) ≫ (equalizer.ι f g).left := by
      rw [he, Category.assoc, Iso.inv_hom_id_assoc, spMap, hq, Spec.map_comp]
    rw [h1]
    simp only [Category.assoc, hcond]

open AddMonoidAlgebra in

/- English proof (translation)
Use `haveI : (J.restrictScalars k).IsCoideal := ⟨fun x hx => h1 x hx, fun x hx => h2 x hx⟩`. Use `haveI : Nontrivial (AddMonoidAlgebra k X ⧸ J) := by`. Use `Ideal.Quotient.nontrivial_iff.2 fun h => ?_` and prove the remaining obligations. Use `h1 1 (h ▸ Submodule.mem_top)` as an intermediate fact. Simplify using `at this`.

Take `⟨Y, hY⟩` from `GlobalTheory.CompanionTheory.CommAlg.ker_eq_span_single_sub_one k X (AddMonoidAlgebra k X ⧸ J) (Bialgebra.Quotient.mkBialgHom (R := k) J) Ideal.Quotient.mk_surjective`. Use `⟨Y, ?_⟩` and prove the remaining obligations. Rewrite using `[← hY]`. Conclude with `(Ideal.mk_ker).symm`.
-/
theorem exists_span_of_coideal (k X : Type) [Field k] [AddCommGroup X] (J : Ideal (AddMonoidAlgebra k X))
    (h1 : ∀ f ∈ J, Coalgebra.counit (R := k) f = 0)
    (h2 : ∀ f ∈ J, TensorProduct.map (J.restrictScalars k).mkQ (J.restrictScalars k).mkQ
      (Coalgebra.comul (R := k) f) = 0) :
    ∃ Y : AddSubgroup X, J = Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} := by
  haveI : (J.restrictScalars k).IsCoideal := ⟨fun x hx => h1 x hx, fun x hx => h2 x hx⟩
  haveI : Nontrivial (AddMonoidAlgebra k X ⧸ J) := by
    refine Ideal.Quotient.nontrivial_iff.2 fun h => ?_
    have := h1 1 (h ▸ Submodule.mem_top)
    simp at this
  obtain ⟨Y, hY⟩ := GlobalTheory.CompanionTheory.CommAlg.ker_eq_span_single_sub_one k X (AddMonoidAlgebra k X ⧸ J)
    (Bialgebra.Quotient.mkBialgHom (R := k) J) Ideal.Quotient.mk_surjective
  refine ⟨Y, ?_⟩
  rw [← hY]
  exact (Ideal.mk_ker).symm

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]
  {k : Type} [Field k]

/- English proof (translation)
Take `⟨h0, hadd⟩` from `(GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.1 t`. Use `letI : Algebra k A := g.toAlgebra`. Set `w : Multiplicative X →* A` to `{ toFun := fun x => charVal t x.toAdd map_one' := h0 map_mul' := fun x y => hadd x.toAdd y.toAdd }`. Use `⟨(AddMonoidAlgebra.lift k A X w : AddMonoidAlgebra k X →ₐ[k] A).toRingHom, ?_, fun χ => ?_⟩` and prove the remaining obligations. Use extensionality with `c`.

Conclude with `(AddMonoidAlgebra.lift k A X w).commutes c`. Simplify using `[w]`.
-/
theorem exists_ringHom_of_point {A : Type} [CommRing A] (g : k →+* A) {a : Sp A ⟶ S}
    (t : Over.mk a ⟶ splitTorus S X) :
    ∃ ρ : AddMonoidAlgebra k X →+* A, ρ.comp (algebraMap k (AddMonoidAlgebra k X)) = g ∧
      ∀ χ, ρ (AddMonoidAlgebra.single χ 1) = charVal t χ := by
  obtain ⟨h0, hadd⟩ := (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.1 t
  letI : Algebra k A := g.toAlgebra
  let w : Multiplicative X →* A :=
    { toFun := fun x => charVal t x.toAdd
      map_one' := h0
      map_mul' := fun x y => hadd x.toAdd y.toAdd }
  refine ⟨(AddMonoidAlgebra.lift k A X w : AddMonoidAlgebra k X →ₐ[k] A).toRingHom, ?_, fun χ => ?_⟩
  · ext c
    exact (AddMonoidAlgebra.lift k A X w).commutes c
  · simp [w]

/- English proof (translation)
Take `⟨t, ht⟩` from `(GlobalTheory.T.charVal_multiplicative S X (AddMonoidAlgebra k X) (spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b)).2.2.2.2.1 (AddMonoidAlgebra.of k X)`. Conclude with `⟨t, fun χ => by simpa using ht χ⟩`.
-/
theorem exists_universal_point (b : Sp k ⟶ S) :
    ∃ t₀ : Over.mk (spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b) ⟶ splitTorus S X,
      ∀ χ, charVal t₀ χ = AddMonoidAlgebra.single χ 1 := by
  obtain ⟨t, ht⟩ := (GlobalTheory.T.charVal_multiplicative S X (AddMonoidAlgebra k X)
    (spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b)).2.2.2.2.1 (AddMonoidAlgebra.of k X)
  exact ⟨t, fun χ => by simpa using ht χ⟩

/- English proof (translation)
Rewrite using `[← Category.assoc, spMap, spMap, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp_base {K A : Type} [CommRing K] [CommRing A] (g₀ : k →+* K) (ρ : K →+* A) (b : Sp k ⟶ S) :
    spMap ρ ≫ spMap g₀ ≫ b = spMap (ρ.comp g₀) ≫ b := by
  rw [← Category.assoc, spMap, spMap, spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
Take `⟨t₀, ht₀⟩` from `exists_universal_point (X := X) b`. Take `⟨J, hJ⟩` from `exists_ideal_eq_iff (t₀ ≫ u) (1 : _ ⟶ G)`. Use `⟨J, fun A _ ρ a ha t ht => ?_⟩` and prove the remaining obligations. Rewrite `ha` using `[← spMap_comp_base]`. Substitute `ha` using the available equality.

Rewrite using `[← hJ A ρ]`. Set `h : Over.mk (spMap ρ ≫ spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b) ⟶ Over.mk (spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b)` to `Over.homMk (spMap ρ)`. Establish `e : t = h ≫ t₀`. Use `(GlobalTheory.T.charVal_multiplicative S X A _).1 _ _ fun χ => ?_` and prove the remaining obligations. Rewrite using `[ht, (GlobalTheory.T.charVal_multiplicative S X _ _).2.2.2.2.2 A ρ t₀ (h ≫ t₀) rfl χ, ht₀]`.

Establish `e1 : (1 : Over.mk (spMap ρ ≫ spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b) ⟶ G) = h ≫ 1` using `(MonObj.comp_one h).symm`. Rewrite using `[e, Category.assoc, e1]`. Prove the components needed by the constructor for the conclusion. Introduce `h'`. Conclude with `congrArg (fun q => q.left) h'`.

Introduce `h' ext1`. Conclude with `h'`.
-/
theorem exists_killing_ideal [IsSeparated G.hom] (u : splitTorus S X ⟶ G) [IsMonHom u] (b : Sp k ⟶ S) :
    ∃ J : Ideal (AddMonoidAlgebra k X), ∀ (A : Type) [CommRing A] (ρ : AddMonoidAlgebra k X →+* A)
      (a : Sp A ⟶ S), a = spMap (ρ.comp (algebraMap k (AddMonoidAlgebra k X))) ≫ b →
      ∀ t : Over.mk a ⟶ splitTorus S X, (∀ χ, charVal t χ = ρ (AddMonoidAlgebra.single χ 1)) →
        (t ≫ u = 1 ↔ J ≤ RingHom.ker ρ) := by
  obtain ⟨t₀, ht₀⟩ := exists_universal_point (X := X) b
  obtain ⟨J, hJ⟩ := exists_ideal_eq_iff (t₀ ≫ u) (1 : _ ⟶ G)
  refine ⟨J, fun A _ ρ a ha t ht => ?_⟩
  rw [← spMap_comp_base] at ha
  subst ha
  rw [← hJ A ρ]
  let h : Over.mk (spMap ρ ≫ spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b) ⟶
      Over.mk (spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b) := Over.homMk (spMap ρ)
  have e : t = h ≫ t₀ := by
    refine (GlobalTheory.T.charVal_multiplicative S X A _).1 _ _ fun χ => ?_
    rw [ht, (GlobalTheory.T.charVal_multiplicative S X _ _).2.2.2.2.2 A ρ t₀ (h ≫ t₀) rfl χ, ht₀]
  have e1 : (1 : Over.mk (spMap ρ ≫ spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b) ⟶ G) = h ≫ 1 :=
    (MonObj.comp_one h).symm
  rw [e, Category.assoc, e1]
  constructor
  · intro h'
    exact congrArg (fun q => q.left) h'
  · intro h'
    ext1
    exact h'

open TensorProduct in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Set `ε : AddMonoidAlgebra k X →ₐ[k] k` to `Bialgebra.counitAlgHom k (AddMonoidAlgebra k X)`. Establish `hε : (ε : AddMonoidAlgebra k X →+* k).comp (algebraMap k (AddMonoidAlgebra k X)) = RingHom.id k`. Use extensionality with `c`. Conclude with `ε.commutes c`.

Establish `hb : b = spMap ((ε : AddMonoidAlgebra k X →+* k).comp (algebraMap k (AddMonoidAlgebra k X))) ≫ b`. Rewrite using `[hε]`. Express the relevant statement in the definitionally equal form `b = Spec.map (𝟙 _) ≫ b`. Rewrite using `[Spec.map_id, Category.id_comp]`. Establish `hk` using `(hJ k (ε : AddMonoidAlgebra k X →+* k) b hb (1 : Over.mk b ⟶ splitTorus S X) ?_).1 (MonObj.one_comp u)`.

Introduce `f hf`. Conclude with `hk hf`. Introduce `χ`. Rewrite using `[(GlobalTheory.T.charVal_multiplicative S X k b).2.2.1 χ]`. Simplify using `[ε]`.

Set `Q` to `AddMonoidAlgebra k X ⧸ J`. Set `mkQ : AddMonoidAlgebra k X →ₐ[k] Q` to `Ideal.Quotient.mkₐ k J`. Set `c : AddMonoidAlgebra k X →ₐ[k] Q ⊗[k] Q` to `(Algebra.TensorProduct.map mkQ mkQ).comp (Bialgebra.comulAlgHom k (AddMonoidAlgebra k X))`. Set `i₁ : AddMonoidAlgebra k X →ₐ[k] Q ⊗[k] Q` to `Algebra.TensorProduct.includeLeft.comp mkQ`. Set `i₂ : AddMonoidAlgebra k X →ₐ[k] Q ⊗[k] Q` to `Algebra.TensorProduct.includeRight.comp mkQ`.

Set `A` to `Q ⊗[k] Q`. Set `a : Sp A ⟶ S` to `spMap (algebraMap k A) ≫ b`. Establish `hcomp : ∀ φ : AddMonoidAlgebra k X →ₐ[k] A, a = spMap ((φ : AddMonoidAlgebra k X →+* A).comp (algebraMap k (AddMonoidAlgebra k X))) ≫ b`. Introduce `φ`. Rewrite using `[φ.comp_algebraMap]`.

Establish `hpt : ∀ φ : AddMonoidAlgebra k X →ₐ[k] A, ∃ t : Over.mk a ⟶ splitTorus S X, ∀ χ, charVal t χ = φ (AddMonoidAlgebra.single χ 1)`. Introduce `φ`. Take `⟨t, ht⟩` from `(GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.1 (((φ : AddMonoidAlgebra k X →+* A) : AddMonoidAlgebra k X →* A).comp (AddMonoidAlgebra.of k X))`. Conclude with `⟨t, fun χ => by simpa using ht χ⟩`. Take `⟨t₁, ht₁⟩` from `hpt i₁`.

Take `⟨t₂, ht₂⟩` from `hpt i₂`. Establish `k₁ : t₁ ≫ u = 1` using `(hJ A (i₁ : AddMonoidAlgebra k X →+* A) a (hcomp i₁) t₁ ht₁).2 fun f hf => by`. Establish `: mkQ f = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 hf`. Simplify using `[RingHom.mem_ker, i₁, this]`. Establish `k₂ : t₂ ≫ u = 1` using `(hJ A (i₂ : AddMonoidAlgebra k X →+* A) a (hcomp i₂) t₂ ht₂).2 fun f hf => by`.

Establish `: mkQ f = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 hf`. Simplify using `[RingHom.mem_ker, i₂, this]`. Establish `hc : ∀ χ, charVal (t₁ * t₂) χ = (c : AddMonoidAlgebra k X →+* A) (AddMonoidAlgebra.single χ 1)`. Introduce `χ`. Rewrite using `[(GlobalTheory.T.charVal_multiplicative S X A a).2.1 t₁ t₂ χ, ht₁, ht₂]`.

Establish `e : (c : AddMonoidAlgebra k X →+* A) (AddMonoidAlgebra.single χ 1) = mkQ (AddMonoidAlgebra.single χ 1) ⊗ₜ mkQ (AddMonoidAlgebra.single χ 1)`. Simplify using `[c, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply]`. Rewrite using `[e]`. Express the relevant statement in the definitionally equal form `(mkQ (AddMonoidAlgebra.single χ 1) ⊗ₜ[k] (1 : Q)) * ((1 : Q) ⊗ₜ[k] mkQ (AddMonoidAlgebra.single χ 1)) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]`.

Establish `hk` using `(hJ A (c : AddMonoidAlgebra k X →+* A) a (hcomp c) (t₁ * t₂) hc).1 (by rw [MonObj.mul_comp, k₁, k₂, _root_.mul_one])`. Introduce `f hf`. Conclude with `hk hf`.
-/
theorem killing_ideal_coideal (b : Sp k ⟶ S) (u : splitTorus S X ⟶ G) [IsMonHom u]
    (J : Ideal (AddMonoidAlgebra k X))
    (hJ : ∀ (A : Type) [CommRing A] (ρ : AddMonoidAlgebra k X →+* A)
      (a : Sp A ⟶ S), a = spMap (ρ.comp (algebraMap k (AddMonoidAlgebra k X))) ≫ b →
      ∀ t : Over.mk a ⟶ splitTorus S X, (∀ χ, charVal t χ = ρ (AddMonoidAlgebra.single χ 1)) →
        (t ≫ u = 1 ↔ J ≤ RingHom.ker ρ)) :
    (∀ f ∈ J, Coalgebra.counit (R := k) f = 0) ∧
    (∀ f ∈ J, TensorProduct.map (J.restrictScalars k).mkQ (J.restrictScalars k).mkQ
      (Coalgebra.comul (R := k) f) = 0) := by
  constructor
  · let ε : AddMonoidAlgebra k X →ₐ[k] k := Bialgebra.counitAlgHom k (AddMonoidAlgebra k X)
    have hε : (ε : AddMonoidAlgebra k X →+* k).comp (algebraMap k (AddMonoidAlgebra k X)) = RingHom.id k := by
      ext c
      exact ε.commutes c
    have hb : b = spMap ((ε : AddMonoidAlgebra k X →+* k).comp (algebraMap k (AddMonoidAlgebra k X))) ≫ b := by
      rw [hε]
      change b = Spec.map (𝟙 _) ≫ b
      rw [Spec.map_id, Category.id_comp]
    have hk := (hJ k (ε : AddMonoidAlgebra k X →+* k) b hb (1 : Over.mk b ⟶ splitTorus S X) ?_).1 (MonObj.one_comp u)
    · intro f hf
      exact hk hf
    · intro χ
      rw [(GlobalTheory.T.charVal_multiplicative S X k b).2.2.1 χ]
      simp [ε]
  · let Q := AddMonoidAlgebra k X ⧸ J
    let mkQ : AddMonoidAlgebra k X →ₐ[k] Q := Ideal.Quotient.mkₐ k J
    let c : AddMonoidAlgebra k X →ₐ[k] Q ⊗[k] Q :=
      (Algebra.TensorProduct.map mkQ mkQ).comp (Bialgebra.comulAlgHom k (AddMonoidAlgebra k X))
    let i₁ : AddMonoidAlgebra k X →ₐ[k] Q ⊗[k] Q := Algebra.TensorProduct.includeLeft.comp mkQ
    let i₂ : AddMonoidAlgebra k X →ₐ[k] Q ⊗[k] Q := Algebra.TensorProduct.includeRight.comp mkQ
    let A := Q ⊗[k] Q
    let a : Sp A ⟶ S := spMap (algebraMap k A) ≫ b
    have hcomp : ∀ φ : AddMonoidAlgebra k X →ₐ[k] A,
        a = spMap ((φ : AddMonoidAlgebra k X →+* A).comp (algebraMap k (AddMonoidAlgebra k X))) ≫ b := by
      intro φ
      rw [φ.comp_algebraMap]
    have hpt : ∀ φ : AddMonoidAlgebra k X →ₐ[k] A, ∃ t : Over.mk a ⟶ splitTorus S X,
        ∀ χ, charVal t χ = φ (AddMonoidAlgebra.single χ 1) := by
      intro φ
      obtain ⟨t, ht⟩ := (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.1
        (((φ : AddMonoidAlgebra k X →+* A) : AddMonoidAlgebra k X →* A).comp (AddMonoidAlgebra.of k X))
      exact ⟨t, fun χ => by simpa using ht χ⟩
    obtain ⟨t₁, ht₁⟩ := hpt i₁
    obtain ⟨t₂, ht₂⟩ := hpt i₂
    have k₁ : t₁ ≫ u = 1 := (hJ A (i₁ : AddMonoidAlgebra k X →+* A) a (hcomp i₁) t₁ ht₁).2 fun f hf => by
      have : mkQ f = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hf
      simp [RingHom.mem_ker, i₁, this]
    have k₂ : t₂ ≫ u = 1 := (hJ A (i₂ : AddMonoidAlgebra k X →+* A) a (hcomp i₂) t₂ ht₂).2 fun f hf => by
      have : mkQ f = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hf
      simp [RingHom.mem_ker, i₂, this]
    have hc : ∀ χ, charVal (t₁ * t₂) χ = (c : AddMonoidAlgebra k X →+* A) (AddMonoidAlgebra.single χ 1) := by
      intro χ
      rw [(GlobalTheory.T.charVal_multiplicative S X A a).2.1 t₁ t₂ χ, ht₁, ht₂]
      have e : (c : AddMonoidAlgebra k X →+* A) (AddMonoidAlgebra.single χ 1) = mkQ (AddMonoidAlgebra.single χ 1) ⊗ₜ mkQ (AddMonoidAlgebra.single χ 1) := by
        simp [c, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply]
      rw [e]
      change (mkQ (AddMonoidAlgebra.single χ 1) ⊗ₜ[k] (1 : Q)) * ((1 : Q) ⊗ₜ[k] mkQ (AddMonoidAlgebra.single χ 1)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    have hk := (hJ A (c : AddMonoidAlgebra k X →+* A) a (hcomp c) (t₁ * t₂) hc).1
      (by rw [MonObj.mul_comp, k₁, k₂, _root_.mul_one])
    intro f hf
    exact hk hf

/- English proof (translation)
Introduce `S G _ _ X _ _ u _ k _ b M hM δ hδ hu`. Take `⟨J, hJ⟩` from `exists_killing_ideal (k := k) u b`. Take `⟨h1, h2⟩` from `killing_ideal_coideal b u J hJ`. Take `⟨Y, hY⟩` from `exists_span_of_coideal k X J h1 h2`. Establish `hmain : ∀ (A : Type) [CommRing A] (g : k →+* A) (a : Sp A ⟶ S), a = spMap g ≫ b → ∀ t : Over.mk a ⟶ splitTorus S X, (t ≫ u = 1 ↔ ∀ y ∈ Y, charVal t y = 1)`.

Introduce `A _ g a ha t`. Take `⟨ρ, hρ, hv⟩` from `exists_ringHom_of_point (k := k) g t`. Rewrite using `[hJ A ρ a (by rw [hρ, ha]) t (fun χ => (hv χ).symm), hY, Ideal.span_le]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`.

Establish `h0 : ρ (AddMonoidAlgebra.single y 1 - 1) = 0` using `h ⟨y, hy, rfl⟩`. Rewrite `h0` using `[map_sub, map_one, hv, sub_eq_zero]`. Then use the resulting hypothesis. Introduce and unpack `h _ ⟨y, hy, rfl⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hv, h y hy, sub_self]`. Establish `hδY : ∀ y ∈ Y, δ y = 0`.

Introduce `y hy`. Establish `h0` using `(hmain (DualNumber k) (algebraMap k (DualNumber k)) _ rfl (M.pt δ)).1 hu y hy`. Rewrite `h0` using `[hM δ y]`. Simplify using `using congrArg TrivSqZeroExt.snd h0`. Take `⟨l, hl, ψ, hs, hψ⟩` from `GlobalTheory.CompanionTheory.QuotPrime.exists_surjective_zmod_of_ne_zero k X Y δ hδ hδY`.

Conclude with `⟨l, hl, ψ, hs, fun A _ g t ht => (hmain A g _ rfl t).2 fun y hy => ht y (hψ y hy)⟩`.
-/
theorem exists_mu_killed : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X]
    [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (b : Sp k ⟶ S)
    (M : LieModel (splitTorus S X) b (X →+ k)), IsCocharLie M → ∀ δ : X →+ k, δ ≠ 0 → M.pt δ ≫ u = 1 →
    ∃ (l : ℕ) (_ : l.Prime) (ψ : X →+ ZMod l), Function.Surjective ψ ∧ KillsOver u ψ.ker b := by
  intro S G _ _ X _ _ u _ k _ b M hM δ hδ hu
  obtain ⟨J, hJ⟩ := exists_killing_ideal (k := k) u b
  obtain ⟨h1, h2⟩ := killing_ideal_coideal b u J hJ
  obtain ⟨Y, hY⟩ := exists_span_of_coideal k X J h1 h2
  have hmain : ∀ (A : Type) [CommRing A] (g : k →+* A) (a : Sp A ⟶ S), a = spMap g ≫ b →
      ∀ t : Over.mk a ⟶ splitTorus S X, (t ≫ u = 1 ↔ ∀ y ∈ Y, charVal t y = 1) := by
    intro A _ g a ha t
    obtain ⟨ρ, hρ, hv⟩ := exists_ringHom_of_point (k := k) g t
    rw [hJ A ρ a (by rw [hρ, ha]) t (fun χ => (hv χ).symm), hY, Ideal.span_le]
    constructor
    · intro h y hy
      have h0 : ρ (AddMonoidAlgebra.single y 1 - 1) = 0 := h ⟨y, hy, rfl⟩
      rwa [map_sub, map_one, hv, sub_eq_zero] at h0
    · rintro h _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hv, h y hy, sub_self]
  have hδY : ∀ y ∈ Y, δ y = 0 := by
    intro y hy
    have h0 := (hmain (DualNumber k) (algebraMap k (DualNumber k)) _ rfl (M.pt δ)).1 hu y hy
    rw [hM δ y] at h0
    simpa using congrArg TrivSqZeroExt.snd h0
  obtain ⟨l, hl, ψ, hs, hψ⟩ := GlobalTheory.CompanionTheory.QuotPrime.exists_surjective_zmod_of_ne_zero k X Y δ hδ hδY
  exact ⟨l, hl, ψ, hs, fun A _ g t ht => (hmain A g _ rfl t).2 fun y hy => ht y (hψ y hy)⟩

end GlobalTheory.CompanionTheory.Ar.TsField
