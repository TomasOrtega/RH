import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtTensorAlt
open IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBaseChangeCons

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor`. Consider the case `exact _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor`. Consider the case `(apply _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor ..)`.
-/
theorem tensor_ringHom_ext {R S B C : Type} [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] (φ ψ : S ⊗[R] B →+* C)
    (h₁ : ∀ s : S, φ (s ⊗ₜ[R] (1 : B)) = ψ (s ⊗ₜ[R] (1 : B)))
    (h₂ : ∀ b : B, φ ((1 : S) ⊗ₜ[R] b) = ψ ((1 : S) ⊗ₜ[R] b)) : φ = ψ := by
  first
  | exact @_root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor
  | exact _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor
  | (apply _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor ..)

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.
-/
theorem one_tmul_algebraMap {R S B : Type} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (r : R) :
    (1 : S) ⊗ₜ[R] algebraMap R B r = algebraMap R S r ⊗ₜ[R] (1 : B) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/- English proof (translation)
The claim follows from `Ideal.mem_span_singleton.mpr X_dvd_sub_C`.
-/
theorem sub_C_coeff_mem {R : Type} [CommRing R] (p : Polynomial R) :
    p - C (p.coeff 0) ∈ Ideal.span {(X : Polynomial R)} :=
  Ideal.mem_span_singleton.mpr X_dvd_sub_C

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hf`. Establish `hle : GlobalTheory.KeyOriginCut.originIdeal R ≤ (maximalIdeal R).comap (constantCoeff (R` using `R)) := by`. Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `a ha`. Simplify `ha` using `[Ideal.mem_comap]`. Rewrite using `[Ideal.span_le]`. Introduce `x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`.

Substitute `hx` using the available equality. Simplify using `[Ideal.mem_comap]`. Simplify `hle hf` using `[Ideal.mem_comap]`. Introduce `hf`. Establish `h1 : C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal R` using `Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)`.

Establish `h2 : f - C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal R` using `Ideal.mem_sup_right (sub_C_coeff_mem f)`. Simplify using `using Ideal.add_mem _ h2 h1`.
-/
theorem mem_originIdeal_iff {R : Type} [CommRing R] [IsLocalRing R] (f : Polynomial R) :
    f ∈ GlobalTheory.KeyOriginCut.originIdeal R ↔ f.coeff 0 ∈ maximalIdeal R := by
  constructor
  · intro hf
    have hle : GlobalTheory.KeyOriginCut.originIdeal R ≤ (maximalIdeal R).comap (constantCoeff (R := R)) := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simpa [Ideal.mem_comap] using ha
      · rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp [Ideal.mem_comap]
    simpa [Ideal.mem_comap] using hle hf
  · intro hf
    have h1 : C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal R :=
      Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)
    have h2 : f - C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal R :=
      Ideal.mem_sup_right (sub_C_coeff_mem f)
    simpa using Ideal.add_mem _ h2 h1

/- English proof (translation)
Use extensionality with `p`. Rewrite using `[Ideal.mem_comap, mem_originIdeal_iff, RingHom.comp_apply, coe_mapRingHom]`. Use `set q := p.map i₁`. Establish `hsplit : algebraMap (Polynomial T) O q = algebraMap (Polynomial T) O (q - C (q.coeff 0)) + algebraMap T O (q.coeff 0)`. Rewrite using `[map_sub, IsScalarTower.algebraMap_apply T (Polynomial T) O, algebraMap_eq]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hX : algebraMap (Polynomial T) O (q - C (q.coeff 0)) ∈ maximalIdeal O`. Take `⟨r, hr⟩` from `(X_dvd_sub_C (p := q))`. Rewrite using `[hr, map_mul]`. Conclude with `Ideal.mul_mem_right _ _ hXO`.

Rewrite using `[hsplit]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : algebraMap T O (q.coeff 0) ∈ maximalIdeal O`. Use `Ideal.sub_mem _ h hX` as an intermediate fact.

Simplify using `using this`. Rewrite `h'` using `[mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal, coeff_map, mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal]`. Conclude with `h'`. Introduce `h`. Use `Ideal.add_mem _ hX ?_` and prove the remaining obligations.

Rewrite using `[mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal, coeff_map, mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal]`. Conclude with `h`.
-/
theorem comap_maximalIdeal_eq_originIdeal {T O A₁ : Type} [CommRing T] [IsLocalRing T] [CommRing O]
    [IsLocalRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    [IsLocalHom (algebraMap T O)] (hXO : algebraMap (Polynomial T) O X ∈ maximalIdeal O)
    [CommRing A₁] [IsLocalRing A₁] (i₁ : A₁ →+* T) [IsLocalHom i₁] :
    (maximalIdeal O).comap ((algebraMap (Polynomial T) O).comp (mapRingHom i₁)) =
      GlobalTheory.KeyOriginCut.originIdeal A₁ := by
  ext p
  rw [Ideal.mem_comap, mem_originIdeal_iff, RingHom.comp_apply, coe_mapRingHom]
  set q := p.map i₁
  have hsplit : algebraMap (Polynomial T) O q =
      algebraMap (Polynomial T) O (q - C (q.coeff 0)) + algebraMap T O (q.coeff 0) := by
    rw [map_sub, IsScalarTower.algebraMap_apply T (Polynomial T) O, algebraMap_eq]; ring
  have hX : algebraMap (Polynomial T) O (q - C (q.coeff 0)) ∈ maximalIdeal O := by
    obtain ⟨r, hr⟩ := (X_dvd_sub_C (p := q))
    rw [hr, map_mul]
    exact Ideal.mul_mem_right _ _ hXO
  rw [hsplit]
  constructor
  · intro h
    have h' : algebraMap T O (q.coeff 0) ∈ maximalIdeal O := by
      have := Ideal.sub_mem _ h hX
      simpa using this
    rw [mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal, coeff_map,
      mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal] at h'
    exact h'
  · intro h
    refine Ideal.add_mem _ hX ?_
    rw [mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal, coeff_map,
      mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal]
    exact h

/- English proof (translation)
Use `haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA`. Use `set L := Localization.AtPrime QA`. Use `set I := RingHom.ker (ρ.comp (algebraMap EA L))`. Use `set N := Ideal.span {algebraMap (Polynomial A) EA X}`. Establish `key : ∀ (J : Ideal EA) (hJ : J.FG), J ≤ I → ∃ s ∉ QA, ∀ e ∈ J, s * e ∈ N`.

Introduce `J hJ`. Proceed by induction on `J, hJ using Submodule.fg_induction with`. Consider the case `singleton x`. Introduce `hx`. Establish `hxI : x ∈ I` using `hx (Submodule.mem_span_singleton_self x)`.

Establish `hk : algebraMap EA L x ∈ RingHom.ker ρ` using `hxI`. Rewrite `hk` using `[hker, Ideal.mem_span_singleton']`. Take `⟨a, ha⟩` from `hk`. Take `⟨⟨y, m⟩, hy⟩` from `IsLocalization.surj QA.primeCompl a`. Establish `he : algebraMap EA L (y * algebraMap (Polynomial A) EA X) = algebraMap EA L (m * x)`.

Rewrite using `[map_mul, map_mul, ← ha, ← IsScalarTower.algebraMap_apply, ← hy]`. Simplify using `only at *`. Expand and normalize the polynomial expressions, which then agree. Take `⟨u, hu⟩` from `(IsLocalization.eq_iff_exists QA.primeCompl L).mp he`. Use `⟨u * m, (u * m).2, ?_⟩` and prove the remaining obligations.

Introduce `e hex`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hex`. Establish `: (u : EA) * (y * algebraMap (Polynomial A) EA X) ∈ N` using `Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))`. Rewrite `this` using `[hu]`. Establish `h2` using `Ideal.mul_mem_left N c this`.

Rewrite using `[smul_eq_mul]`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `sup J₁ J₂ _ _ h₁ h₂`.

Introduce `hle`. Take `⟨s₁, hs₁, H₁⟩` from `h₁ (le_trans le_sup_left hle)`. Take `⟨s₂, hs₂, H₂⟩` from `h₂ (le_trans le_sup_right hle)`. Use `⟨s₁ * s₂, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs₁ hs₂, ?_⟩` and prove the remaining obligations. Introduce `e he`.

Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp he`. Rewrite using `[mul_add]`. Use `N.add_mem ?_ ?_` and prove the remaining obligations. Use `N.mul_mem_left s₂ (H₁ y hy)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Use `N.mul_mem_left s₁ (H₂ z hz)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨s, hs, H⟩` from `key I (IsNoetherian.noetherian I) le_rfl`.

Conclude with `⟨s, hs, fun e he => H e he⟩`.
-/
theorem exists_mul_mem_span_X {A EA : Type} [CommRing A] [IsNoetherianRing A] [CommRing EA]
    [Algebra (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA] (QA : Ideal EA) [QA.IsPrime]
    (ρ : Localization.AtPrime QA →+* A)
    (hker : RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) X}) :
    ∃ s ∉ QA, ∀ e : EA, ρ (algebraMap EA (Localization.AtPrime QA) e) = 0 →
      s * e ∈ Ideal.span {algebraMap (Polynomial A) EA X} := by
  haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA
  set L := Localization.AtPrime QA
  set I := RingHom.ker (ρ.comp (algebraMap EA L))
  set N := Ideal.span {algebraMap (Polynomial A) EA X}
  have key : ∀ (J : Ideal EA) (hJ : J.FG), J ≤ I → ∃ s ∉ QA, ∀ e ∈ J, s * e ∈ N := by
    intro J hJ
    induction J, hJ using Submodule.fg_induction with
    | singleton x =>
      intro hx
      have hxI : x ∈ I := hx (Submodule.mem_span_singleton_self x)
      have hk : algebraMap EA L x ∈ RingHom.ker ρ := hxI
      rw [hker, Ideal.mem_span_singleton'] at hk
      obtain ⟨a, ha⟩ := hk
      obtain ⟨⟨y, m⟩, hy⟩ := IsLocalization.surj QA.primeCompl a
      have he : algebraMap EA L (y * algebraMap (Polynomial A) EA X) =
          algebraMap EA L (m * x) := by
        rw [map_mul, map_mul, ← ha, ← IsScalarTower.algebraMap_apply, ← hy]
        simp only at *
        ring
      obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists QA.primeCompl L).mp he
      refine ⟨u * m, (u * m).2, ?_⟩
      intro e hex
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hex
      have : (u : EA) * (y * algebraMap (Polynomial A) EA X) ∈ N :=
        Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
      rw [hu] at this
      have h2 := Ideal.mul_mem_left N c this
      rw [smul_eq_mul]
      convert h2 using 1
      push_cast
      ring
    | sup J₁ J₂ _ _ h₁ h₂ =>
      intro hle
      obtain ⟨s₁, hs₁, H₁⟩ := h₁ (le_trans le_sup_left hle)
      obtain ⟨s₂, hs₂, H₂⟩ := h₂ (le_trans le_sup_right hle)
      refine ⟨s₁ * s₂, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs₁ hs₂, ?_⟩
      intro e he
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp he
      rw [mul_add]
      refine N.add_mem ?_ ?_
      · have := N.mul_mem_left s₂ (H₁ y hy)
        convert this using 1; ring
      · have := N.mul_mem_left s₁ (H₂ z hz)
        convert this using 1; ring
  obtain ⟨s, hs, H⟩ := key I (IsNoetherian.noetherian I) le_rfl
  exact ⟨s, hs, fun e he => H e he⟩

end GlobalTheory.KeyOriginBaseChangeCons

namespace GlobalTheory.KeyOriginBaseChangeCons

/- English proof (translation)
Introduce `T O _ _ _ _ _ _ _ _ hTO hXO A _ _ _ _ i EA _ _ _ _ _ QA _ jA ρ hQA hjA hρ A₁ _ _ _ j i₁ hi₁ hloc hij`. Use `haveI := hTO`. Use `haveI := hloc`. Use `letI algP : Algebra (Polynomial A) (Polynomial A₁) := (mapRingHom j).toAlgebra`. Use `letI algO : Algebra (Polynomial A) O := ((algebraMap (Polynomial T) O).comp (mapRingHom i)).toAlgebra`.

Use `set L := Localization.AtPrime QA with hL`. Establish `hρpoly : ρ.comp (algebraMap (Polynomial A) L) = evalRingHom 0`. Use `Polynomial.ringHom_ext (fun a => ?_) ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, ← algebraMap_eq (R := A), ← IsScalarTower.algebraMap_apply, ← RingHom.comp_apply ρ, hρ.1, algebraMap_eq]`. Simplify using the standard rewrite rules.

Establish `hx : algebraMap (Polynomial A) L X ∈ RingHom.ker ρ`. Rewrite using `[hρ.2.1]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite using `[RingHom.comp_apply, RingHom.mem_ker.mp hx]`. Simplify using the standard rewrite rules.

Set `f₁ : Polynomial A₁ →ₐ[Polynomial A] O` to `{ toRingHom := (algebraMap (Polynomial T) O).comp (mapRingHom i₁) commutes' := fun r => by show algebraMap (Polynomial T) O (mapRingHom i₁ (mapRingHom j r)) = algebraMap (Polynomial T) O (mapRingHom i r)`. Rewrite using `[coe_mapRingHom, coe_mapRingHom, coe_mapRingHom, Polynomial.map_map, hij] }`. Set `f₂ : EA →ₐ[Polynomial A] O` to `{ toRingHom := jA.comp (algebraMap EA L) commutes' := fun r => by show jA (algebraMap EA L (algebraMap (Polynomial A) EA r)) = algebraMap (Polynomial T) O (mapRingHom i r)`. Rewrite using `[← IsScalarTower.algebraMap_apply (Polynomial A) EA L r]`. Conclude with `congrArg (fun φ => φ r) hjA }`.

Set `EA₁` to `TensorProduct (Polynomial A) (Polynomial A₁) EA`. Set `g : EA₁ →+* O` to `(Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => Commute.all _ _)).toRingHom`. Establish `hg : ∀ p e, g (p ⊗ₜ[Polynomial A] e) = algebraMap (Polynomial T) O (p.map i₁) * jA (algebraMap EA L e)` using `fun p e => Algebra.TensorProduct.lift_tmul _ _ _ p e`. Use `letI iA1 : Algebra A₁ EA₁ := ((algebraMap (Polynomial A₁) EA₁).comp C).toAlgebra`. Establish `hmapP : ∀ p : Polynomial A₁, algebraMap (Polynomial A₁) EA₁ p = p ⊗ₜ[Polynomial A] (1 : EA)`.

Introduce `p`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply]`. Both sides reduce to the same expression. Establish `hAP : ∀ a : A₁, algebraMap A₁ EA₁ a = algebraMap (Polynomial A₁) EA₁ (C a)` using `fun a => rfl`. Establish `hmapA : ∀ a : A₁, algebraMap A₁ EA₁ a = C a ⊗ₜ[Polynomial A] (1 : EA)` using `fun a => hmapP (C a)`.

Set `γ₀ : EA →+* EA₁` to `(Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] EA₁).toRingHom`. Establish `hγ₀ : ∀ e, γ₀ e = (1 : Polynomial A₁) ⊗ₜ[Polynomial A] e` using `fun e => rfl`. Establish `hγ₀A : ∀ a : A, γ₀ (algebraMap A EA a) = algebraMap A₁ EA₁ (j a)`. Introduce `a`. Rewrite using `[hγ₀, hmapA, IsScalarTower.algebraMap_apply A (Polynomial A) EA, one_tmul_algebraMap, algebraMap_eq]`.

Use `show (mapRingHom j (C a)) ⊗ₜ[Polynomial A] (1 : EA) = _`. Rewrite using `[coe_mapRingHom, Polynomial.map_C]`. Establish `hγ₀X : γ₀ (algebraMap (Polynomial A) EA X) = algebraMap (Polynomial A₁) EA₁ X`. Rewrite using `[hγ₀, hmapP, one_tmul_algebraMap]`. Use `show (mapRingHom j X) ⊗ₜ[Polynomial A] (1 : EA) = _`.

Rewrite using `[coe_mapRingHom, Polynomial.map_X]`. Establish `hgP : ∀ p, g (algebraMap (Polynomial A₁) EA₁ p) = algebraMap (Polynomial T) O (p.map i₁)`. Introduce `p`. Rewrite using `[hmapP, hg, map_one, map_one, mul_one]`. Establish `hgγ : ∀ e, g (γ₀ e) = jA (algebraMap EA L e)`.

Introduce `e`. Rewrite using `[hγ₀, hg, Polynomial.map_one, map_one, one_mul]`. Set `QA₁ : Ideal EA₁` to `(maximalIdeal O).comap g`. Establish `hunit : ∀ y : EA₁, y ∉ QA₁ → IsUnit (g y)`. Introduce `y hy`.

Assume the negation of the conclusion as `h`. Conclude with `hy ((mem_maximalIdeal _).2 h)`. Set `L₁` to `Localization.AtPrime QA₁`. Set `jA₁ : L₁ →+* O` to `IsLocalization.lift (M := QA₁.primeCompl) (g := g) (fun y => hunit y y.2)`. Establish `hjA₁ : ∀ x, jA₁ (algebraMap EA₁ L₁ x) = g x` using `fun x => IsLocalization.lift_eq _ x`.

Establish `hγ₀Q : ∀ e : EA, e ∉ QA → γ₀ e ∉ QA₁`. Introduce `e he h`. Establish `h1 : g (γ₀ e) ∈ maximalIdeal O` using `h`. Rewrite `h1` using `[hgγ]`. Establish `hu : IsUnit (algebraMap EA L e)` using `IsLocalization.map_units L (⟨e, he⟩ : QA.primeCompl)`.

Conclude with `(mem_maximalIdeal _).1 h1 (hu.map jA)`. Set `γ : L →+* L₁` to `IsLocalization.lift (M := QA.primeCompl) (g := (algebraMap EA₁ L₁).comp γ₀) (fun y => IsLocalization.map_units L₁ (⟨γ₀ y, hγ₀Q y y.2⟩ : QA₁.primeCompl))`. Establish `hγ : ∀ e, γ (algebraMap EA L e) = algebraMap EA₁ L₁ (γ₀ e)` using `fun e => IsLocalization.lift_eq _ e`. Establish `hρA : ∀ b : A, ρ (algebraMap EA L (algebraMap A EA b)) = b`. Introduce `b`.

Rewrite using `[← IsScalarTower.algebraMap_apply A EA L b]`. Conclude with `congrArg (fun φ => φ b) hρ.1`. Set `Xs : Ideal (Polynomial A₁)` to `Ideal.span {X}`. Set `φ0 : Polynomial A₁ ⧸ Xs →+* A₁` to `Ideal.Quotient.lift Xs (evalRingHom 0) (fun a ha => by`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`.

Use the proof step `simp)`. Establish `hφ0 : ∀ p, φ0 (Ideal.Quotient.mk Xs p) = eval 0 p` using `fun p => Ideal.Quotient.lift_mk _ _ _`. Set `r₁ : Polynomial A₁ →ₐ[Polynomial A] Polynomial A₁ ⧸ Xs` to `Ideal.Quotient.mkₐ (Polynomial A) Xs`. Set `r₂ : EA →ₐ[Polynomial A] Polynomial A₁ ⧸ Xs` to `{ toRingHom := (Ideal.Quotient.mk Xs).comp (C.comp (j.comp (ρ.comp (algebraMap EA L)))) commutes' := fun r => by show Ideal.Quotient.mk Xs (C (j (ρ (algebraMap EA L (algebraMap (Polynomial A) EA r))))) = Ideal.Quotient.mk Xs (mapRingHom j r)`. Rewrite using `[← IsScalarTower.algebraMap_apply (Polynomial A) EA L r, ← RingHom.comp_apply ρ, hρpoly, Ideal.Quotient.eq, coe_mapRingHom, coe_evalRingHom, ← coeff_zero_eq_eval_zero]`.

Establish `: C (j (r.coeff 0)) - r.map j = -((r.map j) - C ((r.map j).coeff 0))`. Rewrite using `[coeff_map]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Xs.neg_mem (sub_C_coeff_mem _) }`.

Set `ρ' : EA₁ →+* A₁` to `φ0.comp (Algebra.TensorProduct.lift r₁ r₂ (fun _ _ => Commute.all _ _)).toRingHom`. Establish `hρ' : ∀ p e, ρ' (p ⊗ₜ[Polynomial A] e) = eval 0 p * j (ρ (algebraMap EA L e))`. Introduce `p e`. Use `show φ0 (Algebra.TensorProduct.lift r₁ r₂ (fun _ _ => Commute.all _ _) (p ⊗ₜ[Polynomial A] e)) = _`. Rewrite using `[Algebra.TensorProduct.lift_tmul, map_mul]`.

Use `show φ0 (Ideal.Quotient.mk Xs p) * φ0 (Ideal.Quotient.mk Xs (C (j (ρ (algebraMap EA L e))))) = _`. Rewrite using `[hφ0, hφ0, eval_C]`. Establish `hρ'P : ∀ p, ρ' (algebraMap (Polynomial A₁) EA₁ p) = eval 0 p`. Introduce `p`. Rewrite using `[hmapP, hρ']`.

Simplify using `only [map_one, mul_one]`. Establish `hρ'γ : ∀ e, ρ' (γ₀ e) = j (ρ (algebraMap EA L e))`. Introduce `e`. Rewrite using `[hγ₀, hρ', eval_one, one_mul]`. Establish `hρ'A : ∀ a, ρ' (algebraMap A₁ EA₁ a) = a`.

Introduce `a`. Use `show ρ' (algebraMap (Polynomial A₁) EA₁ (C a)) = a`. Rewrite using `[hρ'P, eval_C]`. Establish `hcong : ∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ L₁ x) ∈ Ideal.span {algebraMap (Polynomial T) O X}` using `by set I := Ideal.span {algebraMap (Polynomial T) O X}`. Establish `hext : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp ρ')) = (Ideal.Quotient.mk I).comp g`.

Apply `tensor_ringHom_ext` to reduce the goal to its premises. Introduce `p`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[Ideal.Quotient.eq]`. Rewrite using `[← hmapP p, hρ'P, hgP, IsScalarTower.algebraMap_apply T (Polynomial T) O, algebraMap_eq, ← map_sub]`.

Establish `: C (i₁ (eval 0 p)) - p.map i₁ = -((p.map i₁) - C ((p.map i₁).coeff 0))`. Rewrite using `[coeff_map, coeff_zero_eq_eval_zero]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, map_neg]`. Conclude with `I.neg_mem (Ideal.mem_span_singleton.mpr (map_dvd _ X_dvd_sub_C))`.

Introduce `e`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[Ideal.Quotient.eq]`. Rewrite using `[← hγ₀ e, hρ'γ, hgγ, ← RingHom.comp_apply i₁ j, hij]`. Conclude with `hρ.2.2 _`.

Introduce `x`. Rewrite using `[hjA₁, ← Ideal.Quotient.eq]`. Conclude with `congrArg (fun φ => φ x) hext`. Take `⟨s₀, hs₀, Hs₀⟩` from `exists_mul_mem_span_X QA ρ hρ.2.1`. Establish `hker : ∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ X}` using `by set N₁ := Ideal.span {algebraMap (Polynomial A₁) EA₁ X} set Ik := RingHom.ker (ρ.comp (algebraMap EA L)) set J := N₁ ⊔ Ik.map γ₀`.

Establish `hext : (Ideal.Quotient.mk J).comp ((algebraMap A₁ EA₁).comp ρ') = Ideal.Quotient.mk J`. Apply `tensor_ringHom_ext` to reduce the goal to its premises. Introduce `p`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[Ideal.Quotient.eq]`.

Rewrite using `[← hmapP p, hρ'P, hAP, ← map_sub]`. Establish `: C (eval 0 p) - p = -(p - C (p.coeff 0))` using `by rw [coeff_zero_eq_eval_zero]; ring`. Rewrite using `[this, map_neg]`. Use `J.neg_mem (Ideal.mem_sup_left ?_)` and prove the remaining obligations. Conclude with `Ideal.mem_span_singleton.mpr (map_dvd _ X_dvd_sub_C)`.

Introduce `e`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[Ideal.Quotient.eq]`. Rewrite using `[← hγ₀ e, hρ'γ, ← hγ₀A, ← map_sub]`. Use `Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ?_)` and prove the remaining obligations.

Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, map_sub, map_sub, hρA, sub_self]`. Introduce `x hx`. Establish `hxJ : x ∈ J`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← congrArg (fun φ => φ x) hext]`. Simplify using `[hx]`.

Use `⟨γ₀ s₀, hγ₀Q s₀ hs₀, ?_⟩` and prove the remaining obligations. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hxJ`. Rewrite using `[mul_add]`. Use `N₁.add_mem (N₁.mul_mem_left _ hy) ?_` and prove the remaining obligations. Establish `h1 : Ideal.span {γ₀ s₀} * Ik.map γ₀ = (Ideal.span {s₀} * Ik).map γ₀`.

Rewrite using `[Ideal.map_mul, Ideal.map_span, Set.image_singleton]`. Establish `h2 : Ideal.span {s₀} * Ik ≤ Ideal.span {algebraMap (Polynomial A) EA X}`. Rewrite using `[Ideal.span_singleton_mul_le_iff]`. Introduce `w hw`. Conclude with `Hs₀ w (RingHom.mem_ker.mp hw)`.

Establish `h3 : (Ideal.span {algebraMap (Polynomial A) EA X}).map γ₀ = N₁`. Rewrite using `[Ideal.map_span, Set.image_singleton, hγ₀X]`. Establish `h4` using `Ideal.mul_mem_mul (Ideal.mem_span_singleton_self (γ₀ s₀)) hz`. Rewrite `h4` using `[h1]`. Conclude with `h3 ▸ Ideal.map_mono h2 h4`.

Use `⟨EA₁, inferInstance, inferInstance, iA1, IsScalarTower.of_algebraMap_eq (fun x => ?_), inferInstance, QA₁, inferInstance, jA₁, γ₀, γ, ρ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcong, hker⟩` and prove the remaining obligations. Use `show algebraMap (Polynomial A₁) EA₁ (C x) = algebraMap (Polynomial A₁) EA₁ (algebraMap A₁ (Polynomial A₁) x)`. Rewrite using `[algebraMap_eq]`. Rewrite using `[← comap_maximalIdeal_eq_originIdeal hXO i₁]`. Use extensionality with `p`.

Use `show g (algebraMap _ EA₁ p) ∈ maximalIdeal O ↔ _`. Rewrite using `[Ideal.mem_comap, hgP]`. Both sides reduce to the same expression. Use `RingHom.ext fun p => ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, IsScalarTower.algebraMap_apply (Polynomial A₁) EA₁ L₁, hjA₁, hgP]`.

Both sides reduce to the same expression. Use `IsLocalization.ringHom_ext QA.primeCompl (RingHom.ext fun e => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[hγ, hjA₁, hgγ]`. Conclude with `RingHom.ext fun e => hγ e`.

Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, IsScalarTower.algebraMap_apply A EA L, hγ, hγ₀A, RingHom.comp_apply, IsScalarTower.algebraMap_apply A₁ EA₁ L₁]`. Conclude with `RingHom.ext fun e => hρ'γ e`. Conclude with `RingHom.ext fun a => hρ'A a`. Rewrite using `[hρ'P, eval_X]`.
-/
theorem exists_baseChange_retract : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    IsLocalHom (algebraMap T O) → algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (ρ : Localization.AtPrime QA →+* A),
    QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (γ₀ : EA →+* EA₁) (γ : Localization.AtPrime QA →+* Localization.AtPrime QA₁) (ρ' : EA₁ →+* A₁),
      QA₁.comap (algebraMap (Polynomial A₁) EA₁) = GlobalTheory.KeyOriginCut.originIdeal A₁ ∧
      jA₁.comp (algebraMap (Polynomial A₁) (Localization.AtPrime QA₁)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i₁) ∧
      jA₁.comp γ = jA ∧
      γ.comp (algebraMap EA (Localization.AtPrime QA)) = (algebraMap EA₁ (Localization.AtPrime QA₁)).comp γ₀ ∧
      γ.comp (algebraMap A (Localization.AtPrime QA)) = (algebraMap A₁ (Localization.AtPrime QA₁)).comp j ∧
      ρ'.comp γ₀ = j.comp (ρ.comp (algebraMap EA (Localization.AtPrime QA))) ∧
      ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ ∧
      ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 ∧
      (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
        Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) ∧
      (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) := by
  intro T O _ _ _ _ _ _ _ _ hTO hXO A _ _ _ _ i EA _ _ _ _ _ QA _ jA ρ hQA hjA hρ A₁ _ _ _ j i₁ hi₁ hloc hij
  haveI := hTO
  haveI := hloc
  letI algP : Algebra (Polynomial A) (Polynomial A₁) := (mapRingHom j).toAlgebra
  letI algO : Algebra (Polynomial A) O := ((algebraMap (Polynomial T) O).comp (mapRingHom i)).toAlgebra
  set L := Localization.AtPrime QA with hL

  have hρpoly : ρ.comp (algebraMap (Polynomial A) L) = evalRingHom 0 := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · rw [RingHom.comp_apply, ← algebraMap_eq (R := A), ← IsScalarTower.algebraMap_apply,
        ← RingHom.comp_apply ρ, hρ.1, algebraMap_eq]
      simp
    · have hx : algebraMap (Polynomial A) L X ∈ RingHom.ker ρ := by
        rw [hρ.2.1]; exact Ideal.mem_span_singleton_self _
      rw [RingHom.comp_apply, RingHom.mem_ker.mp hx]; simp
  let f₁ : Polynomial A₁ →ₐ[Polynomial A] O :=
    { toRingHom := (algebraMap (Polynomial T) O).comp (mapRingHom i₁)
      commutes' := fun r => by
        show algebraMap (Polynomial T) O (mapRingHom i₁ (mapRingHom j r)) =
          algebraMap (Polynomial T) O (mapRingHom i r)
        rw [coe_mapRingHom, coe_mapRingHom, coe_mapRingHom, Polynomial.map_map, hij] }
  let f₂ : EA →ₐ[Polynomial A] O :=
    { toRingHom := jA.comp (algebraMap EA L)
      commutes' := fun r => by
        show jA (algebraMap EA L (algebraMap (Polynomial A) EA r)) =
          algebraMap (Polynomial T) O (mapRingHom i r)
        rw [← IsScalarTower.algebraMap_apply (Polynomial A) EA L r]
        exact congrArg (fun φ => φ r) hjA }
  let EA₁ := TensorProduct (Polynomial A) (Polynomial A₁) EA
  let g : EA₁ →+* O := (Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => Commute.all _ _)).toRingHom
  have hg : ∀ p e, g (p ⊗ₜ[Polynomial A] e) = algebraMap (Polynomial T) O (p.map i₁) * jA (algebraMap EA L e) :=
    fun p e => Algebra.TensorProduct.lift_tmul _ _ _ p e
  letI iA1 : Algebra A₁ EA₁ := ((algebraMap (Polynomial A₁) EA₁).comp C).toAlgebra
  have hmapP : ∀ p : Polynomial A₁, algebraMap (Polynomial A₁) EA₁ p = p ⊗ₜ[Polynomial A] (1 : EA) := by
    intro p; rw [Algebra.TensorProduct.algebraMap_apply]; rfl
  have hAP : ∀ a : A₁, algebraMap A₁ EA₁ a = algebraMap (Polynomial A₁) EA₁ (C a) := fun a => rfl
  have hmapA : ∀ a : A₁, algebraMap A₁ EA₁ a = C a ⊗ₜ[Polynomial A] (1 : EA) := fun a => hmapP (C a)
  let γ₀ : EA →+* EA₁ := (Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] EA₁).toRingHom
  have hγ₀ : ∀ e, γ₀ e = (1 : Polynomial A₁) ⊗ₜ[Polynomial A] e := fun e => rfl
  have hγ₀A : ∀ a : A, γ₀ (algebraMap A EA a) = algebraMap A₁ EA₁ (j a) := by
    intro a
    rw [hγ₀, hmapA, IsScalarTower.algebraMap_apply A (Polynomial A) EA, one_tmul_algebraMap, algebraMap_eq]
    show (mapRingHom j (C a)) ⊗ₜ[Polynomial A] (1 : EA) = _
    rw [coe_mapRingHom, Polynomial.map_C]
  have hγ₀X : γ₀ (algebraMap (Polynomial A) EA X) = algebraMap (Polynomial A₁) EA₁ X := by
    rw [hγ₀, hmapP, one_tmul_algebraMap]
    show (mapRingHom j X) ⊗ₜ[Polynomial A] (1 : EA) = _
    rw [coe_mapRingHom, Polynomial.map_X]
  have hgP : ∀ p, g (algebraMap (Polynomial A₁) EA₁ p) = algebraMap (Polynomial T) O (p.map i₁) := by
    intro p; rw [hmapP, hg, map_one, map_one, mul_one]
  have hgγ : ∀ e, g (γ₀ e) = jA (algebraMap EA L e) := by
    intro e; rw [hγ₀, hg, Polynomial.map_one, map_one, one_mul]
  let QA₁ : Ideal EA₁ := (maximalIdeal O).comap g
  have hunit : ∀ y : EA₁, y ∉ QA₁ → IsUnit (g y) := by
    intro y hy
    by_contra h
    exact hy ((mem_maximalIdeal _).2 h)
  let L₁ := Localization.AtPrime QA₁
  let jA₁ : L₁ →+* O := IsLocalization.lift (M := QA₁.primeCompl) (g := g) (fun y => hunit y y.2)
  have hjA₁ : ∀ x, jA₁ (algebraMap EA₁ L₁ x) = g x := fun x => IsLocalization.lift_eq _ x
  have hγ₀Q : ∀ e : EA, e ∉ QA → γ₀ e ∉ QA₁ := by
    intro e he h
    have h1 : g (γ₀ e) ∈ maximalIdeal O := h
    rw [hgγ] at h1
    have hu : IsUnit (algebraMap EA L e) := IsLocalization.map_units L (⟨e, he⟩ : QA.primeCompl)
    exact (mem_maximalIdeal _).1 h1 (hu.map jA)
  let γ : L →+* L₁ := IsLocalization.lift (M := QA.primeCompl) (g := (algebraMap EA₁ L₁).comp γ₀)
    (fun y => IsLocalization.map_units L₁ (⟨γ₀ y, hγ₀Q y y.2⟩ : QA₁.primeCompl))
  have hγ : ∀ e, γ (algebraMap EA L e) = algebraMap EA₁ L₁ (γ₀ e) := fun e => IsLocalization.lift_eq _ e
  have hρA : ∀ b : A, ρ (algebraMap EA L (algebraMap A EA b)) = b := by
    intro b; rw [← IsScalarTower.algebraMap_apply A EA L b]; exact congrArg (fun φ => φ b) hρ.1
  let Xs : Ideal (Polynomial A₁) := Ideal.span {X}
  let φ0 : Polynomial A₁ ⧸ Xs →+* A₁ := Ideal.Quotient.lift Xs (evalRingHom 0) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp)
  have hφ0 : ∀ p, φ0 (Ideal.Quotient.mk Xs p) = eval 0 p := fun p => Ideal.Quotient.lift_mk _ _ _
  let r₁ : Polynomial A₁ →ₐ[Polynomial A] Polynomial A₁ ⧸ Xs := Ideal.Quotient.mkₐ (Polynomial A) Xs
  let r₂ : EA →ₐ[Polynomial A] Polynomial A₁ ⧸ Xs :=
    { toRingHom := (Ideal.Quotient.mk Xs).comp (C.comp (j.comp (ρ.comp (algebraMap EA L))))
      commutes' := fun r => by
        show Ideal.Quotient.mk Xs (C (j (ρ (algebraMap EA L (algebraMap (Polynomial A) EA r))))) =
          Ideal.Quotient.mk Xs (mapRingHom j r)
        rw [← IsScalarTower.algebraMap_apply (Polynomial A) EA L r, ← RingHom.comp_apply ρ, hρpoly,
          Ideal.Quotient.eq, coe_mapRingHom, coe_evalRingHom, ← coeff_zero_eq_eval_zero]
        have : C (j (r.coeff 0)) - r.map j = -((r.map j) - C ((r.map j).coeff 0)) := by
          rw [coeff_map]; ring
        rw [this]
        exact Xs.neg_mem (sub_C_coeff_mem _) }
  let ρ' : EA₁ →+* A₁ := φ0.comp (Algebra.TensorProduct.lift r₁ r₂ (fun _ _ => Commute.all _ _)).toRingHom
  have hρ' : ∀ p e, ρ' (p ⊗ₜ[Polynomial A] e) = eval 0 p * j (ρ (algebraMap EA L e)) := by
    intro p e
    show φ0 (Algebra.TensorProduct.lift r₁ r₂ (fun _ _ => Commute.all _ _) (p ⊗ₜ[Polynomial A] e)) = _
    rw [Algebra.TensorProduct.lift_tmul, map_mul]
    show φ0 (Ideal.Quotient.mk Xs p) * φ0 (Ideal.Quotient.mk Xs (C (j (ρ (algebraMap EA L e))))) = _
    rw [hφ0, hφ0, eval_C]
  have hρ'P : ∀ p, ρ' (algebraMap (Polynomial A₁) EA₁ p) = eval 0 p := by
    intro p; rw [hmapP, hρ']; simp only [map_one, mul_one]
  have hρ'γ : ∀ e, ρ' (γ₀ e) = j (ρ (algebraMap EA L e)) := by
    intro e; rw [hγ₀, hρ', eval_one, one_mul]
  have hρ'A : ∀ a, ρ' (algebraMap A₁ EA₁ a) = a := by
    intro a
    show ρ' (algebraMap (Polynomial A₁) EA₁ (C a)) = a
    rw [hρ'P, eval_C]
  have hcong : ∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ L₁ x) ∈
      Ideal.span {algebraMap (Polynomial T) O X} := by
    set I := Ideal.span {algebraMap (Polynomial T) O X}
    have hext : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp ρ')) =
        (Ideal.Quotient.mk I).comp g := by
      apply tensor_ringHom_ext
      · intro p
        simp only [RingHom.comp_apply]
        rw [Ideal.Quotient.eq]
        rw [← hmapP p, hρ'P, hgP, IsScalarTower.algebraMap_apply T (Polynomial T) O, algebraMap_eq, ← map_sub]
        have : C (i₁ (eval 0 p)) - p.map i₁ = -((p.map i₁) - C ((p.map i₁).coeff 0)) := by
          rw [coeff_map, coeff_zero_eq_eval_zero]; ring
        rw [this, map_neg]
        exact I.neg_mem (Ideal.mem_span_singleton.mpr (map_dvd _ X_dvd_sub_C))
      · intro e
        simp only [RingHom.comp_apply]
        rw [Ideal.Quotient.eq]
        rw [← hγ₀ e, hρ'γ, hgγ, ← RingHom.comp_apply i₁ j, hij]
        exact hρ.2.2 _
    intro x
    rw [hjA₁, ← Ideal.Quotient.eq]
    exact congrArg (fun φ => φ x) hext
  obtain ⟨s₀, hs₀, Hs₀⟩ := exists_mul_mem_span_X QA ρ hρ.2.1
  have hker : ∀ x : EA₁, ρ' x = 0 →
      ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ X} := by
    set N₁ := Ideal.span {algebraMap (Polynomial A₁) EA₁ X}
    set Ik := RingHom.ker (ρ.comp (algebraMap EA L))
    set J := N₁ ⊔ Ik.map γ₀
    have hext : (Ideal.Quotient.mk J).comp ((algebraMap A₁ EA₁).comp ρ') = Ideal.Quotient.mk J := by
      apply tensor_ringHom_ext
      · intro p
        simp only [RingHom.comp_apply]
        rw [Ideal.Quotient.eq]
        rw [← hmapP p, hρ'P, hAP, ← map_sub]
        have : C (eval 0 p) - p = -(p - C (p.coeff 0)) := by rw [coeff_zero_eq_eval_zero]; ring
        rw [this, map_neg]
        refine J.neg_mem (Ideal.mem_sup_left ?_)
        exact Ideal.mem_span_singleton.mpr (map_dvd _ X_dvd_sub_C)
      · intro e
        simp only [RingHom.comp_apply]
        rw [Ideal.Quotient.eq]
        rw [← hγ₀ e, hρ'γ, ← hγ₀A, ← map_sub]
        refine Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ?_)
        rw [RingHom.mem_ker, RingHom.comp_apply, map_sub, map_sub, hρA, sub_self]
    intro x hx
    have hxJ : x ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← congrArg (fun φ => φ x) hext]
      simp [hx]
    refine ⟨γ₀ s₀, hγ₀Q s₀ hs₀, ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxJ
    rw [mul_add]
    refine N₁.add_mem (N₁.mul_mem_left _ hy) ?_
    have h1 : Ideal.span {γ₀ s₀} * Ik.map γ₀ = (Ideal.span {s₀} * Ik).map γ₀ := by
      rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
    have h2 : Ideal.span {s₀} * Ik ≤ Ideal.span {algebraMap (Polynomial A) EA X} := by
      rw [Ideal.span_singleton_mul_le_iff]
      intro w hw; exact Hs₀ w (RingHom.mem_ker.mp hw)
    have h3 : (Ideal.span {algebraMap (Polynomial A) EA X}).map γ₀ = N₁ := by
      rw [Ideal.map_span, Set.image_singleton, hγ₀X]
    have h4 := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self (γ₀ s₀)) hz
    rw [h1] at h4
    exact h3 ▸ Ideal.map_mono h2 h4
  refine ⟨EA₁, inferInstance, inferInstance, iA1, IsScalarTower.of_algebraMap_eq (fun x => ?_),
    inferInstance, QA₁, inferInstance, jA₁, γ₀, γ, ρ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcong, hker⟩
  · show algebraMap (Polynomial A₁) EA₁ (C x) = algebraMap (Polynomial A₁) EA₁ (algebraMap A₁ (Polynomial A₁) x)
    rw [algebraMap_eq]
  · rw [← comap_maximalIdeal_eq_originIdeal hXO i₁]
    ext p
    show g (algebraMap _ EA₁ p) ∈ maximalIdeal O ↔ _
    rw [Ideal.mem_comap, hgP]; rfl
  · refine RingHom.ext fun p => ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply (Polynomial A₁) EA₁ L₁, hjA₁, hgP]; rfl
  · refine IsLocalization.ringHom_ext QA.primeCompl (RingHom.ext fun e => ?_)
    simp only [RingHom.comp_apply]
    rw [hγ, hjA₁, hgγ]
  · exact RingHom.ext fun e => hγ e
  · refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A EA L, hγ, hγ₀A, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply A₁ EA₁ L₁]
  · exact RingHom.ext fun e => hρ'γ e
  · exact RingHom.ext fun a => hρ'A a
  · rw [hρ'P, eval_X]

end GlobalTheory.KeyOriginBaseChangeCons
