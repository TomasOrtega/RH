import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTraceDualLocalizationIffForallRegularFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfForallHeightOneLocalizationIntegrallyClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalKaehlerDBasisSmoothSubalgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosurePropertiesStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.ComplementaryForms

/- English proof (translation)
Use `set p : Ideal A := Q.comap (algebraMap A B) with hp`. Use `haveI : p.IsPrime := Ideal.comap_isPrime _ Q`. Use `haveI : Q.LiesOver p := ⟨rfl⟩`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]`.

Introduce `r hr hrp`. Assume the negation of the conclusion as `hcon`. Establish `hr0 : r ≠ ⊥`. Introduce and unpack `rfl`. Simplify using `at hcon`.

Use `haveI := hr`. Take `⟨P₁, hP₁Q, hP₁, hP₁o⟩` from `Ideal.exists_ideal_lt_liesOver_of_lt (p := r) (q := p) Q hrp`. Use `haveI := hP₁`. Use `haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime`. Take `⟨P₀, hP₀P₁, hP₀, -⟩` from `Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := r) P₁ (bot_lt_iff_ne_bot.mpr hr0)`.

Use `haveI := hP₀`. Establish `h1` using `Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁`. Establish `h2` using `Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q`. Rewrite `h2` using `[hQ]`. Establish `h4 : (1 : ℕ∞) ≤ P₁.height` using `le_trans le_add_self h1`.

Establish `h3 : (1 : ℕ∞) + 1 ≤ 1` using `le_trans (by gcongr) h2`. Conclude with `absurd h3 (by decide)`. Use `haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime`. Use `Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hne)` as an intermediate fact. Simplify using `using this`.
-/
theorem height_under_eq_one {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Algebra.HasGoingDown A B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height = 1)
    (hne : Q.comap (algebraMap A B) ≠ ⊥) : (Q.comap (algebraMap A B)).height = 1 := by
  set p : Ideal A := Q.comap (algebraMap A B) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver p := ⟨rfl⟩
  apply le_antisymm
  · rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
    intro r hr hrp
    by_contra hcon
    have hr0 : r ≠ ⊥ := by
      rintro rfl
      simp at hcon
    haveI := hr
    obtain ⟨P₁, hP₁Q, hP₁, hP₁o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := r) (q := p) Q hrp
    haveI := hP₁
    haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    obtain ⟨P₀, hP₀P₁, hP₀, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := r) P₁
      (bot_lt_iff_ne_bot.mpr hr0)
    haveI := hP₀
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q
    rw [hQ] at h2
    have h4 : (1 : ℕ∞) ≤ P₁.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
    exact absurd h3 (by decide)
  · haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hne)
    simpa using this

open KaehlerDifferential in
open scoped IntermediateField.algebraAdjoinAdjoin in

/- English proof (translation)
Set `P` to `MvPolynomial (Fin d) k`. Set `A` to `Algebra.adjoin k (Set.range v)`. Set `L` to `IntermediateField.adjoin k (Set.range v)`. Use `letI : Algebra P A := hv.aevalEquiv.toAlgHom.toRingHom.toAlgebra`. Use `haveI : IsScalarTower k P A := .of_algebraMap_eq fun r => (hv.aevalEquiv.commutes r).symm`.

Use `haveI : Algebra.FormallyEtale P A := .of_equiv (AlgEquiv.ofBijective (Algebra.ofId P A) hv.aevalEquiv.bijective)`. Use `haveI : Algebra.FormallyEtale A L := .of_isLocalization (nonZeroDivisors _)`. Use `haveI : Algebra.IsSeparable L F := ⟨fun a => by`. Establish `ha : a ∈ L` using `by rw [show L = ⊤ from hgen]; trivial`. Conclude with `(show algebraMap L F ⟨a, ha⟩ = a from rfl) ▸ isSeparable_algebraMap _⟩`.

Use `haveI : Algebra.FormallyEtale L F := Algebra.FormallyEtale.of_isSeparable _ F`. Use `haveI : Algebra.FormallyEtale A F := .comp A L F`. Use `haveI : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K`. Set `b₁ : Module.Basis (Fin d) A Ω[A⁄k]` to `((mvPolynomialBasis k (Fin d)).baseChange A).map (tensorKaehlerEquivOfFormallyEtale k P A)`. Set `b₂ : Module.Basis (Fin d) F Ω[F⁄k]` to `(b₁.baseChange F).map (tensorKaehlerEquivOfFormallyEtale k A F)`.

Establish `h₂ : ∀ j, b₂ j = D k F (v j)`. Introduce `j`. Simplify using `only [b₂, b₁, Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, mvPolynomialBasis_apply, map_D]`. Establish `e : algebraMap A F (algebraMap P A (MvPolynomial.X j)) = v j`. Express the relevant statement in the definitionally equal form `algebraMap A F (hv.aevalEquiv (MvPolynomial.X j)) = v j`.

Rewrite using `[hv.algebraMap_aevalEquiv, MvPolynomial.aeval_X]`. Rewrite using `[← e, ← map_D k k A F, ← map_D k k P A]`. Conclude with `congrArg _ ((mapBaseChange_tmul k P A 1 _).trans (one_smul _ _))`. Use `⟨(b₂.baseChange K).map (tensorKaehlerEquivOfFormallyEtale k F K), fun j => ?_⟩` and prove the remaining obligations. Simplify using `only [Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, h₂, map_D]`.
-/
theorem exists_basis_D (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] [Algebra.IsSeparable F K] (d : ℕ) (v : Fin d → F)
    (hv : AlgebraicIndependent k v) (hgen : IntermediateField.adjoin k (Set.range v) = ⊤) :
    ∃ b : Module.Basis (Fin d) K Ω[K⁄k], ∀ j, b j = D k K (algebraMap F K (v j)) := by
  let P := MvPolynomial (Fin d) k
  let A := Algebra.adjoin k (Set.range v)
  let L := IntermediateField.adjoin k (Set.range v)
  letI : Algebra P A := hv.aevalEquiv.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower k P A := .of_algebraMap_eq fun r => (hv.aevalEquiv.commutes r).symm
  haveI : Algebra.FormallyEtale P A :=
    .of_equiv (AlgEquiv.ofBijective (Algebra.ofId P A) hv.aevalEquiv.bijective)
  haveI : Algebra.FormallyEtale A L := .of_isLocalization (nonZeroDivisors _)
  haveI : Algebra.IsSeparable L F := ⟨fun a => by
    have ha : a ∈ L := by rw [show L = ⊤ from hgen]; trivial
    exact (show algebraMap L F ⟨a, ha⟩ = a from rfl) ▸ isSeparable_algebraMap _⟩
  haveI : Algebra.FormallyEtale L F := Algebra.FormallyEtale.of_isSeparable _ F
  haveI : Algebra.FormallyEtale A F := .comp A L F
  haveI : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  let b₁ : Module.Basis (Fin d) A Ω[A⁄k] :=
    ((mvPolynomialBasis k (Fin d)).baseChange A).map (tensorKaehlerEquivOfFormallyEtale k P A)
  let b₂ : Module.Basis (Fin d) F Ω[F⁄k] := (b₁.baseChange F).map (tensorKaehlerEquivOfFormallyEtale k A F)
  have h₂ : ∀ j, b₂ j = D k F (v j) := by
    intro j
    simp only [b₂, b₁, Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply,
      mapBaseChange_tmul, one_smul, mvPolynomialBasis_apply, map_D]
    have e : algebraMap A F (algebraMap P A (MvPolynomial.X j)) = v j := by
      change algebraMap A F (hv.aevalEquiv (MvPolynomial.X j)) = v j
      rw [hv.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
    rw [← e, ← map_D k k A F, ← map_D k k P A]
    exact congrArg _ ((mapBaseChange_tmul k P A 1 _).trans (one_smul _ _))
  refine ⟨(b₂.baseChange K).map (tensorKaehlerEquivOfFormallyEtale k F K), fun j => ?_⟩
  simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply,
    mapBaseChange_tmul, one_smul, h₂, map_D]

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

/- English proof (translation)
Set `φ : Ω[K⁄k] [⋀^Fin d]→ₗ[K] K` to `τ.compAlternatingMap (ExteriorAlgebra.ιMulti K d)`. Establish `hφ : ∀ v, τ (ExteriorAlgebra.ιMulti K d v) = φ v` using `fun v => rfl`. Establish `hb' : (⇑b) = fun j => D k K (u' j : K)` using `funext hb`. Establish `key : ∀ v, φ v = τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) * b.det v`. Introduce `v`.

Use `conv_lhs => rw [AlternatingMap.eq_smul_basis_det b φ]`. Rewrite using `[AlternatingMap.smul_apply, smul_eq_mul, hφ, hb']`. Use `set g := τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) with hg`. Use `⟨fun h0 => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Use `key w` as an intermediate fact.

Rewrite `this` using `[← hφ, hw, h0, zero_mul]`. Conclude with `one_ne_zero this`. Establish `hdet : ∀ v : Fin d → K, (∀ j, v j ∈ B) → ∃ c : B, (f : K) ^ d * b.det (fun j => D k K (v j)) = c`. Introduce `v hv`. Use `choose M hM using fun i j => hc ⟨v j, hv j⟩ i`.

Use `⟨(Matrix.of M).det, ?_⟩` and prove the remaining obligations. Establish `hs` using `Matrix.det_smul (b.toMatrix fun j => D k K (v j)) (f : K)`. Rewrite `hs` using `[Fintype.card_fin]`. Rewrite using `[Module.Basis.det_apply, ← hs]`. Establish `: (f : K) • b.toMatrix (fun j => D k K (v j)) = (algebraMap B K).mapMatrix (Matrix.of M)`.

Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, Module.Basis.toMatrix_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]`. Conclude with `hM i j`. Rewrite using `[this, ← RingHom.map_det]`. Both sides reduce to the same expression.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c₀, hc₀, v, hv, rfl⟩` from `hx`. Take `⟨c, hc'⟩` from `hdet v hv`. Use `⟨⟨c₀, hc₀⟩ * c, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, smul_eq_mul, hφ, key]`. Use `push_cast`. Rewrite using `[← hc']`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨c₁, h₁⟩` from `hx`. Take `⟨c₂, h₂⟩` from `hy`. Conclude with `⟨c₁ + c₂, by rw [map_add, mul_add, h₁, h₂]; push_cast; ring⟩`. Consider the case `smul a x _ hx`.

Take `⟨c, h⟩` from `hx`. Use `⟨algebraMap k B a * c, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul_of_tower, Algebra.smul_def, mul_left_comm, h]`. Use `push_cast`. Rewrite using `[IsScalarTower.algebraMap_apply k B K]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem local_frame (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) (d : ℕ)
    (τ : DR k K →ₗ[K] K) (w : Fin d → Ω[K⁄k]) (hw : τ (ExteriorAlgebra.ιMulti K d w) = 1)
    (f : B) (u' : Fin d → B) (b : Module.Basis (Fin d) K Ω[K⁄k]) (hb : ∀ j, b j = D k K (u' j : K))
    (hc : ∀ (v : B) (j : Fin d), ∃ c : B, (f : K) * b.repr (D k K (v : K)) j = c) :
    τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) ≠ 0 ∧
    ∀ y ∈ omB k K B d, ∃ c : B,
      (f : K) ^ d * τ y = τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) * c := by
  classical
  let φ : Ω[K⁄k] [⋀^Fin d]→ₗ[K] K := τ.compAlternatingMap (ExteriorAlgebra.ιMulti K d)
  have hφ : ∀ v, τ (ExteriorAlgebra.ιMulti K d v) = φ v := fun v => rfl
  have hb' : (⇑b) = fun j => D k K (u' j : K) := funext hb
  have key : ∀ v, φ v = τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) * b.det v := by
    intro v
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det b φ]
    rw [AlternatingMap.smul_apply, smul_eq_mul, hφ, hb']
  set g := τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) with hg
  refine ⟨fun h0 => ?_, fun y hy => ?_⟩
  · have := key w
    rw [← hφ, hw, h0, zero_mul] at this
    exact one_ne_zero this
  have hdet : ∀ v : Fin d → K, (∀ j, v j ∈ B) →
      ∃ c : B, (f : K) ^ d * b.det (fun j => D k K (v j)) = c := by
    intro v hv
    choose M hM using fun i j => hc ⟨v j, hv j⟩ i
    refine ⟨(Matrix.of M).det, ?_⟩
    have hs := Matrix.det_smul (b.toMatrix fun j => D k K (v j)) (f : K)
    rw [Fintype.card_fin] at hs
    rw [Module.Basis.det_apply, ← hs]
    have : (f : K) • b.toMatrix (fun j => D k K (v j)) = (algebraMap B K).mapMatrix (Matrix.of M) := by
      ext i j
      simp only [Matrix.smul_apply, Module.Basis.toMatrix_apply, smul_eq_mul, RingHom.mapMatrix_apply,
        Matrix.map_apply, Matrix.of_apply]
      exact hM i j
    rw [this, ← RingHom.map_det]
    rfl
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c₀, hc₀, v, hv, rfl⟩ := hx
    obtain ⟨c, hc'⟩ := hdet v hv
    refine ⟨⟨c₀, hc₀⟩ * c, ?_⟩
    rw [map_smul, smul_eq_mul, hφ, key]
    push_cast
    rw [← hc']
    ring
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c₁, h₁⟩ := hx
    obtain ⟨c₂, h₂⟩ := hy
    exact ⟨c₁ + c₂, by rw [map_add, mul_add, h₁, h₂]; push_cast; ring⟩
  | smul a x _ hx =>
    obtain ⟨c, h⟩ := hx
    refine ⟨algebraMap k B a * c, ?_⟩
    rw [LinearMap.map_smul_of_tower, Algebra.smul_def, mul_left_comm, h]
    push_cast
    rw [IsScalarTower.algebraMap_apply k B K]
    ring

end GlobalTheory.ComplementaryForms

namespace GlobalTheory.ComplementaryForms

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

/- English proof (translation)
Introduce `k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB hsm τ hτ z`. Use `haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective`. Use `haveI : Algebra.IsSeparable F K := inferInstance`. Use `haveI : IsNoetherianRing A := by`. Substitute `hA` using the available equality.

Conclude with `isNoetherianRing_of_ringEquiv _ hu.aevalEquiv.toRingEquiv`. Use `haveI : UniqueFactorizationMonoid A := by`. Substitute `hA` using the available equality. Conclude with `hu.aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance`. Use `haveI : IsIntegrallyClosed A := inferInstance`.

Establish `hgen : IntermediateField.adjoin k (Set.range u) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨a, s, -, rfl⟩` from `IsFractionRing.div_surjective (A := A) x`. Establish `hle : ∀ t : A, (t : F) ∈ IntermediateField.adjoin k (Set.range u)`.

Introduce `t`. Establish `ht : (t : F) ∈ Algebra.adjoin k (Set.range u)` using `hA ▸ t.2`. Conclude with `IntermediateField.algebra_adjoin_le_adjoin k _ ht`. Conclude with `div_mem (hle a) (hle s)`. Establish `hrank : Module.finrank K Ω[K⁄k] = d`.

Take `⟨b, -⟩` from `exists_basis_D k F K d u hu hgen`. Simplify using `using Module.finrank_eq_card_basis b`. Set `C` to `integralClosure A K`. Use `haveI : IsFractionRing C K := integralClosure.isFractionRing_of_finite_extension F K`. Use `haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension F`.

Use `haveI : IsNoetherianRing C := IsIntegralClosure.isNoetherianRing A F K C`. Establish `hmem : ∀ x : K, x ∈ B ↔ x ∈ C` using `by subst hB; exact fun x => Iff.rfl`. Set `e : C ≃+* B` to `{ toFun := fun x => ⟨x.1, (hmem _).2 x.2⟩ invFun := fun x => ⟨x.1, (hmem _).1 x.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl map_mul' := fun _ _ => rfl map_add' := fun _ _ => rfl }`. Use `haveI : IsNoetherianRing B := isNoetherianRing_of_ringEquiv C e`. Use `haveI : IsFractionRing B K := by subst hB; exact inferInstanceAs (IsFractionRing C K)`.

Use `haveI : IsIntegrallyClosed B := by subst hB; exact inferInstanceAs (IsIntegrallyClosed C)`. Use `haveI : Algebra.Smooth k B := hsm`. Use `haveI : FaithfulSMul A C := by`. Use `(faithfulSMul_iff_algebraMap_injective A C).mpr fun a a' h => ?_` and prove the remaining obligations. Establish `h' : algebraMap F K (a : F) = algebraMap F K (a' : F)` using `congrArg (fun x : C => (x : K)) h`.

Conclude with `Subtype.val_injective ((algebraMap F K).injective h')`. Use `haveI : Algebra.HasGoingDown A C := inferInstance`. Establish `hunder : ∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → ∃ p : Ideal A, p.IsPrime ∧ p.height = 1 ∧ ∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)`. Introduce `Q hQ hQ1`. Use `set Q' : Ideal C := Q.comap (e : C →+* B)`.

Use `haveI : Q'.IsPrime := Ideal.comap_isPrime _ Q`. Establish `hQ'1 : Q'.height = 1` using `(RingEquiv.height_comap e Q).trans hQ1`. Establish `hne : Q'.comap (algebraMap A C) ≠ ⊥`. Establish `hQ'0 : Q' ≠ ⊥`. Introduce and unpack `h`.

Rewrite `hQ'1` using `[h, Ideal.height_bot]`. Conclude with `zero_ne_one hQ'1`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hQ'0`. Conclude with `Ideal.comap_ne_bot_of_integral_mem hx0 hx (integralClosure.isIntegral x)`. Use `⟨Q'.comap (algebraMap A C), Ideal.comap_isPrime _ _, height_under_eq_one Q' hQ'1 hne, ?_⟩` and prove the remaining obligations.

Introduce `a b hab`. Establish `: b = e (algebraMap A C a)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hab]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Set `J : Ideal B` to `{ carrier := {c | ∃ y ∈ omB k K B d, τ y = (c : K) * z} add_mem' := by`.

Introduce and unpack `c₁ c₂ ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩`. Conclude with `⟨y₁ + y₂, add_mem hy₁ hy₂, by rw [map_add, h₁, h₂]; push_cast; ring⟩`. Use the proof step `zero_mem' := ⟨0, zero_mem _, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c c' ⟨y, hy, h⟩`.

Use `⟨(c : K) • y, ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K B d d).2.1 y hy).2.2.2 _ c.2, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, h, smul_eq_mul, smul_eq_mul]`. Use `push_cast`. Use `ring }`. It suffices to establish `h1J : (1 : B) ∈ J by`.

Take `⟨y, hy, h⟩` from `h1J`. Conclude with `⟨y, hy, by simpa using h⟩`. Assume the negation of the conclusion as `hJ`. Take `⟨P, hPmax, hJP⟩` from `Ideal.exists_le_maximal J (fun h => hJ (h ▸ Submodule.mem_top))`. Use `haveI := hPmax.isPrime`.

Take `⟨f, u', bP, hfP, hb, hc⟩` from `GlobalTheory.T.exists_local_kaehlerD_basis_smooth_subalgebra k K B d hrank P`. Take `⟨hg0, hloc⟩` from `local_frame k K B d τ _ hτ f u' bP hb hc`. Use `set g := τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) with hg`. Take `⟨c, hcw⟩` from `GlobalTheory.T.mem_of_forall_heightOne_localization_integrallyClosed B K ((f : K) ^ d * z / g) (by`. Introduce `Q hQ hQ1`.

Take `⟨p, hp, hp1, hover⟩` from `hunder Q hQ hQ1`. Establish `hcod` using `(GlobalTheory.T.mem_traceDual_localization_iff_forall_regularForm_alt k F K d u hu A hA B hB hsm τ hτ p hp hp1 z).1 (fun b => ⟨1, ⟨_, hz b⟩, (Ideal.ne_top_iff_one p).1 hp.ne_top, by simp⟩)`. Take `⟨r, hr, y, hy, hyz⟩` from `hcod Q hQ hover`. Take `⟨c, hc'⟩` from `hloc y hy`. Use `⟨r, c, hr, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(r : K) * ((f : K) ^ d * z / g) = c`. Rewrite using `[mul_div_assoc', mul_left_comm, ← hyz, hc', mul_div_assoc]`. Use the proof step `field_simp)`. Establish `hfd : f ^ d ∈ J`. Use `⟨(c : K) • ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K)), Submodule.subset_span ⟨c, c.2, _, fun j => (u' j).2, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, smul_eq_mul, ← hg]`. Establish `hcw' : (f : K) ^ d * z / g = c` using `hcw`. Rewrite using `[← hcw']`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Conclude with `hfP (hPmax.isPrime.mem_of_pow_mem d (hJP hfd))`. Introduce and unpack `⟨y, hy, rfl⟩ b`. Take `⟨c, hc⟩` from `GlobalTheory.T.mem_of_forall_heightOne_localization_integrallyClosed A F (Algebra.trace F K (τ y * b)) (by`. Introduce `p hp hp1`. Conclude with `(GlobalTheory.T.mem_traceDual_localization_iff_forall_regularForm_alt k F K d u hu A hA B hB hsm τ hτ p hp hp1 (τ y)).2 (fun Q hQ _ => ⟨1, (Ideal.ne_top_iff_one Q).1 hQ.ne_top, y, hy, by simp⟩) b)`.

Rewrite using `[hc]`. Conclude with `c.2`.
-/
theorem complementary_eq_topForms : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ z : K, (∀ b : B, Algebra.trace F K (z * b) ∈ A) ↔ ∃ y ∈ omB k K B d, τ y = z := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB hsm τ hτ z
  classical
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  haveI : Algebra.IsSeparable F K := inferInstance

  haveI : IsNoetherianRing A := by
    subst hA; exact isNoetherianRing_of_ringEquiv _ hu.aevalEquiv.toRingEquiv
  haveI : UniqueFactorizationMonoid A := by
    subst hA; exact hu.aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  haveI : IsIntegrallyClosed A := inferInstance
  have hgen : IntermediateField.adjoin k (Set.range u) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    have hle : ∀ t : A, (t : F) ∈ IntermediateField.adjoin k (Set.range u) := by
      intro t
      have ht : (t : F) ∈ Algebra.adjoin k (Set.range u) := hA ▸ t.2
      exact IntermediateField.algebra_adjoin_le_adjoin k _ ht
    exact div_mem (hle a) (hle s)
  have hrank : Module.finrank K Ω[K⁄k] = d := by
    obtain ⟨b, -⟩ := exists_basis_D k F K d u hu hgen
    simpa using Module.finrank_eq_card_basis b

  let C := integralClosure A K
  haveI : IsFractionRing C K := integralClosure.isFractionRing_of_finite_extension F K
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension F
  haveI : IsNoetherianRing C := IsIntegralClosure.isNoetherianRing A F K C
  have hmem : ∀ x : K, x ∈ B ↔ x ∈ C := by subst hB; exact fun x => Iff.rfl
  let e : C ≃+* B :=
    { toFun := fun x => ⟨x.1, (hmem _).2 x.2⟩
      invFun := fun x => ⟨x.1, (hmem _).1 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : IsNoetherianRing B := isNoetherianRing_of_ringEquiv C e
  haveI : IsFractionRing B K := by subst hB; exact inferInstanceAs (IsFractionRing C K)
  haveI : IsIntegrallyClosed B := by subst hB; exact inferInstanceAs (IsIntegrallyClosed C)
  haveI : Algebra.Smooth k B := hsm
  haveI : FaithfulSMul A C := by
    refine (faithfulSMul_iff_algebraMap_injective A C).mpr fun a a' h => ?_
    have h' : algebraMap F K (a : F) = algebraMap F K (a' : F) := congrArg (fun x : C => (x : K)) h
    exact Subtype.val_injective ((algebraMap F K).injective h')
  haveI : Algebra.HasGoingDown A C := inferInstance

  have hunder : ∀ Q : Ideal B, Q.IsPrime → Q.height = 1 →
      ∃ p : Ideal A, p.IsPrime ∧ p.height = 1 ∧
        ∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p) := by
    intro Q hQ hQ1
    set Q' : Ideal C := Q.comap (e : C →+* B)
    haveI : Q'.IsPrime := Ideal.comap_isPrime _ Q
    have hQ'1 : Q'.height = 1 := (RingEquiv.height_comap e Q).trans hQ1
    have hne : Q'.comap (algebraMap A C) ≠ ⊥ := by
      have hQ'0 : Q' ≠ ⊥ := by
        rintro h
        rw [h, Ideal.height_bot] at hQ'1
        exact zero_ne_one hQ'1
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ'0
      exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (integralClosure.isIntegral x)
    refine ⟨Q'.comap (algebraMap A C), Ideal.comap_isPrime _ _, height_under_eq_one Q' hQ'1 hne, ?_⟩
    intro a b hab
    have : b = e (algebraMap A C a) := by
      apply Subtype.ext
      rw [hab]
      rfl
    rw [this]
    rfl
  constructor
  · intro hz
    let J : Ideal B :=
      { carrier := {c | ∃ y ∈ omB k K B d, τ y = (c : K) * z}
        add_mem' := by
          rintro c₁ c₂ ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩
          exact ⟨y₁ + y₂, add_mem hy₁ hy₂, by rw [map_add, h₁, h₂]; push_cast; ring⟩
        zero_mem' := ⟨0, zero_mem _, by simp⟩
        smul_mem' := by
          rintro c c' ⟨y, hy, h⟩
          refine ⟨(c : K) • y, ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K B d d).2.1 y hy).2.2.2 _ c.2, ?_⟩
          rw [map_smul, h, smul_eq_mul, smul_eq_mul]
          push_cast
          ring }
    suffices h1J : (1 : B) ∈ J by
      obtain ⟨y, hy, h⟩ := h1J
      exact ⟨y, hy, by simpa using h⟩
    by_contra hJ
    obtain ⟨P, hPmax, hJP⟩ := Ideal.exists_le_maximal J (fun h => hJ (h ▸ Submodule.mem_top))
    haveI := hPmax.isPrime
    obtain ⟨f, u', bP, hfP, hb, hc⟩ := GlobalTheory.T.exists_local_kaehlerD_basis_smooth_subalgebra k K B d hrank P
    obtain ⟨hg0, hloc⟩ := local_frame k K B d τ _ hτ f u' bP hb hc
    set g := τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) with hg
    obtain ⟨c, hcw⟩ := GlobalTheory.T.mem_of_forall_heightOne_localization_integrallyClosed B K ((f : K) ^ d * z / g) (by
      intro Q hQ hQ1
      obtain ⟨p, hp, hp1, hover⟩ := hunder Q hQ hQ1
      have hcod := (GlobalTheory.T.mem_traceDual_localization_iff_forall_regularForm_alt k F K d u hu A hA B hB hsm τ hτ p hp hp1 z).1 (fun b =>
        ⟨1, ⟨_, hz b⟩, (Ideal.ne_top_iff_one p).1 hp.ne_top, by simp⟩)
      obtain ⟨r, hr, y, hy, hyz⟩ := hcod Q hQ hover
      obtain ⟨c, hc'⟩ := hloc y hy
      refine ⟨r, c, hr, ?_⟩
      change (r : K) * ((f : K) ^ d * z / g) = c
      rw [mul_div_assoc', mul_left_comm, ← hyz, hc', mul_div_assoc]
      field_simp)
    have hfd : f ^ d ∈ J := by
      refine ⟨(c : K) • ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K)),
        Submodule.subset_span ⟨c, c.2, _, fun j => (u' j).2, rfl⟩, ?_⟩
      rw [map_smul, smul_eq_mul, ← hg]
      have hcw' : (f : K) ^ d * z / g = c := hcw
      rw [← hcw']
      push_cast
      field_simp
    exact hfP (hPmax.isPrime.mem_of_pow_mem d (hJP hfd))
  · rintro ⟨y, hy, rfl⟩ b
    obtain ⟨c, hc⟩ := GlobalTheory.T.mem_of_forall_heightOne_localization_integrallyClosed A F (Algebra.trace F K (τ y * b)) (by
      intro p hp hp1
      exact (GlobalTheory.T.mem_traceDual_localization_iff_forall_regularForm_alt k F K d u hu A hA B hB hsm τ hτ p hp hp1 (τ y)).2
        (fun Q hQ _ => ⟨1, (Ideal.ne_top_iff_one Q).1 hQ.ne_top, y, hy, by simp⟩) b)
    rw [hc]
    exact c.2

end GlobalTheory.ComplementaryForms
