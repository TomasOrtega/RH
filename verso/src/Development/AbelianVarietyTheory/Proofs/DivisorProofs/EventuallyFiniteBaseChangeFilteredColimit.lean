import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
open CategoryTheory Limits TensorProduct

noncomputable section

namespace GlobalTheory.FiniteColim

open MvPolynomial

variable {R S A : Type} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]

def bcPres {n : ℕ} (φ : MvPolynomial (Fin n) R →ₐ[R] A) :
    MvPolynomial (Fin n) S →ₐ[S] S ⊗[R] A :=
  aeval (fun i => (1 : S) ⊗ₜ[R] φ (X i))

/- English proof (translation)
Unfold `bcPres`. Rewrite using `[MvPolynomial.aeval_map_algebraMap]`. Establish `h : (aeval (R` using `R) (fun i => (1 : S) ⊗ₜ[R] φ (X i))) = (Algebra.TensorProduct.includeRight (R := R) (A := S)).comp φ := MvPolynomial.algHom_ext (fun i => by simp)`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem bcPres_map {n : ℕ} (φ : MvPolynomial (Fin n) R →ₐ[R] A) (P : MvPolynomial (Fin n) R) :
    bcPres (S := S) φ (MvPolynomial.map (algebraMap R S) P) = (1 : S) ⊗ₜ[R] φ P := by
  unfold bcPres
  rw [MvPolynomial.aeval_map_algebraMap]
  have h : (aeval (R := R) (fun i => (1 : S) ⊗ₜ[R] φ (X i))) =
      (Algebra.TensorProduct.includeRight (R := R) (A := S)).comp φ :=
    MvPolynomial.algHom_ext (fun i => by simp)
  rw [h]
  rfl

/- English proof (translation)
Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `tmul s a`. Take `⟨P, rfl⟩` from `hφ a`.

Use `⟨s • MvPolynomial.map (algebraMap R S) P, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, bcPres_map, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Consider the case `add x y hx hy`. Take `⟨P, rfl⟩` from `hx`. Take `⟨Q, rfl⟩` from `hy`.

Conclude with `⟨P + Q, map_add _ _ _⟩`.
-/
theorem bcPres_surjective {n : ℕ} (φ : MvPolynomial (Fin n) R →ₐ[R] A)
    (hφ : Function.Surjective φ) : Function.Surjective (bcPres (S := S) φ) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s a =>
    obtain ⟨P, rfl⟩ := hφ a
    refine ⟨s • MvPolynomial.map (algebraMap R S) P, ?_⟩
    rw [map_smul, bcPres_map, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy =>
    obtain ⟨P, rfl⟩ := hx
    obtain ⟨Q, rfl⟩ := hy
    exact ⟨P + Q, map_add _ _ _⟩

/- English proof (translation)
Establish `hψ` using `bcPres_surjective (S := S) φ hφ`. Use `haveI : Algebra.FiniteType S (S ⊗[R] A) := Algebra.FiniteType.of_surjective _ hψ`. Establish `hint : ∀ i, IsIntegral S (bcPres (S` using `S) φ (X i)) := by`. Introduce `i`. Use `⟨q i, hq i, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, hG i, map_sum]`. Use `Finset.sum_eq_zero (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, bcPres_map, hrel, TensorProduct.tmul_zero, mul_zero]`. Use `haveI : Algebra.IsIntegral S (S ⊗[R] A) := by`. Prove the components needed by the constructor for the conclusion.

Introduce `x`. Take `⟨P, rfl⟩` from `hψ x`. Set `ψ' : MvPolynomial (Fin n) S →ₐ[S] S ⊗[R] A` to `(integralClosure S (S ⊗[R] A)).val.comp (aeval (fun i => ⟨_, hint i⟩))`. Establish `h : bcPres (S` using `S) φ = ψ' := MvPolynomial.algHom_ext (fun i => by simp [ψ'])`. Rewrite using `[h]`.

Conclude with `(aeval (fun i => (⟨_, hint i⟩ : integralClosure S (S ⊗[R] A))) P).2`. Conclude with `Algebra.IsIntegral.finite`.
-/
theorem finite_of_relations {n : ℕ} {L : Type} [Fintype L] (φ : MvPolynomial (Fin n) R →ₐ[R] A)
    (hφ : Function.Surjective φ) (rel : L → MvPolynomial (Fin n) R) (hrel : ∀ l, φ (rel l) = 0)
    (q : Fin n → Polynomial S) (hq : ∀ i, (q i).Monic) (G : Fin n → L → MvPolynomial (Fin n) S)
    (hG : ∀ i, Polynomial.aeval (X i : MvPolynomial (Fin n) S) (q i) =
      ∑ l, G i l * MvPolynomial.map (algebraMap R S) (rel l)) :
    Module.Finite S (S ⊗[R] A) := by
  have hψ := bcPres_surjective (S := S) φ hφ
  haveI : Algebra.FiniteType S (S ⊗[R] A) := Algebra.FiniteType.of_surjective _ hψ
  have hint : ∀ i, IsIntegral S (bcPres (S := S) φ (X i)) := by
    intro i
    refine ⟨q i, hq i, ?_⟩
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, hG i, map_sum]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [map_mul, bcPres_map, hrel, TensorProduct.tmul_zero, mul_zero]
  haveI : Algebra.IsIntegral S (S ⊗[R] A) := by
    constructor
    intro x
    obtain ⟨P, rfl⟩ := hψ x
    let ψ' : MvPolynomial (Fin n) S →ₐ[S] S ⊗[R] A :=
      (integralClosure S (S ⊗[R] A)).val.comp (aeval (fun i => ⟨_, hint i⟩))
    have h : bcPres (S := S) φ = ψ' := MvPolynomial.algHom_ext (fun i => by simp [ψ'])
    rw [h]
    exact (aeval (fun i => (⟨_, hint i⟩ : integralClosure S (S ⊗[R] A))) P).2
  exact Algebra.IsIntegral.finite

/- English proof (translation)
Set `e` to `MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R S`. Set `T` to `Algebra.TensorProduct.map (AlgHom.id R S) φ`. Establish `hT : ∀ y, bcPres (S` using `S) φ (e y) = T y := by`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul s p`. Simplify using `only [e, T, MvPolynomial.algebraTensorAlgEquiv_tmul, map_smul, bcPres_map, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add]`.

Establish `hmem : e.symm P ∈ RingHom.ker T`. Rewrite using `[RingHom.mem_ker, ← hT, AlgEquiv.apply_symm_apply, hP]`. Rewrite `hmem` using `[Algebra.TensorProduct.lTensor_ker _ hφ, hker, Ideal.map_span]`. Establish `hmem2 : P ∈ Ideal.span (Set.range (fun l => MvPolynomial.map (algebraMap R S) (rel l)))`. Use `Ideal.mem_map_of_mem (e : S ⊗[R] MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) S) hmem` as an intermediate fact.

Rewrite `this` using `[Ideal.map_span]`. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Set.image_image, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `l`.

Simplify using `[e, Algebra.TensorProduct.includeRight_apply, MvPolynomial.algebraTensorAlgEquiv_tmul]`. Simplify using the standard rewrite rules. Conclude with `Ideal.mem_span_range_iff_exists_fun.mp hmem2`.
-/
theorem exists_comb_of_bcPres_eq_zero {n : ℕ} {L : Type} [Fintype L]
    (φ : MvPolynomial (Fin n) R →ₐ[R] A) (hφ : Function.Surjective φ)
    (rel : L → MvPolynomial (Fin n) R) (hker : RingHom.ker φ = Ideal.span (Set.range rel))
    (P : MvPolynomial (Fin n) S) (hP : bcPres (S := S) φ P = 0) :
    ∃ G : L → MvPolynomial (Fin n) S, ∑ l, G l * MvPolynomial.map (algebraMap R S) (rel l) = P := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R S
  let T := Algebra.TensorProduct.map (AlgHom.id R S) φ
  have hT : ∀ y, bcPres (S := S) φ (e y) = T y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s p =>
      simp only [e, T, MvPolynomial.algebraTensorAlgEquiv_tmul, map_smul, bcPres_map,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have hmem : e.symm P ∈ RingHom.ker T := by
    rw [RingHom.mem_ker, ← hT, AlgEquiv.apply_symm_apply, hP]
  rw [Algebra.TensorProduct.lTensor_ker _ hφ, hker, Ideal.map_span] at hmem
  have hmem2 : P ∈ Ideal.span (Set.range (fun l => MvPolynomial.map (algebraMap R S) (rel l))) := by
    have := Ideal.mem_map_of_mem (e : S ⊗[R] MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) S) hmem
    rw [Ideal.map_span] at this
    convert this using 1
    · rw [Set.image_image, ← Set.range_comp]
      congr 2
      funext l
      simp [e, Algebra.TensorProduct.includeRight_apply, MvPolynomial.algebraTensorAlgEquiv_tmul]
    · simp
  exact Ideal.mem_span_range_iff_exists_fun.mp hmem2

/- English proof (translation)
Establish `hc'` using `isColimitOfPreserves (forget _) hc`. Use `choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y`. Take `⟨k, hk⟩` from `IsFiltered.sup_objs_exists (insert j (s.image jx))`. Take `⟨f⟩` from `hk (Finset.mem_insert_self _ _)`. Use `⟨k, f, fun y hy => ?_⟩` and prove the remaining obligations.

Take `⟨g⟩` from `hk (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jx hy))`. Use `⟨F.map g (x y), ?_⟩` and prove the remaining obligations. Establish `h1` using `hx y`. Establish `h2` using `congr(($(c.w g)).hom (x y))`. Simplify using `only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2`.

Rewrite using `[h2]`. Conclude with `h1`.
-/
theorem exists_stage_range {J : Type} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{0}}
    {c : Cocone F} (hc : IsColimit c) (j : J) (s : Finset c.pt) :
    ∃ (k : J) (_ : j ⟶ k), ∀ x ∈ s, x ∈ Set.range (c.ι.app k).hom := by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (insert j (s.image jx))
  obtain ⟨f⟩ := hk (Finset.mem_insert_self _ _)
  refine ⟨k, f, fun y hy => ?_⟩
  obtain ⟨g⟩ := hk (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jx hy))
  refine ⟨F.map g (x y), ?_⟩
  have h1 := hx y
  have h2 := congr(($(c.w g)).hom (x y))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  rw [h2]
  exact h1

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨k, 𝟙 k, by simp⟩`. Consider the case `insert a s ha ih`. Take `⟨k1, g1, h1⟩` from `ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))`. Establish `h0 : (c.ι.app k).hom a = (c.ι.app k).hom 0`.

Rewrite using `[map_zero]`. Conclude with `hs a (Finset.mem_insert_self _ _)`. Take `⟨k2, g2, h2⟩` from `(Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget CommRingCat.{0}) hc) a 0).1 (by exact h0)`. Establish `h2' : (F.map g2).hom a = 0` using `by simpa using h2`. Set `u` to `g1 ≫ IsFiltered.leftToMax k1 k2`.

Set `v` to `g2 ≫ IsFiltered.rightToMax k1 k2`. Use `⟨IsFiltered.coeq u v, u ≫ IsFiltered.coeqHom u v, fun x hx => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Rewrite using `[IsFiltered.coeq_condition u v]`. Simplify using `only [v, Functor.map_comp, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, h2', map_zero]`.

Simplify using `only [u, Functor.map_comp, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, h1 x hx, map_zero]`.
-/
theorem exists_stage_zero {J : Type} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{0}}
    {c : Cocone F} (hc : IsColimit c) {k : J} (s : Finset (F.obj k))
    (hs : ∀ x ∈ s, (c.ι.app k).hom x = 0) :
    ∃ (k' : J) (g : k ⟶ k'), ∀ x ∈ s, (F.map g).hom x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨k, 𝟙 k, by simp⟩
  | insert a s ha ih =>
    obtain ⟨k1, g1, h1⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
    have h0 : (c.ι.app k).hom a = (c.ι.app k).hom 0 := by
      rw [map_zero]; exact hs a (Finset.mem_insert_self _ _)
    obtain ⟨k2, g2, h2⟩ := (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget CommRingCat.{0}) hc) a 0).1 (by exact h0)
    have h2' : (F.map g2).hom a = 0 := by simpa using h2
    let u := g1 ≫ IsFiltered.leftToMax k1 k2
    let v := g2 ≫ IsFiltered.rightToMax k1 k2
    refine ⟨IsFiltered.coeq u v, u ≫ IsFiltered.coeqHom u v, fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [IsFiltered.coeq_condition u v]
      simp only [v, Functor.map_comp, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
        h2', map_zero]
    · simp only [u, Functor.map_comp, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
        h1 x hx, map_zero]

end GlobalTheory.FiniteColim

namespace GlobalTheory.FiniteColim

open MvPolynomial

/- English proof (translation)
Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `monomial n a => simp`.
-/
theorem map_aeval_X {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {σ : Type} (i : σ)
    (q : Polynomial R) :
    MvPolynomial.map f (Polynomial.aeval (X i : MvPolynomial σ R) q) =
      Polynomial.aeval (X i : MvPolynomial σ S) (q.map f) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

end GlobalTheory.FiniteColim

namespace GlobalTheory.FiniteColim

open MvPolynomial

/- English proof (translation)
Introduce `J _ _ F c hc j A _ _ hfp hfin`. Take `⟨n, φ, hφ, hfg⟩` from `hfp.out`. Take `⟨s, hs⟩` from `hfg`. Set `rel : s → MvPolynomial (Fin n) (F.obj j)` to `fun x => x`. Establish `hker : RingHom.ker φ = Ideal.span (Set.range rel)`.

Establish `: Set.range rel = (s : Set (MvPolynomial (Fin n) (F.obj j)))`. Use extensionality with `x`. Simplify using `[rel]`. Rewrite using `[this, hs]`. Both sides reduce to the same expression.

Use `letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra`. Use `haveI : Algebra.IsIntegral c.pt (c.pt ⊗[F.obj j] A) := Algebra.IsIntegral.of_finite _ _`. Establish `hint : ∀ i, IsIntegral c.pt (bcPres (S` using `c.pt) φ (X i)) := fun i => Algebra.IsIntegral.isIntegral _`. Use `choose p hpm hp0 using hint`. Establish `hcomb : ∀ i, ∃ G : s → MvPolynomial (Fin n) c.pt, ∑ l, G l * MvPolynomial.map (algebraMap (F.obj j) c.pt) (rel l) = Polynomial.aeval (X i : MvPolynomial (Fin n) c.pt) (p i)`.

Introduce `i`. Use `exists_comb_of_bcPres_eq_zero φ hφ rel hker _ ?_` and prove the remaining obligations. Rewrite using `[← Polynomial.aeval_algHom_apply, Polynomial.aeval_def]`. Conclude with `hp0 i`. Use `choose G hG using hcomb`.

Set `T : Finset c.pt` to `Finset.univ.biUnion (fun i => (p i).support.image (p i).coeff) ∪ Finset.univ.biUnion (fun i => Finset.univ.biUnion (fun l => (G i l).coeffs))`. Take `⟨k₁, f₁, hk₁⟩` from `exists_stage_range hc j T`. Establish `hlp : ∀ i, ∃ q : Polynomial (F.obj k₁), q.map (c.ι.app k₁).hom = p i ∧ q.Monic`. Introduce `i`. Establish `hl : p i ∈ Polynomial.lifts (c.ι.app k₁).hom`.

Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `m`. Distinguish the cases in `hm : m ∈ (p i).support`. Conclude with `hk₁ _ (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ hm⟩))`. Rewrite using `[Polynomial.notMem_support_iff.1 hm]`.

Conclude with `⟨0, map_zero _⟩`. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl (hpm i)`. Conclude with `⟨q, hq, hqm⟩`. Use `choose q hq hqm using hlp`. Establish `hlG : ∀ i l, ∃ H, MvPolynomial.map (c.ι.app k₁).hom H = G i l`.

Introduce `i l`. Establish `: G i l ∈ Set.range (MvPolynomial.map (σ` using `Fin n) (c.ι.app k₁).hom) := by`. Rewrite using `[MvPolynomial.mem_range_map_iff_coeffs_subset]`. Introduce `y hy`. Conclude with `hk₁ _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, hy⟩⟩))`.

Conclude with `this`. Use `choose H hH using hlG`. Set `E : Fin n → MvPolynomial (Fin n) (F.obj k₁)` to `fun i => Polynomial.aeval (X i) (q i) - ∑ l, H i l * MvPolynomial.map (F.map f₁).hom (rel l)`. Establish `hE : ∀ i, MvPolynomial.map (c.ι.app k₁).hom (E i) = 0`. Introduce `i`.

Simplify using `only [E, map_sub, map_sum, map_mul, map_aeval_X, hq, hH, MvPolynomial.map_map]`. Rewrite using `[← CommRingCat.hom_comp, c.w f₁, sub_eq_zero, ← hG i]`. Both sides reduce to the same expression. Set `U : Finset (F.obj k₁)` to `Finset.univ.biUnion (fun i => (E i).coeffs)`. Take `⟨k₂, g₂, hg₂⟩` from `exists_stage_zero hc U (by`.

Introduce `x hx`. Take `⟨i, -, hx⟩` from `Finset.mem_biUnion.1 hx`. Take `⟨m, -, rfl⟩` from `MvPolynomial.mem_coeffs_iff.1 hx`. Use `congrArg (MvPolynomial.coeff m) (hE i)` as an intermediate fact. Rewrite using `[MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this)` and apply the resulting hypothesis.

Establish `hE2 : ∀ i, MvPolynomial.map (F.map g₂).hom (E i) = 0`. Introduce `i`. Use extensionality with `m`. Rewrite using `[MvPolynomial.coeff_map, MvPolynomial.coeff_zero]`. Distinguish the cases in `hm : m ∈ (E i).support`.

Conclude with `hg₂ _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, MvPolynomial.coeff_mem_coeffs _ (MvPolynomial.mem_support_iff.1 hm)⟩)`. Rewrite using `[MvPolynomial.notMem_support_iff.1 hm, map_zero]`. Use `⟨k₂, f₁ ≫ g₂, fun k f => ?_⟩` and prove the remaining obligations. Use `letI : Algebra (F.obj j) (F.obj k) := (F.map ((f₁ ≫ g₂) ≫ f)).hom.toAlgebra`. Establish `hrel : ∀ l, φ (rel l) = 0` using `fun l => (RingHom.mem_ker).1 (hker ▸ Ideal.subset_span ⟨l, rfl⟩ : rel l ∈ RingHom.ker φ)`.

Use `finite_of_relations φ hφ rel hrel (fun i => (q i).map (F.map (g₂ ≫ f)).hom) (fun i => (hqm i).map _) (fun i l => MvPolynomial.map (F.map (g₂ ≫ f)).hom (H i l)) (fun i => ?_)` and prove the remaining obligations. Establish `halg : algebraMap (F.obj j) (F.obj k) = (F.map (g₂ ≫ f)).hom.comp (F.map f₁).hom`. Express the relevant statement in the definitionally equal form `(F.map ((f₁ ≫ g₂) ≫ f)).hom = _`. Rewrite using `[Category.assoc, Functor.map_comp, CommRingCat.hom_comp]`. Establish `h3 : MvPolynomial.map (F.map (g₂ ≫ f)).hom (E i) = 0`.

Rewrite using `[Functor.map_comp, CommRingCat.hom_comp, ← MvPolynomial.map_map, hE2, map_zero]`. Simplify using `only [E, map_sub, map_sum, map_mul, map_aeval_X, MvPolynomial.map_map, sub_eq_zero] at h3`. Rewrite using `[halg]`. Conclude with `h3`.
-/
theorem eventually_finite_baseChange : ∀ (J : Type) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Module.Finite (F.obj k) (F.obj k ⊗[F.obj j] A) := by
  intro J _ _ F c hc j A _ _ hfp hfin
  classical
  obtain ⟨n, φ, hφ, hfg⟩ := hfp.out
  obtain ⟨s, hs⟩ := hfg
  let rel : s → MvPolynomial (Fin n) (F.obj j) := fun x => x
  have hker : RingHom.ker φ = Ideal.span (Set.range rel) := by
    have : Set.range rel = (s : Set (MvPolynomial (Fin n) (F.obj j))) := by
      ext x; simp [rel]
    rw [this, hs]
    rfl
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  haveI : Algebra.IsIntegral c.pt (c.pt ⊗[F.obj j] A) := Algebra.IsIntegral.of_finite _ _
  have hint : ∀ i, IsIntegral c.pt (bcPres (S := c.pt) φ (X i)) :=
    fun i => Algebra.IsIntegral.isIntegral _
  choose p hpm hp0 using hint
  have hcomb : ∀ i, ∃ G : s → MvPolynomial (Fin n) c.pt,
      ∑ l, G l * MvPolynomial.map (algebraMap (F.obj j) c.pt) (rel l) =
        Polynomial.aeval (X i : MvPolynomial (Fin n) c.pt) (p i) := by
    intro i
    refine exists_comb_of_bcPres_eq_zero φ hφ rel hker _ ?_
    rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_def]
    exact hp0 i
  choose G hG using hcomb
  let T : Finset c.pt := Finset.univ.biUnion (fun i => (p i).support.image (p i).coeff) ∪
    Finset.univ.biUnion (fun i => Finset.univ.biUnion (fun l => (G i l).coeffs))
  obtain ⟨k₁, f₁, hk₁⟩ := exists_stage_range hc j T
  have hlp : ∀ i, ∃ q : Polynomial (F.obj k₁), q.map (c.ι.app k₁).hom = p i ∧ q.Monic := by
    intro i
    have hl : p i ∈ Polynomial.lifts (c.ι.app k₁).hom := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro m
      by_cases hm : m ∈ (p i).support
      · exact hk₁ _ (Finset.mem_union_left _ (Finset.mem_biUnion.2
          ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ hm⟩))
      · rw [Polynomial.notMem_support_iff.1 hm]; exact ⟨0, map_zero _⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hpm i)
    exact ⟨q, hq, hqm⟩
  choose q hq hqm using hlp
  have hlG : ∀ i l, ∃ H, MvPolynomial.map (c.ι.app k₁).hom H = G i l := by
    intro i l
    have : G i l ∈ Set.range (MvPolynomial.map (σ := Fin n) (c.ι.app k₁).hom) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro y hy
      exact hk₁ _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
        Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, hy⟩⟩))
    exact this
  choose H hH using hlG
  let E : Fin n → MvPolynomial (Fin n) (F.obj k₁) := fun i =>
    Polynomial.aeval (X i) (q i) - ∑ l, H i l * MvPolynomial.map (F.map f₁).hom (rel l)
  have hE : ∀ i, MvPolynomial.map (c.ι.app k₁).hom (E i) = 0 := by
    intro i
    simp only [E, map_sub, map_sum, map_mul, map_aeval_X, hq, hH, MvPolynomial.map_map]
    rw [← CommRingCat.hom_comp, c.w f₁, sub_eq_zero, ← hG i]
    rfl
  let U : Finset (F.obj k₁) := Finset.univ.biUnion (fun i => (E i).coeffs)
  obtain ⟨k₂, g₂, hg₂⟩ := exists_stage_zero hc U (by
    intro x hx
    obtain ⟨i, -, hx⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hx
    have := congrArg (MvPolynomial.coeff m) (hE i)
    rwa [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this)
  have hE2 : ∀ i, MvPolynomial.map (F.map g₂).hom (E i) = 0 := by
    intro i
    ext m
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
    by_cases hm : m ∈ (E i).support
    · exact hg₂ _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
        MvPolynomial.coeff_mem_coeffs _ (MvPolynomial.mem_support_iff.1 hm)⟩)
    · rw [MvPolynomial.notMem_support_iff.1 hm, map_zero]
  refine ⟨k₂, f₁ ≫ g₂, fun k f => ?_⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map ((f₁ ≫ g₂) ≫ f)).hom.toAlgebra
  have hrel : ∀ l, φ (rel l) = 0 := fun l =>
    (RingHom.mem_ker).1 (hker ▸ Ideal.subset_span ⟨l, rfl⟩ : rel l ∈ RingHom.ker φ)
  refine finite_of_relations φ hφ rel hrel (fun i => (q i).map (F.map (g₂ ≫ f)).hom)
    (fun i => (hqm i).map _) (fun i l => MvPolynomial.map (F.map (g₂ ≫ f)).hom (H i l)) (fun i => ?_)
  have halg : algebraMap (F.obj j) (F.obj k) = (F.map (g₂ ≫ f)).hom.comp (F.map f₁).hom := by
    change (F.map ((f₁ ≫ g₂) ≫ f)).hom = _
    rw [Category.assoc, Functor.map_comp, CommRingCat.hom_comp]
  have h3 : MvPolynomial.map (F.map (g₂ ≫ f)).hom (E i) = 0 := by
    rw [Functor.map_comp, CommRingCat.hom_comp, ← MvPolynomial.map_map, hE2, map_zero]
  simp only [E, map_sub, map_sum, map_mul, map_aeval_X, MvPolynomial.map_map, sub_eq_zero] at h3
  rw [halg]
  exact h3

end GlobalTheory.FiniteColim
