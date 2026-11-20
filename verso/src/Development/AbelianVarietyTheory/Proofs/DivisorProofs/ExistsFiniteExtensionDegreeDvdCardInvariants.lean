import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

open Polynomial

namespace GlobalTheory.InvariantSpecialisation

/- English proof (translation)
Use `haveI hP : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e`. Take `⟨Q, -, hQ, hQP⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := B) (RingHom.ker e) ⊥ (by`. Introduce `a ha`. Establish `: a = 0` using `hinj (by simpa using ha)`. Simplify using `[this])`.

Use `haveI : Q.LiesOver (RingHom.ker e) := ⟨hQP.symm⟩`. Use `letI : Algebra (A ⧸ RingHom.ker e) Ω := (RingHom.kerLift e).toAlgebra`. Use `haveI : FaithfulSMul (A ⧸ RingHom.ker e) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective e)`. Use `haveI : Algebra.IsIntegral (A ⧸ RingHom.ker e) (B ⧸ Q) := inferInstance`. Use `haveI : IsDomain (A ⧸ RingHom.ker e) := Ideal.Quotient.isDomain _`.

Use `haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain _`. Use `haveI : FaithfulSMul (A ⧸ RingHom.ker e) (B ⧸ Q) := inferInstance`. Use `haveI : Module.IsTorsionFree (A ⧸ RingHom.ker e) (B ⧸ Q) := Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)`. Use `haveI : Module.IsTorsionFree (A ⧸ RingHom.ker e) Ω := Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective e)`. Use `haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker e) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic`.

Set `l : (B ⧸ Q) →ₐ[A ⧸ RingHom.ker e] Ω` to `IsAlgClosed.lift`. Use `⟨(l : (B ⧸ Q) →+* Ω).comp (Ideal.Quotient.mk Q), ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Establish `h` using `l.commutes (Ideal.Quotient.mk _ a)`. Conclude with `h`.
-/
theorem exists_extension {A B Ω : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B))
    [Field Ω] [IsAlgClosed Ω] (e : A →+* Ω) :
    ∃ φ : B →+* Ω, φ.comp (algebraMap A B) = e := by
  haveI hP : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) (RingHom.ker e) ⊥
    (by
      intro a ha
      have : a = 0 := hinj (by simpa using ha)
      simp [this])
  haveI : Q.LiesOver (RingHom.ker e) := ⟨hQP.symm⟩
  letI : Algebra (A ⧸ RingHom.ker e) Ω := (RingHom.kerLift e).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker e) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective e)
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker e) (B ⧸ Q) := inferInstance
  haveI : IsDomain (A ⧸ RingHom.ker e) := Ideal.Quotient.isDomain _
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain _
  haveI : FaithfulSMul (A ⧸ RingHom.ker e) (B ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker e) (B ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker e) Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective e)
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker e) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let l : (B ⧸ Q) →ₐ[A ⧸ RingHom.ker e] Ω := IsAlgClosed.lift
  refine ⟨(l : (B ⧸ Q) →+* Ω).comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have h := l.commutes (Ideal.Quotient.mk _ a)
  exact h

/- English proof (translation)
Use `letI := Fintype.ofFinite G`. Establish `h1 : ∀ b, ∃ g : G, ψ b = φ (g • b)`. Introduce `b`. Take `⟨p, hp⟩` from `Algebra.IsInvariant.charpoly_mem_lifts A B G b`. Establish `hp' : p.map (algebraMap A B) = MulSemiringAction.charpoly G b` using `hp`.

Establish `e1 : (MulSemiringAction.charpoly G b).map ψ = (MulSemiringAction.charpoly G b).map φ`. Rewrite using `[← hp', Polynomial.map_map, Polynomial.map_map, h]`. Establish `e2 : ((MulSemiringAction.charpoly G b).map ψ).eval (ψ b) = 0`. Rewrite using `[Polynomial.eval_map, Polynomial.eval₂_hom, MulSemiringAction.eval_charpoly, map_zero]`. Rewrite `e2` using `[e1, MulSemiringAction.charpoly_eq, Polynomial.map_prod, Polynomial.eval_prod, Finset.prod_eq_zero_iff]`.

Take `⟨g, -, hg⟩` from `e2`. Use `⟨g, ?_⟩` and prove the remaining obligations. Simplify `hg` using `[sub_eq_zero]`. Set `H : G → AddSubgroup B` to `fun g => { carrier := {b | ψ b = φ (g • b)} zero_mem' := by simp add_mem' := by`. Introduce `a b ha hb`.

Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[map_add, smul_add, map_add, ha, hb]`. Use the proof step `neg_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`.

Rewrite using `[map_neg, smul_neg, map_neg, ha] }`. Take `⟨g, -, hg⟩` from `AddSubgroup.exists_finiteIndex_of_leftCoset_cover (H := H) (g := fun _ => 0) (s := Finset.univ) (by`. Rewrite using `[Set.eq_univ_iff_forall]`. Introduce `b`. Take `⟨g, hg⟩` from `h1 b`.

Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨g, Finset.mem_univ _, b, hg, zero_add b⟩)`. Use `⟨g, fun b => ?_⟩` and prove the remaining obligations. Establish `h2 : ψ ((H g).index • b) = φ (g • ((H g).index • b))` using `(H g).nsmul_index_mem b`. Rewrite `h2` using `[smul_comm g, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]`.

Conclude with `mul_left_cancel₀ (Nat.cast_ne_zero.2 hg.index_ne_zero) h2`.
-/
theorem exists_smul_of_comp_eq {A B Ω : Type} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
    [Field Ω] [CharZero Ω] (φ ψ : B →+* Ω)
    (h : ψ.comp (algebraMap A B) = φ.comp (algebraMap A B)) :
    ∃ g : G, ∀ b, ψ b = φ (g • b) := by
  classical
  letI := Fintype.ofFinite G
  have h1 : ∀ b, ∃ g : G, ψ b = φ (g • b) := by
    intro b
    obtain ⟨p, hp⟩ := Algebra.IsInvariant.charpoly_mem_lifts A B G b
    have hp' : p.map (algebraMap A B) = MulSemiringAction.charpoly G b := hp
    have e1 : (MulSemiringAction.charpoly G b).map ψ = (MulSemiringAction.charpoly G b).map φ := by
      rw [← hp', Polynomial.map_map, Polynomial.map_map, h]
    have e2 : ((MulSemiringAction.charpoly G b).map ψ).eval (ψ b) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, MulSemiringAction.eval_charpoly, map_zero]
    rw [e1, MulSemiringAction.charpoly_eq, Polynomial.map_prod, Polynomial.eval_prod,
      Finset.prod_eq_zero_iff] at e2
    obtain ⟨g, -, hg⟩ := e2
    refine ⟨g, ?_⟩
    simpa [sub_eq_zero] using hg
  let H : G → AddSubgroup B := fun g =>
    { carrier := {b | ψ b = φ (g • b)}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, smul_add, map_add, ha, hb]
      neg_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_neg, smul_neg, map_neg, ha] }
  obtain ⟨g, -, hg⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover
    (H := H) (g := fun _ => 0) (s := Finset.univ) (by
      rw [Set.eq_univ_iff_forall]
      intro b
      obtain ⟨g, hg⟩ := h1 b
      simp only [Set.mem_iUnion]
      exact ⟨g, Finset.mem_univ _, b, hg, zero_add b⟩)
  refine ⟨g, fun b => ?_⟩
  have h2 : ψ ((H g).index • b) = φ (g • ((H g).index • b)) := (H g).nsmul_index_mem b
  rw [smul_comm g, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at h2
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hg.index_ne_zero) h2

/- English proof (translation)
Introduce `A B _ _ _ G _ _ _ _ _ hinj k _ _ ev`. Use `haveI := Algebra.IsInvariant.isIntegral A B G`. Set `Ω` to `AlgebraicClosure k`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective`. Take `⟨φ, hφ⟩` from `exists_extension hinj ((algebraMap k Ω).comp ev)`.

Set `K : IntermediateField k Ω` to `IntermediateField.adjoin k (Set.range φ)`. Set `P : Subgroup ((Ω ≃ₐ[k] Ω) × G)` to `{ carrier := {x | ∀ b, x.1 (φ b) = φ (x.2 • b)} one_mem' := by intro b; simp mul_mem' := by`. Introduce `x y hx hy b`. Simplify using `only [Prod.fst_mul, Prod.snd_mul, AlgEquiv.mul_apply]`. Rewrite using `[hy, hx, mul_smul]`.

Use the proof step `inv_mem' := by`. Introduce `x hx b`. Apply `x.1.injective` to reduce the goal to its premises. Rewrite using `[hx]`. Simplify using `}`.

Set `p₁ : P →* (Ω ≃ₐ[k] Ω)` to `(MonoidHom.fst _ _).comp P.subtype`. Set `p₂ : P →* G` to `(MonoidHom.snd _ _).comp P.subtype`. Establish `hsurj : Function.Surjective p₁`. Introduce `σ`. Take `⟨g, hg⟩` from `exists_smul_of_comp_eq (A := A) G φ ((σ : Ω →+* Ω).comp φ) (by`.

Rewrite using `[RingHom.comp_assoc, hφ]`. Use extensionality with `a`. Use the proof step `simp)`. Conclude with `⟨⟨(σ, g), hg⟩, rfl⟩`. Establish `hle : p₂.ker ≤ K.fixingSubgroup.comap p₁`.

Introduce and unpack `⟨⟨σ, g⟩, hx⟩ hg`. Establish `hg1 : g = 1` using `hg`. Substitute `hg1` using the available equality. Express the relevant statement in the definitionally equal form `σ ∈ K.fixingSubgroup`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `x hxK`. Proceed by induction on `hxK using IntermediateField.adjoin_induction with`. Consider the case `mem x hx'`. Take `⟨b, rfl⟩` from `hx'`. Simplify using `using hx b`.

Consider the case `algebraMap c => exact σ.commutes c`. Consider the case `add x y _ _ h1 h2 => rw [map_add, h1, h2]`. Consider the case `inv x _ h1 => rw [map_inv₀, h1]`. Consider the case `mul x y _ _ h1 h2 => rw [map_mul, h1, h2]`. Establish `hdvd : Module.finrank k K ∣ Nat.card G`.

Rewrite using `[IntermediateField.finrank_eq_fixingSubgroup_index, ← Subgroup.index_comap_of_surjective _ hsurj]`. Use `(Subgroup.index_dvd_of_le hle).trans ?_` and prove the remaining obligations. Rewrite using `[Subgroup.index_ker]`. Conclude with `Subgroup.card_subgroup_dvd_card _`. Use `⟨K, inferInstance, inferInstance, φ.codRestrict K (fun b => IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩), ?_, hdvd, ?_⟩` and prove the remaining obligations.

Conclude with `Module.finite_of_finrank_pos (Nat.pos_of_dvd_of_pos hdvd Nat.card_pos)`. Use extensionality with `a`. Conclude with `RingHom.congr_fun hφ a`.
-/
theorem exists_finite_extension_finrank_dvd :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [Finite G]
      [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G],
      Function.Injective (algebraMap A B) → ∀ (k : Type) [Field k] [CharZero k] (ev : A →+* k),
      ∃ (K' : Type) (_ : Field K') (_ : Algebra k K') (β : B →+* K'), FiniteDimensional k K' ∧
        Module.finrank k K' ∣ Nat.card G ∧
        β.comp (algebraMap A B) = (algebraMap k K').comp ev := by
  intro A B _ _ _ G _ _ _ _ _ hinj k _ _ ev
  haveI := Algebra.IsInvariant.isIntegral A B G
  let Ω := AlgebraicClosure k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  obtain ⟨φ, hφ⟩ := exists_extension hinj ((algebraMap k Ω).comp ev)
  let K : IntermediateField k Ω := IntermediateField.adjoin k (Set.range φ)
  let P : Subgroup ((Ω ≃ₐ[k] Ω) × G) :=
    { carrier := {x | ∀ b, x.1 (φ b) = φ (x.2 • b)}
      one_mem' := by intro b; simp
      mul_mem' := by
        intro x y hx hy b
        simp only [Prod.fst_mul, Prod.snd_mul, AlgEquiv.mul_apply]
        rw [hy, hx, mul_smul]
      inv_mem' := by
        intro x hx b
        apply x.1.injective
        rw [hx]
        simp }
  let p₁ : P →* (Ω ≃ₐ[k] Ω) := (MonoidHom.fst _ _).comp P.subtype
  let p₂ : P →* G := (MonoidHom.snd _ _).comp P.subtype
  have hsurj : Function.Surjective p₁ := by
    intro σ
    obtain ⟨g, hg⟩ := exists_smul_of_comp_eq (A := A) G φ ((σ : Ω →+* Ω).comp φ) (by
      rw [RingHom.comp_assoc, hφ]
      ext a
      simp)
    exact ⟨⟨(σ, g), hg⟩, rfl⟩
  have hle : p₂.ker ≤ K.fixingSubgroup.comap p₁ := by
    rintro ⟨⟨σ, g⟩, hx⟩ hg
    have hg1 : g = 1 := hg
    subst hg1
    change σ ∈ K.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hxK
    induction hxK using IntermediateField.adjoin_induction with
    | mem x hx' =>
      obtain ⟨b, rfl⟩ := hx'
      simpa using hx b
    | algebraMap c => exact σ.commutes c
    | add x y _ _ h1 h2 => rw [map_add, h1, h2]
    | inv x _ h1 => rw [map_inv₀, h1]
    | mul x y _ _ h1 h2 => rw [map_mul, h1, h2]
  have hdvd : Module.finrank k K ∣ Nat.card G := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      ← Subgroup.index_comap_of_surjective _ hsurj]
    refine (Subgroup.index_dvd_of_le hle).trans ?_
    rw [Subgroup.index_ker]
    exact Subgroup.card_subgroup_dvd_card _
  refine ⟨K, inferInstance, inferInstance,
    φ.codRestrict K (fun b => IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩), ?_, hdvd, ?_⟩
  · exact Module.finite_of_finrank_pos (Nat.pos_of_dvd_of_pos hdvd Nat.card_pos)
  · ext a
    exact RingHom.congr_fun hφ a

end GlobalTheory.InvariantSpecialisation
