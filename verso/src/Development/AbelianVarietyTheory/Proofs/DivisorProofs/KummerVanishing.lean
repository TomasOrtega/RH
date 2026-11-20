import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatRefiningEtaleSurjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCocycleCoboundaryIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraMapEqOfFaithfullyFlatIncludeLeftEqIStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicFaithfullyFlatDescentUnitCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneSectionsEqRootsOfUnityStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

/- English proof (translation)
Unfold `UCoc`. Simplify using `[Algebra.TensorProduct.one_def]`.
-/
theorem uCoc_one (A B : Type) [CommRing A] [CommRing B] [Algebra A B] : UCoc A B 1 := by
  unfold UCoc
  simp [Algebra.TensorProduct.one_def]

/- English proof (translation)
Unfold `UCoc at *`. Simplify using `only [Units.val_mul, map_mul, hu, hv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem uCoc_mul {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {u v : (B ⊗[A] B)ˣ}
    (hu : UCoc A B u) (hv : UCoc A B v) : UCoc A B (u * v) := by
  unfold UCoc at *
  simp only [Units.val_mul, map_mul, hu, hv]
  ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using uCoc_one A B`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `uCoc_mul ih hu`.
-/
theorem uCoc_pow {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {u : (B ⊗[A] B)ˣ}
    (hu : UCoc A B u) (n : ℕ) : UCoc A B (u ^ n) := by
  induction n with
  | zero => simpa using uCoc_one A B
  | succ n ih => rw [pow_succ]; exact uCoc_mul ih hu

/- English proof (translation)
Introduce `q _ A _ hq hu hp`. It suffices to establish `h : ∀ x : Ht q (sp A) 1 1, x = 0 from ⟨fun x y => by rw [h x, h y]⟩`. Introduce `x`. Take `⟨Y, f, hfe, hfs, hx⟩` from `GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover (ZMod q) (Spec (CommRingCat.of A)) (tw q 1) 1 one_pos x`. Take `⟨B, g, h, hg, hhf⟩` from `GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection (CommRingCat.of A) Y f hfe hfs`.

Use `letI : Algebra A B := g.hom.toAlgebra`. Use `haveI : Algebra.Etale A B := hg.1`. Use `haveI : Module.FaithfullyFlat A B := hg.2`. Establish `hxB : pull (ZMod q) (spMap (algebraMap A B)) (tw q 1) 1 x = 0`. Establish `: spMap (algebraMap A B) = sch.map h ≫ sch.map f`.

Rewrite using `[← sch.map_comp, hhf]`. Both sides reduce to the same expression. Rewrite using `[this, pull_comp, hx, map_zero]`. Take `⟨γ, hγ⟩` from `GlobalTheory.T.etale_cocycle_coboundary_iff (ZMod q) (tw q 1) A`. Take `⟨hγ0, hγs, -, -⟩` from `hγ B`.

Take `⟨u, rfl⟩` from `hγs x hxB`. Rewrite using `[hγ0]`. Take `⟨e, he⟩` from `GlobalTheory.T.tateTwistOne_sections_eq_rootsOfUnity q`. Establish `hqB : IsUnit (q : (B : Type))` using `by simpa using hq.map (algebraMap A B)`. Establish `hqBB : IsUnit (q : B ⊗[A] B)` using `by simpa using hq.map (algebraMap A (B ⊗[A] B))`.

Establish `hqBBB : IsUnit (q : B ⊗[A] (B ⊗[A] B))` using `by simpa using hq.map (algebraMap A (B ⊗[A] (B ⊗[A] B)))`. Establish `hUq : ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) ^ q = 1` using `(mem_rootsOfUnity _ _).1 (Additive.toMul (e _ hqBB u.1)).2`. Establish `hUc : UCoc A B ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ)`. Establish `h2` using `u.2`. Express the relevant statement in the definitionally equal form `_ = _ at h2`.

Establish `h3` using `congrArg (fun y => ((Additive.toMul (e _ hqBBB y) : rootsOfUnity q _) : (B ⊗[A] (B ⊗[A] B))ˣ)) h2`. Simplify using `only [AddMonoidHom.add_apply, map_add, toMul_add, Subgroup.coe_mul, LinearMap.toAddMonoidHom_coe] at h3`. Rewrite `h3` using `[he _ _ _ hqBB hqBBB, he _ _ _ hqBB hqBBB, he _ _ _ hqBB hqBBB]`. Establish `h4` using `congrArg Units.val h3`. Simplify using `only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, AlgHom.coe_toRingHom] at h4`.

Conclude with `h4`. Use `set U := ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) with hUdef`. Take `⟨δ, hδ⟩` from `GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A`. Take `⟨hmul, hone, -, -, -⟩` from `hδ B`. Establish `hδ1 : δ B 1 = 1`.

Use `hmul 1 1 (uCoc_one A B) (uCoc_one A B)` as an intermediate fact. Rewrite `this` using `[mul_one]`. Simplify using `using this`. Establish `hδpow : ∀ n : ℕ, δ B (U ^ n) = δ B U ^ n`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simpa using hδ1`. Consider the case `succ n ih => rw [pow_succ, hmul _ _ (uCoc_pow hUc n) hUc, ih, pow_succ]`. Establish `hδU : δ B U = 1` using `hp _ (by rw [← hδpow, hUq, hδ1])`. Take `⟨w, hw⟩` from `(hone U hUc).1 hδU`.

Set `iL : (B : Type) →ₐ[A] B ⊗[A] B` to `Algebra.TensorProduct.includeLeft`. Set `iR : (B : Type) →ₐ[A] B ⊗[A] B` to `Algebra.TensorProduct.includeRight`. Establish `hwU : U * Units.map iR.toRingHom.toMonoidHom w = Units.map iL.toRingHom.toMonoidHom w` using `Units.ext (by simpa [iL, iR] using hw)`. Establish `hWq : Units.map iL.toRingHom.toMonoidHom (w ^ q) = Units.map iR.toRingHom.toMonoidHom (w ^ q)`. Rewrite using `[map_pow, map_pow, ← hwU, mul_pow, hUq, one_mul]`.

Establish `hWq' : Units.map iL.toRingHom.toMonoidHom (w ^ q)⁻¹ = Units.map iR.toRingHom.toMonoidHom (w ^ q)⁻¹`. Rewrite using `[map_inv, map_inv, hWq]`. Take `⟨a, ha⟩` from `GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight A B ((w ^ q : (B : Type)ˣ) : (B : Type)) (by simpa [iL, iR] using congrArg Units.val hWq)`. Take `⟨a', ha'⟩` from `GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight A B (((w ^ q)⁻¹ : (B : Type)ˣ) : (B : Type)) (by simpa [iL, iR] using congrArg Units.val hWq')`. Establish `haa : a * a' = 1` using `FaithfulSMul.algebraMap_injective A B (by rw [map_mul, ha, ha', Units.mul_inv, map_one])`.

Take `⟨v, hv⟩` from `hu ⟨a, a', haa, by rw [mul_comm, haa]⟩`. Set `vB : (B : Type)ˣ` to `Units.map (algebraMap A B).toMonoidHom v`. Establish `hvB : vB ^ q = w ^ q`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[← map_pow, ← hv, Units.coe_map]`.

Conclude with `ha`. Establish `hT : (vB * w⁻¹) ^ q = 1` using `by rw [mul_pow, hvB, inv_pow, mul_inv_cancel]`. Set `Tr : rootsOfUnity q (B : Type)` to `⟨vB * w⁻¹, (mem_rootsOfUnity _ _).2 hT⟩`. Establish `hV : Units.map iR.toRingHom.toMonoidHom vB = Units.map iL.toRingHom.toMonoidHom vB`. Apply `Units.ext` to reduce the goal to its premises.

Simplify using `[vB, iL, iR]`. Use `⟨(e _ hqB).symm (Additive.ofMul Tr), ?_⟩` and prove the remaining obligations. Apply `(e _ hqBB).injective` to reduce the goal to its premises. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[map_sub, toMul_sub, SubgroupClass.coe_div, he _ _ _ hqB hqBB, he _ _ _ hqB hqBB, AddEquiv.apply_symm_apply]`. Express the relevant statement in the definitionally equal form `U = Units.map iR.toRingHom.toMonoidHom (vB * w⁻¹) / Units.map iL.toRingHom.toMonoidHom (vB * w⁻¹)`. Rewrite using `[div_eq_mul_inv, eq_mul_inv_iff_mul_eq, map_mul, map_mul, map_inv, map_inv, hV, ← hwU]`. Rewrite using `[mul_inv_rev, mul_left_comm, ← mul_assoc U, mul_comm U, mul_assoc, mul_inv_cancel, mul_one]`.
-/
theorem kummer_vanishing : B6h1 := by
  intro q _ A _ hq hu hp
  suffices h : ∀ x : Ht q (sp A) 1 1, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨Y, f, hfe, hfs, hx⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover (ZMod q) (Spec (CommRingCat.of A)) (tw q 1) 1 one_pos x
  obtain ⟨B, g, h, hg, hhf⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection (CommRingCat.of A) Y f hfe hfs
  letI : Algebra A B := g.hom.toAlgebra
  haveI : Algebra.Etale A B := hg.1
  haveI : Module.FaithfullyFlat A B := hg.2
  have hxB : pull (ZMod q) (spMap (algebraMap A B)) (tw q 1) 1 x = 0 := by
    have : spMap (algebraMap A B) = sch.map h ≫ sch.map f := by
      rw [← sch.map_comp, hhf]; rfl
    rw [this, pull_comp, hx, map_zero]
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.etale_cocycle_coboundary_iff (ZMod q) (tw q 1) A
  obtain ⟨hγ0, hγs, -, -⟩ := hγ B
  obtain ⟨u, rfl⟩ := hγs x hxB
  rw [hγ0]

  obtain ⟨e, he⟩ := GlobalTheory.T.tateTwistOne_sections_eq_rootsOfUnity q
  have hqB : IsUnit (q : (B : Type)) := by simpa using hq.map (algebraMap A B)
  have hqBB : IsUnit (q : B ⊗[A] B) := by simpa using hq.map (algebraMap A (B ⊗[A] B))
  have hqBBB : IsUnit (q : B ⊗[A] (B ⊗[A] B)) := by simpa using hq.map (algebraMap A (B ⊗[A] (B ⊗[A] B)))
  have hUq : ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) ^ q = 1 :=
    (mem_rootsOfUnity _ _).1 (Additive.toMul (e _ hqBB u.1)).2
  have hUc : UCoc A B ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) := by
    have h2 := u.2
    change _ = _ at h2
    have h3 := congrArg (fun y => ((Additive.toMul (e _ hqBBB y) : rootsOfUnity q _) : (B ⊗[A] (B ⊗[A] B))ˣ)) h2
    simp only [AddMonoidHom.add_apply, map_add, toMul_add, Subgroup.coe_mul, LinearMap.toAddMonoidHom_coe] at h3
    rw [he _ _ _ hqBB hqBBB, he _ _ _ hqBB hqBBB, he _ _ _ hqBB hqBBB] at h3
    have h4 := congrArg Units.val h3
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, AlgHom.coe_toRingHom] at h4
    exact h4

  set U := ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) with hUdef
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A
  obtain ⟨hmul, hone, -, -, -⟩ := hδ B
  have hδ1 : δ B 1 = 1 := by
    have := hmul 1 1 (uCoc_one A B) (uCoc_one A B)
    rw [mul_one] at this
    simpa using this
  have hδpow : ∀ n : ℕ, δ B (U ^ n) = δ B U ^ n := by
    intro n
    induction n with
    | zero => simpa using hδ1
    | succ n ih => rw [pow_succ, hmul _ _ (uCoc_pow hUc n) hUc, ih, pow_succ]
  have hδU : δ B U = 1 := hp _ (by rw [← hδpow, hUq, hδ1])
  obtain ⟨w, hw⟩ := (hone U hUc).1 hδU
  let iL : (B : Type) →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeLeft
  let iR : (B : Type) →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeRight
  have hwU : U * Units.map iR.toRingHom.toMonoidHom w = Units.map iL.toRingHom.toMonoidHom w :=
    Units.ext (by simpa [iL, iR] using hw)
  have hWq : Units.map iL.toRingHom.toMonoidHom (w ^ q) = Units.map iR.toRingHom.toMonoidHom (w ^ q) := by
    rw [map_pow, map_pow, ← hwU, mul_pow, hUq, one_mul]
  have hWq' : Units.map iL.toRingHom.toMonoidHom (w ^ q)⁻¹ = Units.map iR.toRingHom.toMonoidHom (w ^ q)⁻¹ := by
    rw [map_inv, map_inv, hWq]
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight A B ((w ^ q : (B : Type)ˣ) : (B : Type)) (by simpa [iL, iR] using congrArg Units.val hWq)
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight A B (((w ^ q)⁻¹ : (B : Type)ˣ) : (B : Type)) (by simpa [iL, iR] using congrArg Units.val hWq')
  have haa : a * a' = 1 :=
    FaithfulSMul.algebraMap_injective A B (by rw [map_mul, ha, ha', Units.mul_inv, map_one])
  obtain ⟨v, hv⟩ := hu ⟨a, a', haa, by rw [mul_comm, haa]⟩
  let vB : (B : Type)ˣ := Units.map (algebraMap A B).toMonoidHom v
  have hvB : vB ^ q = w ^ q := by
    apply Units.ext
    rw [← map_pow, ← hv, Units.coe_map]
    exact ha
  have hT : (vB * w⁻¹) ^ q = 1 := by rw [mul_pow, hvB, inv_pow, mul_inv_cancel]
  let Tr : rootsOfUnity q (B : Type) := ⟨vB * w⁻¹, (mem_rootsOfUnity _ _).2 hT⟩
  have hV : Units.map iR.toRingHom.toMonoidHom vB = Units.map iL.toRingHom.toMonoidHom vB := by
    apply Units.ext
    simp [vB, iL, iR]
  refine ⟨(e _ hqB).symm (Additive.ofMul Tr), ?_⟩
  apply (e _ hqBB).injective
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [map_sub, toMul_sub, SubgroupClass.coe_div, he _ _ _ hqB hqBB, he _ _ _ hqB hqBB, AddEquiv.apply_symm_apply]
  change U = Units.map iR.toRingHom.toMonoidHom (vB * w⁻¹) / Units.map iL.toRingHom.toMonoidHom (vB * w⁻¹)
  rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq, map_mul, map_mul, map_inv, map_inv, hV, ← hwU]
  rw [mul_inv_rev, mul_left_comm, ← mul_assoc U, mul_comm U, mul_assoc, mul_inv_cancel, mul_one]
end GlobalTheory.EtC
