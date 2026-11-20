import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceAdjoinRootMapStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFieldExistsGeneratorMinpolyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanPowersOfUniformizerOfNilpotentStatement
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.LocalTraceNonzero

/- English proof (translation)
Establish `hl` using `(Fact.out : l.Prime)`. Use `haveI : NeZero (l ^ b) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Rewrite `hx`, the goal using `[← ZMod.natCast_zmod_val x]`. Rewrite `hx` using `[map_natCast, ne_eq, ZMod.natCast_eq_zero_iff]`. Rewrite using `[ZMod.isUnit_iff_coprime]`.

Conclude with `Nat.Coprime.pow_right _ ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hx))`.
-/
theorem isUnit_of_cast_ne_zero (l b : ℕ) [Fact l.Prime] (hb : b ≠ 0) (x : ZMod (l ^ b))
    (hx : ZMod.castHom (dvd_pow_self l hb) (ZMod l) x ≠ 0) : IsUnit x := by
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ b) := ⟨pow_ne_zero _ hl.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x] at hx ⊢
  rw [map_natCast, ne_eq, ZMod.natCast_eq_zero_iff] at hx
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right _ ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hx))

/- English proof (translation)
Use `⟨fun f hf a₀ h₁ h₂ => ?_⟩` and prove the remaining obligations. Conclude with `HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)`.
-/
theorem henselian_of_finite (A : Type) [CommRing A] [Finite A] [IsLocalRing A] :
    HenselianLocalRing A := by
  refine ⟨fun f hf a₀ h₁ h₂ => ?_⟩
  exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

/- English proof (translation)
Use `haveI : Fact (Irreducible p) := ⟨hp⟩`. Use `haveI : FiniteDimensional (ZMod l) (AdjoinRoot p) := (AdjoinRoot.powerBasis hp.ne_zero).finite`. Use `haveI : Algebra.IsSeparable (ZMod l) (AdjoinRoot p) := inferInstance`. Take `⟨z, hz⟩` from `Algebra.trace_surjective (ZMod l) (AdjoinRoot p) 1`. Conclude with `⟨z, by rw [hz]; exact one_ne_zero⟩`.
-/
theorem exists_trace_ne_zero_adjoinRoot (l : ℕ) [Fact l.Prime] (p : (ZMod l)[X]) (hp : Irreducible p) :
    ∃ z : AdjoinRoot p, Algebra.trace (ZMod l) (AdjoinRoot p) z ≠ 0 := by
  haveI : Fact (Irreducible p) := ⟨hp⟩
  haveI : FiniteDimensional (ZMod l) (AdjoinRoot p) := (AdjoinRoot.powerBasis hp.ne_zero).finite
  haveI : Algebra.IsSeparable (ZMod l) (AdjoinRoot p) := inferInstance
  obtain ⟨z, hz⟩ := Algebra.trace_surjective (ZMod l) (AdjoinRoot p) 1
  exact ⟨z, by rw [hz]; exact one_ne_zero⟩

/- English proof (translation)
Introduce `l b e _ B _ _ _ π he hunit hspan hcard hdvd`. Establish `hb : b ≠ 0` using `by rintro rfl; exact hdvd (by simp)`. Establish `hl` using `(Fact.out : l.Prime)`. Use `haveI : Nontrivial B := by`. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Conclude with `(hunit 0).2 (dvd_zero π) (by rw [Subsingleton.elim (0 : B) 1]; exact isUnit_one)`. Establish `hnon : ∀ x : B, x ∈ nonunits B ↔ π ∣ x` using `fun x => hunit x`. Use `haveI : IsLocalRing B := IsLocalRing.of_nonunits_add (fun a c ha hc => (hnon _).2 (dvd_add ((hnon a).1 ha) ((hnon c).1 hc)))`. Establish `hmax : IsLocalRing.maximalIdeal B = Ideal.span {π}`.

Use extensionality with `x`. Rewrite using `[IsLocalRing.mem_maximalIdeal, hnon, Ideal.mem_span_singleton]`. Use `set K := IsLocalRing.ResidueField B`. Establish `hlmax : ((l : ℕ) : B) ∈ IsLocalRing.maximalIdeal B`. Rewrite using `[hmax, Ideal.mem_span_singleton]`.

Establish `: ((l : ℕ) : B) ∈ Ideal.span {π ^ e}` using `hspan ▸ Ideal.mem_span_singleton_self _`. Rewrite `this` using `[Ideal.mem_span_singleton]`. Conclude with `(dvd_pow_self π he.ne').trans this`. Use `haveI : CharP K l := by`. Rewrite using `[CharP.charP_iff_prime_eq_zero hl, ← map_natCast (IsLocalRing.residue B), IsLocalRing.residue_eq_zero_iff]`.

Conclude with `hlmax`. Use `letI : Algebra (ZMod l) K := ZMod.algebra K l`. Use `haveI : Finite K := Finite.of_surjective _ IsLocalRing.residue_surjective`. Take `⟨a, p, hpm, hpirr, hpa, hpa', hgen, hcardK⟩` from `GlobalTheory.T.exists_separable_generator_card_eq_pow_natDegree l K`. Use `set g : ZMod (l ^ b) →+* ZMod l := ZMod.castHom (dvd_pow_self l hb) (ZMod l) with hg`.

Establish `hgs : Function.Surjective g` using `ZMod.ringHom_surjective g`. Take `⟨h, hhp, hdeg, hmon⟩` from `lifts_and_natDegree_eq_and_monic ((mem_lifts p).2 (map_surjective g hgs p)) hpm`. Establish `hcomp : (algebraMap B K).comp (algebraMap (ZMod (l ^ b)) B) = (algebraMap (ZMod l) K).comp g` using `RingHom.ext_zmod _ _`. Establish `key : ∀ q : (ZMod (l ^ b))[X], aeval a (q.map (algebraMap (ZMod (l ^ b)) B)) = aeval a (q.map g)`. Introduce `q`.

Simplify using `only [aeval_def, eval₂_map, hcomp]`. Use `haveI : HenselianLocalRing B := henselian_of_finite B`. Establish `H2` using `((HenselianLocalRing.TFAE B).out 0 1).mp ‹_›`. Take `⟨ω, hω, hωa⟩` from `H2 (h.map (algebraMap _ B)) (hmon.map _) a (by rw [key, hhp]; exact hpa) (by rw [derivative_map, key, ← derivative_map, hhp]; exact hpa')`. Establish `hω' : eval₂ (algebraMap (ZMod (l ^ b)) B) ω h = 0`.

Rewrite using `[← eval_map]`. Conclude with `hω`. Use `set C := AdjoinRoot h`. Set `φ : C →+* B` to `AdjoinRoot.lift (algebraMap (ZMod (l ^ b)) B) ω hω'`. Establish `hsurj : ∀ x : B, ∃ y : C, x - φ y ∈ Ideal.span {π}`.

Introduce `x`. Take `⟨q, hq⟩` from `hgen (IsLocalRing.residue B x)`. Take `⟨q', rfl⟩` from `map_surjective g hgs q`. Use `⟨AdjoinRoot.mk h q', ?_⟩` and prove the remaining obligations. Rewrite using `[← hmax, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hq]`.

Use `show _ = IsLocalRing.residue B (AdjoinRoot.lift (algebraMap (ZMod (l ^ b)) B) ω hω' (AdjoinRoot.mk h q'))`. Rewrite using `[AdjoinRoot.lift_mk, hom_eval₂, hωa, ← key, aeval_def, eval₂_map]`. Both sides reduce to the same expression. Establish `hlb : ((l : ℕ) : B) ^ b = 0`. Rewrite using `[← Nat.cast_pow, ← map_natCast (algebraMap (ZMod (l ^ b)) B), ZMod.natCast_self, map_zero]`.

Establish `hpe : π ^ e ∈ Ideal.span {φ (l : C)}`. Rewrite using `[map_natCast, hspan]`. Conclude with `Ideal.mem_span_singleton_self _`. Establish `hE` using `GlobalTheory.T.exists_sum_mul_pow_of_residue_surjective_of_nilpotent C B φ π (l : C) e b hsurj hpe (by rw [map_natCast]; exact hlb)`. Use `letI : Algebra C B := φ.toAlgebra`.

Establish `hsmul : ∀ (c : C) (x : B), c • x = φ c * x` using `fun c x => Algebra.smul_def c x`. Set `T : (Fin e → C) →ₗ[C] B` to `Fintype.linearCombination C (fun j : Fin e => π ^ (j : ℕ))`. Establish `hTsurj : Function.Surjective T`. Introduce `x`. Take `⟨c, hc⟩` from `hE x`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearCombination_apply, hc]`. Simplify using `only [hsmul]`. Set `pb` to `AdjoinRoot.powerBasis' hmon`. Establish `hcardC : Nat.card C = (l ^ b) ^ p.natDegree`.

Rewrite using `[Nat.card_congr pb.basis.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, AdjoinRoot.powerBasis'_dim, hdeg]`. Establish `hcardB : Nat.card B = Nat.card (Fin e → C)`. Rewrite using `[Nat.card_fun, hcardC, Nat.card_eq_fintype_card (α := Fin e), Fintype.card_fin, hcard, ← hmax]`. Express the relevant statement in the definitionally equal form `Nat.card K ^ (b * e) = _`. Rewrite using `[hcardK, ← pow_mul, ← pow_mul, ← pow_mul]`.

Put the polynomial expressions in normal form. Use `haveI : NeZero (l ^ b) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Use `haveI : Module.Finite (ZMod (l ^ b)) C := pb.finite`. Use `haveI : Finite C := Module.finite_of_finite (ZMod (l ^ b))`. Establish `hTbij : Function.Bijective T` using `hTsurj.bijective_of_nat_card_le hcardB.ge`.

Set `bB : Module.Basis (Fin e) C B` to `Module.Basis.ofEquivFun (LinearEquiv.ofBijective T hTbij).symm`. Use `haveI : IsScalarTower (ZMod (l ^ b)) C B := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)`. Establish `htr : ∀ y : C, Algebra.trace (ZMod (l ^ b)) B (φ y) = (e : ZMod (l ^ b)) * Algebra.trace (ZMod (l ^ b)) C y`. Introduce `y`. Rewrite using `[← Algebra.trace_trace_of_basis pb.basis bB]`.

Express the relevant statement in the definitionally equal form `Algebra.trace (ZMod (l ^ b)) C (Algebra.trace C B (algebraMap C B y)) = _`. Rewrite using `[Algebra.trace_algebraMap_of_basis bB, map_nsmul, Fintype.card_fin, nsmul_eq_mul]`. Establish `hirr' : Irreducible (h.map g)` using `hhp ▸ hpirr`. Take `⟨z, hz⟩` from `exists_trace_ne_zero_adjoinRoot l (h.map g) hirr'`. Take `⟨q, rfl⟩` from `AdjoinRoot.mk_surjective z`.

Take `⟨q', rfl⟩` from `map_surjective g hgs q`. Establish `hmap : AdjoinRoot.map g h (h.map g) dvd_rfl (AdjoinRoot.mk h q') = AdjoinRoot.mk (h.map g) (q'.map g)`. Rewrite using `[AdjoinRoot.map, AdjoinRoot.lift_mk, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map, AdjoinRoot.algebraMap_eq]`. Establish `hu : IsUnit (Algebra.trace (ZMod (l ^ b)) C (AdjoinRoot.mk h q'))`. Apply `isUnit_of_cast_ne_zero l b hb` to reduce the goal to its premises.

Rewrite using `[← hg, GlobalTheory.T.map_trace_adjoinRoot_eq_trace_map _ _ g h hmon, hmap]`. Conclude with `hz`. Use `⟨φ (AdjoinRoot.mk h q'), ?_⟩` and prove the remaining obligations. Rewrite using `[htr]`. Introduce `h0`.

Conclude with `hdvd ((ZMod.natCast_eq_zero_iff _ _).1 (hu.mul_left_eq_zero.1 h0))`.
-/
theorem exists_trace_ne_zero : ∀ (l b e : ℕ) [Fact l.Prime] (B : Type) [CommRing B] [Finite B] [Algebra (ZMod (l ^ b)) B] (π : B), 0 < e → (∀ x : B, ¬ IsUnit x ↔ π ∣ x) → Ideal.span {((l : ℕ) : B)} = Ideal.span {π ^ e} → Nat.card B = Nat.card (B ⧸ Ideal.span {π}) ^ (b * e) → ¬ l ^ b ∣ e → ∃ c : B, Algebra.trace (ZMod (l ^ b)) B c ≠ 0 := by
  intro l b e _ B _ _ _ π he hunit hspan hcard hdvd
  have hb : b ≠ 0 := by rintro rfl; exact hdvd (by simp)
  have hl := (Fact.out : l.Prime)
  haveI : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (hunit 0).2 (dvd_zero π) (by rw [Subsingleton.elim (0 : B) 1]; exact isUnit_one)
  have hnon : ∀ x : B, x ∈ nonunits B ↔ π ∣ x := fun x => hunit x
  haveI : IsLocalRing B := IsLocalRing.of_nonunits_add
    (fun a c ha hc => (hnon _).2 (dvd_add ((hnon a).1 ha) ((hnon c).1 hc)))
  have hmax : IsLocalRing.maximalIdeal B = Ideal.span {π} := by
    ext x; rw [IsLocalRing.mem_maximalIdeal, hnon, Ideal.mem_span_singleton]
  set K := IsLocalRing.ResidueField B
  have hlmax : ((l : ℕ) : B) ∈ IsLocalRing.maximalIdeal B := by
    rw [hmax, Ideal.mem_span_singleton]
    have : ((l : ℕ) : B) ∈ Ideal.span {π ^ e} := hspan ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton] at this
    exact (dvd_pow_self π he.ne').trans this
  haveI : CharP K l := by
    rw [CharP.charP_iff_prime_eq_zero hl, ← map_natCast (IsLocalRing.residue B),
      IsLocalRing.residue_eq_zero_iff]
    exact hlmax
  letI : Algebra (ZMod l) K := ZMod.algebra K l
  haveI : Finite K := Finite.of_surjective _ IsLocalRing.residue_surjective
  obtain ⟨a, p, hpm, hpirr, hpa, hpa', hgen, hcardK⟩ := GlobalTheory.T.exists_separable_generator_card_eq_pow_natDegree l K
  set g : ZMod (l ^ b) →+* ZMod l := ZMod.castHom (dvd_pow_self l hb) (ZMod l) with hg
  have hgs : Function.Surjective g := ZMod.ringHom_surjective g
  obtain ⟨h, hhp, hdeg, hmon⟩ :=
    lifts_and_natDegree_eq_and_monic ((mem_lifts p).2 (map_surjective g hgs p)) hpm
  have hcomp : (algebraMap B K).comp (algebraMap (ZMod (l ^ b)) B) =
      (algebraMap (ZMod l) K).comp g := RingHom.ext_zmod _ _
  have key : ∀ q : (ZMod (l ^ b))[X],
      aeval a (q.map (algebraMap (ZMod (l ^ b)) B)) = aeval a (q.map g) := by
    intro q
    simp only [aeval_def, eval₂_map, hcomp]
  haveI : HenselianLocalRing B := henselian_of_finite B
  have H2 := ((HenselianLocalRing.TFAE B).out 0 1).mp ‹_›
  obtain ⟨ω, hω, hωa⟩ := H2 (h.map (algebraMap _ B)) (hmon.map _) a
    (by rw [key, hhp]; exact hpa)
    (by rw [derivative_map, key, ← derivative_map, hhp]; exact hpa')
  have hω' : eval₂ (algebraMap (ZMod (l ^ b)) B) ω h = 0 := by
    rw [← eval_map]; exact hω

  set C := AdjoinRoot h
  let φ : C →+* B := AdjoinRoot.lift (algebraMap (ZMod (l ^ b)) B) ω hω'
  have hsurj : ∀ x : B, ∃ y : C, x - φ y ∈ Ideal.span {π} := by
    intro x
    obtain ⟨q, hq⟩ := hgen (IsLocalRing.residue B x)
    obtain ⟨q', rfl⟩ := map_surjective g hgs q
    refine ⟨AdjoinRoot.mk h q', ?_⟩
    rw [← hmax, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hq]
    show _ = IsLocalRing.residue B (AdjoinRoot.lift (algebraMap (ZMod (l ^ b)) B) ω hω' (AdjoinRoot.mk h q'))
    rw [AdjoinRoot.lift_mk, hom_eval₂, hωa, ← key, aeval_def, eval₂_map]
    rfl
  have hlb : ((l : ℕ) : B) ^ b = 0 := by
    rw [← Nat.cast_pow, ← map_natCast (algebraMap (ZMod (l ^ b)) B), ZMod.natCast_self, map_zero]
  have hpe : π ^ e ∈ Ideal.span {φ (l : C)} := by
    rw [map_natCast, hspan]; exact Ideal.mem_span_singleton_self _
  have hE := GlobalTheory.T.exists_sum_mul_pow_of_residue_surjective_of_nilpotent C B φ π (l : C) e b hsurj hpe (by rw [map_natCast]; exact hlb)

  letI : Algebra C B := φ.toAlgebra
  have hsmul : ∀ (c : C) (x : B), c • x = φ c * x := fun c x => Algebra.smul_def c x
  let T : (Fin e → C) →ₗ[C] B := Fintype.linearCombination C (fun j : Fin e => π ^ (j : ℕ))
  have hTsurj : Function.Surjective T := by
    intro x
    obtain ⟨c, hc⟩ := hE x
    refine ⟨c, ?_⟩
    rw [Fintype.linearCombination_apply, hc]
    simp only [hsmul]
  let pb := AdjoinRoot.powerBasis' hmon
  have hcardC : Nat.card C = (l ^ b) ^ p.natDegree := by
    rw [Nat.card_congr pb.basis.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin, AdjoinRoot.powerBasis'_dim, hdeg]
  have hcardB : Nat.card B = Nat.card (Fin e → C) := by
    rw [Nat.card_fun, hcardC, Nat.card_eq_fintype_card (α := Fin e), Fintype.card_fin, hcard, ← hmax]
    change Nat.card K ^ (b * e) = _
    rw [hcardK, ← pow_mul, ← pow_mul, ← pow_mul]
    ring_nf
  haveI : NeZero (l ^ b) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Module.Finite (ZMod (l ^ b)) C := pb.finite
  haveI : Finite C := Module.finite_of_finite (ZMod (l ^ b))
  have hTbij : Function.Bijective T := hTsurj.bijective_of_nat_card_le hcardB.ge
  let bB : Module.Basis (Fin e) C B := Module.Basis.ofEquivFun (LinearEquiv.ofBijective T hTbij).symm
  haveI : IsScalarTower (ZMod (l ^ b)) C B := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have htr : ∀ y : C, Algebra.trace (ZMod (l ^ b)) B (φ y) = (e : ZMod (l ^ b)) * Algebra.trace (ZMod (l ^ b)) C y := by
    intro y
    rw [← Algebra.trace_trace_of_basis pb.basis bB]
    change Algebra.trace (ZMod (l ^ b)) C (Algebra.trace C B (algebraMap C B y)) = _
    rw [Algebra.trace_algebraMap_of_basis bB, map_nsmul, Fintype.card_fin, nsmul_eq_mul]

  have hirr' : Irreducible (h.map g) := hhp ▸ hpirr
  obtain ⟨z, hz⟩ := exists_trace_ne_zero_adjoinRoot l (h.map g) hirr'
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨q', rfl⟩ := map_surjective g hgs q
  have hmap : AdjoinRoot.map g h (h.map g) dvd_rfl (AdjoinRoot.mk h q') =
      AdjoinRoot.mk (h.map g) (q'.map g) := by
    rw [AdjoinRoot.map, AdjoinRoot.lift_mk, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map,
      AdjoinRoot.algebraMap_eq]
  have hu : IsUnit (Algebra.trace (ZMod (l ^ b)) C (AdjoinRoot.mk h q')) := by
    apply isUnit_of_cast_ne_zero l b hb
    rw [← hg, GlobalTheory.T.map_trace_adjoinRoot_eq_trace_map _ _ g h hmon, hmap]; exact hz
  refine ⟨φ (AdjoinRoot.mk h q'), ?_⟩
  rw [htr]
  intro h0
  exact hdvd ((ZMod.natCast_eq_zero_iff _ _).1 (hu.mul_left_eq_zero.1 h0))

end GlobalTheory.LocalTraceNonzero
