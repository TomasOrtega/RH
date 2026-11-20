import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdealStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
open TensorProduct

namespace GlobalTheory.CompanionTheory.EtalePerfect

/- English proof (translation)
Use `algebraize [f]`. Establish `hint : Algebra.IsIntegral R S` using `⟨fun x => by`. Take `⟨r, hr⟩` from `hpow x`. Use `IsIntegral.of_pow hp.pos ?_` and prove the remaining obligations. Rewrite using `[← hr]`.

Conclude with `isIntegral_algebraMap⟩`. Establish `hfin : Module.Finite R S` using `Algebra.IsIntegral.finite`. Take `⟨t, ht2, ht1⟩` from `Algebra.FormallyUnramified.iff_exists_tensorProduct.1 (inferInstance : Algebra.FormallyUnramified R S)`. Establish `hT : (p : S ⊗[R] S) = 0`. Rewrite using `[← map_natCast (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S), hS, map_zero]`.

Establish `hadd : ∀ x y : S ⊗[R] S, (x + y) ^ p = x ^ p + y ^ p`. Introduce `x y`. Take `⟨c, hc⟩` from `exists_add_pow_prime_eq hp x y`. Rewrite using `[hc, hT]`. Simplify using the standard rewrite rules.

Establish `haddS : ∀ x y : S, (x + y) ^ p = x ^ p + y ^ p`. Introduce `x y`. Take `⟨c, hc⟩` from `exists_add_pow_prime_eq hp x y`. Rewrite using `[hc, hS]`. Simplify using the standard rewrite rules.

Establish `hfrob : ∀ u : S ⊗[R] S, u ^ p = ((Algebra.TensorProduct.lmul' R (S` using `S) u) ^ p) ⊗ₜ[R] (1 : S) := by`. Introduce `u`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp [zero_pow hp.ne_zero]`. Consider the case `tmul a b`.

Take `⟨s, hs⟩` from `hpow b`. Establish `hs' : b ^ p = s • (1 : S)`. Rewrite using `[← hs, Algebra.smul_def, mul_one]`. Both sides reduce to the same expression. Rewrite using `[Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.lmul'_apply_tmul, mul_pow, hs', TensorProduct.tmul_smul, mul_smul_comm, mul_one, TensorProduct.smul_tmul']`.

Consider the case `add x y hx hy`. Rewrite using `[hadd, hx, hy, map_add, haddS, TensorProduct.add_tmul]`. Establish `hmul : ∀ u : S ⊗[R] S, u * t = (Algebra.TensorProduct.lmul' R (S` using `S) u ⊗ₜ[R] (1 : S)) * t := by`. Introduce `u`. Proceed by induction on `u using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a b`. Establish `hb` using `ht2 b`. Rewrite `hb` using `[sub_mul, sub_eq_zero]`. Establish `: a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : S)) * ((1 : S) ⊗ₜ[R] b)` using `by simp`.

Rewrite using `[this, mul_assoc, hb, ← mul_assoc]`. Simplify using the standard rewrite rules. Consider the case `add x y hx hy`. Rewrite using `[add_mul, hx, hy, map_add, TensorProduct.add_tmul, add_mul]`. Establish `hidem : t * t = t`.

Rewrite using `[hmul t, ht1]`. Conclude with `one_mul t`. Establish `htp : t ^ p = t` using `(show IsIdempotentElem t from hidem).pow_eq hp.ne_zero`. Establish `ht : t = 1`. Rewrite using `[← htp, hfrob t, ht1, one_pow]`.

Both sides reduce to the same expression. Establish `hepi : Algebra.IsEpi R S`. Rewrite using `[Algebra.isEpi_iff_forall_one_tmul_eq]`. Introduce `s`. Use `ht2 s` as an intermediate fact.

Rewrite `this` using `[ht, mul_one, sub_eq_zero]`. Conclude with `this`. Conclude with `Algebra.isEpi_iff_surjective_algebraMap_of_finite.1 hepi`.
-/
theorem surjective_of_unramified {R S : Type} [CommRing R] [CommRing S] (p : ℕ) (hp : p.Prime)
    (hS : (p : S) = 0) (f : R →+* S) (hu : f.FormallyUnramified) (hft : f.FiniteType)
    (hpow : ∀ x : S, ∃ r, f r = x ^ p) : Function.Surjective f := by
  algebraize [f]
  have hint : Algebra.IsIntegral R S := ⟨fun x => by
    obtain ⟨r, hr⟩ := hpow x
    refine IsIntegral.of_pow hp.pos ?_
    rw [← hr]
    exact isIntegral_algebraMap⟩
  have hfin : Module.Finite R S := Algebra.IsIntegral.finite
  obtain ⟨t, ht2, ht1⟩ := Algebra.FormallyUnramified.iff_exists_tensorProduct.1
    (inferInstance : Algebra.FormallyUnramified R S)
  have hT : (p : S ⊗[R] S) = 0 := by
    rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S), hS, map_zero]
  have hadd : ∀ x y : S ⊗[R] S, (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, hT]
    simp
  have haddS : ∀ x y : S, (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, hS]
    simp
  have hfrob : ∀ u : S ⊗[R] S,
      u ^ p = ((Algebra.TensorProduct.lmul' R (S := S) u) ^ p) ⊗ₜ[R] (1 : S) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp [zero_pow hp.ne_zero]
    | tmul a b =>
      obtain ⟨s, hs⟩ := hpow b
      have hs' : b ^ p = s • (1 : S) := by
        rw [← hs, Algebra.smul_def, mul_one]; rfl
      rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.lmul'_apply_tmul, mul_pow, hs',
        TensorProduct.tmul_smul, mul_smul_comm, mul_one, TensorProduct.smul_tmul']
    | add x y hx hy =>
      rw [hadd, hx, hy, map_add, haddS, TensorProduct.add_tmul]
  have hmul : ∀ u : S ⊗[R] S,
      u * t = (Algebra.TensorProduct.lmul' R (S := S) u ⊗ₜ[R] (1 : S)) * t := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have hb := ht2 b
      rw [sub_mul, sub_eq_zero] at hb
      have : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : S)) * ((1 : S) ⊗ₜ[R] b) := by simp
      rw [this, mul_assoc, hb, ← mul_assoc]
      simp
    | add x y hx hy =>
      rw [add_mul, hx, hy, map_add, TensorProduct.add_tmul, add_mul]
  have hidem : t * t = t := by
    rw [hmul t, ht1]
    exact one_mul t
  have htp : t ^ p = t := (show IsIdempotentElem t from hidem).pow_eq hp.ne_zero
  have ht : t = 1 := by
    rw [← htp, hfrob t, ht1, one_pow]
    rfl
  have hepi : Algebra.IsEpi R S := by
    rw [Algebra.isEpi_iff_forall_one_tmul_eq]
    intro s
    have := ht2 s
    rw [ht, mul_one, sub_eq_zero] at this
    exact this
  exact Algebra.isEpi_iff_surjective_algebraMap_of_finite.1 hepi

/- English proof (translation)
Introduce `p hp P E _ _ ψ hψ hP`. Establish `hEc : (p : E) = 0` using `by rw [← map_natCast ψ, hP.char, map_zero]`. Establish `hadd : ∀ {A : Type} [CommRing A], (p : A) = 0 → ∀ x y : A, (x + y) ^ p = x ^ p + y ^ p`. Introduce `A _ h x y`. Take `⟨c, hc⟩` from `exists_add_pow_prime_eq hp x y`.

Rewrite using `[hc, h]`. Simplify using the standard rewrite rules. Set `φ : E →+* E` to `{ toFun := fun x => x ^ p map_one' := one_pow p map_mul' := fun x y => mul_pow x y p map_zero' := zero_pow hp.ne_zero map_add' := hadd hEc }`. Set `Fp : P →+* P` to `{ toFun := fun x => x ^ p map_one' := one_pow p map_mul' := fun x y => mul_pow x y p map_zero' := zero_pow hp.ne_zero map_add' := hadd hP.char }`. Set `e : P ≃+* P` to `RingEquiv.ofBijective Fp hP.bij`.

Set `G : P →+* P` to `e.symm.toRingHom`. Establish `hFG : ∀ x, (G x) ^ p = x` using `fun x => e.apply_symm_apply x`. Establish `hGF : ∀ x, G (x ^ p) = x` using `fun x => e.symm_apply_apply x`. Establish `hcomp : φ.comp (ψ.comp G) = ψ`. Use extensionality with `x`.

Express the relevant statement in the definitionally equal form `(ψ (G x)) ^ p = ψ x`. Rewrite using `[← map_pow, hFG]`. Establish `hUψ : ψ.FormallyUnramified` using `hψ.formallyUnramified`. Establish `hFTψ : ψ.FiniteType` using `by algebraize [ψ]`. Establish `: Algebra.Etale P E` using `hψ.toAlgebra`.

Conclude with `(inferInstance : Algebra.FiniteType P E)`. Establish `hu : φ.FormallyUnramified`. Rewrite `hUψ` using `[← hcomp]`. Conclude with `RingHom.FormallyUnramified.of_comp hUψ`. Establish `hft : φ.FiniteType`.

Rewrite `hFTψ` using `[← hcomp]`. Conclude with `RingHom.FiniteType.of_comp_finiteType hFTψ`. Establish `hsurj : Function.Surjective φ` using `surjective_of_unramified p hp hEc φ hu hft (fun x => ⟨x, rfl⟩)`. Set `N : Ideal E` to `RingHom.ker φ`. Establish `hN : ∀ x ∈ N, IsNilpotent x` using `fun x hx => ⟨p, hx⟩`.

Establish `hL : EtLift N` using `GlobalTheory.T.etale_lifting_of_nil_ideal N hN`. Set `eb : (E ⧸ N) ≃+* E` to `RingHom.quotientKerEquivOfSurjective hsurj`. Establish `heb : ∀ x, eb (Ideal.Quotient.mk N x) = x ^ p` using `fun x => rfl`. Set `g : E →+* E ⧸ N` to `eb.symm.toRingHom`. Establish `hg : ∀ x, g (x ^ p) = Ideal.Quotient.mk N x`.

Introduce `x`. Apply `eb.injective` to reduce the goal to its premises. Rewrite using `[heb]`. Conclude with `eb.apply_symm_apply _`. Establish `hgψ : g.comp ψ = (Ideal.Quotient.mk N).comp (ψ.comp G)`.

Use extensionality with `x`. Apply `eb.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `eb (eb.symm (ψ x)) = eb (Ideal.Quotient.mk N (ψ (G x)))`. Rewrite using `[eb.apply_symm_apply, heb, ← map_pow, hFG]`. Take `⟨h, ⟨hh1, hh2⟩, -⟩` from `hL P E ψ hψ (ψ.comp G) g hgψ`.

Establish `hid : h.comp φ = RingHom.id E`. Use `(hL P E ψ hψ ψ (Ideal.Quotient.mk N) rfl).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `h ((ψ x) ^ p) = ψ x`. Rewrite using `[← map_pow]`.

Use `RingHom.congr_fun hh1 (x ^ p)` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Rewrite using `[this, hGF]`. Use extensionality with `x`. Use `RingHom.congr_fun hh2 (x ^ p)` as an intermediate fact.

Simplify using `only [RingHom.comp_apply] at this`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk N (h (x ^ p)) = _`. Rewrite using `[this, hg]`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Use `⟨hEc, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`. Establish `hx` using `RingHom.congr_fun hid x`. Establish `hy` using `RingHom.congr_fun hid y`. Simplify using `only [RingHom.comp_apply, RingHom.id_apply] at hx hy`.

Rewrite using `[← hx, ← hy]`. Conclude with `congrArg h hxy`. Conclude with `hsurj`.
-/
theorem pf_of_etale : ∀ (p : ℕ), p.Prime → ∀ {P E : Type} [CommRing P] [CommRing E] (ψ : P →+* E),
    ψ.Etale → D.Pf p P → D.Pf p E := by
  intro p hp P E _ _ ψ hψ hP
  have hEc : (p : E) = 0 := by rw [← map_natCast ψ, hP.char, map_zero]
  have hadd : ∀ {A : Type} [CommRing A], (p : A) = 0 → ∀ x y : A, (x + y) ^ p = x ^ p + y ^ p := by
    intro A _ h x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, h]
    simp
  let φ : E →+* E :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := hadd hEc }
  let Fp : P →+* P :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := hadd hP.char }
  let e : P ≃+* P := RingEquiv.ofBijective Fp hP.bij
  let G : P →+* P := e.symm.toRingHom
  have hFG : ∀ x, (G x) ^ p = x := fun x => e.apply_symm_apply x
  have hGF : ∀ x, G (x ^ p) = x := fun x => e.symm_apply_apply x
  have hcomp : φ.comp (ψ.comp G) = ψ := by
    ext x
    change (ψ (G x)) ^ p = ψ x
    rw [← map_pow, hFG]
  have hUψ : ψ.FormallyUnramified := hψ.formallyUnramified
  have hFTψ : ψ.FiniteType := by
    algebraize [ψ]
    have : Algebra.Etale P E := hψ.toAlgebra
    exact (inferInstance : Algebra.FiniteType P E)
  have hu : φ.FormallyUnramified := by
    rw [← hcomp] at hUψ
    exact RingHom.FormallyUnramified.of_comp hUψ
  have hft : φ.FiniteType := by
    rw [← hcomp] at hFTψ
    exact RingHom.FiniteType.of_comp_finiteType hFTψ
  have hsurj : Function.Surjective φ :=
    surjective_of_unramified p hp hEc φ hu hft (fun x => ⟨x, rfl⟩)
  let N : Ideal E := RingHom.ker φ
  have hN : ∀ x ∈ N, IsNilpotent x := fun x hx => ⟨p, hx⟩
  have hL : EtLift N := GlobalTheory.T.etale_lifting_of_nil_ideal N hN
  let eb : (E ⧸ N) ≃+* E := RingHom.quotientKerEquivOfSurjective hsurj
  have heb : ∀ x, eb (Ideal.Quotient.mk N x) = x ^ p := fun x => rfl
  let g : E →+* E ⧸ N := eb.symm.toRingHom
  have hg : ∀ x, g (x ^ p) = Ideal.Quotient.mk N x := by
    intro x
    apply eb.injective
    rw [heb]
    exact eb.apply_symm_apply _
  have hgψ : g.comp ψ = (Ideal.Quotient.mk N).comp (ψ.comp G) := by
    ext x
    apply eb.injective
    change eb (eb.symm (ψ x)) = eb (Ideal.Quotient.mk N (ψ (G x)))
    rw [eb.apply_symm_apply, heb, ← map_pow, hFG]
  obtain ⟨h, ⟨hh1, hh2⟩, -⟩ := hL P E ψ hψ (ψ.comp G) g hgψ
  have hid : h.comp φ = RingHom.id E := by
    refine (hL P E ψ hψ ψ (Ideal.Quotient.mk N) rfl).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · ext x
      change h ((ψ x) ^ p) = ψ x
      rw [← map_pow]
      have := RingHom.congr_fun hh1 (x ^ p)
      simp only [RingHom.comp_apply] at this
      rw [this, hGF]
    · ext x
      have := RingHom.congr_fun hh2 (x ^ p)
      simp only [RingHom.comp_apply] at this
      change Ideal.Quotient.mk N (h (x ^ p)) = _
      rw [this, hg]
    · rfl
    · rfl
  refine ⟨hEc, ?_, ?_⟩
  · intro x y hxy
    have hx := RingHom.congr_fun hid x
    have hy := RingHom.congr_fun hid y
    simp only [RingHom.comp_apply, RingHom.id_apply] at hx hy
    rw [← hx, ← hy]
    exact congrArg h hxy
  · exact hsurj

end GlobalTheory.CompanionTheory.EtalePerfect
