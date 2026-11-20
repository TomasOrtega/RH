import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmTypeEmbeddingsIntoValuationRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjEqNegOfSqEqNegNat

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.FrobOrbit

/- English proof (translation)
Set `g : (A →+* k) → (A →ₗ[ℤ] k)` to `fun f => f.toAddMonoidHom.toIntLinearMap`. Establish `hli : LinearIndependent k g`. Apply `LinearIndependent.of_comp (LinearMap.ltoFun ℤ A k k)` to reduce the goal to its premises. Conclude with `(linearIndependent_monoidHom A k).comp (fun f : A →+* k => f.toMonoidHom) (fun f f' h => RingHom.ext fun a => DFunLike.congr_fun h a)`. Set `e` to `(Module.Free.chooseBasis ℤ A).constr (M' := k) k`.

Establish `: Module.Finite k (A →ₗ[ℤ] k)` using `Module.Finite.equiv e`. Use `hli.finite` as an intermediate fact. Use `Fintype.ofFinite (A →+* k)` as an intermediate fact. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_eq_fintype_card]`.

Use `hli.fintype_card_le_finrank.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← e.finrank_eq, Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_chooseBasisIndex]`.
-/
theorem card_ringHom_le (A k : Type) [CommRing A] [Module.Free ℤ A] [Module.Finite ℤ A] [Field k] :
    Finite (A →+* k) ∧ Nat.card (A →+* k) ≤ Module.finrank ℤ A := by
  let g : (A →+* k) → (A →ₗ[ℤ] k) := fun f => f.toAddMonoidHom.toIntLinearMap
  have hli : LinearIndependent k g := by
    apply LinearIndependent.of_comp (LinearMap.ltoFun ℤ A k k)
    exact (linearIndependent_monoidHom A k).comp (fun f : A →+* k => f.toMonoidHom)
      (fun f f' h => RingHom.ext fun a => DFunLike.congr_fun h a)
  let e := (Module.Free.chooseBasis ℤ A).constr (M' := k) k
  have : Module.Finite k (A →ₗ[ℤ] k) := Module.Finite.equiv e
  have := hli.finite
  have := Fintype.ofFinite (A →+* k)
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_eq_fintype_card]
  refine hli.fintype_card_le_finrank.trans (le_of_eq ?_)
  rw [← e.finrank_eq, Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_chooseBasisIndex]

/- English proof (translation)
Set `: Algebra (ZMod p) k` to `ZMod.algebra k p`. Establish `hinj : Function.Injective (fun s : Fin (Module.finrank (ZMod p) F) => (iterateFrobenius k p s).comp ψ)`. Introduce `s t hst`. Apply `(FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F).1` to reduce the goal to its premises. Use extensionality with `x`.

Use `DFunLike.congr_fun hst x` as an intermediate fact. Simplify using `only [RingHom.comp_apply, iterateFrobenius_def, ← map_pow] at this`. Establish `h2` using `ψ.injective this`. Simplify using `only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]`. Conclude with `h2`.

Set `e : (F →+* k) → (F →ₐ[ZMod p] k)` to `fun f => { f with commutes' := fun r => DFunLike.congr_fun (Subsingleton.elim (f.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) k)) r }`. Establish `he : Function.Injective e` using `fun f f' h => RingHom.ext fun a => DFunLike.congr_fun h a`. Establish `: Finite (F →+* k)` using `Finite.of_injective e he`. Use `hinj.bijective_of_nat_card_le ?_` and prove the remaining obligations. Rewrite using `[Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]`.

Conclude with `(Nat.card_le_card_of_injective e he).trans (by simpa using card_algHom_le_finrank (ZMod p) F k)`.
-/
theorem bijective_frob_twist (F k : Type) [Field F] [Finite F] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    [Algebra (ZMod p) F] (ψ : F →+* k) :
    Function.Bijective (fun s : Fin (Module.finrank (ZMod p) F) => (iterateFrobenius k p s).comp ψ) := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  have hinj : Function.Injective (fun s : Fin (Module.finrank (ZMod p) F) => (iterateFrobenius k p s).comp ψ) := by
    intro s t hst
    apply (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F).1
    ext x
    have := DFunLike.congr_fun hst x
    simp only [RingHom.comp_apply, iterateFrobenius_def, ← map_pow] at this
    have h2 := ψ.injective this
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
    exact h2
  let e : (F →+* k) → (F →ₐ[ZMod p] k) := fun f =>
    { f with
      commutes' := fun r =>
        DFunLike.congr_fun (Subsingleton.elim (f.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) k)) r }
  have he : Function.Injective e := fun f f' h => RingHom.ext fun a => DFunLike.congr_fun h a
  have : Finite (F →+* k) := Finite.of_injective e he
  refine hinj.bijective_of_nat_card_le ?_
  rw [Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]
  exact (Nat.card_le_card_of_injective e he).trans (by simpa using card_algHom_le_finrank (ZMod p) F k)

/- English proof (translation)
Establish `: (RingHom.ker ψ).IsPrime` using `RingHom.ker_isPrime ψ`. Set `: Field (A ⧸ RingHom.ker ψ)` to `(Finite.isField_of_domain _).toField`. Set `ψ' : A ⧸ RingHom.ker ψ →+* k` to `RingHom.kerLift ψ`. Establish `hψ : ψ'.comp (Ideal.Quotient.mk _) = ψ` using `RingHom.ext fun a => RingHom.kerLift_mk ψ a`. Establish `: CharP (A ⧸ RingHom.ker ψ) p` using `(RingHom.charP_iff_charP ψ' p).2 inferInstance`.

Set `: Algebra (ZMod p) (A ⧸ RingHom.ker ψ)` to `ZMod.algebra _ p`. Use `Fintype.ofFinite (A ⧸ RingHom.ker ψ)` as an intermediate fact. Establish `hb` using `bijective_frob_twist (A ⧸ RingHom.ker ψ) k p ψ'`. Establish `hc : Fintype.card (A ⧸ RingHom.ker ψ) = p ^ Module.finrank (ZMod p) (A ⧸ RingHom.ker ψ)`. Rewrite using `[Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]`.

Use `⟨Module.finrank (ZMod p) (A ⧸ RingHom.ker ψ), Module.finrank_pos, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_eq_fintype_card, hc]`. Use extensionality with `a`. Rewrite using `[RingHom.comp_apply, iterateFrobenius_def, ← hc, ← RingHom.kerLift_mk ψ a, ← map_pow, FiniteField.pow_card]`. Introduce `s t hs ht hst`.

Establish `: (⟨s, hs⟩ : Fin _) = ⟨t, ht⟩`. Apply `hb.1` to reduce the goal to its premises. Apply `Ideal.Quotient.ringHom_ext` to reduce the goal to its premises. Simplify `hst` using `only [RingHom.comp_assoc, hψ]`. Conclude with `congrArg Fin.val this`.

Introduce `φ`. Prove the components needed by the constructor for the conclusion. Introduce `hφ`. Take `⟨s, hs⟩` from `hb.2 (Ideal.Quotient.lift _ φ (fun a ha => by rwa [← hφ] at ha))`. Use `⟨s, s.2, ?_⟩` and prove the remaining obligations.

Use `congrArg (fun f => RingHom.comp f (Ideal.Quotient.mk (RingHom.ker ψ))) hs` as an intermediate fact. Simplify using `only [RingHom.comp_assoc, hψ] at this`. Rewrite using `[this]`. Use extensionality with `a`. Both sides reduce to the same expression.

Introduce and unpack `⟨s, -, rfl⟩`. Use extensionality with `a`. Simplify using `[RingHom.mem_ker]`.
-/
theorem orbit_of_ker (A k : Type) [CommRing A] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (ψ : A →+* k)
    [Finite (A ⧸ RingHom.ker ψ)] :
    ∃ h : ℕ, 0 < h ∧ Nat.card (A ⧸ RingHom.ker ψ) = p ^ h ∧ (iterateFrobenius k p h).comp ψ = ψ ∧
      (∀ s t, s < h → t < h → (iterateFrobenius k p s).comp ψ = (iterateFrobenius k p t).comp ψ → s = t) ∧
      ∀ φ : A →+* k, RingHom.ker φ = RingHom.ker ψ ↔ ∃ s < h, (iterateFrobenius k p s).comp ψ = φ := by
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  let : Field (A ⧸ RingHom.ker ψ) := (Finite.isField_of_domain _).toField
  let ψ' : A ⧸ RingHom.ker ψ →+* k := RingHom.kerLift ψ
  have hψ : ψ'.comp (Ideal.Quotient.mk _) = ψ := RingHom.ext fun a => RingHom.kerLift_mk ψ a
  have : CharP (A ⧸ RingHom.ker ψ) p := (RingHom.charP_iff_charP ψ' p).2 inferInstance
  let : Algebra (ZMod p) (A ⧸ RingHom.ker ψ) := ZMod.algebra _ p
  have := Fintype.ofFinite (A ⧸ RingHom.ker ψ)
  have hb := bijective_frob_twist (A ⧸ RingHom.ker ψ) k p ψ'
  have hc : Fintype.card (A ⧸ RingHom.ker ψ) = p ^ Module.finrank (ZMod p) (A ⧸ RingHom.ker ψ) := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  refine ⟨Module.finrank (ZMod p) (A ⧸ RingHom.ker ψ), Module.finrank_pos, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, hc]
  · ext a
    rw [RingHom.comp_apply, iterateFrobenius_def, ← hc, ← RingHom.kerLift_mk ψ a, ← map_pow, FiniteField.pow_card]
  · intro s t hs ht hst
    have : (⟨s, hs⟩ : Fin _) = ⟨t, ht⟩ := by
      apply hb.1
      apply Ideal.Quotient.ringHom_ext
      simpa only [RingHom.comp_assoc, hψ] using hst
    exact congrArg Fin.val this
  · intro φ
    constructor
    · intro hφ
      obtain ⟨s, hs⟩ := hb.2 (Ideal.Quotient.lift _ φ (fun a ha => by rwa [← hφ] at ha))
      refine ⟨s, s.2, ?_⟩
      have := congrArg (fun f => RingHom.comp f (Ideal.Quotient.mk (RingHom.ker ψ))) hs
      simp only [RingHom.comp_assoc, hψ] at this
      rw [this]
      ext a
      rfl
    · rintro ⟨s, -, rfl⟩
      ext a
      simp [RingHom.mem_ker]

/- English proof (translation)
Introduce `τ τ' h`. Assume the negation of the conclusion as `hne`. Set `b : (E →+* ℂ) → 𝓞 E` to `fun i => RingOfIntegers.basis E (equivReindex E i)`. Set `M : Matrix (E →+* ℂ) (E →+* ℂ) F` to `Matrix.of fun i σ => u σ (b i)`. Establish `hM : ι.mapMatrix M = basisMatrix E`.

Use extensionality with `i σ`. Simplify using `only [basisMatrix, Matrix.of_apply, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]`. Conclude with `hu σ _`. Establish `hdet : M.det ^ 2 = (discr E : F)`. Apply `ι.injective` to reduce the goal to its premises.

Rewrite using `[map_pow, RingHom.map_det, hM, map_intCast, discr_eq_basisMatrix_det_sq]`. Set `N : Matrix (E →+* ℂ) (E →+* ℂ) R` to `Matrix.of fun i σ => t σ (b i)`. Establish `hN : N.det ^ 2 = (discr E : R)`. Apply `hR` to reduce the goal to its premises. Establish `: (algebraMap R K).mapMatrix N = j.mapMatrix M`.

Use extensionality with `i σ`. Conclude with `ht σ _`. Rewrite using `[map_pow, RingHom.map_det, this, ← RingHom.map_det, ← map_pow, hdet, map_intCast, map_intCast]`. Establish `h0 : (r.mapMatrix N).det = 0` using `Matrix.det_zero_of_column_eq hne fun i => DFunLike.congr_fun h (b i)`. Establish `h1 : (discr E : k) = 0`.

Rewrite using `[← map_intCast r, ← hN, map_pow, RingHom.map_det, h0]`. Simplify using the standard rewrite rules. Conclude with `hd ((CharP.intCast_eq_zero_iff k p _).1 h1)`.
-/
theorem injective_of_det {E k : Type} [Field E] [NumberField E] [Field k] (p : ℕ) [CharP k p]
    (hd : ¬ (p : ℤ) ∣ discr E) {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (hR : Function.Injective (algebraMap R K))
    (r : R →+* k) {F : Type} [Field F] (ι : F →+* ℂ) (j : F →+* K)
    (u : (E →+* ℂ) → (𝓞 E →+* F)) (hu : ∀ τ a, ι (u τ a) = τ (a : E))
    (t : (E →+* ℂ) → (𝓞 E →+* R)) (ht : ∀ τ a, algebraMap R K (t τ a) = j (u τ a)) :
    Function.Injective fun τ => r.comp (t τ) := by
  classical
  intro τ τ' h
  by_contra hne
  let b : (E →+* ℂ) → 𝓞 E := fun i => RingOfIntegers.basis E (equivReindex E i)
  let M : Matrix (E →+* ℂ) (E →+* ℂ) F := Matrix.of fun i σ => u σ (b i)
  have hM : ι.mapMatrix M = basisMatrix E := by
    ext i σ
    simp only [basisMatrix, Matrix.of_apply, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
    exact hu σ _
  have hdet : M.det ^ 2 = (discr E : F) := by
    apply ι.injective
    rw [map_pow, RingHom.map_det, hM, map_intCast, discr_eq_basisMatrix_det_sq]
  let N : Matrix (E →+* ℂ) (E →+* ℂ) R := Matrix.of fun i σ => t σ (b i)
  have hN : N.det ^ 2 = (discr E : R) := by
    apply hR
    have : (algebraMap R K).mapMatrix N = j.mapMatrix M := by
      ext i σ
      exact ht σ _
    rw [map_pow, RingHom.map_det, this, ← RingHom.map_det, ← map_pow, hdet, map_intCast, map_intCast]
  have h0 : (r.mapMatrix N).det = 0 :=
    Matrix.det_zero_of_column_eq hne fun i => DFunLike.congr_fun h (b i)
  have h1 : (discr E : k) = 0 := by
    rw [← map_intCast r, ← hN, map_pow, RingHom.map_det, h0]; simp
  exact hd ((CharP.intCast_eq_zero_iff k p _).1 h1)

/- English proof (translation)
Set `f : ZMod p →+* k` to `ZMod.castHom (dvd_refl p) k`. Establish `hodd : p = 2 * (p / 2) + 1`. Use `(Fact.out : p.Prime).eq_two_or_odd` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hpow : r ^ p = f ((-(d : ZMod p)) ^ (p / 2)) * r`.

Rewrite using `[map_pow, map_neg, map_natCast, ← hr, ← pow_mul, ← pow_succ, ← hodd]`. Establish `hd' : -(d : ZMod p) ≠ 0` using `neg_ne_zero.2 hd`. Use `⟨fun h => ?_, fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Establish `h2 : (2 : k) ≠ 0`. Introduce `h2`.

Use `(CharP.cast_eq_zero_iff k p 2).1 (by exact_mod_cast h2)` as an intermediate fact. Conclude with `hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)`. Establish `h3 : r = 0`. Establish `: 2 * r = 0` using `by linear_combination h`. Conclude with `(mul_eq_zero.1 this).resolve_left h2`.

Apply `hd'` to reduce the goal to its premises. Apply `f.injective` to reduce the goal to its premises. Rewrite using `[map_neg, map_natCast, ← hr, h3, map_zero]`. Simplify using the standard rewrite rules. Rewrite using `[hpow, (ZMod.euler_criterion p hd').1 h, map_one, one_mul]`.

Break down `ZMod.pow_div_two_eq_neg_one_or_one p hd' with h1 | h1` into its components or cases. Conclude with `absurd ((ZMod.euler_criterion p hd').2 h1) h`. Rewrite using `[hpow, h1, map_neg, map_one, neg_one_mul]`.
-/
theorem pow_char_sqrt {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : p ≠ 2) (d : ℕ)
    (hd : (d : ZMod p) ≠ 0) {r : k} (hr : r ^ 2 = -(d : k)) :
    r ≠ -r ∧ (IsSquare (-(d : ZMod p)) → r ^ p = r) ∧ (¬ IsSquare (-(d : ZMod p)) → r ^ p = -r) := by
  let f : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
  have hodd : p = 2 * (p / 2) + 1 := by
    have := (Fact.out : p.Prime).eq_two_or_odd
    omega
  have hpow : r ^ p = f ((-(d : ZMod p)) ^ (p / 2)) * r := by
    rw [map_pow, map_neg, map_natCast, ← hr, ← pow_mul, ← pow_succ, ← hodd]
  have hd' : -(d : ZMod p) ≠ 0 := neg_ne_zero.2 hd
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h2 : (2 : k) ≠ 0 := by
      intro h2
      have := (CharP.cast_eq_zero_iff k p 2).1 (by exact_mod_cast h2)
      exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
    have h3 : r = 0 := by
      have : 2 * r = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_left h2
    apply hd'
    apply f.injective
    rw [map_neg, map_natCast, ← hr, h3, map_zero]; simp
  · rw [hpow, (ZMod.euler_criterion p hd').1 h, map_one, one_mul]
  · rcases ZMod.pow_div_two_eq_neg_one_or_one p hd' with h1 | h1
    · exact absurd ((ZMod.euler_criterion p hd').2 h1) h
    · rw [hpow, h1, map_neg, map_one, neg_one_mul]

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)

/- English proof (translation)
Use `congrArg (σ.comp (algebraMap (𝓞 E) E)) H.rt_sq` as an intermediate fact. Rewrite `this` using `[map_pow, map_neg, map_natCast]`. Conclude with `this`.
-/
theorem emb_rt_sq (σ : E →+* ℂ) : σ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
  have := congrArg (σ.comp (algebraMap (𝓞 E) E)) H.rt_sq
  rw [map_pow, map_neg, map_natCast] at this
  exact this

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ConjugateNegativeSquare.conjugate_rt`. Consider the case `exact _root_.GlobalTheory.ConjugateNegativeSquare.conjugate_rt`. Consider the case `(apply _root_.GlobalTheory.ConjugateNegativeSquare.conjugate_rt <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ConjugateNegativeSquare.conjugate_rt <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ConjugateNegativeSquare.conjugate_rt <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ConjugateNegativeSquare.conjugate_rt ..)`.
-/
theorem conj_rt (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ (H.rt : E) = -σ (H.rt : E) := by
  first
  | exact @_root_.GlobalTheory.ConjugateNegativeSquare.conjugate_rt
  | exact _root_.GlobalTheory.ConjugateNegativeSquare.conjugate_rt
  | (apply _root_.GlobalTheory.ConjugateNegativeSquare.conjugate_rt <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateNegativeSquare.conjugate_rt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateNegativeSquare.conjugate_rt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateNegativeSquare.conjugate_rt ..)

/- English proof (translation)
Take `⟨n, hn⟩ : ∃ n, H.d + 1 = 8 * n` from `⟨(H.d + 1) / 8, by have := H.d_mod; omega⟩`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h1 : (H.d : 𝓞 E) + 1 = 8 * n` using `by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) hn`. Establish `h4 : (4 : 𝓞 E) ≠ 0` using `by norm_num`. Apply `mul_left_cancel₀ h4` to reduce the goal to its premises.

Establish `h2` using `H.rt_sq`. Establish `h3` using `H.two_weight_eq_one_add_root`. Take the linear combination `(2 * H.w0 + H.rt - 1) * h3 + h2 - h1`.
-/
theorem cm_generator_sq_quadratic_eq : ∃ m : 𝓞 E, H.w0 ^ 2 = H.w0 - 2 * m := by
  obtain ⟨n, hn⟩ : ∃ n, H.d + 1 = 8 * n := ⟨(H.d + 1) / 8, by have := H.d_mod; omega⟩
  refine ⟨n, ?_⟩
  have h1 : (H.d : 𝓞 E) + 1 = 8 * n := by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) hn
  have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  have h2 := H.rt_sq
  have h3 := H.two_weight_eq_one_add_root
  linear_combination (2 * H.w0 + H.rt - 1) * h3 + h2 - h1

/- English proof (translation)
Establish `hor : σ' (H.rt : E) = σ (H.rt : E) ∨ σ' (H.rt : E) = -σ (H.rt : E)` using `sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [emb_rt_sq, emb_rt_sq])`. Establish `hr : ψ σ H.rt ^ 2 = -(H.d : k)` using `by rw [← map_pow, H.rt_sq, map_neg, map_natCast]`. Prove the components needed by the constructor for the conclusion. Introduce `hs`. Use `hor.resolve_right fun hneg => ?_` and prove the remaining obligations.

Distinguish the cases in `hp : p = 2`. Substitute `hp` using the available equality. Establish `e : ∀ τ : E →+* ℂ, 2 * τ (H.w0 : E) = 1 + τ (H.rt : E)` using `fun τ => by`. Use `congrArg (τ.comp (algebraMap (𝓞 E) E)) H.two_weight_eq_one_add_root` as an intermediate fact. Rewrite `this` using `[map_mul, map_add, map_one, map_ofNat]`.

Conclude with `this`. Establish `h1 : ψ σ' H.w0 = ψ σ (1 - H.w0)`. Apply `hψ` to reduce the goal to its premises. Establish `: σ ((1 - H.w0 : 𝓞 E) : E) = 1 - σ (H.w0 : E)`. Use `map_sub (σ.comp (algebraMap (𝓞 E) E)) 1 H.w0` as an intermediate fact.

Rewrite `this` using `[map_one]`. Conclude with `this`. Rewrite using `[this]`. Take the linear combination `(1 / 2 : ℂ) * (e σ + e σ' + hneg)`. Take `⟨m, hm⟩` from `cm_generator_sq_quadratic_eq H`.

Establish `h2 : (2 : k) = 0` using `by exact_mod_cast CharP.cast_eq_zero k 2`. Rewrite `h1` using `[h, ← map_pow, hm, map_sub, map_sub, map_mul, map_one, map_ofNat]`. Establish `: (1 : k) = 0` using `by linear_combination -h1 + (ψ σ H.w0 - ψ σ m) * h2`. Conclude with `one_ne_zero this`. Take `⟨h1, h2, -⟩` from `pow_char_sqrt p hp H.d hs.1 hr`.

Establish `h3 : ψ σ' H.rt = ψ σ (-H.rt)`. Apply `hψ` to reduce the goal to its premises. Rewrite using `[hneg]`. Conclude with `(map_neg (σ.comp (algebraMap (𝓞 E) E)) H.rt).symm`. Rewrite `h3` using `[h, h2 hs.2, map_neg]`.

Conclude with `h1 h3`. Introduce `hi`. Use `hor.resolve_left fun hpos => ?_` and prove the remaining obligations. Establish `hp : p ≠ 2`. Introduce and unpack `rfl`.

Apply `hi` to reduce the goal to its premises. Generalize the expression as in `-(H.d : ZMod 2) = z`. Use `revert z`. Evaluate the decidable proposition. Establish `hd : (H.d : ZMod p) ≠ 0`.

Introduce `h0`. Apply `hi` to reduce the goal to its premises. Rewrite using `[h0, neg_zero]`. Conclude with `IsSquare.zero`. Take `⟨h1, -, h2⟩` from `pow_char_sqrt p hp H.d hd hr`.

Establish `h3` using `hψ _ _ _ _ hpos`. Rewrite `h3` using `[h, h2 hi]`. Conclude with `h1 h3.symm`.
-/
theorem frob_rt {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (ψ : (E →+* ℂ) → (𝓞 E →+* k))
    (hψ : ∀ σ σ' (a b : 𝓞 E), σ (a : E) = σ' (b : E) → ψ σ a = ψ σ' b) (σ σ' : E →+* ℂ)
    (h : ∀ a, ψ σ' a = ψ σ a ^ p) :
    (SplitInK H p → σ' (H.rt : E) = σ (H.rt : E)) ∧ (InertInK H p → σ' (H.rt : E) = -σ (H.rt : E)) := by
  have hor : σ' (H.rt : E) = σ (H.rt : E) ∨ σ' (H.rt : E) = -σ (H.rt : E) :=
    sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [emb_rt_sq, emb_rt_sq])
  have hr : ψ σ H.rt ^ 2 = -(H.d : k) := by rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  constructor
  · intro hs
    refine hor.resolve_right fun hneg => ?_
    by_cases hp : p = 2
    · subst hp
      have e : ∀ τ : E →+* ℂ, 2 * τ (H.w0 : E) = 1 + τ (H.rt : E) := fun τ => by
        have := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.two_weight_eq_one_add_root
        rw [map_mul, map_add, map_one, map_ofNat] at this
        exact this
      have h1 : ψ σ' H.w0 = ψ σ (1 - H.w0) := by
        apply hψ
        have : σ ((1 - H.w0 : 𝓞 E) : E) = 1 - σ (H.w0 : E) := by
          have := map_sub (σ.comp (algebraMap (𝓞 E) E)) 1 H.w0
          rw [map_one] at this
          exact this
        rw [this]
        linear_combination (1 / 2 : ℂ) * (e σ + e σ' + hneg)
      obtain ⟨m, hm⟩ := cm_generator_sq_quadratic_eq H
      have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
      rw [h, ← map_pow, hm, map_sub, map_sub, map_mul, map_one, map_ofNat] at h1
      have : (1 : k) = 0 := by linear_combination -h1 + (ψ σ H.w0 - ψ σ m) * h2
      exact one_ne_zero this
    · obtain ⟨h1, h2, -⟩ := pow_char_sqrt p hp H.d hs.1 hr
      have h3 : ψ σ' H.rt = ψ σ (-H.rt) := by
        apply hψ
        rw [hneg]
        exact (map_neg (σ.comp (algebraMap (𝓞 E) E)) H.rt).symm
      rw [h, h2 hs.2, map_neg] at h3
      exact h1 h3
  · intro hi
    refine hor.resolve_left fun hpos => ?_
    have hp : p ≠ 2 := by
      rintro rfl
      apply hi
      generalize -(H.d : ZMod 2) = z
      revert z
      decide
    have hd : (H.d : ZMod p) ≠ 0 := by
      intro h0
      apply hi
      rw [h0, neg_zero]
      exact IsSquare.zero
    obtain ⟨h1, -, h2⟩ := pow_char_sqrt p hp H.d hd hr
    have h3 := hψ _ _ _ _ hpos
    rw [h, h2 hi] at h3
    exact h1 h3.symm

end

/- English proof (translation)
Introduce `E _ _ _ H l c p _ T io X hdisc`. Take `⟨τT, -, hT, -⟩` from `exists_types_valuationRing E H l c T io p X`. Set `t : (E →+* ℂ) → (𝓞 E →+* X.O)` to `fun τ => X.ι.comp (τT τ)`. Establish `ht : ∀ τ a, algebraMap X.O X.C (t τ a) = embX io X τ a` using `hT`. Set `k` to `IsLocalRing.ResidueField X.O`.

Set `ψ : (E →+* ℂ) → (𝓞 E →+* k)` to `fun τ => (IsLocalRing.residue X.O).comp (t τ)`. Establish `hv : ∀ x : X.O, X.v (algebraMap X.O X.C x) < 1 ↔ IsLocalRing.residue X.O x = 0`. Introduce `x`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, X.ints.isUnit_iff_valuation_eq_one, lt_iff_le_and_ne]`. Conclude with `and_iff_right (X.ints.map_le_one x)`.

Establish `hch : CharP k p` using `(CharP.charP_iff_prime_eq_zero Fact.out).2 (by`. Rewrite using `[← map_natCast (IsLocalRing.residue X.O), IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `X.nonunit.out)`. Establish `hker : ∀ τ, primeBelow io X τ = RingHom.ker (ψ τ)`. Introduce `τ`.

Use extensionality with `a`. Express the relevant statement in the definitionally equal form `X.v (embX io X τ a) < 1 ↔ _`. Rewrite using `[← ht, hv, RingHom.mem_ker]`. Both sides reduce to the same expression. Establish `hfrob : ∀ σ σ', GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes.IsFrob io X σ σ' ↔ ∀ a, ψ σ' a = ψ σ a ^ p`.

Introduce `σ σ'`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[← ht, ← ht, ← map_pow, ← map_sub, hv, map_sub, map_pow, sub_eq_zero]`. Both sides reduce to the same expression. Establish `hψ : ∀ σ σ' (a b : 𝓞 E), σ (a : E) = σ' (b : E) → ψ σ a = ψ σ' b`.

Introduce `σ σ' a b hab`. Establish `h1 : embK c σ a = embK c σ' b` using `Subtype.ext (by rw [embK_coe, embK_coe, hab])`. Establish `h2 : t σ a = t σ' b` using `X.ints.hom_inj (by`. Rewrite using `[ht, ht]`. Conclude with `congrArg (fun z => X.ιF (io z)) h1)`.

Conclude with `congrArg (IsLocalRing.residue X.O) h2`. Use `⟨fun σ σ' hσ => ?_, fun τ => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `frob_rt H p ψ hψ σ σ' ((hfrob _ _).1 hσ)`. Use `⟨fun hs => ?_, fun hi => ?_⟩` and prove the remaining obligations. Unfold `InPsi`.

Rewrite using `[h1 hs]`. Unfold `InPsi`. Rewrite using `[h2 hi, conj_rt]`. Establish `hinj : Function.Injective ψ` using `injective_of_det p hdisc X.ints.hom_inj (IsLocalRing.residue X.O) (algebraMap c.F ℂ) (X.ιF.comp io) (embK c) (embK_coe c) t ht`. Take `⟨hfin, hcard⟩` from `card_ringHom_le (𝓞 E) k`.

Establish `hbij : Function.Bijective ψ` using `hinj.bijective_of_nat_card_le (by`. Rewrite using `[Nat.card_eq_fintype_card (α := E →+* ℂ), Embeddings.card, ← RingOfIntegers.rank]`. Conclude with `hcard)`. Set `Φ` to `Equiv.ofBijective ψ hbij`. Establish `hΦ : ∀ φ, ψ (Φ.symm φ) = φ` using `Φ.apply_symm_apply`.

Establish `hne : RingHom.ker (ψ τ) ≠ ⊥`. Introduce `h0`. Establish `h1 : (p : 𝓞 E) ∈ RingHom.ker (ψ τ)`. Rewrite using `[RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]`. Rewrite `h1` using `[h0, Ideal.mem_bot]`.

Conclude with `(Fact.out : p.Prime).ne_zero (by exact_mod_cast h1)`. Use `Ideal.finiteQuotientOfFreeOfNeBot _ hne` as an intermediate fact. Take `⟨h, hpos, hc, hper, hdist, hall⟩` from `orbit_of_ker (𝓞 E) k p (ψ τ)`. Establish `: NeZero h` using `⟨hpos.ne'⟩`. Establish `hmod : ∀ m, (iterateFrobenius k p (m % h)).comp (ψ τ) = (iterateFrobenius k p m).comp (ψ τ)`.

Establish `hq : ∀ q r, (iterateFrobenius k p (r + h * q)).comp (ψ τ) = (iterateFrobenius k p r).comp (ψ τ)`. Introduce `q r`. Proceed by induction on `q with`. Consider the case `zero => simp`. Consider the case `succ q ih => rw [mul_add, mul_one, ← add_assoc, iterateFrobenius_add, RingHom.comp_assoc, hper, ih]`.

Introduce `m`. Rewrite using `[← hq (m / h), Nat.mod_add_div]`. Use `⟨h, hpos, by rw [hker]; exact hc, fun s => Φ.symm ((iterateFrobenius k p s.val).comp (ψ τ)), ?_, fun s => ?_, fun s s' hs => ?_, fun σ => ?_⟩` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hΦ, ZMod.val_zero, iterateFrobenius_zero, RingHom.id_comp]`.

Rewrite using `[hfrob]`. Introduce `a`. Rewrite using `[hΦ, hΦ]`. Establish `h1 : (s + 1).val = (s.val + 1) % h`. Rewrite using `[← ZMod.val_natCast, Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]`.

Rewrite using `[h1, hmod]`. Simplify using `only [RingHom.comp_apply, iterateFrobenius_def, pow_succ, pow_mul]`. Conclude with `ZMod.val_injective h (hdist _ _ (ZMod.val_lt s) (ZMod.val_lt s') (Φ.symm.injective hs))`. Rewrite using `[hker, hker, hall]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨s, hs, hσ⟩`. Use `⟨(s : ZMod h), hinj ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ, ZMod.val_natCast, hmod, hσ]`. Introduce and unpack `⟨s, rfl⟩`. Conclude with `⟨s.val, ZMod.val_lt s, (hΦ _).symm⟩`.
-/
theorem frobOnType_and_orbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), ¬ (p : ℤ) ∣ discr E → FrobOnType io X ∧ ∀ τ : E →+* ℂ, ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h ∧ ∃ lab : ZMod h → (E →+* ℂ), IsOrbit io X τ lab := by
  intro E _ _ _ H l c p _ T io X hdisc
  obtain ⟨τT, -, hT, -⟩ := exists_types_valuationRing E H l c T io p X
  let t : (E →+* ℂ) → (𝓞 E →+* X.O) := fun τ => X.ι.comp (τT τ)
  have ht : ∀ τ a, algebraMap X.O X.C (t τ a) = embX io X τ a := hT
  let k := IsLocalRing.ResidueField X.O
  let ψ : (E →+* ℂ) → (𝓞 E →+* k) := fun τ => (IsLocalRing.residue X.O).comp (t τ)
  have hv : ∀ x : X.O, X.v (algebraMap X.O X.C x) < 1 ↔ IsLocalRing.residue X.O x = 0 := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      X.ints.isUnit_iff_valuation_eq_one, lt_iff_le_and_ne]
    exact and_iff_right (X.ints.map_le_one x)
  have hch : CharP k p := (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
    rw [← map_natCast (IsLocalRing.residue X.O), IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
    exact X.nonunit.out)
  have hker : ∀ τ, primeBelow io X τ = RingHom.ker (ψ τ) := by
    intro τ
    ext a
    change X.v (embX io X τ a) < 1 ↔ _
    rw [← ht, hv, RingHom.mem_ker]
    rfl
  have hfrob : ∀ σ σ', GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes.IsFrob io X σ σ' ↔ ∀ a, ψ σ' a = ψ σ a ^ p := by
    intro σ σ'
    refine forall_congr' fun a => ?_
    rw [← ht, ← ht, ← map_pow, ← map_sub, hv, map_sub, map_pow, sub_eq_zero]
    rfl
  have hψ : ∀ σ σ' (a b : 𝓞 E), σ (a : E) = σ' (b : E) → ψ σ a = ψ σ' b := by
    intro σ σ' a b hab
    have h1 : embK c σ a = embK c σ' b := Subtype.ext (by rw [embK_coe, embK_coe, hab])
    have h2 : t σ a = t σ' b := X.ints.hom_inj (by
      rw [ht, ht]
      exact congrArg (fun z => X.ιF (io z)) h1)
    exact congrArg (IsLocalRing.residue X.O) h2
  refine ⟨fun σ σ' hσ => ?_, fun τ => ?_⟩
  · obtain ⟨h1, h2⟩ := frob_rt H p ψ hψ σ σ' ((hfrob _ _).1 hσ)
    refine ⟨fun hs => ?_, fun hi => ?_⟩
    · unfold InPsi
      rw [h1 hs]
    · unfold InPsi
      rw [h2 hi, conj_rt]
  have hinj : Function.Injective ψ :=
    injective_of_det p hdisc X.ints.hom_inj (IsLocalRing.residue X.O) (algebraMap c.F ℂ) (X.ιF.comp io)
      (embK c) (embK_coe c) t ht
  obtain ⟨hfin, hcard⟩ := card_ringHom_le (𝓞 E) k
  have hbij : Function.Bijective ψ := hinj.bijective_of_nat_card_le (by
    rw [Nat.card_eq_fintype_card (α := E →+* ℂ), Embeddings.card, ← RingOfIntegers.rank]
    exact hcard)
  let Φ := Equiv.ofBijective ψ hbij
  have hΦ : ∀ φ, ψ (Φ.symm φ) = φ := Φ.apply_symm_apply
  have hne : RingHom.ker (ψ τ) ≠ ⊥ := by
    intro h0
    have h1 : (p : 𝓞 E) ∈ RingHom.ker (ψ τ) := by
      rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rw [h0, Ideal.mem_bot] at h1
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h1)
  have := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  obtain ⟨h, hpos, hc, hper, hdist, hall⟩ := orbit_of_ker (𝓞 E) k p (ψ τ)
  have : NeZero h := ⟨hpos.ne'⟩
  have hmod : ∀ m, (iterateFrobenius k p (m % h)).comp (ψ τ) = (iterateFrobenius k p m).comp (ψ τ) := by
    have hq : ∀ q r, (iterateFrobenius k p (r + h * q)).comp (ψ τ) = (iterateFrobenius k p r).comp (ψ τ) := by
      intro q r
      induction q with
      | zero => simp
      | succ q ih => rw [mul_add, mul_one, ← add_assoc, iterateFrobenius_add, RingHom.comp_assoc, hper, ih]
    intro m
    rw [← hq (m / h), Nat.mod_add_div]
  refine ⟨h, hpos, by rw [hker]; exact hc,
    fun s => Φ.symm ((iterateFrobenius k p s.val).comp (ψ τ)), ?_, fun s => ?_, fun s s' hs => ?_, fun σ => ?_⟩
  · apply hinj
    rw [hΦ, ZMod.val_zero, iterateFrobenius_zero, RingHom.id_comp]
  · rw [hfrob]
    intro a
    rw [hΦ, hΦ]
    have h1 : (s + 1).val = (s.val + 1) % h := by
      rw [← ZMod.val_natCast, Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
    rw [h1, hmod]
    simp only [RingHom.comp_apply, iterateFrobenius_def, pow_succ, pow_mul]
  · exact ZMod.val_injective h (hdist _ _ (ZMod.val_lt s) (ZMod.val_lt s') (Φ.symm.injective hs))
  · rw [hker, hker, hall]
    constructor
    · rintro ⟨s, hs, hσ⟩
      refine ⟨(s : ZMod h), hinj ?_⟩
      rw [hΦ, ZMod.val_natCast, hmod, hσ]
    · rintro ⟨s, rfl⟩
      exact ⟨s.val, ZMod.val_lt s, (hΦ _).symm⟩

end GlobalTheory.FrobOrbit
