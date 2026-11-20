import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtChart
open TensorProduct

noncomputable section
namespace GlobalTheory.DenseSec

/- English proof (translation)
Use `letI algPD : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) := (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (Ideal.Quotient.mk I (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebr …`. Use `letI algRA : Algebra (MvPolynomial (Fin g) R) (Localization.Away h) := ((algebraMap A (Localization.Away h)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra`. Use `haveI hEt : Algebra.Etale (MvPolynomial (Fin g) R) (Localization.Away h) := hE`. Use `letI algRP : Algebra (MvPolynomial (Fin g) R) (MvPolynomial (Fin g) Ω) := MvPolynomial.algebraMvPolynomial`. Use `letI algRD : Algebra (MvPolynomial (Fin g) R) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) := ((algebraMap (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))).comp (algebraMap (MvPolynomial (Fin g) R) (MvPolynomial (Fin g) Ω))).toAlgebra`.

Use `haveI hST := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algRP algPD algRD (fun _ => rfl)`. Set `f : A →+* Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))` to `(algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))).comp ((Ideal.Quotient.mk I).comp (Algebra.TensorProduct.includeRight (R := R) (A := Ω) (B := A)).toRingHom)`. Establish `hf : ∀ a, f a = algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (Ideal.Quotient.mk I (1 ⊗ₜ[R] a))` using `fun a => rfl`. Establish `hu : IsUnit (f h)` using `by rw [hf]; exact IsLocalization.Away.algebraMap_isUnit _`. Set `ψ0 : Localization.Away h →+* Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))` to `IsLocalization.Away.lift h hu`.

Establish `hψ0 : ∀ a, ψ0 (algebraMap A (Localization.Away h) a) = f a` using `fun a => IsLocalization.lift_eq _ _`. Establish `hΩ : ∀ w : Ω, algebraMap Ω (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) w = algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (Ideal.Quotient.mk I (w ⊗ₜ[R] 1))`. Introduce `w`. Rewrite using `[IsScalarTower.algebraMap_apply Ω (TensorProduct R Ω A ⧸ I)]`. Both sides reduce to the same expression.

Establish `hcomp : ψ0.comp (algebraMap (MvPolynomial (Fin g) R) (Localization.Away h)) = algebraMap (MvPolynomial (Fin g) R) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r show ψ0 (algebraMap A _ (MvPolynomial.aeval t (MvPolynomial.C r))) = MvPolynomial.aeval _ (MvPolynomial.map (algebraMap R Ω) (MvPolynomial.C r))`. Rewrite using `[hψ0, MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C, hf, hΩ]`. Use `congr 2`.

Rewrite using `[← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']`. Introduce `i show ψ0 (algebraMap A _ (MvPolynomial.aeval t (MvPolynomial.X i))) = MvPolynomial.aeval _ (MvPolynomial.map (algebraMap R Ω) (MvPolynomial.X i))`. Rewrite using `[hψ0, MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X, hf]`. Set `ψ : Localization.Away h →ₐ[MvPolynomial (Fin g) R] Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))` to `{ ψ0 with commutes' := fun p => RingHom.congr_fun hcomp p }`. Set `Φ : MvPolynomial (Fin g) Ω ⊗[MvPolynomial (Fin g) R] Localization.Away h →ₐ[MvPolynomial (Fin g) Ω] Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))` to `Algebra.TensorProduct.lift (Algebra.ofId _ _) ψ (fun _ _ => Commute.all _ _)`.

Establish `hΦ : ∀ (p : MvPolynomial (Fin g) Ω) (y : Localization.Away h), Φ (p ⊗ₜ y) = algebraMap _ _ p * ψ0 y` using `fun p y => Algebra.TensorProduct.lift_tmul _ _ _ _ _`. Establish `hQ : ∀ x : TensorProduct R Ω A ⧸ I, algebraMap _ (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) x ∈ Φ.range`. Introduce `x`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Proceed by induction on `b using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul w a`. Use `⟨MvPolynomial.C w ⊗ₜ algebraMap A _ a, ?_⟩` and prove the remaining obligations. Use `show Φ (MvPolynomial.C w ⊗ₜ algebraMap A _ a) = _`. Rewrite using `[hΦ, hψ0, hf]`.

Use `show MvPolynomial.aeval _ (MvPolynomial.C w) * _ = _`. Rewrite using `[MvPolynomial.aeval_C, hΩ, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Consider the case `add x y hx hy => rw [map_add, map_add]`. Conclude with `add_mem hx hy`. Establish `hsurj : Function.Surjective Φ`.

Introduce `z`. Take `⟨⟨x, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) z`. Take `⟨n, hn⟩` from `Submonoid.mem_powers_iff _ _ |>.mp s.2`. Establish `hs : s = ⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ ^ n` using `Subtype.ext hn.symm`. Establish `hinv : IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I) (⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ : Submonoid.powers (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) = Φ (1 ⊗ₜ IsLocalization.mk' (Localization.Away h) (1 : A …`.

Rewrite using `[hΦ, map_one, one_mul, IsLocalization.mk'_eq_iff_eq_mul]`. Use `show _ = _ * f h`. Rewrite using `[← hψ0, ← map_mul, IsLocalization.mk'_spec]`. Simplify using the standard rewrite rules. Establish `: IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) x s ∈ Φ.range`.

Establish `hpow : IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I) s = (IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I) (⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ : S …`. Rewrite using `[hs, ← IsLocalization.mk'_pow, one_pow]`. Rewrite using `[IsLocalization.mk'_eq_mul_mk'_one, hpow, hinv]`. Conclude with `mul_mem (hQ x) (pow_mem (AlgHom.mem_range_self Φ _) n)`. Conclude with `this`.

Conclude with `⟨Algebra.FiniteType.of_surjective Φ hsurj, Algebra.FormallyUnramified.of_surjective Φ hsurj⟩`.
-/
theorem locQuot_finiteType_formallyUnramified (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A]
    (g : ℕ) (t : Fin g → A) (h : A) (hE : GlobalTheory.DenseSec.EtChart R A t h) (Ω : Type) [Field Ω] [Algebra R Ω]
    (I : Ideal (TensorProduct R Ω A)) :
    letI : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
      (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ I)
        (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (Ideal.Quotient.mk I (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
    Algebra.FiniteType (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) ∧
      Algebra.FormallyUnramified (MvPolynomial (Fin g) Ω)
        (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) := by
  letI algPD : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
    (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ I)
      (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (Ideal.Quotient.mk I (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
  letI algRA : Algebra (MvPolynomial (Fin g) R) (Localization.Away h) :=
    ((algebraMap A (Localization.Away h)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  haveI hEt : Algebra.Etale (MvPolynomial (Fin g) R) (Localization.Away h) := hE
  letI algRP : Algebra (MvPolynomial (Fin g) R) (MvPolynomial (Fin g) Ω) := MvPolynomial.algebraMvPolynomial
  letI algRD : Algebra (MvPolynomial (Fin g) R) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
    ((algebraMap (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))).comp
      (algebraMap (MvPolynomial (Fin g) R) (MvPolynomial (Fin g) Ω))).toAlgebra
  haveI hST := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algRP algPD algRD (fun _ => rfl)
  let f : A →+* Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    (algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))).comp
      ((Ideal.Quotient.mk I).comp (Algebra.TensorProduct.includeRight (R := R) (A := Ω) (B := A)).toRingHom)
  have hf : ∀ a, f a = algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))
      (Ideal.Quotient.mk I (1 ⊗ₜ[R] a)) := fun a => rfl
  have hu : IsUnit (f h) := by rw [hf]; exact IsLocalization.Away.algebraMap_isUnit _
  let ψ0 : Localization.Away h →+* Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    IsLocalization.Away.lift h hu
  have hψ0 : ∀ a, ψ0 (algebraMap A (Localization.Away h) a) = f a := fun a => IsLocalization.lift_eq _ _
  have hΩ : ∀ w : Ω, algebraMap Ω (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) w =
      algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))
        (Ideal.Quotient.mk I (w ⊗ₜ[R] 1)) := by
    intro w
    rw [IsScalarTower.algebraMap_apply Ω (TensorProduct R Ω A ⧸ I)]
    rfl
  have hcomp : ψ0.comp (algebraMap (MvPolynomial (Fin g) R) (Localization.Away h)) =
      algebraMap (MvPolynomial (Fin g) R) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show ψ0 (algebraMap A _ (MvPolynomial.aeval t (MvPolynomial.C r))) =
        MvPolynomial.aeval _ (MvPolynomial.map (algebraMap R Ω) (MvPolynomial.C r))
      rw [hψ0, MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C, hf, hΩ]
      congr 2
      rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
    · intro i
      show ψ0 (algebraMap A _ (MvPolynomial.aeval t (MvPolynomial.X i))) =
        MvPolynomial.aeval _ (MvPolynomial.map (algebraMap R Ω) (MvPolynomial.X i))
      rw [hψ0, MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X, hf]
  let ψ : Localization.Away h →ₐ[MvPolynomial (Fin g) R] Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    { ψ0 with commutes' := fun p => RingHom.congr_fun hcomp p }
  let Φ : MvPolynomial (Fin g) Ω ⊗[MvPolynomial (Fin g) R] Localization.Away h →ₐ[MvPolynomial (Fin g) Ω]
      Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ψ (fun _ _ => Commute.all _ _)
  have hΦ : ∀ (p : MvPolynomial (Fin g) Ω) (y : Localization.Away h), Φ (p ⊗ₜ y) = algebraMap _ _ p * ψ0 y :=
    fun p y => Algebra.TensorProduct.lift_tmul _ _ _ _ _
  have hQ : ∀ x : TensorProduct R Ω A ⧸ I,
      algebraMap _ (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) x ∈ Φ.range := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul w a =>
      refine ⟨MvPolynomial.C w ⊗ₜ algebraMap A _ a, ?_⟩
      show Φ (MvPolynomial.C w ⊗ₜ algebraMap A _ a) = _
      rw [hΦ, hψ0, hf]
      show MvPolynomial.aeval _ (MvPolynomial.C w) * _ = _
      rw [MvPolynomial.aeval_C, hΩ, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Submonoid.powers (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) z
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp s.2
    have hs : s = ⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ ^ n := Subtype.ext hn.symm
    have hinv : IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I)
        (⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ :
          Submonoid.powers (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) =
        Φ (1 ⊗ₜ IsLocalization.mk' (Localization.Away h) (1 : A) (⟨h, Submonoid.mem_powers _⟩ : Submonoid.powers h)) := by
      rw [hΦ, map_one, one_mul, IsLocalization.mk'_eq_iff_eq_mul]
      show _ = _ * f h
      rw [← hψ0, ← map_mul, IsLocalization.mk'_spec]
      simp
    have : IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) x s ∈ Φ.range := by
      have hpow : IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I) s =
          (IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I)
            (⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ :
              Submonoid.powers (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))) ^ n := by
        rw [hs, ← IsLocalization.mk'_pow, one_pow]
      rw [IsLocalization.mk'_eq_mul_mk'_one, hpow, hinv]
      exact mul_mem (hQ x) (pow_mem (AlgHom.mem_range_self Φ _) n)
    exact this
  exact ⟨Algebra.FiniteType.of_surjective Φ hsurj, Algebra.FormallyUnramified.of_surjective Φ hsurj⟩

end GlobalTheory.DenseSec
