import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemLiftOfSteps
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.Id

/- English proof (translation)
Introduce `I s hs`. Take `⟨a, ha⟩` from `(I.cm.fixed (s : I.E)).mp hs`. Establish `hs' : IsIntegral ℤ ((algebraMap I.F I.E).toIntAlgHom a)` using `by show IsIntegral ℤ (algebraMap I.F I.E a)`. Rewrite using `[ha]`. Conclude with `NumberField.RingOfIntegers.isIntegral_coe s`.

Establish `hint : IsIntegral ℤ a` using `(isIntegral_algHom_iff (algebraMap I.F I.E).toIntAlgHom (algebraMap I.F I.E).injective).mp hs'`. Conclude with `⟨⟨a, hint⟩, ha⟩`.
-/
theorem fixInt : FixInt := by
  intro I s hs
  obtain ⟨a, ha⟩ := (I.cm.fixed (s : I.E)).mp hs
  have hs' : IsIntegral ℤ ((algebraMap I.F I.E).toIntAlgHom a) := by
    show IsIntegral ℤ (algebraMap I.F I.E a)
    rw [ha]
    exact NumberField.RingOfIntegers.isIntegral_coe s
  have hint : IsIntegral ℤ a :=
    (isIntegral_algHom_iff (algebraMap I.F I.E).toIntAlgHom (algebraMap I.F I.E).injective).mp hs'
  exact ⟨⟨a, hint⟩, ha⟩

/- English proof (translation)
Use `show ∀ v, _`. Introduce `v`. Rewrite using `[IsDedekindDomain.FiniteAdeleRing.algebraMap_apply]`. Conclude with `IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers v r`.
-/
theorem intF {F : Type} [Field F] [NumberField F] (r : 𝓞 F) :
    algebraMap F (Af F) (r : F) ∈ Formalism.UG.intAd F := by
  show ∀ v, _
  intro v
  rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply]
  exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

section Ten

variable (I : Formalism.MainNotions.S.AutInst)

def iA : Af I.F →ₐ[I.F] I.E ⊗[I.F] Af I.F := Algebra.TensorProduct.includeRight

def iE : I.E →+* I.E ⊗[I.F] Af I.F := Formalism.UG.inclE (F := I.F) (Af I.F)

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeRight_apply x`.
-/
theorem iA_apply (x : Af I.F) : iA I x = (1 : I.E) ⊗ₜ[I.F] x :=
  Algebra.TensorProduct.includeRight_apply x

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeLeftRingHom_apply e`.
-/
theorem iE_apply (e : I.E) : iE I e = e ⊗ₜ[I.F] (1 : Af I.F) :=
  Algebra.TensorProduct.includeLeftRingHom_apply e

/- English proof (translation)
Rewrite using `[iE_apply, iA_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.
-/
theorem iE_alg (x : I.F) : iE I (algebraMap I.F I.E x) = iA I (algebraMap I.F (Af I.F) x) := by
  rw [iE_apply, iA_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul]

/- English proof (translation)
Rewrite using `[iA_apply]`. Use `show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) ((1 : I.E) ⊗ₜ[I.F] x) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`. Both sides reduce to the same expression.
-/
theorem sig_iA (x : Af I.F) : sigA I (iA I x) = iA I x := by
  rw [iA_apply]
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) ((1 : I.E) ⊗ₜ[I.F] x) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

/- English proof (translation)
Rewrite using `[iE_apply, iE_apply]`. Use `show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) (e ⊗ₜ[I.F] (1 : Af I.F)) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`. Both sides reduce to the same expression.
-/
theorem sig_iE (e : I.E) : sigA I (iE I e) = iE I (star e) := by
  rw [iE_apply, iE_apply]
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) (e ⊗ₜ[I.F] (1 : Af I.F)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

/- English proof (translation)
Rewrite using `[iE_apply]`. Conclude with `Subring.subset_closure (Or.inl ⟨⟨(θ : I.E), θ, rfl⟩, rfl⟩)`.
-/
theorem iE_mem (θ : 𝓞 I.E) : iE I (θ : I.E) ∈ IntAf I.F I.E := by
  rw [iE_apply]
  exact Subring.subset_closure (Or.inl ⟨⟨(θ : I.E), θ, rfl⟩, rfl⟩)

/- English proof (translation)
Rewrite using `[iA_apply]`. Conclude with `Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)`.
-/
theorem iA_mem {x : Af I.F} (hx : x ∈ Formalism.UG.intAd I.F) : iA I x ∈ IntAf I.F I.E := by
  rw [iA_apply]
  exact Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)

end Ten

/- English proof (translation)
Introduce `hAd hFix I g θ hg _hsp hθ`. Take `⟨⟨t1, ht1⟩, ⟨t2, ht2⟩, ⟨t3, ht3⟩⟩` from `hθ`. Establish `hgE : ((g : ℕ) : I.E) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Establish `hs2 : star (t2 : I.E) = t2`. Establish `h1 : star ((θ : I.E) * star (θ : I.E)) = (θ : I.E) * star (θ : I.E)`.

Rewrite using `[star_mul, star_star]`. Rewrite `h1` using `[ht2, star_mul, star_natCast, mul_comm]`. Conclude with `mul_left_cancel₀ hgE h1`. Establish `hs3 : star (t3 : I.E) = t3`. Establish `h1 : star (1 - (θ : I.E) - star (θ : I.E)) = 1 - (θ : I.E) - star (θ : I.E)`.

Rewrite using `[star_sub, star_sub, star_one, star_star]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[ht3, star_mul, star_natCast, mul_comm]`. Conclude with `mul_left_cancel₀ hgE h1`. Take `⟨a2, ha2⟩` from `hFix I t2 hs2`.

Take `⟨a3, ha3⟩` from `hFix I t3 hs3`. Establish `hαi : -algebraMap I.F (Af I.F) (a3 : I.F) ∈ Formalism.UG.intAd I.F` using `(Formalism.UG.intAd I.F).neg_mem (intF a3)`. Establish `hβi : algebraMap I.F (Af I.F) (a2 : I.F) ∈ Formalism.UG.intAd I.F` using `intF a2`. Take `⟨C₁, C₂, hC₁, hC₂, hi, hii, hiii⟩` from `hAd I.F g _ _ hg hαi hβi`. Take `⟨W, hWd⟩ : ∃ W : Af I.F, W = 1 + (g : Af I.F) * C₁` from `⟨_, rfl⟩`.

Take `⟨Q, hQd⟩ : ∃ Q : Af I.F, Q = (g : Af I.F) * C₂` from `⟨_, rfl⟩`. Take `⟨A0, hA0d⟩ : ∃ A0 : Af I.F, A0 = 1 + (g : Af I.F) * -algebraMap I.F (Af I.F) (a3 : I.F)` from `⟨_, rfl⟩`. Take `⟨B0, hB0d⟩ : ∃ B0 : Af I.F, B0 = (g : Af I.F) * algebraMap I.F (Af I.F) (a2 : I.F)` from `⟨_, rfl⟩`. Rewrite `hi` using `[← hWd, ← hQd, ← hA0d]`. Rewrite `hii` using `[← hWd, ← hQd, ← hB0d]`.

Rewrite `hiii` using `[← hWd, ← hQd, ← hA0d, ← hB0d]`. Establish `hi'` using `congrArg (iA I) hi`. Establish `hii'` using `congrArg (iA I) hii`. Establish `hiii'` using `congrArg (iA I) hiii`. Simplify using `only [map_mul, map_add, map_sub, map_pow, map_neg, map_ofNat, map_zero] at hi' hii' hiii'`.

Establish `hA : iA I A0 = iE I (θ : I.E) + iE I (star (θ : I.E))`. Establish `e1 : A0 = algebraMap I.F (Af I.F) (1 - (g : I.F) * (a3 : I.F))`. Rewrite using `[hA0d, map_sub, map_one, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : algebraMap I.F I.E (1 - (g : I.F) * (a3 : I.F)) = (θ : I.E) + star (θ : I.E)`.

Rewrite using `[map_sub, map_one, map_mul, map_natCast, ha3]`. Take the linear combination `ht3`. Rewrite using `[e1, ← iE_alg, e2, map_add]`. Establish `hB : iA I B0 = iE I (θ : I.E) * iE I (star (θ : I.E))`. Establish `e1 : B0 = algebraMap I.F (Af I.F) ((g : I.F) * (a2 : I.F))`.

Rewrite using `[hB0d, map_mul, map_natCast]`. Establish `e2 : algebraMap I.F I.E ((g : I.F) * (a2 : I.F)) = (θ : I.E) * star (θ : I.E)`. Rewrite using `[map_mul, map_natCast, ha2, ht2]`. Rewrite using `[e1, ← iE_alg, e2, map_mul]`. Rewrite `hi'`, `hiii'` using `[hA]`.

Rewrite `hii'`, `hiii'` using `[hB]`. Establish `hWi : W ∈ Formalism.UG.intAd I.F`. Rewrite using `[hWd]`. Conclude with `add_mem (one_mem _) (mul_mem (natCast_mem _ g) hC₁)`. Establish `hQi : Q ∈ Formalism.UG.intAd I.F`.

Rewrite using `[hQd]`. Conclude with `mul_mem (natCast_mem _ g) hC₂`. Use `⟨iE I (θ : I.E) * iA I W - iA I Q, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `sub_mem (mul_mem (iE_mem I θ) (iA_mem I hWi)) (iA_mem I hQi)`. Take the linear combination `(iE I (θ : I.E)) * hi' + hii'`.

Rewrite using `[map_sub, map_mul, sig_iE, sig_iA, sig_iA]`. Take the linear combination `hiii'`. Use `⟨iE I (θ : I.E) * iA I C₁ - iA I C₂, sub_mem (mul_mem (iE_mem I θ) (iA_mem I hC₁)) (iA_mem I hC₂), ?_⟩` and prove the remaining obligations. Establish `hW' : iA I W = 1 + (g : I.E ⊗[I.F] Af I.F) * iA I C₁`. Rewrite using `[hWd, map_add, map_one, map_mul, map_natCast]`.

Establish `hQ' : iA I Q = (g : I.E ⊗[I.F] Af I.F) * iA I C₂`. Rewrite using `[hQd, map_mul, map_natCast]`. Use `show iE I (θ : I.E) * iA I W - iA I Q - iE I (θ : I.E) = _`. Rewrite using `[hW', hQ']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tenStep : TenStep := by
  intro hAd hFix I g θ hg _hsp hθ
  obtain ⟨⟨t1, ht1⟩, ⟨t2, ht2⟩, ⟨t3, ht3⟩⟩ := hθ
  have hgE : ((g : ℕ) : I.E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs2 : star (t2 : I.E) = t2 := by
    have h1 : star ((θ : I.E) * star (θ : I.E)) = (θ : I.E) * star (θ : I.E) := by
      rw [star_mul, star_star]
    rw [ht2, star_mul, star_natCast, mul_comm] at h1
    exact mul_left_cancel₀ hgE h1
  have hs3 : star (t3 : I.E) = t3 := by
    have h1 : star (1 - (θ : I.E) - star (θ : I.E)) = 1 - (θ : I.E) - star (θ : I.E) := by
      rw [star_sub, star_sub, star_one, star_star]
      ring
    rw [ht3, star_mul, star_natCast, mul_comm] at h1
    exact mul_left_cancel₀ hgE h1
  obtain ⟨a2, ha2⟩ := hFix I t2 hs2
  obtain ⟨a3, ha3⟩ := hFix I t3 hs3
  have hαi : -algebraMap I.F (Af I.F) (a3 : I.F) ∈ Formalism.UG.intAd I.F :=
    (Formalism.UG.intAd I.F).neg_mem (intF a3)
  have hβi : algebraMap I.F (Af I.F) (a2 : I.F) ∈ Formalism.UG.intAd I.F := intF a2
  obtain ⟨C₁, C₂, hC₁, hC₂, hi, hii, hiii⟩ := hAd I.F g _ _ hg hαi hβi
  obtain ⟨W, hWd⟩ : ∃ W : Af I.F, W = 1 + (g : Af I.F) * C₁ := ⟨_, rfl⟩
  obtain ⟨Q, hQd⟩ : ∃ Q : Af I.F, Q = (g : Af I.F) * C₂ := ⟨_, rfl⟩
  obtain ⟨A0, hA0d⟩ : ∃ A0 : Af I.F,
      A0 = 1 + (g : Af I.F) * -algebraMap I.F (Af I.F) (a3 : I.F) := ⟨_, rfl⟩
  obtain ⟨B0, hB0d⟩ : ∃ B0 : Af I.F, B0 = (g : Af I.F) * algebraMap I.F (Af I.F) (a2 : I.F) :=
    ⟨_, rfl⟩
  rw [← hWd, ← hQd, ← hA0d] at hi
  rw [← hWd, ← hQd, ← hB0d] at hii
  rw [← hWd, ← hQd, ← hA0d, ← hB0d] at hiii
  have hi' := congrArg (iA I) hi
  have hii' := congrArg (iA I) hii
  have hiii' := congrArg (iA I) hiii
  simp only [map_mul, map_add, map_sub, map_pow, map_neg, map_ofNat, map_zero] at hi' hii' hiii'
  have hA : iA I A0 = iE I (θ : I.E) + iE I (star (θ : I.E)) := by
    have e1 : A0 = algebraMap I.F (Af I.F) (1 - (g : I.F) * (a3 : I.F)) := by
      rw [hA0d, map_sub, map_one, map_mul, map_natCast]
      ring
    have e2 : algebraMap I.F I.E (1 - (g : I.F) * (a3 : I.F)) = (θ : I.E) + star (θ : I.E) := by
      rw [map_sub, map_one, map_mul, map_natCast, ha3]
      linear_combination ht3
    rw [e1, ← iE_alg, e2, map_add]
  have hB : iA I B0 = iE I (θ : I.E) * iE I (star (θ : I.E)) := by
    have e1 : B0 = algebraMap I.F (Af I.F) ((g : I.F) * (a2 : I.F)) := by
      rw [hB0d, map_mul, map_natCast]
    have e2 : algebraMap I.F I.E ((g : I.F) * (a2 : I.F)) = (θ : I.E) * star (θ : I.E) := by
      rw [map_mul, map_natCast, ha2, ht2]
    rw [e1, ← iE_alg, e2, map_mul]
  rw [hA] at hi' hiii'
  rw [hB] at hii' hiii'
  have hWi : W ∈ Formalism.UG.intAd I.F := by
    rw [hWd]
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ g) hC₁)
  have hQi : Q ∈ Formalism.UG.intAd I.F := by
    rw [hQd]
    exact mul_mem (natCast_mem _ g) hC₂
  refine ⟨iE I (θ : I.E) * iA I W - iA I Q, ?_, ?_, ?_, ?_⟩
  · exact sub_mem (mul_mem (iE_mem I θ) (iA_mem I hWi)) (iA_mem I hQi)
  · linear_combination (iE I (θ : I.E)) * hi' + hii'
  · rw [map_sub, map_mul, sig_iE, sig_iA, sig_iA]
    linear_combination hiii'
  · refine ⟨iE I (θ : I.E) * iA I C₁ - iA I C₂,
      sub_mem (mul_mem (iE_mem I θ) (iA_mem I hC₁)) (iA_mem I hC₂), ?_⟩
    have hW' : iA I W = 1 + (g : I.E ⊗[I.F] Af I.F) * iA I C₁ := by
      rw [hWd, map_add, map_one, map_mul, map_natCast]
    have hQ' : iA I Q = (g : I.E ⊗[I.F] Af I.F) * iA I C₂ := by
      rw [hQd, map_mul, map_natCast]
    show iE I (θ : I.E) * iA I W - iA I Q - iE I (θ : I.E) = _
    rw [hW', hQ']
    ring

end PI.ScRefExists.Id
