import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AlgebraMapSurjectiveOfUnramifiedOfUniquePoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

/- English proof (translation)
Set `_ : Algebra R K` to `x.toAlgebra`. Set `yA : B →ₐ[R] K` to `{ y with commutes' := fun r => RingHom.congr_fun hy r }`. Set `φ : K ⊗[R] B →ₐ[K] K` to `Algebra.TensorProduct.lift (Algebra.ofId K K) yA (fun _ _ => Commute.all _ _)`. Establish `hall : ∀ ψ : K ⊗[R] B →ₐ[K] K, ∀ (a : K) (b : B), ψ (a ⊗ₜ[R] b) = a * y b`. Introduce `ψ a b`.

Establish `hz : ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom = y`. Apply `hu` to reduce the goal to its premises. Use extensionality with `r`. Conclude with `((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight).commutes r`. Establish `h1 : ψ ((1 : K) ⊗ₜ[R] b) = y b`.

Use `RingHom.congr_fun hz b` as an intermediate fact. Simplify using `using this`. Establish `h2 : a ⊗ₜ[R] b = a • ((1 : K) ⊗ₜ[R] b)`. Rewrite using `[TensorProduct.smul_tmul']`. Simplify using the standard rewrite rules.

Rewrite using `[h2, map_smul, h1, _root_.smul_eq_mul]`. Establish `huniq : ∀ ψ : K ⊗[R] B →ₐ[K] K, ψ = φ`. Introduce `ψ`. Use `AlgHom.ext fun t => ?_` and prove the remaining obligations. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a b => rw [hall ψ, hall φ]`. Consider the case `add s t hs ht => rw [map_add, map_add, hs, ht]`. Establish `hsurj` using `algebraMap_surjective_of_unramified_of_unique_point K (K ⊗[R] B) φ huniq`. Use `set N : Submodule R B := LinearMap.range (Algebra.linearMap R B) with hN`.

Establish `hone : N.mkQ (1 : B) = 0` using `(Submodule.Quotient.mk_eq_zero N).mpr ⟨1, by simp⟩`. Establish `hzero : ∀ t : K ⊗[R] (B ⧸ N), t = 0`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rfl`.

Consider the case `tmul a c`. Take `⟨b, rfl⟩` from `N.mkQ_surjective c`. Take `⟨c', hc'⟩` from `hsurj (a ⊗ₜ[R] b)`. Rewrite using `[← LinearMap.lTensor_tmul, ← hc', Algebra.TensorProduct.algebraMap_apply, LinearMap.lTensor_tmul, hone, TensorProduct.tmul_zero]`. Consider the case `add s t hs ht => rw [hs, ht, add_zero]`.

Set `p : PrimeSpectrum R` to `⟨RingHom.ker x, RingHom.ker_isPrime x⟩`. Establish `hns : p ∉ Module.support R (B ⧸ N)`. Introduce `h`. Establish `hnt` using `nontrivial_tensor_of_mem_support R (B ⧸ N) K p rfl h`. Take `⟨s, t, hst⟩` from `hnt.exists_pair_ne`.

Conclude with `hst ((hzero s).trans (hzero t).symm)`. Rewrite `hns` using `[Module.mem_support_iff_of_finite]`. Take `⟨f, hf, hfp⟩` from `Set.not_subset.mp hns`. Use `⟨f, hfp, fun b => ?_⟩` and prove the remaining obligations. Establish `hfb : f • N.mkQ b = 0` using `Module.mem_annihilator.mp hf _`.

Rewrite `hfb` using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨a, ha⟩` from `hfb`. Conclude with `⟨a, by rw [← Algebra.smul_def, ← ha, Algebra.linearMap_apply]⟩`.
-/
theorem exists_smul_mem_range_of_unique_point (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.FormallyUnramified R B] (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K)
    (y : B →+* K) (hy : y.comp (algebraMap R B) = x) (hu : ∀ z : B →+* K, z.comp (algebraMap R B) = x → z = y) :
    ∃ f : R, f ∉ RingHom.ker x ∧ ∀ b : B, ∃ a : R, algebraMap R B a = algebraMap R B f * b := by
  let _ : Algebra R K := x.toAlgebra
  let yA : B →ₐ[R] K := { y with commutes' := fun r => RingHom.congr_fun hy r }
  let φ : K ⊗[R] B →ₐ[K] K :=
    Algebra.TensorProduct.lift (Algebra.ofId K K) yA (fun _ _ => Commute.all _ _)
  have hall : ∀ ψ : K ⊗[R] B →ₐ[K] K, ∀ (a : K) (b : B), ψ (a ⊗ₜ[R] b) = a * y b := by
    intro ψ a b
    have hz : ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom = y := by
      apply hu
      ext r
      exact ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight).commutes r
    have h1 : ψ ((1 : K) ⊗ₜ[R] b) = y b := by
      have := RingHom.congr_fun hz b
      simpa using this
    have h2 : a ⊗ₜ[R] b = a • ((1 : K) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul']
      simp
    rw [h2, map_smul, h1, _root_.smul_eq_mul]
  have huniq : ∀ ψ : K ⊗[R] B →ₐ[K] K, ψ = φ := by
    intro ψ
    refine AlgHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [hall ψ, hall φ]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  have hsurj := algebraMap_surjective_of_unramified_of_unique_point K (K ⊗[R] B) φ huniq
  set N : Submodule R B := LinearMap.range (Algebra.linearMap R B) with hN
  have hone : N.mkQ (1 : B) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ⟨1, by simp⟩
  have hzero : ∀ t : K ⊗[R] (B ⧸ N), t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | tmul a c =>
      obtain ⟨b, rfl⟩ := N.mkQ_surjective c
      obtain ⟨c', hc'⟩ := hsurj (a ⊗ₜ[R] b)
      rw [← LinearMap.lTensor_tmul, ← hc', Algebra.TensorProduct.algebraMap_apply, LinearMap.lTensor_tmul, hone,
        TensorProduct.tmul_zero]
    | add s t hs ht => rw [hs, ht, add_zero]
  let p : PrimeSpectrum R := ⟨RingHom.ker x, RingHom.ker_isPrime x⟩
  have hns : p ∉ Module.support R (B ⧸ N) := by
    intro h
    have hnt := nontrivial_tensor_of_mem_support R (B ⧸ N) K p rfl h
    obtain ⟨s, t, hst⟩ := hnt.exists_pair_ne
    exact hst ((hzero s).trans (hzero t).symm)
  rw [Module.mem_support_iff_of_finite] at hns
  obtain ⟨f, hf, hfp⟩ := Set.not_subset.mp hns
  refine ⟨f, hfp, fun b => ?_⟩
  have hfb : f • N.mkQ b = 0 := Module.mem_annihilator.mp hf _
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hfb
  obtain ⟨a, ha⟩ := hfb
  exact ⟨a, by rw [← Algebra.smul_def, ← ha, Algebra.linearMap_apply]⟩

/- English proof (translation)
Use `choose a ha using hf`. Use `set g : Localization.Away f := IsLocalization.Away.invSelf f with hg`. Establish `hfg : loc f f * g = 1` using `IsLocalization.Away.mul_invSelf f`. Establish `ha_zero : a 0 = 0` using `hinj (by simp only [ha, MulZeroClass.mul_zero, map_zero])`. Establish `ha_one : a 1 = f` using `hinj (by simp only [ha, _root_.mul_one])`.

Establish `ha_add : ∀ b c, a (b + c) = a b + a c` using `fun b c => hinj (by simp only [ha, map_add]; ring)`. Establish `ha_mul : ∀ b c, f * a (b * c) = a b * a c` using `fun b c => hinj (by simp only [ha, map_mul]; ring)`. Establish `ha_alg : ∀ c, a (algebraMap R B c) = f * c` using `fun c => hinj (by simp only [ha, map_mul])`. Establish `h_one : loc f (a 1) * g = 1` using `by rw [ha_one, hfg]`. Establish `h_mul : ∀ b c, loc f (a (b * c)) * g = loc f (a b) * g * (loc f (a c) * g)`.

Introduce `b c`. Establish `h` using `congrArg (loc f) (ha_mul b c)`. Rewrite `h` using `[map_mul, map_mul]`. Take the linear combination `(-(loc f (a (b * c)) * g)) * hfg + g * g * h`. Establish `h_zero : loc f (a 0) * g = 0` using `by rw [ha_zero, map_zero, MulZeroClass.zero_mul]`.

Establish `h_add : ∀ b c, loc f (a (b + c)) * g = loc f (a b) * g + loc f (a c) * g`. Introduce `b c`. Rewrite using `[ha_add, map_add, add_mul]`. Set `r : B →+* Localization.Away f` to `{ toFun := fun b => loc f (a b) * g map_one' := h_one map_mul' := h_mul map_zero' := h_zero map_add' := h_add }`. Use `⟨r, ?_⟩` and prove the remaining obligations.

Use extensionality with `c show loc f (a (algebraMap R B c)) * g = loc f c`. Rewrite using `[ha_alg, map_mul]`. Take the linear combination `(loc f c) * hfg`.
-/
theorem exists_retraction_away (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (hinj : Function.Injective (algebraMap R B)) (f : R)
    (hf : ∀ b : B, ∃ a : R, algebraMap R B a = algebraMap R B f * b) :
    ∃ r : B →+* Localization.Away f, r.comp (algebraMap R B) = loc f := by
  choose a ha using hf
  set g : Localization.Away f := IsLocalization.Away.invSelf f with hg
  have hfg : loc f f * g = 1 := IsLocalization.Away.mul_invSelf f
  have ha_zero : a 0 = 0 := hinj (by simp only [ha, MulZeroClass.mul_zero, map_zero])
  have ha_one : a 1 = f := hinj (by simp only [ha, _root_.mul_one])
  have ha_add : ∀ b c, a (b + c) = a b + a c := fun b c => hinj (by simp only [ha, map_add]; ring)
  have ha_mul : ∀ b c, f * a (b * c) = a b * a c := fun b c => hinj (by simp only [ha, map_mul]; ring)
  have ha_alg : ∀ c, a (algebraMap R B c) = f * c := fun c => hinj (by simp only [ha, map_mul])
  have h_one : loc f (a 1) * g = 1 := by rw [ha_one, hfg]
  have h_mul : ∀ b c, loc f (a (b * c)) * g = loc f (a b) * g * (loc f (a c) * g) := by
    intro b c
    have h := congrArg (loc f) (ha_mul b c)
    rw [map_mul, map_mul] at h
    linear_combination (-(loc f (a (b * c)) * g)) * hfg + g * g * h
  have h_zero : loc f (a 0) * g = 0 := by rw [ha_zero, map_zero, MulZeroClass.zero_mul]
  have h_add : ∀ b c, loc f (a (b + c)) * g = loc f (a b) * g + loc f (a c) * g := by
    intro b c
    rw [ha_add, map_add, add_mul]
  let r : B →+* Localization.Away f :=
    { toFun := fun b => loc f (a b) * g
      map_one' := h_one
      map_mul' := h_mul
      map_zero' := h_zero
      map_add' := h_add }
  refine ⟨r, ?_⟩
  · ext c
    show loc f (a (algebraMap R B c)) * g = loc f c
    rw [ha_alg, map_mul]
    linear_combination (loc f c) * hfg

/- English proof (translation)
Introduce `R B _ _ _ _ _ P hD hP q₀ hq₀`. Take `⟨K, _, _, x, hker, y, hy, hu⟩` from `hP q₀ hq₀`. Take `⟨f, hfk, hfB⟩` from `exists_smul_mem_range_of_unique_point R B K x y hy hu`. Establish `hinj : Function.Injective (algebraMap R B)`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `a ha`. Use `hD a fun p hp _ => ?_` and prove the remaining obligations. Take `⟨K', _, _, x', hker', y', hy', -⟩` from `hP p hp`. Rewrite using `[← hker', RingHom.mem_ker, ← hy', RingHom.comp_apply, ha, map_zero]`. Take `⟨r, hr⟩` from `exists_retraction_away R B hinj f hfB`.

Use `⟨f, hker ▸ hfk, r, hr, fun T _ x' y' hxy => ?_⟩` and prove the remaining obligations. Use extensionality with `b`. Take `⟨a, ha⟩` from `hfB b`. Establish `h1 : y' (algebraMap R B a) = x' (loc f a)` using `RingHom.congr_fun hxy a`. Establish `h2 : y' (algebraMap R B f) = x' (loc f f)` using `RingHom.congr_fun hxy f`.

Establish `h3 : loc f a = loc f f * r b`. Rewrite using `[← RingHom.congr_fun hr a, ← RingHom.congr_fun hr f, RingHom.comp_apply, RingHom.comp_apply, ha, map_mul]`. Establish `hU : IsUnit (x' (loc f f))` using `(IsLocalization.Away.algebraMap_isUnit f).map x'`. Apply `hU.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[RingHom.comp_apply, ← map_mul, ← h3, ← h1, ha, map_mul, h2]`.
-/
theorem exists_retraction_near_of_unique_point :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.FormallyUnramified R B] (P : Set (Ideal R)), DenseP P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K), RingHom.ker x = q ∧ ∃! y : B →+* K, y.comp (algebraMap R B) = x) → ∀ q₀ ∈ P, ∃ f : R, f ∉ q₀ ∧ ∃ r : B →+* Localization.Away f, r.comp (algebraMap R B) = loc f ∧ ∀ (T : Type) [CommRing T] (x : Localization.Away f →+* T) (y : B →+* T), y.comp (algebraMap R B) = x.comp (loc f) → y = x.comp r := by
  intro R B _ _ _ _ _ P hD hP q₀ hq₀
  obtain ⟨K, _, _, x, hker, y, hy, hu⟩ := hP q₀ hq₀
  obtain ⟨f, hfk, hfB⟩ := exists_smul_mem_range_of_unique_point R B K x y hy hu
  have hinj : Function.Injective (algebraMap R B) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    refine hD a fun p hp _ => ?_
    obtain ⟨K', _, _, x', hker', y', hy', -⟩ := hP p hp
    rw [← hker', RingHom.mem_ker, ← hy', RingHom.comp_apply, ha, map_zero]
  obtain ⟨r, hr⟩ := exists_retraction_away R B hinj f hfB
  refine ⟨f, hker ▸ hfk, r, hr, fun T _ x' y' hxy => ?_⟩
  ext b
  obtain ⟨a, ha⟩ := hfB b
  have h1 : y' (algebraMap R B a) = x' (loc f a) := RingHom.congr_fun hxy a
  have h2 : y' (algebraMap R B f) = x' (loc f f) := RingHom.congr_fun hxy f
  have h3 : loc f a = loc f f * r b := by
    rw [← RingHom.congr_fun hr a, ← RingHom.congr_fun hr f, RingHom.comp_apply, RingHom.comp_apply, ha, map_mul]
  have hU : IsUnit (x' (loc f f)) := (IsLocalization.Away.algebraMap_isUnit f).map x'
  apply hU.mul_left_cancel
  rw [RingHom.comp_apply, ← map_mul, ← h3, ← h1, ha, map_mul, h2]

end GlobalTheory.ZM.NearBuild
