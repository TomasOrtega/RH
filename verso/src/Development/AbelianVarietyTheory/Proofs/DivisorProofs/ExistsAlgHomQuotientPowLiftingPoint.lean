import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfullyFlatAdicCompletionSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHartogsPropertyQuotientSpanPowRetractionStatement
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

/- English proof (translation)
Use `haveI := hE`. Use `haveI : Algebra.FormallyEtale R (Localization.AtPrime P) := Algebra.FormallyEtale.of_isLocalization P.primeCompl`. Use `haveI : Algebra.FormallySmooth R (Localization.AtPrime P ⊗[R] C) := Algebra.FormallySmooth.comp R (Localization.AtPrime P) _`. Use `haveI : Algebra.FormallyUnramified R (Localization.AtPrime P ⊗[R] C) := Algebra.FormallyUnramified.comp R (Localization.AtPrime P) _`. Set `e : Localization.AtPrime P →ₐ[R] B` to `IsLocalization.liftAlgHom (M := P.primeCompl) (f := Algebra.ofId R B) (fun y => hu y)`.

Prove the components needed by the constructor for the conclusion. Introduce `φ`. Set `ψ : Localization.AtPrime P ⊗[R] C →ₐ[R] B ⧸ I` to `Algebra.TensorProduct.productMap ((Ideal.Quotient.mkₐ R I).comp e) φ`. Use `⟨(Algebra.FormallySmooth.lift I hI ψ).comp Algebra.TensorProduct.includeRight, ?_⟩` and prove the remaining obligations. Use extensionality with `c`.

Simplify using `[Algebra.FormallySmooth.mk_lift, ψ]`. Introduce `φ₁ φ₂ h`. Establish `key : Algebra.TensorProduct.productMap e φ₁ = Algebra.TensorProduct.productMap e φ₂`. Use `Algebra.FormallyUnramified.ext I hI (fun x => ?_)` and prove the remaining obligations. Establish `h2 : (Ideal.Quotient.mkₐ R I).comp (Algebra.TensorProduct.productMap e φ₁) = (Ideal.Quotient.mkₐ R I).comp (Algebra.TensorProduct.productMap e φ₂)`.

Apply `Algebra.TensorProduct.ext'` to reduce the goal to its premises. Introduce `a c`. Use `congrArg (fun f => f c) h` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this`. Simplify using `[this]`.

Conclude with `congrArg (fun f => f x) h2`. Use extensionality with `c`. Use `congrArg (fun f => f ((1 : Localization.AtPrime P) ⊗ₜ[R] c)) key` as an intermediate fact. Simplify using `using this`.
-/
theorem lift_of_etaleAt (R C B : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing B]
    [Algebra R B] (P : Ideal R) [P.IsPrime]
    (hE : Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] C))
    (hu : ∀ s : P.primeCompl, IsUnit (algebraMap R B s)) (I : Ideal B) (hI : IsNilpotent I) :
    (∀ φ : C →ₐ[R] B ⧸ I, ∃ φ' : C →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp φ' = φ) ∧
    (∀ φ₁ φ₂ : C →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp φ₁ = (Ideal.Quotient.mkₐ R I).comp φ₂ →
      φ₁ = φ₂) := by
  haveI := hE
  haveI : Algebra.FormallyEtale R (Localization.AtPrime P) :=
    Algebra.FormallyEtale.of_isLocalization P.primeCompl
  haveI : Algebra.FormallySmooth R (Localization.AtPrime P ⊗[R] C) :=
    Algebra.FormallySmooth.comp R (Localization.AtPrime P) _
  haveI : Algebra.FormallyUnramified R (Localization.AtPrime P ⊗[R] C) :=
    Algebra.FormallyUnramified.comp R (Localization.AtPrime P) _
  let e : Localization.AtPrime P →ₐ[R] B :=
    IsLocalization.liftAlgHom (M := P.primeCompl) (f := Algebra.ofId R B) (fun y => hu y)
  constructor
  · intro φ
    let ψ : Localization.AtPrime P ⊗[R] C →ₐ[R] B ⧸ I :=
      Algebra.TensorProduct.productMap ((Ideal.Quotient.mkₐ R I).comp e) φ
    refine ⟨(Algebra.FormallySmooth.lift I hI ψ).comp Algebra.TensorProduct.includeRight, ?_⟩
    ext c
    simp [Algebra.FormallySmooth.mk_lift, ψ]
  · intro φ₁ φ₂ h
    have key : Algebra.TensorProduct.productMap e φ₁ = Algebra.TensorProduct.productMap e φ₂ := by
      refine Algebra.FormallyUnramified.ext I hI (fun x => ?_)
      have h2 : (Ideal.Quotient.mkₐ R I).comp (Algebra.TensorProduct.productMap e φ₁) =
          (Ideal.Quotient.mkₐ R I).comp (Algebra.TensorProduct.productMap e φ₂) := by
        apply Algebra.TensorProduct.ext'
        intro a c
        have := congrArg (fun f => f c) h
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
        simp [this]
      exact congrArg (fun f => f x) h2
    ext c
    have := congrArg (fun f => f ((1 : Localization.AtPrime P) ⊗ₜ[R] c)) key
    simpa using this

end GlobalTheory.GoodEtaleSection

namespace GlobalTheory.GoodEtaleSection

/- English proof (translation)
Establish `hρa : ρ (algebraMap A R (ρ r)) = ρ r` using `by simpa using congrArg (fun f => f (ρ r)) hρ`. Rewrite using `[← Ideal.mem_span_singleton, ← hker, RingHom.mem_ker, map_sub, hρa, sub_self]`.
-/
theorem sub_retract_dvd (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (ρ : R →+* A)
    (hρ : ρ.comp (algebraMap A R) = RingHom.id A) (t : R) (hker : RingHom.ker ρ = Ideal.span {t})
    (r : R) : t ∣ r - algebraMap A R (ρ r) := by
  have hρa : ρ (algebraMap A R (ρ r)) = ρ r := by simpa using congrArg (fun f => f (ρ r)) hρ
  rw [← Ideal.mem_span_singleton, ← hker, RingHom.mem_ker, map_sub, hρa, sub_self]

/- English proof (translation)
Take `⟨x, hx⟩` from `sub_retract_dvd A R ρ hρ t hker s`. Establish `e : s = algebraMap A R (ρ s) + t * x` using `by linear_combination hx`. Rewrite using `[e, map_add]`. Use `IsNilpotent.isUnit_add_left_of_commute ?_ ?_ (Commute.all _ _)` and prove the remaining obligations. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_pow, IsScalarTower.algebraMap_apply R (R ⧸ Ideal.span {t} ^ n), Ideal.Quotient.algebraMap_eq, (Ideal.Quotient.eq_zero_iff_mem).2, map_zero]`. Rewrite using `[mul_pow]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self t) n)`. Rewrite using `[IsScalarTower.algebraMap_apply R (R ⧸ Ideal.span {t} ^ n)]`. Conclude with `IsLocalization.map_units _ (⟨_, Submonoid.mem_map_of_mem _ (Submonoid.mem_map_of_mem _ hs)⟩ : Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {t} ^ n) (S.map (algebraMap A R)))`.
-/
theorem isUnit_loc (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (ρ : R →+* A)
    (hρ : ρ.comp (algebraMap A R) = RingHom.id A) (t : R) (hker : RingHom.ker ρ = Ideal.span {t})
    (n : ℕ) (S : Submonoid A) (s : R) (hs : ρ s ∈ S) :
    IsUnit (algebraMap R (Localization (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {t} ^ n)
      (S.map (algebraMap A R)))) s) := by
  obtain ⟨x, hx⟩ := sub_retract_dvd A R ρ hρ t hker s
  have e : s = algebraMap A R (ρ s) + t * x := by linear_combination hx
  rw [e, map_add]
  refine IsNilpotent.isUnit_add_left_of_commute ?_ ?_ (Commute.all _ _)
  · refine ⟨n, ?_⟩
    rw [← map_pow, IsScalarTower.algebraMap_apply R (R ⧸ Ideal.span {t} ^ n), Ideal.Quotient.algebraMap_eq,
      (Ideal.Quotient.eq_zero_iff_mem).2, map_zero]
    rw [mul_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self t) n)
  · rw [IsScalarTower.algebraMap_apply R (R ⧸ Ideal.span {t} ^ n)]
    exact IsLocalization.map_units _ (⟨_, Submonoid.mem_map_of_mem _ (Submonoid.mem_map_of_mem _ hs)⟩ :
      Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {t} ^ n) (S.map (algebraMap A R)))

/- English proof (translation)
Use `set L := Localization (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {t} ^ n) (p.primeCompl.map (algebraMap A R)))`. Set `P` to `p.comap ρ`. Use `haveI : P.IsPrime := Ideal.comap_isPrime ρ p`. Establish `hPc : P.comap (algebraMap A R) = p`. Simplify using `only [P, Ideal.comap_comap, hρ, Ideal.comap_id]`.

Establish `hE` using `hEt P (by rw [hPc]; exact hp)`. Establish `hu : ∀ s : P.primeCompl, IsUnit (algebraMap R L s)` using `fun s => isUnit_loc A R ρ hρ t hker n p.primeCompl s s.2`. Set `I : Ideal L` to `Ideal.span {algebraMap R L t}`. Establish `hI : IsNilpotent I`. Establish `h0 : algebraMap R L t ^ n = 0`.

Rewrite using `[← map_pow, IsScalarTower.algebraMap_apply R (R ⧸ Ideal.span {t} ^ n), Ideal.Quotient.algebraMap_eq, (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self t) n), map_zero]`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[show I ^ n = Ideal.span {algebraMap R L t ^ n} from Ideal.span_singleton_pow _ n, h0, Ideal.span_singleton_zero, Ideal.zero_eq_bot]`. Take `⟨hex, huniq⟩` from `lift_of_etaleAt R C L P hE hu I hI`. Set `ψ : C →ₐ[R] L ⧸ I` to `{ toRingHom := (Ideal.Quotient.mk I).comp ((algebraMap R L).comp ((algebraMap A R).comp g)) commutes' := fun r => by`.

Establish `h1 : g (algebraMap R C r) = ρ r` using `by simpa using congrArg (fun f => f r) hg`. Simplify using `only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, h1]`. Rewrite using `[← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, Ideal.mem_span_singleton, ← map_sub]`. Conclude with `map_dvd _ (dvd_sub_comm.1 (sub_retract_dvd A R ρ hρ t hker r)) }`. Establish `key : ∀ φ : C →ₐ[R] L, (∀ c, algebraMap R L t ∣ φ c - algebraMap R L (algebraMap A R (g c))) → (Ideal.Quotient.mkₐ R I).comp φ = ψ`.

Introduce `φ h`. Use extensionality with `c`. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ψ, AlgHom.coe_mk, RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Conclude with `h c`.

Use `⟨?_, fun φ₁ φ₂ h1 h2 => huniq φ₁ φ₂ ((key φ₁ h1).trans (key φ₂ h2).symm)⟩` and prove the remaining obligations. Take `⟨φ, hφ⟩` from `hex ψ`. Use `⟨φ, fun c => ?_⟩` and prove the remaining obligations. Use `congrArg (fun f => f c) hφ` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ψ, AlgHom.coe_mk, RingHom.coe_comp, Function.comp_apply] at this`.

Rewrite `this` using `[Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Conclude with `this`.
-/
theorem local_lift (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A) (t : R)
    (hker : RingHom.ker ρ = Ideal.span {t}) (hEt : GlobalTheory.GoodEtale.EtaleLow A R C) (g : C →+* A)
    (hg : g.comp (algebraMap R C) = ρ) (n : ℕ) (p : Ideal A) [p.IsPrime] (hp : p.height ≤ 1) :
    (∃ φ : C →ₐ[R] Localization (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {t} ^ n)
        (p.primeCompl.map (algebraMap A R))),
      ∀ c, algebraMap R _ t ∣ φ c - algebraMap R _ (algebraMap A R (g c))) ∧
    (∀ φ₁ φ₂ : C →ₐ[R] Localization (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {t} ^ n)
        (p.primeCompl.map (algebraMap A R))),
      (∀ c, algebraMap R _ t ∣ φ₁ c - algebraMap R _ (algebraMap A R (g c))) →
      (∀ c, algebraMap R _ t ∣ φ₂ c - algebraMap R _ (algebraMap A R (g c))) → φ₁ = φ₂) := by
  set L := Localization (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {t} ^ n)
        (p.primeCompl.map (algebraMap A R)))
  let P := p.comap ρ
  haveI : P.IsPrime := Ideal.comap_isPrime ρ p
  have hPc : P.comap (algebraMap A R) = p := by
    simp only [P, Ideal.comap_comap, hρ, Ideal.comap_id]
  have hE := hEt P (by rw [hPc]; exact hp)
  have hu : ∀ s : P.primeCompl, IsUnit (algebraMap R L s) := fun s =>
    isUnit_loc A R ρ hρ t hker n p.primeCompl s s.2
  let I : Ideal L := Ideal.span {algebraMap R L t}
  have hI : IsNilpotent I := by
    have h0 : algebraMap R L t ^ n = 0 := by
      rw [← map_pow, IsScalarTower.algebraMap_apply R (R ⧸ Ideal.span {t} ^ n), Ideal.Quotient.algebraMap_eq,
        (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self t) n), map_zero]
    refine ⟨n, ?_⟩
    rw [show I ^ n = Ideal.span {algebraMap R L t ^ n} from Ideal.span_singleton_pow _ n, h0,
      Ideal.span_singleton_zero, Ideal.zero_eq_bot]
  obtain ⟨hex, huniq⟩ := lift_of_etaleAt R C L P hE hu I hI
  let ψ : C →ₐ[R] L ⧸ I :=
    { toRingHom := (Ideal.Quotient.mk I).comp ((algebraMap R L).comp ((algebraMap A R).comp g))
      commutes' := fun r => by
        have h1 : g (algebraMap R C r) = ρ r := by simpa using congrArg (fun f => f r) hg
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, h1]
        rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, Ideal.mem_span_singleton, ← map_sub]
        exact map_dvd _ (dvd_sub_comm.1 (sub_retract_dvd A R ρ hρ t hker r)) }
  have key : ∀ φ : C →ₐ[R] L, (∀ c, algebraMap R L t ∣ φ c - algebraMap R L (algebraMap A R (g c))) →
      (Ideal.Quotient.mkₐ R I).comp φ = ψ := by
    intro φ h
    ext c
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ψ, AlgHom.coe_mk, RingHom.coe_comp,
      Function.comp_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact h c
  refine ⟨?_, fun φ₁ φ₂ h1 h2 => huniq φ₁ φ₂ ((key φ₁ h1).trans (key φ₂ h2).symm)⟩
  obtain ⟨φ, hφ⟩ := hex ψ
  refine ⟨φ, fun c => ?_⟩
  have := congrArg (fun f => f c) hφ
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ψ, AlgHom.coe_mk, RingHom.coe_comp,
      Function.comp_apply] at this
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at this
  exact this

end GlobalTheory.GoodEtaleSection

namespace GlobalTheory.GoodEtaleSection

/- English proof (translation)
Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Take `⟨r', rfl⟩` from `Ideal.Quotient.mk_surjective y`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Rewrite using `[(Ideal.Quotient.eq_zero_iff_mem).2 (show r ∈ Ideal.span {t} ^ 0 by simp)]`. Conclude with `Ideal.zero_mem _`.

Rewrite `h` using `[← map_mul, ← map_mul, Ideal.Quotient.eq]`. Establish `h1 : r * algebraMap A R a - t * r' ∈ Ideal.span {t}` using `Ideal.pow_le_self hn.ne' h`. Establish `h2 : algebraMap A R a * r ∈ Ideal.span {t ^ 1}`. Rewrite using `[pow_one]`. Use `Ideal.add_mem _ h1 (Ideal.mul_mem_right r' _ (Ideal.mem_span_singleton_self t))` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel, mul_comm]`. Conclude with `this`. Take `⟨q, rfl⟩` from `Ideal.mem_span_singleton.1 (by simpa using mem_pow_of_mul_mem_pow A R ρ hρ t hker ht a ha 1 r h2)`. Rewrite using `[map_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`.
-/
theorem mem_span_of_mul_eq (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A) (t : R)
    (hker : RingHom.ker ρ = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R) (n : ℕ) (a : A) (ha : a ≠ 0)
    (z y : R ⧸ Ideal.span {t} ^ n)
    (h : z * Ideal.Quotient.mk _ (algebraMap A R a) = Ideal.Quotient.mk _ t * y) :
    z ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t} := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective y
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [(Ideal.Quotient.eq_zero_iff_mem).2 (show r ∈ Ideal.span {t} ^ 0 by simp)]
    exact Ideal.zero_mem _
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq] at h
  have h1 : r * algebraMap A R a - t * r' ∈ Ideal.span {t} := Ideal.pow_le_self hn.ne' h
  have h2 : algebraMap A R a * r ∈ Ideal.span {t ^ 1} := by
    rw [pow_one]
    have := Ideal.add_mem _ h1 (Ideal.mul_mem_right r' _ (Ideal.mem_span_singleton_self t))
    rw [sub_add_cancel, mul_comm] at this
    exact this
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.1
    (by simpa using mem_pow_of_mul_mem_pow A R ρ hρ t hker ht a ha 1 r h2)
  rw [map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Introduce `A R C _ _ _ _ _ _ _ _ _ _ ρ hρ t hker ht hEt g hg n`. Establish `hbot1 : (⊥ : Ideal A).height ≤ 1` using `by simp`. Use `set B := R ⧸ Ideal.span {t} ^ n`. Use `set M0 := Algebra.algebraMapSubmonoid B ((⊥ : Ideal A).primeCompl.map (algebraMap A R))`. Use `set L0 := Localization M0`.

Take `⟨⟨φ₀, hφ₀⟩, huniq⟩ : (∃ φ : C →ₐ[R] L0, ∀ c, algebraMap R L0 t ∣ φ c - algebraMap R L0 (algebraMap A R (g c))) ∧ (∀ φ₁ φ₂ : C →ₐ[R] L0, (∀ c, algebraMap R L0 t ∣ φ₁ c - algebraMap R L0 (algebraMap A R (g c))) → (∀ c, algebraMap R L0 t ∣ φ₂ c - algebraMap R L0 (algebraMap A R (g c …` from `local_lift A R C ρ hρ t hker hEt g hg n ⊥ hbot1`. Establish `hne : ∀ a : A, a ∈ (⊥ : Ideal A).primeCompl → a ≠ 0`. Introduce and unpack `a ha rfl`. Conclude with `ha (Ideal.zero_mem _)`. Establish `hM0 : M0 ≤ nonZeroDivisors B`.

Introduce and unpack `_ ⟨_, ⟨a, ha, rfl⟩, rfl⟩`. Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `x hx`. Use `torsionFree_quot A R ρ hρ t hker ht n a (hne a ha) x ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`.

Conclude with `hx`. Establish `hinj : Function.Injective (algebraMap B L0)` using `IsLocalization.injective L0 hM0`. Set `ι : B →ₐ[R] L0` to `IsScalarTower.toAlgHom R B L0`. Establish `hι : ∀ b, ι b = algebraMap B L0 b` using `fun b => rfl`. Establish `hRL : ∀ r : R, algebraMap R L0 r = algebraMap B L0 (Ideal.Quotient.mk _ r)` using `fun r => IsScalarTower.algebraMap_apply R B L0 r`.

Establish `hHart` using `GlobalTheory.T.hasHartogsProperty_quotient_span_pow_retraction A R ρ hρ t hker ht n`. Establish `hmem : ∀ c, φ₀ c ∈ ι.range`. Introduce `c`. Take `⟨⟨x, m⟩, hxm⟩` from `IsLocalization.mk'_surjective M0 (φ₀ c)`. Establish `hspec` using `IsLocalization.mk'_spec L0 x m`.

Simplify using `only at hxm`. Rewrite `hspec` using `[hxm]`. Take `⟨_, ⟨a, ha, rfl⟩, hm⟩` from `m.2`. Take `⟨x', hx'⟩` from `hHart a (hne a ha) x (fun p hp hh => by haveI := hp`. Take `⟨⟨φp, hφp⟩, -⟩` from `local_lift A R C ρ hρ t hker hEt g hg n p hh`.

Establish `hle : Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R)) ≤ M0`. Introduce and unpack `_ ⟨_, ⟨u, hu, rfl⟩, rfl⟩`. Use `⟨_, ⟨u, ?_, rfl⟩, rfl⟩` and prove the remaining obligations. Introduce and unpack `(h : u ∈ (⊥ : Ideal A))`. Rewrite `h` using `[Ideal.mem_bot]`.

Conclude with `hu (h ▸ p.zero_mem)`. Set `j` to `IsLocalization.liftAlgHom (M := Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R))) (S := Localization (Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R)))) (f := ι) (fun y => IsLocalization.map_units L0 (⟨y, hle y.2⟩ : M0))`. Establish `hj : ∀ b, j (algebraMap B _ b) = algebraMap B L0 b` using `fun b => by`. Simplify using `only [j, IsLocalization.liftAlgHom_apply]`. Conclude with `IsLocalization.lift_eq _ b`.

Establish `hjφ : j.comp φp = φ₀` using `huniq _ _ (fun c => by`. Use `map_dvd j (hφp c)` as an intermediate fact. Rewrite `this` using `[map_sub, j.commutes, j.commutes]`. Conclude with `this) hφ₀`. Take `⟨⟨y, m'⟩, hym⟩` from `IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R))) (φp c)`.

Establish `hspec'` using `IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R)))) y m'`. Simplify using `only at hym`. Rewrite `hspec'` using `[hym]`. Establish `hspec''` using `congrArg j hspec'`. Rewrite `hspec''` using `[map_mul, hj, hj, ← AlgHom.comp_apply, hjφ]`.

Take `⟨_, ⟨u, hu, rfl⟩, hm'⟩` from `m'.2`. Use `⟨u, hu, y, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Algebra.smul_def]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, ← hspec, ← hspec'', Ideal.Quotient.algebraMap_eq]`.

Rewrite using `[← hm, ← hm', Ideal.Quotient.algebraMap_eq]`. Use the proof step `ring)`. Use `⟨x', ?_⟩` and prove the remaining obligations. Use `show algebraMap B L0 x' = φ₀ c`. Establish `hu` using `IsLocalization.map_units L0 m`.

Use `(hu.mul_left_inj).1 ?_` and prove the remaining obligations. Rewrite using `[hspec, hx', Algebra.smul_def, map_mul, hm]`. Expand and normalize the polynomial expressions, which then agree. Set `f : C →ₐ[R] B` to `(AlgEquiv.ofInjective ι hinj).symm.toAlgHom.comp (φ₀.codRestrict ι.range hmem)`. Establish `hf : ∀ c, algebraMap B L0 (f c) = φ₀ c`.

Introduce `c`. Establish `h1 : (AlgEquiv.ofInjective ι hinj) (f c) = ⟨φ₀ c, hmem c⟩` using `(AlgEquiv.ofInjective ι hinj).apply_symm_apply _`. Conclude with `congrArg Subtype.val h1`. Use `⟨f, fun c => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `hφ₀ c`.

Take `⟨⟨y, m⟩, hym⟩` from `IsLocalization.mk'_surjective M0 w`. Establish `hspec` using `IsLocalization.mk'_spec L0 y m`. Simplify using `only at hym`. Rewrite `hspec` using `[hym]`. Take `⟨_, ⟨a, ha, rfl⟩, hm⟩` from `m.2`.

Use `mem_span_of_mul_eq A R ρ hρ t hker ht n a (hne a ha) _ y ?_` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, map_sub, hf, ← hRL, hw, ← hRL, hRL t, hRL, mul_assoc]`. Rewrite using `[show Ideal.Quotient.mk (Ideal.span {t} ^ n) (algebraMap A R a) = (m : B) from hm, hspec]`.
-/
theorem exists_algHom_quot_pow : ∀ (A R C : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra A R]
    [CommRing C] [Algebra R C] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    GlobalTheory.GoodEtale.EtaleLow A R C →
    ∀ g : C →+* A, g.comp (algebraMap R C) = ρ →
    ∀ n : ℕ, ∃ f : C →ₐ[R] R ⧸ Ideal.span {t} ^ n, ∀ c : C,
      f c - Ideal.Quotient.mk (Ideal.span {t} ^ n) (algebraMap A R (g c)) ∈
        Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t} := by
  intro A R C _ _ _ _ _ _ _ _ _ _ ρ hρ t hker ht hEt g hg n
  have hbot1 : (⊥ : Ideal A).height ≤ 1 := by simp
  set B := R ⧸ Ideal.span {t} ^ n
  set M0 := Algebra.algebraMapSubmonoid B ((⊥ : Ideal A).primeCompl.map (algebraMap A R))
  set L0 := Localization M0
  obtain ⟨⟨φ₀, hφ₀⟩, huniq⟩ : (∃ φ : C →ₐ[R] L0,
      ∀ c, algebraMap R L0 t ∣ φ c - algebraMap R L0 (algebraMap A R (g c))) ∧
    (∀ φ₁ φ₂ : C →ₐ[R] L0,
      (∀ c, algebraMap R L0 t ∣ φ₁ c - algebraMap R L0 (algebraMap A R (g c))) →
      (∀ c, algebraMap R L0 t ∣ φ₂ c - algebraMap R L0 (algebraMap A R (g c))) → φ₁ = φ₂) :=
    local_lift A R C ρ hρ t hker hEt g hg n ⊥ hbot1
  have hne : ∀ a : A, a ∈ (⊥ : Ideal A).primeCompl → a ≠ 0 := by
    rintro a ha rfl; exact ha (Ideal.zero_mem _)
  have hM0 : M0 ≤ nonZeroDivisors B := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    refine torsionFree_quot A R ρ hρ t hker ht n a (hne a ha) x ?_
    rw [Algebra.smul_def, mul_comm]
    exact hx
  have hinj : Function.Injective (algebraMap B L0) := IsLocalization.injective L0 hM0
  let ι : B →ₐ[R] L0 := IsScalarTower.toAlgHom R B L0
  have hι : ∀ b, ι b = algebraMap B L0 b := fun b => rfl
  have hRL : ∀ r : R, algebraMap R L0 r = algebraMap B L0 (Ideal.Quotient.mk _ r) := fun r =>
    IsScalarTower.algebraMap_apply R B L0 r
  have hHart := GlobalTheory.T.hasHartogsProperty_quotient_span_pow_retraction A R ρ hρ t hker ht n
  have hmem : ∀ c, φ₀ c ∈ ι.range := by
    intro c
    obtain ⟨⟨x, m⟩, hxm⟩ := IsLocalization.mk'_surjective M0 (φ₀ c)
    have hspec := IsLocalization.mk'_spec L0 x m
    simp only at hxm
    rw [hxm] at hspec
    obtain ⟨_, ⟨a, ha, rfl⟩, hm⟩ := m.2
    obtain ⟨x', hx'⟩ := hHart a (hne a ha) x (fun p hp hh => by
      haveI := hp
      obtain ⟨⟨φp, hφp⟩, -⟩ := local_lift A R C ρ hρ t hker hEt g hg n p hh
      have hle : Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R)) ≤ M0 := by
        rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨_, ⟨u, ?_, rfl⟩, rfl⟩
        rintro (h : u ∈ (⊥ : Ideal A))
        rw [Ideal.mem_bot] at h
        exact hu (h ▸ p.zero_mem)
      let j := IsLocalization.liftAlgHom
        (M := Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R)))
        (S := Localization (Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R))))
        (f := ι) (fun y => IsLocalization.map_units L0 (⟨y, hle y.2⟩ : M0))
      have hj : ∀ b, j (algebraMap B _ b) = algebraMap B L0 b := fun b => by
        simp only [j, IsLocalization.liftAlgHom_apply]
        exact IsLocalization.lift_eq _ b
      have hjφ : j.comp φp = φ₀ := huniq _ _ (fun c => by
        have := map_dvd j (hφp c)
        rw [map_sub, j.commutes, j.commutes] at this
        exact this) hφ₀
      obtain ⟨⟨y, m'⟩, hym⟩ := IsLocalization.mk'_surjective
        (Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R))) (φp c)
      have hspec' := IsLocalization.mk'_spec
        (Localization (Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R)))) y m'
      simp only at hym
      rw [hym] at hspec'
      have hspec'' := congrArg j hspec'
      rw [map_mul, hj, hj, ← AlgHom.comp_apply, hjφ] at hspec''
      obtain ⟨_, ⟨u, hu, rfl⟩, hm'⟩ := m'.2
      refine ⟨u, hu, y, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def]
      apply hinj
      rw [map_mul, map_mul, ← hspec, ← hspec'', Ideal.Quotient.algebraMap_eq]
      rw [← hm, ← hm', Ideal.Quotient.algebraMap_eq]
      ring)
    refine ⟨x', ?_⟩
    show algebraMap B L0 x' = φ₀ c
    have hu := IsLocalization.map_units L0 m
    refine (hu.mul_left_inj).1 ?_
    rw [hspec, hx', Algebra.smul_def, map_mul, hm]
    ring
  let f : C →ₐ[R] B := (AlgEquiv.ofInjective ι hinj).symm.toAlgHom.comp (φ₀.codRestrict ι.range hmem)
  have hf : ∀ c, algebraMap B L0 (f c) = φ₀ c := by
    intro c
    have h1 : (AlgEquiv.ofInjective ι hinj) (f c) = ⟨φ₀ c, hmem c⟩ :=
      (AlgEquiv.ofInjective ι hinj).apply_symm_apply _
    exact congrArg Subtype.val h1
  refine ⟨f, fun c => ?_⟩
  obtain ⟨w, hw⟩ := hφ₀ c
  obtain ⟨⟨y, m⟩, hym⟩ := IsLocalization.mk'_surjective M0 w
  have hspec := IsLocalization.mk'_spec L0 y m
  simp only at hym
  rw [hym] at hspec
  obtain ⟨_, ⟨a, ha, rfl⟩, hm⟩ := m.2
  refine mem_span_of_mul_eq A R ρ hρ t hker ht n a (hne a ha) _ y ?_
  apply hinj
  rw [map_mul, map_mul, map_sub, hf, ← hRL, hw, ← hRL, hRL t, hRL, mul_assoc]
  rw [show Ideal.Quotient.mk (Ideal.span {t} ^ n) (algebraMap A R a) = (m : B) from hm, hspec]

end GlobalTheory.GoodEtaleSection
