import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing

namespace GlobalTheory.SquareZeroLift

/- English proof (translation)
Use `haveI : Algebra.FormallyEtale R (Localization.Away g) := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g)`. Use `haveI : Algebra.FormallyEtale R (TensorProduct R (Localization.Away g) A) := Algebra.FormallyEtale.comp R (Localization.Away g) _`. Establish `unit : ∀ (P : Type) [CommRing P] [Algebra R P], IsUnit (algebraMap R P g) → ∀ y : Submonoid.powers g, IsUnit ((Algebra.ofId R P) (y : R))`. Introduce `P _ _ h y`. Take `⟨n, hn⟩` from `y.2`.

Rewrite using `[← hn]`. Simplify using `only [map_pow]`. Conclude with `h.pow n`. Set `e : Localization.Away g →ₐ[R] C` to `IsLocalization.liftAlgHom (M := Submonoid.powers g) (unit C hg)`. Establish `hg' : IsUnit (algebraMap R (C ⧸ J) g)`.

Rewrite using `[IsScalarTower.algebraMap_apply R C (C ⧸ J)]`. Conclude with `hg.map _`. Set `e' : Localization.Away g →ₐ[R] C ⧸ J` to `IsLocalization.liftAlgHom (M := Submonoid.powers g) (unit (C ⧸ J) hg')`. Set `F : TensorProduct R (Localization.Away g) A →ₐ[R] C ⧸ J` to `Algebra.TensorProduct.lift e' f (fun _ _ => Commute.all _ _)`. Establish `hsurj : Function.Surjective (Ideal.Quotient.mkₐ R J)` using `Ideal.Quotient.mkₐ_surjective R J`.

Establish `hnil : IsNilpotent (RingHom.ker (Ideal.Quotient.mkₐ R J : C →+* C ⧸ J))`. Use `⟨2, ?_⟩` and prove the remaining obligations. Establish `: RingHom.ker (Ideal.Quotient.mkₐ R J : C →+* C ⧸ J) = J`. Use extensionality with `x`. Simplify using `[Ideal.Quotient.eq_zero_iff_mem]`.

Rewrite using `[this, hJ]`. Both sides reduce to the same expression. Use `⟨(Algebra.FormallySmooth.liftOfSurjective F _ hsurj hnil).comp Algebra.TensorProduct.includeRight, ?_, ?_⟩` and prove the remaining obligations. Use `show (Ideal.Quotient.mkₐ R J).comp ((Algebra.FormallySmooth.liftOfSurjective F _ hsurj hnil).comp Algebra.TensorProduct.includeRight) = f`. Rewrite using `[← AlgHom.comp_assoc, Algebra.FormallySmooth.comp_liftOfSurjective]`.

Use extensionality with `a`. Simplify using `[F]`. Introduce `α hα`. Set `E1 : TensorProduct R (Localization.Away g) A →ₐ[R] C` to `Algebra.TensorProduct.lift e α (fun _ _ => Commute.all _ _)`. Set `E2 : TensorProduct R (Localization.Away g) A →ₐ[R] C` to `Algebra.FormallySmooth.liftOfSurjective F _ hsurj hnil`.

Establish `hE : E1 = E2`. Apply `Algebra.FormallyUnramified.comp_injective J hJ` to reduce the goal to its premises. Apply `Algebra.TensorProduct.ext` to reduce the goal to its premises. Conclude with `(IsLocalization.algHom_subsingleton (Submonoid.powers g)).elim _ _`. Rewrite using `[show E2 = Algebra.FormallySmooth.liftOfSurjective F _ hsurj hnil from rfl]`.

Use extensionality with `a`. Establish `h2` using `congrArg (fun φ => φ (Algebra.TensorProduct.includeRight a)) (Algebra.FormallySmooth.comp_liftOfSurjective F _ hsurj hnil)`. Simplify using `only [AlgHom.comp_apply] at h2`. Simplify using `only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, h2]`. Simplify using `[E1, F, ← hα]`.

Establish `: α = E1.comp Algebra.TensorProduct.includeRight` using `by ext a; simp [E1]`. Rewrite using `[this, hE]`.
-/
theorem localLift (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (g : R)
    [Algebra.FormallyEtale (Localization.Away g) (TensorProduct R (Localization.Away g) A)]
    (C : Type) [CommRing C] [Algebra R C] (hg : IsUnit (algebraMap R C g)) (J : Ideal C)
    (hJ : J ^ 2 = ⊥) (f : A →ₐ[R] C ⧸ J) :
    ∃! α : A →ₐ[R] C, (Ideal.Quotient.mkₐ R J).comp α = f := by
  haveI : Algebra.FormallyEtale R (Localization.Away g) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g)
  haveI : Algebra.FormallyEtale R (TensorProduct R (Localization.Away g) A) :=
    Algebra.FormallyEtale.comp R (Localization.Away g) _
  have unit : ∀ (P : Type) [CommRing P] [Algebra R P], IsUnit (algebraMap R P g) →
      ∀ y : Submonoid.powers g, IsUnit ((Algebra.ofId R P) (y : R)) := by
    intro P _ _ h y
    obtain ⟨n, hn⟩ := y.2
    rw [← hn]; simp only [map_pow]; exact h.pow n
  let e : Localization.Away g →ₐ[R] C :=
    IsLocalization.liftAlgHom (M := Submonoid.powers g) (unit C hg)
  have hg' : IsUnit (algebraMap R (C ⧸ J) g) := by
    rw [IsScalarTower.algebraMap_apply R C (C ⧸ J)]; exact hg.map _
  let e' : Localization.Away g →ₐ[R] C ⧸ J :=
    IsLocalization.liftAlgHom (M := Submonoid.powers g) (unit (C ⧸ J) hg')
  let F : TensorProduct R (Localization.Away g) A →ₐ[R] C ⧸ J :=
    Algebra.TensorProduct.lift e' f (fun _ _ => Commute.all _ _)
  have hsurj : Function.Surjective (Ideal.Quotient.mkₐ R J) := Ideal.Quotient.mkₐ_surjective R J
  have hnil : IsNilpotent (RingHom.ker (Ideal.Quotient.mkₐ R J : C →+* C ⧸ J)) := by
    refine ⟨2, ?_⟩
    have : RingHom.ker (Ideal.Quotient.mkₐ R J : C →+* C ⧸ J) = J := by
      ext x; simp [Ideal.Quotient.eq_zero_iff_mem]
    rw [this, hJ]; rfl
  refine ⟨(Algebra.FormallySmooth.liftOfSurjective F _ hsurj hnil).comp
    Algebra.TensorProduct.includeRight, ?_, ?_⟩
  · show (Ideal.Quotient.mkₐ R J).comp ((Algebra.FormallySmooth.liftOfSurjective F _ hsurj hnil).comp
      Algebra.TensorProduct.includeRight) = f
    rw [← AlgHom.comp_assoc, Algebra.FormallySmooth.comp_liftOfSurjective]
    ext a; simp [F]
  · intro α hα
    let E1 : TensorProduct R (Localization.Away g) A →ₐ[R] C :=
      Algebra.TensorProduct.lift e α (fun _ _ => Commute.all _ _)
    let E2 : TensorProduct R (Localization.Away g) A →ₐ[R] C :=
      Algebra.FormallySmooth.liftOfSurjective F _ hsurj hnil
    have hE : E1 = E2 := by
      apply Algebra.FormallyUnramified.comp_injective J hJ
      apply Algebra.TensorProduct.ext
      · exact (IsLocalization.algHom_subsingleton (Submonoid.powers g)).elim _ _
      · rw [show E2 = Algebra.FormallySmooth.liftOfSurjective F _ hsurj hnil from rfl]
        ext a
        have h2 := congrArg (fun φ => φ (Algebra.TensorProduct.includeRight a))
          (Algebra.FormallySmooth.comp_liftOfSurjective F _ hsurj hnil)
        simp only [AlgHom.comp_apply] at h2
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, h2]
        simp [E1, F, ← hα]
    have : α = E1.comp Algebra.TensorProduct.includeRight := by ext a; simp [E1]
    rw [this, hE]

end GlobalTheory.SquareZeroLift

namespace GlobalTheory.SquareZeroLift

open RingTheory.Sequence
open scoped Pointwise

/- English proof (translation)
Rewrite `h` using `[isWeaklyRegular_cons_iff, isWeaklyRegular_cons_iff]`. Take `⟨hx, hy, -⟩` from `h`. Establish `step : ∀ s u : M, y • s = x • u → ∃ v : M, s = x • v`. Introduce `s u hsu`. Establish `h0 : y • (Submodule.Quotient.mk s : M ⧸ x • (⊤ : Submodule R M)) = y • 0`.

Rewrite using `[smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsu]`. Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top`. Establish `h1` using `hy h0`. Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨v, -, hv⟩` from `h1`.

Conclude with `⟨v, hv.symm⟩`. Establish `P : ∀ (a : ℕ) (s u : M), y • s = x ^ a • u → ∃ v : M, s = x ^ a • v`. Introduce `a`. Proceed by induction on `a with`. Consider the case `zero => intro s u _; exact ⟨s, by simp⟩`.

Consider the case `succ a ih`. Introduce `s u hsu`. Rewrite `hsu` using `[pow_succ', mul_smul]`. Take `⟨s1, rfl⟩` from `step s _ hsu`. Rewrite `hsu` using `[smul_comm]`.

Take `⟨v, rfl⟩` from `ih s1 u (hx hsu)`. Conclude with `⟨v, by rw [pow_succ', mul_smul]⟩`. Proceed by induction on `b generalizing s with`. Consider the case `zero => exact ⟨u, by simpa using hsu⟩`. Consider the case `succ b ih`.

Rewrite `hsu` using `[pow_succ, mul_smul]`. Take `⟨v, hv⟩` from `ih (y • s) hsu`. Conclude with `P a s v hv`.
-/
theorem pow_dvd_of_weaklyRegular {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (x y : R)
    (h : IsWeaklyRegular M [x, y]) (a b : ℕ) (s u : M) (hsu : y ^ b • s = x ^ a • u) :
    ∃ v : M, s = x ^ a • v := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_cons_iff] at h
  obtain ⟨hx, hy, -⟩ := h
  have step : ∀ s u : M, y • s = x • u → ∃ v : M, s = x • v := by
    intro s u hsu
    have h0 : y • (Submodule.Quotient.mk s : M ⧸ x • (⊤ : Submodule R M)) = y • 0 := by
      rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsu]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    have h1 := hy h0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨v, -, hv⟩ := h1
    exact ⟨v, hv.symm⟩
  have P : ∀ (a : ℕ) (s u : M), y • s = x ^ a • u → ∃ v : M, s = x ^ a • v := by
    intro a
    induction a with
    | zero => intro s u _; exact ⟨s, by simp⟩
    | succ a ih =>
      intro s u hsu
      rw [pow_succ', mul_smul] at hsu
      obtain ⟨s1, rfl⟩ := step s _ hsu
      rw [smul_comm] at hsu
      obtain ⟨v, rfl⟩ := ih s1 u (hx hsu)
      exact ⟨v, by rw [pow_succ', mul_smul]⟩
  induction b generalizing s with
  | zero => exact ⟨u, by simpa using hsu⟩
  | succ b ih =>
    rw [pow_succ, mul_smul] at hsu
    obtain ⟨v, hv⟩ := ih (y • s) hsu
    exact P a s v hv

section
variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A]
  {S T : Type} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
  (π : S →ₐ[R] T) (φ : A →ₐ[R] T)

def Lifts {C : Type} [CommRing C] [Algebra R C] (σ : S →ₐ[R] C) (α : A →ₐ[R] C) : Prop :=
  ∀ a s, π s = φ a → α a - σ s ∈ (RingHom.ker π).map σ

/- English proof (translation)
Introduce `a s hs`. Establish `h1` using `Ideal.mem_map_of_mem ρ (h a s hs)`. Rewrite `h1` using `[map_sub]`. Establish `h2 : Ideal.map ρ (Ideal.map σ (RingHom.ker π)) = Ideal.map (ρ.comp σ) (RingHom.ker π)`. Conclude with `Ideal.map_map (σ : S →+* C) (ρ : C →+* D) (I := RingHom.ker π)`.

Rewrite `h1` using `[h2]`. Simplify using `using h1`.
-/
theorem Lifts.comp {C D : Type} [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    {σ : S →ₐ[R] C} {α : A →ₐ[R] C} (h : Lifts π φ σ α) (ρ : C →ₐ[R] D) :
    Lifts π φ (ρ.comp σ) (ρ.comp α) := by
  intro a s hs
  have h1 := Ideal.mem_map_of_mem ρ (h a s hs)
  rw [map_sub] at h1
  have h2 : Ideal.map ρ (Ideal.map σ (RingHom.ker π)) = Ideal.map (ρ.comp σ) (RingHom.ker π) := by
    exact Ideal.map_map (σ : S →+* C) (ρ : C →+* D) (I := RingHom.ker π)
  rw [h2] at h1
  simpa using h1

/- English proof (translation)
Use `haveI := hA`. Use `set J := (RingHom.ker π).map σ with hJdef`. Establish `hJ : J ^ 2 = ⊥` using `by rw [hJdef, ← Ideal.map_pow, hI, Ideal.map_bot]`. Set `e` to `Ideal.quotientKerAlgEquivOfSurjective hπ`. Set `q : S ⧸ RingHom.ker π.toRingHom →ₐ[R] C ⧸ J` to `Ideal.quotientMapₐ J σ Ideal.le_comap_map`.

Set `tgt : A →ₐ[R] C ⧸ J` to `q.comp (e.symm.toAlgHom.comp φ)`. Establish `htgt : ∀ a s, π s = φ a → tgt a = Ideal.Quotient.mk J (σ s)`. Introduce `a s hs`. Establish `: e.symm (φ a) = Ideal.Quotient.mk _ s`. Rewrite using `[AlgEquiv.symm_apply_eq, ← hs]`.

Both sides reduce to the same expression. Use `show q (e.symm (φ a)) = _`. Rewrite using `[this]`. Both sides reduce to the same expression. Establish `key : ∀ α : A →ₐ[R] C, Lifts π φ σ α ↔ (Ideal.Quotient.mkₐ R J).comp α = tgt`.

Introduce `α`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `a`. Take `⟨s, hs⟩` from `hπ (φ a)`.

Rewrite using `[AlgHom.comp_apply, htgt a s hs, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]`. Conclude with `h a s hs`. Introduce `h a s hs`. Use `congrArg (fun f => f a) h` as an intermediate fact. Simplify using `only [AlgHom.comp_apply] at this`.

Rewrite `this` using `[htgt a s hs, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]`. Conclude with `this`. Take `⟨α, hα, huniq⟩` from `localLift R A g C hg J hJ tgt`. Conclude with `⟨α, (key α).2 hα, fun β hβ => huniq β ((key β).1 hβ)⟩`.
-/
theorem existsUnique_lifts (hπ : Function.Surjective π) (hI : RingHom.ker π ^ 2 = ⊥) (g : R)
    (hA : Algebra.FormallyEtale (Localization.Away g) (TensorProduct R (Localization.Away g) A))
    {C : Type} [CommRing C] [Algebra R C] (σ : S →ₐ[R] C) (hg : IsUnit (algebraMap R C g)) :
    ∃! α : A →ₐ[R] C, Lifts π φ σ α := by
  haveI := hA
  set J := (RingHom.ker π).map σ with hJdef
  have hJ : J ^ 2 = ⊥ := by rw [hJdef, ← Ideal.map_pow, hI, Ideal.map_bot]
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let q : S ⧸ RingHom.ker π.toRingHom →ₐ[R] C ⧸ J :=
    Ideal.quotientMapₐ J σ Ideal.le_comap_map
  let tgt : A →ₐ[R] C ⧸ J := q.comp (e.symm.toAlgHom.comp φ)
  have htgt : ∀ a s, π s = φ a → tgt a = Ideal.Quotient.mk J (σ s) := by
    intro a s hs
    have : e.symm (φ a) = Ideal.Quotient.mk _ s := by
      rw [AlgEquiv.symm_apply_eq, ← hs]; rfl
    show q (e.symm (φ a)) = _
    rw [this]; rfl
  have key : ∀ α : A →ₐ[R] C, Lifts π φ σ α ↔ (Ideal.Quotient.mkₐ R J).comp α = tgt := by
    intro α; constructor
    · intro h; ext a; obtain ⟨s, hs⟩ := hπ (φ a)
      rw [AlgHom.comp_apply, htgt a s hs, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
      exact h a s hs
    · intro h a s hs
      have := congrArg (fun f => f a) h
      simp only [AlgHom.comp_apply] at this
      rw [htgt a s hs, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at this
      exact this
  obtain ⟨α, hα, huniq⟩ := localLift R A g C hg J hJ tgt
  exact ⟨α, (key α).2 hα, fun β hβ => huniq β ((key β).1 hβ)⟩

end

end GlobalTheory.SquareZeroLift

namespace GlobalTheory.SquareZeroLift

section
variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]

noncomputable def toAway (g : R) : S →ₐ[R] Localization.Away (algebraMap R S g) :=
  IsScalarTower.toAlgHom R S _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toAway_apply (g : R) (s : S) : toAway S g s = algebraMap S _ s := rfl

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply R S]`. Conclude with `IsLocalization.Away.algebraMap_isUnit (algebraMap R S g)`.
-/
theorem isUnit_toAway (g : R) : IsUnit (algebraMap R (Localization.Away (algebraMap R S g)) g) := by
  rw [IsScalarTower.algebraMap_apply R S]
  exact IsLocalization.Away.algebraMap_isUnit (algebraMap R S g)

/- English proof (translation)
Use `IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap R S (g * h))) (algebraMap R S (g * h))` as an intermediate fact. Establish `e : algebraMap S (Localization.Away (algebraMap R S (g * h))) (algebraMap R S (g * h)) = algebraMap S _ (algebraMap R S g) * algebraMap S _ (algebraMap R S h)`. Rewrite using `[map_mul, map_mul]`. Rewrite `this` using `[e]`. Conclude with `isUnit_of_mul_isUnit_left this`.
-/
theorem isUnit_left (g h : R) :
    IsUnit (algebraMap S (Localization.Away (algebraMap R S (g * h))) (algebraMap R S g)) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap R S (g * h)))
    (algebraMap R S (g * h))
  have e : algebraMap S (Localization.Away (algebraMap R S (g * h))) (algebraMap R S (g * h)) =
      algebraMap S _ (algebraMap R S g) * algebraMap S _ (algebraMap R S h) := by
    rw [map_mul, map_mul]
  rw [e] at this
  exact isUnit_of_mul_isUnit_left this

/- English proof (translation)
Use `IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap R S (g * h))) (algebraMap R S (g * h))` as an intermediate fact. Establish `e : algebraMap S (Localization.Away (algebraMap R S (g * h))) (algebraMap R S (g * h)) = algebraMap S _ (algebraMap R S g) * algebraMap S _ (algebraMap R S h)`. Rewrite using `[map_mul, map_mul]`. Rewrite `this` using `[e]`. Conclude with `isUnit_of_mul_isUnit_right this`.
-/
theorem isUnit_right (g h : R) :
    IsUnit (algebraMap S (Localization.Away (algebraMap R S (g * h))) (algebraMap R S h)) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap R S (g * h)))
    (algebraMap R S (g * h))
  have e : algebraMap S (Localization.Away (algebraMap R S (g * h))) (algebraMap R S (g * h)) =
      algebraMap S _ (algebraMap R S g) * algebraMap S _ (algebraMap R S h) := by
    rw [map_mul, map_mul]
  rw [e] at this
  exact isUnit_of_mul_isUnit_right this

noncomputable def toMulLeft (g h : R) :
    Localization.Away (algebraMap R S g) →ₐ[R] Localization.Away (algebraMap R S (g * h)) :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (algebraMap R S g)) (f := toAway S (g * h))
    (fun y => by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, map_pow]
      exact (isUnit_left S g h).pow n)

noncomputable def toMulRight (g h : R) :
    Localization.Away (algebraMap R S h) →ₐ[R] Localization.Away (algebraMap R S (g * h)) :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (algebraMap R S h)) (f := toAway S (g * h))
    (fun y => by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, map_pow]
      exact (isUnit_right S g h).pow n)

/- English proof (translation)
Simplify using `only [toMulLeft, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]`. Both sides reduce to the same expression.
-/
theorem toMulLeft_apply (g h : R) (s : S) :
    toMulLeft S g h (algebraMap S _ s) = algebraMap S _ s := by
  simp only [toMulLeft, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]; rfl

/- English proof (translation)
Simplify using `only [toMulRight, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]`. Both sides reduce to the same expression.
-/
theorem toMulRight_apply (g h : R) (s : S) :
    toMulRight S g h (algebraMap S _ s) = algebraMap S _ s := by
  simp only [toMulRight, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]; rfl

/- English proof (translation)
The claim follows from `AlgHom.ext fun s => toMulLeft_apply S g h s`.
-/
theorem toMulLeft_comp (g h : R) : (toMulLeft S g h).comp (toAway S g) = toAway S (g * h) :=
  AlgHom.ext fun s => toMulLeft_apply S g h s

/- English proof (translation)
The claim follows from `AlgHom.ext fun s => toMulRight_apply S g h s`.
-/
theorem toMulRight_comp (g h : R) : (toMulRight S g h).comp (toAway S h) = toAway S (g * h) :=
  AlgHom.ext fun s => toMulRight_apply S g h s

end

end GlobalTheory.SquareZeroLift

namespace GlobalTheory.SquareZeroLift
open RingTheory.Sequence

/- English proof (translation)
Introduce `R _ _ A _ _ hA S T _ _ _ _ hS hT π hπ hI φ`. Take `⟨rs, hlen, hmem, hreg⟩` from `hS`. Take `⟨x, y, rfl⟩ : ∃ x y, rs = [x, y]` from `by match rs, hlen with`. Consider the case `[x, y], _ => exact ⟨x, y, rfl⟩`. Establish `hxm : x ∈ maximalIdeal R` using `hmem x (by simp)`.

Establish `hym : y ∈ maximalIdeal R` using `hmem y (by simp)`. Establish `hw` using `hreg.toIsWeaklyRegular`. Establish `hx : IsSMulRegular S x` using `((isWeaklyRegular_cons_iff S x [y]).1 hw).1`. Take `⟨rs', hlen', hmem', hreg'⟩` from `hT`. Take `⟨z, rfl⟩ : ∃ z, rs' = [z]` from `by match rs', hlen' with`.

Consider the case `[z], _ => exact ⟨z, rfl⟩`. Establish `hzm : z ∈ maximalIdeal R` using `hmem' z (by simp)`. Establish `hz : IsSMulRegular T z` using `((isWeaklyRegular_cons_iff T z []).1 hreg'.toIsWeaklyRegular).1`. Establish `EU` using `fun (g : R) (hg : g ∈ maximalIdeal R) => existsUnique_lifts π φ hπ hI g (hA g hg) (toAway S g) (isUnit_toAway S g)`. Take `⟨αx, hαx, -⟩` from `EU x hxm`.

Take `⟨αy, hαy, -⟩` from `EU y hym`. Take `⟨αz, hαz, -⟩` from `EU z hzm`. Establish `hxy : (toMulLeft S x y).comp αx = (toMulRight S x y).comp αy`. Take `⟨β, -, hβ⟩` from `EU (x * y) (Ideal.mul_mem_right _ _ hxm)`. Establish `h1` using `Lifts.comp π φ hαx (toMulLeft S x y)`.

Establish `h2` using `Lifts.comp π φ hαy (toMulRight S x y)`. Rewrite `h1` using `[toMulLeft_comp]`. Rewrite `h2` using `[toMulRight_comp]`. Rewrite using `[hβ _ h1, hβ _ h2]`. Establish `hzx : (toMulLeft S z x).comp αz = (toMulRight S z x).comp αx`.

Take `⟨β, -, hβ⟩` from `EU (z * x) (Ideal.mul_mem_right _ _ hzm)`. Establish `h1` using `Lifts.comp π φ hαz (toMulLeft S z x)`. Establish `h2` using `Lifts.comp π φ hαx (toMulRight S z x)`. Rewrite `h1` using `[toMulLeft_comp]`. Rewrite `h2` using `[toMulRight_comp]`.

Rewrite using `[hβ _ h1, hβ _ h2]`. Establish `glue : ∀ a, ∃ v : S, αx a = toAway S x v`. Introduce `a`. Take `⟨⟨s, m⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers (algebraMap R S x)) (αx a)`. Take `⟨⟨s', m'⟩, hs'⟩` from `IsLocalization.surj (Submonoid.powers (algebraMap R S y)) (αy a)`.

Take `⟨n, hn⟩` from `m.2`. Take `⟨k, hk⟩` from `m'.2`. Establish `hP : toMulLeft S x y (αx a) = toMulRight S x y (αy a)`. Use `congrArg (fun f => f a) hxy` as an intermediate fact. Simplify `this` using `only [AlgHom.comp_apply]`.

Establish `e1` using `congrArg (toMulLeft S x y) hs`. Establish `e2` using `congrArg (toMulRight S x y) hs'`. Rewrite `e1` using `[map_mul (toMulLeft S x y), toMulLeft_apply, toMulLeft_apply]`. Rewrite `e2` using `[map_mul (toMulRight S x y), toMulRight_apply, toMulRight_apply]`. Establish `e3 : algebraMap S (Localization.Away (algebraMap R S (x * y))) (s * m') = algebraMap S _ (s' * m)`.

Rewrite using `[map_mul (algebraMap S (Localization.Away (algebraMap R S (x * y)))), map_mul (algebraMap S (Localization.Away (algebraMap R S (x * y)))), ← e1, ← e2, hP]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨c, hc⟩` from `(IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R S (x * y))) _).1 e3`. Take `⟨j, hj⟩` from `c.2`. Simplify using `only at hn hk hj`.

Rewrite `hc` using `[← hj, ← hn, ← hk]`. Apply the tactic sequence `try rw [map_mul (algebraMap R S)] at hc`. Rewrite `hc` using `[mul_pow]`. Establish `hc2 : (algebraMap R S y) ^ (j + k) * s = (algebraMap R S x) ^ n * ((algebraMap R S y) ^ j * s')`. Apply `hx.pow j` to reduce the goal to its premises.

Simplify using `only [Algebra.smul_def, map_pow]`. Take the linear combination `hc`. Take `⟨v, hv⟩` from `pow_dvd_of_weaklyRegular x y hw n (j + k) s ((algebraMap R S y) ^ j * s') (by simpa only [Algebra.smul_def, map_pow] using hc2)`. Use `⟨v, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (algebraMap S (Localization.Away (algebraMap R S x)) ((algebraMap R S x) ^ n))`.

Rewrite using `[map_pow]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit (algebraMap R S x)).pow n`. Rewrite using `[toAway_apply]`. Apply `hu.mul_right_cancel` to reduce the goal to its premises. Simplify using `only at hs`.

Rewrite `hs` using `[← hn]`. Rewrite using `[hs, hv, Algebra.smul_def, map_mul, map_pow, mul_comm]`. Establish `hinj : Function.Injective (toAway S x)` using `by show Function.Injective (algebraMap S (Localization.Away (algebraMap R S x)))`. Apply `IsLocalization.injective (M := Submonoid.powers (algebraMap R S x))` to reduce the goal to its premises. Introduce `c hc`.

Take `⟨n, rfl⟩` from `hc`. Rewrite using `[mem_nonZeroDivisors_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `t ht`. Apply `hx.pow n` to reduce the goal to its premises.

Simplify using `only [Algebra.smul_def, map_pow, smul_zero]`. Simplify `ht` using `[mul_comm]`. Introduce `t ht`. Apply `hx.pow n` to reduce the goal to its premises. Simplify using `only [Algebra.smul_def, map_pow, smul_zero]`.

Simplify `ht` using `[mul_comm]`. Set `ψ : A →ₐ[R] S` to `((AlgEquiv.ofInjective (toAway S x) hinj).symm : _ →ₐ[R] S).comp (αx.codRestrict (toAway S x).range (fun a => by`. Take `⟨v, hv⟩` from `glue a`. Conclude with `⟨v, hv.symm⟩))`. Establish `hψ : ∀ a, toAway S x (ψ a) = αx a`.

Introduce `a`. Establish `h` using `congrArg Subtype.val ((AlgEquiv.ofInjective (toAway S x) hinj).apply_symm_apply ⟨αx a, by obtain ⟨v, hv⟩ := glue a; exact ⟨v, hv.symm⟩⟩)`. Rewrite `h` using `[AlgEquiv.ofInjective_apply]`. Conclude with `h`. Establish `hαzψ : ∀ a, αz a = toAway S z (ψ a)`.

Introduce `a`. Establish `h1 : toMulLeft S z x (αz a) = toMulLeft S z x (toAway S z (ψ a))`. Use `congrArg (fun f => f a) hzx` as an intermediate fact. Simplify using `only [AlgHom.comp_apply] at this`. Rewrite using `[this, ← hψ a, toAway_apply, toAway_apply, toMulRight_apply, toMulLeft_apply]`.

Rewrite using `[← sub_eq_zero]`. Use `set w := αz a - toAway S z (ψ a) with hwdef`. Establish `hw0 : toMulLeft S z x w = 0` using `by rw [hwdef, map_sub, h1, sub_self]`. Take `⟨⟨s0, m0⟩, hs0⟩` from `IsLocalization.surj (Submonoid.powers (algebraMap R S z)) w`. Simplify using `only at hs0`.

Establish `e0 : algebraMap S (Localization.Away (algebraMap R S (z * x))) s0 = algebraMap S _ 0`. Rewrite using `[map_zero, ← toMulLeft_apply, ← hs0, map_mul (toMulLeft S z x), hw0, zero_mul]`. Take `⟨c, hc⟩` from `(IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R S (z * x))) _).1 e0`. Take `⟨j, hj⟩` from `c.2`. Simplify using `only at hj`.

Rewrite `hc` using `[← hj, mul_zero]`. Apply the tactic sequence `try rw [map_mul (algebraMap R S)] at hc`. Rewrite `hc` using `[mul_pow]`. Establish `hzs : (algebraMap R S z) ^ j * s0 = 0`. Apply `hx.pow j` to reduce the goal to its premises.

Simplify using `only [Algebra.smul_def, map_pow, mul_zero]`. Take the linear combination `hc`. Establish `hu : IsUnit (algebraMap S (Localization.Away (algebraMap R S z)) ((algebraMap R S z) ^ j))`. Rewrite using `[map_pow]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit (algebraMap R S z)).pow j`.

Establish `hs00 : algebraMap S (Localization.Away (algebraMap R S z)) s0 = 0`. Apply `hu.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[← map_mul, hzs, map_zero, mul_zero]`. Take `⟨n, hn⟩` from `m0.2`. Simplify using `only at hn`.

Establish `hu' : IsUnit (algebraMap S (Localization.Away (algebraMap R S z)) (m0 : S))`. Rewrite using `[← hn, map_pow]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit (algebraMap R S z)).pow n`. Apply `hu'.mul_right_cancel` to reduce the goal to its premises. Rewrite using `[hs0, hs00, zero_mul]`.

Use `⟨ψ, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Take `⟨s, hs⟩` from `hπ (φ a)`. Establish `h` using `hαz a s hs`. Rewrite `h` using `[hαzψ a, ← map_sub]`.

Express the relevant statement in the definitionally equal form `algebraMap S (Localization.Away (algebraMap R S z)) (ψ a - s) ∈ Ideal.map (algebraMap S (Localization.Away (algebraMap R S z))) (RingHom.ker π) at h`. Rewrite `h` using `[IsLocalization.mem_map_algebraMap_iff (Submonoid.powers (algebraMap R S z))]`. Take `⟨⟨i, m⟩, hm⟩` from `h`. Simplify using `only at hm`. Rewrite `hm` using `[← map_mul]`.

Take `⟨c, hc⟩` from `(IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R S z)) _).1 hm`. Establish `hker : π ((c : S) * ((ψ a - s) * m)) = 0`. Rewrite using `[hc, map_mul, RingHom.mem_ker.1 i.2, mul_zero]`. Take `⟨j, hj⟩` from `c.2`. Take `⟨k, hk⟩` from `m.2`.

Simplify using `only at hj hk`. Rewrite `hker` using `[← hj, ← hk, map_mul, map_mul, map_pow, map_pow, AlgHom.commutes, map_sub, hs]`. Establish `: π (ψ a) - φ a = 0`. Apply `hz.pow (j + k)` to reduce the goal to its premises. Simplify using `only [Algebra.smul_def, map_pow, smul_zero]`.

Take the linear combination `hker`. Rewrite using `[AlgHom.comp_apply]`. Conclude with `sub_eq_zero.1 this`.
-/
theorem squareZeroLift : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A],
    (∀ g ∈ maximalIdeal R, Algebra.FormallyEtale (Localization.Away g)
      (TensorProduct R (Localization.Away g) A)) →
    ∀ (S T : Type) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T],
    ReciprocityTheory.CA.ModDepthGE R S 2 → ReciprocityTheory.CA.ModDepthGE R T 1 →
    ∀ (π : S →ₐ[R] T), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (φ : A →ₐ[R] T), ∃ ψ : A →ₐ[R] S, π.comp ψ = φ := by
  intro R _ _ A _ _ hA S T _ _ _ _ hS hT π hπ hI φ
  obtain ⟨rs, hlen, hmem, hreg⟩ := hS
  obtain ⟨x, y, rfl⟩ : ∃ x y, rs = [x, y] := by
    match rs, hlen with
    | [x, y], _ => exact ⟨x, y, rfl⟩
  have hxm : x ∈ maximalIdeal R := hmem x (by simp)
  have hym : y ∈ maximalIdeal R := hmem y (by simp)
  have hw := hreg.toIsWeaklyRegular
  have hx : IsSMulRegular S x := ((isWeaklyRegular_cons_iff S x [y]).1 hw).1
  obtain ⟨rs', hlen', hmem', hreg'⟩ := hT
  obtain ⟨z, rfl⟩ : ∃ z, rs' = [z] := by
    match rs', hlen' with
    | [z], _ => exact ⟨z, rfl⟩
  have hzm : z ∈ maximalIdeal R := hmem' z (by simp)
  have hz : IsSMulRegular T z := ((isWeaklyRegular_cons_iff T z []).1 hreg'.toIsWeaklyRegular).1
  have EU := fun (g : R) (hg : g ∈ maximalIdeal R) =>
    existsUnique_lifts π φ hπ hI g (hA g hg) (toAway S g) (isUnit_toAway S g)
  obtain ⟨αx, hαx, -⟩ := EU x hxm
  obtain ⟨αy, hαy, -⟩ := EU y hym
  obtain ⟨αz, hαz, -⟩ := EU z hzm

  have hxy : (toMulLeft S x y).comp αx = (toMulRight S x y).comp αy := by
    obtain ⟨β, -, hβ⟩ := EU (x * y) (Ideal.mul_mem_right _ _ hxm)
    have h1 := Lifts.comp π φ hαx (toMulLeft S x y)
    have h2 := Lifts.comp π φ hαy (toMulRight S x y)
    rw [toMulLeft_comp] at h1
    rw [toMulRight_comp] at h2
    rw [hβ _ h1, hβ _ h2]
  have hzx : (toMulLeft S z x).comp αz = (toMulRight S z x).comp αx := by
    obtain ⟨β, -, hβ⟩ := EU (z * x) (Ideal.mul_mem_right _ _ hzm)
    have h1 := Lifts.comp π φ hαz (toMulLeft S z x)
    have h2 := Lifts.comp π φ hαx (toMulRight S z x)
    rw [toMulLeft_comp] at h1
    rw [toMulRight_comp] at h2
    rw [hβ _ h1, hβ _ h2]

  have glue : ∀ a, ∃ v : S, αx a = toAway S x v := by
    intro a
    obtain ⟨⟨s, m⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R S x)) (αx a)
    obtain ⟨⟨s', m'⟩, hs'⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R S y)) (αy a)
    obtain ⟨n, hn⟩ := m.2
    obtain ⟨k, hk⟩ := m'.2
    have hP : toMulLeft S x y (αx a) = toMulRight S x y (αy a) := by
      have := congrArg (fun f => f a) hxy
      simpa only [AlgHom.comp_apply] using this
    have e1 := congrArg (toMulLeft S x y) hs
    have e2 := congrArg (toMulRight S x y) hs'
    rw [map_mul (toMulLeft S x y), toMulLeft_apply, toMulLeft_apply] at e1
    rw [map_mul (toMulRight S x y), toMulRight_apply, toMulRight_apply] at e2
    have e3 : algebraMap S (Localization.Away (algebraMap R S (x * y))) (s * m') =
        algebraMap S _ (s' * m) := by
      rw [map_mul (algebraMap S (Localization.Away (algebraMap R S (x * y)))),
        map_mul (algebraMap S (Localization.Away (algebraMap R S (x * y)))), ← e1, ← e2, hP]; ring
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
      (Submonoid.powers (algebraMap R S (x * y))) _).1 e3
    obtain ⟨j, hj⟩ := c.2
    simp only at hn hk hj
    rw [← hj, ← hn, ← hk] at hc
    try rw [map_mul (algebraMap R S)] at hc
    rw [mul_pow] at hc
    have hc2 : (algebraMap R S y) ^ (j + k) * s =
        (algebraMap R S x) ^ n * ((algebraMap R S y) ^ j * s') := by
      apply hx.pow j
      simp only [Algebra.smul_def, map_pow]
      linear_combination hc
    obtain ⟨v, hv⟩ := pow_dvd_of_weaklyRegular x y hw n (j + k) s ((algebraMap R S y) ^ j * s')
      (by simpa only [Algebra.smul_def, map_pow] using hc2)
    refine ⟨v, ?_⟩
    have hu : IsUnit (algebraMap S (Localization.Away (algebraMap R S x)) ((algebraMap R S x) ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (algebraMap R S x)).pow n
    rw [toAway_apply]
    apply hu.mul_right_cancel
    simp only at hs
    rw [← hn] at hs
    rw [hs, hv, Algebra.smul_def, map_mul, map_pow, mul_comm]

  have hinj : Function.Injective (toAway S x) := by
    show Function.Injective (algebraMap S (Localization.Away (algebraMap R S x)))
    apply IsLocalization.injective (M := Submonoid.powers (algebraMap R S x))
    intro c hc
    obtain ⟨n, rfl⟩ := hc
    rw [mem_nonZeroDivisors_iff]
    constructor
    · intro t ht
      apply hx.pow n
      simp only [Algebra.smul_def, map_pow, smul_zero]
      simpa [mul_comm] using ht
    · intro t ht
      apply hx.pow n
      simp only [Algebra.smul_def, map_pow, smul_zero]
      simpa [mul_comm] using ht
  let ψ : A →ₐ[R] S := ((AlgEquiv.ofInjective (toAway S x) hinj).symm : _ →ₐ[R] S).comp
    (αx.codRestrict (toAway S x).range (fun a => by
      obtain ⟨v, hv⟩ := glue a
      exact ⟨v, hv.symm⟩))
  have hψ : ∀ a, toAway S x (ψ a) = αx a := by
    intro a
    have h := congrArg Subtype.val ((AlgEquiv.ofInjective (toAway S x) hinj).apply_symm_apply
      ⟨αx a, by obtain ⟨v, hv⟩ := glue a; exact ⟨v, hv.symm⟩⟩)
    rw [AlgEquiv.ofInjective_apply] at h
    exact h

  have hαzψ : ∀ a, αz a = toAway S z (ψ a) := by
    intro a
    have h1 : toMulLeft S z x (αz a) = toMulLeft S z x (toAway S z (ψ a)) := by
      have := congrArg (fun f => f a) hzx
      simp only [AlgHom.comp_apply] at this
      rw [this, ← hψ a, toAway_apply, toAway_apply, toMulRight_apply, toMulLeft_apply]
    rw [← sub_eq_zero]
    set w := αz a - toAway S z (ψ a) with hwdef
    have hw0 : toMulLeft S z x w = 0 := by rw [hwdef, map_sub, h1, sub_self]
    obtain ⟨⟨s0, m0⟩, hs0⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R S z)) w
    simp only at hs0
    have e0 : algebraMap S (Localization.Away (algebraMap R S (z * x))) s0 =
        algebraMap S _ 0 := by
      rw [map_zero, ← toMulLeft_apply, ← hs0, map_mul (toMulLeft S z x), hw0, zero_mul]
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
      (Submonoid.powers (algebraMap R S (z * x))) _).1 e0
    obtain ⟨j, hj⟩ := c.2
    simp only at hj
    rw [← hj, mul_zero] at hc
    try rw [map_mul (algebraMap R S)] at hc
    rw [mul_pow] at hc
    have hzs : (algebraMap R S z) ^ j * s0 = 0 := by
      apply hx.pow j
      simp only [Algebra.smul_def, map_pow, mul_zero]
      linear_combination hc
    have hu : IsUnit (algebraMap S (Localization.Away (algebraMap R S z)) ((algebraMap R S z) ^ j)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (algebraMap R S z)).pow j
    have hs00 : algebraMap S (Localization.Away (algebraMap R S z)) s0 = 0 := by
      apply hu.mul_left_cancel
      rw [← map_mul, hzs, map_zero, mul_zero]
    obtain ⟨n, hn⟩ := m0.2
    simp only at hn
    have hu' : IsUnit (algebraMap S (Localization.Away (algebraMap R S z)) (m0 : S)) := by
      rw [← hn, map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (algebraMap R S z)).pow n
    apply hu'.mul_right_cancel
    rw [hs0, hs00, zero_mul]

  refine ⟨ψ, ?_⟩
  ext a
  obtain ⟨s, hs⟩ := hπ (φ a)
  have h := hαz a s hs
  rw [hαzψ a, ← map_sub] at h
  change algebraMap S (Localization.Away (algebraMap R S z)) (ψ a - s) ∈
    Ideal.map (algebraMap S (Localization.Away (algebraMap R S z))) (RingHom.ker π) at h
  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers (algebraMap R S z))] at h
  obtain ⟨⟨i, m⟩, hm⟩ := h
  simp only at hm
  rw [← map_mul] at hm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R S z)) _).1 hm
  have hker : π ((c : S) * ((ψ a - s) * m)) = 0 := by
    rw [hc, map_mul, RingHom.mem_ker.1 i.2, mul_zero]
  obtain ⟨j, hj⟩ := c.2
  obtain ⟨k, hk⟩ := m.2
  simp only at hj hk
  rw [← hj, ← hk, map_mul, map_mul, map_pow, map_pow, AlgHom.commutes, map_sub, hs] at hker
  have : π (ψ a) - φ a = 0 := by
    apply hz.pow (j + k)
    simp only [Algebra.smul_def, map_pow, smul_zero]
    linear_combination hker
  rw [AlgHom.comp_apply]
  exact sub_eq_zero.1 this

end GlobalTheory.SquareZeroLift
