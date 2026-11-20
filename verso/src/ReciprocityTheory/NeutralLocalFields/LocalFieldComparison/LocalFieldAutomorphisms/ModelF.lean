import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Inertia

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel

/- English proof (translation)
Establish `hp` using `(Fact.out : p.Prime)`. Establish `hdec : n = p ^ padicValNat p n * (n / p ^ padicValNat p n)`. Establish `h1` using `Nat.ordProj_mul_ordCompl_eq_self n p`. Rewrite `h1` using `[Nat.factorization_def n hp]`. Conclude with `h1.symm`.

Establish `hnd : ¬ p ∣ n / p ^ padicValNat p n`. Establish `h1` using `Nat.not_dvd_ordCompl hp hn`. Rewrite `h1` using `[Nat.factorization_def n hp]`. Then use the resulting hypothesis. Establish `hu : IsUnit (((n / p ^ padicValNat p n : ℕ) : ℤ_[p]))`. Rewrite using `[PadicInt.isUnit_iff]`.

Assume the negation of the conclusion as `hne`. Establish `hlt : ‖(((n / p ^ padicValNat p n : ℕ) : ℤ_[p]))‖ < 1` using `lt_of_le_of_ne (PadicInt.norm_le_one _) hne`. Rewrite `hlt` using `[PadicInt.norm_lt_one_iff_dvd]`. Take `⟨c, hc⟩` from `hlt`. Establish `h1` using `congrArg PadicInt.toZMod hc`.

Rewrite `h1` using `[map_natCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul, ZMod.natCast_eq_zero_iff]`. Conclude with `hnd h1`. Establish `hspan : Ideal.span {(n : ℤ_[p])} = Ideal.span {(p : ℤ_[p]) ^ padicValNat p n}` using `by conv_lhs => rw [hdec]`. Use `push_cast`. Conclude with `Ideal.span_singleton_mul_right_unit hu _`.

Rewrite using `[hspan, ← PadicInt.ker_toZModPow]`. Rewrite using `[Nat.card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) (padicValNat p n)))).toEquiv, Nat.card_zmod]`.
-/
theorem card_quot_natCast_padicInt (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (ℤ_[p] ⧸ Ideal.span {(n : ℤ_[p])}) = p ^ padicValNat p n := by
  have hp := (Fact.out : p.Prime)
  have hdec : n = p ^ padicValNat p n * (n / p ^ padicValNat p n) := by
    have h1 := Nat.ordProj_mul_ordCompl_eq_self n p
    rw [Nat.factorization_def n hp] at h1
    exact h1.symm
  have hnd : ¬ p ∣ n / p ^ padicValNat p n := by
    have h1 := Nat.not_dvd_ordCompl hp hn
    rwa [Nat.factorization_def n hp] at h1
  have hu : IsUnit (((n / p ^ padicValNat p n : ℕ) : ℤ_[p])) := by
    rw [PadicInt.isUnit_iff]
    by_contra hne
    have hlt : ‖(((n / p ^ padicValNat p n : ℕ) : ℤ_[p]))‖ < 1 :=
      lt_of_le_of_ne (PadicInt.norm_le_one _) hne
    rw [PadicInt.norm_lt_one_iff_dvd] at hlt
    obtain ⟨c, hc⟩ := hlt
    have h1 := congrArg PadicInt.toZMod hc
    rw [map_natCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul,
      ZMod.natCast_eq_zero_iff] at h1
    exact hnd h1
  have hspan : Ideal.span {(n : ℤ_[p])} = Ideal.span {(p : ℤ_[p]) ^ padicValNat p n} := by
    conv_lhs => rw [hdec]
    push_cast
    exact Ideal.span_singleton_mul_right_unit hu _
  rw [hspan, ← PadicInt.ker_toZModPow]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) (padicValNat p n)))).toEquiv, Nat.card_zmod]

/- English proof (translation)
Set `φ : C →ₗ[R] (ι → R ⧸ Ideal.span {r})` to `LinearMap.pi fun i => (Ideal.span {r}).mkQ ∘ₗ b.coord i`. Establish `hφ : Function.Surjective φ`. Introduce `y`. Use `choose c hc using fun i => Ideal.Quotient.mk_surjective (y i)`. Use `⟨b.equivFun.symm c, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Establish `h1 : b.repr (b.equivFun.symm c) i = c i`. Rewrite using `[← b.equivFun_apply, LinearEquiv.apply_symm_apply]`. Simplify using `only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Module.Basis.coord_apply, Submodule.mkQ_apply, h1]`. Conclude with `hc i`.

Establish `hker : LinearMap.ker φ = (Ideal.span {algebraMap R C r}).restrictScalars R`. Use extensionality with `x`. Simplify using `only [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Establish `: ∀ i, ∃ a, a * r = b.repr x i` using `fun i => by`. Rewrite using `[← Ideal.mem_span_singleton', ← Ideal.Quotient.eq_zero_iff_mem]`. Simplify `congrFun hx i` using `[φ]`. Use `choose a ha using this`. Use `⟨b.equivFun.symm a, ?_⟩` and prove the remaining obligations.

Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Rewrite using `[mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, ← b.equivFun_apply, LinearEquiv.apply_symm_apply, ← ha, smul_eq_mul, mul_comm]`. Introduce and unpack `⟨a, rfl⟩`. Use function extensionality and compare the values at `i`.

Rewrite using `[mul_comm, ← Algebra.smul_def]`. Simplify using `only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Module.Basis.coord_apply, map_smul, Submodule.mkQ_apply, Pi.zero_apply]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 (dvd_mul_right _ _))`. Establish `e` using `((Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {algebraMap R C r})).symm.trans (Submodule.quotEquivOfEq _ _ hker.symm)).trans (φ.quotKerEquivOfSurjective hφ)`. Rewrite using `[Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]`.
-/
theorem card_quot_span_algebraMap {R C ι : Type*} [CommRing R] [CommRing C] [Algebra R C] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι R C) (r : R) :
    Nat.card (C ⧸ Ideal.span {algebraMap R C r}) = Nat.card (R ⧸ Ideal.span {r}) ^ Fintype.card ι := by
  let φ : C →ₗ[R] (ι → R ⧸ Ideal.span {r}) :=
    LinearMap.pi fun i => (Ideal.span {r}).mkQ ∘ₗ b.coord i
  have hφ : Function.Surjective φ := by
    intro y
    choose c hc using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨b.equivFun.symm c, ?_⟩
    funext i
    have h1 : b.repr (b.equivFun.symm c) i = c i := by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Module.Basis.coord_apply, Submodule.mkQ_apply, h1]
    exact hc i
  have hker : LinearMap.ker φ = (Ideal.span {algebraMap R C r}).restrictScalars R := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    constructor
    · intro hx
      have : ∀ i, ∃ a, a * r = b.repr x i := fun i => by
        rw [← Ideal.mem_span_singleton', ← Ideal.Quotient.eq_zero_iff_mem]
        simpa [φ] using congrFun hx i
      choose a ha using this
      refine ⟨b.equivFun.symm a, ?_⟩
      apply b.repr.injective
      ext i
      rw [mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, ← b.equivFun_apply,
        LinearEquiv.apply_symm_apply, ← ha, smul_eq_mul, mul_comm]
    · rintro ⟨a, rfl⟩
      funext i
      rw [mul_comm, ← Algebra.smul_def]
      simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Module.Basis.coord_apply, map_smul,
        Submodule.mkQ_apply, Pi.zero_apply]
      exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 (dvd_mul_right _ _))
  have e := ((Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {algebraMap R C r})).symm.trans
    (Submodule.quotEquivOfEq _ _ hker.symm)).trans (φ.quotKerEquivOfSurjective hφ)
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

attribute [local instance] locRel

/- English proof (translation)
Use `show ‖algebraMap ℚ_[p] (PadicAlgCl p) (x : ℚ_[p])‖ ≤ 1`. Conclude with `(PadicAlgCl.norm_extends p (x : ℚ_[p])).le.trans x.2`.
-/
theorem norm_algebraMap_padicInt_Kloc (ι : Ω →+* PadicAlgCl p) (x : ℤ_[p]) :
    ‖((algebraMap ℤ_[p] (Kloc F ι) x : Kloc F ι) : PadicAlgCl p)‖ ≤ 1 := by
  show ‖algebraMap ℚ_[p] (PadicAlgCl p) (x : ℚ_[p])‖ ≤ 1
  exact (PadicAlgCl.norm_extends p (x : ℚ_[p])).le.trans x.2

def zpToInteger (ι : Ω →+* PadicAlgCl p) : ℤ_[p] →+* 𝒪[Kloc F ι] :=
  (algebraMap ℤ_[p] (Kloc F ι)).codRestrict _
    fun x => (mem_integer_Kloc ι _).2 (norm_algebraMap_padicInt_Kloc ι x)

@[instance_reducible]
def zpAlgInteger (ι : Ω →+* PadicAlgCl p) : Algebra ℤ_[p] 𝒪[Kloc F ι] := (zpToInteger (F := F) ι).toAlgebra

attribute [local instance] zpAlgInteger

/- English proof (translation)
The claim follows from `IsScalarTower.of_algebraMap_eq fun _ => rfl`.
-/
theorem isScalarTower_zp_integer (ι : Ω →+* PadicAlgCl p) : IsScalarTower ℤ_[p] 𝒪[Kloc F ι] (Kloc F ι) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/- English proof (translation)
The claim follows from `IsScalarTower.of_algebraMap_eq fun _ => rfl`.
-/
theorem isScalarTower_zp_Kloc_alg (ι : Ω →+* PadicAlgCl p) : IsScalarTower ℤ_[p] (Kloc F ι) (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/- English proof (translation)
Use `Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_` and prove the remaining obligations. Rewrite `h` using `[Algebra.smul_def, mul_eq_zero]`. Use `h.imp (fun h => ?_) id` and prove the remaining obligations. Rewrite `h` using `[IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (Kloc F ι), map_eq_zero]`. Conclude with `PadicInt.ext (by simpa using h)`.
-/
theorem isTorsionFree_zp_Kloc (ι : Ω →+* PadicAlgCl p) : Module.IsTorsionFree ℤ_[p] (Kloc F ι) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
  rw [Algebra.smul_def, mul_eq_zero] at h
  refine h.imp (fun h => ?_) id
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (Kloc F ι), map_eq_zero] at h
  exact PadicInt.ext (by simpa using h)

/- English proof (translation)
Use `isScalarTower_zp_Kloc_alg (F := F) ι` as an intermediate fact. Rewrite using `[← isIntegral_algebraMap_iff (A := Kloc F ι) (B := PadicAlgCl p) (algebraMap (Kloc F ι) (PadicAlgCl p)).injective]`. Conclude with `Iff.rfl`.
-/
theorem isIntegral_zp_Kloc_iff (ι : Ω →+* PadicAlgCl p) (x : Kloc F ι) :
    IsIntegral ℤ_[p] x ↔ IsIntegral (PadicInt.subring p) (x : PadicAlgCl p) := by
  have := isScalarTower_zp_Kloc_alg (F := F) ι
  rw [← isIntegral_algebraMap_iff (A := Kloc F ι) (B := PadicAlgCl p) (algebraMap (Kloc F ι) (PadicAlgCl p)).injective]
  exact Iff.rfl

/- English proof (translation)
The claim follows from `Subtype.val_injective isIntegral_iff {x} := by rw [isIntegral_zp_Kloc_iff, ← norm_le_one_iff_isIntegral, ← mem_integer_Kloc] exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩`.
-/
theorem isIntegralClosure_Kloc (ι : Ω →+* PadicAlgCl p) :
    IsIntegralClosure 𝒪[Kloc F ι] ℤ_[p] (Kloc F ι) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    rw [isIntegral_zp_Kloc_iff, ← norm_le_one_iff_isIntegral, ← mem_integer_Kloc]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩

/- English proof (translation)
Use `finiteDimensional_Kloc (F := F) ι` as an intermediate fact. Use `isScalarTower_zp_integer (F := F) ι` as an intermediate fact. Use `isIntegralClosure_Kloc (F := F) ι` as an intermediate fact. Use `isTorsionFree_zp_Kloc (F := F) ι` as an intermediate fact. Establish `: Module.Free ℤ_[p] 𝒪[Kloc F ι]` using `IsIntegralClosure.module_free ℤ_[p] ℚ_[p] (Kloc F ι) _`.

Establish `: Module.Finite ℤ_[p] 𝒪[Kloc F ι]` using `IsIntegralClosure.finite ℤ_[p] ℚ_[p] (Kloc F ι) _`. Establish `hr` using `IsIntegralClosure.rank ℤ_[p] ℚ_[p] (Kloc F ι) 𝒪[Kloc F ι]`. Establish `hn' : (n : 𝒪[Kloc F ι]) = algebraMap ℤ_[p] 𝒪[Kloc F ι] n` using `(map_natCast _ _).symm`. Rewrite using `[hn', card_quot_span_algebraMap (Module.finBasis ℤ_[p] 𝒪[Kloc F ι]), card_quot_natCast_padicInt p hn, Fintype.card_fin, hr, pow_mul]`.
-/
theorem card_quot_natCast_Kloc (ι : Ω →+* PadicAlgCl p) {n : ℕ} (hn : n ≠ 0) :
    Nat.card (𝒪[Kloc F ι] ⧸ Ideal.span {(n : 𝒪[Kloc F ι])}) =
      p ^ (padicValNat p n * Module.finrank ℚ_[p] (Kloc F ι)) := by
  have := finiteDimensional_Kloc (F := F) ι
  have := isScalarTower_zp_integer (F := F) ι
  have := isIntegralClosure_Kloc (F := F) ι
  have := isTorsionFree_zp_Kloc (F := F) ι
  have : Module.Free ℤ_[p] 𝒪[Kloc F ι] := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] (Kloc F ι) _
  have : Module.Finite ℤ_[p] 𝒪[Kloc F ι] := IsIntegralClosure.finite ℤ_[p] ℚ_[p] (Kloc F ι) _
  have hr := IsIntegralClosure.rank ℤ_[p] ℚ_[p] (Kloc F ι) 𝒪[Kloc F ι]
  have hn' : (n : 𝒪[Kloc F ι]) = algebraMap ℤ_[p] 𝒪[Kloc F ι] n := (map_natCast _ _).symm
  rw [hn', card_quot_span_algebraMap (Module.finBasis ℤ_[p] 𝒪[Kloc F ι]), card_quot_natCast_padicInt p hn,
    Fintype.card_fin, hr, pow_mul]

end ReciprocityTheory.Neutral.Cmp
