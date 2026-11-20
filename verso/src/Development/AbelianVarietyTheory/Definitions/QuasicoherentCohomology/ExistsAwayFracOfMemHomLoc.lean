import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexAcyclicIffQuasiIsoCechAug
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexExactAtOfIsLocalizedModuleRes
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsGradedMapLinearCombination

open DirectSum MvPolynomial CategoryTheory

universe u

noncomputable section

namespace GlobalTheory

open GradedHilbert

section Away

variable {A : Type*} [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
  {N : Type*} [AddCommGroup N] [Module A N] {P : Type*} [AddCommGroup P] [Module A P]

def awayFrac (f : A) (k : ℕ) : M →ₗ[A] LocalizedModule.Away f M :=
  LocalizedModule.divBy (⟨f ^ k, k, rfl⟩ : Submonoid.powers f) ∘ₗ
    LocalizedModule.mkLinearMap (Submonoid.powers f) M

variable {M}

/- English proof (translation)
Simplify using `[awayFrac, LocalizedModule.liftOn_mk]`.
-/
theorem awayFrac_apply (f : A) (k : ℕ) (m : M) :
    awayFrac M f k m = LocalizedModule.mk m (⟨f ^ k, k, rfl⟩ : Submonoid.powers f) := by
  simp [awayFrac, LocalizedModule.liftOn_mk]

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[awayFrac_apply, LocalizedModule.mkLinearMap_apply]`. Use `congr 1`. Conclude with `Subtype.ext (pow_zero f)`.
-/
theorem awayFrac_zero (f : A) :
    awayFrac M f 0 = LocalizedModule.mkLinearMap (Submonoid.powers f) M := by
  ext m
  rw [awayFrac_apply, LocalizedModule.mkLinearMap_apply]
  congr 1
  exact Subtype.ext (pow_zero f)

/- English proof (translation)
Proceed by induction on `z using LocalizedModule.induction_on with | _ m s`. Take `⟨_, k, rfl⟩` from `s`. Conclude with `⟨k, m, awayFrac_apply f k m⟩`.
-/
theorem exists_awayFrac {f : A} (z : LocalizedModule.Away f M) :
    ∃ k m, awayFrac M f k m = z := by
  induction z using LocalizedModule.induction_on with | _ m s
  obtain ⟨_, k, rfl⟩ := s
  exact ⟨k, m, awayFrac_apply f k m⟩

/- English proof (translation)
Rewrite using `[awayFrac_apply, awayFrac_apply, LocalizedModule.mk_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨_, l, rfl⟩, h⟩`. Conclude with `⟨l, by simpa [pow_add, mul_smul, Submonoid.smul_def] using h⟩`. Introduce and unpack `⟨l, h⟩`.

Conclude with `⟨⟨_, l, rfl⟩, by simpa [pow_add, mul_smul, Submonoid.smul_def] using h⟩`.
-/
theorem awayFrac_eq_iff {f : A} {k j : ℕ} {m m' : M} :
    awayFrac M f k m = awayFrac M f j m' ↔ ∃ l : ℕ, f ^ (l + j) • m = f ^ (l + k) • m' := by
  rw [awayFrac_apply, awayFrac_apply, LocalizedModule.mk_eq]
  constructor
  · rintro ⟨⟨_, l, rfl⟩, h⟩
    exact ⟨l, by simpa [pow_add, mul_smul, Submonoid.smul_def] using h⟩
  · rintro ⟨l, h⟩
    exact ⟨⟨_, l, rfl⟩, by simpa [pow_add, mul_smul, Submonoid.smul_def] using h⟩

/- English proof (translation)
Rewrite using `[← map_zero (awayFrac M f 0), awayFrac_eq_iff]`. Simplify using the standard rewrite rules.
-/
theorem awayFrac_eq_zero_iff {f : A} {k : ℕ} {m : M} :
    awayFrac M f k m = 0 ↔ ∃ l : ℕ, f ^ l • m = 0 := by
  rw [← map_zero (awayFrac M f 0), awayFrac_eq_iff]
  simp

/- English proof (translation)
The claim follows from `awayFrac_eq_iff.2 ⟨0, by simp [pow_add, mul_smul]⟩`.
-/
theorem awayFrac_add_pow_smul (f : A) (k j : ℕ) (m : M) :
    awayFrac M f (k + j) (f ^ j • m) = awayFrac M f k m :=
  awayFrac_eq_iff.2 ⟨0, by simp [pow_add, mul_smul]⟩

/- English proof (translation)
Rewrite using `[← map_smul, ← awayFrac_add_pow_smul f 0 k, zero_add]`.
-/
theorem pow_smul_awayFrac (f : A) (k : ℕ) (m : M) :
    f ^ k • awayFrac M f k m = awayFrac M f 0 m := by
  rw [← map_smul, ← awayFrac_add_pow_smul f 0 k, zero_add]

/- English proof (translation)
The claim follows from `isUnit_algebraMap_end_of_dvd h (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers g) M) (⟨g ^ k, k, rfl⟩ : Submonoid.powers g))`.
-/
theorem isUnit_away_of_dvd_pow {f g : A} {k : ℕ} (h : f ∣ g ^ k) :
    IsUnit (algebraMap A (Module.End A (LocalizedModule.Away g M)) f) :=
  isUnit_algebraMap_end_of_dvd h (IsLocalizedModule.map_units
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M) (⟨g ^ k, k, rfl⟩ : Submonoid.powers g))

/- English proof (translation)
The claim follows from `(Module.End.isUnit_iff _).1 (isUnit_away_of_dvd_pow h)`.
-/
theorem smul_away_bijective {f g : A} {k : ℕ} (h : f ∣ g ^ k) :
    Function.Bijective (LinearMap.lsmul A (LocalizedModule.Away g M) f) :=
  (Module.End.isUnit_iff _).1 (isUnit_away_of_dvd_pow h)

/- English proof (translation)
The claim follows from `LinearMap.ext fun z => by obtain ⟨k, m, rfl⟩ := exists_awayFrac z exact h k m`.
-/
theorem away_ext {f : A} {φ ψ : LocalizedModule.Away f M →ₗ[A] N}
    (h : ∀ k m, φ (awayFrac M f k m) = ψ (awayFrac M f k m)) : φ = ψ :=
  LinearMap.ext fun z => by
    obtain ⟨k, m, rfl⟩ := exists_awayFrac z
    exact h k m

def awayMap (f : A) (φ : M →ₗ[A] N) : LocalizedModule.Away f M →ₗ[A] LocalizedModule.Away f N :=
  IsLocalizedModule.map (Submonoid.powers f) (LocalizedModule.mkLinearMap _ M)
    (LocalizedModule.mkLinearMap _ N) φ

@[simp]
/- English proof (translation)
Rewrite using `[awayFrac_apply, awayFrac_apply]`. Conclude with `IsLocalizedModule.map_LocalizedModules _ _ _ _`. Use the proof step `@[simp]`.
-/
theorem awayMap_awayFrac (f : A) (φ : M →ₗ[A] N) (k : ℕ) (m : M) :
    awayMap f φ (awayFrac M f k m) = awayFrac N f k (φ m) := by
  rw [awayFrac_apply, awayFrac_apply]
  exact IsLocalizedModule.map_LocalizedModules _ _ _ _

@[simp]
/- English proof (translation)
The claim follows from `away_ext fun k m => by simp`.
-/
theorem awayMap_id (f : A) : awayMap f (LinearMap.id : M →ₗ[A] M) = LinearMap.id :=
  away_ext fun k m => by simp

/- English proof (translation)
The claim follows from `away_ext fun k m => by simp @[simp]`.
-/
theorem awayMap_comp (f : A) (ψ : N →ₗ[A] P) (φ : M →ₗ[A] N) :
    awayMap f (ψ ∘ₗ φ) = awayMap f ψ ∘ₗ awayMap f φ :=
  away_ext fun k m => by simp

@[simp]
/- English proof (translation)
The claim follows from `map_zero _`.
-/
theorem awayMap_zero (f : A) : awayMap f (0 : M →ₗ[A] N) = 0 := map_zero _

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`. Take `⟨k, m, rfl⟩` from `exists_awayFrac z`. Rewrite `hz` using `[awayMap_awayFrac, awayFrac_eq_zero_iff]`. Take `⟨l, hl⟩` from `hz`.

Take `⟨j, hj⟩` from `h _ ((map_smul φ _ _).trans hl)`. Conclude with `awayFrac_eq_zero_iff.2 ⟨j + l, by rw [pow_add, mul_smul, hj]⟩`.
-/
theorem awayMap_injective_of {f : A} {φ : M →ₗ[A] N}
    (h : ∀ m, φ m = 0 → ∃ k : ℕ, f ^ k • m = 0) : Function.Injective (awayMap f φ) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨k, m, rfl⟩ := exists_awayFrac z
  rw [awayMap_awayFrac, awayFrac_eq_zero_iff] at hz
  obtain ⟨l, hl⟩ := hz
  obtain ⟨j, hj⟩ := h _ ((map_smul φ _ _).trans hl)
  exact awayFrac_eq_zero_iff.2 ⟨j + l, by rw [pow_add, mul_smul, hj]⟩

/- English proof (translation)
Introduce `z`. Take `⟨k, y, rfl⟩` from `exists_awayFrac z`. Take `⟨j, m, hm⟩` from `h y`. Conclude with `⟨awayFrac M f (k + j) m, by rw [awayMap_awayFrac, hm, awayFrac_add_pow_smul]⟩`.
-/
theorem awayMap_surjective_of {f : A} {φ : M →ₗ[A] N}
    (h : ∀ y, ∃ k : ℕ, f ^ k • y ∈ LinearMap.range φ) : Function.Surjective (awayMap f φ) := by
  intro z
  obtain ⟨k, y, rfl⟩ := exists_awayFrac z
  obtain ⟨j, m, hm⟩ := h y
  exact ⟨awayFrac M f (k + j) m, by rw [awayMap_awayFrac, hm, awayFrac_add_pow_smul]⟩

/- English proof (translation)
The claim follows from `IsLocalizedModule.map_exact _ _ _ _ _ _ h`.
-/
theorem awayMap_exact (f : A) {φ : M →ₗ[A] N} {ψ : N →ₗ[A] P} (h : Function.Exact φ ψ) :
    Function.Exact (awayMap f φ) (awayMap f ψ) :=
  IsLocalizedModule.map_exact _ _ _ _ _ _ h

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `m hm`. Take `⟨l, hl⟩` from `awayFrac_eq_zero_iff.1 hm`. Conclude with `(IsSMulRegular.pow l h) (hl.trans (smul_zero _).symm)`.
-/
theorem awayFrac_injective {f : A} (h : Function.Injective fun m : M => f • m) (k : ℕ) :
    Function.Injective (awayFrac M f k) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨l, hl⟩ := awayFrac_eq_zero_iff.1 hm
  exact (IsSMulRegular.pow l h) (hl.trans (smul_zero _).symm)

/- English proof (translation)
Use `⟨awayFrac_injective h.1 0, fun z => ?_⟩` and prove the remaining obligations. Take `⟨k, m, rfl⟩` from `exists_awayFrac z`. Take `⟨y, rfl⟩` from `(h.2.iterate k) m`. Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_iterate_apply, ← awayFrac_add_pow_smul f 0 k, zero_add]`.
-/
theorem awayFrac_zero_bijective {f : A} (h : Function.Bijective fun m : M => f • m) :
    Function.Bijective (awayFrac M f 0) := by
  refine ⟨awayFrac_injective h.1 0, fun z => ?_⟩
  obtain ⟨k, m, rfl⟩ := exists_awayFrac z
  obtain ⟨y, rfl⟩ := (h.2.iterate k) m
  refine ⟨y, ?_⟩
  rw [smul_iterate_apply, ← awayFrac_add_pow_smul f 0 k, zero_add]

/- English proof (translation)
Rewrite using `[awayFrac_apply, awayFrac_apply]`. Conclude with `locRes_mk f M h m _ _ _ (by simp [hc, mul_pow])`. Use the proof step `@[simp]`.
-/
theorem locRes_awayFrac {ι : Type} (f : ι → A) {s t : Finset ι} (h : s ⊆ t) {c : A}
    (hc : ∏ i ∈ t, f i = c * ∏ i ∈ s, f i) (k : ℕ) (m : M) :
    locRes f M h (awayFrac M _ k m) = awayFrac M _ k (c ^ k • m) := by
  rw [awayFrac_apply, awayFrac_apply]
  exact locRes_mk f M h m _ _ _ (by simp [hc, mul_pow])

@[simp]
/- English proof (translation)
Rewrite using `[awayFrac_zero, awayFrac_zero]`. Conclude with `locRes_mk_one f M h m`.
-/
theorem locRes_awayFrac_zero {ι : Type} (f : ι → A) {s t : Finset ι} (h : s ⊆ t) (m : M) :
    locRes f M h (awayFrac M _ 0 m) = awayFrac M _ 0 m := by
  rw [awayFrac_zero, awayFrac_zero]
  exact locRes_mk_one f M h m

/- English proof (translation)
Take `⟨k, m, rfl⟩` from `exists_awayFrac z`. Take `⟨c, hc⟩` from `exists_eq_mul_left_of_dvd (Finset.prod_dvd_prod_of_subset s t f h)`. Rewrite using `[locRes_awayFrac f h hc, awayMap_awayFrac, awayMap_awayFrac, locRes_awayFrac f h hc, map_smul]`.
-/
theorem awayMap_locRes {ι : Type} (f : ι → A) {s t : Finset ι} (h : s ⊆ t) (φ : M →ₗ[A] N)
    (z : LocalizedModule.Away (∏ i ∈ s, f i) M) :
    awayMap _ φ (locRes f M h z) = locRes f N h (awayMap _ φ z) := by
  obtain ⟨k, m, rfl⟩ := exists_awayFrac z
  obtain ⟨c, hc⟩ := exists_eq_mul_left_of_dvd (Finset.prod_dvd_prod_of_subset s t f h)
  rw [locRes_awayFrac f h hc, awayMap_awayFrac, awayMap_awayFrac, locRes_awayFrac f h hc, map_smul]

end Away

section HomLoc

variable {ι : Type} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  [IsScalarTower R (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
  [IsScalarTower R (MvPolynomial ι R) P]

variable (R) in

abbrev xProd (s : Finset ι) : MvPolynomial ι R := ∏ i ∈ s, X i

variable (R) in

/- English proof (translation)
Simplify using `using SetLike.prod_mem_graded (polyGrading ι R) (fun _ => 1) X (F := s) fun i _ => X_mem_polyGrading i`.
-/
theorem xProd_mem (s : Finset ι) : xProd R s ∈ polyGrading ι R s.card := by
  simpa using SetLike.prod_mem_graded (polyGrading ι R) (fun _ => 1) X
    (F := s) fun i _ => X_mem_polyGrading i

variable (R) in

/- English proof (translation)
Simplify using `using SetLike.pow_mem_graded k (xProd_mem R s)`.
-/
theorem xProd_pow_mem (s : Finset ι) (k : ℕ) :
    xProd R s ^ k ∈ polyGrading ι R (k * s.card) := by
  simpa using SetLike.pow_mem_graded k (xProd_mem R s)

variable (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩]
  {𝒬 : ℤ → Submodule R P} [PolyGradedSMul ι 𝒬]

omit [IsScalarTower R (MvPolynomial ι R) M] in

/- English proof (translation)
Use `grSMul_mem ℳ (xProd_pow_mem R s j) hm using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem xProd_pow_smul_mem {s : Finset ι} {n : ℤ} {k : ℕ} {m : M} (hm : m ∈ ℳ (n + k * s.card))
    (j : ℕ) : xProd R s ^ j • m ∈ ℳ (n + (k + j : ℕ) * s.card) := by
  convert grSMul_mem ℳ (xProd_pow_mem R s j) hm using 2
  push_cast
  ring

def homLoc (s : Finset ι) (n : ℤ) : Submodule R (LocalizedModule.Away (xProd R s) M) where
  carrier := {z | ∃ k : ℕ, ∃ m ∈ ℳ (n + k * s.card), awayFrac M (xProd R s) k m = z}
  zero_mem' := ⟨0, 0, zero_mem _, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨k, m, hm, rfl⟩ ⟨j, m', hm', rfl⟩
    refine ⟨k + j, xProd R s ^ j • m + xProd R s ^ k • m',
      add_mem (xProd_pow_smul_mem ℳ hm j) (add_comm j k ▸ xProd_pow_smul_mem ℳ hm' k), ?_⟩
    rw [map_add, awayFrac_add_pow_smul, add_comm k j, awayFrac_add_pow_smul]
  smul_mem' := by
    rintro r _ ⟨k, m, hm, rfl⟩
    exact ⟨k, r • m, Submodule.smul_mem _ r hm, LinearMap.map_smul_of_tower _ r m⟩

variable {ℳ} in

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_homLoc {s : Finset ι} {n : ℤ} {z : LocalizedModule.Away (xProd R s) M} :
    z ∈ homLoc ℳ s n ↔
      ∃ k : ℕ, ∃ m ∈ ℳ (n + k * s.card), awayFrac M (xProd R s) k m = z := Iff.rfl

variable {ℳ} in

/- English proof (translation)
Assemble the required witnesses or components as `⟨k, m, h ▸ hm, rfl⟩`.
-/
theorem awayFrac_mem_homLoc {s : Finset ι} {n d : ℤ} {k : ℕ} {m : M} (hm : m ∈ ℳ d)
    (h : d = n + k * s.card) : awayFrac M (xProd R s) k m ∈ homLoc ℳ s n := ⟨k, m, h ▸ hm, rfl⟩

/- English proof (translation)
Take `⟨k₀, m, hm, rfl⟩` from `hz`. Use `⟨k₀, fun k hk => ?_⟩` and prove the remaining obligations. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hk`. Conclude with `⟨_, xProd_pow_smul_mem ℳ hm j, awayFrac_add_pow_smul _ _ _ _⟩`.
-/
theorem exists_awayFrac_of_mem_homLoc {s : Finset ι} {n : ℤ}
    {z : LocalizedModule.Away (xProd R s) M} (hz : z ∈ homLoc ℳ s n) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ m ∈ ℳ (n + k * s.card), awayFrac M (xProd R s) k m = z := by
  obtain ⟨k₀, m, hm, rfl⟩ := hz
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact ⟨_, xProd_pow_smul_mem ℳ hm j, awayFrac_add_pow_smul _ _ _ _⟩

instance homLoc.polyGradedSMul (s : Finset ι) : PolyGradedSMul ι (homLoc ℳ s) where
  smul_mem := by
    rintro d n p _ hp ⟨k, m, hm, rfl⟩
    rw [← map_smul]
    exact awayFrac_mem_homLoc (grSMul_mem ℳ hp hm) (by rw [vadd_eq_add]; ring)

instance homLoc.decomposition [Decomposition ℳ] (s : Finset ι) : Decomposition (homLoc ℳ s) :=
  IsInternal.chooseDecomposition _ <| isInternal_of_sum_eq_zero _
    (fun T v hv h j hj => by
      choose! k hk using fun i hi => exists_awayFrac_of_mem_homLoc ℳ (hv i hi)
      choose! m hm e using fun i hi => hk i hi (T.sup k) (Finset.le_sup hi)
      rw [← Finset.sum_congr rfl e, ← map_sum, awayFrac_eq_zero_iff] at h
      obtain ⟨l, hl⟩ := h
      rw [← e j hj, awayFrac_eq_zero_iff]
      refine ⟨l, ?_⟩
      have := grProj_sum (grShift ℳ ((T.sup k + l : ℕ) * s.card)) T
        (fun i => xProd R s ^ l • m i) (fun i hi => xProd_pow_smul_mem ℳ (hm i hi) l) hj
      rw [← this, ← Finset.smul_sum, hl, map_zero])
    fun z => by
      obtain ⟨k, m, rfl⟩ := exists_awayFrac z
      induction m using Decomposition.inductionOn ℳ with
      | zero => rw [map_zero]; exact zero_mem _
      | @homogeneous n m =>
        exact Submodule.mem_iSup_of_mem (n - k * s.card) (awayFrac_mem_homLoc m.2 (by ring))
      | add a b ha hb => rw [map_add]; exact add_mem ha hb

/- English proof (translation)
Introduce `_ _ h` and use `awayFrac_mem_homLoc h rfl`.
-/
theorem isGradedMap_awayFrac (s : Finset ι) (k : ℕ) :
    IsGradedMap (grShift ℳ (k * s.card)) (homLoc ℳ s) (awayFrac M (xProd R s) k) :=
  fun _ _ h => awayFrac_mem_homLoc h rfl

/- English proof (translation)
Introduce `_ _ h` and use `awayFrac_mem_homLoc h (by simp)`.
-/
theorem isGradedMap_awayFrac_zero (s : Finset ι) :
    IsGradedMap ℳ (homLoc ℳ s) (awayFrac M (xProd R s) 0) :=
  fun _ _ h => awayFrac_mem_homLoc h (by simp)

/- English proof (translation)
Introduce and unpack `n _ ⟨k, m, hm, rfl⟩`. Rewrite using `[locRes_awayFrac X h (Finset.prod_sdiff h).symm]`. Use `awayFrac_mem_homLoc (grSMul_mem ℳ (xProd_pow_mem R (t \ s) k) hm) ?_` and prove the remaining obligations. Rewrite using `[← Finset.card_sdiff_add_card_eq_card h]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem isGradedMap_locRes {s t : Finset ι} (h : s ⊆ t) :
    IsGradedMap (homLoc ℳ s) (homLoc ℳ t) (locRes X M h) := by
  classical
  rintro n _ ⟨k, m, hm, rfl⟩
  rw [locRes_awayFrac X h (Finset.prod_sdiff h).symm]
  refine awayFrac_mem_homLoc (grSMul_mem ℳ (xProd_pow_mem R (t \ s) k) hm) ?_
  rw [← Finset.card_sdiff_add_card_eq_card h]
  push_cast
  ring

variable {ℳ} in

/- English proof (translation)
Introduce and unpack `n _ ⟨k, m, hm, rfl⟩`. Rewrite using `[awayMap_awayFrac]`. Conclude with `awayFrac_mem_homLoc (hf hm) rfl`.
-/
theorem IsGradedMap.awayMap {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    (s : Finset ι) : IsGradedMap (homLoc ℳ s) (homLoc 𝒩 s) (awayMap (xProd R s) f) := by
  rintro n _ ⟨k, m, hm, rfl⟩
  rw [awayMap_awayFrac]
  exact awayFrac_mem_homLoc (hf hm) rfl

/- English proof (translation)
Use extensionality with `z`. Simplify using `only [mem_homLoc, grShift_apply, add_right_comm]`.
-/
theorem homLoc_grShift (d : ℤ) (s : Finset ι) (n : ℤ) :
    homLoc (grShift ℳ d) s n = homLoc ℳ s (n + d) := by
  ext z
  simp only [mem_homLoc, grShift_apply, add_right_comm]

def homLocMk (s : Finset ι) (n : ℤ) (k : ℕ) : ℳ (n + k * s.card) →ₗ[R] homLoc ℳ s n :=
  (isGradedMap_awayFrac ℳ s k).piece n

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_homLocMk (s : Finset ι) (n : ℤ) (k : ℕ) (m : ℳ (n + k * s.card)) :
    (homLocMk ℳ s n k m : LocalizedModule.Away (xProd R s) M) = awayFrac M (xProd R s) k m := rfl

variable {ℳ} in

/- English proof (translation)
Take `⟨_, k, m, hm, rfl⟩` from `z`. Conclude with `⟨k, ⟨m, hm⟩, rfl⟩`.
-/
theorem exists_homLocMk {s : Finset ι} {n : ℤ} (z : homLoc ℳ s n) :
    ∃ k m, homLocMk ℳ s n k m = z := by
  obtain ⟨_, k, m, hm, rfl⟩ := z
  exact ⟨k, ⟨m, hm⟩, rfl⟩

def toHomLoc (s : Finset ι) (n : ℤ) : ℳ n →ₗ[R] homLoc ℳ s n :=
  (isGradedMap_awayFrac_zero ℳ s).piece n

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_toHomLoc (s : Finset ι) (n : ℤ) (m : ℳ n) :
    (toHomLoc ℳ s n m : LocalizedModule.Away (xProd R s) M) = awayFrac M (xProd R s) 0 m := rfl

def homLocRes {s t : Finset ι} (h : s ⊆ t) (n : ℤ) : homLoc ℳ s n →ₗ[R] homLoc ℳ t n :=
  (isGradedMap_locRes ℳ h).piece n

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem coe_homLocRes {s t : Finset ι} (h : s ⊆ t) (n : ℤ) (z : homLoc ℳ s n) :
    (homLocRes ℳ h n z : LocalizedModule.Away (xProd R t) M) = locRes X M h z := rfl

@[simp]
/- English proof (translation)
The claim follows from `Subtype.ext congr($(locRes_self X M s) z) @[simp]`.
-/
theorem homLocRes_self {s : Finset ι} (h : s ⊆ s) (n : ℤ) (z : homLoc ℳ s n) :
    homLocRes ℳ h n z = z := Subtype.ext congr($(locRes_self X M s) z)

@[simp]
/- English proof (translation)
The claim follows from `Subtype.ext congr($(locRes_comp X M h h') z) @[simp]`.
-/
theorem homLocRes_homLocRes {s t w : Finset ι} (h : s ⊆ t) (h' : t ⊆ w) (n : ℤ)
    (z : homLoc ℳ s n) : homLocRes ℳ h' n (homLocRes ℳ h n z) = homLocRes ℳ (h.trans h') n z :=
  Subtype.ext congr($(locRes_comp X M h h') z)

@[simp]
/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[coe_homLocRes, coe_toHomLoc, coe_toHomLoc, locRes_awayFrac_zero]`.
-/
theorem homLocRes_toHomLoc {s t : Finset ι} (h : s ⊆ t) (n : ℤ) (m : ℳ n) :
    homLocRes ℳ h n (toHomLoc ℳ s n m) = toHomLoc ℳ t n m := by
  apply Subtype.ext
  rw [coe_homLocRes, coe_toHomLoc, coe_toHomLoc, locRes_awayFrac_zero]

/- English proof (translation)
Introduce `_ _ e` and use `Subtype.ext (awayFrac_injective h 0 (congrArg Subtype.val e))`.
-/
theorem toHomLoc_injective {s : Finset ι} (h : Function.Injective fun m : M => xProd R s • m)
    (n : ℤ) : Function.Injective (toHomLoc ℳ s n) :=
  fun _ _ e => Subtype.ext (awayFrac_injective h 0 (congrArg Subtype.val e))

/- English proof (translation)
Assemble the required witnesses or components as `⟨toHomLoc_injective ℳ h.1 n, (isGradedMap_awayFrac_zero ℳ s).surjective_iff.1 (awayFrac_zero_bijective h).2 n⟩`.
-/
theorem toHomLoc_bijective [Decomposition ℳ] {s : Finset ι}
    (h : Function.Bijective fun m : M => xProd R s • m) (n : ℤ) :
    Function.Bijective (toHomLoc ℳ s n) :=
  ⟨toHomLoc_injective ℳ h.1 n,
    (isGradedMap_awayFrac_zero ℳ s).surjective_iff.1 (awayFrac_zero_bijective h).2 n⟩

variable (ι) in

def homLocEmptyEquiv (n : ℤ) : ℳ n ≃ₗ[R] homLoc ℳ (∅ : Finset ι) n :=
  LinearEquiv.ofBijective (toHomLoc ℳ ∅ n)
    ⟨toHomLoc_injective ℳ (fun _ _ h => by simpa using h) n, by
      rintro ⟨_, k, m, hm, rfl⟩
      exact ⟨⟨m, by simpa using hm⟩, Subtype.ext (awayFrac_eq_iff.2 ⟨0, by simp⟩)⟩⟩

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem homLocEmptyEquiv_apply (n : ℤ) (m : ℳ n) :
    homLocEmptyEquiv ι ℳ n m = toHomLoc ℳ ∅ n m := rfl

def homLocSMul {p : MvPolynomial ι R} {d : ℤ} (hp : p ∈ polyGrading ι R d) (s : Finset ι)
    (n : ℤ) : homLoc ℳ s n →ₗ[R] homLoc ℳ s (n + d) :=
  (isGradedMap_lsmul (homLoc ℳ s) hp).piece n

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_homLocSMul {p : MvPolynomial ι R} {d : ℤ} (hp : p ∈ polyGrading ι R d) (s : Finset ι)
    (n : ℤ) (z : homLoc ℳ s n) :
    (homLocSMul ℳ hp s n z : LocalizedModule.Away (xProd R s) M) = p • z.1 := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨(isGradedMap_lsmul (homLoc ℳ s) hp).injective_iff.1 (smul_away_bijective h).1 n, (isGradedMap_lsmul (homLoc ℳ s) hp).surjective_iff.1 (smul_away_bijective h).2 n⟩`.
-/
theorem homLocSMul_bijective [Decomposition ℳ] {p : MvPolynomial ι R} {d : ℤ}
    (hp : p ∈ polyGrading ι R d) {s : Finset ι} {k : ℕ} (h : p ∣ xProd R s ^ k) (n : ℤ) :
    Function.Bijective (homLocSMul ℳ hp s n) :=
  ⟨(isGradedMap_lsmul (homLoc ℳ s) hp).injective_iff.1 (smul_away_bijective h).1 n,
    (isGradedMap_lsmul (homLoc ℳ s) hp).surjective_iff.1 (smul_away_bijective h).2 n⟩

/- English proof (translation)
The claim follows from `homLocSMul_bijective ℳ _ (k := 1) (by rw [pow_one]; exact Finset.dvd_prod_of_mem _ hi) n`.
-/
theorem homLocSMul_X_bijective [Decomposition ℳ] {s : Finset ι} {i : ι} (hi : i ∈ s) (n : ℤ) :
    Function.Bijective (homLocSMul ℳ (X_mem_polyGrading i) s n) :=
  homLocSMul_bijective ℳ _ (k := 1) (by rw [pow_one]; exact Finset.dvd_prod_of_mem _ hi) n

variable {ℳ}

def homLocMap {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (s : Finset ι) (n : ℤ) :
    homLoc ℳ s n →ₗ[R] homLoc 𝒩 s n := (hf.awayMap s).piece n

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem coe_homLocMap {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (s : Finset ι)
    (n : ℤ) (z : homLoc ℳ s n) :
    (homLocMap hf s n z : LocalizedModule.Away (xProd R s) N) = awayMap _ f z := rfl

@[simp]
/- English proof (translation)
The claim follows from `Subtype.ext (awayMap_awayFrac (xProd R s) f k (m : M)) @[simp]`.
-/
theorem homLocMap_homLocMk {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (s : Finset ι)
    (n : ℤ) (k : ℕ) (m : ℳ (n + k * s.card)) :
    homLocMap hf s n (homLocMk ℳ s n k m) = homLocMk 𝒩 s n k (hf.piece _ m) :=
  Subtype.ext (awayMap_awayFrac (xProd R s) f k (m : M))

@[simp]
/- English proof (translation)
The claim follows from `Subtype.ext (awayMap_awayFrac (xProd R s) f 0 (m : M))`.
-/
theorem homLocMap_toHomLoc {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (s : Finset ι)
    (n : ℤ) (m : ℳ n) : homLocMap hf s n (toHomLoc ℳ s n m) = toHomLoc 𝒩 s n (hf.piece n m) :=
  Subtype.ext (awayMap_awayFrac (xProd R s) f 0 (m : M))

/- English proof (translation)
The claim follows from `Subtype.ext (awayMap_locRes X h f z.1) @[simp]`.
-/
theorem homLocMap_homLocRes {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    {s t : Finset ι} (h : s ⊆ t) (n : ℤ) (z : homLoc ℳ s n) :
    homLocMap hf t n (homLocRes ℳ h n z) = homLocRes 𝒩 h n (homLocMap hf s n z) :=
  Subtype.ext (awayMap_locRes X h f z.1)

@[simp]
/- English proof (translation)
The claim follows from `Subtype.ext congr($(awayMap_id (M := M) (xProd R s)) z.1)`.
-/
theorem homLocMap_id (h : IsGradedMap ℳ ℳ (LinearMap.id : M →ₗ[MvPolynomial ι R] M))
    (s : Finset ι) (n : ℤ) (z : homLoc ℳ s n) : homLocMap h s n z = z :=
  Subtype.ext congr($(awayMap_id (M := M) (xProd R s)) z.1)

/- English proof (translation)
The claim follows from `Subtype.ext congr($(awayMap_comp (xProd R s) g f) z.1) @[simp]`.
-/
theorem homLocMap_comp {g : N →ₗ[MvPolynomial ι R] P} {f : M →ₗ[MvPolynomial ι R] N}
    (hg : IsGradedMap 𝒩 𝒬 g) (hf : IsGradedMap ℳ 𝒩 f) (s : Finset ι) (n : ℤ) (z : homLoc ℳ s n) :
    homLocMap (hg.comp hf) s n z = homLocMap hg s n (homLocMap hf s n z) :=
  Subtype.ext congr($(awayMap_comp (xProd R s) g f) z.1)

@[simp]
/- English proof (translation)
The claim follows from `Subtype.ext congr($(awayMap_zero (M := M) (N := N) (xProd R s)) z.1)`.
-/
theorem homLocMap_zero (h : IsGradedMap ℳ 𝒩 (0 : M →ₗ[MvPolynomial ι R] N))
    (s : Finset ι) (n : ℤ) (z : homLoc ℳ s n) : homLocMap h s n z = 0 :=
  Subtype.ext congr($(awayMap_zero (M := M) (N := N) (xProd R s)) z.1)

/- English proof (translation)
Introduce `_ _ e` and use `Subtype.ext (awayMap_injective_of h (congrArg Subtype.val e))`.
-/
theorem homLocMap_injective_of {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    {s : Finset ι} (h : ∀ m, f m = 0 → ∃ k : ℕ, xProd R s ^ k • m = 0) (n : ℤ) :
    Function.Injective (homLocMap hf s n) :=
  fun _ _ e => Subtype.ext (awayMap_injective_of h (congrArg Subtype.val e))

/- English proof (translation)
The claim follows from `homLocMap_injective_of hf (fun m hm => ⟨0, by rw [(map_eq_zero_iff f h).1 hm, smul_zero]⟩) n`.
-/
theorem homLocMap_injective {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    (h : Function.Injective f) (s : Finset ι) (n : ℤ) : Function.Injective (homLocMap hf s n) :=
  homLocMap_injective_of hf
    (fun m hm => ⟨0, by rw [(map_eq_zero_iff f h).1 hm, smul_zero]⟩) n

variable [Decomposition ℳ] [Decomposition 𝒩]

/- English proof (translation)
The claim follows from `(hf.awayMap s).surjective_iff.1 (awayMap_surjective_of h) n`.
-/
theorem homLocMap_surjective_of {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    {s : Finset ι} (h : ∀ y, ∃ k : ℕ, xProd R s ^ k • y ∈ LinearMap.range f) (n : ℤ) :
    Function.Surjective (homLocMap hf s n) :=
  (hf.awayMap s).surjective_iff.1 (awayMap_surjective_of h) n

/- English proof (translation)
The claim follows from `homLocMap_surjective_of hf (fun _ => ⟨0, h _⟩) n`.
-/
theorem homLocMap_surjective {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    (h : Function.Surjective f) (s : Finset ι) (n : ℤ) : Function.Surjective (homLocMap hf s n) :=
  homLocMap_surjective_of hf (fun _ => ⟨0, h _⟩) n

/- English proof (translation)
The claim follows from `(hf.awayMap s).exact_piece (hg.awayMap s) (awayMap_exact _ h) n`.
-/
theorem homLocMap_exact {f : M →ₗ[MvPolynomial ι R] N} {g : N →ₗ[MvPolynomial ι R] P}
    (hf : IsGradedMap ℳ 𝒩 f) (hg : IsGradedMap 𝒩 𝒬 g) (h : Function.Exact f g) (s : Finset ι)
    (n : ℤ) : Function.Exact (homLocMap hf s n) (homLocMap hg s n) :=
  (hf.awayMap s).exact_piece (hg.awayMap s) (awayMap_exact _ h) n

/- English proof (translation)
Take `⟨c, hc⟩ : ∃ c, xProd R s = c * X i` from `exists_eq_mul_left_of_dvd (Finset.dvd_prod_of_mem _ hi)`. Use `⟨homLocMap_injective_of hf (fun m hm => (h₁ m hm).imp fun k hk => ?_) n, homLocMap_surjective_of hf (fun y => (h₂ y).imp fun k hk => ?_) n⟩` and prove the remaining obligations. Rewrite using `[hc, mul_pow, mul_smul, hk, smul_zero]`. Rewrite using `[hc, mul_pow, mul_smul]`. Conclude with `Submodule.smul_mem _ _ hk`.
-/
theorem homLocMap_bijective_of_X {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    {s : Finset ι} {i : ι} (hi : i ∈ s)
    (h₁ : ∀ m, f m = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • m = 0)
    (h₂ : ∀ y, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ LinearMap.range f) (n : ℤ) :
    Function.Bijective (homLocMap hf s n) := by
  obtain ⟨c, hc⟩ : ∃ c, xProd R s = c * X i :=
    exists_eq_mul_left_of_dvd (Finset.dvd_prod_of_mem _ hi)
  refine ⟨homLocMap_injective_of hf (fun m hm => (h₁ m hm).imp fun k hk => ?_) n,
    homLocMap_surjective_of hf (fun y => (h₂ y).imp fun k hk => ?_) n⟩
  · rw [hc, mul_pow, mul_smul, hk, smul_zero]
  · rw [hc, mul_pow, mul_smul]
    exact Submodule.smul_mem _ _ hk

end HomLoc

section Lift

variable {ι : Type} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  [IsScalarTower R (MvPolynomial ι R) M] {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ]
  {T : Type*} [AddCommGroup T] [Module R T] {s : Finset ι} {n : ℤ}
  (φ : ∀ k : ℕ, ℳ (n + k * s.card) →ₗ[R] T)
  (hφ : ∀ (k : ℕ) (m : ℳ (n + k * s.card)) (m' : ℳ (n + (k + 1 : ℕ) * s.card)),
    (m' : M) = xProd R s • (m : M) → φ (k + 1) m' = φ k m)
include hφ

omit [IsScalarTower R (MvPolynomial ι R) M] in

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => exact congrArg (φ k) (Subtype.ext (by simp))`. Consider the case `succ j ih => exact (hφ (k + j) _ _ (by simp [pow_succ', mul_smul])).trans ih`.
-/
theorem homLocLift_pow (k j : ℕ) (m : ℳ (n + k * s.card)) :
    φ (k + j) ⟨_, xProd_pow_smul_mem ℳ m.2 j⟩ = φ k m := by
  induction j with
  | zero => exact congrArg (φ k) (Subtype.ext (by simp))
  | succ j ih => exact (hφ (k + j) _ _ (by simp [pow_succ', mul_smul])).trans ih

/- English proof (translation)
Take `⟨l, hl⟩` from `awayFrac_eq_iff.1 (congrArg Subtype.val h)`. Establish `key : ∀ (a b : ℕ) (_ : a = b) (x : ℳ (n + a * s.card)) (y : ℳ (n + b * s.card)), (x : M) = y → φ a x = φ b y`. Introduce and unpack `a _ rfl x y e`. Rewrite using `[Subtype.ext e]`. Rewrite using `[← homLocLift_pow φ hφ k (l + j), ← homLocLift_pow φ hφ j (l + k)]`.

Conclude with `key _ _ (by ring) _ _ hl`.
-/
theorem homLocLift_congr {k j : ℕ} {m : ℳ (n + k * s.card)} {m' : ℳ (n + j * s.card)}
    (h : homLocMk ℳ s n k m = homLocMk ℳ s n j m') : φ k m = φ j m' := by
  obtain ⟨l, hl⟩ := awayFrac_eq_iff.1 (congrArg Subtype.val h)
  have key : ∀ (a b : ℕ) (_ : a = b) (x : ℳ (n + a * s.card)) (y : ℳ (n + b * s.card)),
      (x : M) = y → φ a x = φ b y := by
    rintro a _ rfl x y e
    rw [Subtype.ext e]
  rw [← homLocLift_pow φ hφ k (l + j), ← homLocLift_pow φ hφ j (l + k)]
  exact key _ _ (by ring) _ _ hl

def homLocLift : homLoc ℳ s n →ₗ[R] T :=
  have key (k : ℕ) (m : ℳ (n + k * s.card)) :
      φ _ (exists_homLocMk (homLocMk ℳ s n k m)).choose_spec.choose = φ k m :=
    homLocLift_congr φ hφ (exists_homLocMk (homLocMk ℳ s n k m)).choose_spec.choose_spec
  { toFun z := φ _ (exists_homLocMk z).choose_spec.choose
    map_add' z w := by
      obtain ⟨a, ha⟩ := exists_awayFrac_of_mem_homLoc ℳ z.2
      obtain ⟨b, hb⟩ := exists_awayFrac_of_mem_homLoc ℳ w.2
      obtain ⟨x, hx, ex⟩ := ha (max a b) (le_max_left _ _)
      obtain ⟨y, hy, ey⟩ := hb (max a b) (le_max_right _ _)
      obtain rfl : homLocMk ℳ s n _ ⟨x, hx⟩ = z := Subtype.ext ex
      obtain rfl : homLocMk ℳ s n _ ⟨y, hy⟩ = w := Subtype.ext ey
      rw [← map_add, key, key, key, map_add]
    map_smul' r z := by
      obtain ⟨k, m, rfl⟩ := exists_homLocMk z
      rw [← map_smul, key, key, map_smul, RingHom.id_apply] }

@[simp]
/- English proof (translation)
The claim follows from `homLocLift_congr φ hφ (exists_homLocMk (homLocMk ℳ s n k m)).choose_spec.choose_spec`.
-/
theorem homLocLift_homLocMk (k : ℕ) (m : ℳ (n + k * s.card)) :
    homLocLift φ hφ (homLocMk ℳ s n k m) = φ k m :=
  homLocLift_congr φ hφ (exists_homLocMk (homLocMk ℳ s n k m)).choose_spec.choose_spec

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `h k m hm`. Conclude with `awayFrac_eq_zero_iff.1 (congrArg Subtype.val (h _ ((homLocLift_homLocMk φ hφ k m).trans hm)))`. Introduce `h z hz`.

Take `⟨k, m, rfl⟩` from `exists_homLocMk z`. Conclude with `Subtype.ext (awayFrac_eq_zero_iff.2 (h k m ((homLocLift_homLocMk φ hφ k m).symm.trans hz)))`.
-/
theorem homLocLift_injective_iff : Function.Injective (homLocLift φ hφ) ↔
    ∀ k m, φ k m = 0 → ∃ l : ℕ, xProd R s ^ l • (m : M) = 0 := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h k m hm
    exact awayFrac_eq_zero_iff.1
      (congrArg Subtype.val (h _ ((homLocLift_homLocMk φ hφ k m).trans hm)))
  · intro h z hz
    obtain ⟨k, m, rfl⟩ := exists_homLocMk z
    exact Subtype.ext (awayFrac_eq_zero_iff.2 (h k m ((homLocLift_homLocMk φ hφ k m).symm.trans hz)))

/- English proof (translation)
Use `forall_congr' fun t => ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨z, rfl⟩`. Take `⟨k, m, rfl⟩` from `exists_homLocMk z`. Conclude with `⟨k, m, (homLocLift_homLocMk φ hφ k m).symm⟩`. Introduce and unpack `⟨k, m, rfl⟩`.

Conclude with `⟨_, homLocLift_homLocMk φ hφ k m⟩`.
-/
theorem homLocLift_surjective_iff : Function.Surjective (homLocLift φ hφ) ↔
    ∀ t, ∃ k m, φ k m = t := by
  refine forall_congr' fun t => ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨k, m, rfl⟩ := exists_homLocMk z
    exact ⟨k, m, (homLocLift_homLocMk φ hφ k m).symm⟩
  · rintro ⟨k, m, rfl⟩
    exact ⟨_, homLocLift_homLocMk φ hφ k m⟩

end Lift

section Pi

variable {ι : Type} {R : Type*} [CommRing R] {κ : Type*} [Finite κ]
  {M : κ → Type*} [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
  [∀ k, Module (MvPolynomial ι R) (M k)] [∀ k, IsScalarTower R (MvPolynomial ι R) (M k)]
  (ℳ : ∀ k, ℤ → Submodule R (M k)) [∀ k, PolyGradedSMul ι (ℳ k)]

/- English proof (translation)
Use `Fintype.ofFinite κ` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`. Take `⟨j, m, rfl⟩` from `exists_homLocMk z`.

Establish `h (k : κ) : ∃ l : ℕ, xProd R s ^ l • m.1 k = 0`. Use `congrFun hz k` as an intermediate fact. Rewrite `this` using `[LinearMap.pi_apply, homLocMap_homLocMk]`. Conclude with `awayFrac_eq_zero_iff.1 (congrArg Subtype.val this)`. Use `choose l hl using h`.

Use `Subtype.ext ((coe_homLocMk _ s n j m).trans (awayFrac_eq_zero_iff.2 ⟨Finset.univ.sup l, funext fun k => ?_⟩))` and prove the remaining obligations. Take `⟨c, hc⟩` from `Nat.exists_eq_add_of_le' (Finset.le_sup (f := l) (Finset.mem_univ k))`. Rewrite using `[Pi.smul_apply, hc, pow_add, mul_smul, hl, smul_zero, Pi.zero_apply]`. Introduce `z choose j hj using fun k => exists_awayFrac_of_mem_homLoc (ℳ k) (z k).2 choose m hm e using fun k => hj k (Finset.univ.sup j) (Finset.le_sup (Finset.mem_univ k))`. Use `⟨homLocMk _ s n _ ⟨m, mem_grPi.2 hm⟩, funext fun k => ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.pi_apply, homLocMap_homLocMk]`. Conclude with `Subtype.ext (e k)`.
-/
theorem homLocMap_piProj_bijective (s : Finset ι) (n : ℤ) :
    Function.Bijective (LinearMap.pi fun k => homLocMap (isGradedMap_piProj ι ℳ k) s n) := by
  classical
  have := Fintype.ofFinite κ
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨j, m, rfl⟩ := exists_homLocMk z
    have h (k : κ) : ∃ l : ℕ, xProd R s ^ l • m.1 k = 0 := by
      have := congrFun hz k
      rw [LinearMap.pi_apply, homLocMap_homLocMk] at this
      exact awayFrac_eq_zero_iff.1 (congrArg Subtype.val this)
    choose l hl using h
    refine Subtype.ext ((coe_homLocMk _ s n j m).trans
      (awayFrac_eq_zero_iff.2 ⟨Finset.univ.sup l, funext fun k => ?_⟩))
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := l) (Finset.mem_univ k))
    rw [Pi.smul_apply, hc, pow_add, mul_smul, hl, smul_zero, Pi.zero_apply]
  · intro z
    choose j hj using fun k => exists_awayFrac_of_mem_homLoc (ℳ k) (z k).2
    choose m hm e using fun k => hj k (Finset.univ.sup j) (Finset.le_sup (Finset.mem_univ k))
    refine ⟨homLocMk _ s n _ ⟨m, mem_grPi.2 hm⟩, funext fun k => ?_⟩
    rw [LinearMap.pi_apply, homLocMap_homLocMk]
    exact Subtype.ext (e k)

def homLocPiEquiv (s : Finset ι) (n : ℤ) :
    homLoc (grPi ℳ) s n ≃ₗ[R] ∀ k, homLoc (ℳ k) s n :=
  LinearEquiv.ofBijective _ (homLocMap_piProj_bijective ℳ s n)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem homLocPiEquiv_apply (s : Finset ι) (n : ℤ) (z : homLoc (grPi ℳ) s n) (k : κ) :
    homLocPiEquiv ℳ s n z k = homLocMap (isGradedMap_piProj ι ℳ k) s n z := rfl

end Pi

section Cech

variable (ι : Type) {R : Type u} [CommRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  [IsScalarTower R (MvPolynomial ι R) M]
  {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]
  {P : Type u} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
  [IsScalarTower R (MvPolynomial ι R) P]
  (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩]
  {𝒬 : ℤ → Submodule R P} [PolyGradedSMul ι 𝒬]

def grCube (n : ℤ) : Cube.{u} ι R :=
  Cube.mk (fun s => ModuleCat.of R (homLoc ℳ s n)) (fun h => homLocRes ℳ h n)
    (fun _ => homLocRes_self ℳ _ n) fun h h' => homLocRes_homLocRes ℳ h h' n

def grCech [LinearOrder ι] (n : ℤ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  cechComplex (grCube ι ℳ n)

abbrev grH [LinearOrder ι] (n : ℤ) (p : ℕ) : ModuleCat.{u} R := (grCech ι ℳ n).homology p

variable {ι}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem res_grCube (n : ℤ) {s t : Finset ι} (h : s ⊆ t) :
    Cube.res (grCube ι ℳ n) h = homLocRes ℳ h n := rfl

def grCubeShiftIso (d n : ℤ) : grCube ι (grShift ℳ d) n ≅ grCube ι ℳ (n + d) :=
  Cube.isoMk (fun s => LinearEquiv.ofEq _ _ (homLoc_grShift ℳ d s n)) fun _ _ => rfl

variable {ℳ}

def grCubeMap {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) :
    grCube ι ℳ n ⟶ grCube ι 𝒩 n :=
  Cube.homMk (fun s => homLocMap hf s n) fun h => homLocMap_homLocRes hf h n

@[simp]
/- English proof (translation)
The claim follows from `NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext (homLocMap_id h s n)))`.
-/
theorem grCubeMap_id (h : IsGradedMap ℳ ℳ (LinearMap.id : M →ₗ[MvPolynomial ι R] M)) (n : ℤ) :
    grCubeMap h n = 𝟙 _ :=
  NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext (homLocMap_id h s n)))

/- English proof (translation)
The claim follows from `NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext (homLocMap_comp hg hf s n))) @[simp]`.
-/
theorem grCubeMap_comp {g : N →ₗ[MvPolynomial ι R] P} {f : M →ₗ[MvPolynomial ι R] N}
    (hg : IsGradedMap 𝒩 𝒬 g) (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) :
    grCubeMap (hg.comp hf) n = grCubeMap hf n ≫ grCubeMap hg n :=
  NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext (homLocMap_comp hg hf s n)))

@[simp]
/- English proof (translation)
The claim follows from `NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext (homLocMap_zero h s n)))`.
-/
theorem grCubeMap_zero (h : IsGradedMap ℳ 𝒩 (0 : M →ₗ[MvPolynomial ι R] N)) (n : ℤ) :
    grCubeMap h n = 0 :=
  NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext (homLocMap_zero h s n)))

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem grCubeMap_congr {f g : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    (hg : IsGradedMap ℳ 𝒩 g) (h : f = g) (n : ℤ) : grCubeMap hf n = grCubeMap hg n := by
  subst h; rfl

def grCubeIso [Decomposition ℳ] [Decomposition 𝒩] {e : M ≃ₗ[MvPolynomial ι R] N}
    (he : IsGradedMap ℳ 𝒩 e.toLinearMap) (n : ℤ) : grCube ι ℳ n ≅ grCube ι 𝒩 n where
  hom := grCubeMap he n
  inv := grCubeMap he.symm n
  hom_inv_id := by
    rw [← grCubeMap_comp, grCubeMap_congr _ (IsGradedMap.id ι ℳ) (by simp), grCubeMap_id]
  inv_hom_id := by
    rw [← grCubeMap_comp, grCubeMap_congr _ (IsGradedMap.id ι 𝒩) (by simp), grCubeMap_id]

variable [LinearOrder ι]

variable (ℳ) in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem grCech_eq (n : ℤ) : grCech ι ℳ n = cechComplex (grCube ι ℳ n) := rfl

variable (ℳ) in

/- English proof (translation)
The claim follows from `cechComplex_d _ p`.
-/
theorem grCech_d (n : ℤ) (p : ℕ) :
    (grCech ι ℳ n).d p (p + 1) = ModuleCat.ofHom (Cube.d (grCube ι ℳ n) (p + 1)) :=
  cechComplex_d _ p

def grCechMap {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) :
    grCech ι ℳ n ⟶ grCech ι 𝒩 n := cechComplexMap (grCubeMap hf n)

abbrev grHMap {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) (p : ℕ) :
    grH ι ℳ n p ⟶ grH ι 𝒩 n p := HomologicalComplex.homologyMap (grCechMap hf n) p

@[simp]
/- English proof (translation)
The claim follows from `congrArg cechComplexMap (grCubeMap_id h n) @[simp]`.
-/
theorem grCechMap_id (h : IsGradedMap ℳ ℳ (LinearMap.id : M →ₗ[MvPolynomial ι R] M)) (n : ℤ) :
    grCechMap h n = 𝟙 _ := congrArg cechComplexMap (grCubeMap_id h n)

@[simp]
/- English proof (translation)
The claim follows from `congrArg cechComplexMap (grCubeMap_zero h n)`.
-/
theorem grCechMap_zero (h : IsGradedMap ℳ 𝒩 (0 : M →ₗ[MvPolynomial ι R] N)) (n : ℤ) :
    grCechMap h n = 0 := congrArg cechComplexMap (grCubeMap_zero h n)

/- English proof (translation)
The claim follows from `isIso_cechComplexMap _ fun _ ⟨i, hi⟩ => homLocMap_bijective_of_X hf hi (h₁ i) (h₂ i) n`.
-/
theorem isIso_grCechMap [Decomposition ℳ] [Decomposition 𝒩] {f : M →ₗ[MvPolynomial ι R] N}
    (hf : IsGradedMap ℳ 𝒩 f)
    (h₁ : ∀ (i : ι) m, f m = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • m = 0)
    (h₂ : ∀ (i : ι) y, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ LinearMap.range f) (n : ℤ) :
    IsIso (grCechMap hf n) :=
  isIso_cechComplexMap _ fun _ ⟨i, hi⟩ => homLocMap_bijective_of_X hf hi (h₁ i) (h₂ i) n

variable (ℳ) in

def grCechShiftIso (d n : ℤ) : grCech ι (grShift ℳ d) n ≅ grCech ι ℳ (n + d) :=
  (cechFunctor ι R).mapIso (grCubeShiftIso ℳ d n)

variable (ℳ) in

def grHShiftIso (d n : ℤ) (p : ℕ) : grH ι (grShift ℳ d) n p ≅ grH ι ℳ (n + d) p :=
  HomologicalComplex.homologyMapIso (grCechShiftIso ℳ d n) p

variable (ι ℳ) in

def grAug (n : ℤ) : ℳ n →ₗ[R] grH ι ℳ n 0 :=
  (cechAugHomology (grCube ι ℳ n)).hom ∘ₗ toHomLoc ℳ ∅ n

variable (ℳ) in

/- English proof (translation)
The claim follows from `(congrFun congr(($(cechAugHomology_comp (grCube ι ℳ n))).hom (toHomLoc ℳ ∅ n m)) s).trans (homLocRes_toHomLoc ℳ _ n m)`.
-/
theorem cechHomologyZeroIso_grAug (n : ℤ) (m : ℳ n) (s : {s : Finset ι // s.card = 1}) :
    ((cechHomologyZeroIso (grCube ι ℳ n)).hom.hom (grAug ι ℳ n m)).1 s = toHomLoc ℳ s.1 n m :=
  (congrFun congr(($(cechAugHomology_comp (grCube ι ℳ n))).hom (toHomLoc ℳ ∅ n m)) s).trans
    (homLocRes_toHomLoc ℳ _ n m)

/- English proof (translation)
The claim follows from `congr(($(cechAugHomology_naturality (grCubeMap hf n))).hom (toHomLoc ℳ ∅ n m)).symm.trans (congrArg (cechAugHomology (grCube ι 𝒩 n)).hom (homLocMap_toHomLoc hf ∅ n m))`.
-/
theorem grHMap_grAug {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) (m : ℳ n) :
    (grHMap hf n 0).hom (grAug ι ℳ n m) = grAug ι 𝒩 n (hf.piece n m) :=
  congr(($(cechAugHomology_naturality (grCubeMap hf n))).hom (toHomLoc ℳ ∅ n m)).symm.trans
    (congrArg (cechAugHomology (grCube ι 𝒩 n)).hom (homLocMap_toHomLoc hf ∅ n m))

variable (ℳ) in

/- English proof (translation)
Rewrite using `[← isIso_cechAugHomology_iff, ConcreteCategory.isIso_iff_bijective]`. Conclude with `Function.Bijective.of_comp_iff (cechAugHomology (grCube ι ℳ n)).hom (g := toHomLoc ℳ ∅ n) (homLocEmptyEquiv ι ℳ n).bijective`.
-/
theorem grAug_bijective_iff (n : ℤ) : Function.Bijective (grAug ι ℳ n) ↔
    (cubeComplex (grCube ι ℳ n)).ExactAt 0 ∧ (cubeComplex (grCube ι ℳ n)).ExactAt 1 := by
  rw [← isIso_cechAugHomology_iff, ConcreteCategory.isIso_iff_bijective]
  exact Function.Bijective.of_comp_iff (cechAugHomology (grCube ι ℳ n)).hom
    (g := toHomLoc ℳ ∅ n) (homLocEmptyEquiv ι ℳ n).bijective

end Cech

section ShortExactDef

variable {ι : Type} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]

structure GradedShortExact (ℳ : ℤ → Submodule R M) (𝒩 : ℤ → Submodule R N)
    (𝒬 : ℤ → Submodule R P) (f : M →ₗ[MvPolynomial ι R] N) (g : N →ₗ[MvPolynomial ι R] P) :
    Prop where

  graded_f : IsGradedMap ℳ 𝒩 f

  graded_g : IsGradedMap 𝒩 𝒬 g

  injective : Function.Injective f

  exact : Function.Exact f g

  surjective : Function.Surjective g

variable [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) P]

omit [IsScalarTower R (MvPolynomial ι R) P] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨isGradedMap_subtype _ _, hg, Submodule.injective_subtype _, LinearMap.exact_subtype_ker_map g, h⟩`.
-/
theorem IsGradedMap.shortExact_ker {𝒩 : ℤ → Submodule R N} {𝒬 : ℤ → Submodule R P}
    {g : N →ₗ[MvPolynomial ι R] P} (hg : IsGradedMap 𝒩 𝒬 g) (h : Function.Surjective g) :
    GradedShortExact (grSub 𝒩 (LinearMap.ker g)) 𝒩 𝒬 (LinearMap.ker g).subtype g :=
  ⟨isGradedMap_subtype _ _, hg, Submodule.injective_subtype _, LinearMap.exact_subtype_ker_map g, h⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨homLocMap_injective _ h.injective s n, homLocMap_exact _ _ h.exact s n, homLocMap_surjective _ h.surjective s n⟩`.
-/
theorem GradedShortExact.homLoc {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
    {𝒬 : ℤ → Submodule R P} [PolyGradedSMul ι ℳ] [PolyGradedSMul ι 𝒩] [PolyGradedSMul ι 𝒬]
    [Decomposition ℳ] [Decomposition 𝒩] [Decomposition 𝒬]
    {f : M →ₗ[MvPolynomial ι R] N} {g : N →ₗ[MvPolynomial ι R] P}
    (h : GradedShortExact ℳ 𝒩 𝒬 f g) (s : Finset ι) (n : ℤ) :
    Function.Injective (homLocMap h.graded_f s n) ∧
      Function.Exact (homLocMap h.graded_f s n) (homLocMap h.graded_g s n) ∧
      Function.Surjective (homLocMap h.graded_g s n) :=
  ⟨homLocMap_injective _ h.injective s n, homLocMap_exact _ _ h.exact s n,
    homLocMap_surjective _ h.surjective s n⟩

end ShortExactDef

namespace GradedShortExact

variable {ι : Type} {R : Type u} [CommRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  [IsScalarTower R (MvPolynomial ι R) M]
  {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]
  {P : Type u} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
  [IsScalarTower R (MvPolynomial ι R) P]
  {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩]
  {𝒬 : ℤ → Submodule R P} [PolyGradedSMul ι 𝒬]
  {f : M →ₗ[MvPolynomial ι R] N} {g : N →ₗ[MvPolynomial ι R] P} (h : GradedShortExact ℳ 𝒩 𝒬 f g)

abbrev cubes (n : ℤ) : ShortComplex (Cube.{u} ι R) :=
  ShortComplex.mk (grCubeMap h.graded_f n) (grCubeMap h.graded_g n) (by
    rw [← grCubeMap_comp, grCubeMap_congr _ (IsGradedMap.zero ι ℳ 𝒬)
      h.exact.linearMap_comp_eq_zero, grCubeMap_zero])

variable [LinearOrder ι]

abbrev cech (n : ℤ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (grCechMap h.graded_f n) (grCechMap h.graded_g n)
    ((h.cubes n).map (cechFunctor ι R)).zero

variable [Decomposition ℳ] [Decomposition 𝒩] [Decomposition 𝒬]

omit [LinearOrder ι] in

/- English proof (translation)
The claim follows from `ModuleCat.shortComplex_shortExact _ (h.homLoc s n).2.1 (h.homLoc s n).1 (h.homLoc s n).2.2`.
-/
theorem cubes_shortExact (n : ℤ) (s : Finset ι) :
    ((h.cubes n).map ((evaluation _ _).obj s)).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (h.homLoc s n).2.1 (h.homLoc s n).1 (h.homLoc s n).2.2

/- English proof (translation)
The claim follows from `cubeFunctor_shortExact _ (h.cubes_shortExact n)`.
-/
theorem cubeComplex_shortExact (n : ℤ) : ((h.cubes n).map (cubeFunctor ι R)).ShortExact :=
  cubeFunctor_shortExact _ (h.cubes_shortExact n)

/- English proof (translation)
The claim follows from `cechFunctor_shortExact _ fun s _ => h.cubes_shortExact n s`.
-/
theorem cech_shortExact (n : ℤ) : (h.cech n).ShortExact :=
  cechFunctor_shortExact _ fun s _ => h.cubes_shortExact n s

def δ (n : ℤ) (p : ℕ) : grH ι 𝒬 n p ⟶ grH ι ℳ n (p + 1) :=
  (h.cech_shortExact n).δ p (p + 1) rfl

/- English proof (translation)
The claim follows from `(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 ((h.cech_shortExact n).homology_exact₁ p (p + 1) rfl)`.
-/
theorem exact_δ_map (n : ℤ) (p : ℕ) :
    Function.Exact (h.δ n p).hom (grHMap h.graded_f n (p + 1)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((h.cech_shortExact n).homology_exact₁ p (p + 1) rfl)

/- English proof (translation)
The claim follows from `(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 ((h.cech_shortExact n).homology_exact₃ p (p + 1) rfl)`.
-/
theorem exact_map_δ (n : ℤ) (p : ℕ) :
    Function.Exact (grHMap h.graded_g n p).hom (h.δ n p).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((h.cech_shortExact n).homology_exact₃ p (p + 1) rfl)

end GradedShortExact

section PiCech

variable {ι : Type} {R : Type u} [CommRing R] {κ : Type} [Fintype κ]
  {M : κ → Type u} [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
  [∀ k, Module (MvPolynomial ι R) (M k)] [∀ k, IsScalarTower R (MvPolynomial ι R) (M k)]
  (ℳ : ∀ k, ℤ → Submodule R (M k)) [∀ k, PolyGradedSMul ι (ℳ k)]

variable (ι) in

def grCubePiIso (n : ℤ) : grCube ι (grPi ℳ) n ≅ Cube.directSum fun k => grCube ι (ℳ k) n :=
  Cube.isoMk (fun s => homLocPiEquiv ℳ s n ≪≫ₗ
      (DirectSum.linearEquivFunOnFintype R κ fun k => homLoc (ℳ k) s n).symm)
    fun h z => DFinsupp.ext fun k => homLocMap_homLocRes (isGradedMap_piProj ι ℳ k) h n z

variable [LinearOrder ι]

variable (ι) in

def grCechPiIso (n : ℤ) :
    grCech ι (grPi ℳ) n ≅ cechComplex (Cube.directSum fun k => grCube ι (ℳ k) n) :=
  (cechFunctor ι R).mapIso (grCubePiIso ι ℳ n)

variable [Finite ι]

variable (ι) in

def grHPiEquiv [DecidableEq κ] (n : ℤ) (p : ℕ) :
    grH ι (grPi ℳ) n p ≃ₗ[R] ⨁ k, grH ι (ℳ k) n p :=
  (HomologicalComplex.homologyMapIso (grCechPiIso ι ℳ n) p).toLinearEquiv ≪≫ₗ
    (cechHomologyDirectSumEquiv (fun k => grCube ι (ℳ k) n) p).symm

/- English proof (translation)
The claim follows from `(exactAt_iff_of_quasiIsoAt ((cubeFunctor ι R).mapIso (grCubePiIso ι ℳ n)).hom p).trans (cubeComplex_directSum_exactAt_iff _ p)`.
-/
theorem cubeComplex_grPi_exactAt_iff (n : ℤ) (p : ℕ) :
    (cubeComplex (grCube ι (grPi ℳ) n)).ExactAt p ↔
      ∀ k, (cubeComplex (grCube ι (ℳ k) n)).ExactAt p :=
  (exactAt_iff_of_quasiIsoAt
    ((cubeFunctor ι R).mapIso (grCubePiIso ι ℳ n)).hom p).trans
    (cubeComplex_directSum_exactAt_iff _ p)

end PiCech

section Examples

variable {ι : Type} {R : Type u} [CommRing R]

/- English proof (translation)
The claim follows from `(IsRegular.prod fun _ _ => MvPolynomial.isRegular_X).left`.
-/
theorem xProd_smul_injective (s : Finset ι) :
    Function.Injective fun p : MvPolynomial ι R => xProd R s • p :=
  (IsRegular.prod fun _ _ => MvPolynomial.isRegular_X).left

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨inferInstance⟩, inferInstance⟩`.
-/
example (d : Fin 3 → ℤ) : Nonempty (Decomposition (grFree ι R d)) ∧
    PolyGradedSMul ι (grFree ι R d) := ⟨⟨inferInstance⟩, inferInstance⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨by simpa using SetLike.one_mem_graded _, by simpa using X_mem_polyGrading i⟩`.
-/
example (d : ℤ) (i : ι) : (1 : MvPolynomial ι R) ∈ grShift (polyGrading ι R) (-d) d ∧
    (X i : MvPolynomial ι R) ∈ grShift (polyGrading ι R) d (1 - d) :=
  ⟨by simpa using SetLike.one_mem_graded _, by simpa using X_mem_polyGrading i⟩

/- English proof (translation)
The claim follows from `awayFrac_mem_homLoc (X_mem_polyGrading j) (by simp)`.
-/
example (i j : ι) : awayFrac _ (xProd R {i}) 1 (X j) ∈ homLoc (polyGrading ι R) {i} 0 :=
  awayFrac_mem_homLoc (X_mem_polyGrading j) (by simp)

/- English proof (translation)
Establish `h₁ : awayFrac _ (xProd R {i}) 1 1 ∈ homLoc (polyGrading ι R) {i} (-1)` using `awayFrac_mem_homLoc (SetLike.one_mem_graded _) (by simp)`. Establish `h₂ : awayFrac (MvPolynomial ι R) (xProd R {i}) 1 1 ≠ 0` using `(map_ne_zero_iff _ (awayFrac_injective (xProd_smul_injective _) 1)).2 one_ne_zero`. Conclude with `⟨h₁, h₂, fun h => absurd (degree_eq_of_mem_mem _ h₁ h h₂) (by decide)⟩`.
-/
example [Nontrivial R] (i : ι) :
    awayFrac _ (xProd R {i}) 1 1 ∈ homLoc (polyGrading ι R) {i} (-1) ∧
      awayFrac (MvPolynomial ι R) (xProd R {i}) 1 1 ≠ 0 ∧
      awayFrac _ (xProd R {i}) 1 1 ∉ homLoc (polyGrading ι R) {i} 1 := by
  have h₁ : awayFrac _ (xProd R {i}) 1 1 ∈ homLoc (polyGrading ι R) {i} (-1) :=
    awayFrac_mem_homLoc (SetLike.one_mem_graded _) (by simp)
  have h₂ : awayFrac (MvPolynomial ι R) (xProd R {i}) 1 1 ≠ 0 :=
    (map_ne_zero_iff _ (awayFrac_injective (xProd_smul_injective _) 1)).2 one_ne_zero
  exact ⟨h₁, h₂, fun h => absurd (degree_eq_of_mem_mem _ h₁ h h₂) (by decide)⟩

/- English proof (translation)
Rewrite using `[locRes_awayFrac X _ (c := X 1) (by simp [mul_comm])]`. Simplify using the standard rewrite rules.
-/
example : locRes (X : Fin 2 → MvPolynomial (Fin 2) ℤ) (MvPolynomial (Fin 2) ℤ)
    (show ({0} : Finset (Fin 2)) ⊆ {0, 1} by decide) (awayFrac _ _ 1 1) =
    awayFrac _ _ 1 (X 1) := by
  rw [locRes_awayFrac X _ (c := X 1) (by simp [mul_comm])]
  simp

/- English proof (translation)
Rewrite using `[← HomologicalComplex.exactAt_iff_isZero_homology, cochainComplex_exactAt_zero_iff, grCech_d _ _ 0]`. Introduce `h`. Use `Cube.subsingleton_term (grCube (Fin 1) (polyGrading (Fin 1) ℤ) (-1)) (p := 2) (by simp)` as an intermediate fact. Set `z : Cube.Term (grCube (Fin 1) (polyGrading (Fin 1) ℤ) (-1)) 1` to `fun s => ⟨awayFrac _ _ 1 1, awayFrac_mem_homLoc (SetLike.one_mem_graded _) (by simp [s.2])⟩`. Establish `hz : z = 0` using `h (Subsingleton.elim (α := Cube.Term _ 2) _ _)`.

Conclude with `(map_ne_zero_iff _ (awayFrac_injective (xProd_smul_injective {0}) 1)).2 one_ne_zero (congrArg Subtype.val (congrFun hz ⟨{0}, rfl⟩))`.
-/
example : ¬ Limits.IsZero (grH (Fin 1) (polyGrading (Fin 1) ℤ) (-1) 0) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, cochainComplex_exactAt_zero_iff,
    grCech_d _ _ 0]
  intro h
  have := Cube.subsingleton_term (grCube (Fin 1) (polyGrading (Fin 1) ℤ) (-1)) (p := 2) (by simp)
  let z : Cube.Term (grCube (Fin 1) (polyGrading (Fin 1) ℤ) (-1)) 1 := fun s =>
    ⟨awayFrac _ _ 1 1, awayFrac_mem_homLoc (SetLike.one_mem_graded _) (by simp [s.2])⟩
  have hz : z = 0 := h (Subsingleton.elim (α := Cube.Term _ 2) _ _)
  exact (map_ne_zero_iff _ (awayFrac_injective (xProd_smul_injective {0}) 1)).2 one_ne_zero
    (congrArg Subtype.val (congrFun hz ⟨{0}, rfl⟩))

/- English proof (translation)
Rewrite using `[← HomologicalComplex.exactAt_iff_isZero_homology, grCech_eq, cechComplex_exactAt_succ_iff _ 0]`. Introduce `h`. Use `Cube.subsingleton_term (grCube (Fin 2) (polyGrading (Fin 2) ℤ) (-2)) (p := 3) (by simp)` as an intermediate fact. Set `z : homLoc (polyGrading (Fin 2) ℤ) ({0, 1} : Finset (Fin 2)) (-2)` to `⟨awayFrac _ _ 1 1, awayFrac_mem_homLoc (SetLike.one_mem_graded _) (by simp)⟩`. Take `⟨x, hx⟩` from `(h ((Cube.termTwoFinTwo (grCube (Fin 2) (polyGrading (Fin 2) ℤ) (-2))).symm z)).1 (Subsingleton.elim _ _)`.

Establish `e` using `Cube.d_one_finTwo _ x`. Rewrite `e` using `[hx]`. Use `replace e := (LinearEquiv.apply_symm_apply _ _).symm.trans e`. Take `⟨a, ha⟩` from `exists_awayFrac_of_mem_homLoc _ (Cube.termOneFinTwo _ x).1.2`. Take `⟨b, hb⟩` from `exists_awayFrac_of_mem_homLoc _ (Cube.termOneFinTwo _ x).2.2`.

Take `⟨p, -, hp⟩` from `ha (1 + (a + b)) (by omega)`. Take `⟨q, -, hq⟩` from `hb (1 + (a + b)) (by omega)`. Establish `e' : z.1 = locRes X _ (by decide) (Cube.termOneFinTwo _ x).2.1 - locRes X _ (by decide) (Cube.termOneFinTwo _ x).1.1` using `congrArg Subtype.val e`. Rewrite `e'` using `[← hp, ← hq, locRes_awayFrac X _ (c := X 0) (by simp), locRes_awayFrac X _ (c := X 1) (by simp [mul_comm]), ← map_sub]`. Establish `e''` using `congrArg (coeff (Finsupp.single 0 (a + b) + Finsupp.single 1 (a + b))) (awayFrac_injective (xProd_smul_injective _) _ ((awayFrac_add_pow_smul _ 1 (a + b) 1).trans e'))`.

Use `clear * - e''`. Generalize the expression as in `a + b = c at e''`. Rewrite `e''` using `[smul_eq_mul, smul_eq_mul, smul_eq_mul, coeff_sub, X_pow_eq_monomial, X_pow_eq_monomial, coeff_monomial_mul', coeff_monomial_mul', if_neg (by rw [Finsupp.single_le_iff]; simp), if_neg (by rw [Finsupp.single_le_iff]; simp)]`. Simplify using `[xProd, mul_pow, X_pow_eq_monomial] at e''`.
-/
example : ¬ Limits.IsZero (grH (Fin 2) (polyGrading (Fin 2) ℤ) (-2) 1) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, grCech_eq, cechComplex_exactAt_succ_iff _ 0]
  intro h
  have := Cube.subsingleton_term (grCube (Fin 2) (polyGrading (Fin 2) ℤ) (-2)) (p := 3) (by simp)
  let z : homLoc (polyGrading (Fin 2) ℤ) ({0, 1} : Finset (Fin 2)) (-2) :=
    ⟨awayFrac _ _ 1 1, awayFrac_mem_homLoc (SetLike.one_mem_graded _) (by simp)⟩
  obtain ⟨x, hx⟩ := (h ((Cube.termTwoFinTwo (grCube (Fin 2) (polyGrading (Fin 2) ℤ) (-2))).symm
    z)).1 (Subsingleton.elim _ _)
  have e := Cube.d_one_finTwo _ x
  rw [hx] at e
  replace e := (LinearEquiv.apply_symm_apply _ _).symm.trans e
  obtain ⟨a, ha⟩ := exists_awayFrac_of_mem_homLoc _ (Cube.termOneFinTwo _ x).1.2
  obtain ⟨b, hb⟩ := exists_awayFrac_of_mem_homLoc _ (Cube.termOneFinTwo _ x).2.2
  obtain ⟨p, -, hp⟩ := ha (1 + (a + b)) (by omega)
  obtain ⟨q, -, hq⟩ := hb (1 + (a + b)) (by omega)
  have e' : z.1 = locRes X _ (by decide) (Cube.termOneFinTwo _ x).2.1 -
      locRes X _ (by decide) (Cube.termOneFinTwo _ x).1.1 := congrArg Subtype.val e
  rw [← hp, ← hq, locRes_awayFrac X _ (c := X 0) (by simp),
    locRes_awayFrac X _ (c := X 1) (by simp [mul_comm]), ← map_sub] at e'
  have e'' := congrArg (coeff (Finsupp.single 0 (a + b) + Finsupp.single 1 (a + b)))
    (awayFrac_injective (xProd_smul_injective _) _
      ((awayFrac_add_pow_smul _ 1 (a + b) 1).trans e'))
  clear * - e''
  generalize a + b = c at e''
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, coeff_sub, X_pow_eq_monomial, X_pow_eq_monomial,
    coeff_monomial_mul', coeff_monomial_mul', if_neg (by rw [Finsupp.single_le_iff]; simp),
    if_neg (by rw [Finsupp.single_le_iff]; simp)] at e''
  simp [xProd, mul_pow, X_pow_eq_monomial] at e''

variable (ι R) in

/- English proof (translation)
Introduce `_ _ _ _` and use `rfl`.
-/
theorem operatorsCommute_id :
    OperatorsCommute (ι := ι) (R := R) (A := fun _ => R) fun _ _ => LinearMap.id :=
  fun _ _ _ _ => rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨inferInstance, ⟨inferInstance⟩, ⟨GrSum.pieceEquiv (operatorsCommute_id ι R) n⟩⟩`.
-/
example (n : ℤ) : PolyGradedSMul ι (GrSum.grading (operatorsCommute_id ι R)) ∧
    Nonempty (Decomposition (GrSum.grading (operatorsCommute_id ι R))) ∧
    Nonempty (R ≃ₗ[R] GrSum.grading (operatorsCommute_id ι R) n) :=
  ⟨inferInstance, ⟨inferInstance⟩, ⟨GrSum.pieceEquiv (operatorsCommute_id ι R) n⟩⟩

end Examples

end GlobalTheory
