import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PushComparisonBijectiveOfIsClosedEmbedding
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubsingletonOfSheafPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

universe v u

namespace GlobalTheory

section Chi

variable {X Y : Scheme.{u}} (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]

structure FiniteCoh (F : X.Modules) : Prop where

  finite : ∀ n, Module.Finite k (coh F n)

  eventually_zero : ∃ N, ∀ n, N ≤ n → Subsingleton (coh F n)

def chi (F : X.Modules) : ℤ := ∑ᶠ n, (-1 : ℤ) ^ n * hdim k F n

variable {F G : X.Modules}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chi_def (F : X.Modules) : chi k F = ∑ᶠ n, (-1 : ℤ) ^ n * hdim k F n := rfl

/- English proof (translation)
The claim follows from `finsum_neg_one_pow_hdim_eq_sum k F N hN`.
-/
theorem chi_eq_sum_range (N : ℕ) (hN : ∀ n, N ≤ n → Subsingleton (coh F n)) :
    chi k F = ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * hdim k F n :=
  finsum_neg_one_pow_hdim_eq_sum k F N hN

/- English proof (translation)
Rewrite using `[chi_eq_sum_range k 1 h]`. Simplify using the standard rewrite rules.
-/
theorem chi_eq_hdim_zero (h : ∀ n, 0 < n → Subsingleton (coh F n)) : chi k F = hdim k F 0 := by
  rw [chi_eq_sum_range k 1 h]; simp

/- English proof (translation)
Rewrite using `[chi_eq_sum_range k 2 h]`. Simplify using `[Finset.sum_range_succ, sub_eq_add_neg]`.
-/
theorem chi_eq_hdim_zero_sub_hdim_one (h : ∀ n, 2 ≤ n → Subsingleton (coh F n)) :
    chi k F = hdim k F 0 - hdim k F 1 := by
  rw [chi_eq_sum_range k 2 h]; simp [Finset.sum_range_succ, sub_eq_add_neg]

/- English proof (translation)
Rewrite using `[chi_eq_sum_range k 0 fun n _ ↦ h n]`. Simplify using the standard rewrite rules.
-/
theorem chi_eq_zero_of_subsingleton (h : ∀ n, Subsingleton (coh F n)) : chi k F = 0 := by
  rw [chi_eq_sum_range k 0 fun n _ ↦ h n]; simp

/- English proof (translation)
The claim follows from `chi_eq_zero_of_subsingleton k fun n ↦ cohOn.subsingleton_of_isZero h ⊤ n`.
-/
theorem chi_eq_zero_of_isZero (h : IsZero F) : chi k F = 0 :=
  chi_eq_zero_of_subsingleton k fun n ↦ cohOn.subsingleton_of_isZero h ⊤ n

/- English proof (translation)
The claim follows from `finsum_congr fun n ↦ by rw [hdim_congr k n e]`.
-/
theorem chi_congr (e : F ≅ G) : chi k F = chi k G :=
  finsum_congr fun n ↦ by rw [hdim_congr k n e]

/- English proof (translation)
The claim follows from `finsum_congr fun n ↦ by rw [hdim_def, hdim_def, (e n).finrank_eq]`.
-/
theorem chi_eq_of_linearEquiv [Algebra k Γ(Y, ⊤)] {H : Y.Modules}
    (e : ∀ n, coh F n ≃ₗ[k] coh H n) : chi k F = chi k H :=
  finsum_congr fun n ↦ by rw [hdim_def, hdim_def, (e n).finrank_eq]

variable {k}

namespace FiniteCoh

/- English proof (translation)
The claim follows from `have := h.finite n; Module.Finite.equiv (e n) eventually_zero := have ⟨N, hN⟩ := h.eventually_zero ⟨N, fun n hn ↦ have := hN n hn; (e n).symm.injective.subsingleton⟩`.
-/
theorem of_linearEquiv [Algebra k Γ(Y, ⊤)] {H : Y.Modules} (h : FiniteCoh k F)
    (e : ∀ n, coh F n ≃ₗ[k] coh H n) : FiniteCoh k H where
  finite n := have := h.finite n; Module.Finite.equiv (e n)
  eventually_zero :=
    have ⟨N, hN⟩ := h.eventually_zero
    ⟨N, fun n hn ↦ have := hN n hn; (e n).symm.injective.subsingleton⟩

/- English proof (translation)
The claim follows from `h.of_linearEquiv fun n ↦ cohOn.mapIso k ⊤ n e`.
-/
theorem of_iso (h : FiniteCoh k F) (e : F ≅ G) : FiniteCoh k G :=
  h.of_linearEquiv fun n ↦ cohOn.mapIso k ⊤ n e

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun n ↦ have := h n; inferInstance, 0, fun n _ ↦ h n⟩`.
-/
theorem of_subsingleton (h : ∀ n, Subsingleton (coh F n)) : FiniteCoh k F :=
  ⟨fun n ↦ have := h n; inferInstance, 0, fun n _ ↦ h n⟩

/- English proof (translation)
The claim follows from `of_subsingleton fun n ↦ cohOn.subsingleton_of_isZero h ⊤ n`.
-/
theorem of_isZero (h : IsZero F) : FiniteCoh k F :=
  of_subsingleton fun n ↦ cohOn.subsingleton_of_isZero h ⊤ n

/- English proof (translation)
The claim follows from `| 0 => h₀ | n + 1 => have := h (n + 1) n.succ_pos; inferInstance eventually_zero := ⟨1, h⟩`.
-/
theorem of_acyclic (h₀ : Module.Finite k (coh F 0)) (h : ∀ n, 0 < n → Subsingleton (coh F n)) :
    FiniteCoh k F where
  finite
    | 0 => h₀
    | n + 1 => have := h (n + 1) n.succ_pos; inferInstance
  eventually_zero := ⟨1, h⟩

/- English proof (translation)
Take `⟨N, hN⟩` from `h.eventually_zero`. Use `(Finset.range N).finite_toSet.subset fun n hn ↦ ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h'`. Use `hN n (by simpa using h')` as an intermediate fact. Conclude with `hn (by simp [hdim_eq_zero_of_subsingleton])`.
-/
theorem finite_support (h : FiniteCoh k F) :
    (Function.support fun n ↦ (-1 : ℤ) ^ n * hdim k F n).Finite := by
  obtain ⟨N, hN⟩ := h.eventually_zero
  refine (Finset.range N).finite_toSet.subset fun n hn ↦ ?_
  by_contra h'
  have := hN n (by simpa using h')
  exact hn (by simp [hdim_eq_zero_of_subsingleton])

variable {S : ShortComplex X.Modules}

/- English proof (translation)
The claim follows from `cohOn.forall_finite₂ k hS ⊤ h₁.finite h₃.finite eventually_zero := have ⟨N₁, h₁⟩ := h₁.eventually_zero have ⟨N₃, h₃⟩ := h₃.eventually_zero ⟨max N₁ N₃, fun n hn ↦ cohOn.subsingleton₂ hS ⊤ n (h₁ n (by omega)) (h₃ n (by omega))⟩`.
-/
theorem of_shortExact₂ (hS : S.ShortExact) (h₁ : FiniteCoh k S.X₁) (h₃ : FiniteCoh k S.X₃) :
    FiniteCoh k S.X₂ where
  finite := cohOn.forall_finite₂ k hS ⊤ h₁.finite h₃.finite
  eventually_zero :=
    have ⟨N₁, h₁⟩ := h₁.eventually_zero
    have ⟨N₃, h₃⟩ := h₃.eventually_zero
    ⟨max N₁ N₃, fun n hn ↦ cohOn.subsingleton₂ hS ⊤ n (h₁ n (by omega)) (h₃ n (by omega))⟩

/- English proof (translation)
The claim follows from `cohOn.forall_finite₃ k hS ⊤ h₁.finite h₂.finite eventually_zero := have ⟨N₁, h₁⟩ := h₁.eventually_zero have ⟨N₂, h₂⟩ := h₂.eventually_zero ⟨max N₁ N₂, fun n hn ↦ cohOn.subsingleton₃ hS ⊤ n (h₂ n (by omega)) (h₁ (n + 1) (by omega))⟩`.
-/
theorem of_shortExact₃ (hS : S.ShortExact) (h₁ : FiniteCoh k S.X₁) (h₂ : FiniteCoh k S.X₂) :
    FiniteCoh k S.X₃ where
  finite := cohOn.forall_finite₃ k hS ⊤ h₁.finite h₂.finite
  eventually_zero :=
    have ⟨N₁, h₁⟩ := h₁.eventually_zero
    have ⟨N₂, h₂⟩ := h₂.eventually_zero
    ⟨max N₁ N₂, fun n hn ↦ cohOn.subsingleton₃ hS ⊤ n (h₂ n (by omega)) (h₁ (n + 1) (by omega))⟩

/- English proof (translation)
The claim follows from `cohOn.forall_finite₁ k hS ⊤ h₂.finite h₃.finite eventually_zero := by obtain ⟨N₂, h₂⟩ := h₂.eventually_zero obtain ⟨N₃, h₃⟩ := h₃.eventually_zero refine ⟨max N₂ N₃ + 1, fun n hn ↦ ?_⟩ obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩ exact cohOn.subsingleton₁ hS ⊤ m (h₃ m (by …`.
-/
theorem of_shortExact₁ (hS : S.ShortExact) (h₂ : FiniteCoh k S.X₂) (h₃ : FiniteCoh k S.X₃) :
    FiniteCoh k S.X₁ where
  finite := cohOn.forall_finite₁ k hS ⊤ h₂.finite h₃.finite
  eventually_zero := by
    obtain ⟨N₂, h₂⟩ := h₂.eventually_zero
    obtain ⟨N₃, h₃⟩ := h₃.eventually_zero
    refine ⟨max N₂ N₃ + 1, fun n hn ↦ ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact cohOn.subsingleton₁ hS ⊤ m (h₃ m (by omega)) (h₂ (m + 1) (by omega))

/- English proof (translation)
The claim follows from `of_shortExact₂ (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact hF hG`.
-/
theorem biprod (hF : FiniteCoh k F) (hG : FiniteCoh k G) : FiniteCoh k (F ⊞ G) :=
  of_shortExact₂ (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact hF hG

end FiniteCoh

section ShortExact

variable {S : ShortComplex X.Modules}

/- English proof (translation)
The claim follows from `finsum_neg_one_pow_hdim_eq_add k hS h₁.finite h₃.finite h₁.eventually_zero h₃.eventually_zero`.
-/
theorem chi_shortExact (hS : S.ShortExact) (h₁ : FiniteCoh k S.X₁) (h₃ : FiniteCoh k S.X₃) :
    chi k S.X₂ = chi k S.X₁ + chi k S.X₃ :=
  finsum_neg_one_pow_hdim_eq_add k hS h₁.finite h₃.finite h₁.eventually_zero h₃.eventually_zero

/- English proof (translation)
Rewrite using `[chi_shortExact hS h₁ (h₁.of_shortExact₃ hS h₂)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chi_shortExact₃ (hS : S.ShortExact) (h₁ : FiniteCoh k S.X₁) (h₂ : FiniteCoh k S.X₂) :
    chi k S.X₃ = chi k S.X₂ - chi k S.X₁ := by
  rw [chi_shortExact hS h₁ (h₁.of_shortExact₃ hS h₂)]; ring

/- English proof (translation)
Rewrite using `[chi_shortExact hS (h₂.of_shortExact₁ hS h₃) h₃]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chi_shortExact₁ (hS : S.ShortExact) (h₂ : FiniteCoh k S.X₂) (h₃ : FiniteCoh k S.X₃) :
    chi k S.X₁ = chi k S.X₂ - chi k S.X₃ := by
  rw [chi_shortExact hS (h₂.of_shortExact₁ hS h₃) h₃]; ring

end ShortExact

/- English proof (translation)
The claim follows from `have := chi_shortExact (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact hF hG this`.
-/
theorem chi_biprod (hF : FiniteCoh k F) (hG : FiniteCoh k G) :
    chi k (F ⊞ G) = chi k F + chi k G :=
  have := chi_shortExact (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact hF hG
  this

section Pi

variable {ι : Type*} [Fintype ι] {E : ι → X.Modules}

/- English proof (translation)
Use `choose N hN using fun i ↦ (h i).eventually_zero`. Conclude with `⟨Finset.univ.sup N, fun i n hn ↦ hN i n ((Finset.le_sup (Finset.mem_univ i)).trans hn)⟩`.
-/
theorem exists_forall_subsingleton_coh (h : ∀ i, FiniteCoh k (E i)) :
    ∃ N, ∀ i n, N ≤ n → Subsingleton (coh (E i) n) := by
  choose N hN using fun i ↦ (h i).eventually_zero
  exact ⟨Finset.univ.sup N, fun i n hn ↦ hN i n ((Finset.le_sup (Finset.mem_univ i)).trans hn)⟩

/- English proof (translation)
The claim follows from `have := fun i ↦ (h i).finite n; cohOn.finite_pi k E ⊤ n eventually_zero := have ⟨N, hN⟩ := exists_forall_subsingleton_coh h ⟨N, fun n hn ↦ have := fun i ↦ hN i n hn; (cohOn.piEquiv k ⊤ n E).injective.subsingleton⟩`.
-/
theorem FiniteCoh.pi (h : ∀ i, FiniteCoh k (E i)) : FiniteCoh k (∏ᶜ E) where
  finite n := have := fun i ↦ (h i).finite n; cohOn.finite_pi k E ⊤ n
  eventually_zero :=
    have ⟨N, hN⟩ := exists_forall_subsingleton_coh h
    ⟨N, fun n hn ↦ have := fun i ↦ hN i n hn; (cohOn.piEquiv k ⊤ n E).injective.subsingleton⟩

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_forall_subsingleton_coh h`. Rewrite using `[chi_eq_sum_range k N fun n hn ↦`. Use `fun i ↦ hN i n hn` as an intermediate fact. Use the proof step `(cohOn.piEquiv k ⊤ n E).injective.subsingleton,`. Use the proof step `Finset.sum_congr rfl fun i _ ↦ chi_eq_sum_range k N (hN i), Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun n _ ↦ ?_` and prove the remaining obligations. Use `fun i ↦ (h i).finite n` as an intermediate fact. Rewrite using `[hdim_pi, Nat.cast_sum, Finset.mul_sum]`.
-/
theorem chi_pi (h : ∀ i, FiniteCoh k (E i)) : chi k (∏ᶜ E) = ∑ i, chi k (E i) := by
  obtain ⟨N, hN⟩ := exists_forall_subsingleton_coh h
  rw [chi_eq_sum_range k N fun n hn ↦
      have := fun i ↦ hN i n hn; (cohOn.piEquiv k ⊤ n E).injective.subsingleton,
    Finset.sum_congr rfl fun i _ ↦ chi_eq_sum_range k N (hN i), Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have := fun i ↦ (h i).finite n
  rw [hdim_pi, Nat.cast_sum, Finset.mul_sum]

end Pi

variable (k F) in

/- English proof (translation)
The claim follows from `have : Module.Finite Γ(X, ⊤) (coh F 0) := Module.Finite.equiv (coh.zeroEquiv F).symm .of_acyclic (Module.Finite.trans Γ(X, ⊤) _) fun _ hn ↦ coh.subsingleton_of_isAffine F hn`.
-/
theorem finiteCoh_of_isAffine_of_finite [IsAffine X] [Module.Finite k Γ(X, ⊤)]
    [QCoh.IsFiniteQC F] : FiniteCoh k F :=
  have : Module.Finite Γ(X, ⊤) (coh F 0) := Module.Finite.equiv (coh.zeroEquiv F).symm
  .of_acyclic (Module.Finite.trans Γ(X, ⊤) _) fun _ hn ↦ coh.subsingleton_of_isAffine F hn

variable (k X) in

/- English proof (translation)
Rewrite using `[chi_eq_hdim_zero k fun _ hn ↦ coh.subsingleton_of_isAffine _ hn, hdim_def, ((coh.zeroUnitEquiv X).restrictScalars k).finrank_eq]`.
-/
theorem chi_structureModule_of_isAffine [IsAffine X] :
    chi k (structureModule X) = Module.finrank k Γ(X, ⊤) := by
  rw [chi_eq_hdim_zero k fun _ hn ↦ coh.subsingleton_of_isAffine _ hn, hdim_def,
    ((coh.zeroUnitEquiv X).restrictScalars k).finrank_eq]

section Push

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] [Algebra R Γ(Y, ⊤)] (f : Y ⟶ X)

/- English proof (translation)
Use extensionality with `U x`. Express the relevant statement in the definitionally equal form `restrictGlobal Y (f ⁻¹ᵁ U) (f.appTop r) • (show Γ(H, f ⁻¹ᵁ U) from x) = f.app U (restrictGlobal X U r) • (show Γ(H, f ⁻¹ᵁ U) from x)`. Use `congr 1`. Conclude with `(ConcreteCategory.congr_hom (f.naturality (homOfLE le_top : U ⟶ ⊤).op) r).symm`.
-/
theorem pushforward_map_smulHom (H : Y.Modules) (r : Γ(X, ⊤)) :
    (Scheme.Modules.pushforward f).map (smulHom H (f.appTop r)) =
      smulHom ((Scheme.Modules.pushforward f).obj H) r := by
  ext U x
  change restrictGlobal Y (f ⁻¹ᵁ U) (f.appTop r) • (show Γ(H, f ⁻¹ᵁ U) from x) =
    f.app U (restrictGlobal X U r) • (show Γ(H, f ⁻¹ᵁ U) from x)
  congr 1
  exact (ConcreteCategory.congr_hom (f.naturality (homOfLE le_top : U ⟶ ⊤).op) r).symm

def pushH' (H : Y.Modules) (U : X.Opens) (n : ℕ) :
    Sheaf.H'.{u} ((toAbSheaf X).obj ((Scheme.Modules.pushforward f).obj H)) n U →+
      Sheaf.H'.{u} ((toAbSheaf Y).obj H) n (f ⁻¹ᵁ U) :=
  SheafPull.pushComparison.{u, u} f.base ((toAbSheaf Y).obj H) n U

/- English proof (translation)
The claim follows from `SheafPull.pushComparison_map.{u, u} f.base ((toAbSheaf Y).map φ) n U x`.
-/
theorem pushH'_map {H H' : Y.Modules} (φ : H ⟶ H') (U : X.Opens) (n : ℕ)
    (x : Sheaf.H'.{u} ((toAbSheaf X).obj ((Scheme.Modules.pushforward f).obj H)) n U) :
    pushH' f H' U n
        (SiteCoh.map ((toAbSheaf X).map ((Scheme.Modules.pushforward f).map φ)) n U x) =
      SiteCoh.map ((toAbSheaf Y).map φ) n (f ⁻¹ᵁ U) (pushH' f H U n x) :=
  SheafPull.pushComparison_map.{u, u} f.base ((toAbSheaf Y).map φ) n U x

def cohPushMap (hf : ∀ r : R, f.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r)
    (H : Y.Modules) (U : X.Opens) (n : ℕ) :
    cohOn ((Scheme.Modules.pushforward f).obj H) U n →ₗ[R] cohOn H (f ⁻¹ᵁ U) n where
  toFun x := (cohOn.toH' H _ n).symm (pushH' f H U n (cohOn.toH' _ U n x))
  map_add' x y := by simp only [map_add]
  map_smul' r x := by
    apply (cohOn.toH' H _ n).injective
    rw [RingHom.id_apply, cohOn.toH'_smul, cohOn.toH'_smul, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, ← pushforward_map_smulHom, hf, pushH'_map]

variable (hf : ∀ r : R, f.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r)

/- English proof (translation)
The claim follows from `have h : Function.Bijective (pushH' f H U n) := SheafPull.pushComparison_bijective_of_isClosedEmbedding.{u, u} f.isClosedEmbedding _ n U (cohOn.toH' H _ n).symm.bijective.comp (h.comp (cohOn.toH' _ U n).bijective)`.
-/
theorem cohPushMap_bijective_of_isClosedImmersion [IsClosedImmersion f] (H : Y.Modules)
    (U : X.Opens) (n : ℕ) : Function.Bijective (cohPushMap R f hf H U n) :=
  have h : Function.Bijective (pushH' f H U n) :=
    SheafPull.pushComparison_bijective_of_isClosedEmbedding.{u, u} f.isClosedEmbedding _ n U
  (cohOn.toH' H _ n).symm.bijective.comp (h.comp (cohOn.toH' _ U n).bijective)

/- English proof (translation)
The claim follows from `have h : Function.Bijective (pushH' f H U n) := SheafPull.pushComparison_bijective.{u, u} (SheafPull.higherDirectImagesVanish_of_basis f.base ((toAbSheaf Y).obj H) fun _ x hx ↦ have ⟨W, hW, hxW, hWV⟩ := QCoh.exists_affine_mem_le x hx ⟨W, hWV, hxW, fun _ hn ↦ cohOn.subsingleton_of …`.
-/
theorem cohPushMap_bijective_of_isAffineHom [IsAffineHom f] (H : Y.Modules) [H.IsQuasicoherent]
    (U : X.Opens) (n : ℕ) : Function.Bijective (cohPushMap R f hf H U n) :=
  have h : Function.Bijective (pushH' f H U n) :=
    SheafPull.pushComparison_bijective.{u, u}
      (SheafPull.higherDirectImagesVanish_of_basis f.base ((toAbSheaf Y).obj H) fun _ x hx ↦
        have ⟨W, hW, hxW, hWV⟩ := QCoh.exists_affine_mem_le x hx
        ⟨W, hWV, hxW, fun _ hn ↦ cohOn.subsingleton_of_isAffineOpen H (hW.preimage f) hn⟩) n U
  (cohOn.toH' H _ n).symm.bijective.comp (h.comp (cohOn.toH' _ U n).bijective)

end Push

section PushField

variable [Algebra k Γ(Y, ⊤)] {f : Y ⟶ X}
  (hf : ∀ r : k, f.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Y, ⊤) r) {H : Y.Modules}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h' ↦ h'.of_linearEquiv fun n ↦ .ofBijective _ (h n), fun h' ↦ h'.of_linearEquiv fun n ↦ (LinearEquiv.ofBijective _ (h n)).symm⟩`.
-/
theorem finiteCoh_pushforward_iff_of_bijective
    (h : ∀ n, Function.Bijective (cohPushMap k f hf H ⊤ n)) :
    FiniteCoh k ((Scheme.Modules.pushforward f).obj H) ↔ FiniteCoh k H :=
  ⟨fun h' ↦ h'.of_linearEquiv fun n ↦ .ofBijective _ (h n),
    fun h' ↦ h'.of_linearEquiv fun n ↦ (LinearEquiv.ofBijective _ (h n)).symm⟩

/- English proof (translation)
The claim follows from `chi_eq_of_linearEquiv k fun n ↦ .ofBijective _ (h n)`.
-/
theorem chi_pushforward_of_bijective (h : ∀ n, Function.Bijective (cohPushMap k f hf H ⊤ n)) :
    chi k ((Scheme.Modules.pushforward f).obj H) = chi k H :=
  chi_eq_of_linearEquiv k fun n ↦ .ofBijective _ (h n)

include hf

variable (H)

/- English proof (translation)
The claim follows from `finiteCoh_pushforward_iff_of_bijective hf (cohPushMap_bijective_of_isClosedImmersion k f hf H ⊤)`.
-/
theorem finiteCoh_pushforward_iff_of_isClosedImmersion [IsClosedImmersion f] :
    FiniteCoh k ((Scheme.Modules.pushforward f).obj H) ↔ FiniteCoh k H :=
  finiteCoh_pushforward_iff_of_bijective hf (cohPushMap_bijective_of_isClosedImmersion k f hf H ⊤)

/- English proof (translation)
The claim follows from `chi_pushforward_of_bijective hf (cohPushMap_bijective_of_isClosedImmersion k f hf H ⊤)`.
-/
theorem chi_pushforward_of_isClosedImmersion [IsClosedImmersion f] :
    chi k ((Scheme.Modules.pushforward f).obj H) = chi k H :=
  chi_pushforward_of_bijective hf (cohPushMap_bijective_of_isClosedImmersion k f hf H ⊤)

/- English proof (translation)
The claim follows from `finiteCoh_pushforward_iff_of_bijective hf (cohPushMap_bijective_of_isAffineHom k f hf H ⊤)`.
-/
theorem finiteCoh_pushforward_iff_of_isAffineHom [IsAffineHom f] [H.IsQuasicoherent] :
    FiniteCoh k ((Scheme.Modules.pushforward f).obj H) ↔ FiniteCoh k H :=
  finiteCoh_pushforward_iff_of_bijective hf (cohPushMap_bijective_of_isAffineHom k f hf H ⊤)

/- English proof (translation)
The claim follows from `chi_pushforward_of_bijective hf (cohPushMap_bijective_of_isAffineHom k f hf H ⊤)`.
-/
theorem chi_pushforward_of_isAffineHom [IsAffineHom f] [H.IsQuasicoherent] :
    chi k ((Scheme.Modules.pushforward f).obj H) = chi k H :=
  chi_pushforward_of_bijective hf (cohPushMap_bijective_of_isAffineHom k f hf H ⊤)

end PushField

abbrev algebraΓAlong (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] (f : Y ⟶ X) :
    Algebra R Γ(Y, ⊤) :=
  (f.appTop.hom.comp (algebraMap R Γ(X, ⊤))).toAlgebra

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem appTop_algebraMap_along (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] (f : Y ⟶ X) (r : R) :
    letI := algebraΓAlong R f
    f.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r := rfl

def unitToPush (f : Y ⟶ X) :
    structureModule X ⟶ (Scheme.Modules.pushforward f).obj (structureModule Y) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/- English proof (translation)
The claim follows from `Scheme.Modules.Hom.isIso_iff_isIso_app.2 fun U ↦ (ConcreteCategory.isIso_iff_bijective _).2 (h U)`.
-/
theorem isIso_unitToPush (f : Y ⟶ X) (h : ∀ U, Function.Bijective (f.app U)) :
    IsIso (unitToPush f) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.2 fun U ↦
    (ConcreteCategory.isIso_iff_bijective _).2 (h U)

instance isIso_unitToPush_of_isIso (f : Y ⟶ X) [IsIso f] : IsIso (unitToPush f) :=
  isIso_unitToPush f fun U ↦ ConcreteCategory.bijective_of_isIso (f.app U)

end Chi

section Prod

open CechPic

variable {X Y : Scheme.{0}} {ι : Type} [Fintype ι]

def prodChart (L : ι → LB X) (j : ∀ i, (L i).ι) : X.Opens :=
  Finset.univ.inf fun i ↦ (L i).U (j i)

/- English proof (translation)
The claim follows from `Finset.inf_le (f := fun i ↦ (L i).U (j i)) (Finset.mem_univ i)`.
-/
theorem prodChart_le (L : ι → LB X) (j : ∀ i, (L i).ι) (i : ι) : prodChart L j ≤ (L i).U (j i) :=
  Finset.inf_le (f := fun i ↦ (L i).U (j i)) (Finset.mem_univ i)

/- English proof (translation)
Rewrite using `[← SetLike.mem_coe, prodChart, Opens.coe_finset_inf]`. Simplify using the standard rewrite rules.
-/
theorem mem_prodChart {L : ι → LB X} {j : ∀ i, (L i).ι} {x : X} :
    x ∈ prodChart L j ↔ ∀ i, x ∈ (L i).U (j i) := by
  rw [← SetLike.mem_coe, prodChart, Opens.coe_finset_inf]
  simp

def lbProd (L : ι → LB X) (n : ι → ℤ) : LB X where
  ι := ∀ i, (L i).ι
  U := prodChart L
  g j j' := ∏ i, res (inf_le_inf (prodChart_le L j i) (prodChart_le L j' i))
    ((L i).g (j i) (j' i)) ^ n i

open scoped Classical in

def lbInvProd (L : ι → LB X) (S : Finset ι) : LB X :=
  lbProd L fun i ↦ if i ∈ S then -1 else 0

/- English proof (translation)
The claim follows from `(map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ ↦ (map_zpow _ _ _).trans (congrArg (· ^ n i) (Semi.LB.res_res _ _ _)))`.
-/
theorem res_lbProd_g (L : ι → LB X) (n : ι → ℤ) (j j' : ∀ i, (L i).ι) {W : X.Opens}
    (h : W ≤ prodChart L j ⊓ prodChart L j') :
    res h ((lbProd L n).g j j') =
      ∏ i, res (h.trans (inf_le_inf (prodChart_le L j i) (prodChart_le L j' i)))
        ((L i).g (j i) (j' i)) ^ n i :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ ↦
    (map_zpow _ _ _).trans (congrArg (· ^ n i) (Semi.LB.res_res _ _ _)))

/- English proof (translation)
The claim follows from `(map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ ↦ (map_zpow _ _ _).trans (congrArg (· ^ n i) (gm_res r y _ (show r y ∈ prodChart L j ⊓ prodChart L j' from ⟨hj, hj'⟩) _)))`.
-/
theorem gm_lbProd_g (L : ι → LB X) (n : ι → ℤ) (r : Y ⟶ X) (y : Y) (j j' : ∀ i, (L i).ι)
    (hj : r y ∈ prodChart L j) (hj' : r y ∈ prodChart L j') :
    gm r y (prodChart L j ⊓ prodChart L j') ((lbProd L n).g j j') =
      ∏ i, gm r y _ ((L i).g (j i) (j' i)) ^ n i :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ ↦ (map_zpow _ _ _).trans
    (congrArg (· ^ n i) (gm_res r y _ (show r y ∈ prodChart L j ⊓ prodChart L j' from ⟨hj, hj'⟩) _)))

variable {L : ι → LB X}

/- English proof (translation)
The claim follows from `top_le_iff.1 fun x _ ↦ by choose j hj using fun i ↦ Semi.LB.mem_of_cover (hL i) x exact Opens.mem_iSup.2 ⟨j, mem_prodChart.2 hj⟩ g_self j := (res_lbProd_g L n j j _).trans (Finset.prod_eq_one fun i _ ↦ by rw [Semi.LB.res_g_self (hL i), one_zpow]) cocycle j j' j'' := by refine (co …`.
-/
theorem isLB_lbProd (hL : ∀ i, (L i).IsLB) (n : ι → ℤ) : (lbProd L n).IsLB where
  cover := top_le_iff.1 fun x _ ↦ by
    choose j hj using fun i ↦ Semi.LB.mem_of_cover (hL i) x
    exact Opens.mem_iSup.2 ⟨j, mem_prodChart.2 hj⟩
  g_self j := (res_lbProd_g L n j j _).trans (Finset.prod_eq_one fun i _ ↦ by
    rw [Semi.LB.res_g_self (hL i), one_zpow])
  cocycle j j' j'' := by
    refine (congrArg₂ (· * ·) (res_lbProd_g L n j j' _) (res_lbProd_g L n j' j'' _)).trans
      (Eq.trans ?_ (res_lbProd_g L n j j'' _).symm)
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ by rw [← mul_zpow, Semi.LB.res_cocycle (hL i)]

/- English proof (translation)
The claim follows from `isLB_lbProd hL _`.
-/
theorem isLB_lbInvProd (hL : ∀ i, (L i).IsLB) (S : Finset ι) : (lbInvProd L S).IsLB :=
  isLB_lbProd hL _

/- English proof (translation)
Establish `h` using `isLB_tens (isLB_lbProd hL n) (isLB_lbProd hL m)`. Use `(cls_eq_iff _ h).2 (iso_of_chart h ⟨fun j ↦ (j, j), fun _ _ h ↦ ⟨h, h⟩, ?_⟩)` and prove the remaining obligations. Introduce `y p q hp hq`. Use `(gm_lbProd_g L (n + m) (𝟙 X) y p q hp hq).trans (Eq.symm ((gm_tens (lbProd L n) (lbProd L m) (𝟙 X) y (p, p) (q, q) ⟨hp, hp⟩ ⟨hq, hq⟩).trans ((congrArg₂ (· * ·) (gm_lbProd_g L n (𝟙 X) y p q hp hq) (gm_lbProd_g L m (𝟙 X) y p q hp hq)).trans ?_)))` and prove the remaining obligations. Simplify using `only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib]`.
-/
theorem cls_lbProd_add (hL : ∀ i, (L i).IsLB) (n m : ι → ℤ) :
    cls _ (isLB_lbProd hL (n + m)) = cls _ (isLB_lbProd hL n) + cls _ (isLB_lbProd hL m) := by
  have h := isLB_tens (isLB_lbProd hL n) (isLB_lbProd hL m)
  refine (cls_eq_iff _ h).2 (iso_of_chart h ⟨fun j ↦ (j, j), fun _ _ h ↦ ⟨h, h⟩, ?_⟩)
  intro y p q hp hq
  refine (gm_lbProd_g L (n + m) (𝟙 X) y p q hp hq).trans (Eq.symm
    ((gm_tens (lbProd L n) (lbProd L m) (𝟙 X) y (p, p) (q, q) ⟨hp, hp⟩ ⟨hq, hq⟩).trans
      ((congrArg₂ (· * ·) (gm_lbProd_g L n (𝟙 X) y p q hp hq)
        (gm_lbProd_g L m (𝟙 X) y p q hp hq)).trans ?_)))
  simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

/- English proof (translation)
Use `(cls_eq_iff _ (hL i)).2 (iso_of_chart (hL i) ⟨fun j ↦ j i, fun j ↦ prodChart_le L j i, ?_⟩)` and prove the remaining obligations. Introduce `y p q hp hq`. Use `(gm_lbProd_g L _ (𝟙 X) y p q hp hq).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single i (fun b _ hb ↦ by rw [Pi.single_eq_of_ne hb, zpow_zero]) (by simp), Pi.single_eq_same, zpow_one]`.
-/
theorem cls_lbProd_single [DecidableEq ι] (hL : ∀ i, (L i).IsLB) (i : ι) :
    cls _ (isLB_lbProd hL (Pi.single i 1)) = cls (L i) (hL i) := by
  refine (cls_eq_iff _ (hL i)).2 (iso_of_chart (hL i)
    ⟨fun j ↦ j i, fun j ↦ prodChart_le L j i, ?_⟩)
  intro y p q hp hq
  refine (gm_lbProd_g L _ (𝟙 X) y p q hp hq).trans ?_
  rw [Finset.prod_eq_single i (fun b _ hb ↦ by rw [Pi.single_eq_of_ne hb, zpow_zero]) (by simp),
    Pi.single_eq_same, zpow_one]

/- English proof (translation)
Set `c : (ι → ℤ) →+ Pic X` to `AddMonoidHom.mk' (fun n ↦ cls _ (isLB_lbProd hL n)) (cls_lbProd_add hL)`. Establish `e : n = ∑ i, n i • (Pi.single i 1 : ι → ℤ)`. Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Express the relevant statement in the definitionally equal form `c n = _`.

Rewrite using `[e, map_sum]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, ← e]`. Conclude with `congrArg _ (cls_lbProd_single hL i)`.
-/
theorem cls_lbProd (hL : ∀ i, (L i).IsLB) (n : ι → ℤ) (h : (lbProd L n).IsLB) :
    cls _ h = ∑ i, n i • cls (L i) (hL i) := by
  classical
  let c : (ι → ℤ) →+ Pic X :=
    AddMonoidHom.mk' (fun n ↦ cls _ (isLB_lbProd hL n)) (cls_lbProd_add hL)
  have e : n = ∑ i, n i • (Pi.single i 1 : ι → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  change c n = _
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul, ← e]
  exact congrArg _ (cls_lbProd_single hL i)

/- English proof (translation)
Use `(cls_lbProd hL _ h).trans ?_` and prove the remaining obligations. Simplify using `[Finset.sum_ite_mem]`.
-/
theorem cls_lbInvProd (hL : ∀ i, (L i).IsLB) (S : Finset ι) (h : (lbInvProd L S).IsLB) :
    cls _ h = -∑ i ∈ S, cls (L i) (hL i) := by
  classical
  refine (cls_lbProd hL _ h).trans ?_
  simp [Finset.sum_ite_mem]

/- English proof (translation)
Rewrite using `[cls_linComb hM, Fintype.sum_unique, pull_id]`.
-/
theorem cls_lbZPow {M : LB X} (hM : M.IsLB) (n : ℤ) (h : (lbZPow M n).IsLB) :
    cls _ h = n • cls M hM := by
  rw [cls_linComb hM, Fintype.sum_unique, pull_id]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cls_triv (h : (LB.triv X).IsLB) : cls _ h = 0 := rfl

/- English proof (translation)
The claim follows from `Twist.nonempty_iso_of_lbIso hM hN ((cls_eq_iff hM hN).1 h)`.
-/
theorem nonempty_twist_iso_of_cls_eq (F : X.Modules) {M N : LB X} (hM : M.IsLB) (hN : N.IsLB)
    (h : cls M hM = cls N hN) : Nonempty (twist F M ≅ twist F N) :=
  Twist.nonempty_iso_of_lbIso hM hN ((cls_eq_iff hM hN).1 h)

/- English proof (translation)
The claim follows from `Twist.nonempty_twistTwistIso hM hN hP ((cls_eq_iff hN (Semi.LB.isLB_div hP hM)).1 (by rw [cls_div hP hM, h, add_sub_cancel_left]))`.
-/
theorem nonempty_twist_twist_iso_of_cls_eq (F : X.Modules) {M N P : LB X} (hM : M.IsLB)
    (hN : N.IsLB) (hP : P.IsLB) (h : cls P hP = cls M hM + cls N hN) :
    Nonempty (twist (twist F M) N ≅ twist F P) :=
  Twist.nonempty_twistTwistIso hM hN hP ((cls_eq_iff hN (Semi.LB.isLB_div hP hM)).1
    (by rw [cls_div hP hM, h, add_sub_cancel_left]))

/- English proof (translation)
The claim follows from `have ⟨t, ht⟩ := (cls_eq_zero_iff hM).1 h ⟨(Twist.genIso F hM t ht).symm⟩`.
-/
theorem nonempty_twist_iso_of_cls_eq_zero (F : X.Modules) {M : LB X} (hM : M.IsLB)
    (h : cls M hM = 0) : Nonempty (twist F M ≅ F) :=
  have ⟨t, ht⟩ := (cls_eq_zero_iff hM).1 h
  ⟨(Twist.genIso F hM t ht).symm⟩

end Prod

section Twists

open CechPic

variable {X Y : Scheme.{0}} (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]

def FiniteCohTwists (F : X.Modules) : Prop := ∀ M : LB X, M.IsLB → FiniteCoh k (twist F M)

def chiPic (F : X.Modules) : Pic X → ℤ :=
  Quotient.lift (fun M ↦ chi k (twist F M.1)) fun M N h ↦
    (Twist.nonempty_iso_of_lbIso M.2 N.2 h).elim (chi_congr k)

variable {F G : X.Modules} {M N : LB X}

variable (F) in

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem chiPic_cls (hM : M.IsLB) : chiPic k F (cls M hM) = chi k (twist F M) := rfl

variable (F) in

/- English proof (translation)
The claim follows from `(chi_congr k (Twist.trivIso F)).symm`.
-/
@[simp] theorem chiPic_zero : chiPic k F 0 = chi k F := (chi_congr k (Twist.trivIso F)).symm

/- English proof (translation)
Use function extensionality and compare the values at `c`. Take `⟨M, hM, rfl⟩` from `cls_surj c`. Conclude with `chi_congr k ((twistFunctor M).mapIso e)`.
-/
theorem chiPic_congr (e : F ≅ G) : chiPic k F = chiPic k G := by
  funext c
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  exact chi_congr k ((twistFunctor M).mapIso e)

variable (F) in

/- English proof (translation)
Take `⟨N, hN, rfl⟩` from `cls_surj c`. Conclude with `(nonempty_twist_twist_iso_of_cls_eq F hM hN (isLB_tens hM hN) rfl).elim (chi_congr k)`.
-/
theorem chiPic_twist (hM : M.IsLB) (c : Pic X) :
    chiPic k (twist F M) c = chiPic k F (cls M hM + c) := by
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  exact (nonempty_twist_twist_iso_of_cls_eq F hM hN (isLB_tens hM hN) rfl).elim (chi_congr k)

variable (F) in

/- English proof (translation)
Rewrite using `[← cls_lbZPow hM n (Twist.isLB_lbZPow hM n), chiPic_cls]`.
-/
theorem chi_twistZ (hM : M.IsLB) (n : ℤ) : chi k (twistZ F M n) = chiPic k F (n • cls M hM) := by
  rw [← cls_lbZPow hM n (Twist.isLB_lbZPow hM n), chiPic_cls]

variable {k}

namespace FiniteCohTwists

/- English proof (translation)
The claim follows from `(h _ (LB.isLB_triv X)).of_iso (Twist.trivIso F).symm`.
-/
theorem finiteCoh (h : FiniteCohTwists k F) : FiniteCoh k F :=
  (h _ (LB.isLB_triv X)).of_iso (Twist.trivIso F).symm

/- English proof (translation)
The claim follows from `fun M hM ↦ (h M hM).of_iso ((twistFunctor M).mapIso e)`.
-/
theorem of_iso (h : FiniteCohTwists k F) (e : F ≅ G) : FiniteCohTwists k G :=
  fun M hM ↦ (h M hM).of_iso ((twistFunctor M).mapIso e)

/- English proof (translation)
The claim follows from `fun N hN ↦ (nonempty_twist_twist_iso_of_cls_eq F hM hN (isLB_tens hM hN) rfl).elim fun e ↦ (h _ (isLB_tens hM hN)).of_iso e.symm`.
-/
theorem twist (h : FiniteCohTwists k F) (hM : M.IsLB) : FiniteCohTwists k (twist F M) :=
  fun N hN ↦ (nonempty_twist_twist_iso_of_cls_eq F hM hN (isLB_tens hM hN) rfl).elim
    fun e ↦ (h _ (isLB_tens hM hN)).of_iso e.symm

/- English proof (translation)
The claim follows from `fun _ hM ↦ .of_isZero ((Twist.isZero_twist_iff hM).2 h)`.
-/
theorem of_isZero (h : IsZero F) : FiniteCohTwists k F :=
  fun _ hM ↦ .of_isZero ((Twist.isZero_twist_iff hM).2 h)

variable {S : ShortComplex X.Modules}

/- English proof (translation)
The claim follows from `fun M hM ↦ FiniteCoh.of_shortExact₂ (Twist.shortExact_map hM hS) (h₁ M hM) (h₃ M hM)`.
-/
theorem of_shortExact₂ (hS : S.ShortExact) (h₁ : FiniteCohTwists k S.X₁)
    (h₃ : FiniteCohTwists k S.X₃) : FiniteCohTwists k S.X₂ :=
  fun M hM ↦ FiniteCoh.of_shortExact₂ (Twist.shortExact_map hM hS) (h₁ M hM) (h₃ M hM)

/- English proof (translation)
The claim follows from `fun M hM ↦ FiniteCoh.of_shortExact₃ (Twist.shortExact_map hM hS) (h₁ M hM) (h₂ M hM)`.
-/
theorem of_shortExact₃ (hS : S.ShortExact) (h₁ : FiniteCohTwists k S.X₁)
    (h₂ : FiniteCohTwists k S.X₂) : FiniteCohTwists k S.X₃ :=
  fun M hM ↦ FiniteCoh.of_shortExact₃ (Twist.shortExact_map hM hS) (h₁ M hM) (h₂ M hM)

/- English proof (translation)
The claim follows from `fun M hM ↦ FiniteCoh.of_shortExact₁ (Twist.shortExact_map hM hS) (h₂ M hM) (h₃ M hM)`.
-/
theorem of_shortExact₁ (hS : S.ShortExact) (h₂ : FiniteCohTwists k S.X₂)
    (h₃ : FiniteCohTwists k S.X₃) : FiniteCohTwists k S.X₁ :=
  fun M hM ↦ FiniteCoh.of_shortExact₁ (Twist.shortExact_map hM hS) (h₂ M hM) (h₃ M hM)

end FiniteCohTwists

variable (k F) in

/- English proof (translation)
The claim follows from `fun _ hM ↦ have := Twist.isFiniteQC_twist (F := F) hM finiteCoh_of_isAffine_of_finite k _`.
-/
theorem finiteCohTwists_of_isAffine_of_finite [IsAffine X] [Module.Finite k Γ(X, ⊤)]
    [QCoh.IsFiniteQC F] : FiniteCohTwists k F := fun _ hM ↦
  have := Twist.isFiniteQC_twist (F := F) hM
  finiteCoh_of_isAffine_of_finite k _

/- English proof (translation)
The claim follows from `have := chi_shortExact (Twist.shortExact_map hM hS) h₁ h₃ this`.
-/
theorem chi_twist_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) (hM : M.IsLB)
    (h₁ : FiniteCoh k (twist S.X₁ M)) (h₃ : FiniteCoh k (twist S.X₃ M)) :
    chi k (twist S.X₂ M) = chi k (twist S.X₁ M) + chi k (twist S.X₃ M) :=
  have := chi_shortExact (Twist.shortExact_map hM hS) h₁ h₃
  this

/- English proof (translation)
Use function extensionality and compare the values at `c`. Take `⟨M, hM, rfl⟩` from `cls_surj c`. Conclude with `chi_twist_shortExact hS hM (h₁ M hM) (h₃ M hM)`.
-/
theorem chiPic_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : FiniteCohTwists k S.X₁) (h₃ : FiniteCohTwists k S.X₃) :
    chiPic k S.X₂ = chiPic k S.X₁ + chiPic k S.X₃ := by
  funext c
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  exact chi_twist_shortExact hS hM (h₁ M hM) (h₃ M hM)

section Push

variable [Algebra k Γ(Y, ⊤)] {f : Y ⟶ X}
  (hf : ∀ r : k, f.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Y, ⊤) r) (H : Y.Modules)

include hf

/- English proof (translation)
The claim follows from `(chi_congr k (Twist.projIso M f H)).symm.trans (chi_pushforward_of_isClosedImmersion hf _)`.
-/
theorem chi_twist_pushforward_of_isClosedImmersion [IsClosedImmersion f] (M : LB X) :
    chi k (twist ((Scheme.Modules.pushforward f).obj H) M) = chi k (twist H (M.pull f)) :=
  (chi_congr k (Twist.projIso M f H)).symm.trans (chi_pushforward_of_isClosedImmersion hf _)

/- English proof (translation)
The claim follows from `have := Twist.isQuasicoherent_twist (F := H) (pull_isLB hM f) (chi_congr k (Twist.projIso M f H)).symm.trans (chi_pushforward_of_isAffineHom hf _)`.
-/
theorem chi_twist_pushforward_of_isAffineHom [IsAffineHom f] [H.IsQuasicoherent] (hM : M.IsLB) :
    chi k (twist ((Scheme.Modules.pushforward f).obj H) M) = chi k (twist H (M.pull f)) :=
  have := Twist.isQuasicoherent_twist (F := H) (pull_isLB hM f)
  (chi_congr k (Twist.projIso M f H)).symm.trans (chi_pushforward_of_isAffineHom hf _)

/- English proof (translation)
Use function extensionality and compare the values at `c`. Take `⟨M, hM, rfl⟩` from `cls_surj c`. Conclude with `chi_twist_pushforward_of_isClosedImmersion hf H M`.
-/
theorem chiPic_pushforward_of_isClosedImmersion [IsClosedImmersion f] :
    chiPic k ((Scheme.Modules.pushforward f).obj H) = chiPic k H ∘ pull f := by
  funext c
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  exact chi_twist_pushforward_of_isClosedImmersion hf H M

/- English proof (translation)
Use function extensionality and compare the values at `c`. Take `⟨M, hM, rfl⟩` from `cls_surj c`. Conclude with `chi_twist_pushforward_of_isAffineHom hf H hM`.
-/
theorem chiPic_pushforward_of_isAffineHom [IsAffineHom f] [H.IsQuasicoherent] :
    chiPic k ((Scheme.Modules.pushforward f).obj H) = chiPic k H ∘ pull f := by
  funext c
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  exact chi_twist_pushforward_of_isAffineHom hf H hM

variable {H}

/- English proof (translation)
The claim follows from `fun M hM ↦ ((finiteCoh_pushforward_iff_of_isClosedImmersion hf _).2 (h _ (pull_isLB hM f))).of_iso (Twist.projIso M f H)`.
-/
theorem FiniteCohTwists.pushforward_of_isClosedImmersion [IsClosedImmersion f]
    (h : FiniteCohTwists k H) : FiniteCohTwists k ((Scheme.Modules.pushforward f).obj H) :=
  fun M hM ↦ ((finiteCoh_pushforward_iff_of_isClosedImmersion hf _).2
    (h _ (pull_isLB hM f))).of_iso (Twist.projIso M f H)

/- English proof (translation)
The claim follows from `fun M hM ↦ have := Twist.isQuasicoherent_twist (F := H) (pull_isLB hM f) ((finiteCoh_pushforward_iff_of_isAffineHom hf _).2 (h _ (pull_isLB hM f))).of_iso (Twist.projIso M f H)`.
-/
theorem FiniteCohTwists.pushforward_of_isAffineHom [IsAffineHom f] [H.IsQuasicoherent]
    (h : FiniteCohTwists k H) : FiniteCohTwists k ((Scheme.Modules.pushforward f).obj H) :=
  fun M hM ↦
    have := Twist.isQuasicoherent_twist (F := H) (pull_isLB hM f)
    ((finiteCoh_pushforward_iff_of_isAffineHom hf _).2
      (h _ (pull_isLB hM f))).of_iso (Twist.projIso M f H)

end Push

end Twists

section Inter

open CechPic

variable {X Y Z : Scheme.{0}} (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]
  {ι κ : Type} [Fintype ι] [Fintype κ]

def interNum (F : X.Modules) (L : ι → LB X) : ℤ :=
  ∑ S : Finset ι, (-1 : ℤ) ^ S.card * chi k (twist F (lbInvProd L S))

def interNumOn (f : Z ⟶ X) (L : ι → LB X) : ℤ :=
  interNum k ((Scheme.Modules.pushforward f).obj (structureModule Z)) L

def interNumSub (I : X.IdealSheafData) (L : ι → LB X) : ℤ := interNumOn k I.subschemeι L

def interNumRed (Z : Closeds X) (L : ι → LB X) : ℤ :=
  interNumSub k (Scheme.IdealSheafData.vanishingIdeal Z) L

def topSelfIntersection (M : LB X) (d : ℕ) : ℤ := interNum k (structureModule X) fun _ : Fin d ↦ M

variable {F G : X.Modules} {L L' : ι → LB X} {M N A B : LB X}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem interNum_def (F : X.Modules) (L : ι → LB X) :
    interNum k F L = ∑ S : Finset ι, (-1 : ℤ) ^ S.card * chi k (twist F (lbInvProd L S)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem interNumOn_def (f : Z ⟶ X) (L : ι → LB X) :
    interNumOn k f L = interNum k ((Scheme.Modules.pushforward f).obj (structureModule Z)) L := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem interNumSub_def (I : X.IdealSheafData) (L : ι → LB X) :
    interNumSub k I L = interNumOn k I.subschemeι L := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem interNumRed_def (Z : Closeds X) (L : ι → LB X) :
    interNumRed k Z L = interNumSub k (Scheme.IdealSheafData.vanishingIdeal Z) L := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem topSelf_def (M : LB X) (d : ℕ) :
    topSelfIntersection k M d = interNum k (structureModule X) fun _ : Fin d ↦ M := rfl

variable (F) in

/- English proof (translation)
The claim follows from `Finset.sum_congr rfl fun S _ ↦ by rw [zero_sub, ← cls_lbInvProd hL S (isLB_lbInvProd hL S), chiPic_cls, smul_eq_mul]`.
-/
theorem interNum_eq_multiDiff (hL : ∀ i, (L i).IsLB) :
    interNum k F L = multiDiff (fun i ↦ cls (L i) (hL i)) (chiPic k F) 0 :=
  Finset.sum_congr rfl fun S _ ↦ by
    rw [zero_sub, ← cls_lbInvProd hL S (isLB_lbInvProd hL S), chiPic_cls, smul_eq_mul]

variable (F) in

/- English proof (translation)
Rewrite using `[interNum_eq_multiDiff k _ hL, funext (chiPic_twist k F hM), multiDiff_translate, add_zero]`.
-/
theorem interNum_twist_eq_multiDiff (hL : ∀ i, (L i).IsLB) (hM : M.IsLB) :
    interNum k (twist F M) L = multiDiff (fun i ↦ cls (L i) (hL i)) (chiPic k F) (cls M hM) := by
  rw [interNum_eq_multiDiff k _ hL, funext (chiPic_twist k F hM), multiDiff_translate, add_zero]

variable (F) in

/- English proof (translation)
Establish `e` using `congrFun (multiDiff_comap (zmultiplesHom _ (cls M hM)) a (chiPic k F)) 0`. Rewrite `e` using `[Function.comp_apply, map_zero]`. Rewrite using `[interNum_eq_multiDiff k F fun i ↦ Twist.isLB_lbZPow hM (a i), funext (chi_twistZ k F hM),`. Use function extensionality and compare the values at `fun i ↦ cls_lbZPow hM (a i) (Twist.isLB_lbZPow hM (a i))]`. Conclude with `e.symm`.
-/
theorem interNum_lbZPow_eq_multiDiff (hM : M.IsLB) (a : ι → ℤ) :
    interNum k F (fun i ↦ lbZPow M (a i)) = multiDiff a (fun n ↦ chi k (twistZ F M n)) 0 := by
  have e := congrFun (multiDiff_comap (zmultiplesHom _ (cls M hM)) a (chiPic k F)) 0
  rw [Function.comp_apply, map_zero] at e
  rw [interNum_eq_multiDiff k F fun i ↦ Twist.isLB_lbZPow hM (a i), funext (chi_twistZ k F hM),
    funext fun i ↦ cls_lbZPow hM (a i) (Twist.isLB_lbZPow hM (a i))]
  exact e.symm

/- English proof (translation)
The claim follows from `Finset.sum_congr rfl fun S _ ↦ congrArg (_ * ·) (chi_congr k ((twistFunctor (lbInvProd L S)).mapIso e))`.
-/
theorem interNum_congr (e : F ≅ G) (L : ι → LB X) : interNum k F L = interNum k G L :=
  Finset.sum_congr rfl fun S _ ↦
    congrArg (_ * ·) (chi_congr k ((twistFunctor (lbInvProd L S)).mapIso e))

variable (F) in

/- English proof (translation)
Rewrite using `[interNum_eq_multiDiff k F hL, interNum_eq_multiDiff k F hL', funext h]`.
-/
theorem interNum_congr_cls (hL : ∀ i, (L i).IsLB) (hL' : ∀ i, (L' i).IsLB)
    (h : ∀ i, cls (L i) (hL i) = cls (L' i) (hL' i)) : interNum k F L = interNum k F L' := by
  rw [interNum_eq_multiDiff k F hL, interNum_eq_multiDiff k F hL', funext h]

variable (F) in

/- English proof (translation)
The claim follows from `interNum_congr_cls k F hL hL' fun i ↦ (cls_eq_iff _ _).2 (h i)`.
-/
theorem interNum_congr_lbIso (hL : ∀ i, (L i).IsLB) (hL' : ∀ i, (L' i).IsLB)
    (h : ∀ i, LBIso (L i) (L' i)) : interNum k F L = interNum k F L' :=
  interNum_congr_cls k F hL hL' fun i ↦ (cls_eq_iff _ _).2 (h i)

variable (F) in

/- English proof (translation)
Rewrite using `[interNum_eq_multiDiff k F hL, interNum_eq_multiDiff k F (L := L ∘ e) fun i ↦ hL (e i), ← multiDiff_comp_equiv e]`. Both sides reduce to the same expression.
-/
theorem interNum_comp_equiv (hL : ∀ i, (L i).IsLB) (e : κ ≃ ι) :
    interNum k F (L ∘ e) = interNum k F L := by
  rw [interNum_eq_multiDiff k F hL, interNum_eq_multiDiff k F (L := L ∘ e) fun i ↦ hL (e i),
    ← multiDiff_comp_equiv e]
  rfl

variable (F) in

/- English proof (translation)
The claim follows from `interNum_comp_equiv k F hL σ`.
-/
theorem interNum_comp_perm (hL : ∀ i, (L i).IsLB) (σ : Equiv.Perm ι) :
    interNum k F (L ∘ σ) = interNum k F L := interNum_comp_equiv k F hL σ

variable (F) in

/- English proof (translation)
Rewrite using `[interNum_eq_multiDiff k F isEmptyElim, multiDiff_of_isEmpty, chiPic_zero]`.
-/
@[simp] theorem interNum_of_isEmpty [IsEmpty ι] (L : ι → LB X) : interNum k F L = chi k F := by
  rw [interNum_eq_multiDiff k F isEmptyElim, multiDiff_of_isEmpty, chiPic_zero]

/- English proof (translation)
The claim follows from `Finset.sum_eq_zero fun S _ ↦ by rw [chi_eq_zero_of_isZero k ((Twist.isZero_twist_iff (isLB_lbInvProd hL S)).2 h), mul_zero]`.
-/
theorem interNum_eq_zero_of_isZero (h : IsZero F) (hL : ∀ i, (L i).IsLB) : interNum k F L = 0 :=
  Finset.sum_eq_zero fun S _ ↦ by
    rw [chi_eq_zero_of_isZero k ((Twist.isZero_twist_iff (isLB_lbInvProd hL S)).2 h), mul_zero]

section Cons

variable {d : ℕ} {P : Fin d → LB X}

/- English proof (translation)
The claim follows from `Fin.cases hM hP`.
-/
theorem isLB_cons (hM : M.IsLB) (hP : ∀ i, (P i).IsLB) :
    ∀ i, ((Fin.cons M P : Fin (d + 1) → LB X) i).IsLB :=
  Fin.cases hM hP

/- English proof (translation)
The claim follows from `funext (Fin.cases rfl fun _ ↦ rfl)`.
-/
theorem cls_cons (hM : M.IsLB) (hP : ∀ i, (P i).IsLB) :
    (fun i ↦ cls _ (isLB_cons hM hP i)) =
      (Fin.cons (cls M hM) (fun i ↦ cls (P i) (hP i)) : Fin (d + 1) → Pic X) :=
  funext (Fin.cases rfl fun _ ↦ rfl)

variable (F)

/- English proof (translation)
Rewrite using `[interNum_eq_multiDiff k F (isLB_cons hM hP), cls_cons hM hP, multiDiff_cons, bwdDiff_apply, interNum_twist_eq_multiDiff k F hP hN, interNum_eq_multiDiff k F hP, h, zero_sub]`.
-/
theorem interNum_cons_of_cls_eq_neg (hM : M.IsLB) (hP : ∀ i, (P i).IsLB) (hN : N.IsLB)
    (h : cls N hN = -cls M hM) :
    interNum k F (Fin.cons M P : Fin (d + 1) → LB X) =
      interNum k F P - interNum k (twist F N) P := by
  rw [interNum_eq_multiDiff k F (isLB_cons hM hP), cls_cons hM hP, multiDiff_cons, bwdDiff_apply,
    interNum_twist_eq_multiDiff k F hP hN, interNum_eq_multiDiff k F hP, h, zero_sub]

/- English proof (translation)
The claim follows from `interNum_cons_of_cls_eq_neg k F hM hP (Twist.isLB_lbZPow hM (-1)) (by rw [cls_lbZPow hM, neg_one_zsmul])`.
-/
theorem interNum_cons (hM : M.IsLB) (hP : ∀ i, (P i).IsLB) :
    interNum k F (Fin.cons M P : Fin (d + 1) → LB X) =
      interNum k F P - interNum k (twistZ F M (-1)) P :=
  interNum_cons_of_cls_eq_neg k F hM hP (Twist.isLB_lbZPow hM (-1))
    (by rw [cls_lbZPow hM, neg_one_zsmul])

/- English proof (translation)
Rewrite using `[interNum_cons k _ hM hP, interNum_congr k (Twist.twistTwistZNegOneIso F hM)]`.
-/
theorem interNum_twist_cons (hM : M.IsLB) (hP : ∀ i, (P i).IsLB) :
    interNum k (twist F M) (Fin.cons M P : Fin (d + 1) → LB X) =
      interNum k (twist F M) P - interNum k F P := by
  rw [interNum_cons k _ hM hP, interNum_congr k (Twist.twistTwistZNegOneIso F hM)]

/- English proof (translation)
Rewrite using `[interNum_eq_multiDiff k F (isLB_cons hM hP), interNum_eq_multiDiff k F (isLB_cons hA hP), interNum_eq_multiDiff k F (isLB_cons hB hP), interNum_eq_multiDiff k F (isLB_cons hA (isLB_cons hB hP)), cls_cons hA (isLB_cons hB hP), cls_cons hM hP, cls_cons hA hP, cls_cons hB hP]`. Simplify using `only [multiDiff_cons, bwdDiff_apply, h, sub_sub]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem interNum_cons_of_cls_eq_add (hM : M.IsLB) (hA : A.IsLB) (hB : B.IsLB)
    (hP : ∀ i, (P i).IsLB) (h : cls M hM = cls A hA + cls B hB) :
    interNum k F (Fin.cons M P : Fin (d + 1) → LB X) =
      interNum k F (Fin.cons A P : Fin (d + 1) → LB X) +
        interNum k F (Fin.cons B P : Fin (d + 1) → LB X) -
          interNum k F (Fin.cons A (Fin.cons B P) : Fin (d + 1 + 1) → LB X) := by
  rw [interNum_eq_multiDiff k F (isLB_cons hM hP), interNum_eq_multiDiff k F (isLB_cons hA hP),
    interNum_eq_multiDiff k F (isLB_cons hB hP),
    interNum_eq_multiDiff k F (isLB_cons hA (isLB_cons hB hP)), cls_cons hA (isLB_cons hB hP),
    cls_cons hM hP, cls_cons hA hP, cls_cons hB hP]
  simp only [multiDiff_cons, bwdDiff_apply, h, sub_sub]
  ring

/- English proof (translation)
The claim follows from `(interNum_cons k F (P := ![]) hM isEmptyElim).trans (congrArg₂ (· - ·) (interNum_of_isEmpty k _ _) (interNum_of_isEmpty k _ _))`.
-/
theorem interNum_one (hM : M.IsLB) :
    interNum k F ![M] = chi k F - chi k (twistZ F M (-1)) :=
  (interNum_cons k F (P := ![]) hM isEmptyElim).trans
    (congrArg₂ (· - ·) (interNum_of_isEmpty k _ _) (interNum_of_isEmpty k _ _))

end Cons

variable (F) in

/- English proof (translation)
Rewrite using `[interNum_eq_multiDiff k F hL, multiDiff_eq_shiftAct, Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h, diffElt_zero]), map_zero]`. Both sides reduce to the same expression.
-/
theorem interNum_eq_zero_of_cls_eq_zero (hL : ∀ i, (L i).IsLB) (i : ι)
    (h : cls (L i) (hL i) = 0) : interNum k F L = 0 := by
  rw [interNum_eq_multiDiff k F hL, multiDiff_eq_shiftAct,
    Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h, diffElt_zero]), map_zero]
  rfl

variable (F) in

/- English proof (translation)
Rewrite using `[← interNum_lbZPow_eq_multiDiff k F hM]`. Conclude with `interNum_congr_cls k F (fun _ ↦ hM) (fun _ ↦ Twist.isLB_lbZPow hM 1) fun _ ↦ by rw [cls_lbZPow hM, one_zsmul]`.
-/
theorem interNum_const_eq_multiDiff (hM : M.IsLB) :
    interNum k F (fun _ : ι ↦ M) = multiDiff (fun _ : ι ↦ 1) (fun n ↦ chi k (twistZ F M n)) 0 := by
  rw [← interNum_lbZPow_eq_multiDiff k F hM]
  exact interNum_congr_cls k F (fun _ ↦ hM) (fun _ ↦ Twist.isLB_lbZPow hM 1)
    fun _ ↦ by rw [cls_lbZPow hM, one_zsmul]

variable (F) in

/- English proof (translation)
Establish `e` using `Finset.sum_powerset_apply_card (x := (Finset.univ : Finset (Fin d))) fun j ↦ (-1 : ℤ) ^ j * chi k (twistZ F M (-j))`. Rewrite `e` using `[Finset.powerset_univ, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[interNum_const_eq_multiDiff k F hM, multiDiff_apply]`. Simplify using `only [Finset.sum_const, nsmul_eq_mul, mul_one, zero_sub, smul_eq_mul] at e ⊢`. Rewrite using `[e]`.

Conclude with `Finset.sum_congr rfl fun j _ ↦ by ring`.
-/
theorem interNum_const_eq_sum (hM : M.IsLB) (d : ℕ) :
    interNum k F (fun _ : Fin d ↦ M) = ∑ j ∈ Finset.range (d + 1),
      (-1 : ℤ) ^ j * d.choose j * chi k (twistZ F M (-j)) := by
  have e := Finset.sum_powerset_apply_card (x := (Finset.univ : Finset (Fin d)))
    fun j ↦ (-1 : ℤ) ^ j * chi k (twistZ F M (-j))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at e
  rw [interNum_const_eq_multiDiff k F hM, multiDiff_apply]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, zero_sub, smul_eq_mul] at e ⊢
  rw [e]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

variable (F) in

/- English proof (translation)
Establish `e₁` using `congrFun (multiDiff_map (Int.castAddHom ℚ) a fun n ↦ chi k (twistZ F M n)) 0`. Establish `e₂` using `congrFun (multiDiff_comap (Int.castAddHom ℚ) a fun t : ℚ ↦ p.eval t) 0`. Establish `e₃ : (Int.castAddHom ℚ ∘ fun n ↦ chi k (twistZ F M n)) = (fun t : ℚ ↦ p.eval t) ∘ Int.castAddHom ℚ` using `funext h`. Rewrite using `[interNum_lbZPow_eq_multiDiff k F hM]`. Rewrite `e₁` using `[e₃, e₂, Function.comp_apply, multiDiff_polynomial_eval _ p hp]`.

Conclude with `e₁.symm`.
-/
theorem interNum_lbZPow_of_polynomial (hM : M.IsLB) {d : ℕ} (p : Polynomial ℚ)
    (hp : p.natDegree ≤ d) (h : ∀ n : ℤ, (chi k (twistZ F M n) : ℚ) = p.eval (n : ℚ))
    (a : Fin d → ℤ) :
    (interNum k F (fun i ↦ lbZPow M (a i)) : ℚ) = d.factorial * p.coeff d * ∏ i, (a i : ℚ) := by
  have e₁ := congrFun (multiDiff_map (Int.castAddHom ℚ) a fun n ↦ chi k (twistZ F M n)) 0
  have e₂ := congrFun (multiDiff_comap (Int.castAddHom ℚ) a fun t : ℚ ↦ p.eval t) 0
  have e₃ : (Int.castAddHom ℚ ∘ fun n ↦ chi k (twistZ F M n)) =
    (fun t : ℚ ↦ p.eval t) ∘ Int.castAddHom ℚ := funext h
  rw [interNum_lbZPow_eq_multiDiff k F hM]
  rw [e₃, e₂, Function.comp_apply, multiDiff_polynomial_eval _ p hp] at e₁
  exact e₁.symm

variable (F) in

/- English proof (translation)
Rewrite using `[interNum_congr_cls k F (fun _ ↦ hM) (fun _ ↦ Twist.isLB_lbZPow hM 1) fun _ ↦ by rw [cls_lbZPow hM, one_zsmul], interNum_lbZPow_of_polynomial k F hM p hp h fun _ ↦ 1]`. Simplify using the standard rewrite rules.
-/
theorem interNum_const_of_polynomial (hM : M.IsLB) {d : ℕ} (p : Polynomial ℚ)
    (hp : p.natDegree ≤ d) (h : ∀ n : ℤ, (chi k (twistZ F M n) : ℚ) = p.eval (n : ℚ)) :
    (interNum k F (fun _ : Fin d ↦ M) : ℚ) = d.factorial * p.coeff d := by
  rw [interNum_congr_cls k F (fun _ ↦ hM) (fun _ ↦ Twist.isLB_lbZPow hM 1)
    fun _ ↦ by rw [cls_lbZPow hM, one_zsmul],
    interNum_lbZPow_of_polynomial k F hM p hp h fun _ ↦ 1]
  simp

/- English proof (translation)
The claim follows from `interNum_of_isEmpty k _ _`.
-/
@[simp] theorem topSelf_zero (M : LB X) : topSelfIntersection k M 0 = chi k (structureModule X) :=
  interNum_of_isEmpty k _ _

/- English proof (translation)
The claim follows from `interNum_congr_lbIso k _ (fun _ ↦ hM) (fun _ ↦ hN) fun _ ↦ h`.
-/
theorem topSelf_congr (hM : M.IsLB) (hN : N.IsLB) (h : LBIso M N) (d : ℕ) :
    topSelfIntersection k M d = topSelfIntersection k N d :=
  interNum_congr_lbIso k _ (fun _ ↦ hM) (fun _ ↦ hN) fun _ ↦ h

/- English proof (translation)
The claim follows from `interNum_congr k ((Scheme.Modules.pushforwardId X).app _) L`.
-/
@[simp] theorem interNumOn_id (L : ι → LB X) :
    interNumOn k (𝟙 X) L = interNum k (structureModule X) L :=
  interNum_congr k ((Scheme.Modules.pushforwardId X).app _) L

/- English proof (translation)
The claim follows from `interNum_congr k (((Scheme.Modules.pushforwardComp g f).app _).symm ≪≫ (Scheme.Modules.pushforward f).mapIso (asIso (unitToPush g)).symm) L`.
-/
theorem interNumOn_comp_of_isIso (g : Y ⟶ Z) (f : Z ⟶ X) [IsIso (unitToPush g)] (L : ι → LB X) :
    interNumOn k (g ≫ f) L = interNumOn k f L :=
  interNum_congr k (((Scheme.Modules.pushforwardComp g f).app _).symm ≪≫
    (Scheme.Modules.pushforward f).mapIso (asIso (unitToPush g)).symm) L

/- English proof (translation)
Establish `: IsIso f.toImage` using `inferInstance`. Rewrite using `[interNumSub_def, ← interNumOn_comp_of_isIso k f.toImage]`. Conclude with `congrArg (interNumOn k · L) f.toImage_imageι.symm`.
-/
theorem interNumOn_eq_interNumSub (f : Z ⟶ X) [IsClosedImmersion f] (L : ι → LB X) :
    interNumOn k f L = interNumSub k f.ker L := by
  have : IsIso f.toImage := inferInstance
  rw [interNumSub_def, ← interNumOn_comp_of_isIso k f.toImage]
  exact congrArg (interNumOn k · L) f.toImage_imageι.symm

variable {k}

section ShortExact

variable {S : ShortComplex X.Modules}

/- English proof (translation)
Rewrite using `[interNum_def, interNum_def, interNum_def, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun T _ ↦ by`. Rewrite using `[chi_twist_shortExact hS (isLB_lbInvProd hL T) (h₁ T) (h₃ T), mul_add]`.
-/
theorem interNum_shortExact' (hS : S.ShortExact) (hL : ∀ i, (L i).IsLB)
    (h₁ : ∀ T, FiniteCoh k (twist S.X₁ (lbInvProd L T)))
    (h₃ : ∀ T, FiniteCoh k (twist S.X₃ (lbInvProd L T))) :
    interNum k S.X₂ L = interNum k S.X₁ L + interNum k S.X₃ L := by
  rw [interNum_def, interNum_def, interNum_def, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun T _ ↦ by
    rw [chi_twist_shortExact hS (isLB_lbInvProd hL T) (h₁ T) (h₃ T), mul_add]

/- English proof (translation)
The claim follows from `interNum_shortExact' hS hL (fun T ↦ h₁ _ (isLB_lbInvProd hL T)) fun T ↦ h₃ _ (isLB_lbInvProd hL T)`.
-/
theorem interNum_shortExact (hS : S.ShortExact) (hL : ∀ i, (L i).IsLB)
    (h₁ : FiniteCohTwists k S.X₁) (h₃ : FiniteCohTwists k S.X₃) :
    interNum k S.X₂ L = interNum k S.X₁ L + interNum k S.X₃ L :=
  interNum_shortExact' hS hL (fun T ↦ h₁ _ (isLB_lbInvProd hL T))
    fun T ↦ h₃ _ (isLB_lbInvProd hL T)

/- English proof (translation)
Rewrite using `[interNum_shortExact hS hL h₁ (h₁.of_shortExact₃ hS h₂)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem interNum_shortExact₃ (hS : S.ShortExact) (hL : ∀ i, (L i).IsLB)
    (h₁ : FiniteCohTwists k S.X₁) (h₂ : FiniteCohTwists k S.X₂) :
    interNum k S.X₃ L = interNum k S.X₂ L - interNum k S.X₁ L := by
  rw [interNum_shortExact hS hL h₁ (h₁.of_shortExact₃ hS h₂)]; ring

/- English proof (translation)
Rewrite using `[interNum_shortExact hS hL (h₂.of_shortExact₁ hS h₃) h₃]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem interNum_shortExact₁ (hS : S.ShortExact) (hL : ∀ i, (L i).IsLB)
    (h₂ : FiniteCohTwists k S.X₂) (h₃ : FiniteCohTwists k S.X₃) :
    interNum k S.X₁ L = interNum k S.X₂ L - interNum k S.X₃ L := by
  rw [interNum_shortExact hS hL (h₂.of_shortExact₁ hS h₃) h₃]; ring

end ShortExact

/- English proof (translation)
The claim follows from `have hS : (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact := { exact := ShortComplex.exact_cokernel φ } have := interNum_shortExact₃ hS hL hF hG this`.
-/
theorem interNum_cokernel (φ : F ⟶ G) [Mono φ] (hL : ∀ i, (L i).IsLB) (hF : FiniteCohTwists k F)
    (hG : FiniteCohTwists k G) :
    interNum k (cokernel φ) L = interNum k G L - interNum k F L :=
  have hS : (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact :=
    { exact := ShortComplex.exact_cokernel φ }
  have := interNum_shortExact₃ hS hL hF hG
  this

section Push

variable [Algebra k Γ(Z, ⊤)] {f : Z ⟶ X}
  (hf : ∀ r : k, f.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Z, ⊤) r)

/- English proof (translation)
Rewrite using `[interNum_eq_multiDiff k F hL, h, multiDiff_comap, Function.comp_apply, map_zero, interNum_eq_multiDiff k H fun i ↦ pull_isLB (hL i) f]`. Both sides reduce to the same expression.
-/
theorem interNum_eq_of_chiPic_eq {H : Z.Modules} (h : chiPic k F = chiPic k H ∘ pull f)
    (hL : ∀ i, (L i).IsLB) : interNum k F L = interNum k H fun i ↦ (L i).pull f := by
  rw [interNum_eq_multiDiff k F hL, h, multiDiff_comap, Function.comp_apply, map_zero,
    interNum_eq_multiDiff k H fun i ↦ pull_isLB (hL i) f]
  rfl

include hf

/- English proof (translation)
The claim follows from `interNum_eq_of_chiPic_eq (chiPic_pushforward_of_isClosedImmersion hf H) hL`.
-/
theorem interNum_pushforward_of_isClosedImmersion [IsClosedImmersion f] (H : Z.Modules)
    (hL : ∀ i, (L i).IsLB) :
    interNum k ((Scheme.Modules.pushforward f).obj H) L = interNum k H fun i ↦ (L i).pull f :=
  interNum_eq_of_chiPic_eq (chiPic_pushforward_of_isClosedImmersion hf H) hL

/- English proof (translation)
The claim follows from `interNum_eq_of_chiPic_eq (chiPic_pushforward_of_isAffineHom hf H) hL`.
-/
theorem interNum_pushforward_of_isAffineHom [IsAffineHom f] (H : Z.Modules) [H.IsQuasicoherent]
    (hL : ∀ i, (L i).IsLB) :
    interNum k ((Scheme.Modules.pushforward f).obj H) L = interNum k H fun i ↦ (L i).pull f :=
  interNum_eq_of_chiPic_eq (chiPic_pushforward_of_isAffineHom hf H) hL

/- English proof (translation)
The claim follows from `interNum_pushforward_of_isAffineHom hf _ hL`.
-/
theorem interNumOn_eq_interNum_pull [IsAffineHom f] (hL : ∀ i, (L i).IsLB) :
    interNumOn k f L = interNum k (structureModule Z) fun i ↦ (L i).pull f :=
  interNum_pushforward_of_isAffineHom hf _ hL

/- English proof (translation)
The claim follows from `interNumOn_eq_interNum_pull hf fun _ ↦ hM`.
-/
theorem interNumOn_const_eq_topSelf [IsAffineHom f] (hM : M.IsLB) (d : ℕ) :
    interNumOn k f (fun _ : Fin d ↦ M) = topSelfIntersection k (M.pull f) d :=
  interNumOn_eq_interNum_pull hf fun _ ↦ hM

/- English proof (translation)
The claim follows from `(interNum_congr k ((Scheme.Modules.pushforwardComp g f).app _).symm L).trans (interNum_pushforward_of_isAffineHom hf _ hL)`.
-/
theorem interNumOn_comp [IsAffineHom f] (g : Y ⟶ Z) [QuasiCompact g] [QuasiSeparated g]
    (hL : ∀ i, (L i).IsLB) :
    interNumOn k (g ≫ f) L = interNumOn k g fun i ↦ (L i).pull f :=
  (interNum_congr k ((Scheme.Modules.pushforwardComp g f).app _).symm L).trans
    (interNum_pushforward_of_isAffineHom hf _ hL)

end Push

end Inter

section FiniteAlgebra

variable (k : Type v) [Field k] (A : CommRingCat.{0}) [Algebra k A] [Algebra k Γ(Spec A, ⊤)]
  [IsScalarTower k A Γ(Spec A, ⊤)]

/- English proof (translation)
Rewrite using `[chi_eq_hdim_zero k fun _ hn ↦ coh.subsingleton_of_isAffine _ hn, hdim_def, ((coh.zeroUnitSpecEquiv A).restrictScalars k).finrank_eq]`.
-/
theorem chi_structureModule_Spec : chi k (structureModule (Spec A)) = Module.finrank k A := by
  rw [chi_eq_hdim_zero k fun _ hn ↦ coh.subsingleton_of_isAffine _ hn, hdim_def,
    ((coh.zeroUnitSpecEquiv A).restrictScalars k).finrank_eq]

omit [Algebra k Γ(Spec A, ⊤)] [IsScalarTower k A Γ(Spec A, ⊤)] in

abbrev algebraΓSpecOf : Algebra k Γ(Spec A, ⊤) :=
  ((algebraMap A Γ(Spec A, ⊤)).comp (algebraMap k A)).toAlgebra

omit [Algebra k Γ(Spec A, ⊤)] [IsScalarTower k A Γ(Spec A, ⊤)] in

/- English proof (translation)
The claim follows from `letI := algebraΓSpecOf k A .of_algebraMap_eq fun _ ↦ rfl`.
-/
theorem isScalarTower_algebraΓSpecOf :
    letI := algebraΓSpecOf k A
    IsScalarTower k A Γ(Spec A, ⊤) :=
  letI := algebraΓSpecOf k A
  .of_algebraMap_eq fun _ ↦ rfl

end FiniteAlgebra

section Examples

/- English proof (translation)
Use `letI := algebraΓSpecOf ℝ (.of (Polynomial ℝ))`. Use `letI := algebraΓSpecOf ℝ (.of ℂ)`. Use `isScalarTower_algebraΓSpecOf ℝ (.of ℂ)` as an intermediate fact. Rewrite using `[interNumOn_eq_interNum_pull ?_ isEmptyElim, interNum_of_isEmpty, chi_structureModule_Spec]`. Conclude with `congrArg _ Complex.finrank_real_complex`.

Introduce `r`. Use `ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.aeval (R := ℝ) Complex.I).toRingHom)) (algebraMap ℝ _ r)` as an intermediate fact. Use `this.symm.trans ?_` and prove the remaining obligations. Conclude with `congrArg (Scheme.ΓSpecIso (.of ℂ)).inv ((Polynomial.aeval Complex.I).commutes r)`.
-/
example : letI := algebraΓSpecOf ℝ (.of (Polynomial ℝ))
    interNumOn ℝ (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := ℝ) Complex.I).toRingHom))
      (![] : Fin 0 → LB (Spec (.of (Polynomial ℝ)))) = 2 := by
  letI := algebraΓSpecOf ℝ (.of (Polynomial ℝ))
  letI := algebraΓSpecOf ℝ (.of ℂ)
  have := isScalarTower_algebraΓSpecOf ℝ (.of ℂ)
  rw [interNumOn_eq_interNum_pull ?_ isEmptyElim, interNum_of_isEmpty, chi_structureModule_Spec]
  · exact congrArg _ Complex.finrank_real_complex
  · intro r
    have := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Polynomial.aeval (R := ℝ) Complex.I).toRingHom)) (algebraMap ℝ _ r)
    refine this.symm.trans ?_
    exact congrArg (Scheme.ΓSpecIso (.of ℂ)).inv ((Polynomial.aeval Complex.I).commutes r)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[interNum_one k F hM, chi_congr k (Twist.twistZZeroIso F hM), h, h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[interNum_lbZPow_eq_multiDiff k F hM, multiDiff_const]`. Simplify using `[bwdDiff_apply, h]`.
-/
example {X : Scheme.{0}} (k : Type) [Field k] [Algebra k Γ(X, ⊤)] (F : X.Modules) {M : LB X}
    (hM : M.IsLB) (a b : ℤ) (h : ∀ n : ℤ, chi k (twistZ F M n) = a * n + b) :
    interNum k F ![M] = a ∧ interNum k F (fun _ : Fin 1 ↦ lbZPow M (-1)) = -a := by
  constructor
  · rw [interNum_one k F hM, chi_congr k (Twist.twistZZeroIso F hM), h, h]; ring
  · rw [interNum_lbZPow_eq_multiDiff k F hM, multiDiff_const]
    simp [bwdDiff_apply, h]

end Examples

end GlobalTheory
