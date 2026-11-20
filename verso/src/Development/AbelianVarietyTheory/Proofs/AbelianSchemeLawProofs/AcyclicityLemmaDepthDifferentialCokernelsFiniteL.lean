import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing

namespace GlobalTheory
namespace FiniteLengthComplex

variable {R : Type} [CommRing R]

noncomputable def extCongrLeft {X X' : ModuleCat.{0} R} (e : X ≅ X') (Y : ModuleCat.{0} R) (n : ℕ) :
    Abelian.Ext.{0} X' Y n ≃ₗ[R] Abelian.Ext.{0} X Y n :=
  LinearEquiv.ofLinearMap ((Ext.mk₀ e.hom).precompOfLinear R Y (zero_add n))
    ((Ext.mk₀ e.inv).precompOfLinear R Y (zero_add n))
    (by ext x; simp) (by ext x; simp)

/- English proof (translation)
Use `subsingleton_of_forall_eq 0 fun x => ?_` and prove the remaining obligations. Rewrite using `[← Ext.mk₀_id_comp x, h.eq_zero_of_src (𝟙 X), Ext.mk₀_zero, Ext.zero_comp]`.
-/
theorem subsingleton_ext_of_isZero_left {X : ModuleCat.{0} R} (h : IsZero X) (Y : ModuleCat.{0} R)
    (n : ℕ) : Subsingleton (Abelian.Ext.{0} X Y n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.mk₀_id_comp x, h.eq_zero_of_src (𝟙 X), Ext.mk₀_zero, Ext.zero_comp]

/- English proof (translation)
The claim follows from `ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ N) N.subtype_injective N.mkQ_surjective`.
-/
theorem shortExact_submodule {M : Type} [AddCommGroup M] [Module R M] (N : Submodule R M) :
    (ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ
      (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ N) N.subtype_injective
    N.mkQ_surjective

/- English proof (translation)
Take `⟨I, hI, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R M›`. Take `rfl` from `eq_maximalIdeal hI`. Conclude with `⟨e.toModuleIso⟩`.
-/
theorem nonempty_iso_residue [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] :
    Nonempty (ModuleCat.of R M ≅ ModuleCat.of R (R ⧸ maximalIdeal R)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R M›
  obtain rfl := eq_maximalIdeal hI
  exact ⟨e.toModuleIso⟩

/- English proof (translation)
Proceed by induction on `hM with`. Consider the case `of_subsingleton`. Conclude with `subsingleton_ext_of_isZero_left (ModuleCat.isZero_of_subsingleton _) Y n`. Consider the case `@of_simple_quotient M _ _ N _ _ ih`. Take `⟨e⟩` from `nonempty_iso_residue (R := R) (M ⧸ N)`.

Establish `h3` using `(extCongrLeft e Y n).symm.toEquiv.subsingleton`. Use `subsingleton_of_forall_eq 0 fun x => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Ext.contravariant_sequence_exact₂ (shortExact_submodule N) Y x (@Subsingleton.elim _ ih _ _)`. Rewrite using `[@Subsingleton.elim _ h3 y 0]`. Conclude with `Ext.comp_zero _ _ _ _ _`.
-/
theorem subsingleton_ext_of_isFiniteLength [IsLocalRing R] (Y : ModuleCat.{0} R) (n : ℕ)
    (hk : Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y n))
    (M : Type) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Subsingleton (Abelian.Ext.{0} (ModuleCat.of R M) Y n) := by
  induction hM with
  | of_subsingleton =>
    exact subsingleton_ext_of_isZero_left (ModuleCat.isZero_of_subsingleton _) Y n
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨e⟩ := nonempty_iso_residue (R := R) (M ⧸ N)
    have h3 := (extCongrLeft e Y n).symm.toEquiv.subsingleton
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₂ (shortExact_submodule N) Y x
      (@Subsingleton.elim _ ih _ _)
    rw [@Subsingleton.elim _ h3 y 0]
    exact Ext.comp_zero _ _ _ _ _

/- English proof (translation)
Proceed by induction on `hM with`. Consider the case `@of_subsingleton M _ _ _`. Use `subsingleton_ext_of_isZero_left (ModuleCat.isZero_of_subsingleton (ModuleCat.of R M)) Y g` as an intermediate fact. Rewrite using `[Module.length_eq_zero, Module.length_eq_zero (M := M), zero_mul]`. Consider the case `@of_simple_quotient M _ _ N _ hN ih`.

Take `⟨e⟩` from `nonempty_iso_residue (R := R) (M ⧸ N)`. Establish `hS` using `shortExact_submodule N`. Rewrite using `[Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective N.mkQ_surjective (LinearMap.exact_subtype_mkQ N), Module.length_eq_one R (M ⧸ N), add_mul, one_mul, ← ih, (extCongrLeft e Y g).length_eq, add_comm]`. Use `Module.length_eq_add_of_exact ((Ext.mk₀ (ModuleCat.ofHom N.mkQ)).precompOfLinear R Y (zero_add g)) ((Ext.mk₀ (ModuleCat.ofHom N.subtype)).precompOfLinear R Y (zero_add g)) ?_ ?_ ?_` and prove the remaining obligations. Consider the cases of `g with`.

Consider the case `zero`. Use `hS.epi_g` as an intermediate fact. Conclude with `Ext.precomp_mk₀_injective_of_epi Y (ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero).g`. Consider the case `succ g`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Take `⟨y, rfl⟩` from `Ext.contravariant_sequence_exact₃ hS Y x hx (add_comm 1 g)`. Rewrite using `[@Subsingleton.elim _ (subsingleton_ext_of_isFiniteLength Y g (hk g (by omega)) N hN) y 0]`. Conclude with `Ext.comp_zero _ _ _ _ _`. Introduce `x`.

Use `hk (g + 1) (by omega)` as an intermediate fact. Establish `h3` using `(extCongrLeft e Y (g + 1)).symm.toEquiv.subsingleton`. Conclude with `Ext.contravariant_sequence_exact₁ hS Y x (add_comm 1 g) (@Subsingleton.elim _ h3 _ _)`. Introduce `x`. Use `⟨fun hx => Ext.contravariant_sequence_exact₂ hS Y x hx, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨y, rfl⟩`. Express the relevant statement in the definitionally equal form `(Ext.mk₀ _).comp ((Ext.mk₀ _).comp y (zero_add g)) (zero_add g) = 0`. Rewrite using `[Ext.mk₀_comp_mk₀_assoc, ← ModuleCat.ofHom_comp, (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero]`. Simplify using the standard rewrite rules.
-/
theorem length_ext_of_isFiniteLength [IsLocalRing R] (Y : ModuleCat.{0} R) (g : ℕ)
    (hk : ∀ n, n ≠ g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y n))
    (M : Type) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Module.length R (Abelian.Ext.{0} (ModuleCat.of R M) Y g) = Module.length R M *
      Module.length R (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y g) := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
    have := subsingleton_ext_of_isZero_left
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R M)) Y g
    rw [Module.length_eq_zero, Module.length_eq_zero (M := M), zero_mul]
  | @of_simple_quotient M _ _ N _ hN ih =>
    obtain ⟨e⟩ := nonempty_iso_residue (R := R) (M ⧸ N)
    have hS := shortExact_submodule N
    rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N), Module.length_eq_one R (M ⧸ N), add_mul, one_mul, ← ih,
      (extCongrLeft e Y g).length_eq, add_comm]
    refine Module.length_eq_add_of_exact
      ((Ext.mk₀ (ModuleCat.ofHom N.mkQ)).precompOfLinear R Y (zero_add g))
      ((Ext.mk₀ (ModuleCat.ofHom N.subtype)).precompOfLinear R Y (zero_add g)) ?_ ?_ ?_
    · cases g with
      | zero =>
        have := hS.epi_g
        exact Ext.precomp_mk₀_injective_of_epi Y (ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ
          (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero).g
      | succ g =>
        rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y x hx (add_comm 1 g)
        rw [@Subsingleton.elim _ (subsingleton_ext_of_isFiniteLength Y g (hk g (by omega)) N hN) y 0]
        exact Ext.comp_zero _ _ _ _ _
    · intro x
      have := hk (g + 1) (by omega)
      have h3 := (extCongrLeft e Y (g + 1)).symm.toEquiv.subsingleton
      exact Ext.contravariant_sequence_exact₁ hS Y x (add_comm 1 g) (@Subsingleton.elim _ h3 _ _)
    · intro x
      refine ⟨fun hx => Ext.contravariant_sequence_exact₂ hS Y x hx, ?_⟩
      rintro ⟨y, rfl⟩
      change (Ext.mk₀ _).comp ((Ext.mk₀ _).comp y (zero_add g)) (zero_add g) = 0
      rw [Ext.mk₀_comp_mk₀_assoc, ← ModuleCat.ofHom_comp,
        (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero]
      simp

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R F`. Establish `hid : 𝟙 F = ∑ i, (ModuleCat.ofHom (b.coord i) : F ⟶ ModuleCat.of R R) ≫ (ModuleCat.ofHom (LinearMap.toSpanSingleton R F (b i)) : ModuleCat.of R R ⟶ F)`. Use extensionality with `x`. Simplify using `[ModuleCat.hom_sum, b.sum_repr x]`. Use `subsingleton_of_forall_eq 0 fun x => ?_` and prove the remaining obligations.

Rewrite using `[← Ext.comp_mk₀_id x, hid, Ext.mk₀_sum, Ext.comp_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero, Subsingleton.elim (x.comp _ _) 0, Ext.zero_comp]`.
-/
theorem subsingleton_ext_free (X : ModuleCat.{0} R) (n : ℕ)
    (h : Subsingleton (Abelian.Ext.{0} X (ModuleCat.of R R) n))
    (F : ModuleCat.{0} R) [Module.Free R F] [Module.Finite R F] :
    Subsingleton (Abelian.Ext.{0} X F n) := by
  let b := Module.Free.chooseBasis R F
  have hid : 𝟙 F = ∑ i, (ModuleCat.ofHom (b.coord i) : F ⟶ ModuleCat.of R R) ≫
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R F (b i)) : ModuleCat.of R R ⟶ F) := by
    ext x
    simp [ModuleCat.hom_sum, b.sum_repr x]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.comp_mk₀_id x, hid, Ext.mk₀_sum, Ext.comp_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    Subsingleton.elim (x.comp _ _) 0, Ext.zero_comp]

/- English proof (translation)
Take `⟨xs, h, hd⟩` from `exists_ofList_eq_maximalIdeal_length_eq R`. Establish `hreg` using `isRegular_of_ofList_eq_maximalIdeal h hd.le`. Establish `hlen : xs.length = g`. Rewrite `hd` using `[hg]`. Conclude with `hd` after adjusting the coercions.

Break down `lt_or_gt_of_ne hn with hlt | hgt` into its components or cases. Use `ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) _ ?_ _ ?_ xs ?_ hreg n (hlen ▸ hlt)` and prove the remaining obligations. Rewrite using `[Module.support_eq_zeroLocus, Ideal.annihilator_quotient]`. Rewrite using `[smul_eq_mul, Ideal.mul_top]`. Conclude with `(maximalIdeal.isMaximal R).ne_top.lt_top`.

Introduce `r hr`. Rewrite using `[← h]`. Conclude with `Ideal.subset_span hr`. Establish `key` using `ModuleCat.projectiveDimension_quotient_eq_length.{0} xs hreg`. Rewrite `key` using `[projectiveDimension_eq_of_iso (Shrink.linearEquiv R _).toModuleIso, h, hlen]`.

Establish `: HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ maximalIdeal R)) g` using `(projectiveDimension_le_iff _ g).mp key.le`. Conclude with `HasProjectiveDimensionLT.subsingleton _ (g + 1) n hgt _`.
-/
theorem subsingleton_ext_residue [IsRegularLocalRing R] (g : ℕ) (hg : ringKrullDim R = g)
    (n : ℕ) (hn : n ≠ g) :
    Subsingleton
      (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) n) := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have hlen : xs.length = g := by
    rw [hg] at hd
    exact_mod_cast hd
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · refine ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) _ ?_ _ ?_ xs ?_ hreg n
      (hlen ▸ hlt)
    · rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    · rw [smul_eq_mul, Ideal.mul_top]
      exact (maximalIdeal.isMaximal R).ne_top.lt_top
    · intro r hr
      rw [← h]
      exact Ideal.subset_span hr
  · have key := ModuleCat.projectiveDimension_quotient_eq_length.{0} xs hreg
    rw [projectiveDimension_eq_of_iso (Shrink.linearEquiv R _).toModuleIso, h, hlen] at key
    have : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ maximalIdeal R)) g :=
      (projectiveDimension_le_iff _ g).mp key.le
    exact HasProjectiveDimensionLT.subsingleton _ (g + 1) n hgt _

section Complex

variable (C : CochainComplex (ModuleCat.{0} R) ℕ)

noncomputable def opcyclesShortComplex (i : ℕ) : ShortComplex (ModuleCat.{0} R) :=
  ShortComplex.mk (C.fromOpcycles i (i + 1)) (C.pOpcycles (i + 1)) (by
    rw [← cancel_epi (C.pOpcycles i)]
    simp)

/- English proof (translation)
Establish `hm : Mono (C.fromOpcycles i (i + 1))`. Establish `hex` using `ShortComplex.exact_of_f_is_kernel (ShortComplex.mk (C.homologyι i) (C.fromOpcycles i (i + 1)) (by simp)) (C.homologyIsKernel i (i + 1) (by simp))`. Conclude with `hex.mono_g (h.eq_zero_of_src _)`. Establish `hex : (opcyclesShortComplex C i).Exact`. Establish `h1` using `ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk (C.d i (i + 1)) (C.pOpcycles (i + 1)) (by simp)) (C.opcyclesIsCokernel i (i + 1) (by simp))`.

Set `φ : ShortComplex.mk (C.d i (i + 1)) (C.pOpcycles (i + 1)) (by simp) ⟶ opcyclesShortComplex C i` to `{ τ₁ := C.pOpcycles i, τ₂ := 𝟙 _, τ₃ := 𝟙 _ comm₁₂ := by simp [opcyclesShortComplex] comm₂₃ := by simp [opcyclesShortComplex] }`. Establish `: Epi φ.τ₁` using `inferInstanceAs (Epi (C.pOpcycles i))`. Establish `: IsIso φ.τ₂` using `inferInstanceAs (IsIso (𝟙 (C.X (i + 1))))`. Establish `: Mono φ.τ₃` using `inferInstanceAs (Mono (𝟙 (C.opcycles (i + 1))))`. Conclude with `(ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp h1`.

Conclude with `{ exact := hex mono_f := hm epi_g := inferInstanceAs (Epi (C.pOpcycles (i + 1))) }`.
-/
theorem opcyclesShortComplex_shortExact (i : ℕ) (h : IsZero (C.homology i)) :
    (opcyclesShortComplex C i).ShortExact := by
  have hm : Mono (C.fromOpcycles i (i + 1)) := by
    have hex := ShortComplex.exact_of_f_is_kernel
      (ShortComplex.mk (C.homologyι i) (C.fromOpcycles i (i + 1)) (by simp))
      (C.homologyIsKernel i (i + 1) (by simp))
    exact hex.mono_g (h.eq_zero_of_src _)
  have hex : (opcyclesShortComplex C i).Exact := by
    have h1 := ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk (C.d i (i + 1)) (C.pOpcycles (i + 1)) (by simp))
      (C.opcyclesIsCokernel i (i + 1) (by simp))
    let φ : ShortComplex.mk (C.d i (i + 1)) (C.pOpcycles (i + 1)) (by simp) ⟶
        opcyclesShortComplex C i :=
      { τ₁ := C.pOpcycles i, τ₂ := 𝟙 _, τ₃ := 𝟙 _
        comm₁₂ := by simp [opcyclesShortComplex]
        comm₂₃ := by simp [opcyclesShortComplex] }
    have : Epi φ.τ₁ := inferInstanceAs (Epi (C.pOpcycles i))
    have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (C.X (i + 1))))
    have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 (C.opcycles (i + 1))))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp h1
  exact
    { exact := hex
      mono_f := hm
      epi_g := inferInstanceAs (Epi (C.pOpcycles (i + 1))) }

/- English proof (translation)
The claim follows from `C.isIso_pOpcycles 0 0 (by simp) (by simp)`.
-/
theorem isIso_pOpcycles_zero : IsIso (C.pOpcycles 0) :=
  C.isIso_pOpcycles 0 0 (by simp) (by simp)

/- English proof (translation)
Establish `key : ∀ i, (∀ n, n + i < g → Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (C.opcycles i) n)) → i < g → IsZero (C.homology i)`. Introduce `i h hi`. Establish `h0 : Subsingleton (Abelian.Ext.{0} (C.homology i) (C.opcycles i) 0)` using `subsingleton_ext_of_isFiniteLength _ 0 (h 0 (by omega)) _ (hH i)`. Establish `h1 : Subsingleton (C.homology i ⟶ C.opcycles i)` using `Ext.addEquiv₀.subsingleton_congr.mp h0`. Conclude with `IsZero.of_mono_eq_zero (C.homologyι i) (Subsingleton.elim _ _)`.

Proceed by induction on `i with`. Consider the case `zero`. Use `(fun h => ⟨h, key 0 h⟩) fun n hn => ?_` and prove the remaining obligations. Use `isIso_pOpcycles_zero C` as an intermediate fact. Use `hX 0 n (by omega)` as an intermediate fact.

Use `subsingleton_of_forall_eq 0 fun x => ?_` and prove the remaining obligations. Rewrite using `[← Ext.comp_mk₀_id x, ← IsIso.inv_hom_id (C.pOpcycles 0), ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero, Subsingleton.elim (x.comp _ _) 0, Ext.zero_comp]`. Consider the case `succ i ih`. Use `(fun h => ⟨h, key (i + 1) h⟩) fun n hn => ?_` and prove the remaining obligations. Establish `hS` using `opcyclesShortComplex_shortExact C i (ih.2 (by omega))`.

Use `subsingleton_of_forall_eq 0 fun x => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Ext.covariant_sequence_exact₃ _ hS x rfl (@Subsingleton.elim _ (ih.1 (n + 1) (by omega)) _ _)`. Rewrite using `[@Subsingleton.elim _ (hX (i + 1) n (by omega)) y 0]`. Conclude with `Ext.zero_comp _ _ _ _ _`.
-/
theorem acyclicityLemma_depth_differentialCokernels_finiteLength [IsLocalRing R] (g : ℕ)
    (hX : ∀ i n, n < g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (C.X i) n))
    (hH : ∀ i, IsFiniteLength R (C.homology i)) (i : ℕ) :
    (∀ n, n + i < g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (C.opcycles i) n)) ∧
      (i < g → IsZero (C.homology i)) := by
  have key : ∀ i, (∀ n, n + i < g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (C.opcycles i) n)) →
      i < g → IsZero (C.homology i) := by
    intro i h hi
    have h0 : Subsingleton (Abelian.Ext.{0} (C.homology i) (C.opcycles i) 0) :=
      subsingleton_ext_of_isFiniteLength _ 0 (h 0 (by omega)) _ (hH i)
    have h1 : Subsingleton (C.homology i ⟶ C.opcycles i) :=
      Ext.addEquiv₀.subsingleton_congr.mp h0
    exact IsZero.of_mono_eq_zero (C.homologyι i) (Subsingleton.elim _ _)
  induction i with
  | zero =>
    refine (fun h => ⟨h, key 0 h⟩) fun n hn => ?_
    have := isIso_pOpcycles_zero C
    have := hX 0 n (by omega)
    refine subsingleton_of_forall_eq 0 fun x => ?_
    rw [← Ext.comp_mk₀_id x, ← IsIso.inv_hom_id (C.pOpcycles 0), ← Ext.mk₀_comp_mk₀,
      ← Ext.comp_assoc_of_second_deg_zero, Subsingleton.elim (x.comp _ _) 0, Ext.zero_comp]
  | succ i ih =>
    refine (fun h => ⟨h, key (i + 1) h⟩) fun n hn => ?_
    have hS := opcyclesShortComplex_shortExact C i (ih.2 (by omega))
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS x rfl
      (@Subsingleton.elim _ (ih.1 (n + 1) (by omega)) _ _)
    rw [@Subsingleton.elim _ (hX (i + 1) n (by omega)) y 0]
    exact Ext.zero_comp _ _ _ _ _

/- English proof (translation)
Establish `step : ∀ i, IsZero (C.homology i) → ∀ n, Module.length R (Abelian.Ext.{0} (C.opcycles (i + 1)) Y (n + 1)) = Module.length R (Abelian.Ext.{0} (C.opcycles i) Y n ⧸ LinearMap.range ((Ext.mk₀ (C.fromOpcycles i (i + 1))).precompOfLinear R Y (zero_add n)))`. Introduce `i hi n`. Establish `hS` using `opcyclesShortComplex_shortExact C i hi`. Set `δ : Abelian.Ext.{0} (C.opcycles i) Y n →ₗ[R] Abelian.Ext.{0} (C.opcycles (i + 1)) Y (n + 1)` to `hS.extClass.precompOfLinear R Y (add_comm 1 n)`. Establish `hsurj : Function.Surjective δ` using `fun x => by`.

Establish `: Projective (opcyclesShortComplex C i).X₂` using `hP (i + 1)`. Conclude with `Ext.contravariant_sequence_exact₃ hS Y x (Ext.eq_zero_of_projective _) (add_comm 1 n)`. Establish `hker : LinearMap.ker δ = LinearMap.range ((Ext.mk₀ (C.fromOpcycles i (i + 1))).precompOfLinear R Y (zero_add n))`. Use extensionality with `x`. Use `⟨fun hx => Ext.contravariant_sequence_exact₁ hS Y x (add_comm 1 n) hx, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨y, rfl⟩`. Conclude with `hS.extClass_comp_assoc y (h := add_comm 1 n)`. Rewrite using `[← hker]`. Conclude with `(δ.quotKerEquivOfSurjective hsurj).length_eq.symm`. Proceed by induction on `j with`.

Consider the case `zero => exact step 0 (hH 0 (by omega)) 0`. Consider the case `succ j ih`. Rewrite using `[step (j + 1) (hH _ (by omega)) (j + 1), ← ih fun i hi => hH i (by omega)]`. Use `(Submodule.quotEquivOfEqBot _ ?_).length_eq` and prove the remaining obligations. Rewrite using `[LinearMap.range_eq_bot]`.

Use extensionality with `x`. Use `hP (j + 1 + 1)` as an intermediate fact. Rewrite using `[Ext.eq_zero_of_projective x]`. Simplify using the standard rewrite rules.
-/
theorem length_ext_opcycles (Y : ModuleCat.{0} R) (hP : ∀ i, Projective (C.X i)) (j : ℕ)
    (hH : ∀ i < j + 1, IsZero (C.homology i)) :
    Module.length R (Abelian.Ext.{0} (C.opcycles (j + 1)) Y (j + 1)) =
      Module.length R (Abelian.Ext.{0} (C.opcycles 0) Y 0 ⧸ LinearMap.range
        ((Ext.mk₀ (C.fromOpcycles 0 1)).precompOfLinear R Y (zero_add 0))) := by
  have step : ∀ i, IsZero (C.homology i) → ∀ n,
      Module.length R (Abelian.Ext.{0} (C.opcycles (i + 1)) Y (n + 1)) =
      Module.length R (Abelian.Ext.{0} (C.opcycles i) Y n ⧸ LinearMap.range
        ((Ext.mk₀ (C.fromOpcycles i (i + 1))).precompOfLinear R Y (zero_add n))) := by
    intro i hi n
    have hS := opcyclesShortComplex_shortExact C i hi
    let δ : Abelian.Ext.{0} (C.opcycles i) Y n →ₗ[R]
        Abelian.Ext.{0} (C.opcycles (i + 1)) Y (n + 1) :=
      hS.extClass.precompOfLinear R Y (add_comm 1 n)
    have hsurj : Function.Surjective δ := fun x => by
      have : Projective (opcyclesShortComplex C i).X₂ := hP (i + 1)
      exact Ext.contravariant_sequence_exact₃ hS Y x (Ext.eq_zero_of_projective _) (add_comm 1 n)
    have hker : LinearMap.ker δ = LinearMap.range
        ((Ext.mk₀ (C.fromOpcycles i (i + 1))).precompOfLinear R Y (zero_add n)) := by
      ext x
      refine ⟨fun hx => Ext.contravariant_sequence_exact₁ hS Y x (add_comm 1 n) hx, ?_⟩
      rintro ⟨y, rfl⟩
      exact hS.extClass_comp_assoc y (h := add_comm 1 n)
    rw [← hker]
    exact (δ.quotKerEquivOfSurjective hsurj).length_eq.symm
  induction j with
  | zero => exact step 0 (hH 0 (by omega)) 0
  | succ j ih =>
    rw [step (j + 1) (hH _ (by omega)) (j + 1), ← ih fun i hi => hH i (by omega)]
    refine (Submodule.quotEquivOfEqBot _ ?_).length_eq
    rw [LinearMap.range_eq_bot]
    ext x
    have := hP (j + 1 + 1)
    rw [Ext.eq_zero_of_projective x]
    simp

/- English proof (translation)
Use `isIso_pOpcycles_zero C` as an intermediate fact. Set `e (X : ModuleCat.{0} R) : Abelian.Ext.{0} X (ModuleCat.of R R) 0 ≃ₗ[R] Module.Dual R X` to `(Ext.linearEquiv₀ (R := R)).trans ModuleCat.homLinearEquiv`. Establish `he (X : ModuleCat.{0} R) (f : X ⟶ ModuleCat.of R R) : e X (Ext.mk₀ f) = f.hom`. Rewrite using `[← LinearEquiv.eq_symm_apply]`. Both sides reduce to the same expression.

Set `φ` to `(extCongrLeft (asIso (C.pOpcycles 0)) (ModuleCat.of R R) 0).trans (e (C.X 0))`. Establish `hφ (f : C.X 1 ⟶ ModuleCat.of R R) : φ ((Ext.mk₀ (C.fromOpcycles 0 1)).precompOfLinear R (ModuleCat.of R R) (zero_add 0) (Ext.mk₀ f)) = (C.d 0 1).hom.dualMap f.hom`. Express the relevant statement in the definitionally equal form `e _ ((Ext.mk₀ (C.pOpcycles 0)).comp ((Ext.mk₀ _).comp (Ext.mk₀ f) (zero_add 0)) (zero_add 0)) = _`. Rewrite using `[Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, he, HomologicalComplex.p_fromOpcycles_assoc]`. Both sides reduce to the same expression.

Use `(Submodule.Quotient.equiv _ _ φ ?_).length_eq` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨_, ⟨x, rfl⟩, rfl⟩`. Take `⟨f, rfl⟩` from `(Ext.mk₀_bijective _ _).2 x`. Conclude with `⟨f.hom, (hφ f).symm⟩`.

Introduce and unpack `_ ⟨f, rfl⟩`. Conclude with `⟨_, ⟨Ext.mk₀ (ModuleCat.ofHom f), rfl⟩, hφ (ModuleCat.ofHom f)⟩`.
-/
theorem length_ext_zero_quot :
    Module.length R (Abelian.Ext.{0} (C.opcycles 0) (ModuleCat.of R R) 0 ⧸ LinearMap.range
        ((Ext.mk₀ (C.fromOpcycles 0 1)).precompOfLinear R (ModuleCat.of R R) (zero_add 0))) =
      Module.length R (Module.Dual R (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) := by
  have := isIso_pOpcycles_zero C
  let e (X : ModuleCat.{0} R) : Abelian.Ext.{0} X (ModuleCat.of R R) 0 ≃ₗ[R] Module.Dual R X :=
    (Ext.linearEquiv₀ (R := R)).trans ModuleCat.homLinearEquiv
  have he (X : ModuleCat.{0} R) (f : X ⟶ ModuleCat.of R R) : e X (Ext.mk₀ f) = f.hom := by
    rw [← LinearEquiv.eq_symm_apply]
    rfl
  let φ := (extCongrLeft (asIso (C.pOpcycles 0)) (ModuleCat.of R R) 0).trans (e (C.X 0))
  have hφ (f : C.X 1 ⟶ ModuleCat.of R R) :
      φ ((Ext.mk₀ (C.fromOpcycles 0 1)).precompOfLinear R (ModuleCat.of R R) (zero_add 0)
        (Ext.mk₀ f)) = (C.d 0 1).hom.dualMap f.hom := by
    change e _ ((Ext.mk₀ (C.pOpcycles 0)).comp
      ((Ext.mk₀ _).comp (Ext.mk₀ f) (zero_add 0)) (zero_add 0)) = _
    rw [Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, he, HomologicalComplex.p_fromOpcycles_assoc]
    rfl
  refine (Submodule.Quotient.equiv _ _ φ ?_).length_eq
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
    exact ⟨f.hom, (hφ f).symm⟩
  · rintro _ ⟨f, rfl⟩
    exact ⟨_, ⟨Ext.mk₀ (ModuleCat.ofHom f), rfl⟩, hφ (ModuleCat.ofHom f)⟩

end Complex

end FiniteLengthComplex

open FiniteLengthComplex in

/- English proof (translation)
Introduce `O _ _ g hg C hF hZ hH ⟨e⟩`. Establish `hk` using `subsingleton_ext_residue g hg`. Establish `hlt : ∀ i < g, IsZero (C.homology i)` using `fun i hi => (acyclicityLemma_depth_differentialCokernels_finiteLength C g (fun j n hn => by`. Use `(hF j).1` as an intermediate fact. Use `(hF j).2` as an intermediate fact.

Conclude with `subsingleton_ext_free _ n (hk n hn.ne) _) hH i).2 hi`. Use `⟨fun i hi => ?_, ?_⟩` and prove the remaining obligations. Break down `lt_or_gt_of_ne hi with h | h` into its components or cases. Conclude with `hlt i h`. Conclude with `IsZero.of_mono (C.homologyι i) (IsZero.of_epi (C.pOpcycles i) (hZ i h))`.

Establish `hres : Module.length O (IsLocalRing.ResidueField O) = 1`. Establish `: IsSimpleModule O (IsLocalRing.ResidueField O)` using `isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal O, ⟨LinearEquiv.refl _ _⟩⟩`. Conclude with `Module.length_eq_one _ _`. Establish `h0` using `(length_ext_zero_quot C).trans (e.length_eq.trans hres)`. Establish `h1 : Module.length O (Abelian.Ext.{0} (C.opcycles g) (ModuleCat.of O O) g) = 1`.

Consider the cases of `g with`. Consider the case `zero`. Rewrite using `[← h0]`. Use `(Submodule.quotEquivOfEqBot _ ?_).length_eq.symm` and prove the remaining obligations. Rewrite using `[LinearMap.range_eq_bot]`.

Use extensionality with `x`. Use `subsingleton_ext_of_isZero_left (hZ 1 one_pos) (ModuleCat.of O O) 0` as an intermediate fact. Rewrite using `[Subsingleton.elim x 0]`. Simplify using the standard rewrite rules. Consider the case `succ j`.

Rewrite using `[length_ext_opcycles C _ (fun i => by`. Use `(hF i).1` as an intermediate fact. Use the proof step `infer_instance) j hlt, h0]`. Use `C.isIso_homologyι g (g + 1) (by simp) ((hZ _ (by omega)).eq_zero_of_tgt _)` as an intermediate fact. Rewrite `h1` using `[(extCongrLeft (asIso (C.homologyι g)) _ g).length_eq]`.

Establish `h2 : 1 = Module.length O (C.homology g) * Module.length O (Abelian.Ext.{0} (ModuleCat.of O (O ⧸ maximalIdeal O)) (ModuleCat.of O O) g)` using `h1.symm.trans (length_ext_of_isFiniteLength _ g hk _ (hH g))`. Generalize the expression as in `Module.length O (C.homology g) = a at h2 ⊢`. Generalize the expression as in `Module.length O (Abelian.Ext.{0} (ModuleCat.of O (O ⧸ maximalIdeal O)) (ModuleCat.of O O) g) = b at h2`. Establish `hb : b ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at h2`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h2`. Use `le_antisymm ?_ (Order.one_le_iff_ne_zero.mpr ha)` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem homology_of_free_complex_of_isFiniteLength :
    ∀ (O : Type) [CommRing O] [IsRegularLocalRing O] (g : ℕ), ringKrullDim O = g →
      ∀ C : CochainComplex (ModuleCat.{0} O) ℕ,
        (∀ i, Module.Free O (C.X i) ∧ Module.Finite O (C.X i)) → (∀ i, g < i → IsZero (C.X i)) →
        (∀ i, IsFiniteLength O (C.homology i)) →
        Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O]
          IsLocalRing.ResidueField O) →
        (∀ i, i ≠ g → IsZero (C.homology i)) ∧ Module.length O (C.homology g) = 1 := by
  intro O _ _ g hg C hF hZ hH ⟨e⟩
  have hk := subsingleton_ext_residue g hg
  have hlt : ∀ i < g, IsZero (C.homology i) := fun i hi =>
    (acyclicityLemma_depth_differentialCokernels_finiteLength C g (fun j n hn => by
      have := (hF j).1
      have := (hF j).2
      exact subsingleton_ext_free _ n (hk n hn.ne) _) hH i).2 hi
  refine ⟨fun i hi => ?_, ?_⟩
  · rcases lt_or_gt_of_ne hi with h | h
    · exact hlt i h
    · exact IsZero.of_mono (C.homologyι i) (IsZero.of_epi (C.pOpcycles i) (hZ i h))
  have hres : Module.length O (IsLocalRing.ResidueField O) = 1 := by
    have : IsSimpleModule O (IsLocalRing.ResidueField O) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal O, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  have h0 := (length_ext_zero_quot C).trans (e.length_eq.trans hres)
  have h1 : Module.length O (Abelian.Ext.{0} (C.opcycles g) (ModuleCat.of O O) g) = 1 := by
    cases g with
    | zero =>
      rw [← h0]
      refine (Submodule.quotEquivOfEqBot _ ?_).length_eq.symm
      rw [LinearMap.range_eq_bot]
      ext x
      have := subsingleton_ext_of_isZero_left (hZ 1 one_pos) (ModuleCat.of O O) 0
      rw [Subsingleton.elim x 0]
      simp
    | succ j =>
      rw [length_ext_opcycles C _ (fun i => by
        have := (hF i).1
        infer_instance) j hlt, h0]
  have := C.isIso_homologyι g (g + 1) (by simp) ((hZ _ (by omega)).eq_zero_of_tgt _)
  rw [(extCongrLeft (asIso (C.homologyι g)) _ g).length_eq] at h1
  have h2 : 1 = Module.length O (C.homology g) * Module.length O (Abelian.Ext.{0}
      (ModuleCat.of O (O ⧸ maximalIdeal O)) (ModuleCat.of O O) g) :=
    h1.symm.trans (length_ext_of_isFiniteLength _ g hk _ (hH g))
  generalize Module.length O (C.homology g) = a at h2 ⊢
  generalize Module.length O (Abelian.Ext.{0} (ModuleCat.of O (O ⧸ maximalIdeal O))
    (ModuleCat.of O O) g) = b at h2
  have hb : b ≠ 0 := by
    rintro rfl
    simp at h2
  have ha : a ≠ 0 := by
    rintro rfl
    simp at h2
  refine le_antisymm ?_ (Order.one_le_iff_ne_zero.mpr ha)
  calc a = a * 1 := (mul_one a).symm
    _ ≤ a * b := by gcongr; exact Order.one_le_iff_ne_zero.mpr hb
    _ = 1 := h2.symm

end GlobalTheory
