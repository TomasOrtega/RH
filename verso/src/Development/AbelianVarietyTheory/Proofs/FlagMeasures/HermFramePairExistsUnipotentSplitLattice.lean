import Mathlib
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.SplitLift

section Lattice

variable {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/- English proof (translation)
Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K (M : Set V) x hx`. Rewrite `ht` using `[Submodule.span_eq]`. Conclude with `⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩`.
-/
theorem exists_smul_mem (M : Submodule R V) {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : R, d ≠ 0 ∧ d • x ∈ M := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K (M : Set V) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩

/- English proof (translation)
Use `set M : Submodule R V := Λ ⊓ S.restrictScalars R with hM`. Establish `hMfg : M.FG` using `by haveI : Module.Finite R Λ := Module.Finite.iff_fg.2 hfg`. Conclude with `(Module.Finite.iff_fg (N := M)).1 (Module.Finite.of_injective (Submodule.inclusion (inf_le_left : M ≤ Λ)) (Submodule.inclusion_injective _))`. Use `haveI : Module.Finite R M := Module.Finite.iff_fg.2 hMfg`. Set `π : M →ₗ[R] (V ⧸ I)` to `(I.mkQ.restrictScalars R) ∘ₗ M.subtype`.

Use `haveI : Module.IsTorsionFree R (V ⧸ I) := Module.IsTorsionFree.trans K`. Use `haveI : Module.Finite R (LinearMap.range π) := inferInstance`. Use `haveI : Module.Flat R (LinearMap.range π) := inferInstance`. Use `haveI : Module.FinitePresentation R (LinearMap.range π) := Module.finitePresentation_of_finite R _`. Use `haveI : Module.Projective R (LinearMap.range π) := Module.Flat.projective_of_finitePresentation`.

Take `⟨σ, hσ⟩` from `Module.projective_lifting_property π.rangeRestrict LinearMap.id π.surjective_rangeRestrict`. Establish `hσ' : ∀ y, π (σ y) = (y : V ⧸ I)` using `fun y => by`. Use `congrArg Subtype.val (LinearMap.congr_fun hσ y)` as an intermediate fact. Simplify using `using this`. Use `set N : Submodule R V := LinearMap.range (M.subtype ∘ₗ σ) with hN`.

Establish `key : ∀ l ∈ Λ, l ∈ S → ∃ w ∈ Λ, w ∈ Submodule.span K (N : Set V) ∧ l - w ∈ I`. Introduce `l hl hlS`. Set `y : LinearMap.range π` to `⟨π ⟨l, hl, hlS⟩, _, rfl⟩`. Use `⟨(σ y : V), (σ y).2.1, Submodule.subset_span ⟨y, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.eq]`.

Conclude with `(hσ' y).symm`. Establish `hinj : ∀ d : R, d ≠ 0 → algebraMap R K d ≠ 0` using `fun d hd => (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hd`. Use `⟨Submodule.span K (N : Set V), ?_, ?_, ?_, key⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨y, rfl⟩`.

Conclude with `(σ y).2.2`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `x ⟨hx, hxI⟩`. Take `⟨d, hd, y, hy⟩` from `exists_smul_mem N hx`. Establish `hy' : ((σ y : M) : V) = d • x` using `hy`.

Establish `h0 : (y : V ⧸ I) = 0`. Rewrite using `[← hσ' y]`. Use `show I.mkQ ((σ y : M) : V) = 0`. Rewrite using `[hy', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `I.smul_of_tower_mem d hxI`.

Establish `h1 : y = 0` using `Subtype.ext h0`. Rewrite `hy'` using `[h1, map_zero, ← algebraMap_smul K d x]`. Conclude with `(smul_eq_zero.1 hy'.symm).resolve_left (hinj d hd)`. Introduce `x hx`. Take `⟨d, hd, hdx⟩` from `exists_smul_mem (K := K) Λ (x := x) (by rw [hsp]; trivial)`.

Take `⟨w, -, hw, hwI⟩` from `key _ hdx (S.smul_of_tower_mem d hx)`. Establish `h1 : d • x ∈ Submodule.span K (N : Set V) ⊔ I` using `Submodule.mem_sup.2 ⟨w, hw, _, hwI, by abel⟩`. Rewrite `h1` using `[← algebraMap_smul K d x]`. Conclude with `(Submodule.smul_mem_iff _ (hinj d hd)).1 h1`.
-/
theorem exists_split (Λ : Submodule R V) (hfg : Λ.FG) (hsp : Submodule.span K (Λ : Set V) = ⊤)
    (S I : Submodule K V) :
    ∃ W : Submodule K V, W ≤ S ∧ W ⊓ I = ⊥ ∧ S ≤ W ⊔ I ∧
      ∀ l ∈ Λ, l ∈ S → ∃ w ∈ Λ, w ∈ W ∧ l - w ∈ I := by
  set M : Submodule R V := Λ ⊓ S.restrictScalars R with hM
  have hMfg : M.FG := by
    haveI : Module.Finite R Λ := Module.Finite.iff_fg.2 hfg
    exact (Module.Finite.iff_fg (N := M)).1
      (Module.Finite.of_injective (Submodule.inclusion (inf_le_left : M ≤ Λ))
        (Submodule.inclusion_injective _))
  haveI : Module.Finite R M := Module.Finite.iff_fg.2 hMfg
  let π : M →ₗ[R] (V ⧸ I) := (I.mkQ.restrictScalars R) ∘ₗ M.subtype
  haveI : Module.IsTorsionFree R (V ⧸ I) := Module.IsTorsionFree.trans K
  haveI : Module.Finite R (LinearMap.range π) := inferInstance
  haveI : Module.Flat R (LinearMap.range π) := inferInstance
  haveI : Module.FinitePresentation R (LinearMap.range π) :=
    Module.finitePresentation_of_finite R _
  haveI : Module.Projective R (LinearMap.range π) := Module.Flat.projective_of_finitePresentation
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π.rangeRestrict LinearMap.id
    π.surjective_rangeRestrict
  have hσ' : ∀ y, π (σ y) = (y : V ⧸ I) := fun y => by
    have := congrArg Subtype.val (LinearMap.congr_fun hσ y)
    simpa using this
  set N : Submodule R V := LinearMap.range (M.subtype ∘ₗ σ) with hN
  have key : ∀ l ∈ Λ, l ∈ S → ∃ w ∈ Λ, w ∈ Submodule.span K (N : Set V) ∧ l - w ∈ I := by
    intro l hl hlS
    let y : LinearMap.range π := ⟨π ⟨l, hl, hlS⟩, _, rfl⟩
    refine ⟨(σ y : V), (σ y).2.1, Submodule.subset_span ⟨y, rfl⟩, ?_⟩
    rw [← Submodule.Quotient.eq]
    exact (hσ' y).symm
  have hinj : ∀ d : R, d ≠ 0 → algebraMap R K d ≠ 0 := fun d hd =>
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hd
  refine ⟨Submodule.span K (N : Set V), ?_, ?_, ?_, key⟩
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    exact (σ y).2.2
  · rw [eq_bot_iff]
    rintro x ⟨hx, hxI⟩
    obtain ⟨d, hd, y, hy⟩ := exists_smul_mem N hx
    have hy' : ((σ y : M) : V) = d • x := hy
    have h0 : (y : V ⧸ I) = 0 := by
      rw [← hσ' y]
      show I.mkQ ((σ y : M) : V) = 0
      rw [hy', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact I.smul_of_tower_mem d hxI
    have h1 : y = 0 := Subtype.ext h0
    rw [h1, map_zero, ← algebraMap_smul K d x] at hy'
    exact (smul_eq_zero.1 hy'.symm).resolve_left (hinj d hd)
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem (K := K) Λ (x := x) (by rw [hsp]; trivial)
    obtain ⟨w, -, hw, hwI⟩ := key _ hdx (S.smul_of_tower_mem d hx)
    have h1 : d • x ∈ Submodule.span K (N : Set V) ⊔ I :=
      Submodule.mem_sup.2 ⟨w, hw, _, hwI, by abel⟩
    rw [← algebraMap_smul K d x] at h1
    exact (Submodule.smul_mem_iff _ (hinj d hd)).1 h1

end Lattice

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

section Geometry
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Rewrite using `[← H.herm, h, star_zero]`.
-/
theorem flip_zero {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

/- English proof (translation)
Rewrite using `[wSp, mem_perp_iff]`. Conclude with `⟨fun h y hy => flip_zero (h y hy), fun h y hy => flip_zero (h y hy)⟩`.
-/
theorem mem_wSp_iff (F F' : FlagD H r) (w : V) : w ∈ wSp F F' ↔ ∀ y ∈ V0 F F', H.B y w = 0 := by
  rw [wSp, mem_perp_iff]
  exact ⟨fun h y hy => flip_zero (h y hy), fun h y hy => flip_zero (h y hy)⟩

/- English proof (translation)
The claim follows from `le_sup_left`.
-/
theorem hermFlagPair_isotropic_sup_le_commonSpace (F F' : FlagD H r) : F.X ⊔ F'.X ≤ V0 F F' := le_sup_left

/- English proof (translation)
The claim follows from `(inf_le_left.trans le_sup_left).trans (hermFlagPair_isotropic_sup_le_commonSpace F F')`.
-/
theorem isotropicMeet_le_jointSpan (F F' : FlagD H r) : II F F' ≤ V0 F F' :=
  (inf_le_left.trans le_sup_left).trans (hermFlagPair_isotropic_sup_le_commonSpace F F')

/- English proof (translation)
Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))`. Consider the case `cast b`. Conclude with `hermFlagPair_isotropic_sup_le_commonSpace F F' (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩))`.
-/
theorem flag_vector_mem_base_lattice (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))
  | cast b =>
    exact hermFlagPair_isotropic_sup_le_commonSpace F F' (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩))

/- English proof (translation)
Establish `: F.X ≤ LinearMap.ker (H.B.flip w)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, -, rfl⟩`. Conclude with `hw _`. Conclude with `this hx`.
-/
theorem X_perp (F : FlagD H r) {w x : V} (hw : ∀ a : Fin (r + 1), H.B (F.e a) w = 0) (hx : x ∈ F.X) :
    H.B x w = 0 := by
  have : F.X ≤ LinearMap.ker (H.B.flip w) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    exact hw _
  exact this hx

/- English proof (translation)
Take `⟨-, -, -, -, -, h6, -, -, h9⟩` from `h`. Introduce `w hw hww`. Take `⟨x, hx, hwx⟩` from `h9 w hw`. Establish `h1 : H.B (w - x) (w - x) = 0`. Establish `a1 : H.B x (w - x) = 0` using `hwx x (hermFlagPair_isotropic_sup_le_commonSpace F F' (Submodule.mem_sup_right hx))`.

Establish `a2 : H.B w x = 0` using `flip_zero (X_perp F' hw hx)`. Rewrite using `[map_sub H.B, LinearMap.sub_apply, a1, map_sub, hww, a2]`. Simplify using the standard rewrite rules. Establish `h2 : w - x ∈ F.X` using `hF _ (fun a => hwx _ (flag_vector_mem_base_lattice F F' a)) h1`. Establish `h3 : w - x ∈ F'.X` using `((h6 _ h2).1 hwx).2`.

Simplify using `using add_mem h3 hx`.
-/
theorem aniso_right {F F' : FlagD H r} {j : ℕ} {hj : j ≤ r} {c : K} (h : NFFull F F' j hj c)
    (hF : F.Aniso) : F'.Aniso := by
  obtain ⟨-, -, -, -, -, h6, -, -, h9⟩ := h
  intro w hw hww
  obtain ⟨x, hx, hwx⟩ := h9 w hw
  have h1 : H.B (w - x) (w - x) = 0 := by
    have a1 : H.B x (w - x) = 0 := hwx x (hermFlagPair_isotropic_sup_le_commonSpace F F' (Submodule.mem_sup_right hx))
    have a2 : H.B w x = 0 := flip_zero (X_perp F' hw hx)
    rw [map_sub H.B, LinearMap.sub_apply, a1, map_sub, hww, a2]
    simp
  have h2 : w - x ∈ F.X := hF _ (fun a => hwx _ (flag_vector_mem_base_lattice F F' a)) h1
  have h3 : w - x ∈ F'.X := ((h6 _ h2).1 hwx).2
  simpa using add_mem h3 hx

end Geometry

/- English proof (translation)
Establish `hu : ∀ y ∈ wSp F F', y ∈ uPerp F F'` using `fun y hy => (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (hermFlagPair_isotropic_sup_le_commonSpace F F' hx)`. Establish `hp : ∀ y ∈ wSp F F', y ∈ perp H (II F F')` using `fun y hy => (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (isotropicMeet_le_jointSpan F F' hx)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `y ⟨⟨hy1, -⟩, hy3⟩`. Take `⟨l, ⟨hl, -⟩, x, hx, rfl⟩` from `Submodule.mem_sup.1 hy1`.

Use `Submodule.mem_sup.2 ⟨l, ⟨hl, ?_⟩, x, hx, rfl⟩` and prove the remaining obligations. Establish `: l + x - x ∈ wSp F F'` using `sub_mem hy3 (hI hx)`. Simplify using `using this`. Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce and unpack `l ⟨hl, hw⟩`.

Conclude with `⟨⟨Submodule.mem_sup_left ⟨hl, hp l hw⟩, hu l hw⟩, hw⟩`. Introduce `x hx`. Conclude with `⟨⟨Submodule.mem_sup_right hx, hu x (hI hx)⟩, hI hx⟩`.
-/
theorem latTh_eq (F F' : FlagD H r) (hI : II F F' ≤ wSp F F') (Λ : Submodule (𝓞 K) V) :
    latTh F F' Λ = (Λ ⊓ rs (𝓞 K) (wSp F F')) ⊔ rs (𝓞 K) (II F F') := by
  have hu : ∀ y ∈ wSp F F', y ∈ uPerp F F' := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (hermFlagPair_isotropic_sup_le_commonSpace F F' hx)
  have hp : ∀ y ∈ wSp F F', y ∈ perp H (II F F') := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (isotropicMeet_le_jointSpan F F' hx)
  apply le_antisymm
  · rintro y ⟨⟨hy1, -⟩, hy3⟩
    obtain ⟨l, ⟨hl, -⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 hy1
    refine Submodule.mem_sup.2 ⟨l, ⟨hl, ?_⟩, x, hx, rfl⟩
    have : l + x - x ∈ wSp F F' := sub_mem hy3 (hI hx)
    simpa using this
  · refine sup_le ?_ ?_
    · rintro l ⟨hl, hw⟩
      exact ⟨⟨Submodule.mem_sup_left ⟨hl, hp l hw⟩, hu l hw⟩, hw⟩
    · intro x hx
      exact ⟨⟨Submodule.mem_sup_right hx, hu x (hI hx)⟩, hI hx⟩

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ H hK r N g Λ _ hΛ`. Take `⟨hfull, hlift, -, -, -, -, hw, -⟩` from `GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N`. Establish `hL` using `(isLatMod_top_bot_iff Λ).1 hΛ.1.1.1`. Take `⟨W, hWS, hWI, hSW, hWΛ⟩` from `exists_split Λ hL.fg hL.span_eq_top (wSp N.F N.F') (II N.F N.F')`. Establish `hW : IsLift N.F N.F' W` using `⟨fun w h => (mem_wSp_iff _ _ w).1 (hWS h), hWI, fun w h => hSW ((mem_wSp_iff _ _ w).2 h)⟩`.

Take `⟨σ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Establish `hA : N.F.Aniso`. Introduce `w h1 h2`. Assume the negation of the conclusion as `hne`. Use `N.posdef σ w h1 hne` as an intermediate fact.

Rewrite `this` using `[h2]`. Simplify using `at this`. Take `⟨f, hf, hf', hfix, hmap⟩` from `Formalism.HermitianLatticeCounting.P.complementLiftTransitive K V H r N.F N.F' W N.Wt ⟨1, by rw [star_one]; norm_num⟩ hA (aniso_right hfull hA) hW hlift`. Set `s : V ≃ₗ[K] V` to `LinearEquiv.ofBijective f hf.2.1`. Use `⟨s, Subgroup.subset_closure ⟨hf, hf'⟩, ?_⟩` and prove the remaining obligations.

Establish `hI : II N.F N.F' ≤ wSp N.F N.F'` using `by rw [hw]; exact le_sup_right`. Establish `hWt : N.Wt ≤ wSp N.F N.F'` using `by rw [hw]; exact le_sup_left`. Rewrite using `[NF.Split, latTh_eq _ _ hI]`. Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le ?_ le_sup_right` and prove the remaining obligations.

Introduce and unpack `y ⟨hy, hyw⟩`. Take `⟨l, hl, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists y s Λ).1 hy`. Establish `hlw : l ∈ wSp N.F N.F'`. Use `(mem_wSp_iff _ _ l).2 fun y hy => ?_` and prove the remaining obligations. Rewrite using `[← hf.1, hfix y hy]`.

Conclude with `(mem_wSp_iff _ _ _).1 hyw y hy`. Take `⟨w, hw1, hw2, hw3⟩` from `hWΛ l hl hlw`. Use `Submodule.mem_sup.2 ⟨f w, ⟨Submodule.smul_mem_pointwise_smul w s Λ hw1, ?_⟩, l - w, hw3, ?_⟩` and prove the remaining obligations. Use `show f w ∈ N.Wt`. Rewrite using `[← hmap]`.

Conclude with `⟨w, hw2, rfl⟩`. Use `show f w + (l - w) = f l`. Rewrite using `[← hfix _ (isotropicMeet_le_jointSpan _ _ hw3), map_sub]`. Normalize the expressions using the abelian group laws. Conclude with `sup_le_sup_right (inf_le_inf_left _ fun x hx => hWt hx) _`.
-/
theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ s ∈ N.R, N.Split (s • Λ) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ _ hΛ
  obtain ⟨hfull, hlift, -, -, -, -, hw, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  have hL := (isLatMod_top_bot_iff Λ).1 hΛ.1.1.1
  obtain ⟨W, hWS, hWI, hSW, hWΛ⟩ :=
    exists_split Λ hL.fg hL.span_eq_top (wSp N.F N.F') (II N.F N.F')
  have hW : IsLift N.F N.F' W :=
    ⟨fun w h => (mem_wSp_iff _ _ w).1 (hWS h), hWI, fun w h => hSW ((mem_wSp_iff _ _ w).2 h)⟩
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hA : N.F.Aniso := by
    intro w h1 h2
    by_contra hne
    have := N.posdef σ w h1 hne
    rw [h2] at this
    simp at this
  obtain ⟨f, hf, hf', hfix, hmap⟩ := Formalism.HermitianLatticeCounting.P.complementLiftTransitive K V H r N.F N.F' W N.Wt
    ⟨1, by rw [star_one]; norm_num⟩ hA (aniso_right hfull hA) hW hlift
  let s : V ≃ₗ[K] V := LinearEquiv.ofBijective f hf.2.1
  refine ⟨s, Subgroup.subset_closure ⟨hf, hf'⟩, ?_⟩
  have hI : II N.F N.F' ≤ wSp N.F N.F' := by rw [hw]; exact le_sup_right
  have hWt : N.Wt ≤ wSp N.F N.F' := by rw [hw]; exact le_sup_left
  rw [NF.Split, latTh_eq _ _ hI]
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rintro y ⟨hy, hyw⟩
    obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y s Λ).1 hy
    have hlw : l ∈ wSp N.F N.F' := by
      refine (mem_wSp_iff _ _ l).2 fun y hy => ?_
      rw [← hf.1, hfix y hy]
      exact (mem_wSp_iff _ _ _).1 hyw y hy
    obtain ⟨w, hw1, hw2, hw3⟩ := hWΛ l hl hlw
    refine Submodule.mem_sup.2 ⟨f w, ⟨Submodule.smul_mem_pointwise_smul w s Λ hw1, ?_⟩, l - w, hw3, ?_⟩
    · show f w ∈ N.Wt
      rw [← hmap]
      exact ⟨w, hw2, rfl⟩
    · show f w + (l - w) = f l
      rw [← hfix _ (isotropicMeet_le_jointSpan _ _ hw3), map_sub]
      abel
  · exact sup_le_sup_right (inf_le_inf_left _ fun x hx => hWt hx) _

end GlobalTheory.DegCnt.SplitLift
