import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.HermitianLattices.HermitianLatticesProofs.AutFinite

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StabFin

section Core

variable {E V : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]

/- English proof (translation)
Use `set W : Submodule E V := ⨅ u ∈ U, LinearMap.ker (hT u) with hWdef`. Establish `memW : ∀ y, y ∈ W ↔ ∀ x ∈ U, hT x y = 0` using `fun y => by`. Simplify using `[hWdef, Submodule.mem_iInf]`. Establish `hdisj : U ⊓ W = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce and unpack `x ⟨hxU, hxW⟩`. Assume the negation of the conclusion as `hx0`. Use `hpos x hxW hx0` as an intermediate fact. Rewrite `this` using `[(memW x).1 hxW x hxU]`. Simplify using `at this`.

Establish `hsup : U ⊔ W = ⊤`. Set `b` to `Module.finBasis E U`. Set `φ : V →ₗ[E] (Fin (Module.finrank E U) → E)` to `LinearMap.pi fun i => hT (b i : V)`. Establish `hker : LinearMap.ker φ ≤ W`. Introduce `y hy`.

Rewrite using `[memW]`. Introduce `x hx`. Establish `hy' : ∀ i, hT (b i : V) y = 0` using `fun i => congrFun (LinearMap.mem_ker.1 hy) i`. Establish `hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : V)`. Use `congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)` as an intermediate fact.

Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at this`. Conclude with `this.symm`. Rewrite using `[hx', map_sum, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy' i, smul_zero]`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker φ`. Establish `h2 : Module.finrank E (LinearMap.range φ) ≤ Module.finrank E U`. Use `(Submodule.finrank_le _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `h3` using `Submodule.finrank_mono hker`. Establish `h4` using `Submodule.finrank_sup_add_finrank_inf_eq U W`. Rewrite `h4` using `[hdisj, finrank_bot]`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Establish `h5` using `Submodule.finrank_le (U ⊔ W)`.

Use linear arithmetic over natural numbers and integers. Establish `hmul : ∀ v : V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ₀` using `fun v => by`. Establish `hv : v ∈ Submodule.span E (Λ₀ : Set V)` using `by rw [hΛ.span_eq_top]; trivial`. Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv`. Rewrite `ht` using `[Submodule.span_eq]`.

Conclude with `⟨t, nonZeroDivisors.ne_zero t.2, ht⟩`. Set `L : Submodule (𝓞 E) W` to `Λ₀.comap (W.subtype.restrictScalars (𝓞 E))`. Establish `hfg : L.FG`. Apply `Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars (𝓞 E)) Subtype.val_injective` to reduce the goal to its premises. Conclude with `hΛ.fg.of_le (Submodule.map_comap_le _ _)`.

Use `haveI : Submodule.IsLattice E L := ⟨hfg, by`. Rewrite using `[eq_top_iff]`. Introduce `w _`. Take `⟨d, hd0, hd⟩` from `hmul (w : V)`. Establish `hdw : d • w ∈ L` using `hd`.

Use `Submodule.smul_mem (Submodule.span E (L : Set W)) (algebraMap (𝓞 E) E d)⁻¹ (Submodule.subset_span hdw)` as an intermediate fact. Rewrite using `[← algebraMap_smul E d w, inv_smul_smul₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)] at this⟩` and apply the resulting hypothesis. Set `hW` to `hT.domRestrict₁₂ W W`. Establish `hposW : ∀ w : W, w ≠ 0 → 0 < Algebra.trace ℚ E (hW w w)` using `fun w hw => hpos w w.2 fun h0 => hw (Subtype.ext h0)`. Take `⟨N, hN⟩` from `hfg`.

Establish `hNL : ∀ n ∈ N, ((n : W) : V) ∈ Λ₀` using `fun n hn => by`. Establish `: n ∈ L` using `hN ▸ Submodule.subset_span hn`. Conclude with `this`. Establish `hpres : ∀ h : V ≃ₗ[E] V, h ∈ Formalism.HermitianLatticesTheory.isom hT → (∀ u ∈ U, h u = u) → ∀ w ∈ W, h w ∈ W`. Introduce `h hiso hfix w hw`.

Rewrite `hw`, the goal using `[memW]`. Introduce `x hx`. Rewrite using `[← hfix x hx, hiso x w]`. Conclude with `hw x hx`. Use `Set.Finite.of_finite_image (f := fun (h : V ≃ₗ[E] V) (n : N) => h ((n : W) : V)) ?_ ?_` and prove the remaining obligations.

Use `(Set.Finite.pi (t := fun n : N => Subtype.val '' {v : W | v ∈ L ∧ Algebra.trace ℚ E (hW v v) ≤ Algebra.trace ℚ E (hW (n : W) (n : W))}) fun n => (Formalism.HermitianLatticesTheory.autFinite_short hW hposW L _).image _).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, ⟨hiso, hfix, hlat⟩, rfl⟩ n _`. Use `⟨⟨h ((n : W) : V), hpres h hiso hfix _ (n : W).2⟩, ⟨?_, ?_⟩, rfl⟩` and prove the remaining obligations. Establish `hm : ((h : V →ₗ[E] V).restrictScalars (𝓞 E)) ((n : W) : V) ∈ Formalism.HermitianLatticesTheory.gmap h Λ₀` using `Submodule.mem_map_of_mem (hNL n n.2)`. Rewrite `hm` using `[hlat]`.

Conclude with `hm`. Use `show Algebra.trace ℚ E (hT (h ((n : W) : V)) (h ((n : W) : V))) ≤ Algebra.trace ℚ E (hT ((n : W) : V) ((n : W) : V))`. Rewrite using `[hiso]`. Introduce and unpack `h₁ ⟨-, hf1, -⟩ h₂ ⟨-, hf2, -⟩ heq`. Set `K : Submodule E V` to `LinearMap.ker ((h₁ : V →ₗ[E] V) - (h₂ : V →ₗ[E] V))`.

Establish `memK : ∀ x, x ∈ K ↔ h₁ x = h₂ x` using `fun x => by`. Simplify using `[K, LinearMap.mem_ker, sub_eq_zero]`. Establish `hLK : L ≤ (K.restrictScalars (𝓞 E)).comap (W.subtype.restrictScalars (𝓞 E))`. Rewrite using `[← hN]`. Use `Submodule.span_le.2 fun n hn => ?_` and prove the remaining obligations.

Use `show ((n : W) : V) ∈ K`. Rewrite using `[memK]`. Conclude with `congrFun heq ⟨n, hn⟩`. Establish `hWK : W ≤ K`. Introduce `w hw`.

Take `⟨d, hd0, hd⟩` from `hmul w`. Establish `h1 : (⟨d • w, W.smul_of_tower_mem d hw⟩ : W) ∈ L` using `hd`. Establish `h2 : d • w ∈ K` using `hLK h1`. Rewrite `h2` using `[← algebraMap_smul E d w]`. Conclude with `(Submodule.smul_mem_iff K ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)).1 h2`.

Establish `hUK : U ≤ K` using `fun u hu => by rw [memK, hf1 u hu, hf2 u hu]`. Establish `htop : ⊤ ≤ K` using `hsup ▸ sup_le hUK hWK`. Conclude with `LinearEquiv.ext fun x => (memK x).1 (htop trivial)`.
-/
theorem finite_of_fix (hT : V →ₗ⋆[E] V →ₗ[E] E) (U : Submodule E V)
    (hpos : ∀ x ∈ (⨅ u ∈ U, LinearMap.ker (hT u)), x ≠ 0 → 0 < Algebra.trace ℚ E (hT x x))
    (Λ₀ : Submodule (𝓞 E) V) (hΛ : Submodule.IsLattice E Λ₀) :
    {h : V ≃ₗ[E] V | h ∈ Formalism.HermitianLatticesTheory.isom hT ∧ (∀ u ∈ U, h u = u) ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite := by
  set W : Submodule E V := ⨅ u ∈ U, LinearMap.ker (hT u) with hWdef
  have memW : ∀ y, y ∈ W ↔ ∀ x ∈ U, hT x y = 0 := fun y => by
    simp [hWdef, Submodule.mem_iInf]
  have hdisj : U ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, hxW⟩
    by_contra hx0
    have := hpos x hxW hx0
    rw [(memW x).1 hxW x hxU] at this
    simp at this
  have hsup : U ⊔ W = ⊤ := by
    let b := Module.finBasis E U
    let φ : V →ₗ[E] (Fin (Module.finrank E U) → E) := LinearMap.pi fun i => hT (b i : V)
    have hker : LinearMap.ker φ ≤ W := by
      intro y hy
      rw [memW]
      intro x hx
      have hy' : ∀ i, hT (b i : V) y = 0 := fun i => congrFun (LinearMap.mem_ker.1 hy) i
      have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : V) := by
        have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      rw [hx', map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy' i, smul_zero]
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank E (LinearMap.range φ) ≤ Module.finrank E U := by
      refine (Submodule.finrank_le _).trans ?_
      simp
    have h3 := Submodule.finrank_mono hker
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hdisj, finrank_bot] at h4
    apply Submodule.eq_top_of_finrank_eq
    have h5 := Submodule.finrank_le (U ⊔ W)
    omega
  have hmul : ∀ v : V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ₀ := fun v => by
    have hv : v ∈ Submodule.span E (Λ₀ : Set V) := by rw [hΛ.span_eq_top]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv
    rw [Submodule.span_eq] at ht
    exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩
  let L : Submodule (𝓞 E) W := Λ₀.comap (W.subtype.restrictScalars (𝓞 E))
  have hfg : L.FG := by
    apply Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars (𝓞 E)) Subtype.val_injective
    exact hΛ.fg.of_le (Submodule.map_comap_le _ _)
  haveI : Submodule.IsLattice E L := ⟨hfg, by
    rw [eq_top_iff]
    intro w _
    obtain ⟨d, hd0, hd⟩ := hmul (w : V)
    have hdw : d • w ∈ L := hd
    have := Submodule.smul_mem (Submodule.span E (L : Set W)) (algebraMap (𝓞 E) E d)⁻¹
      (Submodule.subset_span hdw)
    rwa [← algebraMap_smul E d w, inv_smul_smul₀
      ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)] at this⟩
  let hW := hT.domRestrict₁₂ W W
  have hposW : ∀ w : W, w ≠ 0 → 0 < Algebra.trace ℚ E (hW w w) := fun w hw =>
    hpos w w.2 fun h0 => hw (Subtype.ext h0)
  obtain ⟨N, hN⟩ := hfg
  have hNL : ∀ n ∈ N, ((n : W) : V) ∈ Λ₀ := fun n hn => by
    have : n ∈ L := hN ▸ Submodule.subset_span hn
    exact this
  have hpres : ∀ h : V ≃ₗ[E] V, h ∈ Formalism.HermitianLatticesTheory.isom hT → (∀ u ∈ U, h u = u) → ∀ w ∈ W, h w ∈ W := by
    intro h hiso hfix w hw
    rw [memW] at hw ⊢
    intro x hx
    rw [← hfix x hx, hiso x w]
    exact hw x hx
  refine Set.Finite.of_finite_image (f := fun (h : V ≃ₗ[E] V) (n : N) => h ((n : W) : V)) ?_ ?_
  · refine (Set.Finite.pi (t := fun n : N => Subtype.val '' {v : W | v ∈ L ∧
        Algebra.trace ℚ E (hW v v) ≤ Algebra.trace ℚ E (hW (n : W) (n : W))})
      fun n => (Formalism.HermitianLatticesTheory.autFinite_short hW hposW L _).image _).subset ?_
    rintro _ ⟨h, ⟨hiso, hfix, hlat⟩, rfl⟩ n _
    refine ⟨⟨h ((n : W) : V), hpres h hiso hfix _ (n : W).2⟩, ⟨?_, ?_⟩, rfl⟩
    · have hm : ((h : V →ₗ[E] V).restrictScalars (𝓞 E)) ((n : W) : V) ∈ Formalism.HermitianLatticesTheory.gmap h Λ₀ :=
        Submodule.mem_map_of_mem (hNL n n.2)
      rw [hlat] at hm
      exact hm
    · show Algebra.trace ℚ E (hT (h ((n : W) : V)) (h ((n : W) : V))) ≤
        Algebra.trace ℚ E (hT ((n : W) : V) ((n : W) : V))
      rw [hiso]
  · rintro h₁ ⟨-, hf1, -⟩ h₂ ⟨-, hf2, -⟩ heq
    let K : Submodule E V := LinearMap.ker ((h₁ : V →ₗ[E] V) - (h₂ : V →ₗ[E] V))
    have memK : ∀ x, x ∈ K ↔ h₁ x = h₂ x := fun x => by
      simp [K, LinearMap.mem_ker, sub_eq_zero]
    have hLK : L ≤ (K.restrictScalars (𝓞 E)).comap (W.subtype.restrictScalars (𝓞 E)) := by
      rw [← hN]
      refine Submodule.span_le.2 fun n hn => ?_
      show ((n : W) : V) ∈ K
      rw [memK]
      exact congrFun heq ⟨n, hn⟩
    have hWK : W ≤ K := by
      intro w hw
      obtain ⟨d, hd0, hd⟩ := hmul w
      have h1 : (⟨d • w, W.smul_of_tower_mem d hw⟩ : W) ∈ L := hd
      have h2 : d • w ∈ K := hLK h1
      rw [← algebraMap_smul E d w] at h2
      exact (Submodule.smul_mem_iff K
        ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)).1 h2
    have hUK : U ≤ K := fun u hu => by rw [memK, hf1 u hu, hf2 u hu]
    have htop : ⊤ ≤ K := hsup ▸ sup_le hUK hWK
    exact LinearEquiv.ext fun x => (memK x).1 (htop trivial)

end Core

/- English proof (translation)
Introduce `D T T' F F' hpos Λ₀ hΛ`. Use `(finite_of_fix (VS D).hT (Xplus F ⊔ Xplus F') hpos Λ₀ hΛ).subset ?_` and prove the remaining obligations. Introduce and unpack `h ⟨⟨hiso, hF, hF'⟩, hlat⟩`. Use `⟨hiso, ?_, hlat⟩` and prove the remaining obligations. Establish `key : ∀ {T0 : D.host.E} (G : LFlag (VS D) D.R.rS T0), (∀ a, h (frame G a) = frame G a) → Xplus G ≤ LinearMap.ker ((h : (VS D).V →ₗ[D.host.E] (VS D).V) - LinearMap.id)`.

Introduce `T0 G hG`. Establish `he : ∀ i, h (G.fl.e i) = G.fl.e i` using `fun i => by`. Use `hG (Fin.castSucc i)` as an intermediate fact. Simplify `this` using `[frame, FlagG.fvec]`. Establish `hz : h G.fl.z = G.fl.z`.

Use `hG (Fin.last _)` as an intermediate fact. Simplify `this` using `[frame, FlagG.fvec]`. Use `show Submodule.span D.host.E (Set.range G.fl.e) ⊔ Submodule.span D.host.E {G.fl.z} ≤ _`. Use `sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Simplify using `[he i]`. Introduce `x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality. Simplify using `[hz]`.

Introduce `u hu`. Use `(sup_le (key F hF) (key F' hF')) hu` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Conclude with `this`.
-/
theorem stab_finite : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → {h | h ∈ H0 F F' ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite := by
  intro D T T' F F' hpos Λ₀ hΛ
  refine (finite_of_fix (VS D).hT (Xplus F ⊔ Xplus F') hpos Λ₀ hΛ).subset ?_
  rintro h ⟨⟨hiso, hF, hF'⟩, hlat⟩
  refine ⟨hiso, ?_, hlat⟩
  have key : ∀ {T0 : D.host.E} (G : LFlag (VS D) D.R.rS T0), (∀ a, h (frame G a) = frame G a) →
      Xplus G ≤ LinearMap.ker ((h : (VS D).V →ₗ[D.host.E] (VS D).V) - LinearMap.id) := by
    intro T0 G hG
    have he : ∀ i, h (G.fl.e i) = G.fl.e i := fun i => by
      have := hG (Fin.castSucc i)
      simpa [frame, FlagG.fvec] using this
    have hz : h G.fl.z = G.fl.z := by
      have := hG (Fin.last _)
      simpa [frame, FlagG.fvec] using this
    show Submodule.span D.host.E (Set.range G.fl.e) ⊔ Submodule.span D.host.E {G.fl.z} ≤ _
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨i, rfl⟩
      simp [he i]
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      simp [hz]
  intro u hu
  have := (sup_le (key F hF) (key F' hF')) hu
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.StabFin
