import Mathlib
import Development.ResolutionOfSingularities.Statements
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsClopen
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsChartNormalization
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NotSubsetOfDenseCompl

universe u

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace PositivityTheory.ResPlug.BlowupCentre

open FunctorialResolution FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Consider the cases of `o with`. Consider the case `none => simp at h`. Consider the case `some j0`. Distinguish the cases in `hb : P j0`. Simplify using `[hb] at h`.

Simplify using `[hb] at h`. Substitute `h` using the available equality. Conclude with `⟨rfl, hb⟩`.
-/
theorem eq_some_and_not_of_bind_ite_eq_some {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    {o : Option (Fin n)} {j : Fin n}
    (h : o.bind (fun j0 => if P j0 then none else some j0) = some j) : o = some j ∧ ¬ P j := by
  cases o with
  | none => simp at h
  | some j0 =>
    by_cases hb : P j0
    · simp [hb] at h
    · simp [hb] at h
      subst h
      exact ⟨rfl, hb⟩

/- English proof (translation)
Substitute `hg` using the available equality. Assume the negation of the conclusion as `hb`. Simplify using `[hb] at h`.
-/
theorem of_bind_ite_eq_none {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    {o : Option (Fin n)} {j : Fin n} (hg : o = some j)
    (h : o.bind (fun j0 => if P j0 then none else some j0) = none) : P j := by
  subst hg
  by_contra hb
  simp [hb] at h

/- English proof (translation)
Establish `hfun : I.ideal = (⊤ : X.IdealSheafData).ideal`. Use function extensionality and compare the values at `W`. Establish `htop : (⊤ : X.IdealSheafData).ideal W = ⊤` using `rfl`. Rewrite using `[h W, htop]`. Conclude with `Scheme.IdealSheafData.ext hfun`.
-/
theorem eq_top_of_forall_ideal_eq_top {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : ∀ W : X.affineOpens, I.ideal W = ⊤) : I = ⊤ := by
  have hfun : I.ideal = (⊤ : X.IdealSheafData).ideal := by
    funext W
    have htop : (⊤ : X.IdealSheafData).ideal W = ⊤ := rfl
    rw [h W, htop]
  exact Scheme.IdealSheafData.ext hfun

/- English proof (translation)
Establish `h0 : x ∈ I.support ↔ x ∈ X.zeroLocus (↑(I.ideal ⟨U, hU⟩) : Set Γ(X, U))` using `Scheme.IdealSheafData.mem_support_iff_of_mem hx`. Rewrite using `[h0, Scheme.mem_zeroLocus_iff]`. Conclude with `Iff.rfl`.
-/
theorem mem_support_iff_forall_notMem_basicOpen {X : Scheme.{u}} (I : X.IdealSheafData)
    {x : ↥X} {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) :
    x ∈ I.support ↔ ∀ f ∈ I.ideal ⟨U, hU⟩, x ∉ X.basicOpen f := by
  have h0 : x ∈ I.support ↔
      x ∈ X.zeroLocus (↑(I.ideal ⟨U, hU⟩) : Set Γ(X, U)) :=
    Scheme.IdealSheafData.mem_support_iff_of_mem hx
  rw [h0, Scheme.mem_zeroLocus_iff]
  exact Iff.rfl

/- English proof (translation)
Establish `h2 : (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) = (x : ↥X)` using `AlgebraicGeometry.IsAffineOpen.fromSpec_primeIdealOf hU x`. Establish `h1 : AlgebraicGeometry.IsAffineOpen.fromSpec hU ⁻¹ᵁ X.basicOpen f = PrimeSpectrum.basicOpen f` using `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen hU f`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hmem : AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x ∈ AlgebraicGeometry.IsAffineOpen.fromSpec hU ⁻¹ᵁ X.basicOpen f` using `by show (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) ∈ X.basicOpen f`.

Rewrite using `[h2]`. Conclude with `hx`. Rewrite `hmem` using `[h1]`. Conclude with `(PrimeSpectrum.mem_basicOpen f _).mp hmem`. Introduce `hx`.

Establish `hmem : AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x ∈ PrimeSpectrum.basicOpen f` using `(PrimeSpectrum.mem_basicOpen f _).mpr hx`. Rewrite `hmem` using `[← h1]`. Establish `h3 : (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) ∈ X.basicOpen f` using `hmem`. Rewrite `h3` using `[h2]`. Conclude with `h3`.
-/
theorem mem_basicOpen_iff_notMem_primeIdealOf {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) (x : ↥U) :
    (x : ↥X) ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf x).asIdeal := by
  have h2 : (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base
      (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) = (x : ↥X) :=
    AlgebraicGeometry.IsAffineOpen.fromSpec_primeIdealOf hU x
  have h1 : AlgebraicGeometry.IsAffineOpen.fromSpec hU ⁻¹ᵁ X.basicOpen f
      = PrimeSpectrum.basicOpen f :=
    AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen hU f
  constructor
  · intro hx
    have hmem : AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x
        ∈ AlgebraicGeometry.IsAffineOpen.fromSpec hU ⁻¹ᵁ X.basicOpen f := by
      show (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base
        (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) ∈ X.basicOpen f
      rw [h2]
      exact hx
    rw [h1] at hmem
    exact (PrimeSpectrum.mem_basicOpen f _).mp hmem
  · intro hx
    have hmem : AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x ∈ PrimeSpectrum.basicOpen f :=
      (PrimeSpectrum.mem_basicOpen f _).mpr hx
    rw [← h1] at hmem
    have h3 : (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base
        (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) ∈ X.basicOpen f := hmem
    rw [h2] at h3
    exact h3

/- English proof (translation)
Rewrite using `[mem_support_iff_forall_notMem_basicOpen I hU hx]`. Introduce `f hf`. Rewrite `hf` using `[hI, Ideal.mem_span_singleton]`. Take `⟨a, rfl⟩` from `hf`. Establish `hle : X.basicOpen (g * a) ≤ X.basicOpen g`.

Rewrite using `[Scheme.basicOpen_mul]`. Conclude with `inf_le_left`. Conclude with `fun hc => hg (hle hc)`.
-/
theorem mem_support_of_ideal_eq_span_singleton {X : Scheme.{u}} (I : X.IdealSheafData) {x : ↥X}
    {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) (g : Γ(X, U))
    (hI : I.ideal ⟨U, hU⟩ = Ideal.span {g}) (hg : x ∉ X.basicOpen g) : x ∈ I.support := by
  rw [mem_support_iff_forall_notMem_basicOpen I hU hx]
  intro f hf
  rw [hI, Ideal.mem_span_singleton] at hf
  obtain ⟨a, rfl⟩ := hf
  have hle : X.basicOpen (g * a) ≤ X.basicOpen g := by
    rw [Scheme.basicOpen_mul]
    exact inf_le_left
  exact fun hc => hg (hle hc)

/- English proof (translation)
Establish `h` using `(mem_support_iff_forall_notMem_basicOpen I hU hx).mp hs g (by rw [hI]; exact Ideal.mem_span_singleton_self g)`. Assume the negation of the conclusion as `hc`. Conclude with `h ((mem_basicOpen_iff_notMem_primeIdealOf hU g ⟨x, hx⟩).mpr hc)`.
-/
theorem mem_primeIdealOf_of_mem_support_of_ideal_eq_span_singleton {X : Scheme.{u}} (I : X.IdealSheafData) {x : ↥X}
    {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) (g : Γ(X, U))
    (hI : I.ideal ⟨U, hU⟩ = Ideal.span {g}) (hs : x ∈ I.support) :
    g ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h := (mem_support_iff_forall_notMem_basicOpen I hU hx).mp hs g
    (by rw [hI]; exact Ideal.mem_span_singleton_self g)
  by_contra hc
  exact h ((mem_basicOpen_iff_notMem_primeIdealOf hU g ⟨x, hx⟩).mpr hc)

/- English proof (translation)
Establish `h : Z.subschemeι.base z ∈ Set.range Z.subschemeι.base` using `⟨z, rfl⟩`. Rewrite `h` using `[Scheme.IdealSheafData.range_subschemeι]`. Then use the resulting hypothesis.
-/
theorem subschemeι_base_mem_support_of_subscheme {W : Scheme.{u}} (Z : W.IdealSheafData)
    (z : ↥Z.subscheme) : Z.subschemeι.base z ∈ Z.support := by
  have h : Z.subschemeι.base z ∈ Set.range Z.subschemeι.base := ⟨z, rfl⟩
  rwa [Scheme.IdealSheafData.range_subschemeι] at h

/- English proof (translation)
Establish `hbU : X.basicOpen f ≤ U` using `X.basicOpen_le f`. Establish `hVU : V ≤ U` using `hVb.trans hbU`. Rewrite using `[restrictIdeal_eq_comap_ι]`. Use `eq_top_of_forall_ideal_eq_top _ ?_` and prove the remaining obligations. Introduce `Wa`.

Establish `e : (Wa : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ U` using `fun x _ => hVU x.2`. Establish `e' : (Wa : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ X.basicOpen f` using `fun x _ => hVb x.2`. Rewrite using `[Scheme.IdealSheafData.comap_ideal_eq_span_image I V.ι ⟨U, hU⟩ Wa e {f} hI, Set.image_singleton, Ideal.span_singleton_eq_top]`. Establish `hfac : V.ι.appLE U (Wa : (V.toScheme).Opens) e = X.presheaf.map (homOfLE hbU).op ≫ V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e'`. Rewrite using `[Scheme.Hom.map_appLE]`.

Establish `hcp : ((X.presheaf.map (homOfLE hbU).op ≫ V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e').hom) f = (V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e').hom ((X.presheaf.map (homOfLE hbU).op).hom f)` using `rfl`. Rewrite using `[hfac, hcp]`. Conclude with `IsUnit.map _ (X.toRingedSpace.isUnit_res_basicOpen f)`.
-/
theorem restrictIdeal_eq_top_of_le_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (I : X.IdealSheafData) (f : Γ(X, U))
    (hI : I.ideal ⟨U, hU⟩ = Ideal.span {f}) {V : X.Opens} (hVb : V ≤ X.basicOpen f) :
    restrictIdeal I V = ⊤ := by
  have hbU : X.basicOpen f ≤ U := X.basicOpen_le f
  have hVU : V ≤ U := hVb.trans hbU
  rw [restrictIdeal_eq_comap_ι]
  refine eq_top_of_forall_ideal_eq_top _ ?_
  intro Wa
  have e : (Wa : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ U := fun x _ => hVU x.2
  have e' : (Wa : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ X.basicOpen f := fun x _ => hVb x.2
  rw [Scheme.IdealSheafData.comap_ideal_eq_span_image I V.ι ⟨U, hU⟩ Wa e {f} hI,
    Set.image_singleton, Ideal.span_singleton_eq_top]
  have hfac : V.ι.appLE U (Wa : (V.toScheme).Opens) e
      = X.presheaf.map (homOfLE hbU).op ≫
        V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e' := by
    rw [Scheme.Hom.map_appLE]
  have hcp : ((X.presheaf.map (homOfLE hbU).op ≫
        V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e').hom) f
      = (V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e').hom
          ((X.presheaf.map (homOfLE hbU).op).hom f) := rfl
  rw [hfac, hcp]
  exact IsUnit.map _ (X.toRingedSpace.isUnit_res_basicOpen f)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ideal_top {X : Scheme.{u}} (U : X.affineOpens) :
    (⊤ : X.IdealSheafData).ideal U = ⊤ := by simp

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.comap_ideal_eq_map_appLE (I * J) g U V e, Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g U V e, Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g U V e, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]`.
-/
theorem ideal_comap_mul {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.affineOpens)
    (V : X.affineOpens) (e : (V : X.Opens) ≤ g ⁻¹ᵁ (U : Y.Opens)) (I J : Y.IdealSheafData) :
    ((I * J).comap g).ideal V = (I.comap g).ideal V * (J.comap g).ideal V := by
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (I * J) g U V e,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g U V e,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g U V e,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]

/- English proof (translation)
Introduce `x _`. Conclude with `x.2`.
-/
theorem top_le_ι_preimage_self {Y : Scheme.{u}} (V : Y.Opens) :
    (⊤ : V.toScheme.Opens) ≤ (Opens.map V.ι.base).obj V := by
  intro x _
  exact x.2

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem ι_appLE_top_eq_topIso_inv {Y : Scheme.{u}} (V : Y.Opens) :
    V.ι.appLE V ⊤ (top_le_ι_preimage_self V) = V.topIso.inv := by
  simp
  rfl

/- English proof (translation)
Rewrite using `[ι_appLE_top_eq_topIso_inv]`. Conclude with `V.topIso.commRingCatIsoToRingEquiv.symm.bijective`.
-/
theorem ι_appLE_top_bijective {Y : Scheme.{u}} (V : Y.Opens) :
    Function.Injective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V))) ∧
      Function.Surjective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V))) := by
  rw [ι_appLE_top_eq_topIso_inv]
  exact V.topIso.commRingCatIsoToRingEquiv.symm.bijective

/- English proof (translation)
Establish `: IsAffine V.toScheme` using `hV`. Establish `key` using `Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_ι_preimage_self V)`. Rewrite `key` using `[← restrictIdeal_eq_comap_ι, htop]`. Establish `h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤`. Simplify using the standard rewrite rules.

Rewrite `key` using `[h0]`. Establish `key2 : Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V))) (D.ideal ⟨V, hV⟩) = ⊤` using `key.symm`. Establish `hbij` using `ι_appLE_top_bijective V`. Establish `hcomap : Ideal.comap (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V))) (Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V))) (D.ideal ⟨V, hV⟩)) = D.ideal ⟨V, hV⟩`. Apply `Ideal.comap_map_of_bijective` to reduce the goal to its premises.

Conclude with `hbij`. Rewrite `hcomap` using `[key2, Ideal.comap_top]`. Conclude with `hcomap.symm`.
-/
theorem ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top {Y : Scheme.{u}} (D : Y.IdealSheafData)
    {V : Y.Opens} (hV : IsAffineOpen V) (htop : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have : IsAffine V.toScheme := hV
  have key := Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_ι_preimage_self V)
  rw [← restrictIdeal_eq_comap_ι, htop] at key
  have h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤ := by
    simp
  rw [h0] at key
  have key2 : Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V)))
      (D.ideal ⟨V, hV⟩) = ⊤ := key.symm
  have hbij := ι_appLE_top_bijective V
  have hcomap : Ideal.comap (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V)))
      (Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V)))
        (D.ideal ⟨V, hV⟩)) = D.ideal ⟨V, hV⟩ := by
    apply Ideal.comap_map_of_bijective
    exact hbij
  rw [key2, Ideal.comap_top] at hcomap
  exact hcomap.symm

/- English proof (translation)
Rewrite using `[etaleChartCoord_def, c.algebraMap_eq_coordRingHom, c.coordRingHom_X]`.
-/
theorem etaleChartCoord_eq_coord {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {V : X.Opens} {m : ℕ} (c : EtaleChart p V m) (j : Fin m) :
    @etaleChartCoord k _ m Γ(X, V) _ c.algebra j = c.coord j := by
  rw [etaleChartCoord_def, c.algebraMap_eq_coordRingHom, c.coordRingHom_X]

/- English proof (translation)
Introduce `F`. Proceed by induction on `F with`. Consider the case `nil`. Introduce `γ _ _ _`. Use `⟨∅, by simp, ?_⟩` and prove the remaining obligations.

Establish `h1 : (([] : List W.IdealSheafData).prod).comap g = (⊤ : Y.IdealSheafData)`. Rewrite using `[Blowup.idealSheafData_prod_nil]`. Simplify using the standard rewrite rules. Rewrite using `[h1, Finset.prod_empty, Ideal.span_singleton_one]`. Conclude with `ideal_top _`.

Consider the case `cons D F ih`. Introduce `γ hnone hsome hinj`. Establish `hlen : ∀ i, i < F.length → i + 1 < (D :: F).length`. Introduce `i hi`. Simplify using `only [List.length_cons]`.

Use linear arithmetic over natural numbers and integers. Establish `hD0 : (0 : ℕ) < (D :: F).length`. Simplify using `only [List.length_cons]`. Use linear arithmetic over natural numbers and integers. Take `⟨J', hJ'mem, hJ'⟩` from `ih (fun i => γ (i + 1)) (fun i h hg => hnone (i + 1) (hlen i h) hg) (fun i h j hg => hsome (i + 1) (hlen i h) j hg) (fun i i' hi hi' j h1 h2 => by`.

Establish `h3` using `hinj (i + 1) (i' + 1) (hlen i hi) (hlen i' hi') j h1 h2`. Use the proof step `omega)`. Establish `hprod : ((D :: F).prod.comap g).ideal ⟨V, hV⟩ = (D.comap g).ideal ⟨V, hV⟩ * ((F.prod).comap g).ideal ⟨V, hV⟩`. Rewrite using `[Blowup.idealSheafData_prod_cons]`. Conclude with `ideal_comap_mul g U ⟨V, hV⟩ e D F.prod`.

Consider the cases of `hγ0 : γ 0 with`. Consider the case `none`. Establish `hD : (D.comap g).ideal ⟨V, hV⟩ = ⊤` using `ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top _ hV (hnone 0 hD0 hγ0)`. Use `⟨J', ?_, ?_⟩` and prove the remaining obligations. Introduce `j hj`.

Take `⟨i, hi, hγi⟩` from `hJ'mem j hj`. Conclude with `⟨i + 1, hlen i hi, hγi⟩`. Rewrite using `[hprod, hD, hJ', Ideal.top_mul]`. Consider the case `some j0`. Establish `hD : (D.comap g).ideal ⟨V, hV⟩ = Ideal.span {c.coord j0}`.

Establish `h2` using `EtaleChart.ideal_eq_span_coord c hV (D.comap g) {j0} (hsome 0 hD0 j0 hγ0)`. Rewrite `h2` using `[Finset.coe_singleton, Set.image_singleton]`. Conclude with `h2`. Establish `hj0 : j0 ∉ J'`. Introduce `hj0mem`.

Take `⟨i, hi, hγi⟩` from `hJ'mem j0 hj0mem`. Establish `h3` using `hinj 0 (i + 1) hD0 (hlen i hi) j0 hγ0 hγi`. Use linear arithmetic over natural numbers and integers. Use `⟨insert j0 J', ?_, ?_⟩` and prove the remaining obligations. Introduce `j hj`.

Break down `Finset.mem_insert.mp hj with rfl | hj'` into its components or cases. Conclude with `⟨0, hD0, hγ0⟩`. Take `⟨i, hi, hγi⟩` from `hJ'mem j hj'`. Conclude with `⟨i + 1, hlen i hi, hγi⟩`. Rewrite using `[hprod, hD, hJ', Ideal.span_singleton_mul_span_singleton, Finset.prod_insert hj0]`.
-/
theorem exists_finset_comap_prod_ideal_eq_span_prod_coord {Y W : Scheme.{u}} {k : Type u}
    [Field k] {pY : Y ⟶ Spec (CommRingCat.of k)} (g : Y ⟶ W) (U : W.affineOpens) {V : Y.Opens}
    (hV : IsAffineOpen V) (e : V ≤ g ⁻¹ᵁ (U : W.Opens)) {n : ℕ} (c : EtaleChart pY V n) :
    ∀ (F : List W.IdealSheafData) (γ : ℕ → Option (Fin n)),
      (∀ i, ∀ h : i < F.length, γ i = none → restrictIdeal ((F[i]'h).comap g) V = ⊤) →
      (∀ i, ∀ h : i < F.length, ∀ j, γ i = some j →
        restrictIdeal ((F[i]'h).comap g) V = c.coordIdeal {j}) →
      (∀ i i', i < F.length → i' < F.length → ∀ j, γ i = some j → γ i' = some j → i = i') →
      ∃ J : Finset (Fin n),
        (∀ j ∈ J, ∃ i, ∃ _ : i < F.length, γ i = some j) ∧
        (F.prod.comap g).ideal ⟨V, hV⟩ = Ideal.span {∏ j ∈ J, c.coord j} := by
  intro F
  induction F with
  | nil =>
      intro γ _ _ _
      refine ⟨∅, by simp, ?_⟩
      have h1 : (([] : List W.IdealSheafData).prod).comap g = (⊤ : Y.IdealSheafData) := by
        rw [Blowup.idealSheafData_prod_nil]
        simp
      rw [h1, Finset.prod_empty, Ideal.span_singleton_one]
      exact ideal_top _
  | cons D F ih =>
      intro γ hnone hsome hinj
      have hlen : ∀ i, i < F.length → i + 1 < (D :: F).length := by
        intro i hi
        simp only [List.length_cons]
        omega
      have hD0 : (0 : ℕ) < (D :: F).length := by
        simp only [List.length_cons]
        omega
      obtain ⟨J', hJ'mem, hJ'⟩ := ih (fun i => γ (i + 1))
        (fun i h hg => hnone (i + 1) (hlen i h) hg)
        (fun i h j hg => hsome (i + 1) (hlen i h) j hg)
        (fun i i' hi hi' j h1 h2 => by
          have h3 := hinj (i + 1) (i' + 1) (hlen i hi) (hlen i' hi') j h1 h2
          omega)
      have hprod : ((D :: F).prod.comap g).ideal ⟨V, hV⟩
          = (D.comap g).ideal ⟨V, hV⟩ * ((F.prod).comap g).ideal ⟨V, hV⟩ := by
        rw [Blowup.idealSheafData_prod_cons]
        exact ideal_comap_mul g U ⟨V, hV⟩ e D F.prod
      cases hγ0 : γ 0 with
      | none =>
          have hD : (D.comap g).ideal ⟨V, hV⟩ = ⊤ :=
            ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top _ hV (hnone 0 hD0 hγ0)
          refine ⟨J', ?_, ?_⟩
          · intro j hj
            obtain ⟨i, hi, hγi⟩ := hJ'mem j hj
            exact ⟨i + 1, hlen i hi, hγi⟩
          · rw [hprod, hD, hJ', Ideal.top_mul]
      | some j0 =>
          have hD : (D.comap g).ideal ⟨V, hV⟩ = Ideal.span {c.coord j0} := by
            have h2 := EtaleChart.ideal_eq_span_coord c hV (D.comap g) {j0}
              (hsome 0 hD0 j0 hγ0)
            rw [Finset.coe_singleton, Set.image_singleton] at h2
            exact h2
          have hj0 : j0 ∉ J' := by
            intro hj0mem
            obtain ⟨i, hi, hγi⟩ := hJ'mem j0 hj0mem
            have h3 := hinj 0 (i + 1) hD0 (hlen i hi) j0 hγ0 hγi
            omega
          refine ⟨insert j0 J', ?_, ?_⟩
          · intro j hj
            rcases Finset.mem_insert.mp hj with rfl | hj'
            · exact ⟨0, hD0, hγ0⟩
            · obtain ⟨i, hi, hγi⟩ := hJ'mem j hj'
              exact ⟨i + 1, hlen i hi, hγi⟩
          · rw [hprod, hD, hJ', Ideal.span_singleton_mul_span_singleton,
              Finset.prod_insert hj0]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil`. Rewrite using `[Blowup.idealSheafData_prod_nil]`. Simplify using `[AlgebraicGeometry.Scheme.IdealSheafData.support_top]`. Consider the case `cons D E ih`.

Rewrite using `[Blowup.idealSheafData_prod_cons]`. Simplify using `[AlgebraicGeometry.Scheme.IdealSheafData.support_mul, ih]`.
-/
theorem support_prod_eq_iUnion {X : Scheme.{u}} (L : List X.IdealSheafData) :
    ((L.prod.support : TopologicalSpace.Closeds ↥X) : Set ↥X)
      = ⋃ D ∈ L, ((D.support : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
  induction L with
  | nil =>
      rw [Blowup.idealSheafData_prod_nil]
      simp [AlgebraicGeometry.Scheme.IdealSheafData.support_top]
  | cons D E ih =>
      rw [Blowup.idealSheafData_prod_cons]
      simp [AlgebraicGeometry.Scheme.IdealSheafData.support_mul, ih]

section

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}

/- English proof (translation)
Use `set notInPrime : Finset (Fin n) := Finset.univ.filter (fun j => c.coord j ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal) with hBadDef`. Establish `hBad : ∀ j : Fin n, j ∈ notInPrime ↔ c.coord j ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal`. Introduce `j`. Rewrite using `[hBadDef]`. Simplify using the standard rewrite rules.

Use `set t : Γ(X, U) := ∏ j ∈ notInPrime, c.coord j with htdef`. Establish `ht : t ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal`. Establish `hmem : ∀ j ∈ notInPrime, c.coord j ∈ Ideal.primeCompl (hU.primeIdealOf ⟨y, hyU⟩).asIdeal` using `fun j hj => (hBad j).mp hj`. Establish `hprod` using `Submonoid.prod_mem (Ideal.primeCompl (hU.primeIdealOf ⟨y, hyU⟩).asIdeal) hmem`. Rewrite `hprod` using `[← htdef]`.

Conclude with `hprod`. Establish `hUt : IsAffineOpen (X.basicOpen t)` using `hU.basicOpen t`. Establish `hle : X.basicOpen t ≤ U` using `X.basicOpen_le t`. Establish `hy' : y ∈ X.basicOpen t` using `(mem_basicOpen_iff_notMem_primeIdealOf hU t ⟨y, hyU⟩).mpr ht`. Establish `hbasic_le : ∀ j ∈ notInPrime, X.basicOpen t ≤ X.basicOpen (c.coord j)`.

Introduce `j hj`. Establish `hsplit : t = c.coord j * ∏ i ∈ notInPrime.erase j, c.coord i`. Rewrite using `[htdef]`. Conclude with `(Finset.mul_prod_erase notInPrime (fun i => c.coord i) hj).symm`. Rewrite using `[hsplit, Scheme.basicOpen_mul]`.

Conclude with `inf_le_left`. Use `⟨X.basicOpen t, hUt, hy', c.restrict hle, fun i => (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0), ?_, ?_, ?_, restrictIdeal_eq_restrict_coordIdeal_of_le hle c Z S hZ⟩` and prove the remaining obligations. Introduce `i hi`. Take `⟨hA, hB⟩` from `hdesc i hi`. Prove the components needed by the constructor for the conclusion.

Introduce `hnone`. Establish `hnone' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = none` using `hnone`. Distinguish the cases in `hg : γ i = none`. Conclude with `restrictIdeal_eq_top_of_le _ hle (hA hg)`. Take `⟨j0, hj0⟩` from `Option.ne_none_iff_exists'.mp hg`.

Establish `hb : j0 ∈ notInPrime` using `of_bind_ite_eq_none (fun j1 => j1 ∈ notInPrime) hj0 hnone'`. Establish `hideal : (F[i]'hi).ideal ⟨U, hU⟩ = Ideal.span {c.coord j0}`. Rewrite using `[c.ideal_eq_span_coord hU _ _ (hB j0 hj0), Finset.coe_singleton, Set.image_singleton]`. Conclude with `restrictIdeal_eq_top_of_le_basicOpen hU _ (c.coord j0) hideal (hbasic_le j0 hb)`. Introduce `j hj`.

Establish `hj' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j` using `hj`. Take `⟨hg, hb⟩` from `eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hj'`. Conclude with `restrictIdeal_eq_restrict_coordIdeal_of_le hle c _ _ (hB j hg)`. Introduce `i i' hi hi' j hj hj'`. Establish `hja : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j` using `hj`.

Establish `hjb : (γ i').bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j` using `hj'`. Conclude with `hinj i i' hi hi' j (eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hja).1 (eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hjb).1`. Introduce `i hi j hj`. Take `⟨_, hB⟩` from `hdesc i hi`. Establish `hj' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j` using `hj`.

Take `⟨hg, hb⟩` from `eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hj'`. Establish `hmemP : c.coord j ∈ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal`. Assume the negation of the conclusion as `hcon`. Conclude with `hb ((hBad j).mpr hcon)`. Establish `hidU : (F[i]'hi).ideal ⟨U, hU⟩ = Ideal.span {c.coord j}`.

Rewrite using `[c.ideal_eq_span_coord hU _ _ (hB j hg), Finset.coe_singleton, Set.image_singleton]`. Establish `hynb : y ∉ X.basicOpen (c.coord j)` using `fun hc => (mem_basicOpen_iff_notMem_primeIdealOf hU (c.coord j) ⟨y, hyU⟩).mp hc hmemP`. Establish `hysup : y ∈ (F[i]'hi).support` using `mem_support_of_ideal_eq_span_singleton _ hU hyU (c.coord j) hidU hynb`. Establish `hidU' : (F[i]'hi).ideal ⟨X.basicOpen t, hUt⟩ = Ideal.span {(c.restrict hle).coord j}`. Rewrite using `[(c.restrict hle).ideal_eq_span_coord hUt _ _ (restrictIdeal_eq_restrict_coordIdeal_of_le hle c _ _ (hB j hg)), Finset.coe_singleton, Set.image_singleton]`.

Conclude with `mem_primeIdealOf_of_mem_support_of_ideal_eq_span_singleton _ hUt hy' _ hidU' hysup`.
-/
theorem exists_chart_normal (F : List X.IdealSheafData) (y : ↥X) (U : X.Opens)
    (hU : IsAffineOpen U) (hyU : y ∈ U) {n : ℕ} (c : EtaleChart p U n) (γ : ℕ → Option (Fin n))
    (hdesc : ∀ i, ∀ hi : i < F.length,
      (γ i = none → restrictIdeal (F[i]'hi) U = ⊤) ∧
        ∀ j, γ i = some j → restrictIdeal (F[i]'hi) U = c.coordIdeal {j})
    (hinj : ∀ i i', i < F.length → i' < F.length → ∀ j, γ i = some j → γ i' = some j → i = i')
    (Z : X.IdealSheafData) (S : Finset (Fin n)) (hZ : restrictIdeal Z U = c.coordIdeal S) :
    ∃ (U' : X.Opens) (hU' : IsAffineOpen U') (hy' : y ∈ U')
      (c' : EtaleChart p U' n) (γ' : ℕ → Option (Fin n)),
      (∀ i, ∀ hi : i < F.length,
        (γ' i = none → restrictIdeal (F[i]'hi) U' = ⊤) ∧
          ∀ j, γ' i = some j → restrictIdeal (F[i]'hi) U' = c'.coordIdeal {j}) ∧
      (∀ i i', i < F.length → i' < F.length → ∀ j, γ' i = some j → γ' i' = some j → i = i') ∧
      (∀ i, i < F.length → ∀ j, γ' i = some j →
        c'.coord j ∈ (hU'.primeIdealOf ⟨y, hy'⟩).asIdeal) ∧
      restrictIdeal Z U' = c'.coordIdeal S := by
  classical
  set notInPrime : Finset (Fin n) :=
    Finset.univ.filter (fun j => c.coord j ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal) with hBadDef
  have hBad : ∀ j : Fin n, j ∈ notInPrime ↔ c.coord j ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    intro j
    rw [hBadDef]
    simp
  set t : Γ(X, U) := ∏ j ∈ notInPrime, c.coord j with htdef
  have ht : t ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    have hmem : ∀ j ∈ notInPrime, c.coord j ∈ Ideal.primeCompl (hU.primeIdealOf ⟨y, hyU⟩).asIdeal :=
      fun j hj => (hBad j).mp hj
    have hprod := Submonoid.prod_mem (Ideal.primeCompl (hU.primeIdealOf ⟨y, hyU⟩).asIdeal) hmem
    rw [← htdef] at hprod
    exact hprod
  have hUt : IsAffineOpen (X.basicOpen t) := hU.basicOpen t
  have hle : X.basicOpen t ≤ U := X.basicOpen_le t
  have hy' : y ∈ X.basicOpen t := (mem_basicOpen_iff_notMem_primeIdealOf hU t ⟨y, hyU⟩).mpr ht
  have hbasic_le : ∀ j ∈ notInPrime, X.basicOpen t ≤ X.basicOpen (c.coord j) := by
    intro j hj
    have hsplit : t = c.coord j * ∏ i ∈ notInPrime.erase j, c.coord i := by
      rw [htdef]
      exact (Finset.mul_prod_erase notInPrime (fun i => c.coord i) hj).symm
    rw [hsplit, Scheme.basicOpen_mul]
    exact inf_le_left
  refine ⟨X.basicOpen t, hUt, hy', c.restrict hle,
    fun i => (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0), ?_, ?_, ?_,
    restrictIdeal_eq_restrict_coordIdeal_of_le hle c Z S hZ⟩
  · intro i hi
    obtain ⟨hA, hB⟩ := hdesc i hi
    constructor
    · intro hnone
      have hnone' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = none := hnone
      by_cases hg : γ i = none
      · exact restrictIdeal_eq_top_of_le _ hle (hA hg)
      · obtain ⟨j0, hj0⟩ := Option.ne_none_iff_exists'.mp hg
        have hb : j0 ∈ notInPrime := of_bind_ite_eq_none (fun j1 => j1 ∈ notInPrime) hj0 hnone'
        have hideal : (F[i]'hi).ideal ⟨U, hU⟩ = Ideal.span {c.coord j0} := by
          rw [c.ideal_eq_span_coord hU _ _ (hB j0 hj0), Finset.coe_singleton,
            Set.image_singleton]
        exact restrictIdeal_eq_top_of_le_basicOpen hU _ (c.coord j0) hideal (hbasic_le j0 hb)
    · intro j hj
      have hj' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj
      obtain ⟨hg, hb⟩ := eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hj'
      exact restrictIdeal_eq_restrict_coordIdeal_of_le hle c _ _ (hB j hg)
  · intro i i' hi hi' j hj hj'
    have hja : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj
    have hjb : (γ i').bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj'
    exact hinj i i' hi hi' j (eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hja).1
      (eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hjb).1
  · intro i hi j hj
    obtain ⟨_, hB⟩ := hdesc i hi
    have hj' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj
    obtain ⟨hg, hb⟩ := eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hj'
    have hmemP : c.coord j ∈ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
      by_contra hcon
      exact hb ((hBad j).mpr hcon)
    have hidU : (F[i]'hi).ideal ⟨U, hU⟩ = Ideal.span {c.coord j} := by
      rw [c.ideal_eq_span_coord hU _ _ (hB j hg), Finset.coe_singleton, Set.image_singleton]
    have hynb : y ∉ X.basicOpen (c.coord j) := fun hc =>
      (mem_basicOpen_iff_notMem_primeIdealOf hU (c.coord j) ⟨y, hyU⟩).mp hc hmemP
    have hysup : y ∈ (F[i]'hi).support :=
      mem_support_of_ideal_eq_span_singleton _ hU hyU (c.coord j) hidU hynb
    have hidU' : (F[i]'hi).ideal ⟨X.basicOpen t, hUt⟩
        = Ideal.span {(c.restrict hle).coord j} := by
      rw [(c.restrict hle).ideal_eq_span_coord hUt _ _
        (restrictIdeal_eq_restrict_coordIdeal_of_le hle c _ _ (hB j hg)), Finset.coe_singleton,
        Set.image_singleton]
    exact mem_primeIdealOf_of_mem_support_of_ideal_eq_span_singleton _ hUt hy' _ hidU' hysup

end

def GCentre : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of k)) [Smooth q] (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) (F : Closeds X),
    HasSimpleNormalCrossings q L → HasSimpleNormalCrossingsWith q Z L → (⋃ D ∈ L, (D.support : Set X)) = F →
    GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup.IsSncCentre F Z

/- English proof (translation)
Introduce `k _ X q _ Z L F _ hZ hF x hx`. Take `⟨U, hxU, m, c0, hc0, he0, a, S, h1, h2, h3, h4⟩` from `hZ x hx`. Set `c : EtaleChart q U m` to `⟨c0, hc0, he0⟩`. Choose the witnesses or unpack the hypotheses as in `⟨V, hVaff, hxV, hVU⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U := by`. Take `⟨V, hVmem, hxV, hVU⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X) hxU`.

Conclude with `⟨V, hVmem, hxV, hVU⟩`. Establish `h2' : ∀ i, ∀ hi : i < L.length, a i = none → restrictIdeal (L[i]'hi) U = ⊤`. Introduce `i hi hg`. Rewrite using `[restrictIdeal_eq_comap_ι]`. Conclude with `h2 i hi hg`.

Establish `h3' : ∀ i, ∀ hi : i < L.length, ∀ t, a i = some t → restrictIdeal (L[i]'hi) U = c.coordIdeal {t}`. Introduce `i hi t hg`. Rewrite using `[restrictIdeal_eq_comap_ι]`. Conclude with `h3 i hi t hg`. Establish `h4' : restrictIdeal Z U = c.coordIdeal S`.

Rewrite using `[restrictIdeal_eq_comap_ι]`. Conclude with `h4`. Establish `hdesc : ∀ i, ∀ hi : i < L.length, (a i = none → restrictIdeal (L[i]'hi) V = ⊤) ∧ ∀ j, a i = some j → restrictIdeal (L[i]'hi) V = (c.restrict hVU).coordIdeal {j}` using `fun i hi => ⟨fun hg => restrictIdeal_eq_top_of_le _ hVU (h2' i hi hg), fun j hg => restrictIdeal_eq_restrict_coordIdeal_of_le hVU c _ {j} (h3' i hi j hg)⟩`. Establish `hinj : ∀ i i', i < L.length → i' < L.length → ∀ j, a i = some j → a i' = some j → i = i'` using `fun i i' hi hi' j h h' => h1 i hi i' hi' j h h'`. Take `⟨V', hV', hxV', c', γ, hγ, hinjγ, hmem, hZV'⟩` from `exists_chart_normal L x V hVaff hxV (c.restrict hVU) a hdesc hinj Z S (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c Z S h4')`.

Establish `hZid : Z.ideal ⟨V', hV'⟩ = Ideal.span (c'.coord '' (S : Set (Fin m)))` using `c'.ideal_eq_span_coord hV' Z S hZV'`. Establish `hSmem : ∀ j ∈ S, c'.coord j ∈ (hV'.primeIdealOf ⟨x, hxV'⟩).asIdeal`. Introduce `j hj`. Establish `hin : c'.coord j ∈ Z.ideal ⟨V', hV'⟩`. Rewrite using `[hZid]`.

Conclude with `Ideal.subset_span ⟨j, hj, rfl⟩`. Establish `h0` using `(mem_support_iff_forall_notMem_basicOpen Z hV' hxV').mp hx _ hin`. Assume the negation of the conclusion as `hc`. Conclude with `h0 ((mem_basicOpen_iff_notMem_primeIdealOf hV' _ ⟨x, hxV'⟩).mpr hc)`. Take `⟨J₀, hJ₀mem, hJ₀⟩` from `exists_finset_comap_prod_ideal_eq_span_prod_coord (𝟙 X) ⟨V', hV'⟩ hV' (fun y hy => hy) c' L γ (fun i h hg => by rw [Scheme.IdealSheafData.comap_id]; exact (hγ i h).1 hg) (fun i h j hg => by rw [Scheme.IdealSheafData.comap_id]; exact (hγ i h).2 j hg) hinjγ`.

Rewrite `hJ₀` using `[Scheme.IdealSheafData.comap_id]`. Establish `hJS : ∀ j ∈ J₀ ∪ S, c'.coord j ∈ (hV'.primeIdealOf ⟨x, hxV'⟩).asIdeal`. Introduce `j hj`. Break down `Finset.mem_union.mp hj with hj | hj` into its components or cases. Take `⟨i, hi, hγi⟩` from `hJ₀mem j hj`.

Conclude with `hmem i hi j hγi`. Conclude with `hSmem j hj`. Take `⟨N, f, hfcoord, hfreg⟩` from `exists_isRegularParameterSystem_with_coords_of_mem_prime hV' c' x hxV' (J₀ ∪ S) hJS`. Use `choose ι hι using hfcoord`. Establish `hntr : Nontrivial Γ(X, V')`.

Break down `subsingleton_or_nontrivial Γ(X, V') with hs | hs` into its components or cases. It suffices to derive a contradiction. Use `(hV'.primeIdealOf ⟨x, hxV'⟩).isPrime.ne_top ?_` and prove the remaining obligations. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h10 : (1 : Γ(X, V')) = 0` using `@Subsingleton.elim _ hs 1 0`.

Rewrite using `[h10]`. Conclude with `Submodule.zero_mem _`. Conclude with `hs`. Establish `hcinj : Function.Injective c'.coord`. Establish `h` using `@etaleChartCoord_injective k _ m Γ(X, V') _ c'.algebra (c'.algebra_etale hV') hntr`.

Introduce `a b hab`. Use `h ?_` and prove the remaining obligations. Simplify using `only [etaleChartCoord_eq_coord]`. Conclude with `hab`. Establish `hrad` using `@isRadical_span_singleton_prod_etaleChartCoord k _ m Γ(X, V') _ c'.algebra (c'.algebra_etale hV') J₀`.

Simplify using `only [etaleChartCoord_eq_coord] at hrad`. Set `ιJ : { x // x ∈ J₀ } → Fin N` to `fun j => ι j.1 (Finset.mem_union_left S j.2)`. Set `ιS : { x // x ∈ S } → Fin N` to `fun j => ι j.1 (Finset.mem_union_right J₀ j.2)`. Establish `hinj2 : ∀ a ∈ J₀.attach, ∀ b ∈ J₀.attach, ιJ a = ιJ b → a = b`. Introduce `a _ b _ hab`.

Establish `h1 : c'.coord a.1 = c'.coord b.1`. Rewrite using `[← hι a.1 (Finset.mem_union_left S a.2), ← hι b.1 (Finset.mem_union_left S b.2)]`. Conclude with `congrArg f hab`. Conclude with `Subtype.ext (hcinj h1)`. Establish `hprodJ : (∏ i ∈ J₀.attach.image ιJ, f i) = ∏ j ∈ J₀, c'.coord j`.

Rewrite using `[Finset.prod_image hinj2, ← Finset.prod_attach J₀ (fun j => c'.coord j)]`. Conclude with `Finset.prod_congr rfl fun j _ => hι j.1 _`. Establish `himS : f '' ((S.attach.image ιS : Finset (Fin N)) : Set (Fin N)) = c'.coord '' (S : Set (Fin m))`. Use extensionality with `y`. Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach, true_and]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨j, rfl⟩, rfl⟩`. Conclude with `⟨j.1, j.2, (hι j.1 _).symm⟩`. Introduce and unpack `⟨j, hj, rfl⟩`. Conclude with `⟨_, ⟨⟨j, hj⟩, rfl⟩, hι j _⟩`.

Establish `hFeq : F = L.prod.support`. Use extensionality with `y`. Rewrite using `[← hF, support_prod_eq_iUnion]`. Use `⟨⟨V', hV'⟩, hxV', N, f, J₀.attach.image ιJ, S.attach.image ιS, hfreg, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hFeq, Scheme.IdealSheafData.vanishingIdeal_support, Scheme.IdealSheafData.radical_ideal, hJ₀, hrad.radical, hprodJ]`.

Rewrite using `[hZid, himS]`.
-/
theorem gCentre : GCentre := by
  intro k _ X q _ Z L F _ hZ hF x hx
  classical
  obtain ⟨U, hxU, m, c0, hc0, he0, a, S, h1, h2, h3, h4⟩ := hZ x hx
  let c : EtaleChart q U m := ⟨c0, hc0, he0⟩
  obtain ⟨V, hVaff, hxV, hVU⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U := by
    obtain ⟨V, hVmem, hxV, hVU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X) hxU
    exact ⟨V, hVmem, hxV, hVU⟩
  have h2' : ∀ i, ∀ hi : i < L.length, a i = none → restrictIdeal (L[i]'hi) U = ⊤ := by
    intro i hi hg
    rw [restrictIdeal_eq_comap_ι]
    exact h2 i hi hg
  have h3' : ∀ i, ∀ hi : i < L.length, ∀ t, a i = some t → restrictIdeal (L[i]'hi) U = c.coordIdeal {t} := by
    intro i hi t hg
    rw [restrictIdeal_eq_comap_ι]
    exact h3 i hi t hg
  have h4' : restrictIdeal Z U = c.coordIdeal S := by
    rw [restrictIdeal_eq_comap_ι]
    exact h4
  have hdesc : ∀ i, ∀ hi : i < L.length, (a i = none → restrictIdeal (L[i]'hi) V = ⊤) ∧
      ∀ j, a i = some j → restrictIdeal (L[i]'hi) V = (c.restrict hVU).coordIdeal {j} :=
    fun i hi => ⟨fun hg => restrictIdeal_eq_top_of_le _ hVU (h2' i hi hg),
      fun j hg => restrictIdeal_eq_restrict_coordIdeal_of_le hVU c _ {j} (h3' i hi j hg)⟩
  have hinj : ∀ i i', i < L.length → i' < L.length → ∀ j, a i = some j → a i' = some j → i = i' :=
    fun i i' hi hi' j h h' => h1 i hi i' hi' j h h'
  obtain ⟨V', hV', hxV', c', γ, hγ, hinjγ, hmem, hZV'⟩ :=
    exists_chart_normal L x V hVaff hxV (c.restrict hVU) a hdesc hinj Z S
      (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c Z S h4')
  have hZid : Z.ideal ⟨V', hV'⟩ = Ideal.span (c'.coord '' (S : Set (Fin m))) :=
    c'.ideal_eq_span_coord hV' Z S hZV'
  have hSmem : ∀ j ∈ S, c'.coord j ∈ (hV'.primeIdealOf ⟨x, hxV'⟩).asIdeal := by
    intro j hj
    have hin : c'.coord j ∈ Z.ideal ⟨V', hV'⟩ := by
      rw [hZid]; exact Ideal.subset_span ⟨j, hj, rfl⟩
    have h0 := (mem_support_iff_forall_notMem_basicOpen Z hV' hxV').mp hx _ hin
    by_contra hc
    exact h0 ((mem_basicOpen_iff_notMem_primeIdealOf hV' _ ⟨x, hxV'⟩).mpr hc)
  obtain ⟨J₀, hJ₀mem, hJ₀⟩ :=
    exists_finset_comap_prod_ideal_eq_span_prod_coord (𝟙 X) ⟨V', hV'⟩ hV' (fun y hy => hy) c' L γ
      (fun i h hg => by rw [Scheme.IdealSheafData.comap_id]; exact (hγ i h).1 hg)
      (fun i h j hg => by rw [Scheme.IdealSheafData.comap_id]; exact (hγ i h).2 j hg) hinjγ
  rw [Scheme.IdealSheafData.comap_id] at hJ₀
  have hJS : ∀ j ∈ J₀ ∪ S, c'.coord j ∈ (hV'.primeIdealOf ⟨x, hxV'⟩).asIdeal := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨i, hi, hγi⟩ := hJ₀mem j hj
      exact hmem i hi j hγi
    · exact hSmem j hj
  obtain ⟨N, f, hfcoord, hfreg⟩ :=
    exists_isRegularParameterSystem_with_coords_of_mem_prime hV' c' x hxV' (J₀ ∪ S) hJS
  choose ι hι using hfcoord
  have hntr : Nontrivial Γ(X, V') := by
    rcases subsingleton_or_nontrivial Γ(X, V') with hs | hs
    · exfalso
      refine (hV'.primeIdealOf ⟨x, hxV'⟩).isPrime.ne_top ?_
      rw [Ideal.eq_top_iff_one]
      have h10 : (1 : Γ(X, V')) = 0 := @Subsingleton.elim _ hs 1 0
      rw [h10]
      exact Submodule.zero_mem _
    · exact hs
  have hcinj : Function.Injective c'.coord := by
    have h := @etaleChartCoord_injective k _ m Γ(X, V') _ c'.algebra (c'.algebra_etale hV') hntr
    intro a b hab
    refine h ?_
    simp only [etaleChartCoord_eq_coord]
    exact hab
  have hrad := @isRadical_span_singleton_prod_etaleChartCoord k _ m Γ(X, V') _ c'.algebra
    (c'.algebra_etale hV') J₀
  simp only [etaleChartCoord_eq_coord] at hrad
  let ιJ : { x // x ∈ J₀ } → Fin N := fun j => ι j.1 (Finset.mem_union_left S j.2)
  let ιS : { x // x ∈ S } → Fin N := fun j => ι j.1 (Finset.mem_union_right J₀ j.2)
  have hinj2 : ∀ a ∈ J₀.attach, ∀ b ∈ J₀.attach, ιJ a = ιJ b → a = b := by
    intro a _ b _ hab
    have h1 : c'.coord a.1 = c'.coord b.1 := by
      rw [← hι a.1 (Finset.mem_union_left S a.2), ← hι b.1 (Finset.mem_union_left S b.2)]
      exact congrArg f hab
    exact Subtype.ext (hcinj h1)
  have hprodJ : (∏ i ∈ J₀.attach.image ιJ, f i) = ∏ j ∈ J₀, c'.coord j := by
    rw [Finset.prod_image hinj2, ← Finset.prod_attach J₀ (fun j => c'.coord j)]
    exact Finset.prod_congr rfl fun j _ => hι j.1 _
  have himS : f '' ((S.attach.image ιS : Finset (Fin N)) : Set (Fin N)) = c'.coord '' (S : Set (Fin m)) := by
    ext y
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j.1, j.2, (hι j.1 _).symm⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨_, ⟨⟨j, hj⟩, rfl⟩, hι j _⟩
  have hFeq : F = L.prod.support := by
    ext y
    rw [← hF, support_prod_eq_iUnion]
  refine ⟨⟨V', hV'⟩, hxV', N, f, J₀.attach.image ιJ, S.attach.image ιS, hfreg, ?_, ?_⟩
  · rw [hFeq, Scheme.IdealSheafData.vanishingIdeal_support, Scheme.IdealSheafData.radical_ideal, hJ₀,
      hrad.radical, hprodJ]
  · rw [hZid, himS]

end PositivityTheory.ResPlug.BlowupCentre
