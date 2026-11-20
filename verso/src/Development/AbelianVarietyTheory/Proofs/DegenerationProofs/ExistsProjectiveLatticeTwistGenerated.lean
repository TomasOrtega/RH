import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveClosureIsProjOver
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMulPowMemOOfIsAffineOpen

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
open Classical in
attribute [local instance] MvPolynomial.gradedAlgebra in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : _root_.GlobalTheory.ZH.RatModel o Ω} in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR`. Rewrite using `[dif_pos h, map_one, map_one]`.
-/
private lemma valR_one_degeneration {L : Type} [Field L] {X : Scheme} (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp L ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR x U 1 = 1 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR
  rw [dif_pos h, map_one, map_one]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
open Classical in
attribute [local instance] MvPolynomial.gradedAlgebra in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : _root_.GlobalTheory.ZH.RatModel o Ω} in

/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver at h`. Take `⟨N, π, hπ, hcomm⟩` from `h`. Use `haveI := hπ`. Establish `hx : (M.pt ≫ π) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str o N = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o Ω)`. Rewrite using `[Category.assoc, hcomm, M.pt_s]`.

Establish `hsub : ∀ p q : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω, p = q`. Introduce `p q`. Conclude with `Subsingleton.elim p q`. Take `⟨p⟩ : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω)` from `inferInstance`. Take `⟨k, hk⟩` from `_root_.GlobalTheory.ProjSpace.exists_mem_chart o N ((M.pt ≫ π) p)`.

Establish `htop : ⊤ ≤ (M.pt ≫ π) ⁻¹ᵁ _root_.GlobalTheory.ProjSpace.chart o N k`. Introduce `q _`. Rewrite using `[hsub q p]`. Conclude with `hk`. Use `set t : Fin (N + 1) → Ω := fun j => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (M.pt ≫ π) (_root_.GlobalTheory.ProjSpace.chart o N k) (_root_.GlobalTheory.ProjSpace.ratio o N k j) with ht_def`.

Establish `htk : t k = 1`. Simplify using `only [ht_def]`. Establish `: _root_.GlobalTheory.ProjSpace.ratio o N k k = 1`. Unfold `_root_.GlobalTheory.ProjSpace.ratio`. Conclude with `_root_.GlobalTheory.ProjSpace.ratioOn_self`.

Rewrite using `[this]`. Conclude with `valR_one_degeneration _ _ htop`. Establish `ht : t ≠ 0`. Introduce `h0`. Use `congrFun h0 k` as an intermediate fact.

Rewrite `this` using `[htk]`. Conclude with `one_ne_zero this`. Establish `heq : M.pt ≫ π = _root_.GlobalTheory.TuplePoint.point o t ht` using `_root_.GlobalTheory.TuplePoint.eq_point hx (i := k) (by rw [htk]; exact one_ne_zero) htop (fun j => by rw [htk, div_one])`. Conclude with `⟨N, t, M.isCl_of_isClosedImmersion π heq⟩`.
-/
theorem _root_.GlobalTheory.ZH.RatModel.exists_isCl_of_isProjOver (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.s) :
    ∃ (n : ℕ) (t : Fin (n + 1) → Ω), M.IsCl t := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver at h
  obtain ⟨N, π, hπ, hcomm⟩ := h
  haveI := hπ
  have hx : (M.pt ≫ π) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str o N = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o Ω) := by
    rw [Category.assoc, hcomm, M.pt_s]
  have hsub : ∀ p q : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω, p = q := by
    intro p q
    exact Subsingleton.elim p q
  obtain ⟨p⟩ : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω) := inferInstance
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.ProjSpace.exists_mem_chart o N ((M.pt ≫ π) p)
  have htop : ⊤ ≤ (M.pt ≫ π) ⁻¹ᵁ _root_.GlobalTheory.ProjSpace.chart o N k := by
    intro q _
    rw [hsub q p]
    exact hk
  set t : Fin (N + 1) → Ω := fun j =>
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (M.pt ≫ π) (_root_.GlobalTheory.ProjSpace.chart o N k) (_root_.GlobalTheory.ProjSpace.ratio o N k j) with ht_def
  have htk : t k = 1 := by
    simp only [ht_def]
    have : _root_.GlobalTheory.ProjSpace.ratio o N k k = 1 := by
      unfold _root_.GlobalTheory.ProjSpace.ratio
      exact _root_.GlobalTheory.ProjSpace.ratioOn_self
    rw [this]
    exact valR_one_degeneration _ _ htop
  have ht : t ≠ 0 := by
    intro h0
    have := congrFun h0 k
    rw [htk] at this
    exact one_ne_zero this
  have heq : M.pt ≫ π = _root_.GlobalTheory.TuplePoint.point o t ht :=
    _root_.GlobalTheory.TuplePoint.eq_point hx (i := k) (by rw [htk]; exact one_ne_zero)
      htop (fun j => by rw [htk, div_one])
  exact ⟨N, t, M.isCl_of_isClosedImmersion π heq⟩

variable {J : Type} [Fintype J] [DecidableEq J]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
open Classical in
attribute [local instance] MvPolynomial.gradedAlgebra in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : _root_.GlobalTheory.ZH.RatModel o Ω} in
/- English proof (translation)
Establish `hu : IsUnit b.det` using `isUnit_iff_ne_zero.mpr hb`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨r, rfl⟩` from `hx`. Introduce `k`. Establish `hrow : Matrix.vecMul (b r) b⁻¹ = Pi.single r 1`. Use function extensionality and compare the values at `j`. Establish `h1` using `congrFun (congrFun (Matrix.mul_nonsing_inv b hu) r) j`.

Rewrite `h1` using `[Matrix.mul_apply]`. Simplify using `only [Matrix.vecMul, dotProduct]`. Rewrite using `[h1, Matrix.one_apply]`. Distinguish the cases in `hrj : r = j`. Substitute `hrj` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hrj, Pi.single_apply, Ne.symm hrj]`. Rewrite using `[hrow]`. Distinguish the cases in `hkr : k = r`. Substitute `hkr` using the available equality.

Simplify using `[R.one_mem]`. Simplify using `[Pi.single_apply, hkr, R.zero_mem]`. Consider the case `zero => intro k`. Simplify using `[R.zero_mem]`. Consider the case `add x y _ _ hx hy`.

Introduce `k`. Rewrite using `[Matrix.add_vecMul]`. Conclude with `R.add_mem (hx k) (hy k)`. Consider the case `smul c x _ hx`. Introduce `k`.

Establish `hsm : Matrix.vecMul (c • x) b⁻¹ = (c : Ω) • Matrix.vecMul x b⁻¹`. Rewrite using `[← Matrix.smul_vecMul]`. Both sides reduce to the same expression. Rewrite using `[hsm, Pi.smul_apply, smul_eq_mul]`. Conclude with `R.mul_mem c.2 (hx k)`.

Introduce `hc`. Establish `hw : w = Matrix.vecMul (Matrix.vecMul w b⁻¹) b`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul b hu, Matrix.vecMul_one]`. Rewrite using `[hw, Matrix.vecMul_eq_sum]`. Use `Submodule.sum_mem _ (fun k _ => ?_)` and prove the remaining obligations.

Establish `hsm : Matrix.vecMul w b⁻¹ k • b k = (⟨_, hc k⟩ : R) • b k` using `rfl`. Rewrite using `[hsm]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.
-/
private theorem mem_span_range_iff_vecMul_inv_mem {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    {J : Type} [Fintype J] [DecidableEq J]
    (R : Subalgebra o Ω) (b : Matrix J J Ω) (hb : b.det ≠ 0) (w : J → Ω) :
    w ∈ Submodule.span R (Set.range b) ↔ ∀ k, Matrix.vecMul w b⁻¹ k ∈ R := by
  have hu : IsUnit b.det := isUnit_iff_ne_zero.mpr hb
  constructor
  · intro hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, rfl⟩ := hx
      intro k
      have hrow : Matrix.vecMul (b r) b⁻¹ = Pi.single r 1 := by
        funext j
        have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv b hu) r) j
        rw [Matrix.mul_apply] at h1
        simp only [Matrix.vecMul, dotProduct]
        rw [h1, Matrix.one_apply]
        by_cases hrj : r = j
        · subst hrj; simp
        · simp [hrj, Pi.single_apply, Ne.symm hrj]
      rw [hrow]
      by_cases hkr : k = r
      · subst hkr; simp [R.one_mem]
      · simp [Pi.single_apply, hkr, R.zero_mem]
    | zero => intro k; simp [R.zero_mem]
    | add x y _ _ hx hy =>
      intro k
      rw [Matrix.add_vecMul]
      exact R.add_mem (hx k) (hy k)
    | smul c x _ hx =>
      intro k
      have hsm : Matrix.vecMul (c • x) b⁻¹ = (c : Ω) • Matrix.vecMul x b⁻¹ := by
        rw [← Matrix.smul_vecMul]; rfl
      rw [hsm, Pi.smul_apply, smul_eq_mul]
      exact R.mul_mem c.2 (hx k)
  · intro hc
    have hw : w = Matrix.vecMul (Matrix.vecMul w b⁻¹) b := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul b hu, Matrix.vecMul_one]
    rw [hw, Matrix.vecMul_eq_sum]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    have hsm : Matrix.vecMul w b⁻¹ k • b k = (⟨_, hc k⟩ : R) • b k := rfl
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
open Classical in
attribute [local instance] MvPolynomial.gradedAlgebra in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : _root_.GlobalTheory.ZH.RatModel o Ω} in
variable {J : Type} [Fintype J] [DecidableEq J] in

/- English proof (translation)
Introduce `o Ω _ _ _ _ M hproj J _ EE`. Take `⟨n, t, hcl⟩` from `_root_.GlobalTheory.ZH.RatModel.exists_isCl_of_isProjOver hproj`. Establish `hcl'` using `hcl`. Unfold `_root_.GlobalTheory.ZH.RatModel.IsCl at hcl'`. Take `⟨hdiv, hchart⟩` from `hcl'`.

Unfold `_root_.GlobalTheory.ZH.RatModel.HasDiv at hdiv`. Establish `hdivne : ∀ {i z}, M.Div t i z → t i ≠ 0`. Introduce `i z h`. Unfold `_root_.GlobalTheory.ZH.RatModel.Div at h`. Conclude with `h.1`.

Establish `hdivratio : ∀ {i z} (j : Fin (n + 1)), M.Div t i z → t j / t i ∈ M.O z`. Introduce `i z j h`. Unfold `_root_.GlobalTheory.ZH.RatModel.Div at h`. Conclude with `h.2 j`. Establish `hD : ∀ i, ∃ U : M.Z.Opens, (∀ z, z ∈ U ↔ M.Div t i z) ∧ (t i ≠ 0 → IsAffineOpen U)`.

Introduce `i`. Distinguish the cases in `hi : t i ≠ 0`. Take `⟨U, hU, hUeq, _⟩` from `hchart i hi`. Use `⟨U, fun z => ?_, fun _ => hU⟩` and prove the remaining obligations. Rewrite using `[← SetLike.mem_coe, hUeq]`.

Both sides reduce to the same expression. Use `⟨⊥, fun z => ⟨fun h => absurd h (by simp), fun h => absurd (hdivne h) hi⟩, fun h => absurd h hi⟩` and prove the remaining obligations. Use `choose D hDmem hDaff using hD`. Establish `hloc : ∀ z : M.Z, ∃ (U : M.Z.Opens) (b : Matrix J J Ω) (i : Fin (n + 1)) (f : Γ(M.Z, D i)), z ∈ M.Z.basicOpen f ∧ M.Z.basicOpen f ≤ U ∧ b.det ≠ 0 ∧ t i ≠ 0 ∧ ∀ z' ∈ U, EE.E z' = Submodule.span (M.O z') (Set.range b)`. Introduce `z`.

Take `⟨U, b, hzU, hb, hspan⟩` from `EE.loc z`. Take `⟨i, hi⟩` from `hdiv z`. Establish `hzD : z ∈ D i` using `(hDmem i z).2 hi`. Take `⟨f, hfle, hzf⟩` from `(hDaff i (hdivne hi)).exists_basicOpen_le (V := D i ⊓ U) ⟨z, hzD, hzU⟩ hzD`. Conclude with `⟨U, b, i, f, hzf, hfle.trans inf_le_right, hb, hdivne hi, hspan⟩`.

Use `choose Uz bz iz fz hzmem hzle hzdet hzti hzspan using hloc`. Use `set u : M.Z → Ω := fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valF M.pt (D (iz z)) (fz z) with hu_def`. Establish `hu_mem : ∀ z z', z' ∈ D (iz z) → u z ∈ M.O z'` using `fun z z' hz' => _root_.GlobalTheory.ZH.RatModel.valF_mem_O hz' (fz z)`. Establish `hzD : ∀ z, z ∈ D (iz z)` using `fun z => (M.Z.basicOpen_le (fz z)) (hzmem z)`. Establish `hu_unit : ∀ z z' (hz' : z' ∈ D (iz z)), z' ∈ M.Z.basicOpen (fz z) ↔ (u z ≠ 0 ∧ (u z)⁻¹ ∈ M.O z')`.

Introduce `z z' hz'`. Rewrite using `[← _root_.GlobalTheory.ZH.RatModel.isUnit_valF_iff hz' (fz z), _root_.GlobalTheory.ZH.RatModel.isUnit_O_iff]`. Establish `hu_ne : ∀ z, u z ≠ 0` using `fun z => ((hu_unit z z (hzD z)).1 (hzmem z)).1`. Establish `hu_inv : ∀ z z', z' ∈ M.Z.basicOpen (fz z) → (u z)⁻¹ ∈ M.O z'` using `fun z z' h => ((hu_unit z z' ((M.Z.basicOpen_le (fz z)) h)).1 h).2`. Use `haveI := M.noetherianSpace_of_isNoetherianRing`.

Take `⟨F, hF⟩` from `isCompact_univ.elim_finite_subcover (fun z => (M.Z.basicOpen (fz z) : Set M.Z)) (fun z => (M.Z.basicOpen (fz z)).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hzmem x⟩)`. Establish `hcover : ∀ z : M.Z, ∃ z₀ ∈ F, z ∈ M.Z.basicOpen (fz z₀)`. Introduce `z`. Use `hF (Set.mem_univ z)` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`.

Take `⟨z₀, hz₀, h⟩` from `this`. Conclude with `⟨z₀, hz₀, h⟩`. Establish `hcoord : ∀ z₁ z', z' ∈ Uz z₁ → ∀ w : J → Ω, w ∈ EE.E z' ↔ ∀ k, Matrix.vecMul w (bz z₁)⁻¹ k ∈ M.O z'`. Introduce `z₁ z' hz' w`. Rewrite using `[hzspan z₁ z' hz']`.

Conclude with `mem_span_range_iff_vecMul_inv_mem _ _ (hzdet z₁) w`. Establish `hrow : ∀ z₀ r z', z' ∈ Uz z₀ → bz z₀ r ∈ EE.E z'`. Introduce `z₀ r z' hz'`. Rewrite using `[hzspan z₀ z' hz']`. Conclude with `Submodule.subset_span ⟨r, rfl⟩`.

Establish `h1 : ∀ z₀ r z₁ k, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ z' ∈ D (iz z₀) ⊓ Uz z₁, Matrix.vecMul (bz z₀ r) (bz z₁)⁻¹ k * u z₀ ^ C ∈ M.O z'`. Introduce `z₀ r z₁ k`. Use `_root_.GlobalTheory.ZH.RatModel.exists_forall_mul_pow_mem_O (D (iz z₀) ⊓ Uz z₁) (hu_ne z₀) (fun z' hz' => hu_mem z₀ z' hz'.1) (fun z' hz' hinv => ?_)` and prove the remaining obligations. Establish `hb : z' ∈ M.Z.basicOpen (fz z₀)` using `((hu_unit z₀ z' hz'.1).2 ⟨hu_ne z₀, hinv⟩)`. Conclude with `(hcoord z₁ z' hz'.2 _).1 (hrow z₀ r z' (hzle z₀ hb)) k`.

Use `choose C1 hC1 using h1`. Use `set C : ℕ := (F ×ˢ F ×ˢ (Finset.univ : Finset J) ×ˢ (Finset.univ : Finset J)).sup (fun p => C1 p.1 p.2.2.1 p.2.1 p.2.2.2) with hC_def`. Establish `hC : ∀ z₀ ∈ F, ∀ z₁ ∈ F, ∀ r k, C1 z₀ r z₁ k ≤ C`. Introduce `z₀ hz₀ z₁ hz₁ r k`. Rewrite using `[hC_def]`.

Conclude with `Finset.le_sup (f := fun p : M.Z × M.Z × J × J => C1 p.1 p.2.2.1 p.2.1 p.2.2.2) (b := (z₀, z₁, r, k)) (Finset.mem_product.2 ⟨hz₀, Finset.mem_product.2 ⟨hz₁, Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩⟩)`. Establish `h2 : ∀ z₀ r (i : Fin (n + 1)) z₁ k, ∃ C₀ : ℕ, z₀ ∈ F → z₁ ∈ F → ∀ e ≥ C₀, ∀ z' ∈ D i ⊓ Uz z₁, Matrix.vecMul (bz z₀ r) (bz z₁)⁻¹ k * u z₀ ^ C * (t (iz z₀) / t i) ^ e ∈ M.O z'`. Introduce `z₀ r i z₁ k`. Distinguish the cases in `hmem : z₀ ∈ F ∧ z₁ ∈ F`. Take `⟨C₀, hC₀⟩` from `_root_.GlobalTheory.ZH.RatModel.exists_forall_mul_prod_div_pow_mem_O o Ω M (Fin (n + 1)) t (D i ⊓ Uz z₁) i (fun z' hz' => (hDmem i z').1 hz'.1) {iz z₀} (Matrix.vecMul (bz z₀ r) (bz z₁)⁻¹ k * u z₀ ^ C) (fun z' hz' hI => hC1 z₀ r z₁ k C (hC z₀ hmem.1 z₁ hmem.2 r k) z' ⟨(hDmem (iz z …`.

Use `⟨C₀, fun _ _ e he z' hz' => ?_⟩` and prove the remaining obligations. Use `hC₀ e he z' hz'` as an intermediate fact. Rewrite `this` using `[Finset.prod_singleton]`. Then use the resulting hypothesis. Conclude with `⟨0, fun h₀ h₁ => absurd ⟨h₀, h₁⟩ hmem⟩`. Use `choose C2 hC2 using h2`.

Use `set e : ℕ := (F ×ˢ (Finset.univ : Finset J) ×ˢ (Finset.univ : Finset (Fin (n + 1))) ×ˢ F ×ˢ (Finset.univ : Finset J)).sup (fun p => C2 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) with he_def`. Establish `he : ∀ z₀ ∈ F, ∀ z₁ ∈ F, ∀ r i k, C2 z₀ r i z₁ k ≤ e`. Introduce `z₀ hz₀ z₁ hz₁ r i k`. Rewrite using `[he_def]`. Conclude with `Finset.le_sup (f := fun p : M.Z × J × Fin (n + 1) × M.Z × J => C2 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) (b := (z₀, r, i, z₁, k)) (Finset.mem_product.2 ⟨hz₀, Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_product.2 ⟨hz₁, Finset.mem_un …`.

Set `gen : F × J → J → Ω` to `fun p j => bz p.1 p.2 j * u p.1 ^ C * t (iz p.1) ^ e`. Set `eqv` to `Fintype.equivFin (F × J)`. Use `⟨n, t, e, Fintype.card (F × J), fun k => gen (eqv.symm k), hcl, fun z i hzi => ?_⟩` and prove the remaining obligations. Establish `hti : t i ≠ 0` using `hdivne hzi`. Establish `hgen : ∀ p : F × J, (fun j => gen p j / t i ^ e) = (u p.1 ^ C * (t (iz p.1) / t i) ^ e) • bz p.1 p.2`.

Introduce `p`. Use function extensionality and compare the values at `j`. Simplify using `only [gen, Pi.smul_apply, smul_eq_mul, div_pow]`. Clear the denominators using the available nonvanishing facts. Establish `hrange : (Set.range fun k j => gen (eqv.symm k) j / t i ^ e) = Set.range fun p : F × J => fun j => gen p j / t i ^ e`.

Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`. Conclude with `⟨eqv.symm k, rfl⟩`. Introduce and unpack `⟨p, rfl⟩; exact ⟨eqv p, by simp⟩`.

Rewrite using `[hrange]`. Apply `le_antisymm` to reduce the goal to its premises. Take `⟨z₀, hz₀F, hz₀⟩` from `hcover z`. Rewrite using `[hzspan z₀ z (hzle z₀ hz₀)]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨r, rfl⟩`. Use `set g : Ω := u z₀ ^ C * (t (iz z₀) / t i) ^ e with hg`. Establish `htz₀ : t (iz z₀) ≠ 0` using `hzti z₀`. Establish `hg_ne : g ≠ 0` using `mul_ne_zero (pow_ne_zero _ (hu_ne z₀)) (pow_ne_zero _ (div_ne_zero htz₀ hti))`. Establish `hdz₀ : M.Div t (iz z₀) z` using `(hDmem (iz z₀) z).1 ((M.Z.basicOpen_le (fz z₀)) hz₀)`.

Establish `hg_inv : g⁻¹ ∈ M.O z`. Establish `h3 : g⁻¹ = (u z₀)⁻¹ ^ C * (t i / t (iz z₀)) ^ e`. Rewrite using `[hg, mul_inv, ← inv_pow, ← inv_pow, inv_div]`. Rewrite using `[h3]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (hu_inv z₀ z hz₀) _) (Subalgebra.pow_mem _ (hdivratio i hdz₀) _)`.

Establish `hb : bz z₀ r = (⟨g⁻¹, hg_inv⟩ : M.O z) • (fun j => gen (⟨z₀, hz₀F⟩, r) j / t i ^ e)`. Rewrite using `[hgen]`. Use `show bz z₀ r = g⁻¹ • (g • bz z₀ r)`. Rewrite using `[smul_smul, inv_mul_cancel₀ hg_ne, one_smul]`. Rewrite using `[hb]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨(⟨z₀, hz₀F⟩, r), rfl⟩)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩`. Take `⟨z₁, hz₁F, hz₁⟩` from `hcover z`. Establish `hzU : z ∈ Uz z₁` using `hzle z₁ hz₁`.

Rewrite using `[SetLike.mem_coe, hcoord z₁ z hzU]`. Introduce `k`. Simplify using `only`. Rewrite using `[hgen p, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]`. Use `hC2 p.1 p.2 i z₁ k p.1.2 hz₁F e (he p.1 p.1.2 z₁ hz₁F p.2 i k) z ⟨(hDmem i z).2 hzi, hzU⟩` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.ZH.RatModel.exists_isCl_lat_eq_span : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    [IsNoetherianRing o] (M : _root_.GlobalTheory.ZH.RatModel o Ω), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.s → ∀ (J : Type) [Fintype J]
    (EE : M.Lat J), ∃ (n : ℕ) (t : Fin (n + 1) → Ω) (e m : ℕ) (v : Fin m → J → Ω),
    M.IsCl t ∧ ∀ z i, M.Div t i z →
      EE.E z = Submodule.span (M.O z)
        (Set.range fun k j => v k j / t i ^ e) := by
  intro o Ω _ _ _ _ M hproj J _ EE
  obtain ⟨n, t, hcl⟩ := _root_.GlobalTheory.ZH.RatModel.exists_isCl_of_isProjOver hproj
  have hcl' := hcl
  unfold _root_.GlobalTheory.ZH.RatModel.IsCl at hcl'
  obtain ⟨hdiv, hchart⟩ := hcl'
  unfold _root_.GlobalTheory.ZH.RatModel.HasDiv at hdiv
  have hdivne : ∀ {i z}, M.Div t i z → t i ≠ 0 := by
    intro i z h
    unfold _root_.GlobalTheory.ZH.RatModel.Div at h
    exact h.1
  have hdivratio : ∀ {i z} (j : Fin (n + 1)), M.Div t i z →
      t j / t i ∈ M.O z := by
    intro i z j h
    unfold _root_.GlobalTheory.ZH.RatModel.Div at h
    exact h.2 j
  have hD : ∀ i, ∃ U : M.Z.Opens, (∀ z, z ∈ U ↔ M.Div t i z) ∧
      (t i ≠ 0 → IsAffineOpen U) := by
    intro i
    by_cases hi : t i ≠ 0
    · obtain ⟨U, hU, hUeq, _⟩ := hchart i hi
      refine ⟨U, fun z => ?_, fun _ => hU⟩
      rw [← SetLike.mem_coe, hUeq]
      rfl
    · refine ⟨⊥, fun z => ⟨fun h => absurd h (by simp), fun h => absurd (hdivne h) hi⟩, fun h => absurd h hi⟩
  choose D hDmem hDaff using hD
  have hloc : ∀ z : M.Z, ∃ (U : M.Z.Opens) (b : Matrix J J Ω) (i : Fin (n + 1)) (f : Γ(M.Z, D i)),
      z ∈ M.Z.basicOpen f ∧ M.Z.basicOpen f ≤ U ∧ b.det ≠ 0 ∧ t i ≠ 0 ∧
      ∀ z' ∈ U, EE.E z' = Submodule.span (M.O z') (Set.range b) := by
    intro z
    obtain ⟨U, b, hzU, hb, hspan⟩ := EE.loc z
    obtain ⟨i, hi⟩ := hdiv z
    have hzD : z ∈ D i := (hDmem i z).2 hi
    obtain ⟨f, hfle, hzf⟩ := (hDaff i (hdivne hi)).exists_basicOpen_le (V := D i ⊓ U) ⟨z, hzD, hzU⟩ hzD
    exact ⟨U, b, i, f, hzf, hfle.trans inf_le_right, hb, hdivne hi, hspan⟩
  choose Uz bz iz fz hzmem hzle hzdet hzti hzspan using hloc

  set u : M.Z → Ω := fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valF M.pt (D (iz z)) (fz z) with hu_def
  have hu_mem : ∀ z z', z' ∈ D (iz z) → u z ∈ M.O z' :=
    fun z z' hz' => _root_.GlobalTheory.ZH.RatModel.valF_mem_O hz' (fz z)
  have hzD : ∀ z, z ∈ D (iz z) := fun z => (M.Z.basicOpen_le (fz z)) (hzmem z)
  have hu_unit : ∀ z z' (hz' : z' ∈ D (iz z)), z' ∈ M.Z.basicOpen (fz z) ↔
      (u z ≠ 0 ∧ (u z)⁻¹ ∈ M.O z') := by
    intro z z' hz'
    rw [← _root_.GlobalTheory.ZH.RatModel.isUnit_valF_iff hz' (fz z), _root_.GlobalTheory.ZH.RatModel.isUnit_O_iff]
  have hu_ne : ∀ z, u z ≠ 0 := fun z => ((hu_unit z z (hzD z)).1 (hzmem z)).1
  have hu_inv : ∀ z z', z' ∈ M.Z.basicOpen (fz z) → (u z)⁻¹ ∈ M.O z' :=
    fun z z' h => ((hu_unit z z' ((M.Z.basicOpen_le (fz z)) h)).1 h).2

  haveI := M.noetherianSpace_of_isNoetherianRing
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun z => (M.Z.basicOpen (fz z) : Set M.Z))
    (fun z => (M.Z.basicOpen (fz z)).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hzmem x⟩)
  have hcover : ∀ z : M.Z, ∃ z₀ ∈ F, z ∈ M.Z.basicOpen (fz z₀) := by
    intro z
    have := hF (Set.mem_univ z)
    simp only [Set.mem_iUnion] at this
    obtain ⟨z₀, hz₀, h⟩ := this
    exact ⟨z₀, hz₀, h⟩

  have hcoord : ∀ z₁ z', z' ∈ Uz z₁ → ∀ w : J → Ω, w ∈ EE.E z' ↔
      ∀ k, Matrix.vecMul w (bz z₁)⁻¹ k ∈ M.O z' := by
    intro z₁ z' hz' w
    rw [hzspan z₁ z' hz']
    exact mem_span_range_iff_vecMul_inv_mem _ _ (hzdet z₁) w
  have hrow : ∀ z₀ r z', z' ∈ Uz z₀ → bz z₀ r ∈ EE.E z' := by
    intro z₀ r z' hz'
    rw [hzspan z₀ z' hz']
    exact Submodule.subset_span ⟨r, rfl⟩

  have h1 : ∀ z₀ r z₁ k, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ z' ∈ D (iz z₀) ⊓ Uz z₁,
      Matrix.vecMul (bz z₀ r) (bz z₁)⁻¹ k * u z₀ ^ C ∈ M.O z' := by
    intro z₀ r z₁ k
    refine _root_.GlobalTheory.ZH.RatModel.exists_forall_mul_pow_mem_O (D (iz z₀) ⊓ Uz z₁) (hu_ne z₀)
      (fun z' hz' => hu_mem z₀ z' hz'.1) (fun z' hz' hinv => ?_)
    have hb : z' ∈ M.Z.basicOpen (fz z₀) := ((hu_unit z₀ z' hz'.1).2 ⟨hu_ne z₀, hinv⟩)
    exact (hcoord z₁ z' hz'.2 _).1 (hrow z₀ r z' (hzle z₀ hb)) k
  choose C1 hC1 using h1
  set C : ℕ := (F ×ˢ F ×ˢ (Finset.univ : Finset J) ×ˢ (Finset.univ : Finset J)).sup
    (fun p => C1 p.1 p.2.2.1 p.2.1 p.2.2.2) with hC_def
  have hC : ∀ z₀ ∈ F, ∀ z₁ ∈ F, ∀ r k, C1 z₀ r z₁ k ≤ C := by
    intro z₀ hz₀ z₁ hz₁ r k
    rw [hC_def]
    exact Finset.le_sup (f := fun p : M.Z × M.Z × J × J => C1 p.1 p.2.2.1 p.2.1 p.2.2.2)
      (b := (z₀, z₁, r, k)) (Finset.mem_product.2 ⟨hz₀, Finset.mem_product.2 ⟨hz₁,
        Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩⟩)

  have h2 : ∀ z₀ r (i : Fin (n + 1)) z₁ k, ∃ C₀ : ℕ, z₀ ∈ F → z₁ ∈ F → ∀ e ≥ C₀, ∀ z' ∈ D i ⊓ Uz z₁,
      Matrix.vecMul (bz z₀ r) (bz z₁)⁻¹ k * u z₀ ^ C * (t (iz z₀) / t i) ^ e ∈
        M.O z' := by
    intro z₀ r i z₁ k
    by_cases hmem : z₀ ∈ F ∧ z₁ ∈ F
    · obtain ⟨C₀, hC₀⟩ := _root_.GlobalTheory.ZH.RatModel.exists_forall_mul_prod_div_pow_mem_O o Ω M (Fin (n + 1)) t
        (D i ⊓ Uz z₁) i (fun z' hz' => (hDmem i z').1 hz'.1) {iz z₀}
        (Matrix.vecMul (bz z₀ r) (bz z₁)⁻¹ k * u z₀ ^ C)
        (fun z' hz' hI => hC1 z₀ r z₁ k C (hC z₀ hmem.1 z₁ hmem.2 r k) z'
          ⟨(hDmem (iz z₀) z').2 (hI _ (Finset.mem_singleton_self _)), hz'.2⟩)
        (fun j hj => by rw [Finset.mem_singleton.1 hj]; exact hzti z₀)
      refine ⟨C₀, fun _ _ e he z' hz' => ?_⟩
      have := hC₀ e he z' hz'
      rwa [Finset.prod_singleton] at this
    · exact ⟨0, fun h₀ h₁ => absurd ⟨h₀, h₁⟩ hmem⟩
  choose C2 hC2 using h2
  set e : ℕ := (F ×ˢ (Finset.univ : Finset J) ×ˢ (Finset.univ : Finset (Fin (n + 1))) ×ˢ F ×ˢ
    (Finset.univ : Finset J)).sup (fun p => C2 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) with he_def
  have he : ∀ z₀ ∈ F, ∀ z₁ ∈ F, ∀ r i k, C2 z₀ r i z₁ k ≤ e := by
    intro z₀ hz₀ z₁ hz₁ r i k
    rw [he_def]
    exact Finset.le_sup (f := fun p : M.Z × J × Fin (n + 1) × M.Z × J =>
        C2 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (b := (z₀, r, i, z₁, k)) (Finset.mem_product.2 ⟨hz₀, Finset.mem_product.2 ⟨Finset.mem_univ _,
        Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_product.2 ⟨hz₁, Finset.mem_univ _⟩⟩⟩⟩)

  let gen : F × J → J → Ω := fun p j => bz p.1 p.2 j * u p.1 ^ C * t (iz p.1) ^ e
  let eqv := Fintype.equivFin (F × J)
  refine ⟨n, t, e, Fintype.card (F × J), fun k => gen (eqv.symm k), hcl, fun z i hzi => ?_⟩
  have hti : t i ≠ 0 := hdivne hzi
  have hgen : ∀ p : F × J, (fun j => gen p j / t i ^ e) =
      (u p.1 ^ C * (t (iz p.1) / t i) ^ e) • bz p.1 p.2 := by
    intro p
    funext j
    simp only [gen, Pi.smul_apply, smul_eq_mul, div_pow]
    field_simp
  have hrange : (Set.range fun k j => gen (eqv.symm k) j / t i ^ e) =
      Set.range fun p : F × J => fun j => gen p j / t i ^ e := by
    ext w
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨eqv.symm k, rfl⟩
    · rintro ⟨p, rfl⟩; exact ⟨eqv p, by simp⟩
  rw [hrange]
  apply le_antisymm
  ·
    obtain ⟨z₀, hz₀F, hz₀⟩ := hcover z
    rw [hzspan z₀ z (hzle z₀ hz₀)]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨r, rfl⟩
    set g : Ω := u z₀ ^ C * (t (iz z₀) / t i) ^ e with hg
    have htz₀ : t (iz z₀) ≠ 0 := hzti z₀
    have hg_ne : g ≠ 0 := mul_ne_zero (pow_ne_zero _ (hu_ne z₀)) (pow_ne_zero _ (div_ne_zero htz₀ hti))
    have hdz₀ : M.Div t (iz z₀) z :=
      (hDmem (iz z₀) z).1 ((M.Z.basicOpen_le (fz z₀)) hz₀)
    have hg_inv : g⁻¹ ∈ M.O z := by
      have h3 : g⁻¹ = (u z₀)⁻¹ ^ C * (t i / t (iz z₀)) ^ e := by
        rw [hg, mul_inv, ← inv_pow, ← inv_pow, inv_div]
      rw [h3]
      exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (hu_inv z₀ z hz₀) _)
        (Subalgebra.pow_mem _ (hdivratio i hdz₀) _)
    have hb : bz z₀ r = (⟨g⁻¹, hg_inv⟩ : M.O z) •
        (fun j => gen (⟨z₀, hz₀F⟩, r) j / t i ^ e) := by
      rw [hgen]
      show bz z₀ r = g⁻¹ • (g • bz z₀ r)
      rw [smul_smul, inv_mul_cancel₀ hg_ne, one_smul]
    rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(⟨z₀, hz₀F⟩, r), rfl⟩)
  ·
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, rfl⟩
    obtain ⟨z₁, hz₁F, hz₁⟩ := hcover z
    have hzU : z ∈ Uz z₁ := hzle z₁ hz₁
    rw [SetLike.mem_coe, hcoord z₁ z hzU]
    intro k
    dsimp only
    rw [hgen p, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]
    have := hC2 p.1 p.2 i z₁ k p.1.2 hz₁F e (he p.1 p.1.2 z₁ hz₁F p.2 i k) z ⟨(hDmem i z).2 hzi, hzU⟩
    convert this using 1
    ring

end GlobalTheory.ZH.RatModel
end
