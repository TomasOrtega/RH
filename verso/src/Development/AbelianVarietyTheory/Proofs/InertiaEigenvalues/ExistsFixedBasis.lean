import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.GaloisDescentLattice

/- English proof (translation)
Rewrite using `[← algebraMap_smul K.E a y, ← algebraMap_smul K.E b (B.σ y), Algebra.smul_def, Algebra.smul_def, map_mul, B.σ_alg, hab]`.
-/
theorem sigma_smul {K : UQ} (B : InvAlg K) {a b : K.O}
    (hab : K.c (algebraMap K.O K.E a) = algebraMap K.O K.E b) (y : B.A) :
    B.σ (a • y) = b • B.σ y := by
  rw [← algebraMap_smul K.E a y, ← algebraMap_smul K.E b (B.σ y), Algebra.smul_def, Algebra.smul_def,
    map_mul, B.σ_alg, hab]

/- English proof (translation)
Introduce `K B M hM hσ`. Take `⟨d, d', hdd', hunit⟩` from `K.c_res`. Establish `hd'd : K.c (algebraMap K.O K.E d') = algebraMap K.O K.E d` using `by rw [← hdd', K.c_c]`. Take `⟨u, hu⟩` from `(IsLocalRing.notMem_maximalIdeal.mp hunit).exists_left_inv`. Set `S : Type` to `{y : B.A // y ∈ M ∧ B.σ y = y}`.

Set `v : S → M` to `fun s => ⟨s.1, s.2.1⟩`. Establish `hspan : Submodule.span K.O (Set.range v) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨y, hy⟩ -`. Establish `hy' : B.σ y ∈ M` using `hσ y hy`.

Establish `h1m : y + B.σ y ∈ M` using `M.add_mem hy hy'`. Establish `h2m : d • y + d' • B.σ y ∈ M` using `M.add_mem (M.smul_mem d hy) (M.smul_mem d' hy')`. Establish `h1f : B.σ (y + B.σ y) = y + B.σ y` using `by rw [map_add, B.σ_σ, add_comm]`. Establish `h2f : B.σ (d • y + d' • B.σ y) = d • y + d' • B.σ y`. Rewrite using `[map_add, sigma_smul B hdd', sigma_smul B hd'd, B.σ_σ, add_comm]`.

Establish `hmem1 : (⟨y + B.σ y, h1m⟩ : M) ∈ Submodule.span K.O (Set.range v)` using `Submodule.subset_span ⟨⟨_, h1m, h1f⟩, rfl⟩`. Establish `hmem2 : (⟨d • y + d' • B.σ y, h2m⟩ : M) ∈ Submodule.span K.O (Set.range v)` using `Submodule.subset_span ⟨⟨_, h2m, h2f⟩, rfl⟩`. Establish `hy_eq : (⟨y, hy⟩ : M) = u • ((⟨d • y + d' • B.σ y, h2m⟩ : M) - d' • (⟨y + B.σ y, h1m⟩ : M))`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_smul, Submodule.coe_sub, smul_add]`.

Establish `: d • y + d' • B.σ y - (d' • y + d' • B.σ y) = (d - d') • y` using `by rw [sub_smul]; abel`. Rewrite using `[this, smul_smul, hu, one_smul]`. Rewrite using `[hy_eq]`. Conclude with `Submodule.smul_mem _ _ (Submodule.sub_mem _ hmem2 (Submodule.smul_mem _ _ hmem1))`. Use `haveI : Module.Finite K.O M := Module.Finite.iff_fg.mpr hM.1`.

Use `haveI : Module.IsTorsionFree K.O M := ⟨fun r hr x y hxy => by`. Establish `hr0 : r ≠ 0` using `hr.ne_zero`. Establish `h0 : algebraMap K.O K.E r ≠ 0`. Introduce `h; exact hr0 (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))`. Express the relevant statement in the definitionally equal form `r • x = r • y at hxy`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg Subtype.val hxy` as an intermediate fact. Simplify using `only [Submodule.coe_smul] at this`. Rewrite `this` using `[← algebraMap_smul K.E r (x : B.A), ← algebraMap_smul K.E r (y : B.A)]`. Conclude with `smul_right_injective B.A h0 this⟩`.

Use `haveI : Module.Free K.O M := Module.free_of_finite_type_torsion_free'`. Use `haveI : Module.FinitePresentation K.O M := Module.finitePresentation_of_finite K.O M`. Take `⟨κ, a, b, hb⟩` from `Module.exists_basis_of_span_of_flat v hspan`. Use `haveI : Finite κ := Module.Finite.finite_basis b`. Set `w : κ → B.A` to `fun i => (b i : B.A)`.

Establish `hwO : LinearIndependent K.O w` using `b.linearIndependent.map' M.subtype M.ker_subtype`. Establish `hwE : LinearIndependent K.E w` using `(LinearIndependent.iff_fractionRing K.O K.E).mp hwO`. Establish `hspanO : Submodule.span K.O (Set.range w) = M`. Establish `: Set.range w = M.subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]`. Establish `hspanE : ⊤ ≤ Submodule.span K.E (Set.range w)`. Rewrite using `[← hM.2, Submodule.span_le]`. Introduce `x hx`.

Establish `: x ∈ Submodule.span K.O (Set.range w)` using `by rw [hspanO]; exact hx`. Conclude with `Submodule.span_le_restrictScalars K.O K.E _ this`. Set `bE : Module.Basis κ K.E B.A` to `Module.Basis.mk hwE hspanE`. Set `e` to `bE.reindex (bE.indexEquiv (Module.finBasis K.E B.A))`. Use `⟨e, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Module.Basis.range_reindex, Module.Basis.coe_mk]`. Conclude with `hspanO`. Introduce `i`. Rewrite using `[Module.Basis.reindex_apply, Module.Basis.mk_apply]`. Use `show B.σ (b _ : B.A) = (b _ : B.A)`.

Rewrite using `[hb]`. Conclude with `(a _).2.2`.
-/
theorem exists_fixed_basis : ∀ (K : UQ) (B : InvAlg K) (M : Submodule K.O B.A), IsLat K.O K.E M →
    (∀ y ∈ M, B.σ y ∈ M) → ∃ e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A,
      Submodule.span K.O (Set.range e) = M ∧ ∀ i, B.σ (e i) = e i := by
  intro K B M hM hσ
  obtain ⟨d, d', hdd', hunit⟩ := K.c_res
  have hd'd : K.c (algebraMap K.O K.E d') = algebraMap K.O K.E d := by rw [← hdd', K.c_c]
  obtain ⟨u, hu⟩ := (IsLocalRing.notMem_maximalIdeal.mp hunit).exists_left_inv

  let S : Type := {y : B.A // y ∈ M ∧ B.σ y = y}
  let v : S → M := fun s => ⟨s.1, s.2.1⟩
  have hspan : Submodule.span K.O (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hy' : B.σ y ∈ M := hσ y hy
    have h1m : y + B.σ y ∈ M := M.add_mem hy hy'
    have h2m : d • y + d' • B.σ y ∈ M := M.add_mem (M.smul_mem d hy) (M.smul_mem d' hy')
    have h1f : B.σ (y + B.σ y) = y + B.σ y := by rw [map_add, B.σ_σ, add_comm]
    have h2f : B.σ (d • y + d' • B.σ y) = d • y + d' • B.σ y := by
      rw [map_add, sigma_smul B hdd', sigma_smul B hd'd, B.σ_σ, add_comm]
    have hmem1 : (⟨y + B.σ y, h1m⟩ : M) ∈ Submodule.span K.O (Set.range v) :=
      Submodule.subset_span ⟨⟨_, h1m, h1f⟩, rfl⟩
    have hmem2 : (⟨d • y + d' • B.σ y, h2m⟩ : M) ∈ Submodule.span K.O (Set.range v) :=
      Submodule.subset_span ⟨⟨_, h2m, h2f⟩, rfl⟩
    have hy_eq : (⟨y, hy⟩ : M) = u • ((⟨d • y + d' • B.σ y, h2m⟩ : M) - d' • (⟨y + B.σ y, h1m⟩ : M)) := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Submodule.coe_sub, smul_add]
      have : d • y + d' • B.σ y - (d' • y + d' • B.σ y) = (d - d') • y := by rw [sub_smul]; abel
      rw [this, smul_smul, hu, one_smul]
    rw [hy_eq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hmem2 (Submodule.smul_mem _ _ hmem1))

  haveI : Module.Finite K.O M := Module.Finite.iff_fg.mpr hM.1
  haveI : Module.IsTorsionFree K.O M := ⟨fun r hr x y hxy => by
    have hr0 : r ≠ 0 := hr.ne_zero
    have h0 : algebraMap K.O K.E r ≠ 0 := by
      intro h; exact hr0 (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))
    change r • x = r • y at hxy
    apply Subtype.ext
    have := congrArg Subtype.val hxy
    simp only [Submodule.coe_smul] at this
    rw [← algebraMap_smul K.E r (x : B.A), ← algebraMap_smul K.E r (y : B.A)] at this
    exact smul_right_injective B.A h0 this⟩
  haveI : Module.Free K.O M := Module.free_of_finite_type_torsion_free'
  haveI : Module.FinitePresentation K.O M := Module.finitePresentation_of_finite K.O M
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat v hspan
  haveI : Finite κ := Module.Finite.finite_basis b
  let w : κ → B.A := fun i => (b i : B.A)
  have hwO : LinearIndependent K.O w :=
    b.linearIndependent.map' M.subtype M.ker_subtype
  have hwE : LinearIndependent K.E w := (LinearIndependent.iff_fractionRing K.O K.E).mp hwO
  have hspanO : Submodule.span K.O (Set.range w) = M := by
    have : Set.range w = M.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspanE : ⊤ ≤ Submodule.span K.E (Set.range w) := by
    rw [← hM.2, Submodule.span_le]
    intro x hx
    have : x ∈ Submodule.span K.O (Set.range w) := by rw [hspanO]; exact hx
    exact Submodule.span_le_restrictScalars K.O K.E _ this
  let bE : Module.Basis κ K.E B.A := Module.Basis.mk hwE hspanE
  let e := bE.reindex (bE.indexEquiv (Module.finBasis K.E B.A))
  refine ⟨e, ?_, ?_⟩
  · rw [Module.Basis.range_reindex, Module.Basis.coe_mk]; exact hspanO
  · intro i
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
    show B.σ (b _ : B.A) = (b _ : B.A)
    rw [hb]
    exact (a _).2.2

end GlobalTheory.GaloisDescentLattice
