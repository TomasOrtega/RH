import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingYAlt
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSDLatLatK
import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseAtCompan

/- English proof (translation)
Substitute `h` using the available equality. Use `show x ∈ reL rfl L ↔ reV rfl E x ∈ L`. Rewrite using `[reL_rfl, reV_rfl]`.
-/
theorem mem_reL_symm {E : Type} [Field E] [NumberField E] {a b : ℕ} (h : a = b) (L : Submodule (𝓞 E) (Fin b → E))
    (x : Fin a → E) : x ∈ reL h.symm L ↔ reV h E x ∈ L := by
  subst h
  show x ∈ reL rfl L ↔ reV rfl E x ∈ L
  rw [reL_rfl, reV_rfl]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, e⟩`. Establish `e' : toLE co z = toLE co y` using `e`. Rewrite `hz` using `[(toLE co).injective e']`. Then use the resulting hypothesis. Introduce `hy`.

Conclude with `⟨y, hy, rfl⟩`.
-/
theorem mem_mvL_iff {E : Type} [Field E] [NumberField E] {N : ℕ} (co : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E))
    (y : Fin N → E) : (co : Matrix (Fin N) (Fin N) E) *ᵥ y ∈ mvL co Λ ↔ y ∈ Λ := by
  constructor
  · rintro ⟨z, hz, e⟩
    have e' : toLE co z = toLE co y := e
    rwa [(toLE co).injective e'] at hz
  · intro hy
    exact ⟨y, hy, rfl⟩

/- English proof (translation)
Set `M : Submodule (𝓞 E) (Fin n → E)` to `{ carrier := {y | (T : E) • y ∈ S.Lb} add_mem' := fun {x z} hx hz => by show (T : E) • (x + z) ∈ S.Lb`. Rewrite using `[smul_add]`. Conclude with `add_mem hx hz`. Use the proof step `zero_mem' := by show (T : E) • (0 : Fin n → E) ∈ S.Lb; rw [smul_zero]; exact zero_mem _`. Use the proof step `smul_mem' := fun c x hx => by show (T : E) • (c • x) ∈ S.Lb`.

Rewrite using `[smul_comm]`. Conclude with `S.Lb.smul_mem c hx }`. Establish `hd : Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J S.Lb) ≤ M`. Rewrite using `[Submodule.span_le]`. Introduce `z hz`.

Rewrite `hz` using `[← hσ]`. Conclude with `S.Lb_dual z hz`. Establish `hL : S.Lb ≤ Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J S.Lb)`. Introduce `x hx`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `S.Lb_int x hx` as an intermediate fact. Rewrite `this` using `[hσ]`. Then use the resulting hypothesis. Conclude with `hd (sup_le hL Submodule.smul_le_right hy)`.
-/
theorem smul_mem_of_mem_compan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {R : Ranks} (sp : Spaces R F E) {σ : E →ₐ[F] E} (hσ : (σ : E →+* E) = (sp.cm.sig : E →+* E)) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (a : 𝓞 E)
    (y : Fin n → E) (hy : y ∈ compan (sp := sp) J a S.Lb) : (T : E) • y ∈ S.Lb := by
  let M : Submodule (𝓞 E) (Fin n → E) :=
    { carrier := {y | (T : E) • y ∈ S.Lb}
      add_mem' := fun {x z} hx hz => by
        show (T : E) • (x + z) ∈ S.Lb
        rw [smul_add]; exact add_mem hx hz
      zero_mem' := by show (T : E) • (0 : Fin n → E) ∈ S.Lb; rw [smul_zero]; exact zero_mem _
      smul_mem' := fun c x hx => by
        show (T : E) • (c • x) ∈ S.Lb
        rw [smul_comm]; exact S.Lb.smul_mem c hx }
  have hd : Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J S.Lb) ≤ M := by
    rw [Submodule.span_le]
    intro z hz
    rw [← hσ] at hz
    exact S.Lb_dual z hz
  have hL : S.Lb ≤ Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J S.Lb) := by
    intro x hx
    apply Submodule.subset_span
    have := S.Lb_int x hx
    rwa [hσ] at this
  exact hd (sup_le hL Submodule.smul_le_right hy)

/- English proof (translation)
Introduce `D X0 u w hg i hi T bad S co a hT hstd`. Establish `hr` using `rankN D (i + 1) hi`. Use `set C := compan (sp := D.sp) (gramN D (i + 1) hi) a S.Lb with hC`. Establish `h1 : latAd (1 : GL (Fin (D.R.N (i + 1))) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) S.Lb = S.Lb`. Rewrite using `[GlobalTheory.SDCompan.latAd_eq]`.

Conclude with `Formalism.L2.GlobalTheoryTheory.Comp.glob_one ⟨S.Lb_fin, S.Lb_span⟩`. Establish `hm : mvL co C = StandardLatticesGL3.stdL D (D.R.N (i + 1))`. Rewrite using `[← hstd, GlobalTheory.TwU.latCo, h1]`. Establish `hCi : ∀ y, y ∈ C ↔ ∀ k, ((co : Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E) *ᵥ y) k ∈ (algebraMap (𝓞 D.host.E) D.host.E).range`. Introduce `y`.

Rewrite using `[← mem_mvL_iff co C y, hm]`. Unfold `StandardLatticesGL3.stdL`. Rewrite using `[Submodule.mem_pi]`. Simplify using `only [Set.mem_univ, true_imp_iff, Submodule.mem_one, RingHom.mem_range]`. Establish `hTC : ∀ y ∈ C, (T : D.host.E) • y ∈ S.Lb` using `smul_mem_of_mem_compan D.sp rfl S a`.

Use `IsBaseAt.congr X0 u w hg (isBaseAt_free X0 u w hg _ (reL (rankN D (i + 1) hi).symm C) fun x => ?_) fun w' hw => ?_` and prove the remaining obligations. Rewrite using `[mem_reL_symm, hCi]`. Conclude with `free_re (rankN D (i + 1) hi) co _ x`. Establish `hT' : ((T : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal` using `natCast_notMem w' (D.what₂.places.resChar_prime w) hw hT`. Use `(loc_lattice_eq_of_torsion_away w' _ _ T hT' ?_ ?_).symm` and prove the remaining obligations.

Introduce `x hx`. Rewrite `hx`, the goal using `[mem_reL_symm hr]`. Conclude with `le_sup_left (a := S.Lb) hx`. Introduce `y hy`. Rewrite `hy`, the goal using `[mem_reL_symm hr]`.

Rewrite using `[map_smul]`. Conclude with `hTC _ hy`.
-/
theorem isBaseAt_inv_of_latCo : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {i : ℕ} (hi : i + 1 ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) (gramN D (i + 1) hi) T D.R.f bad) (co : GL (Fin (D.R.N (i + 1))) D.host.E) (a : 𝓞 D.host.E), ¬ (D.what₂.places.resChar w) ∣ T → GlobalTheory.TwU.latCo D.sp (gramN D (i + 1) hi) co a 1 S.Lb = StandardLatticesGL3.stdL D (D.R.N (i + 1)) → IsBaseAt X0 u w hg ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm co⁻¹) (reL (rankN D (i + 1) hi).symm S.Lb) := by
  intro D X0 u w hg i hi T bad S co a hT hstd
  have hr := rankN D (i + 1) hi
  set C := compan (sp := D.sp) (gramN D (i + 1) hi) a S.Lb with hC
  have h1 : latAd (1 : GL (Fin (D.R.N (i + 1))) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) S.Lb = S.Lb := by
    rw [GlobalTheory.SDCompan.latAd_eq]
    exact Formalism.L2.GlobalTheoryTheory.Comp.glob_one ⟨S.Lb_fin, S.Lb_span⟩
  have hm : mvL co C = StandardLatticesGL3.stdL D (D.R.N (i + 1)) := by
    rw [← hstd, GlobalTheory.TwU.latCo, h1]
  have hCi : ∀ y, y ∈ C ↔ ∀ k, ((co : Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E) *ᵥ y) k ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    rw [← mem_mvL_iff co C y, hm]
    unfold StandardLatticesGL3.stdL
    rw [Submodule.mem_pi]
    simp only [Set.mem_univ, true_imp_iff, Submodule.mem_one, RingHom.mem_range]
  have hTC : ∀ y ∈ C, (T : D.host.E) • y ∈ S.Lb :=
    smul_mem_of_mem_compan D.sp rfl S a
  refine IsBaseAt.congr X0 u w hg (isBaseAt_free X0 u w hg _ (reL (rankN D (i + 1) hi).symm C) fun x => ?_) fun w' hw => ?_
  · rw [mem_reL_symm, hCi]
    exact free_re (rankN D (i + 1) hi) co _ x
  · have hT' : ((T : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal :=
      natCast_notMem w' (D.what₂.places.resChar_prime w) hw hT
    refine (loc_lattice_eq_of_torsion_away w' _ _ T hT' ?_ ?_).symm
    · intro x hx
      rw [mem_reL_symm hr] at hx ⊢
      exact le_sup_left (a := S.Lb) hx
    · intro y hy
      rw [mem_reL_symm hr] at hy ⊢
      rw [map_smul]
      exact hTC _ hy

end GlobalTheory.BaseAtCompan
