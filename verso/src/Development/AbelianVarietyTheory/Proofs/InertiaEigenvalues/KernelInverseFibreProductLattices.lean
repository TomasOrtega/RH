import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd

noncomputable section

namespace GlobalTheory.RedFun.SubLat

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.TopSteps.StdAdm
open scoped LaurentSeries PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL]

def subLattice [IsDomain O] [IsPrincipalIdealRing O] (T : LocLat G Qp LL O) {lam : O}
    (hl : algebraMap O LL lam ≠ 0) (P : Submodule O ↥T.L.T) (hg : ∀ g, ∀ x ∈ P, latRep T.L g x ∈ P)
    (hP : ∀ x, lam • x ∈ P) : Lattice (O := O) T.ρ where
  T := P.map T.L.T.subtype
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨latRep T.L g x, hg g x hx, rfl⟩
  fg := by
    have := finite_lat T
    exact (IsNoetherian.noetherian _).map _
  free := by
    have := finite_lat T
    have := T.L.free
    have : Module.Free O ↥P := Module.free_of_finite_type_torsion_free'
    exact Module.Free.of_equiv (Submodule.equivMapOfInjective _ T.L.T.injective_subtype _)
  span := by
    rw [eq_top_iff, ← T.L.span, Submodule.span_le]
    intro y hy
    have h1 : lam • y ∈ P.map T.L.T.subtype := ⟨lam • ⟨y, hy⟩, hP _, rfl⟩
    have h2 := Submodule.smul_mem _ (algebraMap O LL lam)⁻¹ (Submodule.subset_span (R := LL) h1)
    rwa [← algebraMap_smul LL lam y, inv_smul_smul₀ hl] at h2

variable {k : Type} [Field k] [Algebra O k]

omit [Algebra O LL] in

/- English proof (translation)
Use extensionality with `i`. Simplify using `[Algebra.smul_def, hk]`.
-/
theorem lam_smul {lam : O} (hk : algebraMap O k lam = 0) {m : ℕ} (t : Fin m → k) : lam • t = 0 := by
  ext i
  simp [Algebra.smul_def, hk]

/- English proof (translation)
Establish `hq2 : ∀ σ x, q (latRep T.L σ x) = A.ρ σ (q x)` using `hq.2`. Establish `hP : ∀ x, lam • x ∈ LinearMap.ker q` using `fun x => by`. Rewrite using `[LinearMap.mem_ker, map_smul, lam_smul hk]`. Establish `hg : ∀ σ, ∀ x ∈ LinearMap.ker q, latRep T.L σ x ∈ LinearMap.ker q` using `fun σ x hx => by`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`.

Rewrite using `[hq2, hx, map_zero]`. Use `⟨{ T with L := subLattice T hl (LinearMap.ker q) hg hP }, ⟨LinearMap.id, fun _ _ => rfl, continuous_id, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, -, rfl⟩`. Conclude with `y.2`. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨x, ⟨x, hx, rfl⟩, rfl⟩`. Introduce and unpack `⟨_, ⟨z, hz, rfl⟩, h⟩`. Establish `hzx : z = x` using `Subtype.ext h`.

Substitute `hzx` using the available equality. Conclude with `hz`.
-/
theorem exists_ker [IsDomain O] [IsPrincipalIdealRing O] {lam : O} (hl : algebraMap O LL lam ≠ 0)
    (hk : algebraMap O k lam = 0) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
    (hq : Onto T A q) : ∃ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L),
      ∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x := by
  have hq2 : ∀ σ x, q (latRep T.L σ x) = A.ρ σ (q x) := hq.2
  have hP : ∀ x, lam • x ∈ LinearMap.ker q := fun x => by
    rw [LinearMap.mem_ker, map_smul, lam_smul hk]
  have hg : ∀ σ, ∀ x ∈ LinearMap.ker q, latRep T.L σ x ∈ LinearMap.ker q := fun σ x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hq2, hx, map_zero]
  refine ⟨{ T with L := subLattice T hl (LinearMap.ker q) hg hP },
    ⟨LinearMap.id, fun _ _ => rfl, continuous_id, ?_⟩, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · intro x
    constructor
    · intro hx
      exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, h⟩
      have hzx : z = x := Subtype.ext h
      subst hzx
      exact hz

/- English proof (translation)
Establish `hsurj : Function.Surjective f.f`. Establish `hle : Submodule.span LL (T.L.T : Set T.V) ≤ LinearMap.range f.f`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Take `⟨y, -, hy⟩` from `h x hx`.

Use `⟨(algebraMap O LL lam)⁻¹ • y, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hy, ← algebraMap_smul LL lam x, inv_smul_smul₀ hl]`. Rewrite `hle` using `[T.L.span]`. Conclude with `fun x => hle Submodule.mem_top`. Set `e` to `LinearEquiv.ofBijective f.f ⟨hf, hsurj⟩`.

Establish `h1 : ∀ z, f.f (e.symm z) = z` using `fun z => e.apply_symm_apply z`. Set `c` to `algebraMap O LL lam`. Use `⟨⟨c • (e.symm : T.V →ₗ[LL] T'.V), ?_, IsModuleTopology.continuous_of_linearMap _, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `σ x`. Apply `hf` to reduce the goal to its premises.

Simplify using `only [LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul, f.equiv, h1]`. Introduce `x hx`. Take `⟨y, hy, hfy⟩` from `h x hx`. Establish `hxy : (c • (e.symm : T.V →ₗ[LL] T'.V)) x = y`. Apply `hf` to reduce the goal to its premises.

Rewrite using `[LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe, h1, hfy, algebraMap_smul]`. Rewrite using `[hxy]`. Conclude with `hy`. Introduce `x show f.f ((c • (e.symm : T.V →ₗ[LL] T'.V)) x) = c • x`. Rewrite using `[LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe, h1]`.
-/
theorem exists_inv {lam : O} (hl : algebraMap O LL lam ≠ 0) (T T' : LocLat G Qp LL O) (f : LatHom T'.L T.L)
    (hf : Function.Injective f.f) (h : ∀ x ∈ T.L.T, ∃ y ∈ T'.L.T, f.f y = lam • x) :
    ∃ h : LatHom T.L T'.L, ∀ x, f.f (h.f x) = algebraMap O LL lam • x := by
  have hsurj : Function.Surjective f.f := by
    have hle : Submodule.span LL (T.L.T : Set T.V) ≤ LinearMap.range f.f := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨y, -, hy⟩ := h x hx
      refine ⟨(algebraMap O LL lam)⁻¹ • y, ?_⟩
      rw [map_smul, hy, ← algebraMap_smul LL lam x, inv_smul_smul₀ hl]
    rw [T.L.span] at hle
    exact fun x => hle Submodule.mem_top
  let e := LinearEquiv.ofBijective f.f ⟨hf, hsurj⟩
  have h1 : ∀ z, f.f (e.symm z) = z := fun z => e.apply_symm_apply z
  let c := algebraMap O LL lam
  refine ⟨⟨c • (e.symm : T.V →ₗ[LL] T'.V), ?_, IsModuleTopology.continuous_of_linearMap _, ?_⟩, ?_⟩
  · intro σ x
    apply hf
    simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul, f.equiv, h1]
  · intro x hx
    obtain ⟨y, hy, hfy⟩ := h x hx
    have hxy : (c • (e.symm : T.V →ₗ[LL] T'.V)) x = y := by
      apply hf
      rw [LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe, h1, hfy, algebraMap_smul]
    rw [hxy]
    exact hy
  · intro x
    show f.f ((c • (e.symm : T.V →ₗ[LL] T'.V)) x) = c • x
    rw [LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe, h1]

/- English proof (translation)
Establish `hq2 : ∀ σ x, q (latRep T.L σ x) = A.ρ σ (q x)` using `hq.2`. Establish `hq2' : ∀ σ x, q' (latRep T'.L σ x) = A'.ρ σ (q' x)` using `hq'.2`. Establish `hg0 : ∀ σ x, g (A.ρ σ x) = A'.ρ σ (g x)` using `hg`. Set `φ : ↥(prodLat T T').L.T →ₗ[O] (Fin A'.m → k)` to `q' ∘ₗ (LinearMap.snd O _ _ ∘ₗ (prodLatEquiv T T').toLinearMap) - (g.restrictScalars O) ∘ₗ q ∘ₗ (LinearMap.fst O _ _ ∘ₗ (prodLatEquiv T T').toLinearMap)`. Establish `hφ : ∀ z, φ z = q' (prodLatEquiv T T' z).2 - g (q (prodLatEquiv T T' z).1)` using `fun z => rfl`.

Establish `hP : ∀ z, lam • z ∈ LinearMap.ker φ` using `fun z => by`. Rewrite using `[LinearMap.mem_ker, map_smul, lam_smul hk]`. Establish `hst : ∀ σ, ∀ z ∈ LinearMap.ker φ, latRep (prodLat T T').L σ z ∈ LinearMap.ker φ`. Introduce `σ z hz`. Rewrite `hz`, the goal using `[LinearMap.mem_ker, hφ]`.

Simplify using `only [prodLatEquiv_act]`. Rewrite using `[hq2, hq2', hg0, ← map_sub, hz, map_zero]`. Use `⟨{ prodLat T T' with L := subLattice (prodLat T T') hl (LinearMap.ker φ) hst hP }, ⟨LinearMap.fst LL T.V T'.V, fun _ _ => rfl, continuous_fst, ?_⟩, ⟨LinearMap.snd LL T.V T'.V, fun _ _ => rfl, continuous_snd, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, -, rfl⟩`. Conclude with `z.2.1`.

Introduce and unpack `_ ⟨z, -, rfl⟩`. Conclude with `z.2.2`. Introduce `x hx`. Take `⟨x', hx'⟩` from `hq'.1 (g (q ⟨x, hx⟩))`. Set `w : ↥(prodLat T T').L.T` to `⟨(x, (x' : T'.V)), hx, x'.2⟩`.

Use `⟨(x, (x' : T'.V)), ⟨w, ?_, rfl⟩, rfl⟩` and prove the remaining obligations. Use `show φ w = 0`. Rewrite using `[hφ]`. Conclude with `sub_eq_zero.mpr hx'`. Introduce and unpack `⟨_, ⟨w, hw, rfl⟩⟩`.

Establish `hw' : φ w = 0` using `hw`. Rewrite `hw'` using `[hφ, sub_eq_zero]`. Conclude with `hw'`.
-/
theorem exists_fibre [IsDomain O] [IsPrincipalIdealRing O] {lam : O} (hl : algebraMap O LL lam ≠ 0)
    (hk : algebraMap O k lam = 0) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
    (T' : LocLat G Qp LL O) (A' : Ob k G) (q' : ↥T'.L.T →ₗ[O] (Fin A'.m → k))
    (g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)) (hq : Onto T A q) (hq' : Onto T' A' q') (hg : IsHom A A' g) :
    ∃ (T'' : LocLat G Qp LL O) (f : LatHom T''.L T.L) (f' : LatHom T''.L T'.L),
      (∀ x ∈ T.L.T, ∃ z ∈ T''.L.T, f.f z = x) ∧
      ∀ z : ↥T''.L.T, q' (GlobalTheory.EtaleExact.latMap f' z) = g (q (GlobalTheory.EtaleExact.latMap f z)) := by
  have hq2 : ∀ σ x, q (latRep T.L σ x) = A.ρ σ (q x) := hq.2
  have hq2' : ∀ σ x, q' (latRep T'.L σ x) = A'.ρ σ (q' x) := hq'.2
  have hg0 : ∀ σ x, g (A.ρ σ x) = A'.ρ σ (g x) := hg
  let φ : ↥(prodLat T T').L.T →ₗ[O] (Fin A'.m → k) :=
    q' ∘ₗ (LinearMap.snd O _ _ ∘ₗ (prodLatEquiv T T').toLinearMap) -
      (g.restrictScalars O) ∘ₗ q ∘ₗ (LinearMap.fst O _ _ ∘ₗ (prodLatEquiv T T').toLinearMap)
  have hφ : ∀ z, φ z = q' (prodLatEquiv T T' z).2 - g (q (prodLatEquiv T T' z).1) := fun z => rfl
  have hP : ∀ z, lam • z ∈ LinearMap.ker φ := fun z => by
    rw [LinearMap.mem_ker, map_smul, lam_smul hk]
  have hst : ∀ σ, ∀ z ∈ LinearMap.ker φ, latRep (prodLat T T').L σ z ∈ LinearMap.ker φ := by
    intro σ z hz
    rw [LinearMap.mem_ker, hφ] at hz ⊢
    simp only [prodLatEquiv_act]
    rw [hq2, hq2', hg0, ← map_sub, hz, map_zero]
  refine ⟨{ prodLat T T' with L := subLattice (prodLat T T') hl (LinearMap.ker φ) hst hP },
    ⟨LinearMap.fst LL T.V T'.V, fun _ _ => rfl, continuous_fst, ?_⟩,
    ⟨LinearMap.snd LL T.V T'.V, fun _ _ => rfl, continuous_snd, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact z.2.1
  · rintro _ ⟨z, -, rfl⟩
    exact z.2.2
  · intro x hx
    obtain ⟨x', hx'⟩ := hq'.1 (g (q ⟨x, hx⟩))
    let w : ↥(prodLat T T').L.T := ⟨(x, (x' : T'.V)), hx, x'.2⟩
    refine ⟨(x, (x' : T'.V)), ⟨w, ?_, rfl⟩, rfl⟩
    show φ w = 0
    rw [hφ]
    exact sub_eq_zero.mpr hx'
  · rintro ⟨_, ⟨w, hw, rfl⟩⟩
    have hw' : φ w = 0 := hw
    rw [hφ, sub_eq_zero] at hw'
    exact hw'

/- English proof (translation)
Introduce `G _ _ Qp LL O _ _ _ _ _ _ _ _ k _ _ lam hl hk`. Conclude with `⟨fun T A q hq => exists_ker hl hk T A q hq, fun T T' f hf h => exists_inv hl T T' f hf h, fun T A q T' A' q' g hq hq' hg => exists_fibre hl hk T A q T' A' q' g hq hq' hg⟩`.
-/
theorem ker_inv_fibre : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k] (lam : O), algebraMap O LL lam ≠ 0 → algebraMap O k lam = 0 → (∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q → ∃ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), ∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) ∧ (∀ (T T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), Function.Injective f.f → (∀ x ∈ T.L.T, ∃ y ∈ T'.L.T, f.f y = lam • x) → ∃ h : LatHom T.L T'.L, ∀ x, f.f (h.f x) = algebraMap O LL lam • x) ∧ ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (T' : LocLat G Qp LL O) (A' : Ob k G) (q' : ↥T'.L.T →ₗ[O] (Fin A'.m → k)) (g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)), Onto T A q → Onto T' A' q' → IsHom A A' g → ∃ (T'' : LocLat G Qp LL O) (f : LatHom T''.L T.L) (f' : LatHom T''.L T'.L), (∀ x ∈ T.L.T, ∃ z ∈ T''.L.T, f.f z = x) ∧ ∀ z : ↥T''.L.T, q' (GlobalTheory.EtaleExact.latMap f' z) = g (q (GlobalTheory.EtaleExact.latMap f z)) := by
  intro G _ _ Qp LL O _ _ _ _ _ _ _ _ k _ _ lam hl hk
  exact ⟨fun T A q hq => exists_ker hl hk T A q hq, fun T T' f hf h => exists_inv hl T T' f hf h,
    fun T A q T' A' q' g hq hq' hg => exists_fibre hl hk T A q T' A' q' g hq hq' hg⟩

end GlobalTheory.RedFun.SubLat
