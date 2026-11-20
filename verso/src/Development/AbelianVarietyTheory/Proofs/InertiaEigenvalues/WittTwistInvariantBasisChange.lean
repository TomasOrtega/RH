import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByCyclotomicKernelEtalePhiSolutionMemWachStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.EtMem

section Lin

variable {E S D M : Type} [CommRing E] [CommRing S] [AddCommGroup D] [Module E D] [AddCommGroup M] [Module S M]

/- English proof (translation)
Establish `h : ⊤ ≤ Submodule.span S (Set.range fun i => j (b i))`. Rewrite using `[← hsp, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[← b.sum_repr x, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hj]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `⟨basisOfTopLeSpanOfCardEqFinrank _ h (by simp [hr]), fun i => by simp⟩` and prove the remaining obligations.
-/
theorem exists_basis [Nontrivial S] [Module.Free S M] [Module.Finite S M] {r : ℕ} (io : E → S) (j : D →+ M)
    (hj : ∀ e x, j (e • x) = io e • j x) (hsp : Submodule.span S (Set.range j) = ⊤)
    (b : Module.Basis (Fin r) E D) (hr : Module.finrank S M = r) :
    ∃ e : Module.Basis (Fin r) S M, ∀ i, e i = j (b i) := by
  have h : ⊤ ≤ Submodule.span S (Set.range fun i => j (b i)) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hj]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨basisOfTopLeSpanOfCardEqFinrank _ h (by simp [hr]), fun i => by simp⟩

/- English proof (translation)
Use `conv_lhs => rw [← e.sum_repr m, map_sum, map_sum]`. Simplify using `[hΦ, Finsupp.finset_sum_apply, mul_comm]`.
-/
theorem repr_semi {r : ℕ} (e : Module.Basis (Fin r) S M) (φ : S → S) (Φ : M →+ M)
    (hΦ : ∀ c m, Φ (c • m) = φ c • Φ m) (m : M) (i : Fin r) :
    e.repr (Φ m) i = ∑ k, e.repr (Φ (e k)) i * φ (e.repr m k) := by
  conv_lhs => rw [← e.sum_repr m, map_sum, map_sum]
  simp [hΦ, Finsupp.finset_sum_apply, mul_comm]

/- English proof (translation)
Establish `h : ∀ m : M, ∃ w : Fin r → S, ∀ i, e.repr m i = ∑ k, e.repr (Φ (e k)) i * w k`. Introduce `m`. Establish `hm : m ∈ Submodule.span S {m | Φ m = m}` using `hsp ▸ Submodule.mem_top`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem x hx`.

Use `⟨fun k => φ (e.repr x k), fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← repr_semi e φ Φ hΦ, show Φ x = x from hx]`. Consider the case `zero => exact ⟨0, fun i => by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨u, hu⟩` from `hx`.

Take `⟨w, hw⟩` from `hy`. Conclude with `⟨u + w, fun i => by simp [hu, hw, mul_add, Finset.sum_add_distrib]⟩`. Consider the case `smul c x _ hx`. Take `⟨u, hu⟩` from `hx`. Conclude with `⟨c • u, fun i => by simp [hu, Finset.mul_sum, mul_left_comm]⟩`.

Use `choose w hw using h`. Use `Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun k j => w (e j) k) ?_` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Rewrite using `[← hw, e.repr_self, Matrix.one_apply, Finsupp.single_apply]`.

Simplify using `[eq_comm]`.
-/
theorem isUnit_det {r : ℕ} (e : Module.Basis (Fin r) S M) (φ : S → S) (Φ : M →+ M)
    (hΦ : ∀ c m, Φ (c • m) = φ c • Φ m) (hsp : Submodule.span S {m | Φ m = m} = ⊤) :
    IsUnit (Matrix.of fun i k => e.repr (Φ (e k)) i).det := by
  have h : ∀ m : M, ∃ w : Fin r → S, ∀ i, e.repr m i = ∑ k, e.repr (Φ (e k)) i * w k := by
    intro m
    have hm : m ∈ Submodule.span S {m | Φ m = m} := hsp ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
      refine ⟨fun k => φ (e.repr x k), fun i => ?_⟩
      rw [← repr_semi e φ Φ hΦ, show Φ x = x from hx]
    | zero => exact ⟨0, fun i => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨w, hw⟩ := hy
      exact ⟨u + w, fun i => by simp [hu, hw, mul_add, Finset.sum_add_distrib]⟩
    | smul c x _ hx =>
      obtain ⟨u, hu⟩ := hx
      exact ⟨c • u, fun i => by simp [hu, Finset.mul_sum, mul_left_comm]⟩
  choose w hw using h
  refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun k j => w (e j) k) ?_
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [← hw, e.repr_self, Matrix.one_apply, Finsupp.single_apply]
  simp [eq_comm]

end Lin

section Ten

variable {O S N : Type} [CommRing O] [CommRing S] [Algebra O S] [AddCommGroup N] [Module O N]

/- English proof (translation)
Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a t => simp [TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => simp only [smul_add, map_add, hx, hy]`.
-/
theorem map_smul_semi (f : S →ₐ[O] S) (g : N →ₗ[O] N) (c : S) (m : S ⊗[O] N) :
    TensorProduct.map f.toLinearMap g (c • m) = f c • TensorProduct.map f.toLinearMap g m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a t => simp [TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => simp only [smul_add, map_add, hx, hy]`.
-/
theorem map_mulLeft (c : S) (m : S ⊗[O] N) :
    TensorProduct.map (LinearMap.mulLeft O c) (LinearMap.id : N →ₗ[O] N) m = c • m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `m -`. Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a t`.

Establish `: a ⊗ₜ[O] t = a • ((1 : S) ⊗ₜ[O] t)` using `by simp [TensorProduct.smul_tmul']`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (by simp))`. Consider the case `add x y hx hy => exact Submodule.add_mem _ hx hy`.
-/
theorem span_fixed (f : S →ₐ[O] S) :
    Submodule.span S {m : S ⊗[O] N | TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) m = m} = ⊤ := by
  rw [eq_top_iff]
  rintro m -
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    have : a ⊗ₜ[O] t = a • ((1 : S) ⊗ₜ[O] t) := by simp [TensorProduct.smul_tmul']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end Ten

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {I : WIo R RA RW inclR φR gR πA}

/- English proof (translation)
Apply `Γ.χΓ_inj` to reduce the goal to its premises. Rewrite using `[map_one Γ.χΓ]`. Apply `Units.ext` to reduce the goal to its premises. Apply `hO` to reduce the goal to its premises. Rewrite using `[Γ.χΓ_res g, hg, Units.val_one, map_one, map_one]`.
-/
theorem res_eq_one (hO : Function.Injective (algebraMap O LL)) (g : G) (hg : (PD.χ g : Qp) = 1) :
    Γ.resΓ g = 1 := by
  apply Γ.χΓ_inj
  rw [map_one Γ.χΓ]
  apply Units.ext
  apply hO
  rw [Γ.χΓ_res g, hg, Units.val_one, map_one, map_one]

/- English proof (translation)
Introduce `i₀`. Break down `subsingleton_or_nontrivial RW with hS | hS` into its components or cases. Use `haveI : Subsingleton (TW RW T) := Module.subsingleton RW _`. Conclude with `⟨0, Subsingleton.elim _ _⟩`. Use `haveI : Nontrivial O := (algebraMap O RW).domain_nontrivial`.

Use `haveI : Nontrivial R.EE := I.ioE.toRingHom.domain_nontrivial`. Use `haveI : Module.Free O ↥T.L.T := T.L.free`. Use `haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg`. Use `haveI : Module.Free R.EE (E.DD T) := (E.DD_free T).1`. Establish `hrk : Module.finrank RW (TW RW T) = Module.finrank O ↥T.L.T` using `Module.finrank_baseChange`.

Break down `Nat.eq_zero_or_pos (Module.finrank O ↥T.L.T) with h0 | h0` into its components or cases. Use `haveI : Subsingleton (TW RW T) := (Module.finrank_eq_zero_iff_of_free RW _).1 (hrk.trans h0)`. Conclude with `⟨0, Subsingleton.elim _ _⟩`. Use `haveI : Module.Finite R.EE (E.DD T) := Module.finite_of_finrank_pos ((E.DD_free T).2 ▸ h0)`. Set `b` to `Module.finBasisOfFinrankEq R.EE (E.DD T) (E.DD_free T).2`.

Take `⟨e, he⟩` from `exists_basis I.ioE (E.jD T).toAddMonoidHom (E.jD_smul T) (E.jD_span T) b hrk`. Establish `he' : ∀ i, e i = E.jD T (b i)` using `he`. Establish `hrep : ∀ (d : E.DD T) i, e.repr (E.jD T d) i = I.ioE (b.repr d i)`. Introduce `d i`. Use `conv_lhs => rw [← b.sum_repr d, map_sum]`.

Simplify using `only [E.jD_smul, ← he']`. Rewrite using `[e.repr_sum_self]`. Establish `hsφ : ∀ (c : RW) (m : TW RW T), (TWmap φR T).toAddMonoidHom (c • m) = φR c • (TWmap φR T).toAddMonoidHom m` using `fun c m => map_smul_semi φR _ c m`. Set `F : Matrix (Fin (Module.finrank O ↥T.L.T)) (Fin (Module.finrank O ↥T.L.T)) R.EE` to `Matrix.of fun i k => b.repr (E.φD T (b k)) i`. Establish `hF : F.map I.ioE = Matrix.of fun i k => e.repr ((TWmap φR T).toAddMonoidHom (e k)) i`.

Use extensionality with `i k`. Simplify using `only [F, Matrix.map_apply, Matrix.of_apply, LinearMap.toAddMonoidHom_coe]`. Rewrite using `[he', ← E.jD_φ, hrep]`. Establish `hFu : IsUnit F`. Rewrite using `[Matrix.isUnit_iff_isUnit_det]`.

Apply `hu` to reduce the goal to its premises. Establish `h1` using `isUnit_det e φR (TWmap φR T).toAddMonoidHom hsφ (span_fixed φR)`. Rewrite `h1` using `[← hF]`. Rewrite using `[AlgHom.map_det]`. Conclude with `h1`.

Establish `hU` using `hrat _ F (Matrix.of fun k j => e.repr (x j) k) hFu ?_ ?_`. Use `choose u hu' using hU`. Use `⟨∑ k, u k i₀ • b k, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Simplify using `only [E.jD_smul, ← he', hu', Matrix.of_apply]`.

Conclude with `e.sum_repr _`. Introduce `i j g hg`. Establish `hs : ∀ (c : RW) (m : TW RW T), (TWact (gR g) T g).toAddMonoidHom (c • m) = gR g c • (TWact (gR g) T g).toAddMonoidHom m` using `fun c m => map_smul_semi (gR g) _ c m`. Establish `h1` using `repr_semi e (gR g) (TWact (gR g) T g).toAddMonoidHom hs (x j) i`. Establish `h2 : ∀ k, TWact (gR g) T g (e k) = e k` using `fun k => by`.

Rewrite using `[he', ← E.jD_act, hH g hg, E.γD_one]`. Simplify using `only [LinearMap.toAddMonoidHom_coe, hx g hg, h2, e.repr_self, Finsupp.single_apply] at h1`. Simplify using `only [Matrix.of_apply]`. Rewrite `h1` using `[Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]`. Simplify using `using h1.symm`.

Rewrite using `[hF]`. Use extensionality with `i j`. Establish `h1` using `repr_semi e φR (TWmap φR T).toAddMonoidHom hsφ (x j) i`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]`. Rewrite using `[← h1, LinearMap.toAddMonoidHom_coe, hφ]`.

Simplify using `only [map_mulLeft, map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.
-/
theorem mem_range (E : WEt I) (T : LocLat G Qp LL O) (H : G → Prop) (hH : ∀ g, H g → Γ.resΓ g = 1)
    (hu : ∀ x : R.EE, IsUnit (I.ioE x) → IsUnit x) (q : ℕ) (x : Fin q → TW RW T)
    (A : Matrix (Fin q) (Fin q) R.EE)
    (hrat : ∀ (p : ℕ) (F : Matrix (Fin p) (Fin p) R.EE) (U : Matrix (Fin p) (Fin q) RW), IsUnit F →
      (∀ i j g, H g → gR g (U i j) = U i j) → F.map I.ioE * U.map φR = U * A.map I.ioE →
      ∀ i j, U i j ∈ Set.range I.ioE)
    (hx : ∀ g, H g → ∀ i, TWact (gR g) T g (x i) = x i)
    (hφ : ∀ j, TWmap φR T (x j) = ∑ i, TensorProduct.map (LinearMap.mulLeft O (I.ioE (A i j) : RW))
      (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T) (x i)) :
    ∀ i, x i ∈ Set.range (E.jD T) := by
  intro i₀
  rcases subsingleton_or_nontrivial RW with hS | hS
  · haveI : Subsingleton (TW RW T) := Module.subsingleton RW _
    exact ⟨0, Subsingleton.elim _ _⟩
  haveI : Nontrivial O := (algebraMap O RW).domain_nontrivial
  haveI : Nontrivial R.EE := I.ioE.toRingHom.domain_nontrivial
  haveI : Module.Free O ↥T.L.T := T.L.free
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  haveI : Module.Free R.EE (E.DD T) := (E.DD_free T).1
  have hrk : Module.finrank RW (TW RW T) = Module.finrank O ↥T.L.T := Module.finrank_baseChange
  rcases Nat.eq_zero_or_pos (Module.finrank O ↥T.L.T) with h0 | h0
  · haveI : Subsingleton (TW RW T) := (Module.finrank_eq_zero_iff_of_free RW _).1 (hrk.trans h0)
    exact ⟨0, Subsingleton.elim _ _⟩
  haveI : Module.Finite R.EE (E.DD T) := Module.finite_of_finrank_pos ((E.DD_free T).2 ▸ h0)
  let b := Module.finBasisOfFinrankEq R.EE (E.DD T) (E.DD_free T).2
  obtain ⟨e, he⟩ := exists_basis I.ioE (E.jD T).toAddMonoidHom (E.jD_smul T) (E.jD_span T) b hrk
  have he' : ∀ i, e i = E.jD T (b i) := he
  have hrep : ∀ (d : E.DD T) i, e.repr (E.jD T d) i = I.ioE (b.repr d i) := by
    intro d i
    conv_lhs => rw [← b.sum_repr d, map_sum]
    simp only [E.jD_smul, ← he']
    rw [e.repr_sum_self]
  have hsφ : ∀ (c : RW) (m : TW RW T), (TWmap φR T).toAddMonoidHom (c • m) =
      φR c • (TWmap φR T).toAddMonoidHom m := fun c m => map_smul_semi φR _ c m
  let F : Matrix (Fin (Module.finrank O ↥T.L.T)) (Fin (Module.finrank O ↥T.L.T)) R.EE :=
    Matrix.of fun i k => b.repr (E.φD T (b k)) i
  have hF : F.map I.ioE = Matrix.of fun i k => e.repr ((TWmap φR T).toAddMonoidHom (e k)) i := by
    ext i k
    simp only [F, Matrix.map_apply, Matrix.of_apply, LinearMap.toAddMonoidHom_coe]
    rw [he', ← E.jD_φ, hrep]
  have hFu : IsUnit F := by
    rw [Matrix.isUnit_iff_isUnit_det]
    apply hu
    have h1 := isUnit_det e φR (TWmap φR T).toAddMonoidHom hsφ (span_fixed φR)
    rw [← hF] at h1
    rw [AlgHom.map_det]
    exact h1
  have hU := hrat _ F (Matrix.of fun k j => e.repr (x j) k) hFu ?_ ?_
  · choose u hu' using hU
    refine ⟨∑ k, u k i₀ • b k, ?_⟩
    rw [map_sum]
    simp only [E.jD_smul, ← he', hu', Matrix.of_apply]
    exact e.sum_repr _
  · intro i j g hg
    have hs : ∀ (c : RW) (m : TW RW T), (TWact (gR g) T g).toAddMonoidHom (c • m) =
      gR g c • (TWact (gR g) T g).toAddMonoidHom m := fun c m => map_smul_semi (gR g) _ c m
    have h1 := repr_semi e (gR g) (TWact (gR g) T g).toAddMonoidHom hs (x j) i
    have h2 : ∀ k, TWact (gR g) T g (e k) = e k := fun k => by
      rw [he', ← E.jD_act, hH g hg, E.γD_one]
    simp only [LinearMap.toAddMonoidHom_coe, hx g hg, h2, e.repr_self, Finsupp.single_apply] at h1
    simp only [Matrix.of_apply]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)] at h1
    simpa using h1.symm
  · rw [hF]
    ext i j
    have h1 := repr_semi e φR (TWmap φR T).toAddMonoidHom hsφ (x j) i
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    rw [← h1, LinearMap.toAddMonoidHom_coe, hφ]
    simp only [map_mulLeft, map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end Generic

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `l _ P AI K s LL hG Γ R I hI E T q x A hA hx hφ`. Establish `h1 : ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → Γ.resΓ g = 1` using `fun g hg => res_eq_one Subtype.val_injective g ((P.PD_χ K g).trans (congrArg Units.val hg))`. Establish `h2 : ∀ (p : ℕ) (F : Matrix (Fin p) (Fin p) R.EE) (U : Matrix (Fin p) (Fin q) (RW LL)), IsUnit F → (∀ i j (g : ↥(GK K)), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) (U i j) = U i j) → F.map I.ioE * U.map (φRW LL) = U * A.map I.ioE → ∀ i j, U i j ∈ Set.range I.ioE` using `fun p F U hF hU hE => GlobalTheory.T.fixedByCyclotomicKernel_etalePhi_solution_mem_wach l P AI K s LL hG Γ R I hI p q F A 0 U hF hA (fun i j g hg h1 => hU i j ⟨g, hg⟩ h1) (hE.trans ((add_zero _).symm.trans (congrArg _ (Matrix.map_zero _ (map_zero I.ioE)).symm)))`. Conclude with `mem_range E T (fun g => P.χQ (g : GQ l) = 1) h1 (GlobalTheory.T.wachInclusion_injective_saturated_inter l P AI K s LL hG Γ R I hI).2.1 q x A h2 hx hφ`.
-/
theorem fixed_mem_range : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (q : ℕ) (x : Fin q → TW (RW LL) T) (A : Matrix (Fin q) (Fin q) R.EE), IsUnit A → (∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → ∀ i, TWact (AI.gRW LL (g : GQ l)) T g (x i) = x i) → (∀ j, TWmap (φRW LL) T (x j) = ∑ i, TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (I.ioE (A i j) : RW LL)) (LinearMap.id : ↥T.L.T →ₗ[↥(OL LL)] ↥T.L.T) (x i)) → ∀ i, x i ∈ Set.range (E.jD T) := by
  intro l _ P AI K s LL hG Γ R I hI E T q x A hA hx hφ
  have h1 : ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → Γ.resΓ g = 1 := fun g hg =>
    res_eq_one Subtype.val_injective g ((P.PD_χ K g).trans (congrArg Units.val hg))
  have h2 : ∀ (p : ℕ) (F : Matrix (Fin p) (Fin p) R.EE) (U : Matrix (Fin p) (Fin q) (RW LL)), IsUnit F →
      (∀ i j (g : ↥(GK K)), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) (U i j) = U i j) →
      F.map I.ioE * U.map (φRW LL) = U * A.map I.ioE → ∀ i j, U i j ∈ Set.range I.ioE :=
    fun p F U hF hU hE => GlobalTheory.T.fixedByCyclotomicKernel_etalePhi_solution_mem_wach l P AI K s LL hG Γ R I hI p q F A 0 U hF hA
      (fun i j g hg h1 => hU i j ⟨g, hg⟩ h1)
      (hE.trans ((add_zero _).symm.trans (congrArg _ (Matrix.map_zero _ (map_zero I.ioE)).symm)))
  exact mem_range E T (fun g => P.χQ (g : GQ l) = 1) h1 (GlobalTheory.T.wachInclusion_injective_saturated_inter l P AI K s LL hG Γ R I hI).2.1 q x A
    h2 hx hφ

end GlobalTheory.HWL.EtMem
