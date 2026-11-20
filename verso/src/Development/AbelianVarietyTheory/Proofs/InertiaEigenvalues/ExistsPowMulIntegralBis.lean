import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfPowSmulMem

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.Isog

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

/- English proof (translation)
Consider the cases of `u`. Consider the cases of `w`. Consider the cases of `h`. Both sides reduce to the same expression.
-/
theorem latHom_ext {T T' : LocLat G Qp LL O} {u w : LatHom T.L T'.L} (h : u.f = w.f) : u = w := by
  cases u; cases w; cases h; rfl

/- English proof (translation)
Set `e : T'.V ≃ₗ[LL] T.V` to `LinearEquiv.ofBijective f.f hf`. Establish `he : ∀ g y, e.symm (T.ρ g y) = T'.ρ g (e.symm y)`. Introduce `g y`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[e.apply_symm_apply]`.

Use `f.equiv g (e.symm y)` as an intermediate fact. Express the relevant statement in the definitionally equal form `e _ = T.ρ g (e _) at this`. Rewrite using `[this, e.apply_symm_apply]`. Take `⟨m, hm⟩` from `GlobalTheory.WachSat.exists_pow_smul_le (LL := LL) c hc T'.L.T (T.L.T.map (e.symm.toLinearMap.restrictScalars O)) T'.L.span (T.L.fg.map _)`. Use `haveI : ContinuousSMul LL T'.V := IsModuleTopology.toContinuousSMul LL T'.V`.

Set `g : LatHom T.L T'.L` to `{ f := algebraMap O LL (c ^ m) • e.symm.toLinearMap equiv := fun g y => by simp [he] cont := IsModuleTopology.continuous_of_linearMap _ T_le := fun y hy => by`. Use `hm _ (Submodule.mem_map_of_mem hy)` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul LL]`. Conclude with `this }`. Use `⟨m, g, latHom_ext ?_, latHom_ext ?_⟩` and prove the remaining obligations.

Use extensionality with `y`. Express the relevant statement in the definitionally equal form `algebraMap O LL (c ^ m) • e.symm (e y) = algebraMap O LL (c ^ m) • y`. Rewrite using `[e.symm_apply_apply]`. Use extensionality with `y`. Express the relevant statement in the definitionally equal form `e (algebraMap O LL (c ^ m) • e.symm y) = algebraMap O LL (c ^ m) • y`.

Rewrite using `[map_smul, e.apply_symm_apply]`.
-/
theorem exists_quasi_inverse (c : O)
    (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL c ^ k * a)
    {T' T : LocLat G Qp LL O} (f : LatHom T'.L T.L) (hf : Function.Bijective f.f) :
    ∃ (m : ℕ) (g : LatHom T.L T'.L), latComp g f = latSmul T' (c ^ m) ∧
      latComp f g = latSmul T (c ^ m) := by
  let e : T'.V ≃ₗ[LL] T.V := LinearEquiv.ofBijective f.f hf
  have he : ∀ g y, e.symm (T.ρ g y) = T'.ρ g (e.symm y) := by
    intro g y
    apply e.injective
    rw [e.apply_symm_apply]
    have := f.equiv g (e.symm y)
    change e _ = T.ρ g (e _) at this
    rw [this, e.apply_symm_apply]
  obtain ⟨m, hm⟩ := GlobalTheory.WachSat.exists_pow_smul_le (LL := LL) c hc T'.L.T
    (T.L.T.map (e.symm.toLinearMap.restrictScalars O)) T'.L.span (T.L.fg.map _)
  haveI : ContinuousSMul LL T'.V := IsModuleTopology.toContinuousSMul LL T'.V
  let g : LatHom T.L T'.L :=
    { f := algebraMap O LL (c ^ m) • e.symm.toLinearMap
      equiv := fun g y => by simp [he]
      cont := IsModuleTopology.continuous_of_linearMap _
      T_le := fun y hy => by
        have := hm _ (Submodule.mem_map_of_mem hy)
        rw [← algebraMap_smul LL] at this
        exact this }
  refine ⟨m, g, latHom_ext ?_, latHom_ext ?_⟩
  · ext y
    change algebraMap O LL (c ^ m) • e.symm (e y) = algebraMap O LL (c ^ m) • y
    rw [e.symm_apply_apply]
  · ext y
    change e (algebraMap O LL (c ^ m) • e.symm y) = algebraMap O LL (c ^ m) • y
    rw [map_smul, e.apply_symm_apply]

variable (W : LocWach PD LL O v n)

/- English proof (translation)
Establish `hreg : ∀ (k : ℕ) (y : W.EE), (PD.p : W.EE) ^ k * y = 0 → y = 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro y hy`. Simplify using `using hy`.

Consider the case `succ k ih`. Introduce `y hy`. Conclude with `ih y (GlobalTheory.WachSat.ee_torsionFree W hp _ (by rw [← hy]; ring))`. Use `haveI := (W.DD_free T).1`. Set `b` to `Module.Free.chooseBasis W.EE (W.DD T)`.

Rewrite `hx` using `[← algebraMap_smul W.EE, map_pow, map_natCast]`. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `j`. Use `congrArg (fun z => b.repr z j) hx` as an intermediate fact. Simplify using `only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this`.

Simplify using `using hreg m _ this`.
-/
theorem dd_torsionFree (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0) (T : LocLat G Qp LL O) (m : ℕ)
    (x : W.DD T) (hx : ((PD.p : O) ^ m) • x = 0) : x = 0 := by
  have hreg : ∀ (k : ℕ) (y : W.EE), (PD.p : W.EE) ^ k * y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      exact ih y (GlobalTheory.WachSat.ee_torsionFree W hp _ (by rw [← hy]; ring))
  haveI := (W.DD_free T).1
  let b := Module.Free.chooseBasis W.EE (W.DD T)
  rw [← algebraMap_smul W.EE, map_pow, map_natCast] at hx
  apply b.repr.injective
  ext j
  have := congrArg (fun z => b.repr z j) hx
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
  simpa using hreg m _ this

/- English proof (translation)
Set `b'` to `(W.N_base T hT).basis b`. Establish `hb : (fun j => (b j : W.DD T)) = b'`. Use function extensionality and compare the values at `j`. Conclude with `((W.N_base T hT).basis_apply b j).symm`. Use `⟨b, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hb]`. Conclude with `b'.linearIndependent`. Rewrite using `[hb]`. Conclude with `b'.span_eq`.
-/
theorem globalBasis_of_basis (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (b : Module.Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥(W.N T)) :
    GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.GlobalBasis W T := by
  let b' := (W.N_base T hT).basis b
  have hb : (fun j => (b j : W.DD T)) = b' := by
    funext j
    exact ((W.N_base T hT).basis_apply b j).symm
  refine ⟨b, ?_, ?_⟩
  · rw [hb]; exact b'.linearIndependent
  · rw [hb]; exact b'.span_eq

/- English proof (translation)
Take `⟨m, g, hgf, hfg⟩` from `exists_quasi_inverse (PD.p : O) hc f hf`. Establish `h1 : ∀ x, W.map g (W.map f x) = ((PD.p : O) ^ m) • x` using `fun x => by`. Rewrite using `[← W.map_comp, hgf, W.map_latSmul]`. Establish `h2 : ∀ x, W.map f (W.map g x) = ((PD.p : O) ^ m) • x` using `fun x => by`. Rewrite using `[← W.map_comp, hfg, W.map_latSmul]`.

Use `⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, ⟨m, fun y => ⟨W.map g y, h2 y, W.map_N g hT hT' y⟩⟩, fun x => ⟨fun hx => hs m x ?_, W.map_N f hT' hT x⟩⟩` and prove the remaining obligations. Use `dd_torsionFree W hp T' m x ?_` and prove the remaining obligations. Rewrite using `[← h1, hx, map_zero]`. Rewrite using `[← h1]`. Conclude with `W.map_N g hT hT' _ hx`.
-/
theorem isog_generic (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0)
    (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL (PD.p : O) ^ k * a)
    (T' T : LocLat G Qp LL O) (f : LatHom T'.L T.L) (hT' : IsCrys PD T'.ρ) (hT : IsCrys PD T.ρ)
    (hs : ∀ (m : ℕ) (x : W.DD T'), ((PD.p : O) ^ m) • x ∈ W.N T' → x ∈ W.N T')
    (hf : Function.Bijective f.f) :
    Function.Injective (W.map f) ∧
    (∃ c : ℕ, ∀ y : W.DD T, ∃ x : W.DD T', W.map f x = ((PD.p : O) ^ c) • y ∧
      (y ∈ W.N T → x ∈ W.N T')) ∧
    ∀ x : W.DD T', W.map f x ∈ W.N T ↔ x ∈ W.N T' := by
  obtain ⟨m, g, hgf, hfg⟩ := exists_quasi_inverse (PD.p : O) hc f hf
  have h1 : ∀ x, W.map g (W.map f x) = ((PD.p : O) ^ m) • x := fun x => by
    rw [← W.map_comp, hgf, W.map_latSmul]
  have h2 : ∀ x, W.map f (W.map g x) = ((PD.p : O) ^ m) • x := fun x => by
    rw [← W.map_comp, hfg, W.map_latSmul]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_,
    ⟨m, fun y => ⟨W.map g y, h2 y, W.map_N g hT hT' y⟩⟩,
    fun x => ⟨fun hx => hs m x ?_, W.map_N f hT' hT x⟩⟩
  · refine dd_torsionFree W hp T' m x ?_
    rw [← h1, hx, map_zero]
  · rw [← h1]
    exact W.map_N g hT hT' _ hx

end Generic

section Loc

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)

/- English proof (translation)
Establish `hl0 : (l : ↥LL.1) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Rewrite `ha` using `[P.PD_p]`. Establish `: (l : ↥LL.1) * (a : ↥LL.1) = 0`. Use `congrArg (Subtype.val) ha` as an intermediate fact. Simplify using `using this`.

Conclude with `Subtype.ext ((mul_eq_zero.1 this).resolve_left hl0)`.
-/
theorem p_regular (a : ↥(OL LL)) (ha : (((P.PD K).p : ℕ) : ↥(OL LL)) * a = 0) : a = 0 := by
  have hl0 : (l : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  rw [P.PD_p] at ha
  have : (l : ↥LL.1) * (a : ↥LL.1) = 0 := by
    have := congrArg (Subtype.val) ha
    simpa using this
  exact Subtype.ext ((mul_eq_zero.1 this).resolve_left hl0)

/- English proof (translation)
Rewrite using `[P.PD_p]`. Establish `: ∃ k : ℕ, 0 ≤ P.v LL ((l : ↥LL.1) ^ k * a)`. Consider the cases of `hq : P.v LL a with`. Consider the case `top => exact ⟨0, by simp [hq]⟩`. Consider the case `coe q`.

Take `⟨k, hk⟩` from `exists_nat_ge (-q)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[AddValuation.map_mul, AddValuation.map_pow, P.v_l, hq, nsmul_one, ← WithTop.coe_natCast, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨k, hk⟩` from `this`.

Conclude with `⟨k, ⟨_, (P.v_O LL _).1 hk⟩, by rw [map_natCast]; rfl⟩`.
-/
theorem exists_pow_mul_integral (a : ↥LL.1) : ∃ (k : ℕ) (b : ↥(OL LL)), algebraMap ↥(OL LL) ↥LL.1 b =
    algebraMap ↥(OL LL) ↥LL.1 (((P.PD K).p : ℕ) : ↥(OL LL)) ^ k * a := by
  rw [P.PD_p]
  have : ∃ k : ℕ, 0 ≤ P.v LL ((l : ↥LL.1) ^ k * a) := by
    cases hq : P.v LL a with
    | top => exact ⟨0, by simp [hq]⟩
    | coe q =>
      obtain ⟨k, hk⟩ := exists_nat_ge (-q)
      refine ⟨k, ?_⟩
      rw [AddValuation.map_mul, AddValuation.map_pow, P.v_l, hq, nsmul_one, ← WithTop.coe_natCast,
        ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
      linarith
  obtain ⟨k, hk⟩ := this
  exact ⟨k, ⟨_, (P.v_O LL _).1 hk⟩, by rw [map_natCast]; rfl⟩

end Loc

section Main

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL)

/- English proof (translation)
Take `⟨b⟩` from `N_basis_loc H K s LL h T hT`. Conclude with `GlobalTheory.WachSat.mem_of_pow_smul_mem _ (p_regular P K LL) T (globalBasis_of_basis _ T hT b) m x hx`.
-/
theorem sat_loc (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) (m : ℕ) (x : (H.W K s LL h).DD T)
    (hx : ((((P.PD K).p : ℕ) : ↥(OL LL)) ^ m) • x ∈ (H.W K s LL h).N T) : x ∈ (H.W K s LL h).N T := by
  obtain ⟨b⟩ := N_basis_loc H K s LL h T hT
  exact GlobalTheory.WachSat.mem_of_pow_smul_mem _ (p_regular P K LL) T (globalBasis_of_basis _ T hT b) m x hx

/- English proof (translation)
The claim follows from `isog_generic (H.W K s LL h) (p_regular P K LL) (exists_pow_mul_integral P K LL) T' T f hT' hT (sat_loc H K s LL h T' hT') hf`.
-/
theorem isog_loc (T' T : Lt K LL) (f : LatHom T'.L T.L) (hT' : IsCrys (P.PD K) T'.ρ)
    (hT : IsCrys (P.PD K) T.ρ) (hf : Function.Bijective f.f) :
    Function.Injective ((H.W K s LL h).map f) ∧
    (∃ c : ℕ, ∀ y : (H.W K s LL h).DD T, ∃ x : (H.W K s LL h).DD T',
      (H.W K s LL h).map f x = ((((P.PD K).p : ℕ) : ↥(OL LL)) ^ c) • y ∧
      (y ∈ (H.W K s LL h).N T → x ∈ (H.W K s LL h).N T')) ∧
    ∀ x : (H.W K s LL h).DD T', (H.W K s LL h).map f x ∈ (H.W K s LL h).N T ↔
      x ∈ (H.W K s LL h).N T' :=
  isog_generic (H.W K s LL h) (p_regular P K LL) (exists_pow_mul_integral P K LL) T' T f hT' hT
    (sat_loc H K s LL h T' hT') hf

end Main

end GlobalTheory.NL.Isog
