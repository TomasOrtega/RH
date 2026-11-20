import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.VolStabFromSWW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

noncomputable section

namespace PI.VolStabW

namespace PositiveNearLattice

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp [crd]`. Consider the case `tmul r e`. Simplify using `[crd, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]`. Consider the case `add x y hx hy`.

Simplify using `only [crd] at hx hy ⊢`. Rewrite using `[map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]`.
-/
theorem crd_map {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
    (f : R →ₐ[F] S) (y : R ⊗[F] E) (k : Fin d) :
    crd b S (Algebra.TensorProduct.map f (AlgHom.id F E) y) k = f (crd b R y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp [crd]
  | tmul r e =>
    simp [crd, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
    simp only [crd] at hx hy ⊢
    rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]

/- English proof (translation)
Simplify using `[crd, inclR, Algebra.TensorProduct.basis_repr_tmul]`.
-/
theorem crd_incl (R : Type) [CommRing R] [Algebra F R] (x : E) (k : Fin d) :
    crd b R (inclR R x) k = algebraMap F R (b.repr x k) := by
  simp [crd, inclR, Algebra.TensorProduct.basis_repr_tmul]

/- English proof (translation)
Use `(Algebra.TensorProduct.basis R b).sum_repr y` as an intermediate fact. Simplify using `only [Algebra.TensorProduct.basis_apply] at this`. Conclude with `this.symm`.
-/
theorem eq_sum_crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) :
    y = ∑ i, crd b R y i • ((1 : R) ⊗ₜ[F] b i) := by
  have := (Algebra.TensorProduct.basis R b).sum_repr y
  simp only [Algebra.TensorProduct.basis_apply] at this
  exact this.symm

variable [FiniteDimensional F E]

/- English proof (translation)
The claim follows from `IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis R b).coord k)`.
-/
theorem continuous_crd (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (k : Fin d) : Continuous (fun y : R ⊗[F] E => crd b R y k) :=
  IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis R b).coord k)

include b in
/- English proof (translation)
Establish `e : (⇑(Algebra.TensorProduct.map f (AlgHom.id F E))) = fun y => ∑ k, f (crd b R y k) • ((1 : S) ⊗ₜ[F] b k)`. Use function extensionality and compare the values at `y`. Rewrite using `[eq_sum_crd b S (Algebra.TensorProduct.map f (AlgHom.id F E) y)]`. Simplify using `only [crd_map]`. Rewrite using `[e]`.

Use `continuous_finsetSum _ fun k _ => ?_` and prove the remaining obligations. Conclude with `continuous_smul.comp ((hf.comp (continuous_crd b R k)).prodMk continuous_const)`.
-/
theorem continuous_map_tens {R S : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing S] [Algebra F S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →ₐ[F] S) (hf : Continuous f) :
    Continuous (Algebra.TensorProduct.map f (AlgHom.id F E)) := by
  have e : (⇑(Algebra.TensorProduct.map f (AlgHom.id F E))) =
      fun y => ∑ k, f (crd b R y k) • ((1 : S) ⊗ₜ[F] b k) := by
    funext y
    rw [eq_sum_crd b S (Algebra.TensorProduct.map f (AlgHom.id F E) y)]
    simp only [crd_map]
  rw [e]
  refine continuous_finsetSum _ fun k _ => ?_
  exact continuous_smul.comp ((hf.comp (continuous_crd b R k)).prodMk continuous_const)

end Coord

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
The claim follows from `(ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).isClosed`.
-/
theorem isClosed_int : IsClosed (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).isClosed

/- English proof (translation)
Establish `hc : ∀ (x : Fin a) (i : Fin M) (k : Fin d), Continuous (fun Y : Fin a → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k)` using `fun x i k => (continuous_crd b (Fv F v) k).comp ((continuous_apply i).comp (continuous_apply x))`. Establish `e : latV (M` using `M) (n := a) b v = ⋂ x, ⋂ i, ⋂ k, (fun Y : Fin a → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by`. Use extensionality with `Y`. Simplify using `[latV, crd]`. Rewrite using `[e]`.

Use `⟨isClosed_iInter fun x => isClosed_iInter fun i => isClosed_iInter fun k => (isClosed_int v).preimage (hc x i k), isOpen_iInter_of_finite fun x => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenC …` and prove the remaining obligations.
-/
theorem isClopen_latV (a M : ℕ) : IsClopen (latV (M := M) (n := a) b v) := by
  have hc : ∀ (x : Fin a) (i : Fin M) (k : Fin d),
      Continuous (fun Y : Fin a → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) :=
    fun x i k => (continuous_crd b (Fv F v) k).comp ((continuous_apply i).comp (continuous_apply x))
  have e : latV (M := M) (n := a) b v = ⋂ x, ⋂ i, ⋂ k,
      (fun Y : Fin a → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) ⁻¹'
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext Y
    simp [latV, crd]
  rw [e]
  refine ⟨isClosed_iInter fun x => isClosed_iInter fun i => isClosed_iInter fun k =>
    (isClosed_int v).preimage (hc x i k), isOpen_iInter_of_finite fun x =>
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
    (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).preimage (hc x i k)⟩

/- English proof (translation)
Set `L : (Fin a → Fin M → Fin d → Fv F v) → (Fin a → Fin M → Fv F v ⊗[F] E)` to `fun c x i => ∑ k, c x i k • ((1 : Fv F v) ⊗ₜ[F] b k)`. Establish `hL : Continuous L`. Use `continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_` and prove the remaining obligations. Conclude with `continuous_smul.comp (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk continuous_const)`. Set `K : Set (Fin a → Fin M → Fin d → Fv F v)` to `Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F))`.

Establish `hK : IsCompact K` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v`. Use `(hK.image hL).of_isClosed_subset (isClopen_latV b v a M).isClosed ?_` and prove the remaining obligations. Introduce `Y hY`. Use `⟨fun x i k => crd b (Fv F v) (Y x i) k, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [K, Set.mem_pi, Set.mem_univ, true_implies]`.

Introduce `x i k`. Conclude with `hY x i k`. Use function extensionality and compare the values at `x i`. Conclude with `(eq_sum_crd b (Fv F v) (Y x i)).symm`.
-/
theorem isCompact_latV (a M : ℕ) : IsCompact (latV (M := M) (n := a) b v) := by
  let L : (Fin a → Fin M → Fin d → Fv F v) → (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Fv F v) ⊗ₜ[F] b k)
  have hL : Continuous L := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  let K : Set (Fin a → Fin M → Fin d → Fv F v) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v
  refine (hK.image hL).of_isClosed_subset (isClopen_latV b v a M).isClosed ?_
  intro Y hY
  refine ⟨fun x i k => crd b (Fv F v) (Y x i) k, ?_, ?_⟩
  · simp only [K, Set.mem_pi, Set.mem_univ, true_implies]
    intro x i k
    exact hY x i k
  · funext x i
    exact (eq_sum_crd b (Fv F v) (Y x i)).symm

/- English proof (translation)
Use `⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) (isClopen_latV b v a M)).isLocallyConstant, ?_⟩` and prove the remaining obligations. Conclude with `HasCompactSupport.intro' (isCompact_latV b v a M) (isClopen_latV b v a M).isClosed fun Y hY => Set.indicator_of_notMem hY _`.
-/
theorem isSB_latV (a M : ℕ) :
    IsSB ((latV (M := M) (n := a) b v).indicator (fun _ => (1 : ℂ))) := by
  refine ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ))
    (isClopen_latV b v a M)).isLocallyConstant, ?_⟩
  exact HasCompactSupport.intro' (isCompact_latV b v a M) (isClopen_latV b v a M).isClosed
    fun Y hY => Set.indicator_of_notMem hY _

end Loc

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Set `b0` to `Module.finBasis F E`. Set `s : Finset F` to `Finset.univ.image (fun p : Fin a × Fin M × Fin (Module.finrank F E) => b0.repr (X0 p.1 p.2.1) p.2.2)`. Take `⟨⟨β, hβ⟩, hint⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) s`. Establish `hβ0 : (β : F) ≠ 0`. Introduce `h`.

Conclude with `nonZeroDivisors.ne_zero hβ (RingOfIntegers.coe_eq_zero_iff.1 h)`. Set `u : Fin (Module.finrank F E) → Fˣ` to `fun _ => (Units.mk0 (β : F) hβ0)⁻¹`. Use `⟨_, b0.unitsSMul u, fun x i k => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.repr_unitsSMul]`. Take `⟨m, hm⟩` from `hint _ (Finset.mem_image.2 ⟨(x, i, k), Finset.mem_univ _, rfl⟩)`.

Use `⟨m, ?_⟩` and prove the remaining obligations. Simplify using `only [u, inv_inv, Units.smul_def, Units.val_mk0, smul_eq_mul]`. Rewrite `hm` using `[Algebra.smul_def]`. Conclude with `hm`.
-/
theorem exists_int_basis [FiniteDimensional F E] {a M : ℕ} (X0 : Fin a → Fin M → E) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ x i k, ∃ m : 𝓞 F, (m : F) = b.repr (X0 x i) k := by
  classical
  let b0 := Module.finBasis F E
  let s : Finset F := Finset.univ.image
    (fun p : Fin a × Fin M × Fin (Module.finrank F E) => b0.repr (X0 p.1 p.2.1) p.2.2)
  obtain ⟨⟨β, hβ⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) s
  have hβ0 : (β : F) ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hβ (RingOfIntegers.coe_eq_zero_iff.1 h)
  let u : Fin (Module.finrank F E) → Fˣ := fun _ => (Units.mk0 (β : F) hβ0)⁻¹
  refine ⟨_, b0.unitsSMul u, fun x i k => ?_⟩
  rw [Module.Basis.repr_unitsSMul]
  obtain ⟨m, hm⟩ := hint _ (Finset.mem_image.2 ⟨(x, i, k), Finset.mem_univ _, rfl⟩)
  refine ⟨m, ?_⟩
  simp only [u, inv_inv, Units.smul_def, Units.val_mk0, smul_eq_mul]
  rw [Algebra.smul_def] at hm
  exact hm

variable [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

/- English proof (translation)
Establish `hm : Continuous (fun g : HA (AF F) σ J => ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)))` using `Units.continuous_val.comp continuous_subtype_val`. Use `continuous_pi fun x => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun g : HA (AF F) σ J => ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec (X x)`. Conclude with `hm.matrix_mulVec continuous_const`.
-/
theorem continuous_orbit (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin a → Fin M → AF F ⊗[F] E) : Continuous (fun g : HA (AF F) σ J => g • X) := by
  have hm : Continuous (fun g : HA (AF F) σ J =>
      ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  refine continuous_pi fun x => ?_
  change Continuous fun g : HA (AF F) σ J =>
    ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec (X x)
  exact hm.matrix_mulVec continuous_const

include b in
/- English proof (translation)
The claim follows from `continuous_pi fun x => continuous_pi fun i => (continuous_map_tens b (fstA F) (by exact continuous_fst)).comp ((continuous_apply i).comp (continuous_apply x))`.
-/
theorem continuous_projInf {M a : ℕ} :
    Continuous (projInf (F := F) (E := E) (M := M) (n := a)) :=
  continuous_pi fun x => continuous_pi fun i =>
    (continuous_map_tens b (fstA F) (by exact continuous_fst)).comp
      ((continuous_apply i).comp (continuous_apply x))

include b in
/- English proof (translation)
The claim follows from `continuous_pi fun x => continuous_pi fun i => (continuous_map_tens b (sndA F) (by exact continuous_snd)).comp ((continuous_apply i).comp (continuous_apply x))`.
-/
theorem continuous_projFin {M a : ℕ} :
    Continuous (projFin (F := F) (E := E) (M := M) (n := a)) :=
  continuous_pi fun x => continuous_pi fun i =>
    (continuous_map_tens b (sndA F) (by exact continuous_snd)).comp
      ((continuous_apply i).comp (continuous_apply x))

end Main

end PositiveNearLattice

open PositiveNearLattice
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def TestNear : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∃ φ : (Fin a → Fin M → AF F ⊗[F] E) → ℝ, (∀ X, 0 ≤ φ X) ∧ IsAdm F E (fun X => (φ X : ℂ)) ∧
    ∃ U : Set (HA (AF F) σ J), IsOpen U ∧ U.Nonempty ∧
      ∀ g ∈ U, 0 < φ (g • ratTup (AF F) X0)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hE M J _hJ _ha _hc a _ha1 _ha2 X0 _hT _hdet`. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)`. Take `⟨d, b, hb⟩` from `exists_int_basis (F := F) X0`. Take `⟨fi, hfc, hf0, hfx⟩` from `exists_continuous_nonneg_pos (projInf (ratTup (AF F) X0))`. Set `ind : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℝ` to `fun v => (latV b v).indicator (fun _ => (1 : ℝ))`.

Set `φ : (Fin a → Fin M → AF F ⊗[F] E) → ℝ` to `fun X => fi (projInf X) * ∏ᶠ v, ind v (projV v (projFin X))`. Establish `hφ0 : ∀ X, 0 ≤ φ X` using `fun X => mul_nonneg (hf0 _) (finprod_nonneg fun v => Set.indicator_nonneg (fun _ _ => zero_le_one) _)`. Establish `hcast : ∀ v (Y : Fin a → Fin M → Fv F v ⊗[F] E), ((ind v Y : ℝ) : ℂ) = (latV b v).indicator (fun _ => (1 : ℂ)) Y`. Introduce `v Y`. Apply the tactic sequence `by_cases h : Y ∈ latV b v <;> simp [ind, h]`.

Establish `hadm : IsAdm F E (fun X => (φ X : ℂ))`. Use `⟨d, b, fun Y => (fi Y : ℂ), fun Y => ∏ᶠ v, (latV b v).indicator (fun _ => (1 : ℂ)) (projV v Y), fun v => (latV b v).indicator (fun _ => (1 : ℂ)), Complex.continuous_ofReal.comp fi.continuous, hfc.comp_left Complex.ofReal_zero, ⟨fun v => isSB_latV b v a M, Filter.Eventually.of_for …` and prove the remaining obligations. Simplify using `only [φ, Complex.ofReal_mul, ← hcast]`. Use `congr 1`. Conclude with `Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _`.

Set `U : Set (HA (AF F) σ J)` to `{g | 0 < fi (projInf (g • ratTup (AF F) X0))} ∩ ⋂ x, ⋂ i, ⋂ k, (fun g : HA (AF F) σ J => crd b (Af F) (projFin (g • ratTup (AF F) X0) x i) k) ⁻¹' ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F`. Establish `horb` using `continuous_orbit σ J (ratTup (AF F) X0)`. Use `⟨φ, hφ0, hadm, U, ?_, ⟨1, ?_⟩, ?_⟩` and prove the remaining obligations. Use `(isOpen_lt continuous_const (fi.continuous.comp ((continuous_projInf b).comp horb))).inter ?_` and prove the remaining obligations. Use `isOpen_iInter_of_finite fun x => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_Oint.preimage ?_` and prove the remaining obligations.

Establish `hpf : Continuous fun g : HA (AF F) σ J => projFin (g • ratTup (AF F) X0)` using `(continuous_projFin b).comp horb`. Conclude with `(continuous_crd b (Af F) k).comp ((continuous_apply i).comp ((continuous_apply x).comp hpf))`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show 0 < fi (projInf ((1 : HA (AF F) σ J) • ratTup (AF F) X0))`. Rewrite using `[one_smul]`.

Conclude with `lt_of_le_of_ne (hf0 _) (Ne.symm hfx)`. Simplify using `only [Set.mem_iInter, Set.mem_preimage, one_smul]`. Introduce `x i k`. Take `⟨m, hm⟩` from `hb x i k`. Establish `e : crd b (Af F) (projFin (ratTup (AF F) X0) x i) k = algebraMap F (Af F) (m : F)`.

Simplify using `only [projFin, ratTup, crd_map, crd_incl, AlgHom.commutes, hm]`. Rewrite using `[e]`. Conclude with `ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.algebraMap_int_mem_Oint m`. Introduce and unpack `g ⟨h1, h2⟩`. Simplify using `only [Set.mem_iInter, Set.mem_preimage] at h2`.

Establish `hone : ∀ v, ind v (projV v (projFin (g • ratTup (AF F) X0))) = 1`. Introduce `v`. Use `Set.indicator_of_mem ?_ _` and prove the remaining obligations. Introduce `x i k`. Establish `e : (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin (g • ratTup (AF F) X0)) x i) k = evalV F v (crd b (Af F) (projFin (g • ratTup (AF F) X0) x i) k)`.

Rewrite using `[← crd_map]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h2 x i k v`. Use `show 0 < fi (projInf (g • ratTup (AF F) X0)) * ∏ᶠ v, ind v (projV v (projFin (g • ratTup (AF F) X0)))`.

Simplify using `only [hone, finprod_one, mul_one]`. Conclude with `h1`.
-/
theorem testNear_holds : TestNear := by
  intro F E _ _ _ _ _ σ hE M J _hJ _ha _hc a _ha1 _ha2 X0 _hT _hdet
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  obtain ⟨d, b, hb⟩ := exists_int_basis (F := F) X0
  obtain ⟨fi, hfc, hf0, hfx⟩ := exists_continuous_nonneg_pos (projInf (ratTup (AF F) X0))
  let ind : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℝ :=
    fun v => (latV b v).indicator (fun _ => (1 : ℝ))
  let φ : (Fin a → Fin M → AF F ⊗[F] E) → ℝ :=
    fun X => fi (projInf X) * ∏ᶠ v, ind v (projV v (projFin X))
  have hφ0 : ∀ X, 0 ≤ φ X := fun X =>
    mul_nonneg (hf0 _) (finprod_nonneg fun v => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hcast : ∀ v (Y : Fin a → Fin M → Fv F v ⊗[F] E),
      ((ind v Y : ℝ) : ℂ) = (latV b v).indicator (fun _ => (1 : ℂ)) Y := by
    intro v Y
    by_cases h : Y ∈ latV b v <;> simp [ind, h]
  have hadm : IsAdm F E (fun X => (φ X : ℂ)) := by
    refine ⟨d, b, fun Y => (fi Y : ℂ),
      fun Y => ∏ᶠ v, (latV b v).indicator (fun _ => (1 : ℂ)) (projV v Y),
      fun v => (latV b v).indicator (fun _ => (1 : ℂ)),
      Complex.continuous_ofReal.comp fi.continuous, hfc.comp_left Complex.ofReal_zero,
      ⟨fun v => isSB_latV b v a M, Filter.Eventually.of_forall fun v => rfl, fun X => rfl⟩,
      fun X => ?_⟩
    simp only [φ, Complex.ofReal_mul, ← hcast]
    congr 1
    exact Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _
  let U : Set (HA (AF F) σ J) := {g | 0 < fi (projInf (g • ratTup (AF F) X0))} ∩
    ⋂ x, ⋂ i, ⋂ k, (fun g : HA (AF F) σ J =>
      crd b (Af F) (projFin (g • ratTup (AF F) X0) x i) k) ⁻¹' ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F
  have horb := continuous_orbit σ J (ratTup (AF F) X0)
  refine ⟨φ, hφ0, hadm, U, ?_, ⟨1, ?_⟩, ?_⟩
  · refine (isOpen_lt continuous_const
      (fi.continuous.comp ((continuous_projInf b).comp horb))).inter ?_
    refine isOpen_iInter_of_finite fun x => isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun k => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_Oint.preimage ?_
    have hpf : Continuous fun g : HA (AF F) σ J => projFin (g • ratTup (AF F) X0) :=
      (continuous_projFin b).comp horb
    exact (continuous_crd b (Af F) k).comp ((continuous_apply i).comp ((continuous_apply x).comp hpf))
  · refine ⟨?_, ?_⟩
    · show 0 < fi (projInf ((1 : HA (AF F) σ J) • ratTup (AF F) X0))
      rw [one_smul]
      exact lt_of_le_of_ne (hf0 _) (Ne.symm hfx)
    · simp only [Set.mem_iInter, Set.mem_preimage, one_smul]
      intro x i k
      obtain ⟨m, hm⟩ := hb x i k
      have e : crd b (Af F) (projFin (ratTup (AF F) X0) x i) k = algebraMap F (Af F) (m : F) := by
        simp only [projFin, ratTup, crd_map, crd_incl, AlgHom.commutes, hm]
      rw [e]
      exact ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.algebraMap_int_mem_Oint m
  · rintro g ⟨h1, h2⟩
    simp only [Set.mem_iInter, Set.mem_preimage] at h2
    have hone : ∀ v, ind v (projV v (projFin (g • ratTup (AF F) X0))) = 1 := by
      intro v
      refine Set.indicator_of_mem ?_ _
      intro x i k
      have e : (Algebra.TensorProduct.basis (Fv F v) b).repr
          (projV v (projFin (g • ratTup (AF F) X0)) x i) k =
          evalV F v (crd b (Af F) (projFin (g • ratTup (AF F) X0) x i) k) := by
        rw [← crd_map]
        rfl
      rw [e]
      exact h2 x i k v
    show 0 < fi (projInf (g • ratTup (AF F) X0)) *
      ∏ᶠ v, ind v (projV v (projFin (g • ratTup (AF F) X0)))
    simp only [hone, finprod_one, mul_one]
    exact h1

end PI.VolStabW
