import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdelicExtensionOfAlgebraicWeightDefiniteUnStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinitePartMulDefiniteUnitaryInfinitePointStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitaryRationalMatrixOfFirstPresentationPoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNhdOneInUnitaryPrincipalCongruenceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Matrix Topology

noncomputable section

namespace GlobalTheory.FormDictEx

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def fpt (g : UA L n) : UA L n :=
  ⟨finGL L n (GeneralLinearGroup.map (pFin L) g.1), GlobalTheory.DefU.ClassFin.finGL_mem_UA _ (GlobalTheory.DefU.ClassFin.cT_pFin g)⟩

/- English proof (translation)
The claim follows from `pInf_finGL _`.
-/
theorem fpt_mem (g : UA L n) : fpt g ∈ finU L n := pInf_finGL _

/- English proof (translation)
The claim follows from `Subtype.ext (by simp only [fpt, Subgroup.coe_mul, map_mul])`.
-/
theorem fpt_mul (g h : UA L n) : fpt (g * h) = fpt g * fpt h :=
  Subtype.ext (by simp only [fpt, Subgroup.coe_mul, map_mul])

/- English proof (translation)
Establish `h1 : GeneralLinearGroup.map (pInf L) g.1 = 1` using `hg`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `finGL L n _ = g.1`. Use `conv_rhs => rw [← infGL_mul_finGL g.1, h1, map_one, one_mul]`.
-/
theorem fpt_of_mem_fin {g : UA L n} (hg : g ∈ finU L n) : fpt g = g := by
  have h1 : GeneralLinearGroup.map (pInf L) g.1 = 1 := hg
  apply Subtype.ext
  change finGL L n _ = g.1
  conv_rhs => rw [← infGL_mul_finGL g.1, h1, map_one, one_mul]

/- English proof (translation)
Establish `h1 : GeneralLinearGroup.map (pFin L) g.1 = 1` using `hg`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `finGL L n _ = 1`. Rewrite using `[h1, map_one]`.
-/
theorem fpt_of_mem_inf {g : UA L n} (hg : g ∈ infU L n) : fpt g = 1 := by
  have h1 : GeneralLinearGroup.map (pFin L) g.1 = 1 := hg
  apply Subtype.ext
  change finGL L n _ = 1
  rw [h1, map_one]

/- English proof (translation)
Establish `hs : Continuous (sFin L)` using `(continuous_const.prodMk continuous_id : Continuous fun x : Af L => ((0, x) : InfiniteAdeleRing L × Af L))`. Establish `h1 : Continuous (finGL L n)`. Use `Continuous.units_map _ ?_` and prove the remaining obligations. Conclude with `continuous_const.add (Continuous.matrix_map continuous_id hs)`. Establish `h2 : Continuous (GeneralLinearGroup.map (pFin L) : GL (Fin n) (Ad L) →* GL (Fin n) (Af L))` using `Continuous.units_map _ (Continuous.matrix_map continuous_id continuous_snd)`.

Conclude with `(h1.comp (h2.comp continuous_subtype_val)).subtype_mk _`.
-/
theorem continuous_fpt : Continuous (fpt : UA L n → UA L n) := by
  have hs : Continuous (sFin L) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af L => ((0, x) : InfiniteAdeleRing L × Af L))
  have h1 : Continuous (finGL L n) := by
    refine Continuous.units_map _ ?_
    exact continuous_const.add (Continuous.matrix_map continuous_id hs)
  have h2 : Continuous (GeneralLinearGroup.map (pFin L) : GL (Fin n) (Ad L) →* GL (Fin n) (Af L)) :=
    Continuous.units_map _ (Continuous.matrix_map continuous_id continuous_snd)
  exact (h1.comp (h2.comp continuous_subtype_val)).subtype_mk _

/- English proof (translation)
Introduce `x x' h`. Establish `key : ∀ s t, ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t = ((x' : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t`. Introduce `s t`. Apply `F.κ.injective` to reduce the goal to its premises. Apply `FiniteAdeleRing.ext L` to reduce the goal to its premises.

Introduce `w`. Rewrite using `[← F.loc x w s t, ← F.loc x' w s t, h]`. Conclude with `Subtype.ext (Units.ext (Matrix.ext key))`.
-/
theorem j_injective (F : FinIso L n) : Function.Injective F.j := by
  intro x x' h
  have key : ∀ s t, ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t =
      ((x' : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t := by
    intro s t
    apply F.κ.injective
    apply FiniteAdeleRing.ext L
    intro w
    rw [← F.loc x w s t, ← F.loc x' w s t, h]
  exact Subtype.ext (Units.ext (Matrix.ext key))

def fy (F : FinIso L n) (g : UA L n) : GAf L n := (F.onto _ (fpt_mem g)).choose

/- English proof (translation)
The claim follows from `(F.onto _ (fpt_mem g)).choose_spec`.
-/
theorem j_fy (F : FinIso L n) (g : UA L n) : F.j (fy F g) = fpt g := (F.onto _ (fpt_mem g)).choose_spec

/- English proof (translation)
The claim follows from `j_injective F (by rw [map_mul, j_fy, j_fy, j_fy, fpt_mul])`.
-/
theorem fy_mul (F : FinIso L n) (g h : UA L n) : fy F (g * h) = fy F g * fy F h :=
  j_injective F (by rw [map_mul, j_fy, j_fy, j_fy, fpt_mul])

/- English proof (translation)
The claim follows from `j_injective F (by rw [j_fy, fpt_of_mem_fin (F.fin x)])`.
-/
theorem fy_j (F : FinIso L n) (x : GAf L n) : fy F (F.j x) = x :=
  j_injective F (by rw [j_fy, fpt_of_mem_fin (F.fin x)])

/- English proof (translation)
The claim follows from `j_injective F (by rw [j_fy, fpt_of_mem_inf hg, map_one])`.
-/
theorem fy_inf (F : FinIso L n) {g : UA L n} (hg : g ∈ infU L n) : fy F g = 1 :=
  j_injective F (by rw [j_fy, fpt_of_mem_inf hg, map_one])

/- English proof (translation)
The claim follows from `j_injective F (by rw [j_fy, j_fy, fpt_of_mem_fin (fpt_mem g)])`.
-/
theorem fy_fpt (F : FinIso L n) (g : UA L n) : fy F (fpt g) = fy F g :=
  j_injective F (by rw [j_fy, j_fy, fpt_of_mem_fin (fpt_mem g)])

/- English proof (translation)
The claim follows from `funext fun g => congrArg f (mul_one g)`.
-/
theorem rt_one {W : Type} [AddCommGroup W] [Module ℂ W] (f : GAf L n → W) : NG.rt L n 1 f = f :=
  funext fun g => congrArg f (mul_one g)

section Phi

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def phi (F : FinIso L n) (R : UA L n →* Module.End ℂ W) (f : GAf L n → W) (lam : Module.Dual ℂ W) : UA L n → ℂ :=
  fun g => lam (R g⁻¹ (f (fy F g)))

variable (F : FinIso L n) (R : UA L n →* Module.End ℂ W)

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [GlobalTheory.DefU.RU_apply, phi, fy_mul, _root_.mul_inv_rev, map_mul, LinearMap.comp_apply, Module.End.mul_apply]`. Both sides reduce to the same expression.
-/
theorem RU_phi (f : GAf L n → W) (lam : Module.Dual ℂ W) (x : UA L n) :
    RU L n x (phi F R f lam) = phi F R (NG.rt L n (fy F x) f) (lam ∘ₗ R x⁻¹) := by
  funext g
  simp only [GlobalTheory.DefU.RU_apply, phi, fy_mul, _root_.mul_inv_rev, map_mul, LinearMap.comp_apply, Module.End.mul_apply]
  rfl

/- English proof (translation)
Simplify using `only [phi, fy_j, hfin _ ((finU L n).inv_mem (F.fin x)), Module.End.one_apply]`.
-/
theorem phi_j (hfin : ∀ k ∈ finU L n, R k = 1) (f : GAf L n → W) (lam : Module.Dual ℂ W) (x : GAf L n) :
    phi F R f lam (F.j x) = lam (f x) := by
  simp only [phi, fy_j, hfin _ ((finU L n).inv_mem (F.fin x)), Module.End.one_apply]

def phiR (f : GAf L n → W) : Module.Dual ℂ W →ₗ[ℂ] (UA L n → ℂ) where
  toFun lam := phi F R f lam
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def phiL (lam : Module.Dual ℂ W) : (GAf L n → W) →ₗ[ℂ] (UA L n → ℂ) where
  toFun f := phi F R f lam
  map_add' f f' := funext fun g => by simp [phi]
  map_smul' c f := funext fun g => by simp [phi]

/- English proof (translation)
The claim follows from `map_add (phiL F R lam) f f'`.
-/
theorem phi_add (lam : Module.Dual ℂ W) (f f' : GAf L n → W) :
    phi F R (f + f') lam = phi F R f lam + phi F R f' lam := map_add (phiL F R lam) f f'

/- English proof (translation)
The claim follows from `map_zero (phiL F R lam)`.
-/
theorem phi_zero (lam : Module.Dual ℂ W) : phi F R (0 : GAf L n → W) lam = 0 := map_zero (phiL F R lam)

/- English proof (translation)
The claim follows from `map_smul (phiL F R lam) c f`.
-/
theorem phi_smul (lam : Module.Dual ℂ W) (c : ℂ) (f : GAf L n → W) :
    phi F R (c • f) lam = c • phi F R f lam := map_smul (phiL F R lam) c f

end Phi

section Main

variable {W : Type} [AddCommGroup W] [Module ℂ W] (F : FinIso L n) (ρ : Representation ℂ (GQ L n) W)
  (R : UA L n →* Module.End ℂ W)

/- English proof (translation)
Take `⟨hleft, N, hN, hinv⟩` from `hf`. Take `⟨O, hO, h1O, hOc⟩` from `GlobalTheory.T.exists_open_nhd_one_in_unitary_principal_congruence L n F N hN`. Establish `hOf : ∀ k ∈ O, ∀ g, f (g * fy F (k : UA L n)) = f g` using `fun k hk g => hinv _ (hOc k hk _ (by rw [j_fy, fpt_of_mem_fin k.2])) g`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `continuous_iff_continuousAt.2 fun g0 => ?_` and prove the remaining obligations.

Establish `hc : Continuous fun g : UA L n => lam (R g⁻¹ (f (fy F g0)))` using `(hcont (f (fy F g0)) lam).comp continuous_inv`. Use `hc.continuousAt.congr ?_` and prove the remaining obligations. Set `q : UA L n → finU L n` to `fun g => ⟨fpt (g0⁻¹ * g), fpt_mem _⟩`. Establish `hq : Continuous q` using `(continuous_fpt.comp (continuous_const.mul continuous_id)).subtype_mk _`. Establish `hq0 : q g0 = 1` using `Subtype.ext (by`.

Express the relevant statement in the definitionally equal form `fpt (g0⁻¹ * g0) = 1`. Rewrite using `[inv_mul_cancel]`. Conclude with `fpt_of_mem_fin (finU L n).one_mem)`. Establish `hmem : q ⁻¹' O ∈ 𝓝 g0` using `(hO.preimage hq).mem_nhds (by rw [Set.mem_preimage, hq0]; exact h1O)`. Use `filter_upwards [hmem] with g hg`.

Establish `e : fy F g = fy F g0 * fy F (q g : UA L n)`. Express the relevant statement in the definitionally equal form `fy F g = fy F g0 * fy F (fpt (g0⁻¹ * g))`. Rewrite using `[fy_fpt, ← fy_mul, mul_inv_cancel_left]`. Express the relevant statement in the definitionally equal form `lam (R g⁻¹ (f (fy F g0))) = lam (R g⁻¹ (f (fy F g)))`. Rewrite using `[e, hOf _ hg]`.

Introduce `γ hγ g`. Take `⟨γQ, γ₀, h1, h2, h3⟩` from `GlobalTheory.T.exists_finite_part_mul_definite_unitary_infinite_point L n F γ hγ`. Establish `hy : fy F γ = γQ`. Use `fy_mul F (γ * (F.j γQ)⁻¹) (F.j γQ)` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_right, fy_inf F h3, fy_j, one_mul]`.

Conclude with `this`. Simplify using `only [phi, fy_mul, hy, hleft, _root_.mul_inv_rev, map_mul, Module.End.mul_apply]`. Rewrite using `[← hrat γ γQ γ₀ h1 h2, ← Module.End.mul_apply (R γ⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Set `H : Subgroup (finU L n)` to `{ carrier := {k | RU L n (k : UA L n) (phi F R f lam) = phi F R f lam} mul_mem' := fun {a b} ha hb => by`. Express the relevant statement in the definitionally equal form `RU L n ((a : UA L n) * b) _ = _`.

Rewrite using `[← GlobalTheory.DefU.RU_RU, hb, ha]`. Use the proof step `one_mem' := by`. Express the relevant statement in the definitionally equal form `RU L n 1 _ = _`. Rewrite using `[map_one]`. Both sides reduce to the same expression.

Use the proof step `inv_mem' := fun {a} ha => by`. Express the relevant statement in the definitionally equal form `RU L n ((a : UA L n)⁻¹) _ = _`. Use `conv_lhs => rw [← ha]`. Express the relevant statement in the definitionally equal form `RU L n ((a : UA L n)⁻¹) (RU L n (a : UA L n) _) = _`. Rewrite using `[GlobalTheory.DefU.RU_RU, inv_mul_cancel, map_one]`.

Use `rfl }`. Use `H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hO.mem_nhds h1O) fun k hk => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `RU L n (k : UA L n) _ = _`. Rewrite using `[RU_phi, hfin _ ((finU L n).inv_mem k.2), show lam ∘ₗ (1 : Module.End ℂ W) = lam from LinearMap.ext fun _ => rfl]`. Use `congr 1`.

Conclude with `funext (hOf k hk)`. Use `Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (phiR F R f)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Use `⟨lam ∘ₗ R (k : UA L n)⁻¹, ?_⟩` and prove the remaining obligations. Use `show _ = RU L n (k : UA L n) (phi F R f lam)`.

Rewrite using `[RU_phi, fy_inf F k.2, rt_one]`. Both sides reduce to the same expression.
-/
theorem isAutFormU_phi (hfin : ∀ k ∈ finU L n, R k = 1)
    (hrat : ∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ →
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = ρ γQ)
    (hcont : ∀ (v : W) (μ : Module.Dual ℂ W), Continuous fun g : UA L n => μ (R g v))
    [FiniteDimensional ℂ W] {f : GAf L n → W} (hf : f ∈ NG.AFall L n ρ) (lam : Module.Dual ℂ W) :
    IsAutFormU (phi F R f lam) := by
  obtain ⟨hleft, N, hN, hinv⟩ := hf
  obtain ⟨O, hO, h1O, hOc⟩ := GlobalTheory.T.exists_open_nhd_one_in_unitary_principal_congruence L n F N hN
  have hOf : ∀ k ∈ O, ∀ g, f (g * fy F (k : UA L n)) = f g := fun k hk g =>
    hinv _ (hOc k hk _ (by rw [j_fy, fpt_of_mem_fin k.2])) g
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g0 => ?_
    have hc : Continuous fun g : UA L n => lam (R g⁻¹ (f (fy F g0))) :=
      (hcont (f (fy F g0)) lam).comp continuous_inv
    refine hc.continuousAt.congr ?_
    let q : UA L n → finU L n := fun g => ⟨fpt (g0⁻¹ * g), fpt_mem _⟩
    have hq : Continuous q := (continuous_fpt.comp (continuous_const.mul continuous_id)).subtype_mk _
    have hq0 : q g0 = 1 := Subtype.ext (by
      change fpt (g0⁻¹ * g0) = 1
      rw [inv_mul_cancel]
      exact fpt_of_mem_fin (finU L n).one_mem)
    have hmem : q ⁻¹' O ∈ 𝓝 g0 := (hO.preimage hq).mem_nhds (by rw [Set.mem_preimage, hq0]; exact h1O)
    filter_upwards [hmem] with g hg
    have e : fy F g = fy F g0 * fy F (q g : UA L n) := by
      change fy F g = fy F g0 * fy F (fpt (g0⁻¹ * g))
      rw [fy_fpt, ← fy_mul, mul_inv_cancel_left]
    change lam (R g⁻¹ (f (fy F g0))) = lam (R g⁻¹ (f (fy F g)))
    rw [e, hOf _ hg]
  · intro γ hγ g
    obtain ⟨γQ, γ₀, h1, h2, h3⟩ := GlobalTheory.T.exists_finite_part_mul_definite_unitary_infinite_point L n F γ hγ
    have hy : fy F γ = γQ := by
      have := fy_mul F (γ * (F.j γQ)⁻¹) (F.j γQ)
      rw [inv_mul_cancel_right, fy_inf F h3, fy_j, one_mul] at this
      exact this
    simp only [phi, fy_mul, hy, hleft, _root_.mul_inv_rev, map_mul, Module.End.mul_apply]
    rw [← hrat γ γQ γ₀ h1 h2, ← Module.End.mul_apply (R γ⁻¹), ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  · let H : Subgroup (finU L n) :=
      { carrier := {k | RU L n (k : UA L n) (phi F R f lam) = phi F R f lam}
        mul_mem' := fun {a b} ha hb => by
          change RU L n ((a : UA L n) * b) _ = _
          rw [← GlobalTheory.DefU.RU_RU, hb, ha]
        one_mem' := by
          change RU L n 1 _ = _
          rw [map_one]; rfl
        inv_mem' := fun {a} ha => by
          change RU L n ((a : UA L n)⁻¹) _ = _
          conv_lhs => rw [← ha]
          change RU L n ((a : UA L n)⁻¹) (RU L n (a : UA L n) _) = _
          rw [GlobalTheory.DefU.RU_RU, inv_mul_cancel, map_one]; rfl }
    refine H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hO.mem_nhds h1O) fun k hk => ?_)
    change RU L n (k : UA L n) _ = _
    rw [RU_phi, hfin _ ((finU L n).inv_mem k.2), show lam ∘ₗ (1 : Module.End ℂ W) = lam from LinearMap.ext fun _ => rfl]
    congr 1
    exact funext (hOf k hk)
  · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (phiR F R f)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨lam ∘ₗ R (k : UA L n)⁻¹, ?_⟩
    show _ = RU L n (k : UA L n) (phi F R f lam)
    rw [RU_phi, fy_inf F k.2, rt_one]
    rfl

def gens (S : Submodule ℂ (GAf L n → W)) : Set (UA L n → ℂ) :=
  {ψ | ∃ f ∈ S, ∃ lam : Module.Dual ℂ W, ψ = phi F R f lam}

/- English proof (translation)
Use `set U := Submodule.span ℂ (gens F R S) with hU`. Use `⟨⟨fun ψ hψ => ?_, fun x ψ hψ => ?_, ?_, fun W' hW' hst => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hle : U ≤ GlobalTheory.DefU.autU L n` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨f, hf, lam, rfl⟩`. Conclude with `isAutFormU_phi F ρ R hfin hrat hcont (hS.1.le hf) lam)`.

Conclude with `hle hψ`. Establish `hle : U ≤ U.comap (RU L n x)` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨f, hf, lam, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, RU_phi]`. Conclude with `Submodule.subset_span ⟨_, hS.1.stable _ f hf, _, rfl⟩)`.

Conclude with `hle hψ`. Introduce `hbot`. Take `⟨f, hf, hf0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hS.2.1`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, f x ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `hf0 (funext h)`. Choose the witnesses or unpack the hypotheses as in `⟨lam, hlam⟩ : ∃ lam : Module.Dual ℂ W, lam (f x) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hx ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)`. Establish `hmem : phi F R f lam ∈ U` using `Submodule.subset_span ⟨f, hf, lam, rfl⟩`. Rewrite `hmem` using `[hbot, Submodule.mem_bot]`. Conclude with `hlam (by rw [← phi_j F R hfin f lam x, hmem]; rfl)`. Set `S' : Submodule ℂ (GAf L n → W)` to `{ carrier := {f | f ∈ S ∧ ∀ lam, phi F R f lam ∈ W'} add_mem' := fun {a b} ha hb => ⟨S.add_mem ha.1 hb.1, fun lam => by`.

Use `W'.add_mem (ha.2 lam) (hb.2 lam)` as an intermediate fact. Rewrite using `[phi_add]⟩` and apply the resulting hypothesis. Use the proof step `zero_mem' := ⟨S.zero_mem, fun lam => by`. Use `W'.zero_mem` as an intermediate fact. Rewrite using `[phi_zero]⟩` and apply the resulting hypothesis.

Use the proof step `smul_mem' := fun c a ha => ⟨S.smul_mem c ha.1, fun lam => by`. Use `W'.smul_mem c (ha.2 lam)` as an intermediate fact. Rewrite using `[phi_smul]⟩ }` and apply the resulting hypothesis. Establish `hsub : NG.IsSubrep ρ S'` using `⟨fun f hf => hS.1.le hf.1, fun h f hf => ⟨hS.1.stable h f hf.1, fun lam => by`. Use `hst (F.j h) _ (hf.2 lam)` as an intermediate fact.

Rewrite using `[RU_phi, fy_j, hfin _ ((finU L n).inv_mem (F.fin h)), show lam ∘ₗ (1 : Module.End ℂ W) = lam from LinearMap.ext fun _ => rfl] at this⟩⟩` and apply the resulting hypothesis. Break down `hS.2.2 S' hsub (fun f hf => hf.1) with h | h` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`. Introduce `ψ hψ`.

Rewrite using `[Submodule.mem_bot]`. Take `⟨m, c, g, hsum⟩` from `Submodule.mem_span_set'.1 (hW' hψ)`. Use `choose fs hfs lams hg using fun i => (g i).2`. Set `lp : Fin m → Module.Dual ℂ W` to `fun i => c i • lams i`. Establish `hψe : ψ = ∑ i, phi F R (fs i) (lp i)`.

Rewrite using `[← hsum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hg i]`. Both sides reduce to the same expression. Set `T : Module.End ℂ W →ₗ[ℂ] (UA L n → ℂ)` to `∑ i, phiR F R (fs i) ∘ₗ LinearMap.llcomp ℂ W W ℂ (lp i)`.

Establish `hT : ∀ B, T B = ∑ i, phi F R (fs i) (lp i ∘ₗ B)` using `fun B => by`. Rewrite using `[LinearMap.sum_apply]`. Both sides reduce to the same expression. Establish `hTinf : ∀ x ∈ infU L n, T (R x) ∈ W'`. Introduce `x hx`.

Use `hst x⁻¹ ψ hψ` as an intermediate fact. Rewrite `this` using `[hψe, map_sum]`. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hT]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[RU_phi, fy_inf F ((infU L n).inv_mem hx), rt_one, inv_inv]`. Establish `htop : Submodule.span ℂ (Set.range ρ) ≤ W'.comap T`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨γQ, rfl⟩`. Take `⟨γ, γ₀, h1, h2⟩` from `GlobalTheory.T.exists_unitary_rational_matrix_of_first_presentation_point L n γQ`.

Establish `hx : γ * (fpt γ)⁻¹ ∈ infU L n`. Express the relevant statement in the definitionally equal form `GeneralLinearGroup.map (pFin L) (γ * (fpt γ)⁻¹).1 = 1`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]`. Express the relevant statement in the definitionally equal form `_ * (GeneralLinearGroup.map (pFin L) (finGL L n (GeneralLinearGroup.map (pFin L) γ.1)))⁻¹ = 1`. Rewrite using `[pFin_finGL, mul_inv_cancel]`.

Establish `hR : R (γ * (fpt γ)⁻¹) = ρ γQ`. Rewrite using `[map_mul, hfin _ ((finU L n).inv_mem (fpt_mem γ)), mul_one, hrat γ γQ γ₀ h1 h2]`. Use `show T (ρ γQ) ∈ W'`. Rewrite using `[← hR]`. Conclude with `hTinf _ hx`.

Rewrite `htop` using `[GlobalTheory.BurnsideField.span_range_eq_top_of_isAlgClosed ρ hρ]`. Establish `hall : ∀ B, T B ∈ W'` using `fun B => htop Submodule.mem_top`. Establish `hF : ∀ v : W, (∑ i, lp i v • fs i) = 0`. Introduce `v`. Establish `hmem : (∑ i, lp i v • fs i) ∈ S'`.

Use `⟨Submodule.sum_mem _ fun i _ => S.smul_mem _ (hfs i), fun μ => ?_⟩` and prove the remaining obligations. Use `hall (μ.smulRight v)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hT]`. Express the relevant statement in the definitionally equal form `phiL F R μ (∑ i, lp i v • fs i) = _`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Establish `e : lp i ∘ₗ μ.smulRight v = lp i v • μ` using `LinearMap.ext fun w => by`. Simplify using `[mul_comm]`.

Rewrite using `[e]`. Conclude with `(map_smul (phiR F R (fs i)) (lp i v) μ).symm`. Rewrite `hmem` using `[h]`. Conclude with `(Submodule.mem_bot ℂ).1 hmem`. Rewrite using `[hψe]`.

Use function extensionality and compare the values at `y`. Rewrite using `[Finset.sum_apply, Pi.zero_apply]`. Simplify using `only [phi]`. Set `b` to `Module.finBasis ℂ W`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [← b.sum_repr (R y⁻¹ (fs i (fy F y)))]`. Rewrite using `[map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Use `_ = ∑ k, ∑ i, b.repr (R y⁻¹ (fs i (fy F y))) k * lp i (b k) := Finset.sum_comm`.

Use `_ = ∑ k, b.repr (R y⁻¹ ((∑ i, lp i (b k) • fs i) (fy F y))) k := by`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[Finset.sum_apply, map_sum, map_smul, mul_comm]`. Use `_ = 0 := by simp only [hF, Pi.zero_apply, map_zero, Finsupp.zero_apply, Finset.sum_const_zero]`. Use `right`.

Use `le_antisymm hW' (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, lam, rfl⟩`. Rewrite `hf` using `[← h]`. Conclude with `hf.2 lam`. Rewrite using `[Submodule.map_span]`.

Use `congr 1`. Use extensionality with `φ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨f, hf, lam, rfl⟩, rfl⟩`. Conclude with `⟨f, hf, lam, funext fun x => phi_j F R hfin f lam x⟩`.

Introduce and unpack `⟨f, hf, lam, rfl⟩`. Conclude with `⟨_, ⟨f, hf, lam, rfl⟩, funext fun x => phi_j F R hfin f lam x⟩`.
-/
theorem dict_span [FiniteDimensional ℂ W] (hρ : ρ.IsIrreducible) (S : Submodule ℂ (GAf L n → W))
    (hS : NG.IsIrrRep ρ S) (hfin : ∀ k ∈ finU L n, R k = 1)
    (hrat : ∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ →
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = ρ γQ)
    (hcont : ∀ (v : W) (μ : Module.Dual ℂ W), Continuous fun g : UA L n => μ (R g v)) :
    IsAutRepU (Submodule.span ℂ (gens F R S)) ∧
      (Submodule.span ℂ (gens F R S)).map (LinearMap.funLeft ℂ ℂ F.j) =
        Submodule.span ℂ {φ | ∃ f ∈ S, ∃ lam : Module.Dual ℂ W, φ = fun x => lam (f x)} := by
  set U := Submodule.span ℂ (gens F R S) with hU
  refine ⟨⟨fun ψ hψ => ?_, fun x ψ hψ => ?_, ?_, fun W' hW' hst => ?_⟩, ?_⟩
  ·
    have hle : U ≤ GlobalTheory.DefU.autU L n := Submodule.span_le.2 (by
      rintro _ ⟨f, hf, lam, rfl⟩
      exact isAutFormU_phi F ρ R hfin hrat hcont (hS.1.le hf) lam)
    exact hle hψ
  ·
    have hle : U ≤ U.comap (RU L n x) := Submodule.span_le.2 (by
      rintro _ ⟨f, hf, lam, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, RU_phi]
      exact Submodule.subset_span ⟨_, hS.1.stable _ f hf, _, rfl⟩)
    exact hle hψ
  ·
    intro hbot
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS.2.1
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (funext h)
    obtain ⟨lam, hlam⟩ : ∃ lam : Module.Dual ℂ W, lam (f x) ≠ 0 := by
      by_contra h
      push Not at h
      exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
    have hmem : phi F R f lam ∈ U := Submodule.subset_span ⟨f, hf, lam, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hlam (by rw [← phi_j F R hfin f lam x, hmem]; rfl)
  ·
    let S' : Submodule ℂ (GAf L n → W) :=
      { carrier := {f | f ∈ S ∧ ∀ lam, phi F R f lam ∈ W'}
        add_mem' := fun {a b} ha hb => ⟨S.add_mem ha.1 hb.1, fun lam => by
          have := W'.add_mem (ha.2 lam) (hb.2 lam)
          rwa [phi_add]⟩
        zero_mem' := ⟨S.zero_mem, fun lam => by
          have := W'.zero_mem
          rwa [phi_zero]⟩
        smul_mem' := fun c a ha => ⟨S.smul_mem c ha.1, fun lam => by
          have := W'.smul_mem c (ha.2 lam)
          rwa [phi_smul]⟩ }
    have hsub : NG.IsSubrep ρ S' := ⟨fun f hf => hS.1.le hf.1, fun h f hf => ⟨hS.1.stable h f hf.1, fun lam => by
      have := hst (F.j h) _ (hf.2 lam)
      rwa [RU_phi, fy_j, hfin _ ((finU L n).inv_mem (F.fin h)),
        show lam ∘ₗ (1 : Module.End ℂ W) = lam from LinearMap.ext fun _ => rfl] at this⟩⟩
    rcases hS.2.2 S' hsub (fun f hf => hf.1) with h | h
    · left
      rw [eq_bot_iff]
      intro ψ hψ
      rw [Submodule.mem_bot]
      obtain ⟨m, c, g, hsum⟩ := Submodule.mem_span_set'.1 (hW' hψ)
      choose fs hfs lams hg using fun i => (g i).2
      let lp : Fin m → Module.Dual ℂ W := fun i => c i • lams i
      have hψe : ψ = ∑ i, phi F R (fs i) (lp i) := by
        rw [← hsum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hg i]
        rfl
      let T : Module.End ℂ W →ₗ[ℂ] (UA L n → ℂ) := ∑ i, phiR F R (fs i) ∘ₗ LinearMap.llcomp ℂ W W ℂ (lp i)
      have hT : ∀ B, T B = ∑ i, phi F R (fs i) (lp i ∘ₗ B) := fun B => by
        rw [LinearMap.sum_apply]
        rfl
      have hTinf : ∀ x ∈ infU L n, T (R x) ∈ W' := by
        intro x hx
        have := hst x⁻¹ ψ hψ
        rw [hψe, map_sum] at this
        convert this using 1
        rw [hT]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [RU_phi, fy_inf F ((infU L n).inv_mem hx), rt_one, inv_inv]
      have htop : Submodule.span ℂ (Set.range ρ) ≤ W'.comap T := by
        rw [Submodule.span_le]
        rintro _ ⟨γQ, rfl⟩
        obtain ⟨γ, γ₀, h1, h2⟩ := GlobalTheory.T.exists_unitary_rational_matrix_of_first_presentation_point L n γQ
        have hx : γ * (fpt γ)⁻¹ ∈ infU L n := by
          change GeneralLinearGroup.map (pFin L) (γ * (fpt γ)⁻¹).1 = 1
          rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
          change _ * (GeneralLinearGroup.map (pFin L) (finGL L n (GeneralLinearGroup.map (pFin L) γ.1)))⁻¹ = 1
          rw [pFin_finGL, mul_inv_cancel]
        have hR : R (γ * (fpt γ)⁻¹) = ρ γQ := by
          rw [map_mul, hfin _ ((finU L n).inv_mem (fpt_mem γ)), mul_one, hrat γ γQ γ₀ h1 h2]
        show T (ρ γQ) ∈ W'
        rw [← hR]
        exact hTinf _ hx
      rw [GlobalTheory.BurnsideField.span_range_eq_top_of_isAlgClosed ρ hρ] at htop
      have hall : ∀ B, T B ∈ W' := fun B => htop Submodule.mem_top
      have hF : ∀ v : W, (∑ i, lp i v • fs i) = 0 := by
        intro v
        have hmem : (∑ i, lp i v • fs i) ∈ S' := by
          refine ⟨Submodule.sum_mem _ fun i _ => S.smul_mem _ (hfs i), fun μ => ?_⟩
          have := hall (μ.smulRight v)
          convert this using 1
          rw [hT]
          change phiL F R μ (∑ i, lp i v • fs i) = _
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul]
          have e : lp i ∘ₗ μ.smulRight v = lp i v • μ := LinearMap.ext fun w => by
            simp [mul_comm]
          rw [e]
          exact (map_smul (phiR F R (fs i)) (lp i v) μ).symm
        rw [h] at hmem
        exact (Submodule.mem_bot ℂ).1 hmem
      rw [hψe]
      funext y
      rw [Finset.sum_apply, Pi.zero_apply]
      simp only [phi]
      let b := Module.finBasis ℂ W
      calc ∑ i, lp i (R y⁻¹ (fs i (fy F y)))
          = ∑ i, ∑ k, b.repr (R y⁻¹ (fs i (fy F y))) k * lp i (b k) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            conv_lhs => rw [← b.sum_repr (R y⁻¹ (fs i (fy F y)))]
            rw [map_sum]
            simp only [map_smul, smul_eq_mul]
        _ = ∑ k, ∑ i, b.repr (R y⁻¹ (fs i (fy F y))) k * lp i (b k) := Finset.sum_comm
        _ = ∑ k, b.repr (R y⁻¹ ((∑ i, lp i (b k) • fs i) (fy F y))) k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simp [Finset.sum_apply, map_sum, map_smul, mul_comm]
        _ = 0 := by simp only [hF, Pi.zero_apply, map_zero, Finsupp.zero_apply, Finset.sum_const_zero]
    · right
      refine le_antisymm hW' (Submodule.span_le.2 ?_)
      rintro _ ⟨f, hf, lam, rfl⟩
      rw [← h] at hf
      exact hf.2 lam
  · rw [Submodule.map_span]
    congr 1
    ext φ
    constructor
    · rintro ⟨_, ⟨f, hf, lam, rfl⟩, rfl⟩
      exact ⟨f, hf, lam, funext fun x => phi_j F R hfin f lam x⟩
    · rintro ⟨f, hf, lam, rfl⟩
      exact ⟨_, ⟨f, hf, lam, rfl⟩, funext fun x => phi_j F R hfin f lam x⟩

end Main

/- English proof (translation)
Introduce `L _ _ _ n F π`. Use `haveI : FiniteDimensional ℂ π.W := π.alg.1`. Take `⟨R, hfin, hrat, hcont⟩` from `GlobalTheory.T.exists_adelic_extension_of_algebraicWeight_definiteUnitary L n π.toAlgWt`. Conclude with `⟨_, dict_span F π.ρ R π.irr π.S π.irrS hfin hrat hcont⟩`.
-/
theorem exists_dict : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n),
    ∃ U, Dict F π U := by
  intro L _ _ _ n F π
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  obtain ⟨R, hfin, hrat, hcont⟩ := GlobalTheory.T.exists_adelic_extension_of_algebraicWeight_definiteUnitary L n π.toAlgWt
  exact ⟨_, dict_span F π.ρ R π.irr π.S π.irrS hfin hrat hcont⟩

end GlobalTheory.FormDictEx
