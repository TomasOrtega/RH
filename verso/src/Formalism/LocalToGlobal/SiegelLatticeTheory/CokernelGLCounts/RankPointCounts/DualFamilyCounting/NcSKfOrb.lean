import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSFinVolSk
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSAdTup
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSOmDecomp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.LatHat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RPGlue

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.KfOrbPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol NumberField IsDedekindDomain
  MeasureTheory Topology Filter
open Formalism.L2.SG.Pf.NcS.FinVolSk
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
The claim follows from `(algebraMap F (Af F) x).2`.
-/
theorem ev_int (x : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (algebraMap F (Fv F v) x) ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) x).2

/- English proof (translation)
Establish `h1 : algebraMap F (Fv F v) ((M : F)⁻¹) * algebraMap F (Fv F v) (M : F) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hM), map_one]`. Establish `e : y = (⟨algebraMap F (Fv F v) ((M : F)⁻¹), hMv⟩ : v.adicCompletionIntegers F) • (M • y)` using `by show y = algebraMap F (Fv F v) ((M : F)⁻¹) • (M • y)`. Rewrite using `[← Int.cast_smul_eq_zsmul (Fv F v) M y, smul_smul, ← map_intCast (algebraMap F (Fv F v)) M, h1, one_smul]`. Rewrite using `[e]`.

Conclude with `S.smul_mem _ hy`.
-/
theorem int_smul_mem {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (M : ℤ) (hM : M ≠ 0)
    (hMv : algebraMap F (Fv F v) ((M : F)⁻¹) ∈ v.adicCompletionIntegers F)
    (S : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v ⊗[F] E)) (y : Fin n → Fv F v ⊗[F] E)
    (hy : M • y ∈ S) : y ∈ S := by
  have h1 : algebraMap F (Fv F v) ((M : F)⁻¹) * algebraMap F (Fv F v) (M : F) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hM), map_one]
  have e : y = (⟨algebraMap F (Fv F v) ((M : F)⁻¹), hMv⟩ : v.adicCompletionIntegers F) • (M • y) := by
    show y = algebraMap F (Fv F v) ((M : F)⁻¹) • (M • y)
    rw [← Int.cast_smul_eq_zsmul (Fv F v) M y, smul_smul, ← map_intCast (algebraMap F (Fv F v)) M, h1, one_smul]
  rw [e]
  exact S.smul_mem _ hy

/- English proof (translation)
Take `⟨N, hN0, hN⟩` from `MassDataMassesW.KCptW.std_mult L hL.span_eq_top`. Take `⟨N', hN'0, hN'⟩` from `MassDataMassesW.KCptW.lat_mult L hL.fg`. Use `filter_upwards [ev_int ((N : F)⁻¹), ev_int ((N' : F)⁻¹)] with v hv hv'`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`.

Conclude with `int_smul_mem v N' hN'0 hv' _ y (MassDataMassesW.KCptW.zsmul_mem_latLoc_of _ _ N' hN' v hy)`. Introduce `y hy`. Conclude with `int_smul_mem v N hN0 hv _ y (MassDataMassesW.KCptW.zsmul_mem_latLoc_of _ _ N hN v hy)`.
-/
theorem ev_latLoc_std {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, latLoc (E := E) v (L : Set (Fin n → E)) =
      latLoc (E := E) v ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  obtain ⟨N, hN0, hN⟩ := MassDataMassesW.KCptW.std_mult L hL.span_eq_top
  obtain ⟨N', hN'0, hN'⟩ := MassDataMassesW.KCptW.lat_mult L hL.fg
  filter_upwards [ev_int ((N : F)⁻¹), ev_int ((N' : F)⁻¹)] with v hv hv'
  apply le_antisymm
  · intro y hy
    exact int_smul_mem v N' hN'0 hv' _ y (MassDataMassesW.KCptW.zsmul_mem_latLoc_of _ _ N' hN' v hy)
  · intro y hy
    exact int_smul_mem v N hN0 hv _ y (MassDataMassesW.KCptW.zsmul_mem_latLoc_of _ _ N hN v hy)

/- English proof (translation)
Use `show y i ∈ Submodule.span (v.adicCompletionIntegers F) ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨μ, hμ, rfl⟩` from `hz`. Take `⟨o, ho⟩` from `LinearMap.mem_range.1 ((Submodule.mem_pi.1 hμ) i (Set.mem_univ _))`.

Use `show inclR (Fv F v) (μ i) ∈ _`. Rewrite using `[← ho]`. Conclude with `Submodule.subset_span ⟨o, trivial, rfl⟩`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => exact Submodule.add_mem _ ha hb`.

Consider the case `smul c a _ ha => exact Submodule.smul_mem _ c ha`.
-/
theorem mem_oev_of_std {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E)
    (hy : y ∈ latLoc (E := E) v
      ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E))) (i : Fin n) :
    y i ∈ OEv (E := E) v := by
  show y i ∈ Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨μ, hμ, rfl⟩ := hz
    obtain ⟨o, ho⟩ := LinearMap.mem_range.1 ((Submodule.mem_pi.1 hμ) i (Set.mem_univ _))
    show inclR (Fv F v) (μ i) ∈ _
    rw [← ho]
    exact Submodule.subset_span ⟨o, trivial, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

/- English proof (translation)
Establish `he : ratV (F` using `F) (Fv F v) (Pi.single j (1 : E)) ∈ latLoc (E := E) v ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := Submodule.subset_span ⟨_, MassDataMassesW.KCptW.single_mem_std j, rfl⟩`. Establish `h2` using `(hg _).1 he`. Establish `e1 : ratV (F` using `F) (Fv F v) (Pi.single j (1 : E)) = Pi.single j 1 := by`. Use function extensionality and compare the values at `k`. Distinguish the cases in `h : k = j`.

Substitute `h` using the available equality. Simplify using `[ratV, inclR, Algebra.TensorProduct.one_def]`. Simplify using `[ratV, inclR, Pi.single_apply, h]`. Rewrite `h2` using `[e1]`. Establish `h3` using `mem_oev_of_std v _ h2 i`.

Simplify `h3` using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem entries_oev {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (Fv F v ⊗[F] E))
    (hg : g ∈ Kloc (E := E) v ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)))
    (i j : Fin n) : (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v := by
  classical
  have he : ratV (F := F) (Fv F v) (Pi.single j (1 : E)) ∈ latLoc (E := E) v
      ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) :=
    Submodule.subset_span ⟨_, MassDataMassesW.KCptW.single_mem_std j, rfl⟩
  have h2 := (hg _).1 he
  have e1 : ratV (F := F) (Fv F v) (Pi.single j (1 : E)) = Pi.single j 1 := by
    funext k
    by_cases h : k = j
    · subst h; simp [ratV, inclR, Algebra.TensorProduct.one_def]
    · simp [ratV, inclR, Pi.single_apply, h]
  rw [e1] at h2
  have h3 := mem_oev_of_std v _ h2 i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h3

variable [FiniteDimensional F E]

/- English proof (translation)
Set `B` to `NumberField.RingOfIntegers.basis E`. Use `filter_upwards [eventually_all.2 fun t => eventually_all.2 fun l => ev_int (F := F) (b.repr ((B t : 𝓞 E) : E) l)] with v hv`. Establish `hgen : ∀ (o : 𝓞 E) (l : Fin d), PI.VolStabS.PositiveNearLattice.crd b (Fv F v) (inclR (F` using `F) (Fv F v) (o : E)) l ∈ v.adicCompletionIntegers F := by`. Introduce `o l`. Establish `hcrd : ∀ e : E, PI.VolStabS.PositiveNearLattice.crd b (Fv F v) (inclR (F` using `F) (Fv F v) e) l = algebraMap F (Fv F v) (b.repr e l) := by`.

Introduce `e`. Simplify using `[PI.VolStabS.PositiveNearLattice.crd, inclR, Algebra.TensorProduct.basis_repr_tmul]`. Rewrite using `[hcrd]`. Establish `ho : (o : E) = ∑ t, (B.repr o t) • ((B t : 𝓞 E) : E)`. Use `congrArg (algebraMap (𝓞 E) E) (B.sum_repr o)` as an intermediate fact.

Rewrite `this` using `[map_sum]`. Simplify `this.symm` using `[map_zsmul]`. Rewrite using `[ho, map_sum, Finsupp.finset_sum_apply, map_sum]`. Use `Subring.sum_mem _ fun t _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, Finsupp.smul_apply, map_zsmul]`.

Conclude with `Subring.zsmul_mem _ (hv t l) _`. Introduce `z hz l`. Express the relevant statement in the definitionally equal form `z ∈ Submodule.span (v.adicCompletionIntegers F) ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨o, -, rfl⟩` from `hy`. Conclude with `hgen o l`. Consider the case `zero => simp [PI.VolStabS.PositiveNearLattice.crd]`. Consider the case `add a c _ _ ha hc`. Simplify using `only [PI.VolStabS.PositiveNearLattice.crd, map_add, Finsupp.add_apply] at *`.

Conclude with `Subring.add_mem _ ha hc`. Consider the case `smul c a _ ha`. Establish `e : PI.VolStabS.PositiveNearLattice.crd b (Fv F v) (c • a) l = (c : Fv F v) * PI.VolStabS.PositiveNearLattice.crd b (Fv F v) a l` using `by show (Algebra.TensorProduct.basis (Fv F v) b).repr ((c : Fv F v) • a) l = _`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `Subring.mul_mem _ c.2 ha`.
-/
theorem ev_crd_oev {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ z ∈ OEv (E := E) v, ∀ l,
      PI.VolStabS.PositiveNearLattice.crd b (Fv F v) z l ∈ v.adicCompletionIntegers F := by
  classical
  let B := NumberField.RingOfIntegers.basis E
  filter_upwards [eventually_all.2 fun t => eventually_all.2 fun l =>
    ev_int (F := F) (b.repr ((B t : 𝓞 E) : E) l)] with v hv
  have hgen : ∀ (o : 𝓞 E) (l : Fin d),
      PI.VolStabS.PositiveNearLattice.crd b (Fv F v) (inclR (F := F) (Fv F v) (o : E)) l ∈
        v.adicCompletionIntegers F := by
    intro o l
    have hcrd : ∀ e : E, PI.VolStabS.PositiveNearLattice.crd b (Fv F v) (inclR (F := F) (Fv F v) e) l =
        algebraMap F (Fv F v) (b.repr e l) := by
      intro e
      simp [PI.VolStabS.PositiveNearLattice.crd, inclR, Algebra.TensorProduct.basis_repr_tmul]
    rw [hcrd]
    have ho : (o : E) = ∑ t, (B.repr o t) • ((B t : 𝓞 E) : E) := by
      have := congrArg (algebraMap (𝓞 E) E) (B.sum_repr o)
      rw [map_sum] at this
      simpa [map_zsmul] using this.symm
    rw [ho, map_sum, Finsupp.finset_sum_apply, map_sum]
    refine Subring.sum_mem _ fun t _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact Subring.zsmul_mem _ (hv t l) _
  intro z hz l
  change z ∈ Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨o, -, rfl⟩ := hy
    exact hgen o l
  | zero => simp [PI.VolStabS.PositiveNearLattice.crd]
  | add a c _ _ ha hc =>
    simp only [PI.VolStabS.PositiveNearLattice.crd, map_add, Finsupp.add_apply] at *
    exact Subring.add_mem _ ha hc
  | smul c a _ ha =>
    have e : PI.VolStabS.PositiveNearLattice.crd b (Fv F v) (c • a) l =
        (c : Fv F v) * PI.VolStabS.PositiveNearLattice.crd b (Fv F v) a l := by
      show (Algebra.TensorProduct.basis (Fv F v) b).repr ((c : Fv F v) • a) l = _
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl
    rw [e]
    exact Subring.mul_mem _ c.2 ha

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem projV_eq_map (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (X : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :
    projV v X = X.map (tensMap (E := E) (evalV F v)) := rfl

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J a X0 Λ hCM hJ hLat`. Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Take `⟨L, hL, rfl⟩` from `hLat`. Set `b` to `Module.finBasis F E`. Use `set Y := ratTup (F := F) (Af F) X0 with hYdef`.

Take `⟨hKc, -⟩` from `Formalism.L2.SG.Pf.NcS.AdTupPf.kf_compact_open σ J L hL`. Establish `hmat : Continuous (fun g : HA (Af F) σ J => ((HA.mat (Af F) σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)))` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hact : Continuous (fun g : HA (Af F) σ J => g • Y)`. Use `continuous_pi fun c => ?_` and prove the remaining obligations. Use `show Continuous (fun g : HA (Af F) σ J => ((HA.mat (Af F) σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).mulVec (Y c))`.

Conclude with `hmat.matrix_mulVec continuous_const`. Establish `hcomp : ∀ (v : HeightOneSpectrum (𝓞 F)) (g : HA (Af F) σ J), projV v (g • Y) = (((HA.mat (Af F) σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).map (tensMap (E` using `E) (evalV F v))).mulVec ∘ (fun c => ratTup (F := F) (Fv F v) X0 c) := by`. Introduce `v g`. Use function extensionality and compare the values at `c i`. Express the relevant statement in the definitionally equal form `tensMap (E := E) (evalV F v) (((HA.mat (Af F) σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).mulVec (Y c) i) = _`.

Rewrite using `[RingHom.map_mulVec]`. Use `congr 1`. Use `⟨?_, fun x => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `: T2Space (Af F ⊗[F] E)` using `PI.VolStabS.RestrProdG.t2_tensor_product (Af F)`. Establish `e : {x : Fin a → Fin n → Af F ⊗[F] E | ∃ k ∈ Kf σ J (L : Set (Fin n → E)), x = k • ratTup (Af F) X0} = (fun g : HA (Af F) σ J => g • Y) '' (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J))`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨k, hk, rfl⟩`. Introduce and unpack `⟨k, hk, rfl⟩`.

Conclude with `⟨k, hk, rfl⟩`. Rewrite using `[e]`. Conclude with `(hKc.image hact).isClosed.measurableSet`. Introduce and unpack `⟨k, hk, rfl⟩ v`. Use `⟨haMap σ J (evalV F v) k, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : k ∈ (Kloc (E` using `E) v (L : Set (Fin n → E))).comap ((compV v).comp (incAf σ J)) := (Subgroup.mem_iInf.1 hk) v`. Conclude with `h1`. Rewrite using `[hcomp v k]`. Both sides reduce to the same expression. Introduce `hx`.

Use `choose kv hkv hxv using hx`. Establish `hgoodV : ∀ᶠ v in cofinite, ∀ g : GL (Fin n) (Fv F v ⊗[F] E), g ∈ Kloc (E` using `E) v (L : Set (Fin n → E)) → (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ∈ latV (M := n) (n := n) b v := by filter_upwards [ev_latLoc_std L hL, ev_crd_oev b] with v hv hc`. Introduce `g hg i j l`. Establish `hg' : g ∈ Kloc (E` using `E) v ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by`. Introduce `y`.

Rewrite using `[← hv]`. Conclude with `hg y`. Conclude with `hc _ (entries_oev v g hg' i j) l`. Set `mat : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)` to `fun v => ((HA.mat (Fv F v) σ J (kv v) : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))`. Set `imat : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)` to `fun v => (((HA.mat (Fv F v) σ J (kv v))⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))`.

Establish `hK1 : ∀ v, HA.mat (Fv F v) σ J (kv v) ∈ Kloc (E` using `E) v (L : Set (Fin n → E)) := hkv`. Establish `hg1 : ∀ᶠ v in cofinite, mat v ∈ latV b v` using `hgoodV.mono fun v h => h _ (hK1 v)`. Establish `hg2 : ∀ᶠ v in cofinite, imat v ∈ latV b v` using `hgoodV.mono fun v h => h _ ((Kloc (E := E) v (L : Set (Fin n → E))).inv_mem (hK1 v))`. Take `⟨Γ, -, hΓ⟩` from `PI.VolStabS.rpGlue_holds F E n n _ b`. Set `A : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)` to `projFin (Γ (0, mat))`.

Set `A' : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)` to `projFin (Γ (0, imat))`. Establish `hA : ∀ v, A.map (tensMap (E` using `E) (evalV F v)) = mat v := (hΓ (0, mat) hg1).2`. Establish `hA' : ∀ v, A'.map (tensMap (E` using `E) (evalV F v)) = imat v := (hΓ (0, imat) hg2).2`. Establish `hAA' : A * A' = 1`. Use `Formalism.L2.SG.Pf.NcS.OmDecompPf.projV_ext b fun v => ?_` and prove the remaining obligations.

Rewrite using `[projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hA']`. Conclude with `Units.mul_inv (HA.mat (Fv F v) σ J (kv v))`. Establish `hA'A : A' * A = 1`. Use `Formalism.L2.SG.Pf.NcS.OmDecompPf.projV_ext b fun v => ?_` and prove the remaining obligations. Rewrite using `[projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hA']`.

Conclude with `Units.inv_mul (HA.mat (Fv F v) σ J (kv v))`. Set `gGL : GL (Fin n) (Af F ⊗[F] E)` to `⟨A, A', hAA', hA'A⟩`. Establish `hcT : ∀ v (X : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)), (Formalism.UG.cT (sigR (Af F) σ) X).map (tensMap (E` using `E) (evalV F v)) = Formalism.UG.cT (sigR (Fv F v) σ) (X.map (tensMap (E := E) (evalV F v))) := by`. Introduce `v X`. Use extensionality with `i j`.

Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]`. Conclude with `PI.VolStabS.RestrProdG.map_sigR (evalV F v) σ (X j i)`. Establish `hJR : ∀ v, (JR (Af F) J).map (tensMap (E` using `E) (evalV F v)) = JR (Fv F v) J := by`. Introduce `v`. Use extensionality with `i j`.

Conclude with `PI.VolStabS.RestrProdG.map_inclR (evalV F v) (J i j)`. Establish `hmem : gGL ∈ HR (Af F) σ J` using `by show Formalism.UG.cT (sigR (Af F) σ) A * JR (Af F) J * A = JR (Af F) J`. Use `Formalism.L2.SG.Pf.NcS.OmDecompPf.projV_ext b fun v => ?_` and prove the remaining obligations. Rewrite using `[projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_mul, hcT, hJR, hA]`. Conclude with `(kv v).2`.

Set `k : HA (Af F) σ J` to `(⟨gGL, hmem⟩ : HR (Af F) σ J)`. Use `⟨k, ?_, ?_⟩` and prove the remaining obligations. Use `Subgroup.mem_iInf.2 fun v => ?_ show ∀ y, y ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔ Matrix.mulVec (((compV v (incAf σ J k)) : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) y ∈ latLoc (E := E) v (L : Set (Fin n → E))` and prove the remaining obligations. Establish `e : (((compV v (incAf σ J k)) : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = mat v` using `hA v`. Rewrite using `[e]`.

Conclude with `hK1 v`. Use `Formalism.L2.SG.Pf.NcS.OmDecompPf.projV_ext b fun v => ?_` and prove the remaining obligations. Rewrite using `[hxv v, hcomp v k]`. Establish `e : (((HA.mat (Af F) σ J k : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).map (tensMap (E` using `E) (evalV F v))) = mat v := hA v`. Rewrite using `[e]`.

Both sides reduce to the same expression.
-/
theorem finite_orbit_holds : KfOrb := by
  intro F E _ _ _ _ _ σ n J a X0 Λ hCM hJ hLat
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hL, rfl⟩ := hLat
  let b := Module.finBasis F E
  set Y := ratTup (F := F) (Af F) X0 with hYdef
  obtain ⟨hKc, -⟩ := Formalism.L2.SG.Pf.NcS.AdTupPf.kf_compact_open σ J L hL
  have hmat : Continuous (fun g : HA (Af F) σ J =>
      ((HA.mat (Af F) σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  have hact : Continuous (fun g : HA (Af F) σ J => g • Y) := by
    refine continuous_pi fun c => ?_
    show Continuous (fun g : HA (Af F) σ J =>
      ((HA.mat (Af F) σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).mulVec (Y c))
    exact hmat.matrix_mulVec continuous_const

  have hcomp : ∀ (v : HeightOneSpectrum (𝓞 F)) (g : HA (Af F) σ J),
      projV v (g • Y) = (((HA.mat (Af F) σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).map
        (tensMap (E := E) (evalV F v))).mulVec ∘ (fun c => ratTup (F := F) (Fv F v) X0 c) := by
    intro v g
    funext c i
    change tensMap (E := E) (evalV F v)
        (((HA.mat (Af F) σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).mulVec (Y c) i) = _
    rw [RingHom.map_mulVec]
    congr 1
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  ·
    have : T2Space (Af F ⊗[F] E) := PI.VolStabS.RestrProdG.t2_tensor_product (Af F)
    have e : {x : Fin a → Fin n → Af F ⊗[F] E | ∃ k ∈ Kf σ J (L : Set (Fin n → E)), x = k • ratTup (Af F) X0} =
        (fun g : HA (Af F) σ J => g • Y) '' (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J)) := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
    rw [e]
    exact (hKc.image hact).isClosed.measurableSet
  ·
    rintro ⟨k, hk, rfl⟩ v
    refine ⟨haMap σ J (evalV F v) k, ?_, ?_⟩
    · have h1 : k ∈ (Kloc (E := E) v (L : Set (Fin n → E))).comap ((compV v).comp (incAf σ J)) :=
        (Subgroup.mem_iInf.1 hk) v
      exact h1
    · rw [hcomp v k]
      rfl
  ·
    intro hx
    choose kv hkv hxv using hx
    have hgoodV : ∀ᶠ v in cofinite, ∀ g : GL (Fin n) (Fv F v ⊗[F] E),
        g ∈ Kloc (E := E) v (L : Set (Fin n → E)) →
          (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ∈ latV (M := n) (n := n) b v := by
      filter_upwards [ev_latLoc_std L hL, ev_crd_oev b] with v hv hc
      intro g hg i j l
      have hg' : g ∈ Kloc (E := E) v
          ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
        intro y; rw [← hv]; exact hg y
      exact hc _ (entries_oev v g hg' i j) l
    let mat : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := fun v =>
      ((HA.mat (Fv F v) σ J (kv v) : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    let imat : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := fun v =>
      (((HA.mat (Fv F v) σ J (kv v))⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    have hK1 : ∀ v, HA.mat (Fv F v) σ J (kv v) ∈ Kloc (E := E) v (L : Set (Fin n → E)) := hkv
    have hg1 : ∀ᶠ v in cofinite, mat v ∈ latV b v :=
      hgoodV.mono fun v h => h _ (hK1 v)
    have hg2 : ∀ᶠ v in cofinite, imat v ∈ latV b v :=
      hgoodV.mono fun v h => h _ ((Kloc (E := E) v (L : Set (Fin n → E))).inv_mem (hK1 v))
    obtain ⟨Γ, -, hΓ⟩ := PI.VolStabS.rpGlue_holds F E n n _ b
    let A : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) := projFin (Γ (0, mat))
    let A' : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) := projFin (Γ (0, imat))
    have hA : ∀ v, A.map (tensMap (E := E) (evalV F v)) = mat v := (hΓ (0, mat) hg1).2
    have hA' : ∀ v, A'.map (tensMap (E := E) (evalV F v)) = imat v := (hΓ (0, imat) hg2).2
    have hAA' : A * A' = 1 := by
      refine Formalism.L2.SG.Pf.NcS.OmDecompPf.projV_ext b fun v => ?_
      rw [projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hA']
      exact Units.mul_inv (HA.mat (Fv F v) σ J (kv v))
    have hA'A : A' * A = 1 := by
      refine Formalism.L2.SG.Pf.NcS.OmDecompPf.projV_ext b fun v => ?_
      rw [projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hA']
      exact Units.inv_mul (HA.mat (Fv F v) σ J (kv v))
    let gGL : GL (Fin n) (Af F ⊗[F] E) := ⟨A, A', hAA', hA'A⟩
    have hcT : ∀ v (X : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)),
        (Formalism.UG.cT (sigR (Af F) σ) X).map (tensMap (E := E) (evalV F v)) =
          Formalism.UG.cT (sigR (Fv F v) σ) (X.map (tensMap (E := E) (evalV F v))) := by
      intro v X
      ext i j
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
      exact PI.VolStabS.RestrProdG.map_sigR (evalV F v) σ (X j i)
    have hJR : ∀ v, (JR (Af F) J).map (tensMap (E := E) (evalV F v)) = JR (Fv F v) J := by
      intro v
      ext i j
      exact PI.VolStabS.RestrProdG.map_inclR (evalV F v) (J i j)
    have hmem : gGL ∈ HR (Af F) σ J := by
      show Formalism.UG.cT (sigR (Af F) σ) A * JR (Af F) J * A = JR (Af F) J
      refine Formalism.L2.SG.Pf.NcS.OmDecompPf.projV_ext b fun v => ?_
      rw [projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_mul, hcT, hJR, hA]
      exact (kv v).2
    let k : HA (Af F) σ J := (⟨gGL, hmem⟩ : HR (Af F) σ J)
    refine ⟨k, ?_, ?_⟩
    · refine Subgroup.mem_iInf.2 fun v => ?_
      show ∀ y, y ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
        Matrix.mulVec (((compV v (incAf σ J k)) : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) y ∈ latLoc (E := E) v (L : Set (Fin n → E))
      have e : (((compV v (incAf σ J k)) : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = mat v := hA v
      rw [e]
      exact hK1 v
    · refine Formalism.L2.SG.Pf.NcS.OmDecompPf.projV_ext b fun v => ?_
      rw [hxv v, hcomp v k]
      have e : (((HA.mat (Af F) σ J k : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).map
          (tensMap (E := E) (evalV F v))) = mat v := hA v
      rw [e]
      rfl

end Formalism.L2.SG.Pf.NcS.KfOrbPf
