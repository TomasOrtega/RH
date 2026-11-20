import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsSemisimpleOfISupEigenspace
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeSemis

open Module

section Lin

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p r hp hr => rw [Polynomial.map_add, map_add, hp, hr, map_add, LinearMap.baseChange_add]`. Consider the case `monomial k c`. Rewrite using `[Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← LinearMap.baseChange_pow]`. Apply `TensorProduct.AlgebraTensorModule.curry_injective` to reduce the goal to its premises.

Use extensionality with `x`. Simplify using `[Module.algebraMap_end_apply, LinearMap.baseChange_tmul]`.
-/
theorem aeval_baseChange_map (L : Type) [Field L] [Algebra K L] (f : Module.End K V) (p : K[X]) :
    aeval (f.baseChange L) (p.map (algebraMap K L)) = (aeval f p).baseChange L := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [Polynomial.map_add, map_add, hp, hr, map_add, LinearMap.baseChange_add]
  | monomial k c =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← LinearMap.baseChange_pow]
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext x
    simp [Module.algebraMap_end_apply, LinearMap.baseChange_tmul]

/- English proof (translation)
Establish `hsep : (minpoly K f).Separable` using `PerfectField.separable_iff_squarefree.2 hsq`. Apply `Module.End.isSemisimple_of_squarefree_aeval_eq_zero (hsep.map (f := algebraMap K L)).squarefree` to reduce the goal to its premises. Rewrite using `[aeval_baseChange_map, minpoly.aeval, LinearMap.baseChange_zero]`.
-/
theorem isSemisimple_baseChange [CharZero K] [FiniteDimensional K V] (f : Module.End K V)
    (hsq : Squarefree (minpoly K f)) (L : Type) [Field L] [Algebra K L] :
    Module.End.IsSemisimple (f.baseChange L) := by
  have hsep : (minpoly K f).Separable := PerfectField.separable_iff_squarefree.2 hsq
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero (hsep.map (f := algebraMap K L)).squarefree
  rw [aeval_baseChange_map, minpoly.aeval, LinearMap.baseChange_zero]

variable {U : Type} [AddCommGroup U] [Module ℂ U] {σ : K →+* ℂ} (φ : V →ₛₗ[σ] U) (T : Module.End K V)
  (S : Module.End ℂ U) (h : ∀ x, φ (T x) = S (φ x))
include h

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ', Module.End.mul_apply, h, ih, pow_succ', Module.End.mul_apply]`.
-/
theorem map_pow_apply (n : ℕ) (x : V) : φ ((T ^ n) x) = (S ^ n) (φ x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, h, ih, pow_succ', Module.End.mul_apply]

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Rewrite using `[map_add, LinearMap.add_apply, map_add, hp, hq, Polynomial.map_add, map_add, LinearMap.add_apply]`. Consider the case `monomial n c`. Rewrite using `[aeval_monomial, Polynomial.map_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearMap.map_smulₛₗ, map_pow_apply φ T S h]`.
-/
theorem map_aeval_apply (p : K[X]) (x : V) : φ (aeval T p x) = aeval S (p.map σ) (φ x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, map_add, hp, hq, Polynomial.map_add, map_add, LinearMap.add_apply]
  | monomial n c =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearMap.map_smulₛₗ, map_pow_apply φ T S h]

end Lin

end GlobalTheory.HeckeSemis

noncomputable section

namespace GlobalTheory.HeckeSemis

open Module

variable {U : Type} [AddCommGroup U] [Module ℂ U]

/- English proof (translation)
Apply `GlobalTheory.WeilDeligne.isSemisimple_of_iSup_eigenspace` to reduce the goal to its premises. Rewrite using `[eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top S]`. Use `iSup_mono fun μ => ?_` and prove the remaining obligations. Introduce `u hu`. Establish `hA : ∀ v, (S - μ • 1 : Module.End ℂ U) ((S - μ • 1 : Module.End ℂ U) v) = 0 → (S - μ • 1 : Module.End ℂ U) v = 0`.

Introduce `v hv`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv ⊢`. Rewrite `hv`, the goal using `[sub_eq_zero]`. Conclude with `h μ v hv`. Establish `step : ∀ k v, ((S - μ • 1 : Module.End ℂ U) ^ (k + 1)) v = 0 → (S - μ • 1 : Module.End ℂ U) v = 0`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro v hv`. Simplify using `using hv`. Consider the case `succ k ih`.

Introduce `v hv`. Apply `ih` to reduce the goal to its premises. Establish `e1 : ((S - μ • 1 : Module.End ℂ U) ^ (k + 1 + 1)) v = (S - μ • 1 : Module.End ℂ U) ((S - μ • 1 : Module.End ℂ U) (((S - μ • 1 : Module.End ℂ U) ^ k) v))`. Rewrite using `[pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]`. Establish `e2 : ((S - μ • 1 : Module.End ℂ U) ^ (k + 1)) v = (S - μ • 1 : Module.End ℂ U) (((S - μ • 1 : Module.End ℂ U) ^ k) v)`.

Rewrite using `[pow_succ', Module.End.mul_apply]`. Rewrite using `[e2]`. Conclude with `hA _ (e1 ▸ hv)`. Rewrite `hu` using `[Module.End.mem_maxGenEigenspace]`. Take `⟨k, hk⟩` from `hu`.

Rewrite using `[Module.End.mem_eigenspace_iff]`. Establish `hz : (S - μ • 1 : Module.End ℂ U) u = 0`. Consider the cases of `k with`. Consider the case `zero => simp at hk`. Simplify using `[hk]`.

Consider the case `succ k => exact step k u hk`. Simplify `hz` using `[sub_eq_zero]`.
-/
theorem isSemisimple_of_sq [FiniteDimensional ℂ U] (S : Module.End ℂ U)
    (h : ∀ (μ : ℂ) (u : U), S (S u - μ • u) = μ • (S u - μ • u) → S u = μ • u) : S.IsSemisimple := by
  apply GlobalTheory.WeilDeligne.isSemisimple_of_iSup_eigenspace
  rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top S]
  refine iSup_mono fun μ => ?_
  intro u hu
  have hA : ∀ v, (S - μ • 1 : Module.End ℂ U) ((S - μ • 1 : Module.End ℂ U) v) = 0 → (S - μ • 1 : Module.End ℂ U) v = 0 := by
    intro v hv
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv ⊢
    rw [sub_eq_zero] at hv ⊢
    exact h μ v hv
  have step : ∀ k v, ((S - μ • 1 : Module.End ℂ U) ^ (k + 1)) v = 0 → (S - μ • 1 : Module.End ℂ U) v = 0 := by
    intro k
    induction k with
    | zero => intro v hv; simpa using hv
    | succ k ih =>
      intro v hv
      apply ih
      have e1 : ((S - μ • 1 : Module.End ℂ U) ^ (k + 1 + 1)) v =
          (S - μ • 1 : Module.End ℂ U) ((S - μ • 1 : Module.End ℂ U) (((S - μ • 1 : Module.End ℂ U) ^ k) v)) := by
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      have e2 : ((S - μ • 1 : Module.End ℂ U) ^ (k + 1)) v =
          (S - μ • 1 : Module.End ℂ U) (((S - μ • 1 : Module.End ℂ U) ^ k) v) := by
        rw [pow_succ', Module.End.mul_apply]
      rw [e2]
      exact hA _ (e1 ▸ hv)
  rw [Module.End.mem_maxGenEigenspace] at hu
  obtain ⟨k, hk⟩ := hu
  rw [Module.End.mem_eigenspace_iff]
  have hz : (S - μ • 1 : Module.End ℂ U) u = 0 := by
    cases k with
    | zero => simp at hk; simp [hk]
    | succ k => exact step k u hk
  simpa [sub_eq_zero] using hz

/- English proof (translation)
Establish `h1 : u ∈ A.maxGenEigenspace 0`. Rewrite using `[Module.End.mem_maxGenEigenspace]`. Conclude with `⟨2, by simpa [pow_two] using hu⟩`. Rewrite `h1` using `[hA.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, Module.End.mem_eigenspace_iff]`. Simplify using `using h1`.
-/
theorem apply_eq_zero_of_sq [FiniteDimensional ℂ U] {A : Module.End ℂ U} (hA : A.IsSemisimple) {u : U}
    (hu : A (A u) = 0) : A u = 0 := by
  have h1 : u ∈ A.maxGenEigenspace 0 := by
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨2, by simpa [pow_two] using hu⟩
  rw [hA.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, Module.End.mem_eigenspace_iff] at h1
  simpa using h1

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* ℂ}

/- English proof (translation)
Introduce `p hp`. Take `⟨r, hr⟩` from `hp`. Establish `key : aeval T (p * r) = 0`. Use extensionality with `x`. Establish `hm : aeval T (minpoly K T) = 0` using `minpoly.aeval K T`.

Rewrite `hm` using `[hr]`. Establish `h0 : aeval T p (aeval T p (aeval T r x)) = 0`. Use `LinearMap.congr_fun hm x` as an intermediate fact. Simplify `this` using `[map_mul, Module.End.mul_apply]`. Establish `h1 : aeval S (p.map σ) (aeval S (p.map σ) (φ (aeval T r x))) = 0`.

Rewrite using `[← map_aeval_apply φ T S h, ← map_aeval_apply φ T S h, h0, map_zero]`. Establish `h2` using `apply_eq_zero_of_sq (hS.aeval (p.map σ)) h1`. Rewrite `h2` using `[← map_aeval_apply φ T S h]`. Establish `h3 : aeval T p (aeval T r x) = 0` using `hφ (by rw [h2, map_zero])`. Simplify `h3` using `[map_mul, Module.End.mul_apply]`.

Establish `hdvd` using `minpoly.dvd K T key`. Establish `hm0 : minpoly K T ≠ 0` using `minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)`. Rewrite `hdvd`, `hm0` using `[hr]`. Establish `hne : p * r ≠ 0` using `fun h => hm0 (by rw [mul_assoc, h, mul_zero])`. Establish `h3 : p * (p * r) ∣ 1 * (p * r)` using `by rw [one_mul, ← mul_assoc]; exact hdvd`.

Conclude with `isUnit_of_dvd_one ((mul_dvd_mul_iff_right hne).1 h3)`.
-/
theorem squarefree_minpoly [FiniteDimensional K V] [FiniteDimensional ℂ U] (φ : V →ₛₗ[σ] U)
    (hφ : Function.Injective φ) (T : Module.End K V) (S : Module.End ℂ U) (h : ∀ x, φ (T x) = S (φ x))
    (hS : S.IsSemisimple) : Squarefree (minpoly K T) := by
  intro p hp
  obtain ⟨r, hr⟩ := hp
  have key : aeval T (p * r) = 0 := by
    ext x
    have hm : aeval T (minpoly K T) = 0 := minpoly.aeval K T
    rw [hr] at hm
    have h0 : aeval T p (aeval T p (aeval T r x)) = 0 := by
      have := LinearMap.congr_fun hm x
      simpa [map_mul, Module.End.mul_apply] using this
    have h1 : aeval S (p.map σ) (aeval S (p.map σ) (φ (aeval T r x))) = 0 := by
      rw [← map_aeval_apply φ T S h, ← map_aeval_apply φ T S h, h0, map_zero]
    have h2 := apply_eq_zero_of_sq (hS.aeval (p.map σ)) h1
    rw [← map_aeval_apply φ T S h] at h2
    have h3 : aeval T p (aeval T r x) = 0 := hφ (by rw [h2, map_zero])
    simpa [map_mul, Module.End.mul_apply] using h3
  have hdvd := minpoly.dvd K T key
  have hm0 : minpoly K T ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
  rw [hr] at hdvd hm0
  have hne : p * r ≠ 0 := fun h => hm0 (by rw [mul_assoc, h, mul_zero])
  have h3 : p * (p * r) ∣ 1 * (p * r) := by rw [one_mul, ← mul_assoc]; exact hdvd
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hne).1 h3)

end GlobalTheory.HeckeSemis

namespace GlobalTheory.HeckeLocN

open Module

/- English proof (translation)
Establish `hli` using `(D.what₂.jMt_basis μ j (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j))).1`. Use `haveI := hli.finite`. Conclude with `Module.Finite.of_basis (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j))`.
-/
theorem finiteDimensional_MtL (D : D7) (μ : D.what₂.Tup) (j : ℕ) : FiniteDimensional D.what₂.LL (D.what₂.MtL μ j) := by
  have hli := (D.what₂.jMt_basis μ j (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j))).1
  haveI := hli.finite
  exact Module.Finite.of_basis (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j))

/- English proof (translation)
Use `set b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j)`. Establish `hli` using `(D.what₂.jMt_basis μ j b).1`. Use `haveI := hli.finite`. Use `haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Establish `e : D.what₂.jMt μ j x = ∑ i, D.what₂.embLL (b.repr x i) • D.what₂.jMt μ j (b i)` using `by conv_lhs => rw [← b.sum_repr x]`. Rewrite using `[map_sum]`. Simplify using `[LinearMap.map_smulₛₗ]`. Rewrite `hx` using `[e]`.

Establish `hc` using `Fintype.linearIndependent_iff.1 hli _ hx`. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Simplify using `using hc i`.
-/
theorem jMt_injective (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  classical
  set b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j)
  have hli := (D.what₂.jMt_basis μ j b).1
  haveI := hli.finite
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))
  rw [injective_iff_map_eq_zero]
  intro x hx
  have e : D.what₂.jMt μ j x = ∑ i, D.what₂.embLL (b.repr x i) • D.what₂.jMt μ j (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    simp [LinearMap.map_smulₛₗ]
  rw [e] at hx
  have hc := Fintype.linearIndependent_iff.1 hli _ hx
  apply b.repr.injective
  ext i
  simpa using hc i

/- English proof (translation)
Introduce `D M C hR X hS hStd hJord hGen hSpl`. Introduce `j w h1 h2 _ v k hg`. Take `⟨B, hBO, hBv⟩` from `hGen w j h1 h2`. Take `⟨s, ϖ, hc, hu⟩` from `hSpl v hg.1`. Establish `hsB : s.v ∉ B` using `hBv v k s hg hc`.

Establish `hst` using `hStd D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J (M (D.what₂.muTw w) j h1 h2).χ B (M (D.what₂.muTw w) j h1 h2).J_open hBO s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2`. Establish `hjo` using `hJord D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J (M (D.what₂.muTw w) j h1 h2).χ B (M (D.what₂.muTw w) j h1 h2).J_open hBO s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2`. Use `set Mr := M (D.what₂.muTw w) j h1 h2 with hMr`. Establish `t0 : NG.tN Mr.J s ϖ k (0 : GAf D.host.E D.R.nV → Mr.wt.W) = 0`. Establish `e` using `hst.2.1 0 (zero_mem _) 0 (zero_mem _) 1`.

Simplify using `only [one_smul, add_zero] at e`. Conclude with `left_eq_add.mp e`. Set `S : Module.End ℂ (NG.TypeSp Mr.wt.ρ Mr.J Mr.χ)` to `{ toFun := fun f => ⟨NG.tN Mr.J s ϖ k f, hst.1 f f.2⟩ map_add' := fun f g => Subtype.ext (by simpa using hst.2.1 f f.2 g g.2 1) map_smul' := fun c f => Subtype.ext (by`. Establish `e` using `hst.2.1 f f.2 0 (zero_mem _) c`. Simplify `e) }` using `[t0]`.

Use `haveI : FiniteDimensional ℂ (NG.TypeSp Mr.wt.ρ Mr.J Mr.χ) := by`. Rewrite using `[← Mr.real_range]`. Use `infer_instance`. Use `haveI := finiteDimensional_MtL D (D.what₂.muTw w) j`. Establish `hmem : ∀ x, Mr.real (D.what₂.jMt (D.what₂.muTw w) j x) ∈ NG.TypeSp Mr.wt.ρ Mr.J Mr.χ` using `fun x => by`.

Rewrite using `[← Mr.real_range]`. Conclude with `LinearMap.mem_range_self _ _`. Set `φ : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[D.what₂.embLL] NG.TypeSp Mr.wt.ρ Mr.J Mr.χ` to `{ toFun := fun x => ⟨Mr.real (D.what₂.jMt _ j x), hmem x⟩ map_add' := fun x y => Subtype.ext (by simp) map_smul' := fun c x => Subtype.ext (by simp [LinearMap.map_smulₛₗ]) }`. Establish `hφ : Function.Injective φ` using `fun x y hxy => jMt_injective D _ j (Mr.real_inj (congrArg Subtype.val hxy))`. Establish `hcomm : ∀ x, φ (hLC (mt0 M) C.Q hR j w v k x) = S (φ x)` using `fun x => Subtype.ext (hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hc hu x)`.

Establish `hSs : S.IsSemisimple` using `GlobalTheory.HeckeSemis.isSemisimple_of_sq S (fun μ u hμ => Subtype.ext (by`. Establish `e : NG.tN Mr.J s ϖ k (↑(S u - μ • u)) = μ • (↑(S u - μ • u) : GAf D.host.E D.R.nV → Mr.wt.W)` using `congrArg Subtype.val hμ`. Rewrite `e` using `[Submodule.coe_sub, Submodule.coe_smul]`. Conclude with `hjo u u.2 μ e))`. Establish `hsq` using `GlobalTheory.HeckeSemis.squarefree_minpoly φ hφ (hLC (mt0 M) C.Q hR j w v k) S hcomm hSs`.

Use `haveI : CharZero D.what₂.LL := RingHom.charZero D.what₂.embLL`. Conclude with `GlobalTheory.HeckeSemis.isSemisimple_baseChange _ hsq (FractionRing (OcC X j w))`.
-/
theorem semisimpleTw_base : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X), HeckeStdPlain → (∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → NG.HypOutside J χ B → ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → IsUnif L s.v ϖ → 1 ≤ k → k ≤ n → ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ μ : ℂ, NG.tN J s ϖ k (NG.tN J s ϖ k f - μ • f) = μ • (NG.tN J s ϖ k f - μ • f) → NG.tN J s ϖ k f = μ • f) → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → SemisimpleTw (base M C hR X hS) := by
  intro D M C hR X hS hStd hJord hGen hSpl
  intro j w h1 h2 _ v k hg
  obtain ⟨B, hBO, hBv⟩ := hGen w j h1 h2
  obtain ⟨s, ϖ, hc, hu⟩ := hSpl v hg.1
  have hsB : s.v ∉ B := hBv v k s hg hc
  have hst := hStd D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J
    (M (D.what₂.muTw w) j h1 h2).χ B (M (D.what₂.muTw w) j h1 h2).J_open hBO s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2
  have hjo := hJord D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J
    (M (D.what₂.muTw w) j h1 h2).χ B (M (D.what₂.muTw w) j h1 h2).J_open hBO s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2
  set Mr := M (D.what₂.muTw w) j h1 h2 with hMr
  have t0 : NG.tN Mr.J s ϖ k (0 : GAf D.host.E D.R.nV → Mr.wt.W) = 0 := by
    have e := hst.2.1 0 (zero_mem _) 0 (zero_mem _) 1
    simp only [one_smul, add_zero] at e
    exact left_eq_add.mp e
  let S : Module.End ℂ (NG.TypeSp Mr.wt.ρ Mr.J Mr.χ) :=
    { toFun := fun f => ⟨NG.tN Mr.J s ϖ k f, hst.1 f f.2⟩
      map_add' := fun f g => Subtype.ext (by simpa using hst.2.1 f f.2 g g.2 1)
      map_smul' := fun c f => Subtype.ext (by
        have e := hst.2.1 f f.2 0 (zero_mem _) c
        simpa [t0] using e) }
  haveI : FiniteDimensional ℂ (NG.TypeSp Mr.wt.ρ Mr.J Mr.χ) := by
    rw [← Mr.real_range]; infer_instance
  haveI := finiteDimensional_MtL D (D.what₂.muTw w) j
  have hmem : ∀ x, Mr.real (D.what₂.jMt (D.what₂.muTw w) j x) ∈ NG.TypeSp Mr.wt.ρ Mr.J Mr.χ := fun x => by
    rw [← Mr.real_range]; exact LinearMap.mem_range_self _ _
  let φ : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[D.what₂.embLL] NG.TypeSp Mr.wt.ρ Mr.J Mr.χ :=
    { toFun := fun x => ⟨Mr.real (D.what₂.jMt _ j x), hmem x⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun c x => Subtype.ext (by simp [LinearMap.map_smulₛₗ]) }
  have hφ : Function.Injective φ := fun x y hxy =>
    jMt_injective D _ j (Mr.real_inj (congrArg Subtype.val hxy))
  have hcomm : ∀ x, φ (hLC (mt0 M) C.Q hR j w v k x) = S (φ x) := fun x =>
    Subtype.ext (hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hc hu x)
  have hSs : S.IsSemisimple := GlobalTheory.HeckeSemis.isSemisimple_of_sq S (fun μ u hμ => Subtype.ext (by
    have e : NG.tN Mr.J s ϖ k (↑(S u - μ • u)) = μ • (↑(S u - μ • u) : GAf D.host.E D.R.nV → Mr.wt.W) :=
      congrArg Subtype.val hμ
    rw [Submodule.coe_sub, Submodule.coe_smul] at e
    exact hjo u u.2 μ e))
  have hsq := GlobalTheory.HeckeSemis.squarefree_minpoly φ hφ (hLC (mt0 M) C.Q hR j w v k) S hcomm hSs
  haveI : CharZero D.what₂.LL := RingHom.charZero D.what₂.embLL
  exact GlobalTheory.HeckeSemis.isSemisimple_baseChange _ hsq (FractionRing (OcC X j w))
end GlobalTheory.HeckeLocN
