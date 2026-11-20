import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSphericalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.HeckeScalarAll

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Introduce `v hv` and use `hx v (fun h' => hv (h h'))`.
-/
theorem trivOutside_mono {T T' : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} (h : T ⊆ T') {x : GAf L n}
    (hx : TrivOutside T x) : TrivOutside T' x := fun v hv => hx v (fun h' => hv (h h'))

/- English proof (translation)
Introduce `v hv`. Establish `e : (((x * y : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * ((y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))` using `rfl`. Rewrite using `[e, Matrix.map_mul, hx v hv, hy v hv, one_mul]`.
-/
theorem trivOutside_mul {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GAf L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro v hv
  have e : (((x * y : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * ((y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [e, Matrix.map_mul, hx v hv, hy v hv, one_mul]

/- English proof (translation)
Introduce `v hv`. Establish `e : (((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1` using `Units.inv_mul x.1`. Establish `h2` using `congrArg (fun M : Matrix (Fin n) (Fin n) (AL L) => M.map (compAt L v)) e`. Simplify using `only [Matrix.map_mul, hx v hv, mul_one] at h2`. Rewrite using `[h2]`.

Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem trivOutside_inv {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GAf L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro v hv
  have e : (((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := Units.inv_mul x.1
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) (AL L) => M.map (compAt L v)) e
  simp only [Matrix.map_mul, hx v hv, mul_one] at h2
  rw [h2]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end Gen

open Classical in
/- English proof (translation)
Use `set φ := fun c : G ⧸ J => if hc : ∃ x ∈ Dset, (x : G ⧸ J) = c then F hc.choose else 0 with hφdef`. Use `set ψ := fun c : G ⧸ U => if hc : ∃ x ∈ Dset, (x : G ⧸ U) = c then F hc.choose else 0 with hψdef`. Establish `hφ : Function.support φ ⊆ (fun x : G => (x : G ⧸ J)) '' Dset`. Introduce `c hc`. Assume the negation of the conclusion as `hn`.

Apply `hc` to reduce the goal to its premises. Simplify using `only [φ]`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `hn ⟨x, hx, rfl⟩`.

Establish `hψ : Function.support ψ ⊆ (fun x : G => (x : G ⧸ U)) '' Dset`. Introduce `c hc`. Assume the negation of the conclusion as `hn`. Apply `hc` to reduce the goal to its premises. Simplify using `only [ψ]`.

Rewrite using `[dif_neg]`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `hn ⟨x, hx, rfl⟩`. Rewrite using `[← Set.indicator_eq_self.2 hφ, ← Set.indicator_eq_self.2 hψ, ← finsum_mem_def, ← finsum_mem_def]`. Set `e : G ⧸ J → G ⧸ U` to `fun c => if hc : ∃ x ∈ Dset, (x : G ⧸ J) = c then (hc.choose : G ⧸ U) else ((1 : G) : G ⧸ U)`.

Use `finsum_mem_eq_of_bijOn e ⟨?_, ?_, ?_⟩ ?_` and prove the remaining obligations. Introduce and unpack `c ⟨x, hx, rfl⟩`. Establish `hc : ∃ y ∈ Dset, (y : G ⧸ J) = (x : G ⧸ J)` using `⟨x, hx, rfl⟩`. Simplify using `only [e, dif_pos hc]`. Conclude with `⟨_, hc.choose_spec.1, rfl⟩`.

Introduce and unpack `c ⟨x, hx, rfl⟩ c' ⟨x', hx', rfl⟩ h`. Establish `hc : ∃ y ∈ Dset, (y : G ⧸ J) = (x : G ⧸ J)` using `⟨x, hx, rfl⟩`. Establish `hc' : ∃ y ∈ Dset, (y : G ⧸ J) = (x' : G ⧸ J)` using `⟨x', hx', rfl⟩`. Simplify using `only [e, dif_pos hc, dif_pos hc'] at h`. Rewrite `h` using `[QuotientGroup.eq]`.

Use `show (x : G ⧸ J) = (x' : G ⧸ J)`. Rewrite using `[← hc.choose_spec.2, ← hc'.choose_spec.2, QuotientGroup.eq]`. Conclude with `(hJU _ hc.choose_spec.1 _ hc'.choose_spec.1).2 h`. Introduce and unpack `d ⟨x, hx, rfl⟩`. Establish `hc : ∃ y ∈ Dset, (y : G ⧸ J) = (x : G ⧸ J)` using `⟨x, hx, rfl⟩`.

Use `⟨(x : G ⧸ J), ⟨x, hx, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [e, dif_pos hc]`. Rewrite using `[QuotientGroup.eq]`. Establish `h1` using `hc.choose_spec.2`. Rewrite `h1` using `[QuotientGroup.eq]`.

Conclude with `(hJU _ hc.choose_spec.1 _ hx).1 h1`. Introduce and unpack `c ⟨x, hx, rfl⟩`. Establish `hc : ∃ y ∈ Dset, (y : G ⧸ J) = (x : G ⧸ J)` using `⟨x, hx, rfl⟩`. Establish `he : e x = (hc.choose : G ⧸ U)` using `by simp only [e, dif_pos hc]`. Establish `hd : ∃ y ∈ Dset, (y : G ⧸ U) = e x` using `⟨_, hc.choose_spec.1, he.symm⟩`.

Simplify using `only [φ, ψ, dif_pos hc, dif_pos hd]`. Apply `hF _ hc.choose_spec.1 _ hd.choose_spec.1` to reduce the goal to its premises. Rewrite using `[← QuotientGroup.eq, hd.choose_spec.2, he]`.
-/
theorem finsum_cosets_eq {G W : Type} [Group G] [AddCommGroup W] (J U : Subgroup G) (Dset : Set G) (F : G → W)
    (hJU : ∀ x ∈ Dset, ∀ x' ∈ Dset, (x⁻¹ * x' ∈ J ↔ x⁻¹ * x' ∈ U))
    (hF : ∀ x ∈ Dset, ∀ x' ∈ Dset, x⁻¹ * x' ∈ U → F x = F x') :
    (∑ᶠ c : G ⧸ J, if hc : ∃ x ∈ Dset, (x : G ⧸ J) = c then F hc.choose else 0) =
    ∑ᶠ c : G ⧸ U, if hc : ∃ x ∈ Dset, (x : G ⧸ U) = c then F hc.choose else 0 := by
  set φ := fun c : G ⧸ J => if hc : ∃ x ∈ Dset, (x : G ⧸ J) = c then F hc.choose else 0 with hφdef
  set ψ := fun c : G ⧸ U => if hc : ∃ x ∈ Dset, (x : G ⧸ U) = c then F hc.choose else 0 with hψdef
  have hφ : Function.support φ ⊆ (fun x : G => (x : G ⧸ J)) '' Dset := by
    intro c hc
    by_contra hn
    apply hc
    simp only [φ]
    rw [dif_neg]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  have hψ : Function.support ψ ⊆ (fun x : G => (x : G ⧸ U)) '' Dset := by
    intro c hc
    by_contra hn
    apply hc
    simp only [ψ]
    rw [dif_neg]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  rw [← Set.indicator_eq_self.2 hφ, ← Set.indicator_eq_self.2 hψ, ← finsum_mem_def, ← finsum_mem_def]
  let e : G ⧸ J → G ⧸ U := fun c => if hc : ∃ x ∈ Dset, (x : G ⧸ J) = c then (hc.choose : G ⧸ U) else ((1 : G) : G ⧸ U)
  refine finsum_mem_eq_of_bijOn e ⟨?_, ?_, ?_⟩ ?_
  · rintro c ⟨x, hx, rfl⟩
    have hc : ∃ y ∈ Dset, (y : G ⧸ J) = (x : G ⧸ J) := ⟨x, hx, rfl⟩
    simp only [e, dif_pos hc]
    exact ⟨_, hc.choose_spec.1, rfl⟩
  · rintro c ⟨x, hx, rfl⟩ c' ⟨x', hx', rfl⟩ h
    have hc : ∃ y ∈ Dset, (y : G ⧸ J) = (x : G ⧸ J) := ⟨x, hx, rfl⟩
    have hc' : ∃ y ∈ Dset, (y : G ⧸ J) = (x' : G ⧸ J) := ⟨x', hx', rfl⟩
    simp only [e, dif_pos hc, dif_pos hc'] at h
    rw [QuotientGroup.eq] at h
    show (x : G ⧸ J) = (x' : G ⧸ J)
    rw [← hc.choose_spec.2, ← hc'.choose_spec.2, QuotientGroup.eq]
    exact (hJU _ hc.choose_spec.1 _ hc'.choose_spec.1).2 h
  · rintro d ⟨x, hx, rfl⟩
    have hc : ∃ y ∈ Dset, (y : G ⧸ J) = (x : G ⧸ J) := ⟨x, hx, rfl⟩
    refine ⟨(x : G ⧸ J), ⟨x, hx, rfl⟩, ?_⟩
    simp only [e, dif_pos hc]
    rw [QuotientGroup.eq]
    have h1 := hc.choose_spec.2
    rw [QuotientGroup.eq] at h1
    exact (hJU _ hc.choose_spec.1 _ hx).1 h1
  · rintro c ⟨x, hx, rfl⟩
    have hc : ∃ y ∈ Dset, (y : G ⧸ J) = (x : G ⧸ J) := ⟨x, hx, rfl⟩
    have he : e x = (hc.choose : G ⧸ U) := by simp only [e, dif_pos hc]
    have hd : ∃ y ∈ Dset, (y : G ⧸ U) = e x := ⟨_, hc.choose_spec.1, he.symm⟩
    simp only [φ, ψ, dif_pos hc, dif_pos hd]
    apply hF _ hc.choose_spec.1 _ hd.choose_spec.1
    rw [← QuotientGroup.eq, hd.choose_spec.2, he]

end GlobalTheory.HeckeScalarAll

namespace GlobalTheory.HeckeScalarAll

section Hk

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

open Classical in

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `hsub : Function.support (fun cc : GAf L n ⧸ J => if hc : ∃ x ∈ Dset, (x : GAf L n ⧸ J) = cc then f (g * hc.choose) else 0) ⊆ (hfin.toFinset : Set (GAf L n ⧸ J))`. Introduce `cc hcc`. Rewrite using `[Set.Finite.coe_toFinset]`. Assume the negation of the conclusion as `hn`.

Apply `hcc` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `hn ⟨x, hx, rfl⟩`.

Simplify using `only [NG.heckeD]`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsub, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem heckeD_eq_sum (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (f : GAf L n → W) :
    NG.heckeD J Dset f = ∑ c ∈ hfin.toFinset,
      (if hc : ∃ x ∈ Dset, (x : GAf L n ⧸ J) = c then NG.rt L n hc.choose f else 0) := by
  funext g
  have hsub : Function.support (fun cc : GAf L n ⧸ J =>
      if hc : ∃ x ∈ Dset, (x : GAf L n ⧸ J) = cc then f (g * hc.choose) else 0) ⊆
      (hfin.toFinset : Set (GAf L n ⧸ J)) := by
    intro cc hcc
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    apply hcc
    dsimp only
    rw [dif_neg]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  simp only [NG.heckeD]
  rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> rfl

/- English proof (translation)
Rewrite using `[heckeD_eq_sum _ _ hfin, heckeD_eq_sum _ _ hfin, heckeD_eq_sum _ _ hfin, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem heckeD_add' (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (y z : GAf L n → W) :
    NG.heckeD J Dset (y + z) = NG.heckeD J Dset y + NG.heckeD J Dset z := by
  rw [heckeD_eq_sum _ _ hfin, heckeD_eq_sum _ _ hfin, heckeD_eq_sum _ _ hfin, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[heckeD_eq_sum _ _ hfin]`. Use `Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem heckeD_zero (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) :
    NG.heckeD J Dset (0 : GAf L n → W) = 0 := by
  rw [heckeD_eq_sum _ _ hfin]
  refine Finset.sum_eq_zero fun d _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [NG.heckeD]`. Use `finsum_cosets_eq J (Umax L n) _ (fun x => f (g * x)) ?_ ?_` and prove the remaining obligations. Introduce `x hx x' hx'`. Establish `ht : TrivOutside Bᶜ (x⁻¹ * x')` using `trivOutside_mono (Set.singleton_subset_iff.2 hs) (trivOutside_mul (trivOutside_inv hx.1) hx'.1)`.

Conclude with `(hJ _ ht).1`. Introduce `x hx x' hx' hu`. Establish `ht` using `trivOutside_mul (trivOutside_inv hx.1) hx'.1`. Establish `h1` using `congrFun (hf _ hu ht) (g * x)`. Simplify using `only [NG.rt, LinearMap.coe_mk, AddHom.coe_mk] at h1`.

Rewrite `h1` using `[mul_assoc, mul_inv_cancel_left]`. Conclude with `h1.symm`.
-/
theorem heckeD_eq_of_fixed (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
    (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) (hJ : NG.HypOutside J χ B)
    (s : SplitPlace L) (hs : s.v ∉ B) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ) (f : GAf L n → W)
    (hf : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) :
    NG.heckeD J (tSet L n s ϖ k) f = NG.heckeD (Umax L n) (tSet L n s ϖ k) f := by
  funext g
  simp only [NG.heckeD]
  refine finsum_cosets_eq J (Umax L n) _ (fun x => f (g * x)) ?_ ?_
  · intro x hx x' hx'
    have ht : TrivOutside Bᶜ (x⁻¹ * x') :=
      trivOutside_mono (Set.singleton_subset_iff.2 hs) (trivOutside_mul (trivOutside_inv hx.1) hx'.1)
    exact (hJ _ ht).1
  · intro x hx x' hx' hu
    have ht := trivOutside_mul (trivOutside_inv hx.1) hx'.1
    have h1 := congrFun (hf _ hu ht) (g * x)
    simp only [NG.rt, LinearMap.coe_mk, AddHom.coe_mk] at h1
    rw [mul_assoc, mul_inv_cancel_left] at h1
    exact h1.symm

/- English proof (translation)
Take `⟨T, hT⟩` from `hiso`. Use `set f : S := T.symm ⟨f', hf'⟩ with hfdef`. Establish `hTf : T f = ⟨f', hf'⟩` using `T.apply_symm_apply _`. Establish `hrt : ∀ h : GAf L n, ((T ⟨NG.rt L n h f, hS.stable h _ f.2⟩ : S') : GAf L n → W) = NG.rt L n h f'`. Introduce `h`.

Use `hT h f ⟨_, hS.stable h _ f.2⟩ rfl` as an intermediate fact. Rewrite using `[this, hTf]`. Establish `hffix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ (f : GAf L n → W) = f`. Introduce `κ hκ ht`. Establish `h1` using `hrt κ`.

Rewrite `h1` using `[hfix κ hκ ht]`. Establish `h2 : T ⟨_, hS.stable κ _ f.2⟩ = T f` using `Subtype.ext (by rw [h1, hTf])`. Conclude with `congrArg Subtype.val (T.injective h2)`. Establish `hcf` using `hc f f.2 hffix`. Set `σ : S` to `∑ d ∈ hfin.toFinset, (if hd : ∃ x ∈ tSet L n s ϖ k, (x : GAf L n ⧸ Umax L n) = d then (⟨NG.rt L n hd.choose f, hS.stable _ _ f.2⟩ : S) else 0)`.

Establish `hσ : (σ : GAf L n → W) = NG.heckeD (Umax L n) (tSet L n s ϖ k) f`. Rewrite using `[heckeD_eq_sum _ _ hfin, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> rfl`. Establish `hTσ : ((T σ : S') : GAf L n → W) = NG.heckeD (Umax L n) (tSet L n s ϖ k) f'`.

Rewrite using `[heckeD_eq_sum _ _ hfin, map_sum, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `hrt _`. Simplify using the standard rewrite rules.

Simplify using `only [NG.tN] at hcf ⊢`. Establish `key : ((s.q : ℂ) ^ (k * (n - 1)))⁻¹ • σ = c • f` using `Subtype.ext (by`. Rewrite using `[Submodule.coe_smul, hσ, Submodule.coe_smul]`. Conclude with `hcf)`. Establish `h3` using `congrArg (fun y => ((T y : S') : GAf L n → W)) key`.

Simplify using `only [map_smul, Submodule.coe_smul, hTσ, hTf] at h3`. Conclude with `h3`.
-/
theorem tN_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S)
    (hiso : NG.IsoRep S S') (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ Umax L n)) '' tSet L n s ϖ k).Finite) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → NG.tN (Umax L n) s ϖ k f = c • f)
    (f' : GAf L n → W) (hf' : f' ∈ S') (hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f' = f') :
    NG.tN (Umax L n) s ϖ k f' = c • f' := by
  classical
  obtain ⟨T, hT⟩ := hiso
  set f : S := T.symm ⟨f', hf'⟩ with hfdef
  have hTf : T f = ⟨f', hf'⟩ := T.apply_symm_apply _
  have hrt : ∀ h : GAf L n, ((T ⟨NG.rt L n h f, hS.stable h _ f.2⟩ : S') : GAf L n → W) = NG.rt L n h f' := by
    intro h
    have := hT h f ⟨_, hS.stable h _ f.2⟩ rfl
    rw [this, hTf]
  have hffix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ (f : GAf L n → W) = f := by
    intro κ hκ ht
    have h1 := hrt κ
    rw [hfix κ hκ ht] at h1
    have h2 : T ⟨_, hS.stable κ _ f.2⟩ = T f := Subtype.ext (by rw [h1, hTf])
    exact congrArg Subtype.val (T.injective h2)
  have hcf := hc f f.2 hffix
  let σ : S := ∑ d ∈ hfin.toFinset, (if hd : ∃ x ∈ tSet L n s ϖ k, (x : GAf L n ⧸ Umax L n) = d then
      (⟨NG.rt L n hd.choose f, hS.stable _ _ f.2⟩ : S) else 0)
  have hσ : (σ : GAf L n → W) = NG.heckeD (Umax L n) (tSet L n s ϖ k) f := by
    rw [heckeD_eq_sum _ _ hfin, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> rfl
  have hTσ : ((T σ : S') : GAf L n → W) = NG.heckeD (Umax L n) (tSet L n s ϖ k) f' := by
    rw [heckeD_eq_sum _ _ hfin, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs
    · exact hrt _
    · simp
  simp only [NG.tN] at hcf ⊢
  have key : ((s.q : ℂ) ^ (k * (n - 1)))⁻¹ • σ = c • f := Subtype.ext (by
    rw [Submodule.coe_smul, hσ, Submodule.coe_smul]; exact hcf)
  have h3 := congrArg (fun y => ((T y : S') : GAf L n → W)) key
  simp only [map_smul, Submodule.coe_smul, hTσ, hTf] at h3
  exact h3

end Hk

end GlobalTheory.HeckeScalarAll

namespace GlobalTheory.HeckeScalarAll

section Iso

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Establish `hle : (⨆ i ∈ t, i) ≤ (⨆ i ∈ t, i).comap (NG.rt L n h)`. Use `iSup₂_le fun i hi => ?_` and prove the remaining obligations. Introduce `f hf`. Conclude with `(le_iSup₂ (f := fun i (_ : i ∈ t) => i) i hi) (ht i hi h f hf)`. Conclude with `fun f hf => hle hf`.
-/
theorem iSup_finset_stable' (t : Finset (Submodule ℂ (GAf L n → W)))
    (ht : ∀ i ∈ t, ∀ h, ∀ f ∈ i, NG.rt L n h f ∈ i) (h : GAf L n) :
    ∀ f ∈ (⨆ i ∈ t, i), NG.rt L n h f ∈ (⨆ i ∈ t, i) := by
  have hle : (⨆ i ∈ t, i) ≤ (⨆ i ∈ t, i).comap (NG.rt L n h) := by
    refine iSup₂_le fun i hi => ?_
    intro f hf
    exact (le_iSup₂ (f := fun i (_ : i ∈ t) => i) i hi) (ht i hi h f hf)
  exact fun f hf => hle hf

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Introduce `_ f hf _`. Simplify using `only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf`. Substitute `hf` using the available equality.

Simplify using `only [NG.tN, heckeD_zero _ _ hfin, smul_zero]`. Consider the case `insert a t ha ih`. Introduce `hsub f hf hfix`. Establish `haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a` using `hsub (Finset.mem_insert_self a t)`. Establish `htF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}` using `fun x hx => hsub (Finset.mem_insert_of_mem hx)`.

Rewrite `hf` using `[Finset.iSup_insert]`. Establish `hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), NG.rt L n h g ∈ (⨆ i ∈ t, i)` using `iSup_finset_stable' t (fun i hi => (htF hi).1.1.stable)`. Establish `hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i)` using `⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩`. Break down `haF.1.2.2 _ hsubrep inf_le_left with h0 | htop` into its components or cases. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hf`.

Establish `hyfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ y = y`. Introduce `κ hκ hκt`. Establish `e` using `hfix κ hκ hκt`. Rewrite `e` using `[map_add]`. Establish `hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i`.

Use `⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩` and prove the remaining obligations. Establish `h4 : NG.rt L n κ y - y = z - NG.rt L n κ z`. Rewrite using `[sub_eq_sub_iff_add_eq_add, e]`. Conclude with `add_comm _ _`. Rewrite using `[h4]`.

Conclude with `Submodule.sub_mem _ hz (hMst κ z hz)`. Rewrite `hd` using `[h0, Submodule.mem_bot, sub_eq_zero]`. Conclude with `hd`. Establish `hzfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ z = z`. Introduce `κ hκ hκt`.

Establish `e` using `hfix κ hκ hκt`. Rewrite `e` using `[map_add, hyfix κ hκ hκt]`. Conclude with `add_left_cancel e`. Establish `e1` using `tN_iso hS.1 haF.2 s ϖ k hfin c hc y hy hyfix`. Establish `e2` using `ih htF z hz hzfix`.

Simplify using `only [NG.tN] at e1 e2 ⊢`. Rewrite using `[heckeD_add' _ _ hfin, smul_add, e1, e2, smul_add]`. Establish `hle : a ≤ ⨆ i ∈ t, i` using `inf_eq_left.1 htop`. Conclude with `ih htF f ((sup_le hle le_rfl) hf) hfix`.
-/
theorem tN_finset_sum {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S)
    (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ Umax L n)) '' tSet L n s ϖ k).Finite) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → NG.tN (Umax L n) s ϖ k f = c • f)
    (t : Finset (Submodule ℂ (GAf L n → W))) :
    (↑t ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i),
      (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → NG.tN (Umax L n) s ϖ k f = c • f := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    subst hf
    simp only [NG.tN, heckeD_zero _ _ hfin, smul_zero]
  | insert a t ha ih =>
    intro hsub f hf hfix
    have haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      iSup_finset_stable' t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ y = y := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add] at e
        have hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ z = z := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add, hyfix κ hκ hκt] at e
        exact add_left_cancel e
      have e1 := tN_iso hS.1 haF.2 s ϖ k hfin c hc y hy hyfix
      have e2 := ih htF z hz hzfix
      simp only [NG.tN] at e1 e2 ⊢
      rw [heckeD_add' _ _ hfin, smul_add, e1, e2, smul_add]
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      exact ih htF f ((sup_le hle le_rfl) hf) hfix

/- English proof (translation)
Take `⟨t, ht, hft⟩` from `Submodule.mem_sSup_iff_exists_finset.1 hf`. Conclude with `tN_finset_sum hS s ϖ k hfin c hc t ht f hft hfix`.
-/
theorem tN_isoTyp {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S)
    (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ Umax L n)) '' tSet L n s ϖ k).Finite) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → NG.tN (Umax L n) s ϖ k f = c • f)
    (f : GAf L n → W) (hf : f ∈ NG.isoTyp ρ S)
    (hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) : NG.tN (Umax L n) s ϖ k f = c • f := by
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact tN_finset_sum hS s ϖ k hfin c hc t ht f hft hfix

end Iso

end GlobalTheory.HeckeScalarAll

namespace GlobalTheory.HeckeScalarAll

open Formalism.L2.NG

/- English proof (translation)
The claim follows from `D.host.φ₀.injective (by rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])`.
-/
theorem host_conj_eq' (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

/- English proof (translation)
Introduce `x y hxy`. Establish `hx : (x : D.host.E) = D.host.conj (y : D.host.E)`. Rewrite using `[hxy, host_conj_eq', host_conj_eq', IsCMField.complexConj_apply_apply]`. Conclude with `(h y x hx).symm`.
-/
theorem isConjPl_symm' {D : D7} {w w' : PlE D.host} (h : IsConjPl D.host w w') : IsConjPl D.host w' w := by
  intro x y hxy
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := by
    rw [hxy, host_conj_eq', host_conj_eq', IsCMField.complexConj_apply_apply]
  exact (h y x hx).symm

/- English proof (translation)
Introduce and unpack `⟨w', hover, hw'⟩`. Establish `hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → w ∈ placesOver D.host.E p`. Introduce `p hp`. Establish `h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ w'.asIdeal` using `by rw [map_natCast]; exact hp`. Establish `h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal`.

Rewrite using `[← hover]`. Conclude with `h1`. Establish `h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.w.asIdeal`. Rewrite using `[← Ideal.mem_comap, s.w_under]`. Conclude with `h2`.

Rewrite `h3` using `[map_natCast]`. Conclude with `(hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by rw [host_conj_eq']; simp)).2 h3`. Take `⟨hsp, hl, hS, hQ⟩` from `hw`. Break down `hw' with hQ' | ⟨kk, hg⟩ | hpd` into its components or cases. Break down `GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE s.w w' (hover.trans s.w_under.symm) with e | e` into its components or cases.

Substitute `e` using the available equality. Conclude with `hQ (HT.Q_conj i s.w w (isConjPl_symm' hc) hQ')`. Establish `ew : GlobalTheory.SplitConjPlace.conjPlE s.w = w` using `by ext1; ext x`. Rewrite using `[GlobalTheory.SplitConjPlace.mem_conjPlE]`. Use `(hc x _ ?_).symm` and prove the remaining obligations.

Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq']`. Rewrite `hQ'` using `[e, ew]`. Conclude with `hQ hQ'`. Apply `hS` to reduce the goal to its premises. Use `(D.nd.S_def i w).2 ⟨?_, hl⟩` and prove the remaining obligations.

Establish `hv` using `hp _ hg`. Use `fin_cases kk`. Conclude with `Or.inl hv`. Conclude with `Or.inr (Or.inl hv)`. Conclude with `hS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr (hp _ hpd)), hl⟩)`.
-/
theorem not_bad {D : D7} {M : MtFam D} (HT : HeckeTied D M) (i : D.nd.Loc) {w : PlE D.host}
    (hw : SplitOut D.nd i w) (s : SplitPlace D.host.E) (hc : IsConjPl D.host w s.w) : s.v ∉ badPl D i := by
  rintro ⟨w', hover, hw'⟩
  have hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → w ∈ placesOver D.host.E p := by
    intro p hp
    have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        w'.asIdeal := by rw [map_natCast]; exact hp
    have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hover]; exact h1
    have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        s.w.asIdeal := by
      rw [← Ideal.mem_comap, s.w_under]; exact h2
    rw [map_natCast] at h3
    exact (hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by rw [host_conj_eq']; simp)).2 h3
  obtain ⟨hsp, hl, hS, hQ⟩ := hw
  rcases hw' with hQ' | ⟨kk, hg⟩ | hpd
  · rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE s.w w' (hover.trans s.w_under.symm) with e | e
    · subst e
      exact hQ (HT.Q_conj i s.w w (isConjPl_symm' hc) hQ')
    · have ew : GlobalTheory.SplitConjPlace.conjPlE s.w = w := by
        ext1; ext x
        rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
        refine (hc x _ ?_).symm
        rw [IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq']
      rw [e, ew] at hQ'
      exact hQ hQ'
  · apply hS
    refine (D.nd.S_def i w).2 ⟨?_, hl⟩
    have hv := hp _ hg
    fin_cases kk
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  · exact hS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr (hp _ hpd)), hl⟩)

/- English proof (translation)
Introduce `D M HT A i P w k s ϖ hw hcw hu _ _`. Establish `hsB : s.v ∉ badPl D i` using `not_bad HT i hw s hcw`. Take `⟨c, hc⟩` from `GlobalTheory.T.splitPlace_heckeOperator_scalar_on_spherical D.host.E D.R.nV (M.loc i).wt (A.S i P) (A.irr i P) s ϖ k hu`. Establish `hfinU` using `GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (Umax D.host.E D.R.nV) 1 ∅ (fun κ _ => ⟨Iff.rfl, fun _ => rfl⟩) s ϖ k (by simp) hu`. Use `⟨c, fun y hy => ?_⟩` and prove the remaining obligations.

Establish `hfT : (M.loc i).real y ∈ NG.TypeSp (M.loc i).wt.ρ (M.loc i).J (M.loc i).χ`. Rewrite using `[← (M.loc i).real_range]`. Conclude with `⟨y, rfl⟩`. Establish `hfI : (M.loc i).real y ∈ NG.isoTyp (M.loc i).wt.ρ (A.S i P)`. Rewrite `hy` using `[A.typeV]`.

Conclude with `hy`. Establish `hfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ ((M.loc i).real y) = (M.loc i).real y`. Introduce `κ hκ ht`. Establish `ht' : TrivOutside (badPl D i)ᶜ κ` using `trivOutside_mono (Set.singleton_subset_iff.2 hsB) ht`. Take `⟨h1, h2⟩` from `HT.J_hyp i κ ht'`.

Establish `hJ : κ ∈ (M.loc i).J` using `h1.2 hκ`. Establish `e` using `hfT.2 ⟨κ, hJ⟩`. Rewrite `e` using `[h2 hJ]`. Simplify using `using e`. Establish `e1 : NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = NG.tN (Umax D.host.E D.R.nV) s ϖ k ((M.loc i).real y)`.

Simplify using `only [NG.tN]`. Rewrite using `[heckeD_eq_of_fixed (M.loc i).J (M.loc i).χ (badPl D i) (HT.J_hyp i) s hsB ϖ k _ hfix]`. Rewrite using `[e1]`. Conclude with `tN_isoTyp (A.irr i P) s ϖ k hfinU c hc _ hfI hfix`.
-/
theorem heckeScalar_all : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ i : D.nd.Loc, HeckeScalar M i := by
  intro D M HT A i P w k s ϖ hw hcw hu _ _
  have hsB : s.v ∉ badPl D i := not_bad HT i hw s hcw
  obtain ⟨c, hc⟩ := GlobalTheory.T.splitPlace_heckeOperator_scalar_on_spherical D.host.E D.R.nV (M.loc i).wt (A.S i P) (A.irr i P) s ϖ k hu
  have hfinU := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (Umax D.host.E D.R.nV) 1 ∅
    (fun κ _ => ⟨Iff.rfl, fun _ => rfl⟩) s ϖ k (by simp) hu
  refine ⟨c, fun y hy => ?_⟩
  have hfT : (M.loc i).real y ∈ NG.TypeSp (M.loc i).wt.ρ (M.loc i).J (M.loc i).χ := by
    rw [← (M.loc i).real_range]; exact ⟨y, rfl⟩
  have hfI : (M.loc i).real y ∈ NG.isoTyp (M.loc i).wt.ρ (A.S i P) := by
    rw [A.typeV] at hy; exact hy
  have hfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      NG.rt D.host.E D.R.nV κ ((M.loc i).real y) = (M.loc i).real y := by
    intro κ hκ ht
    have ht' : TrivOutside (badPl D i)ᶜ κ := trivOutside_mono (Set.singleton_subset_iff.2 hsB) ht
    obtain ⟨h1, h2⟩ := HT.J_hyp i κ ht'
    have hJ : κ ∈ (M.loc i).J := h1.2 hκ
    have e := hfT.2 ⟨κ, hJ⟩
    rw [h2 hJ] at e
    simpa using e
  have e1 : NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = NG.tN (Umax D.host.E D.R.nV) s ϖ k ((M.loc i).real y) := by
    simp only [NG.tN]
    rw [heckeD_eq_of_fixed (M.loc i).J (M.loc i).χ (badPl D i) (HT.J_hyp i) s hsB ϖ k _ hfix]
  rw [e1]
  exact tN_isoTyp (A.irr i P) s ϖ k hfinU c hc _ hfI hfix

end GlobalTheory.HeckeScalarAll
