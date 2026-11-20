import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
import Formalism.AdmissibleDesigns.RankReductionIdempotentOne

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KFin

open Formalism.NG

section Gen

variable {O : Type} [CommRing O] [IsDomain O] {Γ : Type} [Group Γ]
  {L : Type} [AddCommGroup L] [Module O L]
  {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
  {M : Type} [AddCommGroup M] [Module O M]
  (ρL : Representation O Γ L) (ρV : Representation O Γ V) (ρM : Representation O Γ M)
  (iL : L →ₗ[O] V) (qV : V →ₗ[O] M) (Zf : Submodule (FractionRing O) (Γ → V))

def finPreG : Submodule O (Γ → L) := (Zf.restrictScalars O).comap (LinearMap.compLeft iL Γ)

def FfG : Submodule O (H1z ρL) := ((finPreG iL Zf).comap (coZ1s ρL).subtype).map (Submodule.mkQ _)

def ImageOfFiniteCocycles : Submodule O (H1z ρM) :=
  (((Zf.restrictScalars O).map (LinearMap.compLeft qV Γ) ⊔ coB1 ρM).comap (coZ1s ρM).subtype).map (Submodule.mkQ _)

/- English proof (translation)
Take `⟨z₀, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Unfold `FfG at hz ⊢`. Rewrite `hz` using `[Submodule.mem_map]`. Take `⟨w, hw, hwz⟩` from `hz`. Rewrite `hwz` using `[← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq]`.

Rewrite `hwz`, `hw` using `[Submodule.mem_comap]`. Unfold `coB1 at hwz`. Rewrite `hwz` using `[LinearMap.mem_range]`. Take `⟨m, hm⟩` from `hwz`. Apply `Submodule.mem_map_of_mem` to reduce the goal to its premises.

Rewrite using `[Submodule.mem_comap]`. Unfold `finPreG at hw ⊢`. Rewrite `hw`, the goal using `[Submodule.mem_comap, Submodule.restrictScalars_mem]`. Establish `hc' : algebraMap O (FractionRing O) c ≠ 0`. Introduce `h0`.

Conclude with `hc ((IsFractionRing.injective O (FractionRing O)) (by rw [h0, map_zero]))`. Establish `key : LinearMap.compLeft iL Γ (z₀ : Γ → L) = (algebraMap O (FractionRing O) c)⁻¹ • (LinearMap.compLeft iL Γ (w : Γ → L) - coD0 ρV (iL m))`. Use function extensionality and compare the values at `g`. Establish `hmg : ρL g m - m = (w : Γ → L) g - c • (z₀ : Γ → L) g` using `congrFun hm g`. Use `show iL ((z₀ : Γ → L) g) = (algebraMap O (FractionRing O) c)⁻¹ • (iL ((w : Γ → L) g) - (ρV g (iL m) - iL m))`.

Rewrite using `[← hiL, ← map_sub, ← map_sub, hmg, sub_sub_cancel, map_smul, ← algebraMap_smul (FractionRing O) c (iL ((z₀ : Γ → L) g)), smul_smul, inv_mul_cancel₀ hc', one_smul]`. Establish `hfin : LinearMap.compLeft iL Γ (z₀ : Γ → L) ∈ Zf`. Rewrite using `[key]`. Conclude with `Zf.smul_mem _ (Zf.sub_mem hw (hB _))`. Conclude with `hfin`.
-/
theorem FfG_sat (hB : ∀ v : V, coD0 ρV v ∈ Zf) (hiL : ∀ g m, iL (ρL g m) = ρV g (iL m))
    (c : O) (z : H1z ρL) (hc : c ≠ 0) (hz : c • z ∈ FfG ρL iL Zf) : z ∈ FfG ρL iL Zf := by
  obtain ⟨z₀, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  unfold FfG at hz ⊢
  rw [Submodule.mem_map] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq] at hwz
  rw [Submodule.mem_comap] at hwz hw
  unfold coB1 at hwz
  rw [LinearMap.mem_range] at hwz
  obtain ⟨m, hm⟩ := hwz
  apply Submodule.mem_map_of_mem
  rw [Submodule.mem_comap]
  unfold finPreG at hw ⊢
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem] at hw ⊢
  have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
    intro h0
    exact hc ((IsFractionRing.injective O (FractionRing O)) (by rw [h0, map_zero]))
  have key : LinearMap.compLeft iL Γ (z₀ : Γ → L) =
      (algebraMap O (FractionRing O) c)⁻¹ • (LinearMap.compLeft iL Γ (w : Γ → L) - coD0 ρV (iL m)) := by
    funext g
    have hmg : ρL g m - m = (w : Γ → L) g - c • (z₀ : Γ → L) g := congrFun hm g
    show iL ((z₀ : Γ → L) g) = (algebraMap O (FractionRing O) c)⁻¹ • (iL ((w : Γ → L) g) - (ρV g (iL m) - iL m))
    rw [← hiL, ← map_sub, ← map_sub, hmg, sub_sub_cancel, map_smul,
      ← algebraMap_smul (FractionRing O) c (iL ((z₀ : Γ → L) g)), smul_smul, inv_mul_cancel₀ hc', one_smul]
  have hfin : LinearMap.compLeft iL Γ (z₀ : Γ → L) ∈ Zf := by
    rw [key]
    exact Zf.smul_mem _ (Zf.sub_mem hw (hB _))
  exact hfin

/- English proof (translation)
Use `choose y hy using fun a => Submodule.Quotient.mk_surjective _ (x a)`. Unfold `ImageOfFiniteCocycles`. Apply `Submodule.mem_map_of_mem` to reduce the goal to its premises. Rewrite using `[Submodule.mem_comap]`. Apply `Submodule.mem_sup_left` to reduce the goal to its premises.

Rewrite using `[Submodule.mem_map]`. Use `⟨∑ a, y a • (fun g => iL (κ a g)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem]`. Conclude with `Zf.sum_mem (fun a _ => Zf.smul_mem _ (hκ a))`. Use function extensionality and compare the values at `g show qV ((∑ a, y a • (fun g => iL (κ a g))) g) = (z : Γ → M) g`.

Rewrite using `[hz g, Finset.sum_apply, map_sum]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[← hy a, htens]`. Both sides reduce to the same expression.
-/
theorem mem_image_of_tensor_sum (tens : L →ₗ[O] KO O →ₗ[O] M)
    (htens : ∀ v (x : FractionRing O), tens v (Submodule.Quotient.mk x) = qV (x • iL v))
    {ι : Type} [Fintype ι] (κ : ι → Γ → L) (hκ : ∀ a, (fun g => iL (κ a g)) ∈ Zf)
    (z : coZ1s ρM) (x : ι → KO O) (hz : ∀ g, (z : Γ → M) g = ∑ a, tens (κ a g) (x a)) :
    Submodule.mkQ _ z ∈ ImageOfFiniteCocycles ρM qV Zf := by
  choose y hy using fun a => Submodule.Quotient.mk_surjective _ (x a)
  unfold ImageOfFiniteCocycles
  apply Submodule.mem_map_of_mem
  rw [Submodule.mem_comap]
  apply Submodule.mem_sup_left
  rw [Submodule.mem_map]
  refine ⟨∑ a, y a • (fun g => iL (κ a g)), ?_, ?_⟩
  · rw [Submodule.restrictScalars_mem]
    exact Zf.sum_mem (fun a _ => Zf.smul_mem _ (hκ a))
  · funext g
    show qV ((∑ a, y a • (fun g => iL (κ a g))) g) = (z : Γ → M) g
    rw [hz g, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← hy a, htens]
    rfl

def LatBasisG (j : ℕ) : Prop :=
  ∃ κ' : Fin j → coZ1s ρL, (∀ a, (fun g => iL ((κ' a : Γ → L) g)) ∈ Zf) ∧
    (∀ z ∈ FfG ρL iL Zf, ∃ (b : Fin j → O) (c : O), c ≠ 0 ∧
      c • (z - ∑ a, b a • (Submodule.mkQ _ (κ' a) : H1z ρL)) = 0) ∧
    (∀ (b : Fin j → O) (c : O), c ≠ 0 → c • ∑ a, b a • (Submodule.mkQ _ (κ' a) : H1z ρL) = 0 → b = 0)

def kapG (j : ℕ) : Fin j → coZ1s ρL :=
  if h : LatBasisG ρL iL Zf j then h.choose else fun _ => 0

/- English proof (translation)
Distinguish the cases in `h : LatBasisG ρL iL Zf j`. Establish `e : kapG ρL iL Zf j = h.choose` using `dif_pos h`. Rewrite using `[e]`. Conclude with `h.choose_spec.1 a`. Establish `e : kapG ρL iL Zf j = fun _ => 0` using `dif_neg h`.

Rewrite using `[e]`. Use `Zf.zero_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules.
-/
theorem kapG_fin (j : ℕ) (a : Fin j) : (fun g => iL ((kapG ρL iL Zf j a : Γ → L) g)) ∈ Zf := by
  by_cases h : LatBasisG ρL iL Zf j
  · have e : kapG ρL iL Zf j = h.choose := dif_pos h
    rw [e]
    exact h.choose_spec.1 a
  · have e : kapG ρL iL Zf j = fun _ => 0 := dif_neg h
    rw [e]
    convert Zf.zero_mem using 1
    funext g
    simp

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem kapG_eq {j : ℕ} (h : LatBasisG ρL iL Zf j) : kapG ρL iL Zf j = h.choose := dif_pos h

/- English proof (translation)
Rewrite using `[kapG_eq (h := h)]`. Conclude with `h.choose_spec.2`.
-/
theorem kapG_basis {j : ℕ} (h : LatBasisG ρL iL Zf j) :
    (∀ z ∈ FfG ρL iL Zf, ∃ (b : Fin j → O) (c : O), c ≠ 0 ∧
      c • (z - ∑ a, b a • (Submodule.mkQ _ (kapG ρL iL Zf j a) : H1z ρL)) = 0) ∧
    (∀ (b : Fin j → O) (c : O), c ≠ 0 →
      c • ∑ a, b a • (Submodule.mkQ _ (kapG ρL iL Zf j a) : H1z ρL) = 0 → b = 0) := by
  rw [kapG_eq (h := h)]
  exact h.choose_spec.2

/- English proof (translation)
Unfold `FfG`. Apply `Submodule.mem_map_of_mem` to reduce the goal to its premises. Rewrite using `[Submodule.mem_comap]`. Unfold `finPreG`. Rewrite using `[Submodule.mem_comap, Submodule.restrictScalars_mem]`.

Conclude with `kapG_fin ρL iL Zf j a`.
-/
theorem kapG_mem' (j : ℕ) (a : Fin j) : Submodule.mkQ _ (kapG ρL iL Zf j a) ∈ FfG ρL iL Zf := by
  unfold FfG
  apply Submodule.mem_map_of_mem
  rw [Submodule.mem_comap]
  unfold finPreG
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem]
  exact kapG_fin ρL iL Zf j a

/- English proof (translation)
The claim follows from `kapG_mem' ρL iL Zf j a`.
-/
theorem kapG_mem (j : ℕ) (a : Fin j) : Submodule.mkQ _ (kapG ρL iL Zf j a) ∈ FfG ρL iL Zf := kapG_mem' ρL iL Zf j a

/- English proof (translation)
Use `haveI := hfg`. Use `haveI hfree : Module.Free O (↥(FfG ρL iL Zf) ⧸ Submodule.torsion O ↥(FfG ρL iL Zf)) := by first`. Consider the case `exact Module.free_of_finite_type_torsion_free'`. Consider the case `infer_instance`. Set `e` to `Module.finBasisOfFinrankEq _ _ hrk`.

Use `choose f hf using fun a => Submodule.Quotient.mk_surjective (Submodule.torsion O ↥(FfG ρL iL Zf)) (e a)`. Establish `hw : ∀ a, ∃ w : ↥(coZ1s ρL), w ∈ (finPreG iL Zf).comap (coZ1s ρL).subtype ∧ Submodule.mkQ _ w = ((f a : ↥(FfG ρL iL Zf)) : H1z ρL)`. Introduce `a`. Establish `h` using `(f a).2`. Unfold `FfG at h`.

Rewrite `h` using `[Submodule.mem_map]`. Conclude with `h`. Use `choose w hwmem hwf using hw`. Use `⟨w, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`.

Establish `h` using `hwmem a`. Rewrite `h` using `[Submodule.mem_comap]`. Unfold `finPreG at h`. Rewrite `h` using `[Submodule.mem_comap, Submodule.restrictScalars_mem]`. Conclude with `h`.

Introduce `z hz`. Set `zF : ↥(FfG ρL iL Zf)` to `⟨z, hz⟩`. Set `b` to `e.repr (Submodule.Quotient.mk zF)`. Use `⟨fun a => b a, ?_⟩` and prove the remaining obligations. Establish `hmem : zF - ∑ a, b a • f a ∈ Submodule.torsion O ↥(FfG ρL iL Zf)`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]`. Simplify using `only [map_smul, Submodule.mkQ_apply, hf]`. Rewrite using `[sub_eq_zero]`. Conclude with `(e.sum_repr _).symm`. Take `⟨c, hc⟩` from `(Submodule.mem_torsion_iff _).1 hmem`.

Use `⟨(c : O), ?_, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `exact nonZeroDivisors.coe_ne_zero c`. Consider the case `exact nonZeroDivisors.ne_zero c.2`. Establish `h2` using `congrArg Subtype.val hc`.

Simplify `h2` using `[zF, Submonoid.smul_def, Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_sum, ← hwf]`. Introduce `b c hc hsum`. Establish `hF : (c • ∑ a, b a • f a : ↥(FfG ρL iL Zf)) = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify `hsum` using `[Submodule.coe_smul, Submodule.coe_sum, ← hwf]`.

Establish `hT : ∑ a, b a • f a ∈ Submodule.torsion O ↥(FfG ρL iL Zf)` using `(Submodule.mem_torsion_iff _).2 ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, hF⟩`. Establish `h0 : (Submodule.torsion O ↥(FfG ρL iL Zf)).mkQ (∑ a, b a • f a) = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hT`. Rewrite `h0` using `[map_sum]`.

Simplify using `only [map_smul, Submodule.mkQ_apply, hf] at h0`. Conclude with `funext (Fintype.linearIndependent_iff.1 e.linearIndependent b h0)`.
-/
theorem latBasisG_of [IsPrincipalIdealRing O] (j : ℕ) (hfg : Module.Finite O ↥(FfG ρL iL Zf))
    (hrk : Module.finrank O (↥(FfG ρL iL Zf) ⧸ Submodule.torsion O ↥(FfG ρL iL Zf)) = j) :
    LatBasisG ρL iL Zf j := by
  classical
  haveI := hfg
  haveI hfree : Module.Free O (↥(FfG ρL iL Zf) ⧸ Submodule.torsion O ↥(FfG ρL iL Zf)) := by
    first
      | exact Module.free_of_finite_type_torsion_free'
      | infer_instance
  let e := Module.finBasisOfFinrankEq _ _ hrk
  choose f hf using fun a => Submodule.Quotient.mk_surjective (Submodule.torsion O ↥(FfG ρL iL Zf)) (e a)
  have hw : ∀ a, ∃ w : ↥(coZ1s ρL), w ∈ (finPreG iL Zf).comap (coZ1s ρL).subtype ∧
      Submodule.mkQ _ w = ((f a : ↥(FfG ρL iL Zf)) : H1z ρL) := by
    intro a
    have h := (f a).2
    unfold FfG at h
    rw [Submodule.mem_map] at h
    exact h
  choose w hwmem hwf using hw
  refine ⟨w, ?_, ?_, ?_⟩
  · intro a
    have h := hwmem a
    rw [Submodule.mem_comap] at h
    unfold finPreG at h
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem] at h
    exact h
  · intro z hz
    let zF : ↥(FfG ρL iL Zf) := ⟨z, hz⟩
    let b := e.repr (Submodule.Quotient.mk zF)
    refine ⟨fun a => b a, ?_⟩
    have hmem : zF - ∑ a, b a • f a ∈ Submodule.torsion O ↥(FfG ρL iL Zf) := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
      simp only [map_smul, Submodule.mkQ_apply, hf]
      rw [sub_eq_zero]
      exact (e.sum_repr _).symm
    obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff _).1 hmem
    refine ⟨(c : O), ?_, ?_⟩
    · first
        | exact nonZeroDivisors.coe_ne_zero c
        | exact nonZeroDivisors.ne_zero c.2
    · have h2 := congrArg Subtype.val hc
      simpa [zF, Submonoid.smul_def, Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_sum, ← hwf] using h2
  · intro b c hc hsum
    have hF : (c • ∑ a, b a • f a : ↥(FfG ρL iL Zf)) = 0 := by
      apply Subtype.ext
      simpa [Submodule.coe_smul, Submodule.coe_sum, ← hwf] using hsum
    have hT : ∑ a, b a • f a ∈ Submodule.torsion O ↥(FfG ρL iL Zf) :=
      (Submodule.mem_torsion_iff _).2 ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, hF⟩
    have h0 : (Submodule.torsion O ↥(FfG ρL iL Zf)).mkQ (∑ a, b a • f a) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hT
    rw [map_sum] at h0
    simp only [map_smul, Submodule.mkQ_apply, hf] at h0
    exact funext (Fintype.linearIndependent_iff.1 e.linearIndependent b h0)

end Gen

section Lat

open Formalism.RepresentationBoundsCohomology.SF

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {A : Type} [Ring A]
  (n : Type) [Fintype n] [DecidableEq n] (ρ : A →+* Matrix n n O)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Use `show algebraMap O (FractionRing O) (∑ j, (ρ a) k j • u j) = ∑ j, (ρ a) k j • algebraMap O (FractionRing O) (u j)`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_eq_mul, map_mul, Algebra.smul_def]`.
-/
theorem iLM_smul (a : A) (u : LatM O O n ρ) : iLM O n ρ (a • u) = a • iLM O n ρ u := by
  funext k
  show algebraMap O (FractionRing O) (∑ j, (ρ a) k j • u j) =
    ∑ j, (ρ a) k j • algebraMap O (FractionRing O) (u j)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_eq_mul, map_mul, Algebra.smul_def]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Use `show u a • (Submodule.Quotient.mk x : KO O) = (1 : Submodule O (FractionRing O)).mkQ (x • algebraMap O (FractionRing O) (u a))`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.mkQ_apply]`. Use `congr 1`. Rewrite using `[Algebra.smul_def, smul_eq_mul, mul_comm]`.
-/
theorem tensM_mk (u : LatM O O n ρ) (x : FractionRing O) :
    tensM O n ρ u (Submodule.Quotient.mk x) = qVM O n ρ (x • iLM O n ρ u) := by
  funext a
  show u a • (Submodule.Quotient.mk x : KO O) =
    (1 : Submodule O (FractionRing O)).mkQ (x • algebraMap O (FractionRing O) (u a))
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply]
  congr 1
  rw [Algebra.smul_def, smul_eq_mul, mul_comm]

end Lat

section Rec

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev Lr : Type := LatM (D.nd.O i) (D.nd.O i) {a // RepresentationBoundsCohomology.blk D.R a = 0} (Dd.ρk 0).toRingHom

abbrev Vr : Type := LatM (D.nd.O i) (FractionRing (D.nd.O i)) {a // RepresentationBoundsCohomology.blk D.R a = 0} (Dd.ρk 0).toRingHom

abbrev iLr : Lr i Dd →ₗ[D.nd.O i] Vr i Dd := iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom

abbrev qVr : Vr i Dd →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0 := qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom

abbrev tensr : Lr i Dd →ₗ[D.nd.O i] KO (D.nd.O i) →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0 :=
  tensM (D.nd.O i) _ (Dd.ρk 0).toRingHom

abbrev Γc (l : K.Col i dc) := KHf.Γn i dc (K.colIdx i dc l)

abbrev ρL (l : K.Col i dc) : Representation (D.nd.O i) ↥(Γc i dc l) (Lr i Dd) :=
  resRep (uRep (D.nd.O i) (M := Lr i Dd) Dd.r Dd.χ) (Γc i dc l)

abbrev ρV (l : K.Col i dc) : Representation (D.nd.O i) ↥(Γc i dc l) (Vr i Dd) :=
  resRep (uRep (D.nd.O i) (M := Vr i Dd) Dd.r Dd.χ) (Γc i dc l)

abbrev ρM (l : K.Col i dc) : Representation (D.nd.O i) ↥(Γc i dc l) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) :=
  resRep (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ) (Γc i dc l)

abbrev Zf (l : K.Col i dc) : Submodule (FractionRing (D.nd.O i)) (↥(Γc i dc l) → Vr i Dd) :=
  KHf.fZ i dc (K.colIdx i dc l) (ρV i dc Dd l)

abbrev Ffr (l : K.Col i dc) := KHf.Ff i dc Dd.r Dd.χ (iLr i Dd) l

variable (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

abbrev jr : ℕ → ℕ := KHf.jK i dc ρ π

def CobFin (l : K.Col i dc) : Prop := ∀ v : Vr i Dd, coD0 (ρV i dc Dd l) v ∈ Zf i dc Dd l

def LatBasis (l : K.Col i dc) : Prop :=
  LatBasisG (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l) (jr i dc ρ π (K.colIdx i dc l))

def κz (l : K.Col i dc) (a : Fin (jr i dc ρ π (K.colIdx i dc l))) :
    coZ1s (resRep (uRep (D.nd.O i) (M := Lr i Dd) Dd.r Dd.χ) (Γc i dc l)) :=
  kapG (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l) (jr i dc ρ π (K.colIdx i dc l)) a

def κ (l : K.Col i dc) (a : Fin (jr i dc ρ π (K.colIdx i dc l))) (g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om) : Lr i Dd :=
  if h : g ∈ Γc i dc l then (κz i dc Dd ρ π l a : ↥(Γc i dc l) → Lr i Dd) ⟨g, h⟩ else 0

/- English proof (translation)
Introduce `v`. Use `show coD0 (ρV i dc Dd l) v ∈ KHf.fZ i dc (K.colIdx i dc l) (ρV i dc Dd l)`. Unfold `KHf.fZ`. Use `split`. Name the introduced variables `hn`.

Establish `hO` using `h hn`. Simplify using `only [KHf.finZ, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]`. Use `⟨⟨?_, ?_⟩, TensorProduct.tmul _ v 1, ?_⟩` and prove the remaining obligations. Conclude with `(hO v).sub continuous_const`. Introduce `g g' show (ρV i dc Dd l) (Br.iota D.nbr i _ hn (g * g')) v - v = ((ρV i dc Dd l) (Br.iota D.nbr i _ hn g) v - v) + (ρV i dc Dd l) (Br.iota D.nbr i _ hn g) ((ρV i dc Dd l) (Br.iota D.nbr i _ hn g') v - v)`.

Establish `hm : ∀ w : Vr i Dd, (ρV i dc Dd l) (Br.iota D.nbr i _ hn (g * g')) w = (ρV i dc Dd l) (Br.iota D.nbr i _ hn g) ((ρV i dc Dd l) (Br.iota D.nbr i _ hn g') w)`. Introduce `w`. Rewrite using `[map_mul]`. Conclude with `LinearMap.congr_fun ((ρV i dc Dd l).map_mul _ _) w`. Rewrite using `[hm, map_sub]`.

Normalize the expressions using the abelian group laws. Introduce `g`. Unfold `Formalism.WeaklyAdmissibleFiltrations.actVB`. Use `erw [TensorProduct.AlgebraTensorModule.map_tmul]`. Establish `h1 : ((Br.PD D.loc D.nbr i _ hn).actB g).toAlgHom 1 = 1` using `map_one _`.

Simplify using `only [LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, h1]`. Use `erw [← TensorProduct.sub_tmul]`. Both sides reduce to the same expression. Conclude with `Submodule.mem_top`.
-/
theorem cobFin_of (l : K.Col i dc) (h : KHf.OrbC i dc (ρV i dc Dd l)) : CobFin i dc Dd l := by
  intro v
  show coD0 (ρV i dc Dd l) v ∈ KHf.fZ i dc (K.colIdx i dc l) (ρV i dc Dd l)
  unfold KHf.fZ
  split
  · rename_i hn
    have hO := h hn
    simp only [KHf.finZ, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    refine ⟨⟨?_, ?_⟩, TensorProduct.tmul _ v 1, ?_⟩
    · exact (hO v).sub continuous_const
    · intro g g'
      show (ρV i dc Dd l) (Br.iota D.nbr i _ hn (g * g')) v - v =
        ((ρV i dc Dd l) (Br.iota D.nbr i _ hn g) v - v) +
          (ρV i dc Dd l) (Br.iota D.nbr i _ hn g) ((ρV i dc Dd l) (Br.iota D.nbr i _ hn g') v - v)
      have hm : ∀ w : Vr i Dd, (ρV i dc Dd l) (Br.iota D.nbr i _ hn (g * g')) w =
          (ρV i dc Dd l) (Br.iota D.nbr i _ hn g) ((ρV i dc Dd l) (Br.iota D.nbr i _ hn g') w) := by
        intro w
        rw [map_mul]
        exact LinearMap.congr_fun ((ρV i dc Dd l).map_mul _ _) w
      rw [hm, map_sub]
      abel
    · intro g
      unfold Formalism.WeaklyAdmissibleFiltrations.actVB
      erw [TensorProduct.AlgebraTensorModule.map_tmul]
      have h1 : ((Br.PD D.loc D.nbr i _ hn).actB g).toAlgHom 1 = 1 := map_one _
      simp only [LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, h1]
      erw [← TensorProduct.sub_tmul]
      rfl
  · exact Submodule.mem_top

def FinFf (l : K.Col i dc) : Prop := Module.Finite (D.nd.O i) ↥(FfG (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l))

def RankFf (l : K.Col i dc) : Prop :=
  Module.finrank (D.nd.O i) (↥(FfG (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l)) ⧸
      Submodule.torsion (D.nd.O i) ↥(FfG (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l))) =
    jr i dc ρ π (K.colIdx i dc l)

/- English proof (translation)
The claim follows from `latBasisG_of _ _ _ _ hf hr`.
-/
theorem latBasis_of (l : K.Col i dc) (hf : FinFf i dc Dd l) (hr : RankFf i dc Dd ρ π l) : LatBasis i dc Dd ρ π l := latBasisG_of _ _ _ _ hf hr

/- English proof (translation)
Unfold `κ`. Rewrite using `[dif_pos g.2]`.
-/
theorem κ_mem (l : K.Col i dc) a (g : ↥(Γc i dc l)) :
    κ i dc Dd ρ π l a g = (κz i dc Dd ρ π l a : ↥(Γc i dc l) → Lr i Dd) g := by
  unfold κ
  rw [dif_pos g.2]

/- English proof (translation)
The claim follows from `iLM_smul (D.nd.O i) _ (Dd.ρk 0).toRingHom (Formalism.NG.uElt Dd.r Dd.χ (g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om)) m`.
-/
theorem iL_equiv (l : K.Col i dc) (g : ↥(Γc i dc l)) (m : Lr i Dd) :
    iLr i Dd (ρL i dc Dd l g m) = ρV i dc Dd l g (iLr i Dd m) := iLM_smul (D.nd.O i) _ (Dd.ρk 0).toRingHom (Formalism.NG.uElt Dd.r Dd.χ (g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om)) m

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Unfold `KHf.FinRhoAt`. Use `⟨fun a g => (κ_mem i dc Dd ρ π l a g).symm, ?_, fun a => ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `c z hc hz`. Conclude with `FfG_sat _ _ _ _ hB (iL_equiv i dc Dd l) c z hc hz`. Conclude with `kapG_mem _ _ _ _ a`.

Conclude with `(kapG_basis (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l) hL).1`. Conclude with `(kapG_basis (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l) hL).2`.
-/
theorem finRhoAt (l : K.Col i dc) (hB : CobFin i dc Dd l) (hL : LatBasis i dc Dd ρ π l) :
    KHf.FinRhoAt i dc Dd.r Dd.χ (Ffr i dc Dd) (jr i dc ρ π) (κ i dc Dd ρ π) (κz i dc Dd ρ π) l := by
  unfold KHf.FinRhoAt
  refine ⟨fun a g => (κ_mem i dc Dd ρ π l a g).symm, ?_, fun a => ?_, ?_, ?_⟩
  · intro c z hc hz
    exact FfG_sat _ _ _ _ hB (iL_equiv i dc Dd l) c z hc hz
  · exact kapG_mem _ _ _ _ a
  · exact (kapG_basis (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l) hL).1
  · exact (kapG_basis (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l) hL).2

/- English proof (translation)
Establish `hκ : ∀ a, (fun g : ↥(Γc i dc l) => iLr i Dd (κ i dc Dd ρ π l a g)) ∈ Zf i dc Dd l`. Introduce `a`. Establish `e : (fun g : ↥(Γc i dc l) => iLr i Dd (κ i dc Dd ρ π l a g)) = fun g => iLr i Dd ((κz i dc Dd ρ π l a : ↥(Γc i dc l) → Lr i Dd) g)`. Use function extensionality and compare the values at `g`. Rewrite using `[κ_mem]`.

Rewrite using `[e]`. Conclude with `kapG_fin _ _ _ _ a`. Conclude with `mem_image_of_tensor_sum (ρM i dc Dd l) (iLr i Dd) (qVr i Dd) (Zf i dc Dd l) (tensr i Dd) (fun v x => tensM_mk _ _ _ v x) (fun a g => κ i dc Dd ρ π l a g) hκ z x hz`.
-/
theorem clause3 (l : K.Col i dc) (z : coZ1s (ρM i dc Dd l)) (x : Fin (jr i dc ρ π (K.colIdx i dc l)) → KO (D.nd.O i))
    (hz : ∀ g : ↥(Γc i dc l), (z : ↥(Γc i dc l) → blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) g =
      ∑ a, tensr i Dd (κ i dc Dd ρ π l a g) (x a)) :
    Submodule.mkQ _ z ∈ KHf.F0col i dc (K.colIdx i dc l) (ρV i dc Dd l) (ρM i dc Dd l) (qVr i Dd) := by
  have hκ : ∀ a, (fun g : ↥(Γc i dc l) => iLr i Dd (κ i dc Dd ρ π l a g)) ∈ Zf i dc Dd l := by
    intro a
    have e : (fun g : ↥(Γc i dc l) => iLr i Dd (κ i dc Dd ρ π l a g)) =
        fun g => iLr i Dd ((κz i dc Dd ρ π l a : ↥(Γc i dc l) → Lr i Dd) g) := by
      funext g
      rw [κ_mem]
    rw [e]
    exact kapG_fin _ _ _ _ a
  exact mem_image_of_tensor_sum (ρM i dc Dd l) (iLr i Dd) (qVr i Dd) (Zf i dc Dd l) (tensr i Dd)
    (fun v x => tensM_mk _ _ _ v x) (fun a g => κ i dc Dd ρ π l a g) hκ z x hz

/- English proof (translation)
The claim follows from `finRhoAt i dc Dd ρ π l (cobFin_of i dc Dd l hO) (latBasis_of i dc Dd ρ π l hf hr)`.
-/
theorem finRhoAt_of (l : K.Col i dc) (hO : KHf.OrbC i dc (ρV i dc Dd l)) (hf : FinFf i dc Dd l)
    (hr : RankFf i dc Dd ρ π l) :
    KHf.FinRhoAt i dc Dd.r Dd.χ (Ffr i dc Dd) (jr i dc ρ π) (κ i dc Dd ρ π) (κz i dc Dd ρ π) l := finRhoAt i dc Dd ρ π l (cobFin_of i dc Dd l hO) (latBasis_of i dc Dd ρ π l hf hr)

end Rec

section Unr

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.RepresentationBoundsCohomology.FIN ReciprocityTheory.Gal

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (δO : D.nd.O i)

abbrev Icol (l : K.Col i dc) : Subgroup ↥(Γc i dc l) :=
  (Ine (F := D.host.E) (K.Aw i dc (K.colIdx i dc l))).subgroupOf (decs D.host.E (K.Aw i dc) (K.colIdx i dc l))

def UnrAdm (l : K.Col i dc) (f : ↥(Γc i dc l) → D.nd.O i) : Prop :=
  (∀ g h, f (g * h) = f g + f h) ∧ (∀ g ∈ Icol i dc l, f g = 0) ∧
    ∀ hn : K.plOf i dc (K.colIdx i dc l) ∈ placesOver D.host.E (D.nd.l i),
      Continuous fun g => KHf.eK (D.nbr i _ hn)
        (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (f (Br.iota D.nbr i _ hn g)))

def UnrHom (l : K.Col i dc) : Prop := ∃ f, UnrAdm i dc l f ∧ ∃ g, f g = 1

def uzOf (l : K.Col i dc) (f : ↥(Γc i dc l) → D.nd.O i) (hf : ∀ g h, f (g * h) = f g + f h) :
    Formalism.NG.coZ1s (Representation.trivial (D.nd.O i) ↥(Γc i dc l) ↥(Ideal.span {δO})) :=
  ⟨fun g => ⟨δO * f g, Ideal.mem_span_singleton'.2 ⟨f g, mul_comm _ _⟩⟩, fun g h => by
    apply Subtype.ext
    simp [hf, mul_add]⟩

def UnrFinIn (l : K.Col i dc) : Prop :=
  ∀ f (hf : UnrAdm i dc l f), Submodule.mkQ _ (uzOf i dc δO l f hf.1) ∈ KHf.HfE₂ i dc δO l

def uCol (l : K.Col i dc) : ↥(Γc i dc l) → D.nd.O i :=
  if h : UnrHom i dc l then h.choose else 0

/- English proof (translation)
Distinguish the cases in `hU : UnrHom i dc l`. Establish `e : uCol i dc l = hU.choose` using `dif_pos hU`. Rewrite using `[e]`. Take `⟨⟨hadd, _, _⟩, _⟩` from `hU.choose_spec`. Conclude with `hadd g h`.

Establish `e : uCol i dc l = 0` using `dif_neg hU`. Rewrite using `[e]`. Simplify using the standard rewrite rules.
-/
theorem uCol_add (l : K.Col i dc) (g h : ↥(Γc i dc l)) : uCol i dc l (g * h) = uCol i dc l g + uCol i dc l h := by
  by_cases hU : UnrHom i dc l
  · have e : uCol i dc l = hU.choose := dif_pos hU
    rw [e]
    obtain ⟨⟨hadd, _, _⟩, _⟩ := hU.choose_spec
    exact hadd g h
  · have e : uCol i dc l = 0 := dif_neg hU
    rw [e]
    simp

def u (l : K.Col i dc) (g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om) : D.nd.O i :=
  if h : g ∈ Γc i dc l then uCol i dc l ⟨g, h⟩ else 0

def uz (l : K.Col i dc) : Formalism.NG.coZ1s (Representation.trivial (D.nd.O i) ↥(Γc i dc l) ↥(Ideal.span {δO})) :=
  uzOf i dc δO l (uCol i dc l) (uCol_add i dc l)

/- English proof (translation)
Unfold `u`. Rewrite using `[dif_pos g.2]`.
-/
theorem u_mem (l : K.Col i dc) (g : ↥(Γc i dc l)) : u i dc l g = uCol i dc l g := by
  unfold u
  rw [dif_pos g.2]

/- English proof (translation)
Establish `e : uCol i dc l = hU.choose` using `dif_pos hU`. Rewrite using `[e]`. Conclude with `hU.choose_spec`.
-/
theorem uCol_spec (l : K.Col i dc) (hU : UnrHom i dc l) :
    UnrAdm i dc l (uCol i dc l) ∧ ∃ g, uCol i dc l g = 1 := by
  have e : uCol i dc l = hU.choose := dif_pos hU
  rw [e]
  exact hU.choose_spec

/- English proof (translation)
Introduce `g hg`. Rewrite using `[u_mem]`. Take `⟨⟨_, hI, _⟩, _⟩` from `uCol_spec i dc l hU`. Conclude with `hI g hg`.
-/
theorem u_I (l : K.Col i dc) (hU : UnrHom i dc l) : ∀ g ∈ Icol i dc l, u i dc l (g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om) = 0 := by
  intro g hg
  rw [u_mem]
  obtain ⟨⟨_, hI, _⟩, _⟩ := uCol_spec i dc l hU
  exact hI g hg

/- English proof (translation)
Take `⟨_, g, hg⟩` from `uCol_spec i dc l hU`. Conclude with `⟨g, g.2, by rw [u_mem]; exact hg⟩`.
-/
theorem u_one (l : K.Col i dc) (hU : UnrHom i dc l) : ∃ g ∈ Γc i dc l, u i dc l g = 1 := by
  obtain ⟨_, g, hg⟩ := uCol_spec i dc l hU
  exact ⟨g, g.2, by rw [u_mem]; exact hg⟩

/- English proof (translation)
Introduce `l`. Conclude with `hF l (uCol i dc l) (uCol_spec i dc l (hU l)).1`.
-/
theorem unrFin (hU : ∀ l, UnrHom i dc l) (hF : ∀ l, UnrFinIn i dc δO l) : KHf.UnrFin i dc δO (uz i dc δO) := by
  intro l
  exact hF l (uCol i dc l) (uCol_spec i dc l (hU l)).1

end Unr

end Formalism.MainNotions.N.KFin
