import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.CoefProd
import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Model

section dual

variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [CharZero K]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma toK_eq_map {σ : Type} (f : MvPolynomial σ O) : toK O K f = map (algebraMap O K) f := rfl

/- English proof (translation)
Use `Module.IsTorsionFree.of_smul_eq_zero fun a f h => ?_` and prove the remaining obligations. Rewrite `h` using `[← algebraMap_smul K a f, smul_eq_zero]`. Break down `h with h | h` into its components or cases. Use the proof step `left; exact (IsFractionRing.injective O K) (by rw [h, map_zero])`. Use `right`.

Conclude with `h`.
-/
lemma polyK_torsionFree {σ : Type} : Module.IsTorsionFree O (MvPolynomial σ K) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun a f h => ?_
  rw [← algebraMap_smul K a f, smul_eq_zero] at h
  rcases h with h | h
  · left; exact (IsFractionRing.injective O K) (by rw [h, map_zero])
  · right; exact h

/- English proof (translation)
Establish `hM : ((dualWeyl O n n ν).map (toK O K)).FG`. Apply `Submodule.FG.map` to reduce the goal to its premises. Take `⟨b, hb, -⟩` from `sSBasis O n n ν`. Rewrite using `[← hb.2.1]`. Use `(sSIdxFinite n n ν).to_subtype` as an intermediate fact.

Conclude with `Submodule.fg_span (Set.finite_range b)`. Establish `hle : (weyl O n n le_rfl ν).map (toK O K) ≤ (dualWeyl O n n ν).map (toK O K)` using `Submodule.map_mono (weylLeDual O n n le_rfl ν hν)`. Use `isNoetherian_of_fg_of_noetherian _ hM` as an intermediate fact. Establish `h` using `IsNoetherian.noetherian (((weyl O n n le_rfl ν).map (toK O K)).comap ((dualWeyl O n n ν).map (toK O K)).subtype)`. Establish `h2` using `h.map ((dualWeyl O n n ν).map (toK O K)).subtype`.

Rewrite `h2` using `[Submodule.map_comap_subtype, inf_eq_right.mpr hle]`. Then use the resulting hypothesis.
-/
lemma weylK_fg {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) :
    ((weyl O n n le_rfl ν).map (toK O K)).FG := by
  have hM : ((dualWeyl O n n ν).map (toK O K)).FG := by
    apply Submodule.FG.map
    obtain ⟨b, hb, -⟩ := sSBasis O n n ν
    rw [← hb.2.1]
    have := (sSIdxFinite n n ν).to_subtype
    exact Submodule.fg_span (Set.finite_range b)
  have hle : (weyl O n n le_rfl ν).map (toK O K) ≤ (dualWeyl O n n ν).map (toK O K) :=
    Submodule.map_mono (weylLeDual O n n le_rfl ν hν)
  have := isNoetherian_of_fg_of_noetherian _ hM
  have h := IsNoetherian.noetherian (((weyl O n n le_rfl ν).map (toK O K)).comap
    ((dualWeyl O n n ν).map (toK O K)).subtype)
  have h2 := h.map ((dualWeyl O n n ν).map (toK O K)).subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2

end dual

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _ n ν hν`. Use `set c := fockR (hw K (le_rfl : n ≤ n) ν) (hw K le_rfl ν) with hc`. Use `set D := (weyl O n n le_rfl ν).map (toK O K) with hD`. Establish `: Module.IsTorsionFree O (MvPolynomial (Fin n × Fin n) K)` using `polyK_torsionFree`. Establish `: Module.Finite O D` using `Module.Finite.iff_fg.mpr (weylK_fg ν hν)`.

Take `⟨N, bD⟩` from `Module.basisOfFiniteTypeTorsionFree' (R := O) (M := D)`. Use `set e : Fin N → MvPolynomial (Fin n × Fin n) K := fun i => (bD i : MvPolynomial (Fin n × Fin n) K) with he_def`. Establish `he : ∀ i, e i ∈ D` using `fun i => (bD i).2`. Establish `hDV : ∀ x ∈ D, x ∈ dualWeyl K n n ν`. Introduce `x hx`.

Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hx`. Rewrite using `[toK_eq_map]`. Conclude with `weylLeDual K n n le_rfl ν hν (sw_weyl_map (algebraMap O K) le_rfl ν y hy)`. Establish `hrep : ∀ x (hx : x ∈ D), x = ∑ i, bD.repr ⟨x, hx⟩ i • e i`. Introduce `x hx`.

Establish `h` using `congrArg Subtype.val (bD.sum_repr ⟨x, hx⟩)`. Rewrite `h` using `[Submodule.coe_sum]`. Simplify `h.symm` using `[he_def]`. Establish `hsm : ∀ (a : O) (f : MvPolynomial (Fin n × Fin n) K), a • f = algebraMap O K a • f` using `fun a f => (algebraMap_smul K a f).symm`. Establish `hDspan : ∀ x ∈ D, x ∈ Submodule.span K (Set.range e)`.

Introduce `x hx`. Rewrite using `[hrep x hx]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hsm]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Establish `hspan : dualWeyl K n n ν ≤ Submodule.span K (Set.range e)`. Rewrite using `[← sw_weyl_eq K n n le_rfl ν hν]`. Unfold `weyl`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, rfl⟩`.

Apply `hDspan` to reduce the goal to its premises. Use `Submodule.mem_map.mpr ⟨applyWord O w (hw O le_rfl ν), Submodule.subset_span ⟨w, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[toK_eq_map, ← lclosedeq_applyWord_map, lclosedeq_hw_map]`. Establish `hliO : LinearIndependent O e` using `bD.linearIndependent.map' D.subtype (Submodule.ker_subtype D)`. Establish `hli : LinearIndependent K e` using `(LinearIndependent.iff_fractionRing O K).mp hliO`.

Use `set W := Submodule.span K (Set.range e) with hW`. Establish `hWV : W = dualWeyl K n n ν`. Use `le_antisymm ?_ hspan` and prove the remaining obligations. Rewrite using `[hW, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `hDV _ (he i)`. Set `bW : Module.Basis (Fin N) K W` to `Module.Basis.span hli`. Establish `hbW : ∀ i, (bW i : MvPolynomial (Fin n × Fin n) K) = e i` using `fun i => congrArg Subtype.val (Module.Basis.span_apply hli i)`. Set `Bf : LinearMap.BilinForm K W` to `LinearMap.mk₂ K (fun x y : W => fockR (x : MvPolynomial (Fin n × Fin n) K) y) (fun x x' y => by simp [fockR_add_left]) (fun a x y => by simp [fockR_smul_left]) (fun x y y' => by simp [fockR_add_right]) (fun a x y => by simp [fockR_smul_right])`. Establish `hBf : ∀ x y : W, Bf x y = fockR (x : MvPolynomial (Fin n × Fin n) K) y` using `fun _ _ => rfl`.

Establish `hnd : Bf.Nondegenerate`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Apply `Subtype.ext` to reduce the goal to its premises. Use `Top.nondegK K n n le_rfl ν hν x.1 (hWV ▸ x.2) fun P hP => ?_` and prove the remaining obligations.

Rewrite using `[fockR_symm]`. Conclude with `hx ⟨P, hWV ▸ hP⟩`. Introduce `y hy`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `Top.nondegK K n n le_rfl ν hν y.1 (hWV ▸ y.2) fun P hP => hy ⟨P, hWV ▸ hP⟩`.

Set `d` to `Bf.dualBasis hnd bW`. Establish `hd : ∀ i k, fockR (e i) (d k : MvPolynomial (Fin n × Fin n) K) = if i = k then 1 else 0`. Introduce `i k`. Establish `h` using `LinearMap.BilinForm.apply_dualBasis_left hnd bW k i`. Rewrite `h` using `[hBf, hbW, fockR_symm]`.

Conclude with `h`. Use `⟨Fin N, inferInstance, inferInstance, e, fun k => c • (d k : MvPolynomial (Fin n × Fin n) K), he, ?_, ?_, hspan⟩` and prove the remaining obligations. Introduce `k`. Establish `hkV : c • (d k : MvPolynomial (Fin n × Fin n) K) ∈ dualWeyl K n n ν` using `Submodule.smul_mem _ _ (hWV ▸ (d k).2)`. Use `Top.dualWeylIn O K n n le_rfl ν hν _ hkV fun P hP => ⟨bD.repr ⟨P, hP⟩ k, ?_⟩` and prove the remaining obligations.

Use `show fockR P (c • (d k : MvPolynomial (Fin n × Fin n) K)) = _`. Use `conv_lhs => rw [hrep P hP]`. Rewrite using `[fockR_sum_left]`. Repeatedly rewrite using `[hsm, fockR_smul_left, fockR_smul_right, hd]`. Simplify using `[hc]`.

Introduce `i k`. Rewrite using `[fockR_smul_right, hd]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem dual_bases_holds : DualBases := by
  intro O K _ _ _ _ _ _ _ n ν hν
  classical
  set c := fockR (hw K (le_rfl : n ≤ n) ν) (hw K le_rfl ν) with hc
  set D := (weyl O n n le_rfl ν).map (toK O K) with hD
  have : Module.IsTorsionFree O (MvPolynomial (Fin n × Fin n) K) := polyK_torsionFree
  have : Module.Finite O D := Module.Finite.iff_fg.mpr (weylK_fg ν hν)
  obtain ⟨N, bD⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := D)
  set e : Fin N → MvPolynomial (Fin n × Fin n) K := fun i => (bD i : MvPolynomial (Fin n × Fin n) K) with he_def
  have he : ∀ i, e i ∈ D := fun i => (bD i).2
  have hDV : ∀ x ∈ D, x ∈ dualWeyl K n n ν := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    rw [toK_eq_map]
    exact weylLeDual K n n le_rfl ν hν (sw_weyl_map (algebraMap O K) le_rfl ν y hy)
  have hrep : ∀ x (hx : x ∈ D), x = ∑ i, bD.repr ⟨x, hx⟩ i • e i := by
    intro x hx
    have h := congrArg Subtype.val (bD.sum_repr ⟨x, hx⟩)
    rw [Submodule.coe_sum] at h
    simpa [he_def] using h.symm
  have hsm : ∀ (a : O) (f : MvPolynomial (Fin n × Fin n) K), a • f = algebraMap O K a • f :=
    fun a f => (algebraMap_smul K a f).symm
  have hDspan : ∀ x ∈ D, x ∈ Submodule.span K (Set.range e) := by
    intro x hx
    rw [hrep x hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : dualWeyl K n n ν ≤ Submodule.span K (Set.range e) := by
    rw [← sw_weyl_eq K n n le_rfl ν hν]
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    apply hDspan
    refine Submodule.mem_map.mpr ⟨applyWord O w (hw O le_rfl ν), Submodule.subset_span ⟨w, rfl⟩, ?_⟩
    rw [toK_eq_map, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
  have hliO : LinearIndependent O e := bD.linearIndependent.map' D.subtype (Submodule.ker_subtype D)
  have hli : LinearIndependent K e := (LinearIndependent.iff_fractionRing O K).mp hliO
  set W := Submodule.span K (Set.range e) with hW
  have hWV : W = dualWeyl K n n ν := by
    refine le_antisymm ?_ hspan
    rw [hW, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hDV _ (he i)
  let bW : Module.Basis (Fin N) K W := Module.Basis.span hli
  have hbW : ∀ i, (bW i : MvPolynomial (Fin n × Fin n) K) = e i := fun i =>
    congrArg Subtype.val (Module.Basis.span_apply hli i)
  let Bf : LinearMap.BilinForm K W := LinearMap.mk₂ K (fun x y : W => fockR (x : MvPolynomial (Fin n × Fin n) K) y)
    (fun x x' y => by simp [fockR_add_left]) (fun a x y => by simp [fockR_smul_left])
    (fun x y y' => by simp [fockR_add_right]) (fun a x y => by simp [fockR_smul_right])
  have hBf : ∀ x y : W, Bf x y = fockR (x : MvPolynomial (Fin n × Fin n) K) y := fun _ _ => rfl
  have hnd : Bf.Nondegenerate := by
    constructor
    · intro x hx
      apply Subtype.ext
      refine Top.nondegK K n n le_rfl ν hν x.1 (hWV ▸ x.2) fun P hP => ?_
      rw [fockR_symm]
      exact hx ⟨P, hWV ▸ hP⟩
    · intro y hy
      apply Subtype.ext
      exact Top.nondegK K n n le_rfl ν hν y.1 (hWV ▸ y.2) fun P hP => hy ⟨P, hWV ▸ hP⟩
  let d := Bf.dualBasis hnd bW
  have hd : ∀ i k, fockR (e i) (d k : MvPolynomial (Fin n × Fin n) K) = if i = k then 1 else 0 := by
    intro i k
    have h := LinearMap.BilinForm.apply_dualBasis_left hnd bW k i
    rw [hBf, hbW, fockR_symm] at h
    exact h
  refine ⟨Fin N, inferInstance, inferInstance, e, fun k => c • (d k : MvPolynomial (Fin n × Fin n) K),
    he, ?_, ?_, hspan⟩
  · intro k
    have hkV : c • (d k : MvPolynomial (Fin n × Fin n) K) ∈ dualWeyl K n n ν :=
      Submodule.smul_mem _ _ (hWV ▸ (d k).2)
    refine Top.dualWeylIn O K n n le_rfl ν hν _ hkV fun P hP => ⟨bD.repr ⟨P, hP⟩ k, ?_⟩
    show fockR P (c • (d k : MvPolynomial (Fin n × Fin n) K)) = _
    conv_lhs => rw [hrep P hP]
    rw [fockR_sum_left]
    simp_rw [hsm, fockR_smul_left, fockR_smul_right, hd]
    simp [hc]
  · intro i k
    rw [fockR_smul_right, hd]
    split_ifs <;> simp

end Formalism.L2.PairingIndexBounds.Ent
