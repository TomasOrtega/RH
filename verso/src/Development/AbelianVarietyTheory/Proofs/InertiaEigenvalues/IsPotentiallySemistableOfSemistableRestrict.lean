import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemClosureMulVOfFinrankEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

/- English proof (translation)
Set `e : DpstUr P (resTo ρ hK) ≃ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ` to `{ toFun := fun x => toUr P ρ ⟨((toUr P _).symm x).1, (Dpst_resTo P ρ hK).le ((toUr P _).symm x).2⟩ invFun := fun x => toUr P _ ⟨((toUr P ρ).symm x).1, (Dpst_resTo P ρ hK).ge ((toUr P ρ).symm x).2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun _ => rfl rig …`. Rewrite using `[IsPst, IsPst, e.rank_eq]`.
-/
theorem isPst_resTo_iff_padic {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K K' : FinExt l} (hK : K.1 ≤ K'.1)
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) :
    IsPst P (resTo ρ hK) ↔ IsPst P ρ := by
  let e : DpstUr P (resTo ρ hK) ≃ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ :=
    { toFun := fun x =>
        toUr P ρ ⟨((toUr P _).symm x).1, (Dpst_resTo P ρ hK).le ((toUr P _).symm x).2⟩
      invFun := fun x =>
        toUr P _ ⟨((toUr P ρ).symm x).1, (Dpst_resTo P ρ hK).ge ((toUr P ρ).symm x).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [IsPst, IsPst, e.rank_eq]

/- English proof (translation)
Use `haveI := K.2`. Use `haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap (IntermediateField.inclusion_injective inf_le_left)`. Set `val : DpstUr P ρ →+ V ⊗[ℚ_[l]] Bst P` to `(Dpst P ρ).subtype.toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom`. Establish `hSD : Dst P ρ ≤ Dpst P ρ` using `fun s hs => (mem_Dpst P ρ).mpr ⟨K, fun g _ => (mem_Dst P ρ).mp hs g⟩`. Take `⟨b, hbS, hsp, hli⟩` from `exists_linearIndependent ↥(MaximalUnramifiedExtension l) {y : DpstUr P ρ | val y ∈ Dst P ρ}`.

Use `haveI : Finite ↥b := hli.finite`. Use `letI : Fintype ↥b := Fintype.ofFinite _`. Establish `hspan : ∀ y : DpstUr P ρ, y ∈ Submodule.span ↥(MaximalUnramifiedExtension l) b → ∃ c : ↥b → ↥(MaximalUnramifiedExtension l), ∑ i, c i • (i : DpstUr P ρ) = y` using `fun y hy => by`. Rewrite using `[← Submodule.mem_span_range_iff_exists_fun, Subtype.range_coe]`. Conclude with `hy`.

Set `inc : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)` to `IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)`. Set `f : (↥b → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P` to `{ toFun := fun c => ∑ i, mulV P ℚ_[l] V (inc (c i)) (val i) map_add' := fun c c' => by simp [Finset.sum_add_distrib] map_smul' := fun q c => by`. Simplify using `only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => mulV_padic_smul P _ V q (inc (c i)) (val i) }`. Establish `hle : Dst P ρ ≤ LinearMap.range f`.

Introduce `s hs`. Take `⟨c, hc⟩` from `hspan (toUr P ρ ⟨s, hSD hs⟩) (hsp ▸ Submodule.subset_span hs)`. Establish `hfix : ∀ i, (c i : Om l) ∈ K.1` using `fun i => mem_of_GK_fixed fun g => by`. Use `semilinear_coord_fixed hli (fun a => ⟨_, galois_mem_Kur g a⟩) (actD P ρ g).toAddMonoidHom (fun a y => LinearMap.congr_fun (actD_mulD P ρ g a _ rfl) y) (fun j => Subtype.ext ((mem_Dst P ρ).mp (hbS j.2) g)) c (by rw [hc]; exact Subtype.ext ((mem_Dst P ρ).mp hs g)) i` as an intermediate fact. Conclude with `congrArg Subtype.val this`.

Use `⟨fun i => ⟨c i, hfix i, (c i).2⟩, ?_⟩` and prove the remaining obligations. Use `congrArg val hc` as an intermediate fact. Rewrite `this` using `[map_sum]`. Conclude with `this`. Establish `h1 : finrank ℚ_[l] ↥(Dst P ρ) ≤ Fintype.card ↥b * finrank ℚ_[l] ↥(K0 K)`.

Use `(Submodule.finrank_mono hle).trans ((LinearMap.finrank_range_le f).trans ?_)` and prove the remaining obligations. Simplify using `[Module.finrank_pi_fintype]`. Establish `h2 : finrank ℚ_[l] ↥(Dst P ρ) = finrank ℚ_[l] V * finrank ℚ_[l] ↥(K0 K)`. Rewrite using `[show finrank ℚ_[l] ↥(Dst P ρ) = _ from hS, mul_comm]`. Establish `h3 : finrank ℚ_[l] V ≤ Fintype.card ↥b` using `Nat.le_of_mul_le_mul_right (h2 ▸ h1) Module.finrank_pos`.

Conclude with `h3.trans hli.fintype_card_le_finrank`.
-/
theorem finrank_le_finrank_DpstUr_of_isSst {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] (hS : IsSst P ρ) :
    finrank ℚ_[l] V ≤ finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) := by
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  let val : DpstUr P ρ →+ V ⊗[ℚ_[l]] Bst P :=
    (Dpst P ρ).subtype.toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom
  have hSD : Dst P ρ ≤ Dpst P ρ := fun s hs => (mem_Dpst P ρ).mpr ⟨K, fun g _ => (mem_Dst P ρ).mp hs g⟩
  obtain ⟨b, hbS, hsp, hli⟩ := exists_linearIndependent ↥(MaximalUnramifiedExtension l) {y : DpstUr P ρ | val y ∈ Dst P ρ}
  haveI : Finite ↥b := hli.finite
  letI : Fintype ↥b := Fintype.ofFinite _
  have hspan : ∀ y : DpstUr P ρ, y ∈ Submodule.span ↥(MaximalUnramifiedExtension l) b → ∃ c : ↥b → ↥(MaximalUnramifiedExtension l),
      ∑ i, c i • (i : DpstUr P ρ) = y := fun y hy => by
    rw [← Submodule.mem_span_range_iff_exists_fun, Subtype.range_coe]; exact hy
  let inc : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) := IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)
  let f : (↥b → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P :=
    { toFun := fun c => ∑ i, mulV P ℚ_[l] V (inc (c i)) (val i)
      map_add' := fun c c' => by simp [Finset.sum_add_distrib]
      map_smul' := fun q c => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => mulV_padic_smul P _ V q (inc (c i)) (val i) }
  have hle : Dst P ρ ≤ LinearMap.range f := by
    intro s hs
    obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨s, hSD hs⟩) (hsp ▸ Submodule.subset_span hs)
    have hfix : ∀ i, (c i : Om l) ∈ K.1 := fun i => mem_of_GK_fixed fun g => by
      have := semilinear_coord_fixed hli (fun a => ⟨_, galois_mem_Kur g a⟩)
        (actD P ρ g).toAddMonoidHom
        (fun a y => LinearMap.congr_fun (actD_mulD P ρ g a _ rfl) y)
        (fun j => Subtype.ext ((mem_Dst P ρ).mp (hbS j.2) g)) c
        (by rw [hc]; exact Subtype.ext ((mem_Dst P ρ).mp hs g)) i
      exact congrArg Subtype.val this
    refine ⟨fun i => ⟨c i, hfix i, (c i).2⟩, ?_⟩
    have := congrArg val hc
    rw [map_sum] at this
    exact this
  have h1 : finrank ℚ_[l] ↥(Dst P ρ) ≤ Fintype.card ↥b * finrank ℚ_[l] ↥(K0 K) := by
    refine (Submodule.finrank_mono hle).trans ((LinearMap.finrank_range_le f).trans ?_)
    simp [Module.finrank_pi_fintype]
  have h2 : finrank ℚ_[l] ↥(Dst P ρ) = finrank ℚ_[l] V * finrank ℚ_[l] ↥(K0 K) := by
    rw [show finrank ℚ_[l] ↥(Dst P ρ) = _ from hS, mul_comm]
  have h3 : finrank ℚ_[l] V ≤ Fintype.card ↥b :=
    Nat.le_of_mul_le_mul_right (h2 ▸ h1) Module.finrank_pos
  exact h3.trans hli.fintype_card_le_finrank

/- English proof (translation)
Introduce `l _ P AI T K K' hK V _ _ _ ρ hS`. Take `⟨hdom, hreg, -⟩` from `GlobalTheory.Pst.stRegular l P AI ⟨T⟩`. Establish `hup` using `GlobalTheory.PstRank.rank_DpstUr_le P hdom hreg (resTo ρ hK)`. Use `haveI : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (resTo ρ hK)) := Module.rank_lt_aleph0_iff.mp (hup.trans_lt (Cardinal.nat_lt_aleph0 _))`. Rewrite using `[← isPst_resTo_iff_padic P hK ρ, GlobalTheory.Pst.isPst_iff]`.

Use `⟨inferInstance, le_antisymm ?_ (finrank_le_finrank_DpstUr_of_isSst P _ hS)⟩` and prove the remaining obligations. Rewrite `hup` using `[← finrank_eq_rank]`. Conclude with `hup` after adjusting the coercions.
-/
theorem isPst_of_isSst_resTo : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K K' : FinExt l) (hK : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P (resTo ρ hK) → IsPst P ρ := by
  intro l _ P AI T K K' hK V _ _ _ ρ hS
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  have hup := GlobalTheory.PstRank.rank_DpstUr_le P hdom hreg (resTo ρ hK)
  haveI : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (resTo ρ hK)) :=
    Module.rank_lt_aleph0_iff.mp (hup.trans_lt (Cardinal.nat_lt_aleph0 _))
  rw [← isPst_resTo_iff_padic P hK ρ, GlobalTheory.Pst.isPst_iff]
  refine ⟨inferInstance, le_antisymm ?_ (finrank_le_finrank_DpstUr_of_isSst P _ hS)⟩
  rw [← finrank_eq_rank] at hup
  exact_mod_cast hup

end GlobalTheory.PMon

end
