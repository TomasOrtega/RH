import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedLengthLatticeQuotientBaseChangeEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeProjectionBaseChangeDvrCommStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeInfSubspaceBaseChangeDvrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthFinsetSupEqSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFormLatticeEqSumLocalisedLatticesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenspaceSumDisjointComplStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEmbeddingIntegersResCharUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthLatticeProjectionQuotientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodEigSumSupComplEigSumEqTopStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormEqSumLocalisationProjectionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgInfSupOfIsComplStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanImageSemilinearLatticeEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DisjointFinsetSupOfSupIndepSupStatement

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoinSum

variable {D : D7} {M : MtFam D}

def qLen {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (G L B : Submodule O V) : ℕ∞ :=
  Module.length O (↥(G ⊓ (L ⊔ B)) ⧸ (L ⊓ G).comap (G ⊓ (L ⊔ B)).subtype)

def gK (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} (i : {i // i ∈ D.nd.locs j w})
    (Y : Set (D.nd.X i.1)) : Submodule (FractionRing (T.B.Oc j w)) (T.B.V j w) :=
  haveI : RingHomSurjective (T.phK j w i.1 i.2).toRingHom := ⟨(T.phK j w i.1 i.2).surjective⟩
  (D.nd.eigSum i.1 Y).map (T.Psi j w i.1 i.2)

/- English proof (translation)
Use `haveI : RingHomSurjective (T.phK j w i.1 i.2).toRingHom := ⟨(T.phK j w i.1 i.2).surjective⟩`. Unfold `gK`. Conclude with `Submodule.mem_map`.
-/
theorem mem_gK (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} (i : {i // i ∈ D.nd.locs j w})
    (Y : Set (D.nd.X i.1)) (z : T.B.V j w) :
    z ∈ gK T i Y ↔ ∃ y ∈ D.nd.eigSum i.1 Y, T.Psi j w i.1 i.2 y = z := by
  haveI : RingHomSurjective (T.phK j w i.1 i.2).toRingHom := ⟨(T.phK j w i.1 i.2).surjective⟩
  unfold gK
  exact Submodule.mem_map

def lO (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} (i : {i // i ∈ D.nd.locs j w}) :
    Submodule (T.B.Oc j w) (T.B.V j w) :=
  haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)
  (D.nd.MtIn i.1).map (psiO T i.2)

/- English proof (translation)
The claim follows from `RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2) ((D.nd.eigSum i.1 Y).restrictScalars (D.nd.O i.1)).map (psiO T i.2) = (gK T i Y).restrictScalars (T.B.Oc j w) := map_psiO_rs T i.2 _ _ (fun y => by rw [mem_gK] exact ⟨fun hy => ⟨y, hy, rfl⟩, fun ⟨y', hy', e⟩ => T.Psi_inj j w i.1 i.2 …`.
-/
theorem map_rs_gK (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} (i : {i // i ∈ D.nd.locs j w})
    (Y : Set (D.nd.X i.1)) :
    haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)
    ((D.nd.eigSum i.1 Y).restrictScalars (D.nd.O i.1)).map (psiO T i.2) =
      (gK T i Y).restrictScalars (T.B.Oc j w) :=
  map_psiO_rs T i.2 _ _ (fun y => by
      rw [mem_gK]
      exact ⟨fun hy => ⟨y, hy, rfl⟩, fun ⟨y', hy', e⟩ => T.Psi_inj j w i.1 i.2 e ▸ hy'⟩)
    (fun z hz => by
      obtain ⟨y, -, e⟩ := (mem_gK T i Y z).1 hz
      exact ⟨y, e⟩)

/- English proof (translation)
Use `haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)`. Unfold `qLen`. Rewrite using `[← map_rs_gK, ← map_rs_gK]`. Unfold `lO`. Rewrite using `[← Submodule.map_sup, ← Submodule.map_inf _ (psiO_injective T i.2), ← Submodule.map_inf _ (psiO_injective T i.2)]`.

Conclude with `NCov.length_quot_map (T.phO j w i.1 i.2) (psiO T i.2) (psiO_injective T i.2) _ _`.
-/
theorem length_loc (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} (i : {i // i ∈ D.nd.locs j w}) :
    qLen ((gK T i ↑(D.nd.Zgood i.1)).restrictScalars (T.B.Oc j w)) (lO T i)
      ((gK T i (↑(D.nd.Zgood i.1))ᶜ).restrictScalars (T.B.Oc j w)) =
    Module.length (D.nd.O i.1) (↥(D.nd.MtUp i.1) ⧸ (D.nd.MtLow i.1).comap (D.nd.MtUp i.1).subtype) := by
  haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)
  unfold qLen
  rw [← map_rs_gK, ← map_rs_gK]
  unfold lO
  rw [← Submodule.map_sup, ← Submodule.map_inf _ (psiO_injective T i.2),
    ← Submodule.map_inf _ (psiO_injective T i.2)]
  exact NCov.length_quot_map (T.phO j w i.1 i.2) (psiO T i.2) (psiO_injective T i.2) _ _

/- English proof (translation)
Establish `hl : D.nd.l i.1 = D.what₂.places.resChar w`. Rewrite using `[← D.nd.w_l i.1, ((D.nd.locs_mem j w i.1).1 i.2).2]`. Rewrite using `[length_loc, NCov.length_quot_natCast (T.phO j w i.1 i.2), ← hl]`. Both sides reduce to the same expression.
-/
theorem etaLoc_eq_loc (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} (i : {i // i ∈ D.nd.locs j w}) :
    D.nd.etaLoc i.1 = ((qLen ((gK T i ↑(D.nd.Zgood i.1)).restrictScalars (T.B.Oc j w)) (lO T i)
      ((gK T i (↑(D.nd.Zgood i.1))ᶜ).restrictScalars (T.B.Oc j w))).toNat : ℚ) /
      ((Module.length (T.B.Oc j w) (T.B.Oc j w ⧸ Ideal.span {((D.what₂.places.resChar w : ℕ) : T.B.Oc j w)})).toNat : ℚ) := by
  have hl : D.nd.l i.1 = D.what₂.places.resChar w := by
    rw [← D.nd.w_l i.1, ((D.nd.locs_mem j w i.1).1 i.2).2]
  rw [length_loc, NCov.length_quot_natCast (T.phO j w i.1 i.2), ← hl]
  rfl

/- English proof (translation)
Take `⟨hj, hw⟩` from `(D.nd.locs_mem j w i).1 h`. Rewrite using `[D.nd.mu_w i, hj, hw]`. Conclude with `hZ`.
-/
theorem zrat_loc {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (hZ : ZRat D (D.what₂.muTw w) j) : ZRat D (D.nd.mu i) (D.nd.j i) := by
  obtain ⟨hj, hw⟩ := (D.nd.locs_mem j w i).1 h
  rw [D.nd.mu_w i, hj, hw]
  exact hZ

/- English proof (translation)
Substitute `hμ` using the available equality. Substitute `hj` using the available equality. Conclude with `⟨Iff.rfl, Iff.rfl⟩`.
-/
theorem cast_mem_rationalFormSubspace_goodPart_iff {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ = μ') (hj : j = j')
    (e : D.what₂.MtL μ j = D.what₂.MtL μ' j') (x : D.what₂.MtL μ j) :
    (cast e x ∈ ratSub D μ' j' (Idx.Z0 D μ' j') ↔ x ∈ ratSub D μ j (Idx.Z0 D μ j)) ∧
    (cast e x ∈ ratSub D μ' j' (Idx.Z0 D μ' j')ᗮ ↔ x ∈ ratSub D μ j (Idx.Z0 D μ j)ᗮ) := by
  subst hμ; subst hj; exact ⟨Iff.rfl, Iff.rfl⟩

/- English proof (translation)
Take `⟨hj, hw⟩` from `(D.nd.locs_mem j w i).1 h`. Establish `hμ : D.what₂.muTw w = D.nd.mu i` using `by rw [D.nd.mu_w i, hw]`. Establish `c` using `cast_mem_rationalFormSubspace_goodPart_iff (D := D) hμ hj.symm (mtL_eq D h).symm y`. Conclude with `⟨c.1.2, c.2.2⟩`.
-/
theorem castInv_mem {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (y : D.what₂.MtL (D.what₂.muTw w) j) :
    (y ∈ ratSub D (D.what₂.muTw w) j (Idx.Z0 D (D.what₂.muTw w) j) →
      castMtInv D h y ∈ ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i))) ∧
    (y ∈ ratSub D (D.what₂.muTw w) j (Idx.Z0 D (D.what₂.muTw w) j)ᗮ →
      castMtInv D h y ∈ ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i))ᗮ) := by
  obtain ⟨hj, hw⟩ := (D.nd.locs_mem j w i).1 h
  have hμ : D.what₂.muTw w = D.nd.mu i := by rw [D.nd.mu_w i, hw]
  have c := cast_mem_rationalFormSubspace_goodPart_iff (D := D) hμ hj.symm (mtL_eq D h).symm y
  exact ⟨c.1.2, c.2.2⟩

/- English proof (translation)
Introduce `D M T j w h1 h2 hw hstd hlat hZ hSP`. Rewrite using `[D.etaJ_tie j w h1 h2]`. Use `set F := (D.nd.locs j w).attach with hF`. Use `set U := ratSub D (D.what₂.muTw w) j (Idx.Z0 D (D.what₂.muTw w) j) with hU`. Use `set U' := ratSub D (D.what₂.muTw w) j (Idx.Z0 D (D.what₂.muTw w) j)ᗮ with hU'`.

Use `set G' := Submodule.span (FractionRing (T.B.Oc j w)) (T.B.iV j w '' (U : Set _)) with hG'`. Use `set B' := Submodule.span (FractionRing (T.B.Oc j w)) (T.B.iV j w '' (U' : Set _)) with hB'`. Use `set GK : {i // i ∈ D.nd.locs j w} → Submodule (FractionRing (T.B.Oc j w)) (T.B.V j w) := fun i => gK T i ↑(D.nd.Zgood i.1) with hGK`. Use `set BK : {i // i ∈ D.nd.locs j w} → Submodule (FractionRing (T.B.Oc j w)) (T.B.V j w) := fun i => gK T i (↑(D.nd.Zgood i.1))ᶜ with hBK`. Establish `hfin : ∀ i ∈ F, qLen ((GK i).restrictScalars (T.B.Oc j w)) (lO T i) ((BK i).restrictScalars (T.B.Oc j w)) ≠ ⊤`.

Introduce `i _`. Rewrite using `[hGK, hBK]`. Simplify using `only []`. Rewrite using `[length_loc]`. Establish `hZi` using `zrat_loc i.2 hZ`.

Establish `hfg : (D.nd.MtIn i.1).FG`. Unfold `NData.MtIn`. Rewrite using `[LinearMap.range_eq_map]`. Conclude with `Module.Finite.fg_top.map _`. Establish `hspan : Submodule.span (FractionRing (D.nd.O i.1)) (↑(D.nd.MtIn i.1) : Set (TensorProduct (D.nd.O i.1) (FractionRing (D.nd.O i.1)) (D.nd.Mt i.1))) = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce and unpack `z -`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `tmul k m`.

Establish `e : k ⊗ₜ[D.nd.O i.1] m = k • ((1 : FractionRing (D.nd.O i.1)) ⊗ₜ[D.nd.O i.1] m)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)`. Consider the case `add x y hx hy => exact Submodule.add_mem _ hx hy`.

Conclude with `(GlobalTheory.T.finiteLength_lattice_projection_quotient (D.nd.O i.1) (FractionRing (D.nd.O i.1)) _ (D.nd.MtIn i.1) _ _ hfg (GlobalTheory.T.heckeEigenspaceSum_disjoint_compl D i.1 _)).resolve_right (not_not.2 ⟨hspan, GlobalTheory.T.goodEigSum_sup_compl_eigSum_eq_top D i.1 hZi (hS …`. Take `⟨hint, hlw, hunit⟩` from `GlobalTheory.T.coeffEmbedding_integers_resChar_unit D M T.B j w`. Establish `hfinI` using `finite_chooseBasisIndex (D := D) j w`. Use `haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))`. Set `b` to `Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)`.

Use `haveI : FiniteDimensional D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := Module.Finite.of_basis b`. Establish `hb` using `T.B.iV_basis j w b`. Establish `hjinj : Function.Injective (D.what₂.jMt (D.what₂.muTw w) j)`. Establish `hli` using `(D.what₂.jMt_basis (D.what₂.muTw w) j b).1`. Use `(injective_iff_map_eq_zero _).2 fun y hy => ?_` and prove the remaining obligations.

Establish `hsum` using `b.sum_repr y`. Rewrite `hy` using `[← hsum, map_sum]`. Simplify using `only [LinearMap.map_smulₛₗ] at hy`. Establish `hz` using `Fintype.linearIndependent_iff.1 hli _ hy`. Rewrite using `[← hsum]`.

Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[(map_eq_zero_iff _ D.what₂.embLL.injective).1 (hz a), zero_smul]`. Establish `hc : IsCompl U U'`. Use `⟨Submodule.disjoint_def.2 fun x hx hx' => hjinj ?_, codisjoint_iff.2 hZ⟩` and prove the remaining obligations. Rewrite using `[map_zero]`.

Conclude with `Submodule.disjoint_def.1 (Submodule.orthogonal_disjoint _) _ hx hx'`. Establish `hup : Submodule.span (T.B.Oc j w) (T.B.iV j w '' (up D (D.what₂.muTw w) j : Set _)) = G'.restrictScalars (T.B.Oc j w) ⊓ (Submodule.span (T.B.Oc j w) (T.B.iV j w '' (lat D (D.what₂.muTw w) j : Set _)) ⊔ B'.restrictScalars (T.B.Oc j w))` using `GlobalTheory.T.latticeProjection_baseChange_dvr_comm D.what₂.LL (T.B.Oc j w) (T.B.ec j w) _ (T.B.V j w) (T.B.iV j w) _ b hb.1 hint (lat D (D.what₂.muTw w) j) U U' hc`. Establish `hlow : Submodule.span (T.B.Oc j w) (T.B.iV j w '' (low D (D.what₂.muTw w) j : Set _)) = Submodule.span (T.B.Oc j w) (T.B.iV j w '' (lat D (D.what₂.muTw w) j : Set _)) ⊓ G'.restrictScalars (T.B.Oc j w)` using `GlobalTheory.T.lattice_inf_subspace_baseChange_dvr D.what₂.LL (T.B.Oc j w) (T.B.ec j w) _ (T.B.V j w) (T.B.iV j w) _ b hb.1 hint (lat D (D.what₂.muTw w) j) U`. Establish `hlatFG : (lat D (D.what₂.muTw w) j).FG`. Establish `hfs : (genSet D (D.what₂.muTw w) j).Finite` using `Set.Finite.preimage hjinj.injOn (D.what₂.MtLat (D.what₂.muTw w) j).gen.finite_toSet`.

Conclude with `⟨hfs.toFinset, by rw [Set.Finite.coe_toFinset]; rfl⟩`. Establish `hupFG : (up D (D.what₂.muTw w) j).FG` using `GlobalTheory.T.fg_inf_sup_of_isCompl' D.what₂.LL _ (lat D (D.what₂.muTw w) j) U U' hlatFG hc`. Establish `hlowle : low D (D.what₂.muTw w) j ≤ up D (D.what₂.muTw w) j` using `le_inf inf_le_right (inf_le_left.trans le_sup_left)`. Establish `hlen` using `GlobalTheory.T.normalizedLength_latticeQuotient_baseChange_eq D.what₂.LL (T.B.Oc j w) (T.B.ec j w) _ (T.B.V j w) (T.B.iV j w) _ b hb.1 hint (D.plEq w) (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w) hlw hunit (up D (D.what₂.muTw w) j) (low D (D.what₂.muTw w) j) hupFG …`. Establish `hlatC : Submodule.span (T.B.Oc j w) (T.B.iV j w '' (lat D (D.what₂.muTw w) j : Set _)) = latC T.B j w` using `GlobalTheory.T.span_image_semilinear_lattice_eq D.what₂.LL (T.B.Oc j w) (T.B.ec j w) _ (T.B.V j w) (T.B.iV j w) hint _`.

Establish `hglob : etaRat D (D.what₂.muTw w) j w = ((qLen (G'.restrictScalars (T.B.Oc j w)) (latC T.B j w) (B'.restrictScalars (T.B.Oc j w))).toNat : ℚ) / ((Module.length (T.B.Oc j w) (T.B.Oc j w ⧸ Ideal.span {((D.what₂.places.resChar w : ℕ) : T.B.Oc j w)})).toNat : ℚ)`. Rewrite using `[show etaRat D (D.what₂.muTw w) j w = Formalism.L2.Col.lenUW (D.plEq w) (up D (D.what₂.muTw w) j) (low D (D.what₂.muTw w) j) from rfl, ← hlen]`. Unfold `lenUnit qLen`. Rewrite using `[hup, hlow, hlatC]`. Take `⟨hfd, -⟩` from `finrank_V T.B j w`.

Use `haveI := hfd`. Take `⟨hS, -, -⟩` from `gens_hypsTw T.B hstd h1 h2 (Or.inl hw)`. Establish `hinjK` using `IsFractionRing.injective (T.B.Oc j w) (FractionRing (T.B.Oc j w))`. Establish `hpart : ∀ (i : {i // i ∈ D.nd.locs j w}) (Y : Set (D.nd.X i.1)), gK T i Y ≤ NCov.part (heckeAlg T.B j w) (T.mx j w i.1)`. Introduce `i Y z hz`.

Take `⟨y, -, rfl⟩` from `(mem_gK T i Y z).1 hz`. Conclude with `(T.Psi_range j w i.1 i.2 _).2 ⟨y, rfl⟩`. Establish `hindP : F.SupIndep (fun i : {i // i ∈ D.nd.locs j w} => NCov.part (heckeAlg T.B j w) (T.mx j w i.1))`. Rewrite using `[Finset.supIndep_iff_disjoint_erase]`. Introduce `i _`.

Use `(NCov.disjoint_part_off hinjK hS (T.mx j w i.1)).mono_right (Finset.sup_le fun i' hi' => ?_)` and prove the remaining obligations. Establish `hne : T.mx j w i'.1 ≠ T.mx j w i.1` using `fun e => Finset.ne_of_mem_erase hi' (Subtype.ext (T.mx_inj j w i'.2 i.2 e))`. Unfold `NCov.part NCov.off`. Conclude with `iSup₂_le fun ψ hψ => le_iSup₂_of_le (f := fun ψ (_ : NCov.cls ψ ≠ T.mx j w i.1) => NCov.W (heckeAlg T.B j w) (NCov.pt ψ)) ψ (hψ ▸ hne) le_rfl`. Establish `hindGB : F.SupIndep (fun i => GK i ⊔ BK i)`.

Rewrite `hindP`, the goal using `[Finset.supIndep_iff_disjoint_erase]`. Introduce `i hi`. Conclude with `(hindP i hi).mono (sup_le (hpart i _) (hpart i _)) (Finset.sup_mono_fun fun i' _ => sup_le (hpart i' _) (hpart i' _))`. Establish `hdisGB : ∀ i ∈ F, Disjoint (GK i) (BK i)`. Introduce `i _`.

Rewrite using `[Submodule.disjoint_def]`. Introduce `z hz hz'`. Take `⟨y, hy, rfl⟩` from `(mem_gK T i _ z).1 hz`. Take `⟨y', hy', e⟩` from `(mem_gK T i _ _).1 hz'`. Establish `e'` using `T.Psi_inj j w i.1 i.2 e`.

Establish `h0 : y = 0` using `Submodule.disjoint_def.1 (GlobalTheory.T.heckeEigenspaceSum_disjoint_compl D i.1 _) y hy (e' ▸ hy')`. Rewrite using `[h0, map_zero]`. Establish `hdS` using `GlobalTheory.T.disjoint_finset_sup_of_supIndep_sup' (FractionRing (T.B.Oc j w)) (T.B.V j w) _ F GK BK hindGB hdisGB`. Establish `hGle : G' ≤ F.sup GK` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Rewrite using `[GlobalTheory.T.rationalForm_eq_sum_localisation_projections D M T j w h1 h2 hw hstd y]`. Use `Submodule.sum_mem _ fun i hi => Finset.le_sup (f := GK) hi ?_` and prove the remaining obligations. Conclude with `(mem_gK T i _ _).2 ⟨_, (hSP i.1 i.2).1 _ ((castInv_mem i.2 y).1 hy), rfl⟩)`. Establish `hBle : B' ≤ F.sup BK` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Rewrite using `[GlobalTheory.T.rationalForm_eq_sum_localisation_projections D M T j w h1 h2 hw hstd y]`. Use `Submodule.sum_mem _ fun i hi => Finset.le_sup (f := BK) hi ?_` and prove the remaining obligations. Conclude with `(mem_gK T i _ _).2 ⟨_, (hSP i.1 i.2).2 _ ((castInv_mem i.2 y).2 hy), rfl⟩)`. Establish `htop : G' ⊔ B' = ⊤`. Establish `hUU : U ⊔ U' = ⊤` using `hZ`.

Rewrite using `[eq_top_iff, ← hb.2]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `hm : b a ∈ U ⊔ U'` using `by rw [hUU]; exact Submodule.mem_top`. Take `⟨u, hu, u', hu', e⟩` from `Submodule.mem_sup.1 hm`.

Use `show T.B.iV j w (b a) ∈ G' ⊔ B'`. Rewrite using `[← e, map_add]`. Conclude with `Submodule.add_mem_sup (Submodule.subset_span ⟨u, hu, rfl⟩) (Submodule.subset_span ⟨u', hu', rfl⟩)`. Establish `key : ∀ {a c d e : Submodule (FractionRing (T.B.Oc j w)) (T.B.V j w)}, a ≤ c → d ≤ e → a ⊔ d = ⊤ → Disjoint c e → c = a`. Introduce `a c d e hac hde had hce`.

Use `le_antisymm ?_ hac` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Submodule.disjoint_def.1 hce x hx.2 (hde hx.1)]`. Conclude with `a.zero_mem`. Establish `hEGK : F.sup GK = G'` using `key hGle hBle htop hdS`.

Establish `hEBK : F.sup BK = B'` using `key hBle hGle (by rw [sup_comm]; exact htop) hdS.symm`. Establish `hrs : ∀ (s : Finset {i // i ∈ D.nd.locs j w}) (f : {i // i ∈ D.nd.locs j w} → Submodule (FractionRing (T.B.Oc j w)) (T.B.V j w)), s.sup (fun i => (f i).restrictScalars (T.B.Oc j w)) = (s.sup f).restrictScalars (T.B.Oc j w)` using `fun s f => (map_finset_sup (Submodule.restrictScalarsLatticeHom (T.B.Oc j w) (FractionRing (T.B.Oc j w)) (T.B.V j w)) s f).symm`. Establish `hEG : F.sup (fun i => (GK i).restrictScalars (T.B.Oc j w)) = G'.restrictScalars (T.B.Oc j w)`. Rewrite using `[hrs, hEGK]`. Establish `hEB : F.sup (fun i => (BK i).restrictScalars (T.B.Oc j w)) = B'.restrictScalars (T.B.Oc j w)`.

Rewrite using `[hrs, hEBK]`. Establish `hindO : F.SupIndep (fun i => (GK i).restrictScalars (T.B.Oc j w) ⊔ (BK i).restrictScalars (T.B.Oc j w))`. Simplify using `only [← Submodule.restrictScalars_sup]`. Rewrite `hindGB`, the goal using `[Finset.supIndep_iff_disjoint_erase]`. Introduce `i hi`.

Rewrite using `[hrs]`. Conclude with `Submodule.disjoint_def.2 fun x hx hx' => Submodule.disjoint_def.1 (hindGB i hi) x hx hx'`. Establish `hdisO : ∀ i ∈ F, Disjoint ((GK i).restrictScalars (T.B.Oc j w)) ((BK i).restrictScalars (T.B.Oc j w))` using `fun i hi => Submodule.disjoint_def.2 fun x hx hx' => Submodule.disjoint_def.1 (hdisGB i hi) x hx hx'`. Establish `hLle : ∀ i ∈ F, lO T i ≤ (GK i).restrictScalars (T.B.Oc j w) ⊔ (BK i).restrictScalars (T.B.Oc j w)`. Introduce `i _ z hz`.

Use `haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)`. Unfold `lO at hz`. Take `⟨y, -, rfl⟩` from `Submodule.mem_map.1 hz`. Establish `hy : y ∈ D.nd.eigSum i.1 ↑(D.nd.Zgood i.1) ⊔ D.nd.eigSum i.1 (↑(D.nd.Zgood i.1))ᶜ`. Rewrite using `[GlobalTheory.T.goodEigSum_sup_compl_eigSum_eq_top D i.1 (zrat_loc i.2 hZ) (hSP i.1 i.2)]`.

Conclude with `Submodule.mem_top`. Take `⟨a, ha, c, hc', e⟩` from `Submodule.mem_sup.1 hy`. Rewrite using `[← Submodule.restrictScalars_sup, Submodule.restrictScalars_mem, psiO_apply, ← e, map_add]`. Conclude with `Submodule.add_mem_sup ((mem_gK T i _ _).2 ⟨a, ha, rfl⟩) ((mem_gK T i _ _).2 ⟨c, hc', rfl⟩)`. Establish `hEL : F.sup (lO T) = latC T.B j w`.

Use extensionality with `y`. Rewrite using `[Finset.sup_eq_iSup, Submodule.mem_iSup_finset_iff_exists_sum]`. Express the relevant statement in the definitionally equal form `_ ↔ y ∈ latLoc T.B j w`. Rewrite using `[GlobalTheory.T.integralFormLattice_eq_sum_localised_lattices D M T j w h1 h2 hw hstd hlat y]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨μ, hμ⟩`. Establish `hch : ∀ i : {i // i ∈ D.nd.locs j w}, ∃ z ∈ D.nd.MtIn i.1, T.Psi j w i.1 i.2 z = μ i` using `fun i => by haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)`. Take `⟨z, hz, e⟩` from `Submodule.mem_map.1 (μ i).2`. Conclude with `⟨z, hz, e⟩`. Use `choose zf hzf hzf' using hch`.

Use `⟨fun i => if h : i ∈ D.nd.locs j w then zf ⟨i, h⟩ else 0, fun i => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only`. Distinguish the cases in `h : i ∈ D.nd.locs j w`. Rewrite using `[dif_pos h]`. Conclude with `hzf ⟨i, h⟩`.

Rewrite using `[dif_neg h]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[← hμ]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[dif_pos i.2]`. Conclude with `(hzf' i).symm`. Introduce and unpack `⟨z, hz, rfl⟩`. Use `⟨fun i => ⟨T.Psi j w i.1 i.2 (z i.1), ?_⟩, rfl⟩` and prove the remaining obligations. Use `haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)`.

Conclude with `Submodule.mem_map_of_mem (f := psiO T i.2) (hz i.1)`. Establish `asum : qLen (F.sup (fun i => (GK i).restrictScalars (T.B.Oc j w))) (F.sup (lO T)) (F.sup (fun i => (BK i).restrictScalars (T.B.Oc j w))) = ∑ i ∈ F, qLen ((GK i).restrictScalars (T.B.Oc j w)) (lO T i) ((BK i).restrictScalars (T.B.Oc j w))` using `GlobalTheory.T.congruenceLength_finset_sup_eq_sum (T.B.Oc j w) (T.B.V j w) _ F (lO T) (fun i => (GK i).restrictScalars (T.B.Oc j w)) (fun i => (BK i).restrictScalars (T.B.Oc j w)) hindO hdisO hLle`. Rewrite `hglob` using `[← hEG, ← hEB, ← hEL, asum]`. Rewrite using `[hglob, ← Finset.sum_attach (D.nd.locs j w) D.nd.etaLoc, ← hF, ENat.toNat_sum hfin, Nat.cast_sum, Finset.sum_div]`. Conclude with `Finset.sum_congr rfl fun i _ => etaLoc_eq_loc T i`.
-/
theorem sum_etaLoc_eq_etaRat : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → LatStable T.B j w → ZRat D (D.what₂.muTw w) j → (∀ i ∈ D.nd.locs j w, SpecPr D i) → D.what₂.etaJ j w = etaRat D (D.what₂.muTw w) j w := by
  intro D M T j w h1 h2 hw hstd hlat hZ hSP
  classical
  rw [D.etaJ_tie j w h1 h2]
  set F := (D.nd.locs j w).attach with hF
  set U := ratSub D (D.what₂.muTw w) j (Idx.Z0 D (D.what₂.muTw w) j) with hU
  set U' := ratSub D (D.what₂.muTw w) j (Idx.Z0 D (D.what₂.muTw w) j)ᗮ with hU'
  set G' := Submodule.span (FractionRing (T.B.Oc j w)) (T.B.iV j w '' (U : Set _)) with hG'
  set B' := Submodule.span (FractionRing (T.B.Oc j w)) (T.B.iV j w '' (U' : Set _)) with hB'
  set GK : {i // i ∈ D.nd.locs j w} → Submodule (FractionRing (T.B.Oc j w)) (T.B.V j w) :=
    fun i => gK T i ↑(D.nd.Zgood i.1) with hGK
  set BK : {i // i ∈ D.nd.locs j w} → Submodule (FractionRing (T.B.Oc j w)) (T.B.V j w) :=
    fun i => gK T i (↑(D.nd.Zgood i.1))ᶜ with hBK

  have hfin : ∀ i ∈ F, qLen ((GK i).restrictScalars (T.B.Oc j w)) (lO T i)
      ((BK i).restrictScalars (T.B.Oc j w)) ≠ ⊤ := by
    intro i _
    rw [hGK, hBK]
    simp only []
    rw [length_loc]
    have hZi := zrat_loc i.2 hZ
    have hfg : (D.nd.MtIn i.1).FG := by
      unfold NData.MtIn
      rw [LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map _
    have hspan : Submodule.span (FractionRing (D.nd.O i.1)) (↑(D.nd.MtIn i.1) : Set (TensorProduct (D.nd.O i.1) (FractionRing (D.nd.O i.1)) (D.nd.Mt i.1))) = ⊤ := by
      rw [eq_top_iff]
      rintro z -
      induction z using TensorProduct.induction_on with
      | zero => exact Submodule.zero_mem _
      | tmul k m =>
        have e : k ⊗ₜ[D.nd.O i.1] m = k • ((1 : FractionRing (D.nd.O i.1)) ⊗ₜ[D.nd.O i.1] m) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
      | add x y hx hy => exact Submodule.add_mem _ hx hy
    exact (GlobalTheory.T.finiteLength_lattice_projection_quotient (D.nd.O i.1) (FractionRing (D.nd.O i.1)) _ (D.nd.MtIn i.1) _ _ hfg (GlobalTheory.T.heckeEigenspaceSum_disjoint_compl D i.1 _)).resolve_right
      (not_not.2 ⟨hspan, GlobalTheory.T.goodEigSum_sup_compl_eigSum_eq_top D i.1 hZi (hSP i.1 i.2)⟩)

  obtain ⟨hint, hlw, hunit⟩ := GlobalTheory.T.coeffEmbedding_integers_resChar_unit D M T.B j w
  have hfinI := finite_chooseBasisIndex (D := D) j w
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  haveI : FiniteDimensional D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := Module.Finite.of_basis b
  have hb := T.B.iV_basis j w b
  have hjinj : Function.Injective (D.what₂.jMt (D.what₂.muTw w) j) := by
    have hli := (D.what₂.jMt_basis (D.what₂.muTw w) j b).1
    refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    have hsum := b.sum_repr y
    rw [← hsum, map_sum] at hy
    simp only [LinearMap.map_smulₛₗ] at hy
    have hz := Fintype.linearIndependent_iff.1 hli _ hy
    rw [← hsum]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [(map_eq_zero_iff _ D.what₂.embLL.injective).1 (hz a), zero_smul]
  have hc : IsCompl U U' := by
    refine ⟨Submodule.disjoint_def.2 fun x hx hx' => hjinj ?_, codisjoint_iff.2 hZ⟩
    rw [map_zero]
    exact Submodule.disjoint_def.1 (Submodule.orthogonal_disjoint _) _ hx hx'
  have hup : Submodule.span (T.B.Oc j w) (T.B.iV j w '' (up D (D.what₂.muTw w) j : Set _)) =
      G'.restrictScalars (T.B.Oc j w) ⊓ (Submodule.span (T.B.Oc j w) (T.B.iV j w '' (lat D (D.what₂.muTw w) j : Set _)) ⊔ B'.restrictScalars (T.B.Oc j w)) :=
    GlobalTheory.T.latticeProjection_baseChange_dvr_comm D.what₂.LL (T.B.Oc j w) (T.B.ec j w) _ (T.B.V j w) (T.B.iV j w) _ b hb.1 hint
      (lat D (D.what₂.muTw w) j) U U' hc
  have hlow : Submodule.span (T.B.Oc j w) (T.B.iV j w '' (low D (D.what₂.muTw w) j : Set _)) =
      Submodule.span (T.B.Oc j w) (T.B.iV j w '' (lat D (D.what₂.muTw w) j : Set _)) ⊓ G'.restrictScalars (T.B.Oc j w) :=
    GlobalTheory.T.lattice_inf_subspace_baseChange_dvr D.what₂.LL (T.B.Oc j w) (T.B.ec j w) _ (T.B.V j w) (T.B.iV j w) _ b hb.1 hint
      (lat D (D.what₂.muTw w) j) U
  have hlatFG : (lat D (D.what₂.muTw w) j).FG := by
    have hfs : (genSet D (D.what₂.muTw w) j).Finite :=
      Set.Finite.preimage hjinj.injOn (D.what₂.MtLat (D.what₂.muTw w) j).gen.finite_toSet
    exact ⟨hfs.toFinset, by rw [Set.Finite.coe_toFinset]; rfl⟩
  have hupFG : (up D (D.what₂.muTw w) j).FG :=
    GlobalTheory.T.fg_inf_sup_of_isCompl' D.what₂.LL _ (lat D (D.what₂.muTw w) j) U U' hlatFG hc
  have hlowle : low D (D.what₂.muTw w) j ≤ up D (D.what₂.muTw w) j :=
    le_inf inf_le_right (inf_le_left.trans le_sup_left)
  have hlen := GlobalTheory.T.normalizedLength_latticeQuotient_baseChange_eq D.what₂.LL (T.B.Oc j w) (T.B.ec j w) _ (T.B.V j w) (T.B.iV j w) _ b hb.1 hint
    (D.plEq w) (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w) hlw hunit
    (up D (D.what₂.muTw w) j) (low D (D.what₂.muTw w) j) hupFG hlowle
  have hlatC : Submodule.span (T.B.Oc j w) (T.B.iV j w '' (lat D (D.what₂.muTw w) j : Set _)) = latC T.B j w :=
    GlobalTheory.T.span_image_semilinear_lattice_eq D.what₂.LL (T.B.Oc j w) (T.B.ec j w) _ (T.B.V j w) (T.B.iV j w) hint _
  have hglob : etaRat D (D.what₂.muTw w) j w =
      ((qLen (G'.restrictScalars (T.B.Oc j w)) (latC T.B j w) (B'.restrictScalars (T.B.Oc j w))).toNat : ℚ) /
      ((Module.length (T.B.Oc j w) (T.B.Oc j w ⧸ Ideal.span {((D.what₂.places.resChar w : ℕ) : T.B.Oc j w)})).toNat : ℚ) := by
    rw [show etaRat D (D.what₂.muTw w) j w = Formalism.L2.Col.lenUW (D.plEq w) (up D (D.what₂.muTw w) j) (low D (D.what₂.muTw w) j) from rfl, ← hlen]
    unfold lenUnit qLen
    rw [hup, hlow, hlatC]

  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  obtain ⟨hS, -, -⟩ := gens_hypsTw T.B hstd h1 h2 (Or.inl hw)
  have hinjK := IsFractionRing.injective (T.B.Oc j w) (FractionRing (T.B.Oc j w))
  have hpart : ∀ (i : {i // i ∈ D.nd.locs j w}) (Y : Set (D.nd.X i.1)),
      gK T i Y ≤ NCov.part (heckeAlg T.B j w) (T.mx j w i.1) := by
    intro i Y z hz
    obtain ⟨y, -, rfl⟩ := (mem_gK T i Y z).1 hz
    exact (T.Psi_range j w i.1 i.2 _).2 ⟨y, rfl⟩
  have hindP : F.SupIndep (fun i : {i // i ∈ D.nd.locs j w} =>
      NCov.part (heckeAlg T.B j w) (T.mx j w i.1)) := by
    rw [Finset.supIndep_iff_disjoint_erase]
    intro i _
    refine (NCov.disjoint_part_off hinjK hS (T.mx j w i.1)).mono_right (Finset.sup_le fun i' hi' => ?_)
    have hne : T.mx j w i'.1 ≠ T.mx j w i.1 := fun e =>
      Finset.ne_of_mem_erase hi' (Subtype.ext (T.mx_inj j w i'.2 i.2 e))
    unfold NCov.part NCov.off
    exact iSup₂_le fun ψ hψ => le_iSup₂_of_le (f := fun ψ (_ : NCov.cls ψ ≠ T.mx j w i.1) =>
      NCov.W (heckeAlg T.B j w) (NCov.pt ψ)) ψ (hψ ▸ hne) le_rfl
  have hindGB : F.SupIndep (fun i => GK i ⊔ BK i) := by
    rw [Finset.supIndep_iff_disjoint_erase] at hindP ⊢
    intro i hi
    exact (hindP i hi).mono (sup_le (hpart i _) (hpart i _))
      (Finset.sup_mono_fun fun i' _ => sup_le (hpart i' _) (hpart i' _))
  have hdisGB : ∀ i ∈ F, Disjoint (GK i) (BK i) := by
    intro i _
    rw [Submodule.disjoint_def]
    intro z hz hz'
    obtain ⟨y, hy, rfl⟩ := (mem_gK T i _ z).1 hz
    obtain ⟨y', hy', e⟩ := (mem_gK T i _ _).1 hz'
    have e' := T.Psi_inj j w i.1 i.2 e
    have h0 : y = 0 := Submodule.disjoint_def.1 (GlobalTheory.T.heckeEigenspaceSum_disjoint_compl D i.1 _) y hy (e' ▸ hy')
    rw [h0, map_zero]
  have hdS := GlobalTheory.T.disjoint_finset_sup_of_supIndep_sup' (FractionRing (T.B.Oc j w)) (T.B.V j w) _ F GK BK hindGB hdisGB
  have hGle : G' ≤ F.sup GK := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    rw [GlobalTheory.T.rationalForm_eq_sum_localisation_projections D M T j w h1 h2 hw hstd y]
    refine Submodule.sum_mem _ fun i hi => Finset.le_sup (f := GK) hi ?_
    exact (mem_gK T i _ _).2 ⟨_, (hSP i.1 i.2).1 _ ((castInv_mem i.2 y).1 hy), rfl⟩)
  have hBle : B' ≤ F.sup BK := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    rw [GlobalTheory.T.rationalForm_eq_sum_localisation_projections D M T j w h1 h2 hw hstd y]
    refine Submodule.sum_mem _ fun i hi => Finset.le_sup (f := BK) hi ?_
    exact (mem_gK T i _ _).2 ⟨_, (hSP i.1 i.2).2 _ ((castInv_mem i.2 y).2 hy), rfl⟩)
  have htop : G' ⊔ B' = ⊤ := by
    have hUU : U ⊔ U' = ⊤ := hZ
    rw [eq_top_iff, ← hb.2]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    have hm : b a ∈ U ⊔ U' := by rw [hUU]; exact Submodule.mem_top
    obtain ⟨u, hu, u', hu', e⟩ := Submodule.mem_sup.1 hm
    show T.B.iV j w (b a) ∈ G' ⊔ B'
    rw [← e, map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨u, hu, rfl⟩) (Submodule.subset_span ⟨u', hu', rfl⟩)
  have key : ∀ {a c d e : Submodule (FractionRing (T.B.Oc j w)) (T.B.V j w)},
      a ≤ c → d ≤ e → a ⊔ d = ⊤ → Disjoint c e → c = a := by
    intro a c d e hac hde had hce
    refine le_antisymm ?_ hac
    calc c = (a ⊔ d) ⊓ c := by rw [had, top_inf_eq]
      _ = a ⊔ d ⊓ c := sup_inf_assoc_of_le d hac
      _ ≤ a := sup_le le_rfl fun x hx => by
        rw [Submodule.disjoint_def.1 hce x hx.2 (hde hx.1)]
        exact a.zero_mem
  have hEGK : F.sup GK = G' := key hGle hBle htop hdS
  have hEBK : F.sup BK = B' := key hBle hGle (by rw [sup_comm]; exact htop) hdS.symm
  have hrs : ∀ (s : Finset {i // i ∈ D.nd.locs j w})
      (f : {i // i ∈ D.nd.locs j w} → Submodule (FractionRing (T.B.Oc j w)) (T.B.V j w)),
      s.sup (fun i => (f i).restrictScalars (T.B.Oc j w)) = (s.sup f).restrictScalars (T.B.Oc j w) := fun s f =>
    (map_finset_sup (Submodule.restrictScalarsLatticeHom (T.B.Oc j w) (FractionRing (T.B.Oc j w)) (T.B.V j w)) s f).symm
  have hEG : F.sup (fun i => (GK i).restrictScalars (T.B.Oc j w)) = G'.restrictScalars (T.B.Oc j w) := by
    rw [hrs, hEGK]
  have hEB : F.sup (fun i => (BK i).restrictScalars (T.B.Oc j w)) = B'.restrictScalars (T.B.Oc j w) := by
    rw [hrs, hEBK]
  have hindO : F.SupIndep (fun i => (GK i).restrictScalars (T.B.Oc j w) ⊔ (BK i).restrictScalars (T.B.Oc j w)) := by
    simp only [← Submodule.restrictScalars_sup]
    rw [Finset.supIndep_iff_disjoint_erase] at hindGB ⊢
    intro i hi
    rw [hrs]
    exact Submodule.disjoint_def.2 fun x hx hx' => Submodule.disjoint_def.1 (hindGB i hi) x hx hx'
  have hdisO : ∀ i ∈ F, Disjoint ((GK i).restrictScalars (T.B.Oc j w)) ((BK i).restrictScalars (T.B.Oc j w)) :=
    fun i hi => Submodule.disjoint_def.2 fun x hx hx' => Submodule.disjoint_def.1 (hdisGB i hi) x hx hx'
  have hLle : ∀ i ∈ F, lO T i ≤ (GK i).restrictScalars (T.B.Oc j w) ⊔ (BK i).restrictScalars (T.B.Oc j w) := by
    intro i _ z hz
    haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)
    unfold lO at hz
    obtain ⟨y, -, rfl⟩ := Submodule.mem_map.1 hz
    have hy : y ∈ D.nd.eigSum i.1 ↑(D.nd.Zgood i.1) ⊔ D.nd.eigSum i.1 (↑(D.nd.Zgood i.1))ᶜ := by
      rw [GlobalTheory.T.goodEigSum_sup_compl_eigSum_eq_top D i.1 (zrat_loc i.2 hZ) (hSP i.1 i.2)]; exact Submodule.mem_top
    obtain ⟨a, ha, c, hc', e⟩ := Submodule.mem_sup.1 hy
    rw [← Submodule.restrictScalars_sup, Submodule.restrictScalars_mem, psiO_apply, ← e, map_add]
    exact Submodule.add_mem_sup ((mem_gK T i _ _).2 ⟨a, ha, rfl⟩) ((mem_gK T i _ _).2 ⟨c, hc', rfl⟩)
  have hEL : F.sup (lO T) = latC T.B j w := by
    ext y
    rw [Finset.sup_eq_iSup, Submodule.mem_iSup_finset_iff_exists_sum]
    change _ ↔ y ∈ latLoc T.B j w
    rw [GlobalTheory.T.integralFormLattice_eq_sum_localised_lattices D M T j w h1 h2 hw hstd hlat y]
    constructor
    · rintro ⟨μ, hμ⟩
      have hch : ∀ i : {i // i ∈ D.nd.locs j w}, ∃ z ∈ D.nd.MtIn i.1, T.Psi j w i.1 i.2 z = μ i := fun i => by
        haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)
        obtain ⟨z, hz, e⟩ := Submodule.mem_map.1 (μ i).2
        exact ⟨z, hz, e⟩
      choose zf hzf hzf' using hch
      refine ⟨fun i => if h : i ∈ D.nd.locs j w then zf ⟨i, h⟩ else 0, fun i => ?_, ?_⟩
      · dsimp only
        by_cases h : i ∈ D.nd.locs j w
        · rw [dif_pos h]; exact hzf ⟨i, h⟩
        · rw [dif_neg h]; exact Submodule.zero_mem _
      · rw [← hμ]
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only
        rw [dif_pos i.2]
        exact (hzf' i).symm
    · rintro ⟨z, hz, rfl⟩
      refine ⟨fun i => ⟨T.Psi j w i.1 i.2 (z i.1), ?_⟩, rfl⟩
      haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)
      exact Submodule.mem_map_of_mem (f := psiO T i.2) (hz i.1)
  have asum : qLen (F.sup (fun i => (GK i).restrictScalars (T.B.Oc j w))) (F.sup (lO T))
      (F.sup (fun i => (BK i).restrictScalars (T.B.Oc j w))) =
      ∑ i ∈ F, qLen ((GK i).restrictScalars (T.B.Oc j w)) (lO T i) ((BK i).restrictScalars (T.B.Oc j w)) :=
    GlobalTheory.T.congruenceLength_finset_sup_eq_sum (T.B.Oc j w) (T.B.V j w) _ F (lO T) (fun i => (GK i).restrictScalars (T.B.Oc j w))
      (fun i => (BK i).restrictScalars (T.B.Oc j w)) hindO hdisO hLle
  rw [← hEG, ← hEB, ← hEL, asum] at hglob
  rw [hglob, ← Finset.sum_attach (D.nd.locs j w) D.nd.etaLoc, ← hF, ENat.toNat_sum hfin, Nat.cast_sum,
    Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => etaLoc_eq_loc T i

end GlobalTheory.EtaJoinSum
