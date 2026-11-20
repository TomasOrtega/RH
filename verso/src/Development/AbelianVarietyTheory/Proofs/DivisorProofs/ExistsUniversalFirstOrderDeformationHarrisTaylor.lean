import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackAlongStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderIsoOfSameHodgeFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHodgeFiltrationNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsGluedFirstOrderDeformationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationsBasisCountStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

/- English proof (translation)
Introduce `p _ D R _ b N hN hNp k _ _ t o₀`. Take `⟨f, hdir, huniq⟩` from `GlobalTheory.T.harrisTaylor_firstOrder_deformations_basis_count p D R b N hN hNp k t o₀`. Take `⟨o, m, hm⟩` from `GlobalTheory.T.harrisTaylor_exists_glued_firstOrder_deformation p D R b N hN hNp k t o₀ _ f hdir`. Use `⟨o, ⟨m⟩, fun o' ho' => ?_⟩` and prove the remaining obligations. Take `⟨m'⟩` from `ho'`.

Establish `key : ∀ (s' : Sp (DualNumber k) ⟶ Sp R) (o'' : GlobalTheory.UPel.HT.Obj b N s') (m'' : GlobalTheory.UPel.HT.ObjMap o₀ o'' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k) (n : GlobalTheory.UPel.HT.ObjMap o'' o (spMap (TrivSqZeroExt.map c). …`. Introduce `s' o'' m'' c n x hx`. Establish `h` using `GlobalTheory.T.harrisTaylor_hodgeFiltration_naturality p D R b N hN hNp k t o₀ _ _ o m c s' o'' m'' n x _ (hm x hx)`. Rewrite `h` using `[GlobalTheory.HTUniv.comp_pi]`. Conclude with `h`.

Take `⟨c₀, hc₀, hc₀u⟩` from `huniq o' m'`. Set `c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k` to `∑ j, c₀ j • LinearMap.proj j`. Establish `hcj : ∀ j, c (Pi.single j 1) = c₀ j` using `fun j => GlobalTheory.HTUniv.sum_proj_single c₀ j`. Take `⟨oc, ⟨nc⟩⟩` from `GlobalTheory.T.exists_harrisTaylorObject_pullback_along p D R b N _ _ _ (spMap (TrivSqZeroExt.map c).toRingHom) o`. Establish `hcomp : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (TrivSqZeroExt.map c).toRingHom = spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom`.

Rewrite using `[← GlobalTheory.Cris.spMap_comp]`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules. Take `⟨mc⟩` from `(GlobalTheory.T.harris_taylor_object_maps_compose_cancel p D R b N _ _ _ _ _ _ o₀ oc o (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (spMap (TrivSqZeroExt.map c).toRingHom)).2 (by rw [hcomp]; exact ⟨m⟩) ⟨nc⟩`.

Establish `hfc` using `key _ oc mc c nc`. Simplify using `only [hcj] at hfc`. Take `⟨iso⟩` from `GlobalTheory.T.harrisTaylor_firstOrder_iso_of_same_hodge_filtration p D R b N hN hNp k t o₀ _ _ o' oc m' mc (fun x => ∑ j, c₀ j • f j x) hc₀ hfc`. Use `⟨c, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `(GlobalTheory.T.harris_taylor_object_maps_compose_cancel p D R b N _ _ _ _ _ _ o' oc o (𝟙 _) (spMap (TrivSqZeroExt.map c).toRingHom)).1 ⟨iso⟩ ⟨nc⟩`.

Rewrite `h` using `[Category.id_comp]`. Then use the resulting hypothesis. Introduce and unpack `c' ⟨n'⟩`. Establish `h1` using `key _ o' m' c' n'`. Establish `h2` using `hc₀u (fun j => c' (Pi.single j 1)) h1`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.HTUniv.coord c' v, GlobalTheory.HTUniv.coord c v]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hcj]`. Conclude with `congrArg _ (congrFun h2 j)`.
-/
theorem GlobalTheory.HTUniv.main : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom)) ∧ ∀ o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, Nonempty (GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀
  obtain ⟨f, hdir, huniq⟩ := GlobalTheory.T.harrisTaylor_firstOrder_deformations_basis_count p D R b N hN hNp k t o₀
  obtain ⟨o, m, hm⟩ := GlobalTheory.T.harrisTaylor_exists_glued_firstOrder_deformation p D R b N hN hNp k t o₀ _ f hdir
  refine ⟨o, ⟨m⟩, fun o' ho' => ?_⟩
  obtain ⟨m'⟩ := ho'
  have key : ∀ (s' : Sp (DualNumber k) ⟶ Sp R) (o'' : GlobalTheory.UPel.HT.Obj b N s')
      (m'' : GlobalTheory.UPel.HT.ObjMap o₀ o'' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
      (c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k)
      (n : GlobalTheory.UPel.HT.ObjMap o'' o (spMap (TrivSqZeroExt.map c).toRingHom)),
      ∀ x ∈ Fil o₀.A, IsFilLift m''.cart x (∑ j, c (Pi.single j 1) • f j x) := by
    intro s' o'' m'' c n x hx
    have h := GlobalTheory.T.harrisTaylor_hodgeFiltration_naturality p D R b N hN hNp k t o₀ _ _ o m c s' o'' m'' n x _ (hm x hx)
    rw [GlobalTheory.HTUniv.comp_pi] at h
    exact h
  obtain ⟨c₀, hc₀, hc₀u⟩ := huniq o' m'
  let c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k := ∑ j, c₀ j • LinearMap.proj j
  have hcj : ∀ j, c (Pi.single j 1) = c₀ j := fun j => GlobalTheory.HTUniv.sum_proj_single c₀ j
  obtain ⟨oc, ⟨nc⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback_along p D R b N _ _ _ (spMap (TrivSqZeroExt.map c).toRingHom) o
  have hcomp : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (TrivSqZeroExt.map c).toRingHom =
      spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom := by
    rw [← GlobalTheory.Cris.spMap_comp]
    congr 1
    ext x
    simp
  obtain ⟨mc⟩ := (GlobalTheory.T.harris_taylor_object_maps_compose_cancel p D R b N _ _ _ _ _ _ o₀ oc o
    (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (spMap (TrivSqZeroExt.map c).toRingHom)).2
    (by rw [hcomp]; exact ⟨m⟩) ⟨nc⟩
  have hfc := key _ oc mc c nc
  simp only [hcj] at hfc
  obtain ⟨iso⟩ := GlobalTheory.T.harrisTaylor_firstOrder_iso_of_same_hodge_filtration p D R b N hN hNp k t o₀ _ _ o' oc m' mc (fun x => ∑ j, c₀ j • f j x) hc₀ hfc
  refine ⟨c, ?_, ?_⟩
  · have h := (GlobalTheory.T.harris_taylor_object_maps_compose_cancel p D R b N _ _ _ _ _ _ o' oc o (𝟙 _)
      (spMap (TrivSqZeroExt.map c).toRingHom)).1 ⟨iso⟩ ⟨nc⟩
    rwa [Category.id_comp] at h
  · rintro c' ⟨n'⟩
    have h1 := key _ o' m' c' n'
    have h2 := hc₀u (fun j => c' (Pi.single j 1)) h1
    refine LinearMap.ext fun v => ?_
    rw [GlobalTheory.HTUniv.coord c' v, GlobalTheory.HTUniv.coord c v]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcj]
    exact congrArg _ (congrFun h2 j)
