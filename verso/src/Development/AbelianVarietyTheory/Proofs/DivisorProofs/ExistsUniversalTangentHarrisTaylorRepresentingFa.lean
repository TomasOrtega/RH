import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackAlongStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.RepTangent

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

/- English proof (translation)
Simplify using `only [spMap]`. Conclude with `Spec.map_id _`.
-/
theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by
  simp only [spMap]; exact Spec.map_id _

/- English proof (translation)
Introduce `p _ D R _ _ b N hN hNp F _ _ k _ _ x`. Take `⟨o₀, ⟨m₀⟩⟩` from `GlobalTheory.T.exists_harrisTaylorObject_pullback_along p D R b N F.X (Sp k) F.s x F.univ`. Take `⟨o, ⟨mo⟩, huniv⟩` from `GlobalTheory.T.exists_universal_firstOrder_deformation_harrisTaylor p D R b N hN hNp k (x ≫ F.s) o₀`. Take `⟨u, ⟨hu1, ⟨mu⟩⟩, -⟩` from `F.rep _ _ o`. Establish `hfst : spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) = 𝟙 _`.

Rewrite using `[spMap_comp_spMap]`. Use `spMap_id' k` and compare the differences between its conclusion and the goal. Use extensionality with `a`. Simplify using the standard rewrite rules. Use `⟨u, ?_, hu1, ?_⟩` and prove the remaining obligations.

Take `⟨f, -, hf⟩` from `F.rep _ _ o₀`. Establish `e1` using `hf x ⟨rfl, ⟨m₀⟩⟩`. Establish `e2` using `hf (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u) ⟨by rw [Category.assoc, hu1, ← Category.assoc, hfst, Category.id_comp], ⟨MapComp.comp mo mu⟩⟩`. Conclude with `e2.trans e1.symm`. Introduce `v hv1 hv2`.

Take `⟨o', ⟨m'⟩⟩` from `GlobalTheory.T.exists_harrisTaylorObject_pullback_along p D R b N F.X (Sp (DualNumber k)) F.s v F.univ`. Establish `main : ∀ (s₁ : Sp (DualNumber k) ⟶ Sp R) (o' : Obj b N s₁), s₁ = v ≫ F.s → ObjMap o' F.univ v → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u`. Introduce `s₁ o' hs m'`. Rewrite `hs` using `[hv2]`. Substitute `hs` using the available equality.

Establish `h0 : Nonempty (ObjMap o₀ F.univ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v))`. Rewrite using `[hv1]`. Conclude with `⟨m₀⟩`. Establish `m''` using `(GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o₀ o' F.univ _ v).2 h0 ⟨m'⟩`. Take `⟨c, ⟨mc⟩, hc⟩` from `huniv o' m''`.

Establish `hbase : ∀ c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, (spMap (TrivSqZeroExt.map c).toRingHom ≫ u) ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s`. Introduce `c`. Rewrite using `[Category.assoc, hu1, ← Category.assoc, spMap_comp_spMap]`. Use `congr 2`. Conclude with `(TrivSqZeroExt.map c).comp_algebraMap`.

Use `⟨c, ?_, ?_⟩` and prove the remaining obligations. Take `⟨f, -, hf⟩` from `F.rep _ _ o'`. Conclude with `(hf v ⟨hv2, ⟨m'⟩⟩).trans (hf _ ⟨hbase c, ⟨MapComp.comp mc mu⟩⟩).symm`. Introduce `c' hc'`. Apply `hc` to reduce the goal to its premises.

Rewrite `m'` using `[hc']`. Conclude with `(GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o' o F.univ _ u).2 ⟨m'⟩ ⟨mu⟩`. Conclude with `main _ o' rfl m'`.
-/
theorem exists_univ_tangent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → Smooth F.s → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ F.X), ∃ u : Sp (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k)) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u = x ∧ u ≫ F.s = spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ x ≫ F.s ∧ ∀ v : Sp (DualNumber k) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
  intro p _ D R _ _ b N hN hNp F _ _ k _ _ x
  obtain ⟨o₀, ⟨m₀⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback_along p D R b N F.X (Sp k) F.s x F.univ
  obtain ⟨o, ⟨mo⟩, huniv⟩ := GlobalTheory.T.exists_universal_firstOrder_deformation_harrisTaylor p D R b N hN hNp k (x ≫ F.s) o₀
  obtain ⟨u, ⟨hu1, ⟨mu⟩⟩, -⟩ := F.rep _ _ o
  have hfst : spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫
      spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) = 𝟙 _ := by
    rw [spMap_comp_spMap]
    convert spMap_id' k
    ext a; simp
  refine ⟨u, ?_, hu1, ?_⟩
  · obtain ⟨f, -, hf⟩ := F.rep _ _ o₀
    have e1 := hf x ⟨rfl, ⟨m₀⟩⟩
    have e2 := hf (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u)
      ⟨by rw [Category.assoc, hu1, ← Category.assoc, hfst, Category.id_comp], ⟨MapComp.comp mo mu⟩⟩
    exact e2.trans e1.symm
  · intro v hv1 hv2
    obtain ⟨o', ⟨m'⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback_along p D R b N F.X (Sp (DualNumber k)) F.s v F.univ
    have main : ∀ (s₁ : Sp (DualNumber k) ⟶ Sp R) (o' : Obj b N s₁), s₁ = v ≫ F.s → ObjMap o' F.univ v →
        ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
      intro s₁ o' hs m'
      rw [hv2] at hs
      subst hs
      have h0 : Nonempty (ObjMap o₀ F.univ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v)) := by
        rw [hv1]; exact ⟨m₀⟩
      have m'' := (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o₀ o' F.univ _ v).2 h0 ⟨m'⟩
      obtain ⟨c, ⟨mc⟩, hc⟩ := huniv o' m''
      have hbase : ∀ c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k,
          (spMap (TrivSqZeroExt.map c).toRingHom ≫ u) ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s := by
        intro c
        rw [Category.assoc, hu1, ← Category.assoc, spMap_comp_spMap]
        congr 2
        exact (TrivSqZeroExt.map c).comp_algebraMap
      refine ⟨c, ?_, ?_⟩
      · obtain ⟨f, -, hf⟩ := F.rep _ _ o'
        exact (hf v ⟨hv2, ⟨m'⟩⟩).trans (hf _ ⟨hbase c, ⟨MapComp.comp mc mu⟩⟩).symm
      · intro c' hc'
        apply hc
        rw [hc'] at m'
        exact (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o' o F.univ _ u).2 ⟨m'⟩ ⟨mu⟩
    exact main _ o' rfl m'

end GlobalTheory.UPel.HT.RepTangent
