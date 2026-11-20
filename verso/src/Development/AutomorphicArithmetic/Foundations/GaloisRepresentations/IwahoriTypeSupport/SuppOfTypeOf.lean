import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.Gal.TypesAndIwahori

/- English proof (translation)
Introduce `k _ _ _ _`. Use `⟨fun η θ h => isSmoothChar_of_isTame h.isTame, fun θ => ?_, fun η θ θ' h h' => ?_⟩` and prove the remaining obligations. Take `⟨ϖ, hϖ⟩` from `exists_uniformizer k`. Take `⟨η, hη, -⟩` from `exists_isTameLift θ hϖ 1`. Conclude with `⟨η, hη⟩`.

Establish `hsurj : Function.Surjective (unitRes k)` using `IsLocalRing.surjective_units_map_of_local_ringHom _ IsLocalRing.residue_surjective inferInstance`. Use `MonoidHom.ext fun t => ?_` and prove the remaining obligations. Take `⟨u, rfl⟩` from `hsurj t`. Rewrite using `[← h u, ← h' u]`.
-/
theorem lifts : Lifts := by
  intro k _ _ _ _
  refine ⟨fun η θ h => isSmoothChar_of_isTame h.isTame, fun θ => ?_, fun η θ θ' h h' => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
    obtain ⟨η, hη, -⟩ := exists_isTameLift θ hϖ 1
    exact ⟨η, hη⟩
  · have hsurj : Function.Surjective (unitRes k) :=
      IsLocalRing.surjective_units_map_of_local_ringHom _ IsLocalRing.residue_surjective inferInstance
    refine MonoidHom.ext fun t => ?_
    obtain ⟨u, rfl⟩ := hsurj t
    rw [← h u, ← h' u]

/- English proof (translation)
Introduce `k _ _ _ _ _ N s d hd V _ _ π hsm hirr θ hθ`. Take `⟨v, hv0, hv⟩` from `hθ`. Use `choose μ hμ using fun a => (lifts k).2.1 (θ a)`. Establish `hIw` using `h1 k N s d hd V π θ μ hμ v hv`. Take `⟨ψ, hψ1, -, hψ3⟩` from `GlobalTheory.TameIwahori.exists_prinSeries L.bz L.dzj (GlobalTheory.SplitRead.Irr.mk V π hsm hirr) (fun i => (lifts k).1 _ _ (hμ _)) hv0 hIw`.

Establish `hψ : ∀ i, IsTameLift (ψ i) (θ (blockOf d hd i))`. Introduce `i u`. Rewrite using `[hψ1 i _ (valuation_eq_one_iff.mpr ⟨u, rfl⟩)]`. Conclude with `hμ _ u`. Conclude with `⟨ψ, hψ, GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries (GlobalTheory.SplitRead.Irr.mk V π hsm hirr) (fun i => (lifts k).1 _ _ (hψ i)) hψ3⟩`.
-/
theorem suppOfType_of (L : Loc) (h1 : TypeToIw) : SuppOfType := by
  intro k _ _ _ _ _ N s d hd V _ _ π hsm hirr θ hθ
  obtain ⟨v, hv0, hv⟩ := hθ
  choose μ hμ using fun a => (lifts k).2.1 (θ a)
  have hIw := h1 k N s d hd V π θ μ hμ v hv
  obtain ⟨ψ, hψ1, -, hψ3⟩ := GlobalTheory.TameIwahori.exists_prinSeries L.bz L.dzj
    (GlobalTheory.SplitRead.Irr.mk V π hsm hirr) (fun i => (lifts k).1 _ _ (hμ _)) hv0 hIw
  have hψ : ∀ i, IsTameLift (ψ i) (θ (blockOf d hd i)) := by
    intro i u
    rw [hψ1 i _ (valuation_eq_one_iff.mpr ⟨u, rfl⟩)]
    exact hμ _ u
  exact ⟨ψ, hψ, GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries (GlobalTheory.SplitRead.Irr.mk V π hsm hirr)
    (fun i => (lifts k).1 _ _ (hψ i)) hψ3⟩

/- English proof (translation)
Take `⟨v, hv0, hv⟩` from `h`. Take `⟨x, rfl⟩` from `φ.toLinearEquiv.surjective v`. Use `⟨x, fun h => hv0 (by rw [h, map_zero]), fun g => φ.toLinearEquiv.injective ?_⟩` and prove the remaining obligations. Establish `key : φ.toLinearEquiv (π g x) = σ g (φ.toLinearEquiv x)` using `LinearMap.congr_fun (φ.toIntertwiningMap.isIntertwining' g) x`. Rewrite using `[key, hv, map_smul]`.
-/
theorem HasTypeVec.of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL n k) V} {σ : Representation ℂ (GL n k) W} {e : (Σ a, m a) ≃ n} {θ : α → 𝓀[k]ˣ →* ℂˣ}
    (φ : π.Equiv σ) (h : HasTypeVec σ e θ) : HasTypeVec π e θ := by
  obtain ⟨v, hv0, hv⟩ := h
  obtain ⟨x, rfl⟩ := φ.toLinearEquiv.surjective v
  refine ⟨x, fun h => hv0 (by rw [h, map_zero]), fun g => φ.toLinearEquiv.injective ?_⟩
  have key : φ.toLinearEquiv (π g x) = σ g (φ.toLinearEquiv x) :=
    LinearMap.congr_fun (φ.toIntertwiningMap.isIntertwining' g) x
  rw [key, hv, map_smul]

/- English proof (translation)
Introduce `k _ _ _ _ _ N s d hd hpos V _ _ π hsm hirr θ hinj hθ`. Use `choose μ hμ using fun a => (lifts k).2.1 (θ a)`. Establish `hsmooth : ∀ a, IsSmoothChar (μ a)` using `fun a => (lifts k).1 _ _ (hμ a)`. Establish `hf` using `h2 k s θ μ hinj hμ`. Set `G : UpperTheory.TNZ.Grp k N` to `{ s := s, d := d, pos := hpos, hd := hd, μ := μ, smooth := hsmooth, dist := fun a b hab => (hf a b hab).1, ball := fun a a' b' b h1 h2 h3 => by`.

Rewrite using `[(hf a' b' h2.ne).2, (hf a b (by intro h; subst h; omega)).2] }`. Take `⟨y, hy0, hy⟩` from `h1 k N s d (stdBlocks d hd) V π hsm hirr θ μ hμ hθ`. Conclude with `⟨μ, fun a => ⟨hsmooth a, hμ a⟩, h3 k N G V π hsm hirr ⟨y, hy0, hy⟩⟩`.
-/
theorem topB_of (h1 : JacOfType) (h2 : GrpFacts) (h3 : JacProd) : TopB := by
  intro k _ _ _ _ _ N s d hd hpos V _ _ π hsm hirr θ hinj hθ
  choose μ hμ using fun a => (lifts k).2.1 (θ a)
  have hsmooth : ∀ a, IsSmoothChar (μ a) := fun a => (lifts k).1 _ _ (hμ a)
  have hf := h2 k s θ μ hinj hμ
  let G : UpperTheory.TNZ.Grp k N :=
    { s := s, d := d, pos := hpos, hd := hd, μ := μ, smooth := hsmooth,
      dist := fun a b hab => (hf a b hab).1,
      ball := fun a a' b' b h1 h2 h3 => by
        rw [(hf a' b' h2.ne).2, (hf a b (by intro h; subst h; omega)).2] }
  obtain ⟨y, hy0, hy⟩ := h1 k N s d (stdBlocks d hd) V π hsm hirr θ μ hμ hθ
  exact ⟨μ, fun a => ⟨hsmooth a, hμ a⟩, h3 k N G V π hsm hirr ⟨y, hy0, hy⟩⟩

end UpperTheory.Gal.TypesAndIwahori
