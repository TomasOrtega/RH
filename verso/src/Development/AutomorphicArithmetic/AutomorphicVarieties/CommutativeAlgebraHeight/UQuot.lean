import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFactor
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsOpenNormalSubgroupKillsOfGroupDetLawIsCont

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

namespace UpperTheory.V.CA

variable {n : ℕ} {A G : Type} [CommRing A] [Group G]

noncomputable def coord (D : GDet n A G) (t : ℕ × G) : A := D.lam t.1 (MonoidAlgebra.single t.2 1)

/- English proof (translation)
The claim follows from `d_gext D D' fun g i _ _ => h (i, g)`.
-/
theorem coord_ext {D D' : GDet n A G} (h : ∀ t, coord D t = coord D' t) : D = D' :=
  d_gext D D' fun g i _ _ => h (i, g)

/- English proof (translation)
Unfold `coord`. Rewrite using `[← ((d_gmap D).2.2.1 _ _).2 t.1, MonoidAlgebra.mapRingHom_single, map_one]`.
-/
theorem coord_map (D : GDet n A G) {B : Type} [CommRing B] (f : A →+* B) (t : ℕ × G) :
    coord (D.map f) t = f (coord D t) := by
  unfold coord
  rw [← ((d_gmap D).2.2.1 _ _).2 t.1, MonoidAlgebra.mapRingHom_single, map_one]

/- English proof (translation)
Unfold `coord GDet.lam GDet.chi`. Use `congr 2`. Express the relevant statement in the definitionally equal form `D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = _`. Use `congr 1`. Rewrite using `[map_sub]`.

Simplify using the standard rewrite rules.
-/
theorem coord_comap (D : GDet n A G) {H : Type} [Group H] (φ : H →* G) (t : ℕ × H) :
    coord (D.comap φ) t = coord D (t.1, φ t.2) := by
  unfold coord GDet.lam GDet.chi
  congr 2
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = _
  congr 1
  rw [map_sub]
  simp

/- English proof (translation)
Establish `hk : ∀ h ∈ H, (MonoidAlgebra.single h 1 - 1 : MonoidAlgebra A G) ∈ D.toDet.ker` using `fun h hh => (d_ker D.toDet _).1.2 ((d_toDet D _).2.2.2.2 (hD h hh))`. Set `f : MonoidAlgebra A G →ₐ[A] MonoidAlgebra A (G ⧸ H)` to `MonoidAlgebra.mapDomainAlgHom A A (QuotientGroup.mk' H)`. Set `σ : MonoidAlgebra A (G ⧸ H) →+ MonoidAlgebra A G` to `{ toFun := MonoidAlgebra.mapDomain Quotient.out map_zero' := MonoidAlgebra.mapDomain_zero _ map_add' := MonoidAlgebra.mapDomain_add _ }`. Establish `h1 : ∀ y, f (σ y) = y` using `fun y => by`. Proceed by induction on `y using MonoidAlgebra.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `single g r => simp [f, σ]`. Establish `h2 : ∀ x, x - σ (f x) ∈ D.toDet.ker` using `fun x => by`. Proceed by induction on `x using MonoidAlgebra.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add, add_sub_add_comm]`. Conclude with `D.toDet.ker.add_mem ha hb`. Consider the case `single g r`.

Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul H g`. Establish `: MonoidAlgebra.single g r - σ (f (MonoidAlgebra.single g r)) = - (MonoidAlgebra.single g r * (MonoidAlgebra.single (h : G) 1 - 1))`. Simplify using `[f, σ, hh, mul_sub, MonoidAlgebra.single_mul_single]`. Rewrite using `[this]`. Conclude with `D.toDet.ker.neg_mem (D.toDet.ker.mul_mem_left _ _ (hk h h.2))`.

Take `⟨D', hD', -⟩` from `d_factor D.toDet f (fun y => ⟨_, h1 y⟩) fun x hx => by`. Simplify `h2 x` using `[hx]`. Use `⟨GDet.ofDet D', GDet.ext fun S _ _ x => ?_⟩` and prove the remaining obligations. Rewrite using `[← GDet.ofDet_toDet D, ← hD']`. Express the relevant statement in the definitionally equal form `D'.D S (toT A _ S (MonoidAlgebra.mapDomainRingHom S (QuotientGroup.mk' H) x)) = D'.D S (Algebra.TensorProduct.map (AlgHom.id S S) f (toT A G S x))`.

Use `congr 1`. Proceed by induction on `x using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `single g r => simp [f, toT_single]`.
-/
theorem exists_comap_quot (D : GDet n A G) (H : Subgroup G) [H.Normal]
    (hD : ∀ h ∈ H, D.Kills (MonoidAlgebra.single h 1 - 1)) :
    ∃ D0 : GDet n A (G ⧸ H), D0.comap (QuotientGroup.mk' H) = D := by
  have hk : ∀ h ∈ H, (MonoidAlgebra.single h 1 - 1 : MonoidAlgebra A G) ∈ D.toDet.ker := fun h hh =>
    (d_ker D.toDet _).1.2 ((d_toDet D _).2.2.2.2 (hD h hh))
  let f : MonoidAlgebra A G →ₐ[A] MonoidAlgebra A (G ⧸ H) := MonoidAlgebra.mapDomainAlgHom A A (QuotientGroup.mk' H)
  let σ : MonoidAlgebra A (G ⧸ H) →+ MonoidAlgebra A G :=
    { toFun := MonoidAlgebra.mapDomain Quotient.out
      map_zero' := MonoidAlgebra.mapDomain_zero _
      map_add' := MonoidAlgebra.mapDomain_add _ }
  have h1 : ∀ y, f (σ y) = y := fun y => by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => simp [f, σ]
  have h2 : ∀ x, x - σ (f x) ∈ D.toDet.ker := fun x => by
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add, map_add, add_sub_add_comm]
      exact D.toDet.ker.add_mem ha hb
    | single g r =>
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
      have : MonoidAlgebra.single g r - σ (f (MonoidAlgebra.single g r)) =
          - (MonoidAlgebra.single g r * (MonoidAlgebra.single (h : G) 1 - 1)) := by
        simp [f, σ, hh, mul_sub, MonoidAlgebra.single_mul_single]
      rw [this]
      exact D.toDet.ker.neg_mem (D.toDet.ker.mul_mem_left _ _ (hk h h.2))
  obtain ⟨D', hD', -⟩ := d_factor D.toDet f (fun y => ⟨_, h1 y⟩) fun x hx => by
    simpa [hx] using h2 x
  refine ⟨GDet.ofDet D', GDet.ext fun S _ _ x => ?_⟩
  rw [← GDet.ofDet_toDet D, ← hD']
  change D'.D S (toT A _ S (MonoidAlgebra.mapDomainRingHom S (QuotientGroup.mk' H) x)) =
    D'.D S (Algebra.TensorProduct.map (AlgHom.id S S) f (toT A G S x))
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r => simp [f, toT_single]

/- English proof (translation)
Take `⟨H, hH⟩` from `exists_openNormalSubgroup_kills_of_groupDetLaw_isCont D I hc N`. Use `⟨H, fun K _ hK => ?_⟩` and prove the remaining obligations. Take `⟨D1, h1⟩` from `exists_comap_quot _ K fun h hh => hH h (hK hh)`. Set `g : A ⧸ I ^ N →+* A` to `Ideal.Quotient.lift _ (RingHom.id A) fun a ha => by simpa [hN] using ha`. Use `⟨D1.map g, coord_ext fun t => ?_⟩` and prove the remaining obligations.

Rewrite using `[coord_comap, coord_map, ← coord_comap, h1, coord_map]`. Both sides reduce to the same expression.
-/
theorem exists_comap_level [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (D : GDet n A G) (I : Ideal A) (hc : D.IsCont I) {N : ℕ} (hN : I ^ N = ⊥) :
    ∃ H : OpenNormalSubgroup G, ∀ (K : Subgroup G) [K.Normal], K ≤ H.toSubgroup →
      ∃ D0 : GDet n A (G ⧸ K), D0.comap (QuotientGroup.mk' K) = D := by
  obtain ⟨H, hH⟩ := exists_openNormalSubgroup_kills_of_groupDetLaw_isCont D I hc N
  refine ⟨H, fun K _ hK => ?_⟩
  obtain ⟨D1, h1⟩ := exists_comap_quot _ K fun h hh => hH h (hK hh)
  let g : A ⧸ I ^ N →+* A := Ideal.Quotient.lift _ (RingHom.id A) fun a ha => by simpa [hN] using ha
  refine ⟨D1.map g, coord_ext fun t => ?_⟩
  rw [coord_comap, coord_map, ← coord_comap, h1, coord_map]
  rfl

end UpperTheory.V.CA
