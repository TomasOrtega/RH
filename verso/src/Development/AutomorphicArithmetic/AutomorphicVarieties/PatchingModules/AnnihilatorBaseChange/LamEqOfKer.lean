import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsOpenNormalSubgroupKillsOfGroupDetLawIsCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

/- English proof (translation)
Establish `hchi : D.chi x = D.chi y`. Establish `h2` using `((UpperTheory.V.CA.d_ker D (x - y)).2.1.1 h) (Polynomial A) (-1) (Polynomial.X ⊗ₜ[A] (1 : E) - 1 ⊗ₜ[A] y)`. Unfold `Det.chi`. Rewrite using `[← h2]`. Use `congr 1`.

Rewrite using `[TensorProduct.neg_tmul, TensorProduct.tmul_sub]`. Normalize the expressions using the abelian group laws. Unfold `Det.lam`. Rewrite using `[hchi]`.
-/
private theorem lam_eq_of_ker {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
    {x y : E} (h : x - y ∈ D.ker) (i : ℕ) : D.lam i x = D.lam i y := by
  have hchi : D.chi x = D.chi y := by
    have h2 := ((UpperTheory.V.CA.d_ker D (x - y)).2.1.1 h) (Polynomial A) (-1)
      (Polynomial.X ⊗ₜ[A] (1 : E) - 1 ⊗ₜ[A] y)
    unfold Det.chi
    rw [← h2]
    congr 1
    rw [TensorProduct.neg_tmul, TensorProduct.tmul_sub]
    abel
  unfold Det.lam
  rw [hchi]

/- English proof (translation)
Establish `hker : ∀ h ∈ V, MonoidAlgebra.single h (1 : A) - 1 ∈ D.toDet.ker` using `fun h hh => (UpperTheory.V.CA.d_ker D.toDet _).1.2 ((UpperTheory.V.CA.d_toDet D _).2.2.2.2 (hV h hh))`. Rewrite using `[MonoidAlgebra.mapDomainRingHom_apply]`. Proceed by induction on `x using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb`.

Rewrite using `[MonoidAlgebra.mapDomain_add, MonoidAlgebra.mapDomain_add]`. Use `D.toDet.ker.add_mem ha hb` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Consider the case `single g r`.

Rewrite using `[MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single]`. Take `⟨v, hv⟩` from `QuotientGroup.mk_out_eq_mul V g`. Establish `hv' : (QuotientGroup.mk' V g).out = g * v` using `hv`. Rewrite using `[hv']`. Establish `heq : MonoidAlgebra.single g r - MonoidAlgebra.single (g * (v : G)) r = -(MonoidAlgebra.single g r * (MonoidAlgebra.single (v : G) (1 : A) - 1))`.

Rewrite using `[mul_sub, mul_one, MonoidAlgebra.single_mul_single, mul_one]`. Normalize the expressions using the abelian group laws. Rewrite using `[heq]`. Conclude with `D.toDet.ker.neg_mem (D.toDet.ker.mul_mem_left _ _ (hker _ v.2))`.
-/
private theorem sub_mem_ker {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (V : Subgroup G)
    [V.Normal] (hV : ∀ h ∈ V, D.Kills (MonoidAlgebra.single h 1 - 1)) (x : MonoidAlgebra A G) :
    x - MonoidAlgebra.mapDomain (fun q : G ⧸ V => q.out)
      (MonoidAlgebra.mapDomainRingHom A (QuotientGroup.mk' V) x) ∈ D.toDet.ker := by
  have hker : ∀ h ∈ V, MonoidAlgebra.single h (1 : A) - 1 ∈ D.toDet.ker := fun h hh =>
    (UpperTheory.V.CA.d_ker D.toDet _).1.2 ((UpperTheory.V.CA.d_toDet D _).2.2.2.2 (hV h hh))
  rw [MonoidAlgebra.mapDomainRingHom_apply]
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [MonoidAlgebra.mapDomain_add, MonoidAlgebra.mapDomain_add]
    have := D.toDet.ker.add_mem ha hb
    convert this using 1
    abel
  | single g r =>
    rw [MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single]
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V g
    have hv' : (QuotientGroup.mk' V g).out = g * v := hv
    rw [hv']
    have heq : MonoidAlgebra.single g r - MonoidAlgebra.single (g * (v : G)) r
        = -(MonoidAlgebra.single g r * (MonoidAlgebra.single (v : G) (1 : A) - 1)) := by
      rw [mul_sub, mul_one, MonoidAlgebra.single_mul_single, mul_one]
      abel
    rw [heq]
    exact D.toDet.ker.neg_mem (D.toDet.ker.mul_mem_left _ _ (hker _ v.2))

/- English proof (translation)
Introduce `n R G _ _ _ _ _ _ D I hD N`. Take `⟨V, hV⟩` from `UpperTheory.V.CA.exists_openNormalSubgroup_kills_of_groupDetLaw_isCont D I hD N`. Use `⟨V, ?_⟩` and prove the remaining obligations. Introduce `i x y hxy`. Use `set f := Ideal.Quotient.mk (I ^ N)`.

Use `set D' := D.map f`. Establish `hcomm : ∀ z : MonoidAlgebra R G, MonoidAlgebra.mapDomainRingHom (R ⧸ I ^ N) (QuotientGroup.mk' V.toSubgroup) (MonoidAlgebra.mapRingHom G f z) = MonoidAlgebra.mapRingHom (G ⧸ V.toSubgroup) f (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' V.toSubgroup) z)`. Introduce `z`. Proceed by induction on `z using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `single g r => simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]`. Establish `key : ∀ z : MonoidAlgebra R G, D'.lam i (MonoidAlgebra.mapRingHom G f z) = D'.lam i (MonoidAlgebra.mapDomain (fun q : G ⧸ V.toSubgroup => q.out) (MonoidAlgebra.mapDomainRingHom (R ⧸ I ^ N) (QuotientGroup.mk' V.toSubgroup) (MonoidAlgebra.mapRingHom G f z)))`. Introduce `z`. Rewrite using `[← (UpperTheory.V.CA.d_toDet D' _).2.1 i, ← (UpperTheory.V.CA.d_toDet D' _).2.1 i]`.

Conclude with `lam_eq_of_ker D'.toDet (sub_mem_ker D' V.toSubgroup hV _) i`. Establish `h1` using `key x`. Establish `h2` using `key y`. Rewrite `h1` using `[hcomm x, hxy, ← hcomm y, ← h2]`. Rewrite `h1` using `[((UpperTheory.V.CA.d_gmap D).2.2.1 f x).2 i, ((UpperTheory.V.CA.d_gmap D).2.2.1 f y).2 i]`.

Conclude with `Ideal.Quotient.eq.1 h1`.
-/
theorem UpperTheory.V.Pa.Core.dSees :
    ∀ (n : ℕ) (R G : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (D : GDet n R G) (I : Ideal R), D.IsCont I → ∀ N : ℕ, ∃ V : OpenNormalSubgroup G, Sees D V.toSubgroup (I ^ N) := by
  intro n R G _ _ _ _ _ _ D I hD N
  obtain ⟨V, hV⟩ := UpperTheory.V.CA.exists_openNormalSubgroup_kills_of_groupDetLaw_isCont D I hD N
  refine ⟨V, ?_⟩
  intro i x y hxy
  set f := Ideal.Quotient.mk (I ^ N)
  set D' := D.map f
  have hcomm : ∀ z : MonoidAlgebra R G,
      MonoidAlgebra.mapDomainRingHom (R ⧸ I ^ N) (QuotientGroup.mk' V.toSubgroup)
          (MonoidAlgebra.mapRingHom G f z) =
        MonoidAlgebra.mapRingHom (G ⧸ V.toSubgroup) f
          (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' V.toSubgroup) z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  have key : ∀ z : MonoidAlgebra R G, D'.lam i (MonoidAlgebra.mapRingHom G f z) =
      D'.lam i (MonoidAlgebra.mapDomain (fun q : G ⧸ V.toSubgroup => q.out)
        (MonoidAlgebra.mapDomainRingHom (R ⧸ I ^ N) (QuotientGroup.mk' V.toSubgroup)
          (MonoidAlgebra.mapRingHom G f z))) := by
    intro z
    rw [← (UpperTheory.V.CA.d_toDet D' _).2.1 i, ← (UpperTheory.V.CA.d_toDet D' _).2.1 i]
    exact lam_eq_of_ker D'.toDet (sub_mem_ker D' V.toSubgroup hV _) i
  have h1 := key x
  have h2 := key y
  rw [hcomm x, hxy, ← hcomm y, ← h2] at h1
  rw [((UpperTheory.V.CA.d_gmap D).2.2.1 f x).2 i, ((UpperTheory.V.CA.d_gmap D).2.2.1 f y).2 i] at h1
  exact Ideal.Quotient.eq.1 h1
