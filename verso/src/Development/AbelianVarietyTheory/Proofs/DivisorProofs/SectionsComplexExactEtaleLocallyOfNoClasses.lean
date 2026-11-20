import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSections
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.SchLocExact

variable {R : Type} [CommRing R]

/- English proof (translation)
Simplify using `only [Sec.map, Sec.res]`. Conclude with `congrArg (fun f => f.hom x) (ψ.hom.naturality g.op)`.
-/
theorem map_res {F G : Shv R} (ψ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map ψ (Sec.res g x) = Sec.res g (Sec.map ψ x) := by
  simp only [Sec.map, Sec.res]
  exact congrArg (fun f => f.hom x) (ψ.hom.naturality g.op)

/- English proof (translation)
Simplify using `[Sec.map]`.
-/
theorem map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := by
  simp [Sec.map]

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
theorem res_res {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.res f x) = Sec.res (g ≫ f) x := by
  simp [Sec.res]

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
theorem res_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

/- English proof (translation)
It suffices to establish `H : ∀ x : CohomologyClass K M n, x = 0 from ⟨fun x y => (H x).trans (H y).symm⟩`. Introduce `x`. Take `⟨α, rfl⟩` from `x.mk_surjective`. Establish `h0 : cpull e.inv M n (CohomologyClass.mk α) = 0` using `Subsingleton.elim _ _`. Establish `key : cpull e.hom M n (cpull e.inv M n (CohomologyClass.mk α)) = CohomologyClass.mk α`.

Express the relevant statement in the definitionally equal form `CohomologyClass.mk (zcomp (Cocycle.ofHom e.hom) (zcomp (Cocycle.ofHom e.inv) α (zero_add n)) (zero_add n)) = CohomologyClass.mk α`. Rewrite using `[← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]`. Use `⟨n.negOnePow • (Cochain.ofHomotopy e.homotopyHomInvId).comp α.1 (by omega), ?_⟩` and prove the remaining obligations. Rewrite using `[δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) (by omega), Cocycle.δ_eq_zero, δ_ofHomotopy]`. Use extensionality with `p q hpq`.

Simplify using `[zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq, smul_smul]`. Rewrite using `[← key, h0, map_zero]`.
-/
theorem subsingleton_of_homotopyEquiv {K L M : Cx R} (e : HomotopyEquiv K L) (n : ℤ)
    (h : Subsingleton (CohomologyClass L M n)) : Subsingleton (CohomologyClass K M n) := by
  suffices H : ∀ x : CohomologyClass K M n, x = 0 from ⟨fun x y => (H x).trans (H y).symm⟩
  intro x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have h0 : cpull e.inv M n (CohomologyClass.mk α) = 0 := Subsingleton.elim _ _
  have key : cpull e.hom M n (cpull e.inv M n (CohomologyClass.mk α)) = CohomologyClass.mk α := by
    change CohomologyClass.mk (zcomp (Cocycle.ofHom e.hom) (zcomp (Cocycle.ofHom e.inv) α (zero_add n)) (zero_add n)) =
      CohomologyClass.mk α
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨n.negOnePow • (Cochain.ofHomotopy e.homotopyHomInvId).comp α.1 (by omega), ?_⟩
    rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) (by omega), Cocycle.δ_eq_zero, δ_ofHomotopy]
    ext p q hpq
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq, smul_smul]
  rw [← key, h0, map_zero]

/- English proof (translation)
Establish `h0 : CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add m) (m + 1) rfl hf) = 0` using `Subsingleton.elim _ _`. Rewrite `h0` using `[CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ m' hm]`. Conclude with `h0`.
-/
theorem lift_of_subsingleton {A : Shv R} {M : Cx R} {m' m : ℤ} (hm : m' + 1 = m)
    (hA : Subsingleton (CohomologyClass (sgl A) M m)) (f : A ⟶ M.X m) (hf : f ≫ M.d m (m + 1) = 0) :
    ∃ g : A ⟶ M.X m', g ≫ M.d m' m = f := by
  have h0 : CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add m) (m + 1) rfl hf) = 0 := Subsingleton.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ m' hm] at h0
  exact h0

end GlobalTheory.EtC.SchLocExact

open GlobalTheory.EtC.SchLocExact in

/- English proof (translation)
Introduce `R _ M U hU n b hb`. Take `⟨e, -, -⟩` from `GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R`. Establish `hs : Subsingleton (CohomologyClass (sgl ((free R).obj (yoneda.obj U))) M n)` using `subsingleton_of_homotopyEquiv (e (yoneda.obj U)) n (hU n)`. Take `⟨hex, -, -, -⟩` from `GlobalTheory.EtC.free_hom_sections R (yoneda.obj U) (M.X n)`. Take `⟨φ, hφ⟩` from `hex (fun V x => Sec.res x b) (fun V W g x => res_res g x b)`.

Establish `hφd : φ ≫ M.d n (n + 1) = 0`. Apply `(GlobalTheory.EtC.free_hom_sections R (yoneda.obj U) (M.X (n + 1))).2.1` to reduce the goal to its premises. Introduce `W x`. Rewrite using `[map_comp, hφ, map_res, hb]`. Simplify using `[Sec.map, Sec.res]`.

Take `⟨ψ, hψ⟩` from `lift_of_subsingleton (m' := n - 1) (by omega) hs φ hφd`. Set `a0 : Sec (M.X (n - 1)) U` to `Sec.map ψ (freeGen R (yoneda.obj U) U (𝟙 U))`. Establish `ha0 : Sec.map (M.d (n - 1) n) a0 = b`. Simplify using `only [a0]`. Rewrite using `[← map_comp, hψ, hφ, res_id]`.

Use `⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨Sec.res g a0, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_res, ha0]`.
-/
theorem GlobalTheory.EtC.sch_loc_exact : ∀ (R : Type) [CommRing R] (M : Cx R) (U : Scheme.{0}),
    (∀ n, Subsingleton (CohomologyClass ((chains R).obj (sch.obj U)) M n)) → ∀ (n : ℤ) (b : Sec (M.X n) U),
    Sec.map (M.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (M.X (n - 1)) V, Sec.map (M.d (n - 1) n) a = Sec.res g b := by
  intro R _ M U hU n b hb
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  have hs : Subsingleton (CohomologyClass (sgl ((free R).obj (yoneda.obj U))) M n) :=
    subsingleton_of_homotopyEquiv (e (yoneda.obj U)) n (hU n)
  obtain ⟨hex, -, -, -⟩ := GlobalTheory.EtC.free_hom_sections R (yoneda.obj U) (M.X n)
  obtain ⟨φ, hφ⟩ := hex (fun V x => Sec.res x b) (fun V W g x => res_res g x b)
  have hφd : φ ≫ M.d n (n + 1) = 0 := by
    apply (GlobalTheory.EtC.free_hom_sections R (yoneda.obj U) (M.X (n + 1))).2.1
    intro W x
    rw [map_comp, hφ, map_res, hb]
    simp [Sec.map, Sec.res]
  obtain ⟨ψ, hψ⟩ := lift_of_subsingleton (m' := n - 1) (by omega) hs φ hφd
  let a0 : Sec (M.X (n - 1)) U := Sec.map ψ (freeGen R (yoneda.obj U) U (𝟙 U))
  have ha0 : Sec.map (M.d (n - 1) n) a0 = b := by
    simp only [a0]
    rw [← map_comp, hψ, hφ, res_id]
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨Sec.res g a0, ?_⟩⟩
  rw [map_res, ha0]
