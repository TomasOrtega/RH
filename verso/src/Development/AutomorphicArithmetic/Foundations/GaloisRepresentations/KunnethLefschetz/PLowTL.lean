import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfTwistCoverCocycle
import Development.EtaleCohomology.EtaleTrace.PtCoverPf
import Development.EtaleCohomology.EtaleTrace.TwZeroPfSplit
import Development.EtaleCohomology.EtaleTrace.PrimSplitPf
import Development.EtaleCohomology.EtaleTrace.CocEqPf
import Development.EtaleCohomology.EtaleTrace.EtaleTateTwistSectionConstantOnPointsOfConnected
import Development.EtaleCohomology.EtaleTrace.PtCovPf
import Development.EtaleCohomology.EtaleTrace.TateTwistSectionConstantOnPointsOfTwLocPtCov
import Development.EtaleCohomology.TateTwists.TwLocPfR
import Development.EtaleCohomology.TateTwists.TwSecLocPfZarR
import Development.EtaleCohomology.TateTwists.AlgPowPfR
import Development.EtaleCohomology.TateTwists.TwTorsPfR

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CochainComplex.HomComplex

namespace UpperTheory.Gal.KunnethLefschetz

/- English proof (translation)
The claim follows from `LateralTheory.EtaleFoundations.TwLocPf.TwLoc_of (LateralTheory.EtaleFoundations.TwSecLocPf.TwSecLoc_of_alg LateralTheory.EtaleFoundations.AlgPowPf.AlgPow_of) LateralTheory.EtaleFoundations.TwTorsPf.TwTors_of`.
-/
private theorem twLoc : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc :=
  LateralTheory.EtaleFoundations.TwLocPf.TwLoc_of
    (LateralTheory.EtaleFoundations.TwSecLocPf.TwSecLoc_of_alg LateralTheory.EtaleFoundations.AlgPowPf.AlgPow_of)
    LateralTheory.EtaleFoundations.TwTorsPf.TwTors_of

/- English proof (translation)
The claim follows from `TwZero_of_split twLoc PrimSplit_of`.
-/
private theorem twZero : TwZero := TwZero_of_split twLoc PrimSplit_of

/- English proof (translation)
The claim follows from `tateTwistSections_determinedByPoints_of_constant twLoc PtCov_of (tateTwistSection_constantOnPoints_of_twLoc_ptCov twLoc PtCov_of)`.
-/
private theorem lowSec : EtaleTateTwistSectionsDeterminedByPointsOfProper := tateTwistSections_determinedByPoints_of_constant twLoc PtCov_of (tateTwistSection_constantOnPoints_of_twLoc_ptCov twLoc PtCov_of)

/- English proof (translation)
Establish `h` using `Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) s`. Take `⟨t, ht⟩` from `PtCover_of k _ h`. Use `⟨t, ht.trans ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
private theorem exists_ofRings_sec_eq_twF_zero (k : Type) [Field k] [IsAlgClosed k] (q : ℕ) (s : Sec (tw q 0) (S k)) :
    ∃ t, ofRings.sec (twF q 0) (S k) t = s := by
  have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) s
  obtain ⟨t, ht⟩ := PtCover_of k _ h
  refine ⟨t, ht.trans ?_⟩
  simp
  rfl

/- English proof (translation)
Establish `h2` using `Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) t1 t2 h`. Establish `h3` using `PtCover_of k _ h2`. Establish `h4 : (Scheme.Γ ⋙ twF q 0).map (𝟙 (Opposite.op (S k))) t1 = (Scheme.Γ ⋙ twF q 0).map (𝟙 (Opposite.op (S k))) t2` using `h3`. Rewrite `h4` using `[CategoryTheory.Functor.map_id, ModuleCat.id_apply, ModuleCat.id_apply]`. Then use the resulting hypothesis.
-/
private theorem ofRings_sec_twF_zero_injective (k : Type) [Field k] [IsAlgClosed k] (q : ℕ)
    (t1 t2 : ToType ((Scheme.Γ ⋙ twF q 0).obj (Opposite.op (S k))))
    (h : ofRings.sec (twF q 0) (S k) t1 = ofRings.sec (twF q 0) (S k) t2) : t1 = t2 := by
  have h2 := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) t1 t2 h
  have h3 := PtCover_of k _ h2
  have h4 : (Scheme.Γ ⋙ twF q 0).map (𝟙 (Opposite.op (S k))) t1 =
      (Scheme.Γ ⋙ twF q 0).map (𝟙 (Opposite.op (S k))) t2 := h3
  rwa [CategoryTheory.Functor.map_id, ModuleCat.id_apply, ModuleCat.id_apply] at h4

/- English proof (translation)
Establish `hn` using `congrArg (fun φ => (ModuleCat.Hom.hom φ) (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Scheme.Γ ⋙ twF q 0).obj (Opposite.op U))) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).naturality x.op)`. Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply] at hn`. Use `hn.symm.trans ?_` and prove the remaining obligations. Use `congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app (Opposite.op V))) ?_` and prove the remaining obligations. Conclude with `congrArg Submodule.Quotient.mk Finsupp.mapDomain_single`.
-/
private theorem res_twGen_zero_eq_twGen_prim_map {q : ℕ} {U V : Scheme.{0}} (x : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res x (twGen 0 ζ) = twGen 0 (Prim.map (Scheme.Γ.map x.op).hom ζ) := by
  have hn := congrArg (fun φ => (ModuleCat.Hom.hom φ)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Scheme.Γ ⋙ twF q 0).obj (Opposite.op U)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).naturality x.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hn
  refine hn.symm.trans ?_
  refine congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app (Opposite.op V))) ?_
  exact congrArg Submodule.Quotient.mk Finsupp.mapDomain_single

/- English proof (translation)
Proceed by induction on `f using Finsupp.induction with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `single_add ξ c g _ _ ih`. Take `⟨n, hn⟩` from `ih`. Use `⟨c.down.val + n, ?_⟩` and prove the remaining obligations.

Establish `hc : c = ((c.down.val : ℕ) : ULift.{1, 0} (ZMod q))`. Apply `ULift.ext` to reduce the goal to its premises. Rewrite using `[ULift.down_natCast, ZMod.natCast_zmod_val]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_add, ← Finsupp.smul_single_one, map_smul, h, hn]`.

Use `_ = (c.down.val + n) • g0 := by`. Rewrite using `[add_nsmul, ← Nat.cast_smul_eq_nsmul (ULift.{1, 0} (ZMod q)) c.down.val, ← hc]`.
-/
private theorem exists_nsmul_eq_of_single_one_eq {q : ℕ} [NeZero q] {P N : Type*} [AddCommGroup N] [Module (ULift.{1, 0} (ZMod q)) N]
    (φ : (P →₀ ULift.{1, 0} (ZMod q)) →ₗ[ULift.{1, 0} (ZMod q)] N) (g0 : N)
    (h : ∀ ξ, φ (Finsupp.single ξ 1) = g0) (f : P →₀ ULift.{1, 0} (ZMod q)) :
    ∃ n : ℕ, φ f = n • g0 := by
  induction f using Finsupp.induction with
  | zero => exact ⟨0, by simp⟩
  | single_add ξ c g _ _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨c.down.val + n, ?_⟩
    have hc : c = ((c.down.val : ℕ) : ULift.{1, 0} (ZMod q)) := by
      apply ULift.ext
      rw [ULift.down_natCast, ZMod.natCast_zmod_val]
    calc φ (Finsupp.single ξ c + g) = c • g0 + n • g0 := by
          rw [map_add, ← Finsupp.smul_single_one, map_smul, h, hn]
      _ = (c.down.val + n) • g0 := by
          rw [add_nsmul, ← Nat.cast_smul_eq_nsmul (ULift.{1, 0} (ZMod q)) c.down.val, ← hc]

/- English proof (translation)
Simplify using `only [Sec.res, Sec.map]`. Rewrite using `[← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]`.
-/
private theorem sec_res_sec_map_comm {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (k : V ⟶ U)
    (b : Sec F U) : Sec.res k (Sec.map φ b) = Sec.map φ (Sec.res k b) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

/- English proof (translation)
Use `haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Take `⟨_, e, _, he2⟩` from `hA (ZMod (l ^ j)) (tw (l ^ j) 0)`. Take `⟨ζ0⟩` from `exists_prim l k hl j`. Set `φ : ((Prim (l ^ j) Γ(S k, ⊤)) →₀ ULift.{1, 0} (ZMod (l ^ j))) →ₗ[ULift.{1, 0} (ZMod (l ^ j))] Sec (tw (l ^ j) 0) (S k)` to `(ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF (l ^ j) 0)).app (Opposite.op (S k)))).comp (twRel (l ^ j) 0 Γ(S k, ⊤)).mkQ`. Establish `hone : one (l ^ j) (sch.obj (S k)) = e (S k) (twGen 0 ζ0)`.

Take `⟨α, hα, hev⟩` from `he2 (S k) (twGen 0 ζ0)`. Establish `hnat : ∀ (U : Scheme.{0}) (x : Sx (sch.obj (S k)) 0 U) (ζ : Prim (l ^ j) Γ(U, ⊤)), ev (α : Cochain _ _ 0) 0 0 (by simp) U x = resGen 0 ζ`. Introduce `U x ζ`. Rewrite using `[evNat (ZMod (l ^ j)) (tw (l ^ j) 0) (S k) U (α : Cochain _ _ 0) x, hev]`. Use `(sec_res_sec_map_comm (resι (ZMod (l ^ j)) (tw (l ^ j) 0)) (x : U ⟶ S k) (twGen 0 ζ0)).trans ?_` and prove the remaining obligations.

Conclude with `congrArg (Sec.map (resι (ZMod (l ^ j)) (tw (l ^ j) 0))) ((res_twGen_zero_eq_twGen_prim_map (x : U ⟶ S k) ζ0).trans (twZero (l ^ j) U _ ζ))`. Establish `h1` using `pick_spec (show ∃ c, (fun c => ∃ β : Cocycle ((chains (ZMod (l ^ j))).obj (sch.obj (S k))) (res (ZMod (l ^ j)) (tw (l ^ j) 0)) 0, CohomologyClass.mk β = c ∧ ∀ (U : Scheme) (x : Sx (sch.obj (S k)) 0 U) (ζ : Prim (l ^ j) Γ(U, ⊤)), ev (β : Cochain _ _ 0) 0 0 (by simp) U x = resGen 0 …`. Take `⟨β, hβ, hβev⟩` from `h1`. Use `hβ.symm.trans ((congrArg CohomologyClass.mk (CocEq_of _ _ _ β α (fun U x => ?_))).trans hα)` and prove the remaining obligations. Conclude with `(hβev U x (Prim.map (Scheme.Γ.map x.op).hom ζ0)).trans (hnat U x _).symm`.

Use `⟨fun z => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `exists_ofRings_sec_eq_twF_zero k (l ^ j) ((e (S k)).symm z)`. Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective (twRel (l ^ j) 0 Γ(S k, ⊤)) t`. Take `⟨n, hn⟩` from `exists_nsmul_eq_of_single_one_eq φ (twGen 0 ζ0) (fun ξ => (show φ (Finsupp.single ξ 1) = twGen 0 ζ0 from twZero (l ^ j) (S k) ξ ζ0)) f`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `hf : φ f = (e (S k)).symm z` using `ht`. Rewrite using `[hone, ← map_nsmul, ← hn, hf, AddEquiv.apply_symm_apply]`. Rewrite `ha` using `[hone, ← map_nsmul]`. Establish `hs : a • twGen 0 ζ0 = (0 : Sec (tw (l ^ j) 0) (S k))` using `(e (S k)).injective (ha.trans (map_zero _).symm)`. Establish `h3 : (Submodule.Quotient.mk (a • Finsupp.single ζ0 (1 : ULift.{1, 0} (ZMod (l ^ j)))) : (_ ⧸ twRel (l ^ j) 0 Γ(S k, ⊤))) = Submodule.Quotient.mk 0` using `ofRings_sec_twF_zero_injective k (l ^ j) _ _ (show φ (a • Finsupp.single ζ0 1) = φ 0 by`.

Rewrite using `[map_nsmul, map_zero]`. Conclude with `hs)`. Establish `h4` using `(Submodule.Quotient.mk_eq_zero _).1 (h3.trans (Submodule.Quotient.mk_zero _))`. Set `ψ` to `Finsupp.linearCombination (ULift.{1, 0} (ZMod (l ^ j))) (fun _ : Prim (l ^ j) Γ(S k, ⊤) => (1 : ULift.{1, 0} (ZMod (l ^ j))))`. Establish `hker : twRel (l ^ j) 0 Γ(S k, ⊤) ≤ LinearMap.ker ψ`.

Rewrite using `[twRel, Submodule.span_le]`. Introduce and unpack `x ⟨ζ, ξ, b, -, rfl⟩`. Simplify using `[ψ]`. Conclude with `sub_self (1 : ULift.{1, 0} (ZMod (l ^ j)))`. Establish `h5 : ψ (a • Finsupp.single ζ0 1) = 0` using `hker h4`.

Establish `h6 : ((a : ZMod (l ^ j))) = 0`. Use `congrArg ULift.down h5` as an intermediate fact. Simplify `this` using `[ψ]`. Conclude with `(ZMod.natCast_eq_zero_iff a (l ^ j)).1 h6`.
-/
private theorem lowPt (hA : A9) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (hl : (l : k) ≠ 0) (j : ℕ) :
    (∀ z : Ht (l ^ j) (sch.obj (S k)) 0 0, ∃ a : ℕ, z = a • one (l ^ j) (sch.obj (S k))) ∧
      ∀ a : ℕ, a • one (l ^ j) (sch.obj (S k)) = 0 → l ^ j ∣ a := by
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_, e, _, he2⟩ := hA (ZMod (l ^ j)) (tw (l ^ j) 0)
  obtain ⟨ζ0⟩ := exists_prim l k hl j
  let φ : ((Prim (l ^ j) Γ(S k, ⊤)) →₀ ULift.{1, 0} (ZMod (l ^ j))) →ₗ[ULift.{1, 0} (ZMod (l ^ j))]
      Sec (tw (l ^ j) 0) (S k) :=
    (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF (l ^ j) 0)).app
      (Opposite.op (S k)))).comp (twRel (l ^ j) 0 Γ(S k, ⊤)).mkQ
  have hone : one (l ^ j) (sch.obj (S k)) = e (S k) (twGen 0 ζ0) := by
    obtain ⟨α, hα, hev⟩ := he2 (S k) (twGen 0 ζ0)
    have hnat : ∀ (U : Scheme.{0}) (x : Sx (sch.obj (S k)) 0 U) (ζ : Prim (l ^ j) Γ(U, ⊤)),
        ev (α : Cochain _ _ 0) 0 0 (by simp) U x = resGen 0 ζ := by
      intro U x ζ
      rw [evNat (ZMod (l ^ j)) (tw (l ^ j) 0) (S k) U (α : Cochain _ _ 0) x, hev]
      refine (sec_res_sec_map_comm (resι (ZMod (l ^ j)) (tw (l ^ j) 0)) (x : U ⟶ S k) (twGen 0 ζ0)).trans ?_
      exact congrArg (Sec.map (resι (ZMod (l ^ j)) (tw (l ^ j) 0)))
        ((res_twGen_zero_eq_twGen_prim_map (x : U ⟶ S k) ζ0).trans (twZero (l ^ j) U _ ζ))
    have h1 := pick_spec (show ∃ c, (fun c => ∃ β : Cocycle ((chains (ZMod (l ^ j))).obj (sch.obj (S k)))
        (res (ZMod (l ^ j)) (tw (l ^ j) 0)) 0, CohomologyClass.mk β = c ∧
          ∀ (U : Scheme) (x : Sx (sch.obj (S k)) 0 U) (ζ : Prim (l ^ j) Γ(U, ⊤)),
            ev (β : Cochain _ _ 0) 0 0 (by simp) U x = resGen 0 ζ) c from ⟨_, α, hα, hnat⟩)
    obtain ⟨β, hβ, hβev⟩ := h1
    refine hβ.symm.trans ((congrArg CohomologyClass.mk (CocEq_of _ _ _ β α (fun U x => ?_))).trans hα)
    exact (hβev U x (Prim.map (Scheme.Γ.map x.op).hom ζ0)).trans (hnat U x _).symm
  refine ⟨fun z => ?_, fun a ha => ?_⟩
  · obtain ⟨t, ht⟩ := exists_ofRings_sec_eq_twF_zero k (l ^ j) ((e (S k)).symm z)
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (twRel (l ^ j) 0 Γ(S k, ⊤)) t
    obtain ⟨n, hn⟩ := exists_nsmul_eq_of_single_one_eq φ (twGen 0 ζ0)
      (fun ξ => (show φ (Finsupp.single ξ 1) = twGen 0 ζ0 from twZero (l ^ j) (S k) ξ ζ0)) f
    refine ⟨n, ?_⟩
    have hf : φ f = (e (S k)).symm z := ht
    rw [hone, ← map_nsmul, ← hn, hf, AddEquiv.apply_symm_apply]
  · rw [hone, ← map_nsmul] at ha
    have hs : a • twGen 0 ζ0 = (0 : Sec (tw (l ^ j) 0) (S k)) :=
      (e (S k)).injective (ha.trans (map_zero _).symm)
    have h3 : (Submodule.Quotient.mk (a • Finsupp.single ζ0 (1 : ULift.{1, 0} (ZMod (l ^ j)))) :
        (_ ⧸ twRel (l ^ j) 0 Γ(S k, ⊤))) = Submodule.Quotient.mk 0 :=
      ofRings_sec_twF_zero_injective k (l ^ j) _ _ (show φ (a • Finsupp.single ζ0 1) = φ 0 by
        rw [map_nsmul, map_zero]
        exact hs)
    have h4 := (Submodule.Quotient.mk_eq_zero _).1 (h3.trans (Submodule.Quotient.mk_zero _))
    let ψ := Finsupp.linearCombination (ULift.{1, 0} (ZMod (l ^ j)))
      (fun _ : Prim (l ^ j) Γ(S k, ⊤) => (1 : ULift.{1, 0} (ZMod (l ^ j))))
    have hker : twRel (l ^ j) 0 Γ(S k, ⊤) ≤ LinearMap.ker ψ := by
      rw [twRel, Submodule.span_le]
      rintro x ⟨ζ, ξ, b, -, rfl⟩
      simp [ψ]
      exact sub_self (1 : ULift.{1, 0} (ZMod (l ^ j)))
    have h5 : ψ (a • Finsupp.single ζ0 1) = 0 := hker h4
    have h6 : ((a : ZMod (l ^ j))) = 0 := by
      have := congrArg ULift.down h5
      simpa [ψ] using this
    exact (ZMod.natCast_eq_zero_iff a (l ^ j)).1 h6

/- English proof (translation)
Introduce `hIn l _ k _ _ hl j`. Take `⟨_, e, he1, _⟩` from `(In.a9 hIn) (ZMod (l ^ j)) (tw (l ^ j) 0)`. Use `⟨lowPt (In.a9 hIn) l k hl j, ?_⟩` and prove the remaining obligations. Introduce `X p hp z`. Establish `hz : ∀ y : Pt p, pull (ZMod (l ^ j)) (sch.map y.1) (tw (l ^ j) 0) 0 z = e (S k) (Sec.res y.1 ((e X).symm z))`.

Introduce `y`. Rewrite using `[← he1, AddEquiv.apply_symm_apply]`. Take `⟨h1, h2⟩` from `lowSec l k hl j p hp ((e X).symm z)`. Use `⟨fun hy => ?_, fun hc y y' => ?_⟩` and prove the remaining obligations. Establish `h0 : (e X).symm z = 0` using `h1 (fun y => (e (S k)).injective (by rw [← hz, hy y, map_zero]))`.

Use `congrArg (e X) h0` as an intermediate fact. Rewrite `this` using `[AddEquiv.apply_symm_apply, map_zero]`. Then use the resulting hypothesis. Rewrite using `[hz, hz, h2 hc y y']`.
-/
theorem lowTL_holds : LowTL := by
  intro hIn l _ k _ _ hl j
  obtain ⟨_, e, he1, _⟩ := (In.a9 hIn) (ZMod (l ^ j)) (tw (l ^ j) 0)
  refine ⟨lowPt (In.a9 hIn) l k hl j, ?_⟩
  intro X p hp z
  have hz : ∀ y : Pt p, pull (ZMod (l ^ j)) (sch.map y.1) (tw (l ^ j) 0) 0 z =
      e (S k) (Sec.res y.1 ((e X).symm z)) := by
    intro y
    rw [← he1, AddEquiv.apply_symm_apply]
  obtain ⟨h1, h2⟩ := lowSec l k hl j p hp ((e X).symm z)
  refine ⟨fun hy => ?_, fun hc y y' => ?_⟩
  · have h0 : (e X).symm z = 0 :=
      h1 (fun y => (e (S k)).injective (by rw [← hz, hy y, map_zero]))
    have := congrArg (e X) h0
    rwa [AddEquiv.apply_symm_apply, map_zero] at this
  · rw [hz, hz, h2 hc y y']

end UpperTheory.Gal.KunnethLefschetz
