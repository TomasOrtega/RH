import Development.EtaleCohomology.KummerTheory.BockCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedPostPf
open LateralTheory.KummerTheory.BockCut

variable {S R T : Type} [CommRing S] [CommRing R] [CommRing T]

/- English proof (translation)
Establish `h` using `φ.hom.naturality g.op`. Conclude with `(congrArg (fun f => f.hom a) h).symm`.
-/
theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun f => f.hom a) h).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sec_comp {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ ≫ ψ) a = Sec.map ψ (Sec.map φ a) := rfl

def scomp {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J) (σ : SemiMap J K) : SemiMap I K where
  app U s := (σ.app U s).comp (ρ.app U s)
  nat g s a := by simp only [AddMonoidHom.comp_apply]; rw [σ.nat, ρ.nat]
  comm U s t a := by simp only [AddMonoidHom.comp_apply]; rw [σ.comm, ρ.comm]

def spost {I : Cx S} {J J' : Cx R} (ρ : SemiMap I J) (u : J ⟶ J') : SemiMap I J' where
  app U s := ((u.f s).hom.app (op U)).hom.toAddMonoidHom.comp (ρ.app U s)
  nat g s a := by
    change Sec.res g (Sec.map (u.f s) (ρ.app _ s a)) = Sec.map (u.f s) (ρ.app _ s (Sec.res g a))
    rw [sec_nat, ρ.nat]
  comm U s t a := by
    change Sec.map (J'.d s t) (Sec.map (u.f s) (ρ.app U s a)) = Sec.map (u.f t) (ρ.app U t (Sec.map (I.d s t) a))
    rw [← ρ.comm, ← sec_comp, ← sec_comp, u.comm]

/- English proof (translation)
Take `⟨α, rfl⟩` from `CohomologyClass.mk_surjective x`. Take `⟨β, hβ⟩` from `(hS S R ρ).1 E n α`. Take `⟨γ, hγ⟩` from `(hS R T σ).1 E n β`. Rewrite using `[(hS S R ρ).2 E n α β hβ, (hS R T σ).2 E n β γ hγ, (hS S T (scomp ρ σ)).2 E n α γ ?_]`. Introduce `p s h U y`.

Rewrite using `[hγ, hβ]`. Both sides reduce to the same expression.
-/
theorem scomp_op (hS : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses) {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J)
    (σ : SemiMap J K) (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) I n) :
    (scomp ρ σ).op.app E n x = σ.op.app E n (ρ.op.app E n x) := by
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨β, hβ⟩ := (hS S R ρ).1 E n α
  obtain ⟨γ, hγ⟩ := (hS R T σ).1 E n β
  rw [(hS S R ρ).2 E n α β hβ, (hS R T σ).2 E n β γ hγ, (hS S T (scomp ρ σ)).2 E n α γ ?_]
  intro p s h U y
  rw [hγ, hβ]
  rfl

end LateralTheory.KummerTheory.RedPostPf

namespace LateralTheory.KummerTheory.RedPostPf
open LateralTheory.KummerTheory.BockCut

variable {S R : Type} [CommRing S] [CommRing R]

def up {F : Shv S} (φ : R →+* S) {U : Scheme.{0}} (a : Sec ((restr φ).obj F) U) : Sec F U := a

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem up_add {F : Shv S} (φ : R →+* S) {U : Scheme.{0}} (a b : Sec ((restr φ).obj F) U) :
    up φ (a + b) = up φ a + up φ b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem up_res {F : Shv S} (φ : R →+* S) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec ((restr φ).obj F) U) :
    Sec.res g (up φ a) = up φ (Sec.res g a) := rfl

/- English proof (translation)
The claim follows from `map_add _ _ _`.
-/
theorem sec_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ _ _

/- English proof (translation)
Introduce `Q q _ hq i π hπ E n x`. Establish `: NeZero q` using `⟨ne_zero_of_dvd_ne_zero (NeZero.ne Q) hq⟩`. Set `ρ` to `scomp (redMap Q q i) (restrMap (Int.castRingHom (ZMod q)) (tw q i))`. Set `r0` to `restrMap (Int.castRingHom (ZMod Q)) (tw Q i)`. Set `ρ'` to `spost r0 (resMap ℤ π)`.

Establish `h1 : restrH (Int.castRingHom (ZMod q)) E (tw q i) n (red Q q E n i x) = ρ.op.app E n x` using `(scomp_op hS _ _ E n x).symm`. Establish `h2 : HK.post ℤ ((chains ℤ).obj E) π n (restrH (Int.castRingHom (ZMod Q)) E (tw Q i) n x) = ρ'.op.app E n x` using `((hC (ZMod Q) ℤ r0 ρ' (resMap ℤ π) (fun _ _ _ => rfl)).1 E n x).symm`. Rewrite using `[h1, h2]`. Take `⟨φ1, hφ1⟩` from `hZ (TZ Q i) ((res ℤ (TZ q i)).X 0) (fun U => AddMonoidHom.mk' (fun a : Sec (TZ Q i) U => ρ.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a))) (fun a b => by rw [up_add, sec_add, map_add])) (fun V U g a => by`. Express the relevant statement in the definitionally equal form `Sec.res g (ρ.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a))) = ρ.app V 0 (Sec.map (resι _ (tw Q i)) (up _ (Sec.res g a)))`.

Rewrite using `[ρ.nat, sec_nat, up_res])`. Take `⟨φ2, hφ2⟩` from `hZ (TZ Q i) ((res ℤ (TZ q i)).X 0) (fun U => AddMonoidHom.mk' (fun a : Sec (TZ Q i) U => ρ'.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a))) (fun a b => by rw [up_add, sec_add, map_add])) (fun V U g a => by`. Express the relevant statement in the definitionally equal form `Sec.res g (ρ'.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a))) = ρ'.app V 0 (Sec.map (resι _ (tw Q i)) (up _ (Sec.res g a)))`. Rewrite using `[ρ'.nat, sec_nat, up_res])`. Establish `heq : φ1 = φ2`.

Use `hE Q i _ φ1 φ2 fun U ζ => ?_` and prove the remaining obligations. Take `⟨ξ, hξ⟩` from `(hP Q Γ(U, ⊤)).2.2.2.2.2 q hq ζ`. Rewrite using `[hφ1, hφ2]`. Express the relevant statement in the definitionally equal form `(restrMap (Int.castRingHom (ZMod q)) (tw q i)).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) = Sec.map ((resMap ℤ π).f 0) (r0.app U 0 (Sec.map (resι _ (tw Q i)) (twGen i ζ)))`. Rewrite using `[hR Q q hq i U ζ ξ hξ, hX ℤ (ZMod Q) _ (tw Q i) U (twGen i ζ)]`.

Express the relevant statement in the definitionally equal form `(restrMap (Int.castRingHom (ZMod q)) (tw q i)).app U 0 (Sec.map (resι _ (tw q i)) (twGen i ξ)) = _`. Rewrite using `[hX ℤ (ZMod q) _ (tw q i) U (twGen i ξ), ← sec_comp, ((hB ℤ (TZ Q i)).2.2.2.2.2.2.2 (TZ q i) π).2, sec_comp]`. Conclude with `congrArg (Sec.map (resι ℤ (TZ q i))) (hπ U ζ ξ hξ).symm`. Use `hU (ZMod Q) (tw Q i) (TZ q i) ρ ρ' (fun U a => ?_) E n x` and prove the remaining obligations. Establish `e1` using `hφ1 U a`.

Establish `e2` using `hφ2 U a`. Rewrite `e1` using `[heq]`. Conclude with `e1.symm.trans e2`.
-/
theorem RedPost_of (hU : SemiUniq) (hE : TwExt) (hZ : ZHom) (hS : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses)
    (hC : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible) (hR : LateralTheory.EtaleFoundations.EtaleRootsOfUnityReductionMapGenerator) (hX : LateralTheory.EtaleFoundations.EtaleRestrictScalarsResolutionCompatible)
    (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities) (hB : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) : RedPost := by
  intro Q q _ hq i π hπ E n x
  have : NeZero q := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne Q) hq⟩
  let ρ := scomp (redMap Q q i) (restrMap (Int.castRingHom (ZMod q)) (tw q i))
  let r0 := restrMap (Int.castRingHom (ZMod Q)) (tw Q i)
  let ρ' := spost r0 (resMap ℤ π)
  have h1 : restrH (Int.castRingHom (ZMod q)) E (tw q i) n (red Q q E n i x) = ρ.op.app E n x :=
    (scomp_op hS _ _ E n x).symm
  have h2 : HK.post ℤ ((chains ℤ).obj E) π n (restrH (Int.castRingHom (ZMod Q)) E (tw Q i) n x) = ρ'.op.app E n x :=
    ((hC (ZMod Q) ℤ r0 ρ' (resMap ℤ π) (fun _ _ _ => rfl)).1 E n x).symm
  rw [h1, h2]
  obtain ⟨φ1, hφ1⟩ := hZ (TZ Q i) ((res ℤ (TZ q i)).X 0)
    (fun U => AddMonoidHom.mk' (fun a : Sec (TZ Q i) U => ρ.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a)))
      (fun a b => by rw [up_add, sec_add, map_add]))
    (fun V U g a => by
      change Sec.res g (ρ.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a))) = ρ.app V 0 (Sec.map (resι _ (tw Q i)) (up _ (Sec.res g a)))
      rw [ρ.nat, sec_nat, up_res])
  obtain ⟨φ2, hφ2⟩ := hZ (TZ Q i) ((res ℤ (TZ q i)).X 0)
    (fun U => AddMonoidHom.mk' (fun a : Sec (TZ Q i) U => ρ'.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a)))
      (fun a b => by rw [up_add, sec_add, map_add]))
    (fun V U g a => by
      change Sec.res g (ρ'.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a))) = ρ'.app V 0 (Sec.map (resι _ (tw Q i)) (up _ (Sec.res g a)))
      rw [ρ'.nat, sec_nat, up_res])
  have heq : φ1 = φ2 := by
    refine hE Q i _ φ1 φ2 fun U ζ => ?_
    obtain ⟨ξ, hξ⟩ := (hP Q Γ(U, ⊤)).2.2.2.2.2 q hq ζ
    rw [hφ1, hφ2]
    change (restrMap (Int.castRingHom (ZMod q)) (tw q i)).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) =
      Sec.map ((resMap ℤ π).f 0) (r0.app U 0 (Sec.map (resι _ (tw Q i)) (twGen i ζ)))
    rw [hR Q q hq i U ζ ξ hξ, hX ℤ (ZMod Q) _ (tw Q i) U (twGen i ζ)]
    change (restrMap (Int.castRingHom (ZMod q)) (tw q i)).app U 0 (Sec.map (resι _ (tw q i)) (twGen i ξ)) = _
    rw [hX ℤ (ZMod q) _ (tw q i) U (twGen i ξ), ← sec_comp, ((hB ℤ (TZ Q i)).2.2.2.2.2.2.2 (TZ q i) π).2, sec_comp]
    exact congrArg (Sec.map (resι ℤ (TZ q i))) (hπ U ζ ξ hξ).symm
  refine hU (ZMod Q) (tw Q i) (TZ q i) ρ ρ' (fun U a => ?_) E n x
  have e1 := hφ1 U a
  have e2 := hφ2 U a
  rw [heq] at e1
  exact e1.symm.trans e2

end LateralTheory.KummerTheory.RedPostPf
