import Development.EtaleCohomology.EtaleSheaves.LCSurjPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.DescentPf

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]`. Use `congr 1`. Apply `ULift.ext` to reduce the goal to its premises. Rewrite using `[ULift.down_natCast, ZMod.natCast_zmod_val]`.
-/
theorem val_smul {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}} (c : ZMod q) (x : Sec (tw q i) U) :
    c.val • x = (ULift.up c : ULift.{1} (ZMod q)) • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  congr 1
  apply ULift.ext
  rw [ULift.down_natCast, ZMod.natCast_zmod_val]

/- English proof (translation)
Introduce `q _ i m hm B _ ζ y hloc`. Take `⟨S, hS, hP⟩` from `hloc`. Establish `hform : ∀ {V W : Scheme.{0}} (g : V ⟶ Spec (CommRingCat.of B)) (h : W ⟶ V) (c : ZMod q), Sec.res g y = c.val • twGen i ((gam ζ).map g.appTop.hom) → Sec.res (h ≫ g) y = c.val • twGen i ((gam ζ).map (h ≫ g).appTop.hom)`. Introduce `V W g h c hc`. Establish `hs : ∀ x : Sec (tw q i) V, Sec.res h (c.val • x) = c.val • Sec.res h x` using `fun x => map_nsmul _ _ x`.

Rewrite using `[res_comp, hc, hs, LateralTheory.E.LCBijPf.twGen_res]`. Both sides reduce to the same expression. Establish `huniq : ∀ {V1 V2 : Scheme.{0}} (g1 : V1 ⟶ Spec (CommRingCat.of B)) (g2 : V2 ⟶ Spec (CommRingCat.of B)) (c1 c2 : ZMod q), Sec.res g1 y = c1.val • twGen i ((gam ζ).map g1.appTop.hom) → Sec.res g2 y = c2.val • twGen i ((gam ζ).map g2.appTop.hom) → ∀ v1 v2, g1 v1 = g2 v2 → c1 = c2`. Introduce `V1 V2 g1 g2 c1 c2 h1 h2 v1 v2 hv`. Take `⟨z, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback v1 v2 hv`.

Set `A` to `(pullback g1 g2).affineOpenCover`. Take `⟨w, -⟩` from `A.covers z`. Set `a` to `A.f (A.idx z)`. Establish `e1` using `hform g1 (a ≫ pullback.fst g1 g2) c1 h1`. Establish `e2` using `hform g2 (a ≫ pullback.snd g1 g2) c2 h2`.

Establish `hcomp : (a ≫ pullback.snd g1 g2) ≫ g2 = (a ≫ pullback.fst g1 g2) ≫ g1`. Simplify using `[pullback.condition]`. Rewrite `e2` using `[hcomp]`. Establish `hne : Nontrivial (A.X (A.idx z))` using `PrimeSpectrum.nontrivial w`. Take `⟨φ, hφ⟩` from `Spec.map_surjective ((a ≫ pullback.fst g1 g2) ≫ g1)`.

Establish `key` using `LateralTheory.E.LCBijPf.twGenNZ_of hAC q i (A.X (A.idx z)) (ζ.map φ.hom) (c1 - c2)`. Use `sub_eq_zero.1 (key ?_)` and prove the remaining obligations. Establish `e` using `e1.symm.trans e2`. Rewrite `e` using `[← hφ]`. Rewrite using `[LateralTheory.E.LCBijPf.gam_map]`.

Rewrite `e` using `[val_smul, val_smul]`. Establish `hup : (ULift.up (c1 - c2) : ULift.{1} (ZMod q)) = ULift.up c1 - ULift.up c2` using `rfl`. Rewrite using `[val_smul, hup, sub_smul, sub_eq_zero]`. Conclude with `e`. Take `⟨𝒰, h𝒰⟩` from `(Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS`.

Establish `hpiece : ∀ x : PrimeSpectrum B, ∃ (R : CommRingCat.{0}) (g : Spec R ⟶ Spec (CommRingCat.of B)), Etale g ∧ S.arrows g ∧ x ∈ Set.range g`. Introduce `x`. Take `⟨j, v, hv⟩` from `((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 x`. Set `A` to `(𝒰.X j).affineOpenCover`. Take `⟨w, hw⟩` from `A.covers v`.

Establish `: Etale (𝒰.f j)` using `((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).2 j`. Use `⟨A.X (A.idx v), A.f (A.idx v) ≫ 𝒰.f j, inferInstance, S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk j)) _, ⟨w, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.comp_apply, hw, hv]`. Use `choose R g hg hSg hx using hpiece`. Establish `hc : ∀ x, ∃ c : ZMod q, Sec.res (g x) y = c.val • twGen i ((gam ζ).map (g x).appTop.hom)` using `fun x => hP _ _ (hSg x)`.

Use `choose c hc using hc`. Establish `key : ∀ (x : PrimeSpectrum B) {V : Scheme.{0}} (g' : V ⟶ Spec (CommRingCat.of B)) (c' : ZMod q), Sec.res g' y = c'.val • twGen i ((gam ζ).map g'.appTop.hom) → ∀ v, g' v = x → c x = c'`. Introduce `x V g' c' h' v hv`. Take `⟨u, hu⟩` from `hx x`. Conclude with `huniq (g x) g' _ _ (hc x) h' u v (hu.trans hv.symm)`.

Establish `hlc : IsLocallyConstant c`. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Use `hg x` as an intermediate fact. Use `⟨Set.range (g x), (g x).isOpenMap.isOpen_range, hx x, fun x' hx' => ?_⟩` and prove the remaining obligations.

Take `⟨u, hu⟩` from `hx'`. Conclude with `key x' (g x) (c x) (hc x) u hu`. Set `ψ : LocallyConstant (PrimeSpectrum B) (ZMod q)` to `⟨c, hlc⟩`. Use `⟨ψ, Sieve.ofArrows (fun x => Spec (R x)) g, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Scheme.Cover.mem_grothendieckTopology (Scheme.Cover.mkOfCovers (P := @Etale) (PrimeSpectrum B) (fun x => Spec (R x)) g (fun x => by obtain ⟨u, hu⟩ := hx x; exact ⟨x, u, hu⟩) hg)`.

Introduce `V k hk`. Take `⟨W, h, k', hk', rfl⟩` from `hk`. Take `⟨x⟩` from `hk'`. Rewrite using `[res_comp, res_comp]`. Use `congr 1`.

Rewrite using `[hc x]`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (g x)`. Establish `hlc' : lcMap φ.hom ψ = LocallyConstant.const _ (c x)`. Use extensionality with `u`. Conclude with `key _ (g x) (c x) (hc x) u (by rw [← hφ]; rfl)`.

Establish `e` using `hm.1 B (R x) φ.hom ζ ψ`. Rewrite `e` using `[hlc', hm.2, LateralTheory.E.LCBijPf.gam_map]`. Rewrite using `[← hφ]`. Conclude with `e.symm`.
-/
theorem Descent_of (hAC : LateralTheory.E.LCBijPf.TwGenNZAC) : LateralTheory.E.LCSurjPf.Descent := by
  intro q _ i m hm B _ ζ y hloc
  obtain ⟨S, hS, hP⟩ := hloc
  have hform : ∀ {V W : Scheme.{0}} (g : V ⟶ Spec (CommRingCat.of B)) (h : W ⟶ V) (c : ZMod q),
      Sec.res g y = c.val • twGen i ((gam ζ).map g.appTop.hom) →
      Sec.res (h ≫ g) y = c.val • twGen i ((gam ζ).map (h ≫ g).appTop.hom) := by
    intro V W g h c hc
    have hs : ∀ x : Sec (tw q i) V, Sec.res h (c.val • x) = c.val • Sec.res h x := fun x => map_nsmul _ _ x
    rw [res_comp, hc, hs, LateralTheory.E.LCBijPf.twGen_res]
    rfl
  have huniq : ∀ {V1 V2 : Scheme.{0}} (g1 : V1 ⟶ Spec (CommRingCat.of B)) (g2 : V2 ⟶ Spec (CommRingCat.of B))
      (c1 c2 : ZMod q), Sec.res g1 y = c1.val • twGen i ((gam ζ).map g1.appTop.hom) →
      Sec.res g2 y = c2.val • twGen i ((gam ζ).map g2.appTop.hom) →
      ∀ v1 v2, g1 v1 = g2 v2 → c1 = c2 := by
    intro V1 V2 g1 g2 c1 c2 h1 h2 v1 v2 hv
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v1 v2 hv
    let A := (pullback g1 g2).affineOpenCover
    obtain ⟨w, -⟩ := A.covers z
    let a := A.f (A.idx z)
    have e1 := hform g1 (a ≫ pullback.fst g1 g2) c1 h1
    have e2 := hform g2 (a ≫ pullback.snd g1 g2) c2 h2
    have hcomp : (a ≫ pullback.snd g1 g2) ≫ g2 = (a ≫ pullback.fst g1 g2) ≫ g1 := by
      simp [pullback.condition]
    rw [hcomp] at e2
    have hne : Nontrivial (A.X (A.idx z)) := PrimeSpectrum.nontrivial w
    obtain ⟨φ, hφ⟩ := Spec.map_surjective ((a ≫ pullback.fst g1 g2) ≫ g1)
    have key := LateralTheory.E.LCBijPf.twGenNZ_of hAC q i (A.X (A.idx z)) (ζ.map φ.hom) (c1 - c2)
    refine sub_eq_zero.1 (key ?_)
    have e := e1.symm.trans e2
    rw [← hφ] at e
    rw [LateralTheory.E.LCBijPf.gam_map]
    rw [val_smul, val_smul] at e
    have hup : (ULift.up (c1 - c2) : ULift.{1} (ZMod q)) = ULift.up c1 - ULift.up c2 := rfl
    rw [val_smul, hup, sub_smul, sub_eq_zero]
    exact e
  obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
  have hpiece : ∀ x : PrimeSpectrum B, ∃ (R : CommRingCat.{0}) (g : Spec R ⟶ Spec (CommRingCat.of B)),
      Etale g ∧ S.arrows g ∧ x ∈ Set.range g := by
    intro x
    obtain ⟨j, v, hv⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 x
    let A := (𝒰.X j).affineOpenCover
    obtain ⟨w, hw⟩ := A.covers v
    have : Etale (𝒰.f j) := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).2 j
    refine ⟨A.X (A.idx v), A.f (A.idx v) ≫ 𝒰.f j, inferInstance, S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk j)) _, ⟨w, ?_⟩⟩
    rw [Scheme.Hom.comp_apply, hw, hv]
  choose R g hg hSg hx using hpiece
  have hc : ∀ x, ∃ c : ZMod q, Sec.res (g x) y = c.val • twGen i ((gam ζ).map (g x).appTop.hom) :=
    fun x => hP _ _ (hSg x)
  choose c hc using hc
  have key : ∀ (x : PrimeSpectrum B) {V : Scheme.{0}} (g' : V ⟶ Spec (CommRingCat.of B)) (c' : ZMod q),
      Sec.res g' y = c'.val • twGen i ((gam ζ).map g'.appTop.hom) → ∀ v, g' v = x → c x = c' := by
    intro x V g' c' h' v hv
    obtain ⟨u, hu⟩ := hx x
    exact huniq (g x) g' _ _ (hc x) h' u v (hu.trans hv.symm)
  have hlc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    have := hg x
    refine ⟨Set.range (g x), (g x).isOpenMap.isOpen_range, hx x, fun x' hx' => ?_⟩
    obtain ⟨u, hu⟩ := hx'
    exact key x' (g x) (c x) (hc x) u hu
  let ψ : LocallyConstant (PrimeSpectrum B) (ZMod q) := ⟨c, hlc⟩
  refine ⟨ψ, Sieve.ofArrows (fun x => Spec (R x)) g, ?_, ?_⟩
  · exact Scheme.Cover.mem_grothendieckTopology
      (Scheme.Cover.mkOfCovers (P := @Etale) (PrimeSpectrum B) (fun x => Spec (R x)) g
        (fun x => by obtain ⟨u, hu⟩ := hx x; exact ⟨x, u, hu⟩) hg)
  · intro V k hk
    obtain ⟨W, h, k', hk', rfl⟩ := hk
    obtain ⟨x⟩ := hk'
    rw [res_comp, res_comp]
    congr 1
    rw [hc x]
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (g x)
    have hlc' : lcMap φ.hom ψ = LocallyConstant.const _ (c x) := by
      ext u
      exact key _ (g x) (c x) (hc x) u (by rw [← hφ]; rfl)
    have e := hm.1 B (R x) φ.hom ζ ψ
    rw [hlc', hm.2, LateralTheory.E.LCBijPf.gam_map] at e
    rw [← hφ]
    exact e.symm

end LateralTheory.E.DescentPf
