import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling
import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.HkpullComp

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.SecondDegreeKilling.Nbhd
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling.Comp

/- English proof (translation)
Substitute `hu he` using the available equality. Both sides reduce to the same expression.
-/
theorem rpl_congr (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (u₁ u₂ : U' ⟶ U) (e₁ e₂ : E' ⟶ E)
    (h₁ : f' ≫ e₁ = u₁ ≫ f) (h₂ : f' ≫ e₂ = u₂ ≫ f) (hu : u₁ = u₂) (he : e₁ = e₂) (n : ℤ) :
    rpl q i f f' u₁ e₁ h₁ n = rpl q i f f' u₂ e₂ h₂ n := by
  subst hu he; rfl

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Apply the tactic sequence `erw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc] first | simp [resY_comp] | (rw [Category.assoc]; rfl)`. Use `erw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]`. Simplify using `only [Category.assoc]`. Both sides reduce to the same expression.
-/
theorem resY_comp {Y B : Scheme.{0}} (p : Y ⟶ B) {U U' U'' : B.Etale} (c : U'' ⟶ U') (a : U' ⟶ U) :
    resY p (c ≫ a) = resY p c ≫ resY p a := by
  apply pullback.hom_ext
  · erw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    first | simp [resY_comp] | (rw [Category.assoc]; rfl)
  · erw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    simp only [Category.assoc]; rfl

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Apply the tactic sequence `erw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc] first | simp [resY_comp] | (rw [resY_comp, Category.assoc])`. Apply the tactic sequence `erw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc] first | simp [resY_comp] | (rw [Category.assoc]; rfl)`.
-/
theorem resYW_comp {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {U U' U'' : B.Etale} (c : U'' ⟶ U') (a : U' ⟶ U) :
    resYW p ι (c ≫ a) = resYW p ι c ≫ resYW p ι a := by
  apply pullback.hom_ext
  · erw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    first | simp [resY_comp] | (rw [resY_comp, Category.assoc])
  · erw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    first | simp [resY_comp] | (rw [Category.assoc]; rfl)

/- English proof (translation)
Simplify using `only [rY]`. Establish `h1 : resYW p ι c ≫ prU p ι U' = prU p ι U'' ≫ resY p c` using `pullback.lift_fst _ _ _`. Establish `h2 : resYW p ι a ≫ prU p ι U = prU p ι U' ≫ resY p a` using `pullback.lift_fst _ _ _`. Rewrite using `[rpl_comp q i _ _ _ _ _ _ _ _ _ (by rw [Category.assoc, h2, ← Category.assoc (resYW p ι c), h1, Category.assoc])]`. Conclude with `congrFun (congrArg DFunLike.coe (rpl_congr q i _ _ _ _ _ _ _ _ (resYW_comp p ι c a) (resY_comp p c a) m)) z`.
-/
theorem rY_comp (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {U U' U'' : B.Etale} (c : U'' ⟶ U')
    (a : U' ⟶ U) (m : ℤ) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m) :
    rY q i p ι (c ≫ a) m z = rY q i p ι c m (rY q i p ι a m z) := by
  simp only [rY]
  have h1 : resYW p ι c ≫ prU p ι U' = prU p ι U'' ≫ resY p c := pullback.lift_fst _ _ _
  have h2 : resYW p ι a ≫ prU p ι U = prU p ι U' ≫ resY p a := pullback.lift_fst _ _ _
  rw [rpl_comp q i _ _ _ _ _ _ _ _ _ (by rw [Category.assoc, h2, ← Category.assoc (resYW p ι c), h1, Category.assoc])]
  exact congrFun (congrArg DFunLike.coe (rpl_congr q i _ _ _ _ _ _ _ _ (resYW_comp p ι c a) (resY_comp p c a) m)) z

/- English proof (translation)
Use `choose V a hu hz using h`. Use `⟨Sieve.ofArrows V a, (Scheme.ofArrows_mem_smallEtaleTopology_iff a).2 ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [Set.mem_iUnion, Set.mem_univ, iff_true]`. Conclude with `⟨x, hu x⟩`.

Introduce and unpack `U' b ⟨Z, c, d, ⟨u⟩, rfl⟩`. Rewrite using `[rY_comp, hz u, map_zero]`.
-/
theorem cov_of_nbhd (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ)
    (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m)
    (h : ∀ u : U.left, ∃ (U' : B.Etale) (a : U' ⟶ U), u ∈ Set.range a.left ∧ rY q i p ι a m z = 0) :
    Cov U (fun _ a => rY q i p ι a m z = 0) := by
  choose V a hu hz using h
  refine ⟨Sieve.ofArrows V a, (Scheme.ofArrows_mem_smallEtaleTopology_iff a).2 ?_, ?_⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨x, hu x⟩
  · rintro U' b ⟨Z, c, d, ⟨u⟩, rfl⟩
    rw [rY_comp, hz u, map_zero]

def LeafKillNbhd : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A → LateralTheory.E.SecondDegreeKilling.rT q i p ι U t m z = 0) →
  ∀ u : U.left, ∃ (U' : B.Etale) (a : U' ⟶ U), u ∈ Set.range a.left ∧ rY q i p ι a m z = 0

/- English proof (translation)
Introduce `hH q _ k _ hq i B W Y toK ι _ p hp U m z hz`. Conclude with `cov_of_nbhd q i p ι U m z (h hH q k hq i toK ι p hp U m z hz)`.
-/
theorem killPt_of (h : LeafKillNbhd) : LateralTheory.E.SecondDegreeKilling.LeafKillPt := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m z hz
  exact cov_of_nbhd q i p ι U m z (h hH q k hq i toK ι p hp U m z hz)

/- English proof (translation)
The claim follows from `LateralTheory.E.SecondDegreeKilling.LeafKill2_of (killPt_of hN) hW hV`.
-/
theorem LeafKill2_of (hN : LeafKillNbhd) (hW : LateralTheory.E.SecondDegreeKilling.LeafPtW) (hV : LateralTheory.E.SecondDegreeKilling.LeafPtV) :
    LeafKill2 :=
  LateralTheory.E.SecondDegreeKilling.LeafKill2_of (killPt_of hN) hW hV

end LateralTheory.E.SecondDegreeKilling.Nbhd
