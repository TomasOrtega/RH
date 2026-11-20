import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ClosedIndep
open GlobalTheory.FieldBaseChange

variable {X Y Z : Scheme.{0}}

/- English proof (translation)
Distinguish the cases in `h : r (ψ y) ∈ W`. Rewrite using `[gs_eq r (ψ y) W h, gs_eq (ψ ≫ r) y W h]`. Use `Scheme.Hom.germ_stalkMap_apply ψ (r ⁻¹ᵁ W) y h ((r.app W).hom a)` as an intermediate fact. Rewrite using `[this]`. Simplify using `[Scheme.Hom.comp_app]`.

Both sides reduce to the same expression. Establish `h' : ¬ (ψ ≫ r) y ∈ W` using `h`. Simplify using `[gs, h, h']`.
-/
theorem gs_comp (ψ : Z ⟶ Y) (r : Y ⟶ X) (y : Z) (W : X.Opens) (a : Γ(X, W)) :
    gs (ψ ≫ r) y W a = (ψ.stalkMap y).hom (gs r (ψ y) W a) := by
  by_cases h : r (ψ y) ∈ W
  · rw [gs_eq r (ψ y) W h, gs_eq (ψ ≫ r) y W h]
    have := Scheme.Hom.germ_stalkMap_apply ψ (r ⁻¹ᵁ W) y h ((r.app W).hom a)
    rw [this]
    simp [Scheme.Hom.comp_app]
    rfl
  · have h' : ¬ (ψ ≫ r) y ∈ W := h
    simp [gs, h, h']

/- English proof (translation)
Rewrite using `[sval_of s (ψ ≫ r) y J (fun k => J (ψ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]`. Conclude with `gs_comp ψ r y _ _`.
-/
theorem sval_comp {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {Y' : Scheme.{0}}
    (s : LB.Sec (LB.LinComb L φ ε)) (ψ : Z ⟶ Y') (r : Y' ⟶ Y) (y : Z) (J : (Z ⟶ X) → L.ι) :
    sval s (ψ ≫ r) y J = (ψ.stalkMap y).hom (sval s r (ψ y) (fun χ => J (ψ ≫ χ))) := by
  rw [sval_of s (ψ ≫ r) y J (fun k => J (ψ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp ψ r y _ _

/- English proof (translation)
Introduce `χ` and use `hJ (ψ ≫ χ)`.
-/
theorem Good.comp {L : LB X} {Y' : Scheme.{0}} (ψ : Z ⟶ Y') {y : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L y J) :
    Good L (ψ y) (fun χ => J (ψ ≫ χ)) := fun χ => hJ (ψ ≫ χ)

/- English proof (translation)
Take `⟨a, ha⟩` from `residue_surjective ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).hom.hom e)`. Establish `key : scal (spMap (residue R)) a = e`. Establish `h1` using `congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (residue R)))`. Establish `h2 : (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).inv.hom (residue R a) = e`. Rewrite using `[ha]`.

Conclude with `congrArg (fun q => q.hom e) (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).hom_inv_id`. Conclude with `(h1.symm.trans h2)`. Use `⟨a, key, fun he ha' => he ?_⟩` and prove the remaining obligations. Establish `h0 : residue R a = 0` using `(residue_eq_zero_iff a).2 ha'`. Establish `: (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).hom.hom e = 0` using `by rw [← ha, h0]`.

Establish `h3` using `congrArg (fun q => q.hom e) (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).hom_inv_id`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, this, map_zero] at h3`. Conclude with `h3.symm`.
-/
theorem exists_lift (R : Type) [CommRing R] [IsLocalRing R] (e : Γ(Sp (ResidueField R), ⊤)) :
    ∃ a : R, scal (spMap (residue R)) a = e ∧ (e ≠ 0 → a ∉ maximalIdeal R) := by
  obtain ⟨a, ha⟩ := residue_surjective ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).hom.hom e)
  have key : scal (spMap (residue R)) a = e := by
    have h1 := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (residue R)))
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).inv.hom (residue R a) = e := by
      rw [ha]
      exact congrArg (fun q => q.hom e) (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).hom_inv_id
    exact (h1.symm.trans h2)
  refine ⟨a, key, fun he ha' => he ?_⟩
  have h0 : residue R a = 0 := (residue_eq_zero_iff a).2 ha'
  have : (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).hom.hom e = 0 := by rw [← ha, h0]
  have h3 := congrArg (fun q => q.hom e) (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).hom_inv_id
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, this, map_zero] at h3
  exact h3.symm

/- English proof (translation)
Establish `h` using `_root_.range_comap_of_surjective (R ⧸ maximalIdeal R ^ (0 + 1)) (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) Ideal.Quotient.mk_surjective`. Establish `hm : closedPoint R ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))))`. Rewrite using `[h, Ideal.mk_ker]`. Rewrite using `[PrimeSpectrum.mem_zeroLocus]`. Introduce `x hx`.

Conclude with `(by simpa using hx : x ∈ maximalIdeal R)`. Take `⟨y, hy⟩` from `hm`. Conclude with `⟨y, hy⟩`.
-/
theorem exists_thick_closed (R : Type) [CommRing R] [IsLocalRing R] :
    ∃ y : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))), thick R (maximalIdeal R) 0 y = closedPoint R := by
  have h := _root_.range_comap_of_surjective (R ⧸ maximalIdeal R ^ (0 + 1)) (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))
    Ideal.Quotient.mk_surjective
  have hm : closedPoint R ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))) := by
    rw [h, Ideal.mk_ker]
    rw [PrimeSpectrum.mem_zeroLocus]
    intro x hx
    exact (by simpa using hx : x ∈ maximalIdeal R)
  obtain ⟨y, hy⟩ := hm
  exact ⟨y, hy⟩

def toRes (R : Type) [CommRing R] [IsLocalRing R] : ResidueField R →+* R ⧸ maximalIdeal R ^ (0 + 1) :=
  Ideal.Quotient.lift (maximalIdeal R) (Ideal.Quotient.mk _) (fun a ha => by
    rw [Ideal.Quotient.eq_zero_iff_mem]; simpa using ha)

/- English proof (translation)
Rewrite using `[spMap, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem toRes_comp (R : Type) [CommRing R] [IsLocalRing R] :
    spMap (toRes R) ≫ spMap (residue R) = thick R (maximalIdeal R) 0 := by
  rw [spMap, spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
Establish `hJ'` using `Good.comp ψ hJ`. Establish `e1` using `h (ψ y) _ hJ'`. Establish `e2` using `h' (ψ y) _ hJ'`. Establish `key : ∀ i, sval (upSec G (σ i)) (toBase (residue R) ▷ G).left (ψ y) (fun χ => J (ψ ≫ χ)) = sval (σ i) (snd (Over.mk (spMap (residue R))) G).left (ψ y) (fun χ => J (ψ ≫ χ))` using `fun i => (sval_upSec G (σ i) _ (ψ y) hJ').trans (by rw [← Over.comp_left, whiskerRight_snd])`. Establish `hsub : ∀ i, gs (fst (Over.mk (spMap (residue R))) G).left (ψ y) ⊤ (c i - c' i) = gs (fst (Over.mk (spMap (residue R))) G).left (ψ y) ⊤ (c i) - gs (fst (Over.mk (spMap (residue R))) G).left (ψ y) ⊤ (c' i)` using `fun i => by`.

Rewrite using `[eq_sub_iff_add_eq, ← gs_add _ _ _ (by trivial), sub_add_cancel]`. Establish `e3 : ∑ i, gs (fst (Over.mk (spMap (residue R))) G).left (ψ y) ⊤ (c i - c' i) * sval (σ i) (snd (Over.mk (spMap (residue R))) G).left (ψ y) (fun χ => J (ψ ≫ χ)) = 0`. Simplify using `only [hsub, sub_mul, Finset.sum_sub_distrib, ← key]`. Conclude with `sub_eq_zero.2 (e1.symm.trans e2)`. Establish `e4` using `congrArg (ψ.stalkMap y).hom e3`.

Rewrite `e4` using `[map_sum, map_zero]`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) e4` and prove the remaining obligations. Rewrite using `[map_mul, ← gs_comp, ← sval_comp]`.
-/
theorem sum_eq_zero_of_lin {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) (L : LB G.left) (N n : ℕ)
    (σ : Fin n → H0 L N) (c c' : Fin n → Γ((Over.mk (spMap (residue R))).left, ⊤)) (s)
    (h : Lin G L N (toBase (residue R)) (fun i => upSec G (σ i)) c s)
    (h' : Lin G L N (toBase (residue R)) (fun i => upSec G (σ i)) c' s)
    {Z : Scheme.{0}} (ψ : Z ⟶ (Over.mk (spMap (residue R)) ⊗ G).left) (y : Z) (J : (Z ⟶ G.left) → L.ι) (hJ : Good L y J) :
    ∑ i, gs (ψ ≫ (fst (Over.mk (spMap (residue R))) G).left) y ⊤ (c i - c' i) *
      sval (σ i) (ψ ≫ (snd (Over.mk (spMap (residue R))) G).left) y J = 0 := by
  have hJ' := Good.comp ψ hJ
  have e1 := h (ψ y) _ hJ'
  have e2 := h' (ψ y) _ hJ'
  have key : ∀ i, sval (upSec G (σ i)) (toBase (residue R) ▷ G).left (ψ y) (fun χ => J (ψ ≫ χ)) =
      sval (σ i) (snd (Over.mk (spMap (residue R))) G).left (ψ y) (fun χ => J (ψ ≫ χ)) := fun i =>
    (sval_upSec G (σ i) _ (ψ y) hJ').trans (by rw [← Over.comp_left, whiskerRight_snd])
  have hsub : ∀ i, gs (fst (Over.mk (spMap (residue R))) G).left (ψ y) ⊤ (c i - c' i) =
      gs (fst (Over.mk (spMap (residue R))) G).left (ψ y) ⊤ (c i) -
        gs (fst (Over.mk (spMap (residue R))) G).left (ψ y) ⊤ (c' i) := fun i => by
    rw [eq_sub_iff_add_eq, ← gs_add _ _ _ (by trivial), sub_add_cancel]
  have e3 : ∑ i, gs (fst (Over.mk (spMap (residue R))) G).left (ψ y) ⊤ (c i - c' i) *
      sval (σ i) (snd (Over.mk (spMap (residue R))) G).left (ψ y) (fun χ => J (ψ ≫ χ)) = 0 := by
    simp only [hsub, sub_mul, Finset.sum_sub_distrib, ← key]
    exact sub_eq_zero.2 (e1.symm.trans e2)
  have e4 := congrArg (ψ.stalkMap y).hom e3
  rw [map_sum, map_zero] at e4
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) e4
  rw [map_mul, ← gs_comp, ← sval_comp]

end GlobalTheory.ClosedIndep

open GlobalTheory.ClosedIndep GlobalTheory.FieldBaseChange in
/- English proof (translation)
Introduce `R _ _ _ hR D A G _ _ hG U N hN n σ f hE hc c c' s h h'`. Assume the negation of the conclusion as `hne`. Use `choose a ha ha' using fun i => exists_lift R (c i - c' i)`. Choose the witnesses or unpack the hypotheses as in `⟨i₀, hi₀⟩ : ∃ i, c i - c' i ≠ 0 := by`. Assume the negation of the conclusion as `hh`.

Use `push_neg at hh`. Conclude with `hne (funext fun i => sub_eq_zero.1 (hh i))`. Take `⟨α, j, b, hb, hbo⟩` from `hc a ⟨i₀, ha' i₀ hi₀⟩`. Set `a₁ : (Over.map (thick R (maximalIdeal R) 0)).obj (thickObj R (maximalIdeal R) 0 G) ⟶ Over.mk (spMap (residue R))` to `Over.homMk (pullback.snd G.hom (thick R (maximalIdeal R) 0) ≫ spMap (toRes R)) (by`. Simplify using `[toRes_comp])`.

Set `ψ` to `lift a₁ (fstG (maximalIdeal R) 0 G)`. Establish `hs : ψ.left ≫ (snd (Over.mk (spMap (residue R))) G).left = (fstG (maximalIdeal R) 0 G).left`. Rewrite using `[← Over.comp_left, lift_snd]`. Establish `hf : ψ.left ≫ (fst (Over.mk (spMap (residue R))) G).left = pullback.snd G.hom (thick R (maximalIdeal R) 0) ≫ spMap (toRes R)`. Rewrite using `[← Over.comp_left, lift_fst]`.

Both sides reduce to the same expression. Establish `hp : (fstG (maximalIdeal R) 0 G).left ≫ G.hom = (pullback.snd G.hom (thick R (maximalIdeal R) 0) ≫ spMap (toRes R)) ≫ spMap (residue R)`. Rewrite using `[Category.assoc, toRes_comp]`. Conclude with `pullback.condition`. Set `τ : SecG U.toUnifPre N` to `∑ p, a p • (show SecG U.toUnifPre N from σ p)`.

Establish `hval : ∀ (y : (thickObj R (maximalIdeal R) 0 G).left) J, Good U.LG.L y J → sval (show H0 U.LG.L N from τ) (fstG (maximalIdeal R) 0 G).left y J = 0`. Introduce `y J hJ`. Establish `e` using `sum_eq_zero_of_lin G U.LG.L N n σ c c' s h h' ψ.left y J hJ`. Use `Eq.trans ?_ e` and prove the remaining obligations. Use `(sval_sum' hJ _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations.

Use `(sval_smul' hJ _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[hs, hf, ← ha i, GlobalTheory.FieldBaseChange.gs_scal, hp]`. Establish `hzero : ∀ j, ((fstG (maximalIdeal R) 0 G).left.app _).hom ((show H0 U.LG.L N from τ).f j) = 0`. Introduce `j`. Use `fn_ext fun y hy => ?_` and prove the remaining obligations.

Establish `hmem : ∀ k, ((fun _ : Fin 1 => (fstG (maximalIdeal R) 0 G).left ≫ 𝟙 G.left) k) y ∈ U.LG.L.U (j k)` using `fun k => Set.mem_iInter.1 hy k`. Take `⟨J, hJ, e⟩` from `exists_good U.LG.L U.LG.isLB y (fun _ : Fin 1 => (fstG (maximalIdeal R) 0 G).left ≫ 𝟙 G.left) j (fun a b _ => by rw [Subsingleton.elim a b]) hmem`. Establish `e2` using `hval y J hJ`. Rewrite `e2` using `[sval_of _ _ y J j (fun k => e k)]`. Use `(gs_pull (𝟙 _) _ y _ hy _).trans ?_` and prove the remaining obligations.

Rewrite using `[Category.id_comp]`. Conclude with `e2.trans (GlobalTheory.FieldBaseChange.gs_zero' _ y _ hy).symm`. Establish `WI` using `GlobalTheory.allSixLaws.2.2.2.1.weightIndep R (maximalIdeal R) D A G U.toUnifPre 0 N τ (fun α => (∑ p, a p • f p α : SecAb D.toPre N α)) hzero (expandsAt_comb U.toUnifPre 0 N σ f hE a) α j`. Take `⟨y₀, hy₀⟩` from `exists_thick_closed R`. Take `⟨w, hw, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := D.toPre.P.A.hom) (g := thick R (maximalIdeal R) 0) b y₀ (hb.trans hy₀.symm)`.

Take `⟨g, hg⟩` from `(U.gt 0).q_surj.surj w`. Establish `hgb : (U.gt 0).pG.left g = b`. Rewrite using `[← hw, ← hg]`. Both sides reduce to the same expression. Establish `hmem : g ∈ (U.gt 0).pG.left ⁻¹ᵁ D.toPre.P.A.left.basicOpen ((∑ i, a i • f i α).f j)` using `by show (U.gt 0).pG.left g ∈ D.toPre.P.A.left.basicOpen ((∑ i, a i • f i α).f j)`.

Rewrite using `[hgb]`. Conclude with `hbo`. Rewrite `hmem` using `[Scheme.preimage_basicOpen, WI, Scheme.basicOpen_zero]`. Conclude with `hmem`.
-/
theorem GlobalTheory.ClosedIndep.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (N : ℕ), 1 ≤ N →
    ∀ (n : ℕ) (σ : Fin n → H0 U.LG.L N) (f : Fin n → ∀ α, SecAb D.toPre N α),
      (∀ i, U.ExpandsAt 0 N (σ i) (f i)) →
      (∀ c : Fin n → R, (∃ i, c i ∉ maximalIdeal R) →
        ∃ (α : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι) (b : D.toPre.P.A.left),
          D.toPre.P.A.hom b = closedPoint R ∧
          b ∈ D.toPre.P.A.left.basicOpen ((∑ i, c i • f i α).f j)) →
      IndepAlong G U.LG.L N (toBase (residue R)) (fun i => upSec G (σ i)) := by
  intro R _ _ _ hR D A G _ _ hG U N hN n σ f hE hc c c' s h h'
  by_contra hne
  choose a ha ha' using fun i => exists_lift R (c i - c' i)
  obtain ⟨i₀, hi₀⟩ : ∃ i, c i - c' i ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hne (funext fun i => sub_eq_zero.1 (hh i))
  obtain ⟨α, j, b, hb, hbo⟩ := hc a ⟨i₀, ha' i₀ hi₀⟩
  let a₁ : (Over.map (thick R (maximalIdeal R) 0)).obj (thickObj R (maximalIdeal R) 0 G) ⟶ Over.mk (spMap (residue R)) :=
    Over.homMk (pullback.snd G.hom (thick R (maximalIdeal R) 0) ≫ spMap (toRes R)) (by
      simp [toRes_comp])
  let ψ := lift a₁ (fstG (maximalIdeal R) 0 G)
  have hs : ψ.left ≫ (snd (Over.mk (spMap (residue R))) G).left = (fstG (maximalIdeal R) 0 G).left := by
    rw [← Over.comp_left, lift_snd]
  have hf : ψ.left ≫ (fst (Over.mk (spMap (residue R))) G).left =
      pullback.snd G.hom (thick R (maximalIdeal R) 0) ≫ spMap (toRes R) := by
    rw [← Over.comp_left, lift_fst]
    rfl
  have hp : (fstG (maximalIdeal R) 0 G).left ≫ G.hom =
      (pullback.snd G.hom (thick R (maximalIdeal R) 0) ≫ spMap (toRes R)) ≫ spMap (residue R) := by
    rw [Category.assoc, toRes_comp]
    exact pullback.condition
  let τ : SecG U.toUnifPre N := ∑ p, a p • (show SecG U.toUnifPre N from σ p)
  have hval : ∀ (y : (thickObj R (maximalIdeal R) 0 G).left) J, Good U.LG.L y J →
      sval (show H0 U.LG.L N from τ) (fstG (maximalIdeal R) 0 G).left y J = 0 := by
    intro y J hJ
    have e := sum_eq_zero_of_lin G U.LG.L N n σ c c' s h h' ψ.left y J hJ
    refine Eq.trans ?_ e
    refine (sval_sum' hJ _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    refine (sval_smul' hJ _ _ _).trans ?_
    rw [hs, hf, ← ha i, GlobalTheory.FieldBaseChange.gs_scal, hp]
  have hzero : ∀ j, ((fstG (maximalIdeal R) 0 G).left.app _).hom ((show H0 U.LG.L N from τ).f j) = 0 := by
    intro j
    refine fn_ext fun y hy => ?_
    have hmem : ∀ k, ((fun _ : Fin 1 => (fstG (maximalIdeal R) 0 G).left ≫ 𝟙 G.left) k) y ∈ U.LG.L.U (j k) := fun k =>
      Set.mem_iInter.1 hy k
    obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB y (fun _ : Fin 1 => (fstG (maximalIdeal R) 0 G).left ≫ 𝟙 G.left) j
      (fun a b _ => by rw [Subsingleton.elim a b]) hmem
    have e2 := hval y J hJ
    rw [sval_of _ _ y J j (fun k => e k)] at e2
    refine (gs_pull (𝟙 _) _ y _ hy _).trans ?_
    rw [Category.id_comp]
    exact e2.trans (GlobalTheory.FieldBaseChange.gs_zero' _ y _ hy).symm
  have WI := GlobalTheory.allSixLaws.2.2.2.1.weightIndep R (maximalIdeal R) D A G U.toUnifPre 0 N τ
    (fun α => (∑ p, a p • f p α : SecAb D.toPre N α)) hzero (expandsAt_comb U.toUnifPre 0 N σ f hE a) α j
  obtain ⟨y₀, hy₀⟩ := exists_thick_closed R
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := D.toPre.P.A.hom)
    (g := thick R (maximalIdeal R) 0) b y₀ (hb.trans hy₀.symm)
  obtain ⟨g, hg⟩ := (U.gt 0).q_surj.surj w
  have hgb : (U.gt 0).pG.left g = b := by
    rw [← hw, ← hg]
    rfl
  have hmem : g ∈ (U.gt 0).pG.left ⁻¹ᵁ D.toPre.P.A.left.basicOpen ((∑ i, a i • f i α).f j) := by
    show (U.gt 0).pG.left g ∈ D.toPre.P.A.left.basicOpen ((∑ i, a i • f i α).f j)
    rw [hgb]
    exact hbo
  rw [Scheme.preimage_basicOpen, WI, Scheme.basicOpen_zero] at hmem
  exact hmem
