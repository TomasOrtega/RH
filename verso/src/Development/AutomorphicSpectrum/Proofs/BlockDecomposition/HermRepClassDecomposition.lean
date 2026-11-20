import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepOfIsometric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianO1PullbackFubiniStudyMetric
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoheightEqOneOfDimClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLineBundleSectionsGenerateIdealSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DimOfIsArithVar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MPDict.ClsRep

open GlobalTheory.CompanionTheory.MPDict.IsomT GlobalTheory.CompanionTheory.MPDict.TensRep

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def HasFrame (L : LB (MP ℤ m n)) (a : Fin (m + 1) → ℤ) : Prop :=
  ∃ u : ∀ (i : L.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, L.U i ⊓ mchart c)ˣ,
    (∀ i j c,
      Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          L.U i ⊓ L.U j ⊓ mchart c ≤ L.U j ⊓ mchart c) (u j c) =
        Semi.res (inf_le_left : L.U i ⊓ L.U j ⊓ mchart c ≤ L.U i ⊓ L.U j) (L.g i j) *
          Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            L.U i ⊓ L.U j ⊓ mchart c ≤ L.U i ⊓ mchart c) (u i c)) ∧
    (∀ i c c',
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          L.U i ⊓ (mchart c ⊓ mchart c') ≤ L.U i ⊓ mchart c) (u i c) =
        Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          L.U i ⊓ (mchart c ⊓ mchart c') ≤ L.U i ⊓ mchart c') (u i c') *
        ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
          ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
            L.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ a k)

/- English proof (translation)
Take `⟨u, h₁, h₂, -⟩` from `h`. Conclude with `⟨u, h₁, h₂⟩`.
-/
theorem hasFrame_of_isHermRep {M : HermLB (mpStr ℤ m n)} {A : Geo.HermLine (Bk n)} (h : IsHermRep M A) :
    HasFrame M.B A.a := by
  obtain ⟨u, h₁, h₂, -⟩ := h
  exact ⟨u, h₁, h₂⟩

/- English proof (translation)
Use `top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨fun k => ptChart x k, ?_⟩` and prove the remaining obligations. Conclude with `Set.mem_iInter.2 fun k => mem_ptChart x k`.
-/
theorem iSup_mchart : ⨆ c : (∀ k, Bk n k), mchart c = (⊤ : (MP ℤ m n).Opens) := by
  refine top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨fun k => ptChart x k, ?_⟩
  exact Set.mem_iInter.2 fun k => mem_ptChart x k

/- English proof (translation)
Substitute `h h'` using the available equality. Rewrite using `[mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]`.
-/
theorem cg₃ {G : Type*} [CommGroup G] {x x' y y' P : G} (h : x = x' * P) (h' : y = y' * P) :
    x * y⁻¹ = x' * y'⁻¹ := by
  subst h h'
  rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]

/- English proof (translation)
Substitute `h h'` using the available equality. Simplify using `only [mul_inv]`. Rewrite using `[show g * g'⁻¹ * (g' * x * (g⁻¹ * y⁻¹)) = (g * g⁻¹) * (g'⁻¹ * g') * (x * y⁻¹) by ac_rfl]`. Simplify using the standard rewrite rules.
-/
theorem cg₄ {G : Type*} [CommGroup G] {x x' y y' g g' : G} (h : x' = g' * x) (h' : y' = g * y) :
    x * y⁻¹ = g * g'⁻¹ * (x' * y'⁻¹) := by
  subst h h'
  simp only [mul_inv]
  rw [show g * g'⁻¹ * (g' * x * (g⁻¹ * y⁻¹)) = (g * g⁻¹) * (g'⁻¹ * g') * (x * y⁻¹) by ac_rfl]
  simp

/- English proof (translation)
Take `⟨u, u₁, u₂⟩` from `hL`. Take `⟨v, v₁, v₂⟩` from `hN`. Establish `hglue (p : N.ι × L.ι) : ∃ t : Γ(MP ℤ m n, N.U p.1 ⊓ L.U p.2)ˣ, ∀ c, Semi.res inf_le_left t = Semi.res (ofMem fun _ hx => ⟨hx.1.2, hx.2⟩ : (N.U p.1 ⊓ L.U p.2) ⊓ mchart c ≤ L.U p.2 ⊓ mchart c) (u p.2 c) * (Semi.res (ofMem fun _ hx => ⟨hx.1.1, hx.2⟩ : (N.U p.1 ⊓ L.U p.2) ⊓ mchart c …`. Use `exists_glue mchart iSup_mchart _ _ fun c c' => ?_` and prove the remaining obligations. Establish `e₁` using `(congrArg (Semi.res (ofMem fun _ hx => ⟨hx.1.1.2, hx.1.2, hx.2.2⟩ : ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c) ⊓ ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c') ≤ L.U p.2 ⊓ (mchart c ⊓ mchart c'))) (u₂ p.2 c c')).trans (res_mul_prod c c' a _ _ _)`.

Establish `e₂` using `(congrArg (Semi.res (ofMem fun _ hx => ⟨hx.1.1.1, hx.1.2, hx.2.2⟩ : ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c) ⊓ ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c') ≤ N.U p.1 ⊓ (mchart c ⊓ mchart c'))) (v₂ p.1 c c')).trans (res_mul_prod c c' a _ _ _)`. Simplify using `only [map_mul, map_inv, res_twice] at e₁ e₂ ⊢`. Conclude with `cg₃ e₁ e₂`. Use `choose t ht using hglue`. Establish `htT (p : N.ι × L.ι) (c : ∀ k, Bk n k) {T : (MP ℤ m n).Opens} (hT : T ≤ (N.U p.1 ⊓ L.U p.2) ⊓ mchart c) : Semi.res (hT.trans inf_le_left) (t p) = Semi.res (ofMem fun _ hx => ⟨(hT hx).1.2, (hT hx).2⟩ : T ≤ L.U p.2 ⊓ mchart c) (u p.2 c) * (Semi.res (ofMem fun _ hx => ⟨(hT hx).1.1, ( …`.

Establish `e` using `congrArg (Semi.res hT) (ht p c)`. Simplify `e` using `only [map_mul, map_inv, res_twice]`. Use `⟨⟨t⟩, fun (p q : N.ι × L.ι) => units_ext_cover mchart iSup_mchart fun c => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2)) (Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U p.1 ⊓ L.U p.2) (t p)) = Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U …`. Simplify using `only [map_mul, map_inv, res_twice]`.

Rewrite using `[htT p c (T := (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c) (ofMem fun _ hx => ⟨hx.1.1, hx.2⟩), htT q c (T := (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c) (ofMem fun _ hx => ⟨hx.1.2, hx.2⟩)]`. Establish `hU : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ L.U p.2 ⊓ L.U q.2 ⊓ mchart c` using `ofMem fun _ hx => ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2⟩`. Establish `hV : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ N.U p.1 ⊓ N.U q.1 ⊓ mchart c` using `ofMem fun _ hx => ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2⟩`. Establish `e₁` using `congrArg (Semi.res hU) (u₁ p.2 q.2 c)`. Establish `e₂` using `congrArg (Semi.res hV) (v₁ p.1 q.1 c)`.

Simplify using `only [map_mul, res_twice] at e₁ e₂`. Conclude with `cg₄ e₁ e₂`.
-/
theorem lbIso_of_hasFrame {L N : LB (MP ℤ m n)} {a : Fin (m + 1) → ℤ} (hL : HasFrame L a) (hN : HasFrame N a) :
    LBIso L N := by
  obtain ⟨u, u₁, u₂⟩ := hL
  obtain ⟨v, v₁, v₂⟩ := hN
  have hglue (p : N.ι × L.ι) : ∃ t : Γ(MP ℤ m n, N.U p.1 ⊓ L.U p.2)ˣ, ∀ c,
      Semi.res inf_le_left t =
        Semi.res (ofMem fun _ hx => ⟨hx.1.2, hx.2⟩ : (N.U p.1 ⊓ L.U p.2) ⊓ mchart c ≤ L.U p.2 ⊓ mchart c) (u p.2 c) *
        (Semi.res (ofMem fun _ hx => ⟨hx.1.1, hx.2⟩ : (N.U p.1 ⊓ L.U p.2) ⊓ mchart c ≤ N.U p.1 ⊓ mchart c) (v p.1 c))⁻¹ := by
    refine exists_glue mchart iSup_mchart _ _ fun c c' => ?_
    have e₁ := (congrArg (Semi.res (ofMem fun _ hx => ⟨hx.1.1.2, hx.1.2, hx.2.2⟩ :
      ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c) ⊓ ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c') ≤ L.U p.2 ⊓ (mchart c ⊓ mchart c'))) (u₂ p.2 c c')).trans
      (res_mul_prod c c' a _ _ _)
    have e₂ := (congrArg (Semi.res (ofMem fun _ hx => ⟨hx.1.1.1, hx.1.2, hx.2.2⟩ :
      ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c) ⊓ ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c') ≤ N.U p.1 ⊓ (mchart c ⊓ mchart c'))) (v₂ p.1 c c')).trans
      (res_mul_prod c c' a _ _ _)
    simp only [map_mul, map_inv, res_twice] at e₁ e₂ ⊢
    exact cg₃ e₁ e₂
  choose t ht using hglue
  have htT (p : N.ι × L.ι) (c : ∀ k, Bk n k) {T : (MP ℤ m n).Opens} (hT : T ≤ (N.U p.1 ⊓ L.U p.2) ⊓ mchart c) :
      Semi.res (hT.trans inf_le_left) (t p) =
        Semi.res (ofMem fun _ hx => ⟨(hT hx).1.2, (hT hx).2⟩ : T ≤ L.U p.2 ⊓ mchart c) (u p.2 c) *
        (Semi.res (ofMem fun _ hx => ⟨(hT hx).1.1, (hT hx).2⟩ : T ≤ N.U p.1 ⊓ mchart c) (v p.1 c))⁻¹ := by
    have e := congrArg (Semi.res hT) (ht p c)
    simpa only [map_mul, map_inv, res_twice] using e
  refine ⟨⟨t⟩, fun (p q : N.ι × L.ι) => units_ext_cover mchart iSup_mchart fun c => ?_⟩
  change Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2))
      (Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U p.1 ⊓ L.U p.2) (t p)) =
    Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2))
      ((Semi.res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U p.1 ⊓ N.U q.1) (N.g p.1 q.1) *
        (Semi.res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹) *
        Semi.res (inf_le_right : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U q.1 ⊓ L.U q.2) (t q))
  simp only [map_mul, map_inv, res_twice]
  rw [htT p c (T := (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c) (ofMem fun _ hx => ⟨hx.1.1, hx.2⟩),
    htT q c (T := (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c) (ofMem fun _ hx => ⟨hx.1.2, hx.2⟩)]
  have hU : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ L.U p.2 ⊓ L.U q.2 ⊓ mchart c :=
    ofMem fun _ hx => ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2⟩
  have hV : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ N.U p.1 ⊓ N.U q.1 ⊓ mchart c :=
    ofMem fun _ hx => ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2⟩
  have e₁ := congrArg (Semi.res hU) (u₁ p.2 q.2 c)
  have e₂ := congrArg (Semi.res hV) (v₁ p.1 q.1 c)
  simp only [map_mul, res_twice] at e₁ e₂
  exact cg₄ e₁ e₂

/- English proof (translation)
Take `⟨u, hu₁, hu₂⟩` from `hL`. Take `⟨v, hv₁, hv₂⟩` from `hN`. Use `⟨fun p c => mulUnit (u p.1 c) (v p.2 c), ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨i, i'⟩ ⟨j, j'⟩ c`. Conclude with `frame_mulUnit _ _ _ _ _ _ _ _ _ _ _ _ (hu₁ i j c) (hv₁ i' j' c) _ _ _ _ _`.

Introduce and unpack `⟨i, i'⟩ c c'`. Conclude with `mono_mulUnit a b _ _ _ _ _ _ _ _ _ _ (hu₂ i c c') (hv₂ i' c c') _ _ _`.
-/
theorem hasFrame_tens {L N : LB (MP ℤ m n)} {a b : Fin (m + 1) → ℤ} (hL : HasFrame L a) (hN : HasFrame N b) :
    HasFrame (GlobalTheory.CechPic.tens L N) (a + b) := by
  obtain ⟨u, hu₁, hu₂⟩ := hL
  obtain ⟨v, hv₁, hv₂⟩ := hN
  refine ⟨fun p c => mulUnit (u p.1 c) (v p.2 c), ?_, ?_⟩
  · rintro ⟨i, i'⟩ ⟨j, j'⟩ c
    exact frame_mulUnit _ _ _ _ _ _ _ _ _ _ _ _ (hu₁ i j c) (hv₁ i' j' c) _ _ _ _ _
  · rintro ⟨i, i'⟩ c c'
    exact mono_mulUnit a b _ _ _ _ _ _ _ _ _ _ (hu₂ i c c') (hv₂ i' c c') _ _ _

/- English proof (translation)
Take `⟨u, h1, h2⟩` from `hL`. Use `⟨fun i c => (u i c)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j c`. Establish `e` using `h1 i j c`. Express the relevant statement in the definitionally equal form `Semi.res _ (u j c)⁻¹ = Semi.res _ (L.g i j)⁻¹ * Semi.res _ (u i c)⁻¹`.

Rewrite using `[map_inv, map_inv, map_inv]`. Conclude with `(congrArg (·⁻¹) e).trans (mul_inv _ _)`. Introduce `i c c'`. Establish `e` using `h2 i c c'`. Express the relevant statement in the definitionally equal form `Semi.res _ (u i c)⁻¹ = Semi.res _ (u i c')⁻¹ * ∏ k, blockUnit (c k) (c' k) _ ^ (-a k)`.

Simplify using `only [zpow_neg, Finset.prod_inv_distrib, map_inv]`. Conclude with `(congrArg (·⁻¹) e).trans (mul_inv _ _)`.
-/
theorem hasFrame_dual {L : LB (MP ℤ m n)} {a : Fin (m + 1) → ℤ} (hL : HasFrame L a) :
    HasFrame (GlobalTheory.CechPic.dual L) (-a) := by
  obtain ⟨u, h1, h2⟩ := hL
  refine ⟨fun i c => (u i c)⁻¹, ?_, ?_⟩
  · intro i j c
    have e := h1 i j c
    change Semi.res _ (u j c)⁻¹ = Semi.res _ (L.g i j)⁻¹ * Semi.res _ (u i c)⁻¹
    rw [map_inv, map_inv, map_inv]
    exact (congrArg (·⁻¹) e).trans (mul_inv _ _)
  · intro i c c'
    have e := h2 i c c'
    change Semi.res _ (u i c)⁻¹ = Semi.res _ (u i c')⁻¹ * ∏ k, blockUnit (c k) (c' k) _ ^ (-a k)
    simp only [zpow_neg, Finset.prod_inv_distrib, map_inv]
    exact (congrArg (·⁻¹) e).trans (mul_inv _ _)

/- English proof (translation)
Use `⟨fun _ _ => 1, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j c`. Simplify using `only [map_one, mul_one]`. Introduce `i c c'`. Simplify using the standard rewrite rules.
-/
theorem hasFrame_triv : HasFrame (LB.triv (MP ℤ m n)) 0 := by
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · intro i j c
    simp only [map_one, mul_one]
  · intro i c c'
    simp

/- English proof (translation)
Use `Units.ext ((val_res_pullO_g (prB n k) 1 i j h).trans ?_)` and prove the remaining obligations. Rewrite using `[pow_one]`. Conclude with `(GlobalTheory.CompanionTheory.MPDict.Inhab.val_blockUnit i j h).symm`.
-/
theorem res_pullO_g (k : Fin (m + 1)) (i j : Bk n k) {V : (MP ℤ m n).Opens}
    (h : V ≤ (pullO (prB n k) 1).U i ⊓ (pullO (prB n k) 1).U j) :
    Semi.res h ((pullO (prB n k) 1).g i j) = blockUnit i j h := by
  refine Units.ext ((val_res_pullO_g (prB n k) 1 i j h).trans ?_)
  rw [pow_one]
  exact (GlobalTheory.CompanionTheory.MPDict.Inhab.val_blockUnit i j h).symm

/- English proof (translation)
Use `⟨fun i c => blockUnit (c k) i (le_inf (inf_le_right.trans (mchart_le c k)) inf_le_left), ?_, ?_⟩` and prove the remaining obligations. Introduce `i j c`. Use `(GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (res_pullO_g k i j _) (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _)).symm)` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `(GlobalTheory.CompanionTheory.MPDict.Inhab.blockUnit_mul _ _ _ _ _ _).symm`.

Introduce `i c c'`. Use `(GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _) (GlobalTheory.CompanionTheory.MPDict.Inhab.prod_blockUnit_single k c c' _)).symm)` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `(GlobalTheory.CompanionTheory.MPDict.Inhab.blockUnit_mul _ _ _ _ _ _).symm`.
-/
theorem hasFrame_pullO (k : Fin (m + 1)) : HasFrame (pullO (prB n k) 1) (Pi.single k 1) := by
  refine ⟨fun i c => blockUnit (c k) i (le_inf (inf_le_right.trans (mchart_le c k)) inf_le_left), ?_, ?_⟩
  · intro i j c
    refine (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (res_pullO_g k i j _) (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _)).symm)
    rw [mul_comm]
    exact (GlobalTheory.CompanionTheory.MPDict.Inhab.blockUnit_mul _ _ _ _ _ _).symm
  · intro i c c'
    refine (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _)
        (GlobalTheory.CompanionTheory.MPDict.Inhab.prod_blockUnit_single k c c' _)).symm)
    rw [mul_comm]
    exact (GlobalTheory.CompanionTheory.MPDict.Inhab.blockUnit_mul _ _ _ _ _ _).symm

/- English proof (translation)
Set `H : AddSubgroup (Fin (m + 1) → ℤ)` to `{ carrier := {a | ∃ (L : LB (MP ℤ m n)) (hL : L.IsLB), HasFrame L a ∧ cls L hL = ∑ k, a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1)} add_mem' := by`. Introduce and unpack `a b ⟨L, hL, fL, eL⟩ ⟨N, hN, fN, eN⟩`. Use `⟨_, isLB_tens hL hN, hasFrame_tens fL fN, ?_⟩` and prove the remaining obligations. Rewrite using `[cls_tens hL hN, eL, eN, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => (add_smul _ _ _).symm`.

Use the proof step `zero_mem' := ⟨_, LB.isLB_triv _, hasFrame_triv, by simp; rfl⟩`. Use the proof step `neg_mem' := by`. Introduce and unpack `a ⟨L, hL, fL, eL⟩`. Use `⟨_, isLB_dual hL, hasFrame_dual fL, ?_⟩` and prove the remaining obligations. Rewrite using `[cls_dual hL, eL, ← Finset.sum_neg_distrib]`.

Conclude with `Finset.sum_congr rfl fun k _ => (neg_smul _ _).symm }`. Establish `hs (k : Fin (m + 1)) : (Pi.single k 1 : Fin (m + 1) → ℤ) ∈ H`. Use `⟨_, isLB_pullO _ 1, hasFrame_pullO k, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single k (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp), Pi.single_eq_same, one_smul]`. Establish `e : a = ∑ k, a k • (Pi.single k 1 : Fin (m + 1) → ℤ)`.

Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `: a ∈ H` using `e ▸ H.sum_mem fun k _ => H.zsmul_mem (hs k) _`. Conclude with `this`.
-/
theorem exists_hasFrame_cls (a : Fin (m + 1) → ℤ) : ∃ (L : LB (MP ℤ m n)) (hL : L.IsLB), HasFrame L a ∧
    cls L hL = ∑ k, a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1) := by
  classical
  let H : AddSubgroup (Fin (m + 1) → ℤ) :=
    { carrier := {a | ∃ (L : LB (MP ℤ m n)) (hL : L.IsLB), HasFrame L a ∧
        cls L hL = ∑ k, a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1)}
      add_mem' := by
        rintro a b ⟨L, hL, fL, eL⟩ ⟨N, hN, fN, eN⟩
        refine ⟨_, isLB_tens hL hN, hasFrame_tens fL fN, ?_⟩
        rw [cls_tens hL hN, eL, eN, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => (add_smul _ _ _).symm
      zero_mem' := ⟨_, LB.isLB_triv _, hasFrame_triv, by simp; rfl⟩
      neg_mem' := by
        rintro a ⟨L, hL, fL, eL⟩
        refine ⟨_, isLB_dual hL, hasFrame_dual fL, ?_⟩
        rw [cls_dual hL, eL, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => (neg_smul _ _).symm }
  have hs (k : Fin (m + 1)) : (Pi.single k 1 : Fin (m + 1) → ℤ) ∈ H := by
    refine ⟨_, isLB_pullO _ 1, hasFrame_pullO k, ?_⟩
    rw [Finset.sum_eq_single k (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
      Pi.single_eq_same, one_smul]
  have e : a = ∑ k, a k • (Pi.single k 1 : Fin (m + 1) → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have : a ∈ H := e ▸ H.sum_mem fun k _ => H.zsmul_mem (hs k) _
  exact this

end GlobalTheory.CompanionTheory.MPDict.ClsRep

/- English proof (translation)
Introduce `m n M A h`. Take `⟨L, hL, fL, eL⟩` from `GlobalTheory.CompanionTheory.MPDict.ClsRep.exists_hasFrame_cls (m := m) (n := n) A.a`. Conclude with `((cls_eq_iff M.isLB hL).2 (GlobalTheory.CompanionTheory.MPDict.ClsRep.lbIso_of_hasFrame (GlobalTheory.CompanionTheory.MPDict.ClsRep.hasFrame_of_isHermRep h) fL)).trans eL`.
-/
theorem GlobalTheory.CompanionTheory.MPDict.ClsRep.cls_eq_of_isHermRep : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)), IsHermRep M A → cls M.B M.isLB = ∑ k, A.a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1) := by
  intro m n M A h
  obtain ⟨L, hL, fL, eL⟩ := GlobalTheory.CompanionTheory.MPDict.ClsRep.exists_hasFrame_cls (m := m) (n := n) A.a
  exact ((cls_eq_iff M.isLB hL).2 (GlobalTheory.CompanionTheory.MPDict.ClsRep.lbIso_of_hasFrame
    (GlobalTheory.CompanionTheory.MPDict.ClsRep.hasFrame_of_isHermRep h) fL)).trans eL
