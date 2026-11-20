import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfMulComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinProdIsGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordLambdaBilinearIntegralCombinationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFourMapsEqOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumSide

open GlobalTheory.TensAct

section Main

/- English proof (translation)
Introduce `R _ _ I D D' r W T A f hf hW`. Set `M : Fin 4 → Matrix (Fin r) (Fin r) ℤ` to `![1 + A, 1, A, 0]`. Set `e : Fin 4 → ℤ` to `![1, -2, -1, 2]`. Set `E : Fin 4 × (Fin r × Fin r) → ℤ` to `fun q => e q.1 * W q.2.1 q.2.2`. Establish `hB` using `fun q : Fin 4 × (Fin r × Fin r) => GlobalTheory.T.mumfordLambda_bilinear_integral_combinations R I D D'.P.A T.pr (M q.1 q.2.1) (M q.1 q.2.2)`.

Use `choose t ht hv using hB`. Establish `hP` using `fun q : Fin 4 × (Fin r × Fin r) => exists_zpow D.toPre.P.isLB (t q) (ht q) (E q)`. Use `choose s hs hsv using hP`. Establish `hpr : ∀ (a : Fin 4) (i : Fin r), GlobalTheory.TensAct.matAct T (M a) ≫ T.pr i = ∏ k, T.pr k ^ M a i k` using `fun a i => GlobalTheory.TensAct.matAct_pr T (M a) i`. Take `⟨t', ht', hv'⟩` from `exists_gen D.toPre.P.isLB (φ' := fun p : Fin 4 × ((Fin r × Fin r) × Fin 4) => (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) (ε' := fun p => (![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * t …`.

Introduce `U _ h`. Set `Lh : (D'.P.A ⟶ D.toPre.P.A) → (D'.P.A ⟶ D.toPre.P.A) → U` to `fun x x' => ∏ l : Fin 4, h (GlobalTheory.PolDeg.lamPts x x' l) ^ Oε l`. Set `P : Fin 4 → Fin r → (D'.P.A ⟶ D.toPre.P.A)` to `fun a i => ∏ k, T.pr k ^ M a i k`. Establish `lamS : ∀ k l, Lh (T.pr k) (T.pr l) = Lh (T.pr l) (T.pr k)`. Introduce `k l`.

Simplify using `only [Lh, Fin.prod_univ_four]`. Use `show h (T.pr k * T.pr l).left ^ (1 : ℤ) * h (T.pr k).left ^ (-1 : ℤ) * h (T.pr l).left ^ (-1 : ℤ) * h (1 : D'.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ) = h (T.pr l * T.pr k).left ^ (1 : ℤ) * h (T.pr l).left ^ (-1 : ℤ) * h (T.pr k).left ^ (-1 : ℤ) * h (1 : D'.P.A ⟶ D.toPre.P.A).left ^ (1 …`. Rewrite using `[mul_comm (T.pr k) (T.pr l)]`. The two sides agree by associativity and commutativity. Establish `H1` using `GlobalTheory.T.prod_four_maps_lam_pow_eq_one U W A (fun k l => Lh (T.pr k) (T.pr l)) lamS hW`.

Establish `H2 : ∏ q : Fin 4 × (Fin r × Fin r), (∏ k, ∏ l, Lh (T.pr k) (T.pr l) ^ (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q = 1`. Rewrite using `[Fintype.prod_prod_type]`. Conclude with `Eq.trans (Finset.prod_congr rfl fun a _ => Fintype.prod_prod_type _) H1`. Establish `hR : ∏ p : Fin 4 × ((Fin r × Fin r) × Fin 4), h ((![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) ^ ((![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2) = ∏ q : Fin 4 × (Fin r × Fin r …`. Rewrite using `[Fintype.prod_prod_type, Fintype.prod_prod_type]`.

Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun ij _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_zpow]`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[four_eq T A f hf a, comp_tensφ', hpr, hpr, ← zpow_mul]`. Use `congr 1`. Simplify using `only [tensε, E, e]`. Expand and normalize the polynomial expressions, which then agree. Establish `hL : ∀ q : Fin 4 × (Fin r × Fin r), ∏ κ : Fin 4 ⊕ ((Fin r × Fin r) × Fin 4), h (Sum.elim (GlobalTheory.PolDeg.lamPts (P q.1 q.2.1) (P q.1 q.2.2)) (fun m : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (T.pr m.1.1) (T.pr m.1.2) m.2) κ) ^ (E q * Sum.elim Oε (fun m : (Fin r …`.

Introduce `q`. Rewrite using `[Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Use `congr 1`. Rewrite using `[← Finset.prod_zpow]`.

Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_mul, mul_comm]`. Rewrite using `[← zpow_neg, ← Finset.prod_zpow, Fintype.prod_prod_type, Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_zpow]`.

Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_mul, ← Finset.prod_zpow]`. Use `Finset.prod_congr rfl fun l' _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hR, Fintype.prod_prod_type]`. Use `(Finset.prod_congr rfl fun q _ => hL q).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_inv_distrib, H2, inv_one, _root_.mul_one]) (GeneratorPullback.finProdGen D.toPre.P.L _ _ s)`. Use the proof step `(finProd_isGen _ _ s hs)`.

Use `⟨t', ht', fun y z J hJ => ?_⟩` and prove the remaining obligations. Set `ρ : TK R ⟶ D'.P.A` to `toUnit (TK R) ≫ D'.c y`. Establish `hρ : ∀ k, ρ ≫ T.pr k = toUnit (TK R) ≫ D.toPre.c (T.xe y k)` using `fun k => by`. Rewrite using `[Category.assoc, T.c_pr]`. Establish `lamS : ∀ k l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J = val (D.toPre.tau (T.xe y l) (T.xe y k)) (𝟙 _) z J` using `fun k l => DVR.tauK_symm hJ _ _`.

Establish `H1` using `GlobalTheory.T.prod_four_maps_lam_pow_eq_one _ W A _ lamS hW`. Establish `H2 : ∏ q : Fin 4 × (Fin r × Fin r), (∏ k, ∏ l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J ^ (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q = 1`. Rewrite using `[Fintype.prod_prod_type]`. Use `Eq.trans (Finset.prod_congr rfl fun a _ => Fintype.prod_prod_type _) H1` and prove the remaining obligations. Establish `hq : ∀ q : Fin 4 × (Fin r × Fin r), val (s q) (D'.xK y) z J = ((val (D.toPre.tau (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) q.1) q.2.1) (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T …` using `fun q => by`.

Rewrite using `[hsv q _ _ z J hJ, show D'.xK y = ρ.left from rfl, hv q ρ (fun k => T.xe y k) hρ z J hJ, xe_four, xe_four]`. Rewrite using `[hv' _ _ z J hJ, val_finProd _ _ _ _ _ hJ, Finset.prod_congr rfl fun q _ => hq q]`. Simplify using `only [mul_zpow, Finset.prod_mul_distrib]`. Rewrite using `[H2, _root_.mul_one, Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Fintype.prod_prod_type, ← Finset.prod_zpow]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_zpow]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[inv_zpow', ← zpow_mul]`.

Use `congr 1`. Simplify using `only [E, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mside : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D' W) (A : Matrix (Fin r) (Fin r) ℤ) (f : D'.P.A ⟶ D'.P.A), f = GlobalTheory.TensAct.matAct T A → W = (W + W.transpose) * A → ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun p : Fin 4 × ((Fin r × Fin r) × Fin 4) => (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) (fun p => (![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2)), t.IsGen ∧ ∀ (y : D'.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val t (D'.xK y) z J = ∏ a : Fin 4, (∏ i, ∏ j, val (D.toPre.tau (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) i) (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) j)) (𝟙 _) z J ^ W i j) ^ (-(![1, -2, -1, 2] : Fin 4 → ℤ) a) := by
  intro R _ _ I D D' r W T A f hf hW
  classical
  let M : Fin 4 → Matrix (Fin r) (Fin r) ℤ := ![1 + A, 1, A, 0]
  let e : Fin 4 → ℤ := ![1, -2, -1, 2]
  let E : Fin 4 × (Fin r × Fin r) → ℤ := fun q => e q.1 * W q.2.1 q.2.2
  have hB := fun q : Fin 4 × (Fin r × Fin r) => GlobalTheory.T.mumfordLambda_bilinear_integral_combinations R I D D'.P.A T.pr (M q.1 q.2.1) (M q.1 q.2.2)
  choose t ht hv using hB
  have hP := fun q : Fin 4 × (Fin r × Fin r) => exists_zpow D.toPre.P.isLB (t q) (ht q) (E q)
  choose s hs hsv using hP
  have hpr : ∀ (a : Fin 4) (i : Fin r), GlobalTheory.TensAct.matAct T (M a) ≫ T.pr i = ∏ k, T.pr k ^ M a i k :=
    fun a i => GlobalTheory.TensAct.matAct_pr T (M a) i
  obtain ⟨t', ht', hv'⟩ := exists_gen D.toPre.P.isLB
    (φ' := fun p : Fin 4 × ((Fin r × Fin r) × Fin 4) => (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left,
      (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2)
    (ε' := fun p => (![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2) (by
      intro U _ h
      let Lh : (D'.P.A ⟶ D.toPre.P.A) → (D'.P.A ⟶ D.toPre.P.A) → U :=
        fun x x' => ∏ l : Fin 4, h (GlobalTheory.PolDeg.lamPts x x' l) ^ Oε l
      let P : Fin 4 → Fin r → (D'.P.A ⟶ D.toPre.P.A) := fun a i => ∏ k, T.pr k ^ M a i k
      have lamS : ∀ k l, Lh (T.pr k) (T.pr l) = Lh (T.pr l) (T.pr k) := by
        intro k l
        simp only [Lh, Fin.prod_univ_four]
        show h (T.pr k * T.pr l).left ^ (1 : ℤ) * h (T.pr k).left ^ (-1 : ℤ) * h (T.pr l).left ^ (-1 : ℤ) *
            h (1 : D'.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ) =
          h (T.pr l * T.pr k).left ^ (1 : ℤ) * h (T.pr l).left ^ (-1 : ℤ) * h (T.pr k).left ^ (-1 : ℤ) *
            h (1 : D'.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ)
        rw [mul_comm (T.pr k) (T.pr l)]
        ac_rfl
      have H1 := GlobalTheory.T.prod_four_maps_lam_pow_eq_one U W A (fun k l => Lh (T.pr k) (T.pr l)) lamS hW
      have H2 : ∏ q : Fin 4 × (Fin r × Fin r), (∏ k, ∏ l, Lh (T.pr k) (T.pr l) ^
          (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q = 1 := by
        rw [Fintype.prod_prod_type]
        exact Eq.trans (Finset.prod_congr rfl fun a _ => Fintype.prod_prod_type _) H1
      have hR : ∏ p : Fin 4 × ((Fin r × Fin r) × Fin 4), h ((![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left,
          (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) ^
          ((![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2) =
          ∏ q : Fin 4 × (Fin r × Fin r), Lh (P q.1 q.2.1) (P q.1 q.2.2) ^ E q := by
        rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun ij _ => ?_
        rw [← Finset.prod_zpow]
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [four_eq T A f hf a, comp_tensφ', hpr, hpr, ← zpow_mul]
        congr 1
        simp only [tensε, E, e]
        ring
      have hL : ∀ q : Fin 4 × (Fin r × Fin r), ∏ κ : Fin 4 ⊕ ((Fin r × Fin r) × Fin 4),
          h (Sum.elim (GlobalTheory.PolDeg.lamPts (P q.1 q.2.1) (P q.1 q.2.2))
            (fun m : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (T.pr m.1.1) (T.pr m.1.2) m.2) κ) ^
          (E q * Sum.elim Oε (fun m : (Fin r × Fin r) × Fin 4 => -(M q.1 q.2.1 m.1.1 * M q.1 q.2.2 m.1.2 * Oε m.2)) κ) =
          Lh (P q.1 q.2.1) (P q.1 q.2.2) ^ E q * ((∏ k, ∏ l, Lh (T.pr k) (T.pr l) ^
            (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q)⁻¹ := by
        intro q
        rw [Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        congr 1
        · rw [← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l _ => ?_
          rw [← zpow_mul, mul_comm]
        · rw [← zpow_neg, ← Finset.prod_zpow, Fintype.prod_prod_type, Fintype.prod_prod_type]
          refine Finset.prod_congr rfl fun k _ => ?_
          rw [← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l _ => ?_
          rw [← zpow_mul, ← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l' _ => ?_
          rw [← zpow_mul]
          congr 1
          ring
      rw [hR, Fintype.prod_prod_type]
      refine (Finset.prod_congr rfl fun q _ => hL q).trans ?_
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, H2, inv_one, _root_.mul_one]) (GeneratorPullback.finProdGen D.toPre.P.L _ _ s)
    (finProd_isGen _ _ s hs)
  refine ⟨t', ht', fun y z J hJ => ?_⟩
  let ρ : TK R ⟶ D'.P.A := toUnit (TK R) ≫ D'.c y
  have hρ : ∀ k, ρ ≫ T.pr k = toUnit (TK R) ≫ D.toPre.c (T.xe y k) := fun k => by
    rw [Category.assoc, T.c_pr]
  have lamS : ∀ k l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J =
      val (D.toPre.tau (T.xe y l) (T.xe y k)) (𝟙 _) z J := fun k l => DVR.tauK_symm hJ _ _
  have H1 := GlobalTheory.T.prod_four_maps_lam_pow_eq_one _ W A _ lamS hW
  have H2 : ∏ q : Fin 4 × (Fin r × Fin r), (∏ k, ∏ l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J ^
      (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q = 1 := by
    rw [Fintype.prod_prod_type]
    refine Eq.trans (Finset.prod_congr rfl fun a _ => Fintype.prod_prod_type _) H1
  have hq : ∀ q : Fin 4 × (Fin r × Fin r), val (s q) (D'.xK y) z J =
      ((val (D.toPre.tau (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) q.1) q.2.1) (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) q.1) q.2.2)) (𝟙 _) z J)⁻¹ *
        ∏ k, ∏ l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J ^ (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q := fun q => by
    rw [hsv q _ _ z J hJ, show D'.xK y = ρ.left from rfl, hv q ρ (fun k => T.xe y k) hρ z J hJ, xe_four, xe_four]
  rw [hv' _ _ z J hJ, val_finProd _ _ _ _ _ hJ, Finset.prod_congr rfl fun q _ => hq q]
  simp only [mul_zpow, Finset.prod_mul_distrib]
  rw [H2, _root_.mul_one, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [inv_zpow', ← zpow_mul]
  congr 1
  simp only [E, e]
  ring

end Main

end GlobalTheory.MumSide
