import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescendsOfIsotropic
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.CyclicDescent

open ThetaSplit

section Bundles

variable {X Y : Scheme.{0}} {L : LB X}

/- English proof (translation)
Use `⟨⟨fun i => t.s i * res le_top b⟩, ?_, ?_⟩` and prove the remaining obligations. Unfold `LB.Gen.IsGen at ht ⊢`. Introduce `i j`. Simplify using `only [map_mul, LB.res_res]`. Rewrite using `[ht i j]`.

Conclude with `mul_assoc _ _ _`. Introduce `Z r z J hJ`. Use `(map_mul (gm r z _) _ _).trans ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `gm_res r z _ (hJ.mem φ r) b`.
-/
theorem exists_gen_scale {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (b : Γ(Y, ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J * gm r z ⊤ b := by
  refine ⟨⟨fun i => t.s i * res le_top b⟩, ?_, ?_⟩
  · unfold LB.Gen.IsGen at ht ⊢
    intro i j
    simp only [map_mul, LB.res_res]
    rw [ht i j]
    exact mul_assoc _ _ _
  · intro Z r z J hJ
    refine (map_mul (gm r z _) _ _).trans ?_
    congr 1
    exact gm_res r z _ (hJ.mem φ r) b

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Establish `hF : FormEq (PEmpty.elim : PEmpty → (X ⟶ X)) PEmpty.elim ![𝟙 X, τ 0] ![(1 : ℤ), -1]`. Introduce `U _ h`. Simplify using `[Fin.prod_univ_two, h0]`.

Take `⟨w, hw, hw'⟩` from `exists_gen hL hF (LB.oneGen L (Y := X)) (LB.isGen_oneGen L)`. Use `⟨w, hw, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[hw' Z r z J hJ, val_one]`. Simplify using the standard rewrite rules. Consider the case `succ j ih`.

Take `⟨w, hw, hw'⟩` from `ih`. Establish `hp` using `LB.isGen_pullGen L _ _ v hv (τ j)`. Establish `hm` using `LB.isGen_mulGen L ![𝟙 X, τ j] ![1, -1] (fun k => τ j ≫ ![𝟙 X, τ 1] k) ![1, -1] w (L.pullGen ![𝟙 X, τ 1] ![1, -1] v (τ j)) hw hp`. Establish `hF : FormEq (Sum.elim ![𝟙 X, τ j] (fun k => τ j ≫ ![𝟙 X, τ 1] k)) (Sum.elim ![(1 : ℤ), -1] ![1, -1]) ![𝟙 X, τ (j + 1)] ![(1 : ℤ), -1]`. Introduce `U _ h`.

Simplify using `only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, ← hτ]`. Use `group`. Take `⟨w', hw'', hv'⟩` from `exists_gen hL hF _ hm`. Use `⟨w', hw'', fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[hv' Z r z J hJ, val_mul hJ, val_pull hJ, hw' Z r z J hJ, Finset.prod_range_succ]`.
-/
theorem exists_gen_iterate (hL : L.IsLB) (τ : ℕ → (X ⟶ X)) (h0 : τ 0 = 𝟙 X) (hτ : ∀ i, τ (i + 1) = τ i ≫ τ 1)
    (v : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, τ 1] ![1, -1])) (hv : v.IsGen) (j : ℕ) :
    ∃ w : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, τ j] ![1, -1]), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
        val w r z J = ∏ i ∈ Finset.range j, val v (r ≫ τ i) z J := by
  induction j with
  | zero =>
    have hF : FormEq (PEmpty.elim : PEmpty → (X ⟶ X)) PEmpty.elim ![𝟙 X, τ 0] ![(1 : ℤ), -1] := by
      intro U _ h
      simp [Fin.prod_univ_two, h0]
    obtain ⟨w, hw, hw'⟩ := exists_gen hL hF (LB.oneGen L (Y := X)) (LB.isGen_oneGen L)
    refine ⟨w, hw, fun Z r z J hJ => ?_⟩
    rw [hw' Z r z J hJ, val_one]
    simp
  | succ j ih =>
    obtain ⟨w, hw, hw'⟩ := ih
    have hp := LB.isGen_pullGen L _ _ v hv (τ j)
    have hm := LB.isGen_mulGen L ![𝟙 X, τ j] ![1, -1] (fun k => τ j ≫ ![𝟙 X, τ 1] k) ![1, -1] w
      (L.pullGen ![𝟙 X, τ 1] ![1, -1] v (τ j)) hw hp
    have hF : FormEq (Sum.elim ![𝟙 X, τ j] (fun k => τ j ≫ ![𝟙 X, τ 1] k)) (Sum.elim ![(1 : ℤ), -1] ![1, -1])
        ![𝟙 X, τ (j + 1)] ![(1 : ℤ), -1] := by
      intro U _ h
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, Category.comp_id, ← hτ]
      group
    obtain ⟨w', hw'', hv'⟩ := exists_gen hL hF _ hm
    refine ⟨w', hw'', fun Z r z J hJ => ?_⟩
    rw [hv' Z r z J hJ, val_mul hJ, val_pull hJ, hw' Z r z J hJ, Finset.prod_range_succ]

end Bundles

section Group

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

/- English proof (translation)
Take `⟨p⟩` from `‹Nonempty S›`. Take `⟨V, hpV, c, hc⟩` from `hx p`. Establish `: Subsingleton ↥(𝟙_ (Over S)).left` using `‹Subsingleton ↥S›`. Establish `hW : ∀ y, y ∈ (fst (𝟙_ (Over S)) A).left ⁻¹ᵁ V` using `fun y => by show (fst (𝟙_ (Over S)) A).left y ∈ V`. Rewrite using `[Subsingleton.elim ((fst (𝟙_ (Over S)) A).left y) p]` and apply the resulting hypothesis.

Take `⟨t, ht⟩` from `GlobalTheory.TwistTranslate.gen_of_pull_top hL _ hW c hc`. Establish `h1` using `LB.isGen_invGen L _ _ (LB.pullGen L _ _ t (lift (toUnit A) (𝟙 A)).left) (LB.isGen_pullGen L _ _ t ht (lift (toUnit A) (𝟙 A)).left)`. Establish `ea : (lift (toUnit A) (𝟙 A)).left ≫ (lift (fst (𝟙_ (Over S)) A ≫ x) (snd _ A) ≫ μ).left = ThetaSplit.transl x`. Rewrite using `[← Over.comp_left]`. Use `congr 1`.

Rewrite using `[← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]`. Both sides reduce to the same expression. Establish `eb : (lift (toUnit A) (𝟙 A)).left ≫ (snd (𝟙_ (Over S)) A).left = 𝟙 A.left`. Rewrite using `[← Over.comp_left, lift_snd]`. Both sides reduce to the same expression.

Establish `hF : FormEq (fun k => (lift (toUnit A) (𝟙 A)).left ≫ ![(lift (fst (𝟙_ (Over S)) A ≫ x) (snd _ A) ≫ μ).left, (snd (𝟙_ (Over S)) A).left] k) (fun k => -![(1 : ℤ), -1] k) ![𝟙 A.left, ThetaSplit.transl x] ![(1 : ℤ), -1]`. Introduce `U _ h`. Simplify using `only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, ea, eb]`. Simplify using `[mul_comm]`. Take `⟨v, hv, -⟩` from `exists_gen hL hF _ h1`.

Conclude with `⟨v, hv⟩`.
-/
theorem exists_gen_of_memKL {L : LB A.left} (hL : L.IsLB) [Subsingleton S] [Nonempty S]
    {x : 𝟙_ (Over S) ⟶ A} (hx : MemKL A L x) :
    ∃ v : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl x] ![1, -1]), v.IsGen := by
  obtain ⟨p⟩ := ‹Nonempty S›
  obtain ⟨V, hpV, c, hc⟩ := hx p
  have : Subsingleton ↥(𝟙_ (Over S)).left := ‹Subsingleton ↥S›
  have hW : ∀ y, y ∈ (fst (𝟙_ (Over S)) A).left ⁻¹ᵁ V := fun y => by
    show (fst (𝟙_ (Over S)) A).left y ∈ V
    rwa [Subsingleton.elim ((fst (𝟙_ (Over S)) A).left y) p]
  obtain ⟨t, ht⟩ := GlobalTheory.TwistTranslate.gen_of_pull_top hL _ hW c hc
  have h1 := LB.isGen_invGen L _ _ (LB.pullGen L _ _ t (lift (toUnit A) (𝟙 A)).left)
    (LB.isGen_pullGen L _ _ t ht (lift (toUnit A) (𝟙 A)).left)
  have ea : (lift (toUnit A) (𝟙 A)).left ≫ (lift (fst (𝟙_ (Over S)) A ≫ x) (snd _ A) ≫ μ).left =
      ThetaSplit.transl x := by
    rw [← Over.comp_left]
    congr 1
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
    rfl
  have eb : (lift (toUnit A) (𝟙 A)).left ≫ (snd (𝟙_ (Over S)) A).left = 𝟙 A.left := by
    rw [← Over.comp_left, lift_snd]
    rfl
  have hF : FormEq (fun k => (lift (toUnit A) (𝟙 A)).left ≫
      ![(lift (fst (𝟙_ (Over S)) A ≫ x) (snd _ A) ≫ μ).left, (snd (𝟙_ (Over S)) A).left] k)
      (fun k => -![(1 : ℤ), -1] k) ![𝟙 A.left, ThetaSplit.transl x] ![(1 : ℤ), -1] := by
    intro U _ h
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, ea, eb]
    simp [mul_comm]
  obtain ⟨v, hv, -⟩ := exists_gen hL hF _ h1
  exact ⟨v, hv⟩

/- English proof (translation)
Establish `: IsCommMonObj A` using `hA.comm`. Establish `e1 : toUnit A ≫ (1 : 𝟙_ (Over S) ⟶ A) = 1` using `comp_one (toUnit A)`. Establish `h0 : ThetaSplit.transl (x ^ 0) = 𝟙 A.left`. Rewrite using `[pow_zero]`. Use `show ((toUnit A ≫ (1 : 𝟙_ (Over S) ⟶ A)) * 𝟙 A).left = 𝟙 A.left`.

Rewrite using `[e1, _root_.one_mul (𝟙 A : A ⟶ A)]`. Both sides reduce to the same expression. Establish `hτ : ∀ m : ℕ, ThetaSplit.transl (x ^ (m + 1)) = ThetaSplit.transl (x ^ m) ≫ ThetaSplit.transl (x ^ 1)`. Introduce `m`. Rewrite using `[pow_succ, pow_one, ThetaSplit.transl_mul]`.

Take `⟨v, hv⟩ : ∃ v : LB.Gen (LB.LinComb L (K` from `Fin 2) ![𝟙 A.left, ThetaSplit.transl (x ^ 1)] ![1, -1]), v.IsGen := by`. Rewrite using `[pow_one]`. Conclude with `exists_gen_of_memKL hL hx`. Use `choose j hj using hi`. Establish `hw : ∀ c, ∃ w : LB.Gen (LB.LinComb L (K` using `Fin 2) ![𝟙 A.left, ThetaSplit.transl (i c)] ![1, -1]), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J → val w r z J = ∏ m ∈ Finset.range (j c), val v (r ≫ ThetaSplit.transl (x ^ m)) z J := by`.

Introduce `c`. Rewrite using `[← hj c]`. Conclude with `exists_gen_iterate hL (fun m => ThetaSplit.transl (x ^ m)) h0 hτ v hv (j c)`. Use `choose w hwg hwv using hw`. Establish `key : ∀ {Z : Scheme.{0}} (r : Z ⟶ A.left) (a m : ℕ), (r ≫ ThetaSplit.transl (x ^ a)) ≫ ThetaSplit.transl (x ^ m) = r ≫ ThetaSplit.transl (x ^ (a + m))`.

Introduce `Z r a m`. Rewrite using `[pow_add, ThetaSplit.transl_mul, Category.assoc]`. Establish `hc : ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J → val (w c) r z J * val (w c') (r ≫ ThetaSplit.transl (i c)) z J = val (w c') r z J * val (w c) (r ≫ ThetaSplit.transl (i c')) z J`. Introduce `c c' Z r z J hJ`. Establish `hs : ∀ a b, ∏ m ∈ Finset.range (a + b), val v (r ≫ ThetaSplit.transl (x ^ m)) z J = (∏ m ∈ Finset.range a, val v (r ≫ ThetaSplit.transl (x ^ m)) z J) * ∏ m ∈ Finset.range b, val v ((r ≫ ThetaSplit.transl (x ^ a)) ≫ ThetaSplit.transl (x ^ m)) z J`.

Introduce `a b`. Rewrite using `[Finset.prod_range_add]`. Simplify using `only [key]`. Rewrite using `[hwv c Z r z J hJ, hwv c' Z r z J hJ, hwv c' Z _ z J hJ, hwv c Z _ z J hJ, ← hj c, ← hj c', ← hs, ← hs, add_comm]`. Take `⟨b, hb⟩` from `ThetaSplit.exists_rescale hL A.hom η[A].left (Over.w η[A]) (hG S A hA).2 hU (fun c => ThetaSplit.transl (i c)) (fun c c' => by simp only [map_mul, ThetaSplit.transl_mul]) (fun c => ThetaSplit.transl_hom (i c)) 1 w hwg hc`.

Establish `gmtop_lemma : ∀ {Z : Scheme.{0}} (r : Z ⟶ A.left) (z : Z) (c : Γ(S, ⊤)ˣ), gm r z ⊤ (Units.map A.hom.appTop.hom c) = gm (r ≫ A.hom) z ⊤ c`. Introduce `Z r z c`. Unfold `gm`. Rewrite using `[dif_pos (show r z ∈ (⊤ : A.left.Opens) from trivial), dif_pos (show (r ≫ A.hom) z ∈ (⊤ : S.Opens) from trivial)]`. Use `ext`.

Simplify using `only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, pullU]`. Both sides reduce to the same expression. Establish `hu : ∀ c, ∃ u : LB.Gen (LB.LinComb L (K` using `Fin 2) ![𝟙 A.left, ThetaSplit.transl (i c)] ![1, -1]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J → val u r z J = val (w c) r z J * gm (r ≫ A.hom) z ⊤ (b c) := by`. Introduce `c`. Take `⟨u, hu, hsc⟩` from `exists_gen_scale (w c) (hwg c) (Units.map A.hom.appTop.hom (b c))`.

Use `⟨u, hu, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[hsc Z r z J hJ, gmtop_lemma]`. Use `choose u hug huv using hu`. Use `⟨u, hug, fun c c' => corr_of_val hL (fun y J hJ => ?_)⟩` and prove the remaining obligations. Rewrite using `[val_mul hJ, val_pull hJ, huv _ _ _ _ _ hJ, huv _ _ _ _ _ hJ, huv _ _ _ _ _ hJ, Category.assoc, ThetaSplit.transl_hom]`.

Conclude with `hb c c' _ (𝟙 _) y J hJ`.
-/
theorem exists_cocycle (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB)
    [Subsingleton S] [Nonempty S] (hU : ∀ n : ℕ, 0 < n → ∀ y : Γ(S, ⊤)ˣ, ∃ x : Γ(S, ⊤)ˣ, x ^ n = y)
    {x : 𝟙_ (Over S) ⟶ A} (hx : MemKL A L x)
    {C : Type} [CommGroup C] (i : C →* (𝟙_ (Over S) ⟶ A)) (hi : ∀ c, ∃ j : ℕ, x ^ j = i c) :
    ∃ u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl (i c)] ![1, -1]),
      (∀ c, (u c).IsGen) ∧ ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
        (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (ThetaSplit.transl (i c)))) := by
  have : IsCommMonObj A := hA.comm
  have e1 : toUnit A ≫ (1 : 𝟙_ (Over S) ⟶ A) = 1 := comp_one (toUnit A)
  have h0 : ThetaSplit.transl (x ^ 0) = 𝟙 A.left := by
    rw [pow_zero]
    show ((toUnit A ≫ (1 : 𝟙_ (Over S) ⟶ A)) * 𝟙 A).left = 𝟙 A.left
    rw [e1, _root_.one_mul (𝟙 A : A ⟶ A)]
    rfl
  have hτ : ∀ m : ℕ, ThetaSplit.transl (x ^ (m + 1)) = ThetaSplit.transl (x ^ m) ≫ ThetaSplit.transl (x ^ 1) := by
    intro m
    rw [pow_succ, pow_one, ThetaSplit.transl_mul]
  obtain ⟨v, hv⟩ : ∃ v : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl (x ^ 1)] ![1, -1]),
      v.IsGen := by
    rw [pow_one]
    exact exists_gen_of_memKL hL hx
  choose j hj using hi
  have hw : ∀ c, ∃ w : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl (i c)] ![1, -1]),
      w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
        val w r z J = ∏ m ∈ Finset.range (j c), val v (r ≫ ThetaSplit.transl (x ^ m)) z J := by
    intro c
    rw [← hj c]
    exact exists_gen_iterate hL (fun m => ThetaSplit.transl (x ^ m)) h0 hτ v hv (j c)
  choose w hwg hwv using hw
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ A.left) (a m : ℕ),
      (r ≫ ThetaSplit.transl (x ^ a)) ≫ ThetaSplit.transl (x ^ m) = r ≫ ThetaSplit.transl (x ^ (a + m)) := by
    intro Z r a m
    rw [pow_add, ThetaSplit.transl_mul, Category.assoc]
  have hc : ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
      val (w c) r z J * val (w c') (r ≫ ThetaSplit.transl (i c)) z J =
        val (w c') r z J * val (w c) (r ≫ ThetaSplit.transl (i c')) z J := by
    intro c c' Z r z J hJ
    have hs : ∀ a b, ∏ m ∈ Finset.range (a + b), val v (r ≫ ThetaSplit.transl (x ^ m)) z J =
        (∏ m ∈ Finset.range a, val v (r ≫ ThetaSplit.transl (x ^ m)) z J) *
          ∏ m ∈ Finset.range b, val v ((r ≫ ThetaSplit.transl (x ^ a)) ≫ ThetaSplit.transl (x ^ m)) z J := by
      intro a b
      rw [Finset.prod_range_add]
      simp only [key]
    rw [hwv c Z r z J hJ, hwv c' Z r z J hJ, hwv c' Z _ z J hJ, hwv c Z _ z J hJ, ← hj c, ← hj c', ← hs, ← hs,
      add_comm]
  obtain ⟨b, hb⟩ := ThetaSplit.exists_rescale hL A.hom η[A].left (Over.w η[A]) (hG S A hA).2 hU
    (fun c => ThetaSplit.transl (i c)) (fun c c' => by simp only [map_mul, ThetaSplit.transl_mul])
    (fun c => ThetaSplit.transl_hom (i c)) 1 w hwg hc
  have gmtop_lemma : ∀ {Z : Scheme.{0}} (r : Z ⟶ A.left) (z : Z) (c : Γ(S, ⊤)ˣ),
      gm r z ⊤ (Units.map A.hom.appTop.hom c) = gm (r ≫ A.hom) z ⊤ c := by
    intro Z r z c
    unfold gm
    rw [dif_pos (show r z ∈ (⊤ : A.left.Opens) from trivial),
      dif_pos (show (r ≫ A.hom) z ∈ (⊤ : S.Opens) from trivial)]
    ext
    simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, pullU]
    rfl
  have hu : ∀ c, ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl (i c)] ![1, -1]),
      u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
        val u r z J = val (w c) r z J * gm (r ≫ A.hom) z ⊤ (b c) := by
    intro c
    obtain ⟨u, hu, hsc⟩ := exists_gen_scale (w c) (hwg c) (Units.map A.hom.appTop.hom (b c))
    refine ⟨u, hu, fun Z r z J hJ => ?_⟩
    rw [hsc Z r z J hJ, gmtop_lemma]
  choose u hug huv using hu
  refine ⟨u, hug, fun c c' => corr_of_val hL (fun y J hJ => ?_)⟩
  rw [val_mul hJ, val_pull hJ, huv _ _ _ _ _ hJ, huv _ _ _ _ _ hJ, huv _ _ _ _ _ hJ, Category.assoc,
    ThetaSplit.transl_hom]
  exact hb c c' _ (𝟙 _) y J hJ

end Group

/- English proof (translation)
Introduce `k _ _ A B _ _ hA L hL x n hn hord hx ψ hψ _ _ _ hker`. Establish `: IsCommMonObj A` using `hA.comm`. Establish `hfin : IsOfFinOrder x`. Rewrite using `[← orderOf_pos_iff, hord]`. Use linear arithmetic over natural numbers and integers.

Establish `: Finite (Subgroup.zpowers x)`. Conclude with `(finite_zpowers.mpr hfin).to_subtype`. Establish `hi : ∀ c : Subgroup.zpowers x, ∃ j : ℕ, x ^ j = (Subgroup.zpowers x).subtype c` using `fun c => (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr c.2)`. Take `⟨u, hu, hcoc⟩` from `exists_cocycle globalFns_holds hA hL (ThetaSplit.units_divisible k) hx (Subgroup.zpowers x).subtype hi`. Use `GlobalTheory.LinDescent.exists_descent_of_isReduced (Sp k) A B ψ (Subgroup.zpowers x) (Subgroup.zpowers x).subtype L hL hψ ‹_› ‹_› ‹_› ?_ u hu hcoc` and prove the remaining obligations.

Introduce `k' _ _ t`. Use `⟨fun y => ?_, fun c hc => ?_⟩` and prove the remaining obligations. Rewrite using `[hker k' t y]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, rfl⟩`.

Conclude with `⟨⟨c, hc⟩, rfl⟩`. Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨c, c.2, rfl⟩`. Establish `e : (toUnit (Over.mk t)).left = t` using `by simp`. Establish `: Epi (toUnit (Over.mk t)).left` using `e ▸ ThetaSplit.epi_of_fields t`.

Establish `: Epi (toUnit (Over.mk t))` using `Over.epi_of_epi_left _`. Establish `hc' : toUnit (Over.mk t) ≫ (c : 𝟙_ (Over (Sp k)) ⟶ A) = 1` using `hc`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `(cancel_epi (toUnit (Over.mk t))).mp` to reduce the goal to its premises. Rewrite using `[hc', Subgroup.coe_one, comp_one]`.
-/
theorem exists_descent : ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → ∀ (x : (𝟙_ (Over (Sp k)) ⟶ A)) (n : ℕ), 1 ≤ n → orderOf x = n → GlobalTheory.MemKL A L x → ∀ ψ : A ⟶ B, IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (t : Sp k' ⟶ Sp k) (y : Over.mk t ⟶ A), y ≫ ψ = 1 ↔ ∃ c ∈ Subgroup.zpowers x, y = toUnit _ ≫ c) → ∃ M : LB B.left, M.IsLB ∧ LBIso L (M.pull ψ.left) := by
  intro k _ _ A B _ _ hA L hL x n hn hord hx ψ hψ _ _ _ hker
  have : IsCommMonObj A := hA.comm
  have hfin : IsOfFinOrder x := by
    rw [← orderOf_pos_iff, hord]
    omega
  have : Finite (Subgroup.zpowers x) := by
    exact (finite_zpowers.mpr hfin).to_subtype
  have hi : ∀ c : Subgroup.zpowers x, ∃ j : ℕ, x ^ j = (Subgroup.zpowers x).subtype c := fun c =>
    (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr c.2)
  obtain ⟨u, hu, hcoc⟩ := exists_cocycle globalFns_holds hA hL (ThetaSplit.units_divisible k) hx
    (Subgroup.zpowers x).subtype hi
  refine GlobalTheory.LinDescent.exists_descent_of_isReduced (Sp k) A B ψ (Subgroup.zpowers x) (Subgroup.zpowers x).subtype
    L hL hψ ‹_› ‹_› ‹_› ?_ u hu hcoc
  intro k' _ _ t
  refine ⟨fun y => ?_, fun c hc => ?_⟩
  · rw [hker k' t y]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, c.2, rfl⟩
  · have e : (toUnit (Over.mk t)).left = t := by simp
    have : Epi (toUnit (Over.mk t)).left := e ▸ ThetaSplit.epi_of_fields t
    have : Epi (toUnit (Over.mk t)) := Over.epi_of_epi_left _
    have hc' : toUnit (Over.mk t) ≫ (c : 𝟙_ (Over (Sp k)) ⟶ A) = 1 := hc
    apply Subtype.ext
    apply (cancel_epi (toUnit (Over.mk t))).mp
    rw [hc', Subgroup.coe_one, comp_one]

end GlobalTheory.CyclicDescent
