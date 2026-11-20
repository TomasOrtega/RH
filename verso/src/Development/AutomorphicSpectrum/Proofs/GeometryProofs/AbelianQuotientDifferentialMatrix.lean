import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEig

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open Formalism.MainNotions.ModuliIntegralCharts.H1.LinEig
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Lin

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {d : ℕ} (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

def tanPt (c : Fin d → S) : overAt x0 (DualNumber S) ⟶ t.G :=
  homAt x0 (tanV (fun p : Fin 1 × Fin d => c p.2) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1

variable {t x0 x}

/- English proof (translation)
Unfold `tanPt`. Establish `e : (fun p : Fin 1 × Fin d => (0 : Fin d → S) p.2) = 0` using `rfl`. Rewrite using `[e, tanV_zero, ← homAt_comp, Category.assoc]`. Use `erw [h0]`. Conclude with `MonObj.comp_one _`.
-/
theorem tanPt_zero (h0 : homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 1 →ₐ[S] S) ≫ x 1 = 1) :
    tanPt t x0 x 0 = 1 := by
  unfold tanPt
  have e : (fun p : Fin 1 × Fin d => (0 : Fin d → S) p.2) = 0 := rfl
  rw [e, tanV_zero, ← homAt_comp, Category.assoc]
  erw [h0]
  exact MonObj.comp_one _

/- English proof (translation)
Set `ψv : Fin 2 × Fin d → S` to `fun p => if p.1 = 0 then v p.2 else w p.2`. Establish `hc : ∀ (i : Fin 2), (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S).comp (jetCopy d 1 i : Jet S (Fin 1 × Fin d) 1 →ₐ[S] Jet S (Fin 2 × Fin d) 1) = tanV (fun p : Fin 1 × Fin d => ψv (i, p.2))`. Introduce `i`. Unfold `jetCopy`. Rewrite using `[tanV_comp_jetMap]`.

Use `congr 1`. Use function extensionality and compare the values at `p`. Simplify using `only [MvPolynomial.coeff_X]`. Rewrite using `[Finset.sum_eq_single (i, p.2)]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Rewrite using `[if_neg (fun h => hb (Finsupp.single_left_injective one_ne_zero h).symm), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hL : (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S).comp (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (F.F p.2)) = tanV (fun p : Fin 1 × Fin d => (v + w) p.2)`.

Unfold `jetSubstP`. Rewrite using `[tanV_comp_jetMap]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Establish `hco : ∀ s : Fin 2 × Fin d, MvPolynomial.coeff (Finsupp.single s 1) (psTrunc 1 (F.F p.2) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc 1 (F.F p.2)))) = if s.2 = p.2 then 1 else 0`.

Introduce `s`. Rewrite using `[MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm, sub_zero, coeff_psTrunc' 1 _ _ (by simp), law_coeff]`. Simplify using `only [hco, ite_mul, _root_.one_mul, zero_mul, Fintype.sum_prod_type, Fin.sum_univ_two]`. Simplify using `[ψv, Finset.sum_ite_eq']`. Establish `h1 : homAt x0 (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ jptG t x0 d x 1 (0 : Fin 2) = tanPt t x0 x v`.

Unfold `jptG tanPt`. Rewrite using `[← Category.assoc, homAt_comp, hc]`. Establish `e : (fun p : Fin 1 × Fin d => ψv (0, p.2)) = fun p => v p.2`. Use function extensionality and compare the values at `p`. Simplify using `[ψv]`.

Rewrite using `[e]`. Establish `h2 : homAt x0 (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ jptG t x0 d x 1 (1 : Fin 2) = tanPt t x0 x w`. Unfold `jptG tanPt`. Rewrite using `[← Category.assoc, homAt_comp, hc]`. Establish `e : (fun p : Fin 1 × Fin d => ψv (1, p.2)) = fun p => w p.2`.

Use function extensionality and compare the values at `p`. Simplify using `[ψv]`. Rewrite using `[e]`. Rewrite using `[← h1, ← h2, ← MonObj.comp_mul, ← hlaw, ← Category.assoc, homAt_comp, hL]`. Both sides reduce to the same expression.
-/
theorem tanPt_add (F : Germ.FGLaw S d)
    (hlaw : homAt x0 (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (F.F p.2)) ≫ x 1 =
      jptG t x0 d x 1 (0 : Fin 2) * jptG t x0 d x 1 (1 : Fin 2)) (v w : Fin d → S) :
    tanPt t x0 x (v + w) = tanPt t x0 x v * tanPt t x0 x w := by
  classical
  let ψv : Fin 2 × Fin d → S := fun p => if p.1 = 0 then v p.2 else w p.2
  have hc : ∀ (i : Fin 2), (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S).comp
      (jetCopy d 1 i : Jet S (Fin 1 × Fin d) 1 →ₐ[S] Jet S (Fin 2 × Fin d) 1) =
      tanV (fun p : Fin 1 × Fin d => ψv (i, p.2)) := by
    intro i
    unfold jetCopy
    rw [tanV_comp_jetMap]
    congr 1
    funext p
    simp only [MvPolynomial.coeff_X]
    rw [Finset.sum_eq_single (i, p.2)]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb (Finsupp.single_left_injective one_ne_zero h).symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hL : (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S).comp
      (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (F.F p.2)) =
      tanV (fun p : Fin 1 × Fin d => (v + w) p.2) := by
    unfold jetSubstP
    rw [tanV_comp_jetMap]
    congr 1
    funext p
    have hco : ∀ s : Fin 2 × Fin d, MvPolynomial.coeff (Finsupp.single s 1)
        (psTrunc 1 (F.F p.2) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc 1 (F.F p.2)))) =
        if s.2 = p.2 then 1 else 0 := by
      intro s
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm,
        sub_zero, coeff_psTrunc' 1 _ _ (by simp), law_coeff]
    simp only [hco, ite_mul, _root_.one_mul, zero_mul, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [ψv, Finset.sum_ite_eq']
  have h1 : homAt x0 (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ jptG t x0 d x 1 (0 : Fin 2) =
      tanPt t x0 x v := by
    unfold jptG tanPt
    rw [← Category.assoc, homAt_comp, hc]
    have e : (fun p : Fin 1 × Fin d => ψv (0, p.2)) = fun p => v p.2 := by
      funext p; simp [ψv]
    rw [e]
  have h2 : homAt x0 (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ jptG t x0 d x 1 (1 : Fin 2) =
      tanPt t x0 x w := by
    unfold jptG tanPt
    rw [← Category.assoc, homAt_comp, hc]
    have e : (fun p : Fin 1 × Fin d => ψv (1, p.2)) = fun p => w p.2 := by
      funext p; simp [ψv]
    rw [e]
  rw [← h1, ← h2, ← MonObj.comp_mul, ← hlaw, ← Category.assoc, homAt_comp, hL]
  rfl

/- English proof (translation)
Establish `h : tanPt t x0 x (a • c) = smT x0 a (tanPt t x0 x c)`. Unfold `tanPt smT`. Rewrite using `[← Category.assoc, homAt_comp, tanV_smul]`. Both sides reduce to the same expression. Rewrite using `[h]`.

Both sides reduce to the same expression.
-/
theorem tanPt_smul (a : S) (c : Fin d → S) :
    (tanPt t x0 x (a • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ (tanPt t x0 x c).left := by
  have h : tanPt t x0 x (a • c) = smT x0 a (tanPt t x0 x c) := by
    unfold tanPt smT
    rw [← Category.assoc, homAt_comp, tanV_smul]
    rfl
  rw [h]
  rfl

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `c`. Simplify using `[tanPt_zero h0]`.

Consider the case `succ n ih`. Introduce `c`. Rewrite using `[List.ofFn_succ, List.prod_cons, ih (fun i => c i.succ), Fin.sum_univ_succ, tanPt_add F hlaw]`.
-/
theorem tanPt_prod (h0 : homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 1 →ₐ[S] S) ≫ x 1 = 1)
    (F : Germ.FGLaw S d)
    (hlaw : homAt x0 (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (F.F p.2)) ≫ x 1 =
      jptG t x0 d x 1 (0 : Fin 2) * jptG t x0 d x 1 (1 : Fin 2)) :
    ∀ (n : ℕ) (c : Fin n → Fin d → S),
      (List.ofFn fun i => tanPt t x0 x (c i)).prod = tanPt t x0 x (∑ i, c i) := by
  intro n
  induction n with
  | zero =>
    intro c
    simp [tanPt_zero h0]
  | succ n ih =>
    intro c
    rw [List.ofFn_succ, List.prod_cons, ih (fun i => c i.succ), Fin.sum_univ_succ, tanPt_add F hlaw]

/- English proof (translation)
Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem sum_single (cf : Fin d → S) : (∑ i, cf i • (Pi.single i 1 : Fin d → S)) = cf := by
  classical
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Take `⟨u, hu, hw⟩` from `hc`. Establish `e : u = fun i => tanPt t x0 x (cf i • Pi.single i 1)`. Use function extensionality and compare the values at `i`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hu, hv, tanPt_smul]`.

Rewrite using `[← hw, e]`. Use `tanPt_prod h0 F hlaw d (fun i => cf i • Pi.single i 1)` as an intermediate fact. Rewrite `this` using `[sum_single]`. Conclude with `congrArg (fun f => f.left) this`.
-/
theorem comb_eq (h0 : homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 1 →ₐ[S] S) ≫ x 1 = 1)
    (F : Germ.FGLaw S d)
    (hlaw : homAt x0 (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (F.F p.2)) ≫ x 1 =
      jptG t x0 d x 1 (0 : Fin 2) * jptG t x0 d x 1 (1 : Fin 2))
    {v : Fin d → (Sp (DualNumber S) ⟶ t.G.left)}
    (hv : ∀ j, v j = (tanPt t x0 x (Pi.single j 1)).left) {cf : Fin d → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (hc : IsCombAtG t x0 v cf w) : w = (tanPt t x0 x cf).left := by
  obtain ⟨u, hu, hw⟩ := hc
  have e : u = fun i => tanPt t x0 x (cf i • Pi.single i 1) := by
    funext i
    apply Over.OverMorphism.ext
    rw [hu, hv, tanPt_smul]
  rw [← hw, e]
  have := tanPt_prod h0 F hlaw d (fun i => cf i • Pi.single i 1)
  rw [sum_single] at this
  exact congrArg (fun f => f.left) this

/- English proof (translation)
Use `⟨fun i => tanPt t x0 x (cf i • Pi.single i 1), fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[tanPt_smul, hv]`. Use `tanPt_prod h0 F hlaw d (fun i => cf i • Pi.single i 1)` as an intermediate fact. Rewrite `this` using `[sum_single]`. Conclude with `congrArg (fun f => f.left) this`.
-/
theorem comb_tanPt (h0 : homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 1 →ₐ[S] S) ≫ x 1 = 1)
    (F : Germ.FGLaw S d)
    (hlaw : homAt x0 (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (F.F p.2)) ≫ x 1 =
      jptG t x0 d x 1 (0 : Fin 2) * jptG t x0 d x 1 (1 : Fin 2))
    {v : Fin d → (Sp (DualNumber S) ⟶ t.G.left)}
    (hv : ∀ j, v j = (tanPt t x0 x (Pi.single j 1)).left) (cf : Fin d → S) :
    IsCombAtG t x0 v cf (tanPt t x0 x cf).left := by
  refine ⟨fun i => tanPt t x0 x (cf i • Pi.single i 1), fun i => ?_, ?_⟩
  · rw [tanPt_smul, hv]
  · have := tanPt_prod h0 F hlaw d (fun i => cf i • Pi.single i 1)
    rw [sum_single] at this
    exact congrArg (fun f => f.left) this

/- English proof (translation)
Use `⟨Over.w (tanPt t x0 x c), ?_⟩` and prove the remaining obligations. Establish `e : (TrivSqZeroExt.fstHom S S S).comp (tanV (fun p : Fin 1 × Fin d => c p.2) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) = jetAug`. Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`.

Use `show TrivSqZeroExt.fstHom S S S (tanV _ (Ideal.Quotient.mk _ (MvPolynomial.X i))) = (jetAug : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] S) (Ideal.Quotient.mk _ (MvPolynomial.X i))`. Establish `h2 : (jetAug : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] S) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0` using `by show (MvPolynomial.aeval fun _ => (0 : S)) (MvPolynomial.X i) = _`. Rewrite using `[MvPolynomial.aeval_X]`. Rewrite using `[h2, tanV_mk, MvPolynomial.aeval_X]`. Simplify using the standard rewrite rules.

Establish `h1 : homAt x0 (TrivSqZeroExt.fstHom S S S) ≫ tanPt t x0 x c = 1`. Unfold `tanPt`. Rewrite using `[← Category.assoc, homAt_comp, e]`. Conclude with `h0`. Set `iq : overAt x0 S ⟶ Over.mk x0` to `Over.homMk (𝟙 (Sp S)) (by show 𝟙 _ ≫ x0 = spMap (algebraMap S S) ≫ x0`.

Establish `: spMap (algebraMap S S) = 𝟙 _`. Simplify using `[spMap]`. Rewrite using `[this])`. Establish `h2 : iq ≫ (1 : Over.mk x0 ⟶ t.G) = 1` using `MonObj.comp_one _`. Establish `h3 : (homAt x0 (TrivSqZeroExt.fstHom S S S) ≫ tanPt t x0 x c).left = (iq ≫ (1 : Over.mk x0 ⟶ t.G)).left` using `congrArg (fun f => f.left) (h1.trans h2.symm)`.

Use `Eq.trans h3 ?_` and prove the remaining obligations. Conclude with `Category.id_comp _`.
-/
theorem tanPt_isTan (h0 : homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 1 →ₐ[S] S) ≫ x 1 = 1)
    (c : Fin d → S) : IsTanAtG t x0 (tanPt t x0 x c).left := by
  refine ⟨Over.w (tanPt t x0 x c), ?_⟩
  have e : (TrivSqZeroExt.fstHom S S S).comp
      (tanV (fun p : Fin 1 × Fin d => c p.2) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) = jetAug := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    show TrivSqZeroExt.fstHom S S S (tanV _ (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
      (jetAug : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] S) (Ideal.Quotient.mk _ (MvPolynomial.X i))
    have h2 : (jetAug : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] S) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
      show (MvPolynomial.aeval fun _ => (0 : S)) (MvPolynomial.X i) = _
      rw [MvPolynomial.aeval_X]
    rw [h2, tanV_mk, MvPolynomial.aeval_X]
    simp
  have h1 : homAt x0 (TrivSqZeroExt.fstHom S S S) ≫ tanPt t x0 x c = 1 := by
    unfold tanPt
    rw [← Category.assoc, homAt_comp, e]
    exact h0
  let iq : overAt x0 S ⟶ Over.mk x0 := Over.homMk (𝟙 (Sp S)) (by
    show 𝟙 _ ≫ x0 = spMap (algebraMap S S) ≫ x0
    have : spMap (algebraMap S S) = 𝟙 _ := by
      simp [spMap]
    rw [this])
  have h2 : iq ≫ (1 : Over.mk x0 ⟶ t.G) = 1 := MonObj.comp_one _
  have h3 : (homAt x0 (TrivSqZeroExt.fstHom S S S) ≫ tanPt t x0 x c).left =
      (iq ≫ (1 : Over.mk x0 ⟶ t.G)).left := congrArg (fun f => f.left) (h1.trans h2.symm)
  refine Eq.trans h3 ?_
  exact Category.id_comp _

end Pts

section Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
  {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} [StarRing (𝓞 E)]

/- English proof (translation)
Establish `hdir : ∀ j, (homAt x0 (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ g.x 1).left = (tanPt t x0 g.x (Pi.single j 1)).left`. Introduce `j`. Unfold `tanPt`. Rewrite using `[jetTan_eq]`. Establish `e : (Pi.single ((0 : Fin 1), j) 1 : Fin 1 × Fin d → S) = fun p => (Pi.single j 1 : Fin d → S) p.2`.

Use function extensionality and compare the values at `p`. Take `⟨a, b⟩` from `p`. Establish `: a = 0` using `Subsingleton.elim _ _`. Substitute `this` using the available equality. Distinguish the cases in `h : b = j`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`. Rewrite using `[e]`. Establish `h` using `comb_eq (g.chart.zero 1) g.B.G (g.chart.law 1) hdir (g.chart.tan l)`.

Rewrite using `[h]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Simplify using `[Pi.single_apply, eq_comm]`.
-/
theorem germ_tg (g : GermAt t x0 d) (l : Fin d) :
    g.tg l = (tanPt t x0 g.x (Pi.single l 1)).left := by
  classical
  have hdir : ∀ j, (homAt x0 (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ g.x 1).left =
      (tanPt t x0 g.x (Pi.single j 1)).left := by
    intro j
    unfold tanPt
    rw [jetTan_eq]
    have e : (Pi.single ((0 : Fin 1), j) 1 : Fin 1 × Fin d → S) = fun p => (Pi.single j 1 : Fin d → S) p.2 := by
      funext p
      obtain ⟨a, b⟩ := p
      have : a = 0 := Subsingleton.elim _ _
      subst this
      by_cases h : b = j
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [e]
  have h := comb_eq (g.chart.zero 1) g.B.G (g.chart.law 1) hdir (g.chart.tan l)
  rw [h]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

end Germ

end Lin

open Lin

/- English proof (translation)
Use extensionality with `i l`. It suffices to establish `h : (fun i => linQ Qs i l) = fun i => P i l from congrFun h i`. Set `τ : Jet k (Fin 1 × Fin d) (0 + 1) →ₐ[k] DualNumber k` to `tanV (fun p : Fin 1 × Fin d => (Pi.single l 1 : Fin d → k) p.2)`. Set `v : Sp (DualNumber k) ⟶ ((Over.pullback x).obj t.G).left` to `pullback.lift (g.tg l) (spMap (algebraMap k (DualNumber k))) (g.tan l).1`. Establish `hv1 : v ≫ pullback.fst t.G.hom x = g.tg l` using `pullback.lift_fst _ _ _`.

Establish `hv2 : v ≫ ((Over.pullback x).obj t.G).hom = spMap (algebraMap k (DualNumber k))` using `pullback.lift_snd _ _ _`. Establish `hdiff` using `hP l v hv1 hv2`. Establish `hvF : v = spMap (τ : Jet k (Fin 1 × Fin d) (0 + 1) →+* DualNumber k) ≫ (fibPt t x (g.x 1)).left`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[hv1, germ_tg g l, Category.assoc]`.

Establish `: (fibPt t x (g.x 1)).left ≫ pullback.fst t.G.hom x = (g.x 1).left` using `pullback.lift_fst _ _ _`. Rewrite using `[this]`. Both sides reduce to the same expression. Use `hv2.trans ?_` and prove the remaining obligations. Rewrite using `[Category.assoc]`.

Establish `: (fibPt t x (g.x 1)).left ≫ pullback.snd t.G.hom x = spMap (algebraMap k (Jet k (Fin 1 × Fin d) 1)) ≫ 𝟙 _` using `pullback.lift_snd _ _ _`. Rewrite using `[this, Category.comp_id]`. Conclude with `(spMap_comp_alg τ).symm`. Establish `hsub : τ.comp (sub1 Qs 1 : Jet k (Fin 1 × Fin d') 1 →ₐ[k] Jet k (Fin 1 × Fin d) 1) = tanV (fun p : Fin 1 × Fin d' => linQ Qs p.2 l)` using `by show (tanV (fun p : Fin 1 × Fin d => (Pi.single l 1 : Fin d → k) p.2) : Jet k (Fin 1 × Fin d) (0 + 1) →ₐ[k] DualNumber k).comp (jetMap (fun q : Fin 1 × Fin d' => psTrunc 1 (Qs q.2) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc 1 (Qs q.2)))) fun _ => sub_const_mem_orig …`. Rewrite using `[tanV_comp_jetMap]`.

Use `congr 1`. Use function extensionality and compare the values at `q`. Rewrite using `[Finset.sum_eq_single ((0 : Fin 1), l)]`. Rewrite using `[MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm, sub_zero, coeff_psTrunc' 1 _ _ (by simp)]`. Simplify using `[linQ]`.

Introduce and unpack `⟨a, b⟩ _ hb`. Establish `hbl : b ≠ l`. Introduce `h`. Apply `hb` to reduce the goal to its premises. Rewrite using `[h, Subsingleton.elim a 0]`.

Simplify using `[Pi.single_apply, hbl]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hvq : v ≫ Q.q.left = (tanPt Q.tB (𝟙 (Sp k)) gB.x (fun i => linQ Qs i l)).left`. Establish `hm : (fibPt t x (g.x 1)).left ≫ Q.q.left = (homAt (𝟙 (Sp k)) (sub1 Qs 1) ≫ gB.x 1).left` using `congrArg (fun f => f.left) (hQ 1)`.

Establish `h2 : tanPt Q.tB (𝟙 (Sp k)) gB.x (fun i => linQ Qs i l) = homAt (𝟙 (Sp k)) τ ≫ homAt (𝟙 (Sp k)) (sub1 Qs 1) ≫ gB.x 1`. Unfold `tanPt`. Rewrite using `[← Category.assoc, homAt_comp, hsub]`. Rewrite using `[hvF, Category.assoc, hm, h2]`. Both sides reduce to the same expression.

Establish `hw` using `tanPt_isTan (t := Q.tB) (x0 := 𝟙 (Sp k)) (x := gB.x) (gB.chart.zero 1) (fun i => linQ Qs i l)`. Take `⟨a, _, hu⟩` from `gB.basis _ hw`. Establish `c1` using `comb_tanPt (gB.chart.zero 1) gB.B.G (gB.chart.law 1) (germ_tg gB) (fun i => linQ Qs i l)`. Establish `c2 : IsCombAtG Q.tB (𝟙 (Sp k)) gB.tg (fun i => P i l) (tanPt Q.tB (𝟙 (Sp k)) gB.x (fun i => linQ Qs i l)).left` using `hvq ▸ hdiff`. Conclude with `(hu _ c1).trans (hu _ c2).symm`.
-/
theorem linQ_eq_diff (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)]
    (_hstar : ∀ a : 𝓞 E, star a = H.bar a) (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d)
    (gB : GermAt Q.tB (𝟙 (Sp k)) d') (P : Matrix (Fin d') (Fin d) k) (hP : Q.IsDiff g gB P)
    (Qs : Fin d' → PS k 1 d) (_hQ0 : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0)
    (hQ : ∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) : linQ Qs = P := by
  classical
  ext i l
  suffices h : (fun i => linQ Qs i l) = fun i => P i l from congrFun h i
  let τ : Jet k (Fin 1 × Fin d) (0 + 1) →ₐ[k] DualNumber k :=
    tanV (fun p : Fin 1 × Fin d => (Pi.single l 1 : Fin d → k) p.2)
  let v : Sp (DualNumber k) ⟶ ((Over.pullback x).obj t.G).left :=
    pullback.lift (g.tg l) (spMap (algebraMap k (DualNumber k))) (g.tan l).1
  have hv1 : v ≫ pullback.fst t.G.hom x = g.tg l := pullback.lift_fst _ _ _
  have hv2 : v ≫ ((Over.pullback x).obj t.G).hom = spMap (algebraMap k (DualNumber k)) :=
    pullback.lift_snd _ _ _
  have hdiff := hP l v hv1 hv2
  have hvF : v = spMap (τ : Jet k (Fin 1 × Fin d) (0 + 1) →+* DualNumber k) ≫ (fibPt t x (g.x 1)).left := by
    apply pullback.hom_ext
    · rw [hv1, germ_tg g l, Category.assoc]
      have : (fibPt t x (g.x 1)).left ≫ pullback.fst t.G.hom x = (g.x 1).left := pullback.lift_fst _ _ _
      rw [this]
      rfl
    · refine hv2.trans ?_
      rw [Category.assoc]
      have : (fibPt t x (g.x 1)).left ≫ pullback.snd t.G.hom x =
          spMap (algebraMap k (Jet k (Fin 1 × Fin d) 1)) ≫ 𝟙 _ := pullback.lift_snd _ _ _
      rw [this, Category.comp_id]
      exact (spMap_comp_alg τ).symm
  have hsub : τ.comp (sub1 Qs 1 : Jet k (Fin 1 × Fin d') 1 →ₐ[k] Jet k (Fin 1 × Fin d) 1) =
      tanV (fun p : Fin 1 × Fin d' => linQ Qs p.2 l) := by
    show (tanV (fun p : Fin 1 × Fin d => (Pi.single l 1 : Fin d → k) p.2) :
        Jet k (Fin 1 × Fin d) (0 + 1) →ₐ[k] DualNumber k).comp
      (jetMap (fun q : Fin 1 × Fin d' => psTrunc 1 (Qs q.2) -
        MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc 1 (Qs q.2)))) fun _ => sub_const_mem_orig _) = _
    rw [tanV_comp_jetMap]
    congr 1
    funext q
    rw [Finset.sum_eq_single ((0 : Fin 1), l)]
    · rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm,
        sub_zero, coeff_psTrunc' 1 _ _ (by simp)]
      simp [linQ]
    · rintro ⟨a, b⟩ _ hb
      have hbl : b ≠ l := by
        intro h
        apply hb
        rw [h, Subsingleton.elim a 0]
      simp [Pi.single_apply, hbl]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hvq : v ≫ Q.q.left = (tanPt Q.tB (𝟙 (Sp k)) gB.x (fun i => linQ Qs i l)).left := by
    have hm : (fibPt t x (g.x 1)).left ≫ Q.q.left = (homAt (𝟙 (Sp k)) (sub1 Qs 1) ≫ gB.x 1).left :=
      congrArg (fun f => f.left) (hQ 1)
    have h2 : tanPt Q.tB (𝟙 (Sp k)) gB.x (fun i => linQ Qs i l) =
        homAt (𝟙 (Sp k)) τ ≫ homAt (𝟙 (Sp k)) (sub1 Qs 1) ≫ gB.x 1 := by
      unfold tanPt
      rw [← Category.assoc, homAt_comp, hsub]
    rw [hvF, Category.assoc, hm, h2]
    rfl
  have hw := tanPt_isTan (t := Q.tB) (x0 := 𝟙 (Sp k)) (x := gB.x) (gB.chart.zero 1) (fun i => linQ Qs i l)
  obtain ⟨a, _, hu⟩ := gB.basis _ hw
  have c1 := comb_tanPt (gB.chart.zero 1) gB.B.G (gB.chart.law 1) (germ_tg gB) (fun i => linQ Qs i l)
  have c2 : IsCombAtG Q.tB (𝟙 (Sp k)) gB.tg (fun i => P i l)
      (tanPt Q.tB (𝟙 (Sp k)) gB.x (fun i => linQ Qs i l)).left := hvq ▸ hdiff
  exact (hu _ c1).trans (hu _ c2).symm

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
