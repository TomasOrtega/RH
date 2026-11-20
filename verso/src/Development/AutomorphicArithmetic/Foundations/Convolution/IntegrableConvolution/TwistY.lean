import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwTrace
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.JointEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistPerm
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.RestScalar
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SphRank
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensOp
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.IntPow
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.FinSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GlueBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistUnitary
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistYA

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate InnerProductSpace Classical

namespace UpperTheory.ConvolutionTheory.L1.TY

section Hil
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
The claim follows from `Commute.mul_nonneg h (prj_star _).nonneg hc`.
-/
private theorem pos_mul {O : H →L[ℂ] H} {W : Submodule ℂ H} (h : 0 ≤ O) (hc : Commute O (prj W)) : 0 ≤ O * prj W :=
  Commute.mul_nonneg h (prj_star _).nonneg hc

/- English proof (translation)
Use extensionality with `v`. Rewrite using `[mem_eigIn, Complex.ofReal_one, one_smul, Submodule.mem_inf]`. Conclude with `and_congr_right fun _ => ⟨fun h => h ▸ prj_mem hW v, prj_self⟩`.
-/
private theorem eig_one (V : Submodule ℂ H) {W : Submodule ℂ H} (hW : IsClosed (W : Set H)) : eigIn V (prj W) 1 = V ⊓ W := by
  ext v
  rw [mem_eigIn, Complex.ofReal_one, one_smul, Submodule.mem_inf]
  exact and_congr_right fun _ => ⟨fun h => h ▸ prj_mem hW v, prj_self⟩

/- English proof (translation)
Establish `hprod : (List.ofFn fun i => O i * prj (W i)).prod = Oi * prj Wn`. Rewrite using `[ofFn_mul _ _ _ fun i j _ => hc i j, hOi, hQ]`. Establish `hOQ : Commute Oi (prj Wn)`. Rewrite using `[hOi]`. Use `Commute.list_prod_left _ _ fun x hx => ?_` and prove the remaining obligations.

Take `⟨i, rfl⟩` from `(List.mem_ofFn' _ _).1 hx`. Conclude with `(hc' i).symm`. Use `⟨fun x hx => ?_, fun y hy => ?_, ?_, fun v hv h => ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Rewrite using `[prodEig, eig_one V h₀, hprod, mem_eigIn, mem_eigIn, eig_mul hn hOQ hx.ne', hTy]`.

Simplify using `only [Submodule.mem_inf]`. The claim follows by propositional logic. Use extensionality with `v`. Establish `h2` using `fun i => eig_mul (hW i) (hc i i).symm hy.ne' v`. Simplify using `only [jointEig, eig_one V h₀, hTy, hWn, Submodule.mem_iInf, Submodule.mem_inf, mem_eigIn, h2, Submodule.mem_top, true_and, forall_and, forall_const]`.

The claim follows by propositional logic. Rewrite using `[hprod, eig_one V h₀]`. Establish `hcl : IsClosed ((V ⊓ W₀ : Submodule ℂ H) : Set H)`. Rewrite using `[Submodule.coe_inf]`. Conclude with `hV.inter h₀`.

Use `cast (congrArg _ (funext fun v => ?_)) (hK.comp_clm (prj (V ⊓ W₀)))` and prove the remaining obligations. Establish `hu` using `prj_mem hcl v`. Simplify using `only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply]`. Rewrite using `[prj_self (hVC hu.1), hTy, ← prj_mul hn h₀ hc₀, ContinuousLinearMap.mul_apply, prj_self hu.2]`. Rewrite `hv` using `[hTy, hWn]`.

Use `⟨0, v, eig_one V h₀ ▸ ⟨hv.1, hv.2.2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.mul_apply, prj_self ((Submodule.mem_iInf _).1 hv.2.1 0)]` and apply the resulting hypothesis.
-/
private theorem fin_abs {m : ℕ} {V W₀ Wn Ty C : Submodule ℂ H} {W : Fin (m + 1) → Submodule ℂ H} {O : Fin (m + 1) → H →L[ℂ] H}
    {Oi : H →L[ℂ] H} (hV : IsClosed (V : Set H)) (h₀ : IsClosed (W₀ : Set H)) (hn : IsClosed (Wn : Set H))
    (hW : ∀ i, IsClosed (W i : Set H)) (hTy : Ty = Wn ⊓ W₀) (hWn : Wn = ⨅ i, W i) (hVC : V ≤ C)
    (hOi : Oi = (List.ofFn O).prod) (hQ : (List.ofFn fun i => prj (W i)).prod = prj Wn)
    (hc : ∀ i j, Commute (prj (W i)) (O j)) (hc' : ∀ j, Commute (prj Wn) (O j)) (hc₀ : Commute (prj Wn) (prj W₀))
    (hK : IsCompactOperator (Oi ∘L prj Ty ∘L prj C)) :
    (∀ x : ℝ, 0 < x → prodEig V (prj W₀) (fun i => O i * prj (W i)) x = eigIn (V ⊓ Ty) Oi x) ∧
    (∀ y : ℝ, 0 < y → jointEig V (prj W₀) (fun i => O i * prj (W i)) y = V ⊓ (⨅ i, eigIn ⊤ (O i) y) ⊓ Ty) ∧
    IsCompactOperator ((List.ofFn fun i => O i * prj (W i)).prod ∘L prj (eigIn V (prj W₀) 1)) ∧
    ∀ v ∈ V ⊓ Ty, O 0 v ≠ 0 → ∃ i, ∃ v ∈ eigIn V (prj W₀) 1, (O i * prj (W i)) v ≠ 0 := by
  have hprod : (List.ofFn fun i => O i * prj (W i)).prod = Oi * prj Wn := by
    rw [ofFn_mul _ _ _ fun i j _ => hc i j, hOi, hQ]
  have hOQ : Commute Oi (prj Wn) := by
    rw [hOi]
    refine Commute.list_prod_left _ _ fun x hx => ?_
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact (hc' i).symm
  refine ⟨fun x hx => ?_, fun y hy => ?_, ?_, fun v hv h => ?_⟩
  · ext v
    rw [prodEig, eig_one V h₀, hprod, mem_eigIn, mem_eigIn, eig_mul hn hOQ hx.ne', hTy]
    simp only [Submodule.mem_inf]
    tauto
  · ext v
    have h2 := fun i => eig_mul (hW i) (hc i i).symm hy.ne' v
    simp only [jointEig, eig_one V h₀, hTy, hWn, Submodule.mem_iInf, Submodule.mem_inf, mem_eigIn, h2, Submodule.mem_top,
      true_and, forall_and, forall_const]
    tauto
  · rw [hprod, eig_one V h₀]
    have hcl : IsClosed ((V ⊓ W₀ : Submodule ℂ H) : Set H) := by
      rw [Submodule.coe_inf]; exact hV.inter h₀
    refine cast (congrArg _ (funext fun v => ?_)) (hK.comp_clm (prj (V ⊓ W₀)))
    have hu := prj_mem hcl v
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply]
    rw [prj_self (hVC hu.1), hTy, ← prj_mul hn h₀ hc₀, ContinuousLinearMap.mul_apply, prj_self hu.2]
  · rw [hTy, hWn] at hv
    refine ⟨0, v, eig_one V h₀ ▸ ⟨hv.1, hv.2.2⟩, ?_⟩
    rwa [ContinuousLinearMap.mul_apply, prj_self ((Submodule.mem_iInf _).1 hv.2.1 0)]

end Hil

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {n m : ℕ} {q : Pl F} {w₀ : PlacesOver E q}

/- English proof (translation)
Take `⟨h1, -, -, -, -, -, h2, -⟩` from `glueBasic _ _ _ _ m D n`. Establish `hc : ∀ x j, GM.cmp (w j) x = mapGL n (completionMap p (w j).1) (D.comp n j x)` using `fun x j => Units.ext (Matrix.ext fun a b => (hw _ j).symm)`. Establish `key : ∀ j : Fin (m + 1), (T.J (w (j + 1)).1).comap (mapGL n (completionMap p (w (j + 1)).1)) ≤ (T.J (w j).1).comap (mapGL n (completionMap p (w j).1))` using `fun j g hg => by`. Establish `h3` using `(T.stable p (D.glue n (Pi.mulSingle (j + 1) g)) fun u => by`. Take `⟨k, rfl⟩` from `w.surjective u`.

Rewrite using `[hc, h1]`. Distinguish the cases in `e : k = j + 1`. Substitute `e` using the available equality. Rewrite using `[Pi.mulSingle_eq_same]`. Conclude with `hg`.

Rewrite using `[Pi.mulSingle_eq_of_ne e, map_one]`. Conclude with `one_mem _).1 (w j)`. Rewrite `h3` using `[hc, h2, h1, Pi.mulSingle_eq_same]`. Then use the resulting hypothesis. Conclude with `le_antisymm (cyc_le (fun j => (T.J (w j).1).comap (mapGL n (completionMap p (w j).1))) key i) (key i)`.
-/
private theorem lev_step (T : Ty σ n q w₀) (p : Pl F) (D : Split (incFin E p) (galFin σ p) m) (w : Fin (m + 1) ≃ PlacesOver E p)
    (hw : ∀ (b : CompletionsOver E p) i, completionMap p (w i).1 (D.e b i) = b (w i)) (i : Fin (m + 1)) :
    (T.J (w i).1).comap (mapGL n (completionMap p (w i).1)) = (T.J (w (i + 1)).1).comap (mapGL n (completionMap p (w (i + 1)).1)) := by
  obtain ⟨h1, -, -, -, -, -, h2, -⟩ := glueBasic _ _ _ _ m D n
  have hc : ∀ x j, GM.cmp (w j) x = mapGL n (completionMap p (w j).1) (D.comp n j x) := fun x j =>
    Units.ext (Matrix.ext fun a b => (hw _ j).symm)
  have key : ∀ j : Fin (m + 1), (T.J (w (j + 1)).1).comap (mapGL n (completionMap p (w (j + 1)).1)) ≤
      (T.J (w j).1).comap (mapGL n (completionMap p (w j).1)) := fun j g hg => by
    have h3 := (T.stable p (D.glue n (Pi.mulSingle (j + 1) g)) fun u => by
      obtain ⟨k, rfl⟩ := w.surjective u
      rw [hc, h1]
      by_cases e : k = j + 1
      · subst e
        rw [Pi.mulSingle_eq_same]
        exact hg
      · rw [Pi.mulSingle_eq_of_ne e, map_one]
        exact one_mem _).1 (w j)
    rwa [hc, h2, h1, Pi.mulSingle_eq_same] at h3
  exact le_antisymm (cyc_le (fun j => (T.J (w j).1).comap (mapGL n (completionMap p (w j).1))) key i) (key i)

/- English proof (translation)
Take `rfl : p = p'` from `Subtype.ext (by rw [← under_of_over (w p i), h, under_of_over])`. Conclude with `⟨rfl, (w p).injective (Subtype.ext h)⟩`.
-/
private theorem place_inj {P : Finset (Pl F)} (w : ∀ p : P, Fin (m + 1) ≃ PlacesOver E p.1) {p p' : P} {i j : Fin (m + 1)}
    (h : (w p i).1 = (w p' j).1) : p = p' ∧ i = j := by
  obtain rfl : p = p' := Subtype.ext (by rw [← under_of_over (w p i), h, under_of_over])
  exact ⟨rfl, (w p).injective (Subtype.ext h)⟩

private def gen {P : Finset (Pl F)} (s : Fin (m + 1) → archGroup F n →* archGroup E n)
    (w : ∀ p : P, Fin (m + 1) ≃ PlacesOver E p.1) (i : Fin (m + 1)) :
    archGroup F n ⊕ (Σ p : P, GL (Fin n) (p.1.adicCompletion F)) → normOneGL E n
  | .inl g => archP E n (s i g)
  | .inr x => MultiplicityOne.finProj E n (AdelicGLn.localEmbedding (w x.1 i).1 (mapGL n (completionMap x.1.1 (w x.1 i).1) x.2))

/- English proof (translation)
The claim follows from `lift_int _ B _ _ (fun x v => by rcases x with g | ⟨p, g⟩ · exact DFunLike.congr_fun (h1 g).eq v · exact DFunLike.congr_fun (h2 p _).eq v) g v`.
-/
private theorem gen_int (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] {P : Finset (Pl F)}
    (s : Fin (m + 1) → archGroup F n →* archGroup E n) (w : ∀ p : P, Fin (m + 1) ≃ PlacesOver E p.1) (i : Fin (m + 1))
    (B : LL μ →L[ℂ] LL μ) (h1 : ∀ g, Commute B (rightRegularRep (rationalGLOne E n) μ (archP E n (s i g))))
    (h2 : ∀ p g, Commute B (rhoL μ (w p i).1 g)) (g : FreeGroup _) (v : LL μ) :
    B (rightRegularRep (rationalGLOne E n) μ (FreeGroup.lift (gen s w i) g) v) =
      rightRegularRep (rationalGLOne E n) μ (FreeGroup.lift (gen s w i) g) (B v) :=
  lift_int _ B _ _ (fun x v => by
    rcases x with g | ⟨p, g⟩
    · exact DFunLike.congr_fun (h1 g).eq v
    · exact DFunLike.congr_fun (h2 p _).eq v) g v

end UpperTheory.ConvolutionTheory.L1.TY

open UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.L1.TY in
set_option maxHeartbeats 1600000 in
/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ hσ m n hm hn μ _ θ hθ D s hs hposition νE _ νF _ b a aE aF hA q w₀ hq T V hV hVU hrk`. Set `P : Finset (Pl F)` to `insert q T.sp`. Establish `hsp : ∀ p : P, GM.Split E p.1` using `fun p => by`. Break down `Finset.mem_insert.1 p.2 with h | h` into its components or cases. Conclude with `h ▸ hq`.

Conclude with `(Finset.mem_filter.1 h).2`. Establish `hmk : ∀ p : P, ∃ u : PlacesOver E p.1, ∀ x ∈ T.marked, x.under (𝓞 F) = p.1 → x = u.1` using `fun p => by`. Take `⟨p, hp⟩` from `p`. Distinguish the cases in `e : p = q`. Substitute `e` using the available equality.

Use `⟨w₀, ?_⟩` and prove the remaining obligations. Introduce and unpack `x (rfl | ⟨v, hv, rfl⟩) hx`. Both sides reduce to the same expression. Rewrite `hx` using `[under_of_over]`. Take `rfl : v = p` from `hx`.

Conclude with `absurd (Finset.mem_filter.1 hv).1 T.q_not`. Use `⟨T.mk' p, ?_⟩` and prove the remaining obligations. Introduce and unpack `x (rfl | ⟨v, hv, rfl⟩) hx`. Rewrite `hx` using `[under_of_over]`. Conclude with `absurd hx.symm e`.

Rewrite `hx` using `[under_of_over]`. Substitute `hx` using the available equality. Both sides reduce to the same expression. Use `choose mk hmk using hmk`. Use `choose Df w hw0 hw using fun p : P => finSplit F E σ hσ m hm p.1 (mk p) (hsp p)`.

Take `⟨U, hU, -, -⟩` from `twistUnitary E n μ θ`. Establish `hU' : ∀ v, U v = θ.U v` using `fun v => DFunLike.congr_fun hU v`. Take `⟨tp1, tp2, tp3⟩` from `twistPerm F E σ hσ m n μ θ hθ`. Take `⟨-, ag2, ag3, -⟩` from `archBasic F E σ m D n`. Establish `hsurj : ∀ (p : P) i, Function.Surjective (mapGL n (completionMap p.1 (w p i).1))` using `fun p i y => by`.

Take `⟨⟨e, he⟩, -⟩` from `splitLoc F E p.1 (w p i) (hsp p _) n`. Conclude with `⟨e.symm y, by rw [← he, e.apply_symm_apply]⟩`. Set `R : Fin (m + 1) → Set (Pl E)` to `fun i => Set.range fun p : P => (w p i).1`. Set `On : Set (Pl E)` to `{u | u.under (𝓞 F) ∈ (P : Set (Pl F))}`. Establish `hOn : ∀ u ∈ On, ∃ p i, (w p i).1 = u` using `fun u hu => ⟨⟨_, hu⟩, (w ⟨_, hu⟩).symm ⟨u, ⟨rfl⟩⟩, by rw [Equiv.apply_symm_apply]⟩`.

Establish `hOn' : ∀ p i, (w p i).1 ∈ On` using `fun p i => by show _ ∈ (P : Set (Pl F))`. Rewrite using `[under_of_over]`. Conclude with `p.2`. Establish `hRU : ⋃ i, R i = On`. Use extensionality with `u`.

Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨fun ⟨i, p, e⟩ => e ▸ hOn' p i, fun h => by obtain ⟨p, i, e⟩ := hOn u h; exact ⟨i, p, e⟩⟩`. Establish `hRd : ∀ i j, i ≠ j → Disjoint (R i) (R j)` using `fun i j hij => Set.disjoint_left.2 (by`. Introduce and unpack `_ ⟨p, rfl⟩ ⟨p', e⟩`. Conclude with `hij (place_inj w e).2.symm)`.

Establish `hRO : ∀ i, Disjoint (R i) Onᶜ` using `fun i => Set.disjoint_left.2 (by`. Introduce and unpack `_ ⟨p, rfl⟩ h`. Conclude with `h (hOn' p i))`. Set `O : Fin (m + 1) → LL μ →L[ℂ] LL μ` to `fun i => OComponent μ (s i) (hs i) νF a`. Set `Q : Set (Pl E) → LL μ →L[ℂ] LL μ` to `fun A => prj (GA μ T.J T.χ A)`.

Establish `hss : ∀ i j, i ≠ j → ∀ g h, Commute (s i g) (s j h)` using `fun i j hij g h => by`. Rewrite using `[hposition, hposition]`. Use `show _ * _ = _ * _`. Rewrite using `[← ag3, ← ag3]`. Conclude with `congrArg _ (Pi.mulSingle_commute (f := fun _ : Fin (m + 1) => archGroup F n) hij g h).eq`.

Establish `hOc : ∀ (B : LL μ →L[ℂ] LL μ) i, (∀ g, Commute B (rightRegularRep (rationalGLOne E n) μ (archP E n (s i g)))) → Commute B (O i)` using `fun B i h => ContinuousLinearMap.ext fun v => operatorAt_int μ (hs i) (hs i) νF a B (fun x u => DFunLike.congr_fun (h x).eq u) v`. Establish `hrep : ∀ x y : normOneGL E n, Commute x y → Commute (rightRegularRep (rationalGLOne E n) μ x) (rightRegularRep (rationalGLOne E n) μ y)` using `fun x y h => ContinuousLinearMap.ext fun v => by`. Simplify using `only [ContinuousLinearMap.mul_apply]`. Rewrite using `[← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, h.eq]`. Establish `hQO : ∀ A i, Commute (Q A) (O i)` using `fun A i => hOc _ i fun g => (GA_arch μ A _).symm`.

Establish `hOa : ∀ i j, i ≠ j → ∀ g, Commute (O i) (rightRegularRep (rationalGLOne E n) μ (archP E n (s j g)))` using `fun i j hij g => (hOc _ i fun x => hrep _ _ ((hss j i hij.symm g x).map _)).symm`. Establish `hOO : ∀ i j, Commute (O i) (O j)` using `fun i j => by`. Distinguish the cases in `e : i = j`. Rewrite using `[e]`. Conclude with `hOc _ j (hOa i j e)`.

Establish `hOr : ∀ i u g, Commute (O i) (rhoL μ u g)` using `fun i u g => (hOc _ i fun x => (hrep _ _ (arch_fin _ _)).symm).symm`. Establish `hOV : ∀ i, ∀ v ∈ V, O i v ∈ V` using `fun i v hv => by`. Establish `h` using `hOc (prj V) i fun g => ContinuousLinearMap.ext fun y => inv_commute _ hV.closed hV.inv _ y`. Rewrite using `[← prj_self hv, ← ContinuousLinearMap.mul_apply, ← h.eq]`. Conclude with `prj_mem hV.closed _`.

Establish `hQQ : ∀ i j, Commute (Q (R i)) (Q (R j))` using `fun i j => by`. Distinguish the cases in `e : i = j`. Rewrite using `[e]`. Conclude with `GA_GA μ (hRd i j e)`. Establish `hco : ∀ u, CO (T.J u) ∧ IsChr (T.J u) (T.χ u)` using `fun u => ⟨T.co u, T.chr u⟩`.

Establish `hcof : ∀ᶠ u in Filter.cofinite, T.J u = GLnLocal.integralGL (u.adicCompletion E) n ∧ T.χ u = 1`. Use `Filter.eventually_cofinite.2 (((insert q T.S).finite_toSet.biUnion fun v _ => finite_over (E := E) v).subset fun u hu => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, exists_eq_right', Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or] at h`. Conclude with `hu (T.off u h.2 h.1)`.

Establish `hcomm : ∀ i j, i ≠ j → ∀ g h, Commute (FreeGroup.lift (gen s w i) g) (FreeGroup.lift (gen s w j) h)` using `fun i j hij => lift_commute _ _ fun x y => by`. Apply the tactic sequence `rcases x with g | ⟨p, g⟩ <;> rcases y with g' | ⟨p', g'⟩`. Conclude with `(hss i j hij g g').map _`. Conclude with `arch_fin _ _`. Conclude with `(arch_fin _ _).symm`.

Conclude with `Commute.map ((UpperTheory.ConvolutionTheory.Tf.locEmb E n _).2.2.2.1 _ (fun e => hij (place_inj w e).2.symm) _ _) _`. Establish `hUQ : ∀ i v, U (Q (R (i + 1)) v) = Q (R i) (U v)` using `fun i => by`. Use `prj_equiv (GA_closed μ _) (GA_closed μ _) U fun v => ?_` and prove the remaining obligations. Establish `h1 : ∀ j y, y ∈ GA μ T.J T.χ (R j) ↔ ∀ p : P, ∀ g ∈ (T.J (w p j).1).comap (mapGL n (completionMap p.1 (w p j).1)), rhoL μ (w p j).1 (mapGL n (completionMap p.1 (w p j).1) g) y = y` using `fun j y => by`. Rewrite using `[mem_GA]`.

Prove the components needed by the constructor for the conclusion. Introduce `h p g hg`. Rewrite using `[h _ ⟨p, rfl⟩ _ hg, T.triv p.1 (hsp p) (w p j), Pi.one_apply, one_smul]`. Introduce and unpack `h _ ⟨p, rfl⟩ x hx`. Take `⟨g, rfl⟩` from `hsurj p j x`.

Rewrite using `[h p g hx, T.triv p.1 (hsp p) (w p j), Pi.one_apply, one_smul]`. Rewrite using `[h1, h1]`. Use `forall_congr' fun p => ?_` and prove the remaining obligations. Rewrite using `[lev_step T p.1 (Df p) (w p) (hw p) i]`. Use `forall₂_congr fun g _ => ?_` and prove the remaining obligations.

Rewrite using `[hU', ← tp2 p.1 (Df p) (w p) (hw p) i g v, ← hU', ← hU']`. Conclude with `U.injective.eq_iff`. Establish `S : Slots (rightRegularRep (rationalGLOne E n) μ) V m (fun i => FreeGroup.lift (gen s w i)) (Q Onᶜ) (fun i => O i * Q (R i)) U` using `{ summand := ⟨le_top, hV.closed, hV.inv, hV.ne_bot, hV.irred⟩ ι_comm := hcomm rest := fun γ => by`. Take `⟨A, h, rfl⟩` from `MultiplicityOne.exists_archProj_mul_finProj γ`. Establish `hfin : On.Finite` using `(P.finite_toSet.biUnion fun v _ => finite_over (E := E) v).subset fun u hu => Set.mem_biUnion hu rfl`.

Take `⟨x, hx, h', e, h1⟩` from `split_fin (prodM _ hcomm) hfin.toFinset (fun u hu y => by`. Take `⟨p, i, rfl⟩` from `hOn u (hfin.mem_toFinset.1 hu)`. Take `⟨g, rfl⟩` from `hsurj p i y`. Use `mem_prodM _ hcomm i (FreeGroup.of (.inr ⟨p, g⟩))` as an intermediate fact. Rewrite using `[FreeGroup.lift_apply_of] at this) h` and apply the resulting hypothesis.

Establish `ha : archP E n ⟨A, Subgroup.mem_top A⟩ ∈ prodM _ hcomm`. Rewrite using `[← ag2 ⟨A, Subgroup.mem_top A⟩, ← ofFn_mulSingle fun i => compA D n i _]`. Use `map_list_prod ((archP E n).comp (MonoidHom.mk' (glueA D n) ag3)) (List.ofFn fun i => (Pi.mulSingle i (compA D n i ⟨A, Subgroup.mem_top A⟩) : Fin (m + 1) → archGroup F n))` as an intermediate fact. Use `(this ▸ Submonoid.list_prod_mem _ fun y hy => ?_ : ((archP E n).comp (MonoidHom.mk' (glueA D n) ag3)) _ ∈ _)` and prove the remaining obligations. Rewrite `hy` using `[List.map_ofFn]`.

Take `⟨i, rfl⟩` from `(List.mem_ofFn' _ _).1 hy`. Use `mem_prodM _ hcomm i (FreeGroup.of (.inl (compA D n i ⟨A, Subgroup.mem_top A⟩)))` as an intermediate fact. Rewrite `this` using `[FreeGroup.lift_apply_of, gen, hposition]`. Conclude with `this`. Take `⟨g, hg⟩` from `Submonoid.mul_mem _ ha hx`.

Take `⟨c, hc⟩` from `restScalar E n μ V hV T.J T.χ hco hcof On (fun u hu => by`. Distinguish the cases in `hS : u.under (𝓞 F) ∈ T.S`. Conclude with `hrk _ hS (fun h => hu (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hS, h⟩))) ⟨u, ⟨rfl⟩⟩`. Take `⟨e1, e2⟩` from `T.off u hS fun h => hu (h ▸ Finset.mem_insert_self _ _ : _ ∈ P)`. Rewrite using `[e1, e2]`.

Conclude with `sphRank E n μ V hV u) h' fun u hu => h1 u (hfin.mem_toFinset.2 hu)`. Use `⟨g, _, c, ?_, fun v hv => hc _ ⟨GA_mem μ hV _ hv, prj_mem (GA_closed μ _) v⟩⟩` and prove the remaining obligations. Rewrite using `[← hg, e, mul_assoc]`. Both sides reduce to the same expression. Use `E_sa := (prj_star _).isSelfAdjoint`.

Use `E_idem := fun v => prj_self (prj_mem (GA_closed μ _) v)`. Use `E_mem := fun v hv => GA_mem μ hV _ hv`. Use `E_ι := fun i => gen_int μ s w i _ (fun g => (GA_arch μ _ _).symm) fun p g => (GA_rhoL μ (Set.notMem_compl_iff.2 (hOn' p i)) g).symm`. Use `A_pos := fun i => pos_mul (sqOp F n νF b a aF m hA.sq hA.pow hA.norm _ _).2.1 (hQO _ i).symm`. Use `A_mem := fun i v hv => hOV i _ (GA_mem μ hV _ hv)`.

Use `A_E := fun i v => DFunLike.congr_fun ((hQO _ i).symm.mul_left (GA_GA μ (hRO i))).eq v`. Use `A_A := fun i j v => DFunLike.congr_fun (((hOO i j).mul_left (hQO _ j)).mul_right ((hQO _ i).symm.mul_left (hQQ i j))).eq v`. Use `A_ι := fun i j hij => gen_int μ s w j _ (fun g => (hOa i j hij g).mul_left (GA_arch μ _ _).symm) fun p g => (hOr i _ g).mul_left (GA_rhoL μ (Set.disjoint_right.1 (hRd i j hij) ⟨p, rfl⟩) g).symm`. Use `U_mem := by`. Rewrite using `[← hVU]`.

Use `congr 1`. Conclude with `LinearMap.ext hU'`. Use `U_E := fun v => by`. Rewrite using `[hU', hU']`. Conclude with `DFunLike.congr_fun (tp3 q w₀ T P).eq v`.

Use `U_A := fun i v => by show U (O (i + 1) (Q (R (i + 1)) v)) = O i (Q (R i) (U v))`. Rewrite using `[← hUQ, hU', hU']`. Conclude with `operatorAt_int μ (hs _) (hs _) νF a θ.U (tp1 D s hposition i) _`. Use `U_ι := fun i => lift_int _ U _ _ fun x v => by`. Rewrite using `[hU', hU']`.

Break down `x with g | ⟨p, g⟩` into its components or cases. Conclude with `tp1 D s hposition i g v`. Conclude with `tp2 p.1 (Df p) (w p) (hw p) i g v }`. Establish `hOi : Oinf μ νE aE = (List.ofFn O).prod` using `tensOp F E σ m D n νE νF hA.meas s hs hposition (LL μ) _ (fun _ => a) aE hA.tens`. Establish `hty : T.typed μ = GA μ T.J T.χ Set.univ` using `by simp only [GA, Ty.typed, Set.mem_univ, iInf_true]`.

Take `⟨hPE, hJE, hcpt, hne⟩` from `fin_abs (W := fun i => GA μ T.J T.χ (R i)) (Ty := T.typed μ) hV.closed (GA_closed μ (J := T.J) (χ := T.χ) Onᶜ) (GA_closed μ (J := T.J) (χ := T.χ) On) (fun i => GA_closed μ _) (by rw [← GA_union, Set.union_compl_self, hty]) (by rw [← hRU]; exact iInf_iUnion _ _) hV.le hOi (by rw [ …`. Take `⟨hfd, hex⟩` from `jointEx _ _ _ _ V m _ _ _ U S hcpt`. Use `⟨fun ⟨v, hv, h0⟩ => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, h⟩` from `hex (hne v hv h0)`. Conclude with `⟨y, hy, fun e => h ((hJE y hy).trans e)⟩`.

Take `⟨c, hc, -, H⟩` from `twTrace _ _ _ _ V m _ _ _ U S y hy (hfd _ (pow_pos hy _))`. Use `⟨c, hc, fun B hB1 hB2 => ?_⟩` and prove the remaining obligations. Establish `hnm : ∀ j, j ≠ 0 → ∀ p, (w p j).1 ∉ T.marked` using `fun j hj p h => hj (place_inj w ((hmk p _ h (under_of_over _)).trans (congrArg Subtype.val (hw0 p)).symm)).2`. Use `H 0 B (fun j hj v => DFunLike.congr_fun ((hOc B j fun g => hB1 _).mul_right (GA_commute μ B (by rintro _ ⟨p, rfl⟩; exact hB2 _ (hnm j hj p)))).eq v) fun j hj => gen_int μ s w j B (fun g => hB1 _) fun p => hB2 _ (hnm j hj p)` as an intermediate fact. Rewrite `this` using `[hU]`.

Conclude with `(congrArg (trOn · (B ∘L θ.U)) (hPE _ (pow_pos hy _))).symm.trans (this.trans (congrArg (fun X => c * trOn X B) (hJE y hy)))`.
-/
theorem UpperTheory.ConvolutionTheory.L1.twistY :
    UpperTheory.ConvolutionTheory.L1.TwistY := by
  intro F E _ _ _ _ _ _ σ hσ m n hm hn μ _ θ hθ D s hs hposition νE _ νF _ b a aE aF hA q w₀ hq T V hV hVU hrk
  let P : Finset (Pl F) := insert q T.sp
  have hsp : ∀ p : P, GM.Split E p.1 := fun p => by
    rcases Finset.mem_insert.1 p.2 with h | h
    · exact h ▸ hq
    · exact (Finset.mem_filter.1 h).2
  have hmk : ∀ p : P, ∃ u : PlacesOver E p.1, ∀ x ∈ T.marked, x.under (𝓞 F) = p.1 → x = u.1 := fun p => by
    obtain ⟨p, hp⟩ := p
    by_cases e : p = q
    · subst e
      refine ⟨w₀, ?_⟩
      rintro x (rfl | ⟨v, hv, rfl⟩) hx
      · rfl
      · rw [under_of_over] at hx
        obtain rfl : v = p := hx
        exact absurd (Finset.mem_filter.1 hv).1 T.q_not
    · refine ⟨T.mk' p, ?_⟩
      rintro x (rfl | ⟨v, hv, rfl⟩) hx
      · rw [under_of_over] at hx
        exact absurd hx.symm e
      · rw [under_of_over] at hx
        subst hx
        rfl
  choose mk hmk using hmk
  choose Df w hw0 hw using fun p : P => finSplit F E σ hσ m hm p.1 (mk p) (hsp p)
  obtain ⟨U, hU, -, -⟩ := twistUnitary E n μ θ
  have hU' : ∀ v, U v = θ.U v := fun v => DFunLike.congr_fun hU v
  obtain ⟨tp1, tp2, tp3⟩ := twistPerm F E σ hσ m n μ θ hθ
  obtain ⟨-, ag2, ag3, -⟩ := archBasic F E σ m D n
  have hsurj : ∀ (p : P) i, Function.Surjective (mapGL n (completionMap p.1 (w p i).1)) := fun p i y => by
    obtain ⟨⟨e, he⟩, -⟩ := splitLoc F E p.1 (w p i) (hsp p _) n
    exact ⟨e.symm y, by rw [← he, e.apply_symm_apply]⟩
  let R : Fin (m + 1) → Set (Pl E) := fun i => Set.range fun p : P => (w p i).1
  let On : Set (Pl E) := {u | u.under (𝓞 F) ∈ (P : Set (Pl F))}
  have hOn : ∀ u ∈ On, ∃ p i, (w p i).1 = u := fun u hu =>
    ⟨⟨_, hu⟩, (w ⟨_, hu⟩).symm ⟨u, ⟨rfl⟩⟩, by rw [Equiv.apply_symm_apply]⟩
  have hOn' : ∀ p i, (w p i).1 ∈ On := fun p i => by
    show _ ∈ (P : Set (Pl F))
    rw [under_of_over]
    exact p.2
  have hRU : ⋃ i, R i = On := by
    ext u
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨i, p, e⟩ => e ▸ hOn' p i, fun h => by obtain ⟨p, i, e⟩ := hOn u h; exact ⟨i, p, e⟩⟩
  have hRd : ∀ i j, i ≠ j → Disjoint (R i) (R j) := fun i j hij => Set.disjoint_left.2 (by
    rintro _ ⟨p, rfl⟩ ⟨p', e⟩
    exact hij (place_inj w e).2.symm)
  have hRO : ∀ i, Disjoint (R i) Onᶜ := fun i => Set.disjoint_left.2 (by
    rintro _ ⟨p, rfl⟩ h
    exact h (hOn' p i))
  let O : Fin (m + 1) → LL μ →L[ℂ] LL μ := fun i => OComponent μ (s i) (hs i) νF a
  let Q : Set (Pl E) → LL μ →L[ℂ] LL μ := fun A => prj (GA μ T.J T.χ A)
  have hss : ∀ i j, i ≠ j → ∀ g h, Commute (s i g) (s j h) := fun i j hij g h => by
    rw [hposition, hposition]
    show _ * _ = _ * _
    rw [← ag3, ← ag3]
    exact congrArg _ (Pi.mulSingle_commute (f := fun _ : Fin (m + 1) => archGroup F n) hij g h).eq
  have hOc : ∀ (B : LL μ →L[ℂ] LL μ) i, (∀ g, Commute B (rightRegularRep (rationalGLOne E n) μ (archP E n (s i g)))) →
      Commute B (O i) := fun B i h => ContinuousLinearMap.ext fun v =>
    operatorAt_int μ (hs i) (hs i) νF a B (fun x u => DFunLike.congr_fun (h x).eq u) v
  have hrep : ∀ x y : normOneGL E n, Commute x y →
      Commute (rightRegularRep (rationalGLOne E n) μ x) (rightRegularRep (rationalGLOne E n) μ y) := fun x y h =>
    ContinuousLinearMap.ext fun v => by
      simp only [ContinuousLinearMap.mul_apply]
      rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, h.eq]
  have hQO : ∀ A i, Commute (Q A) (O i) := fun A i => hOc _ i fun g => (GA_arch μ A _).symm
  have hOa : ∀ i j, i ≠ j → ∀ g, Commute (O i) (rightRegularRep (rationalGLOne E n) μ (archP E n (s j g))) :=
    fun i j hij g => (hOc _ i fun x => hrep _ _ ((hss j i hij.symm g x).map _)).symm
  have hOO : ∀ i j, Commute (O i) (O j) := fun i j => by
    by_cases e : i = j
    · rw [e]
    · exact hOc _ j (hOa i j e)
  have hOr : ∀ i u g, Commute (O i) (rhoL μ u g) := fun i u g => (hOc _ i fun x => (hrep _ _ (arch_fin _ _)).symm).symm
  have hOV : ∀ i, ∀ v ∈ V, O i v ∈ V := fun i v hv => by
    have h := hOc (prj V) i fun g => ContinuousLinearMap.ext fun y => inv_commute _ hV.closed hV.inv _ y
    rw [← prj_self hv, ← ContinuousLinearMap.mul_apply, ← h.eq]
    exact prj_mem hV.closed _
  have hQQ : ∀ i j, Commute (Q (R i)) (Q (R j)) := fun i j => by
    by_cases e : i = j
    · rw [e]
    · exact GA_GA μ (hRd i j e)
  have hco : ∀ u, CO (T.J u) ∧ IsChr (T.J u) (T.χ u) := fun u => ⟨T.co u, T.chr u⟩
  have hcof : ∀ᶠ u in Filter.cofinite, T.J u = GLnLocal.integralGL (u.adicCompletion E) n ∧ T.χ u = 1 := by
    refine Filter.eventually_cofinite.2 (((insert q T.S).finite_toSet.biUnion fun v _ => finite_over (E := E) v).subset fun u hu => ?_)
    by_contra h
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, exists_eq_right', Finset.coe_insert, Set.mem_insert_iff,
      Finset.mem_coe, not_or] at h
    exact hu (T.off u h.2 h.1)
  have hcomm : ∀ i j, i ≠ j → ∀ g h, Commute (FreeGroup.lift (gen s w i) g) (FreeGroup.lift (gen s w j) h) :=
    fun i j hij => lift_commute _ _ fun x y => by
      rcases x with g | ⟨p, g⟩ <;> rcases y with g' | ⟨p', g'⟩
      · exact (hss i j hij g g').map _
      · exact arch_fin _ _
      · exact (arch_fin _ _).symm
      · exact Commute.map ((UpperTheory.ConvolutionTheory.Tf.locEmb E n _).2.2.2.1 _ (fun e => hij (place_inj w e).2.symm) _ _) _
  have hUQ : ∀ i v, U (Q (R (i + 1)) v) = Q (R i) (U v) := fun i => by
    refine prj_equiv (GA_closed μ _) (GA_closed μ _) U fun v => ?_
    have h1 : ∀ j y, y ∈ GA μ T.J T.χ (R j) ↔ ∀ p : P, ∀ g ∈ (T.J (w p j).1).comap (mapGL n (completionMap p.1 (w p j).1)),
        rhoL μ (w p j).1 (mapGL n (completionMap p.1 (w p j).1) g) y = y := fun j y => by
      rw [mem_GA]
      constructor
      · intro h p g hg
        rw [h _ ⟨p, rfl⟩ _ hg, T.triv p.1 (hsp p) (w p j), Pi.one_apply, one_smul]
      · rintro h _ ⟨p, rfl⟩ x hx
        obtain ⟨g, rfl⟩ := hsurj p j x
        rw [h p g hx, T.triv p.1 (hsp p) (w p j), Pi.one_apply, one_smul]
    rw [h1, h1]
    refine forall_congr' fun p => ?_
    rw [lev_step T p.1 (Df p) (w p) (hw p) i]
    refine forall₂_congr fun g _ => ?_
    rw [hU', ← tp2 p.1 (Df p) (w p) (hw p) i g v, ← hU', ← hU']
    exact U.injective.eq_iff
  have S : Slots (rightRegularRep (rationalGLOne E n) μ) V m (fun i => FreeGroup.lift (gen s w i)) (Q Onᶜ)
      (fun i => O i * Q (R i)) U :=
    { summand := ⟨le_top, hV.closed, hV.inv, hV.ne_bot, hV.irred⟩
      ι_comm := hcomm
      rest := fun γ => by
        obtain ⟨A, h, rfl⟩ := MultiplicityOne.exists_archProj_mul_finProj γ
        have hfin : On.Finite := (P.finite_toSet.biUnion fun v _ => finite_over (E := E) v).subset fun u hu =>
          Set.mem_biUnion hu rfl
        obtain ⟨x, hx, h', e, h1⟩ := split_fin (prodM _ hcomm) hfin.toFinset (fun u hu y => by
          obtain ⟨p, i, rfl⟩ := hOn u (hfin.mem_toFinset.1 hu)
          obtain ⟨g, rfl⟩ := hsurj p i y
          have := mem_prodM _ hcomm i (FreeGroup.of (.inr ⟨p, g⟩))
          rwa [FreeGroup.lift_apply_of] at this) h
        have ha : archP E n ⟨A, Subgroup.mem_top A⟩ ∈ prodM _ hcomm := by
          rw [← ag2 ⟨A, Subgroup.mem_top A⟩, ← ofFn_mulSingle fun i => compA D n i _]
          have := map_list_prod ((archP E n).comp (MonoidHom.mk' (glueA D n) ag3))
            (List.ofFn fun i => (Pi.mulSingle i (compA D n i ⟨A, Subgroup.mem_top A⟩) : Fin (m + 1) → archGroup F n))
          refine (this ▸ Submonoid.list_prod_mem _ fun y hy => ?_ :
            ((archP E n).comp (MonoidHom.mk' (glueA D n) ag3)) _ ∈ _)
          rw [List.map_ofFn] at hy
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hy
          have := mem_prodM _ hcomm i (FreeGroup.of (.inl (compA D n i ⟨A, Subgroup.mem_top A⟩)))
          rw [FreeGroup.lift_apply_of, gen, hposition] at this
          exact this
        obtain ⟨g, hg⟩ := Submonoid.mul_mem _ ha hx
        obtain ⟨c, hc⟩ := restScalar E n μ V hV T.J T.χ hco hcof On (fun u hu => by
          by_cases hS : u.under (𝓞 F) ∈ T.S
          · exact hrk _ hS (fun h => hu (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hS, h⟩))) ⟨u, ⟨rfl⟩⟩
          · obtain ⟨e1, e2⟩ := T.off u hS fun h => hu (h ▸ Finset.mem_insert_self _ _ : _ ∈ P)
            rw [e1, e2]
            exact sphRank E n μ V hV u) h' fun u hu => h1 u (hfin.mem_toFinset.2 hu)
        refine ⟨g, _, c, ?_, fun v hv => hc _ ⟨GA_mem μ hV _ hv, prj_mem (GA_closed μ _) v⟩⟩
        rw [← hg, e, mul_assoc]
        rfl
      E_sa := (prj_star _).isSelfAdjoint
      E_idem := fun v => prj_self (prj_mem (GA_closed μ _) v)
      E_mem := fun v hv => GA_mem μ hV _ hv
      E_ι := fun i => gen_int μ s w i _ (fun g => (GA_arch μ _ _).symm)
        fun p g => (GA_rhoL μ (Set.notMem_compl_iff.2 (hOn' p i)) g).symm
      A_pos := fun i => pos_mul (sqOp F n νF b a aF m hA.sq hA.pow hA.norm _ _).2.1 (hQO _ i).symm
      A_mem := fun i v hv => hOV i _ (GA_mem μ hV _ hv)
      A_E := fun i v => DFunLike.congr_fun ((hQO _ i).symm.mul_left (GA_GA μ (hRO i))).eq v
      A_A := fun i j v => DFunLike.congr_fun
        (((hOO i j).mul_left (hQO _ j)).mul_right ((hQO _ i).symm.mul_left (hQQ i j))).eq v
      A_ι := fun i j hij => gen_int μ s w j _ (fun g => (hOa i j hij g).mul_left (GA_arch μ _ _).symm)
        fun p g => (hOr i _ g).mul_left (GA_rhoL μ (Set.disjoint_right.1 (hRd i j hij) ⟨p, rfl⟩) g).symm
      U_mem := by
        rw [← hVU]
        congr 1
        exact LinearMap.ext hU'
      U_E := fun v => by
        rw [hU', hU']
        exact DFunLike.congr_fun (tp3 q w₀ T P).eq v
      U_A := fun i v => by
        show U (O (i + 1) (Q (R (i + 1)) v)) = O i (Q (R i) (U v))
        rw [← hUQ, hU', hU']
        exact operatorAt_int μ (hs _) (hs _) νF a θ.U (tp1 D s hposition i) _
      U_ι := fun i => lift_int _ U _ _ fun x v => by
        rw [hU', hU']
        rcases x with g | ⟨p, g⟩
        · exact tp1 D s hposition i g v
        · exact tp2 p.1 (Df p) (w p) (hw p) i g v }
  have hOi : Oinf μ νE aE = (List.ofFn O).prod := tensOp F E σ m D n νE νF hA.meas s hs hposition (LL μ) _ (fun _ => a) aE hA.tens
  have hty : T.typed μ = GA μ T.J T.χ Set.univ := by simp only [GA, Ty.typed, Set.mem_univ, iInf_true]
  obtain ⟨hPE, hJE, hcpt, hne⟩ := fin_abs (W := fun i => GA μ T.J T.χ (R i)) (Ty := T.typed μ) hV.closed
    (GA_closed μ (J := T.J) (χ := T.χ) Onᶜ) (GA_closed μ (J := T.J) (χ := T.χ) On) (fun i => GA_closed μ _)
    (by rw [← GA_union, Set.union_compl_self, hty]) (by rw [← hRU]; exact iInf_iUnion _ _) hV.le hOi
    (by rw [← hRU]; exact GA_prod μ _ R hRd) (fun i j => hQO _ j) (hQO _) (GA_GA μ disjoint_compl_right)
    (by rw [hty]; exact compact_typed μ hn νE hco hcof aE)
  obtain ⟨hfd, hex⟩ := jointEx _ _ _ _ V m _ _ _ U S hcpt
  refine ⟨fun ⟨v, hv, h0⟩ => ?_, fun y hy => ?_⟩
  · obtain ⟨y, hy, h⟩ := hex (hne v hv h0)
    exact ⟨y, hy, fun e => h ((hJE y hy).trans e)⟩
  · obtain ⟨c, hc, -, H⟩ := twTrace _ _ _ _ V m _ _ _ U S y hy (hfd _ (pow_pos hy _))
    refine ⟨c, hc, fun B hB1 hB2 => ?_⟩
    have hnm : ∀ j, j ≠ 0 → ∀ p, (w p j).1 ∉ T.marked := fun j hj p h =>
      hj (place_inj w ((hmk p _ h (under_of_over _)).trans (congrArg Subtype.val (hw0 p)).symm)).2
    have := H 0 B (fun j hj v => DFunLike.congr_fun ((hOc B j fun g => hB1 _).mul_right
        (GA_commute μ B (by rintro _ ⟨p, rfl⟩; exact hB2 _ (hnm j hj p)))).eq v)
      fun j hj => gen_int μ s w j B (fun g => hB1 _) fun p => hB2 _ (hnm j hj p)
    rw [hU] at this
    exact (congrArg (trOn · (B ∘L θ.U)) (hPE _ (pow_pos hy _))).symm.trans
      (this.trans (congrArg (fun X => c * trOn X B) (hJE y hy)))
