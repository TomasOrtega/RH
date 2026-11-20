import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AutomorphicArithmetic.DivisorFrames.ExistsAdaptedFlagCharts
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

section SlopeTestRemainingChoices

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

/- English proof (translation)
Use `isFrame_of_forall_exists fun V h x hx => ?_` and prove the remaining obligations. Take `⟨W, a, -, hxW, hle, ha⟩` from `hA.exists_affine hx`. Use `⟨W, hle, hxW, ?_⟩` and prove the remaining obligations. Set `p : Γ(A, W) →ₗ[Γ(X, W)] (Fin k → Γ(X, W))` to `LinearMap.funLeft _ _ g ∘ₗ (he.basis (hle.trans h)).equivFun.toLinearMap ∘ₗ appLinear u W`. Establish `hp : p ∘ₗ (Fintype.linearCombination Γ(X, W) fun i => resM A (hle.trans h) (s i)) = LinearMap.id`.

Use `(Pi.basisFun _ _).ext fun j => ?_` and prove the remaining obligations. Establish `h₁ : appLinear u W (resM A (hle.trans h) (s j)) = he.basis (hle.trans h) (g j)`. Rewrite using `[appLinear_apply, app_resM, hs, IsFrame.basis_apply]`. Use function extensionality and compare the values at `i`. Simplify using `[p, h₁, Finsupp.single_apply, Pi.single_apply, hg.eq_iff, eq_comm, -IsFrame.basis_apply]`.

Establish `hp' (c) : p (Fintype.linearCombination Γ(X, W) (fun i => resM A (hle.trans h) (s i)) c) = c` using `LinearMap.congr_fun hp c`. Establish `hsurj : Function.Surjective p` using `fun c => ⟨_, hp' c⟩`. Establish `hinj : Function.Injective p`. Use `OrzechProperty.injective_of_surjective_endomorphism (p ∘ₗ (ha.basis le_rfl).equivFun.symm.toLinearMap) (hsurj.comp (ha.basis le_rfl).equivFun.symm.surjective)` as an intermediate fact. Conclude with `(Function.Injective.of_comp_iff' _ (ha.basis le_rfl).equivFun.symm.bijective).1 this`.

Conclude with `⟨fun c c' hc => by rw [← hp' c, hc, hp'], fun y => ⟨p y, hinj (hp' _)⟩⟩`.
-/
private theorem UpperTheory.subbundle_frame_injective_metric {X : Scheme.{0}} {A M : X.Modules} {k r : ℕ} (hA : IsVB A k) (u : A ⟶ M)
    {U : X.Opens} {e : Fin r → Γ(M, U)} (he : IsFrame e) (g : Fin k → Fin r) (hg : Function.Injective g)
    (s : Fin k → Γ(A, U)) (hs : ∀ j, u.app U (s j) = e (g j)) : IsFrame s := by
  refine isFrame_of_forall_exists fun V h x hx => ?_
  obtain ⟨W, a, -, hxW, hle, ha⟩ := hA.exists_affine hx
  refine ⟨W, hle, hxW, ?_⟩
  let p : Γ(A, W) →ₗ[Γ(X, W)] (Fin k → Γ(X, W)) :=
    LinearMap.funLeft _ _ g ∘ₗ (he.basis (hle.trans h)).equivFun.toLinearMap ∘ₗ appLinear u W
  have hp : p ∘ₗ (Fintype.linearCombination Γ(X, W) fun i => resM A (hle.trans h) (s i)) = LinearMap.id := by
    refine (Pi.basisFun _ _).ext fun j => ?_
    have h₁ : appLinear u W (resM A (hle.trans h) (s j)) = he.basis (hle.trans h) (g j) := by
      rw [appLinear_apply, app_resM, hs, IsFrame.basis_apply]
    funext i
    simp [p, h₁, Finsupp.single_apply, Pi.single_apply, hg.eq_iff, eq_comm, -IsFrame.basis_apply]
  have hp' (c) : p (Fintype.linearCombination Γ(X, W) (fun i => resM A (hle.trans h) (s i)) c) = c :=
    LinearMap.congr_fun hp c
  have hsurj : Function.Surjective p := fun c => ⟨_, hp' c⟩
  have hinj : Function.Injective p := by
    have := OrzechProperty.injective_of_surjective_endomorphism
      (p ∘ₗ (ha.basis le_rfl).equivFun.symm.toLinearMap) (hsurj.comp (ha.basis le_rfl).equivFun.symm.surjective)
    exact (Function.Injective.of_comp_iff' _ (ha.basis le_rfl).equivFun.symm.bijective).1 this
  exact ⟨fun c c' hc => by rw [← hp' c, hc, hp'], fun y => ⟨p y, hinj (hp' _)⟩⟩

/- English proof (translation)
Proceed by induction on `b using Fin.induction with`. Consider the case `zero`. Take `rfl : a = 0` from `Fin.le_zero_iff.1 h`. Conclude with `⟨𝟙 _, Category.id_comp _⟩`. Consider the case `succ b ih`.

Break down `h.eq_or_lt with rfl | h'` into its components or cases. Conclude with `⟨𝟙 _, Category.id_comp _⟩`. Take `⟨φ, hφ⟩` from `ih (Fin.le_castSucc_iff.2 h')`. Conclude with `⟨φ ≫ fl.step b, by rw [Category.assoc, fl.step_ι, hφ]⟩`.
-/
private theorem UpperTheory.flag_nested_metric {X : Scheme.{0}} {M : X.Modules} {r : ℕ} (fl : Vert.Flag M r) (a b : Fin (r + 1))
    (h : a ≤ b) : ∃ φ : fl.F a ⟶ fl.F b, φ ≫ fl.ι b = fl.ι a := by
  induction b using Fin.induction with
  | zero =>
    obtain rfl : a = 0 := Fin.le_zero_iff.1 h
    exact ⟨𝟙 _, Category.id_comp _⟩
  | succ b ih =>
    rcases h.eq_or_lt with rfl | h'
    · exact ⟨𝟙 _, Category.id_comp _⟩
    · obtain ⟨φ, hφ⟩ := ih (Fin.le_castSucc_iff.2 h')
      exact ⟨φ ≫ fl.step b, by rw [Category.assoc, fl.step_ι, hφ]⟩

end SlopeTestRemainingChoices

/- English proof (translation)
Take `⟨_⟩` from `((isUnit_iff_isUnit_det _).2 hK).nonempty_invertible`. Use `conv_lhs => rw [← fromBlocks_toBlocks K]`. Rewrite using `[det_fromBlocks₁₁, invOf_eq_nonsing_inv]`. Both sides reduce to the same expression.
-/
private theorem UpperTheory.det_block_schur_quotient {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    (K : Matrix (m ⊕ l) (m ⊕ l) ℂ) (hK : IsUnit K.toBlocks₁₁.det) :
    K.det = K.toBlocks₁₁.det * (HermFrame.quotGram K).det := by
  obtain ⟨_⟩ := ((isUnit_iff_isUnit_det _).2 hK).nonempty_invertible
  conv_lhs => rw [← fromBlocks_toBlocks K]
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  rfl

/- English proof (translation)
Introduce `k _ X p M r h H fl ch hch i t hti ht σ z hz`. Establish `hi : (i : ℕ) ≤ r` using `i.2.le`. Establish `hi' : (i : ℕ) + 1 ≤ r` using `i.2`. Establish `key (j : Fin (i : ℕ)) : ∃ s : Γ(fl.F i.castSucc, ch.U), (fl.ι i.castSucc).app ch.U s = ch.e (j.castLE hi)`. Take `⟨s₀, hs₀⟩` from `hch (j.castLE hi)`.

Take `⟨φ, hφ⟩` from `UpperTheory.flag_nested_metric fl (j.castLE hi).succ i.castSucc j.2`. Conclude with `⟨φ.app ch.U s₀, by rw [QCoh.app_app, hφ, hs₀]⟩`. Use `choose s hs using key`. Establish `hf : IsFrame s` using `UpperTheory.subbundle_frame_injective_metric (fl.isVB i.castSucc) (fl.ι i.castSucc) ch.isFrame _ (Fin.castLE_injective hi) s hs`. Set `a : VBExt.AdaptedChart (VMetric.stepSeq fl i) i 1` to `{ U := ch.U, e := s, t := fun _ => t, he := hf, ht := ht }`.

Establish `hfr (j : Fin i ⊕ Fin 1) : (fl.ι i.succ).app ch.U (a.frame j) = ch.e ((finSumFinEquiv j).castLE hi')`. Break down `j with j | j` into its components or cases. Use `Eq.trans ?_ (hs j)` and prove the remaining obligations. Rewrite using `[← fl.step_ι]`. Both sides reduce to the same expression.

Use `hti.trans (congrArg ch.e (Fin.ext ?_))` and prove the remaining obligations. Rewrite using `[Subsingleton.elim j 0]`. Both sides reduce to the same expression. Establish `hg : ((h.stepMet fl i).met σ).gram a.frame z = (((h.met σ).G ch z).submatrix (Fin.castLE hi') (Fin.castLE hi')).submatrix finSumFinEquiv finSumFinEquiv`. Use extensionality with `b c`.

Use `((h.met σ).form_restrict (fl.isSubbundle i.succ) (fl.isVB i.succ) (a.frame b) (a.frame c) hz).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ ((h.met σ).form_frame ch hz _ _)` and prove the remaining obligations. Conclude with `congrArg₂ (fun u v => (h.met σ).form u v z) (hfr b) (hfr c)`. Establish `hq` using `((h.stepMet fl i).met σ).quot_G (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) a hz`. Establish `hpos` using `HermFrame.det_re_pos (((h.grMet fl i).met σ).posDef a.quot z hz)`.

Establish `hG` using `(h.met σ).posDef ch z hz`. Establish `h₀` using `(GradedNorm.lminor_pos hG i.castSucc).ne'`. Establish `h₁ : (((h.stepMet fl i).met σ).gram a.frame z).toBlocks₁₁.det = ReciprocityTheory.ChartRestriction.G.FD.lminor ((h.met σ).G ch z) i.castSucc`. Rewrite using `[hg]`. Both sides reduce to the same expression.

Establish `h₂ : (((h.stepMet fl i).met σ).gram a.frame z).det = ReciprocityTheory.ChartRestriction.G.FD.lminor ((h.met σ).G ch z) i.succ`. Rewrite using `[hg, det_submatrix_equiv_self]`. Both sides reduce to the same expression. Establish `h₃` using `UpperTheory.det_block_schur_quotient (((h.stepMet fl i).met σ).gram a.frame z) (h₁ ▸ h₀.isUnit)`. Rewrite `h₃` using `[h₁, h₂, ← hq]`.

Express the relevant statement in the definitionally equal form `Real.exp (- -Real.log (((h.grMet fl i).met σ).G a.quot z).det.re) = _`. Rewrite using `[neg_neg, Real.exp_log hpos, GradedNorm.grSq, h₃, mul_div_cancel_left₀ _ h₀]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.flag_line_metric_exp_bound :
    ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (M : X.Modules) (r : ℕ) (h : VMetric p M r) (H : h.IsCInf) (fl : Vert.Flag M r) (ch : Chart M r), IsAdapted fl ch → ∀ (i : Fin r) (t : Γ(fl.F i.succ, ch.U)), (fl.ι i.succ).app ch.U t = ch.e i → ∀ (ht : IsFrame fun _ : Fin 1 => (fl.π i).app ch.U t) (σ : k →+* ℂ) (z : CxPts p σ), z ∈ CxPts.ptsIn p σ ch.U → Real.exp (-((VMetric.grLB fl i H).φ σ).φ (⟨ch.U, _, ht⟩ : Chart (fl.gr i) 1) z) = GlobalTheory.GradedNorm.grSq ((h.met σ).G ch z) i := by
  intro k _ X p M r h H fl ch hch i t hti ht σ z hz
  have hi : (i : ℕ) ≤ r := i.2.le
  have hi' : (i : ℕ) + 1 ≤ r := i.2
  have key (j : Fin (i : ℕ)) : ∃ s : Γ(fl.F i.castSucc, ch.U), (fl.ι i.castSucc).app ch.U s = ch.e (j.castLE hi) := by
    obtain ⟨s₀, hs₀⟩ := hch (j.castLE hi)
    obtain ⟨φ, hφ⟩ := UpperTheory.flag_nested_metric fl (j.castLE hi).succ i.castSucc j.2
    exact ⟨φ.app ch.U s₀, by rw [QCoh.app_app, hφ, hs₀]⟩
  choose s hs using key
  have hf : IsFrame s :=
    UpperTheory.subbundle_frame_injective_metric (fl.isVB i.castSucc) (fl.ι i.castSucc) ch.isFrame _ (Fin.castLE_injective hi) s hs
  let a : VBExt.AdaptedChart (VMetric.stepSeq fl i) i 1 :=
    { U := ch.U, e := s, t := fun _ => t, he := hf, ht := ht }
  have hfr (j : Fin i ⊕ Fin 1) :
      (fl.ι i.succ).app ch.U (a.frame j) = ch.e ((finSumFinEquiv j).castLE hi') := by
    rcases j with j | j
    · refine Eq.trans ?_ (hs j)
      rw [← fl.step_ι]
      rfl
    · refine hti.trans (congrArg ch.e (Fin.ext ?_))
      rw [Subsingleton.elim j 0]
      rfl
  have hg : ((h.stepMet fl i).met σ).gram a.frame z =
      (((h.met σ).G ch z).submatrix (Fin.castLE hi') (Fin.castLE hi')).submatrix finSumFinEquiv finSumFinEquiv := by
    ext b c
    refine ((h.met σ).form_restrict (fl.isSubbundle i.succ) (fl.isVB i.succ) (a.frame b) (a.frame c) hz).trans ?_
    refine Eq.trans ?_ ((h.met σ).form_frame ch hz _ _)
    exact congrArg₂ (fun u v => (h.met σ).form u v z) (hfr b) (hfr c)
  have hq := ((h.stepMet fl i).met σ).quot_G (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc)
    (fl.isVB_gr i) a hz
  have hpos := HermFrame.det_re_pos (((h.grMet fl i).met σ).posDef a.quot z hz)
  have hG := (h.met σ).posDef ch z hz
  have h₀ := (GradedNorm.lminor_pos hG i.castSucc).ne'
  have h₁ : (((h.stepMet fl i).met σ).gram a.frame z).toBlocks₁₁.det =
      ReciprocityTheory.ChartRestriction.G.FD.lminor ((h.met σ).G ch z) i.castSucc := by
    rw [hg]
    rfl
  have h₂ : (((h.stepMet fl i).met σ).gram a.frame z).det =
      ReciprocityTheory.ChartRestriction.G.FD.lminor ((h.met σ).G ch z) i.succ := by
    rw [hg, det_submatrix_equiv_self]
    rfl
  have h₃ := UpperTheory.det_block_schur_quotient (((h.stepMet fl i).met σ).gram a.frame z) (h₁ ▸ h₀.isUnit)
  rw [h₁, h₂, ← hq] at h₃
  change Real.exp (- -Real.log (((h.grMet fl i).met σ).G a.quot z).det.re) = _
  rw [neg_neg, Real.exp_log hpos, GradedNorm.grSq, h₃, mul_div_cancel_left₀ _ h₀]
  rfl
