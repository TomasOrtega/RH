import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.BlkOneMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintSph
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CvHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UnitHecke
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetSumCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemULOfSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralLeviConstantTerm

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

/- English proof (translation)
Use `set Cf : Finset β := hC.toFinset with hCf`. Set `Af : β → Finset γ` to `fun c => (hA c).toFinset`. Establish `hin : ∀ X : α, ∑ᶠ c, ∑ᶠ x, u c x * v c x X = ∑ p ∈ Cf.sigma Af, u p.1 p.2 * v p.1 p.2 X`. Introduce `X`. Rewrite using `[← Finset.sum_sigma' Cf Af (fun c x => u c x * v c x X)]`.

Rewrite using `[finsum_eq_sum_of_support_subset (s := Cf)]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `finsum_eq_sum_of_support_subset _ ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Function.mem_support] at hx`.

Simplify using `only [Af, Set.Finite.coe_toFinset, Function.mem_support]`. Conclude with `left_ne_zero_of_mul hx`. Introduce `c hc`. Simplify using `only [Function.mem_support] at hc`. Simplify using `only [hCf, Set.Finite.coe_toFinset]`.

Assume the negation of the conclusion as `hcs`. Conclude with `hc (by simp [hCs c hcs])`. Repeatedly rewrite using `[hin]`. Establish `hfs : ∑ᶠ X : α, ∑ p ∈ Cf.sigma Af, u p.1 p.2 * v p.1 p.2 X = ∑ p ∈ Cf.sigma Af, ∑ᶠ X : α, u p.1 p.2 * v p.1 p.2 X`. Use `finsum_sum_comm (Cf.sigma Af) (fun (X : α) (p : (_ : β) × γ) => u p.1 p.2 * v p.1 p.2 X) fun p _ => ?_` and prove the remaining obligations.

Use `(hv p.1 p.2).subset fun X hX => ?_` and prove the remaining obligations. Simplify using `only [Function.mem_support] at hX ⊢`. Conclude with `right_ne_zero_of_mul hX`. Rewrite using `[hfs]`. Establish `hstep : ∀ p : (_ : β) × γ, ∑ᶠ X, u p.1 p.2 * v p.1 p.2 X = u p.1 p.2 * r p.1`.

Introduce `p`. Use `smul_finsum (u p.1 p.2) (v p.1 p.2)` as an intermediate fact. Simplify using `only [smul_eq_mul] at this`. Rewrite using `[← this, hr]`. Repeatedly rewrite using `[hstep]`.

Rewrite using `[← Finset.sum_sigma' Cf Af (fun c x => u c x * r c)]`. Rewrite using `[finsum_eq_sum_of_support_subset (s := Cf)]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul]`. Use `congr 1`.

Conclude with `(finsum_eq_sum_of_support_subset (s := Af c) (u c) (by simp [Af])).symm`. Introduce `c hc`. Simplify using `only [Function.mem_support] at hc`. Simplify using `only [hCf, Set.Finite.coe_toFinset]`. Assume the negation of the conclusion as `hcs`.

Use `hc ?_` and prove the remaining obligations. Establish `: (fun x => u c x) = fun _ => 0` using `funext (hCs c hcs)`. Simplify using `[this]`.
-/
private theorem swap3 {α β γ : Type} (u : β → γ → ℂ) (v : β → γ → α → ℂ) (Cs : Set β) (hC : Cs.Finite)
    (hCs : ∀ c, c ∉ Cs → ∀ x, u c x = 0) (hA : ∀ c, (Function.support (u c)).Finite)
    (hv : ∀ c x, (Function.support (v c x)).Finite) (r : β → ℂ) (hr : ∀ c x, ∑ᶠ X, v c x X = r c) :
    ∑ᶠ X : α, ∑ᶠ c, ∑ᶠ x, u c x * v c x X = ∑ᶠ c, (∑ᶠ x, u c x) * r c := by
  set Cf : Finset β := hC.toFinset with hCf
  let Af : β → Finset γ := fun c => (hA c).toFinset
  have hin : ∀ X : α, ∑ᶠ c, ∑ᶠ x, u c x * v c x X = ∑ p ∈ Cf.sigma Af, u p.1 p.2 * v p.1 p.2 X := by
    intro X
    rw [← Finset.sum_sigma' Cf Af (fun c x => u c x * v c x X)]
    rw [finsum_eq_sum_of_support_subset (s := Cf)]
    · refine Finset.sum_congr rfl fun c _ => ?_
      refine finsum_eq_sum_of_support_subset _ ?_
      intro x hx
      simp only [Function.mem_support] at hx
      simp only [Af, Set.Finite.coe_toFinset, Function.mem_support]
      exact left_ne_zero_of_mul hx
    · intro c hc
      simp only [Function.mem_support] at hc
      simp only [hCf, Set.Finite.coe_toFinset]
      by_contra hcs
      exact hc (by simp [hCs c hcs])
  simp_rw [hin]
  have hfs : ∑ᶠ X : α, ∑ p ∈ Cf.sigma Af, u p.1 p.2 * v p.1 p.2 X =
      ∑ p ∈ Cf.sigma Af, ∑ᶠ X : α, u p.1 p.2 * v p.1 p.2 X := by
    refine finsum_sum_comm (Cf.sigma Af) (fun (X : α) (p : (_ : β) × γ) => u p.1 p.2 * v p.1 p.2 X) fun p _ => ?_
    refine (hv p.1 p.2).subset fun X hX => ?_
    simp only [Function.mem_support] at hX ⊢
    exact right_ne_zero_of_mul hX
  rw [hfs]
  · have hstep : ∀ p : (_ : β) × γ, ∑ᶠ X, u p.1 p.2 * v p.1 p.2 X = u p.1 p.2 * r p.1 := by
      intro p
      have := smul_finsum (u p.1 p.2) (v p.1 p.2)
      simp only [smul_eq_mul] at this
      rw [← this, hr]
    simp_rw [hstep]
    rw [← Finset.sum_sigma' Cf Af (fun c x => u c x * r c)]
    rw [finsum_eq_sum_of_support_subset (s := Cf)]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_mul]
      congr 1
      exact (finsum_eq_sum_of_support_subset (s := Af c) (u c) (by simp [Af])).symm
    · intro c hc
      simp only [Function.mem_support] at hc
      simp only [hCf, Set.Finite.coe_toFinset]
      by_contra hcs
      refine hc ?_
      have : (fun x => u c x) = fun _ => 0 := funext (hCs c hcs)
      simp [this]

section Tr

variable {N : Type} [CommGroup N] (L : Subgroup N)

/- English proof (translation)
Take `⟨⟨y, hy⟩, hy'⟩` from `QuotientGroup.mk_out_eq_mul L g`. Rewrite using `[hy']`. Conclude with `hφ g y hy`.
-/
private theorem out_val (φ : N → ℂ) (hφ : ∀ x, ∀ l ∈ L, φ (x * l) = φ x) (g : N) :
    φ (QuotientGroup.mk g : N ⧸ L).out = φ g := by
  obtain ⟨⟨y, hy⟩, hy'⟩ := QuotientGroup.mk_out_eq_mul L g
  rw [hy']
  exact hφ g y hy

/- English proof (translation)
Establish `e : ∀ x : N ⧸ L, φ (x.out * t) = φ (Equiv.mulRight (QuotientGroup.mk t : N ⧸ L) x).out`. Introduce `x`. Rewrite using `[← out_val L φ hφ (x.out * t)]`. Use `congr 2`. Simplify using the standard rewrite rules.

Repeatedly rewrite using `[e]`. Conclude with `finsum_comp_equiv (f := fun x : N ⧸ L => φ x.out) (Equiv.mulRight (QuotientGroup.mk t : N ⧸ L))`.
-/
private theorem sum_translate (φ : N → ℂ) (hφ : ∀ x, ∀ l ∈ L, φ (x * l) = φ x) (t : N) :
    ∑ᶠ x : N ⧸ L, φ (x.out * t) = ∑ᶠ x : N ⧸ L, φ x.out := by
  have e : ∀ x : N ⧸ L, φ (x.out * t) = φ (Equiv.mulRight (QuotientGroup.mk t : N ⧸ L) x).out := by
    intro x
    rw [← out_val L φ hφ (x.out * t)]
    congr 2
    simp
  simp_rw [e]
  exact finsum_comp_equiv (f := fun x : N ⧸ L => φ x.out) (Equiv.mulRight (QuotientGroup.mk t : N ⧸ L))

/- English proof (translation)
Use `(hf.preimage (Equiv.mulRight (QuotientGroup.mk t : N ⧸ L)).injective.injOn).subset fun x hx => ?_` and prove the remaining obligations. Simplify using `only [Function.mem_support, Set.mem_preimage] at hx ⊢`. Rewrite `hx` using `[← out_val L φ hφ (x.out * t)]`. Establish `: (QuotientGroup.mk (x.out * t) : N ⧸ L) = Equiv.mulRight (QuotientGroup.mk t : N ⧸ L) x` using `by simp`. Rewrite `hx` using `[this]`. Then use the resulting hypothesis.
-/
private theorem support_translate (φ : N → ℂ) (hφ : ∀ x, ∀ l ∈ L, φ (x * l) = φ x) (t : N)
    (hf : (Function.support fun x : N ⧸ L => φ x.out).Finite) :
    (Function.support fun x : N ⧸ L => φ (x.out * t)).Finite := by
  refine (hf.preimage (Equiv.mulRight (QuotientGroup.mk t : N ⧸ L)).injective.injOn).subset fun x hx => ?_
  simp only [Function.mem_support, Set.mem_preimage] at hx ⊢
  rw [← out_val L φ hφ (x.out * t)] at hx
  have : (QuotientGroup.mk (x.out * t) : N ⧸ L) = Equiv.mulRight (QuotientGroup.mk t : N ⧸ L) x := by simp
  rwa [this] at hx

end Tr

section Conc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

private def dl (w : Pl E) (m : GLw a w × GLw b w) : ℂ := absHalf w (m.1.val.det ^ b / m.2.val.det ^ a)

/- English proof (translation)
Unfold `dl`. Establish `h1` using `Matrix.GeneralLinearGroup.det_ne_zero m.1`. Establish `h2` using `Matrix.GeneralLinearGroup.det_ne_zero m.2`. Establish `h3` using `Matrix.GeneralLinearGroup.det_ne_zero m'.1`. Establish `h4` using `Matrix.GeneralLinearGroup.det_ne_zero m'.2`.

Rewrite using `[← GlobalTheory.LeviDesc.absHalf_mul E w _ _ (div_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ h2)) (div_ne_zero (pow_ne_zero _ h3) (pow_ne_zero _ h4))]`. Use `congr 1`. Simplify using `only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.det_mul, mul_pow]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem dl_mul (w : Pl E) (m m' : GLw a w × GLw b w) : dl w (m * m') = dl w m * dl w m' := by
  unfold dl
  have h1 := Matrix.GeneralLinearGroup.det_ne_zero m.1
  have h2 := Matrix.GeneralLinearGroup.det_ne_zero m.2
  have h3 := Matrix.GeneralLinearGroup.det_ne_zero m'.1
  have h4 := Matrix.GeneralLinearGroup.det_ne_zero m'.2
  rw [← GlobalTheory.LeviDesc.absHalf_mul E w _ _ (div_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ h2))
    (div_ne_zero (pow_ne_zero _ h3) (pow_ne_zero _ h4))]
  congr 1
  simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.det_mul, mul_pow]
  field_simp

private def Sm (h : a + b = n) (w : Pl E) (φ : GLw n w → ℂ) (m : GLw a w × GLw b w) : ℂ :=
  ∑ᶠ x : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w,
    φ (blk h w m (Multiplicative.toAdd x.out))

/- English proof (translation)
Establish `e` using `(GlobalTheory.CompanionTheory.LeviInt.comap_uN_and_map_sM E a b n h w).1`. Rewrite `hl` using `[← e]`. Conclude with `hl`.
-/
private theorem K_of_int (h : a + b = n) (w : Pl E)
    (l : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) (hl : l ∈ intMat a b w) :
    blk h w 1 (Multiplicative.toAdd l) ∈ KGL w n := by
  have e := (GlobalTheory.CompanionTheory.LeviInt.comap_uN_and_map_sM E a b n h w).1
  rw [← e] at hl
  exact hl

/- English proof (translation)
Rewrite using `[toAdd_mul, GlobalTheory.CompanionTheory.IntDec.blk_add]`. Conclude with `hφ _ (K_of_int h w l hl) _`.
-/
private theorem right_L (h : a + b = n) (w : Pl E) (φ : GLw n w → ℂ) (hφ : ∀ k ∈ KGL w n, ∀ x, φ (x * k) = φ x)
    (m : GLw a w × GLw b w) (x l : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))
    (hl : l ∈ intMat a b w) :
    φ (blk h w m (Multiplicative.toAdd (x * l))) = φ (blk h w m (Multiplicative.toAdd x)) := by
  rw [toAdd_mul, GlobalTheory.CompanionTheory.IntDec.blk_add]
  exact hφ _ (K_of_int h w l hl) _

/- English proof (translation)
Rewrite using `[inv_mul_eq_iff_eq_mul, GlobalTheory.LeviFubini.blk_mul_blk]`. Simplify using the standard rewrite rules.
-/
private theorem inv_blk (h : a + b = n) (w : Pl E) (c m : GLw a w × GLw b w)
    (Y X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w c Y)⁻¹ * blk h w m X =
      blk h w (c⁻¹ * m) (X + -(((c⁻¹ * m).1⁻¹).val * Y * (c⁻¹ * m).2.val)) := by
  rw [inv_mul_eq_iff_eq_mul, GlobalTheory.LeviFubini.blk_mul_blk]
  simp

/- English proof (translation)
Establish `hkN : GlobalTheory.BCT.CtLevel.dgM h w k ∈ KGL w n`. Rewrite using `[← GlobalTheory.CompanionTheory.IntDec.blk_zero_eq_dgM]`. Conclude with `(GlobalTheory.CompanionTheory.LeviInt.comap_uN_and_map_sM E a b n h w).2 (Subgroup.mem_map_of_mem _ hk)`. Conclude with `GlobalTheory.BCT.CtLevel.ct_inv h w (KGL w n) F (fun k hk x hx => mul_mem (mul_mem (inv_mem hk) hx) hk) (fun y hy x => hF.2 y hy x) k (Subgroup.mem_prod.1 hk).1 (Subgroup.mem_prod.1 hk).2 hkN m`.
-/
private theorem ct_bi (h : a + b = n) (w : Pl E) (F : GLw n w → ℂ) (hF : IsHecke (KGL w n) F)
    (k : GLw a w × GLw b w) (hk : k ∈ K2 a b w) (m : GLw a w × GLw b w) :
    ct h w F (k * m) = ct h w F m ∧ ct h w F (m * k) = ct h w F m := by
  have hkN : GlobalTheory.BCT.CtLevel.dgM h w k ∈ KGL w n := by
    rw [← GlobalTheory.CompanionTheory.IntDec.blk_zero_eq_dgM]
    exact (GlobalTheory.CompanionTheory.LeviInt.comap_uN_and_map_sM E a b n h w).2 (Subgroup.mem_map_of_mem _ hk)
  exact GlobalTheory.BCT.CtLevel.ct_inv h w (KGL w n) F
    (fun k hk x hx => mul_mem (mul_mem (inv_mem hk) hx) hk) (fun y hy x => hF.2 y hy x) k
    (Subgroup.mem_prod.1 hk).1 (Subgroup.mem_prod.1 hk).2 hkN m

end Conc

/- English proof (translation)
Introduce `E _ _ _ w n a b h f g hf hg`. Take `⟨-, -, hKo, hKc, -, -, -⟩` from `unitHecke E n a b w`. Establish `hfg : IsHecke (KGL w n) (cv (KGL w n) f g)` using `cvHecke _ (KGL w n) hKo hKc f g hf hg`. Establish `hct : ∀ φ, IsHecke (KGL w n) φ → ∀ m, ct h w φ m = dl w m * Sm h w φ m` using `fun φ hφ m => (ctSph E w n a b h φ hφ m).1`. Establish `hsup : ∀ φ : GLw n w → ℂ, IsHecke (KGL w n) φ → ∀ m : GLw a w × GLw b w, (Function.support fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w => φ (blk h w m (Multiplicative.toAdd q.out))).Finite` using `fun φ hφ m => (ctSph E w n a b h φ hφ m).2`.

Use function extensionality and compare the values at `m`. Establish `hR : cv (K2 a b w) (ct h w f) (ct h w g) m = ∑ᶠ c : (GLw a w × GLw b w) ⧸ K2 a b w, ct h w f c.out * ct h w g (c.out⁻¹ * m)`. Use `hintSph _ (K2 a b w) (fun z => ct h w f z * ct h w g (z⁻¹ * m)) fun k hk x => ?_` and prove the remaining obligations. Establish `e : (x * k)⁻¹ * m = k⁻¹ * (x⁻¹ * m)` using `by group`. Use `show ct h w f (x * k) * ct h w g ((x * k)⁻¹ * m) = ct h w f x * ct h w g (x⁻¹ * m)`.

Rewrite using `[e, (ct_bi h w f hf k hk x).2, (ct_bi h w g hg k⁻¹ (inv_mem hk) _).1]`. Establish `hinv : ∀ y, ∀ k ∈ KGL w n, ∀ x, f (x * k) * g ((x * k)⁻¹ * y) = f x * g (x⁻¹ * y)`. Introduce `y k hk x`. Establish `e : (x * k)⁻¹ * y = k⁻¹ * (x⁻¹ * y)` using `by group`. Rewrite using `[e, (hf.2 k hk x).2, (hg.2 k⁻¹ (inv_mem hk) _).1]`.

Establish `hcv : ∀ y, cv (KGL w n) f g y = ∑ᶠ c : (GLw a w × GLw b w) ⧸ (KGL w a).prod (KGL w b), ∑ᶠ x : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w, f (blk h w c.out (Multiplicative.toAdd x.out)) * g ((blk h w c.out (Multiplicative.toAdd x.out))⁻¹ * y)`. Introduce `y`. Establish `e1 : cv (KGL w n) f g y = ∑ᶠ p : GLw n w ⧸ KGL w n, f p.out * g (p.out⁻¹ * y)` using `hintSph _ (KGL w n) (fun z => f z * g (z⁻¹ * y)) fun k hk x => hinv y k hk x`. Rewrite using `[e1]`. Use `GlobalTheory.CompanionTheory.IntDec.iwasawa_sum h w (fun z => f z * g (z⁻¹ * y)) (fun k hk x => hinv y k hk x) ?_` and prove the remaining obligations.

Use `(GlobalTheory.CompanionTheory.IntDec.finite_mk_support (KGL w n) hKo f hf.1).subset fun p hp => ?_` and prove the remaining obligations. Conclude with `⟨p.out, left_ne_zero_of_mul hp, QuotientGroup.out_eq' p⟩`. Establish `hCs : {c : (GLw a w × GLw b w) ⧸ (KGL w a).prod (KGL w b) | ∃ Y, f (blk h w c.out Y) ≠ 0}.Finite`. Use `GlobalTheory.CompanionTheory.IntDec.finite_lev h w _ (GlobalTheory.CompanionTheory.IntDec.finite_mk_support (KGL w n) hKo f hf.1) _ ?_` and prove the remaining obligations. Introduce and unpack `c ⟨Y, hY⟩`.

Conclude with `⟨c.out, Y, QuotientGroup.out_eq' c, _, hY, rfl⟩`. Establish `hgR : ∀ k ∈ KGL w n, ∀ x, g (x * k) = g x` using `fun k hk x => (hg.2 k hk x).2`. Establish `hv : ∀ (c : GLw a w × GLw b w) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))), g ((blk h w c Y)⁻¹ * blk h w m (Multiplicative.toAdd X)) = g (blk h w (c⁻¹ * m) (Multiplicative.toAdd (X * Multiplicative.ofAdd (-( …`. Introduce `c Y X`. Rewrite using `[inv_blk]`.

Both sides reduce to the same expression. Establish `hS : Sm h w (cv (KGL w n) f g) m = ∑ᶠ c : (GLw a w × GLw b w) ⧸ (KGL w a).prod (KGL w b), Sm h w f c.out * Sm h w g (c.out⁻¹ * m)`. Unfold `Sm`. Repeatedly rewrite using `[hcv]`. Use `swap3 (fun c x => f (blk h w (Quotient.out c) (Multiplicative.toAdd (Quotient.out x)))) (fun c x X => g ((blk h w (Quotient.out c) (Multiplicative.toAdd (Quotient.out x)))⁻¹ * blk h w m (Multiplicative.toAdd (Quotient.out X)))) _ hCs ?_ (fun c => hsup f hf _) ?_ (fun c => ∑ᶠ x : …` and prove the remaining obligations.

Introduce `c hc x`. Assume the negation of the conclusion as `hx`. Conclude with `hc ⟨_, hx⟩`. Introduce `c x`. Repeatedly rewrite using `[hv]`.

Conclude with `support_translate (intMat a b w) (fun z => g (blk h w ((Quotient.out c)⁻¹ * m) (Multiplicative.toAdd z))) (fun z l hl => right_L h w g hgR _ z l hl) _ (hsup g hg _)`. Introduce `c x`. Repeatedly rewrite using `[hv]`. Conclude with `sum_translate (intMat a b w) (fun z => g (blk h w ((Quotient.out c)⁻¹ * m) (Multiplicative.toAdd z))) (fun z l hl => right_L h w g hgR _ z l hl) _`. Rewrite using `[hR, hct _ hfg, hS, ← smul_eq_mul, smul_finsum]`.

Use `finsum_congr fun c => ?_` and prove the remaining obligations. Establish `e : dl w m = dl w (Quotient.out c) * dl w ((Quotient.out c)⁻¹ * m)`. Rewrite using `[← dl_mul, mul_inv_cancel_left]`. Rewrite using `[hct f hf, hct g hg, smul_eq_mul, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ctMul : CtMul := by
  intro E _ _ _ w n a b h f g hf hg
  obtain ⟨-, -, hKo, hKc, -, -, -⟩ := unitHecke E n a b w
  have hfg : IsHecke (KGL w n) (cv (KGL w n) f g) := cvHecke _ (KGL w n) hKo hKc f g hf hg
  have hct : ∀ φ, IsHecke (KGL w n) φ → ∀ m, ct h w φ m = dl w m * Sm h w φ m :=
    fun φ hφ m => (ctSph E w n a b h φ hφ m).1
  have hsup : ∀ φ : GLw n w → ℂ, IsHecke (KGL w n) φ → ∀ m : GLw a w × GLw b w,
      (Function.support fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w =>
        φ (blk h w m (Multiplicative.toAdd q.out))).Finite :=
    fun φ hφ m => (ctSph E w n a b h φ hφ m).2
  funext m
  have hR : cv (K2 a b w) (ct h w f) (ct h w g) m =
      ∑ᶠ c : (GLw a w × GLw b w) ⧸ K2 a b w, ct h w f c.out * ct h w g (c.out⁻¹ * m) := by
    refine hintSph _ (K2 a b w) (fun z => ct h w f z * ct h w g (z⁻¹ * m)) fun k hk x => ?_
    have e : (x * k)⁻¹ * m = k⁻¹ * (x⁻¹ * m) := by group
    show ct h w f (x * k) * ct h w g ((x * k)⁻¹ * m) = ct h w f x * ct h w g (x⁻¹ * m)
    rw [e, (ct_bi h w f hf k hk x).2, (ct_bi h w g hg k⁻¹ (inv_mem hk) _).1]
  have hinv : ∀ y, ∀ k ∈ KGL w n, ∀ x, f (x * k) * g ((x * k)⁻¹ * y) = f x * g (x⁻¹ * y) := by
    intro y k hk x
    have e : (x * k)⁻¹ * y = k⁻¹ * (x⁻¹ * y) := by group
    rw [e, (hf.2 k hk x).2, (hg.2 k⁻¹ (inv_mem hk) _).1]
  have hcv : ∀ y, cv (KGL w n) f g y =
      ∑ᶠ c : (GLw a w × GLw b w) ⧸ (KGL w a).prod (KGL w b),
        ∑ᶠ x : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w,
          f (blk h w c.out (Multiplicative.toAdd x.out)) *
            g ((blk h w c.out (Multiplicative.toAdd x.out))⁻¹ * y) := by
    intro y
    have e1 : cv (KGL w n) f g y = ∑ᶠ p : GLw n w ⧸ KGL w n, f p.out * g (p.out⁻¹ * y) :=
      hintSph _ (KGL w n) (fun z => f z * g (z⁻¹ * y)) fun k hk x => hinv y k hk x
    rw [e1]
    refine GlobalTheory.CompanionTheory.IntDec.iwasawa_sum h w (fun z => f z * g (z⁻¹ * y)) (fun k hk x => hinv y k hk x) ?_
    refine (GlobalTheory.CompanionTheory.IntDec.finite_mk_support (KGL w n) hKo f hf.1).subset fun p hp => ?_
    exact ⟨p.out, left_ne_zero_of_mul hp, QuotientGroup.out_eq' p⟩
  have hCs : {c : (GLw a w × GLw b w) ⧸ (KGL w a).prod (KGL w b) |
      ∃ Y, f (blk h w c.out Y) ≠ 0}.Finite := by
    refine GlobalTheory.CompanionTheory.IntDec.finite_lev h w _ (GlobalTheory.CompanionTheory.IntDec.finite_mk_support (KGL w n) hKo f hf.1) _ ?_
    rintro c ⟨Y, hY⟩
    exact ⟨c.out, Y, QuotientGroup.out_eq' c, _, hY, rfl⟩
  have hgR : ∀ k ∈ KGL w n, ∀ x, g (x * k) = g x := fun k hk x => (hg.2 k hk x).2
  have hv : ∀ (c : GLw a w × GLw b w) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E))
      (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))),
      g ((blk h w c Y)⁻¹ * blk h w m (Multiplicative.toAdd X)) =
        g (blk h w (c⁻¹ * m) (Multiplicative.toAdd
          (X * Multiplicative.ofAdd (-(((c⁻¹ * m).1⁻¹).val * Y * (c⁻¹ * m).2.val))))) := by
    intro c Y X
    rw [inv_blk]
    rfl
  have hS : Sm h w (cv (KGL w n) f g) m =
      ∑ᶠ c : (GLw a w × GLw b w) ⧸ (KGL w a).prod (KGL w b),
        Sm h w f c.out * Sm h w g (c.out⁻¹ * m) := by
    unfold Sm
    simp_rw [hcv]
    refine swap3 (fun c x => f (blk h w (Quotient.out c) (Multiplicative.toAdd (Quotient.out x))))
      (fun c x X => g ((blk h w (Quotient.out c) (Multiplicative.toAdd (Quotient.out x)))⁻¹ *
        blk h w m (Multiplicative.toAdd (Quotient.out X)))) _ hCs ?_ (fun c => hsup f hf _) ?_
      (fun c => ∑ᶠ x : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w,
        g (blk h w ((Quotient.out c)⁻¹ * m) (Multiplicative.toAdd (Quotient.out x)))) ?_
    · intro c hc x
      by_contra hx
      exact hc ⟨_, hx⟩
    · intro c x
      simp_rw [hv]
      exact support_translate (intMat a b w)
        (fun z => g (blk h w ((Quotient.out c)⁻¹ * m) (Multiplicative.toAdd z)))
        (fun z l hl => right_L h w g hgR _ z l hl) _ (hsup g hg _)
    · intro c x
      simp_rw [hv]
      exact sum_translate (intMat a b w)
        (fun z => g (blk h w ((Quotient.out c)⁻¹ * m) (Multiplicative.toAdd z)))
        (fun z l hl => right_L h w g hgR _ z l hl) _
  rw [hR, hct _ hfg, hS, ← smul_eq_mul, smul_finsum]
  refine finsum_congr fun c => ?_
  have e : dl w m = dl w (Quotient.out c) * dl w ((Quotient.out c)⁻¹ * m) := by
    rw [← dl_mul, mul_inv_cancel_left]
  rw [hct f hf, hct g hg, smul_eq_mul, e]
  ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
