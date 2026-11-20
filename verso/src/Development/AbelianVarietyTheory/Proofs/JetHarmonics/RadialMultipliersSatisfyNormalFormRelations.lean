import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormActualOperatorsAlgebraicHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPairConstantsPointwiseAdjointBoundedStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EulerDerivMultipliersCommuteCoordOpsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormEntriesCommutatorMultiplierStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConnectionMulRelOfEntryRelationsStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.MulRelActual

section pairs

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mkPair_mul_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b * Q.mkP c d = Q.mkP (a * c) (d * b) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mkPair_add_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b + Q.mkP c d = Q.mkP (a + c) (b + d) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mkPair_sub_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b - Q.mkP c d = Q.mkP (a - c) (b - d) := rfl
/- English proof (translation)
Rewrite using `[h, h']`.
-/
theorem mkPair_congr {a b c d : Module.End ℂ V} (h : a = c) (h' : b = d) : Q.mkP a b = Q.mkP c d := by rw [h, h']

/- English proof (translation)
The claim follows from `congrArg (fun x : Q.Pr V => MulOpposite.unop (Prod.snd x)) h`.
-/
theorem snd_eq_of_mkPair_eq {a b c d : Module.End ℂ V} (h : Q.mkP a b = Q.mkP c d) : b = d :=
  congrArg (fun x : Q.Pr V => MulOpposite.unop (Prod.snd x)) h

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Q.mkP a b * Q.mkP w w = Q.mkP w w * Q.mkP a b`. Rewrite using `[mkPair_mul_mkPair, mkPair_mul_mkPair]`. Conclude with `mkPair_congr ha.eq hb.eq.symm`.
-/
theorem commute_mkP {a b w : Module.End ℂ V} (ha : Commute a w) (hb : Commute b w) :
    Commute (Q.mkP a b) (Q.mkP w w) := by
  change Q.mkP a b * Q.mkP w w = Q.mkP w w * Q.mkP a b
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair]
  exact mkPair_congr ha.eq hb.eq.symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨Prod.fst x, MulOpposite.unop (Prod.snd x), rfl⟩`.
-/
theorem exists_mkP (x : Q.Pr V) : ∃ a b, x = Q.mkP a b := ⟨Prod.fst x, MulOpposite.unop (Prod.snd x), rfl⟩

end pairs

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

omit [FiniteDimensional ℂ Wp] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hsVec_smul (s : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (s • A) = s • B.hsVec A := rfl

omit [FiniteDimensional ℂ Wp] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hsVec_sub (A A' : Wq →L[ℂ] Wp) : B.hsVec (A - A') = B.hsVec A - B.hsVec A' := rfl

omit [FiniteDimensional ℂ Wp] in
/- English proof (translation)
Establish `h1 : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0` using `fun i => congrArg (fun v => v i) h`. Apply `ContinuousLinearMap.coe_injective` to reduce the goal to its premises. Apply `(stdOrthonormalBasis ℂ Wq).toBasis.ext` to reduce the goal to its premises. Introduce `i`. Simplify using `using h1 i`.
-/
theorem eq_zero_of_hsVec {A : Wq →L[ℂ] Wp} (h : B.hsVec A = 0) : A = 0 := by
  have h1 : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := fun i => congrArg (fun v => v i) h
  apply ContinuousLinearMap.coe_injective
  apply (stdOrthonormalBasis ℂ Wq).toBasis.ext
  intro i
  simpa using h1 i

omit [FiniteDimensional ℂ Wp] in
/- English proof (translation)
Establish `h1 : inner ℂ (B.hsVec (A - A')) (B.hsVec (A - A')) = 0` using `by nth_rewrite 2 [hsVec_sub]`. Rewrite using `[inner_sub_right, h, sub_self]`. Conclude with `sub_eq_zero.1 (eq_zero_of_hsVec (inner_self_eq_zero.1 h1))`.
-/
theorem eq_of_inner {A A' : Wq →L[ℂ] Wp}
    (h : inner ℂ (B.hsVec (A - A')) (B.hsVec A) = inner ℂ (B.hsVec (A - A')) (B.hsVec A')) : A = A' := by
  have h1 : inner ℂ (B.hsVec (A - A')) (B.hsVec (A - A')) = 0 := by
    nth_rewrite 2 [hsVec_sub]
    rw [inner_sub_right, h, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_hsVec (inner_self_eq_zero.1 h1))

variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `c g`. Distinguish the cases in `hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z'`. Conclude with `h (c, g) hx`. Rewrite using `[Φ.2.1 (c, g) hx, Ψ.2.1 (c, g) hx]`.
-/
theorem radSp_ext {Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
    (h : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) : Φ = Ψ := by
  apply Subtype.ext
  funext c g
  by_cases hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z'
  · exact h (c, g) hx
  · rw [Φ.2.1 (c, g) hx, Ψ.2.1 (c, g) hx]

/- English proof (translation)
Use `LinearMap.ext fun Φ => radSp_ext fun x hx => ?_` and prove the remaining obligations. Apply `eq_of_inner` to reduce the goal to its premises. Establish `h1` using `hab (w Φ) (a (w Φ) - w (a Φ)) x hx`. Establish `h2` using `hab Φ (a (w Φ) - w (a Φ)) x hx`. Unfold `B.hsInner at h1 h2`.

Rewrite `h1` using `[hw Φ, hsVec_smul, inner_smul_right, ← h2, ← inner_smul_right, ← hsVec_smul, ← hw (a Φ)]`. Conclude with `h1`.
-/
theorem commute_of_adj {a b w : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {m : (Fin P.r → ℂ) → Q.Mx P.k P.r → ℂ} (hw : P5.multiplicationOperator w m)
    (hab : ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      B.hsInner ((a Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) =
        B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) ((b Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)) :
    Commute a w := by
  refine LinearMap.ext fun Φ => radSp_ext fun x hx => ?_
  apply eq_of_inner
  have h1 := hab (w Φ) (a (w Φ) - w (a Φ)) x hx
  have h2 := hab Φ (a (w Φ) - w (a Φ)) x hx
  unfold B.hsInner at h1 h2
  rw [hw Φ, hsVec_smul, inner_smul_right, ← h2, ← inner_smul_right, ← hsVec_smul, ← hw (a Φ)] at h1
  exact h1

/- English proof (translation)
Take `⟨a, b, rfl⟩` from `exists_mkP x`. Use `commute_mkP (commute_of_adj (b := b) hw hx) (commute_of_adj (b := a) hw fun Φ Ψ y hy => ?_)` and prove the remaining obligations. Establish `h` using `hx Ψ Φ y hy`. Unfold `B.hsInner at h ⊢`. Rewrite using `[← inner_conj_symm, ← inner_conj_symm (B.hsVec ((a Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2))]`.

Conclude with `congrArg _ h.symm`.
-/
theorem commute_of_ptAdj {x : RA P Bs} (hx : PtAdj P Bs x) {w : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {m : (Fin P.r → ℂ) → Q.Mx P.k P.r → ℂ} (hw : P5.multiplicationOperator w m) : Commute x (Q.mkP w w) := by
  obtain ⟨a, b, rfl⟩ := exists_mkP x
  refine commute_mkP (commute_of_adj (b := b) hw hx) (commute_of_adj (b := a) hw fun Φ Ψ y hy => ?_)
  have h := hx Ψ Φ y hy
  unfold B.hsInner at h ⊢
  rw [← inner_conj_symm, ← inner_conj_symm (B.hsVec ((a Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2))]
  exact congrArg _ h.symm

end hs

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN φ W hφ hW`. Establish `hH` using `(GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hN).1`. Establish `hK` using `GlobalTheory.T.radialPairConstants_pointwiseAdjoint_bounded Wp Wq P Bs X μ L st l0 d hD hN`. Establish `hC` using `GlobalTheory.T.eulerDerivMultipliers_coordOps_commutation_relations Wp Wq P Bs X μ L st l0 d hD hN φ W hφ hW`. Establish `hT` using `GlobalTheory.T.normalForm_entries_commutator_multiplier Wp Wq P Bs X μ L st l0 d hD hN φ W hφ hW`.

Take `⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩, -, hR, hQ⟩` from `hN`. Establish `hκ : ∀ q (f : M.Ty P → ℂ), Commute (d.κ f) (Q.mkP (W q) (W q))` using `fun q f => commute_of_ptAdj (hK f).1 (hW q)`. Establish `hf : ∀ q, ∀ f ∈ d.L.fns, Commute f (Q.mkP (W q) (W q))`. Introduce `q f hf`. Take `⟨ho, hfn⟩` from `hC q`.

Break down `hf with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | hf)` into its components or cases. Rewrite using `[h3]`. Conclude with `commute_mkP (ho l).2.2.1 (ho l).2.2.2.2.1`. Rewrite using `[h4]`. Conclude with `commute_mkP (ho l).2.2.2.1 (ho l).2.2.2.2.2`.

Rewrite using `[h5]`. Conclude with `commute_mkP (ho l).2.2.2.2.1 (ho l).2.2.1`. Rewrite using `[h6]`. Conclude with `commute_mkP (ho l).2.2.2.2.2 (ho l).2.2.2.1`. Break down `hf with rfl | rfl | rfl | rfl | rfl | rfl` into its components or cases.

Rewrite using `[h7]`. Conclude with `commute_mkP (hfn _) (hfn _)`. Rewrite using `[h8]`. Conclude with `commute_mkP (hfn _) (hfn _)`. Rewrite using `[h9]`.

Conclude with `commute_mkP (hfn _) (hfn _)`. Rewrite using `[h10]`. Conclude with `commute_mkP (hfn _) (hfn _)`. Rewrite using `[h11]`. Conclude with `commute_mkP (hfn _) (hfn _)`.

Rewrite using `[h12]`. Conclude with `commute_mkP (hfn _) (hfn _)`. Use `GlobalTheory.T.connection_mulRel_of_entry_relations P (RA P Bs) d hH _ fun q => ⟨hf q, fun l => ?_, fun l => ?_, hκ q, rfl, fun Y => ?_⟩` and prove the remaining obligations. Rewrite using `[h1, mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_add_mkPair]`. Use `mkPair_congr ((hC q).1 l).1 ?_` and prove the remaining obligations.

Rewrite using `[neg_mul, ((hC q).1 l).2.1, mul_neg]`. Normalize the expressions using the abelian group laws. Rewrite using `[h2, mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_add_mkPair]`. Use `mkPair_congr ((hC q).1 l).2.1 ?_` and prove the remaining obligations. Rewrite using `[neg_mul, ((hC q).1 l).1, mul_neg]`.

Normalize the expressions using the abelian group laws. Establish `mζ : d.L.ζb ∈ d.L.fns` using `Or.inr (by simp)`. Establish `mG : d.L.GG ∈ d.L.fns` using `Or.inr (by simp)`. Establish `mGi : d.L.GGi ∈ d.L.fns` using `Or.inr (by simp)`. Establish `e11 : d.QQ Y 1 1 = d.L.GG * d.x Y` using `rfl`.

Establish `c11 : ∀ g ∈ d.L.fns, Commute (d.QQ Y 1 1) g` using `fun g hg => by`. Rewrite using `[e11]`. Conclude with `Commute.mul_left (d.L.fns_comm _ mG _ hg) (hR.2.1 _ g (Or.inl hg))`. Establish `c11m : Commute (d.QQ Y 1 1) (Q.mkP (W (q + 1)) (W (q + 1)))`. Rewrite using `[e11]`.

Conclude with `Commute.mul_left (hf _ _ mG) (hκ _ _)`. Establish `cζG : Commute d.L.ζb d.L.GGi` using `d.L.fns_comm _ mζ _ mGi`. Establish `key : d.L.ζb * d.L.GGi * Q.mkP (W (q + 1)) (W (q + 1)) * d.QQ Y 1 1 = d.QQ Y 1 1 * (Q.mkP (W (q + 1)) (W (q + 1)) * (d.L.GGi * d.L.ζb))`. Rewrite using `[← (((c11 _ mζ).mul_right (c11 _ mGi)).mul_right c11m).eq, (Commute.mul_left (hf (q + 1) _ mζ) (hf (q + 1) _ mGi)).eq, cζG.eq]`. Establish `hY : star (Y : ℂ) = Y` using `Complex.conj_ofReal Y`.

Establish `q10 : d.QQ Y 1 0 = Q.mkP (X.t Y 1 0) (X.t Y 0 1)`. Rewrite using `[← hQ]`. Express the relevant statement in the definitionally equal form `Q.mkP (X.t Y 1 0) (X.t (star (Y : ℂ)) 0 1) = _`. Rewrite using `[hY]`. Establish `q11 : d.QQ Y 1 1 = Q.mkP (X.t Y 1 1) (X.t Y 1 1)`.

Rewrite using `[← hQ]`. Express the relevant statement in the definitionally equal form `Q.mkP (X.t Y 1 1) (X.t (star (Y : ℂ)) 1 1) = _`. Rewrite using `[hY]`. Rewrite `key` using `[q11, h9, h12]`. Rewrite using `[q10, q11, h9, h12]`.

Simplify using `only [mkPair_mul_mkPair, mkPair_sub_mkPair] at key ⊢`. Use `mkPair_congr (hT q Y).1 ?_` and prove the remaining obligations. Rewrite using `[snd_eq_of_mkPair_eq key, (hT q Y).2.2]`. Normalize the expressions using the abelian group laws.
-/
theorem mulRel_actual : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → MulRel d.L (fun q => Q.mkP (W q) (W q)) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN φ W hφ hW
  have hH := (GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hN).1
  have hK := GlobalTheory.T.radialPairConstants_pointwiseAdjoint_bounded Wp Wq P Bs X μ L st l0 d hD hN
  have hC := GlobalTheory.T.eulerDerivMultipliers_coordOps_commutation_relations Wp Wq P Bs X μ L st l0 d hD hN φ W hφ hW
  have hT := GlobalTheory.T.normalForm_entries_commutator_multiplier Wp Wq P Bs X μ L st l0 d hD hN φ W hφ hW
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩, -, hR, hQ⟩ := hN
  have hκ : ∀ q (f : M.Ty P → ℂ), Commute (d.κ f) (Q.mkP (W q) (W q)) := fun q f =>
    commute_of_ptAdj (hK f).1 (hW q)
  have hf : ∀ q, ∀ f ∈ d.L.fns, Commute f (Q.mkP (W q) (W q)) := by
    intro q f hf
    obtain ⟨ho, hfn⟩ := hC q
    rcases hf with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | hf)
    · rw [h3]; exact commute_mkP (ho l).2.2.1 (ho l).2.2.2.2.1
    · rw [h4]; exact commute_mkP (ho l).2.2.2.1 (ho l).2.2.2.2.2
    · rw [h5]; exact commute_mkP (ho l).2.2.2.2.1 (ho l).2.2.1
    · rw [h6]; exact commute_mkP (ho l).2.2.2.2.2 (ho l).2.2.2.1
    · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h7]; exact commute_mkP (hfn _) (hfn _)
      · rw [h8]; exact commute_mkP (hfn _) (hfn _)
      · rw [h9]; exact commute_mkP (hfn _) (hfn _)
      · rw [h10]; exact commute_mkP (hfn _) (hfn _)
      · rw [h11]; exact commute_mkP (hfn _) (hfn _)
      · rw [h12]; exact commute_mkP (hfn _) (hfn _)
  refine GlobalTheory.T.connection_mulRel_of_entry_relations P (RA P Bs) d hH _ fun q => ⟨hf q, fun l => ?_, fun l => ?_, hκ q, rfl, fun Y => ?_⟩
  · rw [h1, mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_add_mkPair]
    refine mkPair_congr ((hC q).1 l).1 ?_
    rw [neg_mul, ((hC q).1 l).2.1, mul_neg]; abel
  · rw [h2, mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_add_mkPair]
    refine mkPair_congr ((hC q).1 l).2.1 ?_
    rw [neg_mul, ((hC q).1 l).1, mul_neg]; abel
  · have mζ : d.L.ζb ∈ d.L.fns := Or.inr (by simp)
    have mG : d.L.GG ∈ d.L.fns := Or.inr (by simp)
    have mGi : d.L.GGi ∈ d.L.fns := Or.inr (by simp)
    have e11 : d.QQ Y 1 1 = d.L.GG * d.x Y := rfl
    have c11 : ∀ g ∈ d.L.fns, Commute (d.QQ Y 1 1) g := fun g hg => by
      rw [e11]
      exact Commute.mul_left (d.L.fns_comm _ mG _ hg) (hR.2.1 _ g (Or.inl hg))
    have c11m : Commute (d.QQ Y 1 1) (Q.mkP (W (q + 1)) (W (q + 1))) := by
      rw [e11]
      exact Commute.mul_left (hf _ _ mG) (hκ _ _)
    have cζG : Commute d.L.ζb d.L.GGi := d.L.fns_comm _ mζ _ mGi
    have key : d.L.ζb * d.L.GGi * Q.mkP (W (q + 1)) (W (q + 1)) * d.QQ Y 1 1 =
        d.QQ Y 1 1 * (Q.mkP (W (q + 1)) (W (q + 1)) * (d.L.GGi * d.L.ζb)) := by
      rw [← (((c11 _ mζ).mul_right (c11 _ mGi)).mul_right c11m).eq,
        (Commute.mul_left (hf (q + 1) _ mζ) (hf (q + 1) _ mGi)).eq, cζG.eq]
    have hY : star (Y : ℂ) = Y := Complex.conj_ofReal Y
    have q10 : d.QQ Y 1 0 = Q.mkP (X.t Y 1 0) (X.t Y 0 1) := by
      rw [← hQ]
      change Q.mkP (X.t Y 1 0) (X.t (star (Y : ℂ)) 0 1) = _
      rw [hY]
    have q11 : d.QQ Y 1 1 = Q.mkP (X.t Y 1 1) (X.t Y 1 1) := by
      rw [← hQ]
      change Q.mkP (X.t Y 1 1) (X.t (star (Y : ℂ)) 1 1) = _
      rw [hY]
    rw [q11, h9, h12] at key
    rw [q10, q11, h9, h12]
    simp only [mkPair_mul_mkPair, mkPair_sub_mkPair] at key ⊢
    refine mkPair_congr (hT q Y).1 ?_
    rw [snd_eq_of_mkPair_eq key, (hT q Y).2.2]
    abel

end GlobalTheory.HatNF.MulRelActual
