import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.UnitaryBC GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `h1 : IsIntegral ℤ (j (x : E))` using `x.isIntegral_coe.map j.toIntAlgHom`. Establish `h2 : IsIntegral (PadicAlgCl.valued l).v.integer (j (x : E))` using `h1.tower_top`. Establish `h3` using `(Valuation.integer.integers (PadicAlgCl.valued l).v).mem_of_integral h2`. Rewrite `h3` using `[Valuation.mem_integer_iff, PadicAlgCl.valuation_def]`. Conclude with `h3` after adjusting the coercions.
-/
private theorem norm_int_le_one {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (j : E →+* PadicAlgCl l) (x : 𝓞 E) :
    ‖j (x : E)‖ ≤ 1 := by
  have h1 : IsIntegral ℤ (j (x : E)) := x.isIntegral_coe.map j.toIntAlgHom
  have h2 : IsIntegral (PadicAlgCl.valued l).v.integer (j (x : E)) := h1.tower_top
  have h3 := (Valuation.integer.integers (PadicAlgCl.valued l).v).mem_of_integral h2
  rw [Valuation.mem_integer_iff, PadicAlgCl.valuation_def] at h3
  exact_mod_cast h3

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, rfl⟩` from `hy`. Establish `e : a ⊗ₜ[D.host.F] (x : D.host.E) = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] (x : D.host.E))`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.

Rewrite using `[e, RingHom.map_mul, norm_mul]`. Establish `h2` using `norm_int_le_one (ev.comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) x`. Conclude with `mul_le_one₀ (h a ha) (norm_nonneg _) h2`. Consider the case `zero => rw [RingHom.map_zero, norm_zero]`. Conclude with `zero_le_one`.

Consider the case `add x y _ _ hx hy`. Rewrite using `[RingHom.map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)`. Consider the case `neg x _ hx => rw [RingHom.map_neg, norm_neg]`. Conclude with `hx`.
-/
private theorem norm_le_of_int {D : D7} {l : ℕ} [Fact l.Prime]
    (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l)
    (h : ∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) →
      ‖ev (a ⊗ₜ[D.host.F] 1)‖ ≤ 1) (z) (hz : z ∈ intAE D) : ‖ev z‖ ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    have e : a ⊗ₜ[D.host.F] (x : D.host.E) = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] (x : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, RingHom.map_mul, norm_mul]
    have h2 := norm_int_le_one (ev.comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) x
    exact mul_le_one₀ (h a ha) (norm_nonneg _) h2
  | zero => rw [RingHom.map_zero, norm_zero]; exact zero_le_one
  | add x y _ _ hx hy =>
    rw [RingHom.map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | neg x _ hx => rw [RingHom.map_neg, norm_neg]; exact hx

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `hcO : ((l : ℕ) : 𝓞 D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hl.ne_zero`. Establish `h1` using `(hx _ hcO).not.1 hP`. Rewrite `h1` using `[not_not]`. Establish `h2` using `norm_le_of_int ev h _ h1`.

Assume the negation of the conclusion as `hne`. Establish `h3 : ev (finPart D e) * ev (finPart D e) = ev (finPart D e)`. Rewrite using `[← RingHom.map_mul, ← RingHom.map_mul, he]`. Establish `h4 : ev (finPart D e) = 1` using `mul_left_cancel₀ hne (h3.trans (mul_one _).symm)`. Rewrite `h2` using `[RingHom.map_mul, RingHom.map_mul, h4, one_mul]`.

Establish `h5 : ev (finPart D (incA D ((((l : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹))) = ((l : ℕ) : PadicAlgCl l)⁻¹`. Express the relevant statement in the definitionally equal form `(ev.comp ((finPart D).comp (incA D))) _ = _`. Rewrite using `[map_inv₀]`. Use `congr 1`. Simplify using `only [map_natCast]`.

Rewrite `h2` using `[h5, norm_inv]`. Establish `h6 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends]`. Conclude with `Padic.norm_p_lt_one`. Establish `h7 : 0 < ‖((l : ℕ) : PadicAlgCl l)‖` using `norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)`.

Conclude with `absurd h2 (not_le.2 ((one_lt_inv₀ h7).2 h6))`.
-/
private theorem ev_idem {D : D7} {l : ℕ} [Fact l.Prime]
    (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l)
    (h : ∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) →
      ‖ev (a ⊗ₜ[D.host.F] 1)‖ ≤ 1) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (e : AE D) (he : e * e = e)
    (hx : ∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)) :
    ev (finPart D e) = 0 := by
  have hl : l.Prime := Fact.out
  have hcO : ((l : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have h1 := (hx _ hcO).not.1 hP
  rw [not_not] at h1
  have h2 := norm_le_of_int ev h _ h1
  by_contra hne
  have h3 : ev (finPart D e) * ev (finPart D e) = ev (finPart D e) := by
    rw [← RingHom.map_mul, ← RingHom.map_mul, he]
  have h4 : ev (finPart D e) = 1 := mul_left_cancel₀ hne (h3.trans (mul_one _).symm)
  rw [RingHom.map_mul, RingHom.map_mul, h4, one_mul] at h2
  have h5 : ev (finPart D (incA D ((((l : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹))) = ((l : ℕ) : PadicAlgCl l)⁻¹ := by
    change (ev.comp ((finPart D).comp (incA D))) _ = _
    rw [map_inv₀]
    congr 1
    simp only [map_natCast]
  rw [h5, norm_inv] at h2
  have h6 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have h7 : 0 < ‖((l : ℕ) : PadicAlgCl l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  exact absurd h2 (not_le.2 ((one_lt_inv₀ h7).2 h6))

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul a e => rfl`.
-/
private theorem finPart_cA {D : D7} (w : AE D) :
    finPart D (cA D w) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e => rfl

/- English proof (translation)
Take `⟨α, rfl, h1, h0⟩` from `h`. Establish `: α * α = α`. Use `DFunLike.ext _ _ fun w => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (α * α) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w α`. Rewrite using `[map_mul]`.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[h1, mul_one]`. Rewrite using `[h0 w hw, mul_zero]`. Conclude with `Prod.ext (mul_zero _) this`.
-/
private theorem placeIdem {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F}
    (h : IsPlaceIdem D v ε) : ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have : α * α = α := by
    refine DFunLike.ext _ _ fun w => ?_
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (α * α) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w α
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [h1, mul_one]
    · rw [h0 w hw, mul_zero]
  exact Prod.ext (mul_zero _) this

/- English proof (translation)
Rewrite using `[Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]`. Use `congr 1`. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]`.

Rewrite using `[Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]`.
-/
private theorem finPart_sub_one {D : D7} (V : HSp D) (h : GA D V) (i j : Fin V.rank) :
    finPart D ((Formalism.L2.Theta.mt V h - 1) i j) = ((finHom V h).1 - 1) i j := by
  rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
  congr 1
  by_cases e : i = j
  · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]

/- English proof (translation)
Introduce `D V l _ ev h P hP x ⟨e, f, g, hef, _, hx, hs⟩`. Establish `hf : ev (finPart D f) = 0`. Break down `hef with ⟨⟨⟨h1, -⟩, h2⟩, rfl⟩ | ⟨rfl, ⟨v, ε, hε, h1⟩, h2⟩` into its components or cases. Establish `a1` using `ev_idem ev h P hP e h1 h2`. Establish `a2` using `ev_idem (ev.comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig)) (fun a ha => by`.

Express the relevant statement in the definitionally equal form `‖ev (a ⊗ₜ[D.host.F] D.sp.cm.sig 1)‖ ≤ 1`. Rewrite using `[map_one]`. Conclude with `h a ha) P hP e h1 h2`. Rewrite using `[RingHom.map_add, RingHom.map_add, a1, finPart_cA, zero_add]`. Conclude with `a2`.

Use `ev_idem ev h P hP f ?_ h2` and prove the remaining obligations. Rewrite using `[h1, ← RingHom.map_mul, placeIdem hε]`. Use extensionality with `i j`. Establish `h1` using `congrArg (fun z => ev (finPart D z)) (hs i j)`. Simplify using `only [RingHom.map_mul, hf, zero_mul] at h1`.

Rewrite `h1` using `[finPart_sub_one, ← hx, Matrix.sub_apply, RingHom.map_sub, eq_comm, sub_eq_zero]`. Rewrite using `[Matrix.map_apply, h1]`. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]`.

Rewrite using `[Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]`.
-/
theorem UpperTheory.eval_localElement_matrix_eq_one_of_prime_not_dvd :
    ∀ (D : D7) (V : HSp D) (l : ℕ) [Fact l.Prime]
        (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l),
        (∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) → ‖ev (a ⊗ₜ[D.host.F] 1)‖ ≤ 1) →
        ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ x : Bridge.Gf V, GlobalTheory.Hk3.IsLocElt V P x →
          Matrix.map x.1.val ev = 1 := by
  intro D V l _ ev h P hP x ⟨e, f, g, hef, _, hx, hs⟩
  have hf : ev (finPart D f) = 0 := by
    rcases hef with ⟨⟨⟨h1, -⟩, h2⟩, rfl⟩ | ⟨rfl, ⟨v, ε, hε, h1⟩, h2⟩
    · have a1 := ev_idem ev h P hP e h1 h2
      have a2 := ev_idem (ev.comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig))
        (fun a ha => by
          change ‖ev (a ⊗ₜ[D.host.F] D.sp.cm.sig 1)‖ ≤ 1
          rw [map_one]; exact h a ha) P hP e h1 h2
      rw [RingHom.map_add, RingHom.map_add, a1, finPart_cA, zero_add]
      exact a2
    · refine ev_idem ev h P hP f ?_ h2
      rw [h1, ← RingHom.map_mul, placeIdem hε]
  ext i j
  have h1 := congrArg (fun z => ev (finPart D z)) (hs i j)
  simp only [RingHom.map_mul, hf, zero_mul] at h1
  rw [finPart_sub_one, ← hx, Matrix.sub_apply, RingHom.map_sub, eq_comm, sub_eq_zero] at h1
  rw [Matrix.map_apply, h1]
  by_cases e : i = j
  · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
