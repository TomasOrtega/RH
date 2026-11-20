import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelSigns
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GradedModelSpansCotOfRigidWeights
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelIdealFinitenessOfWeightZeroFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GradedModelPointConditionOfPtHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GradedModelDerivationConditionOfPtHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjTor
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

/- English proof (translation)
Proceed by induction on `T₁ using Finset.strongInduction with`. Consider the case `H T₁ ih`. Distinguish the cases in `hirr : ∀ f ∈ T₁, ∀ f' ∈ T₁, R f f' → f = f'`. Conclude with `⟨T₁, h, hirr⟩`. Use `push_neg at hirr`.

Take `⟨f, hf, f', hf', hR, hne⟩` from `hirr`. Apply `ih (T₁.erase f') (Finset.erase_ssubset hf')` to reduce the goal to its premises. Use `⟨fun g hg => h.1 g (Finset.mem_of_mem_erase hg), fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨g', hg'T, hg'R⟩` from `h.2 g hg`. Distinguish the cases in `he : g' = f'`.

Substitute `he` using the available equality. Conclude with `⟨f, Finset.mem_erase.2 ⟨hne, hf⟩, htr _ _ _ hR hg'R⟩`. Conclude with `⟨g', Finset.mem_erase.2 ⟨he, hg'T⟩, hg'R⟩`.
-/
private theorem exists_irred {α : Type} (R : α → α → Prop) (htr : ∀ a b c, R a b → R b c → R a c) (P : α → Prop)
    (T₁ : Finset α) (h : (∀ f ∈ T₁, P f) ∧ ∀ f, P f → ∃ f' ∈ T₁, R f' f) :
    ∃ T : Finset α, ((∀ f ∈ T, P f) ∧ ∀ f, P f → ∃ f' ∈ T, R f' f) ∧ ∀ f ∈ T, ∀ f' ∈ T, R f f' → f = f' := by
  classical
  induction T₁ using Finset.strongInduction with
  | H T₁ ih =>
    by_cases hirr : ∀ f ∈ T₁, ∀ f' ∈ T₁, R f f' → f = f'
    · exact ⟨T₁, h, hirr⟩
    · push_neg at hirr
      obtain ⟨f, hf, f', hf', hR, hne⟩ := hirr
      apply ih (T₁.erase f') (Finset.erase_ssubset hf')
      refine ⟨fun g hg => h.1 g (Finset.mem_of_mem_erase hg), fun g hg => ?_⟩
      obtain ⟨g', hg'T, hg'R⟩ := h.2 g hg
      by_cases he : g' = f'
      · subst he
        exact ⟨f, Finset.mem_erase.2 ⟨hne, hf⟩, htr _ _ _ hR hg'R⟩
      · exact ⟨g', Finset.mem_erase.2 ⟨he, hg'T⟩, hg'R⟩

section Act

variable {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
  [Field K] [Algebra O K]

/- English proof (translation)
Rewrite using `[act_of_mem 𝒜 _ ξ hf]`. Both sides reduce to the same expression.
-/
private theorem act_tz (t : Kˣ) (ξ : A →ₐ[O] K) {j : ℤ} {f : A} (hf : f ∈ 𝒜 j) :
    act 𝒜 (tz t) ξ f = ((t ^ j : Kˣ) : K) * ξ f := by
  rw [act_of_mem 𝒜 _ ξ hf]
  rfl

/- English proof (translation)
Use `AlgHom.ext fun f => ?_` and prove the remaining obligations. Proceed by induction on `f using DirectSum.Decomposition.inductionOn 𝒜 with`. Consider the case `zero => simp`. Consider the case `homogeneous m => exact h _ _ m.2`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
private theorem graded_ext {ξ ξ' : A →ₐ[O] K} (h : ∀ j, ∀ f ∈ 𝒜 j, ξ f = ξ' f) : ξ = ξ' := by
  refine AlgHom.ext fun f => ?_
  induction f using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous m => exact h _ _ m.2
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
The claim follows from `graded_ext 𝒜 fun j f hf => by rw [act_tz 𝒜 _ _ hf, act_tz 𝒜 _ _ hf, act_tz 𝒜 _ _ hf, mul_zpow, Units.val_mul, mul_assoc]`.
-/
private theorem act_act (s t : Kˣ) (ξ : A →ₐ[O] K) :
    act 𝒜 (tz s) (act 𝒜 (tz t) ξ) = act 𝒜 (tz (s * t)) ξ :=
  graded_ext 𝒜 fun j f hf => by
    rw [act_tz 𝒜 _ _ hf, act_tz 𝒜 _ _ hf, act_tz 𝒜 _ _ hf, mul_zpow, Units.val_mul, mul_assoc]

/- English proof (translation)
Apply `graded_ext 𝒜` to reduce the goal to its premises. Introduce `j f hf`. Rewrite using `[act_tz 𝒜 1 ξ hf]`. Simplify using the standard rewrite rules.
-/
private theorem act_one (ξ : A →ₐ[O] K) : act 𝒜 (tz 1) ξ = ξ := by
  apply graded_ext 𝒜
  intro j f hf
  rw [act_tz 𝒜 1 ξ hf]
  simp

/- English proof (translation)
Establish `key : ∀ j, ∀ f ∈ 𝒜 j, (act 𝒜 (tz t) ξ f = 0 ↔ ξ f = 0)` using `fun j f hf => by`. Rewrite using `[act_tz 𝒜 t ξ hf]`. Simplify using `only [mul_eq_zero, Units.val_zpow_eq_zpow_val]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h0 | h0)`.

Conclude with `absurd h0 (zpow_ne_zero _ t.ne_zero)`. Conclude with `h0`. Conclude with `Or.inr`. Conclude with `⟨fun hn => h.1 fun j hj f hf => (key j f hf).1 (hn j hj f hf), fun hp => h.2 fun j hj f hf => (key j f hf).1 (hp j hj f hf)⟩`.
-/
private theorem twoSigned_act (t : Kˣ) {ξ : A →ₐ[O] K} (h : TwoSigned 𝒜 ξ) : TwoSigned 𝒜 (act 𝒜 (tz t) ξ) := by
  have key : ∀ j, ∀ f ∈ 𝒜 j, (act 𝒜 (tz t) ξ f = 0 ↔ ξ f = 0) := fun j f hf => by
    rw [act_tz 𝒜 t ξ hf]
    simp only [mul_eq_zero, Units.val_zpow_eq_zpow_val]
    constructor
    · rintro (h0 | h0)
      · exact absurd h0 (zpow_ne_zero _ t.ne_zero)
      · exact h0
    · exact Or.inr
  exact ⟨fun hn => h.1 fun j hj f hf => (key j f hf).1 (hn j hj f hf),
    fun hp => h.2 fun j hj f hf => (key j f hf).1 (hp j hj f hf)⟩

end Act

/- English proof (translation)
Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `e0 : (0 : ℝ) ≤ ((UpperTheory.V.Base.eO l c.O).toNat : ℝ)` using `Nat.cast_nonneg _`. Use `⟨fun x y hx hy => ?_, fun x y hx hy hxy => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Simplify using `only [vl, norm_mul]`. Rewrite using `[Real.logb_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy)]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [vl]`. Establish `hmax` using `IsUltrametricDist.norm_add_le_max x y`. Establish `hxy' : 0 < ‖x + y‖` using `norm_pos_iff.2 hxy`. Rewrite using `[← mul_min_of_nonneg _ _ e0]`.

Apply `mul_le_mul_of_nonneg_left _ e0` to reduce the goal to its premises. Break down `le_total ‖x‖ ‖y‖ with hle | hle` into its components or cases. Rewrite `hmax` using `[max_eq_right hle]`. Conclude with `(min_le_right _ _).trans (neg_le_neg (Real.logb_le_logb_of_le hl hxy' hmax))`. Rewrite `hmax` using `[max_eq_left hle]`.

Conclude with `(min_le_left _ _).trans (neg_le_neg (Real.logb_le_logb_of_le hl hxy' hmax))`. Establish `hn` using `UpperTheory.V.Base.normO l c.O a ha`. Establish `h2` using `congrArg (Real.logb l) hn`. Rewrite `h2` using `[Real.logb_pow, Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one hl]`. Use `show _ * -Real.logb l ‖(a : PadicAlgCl l)‖ = _`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem isNVal (l : ℕ) [Fact l.Prime] (c : Coef l) :
    IsNVal c.O (PadicAlgCl l) fun x => ((UpperTheory.V.Base.eO l c.O).toNat : ℝ) * vl l x := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have e0 : (0 : ℝ) ≤ ((UpperTheory.V.Base.eO l c.O).toNat : ℝ) := Nat.cast_nonneg _
  refine ⟨fun x y hx hy => ?_, fun x y hx hy hxy => ?_, fun a ha => ?_⟩
  · simp only [vl, norm_mul]
    rw [Real.logb_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy)]
    ring
  · simp only [vl]
    have hmax := IsUltrametricDist.norm_add_le_max x y
    have hxy' : 0 < ‖x + y‖ := norm_pos_iff.2 hxy
    rw [← mul_min_of_nonneg _ _ e0]
    apply mul_le_mul_of_nonneg_left _ e0
    rcases le_total ‖x‖ ‖y‖ with hle | hle
    · rw [max_eq_right hle] at hmax
      exact (min_le_right _ _).trans (neg_le_neg (Real.logb_le_logb_of_le hl hxy' hmax))
    · rw [max_eq_left hle] at hmax
      exact (min_le_left _ _).trans (neg_le_neg (Real.logb_le_logb_of_le hl hxy' hmax))
  · have hn := UpperTheory.V.Base.normO l c.O a ha
    have h2 := congrArg (Real.logb l) hn
    rw [Real.logb_pow, Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one hl] at h2
    show _ * -Real.logb l ‖(a : PadicAlgCl l)‖ = _
    linarith

/- English proof (translation)
Apply `MonoidHom.ext` to reduce the goal to its premises. Introduce `g`. Simplify using `[conjBy, map_mul, mul_assoc]`.
-/
private theorem conj_conj {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (s t : Rˣ) :
    conjBy (tor R s) (conjBy (tor R t) r) = conjBy (tor R (s * t)) r := by
  apply MonoidHom.ext
  intro g
  simp [conjBy, map_mul, mul_assoc]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M hl hmk hLM hfin hpt σ hσ htr`. Use `letI := M.cr`. Use `letI := M.al`. Use `letI := M.gr`. Establish `hM2` using `modelIdeal_finiteness_of_weightZero_finite S M hl hmk hfin`.

Establish `hM1` using `gradedModel_spansCot_of_rigid_weights S M hl hmk hM2 hpt.rigid0`. Establish `hM3` using `gradedModel_pointCondition_of_ptHyp S M hl hmk hM2 hpt`. Establish `hM4` using `gradedModel_derivationCondition_of_ptHyp S M hl hmk hM2 hpt`. Establish `hsg` using `model_signs S M hl hmk`. Establish `hv` using `isNVal l c`.

Take `⟨-, -, -, hcomp, -, he0, hefin, -, -⟩` from `UpperTheory.V.Base.dvrFacts l c.O`. Use `haveI := hcomp`. Establish `htp : ∀ f : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f → (TwoPt η S.r.hom f ↔ TwoSigned M.𝒜 (f.comp M.q))` using `fun f hf => ⟨fun h => ⟨fun hn => h.2.1 ((hsg f hf).1.1 hn), fun hp => h.2.2 ((hsg f hf).2.1.1 hp)⟩, fun h => ⟨hf, fun hu => h.1 ((hsg f hf).1.2 hu), fun hw => h.2 ((hsg f hf).2.1.2 hw)⟩⟩`. Establish `hon : ∀ f : S.R →ₐ[c.O] PadicAlgCl l, OnS M.Q.ideal (f.comp M.q)`. Introduce `f y hy`.

Establish `hy' : y ∈ RingHom.ker M.q` using `by rw [M.ker_q]; exact hy`. Rewrite using `[AlgHom.comp_apply, RingHom.mem_ker.1 hy', map_zero]`. Use `choose E hE hqE using M.ent σ`. Establish `hmem : ∀ i, E i i ∈ M.𝒜 0` using `fun i => by`. Use `hE i i` as an intermediate fact.

Simplify `this` using `[wt]`. Use `set a : M.A := E 0 0 + E 1 1 + E 2 2 - algebraMap c.O M.A ((r0 η Ψ σ).mat.trace) with ha`. Establish `ha0 : a ∈ M.𝒜 0` using `Submodule.sub_mem _ (add_mem (add_mem (hmem 0) (hmem 1)) (hmem 2)) (SetLike.algebraMap_mem_graded M.𝒜 _)`. Establish `hqa : ∀ f : S.R →ₐ[c.O] PadicAlgCl l, f (M.q a) = trDiff η Ψ S.r.hom σ f`. Introduce `f`.

Simplify using `[ha, hqE, trDiff, Matrix.trace_fin_three]`. Establish `hb : (r0 η Ψ σ).mat = (S.r.hom σ).mat.map M.x₀`. Rewrite using `[← M.base]`. Conclude with `GG.map_mat _ _`. Establish `hxa : M.x a = 0`.

Rewrite using `[← M.x₀_q, AlgHom.comp_apply]`. Simplify using `[ha, hqE, hb, Matrix.trace_fin_three]`. Establish `hM5 : M5 M.𝒜 (PadicAlgCl l) M.x M.Q.ideal a`. Use `⟨ha0, hxa, fun ξ hξ hts => ?_⟩` and prove the remaining obligations. Take `⟨t, f, hf, hact⟩` from `M.pts hM2 ξ hξ`.

Establish `h1` using `congrArg (fun g => g a) hact`. Simplify using `only [AlgHom.comp_apply] at h1`. Rewrite `h1` using `[act_tz M.𝒜 t ξ ha0, zpow_zero, Units.val_one, one_mul, hqa]`. Rewrite using `[h1]`. Apply `htr f` to reduce the goal to its premises.

Rewrite using `[htp f hf, ← hact]`. Conclude with `twoSigned_act M.𝒜 t hts`. Take `⟨⟨T₀, hT₀⟩, hlen, hineq⟩` from `hLM c.O (PadicAlgCl l) _ hv M.A M.𝒜 M.x M.wring M.r M.s M.r' M.s' M.m M.Q a hM1 hM2 hM3 hM4 hM5`. Establish `hpm : ∀ (f : S.R →ₐ[c.O] PadicAlgCl l) g i j, ((push f S.r.hom) g).mat i j = f ((S.r.hom g).mat i j)` using `fun f g i j => by show ((GG.map (f : S.R →+* PadicAlgCl l)) (S.r.hom g)).mat i j = _`. Rewrite using `[GG.map_mat]`.

Both sides reduce to the same expression. Establish `hpr : ∀ (f : S.R →ₐ[c.O] PadicAlgCl l) g, ((push f S.r.hom) g).right = (S.r.hom g).right` using `fun f g => GG.map_right _ _`. Establish `hext : ∀ r₁ r₂ : Γ →* GG 3 (PadicAlgCl l), (∀ g i j, (r₁ g).mat i j = (r₂ g).mat i j) → (∀ g, (r₁ g).right = (r₂ g).right) → r₁ = r₂`. Introduce `r₁ r₂ hm hr`. Apply `MonoidHom.ext` to reduce the goal to its premises.

Introduce `g`. Apply `SemidirectProduct.ext` to reduce the goal to its premises. Conclude with `Units.ext (Matrix.ext (hm g))`. Conclude with `hr g`. Establish `hac : ∀ (f f' : S.R →ₐ[c.O] PadicAlgCl l) (t : (PadicAlgCl l)ˣ), f.comp M.q = act M.𝒜 (tz t) (f'.comp M.q) → push f S.r.hom = conjBy (tor _ t) (push f' S.r.hom)`.

Introduce `f f' t h`. Apply `hext` to reduce the goal to its premises. Introduce `g i j`. Rewrite using `[(conjBy_tor _ t).1, hpm, hpm]`. Take `⟨e, he, hqe⟩` from `M.ent g i j`.

Rewrite using `[← hqe]`. Establish `h2` using `congrArg (fun φ => φ e) h`. Simplify using `only [AlgHom.comp_apply] at h2`. Rewrite using `[h2, act_tz M.𝒜 t _ he, AlgHom.comp_apply]`. Introduce `g`.

Rewrite using `[(conjBy_tor _ t).2.1, hpr, hpr]`. Establish `hch : ∀ ξ ∈ T₀, ∃ f : S.R →ₐ[c.O] PadicAlgCl l, ∃ t : (PadicAlgCl l)ˣ, IsLocPt f ∧ act M.𝒜 (tz t) ξ = f.comp M.q` using `fun ξ hξ => by`. Take `⟨t, f, h1, h2⟩` from `M.pts hM2 ξ (hT₀.1 ξ hξ).1`. Conclude with `⟨f, t, h1, h2⟩`. Use `choose F tF hF using hch`.

Set `Rel : (S.R →ₐ[c.O] PadicAlgCl l) → (S.R →ₐ[c.O] PadicAlgCl l) → Prop` to `fun f' f => ∃ t : (PadicAlgCl l)ˣ, push f S.r.hom = conjBy (tor _ t) (push f' S.r.hom)`. Establish `htrans : ∀ f₁ f₂ f₃, Rel f₁ f₂ → Rel f₂ f₃ → Rel f₁ f₃`. Introduce and unpack `f₁ f₂ f₃ ⟨t₁, h₁⟩ ⟨t₂, h₂⟩`. Conclude with `⟨t₂ * t₁, by rw [h₂, h₁, conj_conj]⟩`. Set `T₁` to `T₀.attach.image (fun ξ => F ξ.1 ξ.2)`.

Establish `hT₁ : (∀ f ∈ T₁, TwoPt η S.r.hom f) ∧ ∀ f, TwoPt η S.r.hom f → ∃ f' ∈ T₁, Rel f' f`. Prove the components needed by the constructor for the conclusion. Introduce `f hf`. Take `⟨⟨ξ, hξ⟩, -, rfl⟩` from `Finset.mem_image.1 hf`. Rewrite using `[htp _ (hF ξ hξ).1, ← (hF ξ hξ).2]`.

Conclude with `twoSigned_act M.𝒜 _ (hT₀.1 ξ hξ).2`. Introduce `f hf`. Take `⟨ξ', hξ', t, hξeq⟩` from `hT₀.2 _ (hon f) ((htp f hf.1).1 hf)`. Establish `hf'` using `hF ξ' hξ'`. Establish `hξ'' : ξ' = act M.𝒜 (tz (tF ξ' hξ')⁻¹) ((F ξ' hξ').comp M.q)`.

Rewrite using `[← hf'.2, act_act, inv_mul_cancel, act_one]`. Use `⟨F ξ' hξ', Finset.mem_image.2 ⟨⟨ξ', hξ'⟩, Finset.mem_attach _ _, rfl⟩, t * (tF ξ' hξ')⁻¹, ?_⟩` and prove the remaining obligations. Apply `hac` to reduce the goal to its premises. Rewrite using `[hξeq]`. Conclude with `(congrArg (act M.𝒜 (tz t)) hξ'').trans (act_act M.𝒜 _ _ _)`.

Take `⟨T, hTP, hirr⟩` from `exists_irred Rel htrans _ T₁ hT₁`. Use `⟨hlen, T, hTP, fun f hf f' hf' t h => hirr f hf f' hf' ⟨t, h⟩, ?_⟩` and prove the remaining obligations. Set `T'` to `T.image (fun f => f.comp M.q)`. Establish `hcov : Covers M.𝒜 M.Q.ideal T'`. Prove the components needed by the constructor for the conclusion.

Introduce `ξ hξ`. Take `⟨f, hf, rfl⟩` from `Finset.mem_image.1 hξ`. Conclude with `⟨hon f, (htp f (hTP.1 f hf).1).1 (hTP.1 f hf)⟩`. Introduce `ξ hξ hts`. Take `⟨t, f, hfl, hact⟩` from `M.pts hM2 ξ hξ`.

Establish `hf2 : TwoPt η S.r.hom f`. Rewrite using `[htp f hfl, ← hact]`. Conclude with `twoSigned_act M.𝒜 t hts`. Take `⟨f', hf', t', hpush⟩` from `hTP.2 f hf2`. Establish `hcq` using `(hsg f' (hTP.1 f' hf').1).2.2 f hfl t' hpush`.

Use `⟨f'.comp M.q, Finset.mem_image.2 ⟨f', hf', rfl⟩, t⁻¹ * t', ?_⟩` and prove the remaining obligations. Rewrite using `[← act_act, ← hcq, ← hact, act_act, inv_mul_cancel, act_one]`. Establish `hinj : Set.InjOn (fun f : S.R →ₐ[c.O] PadicAlgCl l => f.comp M.q) T`. Introduce `f hf f' hf' h`. Conclude with `hirr f hf f' hf' ⟨1, hac f' f 1 (by rw [act_one]; exact h.symm)⟩`.

Establish `hsum` using `hineq T' hcov`. Rewrite `hsum` using `[Finset.sum_image hinj]`. Simplify using `only [AlgHom.comp_apply, hqa] at hsum`. Rewrite `hsum` using `[← Finset.mul_sum]`. Establish `hepos : (0 : ℝ) < ((UpperTheory.V.Base.eO l c.O).toNat : ℝ)`.

Establish `hne : UpperTheory.V.Base.eO l c.O ≠ ⊤` using `ne_top_of_le_ne_top (ENat.coe_ne_top _) hefin`. Establish `hz : (UpperTheory.V.Base.eO l c.O).toNat ≠ 0`. Rewrite using `[Ne, ENat.toNat_eq_zero]`. Use `push_neg`. Conclude with `⟨he0, hne⟩`.

Conclude with `Nat.pos_of_ne_zero hz` after adjusting the coercions. Rewrite using `[UpperTheory.V.Chr.nrm, div_le_iff₀ hepos]`. Establish `hML : M.len = cotLen M.x M.𝒜 (-1) M.Q.F` using `rfl`. Rewrite using `[hML]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.U3.model_upper :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S (PadicAlgCl l)), l ≠ 2 → Marks η Ψ cc g₁ →
      LemmaM → Module.Finite c.O (weightZeroSubalgebra c.O S.r.hom) → PtHyp η S.r.hom M.x₀ → ∀ σ : Γ, η σ = 1 →
      (∀ f : S.R →ₐ[c.O] PadicAlgCl l, TwoPt η S.r.hom f → trDiff η Ψ S.r.hom σ f ≠ 0) →
      M.len ≠ ⊤ ∧ ∃ T : Finset (S.R →ₐ[c.O] PadicAlgCl l), CoversPt η S.r.hom T ∧
        (∀ f ∈ T, ∀ f' ∈ T, ∀ t : (PadicAlgCl l)ˣ, push f' S.r.hom = conjBy (tor _ t) (push f S.r.hom) → f = f') ∧
        UpperTheory.V.Chr.nrm l c.O M.len ≤ 2 * ∑ f ∈ T, vl l (trDiff η Ψ S.r.hom σ f) := by
  classical
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M hl hmk hLM hfin hpt σ hσ htr
  letI := M.cr
  letI := M.al
  letI := M.gr
  have hM2 := modelIdeal_finiteness_of_weightZero_finite S M hl hmk hfin
  have hM1 := gradedModel_spansCot_of_rigid_weights S M hl hmk hM2 hpt.rigid0
  have hM3 := gradedModel_pointCondition_of_ptHyp S M hl hmk hM2 hpt
  have hM4 := gradedModel_derivationCondition_of_ptHyp S M hl hmk hM2 hpt
  have hsg := model_signs S M hl hmk
  have hv := isNVal l c
  obtain ⟨-, -, -, hcomp, -, he0, hefin, -, -⟩ := UpperTheory.V.Base.dvrFacts l c.O
  haveI := hcomp
  have htp : ∀ f : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f →
      (TwoPt η S.r.hom f ↔ TwoSigned M.𝒜 (f.comp M.q)) := fun f hf =>
    ⟨fun h => ⟨fun hn => h.2.1 ((hsg f hf).1.1 hn), fun hp => h.2.2 ((hsg f hf).2.1.1 hp)⟩,
     fun h => ⟨hf, fun hu => h.1 ((hsg f hf).1.2 hu), fun hw => h.2 ((hsg f hf).2.1.2 hw)⟩⟩
  have hon : ∀ f : S.R →ₐ[c.O] PadicAlgCl l, OnS M.Q.ideal (f.comp M.q) := by
    intro f y hy
    have hy' : y ∈ RingHom.ker M.q := by rw [M.ker_q]; exact hy
    rw [AlgHom.comp_apply, RingHom.mem_ker.1 hy', map_zero]
  choose E hE hqE using M.ent σ
  have hmem : ∀ i, E i i ∈ M.𝒜 0 := fun i => by
    have := hE i i
    simpa [wt] using this
  set a : M.A := E 0 0 + E 1 1 + E 2 2 - algebraMap c.O M.A ((r0 η Ψ σ).mat.trace) with ha
  have ha0 : a ∈ M.𝒜 0 :=
    Submodule.sub_mem _ (add_mem (add_mem (hmem 0) (hmem 1)) (hmem 2)) (SetLike.algebraMap_mem_graded M.𝒜 _)
  have hqa : ∀ f : S.R →ₐ[c.O] PadicAlgCl l, f (M.q a) = trDiff η Ψ S.r.hom σ f := by
    intro f
    simp [ha, hqE, trDiff, Matrix.trace_fin_three]
  have hb : (r0 η Ψ σ).mat = (S.r.hom σ).mat.map M.x₀ := by
    rw [← M.base]
    exact GG.map_mat _ _
  have hxa : M.x a = 0 := by
    rw [← M.x₀_q, AlgHom.comp_apply]
    simp [ha, hqE, hb, Matrix.trace_fin_three]
  have hM5 : M5 M.𝒜 (PadicAlgCl l) M.x M.Q.ideal a := by
    refine ⟨ha0, hxa, fun ξ hξ hts => ?_⟩
    obtain ⟨t, f, hf, hact⟩ := M.pts hM2 ξ hξ
    have h1 := congrArg (fun g => g a) hact
    simp only [AlgHom.comp_apply] at h1
    rw [act_tz M.𝒜 t ξ ha0, zpow_zero, Units.val_one, one_mul, hqa] at h1
    rw [h1]
    apply htr f
    rw [htp f hf, ← hact]
    exact twoSigned_act M.𝒜 t hts
  obtain ⟨⟨T₀, hT₀⟩, hlen, hineq⟩ := hLM c.O (PadicAlgCl l) _ hv M.A M.𝒜 M.x M.wring M.r M.s M.r' M.s' M.m
    M.Q a hM1 hM2 hM3 hM4 hM5
  have hpm : ∀ (f : S.R →ₐ[c.O] PadicAlgCl l) g i j,
      ((push f S.r.hom) g).mat i j = f ((S.r.hom g).mat i j) := fun f g i j => by
    show ((GG.map (f : S.R →+* PadicAlgCl l)) (S.r.hom g)).mat i j = _
    rw [GG.map_mat]
    rfl
  have hpr : ∀ (f : S.R →ₐ[c.O] PadicAlgCl l) g, ((push f S.r.hom) g).right = (S.r.hom g).right :=
    fun f g => GG.map_right _ _
  have hext : ∀ r₁ r₂ : Γ →* GG 3 (PadicAlgCl l), (∀ g i j, (r₁ g).mat i j = (r₂ g).mat i j) →
      (∀ g, (r₁ g).right = (r₂ g).right) → r₁ = r₂ := by
    intro r₁ r₂ hm hr
    apply MonoidHom.ext
    intro g
    apply SemidirectProduct.ext
    · exact Units.ext (Matrix.ext (hm g))
    · exact hr g
  have hac : ∀ (f f' : S.R →ₐ[c.O] PadicAlgCl l) (t : (PadicAlgCl l)ˣ),
      f.comp M.q = act M.𝒜 (tz t) (f'.comp M.q) →
      push f S.r.hom = conjBy (tor _ t) (push f' S.r.hom) := by
    intro f f' t h
    apply hext
    · intro g i j
      rw [(conjBy_tor _ t).1, hpm, hpm]
      obtain ⟨e, he, hqe⟩ := M.ent g i j
      rw [← hqe]
      have h2 := congrArg (fun φ => φ e) h
      simp only [AlgHom.comp_apply] at h2
      rw [h2, act_tz M.𝒜 t _ he, AlgHom.comp_apply]
    · intro g
      rw [(conjBy_tor _ t).2.1, hpr, hpr]
  have hch : ∀ ξ ∈ T₀, ∃ f : S.R →ₐ[c.O] PadicAlgCl l, ∃ t : (PadicAlgCl l)ˣ,
      IsLocPt f ∧ act M.𝒜 (tz t) ξ = f.comp M.q := fun ξ hξ => by
    obtain ⟨t, f, h1, h2⟩ := M.pts hM2 ξ (hT₀.1 ξ hξ).1
    exact ⟨f, t, h1, h2⟩
  choose F tF hF using hch
  let Rel : (S.R →ₐ[c.O] PadicAlgCl l) → (S.R →ₐ[c.O] PadicAlgCl l) → Prop :=
    fun f' f => ∃ t : (PadicAlgCl l)ˣ, push f S.r.hom = conjBy (tor _ t) (push f' S.r.hom)
  have htrans : ∀ f₁ f₂ f₃, Rel f₁ f₂ → Rel f₂ f₃ → Rel f₁ f₃ := by
    rintro f₁ f₂ f₃ ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
    exact ⟨t₂ * t₁, by rw [h₂, h₁, conj_conj]⟩
  let T₁ := T₀.attach.image (fun ξ => F ξ.1 ξ.2)
  have hT₁ : (∀ f ∈ T₁, TwoPt η S.r.hom f) ∧ ∀ f, TwoPt η S.r.hom f → ∃ f' ∈ T₁, Rel f' f := by
    constructor
    · intro f hf
      obtain ⟨⟨ξ, hξ⟩, -, rfl⟩ := Finset.mem_image.1 hf
      rw [htp _ (hF ξ hξ).1, ← (hF ξ hξ).2]
      exact twoSigned_act M.𝒜 _ (hT₀.1 ξ hξ).2
    · intro f hf
      obtain ⟨ξ', hξ', t, hξeq⟩ := hT₀.2 _ (hon f) ((htp f hf.1).1 hf)
      have hf' := hF ξ' hξ'
      have hξ'' : ξ' = act M.𝒜 (tz (tF ξ' hξ')⁻¹) ((F ξ' hξ').comp M.q) := by
        rw [← hf'.2, act_act, inv_mul_cancel, act_one]
      refine ⟨F ξ' hξ', Finset.mem_image.2 ⟨⟨ξ', hξ'⟩, Finset.mem_attach _ _, rfl⟩, t * (tF ξ' hξ')⁻¹, ?_⟩
      apply hac
      rw [hξeq]
      exact (congrArg (act M.𝒜 (tz t)) hξ'').trans (act_act M.𝒜 _ _ _)
  obtain ⟨T, hTP, hirr⟩ := exists_irred Rel htrans _ T₁ hT₁
  refine ⟨hlen, T, hTP, fun f hf f' hf' t h => hirr f hf f' hf' ⟨t, h⟩, ?_⟩
  let T' := T.image (fun f => f.comp M.q)
  have hcov : Covers M.𝒜 M.Q.ideal T' := by
    constructor
    · intro ξ hξ
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hξ
      exact ⟨hon f, (htp f (hTP.1 f hf).1).1 (hTP.1 f hf)⟩
    · intro ξ hξ hts
      obtain ⟨t, f, hfl, hact⟩ := M.pts hM2 ξ hξ
      have hf2 : TwoPt η S.r.hom f := by
        rw [htp f hfl, ← hact]
        exact twoSigned_act M.𝒜 t hts
      obtain ⟨f', hf', t', hpush⟩ := hTP.2 f hf2
      have hcq := (hsg f' (hTP.1 f' hf').1).2.2 f hfl t' hpush
      refine ⟨f'.comp M.q, Finset.mem_image.2 ⟨f', hf', rfl⟩, t⁻¹ * t', ?_⟩
      rw [← act_act, ← hcq, ← hact, act_act, inv_mul_cancel, act_one]
  have hinj : Set.InjOn (fun f : S.R →ₐ[c.O] PadicAlgCl l => f.comp M.q) T := by
    intro f hf f' hf' h
    exact hirr f hf f' hf' ⟨1, hac f' f 1 (by rw [act_one]; exact h.symm)⟩
  have hsum := hineq T' hcov
  rw [Finset.sum_image hinj] at hsum
  simp only [AlgHom.comp_apply, hqa] at hsum
  rw [← Finset.mul_sum] at hsum
  have hepos : (0 : ℝ) < ((UpperTheory.V.Base.eO l c.O).toNat : ℝ) := by
    have hne : UpperTheory.V.Base.eO l c.O ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hefin
    have hz : (UpperTheory.V.Base.eO l c.O).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero]
      push_neg
      exact ⟨he0, hne⟩
    exact_mod_cast Nat.pos_of_ne_zero hz
  rw [UpperTheory.V.Chr.nrm, div_le_iff₀ hepos]
  have hML : M.len = cotLen M.x M.𝒜 (-1) M.Q.F := rfl
  rw [hML]
  linarith
