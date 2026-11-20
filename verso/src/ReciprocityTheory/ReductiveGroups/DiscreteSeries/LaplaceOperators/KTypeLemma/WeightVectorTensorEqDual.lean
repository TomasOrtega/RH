import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RealSmulCj

noncomputable section

open Finset Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def lamd (lam : Fin n → ℝ) : Fin n → ℝ := fun a => -lam (Fin.rev a)

/- English proof (translation)
Apply the tactic sequence `apply Finset.card_bij' (fun b _ => Fin.rev b) (fun b _ => Fin.rev b) <;> simp [h]`.
-/
theorem card_eq_of_rev (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ b, P b ↔ Q (Fin.rev b)) : (univ.filter P).card = (univ.filter Q).card := by
  apply Finset.card_bij' (fun b _ => Fin.rev b) (fun b _ => Fin.rev b) <;> simp [h]

/- English proof (translation)
Establish `h1 : (univ.filter fun b => a < b ∧ (ε ∘ Fin.rev) b ≠ (ε ∘ Fin.rev) a).card = (univ.filter fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a)).card` using `card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]`. Establish `h2 : (univ.filter fun b => b < a ∧ (ε ∘ Fin.rev) b ≠ (ε ∘ Fin.rev) a).card = (univ.filter fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a)).card` using `card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]`. Unfold `rhoN`. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rhoN_rev (ε : Fin n → Bool) (a : Fin n) : rhoN (ε ∘ Fin.rev) a = -rhoN ε (Fin.rev a) := by
  have h1 : (univ.filter fun b => a < b ∧ (ε ∘ Fin.rev) b ≠ (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  have h2 : (univ.filter fun b => b < a ∧ (ε ∘ Fin.rev) b ≠ (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  unfold rhoN
  rw [h1, h2]
  ring

/- English proof (translation)
Establish `h1 : (univ.filter fun b => a < b ∧ (ε ∘ Fin.rev) b = (ε ∘ Fin.rev) a).card = (univ.filter fun b => b < Fin.rev a ∧ ε b = ε (Fin.rev a)).card` using `card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]`. Establish `h2 : (univ.filter fun b => b < a ∧ (ε ∘ Fin.rev) b = (ε ∘ Fin.rev) a).card = (univ.filter fun b => Fin.rev a < b ∧ ε b = ε (Fin.rev a)).card` using `card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]`. Unfold `rhoC`. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rhoC_rev (ε : Fin n → Bool) (a : Fin n) : rhoC (ε ∘ Fin.rev) a = -rhoC ε (Fin.rev a) := by
  have h1 : (univ.filter fun b => a < b ∧ (ε ∘ Fin.rev) b = (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => b < Fin.rev a ∧ ε b = ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  have h2 : (univ.filter fun b => b < a ∧ (ε ∘ Fin.rev) b = (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => Fin.rev a < b ∧ ε b = ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  unfold rhoC
  rw [h1, h2]
  ring

/- English proof (translation)
Simplify using `only [lowK, Pi.add_apply, Pi.sub_apply, lamd, rhoN_rev, rhoC_rev]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lowK_rev (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    lowK (ε ∘ Fin.rev) (lamd lam) a = -lowK ε lam (Fin.rev a) := by
  simp only [lowK, Pi.add_apply, Pi.sub_apply, lamd, rhoN_rev, rhoC_rev]
  ring

/- English proof (translation)
Unfold `casVal nsq dot`. Simplify using `only [lamd, neg_mul_neg]`. Use `congr 1`. Conclude with `Equiv.sum_comp Fin.revPerm (fun a => lam a * lam a)`.
-/
theorem casVal_rev (lam : Fin n → ℝ) : casVal (lamd lam) = casVal lam := by
  unfold casVal nsq dot
  simp only [lamd, neg_mul_neg]
  congr 1
  exact Equiv.sum_comp Fin.revPerm (fun a => lam a * lam a)

/- English proof (translation)
The claim follows from `card_eq_of_rev _ _ fun b => by simp`.
-/
theorem pOf_rev (ε : Fin n → Bool) : pOf (ε ∘ Fin.rev) = pOf ε :=
  card_eq_of_rev _ _ fun b => by simp

/- English proof (translation)
The claim follows from `card_eq_of_rev _ _ fun b => by simp`.
-/
theorem qOf_rev (ε : Fin n → Bool) : qOf (ε ∘ Fin.rev) = qOf ε :=
  card_eq_of_rev _ _ fun b => by simp

/- English proof (translation)
Unfold `hNeed`. Rewrite using `[pOf_rev, qOf_rev]`.
-/
theorem hNeed_rev (ε : Fin n → Bool) : hNeed (ε ∘ Fin.rev) = hNeed ε := by
  unfold hNeed; rw [pOf_rev, qOf_rev]

/- English proof (translation)
Take `⟨hanti, hgap, hh⟩` from `hg`. Use `⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a b hab => ?_, by rwa [hNeed_rev]⟩` and prove the remaining obligations. Use `hgap (Fin.rev a) (Fin.rev b) hab` as an intermediate fact. Rewrite using `[show lamd lam a - lamd lam b = -(lam (Fin.rev a) - lam (Fin.rev b)) by simp only [lamd]; ring, abs_neg]`. Conclude with `this`.
-/
theorem gapLap_rev {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hg : GapLap ε lam h) :
    GapLap (ε ∘ Fin.rev) (lamd lam) h := by
  obtain ⟨hanti, hgap, hh⟩ := hg
  refine ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a b hab => ?_, by rwa [hNeed_rev]⟩
  have := hgap (Fin.rev a) (Fin.rev b) hab
  rw [show lamd lam a - lamd lam b = -(lam (Fin.rev a) - lam (Fin.rev b)) by simp only [lamd]; ring, abs_neg]
  exact this

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

def cjV (V : Submodule ℂ D) : Submodule ℂ (cjSub D) := V.map (ofDL (D := D))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `hu`. Introduce `h`. Conclude with `⟨toD x, h, rfl⟩`.
-/
theorem mem_cjV {V : Submodule ℂ D} (x : cjSub D) : x ∈ cjV V ↔ toD x ∈ V := by
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro h; exact ⟨toD x, h, rfl⟩

/- English proof (translation)
Rewrite using `[Edd_ofD, smul_ofD, Fin.rev_rev, Fin.rev_rev, smul_smul]`. Establish `h1 : conj (-(sg ε (Fin.rev b) * sg ε (Fin.rev a))) * -(sg ε (Fin.rev b) * sg ε (Fin.rev a)) = 1`. Simplify using `only [map_neg, map_mul, conj_sg]`. Take the linear combination `(sg ε (Fin.rev a) * sg ε (Fin.rev a)) * sg_sq ε (Fin.rev b) + sg_sq ε (Fin.rev a)`. Rewrite using `[h1, one_smul]`.
-/
theorem ofD_E (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (u : D) :
    ofD (E a b u) = (-(sg ε (Fin.rev b) * sg ε (Fin.rev a))) • Edd ε E (Fin.rev b) (Fin.rev a) (ofD u) := by
  rw [Edd_ofD, smul_ofD, Fin.rev_rev, Fin.rev_rev, smul_smul]
  have h1 : conj (-(sg ε (Fin.rev b) * sg ε (Fin.rev a))) * -(sg ε (Fin.rev b) * sg ε (Fin.rev a)) = 1 := by
    simp only [map_neg, map_mul, conj_sg]
    linear_combination (sg ε (Fin.rev a) * sg ε (Fin.rev a)) * sg_sq ε (Fin.rev b) + sg_sq ε (Fin.rev a)
  rw [h1, one_smul]

/- English proof (translation)
Take `⟨hfin, hst, hirr, w, hwV, hw0, hwa, hwb⟩` from `hV`. Use `⟨?_, ?_, ?_, ofD w, (mem_cjV _).2 hwV, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hfg : V.FG` using `Module.Finite.iff_fg.mp hfin`. Conclude with `Module.Finite.iff_fg.mpr (hfg.map _)`. Introduce `a b hab v hv`.

Rewrite `hv`, the goal using `[mem_cjV]`. Conclude with `V.smul_mem _ (hst (Fin.rev b) (Fin.rev a) hab.symm _ hv)`. Introduce `S' hle hS'`. Establish `hSle : S'.comap (ofDL (D` using `D)) ≤ V := fun u hu => (mem_cjV (ofD u)).1 (hle hu)`. Establish `hSst : IsKStableSub ε E (S'.comap (ofDL (D` using `D))) := by`.

Introduce `a b hab u hu`. Use `show ofD (E a b u) ∈ S'`. Rewrite using `[ofD_E ε E a b u]`. Use `S'.smul_mem _ (hS' _ _ ?_ _ hu)` and prove the remaining obligations. Simplify using `[hab]`.

Break down `hirr _ hSle hSst with h0 | h1` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `: toD x ∈ S'.comap (ofDL (D` using `D)) := hx`.

Rewrite `this` using `[h0, Submodule.mem_bot]`. Rewrite using `[Submodule.mem_bot, ← ofD_toD x, this]`. Both sides reduce to the same expression. Use `right`. Use `le_antisymm hle fun x hx => ?_` and prove the remaining obligations.

Establish `: toD x ∈ S'.comap (ofDL (D` using `D)) := by rw [h1]; exact (mem_cjV x).1 hx`. Conclude with `this`. Introduce `h`. Apply `hw0` to reduce the goal to its premises. Apply `ofD_injective` to reduce the goal to its premises.

Rewrite using `[h]`. Both sides reduce to the same expression. Introduce `a`. Rewrite using `[Edd_ofD, hwa, smul_smul, sg_sq, smul_ofD, lowK_rev]`. Use `congr 1`.

Use `push_cast`. Simplify using the standard rewrite rules. Introduce `a b hab hε`. Rewrite using `[Edd_ofD, hwb _ _ (Fin.rev_lt_rev.mpr hab) hε.symm, smul_zero]`. Both sides reduce to the same expression.
-/
theorem kirr_cjV {ε : Fin n → Bool} {lam : Fin n → ℝ} {E : Fin n → Fin n → Module.End ℂ D}
    {V : Submodule ℂ D} (hV : IsKIrrHW ε E (lowK ε lam) V) :
    IsKIrrHW (ε ∘ Fin.rev) (Edd ε E) (lowK (ε ∘ Fin.rev) (lamd lam)) (cjV V) := by
  obtain ⟨hfin, hst, hirr, w, hwV, hw0, hwa, hwb⟩ := hV
  refine ⟨?_, ?_, ?_, ofD w, (mem_cjV _).2 hwV, ?_, ?_, ?_⟩
  · have hfg : V.FG := Module.Finite.iff_fg.mp hfin
    exact Module.Finite.iff_fg.mpr (hfg.map _)
  · intro a b hab v hv
    rw [mem_cjV] at hv ⊢
    exact V.smul_mem _ (hst (Fin.rev b) (Fin.rev a) hab.symm _ hv)
  · intro S' hle hS'
    have hSle : S'.comap (ofDL (D := D)) ≤ V := fun u hu => (mem_cjV (ofD u)).1 (hle hu)
    have hSst : IsKStableSub ε E (S'.comap (ofDL (D := D))) := by
      intro a b hab u hu
      show ofD (E a b u) ∈ S'
      rw [ofD_E ε E a b u]
      refine S'.smul_mem _ (hS' _ _ ?_ _ hu)
      simp [hab]
    rcases hirr _ hSle hSst with h0 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have : toD x ∈ S'.comap (ofDL (D := D)) := hx
      rw [h0, Submodule.mem_bot] at this
      rw [Submodule.mem_bot, ← ofD_toD x, this]
      rfl
    · right
      refine le_antisymm hle fun x hx => ?_
      have : toD x ∈ S'.comap (ofDL (D := D)) := by rw [h1]; exact (mem_cjV x).1 hx
      exact this
  · intro h
    apply hw0
    apply ofD_injective
    rw [h]; rfl
  · intro a
    rw [Edd_ofD, hwa, smul_smul, sg_sq, smul_ofD, lowK_rev]
    congr 1
    push_cast
    simp
  · intro a b hab hε
    rw [Edd_ofD, hwb _ _ (Fin.rev_lt_rev.mpr hab) hε.symm, smul_zero]
    rfl

/- English proof (translation)
Unfold `casimir`. Simplify using `only [LinearMap.sum_apply, Module.End.mul_apply, Edd_ofD, ofD_sum, LinearMap.map_smul, smul_smul]`. Use `conv_lhs => rw [sum_rev_swap]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.rev_rev]`.

Establish `h1 : -(sg ε (Fin.rev b) * sg ε (Fin.rev a)) * -(sg ε (Fin.rev a) * sg ε (Fin.rev b)) = 1`. Take the linear combination `(sg ε (Fin.rev a) * sg ε (Fin.rev a)) * sg_sq ε (Fin.rev b) + sg_sq ε (Fin.rev a)`. Rewrite using `[h1, one_smul]`.
-/
theorem casimir_Edd (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (u : D) :
    casimir (Edd ε E) (ofD u) = ofD (casimir E u) := by
  unfold casimir
  simp only [LinearMap.sum_apply, Module.End.mul_apply, Edd_ofD, ofD_sum, LinearMap.map_smul, smul_smul]
  conv_lhs => rw [sum_rev_swap]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Fin.rev_rev]
  have h1 : -(sg ε (Fin.rev b) * sg ε (Fin.rev a)) * -(sg ε (Fin.rev a) * sg ε (Fin.rev b)) = 1 := by
    linear_combination (sg ε (Fin.rev a) * sg ε (Fin.rev a)) * sg_sq ε (Fin.rev b) + sg_sq ε (Fin.rev a)
  rw [h1, one_smul]

/- English proof (translation)
The claim follows from `le_sInf fun _ hT => hT.1`.
-/
theorem le_genSub' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (S : Submodule ℂ M) : S ≤ genSub E S := le_sInf fun _ hT => hT.1

/- English proof (translation)
Unfold `genSub at hv ⊢`. Rewrite `hv`, the goal using `[Submodule.mem_sInf]`. Introduce `T hT`. Conclude with `hT.2 a b v (hv T hT)`.
-/
theorem genSub_stable' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (S : Submodule ℂ M) (a b : Fin n) {v : M} (hv : v ∈ genSub E S) : E a b v ∈ genSub E S := by
  unfold genSub at hv ⊢
  rw [Submodule.mem_sInf] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)

/- English proof (translation)
The claim follows from `sInf_le ⟨hS, hT⟩`.
-/
theorem genSub_le' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    {S T : Submodule ℂ M} (hS : S ≤ T) (hT : ∀ a b, ∀ v ∈ T, E a b v ∈ T) : genSub E S ≤ T :=
  sInf_le ⟨hS, hT⟩

/- English proof (translation)
Establish `hle : genSub E V ≤ (genSub (Edd ε E) (cjV V)).comap (ofDL (D` using `D)) := by`. Use `genSub_le' E (fun v hv => (le_genSub' (Edd ε E) (cjV V) ((mem_cjV (ofD v)).2 hv) : ofD v ∈ genSub (Edd ε E) (cjV V))) fun a b v hv => ?_` and prove the remaining obligations. Use `show ofD (E a b v) ∈ _`. Rewrite using `[ofD_E ε E a b v]`. Conclude with `Submodule.smul_mem _ _ (genSub_stable' (Edd ε E) (cjV V) _ _ (hv : ofD v ∈ genSub (Edd ε E) (cjV V)))`.

Conclude with `hle hu`.
-/
theorem mem_genSub_Edd (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) {u : D}
    (hu : u ∈ genSub E V) : ofD u ∈ genSub (Edd ε E) (cjV V) := by
  have hle : genSub E V ≤ (genSub (Edd ε E) (cjV V)).comap (ofDL (D := D)) := by
    refine genSub_le' E (fun v hv => (le_genSub' (Edd ε E) (cjV V) ((mem_cjV (ofD v)).2 hv) : ofD v ∈ genSub (Edd ε E) (cjV V))) fun a b v hv => ?_
    show ofD (E a b v) ∈ _
    rw [ofD_E ε E a b v]
    exact Submodule.smul_mem _ _ (genSub_stable' (Edd ε E) (cjV V) _ _ (hv : ofD v ∈ genSub (Edd ε E) (cjV V)))
  exact hle hu

def Tf (ε : Fin n → Bool) (f : Fin n → D) : Fin n → cjSub D := fun c => ofD (sg ε c • f (Fin.rev c))

def Tfh (ε : Fin n → Bool) : (Fin n → D) →+ (Fin n → cjSub D) where
  toFun := Tf ε
  map_zero' := by
    funext c
    show ofD (sg ε c • (0 : D)) = 0
    rw [smul_zero]; rfl
  map_add' f g := by
    funext c
    show ofD (sg ε c • (f (Fin.rev c) + g (Fin.rev c))) = ofD (sg ε c • f (Fin.rev c)) + ofD (sg ε c • g (Fin.rev c))
    rw [smul_add, ofD_add]

/- English proof (translation)
Use function extensionality and compare the values at `c`. Use `show ofD (sg ε c • (z • f (Fin.rev c))) = conj z • ofD (sg ε c • f (Fin.rev c))`. Rewrite using `[smul_ofD, Complex.conj_conj, smul_comm]`.
-/
theorem Tf_smul (ε : Fin n → Bool) (z : ℂ) (f : Fin n → D) : Tfh ε (z • f) = conj z • Tfh ε f := by
  funext c
  show ofD (sg ε c • (z • f (Fin.rev c))) = conj z • ofD (sg ε c • f (Fin.rev c))
  rw [smul_ofD, Complex.conj_conj, smul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `c`. Establish `h1` using `congrFun h (Fin.rev c)`. Simplify using `only [Tf, Fin.rev_rev, Pi.zero_apply] at h1`. Establish `h2 : sg ε (Fin.rev c) • g c = 0` using `ofD_injective (h1.trans ofD_zero.symm)`. Conclude with `(smul_eq_zero.mp h2).resolve_left (sg_ne ε _)`.
-/
theorem Tf_inj (ε : Fin n → Bool) {g : Fin n → D} (h : Tf ε g = 0) : g = 0 := by
  funext c
  have h1 := congrFun h (Fin.rev c)
  simp only [Tf, Fin.rev_rev, Pi.zero_apply] at h1
  have h2 : sg ε (Fin.rev c) • g c = 0 := ofD_injective (h1.trans ofD_zero.symm)
  exact (smul_eq_zero.mp h2).resolve_left (sg_ne ε _)

/- English proof (translation)
Use function extensionality and compare the values at `d`. Simplify using `only [Tf, eeV, eeVd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.neg_apply, LinearMap.comp_apply, prj, LinearMap.proj_apply, Edd_ofD, LinearMap.map_smul, smul_smul]`. Rewrite using `[← ofD_sum]`. Use `congr 1`. Rewrite using `[smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]`.

Use `conv_rhs => rw [← Equiv.sum_comp Fin.revPerm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.revPerm_apply]`. Rewrite using `[← neg_smul]`. Use `congr 1`.

Take the linear combination `(-sg ε d) * sg_sq ε c`.
-/
theorem weightVector_tensor_eq_dual (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (f : Fin n → D) :
    eeV (Edd ε E) (Tf ε f) = Tf ε (eeVd E f) := by
  funext d
  simp only [Tf, eeV, eeVd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, prj, LinearMap.proj_apply, Edd_ofD, LinearMap.map_smul, smul_smul]
  rw [← ofD_sum]
  congr 1
  rw [smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
  conv_rhs => rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Fin.revPerm_apply]
  rw [← neg_smul]
  congr 1
  linear_combination (-sg ε d) * sg_sq ε c

/- English proof (translation)
Unfold `prodShift`. Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression.
-/
theorem prodShift_eq {X : Type*} [AddCommGroup X] [Module ℂ X] (A : Module.End ℂ X) (θ : Fin n → ℝ) :
    prodShift A θ = ((List.ofFn θ).map fun r : ℝ => A - ((r : ℝ) : ℂ) • (1 : Module.End ℂ X)).prod := by
  unfold prodShift; rw [List.map_ofFn]; rfl

/- English proof (translation)
Rewrite using `[← List.prod_ofFn, map_list_prod, List.map_ofFn]`. Unfold `prodShift`. Use `congr 2`. Use function extensionality and compare the values at `t`. Simplify using `[Algebra.algebraMap_eq_smul_one]`.
-/
theorem prodShift_aeval {X : Type*} [AddCommGroup X] [Module ℂ X] (A : Module.End ℂ X) (θ : Fin n → ℝ) :
    prodShift A θ = Polynomial.aeval A (∏ t, (Polynomial.X - Polynomial.C ((θ t : ℝ) : ℂ))) := by
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  unfold prodShift
  congr 2
  funext t
  simp [Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Rewrite using `[prodShift_aeval, prodShift_aeval]`. Use `congr 1`. Conclude with `Equiv.prod_comp Fin.revPerm (fun t => Polynomial.X - Polynomial.C ((θ t : ℝ) : ℂ))`.
-/
theorem prodShift_rev {X : Type*} [AddCommGroup X] [Module ℂ X] (A : Module.End ℂ X) (θ : Fin n → ℝ) :
    prodShift A (fun t => θ (Fin.rev t)) = prodShift A θ := by
  rw [prodShift_aeval, prodShift_aeval]
  congr 1
  exact Equiv.prod_comp Fin.revPerm (fun t => Polynomial.X - Polynomial.C ((θ t : ℝ) : ℂ))

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons r L ih`. Simplify using `only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`. Rewrite using `[map_sub, hAB, hs, Complex.conj_ofReal, ih]`.
-/
theorem list_inter {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (T : X →+ Y) (hs : ∀ (z : ℂ) (x : X), T (z • x) = conj z • T x) (A : Module.End ℂ Y)
    (B : Module.End ℂ X) (hAB : ∀ x, T (B x) = A (T x)) (L : List ℝ) (x : X) :
    T ((L.map fun r : ℝ => B - ((r : ℝ) : ℂ) • (1 : Module.End ℂ X)).prod x) =
      (L.map fun r : ℝ => A - ((r : ℝ) : ℂ) • (1 : Module.End ℂ Y)).prod (T x) := by
  induction L with
  | nil => simp
  | cons r L ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply]
    rw [map_sub, hAB, hs, Complex.conj_ofReal, ih]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal
