import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfUnimodular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearFormsBoundedRepresentatives
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe

noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.FrameMove

open GlobalTheory.EichlerUnip GlobalTheory.LoopC.FrEqv

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
  {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T}

/- English proof (translation)
Simplify using `[frame, FlagG.fvec]`.
-/
theorem frame_cast (F : LFlag S r T) (a : Fin r) : frame F a.castSucc = F.fl.e a := by
  simp [frame, FlagG.fvec]

/- English proof (translation)
Simplify using `[frame, FlagG.fvec]`.
-/
theorem frame_last (F : LFlag S r T) : frame F (Fin.last r) = F.fl.z := by
  simp [frame, FlagG.fvec]

/- English proof (translation)
Introduce `x hx`. Use `LinearMap.eqOn_span (s := F.fl.e '' {i | i.1 < j}) ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Use `h a.castSucc ha` as an intermediate fact. Rewrite `this` using `[frame_cast]`. Then use the resulting hypothesis.
-/
theorem ext_Xflag {W : Type} [AddCommGroup W] [Module E W] (f g : S.V →ₗ[E] W) (j : ℕ)
    (h : ∀ a : Fin (r + 1), a.val < j → f (frame F a) = g (frame F a)) :
    ∀ x ∈ Xflag F j, f x = g x := by
  intro x hx
  refine LinearMap.eqOn_span (s := F.fl.e '' {i | i.1 < j}) ?_ hx
  rintro _ ⟨a, ha, rfl⟩
  have := h a.castSucc ha
  rwa [frame_cast] at this

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_subset_range _ _)`.
-/
theorem Xflag_le_X (j : ℕ) : Xflag F j ≤ Xsp F := Submodule.span_mono (Set.image_subset_range _ _)

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)`.
-/
theorem Xflag_mono' {i j : ℕ} (h : i ≤ j) : Xflag F i ≤ Xflag F j :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

/- English proof (translation)
Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`. Rewrite using `[frame_last]`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨a, rfl⟩ := hx`.

Conclude with `F.fl.z_orth a`. Consider the case `zero => simp`. Consider the case `add x y _ _ h1 h2 => simp [h1, h2]`. Consider the case `smul c x _ h => simp [h]`. Consider the case `cast a`.

Rewrite using `[frame_cast]`. Conclude with `iso_X S F hw (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem X_orth_frame {w : S.V} (hw : w ∈ Xsp F) (j : Fin (r + 1)) : S.hT w (frame F j) = 0 := by
  induction j using Fin.lastCases with
  | last =>
    rw [frame_last]
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact F.fl.z_orth a
    | zero => simp
    | add x y _ _ h1 h2 => simp [h1, h2]
    | smul c x _ h => simp [h]
  | cast a =>
    rw [frame_cast]
    exact iso_X S F hw (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `h1 : c (Fin.last r) = 0`. Use `congrArg (S.hT F.fl.z) hc` as an intermediate fact. Establish `h0 : ∀ a, S.hT F.fl.z (F.fl.e a) = 0` using `fun a => by`.

Rewrite using `[herm S, F.fl.z_orth, star_zero]`. Rewrite `this` using `[Fin.sum_univ_castSucc]`. Simplify `this` using `[frame_cast, frame_last, map_sum, h0, F.fl.z_norm, hT]`. Rewrite `hc` using `[Fin.sum_univ_castSucc, h1, zero_smul, add_zero]`. Simplify using `only [frame_cast] at hc`.

Establish `h2` using `Fintype.linearIndependent_iff.1 F.fl.e_indep _ hc`. Introduce `i`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => exact h1`. Consider the case `cast a => exact h2 a`.
-/
theorem frame_indep (hT : T ≠ 0) : LinearIndependent E (frame F) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 : c (Fin.last r) = 0 := by
    have := congrArg (S.hT F.fl.z) hc
    have h0 : ∀ a, S.hT F.fl.z (F.fl.e a) = 0 := fun a => by
      rw [herm S, F.fl.z_orth, star_zero]
    rw [Fin.sum_univ_castSucc] at this
    simpa [frame_cast, frame_last, map_sum, h0, F.fl.z_norm, hT] using this
  rw [Fin.sum_univ_castSucc, h1, zero_smul, add_zero] at hc
  simp only [frame_cast] at hc
  have h2 := Fintype.linearIndependent_iff.1 F.fl.e_indep _ hc
  intro i
  induction i using Fin.lastCases with
  | last => exact h1
  | cast a => exact h2 a

/- English proof (translation)
Establish `hli : LinearIndependent E (frame F)` using `frame_indep hT`. Use `set U := Submodule.span E (Set.range (frame F))`. Take `⟨φ, hφ⟩` from `LinearMap.exists_extend (p := U) ((Basis.span hli).constr E fun j => if j = b then s else 0)`. Establish `hφ' : ∀ j, φ (frame F j) = if j = b then s else 0`. Introduce `j`.

Use `LinearMap.congr_fun hφ (Basis.span hli j)` as an intermediate fact. Rewrite `this` using `[Basis.constr_basis]`. Rewrite using `[← this]`. Simplify using `[Basis.span_apply]`. Use `set M0 : Submodule (𝓞 E) S.V := Λ ⊓ toO S U`.

Establish `hprim : IsPrimitiveSub M0 Λ`. Use `⟨inf_le_left, le_antisymm (le_inf inf_le_left fun x hx => Submodule.subset_span hx) ?_⟩` and prove the remaining obligations. Use `inf_le_inf_left _ ?_` and prove the remaining obligations. Introduce `x hx`. Conclude with `(Submodule.span_le (p := U)).2 (fun y hy => hy.2) hx`.

Establish `hint : ∀ x : M0, ∃ o : 𝓞 E, (o : E) = φ x`. Introduce and unpack `⟨x, hx, hxU⟩`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hxU`. Establish `h1` using `FractionalIdeal.mul_mem_mul ((hc c).1 hx b) hs`. Rewrite `h1` using `[mul_inv_cancel₀ (h0 b), FractionalIdeal.mem_one_iff]`.

Take `⟨o, ho⟩` from `h1`. Use `⟨o, ?_⟩` and prove the remaining obligations. Simplify using `[map_sum, hφ', ← ho]`. Use `choose ψ hψ using hint`. Set `ψ' : M0 →ₗ[𝓞 E] 𝓞 E` to `{ toFun := ψ map_add' := fun x y => by`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `[hψ]`. Use the proof step `map_smul' := fun c x => by`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `only [hψ, RingHom.id_apply, smul_eq_mul, map_mul, Submodule.coe_smul]`.

Rewrite using `[← algebraMap_smul E c (x : S.V), map_smul]`. Simplify using `[hψ] }`. Take `⟨w, hw⟩` from `FunIdx.exists_dual_vec S M0 Λ hlat hprim ψ'`. Use `⟨w, ?_, fun j => ?_⟩` and prove the remaining obligations. Use `w.2.1` as an intermediate fact.

Rewrite `this` using `[hΛ]`. Then use the resulting hypothesis. Choose the witnesses or unpack the hypotheses as in `⟨c, hcm, hc0⟩ : ∃ c ∈ aa j, c ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Conclude with `h0 j (FractionalIdeal.eq_zero_iff.2 hne)`.

Establish `hm : c • frame F j ∈ M0`. Use `⟨?_, U.smul_mem c (Submodule.subset_span ⟨j, rfl⟩)⟩` and prove the remaining obligations. Use `(hc (Pi.single j c)).2 fun i => by` as an intermediate fact. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `using hcm`. Simplify using `[h, FractionalIdeal.zero_mem]`. Simplify `this` using `[Pi.single_apply]`. Establish `h1` using `hw ⟨_, hm⟩`. Establish `h2 : (ψ' ⟨_, hm⟩ : E) = φ (c • frame F j)` using `hψ ⟨_, hm⟩`.

Rewrite `h1` using `[h2, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`. Rewrite using `[← hφ']`. Conclude with `(mul_left_cancel₀ hc0 h1).symm`.
-/
theorem exists_partner (hlat : Submodule.IsLattice E Λ) (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hT : T ≠ 0)
    (aa : Fin (r + 1) → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (h0 : ∀ j, aa j ≠ 0)
    (hc : ∀ c : Fin (r + 1) → E, ∑ j, c j • frame F j ∈ Λ ↔ ∀ j, c j ∈ aa j)
    (b : Fin (r + 1)) (s : E) (hs : s ∈ (aa b)⁻¹) :
    ∃ σ ∈ Λ, ∀ j, S.hT σ (frame F j) = if j = b then s else 0 := by
  have hli : LinearIndependent E (frame F) := frame_indep hT
  set U := Submodule.span E (Set.range (frame F))
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (p := U) ((Basis.span hli).constr E fun j => if j = b then s else 0)
  have hφ' : ∀ j, φ (frame F j) = if j = b then s else 0 := by
    intro j
    have := LinearMap.congr_fun hφ (Basis.span hli j)
    rw [Basis.constr_basis] at this
    rw [← this]
    simp [Basis.span_apply]
  set M0 : Submodule (𝓞 E) S.V := Λ ⊓ toO S U
  have hprim : IsPrimitiveSub M0 Λ := by
    refine ⟨inf_le_left, le_antisymm (le_inf inf_le_left fun x hx => Submodule.subset_span hx) ?_⟩
    refine inf_le_inf_left _ ?_
    intro x hx
    exact (Submodule.span_le (p := U)).2 (fun y hy => hy.2) hx
  have hint : ∀ x : M0, ∃ o : 𝓞 E, (o : E) = φ x := by
    rintro ⟨x, hx, hxU⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxU
    have h1 := FractionalIdeal.mul_mem_mul ((hc c).1 hx b) hs
    rw [mul_inv_cancel₀ (h0 b), FractionalIdeal.mem_one_iff] at h1
    obtain ⟨o, ho⟩ := h1
    refine ⟨o, ?_⟩
    simp [map_sum, hφ', ← ho]
  choose ψ hψ using hint
  let ψ' : M0 →ₗ[𝓞 E] 𝓞 E :=
    { toFun := ψ
      map_add' := fun x y => by
        apply RingOfIntegers.ext
        simp [hψ]
      map_smul' := fun c x => by
        apply RingOfIntegers.ext
        simp only [hψ, RingHom.id_apply, smul_eq_mul, map_mul, Submodule.coe_smul]
        rw [← algebraMap_smul E c (x : S.V), map_smul]
        simp [hψ] }
  obtain ⟨w, hw⟩ := FunIdx.exists_dual_vec S M0 Λ hlat hprim ψ'
  refine ⟨w, ?_, fun j => ?_⟩
  · have := w.2.1
    rwa [hΛ] at this
  · obtain ⟨c, hcm, hc0⟩ : ∃ c ∈ aa j, c ≠ 0 := by
      by_contra hne
      push Not at hne
      exact h0 j (FractionalIdeal.eq_zero_iff.2 hne)
    have hm : c • frame F j ∈ M0 := by
      refine ⟨?_, U.smul_mem c (Submodule.subset_span ⟨j, rfl⟩)⟩
      have := (hc (Pi.single j c)).2 fun i => by
        by_cases h : i = j
        · subst h; simpa using hcm
        · simp [h, FractionalIdeal.zero_mem]
      simpa [Pi.single_apply] using this
    have h1 := hw ⟨_, hm⟩
    have h2 : (ψ' ⟨_, hm⟩ : E) = φ (c • frame F j) := hψ ⟨_, hm⟩
    rw [h2, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    rw [← hφ']
    exact (mul_left_cancel₀ hc0 h1).symm

/- English proof (translation)
Establish `hwX : w ∈ Xsp F` using `Xflag_le_X _ hw`. Establish `hσb : ∀ x ∈ Xflag F b, S.hT σ x = 0`. Use `ext_Xflag (S.hT σ) 0 b fun a ha => ?_` and prove the remaining obligations. Rewrite using `[hσ, if_neg (fun h => by rw [h] at ha; exact lt_irrefl _ ha)]`. Both sides reduce to the same expression.

Establish `hww : S.hT w w = 0` using `iso_X S F hwX hwX`. Establish `hwσ : S.hT w σ = 0` using `by rw [herm S, hσb w hw, star_zero]`. Establish `ht : (θ : E) * S.hT σ σ + star ((θ : E) * S.hT σ σ) = S.hT σ σ`. Rewrite using `[star_mul', ← herm S σ σ, ← add_mul, hθ, one_mul]`. Establish `htO : ∃ o : 𝓞 E, (o : E) = (θ : E) * S.hT σ σ`.

Take `⟨p, hp⟩` from `integral_of_unimodular S hΛ hσΛ hσΛ`. Conclude with `⟨θ * p, by rw [← hp]; simp⟩`. Use `set t := (θ : E) * S.hT σ σ`. Establish `hap : ∀ x, S.hT w x = 0 → eichE S σ w t hww hwσ ht x = x - S.hT σ x • w`. Introduce `x hx`.

Express the relevant statement in the definitionally equal form `eich S σ w t x = _`. Rewrite using `[eich_apply, hx]`. Simplify using the standard rewrite rules. Use `⟨eichE S σ w t hww hwσ ht, ⟨⟨fun x y => eich_isom S σ w t hww hwσ ht x y, ?_⟩, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `eich_mem S hΛ hσΛ hwΛ htO hx`. Introduce `x hx`. Conclude with `⟨eich S (-σ) w (star t) x, eich_mem S hΛ (Λ.neg_mem hσΛ) hwΛ (star_int htO) hx, (eichE S σ w t hww hwσ ht).apply_symm_apply x⟩`. Introduce `j x hx`.

Rewrite using `[hap x (iso_X S F hwX (Xflag_le_X _ hx)), sub_sub_cancel_left]`. Distinguish the cases in `hj : j + 1 ≤ b.val`. Rewrite using `[hσb x (Xflag_mono' hj hx)]`. Simplify using the standard rewrite rules. Conclude with `Submodule.neg_mem _ (Submodule.smul_mem _ _ (Xflag_mono' (by omega) hw))`.

Introduce `x hx`. Rewrite using `[hap x ((mem_orth S).1 hx w hwX), sub_sub_cancel_left]`. Conclude with `Submodule.neg_mem _ (Submodule.smul_mem _ _ hwX)`. Rewrite using `[hap _ (X_orth_frame hwX b), hσ, if_pos rfl]`. Introduce `j hj`.

Rewrite using `[hap _ (X_orth_frame hwX j), hσ, if_neg hj]`. Simplify using the standard rewrite rules.
-/
theorem exists_elem (θ : 𝓞 E) (hθ : (θ : E) + star (θ : E) = 1) (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (b : Fin (r + 1)) (s : E) (σ : S.V) (hσΛ : σ ∈ Λ)
    (hσ : ∀ j, S.hT σ (frame F j) = if j = b then s else 0) (w : S.V) (hwΛ : w ∈ Λ) (hw : w ∈ Xflag F b) :
    ∃ n ∈ NLam Λ F, n (frame F b) = frame F b - s • w ∧ ∀ j, j ≠ b → n (frame F j) = frame F j := by
  have hwX : w ∈ Xsp F := Xflag_le_X _ hw
  have hσb : ∀ x ∈ Xflag F b, S.hT σ x = 0 := by
    refine ext_Xflag (S.hT σ) 0 b fun a ha => ?_
    rw [hσ, if_neg (fun h => by rw [h] at ha; exact lt_irrefl _ ha)]
    rfl
  have hww : S.hT w w = 0 := iso_X S F hwX hwX
  have hwσ : S.hT w σ = 0 := by rw [herm S, hσb w hw, star_zero]
  have ht : (θ : E) * S.hT σ σ + star ((θ : E) * S.hT σ σ) = S.hT σ σ := by
    rw [star_mul', ← herm S σ σ, ← add_mul, hθ, one_mul]
  have htO : ∃ o : 𝓞 E, (o : E) = (θ : E) * S.hT σ σ := by
    obtain ⟨p, hp⟩ := integral_of_unimodular S hΛ hσΛ hσΛ
    exact ⟨θ * p, by rw [← hp]; simp⟩
  set t := (θ : E) * S.hT σ σ
  have hap : ∀ x, S.hT w x = 0 → eichE S σ w t hww hwσ ht x = x - S.hT σ x • w := by
    intro x hx
    change eich S σ w t x = _
    rw [eich_apply, hx]; simp
  refine ⟨eichE S σ w t hww hwσ ht, ⟨⟨fun x y => eich_isom S σ w t hww hwσ ht x y, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact eich_mem S hΛ hσΛ hwΛ htO hx
    · intro x hx
      exact ⟨eich S (-σ) w (star t) x, eich_mem S hΛ (Λ.neg_mem hσΛ) hwΛ (star_int htO) hx,
        (eichE S σ w t hww hwσ ht).apply_symm_apply x⟩
  · intro j x hx
    rw [hap x (iso_X S F hwX (Xflag_le_X _ hx)), sub_sub_cancel_left]
    by_cases hj : j + 1 ≤ b.val
    · rw [hσb x (Xflag_mono' hj hx)]; simp
    · exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Xflag_mono' (by omega) hw))
  · intro x hx
    rw [hap x ((mem_orth S).1 hx w hwX), sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hwX)
  · rw [hap _ (X_orth_frame hwX b), hσ, if_pos rfl]
  · intro j hj
    rw [hap _ (X_orth_frame hwX j), hσ, if_neg hj]; simp

/- English proof (translation)
Establish `key : ∀ x ∈ aa b * (aa b)⁻¹, ∃ n ∈ NLam Λ F, n (frame F b) = frame F b + x • w ∧ ∀ j, j ≠ b → n (frame F j) = frame F j`. Introduce `x hx`. Use `FractionalIdeal.mul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `c hcm s hs`. Take `⟨σ, hσΛ, hσ⟩` from `exists_partner hlat hΛ hT aa h0 hc b s hs`.

Take `⟨n, hn, h1, h2⟩` from `exists_elem θ hθ hΛ b s σ hσΛ hσ (-(c • w)) (Λ.neg_mem (hwΛ c hcm)) (Submodule.neg_mem _ (Submodule.smul_mem _ _ hw))`. Use `⟨n, hn, ?_, h2⟩` and prove the remaining obligations. Rewrite using `[h1]`. Use `module`. Introduce and unpack `x y ⟨n, hn, h1, h2⟩ ⟨m, hm, e1, e2⟩`.

Use `⟨m * n, mul_mem_NLam hn hm, ?_, fun j hj => ?_⟩` and prove the remaining obligations. Establish `: m w = w` using `ext_Xflag (m : S.V →ₗ[E] S.V) LinearMap.id b (fun a ha => e2 a fun h => by rw [h] at ha; exact lt_irrefl _ ha) w hw`. Express the relevant statement in the definitionally equal form `m (n _) = _`. Rewrite using `[h1, map_add, map_smul, e1, this]`. Use `module`.

Express the relevant statement in the definitionally equal form `m (n _) = _`. Rewrite using `[h2 j hj, e2 j hj]`. Use `key 1 (by rw [mul_inv_cancel₀ (h0 b)]; exact FractionalIdeal.one_mem_one _)` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_col (θ : 𝓞 E) (hθ : (θ : E) + star (θ : E) = 1) (hlat : Submodule.IsLattice E Λ)
    (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hT : T ≠ 0)
    (aa : Fin (r + 1) → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (h0 : ∀ j, aa j ≠ 0)
    (hc : ∀ c : Fin (r + 1) → E, ∑ j, c j • frame F j ∈ Λ ↔ ∀ j, c j ∈ aa j)
    (b : Fin (r + 1)) (w : S.V) (hw : w ∈ Xflag F b) (hwΛ : ∀ c ∈ aa b, c • w ∈ Λ) :
    ∃ n ∈ NLam Λ F, n (frame F b) = frame F b + w ∧ ∀ j, j ≠ b → n (frame F j) = frame F j := by
  have key : ∀ x ∈ aa b * (aa b)⁻¹, ∃ n ∈ NLam Λ F, n (frame F b) = frame F b + x • w ∧
      ∀ j, j ≠ b → n (frame F j) = frame F j := by
    intro x hx
    refine FractionalIdeal.mul_induction_on hx ?_ ?_
    · intro c hcm s hs
      obtain ⟨σ, hσΛ, hσ⟩ := exists_partner hlat hΛ hT aa h0 hc b s hs
      obtain ⟨n, hn, h1, h2⟩ := exists_elem θ hθ hΛ b s σ hσΛ hσ (-(c • w)) (Λ.neg_mem (hwΛ c hcm))
        (Submodule.neg_mem _ (Submodule.smul_mem _ _ hw))
      refine ⟨n, hn, ?_, h2⟩
      rw [h1]; module
    · rintro x y ⟨n, hn, h1, h2⟩ ⟨m, hm, e1, e2⟩
      refine ⟨m * n, mul_mem_NLam hn hm, ?_, fun j hj => ?_⟩
      · have : m w = w := ext_Xflag (m : S.V →ₗ[E] S.V) LinearMap.id b
          (fun a ha => e2 a fun h => by rw [h] at ha; exact lt_irrefl _ ha) w hw
        change m (n _) = _
        rw [h1, map_add, map_smul, e1, this]; module
      · change m (n _) = _
        rw [h2 j hj, e2 j hj]
  have := key 1 (by rw [mul_inv_cancel₀ (h0 b)]; exact FractionalIdeal.one_mem_one _)
  simpa using this

/- English proof (translation)
Establish `key : ∀ k : ℕ, ∃ n ∈ NLam Λ F, ∀ b : Fin (r + 1), n (frame F b) = frame F b + if b.val < k then w b else 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨1, one_mem_NLam, fun b => by simp⟩`. Consider the case `succ k ih`.

Take `⟨n, hn, h1⟩` from `ih`. Distinguish the cases in `hk : k < r + 1`. Take `⟨m, hm, e1, e2⟩` from `h ⟨k, hk⟩`. Use `⟨m * n, mul_mem_NLam hn hm, fun b => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `m (n _) = _`.

Rewrite using `[h1]`. Break down `lt_trichotomy b.val k with hb | hb | hb` into its components or cases. Establish `: m (w b) = w b` using `ext_Xflag (m : S.V →ₗ[E] S.V) LinearMap.id b (fun a ha => e2 a fun h => by rw [h] at ha; exact lt_asymm ha hb) _ (hw b)`. Rewrite using `[if_pos hb, if_pos (by omega), map_add, this, e2 b fun h => by rw [h] at hb; exact lt_irrefl _ hb]`. Establish `: b = ⟨k, hk⟩` using `Fin.ext hb`.

Rewrite using `[if_neg (by omega), if_pos (by omega), add_zero, this, e1]`. Rewrite using `[if_neg (by omega), if_neg (by omega), add_zero, e2 b fun h => by rw [h] at hb; exact lt_irrefl _ hb]`. Use `⟨n, hn, fun b => ?_⟩` and prove the remaining obligations. Use `b.2` as an intermediate fact. Rewrite using `[h1, if_pos (by omega), if_pos (by omega)]`.

Take `⟨n, hn, h1⟩` from `key (r + 1)`. Conclude with `⟨n, hn, fun b => by rw [h1, if_pos b.2]⟩`.
-/
theorem exists_cols (w : Fin (r + 1) → S.V) (hw : ∀ b : Fin (r + 1), w b ∈ Xflag F b)
    (h : ∀ b, ∃ n ∈ NLam Λ F, n (frame F b) = frame F b + w b ∧ ∀ j, j ≠ b → n (frame F j) = frame F j) :
    ∃ n ∈ NLam Λ F, ∀ b, n (frame F b) = frame F b + w b := by
  have key : ∀ k : ℕ, ∃ n ∈ NLam Λ F, ∀ b : Fin (r + 1),
      n (frame F b) = frame F b + if b.val < k then w b else 0 := by
    intro k
    induction k with
    | zero => exact ⟨1, one_mem_NLam, fun b => by simp⟩
    | succ k ih =>
      obtain ⟨n, hn, h1⟩ := ih
      by_cases hk : k < r + 1
      · obtain ⟨m, hm, e1, e2⟩ := h ⟨k, hk⟩
        refine ⟨m * n, mul_mem_NLam hn hm, fun b => ?_⟩
        change m (n _) = _
        rw [h1]
        rcases lt_trichotomy b.val k with hb | hb | hb
        · have : m (w b) = w b := ext_Xflag (m : S.V →ₗ[E] S.V) LinearMap.id b
            (fun a ha => e2 a fun h => by rw [h] at ha; exact lt_asymm ha hb) _ (hw b)
          rw [if_pos hb, if_pos (by omega), map_add, this, e2 b fun h => by rw [h] at hb; exact lt_irrefl _ hb]
        · have : b = ⟨k, hk⟩ := Fin.ext hb
          rw [if_neg (by omega), if_pos (by omega), add_zero, this, e1]
        · rw [if_neg (by omega), if_neg (by omega), add_zero,
            e2 b fun h => by rw [h] at hb; exact lt_irrefl _ hb]
      · refine ⟨n, hn, fun b => ?_⟩
        have := b.2
        rw [h1, if_pos (by omega), if_pos (by omega)]
  obtain ⟨n, hn, h1⟩ := key (r + 1)
  exact ⟨n, hn, fun b => by rw [h1, if_pos b.2]⟩

/- English proof (translation)
Set `w : Fin (r + 1) → S.V` to `fun b => ∑ a, (if a < b then (ξ a b : E) else 0) • frame F a`. Establish `hw : ∀ b : Fin (r + 1), w b ∈ Xflag F b`. Introduce `b`. Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Use `split_ifs with hab`.

Establish `ha : a.val < r` using `by have := b.2; have : a.val < b.val := hab; omega`. Establish `: a = Fin.castSucc ⟨a.val, ha⟩` using `rfl`. Rewrite using `[this, frame_cast]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hab, rfl⟩)`. Simplify using the standard rewrite rules.

Take `⟨n, hn, h⟩` from `exists_cols w hw fun b => exists_col θ hθ hlat hΛ hT aa h0 hc b (w b) (hw b) (by`. Introduce `c hcm`. Simplify using `only [w, Finset.smul_sum, smul_smul]`. Use `(hc _).2 fun a => ?_` and prove the remaining obligations. Use `split_ifs with hab`.

Use `(aa a : Submodule (𝓞 E) E).smul_mem (ξ a b) (hanti a b hab.le hcm)` as an intermediate fact. Rewrite using `[mul_comm]`. Conclude with `this`. Simplify using `[FractionalIdeal.zero_mem])`. Use `⟨n, hn, fun b => ?_⟩` and prove the remaining obligations.

Rewrite using `[h]`. Establish `: frame F b = ∑ a, (if a = b then (1 : E) else 0) • frame F a` using `by simp`. Rewrite using `[this]`. Simplify using `only [w, frameAct, ← Finset.sum_add_distrib, ← add_smul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Use `congr 1`. Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases. Simplify using `[hab, hab.ne]`. Simplify using `[h2]`. Simplify using `[hab.ne', hab.not_gt, h1 a b hab]`.
-/
theorem exists_frame_op (θ : 𝓞 E) (hθ : (θ : E) + star (θ : E) = 1) (hlat : Submodule.IsLattice E Λ)
    (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hT : T ≠ 0)
    (aa : Fin (r + 1) → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (h0 : ∀ j, aa j ≠ 0)
    (hanti : ∀ a b, a ≤ b → aa b ≤ aa a)
    (hc : ∀ c : Fin (r + 1) → E, ∑ j, c j • frame F j ∈ Λ ↔ ∀ j, c j ∈ aa j)
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) :
    ∃ n ∈ NLam Λ F, ∀ b, n (frame F b) = frameAct (frame F) ξ b := by
  let w : Fin (r + 1) → S.V := fun b => ∑ a, (if a < b then (ξ a b : E) else 0) • frame F a
  have hw : ∀ b : Fin (r + 1), w b ∈ Xflag F b := by
    intro b
    refine Submodule.sum_mem _ fun a _ => ?_
    split_ifs with hab
    · have ha : a.val < r := by have := b.2; have : a.val < b.val := hab; omega
      have : a = Fin.castSucc ⟨a.val, ha⟩ := rfl
      rw [this, frame_cast]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hab, rfl⟩)
    · simp
  obtain ⟨n, hn, h⟩ := exists_cols w hw fun b => exists_col θ hθ hlat hΛ hT aa h0 hc b (w b) (hw b) (by
    intro c hcm
    simp only [w, Finset.smul_sum, smul_smul]
    refine (hc _).2 fun a => ?_
    split_ifs with hab
    · have := (aa a : Submodule (𝓞 E) E).smul_mem (ξ a b) (hanti a b hab.le hcm)
      rw [mul_comm]
      exact this
    · simp [FractionalIdeal.zero_mem])
  refine ⟨n, hn, fun b => ?_⟩
  rw [h]
  have : frame F b = ∑ a, (if a = b then (1 : E) else 0) • frame F a := by simp
  rw [this]
  simp only [w, frameAct, ← Finset.sum_add_distrib, ← add_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rcases lt_trichotomy a b with hab | rfl | hab
  · simp [hab, hab.ne]
  · simp [h2]
  · simp [hab.ne', hab.not_gt, h1 a b hab]

/- English proof (translation)
Establish `hsum : ∑ j, c j • frame F j = ∑ a : Fin r, c a.castSucc • F.fl.e a + c (Fin.last r) • F.fl.z`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [frame_cast, frame_last]`. Establish `hx : ∑ a : Fin r, c a.castSucc • F.fl.e a ∈ Xsp F` using `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Establish `hzo : ∀ t : E, t • F.fl.z ∈ orth S (Xsp F)` using `fun t => Submodule.smul_mem _ _ ((mem_orth S).2 fun x hx => by rw [← frame_last]; exact X_orth_frame hx _)`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `h` using `[hsum]`. Take `⟨o, ho⟩` from `hp (c (Fin.last r)) ⟨by`. Establish `e : c (Fin.last r) • F.fl.z = (∑ a : Fin r, c a.castSucc • F.fl.e a + c (Fin.last r) • F.fl.z) + -(∑ a : Fin r, c a.castSucc • F.fl.e a)` using `by abel`.

Rewrite using `[e]`. Conclude with `Submodule.add_mem_sup ⟨h, (orth S (Xsp F)).add_mem (X_le_orth hx) (hzo _)⟩ ((Xsp F).neg_mem hx), hzo _⟩`. Establish `h3 : ∑ a : Fin r, c a.castSucc • F.fl.e a ∈ XLam Λ F`. Use `⟨?_, hx⟩` and prove the remaining obligations. Use `Λ.sub_mem h (smul_mem_of S ⟨o, ho⟩ hz)` as an intermediate fact.

Simplify using `using this`. Establish `h4 : ∀ y ∈ XLam Λ F, ∃ d : Fin r → E, (∀ a, d a ∈ aa a.castSucc) ∧ y = ∑ a, d a • F.fl.e a`. Introduce `y hy`. Rewrite `hy` using `[hX]`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨a, x, hx, rfl⟩` from `hy`. Use `⟨Pi.single a x, fun i => ?_, by simp [Pi.single_apply]⟩` and prove the remaining obligations. Distinguish the cases in `h : i = a`. Substitute `h` using the available equality.

Simplify using `using hx`. Simplify using `[h, FractionalIdeal.zero_mem]`. Consider the case `zero => exact ⟨0, fun a => FractionalIdeal.zero_mem _, by simp⟩`. Consider the case `add x y _ _ h1 h2`. Take `⟨d, hd, rfl⟩` from `h1`.

Take `⟨d', hd', rfl⟩` from `h2`. Conclude with `⟨d + d', fun a => (aa a.castSucc : Submodule (𝓞 E) E).add_mem (hd a) (hd' a), by simp [add_smul, Finset.sum_add_distrib]⟩`. Consider the case `smul t x _ h1`. Take `⟨d, hd, rfl⟩` from `h1`. Use `⟨t • d, fun a => (aa a.castSucc : Submodule (𝓞 E) E).smul_mem t (hd a), ?_⟩` and prove the remaining obligations.

Simplify using `[Finset.smul_sum]`. Take `⟨d, hd, e⟩` from `h4 _ h3`. Establish `h5` using `Fintype.linearIndependent_iff.1 F.fl.e_indep (fun a => c a.castSucc - d a) (by simp [sub_smul, Finset.sum_sub_distrib, e])`. Introduce `j`. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last => rw [hl, FractionalIdeal.mem_one_iff]`. Conclude with `⟨o, ho⟩`. Consider the case `cast a => rw [sub_eq_zero.1 (h5 a)]`. Conclude with `hd a`. Introduce `h`.

Rewrite using `[hsum]`. Use `Λ.add_mem (Submodule.sum_mem _ fun a _ => ?_) (smul_mem_of S ?_ hz)` and prove the remaining obligations. Establish `: c a.castSucc • F.fl.e a ∈ XLam Λ F`. Rewrite using `[hX]`. Conclude with `Submodule.subset_span ⟨a, _, h _, rfl⟩`.

Conclude with `this.1`. Use `h (Fin.last r)` as an intermediate fact. Rewrite `this` using `[hl, FractionalIdeal.mem_one_iff]`. Then use the resulting hypothesis.
-/
theorem coord_iff (aa : Fin (r + 1) → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hl : aa (Fin.last r) = 1)
    (hz : F.fl.z ∈ Λ) (hp : ∀ c : E, c • F.fl.z ∈ Lsub Λ F → ∃ o : 𝓞 E, (o : E) = c)
    (hX : XLam Λ F = Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ aa a.castSucc ∧ y = x • F.fl.e a})
    (c : Fin (r + 1) → E) : ∑ j, c j • frame F j ∈ Λ ↔ ∀ j, c j ∈ aa j := by
  have hsum : ∑ j, c j • frame F j = ∑ a : Fin r, c a.castSucc • F.fl.e a + c (Fin.last r) • F.fl.z := by
    rw [Fin.sum_univ_castSucc]; simp only [frame_cast, frame_last]
  have hx : ∑ a : Fin r, c a.castSucc • F.fl.e a ∈ Xsp F :=
    Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hzo : ∀ t : E, t • F.fl.z ∈ orth S (Xsp F) := fun t => Submodule.smul_mem _ _
    ((mem_orth S).2 fun x hx => by rw [← frame_last]; exact X_orth_frame hx _)
  constructor
  · intro h
    rw [hsum] at h
    obtain ⟨o, ho⟩ := hp (c (Fin.last r)) ⟨by
      have e : c (Fin.last r) • F.fl.z = (∑ a : Fin r, c a.castSucc • F.fl.e a + c (Fin.last r) • F.fl.z) +
        -(∑ a : Fin r, c a.castSucc • F.fl.e a) := by abel
      rw [e]
      exact Submodule.add_mem_sup ⟨h, (orth S (Xsp F)).add_mem (X_le_orth hx) (hzo _)⟩
        ((Xsp F).neg_mem hx), hzo _⟩
    have h3 : ∑ a : Fin r, c a.castSucc • F.fl.e a ∈ XLam Λ F := by
      refine ⟨?_, hx⟩
      have := Λ.sub_mem h (smul_mem_of S ⟨o, ho⟩ hz)
      simpa using this
    have h4 : ∀ y ∈ XLam Λ F, ∃ d : Fin r → E, (∀ a, d a ∈ aa a.castSucc) ∧ y = ∑ a, d a • F.fl.e a := by
      intro y hy
      rw [hX] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, x, hx, rfl⟩ := hy
        refine ⟨Pi.single a x, fun i => ?_, by simp [Pi.single_apply]⟩
        by_cases h : i = a
        · subst h; simpa using hx
        · simp [h, FractionalIdeal.zero_mem]
      | zero => exact ⟨0, fun a => FractionalIdeal.zero_mem _, by simp⟩
      | add x y _ _ h1 h2 =>
        obtain ⟨d, hd, rfl⟩ := h1
        obtain ⟨d', hd', rfl⟩ := h2
        exact ⟨d + d', fun a => (aa a.castSucc : Submodule (𝓞 E) E).add_mem (hd a) (hd' a),
          by simp [add_smul, Finset.sum_add_distrib]⟩
      | smul t x _ h1 =>
        obtain ⟨d, hd, rfl⟩ := h1
        refine ⟨t • d, fun a => (aa a.castSucc : Submodule (𝓞 E) E).smul_mem t (hd a), ?_⟩
        simp [Finset.smul_sum]
    obtain ⟨d, hd, e⟩ := h4 _ h3
    have h5 := Fintype.linearIndependent_iff.1 F.fl.e_indep (fun a => c a.castSucc - d a)
      (by simp [sub_smul, Finset.sum_sub_distrib, e])
    intro j
    induction j using Fin.lastCases with
    | last => rw [hl, FractionalIdeal.mem_one_iff]; exact ⟨o, ho⟩
    | cast a => rw [sub_eq_zero.1 (h5 a)]; exact hd a
  · intro h
    rw [hsum]
    refine Λ.add_mem (Submodule.sum_mem _ fun a _ => ?_) (smul_mem_of S ?_ hz)
    · have : c a.castSucc • F.fl.e a ∈ XLam Λ F := by
        rw [hX]; exact Submodule.subset_span ⟨a, _, h _, rfl⟩
      exact this.1
    · have := h (Fin.last r)
      rwa [hl, FractionalIdeal.mem_one_iff] at this

/- English proof (translation)
Use `set g := frameAct (frame F) B with hg`. Establish `hX : ∀ b, ∃ x ∈ Xsp F, g b = x + (B (Fin.last r) b : E) • F.fl.z`. Introduce `b`. Use `⟨∑ a : Fin r, (B a.castSucc b : E) • F.fl.e a, Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩), ?_⟩` and prove the remaining obligations. Simplify using `only [hg, frameAct]`.

Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [frame_cast, frame_last]`. Establish `he : ∀ a : Fin r, g a.castSucc ∈ Xsp F`. Introduce `a`. Take `⟨x, hx, e⟩` from `hX a.castSucc`.

Rewrite using `[e, h1 _ _ (Fin.castSucc_lt_last a)]`. Simplify using `using hx`. Establish `ho : ∀ x ∈ Xsp F, ∀ b, S.hT x (g b) = 0`. Introduce `x hx b`. Simplify using `[hg, frameAct, map_sum, X_orth_frame hx]`.

Establish `hli : LinearIndependent E g`. Take `⟨η, -, -, e⟩` from `uni_inv h1 h2`. Establish `e' : η * B = 1` using `mul_eq_one_comm.1 e`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`.

Establish `h3` using `Fintype.linearIndependent_iff.1 (frame_indep (F := F) hT) ((B.map (algebraMap (𝓞 E) E)).mulVec c) (by`. Rewrite using `[← hc]`. Simplify using `only [hg, frameAct, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul, Matrix.map_apply]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm])`.

Establish `h4 : (B.map (algebraMap (𝓞 E) E)).mulVec c = 0` using `funext h3`. Establish `h5` using `congrArg ((η.map (algebraMap (𝓞 E) E)).mulVec) h4`. Rewrite `h5` using `[Matrix.mulVec_mulVec, ← Matrix.map_mul, e', Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec, Matrix.mulVec_zero]`. Conclude with `fun i => congrFun h5 i`. Use `⟨⟨⟨fun a => n (g a.castSucc), n (g (Fin.last r)), ?_, fun a b => ?_, fun a => ?_, ?_⟩, n (g (Fin.last r))⟩, rfl, ?_⟩` and prove the remaining obligations.

Conclude with `(hli.comp _ (Fin.castSucc_injective r)).map' (n : S.V →ₗ[E] S.V) n.ker`. Rewrite using `[hn]`. Conclude with `ho _ (he a) _`. Rewrite using `[hn]`. Conclude with `ho _ (he a) _`.

Rewrite using `[hn]`. Take `⟨x, hx, e⟩` from `hX (Fin.last r)`. Establish `e1` using `ho x hx (Fin.last r)`. Establish `e2 : S.hT x F.fl.z = 0` using `by rw [← frame_last]; exact X_orth_frame hx _`. Establish `e3 : S.hT F.fl.z x = 0` using `by rw [herm S, e2, star_zero]`.

Rewrite `e` using `[h2]`. Establish `e' : g (Fin.last r) = x + F.fl.z` using `by simpa using e`. Rewrite using `[e']`. Simplify using `[iso_X S F hx hx, e2, e3, F.fl.z_norm]`. Rewrite using `[← map_frameAct]`.

Use function extensionality and compare the values at `b`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => rw [frame_last]`. Consider the case `cast a => rw [frame_cast]`.
-/
theorem exists_moved (hT : T ≠ 0) (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (B : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (h1 : ∀ a b, b < a → B a b = 0) (h2 : ∀ a, B a a = 1) :
    ∃ G : LFlag S r T, G.zt = G.fl.z ∧ frame G = frameAct (fun a => n (frame F a)) B := by
  set g := frameAct (frame F) B with hg
  have hX : ∀ b, ∃ x ∈ Xsp F, g b = x + (B (Fin.last r) b : E) • F.fl.z := by
    intro b
    refine ⟨∑ a : Fin r, (B a.castSucc b : E) • F.fl.e a,
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩), ?_⟩
    simp only [hg, frameAct]
    rw [Fin.sum_univ_castSucc]; simp only [frame_cast, frame_last]
  have he : ∀ a : Fin r, g a.castSucc ∈ Xsp F := by
    intro a
    obtain ⟨x, hx, e⟩ := hX a.castSucc
    rw [e, h1 _ _ (Fin.castSucc_lt_last a)]
    simpa using hx
  have ho : ∀ x ∈ Xsp F, ∀ b, S.hT x (g b) = 0 := by
    intro x hx b
    simp [hg, frameAct, map_sum, X_orth_frame hx]
  have hli : LinearIndependent E g := by
    obtain ⟨η, -, -, e⟩ := uni_inv h1 h2
    have e' : η * B = 1 := mul_eq_one_comm.1 e
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h3 := Fintype.linearIndependent_iff.1 (frame_indep (F := F) hT)
      ((B.map (algebraMap (𝓞 E) E)).mulVec c) (by
        rw [← hc]
        simp only [hg, frameAct, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul,
          Matrix.map_apply]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm])
    have h4 : (B.map (algebraMap (𝓞 E) E)).mulVec c = 0 := funext h3
    have h5 := congrArg ((η.map (algebraMap (𝓞 E) E)).mulVec) h4
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, e', Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec, Matrix.mulVec_zero] at h5
    exact fun i => congrFun h5 i
  refine ⟨⟨⟨fun a => n (g a.castSucc), n (g (Fin.last r)), ?_, fun a b => ?_, fun a => ?_, ?_⟩,
    n (g (Fin.last r))⟩, rfl, ?_⟩
  · exact (hli.comp _ (Fin.castSucc_injective r)).map' (n : S.V →ₗ[E] S.V) n.ker
  · rw [hn]; exact ho _ (he a) _
  · rw [hn]; exact ho _ (he a) _
  · rw [hn]
    obtain ⟨x, hx, e⟩ := hX (Fin.last r)
    have e1 := ho x hx (Fin.last r)
    have e2 : S.hT x F.fl.z = 0 := by rw [← frame_last]; exact X_orth_frame hx _
    have e3 : S.hT F.fl.z x = 0 := by rw [herm S, e2, star_zero]
    rw [h2] at e
    have e' : g (Fin.last r) = x + F.fl.z := by simpa using e
    rw [e']
    simp [iso_X S F hx hx, e2, e3, F.fl.z_norm]
  · rw [← map_frameAct]
    funext b
    induction b using Fin.lastCases with
    | last => rw [frame_last]
    | cast a => rw [frame_cast]

/- English proof (translation)
Use `(mem_orth S).2 fun y hy => ?_` and prove the remaining obligations. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨a, rfl⟩ := hy`. Rewrite using `[← frame_cast]`. Conclude with `h _`.

Consider the case `zero => simp`. Consider the case `add y z _ _ h1 h2 => simp [h1, h2]`. Consider the case `smul c y _ h => simp [h]`.
-/
theorem orth_X_of_frame {x : S.V} (h : ∀ b, S.hT (frame F b) x = 0) : x ∈ orth S (Xsp F) := by
  refine (mem_orth S).2 fun y hy => ?_
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; rw [← frame_cast]; exact h _
  | zero => simp
  | add y z _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

/- English proof (translation)
Unfold `Hp UUE spanE`. Rewrite using `[mem_orth]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : ∀ y ∈ UU Λ F G, S.hT y x = 0` using `fun y hy => h y (Submodule.subset_span hy)`.

Unfold `UU at h'`. Prove the components needed by the constructor for the conclusion. Introduce `b`. Apply `h'` to reduce the goal to its premises. Use `Submodule.mem_sup_left (Submodule.mem_sup_left ?_)` and prove the remaining obligations.

Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => rw [frame_last, hF]`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span rfl)`. Consider the case `cast a`. Rewrite using `[frame_cast]`.

Conclude with `Submodule.mem_sup_left ⟨hFe a, Submodule.subset_span ⟨a, rfl⟩⟩`. Introduce `b`. Apply `h'` to reduce the goal to its premises. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => rw [frame_last, hG]`.

Conclude with `Submodule.mem_sup_right (Submodule.subset_span rfl)`. Consider the case `cast a`. Rewrite using `[frame_cast]`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right ⟨hGe a, Submodule.subset_span ⟨a, rfl⟩⟩)`. Introduce and unpack `⟨h1, h2⟩`.

Set `K : Submodule E S.V` to `{ carrier := {y | S.hT y x = 0} add_mem' := fun {a b} ha hb => by simp_all zero_mem' := by simp smul_mem' := fun c a ha => by simp_all }`. Establish `: UU Λ F G ≤ toO S K`. Use `sup_le (sup_le (sup_le ?_ ?_) ?_) ?_` and prove the remaining obligations. Conclude with `fun y hy => (mem_orth S).1 (orth_X_of_frame h1) y hy.2`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff, hF, ← frame_last]`.

Conclude with `h1 _`. Conclude with `fun y hy => (mem_orth S).1 (orth_X_of_frame h2) y hy.2`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff, hG, ← frame_last]`. Conclude with `h2 _`. Conclude with `fun y hy => (Submodule.span_le (p := K)).2 this hy`.
-/
theorem mem_Hp_iff {T' : E} {G : LFlag S r T'} (hF : F.zt = F.fl.z) (hG : G.zt = G.fl.z)
    (hFe : ∀ a, F.fl.e a ∈ Λ) (hGe : ∀ a, G.fl.e a ∈ Λ) (x : S.V) :
    x ∈ Hp Λ F G ↔ (∀ b, S.hT (frame F b) x = 0) ∧ ∀ b, S.hT (frame G b) x = 0 := by
  unfold Hp UUE spanE
  rw [mem_orth]
  constructor
  · intro h
    have h' : ∀ y ∈ UU Λ F G, S.hT y x = 0 := fun y hy => h y (Submodule.subset_span hy)
    unfold UU at h'
    constructor
    · intro b
      apply h'
      refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
      induction b using Fin.lastCases with
      | last => rw [frame_last, hF]; exact Submodule.mem_sup_right (Submodule.subset_span rfl)
      | cast a =>
        rw [frame_cast]; exact Submodule.mem_sup_left ⟨hFe a, Submodule.subset_span ⟨a, rfl⟩⟩
    · intro b
      apply h'
      induction b using Fin.lastCases with
      | last => rw [frame_last, hG]; exact Submodule.mem_sup_right (Submodule.subset_span rfl)
      | cast a =>
        rw [frame_cast]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨hGe a, Submodule.subset_span ⟨a, rfl⟩⟩)
  · rintro ⟨h1, h2⟩
    let K : Submodule E S.V :=
      { carrier := {y | S.hT y x = 0}
        add_mem' := fun {a b} ha hb => by simp_all
        zero_mem' := by simp
        smul_mem' := fun c a ha => by simp_all }
    have : UU Λ F G ≤ toO S K := by
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · exact fun y hy => (mem_orth S).1 (orth_X_of_frame h1) y hy.2
      · rw [Submodule.span_le, Set.singleton_subset_iff, hF, ← frame_last]; exact h1 _
      · exact fun y hy => (mem_orth S).1 (orth_X_of_frame h2) y hy.2
      · rw [Submodule.span_le, Set.singleton_subset_iff, hG, ← frame_last]; exact h2 _
    exact fun y hy => (Submodule.span_le (p := K)).2 this hy

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Unfold `ddS`. Rewrite using `[FractionalIdeal.coeIdeal_ne_zero, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]`. Conclude with `differentIdeal_ne_bot`.
-/
theorem ddS_ne_zero (D : D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [FractionalIdeal.coeIdeal_ne_zero, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
  exact differentIdeal_ne_bot

/- English proof (translation)
Take `⟨k, rfl⟩` from `Int.le.dest h`. Rewrite using `[zpow_add₀ (ddS_ne_zero D), zpow_natCast]`. Establish `: ddS D ^ k ≤ 1`. Unfold `ddS`. Rewrite using `[← FractionalIdeal.coeIdeal_pow]`.

Conclude with `FractionalIdeal.coeIdeal_le_one`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ddS_anti (D : D7) {m n : ℤ} (h : m ≤ n) : ddS D ^ n ≤ ddS D ^ m := by
  obtain ⟨k, rfl⟩ := Int.le.dest h
  rw [zpow_add₀ (ddS_ne_zero D), zpow_natCast]
  have : ddS D ^ k ≤ 1 := by
    unfold ddS
    rw [← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one
  calc _ ≤ ddS D ^ m * 1 := by gcongr
    _ = _ := mul_one _

/- English proof (translation)
Use `Submodule.subset_span ⟨a, 1, ?_, (one_smul _ _).symm⟩` and prove the remaining obligations. Use `ddS_anti D (m := -((D.R.rS : ℤ) - (a : ℕ))) (n := 0) (by have := a.2; omega)` as an intermediate fact. Rewrite `this` using `[zpow_zero]`. Conclude with `this (FractionalIdeal.one_mem_one _)`.
-/
theorem e_mem_XS (D : D7) {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) : F.e a ∈ XS D F := by
  refine Submodule.subset_span ⟨a, 1, ?_, (one_smul _ _).symm⟩
  have := ddS_anti D (m := -((D.R.rS : ℤ) - (a : ℕ))) (n := 0) (by have := a.2; omega)
  rw [zpow_zero] at this
  exact this (FractionalIdeal.one_mem_one _)

/- English proof (translation)
Introduce `D u u' F0 Λ hSt _ hR P Z F' hF'`. Take `⟨⟨⟨hlift', -, -⟩, -, hX'⟩, ⟨A, B, hA1, hA2, hB1, hB2, hZ⟩, hP⟩` from `hF'`. Take `⟨-, ⟨hlat, hΛ, hlift, -, hprim⟩, hX⟩` from `hR`. Establish `hT : ((Tu D u : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hSt.2.1.ne_zero`. Establish `hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hSt.2.2.1.ne_zero`.

Take `⟨θ, hθ, -⟩` from `GlobalTheory.TraceOne.exists_trace_one D 2 Nat.prime_two`. Establish `hθ' : (θ : D.host.E) + star (θ : D.host.E) = 1`. Use `congrArg (algebraMap (𝓞 D.host.E) D.host.E) hθ` as an intermediate fact. Rewrite `this` using `[map_add, map_one]`. Rewrite using `[GlobalTheory.NormSum.AdLattice.star_eq_conj]`.

Conclude with `this`. Use `choose st hst using fun o : 𝓞 D.host.E => star_int (E := D.host.E) ⟨o, rfl⟩`. Establish `hst0 : st 0 = 0` using `RingOfIntegers.ext (by rw [hst]; simp)`. Establish `hst1 : st 1 = 1` using `RingOfIntegers.ext (by rw [hst]; simp)`. Take `⟨m, hm, hmf⟩` from `exists_frame_op (F := lf D F0) θ hθ' hlat hΛ hT (fun j => ddS D ^ (-((D.R.rS : ℤ) - (j : ℕ)))) (fun j => zpow_ne_zero _ (ddS_ne_zero D)) (fun a b hab => ddS_anti D (by have : a.val ≤ b.val := hab; omega)) (coord_iff _ (by simp) hlift.1 hprim hX) (fun a b => st (A b a)) (fun a b h …`.

Establish `hn` using `symm_mem_NLam hm`. Take `⟨G, hGz, hG⟩` from `exists_moved (F := F') hT' m.symm hn.1.1 B hB1 hB2`. Establish `he : ∀ a, F0.e a ∈ Λ` using `fun a => (hX.symm ▸ e_mem_XS D F0 a : F0.e a ∈ XLam Λ (lf D F0)).1`. Establish `he' : ∀ a, F'.fl.e a ∈ Λ` using `fun a => (hX'.symm ▸ e_mem_XS D F'.fl a : F'.fl.e a ∈ XLam Λ F').1`. Establish `hf' : ∀ b, frame F' b ∈ Λ` using `fun b => by`.

Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => rw [frame_last]`. Conclude with `hlift'.1`. Consider the case `cast a => rw [frame_cast]`. Conclude with `he' a`.

Establish `hGΛ : ∀ b, frame G b ∈ Λ` using `fun b => by`. Rewrite using `[hG]`. Conclude with `Submodule.sum_mem _ fun a _ => smul_mem_of _ ⟨_, rfl⟩ ((aut_mem_iff hn.1 _).2 (hf' a))`. Establish `hGe : ∀ a, G.fl.e a ∈ Λ` using `fun a => by rw [← frame_cast]; exact hGΛ _`. Establish `hadj : ∀ x y, (hS D).hT x (m.symm y) = (hS D).hT (m x) y` using `fun x y => by`.

Rewrite using `[← hm.1.1 x, LinearEquiv.apply_symm_apply]`. Use `⟨G, ⟨⟨by rw [← frame_last]; exact hGΛ _, hGz⟩, hGe, ?_, hP.trans ?_⟩, m.symm, hn, B, hB1, hB2, hG⟩` and prove the remaining obligations. Rewrite using `[hZ]`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(hS D).hT (frame (lf D F0) a) (frame G b) = _`.

Rewrite using `[hG]`. Simplify using `only [frameAct, map_sum, map_smul, hadj, hmf, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Use `congr 1`.

Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, hst, LinearMap.smul_apply, starRingEnd_apply, star_star]`. Both sides reduce to the same expression. Use `Submodule.comap_mono (sup_le ?_ le_sup_right)` and prove the remaining obligations.

Introduce and unpack `x ⟨hx, hxH⟩`. Take `⟨h1, h2⟩` from `(mem_Hp_iff rfl hlift'.2 he he' x).1 hxH`. Establish `e : x = m.symm x + -(m.symm x - x)` using `by abel`. Rewrite using `[e]`. Use `Submodule.add_mem_sup ⟨(aut_mem_iff hn.1 _).2 hx, (mem_Hp_iff rfl hGz he hGe _).2 ⟨fun b => ?_, fun b => ?_⟩⟩ (Submodule.neg_mem _ (hn.2.2 x (orth_X_of_frame h1)))` and prove the remaining obligations.

Rewrite using `[hadj, hmf]`. Simplify using `only [frameAct, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Rewrite using `[h1, smul_zero]`. Rewrite using `[hG]`.

Simplify using `only [frameAct, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hn.1.1, h2, smul_zero]`.
-/
theorem exists_exact_frame : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (Z : GramM D), ∀ F' ∈ FrSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P, ∃ F'' ∈ ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P, TEqv D Λ (lf D F0) F' F'' := by
  intro D u u' F0 Λ hSt _ hR P Z F' hF'
  obtain ⟨⟨⟨hlift', -, -⟩, -, hX'⟩, ⟨A, B, hA1, hA2, hB1, hB2, hZ⟩, hP⟩ := hF'
  obtain ⟨-, ⟨hlat, hΛ, hlift, -, hprim⟩, hX⟩ := hR
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hSt.2.1.ne_zero
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hSt.2.2.1.ne_zero
  obtain ⟨θ, hθ, -⟩ := GlobalTheory.TraceOne.exists_trace_one D 2 Nat.prime_two
  have hθ' : (θ : D.host.E) + star (θ : D.host.E) = 1 := by
    have := congrArg (algebraMap (𝓞 D.host.E) D.host.E) hθ
    rw [map_add, map_one] at this
    rw [GlobalTheory.NormSum.AdLattice.star_eq_conj]
    exact this
  choose st hst using fun o : 𝓞 D.host.E => star_int (E := D.host.E) ⟨o, rfl⟩
  have hst0 : st 0 = 0 := RingOfIntegers.ext (by rw [hst]; simp)
  have hst1 : st 1 = 1 := RingOfIntegers.ext (by rw [hst]; simp)
  obtain ⟨m, hm, hmf⟩ := exists_frame_op (F := lf D F0) θ hθ' hlat hΛ hT
    (fun j => ddS D ^ (-((D.R.rS : ℤ) - (j : ℕ)))) (fun j => zpow_ne_zero _ (ddS_ne_zero D))
    (fun a b hab => ddS_anti D (by have : a.val ≤ b.val := hab; omega))
    (coord_iff _ (by simp) hlift.1 hprim hX) (fun a b => st (A b a))
    (fun a b h => by rw [hA1 b a h, hst0]) (fun a => by rw [hA2, hst1])
  have hn := symm_mem_NLam hm
  obtain ⟨G, hGz, hG⟩ := exists_moved (F := F') hT' m.symm hn.1.1 B hB1 hB2
  have he : ∀ a, F0.e a ∈ Λ := fun a => (hX.symm ▸ e_mem_XS D F0 a : F0.e a ∈ XLam Λ (lf D F0)).1
  have he' : ∀ a, F'.fl.e a ∈ Λ := fun a => (hX'.symm ▸ e_mem_XS D F'.fl a : F'.fl.e a ∈ XLam Λ F').1
  have hf' : ∀ b, frame F' b ∈ Λ := fun b => by
    induction b using Fin.lastCases with
    | last => rw [frame_last]; exact hlift'.1
    | cast a => rw [frame_cast]; exact he' a
  have hGΛ : ∀ b, frame G b ∈ Λ := fun b => by
    rw [hG]
    exact Submodule.sum_mem _ fun a _ => smul_mem_of _ ⟨_, rfl⟩ ((aut_mem_iff hn.1 _).2 (hf' a))
  have hGe : ∀ a, G.fl.e a ∈ Λ := fun a => by rw [← frame_cast]; exact hGΛ _
  have hadj : ∀ x y, (hS D).hT x (m.symm y) = (hS D).hT (m x) y := fun x y => by
    rw [← hm.1.1 x, LinearEquiv.apply_symm_apply]
  refine ⟨G, ⟨⟨by rw [← frame_last]; exact hGΛ _, hGz⟩, hGe, ?_, hP.trans ?_⟩, m.symm, hn, B, hB1, hB2, hG⟩
  · rw [hZ]
    refine Matrix.ext fun a b => ?_
    change (hS D).hT (frame (lf D F0) a) (frame G b) = _
    rw [hG]
    simp only [frameAct, map_sum, map_smul, hadj, hmf, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]
    congr 1
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [LinearMap.map_smulₛₗ, hst, LinearMap.smul_apply, starRingEnd_apply, star_star]
    rfl
  · refine Submodule.comap_mono (sup_le ?_ le_sup_right)
    rintro x ⟨hx, hxH⟩
    obtain ⟨h1, h2⟩ := (mem_Hp_iff rfl hlift'.2 he he' x).1 hxH
    have e : x = m.symm x + -(m.symm x - x) := by abel
    rw [e]
    refine Submodule.add_mem_sup ⟨(aut_mem_iff hn.1 _).2 hx, (mem_Hp_iff rfl hGz he hGe _).2 ⟨fun b => ?_, fun b => ?_⟩⟩
      (Submodule.neg_mem _ (hn.2.2 x (orth_X_of_frame h1)))
    · rw [hadj, hmf]
      simp only [frameAct, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [h1, smul_zero]
    · rw [hG]
      simp only [frameAct, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [hn.1.1, h2, smul_zero]

end GlobalTheory.LoopC.FrameMove

end
