import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

def LetPt (Y : Finset ℝ) (y : ℝ) : Prop := y ∈ Y ∨ y - 1 ∈ Y

/- English proof (translation)
Introduce `l hl`. Take `⟨y, hy, h | h⟩` from `hw.2 l hl`. Substitute `h` using the available equality. Conclude with `Or.inl hy`. Substitute `h right` using the available equality.

Simplify using `using hy`.
-/
theorem letters_of_admissible_word_are_points {P : M.Par} {l0 : ℕ} {Y : Finset ℝ} {w : List C.Letter} (hw : TBB.AdmW P l0 Y w) :
    ∀ l ∈ w, LetPt Y l.2 := by
  intro l hl
  obtain ⟨y, hy, h | h⟩ := hw.2 l hl
  · subst h
    exact Or.inl hy
  · subst h
    right
    simpa using hy

section tools

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Use `letI : NormedAddCommGroup (Q.Mx k r) := Matrix.normedAddCommGroup`. Use `letI : NormedSpace ℝ (Q.Mx k r) := Matrix.normedSpace`. Establish `hz : Q.SmoothLev k r 0 Set.univ (fun _ : B.Mat k r => (0 : E))`. Introduce `g₀ _`. Conclude with `⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩`.

Establish `hadd : ∀ (f f₂ : B.Mat k r → E) (a : ℂ), Q.SmoothLev k r 0 Set.univ f → Q.SmoothLev k r 0 Set.univ f₂ → Q.SmoothLev k r 0 Set.univ (fun y => f y + a • f₂ y)`. Introduce `f f₂ a hf hf₂ g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hfe⟩` from `hf g₀ hg₀`. Take `⟨U₂, F₂, hU₂, hgU₂, hF₂, hfe₂⟩` from `hf₂ g₀ hg₀`. Use `⟨U ∩ U₂, fun y => F y + a • F₂ y, hU.inter hU₂, ⟨hgU, hgU₂⟩, (hF.mono Set.inter_subset_left).add ((hF₂.mono Set.inter_subset_right).const_smul a), ?_⟩` and prove the remaining obligations.

Introduce `g hg hgl`. Simplify using `only [hfe g hg.1 hgl, hfe₂ g hg.2 hgl]`. Establish `hT0 : ∀ x ∈ Q.Glev k r 0 ∩ Set.univ, T (fun _ => (0 : E)) x = 0`. Introduce `x hx`. Establish `h0` using `hT.lin (fun _ => 0) (fun _ => 0) (-1) hz hz x hx`.

Simplify using `only [smul_zero, add_zero] at h0`. Rewrite `h0` using `[neg_one_smul, add_neg_cancel]`. Conclude with `h0`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Simplify using `only [Finset.sum_empty]`. Conclude with `⟨hz, hT0⟩`. Consider the case `@insert i s hi ih`. Establish `e : (fun y => ∑ j ∈ insert i s, c j • h j y) = (fun y => (∑ j ∈ s, c j • h j y) + c i • h i y)`. Use function extensionality and compare the values at `y`.

Rewrite using `[Finset.sum_insert hi, add_comm]`. Rewrite using `[e]`. Use `⟨hadd _ _ _ ih.1 (hs i), fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[hT.lin _ _ _ ih.1 (hs i) x hx, ih.2 x hx, Finset.sum_insert hi, add_comm]`.
-/
theorem good_finsum {T : (B.Mat k r → E) → B.Mat k r → E} (hT : Qx2.Good k r 0 Set.univ T) {ι : Type*}
    (c : ι → ℂ) (h : ι → B.Mat k r → E) (hs : ∀ i, Q.SmoothLev k r 0 Set.univ (h i)) (s : Finset ι) :
    Q.SmoothLev k r 0 Set.univ (fun y => ∑ i ∈ s, c i • h i y) ∧
      ∀ x ∈ Q.Glev k r 0 ∩ Set.univ, T (fun y => ∑ i ∈ s, c i • h i y) x = ∑ i ∈ s, c i • T (h i) x := by
  classical
  letI : NormedAddCommGroup (Q.Mx k r) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Q.Mx k r) := Matrix.normedSpace
  have hz : Q.SmoothLev k r 0 Set.univ (fun _ : B.Mat k r => (0 : E)) := by
    intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
  have hadd : ∀ (f f₂ : B.Mat k r → E) (a : ℂ), Q.SmoothLev k r 0 Set.univ f → Q.SmoothLev k r 0 Set.univ f₂ →
      Q.SmoothLev k r 0 Set.univ (fun y => f y + a • f₂ y) := by
    intro f f₂ a hf hf₂ g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hfe⟩ := hf g₀ hg₀
    obtain ⟨U₂, F₂, hU₂, hgU₂, hF₂, hfe₂⟩ := hf₂ g₀ hg₀
    refine ⟨U ∩ U₂, fun y => F y + a • F₂ y, hU.inter hU₂, ⟨hgU, hgU₂⟩,
      (hF.mono Set.inter_subset_left).add ((hF₂.mono Set.inter_subset_right).const_smul a), ?_⟩
    intro g hg hgl
    simp only [hfe g hg.1 hgl, hfe₂ g hg.2 hgl]
  have hT0 : ∀ x ∈ Q.Glev k r 0 ∩ Set.univ, T (fun _ => (0 : E)) x = 0 := by
    intro x hx
    have h0 := hT.lin (fun _ => 0) (fun _ => 0) (-1) hz hz x hx
    simp only [smul_zero, add_zero] at h0
    rw [neg_one_smul, add_neg_cancel] at h0
    exact h0
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨hz, hT0⟩
  | @insert i s hi ih =>
    have e : (fun y => ∑ j ∈ insert i s, c j • h j y) = (fun y => (∑ j ∈ s, c j • h j y) + c i • h i y) := by
      funext y
      rw [Finset.sum_insert hi, add_comm]
    rw [e]
    refine ⟨hadd _ _ _ ih.1 (hs i), fun x hx => ?_⟩
    rw [hT.lin _ _ _ ih.1 (hs i) x hx, ih.2 x hx, Finset.sum_insert hi, add_comm]

/- English proof (translation)
The claim follows from `| [], _ => by simp | a :: L, h => by simp only [List.map_cons, List.prod_cons] rw [norm_mul] have ha := h a (List.mem_cons_self ..) have hL := norm_prod_map_le f g L fun b hb => h b (List.mem_cons_of_mem a hb) exact mul_le_mul ha hL (norm_nonneg _) ((norm_nonneg _).trans ha)`.
-/
theorem norm_prod_map_le {α : Type*} (f : α → ℂ) (g : α → ℝ) :
    ∀ L : List α, (∀ a ∈ L, ‖f a‖ ≤ g a) → ‖(L.map f).prod‖ ≤ (L.map g).prod
  | [], _ => by simp
  | a :: L, h => by
    simp only [List.map_cons, List.prod_cons]
    rw [norm_mul]
    have ha := h a (List.mem_cons_self ..)
    have hL := norm_prod_map_le f g L fun b hb => h b (List.mem_cons_of_mem a hb)
    exact mul_le_mul ha hL (norm_nonneg _) ((norm_nonneg _).trans ha)

end tools

section betaT

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Establish `hw : ∀ q : (Fin r → ℂ) × ℂ, 0 ≤ bcWeight k r (Tz k r D.z) (Tz k r D.z') q`. Introduce `q`. Unfold `bcWeight`. Use `split_ifs with h`. Conclude with `mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (sub_nonneg.mpr h) _)`.

Conclude with `le_refl 0`. Use `⟨∫ q : (Fin r → ℂ) × ℂ, bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (bigCell k r q.1 (D.μsec q.2)))‖ ^ 2, MeasureTheory.integral_nonneg (fun q => mul_nonneg (hw q) (sq_nonneg _)), ?_⟩` and prove the remaining obligations. Unfold `B.beta betaBig`. Rewrite using `[← integral_complex_ofReal]`. Use `congr 1`.

Use function extensionality and compare the values at `q`. Simplify using `[inner_self_eq_norm_sq_to_K]`.
-/
theorem beta_self_real (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    ∃ t : ℝ, 0 ≤ t ∧ B.beta D F F = t := by
  have hw : ∀ q : (Fin r → ℂ) × ℂ, 0 ≤ bcWeight k r (Tz k r D.z) (Tz k r D.z') q := by
    intro q
    unfold bcWeight
    split_ifs with h
    · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (sub_nonneg.mpr h) _)
    · exact le_refl 0
  refine ⟨∫ q : (Fin r → ℂ) × ℂ, bcWeight k r (Tz k r D.z) (Tz k r D.z') q *
      ‖B.hsVec (B.JF D F (bigCell k r q.1 (D.μsec q.2)))‖ ^ 2,
    MeasureTheory.integral_nonneg (fun q => mul_nonneg (hw q) (sq_nonneg _)), ?_⟩
  unfold B.beta betaBig
  rw [← integral_complex_ofReal]
  congr 1
  funext q
  simp [inner_self_eq_norm_sq_to_K]

/- English proof (translation)
Establish `h : ∀ g, B.hsVec (B.JF D 0 g) = 0`. Introduce `g`. Establish `: B.JF D 0 g = 0` using `by simp [B.JF, besselJ]`. Rewrite using `[this]`. Use extensionality with `i`.

Simplify using `[B.hsVec]`. Simplify using `[B.beta, betaBig, h]`.
-/
theorem beta_zero_left' (D : B.RealPlaceData k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp)) : B.beta D 0 G = 0 := by
  have h : ∀ g, B.hsVec (B.JF D 0 g) = 0 := by
    intro g
    have : B.JF D 0 g = 0 := by simp [B.JF, besselJ]
    rw [this]; ext i; simp [B.hsVec]
  simp [B.beta, betaBig, h]

variable [FiniteDimensional ℂ Wp]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `beta_zero_left' D G`. Consider the case `insert a s ha ih`.

Establish `hS : B.InCC A 5 (fun g => ∑ i ∈ s, c i • h i g)` using `JCx2.sq_inCC_sum s _ fun i _ => JCx2.sq_inCC_smul (c i) (hh i)`. Establish `e : (fun g => ∑ i ∈ insert a s, c i • h i g) = (fun g => ∑ i ∈ s, c i • h i g) + c a • h a`. Use function extensionality and compare the values at `g`. Simplify using `only [Finset.sum_insert ha, Pi.add_apply, Pi.smul_apply]`. Rewrite using `[add_comm]`.

Rewrite using `[e, (JCx2.sq_beta_sesq D hA hS (hh a) hG (c a)).1, ih, Finset.sum_insert ha, add_comm]`.
-/
theorem beta_sum_left (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : B.AB k r ≤ A) {ι : Type*} (c : ι → ℂ)
    (h : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (hh : ∀ i, B.InCC A 5 (h i)) {G : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hG : B.InCC A 5 G) (s : Finset ι) :
    B.beta D (fun g => ∑ i ∈ s, c i • h i g) G = ∑ i ∈ s, c i * B.beta D (h i) G := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact beta_zero_left' D G
  | insert a s ha ih =>
    have hS : B.InCC A 5 (fun g => ∑ i ∈ s, c i • h i g) :=
      JCx2.sq_inCC_sum s _ fun i _ => JCx2.sq_inCC_smul (c i) (hh i)
    have e : (fun g => ∑ i ∈ insert a s, c i • h i g) =
        (fun g => ∑ i ∈ s, c i • h i g) + c a • h a := by
      funext g
      simp only [Finset.sum_insert ha, Pi.add_apply, Pi.smul_apply]
      rw [add_comm]
    rw [e, (JCx2.sq_beta_sesq D hA hS (hh a) hG (c a)).1, ih, Finset.sum_insert ha, add_comm]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `Dx1.LZ.beta_zero_right D G`. Consider the case `insert a s ha ih`.

Establish `hS : B.InCC A 5 (fun g => ∑ i ∈ s, h i g)` using `JCx2.sq_inCC_sum s _ fun i _ => hh i`. Establish `e : (fun g => ∑ i ∈ insert a s, h i g) = (fun g => ∑ i ∈ s, h i g) + (1 : ℂ) • h a`. Use function extensionality and compare the values at `g`. Simplify using `only [Finset.sum_insert ha, Pi.add_apply, one_smul]`. Rewrite using `[add_comm]`.

Rewrite using `[e, (JCx2.sq_beta_sesq D hA hS (hh a) hG 1).2, ih, Finset.sum_insert ha, map_one, one_mul, add_comm]`.
-/
theorem beta_sum_right (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : B.AB k r ≤ A) {ι : Type*}
    (h : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (hh : ∀ i, B.InCC A 5 (h i)) {G : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hG : B.InCC A 5 G) (s : Finset ι) :
    B.beta D G (fun g => ∑ i ∈ s, h i g) = ∑ i ∈ s, B.beta D G (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Dx1.LZ.beta_zero_right D G
  | insert a s ha ih =>
    have hS : B.InCC A 5 (fun g => ∑ i ∈ s, h i g) := JCx2.sq_inCC_sum s _ fun i _ => hh i
    have e : (fun g => ∑ i ∈ insert a s, h i g) = (fun g => ∑ i ∈ s, h i g) + (1 : ℂ) • h a := by
      funext g
      simp only [Finset.sum_insert ha, Pi.add_apply, one_smul]
      rw [add_comm]
    rw [e, (JCx2.sq_beta_sesq D hA hS (hh a) hG 1).2, ih, Finset.sum_insert ha, map_one, one_mul, add_comm]

end betaT

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def EigStr (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) : Prop :=
  ∃ (A : ℝ) (n : ℕ) (h : Fin n → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ev : Fin n → ℝ → ℂ),
    B.AB P.k P.r ≤ A ∧ (∀ i, B.CkOn ⊤ (B.GV P.k P.r) (h i)) ∧ (∀ i, B.InCC A 5 (h i)) ∧
    (∀ g ∈ B.GV P.k P.r, F g = ∑ i, h i g) ∧
    (∀ i y, LetPt Y y → ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (y : ℂ) (h i) g = ev i y • h i g) ∧
    (∀ i y, LetPt Y y → ‖ev i y‖ ≤ nn y) ∧
    (∀ i j, i ≠ j → B.beta p.T.base (h i) (h j) = 0)

/- English proof (translation)
The claim follows from `| [], _, g, hg => by simpa using hF g hg | a :: L, hL, g, hg => by have ih := fold_eig s Y h ev hs he hF L (fun l hl => hL l (List.mem_cons_of_mem a hl)) have hsm : ∀ i, Q.SmoothLev k r 0 Set.univ (h i) := fun i => Dx1.LZ.smooth_of_ck (hs i) have hlin := (good_finsum (Dx1.LZ.good …`.
-/
theorem fold_eig {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} (s : ℂ) (Y : Finset ℝ)
    (h : Fin n → B.Mat k r → E) (ev : Fin n → ℝ → ℂ) (hs : ∀ i, B.CkOn ⊤ (B.GV k r) (h i))
    (he : ∀ i y, LetPt Y y → ∀ g ∈ B.GV k r, Q.CV k r (y : ℂ) (h i) g = ev i y • h i g)
    {F : B.Mat k r → E} (hF : ∀ g ∈ B.GV k r, F g = ∑ i, h i g) :
    ∀ L : List C.Letter, (∀ l ∈ L, LetPt Y l.2) → ∀ g ∈ B.GV k r,
      L.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) F g = ∑ i, (L.map fun a => s * ev i a.2).prod • h i g
  | [], _, g, hg => by simpa using hF g hg
  | a :: L, hL, g, hg => by
    have ih := fold_eig s Y h ev hs he hF L (fun l hl => hL l (List.mem_cons_of_mem a hl))
    have hsm : ∀ i, Q.SmoothLev k r 0 Set.univ (h i) := fun i => Dx1.LZ.smooth_of_ck (hs i)
    have hlin := (good_finsum (Dx1.LZ.good_CV (k := k) (r := r) (E := E) (a.2 : ℂ))
      (fun i => (L.map fun a => s * ev i a.2).prod) h hsm Finset.univ).2 g (Dx1.LZ.glev0 hg)
    have hloc := (Dx1.LZ.good_CV (k := k) (r := r) (E := E) (a.2 : ℂ)).loc
      (L.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) F)
      (fun y => ∑ i, (L.map fun a => s * ev i a.2).prod • h i y) (fun y hy => ih y hy.1.1) g (Dx1.LZ.glev0 hg)
    have ha := hL a (List.mem_cons_self ..)
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, Pi.smul_apply]
    rw [hloc, hlin, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he i a.2 ha g hg, smul_smul, smul_smul]
    ring_nf

/- English proof (translation)
Take `⟨A, n, h, ev, hA, hs, hcc, hF, he, hev, horth⟩` from `hE`. Introduce `w hw _`. Use `set s : ℂ := M.sgn P p.l0 with hsdef`. Establish `hs1 : ‖s‖ = 1` using `by simp [hsdef, M.sgn]`. Use `set c : Fin n → ℂ := fun i => (w.map fun a => s * ev i a.2).prod with hc`.

Establish `hFck : B.CkOn ⊤ (B.GV P.k P.r) F` using `Qb1.ckOn_congr (fun g hg => (hF g hg).symm) (JCx2.sq_ckOn_sum Finset.univ h fun i _ => hs i)`. Establish `hLet` using `letters_of_admissible_word_are_points hw`. Establish `hRR : p.RR F 0 w [] [] = B.beta p.T.base (fun g => ∑ i, c i • h i g) (fun g => ∑ j, h j g)`. Unfold `KB.Pl.RR`. Rewrite using `[Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hFck (good_positioned_of_cut hw.1)]`.

Unfold `C7.principalHermitianLattice`. Rewrite using `[JCx2.sq_beta_congr _ (fold_eig s Y h ev hs he hF w hLet)]`. Conclude with `beta_congr_right _ hF`. Establish `hBF : B.beta p.T.base F F = B.beta p.T.base (fun g => ∑ i, (1 : ℂ) • h i g) (fun g => ∑ j, h j g)`. Rewrite using `[JCx2.sq_beta_congr _ (F₂ := fun g => ∑ i, (1 : ℂ) • h i g) (fun g hg => by simp [hF g hg]), beta_congr_right _ hF]`.

Establish `hSum : B.InCC A 5 (fun g => ∑ j, h j g)` using `JCx2.sq_inCC_sum _ _ fun i _ => hcc i`. Establish `hexp : ∀ d : Fin n → ℂ, B.beta p.T.base (fun g => ∑ i, d i • h i g) (fun g => ∑ j, h j g) = ∑ i, d i * B.beta p.T.base (h i) (h i)`. Introduce `d`. Rewrite using `[beta_sum_left p.T.base hA d h hcc hSum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[beta_sum_right p.T.base hA h hcc (hcc i), Finset.sum_eq_single i]`. Introduce `j _ hji`. Conclude with `horth i j (Ne.symm hji)`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`.

Rewrite using `[hRR, hBF, hexp, hexp]`. Establish `hcn : ∀ i, ‖c i‖ ≤ TBB.normC nn w`. Introduce `i`. Unfold `TBB.normC`. Use `norm_prod_map_le (fun a => s * ev i a.2) (fun l => nn l.2) w fun a ha => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, hs1, one_mul]`. Conclude with `hev i a.2 (hLet a ha)`. Simplify using `only [one_mul, Complex.re_sum, Finset.mul_sum]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Take `⟨t, ht, hbt⟩` from `beta_self_real p.T.base (h i)`.

Rewrite using `[hbt, Complex.re_mul_ofReal, Complex.ofReal_re]`. Conclude with `mul_le_mul_of_nonneg_right ((Complex.re_le_norm _).trans (hcn i)) ht`.
-/
theorem limBd_of_eigStr (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (N : ℕ) (hE : EigStr p nn F Y) : LimBd p nn F Y N := by
  classical
  obtain ⟨A, n, h, ev, hA, hs, hcc, hF, he, hev, horth⟩ := hE
  intro w hw _
  set s : ℂ := M.sgn P p.l0 with hsdef
  have hs1 : ‖s‖ = 1 := by simp [hsdef, M.sgn]
  set c : Fin n → ℂ := fun i => (w.map fun a => s * ev i a.2).prod with hc
  have hFck : B.CkOn ⊤ (B.GV P.k P.r) F :=
    Qb1.ckOn_congr (fun g hg => (hF g hg).symm) (JCx2.sq_ckOn_sum Finset.univ h fun i _ => hs i)
  have hLet := letters_of_admissible_word_are_points hw

  have hRR : p.RR F 0 w [] [] = B.beta p.T.base (fun g => ∑ i, c i • h i g) (fun g => ∑ j, h j g) := by
    unfold KB.Pl.RR
    rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hFck (good_positioned_of_cut hw.1)]
    unfold C7.principalHermitianLattice
    rw [JCx2.sq_beta_congr _ (fold_eig s Y h ev hs he hF w hLet)]
    exact beta_congr_right _ hF
  have hBF : B.beta p.T.base F F = B.beta p.T.base (fun g => ∑ i, (1 : ℂ) • h i g) (fun g => ∑ j, h j g) := by
    rw [JCx2.sq_beta_congr _ (F₂ := fun g => ∑ i, (1 : ℂ) • h i g) (fun g hg => by simp [hF g hg]),
      beta_congr_right _ hF]
  have hSum : B.InCC A 5 (fun g => ∑ j, h j g) := JCx2.sq_inCC_sum _ _ fun i _ => hcc i
  have hexp : ∀ d : Fin n → ℂ, B.beta p.T.base (fun g => ∑ i, d i • h i g) (fun g => ∑ j, h j g) =
      ∑ i, d i * B.beta p.T.base (h i) (h i) := by
    intro d
    rw [beta_sum_left p.T.base hA d h hcc hSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [beta_sum_right p.T.base hA h hcc (hcc i), Finset.sum_eq_single i]
    · intro j _ hji
      exact horth i j (Ne.symm hji)
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hRR, hBF, hexp, hexp]
  have hcn : ∀ i, ‖c i‖ ≤ TBB.normC nn w := by
    intro i
    unfold TBB.normC
    refine norm_prod_map_le (fun a => s * ev i a.2) (fun l => nn l.2) w fun a ha => ?_
    rw [norm_mul, hs1, one_mul]
    exact hev i a.2 (hLet a ha)
  simp only [one_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨t, ht, hbt⟩ := beta_self_real p.T.base (h i)
  rw [hbt, Complex.re_mul_ofReal, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right ((Complex.re_le_norm _).trans (hcn i)) ht

end place

/- English proof (translation)
Take `⟨C₄, hC⟩` from `thmBpAt_of_leaves_limBd hA C₃ CΛ C₀ Cκ hC₃ hCΛ hC₀`. Use `⟨C₄, ?_⟩` and prove the remaining obligations. Introduce `Wp Wq _ _ _ _ _ _ P p f Ap Am ApPt AmPt b Λ κ₀ n₀ p₀ χ nn Y K N Cb h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hEp hEm hLp hLm`. Conclude with `hC Wp Wq P p f Ap Am ApPt AmPt b Λ κ₀ n₀ p₀ χ nn Y K N Cb h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 (limBd_of_eigStr p nn _ Y N hEp) (limBd_of_eigStr p nn _ Y N hEm) hLp hLm`.
-/
theorem thmBpAt_of_leaves_eigStr (hA : P5.ThmPActual) (C₃ CΛ C₀ Cκ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ)
    (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap Am : B.Mat P.k P.r → (Wq →L[ℂ] Wq))
      (ApPt AmPt : C.LPt → (Wq →L[ℂ] Wq)) (b Λ κ₀ : ℝ) (n₀ p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ)
      (Cb : ℝ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 0 < κ₀ →
      κ₀ ≤ b ^ (Cκ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2) → 1 ≤ TBB.Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base f →
      B.CkOn ⊤ (B.GV P.k P.r) Ap → B.CkOn ⊤ (B.GV P.k P.r) Am →
      Amaps p f Ap Am ApPt AmPt b n₀ → BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      GermCutPD p nn χ (TBBx4.fpm p f Ap p₀) Y K N → GermCutPD p nn χ (TBBx4.fpm p f Am p₀) Y K N →
      EigStr p nn (TBBx4.fpm p f Ap p₀) Y → EigStr p nn (TBBx4.fpm p f Am p₀) Y →
      LemB p (TBBx4.fpm p f Ap p₀) κ₀ → LemB p (TBBx4.fpm p f Am p₀) κ₀ →
      TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  obtain ⟨C₄, hC⟩ := thmBpAt_of_leaves_limBd hA C₃ CΛ C₀ Cκ hC₃ hCΛ hC₀
  refine ⟨C₄, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f Ap Am ApPt AmPt b Λ κ₀ n₀ p₀ χ nn Y K N Cb h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hEp hEm hLp hLm
  exact hC Wp Wq P p f Ap Am ApPt AmPt b Λ κ₀ n₀ p₀ χ nn Y K N Cb h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
    (limBd_of_eigStr p nn _ Y N hEp) (limBd_of_eigStr p nn _ Y N hEm) hLp hLm

end

end Formalism.FourierDecayAlt.P.CutBP
