import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.WordIdAt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.WdValAppend
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.UnitaryAdjointHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupG
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HermitianConvolution.NontrivInfPf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace PositivityTheory.Rg.BcB.F.B3

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PTop

section Generic

variable {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)]
  [∀ s, InnerProductSpace ℂ (H s)] [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simp [wdVal]`. Consider the case `cons p w ih`. Simplify using `only [wdVal, List.map_cons, List.prod_cons, Prod.snd_mul] at ih ⊢`. Rewrite using `[ih]`.

Use `congr 1`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem wdVal_snd (gen : Γ → Prod' H d) (w : List (Γ × Bool)) :
    (wdVal gen w).2 = wdVal (fun x => (gen x).2) w := by
  induction w with
  | nil => simp [wdVal]
  | cons p w ih =>
    simp only [wdVal, List.map_cons, List.prod_cons, Prod.snd_mul] at ih ⊢
    rw [ih]
    congr 1
    split_ifs <;> simp

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simp [wdVal]`. Consider the case `cons p w ih`. Simplify using `only [wdVal, List.map_cons, List.prod_cons, Prod.fst_mul, Pi.mul_apply] at ih ⊢`. Rewrite using `[ih]`.

Use `congr 1`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem wdVal_fst (gen : Γ → Prod' H d) (w : List (Γ × Bool)) (s : ι) :
    (wdVal gen w).1 s = wdVal (fun x => (gen x).1 s) w := by
  induction w with
  | nil => simp [wdVal]
  | cons p w ih =>
    simp only [wdVal, List.map_cons, List.prod_cons, Prod.fst_mul, Pi.mul_apply] at ih ⊢
    rw [ih]
    congr 1
    split_ifs <;> simp

/- English proof (translation)
Introduce `a ha _`. Take `⟨J, _, c, w, L, -, rfl, hpow⟩` from `adjWords _ _ gen a ha`. Take `⟨t, ht, hb⟩` from `hW J c w`. Use `SG.boundAt_of β m u _ t 0 ?_ ?_` and prove the remaining obligations. Establish `hc : Commute u (∑ j, c j • wdVal gen (w j)).2`.

Rewrite using `[Prod.snd_sum]`. Use `Commute.sum_right _ _ _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Prod.smul_snd]`. Use `Commute.smul_right ?_ _` and prove the remaining obligations. Rewrite using `[wdVal_snd]`.

Use `Commute.list_prod_right _ _ fun y hy => ?_` and prove the remaining obligations. Take `⟨p, -, rfl⟩` from `List.mem_map.1 hy`. Use `split_ifs`. Conclude with `(hu p.1).2`. Conclude with `(hu p.1).1`.

Use `filter_upwards [eventually_ge_atTop 1] with k hk`. Rewrite using `[← ht k hk]`. Unfold `SG.trU`. Rewrite using `[hc.mul_pow, ← Prod.pow_snd, hpow, Prod.snd_sum, Finset.mul_sum, ContinuousLinearMap.coe_sum, map_sum]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations.

Rewrite using `[Prod.smul_snd, mul_smul_comm, ContinuousLinearMap.coe_smul, map_smul, smul_eq_mul, wdVal_snd]`. Introduce `s`. Take `⟨C, N, hC⟩` from `hb s`. Establish `e : (∑ j, c j • wdVal gen (w j)).1 s = ∑ j, c j • wdVal (fun x => (gen x).1 s) (w j)`. Rewrite using `[Prod.fst_sum, Finset.sum_apply]`.

Simplify using `only [Prod.smul_fst, Pi.smul_apply, wdVal_fst]`. Conclude with `⟨C, N, by filter_upwards [eventually_ge_atTop 1] with k hk`. Rewrite using `[e, Nat.sub_zero]`. Conclude with `hC k hk⟩`.
-/
theorem gBound_words (gen : Γ → Prod' H d) (a₀ : Γ) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ)
    (u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (hu : ∀ x, Commute u (gen x).2 ∧ Commute u (star (gen x).2))
    (hW : ∀ (J : Type) [Fintype J] (c : J → ℂ) (w : J → List (Γ × Bool)), ∃ t : ι → ℕ → ℂ,
      (∀ k, 1 ≤ k → ∑ f : Fin k → J, (∏ i, c (f i)) *
        LinearMap.trace ℂ _ ((u ^ k * wdVal (fun x => (gen x).2) (List.ofFn fun i => w (f i)).flatten :
          EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :
          EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) = ∑ s, t s k) ∧
      ∀ s, ∃ (C : ℝ) (N : ℕ), ∀ k, 1 ≤ k →
        ‖t s k‖ ≤ C * (1 + k) ^ N * ‖(β s ^ m * ∑ j, c j • wdVal (fun x => (gen x).1 s) (w j)) ^ k‖) :
    GBound gen a₀ β m u := by
  intro a ha _
  obtain ⟨J, _, c, w, L, -, rfl, hpow⟩ := adjWords _ _ gen a ha
  obtain ⟨t, ht, hb⟩ := hW J c w
  refine SG.boundAt_of β m u _ t 0 ?_ ?_
  · have hc : Commute u (∑ j, c j • wdVal gen (w j)).2 := by
      rw [Prod.snd_sum]
      refine Commute.sum_right _ _ _ fun j _ => ?_
      rw [Prod.smul_snd]
      refine Commute.smul_right ?_ _
      rw [wdVal_snd]
      refine Commute.list_prod_right _ _ fun y hy => ?_
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hy
      split_ifs
      · exact (hu p.1).2
      · exact (hu p.1).1
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [← ht k hk]
    unfold SG.trU
    rw [hc.mul_pow, ← Prod.pow_snd, hpow, Prod.snd_sum, Finset.mul_sum, ContinuousLinearMap.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Prod.smul_snd, mul_smul_comm, ContinuousLinearMap.coe_smul, map_smul, smul_eq_mul, wdVal_snd]
  · intro s
    obtain ⟨C, N, hC⟩ := hb s
    have e : (∑ j, c j • wdVal gen (w j)).1 s = ∑ j, c j • wdVal (fun x => (gen x).1 s) (w j) := by
      rw [Prod.fst_sum, Finset.sum_apply]
      simp only [Prod.smul_fst, Pi.smul_apply, wdVal_fst]
    exact ⟨C, N, by
      filter_upwards [eventually_ge_atTop 1] with k hk
      rw [e, Nat.sub_zero]
      exact hC k hk⟩

end Generic

/- English proof (translation)
Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression.
-/
theorem map_ofFn' {α β : Type} {k : ℕ} (g : α → β) (h : Fin k → α) :
    (List.ofFn h).map g = List.ofFn (fun i => g (h i)) := by
  rw [List.map_ofFn]; rfl

/- English proof (translation)
Break down `g with c | t` into its components or cases. Use `⟨trivial, ?_⟩ show (starRingEnd ℂ c) • (1 : B.Hb →L[ℂ] B.Hb) = star (c • (1 : B.Hb →L[ℂ] B.Hb))` and prove the remaining obligations. Rewrite using `[star_smul, star_one]`. Both sides reduce to the same expression. Use `BlockFiniteConvolution.blkOp₀ E B t t hg hg` as an intermediate fact.

Conclude with `⟨this.2.2.2.2.1, by rw [ContinuousLinearMap.star_eq_adjoint]; exact this.2.2.2.2.2.1⟩`.
-/
theorem bgen_adj {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E) (g : BGen B) (hg : g.Ok) :
    g.adj.Ok ∧ g.adj.op = star g.op := by
  rcases g with c | t
  · refine ⟨trivial, ?_⟩
    show (starRingEnd ℂ c) • (1 : B.Hb →L[ℂ] B.Hb) = star (c • (1 : B.Hb →L[ℂ] B.Hb))
    rw [star_smul, star_one]
    rfl
  · have := BlockFiniteConvolution.blkOp₀ E B t t hg hg
    exact ⟨this.2.2.2.2.1, by rw [ContinuousLinearMap.star_eq_adjoint]; exact this.2.2.2.2.2.1⟩

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S}
  (F : RunFrame F₀ T)

/- English proof (translation)
Take `⟨-, hT, hS, hB, -⟩` from `hw`. Simplify using `[LocData.B, hT, hS, hB]`.
-/
theorem good_notin_B {w : Pl E} (hw : F.d.Good w) : w ∉ F.d.B := by
  obtain ⟨-, hT, hS, hB, -⟩ := hw
  simp [LocData.B, hT, hS, hB]

/- English proof (translation)
Break down `x with _ | x | x` into its components or cases. Conclude with `trivial`. Conclude with `trivial`. Conclude with `⟨x.1.2.1, good_notin_B F x.1.2.2, GlobalTheory.CompanionTheory.MatchWord.isHecke_hU F.d F.ok (if_pos x.1.2.2.1) x.2.1⟩`.
-/
theorem ug_ok (x : F.Γ) : (F.ug x).Ok F₀.Sec F.d.B := by
  rcases x with _ | x | x
  · exact trivial
  · exact trivial
  · exact ⟨x.1.2.1, good_notin_B F x.1.2.2, GlobalTheory.CompanionTheory.MatchWord.isHecke_hU F.d F.ok (if_pos x.1.2.2.1) x.2.1⟩

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons p w ih`. Simplify using `only [wdVal, List.map_cons, List.prod_cons] at ih ⊢`. Rewrite using `[ih]`.

Use `congr 1`. Take `⟨x, b⟩` from `p`. Consider the cases of `b`. Simplify using `[ul]`. Simplify using `only [ul, if_true]`.

Conclude with `(U.unitary_adjoint_holds E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff (F.ug x) (ug_ok F x)).2.symm`.
-/
theorem u_word (hE : GlobalTheory.BCT.Unr E) (w : List (F.Γ × Bool)) :
    wdVal (fun x => F.R.op (F.ug x)) w = ((w.map (ul F)).map F.R.op).prod := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    simp only [wdVal, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    congr 1
    obtain ⟨x, b⟩ := p
    cases b
    · simp [ul]
    · simp only [ul, if_true]
      exact (U.unitary_adjoint_holds E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff (F.ug x)
        (ug_ok F x)).2.symm

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons p w ih`. Simplify using `only [wdVal, List.map_cons, List.prod_cons] at ih ⊢`. Rewrite using `[ih]`.

Use `congr 1`. Take `⟨x, b⟩` from `p`. Consider the cases of `b`. Simplify using `[gl]`. Simplify using `only [gl, if_true]`.

Conclude with `(bgen_adj _ _ (hS.ok x i)).2.symm`.
-/
theorem b_word (hS : F.Struct) (i : F₀.C.ι) (w : List (F.Γ × Bool)) :
    wdVal (fun x => (F.g x i).op) w = ((w.map (gl F i)).map BGen.op).prod := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    simp only [wdVal, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    congr 1
    obtain ⟨x, b⟩ := p
    cases b
    · simp [gl]
    · simp only [gl, if_true]
      exact (bgen_adj _ _ (hS.ok x i)).2.symm

/- English proof (translation)
Introduce `g hg`. Simplify using `only [bw, List.mem_append, List.mem_replicate, List.mem_map] at hg`. Break down `hg with ⟨-, rfl⟩ | ⟨p, -, rfl⟩` into its components or cases. Conclude with `hS.βok i`. Take `⟨x, b⟩` from `p`.

Consider the cases of `b`. Conclude with `hS.ok x i`. Conclude with `(bgen_adj _ _ (hS.ok x i)).1`.
-/
theorem bw_ok (hS : F.Struct) (i : F₀.C.ι) (w : List (F.Γ × Bool)) : ∀ g ∈ bw F i w, g.Ok := by
  intro g hg
  simp only [bw, List.mem_append, List.mem_replicate, List.mem_map] at hg
  rcases hg with ⟨-, rfl⟩ | ⟨p, -, rfl⟩
  · exact hS.βok i
  · obtain ⟨x, b⟩ := p
    cases b
    · exact hS.ok x i
    · exact (bgen_adj _ _ (hS.ok x i)).1

/- English proof (translation)
Simplify using `only [bw, List.map_append, List.map_replicate, List.prod_append, List.prod_replicate]`. Both sides reduce to the same expression.
-/
theorem bw_prod (i : F₀.C.ι) (w : List (F.Γ × Bool)) :
    ((bw F i w).map BGen.op).prod = (F.β i).op ^ F.m * ((w.map (gl F i)).map BGen.op).prod := by
  simp only [bw, List.map_append, List.map_replicate, List.prod_append, List.prod_replicate]
  rfl

/- English proof (translation)
Take `⟨cc, c₀, hc₀, hid⟩` from `hw`. Use `⟨fun s k => cc s * ∑ f : Fin k → J, (∏ i, c (f i)) * BGen.sc (List.ofFn fun l => bw F s (w (f l))).flatten * ellSum2 (F₀.C.μG (F₀.C.a s)) (F₀.C.μG (n - F₀.C.a s)) (trM (BGen.wd (Sum.inr (F.t₁ s) :: (List.ofFn fun l => bw F s (w (f l))).flatten) (F.t₂ s)).Φ (MM F s)), ?_, ?_⟩` and prove the remaining obligations. Introduce `k hk`. Establish `key : ∀ f : Fin k → J, LinearMap.trace ℂ _ ((F.R.u ^ k * wdVal (fun x => F.R.op (F.ug x)) (List.ofFn fun i => w (f i)).flatten : EuclideanSpace ℂ (Fin F.R.d) →L[ℂ] EuclideanSpace ℂ (Fin F.R.d)) : EuclideanSpace ℂ (Fin F.R.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin F.R.d)) = ∑ s, cc s * (BGen …`. Introduce `f`.

Establish `hne : (List.ofFn fun i => w (f i)) ≠ []`. Rewrite using `[Ne, List.ofFn_eq_nil_iff]`. Use linear arithmetic over natural numbers and integers. Establish `e` using `(hid _ hne).2`. Rewrite `e` using `[List.length_ofFn]`.

Unfold `tw at e`. Simplify using `only [map_ofFn'] at e`. Rewrite using `[u_word F hE]`. Conclude with `e`. Use `(Finset.sum_congr rfl fun f _ => by rw [key f, Finset.mul_sum]).trans ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Introduce `s`.

Use `F₀.C.hG (F₀.C.a s)` as an intermediate fact. Use `F₀.C.hG (n - F₀.C.a s)` as an intermediate fact. Take `⟨C, N, hC⟩` from `BlockFiniteConvolution.blkGrowth₁ E (F.B s) (F₀.C.μG (F₀.C.a s)) (F₀.C.μG (n - F₀.C.a s)) ((F₀.A s).growth F.κ) (MM F s) (F.t₁ s) (F.t₂ s) J c (fun j => bw F s (w j)) (c₀ s) (hc₀ s) (hS.tok s).1 (hS.tok s).2 (fun j => bw_ok F hS s (w j))`. Use `⟨‖cc s‖ * C, N, fun k hk => ?_⟩` and prove the remaining obligations. Establish `adm : ∀ f : Fin k → J, ∀ t, t = BGen.wd (Sum.inr (F.t₁ s) :: (List.ofFn fun i => bw F s (w (f i))).flatten) (F.t₂ s) → D4.IsTest2J (trM t.Φ (MM F s)) (c₀ s * (1 + t.T) + t.r)`.

Introduce `f t ht`. Establish `hne : (List.ofFn fun i => w (f i)) ≠ []`. Rewrite using `[Ne, List.ofFn_eq_nil_iff]`. Use linear arithmetic over natural numbers and integers. Establish `e` using `(hid _ hne).1 s`.

Unfold `tw at e`. Rewrite `e` using `[map_ofFn']`. Substitute `ht` using the available equality. Conclude with `e`. Establish `hb` using `hC k adm`.

Establish `hsum : ∑ j, c j • ((bw F s (w j)).map BGen.op).prod = (F.β s).op ^ F.m * ∑ j, c j • wdVal (fun x => (F.g x s).op) (w j)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, bw_prod, b_word F hS s (w j)]`. Rewrite `hb` using `[hsum]`.

Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hW_frame (hE : GlobalTheory.BCT.Unr E) (hS : F.Struct) [Nontrivial (InfinitePlace E)] (hw : WordIdAt F)
    (J : Type) [Fintype J] (c : J → ℂ) (w : J → List (F.Γ × Bool)) :
    ∃ t : F₀.C.ι → ℕ → ℂ,
      (∀ k, 1 ≤ k → ∑ f : Fin k → J, (∏ i, c (f i)) *
        LinearMap.trace ℂ _ ((F.R.u ^ k * wdVal (fun x => F.R.op (F.ug x)) (List.ofFn fun i => w (f i)).flatten :
          EuclideanSpace ℂ (Fin F.R.d) →L[ℂ] EuclideanSpace ℂ (Fin F.R.d)) :
          EuclideanSpace ℂ (Fin F.R.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin F.R.d)) = ∑ s, t s k) ∧
      ∀ s, ∃ (C : ℝ) (N : ℕ), ∀ k, 1 ≤ k →
        ‖t s k‖ ≤ C * (1 + k) ^ N * ‖((F.β s).op ^ F.m * ∑ j, c j • wdVal (fun x => (F.g x s).op) (w j)) ^ k‖ := by
  obtain ⟨cc, c₀, hc₀, hid⟩ := hw
  refine ⟨fun s k => cc s * ∑ f : Fin k → J, (∏ i, c (f i)) * BGen.sc (List.ofFn fun l => bw F s (w (f l))).flatten *
      ellSum2 (F₀.C.μG (F₀.C.a s)) (F₀.C.μG (n - F₀.C.a s))
        (trM (BGen.wd (Sum.inr (F.t₁ s) :: (List.ofFn fun l => bw F s (w (f l))).flatten) (F.t₂ s)).Φ (MM F s)), ?_, ?_⟩
  · intro k hk
    have key : ∀ f : Fin k → J, LinearMap.trace ℂ _ ((F.R.u ^ k *
        wdVal (fun x => F.R.op (F.ug x)) (List.ofFn fun i => w (f i)).flatten :
          EuclideanSpace ℂ (Fin F.R.d) →L[ℂ] EuclideanSpace ℂ (Fin F.R.d)) :
          EuclideanSpace ℂ (Fin F.R.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin F.R.d)) =
        ∑ s, cc s * (BGen.sc (List.ofFn fun l => bw F s (w (f l))).flatten *
          ellSum2 (F₀.C.μG (F₀.C.a s)) (F₀.C.μG (n - F₀.C.a s))
            (trM (BGen.wd (Sum.inr (F.t₁ s) :: (List.ofFn fun l => bw F s (w (f l))).flatten) (F.t₂ s)).Φ (MM F s))) := by
      intro f
      have hne : (List.ofFn fun i => w (f i)) ≠ [] := by
        rw [Ne, List.ofFn_eq_nil_iff]; omega
      have e := (hid _ hne).2
      rw [List.length_ofFn] at e
      unfold tw at e
      simp only [map_ofFn'] at e
      rw [u_word F hE]
      exact e
    refine (Finset.sum_congr rfl fun f _ => by rw [key f, Finset.mul_sum]).trans ?_
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun f _ => ?_
    ring
  · intro s
    have := F₀.C.hG (F₀.C.a s)
    have := F₀.C.hG (n - F₀.C.a s)
    obtain ⟨C, N, hC⟩ := BlockFiniteConvolution.blkGrowth₁ E (F.B s) (F₀.C.μG (F₀.C.a s)) (F₀.C.μG (n - F₀.C.a s))
      ((F₀.A s).growth F.κ) (MM F s) (F.t₁ s) (F.t₂ s) J c (fun j => bw F s (w j)) (c₀ s) (hc₀ s)
      (hS.tok s).1 (hS.tok s).2 (fun j => bw_ok F hS s (w j))
    refine ⟨‖cc s‖ * C, N, fun k hk => ?_⟩
    have adm : ∀ f : Fin k → J, ∀ t, t = BGen.wd (Sum.inr (F.t₁ s) :: (List.ofFn fun i => bw F s (w (f i))).flatten) (F.t₂ s) →
        D4.IsTest2J (trM t.Φ (MM F s)) (c₀ s * (1 + t.T) + t.r) := by
      intro f t ht
      have hne : (List.ofFn fun i => w (f i)) ≠ [] := by
        rw [Ne, List.ofFn_eq_nil_iff]; omega
      have e := (hid _ hne).1 s
      unfold tw at e
      rw [map_ofFn'] at e
      subst ht
      exact e
    have hb := hC k adm
    have hsum : ∑ j, c j • ((bw F s (w j)).map BGen.op).prod =
        (F.β s).op ^ F.m * ∑ j, c j • wdVal (fun x => (F.g x s).op) (w j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm, bw_prod, b_word F hS s (w j)]
    rw [hsum] at hb
    calc ‖cc s * _‖ = ‖cc s‖ * ‖_‖ := norm_mul _ _
      _ ≤ ‖cc s‖ * (C * (1 + k) ^ N * ‖((F.β s).op ^ F.m * ∑ j, c j • wdVal (fun x => (F.g x s).op) (w j)) ^ k‖) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = ‖cc s‖ * C * (1 + k) ^ N * ‖((F.β s).op ^ F.m * ∑ j, c j • wdVal (fun x => (F.g x s).op) (w j)) ^ k‖ := by
          ring

end Frame

end PTop

/- English proof (translation)
Introduce `hR hD E _ _ _ hE n hn π hπ S T F₀ F hS`. Use `FBL.nontrivInf E hE` as an intermediate fact. Establish `hw` using `h hR E hE n hn π S T F₀ F hS`. Use `show GBound _ _ _ _ _`. Conclude with `PTop.gBound_words _ _ _ _ _ (fun x => (F.toGenIn hD hS).ucomm x) (fun J _ c w => PTop.hW_frame F hE hS hw J c w)`.
-/
theorem frameBound_of (h : WordId) : FrameBound := by
  intro hR hD E _ _ _ hE n hn π hπ S T F₀ F hS
  have := FBL.nontrivInf E hE
  have hw := h hR E hE n hn π S T F₀ F hS
  show GBound _ _ _ _ _
  exact PTop.gBound_words _ _ _ _ _ (fun x => (F.toGenIn hD hS).ucomm x)
    (fun J _ c w => PTop.hW_frame F hE hS hw J c w)

end PositivityTheory.Rg.BcB.F.B3

end
