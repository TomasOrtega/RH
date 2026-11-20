import Formalism.HermitianCurvature.StatementM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstEmbeddingOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MultiplicationOpHom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelNablaStarRelations
import Formalism.YangianSpanCharacter.YangianRelationFirst

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt Matrix Finset

namespace Formalism.FourierDecayAlt.P.Mx8

section Abstract

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/- English proof (translation)
Use extensionality with `ik jl`. Simplify using `only [E1, Matrix.of_apply, Matrix.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem kronecker_E1_smul (s : ℂ) (M : M2 A) : E1 (s • M) = s • E1 M := by
  ext ik jl
  simp only [E1, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `ik jl`. Simplify using `only [E2, Matrix.of_apply, Matrix.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem eval_two_smul (s : ℂ) (M : M2 A) : E2 (s • M) = s • E2 M := by
  ext ik jl
  simp only [E2, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> simp

/- English proof (translation)
Use `⟨fun Y hY => ?_, fun Y Y' => ?_, fun Y => ?_, h.q_real⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_smul, hs', h.herm Y hY]`. Use `h.rtt Y Y'` as an intermediate fact. Simplify using `only [kronecker_E1_smul, eval_two_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hs, one_smul]`. Conclude with `this`.

Use `h.det Y` as an intermediate fact. Simplify using `only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hs, one_smul]`. Conclude with `this`.
-/
theorem isStart_smul (QQ : ℂ → M2 A) (q : ℂ → ℂ) (s : ℂ) (hs : s * s = 1) (hs' : star s = s)
    (h : IsStart QQ q) : IsStart (fun Y => s • QQ Y) q := by
  refine ⟨fun Y hY => ?_, fun Y Y' => ?_, fun Y => ?_, h.q_real⟩
  · rw [Matrix.conjTranspose_smul, hs', h.herm Y hY]
  · have := h.rtt Y Y'
    simp only [kronecker_E1_smul, eval_two_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hs, one_smul]
    exact this
  · have := h.det Y
    simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hs, one_smul]
    exact this

def sStar (σ : Site A) : Site A := ⟨star σ.p, -star σ.ci, -star σ.c⟩

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[Ts, Tm, sStar, Matrix.conjTranspose_apply, algebraMap_star_comm]`. Rewrite using `[starRingEnd_apply, ← algebraMap_star_comm, star_star]`.
-/
theorem Ts_conj (σ : Site A) (Y : ℂ) : (Ts σ (star Y))ᴴ = Ts (sStar σ) Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ts, Tm, sStar, Matrix.conjTranspose_apply, algebraMap_star_comm]
  rw [starRingEnd_apply, ← algebraMap_star_comm, star_star]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `key : ci * p = p * ci + ci`. Establish `e` using `congrArg (fun x => ci * x * ci) h3`. Simplify using `only [mul_add, add_mul, ← mul_assoc, h2, one_mul] at e`. Rewrite `e` using `[mul_assoc (ci * p), h1, mul_one]`.

Conclude with `e`. Rewrite using `[key]`. Normalize the expressions using the abelian group laws.
-/
theorem weyl_ci {p c ci : A} (h : WeylRel p c ci) : p * ci = ci * p - ci := by
  obtain ⟨h1, h2, h3⟩ := h
  have key : ci * p = p * ci + ci := by
    have e := congrArg (fun x => ci * x * ci) h3
    simp only [mul_add, add_mul, ← mul_assoc, h2, one_mul] at e
    rw [mul_assoc (ci * p), h1, mul_one] at e
    exact e
  rw [key]; abel

/- English proof (translation)
Establish `key` using `weyl_ci h`. Unfold `WeylRel at h ⊢`. Take `⟨h1, h2, _⟩` from `h`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [sStar, neg_mul_neg, ← star_mul, h1, star_one]`.

Simplify using `only [sStar, neg_mul_neg, ← star_mul, h2, star_one]`. Simplify using `only [sStar, mul_neg, neg_mul, ← star_mul, key, star_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem weyl_star {σ : Site A} (h : WeylRel σ.p σ.c σ.ci) :
    WeylRel (sStar σ).p (sStar σ).c (sStar σ).ci := by
  have key := weyl_ci h
  unfold WeylRel at h ⊢
  obtain ⟨h1, h2, _⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [sStar, neg_mul_neg, ← star_mul, h1, star_one]
  · simp only [sStar, neg_mul_neg, ← star_mul, h2, star_one]
  · simp only [sStar, mul_neg, neg_mul, ← star_mul, key, star_sub]
    abel

/- English proof (translation)
Introduce `Y Y'` and use `Formalism.YangianSpanCharacter.P.rttRelation ℂ A p c ci Y Y' h`.
-/
theorem isRTT_Tm {p c ci : A} (h : WeylRel p c ci) : IsRTT (fun Y : ℂ => Tm Y p c ci) :=
  fun Y Y' => Formalism.YangianSpanCharacter.P.rttRelation ℂ A p c ci Y Y' h

/- English proof (translation)
Introduce `Y`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, one_smul]`. Conclude with `Formalism.YangianSpanCharacter.P.transposeSymplecticShift ℂ A p c ci Y h`. Rewrite using `[map_one, one_smul]`.

Take `⟨h1, h2, h3⟩` from `h`. Establish `hc : algebraMap ℂ A Y * c = c * algebraMap ℂ A Y` using `Algebra.commutes _ _`. Use extensionality with `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Simplify using `[Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add, h3, hc]`.

Normalize the expressions using the abelian group laws. Simplify using `[Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, h1]`. Simplify using `[Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, h2]`. Simplify using `[Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem isDet_Tm {p c ci : A} (h : WeylRel p c ci) : IsDet (fun Y : ℂ => Tm Y p c ci) (fun _ => 1) := by
  intro Y
  refine ⟨?_, ?_⟩
  · rw [map_one, one_smul]
    exact Formalism.YangianSpanCharacter.P.transposeSymplecticShift ℂ A p c ci Y h
  · rw [map_one, one_smul]
    obtain ⟨h1, h2, h3⟩ := h
    have hc : algebraMap ℂ A Y * c = c * algebraMap ℂ A Y := Algebra.commutes _ _
    ext a b
    fin_cases a <;> fin_cases b
    · simp [Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add, h3, hc]
      abel
    · simp [Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, h1]
    · simp [Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, h2]
    · simp [Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Apply the tactic sequence `fin_cases a <;> fin_cases b`. Use `show Commute x (algebraMap ℂ A Y + σ.p)`. Conclude with `Commute.add_right (Algebra.commutes Y x).symm hp`. Use `show Commute x (-σ.c)`. Conclude with `hc.neg_right`.

Use `show Commute x σ.ci`. Conclude with `hci`. Use `show Commute x 0`. Conclude with `Commute.zero_right x`.
-/
theorem Ts_comm (σ : Site A) (x : A) (hp : Commute x σ.p) (hc : Commute x σ.c) (hci : Commute x σ.ci)
    (Y : ℂ) (a b : Fin 2) : Commute x (Ts σ Y a b) := by
  fin_cases a <;> fin_cases b
  · show Commute x (algebraMap ℂ A Y + σ.p)
    exact Commute.add_right (Algebra.commutes Y x).symm hp
  · show Commute x (-σ.c)
    exact hc.neg_right
  · show Commute x σ.ci
    exact hci
  · show Commute x 0
    exact Commute.zero_right x

/- English proof (translation)
Take `⟨hW, hH⟩` from `hσ`. Establish `mp : σ.p ∈ hol σ` using `by simp [hol]`. Establish `mc : σ.c ∈ hol σ` using `by simp [hol]`. Establish `mci : σ.ci ∈ hol σ` using `by simp [hol]`. Establish `c1 : EntriesCommute (fun Y : ℂ => Ts (sStar σ) Y) QQ`.

Introduce `Y Y' i j k l`. Use `(Ts_comm (sStar σ) (QQ Y' k l) ?_ ?_ ?_ Y i j).symm` and prove the remaining obligations. Conclude with `hc Y' k l (star σ.p) (Or.inr (by rw [star_star]; exact mp))`. Conclude with `(hc Y' k l (star σ.ci) (Or.inr (by rw [star_star]; exact mci))).neg_right`. Conclude with `(hc Y' k l (star σ.c) (Or.inr (by rw [star_star]; exact mc))).neg_right`.

Establish `c2 : EntriesCommute QQ (fun Y : ℂ => Ts σ Y)`. Introduce `Y Y' i j k l`. Conclude with `Ts_comm σ (QQ Y i j) (hc Y i j _ (Or.inl mp)) (hc Y i j _ (Or.inl mc)) (hc Y i j _ (Or.inl mci)) Y' k l`. Establish `c3 : EntriesCommute (fun Y : ℂ => Ts (sStar σ) Y) (fun Y : ℂ => Ts σ Y)`. Introduce `Y Y' i j k l`.

Establish `key : ∀ x ∈ hol σ, Commute (Ts (sStar σ) Y i j) x` using `fun x hx => (Ts_comm (sStar σ) x (hH x hx _ mp) (hH x hx _ mci).neg_right (hH x hx _ mc).neg_right Y i j).symm`. Conclude with `Ts_comm σ _ (key _ mp) (key _ mc) (key _ mci) Y' k l`. Establish `hF` using `Formalism.FourierDecayAlt.P.W.wordFusion_list (R := ℂ) (B := A) [(fun Y : ℂ => Ts (sStar σ) Y, fun _ => 1), (QQ, q), (fun Y : ℂ => Ts σ Y, fun _ => 1)] (by`. Introduce `x hx`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hx`.

Break down `hx with rfl | rfl | rfl` into its components or cases. Conclude with `⟨isRTT_Tm (weyl_star hW), isDet_Tm (weyl_star hW)⟩`. Conclude with `⟨h.rtt, h.det⟩`. Conclude with `⟨isRTT_Tm hW, isDet_Tm hW⟩)`. Use the proof step `(by`.

Simplify using `only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]`. Conclude with `⟨⟨c1, c3⟩, c2⟩)`. Establish `e1 : (fun Y => (Ts σ (star Y))ᴴ * QQ Y * Ts σ Y) = fun Y => (([(fun Y : ℂ => Ts (sStar σ) Y, fun _ => 1), (QQ, q), (fun Y : ℂ => Ts σ Y, fun _ => 1)] : List ((ℂ → Matrix (Fin 2) (Fin 2) A) × (ℂ → ℂ))).map (fun x => x.1 Y)).prod`. Use function extensionality and compare the values at `Y`. Rewrite using `[Ts_conj]`.

Simplify using `[mul_assoc]`. Establish `e2 : q = fun Y => (([(fun Y : ℂ => Ts (sStar σ) Y, fun _ => 1), (QQ, q), (fun Y : ℂ => Ts σ Y, fun _ => 1)] : List ((ℂ → Matrix (Fin 2) (Fin 2) A) × (ℂ → ℂ))).map (fun x => x.2 Y)).prod`. Use function extensionality and compare the values at `Y`. Simplify using the standard rewrite rules. Use `⟨fun Y hY => ?_, ?_, ?_, h.q_real⟩` and prove the remaining obligations.

Simplify using `only [hY, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h.herm Y hY, mul_assoc]`. Rewrite using `[e1]`. Conclude with `hF.1`. Rewrite using `[e1]`. Use `hF.2` as an intermediate fact.

Rewrite `this` using `[← e2]`. Then use the resulting hypothesis.
-/
theorem isStart_step (σ : Site A) (QQ : ℂ → M2 A) (q : ℂ → ℂ) (hσ : IsSite σ)
    (hc : QQCommutes QQ σ) (h : IsStart QQ q) :
    IsStart (fun Y => (Ts σ (star Y))ᴴ * QQ Y * Ts σ Y) q := by
  obtain ⟨hW, hH⟩ := hσ
  have mp : σ.p ∈ hol σ := by simp [hol]
  have mc : σ.c ∈ hol σ := by simp [hol]
  have mci : σ.ci ∈ hol σ := by simp [hol]
  have c1 : EntriesCommute (fun Y : ℂ => Ts (sStar σ) Y) QQ := by
    intro Y Y' i j k l
    refine (Ts_comm (sStar σ) (QQ Y' k l) ?_ ?_ ?_ Y i j).symm
    · exact hc Y' k l (star σ.p) (Or.inr (by rw [star_star]; exact mp))
    · exact (hc Y' k l (star σ.ci) (Or.inr (by rw [star_star]; exact mci))).neg_right
    · exact (hc Y' k l (star σ.c) (Or.inr (by rw [star_star]; exact mc))).neg_right
  have c2 : EntriesCommute QQ (fun Y : ℂ => Ts σ Y) := by
    intro Y Y' i j k l
    exact Ts_comm σ (QQ Y i j) (hc Y i j _ (Or.inl mp)) (hc Y i j _ (Or.inl mc)) (hc Y i j _ (Or.inl mci)) Y' k l
  have c3 : EntriesCommute (fun Y : ℂ => Ts (sStar σ) Y) (fun Y : ℂ => Ts σ Y) := by
    intro Y Y' i j k l
    have key : ∀ x ∈ hol σ, Commute (Ts (sStar σ) Y i j) x := fun x hx =>
      (Ts_comm (sStar σ) x (hH x hx _ mp) (hH x hx _ mci).neg_right (hH x hx _ mc).neg_right Y i j).symm
    exact Ts_comm σ _ (key _ mp) (key _ mc) (key _ mci) Y' k l
  have hF := Formalism.FourierDecayAlt.P.W.wordFusion_list (R := ℂ) (B := A)
    [(fun Y : ℂ => Ts (sStar σ) Y, fun _ => 1), (QQ, q), (fun Y : ℂ => Ts σ Y, fun _ => 1)]
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨isRTT_Tm (weyl_star hW), isDet_Tm (weyl_star hW)⟩
      · exact ⟨h.rtt, h.det⟩
      · exact ⟨isRTT_Tm hW, isDet_Tm hW⟩)
    (by
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
      exact ⟨⟨c1, c3⟩, c2⟩)
  have e1 : (fun Y => (Ts σ (star Y))ᴴ * QQ Y * Ts σ Y) = fun Y =>
      (([(fun Y : ℂ => Ts (sStar σ) Y, fun _ => 1), (QQ, q), (fun Y : ℂ => Ts σ Y, fun _ => 1)] :
        List ((ℂ → Matrix (Fin 2) (Fin 2) A) × (ℂ → ℂ))).map (fun x => x.1 Y)).prod := by
    funext Y
    rw [Ts_conj]
    simp [mul_assoc]
  have e2 : q = fun Y =>
      (([(fun Y : ℂ => Ts (sStar σ) Y, fun _ => 1), (QQ, q), (fun Y : ℂ => Ts σ Y, fun _ => 1)] :
        List ((ℂ → Matrix (Fin 2) (Fin 2) A) × (ℂ → ℂ))).map (fun x => x.2 Y)).prod := by
    funext Y
    simp
  refine ⟨fun Y hY => ?_, ?_, ?_, h.q_real⟩
  · simp only [hY, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h.herm Y hY, mul_assoc]
  · rw [e1]; exact hF.1
  · rw [e1]
    have := hF.2
    rwa [← e2] at this

end Abstract

section Lev

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

def G (l : Fin r) : Set A := {L.p l, L.c l, L.ci l, -L.pb l, L.cb l, L.cbi l}

/- English proof (translation)
Establish `h'` using `h.symm`. Establish `pc : ∀ a b : Fin r, a ≠ b → Commute (L.p a) (L.c b)` using `fun a b hab => by`. Use `L.p_c a b` as an intermediate fact. Rewrite `this` using `[if_neg hab, add_zero]`. Then use the resulting hypothesis. Establish `pci : ∀ a b : Fin r, a ≠ b → Commute (L.p a) (L.ci b)` using `fun a b hab => by`.

Use `L.p_ci a b` as an intermediate fact. Rewrite `this` using `[if_neg hab, sub_zero]`. Then use the resulting hypothesis. Establish `pbcb : ∀ a b : Fin r, a ≠ b → Commute (L.pb a) (L.cb b)` using `fun a b hab => by`. Use `L.pb_cb a b` as an intermediate fact. Rewrite `this` using `[if_neg hab, add_zero]`. Then use the resulting hypothesis.

Establish `pbcbi : ∀ a b : Fin r, a ≠ b → Commute (L.pb a) (L.cbi b)` using `fun a b hab => by`. Use `L.pb_cbi a b` as an intermediate fact. Rewrite `this` using `[if_neg hab, sub_zero]`. Then use the resulting hypothesis. Introduce `x hx y hy`. Simplify using `only [G, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy`.

Apply the tactic sequence `rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>`. Apply the tactic sequence `rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>`. Apply the tactic sequence `(try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;>`. Use `first`. Consider the case `exact L.p_p _ _ | exact L.p_pb _ _ | exact (L.p_pb _ _).symm | exact L.pb_pb _ _`.

Consider the case `exact pc _ _ h | exact (pc _ _ h').symm | exact pci _ _ h | exact (pci _ _ h').symm`. Consider the case `exact pbcb _ _ h | exact (pbcb _ _ h').symm | exact pbcbi _ _ h | exact (pbcbi _ _ h').symm`. Consider the case `exact L.p_cb _ _ | exact (L.p_cb _ _).symm | exact L.p_cbi _ _ | exact (L.p_cbi _ _).symm`. Consider the case `exact L.pb_c _ _ | exact (L.pb_c _ _).symm | exact L.pb_ci _ _ | exact (L.pb_ci _ _).symm`. Consider the case `exact L.fns_comm _ (by simp) _ (by simp)`.
-/
theorem G_comm_ne (l m : Fin r) (h : l ≠ m) : ∀ x ∈ G L l, ∀ y ∈ G L m, Commute x y := by
  have h' := h.symm
  have pc : ∀ a b : Fin r, a ≠ b → Commute (L.p a) (L.c b) := fun a b hab => by
    have := L.p_c a b; rwa [if_neg hab, add_zero] at this
  have pci : ∀ a b : Fin r, a ≠ b → Commute (L.p a) (L.ci b) := fun a b hab => by
    have := L.p_ci a b; rwa [if_neg hab, sub_zero] at this
  have pbcb : ∀ a b : Fin r, a ≠ b → Commute (L.pb a) (L.cb b) := fun a b hab => by
    have := L.pb_cb a b; rwa [if_neg hab, add_zero] at this
  have pbcbi : ∀ a b : Fin r, a ≠ b → Commute (L.pb a) (L.cbi b) := fun a b hab => by
    have := L.pb_cbi a b; rwa [if_neg hab, sub_zero] at this
  intro x hx y hy
  simp only [G, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;>
    first
    | exact L.p_p _ _ | exact L.p_pb _ _ | exact (L.p_pb _ _).symm | exact L.pb_pb _ _
    | exact pc _ _ h | exact (pc _ _ h').symm | exact pci _ _ h | exact (pci _ _ h').symm
    | exact pbcb _ _ h | exact (pbcb _ _ h').symm | exact pbcbi _ _ h | exact (pbcbi _ _ h').symm
    | exact L.p_cb _ _ | exact (L.p_cb _ _).symm | exact L.p_cbi _ _ | exact (L.p_cbi _ _).symm
    | exact L.pb_c _ _ | exact (L.pb_c _ _).symm | exact L.pb_ci _ _ | exact (L.pb_ci _ _).symm
    | exact L.fns_comm _ (by simp) _ (by simp)

/- English proof (translation)
Introduce `x hx y hy`. Simplify using `only [G, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy`. Apply the tactic sequence `rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>`. Apply the tactic sequence `rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>`. Apply the tactic sequence `(try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;>`.

Use `first`. Consider the case `exact L.p_ζ _ | exact L.p_ζb _ | exact L.p_GG _ | exact L.p_GGi _ | exact L.p_nab _ | exact L.p_nabs _`. Consider the case `exact L.pb_ζ _ | exact L.pb_ζb _ | exact L.pb_GG _ | exact L.pb_GGi _ | exact L.pb_nab _`. Consider the case `exact L.pb_nabs _`. Consider the case `exact (L.nab_c _).symm | exact (L.nab_ci _).symm | exact (L.nab_cb _).symm | exact (L.nab_cbi _).symm`.

Consider the case `exact (L.nabs_c _).symm | exact (L.nabs_ci _).symm | exact (L.nabs_cb _).symm`. Consider the case `exact (L.nabs_cbi _).symm`. Consider the case `exact L.fns_comm _ (by simp) _ (by simp)`.
-/
theorem gamma_family_commute_generators (l : Fin r) : ∀ x ∈ G L l,
    ∀ y ∈ ({L.ζ, L.ζb, L.GG, L.GGi, L.nab, L.nabs} : Set A), Commute x y := by
  intro x hx y hy
  simp only [G, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;>
    first
    | exact L.p_ζ _ | exact L.p_ζb _ | exact L.p_GG _ | exact L.p_GGi _ | exact L.p_nab _ | exact L.p_nabs _
    | exact L.pb_ζ _ | exact L.pb_ζb _ | exact L.pb_GG _ | exact L.pb_GGi _ | exact L.pb_nab _
    | exact L.pb_nabs _
    | exact (L.nab_c _).symm | exact (L.nab_ci _).symm | exact (L.nab_cb _).symm | exact (L.nab_cbi _).symm
    | exact (L.nabs_c _).symm | exact (L.nabs_ci _).symm | exact (L.nabs_cb _).symm
    | exact (L.nabs_cbi _).symm
    | exact L.fns_comm _ (by simp) _ (by simp)

/- English proof (translation)
Introduce `x hx y hy`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy`. Apply the tactic sequence `rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> (try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;> first`. Consider the case `exact L.p_pb _ _ | exact L.p_cb _ _ | exact L.p_cbi _ _`. Consider the case `exact (L.pb_c _ _).symm | exact (L.pb_ci _ _).symm`.

Consider the case `exact L.fns_comm _ (by simp) _ (by simp)`.
-/
theorem hol_comm (l : Fin r) : ∀ x ∈ ({L.p l, L.c l, L.ci l} : Set A),
    ∀ y ∈ ({-L.pb l, L.cb l, L.cbi l} : Set A), Commute x y := by
  intro x hx y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    (try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;>
    first
    | exact L.p_pb _ _ | exact L.p_cb _ _ | exact L.p_cbi _ _
    | exact (L.pb_c _ _).symm | exact (L.pb_ci _ _).symm
    | exact L.fns_comm _ (by simp) _ (by simp)

/- English proof (translation)
Establish `c1 : L.GGi * L.ζ = L.ζ * L.GGi` using `L.fns_comm _ (by simp) _ (by simp)`. Establish `c3 : L.ζb * L.GGi = L.GGi * L.ζb` using `L.fns_comm _ (by simp) _ (by simp)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = L.ζb * ((L.ζi * L.ζ) * L.GGi) * L.ζbi := by rw [c1]; simp only [mul_assoc]`.

Use `_ = L.GGi * (L.ζb * L.ζbi) := by rw [L.ζi_ζ, one_mul, c3, mul_assoc]`. Use `_ = L.GGi := by rw [L.ζb_ζbi, mul_one]`.
-/
theorem fn_cancel : L.ζb * L.ζi * L.GGi * (L.ζ * L.ζbi) = L.GGi := by
  have c1 : L.GGi * L.ζ = L.ζ * L.GGi := L.fns_comm _ (by simp) _ (by simp)
  have c3 : L.ζb * L.GGi = L.GGi * L.ζb := L.fns_comm _ (by simp) _ (by simp)
  calc L.ζb * L.ζi * L.GGi * (L.ζ * L.ζbi) = L.ζb * (L.ζi * (L.GGi * L.ζ)) * L.ζbi := by
        simp only [mul_assoc]
    _ = L.ζb * ((L.ζi * L.ζ) * L.GGi) * L.ζbi := by rw [c1]; simp only [mul_assoc]
    _ = L.GGi * (L.ζb * L.ζbi) := by rw [L.ζi_ζ, one_mul, c3, mul_assoc]
    _ = L.GGi := by rw [L.ζb_ζbi, mul_one]

end Lev

/- English proof (translation)
Simplify using `only [sgn, ← mul_pow, neg_one_mul, neg_neg, one_pow]`.
-/
theorem sgn_sq (P : Par) (l : ℕ) : sgn P l * sgn P l = 1 := by
  simp only [sgn, ← mul_pow, neg_one_mul, neg_neg, one_pow]

/- English proof (translation)
Simplify using `[sgn]`.
-/
theorem sgn_star (P : Par) (l : ℕ) : star (sgn P l) = sgn P l := by
  simp [sgn]

/- English proof (translation)
Establish `hY' : (starRingEnd ℂ) Y = Y` using `hY`. Establish `h2 : (starRingEnd ℂ) (2 : ℂ) = 2` using `map_ofNat _ 2`. Use `show (starRingEnd ℂ) (qC P Y) = qC P Y`. Simplify using `[qC, map_prod, hY', h2]`.
-/
theorem qC_real (P : Par) (Y : ℂ) (hY : star Y = Y) : star (qC P Y) = qC P Y := by
  have hY' : (starRingEnd ℂ) Y = Y := hY
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  show (starRingEnd ℂ) (qC P Y) = qC P Y
  simp [qC, map_prod, hY', h2]

/- English proof (translation)
Establish `hY' : (starRingEnd ℂ) Y = Y` using `hY`. Use `show (starRingEnd ℂ) (x0 P l π Y) = x0 P l π Y`. Simplify using `[x0, map_prod, hY']`.
-/
theorem coordinate_real (P : Par) (l : ℕ) (π : Ty P) (Y : ℂ) (hY : star Y = Y) :
    star (x0 P l π Y) = x0 P l π Y := by
  have hY' : (starRingEnd ℂ) Y = Y := hY
  show (starRingEnd ℂ) (x0 P l π Y) = x0 P l π Y
  simp [x0, map_prod, hY']

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kap_eq (P : Par) (f : Ty P → ℂ) :
    kap P f = Matrix.diagonal fun π => algebraMap ℂ (Pr P.r) (f π) := rfl

/- English proof (translation)
Rewrite using `[kap_eq]`. Simplify using `only [Commute, SemiconjBy, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Conclude with `Algebra.commutes _ _`.
-/
theorem kap_comm_diag (P : Par) (f : Ty P → ℂ) (d : Ty P → Pr P.r) :
    Commute (kap P f) (Matrix.diagonal d) := by
  rw [kap_eq]
  simp only [Commute, SemiconjBy, Matrix.diagonal_mul_diagonal]
  congr 1
  funext π
  exact Algebra.commutes _ _

/- English proof (translation)
The claim follows from `kap_comm_diag P f _`.
-/
theorem kap_comm_sc (P : Par) (f : Ty P → ℂ) (w : Pr P.r) : Commute (kap P f) (sc P w) :=
  kap_comm_diag P f _

/- English proof (translation)
Conclude with `(Commute.all f g).map (kap P)`.
-/
theorem kap_comm_kap (P : Par) (f g : Ty P → ℂ) : Commute (kap P f) (kap P g) := by
  exact (Commute.all f g).map (kap P)

/- English proof (translation)
Rewrite using `[kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Simplify using `[algebraMap_star_comm]`. Rewrite using `[starRingEnd_apply, algebraMap_star_comm]`.
-/
theorem star_kap (P : Par) (f : Ty P → ℂ) : star (kap P f) = kap P (star f) := by
  rw [kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext π
  simp [algebraMap_star_comm]
  rw [starRingEnd_apply, algebraMap_star_comm]

/- English proof (translation)
Establish `h : (fun π => x0 P l π Y) = sgn P l • (fun π => xC P π Y)`. Use extensionality with `π`. Simplify using `[x0, sgn, xC]`. Rewrite using `[h, map_smul]`. Both sides reduce to the same expression.
-/
theorem kappa_sign_coordinate (P : Par) (l : ℕ) (Y : ℂ) : (kap P fun π => x0 P l π Y) = sgn P l • xA P Y := by
  have h : (fun π => x0 P l π Y) = sgn P l • (fun π => xC P π Y) := by
    ext π; simp [x0, sgn, xC]
  rw [h, map_smul]; rfl

/- English proof (translation)
Introduce `P l w`. Use `show SS P l * sc P w = sc P w * SS P l`. Use extensionality with `π' π`. Simplify using `only [sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, SS, Matrix.of_apply]`. Use `split_ifs`.

Conclude with `(Algebra.commutes _ _)`. Simplify using the standard rewrite rules.
-/
theorem ssScalar : SSScalar := by
  intro P l w
  show SS P l * sc P w = sc P w * SS P l
  ext π' π
  simp only [sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, SS, Matrix.of_apply]
  split_ifs
  · exact (Algebra.commutes _ _)
  · simp

/- English proof (translation)
Rewrite using `[Finset.mul_sum, weightedSumBis]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, xA, ← map_mul]`. Use `hSh P j _ _ fun π π' hU => ?_` and prove the remaining obligations. Establish `hsub : ({j} : Finset ℕ) ⊆ Icc 1 (P.k - 1)` using `Finset.singleton_subset_iff.2 hj`.

Establish `h1 : xC P π' Y = xEx P {j} π' Y * (Y + (rho P π' j : ℂ))`. Rewrite using `[xC, xEx, ← Finset.prod_sdiff hsub, Finset.prod_singleton]`. Establish `h2 : Y + (rho P π' j : ℂ) ≠ 0` using `fun h0 => hY π' (by rw [h1, h0, mul_zero])`. Establish `h3 : xEx P {j} π' Y = xEx P {j} π Y`. Unfold `xEx`.

Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_sdiff, Finset.mem_singleton]`. Rewrite using `[hRho P j π π' hU i hi.1, if_neg hi.2, add_zero]`. Use `show xC P π' Y * (Y + (rho P π' j : ℂ))⁻¹ = xEx P {j} π Y`. Rewrite using `[h1, mul_assoc, mul_inv_cancel₀ h2, mul_one, h3]`.
-/
theorem low_sum (hSh : SSShift) (hRho : RhoUp) (P : Par) (Y : ℂ) (hY : ∀ π, xC P π Y ≠ 0) :
    xA P Y * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j = weightedSumBis P Y := by
  rw [Finset.mul_sum, weightedSumBis]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← mul_assoc, xA, ← map_mul]
  refine hSh P j _ _ fun π π' hU => ?_
  have hsub : ({j} : Finset ℕ) ⊆ Icc 1 (P.k - 1) := Finset.singleton_subset_iff.2 hj
  have h1 : xC P π' Y = xEx P {j} π' Y * (Y + (rho P π' j : ℂ)) := by
    rw [xC, xEx, ← Finset.prod_sdiff hsub, Finset.prod_singleton]
  have h2 : Y + (rho P π' j : ℂ) ≠ 0 := fun h0 => hY π' (by rw [h1, h0, mul_zero])
  have h3 : xEx P {j} π' Y = xEx P {j} π Y := by
    unfold xEx
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    rw [hRho P j π π' hU i hi.1, if_neg hi.2, add_zero]
  show xC P π' Y * (Y + (rho P π' j : ℂ))⁻¹ = xEx P {j} π Y
  rw [h1, mul_assoc, mul_inv_cancel₀ h2, mul_one, h3]

/- English proof (translation)
Introduce `P hP l L hL`. Take `⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hgg, hggi, hnab, hnabs, hTT⟩` from `hL`. Establish `hzf : ∀ g ∈ zfns L, ∃ w, g = sc P w`. Introduce `g hg`. Simplify using `only [zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg`.

Break down `hg with rfl | rfl | rfl | rfl | rfl | rfl` into its components or cases. Conclude with `⟨zP, hz⟩`. Conclude with `⟨ziP, hzi⟩`. Conclude with `⟨zbP, hzb⟩`. Conclude with `⟨zbiP, hzbi⟩`.

Conclude with `⟨ggP P.TT, hgg⟩`. Conclude with `⟨ggiP P.TT, hggi⟩`. Use `⟨hS P hP l, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `Y Y' show Commute (sgn P l • t21 P Y) (sgn P l • t21 P Y')`. Conclude with `((hT P hP Y Y').smul_left _).smul_right _`.

Introduce `Y hY`. Establish `hne : ∀ π, x0 P l π Y ≠ 0` using `fun π => mul_ne_zero (pow_ne_zero _ (by norm_num)) (hY π)`. Establish `h1 : ((fun π => x0 P l π Y) * fun π => (x0 P l π Y)⁻¹) = (1 : Ty P → ℂ)`. Use function extensionality and compare the values at `π`. Conclude with `mul_inv_cancel₀ (hne π)`.

Establish `h2 : ((fun π => (x0 P l π Y)⁻¹) * fun π => x0 P l π Y) = (1 : Ty P → ℂ)`. Use function extensionality and compare the values at `π`. Conclude with `inv_mul_cancel₀ (hne π)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (kap P fun π => x0 P l π Y) * (kap P fun π => (x0 P l π Y)⁻¹) = 1`.

Rewrite using `[← map_mul, h1, map_one]`. Use `show (kap P fun π => (x0 P l π Y)⁻¹) * (kap P fun π => x0 P l π Y) = 1`. Rewrite using `[← map_mul, h2, map_one]`. Introduce `Y Y'`. Conclude with `kap_comm_kap P _ _`.

Introduce `Y g hg`. Take `⟨w, rfl⟩` from `hzf g hg`. Conclude with `kap_comm_sc P _ w`. Introduce `Y`. Rewrite using `[hnab]`.

Conclude with `kap_comm_diag P _ _`. Introduce `Y hY show star (kap P fun π => x0 P l π Y) = kap P fun π => x0 P l π Y`. Rewrite using `[star_kap]`. Use `congr 1`. Use function extensionality and compare the values at `π`.

Conclude with `coordinate_real P l π Y hY`. Introduce `Y g hg`. Establish `h1 : Commute (zA P) g`. Rewrite using `[← hz]; exact L.fns_comm _ (Or.inr (by simp)) g (Or.inr hg)`. Establish `h2 : Commute (zbiA P) g`.

Rewrite using `[← hzbi]; exact L.fns_comm _ (Or.inr (by simp)) g (Or.inr hg)`. Establish `h3 : Commute (∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j) g`. Take `⟨w, hw⟩` from `hzf g hg`. Rewrite using `[hw]`. Conclude with `Commute.sum_left _ _ _ fun j _ => (kap_comm_sc P _ w).mul_left (hSc P j w)`.

Conclude with `(h1.mul_left h2).mul_left h3`. Introduce `Y show sgn P l • (ggA P * xA P Y) = L.GG * kap P (fun π => x0 P l π Y)`. Rewrite using `[kappa_sign_coordinate, mul_smul_comm, hgg]`. Introduce `Y hY`. Establish `hl0 : L.l0 Y = l0A P Y` using `by simp only [LevelData.l0, l0A, hnab, hzb, hggi]`.

Establish `hcan` using `fn_cancel L`. Establish `hgi` using `L.GG_GGi`. Rewrite `hcan` using `[hzb, hzi, hggi, hz, hzbi]`. Rewrite `hgi` using `[hgg, hggi]`. Establish `hcx : ggA P * xA P Y = xA P Y * ggA P` using `(kap_comm_sc P _ _).eq.symm`.

Use `show sgn P l • (ggA P * xA P Y * l0A P Y + weightedSumBis P Y) = L.GG * (kap P fun π => x0 P l π Y) * (L.l0 Y + L.ζb * L.ζi * L.GGi * eeA P Y)`. Rewrite using `[hl0, kappa_sign_coordinate, hgg, hzb, hzi, hggi, ← low_sum hSh hRho P Y hY, eeA, ← mul_assoc _ (zA P * zbiA P), hcan, mul_smul_comm, smul_mul_assoc, mul_add]`. Use `congr 2`. Rewrite using `[hcx, mul_assoc, ← mul_assoc (ggA P), hgi, one_mul]`.
-/
theorem startOK_of (hS : StartIsStart) (hT : T21Commute) (hSc : SSScalar) (hSh : SSShift) (hRho : RhoUp) :
    StartOK := by
  intro P hP l L hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hgg, hggi, hnab, hnabs, hTT⟩ := hL
  have hzf : ∀ g ∈ zfns L, ∃ w, g = sc P w := by
    intro g hg
    simp only [zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨zP, hz⟩
    · exact ⟨ziP, hzi⟩
    · exact ⟨zbP, hzb⟩
    · exact ⟨zbiP, hzbi⟩
    · exact ⟨ggP P.TT, hgg⟩
    · exact ⟨ggiP P.TT, hggi⟩
  refine ⟨hS P hP l, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y Y'
    show Commute (sgn P l • t21 P Y) (sgn P l • t21 P Y')
    exact ((hT P hP Y Y').smul_left _).smul_right _
  · intro Y hY
    have hne : ∀ π, x0 P l π Y ≠ 0 := fun π =>
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (hY π)
    have h1 : ((fun π => x0 P l π Y) * fun π => (x0 P l π Y)⁻¹) = (1 : Ty P → ℂ) := by
      funext π; exact mul_inv_cancel₀ (hne π)
    have h2 : ((fun π => (x0 P l π Y)⁻¹) * fun π => x0 P l π Y) = (1 : Ty P → ℂ) := by
      funext π; exact inv_mul_cancel₀ (hne π)
    refine ⟨?_, ?_⟩
    · show (kap P fun π => x0 P l π Y) * (kap P fun π => (x0 P l π Y)⁻¹) = 1
      rw [← map_mul, h1, map_one]
    · show (kap P fun π => (x0 P l π Y)⁻¹) * (kap P fun π => x0 P l π Y) = 1
      rw [← map_mul, h2, map_one]
  · intro Y Y'
    exact kap_comm_kap P _ _
  · intro Y g hg
    obtain ⟨w, rfl⟩ := hzf g hg
    exact kap_comm_sc P _ w
  · intro Y
    rw [hnab]
    exact kap_comm_diag P _ _
  · intro Y hY
    show star (kap P fun π => x0 P l π Y) = kap P fun π => x0 P l π Y
    rw [star_kap]
    congr 1
    funext π
    exact coordinate_real P l π Y hY
  · intro Y g hg
    have h1 : Commute (zA P) g := by
      rw [← hz]; exact L.fns_comm _ (Or.inr (by simp)) g (Or.inr hg)
    have h2 : Commute (zbiA P) g := by
      rw [← hzbi]; exact L.fns_comm _ (Or.inr (by simp)) g (Or.inr hg)
    have h3 : Commute (∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j) g := by
      obtain ⟨w, hw⟩ := hzf g hg
      rw [hw]
      exact Commute.sum_left _ _ _ fun j _ => (kap_comm_sc P _ w).mul_left (hSc P j w)
    exact (h1.mul_left h2).mul_left h3
  · intro Y
    show sgn P l • (ggA P * xA P Y) = L.GG * kap P (fun π => x0 P l π Y)
    rw [kappa_sign_coordinate, mul_smul_comm, hgg]
  · intro Y hY
    have hl0 : L.l0 Y = l0A P Y := by simp only [LevelData.l0, l0A, hnab, hzb, hggi]
    have hcan := fn_cancel L
    have hgi := L.GG_GGi
    rw [hzb, hzi, hggi, hz, hzbi] at hcan
    rw [hgg, hggi] at hgi
    have hcx : ggA P * xA P Y = xA P Y * ggA P := (kap_comm_sc P _ _).eq.symm
    show sgn P l • (ggA P * xA P Y * l0A P Y + weightedSumBis P Y) =
      L.GG * (kap P fun π => x0 P l π Y) * (L.l0 Y + L.ζb * L.ζi * L.GGi * eeA P Y)
    rw [hl0, kappa_sign_coordinate, hgg, hzb, hzi, hggi, ← low_sum hSh hRho P Y hY, eeA, ← mul_assoc _ (zA P * zbiA P), hcan,
      mul_smul_comm, smul_mul_assoc, mul_add]
    congr 2
    rw [hcx, mul_assoc, ← mul_assoc (ggA P), hgi, one_mul]

/- English proof (translation)
Introduce `x hx`. Take `⟨hs, -⟩` from `star_generators P`. Take `⟨h1, h2, h3⟩` from `hs i`. Break down `(hx : x ∈ hol (siteA P i) ∨ star x ∈ hol (siteA P i)) with hx | hx` into its components or cases. Simplify using `only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx`.

Apply the tactic sequence `rcases hx with rfl | rfl | rfl <;> simp`. Simplify using `only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx`. Establish `e : x = star (star x)` using `(star_star x).symm`. Apply the tactic sequence `rcases hx with hx | hx | hx <;> rw [e, hx] <;> simp [h1, h2, h3]`.
-/
theorem ops_sub (P : Par) (i : Fin P.r) : ∀ x ∈ ops (siteA P i),
    x ∈ ({pA P i, cA P i, ciA P i, -pbA P i, cbA P i, cbiA P i} : Set (A P)) := by
  intro x hx
  obtain ⟨hs, -⟩ := star_generators P
  obtain ⟨h1, h2, h3⟩ := hs i
  rcases (hx : x ∈ hol (siteA P i) ∨ star x ∈ hol (siteA P i)) with hx | hx
  · simp only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> simp
  · simp only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have e : x = star (star x) := (star_star x).symm
    rcases hx with hx | hx | hx <;> rw [e, hx] <;> simp [h1, h2, h3]

/- English proof (translation)
Take `⟨hp, hpb, hc, hci, hcb, hcbi, -⟩` from `hL`. Introduce `x hx`. Use `ops_sub P i x hx` as an intermediate fact. Simplify `this` using `only [G, hp, hpb, hc, hci, hcb, hcbi]`.
-/
theorem ops_G (P : Par) (L : LevelData (A P) P.r) (hL : IsModelLevel P L) (i : Fin P.r) :
    ∀ x ∈ ops (siteA P i), x ∈ G L i := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  intro x hx
  have := ops_sub P i x hx
  simpa only [G, hp, hpb, hc, hci, hcb, hcbi] using this

/- English proof (translation)
Introduce `x hx`. Use `ops_sub P i x hx` as an intermediate fact. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at this`. Break down `this with rfl | rfl | rfl | rfl | rfl | rfl` into its components or cases. Conclude with `⟨pP i, rfl⟩`.

Conclude with `⟨cP i, rfl⟩`. Conclude with `⟨ciP i, rfl⟩`. Use `⟨-pbP i, ?_⟩` and prove the remaining obligations. Unfold `pbA sc`. Rewrite using `[map_neg]`.

Conclude with `⟨cbP i, rfl⟩`. Conclude with `⟨cbiP i, rfl⟩`.
-/
theorem ops_sc (P : Par) (i : Fin P.r) : ∀ x ∈ ops (siteA P i), ∃ w, x = sc P w := by
  intro x hx
  have := ops_sub P i x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pP i, rfl⟩
  · exact ⟨cP i, rfl⟩
  · exact ⟨ciP i, rfl⟩
  · refine ⟨-pbP i, ?_⟩
    unfold pbA sc
    rw [map_neg]
  · exact ⟨cbP i, rfl⟩
  · exact ⟨cbiP i, rfl⟩

/- English proof (translation)
Introduce `x hx`. Simplify using `only [ops, Set.mem_setOf_eq, star_star] at hx ⊢`. Conclude with `hx.symm`.
-/
theorem star_ops {A : Type} [Ring A] [StarRing A] (σ : Site A) : ∀ x ∈ ops σ, star x ∈ ops σ := by
  intro x hx
  simp only [ops, Set.mem_setOf_eq, star_star] at hx ⊢
  exact hx.symm

/- English proof (translation)
Take `⟨L, hL⟩` from `Mx2.levelExists P`. Take `⟨hs, -⟩` from `star_generators P`. Take `⟨h1, h2, h3⟩` from `hs i`. Take `⟨hp, hpb, hc, hci, hcb, hcbi, -⟩` from `hL`. Use `⟨⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `L.c_ci i` as an intermediate fact. Rewrite `this` using `[hc, hci]`. Then use the resulting hypothesis. Use `L.ci_c i` as an intermediate fact. Rewrite `this` using `[hc, hci]`. Then use the resulting hypothesis. Use `L.p_c i i` as an intermediate fact.

Rewrite `this` using `[if_pos rfl, hp, hc]`. Then use the resulting hypothesis. Establish `key` using `hol_comm L i`. Rewrite `key` using `[hp, hpb, hc, hci, hcb, hcbi]`. Introduce `x hx y hy`. Use `key x hx (star y) ?_` and prove the remaining obligations.

Simplify using `only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hy`. Apply the tactic sequence `rcases hy with rfl | rfl | rfl <;> simp [h1, h2, h3]`.
-/
theorem isSiteA (P : Par) (i : Fin P.r) : IsSite (siteA P i) := by
  obtain ⟨L, hL⟩ := Mx2.levelExists P
  obtain ⟨hs, -⟩ := star_generators P
  obtain ⟨h1, h2, h3⟩ := hs i
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have := L.c_ci i; rwa [hc, hci] at this
  · have := L.ci_c i; rwa [hc, hci] at this
  · have := L.p_c i i; rwa [if_pos rfl, hp, hc] at this
  · have key := hol_comm L i
    rw [hp, hpb, hc, hci, hcb, hcbi] at key
    intro x hx y hy
    refine key x hx (star y) ?_
    simp only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> simp [h1, h2, h3]

/- English proof (translation)
Take `⟨L, hL⟩` from `Mx2.levelExists P`. Conclude with `fun x hx y hy => G_comm_ne L i j h x (ops_G P L hL i x hx) y (ops_G P L hL j y hy)`.
-/
theorem sitesCommuteA (P : Par) (i j : Fin P.r) (h : i ≠ j) : SitesCommute (siteA P i) (siteA P j) := by
  obtain ⟨L, hL⟩ := Mx2.levelExists P
  exact fun x hx y hy => G_comm_ne L i j h x (ops_G P L hL i x hx) y (ops_G P L hL j y hy)

noncomputable def Cen (P : Par) (i : Fin P.r) : Subalgebra ℂ (A P) := Subalgebra.centralizer ℂ (ops (siteA P i))

/- English proof (translation)
Conclude with `Subalgebra.mem_centralizer_iff (R := ℂ)`.
-/
theorem mem_Cen {P : Par} {i : Fin P.r} {z : A P} :
    z ∈ Cen P i ↔ ∀ g ∈ ops (siteA P i), Commute g z := by
  exact Subalgebra.mem_centralizer_iff (R := ℂ)

/- English proof (translation)
Rewrite `h`, the goal using `[mem_Cen]`. Introduce `g hg`. Use `(h (star g) (star_ops _ g hg)).star_star` as an intermediate fact. Rewrite `this` using `[star_star]`. Then use the resulting hypothesis.
-/
theorem star_mem_Cen {P : Par} {i : Fin P.r} {z : A P} (h : z ∈ Cen P i) : star z ∈ Cen P i := by
  rw [mem_Cen] at h ⊢
  intro g hg
  have := (h (star g) (star_ops _ g hg)).star_star
  rwa [star_star] at this

/- English proof (translation)
Rewrite using `[mem_Cen]`. Introduce `g hg`. Take `⟨w, rfl⟩` from `ops_sc P i g hg`. Conclude with `(kap_comm_sc P f w).symm`.
-/
theorem kap_mem (P : Par) (i : Fin P.r) (f : Ty P → ℂ) : kap P f ∈ Cen P i := by
  rw [mem_Cen]
  intro g hg
  obtain ⟨w, rfl⟩ := ops_sc P i g hg
  exact (kap_comm_sc P f w).symm

/- English proof (translation)
Rewrite using `[mem_Cen]`. Introduce `g hg`. Take `⟨w, rfl⟩` from `ops_sc P i g hg`. Conclude with `(ssScalar P l w).symm`.
-/
theorem SS_mem (P : Par) (i : Fin P.r) (l : ℕ) : SS P l ∈ Cen P i := by
  rw [mem_Cen]
  intro g hg
  obtain ⟨w, rfl⟩ := ops_sc P i g hg
  exact (ssScalar P l w).symm

/- English proof (translation)
Take `⟨L, hL⟩` from `Mx2.levelExists P`. Establish `key` using `gamma_family_commute_generators L i`. Establish `hG` using `ops_G P L hL i`. Take `⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hgg, hggi, hnab, hnabs, hTT⟩` from `hL`. Rewrite `key` using `[hz, hzb, hgg, hggi, hnab, hnabs]`.

Introduce `y hy`. Rewrite using `[mem_Cen]`. Conclude with `fun g hg => key g (hG g hg) y hy`.
-/
theorem z_mem (P : Par) (i : Fin P.r) : ∀ y ∈ ({zA P, zbA P, ggA P, ggiA P, nabA P, nabsA P} : Set (A P)),
    y ∈ Cen P i := by
  obtain ⟨L, hL⟩ := Mx2.levelExists P
  have key := gamma_family_commute_generators L i
  have hG := ops_G P L hL i
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hgg, hggi, hnab, hnabs, hTT⟩ := hL
  rw [hz, hzb, hgg, hggi, hnab, hnabs] at key
  intro y hy
  rw [mem_Cen]
  exact fun g hg => key g (hG g hg) y hy

def Ent {A : Type} [Ring A] [Algebra ℂ A] (C : Subalgebra ℂ A) (M : M2 A) : Prop := ∀ a b, M a b ∈ C

section Ent

variable {A : Type} [Ring A] [Algebra ℂ A] {C : Subalgebra ℂ A}

/- English proof (translation)
Introduce `a b`. Rewrite using `[Matrix.mul_apply]`. Conclude with `sum_mem fun k _ => mul_mem (hM a k) (hN k b)`.
-/
theorem Ent.mul {M N : M2 A} (hM : Ent C M) (hN : Ent C N) : Ent C (M * N) := by
  intro a b
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hM a k) (hN k b)

/- English proof (translation)
Introduce `a b`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem C`. Conclude with `zero_mem C`.
-/
theorem Ent.one : Ent C (1 : M2 A) := by
  intro a b
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem C
  · exact zero_mem C

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rw [List.prod_nil]`. Conclude with `Ent.one`. Consider the case `cons M l ih`. Rewrite using `[List.prod_cons]`.

Conclude with `Ent.mul (h M (by simp)) (ih fun N hN => h N (by simp [hN]))`.
-/
theorem Ent.prod {l : List (M2 A)} (h : ∀ M ∈ l, Ent C M) : Ent C l.prod := by
  induction l with
  | nil => rw [List.prod_nil]; exact Ent.one
  | cons M l ih =>
    rw [List.prod_cons]
    exact Ent.mul (h M (by simp)) (ih fun N hN => h N (by simp [hN]))

/- English proof (translation)
Introduce `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Use `show algebraMap ℂ A Y + σ.p ∈ C`. Conclude with `add_mem (C.algebraMap_mem Y) hp`. Use `show -σ.c ∈ C`.

Conclude with `neg_mem hc`. Use `show σ.ci ∈ C`. Conclude with `hci`. Use `show (0 : A) ∈ C`. Conclude with `zero_mem C`.
-/
theorem Ent.Ts {σ : Site A} (hp : σ.p ∈ C) (hc : σ.c ∈ C) (hci : σ.ci ∈ C) (Y : ℂ) : Ent C (Ts σ Y) := by
  intro a b
  fin_cases a <;> fin_cases b
  · show algebraMap ℂ A Y + σ.p ∈ C
    exact add_mem (C.algebraMap_mem Y) hp
  · show -σ.c ∈ C
    exact neg_mem hc
  · show σ.ci ∈ C
    exact hci
  · show (0 : A) ∈ C
    exact zero_mem C

end Ent

/- English proof (translation)
Establish `hz : zA P ∈ Cen P i` using `z_mem P i _ (by simp)`. Establish `hzb : zbA P ∈ Cen P i` using `z_mem P i _ (by simp)`. Establish `hgg : ggA P ∈ Cen P i` using `z_mem P i _ (by simp)`. Establish `hggi : ggiA P ∈ Cen P i` using `z_mem P i _ (by simp)`. Establish `hnab : nabA P ∈ Cen P i` using `z_mem P i _ (by simp)`.

Establish `hnabs : nabsA P ∈ Cen P i` using `z_mem P i _ (by simp)`. Establish `hk` using `kap_mem P i`. Establish `hS` using `SS_mem P i`. Establish `hSs : ∀ l, star (SS P l) ∈ Cen P i` using `fun l => star_mem_Cen (hS l)`. Establish `hl0 : l0A P Y ∈ Cen P i` using `sub_mem (neg_mem hnab) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hzb hggi))`.

Establish `hm0 : m0A P Y ∈ Cen P i` using `sub_mem (neg_mem hnabs) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hz hggi))`. Establish `hx : xA P Y ∈ Cen P i` using `hk _`. Establish `h21 : weightedSumBis P Y ∈ Cen P i` using `sum_mem fun l _ => mul_mem (hS l) (hk _)`. Establish `h12 : S12 P Y ∈ Cen P i` using `sum_mem fun l _ => mul_mem (hk _) (hSs l)`. Establish `h4 : S4 P Y ∈ Cen P i` using `sum_mem fun l _ => sum_mem fun j _ => mul_mem (mul_mem (hSs l) (hS j)) (hk _)`.

Introduce `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Use `show t11 P Y ∈ Cen P i`. Conclude with `add_mem (add_mem (add_mem (add_mem (mul_mem hggi (hk _)) (mul_mem (mul_mem (mul_mem hgg hx) hm0) hl0)) (mul_mem (mul_mem (mul_mem hgg hm0) hggi) h21)) (mul_mem h12 hl0)) (mul_mem hggi h4)`. Use `show t12 P Y ∈ Cen P i`.

Conclude with `add_mem (mul_mem (mul_mem hgg hx) hm0) h12`. Use `show t21 P Y ∈ Cen P i`. Conclude with `add_mem (mul_mem (mul_mem hgg hx) hl0) h21`. Use `show t22 P Y ∈ Cen P i`. Conclude with `mul_mem hgg hx`.
-/
theorem QQr_ent (P : Par) (i : Fin P.r) (Y : ℂ) : Ent (Cen P i) (QQr P Y) := by
  have hz : zA P ∈ Cen P i := z_mem P i _ (by simp)
  have hzb : zbA P ∈ Cen P i := z_mem P i _ (by simp)
  have hgg : ggA P ∈ Cen P i := z_mem P i _ (by simp)
  have hggi : ggiA P ∈ Cen P i := z_mem P i _ (by simp)
  have hnab : nabA P ∈ Cen P i := z_mem P i _ (by simp)
  have hnabs : nabsA P ∈ Cen P i := z_mem P i _ (by simp)
  have hk := kap_mem P i
  have hS := SS_mem P i
  have hSs : ∀ l, star (SS P l) ∈ Cen P i := fun l => star_mem_Cen (hS l)
  have hl0 : l0A P Y ∈ Cen P i :=
    sub_mem (neg_mem hnab) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hzb hggi))
  have hm0 : m0A P Y ∈ Cen P i :=
    sub_mem (neg_mem hnabs) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hz hggi))
  have hx : xA P Y ∈ Cen P i := hk _
  have h21 : weightedSumBis P Y ∈ Cen P i := sum_mem fun l _ => mul_mem (hS l) (hk _)
  have h12 : S12 P Y ∈ Cen P i := sum_mem fun l _ => mul_mem (hk _) (hSs l)
  have h4 : S4 P Y ∈ Cen P i :=
    sum_mem fun l _ => sum_mem fun j _ => mul_mem (mul_mem (hSs l) (hS j)) (hk _)
  intro a b
  fin_cases a <;> fin_cases b
  · show t11 P Y ∈ Cen P i
    exact add_mem (add_mem (add_mem (add_mem (mul_mem hggi (hk _))
      (mul_mem (mul_mem (mul_mem hgg hx) hm0) hl0)) (mul_mem (mul_mem (mul_mem hgg hm0) hggi) h21))
      (mul_mem h12 hl0)) (mul_mem hggi h4)
  · show t12 P Y ∈ Cen P i
    exact add_mem (mul_mem (mul_mem hgg hx) hm0) h12
  · show t21 P Y ∈ Cen P i
    exact add_mem (mul_mem (mul_mem hgg hx) hl0) h21
  · show t22 P Y ∈ Cen P i
    exact mul_mem hgg hx

/- English proof (translation)
Introduce `a b` and use `(Cen P i).smul_mem (QQr_ent P i Y a b) (sgn P l)`.
-/
theorem start_ent (P : Par) (l : ℕ) (i : Fin P.r) (Y : ℂ) : Ent (Cen P i) ((startM P l).QQ Y) :=
  fun a b => (Cen P i).smul_mem (QQr_ent P i Y a b) (sgn P l)

/- English proof (translation)
Introduce `Y a b x hx`. Conclude with `((mem_Cen.mp (h Y a b)) x hx).symm`.
-/
theorem commutes_of_ent (P : Par) (i : Fin P.r) (QQ : ℂ → M2 (A P)) (h : ∀ Y, Ent (Cen P i) (QQ Y)) :
    QQCommutes QQ (siteA P i) := by
  intro Y a b x hx
  exact ((mem_Cen.mp (h Y a b)) x hx).symm

/- English proof (translation)
Establish `key : ∀ y ∈ hol (siteA P j), y ∈ Cen P i` using `fun y hy => mem_Cen.2 fun g hg => sitesCommuteA P i j h g hg y (Or.inl hy)`. Conclude with `Ent.Ts (key _ (by simp [hol])) (key _ (by simp [hol])) (key _ (by simp [hol])) Y`.
-/
theorem Ts_ent (P : Par) (i j : Fin P.r) (h : i ≠ j) (Y : ℂ) : Ent (Cen P i) (Ts (siteA P j) Y) := by
  have key : ∀ y ∈ hol (siteA P j), y ∈ Cen P i := fun y hy =>
    mem_Cen.2 fun g hg => sitesCommuteA P i j h g hg y (Or.inl hy)
  exact Ent.Ts (key _ (by simp [hol])) (key _ (by simp [hol])) (key _ (by simp [hol])) Y

/- English proof (translation)
Unfold `sitesFrom at h`. Rewrite `h` using `[List.mem_reverse, List.mem_iff_getElem]`. Take `⟨k, hk, rfl⟩` from `h`. Simplify using `only [List.length_drop, List.length_ofFn] at hk`. Use `⟨⟨n + k, by omega⟩, by simp, ?_⟩` and prove the remaining obligations.

Simplify using `[List.getElem_drop, List.getElem_ofFn]`.
-/
theorem mem_sitesFrom (P : Par) (n : ℕ) (σ : Site (A P)) (h : σ ∈ sitesFrom P n) :
    ∃ j : Fin P.r, n ≤ j ∧ σ = siteA P j := by
  unfold sitesFrom at h
  rw [List.mem_reverse, List.mem_iff_getElem] at h
  obtain ⟨k, hk, rfl⟩ := h
  simp only [List.length_drop, List.length_ofFn] at hk
  refine ⟨⟨n + k, by omega⟩, by simp, ?_⟩
  simp [List.getElem_drop, List.getElem_ofFn]

/- English proof (translation)
Establish `hT : ∀ Z : ℂ, Ent (Cen P i) (((sitesFrom P (i + 1)).map fun σ => Ts σ Z).prod)`. Introduce `Z`. Use `Ent.prod fun M hM => ?_` and prove the remaining obligations. Take `⟨σ, hσ, rfl⟩` from `List.mem_map.1 hM`. Take `⟨j, hj, rfl⟩` from `mem_sitesFrom P _ σ hσ`.

Use `Ts_ent P i j ?_ Z` and prove the remaining obligations. Introduce `e`. Rewrite `hj` using `[e]`. Use linear arithmetic over natural numbers and integers. Use `Ent.mul (Ent.mul ?_ (start_ent P l i Y)) (hT Y)` and prove the remaining obligations.

Introduce `a b`. Rewrite using `[Matrix.conjTranspose_apply]`. Conclude with `star_mem_Cen (hT (star Y) b a)`.
-/
theorem QQlev_ent (P : Par) (l : ℕ) (i : Fin P.r) (Y : ℂ) : Ent (Cen P i) (QQlev P l (i + 1) Y) := by
  have hT : ∀ Z : ℂ, Ent (Cen P i) (((sitesFrom P (i + 1)).map fun σ => Ts σ Z).prod) := by
    intro Z
    refine Ent.prod fun M hM => ?_
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hM
    obtain ⟨j, hj, rfl⟩ := mem_sitesFrom P _ σ hσ
    refine Ts_ent P i j ?_ Z
    intro e
    rw [e] at hj
    omega
  refine Ent.mul (Ent.mul ?_ (start_ent P l i Y)) (hT Y)
  intro a b
  rw [Matrix.conjTranspose_apply]
  exact star_mem_Cen (hT (star Y) b a)

/- English proof (translation)
Unfold `sitesFrom`. Rewrite using `[List.drop_eq_getElem_cons (by simp), List.reverse_cons]`. Simplify using `[List.getElem_ofFn]`.
-/
theorem sites_step (P : Par) (i : Fin P.r) : sitesFrom P i = sitesFrom P (i + 1) ++ [siteA P i] := by
  unfold sitesFrom
  rw [List.drop_eq_getElem_cons (by simp), List.reverse_cons]
  simp [List.getElem_ofFn]

/- English proof (translation)
Introduce `P l`. Use `⟨fun Y => ?_, fun i Y => ?_⟩` and prove the remaining obligations. Establish `h : sitesFrom P P.r = []`. Unfold `sitesFrom`. Rewrite using `[List.drop_eq_nil_of_le (by simp)]; rfl`.

Simplify using `[QQlev, h]`. Simplify using `only [QQlev, sites_step P i, List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Matrix.conjTranspose_mul, Matrix.mul_assoc]`.
-/
theorem chainM : ChainM := by
  intro P l
  refine ⟨fun Y => ?_, fun i Y => ?_⟩
  · have h : sitesFrom P P.r = [] := by
      unfold sitesFrom
      rw [List.drop_eq_nil_of_le (by simp)]; rfl
    simp [QQlev, h]
  · simp only [QQlev, sites_step P i, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/- English proof (translation)
Introduce `P l i` and use `commutes_of_ent P i _ (QQlev_ent P l i)`.
-/
theorem lowerCommutes : LowerCommutes :=
  fun P l i => commutes_of_ent P i _ (QQlev_ent P l i)

/- English proof (translation)
Introduce `P hP l`. Establish `key : ∀ d i : ℕ, i + d = P.r → IsStart (QQlev P l i) (qC P)`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`.

Introduce `i hi`. Establish `e : QQlev P l i = (startM P l).QQ`. Use function extensionality and compare the values at `Y`. Rewrite using `[show i = P.r by omega]`. Conclude with `(chainM P l).1 Y`.

Rewrite using `[e]`. Conclude with `h P hP l`. Consider the case `succ d ih`. Introduce `i hi`. Establish `hlt : i < P.r` using `by omega`.

Establish `e : QQlev P l i = fun Y => (Ts (siteA P ⟨i, hlt⟩) (star Y))ᴴ * QQlev P l (i + 1) Y * Ts (siteA P ⟨i, hlt⟩) Y`. Use function extensionality and compare the values at `Y`. Conclude with `(chainM P l).2 ⟨i, hlt⟩ Y`. Rewrite using `[e]`. Conclude with `isStart_step _ _ _ (isSiteA P _) (lowerCommutes P l ⟨i, hlt⟩) (ih (i + 1) (by omega))`.

Introduce `i hi`. Conclude with `key (P.r - i) i (by omega)`.
-/
theorem lowerStart_of (h : StartIsStart) : LowerStart := by
  intro P hP l
  have key : ∀ d i : ℕ, i + d = P.r → IsStart (QQlev P l i) (qC P) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have e : QQlev P l i = (startM P l).QQ := by
        funext Y
        rw [show i = P.r by omega]
        exact (chainM P l).1 Y
      rw [e]
      exact h P hP l
    | succ d ih =>
      intro i hi
      have hlt : i < P.r := by omega
      have e : QQlev P l i = fun Y => (Ts (siteA P ⟨i, hlt⟩) (star Y))ᴴ * QQlev P l (i + 1) Y *
          Ts (siteA P ⟨i, hlt⟩) Y := by
        funext Y
        exact (chainM P l).2 ⟨i, hlt⟩ Y
      rw [e]
      exact isStart_step _ _ _ (isSiteA P _) (lowerCommutes P l ⟨i, hlt⟩) (ih (i + 1) (by omega))
  intro i hi
  exact key (P.r - i) i (by omega)

end Formalism.FourierDecayAlt.P.Mx8

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Introduce `hH hR hD P hP l`. Conclude with `Mx8.isStart_smul (QQr P) (qC P) (sgn P l) (Mx8.sgn_sq P l) (Mx8.sgn_star P l) ⟨fun Y hY => by rw [hH P hP Y, hY], hR P hP, hD P hP, Mx8.qC_real P⟩`.
-/
theorem start_module_assemble : Formalism.FourierDecayAlt.M.StartIsStartAssemble := by
  intro hH hR hD P hP l
  exact Mx8.isStart_smul (QQr P) (qC P) (sgn P l) (Mx8.sgn_sq P l) (Mx8.sgn_star P l)
    ⟨fun Y hY => by rw [hH P hP Y, hY], hR P hP, hD P hP, Mx8.qC_real P⟩

/- English proof (translation)
Conclude with `fun hS hT hSc hSh hRho => Mx8.startOK_of hS hT hSc hSh hRho`.
-/
theorem start_assemble : Formalism.FourierDecayAlt.M.StartAssemble := by
  exact fun hS hT hSc hSh hRho => Mx8.startOK_of hS hT hSc hSh hRho

/- English proof (translation)
Introduce `P l`. Use `⟨fun σ hσ => ?_, ?_⟩` and prove the remaining obligations. Take `⟨j, -, rfl⟩` from `Mx8.mem_sitesFrom P 0 σ hσ`. Conclude with `⟨Mx8.isSiteA P j, Mx8.commutes_of_ent P j _ (Mx8.start_ent P l j)⟩`. Unfold `sitesFrom`.

Rewrite using `[List.drop_zero, List.pairwise_reverse, List.pairwise_ofFn]`. Introduce `i j hij`. Conclude with `Mx8.sitesCommuteA P j i (ne_of_gt hij)`.
-/
theorem sites_admissible_model : Formalism.FourierDecayAlt.M.SitesOKM := by
  intro P l
  refine ⟨fun σ hσ => ?_, ?_⟩
  · obtain ⟨j, -, rfl⟩ := Mx8.mem_sitesFrom P 0 σ hσ
    exact ⟨Mx8.isSiteA P j, Mx8.commutes_of_ent P j _ (Mx8.start_ent P l j)⟩
  · unfold sitesFrom
    rw [List.drop_zero, List.pairwise_reverse, List.pairwise_ofFn]
    intro i j hij
    exact Mx8.sitesCommuteA P j i (ne_of_gt hij)

/- English proof (translation)
Introduce `P L hL l Y`. Take `⟨hp, hpb, hc, hci, hcb, hcbi, -⟩` from `hL`. Take `⟨hs, -⟩` from `star_generators P`. Take `⟨h1, h2, h3⟩` from `hs l`. Use `⟨?_, fun hY => ?_⟩` and prove the remaining obligations.

Simplify using `only [LevelData.Tl, Ts, Tm, siteA, hp, hc, hci]`. Simplify using `only [LevelData.Tvl, Ts, Tm, siteA, hpb, hcb, hcbi]`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Use `show algebraMap ℂ (A P) Y - pbA P l = star (algebraMap ℂ (A P) Y + pA P l)`.

Rewrite using `[star_add, h3, ← algebraMap_star_comm, hY, sub_eq_add_neg]`. Use `show -cbA P l = star (-cA P l)`. Rewrite using `[star_neg, h1]`. Conclude with `h2.symm`. Conclude with `(star_zero (A P)).symm`.
-/
theorem site_joint : Formalism.FourierDecayAlt.M.SiteJoint := by
  intro P L hL l Y
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  obtain ⟨hs, -⟩ := star_generators P
  obtain ⟨h1, h2, h3⟩ := hs l
  refine ⟨?_, fun hY => ?_⟩
  · simp only [LevelData.Tl, Ts, Tm, siteA, hp, hc, hci]
  · simp only [LevelData.Tvl, Ts, Tm, siteA, hpb, hcb, hcbi]
    refine Matrix.ext fun a b => ?_
    fin_cases a <;> fin_cases b
    · show algebraMap ℂ (A P) Y - pbA P l = star (algebraMap ℂ (A P) Y + pA P l)
      rw [star_add, h3, ← algebraMap_star_comm, hY, sub_eq_add_neg]
    · show -cbA P l = star (-cA P l)
      rw [star_neg, h1]
    · exact h2.symm
    · exact (star_zero (A P)).symm

/- English proof (translation)
Conclude with `Mx8.chainM`.
-/
theorem model_chain : Formalism.FourierDecayAlt.M.ChainM := by
  exact Mx8.chainM

/- English proof (translation)
Conclude with `Mx8.lowerCommutes`.
-/
theorem lower_commutes : Formalism.FourierDecayAlt.M.LowerCommutes := by
  exact Mx8.lowerCommutes

/- English proof (translation)
Conclude with `Mx8.lowerStart_of h`.
-/
theorem mx_lowerStart_of (h : Formalism.FourierDecayAlt.M.StartIsStart) : Formalism.FourierDecayAlt.M.LowerStart := by
  exact Mx8.lowerStart_of h

/- English proof (translation)
Conclude with `Mx8.lowerStart_of (start_module_assemble hH hR hD)`.
-/
theorem mx_lowerStart_of_parts (hH : Formalism.FourierDecayAlt.M.QQHerm) (hR : Formalism.FourierDecayAlt.M.QQRTT) (hD : Formalism.FourierDecayAlt.M.QQDet) :
    Formalism.FourierDecayAlt.M.LowerStart := by
  exact Mx8.lowerStart_of (start_module_assemble hH hR hD)

end Formalism.FourierDecayAlt.P
