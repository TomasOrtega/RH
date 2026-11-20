import Formalism.HermitianCurvature.HermitianCurvatureProofs.RepIntCastMul

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Bridge

variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

/- English proof (translation)
Assemble the required witnesses or components as `⟨[], by simp, fun _ _ => by simp⟩`.
-/
private theorem rep_zero_lemma_2 (d : ℕ) : Rep d (0 : AA k r E) :=
  ⟨[], by simp, fun _ _ => by simp⟩

/- English proof (translation)
Simplify using `only [Formalism.REAL.Tm]`. Use `rep_add ?_ (hΛ c d)` and prove the remaining obligations. Use `split_ifs`. Conclude with `⟨[(v, [])], by simp, fun _ _ => by simp⟩`. Conclude with `rep_zero_lemma_2 1`.
-/
theorem rep_Tm_of {Λ : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → AA k r E} (hΛ : ∀ c d, Rep 1 (Λ c d))
    (v : ℂ) (c d : Fin (2 * r + k + 1)) : Rep 1 (Tm Λ v c d) := by
  simp only [Formalism.REAL.Tm]
  refine rep_add ?_ (hΛ c d)
  split_ifs
  · exact ⟨[(v, [])], by simp, fun _ _ => by simp⟩
  · exact rep_zero_lemma_2 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ev_one (f : Mat k r → E) : ev Eop (1 : AA k r E) f = f := rfl

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, f', hU, hgU, hcd, heq⟩` from `hf g₀ hg₀`. Conclude with `⟨U, f', hU, hgU, hcd.of_le (WithTop.coe_le_coe.mpr h), heq⟩`.
-/
private theorem ckOn_mono_lemma_4 {m m' : ℕ∞} (h : m' ≤ m) {f : Mat k r → E} (hf : CkOn m (GV k r) f) :
    CkOn m' (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hcd.of_le (WithTop.coe_le_coe.mpr h), heq⟩

/- English proof (translation)
Introduce `ts`. Proceed by induction on `ts with`. Consider the case `nil => exact ⟨[(1, [])], by simp, fun _ _ => by simp⟩`. Consider the case `cons t ts ih`. Rewrite using `[List.map_cons, List.prod_cons]`.

Conclude with `Rep.mono (by simp only [List.length_cons]; omega) (rep_mul (rep_Tm_of hΛ _ _ _) ih)`.
-/
private theorem rep_prod_lemma_3 {Λ : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → AA k r E} (hΛ : ∀ c d, Rep 1 (Λ c d)) :
    ∀ ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)),
      Rep ts.length ((ts.map fun t => Tm Λ t.1 t.2.1 t.2.2).prod) := by
  intro ts
  induction ts with
  | nil => exact ⟨[(1, [])], by simp, fun _ _ => by simp⟩
  | cons t ts ih =>
    rw [List.map_cons, List.prod_cons]
    exact Rep.mono (by simp only [List.length_cons]; omega) (rep_mul (rep_Tm_of hΛ _ _ _) ih)

/- English proof (translation)
Introduce `ts`. Proceed by induction on `ts with`. Consider the case `nil`. Introduce `f _ g _`. Simplify using `[ev_one]`.

Consider the case `cons t ts ih`. Introduce `f hf g hg`. Establish `hP` using `rep_prod_lemma_3 hΛ ts`. Establish `hf' : CkOn ((1 + ts.length : ℕ) : ℕ∞) (GV k r) f` using `ckOn_mono_lemma_4 (ENat.coe_le_coe.mpr (by simp only [List.length_cons]; omega)) hf`. Establish `hfs : CkOn ((ts.length : ℕ) : ℕ∞) (GV k r) f` using `ckOn_mono_lemma_4 (ENat.coe_le_coe.mpr (by simp only [List.length_cons]; omega)) hf`.

Establish `hφ : CkOn 1 (GV k r) (ev Eop ((ts.map fun t => Tm Λ t.1 t.2.1 t.2.2).prod) f)`. Simplify using `using ev_ck (Eop := Eop) hC hP 1 f hf'`. Establish `hI` using `ih f hfs`. Rewrite using `[List.map_cons, List.prod_cons, ev_mul (Eop := Eop) hC hL hA hS (rep_Tm_of hΛ _ _ _) hP f hf' g hg, hT _ _ _ _ hφ g hg]`. Simplify using `only [List.map_cons, List.foldr_cons, Formalism.QuantumDeterminants.Top]`.

Rewrite using `[hLop _ _ _ _ hI g hg, hI g hg]`.
-/
theorem bridge_fold (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop)
    {Λ : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → AA k r E} (hΛ : ∀ c d, Rep 1 (Λ c d))
    (Op : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (hLop : HL Op)
    (hT : ∀ v c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r, ev Eop (Tm Λ v c d) φ g = Top Op v c d φ g) :
    ∀ (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (f : Mat k r → E),
      CkOn ((ts.length : ℕ) : ℕ∞) (GV k r) f → ∀ g ∈ GV k r,
        ev Eop ((ts.map fun t => Tm Λ t.1 t.2.1 t.2.2).prod) f g =
          (ts.map fun t => Top Op t.1 t.2.1 t.2.2).foldr (fun T h => T h) f g := by
  intro ts
  induction ts with
  | nil =>
    intro f _ g _
    simp [ev_one]
  | cons t ts ih =>
    intro f hf g hg
    have hP := rep_prod_lemma_3 hΛ ts
    have hf' : CkOn ((1 + ts.length : ℕ) : ℕ∞) (GV k r) f :=
      ckOn_mono_lemma_4 (ENat.coe_le_coe.mpr (by simp only [List.length_cons]; omega)) hf
    have hfs : CkOn ((ts.length : ℕ) : ℕ∞) (GV k r) f :=
      ckOn_mono_lemma_4 (ENat.coe_le_coe.mpr (by simp only [List.length_cons]; omega)) hf
    have hφ : CkOn 1 (GV k r) (ev Eop ((ts.map fun t => Tm Λ t.1 t.2.1 t.2.2).prod) f) := by
      simpa using ev_ck (Eop := Eop) hC hP 1 f hf'
    have hI := ih f hfs
    rw [List.map_cons, List.prod_cons,
      ev_mul (Eop := Eop) hC hL hA hS (rep_Tm_of hΛ _ _ _) hP f hf' g hg, hT _ _ _ _ hφ g hg]
    simp only [List.map_cons, List.foldr_cons, Formalism.QuantumDeterminants.Top]
    rw [hLop _ _ _ _ hI g hg, hI g hg]

/- English proof (translation)
Simplify using `only [ev, Formalism.REAL.Tm, Formalism.QuantumDeterminants.Top]`. Apply the tactic sequence `split_ifs <;> simp [Lf, Formalism.FourierDecayAlt.P.JFxE.ell, Phi, Fw]`.
-/
theorem ev_Tm_Lf (v : ℂ) (a b : Fin (2 * r + k + 1)) (φ : Mat k r → E) (x : Mat k r) :
    ev Eop (Tm (Lf k r E) v a b) φ x = Top Eop v a b φ x := by
  simp only [ev, Formalism.REAL.Tm, Formalism.QuantumDeterminants.Top]
  split_ifs <;> simp [Lf, Formalism.FourierDecayAlt.P.JFxE.ell, Phi, Fw]

/- English proof (translation)
Introduce `g hg`. Simplify using `only [qminor, ev, Formalism.QuantumDeterminants.qminorOp, LinearMap.sum_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Establish `hb` using `bridge_fold Eop hC hL hA hS hΛ Op hLop hT (List.ofFn fun j => (u - ((j : ℕ) : ℂ), p (σ j), q j)) f (by simpa using hf) g hg`. Simplify using `only [List.map_ofFn, Function.comp_def, ev] at hb`.

Simplify using `[hb, Int.cast_smul_eq_zsmul]`.
-/
theorem bridge_qminor (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop)
    {Λ : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → AA k r E} (hΛ : ∀ c d, Rep 1 (Λ c d))
    (Op : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (hLop : HL Op)
    (hT : ∀ v c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r, ev Eop (Tm Λ v c d) φ g = Top Op v c d φ g)
    {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, ev Eop (qminor Λ p q u) f g = qminorOp Op p q u f g := by
  intro g hg
  simp only [qminor, ev, Formalism.QuantumDeterminants.qminorOp, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hb := bridge_fold Eop hC hL hA hS hΛ Op hLop hT
    (List.ofFn fun j => (u - ((j : ℕ) : ℂ), p (σ j), q j)) f (by simpa using hf) g hg
  simp only [List.map_ofFn, Function.comp_def, ev] at hb
  simp [hb, Int.cast_smul_eq_zsmul]

end Bridge

section Skew

variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

/- English proof (translation)
Assemble the required witnesses or components as `⟨[(1, [(a, b)])], by simp, fun _ _ => by simp [Lf, Formalism.FourierDecayAlt.P.JFxE.ell]⟩`.
-/
private theorem rep_Lf_lemma (a b : Fin (2 * r + k + 1)) : Rep 1 (Lf k r E a b) :=
  ⟨[(1, [(a, b)])], by simp, fun _ _ => by simp [Lf, Formalism.FourierDecayAlt.P.JFxE.ell]⟩

/- English proof (translation)
Simplify using `only [Formalism.FourierDecayAlt.P.JFxE.rel]`. Establish `h1` using `rep_Lf_lemma (k := k) (r := r) (E := E)`. Apply the tactic sequence `refine rep_sub (rep_sub (rep_mul (h1 a b) (h1 c d)) (rep_mul (h1 c d) (h1 a b))) (rep_sub ?_ ?_) <;> split_ifs`. Apply the tactic sequence `all_goals first`. Consider the case `exact Rep.mono (by norm_num) (h1 _ _)`.

Consider the case `exact rep_zero_lemma_2 2`.
-/
theorem rep_rel (a b c d : Fin (2 * r + k + 1)) : Rep 2 (rel (Lf k r E) a b c d) := by
  simp only [Formalism.FourierDecayAlt.P.JFxE.rel]
  have h1 := rep_Lf_lemma (k := k) (r := r) (E := E)
  refine rep_sub (rep_sub (rep_mul (h1 a b) (h1 c d)) (rep_mul (h1 c d) (h1 a b))) (rep_sub ?_ ?_) <;>
    split_ifs
  all_goals first
    | exact Rep.mono (by norm_num) (h1 _ _)
    | exact rep_zero_lemma_2 2

/- English proof (translation)
Introduce `g hg`. Establish `hLf : ∀ (a b : Fin (2 * r + k + 1)) (φ : Mat k r → E), ev Eop (Lf k r E a b) φ = Eop a b φ`. Introduce `a b φ`. Use function extensionality and compare the values at `x`. Simplify using `[ev, Lf, Formalism.FourierDecayAlt.P.JFxE.ell, Phi, Fw]`.

Establish `hz : ∀ φ : Mat k r → E, ev Eop (0 : AA k r E) φ = 0`. Introduce `φ`. Use function extensionality and compare the values at `x`. Simplify using `[ev]`. Establish `hsub : ∀ (x y : AA k r E) (φ : Mat k r → E), ev Eop (x - y) φ g = ev Eop x φ g - ev Eop y φ g`.

Introduce `x y φ`. Simplify using `[ev]`. Establish `h1` using `rep_Lf_lemma (k := k) (r := r) (E := E)`. Establish `hm : ∀ a b c d : Fin (2 * r + k + 1), ev Eop (Lf k r E a b * Lf k r E c d) ψ g = Eop a b (Eop c d ψ) g`. Introduce `a b c d`.

Rewrite using `[ev_mul (Eop := Eop) hC hL hA hS (h1 a b) (h1 c d) ψ hψ g hg, hLf, hLf]`. Simplify using `only [Formalism.FourierDecayAlt.P.JFxE.rel]`. Rewrite using `[hsub, hsub, hsub, hm, hm, hG a b c d ψ hψ g hg]`. Apply the tactic sequence `split_ifs <;> simp [hLf, hz]`.
-/
theorem ev_rel (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop)
    (a b c d : Fin (2 * r + k + 1)) (ψ : Mat k r → E) (hψ : CkOn 2 (GV k r) ψ) :
    ∀ g ∈ GV k r, ev Eop (rel (Lf k r E) a b c d) ψ g = 0 := by
  intro g hg
  have hLf : ∀ (a b : Fin (2 * r + k + 1)) (φ : Mat k r → E), ev Eop (Lf k r E a b) φ = Eop a b φ := by
    intro a b φ
    funext x
    simp [ev, Lf, Formalism.FourierDecayAlt.P.JFxE.ell, Phi, Fw]
  have hz : ∀ φ : Mat k r → E, ev Eop (0 : AA k r E) φ = 0 := by
    intro φ
    funext x
    simp [ev]
  have hsub : ∀ (x y : AA k r E) (φ : Mat k r → E), ev Eop (x - y) φ g = ev Eop x φ g - ev Eop y φ g := by
    intro x y φ
    simp [ev]
  have h1 := rep_Lf_lemma (k := k) (r := r) (E := E)
  have hm : ∀ a b c d : Fin (2 * r + k + 1),
      ev Eop (Lf k r E a b * Lf k r E c d) ψ g = Eop a b (Eop c d ψ) g := by
    intro a b c d
    rw [ev_mul (Eop := Eop) hC hL hA hS (h1 a b) (h1 c d) ψ hψ g hg, hLf, hLf]
  simp only [Formalism.FourierDecayAlt.P.JFxE.rel]
  rw [hsub, hsub, hsub, hm, hm, hG a b c d ψ hψ g hg]
  split_ifs <;> simp [hLf, hz]

/- English proof (translation)
Unfold `Md`. Conclude with `rep_add (rep_rel _ _ _ _) (rep_rel _ _ _ _)`.
-/
theorem rep_Md {m : ℕ} (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m) :
    Rep 2 (Md (Lf k r E) a b σ i) := by
  unfold Md
  exact rep_add (rep_rel _ _ _ _) (rep_rel _ _ _ _)

/- English proof (translation)
Introduce `x hx`. Rewrite `hx` using `[List.mem_ofFn]`. Take `⟨j, rfl⟩` from `hx`. Conclude with `rep_Tm_of (fun c d => rep_Lf_lemma c d) _ _ _`.
-/
theorem rep_fac_list {m : ℕ} (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1))) :
    ∀ x ∈ List.ofFn (fac (Lf k r E) a b u σ), Rep 1 x := by
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨j, rfl⟩ := hx
  exact rep_Tm_of (fun c d => rep_Lf_lemma c d) _ _ _

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simpa [Fw] using h`. Consider the case `cons x w ih`. Introduce `g hg`. Simplify using `only [Fw, List.foldr_cons] at ih ⊢`.

Conclude with `hL _ _ _ _ ih g hg`.
-/
private theorem fw_local_lemma_7 (hL : HL Eop) (w : List (Ix k r)) (f f₂ : Mat k r → E)
    (h : ∀ g ∈ GV k r, f g = f₂ g) : ∀ g ∈ GV k r, Fw Eop w f g = Fw Eop w f₂ g := by
  induction w with
  | nil => simpa [Fw] using h
  | cons x w ih =>
    intro g hg
    simp only [Fw, List.foldr_cons] at ih ⊢
    exact hL _ _ _ _ ih g hg

/- English proof (translation)
Introduce `g hg`. Take `⟨L, -, hLa⟩` from `ha`. Simplify using `only [ev, hLa, Phi, List.nil_append]`. Establish `key : ∀ L' : List (ℂ × List (Ix k r)), (L'.map fun p => p.1 • Fw Eop p.2 f).sum g = (L'.map fun p => p.1 • Fw Eop p.2 f₂).sum g`. Introduce `L'`.

Proceed by induction on `L' with`. Consider the case `nil => simp`. Consider the case `cons p L' ih`. Simplify using `only [List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply, ih, fw_local_lemma_7 Eop hL p.2 f f₂ h g hg]`. Conclude with `key L`.
-/
private theorem ev_local_lemma_8 (hL : HL Eop) {d : ℕ} {a : AA k r E} (ha : Rep d a) (f f₂ : Mat k r → E)
    (h : ∀ g ∈ GV k r, f g = f₂ g) : ∀ g ∈ GV k r, ev Eop a f g = ev Eop a f₂ g := by
  intro g hg
  obtain ⟨L, -, hLa⟩ := ha
  simp only [ev, hLa, Phi, List.nil_append]
  have key : ∀ L' : List (ℂ × List (Ix k r)),
      (L'.map fun p => p.1 • Fw Eop p.2 f).sum g = (L'.map fun p => p.1 • Fw Eop p.2 f₂).sum g := by
    intro L'
    induction L' with
    | nil => simp
    | cons p L' ih =>
      simp only [List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply, ih,
        fw_local_lemma_7 Eop hL p.2 f f₂ h g hg]
  exact key L

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro _; exact ⟨[(1, [])], by simp, fun _ _ => by simp⟩`. Consider the case `cons x l ih`. Introduce `h`.

Rewrite using `[List.prod_cons]`. Conclude with `Rep.mono (by simp only [List.length_cons]; omega) (rep_mul (h x (by simp)) (ih fun y hy => h y (by simp [hy])))`.
-/
private theorem rep_list_lemma_9 : ∀ l : List (AA k r E), (∀ x ∈ l, Rep 1 x) → Rep l.length l.prod := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[(1, [])], by simp, fun _ _ => by simp⟩
  | cons x l ih =>
    intro h
    rw [List.prod_cons]
    exact Rep.mono (by simp only [List.length_cons]; omega)
      (rep_mul (h x (by simp)) (ih fun y hy => h y (by simp [hy])))

/- English proof (translation)
Introduce `g hg`. Unfold `Lt Rt`. Establish `h0 : ∀ φ : Mat k r → E, ev Eop (0 : AA k r E) φ = 0`. Introduce `φ`. Use function extensionality and compare the values at `x`.

Simplify using `[ev]`. Establish `hadd : ∀ (x y : AA k r E) (φ : Mat k r → E) (g' : Mat k r), ev Eop (x + y) φ g' = ev Eop x φ g' + ev Eop y φ g'`. Introduce `x y φ g'`. Simplify using `[ev]`. Establish `hL1` using `rep_fac_list (k := k) (r := r) (E := E) a b u σ`.

Use `set L := List.ofFn (fac (Lf k r E) a b u σ) with hLdef`. Establish `hLt` using `rep_list_lemma_9 (L.take i) (fun x hx => hL1 x (List.mem_of_mem_take hx))`. Establish `hRt` using `rep_list_lemma_9 (L.drop ((i : ℕ) + 2)) (fun x hx => hL1 x (List.mem_of_mem_drop hx))`. Establish `hMd` using `rep_Md (k := k) (r := r) (E := E) a b σ i`. Establish `hlen : (L.take i).length + 2 + (L.drop ((i : ℕ) + 2)).length = m + 1`.

Use `i.isLt` as an intermediate fact. Simplify using `only [hLdef, List.length_take, List.length_drop, List.length_ofFn]`. Use linear arithmetic over natural numbers and integers. Establish `hf3 : CkOn (((L.take i).length + 2 + (L.drop ((i : ℕ) + 2)).length : ℕ) : ℕ∞) (GV k r) f`. Rewrite using `[hlen]`.

Conclude with `hf`. Establish `hψ : CkOn (((L.take i).length + 2 : ℕ) : ℕ∞) (GV k r) (ev Eop (L.drop ((i : ℕ) + 2)).prod f)` using `ev_ck (Eop := Eop) hC hRt _ f hf3`. Establish `hψ2 : CkOn 2 (GV k r) (ev Eop (L.drop ((i : ℕ) + 2)).prod f)`. Use `ev_ck (Eop := Eop) hC hRt 2 f (ckOn_mono_lemma_4 (ENat.coe_le_coe.mpr (by omega)) hf3)` as an intermediate fact. Simplify using `using this`.

Establish `hz : ∀ g' ∈ GV k r, ev Eop (Md (Lf k r E) a b σ i) (ev Eop (L.drop ((i : ℕ) + 2)).prod f) g' = 0`. Introduce `g' hg'`. Unfold `Md`. Rewrite using `[hadd, ev_rel Eop hC hL hA hS hG _ _ _ _ _ hψ2 g' hg', ev_rel Eop hC hL hA hS hG _ _ _ _ _ hψ2 g' hg', add_zero]`. Rewrite using `[ev_mul (Eop := Eop) hC hL hA hS (rep_mul hLt hMd) hRt f hf3 g hg, ev_mul (Eop := Eop) hC hL hA hS hLt hMd _ hψ g hg, ev_local_lemma_8 Eop hL hLt (ev Eop (Md (Lf k r E) a b σ i) (ev Eop (L.drop ((i : ℕ) + 2)).prod f)) (ev Eop (0 : AA k r E) (ev Eop (L.drop ((i : ℕ) + 2)).prod f)) …`.

Simplify using `[h0]`.
-/
theorem ev_LMR (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop) {m : ℕ}
    (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m)
    (f : Mat k r → E) (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, ev Eop (Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i) f g = 0 := by
  intro g hg
  unfold Lt Rt
  have h0 : ∀ φ : Mat k r → E, ev Eop (0 : AA k r E) φ = 0 := by
    intro φ
    funext x
    simp [ev]
  have hadd : ∀ (x y : AA k r E) (φ : Mat k r → E) (g' : Mat k r),
      ev Eop (x + y) φ g' = ev Eop x φ g' + ev Eop y φ g' := by
    intro x y φ g'
    simp [ev]
  have hL1 := rep_fac_list (k := k) (r := r) (E := E) a b u σ
  set L := List.ofFn (fac (Lf k r E) a b u σ) with hLdef
  have hLt := rep_list_lemma_9 (L.take i) (fun x hx => hL1 x (List.mem_of_mem_take hx))
  have hRt := rep_list_lemma_9 (L.drop ((i : ℕ) + 2)) (fun x hx => hL1 x (List.mem_of_mem_drop hx))
  have hMd := rep_Md (k := k) (r := r) (E := E) a b σ i
  have hlen : (L.take i).length + 2 + (L.drop ((i : ℕ) + 2)).length = m + 1 := by
    have := i.isLt
    simp only [hLdef, List.length_take, List.length_drop, List.length_ofFn]
    omega
  have hf3 : CkOn (((L.take i).length + 2 + (L.drop ((i : ℕ) + 2)).length : ℕ) : ℕ∞) (GV k r) f := by
    rw [hlen]
    exact hf
  have hψ : CkOn (((L.take i).length + 2 : ℕ) : ℕ∞) (GV k r) (ev Eop (L.drop ((i : ℕ) + 2)).prod f) :=
    ev_ck (Eop := Eop) hC hRt _ f hf3
  have hψ2 : CkOn 2 (GV k r) (ev Eop (L.drop ((i : ℕ) + 2)).prod f) := by
    have := ev_ck (Eop := Eop) hC hRt 2 f (ckOn_mono_lemma_4 (ENat.coe_le_coe.mpr (by omega)) hf3)
    simpa using this
  have hz : ∀ g' ∈ GV k r,
      ev Eop (Md (Lf k r E) a b σ i) (ev Eop (L.drop ((i : ℕ) + 2)).prod f) g' = 0 := by
    intro g' hg'
    unfold Md
    rw [hadd, ev_rel Eop hC hL hA hS hG _ _ _ _ _ hψ2 g' hg', ev_rel Eop hC hL hA hS hG _ _ _ _ _ hψ2 g' hg',
      add_zero]
  rw [ev_mul (Eop := Eop) hC hL hA hS (rep_mul hLt hMd) hRt f hf3 g hg,
    ev_mul (Eop := Eop) hC hL hA hS hLt hMd _ hψ g hg,
    ev_local_lemma_8 Eop hL hLt (ev Eop (Md (Lf k r E) a b σ i) (ev Eop (L.drop ((i : ℕ) + 2)).prod f))
      (ev Eop (0 : AA k r E) (ev Eop (L.drop ((i : ℕ) + 2)).prod f))
      (fun g' hg' => by simp [hz g' hg', h0]) g hg,
    ← ev_mul (Eop := Eop) hC hL hA hS hLt (rep_zero_lemma_2 2) _ hψ g hg]
  simp [h0]

/- English proof (translation)
Introduce `g hg`. Establish `hR : ∀ σ : Equiv.Perm (Fin (m + 1)), (Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i) (Phi Eop f) [] g = 0` using `fun σ => ev_LMR Eop hC hL hA hS hG a b u σ i f hf g hg`. Establish `hR' : ∀ σ : Equiv.Perm (Fin (m + 1)), (((Equiv.Perm.sign σ : ℤ) : AA k r E) * (Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i)) (Phi Eop f) [] g = 0`. Introduce `σ`. Establish `h0` using `hR σ`.

Generalize the expression as in `Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i = P at h0 ⊢`. Simplify using `[h0]`. Establish `h` using `congrArg (fun x : AA k r E => x (Phi Eop f) [] g) (adj_formal (Lf k r E) a b i u)`. Simplify using `only [LinearMap.smul_apply, LinearMap.add_apply, Pi.smul_apply, Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply, hR', Finset.sum_const_zero] at h`. Establish `h3` using `(smul_eq_zero.mp h).resolve_left two_ne_zero`.

Conclude with `eq_neg_of_add_eq_zero_left h3`.
-/
theorem sk_adj (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop) {m : ℕ}
    (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (i : Fin m) (u : ℂ)
    (f : Mat k r → E) (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, ev Eop (qminor (Lf k r E) a (b ∘ Equiv.swap i.castSucc i.succ) u) f g =
      - ev Eop (qminor (Lf k r E) a b u) f g := by
  intro g hg
  have hR : ∀ σ : Equiv.Perm (Fin (m + 1)),
      (Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i) (Phi Eop f) [] g = 0 :=
    fun σ => ev_LMR Eop hC hL hA hS hG a b u σ i f hf g hg
  have hR' : ∀ σ : Equiv.Perm (Fin (m + 1)),
      (((Equiv.Perm.sign σ : ℤ) : AA k r E) *
        (Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i)) (Phi Eop f) [] g = 0 := by
    intro σ
    have h0 := hR σ
    generalize Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i = P at h0 ⊢
    simp [h0]
  have h := congrArg (fun x : AA k r E => x (Phi Eop f) [] g) (adj_formal (Lf k r E) a b i u)
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Pi.smul_apply, Pi.add_apply, LinearMap.sum_apply,
    Finset.sum_apply, hR', Finset.sum_const_zero] at h
  have h3 := (smul_eq_zero.mp h).resolve_left two_ne_zero
  exact eq_neg_of_add_eq_zero_left h3

/- English proof (translation)
Consider the cases of `t with`. Consider the case `zero`. Introduce `b g hg`. Establish `hτ : τ = 1` using `Subsingleton.elim _ _`. Substitute `hτ` using the available equality.

Simplify using the standard rewrite rules. Consider the case `succ m`. Establish `hmem : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ)`. Rewrite using `[Equiv.Perm.mclosure_swap_castSucc_succ]`. Conclude with `Submonoid.mem_top τ`.

Proceed by induction on `hmem using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Introduce `b g hg`. Rewrite using `[sk_adj Eop hC hL hA hS hG a b i u f hf g hg, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ : i.castSucc < i.succ).ne]`.

Simplify using the standard rewrite rules. Consider the case `one`. Introduce `b g hg`. Simplify using the standard rewrite rules. Consider the case `mul x y _ _ hx hy`.

Introduce `b g hg`. Establish `e : b ∘ ⇑(x * y) = (b ∘ ⇑x) ∘ ⇑y` using `rfl`. Rewrite using `[e, hy (b ∘ ⇑x) g hg, hx b g hg, Equiv.Perm.sign_mul]`. Simplify using `only [Units.val_mul, Int.cast_mul, mul_smul]`. Rewrite using `[smul_comm]`.
-/
theorem sk_perm (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop) {t : ℕ}
    (a : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f)
    (τ : Equiv.Perm (Fin t)) :
    ∀ (b : Fin t → Fin (2 * r + k + 1)), ∀ g ∈ GV k r,
      ev Eop (qminor (Lf k r E) a (b ∘ τ) u) f g = ((Equiv.Perm.sign τ : ℤ) : ℂ) • ev Eop (qminor (Lf k r E) a b u) f g := by
  cases t with
  | zero =>
    intro b g hg
    have hτ : τ = 1 := Subsingleton.elim _ _
    subst hτ
    simp
  | succ m =>
    have hmem : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top τ
    induction hmem using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro b g hg
      rw [sk_adj Eop hC hL hA hS hG a b i u f hf g hg, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ : i.castSucc < i.succ).ne]
      simp
    | one =>
      intro b g hg
      simp
    | mul x y _ _ hx hy =>
      intro b g hg
      have e : b ∘ ⇑(x * y) = (b ∘ ⇑x) ∘ ⇑y := rfl
      rw [e, hy (b ∘ ⇑x) g hg, hx b g hg, Equiv.Perm.sign_mul]
      simp only [Units.val_mul, Int.cast_mul, mul_smul]
      rw [smul_comm]

/- English proof (translation)
Introduce `g hg`. Simplify using `only [Function.Injective, not_forall] at hb`. Take `⟨i, j, hij, hne⟩` from `hb`. Establish `hb' : b ∘ ⇑(Equiv.swap i j) = b`. Use function extensionality and compare the values at `x`.

Simplify using `only [Function.comp_apply, Equiv.swap_apply_def]`. Apply the tactic sequence `split_ifs <;> simp_all`. Establish `h` using `sk_perm Eop hC hL hA hS hG a u f hf (Equiv.swap i j) b g hg`. Rewrite `h` using `[hb', Equiv.Perm.sign_swap hne]`. Simplify using `at h`.

Establish `h2 : (2 : ℂ) • ev Eop (qminor (Lf k r E) a b u) f g = 0`. Rewrite using `[two_smul]`. Use `nth_rw 1 [h]`. Simplify using the standard rewrite rules. Conclude with `(smul_eq_zero.mp h2).resolve_left two_ne_zero`.
-/
theorem sk_zero (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop) {t : ℕ}
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f)
    (hb : ¬ Function.Injective b) : ∀ g ∈ GV k r, ev Eop (qminor (Lf k r E) a b u) f g = 0 := by
  intro g hg
  simp only [Function.Injective, not_forall] at hb
  obtain ⟨i, j, hij, hne⟩ := hb
  have hb' : b ∘ ⇑(Equiv.swap i j) = b := by
    funext x
    simp only [Function.comp_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have h := sk_perm Eop hC hL hA hS hG a u f hf (Equiv.swap i j) b g hg
  rw [hb', Equiv.Perm.sign_swap hne] at h
  simp at h
  have h2 : (2 : ℂ) • ev Eop (qminor (Lf k r E) a b u) f g = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

end Skew

section Ad

variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

/- English proof (translation)
Unfold `Ead`. Use `Finset.sum_induction _ (Rep 1) (fun _ _ => rep_add) (rep_zero_lemma_2 1) (fun a _ => ?_)` and prove the remaining obligations. Use `Finset.sum_induction _ (Rep 1) (fun _ _ => rep_add) (rep_zero_lemma_2 1) (fun b _ => ?_)` and prove the remaining obligations. Conclude with `rep_smul _ (rep_Lf_lemma a b)`.
-/
theorem rep_Ead (P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c d : Fin (2 * r + k + 1)) :
    Rep 1 (Ead (Lf k r E) P Q c d) := by
  unfold Ead
  refine Finset.sum_induction _ (Rep 1) (fun _ _ => rep_add) (rep_zero_lemma_2 1) (fun a _ => ?_)
  refine Finset.sum_induction _ (Rep 1) (fun _ _ => rep_add) (rep_zero_lemma_2 1) (fun b _ => ?_)
  exact rep_smul _ (rep_Lf_lemma a b)

/- English proof (translation)
Simplify using `only [ev, Formalism.REAL.Tm, Ead]`. Apply the tactic sequence `split_ifs <;> simp [Lf, Formalism.FourierDecayAlt.P.JFxE.ell, Phi, Fw, LinearMap.sum_apply, Finset.sum_apply]`.
-/
theorem ev_Tm_Ead (P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : ℂ) (c d : Fin (2 * r + k + 1))
    (φ : Mat k r → E) (x : Mat k r) :
    ev Eop (Tm (Ead (Lf k r E) P Q) v c d) φ x =
      (if c = d then v • φ x else 0) + ∑ a, ∑ b, (P a c * Q d b) • Eop a b φ x := by
  simp only [ev, Formalism.REAL.Tm, Ead]
  split_ifs <;> simp [Lf, Formalism.FourierDecayAlt.P.JFxE.ell, Phi, Fw, LinearMap.sum_apply, Finset.sum_apply]

/- English proof (translation)
Introduce `g hg`. Establish `hΛ : ∀ c d, Rep 1 (Ead (Lf k r E) P Q c d)` using `fun c d => rep_Ead P Q c d`. Establish `hT : ∀ v c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r, ev Eop (Tm (Ead (Lf k r E) P Q) v c d) φ g = Formalism.QuantumDeterminants.Top Op v c d φ g`. Introduce `v c d φ hφ g hg`. Simplify using `only [ev_Tm_Ead, Formalism.QuantumDeterminants.Top, hE c d φ hφ g hg]`.

Establish `hA'` using `bridge_qminor Eop hC hL hA hS hΛ Op hLop hT (⇑e) (⇑e) u f hf g hg`. Establish `hB'` using `bridge_qminor Eop hC hL hA hS (fun c d => rep_Lf_lemma c d) Eop hL (fun v c d φ _ g _ => ev_Tm_Lf Eop v c d φ g) (⇑e) (⇑e) u f hf g hg`. Rewrite using `[← hA', ← hB', qminor_Ead (Lf k r E) hQP e u]`. Establish `hlin : ev Eop (P.det • ∑ β : Fin t → Fin (2 * r + k + 1), (∏ j, Q (e j) (β j)) • qminor (Lf k r E) (⇑e) β u) f g = P.det • ∑ β : Fin t → Fin (2 * r + k + 1), (∏ j, Q (e j) (β j)) • ev Eop (qminor (Lf k r E) (⇑e) β u) f g`. Simplify using `only [ev, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply, Pi.smul_apply]`.

Rewrite using `[hlin, ← Equiv.sum_comp (Equiv.arrowCongr (Equiv.refl (Fin t)) e)]`. Simplify using `only [Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, Function.comp_apply]`. Establish `hac : ∀ γ : Fin t → Fin t, (Equiv.arrowCongr (Equiv.refl (Fin t)) e) γ = ⇑e ∘ γ` using `fun γ => rfl`. Simplify using `only [hac]`. Establish `hsplit : ∀ F : (Fin t → Fin t) → E, (∀ γ, ¬ Function.Injective γ → F γ = 0) → ∑ γ, F γ = ∑ τ : Equiv.Perm (Fin t), F ⇑τ` using `by classical`.

Introduce `F hF`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ (Finset.univ.image fun τ : Equiv.Perm (Fin t) => (⇑τ : Fin t → Fin t))) ?_]`. Rewrite using `[Finset.sum_image]`. Introduce `τ₁ _ τ₂ _ h`. Conclude with `Equiv.coe_fn_injective h`.

Introduce `γ _ hγ`. Apply `hF` to reduce the goal to its premises. Introduce `hinj`. Apply `hγ` to reduce the goal to its premises. Conclude with `Finset.mem_image.mpr ⟨Equiv.ofBijective γ (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩`.

Establish `hz : ∀ γ : Fin t → Fin t, ¬ Function.Injective γ → (∏ j, Q (e j) (e (γ j))) • ev Eop (qminor (Lf k r E) (⇑e) (⇑e ∘ γ) u) f g = 0`. Introduce `γ hγ`. Rewrite using `[sk_zero Eop hC hL hA hS hG (⇑e) (⇑e ∘ γ) u f hf (fun h => hγ (Function.Injective.of_comp h)) g hg, smul_zero]`. Rewrite using `[hsplit _ hz]`. Establish `hp : ∀ τ : Equiv.Perm (Fin t), ev Eop (qminor (Lf k r E) (⇑e) (⇑e ∘ ⇑τ) u) f g = ((Equiv.Perm.sign τ : ℤ) : ℂ) • ev Eop (qminor (Lf k r E) (⇑e) (⇑e) u) f g` using `fun τ => sk_perm Eop hC hL hA hS hG (⇑e) u f hf τ (⇑e) g hg`.

Simplify using `only [hp, smul_smul, ← Finset.sum_smul]`. Establish `hdet : ∑ τ : Equiv.Perm (Fin t), (∏ j, Q (e j) (e (τ j))) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = Q.det`. Rewrite using `[← Matrix.det_submatrix_equiv_self e Q, ← Matrix.det_transpose, Matrix.det_apply]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.submatrix_apply, Matrix.transpose_apply, Units.smul_def, zsmul_eq_mul, mul_comm]`.

Establish `h1 : P.det * Q.det = 1`. Rewrite using `[mul_comm, ← Matrix.det_mul, hQP, Matrix.det_one]`. Rewrite using `[hdet, h1, one_smul]`.
-/
theorem ad_main (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop)
    (Op : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (hLop : HL Op)
    {P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hQP : Q * P = 1)
    (hE : ∀ c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r,
      Op c d φ g = ∑ a, ∑ b, (P a c * Q d b) • Eop a b φ g)
    {t : ℕ} (e : Fin t ≃ Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, qminorOp Op e e u f g = qminorOp Eop e e u f g := by
  intro g hg
  have hΛ : ∀ c d, Rep 1 (Ead (Lf k r E) P Q c d) := fun c d => rep_Ead P Q c d
  have hT : ∀ v c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r,
      ev Eop (Tm (Ead (Lf k r E) P Q) v c d) φ g = Formalism.QuantumDeterminants.Top Op v c d φ g := by
    intro v c d φ hφ g hg
    simp only [ev_Tm_Ead, Formalism.QuantumDeterminants.Top, hE c d φ hφ g hg]
  have hA' := bridge_qminor Eop hC hL hA hS hΛ Op hLop hT (⇑e) (⇑e) u f hf g hg
  have hB' := bridge_qminor Eop hC hL hA hS (fun c d => rep_Lf_lemma c d) Eop hL
    (fun v c d φ _ g _ => ev_Tm_Lf Eop v c d φ g) (⇑e) (⇑e) u f hf g hg
  rw [← hA', ← hB', qminor_Ead (Lf k r E) hQP e u]
  have hlin : ev Eop (P.det • ∑ β : Fin t → Fin (2 * r + k + 1),
      (∏ j, Q (e j) (β j)) • qminor (Lf k r E) (⇑e) β u) f g =
      P.det • ∑ β : Fin t → Fin (2 * r + k + 1),
        (∏ j, Q (e j) (β j)) • ev Eop (qminor (Lf k r E) (⇑e) β u) f g := by
    simp only [ev, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply, Pi.smul_apply]
  rw [hlin, ← Equiv.sum_comp (Equiv.arrowCongr (Equiv.refl (Fin t)) e)]
  simp only [Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, Function.comp_apply]
  have hac : ∀ γ : Fin t → Fin t, (Equiv.arrowCongr (Equiv.refl (Fin t)) e) γ = ⇑e ∘ γ := fun γ => rfl
  simp only [hac]
  have hsplit : ∀ F : (Fin t → Fin t) → E, (∀ γ, ¬ Function.Injective γ → F γ = 0) →
      ∑ γ, F γ = ∑ τ : Equiv.Perm (Fin t), F ⇑τ := by
    classical
    intro F hF
    rw [← Finset.sum_subset
      (Finset.subset_univ (Finset.univ.image fun τ : Equiv.Perm (Fin t) => (⇑τ : Fin t → Fin t))) ?_]
    · rw [Finset.sum_image]
      intro τ₁ _ τ₂ _ h
      exact Equiv.coe_fn_injective h
    · intro γ _ hγ
      apply hF
      intro hinj
      apply hγ
      exact Finset.mem_image.mpr
        ⟨Equiv.ofBijective γ (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩
  have hz : ∀ γ : Fin t → Fin t, ¬ Function.Injective γ →
      (∏ j, Q (e j) (e (γ j))) • ev Eop (qminor (Lf k r E) (⇑e) (⇑e ∘ γ) u) f g = 0 := by
    intro γ hγ
    rw [sk_zero Eop hC hL hA hS hG (⇑e) (⇑e ∘ γ) u f hf (fun h => hγ (Function.Injective.of_comp h)) g hg,
      smul_zero]
  rw [hsplit _ hz]
  have hp : ∀ τ : Equiv.Perm (Fin t), ev Eop (qminor (Lf k r E) (⇑e) (⇑e ∘ ⇑τ) u) f g =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) • ev Eop (qminor (Lf k r E) (⇑e) (⇑e) u) f g :=
    fun τ => sk_perm Eop hC hL hA hS hG (⇑e) u f hf τ (⇑e) g hg
  simp only [hp, smul_smul, ← Finset.sum_smul]
  have hdet : ∑ τ : Equiv.Perm (Fin t), (∏ j, Q (e j) (e (τ j))) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = Q.det := by
    rw [← Matrix.det_submatrix_equiv_self e Q, ← Matrix.det_transpose, Matrix.det_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp [Matrix.submatrix_apply, Matrix.transpose_apply, Units.smul_def, zsmul_eq_mul, mul_comm]
  have h1 : P.det * Q.det = 1 := by
    rw [mul_comm, ← Matrix.det_mul, hQP, Matrix.det_one]
  rw [hdet, h1, one_smul]

end Ad

end Formalism.FourierDecayAlt.P.JFxE
