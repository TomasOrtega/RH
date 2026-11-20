import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.HeisOpHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.SecondDualReduction

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW.LeviW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.TermsAtPtFiniteW.HeisW

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def psiF (e f : Fin r → S.V) (U U' : Matrix (Fin r) (Fin r) E) : S.V →ₗ[E] S.V :=
  LinearMap.id + ∑ a, (S.hT (f a)).smulRight (∑ c, U c a • e c - e a) +
    ∑ a, (S.hT (e a)).smulRight (∑ c, U' c a • f c - f a)

/- English proof (translation)
Simplify using `[psiF, LinearMap.sum_apply]`.
-/
theorem psiF_apply (e f : Fin r → S.V) (U U' : Matrix (Fin r) (Fin r) E) (v : S.V) :
    psiF e f U U' v = v + ∑ a, S.hT (f a) v • (∑ c, U c a • e c - e a) +
      ∑ a, S.hT (e a) v • (∑ c, U' c a • f c - f a) := by
  simp [psiF, LinearMap.sum_apply]

def wv (e f : Fin r → S.V) (v : S.V) : S.V :=
  v - ∑ a, S.hT (f a) v • e a - ∑ a, S.hT (e a) v • f a

/- English proof (translation)
Rewrite using `[psiF_apply, wv]`. Simplify using `only [smul_sub, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem psiF_eq (e f : Fin r → S.V) (U U' : Matrix (Fin r) (Fin r) E) (v : S.V) :
    psiF e f U U' v = wv e f v + ∑ a, S.hT (f a) v • ∑ c, U c a • e c +
      ∑ a, S.hT (e a) v • ∑ c, U' c a • f c := by
  rw [psiF_apply, wv]
  simp only [smul_sub, Finset.sum_sub_distrib]
  abel

/- English proof (translation)
Rewrite using `[psiF_apply]`. Simplify using `[Matrix.one_apply]`.
-/
theorem psiF_one (e f : Fin r → S.V) (v : S.V) : psiF e f 1 1 v = v := by
  rw [psiF_apply]
  simp [Matrix.one_apply]

section Pair

variable (e f : Fin r → S.V) (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)

include hef in
/- English proof (translation)
Rewrite using `[← hsym, hef]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.
-/
theorem hfe (a b : Fin r) : S.hT (f a) (e b) = if a = b then 1 else 0 := by
  rw [← hsym, hef]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

include hee hef in
/- English proof (translation)
Simplify using `[wv, hee, hef]`.
-/
theorem e_w (c : Fin r) (v : S.V) : S.hT (e c) (wv e f v) = 0 := by
  simp [wv, hee, hef]

include hff hef in
/- English proof (translation)
Simplify using `[wv, hff, hfe e f hef]`.
-/
theorem f_w (c : Fin r) (v : S.V) : S.hT (f c) (wv e f v) = 0 := by
  simp [wv, hff, hfe e f hef]

/- English proof (translation)
Establish `key : ∀ a, ∑ c, u c a * ∑ b, q b * w c b = q a`. Introduce `a`. Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Use `_ = q a := by simp [h]`. Simplify using `only [key]`.
-/
theorem algδ (p q : Fin r → E) (u w : Matrix (Fin r) (Fin r) E)
    (h : ∀ a b, ∑ c, u c a * w c b = if a = b then 1 else 0) :
    ∑ a, p a * ∑ c, u c a * ∑ b, q b * w c b = ∑ a, p a * q a := by
  have key : ∀ a, ∑ c, u c a * ∑ b, q b * w c b = q a := by
    intro a
    calc ∑ c, u c a * ∑ b, q b * w c b = ∑ b, q b * ∑ c, u c a * w c b := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = q a := by simp [h]
  simp only [key]

include hee hff hef in
/- English proof (translation)
Establish `hUU' : ∀ a b, ∑ c, star (U' c a) * U c b = if a = b then 1 else 0`. Introduce `a b`. Establish `h1 : ∑ c, star (U' c a) * U c b = star (∑ c, star (U c b) * U' c a)`. Simplify using `only [star_sum, star_mul', star_star]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`.

Rewrite using `[h1, hUU b a]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.

Establish `pairR : ∀ (u : S.V) (s : Fin r → E) (t : Matrix (Fin r) (Fin r) E) (g : Fin r → S.V), S.hT u (∑ a, s a • ∑ c, t c a • g c) = ∑ a, s a * ∑ c, t c a * S.hT u (g c)`. Introduce `u s t g`. Simplify using `[map_sum, smul_eq_mul]`. Establish `pairL : ∀ (u : S.V) (s : Fin r → E) (t : Matrix (Fin r) (Fin r) E) (g : Fin r → S.V), S.hT (∑ a, s a • ∑ c, t c a • g c) u = ∑ a, star (s a) * ∑ c, star (t c a) * S.hT (g c) u`. Introduce `u s t g`.

Simplify using `[map_sum, LinearMap.sum_apply, smul_eq_mul, starRingEnd_apply]`. Establish `hwe : ∀ (v : S.V) (c : Fin r), S.hT (wv e f v) (e c) = 0` using `fun v c => by`. Rewrite using `[← hsym, e_w e f hee hef c v, star_zero]`. Establish `hwf : ∀ (v : S.V) (c : Fin r), S.hT (wv e f v) (f c) = 0` using `fun v c => by`. Rewrite using `[← hsym, f_w e f hff hef c v, star_zero]`.

Establish `hfe'` using `hfe e f hef`. Establish `k1 : ∑ a, star (S.hT (f a) x) * ∑ c, star (U c a) * ∑ b, S.hT (e b) y * U' c b = ∑ a, star (S.hT (f a) x) * S.hT (e a) y` using `algδ _ _ (fun c a => star (U c a)) U' hUU`. Establish `k2 : ∑ a, star (S.hT (e a) x) * ∑ c, star (U' c a) * ∑ b, S.hT (f b) y * U c b = ∑ a, star (S.hT (e a) x) * S.hT (f a) y` using `algδ _ _ (fun c a => star (U' c a)) U hUU'`. Rewrite using `[psiF_eq, psiF_eq]`. Simplify using `only [map_add, LinearMap.add_apply]`.

Simplify using `only [pairL]`. Simplify using `only [pairR]`. Simplify using `only [hwe, hwf, e_w e f hee hef, f_w e f hff hef, hee, hff, hef, hfe', mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Take the linear combination `k1 + k2`.
-/
theorem gram (U U' : Matrix (Fin r) (Fin r) E) (hUU : ∀ a b, ∑ c, star (U c a) * U' c b = if a = b then 1 else 0)
    (x y : S.V) :
    S.hT (psiF e f U U' x) (psiF e f U U' y) = S.hT (wv e f x) (wv e f y) +
      ∑ a, star (S.hT (f a) x) * S.hT (e a) y + ∑ a, star (S.hT (e a) x) * S.hT (f a) y := by
  have hUU' : ∀ a b, ∑ c, star (U' c a) * U c b = if a = b then 1 else 0 := by
    intro a b
    have h1 : ∑ c, star (U' c a) * U c b = star (∑ c, star (U c b) * U' c a) := by
      simp only [star_sum, star_mul', star_star]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [h1, hUU b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have pairR : ∀ (u : S.V) (s : Fin r → E) (t : Matrix (Fin r) (Fin r) E) (g : Fin r → S.V),
      S.hT u (∑ a, s a • ∑ c, t c a • g c) = ∑ a, s a * ∑ c, t c a * S.hT u (g c) := by
    intro u s t g
    simp [map_sum, smul_eq_mul]
  have pairL : ∀ (u : S.V) (s : Fin r → E) (t : Matrix (Fin r) (Fin r) E) (g : Fin r → S.V),
      S.hT (∑ a, s a • ∑ c, t c a • g c) u = ∑ a, star (s a) * ∑ c, star (t c a) * S.hT (g c) u := by
    intro u s t g
    simp [map_sum, LinearMap.sum_apply, smul_eq_mul, starRingEnd_apply]
  have hwe : ∀ (v : S.V) (c : Fin r), S.hT (wv e f v) (e c) = 0 := fun v c => by
    rw [← hsym, e_w e f hee hef c v, star_zero]
  have hwf : ∀ (v : S.V) (c : Fin r), S.hT (wv e f v) (f c) = 0 := fun v c => by
    rw [← hsym, f_w e f hff hef c v, star_zero]
  have hfe' := hfe e f hef
  have k1 : ∑ a, star (S.hT (f a) x) * ∑ c, star (U c a) * ∑ b, S.hT (e b) y * U' c b =
      ∑ a, star (S.hT (f a) x) * S.hT (e a) y :=
    algδ _ _ (fun c a => star (U c a)) U' hUU
  have k2 : ∑ a, star (S.hT (e a) x) * ∑ c, star (U' c a) * ∑ b, S.hT (f b) y * U c b =
      ∑ a, star (S.hT (e a) x) * S.hT (f a) y :=
    algδ _ _ (fun c a => star (U' c a)) U hUU'
  rw [psiF_eq, psiF_eq]
  simp only [map_add, LinearMap.add_apply]
  simp only [pairL]
  simp only [pairR]
  simp only [hwe, hwf, e_w e f hee hef, f_w e f hff hef, hee, hff, hef, hfe', mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  linear_combination k1 + k2

include hee hff hef in
/- English proof (translation)
Rewrite using `[gram e f hee hff hef U U' hUU x y]`. Establish `h1 : ∀ c, S.hT (wv e f x) (e c) = 0` using `fun c => by`. Rewrite using `[← hsym, e_w e f hee hef c x, star_zero]`. Establish `h2 : ∀ c, S.hT (wv e f x) (f c) = 0` using `fun c => by`. Rewrite using `[← hsym, f_w e f hff hef c x, star_zero]`.

Establish `h3 : S.hT (wv e f x) (wv e f y) = S.hT (wv e f x) y`. Rewrite using `[show wv e f y = y - ∑ a, S.hT (f a) y • e a - ∑ a, S.hT (e a) y • f a from rfl]`. Simplify using `[h1, h2]`. Establish `h4 : S.hT (wv e f x) y = S.hT x y - ∑ a, star (S.hT (f a) x) * S.hT (e a) y - ∑ a, star (S.hT (e a) x) * S.hT (f a) y`. Simplify using `[wv, LinearMap.sum_apply, smul_eq_mul, starRingEnd_apply]`.

Rewrite using `[h3, h4]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isom_psiF (U U' : Matrix (Fin r) (Fin r) E)
    (hUU : ∀ a b, ∑ c, star (U c a) * U' c b = if a = b then 1 else 0) (x y : S.V) :
    S.hT (psiF e f U U' x) (psiF e f U U' y) = S.hT x y := by
  rw [gram e f hee hff hef U U' hUU x y]
  have h1 : ∀ c, S.hT (wv e f x) (e c) = 0 := fun c => by
    rw [← hsym, e_w e f hee hef c x, star_zero]
  have h2 : ∀ c, S.hT (wv e f x) (f c) = 0 := fun c => by
    rw [← hsym, f_w e f hff hef c x, star_zero]
  have h3 : S.hT (wv e f x) (wv e f y) = S.hT (wv e f x) y := by
    rw [show wv e f y = y - ∑ a, S.hT (f a) y • e a - ∑ a, S.hT (e a) y • f a from rfl]
    simp [h1, h2]
  have h4 : S.hT (wv e f x) y = S.hT x y - ∑ a, star (S.hT (f a) x) * S.hT (e a) y -
      ∑ a, star (S.hT (e a) x) * S.hT (f a) y := by
    simp [wv, LinearMap.sum_apply, smul_eq_mul, starRingEnd_apply]
  rw [h3, h4]
  ring

include hef in
/- English proof (translation)
Rewrite using `[psiF_apply]`. Apply the tactic sequence `simp [hfe e f hef, hee] <;> abel`.
-/
theorem psiF_e (U U' : Matrix (Fin r) (Fin r) E) (hee : ∀ a b, S.hT (e a) (e b) = 0) (j : Fin r) :
    psiF e f U U' (e j) = ∑ c, U c j • e c := by
  rw [psiF_apply]
  simp [hfe e f hef, hee] <;> abel

/- English proof (translation)
Rewrite using `[psiF_apply]`. Simplify using `[h1, h2]`.
-/
theorem psiF_fix (U U' : Matrix (Fin r) (Fin r) E) (v : S.V) (h1 : ∀ a, S.hT (f a) v = 0)
    (h2 : ∀ a, S.hT (e a) v = 0) : psiF e f U U' v = v := by
  rw [psiF_apply]
  simp [h1, h2]

end Pair

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.gmap`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce `w hw`. Conclude with `hΛ w hw`.

Introduce `v hv`. Rewrite using `[Submodule.mem_map]`. Use `⟨n.symm v, ?_, by simp⟩` and prove the remaining obligations. Establish `hU' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ` using `hU`. Establish `h1 : v ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ` using `by rw [hU']; exact hv`.

Rewrite using `[← hU']`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars] at h1 ⊢`. Introduce `y hy`. Use `h1 (n y) (hΛ y hy)` as an intermediate fact. Rewrite using `[← hn y (n.symm v), LinearEquiv.apply_symm_apply]` and apply the resulting hypothesis.
-/
theorem gmap_of_isom (Λ : Submodule (𝓞 E) S.V) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (n : S.V ≃ₗ[E] S.V)
    (hn : ∀ x y, S.hT (n x) (n y) = S.hT x y) (hΛ : ∀ v ∈ Λ, n v ∈ Λ) : Formalism.HermitianLatticesTheory.gmap n Λ = Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro w hw
    exact hΛ w hw
  · intro v hv
    rw [Submodule.mem_map]
    refine ⟨n.symm v, ?_, by simp⟩
    have hU' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hU
    have h1 : v ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hU']; exact hv
    rw [← hU']
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.coe_restrictScalars] at h1 ⊢
    intro y hy
    have := h1 (n y) (hΛ y hy)
    rwa [← hn y (n.symm v), LinearEquiv.apply_symm_apply]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Apply `S.nondeg.1 x` to reduce the goal to its premises. Introduce `y`. Rewrite using `[← hg x y, hx]`.

Simplify using the standard rewrite rules.
-/
theorem inj_of_isom (g : S.V →ₗ[E] S.V) (hg : ∀ x y, S.hT (g x) (g y) = S.hT x y) : Function.Injective g := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply S.nondeg.1 x
  intro y
  rw [← hg x y, hx]
  simp

end PI.TermsAtPtFiniteW.LeviW
