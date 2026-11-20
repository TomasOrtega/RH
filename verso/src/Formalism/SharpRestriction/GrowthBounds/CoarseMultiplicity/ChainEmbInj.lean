import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LettersAtUpdate

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section NV

variable {K σ : Type} [Field K]

/- English proof (translation)
Introduce `h`. Break down `Finset.mem_union.1 (MvPolynomial.vars_mul F G h) with h' | h'` into its components or cases. Conclude with `h1 h'`. Conclude with `h2 h'`.
-/
theorem nv_mul {v : σ} {F G : MvPolynomial σ K} (h1 : v ∉ F.vars) (h2 : v ∉ G.vars) : v ∉ (F * G).vars := by
  classical
  intro h
  rcases Finset.mem_union.1 (MvPolynomial.vars_mul F G h) with h' | h'
  · exact h1 h'
  · exact h2 h'

/- English proof (translation)
Introduce `h`. Break down `Finset.mem_union.1 (MvPolynomial.vars_add_subset F G h) with h' | h'` into its components or cases. Conclude with `h1 h'`. Conclude with `h2 h'`.
-/
theorem nv_add {v : σ} {F G : MvPolynomial σ K} (h1 : v ∉ F.vars) (h2 : v ∉ G.vars) : v ∉ (F + G).vars := by
  classical
  intro h
  rcases Finset.mem_union.1 (MvPolynomial.vars_add_subset F G h) with h' | h'
  · exact h1 h'
  · exact h2 h'

/- English proof (translation)
Introduce `h`. Conclude with `h1 (MvPolynomial.vars_pow F n h)`.
-/
theorem nv_pow {v : σ} {F : MvPolynomial σ K} (h1 : v ∉ F.vars) (n : ℕ) : v ∉ (F ^ n).vars := by
  intro h
  exact h1 (MvPolynomial.vars_pow F n h)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [MvPolynomial.vars_one]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`. Conclude with `nv_mul (h1 a (Finset.mem_insert_self a s)) (ih fun i hi => h1 i (Finset.mem_insert_of_mem hi))`.
-/
theorem nv_prod {v : σ} {ι : Type} (s : Finset ι) {f : ι → MvPolynomial σ K} (h1 : ∀ i ∈ s, v ∉ (f i).vars) :
    v ∉ (∏ i ∈ s, f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MvPolynomial.vars_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact nv_mul (h1 a (Finset.mem_insert_self a s)) (ih fun i hi => h1 i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `nv_add (h1 a (Finset.mem_insert_self a s)) (ih fun i hi => h1 i (Finset.mem_insert_of_mem hi))`.
-/
theorem nv_sum {v : σ} {ι : Type} (s : Finset ι) {f : ι → MvPolynomial σ K} (h1 : ∀ i ∈ s, v ∉ (f i).vars) :
    v ∉ (∑ i ∈ s, f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact nv_add (h1 a (Finset.mem_insert_self a s)) (ih fun i hi => h1 i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Rewrite using `[MvPolynomial.vars_X, Finset.mem_singleton]`. Conclude with `h`.
-/
theorem nv_X {v u : σ} (h : v ≠ u) : v ∉ (X u : MvPolynomial σ K).vars := by
  classical
  rw [MvPolynomial.vars_X, Finset.mem_singleton]
  exact h

/- English proof (translation)
Introduce `hv`. Take `⟨x, _, hx⟩` from `Finset.mem_image.1 (MvPolynomial.vars_rename f y hv)`. Conclude with `h x hx`.
-/
theorem nv_rename {τ : Type} {v : σ} (f : τ → σ) (h : ∀ x, f x ≠ v) (y : MvPolynomial τ K) : v ∉ (rename f y).vars := by
  classical
  intro hv
  obtain ⟨x, _, hx⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename f y hv)
  exact h x hx

/- English proof (translation)
Proceed by induction on `y using MvPolynomial.induction_on' with`. Consider the case `monomial e c`. Rewrite using `[rename_monomial, cth_monomial, cth_monomial, rename_monomial, Finsupp.mapDomain_apply hf]`. Consider the case `add p q hp hq => rw [map_add, cth_add, cth_add, map_add, hp, hq]`.
-/
theorem cth_rename {τ : Type} (f : τ → σ) (hf : Function.Injective f) (x : τ) (n : ℕ) (y : MvPolynomial τ K) :
    cth (f x) n (rename f y) = rename f (cth x n y) := by
  induction y using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [rename_monomial, cth_monomial, cth_monomial, rename_monomial, Finsupp.mapDomain_apply hf]
  | add p q hp hq => rw [map_add, cth_add, cth_add, map_add, hp, hq]

/- English proof (translation)
Rewrite using `[X_pow_eq_monomial, cth_monomial, Finsupp.single_eq_same, one_mul, ← Nat.cast_smul_eq_nsmul K, smul_monomial, smul_eq_mul, mul_one]`.
-/
theorem cth_X_pow (v : σ) (b z : ℕ) : cth v b ((X v : MvPolynomial σ K) ^ z) = (z.choose b) • (X v : MvPolynomial σ K) ^ z := by
  rw [X_pow_eq_monomial, cth_monomial, Finsupp.single_eq_same, one_mul, ← Nat.cast_smul_eq_nsmul K,
    smul_monomial, smul_eq_mul, mul_one]

end NV

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

/- English proof (translation)
Introduce `a b h`. Simplify using `only [chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h`. Conclude with `Prod.ext (Fin.castSucc_injective _ h.1) h.2`.
-/
theorem chainEmb_inj (N r t : ℕ) : Function.Injective (chainEmb N r t) := by
  intro a b h
  simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
  exact Prod.ext (Fin.castSucc_injective _ h.1) h.2

/- English proof (translation)
Establish `e1 : finPos N (D.T.pos i) = Fin.castSucc (tieW hT i)`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [finPos, tieW, Fin.coe_castSucc]`. Conclude with `Nat.min_eq_left (by have := hT.lt i; omega)`. Establish `e2 : finPos N (D.T.pos i + 1) = Fin.castSucc (tieE hT i)`.

Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [finPos, tieE, Fin.coe_castSucc]`. Conclude with `Nat.min_eq_left (by have := hT.lt i; omega)`. Rewrite using `[BlockData.Ehat, e1, e2]`. Both sides reduce to the same expression.
-/
theorem Ehat_eq {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) :
    D.Ehat O (r := r) i = X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
      ∑ c, X (chainEmb N r D.T.t (tieW hT i, c)) * X (chainEmb N r D.T.t (tieE hT i, c)) := by
  have e1 : finPos N (D.T.pos i) = Fin.castSucc (tieW hT i) := by
    apply Fin.ext
    simp only [finPos, tieW, Fin.coe_castSucc]
    exact Nat.min_eq_left (by have := hT.lt i; omega)
  have e2 : finPos N (D.T.pos i + 1) = Fin.castSucc (tieE hT i) := by
    apply Fin.ext
    simp only [finPos, tieE, Fin.coe_castSucc]
    exact Nat.min_eq_left (by have := hT.lt i; omega)
  rw [BlockData.Ehat, e1, e2]
  rfl

def pairP (O : Type) [CommRing O] [IsDomain O] (r : ℕ) {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) :
    MvPolynomial (Fin N × Fin r) (KK O) :=
  ∑ c, X (tieW hT i, c) * X (tieE hT i, c)

/- English proof (translation)
Rewrite using `[Ehat_eq hT i]`. Simplify using `[pairP, map_sum, rename_X]`.
-/
theorem Ehat_eq' {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) :
    D.Ehat O (r := r) i = X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
      rename (chainEmb N r D.T.t) (pairP O r hT i) := by
  rw [Ehat_eq hT i]
  simp [pairP, map_sum, rename_X]

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [tieW, tieE] at this`. Conclude with `hT.sep i' i this.symm`.
-/
theorem tieW_ne_tieE {D : BlockData N} (hT : TieOK D) (i i' : Fin D.T.t) : tieW hT i ≠ tieE hT i' := by
  intro h
  have := congrArg Fin.val h
  simp only [tieW, tieE] at this
  exact hT.sep i' i this.symm

/- English proof (translation)
Rewrite using `[Ehat_eq hT i]`. Conclude with `nv_add (nv_mul (nv_X h1) (nv_X h2)) (nv_sum _ fun c _ => nv_mul (nv_X (h3 c)) (nv_X (h4 c)))`.
-/
theorem nv_Ehat {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) {v : BVar N r D.T.t}
    (h1 : v ≠ scalZ N r D.T.t (Fin.castSucc i)) (h2 : v ≠ scalS N r D.T.t (Fin.castSucc i))
    (h3 : ∀ c, v ≠ chainEmb N r D.T.t (tieW hT i, c)) (h4 : ∀ c, v ≠ chainEmb N r D.T.t (tieE hT i, c)) :
    v ∉ (D.Ehat O (r := r) i).vars := by
  rw [Ehat_eq hT i]
  exact nv_add (nv_mul (nv_X h1) (nv_X h2)) (nv_sum _ fun c _ => nv_mul (nv_X (h3 c)) (nv_X (h4 c)))

/- English proof (translation)
Unfold `BlockData.Eplus`. Conclude with `nv_add (nv_mul (nv_X h1) (nv_X h2)) (nv_sum _ fun c _ => nv_mul (nv_X (h3 c)) (nv_X (h4 c)))`.
-/
theorem nv_Eplus (D : BlockData N) {v : BVar N r D.T.t}
    (h1 : v ≠ scalZ N r D.T.t (Fin.last D.T.t)) (h2 : v ≠ scalS N r D.T.t (Fin.last D.T.t))
    (h3 : ∀ c, v ≠ Sum.inl (Fin.castSucc D.uPos, c)) (h4 : ∀ c, v ≠ xiVar N r D.T.t c) :
    v ∉ (D.Eplus O (r := r)).vars := by
  unfold BlockData.Eplus
  exact nv_add (nv_mul (nv_X h1) (nv_X h2)) (nv_sum _ fun c _ => nv_mul (nv_X (h3 c)) (nv_X (h4 c)))

/- English proof (translation)
Introduce `hv`. Take `⟨m, hm, hvm⟩` from `(MvPolynomial.mem_vars v).1 hv`. Establish `h1` using `(MvPolynomial.mem_restrictSupport_iff (KK O)).1 (Submodule.mem_inf.1 hg).1 hm`. Take `⟨c, hc⟩` from `h1.1 v hvm`. Conclude with `h c hc`.
-/
theorem nv_xi {t b : ℕ} {v : BVar N r t} (h : ∀ c, v ≠ xiVar N r t c) {g : MvPolynomial (BVar N r t) (KK O)}
    (hg : g ∈ XiPolZ O N r t b) : v ∉ g.vars := by
  intro hv
  obtain ⟨m, hm, hvm⟩ := (MvPolynomial.mem_vars v).1 hv
  have h1 := (MvPolynomial.mem_restrictSupport_iff (KK O)).1 (Submodule.mem_inf.1 hg).1 hm
  obtain ⟨c, hc⟩ := h1.1 v hvm
  exact h c hc

def OddV (D : BlockData N) : BVar N r D.T.t → Prop
  | Sum.inl (a, _) => a ≠ Fin.castSucc D.uPos ∧ a ≠ Fin.last N
  | Sum.inr (l, _) => l ≠ Fin.last D.T.t

/- English proof (translation)
Establish `hfree : ∀ F : MvPolynomial (BVar N r D.T.t) (KK O), chainEmb N r D.T.t (a0, c) ∉ F.vars → ∀ μ ∈ F.support, μ (chainEmb N r D.T.t (a0, c)) = 0`. Introduce `F h μ hμ`. Assume the negation of the conclusion as `hne`. Conclude with `h ((MvPolynomial.mem_vars _).2 ⟨μ, hμ, Finsupp.mem_support_iff.2 hne⟩)`. Establish `hE : chainEmb N r D.T.t (a0, c) ∉ (D.Eplus O (r` using `r)).vars := by`.

Use `nv_Eplus D ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using `[chainEmb, scalZ]`. Simplify using `[chainEmb, scalS]`. Introduce `c' h`. Simplify using `only [chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h`.

Conclude with `ha0 (Fin.castSucc_injective _ h.1)`. Introduce `c' h`. Simplify using `only [chainEmb, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h`. Conclude with `Fin.castSucc_ne_last _ h.1`. Establish `hP : chainEmb N r D.T.t (a0, c) ∉ (D.Eplus O (r` using `r) ^ jp * (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) * X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus : MvPolynomial (BVar N r D.T.t) (KK O)).vars := by`.

Use `nv_mul (nv_mul (nv_pow hE jp) (nv_prod _ fun i _ => nv_pow (nv_X ?_) _)) (nv_pow (nv_X ?_) _)` and prove the remaining obligations. Simplify using `[chainEmb, scalZ]`. Simplify using `[chainEmb, scalZ]`. Establish `hg' : chainEmb N r D.T.t (a0, c) ∉ g.vars`. Use `nv_xi (fun c' h => ?_) hg` and prove the remaining obligations.

Simplify using `only [chainEmb, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h`. Conclude with `Fin.castSucc_ne_last _ h.1`. Establish `key : ∀ Y : MvPolynomial (Fin N × Fin r) (KK O), tailP O r D jp Y g = (D.Eplus O (r` using `r) ^ jp * (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) * X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus) * (g * rename (chainEmb N r D.T.t) Y) := by`. Introduce `Y`. Unfold `tailP`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, key, cth_mul_free _ _ (hfree _ hP), cth_mul_free _ _ (hfree _ hg'), cth_rename _ (chainEmb_inj N r D.T.t)]`.
-/
theorem tail_chain (D : BlockData N) (jp : ℕ) (a0 : Fin N) (ha0 : a0 ≠ D.uPos) (c : Fin r) (b : ℕ)
    (y : MvPolynomial (Fin N × Fin r) (KK O)) {g : MvPolynomial (BVar N r D.T.t) (KK O)}
    (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp)) :
    cth (chainEmb N r D.T.t (a0, c)) b (tailP O r D jp y g) = tailP O r D jp (cth (a0, c) b y) g := by
  have hfree : ∀ F : MvPolynomial (BVar N r D.T.t) (KK O), chainEmb N r D.T.t (a0, c) ∉ F.vars →
      ∀ μ ∈ F.support, μ (chainEmb N r D.T.t (a0, c)) = 0 := by
    intro F h μ hμ
    by_contra hne
    exact h ((MvPolynomial.mem_vars _).2 ⟨μ, hμ, Finsupp.mem_support_iff.2 hne⟩)
  have hE : chainEmb N r D.T.t (a0, c) ∉ (D.Eplus O (r := r)).vars := by
    refine nv_Eplus D ?_ ?_ ?_ ?_
    · simp [chainEmb, scalZ]
    · simp [chainEmb, scalS]
    · intro c' h
      simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
      exact ha0 (Fin.castSucc_injective _ h.1)
    · intro c' h
      simp only [chainEmb, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
      exact Fin.castSucc_ne_last _ h.1
  have hP : chainEmb N r D.T.t (a0, c) ∉ (D.Eplus O (r := r) ^ jp *
      (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
      X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus : MvPolynomial (BVar N r D.T.t) (KK O)).vars := by
    refine nv_mul (nv_mul (nv_pow hE jp) (nv_prod _ fun i _ => nv_pow (nv_X ?_) _)) (nv_pow (nv_X ?_) _)
    · simp [chainEmb, scalZ]
    · simp [chainEmb, scalZ]
  have hg' : chainEmb N r D.T.t (a0, c) ∉ g.vars := by
    refine nv_xi (fun c' h => ?_) hg
    simp only [chainEmb, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
    exact Fin.castSucc_ne_last _ h.1
  have key : ∀ Y : MvPolynomial (Fin N × Fin r) (KK O), tailP O r D jp Y g =
      (D.Eplus O (r := r) ^ jp * (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
        X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus) * (g * rename (chainEmb N r D.T.t) Y) := by
    intro Y
    unfold tailP
    ring
  rw [key, key, cth_mul_free _ _ (hfree _ hP), cth_mul_free _ _ (hfree _ hg'),
    cth_rename _ (chainEmb_inj N r D.T.t)]

end GlobalTheory

end Formalism.MainNotions.ColumnSystems.Pf
