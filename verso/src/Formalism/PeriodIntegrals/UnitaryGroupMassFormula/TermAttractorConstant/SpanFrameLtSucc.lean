import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.LeadMinorEMulUpper

noncomputable section

open scoped Classical

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

def cg (g : S.V ≃ₗ[E] S.V) (Y : S.V →ₗ[E] S.V) : S.V →ₗ[E] S.V :=
  (g : S.V →ₗ[E] S.V) ∘ₗ Y ∘ₗ (g.symm : S.V →ₗ[E] S.V)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cg_apply (g : S.V ≃ₗ[E] S.V) (Y : S.V →ₗ[E] S.V) (v : S.V) : cg g Y v = g (Y (g.symm v)) := rfl

/- English proof (translation)
The claim follows from `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem sum_mem_X (F : FlagG S r T) (c : Fin r → E) :
    (∑ j, c j • F.e j) ∈ Submodule.span E (Set.range F.e) :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/- English proof (translation)
Unfold `FlagG.coefX`. Rewrite using `[dif_pos (sum_mem_X F c)]`. Rewrite using `[F.e_indep.repr_eq (l := Finsupp.equivFunOnFinite.symm c) (x := ⟨_, sum_mem_X F c⟩) (by simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype])]`. Simplify using the standard rewrite rules.
-/
theorem coefX_sum (F : FlagG S r T) (c : Fin r → E) (i : Fin r) : F.coefX (∑ j, c j • F.e j) i = c i := by
  unfold FlagG.coefX
  rw [dif_pos (sum_mem_X F c)]
  rw [F.e_indep.repr_eq (l := Finsupp.equivFunOnFinite.symm c) (x := ⟨_, sum_mem_X F c⟩)
    (by simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype])]
  simp

/- English proof (translation)
Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (R := E)).1 hv`. Establish `hw' : w ∈ Submodule.span E (F.e '' {j | j < i})` using `hw`. Take `⟨d, hd0, rfl⟩` from `exists_coeffs (S := S) F.e i w hw'`. Rewrite using `[← Finset.sum_add_distrib]`. Repeatedly rewrite using `[← add_smul]`.

Rewrite using `[coefX_sum, coefX_sum, hd0 i (lt_irrefl i), add_zero]`.
-/
theorem coefX_add_low (F : FlagG S r T) {v w : S.V} (hv : v ∈ F.X) (i : Fin r) (hw : w ∈ F.Xa i.1) :
    F.coefX (v + w) i = F.coefX v i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hv
  have hw' : w ∈ Submodule.span E (F.e '' {j | j < i}) := hw
  obtain ⟨d, hd0, rfl⟩ := exists_coeffs (S := S) F.e i w hw'
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_smul]
  rw [coefX_sum, coefX_sum, hd0 i (lt_irrefl i), add_zero]

/- English proof (translation)
Distinguish the cases in `hv : v ∈ Submodule.span E (Set.range F₁.e)`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (R := E)).1 hv`. Establish `: g (∑ j, c j • F₁.e j) = ∑ j, c j • F₂.e j` using `by simp [he, map_sum, map_smul]`. Rewrite using `[this, coefX_sum, coefX_sum]`. Establish `hgv : g v ∉ Submodule.span E (Set.range F₂.e)`.

Introduce `hm`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun (R := E)).1 hm`. Apply `hv` to reduce the goal to its premises. Establish `: v = ∑ j, c j • F₁.e j`. Apply `g.injective` to reduce the goal to its premises.

Rewrite using `[← hc]`. Simplify using `[he, map_sum, map_smul]`. Rewrite using `[this]`. Conclude with `sum_mem_X F₁ c`. Unfold `FlagG.coefX`.

Rewrite using `[dif_neg hgv, dif_neg hv]`.
-/
theorem coefX_transport (F₁ : FlagG S r T) (F₂ : FlagG S r T') (g : S.V ≃ₗ[E] S.V)
    (he : ∀ j, F₂.e j = g (F₁.e j)) (v : S.V) (i : Fin r) : F₂.coefX (g v) i = F₁.coefX v i := by
  by_cases hv : v ∈ Submodule.span E (Set.range F₁.e)
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hv
    have : g (∑ j, c j • F₁.e j) = ∑ j, c j • F₂.e j := by simp [he, map_sum, map_smul]
    rw [this, coefX_sum, coefX_sum]
  · have hgv : g v ∉ Submodule.span E (Set.range F₂.e) := by
      intro hm
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hm
      apply hv
      have : v = ∑ j, c j • F₁.e j := by
        apply g.injective
        rw [← hc]
        simp [he, map_sum, map_smul]
      rw [this]
      exact sum_mem_X F₁ c
    unfold FlagG.coefX
    rw [dif_neg hgv, dif_neg hv]

/- English proof (translation)
Establish `he : ∀ j, F₂.e j = g (F₁.e j)` using `fun j => by`. Use `hf (Fin.castSucc j)` as an intermediate fact. Simplify `this` using `[FlagG.fvec]`. Unfold `FlagG.ell`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[cg_apply, hf, LinearEquiv.symm_apply_apply]`. Conclude with `coefX_transport F₁ F₂ g he (Y (F₁.fvec i.succ)) i`.
-/
theorem ell_transport (F₁ : FlagG S r T) (F₂ : FlagG S r T') (g : S.V ≃ₗ[E] S.V)
    (hf : ∀ a, F₂.fvec a = g (F₁.fvec a)) (Y : S.V →ₗ[E] S.V) : F₂.ell (cg g Y) = F₁.ell Y := by
  have he : ∀ j, F₂.e j = g (F₁.e j) := fun j => by
    have := hf (Fin.castSucc j)
    simpa [FlagG.fvec] using this
  unfold FlagG.ell
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cg_apply, hf, LinearEquiv.symm_apply_apply]
  exact coefX_transport F₁ F₂ g he (Y (F₁.fvec i.succ)) i

/- English proof (translation)
Take `⟨hU, hfl, hp⟩` from `hY`. Establish `hU' : ∀ u v, S.hT (Y u) v + S.hT u (Y v) = 0` using `hU`. Establish `hp' : ∀ x, (∀ u ∈ F₁.X, S.hT u x = 0) → Y x ∈ F₁.X` using `fun x hx => hp x hx`. Use `show cg g Y ∈ LieU S ∧ (∀ a : ℕ, 1 ≤ a → a ≤ r → ∀ x ∈ F₂.Xa a, cg g Y x ∈ F₂.Xa (a - 1)) ∧ ∀ x ∈ perpS S F₂.X, cg g Y x ∈ F₂.X`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show ∀ u v, S.hT (cg g Y u) v + S.hT u (cg g Y v) = 0`. Introduce `u v`. Rewrite using `[cg_apply, cg_apply]`. Establish `e1` using `hg (Y (g.symm u)) (g.symm v)`. Establish `e2` using `hg (g.symm u) (Y (g.symm v))`.

Rewrite `e1`, `e2` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[e1, e2]`. Conclude with `hU' _ _`. Introduce `a h1 h2 v hv`. Rewrite using `[hXa, cg_apply, LinearEquiv.symm_apply_apply]`.

Conclude with `hfl a h1 h2 _ ((hXa a v).1 hv)`. Introduce `v hv`. Establish `hv' : ∀ u ∈ F₂.X, S.hT u v = 0` using `hv`. Rewrite using `[hX, cg_apply, LinearEquiv.symm_apply_apply]`. Use `hp' _ fun u hu => ?_` and prove the remaining obligations.

Establish `h1` using `hv' (g u) ((hX (g u)).2 (by simpa using hu))`. Rewrite using `[← hg u (g.symm v), LinearEquiv.apply_symm_apply]`. Conclude with `h1`.
-/
theorem lieN_transport (F₁ : FlagG S r T) (F₂ : FlagG S r T') (g : S.V ≃ₗ[E] S.V)
    (hg : ∀ u v, S.hT (g u) (g v) = S.hT u v)
    (hXa : ∀ a v, v ∈ F₂.Xa a ↔ g.symm v ∈ F₁.Xa a) (hX : ∀ v, v ∈ F₂.X ↔ g.symm v ∈ F₁.X)
    {Y : S.V →ₗ[E] S.V} (hY : Y ∈ F₁.LieN) : cg g Y ∈ F₂.LieN := by
  obtain ⟨hU, hfl, hp⟩ := hY
  have hU' : ∀ u v, S.hT (Y u) v + S.hT u (Y v) = 0 := hU
  have hp' : ∀ x, (∀ u ∈ F₁.X, S.hT u x = 0) → Y x ∈ F₁.X := fun x hx => hp x hx
  show cg g Y ∈ LieU S ∧ (∀ a : ℕ, 1 ≤ a → a ≤ r → ∀ x ∈ F₂.Xa a, cg g Y x ∈ F₂.Xa (a - 1)) ∧
    ∀ x ∈ perpS S F₂.X, cg g Y x ∈ F₂.X
  refine ⟨?_, ?_, ?_⟩
  · show ∀ u v, S.hT (cg g Y u) v + S.hT u (cg g Y v) = 0
    intro u v
    rw [cg_apply, cg_apply]
    have e1 := hg (Y (g.symm u)) (g.symm v)
    have e2 := hg (g.symm u) (Y (g.symm v))
    rw [LinearEquiv.apply_symm_apply] at e1 e2
    rw [e1, e2]
    exact hU' _ _
  · intro a h1 h2 v hv
    rw [hXa, cg_apply, LinearEquiv.symm_apply_apply]
    exact hfl a h1 h2 _ ((hXa a v).1 hv)
  · intro v hv
    have hv' : ∀ u ∈ F₂.X, S.hT u v = 0 := hv
    rw [hX, cg_apply, LinearEquiv.symm_apply_apply]
    refine hp' _ fun u hu => ?_
    have h1 := hv' (g u) ((hX (g u)).2 (by simpa using hu))
    rw [← hg u (g.symm v), LinearEquiv.apply_symm_apply]
    exact h1

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun hv => symm_mem_of_maps n U h v hv, fun hv => by simpa using h _ hv⟩`.
-/
theorem maps_iff {U : Submodule E S.V} (n : S.V ≃ₗ[E] S.V) (h : ∀ x ∈ U, n x ∈ U) (v : S.V) :
    v ∈ U ↔ n.symm v ∈ U :=
  ⟨fun hv => symm_mem_of_maps n U h v hv, fun hv => by simpa using h _ hv⟩

/- English proof (translation)
Simplify using `[FlagG.Xa]`.
-/
theorem Xa_zero (F : FlagG S r T) : F.Xa 0 = ⊥ := by
  simp [FlagG.Xa]

/- English proof (translation)
Consider the cases of `a with`. Consider the case `zero`. Introduce `x hx`. Rewrite `hx`, the goal using `[Xa_zero]`. Rewrite using `[(Submodule.mem_bot E).1 hx, map_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `succ j => exact nlam_maps_Xflag hn j`.
-/
theorem nlam_maps_Xa (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F)
    (a : ℕ) : ∀ x ∈ F.fl.Xa a, n x ∈ F.fl.Xa a := by
  cases a with
  | zero =>
    intro x hx
    rw [Xa_zero] at hx ⊢
    rw [(Submodule.mem_bot E).1 hx, map_zero]
    exact Submodule.zero_mem _
  | succ j => exact nlam_maps_Xflag hn j

/- English proof (translation)
The claim follows from `lieN_transport F.fl F.fl n (isom_app hn.1.1) (fun a v => maps_iff n (nlam_maps_Xa Λ hn a) v) (fun v => maps_iff n (nlam_maps_X hn) v) hY`.
-/
theorem lieN_conj_nlam (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) {Y : S.V →ₗ[E] S.V} (hY : Y ∈ F.fl.LieN) : cg n Y ∈ F.fl.LieN :=
  lieN_transport F.fl F.fl n (isom_app hn.1.1) (fun a v => maps_iff n (nlam_maps_Xa Λ hn a) v)
    (fun v => maps_iff n (nlam_maps_X hn) v) hY

/- English proof (translation)
Use `show ∀ x ∈ F.X, S.hT x F.z = 0`. Introduce `x hx`. Simplify using `only [Formalism.MainNotions.S.FlagG.X] at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨i, rfl⟩` from `hy`. Conclude with `F.z_orth i`. Consider the case `zero => simp`. Consider the case `add y y' _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]`. Consider the case `smul c y _ h => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h, smul_zero]`.
-/
theorem z_mem_perp (F : FlagG S r T) : F.z ∈ perpS S F.X := by
  show ∀ x ∈ F.X, S.hT x F.z = 0
  intro x hx
  dsimp only [Formalism.MainNotions.S.FlagG.X] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact F.z_orth i
  | zero => simp
  | add y y' _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
  | smul c y _ h => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h, smul_zero]

/- English proof (translation)
Simplify using `only [Formalism.MainNotions.S.FlagG.X, Formalism.MainNotions.S.FlagG.Xa]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `⟨j, j.2, rfl⟩`.
-/
theorem X_le_Xa_r (F : FlagG S r T) : F.X ≤ F.Xa r := by
  dsimp only [Formalism.MainNotions.S.FlagG.X, Formalism.MainNotions.S.FlagG.Xa]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  exact ⟨j, j.2, rfl⟩

/- English proof (translation)
Distinguish the cases in `hi : i.1 + 1 < r`. Set `j : Fin r` to `⟨i.1 + 1, hi⟩`. Establish `hs : i.succ = Fin.castSucc j` using `Fin.ext rfl`. Establish `hf : F.fvec i.succ = F.e j` using `by rw [hs]; simp [FlagG.fvec]`. Rewrite using `[hf]`.

Establish `hj : F.e j ∈ F.Xa (i.1 + 2)` using `Submodule.subset_span ⟨j, (show j.1 < i.1 + 2 by simp [j]), rfl⟩`. Establish `h` using `hY.2.1 (i.1 + 2) (by omega) (by omega) (F.e j) hj`. Simplify using `using h`. Establish `hr : i.1 + 1 = r` using `by omega`. Establish `hs : i.succ = Fin.last r` using `Fin.ext (by simp; omega)`.

Establish `hf : F.fvec i.succ = F.z` using `by rw [hs]; simp [FlagG.fvec]`. Rewrite using `[hf, hr]`. Conclude with `X_le_Xa_r F (hY.2.2 _ (z_mem_perp F))`.
-/
theorem Yf_mem (F : FlagG S r T) {Y : S.V →ₗ[E] S.V} (hY : Y ∈ F.LieN) (i : Fin r) :
    Y (F.fvec i.succ) ∈ F.Xa (i.1 + 1) := by
  by_cases hi : i.1 + 1 < r
  · let j : Fin r := ⟨i.1 + 1, hi⟩
    have hs : i.succ = Fin.castSucc j := Fin.ext rfl
    have hf : F.fvec i.succ = F.e j := by rw [hs]; simp [FlagG.fvec]
    rw [hf]
    have hj : F.e j ∈ F.Xa (i.1 + 2) := Submodule.subset_span ⟨j, (show j.1 < i.1 + 2 by simp [j]), rfl⟩
    have h := hY.2.1 (i.1 + 2) (by omega) (by omega) (F.e j) hj
    simpa using h
  · have hr : i.1 + 1 = r := by omega
    have hs : i.succ = Fin.last r := Fin.ext (by simp; omega)
    have hf : F.fvec i.succ = F.z := by rw [hs]; simp [FlagG.fvec]
    rw [hf, hr]
    exact X_le_Xa_r F (hY.2.2 _ (z_mem_perp F))

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Establish `hc' : c.1 < i.1 + 1`. Use `Fin.lt_def.1 hc` as an intermediate fact. Simplify using `using this`.

Establish `hcr : c.1 < r` using `by omega`. Establish `hce : c = Fin.castSucc ⟨c.1, hcr⟩` using `Fin.ext rfl`. Rewrite using `[hce, frame_castSucc]`. Conclude with `Submodule.subset_span ⟨⟨c.1, hcr⟩, hc', rfl⟩`.
-/
theorem span_frame_lt_succ (F : LFlag S r T) (i : Fin r) :
    Submodule.span E (frame F '' {c | c < i.succ}) ≤ F.fl.Xa (i.1 + 1) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, hc, rfl⟩
  have hc' : c.1 < i.1 + 1 := by
    have := Fin.lt_def.1 hc
    simpa using this
  have hcr : c.1 < r := by omega
  have hce : c = Fin.castSucc ⟨c.1, hcr⟩ := Fin.ext rfl
  rw [hce, frame_castSucc]
  exact Submodule.subset_span ⟨⟨c.1, hcr⟩, hc', rfl⟩

/- English proof (translation)
Unfold `FlagG.ell`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hni : n.symm ∈ NLam Λ F` using `nlam_inv hn`. Establish `hu : n.symm (frame F i.succ) - frame F i.succ ∈ F.fl.Xa (i.1 + 1)` using `span_frame_lt_succ F i (nlam_frame Λ hni i.succ)`. Establish `hYf : Y (frame F i.succ) ∈ F.fl.Xa (i.1 + 1)` using `Yf_mem F.fl hY i`.

Use `set v := Y (n.symm (frame F i.succ)) with hvdef`. Establish `hYu : v - Y (frame F i.succ) ∈ F.fl.Xa i.1`. Establish `h` using `hY.2.1 (i.1 + 1) (by omega) (by omega) _ hu`. Rewrite `h` using `[map_sub]`. Simplify using `using h`.

Establish `hvmem : v ∈ F.fl.Xa (i.1 + 1)`. Use `Submodule.add_mem _ hYf (Xflag_mono F i.1 hYu)` as an intermediate fact. Simplify using `using this`. Establish `hnv : n v - v ∈ F.fl.Xa i.1` using `hn.2.1 i.1 _ hvmem`. Establish `key : n v = Y (frame F i.succ) + ((v - Y (frame F i.succ)) + (n v - v))` using `by abel`.

Use `show F.fl.coefX (n v) i = F.fl.coefX (Y (frame F i.succ)) i`. Rewrite using `[key]`. Conclude with `coefX_add_low F.fl (Xflag_le_X F _ hYf) i (Submodule.add_mem _ hYu hnv)`.
-/
theorem ell_conj_nlam (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) {Y : S.V →ₗ[E] S.V} (hY : Y ∈ F.fl.LieN) : F.fl.ell (cg n Y) = F.fl.ell Y := by
  unfold FlagG.ell
  refine Finset.sum_congr rfl fun i _ => ?_
  have hni : n.symm ∈ NLam Λ F := nlam_inv hn
  have hu : n.symm (frame F i.succ) - frame F i.succ ∈ F.fl.Xa (i.1 + 1) :=
    span_frame_lt_succ F i (nlam_frame Λ hni i.succ)
  have hYf : Y (frame F i.succ) ∈ F.fl.Xa (i.1 + 1) := Yf_mem F.fl hY i
  set v := Y (n.symm (frame F i.succ)) with hvdef
  have hYu : v - Y (frame F i.succ) ∈ F.fl.Xa i.1 := by
    have h := hY.2.1 (i.1 + 1) (by omega) (by omega) _ hu
    rw [map_sub] at h
    simpa using h
  have hvmem : v ∈ F.fl.Xa (i.1 + 1) := by
    have := Submodule.add_mem _ hYf (Xflag_mono F i.1 hYu)
    simpa using this
  have hnv : n v - v ∈ F.fl.Xa i.1 := hn.2.1 i.1 _ hvmem
  have key : n v = Y (frame F i.succ) + ((v - Y (frame F i.succ)) + (n v - v)) := by abel
  show F.fl.coefX (n v) i = F.fl.coefX (Y (frame F i.succ)) i
  rw [key]
  exact coefX_add_low F.fl (Xflag_le_X F _ hYf) i (Submodule.add_mem _ hYu hnv)

/- English proof (translation)
Introduce `Y hY`. Take `⟨hYF, hYy⟩` from `hY`. Take `⟨n, hn, m, hm, hfr, -⟩` from `h`. Set `g : S.V ≃ₗ[E] S.V` to `m.trans n`. Establish `hfr' : ∀ a, frame y a = g (frame x a)` using `fun a => hfr a`.

Establish `hgi : ∀ u v, S.hT (g.symm.symm u) (g.symm.symm v) = S.hT u v`. Introduce `u v`. Rewrite using `[LinearEquiv.symm_symm]`. Use `show S.hT (n (m u)) (n (m v)) = S.hT u v`. Rewrite using `[isom_app hn.1.1, isom_app hm.1.1]`.

Establish `hgs : ∀ u v, S.hT (g.symm u) (g.symm v) = S.hT u v`. Introduce `u v`. Use `hgi (g.symm u) (g.symm v)` as an intermediate fact. Rewrite `this` using `[LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Conclude with `this.symm`.

Establish `hni : n.symm ∈ NLam Λ F` using `nlam_inv hn`. Establish `hY1F` using `lieN_conj_nlam Λ hni hYF`. Establish `hY1e` using `ell_conj_nlam Λ hni hYF`. Establish `hXa : ∀ a v, v ∈ x.fl.Xa a ↔ g.symm.symm v ∈ y.fl.Xa a`. Introduce `a v`.

Rewrite using `[LinearEquiv.symm_symm]`. Conclude with `⟨fun hv => (Xflag_mem_transport hfr' a (g v)).2 (by simpa using hv), fun hv => by simpa using (Xflag_mem_transport hfr' a (g v)).1 hv⟩`. Establish `hX : ∀ v, v ∈ x.fl.X ↔ g.symm.symm v ∈ y.fl.X`. Introduce `v`. Rewrite using `[LinearEquiv.symm_symm]`.

Conclude with `⟨fun hv => (Xsp_mem_transport hfr' (g v)).2 (by simpa using hv), fun hv => by simpa using (Xsp_mem_transport hfr' (g v)).1 hv⟩`. Establish `hY2 : cg g.symm Y ∈ x.fl.LieN` using `lieN_transport y.fl x.fl g.symm hgs hXa hX hYy`. Establish `hY2e : x.fl.ell (cg g.symm Y) = y.fl.ell Y`. Use `ell_transport y.fl x.fl g.symm (fun a => ?_) Y` and prove the remaining obligations. Use `hfr' a` as an intermediate fact.

Simplify using `only [frame] at this`. Rewrite using `[this, LinearEquiv.symm_apply_apply]`. Establish `hc : cg m (cg g.symm Y) = cg n.symm Y`. Use extensionality with `v`. Simplify using `only [cg_apply, LinearEquiv.symm_symm]`.

Use `show m (m.symm (n.symm (Y (n (m (m.symm v)))))) = n.symm (Y (n v))`. Rewrite using `[LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Establish `hY1x : cg n.symm Y ∈ x.fl.LieN` using `hc ▸ lieN_conj_nlam Λ hm hY2`. Establish `hY1xe : x.fl.ell (cg n.symm Y) = x.fl.ell (cg g.symm Y)`. Rewrite using `[← hc]`.

Conclude with `ell_conj_nlam Λ hm hY2`. Establish `key` using `hx (cg n.symm Y) ⟨hY1F, hY1x⟩`. Unfold `FlagG.dpsi at key ⊢`. Rewrite using `[← hY1e, key, hY1xe, hY2e]`.
-/
theorem rel_fwd (K : Type) [Field K] [Algebra K E] (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T}
    {x y : LFlag S r T'} (h : DCRel Λ F x y) (hx : Relevant K F.fl x.fl) : Relevant K F.fl y.fl := by
  intro Y hY
  obtain ⟨hYF, hYy⟩ := hY
  obtain ⟨n, hn, m, hm, hfr, -⟩ := h
  let g : S.V ≃ₗ[E] S.V := m.trans n
  have hfr' : ∀ a, frame y a = g (frame x a) := fun a => hfr a
  have hgi : ∀ u v, S.hT (g.symm.symm u) (g.symm.symm v) = S.hT u v := by
    intro u v
    rw [LinearEquiv.symm_symm]
    show S.hT (n (m u)) (n (m v)) = S.hT u v
    rw [isom_app hn.1.1, isom_app hm.1.1]
  have hgs : ∀ u v, S.hT (g.symm u) (g.symm v) = S.hT u v := by
    intro u v
    have := hgi (g.symm u) (g.symm v)
    rw [LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have hni : n.symm ∈ NLam Λ F := nlam_inv hn
  have hY1F := lieN_conj_nlam Λ hni hYF
  have hY1e := ell_conj_nlam Λ hni hYF
  have hXa : ∀ a v, v ∈ x.fl.Xa a ↔ g.symm.symm v ∈ y.fl.Xa a := by
    intro a v
    rw [LinearEquiv.symm_symm]
    exact ⟨fun hv => (Xflag_mem_transport hfr' a (g v)).2 (by simpa using hv),
      fun hv => by simpa using (Xflag_mem_transport hfr' a (g v)).1 hv⟩
  have hX : ∀ v, v ∈ x.fl.X ↔ g.symm.symm v ∈ y.fl.X := by
    intro v
    rw [LinearEquiv.symm_symm]
    exact ⟨fun hv => (Xsp_mem_transport hfr' (g v)).2 (by simpa using hv),
      fun hv => by simpa using (Xsp_mem_transport hfr' (g v)).1 hv⟩
  have hY2 : cg g.symm Y ∈ x.fl.LieN := lieN_transport y.fl x.fl g.symm hgs hXa hX hYy
  have hY2e : x.fl.ell (cg g.symm Y) = y.fl.ell Y := by
    refine ell_transport y.fl x.fl g.symm (fun a => ?_) Y
    have := hfr' a
    simp only [frame] at this
    rw [this, LinearEquiv.symm_apply_apply]
  have hc : cg m (cg g.symm Y) = cg n.symm Y := by
    ext v
    simp only [cg_apply, LinearEquiv.symm_symm]
    show m (m.symm (n.symm (Y (n (m (m.symm v)))))) = n.symm (Y (n v))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hY1x : cg n.symm Y ∈ x.fl.LieN := hc ▸ lieN_conj_nlam Λ hm hY2
  have hY1xe : x.fl.ell (cg n.symm Y) = x.fl.ell (cg g.symm Y) := by
    rw [← hc]
    exact ell_conj_nlam Λ hm hY2
  have key := hx (cg n.symm Y) ⟨hY1F, hY1x⟩
  unfold FlagG.dpsi at key ⊢
  rw [← hY1e, key, hY1xe, hY2e]

/- English proof (translation)
Introduce `x y h`. Establish `h' : DCRel Λ F x.1 y.1` using `h`. Establish `hs : DCRel Λ F y.1 x.1` using `(dCRelEquivAll_holds E S r T T' Λ F).symm h'`. Conclude with `⟨rel_fwd K Λ h', rel_fwd K Λ hs⟩`.
-/
theorem relFun_all (K : Type) [Field K] [Algebra K E] (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T)
    (P : LFlag S r T' → Prop) : RelFun Λ F P K := by
  intro x y h
  have h' : DCRel Λ F x.1 y.1 := h
  have hs : DCRel Λ F y.1 x.1 := (dCRelEquivAll_holds E S r T T' Λ F).symm h'
  exact ⟨rel_fwd K Λ h', rel_fwd K Λ hs⟩

end Gen

end PI.TermAttrConst.UnitaryGroupMassFormula
