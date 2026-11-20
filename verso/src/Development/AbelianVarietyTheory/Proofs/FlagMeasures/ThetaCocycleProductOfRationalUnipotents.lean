import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeSpanEInfToO
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DcosetCompl

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

/- English proof (translation)
Simplify using `[orth, Submodule.mem_iInf, LinearMap.mem_ker]`.
-/
theorem mem_orth_iff (U : Submodule E S.V) (v : S.V) : v ∈ orth S U ↔ ∀ y ∈ U, S.hT y v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
Introduce `v hv`. Rewrite `hv`, the goal using `[mem_orth_iff]`. Conclude with `fun y hy => hv y (h hy)`.
-/
theorem orth_anti {U U' : Submodule E S.V} (h : U ≤ U') : orth S U' ≤ orth S U := by
  intro v hv
  rw [mem_orth_iff] at hv ⊢
  exact fun y hy => hv y (h hy)

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SpanInfDenominators.le_spanE_inf_toO`. Consider the case `exact _root_.GlobalTheory.SpanInfDenominators.le_spanE_inf_toO`. Consider the case `(apply _root_.GlobalTheory.SpanInfDenominators.le_spanE_inf_toO <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SpanInfDenominators.le_spanE_inf_toO <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SpanInfDenominators.le_spanE_inf_toO <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SpanInfDenominators.le_spanE_inf_toO ..)`.
-/
theorem le_spanE_inf (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (U : Submodule E S.V) :
    U ≤ spanE S (Λ ⊓ toO S U) := by
  first
  | exact @_root_.GlobalTheory.SpanInfDenominators.le_spanE_inf_toO
  | exact _root_.GlobalTheory.SpanInfDenominators.le_spanE_inf_toO
  | (apply _root_.GlobalTheory.SpanInfDenominators.le_spanE_inf_toO <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanInfDenominators.le_spanE_inf_toO <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanInfDenominators.le_spanE_inf_toO <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanInfDenominators.le_spanE_inf_toO ..)

end Gen

end GlobalTheory.DcosetCompl

namespace GlobalTheory.DcosetCompl

section Flags

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

/- English proof (translation)
Unfold `Formalism.MainNotions.S.FlagG.Xa Formalism.MainNotions.S.FlagG.X`. Use `congr 1`. Use extensionality with `v`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, _, rfl⟩`. Conclude with `⟨i, rfl⟩`. Introduce and unpack `⟨i, rfl⟩`. Conclude with `⟨i, lt_of_lt_of_le i.2 hj, rfl⟩`.
-/
theorem xa_eq_x_of_le {T : E} (F : Formalism.MainNotions.S.FlagG S r T) {j : ℕ} (hj : r ≤ j) : F.Xa j = F.X := by
  unfold Formalism.MainNotions.S.FlagG.Xa Formalism.MainNotions.S.FlagG.X
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, lt_of_lt_of_le i.2 hj, rfl⟩

/- English proof (translation)
Rewrite using `[mem_orth_iff]`. Introduce `y hy`. Establish `: F.X ≤ LinearMap.ker (S.hT.flip F.z)`. Unfold `Formalism.MainNotions.S.FlagG.X`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Simplify using `[F.z_orth i]`. Simplify using `using this hy`.
-/
theorem z_mem_orth {T : E} (F : Formalism.MainNotions.S.FlagG S r T) : F.z ∈ orth S F.X := by
  rw [mem_orth_iff]
  intro y hy
  have : F.X ≤ LinearMap.ker (S.hT.flip F.z) := by
    unfold Formalism.MainNotions.S.FlagG.X
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [F.z_orth i]
  simpa using this hy

/- English proof (translation)
Establish `hle : X.map (g : S.V →ₗ[E] S.V) ≤ X`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `X.add_mem (h x hx) hx` as an intermediate fact. Simplify using `using this`. Conclude with `Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq g X)`.
-/
theorem map_eq_of_sub_mem (g : S.V ≃ₗ[E] S.V) (X : Submodule E S.V) (h : ∀ x ∈ X, g x - x ∈ X) :
    X.map (g : S.V →ₗ[E] S.V) = X := by
  have hle : X.map (g : S.V →ₗ[E] S.V) ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    have := X.add_mem (h x hx) hx
    simpa using this
  exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq g X)

end Flags

end GlobalTheory.DcosetCompl

namespace GlobalTheory.DcosetCompl

section Main

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

/- English proof (translation)
Establish `hUU : UU Λ F F' = XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} ⊔ XLam Λ F' ⊔ Submodule.span (𝓞 E) {F'.zt}` using `rfl`. Establish `h1 : XLam Λ F ≤ UU Λ F F'`. Rewrite using `[hUU]`. Conclude with `le_sup_left.trans (le_sup_left.trans le_sup_left)`. Establish `h2 : XLam Λ F' ≤ UU Λ F F'`.

Rewrite using `[hUU]`. Conclude with `le_sup_right.trans le_sup_left`. Establish `h3 : F.zt ∈ UU Λ F F'`. Rewrite using `[hUU]`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))`.

Establish `h4 : F'.zt ∈ UU Λ F F'`. Rewrite using `[hUU]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Establish `hs1 : spanE S (XLam Λ F) ≤ UUE Λ F F'` using `Submodule.span_mono (fun x hx => h1 hx)`. Establish `hs2 : spanE S (XLam Λ F') ≤ UUE Λ F F'` using `Submodule.span_mono (fun x hx => h2 hx)`.

Establish `hl1 : Xsp F ≤ spanE S (XLam Λ F)` using `le_spanE_inf Λ hΛ _`. Establish `hl2 : Xsp F' ≤ spanE S (XLam Λ F')` using `le_spanE_inf Λ hΛ _`. Conclude with `⟨hl1.trans hs1, hl2.trans hs2, Submodule.subset_span h3, Submodule.subset_span h4⟩`.
-/
theorem sub_le_uue {T T' : E} (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') :
    Xsp F ≤ UUE Λ F F' ∧ Xsp F' ≤ UUE Λ F F' ∧ F.zt ∈ UUE Λ F F' ∧ F'.zt ∈ UUE Λ F F' := by
  have hUU : UU Λ F F' = XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} ⊔ XLam Λ F' ⊔ Submodule.span (𝓞 E) {F'.zt} := rfl
  have h1 : XLam Λ F ≤ UU Λ F F' := by
    rw [hUU]; exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  have h2 : XLam Λ F' ≤ UU Λ F F' := by
    rw [hUU]; exact le_sup_right.trans le_sup_left
  have h3 : F.zt ∈ UU Λ F F' := by
    rw [hUU]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  have h4 : F'.zt ∈ UU Λ F F' := by
    rw [hUU]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hs1 : spanE S (XLam Λ F) ≤ UUE Λ F F' := Submodule.span_mono (fun x hx => h1 hx)
  have hs2 : spanE S (XLam Λ F') ≤ UUE Λ F F' := Submodule.span_mono (fun x hx => h2 hx)
  have hl1 : Xsp F ≤ spanE S (XLam Λ F) := le_spanE_inf Λ hΛ _
  have hl2 : Xsp F' ≤ spanE S (XLam Λ F') := le_spanE_inf Λ hΛ _
  exact ⟨hl1.trans hs1, hl2.trans hs2, Submodule.subset_span h3, Submodule.subset_span h4⟩

/- English proof (translation)
Unfold `UUE spanE`. Rewrite using `[Submodule.span_le]`. Establish `: UU Λ F F'' ≤ M.restrictScalars (𝓞 E)`. Use `sup_le (sup_le (sup_le ?_ ?_) ?_) ?_` and prove the remaining obligations. Conclude with `fun x hx => hX hx.2`.

Conclude with `Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (by rw [hz]; exact hzM))`. Conclude with `fun x hx => hX'' hx.2`. Conclude with `Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (by rw [hz'']; exact hz''M))`. Conclude with `fun v hv => this hv`.
-/
theorem uue_le {T T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F'' : LFlag S r T')
    (hz : F.zt = F.fl.z) (hz'' : F''.zt = F''.fl.z) (M : Submodule E S.V)
    (hX : Xsp F ≤ M) (hX'' : Xsp F'' ≤ M) (hzM : F.fl.z ∈ M) (hz''M : F''.fl.z ∈ M) :
    UUE Λ F F'' ≤ M := by
  unfold UUE spanE
  rw [Submodule.span_le]
  have : UU Λ F F'' ≤ M.restrictScalars (𝓞 E) := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact fun x hx => hX hx.2
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (by rw [hz]; exact hzM))
    · exact fun x hx => hX'' hx.2
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (by rw [hz'']; exact hz''M))
  exact fun v hv => this hv

/- English proof (translation)
Take `⟨hXU, hX'U, hzU, hz'U⟩` from `sub_le_uue Λ hΛ F F'`. Rewrite `hzU` using `[hz]`. Rewrite `hz'U` using `[hz']`. Establish `hcomp : ((n * m : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) = (n : S.V →ₗ[E] S.V).comp (m : S.V →ₗ[E] S.V)`. Use extensionality with `x`.

Both sides reduce to the same expression. Establish `he : ∀ i, F''.fl.e i = n (m (F'.fl.e i))`. Introduce `i`. Use `hfr (Fin.castSucc i)` as an intermediate fact. Simplify `this` using `[frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]`.

Establish `hzz : F''.fl.z = n (m F'.fl.z)`. Use `hfr (Fin.last r)` as an intermediate fact. Simplify `this` using `[frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]`. Establish `hmX' : (Xsp F').map (m : S.V →ₗ[E] S.V) = Xsp F'` using `map_eq_of_sub_mem m _ hmX`. Establish `hnXF : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp F` using `map_eq_of_sub_mem n _ hnX`.

Establish `hX'' : Xsp F'' = (Xsp F').map (n : S.V →ₗ[E] S.V)`. Establish `h0 : Xsp F'' = (Xsp F').map ((n * m : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V)` using `by show F''.fl.X = F'.fl.X.map _`. Unfold `Formalism.MainNotions.S.FlagG.X`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Establish `hfun : F''.fl.e = (((n * m : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) ∘ F'.fl.e)` using `funext fun i => he i`.

Rewrite using `[hfun]`. Rewrite using `[h0, hcomp, Submodule.map_comp, hmX']`. Establish `hUle : UUE Λ F F'' ≤ (UUE Λ F F').map (n : S.V →ₗ[E] S.V)`. Use `uue_le Λ F F'' hz hz'' _ ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← hnXF]`.

Conclude with `Submodule.map_mono hXU`. Rewrite using `[hX'']`. Conclude with `Submodule.map_mono hX'U`. Establish `h1 : n F.fl.z ∈ (UUE Λ F F').map (n : S.V →ₗ[E] S.V)` using `Submodule.mem_map_of_mem hzU`. Establish `h2 : n F.fl.z - F.fl.z ∈ (UUE Λ F F').map (n : S.V →ₗ[E] S.V)`.

Establish `h3` using `hnP _ (z_mem_orth F.fl)`. Rewrite `h3` using `[← hnXF]`. Conclude with `Submodule.map_mono hXU h3`. Use `Submodule.sub_mem _ h1 h2` as an intermediate fact. Simplify using `using this`.

Rewrite using `[hzz]`. Apply `Submodule.mem_map_of_mem` to reduce the goal to its premises. Establish `hm1 : m F'.fl.z - F'.fl.z ∈ UUE Λ F F'` using `hX'U (hmP _ (z_mem_orth F'.fl))`. Use `Submodule.add_mem _ hm1 hz'U` as an intermediate fact. Simplify using `using this`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Th, Submodule.map_le_iff_le_comap]`. Introduce and unpack `⟨a, b⟩ hp`. Conclude with `hp.1.1.1`. Introduce `x hx`.

Establish `hxP : x ∈ orth S (Xsp F)` using `orth_anti hXU hx`. Establish `hxP' : x ∈ orth S (Xsp F')` using `orth_anti hX'U hx`. Use `⟨(x, n x), ⟨⟨⟨hx, ?_⟩, ?_⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Use `show n x ∈ orth S (UUE Λ F F'')`. Rewrite using `[mem_orth_iff]`.

Introduce `w hw`. Take `⟨w0, hw0, rfl⟩` from `hUle hw`. Use `show S.hT (n w0) (n x) = 0`. Rewrite using `[hni]`. Conclude with `(mem_orth_iff _ _).1 hx w0 hw0`.

Use `show x - n x ∈ Xsp F`. Use `neg_mem (hnP x hxP)` as an intermediate fact. Simplify using `using this`. Use `show n (m x) - n x ∈ Xsp F''`. Rewrite using `[hX'']`.

Use `⟨m x - x, hmP x hxP', ?_⟩` and prove the remaining obligations. Simplify using `[map_sub]`.
-/
theorem th_eq_hp_gen {T T' : E} (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' F'' : LFlag S r T')
    (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hz'' : F''.zt = F''.fl.z)
    (n m : S.V ≃ₗ[E] S.V) (hni : ∀ x y, S.hT (n x) (n y) = S.hT x y)
    (hnX : ∀ x ∈ Xsp F, n x - x ∈ Xsp F) (hnP : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F)
    (hmX : ∀ x ∈ Xsp F', m x - x ∈ Xsp F') (hmP : ∀ x ∈ orth S (Xsp F'), m x - x ∈ Xsp F')
    (hfr : ∀ a, frame F'' a = (n * m) (frame F' a)) :
    Th Λ F F' F'' (n * m) = Hp Λ F F' := by
  obtain ⟨hXU, hX'U, hzU, hz'U⟩ := sub_le_uue Λ hΛ F F'
  rw [hz] at hzU; rw [hz'] at hz'U
  have hcomp : ((n * m : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) = (n : S.V →ₗ[E] S.V).comp (m : S.V →ₗ[E] S.V) := by
    ext x; rfl
  have he : ∀ i, F''.fl.e i = n (m (F'.fl.e i)) := by
    intro i
    have := hfr (Fin.castSucc i)
    simpa [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using this
  have hzz : F''.fl.z = n (m F'.fl.z) := by
    have := hfr (Fin.last r)
    simpa [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last] using this
  have hmX' : (Xsp F').map (m : S.V →ₗ[E] S.V) = Xsp F' := map_eq_of_sub_mem m _ hmX
  have hnXF : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp F := map_eq_of_sub_mem n _ hnX
  have hX'' : Xsp F'' = (Xsp F').map (n : S.V →ₗ[E] S.V) := by
    have h0 : Xsp F'' = (Xsp F').map ((n * m : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) := by
      show F''.fl.X = F'.fl.X.map _
      unfold Formalism.MainNotions.S.FlagG.X
      rw [Submodule.map_span, ← Set.range_comp]
      have hfun : F''.fl.e = (((n * m : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) ∘ F'.fl.e) := funext fun i => he i
      rw [hfun]
    rw [h0, hcomp, Submodule.map_comp, hmX']
  have hUle : UUE Λ F F'' ≤ (UUE Λ F F').map (n : S.V →ₗ[E] S.V) := by
    refine uue_le Λ F F'' hz hz'' _ ?_ ?_ ?_ ?_
    · rw [← hnXF]; exact Submodule.map_mono hXU
    · rw [hX'']; exact Submodule.map_mono hX'U
    · have h1 : n F.fl.z ∈ (UUE Λ F F').map (n : S.V →ₗ[E] S.V) := Submodule.mem_map_of_mem hzU
      have h2 : n F.fl.z - F.fl.z ∈ (UUE Λ F F').map (n : S.V →ₗ[E] S.V) := by
        have h3 := hnP _ (z_mem_orth F.fl)
        rw [← hnXF] at h3
        exact Submodule.map_mono hXU h3
      have := Submodule.sub_mem _ h1 h2
      simpa using this
    · rw [hzz]
      apply Submodule.mem_map_of_mem
      have hm1 : m F'.fl.z - F'.fl.z ∈ UUE Λ F F' := hX'U (hmP _ (z_mem_orth F'.fl))
      have := Submodule.add_mem _ hm1 hz'U
      simpa using this
  apply le_antisymm
  · rw [Th, Submodule.map_le_iff_le_comap]
    rintro ⟨a, b⟩ hp
    exact hp.1.1.1
  · intro x hx
    have hxP : x ∈ orth S (Xsp F) := orth_anti hXU hx
    have hxP' : x ∈ orth S (Xsp F') := orth_anti hX'U hx
    refine ⟨(x, n x), ⟨⟨⟨hx, ?_⟩, ?_⟩, ?_⟩, rfl⟩
    · show n x ∈ orth S (UUE Λ F F'')
      rw [mem_orth_iff]
      intro w hw
      obtain ⟨w0, hw0, rfl⟩ := hUle hw
      show S.hT (n w0) (n x) = 0
      rw [hni]
      exact (mem_orth_iff _ _).1 hx w0 hw0
    · show x - n x ∈ Xsp F
      have := neg_mem (hnP x hxP)
      simpa using this
    · show n (m x) - n x ∈ Xsp F''
      rw [hX'']
      refine ⟨m x - x, hmP x hxP', ?_⟩
      simp [map_sub]

end Main

end GlobalTheory.DcosetCompl

namespace GlobalTheory.DcosetCompl

/- English proof (translation)
Introduce `D T T' Λ F F' F'' hΛ hz hz' hz'' n hn m hm hfr`. Establish `hnX : ∀ x ∈ Xsp F, n x - x ∈ Xsp F`. Introduce `x hx`. Establish `h` using `hn.2.1 D.R.rS x (by show x ∈ F.fl.Xa (D.R.rS + 1)`. Rewrite using `[xa_eq_x_of_le F.fl (Nat.le_succ _)]`.

Conclude with `hx)`. Express the relevant statement in the definitionally equal form `n x - x ∈ F.fl.Xa D.R.rS at h`. Rewrite `h` using `[xa_eq_x_of_le F.fl (le_refl _)]`. Then use the resulting hypothesis. Establish `hmX : ∀ x ∈ Xsp F', m x - x ∈ Xsp F'`. Introduce `x hx`.

Establish `h` using `hm.2.1 D.R.rS x (by show x ∈ F'.fl.Xa (D.R.rS + 1)`. Rewrite using `[xa_eq_x_of_le F'.fl (Nat.le_succ _)]`. Conclude with `hx)`. Express the relevant statement in the definitionally equal form `m x - x ∈ F'.fl.Xa D.R.rS at h`. Rewrite `h` using `[xa_eq_x_of_le F'.fl (le_refl _)]`. Then use the resulting hypothesis.

Conclude with `th_eq_hp_gen Λ hΛ F F' F'' hz hz' hz'' n m (fun x y => hn.1 x y) hnX hn.2.2 hmX hm.2.2 hfr`.
-/
theorem th_eq_hp : ∀ (D : D7) {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (VS D) D.R.rS T) (F' F'' : LFlag (VS D) D.R.rS T'), Submodule.IsLattice D.host.E Λ → F.zt = F.fl.z → F'.zt = F'.fl.z → F''.zt = F''.fl.z → ∀ n ∈ NRat F, ∀ m ∈ NRat F', (∀ a, frame F'' a = (n * m) (frame F' a)) → Th Λ F F' F'' (n * m) = Hp Λ F F' := by
  intro D T T' Λ F F' F'' hΛ hz hz' hz'' n hn m hm hfr
  have hnX : ∀ x ∈ Xsp F, n x - x ∈ Xsp F := by
    intro x hx
    have h := hn.2.1 D.R.rS x (by
      show x ∈ F.fl.Xa (D.R.rS + 1)
      rw [xa_eq_x_of_le F.fl (Nat.le_succ _)]; exact hx)
    change n x - x ∈ F.fl.Xa D.R.rS at h
    rwa [xa_eq_x_of_le F.fl (le_refl _)] at h
  have hmX : ∀ x ∈ Xsp F', m x - x ∈ Xsp F' := by
    intro x hx
    have h := hm.2.1 D.R.rS x (by
      show x ∈ F'.fl.Xa (D.R.rS + 1)
      rw [xa_eq_x_of_le F'.fl (Nat.le_succ _)]; exact hx)
    change m x - x ∈ F'.fl.Xa D.R.rS at h
    rwa [xa_eq_x_of_le F'.fl (le_refl _)] at h
  exact th_eq_hp_gen Λ hΛ F F' F'' hz hz' hz'' n m (fun x y => hn.1 x y) hnX hn.2.2 hmX hm.2.2 hfr

end GlobalTheory.DcosetCompl
