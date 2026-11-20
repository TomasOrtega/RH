import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.NormSubOneLeOfHsdA

noncomputable section

open Finset Matrix MeasureTheory Topology
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def kUJA (ε : Fin n → Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : Formalism.REAL.UJ ε :=
  ⟨⟨k, star k, Matrix.mem_unitaryGroup_iff.1 hk.1, Matrix.mem_unitaryGroup_iff'.1 hk.1⟩, by
    show Formalism.REAL.inUJ ε k
    rw [mir_inUJ_iff]
    show kᴴ * Jm ε * k = Jm ε
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff'.1 hk.1, Matrix.one_mul]⟩

/- English proof (translation)
Use `set κ := kUJA ε hk with hκdef`. Establish `hκ : Formalism.MainNotions.S.umat κ = k` using `rfl`. Establish `: (Formalism.REAL.muG ε).IsMulRightInvariant` using `⟨fun y => (measurePreserving_mul_right ε y).map_eq⟩`. Establish `hmul : ∀ a b : Formalism.REAL.UJ ε, σ (Formalism.MainNotions.S.umat (a * b)) = (σ (Formalism.MainNotions.S.umat a)).comp (σ (Formalism.MainNotions.S.umat b))` using `fun a b => hσ.1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)`. Use `set F : Formalism.REAL.UJ ε → H := fun g => α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat (g * κ)) v with hF`.

Establish `hR : cvA ε σ α (σ k v) = ∫ g, F g ∂(Formalism.REAL.muG ε)`. Unfold `cvA`. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[hF]`.

Simplify using `only`. Rewrite using `[hmul, ContinuousLinearMap.comp_apply, hκ]`. Establish `hL : σ k (cvA ε σ α v) = ∫ g, F (κ * g * κ⁻¹) ∂(Formalism.REAL.muG ε)`. Unfold `cvA`. Rewrite using `[← ContinuousLinearMap.integral_comp_comm _ (integrable_cvA hσ hα hαc v)]`.

Use `congr 1`. Use function extensionality and compare the values at `g`. Establish `hc : Formalism.MainNotions.S.umat (κ * g * κ⁻¹) = k * Formalism.MainNotions.S.umat g * star k` using `rfl`. Rewrite using `[hF]`. Simplify using `only`.

Rewrite using `[inv_mul_cancel_right, hc, hαK k hk, hmul, ContinuousLinearMap.comp_apply, hκ, map_smul]`. Rewrite using `[hL, hR]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cvA_equivariantA (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hα : Continuous α) (hαc : HasCompactSupport α) (hαK : ∀ k ∈ Kset ε, ∀ g, α (k * g * star k) = α g)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v : H) :
    σ k (cvA ε σ α v) = cvA ε σ α (σ k v) := by
  set κ := kUJA ε hk with hκdef
  have hκ : Formalism.MainNotions.S.umat κ = k := rfl
  have : (Formalism.REAL.muG ε).IsMulRightInvariant :=
    ⟨fun y => (measurePreserving_mul_right ε y).map_eq⟩
  have hmul : ∀ a b : Formalism.REAL.UJ ε,
      σ (Formalism.MainNotions.S.umat (a * b)) = (σ (Formalism.MainNotions.S.umat a)).comp (σ (Formalism.MainNotions.S.umat b)) :=
    fun a b => hσ.1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)
  set F : Formalism.REAL.UJ ε → H := fun g => α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat (g * κ)) v with hF
  have hR : cvA ε σ α (σ k v) = ∫ g, F g ∂(Formalism.REAL.muG ε) := by
    unfold cvA
    congr 1
    funext g
    rw [hF]
    dsimp only
    rw [hmul, ContinuousLinearMap.comp_apply, hκ]
  have hL : σ k (cvA ε σ α v) = ∫ g, F (κ * g * κ⁻¹) ∂(Formalism.REAL.muG ε) := by
    unfold cvA
    rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_cvA hσ hα hαc v)]
    congr 1
    funext g
    have hc : Formalism.MainNotions.S.umat (κ * g * κ⁻¹) = k * Formalism.MainNotions.S.umat g * star k := rfl
    rw [hF]
    dsimp only
    rw [inv_mul_cancel_right, hc, hαK k hk, hmul, ContinuousLinearMap.comp_apply, hκ, map_smul]
  rw [hL, hR]
  calc ∫ g, F (κ * g * κ⁻¹) ∂(Formalism.REAL.muG ε) = ∫ g, F (g * κ⁻¹) ∂(Formalism.REAL.muG ε) :=
        integral_mul_left_eq_self (fun x => F (x * κ⁻¹)) κ
    _ = ∫ g, F g ∂(Formalism.REAL.muG ε) := integral_mul_right_eq_self F κ⁻¹

/- English proof (translation)
Take `⟨hfin, hstab, hirr, ⟨w, hwS, hw0, hwt⟩, hdom⟩` from `hS`. Establish `hstab0 : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ LinearMap.ker T)`. Introduce `g hg v hv`. Rewrite `hv`, the goal using `[Submodule.mem_inf, LinearMap.mem_ker]`. Conclude with `⟨hstab g hg v hv.1, by rw [← hT g hg v, hv.2, _root_.map_zero]⟩`.

Break down `hirr _ inf_le_left hstab0 with h0 | h0` into its components or cases. Establish `hinj : ∀ x ∈ S, T x = 0 → x = 0` using `fun x hx hTx => by`. Establish `hx' : x ∈ S ⊓ LinearMap.ker T` using `Submodule.mem_inf.2 ⟨hx, LinearMap.mem_ker.2 hTx⟩`. Rewrite `hx'` using `[h0]`. Conclude with `(Submodule.mem_bot ℂ).1 hx'`.

Apply `le_sSup` to reduce the goal to its premises. Use `show Formalism.MainNotions.S.IsKTypeOf ε σ μ (S.map T)`. Unfold `Formalism.MainNotions.S.IsKTypeOf`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `haveI : FiniteDimensional ℂ S := hfin infer_instance`.

Introduce and unpack `g hg _ ⟨x, hx, rfl⟩`. Rewrite using `[hT g hg x]`. Conclude with `Submodule.mem_map_of_mem (hstab g hg x hx)`. Introduce `S' hS' hS'st`. Establish `hst : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ S'.comap T)`.

Introduce `g hg v hv`. Rewrite `hv`, the goal using `[Submodule.mem_inf, Submodule.mem_comap]`. Conclude with `⟨hstab g hg v hv.1, by rw [← hT g hg v]; exact hS'st g hg _ hv.2⟩`. Break down `hirr _ inf_le_left hst with h1 | h1` into its components or cases. Use `left`.

Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `hS' hy`. Establish `hx' : x ∈ S ⊓ S'.comap T` using `Submodule.mem_inf.2 ⟨hx, Submodule.mem_comap.2 hy⟩`. Rewrite `hx'` using `[h1, Submodule.mem_bot]`.

Rewrite using `[hx', _root_.map_zero]`. Conclude with `Submodule.zero_mem _`. Use `right`. Use `le_antisymm hS' ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Establish `hx' : x ∈ S ⊓ S'.comap T` using `by rw [h1]; exact hx`. Conclude with `Submodule.mem_comap.1 (Submodule.mem_inf.1 hx').2`. Establish `hTw : T w ≠ 0` using `fun h => hw0 (hinj w hwS h)`. Use `⟨T w, Submodule.mem_map_of_mem hwS, hTw, ?_⟩` and prove the remaining obligations. Introduce `θ hθ`.

Rewrite using `[hT _ hθ w, hwt θ hθ, _root_.map_smul]`. Introduce and unpack `μ' _ ⟨x, hx, rfl⟩ hne hwt'`. Establish `hx0 : x ≠ 0` using `fun h => hne (by rw [h, _root_.map_zero])`. Use `hdom μ' x hx hx0 ?_` and prove the remaining obligations. Introduce `θ hθ`.

Establish `h1` using `hwt' θ hθ`. Rewrite `h1` using `[hT _ hθ x]`. Use `sub_eq_zero.1 (hinj _ (Submodule.sub_mem _ (hstab _ hθ x hx) (Submodule.smul_mem _ _ hx)) ?_)` and prove the remaining obligations. Rewrite using `[_root_.map_sub, h1, _root_.map_smul, sub_self]`. Introduce and unpack `y ⟨x, hx, rfl⟩`.

Establish `hx' : x ∈ S ⊓ LinearMap.ker T` using `by rw [h0]; exact hx`. Rewrite using `[LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx').2]`. Conclude with `Submodule.zero_mem _`.
-/
theorem map_le_isoA (T : H →ₗ[ℂ] H) (hT : ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, σ k (T v) = T (σ k v))
    {μ : Fin n → ℝ} {S : Submodule ℂ H} (hS : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) :
    S.map T ≤ sSup {S' | Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} := by
  obtain ⟨hfin, hstab, hirr, ⟨w, hwS, hw0, hwt⟩, hdom⟩ := hS
  have hstab0 : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ LinearMap.ker T) := by
    intro g hg v hv
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hv ⊢
    exact ⟨hstab g hg v hv.1, by rw [← hT g hg v, hv.2, _root_.map_zero]⟩
  rcases hirr _ inf_le_left hstab0 with h0 | h0
  · have hinj : ∀ x ∈ S, T x = 0 → x = 0 := fun x hx hTx => by
      have hx' : x ∈ S ⊓ LinearMap.ker T := Submodule.mem_inf.2 ⟨hx, LinearMap.mem_ker.2 hTx⟩
      rw [h0] at hx'
      exact (Submodule.mem_bot ℂ).1 hx'
    apply le_sSup
    show Formalism.MainNotions.S.IsKTypeOf ε σ μ (S.map T)
    unfold Formalism.MainNotions.S.IsKTypeOf
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · haveI : FiniteDimensional ℂ S := hfin
      infer_instance
    · rintro g hg _ ⟨x, hx, rfl⟩
      rw [hT g hg x]
      exact Submodule.mem_map_of_mem (hstab g hg x hx)
    · intro S' hS' hS'st
      have hst : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ S'.comap T) := by
        intro g hg v hv
        rw [Submodule.mem_inf, Submodule.mem_comap] at hv ⊢
        exact ⟨hstab g hg v hv.1, by rw [← hT g hg v]; exact hS'st g hg _ hv.2⟩
      rcases hirr _ inf_le_left hst with h1 | h1
      · left
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hS' hy
        have hx' : x ∈ S ⊓ S'.comap T := Submodule.mem_inf.2 ⟨hx, Submodule.mem_comap.2 hy⟩
        rw [h1, Submodule.mem_bot] at hx'
        rw [hx', _root_.map_zero]
        exact Submodule.zero_mem _
      · right
        refine le_antisymm hS' ?_
        rintro _ ⟨x, hx, rfl⟩
        have hx' : x ∈ S ⊓ S'.comap T := by rw [h1]; exact hx
        exact Submodule.mem_comap.1 (Submodule.mem_inf.1 hx').2
    · have hTw : T w ≠ 0 := fun h => hw0 (hinj w hwS h)
      refine ⟨T w, Submodule.mem_map_of_mem hwS, hTw, ?_⟩
      intro θ hθ
      rw [hT _ hθ w, hwt θ hθ, _root_.map_smul]
    · rintro μ' _ ⟨x, hx, rfl⟩ hne hwt'
      have hx0 : x ≠ 0 := fun h => hne (by rw [h, _root_.map_zero])
      refine hdom μ' x hx hx0 ?_
      intro θ hθ
      have h1 := hwt' θ hθ
      rw [hT _ hθ x] at h1
      refine sub_eq_zero.1 (hinj _ (Submodule.sub_mem _ (hstab _ hθ x hx) (Submodule.smul_mem _ _ hx)) ?_)
      rw [_root_.map_sub, h1, _root_.map_smul, sub_self]
  · rintro y ⟨x, hx, rfl⟩
    have hx' : x ∈ S ⊓ LinearMap.ker T := by rw [h0]; exact hx
    rw [LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx').2]
    exact Submodule.zero_mem _

/- English proof (translation)
Set `T : ∀ α, AdmA ε U α → H →ₗ[ℂ] H` to `fun α hα => { toFun := cvA ε σ α map_add' := cvA_add_vec hσ hα.1.continuous hα.2.1 map_smul' := fun c v => cvA_smul_vec α c v }`. Establish `hTK : ∀ α (hα : AdmA ε U α), ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, σ k (T α hα v) = T α hα (σ k v)` using `fun α hα k hk v => cvA_equivariantA hσ hα.1.continuous hα.2.1 hα.2.2.2 (by rw [← mir_Kset_eq]; exact hk) v`. Establish `hWc : IsCompactElement W` using `(Submodule.fg_iff_compact W).1 (Module.Finite.iff_fg.1 hWf)`. Take `⟨t, hts, hWt⟩` from `(CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup (k := W)).1 hWc _ hWsum`. Set `iso : Submodule ℂ H → Submodule ℂ H` to `fun S => if h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S then sSup {S' | Formalism.MainNotions.S.IsKTypeOf ε σ h.choose S'} else ⊥`.

Use `haveI hisoF : ∀ S, FiniteDimensional ℂ (iso S) := by`. Introduce `S`. Distinguish the cases in `h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S`. Establish `e : iso S = sSup {S' | Formalism.MainNotions.S.IsKTypeOf ε σ h.choose S'}` using `dif_pos h`. Rewrite using `[e]`.

Conclude with `hadm _`. Establish `e : iso S = ⊥` using `dif_neg h`. Rewrite using `[e]`. Use `infer_instance`. Set `W2` to `t.sup iso`.

Establish `hS_le : ∀ S ∈ t, S ≤ iso S ∧ ∀ α (hα : AdmA ε U α), S.map (T α hα) ≤ iso S`. Introduce `S hS`. Establish `h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S` using `hts hS`. Simplify using `only [iso, dif_pos h]`. Conclude with `⟨le_sSup h.choose_spec, fun α hα => map_le_isoA (T α hα) (hTK α hα) h.choose_spec⟩`.

Establish `hWW2 : W ≤ W2` using `hWt.trans (Finset.sup_le fun S hS => (hS_le S hS).1.trans (Finset.le_sup (f := iso) hS))`. Establish `hmapW : ∀ α (hα : AdmA ε U α), ∀ w ∈ W, cvA ε σ α w ∈ W2`. Introduce `α hα w hw`. Establish `: W ≤ W2.comap (T α hα)` using `hWt.trans (Finset.sup_le fun S hS => Submodule.map_le_iff_le_comap.1 (((hS_le S hS).2 α hα).trans (Finset.le_sup (f := iso) hS)))`. Conclude with `this hw`.

Set `b` to `Module.finBasis ℂ W`. Set `bw : Fin (Module.finrank ℂ W) → H` to `fun i => (b i : H)`. Set `R : Submodule ℂ (Fin (Module.finrank ℂ W) → W2)` to `{ carrier := {p | ∃ α, AdmA ε U α ∧ ∀ i, cvA ε σ α (bw i) = (p i : H)} add_mem' := by`. Introduce and unpack `p q ⟨α, hα, hp⟩ ⟨β, hβ, hq⟩`. Conclude with `⟨α + β, hα.add hβ, fun i => by`.

Rewrite using `[cvA_add_fun hσ hα.1.continuous hα.2.1 hβ.1.continuous hβ.2.1, hp, hq]`. Use the proof step `rfl⟩`. Use the proof step `zero_mem' := ⟨0, AdmA.zero U, fun i => by rw [cvA_zero_fun]; rfl⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c p ⟨α, hα, hp⟩`.

Conclude with `⟨c • α, hα.smul c, fun i => by rw [cvA_smul_fun, hp]; rfl⟩ }`. Establish `hRc : IsClosed (R : Set (Fin (Module.finrank ℂ W) → W2))` using `R.closed_of_finiteDimensional`. Set `p0 : Fin (Module.finrank ℂ W) → W2` to `fun i => ⟨bw i, hWW2 (b i).2⟩`. Establish `hp0 : p0 ∈ closure (R : Set (Fin (Module.finrank ℂ W) → W2))`. Rewrite using `[Metric.mem_closure_iff]`.

Introduce `η hη`. Take `⟨α, hα, hnear⟩` from `exists_nearA hσ hU h1 bw (half_pos hη)`. Use `⟨fun i => ⟨cvA ε σ α (bw i), hmapW α hα _ (b i).2⟩, ⟨α, hα, fun i => rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[dist_pi_lt_iff hη]`. Introduce `i`.

Use `show dist (bw i) (cvA ε σ α (bw i)) < η`. Rewrite using `[dist_comm, dist_eq_norm]`. Combine the linear relations using `[hnear i]`. Rewrite `hp0` using `[hRc.closure_eq]`. Take `⟨α, hα, hfix⟩` from `hp0`.

Use `⟨α, hα, ?_⟩` and prove the remaining obligations. Establish `hext : (T α hα).comp W.subtype = W.subtype` using `b.ext fun i => hfix i`. Introduce `w hw`. Conclude with `LinearMap.congr_fun hext ⟨w, hw⟩`.
-/
theorem exists_cvA_idA (hσ : IsURepOn (UJset ε) σ)
    (hadm : ∀ μ : Fin n → ℝ, FiniteDimensional ℂ
      (sSup {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H))
    (W : Submodule ℂ H) (hWf : FiniteDimensional ℂ W)
    (hWsum : W ≤ sSup {S : Submodule ℂ H | ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S})
    {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U) (h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U) :
    ∃ α, AdmA ε U α ∧ ∀ w ∈ W, cvA ε σ α w = w := by
  classical
  let T : ∀ α, AdmA ε U α → H →ₗ[ℂ] H := fun α hα =>
    { toFun := cvA ε σ α
      map_add' := cvA_add_vec hσ hα.1.continuous hα.2.1
      map_smul' := fun c v => cvA_smul_vec α c v }
  have hTK : ∀ α (hα : AdmA ε U α), ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, σ k (T α hα v) = T α hα (σ k v) :=
    fun α hα k hk v => cvA_equivariantA hσ hα.1.continuous hα.2.1 hα.2.2.2
      (by rw [← mir_Kset_eq]; exact hk) v
  have hWc : IsCompactElement W :=
    (Submodule.fg_iff_compact W).1 (Module.Finite.iff_fg.1 hWf)
  obtain ⟨t, hts, hWt⟩ :=
    (CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup (k := W)).1 hWc _ hWsum
  let iso : Submodule ℂ H → Submodule ℂ H := fun S =>
    if h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S then sSup {S' | Formalism.MainNotions.S.IsKTypeOf ε σ h.choose S'} else ⊥
  haveI hisoF : ∀ S, FiniteDimensional ℂ (iso S) := by
    intro S
    by_cases h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S
    · have e : iso S = sSup {S' | Formalism.MainNotions.S.IsKTypeOf ε σ h.choose S'} := dif_pos h
      rw [e]
      exact hadm _
    · have e : iso S = ⊥ := dif_neg h
      rw [e]
      infer_instance
  let W2 := t.sup iso
  have hS_le : ∀ S ∈ t, S ≤ iso S ∧ ∀ α (hα : AdmA ε U α), S.map (T α hα) ≤ iso S := by
    intro S hS
    have h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S := hts hS
    simp only [iso, dif_pos h]
    exact ⟨le_sSup h.choose_spec, fun α hα => map_le_isoA (T α hα) (hTK α hα) h.choose_spec⟩
  have hWW2 : W ≤ W2 :=
    hWt.trans (Finset.sup_le fun S hS => (hS_le S hS).1.trans (Finset.le_sup (f := iso) hS))
  have hmapW : ∀ α (hα : AdmA ε U α), ∀ w ∈ W, cvA ε σ α w ∈ W2 := by
    intro α hα w hw
    have : W ≤ W2.comap (T α hα) :=
      hWt.trans (Finset.sup_le fun S hS => Submodule.map_le_iff_le_comap.1
        (((hS_le S hS).2 α hα).trans (Finset.le_sup (f := iso) hS)))
    exact this hw
  let b := Module.finBasis ℂ W
  let bw : Fin (Module.finrank ℂ W) → H := fun i => (b i : H)
  let R : Submodule ℂ (Fin (Module.finrank ℂ W) → W2) :=
    { carrier := {p | ∃ α, AdmA ε U α ∧ ∀ i, cvA ε σ α (bw i) = (p i : H)}
      add_mem' := by
        rintro p q ⟨α, hα, hp⟩ ⟨β, hβ, hq⟩
        exact ⟨α + β, hα.add hβ, fun i => by
          rw [cvA_add_fun hσ hα.1.continuous hα.2.1 hβ.1.continuous hβ.2.1, hp, hq]
          rfl⟩
      zero_mem' := ⟨0, AdmA.zero U, fun i => by rw [cvA_zero_fun]; rfl⟩
      smul_mem' := by
        rintro c p ⟨α, hα, hp⟩
        exact ⟨c • α, hα.smul c, fun i => by rw [cvA_smul_fun, hp]; rfl⟩ }
  have hRc : IsClosed (R : Set (Fin (Module.finrank ℂ W) → W2)) := R.closed_of_finiteDimensional
  let p0 : Fin (Module.finrank ℂ W) → W2 := fun i => ⟨bw i, hWW2 (b i).2⟩
  have hp0 : p0 ∈ closure (R : Set (Fin (Module.finrank ℂ W) → W2)) := by
    rw [Metric.mem_closure_iff]
    intro η hη
    obtain ⟨α, hα, hnear⟩ := exists_nearA hσ hU h1 bw (half_pos hη)
    refine ⟨fun i => ⟨cvA ε σ α (bw i), hmapW α hα _ (b i).2⟩, ⟨α, hα, fun i => rfl⟩, ?_⟩
    rw [dist_pi_lt_iff hη]
    intro i
    show dist (bw i) (cvA ε σ α (bw i)) < η
    rw [dist_comm, dist_eq_norm]
    linarith [hnear i]
  rw [hRc.closure_eq] at hp0
  obtain ⟨α, hα, hfix⟩ := hp0
  refine ⟨α, hα, ?_⟩
  have hext : (T α hα).comp W.subtype = W.subtype := b.ext fun i => hfix i
  intro w hw
  exact LinearMap.congr_fun hext ⟨w, hw⟩

end ReciprocityTheory.ChartRestriction.DS
