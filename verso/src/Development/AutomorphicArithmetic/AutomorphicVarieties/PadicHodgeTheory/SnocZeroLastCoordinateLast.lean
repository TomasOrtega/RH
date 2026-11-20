import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PrF
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmBilin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.DualInvariantFiltration

section Filt

variable {G E V : Type} [Group G] [Field E] [AddCommGroup V] [Module E V]

private def Ch (ρ : Representation E G V) (S : Set (G →* Eˣ)) (W : Submodule E V) : Prop :=
  ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = W ∧ ∀ i < n, F i ≤ F (i + 1) ∧
    ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ Submodule.span E {x} ∧ ∀ g, ρ g x - ((κ g : Eˣ) : E) • x ∈ F i

/- English proof (translation)
Take `⟨n, F, h0, hn, hF⟩` from `hU`. Use `⟨n + 1, fun i => if i ≤ n then F i else U ⊔ Submodule.span E {x}, by simp [h0], by simp, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl` into its components or cases. Establish `h1 : i ≤ n` using `h.le`.

Establish `h2 : i + 1 ≤ n` using `h`. Simplify using `only [h1, h2, if_true]`. Conclude with `hF i h`. Simplify using `only [le_refl, if_true, Nat.add_one_le_iff, lt_irrefl, if_false, hn]`. Conclude with `⟨le_sup_left, κ, hκ, x, rfl, hx⟩`.
-/
private theorem ch_step {ρ : Representation E G V} {S : Set (G →* Eˣ)} {U : Submodule E V} (hU : Ch ρ S U)
    {κ : G →* Eˣ} (hκ : κ ∈ S) (x : V) (hx : ∀ g, ρ g x - ((κ g : Eˣ) : E) • x ∈ U) :
    Ch ρ S (U ⊔ Submodule.span E {x}) := by
  obtain ⟨n, F, h0, hn, hF⟩ := hU
  refine ⟨n + 1, fun i => if i ≤ n then F i else U ⊔ Submodule.span E {x}, by simp [h0], by simp, ?_⟩
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
  · have h1 : i ≤ n := h.le
    have h2 : i + 1 ≤ n := h
    simp only [h1, h2, if_true]
    exact hF i h
  · simp only [le_refl, if_true, Nat.add_one_le_iff, lt_irrefl, if_false, hn]
    exact ⟨le_sup_left, κ, hκ, x, rfl, hx⟩

/- English proof (translation)
Take `⟨t, ht⟩ : W.FG` from `IsNoetherian.noetherian W`. Establish `key : ∀ s : Finset V, (∀ x ∈ s, x ∈ W) → Ch ρ S (U ⊔ Submodule.span E (s : Set V))`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _`.

Simplify using `using hU`. Consider the case `insert a s ha ih`. Introduce `h`. Establish `h1` using `ih fun x hx => h x (Finset.mem_insert_of_mem hx)`. Establish `h2` using `ch_step h1 hκ a fun g => Submodule.mem_sup_left (hx a (h a (Finset.mem_insert_self _ _)) g)`.

Rewrite using `[Finset.coe_insert, Submodule.span_insert, sup_comm (Submodule.span E {a}), ← sup_assoc]`. Conclude with `h2`. Use `key t fun x hx => ht ▸ Submodule.subset_span hx` as an intermediate fact. Rewrite `this` using `[ht, sup_eq_right.2 hUW]`. Then use the resulting hypothesis.
-/
private theorem ch_step2 [FiniteDimensional E V] {ρ : Representation E G V} {S : Set (G →* Eˣ)}
    {U W : Submodule E V} (hU : Ch ρ S U) (hUW : U ≤ W)
    {κ : G →* Eˣ} (hκ : κ ∈ S) (hx : ∀ x ∈ W, ∀ g, ρ g x - ((κ g : Eˣ) : E) • x ∈ U) :
    Ch ρ S W := by
  classical
  obtain ⟨t, ht⟩ : W.FG := IsNoetherian.noetherian W
  have key : ∀ s : Finset V, (∀ x ∈ s, x ∈ W) → Ch ρ S (U ⊔ Submodule.span E (s : Set V)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using hU
    | insert a s ha ih =>
      intro h
      have h1 := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
      have h2 := ch_step h1 hκ a fun g =>
        Submodule.mem_sup_left (hx a (h a (Finset.mem_insert_self _ _)) g)
      rw [Finset.coe_insert, Submodule.span_insert, sup_comm (Submodule.span E {a}), ← sup_assoc]
      exact h2
  have := key t fun x hx => ht ▸ Submodule.subset_span hx
  rwa [ht, sup_eq_right.2 hUW] at this

/- English proof (translation)
Take `⟨n, F, h0, hn, hF⟩` from `h`. Rewrite using `[eq_bot_iff]`. Introduce `f hf`. Establish `key : ∀ i ≤ n, F i ≤ LinearMap.ker f`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero => intro _`. Simplify using `[h0]`. Consider the case `succ i ih`. Introduce `hi`.

Take `⟨-, κ, hκ, x, hx, hg⟩` from `hF i hi`. Establish `h1` using `ih (Nat.le_of_succ_le hi)`. Rewrite using `[hx, sup_le_iff, Submodule.span_singleton_le_iff_mem]`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Take `⟨g, hne⟩` from `hS κ hκ`.

Establish `h2` using `h1 (hg g)`. Rewrite `h2` using `[LinearMap.mem_ker, map_sub, map_smul, hf g x, smul_eq_mul, ← sub_mul]`. Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h3).symm hne`. Conclude with `h3`.

Use `key n le_rfl` as an intermediate fact. Rewrite `this` using `[hn, top_le_iff, LinearMap.ker_eq_top]`. Simplify using `[this]`.
-/
private theorem h0dual_bot {ρ : Representation E G V} {S : Set (G →* Eˣ)} (h : FiltBy ρ S) (χ : G →* Eˣ)
    (hS : ∀ κ ∈ S, ∃ g, (κ g : E) ≠ χ g) : H0dual χ ρ = ⊥ := by
  obtain ⟨n, F, h0, hn, hF⟩ := h
  rw [eq_bot_iff]
  intro f hf
  have key : ∀ i ≤ n, F i ≤ LinearMap.ker f := by
    intro i
    induction i with
    | zero => intro _; simp [h0]
    | succ i ih =>
      intro hi
      obtain ⟨-, κ, hκ, x, hx, hg⟩ := hF i hi
      have h1 := ih (Nat.le_of_succ_le hi)
      rw [hx, sup_le_iff, Submodule.span_singleton_le_iff_mem]
      refine ⟨h1, ?_⟩
      obtain ⟨g, hne⟩ := hS κ hκ
      have h2 := h1 (hg g)
      rw [LinearMap.mem_ker, map_sub, map_smul, hf g x, smul_eq_mul, ← sub_mul] at h2
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd (sub_eq_zero.1 h3).symm hne
      · exact h3
  have := key n le_rfl
  rw [hn, top_le_iff, LinearMap.ker_eq_top] at this
  simp [this]

/- English proof (translation)
Use `haveI : IsNoetherianRing A := isNoetherian_of_tower E inferInstance`. Use `set m : Ideal A := RingHom.ker (π : A →+* E) with hm`. Choose the witnesses or unpack the hypotheses as in `⟨N, hN⟩ : IsNilpotent m := by`. Rewrite using `[Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian m)]`. Conclude with `fun a ha => hπ a ha`.

Set `U : ℕ → Submodule E (Fin n → A)` to `fun i => { carrier := {x | ∀ j : Fin n, i ≤ j.val → x j = 0} zero_mem' := fun _ _ => rfl add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj] smul_mem' := fun c x hx j hj => by simp [hx j hj] }`. Establish `key : ∀ i ≤ n, Ch ρ S (U i)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`.

Introduce `_`. Establish `: U 0 = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Conclude with `funext fun j => hx j (Nat.zero_le _)`.

Rewrite using `[this]`. Conclude with `⟨0, fun _ => ⊥, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩`. Consider the case `succ i ih`. Introduce `hi`. Establish `h1` using `ih (Nat.le_of_succ_le hi)`.

Set `i' : Fin n` to `⟨i, hi⟩`. Set `W : ℕ → Submodule E (Fin n → A)` to `fun k => U (i + 1) ⊓ ((m ^ k).restrictScalars E).comap (LinearMap.proj i')`. Establish `hWN : W N = U i`. Use extensionality with `x`. Simplify using `only [W, hN, Submodule.mem_inf, Submodule.mem_comap, Submodule.restrictScalars_mem, LinearMap.proj_apply, Submodule.zero_eq_bot, Submodule.mem_bot]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b⟩ j hj`. Break down `hj.lt_or_eq with h | h` into its components or cases. Conclude with `a j h`. Establish `: j = i'` using `Fin.ext h.symm`.

Rewrite using `[this]`. Conclude with `b`. Introduce `a`. Conclude with `⟨fun j hj => a j (Nat.le_of_succ_le hj), a i' le_rfl⟩`. Establish `hW0 : W 0 = U (i + 1)` using `by simp [W]`.

Take `⟨κ, hκ, hκψ⟩` from `hψ i'`. Establish `step : ∀ k, Ch ρ S (W (k + 1)) → Ch ρ S (W k)`. Introduce `k hk`. Use `ch_step2 hk (inf_le_inf_left _ (Submodule.comap_mono ?_)) hκ ?_` and prove the remaining obligations. Conclude with `fun a ha => Ideal.pow_le_pow_right (Nat.le_succ k) ha`.

Introduce and unpack `x ⟨hx1, hx2⟩ g`. Take `⟨a, b⟩` from `hρ g i' x fun j hj => hx1 j hj`. Use `⟨fun j hj => ?_, ?_⟩` and prove the remaining obligations. Use `hx1 j hj` as an intermediate fact. Simplify using `[a j hj, this]`.

Express the relevant statement in the definitionally equal form `ρ g x i' - (κ g : E) • x i' ∈ m ^ (k + 1)`. Rewrite using `[b, Algebra.smul_def, ← sub_mul, pow_succ']`. Use `Ideal.mul_mem_mul ?_ hx2` and prove the remaining obligations. Simplify using `[hm, RingHom.mem_ker, hκψ]`. Rewrite using `[← hW0]`.

Conclude with `Nat.decreasingInduction (motive := fun k _ => Ch ρ S (W k)) (fun k _ h => step k h) (hWN ▸ h1) (Nat.zero_le N)`. Use `key n le_rfl` as an intermediate fact. Establish `hn : U n = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _ j hj`.

Conclude with `absurd j.2 (not_lt.2 hj)`. Rewrite `this` using `[hn]`. Conclude with `this`.
-/
private theorem filt_tri {A : Type} [CommRing A] [Algebra E A] [Module.Finite E A] (π : A →ₐ[E] E)
    (hπ : ∀ a, π a = 0 → IsNilpotent a) {n : ℕ} (ρ : Representation E G (Fin n → A)) (S : Set (G →* Eˣ))
    (ψ : Fin n → G → A) (hψ : ∀ i, ∃ κ ∈ S, ∀ g, (κ g : E) = π (ψ i g))
    (hρ : ∀ g (i : Fin n) (x : Fin n → A), (∀ j, i < j → x j = 0) →
      (∀ j, i < j → ρ g x j = 0) ∧ ρ g x i = ψ i g * x i) : FiltBy ρ S := by
  haveI : IsNoetherianRing A := isNoetherian_of_tower E inferInstance
  set m : Ideal A := RingHom.ker (π : A →+* E) with hm
  obtain ⟨N, hN⟩ : IsNilpotent m := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian m)]
    exact fun a ha => hπ a ha
  let U : ℕ → Submodule E (Fin n → A) := fun i =>
    { carrier := {x | ∀ j : Fin n, i ≤ j.val → x j = 0}
      zero_mem' := fun _ _ => rfl
      add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
      smul_mem' := fun c x hx j hj => by simp [hx j hj] }
  have key : ∀ i ≤ n, Ch ρ S (U i) := by
    intro i
    induction i with
    | zero =>
      intro _
      have : U 0 = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact funext fun j => hx j (Nat.zero_le _)
      rw [this]
      exact ⟨0, fun _ => ⊥, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ i ih =>
      intro hi
      have h1 := ih (Nat.le_of_succ_le hi)
      let i' : Fin n := ⟨i, hi⟩
      let W : ℕ → Submodule E (Fin n → A) := fun k =>
        U (i + 1) ⊓ ((m ^ k).restrictScalars E).comap (LinearMap.proj i')
      have hWN : W N = U i := by
        ext x
        simp only [W, hN, Submodule.mem_inf, Submodule.mem_comap, Submodule.restrictScalars_mem,
          LinearMap.proj_apply, Submodule.zero_eq_bot, Submodule.mem_bot]
        constructor
        · rintro ⟨a, b⟩ j hj
          rcases hj.lt_or_eq with h | h
          · exact a j h
          · have : j = i' := Fin.ext h.symm
            rw [this]; exact b
        · intro a
          exact ⟨fun j hj => a j (Nat.le_of_succ_le hj), a i' le_rfl⟩
      have hW0 : W 0 = U (i + 1) := by simp [W]
      obtain ⟨κ, hκ, hκψ⟩ := hψ i'
      have step : ∀ k, Ch ρ S (W (k + 1)) → Ch ρ S (W k) := by
        intro k hk
        refine ch_step2 hk (inf_le_inf_left _ (Submodule.comap_mono ?_)) hκ ?_
        · exact fun a ha => Ideal.pow_le_pow_right (Nat.le_succ k) ha
        · rintro x ⟨hx1, hx2⟩ g
          obtain ⟨a, b⟩ := hρ g i' x fun j hj => hx1 j hj
          refine ⟨fun j hj => ?_, ?_⟩
          · have := hx1 j hj
            simp [a j hj, this]
          · change ρ g x i' - (κ g : E) • x i' ∈ m ^ (k + 1)
            rw [b, Algebra.smul_def, ← sub_mul, pow_succ']
            refine Ideal.mul_mem_mul ?_ hx2
            simp [hm, RingHom.mem_ker, hκψ]
      rw [← hW0]
      exact Nat.decreasingInduction (motive := fun k _ => Ch ρ S (W k)) (fun k _ h => step k h)
        (hWN ▸ h1) (Nat.zero_le N)
  have := key n le_rfl
  have hn : U n = ⊤ := by
    rw [eq_top_iff]
    intro x _ j hj
    exact absurd j.2 (not_lt.2 hj)
  rw [hn] at this
  exact this

end Filt

section Mat

variable {G A : Type} [Group G] [CommRing A]

private noncomputable def mrep {n : ℕ} (M : G →* Matrix (Fin n) (Fin n) A) : Representation A G (Fin n → A) where
  toFun g := Matrix.toLin' (M g)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Module.End.mul_eq_comp]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem mrep_apply {n : ℕ} (M : G →* Matrix (Fin n) (Fin n) A) (g : G) (x : Fin n → A) (i : Fin n) :
    mrep M g x i = ∑ j, M g i j * x j := rfl

private def topBlock {n : ℕ} (M : G →* Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (h : ∀ g i j, j < i → M g i j = 0) : G →* Matrix (Fin n) (Fin n) A where
  toFun g := (M g).submatrix Fin.castSucc Fin.castSucc
  map_one' := by rw [map_one, Matrix.submatrix_one _ (Fin.castSucc_injective n)]
  map_mul' g k := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, h k (Fin.last n) j.castSucc (Fin.castSucc_lt_last j)]

private def ext0 (n : ℕ) : (Fin n → A) →ₗ[A] (Fin (n + 1) → A) :=
  LinearMap.pi fun i => Fin.lastCases 0 (fun j => LinearMap.proj j) i

/- English proof (translation)
Simplify using `[ext0]`.
-/
@[simp] private theorem snocZeroLastCoordinate_last (n : ℕ) (x : Fin n → A) : ext0 n x (Fin.last n) = 0 := by simp [ext0]

/- English proof (translation)
Simplify using `[ext0]`.
-/
@[simp] private theorem extend_zero_castSucc (n : ℕ) (x : Fin n → A) (j : Fin n) : ext0 n x j.castSucc = x j := by
  simp [ext0]

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Simplify using `only [mrep_apply]`. Conclude with `continuous_finset_sum _ fun j _ => ((h i j).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)`.
-/
private theorem cont_mrep [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalRing A] {n : ℕ}
    (M : G →* Matrix (Fin n) (Fin n) A) (h : ∀ i j, Continuous fun g => M g i j) : ContAction (mrep M) := by
  refine continuous_pi fun i => ?_
  simp only [mrep_apply]
  exact continuous_finset_sum _ fun j _ =>
    ((h i j).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `j hj`. Rewrite using `[mrep_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge i k with hk | hk` into its components or cases.

Rewrite using `[hx k hk, mul_zero]`. Rewrite using `[h g j k (hk.trans_lt hj), zero_mul]`. Rewrite using `[mrep_apply]`. Use `Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hk with hk | hk` into its components or cases.

Rewrite using `[h g i k hk, zero_mul]`. Rewrite using `[hx k hk, mul_zero]`.
-/
private theorem tri_apply {n : ℕ} (M : G →* Matrix (Fin n) (Fin n) A) (h : ∀ g i j, j < i → M g i j = 0)
    (g : G) (i : Fin n) (x : Fin n → A) (hx : ∀ j, i < j → x j = 0) :
    (∀ j, i < j → mrep M g x j = 0) ∧ mrep M g x i = M g i i * x i := by
  constructor
  · intro j hj
    rw [mrep_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with hk | hk
    · rw [hx k hk, mul_zero]
    · rw [h g j k (hk.trans_lt hj), zero_mul]
  · rw [mrep_apply]
    refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [h g i k hk, zero_mul]
    · rw [hx k hk, mul_zero]

end Mat

/- English proof (translation)
Establish `h1 : (φ.comp (⊤ : Subgroup G).subtype).range = φ.range`. Rewrite using `[MonoidHom.range_comp, Subgroup.range_subtype, ← MonoidHom.range_eq_map]`. Establish `h2 : Dcr (φ.comp (⊤ : Subgroup G).subtype) (resCoef ℚ_[l] (ρ.comp (⊤ : Subgroup G).subtype : Representation A (⊤ : Subgroup G) V)) = Dcr φ (resCoef ℚ_[l] ρ)`. Use extensionality with `x`. Simplify using `only [Dcr, Submodule.mem_iInf]`.

Conclude with `⟨fun h g => h ⟨g, trivial⟩, fun h g => h g.1⟩`. Unfold `CrOn IsCr`. Rewrite using `[h1, h2]`.
-/
private theorem isCr_of_top {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l)
    (ρ : Representation A G V) : CrOn φ ρ ⊤ ↔ IsCr φ ρ := by
  have h1 : (φ.comp (⊤ : Subgroup G).subtype).range = φ.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, ← MonoidHom.range_eq_map]
  have h2 : Dcr (φ.comp (⊤ : Subgroup G).subtype)
      (resCoef ℚ_[l] (ρ.comp (⊤ : Subgroup G).subtype : Representation A (⊤ : Subgroup G) V)) =
      Dcr φ (resCoef ℚ_[l] ρ) := by
    ext x
    simp only [Dcr, Submodule.mem_iInf]
    exact ⟨fun h g => h ⟨g, trivial⟩, fun h g => h g.1⟩
  unfold CrOn IsCr
  rw [h1, h2]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `M hM κ w _ _ _ _ _`. Conclude with `crUnr φ hφ (mrep M) (cont_mrep M hM) 0 fun _ _ _ => Subsingleton.elim _ _`. Consider the case `succ n ih`.

Introduce `M hM κ w htri hdiag hw hI hne`. Use `haveI : ContinuousConstSMul E (Fin n → A) := ⟨fun c => IsModuleTopology.continuous_of_linearMap ((Algebra.lsmul ℚ_[l] ℚ_[l] (Fin n → A) : E →ₐ[ℚ_[l]] Module.End ℚ_[l] (Fin n → A)) c)⟩`. Use `set M0 := topBlock M htri with hM0`. Establish `hM0c : ∀ i j, Continuous fun g => M0 g i j` using `fun i j => hM _ _`. Establish `htri0 : ∀ g i j, j < i → M0 g i j = 0` using `fun g i j h => htri g _ _ (Fin.castSucc_lt_castSucc_iff.2 h)`.

Establish `h0 : IsCr φ (mrep M0)` using `ih M0 hM0c (fun i => κ i.castSucc) (fun i => w i.castSucc) htri0 (fun g i => hdiag g _) (fun i j h => hw (Fin.castSucc_lt_castSucc_iff.2 h)) (fun i => hI _) (fun i j h => hne _ _ (Fin.castSucc_lt_castSucc_iff.2 h))`. Use `set k := κ (Fin.last n) with hk`. Establish `hkc : Continuous fun g => (k g : A)`. Simplify using `only [hk, ← hdiag]`. Conclude with `hM _ _`.

Establish `hkc' : Continuous fun g => ((k⁻¹ g : Aˣ) : A)`. Establish `: (fun g => ((k⁻¹ g : Aˣ) : A)) = (fun g => (k g : A)) ∘ fun g => g⁻¹`. Use extensionality with `g`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `hkc.comp continuous_inv`. Establish `hch : ∀ χ : G →* Aˣ, Continuous (fun g => (χ g : A)) → ContAction (chRep χ)` using `fun χ h => (h.comp continuous_fst).mul continuous_snd`. Establish `hkcr : IsCr φ (chRep k)` using `crUnr φ hφ _ (hch _ hkc) (w (Fin.last n)) fun g hg x => by`. Rewrite using `[← hI _ g hg]`. Both sides reduce to the same expression.

Establish `hkcr' : IsCr φ (chRep k⁻¹)` using `crUnr φ hφ _ (hch _ hkc') (-w (Fin.last n)) fun g hg x => by`. Rewrite using `[zpow_neg, ← hI _ g hg]`. Both sides reduce to the same expression. Establish `htw : ContAction (twist k⁻¹ (mrep M0))` using `(hkc'.comp continuous_fst).smul (cont_mrep M0 hM0c)`. Establish `htwcr : IsCr φ (twist k⁻¹ (mrep M0))`.

Use `(admissible_of_bilinear_openSubgroup_galois φ hφ (chRep k⁻¹) (mrep M0) _ (hch _ hkc') (cont_mrep M0 hM0c) htw ((LinearMap.lsmul A (Fin n → A)).restrictScalars₁₂ ℚ_[l] ℚ_[l]) ?_ ?_).1 hkcr' h0` and prove the remaining obligations. Introduce `g x y`. Simplify using `[chRep, twist, smul_smul, mul_comm]`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Conclude with `Submodule.subset_span ⟨(1, x), by simp⟩`. Establish `hπc : ∀ σ, π (cycA l l A σ : A) = (cycA l l E σ : E)` using `fun σ => by`. Simplify using `only [cycA, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] A, IsScalarTower.algebraMap_apply ℚ_[l] E A, AlgHom.commutes, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E]`. Both sides reduce to the same expression.

Set `ψ : Fin n → G →* Eˣ` to `fun i => (Units.map (π : A →* E)).comp (k⁻¹ * κ i.castSucc)`. Establish `hfil : ∀ S : Set (G →* Eˣ), (∀ i, ψ i ∈ S) → FiltBy (resCoef E (twist k⁻¹ (mrep M0))) S`. Introduce `S hS`. Use `filt_tri π hπ _ S (fun i g => ((k⁻¹ * κ i.castSucc) g : Aˣ)) (fun i => ⟨ψ i, hS i, fun g => rfl⟩) ?_` and prove the remaining obligations. Introduce `g i x hx`.

Take `⟨a, b⟩` from `tri_apply M0 htri0 g i x hx`. Establish `e : ∀ j, resCoef E (twist k⁻¹ (mrep M0)) g x j = ((k⁻¹ g : Aˣ) : A) * mrep M0 g x j` using `fun j => rfl`. Use `⟨fun j hj => by rw [e, a j hj, mul_zero], ?_⟩` and prove the remaining obligations. Establish `: M0 g i i = κ i.castSucc g` using `hdiag g _`. Rewrite using `[e, b, this]`.

Simplify using `[mul_assoc]`. Establish `hpos : Positive φ (resCoef E (twist k⁻¹ (mrep M0)))`. Use `⟨(isCrys_isDR_restrict_openSubgroup φ hφ _ htw).1 htwcr, hfil _ fun i => ⟨w i.castSucc - w (Fin.last n), ?_, ⊤, isOpen_univ, ?_⟩⟩` and prove the remaining obligations. Use `hw (Fin.castSucc_lt_last i)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce `g _ hg`. Establish `e : Units.map (π : A →* E) (cycA l l A (φ g)) = cycA l l E (φ g)` using `Units.ext (hπc _)`. Simplify using `only [ψ, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, hk, hI _ g hg]`. Rewrite using `[map_mul, map_inv, map_zpow (Units.map (π : A →* E)), map_zpow (Units.map (π : A →* E)), e, zpow_sub]`. Conclude with `mul_comm _ _`.

Establish `hdual : H0dual ((cycA l l E).comp φ) (resCoef E (twist k⁻¹ (mrep M0))) = ⊥`. Use `h0dual_bot (hfil (Set.range ψ) fun i => ⟨i, rfl⟩) _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨g, hg⟩` from `hne _ _ (Fin.castSucc_lt_last i)`. Use `⟨g, fun h => hg ?_⟩` and prove the remaining obligations.

Establish `h' : (ψ i g : E) = (cycA l l E (φ g) : E)` using `h`. Rewrite using `[← h']`. Express the relevant statement in the definitionally equal form `_ = π (k g : A) * π (((k⁻¹ * κ i.castSucc) g : Aˣ) : A)`. Rewrite using `[← map_mul]`. Simplify using the standard rewrite rules.

Establish `hF` using `prF hP φ hφ (resCoef E (twist k⁻¹ (mrep M0))) htw hpos hdual`. Set `c : G → Fin n → A` to `fun g i => ((k⁻¹ g : Aˣ) : A) * M g i.castSucc (Fin.last n)`. Establish `hc : c ∈ Z1 (resCoef E (twist k⁻¹ (mrep M0)))`. Use `⟨continuous_pi fun i => hkc'.mul (hM _ _), fun g h => funext fun i => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((k⁻¹ (g * h) : Aˣ) : A) * M (g * h) i.castSucc (Fin.last n) = ((k⁻¹ g : Aˣ) : A) * M g i.castSucc (Fin.last n) + ((k⁻¹ g : Aˣ) : A) * ∑ j : Fin n, M g i.castSucc j.castSucc * (((k⁻¹ h : Aˣ) : A) * M h j.castSucc (Fin.last n))`.

Establish `e : ((k⁻¹ h : Aˣ) : A) * (k h : A) = 1` using `by simp`. Establish `e2 : ∑ j : Fin n, M g i.castSucc j.castSucc * (((k⁻¹ h : Aˣ) : A) * M h j.castSucc (Fin.last n)) = ((k⁻¹ h : Aˣ) : A) * ∑ j : Fin n, M g i.castSucc j.castSucc * M h j.castSucc (Fin.last n)`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[map_mul, map_mul, Matrix.mul_apply, Fin.sum_univ_castSucc, hdiag, ← hk, Units.val_mul, e2]`.

Take the linear combination `((k⁻¹ g : Aˣ) : A) * M g i.castSucc (Fin.last n) * e`. Rewrite `hc` using `[← hF]`. Establish `hc' : c ∈ UpperTheory.V.Loc.finiteCocycles φ (twist k⁻¹ (mrep M0))` using `hc`. Rewrite `h0`, `hkcr`, the goal using `[← isCr_of_top]`. Use `(crExt φ hφ (mrep M0) (mrep M) (cont_mrep M0 hM0c) (cont_mrep M hM) k (ext0 n) (LinearMap.proj (Fin.last n)) (Pi.single (Fin.last n) 1) c ?_ ?_ (by simp) ?_ ?_ ⊤ isOpen_univ h0 hkcr).2 hc'` and prove the remaining obligations.

Introduce `x y h`. Use function extensionality and compare the values at `j`. Simplify using `using congrFun h j.castSucc`. Introduce `y`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨fun j => y j.castSucc, funext fun j => ?_⟩` and prove the remaining obligations. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => rw [snocZeroLastCoordinate_last]`. Conclude with `h.symm`.

Consider the case `cast j => simp`. Introduce and unpack `⟨x, rfl⟩`. Simplify using the standard rewrite rules. Introduce `g x`. Use function extensionality and compare the values at `j`.

Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`. Simplify using `[mrep_apply, Fin.sum_univ_castSucc, fun j : Fin n => htri g _ _ (Fin.castSucc_lt_last j)]`. Consider the case `cast j => simp [mrep_apply, Fin.sum_univ_castSucc, hM0, topBlock]`. Introduce `g`.

Use function extensionality and compare the values at `j`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp [mrep_apply, Pi.single_apply, hdiag, hk]`. Consider the case `cast j => simp [mrep_apply, Pi.single_apply, c, (Fin.castSucc_lt_last j).ne]`.
-/
private theorem key (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {A : Type} [CommRing A]
    [Algebra E A] [Algebra ℚ_[l] A] [IsScalarTower ℚ_[l] E A] [Module.Finite E A] [Algebra ℤ_[l] A]
    [IsScalarTower ℤ_[l] ℚ_[l] A] [Module.Finite ℚ_[l] A] [TopologicalSpace A] [IsModuleTopology ℚ_[l] A]
    [IsTopologicalRing A] (π : A →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (n : ℕ) :
    ∀ (M : G →* Matrix (Fin n) (Fin n) A), (∀ i j, Continuous fun g => M g i j) →
      ∀ (κ : Fin n → G →* Aˣ) (w : Fin n → ℤ), (∀ g i j, j < i → M g i j = 0) → (∀ g i, M g i i = κ i g) →
      StrictAnti w → (∀ i g, φ g ∈ Iq l → κ i g = cycA l l A (φ g) ^ w i) →
      (∀ i j, i < j → ∃ g, π (κ i g : A) ≠ π (κ j g : A) * (cycA l l E (φ g) : E)) → IsCr φ (mrep M) := by
  induction n with
  | zero =>
    intro M hM κ w _ _ _ _ _
    exact crUnr φ hφ (mrep M) (cont_mrep M hM) 0 fun _ _ _ => Subsingleton.elim _ _
  | succ n ih =>
    intro M hM κ w htri hdiag hw hI hne
    haveI : ContinuousConstSMul E (Fin n → A) := ⟨fun c => IsModuleTopology.continuous_of_linearMap
      ((Algebra.lsmul ℚ_[l] ℚ_[l] (Fin n → A) : E →ₐ[ℚ_[l]] Module.End ℚ_[l] (Fin n → A)) c)⟩
    set M0 := topBlock M htri with hM0
    have hM0c : ∀ i j, Continuous fun g => M0 g i j := fun i j => hM _ _
    have htri0 : ∀ g i j, j < i → M0 g i j = 0 := fun g i j h => htri g _ _ (Fin.castSucc_lt_castSucc_iff.2 h)
    have h0 : IsCr φ (mrep M0) := ih M0 hM0c (fun i => κ i.castSucc) (fun i => w i.castSucc) htri0
      (fun g i => hdiag g _) (fun i j h => hw (Fin.castSucc_lt_castSucc_iff.2 h)) (fun i => hI _)
      (fun i j h => hne _ _ (Fin.castSucc_lt_castSucc_iff.2 h))
    set k := κ (Fin.last n) with hk
    have hkc : Continuous fun g => (k g : A) := by
      simp only [hk, ← hdiag]; exact hM _ _
    have hkc' : Continuous fun g => ((k⁻¹ g : Aˣ) : A) := by
      have : (fun g => ((k⁻¹ g : Aˣ) : A)) = (fun g => (k g : A)) ∘ fun g => g⁻¹ := by
        ext g; simp
      rw [this]; exact hkc.comp continuous_inv
    have hch : ∀ χ : G →* Aˣ, Continuous (fun g => (χ g : A)) → ContAction (chRep χ) := fun χ h =>
      (h.comp continuous_fst).mul continuous_snd
    have hkcr : IsCr φ (chRep k) := crUnr φ hφ _ (hch _ hkc) (w (Fin.last n)) fun g hg x => by
      rw [← hI _ g hg]; rfl
    have hkcr' : IsCr φ (chRep k⁻¹) := crUnr φ hφ _ (hch _ hkc') (-w (Fin.last n)) fun g hg x => by
      rw [zpow_neg, ← hI _ g hg]; rfl
    have htw : ContAction (twist k⁻¹ (mrep M0)) :=
      (hkc'.comp continuous_fst).smul (cont_mrep M0 hM0c)
    have htwcr : IsCr φ (twist k⁻¹ (mrep M0)) := by
      refine (admissible_of_bilinear_openSubgroup_galois φ hφ (chRep k⁻¹) (mrep M0) _ (hch _ hkc') (cont_mrep M0 hM0c) htw
        ((LinearMap.lsmul A (Fin n → A)).restrictScalars₁₂ ℚ_[l] ℚ_[l]) ?_ ?_).1 hkcr' h0
      · intro g x y
        simp [chRep, twist, smul_smul, mul_comm]
      · rw [eq_top_iff]
        intro x _
        exact Submodule.subset_span ⟨(1, x), by simp⟩
    have hπc : ∀ σ, π (cycA l l A σ : A) = (cycA l l E σ : E) := fun σ => by
      simp only [cycA, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] A, IsScalarTower.algebraMap_apply ℚ_[l] E A,
        AlgHom.commutes, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E]
      rfl
    let ψ : Fin n → G →* Eˣ := fun i => (Units.map (π : A →* E)).comp (k⁻¹ * κ i.castSucc)
    have hfil : ∀ S : Set (G →* Eˣ), (∀ i, ψ i ∈ S) → FiltBy (resCoef E (twist k⁻¹ (mrep M0))) S := by
      intro S hS
      refine filt_tri π hπ _ S (fun i g => ((k⁻¹ * κ i.castSucc) g : Aˣ)) (fun i => ⟨ψ i, hS i, fun g => rfl⟩) ?_
      intro g i x hx
      obtain ⟨a, b⟩ := tri_apply M0 htri0 g i x hx
      have e : ∀ j, resCoef E (twist k⁻¹ (mrep M0)) g x j = ((k⁻¹ g : Aˣ) : A) * mrep M0 g x j := fun j => rfl
      refine ⟨fun j hj => by rw [e, a j hj, mul_zero], ?_⟩
      have : M0 g i i = κ i.castSucc g := hdiag g _
      rw [e, b, this]
      simp [mul_assoc]
    have hpos : Positive φ (resCoef E (twist k⁻¹ (mrep M0))) := by
      refine ⟨(isCrys_isDR_restrict_openSubgroup φ hφ _ htw).1 htwcr, hfil _ fun i => ⟨w i.castSucc - w (Fin.last n), ?_, ⊤, isOpen_univ, ?_⟩⟩
      · have := hw (Fin.castSucc_lt_last i)
        omega
      · intro g _ hg
        have e : Units.map (π : A →* E) (cycA l l A (φ g)) = cycA l l E (φ g) := Units.ext (hπc _)
        simp only [ψ, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, hk, hI _ g hg]
        rw [map_mul, map_inv, map_zpow (Units.map (π : A →* E)), map_zpow (Units.map (π : A →* E)), e, zpow_sub]
        exact mul_comm _ _
    have hdual : H0dual ((cycA l l E).comp φ) (resCoef E (twist k⁻¹ (mrep M0))) = ⊥ := by
      refine h0dual_bot (hfil (Set.range ψ) fun i => ⟨i, rfl⟩) _ ?_
      rintro _ ⟨i, rfl⟩
      obtain ⟨g, hg⟩ := hne _ _ (Fin.castSucc_lt_last i)
      refine ⟨g, fun h => hg ?_⟩
      have h' : (ψ i g : E) = (cycA l l E (φ g) : E) := h
      rw [← h']
      change _ = π (k g : A) * π (((k⁻¹ * κ i.castSucc) g : Aˣ) : A)
      rw [← map_mul]
      simp
    have hF := prF hP φ hφ (resCoef E (twist k⁻¹ (mrep M0))) htw hpos hdual
    let c : G → Fin n → A := fun g i => ((k⁻¹ g : Aˣ) : A) * M g i.castSucc (Fin.last n)
    have hc : c ∈ Z1 (resCoef E (twist k⁻¹ (mrep M0))) := by
      refine ⟨continuous_pi fun i => hkc'.mul (hM _ _), fun g h => funext fun i => ?_⟩
      change ((k⁻¹ (g * h) : Aˣ) : A) * M (g * h) i.castSucc (Fin.last n) =
        ((k⁻¹ g : Aˣ) : A) * M g i.castSucc (Fin.last n) + ((k⁻¹ g : Aˣ) : A) *
          ∑ j : Fin n, M g i.castSucc j.castSucc * (((k⁻¹ h : Aˣ) : A) * M h j.castSucc (Fin.last n))
      have e : ((k⁻¹ h : Aˣ) : A) * (k h : A) = 1 := by simp
      have e2 : ∑ j : Fin n, M g i.castSucc j.castSucc * (((k⁻¹ h : Aˣ) : A) * M h j.castSucc (Fin.last n)) =
          ((k⁻¹ h : Aˣ) : A) * ∑ j : Fin n, M g i.castSucc j.castSucc * M h j.castSucc (Fin.last n) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [map_mul, map_mul, Matrix.mul_apply, Fin.sum_univ_castSucc, hdiag, ← hk, Units.val_mul, e2]
      linear_combination ((k⁻¹ g : Aˣ) : A) * M g i.castSucc (Fin.last n) * e
    rw [← hF] at hc
    have hc' : c ∈ UpperTheory.V.Loc.finiteCocycles φ (twist k⁻¹ (mrep M0)) := hc
    rw [← isCr_of_top] at h0 hkcr ⊢
    refine (crExt φ hφ (mrep M0) (mrep M) (cont_mrep M0 hM0c) (cont_mrep M hM) k (ext0 n)
      (LinearMap.proj (Fin.last n)) (Pi.single (Fin.last n) 1) c ?_ ?_ (by simp) ?_ ?_ ⊤ isOpen_univ h0 hkcr).2 hc'
    · intro x y h
      funext j
      simpa using congrFun h j.castSucc
    · intro y
      constructor
      · intro h
        refine ⟨fun j => y j.castSucc, funext fun j => ?_⟩
        induction j using Fin.lastCases with
        | last => rw [snocZeroLastCoordinate_last]; exact h.symm
        | cast j => simp
      · rintro ⟨x, rfl⟩
        simp
    · intro g x
      funext j
      induction j using Fin.lastCases with
      | last =>
        simp [mrep_apply, Fin.sum_univ_castSucc, fun j : Fin n => htri g _ _ (Fin.castSucc_lt_last j)]
      | cast j => simp [mrep_apply, Fin.sum_univ_castSucc, hM0, topBlock]
    · intro g
      funext j
      induction j using Fin.lastCases with
      | last => simp [mrep_apply, Pi.single_apply, hdiag, hk]
      | cast j => simp [mrep_apply, Pi.single_apply, c, (Fin.castSucc_lt_last j).ne]

end UpperTheory.V.Loc.DualInvariantFiltration

open UpperTheory.V.Loc.DualInvariantFiltration in
/- English proof (translation)
Introduce `hP l _ G _ _ _ φ hφ E _ _ _ _ _ A _ _ _ _ _ _ _ π hπ n r hr κ w htri hw hI hne`. Use `letI : TopologicalSpace A := moduleTopology ℚ_[l] A`. Use `haveI : IsModuleTopology ℚ_[l] A := ⟨rfl⟩`. Use `haveI : Module.Finite ℚ_[l] A := Module.Finite.trans E A`. Use `haveI : IsTopologicalRing A := IsModuleTopology.isTopologicalRing ℚ_[l] A`.

Conclude with `key hP φ hφ π hπ n ((Units.coeHom _).comp r) hr κ w (fun g => (htri g).1) (fun g => (htri g).2) hw hI hne`.
-/
theorem UpperTheory.V.Loc.prC :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {A : Type} [CommRing A] [Algebra E A] [Algebra ℚ_[l] A] [IsScalarTower ℚ_[l] E A] [Module.Finite E A] [Algebra ℤ_[l] A] [IsScalarTower ℤ_[l] ℚ_[l] A] (π : A →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ {n : ℕ} (r : G →* GL (Fin n) A), (∀ i j, QCont l fun g => (r g : Matrix (Fin n) (Fin n) A) i j) → ∀ (κ : Fin n → G →* Aˣ) (w : Fin n → ℤ), UpperTri r κ → StrictAnti w → (∀ i g, φ g ∈ Iq l → κ i g = cycA l l A (φ g) ^ w i) → (∀ i j, i < j → ∃ g, π (κ i g : A) ≠ π (κ j g : A) * (cycA l l E (φ g) : E)) → IsCr φ (colRep r) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ A _ _ _ _ _ _ _ π hπ n r hr κ w htri hw hI hne
  letI : TopologicalSpace A := moduleTopology ℚ_[l] A
  haveI : IsModuleTopology ℚ_[l] A := ⟨rfl⟩
  haveI : Module.Finite ℚ_[l] A := Module.Finite.trans E A
  haveI : IsTopologicalRing A := IsModuleTopology.isTopologicalRing ℚ_[l] A
  exact key hP φ hφ π hπ n ((Units.coeHom _).comp r) hr κ w (fun g => (htri g).1) (fun g => (htri g).2) hw hI hne
