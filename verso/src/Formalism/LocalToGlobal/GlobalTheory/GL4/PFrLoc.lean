import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrCore
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

variable (v : HeightOneSpectrum (𝓞 F))

abbrev lv (Λ : Submodule (𝓞 E) (n → E)) : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) Λ

/- English proof (translation)
Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu`. Take `⟨x, hx, rfl⟩` from `hu`. Conclude with `Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero`.

Establish `: (fun i => prV (E` using `E) v ((0 : n → 𝒜) i)) = 0 := by funext i; simp`. Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add u w _ _ hu hw`. Establish `: (fun i => prV (E` using `E) v ((u + w) i)) = (fun i => prV (E := E) v (u i)) + (fun i => prV (E := E) v (w i)) := by funext i; simp`.

Rewrite using `[this]`. Conclude with `add_mem hu hw`. Consider the case `smul s u _ hu`. Establish `hs` using `afsplit_prV_int (E := E) v (s : 𝒜) s.2`. Establish `: (fun i => prV (E` using `E) v ((s • u) i)) = (⟨_, hs⟩ : intV E v) • (fun i => prV (E := E) v (u i)) := by`.

Use function extensionality and compare the values at `i`. Simplify using `[Subring.smul_def, map_mul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hu`.
-/
theorem prV_hat {Λ : Submodule (𝓞 E) (n → E)} (u : n → 𝒜) (hu : u ∈ hat F Λ) :
    (fun i => prV (E := E) v (u i)) ∈ lv v Λ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have : (fun i => prV (E := E) v ((0 : n → 𝒜) i)) = 0 := by funext i; simp
    rw [this]; exact zero_mem _
  | add u w _ _ hu hw =>
    have : (fun i => prV (E := E) v ((u + w) i)) =
        (fun i => prV (E := E) v (u i)) + (fun i => prV (E := E) v (w i)) := by funext i; simp
    rw [this]; exact add_mem hu hw
  | smul s u _ hu =>
    have hs := afsplit_prV_int (E := E) v (s : 𝒜) s.2
    have : (fun i => prV (E := E) v ((s • u) i)) =
        (⟨_, hs⟩ : intV E v) • (fun i => prV (E := E) v (u i)) := by
      funext i
      simp [Subring.smul_def, map_mul]
    rw [this]; exact Submodule.smul_mem _ _ hu

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
theorem bc_mulVec_vi (k : GL n 𝒜) (x : n → E) :
    ((bc (prV (E := E) v) k : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n _) *ᵥ
      (fun i => inclE (F := F) (v.adicCompletion F) (x i)) =
      fun i => prV (E := E) v (((k : Matrix n n 𝒜) *ᵥ vi F x) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x, hx, rfl⟩` from `hy`. Rewrite using `[bc_mulVec_vi]`. Conclude with `prV_hat v _ (hk _ (vi_mem_hat hx))`.

Consider the case `zero => rw [mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add y w _ _ hy hw => rw [mulVec_add]`. Conclude with `add_mem hy hw`. Consider the case `smul t y _ hy`.

Rewrite using `[Subring.smul_def, mulVec_smul]`. Conclude with `Submodule.smul_mem _ t hy`.
-/
theorem loc_fwd {Λ Λ' : Submodule (𝓞 E) (n → E)} (k : GL n 𝒜) (hk : ∀ u ∈ hat F Λ, (k : Matrix n n 𝒜) *ᵥ u ∈ hat F Λ')
    (y : n → E ⊗[F] v.adicCompletion F) (hy : y ∈ lv v Λ) :
    ((bc (prV (E := E) v) k : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n _) *ᵥ y ∈ lv v Λ' := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [bc_mulVec_vi]
    exact prV_hat v _ (hk _ (vi_mem_hat hx))
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add y w _ _ hy hw => rw [mulVec_add]; exact add_mem hy hw
  | smul t y _ hy =>
    rw [Subring.smul_def, mulVec_smul]
    exact Submodule.smul_mem _ t hy

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x, hx, rfl⟩` from `hy`. Take `⟨z, hz, hze⟩` from `hk _ (vi_mem_hat hx)`. Use `⟨fun i => prV (E := E) v (z i), prV_hat v z hz, ?_⟩` and prove the remaining obligations.

Rewrite using `[bc_mulVec_vi]`. Use function extensionality and compare the values at `i`. Use `congrFun hze i` as an intermediate fact. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢`. Rewrite using `[← afsplit_prV_inclE, ← map_sub, show (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) (x i) = vi F x i from rfl, this, map_mul, map_natCast]`.

Consider the case `zero => exact ⟨0, zero_mem _, by rw [mulVec_zero, sub_zero, smul_zero]⟩`. Consider the case `add y w _ _ hy hw`. Take `⟨z, hz, hze⟩` from `hy`. Take `⟨z', hz', hze'⟩` from `hw`. Use `⟨z + z', add_mem hz hz', ?_⟩` and prove the remaining obligations.

Rewrite using `[mulVec_add, smul_add, ← hze, ← hze']`. Normalize the expressions using the abelian group laws. Consider the case `smul t y _ hy`. Take `⟨z, hz, hze⟩` from `hy`. Use `⟨t • z, Submodule.smul_mem _ t hz, ?_⟩` and prove the remaining obligations.

Rewrite using `[Subring.smul_def, Subring.smul_def, mulVec_smul, ← smul_sub, hze, smul_comm]`.
-/
theorem loc_cong {Λ Λ' : Submodule (𝓞 E) (n → E)} (k : GL n 𝒜) (M : ℕ)
    (hk : ∀ u ∈ hat F Λ, ∃ z ∈ hat F Λ', (k : Matrix n n 𝒜) *ᵥ u - u = (M : 𝒜) • z)
    (y : n → E ⊗[F] v.adicCompletion F) (hy : y ∈ lv v Λ) :
    ∃ z ∈ lv v Λ', ((bc (prV (E := E) v) k : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n _) *ᵥ y - y =
      (M : E ⊗[F] v.adicCompletion F) • z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨z, hz, hze⟩ := hk _ (vi_mem_hat hx)
    refine ⟨fun i => prV (E := E) v (z i), prV_hat v z hz, ?_⟩
    rw [bc_mulVec_vi]
    funext i
    have := congrFun hze i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← afsplit_prV_inclE, ← map_sub, show (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) (x i) = vi F x i from rfl,
      this, map_mul, map_natCast]
  | zero => exact ⟨0, zero_mem _, by rw [mulVec_zero, sub_zero, smul_zero]⟩
  | add y w _ _ hy hw =>
    obtain ⟨z, hz, hze⟩ := hy
    obtain ⟨z', hz', hze'⟩ := hw
    refine ⟨z + z', add_mem hz hz', ?_⟩
    rw [mulVec_add, smul_add, ← hze, ← hze']
    abel
  | smul t y _ hy =>
    obtain ⟨z, hz, hze⟩ := hy
    refine ⟨t • z, Submodule.smul_mem _ t hz, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, mulVec_smul, ← smul_sub, hze, smul_comm]

/- English proof (translation)
Use `Submodule.smul_mem (lv v Λ) (N : intV E v) hz` as an intermediate fact. Rewrite `this` using `[Subring.smul_def, Subring.coe_natCast]`. Then use the resulting hypothesis.
-/
theorem natCast_smul_mem {Λ : Submodule (𝓞 E) (n → E)} (N : ℕ) {z : n → E ⊗[F] v.adicCompletion F}
    (hz : z ∈ lv v Λ) : (N : E ⊗[F] v.adicCompletion F) • z ∈ lv v Λ := by
  have := Submodule.smul_mem (lv v Λ) (N : intV E v) hz
  rwa [Subring.smul_def, Subring.coe_natCast] at this

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨x, hx, rfl⟩` from `hz`. Use `Submodule.subset_span ⟨t • x, ht x hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `[map_mul]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add z w _ _ hz hw => rw [smul_add]`. Conclude with `add_mem hz hw`.

Consider the case `smul s z _ hz`. Rewrite using `[Subring.smul_def, smul_comm]`. Conclude with `Submodule.smul_mem _ s hz`.
-/
theorem smul_lv_of {Λ Λ' : Submodule (𝓞 E) (n → E)} (t : E) (ht : ∀ x ∈ Λ, t • x ∈ Λ')
    {z : n → E ⊗[F] v.adicCompletion F} (hz : z ∈ lv v Λ) :
    inclE (F := F) (v.adicCompletion F) t • z ∈ lv v Λ' := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨t • x, ht x hx, ?_⟩
    funext i
    simp [map_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z w _ _ hz hw => rw [smul_add]; exact add_mem hz hw
  | smul s z _ hz =>
    rw [Subring.smul_def, smul_comm]
    exact Submodule.smul_mem _ s hz

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Conclude with `loc_fwd v k (fun u hu => (hk u).1 hu) x`. Introduce `hx`. Establish `hk' : ∀ u ∈ hat F Λ, ((k⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F Λ`. Introduce `u hu`.

Use `(hk _).2 ?_` and prove the remaining obligations. Rewrite using `[mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]`. Conclude with `hu`. Establish `h` using `loc_fwd v k⁻¹ hk' _ hx`. Rewrite `h` using `[map_inv, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]`. Then use the resulting hypothesis.
-/
theorem loc_stab {Λ : Submodule (𝓞 E) (n → E)} (k : GL n 𝒜)
    (hk : ∀ u : n → 𝒜, u ∈ hat F Λ ↔ (k : Matrix n n 𝒜) *ᵥ u ∈ hat F Λ) (x : n → E ⊗[F] v.adicCompletion F) :
    x ∈ lv v Λ ↔ ((bc (prV (E := E) v) k : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n _) *ᵥ x ∈ lv v Λ := by
  constructor
  · exact loc_fwd v k (fun u hu => (hk u).1 hu) x
  · intro hx
    have hk' : ∀ u ∈ hat F Λ, ((k⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F Λ := by
      intro u hu
      refine (hk _).2 ?_
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      exact hu
    have h := loc_fwd v k⁻¹ hk' _ hx
    rwa [map_inv, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at h

end Loc

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F

open Formalism.L2.Herm in

/- English proof (translation)
Rewrite using `[lev.U_eq]`. Use `⟨hkU, fun v => ?_⟩` and prove the remaining obligations. Establish `hlev : bc (prV (E` using `E) v) k ∈ levelVL hc.sig S.gram v lev.Lb := Subgroup.mem_inf.2 ⟨afsplit_bc_mem hc.sig S.gram v k hkU, fun x => loc_stab v k hst x⟩`. Establish `hTd : ∀ x ∈ dualL hc S lev.Lb, (T : E) • x ∈ lev.Lb` using `lev.Lb_dual`. Establish `hTz : ∀ z ∈ lv v (dualL hc S lev.Lb), (T : E ⊗[F] v.adicCompletion F) • z ∈ lv v lev.Lb`.

Introduce `z hz`. Use `smul_lv_of v (T : E) hTd hz` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hmono : lv v lev.Lb ≤ lv v (dualL hc S lev.Lb)` using `Submodule.span_mono (Set.image_mono lev.Lb_int)`. Distinguish the cases in `hTv : (T : 𝓞 F) ∈ v.asIdeal`.

Rewrite using `[lev.UlocAlt v hTv]`. Use `⟨hlev, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, hze⟩` from `loc_cong v k _ hcg y hy`. Rewrite using `[hze, show ((T * gp 0 * gp 1 : ℕ) : E ⊗[F] v.adicCompletion F) = ((gp 0 * gp 1 : ℕ) : E ⊗[F] v.adicCompletion F) * (T : E ⊗[F] v.adicCompletion F) by push_cast; ring, mul_smul]`. Conclude with `natCast_smul_mem v _ (hTz z hz)`.

Distinguish the cases in `hg0 : (gp 0 : 𝓞 F) ∈ v.asIdeal`. Use `lev.Uloc_g 0 v hg0 _ ⟨hlev, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, hze⟩` from `loc_cong v k _ hcg y (hmono hy)`. Use `⟨((gp 1 : ℕ) : E ⊗[F] v.adicCompletion F) • ((T : E ⊗[F] v.adicCompletion F) • z), natCast_smul_mem v _ (hTz z hz), ?_⟩` and prove the remaining obligations. Rewrite using `[hze, smul_smul, smul_smul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hg1 : (gp 1 : 𝓞 F) ∈ v.asIdeal`. Use `lev.Uloc_g 1 v hg1 _ ⟨hlev, fun y hy => ?_⟩` and prove the remaining obligations.

Take `⟨z, hz, hze⟩` from `loc_cong v k _ hcg y (hmono hy)`. Use `⟨((gp 0 : ℕ) : E ⊗[F] v.adicCompletion F) • ((T : E ⊗[F] v.adicCompletion F) • z), natCast_smul_mem v _ (hTz z hz), ?_⟩` and prove the remaining obligations. Rewrite using `[hze, smul_smul, smul_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[lev.Uloc_hyp v hg0 hg1 hTv]`. Conclude with `hlev`.
-/
theorem stepLevel_mem {hc : CMData F E} {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ}
    (lev : StepLevel hc S gp T f) (k : GL (Fin S.rank) 𝒜) (hkU : k ∈ UAf hc S)
    (hst : ∀ u, u ∈ hat F lev.Lb ↔ (k : Matrix (Fin S.rank) (Fin S.rank) 𝒜) *ᵥ u ∈ hat F lev.Lb)
    (hcg : ∀ u ∈ hat F (dualL hc S lev.Lb), ∃ z ∈ hat F (dualL hc S lev.Lb),
      (k : Matrix (Fin S.rank) (Fin S.rank) 𝒜) *ᵥ u - u = ((T * gp 0 * gp 1 : ℕ) : 𝒜) • z) :
    k ∈ lev.U := by
  rw [lev.U_eq]
  refine ⟨hkU, fun v => ?_⟩
  have hlev : bc (prV (E := E) v) k ∈ levelVL hc.sig S.gram v lev.Lb :=
    Subgroup.mem_inf.2 ⟨afsplit_bc_mem hc.sig S.gram v k hkU, fun x => loc_stab v k hst x⟩
  have hTd : ∀ x ∈ dualL hc S lev.Lb, (T : E) • x ∈ lev.Lb := lev.Lb_dual
  have hTz : ∀ z ∈ lv v (dualL hc S lev.Lb), (T : E ⊗[F] v.adicCompletion F) • z ∈ lv v lev.Lb := by
    intro z hz
    have := smul_lv_of v (T : E) hTd hz
    rwa [map_natCast] at this
  have hmono : lv v lev.Lb ≤ lv v (dualL hc S lev.Lb) := Submodule.span_mono (Set.image_mono lev.Lb_int)
  by_cases hTv : (T : 𝓞 F) ∈ v.asIdeal
  · rw [lev.UlocAlt v hTv]
    refine ⟨hlev, fun y hy => ?_⟩
    obtain ⟨z, hz, hze⟩ := loc_cong v k _ hcg y hy
    rw [hze, show ((T * gp 0 * gp 1 : ℕ) : E ⊗[F] v.adicCompletion F) = ((gp 0 * gp 1 : ℕ) : E ⊗[F] v.adicCompletion F) *
      (T : E ⊗[F] v.adicCompletion F) by push_cast; ring, mul_smul]
    exact natCast_smul_mem v _ (hTz z hz)
  by_cases hg0 : (gp 0 : 𝓞 F) ∈ v.asIdeal
  · refine lev.Uloc_g 0 v hg0 _ ⟨hlev, fun y hy => ?_⟩
    obtain ⟨z, hz, hze⟩ := loc_cong v k _ hcg y (hmono hy)
    refine ⟨((gp 1 : ℕ) : E ⊗[F] v.adicCompletion F) • ((T : E ⊗[F] v.adicCompletion F) • z),
      natCast_smul_mem v _ (hTz z hz), ?_⟩
    rw [hze, smul_smul, smul_smul]
    congr 1
    push_cast; ring
  by_cases hg1 : (gp 1 : 𝓞 F) ∈ v.asIdeal
  · refine lev.Uloc_g 1 v hg1 _ ⟨hlev, fun y hy => ?_⟩
    obtain ⟨z, hz, hze⟩ := loc_cong v k _ hcg y (hmono hy)
    refine ⟨((gp 0 : ℕ) : E ⊗[F] v.adicCompletion F) • ((T : E ⊗[F] v.adicCompletion F) • z),
      natCast_smul_mem v _ (hTz z hz), ?_⟩
    rw [hze, smul_smul, smul_smul]
    congr 1
    push_cast; ring
  rw [lev.Uloc_hyp v hg0 hg1 hTv]
  exact hlev

open Formalism.L2.Herm in

/- English proof (translation)
Rewrite using `[lev.U_eq]`. Use `⟨hkU, fun v => ?_⟩` and prove the remaining obligations. Establish `hlev : bc (prV (E` using `E) v) k ∈ levelVL hc.sig S.gram v Lb := Subgroup.mem_inf.2 ⟨afsplit_bc_mem hc.sig S.gram v k hkU, fun x => loc_stab v k hst x⟩`. Rewrite `hcg` using `[hsd]`. Distinguish the cases in `hg0 : (gp 0 : 𝓞 F) ∈ v.asIdeal`.

Use `lev.Uloc_g 0 v hg0 _ ⟨hlev, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, hze⟩` from `loc_cong v k _ hcg y hy`. Use `⟨((T * gp 1 : ℕ) : E ⊗[F] v.adicCompletion F) • z, natCast_smul_mem v _ hz, ?_⟩` and prove the remaining obligations. Rewrite using `[hze, smul_smul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hg1 : (gp 1 : 𝓞 F) ∈ v.asIdeal`. Use `lev.Uloc_g 1 v hg1 _ ⟨hlev, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, hze⟩` from `loc_cong v k _ hcg y hy`.

Use `⟨((T * gp 0 : ℕ) : E ⊗[F] v.adicCompletion F) • z, natCast_smul_mem v _ hz, ?_⟩` and prove the remaining obligations. Rewrite using `[hze, smul_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[lev.Uloc_hyp v hg0 hg1]`. Conclude with `hlev`.
-/
theorem stepLevel0_mem {hc : CMData F E} {S : HSpace E} {gp : Fin 2 → ℕ} {Lb : Submodule (𝓞 E) (Fin S.rank → E)}
    (hsd : dualL hc S Lb = Lb) (lev : StepLevel0 hc S gp Lb) (T : ℕ) (k : GL (Fin S.rank) 𝒜) (hkU : k ∈ UAf hc S)
    (hst : ∀ u, u ∈ hat F Lb ↔ (k : Matrix (Fin S.rank) (Fin S.rank) 𝒜) *ᵥ u ∈ hat F Lb)
    (hcg : ∀ u ∈ hat F (dualL hc S Lb), ∃ z ∈ hat F (dualL hc S Lb),
      (k : Matrix (Fin S.rank) (Fin S.rank) 𝒜) *ᵥ u - u = ((T * gp 0 * gp 1 : ℕ) : 𝒜) • z) :
    k ∈ lev.U := by
  rw [lev.U_eq]
  refine ⟨hkU, fun v => ?_⟩
  have hlev : bc (prV (E := E) v) k ∈ levelVL hc.sig S.gram v Lb :=
    Subgroup.mem_inf.2 ⟨afsplit_bc_mem hc.sig S.gram v k hkU, fun x => loc_stab v k hst x⟩
  rw [hsd] at hcg
  by_cases hg0 : (gp 0 : 𝓞 F) ∈ v.asIdeal
  · refine lev.Uloc_g 0 v hg0 _ ⟨hlev, fun y hy => ?_⟩
    obtain ⟨z, hz, hze⟩ := loc_cong v k _ hcg y hy
    refine ⟨((T * gp 1 : ℕ) : E ⊗[F] v.adicCompletion F) • z, natCast_smul_mem v _ hz, ?_⟩
    rw [hze, smul_smul]
    congr 1
    push_cast; ring
  by_cases hg1 : (gp 1 : 𝓞 F) ∈ v.asIdeal
  · refine lev.Uloc_g 1 v hg1 _ ⟨hlev, fun y hy => ?_⟩
    obtain ⟨z, hz, hze⟩ := loc_cong v k _ hcg y hy
    refine ⟨((T * gp 0 : ℕ) : E ⊗[F] v.adicCompletion F) • z, natCast_smul_mem v _ hz, ?_⟩
    rw [hze, smul_smul]
    congr 1
    push_cast; ring
  rw [lev.Uloc_hyp v hg0 hg1]
  exact hlev

end Lev

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

end
