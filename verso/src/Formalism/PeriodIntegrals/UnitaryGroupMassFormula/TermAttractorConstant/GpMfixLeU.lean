import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GpLocPSubE

noncomputable section

open scoped Classical

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula
  IsDedekindDomain

section GP2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V}

def gpMfix (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) : Submodule (𝓞 E) S.V :=
  Submodule.span (𝓞 E) ((XLam Λ F : Set S.V) ∪ {F.zt})

def gpGen (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (b : Fin (r + 1)) : S.V :=
  ((g : E)⁻¹) • (frame F' b - frameAct (frame F) ξ b)

def gpU (F : LFlag S r T) : Submodule E S.V := Xsp F ⊔ Submodule.span E {F.fl.z}

/- English proof (translation)
Unfold `Mplus gpMfix gpGen`. Rewrite using `[Submodule.span_union]`.
-/
theorem gp_mplus_eq (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T')
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) :
    Mplus Λ g F F' ξ = gpMfix Λ F ⊔ Submodule.span (𝓞 E) (Set.range (gpGen g F F' ξ)) := by
  unfold Mplus gpMfix gpGen
  rw [Submodule.span_union]

/- English proof (translation)
Establish `key : ∀ b, ∀ x ∈ Xsp F, S.hT x (F.fl.e b) = 0`. Introduce `b x hx`. Simplify using `only [Xsp, Formalism.MainNotions.S.FlagG.X] at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨a, rfl⟩` from `hy`. Conclude with `F.fl.e_iso a b`. Consider the case `zero => simp`. Consider the case `add y y' _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]`. Consider the case `smul c y _ h => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h, smul_zero]`.

Introduce `v hv`. Rewrite using `[mem_orth_iff]`. Introduce `x hx`. Simplify using `only [Xsp, Formalism.MainNotions.S.FlagG.X] at hv`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨b, rfl⟩` from `hy`. Conclude with `key b x hx`. Consider the case `zero => simp`. Consider the case `add y y' _ _ h1 h2 => rw [map_add, h1, h2, add_zero]`.

Consider the case `smul c y _ h => rw [map_smul, h, smul_zero]`.
-/
theorem gp_X_iso (F : LFlag S r T) : ∀ v ∈ Xsp F, v ∈ orth S (Xsp F) := by
  have key : ∀ b, ∀ x ∈ Xsp F, S.hT x (F.fl.e b) = 0 := by
    intro b x hx
    dsimp only [Xsp, Formalism.MainNotions.S.FlagG.X] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact F.fl.e_iso a b
    | zero => simp
    | add y y' _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
    | smul c y _ h => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h, smul_zero]
  intro v hv
  rw [mem_orth_iff]
  intro x hx
  dsimp only [Xsp, Formalism.MainNotions.S.FlagG.X] at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact key b x hx
  | zero => simp
  | add y y' _ _ h1 h2 => rw [map_add, h1, h2, add_zero]
  | smul c y _ h => rw [map_smul, h, smul_zero]

/- English proof (translation)
Establish `h : gpMfix Λ F ≤ toO S (gpU F)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w (hw | hw)`. Conclude with `Submodule.mem_sup_left (mem_XLam.1 hw).2`. Rewrite `hw` using `[Set.mem_singleton_iff]`.

Rewrite using `[hw, hl.2]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Conclude with `fun w hw => h hw`.
-/
theorem gp_Mfix_le_U (F : LFlag S r T) (hl : IsLift Λ F) : ∀ w ∈ gpMfix Λ F, w ∈ gpU F := by
  have h : gpMfix Λ F ≤ toO S (gpU F) := by
    refine Submodule.span_le.2 ?_
    rintro w (hw | hw)
    · exact Submodule.mem_sup_left (mem_XLam.1 hw).2
    · rw [Set.mem_singleton_iff] at hw
      rw [hw, hl.2]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  exact fun w hw => h hw

/- English proof (translation)
Introduce `w hw hU`. Take `⟨s, hs, hsw⟩` from `(mem_localization_iff p Λ w).1 hw`. Take `⟨u, hu, v, hv, rfl⟩` from `Submodule.mem_sup.1 hU`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hv`. Establish `hzΛ : F.fl.z ∈ Λ` using `hl.1`.

Establish `horth : s • (u + c • F.fl.z) ∈ orth S (Xsp F)`. Rewrite using `[gp_osmul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.add_mem _ (gp_X_iso F u hu) (Submodule.smul_mem _ _ (z_mem_orth F)))`. Establish `hLsub : (algebraMap (𝓞 E) E s * c) • F.fl.z ∈ Lsub Λ F`. Unfold `Lsub Lrep`.

Rewrite using `[Submodule.mem_inf]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_sup]`. Use `⟨s • (u + c • F.fl.z), ?_, -((algebraMap (𝓞 E) E s) • u), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_inf]`.

Conclude with `⟨hsw, (Submodule.restrictScalars_mem _ _ _).2 horth⟩`. Rewrite using `[Submodule.restrictScalars_mem]`. Conclude with `Submodule.neg_mem _ (Submodule.smul_mem _ _ hu)`. Rewrite using `[gp_osmul, smul_add, smul_smul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[Submodule.restrictScalars_mem]`. Conclude with `Submodule.smul_mem _ _ (z_mem_orth F)`. Take `⟨o, ho⟩` from `hprim _ hLsub`. Establish `heq : s • (u + c • F.fl.z) = (algebraMap (𝓞 E) E s) • u + o • F.fl.z`. Establish `: o • F.fl.z = (algebraMap (𝓞 E) E s * c) • F.fl.z`.

Rewrite using `[gp_osmul]`. Conclude with `congrArg (· • F.fl.z) ho`. Rewrite using `[this, gp_osmul, smul_add, smul_smul]`. Establish `hoz : o • F.fl.z ∈ Λ` using `Submodule.smul_mem _ o hzΛ`. Establish `hsu : (algebraMap (𝓞 E) E s) • u ∈ XLam Λ F`.

Use `mem_XLam.2 ⟨?_, Submodule.smul_mem _ _ hu⟩` and prove the remaining obligations. Establish `: (algebraMap (𝓞 E) E s) • u = s • (u + c • F.fl.z) - o • F.fl.z` using `by rw [heq]; abel`. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ hsw hoz`. Use `(mem_localization_iff p _ _).2 ⟨s, hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[heq]`. Use `Submodule.add_mem _ (Submodule.subset_span (Set.mem_union_left _ hsu)) ?_` and prove the remaining obligations. Use `Submodule.smul_mem _ o (Submodule.subset_span (Set.mem_union_right _ ?_))` and prove the remaining obligations. Rewrite using `[Set.mem_singleton_iff, hl.2]`.
-/
theorem gp_sat (p : Ideal (𝓞 E)) [p.IsPrime] (F : LFlag S r T) (hl : IsLift Λ F)
    (hprim : ∀ c : E, c • F.fl.z ∈ Lsub Λ F → ∃ o : 𝓞 E, (o : E) = c) :
    ∀ w ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ, w ∈ gpU F → w ∈ Formalism.HermitianLatticesTheory.localization₂ p (gpMfix Λ F) := by
  intro w hw hU
  obtain ⟨s, hs, hsw⟩ := (mem_localization_iff p Λ w).1 hw
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hU
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  have hzΛ : F.fl.z ∈ Λ := hl.1
  have horth : s • (u + c • F.fl.z) ∈ orth S (Xsp F) := by
    rw [gp_osmul]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (gp_X_iso F u hu)
      (Submodule.smul_mem _ _ (z_mem_orth F)))
  have hLsub : (algebraMap (𝓞 E) E s * c) • F.fl.z ∈ Lsub Λ F := by
    unfold Lsub Lrep
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [Submodule.mem_sup]
      refine ⟨s • (u + c • F.fl.z), ?_, -((algebraMap (𝓞 E) E s) • u), ?_, ?_⟩
      · rw [Submodule.mem_inf]
        exact ⟨hsw, (Submodule.restrictScalars_mem _ _ _).2 horth⟩
      · rw [Submodule.restrictScalars_mem]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hu)
      · rw [gp_osmul, smul_add, smul_smul]
        abel
    · rw [Submodule.restrictScalars_mem]
      exact Submodule.smul_mem _ _ (z_mem_orth F)
  obtain ⟨o, ho⟩ := hprim _ hLsub
  have heq : s • (u + c • F.fl.z) = (algebraMap (𝓞 E) E s) • u + o • F.fl.z := by
    have : o • F.fl.z = (algebraMap (𝓞 E) E s * c) • F.fl.z := by
      rw [gp_osmul]
      exact congrArg (· • F.fl.z) ho
    rw [this, gp_osmul, smul_add, smul_smul]
  have hoz : o • F.fl.z ∈ Λ := Submodule.smul_mem _ o hzΛ
  have hsu : (algebraMap (𝓞 E) E s) • u ∈ XLam Λ F := by
    refine mem_XLam.2 ⟨?_, Submodule.smul_mem _ _ hu⟩
    have : (algebraMap (𝓞 E) E s) • u = s • (u + c • F.fl.z) - o • F.fl.z := by rw [heq]; abel
    rw [this]
    exact Submodule.sub_mem _ hsw hoz
  refine (mem_localization_iff p _ _).2 ⟨s, hs, ?_⟩
  rw [heq]
  refine Submodule.add_mem _ (Submodule.subset_span (Set.mem_union_left _ hsu)) ?_
  refine Submodule.smul_mem _ o (Submodule.subset_span (Set.mem_union_right _ ?_))
  rw [Set.mem_singleton_iff, hl.2]

end GP2

end PI.TermAttrConst.UnitaryGroupMassFormula
