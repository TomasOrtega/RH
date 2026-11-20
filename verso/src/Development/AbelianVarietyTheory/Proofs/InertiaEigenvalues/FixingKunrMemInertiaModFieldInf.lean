import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedFieldOfMemMaxUnramifiedSupRootStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.InertiaMod

open scoped Pointwise

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ofGQ_apply (g : GQ l) (x : Om l) : Formalism.MainNotions.N.PreambleDegrees.Loc.ofGQ g x = g x := rfl

/- English proof (translation)
Rewrite `hx`, the goal using `[← Formalism.MainNotions.N.PreambleDegrees.Loc.Kur_eq]`. Establish `h` using `ReciprocityTheory.DiscreteGroups.LocalClassField.Kur_stable (p := l) (K := Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l) (Formalism.MainNotions.N.PreambleDegrees.Loc.ofGQ g) x hx`. Rewrite `h` using `[ofGQ_apply]`. Conclude with `h`.
-/
theorem Kur_stable (g : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : g x ∈ MaximalUnramifiedExtension l := by
  rw [← Formalism.MainNotions.N.PreambleDegrees.Loc.Kur_eq] at hx ⊢
  have h := ReciprocityTheory.DiscreteGroups.LocalClassField.Kur_stable (p := l) (K := Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l) (Formalism.MainNotions.N.PreambleDegrees.Loc.ofGQ g) x hx
  rw [ofGQ_apply] at h
  exact h

/- English proof (translation)
Establish `hmem : Formalism.MainNotions.N.PreambleDegrees.Loc.ofGQ n ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.subG l (Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l) (ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l (Formalism.MainNotions.N.PreambleD …`. Rewrite using `[ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_iff]`. Introduce `x hx`. Rewrite `hx` using `[Formalism.MainNotions.N.PreambleDegrees.Loc.Kur_eq]`. Rewrite using `[ofGQ_apply]`.

Conclude with `hn x hx`. Introduce `x hx`. Establish `h` using `(ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_Kur_iff (p := l) (K := Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l) Formalism.MainNotions.N.PreambleDegrees.Loc.finiteDimensional_Q0_alt _).1 hmem x hx`. Rewrite `h` using `[ofGQ_apply]`. Conclude with `h`.
-/
theorem resid_of_fix (n : GQ l) (hn : ∀ x ∈ MaximalUnramifiedExtension l, n x = x) :
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖n x - x‖ < 1 := by
  have hmem : Formalism.MainNotions.N.PreambleDegrees.Loc.ofGQ n ∈
      ReciprocityTheory.DiscreteGroups.LocalClassField.subG l (Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l)
        (ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l (Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l)) := by
    rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_iff]
    intro x hx
    rw [Formalism.MainNotions.N.PreambleDegrees.Loc.Kur_eq] at hx
    rw [ofGQ_apply]
    exact hn x hx
  intro x hx
  have h := (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_Kur_iff (p := l) (K := Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l)
    Formalism.MainNotions.N.PreambleDegrees.Loc.finiteDimensional_Q0_alt _).1 hmem x hx
  rw [ofGQ_apply] at h
  exact h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `n hn τ`. Rewrite `hn`, the goal using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Rewrite using `[AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ (Kur_stable τ⁻¹ hx), ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]`.
-/
theorem fix_Kur_normal : ((MaximalUnramifiedExtension l).fixingSubgroup : Subgroup (GQ l)).Normal := by
  constructor
  intro n hn τ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ (Kur_stable τ⁻¹ hx), ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

/- English proof (translation)
Establish `hG : σ ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l)`. Rewrite using `[GK, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Take `⟨a, rfl⟩` from `IntermediateField.mem_bot.1 hx`. Conclude with `σ.commutes a`.

Conclude with `⟨⟨σ, hG⟩, Subgroup.subset_closure (fun x hx => resid_of_fix σ hσ x hx), rfl⟩`.
-/
theorem mem_IK_of_fix (σ : GQ l) (hσ : ∀ x ∈ MaximalUnramifiedExtension l, σ x = x) :
    ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), (k' : GQ l) = σ := by
  have hG : σ ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact σ.commutes a
  exact ⟨⟨σ, hG⟩, Subgroup.subset_closure (fun x hx => resid_of_fix σ hσ x hx), rfl⟩

/- English proof (translation)
Use `haveI := fix_Kur_normal (l := l)`. Set `S : Subgroup (GQ l)` to `M.fixingSubgroup ⊔ (MaximalUnramifiedExtension l).fixingSubgroup`. Establish `hSc : IsClosed (S : Set (GQ l))`. Rewrite using `[Subgroup.mul_normal]`. Conclude with `IsClosed.mul_left_of_isCompact (InfiniteGalois.fixingSubgroup_isClosed _) (InfiniteGalois.fixingSubgroup_isClosed M).isCompact`.

Establish `hfS : (IntermediateField.fixedField S).fixingSubgroup = S` using `InfiniteGalois.fixingSubgroup_fixedField ⟨S, hSc⟩`. Establish `hgS : g ∈ S`. Rewrite using `[← hfS, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Rewrite `hx` using `[IntermediateField.mem_fixedField_iff]`.

Apply `hg` to reduce the goal to its premises. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup M, IntermediateField.mem_fixedField_iff]`. Conclude with `fun σ hσ => hx σ (Subgroup.mem_sup_left hσ)`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]`. Conclude with `fun σ hσ => hx σ (Subgroup.mem_sup_right hσ)`.

Establish `hgNH : g ∈ ((M.fixingSubgroup : Set (GQ l)) * ((MaximalUnramifiedExtension l).fixingSubgroup : Set (GQ l)))`. Rewrite using `[← Subgroup.mul_normal]`. Conclude with `hgS`. Take `⟨u, hu, n, hn, hun⟩` from `Set.mem_mul.1 hgNH`. Use `⟨u⁻¹, M.fixingSubgroup.inv_mem hu, ?_⟩` and prove the remaining obligations.

Establish `hmem : g * u⁻¹ ∈ (MaximalUnramifiedExtension l).fixingSubgroup`. Rewrite using `[← hun]`. Conclude with `(inferInstance : (MaximalUnramifiedExtension l).fixingSubgroup.Normal).conj_mem n hn u`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem`.
-/
theorem exists_fix_Kur (M : IntermediateField ℚ_[l] (Om l)) (g : GQ l)
    (hg : ∀ x ∈ M, x ∈ MaximalUnramifiedExtension l → g x = x) :
    ∃ h ∈ M.fixingSubgroup, ∀ x ∈ MaximalUnramifiedExtension l, (g * h) x = x := by
  haveI := fix_Kur_normal (l := l)
  let S : Subgroup (GQ l) := M.fixingSubgroup ⊔ (MaximalUnramifiedExtension l).fixingSubgroup
  have hSc : IsClosed (S : Set (GQ l)) := by
    rw [Subgroup.mul_normal]
    exact IsClosed.mul_left_of_isCompact (InfiniteGalois.fixingSubgroup_isClosed _)
      (InfiniteGalois.fixingSubgroup_isClosed M).isCompact
  have hfS : (IntermediateField.fixedField S).fixingSubgroup = S :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨S, hSc⟩
  have hgS : g ∈ S := by
    rw [← hfS, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    apply hg
    · rw [← InfiniteGalois.fixedField_fixingSubgroup M, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => hx σ (Subgroup.mem_sup_left hσ)
    · rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => hx σ (Subgroup.mem_sup_right hσ)
  have hgNH : g ∈ ((M.fixingSubgroup : Set (GQ l)) * ((MaximalUnramifiedExtension l).fixingSubgroup : Set (GQ l))) := by
    rw [← Subgroup.mul_normal]; exact hgS
  obtain ⟨u, hu, n, hn, hun⟩ := Set.mem_mul.1 hgNH
  refine ⟨u⁻¹, M.fixingSubgroup.inv_mem hu, ?_⟩
  have hmem : g * u⁻¹ ∈ (MaximalUnramifiedExtension l).fixingSubgroup := by
    rw [← hun]
    exact (inferInstance : (MaximalUnramifiedExtension l).fixingSubgroup.Normal).conj_mem n hn u
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => show ϖ.seq (m + k + 1) ^ l ^ (k + 1) = _`. Rewrite using `[pow_succ', pow_mul, ϖ.seq_succ, ih]`.
-/
theorem seq_add_pow {e : ℕ} (ϖ : PiSys l e) (m k : ℕ) : ϖ.seq (m + k) ^ l ^ k = ϖ.seq m := by
  induction k with
  | zero => simp
  | succ k ih =>
    show ϖ.seq (m + k + 1) ^ l ^ (k + 1) = _
    rw [pow_succ', pow_mul, ϖ.seq_succ, ih]

/- English proof (translation)
Set `F : ℕ → IntermediateField ℚ_[l] (Om l)` to `fun n => Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n}`. Establish `hs : ∀ n, ϖ.seq n ∈ F n` using `fun n => (le_sup_right : _ ≤ F n) (IntermediateField.mem_adjoin_simple_self _ _)`. Establish `hseq : ∀ m k, ϖ.seq m ∈ F (m + k)`. Introduce `m k`. Rewrite using `[← seq_add_pow ϖ m k]`.

Conclude with `pow_mem (hs (m + k)) _`. Establish `hmono : Monotone F`. Introduce `m n hmn`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Conclude with `sup_le le_sup_left (IntermediateField.adjoin_simple_le_iff.2 (hseq m k))`.

Establish `hle : ϖ.fieldInf a ≤ ⨆ n, F n`. Use `sup_le (sup_le ?_ ?_) ?_` and prove the remaining obligations. Conclude with `le_trans le_sup_left (le_iSup F 0)`. Conclude with `le_trans (IntermediateField.adjoin_simple_le_iff.2 (hs 0)) (le_iSup F 0)`. Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨n, rfl⟩`. Conclude with `le_iSup F n (hs n)`. Establish `hx' : x ∈ ((⨆ n, F n : IntermediateField ℚ_[l] (Om l)) : Set (Om l))` using `hle hx`. Rewrite `hx'` using `[IntermediateField.coe_iSup_of_directed hmono.directed_le]`. Conclude with `Set.mem_iUnion.1 hx'`.
-/
theorem mem_level {a e : ℕ} [NeZero a] (ϖ : PiSys l e) {x : Om l} (hx : x ∈ ϖ.fieldInf a) :
    ∃ n, x ∈ Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n} := by
  let F : ℕ → IntermediateField ℚ_[l] (Om l) := fun n => Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n}
  have hs : ∀ n, ϖ.seq n ∈ F n := fun n =>
    (le_sup_right : _ ≤ F n) (IntermediateField.mem_adjoin_simple_self _ _)
  have hseq : ∀ m k, ϖ.seq m ∈ F (m + k) := by
    intro m k
    rw [← seq_add_pow ϖ m k]
    exact pow_mem (hs (m + k)) _
  have hmono : Monotone F := by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact sup_le le_sup_left (IntermediateField.adjoin_simple_le_iff.2 (hseq m k))
  have hle : ϖ.fieldInf a ≤ ⨆ n, F n := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_trans le_sup_left (le_iSup F 0)
    · exact le_trans (IntermediateField.adjoin_simple_le_iff.2 (hs 0)) (le_iSup F 0)
    · refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨n, rfl⟩
      exact le_iSup F n (hs n)
  have hx' : x ∈ ((⨆ n, F n : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) := hle hx
  rw [IntermediateField.coe_iSup_of_directed hmono.directed_le] at hx'
  exact Set.mem_iUnion.1 hx'

/- English proof (translation)
Introduce `x hx` and use `by induction hx using IntermediateField.adjoin_induction with | mem x hx => exact hg x hx | algebraMap r => exact g.commutes r | add x y _ _ hx hy => rw [map_add, hx, hy] | inv x _ hx => rw [map_inv₀, hx] | mul x y _ _ hx hy => rw [map_mul, hx, hy]`.
-/
theorem fix_Kunr {a : ℕ} [NeZero a] (g : GQ l) (hg : ∀ x : Om l, x ^ l ^ a = x → g x = x) :
    ∀ x ∈ Kunr l a, g x = x := fun x hx => by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact hg x hx
  | algebraMap r => exact g.commutes r
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

/- English proof (translation)
Introduce `l _ a e _ _ ϖ _ g hg`. Take `⟨h, hh, hgh⟩` from `exists_fix_Kur (ϖ.fieldInf a) g fun x hx hK => by`. Take `⟨n, hn⟩` from `mem_level ϖ hx`. Conclude with `fix_Kunr g hg x (GlobalTheory.T.mem_unramifiedField_of_mem_maxUnramified_sup_root l a e ϖ n x hK hn)`. Take `⟨k', hk', hkeq⟩` from `mem_IK_of_fix (g * h) hgh`.

Conclude with `⟨k', hk', h, hh, hkeq⟩`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a →
    ∀ g : GQ l, (∀ x : Om l, x ^ l ^ a = x → g x = x) →
      ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ h ∈ ϖ.GfieldInf a, (k' : GQ l) = g * h := by
  intro l _ a e _ _ ϖ _ g hg
  obtain ⟨h, hh, hgh⟩ := exists_fix_Kur (ϖ.fieldInf a) g fun x hx hK => by
    obtain ⟨n, hn⟩ := mem_level ϖ hx
    exact fix_Kunr g hg x (GlobalTheory.T.mem_unramifiedField_of_mem_maxUnramified_sup_root l a e ϖ n x hK hn)
  obtain ⟨k', hk', hkeq⟩ := mem_IK_of_fix (g * h) hgh
  exact ⟨k', hk', h, hh, hkeq⟩

end GlobalTheory.InertiaMod
