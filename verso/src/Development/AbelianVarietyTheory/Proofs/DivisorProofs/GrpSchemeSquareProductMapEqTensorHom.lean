import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsStableFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqZeroOfFpqc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotSchemeLocalOfQuotSchemeSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.UPel.HT.ES.KerDet

variable {S : Scheme.{0}}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, MonObj.comp_one]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]`.
-/
theorem comp_pow_id {A B : Over S} [GrpObj B] (f : A ⟶ B) (n : ℕ) : f ≫ (𝟙 B) ^ n = f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, MonObj.one_comp]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih, Category.id_comp]`.
-/
theorem pow_id_comp {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    ((𝟙 A) ^ n) ≫ f = f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih, Category.id_comp]

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A hA c hc`. Conclude with `GlobalTheory.FlatQuotient.epi_of_flat_surjective _`.
-/
theorem epi_pow_id (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (c : ℕ) (hc : 0 < c) :
    Epi ((𝟙 A) ^ c : A ⟶ A) := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A hA c hc
  exact GlobalTheory.FlatQuotient.epi_of_flat_surjective _

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A₁ hA₁ c hc`. Rewrite `h1`, `h2`, `h3` using `[← h₂]`. Establish `hpb` using `IsPullback.of_hasPullback (ψ' ≫ ψ₁) (η[A₁])`. Establish `ht : pullback.snd (ψ' ≫ ψ₁) (η[A₁]) = toUnit _` using `toUnit_unique _ _`. Rewrite `hpb` using `[ht]`.

Take `⟨β, hβ, e⟩` from `GlobalTheory.FlatQuotient.exists_desc (ψ' ≫ ψ₁) _ (ψ' ≫ ψ₂) hpb (by`. Rewrite using `[← Category.assoc, ← Hom.one_def]`. Use `hk _ _ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hpb.w, Hom.one_def])`. Use `⟨β, hβ, ?_⟩` and prove the remaining obligations.

Use `epi_pow_id A hA c hc` as an intermediate fact. Rewrite using `[← cancel_epi ((𝟙 A) ^ c), ← Category.assoc, pow_id_comp, ← comp_pow_id, ← h₂, Category.assoc, e, ← Category.assoc, h₁]`.
-/
theorem exists_factor {A A₁ A₂ : Over S} [GrpObj A] [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₂]
    (hA : IsAbelianScheme A) (hA₁ : IsAbelianScheme A₁) (c : ℕ) (hc : 0 < c)
    (ψ₁ : A ⟶ A₁) (ψ₂ : A ⟶ A₂) (ψ' : A₁ ⟶ A) [IsMonHom ψ₁] [IsMonHom ψ₂] [IsMonHom ψ']
    (h₁ : ψ₁ ≫ ψ' = (𝟙 A) ^ c) (h₂ : ψ' ≫ ψ₁ = (𝟙 A₁) ^ c)
    (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ ψ₁ = 1 → x ≫ ψ₂ = 1) :
    ∃ β : A₁ ⟶ A₂, IsMonHom β ∧ ψ₁ ≫ β = ψ₂ := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A₁ hA₁ c hc
  rw [← h₂] at h1 h2 h3
  have hpb := IsPullback.of_hasPullback (ψ' ≫ ψ₁) (η[A₁])
  have ht : pullback.snd (ψ' ≫ ψ₁) (η[A₁]) = toUnit _ := toUnit_unique _ _
  rw [ht] at hpb
  obtain ⟨β, hβ, e⟩ := GlobalTheory.FlatQuotient.exists_desc (ψ' ≫ ψ₁) _ (ψ' ≫ ψ₂) hpb (by
    rw [← Category.assoc, ← Hom.one_def]
    refine hk _ _ ?_
    rw [Category.assoc, hpb.w, Hom.one_def])
  refine ⟨β, hβ, ?_⟩
  have := epi_pow_id A hA c hc
  rw [← cancel_epi ((𝟙 A) ^ c), ← Category.assoc, pow_id_comp, ← comp_pow_id, ← h₂, Category.assoc, e,
    ← Category.assoc, h₁]

open GlobalTheory.CechPic GlobalTheory.BirigUniq in

/- English proof (translation)
Take `⟨hfl, hsu, hqc⟩` from `GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S B hB k hk`. Establish `hD : pull (χ ⊗ₘ 𝟙 B).left d = 0`. Use `pic_eq_zero_of_fpqc X B B hX ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_` and prove the remaining obligations. Rewrite using `[← pull_comp_left]`. Establish `: lift (1 : B ⟶ X) (𝟙 B) ≫ (χ ⊗ₘ 𝟙 B) = lift (1 : B ⟶ B) (𝟙 B)`.

Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp`. Rewrite using `[this, d₁]`. Rewrite using `[← pull_comp_left]`. Establish `: lift (fst X B) (snd X B ≫ (𝟙 B) ^ k) ≫ (χ ⊗ₘ 𝟙 B) = lift (fst X B) (snd X B ≫ χ') ≫ (χ ⊗ₘ χ)`. Apply the tactic sequence `rw [← hc]; apply CartesianMonoidalCategory.hom_ext <;> simp`.

Rewrite using `[this, pull_comp_left, dχ, map_zero]`. Establish `hQ : pull (lift (snd B B) (fst B B)).left d = 0`. Use `pic_eq_zero_of_fpqc B B B hB ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_` and prove the remaining obligations. Rewrite using `[← pull_comp_left]`. Establish `: lift (1 : B ⟶ B) (𝟙 B) ≫ lift (snd B B) (fst B B) = lift (𝟙 B) (1 : B ⟶ B)`.

Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp`. Rewrite using `[this, d₂]`. Rewrite using `[← pull_comp_left]`. Establish `: lift (fst B B) (snd B B ≫ (𝟙 B) ^ k) ≫ lift (snd B B) (fst B B) = lift (snd B B ≫ χ') (fst B B) ≫ (χ ⊗ₘ 𝟙 B)`. Apply the tactic sequence `rw [← hc]; apply CartesianMonoidalCategory.hom_ext <;> simp`.

Rewrite using `[this, pull_comp_left, hD, map_zero]`. Establish `hsw : lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B) = 𝟙 (B ⊗ B)`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp`. Establish `H : pull (lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B)).left d = d`. Rewrite using `[hsw, Over.id_left, pull_id]`.

Rewrite `H` using `[pull_comp_left, hQ, map_zero]`. Conclude with `H.symm`.
-/
theorem pic_eq_zero_of_pull {X B : Over S} [GrpObj X] [GrpObj B] (hX : IsAbelianScheme X)
    (hB : IsAbelianScheme B) (k : ℕ) (hk : 0 < k) (χ : X ⟶ B) (χ' : B ⟶ X) [IsMonHom χ]
    (hc : χ' ≫ χ = (𝟙 B) ^ k) (d : Pic (B ⊗ B).left)
    (d₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left d = 0) (d₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left d = 0)
    (dχ : pull (χ ⊗ₘ χ).left d = 0) : d = 0 := by
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S B hB k hk
  have hD : pull (χ ⊗ₘ 𝟙 B).left d = 0 := by
    refine pic_eq_zero_of_fpqc X B B hX ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_
    · rw [← pull_comp_left]
      have : lift (1 : B ⟶ X) (𝟙 B) ≫ (χ ⊗ₘ 𝟙 B) = lift (1 : B ⟶ B) (𝟙 B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, d₁]
    · rw [← pull_comp_left]
      have : lift (fst X B) (snd X B ≫ (𝟙 B) ^ k) ≫ (χ ⊗ₘ 𝟙 B) =
          lift (fst X B) (snd X B ≫ χ') ≫ (χ ⊗ₘ χ) := by
        rw [← hc]; apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, pull_comp_left, dχ, map_zero]
  have hQ : pull (lift (snd B B) (fst B B)).left d = 0 := by
    refine pic_eq_zero_of_fpqc B B B hB ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_
    · rw [← pull_comp_left]
      have : lift (1 : B ⟶ B) (𝟙 B) ≫ lift (snd B B) (fst B B) = lift (𝟙 B) (1 : B ⟶ B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, d₂]
    · rw [← pull_comp_left]
      have : lift (fst B B) (snd B B ≫ (𝟙 B) ^ k) ≫ lift (snd B B) (fst B B) =
          lift (snd B B ≫ χ') (fst B B) ≫ (χ ⊗ₘ 𝟙 B) := by
        rw [← hc]; apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, pull_comp_left, hD, map_zero]
  have hsw : lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B) = 𝟙 (B ⊗ B) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have H : pull (lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B)).left d = d := by
    rw [hsw, Over.id_left, pull_id]
  rw [pull_comp_left, hQ, map_zero] at H
  exact H.symm

/- English proof (translation)
Establish `: lift (fst A A ≫ ψ) (snd A A ≫ ψ) = ψ ⊗ₘ ψ`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp`. Conclude with `congrArg (fun f : A ⊗ A ⟶ A' ⊗ A' => f.left) this`.
-/
theorem grpSchemeSquareProductMap_eq_tensorHom {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ = (ψ ⊗ₘ ψ).left := by
  have : lift (fst A A ≫ ψ) (snd A A ≫ ψ) = ψ ⊗ₘ ψ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  exact congrArg (fun f : A ⊗ A ⟶ A' ⊗ A' => f.left) this

open GlobalTheory.CechPic GlobalTheory.BirigUniq in

/- English proof (translation)
Introduce `p _ D R _ b N _ _ c S _ s o o₁ o₂ ψ₁ ψ₂ H₁ H₂ hk`. Establish `hc` using `H₁.pos`. Take `⟨-, m₁, a₁, l₁, ⟨P₁⟩, ψ₁', m₁', u₁, v₁⟩` from `H₁`. Take `⟨-, m₂, a₂, l₂, ⟨P₂⟩, ψ₂', m₂', u₂, v₂⟩` from `H₂`. Take `⟨β, hβ, e⟩` from `exists_factor o.ab o₁.ab c hc ψ₁ ψ₂ ψ₁' u₁ v₁ fun T x => (hk T x).1`.

Take `⟨β', -, e'⟩` from `exists_factor o.ab o₂.ab c hc ψ₂ ψ₁ ψ₂' u₂ v₂ fun T x => (hk T x).2`. Establish `E₁ : Epi ψ₁`. Use `epi_pow_id o₁.A o₁.ab c hc` as an intermediate fact. Conclude with `epi_of_epi_fac v₁`. Establish `E₂ : Epi ψ₂`.

Use `epi_pow_id o₂.A o₂.ab c hc` as an intermediate fact. Conclude with `epi_of_epi_fac v₂`. Set `i : o₁.A ≅ o₂.A` to `⟨β, β', by rw [← cancel_epi ψ₁, ← Category.assoc, e, e', Category.comp_id], by rw [← cancel_epi ψ₂, ← Category.assoc, e', e, Category.comp_id]⟩`. Establish `hpol : LBIso o₁.P (o₂.P.pull (β ⊗ₘ β).left)`. Establish `hN : (Hecke.lbPow o.P c).IsLB` using `LB.isLB_linComb o.isLB _ _`.

Rewrite `P₁`, `P₂` using `[grpSchemeSquareProductMap_eq_tensorHom]`. Set `p₁` to `cls o₁.P o₁.isLB`. Set `p₂` to `cls o₂.P o₂.isLB`. Establish `n₁ : pull (ψ₁ ⊗ₘ ψ₁).left p₁ = cls _ hN` using `((cls_eq_iff hN (pull_isLB o₁.isLB _)).2 P₁).symm`. Establish `n₂ : pull (ψ₂ ⊗ₘ ψ₂).left p₂ = cls _ hN` using `((cls_eq_iff hN (pull_isLB o₂.isLB _)).2 P₂).symm`.

Establish `r₁₁ : pull (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left p₁ = 0` using `(cls_eq_zero_iff (pull_isLB o₁.isLB _)).2 o₁.rig₁`. Establish `r₁₂ : pull (lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)).left p₁ = 0` using `(cls_eq_zero_iff (pull_isLB o₁.isLB _)).2 o₁.rig₂`. Establish `r₂₁ : pull (lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A)).left p₂ = 0` using `(cls_eq_zero_iff (pull_isLB o₂.isLB _)).2 o₂.rig₁`. Establish `r₂₂ : pull (lift (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A)).left p₂ = 0` using `(cls_eq_zero_iff (pull_isLB o₂.isLB _)).2 o₂.rig₂`. Establish `e₁ : lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A) ≫ (β ⊗ₘ β) = β ≫ lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A)`.

Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp`. Establish `e₂ : lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A) ≫ (β ⊗ₘ β) = β ≫ lift (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A)`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp`. Establish `hd : pull (β ⊗ₘ β).left p₂ - p₁ = 0`. Use `pic_eq_zero_of_pull o.ab o₁.ab c hc ψ₁ ψ₁' v₁ _ ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[map_sub, r₁₁, sub_zero, ← pull_comp_left, e₁, pull_comp_left, r₂₁, map_zero]`. Rewrite using `[map_sub, r₁₂, sub_zero, ← pull_comp_left, e₂, pull_comp_left, r₂₂, map_zero]`. Rewrite using `[map_sub, n₁, ← pull_comp_left, tensorHom_comp_tensorHom, e, n₂, sub_self]`. Conclude with `(cls_eq_iff o₁.isLB (pull_isLB o₂.isLB _)).1 (sub_eq_zero.1 hd).symm`. Use `⟨{ φ := β.left, φ₂ := (β ⊗ₘ β).left cart := (GlobalTheory.TQCompare.isGrpPullback_id_iff _).2 ⟨i, hβ, rfl⟩ sq := ⟨?_, ?_⟩, act := fun a => ?_, pol := hpol, eta := fun y => ?_ }, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Over.comp_left, ← Over.comp_left, tensorHom_fst]`. Rewrite using `[← Over.comp_left, ← Over.comp_left, tensorHom_snd]`. Rewrite using `[← Over.comp_left, ← Over.comp_left]`. Use `congr 1`. Rewrite using `[← cancel_epi ψ₁, ← Category.assoc, ← a₁, Category.assoc, e, a₂, ← Category.assoc, e]`.

Rewrite using `[← Over.comp_left, l₁, l₂, Category.assoc, e]`. Conclude with `(Category.id_comp _).symm`. Use `show ψ₁.left ≫ β.left = _`. Rewrite using `[← Over.comp_left, e]`.
-/
theorem exists_objMap_of_ker_eq : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o o₁ o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsPIsog c o o₁ ψ₁ → IsPIsog c o o₂ ψ₂ → (∀ (T : Over S) (x : T ⟶ o.A), x ≫ ψ₁ = 1 ↔ x ≫ ψ₂ = 1) → ∃ m : ObjMap o₁ o₂ (𝟙 S), ψ₁.left ≫ m.φ = ψ₂.left := by
  intro p _ D R _ b N _ _ c S _ s o o₁ o₂ ψ₁ ψ₂ H₁ H₂ hk
  have hc := H₁.pos
  obtain ⟨-, m₁, a₁, l₁, ⟨P₁⟩, ψ₁', m₁', u₁, v₁⟩ := H₁
  obtain ⟨-, m₂, a₂, l₂, ⟨P₂⟩, ψ₂', m₂', u₂, v₂⟩ := H₂
  obtain ⟨β, hβ, e⟩ := exists_factor o.ab o₁.ab c hc ψ₁ ψ₂ ψ₁' u₁ v₁ fun T x => (hk T x).1
  obtain ⟨β', -, e'⟩ := exists_factor o.ab o₂.ab c hc ψ₂ ψ₁ ψ₂' u₂ v₂ fun T x => (hk T x).2
  have E₁ : Epi ψ₁ := by
    have := epi_pow_id o₁.A o₁.ab c hc
    exact epi_of_epi_fac v₁
  have E₂ : Epi ψ₂ := by
    have := epi_pow_id o₂.A o₂.ab c hc
    exact epi_of_epi_fac v₂
  let i : o₁.A ≅ o₂.A := ⟨β, β', by rw [← cancel_epi ψ₁, ← Category.assoc, e, e', Category.comp_id],
    by rw [← cancel_epi ψ₂, ← Category.assoc, e', e, Category.comp_id]⟩
  have hpol : LBIso o₁.P (o₂.P.pull (β ⊗ₘ β).left) := by
    have hN : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
    rw [grpSchemeSquareProductMap_eq_tensorHom] at P₁ P₂
    let p₁ := cls o₁.P o₁.isLB
    let p₂ := cls o₂.P o₂.isLB
    have n₁ : pull (ψ₁ ⊗ₘ ψ₁).left p₁ = cls _ hN := ((cls_eq_iff hN (pull_isLB o₁.isLB _)).2 P₁).symm
    have n₂ : pull (ψ₂ ⊗ₘ ψ₂).left p₂ = cls _ hN := ((cls_eq_iff hN (pull_isLB o₂.isLB _)).2 P₂).symm
    have r₁₁ : pull (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left p₁ = 0 :=
      (cls_eq_zero_iff (pull_isLB o₁.isLB _)).2 o₁.rig₁
    have r₁₂ : pull (lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)).left p₁ = 0 :=
      (cls_eq_zero_iff (pull_isLB o₁.isLB _)).2 o₁.rig₂
    have r₂₁ : pull (lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A)).left p₂ = 0 :=
      (cls_eq_zero_iff (pull_isLB o₂.isLB _)).2 o₂.rig₁
    have r₂₂ : pull (lift (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A)).left p₂ = 0 :=
      (cls_eq_zero_iff (pull_isLB o₂.isLB _)).2 o₂.rig₂
    have e₁ : lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A) ≫ (β ⊗ₘ β) = β ≫ lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have e₂ : lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A) ≫ (β ⊗ₘ β) = β ≫ lift (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have hd : pull (β ⊗ₘ β).left p₂ - p₁ = 0 := by
      refine pic_eq_zero_of_pull o.ab o₁.ab c hc ψ₁ ψ₁' v₁ _ ?_ ?_ ?_
      · rw [map_sub, r₁₁, sub_zero, ← pull_comp_left, e₁, pull_comp_left, r₂₁, map_zero]
      · rw [map_sub, r₁₂, sub_zero, ← pull_comp_left, e₂, pull_comp_left, r₂₂, map_zero]
      · rw [map_sub, n₁, ← pull_comp_left, tensorHom_comp_tensorHom, e, n₂, sub_self]
    exact (cls_eq_iff o₁.isLB (pull_isLB o₂.isLB _)).1 (sub_eq_zero.1 hd).symm
  refine ⟨{ φ := β.left, φ₂ := (β ⊗ₘ β).left
            cart := (GlobalTheory.TQCompare.isGrpPullback_id_iff _).2 ⟨i, hβ, rfl⟩
            sq := ⟨?_, ?_⟩, act := fun a => ?_, pol := hpol, eta := fun y => ?_ }, ?_⟩
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_fst]
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_snd]
  · rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [← cancel_epi ψ₁, ← Category.assoc, ← a₁, Category.assoc, e, a₂, ← Category.assoc, e]
  · rw [← Over.comp_left, l₁, l₂, Category.assoc, e]
    exact (Category.id_comp _).symm
  · show ψ₁.left ≫ β.left = _
    rw [← Over.comp_left, e]

end GlobalTheory.UPel.HT.ES.KerDet
