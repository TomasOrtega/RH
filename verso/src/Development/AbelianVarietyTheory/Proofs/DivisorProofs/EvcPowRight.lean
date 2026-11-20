import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsStableFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProdIsoOfPowIsoBirigidified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqZeroOfFpqc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFactorsThroughMulN
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.UPel.HT.ES.KerFin

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

/- English proof (translation)
Take `⟨-, ad⟩` from `GlobalTheory.BirigidRoot.additive_of_birigid o.ab o.isLB o.rig₁ o.rig₂`. Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, zero_smul]`. Conclude with `evc_one_right o.isLB o.rig₂ x`. Consider the case `succ n ih => rw [pow_succ, (GlobalTheory.BirigidLift.isAdditive_swap_iff o.isLB).1 ad, ih, succ_nsmul]`.
-/
theorem evc_pow_right {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {T : Over S} (x y : T ⟶ o.A) (n : ℕ) :
    evc o.isLB x (y ^ n) = n • evc o.isLB x y := by
  obtain ⟨-, ad⟩ := GlobalTheory.BirigidRoot.additive_of_birigid o.ab o.isLB o.rig₁ o.rig₂
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact evc_one_right o.isLB o.rig₂ x
  | succ n ih => rw [pow_succ, (GlobalTheory.BirigidLift.isAdditive_swap_iff o.isLB).1 ad, ih, succ_nsmul]

/- English proof (translation)
Take `⟨e⟩` from `h.2.2.2.2.1`. Establish `hQ : (Hecke.lbPow o.P c).IsLB` using `LB.isLB_linComb o.isLB _ _`. Establish `hP : (ev o'.P (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ)).IsLB` using `pull_isLB o'.isLB _`. Establish `e₁ : cls _ hQ = cls _ hP` using `(cls_eq_iff hQ hP).2 e`. Establish `e₂ : cls _ hQ = c • cls o.P o.isLB`.

Use `(cls_linComb o.isLB _ _ hQ).trans ?_` and prove the remaining obligations. Simplify using `[pull_id]`. Establish `z` using `evc_ev o'.isLB (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ) hP x y`. Rewrite `z` using `[lift_fst_assoc, lift_snd_assoc]`. Rewrite using `[← z, evc, ← e₁, e₂, map_nsmul]`.

Both sides reduce to the same expression.
-/
theorem evc_isog {S : Scheme.{0}} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) {T : Over S} (x y : T ⟶ o.A) :
    evc o'.isLB (x ≫ ψ) (y ≫ ψ) = c • evc o.isLB x y := by
  obtain ⟨e⟩ := h.2.2.2.2.1
  have hQ : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
  have hP : (ev o'.P (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ)).IsLB := pull_isLB o'.isLB _
  have e₁ : cls _ hQ = cls _ hP := (cls_eq_iff hQ hP).2 e
  have e₂ : cls _ hQ = c • cls o.P o.isLB := by
    refine (cls_linComb o.isLB _ _ hQ).trans ?_
    simp [pull_id]
  have z := evc_ev o'.isLB (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ) hP x y
  rw [lift_fst_assoc, lift_snd_assoc] at z
  rw [← z, evc, ← e₁, e₂, map_nsmul]
  rfl

/- English proof (translation)
Use `haveI := h.2.1`. Take `⟨hfl, hsu, hqc⟩` from `SiegUniqBase.flat_surjective_qc_pow S o'.A o'.ab c h.pos`. Establish `key` using `GlobalTheory.BirigUniq.pic_eq_zero_of_fpqc o.A o'.A o'.A o.ab ((𝟙 o'.A) ^ c) hfl hsu hqc (evc o'.isLB (fst o.A o'.A ≫ ψ) (snd o.A o'.A) - evc o.isLB (fst o.A o'.A) (snd o.A o'.A ≫ ψ')) (by`. Rewrite using `[map_sub, pull_evc, pull_evc, lift_fst_assoc, lift_fst, MonObj.one_comp, evc_one_left o'.isLB o'.rig₁, evc_one_left o.isLB o.rig₁, sub_self]) (by`. Rewrite using `[map_sub, pull_evc, pull_evc, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc, sub_eq_zero]`.

Establish `e₁ : (snd o.A o'.A ≫ (𝟙 o'.A) ^ c) ≫ ψ' = (snd o.A o'.A ≫ ψ') ^ c`. Rewrite using `[MonObj.comp_pow, Category.comp_id, GlobalTheory.BirigidRoot.pow_comp_hom]`. Rewrite using `[e₁, evc_pow_right, ← h', ← Category.assoc, evc_isog h])`. Establish `z` using `congrArg (CechPic.pull (lift x y).left) (sub_eq_zero.1 key)`. Rewrite `z` using `[pull_evc, pull_evc, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc]`. Then use the resulting hypothesis.
-/
theorem evc_adj {S : Scheme.{0}} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) (ψ' : o'.A ⟶ o.A) [IsMonHom ψ'] (h' : ψ' ≫ ψ = (𝟙 o'.A) ^ c) {T : Over S}
    (x : T ⟶ o.A) (y : T ⟶ o'.A) : evc o'.isLB (x ≫ ψ) y = evc o.isLB x (y ≫ ψ') := by
  haveI := h.2.1
  obtain ⟨hfl, hsu, hqc⟩ := SiegUniqBase.flat_surjective_qc_pow S o'.A o'.ab c h.pos
  have key := GlobalTheory.BirigUniq.pic_eq_zero_of_fpqc o.A o'.A o'.A o.ab ((𝟙 o'.A) ^ c) hfl hsu hqc
    (evc o'.isLB (fst o.A o'.A ≫ ψ) (snd o.A o'.A) - evc o.isLB (fst o.A o'.A) (snd o.A o'.A ≫ ψ')) (by
      rw [map_sub, pull_evc, pull_evc, lift_fst_assoc, lift_fst, MonObj.one_comp,
        evc_one_left o'.isLB o'.rig₁, evc_one_left o.isLB o.rig₁, sub_self]) (by
      rw [map_sub, pull_evc, pull_evc, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc, sub_eq_zero]
      have e₁ : (snd o.A o'.A ≫ (𝟙 o'.A) ^ c) ≫ ψ' = (snd o.A o'.A ≫ ψ') ^ c := by
        rw [MonObj.comp_pow, Category.comp_id, GlobalTheory.BirigidRoot.pow_comp_hom]
      rw [e₁, evc_pow_right, ← h', ← Category.assoc, evc_isog h])
  have z := congrArg (CechPic.pull (lift x y).left) (sub_eq_zero.1 key)
  rwa [pull_evc, pull_evc, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc] at z

/- English proof (translation)
Establish `h₁ : (ev o.P (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).IsLB` using `pull_isLB o.isLB _`. Establish `h₂ : (ev o.P (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).IsLB` using `pull_isLB o.isLB _`. Establish `e` using `(cls_eq_iff h₁ h₂).2 (o.rosati a)`. Establish `z₁` using `evc_ev o.isLB _ _ h₁ x y`. Establish `z₂` using `evc_ev o.isLB _ _ h₂ x y`.

Rewrite `z₁` using `[lift_fst_assoc, lift_snd]`. Rewrite `z₂` using `[lift_fst, lift_snd_assoc]`. Rewrite using `[← z₁, ← z₂, evc, evc, e]`.
-/
theorem evc_rosati {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (a : D.O) {T : Over S} (x y : T ⟶ o.A) :
    evc o.isLB (x ≫ o.act.act a) y = evc o.isLB x (y ≫ o.act.act (D.star a).unop) := by
  have h₁ : (ev o.P (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).IsLB := pull_isLB o.isLB _
  have h₂ : (ev o.P (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).IsLB := pull_isLB o.isLB _
  have e := (cls_eq_iff h₁ h₂).2 (o.rosati a)
  have z₁ := evc_ev o.isLB _ _ h₁ x y
  have z₂ := evc_ev o.isLB _ _ h₂ x y
  rw [lift_fst_assoc, lift_snd] at z₁
  rw [lift_fst, lift_snd_assoc] at z₂
  rw [← z₁, ← z₂, evc, evc, e]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Both sides reduce to the same expression. Consider the case `succ n ih => rw [pow_succ, ← ih]`. Both sides reduce to the same expression.
-/
theorem mulN_eq_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] (n : ℕ) : mulN A n = (𝟙 A) ^ n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

/- English proof (translation)
Use `haveI := h₁.2.1`. Use `haveI := h₂.2.1`. Use `haveI := o.act.hom a`. Use `haveI := o.act.hom (D.star a).unop`. Take `⟨φ₁, hφ₁, e₁, e₁'⟩` from `h₁.2.2.2.2.2`.

Take `⟨φ₂, hφ₂, e₂, e₂'⟩` from `h₂.2.2.2.2.2`. Take `⟨β, hβ, eβ⟩` from `GlobalTheory.MulNDiv.exists_factor_mulN k o₂.A o₁.A o₂.ab o₁.ab c h₁.pos (φ₂ ≫ o.act.act a ≫ ψ₁) inferInstance (fun S _ _ z hz => by`. Use `H _ (z ≫ φ₂) (by rw [Category.assoc, e₂', MonObj.comp_pow, Category.comp_id, hz])` as an intermediate fact. Simplify `this)` using `only [Category.assoc]`. Rewrite `eβ` using `[mulN_eq_pow]`.

Establish `hfac : φ₂ ≫ o.act.act a = β ≫ φ₁`. Take `⟨hfl, hsu, -⟩` from `SiegUniqBase.flat_surjective_qc_pow _ o₂.A o₂.ab c h₁.pos`. Use `haveI := hfl`. Use `haveI := hsu`. Use `haveI : Epi ((𝟙 o₂.A) ^ c).left := Flat.epi_of_flat_of_surjective _`.

Establish `e : (((𝟙 o₂.A) ^ c) ≫ φ₂ ≫ o.act.act a).left = (((𝟙 o₂.A) ^ c) ≫ β ≫ φ₁).left`. Rewrite using `[← Category.assoc _ β, ← eβ, Category.assoc, Category.assoc, e₁, GlobalTheory.BirigidRoot.pow_comp_hom, Category.id_comp, ← Category.assoc, MonObj.comp_pow, Category.comp_id]`. Rewrite `e` using `[Over.comp_left, Over.comp_left]`. Conclude with `Over.OverMorphism.ext ((cancel_epi ((𝟙 o₂.A) ^ c).left).1 e)`. Take `⟨e, he, hker⟩` from `o₂.kerP`.

Use `set y := (x ≫ o.act.act (D.star a).unop) ≫ ψ₂ with hy`. Establish `hye : y ^ e = 1`. Use `hker T y ((triv_ev_iff o₂.isLB _ _).2 ?_)` and prove the remaining obligations. Rewrite using `[hy, ← Category.assoc, evc_adj h₂ φ₂ e₂', ← Category.assoc, evc_rosati, D.star_star, Category.assoc, hfac, ← Category.assoc, ← evc_adj h₁ φ₁ e₁', Category.assoc, hx, MonObj.comp_one]`. Conclude with `evc_one_left o₁.isLB o₁.rig₁ _`.

Establish `hyc : y ^ c = 1`. Establish `hxc : x ^ c = 1`. Rewrite using `[← Category.comp_id x, ← MonObj.comp_pow, ← e₁, ← Category.assoc, hx, MonObj.one_comp]`. Rewrite using `[hy, ← GlobalTheory.BirigidRoot.pow_comp_hom, ← GlobalTheory.BirigidRoot.pow_comp_hom, hxc, MonObj.one_comp, MonObj.one_comp]`. Take `⟨m, rfl⟩` from `h₁.1`.

Use `pow_gcd_eq_one.2 ⟨hye, hyc⟩` as an intermediate fact. Rewrite `this` using `[(Nat.Coprime.pow_right m he).gcd_eq_one, pow_one]`. Then use the resulting hypothesis.
-/
theorem star_ker_le {k : Type} [CommRing k] {s : Sp k ⟶ Sp R} {c : ℕ} {o o₁ o₂ : Obj b N s} {ψ₁ : o.A ⟶ o₁.A}
    {ψ₂ : o.A ⟶ o₂.A} (h₁ : IsPIsog c o o₁ ψ₁) (h₂ : IsPIsog c o o₂ ψ₂) (a : D.O)
    (H : ∀ (T : Over (Sp k)) (x : T ⟶ o.A), x ≫ ψ₂ = 1 → (x ≫ o.act.act a) ≫ ψ₁ = 1)
    (T : Over (Sp k)) (x : T ⟶ o.A) (hx : x ≫ ψ₁ = 1) : (x ≫ o.act.act (D.star a).unop) ≫ ψ₂ = 1 := by
  haveI := h₁.2.1
  haveI := h₂.2.1
  haveI := o.act.hom a
  haveI := o.act.hom (D.star a).unop
  obtain ⟨φ₁, hφ₁, e₁, e₁'⟩ := h₁.2.2.2.2.2
  obtain ⟨φ₂, hφ₂, e₂, e₂'⟩ := h₂.2.2.2.2.2
  obtain ⟨β, hβ, eβ⟩ := GlobalTheory.MulNDiv.exists_factor_mulN k o₂.A o₁.A o₂.ab o₁.ab c h₁.pos
    (φ₂ ≫ o.act.act a ≫ ψ₁) inferInstance (fun S _ _ z hz => by
      have := H _ (z ≫ φ₂) (by rw [Category.assoc, e₂', MonObj.comp_pow, Category.comp_id, hz])
      simpa only [Category.assoc] using this)
  rw [mulN_eq_pow] at eβ
  have hfac : φ₂ ≫ o.act.act a = β ≫ φ₁ := by
    obtain ⟨hfl, hsu, -⟩ := SiegUniqBase.flat_surjective_qc_pow _ o₂.A o₂.ab c h₁.pos
    haveI := hfl
    haveI := hsu
    haveI : Epi ((𝟙 o₂.A) ^ c).left := Flat.epi_of_flat_of_surjective _
    have e : (((𝟙 o₂.A) ^ c) ≫ φ₂ ≫ o.act.act a).left = (((𝟙 o₂.A) ^ c) ≫ β ≫ φ₁).left := by
      rw [← Category.assoc _ β, ← eβ, Category.assoc, Category.assoc, e₁, GlobalTheory.BirigidRoot.pow_comp_hom,
        Category.id_comp, ← Category.assoc, MonObj.comp_pow, Category.comp_id]
    rw [Over.comp_left, Over.comp_left] at e
    exact Over.OverMorphism.ext ((cancel_epi ((𝟙 o₂.A) ^ c).left).1 e)
  obtain ⟨e, he, hker⟩ := o₂.kerP
  set y := (x ≫ o.act.act (D.star a).unop) ≫ ψ₂ with hy
  have hye : y ^ e = 1 := by
    refine hker T y ((triv_ev_iff o₂.isLB _ _).2 ?_)
    rw [hy, ← Category.assoc, evc_adj h₂ φ₂ e₂', ← Category.assoc, evc_rosati, D.star_star, Category.assoc, hfac,
      ← Category.assoc, ← evc_adj h₁ φ₁ e₁', Category.assoc, hx, MonObj.comp_one]
    exact evc_one_left o₁.isLB o₁.rig₁ _
  have hyc : y ^ c = 1 := by
    have hxc : x ^ c = 1 := by
      rw [← Category.comp_id x, ← MonObj.comp_pow, ← e₁, ← Category.assoc, hx, MonObj.one_comp]
    rw [hy, ← GlobalTheory.BirigidRoot.pow_comp_hom, ← GlobalTheory.BirigidRoot.pow_comp_hom, hxc, MonObj.one_comp, MonObj.one_comp]
  obtain ⟨m, rfl⟩ := h₁.1
  have := pow_gcd_eq_one.2 ⟨hye, hyc⟩
  rwa [(Nat.Coprime.pow_right m he).gcd_eq_one, pow_one] at this

end GlobalTheory.UPel.HT.ES.KerFin
