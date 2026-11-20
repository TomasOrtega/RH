import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMumfordClassEqZeroAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleBaseChangeIsoSemiabelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfCubWeilOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.PicBilin

variable {S : Scheme.{0}}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `e` using `hadd 1 1 t`. Rewrite `e` using `[_root_.mul_one]`. Rewrite using `[pow_zero, zero_smul]`.

Conclude with `left_eq_add.1 e`. Consider the case `succ n ih => rw [pow_succ, hadd, ih, succ_nsmul]`.
-/
theorem evc_pow_left {A B Y : Over S} [GrpObj A] {P : LB (A ⊗ B).left} (hP : P.IsLB)
    (hadd : ∀ (a a' : Y ⟶ A) (t : Y ⟶ B), evc hP (a * a') t = evc hP a t + evc hP a' t)
    (a : Y ⟶ A) (t : Y ⟶ B) (n : ℕ) : evc hP (a ^ n) t = n • evc hP a t := by
  induction n with
  | zero =>
    have e := hadd 1 1 t
    rw [_root_.mul_one] at e
    rw [pow_zero, zero_smul]
    exact left_eq_add.1 e
  | succ n ih => rw [pow_succ, hadd, ih, succ_nsmul]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, MonObj.comp_one]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]`.
-/
theorem comp_pow_pt {A T Y : Over S} [GrpObj A] (f : Y ⟶ T) (g : T ⟶ A) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

/- English proof (translation)
Use `(cls_linComb hL (K := Fin m) (fun _ => 𝟙 X) (fun _ => 1) h).trans ?_` and prove the remaining obligations. Simplify using `[pull_id]`.
-/
theorem cls_heckePow {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (m : ℕ)
    (h : (GlobalTheory.UPel.HT.Hecke.lbPow L m).IsLB) : cls _ h = m • cls L hL := by
  refine (cls_linComb hL (K := Fin m) (fun _ => 𝟙 X) (fun _ => 1) h).trans ?_
  simp [pull_id]

end GlobalTheory.PicBilin

namespace GlobalTheory.PicBilin

/- English proof (translation)
Introduce `S A _ _ hA P hP rig₁ rig₂ hsym T hT h₀ h' m hsq htd`. Establish `hs : (swap P).IsLB` using `pull_isLB hP _`. Take `⟨hadd₁, hadd₂⟩` from `additive_of_cube GlobalTheory.CubeTop.cubeTheorem hA hA hP rig₁ rig₂`. Establish `eL : ∀ {Y : Over S} (a a' t : Y ⟶ A), evc hP (a * a') t = evc hP a t + evc hP a' t` using `fun a a' t => (isAdditive_iff hP).1 hadd₁ _ a a' t`. Establish `eR : ∀ {Y : Over S} (a t t' : Y ⟶ A), evc hP a (t * t') = evc hP a t + evc hP a t'`.

Introduce `Y a t t'`. Establish `e` using `(isAdditive_iff hs).1 hadd₂ _ t t' a`. Rewrite `e` using `[evc_swap hP hs, evc_swap hP hs, evc_swap hP hs]`. Then use the resulting hypothesis. Establish `hsymc : cls P hP = cls _ hs` using `(cls_eq_iff hP hs).2 hsym`. Establish `eS : ∀ {Y : Over S} (a b : Y ⟶ A), evc hP a b = evc hP b a`.

Introduce `Y a b`. Rewrite using `[← evc_swap hP hs a b]`. Simplify using `only [evc, hsymc]`. Establish `hL₁ : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB` using `pull_isLB hP _`. Establish `hD : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) (h' ^ m)).IsLB` using `LB.isLB_linComb hL₁ _ _`.

Establish `e0` using `pull_translDiff hL₁ (h' ^ m) hD (snd A T) (fst A T)`. Rewrite `e0` using `[(cls_eq_zero_iff hD).2 htd, map_zero]`. Establish `hu : ∀ u : A ⊗ T ⟶ A, CechPic.pull u.left (cls _ hL₁) = evc hP u u` using `fun u => by`. Rewrite using `[cls_ev hP, pull_evc, Category.comp_id]`. Rewrite `e0` using `[hu, hu]`.

Establish `hXX : evc hP (snd A T ≫ h' ^ m) (snd A T ≫ h' ^ m) = 0`. Rewrite using `[← pull_evc, hT (evc hP (h' ^ m) (h' ^ m)), map_zero]`. Establish `key : evc hP (snd A T ≫ h' ^ m) (snd A T ≫ h' ^ m) + evc hP (snd A T ≫ h' ^ m) (fst A T) + (evc hP (fst A T) (snd A T ≫ h' ^ m) + evc hP (fst A T) (fst A T)) - evc hP (fst A T) (fst A T) = 0`. Rewrite using `[← eR, ← eR, ← eL]`. Conclude with `e0.symm`.

Rewrite `key` using `[hXX, eS (fst A T) (snd A T ≫ h' ^ m)]`. Establish `h2 : 2 • evc hP (snd A T ≫ h' ^ m) (fst A T) = 0`. Rewrite using `[two_nsmul, ← key]`. Normalize the expressions using the abelian group laws. Rewrite `h2` using `[comp_pow_pt, evc_pow_left hP (fun a a' t => eL a a' t)]`.

Establish `hsq' : toUnit (A ⊗ T) ≫ h₀ = (snd A T ≫ h') ^ 2`. Rewrite using `[← comp_pow_pt, hsq, ← Category.assoc, toUnit_unique (snd A T ≫ toUnit T) (toUnit _)]`. Establish `hQ : (GlobalTheory.UPel.HT.Hecke.lbPow P m).IsLB` using `LB.isLB_linComb hP _ _`. Establish `eQ : ∀ {Y : Over S} (a b : Y ⟶ A), evc hQ a b = m • evc hP a b`. Introduce `Y a b`.

Rewrite using `[evc, cls_heckePow hP m hQ, map_nsmul]`. Both sides reduce to the same expression. Use `(cls_eq_zero_iff (pull_isLB (pull_isLB hQ _) _)).1 ?_` and prove the remaining obligations. Rewrite using `[cls_pull (pull_isLB hQ _)]`. Express the relevant statement in the definitionally equal form `CechPic.pull (fst A T).left (evc hQ (toUnit A ≫ h₀) (𝟙 A)) = 0`.

Rewrite using `[pull_evc, eQ, Category.comp_id, ← Category.assoc, toUnit_unique (fst A T ≫ toUnit A) (toUnit _), hsq', evc_pow_left hP (fun a a' t => eL a a' t), smul_comm]`. Conclude with `h2`.
-/
theorem triv_pow_of_translDiff : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left), P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∀ (T : Over S), (∀ c : GlobalTheory.CechPic.Pic T.left, c = 0) →
    ∀ (h₀ : 𝟙_ (Over S) ⟶ A) (h' : T ⟶ A) (m : ℕ), h' ^ 2 = toUnit T ≫ h₀ →
    (∃ t : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) (h' ^ m)).Gen, t.IsGen) →
    ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h₀) (𝟙 A)).left).pull (fst A T).left).Gen, t.IsGen := by
  intro S A _ _ hA P hP rig₁ rig₂ hsym T hT h₀ h' m hsq htd
  have hs : (swap P).IsLB := pull_isLB hP _
  obtain ⟨hadd₁, hadd₂⟩ := additive_of_cube GlobalTheory.CubeTop.cubeTheorem hA hA hP rig₁ rig₂
  have eL : ∀ {Y : Over S} (a a' t : Y ⟶ A), evc hP (a * a') t = evc hP a t + evc hP a' t :=
    fun a a' t => (isAdditive_iff hP).1 hadd₁ _ a a' t
  have eR : ∀ {Y : Over S} (a t t' : Y ⟶ A), evc hP a (t * t') = evc hP a t + evc hP a t' := by
    intro Y a t t'
    have e := (isAdditive_iff hs).1 hadd₂ _ t t' a
    rwa [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs] at e
  have hsymc : cls P hP = cls _ hs := (cls_eq_iff hP hs).2 hsym
  have eS : ∀ {Y : Over S} (a b : Y ⟶ A), evc hP a b = evc hP b a := by
    intro Y a b
    rw [← evc_swap hP hs a b]
    simp only [evc, hsymc]
  have hL₁ : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hD : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) (h' ^ m)).IsLB := LB.isLB_linComb hL₁ _ _
  have e0 := pull_translDiff hL₁ (h' ^ m) hD (snd A T) (fst A T)
  rw [(cls_eq_zero_iff hD).2 htd, map_zero] at e0
  have hu : ∀ u : A ⊗ T ⟶ A, CechPic.pull u.left (cls _ hL₁) = evc hP u u := fun u => by
    rw [cls_ev hP, pull_evc, Category.comp_id]
  rw [hu, hu] at e0
  have hXX : evc hP (snd A T ≫ h' ^ m) (snd A T ≫ h' ^ m) = 0 := by
    rw [← pull_evc, hT (evc hP (h' ^ m) (h' ^ m)), map_zero]
  have key : evc hP (snd A T ≫ h' ^ m) (snd A T ≫ h' ^ m) + evc hP (snd A T ≫ h' ^ m) (fst A T) +
      (evc hP (fst A T) (snd A T ≫ h' ^ m) + evc hP (fst A T) (fst A T)) - evc hP (fst A T) (fst A T) = 0 := by
    rw [← eR, ← eR, ← eL]
    exact e0.symm
  rw [hXX, eS (fst A T) (snd A T ≫ h' ^ m)] at key
  have h2 : 2 • evc hP (snd A T ≫ h' ^ m) (fst A T) = 0 := by
    rw [two_nsmul, ← key]
    abel
  rw [comp_pow_pt, evc_pow_left hP (fun a a' t => eL a a' t)] at h2
  have hsq' : toUnit (A ⊗ T) ≫ h₀ = (snd A T ≫ h') ^ 2 := by
    rw [← comp_pow_pt, hsq, ← Category.assoc, toUnit_unique (snd A T ≫ toUnit T) (toUnit _)]
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow P m).IsLB := LB.isLB_linComb hP _ _
  have eQ : ∀ {Y : Over S} (a b : Y ⟶ A), evc hQ a b = m • evc hP a b := by
    intro Y a b
    rw [evc, cls_heckePow hP m hQ, map_nsmul]
    rfl
  refine (cls_eq_zero_iff (pull_isLB (pull_isLB hQ _) _)).1 ?_
  rw [cls_pull (pull_isLB hQ _)]
  change CechPic.pull (fst A T).left (evc hQ (toUnit A ≫ h₀) (𝟙 A)) = 0
  rw [pull_evc, eQ, Category.comp_id, ← Category.assoc, toUnit_unique (fst A T ≫ toUnit A) (toUnit _), hsq',
    evc_pow_left hP (fun a a' t => eL a a' t), smul_comm]
  exact h2

end GlobalTheory.PicBilin
