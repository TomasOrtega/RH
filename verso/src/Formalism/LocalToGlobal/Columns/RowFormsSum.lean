import Mathlib
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.GL3MeanSquares.HookFormulaTorsion.DoubleCosetDecompositionAll

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Abstract

variable {Γ D M : Type} [Group Γ] [MulAction Γ D] [AddCommGroup M] [Module ℚ M]

/- English proof (translation)
Rewrite using `[MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]`.
-/
theorem rf_smul_one_coset (N : Subgroup Γ) (γ : Γ) : γ • ((1 : Γ) : Γ ⧸ N) = ((1 : Γ) : Γ ⧸ N) ↔ γ ∈ N := by
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]

def rf_stabEquiv (N : Subgroup Γ) (r : D) :
    MulAction.stabilizer N r ≃ MulAction.stabilizer Γ ((r, ((1 : Γ) : Γ ⧸ N)) : D × Γ ⧸ N) where
  toFun n := ⟨(n.1 : Γ), Prod.ext n.2 ((rf_smul_one_coset N _).mpr n.1.2)⟩
  invFun γ := ⟨⟨γ.1, (rf_smul_one_coset N _).mp (congrArg Prod.snd γ.2)⟩, congrArg Prod.fst γ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Use `Fintype.ofFinite (Γ ⧸ N)` as an intermediate fact. Establish `hinj : Function.Injective fun r : D => ((r, ((1 : Γ) : Γ ⧸ N)) : D × Γ ⧸ N)` using `fun a b h => congrArg Prod.fst h`. Establish `key` using `Formalism.HermitianLattices.RamifiedLatticeOperators.fubini_over_orbits Γ (D × Γ ⧸ N) D M Prod.fst (fun y => Finset.univ.image fun a : Γ ⧸ N => (y, a)) (fun p => F p.1) (RN.image fun r : D => ((r, ((1 : Γ) : Γ ⧸ N)) : D × Γ ⧸ N)) RΓ (fun _ _ => rfl) (by`. Introduce `p y`. Rewrite using `[Finset.mem_image]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, -, rfl⟩`. Both sides reduce to the same expression. Introduce and unpack `rfl`. Conclude with `⟨p.2, Finset.mem_univ _, rfl⟩)`.

Use the proof step `(fun γ p => hF γ p.1) hfin`. Use the proof step `(by`. Introduce and unpack `⟨d, a⟩`. Proceed by induction on `a using QuotientGroup.induction_on with`. Consider the case `H g`.

Take `⟨r0, ⟨hr0, n, hn⟩, huniq⟩` from `hN (g⁻¹ • d)`. Establish `hn' : (n : Γ) • g⁻¹ • d = r0` using `hn`. Use `⟨(r0, ((1 : Γ) : Γ ⧸ N)), ⟨Finset.mem_image_of_mem _ hr0, (n : Γ) * g⁻¹, ?_⟩, ?_⟩` and prove the remaining obligations. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show ((n : Γ) * g⁻¹) • d = r0`.

Rewrite using `[mul_smul, hn']`. Use `show ((n : Γ) * g⁻¹) • ((g : Γ) : Γ ⧸ N) = ((1 : Γ) : Γ ⧸ N)`. Rewrite using `[MulAction.Quotient.smul_coe, smul_eq_mul, inv_mul_cancel_right, eq_comm, QuotientGroup.eq, inv_one, one_mul]`. Conclude with `n.2`. Introduce and unpack `p ⟨hp, γ, hγ⟩`.

Take `⟨r, hr, rfl⟩` from `Finset.mem_image.mp hp`. Establish `h1 : γ • d = r` using `congrArg Prod.fst hγ`. Establish `h2 : γ • ((g : Γ) : Γ ⧸ N) = ((1 : Γ) : Γ ⧸ N)` using `congrArg Prod.snd hγ`. Establish `h3 : γ * g ∈ N`. Rewrite `h2` using `[MulAction.Quotient.smul_coe, smul_eq_mul, eq_comm, QuotientGroup.eq, inv_one, one_mul]`.

Conclude with `h2`. Establish `h4 : r = r0` using `huniq r ⟨hr, ⟨γ * g, h3⟩, by show (γ * g) • g⁻¹ • d = r`. Rewrite using `[smul_smul, mul_inv_cancel_right, h1]⟩`. Rewrite using `[h4])`. Use `hΓ`.

Rewrite `key` using `[Finset.sum_image (fun a _ b _ h => hinj h)]`. Rewrite using `[Finset.smul_sum]`. Use `Eq.trans (Finset.sum_congr rfl fun r _ => ?_) (key.trans (Finset.sum_congr rfl fun y _ => ?_))` and prove the remaining obligations. Rewrite using `[Nat.card_congr (rf_stabEquiv N r)]`. Rewrite using `[Finset.sum_image (fun a _ b _ h => congrArg Prod.snd h)] show _ • ∑ _a : Γ ⧸ N, F y = _`.

Rewrite using `[Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul, smul_comm]`.
-/
theorem rf_cs_subgroup (N : Subgroup Γ) [Finite (Γ ⧸ N)] (F : D → M) (hF : ∀ (γ : Γ) (d : D), F (γ • d) = F d)
    (hfin : ∀ d : D, Finite (MulAction.stabilizer Γ d)) (RΓ RN : Finset D)
    (hΓ : ∀ d : D, ∃! r, r ∈ RΓ ∧ r ∈ MulAction.orbit Γ d)
    (hN : ∀ d : D, ∃! r, r ∈ RN ∧ r ∈ MulAction.orbit N d) :
    ∑ r ∈ RN, ((Nat.card (MulAction.stabilizer N r) : ℚ))⁻¹ • F r =
      (Nat.card (Γ ⧸ N) : ℚ) • ∑ r ∈ RΓ, ((Nat.card (MulAction.stabilizer Γ r) : ℚ))⁻¹ • F r := by
  classical
  have := Fintype.ofFinite (Γ ⧸ N)
  have hinj : Function.Injective fun r : D => ((r, ((1 : Γ) : Γ ⧸ N)) : D × Γ ⧸ N) := fun a b h => congrArg Prod.fst h
  have key := Formalism.HermitianLattices.RamifiedLatticeOperators.fubini_over_orbits Γ (D × Γ ⧸ N) D M Prod.fst
    (fun y => Finset.univ.image fun a : Γ ⧸ N => (y, a)) (fun p => F p.1)
    (RN.image fun r : D => ((r, ((1 : Γ) : Γ ⧸ N)) : D × Γ ⧸ N)) RΓ (fun _ _ => rfl)
    (by
      intro p y
      rw [Finset.mem_image]
      constructor
      · rintro ⟨a, -, rfl⟩
        rfl
      · rintro rfl
        exact ⟨p.2, Finset.mem_univ _, rfl⟩)
    (fun γ p => hF γ p.1) hfin
    (by
      rintro ⟨d, a⟩
      induction a using QuotientGroup.induction_on with
      | H g =>
      obtain ⟨r0, ⟨hr0, n, hn⟩, huniq⟩ := hN (g⁻¹ • d)
      have hn' : (n : Γ) • g⁻¹ • d = r0 := hn
      refine ⟨(r0, ((1 : Γ) : Γ ⧸ N)), ⟨Finset.mem_image_of_mem _ hr0, (n : Γ) * g⁻¹, ?_⟩, ?_⟩
      · refine Prod.ext ?_ ?_
        · show ((n : Γ) * g⁻¹) • d = r0
          rw [mul_smul, hn']
        · show ((n : Γ) * g⁻¹) • ((g : Γ) : Γ ⧸ N) = ((1 : Γ) : Γ ⧸ N)
          rw [MulAction.Quotient.smul_coe, smul_eq_mul, inv_mul_cancel_right, eq_comm, QuotientGroup.eq, inv_one, one_mul]
          exact n.2
      · rintro p ⟨hp, γ, hγ⟩
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
        have h1 : γ • d = r := congrArg Prod.fst hγ
        have h2 : γ • ((g : Γ) : Γ ⧸ N) = ((1 : Γ) : Γ ⧸ N) := congrArg Prod.snd hγ
        have h3 : γ * g ∈ N := by
          rw [MulAction.Quotient.smul_coe, smul_eq_mul, eq_comm, QuotientGroup.eq, inv_one, one_mul] at h2
          exact h2
        have h4 : r = r0 := huniq r ⟨hr, ⟨γ * g, h3⟩, by
          show (γ * g) • g⁻¹ • d = r
          rw [smul_smul, mul_inv_cancel_right, h1]⟩
        rw [h4])
    hΓ
  rw [Finset.sum_image (fun a _ b _ h => hinj h)] at key
  rw [Finset.smul_sum]
  refine Eq.trans (Finset.sum_congr rfl fun r _ => ?_) (key.trans (Finset.sum_congr rfl fun y _ => ?_))
  · rw [Nat.card_congr (rf_stabEquiv N r)]
  · rw [Finset.sum_image (fun a _ b _ h => congrArg Prod.snd h)]
    show _ • ∑ _a : Γ ⧸ N, F y = _
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul, smul_comm]

end Abstract

section TwoLevels

variable {X : Fields} {n r : ℕ} {ST SG SG0 : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) {ι : GLG X.E r SG0 →* GLG X.E n SG} {ΛP ΛK : LevFam X.E X.K n SG}
  {Λ0 : LevFam X.E X.K r SG0}

def rf_subN (ΛP ΛK : LevFam X.E X.K n SG) : Subgroup (FormG ΛP) where
  carrier := {g | (g.2.1 : GLG X.E n SG) ∈ ΛK.grp}
  one_mem' := ΛK.grp.one_mem
  mul_mem' := fun ha hb => ΛK.grp.mul_mem ha hb
  inv_mem' := fun ha => ΛK.grp.inv_mem ha

def rf_cosetEquiv (H : LevFam.Split ι ΛP ΛK Λ0) (hinj : ∀ a : ↥Λ0.grp, ι a.1 ∈ ΛK.grp → a = 1) :
    ↥Λ0.grp ≃ FormG ΛP ⧸ rf_subN ΛP ΛK :=
  Equiv.ofBijective (fun a => ((((1 : UF X.E n), (⟨ι a.1, (H.emb a).1⟩ : ↥ΛP.grp)) : FormG ΛP) : FormG ΛP ⧸ rf_subN ΛP ΛK)) (by
    constructor
    · intro a b hab
      have h1 := QuotientGroup.eq.mp hab
      have h2 : (ι a.1)⁻¹ * ι b.1 ∈ ΛK.grp := h1
      have h3 : ι ((a⁻¹ * b : ↥Λ0.grp) : GLG X.E r SG0) ∈ ΛK.grp := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
        exact h2
      exact (inv_mul_eq_one.mp (hinj _ h3))
    · intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
      obtain ⟨a, k, e1, -⟩ := H.fac g.2
      refine ⟨a, QuotientGroup.eq.mpr ?_⟩
      show (ι a.1)⁻¹ * g.2.1 ∈ ΛK.grp
      rw [e1, inv_mul_cancel_left]
      exact k.2)

/- English proof (translation)
Set `_` to `hP.fintypeCl`. Set `_` to `hK.fintypeCl`. Establish `: Finite ↥Λ0.grp` using `inferInstance`. Establish `: Finite (FormG ΛP ⧸ rf_subN ΛP ΛK)` using `Finite.of_equiv _ (rf_cosetEquiv H hinj)`. Establish `hinjP : Function.Injective sP.rep` using `fun c c' hc => by rw [← sP.spec c, hc, sP.spec]`.

Establish `hinjK : Function.Injective sK.rep` using `fun c c' hc => by rw [← sK.spec c, hc, sK.spec]`. Set `up : FormG ΛK → ↥(rf_subN ΛP ΛK)` to `fun g => ⟨(g.1, ⟨g.2.1, (H.sub g.2).1⟩), g.2.2⟩`. Set `dn : ↥(rf_subN ΛP ΛK) → FormG ΛK` to `fun g => (g.1.1, ⟨g.1.2.1, g.2⟩)`. Establish `hstab : ∀ d : DecoSet X.E n ST SG, MulAction.stabilizer (FormG ΛK) d ≃ MulAction.stabilizer ↥(rf_subN ΛP ΛK) d` using `fun d => { toFun := fun g => ⟨up g.1, g.2⟩ invFun := fun g => ⟨dn g.1, g.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Establish `key` using `rf_cs_subgroup (Γ := FormG ΛP) (D := DecoSet X.E n ST SG) (M := X.K) (rf_subN ΛP ΛK) F (fun g d => hF g.1 g.2 d) hP.fin_stab (Finset.univ.image sP.rep) (Finset.univ.image sK.rep) (by`.

Introduce `a`. Use `⟨sP.rep ((formGSD C ΛP).cls a), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `((formGSD C ΛP).cls_eq_iff _ _).mp (sP.spec _)`. Introduce and unpack `r ⟨hr, hr2⟩`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.mp hr`.

Establish `h1 : (formGSD C ΛP).cls (sP.rep c) = (formGSD C ΛP).cls a` using `((formGSD C ΛP).cls_eq_iff _ _).mpr hr2`. Rewrite using `[← h1, sP.spec])`. Use the proof step `(by`. Introduce `a`. Use `⟨sK.rep ((formGSD C ΛK).cls a), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩` and prove the remaining obligations.

Take `⟨g, hg⟩` from `((formGSD C ΛK).cls_eq_iff _ _).mp (sK.spec ((formGSD C ΛK).cls a))`. Conclude with `⟨up g, hg⟩`. Introduce and unpack `r ⟨hr, g, hg⟩`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.mp hr`. Establish `h1 : (formGSD C ΛK).cls (sK.rep c) = (formGSD C ΛK).cls a` using `((formGSD C ΛK).cls_eq_iff _ _).mpr ⟨dn g, hg⟩`.

Rewrite using `[← h1, sK.spec])`. Rewrite `key` using `[Finset.sum_image (fun c _ c' _ hc => hinjK hc), Finset.sum_image (fun c _ c' _ hc => hinjP hc)]`. Unfold `GSD.csOf`. Rewrite `key` using `[← Nat.card_congr (rf_cosetEquiv H hinj)]`. Rewrite `key` using `[Rat.smul_def, Rat.cast_natCast]`.

Use `Eq.trans (Finset.sum_congr rfl fun c _ => ?_) (key.trans (congrArg _ (Finset.sum_congr rfl fun c _ => ?_)))` and prove the remaining obligations. Rewrite using `[(formGSD C ΛK).wt_eq, Rat.smul_def, Rat.cast_inv, Rat.cast_natCast, ← Nat.card_congr (hstab (sK.rep c)), smul_eq_mul]`. Rewrite using `[(formGSD C ΛP).wt_eq, Rat.smul_def, Rat.cast_inv, Rat.cast_natCast, smul_eq_mul]`.
-/
theorem rf_cs_split (H : LevFam.Split ι ΛP ΛK Λ0) (hinj : ∀ a : ↥Λ0.grp, ι a.1 ∈ ΛK.grp → a = 1)
    (hP : (formGSD C ΛP).Ok) (hK : (formGSD C ΛK).Ok) (sP : (formGSD C ΛP).Sec) (sK : (formGSD C ΛK).Sec)
    (F : DecoSet X.E n ST SG → X.K)
    (hF : ∀ (γ : UF X.E n) (h : ↥ΛP.grp) (d : DecoSet X.E n ST SG), F ((γ, (h.1 : GLG X.E n SG)) • d) = F d) :
    (formGSD C ΛK).csOf hK sK F = (Nat.card ↥Λ0.grp : X.K) * (formGSD C ΛP).csOf hP sP F := by
  classical
  let _ := hP.fintypeCl
  let _ := hK.fintypeCl
  have : Finite ↥Λ0.grp := inferInstance
  have : Finite (FormG ΛP ⧸ rf_subN ΛP ΛK) := Finite.of_equiv _ (rf_cosetEquiv H hinj)
  have hinjP : Function.Injective sP.rep := fun c c' hc => by rw [← sP.spec c, hc, sP.spec]
  have hinjK : Function.Injective sK.rep := fun c c' hc => by rw [← sK.spec c, hc, sK.spec]

  let up : FormG ΛK → ↥(rf_subN ΛP ΛK) := fun g => ⟨(g.1, ⟨g.2.1, (H.sub g.2).1⟩), g.2.2⟩
  let dn : ↥(rf_subN ΛP ΛK) → FormG ΛK := fun g => (g.1.1, ⟨g.1.2.1, g.2⟩)
  have hstab : ∀ d : DecoSet X.E n ST SG,
      MulAction.stabilizer (FormG ΛK) d ≃ MulAction.stabilizer ↥(rf_subN ΛP ΛK) d := fun d =>
    { toFun := fun g => ⟨up g.1, g.2⟩
      invFun := fun g => ⟨dn g.1, g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have key := rf_cs_subgroup (Γ := FormG ΛP) (D := DecoSet X.E n ST SG) (M := X.K) (rf_subN ΛP ΛK) F
    (fun g d => hF g.1 g.2 d) hP.fin_stab (Finset.univ.image sP.rep) (Finset.univ.image sK.rep)
    (by
      intro a
      refine ⟨sP.rep ((formGSD C ΛP).cls a), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
      · exact ((formGSD C ΛP).cls_eq_iff _ _).mp (sP.spec _)
      · rintro r ⟨hr, hr2⟩
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
        have h1 : (formGSD C ΛP).cls (sP.rep c) = (formGSD C ΛP).cls a := ((formGSD C ΛP).cls_eq_iff _ _).mpr hr2
        rw [← h1, sP.spec])
    (by
      intro a
      refine ⟨sK.rep ((formGSD C ΛK).cls a), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
      · obtain ⟨g, hg⟩ := ((formGSD C ΛK).cls_eq_iff _ _).mp (sK.spec ((formGSD C ΛK).cls a))
        exact ⟨up g, hg⟩
      · rintro r ⟨hr, g, hg⟩
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
        have h1 : (formGSD C ΛK).cls (sK.rep c) = (formGSD C ΛK).cls a :=
          ((formGSD C ΛK).cls_eq_iff _ _).mpr ⟨dn g, hg⟩
        rw [← h1, sK.spec])
  rw [Finset.sum_image (fun c _ c' _ hc => hinjK hc), Finset.sum_image (fun c _ c' _ hc => hinjP hc)] at key
  unfold GSD.csOf
  rw [← Nat.card_congr (rf_cosetEquiv H hinj)] at key
  rw [Rat.smul_def, Rat.cast_natCast] at key
  refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) (key.trans (congrArg _ (Finset.sum_congr rfl fun c _ => ?_)))
  · rw [(formGSD C ΛK).wt_eq, Rat.smul_def, Rat.cast_inv, Rat.cast_natCast, ← Nat.card_congr (hstab (sK.rep c)), smul_eq_mul]
  · rw [(formGSD C ΛP).wt_eq, Rat.smul_def, Rat.cast_inv, Rat.cast_natCast, smul_eq_mul]

/- English proof (translation)
Establish `h0 : (Nat.card ↥Λ0.grp : X.K) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Establish `h1` using `rf_cs_split C H hinj hP hK (formGSD C ΛP).outSec (formGSD C ΛK).outSec (fun d => C.pair (φ d) (ψ d)) (fun γ h d => by`. Establish `e1` using `hφ ((γ, h) : FormG ΛP) d`. Establish `e2` using `hψ ((γ, h) : FormG ΛP) d`. Use `show C.pair (φ ((γ, (h.1 : GLG X.E n SG)) • d)) (ψ ((γ, (h.1 : GLG X.E n SG)) • d)) = _`.

Establish `e1' : φ ((γ, (h.1 : GLG X.E n SG)) • d) = (formGSD C ΛP).ρ ((γ, h) : FormG ΛP) (φ d)` using `e1`. Establish `e2' : ψ ((γ, (h.1 : GLG X.E n SG)) • d) = (formGSD C ΛP).ρ ((γ, h) : FormG ΛP) (ψ d)` using `e2`. Rewrite using `[e1', e2']`. Conclude with `hP.inv _ _ _)`. Use `show (formGSD C ΛP).csOf hP (formGSD C ΛP).outSec (fun d => C.pair (φ d) (ψ d)) = _ * (formGSD C ΛK).csOf hK (formGSD C ΛK).outSec (fun d => C.pair (φ d) (ψ d))`.

Rewrite using `[h1, inv_mul_cancel_left₀ h0]`.
-/
theorem rf_ip_split (H : LevFam.Split ι ΛP ΛK Λ0) (hinj : ∀ a : ↥Λ0.grp, ι a.1 ∈ ΛK.grp → a = 1)
    (hP : (formGSD C ΛP).Ok) (hK : (formGSD C ΛK).Ok) (φ ψ : DecoSet X.E n ST SG → C.V)
    (hφ : φ ∈ (formGSD C ΛP).EqFun) (hψ : ψ ∈ (formGSD C ΛP).EqFun) :
    (formGSD C ΛP).ip hP φ ψ = ((Nat.card ↥Λ0.grp : X.K))⁻¹ * (formGSD C ΛK).ip hK φ ψ := by
  have h0 : (Nat.card ↥Λ0.grp : X.K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1 := rf_cs_split C H hinj hP hK (formGSD C ΛP).outSec (formGSD C ΛK).outSec (fun d => C.pair (φ d) (ψ d))
    (fun γ h d => by
      have e1 := hφ ((γ, h) : FormG ΛP) d
      have e2 := hψ ((γ, h) : FormG ΛP) d
      show C.pair (φ ((γ, (h.1 : GLG X.E n SG)) • d)) (ψ ((γ, (h.1 : GLG X.E n SG)) • d)) = _
      have e1' : φ ((γ, (h.1 : GLG X.E n SG)) • d) = (formGSD C ΛP).ρ ((γ, h) : FormG ΛP) (φ d) := e1
      have e2' : ψ ((γ, (h.1 : GLG X.E n SG)) • d) = (formGSD C ΛP).ρ ((γ, h) : FormG ΛP) (ψ d) := e2
      rw [e1', e2']
      exact hP.inv _ _ _)
  show (formGSD C ΛP).csOf hP (formGSD C ΛP).outSec (fun d => C.pair (φ d) (ψ d)) =
    _ * (formGSD C ΛK).csOf hK (formGSD C ΛK).outSec (fun d => C.pair (φ d) (ψ d))
  rw [h1, inv_mul_cancel_left₀ h0]

end TwoLevels

section Rows

/- English proof (translation)
Rewrite `hg` using `[HK_eq_HPar h bl, mem_HPar]`. Take `⟨hB, h0⟩` from `hg`. Use `Subgroup.mem_bot.mp h0` as an intermediate fact. Rewrite `this` using `[firstBlock_diagEmb_eq]`. Then use the resulting hypothesis.
-/
theorem rf_diagEmb_mem_HK {κ : Type} [CommRing κ] {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (g : GL (Fin r) κ)
    (hg : diagEmb κ h g ∈ HK n κ r bl) : g = 1 := by
  rw [HK_eq_HPar h bl, mem_HPar] at hg
  obtain ⟨hB, h0⟩ := hg
  have := Subgroup.mem_bot.mp h0
  rwa [firstBlock_diagEmb_eq] at this

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

/- English proof (translation)
Use function extensionality and compare the values at `w`. Establish `h1 : unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) a (inlSG w) ∈ (((rowTyK Ch).glue (rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)))) (inlSG w)).H` using `(rowTyKK Ch sel mu).mem_at ⟨_, ha⟩ (inlSG w)`. Rewrite `h1` using `[LevFam.glue_of_mem _ _ (inlSG w) w.2]`. Establish `h2 : unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) a (inlSG w) = diagEmb _ (r_le_X' R) (a w)` using `extGLG_of_mem _ (inlSG w) w.2`. Establish `h3 : diagEmb _ (r_le_X' R) (a w) ∈ HK (R.N R.m - 1) (𝓞 X.E ⧸ w.1.asIdeal) R.r (List.replicate R.m R.t)`.

Rewrite using `[← h2]`. Conclude with `h1`. Conclude with `rf_diagEmb_mem_HK _ _ _ h3`.
-/
theorem rf_g0Hat_injX (a : G0 X.E Pr.vGs R.r) (ha : unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) a ∈ (rowTyKK Ch sel mu).grp) : a = 1 := by
  funext w
  have h1 : unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) a (inlSG w) ∈ (((rowTyK Ch).glue
      (rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)))) (inlSG w)).H :=
    (rowTyKK Ch sel mu).mem_at ⟨_, ha⟩ (inlSG w)
  rw [LevFam.glue_of_mem _ _ (inlSG w) w.2] at h1
  have h2 : unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) a (inlSG w) = diagEmb _ (r_le_X' R) (a w) := extGLG_of_mem _ (inlSG w) w.2
  have h3 : diagEmb _ (r_le_X' R) (a w) ∈ HK (R.N R.m - 1) (𝓞 X.E ⧸ w.1.asIdeal) R.r (List.replicate R.m R.t) := by
    rw [← h2]
    exact h1
  exact rf_diagEmb_mem_HK _ _ _ h3

/- English proof (translation)
Use function extensionality and compare the values at `w`. Establish `h1 : unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) a (inlSG w) ∈ (((mtTyK Ch j).glue (mtTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)))) (inlSG w)).H` using `(mtTyKK Ch sel mu j).mem_at ⟨_, ha⟩ (inlSG w)`. Rewrite `h1` using `[LevFam.glue_of_mem _ _ (inlSG w) w.2]`. Establish `h2 : unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) a (inlSG w) = diagEmb _ (r_le_nV R) (a w)` using `extGLG_of_mem _ (inlSG w) w.2`. Establish `h3 : diagEmb _ (r_le_nV R) (a w) ∈ HK R.nV (𝓞 X.E ⧸ w.1.asIdeal) R.r [R.t]`.

Rewrite using `[← h2]`. Conclude with `h1`. Conclude with `rf_diagEmb_mem_HK _ _ _ h3`.
-/
theorem rf_g0Hat_injV (j : ℕ) (a : G0 X.E Pr.vGs R.r) (ha : unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) a ∈ (mtTyKK Ch sel mu j).grp) :
    a = 1 := by
  funext w
  have h1 : unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) a (inlSG w) ∈ (((mtTyK Ch j).glue
      (mtTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)))) (inlSG w)).H :=
    (mtTyKK Ch sel mu j).mem_at ⟨_, ha⟩ (inlSG w)
  rw [LevFam.glue_of_mem _ _ (inlSG w) w.2] at h1
  have h2 : unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) a (inlSG w) = diagEmb _ (r_le_nV R) (a w) := extGLG_of_mem _ (inlSG w) w.2
  have h3 : diagEmb _ (r_le_nV R) (a w) ∈ HK R.nV (𝓞 X.E ⧸ w.1.asIdeal) R.r [R.t] := by
    rw [← h2]
    exact h1
  exact rf_diagEmb_mem_HK _ _ _ h3

/- English proof (translation)
Conclude with `rf_ip_split (rowVal W (rowSG Pr sel mu)) (rowTy_split Ch sel mu P).inv (fun a ha => Subtype.ext (rf_g0Hat_injX Ch sel mu a.1 ha)) h h' φ ψ hφ hψ`.
-/
theorem levelSumX (h : (mtildeGSD W Ch sel mu P).Ok) (h' : (mtildeKGSD W Ch sel mu).Ok)
    (φ ψ : DecoSet X.E (R.N R.m - 1) ∅ (rowSG Pr sel mu) → VV X.K W.sgTrue)
    (hφ : φ ∈ (mtildeGSD W Ch sel mu P).EqFun) (hψ : ψ ∈ (mtildeGSD W Ch sel mu P).EqFun) :
    (mtildeGSD W Ch sel mu P).ip h φ ψ = ((Nat.card P.grp : X.K))⁻¹ * (mtildeKGSD W Ch sel mu).ip h' φ ψ := by
  exact rf_ip_split (rowVal W (rowSG Pr sel mu)) (rowTy_split Ch sel mu P).inv
    (fun a ha => Subtype.ext (rf_g0Hat_injX Ch sel mu a.1 ha)) h h' φ ψ hφ hψ

/- English proof (translation)
Conclude with `rf_ip_split (mtVal W j (rowSG Pr sel mu)) (mtTy_split Ch sel mu P j).inv (fun a ha => Subtype.ext (rf_g0Hat_injV Ch sel mu j a.1 ha)) h h' φ ψ hφ hψ`.
-/
theorem levelSumV (j : ℕ) (h : (mtGSD W Ch sel mu P j).Ok) (h' : (mtKGSD W Ch sel mu j).Ok)
    (φ ψ : DecoSet X.E R.nV ∅ (rowSG Pr sel mu) → VV X.K (W.lamV j))
    (hφ : φ ∈ (mtGSD W Ch sel mu P j).EqFun) (hψ : ψ ∈ (mtGSD W Ch sel mu P j).EqFun) :
    (mtGSD W Ch sel mu P j).ip h φ ψ = ((Nat.card P.grp : X.K))⁻¹ * (mtKGSD W Ch sel mu j).ip h' φ ψ := by
  exact rf_ip_split (mtVal W j (rowSG Pr sel mu)) (mtTy_split Ch sel mu P j).inv
    (fun a ha => Subtype.ext (rf_g0Hat_injV Ch sel mu j a.1 ha)) h h' φ ψ hφ hψ

/- English proof (translation)
Conclude with `rf_cs_split (rowVal W (rowSG Pr sel mu)) (rowTy_split Ch sel mu P).inv (fun a ha => Subtype.ext (rf_g0Hat_injX Ch sel mu a.1 ha)) h h' _ _ F (fun γ k d => hF (γ, k) d)`.
-/
theorem levelCsX (h : (mtildeGSD W Ch sel mu P).Ok) (h' : (mtildeKGSD W Ch sel mu).Ok)
    (F : DecoSet X.E (R.N R.m - 1) ∅ (rowSG Pr sel mu) → X.K)
    (hF : ∀ (g : (mtildeGSD W Ch sel mu P).G) (d : (mtildeGSD W Ch sel mu P).D), F (g • d) = F d) :
    (mtildeKGSD W Ch sel mu).csOf h' (mtildeKGSD W Ch sel mu).outSec F =
      (Nat.card P.grp : X.K) * (mtildeGSD W Ch sel mu P).csOf h (mtildeGSD W Ch sel mu P).outSec F := by
  exact rf_cs_split (rowVal W (rowSG Pr sel mu)) (rowTy_split Ch sel mu P).inv
    (fun a ha => Subtype.ext (rf_g0Hat_injX Ch sel mu a.1 ha)) h h' _ _ F
    (fun γ k d => hF (γ, k) d)

end Rows

end Formalism.L2.Col
