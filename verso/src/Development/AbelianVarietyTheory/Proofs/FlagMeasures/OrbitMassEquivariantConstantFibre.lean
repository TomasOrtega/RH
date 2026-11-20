import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolMulPosLeConj
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.MassFibre

/- English proof (translation)
Establish `h1` using `Subgroup.card_mul_index (H.subgroupOf K)`. Establish `h2 : Nat.card (H.subgroupOf K) = Nat.card H` using `Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv`. Rewrite `h1` using `[h2]`. Conclude with `h1`.
-/
theorem card_mul_relIndex {G : Type} [Group G] (H K : Subgroup G) (hle : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  have h1 := Subgroup.card_mul_index (H.subgroupOf K)
  have h2 : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h2] at h1
  exact h1

/- English proof (translation)
Use `split_ifs with h`. Establish `: (H : Set G).Infinite`. Break down `Nat.card_eq_zero.mp h with h' | h'` into its components or cases. Conclude with `absurd h' (not_isEmpty_of_nonempty _)`. Conclude with `Set.infinite_coe_iff.mp h'`.

Rewrite using `[Set.encard_eq_top_iff.mpr this]`. Both sides reduce to the same expression. Establish `hf : (H : Set G).Finite`. Use `Nat.finite_of_card_ne_zero h` as an intermediate fact. Conclude with `Set.toFinite _`.

Rewrite using `[← hf.cast_ncard_eq, ← Nat.card_coe_set_eq]`. Both sides reduce to the same expression.
-/
theorem encard_coe_subgroup {G : Type} [Group G] (H : Subgroup G) :
    ((H : Set G).encard : ℝ≥0∞) = if Nat.card H = 0 then ⊤ else (Nat.card H : ℝ≥0∞) := by
  split_ifs with h
  · have : (H : Set G).Infinite := by
      rcases Nat.card_eq_zero.mp h with h' | h'
      · exact absurd h' (not_isEmpty_of_nonempty _)
      · exact Set.infinite_coe_iff.mp h'
    rw [Set.encard_eq_top_iff.mpr this]; rfl
  · have hf : (H : Set G).Finite := by
      have := Nat.finite_of_card_ne_zero h
      exact Set.toFinite _
    rw [← hf.cast_ncard_eq, ← Nat.card_coe_set_eq]
    rfl

/- English proof (translation)
Establish `hc` using `card_mul_relIndex H K hle`. Rewrite using `[encard_coe_subgroup, encard_coe_subgroup]`. Distinguish the cases in `hK : Nat.card K = 0`. Establish `hH : Nat.card H = 0`. Rewrite `hc` using `[hK]`.

Break down `Nat.mul_eq_zero.mp hc with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hr`. Simplify using `[hH, hK]`. Establish `hH : Nat.card H ≠ 0`.

Introduce `h`. Rewrite `hc` using `[h, zero_mul]`. Conclude with `hK hc.symm`. Rewrite using `[if_neg hH, if_neg hK, ← hc]`. Use `push_cast`.

Rewrite using `[ENNReal.mul_inv (Or.inl (by exact_mod_cast hH)) (Or.inl (by simp)), mul_comm, mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hr) (by simp), mul_one]`.
-/
theorem inv_encard_eq_relIndex_mul {G : Type} [Group G] (H K : Subgroup G) (hle : H ≤ K)
    (hr : H.relIndex K ≠ 0) :
    (((H : Set G).encard : ℝ≥0∞))⁻¹ = (H.relIndex K : ℝ≥0∞) * (((K : Set G).encard : ℝ≥0∞))⁻¹ := by
  have hc := card_mul_relIndex H K hle
  rw [encard_coe_subgroup, encard_coe_subgroup]
  by_cases hK : Nat.card K = 0
  · have hH : Nat.card H = 0 := by
      rw [hK] at hc
      rcases Nat.mul_eq_zero.mp hc with h | h
      · exact h
      · exact absurd h hr
    simp [hH, hK]
  · have hH : Nat.card H ≠ 0 := by
      intro h; rw [h, zero_mul] at hc; exact hK hc.symm
    rw [if_neg hH, if_neg hK, ← hc]
    push_cast
    rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast hH)) (Or.inl (by simp)), mul_comm,
      mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hr) (by simp), mul_one]

end GlobalTheory.MassFibre

namespace GlobalTheory.MassFibre

open MulAction

noncomputable def wt {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (y : Y) : ℝ≥0∞ :=
  ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹

/- English proof (translation)
Unfold `wt`. Use `congr 2`. Establish `hset : ((Γ ⊓ MulAction.stabilizer G (γ • y) : Subgroup G) : Set G) = (fun h => γ * h * γ⁻¹) '' ((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G)`. Use extensionality with `x`. Simplify using `only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_image]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx1, hx2⟩`. Use `⟨γ⁻¹ * x * γ, ⟨?_, ?_⟩, by group⟩` and prove the remaining obligations. Conclude with `Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) hx1) hγ`. Rewrite using `[mul_smul, mul_smul, hx2, inv_smul_smul]`.

Introduce and unpack `⟨h, ⟨hh1, hh2⟩, rfl⟩`. Use `⟨Γ.mul_mem (Γ.mul_mem hγ hh1) (Γ.inv_mem hγ), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, mul_smul, inv_smul_smul, hh2]`. Rewrite using `[hset, Function.Injective.encard_image]`. Introduce `a b hab`.

Simplify using `using hab`.
-/
theorem wt_smul {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (γ : G)
    (hγ : γ ∈ Γ) (y : Y) : wt Γ (γ • y) = wt Γ y := by
  unfold wt
  congr 2
  have hset : ((Γ ⊓ MulAction.stabilizer G (γ • y) : Subgroup G) : Set G)
      = (fun h => γ * h * γ⁻¹) '' ((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G) := by
    ext x
    simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      Set.mem_image]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨γ⁻¹ * x * γ, ⟨?_, ?_⟩, by group⟩
      · exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) hx1) hγ
      · rw [mul_smul, mul_smul, hx2, inv_smul_smul]
    · rintro ⟨h, ⟨hh1, hh2⟩, rfl⟩
      refine ⟨Γ.mul_mem (Γ.mul_mem hγ hh1) (Γ.inv_mem hγ), ?_⟩
      rw [mul_smul, mul_smul, inv_smul_smul, hh2]
  rw [hset, Function.Injective.encard_image]
  intro a b hab
  simpa using hab

/- English proof (translation)
Take `⟨γ, rfl⟩` from `h`. Use `show wt Γ (γ • y) = wt Γ y`. Rewrite using `[Subgroup.smul_def]`. Conclude with `wt_smul Γ γ γ.2 y`.
-/
theorem wt_of_mem_orbit {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y]
    {y y' : Y} (h : y' ∈ MulAction.orbit Γ y) : wt Γ y' = wt Γ y := by
  obtain ⟨γ, rfl⟩ := h
  show wt Γ (γ • y) = wt Γ y
  rw [Subgroup.smul_def]
  exact wt_smul Γ γ γ.2 y

/- English proof (translation)
The claim follows from `wt_of_mem_orbit Γ (Quotient.mk_out (s := MulAction.orbitRel Γ Y) y)`.
-/
theorem wt_out_mk {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (y : Y) :
    wt Γ (Quotient.out (Quotient.mk (MulAction.orbitRel Γ Y) y : MulAction.orbitRel.Quotient Γ Y)) = wt Γ y :=
  wt_of_mem_orbit Γ (Quotient.mk_out (s := MulAction.orbitRel Γ Y) y)

end GlobalTheory.MassFibre

namespace GlobalTheory.MassFibre

/- English proof (translation)
Distinguish the cases in `hz : Quotient.out O ∈ S`. Use `swap`. Rewrite using `[if_neg hz, mul_zero] haveI : IsEmpty {P // fbar P = O} := by`. Use `⟨fun ⟨P, hP⟩ => ?_⟩` and prove the remaining obligations. Establish `h1 : Quotient.mk (MulAction.orbitRel Γ Z) (f (Quotient.out P)) = Quotient.mk (MulAction.orbitRel Γ Z) (Quotient.out O)`.

Rewrite using `[← hfbar, Quotient.out_eq, Quotient.out_eq, hP]`. Take `⟨γ, hγ⟩` from `Quotient.exact h1`. Conclude with `(hemp _ hz).false ⟨(γ⁻¹ : G) • Quotient.out P, by`. Rewrite using `[hf, ← hγ]`. Simplify using `[Subgroup.smul_def]⟩`.

Simplify using the standard rewrite rules. Rewrite using `[if_pos hz]`. Take `⟨z, hzO⟩ : ∃ z, Quotient.out O = z` from `⟨_, rfl⟩`. Rewrite `hz`, the goal using `[hzO]`. Establish `hOz : Quotient.mk (MulAction.orbitRel Γ Z) z = O` using `by rw [← hzO, Quotient.out_eq]`.

Set `Δ : Subgroup G` to `Γ ⊓ MulAction.stabilizer G z`. Establish `hΔ : ∀ {g : G}, g ∈ Δ ↔ g ∈ Γ ∧ g • z = z` using `fun {g} => by`. Simplify using `[Δ, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]`. Set `p : SubMulAction Δ Y` to `{ carrier := f ⁻¹' {z} smul_mem' := fun δ y hy => by`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢`.

Rewrite using `[Subgroup.smul_def, hf, hy]`. Conclude with `(hΔ.mp δ.2).2 }`. Establish `hmem : ∀ y : Y, y ∈ p ↔ f y = z` using `fun y => Iff.rfl`. Set `e : p ≃ {y // f y = z}` to `Equiv.subtypeEquivRight hmem`. Use `haveI : Finite {y // f y = z} := (hfin z hz).1`.

Use `haveI : Finite p := Finite.of_equiv _ e.symm`. Establish `hcard : Nat.card p = n` using `(Nat.card_congr e).trans (hfin z hz).2`. Set `φ : MulAction.orbitRel.Quotient Δ p → {P // fbar P = O}` to `fun Q => ⟨Quotient.mk _ (Quotient.out Q : p).1, by`. Rewrite using `[hfbar, (hmem _).mp (Quotient.out Q).2, hOz]⟩`. Establish `hinj : Function.Injective φ`.

Introduce `Q1 Q2 h`. Establish `h'` using `congrArg Subtype.val h`. Take `⟨γ, hγ⟩` from `Quotient.exact h'`. Establish `hγΔ : (γ : G) ∈ Δ`. Use `hΔ.mpr ⟨γ.2, ?_⟩` and prove the remaining obligations.

Establish `hy1` using `(hmem _).mp (Quotient.out Q1).2`. Establish `hy2` using `(hmem _).mp (Quotient.out Q2).2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Quotient.out_equiv_out]`. Use `⟨⟨γ, hγΔ⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hγ`. Establish `hsurj : Function.Surjective φ`. Introduce and unpack `⟨P, hP⟩`. Establish `h1 : Quotient.mk (MulAction.orbitRel Γ Z) (f (Quotient.out P)) = Quotient.mk (MulAction.orbitRel Γ Z) z`.

Rewrite using `[← hfbar, Quotient.out_eq, hP, hOz]`. Take `⟨γ, hγ⟩` from `Quotient.exact h1`. Set `y' : p` to `⟨(γ⁻¹ : G) • Quotient.out P, by`. Rewrite using `[hmem, hf, ← hγ]`. Simplify using `[Subgroup.smul_def]⟩`.

Use `⟨Quotient.mk _ y', Subtype.ext ?_⟩` and prove the remaining obligations. Take `⟨δ, hδ⟩` from `(Quotient.mk_out (s := MulAction.orbitRel Δ p) y')`. Use `show Quotient.mk _ _ = P`. Use `conv_rhs => rw [← Quotient.out_eq P]`. Apply `Quotient.sound` to reduce the goal to its premises.

Use `⟨⟨(δ : G) * (γ : G)⁻¹, Γ.mul_mem (hΔ.mp δ.2).1 (Γ.inv_mem γ.2)⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hδ]`. Use `show ((δ : G) * (γ : G)⁻¹) • Quotient.out P = (δ : G) • ((γ⁻¹ : G) • Quotient.out P)`. Rewrite using `[mul_smul]`. Establish `hw : ∀ y : p, wt Γ (y : Y) = ((MulAction.orbit Δ y).ncard : ℝ≥0∞) * wt Γ z`.

Introduce `y`. Establish `hy` using `(hmem _).mp y.2`. Establish `hle : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G) ≤ Δ`. Introduce `g hg`. Rewrite `hg` using `[Subgroup.mem_inf, MulAction.mem_stabilizer_iff]`.

Use `hΔ.mpr ⟨hg.1, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, ← hf, hg.2]`. Establish `hsub : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G).subgroupOf Δ = MulAction.stabilizer Δ y`. Use extensionality with `δ`. Rewrite using `[Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩`. Conclude with `Subtype.ext h`. Introduce `h`. Conclude with `⟨(hΔ.mp δ.2).1, congrArg Subtype.val h⟩`.

Establish `hri : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G).relIndex Δ = (MulAction.orbit Δ y).ncard`. Rewrite using `[Subgroup.relIndex, hsub, MulAction.index_stabilizer]`. Establish `hne : (MulAction.orbit Δ y).ncard ≠ 0` using `(Set.ncard_pos (Set.toFinite _)).mpr ⟨y, MulAction.mem_orbit_self y⟩ |>.ne'`. Unfold `wt`. Rewrite using `[inv_encard_eq_relIndex_mul _ _ hle (hri ▸ hne), hri]`.

Rewrite using `[← (Equiv.ofBijective φ ⟨hinj, hsurj⟩).tsum_eq]`. Use `haveI : Fintype (MulAction.orbitRel.Quotient Δ p) := Fintype.ofFinite _`. Rewrite using `[tsum_fintype]`. Establish `hterm : ∀ Q : MulAction.orbitRel.Quotient Δ p, wt Γ (Quotient.out (Equiv.ofBijective φ ⟨hinj, hsurj⟩ Q).1) = ((MulAction.orbit Δ (Quotient.out Q)).ncard : ℝ≥0∞) * wt Γ z`. Introduce `Q`.

Rewrite using `[← hw]`. Conclude with `wt_out_mk Γ _`. Repeatedly rewrite using `[hterm, ← Finset.sum_mul]`. Use `congr 1`. Establish `hsum : ∑ Q : MulAction.orbitRel.Quotient Δ p, (MulAction.orbit Δ (Quotient.out Q)).ncard = n`.

Rewrite using `[← hcard, Nat.card_congr (MulAction.selfEquivSigmaOrbits Δ p), Nat.card_sigma]`. Use `Finset.sum_congr rfl (fun Q _ => ?_)` and prove the remaining obligations. Rewrite using `[Nat.card_coe_set_eq]`. Rewrite using `[← hsum]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem fibre_sum {G : Type} [Group G] (Γ : Subgroup G) {Y Z : Type} [MulAction G Y] [MulAction G Z]
    (f : Y → Z) (S : Set Z) (n : ℕ) (hf : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (hfin : ∀ z ∈ S, Finite {y // f y = z} ∧ Nat.card {y // f y = z} = n)
    (hemp : ∀ z, z ∉ S → IsEmpty {y // f y = z})
    (fbar : MulAction.orbitRel.Quotient Γ Y → MulAction.orbitRel.Quotient Γ Z)
    (hfbar : ∀ y, fbar (Quotient.mk _ y) = Quotient.mk _ (f y))
    (O : MulAction.orbitRel.Quotient Γ Z) :
    ∑' P : {P // fbar P = O}, wt Γ (Quotient.out P.1) = (n : ℝ≥0∞) * (if Quotient.out O ∈ S then wt Γ (Quotient.out O) else 0) := by

  classical
  by_cases hz : Quotient.out O ∈ S
  swap
  · rw [if_neg hz, mul_zero]
    haveI : IsEmpty {P // fbar P = O} := by
      refine ⟨fun ⟨P, hP⟩ => ?_⟩
      have h1 : Quotient.mk (MulAction.orbitRel Γ Z) (f (Quotient.out P))
          = Quotient.mk (MulAction.orbitRel Γ Z) (Quotient.out O) := by
        rw [← hfbar, Quotient.out_eq, Quotient.out_eq, hP]
      obtain ⟨γ, hγ⟩ := Quotient.exact h1
      exact (hemp _ hz).false ⟨(γ⁻¹ : G) • Quotient.out P, by
        rw [hf, ← hγ]; simp [Subgroup.smul_def]⟩
    simp
  rw [if_pos hz]
  obtain ⟨z, hzO⟩ : ∃ z, Quotient.out O = z := ⟨_, rfl⟩
  rw [hzO] at hz ⊢
  have hOz : Quotient.mk (MulAction.orbitRel Γ Z) z = O := by rw [← hzO, Quotient.out_eq]
  let Δ : Subgroup G := Γ ⊓ MulAction.stabilizer G z
  have hΔ : ∀ {g : G}, g ∈ Δ ↔ g ∈ Γ ∧ g • z = z := fun {g} => by
    simp [Δ, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  let p : SubMulAction Δ Y :=
    { carrier := f ⁻¹' {z}
      smul_mem' := fun δ y hy => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
        rw [Subgroup.smul_def, hf, hy]; exact (hΔ.mp δ.2).2 }
  have hmem : ∀ y : Y, y ∈ p ↔ f y = z := fun y => Iff.rfl
  let e : p ≃ {y // f y = z} := Equiv.subtypeEquivRight hmem
  haveI : Finite {y // f y = z} := (hfin z hz).1
  haveI : Finite p := Finite.of_equiv _ e.symm
  have hcard : Nat.card p = n := (Nat.card_congr e).trans (hfin z hz).2

  let φ : MulAction.orbitRel.Quotient Δ p → {P // fbar P = O} := fun Q =>
    ⟨Quotient.mk _ (Quotient.out Q : p).1, by
      rw [hfbar, (hmem _).mp (Quotient.out Q).2, hOz]⟩
  have hinj : Function.Injective φ := by
    intro Q1 Q2 h
    have h' := congrArg Subtype.val h
    obtain ⟨γ, hγ⟩ := Quotient.exact h'
    have hγΔ : (γ : G) ∈ Δ := by
      refine hΔ.mpr ⟨γ.2, ?_⟩
      have hy1 := (hmem _).mp (Quotient.out Q1).2
      have hy2 := (hmem _).mp (Quotient.out Q2).2
      calc (γ : G) • z = (γ : G) • f (Quotient.out Q2 : p).1 := by rw [hy2]
        _ = f ((γ : G) • (Quotient.out Q2 : p).1) := (hf _ _).symm
        _ = f (Quotient.out Q1 : p).1 := by rw [← hγ]; rfl
        _ = z := hy1
    rw [← Quotient.out_equiv_out]
    refine ⟨⟨γ, hγΔ⟩, ?_⟩
    apply Subtype.ext
    exact hγ
  have hsurj : Function.Surjective φ := by
    rintro ⟨P, hP⟩
    have h1 : Quotient.mk (MulAction.orbitRel Γ Z) (f (Quotient.out P))
        = Quotient.mk (MulAction.orbitRel Γ Z) z := by
      rw [← hfbar, Quotient.out_eq, hP, hOz]
    obtain ⟨γ, hγ⟩ := Quotient.exact h1
    let y' : p := ⟨(γ⁻¹ : G) • Quotient.out P, by
      rw [hmem, hf, ← hγ]; simp [Subgroup.smul_def]⟩
    refine ⟨Quotient.mk _ y', Subtype.ext ?_⟩
    obtain ⟨δ, hδ⟩ := (Quotient.mk_out (s := MulAction.orbitRel Δ p) y')
    show Quotient.mk _ _ = P
    conv_rhs => rw [← Quotient.out_eq P]
    apply Quotient.sound
    refine ⟨⟨(δ : G) * (γ : G)⁻¹, Γ.mul_mem (hΔ.mp δ.2).1 (Γ.inv_mem γ.2)⟩, ?_⟩
    rw [← hδ]
    show ((δ : G) * (γ : G)⁻¹) • Quotient.out P = (δ : G) • ((γ⁻¹ : G) • Quotient.out P)
    rw [mul_smul]

  have hw : ∀ y : p, wt Γ (y : Y) = ((MulAction.orbit Δ y).ncard : ℝ≥0∞) * wt Γ z := by
    intro y
    have hy := (hmem _).mp y.2
    have hle : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G) ≤ Δ := by
      intro g hg
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff] at hg
      refine hΔ.mpr ⟨hg.1, ?_⟩
      rw [← hy, ← hf, hg.2]
    have hsub : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G).subgroupOf Δ
        = MulAction.stabilizer Δ y := by
      ext δ
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
        MulAction.mem_stabilizer_iff]
      constructor
      · rintro ⟨-, h⟩; exact Subtype.ext h
      · intro h; exact ⟨(hΔ.mp δ.2).1, congrArg Subtype.val h⟩
    have hri : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G).relIndex Δ
        = (MulAction.orbit Δ y).ncard := by
      rw [Subgroup.relIndex, hsub, MulAction.index_stabilizer]
    have hne : (MulAction.orbit Δ y).ncard ≠ 0 :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨y, MulAction.mem_orbit_self y⟩ |>.ne'
    unfold wt
    rw [inv_encard_eq_relIndex_mul _ _ hle (hri ▸ hne), hri]
  rw [← (Equiv.ofBijective φ ⟨hinj, hsurj⟩).tsum_eq]
  haveI : Fintype (MulAction.orbitRel.Quotient Δ p) := Fintype.ofFinite _
  rw [tsum_fintype]
  have hterm : ∀ Q : MulAction.orbitRel.Quotient Δ p,
      wt Γ (Quotient.out (Equiv.ofBijective φ ⟨hinj, hsurj⟩ Q).1)
        = ((MulAction.orbit Δ (Quotient.out Q)).ncard : ℝ≥0∞) * wt Γ z := by
    intro Q
    rw [← hw]
    exact wt_out_mk Γ _
  simp_rw [hterm, ← Finset.sum_mul]
  congr 1
  have hsum : ∑ Q : MulAction.orbitRel.Quotient Δ p, (MulAction.orbit Δ (Quotient.out Q)).ncard = n := by
    rw [← hcard, Nat.card_congr (MulAction.selfEquivSigmaOrbits Δ p), Nat.card_sigma]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [Nat.card_coe_set_eq]
  rw [← hsum]
  push_cast
  rfl

/- English proof (translation)
Introduce `G _ Γ Y Z _ _ f S n hf hS hfin hemp`. Set `fbar : MulAction.orbitRel.Quotient Γ Y → MulAction.orbitRel.Quotient Γ Z` to `Quotient.map' f (fun a b h => by`. Take `⟨γ, hγ⟩` from `h`. Use `⟨γ, ?_⟩` and prove the remaining obligations. Use `show (γ : G) • f b = f a`.

Rewrite using `[← hf, ← hγ]`. Use the proof step `rfl)`. Establish `hfbar : ∀ y, fbar (Quotient.mk _ y) = Quotient.mk _ (f y)` using `fun y => rfl`. Establish `key` using `fibre_sum Γ f S n hf hfin hemp fbar hfbar`. Express the relevant statement in the definitionally equal form `∑' o : MulAction.orbitRel.Quotient Γ Y, wt Γ (Quotient.out o) = _`.

Rewrite using `[← (Equiv.sigmaFiberEquiv fbar).tsum_eq, ENNReal.tsum_sigma', ← ENNReal.tsum_mul_left]`. Use `tsum_congr (fun O => ?_)` and prove the remaining obligations. Conclude with `key O`.
-/
theorem mass_fibre : ∀ {G : Type} [Group G] (Γ : Subgroup G) (Y Z : Type) [MulAction G Y] [MulAction G Z] (f : Y → Z) (S : Set Z) (n : ℕ), (∀ (g : G) (y : Y), f (g • y) = g • f y) → (∀ (g : G) (z : Z), z ∈ S → g • z ∈ S) → (∀ z ∈ S, Finite {y // f y = z} ∧ Nat.card {y // f y = z} = n) → (∀ z, z ∉ S → IsEmpty {y // f y = z}) → (∑' o : MulAction.orbitRel.Quotient Γ Y, ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) = (n : ℝ≥0∞) * ∑' o : MulAction.orbitRel.Quotient Γ Z, if o.out ∈ S then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0 := by
  intro G _ Γ Y Z _ _ f S n hf hS hfin hemp
  let fbar : MulAction.orbitRel.Quotient Γ Y → MulAction.orbitRel.Quotient Γ Z :=
    Quotient.map' f (fun a b h => by
      obtain ⟨γ, hγ⟩ := h
      refine ⟨γ, ?_⟩
      show (γ : G) • f b = f a
      rw [← hf, ← hγ]; rfl)
  have hfbar : ∀ y, fbar (Quotient.mk _ y) = Quotient.mk _ (f y) := fun y => rfl
  have key := fibre_sum Γ f S n hf hfin hemp fbar hfbar
  change ∑' o : MulAction.orbitRel.Quotient Γ Y, wt Γ (Quotient.out o) = _
  rw [← (Equiv.sigmaFiberEquiv fbar).tsum_eq, ENNReal.tsum_sigma', ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun O => ?_)
  exact key O

end GlobalTheory.MassFibre
