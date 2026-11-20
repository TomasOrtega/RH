import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.SmulYGenEqZero

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

/- English proof (translation)
Establish `hy : ycoc r χ E g = ycoc r χ E g'` using `by show ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) * E = ((((χ g')⁻¹ : T'ˣ) : T') • r g' - 1) * E`. Rewrite using `[hr, hχ]`. Unfold `yGen`. Use `congr 1`. Conclude with `Prod.ext (Subtype.ext hy) rfl`.
-/
lemma yGen_congr {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A) (g g' : G)
    (hr : r g = r g') (hχ : χ g = χ g') :
    yGen r χ E e₁ δ D j Kc k0 g = yGen r χ E e₁ δ D j Kc k0 g' := by
  have hy : ycoc r χ E g = ycoc r χ E g' := by
    show ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) * E = ((((χ g')⁻¹ : T'ˣ) : T') • r g' - 1) * E
    rw [hr, hχ]
  unfold yGen
  congr 1
  exact Prod.ext (Subtype.ext hy) rfl

/- English proof (translation)
Introduce `O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 Dw I γ ζ ζO n hγ hquad hζ hpow htriv hγM`. Establish `h1 : ∀ φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M, (ζO - 1) • φ (yGen r χ E e₁ δ D j Kc k0 (γ : G)) = 0`. Introduce `φ`. Establish `h` using `smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 (r (γ : G) - 1) (γ : G) (qAlg A T' G r χ E (γ : G) ζ hquad hζ)`. Establish `h2` using `congrArg φ h`.

Rewrite `h2` using `[map_smul, map_zero, sub_smul, one_smul, hγM]`. Rewrite using `[sub_smul, one_smul]`. Conclude with `h2`. Establish `hpw : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) (k : ℕ), φ (yGen r χ E e₁ δ D j Kc k0 ((γ : G) ^ k)) = k • φ (yGen r χ E e₁ δ D j Kc k0 (γ : G))`. Introduce `φ k`.

Proceed by induction on `k with`. Consider the case `zero`. Establish `h0` using `smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 1 ((γ : G) ^ 0) (by`. Unfold `ycoc`. Use the proof step `simp)`.

Rewrite `h0` using `[one_smul]`. Rewrite using `[h0, map_zero, zero_smul]`. Consider the case `succ k ih`. Establish `hmem : γ ^ k ∈ I` using `I.pow_mem hγ k`. Establish `ht` using `htriv (γ ^ k) hmem (φ (yGen r χ E e₁ δ D j Kc k0 (γ : G)))`.

Rewrite `ht` using `[Subgroup.coe_pow]`. Rewrite using `[pow_succ, yGen_mul, map_add, map_smul, ih, ht, succ_nsmul]`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Use `set ρD := resRep (uRep O (M := M) r χ) Dw with hρD`. Use `set ρI := resRep ρD I with hρI`.

Set `γ' : I` to `⟨γ, hγ⟩`. Set `ZI : Submodule O (coZ1s ρI)` to `{ carrier := {z | (ζO - 1) • (z : I → M) γ' = 0 ∧ ∀ g : I, (z : I → M) g = n g • (z : I → M) γ'} add_mem' := by`. Introduce and unpack `a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩`. Use `⟨?_, fun g => ?_⟩` and prove the remaining obligations. Use `show (ζO - 1) • ((a : I → M) γ' + (b : I → M) γ') = 0`.

Rewrite using `[smul_add, ha1, hb1, add_zero]`. Use `show (a : I → M) g + (b : I → M) g = n g • ((a : I → M) γ' + (b : I → M) γ')`. Rewrite using `[ha2 g, hb2 g, smul_add]`. Use the proof step `zero_mem' := ⟨smul_zero _, fun g => (smul_zero _).symm⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `c a ⟨ha1, ha2⟩`. Use `⟨?_, fun g => ?_⟩` and prove the remaining obligations. Use `show (ζO - 1) • (c • (a : I → M) γ') = 0`. Rewrite using `[smul_comm, ha1, smul_zero]`. Use `show c • (a : I → M) g = n g • (c • (a : I → M) γ')`.

Rewrite using `[ha2 g, smul_comm] }`. Set `evZ : coZ1s ρI →ₗ[O] M` to `{ toFun := fun z => (z : I → M) γ' map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hev : (coB1 ρI).comap (coZ1s ρI).subtype ≤ LinearMap.ker evZ`. Introduce and unpack `z ⟨v, hv⟩`. Establish `: (z : I → M) γ' = ρI γ' v - v` using `(congrFun hv γ').symm`.

Use `show (z : I → M) γ' = 0`. Rewrite using `[this]`. Conclude with `sub_eq_zero.mpr (htriv γ hγ v)`. Set `ev : H1z ρI →ₗ[O] M` to `Submodule.liftQ _ evZ hev`. Set `BI : Submodule O (H1z ρI)` to `ZI.map (Submodule.mkQ _)`.

Set `B : Submodule O (H1z ρD)` to `BI.comap (resH1 ρD I)`. Set `tgt` to `LinearMap.ker (DistribSMul.toLinearMap O M (ζO - 1))`. Establish `hB : ∀ b : B, ev (resH1 ρD I b) ∈ tgt`. Introduce and unpack `⟨b, z, hz, hzb⟩`. Use `show (ζO - 1) • ev (resH1 ρD I b) = 0`.

Rewrite using `[← hzb]`. Conclude with `hz.1`. Set `f : B →ₗ[O] tgt` to `LinearMap.codRestrict tgt (ev ∘ₗ resH1 ρD I ∘ₗ B.subtype) hB`. Establish `hk1 : (unrH1 ρD I).comap B.subtype ≤ LinearMap.ker f`. Introduce `b hb`.

Establish `hb' : resH1 ρD I b = 0` using `hb`. Use `Subtype.ext ?_` and prove the remaining obligations. Use `show ev (resH1 ρD I b) = 0`. Rewrite using `[hb', map_zero]`. Establish `hk2 : LinearMap.ker f ≤ (unrH1 ρD I).comap B.subtype`.

Introduce and unpack `⟨b, z, hz, hzb⟩ hb`. Establish `hb' : ev (resH1 ρD I b) = 0` using `congrArg Subtype.val hb`. Use `show resH1 ρD I b = 0`. Rewrite `hb'`, the goal using `[← hzb]`. Establish `hz0 : (z : I → M) γ' = 0` using `hb'`.

Establish `: z = 0` using `Subtype.ext (funext fun g => by rw [hz.2 g, hz0, smul_zero]; rfl)`. Rewrite using `[this, map_zero]`. Use `⟨B, fun x hx => ?_, ?_, fun φ => ?_⟩` and prove the remaining obligations. Use `show resH1 ρD I x ∈ BI`. Rewrite using `[show resH1 ρD I x = 0 from hx]`.

Conclude with `BI.zero_mem`. Use `Module.length_le_of_injective (Submodule.liftQ _ f hk1) ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot]`. Conclude with `Submodule.ker_liftQ_eq_bot _ _ _ hk2`. Use `⟨restrictCocycles1 ρD I (restrictCocycles1 (uRep O (M := M) r χ) Dw (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)), ⟨h1 φ, fun g => ?_⟩, rfl⟩ show φ (yGen r χ E e₁ δ D j Kc k0 ((g : Dw) : G)) = n g • φ (yGen r χ E e₁ δ D j Kc k0 (γ : G))` and prove the remaining obligations.

Rewrite using `[← hpw φ (n g)]`. Use `congr 1`. Use `yGen_congr r χ E e₁ δ D j Kc k0 _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[(hpow g g.2).1, map_pow]`. Rewrite using `[(hpow g g.2).2, map_pow]`.
-/
theorem qPlace : StatQPlace := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 Dw I γ ζ ζO n hγ hquad hζ hpow
    htriv hγM
  have h1 : ∀ φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M,
      (ζO - 1) • φ (yGen r χ E e₁ δ D j Kc k0 (γ : G)) = 0 := by
    intro φ
    have h := smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 (r (γ : G) - 1) (γ : G)
      (qAlg A T' G r χ E (γ : G) ζ hquad hζ)
    have h2 := congrArg φ h
    rw [map_smul, map_zero, sub_smul, one_smul, hγM] at h2
    rw [sub_smul, one_smul]
    exact h2
  have hpw : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) (k : ℕ),
      φ (yGen r χ E e₁ δ D j Kc k0 ((γ : G) ^ k)) =
        k • φ (yGen r χ E e₁ δ D j Kc k0 (γ : G)) := by
    intro φ k
    induction k with
    | zero =>
      have h0 := smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 1 ((γ : G) ^ 0) (by
        unfold ycoc
        simp)
      rw [one_smul] at h0
      rw [h0, map_zero, zero_smul]
    | succ k ih =>
      have hmem : γ ^ k ∈ I := I.pow_mem hγ k
      have ht := htriv (γ ^ k) hmem (φ (yGen r χ E e₁ δ D j Kc k0 (γ : G)))
      rw [Subgroup.coe_pow] at ht
      rw [pow_succ, yGen_mul, map_add, map_smul, ih, ht, succ_nsmul]
  refine ⟨h1, ?_⟩
  set ρD := resRep (uRep O (M := M) r χ) Dw with hρD
  set ρI := resRep ρD I with hρI
  let γ' : I := ⟨γ, hγ⟩
  let ZI : Submodule O (coZ1s ρI) :=
    { carrier := {z | (ζO - 1) • (z : I → M) γ' = 0 ∧ ∀ g : I, (z : I → M) g = n g • (z : I → M) γ'}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨?_, fun g => ?_⟩
        · show (ζO - 1) • ((a : I → M) γ' + (b : I → M) γ') = 0
          rw [smul_add, ha1, hb1, add_zero]
        · show (a : I → M) g + (b : I → M) g = n g • ((a : I → M) γ' + (b : I → M) γ')
          rw [ha2 g, hb2 g, smul_add]
      zero_mem' := ⟨smul_zero _, fun g => (smul_zero _).symm⟩
      smul_mem' := by
        rintro c a ⟨ha1, ha2⟩
        refine ⟨?_, fun g => ?_⟩
        · show (ζO - 1) • (c • (a : I → M) γ') = 0
          rw [smul_comm, ha1, smul_zero]
        · show c • (a : I → M) g = n g • (c • (a : I → M) γ')
          rw [ha2 g, smul_comm] }
  let evZ : coZ1s ρI →ₗ[O] M :=
    { toFun := fun z => (z : I → M) γ'
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : (coB1 ρI).comap (coZ1s ρI).subtype ≤ LinearMap.ker evZ := by
    rintro z ⟨v, hv⟩
    have : (z : I → M) γ' = ρI γ' v - v := (congrFun hv γ').symm
    show (z : I → M) γ' = 0
    rw [this]
    exact sub_eq_zero.mpr (htriv γ hγ v)
  let ev : H1z ρI →ₗ[O] M := Submodule.liftQ _ evZ hev
  let BI : Submodule O (H1z ρI) := ZI.map (Submodule.mkQ _)
  let B : Submodule O (H1z ρD) := BI.comap (resH1 ρD I)
  let tgt := LinearMap.ker (DistribSMul.toLinearMap O M (ζO - 1))
  have hB : ∀ b : B, ev (resH1 ρD I b) ∈ tgt := by
    rintro ⟨b, z, hz, hzb⟩
    show (ζO - 1) • ev (resH1 ρD I b) = 0
    rw [← hzb]
    exact hz.1
  let f : B →ₗ[O] tgt := LinearMap.codRestrict tgt (ev ∘ₗ resH1 ρD I ∘ₗ B.subtype) hB
  have hk1 : (unrH1 ρD I).comap B.subtype ≤ LinearMap.ker f := by
    intro b hb
    have hb' : resH1 ρD I b = 0 := hb
    refine Subtype.ext ?_
    show ev (resH1 ρD I b) = 0
    rw [hb', map_zero]
  have hk2 : LinearMap.ker f ≤ (unrH1 ρD I).comap B.subtype := by
    rintro ⟨b, z, hz, hzb⟩ hb
    have hb' : ev (resH1 ρD I b) = 0 := congrArg Subtype.val hb
    show resH1 ρD I b = 0
    rw [← hzb] at hb' ⊢
    have hz0 : (z : I → M) γ' = 0 := hb'
    have : z = 0 := Subtype.ext (funext fun g => by rw [hz.2 g, hz0, smul_zero]; rfl)
    rw [this, map_zero]
  refine ⟨B, fun x hx => ?_, ?_, fun φ => ?_⟩
  · show resH1 ρD I x ∈ BI
    rw [show resH1 ρD I x = 0 from hx]
    exact BI.zero_mem
  · refine Module.length_le_of_injective (Submodule.liftQ _ f hk1) ?_
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hk2
  · refine ⟨restrictCocycles1 ρD I (restrictCocycles1 (uRep O (M := M) r χ) Dw
      (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)), ⟨h1 φ, fun g => ?_⟩, rfl⟩
    show φ (yGen r χ E e₁ δ D j Kc k0 ((g : Dw) : G)) =
      n g • φ (yGen r χ E e₁ δ D j Kc k0 (γ : G))
    rw [← hpw φ (n g)]
    congr 1
    refine yGen_congr r χ E e₁ δ D j Kc k0 _ _ ?_ ?_
    · rw [(hpow g g.2).1, map_pow]
    · rw [(hpow g g.2).2, map_pow]

end Formalism.RepresentationBoundsCohomology.BR
