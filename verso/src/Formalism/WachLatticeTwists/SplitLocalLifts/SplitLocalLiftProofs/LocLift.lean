import Formalism.WachLatticeTwists.SplitLocalLifts.Cocycles1MapOfEquivariant
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.SelmerInjColumnPlace
import Formalism.WachLatticeTwists.TorsionLengthCounts.RowCol

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

/- English proof (translation)
Introduce `O D M₁ M₂ _ _ _ _ _ _ ρ₁ ρ₂ p hp hs Hf₁ Hf₂ ℓ e hL κ hκ`. Take `⟨x, hx, hxe⟩` from `hL _ hκ`. Take `⟨K₀, rfl⟩` from `Submodule.mkQ_surjective _ x`. Establish `h1 : (Submodule.Quotient.mk (cocycles1MapOfEquivariant ρ₁ ρ₂ p hp K₀ - ((ℓ : O) ^ e) • κ) : H1z ρ₂) = 0`. Rewrite using `[Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero]`.

Conclude with `hxe`. Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Take `⟨v, hv⟩` from `h1`. Take `⟨w, rfl⟩` from `hs v`. Set `cb : coZ1s ρ₁` to `⟨fun g => ρ₁ g w - w, fun g h => by`.

Simplify using `only [map_mul, Module.End.mul_apply, map_sub]`. Use the proof step `abel⟩`. Use `⟨K₀ - cb, ?_, fun g => ?_⟩` and prove the remaining obligations. Establish `hcb : Submodule.mkQ _ cb = (0 : H1z ρ₁)`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`.

Conclude with `⟨w, by funext g; rfl⟩`. Rewrite using `[map_sub, hcb, sub_zero]`. Conclude with `hx`. Establish `h2 : ρ₂ g (p w) - p w = p ((K₀ : D → M₁) g) - ((ℓ : O) ^ e) • (κ : D → M₂) g` using `congrFun hv g show p ((K₀ : D → M₁) g - (ρ₁ g w - w)) = _`. Rewrite using `[map_sub, map_sub, hp, h2]`.

Normalize the expressions using the abelian group laws.
-/
theorem liftCoc : StatLiftCoc := by
  intro O D M₁ M₂ _ _ _ _ _ _ ρ₁ ρ₂ p hp hs Hf₁ Hf₂ ℓ e hL κ hκ
  obtain ⟨x, hx, hxe⟩ := hL _ hκ
  obtain ⟨K₀, rfl⟩ := Submodule.mkQ_surjective _ x
  have h1 : (Submodule.Quotient.mk (cocycles1MapOfEquivariant ρ₁ ρ₂ p hp K₀ - ((ℓ : O) ^ e) • κ) : H1z ρ₂) = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero]
    exact hxe
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
  obtain ⟨v, hv⟩ := h1
  obtain ⟨w, rfl⟩ := hs v
  let cb : coZ1s ρ₁ := ⟨fun g => ρ₁ g w - w, fun g h => by
    simp only [map_mul, Module.End.mul_apply, map_sub]
    abel⟩
  refine ⟨K₀ - cb, ?_, fun g => ?_⟩
  · have hcb : Submodule.mkQ _ cb = (0 : H1z ρ₁) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact ⟨w, by funext g; rfl⟩
    rw [map_sub, hcb, sub_zero]
    exact hx
  · have h2 : ρ₂ g (p w) - p w = p ((K₀ : D → M₁) g) - ((ℓ : O) ^ e) • (κ : D → M₂) g :=
      congrFun hv g
    show p ((K₀ : D → M₁) g - (ρ₁ g w - w)) = _
    rw [map_sub, map_sub, hp, h2]
    abel

/- English proof (translation)
Introduce `O A T' G _ _ _ _ _ P _ _ _ _ L _ _ _ _ r χ Dl inc v₁ ev hev hs Hf₁ Hf₂ ℓ e' j κ κz hκ hκf hL`. Establish `key` using `fun a => liftCoc O Dl P L _ _ ev (ev_equiv r χ Dl inc v₁ ev hev) hs Hf₁ Hf₂ ℓ e' hL (κz a) (hκf a)`. Use `choose Kz hKz1 hKz2 using key`. Use `⟨fun a g => if h : g ∈ Dl then inc ((Kz a : Dl → P) ⟨g, h⟩) else 0, Kz, ?_, hKz1, ?_⟩` and prove the remaining obligations. Introduce `a g dsimp only`.

Rewrite using `[dif_pos g.2]`. Introduce `a g hg dsimp only`. Rewrite using `[dif_pos hg, ← hev, hKz2 a ⟨g, hg⟩, hκ a ⟨g, hg⟩]`.
-/
theorem colK : StatColK := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ L _ _ _ _ r χ Dl inc v₁ ev hev hs Hf₁ Hf₂ ℓ e' j κ κz hκ hκf hL
  have key := fun a => liftCoc O Dl P L _ _ ev (ev_equiv r χ Dl inc v₁ ev hev) hs Hf₁ Hf₂ ℓ e' hL
    (κz a) (hκf a)
  choose Kz hKz1 hKz2 using key
  refine ⟨fun a g => if h : g ∈ Dl then inc ((Kz a : Dl → P) ⟨g, h⟩) else 0, Kz, ?_, hKz1, ?_⟩
  · intro a g
    dsimp only
    rw [dif_pos g.2]
  · intro a g hg
    dsimp only
    rw [dif_pos hg, ← hev, hKz2 a ⟨g, hg⟩, hκ a ⟨g, hg⟩]

/- English proof (translation)
Introduce `O A T' G _ _ _ _ _ P _ _ _ _ M _ _ _ r χ E δO Dl inc ev hE hM hev hs Hf₁ Hf₂ ℓ e' u uz huz hmem hL`. Take `⟨kz, hk1, hk2⟩` from `liftCoc O Dl P _ _ _ ev (ev_equiv_triv r χ Dl ev hev) hs Hf₁ Hf₂ ℓ e' hL uz hmem`. Use `⟨fun g => if h : g ∈ Dl then inc ((kz : Dl → P) ⟨g, h⟩) else 0, kz, ?_, hk1, ?_, ?_⟩` and prove the remaining obligations. Introduce `g dsimp only`. Rewrite using `[dif_pos g.2]`.

Introduce `g dsimp only split_ifs with h`. Conclude with `hE _`. Conclude with `⟨0, (zero_mul E).symm⟩`. Introduce `g hg m dsimp only`. Rewrite using `[dif_pos hg, hM, hk2 ⟨g, hg⟩, Submodule.coe_smul, huz ⟨g, hg⟩, smul_eq_mul, mul_assoc]`.
-/
theorem colk : StatColk := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ M _ _ _ r χ E δO Dl inc ev hE hM hev hs Hf₁ Hf₂ ℓ e' u uz huz hmem hL
  obtain ⟨kz, hk1, hk2⟩ := liftCoc O Dl P _ _ _ ev (ev_equiv_triv r χ Dl ev hev) hs Hf₁ Hf₂ ℓ e' hL
    uz hmem
  refine ⟨fun g => if h : g ∈ Dl then inc ((kz : Dl → P) ⟨g, h⟩) else 0, kz, ?_, hk1, ?_, ?_⟩
  · intro g
    dsimp only
    rw [dif_pos g.2]
  · intro g
    dsimp only
    split_ifs with h
    · exact hE _
    · exact ⟨0, (zero_mul E).symm⟩
  · intro g hg m
    dsimp only
    rw [dif_pos hg, hM, hk2 ⟨g, hg⟩, Submodule.coe_smul, huz ⟨g, hg⟩, smul_eq_mul, mul_assoc]

/- English proof (translation)
Introduce `O A T' G _ _ _ _ _ P _ _ _ _ V _ _ r χ Dl inc Hf₁ Lf H K Kz hK hKz s`. Establish `h` using `H ((LinearMap.toSpanSingleton A V s).comp inc) Kz hKz`. Establish `e : (fun g : Dl => K g • s) = fun g : Dl => ((LinearMap.toSpanSingleton A V s).comp inc) ((Kz : Dl → P) g)`. Use function extensionality and compare the values at `g`. Rewrite using `[hK g]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h`.
-/
theorem colFun : StatColFun := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ V _ _ r χ Dl inc Hf₁ Lf H K Kz hK hKz s
  have h := H ((LinearMap.toSpanSingleton A V s).comp inc) Kz hKz
  have e : (fun g : Dl => K g • s) =
      fun g : Dl => ((LinearMap.toSpanSingleton A V s).comp inc) ((Kz : Dl → P) g) := by
    funext g
    rw [hK g]
    rfl
  rw [e]
  exact h

/- English proof (translation)
Introduce `O _ _ _ H₁ Cs _ _ _ _ Hf₁ Fs g ℓ e' hL`. Establish `h1 : ∀ x : Fs, ((ℓ : O) ^ e') • x ∈ (Hf₁.map g).comap Fs.subtype`. Introduce `x`. Rewrite using `[Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]`. Conclude with `hL _ x.2`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Introduce `hfin`. Conclude with `Formalism.RepresentationBoundsCohomology.rowColength O Fs _ ℓ e' h1`.
-/
theorem rowLift : StatRowLift := by
  intro O _ _ _ H₁ Cs _ _ _ _ Hf₁ Fs g ℓ e' hL
  have h1 : ∀ x : Fs, ((ℓ : O) ^ e') • x ∈ (Hf₁.map g).comap Fs.subtype := by
    intro x
    rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]
    exact hL _ x.2
  refine ⟨h1, ?_⟩
  intro hfin
  exact Formalism.RepresentationBoundsCohomology.rowColength O Fs _ ℓ e' h1

/- English proof (translation)
Introduce `O Dw T₁ T₂ _ _ _ _ _ _ ρ₁ ρ₂ π hπ C₁ Hf₁ Fs hFun hC`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨y, hy, rfl⟩`. Take `⟨a, ha, rfl⟩` from `hC y hy`. Use `⟨(a : Dw → T₁), a.2, ha, ?_⟩` and prove the remaining obligations.

Establish `hm : (fun g => π ((a : Dw → T₁) g)) ∈ coZ1s ρ₂` using `(cocycles1MapOfEquivariant ρ₁ ρ₂ π hπ a).2`. Unfold `clsOf`. Rewrite using `[dif_pos hm]`. Both sides reduce to the same expression. Introduce and unpack `x ⟨y, hy, rfl⟩`.

Conclude with `hFun y hy`.
-/
theorem rowIm : StatRowIm := by
  intro O Dw T₁ T₂ _ _ _ _ _ _ ρ₁ ρ₂ π hπ C₁ Hf₁ Fs hFun hC
  refine ⟨?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hC y hy
    refine ⟨(a : Dw → T₁), a.2, ha, ?_⟩
    have hm : (fun g => π ((a : Dw → T₁) g)) ∈ coZ1s ρ₂ := (cocycles1MapOfEquivariant ρ₁ ρ₂ π hπ a).2
    unfold clsOf
    rw [dif_pos hm]
    rfl
  · rintro x ⟨y, hy, rfl⟩
    exact hFun y hy

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> intros <;> exact Iff.rfl`.
-/
theorem locLift : StatLocLift := by
  refine ⟨?_, ?_⟩ <;> intros <;> exact Iff.rfl

end Formalism.RepresentationBoundsCohomology.JL
