import Formalism.WachLatticeTwists.TorsionKernelSplitting.WachTwistSplitTheoremHZero

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

/- English proof (translation)
Introduce `O _ _ _ Cs _ _ Fs hfin`. Use `infer_instance`.
-/
theorem finSub : StatFinSub := by
  intro O _ _ _ Cs _ _ Fs hfin
  infer_instance

/- English proof (translation)
Introduce `O _ _ _ D _ T₂ V A Cs _ _ _ _ _ _ _ _ _ _ ρ₂ ρV ρA i q Zc cls Fs hseq hcls`. Take `⟨hi, hex, hiE, hqE⟩` from `hseq`. Take `⟨hadd, hsmul, hB, hFs⟩` from `hcls`. Set `clsL : Zc →ₗ[O] Cs` to `{ toFun := fun a => cls a.1 map_add' := fun a b => hadd a.1 a.2 b.1 b.2 map_smul' := fun c a => hsmul c a.1 a.2 }`. Set `Γ : Submodule O (Zc × V)` to `{ carrier := {p | ∀ g, i ((p.1 : D → T₂) g) = ρV g p.2 - p.2} add_mem' := by`.

Introduce `p p' hp hp' g`. Establish `h1` using `hp g`. Establish `h2` using `hp' g`. Simplify using `only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply, map_add, h1, h2]`. Normalize the expressions using the abelian group laws.

Use the proof step `zero_mem' := by`. Introduce `g`. Simplify using the standard rewrite rules. Use the proof step `smul_mem' := by`. Introduce `c p hp g`.

Establish `h1` using `hp g`. Simplify using `only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Pi.smul_apply, map_smul, h1, smul_sub] }`. Set `f : Γ →ₗ[O] Cs` to `clsL ∘ₗ LinearMap.fst O Zc V ∘ₗ Γ.subtype`. Set `g : Γ →ₗ[O] A` to `q ∘ₗ LinearMap.snd O Zc V ∘ₗ Γ.subtype`. Establish `hker : LinearMap.ker g ≤ LinearMap.ker f`.

Introduce `p hp`. Rewrite `hp`, the goal using `[LinearMap.mem_ker]`. Establish `hq : q p.1.2 = 0` using `hp`. Take `⟨t, ht⟩` from `(hex _).1 hq`. Use `show cls (p.1.1 : D → T₂) = 0`.

Rewrite using `[hB _ p.1.1.2]`. Use `⟨t, funext fun γ => hi ?_⟩` and prove the remaining obligations. Establish `h1 : i ((p.1.1 : D → T₂) γ) = ρV γ p.1.2 - p.1.2` using `p.2 γ`. Rewrite using `[h1, ← ht]`. Use `show i (ρ₂ γ t - t) = _`.

Rewrite using `[map_sub, hiE γ t]`. Establish `hg : LinearMap.range g ≤ LinearMap.ker (coD0 ρA)`. Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[LinearMap.mem_ker]`. Use function extensionality and compare the values at `γ`.

Use `show ρA γ (q p.1.2) - q p.1.2 = 0`. Rewrite using `[← hqE γ, ← map_sub]`. Establish `h1 : i ((p.1.1 : D → T₂) γ) = ρV γ p.1.2 - p.1.2` using `p.2 γ`. Rewrite using `[← h1]`. Conclude with `(hex _).2 ⟨_, rfl⟩`.

Establish `hT : (Submodule.torsion O Fs).map Fs.subtype ≤ LinearMap.range f`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨c, hc⟩` from `(Submodule.mem_torsion_iff x).1 hx`. Take `⟨a, ha, hxa⟩` from `hFs x.1 x.2`. Establish `hc0 : (c : O) ≠ 0` using `nonZeroDivisors.ne_zero c.2`.

Establish `hcx : (c : O) • (x : Cs) = 0`. Establish `h` using `congrArg (Subtype.val) hc`. Conclude with `h`. Establish `h0 : cls ((c : O) • a) = 0` using `by rw [hsmul _ a ha, ← hxa, hcx]`. Take `⟨t, ht⟩` from `(hB _ (Zc.smul_mem _ ha)).1 h0`.

Establish `hcK : algebraMap O (FractionRing O) (c : O) ≠ 0`. Simplify using `[hc0]`. Set `v : V` to `(algebraMap O (FractionRing O) (c : O))⁻¹ • i t`. Establish `hv : (c : O) • v = i t` using `by show (c : O) • ((algebraMap O (FractionRing O) (c : O))⁻¹ • i t) = i t`. Rewrite using `[← algebraMap_smul (FractionRing O) (c : O), smul_smul, mul_inv_cancel₀ hcK, one_smul]`.

Establish `hinj : ∀ y : V, (c : O) • y = 0 → y = 0`. Introduce `y hy`. Rewrite `hy` using `[← algebraMap_smul (FractionRing O) (c : O)]`. Conclude with `(smul_eq_zero.1 hy).resolve_left hcK`. Establish `hmem : ((⟨a, ha⟩ : Zc), v) ∈ Γ`.

Introduce `γ`. Use `show i (a γ) = ρV γ v - v`. Establish `h2 : (c : O) • (i (a γ) - (ρV γ v - v)) = 0`. Rewrite using `[smul_sub, smul_sub, ← map_smul, ← map_smul, hv, ← hiE γ t, ← map_sub]`. Establish `h3 : ρ₂ γ t - t = ((c : O) • a) γ` using `congrFun ht γ`.

Rewrite using `[h3, Pi.smul_apply, sub_self]`. Conclude with `sub_eq_zero.1 (hinj _ h2)`. Conclude with `⟨⟨_, hmem⟩, hxa.symm⟩`. Combine the equalities or inequalities in the displayed calculation. Establish `hker' : LinearMap.ker g ≤ LinearMap.ker f.rangeRestrict`.

Rewrite using `[LinearMap.ker_rangeRestrict]`. Conclude with `hker`. Use `Module.length_le_of_surjective ((LinearMap.ker g).liftQ f.rangeRestrict hker') ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_rangeRestrict]`. Use `_ = Module.length O (LinearMap.range g) := g.quotKerEquivRange.length_eq`.

Use `_ ≤ Module.length O (LinearMap.ker (coD0 ρA)) := Module.length_le_of_injective (Submodule.inclusion hg) (Submodule.inclusion_injective hg)`.
-/
theorem torsion_le_h_zero : TorsionLeHZero := by
  intro O _ _ _ D _ T₂ V A Cs _ _ _ _ _ _ _ _ _ _ ρ₂ ρV ρA i q Zc cls Fs hseq hcls
  obtain ⟨hi, hex, hiE, hqE⟩ := hseq
  obtain ⟨hadd, hsmul, hB, hFs⟩ := hcls
  let clsL : Zc →ₗ[O] Cs :=
    { toFun := fun a => cls a.1
      map_add' := fun a b => hadd a.1 a.2 b.1 b.2
      map_smul' := fun c a => hsmul c a.1 a.2 }
  let Γ : Submodule O (Zc × V) :=
    { carrier := {p | ∀ g, i ((p.1 : D → T₂) g) = ρV g p.2 - p.2}
      add_mem' := by
        intro p p' hp hp' g
        have h1 := hp g
        have h2 := hp' g
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply, map_add, h1, h2]
        abel
      zero_mem' := by
        intro g
        simp
      smul_mem' := by
        intro c p hp g
        have h1 := hp g
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Pi.smul_apply, map_smul, h1,
          smul_sub] }
  let f : Γ →ₗ[O] Cs := clsL ∘ₗ LinearMap.fst O Zc V ∘ₗ Γ.subtype
  let g : Γ →ₗ[O] A := q ∘ₗ LinearMap.snd O Zc V ∘ₗ Γ.subtype
  have hker : LinearMap.ker g ≤ LinearMap.ker f := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    have hq : q p.1.2 = 0 := hp
    obtain ⟨t, ht⟩ := (hex _).1 hq
    show cls (p.1.1 : D → T₂) = 0
    rw [hB _ p.1.1.2]
    refine ⟨t, funext fun γ => hi ?_⟩
    have h1 : i ((p.1.1 : D → T₂) γ) = ρV γ p.1.2 - p.1.2 := p.2 γ
    rw [h1, ← ht]
    show i (ρ₂ γ t - t) = _
    rw [map_sub, hiE γ t]
  have hg : LinearMap.range g ≤ LinearMap.ker (coD0 ρA) := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.mem_ker]
    funext γ
    show ρA γ (q p.1.2) - q p.1.2 = 0
    rw [← hqE γ, ← map_sub]
    have h1 : i ((p.1.1 : D → T₂) γ) = ρV γ p.1.2 - p.1.2 := p.2 γ
    rw [← h1]
    exact (hex _).2 ⟨_, rfl⟩
  have hT : (Submodule.torsion O Fs).map Fs.subtype ≤ LinearMap.range f := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff x).1 hx
    obtain ⟨a, ha, hxa⟩ := hFs x.1 x.2
    have hc0 : (c : O) ≠ 0 := nonZeroDivisors.ne_zero c.2
    have hcx : (c : O) • (x : Cs) = 0 := by
      have h := congrArg (Subtype.val) hc
      exact h
    have h0 : cls ((c : O) • a) = 0 := by rw [hsmul _ a ha, ← hxa, hcx]
    obtain ⟨t, ht⟩ := (hB _ (Zc.smul_mem _ ha)).1 h0
    have hcK : algebraMap O (FractionRing O) (c : O) ≠ 0 := by
      simp [hc0]
    let v : V := (algebraMap O (FractionRing O) (c : O))⁻¹ • i t
    have hv : (c : O) • v = i t := by
      show (c : O) • ((algebraMap O (FractionRing O) (c : O))⁻¹ • i t) = i t
      rw [← algebraMap_smul (FractionRing O) (c : O), smul_smul, mul_inv_cancel₀ hcK, one_smul]
    have hinj : ∀ y : V, (c : O) • y = 0 → y = 0 := by
      intro y hy
      rw [← algebraMap_smul (FractionRing O) (c : O)] at hy
      exact (smul_eq_zero.1 hy).resolve_left hcK
    have hmem : ((⟨a, ha⟩ : Zc), v) ∈ Γ := by
      intro γ
      show i (a γ) = ρV γ v - v
      have h2 : (c : O) • (i (a γ) - (ρV γ v - v)) = 0 := by
        rw [smul_sub, smul_sub, ← map_smul, ← map_smul, hv, ← hiE γ t, ← map_sub]
        have h3 : ρ₂ γ t - t = ((c : O) • a) γ := congrFun ht γ
        rw [h3, Pi.smul_apply, sub_self]
      exact sub_eq_zero.1 (hinj _ h2)
    exact ⟨⟨_, hmem⟩, hxa.symm⟩
  calc Module.length O (Submodule.torsion O Fs)
      = Module.length O ((Submodule.torsion O Fs).map Fs.subtype) :=
        (Submodule.equivMapOfInjective Fs.subtype Fs.injective_subtype _).length_eq
    _ ≤ Module.length O (LinearMap.range f) :=
        Module.length_le_of_injective (Submodule.inclusion hT) (Submodule.inclusion_injective hT)
    _ ≤ Module.length O (Γ ⧸ LinearMap.ker g) := by
        have hker' : LinearMap.ker g ≤ LinearMap.ker f.rangeRestrict := by
          rw [LinearMap.ker_rangeRestrict]
          exact hker
        refine Module.length_le_of_surjective ((LinearMap.ker g).liftQ f.rangeRestrict hker') ?_
        rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_rangeRestrict]
    _ = Module.length O (LinearMap.range g) := g.quotKerEquivRange.length_eq
    _ ≤ Module.length O (LinearMap.ker (coD0 ρA)) :=
        Module.length_le_of_injective (Submodule.inclusion hg) (Submodule.inclusion_injective hg)

end Formalism.RepresentationBoundsCohomology.JS
