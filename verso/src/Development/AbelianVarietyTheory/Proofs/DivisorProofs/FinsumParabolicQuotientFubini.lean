import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

/- English proof (translation)
Introduce `P M N V _ _ _ _ lev s u hsec hlu _hu_inj hker UP UM hsU hlevU Φ hΦ hfin`. Set `F : (M ⧸ UM) × (N ⧸ UP.comap u) → P ⧸ UP` to `fun cx => (QuotientGroup.mk (s cx.1.out * u cx.2.out) : P ⧸ UP)`. Establish `hbij : Function.Bijective F`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, x⟩ ⟨c', x'⟩ h`.

Simplify using `only [F] at h`. Rewrite `h` using `[QuotientGroup.eq]`. Establish `h1 : (c.out)⁻¹ * c'.out ∈ UM`. Use `hlevU (Subgroup.mem_map_of_mem lev h)` as an intermediate fact. Simplify `this` using `[map_mul, map_inv, hsec, hlu]`.

Establish `hc : c = c'`. Rewrite using `[← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']`. Conclude with `QuotientGroup.eq.mpr h1`. Substitute `hc` using the available equality. Establish `h2 : (x.out)⁻¹ * x'.out ∈ UP.comap u`.

Rewrite using `[Subgroup.mem_comap]`. Establish `he : (s c.out * u x.out)⁻¹ * (s c.out * u x'.out) = u ((x.out)⁻¹ * x'.out)`. Rewrite using `[map_mul, map_inv]`. Use `group`. Rewrite using `[← he]`.

Conclude with `h`. Establish `hx : x = x'`. Rewrite using `[← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x']`. Conclude with `QuotientGroup.eq.mpr h2`. Rewrite using `[hx]`.

Introduce `q set p := q.out with hp set c : M ⧸ UM := (QuotientGroup.mk (lev p) : M ⧸ UM) with hc`. Establish `hk : (c.out)⁻¹ * lev p ∈ UM`. Rewrite using `[← QuotientGroup.eq, QuotientGroup.out_eq']`. Use `set k := (c.out)⁻¹ * lev p with hkdef`. Establish `hr : lev ((s c.out)⁻¹ * p * (s k)⁻¹) = 1`.

Simplify using `only [map_mul, map_inv, hsec, hkdef]`. Use `group`. Take `⟨Z, hZ⟩` from `hker _ hr`. Use `⟨(c, (QuotientGroup.mk Z : N ⧸ UP.comap u)), ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `QuotientGroup.mk_out_eq_mul (UP.comap u) Z`.

Simplify using `only [F]`. Rewrite using `[hy, ← QuotientGroup.out_eq' q, ← hp, QuotientGroup.eq]`. Establish `hyU : u (y : N) ∈ UP` using `y.2`. Establish `hsk : s k ∈ UP` using `hsU (Subgroup.mem_map_of_mem s hk)`. Establish `he : (s c.out * u (Z * y))⁻¹ * p = (u (y : N))⁻¹ * s k`.

Rewrite using `[map_mul, hZ]`. Use `group`. Rewrite using `[he]`. Conclude with `UP.mul_mem (UP.inv_mem hyU) hsk`. Set `e` to `Equiv.ofBijective F hbij`.

Establish `hval : ∀ cx, Φ (e cx).out = Φ (s cx.1.out * u cx.2.out)`. Introduce `cx`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul UP (s cx.1.out * u cx.2.out)`. Use `show Φ (F cx).out = _`. Simplify using `only [F]`.

Rewrite using `[hh]`. Conclude with `hΦ _ _ h.2`. Establish `hsupp : (Function.support (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out))).Finite`. Establish `: Function.support (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out)) = e ⁻¹' {q : P ⧸ UP | Φ q.out ≠ 0}`. Use extensionality with `cx`.

Simplify using `only [Function.mem_support, Set.mem_preimage, Set.mem_setOf_eq, hval]`. Rewrite using `[this]`. Conclude with `hfin.preimage e.injective.injOn`. Rewrite using `[← finsum_comp_equiv e]`. Rewrite using `[finsum_congr hval]`.

Conclude with `finsum_curry (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out)) hsupp`.
-/
theorem split_quotient_finsum_regroup : ∀ (P M N V : Type) [Group P] [Group M] [Group N] [AddCommMonoid V] (lev : P →* M) (s : M →* P) (u : N →* P), (∀ m, lev (s m) = m) → (∀ x, lev (u x) = 1) → Function.Injective u → (∀ p, lev p = 1 → ∃ x, u x = p) → ∀ (UP : Subgroup P) (UM : Subgroup M), UM.map s ≤ UP → UP.map lev ≤ UM → ∀ (Φ : P → V), (∀ p, ∀ q ∈ UP, Φ (p * q) = Φ p) → {q : P ⧸ UP | Φ q.out ≠ 0}.Finite → ∑ᶠ q : P ⧸ UP, Φ q.out = ∑ᶠ c : M ⧸ UM, ∑ᶠ x : N ⧸ UP.comap u, Φ (s c.out * u x.out) := by
  intro P M N V _ _ _ _ lev s u hsec hlu _hu_inj hker UP UM hsU hlevU Φ hΦ hfin
  let F : (M ⧸ UM) × (N ⧸ UP.comap u) → P ⧸ UP :=
    fun cx => (QuotientGroup.mk (s cx.1.out * u cx.2.out) : P ⧸ UP)
  have hbij : Function.Bijective F := by
    constructor
    · rintro ⟨c, x⟩ ⟨c', x'⟩ h
      simp only [F] at h
      rw [QuotientGroup.eq] at h
      have h1 : (c.out)⁻¹ * c'.out ∈ UM := by
        have := hlevU (Subgroup.mem_map_of_mem lev h)
        simpa [map_mul, map_inv, hsec, hlu] using this
      have hc : c = c' := by
        rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
        exact QuotientGroup.eq.mpr h1
      subst hc
      have h2 : (x.out)⁻¹ * x'.out ∈ UP.comap u := by
        rw [Subgroup.mem_comap]
        have he : (s c.out * u x.out)⁻¹ * (s c.out * u x'.out) = u ((x.out)⁻¹ * x'.out) := by
          rw [map_mul, map_inv]; group
        rw [← he]; exact h
      have hx : x = x' := by
        rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x']
        exact QuotientGroup.eq.mpr h2
      rw [hx]
    · intro q
      set p := q.out with hp
      set c : M ⧸ UM := (QuotientGroup.mk (lev p) : M ⧸ UM) with hc
      have hk : (c.out)⁻¹ * lev p ∈ UM := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      set k := (c.out)⁻¹ * lev p with hkdef
      have hr : lev ((s c.out)⁻¹ * p * (s k)⁻¹) = 1 := by
        simp only [map_mul, map_inv, hsec, hkdef]; group
      obtain ⟨Z, hZ⟩ := hker _ hr
      refine ⟨(c, (QuotientGroup.mk Z : N ⧸ UP.comap u)), ?_⟩
      obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul (UP.comap u) Z
      simp only [F]
      rw [hy, ← QuotientGroup.out_eq' q, ← hp, QuotientGroup.eq]
      have hyU : u (y : N) ∈ UP := y.2
      have hsk : s k ∈ UP := hsU (Subgroup.mem_map_of_mem s hk)
      have he : (s c.out * u (Z * y))⁻¹ * p = (u (y : N))⁻¹ * s k := by
        rw [map_mul, hZ]; group
      rw [he]
      exact UP.mul_mem (UP.inv_mem hyU) hsk
  let e := Equiv.ofBijective F hbij
  have hval : ∀ cx, Φ (e cx).out = Φ (s cx.1.out * u cx.2.out) := by
    intro cx
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul UP (s cx.1.out * u cx.2.out)
    show Φ (F cx).out = _
    simp only [F]; rw [hh]; exact hΦ _ _ h.2
  have hsupp : (Function.support
      (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out))).Finite := by
    have : Function.support
        (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out))
        = e ⁻¹' {q : P ⧸ UP | Φ q.out ≠ 0} := by
      ext cx; simp only [Function.mem_support, Set.mem_preimage, Set.mem_setOf_eq, hval]
    rw [this]; exact hfin.preimage e.injective.injOn
  rw [← finsum_comp_equiv e]
  rw [finsum_congr hval]
  exact finsum_curry (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out)) hsupp

end GlobalTheory
